'use strict';

// VIRTUAL REGATTA PWA — service distant NOAA GFS GRIB2.
// Le serveur et le décodeur sont installés sur l'hébergeur, jamais sur les appareils clients.
// Les navigateurs accèdent à l'application par une URL HTTPS.

const http = require('http');
const https = require('https');
const fs = require('fs');
const path = require('path');
const crypto = require('crypto');
const zlib = require('zlib');

const PORT = Number(process.env.PORT || 3000);
const HOST = process.env.HOST || '0.0.0.0';
const DIR = __dirname;
const SAVE = path.join(DIR, 'save.json');
const DEFAULT_PAGE = 'index.html';
const WEATHER_DIR = path.join(DIR, 'noaa_cache');
const GRIB_DIR = path.join(WEATHER_DIR, 'grib');
const FORECAST_DIR = path.join(WEATHER_DIR, 'forecast');
const MAX_BODY = 8 * 1024 * 1024;
const MAX_POINTS = 12000;
const HOURS = Array.from({ length: 129 }, (_, i) => i * 3); // f000 → f384
const NATIVE_COUNT = HOURS.length;
const PRE_HOURS = 48;       // marge passée pour conserver l'axe temporel du jeu
const GAME_HOURS = PRE_HOURS + 384 + 1; // 433 valeurs : -48 h → +384 h
const MPS_TO_KNOTS = 1.9438444924406;
const DEG = Math.PI / 180;
const HOUR_MS = 3600000;
// NOMADS demande d'espacer les téléchargements automatisés d'environ 10 s.
// Peut être ajusté par variable d'environnement si NOAA publie une nouvelle consigne.
const NOAA_MIN_INTERVAL_MS = Math.max(1000, Number(process.env.NOAA_MIN_INTERVAL_MS || 2000));
// NOMADS tolère 120 requêtes/min par IP : 2 s d'écart = 30/min, très prudent.
// Origine autorisée à appeler l'API (ex. https://tonpseudo.github.io). '*' = tout le monde.
const ALLOWED_ORIGIN = process.env.ALLOWED_ORIGIN || '*';

fs.mkdirSync(GRIB_DIR, { recursive: true });
fs.mkdirSync(FORECAST_DIR, { recursive: true });

const MIME = {
  '.html': 'text/html; charset=utf-8',
  '.webmanifest': 'application/manifest+json; charset=utf-8',
  '.js': 'text/javascript; charset=utf-8',
  '.json': 'application/json; charset=utf-8',
  '.css': 'text/css; charset=utf-8',
  '.png': 'image/png',
  '.jpg': 'image/jpeg',
  '.jpeg': 'image/jpeg',
  '.svg': 'image/svg+xml',
  '.ico': 'image/x-icon'
};

function send(res, status, body, type = 'text/plain; charset=utf-8', extra = {}) {
  res.writeHead(status, {
    'Content-Type': type,
    'X-Content-Type-Options': 'nosniff',
    'Cache-Control': 'no-store',
    ...extra
  });
  res.end(body);
}

function sendJson(res, status, data, extra = {}) {
  return send(res, status, JSON.stringify(data), 'application/json; charset=utf-8', extra);
}

function readBody(req, limit = MAX_BODY) {
  return new Promise((resolve, reject) => {
    let body = '';
    let tooLarge = false;
    req.on('data', chunk => {
      if (tooLarge) return;
      body += chunk.toString('utf8');
      if (Buffer.byteLength(body, 'utf8') > limit) {
        tooLarge = true;
        reject(Object.assign(new Error('Requête trop volumineuse.'), { statusCode: 413 }));
        req.destroy();
      }
    });
    req.on('end', () => {
      if (!tooLarge) resolve(body);
    });
    req.on('error', error => {
      if (!tooLarge) reject(error);
    });
  });
}

// -----------------------------------------------------------------------------
// Sauvegardes de course
// -----------------------------------------------------------------------------
function readSave() {
  try {
    const data = JSON.parse(fs.readFileSync(SAVE, 'utf8'));
    if (!data || typeof data !== 'object' || !data.races ||
        typeof data.races !== 'object' || Array.isArray(data.races)) {
      return { races: {} };
    }
    return data;
  } catch (_) {
    return { races: {} };
  }
}

function validSave(data) {
  if (!data || typeof data !== 'object' || Array.isArray(data) ||
      !data.races || typeof data.races !== 'object' || Array.isArray(data.races)) return false;

  const allowed = new Set(['rhum', 'atlantic', 'lorient']);
  for (const [race, snap] of Object.entries(data.races)) {
    if (!allowed.has(race) || !snap || typeof snap !== 'object') return false;
    const p = snap.position;
    if (!p || !Number.isFinite(p.lat) || !Number.isFinite(p.lng) ||
        p.lat < -90 || p.lat > 90 || p.lng < -180 || p.lng > 180) return false;
    if (!Number.isFinite(snap.heading) || snap.heading < 0 || snap.heading >= 360) return false;
    if (!Array.isArray(snap.track) || snap.track.length > 5000) return false;
    for (const point of snap.track) {
      if (!point || !Number.isFinite(point.lat) || !Number.isFinite(point.lng) ||
          point.lat < -90 || point.lat > 90 || point.lng < -180 || point.lng > 180) return false;
    }
  }
  return true;
}

function saveAtomically(data) {
  const tmp = SAVE + '.tmp';
  fs.writeFileSync(tmp, JSON.stringify(data), { encoding: 'utf8', mode: 0o600 });
  fs.renameSync(tmp, SAVE);
}

// -----------------------------------------------------------------------------
// NOAA GFS + décodage GRIB2
// Décodeur TypeScript pur : messages NCEP multi-champs et packing GFS 5.3.
// -----------------------------------------------------------------------------
let decoderPromise = null;
let decoderModule = null;
let decoderError = '';

async function getDecoder() {
  if (decoderModule) return decoderModule;
  if (!decoderPromise) {
    decoderPromise = (async () => {
      try {
        const mod = await import('@azohra/meteo.grib');
        const required = ['splitMessages', 'parseFields', 'parseProduct', 'parseGrid', 'decodeFieldValues', 'nearestGridpoint'];
        const missing = required.filter(name => typeof mod[name] !== 'function');
        if (missing.length) {
          throw new Error('API GRIB2 incomplète : ' + missing.join(', '));
        }
        decoderModule = mod;
        decoderError = '';
        console.log('Décodeur GRIB2 @azohra/meteo.grib chargé.');
        return mod;
      } catch (error) {
        decoderError = error && error.message ? error.message : String(error);
        decoderPromise = null;
        throw new Error('Impossible de charger @azohra/meteo.grib. Détail : ' + decoderError);
      }
    })();
  }
  return decoderPromise;
}

const wxStatus = {
  busy: false,
  done: 0,
  total: HOURS.length,
  message: 'En attente',
  cycle: null,
  startedAt: null,
  error: null
};
let lastNoaaRequestAt = 0;
let noaaRequestQueue = Promise.resolve();
const forecastInflight = new Map();
const forecastMemory = new Map();
const localMemory = new Map();


// Les prévisions complètes peuvent prendre plusieurs minutes. Le calcul se fait
// côté serveur et la PWA interroge ensuite l'état de la tâche.
const gfsJobs = new Map();
let activeGfsJob = null;

function startGfsJob(points) {
  const signature = hash(JSON.stringify(points.map(p => [Number(p.lat.toFixed(4)), Number(p.lng.toFixed(4))])));
  const existing = [...gfsJobs.values()].find(job =>
    job.signature === signature && (job.state === 'running' || job.state === 'ready')
  );
  if (existing) return existing;
  if (activeGfsJob && activeGfsJob.state === 'running') {
    throw Object.assign(new Error('Un calcul NOAA est déjà en cours sur le serveur. Attends qu’il se termine avant de lancer une autre course.'), { statusCode: 409 });
  }

  const now = Date.now();
  for (const [id, job] of gfsJobs) {
    if (now - job.createdAt > 2 * 3600000) gfsJobs.delete(id);
  }
  const id = crypto.randomBytes(12).toString('hex');
  const job = { id, signature, state: 'running', message: 'Préparation du calcul NOAA…', createdAt: now, result: null, error: null };
  gfsJobs.set(id, job);
  activeGfsJob = job;

  Promise.resolve().then(() => buildForecast(points)).then(result => {
    job.result = result;
    job.state = 'ready';
    job.message = wxStatus.message || 'Prévisions NOAA prêtes.';
    job.completedAt = Date.now();
  }).catch(error => {
    job.state = 'failed';
    job.error = error.message || String(error);
    job.message = 'Erreur NOAA : ' + job.error;
    job.completedAt = Date.now();
  }).finally(() => {
    if (activeGfsJob === job) activeGfsJob = null;
  });
  return job;
}

function sendGfsJobResult(res, job) {
  if (!job || job.state !== 'ready' || !job.result) {
    return sendJson(res, 409, { error: 'Le résultat NOAA n’est pas encore disponible.' });
  }
  return send(res, 200, job.result.payload, 'application/octet-stream', {
    'Content-Encoding': 'gzip',
    'X-VR-GFS-T0': String(job.result.t0),
    'X-VR-GFS-Cycle': runLabel(job.result.run),
    'X-VR-GFS-Points': String(job.result.points),
    'X-VR-GFS-Hours': String(job.result.hours),
    'X-VR-GFS-Model': job.result.model
  });
}

const delay = ms => new Promise(resolve => setTimeout(resolve, ms));

function hash(value) {
  return crypto.createHash('sha1').update(value).digest('hex').slice(0, 18);
}

function normalizeLon(lon) {
  return ((lon % 360) + 360) % 360;
}

function makeBbox(points) {
  const lats = points.map(p => p.lat);
  const lons = points.map(p => ((p.lng + 180) % 360 + 360) % 360 - 180);
  const minLat = Math.min(...lats);
  const maxLat = Math.max(...lats);
  const minLon = Math.min(...lons);
  const maxLon = Math.max(...lons);
  let west, east;

  // Les longitudes signées permettent de conserver une petite boîte près de
  // Greenwich (-2° à +2°). Seul un trajet traversant l'antiméridien impose
  // une requête mondiale, que NOMADS ne peut pas représenter en une boîte.
  if (maxLon - minLon > 180) {
    west = -180;
    east = 179.75;
  } else {
    west = Math.max(-180, Math.floor((minLon - 0.5) * 4) / 4);
    east = Math.min(179.75, Math.ceil((maxLon + 0.5) * 4) / 4);
  }

  const south = Math.max(-89.75, Math.floor((minLat - 0.5) * 4) / 4);
  const north = Math.min(89.75, Math.ceil((maxLat + 0.5) * 4) / 4);
  const fmt = n => Number(n.toFixed(2));
  const box = { west: fmt(west), east: fmt(east), south: fmt(south), north: fmt(north) };
  box.key = [box.west, box.east, box.south, box.north].join('_').replace(/\./g, 'p').replace(/-/g, 'm');
  return box;
}

function validatePoints(points) {
  if (!Array.isArray(points) || points.length < 1 || points.length > MAX_POINTS) {
    throw Object.assign(new Error('Nombre de points météo invalide (1 à ' + MAX_POINTS + ').'), { statusCode: 400 });
  }
  for (const p of points) {
    if (!p || !Number.isFinite(p.lat) || !Number.isFinite(p.lng) ||
        p.lat < -85 || p.lat > 85 || p.lng < -180 || p.lng > 180) {
      throw Object.assign(new Error('Coordonnée météo invalide.'), { statusCode: 400 });
    }
  }
}

function runCandidates(now = Date.now()) {
  const target = now - 8 * HOUR_MS; // laisse le temps au run GFS de terminer ses 384 h
  const candidates = [];
  const hours = [18, 12, 6, 0];
  for (let back = 0; back <= 2; back++) {
    const d = new Date(target - back * 86400000);
    for (const h of hours) {
      const stamp = Date.UTC(d.getUTCFullYear(), d.getUTCMonth(), d.getUTCDate(), h);
      if (stamp <= target) {
        const date = new Date(stamp);
        const y = date.getUTCFullYear();
        const m = String(date.getUTCMonth() + 1).padStart(2, '0');
        const day = String(date.getUTCDate()).padStart(2, '0');
        candidates.push({ date: `${y}${m}${day}`, cycle: String(h).padStart(2, '0'), stamp });
      }
    }
  }
  candidates.sort((a, b) => b.stamp - a.stamp);
  return candidates;
}

function gribCachePath(run, forecastHour, bbox) {
  const name = `gfs_${run.date}_${run.cycle}_f${String(forecastHour).padStart(3, '0')}_${bbox.key}.grib2`;
  return path.join(GRIB_DIR, name);
}

function requestBuffer(url, redirects = 0) {
  return new Promise((resolve, reject) => {
    const req = https.get(url, {
      headers: {
        'User-Agent': 'Virtual-Regatta-local-weather/13 (NOAA GFS GRIB2)',
        'Accept': 'application/octet-stream,*/*'
      }
    }, response => {
      const code = Number(response.statusCode || 0);
      if ([301, 302, 303, 307, 308].includes(code) && response.headers.location && redirects < 4) {
        const nextUrl = new URL(response.headers.location, url).toString();
        response.resume();
        requestBuffer(nextUrl, redirects + 1).then(resolve, reject);
        return;
      }

      const chunks = [];
      let bytes = 0;
      response.on('data', chunk => {
        bytes += chunk.length;
        if (bytes > 80 * 1024 * 1024) {
          req.destroy(new Error('Fichier GRIB2 trop volumineux (limite locale 80 Mo).'));
          return;
        }
        chunks.push(chunk);
      });
      response.on('end', () => {
        const buffer = Buffer.concat(chunks);
        if (code !== 200) {
          const error = new Error('NOAA NOMADS HTTP ' + code + ' pour ' + new URL(url).searchParams.get('file'));
          error.statusCode = code;
          error.noaaUnavailable = code === 404 || code === 410;
          reject(error);
          return;
        }
        if (buffer.length < 20 || buffer.subarray(0, 4).toString('ascii') !== 'GRIB') {
          const detail = buffer.toString('utf8', 0, Math.min(buffer.length, 180)).replace(/\s+/g, ' ').trim();
          const error = new Error('NOAA n’a pas renvoyé un GRIB2 valide' + (detail ? ' : ' + detail : '.'));
          error.noaaUnavailable = /not available|not found|no data|cannot open|does not exist/i.test(detail);
          reject(error);
          return;
        }
        resolve(buffer);
      });
      response.on('error', reject);
    });
    req.setTimeout(60000, () => req.destroy(new Error('Délai dépassé pendant le téléchargement NOAA.')));
    req.on('error', reject);
  });
}

function buildGribUrl(run, forecastHour, bbox) {
  const file = `gfs.t${run.cycle}z.pgrb2.0p25.f${String(forecastHour).padStart(3, '0')}`;
  const query = new URLSearchParams();
  query.set('file', file);
  query.set('lev_10_m_above_ground', 'on');
  query.set('var_UGRD', 'on');
  query.set('var_VGRD', 'on');
  query.set('subregion', '');
  query.set('leftlon', String(bbox.west));
  query.set('rightlon', String(bbox.east));
  query.set('toplat', String(bbox.north));
  query.set('bottomlat', String(bbox.south));
  query.set('dir', `/gfs.${run.date}/${run.cycle}/atmos`);
  return 'https://nomads.ncep.noaa.gov/cgi-bin/filter_gfs_0p25.pl?' + query.toString();
}

async function getGrib(run, forecastHour, bbox) {
  const file = gribCachePath(run, forecastHour, bbox);
  try {
    const stat = fs.statSync(file);
    if (stat.size > 20 && stat.size < 80 * 1024 * 1024) {
      const cached = fs.readFileSync(file);
      if (cached.subarray(0, 4).toString('ascii') === 'GRIB') return cached;
    }
  } catch (_) {}

  // File d'attente globale : évite que deux workers lancent deux requêtes
  // NOMADS simultanément et respecte l'intervalle de courtoisie.
  let release;
  const previous = noaaRequestQueue;
  noaaRequestQueue = new Promise(resolve => { release = resolve; });
  await previous;
  try {
    const wait = Math.max(0, NOAA_MIN_INTERVAL_MS - (Date.now() - lastNoaaRequestAt));
    if (wait) await delay(wait);
    lastNoaaRequestAt = Date.now();
  } finally {
    release();
  }

  const buffer = await requestBuffer(buildGribUrl(run, forecastHour, bbox));
  const tmp = file + '.tmp';
  fs.writeFileSync(tmp, buffer);
  fs.renameSync(tmp, file);
  return buffer;
}

async function chooseUsableRun(bbox) {
  const candidates = runCandidates();
  let lastError = null;
  for (const run of candidates) {
    try {
      // Le fichier f384 sert de test : il confirme que l'horizon de 16 jours
      // est disponible pour ce cycle. Il est ensuite conservé dans le cache.
      await getGrib(run, 384, bbox);
      await getGrib(run, 0, bbox);
      return run;
    } catch (error) {
      lastError = error;
      if (!error.noaaUnavailable) throw error;
    }
  }
  throw new Error('Aucun cycle GFS NOAA complet trouvé dans les dernières 48 heures. ' +
    (lastError ? lastError.message : 'Réessaie un peu plus tard.'));
}

function matchesWindProduct(product, parameterNumber) {
  if (!product || Number(product.parameterCategory) !== 2 || Number(product.parameterNumber) !== parameterNumber) {
    return false;
  }
  // 103 = height above ground; the NOMADS query explicitly requests 10 m.
  if (product.typeOfFirstFixedSurface !== undefined && Number(product.typeOfFirstFixedSurface) !== 103) return false;
  if (product.scaledValueOfFirstFixedSurface !== undefined && Number(product.scaledValueOfFirstFixedSurface) !== 10) return false;
  return true;
}

function decodeOneField(decoder, field) {
  const grid = decoder.parseGrid(field.section3);
  if (!Number.isInteger(grid.ni) || !Number.isInteger(grid.nj) || grid.ni < 2 || grid.nj < 2) {
    throw new Error('Dimensions de grille GRIB2 invalides.');
  }
  if (grid.uvRelativeToGrid) {
    throw new Error('Le champ de vent NOAA est relatif à la grille ; le GFS régulier attendu doit être relatif au nord vrai.');
  }
  const decoded = decoder.decodeFieldValues(field);
  if (!decoded || !decoded.values || decoded.values.length !== grid.ni * grid.nj) {
    throw new Error('Le décodeur GRIB2 a renvoyé un nombre de valeurs incohérent.');
  }
  return { grid, values: decoded.values, missingValue: decoded.missingValue };
}

async function decodeWindPair(buffer) {
  const decoder = await getDecoder();
  const bytes = new Uint8Array(buffer.buffer, buffer.byteOffset, buffer.byteLength);
  const messages = decoder.splitMessages(bytes);
  let u = null;
  let v = null;
  let fieldCount = 0;

  for (const message of messages) {
    const fields = decoder.parseFields(message);
    fieldCount += fields.length;
    for (const field of fields) {
      const product = decoder.parseProduct(field.section4);
      if (!matchesWindProduct(product, 2) && !matchesWindProduct(product, 3)) continue;

      const parameterNumber = Number(product.parameterNumber);
      if ((parameterNumber === 2 && u) || (parameterNumber === 3 && v)) continue;
      const decoded = decodeOneField(decoder, field);
      if (parameterNumber === 2) u = decoded;
      if (parameterNumber === 3) v = decoded;
      if (u && v) break;
    }
    if (u && v) break;
  }

  if (!u || !v) {
    throw new Error('Les deux champs UGRD/VGRD à 10 m sont absents du GRIB2 NOAA (champs=' + fieldCount + ').');
  }
  if (u.grid.gridKey !== v.grid.gridKey || u.values.length !== v.values.length) {
    throw new Error('Les grilles U et V du GRIB2 NOAA ne correspondent pas.');
  }
  return { u, v };
}

function gribStorageIndex(grid, column, row) {
  // Ordre de stockage GRIB2 (ligne/colonne, balayage alterné éventuel).
  if (grid.jPointsAreConsecutive) {
    if (grid.alternativeRowScanning) {
      return column * grid.nj + (column % 2 === 1 ? grid.nj - 1 - row : row);
    }
    return column * grid.nj + row;
  }
  if (grid.alternativeRowScanning) {
    return row * grid.ni + (row % 2 === 1 ? grid.ni - 1 - column : column);
  }
  return row * grid.ni + column;
}

function sampleField(field, point) {
  const decoder = decoderModule;
  const grid = field.grid;
  if (!decoder || !grid || grid.kind !== 'latlon') return null;

  // Garde-fou géographique : le point doit être proche de la grille NOAA.
  const nearest = decoder.nearestGridpoint(grid, point.lat, point.lng);
  if (!nearest || !Number.isInteger(nearest.index) || nearest.index < 0 ||
      nearest.index >= field.values.length || !Number.isFinite(nearest.distanceKm) || nearest.distanceKm > 35) {
    return null;
  }

  // Coordonnées fractionnaires dans la grille régulière GFS 0,25°.
  const iSign = grid.iScansNegatively ? -1 : 1;
  const jStep = grid.jScansPositively ? grid.jDirectionIncrement : -grid.jDirectionIncrement;
  // Normalisation nécessaire près de Greenwich : le GRIB peut encoder 357°
  // alors que le simulateur exprime la même longitude sous la forme -3°.
  let lonDelta = (((point.lng - grid.longitudeOfFirstGridPoint) * iSign) % 360 + 360) % 360;
  const iWraps = grid.ni * grid.iDirectionIncrement >= 360 - grid.iDirectionIncrement * 0.5;
  const column = lonDelta / grid.iDirectionIncrement;
  const row = (point.lat - grid.latitudeOfFirstGridPoint) / jStep;

  if (!Number.isFinite(column) || !Number.isFinite(row) ||
      (!iWraps && (column < -1e-4 || column > grid.ni - 1 + 1e-4)) ||
      row < -1e-4 || row > grid.nj - 1 + 1e-4) return null;

  const c = Math.max(0, Math.min(iWraps ? grid.ni - 1 : grid.ni - 1, column));
  const r = Math.max(0, Math.min(grid.nj - 1, row));
  let c0 = Math.floor(c);
  let r0 = Math.floor(r);
  let tx = c - c0;
  let ty = r - r0;
  let c1 = c0 + 1;
  let r1 = r0 + 1;

  if (c1 >= grid.ni) {
    if (iWraps) c1 = 0;
    else { c0 = grid.ni - 2; c1 = grid.ni - 1; tx = 1; }
  }
  if (r1 >= grid.nj) { r0 = grid.nj - 2; r1 = grid.nj - 1; ty = 1; }

  const a = Number(field.values[gribStorageIndex(grid, c0, r0)]);
  const b = Number(field.values[gribStorageIndex(grid, c1, r0)]);
  const cValue = Number(field.values[gribStorageIndex(grid, c0, r1)]);
  const d = Number(field.values[gribStorageIndex(grid, c1, r1)]);
  const valid = value => Number.isFinite(value) && Math.abs(value) < 9000;
  if (![a, b, cValue, d].every(valid)) return null;

  const top = a + (b - a) * tx;
  const bottom = cValue + (d - cValue) * tx;
  return top + (bottom - top) * ty;
}

async function mapLimit(items, limit, worker) {
  let next = 0;
  const workers = Array.from({ length: Math.min(limit, items.length) }, async () => {
    while (true) {
      const index = next++;
      if (index >= items.length) return;
      await worker(items[index], index);
    }
  });
  await Promise.all(workers);
}

function runLabel(run) {
  return `${run.date} ${run.cycle}Z`;
}

function forecastFiles(pointKey) {
  return {
    data: path.join(FORECAST_DIR, `forecast_${pointKey}.gz`),
    meta: path.join(FORECAST_DIR, `forecast_${pointKey}.json`)
  };
}

function readForecastCache(pointKey) {
  const files = forecastFiles(pointKey);
  try {
    const meta = JSON.parse(fs.readFileSync(files.meta, 'utf8'));
    if (!meta || !Number.isFinite(meta.savedAt) || Date.now() - meta.savedAt > 5.5 * 3600000) return null;
    const payload = fs.readFileSync(files.data);
    if (!payload.length) return null;
    return { ...meta, payload };
  } catch (_) {
    return null;
  }
}

function writeForecastCache(pointKey, result) {
  const files = forecastFiles(pointKey);
  const tmpData = files.data + '.tmp';
  const tmpMeta = files.meta + '.tmp';
  fs.writeFileSync(tmpData, result.payload);
  fs.writeFileSync(tmpMeta, JSON.stringify({
    t0: result.t0,
    run: result.run,
    points: result.points,
    hours: result.hours,
    model: result.model,
    savedAt: result.savedAt
  }));
  fs.renameSync(tmpData, files.data);
  fs.renameSync(tmpMeta, files.meta);
}

async function buildForecast(points) {
  validatePoints(points);
  const pointKey = hash(JSON.stringify(points.map(p => [Number(p.lat.toFixed(4)), Number(p.lng.toFixed(4))])));

  const inMemory = forecastMemory.get(pointKey);
  if (inMemory && Date.now() - inMemory.savedAt < 5.5 * 3600000) {
    wxStatus.message = `Prévisions NOAA GFS servies depuis le cache mémoire · ${runLabel(inMemory.run)}`;
    return inMemory;
  }
  const onDisk = readForecastCache(pointKey);
  if (onDisk) {
    forecastMemory.set(pointKey, onDisk);
    wxStatus.message = `Prévisions NOAA GFS servies depuis le cache disque · ${runLabel(onDisk.run)}`;
    return onDisk;
  }
  if (forecastInflight.has(pointKey)) return forecastInflight.get(pointKey);

  const bbox = makeBbox(points);
  const job = (async () => {
    wxStatus.busy = true;
    wxStatus.done = 0;
    wxStatus.total = NATIVE_COUNT + 2;
    wxStatus.message = 'Recherche d’un cycle NOAA GFS complet…';
    wxStatus.cycle = null;
    wxStatus.startedAt = Date.now();
    wxStatus.error = null;

    try {
      const run = await chooseUsableRun(bbox);
      wxStatus.cycle = runLabel(run);
      wxStatus.done = 2; // test des fichiers f000 et f384 effectué lors du choix du cycle
      const nativeU = new Float32Array(points.length * NATIVE_COUNT);
      const nativeV = new Float32Array(points.length * NATIVE_COUNT);

      // NOMADS recommande une pause entre les requêtes automatisées.
      // Un seul téléchargement à la fois évite de surcharger le service NOAA.
      await mapLimit(HOURS, 1, async (forecastHour, nativeIndex) => {
        wxStatus.message = `NOAA GFS ${runLabel(run)} · échéance f${String(forecastHour).padStart(3, '0')} (${wxStatus.done + 1}/${wxStatus.total})`;
        const grib = await getGrib(run, forecastHour, bbox);
        const pair = await decodeWindPair(grib);
        for (let i = 0; i < points.length; i++) {
          const east = sampleField(pair.u, points[i]);
          const north = sampleField(pair.v, points[i]);
          if (!Number.isFinite(east) || !Number.isFinite(north)) {
            throw new Error('Un point de la grille de jeu est hors de la sous-région GRIB2 NOAA.');
          }
          const index = i * NATIVE_COUNT + nativeIndex;
          nativeU[index] = east * MPS_TO_KNOTS;
          nativeV[index] = north * MPS_TO_KNOTS;
        }
        wxStatus.done++;
      });

      wxStatus.message = 'Interpolation horaire des composantes U/V…';
      const count = points.length * GAME_HOURS;
      const hourlyU = new Float32Array(count);
      const hourlyV = new Float32Array(count);

      for (let p = 0; p < points.length; p++) {
        const nativeBase = p * NATIVE_COUNT;
        const hourlyBase = p * GAME_HOURS;
        // Les 48 heures avant le cycle sont remplies par f000 : l'axe
        // temporel du jeu conserve ainsi sa marge historique de 2 jours.
        for (let h = 0; h < PRE_HOURS; h++) {
          hourlyU[hourlyBase + h] = nativeU[nativeBase];
          hourlyV[hourlyBase + h] = nativeV[nativeBase];
        }
        for (let lead = 0; lead <= 384; lead++) {
          const low = Math.floor(lead / 3);
          const high = Math.min(NATIVE_COUNT - 1, low + 1);
          const t = (lead - low * 3) / 3;
          const u0 = nativeU[nativeBase + low];
          const u1 = nativeU[nativeBase + high];
          const v0 = nativeV[nativeBase + low];
          const v1 = nativeV[nativeBase + high];
          const target = hourlyBase + PRE_HOURS + lead;
          hourlyU[target] = u0 + (u1 - u0) * t;
          hourlyV[target] = v0 + (v1 - v0) * t;
        }
      }

      const raw = Buffer.allocUnsafe(count * 8);
      Buffer.from(hourlyU.buffer, hourlyU.byteOffset, hourlyU.byteLength).copy(raw, 0);
      Buffer.from(hourlyV.buffer, hourlyV.byteOffset, hourlyV.byteLength).copy(raw, count * 4);
      const payload = zlib.gzipSync(raw, { level: 1 });
      const result = {
        payload,
        t0: run.stamp - PRE_HOURS * HOUR_MS,
        run,
        points: points.length,
        hours: GAME_HOURS,
        model: 'NOAA GFS 0.25° · U/V 10 m · interpolation horaire',
        savedAt: Date.now()
      };
      writeForecastCache(pointKey, result);
      forecastMemory.clear();
      forecastMemory.set(pointKey, result);
      wxStatus.message = `Prévisions NOAA GFS prêtes · ${points.length} points · cycle ${runLabel(run)}`;
      wxStatus.done = wxStatus.total;
      return result;
    } catch (error) {
      wxStatus.error = error.message || String(error);
      wxStatus.message = 'Erreur NOAA GFS : ' + wxStatus.error;
      throw error;
    } finally {
      wxStatus.busy = false;
      forecastInflight.delete(pointKey);
    }
  })();

  forecastInflight.set(pointKey, job);
  return job;
}

function windFromUV(u, v) {
  const speed = Math.hypot(u, v);
  const direction = (Math.atan2(-u, -v) / DEG + 360) % 360;
  return { u, v, speed, direction };
}

async function buildLocalWind(lat, lng, targetTime = Date.now()) {
  const points = [];
  for (let row = -1; row <= 1; row++) {
    for (let col = -1; col <= 1; col++) {
      points.push({ lat: Math.max(-84.5, Math.min(84.5, lat + row)), lng: Math.max(-179.5, Math.min(179.5, lng + col)) });
    }
  }
  const bbox = makeBbox(points);
  const validTarget = Number.isFinite(targetTime) ? targetTime : Date.now();
  const candidates = runCandidates();
  let selected = null;
  let lastError = null;

  // Pour le vent instantané du départ, inutile de tester tout le f384 :
  // on cherche directement le premier fichier qui couvre l'heure virtuelle.
  for (const run of candidates) {
    const ageHours = Math.max(0, (validTarget - run.stamp) / HOUR_MS);
    const forecastHour = Math.max(0, Math.min(384, Math.round(ageHours / 3) * 3));
    try {
      const grib = await getGrib(run, forecastHour, bbox);
      selected = { run, forecastHour, grib };
      break;
    } catch (error) {
      lastError = error;
      if (!error.noaaUnavailable) throw error;
    }
  }
  if (!selected) throw new Error('Aucun champ de vent NOAA récent disponible. ' + (lastError?.message || ''));

  const { run, forecastHour, grib } = selected;
  const cacheKey = `${run.date}${run.cycle}_f${forecastHour}_${bbox.key}_${lat.toFixed(2)}_${lng.toFixed(2)}`;
  const old = localMemory.get(cacheKey);
  if (old && Date.now() - old.at < 10 * 60 * 1000) return old.value;

  const pair = await decodeWindPair(grib);
  const winds = points.map(point => {
    const u = sampleField(pair.u, point);
    const v = sampleField(pair.v, point);
    if (!Number.isFinite(u) || !Number.isFinite(v)) throw new Error('Point météo local hors de la grille NOAA.');
    return windFromUV(u * MPS_TO_KNOTS, v * MPS_TO_KNOTS);
  });
  const value = {
    provider: 'NOAA GFS', resolution: '0.25°', cycle: runLabel(run),
    forecastHour, validTime: run.stamp + forecastHour * HOUR_MS,
    points, winds
  };
  localMemory.set(cacheKey, { at: Date.now(), value });
  return value;
}

function purgeOldGribCache() {
  const cutoff = Date.now() - 3 * 86400000;
  for (const folder of [GRIB_DIR, FORECAST_DIR]) {
    try {
      for (const name of fs.readdirSync(folder)) {
        const full = path.join(folder, name);
        try {
          const stat = fs.statSync(full);
          if (stat.isFile() && stat.mtimeMs < cutoff) fs.unlinkSync(full);
        } catch (_) {}
      }
    } catch (_) {}
  }
}

purgeOldGribCache();

// -----------------------------------------------------------------------------
// Routes HTTP
// -----------------------------------------------------------------------------
const server = http.createServer(async (req, res) => {
  let requestUrl;
  try {
    requestUrl = new URL(req.url, `http://${req.headers.host || 'localhost'}`);
  } catch (_) {
    return send(res, 400, 'Bad Request');
  }

  // CORS : le site (GitHub Pages) et l'API (Render) sont sur deux domaines différents.
  res.setHeader('Access-Control-Allow-Origin', ALLOWED_ORIGIN);
  res.setHeader('Vary', 'Origin');
  res.setHeader('Access-Control-Allow-Methods', 'GET, POST, PUT, DELETE, OPTIONS');
  res.setHeader('Access-Control-Allow-Headers', 'Content-Type');
  res.setHeader('Access-Control-Expose-Headers', 'X-VR-GFS-T0, X-VR-GFS-Cycle, X-VR-GFS-Points, X-VR-GFS-Hours, X-VR-GFS-Model, X-VR-Weather-Source');
  res.setHeader('Access-Control-Max-Age', '86400');
  if (req.method === 'OPTIONS') { res.writeHead(204); return res.end(); }

  if (requestUrl.pathname === '/api/save') {
    if (req.method === 'GET') return sendJson(res, 200, readSave());
    if (req.method === 'PUT' || req.method === 'POST') {
      try {
        const data = JSON.parse((await readBody(req)) || '{}');
        if (!validSave(data)) return sendJson(res, 400, { ok: false, error: 'invalid_save_format' });
        saveAtomically(data);
        return sendJson(res, 200, { ok: true });
      } catch (error) {
        return sendJson(res, error.statusCode || 400, { ok: false, error: error.message || 'invalid_json' });
      }
    }
    res.setHeader('Allow', 'GET, PUT, POST');
    return send(res, 405, 'Method Not Allowed');
  }

  if (requestUrl.pathname === '/api/gfs/status') {
    if (req.method !== 'GET') return send(res, 405, 'Method Not Allowed');
    return sendJson(res, 200, {
      provider: 'NOAA GFS', resolution: '0.25°', nativeStepHours: 3,
      forecastHours: 384, hourlyValues: GAME_HOURS,
      decoderAvailable: !!decoderModule,
      decoderError: decoderError || null,
      busy: wxStatus.busy, done: wxStatus.done, total: wxStatus.total,
      message: wxStatus.message, cycle: wxStatus.cycle,
      startedAt: wxStatus.startedAt, error: wxStatus.error
    });
  }

  if (requestUrl.pathname === '/api/gfs/local') {
    if (req.method !== 'GET') return send(res, 405, 'Method Not Allowed');
    const lat = Number(requestUrl.searchParams.get('lat'));
    const lng = Number(requestUrl.searchParams.get('lng'));
    const targetTime = Number(requestUrl.searchParams.get('time'));
    if (!Number.isFinite(lat) || !Number.isFinite(lng) || lat < -85 || lat > 85 || lng < -180 || lng > 180) {
      return sendJson(res, 400, { ok: false, error: 'Coordonnées lat/lng invalides.' });
    }
    try {
      const result = await buildLocalWind(lat, lng, Number.isFinite(targetTime) ? targetTime : Date.now());
      return sendJson(res, 200, result, { 'X-VR-Weather-Source': 'NOAA-GFS' });
    } catch (error) {
      console.error('NOAA GFS local:', error.message);
      return sendJson(res, error.statusCode || 502, { ok: false, error: error.message || 'NOAA GFS indisponible.' });
    }
  }


  if (requestUrl.pathname === '/api/gfs/start') {
    if (req.method !== 'POST') return send(res, 405, 'Method Not Allowed');
    try {
      const body = JSON.parse((await readBody(req)) || '{}');
      validatePoints(body.points);
      const job = startGfsJob(body.points);
      return sendJson(res, 202, { jobId: job.id, state: job.state, message: job.message });
    } catch (error) {
      return sendJson(res, error.statusCode || 400, { ok: false, error: error.message || 'Impossible de démarrer le calcul NOAA.' });
    }
  }

  const gfsJobMatch = requestUrl.pathname.match(/^\/api\/gfs\/jobs\/([a-f0-9]{24})(?:\/(result))?$/);
  if (gfsJobMatch) {
    const job = gfsJobs.get(gfsJobMatch[1]);
    if (!job) return sendJson(res, 404, { error: 'Calcul NOAA introuvable ou expiré.' });
    if (gfsJobMatch[2] === 'result') {
      if (req.method !== 'GET') return send(res, 405, 'Method Not Allowed');
      return sendGfsJobResult(res, job);
    }
    if (req.method !== 'GET') return send(res, 405, 'Method Not Allowed');
    return sendJson(res, 200, {
      jobId: job.id,
      state: job.state,
      done: wxStatus.done,
      total: wxStatus.total,
      message: job.state === 'running' ? wxStatus.message : job.message,
      cycle: wxStatus.cycle,
      error: job.error,
      createdAt: job.createdAt,
      completedAt: job.completedAt || null
    });
  }

  if (requestUrl.pathname === '/api/gfs') {
    if (req.method !== 'POST') return send(res, 405, 'Method Not Allowed');
    try {
      const body = JSON.parse((await readBody(req)) || '{}');
      validatePoints(body.points);
      const result = await buildForecast(body.points);
      return send(res, 200, result.payload, 'application/octet-stream', {
        'Content-Encoding': 'gzip',
        'X-VR-GFS-T0': String(result.t0),
        'X-VR-GFS-Cycle': runLabel(result.run),
        'X-VR-GFS-Points': String(result.points),
        'X-VR-GFS-Hours': String(result.hours),
        'X-VR-GFS-Model': result.model
      });
    } catch (error) {
      console.error('NOAA GFS forecast:', error.message);
      return sendJson(res, error.statusCode || 502, { ok: false, error: error.message || 'Prévisions NOAA indisponibles.' });
    }
  }

  if (requestUrl.pathname === '/api/gfs/cache') {
    if (req.method !== 'DELETE') return send(res, 405, 'Method Not Allowed');
    try {
      for (const folder of [GRIB_DIR, FORECAST_DIR]) {
        for (const name of fs.readdirSync(folder)) {
          const full = path.join(folder, name);
          try { if (fs.statSync(full).isFile()) fs.unlinkSync(full); } catch (_) {}
        }
      }
      forecastMemory.clear();
      localMemory.clear();
      return sendJson(res, 200, { ok: true, message: 'Cache GRIB2 NOAA vidé.' });
    } catch (error) {
      return sendJson(res, 500, { ok: false, error: error.message });
    }
  }

  if (req.method !== 'GET' && req.method !== 'HEAD') return send(res, 405, 'Method Not Allowed');

  let pathname;
  try { pathname = decodeURIComponent(requestUrl.pathname); }
  catch (_) { return send(res, 400, 'Bad Request'); }
  if (pathname === '/') pathname = '/' + DEFAULT_PAGE;

  const requested = path.resolve(DIR, '.' + pathname);
  const relative = path.relative(DIR, requested);
  if (!relative || relative.startsWith('..') || path.isAbsolute(relative) ||
      path.basename(requested) === 'save.json' || requested.startsWith(WEATHER_DIR + path.sep)) {
    return send(res, 403, 'Forbidden');
  }

  fs.readFile(requested, (error, contents) => {
    if (error) {
      return send(res, error.code === 'ENOENT' ? 404 : 500,
        error.code === 'ENOENT' ? '404 — Fichier introuvable' : 'Erreur serveur');
    }
    const type = MIME[path.extname(requested).toLowerCase()] || 'application/octet-stream';
    res.writeHead(200, {
      'Content-Type': type,
      'X-Content-Type-Options': 'nosniff',
      'Cache-Control': type.startsWith('text/html') ? 'no-cache' : 'public, max-age=3600'
    });
    if (req.method === 'HEAD') return res.end();
    res.end(contents);
  });
});

server.listen(PORT, HOST, () => {
  console.log(`Virtual Regatta NOAA GFS PWA : http://${HOST}:${PORT}`);
  console.log(`Page d'accueil : ${DEFAULT_PAGE}`);
  console.log('Météo : NOAA GFS 0,25° · GRIB2 · U/V à 10 m');
  console.log('Décodeur GRIB2 : ' + (decoderModule ? 'prêt' : 'sera chargé à la première requête météo'));
  console.log('Intervalle NOMADS : ' + (NOAA_MIN_INTERVAL_MS / 1000) + ' s entre deux téléchargements.');
  console.log('Cache météo local : ' + WEATHER_DIR);
});

server.on('error', error => {
  if (error.code === 'EADDRINUSE') {
    console.error(`Le port ${PORT} est déjà utilisé. Essaie PORT=3001 node server.js`);
  } else {
    console.error('Erreur serveur :', error.message);
  }
  process.exitCode = 1;
});
