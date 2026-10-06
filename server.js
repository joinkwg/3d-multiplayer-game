require('dotenv').config();
const path = require('path');
const http = require('http');
const express = require('express');
const { Server } = require('socket.io');
const { Pool } = require('pg');
const bcrypt = require('bcryptjs');
const crypto = require('crypto');

const PORT = Number(process.env.PORT || 3000);
const DATABASE_URL = process.env.DATABASE_URL;
if (!DATABASE_URL) throw new Error('DATABASE_URL is required.');

const SUPABASE_URL = String(process.env.SUPABASE_URL || '').replace(/\/+$/, '');
const SUPABASE_SERVICE_ROLE_KEY = String(process.env.SUPABASE_SERVICE_ROLE_KEY || '');
const SUPABASE_STORE_BUCKET = String(process.env.SUPABASE_STORE_BUCKET || 'store-assets');
const STORE_CATEGORIES = new Set(['eyes','mouth','torso_decal','hat','head_shape']);

const pool = new Pool({
  connectionString: DATABASE_URL,
  ssl: process.env.PGSSL === 'disable' ? false : { rejectUnauthorized: false }
});

const app = express();
const server = http.createServer(app);
const io = new Server(server, { maxHttpBufferSize: 10 * 1024 * 1024 });

app.use(express.static(path.join(__dirname, 'public')));
app.get('/health', (_req, res) => res.json({ ok: true }));

const defaultAppearance = {
  hat: 'none',
  headShape: 'sphere',
  headColor: '#f3ff00',
  torsoColor: '#0015ff',
  leftArmColor: '#0015ff',
  rightArmColor: '#0015ff',
  leftLegColor: '#000000',
  rightLegColor: '#000000',
  eyesItemId: null,
  mouthItemId: null,
  torsoDecalItemId: null,
  hatItemId: null,
  headShapeItemId: null
};

function cleanUsername(v) {
  return String(v || '').trim().slice(0, 16);
}
function cleanWorldName(v) {
  return String(v || '').trim().slice(0, 20);
}
function validColor(v) {
  return typeof v === 'string' && /^#[0-9a-fA-F]{6}$/.test(v);
}
function cleanStoreItemId(v) {
  const n = Number(v);
  return Number.isInteger(n) && n > 0 ? n : null;
}
function sanitizeAppearance(a = {}) {
  return {
    hat: ['none','black_tophat','blue_tophat','red_tophat','pink_tophat','pink_bow','blue_bow','white_bow','black_cat_ears','pink_cat_ears'].includes(a.hat) ? a.hat : defaultAppearance.hat,
    headShape: ['sphere','cube','cylinder','headless'].includes(a.headShape) ? a.headShape : defaultAppearance.headShape,
    headColor: validColor(a.headColor) ? a.headColor : defaultAppearance.headColor,
    torsoColor: validColor(a.torsoColor) ? a.torsoColor : defaultAppearance.torsoColor,
    leftArmColor: validColor(a.leftArmColor) ? a.leftArmColor : defaultAppearance.leftArmColor,
    rightArmColor: validColor(a.rightArmColor) ? a.rightArmColor : defaultAppearance.rightArmColor,
    leftLegColor: validColor(a.leftLegColor) ? a.leftLegColor : defaultAppearance.leftLegColor,
    rightLegColor: validColor(a.rightLegColor) ? a.rightLegColor : defaultAppearance.rightLegColor,
    eyesItemId: cleanStoreItemId(a.eyesItemId),
    mouthItemId: cleanStoreItemId(a.mouthItemId),
    torsoDecalItemId: cleanStoreItemId(a.torsoDecalItemId),
    hatItemId: cleanStoreItemId(a.hatItemId),
    headShapeItemId: cleanStoreItemId(a.headShapeItemId)
  };
}

function rowToStoreItem(row) {
  return {
    id: Number(row.id),
    category: row.category,
    name: row.name,
    price: Number(row.price || 0),
    assetUrl: row.asset_url,
    assetKind: row.asset_kind,
    metadata: row.metadata || {},
    isVisible: !!row.is_visible
  };
}

async function validateAppearanceForUser(userId, rawAppearance = {}) {
  const app = sanitizeAppearance(rawAppearance);
  const slots = [
    ['eyesItemId', 'eyes'],
    ['mouthItemId', 'mouth'],
    ['torsoDecalItemId', 'torso_decal'],
    ['hatItemId', 'hat'],
    ['headShapeItemId', 'head_shape']
  ];
  const ids = [...new Set(slots.map(([slot]) => app[slot]).filter(Boolean))];
  if (!ids.length) return app;

  const r = await pool.query(`
    SELECT s.id, s.category
    FROM store_items s
    JOIN user_store_items o ON o.item_id=s.id
    WHERE o.user_id=$1 AND s.id = ANY($2::bigint[])
  `, [userId, ids]);
  const owned = new Map(r.rows.map(row => [Number(row.id), row.category]));
  for (const [slot, category] of slots) {
    const id = app[slot];
    if (id && owned.get(id) !== category) app[slot] = null;
  }
  return app;
}

async function resolveAppearanceAssets(app = {}) {
  const slotToCategory = {
    eyesItemId: 'eyes',
    mouthItemId: 'mouth',
    torsoDecalItemId: 'torso_decal',
    hatItemId: 'hat',
    headShapeItemId: 'head_shape'
  };
  const ids = [...new Set(Object.keys(slotToCategory).map(k => cleanStoreItemId(app[k])).filter(Boolean))];
  if (!ids.length) return {};
  const r = await pool.query(`
    SELECT id,category,name,price,asset_url,asset_kind,metadata,is_visible
    FROM store_items WHERE id = ANY($1::bigint[])
  `, [ids]);
  const byId = new Map(r.rows.map(row => [Number(row.id), rowToStoreItem(row)]));
  const out = {};
  for (const [slot, category] of Object.entries(slotToCategory)) {
    const id = cleanStoreItemId(app[slot]);
    const item = id ? byId.get(id) : null;
    if (item && item.category === category) out[category] = item;
  }
  return out;
}

function storeStorageConfigured() {
  return !!(SUPABASE_URL && SUPABASE_SERVICE_ROLE_KEY && SUPABASE_STORE_BUCKET);
}

function storageHeaders(extra = {}) {
  return {
    apikey: SUPABASE_SERVICE_ROLE_KEY,
    Authorization: `Bearer ${SUPABASE_SERVICE_ROLE_KEY}`,
    ...extra
  };
}

async function ensureStoreBucket() {
  if (!storeStorageConfigured()) throw new Error('Store uploads are not configured on the server yet.');
  const bucketId = encodeURIComponent(SUPABASE_STORE_BUCKET);
  const check = await fetch(`${SUPABASE_URL}/storage/v1/bucket/${bucketId}`, {
    headers: storageHeaders()
  });
  if (check.ok) return;
  if (check.status !== 404) throw new Error(`Could not check store bucket (${check.status}).`);
  const create = await fetch(`${SUPABASE_URL}/storage/v1/bucket`, {
    method: 'POST',
    headers: storageHeaders({ 'Content-Type': 'application/json' }),
    body: JSON.stringify({ id: SUPABASE_STORE_BUCKET, name: SUPABASE_STORE_BUCKET, public: true })
  });
  if (!create.ok && create.status !== 409) {
    const text = await create.text().catch(() => '');
    throw new Error(`Could not create store bucket (${create.status}) ${text}`.trim());
  }
}

function fileBufferFromSocket(value) {
  if (!value) return null;
  if (Buffer.isBuffer(value)) return value;
  if (value instanceof ArrayBuffer) return Buffer.from(value);
  if (ArrayBuffer.isView(value)) return Buffer.from(value.buffer, value.byteOffset, value.byteLength);
  if (value && value.type === 'Buffer' && Array.isArray(value.data)) return Buffer.from(value.data);
  return null;
}

function cleanUploadMeta(category, raw = {}) {
  const clamp = (v, min, max, fallback) => {
    const n = Number(v);
    return Number.isFinite(n) ? Math.max(min, Math.min(max, n)) : fallback;
  };
  if (category === 'hat' || category === 'head_shape') {
    return {
      size: clamp(raw.size, 0.05, 10, 1),
      offsetX: clamp(raw.offsetX, -5, 5, 0),
      offsetY: clamp(raw.offsetY, -5, 5, 0),
      offsetZ: clamp(raw.offsetZ, -5, 5, 0)
    };
  }
  return {};
}

async function uploadStoreAsset({ category, fileName, mimeType, buffer }) {
  await ensureStoreBucket();
  const isImage = ['eyes','mouth','torso_decal'].includes(category);
  const lowerName = String(fileName || '').toLowerCase();
  let ext;
  let contentType;
  if (isImage) {
    const allowed = new Map([
      ['image/png', 'png'],
      ['image/jpeg', 'jpg'],
      ['image/webp', 'webp']
    ]);
    ext = allowed.get(String(mimeType || '').toLowerCase());
    if (!ext) {
      if (lowerName.endsWith('.png')) { ext = 'png'; contentType = 'image/png'; }
      else if (lowerName.endsWith('.jpg') || lowerName.endsWith('.jpeg')) { ext = 'jpg'; contentType = 'image/jpeg'; }
      else if (lowerName.endsWith('.webp')) { ext = 'webp'; contentType = 'image/webp'; }
    }
    contentType = contentType || String(mimeType || '').toLowerCase();
    if (!ext) throw new Error('Eyes, mouths, and torso decals must be PNG, JPG, or WebP images.');
    if (buffer.length > 3 * 1024 * 1024) throw new Error('Image files must be 3 MB or smaller.');
  } else {
    if (!lowerName.endsWith('.glb')) throw new Error('Hat and head shape meshes must be .glb files.');
    ext = 'glb';
    contentType = 'model/gltf-binary';
    if (buffer.length > 8 * 1024 * 1024) throw new Error('Mesh files must be 8 MB or smaller.');
  }

  const pathName = `${category}/${Date.now()}-${crypto.randomBytes(8).toString('hex')}.${ext}`;
  const encodedPath = pathName.split('/').map(encodeURIComponent).join('/');
  const bucketId = encodeURIComponent(SUPABASE_STORE_BUCKET);
  const upload = await fetch(`${SUPABASE_URL}/storage/v1/object/${bucketId}/${encodedPath}`, {
    method: 'POST',
    headers: storageHeaders({
      'Content-Type': contentType || 'application/octet-stream',
      'x-upsert': 'false'
    }),
    body: buffer
  });
  if (!upload.ok) {
    const text = await upload.text().catch(() => '');
    throw new Error(`Asset upload failed (${upload.status}) ${text}`.trim());
  }
  return `${SUPABASE_URL}/storage/v1/object/public/${bucketId}/${encodedPath}`;
}

const socketsByUser = new Map();
const playersBySocket = new Map();

function requireAuth(socket, cb) {
  if (!socket.user) {
    if (cb) cb({ success: false, message: 'You must be logged in.' });
    return false;
  }
  return true;
}
function requireAdmin(socket, cb) {
  if (!requireAuth(socket, cb)) return false;
  if (!(socket.user.isAdmin || socket.user.is_admin)) {
    cb && cb({ success: false, message: 'Admin access required.' });
    return false;
  }
  return true;
}

async function migrate() {
  await pool.query(`
    CREATE TABLE IF NOT EXISTS users (
      id BIGSERIAL PRIMARY KEY,
      username VARCHAR(16) UNIQUE NOT NULL,
      password_hash TEXT NOT NULL,
      appearance JSONB NOT NULL DEFAULT '{}'::jsonb,
      is_admin BOOLEAN NOT NULL DEFAULT FALSE,
      coins INTEGER NOT NULL DEFAULT 100,
      created_at TIMESTAMPTZ NOT NULL DEFAULT NOW()
    );
    CREATE TABLE IF NOT EXISTS worlds (
      id BIGSERIAL PRIMARY KEY,
      name VARCHAR(20) UNIQUE NOT NULL,
      owner_user_id BIGINT REFERENCES users(id) ON DELETE SET NULL,
      data JSONB NOT NULL,
      created_at TIMESTAMPTZ NOT NULL DEFAULT NOW(),
      updated_at TIMESTAMPTZ NOT NULL DEFAULT NOW()
    );
    CREATE TABLE IF NOT EXISTS chat_messages (
      id BIGSERIAL PRIMARY KEY,
      world_id BIGINT NOT NULL REFERENCES worlds(id) ON DELETE CASCADE,
      user_id BIGINT REFERENCES users(id) ON DELETE SET NULL,
      username VARCHAR(16) NOT NULL,
      message VARCHAR(300) NOT NULL,
      created_at TIMESTAMPTZ NOT NULL DEFAULT NOW()
    );

    ALTER TABLE users ADD COLUMN IF NOT EXISTS coins INTEGER NOT NULL DEFAULT 100;

    CREATE TABLE IF NOT EXISTS store_items (
      id BIGSERIAL PRIMARY KEY,
      category VARCHAR(32) NOT NULL CHECK (category IN ('eyes','mouth','torso_decal','hat','head_shape')),
      name VARCHAR(40) NOT NULL,
      price INTEGER NOT NULL CHECK (price >= 0),
      asset_url TEXT NOT NULL,
      asset_kind VARCHAR(16) NOT NULL CHECK (asset_kind IN ('image','glb')),
      metadata JSONB NOT NULL DEFAULT '{}'::jsonb,
      is_visible BOOLEAN NOT NULL DEFAULT TRUE,
      created_by BIGINT REFERENCES users(id) ON DELETE SET NULL,
      created_at TIMESTAMPTZ NOT NULL DEFAULT NOW(),
      updated_at TIMESTAMPTZ NOT NULL DEFAULT NOW()
    );

    CREATE TABLE IF NOT EXISTS user_store_items (
      user_id BIGINT NOT NULL REFERENCES users(id) ON DELETE CASCADE,
      item_id BIGINT NOT NULL REFERENCES store_items(id) ON DELETE CASCADE,
      purchased_at TIMESTAMPTZ NOT NULL DEFAULT NOW(),
      PRIMARY KEY (user_id, item_id)
    );

    CREATE TABLE IF NOT EXISTS world_templates (
      id BIGSERIAL PRIMARY KEY,
      name VARCHAR(40) UNIQUE NOT NULL,
      source_world_id BIGINT REFERENCES worlds(id) ON DELETE SET NULL,
      data JSONB NOT NULL,
      created_by BIGINT REFERENCES users(id) ON DELETE SET NULL,
      created_at TIMESTAMPTZ NOT NULL DEFAULT NOW(),
      updated_at TIMESTAMPTZ NOT NULL DEFAULT NOW()
    );

    CREATE TABLE IF NOT EXISTS auth_sessions (
      token_hash TEXT PRIMARY KEY,
      user_id BIGINT NOT NULL REFERENCES users(id) ON DELETE CASCADE,
      expires_at TIMESTAMPTZ NOT NULL,
      created_at TIMESTAMPTZ NOT NULL DEFAULT NOW()
    );

    CREATE TABLE IF NOT EXISTS world_likes (
      world_id BIGINT NOT NULL REFERENCES worlds(id) ON DELETE CASCADE,
      user_id BIGINT NOT NULL REFERENCES users(id) ON DELETE CASCADE,
      created_at TIMESTAMPTZ NOT NULL DEFAULT NOW(),
      PRIMARY KEY (world_id, user_id)
    );

    CREATE INDEX IF NOT EXISTS auth_sessions_user_idx ON auth_sessions(user_id);
    CREATE INDEX IF NOT EXISTS auth_sessions_expiry_idx ON auth_sessions(expires_at);
    CREATE INDEX IF NOT EXISTS world_likes_world_idx ON world_likes(world_id);
    CREATE INDEX IF NOT EXISTS chat_world_created_idx ON chat_messages(world_id, created_at DESC);
    CREATE INDEX IF NOT EXISTS store_items_category_visible_idx ON store_items(category, is_visible, created_at DESC);
    CREATE INDEX IF NOT EXISTS user_store_items_user_idx ON user_store_items(user_id);
  `);

  await pool.query('DELETE FROM auth_sessions WHERE expires_at <= NOW()');

  // Older multiplayer worlds could be created completely empty. The editor places
  // parts onto existing surfaces, so seed a baseplate only when a world has zero blocks.
  const emptyWorlds = await pool.query(`SELECT id,data FROM worlds`);
  for (const row of emptyWorlds.rows) {
    const data = row.data || {};
    data.blocks = data.blocks || {};
    if (Object.keys(data.blocks).length === 0) {
      data.blocks.baseplate = {
        id:'baseplate', shape:'baseplate', actionType:'normal', material:'grid', color:'#555555',
        transparency:0, canCollide:true, anchored:true,
        x:0, y:-0.5, z:0, scaleX:250, scaleY:1, scaleZ:250
      };
      await pool.query('UPDATE worlds SET data=$1,updated_at=NOW() WHERE id=$2', [JSON.stringify(data), row.id]);
    }
  }

  const adminUsername = cleanUsername(process.env.ADMIN_USERNAME);
  const adminPassword = process.env.ADMIN_PASSWORD;
  if (adminUsername && adminPassword) {
    const hash = await bcrypt.hash(adminPassword, 12);
    await pool.query(`
      INSERT INTO users(username,password_hash,appearance,is_admin)
      VALUES($1,$2,$3,true)
      ON CONFLICT(username) DO UPDATE SET
  password_hash = EXCLUDED.password_hash,
  is_admin = true
    `, [adminUsername, hash, JSON.stringify(defaultAppearance)]);
  }
}

async function getWorldByName(name) {
  const r = await pool.query('SELECT * FROM worlds WHERE name=$1', [name]);
  return r.rows[0] || null;
}

function canEditWorld(socket, world) {
  if (!socket.user || !world) return false;
  return !!(socket.user.isAdmin || socket.user.is_admin || Number(world.owner_user_id) === Number(socket.user.id));
}

async function worldSummary(row) {
  const room = `world:${row.name}`;
  return {
    name: row.name,
    onlineCount: io.sockets.adapter.rooms.get(room)?.size || 0,
    ownerUsername: row.owner_username || null,
    likes: Number(row.like_count || 0),
    likedByMe: !!row.liked_by_me,
    createdAt: row.created_at
  };
}

function sessionTokenHash(token) {
  return crypto.createHash('sha256').update(String(token || '')).digest('hex');
}
async function createSession(userId) {
  const token = crypto.randomBytes(32).toString('hex');
  const hash = sessionTokenHash(token);
  await pool.query(`INSERT INTO auth_sessions(token_hash,user_id,expires_at) VALUES($1,$2,NOW() + INTERVAL '30 days')`, [hash,userId]);
  return token;
}
async function loginSocketUser(socket, user) {
  socket.user = user;
  socket.user.isAdmin = !!user.is_admin;
  socketsByUser.set(user.id, socket);
}
function authResponse(user, token) {
  return {success:true,username:user.username,appearance:user.appearance,isAdmin:!!user.is_admin,coins:Number(user.coins || 0),sessionToken:token};
}

io.on('connection', (socket) => {
  socket.on('register', async ({ username, password }, cb) => {
    try {
      username = cleanUsername(username);
      password = String(password || '');
      if (!/^[A-Za-z0-9_]{3,16}$/.test(username)) return cb({success:false,message:'Username must be 3-16 letters, numbers, or underscores.'});
      if (password.length < 6 || password.length > 72) return cb({success:false,message:'Password must be 6-72 characters.'});

      const existing = await pool.query('SELECT id FROM users WHERE lower(username)=lower($1)', [username]);
      if (existing.rowCount) return cb({success:false,message:'Username already exists.'});

      const hash = await bcrypt.hash(password, 12);
      const r = await pool.query(
        `INSERT INTO users(username,password_hash,appearance) VALUES($1,$2,$3) RETURNING id,username,appearance,is_admin,coins`,
        [username, hash, JSON.stringify(defaultAppearance)]
      );
      const user = r.rows[0];
      await loginSocketUser(socket, user);
      const sessionToken = await createSession(user.id);
      cb(authResponse(user, sessionToken));
    } catch (e) {
      console.error(e);
      cb({success:false,message:'Registration failed.'});
    }
  });

  socket.on('login', async ({ username, password }, cb) => {
    try {
      const r = await pool.query('SELECT id,username,password_hash,appearance,is_admin,coins FROM users WHERE lower(username)=lower($1)', [cleanUsername(username)]);
      const user = r.rows[0];
      if (!user || !(await bcrypt.compare(String(password || ''), user.password_hash))) {
        return cb({success:false,message:'Invalid username or password.'});
      }
      await loginSocketUser(socket, user);
      const sessionToken = await createSession(user.id);
      cb(authResponse(user, sessionToken));
    } catch (e) {
      console.error(e);
      cb({success:false,message:'Login failed.'});
    }
  });

  socket.on('resume_session', async ({token} = {}, cb) => {
    try {
      const hash = sessionTokenHash(token);
      const r = await pool.query(`
        SELECT u.id,u.username,u.appearance,u.is_admin,u.coins
        FROM auth_sessions s JOIN users u ON u.id=s.user_id
        WHERE s.token_hash=$1 AND s.expires_at > NOW()
      `,[hash]);
      const user = r.rows[0];
      if (!user) return cb({success:false,message:'Session expired.'});
      await loginSocketUser(socket,user);
      await pool.query(`UPDATE auth_sessions SET expires_at=NOW() + INTERVAL '30 days' WHERE token_hash=$1`,[hash]);
      cb(authResponse(user, token));
    } catch (e) { console.error(e); cb({success:false,message:'Could not restore session.'}); }
  });

  socket.on('logout', async ({token} = {}, cb) => {
    try {
      if (token) await pool.query('DELETE FROM auth_sessions WHERE token_hash=$1',[sessionTokenHash(token)]);
      if (socket.user) socketsByUser.delete(socket.user.id);
      socket.user = null;
      cb && cb({success:true});
    } catch (e) { console.error(e); cb && cb({success:false}); }
  });

  socket.on('get_worlds', async (payload, cb) => {
    if (typeof payload === 'function') { cb = payload; payload = {}; }
    if (!requireAuth(socket, cb)) return;
    try {
      const sort = payload?.sort === 'liked' ? 'liked' : 'recent';
      const order = sort === 'liked' ? 'like_count DESC, w.created_at DESC' : 'w.created_at DESC';
      const r = await pool.query(`
        SELECT w.*, u.username AS owner_username,
          COUNT(wl.user_id)::int AS like_count,
          BOOL_OR(wl.user_id=$1) AS liked_by_me
        FROM worlds w
        LEFT JOIN users u ON u.id=w.owner_user_id
        LEFT JOIN world_likes wl ON wl.world_id=w.id
        GROUP BY w.id,u.username
        ORDER BY ${order}
      `,[socket.user.id]);
      cb({success:true,worlds:await Promise.all(r.rows.map(worldSummary))});
    } catch (e) { console.error(e); cb({success:false,message:'Could not load worlds.'}); }
  });

  socket.on('toggle_world_like', async ({worldName}, cb) => {
    if (!requireAuth(socket, cb)) return;
    try {
      const world = await getWorldByName(cleanWorldName(worldName));
      if (!world) return cb({success:false,message:'World not found.'});
      const existing = await pool.query('SELECT 1 FROM world_likes WHERE world_id=$1 AND user_id=$2',[world.id,socket.user.id]);
      let liked;
      if (existing.rowCount) {
        await pool.query('DELETE FROM world_likes WHERE world_id=$1 AND user_id=$2',[world.id,socket.user.id]);
        liked=false;
      } else {
        await pool.query('INSERT INTO world_likes(world_id,user_id) VALUES($1,$2) ON CONFLICT DO NOTHING',[world.id,socket.user.id]);
        liked=true;
      }
      const count=await pool.query('SELECT COUNT(*)::int AS n FROM world_likes WHERE world_id=$1',[world.id]);
      cb({success:true,liked,likes:Number(count.rows[0].n||0)});
    } catch(e){ console.error(e); cb({success:false,message:'Could not update like.'}); }
  });

  socket.on('get_world_templates', async (cb) => {
    if (!requireAuth(socket, cb)) return;
    try {
      const r = await pool.query('SELECT id,name,created_at FROM world_templates ORDER BY name ASC');
      cb({success:true,templates:r.rows});
    } catch (e) { console.error(e); cb({success:false,message:'Could not load world templates.'}); }
  });

  socket.on('create_world', async ({name, templateId}, cb) => {
    if (!requireAuth(socket, cb)) return;
    name = cleanWorldName(name);
    if (!/^[A-Za-z0-9 _-]{1,20}$/.test(name)) return cb({success:false,message:'World name contains invalid characters.'});
    try {
      const exists = await pool.query('SELECT id FROM worlds WHERE lower(name)=lower($1)', [name]);
      if (exists.rowCount) return cb({success:false,message:'That world already exists.'});

      let data;
      if (templateId && String(templateId) !== 'blank') {
        const t = await pool.query('SELECT data FROM world_templates WHERE id=$1',[Number(templateId)]);
        if (!t.rowCount) return cb({success:false,message:'That template no longer exists.'});
        data = JSON.parse(JSON.stringify(t.rows[0].data));
        data.name = name;
      } else {
        data = {
          name,
          blocks: {
            "baseplate": {
              id: "baseplate", shape: "baseplate", actionType: "normal", material: "grid",
              color: "#555555", transparency: 0, canCollide: true, anchored: true,
              x: 0, y: -0.5, z: 0, scaleX: 250, scaleY: 1, scaleZ: 250
            }
          },
          spawnPoint: {x:0,y:0.05,z:0},
          skyColor:'#a0a0e0',
          cloudsEnabled:true,
          cloudSpeed:1.0,
          cloudColor:'#ffffff'
        };
      }
      await pool.query('INSERT INTO worlds(name,owner_user_id,data) VALUES($1,$2,$3)', [name,socket.user.id,JSON.stringify(data)]);
      cb({success:true});
    } catch (e) { console.error(e); cb({success:false,message:'Could not create world.'}); }
  });

  socket.on('join_world', async ({worldName, appearance}, cb) => {
    if (!requireAuth(socket, cb)) return;
    try {
      const world = await getWorldByName(cleanWorldName(worldName));
      if (!world) return cb({success:false,message:'World not found.'});

      if (socket.data.worldName) socket.leave(`world:${socket.data.worldName}`);
      socket.join(`world:${world.name}`);
      socket.data.worldName = world.name;

      const app = await validateAppearanceForUser(socket.user.id, socket.user.appearance || {});
      const cosmetics = await resolveAppearanceAssets(app);
      socket.user.appearance = app;
      const players = {};
      for (const [sid, p] of playersBySocket) {
        if (p.worldName === world.name) players[sid] = p;
      }
      const p = {
        id: socket.id, username: socket.user.username,
        x: world.data.spawnPoint.x, y: world.data.spawnPoint.y, z: world.data.spawnPoint.z,
        rotationY: 0, walkClock: 0, isMoving:false, isGrounded:true,
        appearance: app, cosmetics, worldName: world.name
      };
      playersBySocket.set(socket.id, p);
      socket.to(`world:${world.name}`).emit('player_joined', p);
      cb({success:true,worldData:world.data,players,selfId:socket.id,canEdit:canEditWorld(socket, world),selfAppearance:app,selfCosmetics:cosmetics});
    } catch (e) { console.error(e); cb({success:false,message:'Could not join world.'}); }
  });

  socket.on('leave_world', () => {
    const p = playersBySocket.get(socket.id);
    if (p?.worldName) {
      socket.to(`world:${p.worldName}`).emit('player_left', socket.id);
      socket.leave(`world:${p.worldName}`);
    }
    socket.data.worldName = null;
    playersBySocket.delete(socket.id);
  });

  socket.on('player_movement', (data) => {
    if (!requireAuth(socket)) return;
    const p = playersBySocket.get(socket.id);
    if (!p || !p.worldName) return;
    for (const k of ['x','y','z','rotationY','walkClock']) if (typeof data[k] !== 'number' || !Number.isFinite(data[k])) return;
    p.x = Math.max(-10000, Math.min(10000, data.x));
    p.y = Math.max(-1000, Math.min(10000, data.y));
    p.z = Math.max(-10000, Math.min(10000, data.z));
    p.rotationY = data.rotationY;
    p.walkClock = data.walkClock;
    p.verticalVelocity = (typeof data.verticalVelocity === 'number' && Number.isFinite(data.verticalVelocity)) ? data.verticalVelocity : 0;
    p.isMoving = !!data.isMoving;
    p.isGrounded = data.isGrounded !== false;
    socket.to(`world:${p.worldName}`).emit('player_moved', p);
  });

  socket.on('block_update', async ({worldName, action, blockData, blockId}, cb) => {
    if (!requireAuth(socket)) return;
    if (socket.data.worldName !== cleanWorldName(worldName)) return;
    try {
      const world = await getWorldByName(worldName);
      if (!world) return cb && cb({success:false,message:'World not found.'});
      if (!canEditWorld(socket, world)) return cb && cb({success:false,message:'Only the world owner or an admin can edit this world.'});

      // IMPORTANT: update only the affected block inside PostgreSQL JSONB.
      // The old code read the entire world, changed one block, then wrote the
      // entire world back. Rapid edits could therefore overwrite each other
      // ("last stale snapshot wins"), making deleted parts reappear later.
      if (action === 'add' || action === 'update') {
        if (!blockData || !blockData.id) return cb && cb({success:false,message:'Invalid block data.'});

        if (action === 'add') {
          const countResult = await pool.query(
            `SELECT COALESCE(jsonb_object_length(COALESCE(data->'blocks','{}'::jsonb)),0) AS count
             FROM worlds WHERE id=$1`,
            [world.id]
          );
          if (Number(countResult.rows[0]?.count || 0) >= 1400) {
            return cb && cb({success:false,message:'Part limit reached (1400/1400 parts).'});
          }
        }

        await pool.query(
          `UPDATE worlds
           SET data = jsonb_set(
             jsonb_set(COALESCE(data,'{}'::jsonb), '{blocks}',
               COALESCE(data->'blocks','{}'::jsonb), true),
             ARRAY['blocks',$2]::text[],
             $3::jsonb,
             true
           ),
           updated_at=NOW()
           WHERE id=$1`,
          [world.id, String(blockData.id), JSON.stringify(blockData)]
        );
      } else if (action === 'delete') {
        if (!blockId) return cb && cb({success:false,message:'Invalid block id.'});

        const current = await pool.query(
          `SELECT data->'blocks'->$2 AS block FROM worlds WHERE id=$1`,
          [world.id, String(blockId)]
        );
        const target = current.rows[0]?.block;
        if (blockId === 'baseplate' || target?.shape === 'baseplate') {
          return cb && cb({success:false,message:'The baseplate cannot be deleted. You can resize it instead.'});
        }

        await pool.query(
          `UPDATE worlds
           SET data = jsonb_set(
             COALESCE(data,'{}'::jsonb),
             '{blocks}',
             COALESCE(data->'blocks','{}'::jsonb) - $2,
             true
           ),
           updated_at=NOW()
           WHERE id=$1`,
          [world.id, String(blockId)]
        );
      } else {
        return cb && cb({success:false,message:'Invalid block action.'});
      }

      // ACK only after this exact edit has been committed.
      socket.to(`world:${world.name}`).emit('block_updated', {action,blockData,blockId});
      cb && cb({success:true});
    } catch (e) {
      console.error(e);
      cb && cb({success:false,message:'Could not save block change.'});
    }
  });

  socket.on('world_settings_update', async ({worldName,settings}, cb) => {
    if (!requireAuth(socket)) return;
    if (socket.data.worldName !== cleanWorldName(worldName) || !settings) return;
    try {
      const world = await getWorldByName(worldName);
      if (!world) return cb && cb({success:false,message:'World not found.'});
      if (!canEditWorld(socket, world)) return cb && cb({success:false,message:'Only the world owner or an admin can edit this world.'});
      const allowed = ['skyColor','cloudsEnabled','cloudSpeed','cloudColor','spawnPoint'];
      const next = {};
      for (const k of allowed) if (Object.prototype.hasOwnProperty.call(settings,k)) next[k] = settings[k];
      if (next.skyColor && !validColor(next.skyColor)) delete next.skyColor;
      if (next.cloudColor && !validColor(next.cloudColor)) delete next.cloudColor;
      if (next.cloudSpeed !== undefined) next.cloudSpeed = Math.max(0, Math.min(10, Number(next.cloudSpeed) || 0));
      if (next.cloudsEnabled !== undefined) next.cloudsEnabled = !!next.cloudsEnabled;
      if (next.spawnPoint) {
        const s = next.spawnPoint;
        if (![s.x,s.y,s.z].every(Number.isFinite)) delete next.spawnPoint;
      }
      Object.assign(world.data,next);
      await pool.query('UPDATE worlds SET data=$1,updated_at=NOW() WHERE id=$2',[JSON.stringify(world.data),world.id]);
      io.to(`world:${world.name}`).emit('world_settings_updated',next);
      cb && cb({success:true});
    } catch (e) { console.error(e); cb && cb({success:false,message:'Could not save world settings.'}); }
  });

  socket.on('save_appearance', async (appearance, cb) => {
    if (!requireAuth(socket, cb)) return;
    try {
      const app = await validateAppearanceForUser(socket.user.id, appearance);
      const cosmetics = await resolveAppearanceAssets(app);
      await pool.query('UPDATE users SET appearance=$1 WHERE id=$2',[JSON.stringify(app),socket.user.id]);
      socket.user.appearance = app;
      const p = playersBySocket.get(socket.id);
      if (p) {
        p.appearance = app;
        p.cosmetics = cosmetics;
        socket.to(`world:${p.worldName}`).emit('player_appearance_updated', p);
      }
      cb && cb({success:true,appearance:app,cosmetics});
    } catch (e) {
      console.error(e);
      cb && cb({success:false,message:'Could not save appearance.'});
    }
  });

  socket.on('get_store', async (cb) => {
    if (!requireAuth(socket, cb)) return;
    try {
      const [visible, owned, user] = await Promise.all([
        pool.query(`
          SELECT id,category,name,price,asset_url,asset_kind,metadata,is_visible
          FROM store_items WHERE is_visible=true
          ORDER BY category ASC, created_at DESC
        `),
        pool.query(`
          SELECT s.id,s.category,s.name,s.price,s.asset_url,s.asset_kind,s.metadata,s.is_visible
          FROM user_store_items o
          JOIN store_items s ON s.id=o.item_id
          WHERE o.user_id=$1
          ORDER BY o.purchased_at ASC
        `, [socket.user.id]),
        pool.query('SELECT coins FROM users WHERE id=$1', [socket.user.id])
      ]);
      const coins = Number(user.rows[0]?.coins || 0);
      socket.user.coins = coins;
      cb({
        success: true,
        coins,
        items: visible.rows.map(rowToStoreItem),
        ownedItems: owned.rows.map(rowToStoreItem),
        uploadConfigured: storeStorageConfigured()
      });
    } catch (e) {
      console.error(e);
      cb({success:false,message:'Could not load the store.'});
    }
  });

  socket.on('buy_store_item', async ({itemId}, cb) => {
    if (!requireAuth(socket, cb)) return;
    itemId = cleanStoreItemId(itemId);
    if (!itemId) return cb({success:false,message:'Invalid store item.'});
    const client = await pool.connect();
    try {
      await client.query('BEGIN');
      const user = await client.query('SELECT coins FROM users WHERE id=$1 FOR UPDATE', [socket.user.id]);
      const item = await client.query('SELECT id,price,is_visible FROM store_items WHERE id=$1', [itemId]);
      if (!item.rowCount) {
        await client.query('ROLLBACK');
        return cb({success:false,message:'That store item no longer exists.'});
      }
      if (!item.rows[0].is_visible) {
        await client.query('ROLLBACK');
        return cb({success:false,message:'That item is not currently available.'});
      }
      const already = await client.query('SELECT 1 FROM user_store_items WHERE user_id=$1 AND item_id=$2', [socket.user.id,itemId]);
      if (already.rowCount) {
        const coins = Number(user.rows[0].coins || 0);
        await client.query('COMMIT');
        return cb({success:true,alreadyOwned:true,coins});
      }
      const price = Number(item.rows[0].price || 0);
      const coins = Number(user.rows[0].coins || 0);
      if (coins < price) {
        await client.query('ROLLBACK');
        return cb({success:false,message:`You need ${price - coins} more coin${price - coins === 1 ? '' : 's'} for that item.`});
      }
      const updated = await client.query('UPDATE users SET coins=coins-$1 WHERE id=$2 RETURNING coins', [price,socket.user.id]);
      await client.query('INSERT INTO user_store_items(user_id,item_id) VALUES($1,$2)', [socket.user.id,itemId]);
      await client.query('COMMIT');
      const newCoins = Number(updated.rows[0].coins || 0);
      socket.user.coins = newCoins;
      cb({success:true,coins:newCoins});
    } catch (e) {
      await client.query('ROLLBACK').catch(() => {});
      console.error(e);
      cb({success:false,message:'Purchase failed.'});
    } finally {
      client.release();
    }
  });

  socket.on('admin_store_list', async (cb) => {
    if (!requireAdmin(socket, cb)) return;
    try {
      const r = await pool.query(`
        SELECT id,category,name,price,asset_url,asset_kind,metadata,is_visible
        FROM store_items ORDER BY created_at DESC
      `);
      cb({success:true,items:r.rows.map(rowToStoreItem),uploadConfigured:storeStorageConfigured()});
    } catch (e) {
      console.error(e);
      cb({success:false,message:'Could not load store items.'});
    }
  });

  socket.on('admin_store_set_visible', async ({itemId,isVisible}, cb) => {
    if (!requireAdmin(socket, cb)) return;
    itemId = cleanStoreItemId(itemId);
    if (!itemId) return cb({success:false,message:'Invalid store item.'});
    try {
      const r = await pool.query(`
        UPDATE store_items SET is_visible=$1,updated_at=NOW() WHERE id=$2 RETURNING id
      `, [!!isVisible,itemId]);
      if (!r.rowCount) return cb({success:false,message:'Store item not found.'});
      cb({success:true});
    } catch (e) {
      console.error(e);
      cb({success:false,message:'Could not update store visibility.'});
    }
  });

  socket.on('admin_store_create', async (payload = {}, cb) => {
    if (!requireAdmin(socket, cb)) return;
    try {
      const category = String(payload.category || '').trim();
      const name = String(payload.name || '').trim().slice(0, 40);
      const price = Number(payload.price);
      if (!STORE_CATEGORIES.has(category)) return cb({success:false,message:'Choose a valid store category.'});
      if (!name) return cb({success:false,message:'Item name is required.'});
      if (!Number.isInteger(price) || price < 0 || price > 100000000) return cb({success:false,message:'Price must be a whole number of coins.'});
      const buffer = fileBufferFromSocket(payload.fileData);
      if (!buffer || !buffer.length) return cb({success:false,message:'Choose a file to upload.'});
      if (!storeStorageConfigured()) {
        return cb({success:false,message:'Store uploads need SUPABASE_URL and SUPABASE_SERVICE_ROLE_KEY configured on Render first.'});
      }

      const metadata = cleanUploadMeta(category, payload.metadata || {});
      if (category === 'hat') {
        for (const key of ['size','offsetX','offsetY','offsetZ']) {
          if (!Number.isFinite(Number(payload.metadata?.[key]))) {
            return cb({success:false,message:'Hat size and X/Y/Z offsets are required.'});
          }
        }
      }
      const assetUrl = await uploadStoreAsset({
        category,
        fileName: payload.fileName,
        mimeType: payload.mimeType,
        buffer
      });
      const assetKind = ['eyes','mouth','torso_decal'].includes(category) ? 'image' : 'glb';
      const r = await pool.query(`
        INSERT INTO store_items(category,name,price,asset_url,asset_kind,metadata,is_visible,created_by)
        VALUES($1,$2,$3,$4,$5,$6,$7,$8)
        RETURNING id,category,name,price,asset_url,asset_kind,metadata,is_visible
      `, [category,name,price,assetUrl,assetKind,JSON.stringify(metadata),payload.isVisible !== false,socket.user.id]);
      cb({success:true,item:rowToStoreItem(r.rows[0])});
    } catch (e) {
      console.error(e);
      cb({success:false,message:e.message || 'Could not create store item.'});
    }
  });

  socket.on('get_world_chat', async ({worldName}, cb) => {
    if (!requireAuth(socket, cb)) return;
    try {
      const world = await getWorldByName(cleanWorldName(worldName));
      if (!world) return cb({success:false,message:'World not found.'});
      if (socket.data.worldName !== world.name) return cb({success:false,message:'Join the world first.'});
      const r = await pool.query(`
        SELECT username,message,created_at AS "createdAt"
        FROM chat_messages WHERE world_id=$1
        ORDER BY created_at DESC LIMIT 100
      `,[world.id]);
      cb({success:true,messages:r.rows.reverse().map(x=>({...x,worldName:world.name}))});
    } catch (e) { console.error(e); cb({success:false,message:'Could not load chat.'}); }
  });

  socket.on('send_world_chat', async ({worldName,message},cb) => {
    if (!requireAuth(socket, cb)) return;
    worldName = cleanWorldName(worldName);
    message = String(message || '').trim().slice(0,300);
    if (!message) return cb({success:false,message:'Message cannot be empty.'});
    if (socket.data.worldName !== worldName) return cb({success:false,message:'Join the world first.'});
    try {
      const world = await getWorldByName(worldName);
      if (!world) return cb({success:false,message:'World not found.'});
      const r = await pool.query(`
        INSERT INTO chat_messages(world_id,user_id,username,message)
        VALUES($1,$2,$3,$4)
        RETURNING created_at AS "createdAt"
      `,[world.id,socket.user.id,socket.user.username,message]);
      io.to(`world:${world.name}`).emit('world_chat_message',{
        worldName:world.name, username:socket.user.username, message, createdAt:r.rows[0].createdAt
      });
      cb({success:true});
    } catch (e) { console.error(e); cb({success:false,message:'Could not send message.'}); }
  });

  socket.on('admin_search_users', async ({query} = {}, cb) => {
    if (!requireAdmin(socket, cb)) return;
    try {
      const q = String(query || '').trim().slice(0, 50);
      if (!q) return cb({success:true,users:[]});
      const users = await pool.query(`
        SELECT id,username,is_admin AS "isAdmin",coins,created_at AS "createdAt"
        FROM users
        WHERE username ILIKE $1
        ORDER BY CASE WHEN LOWER(username)=LOWER($2) THEN 0 ELSE 1 END, username ASC
        LIMIT 25
      `,[`%${q}%`,q]);
      cb({success:true,users:users.rows.map(u => ({
        username:u.username,isAdmin:u.isAdmin,createdAt:u.createdAt,
        coins:Number(u.coins || 0),online:socketsByUser.has(u.id)
      }))});
    } catch (e) { console.error(e); cb({success:false,message:'Could not search users.'}); }
  });

  socket.on('admin_search_worlds', async ({query} = {}, cb) => {
    if (!requireAdmin(socket, cb)) return;
    try {
      const q = String(query || '').trim().slice(0, 80);
      if (!q) return cb({success:true,worlds:[]});
      const worlds = await pool.query(`
        WITH matches AS (
          SELECT w.id,w.name,w.owner_user_id,w.created_at
          FROM worlds w
          LEFT JOIN users owner ON owner.id=w.owner_user_id
          WHERE w.name ILIKE $1 OR owner.username ILIKE $1
          ORDER BY CASE WHEN LOWER(w.name)=LOWER($2) THEN 0 ELSE 1 END, w.name ASC
          LIMIT 25
        )
        SELECT m.id,m.name,u.username AS "ownerUsername",
               COUNT(cm.id)::int AS "chatCount"
        FROM matches m
        LEFT JOIN users u ON u.id=m.owner_user_id
        LEFT JOIN chat_messages cm ON cm.world_id=m.id
        GROUP BY m.id,m.name,u.username,m.created_at
        ORDER BY CASE WHEN LOWER(m.name)=LOWER($2) THEN 0 ELSE 1 END, m.name ASC
      `,[`%${q}%`,q]);
      cb({success:true,worlds:worlds.rows.map(w => ({
        name:w.name,ownerUsername:w.ownerUsername,chatCount:w.chatCount,
        onlineCount:io.sockets.adapter.rooms.get(`world:${w.name}`)?.size || 0
      }))});
    } catch (e) { console.error(e); cb({success:false,message:'Could not search worlds.'}); }
  });

  socket.on('admin_kick_user', async ({username}, cb) => {
    if (!requireAdmin(socket, cb)) return;
    try {
      const target = await pool.query('SELECT id,is_admin FROM users WHERE lower(username)=lower($1)',[cleanUsername(username)]);
      if (!target.rowCount) return cb({success:false,message:'User not found.'});
      if (target.rows[0].is_admin) return cb({success:false,message:'Admin accounts cannot be kicked from this panel.'});
      const targetSocket = socketsByUser.get(target.rows[0].id);
      if (!targetSocket) return cb({success:false,message:'That user is not currently online.'});
      targetSocket.emit('admin_kicked');
      targetSocket.disconnect(true);
      cb({success:true});
    } catch (e) { console.error(e); cb({success:false,message:'Could not kick user.'}); }
  });

  socket.on('admin_clear_world_chat', async ({worldName}, cb) => {
    if (!requireAdmin(socket, cb)) return;
    try {
      const world = await getWorldByName(cleanWorldName(worldName));
      if (!world) return cb({success:false,message:'World not found.'});
      await pool.query('DELETE FROM chat_messages WHERE world_id=$1',[world.id]);
      io.to(`world:${world.name}`).emit('world_chat_cleared', {worldName:world.name});
      cb({success:true});
    } catch (e) { console.error(e); cb({success:false,message:'Could not clear world chat.'}); }
  });

  socket.on('admin_delete_user', async ({username}, cb) => {
    if (!requireAdmin(socket, cb)) return;
    try {
      const target = await pool.query('SELECT id,is_admin FROM users WHERE username=$1',[cleanUsername(username)]);
      if (!target.rowCount) return cb({success:false,message:'User not found.'});
      if (target.rows[0].is_admin) return cb({success:false,message:'Admin accounts cannot be deleted from this panel.'});
      const targetSocket = socketsByUser.get(target.rows[0].id);
      if (targetSocket) {
        targetSocket.emit('account_deleted');
        targetSocket.disconnect(true);
      }
      await pool.query('DELETE FROM users WHERE id=$1',[target.rows[0].id]);
      cb({success:true});
    } catch (e) { console.error(e); cb({success:false,message:'Could not delete account.'}); }
  });

  socket.on('delete_own_world', async ({worldName}, cb) => {
    if (!requireAuth(socket, cb)) return;
    try {
      const world = await getWorldByName(cleanWorldName(worldName));
      if (!world) return cb({success:false,message:'World not found.'});
      if (Number(world.owner_user_id) !== Number(socket.user.id)) return cb({success:false,message:'You can only delete worlds you own.'});
      const room = `world:${world.name}`;
      for (const [sid,p] of playersBySocket) {
        if (p.worldName === world.name) {
          const target = io.sockets.sockets.get(sid);
          if (target) { target.emit('world_deleted',{worldName:world.name}); target.leave(room); target.data.worldName=null; }
          playersBySocket.delete(sid);
        }
      }
      await pool.query('DELETE FROM worlds WHERE id=$1',[world.id]);
      cb({success:true});
    } catch (e) { console.error(e); cb({success:false,message:'Could not delete world.'}); }
  });

  socket.on('admin_make_world_template', async ({worldName,templateName}, cb) => {
    if (!requireAdmin(socket, cb)) return;
    try {
      const world = await getWorldByName(cleanWorldName(worldName));
      if (!world) return cb({success:false,message:'World not found.'});
      const name = String(templateName || world.name).trim().slice(0,40);
      if (!name) return cb({success:false,message:'Template name is required.'});
      await pool.query(`
        INSERT INTO world_templates(name,source_world_id,data,created_by)
        VALUES($1,$2,$3,$4)
        ON CONFLICT(name) DO UPDATE SET source_world_id=EXCLUDED.source_world_id,data=EXCLUDED.data,created_by=EXCLUDED.created_by,updated_at=NOW()
      `,[name,world.id,JSON.stringify(world.data),socket.user.id]);
      cb({success:true});
    } catch (e) { console.error(e); cb({success:false,message:'Could not create template.'}); }
  });

  socket.on('admin_delete_world', async ({worldName}, cb) => {
    if (!requireAdmin(socket, cb)) return;
    try {
      const world = await getWorldByName(cleanWorldName(worldName));
      if (!world) return cb({success:false,message:'World not found.'});
      const room = `world:${world.name}`;
      for (const [sid,p] of playersBySocket) {
        if (p.worldName === world.name) {
          const s = io.sockets.sockets.get(sid);
          if (s) {
            s.emit('world_deleted', {worldName:world.name});
            s.leave(room);
            s.data.worldName = null;
          }
          playersBySocket.delete(sid);
        }
      }
      await pool.query('DELETE FROM worlds WHERE id=$1',[world.id]);
      cb({success:true});
    } catch (e) { console.error(e); cb({success:false,message:'Could not delete world.'}); }
  });

  socket.on('disconnect', () => {
    const p = playersBySocket.get(socket.id);
    if (p?.worldName) socket.to(`world:${p.worldName}`).emit('player_left', socket.id);
    playersBySocket.delete(socket.id);
    if (socket.user) socketsByUser.delete(socket.user.id);
  });
});

migrate().then(() => {
  server.listen(PORT, () => console.log(`KWG 3D server listening on port ${PORT}`));
}).catch(err => {
  console.error('Database migration failed:', err);
  process.exit(1);
});
