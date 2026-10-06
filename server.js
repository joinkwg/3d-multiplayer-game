require('dotenv').config();
const path = require('path');
const http = require('http');
const express = require('express');
const { Server } = require('socket.io');
const { Pool } = require('pg');
const bcrypt = require('bcryptjs');

const PORT = Number(process.env.PORT || 3000);
const DATABASE_URL = process.env.DATABASE_URL;
if (!DATABASE_URL) throw new Error('DATABASE_URL is required.');

const pool = new Pool({
  connectionString: DATABASE_URL,
  ssl: process.env.PGSSL === 'disable' ? false : { rejectUnauthorized: false }
});

const app = express();
const server = http.createServer(app);
const io = new Server(server);

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
  rightLegColor: '#000000'
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
function sanitizeAppearance(a = {}) {
  return {
    hat: ['none','black_tophat','blue_tophat','red_tophat','pink_tophat','pink_bow','blue_bow','white_bow','black_cat_ears','pink_cat_ears'].includes(a.hat) ? a.hat : defaultAppearance.hat,
    headShape: ['sphere','cube','cylinder','headless'].includes(a.headShape) ? a.headShape : defaultAppearance.headShape,
    headColor: validColor(a.headColor) ? a.headColor : defaultAppearance.headColor,
    torsoColor: validColor(a.torsoColor) ? a.torsoColor : defaultAppearance.torsoColor,
    leftArmColor: validColor(a.leftArmColor) ? a.leftArmColor : defaultAppearance.leftArmColor,
    rightArmColor: validColor(a.rightArmColor) ? a.rightArmColor : defaultAppearance.rightArmColor,
    leftLegColor: validColor(a.leftLegColor) ? a.leftLegColor : defaultAppearance.leftLegColor,
    rightLegColor: validColor(a.rightLegColor) ? a.rightLegColor : defaultAppearance.rightLegColor
  };
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
    CREATE INDEX IF NOT EXISTS chat_world_created_idx ON chat_messages(world_id, created_at DESC);
  `);

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
    ownerUsername: row.owner_username || null
  };
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
        `INSERT INTO users(username,password_hash,appearance) VALUES($1,$2,$3) RETURNING id,username,appearance,is_admin`,
        [username, hash, JSON.stringify(defaultAppearance)]
      );
      socket.user = r.rows[0];
      socket.user.isAdmin = !!socket.user.is_admin;
      socketsByUser.set(socket.user.id, socket);
      cb({success:true,username:socket.user.username,appearance:socket.user.appearance,isAdmin:false});
    } catch (e) {
      console.error(e);
      cb({success:false,message:'Registration failed.'});
    }
  });

  socket.on('login', async ({ username, password }, cb) => {
    try {
      const r = await pool.query('SELECT id,username,password_hash,appearance,is_admin FROM users WHERE lower(username)=lower($1)', [cleanUsername(username)]);
      const user = r.rows[0];
      if (!user || !(await bcrypt.compare(String(password || ''), user.password_hash))) {
        return cb({success:false,message:'Invalid username or password.'});
      }
      socket.user = user;
      socket.user.isAdmin = !!user.is_admin;
      socketsByUser.set(user.id, socket);
      cb({success:true,username:user.username,appearance:user.appearance,isAdmin:user.is_admin});
    } catch (e) {
      console.error(e);
      cb({success:false,message:'Login failed.'});
    }
  });

  socket.on('get_worlds', async (cb) => {
    if (!requireAuth(socket, cb)) return;
    try {
      const r = await pool.query(`
        SELECT w.*, u.username AS owner_username
        FROM worlds w LEFT JOIN users u ON u.id=w.owner_user_id
        ORDER BY w.created_at ASC
      `);
      cb({success:true,worlds:await Promise.all(r.rows.map(worldSummary))});
    } catch (e) { console.error(e); cb({success:false,message:'Could not load worlds.'}); }
  });

  socket.on('create_world', async ({name}, cb) => {
    if (!requireAuth(socket, cb)) return;
    name = cleanWorldName(name);
    if (!/^[A-Za-z0-9 _-]{1,20}$/.test(name)) return cb({success:false,message:'World name contains invalid characters.'});
    try {
      const exists = await pool.query('SELECT id FROM worlds WHERE lower(name)=lower($1)', [name]);
      if (exists.rowCount) return cb({success:false,message:'That world already exists.'});
      const data = {
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

      const app = sanitizeAppearance(appearance || socket.user.appearance || {});
      const players = {};
      for (const [sid, p] of playersBySocket) {
        if (p.worldName === world.name) players[sid] = p;
      }
      const p = {
        id: socket.id, username: socket.user.username,
        x: world.data.spawnPoint.x, y: world.data.spawnPoint.y, z: world.data.spawnPoint.z,
        rotationY: 0, walkClock: 0, isMoving:false, isGrounded:true,
        appearance: app, worldName: world.name
      };
      playersBySocket.set(socket.id, p);
      socket.to(`world:${world.name}`).emit('player_joined', p);
      cb({success:true,worldData:world.data,players,selfId:socket.id,canEdit:canEditWorld(socket, world)});
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
      const data = world.data;
      data.blocks = data.blocks || {};
      if (action === 'add' || action === 'update') {
        if (!blockData || !blockData.id) return;
        if (Object.keys(data.blocks).length >= 1400 && action === 'add') return;
        data.blocks[blockData.id] = blockData;
      } else if (action === 'delete') {
        delete data.blocks[blockId];
      } else return;

      await pool.query('UPDATE worlds SET data=$1,updated_at=NOW() WHERE id=$2', [JSON.stringify(data), world.id]);
      // The editing client already applies its own change locally.
      // Broadcast only to OTHER players so the sender does not receive a
      // delayed copy of its own drag and visually snap backward/forward.
      socket.to(`world:${world.name}`).emit('block_updated', {action,blockData,blockId});
      cb && cb({success:true});
    } catch (e) { console.error(e); cb && cb({success:false,message:'Could not save block change.'}); }
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

  socket.on('save_appearance', async (appearance) => {
    if (!requireAuth(socket)) return;
    const app = sanitizeAppearance(appearance);
    try {
      await pool.query('UPDATE users SET appearance=$1 WHERE id=$2',[JSON.stringify(app),socket.user.id]);
      socket.user.appearance = app;
      const p = playersBySocket.get(socket.id);
      if (p) {
        p.appearance = app;
        socket.to(`world:${p.worldName}`).emit('player_joined', p);
      }
    } catch (e) { console.error(e); }
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

  socket.on('admin_list', async (cb) => {
    if (!requireAdmin(socket, cb)) return;
    try {
      const users = await pool.query('SELECT id,username,is_admin AS "isAdmin",created_at AS "createdAt" FROM users ORDER BY created_at ASC');
      const worlds = await pool.query(`
        SELECT w.id,w.name,u.username AS "ownerUsername",
               COUNT(cm.id)::int AS "chatCount"
        FROM worlds w
        LEFT JOIN users u ON u.id=w.owner_user_id
        LEFT JOIN chat_messages cm ON cm.world_id=w.id
        GROUP BY w.id,w.name,u.username,w.created_at
        ORDER BY w.created_at ASC
      `);
      const userRows = users.rows.map(u => ({
        username: u.username,
        isAdmin: u.isAdmin,
        createdAt: u.createdAt,
        online: socketsByUser.has(u.id)
      }));
      const worldRows = worlds.rows.map(w => ({
        name: w.name,
        ownerUsername: w.ownerUsername,
        chatCount: w.chatCount,
        onlineCount: io.sockets.adapter.rooms.get(`world:${w.name}`)?.size || 0
      }));
      cb({success:true,users:userRows,worlds:worldRows});
    } catch (e) { console.error(e); cb({success:false,message:'Could not load admin data.'}); }
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
