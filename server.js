const express = require('express');
const http = require('http');
const { Server } = require('socket.io');
const sqlite3 = require('sqlite3');
const { open } = require('sqlite');
const bcrypt = require('bcryptjs');
const path = require('path');

const app = express();
const server = http.createServer(app);
const io = new Server(server, {
  cors: {
    origin: '*',
    methods: ['GET', 'POST']
  }
});

const PORT = process.env.PORT || 3000;

app.use(express.static(path.join(__dirname)));

let db;

async function initDB() {
  db = await open({
    filename: path.join(__dirname, 'database.db'),
    driver: sqlite3.Database
  });

  await db.exec(`
    CREATE TABLE IF NOT EXISTS users (
      id INTEGER PRIMARY KEY AUTOINCREMENT,
      username TEXT UNIQUE NOT NULL,
      password TEXT NOT NULL,
      appearance TEXT
    );

    CREATE TABLE IF NOT EXISTS worlds (
      name TEXT PRIMARY KEY,
      data TEXT NOT NULL
    );
  `);

  const defaultWorld = await db.get('SELECT * FROM worlds WHERE name = ?', ['Default World']);
  if (!defaultWorld) {
    const initialWorldData = {
      spawnPoint: { x: 0, y: 0.05, z: 0 },
      skyColor: '#a0a0e0',
      cloudsEnabled: true,
      cloudSpeed: 1.0,
      cloudColor: '#ffffff',
      blocks: {
        "0_ -1_0": {
          id: "0_ -1_0",
          shape: "baseplate",
          actionType: "normal",
          material: "grid",
          color: "#555555",
          transparency: 0,
          canCollide: true,
          anchored: true,
          x: 0, y: -0.5, z: 0,
          scaleX: 250, scaleY: 1, scaleZ: 250
        }
      }
    };
    await db.run('INSERT INTO worlds (name, data) VALUES (?, ?)', ['Default World', JSON.stringify(initialWorldData)]);
  }
}

const activePlayers = {}; 

io.on('connection', (socket) => {
  let currentUsername = null;
  let currentWorld = null;

  socket.on('register', async ({ username, password }, callback) => {
    const cleanUser = (username || '').trim();
    if (!cleanUser || !password) {
      return callback({ success: false, message: 'Username and password required.' });
    }
    try {
      const existing = await db.get('SELECT id FROM users WHERE username = ?', [cleanUser]);
      if (existing) {
        return callback({ success: false, message: 'Username already exists.' });
      }

      const hash = await bcrypt.hash(password, 10);
      await db.run('INSERT INTO users (username, password) VALUES (?, ?)', [cleanUser, hash]);
      currentUsername = cleanUser;
      callback({ success: true, username: cleanUser });
    } catch (err) {
      callback({ success: false, message: 'Registration failed server-side.' });
    }
  });

  socket.on('login', async ({ username, password }, callback) => {
    const cleanUser = (username || '').trim();
    if (!cleanUser || !password) {
      return callback({ success: false, message: 'Username and password required.' });
    }
    try {
      const user = await db.get('SELECT * FROM users WHERE username = ?', [cleanUser]);
      if (!user) {
        return callback({ success: false, message: 'Invalid username or password.' });
      }

      const match = await bcrypt.compare(password, user.password);
      if (!match) {
        return callback({ success: false, message: 'Invalid username or password.' });
      }

      currentUsername = cleanUser;
      let appearance = null;
      try { appearance = JSON.parse(user.appearance); } catch (e) {}

      callback({ success: true, username: cleanUser, appearance });
    } catch (err) {
      callback({ success: false, message: 'Login failed server-side.' });
    }
  });

  socket.on('save_appearance', async (appearance) => {
    if (!currentUsername) return;
    await db.run('UPDATE users SET appearance = ? WHERE username = ?', [JSON.stringify(appearance), currentUsername]);
  });

  socket.on('get_worlds', async (callback) => {
    try {
      const rows = await db.all('SELECT name FROM worlds');
      const worldList = rows.map(r => {
        const roomSockets = io.sockets.adapter.rooms.get(r.name);
        return {
          name: r.name,
          onlineCount: roomSockets ? roomSockets.size : 0
        };
      });
      callback({ success: true, worlds: worldList });
    } catch (err) {
      callback({ success: false, worlds: [] });
    }
  });

  socket.on('create_world', async ({ name }, callback) => {
    const cleanName = (name || '').trim();
    if (!cleanName) return callback({ success: false, message: 'World name required.' });

    try {
      const existing = await db.get('SELECT name FROM worlds WHERE name = ?', [cleanName]);
      if (existing) {
        return callback({ success: false, message: 'World already exists.' });
      }

      const newWorldData = {
        spawnPoint: { x: 0, y: 0.05, z: 0 },
        skyColor: '#a0a0e0',
        cloudsEnabled: true,
        cloudSpeed: 1.0,
        cloudColor: '#ffffff',
        blocks: {
          "0_ -1_0": {
            id: "0_ -1_0",
            shape: "baseplate",
            actionType: "normal",
            material: "grid",
            color: "#555555",
            transparency: 0,
            canCollide: true,
            anchored: true,
            x: 0, y: -0.5, z: 0,
            scaleX: 250, scaleY: 1, scaleZ: 250
          }
        }
      };

      await db.run('INSERT INTO worlds (name, data) VALUES (?, ?)', [cleanName, JSON.stringify(newWorldData)]);
      callback({ success: true, name: cleanName });
    } catch (err) {
      callback({ success: false, message: 'Failed to create world.' });
    }
  });

  socket.on('join_world', async ({ worldName, appearance }, callback) => {
    try {
      const worldRecord = await db.get('SELECT * FROM worlds WHERE name = ?', [worldName]);
      if (!worldRecord) {
        return callback({ success: false, message: 'World not found.' });
      }

      if (currentWorld) {
        socket.leave(currentWorld);
        socket.to(currentWorld).emit('player_left', socket.id);
        delete activePlayers[socket.id];
      }

      currentWorld = worldName;
      socket.join(worldName);

      const worldData = JSON.parse(worldRecord.data);

      activePlayers[socket.id] = {
        id: socket.id,
        username: currentUsername || 'Guest',
        appearance: appearance,
        x: worldData.spawnPoint.x,
        y: worldData.spawnPoint.y,
        z: worldData.spawnPoint.z,
        rotationY: 0,
        walkClock: 0
      };

      const roomPlayers = {};
      const clientsInRoom = io.sockets.adapter.rooms.get(worldName);
      if (clientsInRoom) {
        for (const id of clientsInRoom) {
          if (activePlayers[id]) {
            roomPlayers[id] = activePlayers[id];
          }
        }
      }

      socket.to(worldName).emit('player_joined', activePlayers[socket.id]);

      callback({
        success: true,
        worldData,
        players: roomPlayers,
        selfId: socket.id
      });
    } catch (err) {
      callback({ success: false, message: 'Failed to join world.' });
    }
  });

  socket.on('leave_world', () => {
    if (currentWorld) {
      socket.to(currentWorld).emit('player_left', socket.id);
      socket.leave(currentWorld);
      delete activePlayers[socket.id];
      currentWorld = null;
    }
  });

  socket.on('player_movement', (data) => {
    if (!currentWorld || !activePlayers[socket.id]) return;
    activePlayers[socket.id].x = data.x;
    activePlayers[socket.id].y = data.y;
    activePlayers[socket.id].z = data.z;
    activePlayers[socket.id].rotationY = data.rotationY;
    activePlayers[socket.id].walkClock = data.walkClock;

    socket.to(currentWorld).emit('player_moved', {
      id: socket.id,
      ...data
    });
  });

  socket.on('block_update', async ({ worldName, action, blockData, blockId }) => {
    if (!worldName) return;
    try {
      const row = await db.get('SELECT data FROM worlds WHERE name = ?', [worldName]);
      if (!row) return;

      const worldData = JSON.parse(row.data);
      if (action === 'add' || action === 'update') {
        worldData.blocks[blockData.id] = blockData;
      } else if (action === 'delete') {
        delete worldData.blocks[blockId];
      }

      await db.run('UPDATE worlds SET data = ? WHERE name = ?', [JSON.stringify(worldData), worldName]);
      socket.to(worldName).emit('block_updated', { action, blockData, blockId });
    } catch (e) {}
  });

  socket.on('world_settings_update', async ({ worldName, settings }) => {
    if (!worldName) return;
    try {
      const row = await db.get('SELECT data FROM worlds WHERE name = ?', [worldName]);
      if (!row) return;

      const worldData = JSON.parse(row.data);
      Object.assign(worldData, settings);

      await db.run('UPDATE worlds SET data = ? WHERE name = ?', [JSON.stringify(worldData), worldName]);
      socket.to(worldName).emit('world_settings_updated', settings);
    } catch (e) {}
  });

  socket.on('disconnect', () => {
    if (currentWorld) {
      socket.to(currentWorld).emit('player_left', socket.id);
      delete activePlayers[socket.id];
    }
  });
});

initDB().then(() => {
  server.listen(PORT, () => {
    console.log(`KWG 3D Server running on port ${PORT}`);
  });
});
