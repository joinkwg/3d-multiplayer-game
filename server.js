const express = require('express');
const http = require('http');
const { Server } = require('socket.io');
const cors = require('cors');
const fs = require('fs');
const path = require('path');
const bcrypt = require('bcryptjs');

const app = express();
app.use(cors());

const server = http.createServer(app);
const io = new Server(server, {
  cors: {
    origin: "*",
    methods: ["GET", "POST"]
  }
});

const DB_FILE = path.join(__dirname, 'data.json');

// Initial Database Structure
let db = {
  users: {},
  worlds: {
    "Default World": {
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
    }
  }
};

// Load database if file exists
if (fs.existsSync(DB_FILE)) {
  try {
    db = JSON.parse(fs.readFileSync(DB_FILE, 'utf8'));
  } catch (err) {
    console.error("Error reading data.json, starting with default state.");
  }
}

function saveDB() {
  fs.writeFileSync(DB_FILE, JSON.stringify(db, null, 2));
}

// Track active player sockets
const activePlayers = {}; // socket.id -> { username, worldName, appearance, pos }

io.on('connection', (socket) => {
  console.log(`Player connected: ${socket.id}`);

  // --- AUTHENTICATION ---
  socket.on('register', async ({ username, password }, callback) => {
    const cleanUser = username.trim().toLowerCase();
    if (!cleanUser || !password) {
      return callback({ success: false, message: 'Username and password required.' });
    }
    if (db.users[cleanUser]) {
      return callback({ success: false, message: 'Username already taken.' });
    }

    const hashedPassword = await bcrypt.hash(password, 10);
    db.users[cleanUser] = { username: username.trim(), password: hashedPassword };
    saveDB();
    callback({ success: true, message: 'Account created! You can now log in.' });
  });

  socket.on('login', async ({ username, password }, callback) => {
    const cleanUser = username.trim().toLowerCase();
    const user = db.users[cleanUser];
    if (!user) {
      return callback({ success: false, message: 'User does not exist.' });
    }

    const match = await bcrypt.compare(password, user.password);
    if (!match) {
      return callback({ success: false, message: 'Incorrect password.' });
    }

    callback({ success: true, username: user.username });
  });

  // --- WORLD MANAGEMENT ---
  socket.on('get_worlds', (callback) => {
    callback(Object.keys(db.worlds));
  });

  socket.on('create_world', ({ worldName }, callback) => {
    if (!worldName || db.worlds[worldName]) {
      return callback({ success: false, message: 'World already exists or invalid name.' });
    }

    db.worlds[worldName] = {
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
    saveDB();
    io.emit('world_list_updated', Object.keys(db.worlds));
    callback({ success: true, worldName });
  });

  socket.on('join_world', ({ worldName, username, appearance }) => {
    if (!db.worlds[worldName]) return;

    // Leave any prior world
    if (socket.worldName) {
      socket.leave(socket.worldName);
      socket.to(socket.worldName).emit('player_left', socket.id);
    }

    socket.worldName = worldName;
    socket.username = username;
    socket.appearance = appearance;
    socket.join(worldName);

    activePlayers[socket.id] = {
      id: socket.id,
      username,
      appearance,
      x: db.worlds[worldName].spawnPoint.x,
      y: db.worlds[worldName].spawnPoint.y,
      z: db.worlds[worldName].spawnPoint.z,
      rotY: 0,
      isMoving: false
    };

    // Send world state to joining player
    socket.emit('load_world_state', {
      worldName,
      worldData: db.worlds[worldName]
    });

    // Gather existing players in this world
    const roomPlayers = {};
    for (const id in activePlayers) {
      if (activePlayers[id].worldName === worldName && id !== socket.id) {
        roomPlayers[id] = activePlayers[id];
      }
    }
    socket.emit('existing_players', roomPlayers);

    // Notify others in room
    socket.to(worldName).emit('player_joined', activePlayers[socket.id]);
  });

  socket.on('leave_world', () => {
    if (socket.worldName) {
      socket.to(socket.worldName).emit('player_left', socket.id);
      socket.leave(socket.worldName);
      delete activePlayers[socket.id];
      socket.worldName = null;
    }
  });

  // --- REAL-TIME MOVEMENT ---
  socket.on('player_move', (moveData) => {
    if (!socket.worldName || !activePlayers[socket.id]) return;

    Object.assign(activePlayers[socket.id], moveData);
    socket.to(socket.worldName).emit('player_moved', {
      id: socket.id,
      ...moveData
    });
  });

  // --- PER-WORLD CHAT SYSTEM ---
  socket.on('send_chat', (msg) => {
    if (!socket.worldName || !msg.trim()) return;
    const chatPayload = {
      sender: socket.username || 'Anonymous',
      message: msg.trim().substring(0, 150),
      timestamp: new Date().toLocaleTimeString([], { hour: '2-digit', minute: '2-digit' })
    };
    io.to(socket.worldName).emit('receive_chat', chatPayload);
  });

  // --- REAL-TIME BLOCK & ENVIRONMENT EDITS ---
  socket.on('place_block', (blockData) => {
    const worldName = socket.worldName;
    if (!worldName || !db.worlds[worldName]) return;

    db.worlds[worldName].blocks[blockData.id] = blockData;
    saveDB();
    socket.to(worldName).emit('block_placed', blockData);
  });

  socket.on('delete_block', (blockId) => {
    const worldName = socket.worldName;
    if (!worldName || !db.worlds[worldName]) return;

    delete db.worlds[worldName].blocks[blockId];
    saveDB();
    socket.to(worldName).emit('block_deleted', blockId);
  });

  socket.on('update_environment', (envData) => {
    const worldName = socket.worldName;
    if (!worldName || !db.worlds[worldName]) return;

    Object.assign(db.worlds[worldName], envData);
    saveDB();
    socket.to(worldName).emit('environment_updated', envData);
  });

  socket.on('disconnect', () => {
    if (socket.worldName) {
      io.to(socket.worldName).emit('player_left', socket.id);
    }
    delete activePlayers[socket.id];
    console.log(`Player disconnected: ${socket.id}`);
  });
});

const PORT = process.env.PORT || 3000;
server.listen(PORT, () => {
  console.log(`Backend server running on port ${PORT}`);
});