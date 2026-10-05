-- The server auto-creates these tables on startup.
-- This file is provided for inspection / manual provisioning.

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

CREATE INDEX IF NOT EXISTS chat_world_created_idx
  ON chat_messages(world_id, created_at DESC);
