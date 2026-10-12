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
const SUPABASE_THUMBNAIL_BUCKET = String(process.env.SUPABASE_THUMBNAIL_BUCKET || 'world-thumbnails');
const STORE_CATEGORIES = new Set(['eyes','mouth','torso_decal','hat','head_shape','hair','hats','heads','eyes','mouth','skin','tops','bottoms','shoes','flightsuits']);

const pool = new Pool({
  connectionString: DATABASE_URL,
  ssl: process.env.PGSSL === 'disable' ? false : { rejectUnauthorized: false }
});

const app = express();
const server = http.createServer(app);
const io = new Server(server, { maxHttpBufferSize: 10 * 1024 * 1024 });

app.use(express.static(path.join(__dirname, 'public')));
app.get('/health', (_req, res) => res.json({ ok: true }));

const PROCEDURAL_SLOTS = {hair:'hairItemId',hats:'hatsItemId',heads:'headsItemId',eyes:'eyesItemId',mouth:'mouthItemId',skin:'skinItemId',tops:'topsItemId',bottoms:'bottomsItemId',shoes:'shoesItemId',flightsuits:'flightsuitsItemId'};
const defaultAppearance = {
  ...Object.fromEntries(Object.values(PROCEDURAL_SLOTS).map(slot=>[slot,null])),
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

// KWG V3.35 — User-generated text filter. Server is authoritative;
// client uses the same filter for optimistic previews and legacy content.
// Account passwords, internal IDs and numeric game data must NOT be filtered.
const KWG_BLOCKED_TERMS = [
  'fuck','fack','fucks','fucker','fuckers','fucking','motherfucker','motherfucking',
  'shit','shits','shitty','bullshit','bitch','bitches','bitching',
  'ass','asshole','assholes','dumbass','jackass','bastard','bastards',
  'damn','damned','hell','crap','piss','pissed','pissing',
  'dick','dicks','dickhead','cock','cocks','cocksucker','pussy','cunt','cunts',
  'slut','sluts','whore','whores','wtf','stfu',
  'nigger','niggers','nigga','niggas','faggot','faggots','fag','fags',
  'kike','kikes','spic','spics','chink','chinks','gook','gooks',
  'wetback','wetbacks','beaner','beaners','raghead','ragheads',
  'paki','pakis','tranny','trannies','retard','retards','retarded',
  'dyke','dykes','coon','coons',
  // Additional sexual terms and common variants missed by the original filter.
  'sex','sexy','sexual','sexuality','sext','sexting','sexted','sexts',
  'porn','porno','pornography','pornographic','pornhub','xxx',
  'nude','nudes','nudity','naked','horny','horniness','aroused',
  'penis','penises','vagina','vaginas','vaginal','vulva','vulvas',
  'boob','boobs','boobies','breast','breasts','tits','titties','nipple','nipples',
  'testicle','testicles','ballsack','scrotum','semen','sperm',
  'orgasm','orgasms','orgasmic','masturbate','masturbation','masturbating',
  'blowjob','blowjobs','handjob','handjobs','rimjob','rimjobs',
  'intercourse','ejaculate','ejaculation','ejaculating','erection','erections',
  'dildo','dildos','vibrator','vibrators','fetish','fetishes',
  'hentai','onlyfans','nsfw','anal','anus','clitoris','clit','clits',
  'cum','cums','cumming','cummed','jizz','boner','boners','erect',
  'threesome','threesomes','orgy','orgies','incest',
  'rape','raped','raping','rapist','molest','molested','molesting',
  'pedophile','paedophile','pedo','pedos',
];
// Spell-out numbers are blocked as *whole words* to avoid damaging
// harmless words such as someone, alone, stone, weight or sixth.
const KWG_NUMBER_WORDS = [
  'zero','one','two','three','four','five','six','seven','eight','nine',
  'ten','eleven','twelve','thirteen','fourteen','fifteen','sixteen',
  'seventeen','eighteen','nineteen','twenty','thirty','forty','fourty',
  'fifty','sixty','seventy','eighty','ninety','hundred','thousand',
  'million','billion','trillion',
  'first','second','third','fourth','fifth','sixth','seventh','eighth',
  'ninth','tenth','eleventh','twelfth','thirteenth','fourteenth',
  'fifteenth','sixteenth','seventeenth','eighteenth','nineteenth',
  'twentieth','thirtieth','fortieth','fiftieth','sixtieth',
  'seventieth','eightieth','ninetieth','hundredth','thousandth'
];
// Match obfuscated spellings such as s.e.x and t-w-o, while requiring
// word boundaries so innocent words are not partly censored.
const KWG_FILTER_TERMS = [...new Set([...KWG_BLOCKED_TERMS, ...KWG_NUMBER_WORDS])];
const KWG_BLOCKED_REGEX = new RegExp(
  '(^|[^a-z])(' + KWG_FILTER_TERMS
    .sort((a,b)=>b.length-a.length)
    .map(term=>term.split('').join('[\\s._-]{0,3}'))
    .join('|') + ')(?![a-z])','gi'
);
function filterKWGUserText(value){
  const raw=String(value??'');
  if(!raw)return raw;
  // Map common leetspeak and Unicode accents to comparable letters while
  // keeping an index for masking the exact characters in the original text.
  const map={'0':'o','1':'i','3':'e','4':'a','5':'s','7':'t','@':'a','$':'s',
    '!':'i','|':'i','€':'e','£':'l','+':'t','а':'a','е':'e','о':'o',
    'р':'p','с':'c','х':'x','у':'y','і':'i'};
  let folded='',offsets=[];
  for(let i=0;i<raw.length;){
    const ch=String.fromCodePoint(raw.codePointAt(i));
    const trailingPunctuation=['!','@','$'].includes(ch) && !/[a-z]/i.test(raw[i+ch.length]||'');
    const plain=(trailingPunctuation?ch:(map[ch]||ch.normalize('NFKD').replace(/[\u0300-\u036f]/g,'').toLowerCase()));
    for(const unit of plain){folded+=unit;offsets.push([i,i+ch.length]);}
    i+=ch.length;
  }
  const masked=new Set();
  for(const match of folded.matchAll(KWG_BLOCKED_REGEX)){
    const start=match.index+match[1].length;
    const end=start+match[2].length;
    for(let j=start;j<end;j++){
      const bounds=offsets[j];if(!bounds)continue;
      for(let k=bounds[0];k<bounds[1];k++)if(!/\s/.test(raw[k]))masked.add(k);
    }
  }
  // Numbers are masked even when embedded in otherwise permitted words.
  for(let i=0;i<raw.length;i++)if(/\p{N}/u.test(raw[i]))masked.add(i);
  return raw.split('').map((ch,i)=>masked.has(i)?'*':ch).join('');
}

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
    ...Object.fromEntries(Object.values(PROCEDURAL_SLOTS).map(slot=>[slot,cleanStoreItemId(a[slot])])),
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
    isVisible: !!row.is_visible,
    isUploaded: !!row.is_uploaded
  };
}

async function ensureStarterFlightsuit(userId){
  await pool.query(`INSERT INTO user_store_items(user_id,item_id)
    SELECT $1,id FROM store_items WHERE asset_url='procedural:flightsuits-0-2'
    ON CONFLICT DO NOTHING`,[userId]);
}
async function validateAppearanceForUser(userId, rawAppearance = {}) {
  await ensureStarterFlightsuit(userId);
  const app = sanitizeAppearance(rawAppearance);
  const slots = [
    ['eyesItemId', 'eyes'],
    ['mouthItemId', 'mouth'],
    ['torsoDecalItemId', 'torso_decal'],
    ['hatItemId', 'hat'],
    ['headShapeItemId', 'head_shape'],
    ...Object.entries(PROCEDURAL_SLOTS).map(([category,slot])=>[slot,category])
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
    headShapeItemId: 'head_shape',
    ...Object.fromEntries(Object.entries(PROCEDURAL_SLOTS).map(([category,slot])=>[slot,category]))
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

// World thumbnails are public JPEG screenshots; server validates the bytes and owns the upload.
async function uploadWorldThumbnail(worldId, imageData) {
  if (!SUPABASE_URL || !SUPABASE_SERVICE_ROLE_KEY) {
    const err=new Error('Thumbnail storage is not configured (SUPABASE_URL / SUPABASE_SERVICE_ROLE_KEY).');
    err.clientMessage=err.message; throw err;
  }
  if (typeof imageData !== 'string' || !/^data:image\/jpeg;base64,[A-Za-z0-9+/=]+$/.test(imageData) || imageData.length>2400000) {
    const err=new Error('Invalid thumbnail. Capture a new screenshot.');err.clientMessage=err.message;throw err;
  }
  const bytes=Buffer.from(imageData.slice('data:image/jpeg;base64,'.length),'base64');
  if (bytes.length<100 || bytes.length>1500000 || bytes[0]!==0xff || bytes[1]!==0xd8 || bytes[bytes.length-2]!==0xff || bytes[bytes.length-1]!==0xd9) {
    const err=new Error('Thumbnail must be a JPEG smaller than 1.5 MB.');err.clientMessage=err.message;throw err;
  }
  const bucket=encodeURIComponent(SUPABASE_THUMBNAIL_BUCKET);
  const check=await fetch(`${SUPABASE_URL}/storage/v1/bucket/${bucket}`,{headers:storageHeaders()});
  if (check.status===404) {
    const created=await fetch(`${SUPABASE_URL}/storage/v1/bucket`,{method:'POST',headers:storageHeaders({'Content-Type':'application/json'}),body:JSON.stringify({id:SUPABASE_THUMBNAIL_BUCKET,name:SUPABASE_THUMBNAIL_BUCKET,public:true})});
    if (!created.ok && created.status!==409) throw new Error(`Could not create thumbnail bucket (${created.status}).`);
  } else if (!check.ok) throw new Error(`Could not check thumbnail bucket (${check.status}).`);
  const key=`world-${Number(worldId)}/${Date.now()}-${crypto.randomBytes(6).toString('hex')}.jpg`;
  const url=`${SUPABASE_URL}/storage/v1/object/${bucket}/${key}`;
  const uploaded=await fetch(url,{method:'POST',headers:storageHeaders({'Content-Type':'image/jpeg','x-upsert':'false'}),body:bytes});
  if (!uploaded.ok) throw new Error(`Thumbnail upload failed (${uploaded.status}).`);
  return `${SUPABASE_URL}/storage/v1/object/public/${bucket}/${key}`;
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
    ALTER TABLE users ADD COLUMN IF NOT EXISTS bio VARCHAR(300) NOT NULL DEFAULT '';
    ALTER TABLE users ADD COLUMN IF NOT EXISTS showcased_world_ids BIGINT[] NOT NULL DEFAULT '{}'::bigint[];
    CREATE TABLE IF NOT EXISTS friendships (
      requester_id BIGINT NOT NULL REFERENCES users(id) ON DELETE CASCADE,
      addressee_id BIGINT NOT NULL REFERENCES users(id) ON DELETE CASCADE,
      status VARCHAR(16) NOT NULL DEFAULT 'pending' CHECK (status IN ('pending','accepted')),
      created_at TIMESTAMPTZ NOT NULL DEFAULT NOW(),
      updated_at TIMESTAMPTZ NOT NULL DEFAULT NOW(),
      PRIMARY KEY (requester_id, addressee_id),
      CHECK (requester_id <> addressee_id)
    );
    CREATE INDEX IF NOT EXISTS friendships_requester_idx ON friendships(requester_id,status);
    CREATE INDEX IF NOT EXISTS friendships_addressee_idx ON friendships(addressee_id,status);
    -- Blocking is directional, but all privacy effects apply to BOTH players.
    CREATE TABLE IF NOT EXISTS user_blocks (
      blocker_id BIGINT NOT NULL REFERENCES users(id) ON DELETE CASCADE,
      blocked_id BIGINT NOT NULL REFERENCES users(id) ON DELETE CASCADE,
      created_at TIMESTAMPTZ NOT NULL DEFAULT NOW(),
      PRIMARY KEY (blocker_id,blocked_id),
      CHECK (blocker_id <> blocked_id)
    );
    CREATE INDEX IF NOT EXISTS user_blocks_blocked_idx ON user_blocks(blocked_id);
    CREATE TABLE IF NOT EXISTS profile_messages (
      id BIGSERIAL PRIMARY KEY,
      profile_user_id BIGINT NOT NULL REFERENCES users(id) ON DELETE CASCADE,
      author_user_id BIGINT NOT NULL REFERENCES users(id) ON DELETE CASCADE,
      body VARCHAR(240) NOT NULL,
      created_at TIMESTAMPTZ NOT NULL DEFAULT NOW()
    );
    CREATE INDEX IF NOT EXISTS profile_messages_profile_idx ON profile_messages(profile_user_id,created_at DESC,id DESC);
    CREATE INDEX IF NOT EXISTS profile_messages_author_idx ON profile_messages(author_user_id,created_at DESC);
    CREATE TABLE IF NOT EXISTS notifications (
      id BIGSERIAL PRIMARY KEY,
      user_id BIGINT NOT NULL REFERENCES users(id) ON DELETE CASCADE,
      actor_user_id BIGINT REFERENCES users(id) ON DELETE SET NULL,
      type VARCHAR(40) NOT NULL,
      message VARCHAR(240) NOT NULL,
      is_read BOOLEAN NOT NULL DEFAULT FALSE,
      created_at TIMESTAMPTZ NOT NULL DEFAULT NOW()
    );
    CREATE INDEX IF NOT EXISTS notifications_user_idx ON notifications(user_id,created_at DESC);
    CREATE INDEX IF NOT EXISTS notifications_unread_idx ON notifications(user_id,is_read);

    CREATE TABLE IF NOT EXISTS store_items (
      id BIGSERIAL PRIMARY KEY,
      category VARCHAR(32) NOT NULL CHECK (category IN ('eyes','mouth','torso_decal','hat','head_shape','hair','hats','heads','eyes','mouth','skin','tops','bottoms','shoes','flightsuits')),
      name VARCHAR(40) NOT NULL,
      price INTEGER NOT NULL CHECK (price >= 0),
      asset_url TEXT NOT NULL,
      asset_kind VARCHAR(16) NOT NULL CHECK (asset_kind IN ('image','glb','avatar_glb','procedural')),
      metadata JSONB NOT NULL DEFAULT '{}'::jsonb,
      is_visible BOOLEAN NOT NULL DEFAULT TRUE,
      created_by BIGINT REFERENCES users(id) ON DELETE SET NULL,
      created_at TIMESTAMPTZ NOT NULL DEFAULT NOW(),
      updated_at TIMESTAMPTZ NOT NULL DEFAULT NOW()
    );

    ALTER TABLE store_items DROP CONSTRAINT IF EXISTS store_items_category_check;
    ALTER TABLE store_items ADD CONSTRAINT store_items_category_check CHECK (category IN ('eyes','mouth','torso_decal','hat','head_shape','hair','hats','heads','eyes','mouth','skin','tops','bottoms','shoes','flightsuits'));
    ALTER TABLE store_items DROP CONSTRAINT IF EXISTS store_items_asset_kind_check;
    ALTER TABLE store_items ADD CONSTRAINT store_items_asset_kind_check CHECK (asset_kind IN ('image','glb','avatar_glb','procedural'));
    CREATE UNIQUE INDEX IF NOT EXISTS store_items_procedural_key ON store_items(asset_url) WHERE asset_kind='procedural';
INSERT INTO store_items(category,name,price,asset_url,asset_kind,metadata) VALUES
('hair','Bald',45,'procedural:hair-0-0','procedural','{"key": "hair-0-0", "style": "Bald", "color": "#e6e6e6", "styleIndex": 0, "colorIndex": 0}'::jsonb),
('hair','Buzz Cut / 1',65,'procedural:hair-1-0','procedural','{"key": "hair-1-0", "style": "Buzz Cut", "color": "#e6e6e6", "styleIndex": 1, "colorIndex": 0}'::jsonb),
('hair','Buzz Cut / 2',70,'procedural:hair-1-1','procedural','{"key": "hair-1-1", "style": "Buzz Cut", "color": "#181818", "styleIndex": 1, "colorIndex": 1}'::jsonb),
('hair','Buzz Cut / 3',75,'procedural:hair-1-2','procedural','{"key": "hair-1-2", "style": "Buzz Cut", "color": "#ed4545", "styleIndex": 1, "colorIndex": 2}'::jsonb),
('hair','Buzz Cut / 4',80,'procedural:hair-1-3','procedural','{"key": "hair-1-3", "style": "Buzz Cut", "color": "#3689ed", "styleIndex": 1, "colorIndex": 3}'::jsonb),
('hair','Buzz Cut / 5',65,'procedural:hair-1-4','procedural','{"key": "hair-1-4", "style": "Buzz Cut", "color": "#37bf83", "styleIndex": 1, "colorIndex": 4}'::jsonb),
('hair','Buzz Cut / 6',70,'procedural:hair-1-5','procedural','{"key": "hair-1-5", "style": "Buzz Cut", "color": "#f4c542", "styleIndex": 1, "colorIndex": 5}'::jsonb),
('hair','Buzz Cut / 7',75,'procedural:hair-1-6','procedural','{"key": "hair-1-6", "style": "Buzz Cut", "color": "#9b62d9", "styleIndex": 1, "colorIndex": 6}'::jsonb),
('hair','Buzz Cut / 8',80,'procedural:hair-1-7','procedural','{"key": "hair-1-7", "style": "Buzz Cut", "color": "#ef88c0", "styleIndex": 1, "colorIndex": 7}'::jsonb),
('hair','Buzz Cut / 9',65,'procedural:hair-1-8','procedural','{"key": "hair-1-8", "style": "Buzz Cut", "color": "#ed8838", "styleIndex": 1, "colorIndex": 8}'::jsonb),
('hair','Buzz Cut / 10',70,'procedural:hair-1-9','procedural','{"key": "hair-1-9", "style": "Buzz Cut", "color": "#6b4b35", "styleIndex": 1, "colorIndex": 9}'::jsonb),
('hair','Buzz Cut / 11',75,'procedural:hair-1-10','procedural','{"key": "hair-1-10", "style": "Buzz Cut", "color": "#42d8d0", "styleIndex": 1, "colorIndex": 10}'::jsonb),
('hair','Buzz Cut / 12',80,'procedural:hair-1-11','procedural','{"key": "hair-1-11", "style": "Buzz Cut", "color": "#a5abb8", "styleIndex": 1, "colorIndex": 11}'::jsonb),
('hair','Crew Cut / 1',85,'procedural:hair-2-0','procedural','{"key": "hair-2-0", "style": "Crew Cut", "color": "#e6e6e6", "styleIndex": 2, "colorIndex": 0}'::jsonb),
('hair','Crew Cut / 2',90,'procedural:hair-2-1','procedural','{"key": "hair-2-1", "style": "Crew Cut", "color": "#181818", "styleIndex": 2, "colorIndex": 1}'::jsonb),
('hair','Crew Cut / 3',95,'procedural:hair-2-2','procedural','{"key": "hair-2-2", "style": "Crew Cut", "color": "#ed4545", "styleIndex": 2, "colorIndex": 2}'::jsonb),
('hair','Crew Cut / 4',100,'procedural:hair-2-3','procedural','{"key": "hair-2-3", "style": "Crew Cut", "color": "#3689ed", "styleIndex": 2, "colorIndex": 3}'::jsonb),
('hair','Crew Cut / 5',85,'procedural:hair-2-4','procedural','{"key": "hair-2-4", "style": "Crew Cut", "color": "#37bf83", "styleIndex": 2, "colorIndex": 4}'::jsonb),
('hair','Crew Cut / 6',90,'procedural:hair-2-5','procedural','{"key": "hair-2-5", "style": "Crew Cut", "color": "#f4c542", "styleIndex": 2, "colorIndex": 5}'::jsonb),
('hair','Crew Cut / 7',95,'procedural:hair-2-6','procedural','{"key": "hair-2-6", "style": "Crew Cut", "color": "#9b62d9", "styleIndex": 2, "colorIndex": 6}'::jsonb),
('hair','Crew Cut / 8',100,'procedural:hair-2-7','procedural','{"key": "hair-2-7", "style": "Crew Cut", "color": "#ef88c0", "styleIndex": 2, "colorIndex": 7}'::jsonb),
('hair','Crew Cut / 9',85,'procedural:hair-2-8','procedural','{"key": "hair-2-8", "style": "Crew Cut", "color": "#ed8838", "styleIndex": 2, "colorIndex": 8}'::jsonb),
('hair','Crew Cut / 10',90,'procedural:hair-2-9','procedural','{"key": "hair-2-9", "style": "Crew Cut", "color": "#6b4b35", "styleIndex": 2, "colorIndex": 9}'::jsonb),
('hair','Crew Cut / 11',95,'procedural:hair-2-10','procedural','{"key": "hair-2-10", "style": "Crew Cut", "color": "#42d8d0", "styleIndex": 2, "colorIndex": 10}'::jsonb),
('hair','Crew Cut / 12',100,'procedural:hair-2-11','procedural','{"key": "hair-2-11", "style": "Crew Cut", "color": "#a5abb8", "styleIndex": 2, "colorIndex": 11}'::jsonb),
('hair','Side Part / 1',105,'procedural:hair-3-0','procedural','{"key": "hair-3-0", "style": "Side Part", "color": "#e6e6e6", "styleIndex": 3, "colorIndex": 0}'::jsonb),
('hair','Side Part / 2',110,'procedural:hair-3-1','procedural','{"key": "hair-3-1", "style": "Side Part", "color": "#181818", "styleIndex": 3, "colorIndex": 1}'::jsonb),
('hair','Side Part / 3',115,'procedural:hair-3-2','procedural','{"key": "hair-3-2", "style": "Side Part", "color": "#ed4545", "styleIndex": 3, "colorIndex": 2}'::jsonb),
('hair','Side Part / 4',120,'procedural:hair-3-3','procedural','{"key": "hair-3-3", "style": "Side Part", "color": "#3689ed", "styleIndex": 3, "colorIndex": 3}'::jsonb),
('hair','Side Part / 5',105,'procedural:hair-3-4','procedural','{"key": "hair-3-4", "style": "Side Part", "color": "#37bf83", "styleIndex": 3, "colorIndex": 4}'::jsonb),
('hair','Side Part / 6',110,'procedural:hair-3-5','procedural','{"key": "hair-3-5", "style": "Side Part", "color": "#f4c542", "styleIndex": 3, "colorIndex": 5}'::jsonb),
('hair','Side Part / 7',115,'procedural:hair-3-6','procedural','{"key": "hair-3-6", "style": "Side Part", "color": "#9b62d9", "styleIndex": 3, "colorIndex": 6}'::jsonb),
('hair','Side Part / 8',120,'procedural:hair-3-7','procedural','{"key": "hair-3-7", "style": "Side Part", "color": "#ef88c0", "styleIndex": 3, "colorIndex": 7}'::jsonb),
('hair','Side Part / 9',105,'procedural:hair-3-8','procedural','{"key": "hair-3-8", "style": "Side Part", "color": "#ed8838", "styleIndex": 3, "colorIndex": 8}'::jsonb),
('hair','Side Part / 10',110,'procedural:hair-3-9','procedural','{"key": "hair-3-9", "style": "Side Part", "color": "#6b4b35", "styleIndex": 3, "colorIndex": 9}'::jsonb),
('hair','Side Part / 11',115,'procedural:hair-3-10','procedural','{"key": "hair-3-10", "style": "Side Part", "color": "#42d8d0", "styleIndex": 3, "colorIndex": 10}'::jsonb),
('hair','Side Part / 12',120,'procedural:hair-3-11','procedural','{"key": "hair-3-11", "style": "Side Part", "color": "#a5abb8", "styleIndex": 3, "colorIndex": 11}'::jsonb),
('hair','Pompadour / 1',125,'procedural:hair-4-0','procedural','{"key": "hair-4-0", "style": "Pompadour", "color": "#e6e6e6", "styleIndex": 4, "colorIndex": 0}'::jsonb),
('hair','Pompadour / 2',130,'procedural:hair-4-1','procedural','{"key": "hair-4-1", "style": "Pompadour", "color": "#181818", "styleIndex": 4, "colorIndex": 1}'::jsonb),
('hair','Pompadour / 3',135,'procedural:hair-4-2','procedural','{"key": "hair-4-2", "style": "Pompadour", "color": "#ed4545", "styleIndex": 4, "colorIndex": 2}'::jsonb),
('hair','Pompadour / 4',140,'procedural:hair-4-3','procedural','{"key": "hair-4-3", "style": "Pompadour", "color": "#3689ed", "styleIndex": 4, "colorIndex": 3}'::jsonb),
('hair','Pompadour / 5',125,'procedural:hair-4-4','procedural','{"key": "hair-4-4", "style": "Pompadour", "color": "#37bf83", "styleIndex": 4, "colorIndex": 4}'::jsonb),
('hair','Pompadour / 6',130,'procedural:hair-4-5','procedural','{"key": "hair-4-5", "style": "Pompadour", "color": "#f4c542", "styleIndex": 4, "colorIndex": 5}'::jsonb),
('hair','Pompadour / 7',135,'procedural:hair-4-6','procedural','{"key": "hair-4-6", "style": "Pompadour", "color": "#9b62d9", "styleIndex": 4, "colorIndex": 6}'::jsonb),
('hair','Pompadour / 8',140,'procedural:hair-4-7','procedural','{"key": "hair-4-7", "style": "Pompadour", "color": "#ef88c0", "styleIndex": 4, "colorIndex": 7}'::jsonb),
('hair','Pompadour / 9',125,'procedural:hair-4-8','procedural','{"key": "hair-4-8", "style": "Pompadour", "color": "#ed8838", "styleIndex": 4, "colorIndex": 8}'::jsonb),
('hair','Pompadour / 10',130,'procedural:hair-4-9','procedural','{"key": "hair-4-9", "style": "Pompadour", "color": "#6b4b35", "styleIndex": 4, "colorIndex": 9}'::jsonb),
('hair','Pompadour / 11',135,'procedural:hair-4-10','procedural','{"key": "hair-4-10", "style": "Pompadour", "color": "#42d8d0", "styleIndex": 4, "colorIndex": 10}'::jsonb),
('hair','Pompadour / 12',140,'procedural:hair-4-11','procedural','{"key": "hair-4-11", "style": "Pompadour", "color": "#a5abb8", "styleIndex": 4, "colorIndex": 11}'::jsonb),
('hair','Spiky / 1',45,'procedural:hair-5-0','procedural','{"key": "hair-5-0", "style": "Spiky", "color": "#e6e6e6", "styleIndex": 5, "colorIndex": 0}'::jsonb),
('hair','Spiky / 2',50,'procedural:hair-5-1','procedural','{"key": "hair-5-1", "style": "Spiky", "color": "#181818", "styleIndex": 5, "colorIndex": 1}'::jsonb),
('hair','Spiky / 3',55,'procedural:hair-5-2','procedural','{"key": "hair-5-2", "style": "Spiky", "color": "#ed4545", "styleIndex": 5, "colorIndex": 2}'::jsonb),
('hair','Spiky / 4',60,'procedural:hair-5-3','procedural','{"key": "hair-5-3", "style": "Spiky", "color": "#3689ed", "styleIndex": 5, "colorIndex": 3}'::jsonb),
('hair','Spiky / 5',45,'procedural:hair-5-4','procedural','{"key": "hair-5-4", "style": "Spiky", "color": "#37bf83", "styleIndex": 5, "colorIndex": 4}'::jsonb),
('hair','Spiky / 6',50,'procedural:hair-5-5','procedural','{"key": "hair-5-5", "style": "Spiky", "color": "#f4c542", "styleIndex": 5, "colorIndex": 5}'::jsonb),
('hair','Spiky / 7',55,'procedural:hair-5-6','procedural','{"key": "hair-5-6", "style": "Spiky", "color": "#9b62d9", "styleIndex": 5, "colorIndex": 6}'::jsonb),
('hair','Spiky / 8',60,'procedural:hair-5-7','procedural','{"key": "hair-5-7", "style": "Spiky", "color": "#ef88c0", "styleIndex": 5, "colorIndex": 7}'::jsonb),
('hair','Spiky / 9',45,'procedural:hair-5-8','procedural','{"key": "hair-5-8", "style": "Spiky", "color": "#ed8838", "styleIndex": 5, "colorIndex": 8}'::jsonb),
('hair','Spiky / 10',50,'procedural:hair-5-9','procedural','{"key": "hair-5-9", "style": "Spiky", "color": "#6b4b35", "styleIndex": 5, "colorIndex": 9}'::jsonb),
('hair','Spiky / 11',55,'procedural:hair-5-10','procedural','{"key": "hair-5-10", "style": "Spiky", "color": "#42d8d0", "styleIndex": 5, "colorIndex": 10}'::jsonb),
('hair','Spiky / 12',60,'procedural:hair-5-11','procedural','{"key": "hair-5-11", "style": "Spiky", "color": "#a5abb8", "styleIndex": 5, "colorIndex": 11}'::jsonb),
('hair','Wavy / 1',65,'procedural:hair-6-0','procedural','{"key": "hair-6-0", "style": "Wavy", "color": "#e6e6e6", "styleIndex": 6, "colorIndex": 0}'::jsonb),
('hair','Wavy / 2',70,'procedural:hair-6-1','procedural','{"key": "hair-6-1", "style": "Wavy", "color": "#181818", "styleIndex": 6, "colorIndex": 1}'::jsonb),
('hair','Wavy / 3',75,'procedural:hair-6-2','procedural','{"key": "hair-6-2", "style": "Wavy", "color": "#ed4545", "styleIndex": 6, "colorIndex": 2}'::jsonb),
('hair','Wavy / 4',80,'procedural:hair-6-3','procedural','{"key": "hair-6-3", "style": "Wavy", "color": "#3689ed", "styleIndex": 6, "colorIndex": 3}'::jsonb),
('hair','Wavy / 5',65,'procedural:hair-6-4','procedural','{"key": "hair-6-4", "style": "Wavy", "color": "#37bf83", "styleIndex": 6, "colorIndex": 4}'::jsonb),
('hair','Wavy / 6',70,'procedural:hair-6-5','procedural','{"key": "hair-6-5", "style": "Wavy", "color": "#f4c542", "styleIndex": 6, "colorIndex": 5}'::jsonb),
('hair','Wavy / 7',75,'procedural:hair-6-6','procedural','{"key": "hair-6-6", "style": "Wavy", "color": "#9b62d9", "styleIndex": 6, "colorIndex": 6}'::jsonb),
('hair','Wavy / 8',80,'procedural:hair-6-7','procedural','{"key": "hair-6-7", "style": "Wavy", "color": "#ef88c0", "styleIndex": 6, "colorIndex": 7}'::jsonb),
('hair','Wavy / 9',65,'procedural:hair-6-8','procedural','{"key": "hair-6-8", "style": "Wavy", "color": "#ed8838", "styleIndex": 6, "colorIndex": 8}'::jsonb),
('hair','Wavy / 10',70,'procedural:hair-6-9','procedural','{"key": "hair-6-9", "style": "Wavy", "color": "#6b4b35", "styleIndex": 6, "colorIndex": 9}'::jsonb),
('hair','Wavy / 11',75,'procedural:hair-6-10','procedural','{"key": "hair-6-10", "style": "Wavy", "color": "#42d8d0", "styleIndex": 6, "colorIndex": 10}'::jsonb),
('hair','Wavy / 12',80,'procedural:hair-6-11','procedural','{"key": "hair-6-11", "style": "Wavy", "color": "#a5abb8", "styleIndex": 6, "colorIndex": 11}'::jsonb),
('hair','Curly / 1',85,'procedural:hair-7-0','procedural','{"key": "hair-7-0", "style": "Curly", "color": "#e6e6e6", "styleIndex": 7, "colorIndex": 0}'::jsonb),
('hair','Curly / 2',90,'procedural:hair-7-1','procedural','{"key": "hair-7-1", "style": "Curly", "color": "#181818", "styleIndex": 7, "colorIndex": 1}'::jsonb),
('hair','Curly / 3',95,'procedural:hair-7-2','procedural','{"key": "hair-7-2", "style": "Curly", "color": "#ed4545", "styleIndex": 7, "colorIndex": 2}'::jsonb),
('hair','Curly / 4',100,'procedural:hair-7-3','procedural','{"key": "hair-7-3", "style": "Curly", "color": "#3689ed", "styleIndex": 7, "colorIndex": 3}'::jsonb),
('hair','Curly / 5',85,'procedural:hair-7-4','procedural','{"key": "hair-7-4", "style": "Curly", "color": "#37bf83", "styleIndex": 7, "colorIndex": 4}'::jsonb),
('hair','Curly / 6',90,'procedural:hair-7-5','procedural','{"key": "hair-7-5", "style": "Curly", "color": "#f4c542", "styleIndex": 7, "colorIndex": 5}'::jsonb),
('hair','Curly / 7',95,'procedural:hair-7-6','procedural','{"key": "hair-7-6", "style": "Curly", "color": "#9b62d9", "styleIndex": 7, "colorIndex": 6}'::jsonb),
('hair','Curly / 8',100,'procedural:hair-7-7','procedural','{"key": "hair-7-7", "style": "Curly", "color": "#ef88c0", "styleIndex": 7, "colorIndex": 7}'::jsonb),
('hair','Curly / 9',85,'procedural:hair-7-8','procedural','{"key": "hair-7-8", "style": "Curly", "color": "#ed8838", "styleIndex": 7, "colorIndex": 8}'::jsonb),
('hair','Curly / 10',90,'procedural:hair-7-9','procedural','{"key": "hair-7-9", "style": "Curly", "color": "#6b4b35", "styleIndex": 7, "colorIndex": 9}'::jsonb),
('hair','Curly / 11',95,'procedural:hair-7-10','procedural','{"key": "hair-7-10", "style": "Curly", "color": "#42d8d0", "styleIndex": 7, "colorIndex": 10}'::jsonb),
('hair','Curly / 12',100,'procedural:hair-7-11','procedural','{"key": "hair-7-11", "style": "Curly", "color": "#a5abb8", "styleIndex": 7, "colorIndex": 11}'::jsonb),
('hair','Afro / 1',105,'procedural:hair-8-0','procedural','{"key": "hair-8-0", "style": "Afro", "color": "#e6e6e6", "styleIndex": 8, "colorIndex": 0}'::jsonb),
('hair','Afro / 2',110,'procedural:hair-8-1','procedural','{"key": "hair-8-1", "style": "Afro", "color": "#181818", "styleIndex": 8, "colorIndex": 1}'::jsonb),
('hair','Afro / 3',115,'procedural:hair-8-2','procedural','{"key": "hair-8-2", "style": "Afro", "color": "#ed4545", "styleIndex": 8, "colorIndex": 2}'::jsonb),
('hair','Afro / 4',120,'procedural:hair-8-3','procedural','{"key": "hair-8-3", "style": "Afro", "color": "#3689ed", "styleIndex": 8, "colorIndex": 3}'::jsonb),
('hair','Afro / 5',105,'procedural:hair-8-4','procedural','{"key": "hair-8-4", "style": "Afro", "color": "#37bf83", "styleIndex": 8, "colorIndex": 4}'::jsonb),
('hair','Afro / 6',110,'procedural:hair-8-5','procedural','{"key": "hair-8-5", "style": "Afro", "color": "#f4c542", "styleIndex": 8, "colorIndex": 5}'::jsonb),
('hair','Afro / 7',115,'procedural:hair-8-6','procedural','{"key": "hair-8-6", "style": "Afro", "color": "#9b62d9", "styleIndex": 8, "colorIndex": 6}'::jsonb),
('hair','Afro / 8',120,'procedural:hair-8-7','procedural','{"key": "hair-8-7", "style": "Afro", "color": "#ef88c0", "styleIndex": 8, "colorIndex": 7}'::jsonb),
('hair','Afro / 9',105,'procedural:hair-8-8','procedural','{"key": "hair-8-8", "style": "Afro", "color": "#ed8838", "styleIndex": 8, "colorIndex": 8}'::jsonb),
('hair','Afro / 10',110,'procedural:hair-8-9','procedural','{"key": "hair-8-9", "style": "Afro", "color": "#6b4b35", "styleIndex": 8, "colorIndex": 9}'::jsonb),
('hair','Afro / 11',115,'procedural:hair-8-10','procedural','{"key": "hair-8-10", "style": "Afro", "color": "#42d8d0", "styleIndex": 8, "colorIndex": 10}'::jsonb),
('hair','Afro / 12',120,'procedural:hair-8-11','procedural','{"key": "hair-8-11", "style": "Afro", "color": "#a5abb8", "styleIndex": 8, "colorIndex": 11}'::jsonb),
('hair','Bob / 1',125,'procedural:hair-9-0','procedural','{"key": "hair-9-0", "style": "Bob", "color": "#e6e6e6", "styleIndex": 9, "colorIndex": 0}'::jsonb),
('hair','Bob / 2',130,'procedural:hair-9-1','procedural','{"key": "hair-9-1", "style": "Bob", "color": "#181818", "styleIndex": 9, "colorIndex": 1}'::jsonb),
('hair','Bob / 3',135,'procedural:hair-9-2','procedural','{"key": "hair-9-2", "style": "Bob", "color": "#ed4545", "styleIndex": 9, "colorIndex": 2}'::jsonb),
('hair','Bob / 4',140,'procedural:hair-9-3','procedural','{"key": "hair-9-3", "style": "Bob", "color": "#3689ed", "styleIndex": 9, "colorIndex": 3}'::jsonb),
('hair','Bob / 5',125,'procedural:hair-9-4','procedural','{"key": "hair-9-4", "style": "Bob", "color": "#37bf83", "styleIndex": 9, "colorIndex": 4}'::jsonb),
('hair','Bob / 6',130,'procedural:hair-9-5','procedural','{"key": "hair-9-5", "style": "Bob", "color": "#f4c542", "styleIndex": 9, "colorIndex": 5}'::jsonb),
('hair','Bob / 7',135,'procedural:hair-9-6','procedural','{"key": "hair-9-6", "style": "Bob", "color": "#9b62d9", "styleIndex": 9, "colorIndex": 6}'::jsonb),
('hair','Bob / 8',140,'procedural:hair-9-7','procedural','{"key": "hair-9-7", "style": "Bob", "color": "#ef88c0", "styleIndex": 9, "colorIndex": 7}'::jsonb),
('hair','Bob / 9',125,'procedural:hair-9-8','procedural','{"key": "hair-9-8", "style": "Bob", "color": "#ed8838", "styleIndex": 9, "colorIndex": 8}'::jsonb),
('hair','Bob / 10',130,'procedural:hair-9-9','procedural','{"key": "hair-9-9", "style": "Bob", "color": "#6b4b35", "styleIndex": 9, "colorIndex": 9}'::jsonb),
('hair','Bob / 11',135,'procedural:hair-9-10','procedural','{"key": "hair-9-10", "style": "Bob", "color": "#42d8d0", "styleIndex": 9, "colorIndex": 10}'::jsonb),
('hair','Bob / 12',140,'procedural:hair-9-11','procedural','{"key": "hair-9-11", "style": "Bob", "color": "#a5abb8", "styleIndex": 9, "colorIndex": 11}'::jsonb),
('hair','Pixie / 1',45,'procedural:hair-10-0','procedural','{"key": "hair-10-0", "style": "Pixie", "color": "#e6e6e6", "styleIndex": 10, "colorIndex": 0}'::jsonb),
('hair','Pixie / 2',50,'procedural:hair-10-1','procedural','{"key": "hair-10-1", "style": "Pixie", "color": "#181818", "styleIndex": 10, "colorIndex": 1}'::jsonb),
('hair','Pixie / 3',55,'procedural:hair-10-2','procedural','{"key": "hair-10-2", "style": "Pixie", "color": "#ed4545", "styleIndex": 10, "colorIndex": 2}'::jsonb),
('hair','Pixie / 4',60,'procedural:hair-10-3','procedural','{"key": "hair-10-3", "style": "Pixie", "color": "#3689ed", "styleIndex": 10, "colorIndex": 3}'::jsonb),
('hair','Pixie / 5',45,'procedural:hair-10-4','procedural','{"key": "hair-10-4", "style": "Pixie", "color": "#37bf83", "styleIndex": 10, "colorIndex": 4}'::jsonb),
('hair','Pixie / 6',50,'procedural:hair-10-5','procedural','{"key": "hair-10-5", "style": "Pixie", "color": "#f4c542", "styleIndex": 10, "colorIndex": 5}'::jsonb),
('hair','Pixie / 7',55,'procedural:hair-10-6','procedural','{"key": "hair-10-6", "style": "Pixie", "color": "#9b62d9", "styleIndex": 10, "colorIndex": 6}'::jsonb),
('hair','Pixie / 8',60,'procedural:hair-10-7','procedural','{"key": "hair-10-7", "style": "Pixie", "color": "#ef88c0", "styleIndex": 10, "colorIndex": 7}'::jsonb),
('hair','Pixie / 9',45,'procedural:hair-10-8','procedural','{"key": "hair-10-8", "style": "Pixie", "color": "#ed8838", "styleIndex": 10, "colorIndex": 8}'::jsonb),
('hair','Pixie / 10',50,'procedural:hair-10-9','procedural','{"key": "hair-10-9", "style": "Pixie", "color": "#6b4b35", "styleIndex": 10, "colorIndex": 9}'::jsonb),
('hair','Pixie / 11',55,'procedural:hair-10-10','procedural','{"key": "hair-10-10", "style": "Pixie", "color": "#42d8d0", "styleIndex": 10, "colorIndex": 10}'::jsonb) ON CONFLICT (asset_url) WHERE asset_kind='procedural' DO NOTHING;
INSERT INTO store_items(category,name,price,asset_url,asset_kind,metadata) VALUES
('hair','Pixie / 12',60,'procedural:hair-10-11','procedural','{"key": "hair-10-11", "style": "Pixie", "color": "#a5abb8", "styleIndex": 10, "colorIndex": 11}'::jsonb),
('hair','Mohawk / 1',65,'procedural:hair-11-0','procedural','{"key": "hair-11-0", "style": "Mohawk", "color": "#e6e6e6", "styleIndex": 11, "colorIndex": 0}'::jsonb),
('hair','Mohawk / 2',70,'procedural:hair-11-1','procedural','{"key": "hair-11-1", "style": "Mohawk", "color": "#181818", "styleIndex": 11, "colorIndex": 1}'::jsonb),
('hair','Mohawk / 3',75,'procedural:hair-11-2','procedural','{"key": "hair-11-2", "style": "Mohawk", "color": "#ed4545", "styleIndex": 11, "colorIndex": 2}'::jsonb),
('hair','Mohawk / 4',80,'procedural:hair-11-3','procedural','{"key": "hair-11-3", "style": "Mohawk", "color": "#3689ed", "styleIndex": 11, "colorIndex": 3}'::jsonb),
('hair','Mohawk / 5',65,'procedural:hair-11-4','procedural','{"key": "hair-11-4", "style": "Mohawk", "color": "#37bf83", "styleIndex": 11, "colorIndex": 4}'::jsonb),
('hair','Mohawk / 6',70,'procedural:hair-11-5','procedural','{"key": "hair-11-5", "style": "Mohawk", "color": "#f4c542", "styleIndex": 11, "colorIndex": 5}'::jsonb),
('hair','Mohawk / 7',75,'procedural:hair-11-6','procedural','{"key": "hair-11-6", "style": "Mohawk", "color": "#9b62d9", "styleIndex": 11, "colorIndex": 6}'::jsonb),
('hair','Mohawk / 8',80,'procedural:hair-11-7','procedural','{"key": "hair-11-7", "style": "Mohawk", "color": "#ef88c0", "styleIndex": 11, "colorIndex": 7}'::jsonb),
('hair','Mohawk / 9',65,'procedural:hair-11-8','procedural','{"key": "hair-11-8", "style": "Mohawk", "color": "#ed8838", "styleIndex": 11, "colorIndex": 8}'::jsonb),
('hair','Mohawk / 10',70,'procedural:hair-11-9','procedural','{"key": "hair-11-9", "style": "Mohawk", "color": "#6b4b35", "styleIndex": 11, "colorIndex": 9}'::jsonb),
('hair','Mohawk / 11',75,'procedural:hair-11-10','procedural','{"key": "hair-11-10", "style": "Mohawk", "color": "#42d8d0", "styleIndex": 11, "colorIndex": 10}'::jsonb),
('hair','Mohawk / 12',80,'procedural:hair-11-11','procedural','{"key": "hair-11-11", "style": "Mohawk", "color": "#a5abb8", "styleIndex": 11, "colorIndex": 11}'::jsonb),
('hair','Long Waves / 1',85,'procedural:hair-12-0','procedural','{"key": "hair-12-0", "style": "Long Waves", "color": "#e6e6e6", "styleIndex": 12, "colorIndex": 0}'::jsonb),
('hair','Long Waves / 2',90,'procedural:hair-12-1','procedural','{"key": "hair-12-1", "style": "Long Waves", "color": "#181818", "styleIndex": 12, "colorIndex": 1}'::jsonb),
('hair','Long Waves / 3',95,'procedural:hair-12-2','procedural','{"key": "hair-12-2", "style": "Long Waves", "color": "#ed4545", "styleIndex": 12, "colorIndex": 2}'::jsonb),
('hair','Long Waves / 4',100,'procedural:hair-12-3','procedural','{"key": "hair-12-3", "style": "Long Waves", "color": "#3689ed", "styleIndex": 12, "colorIndex": 3}'::jsonb),
('hair','Long Waves / 5',85,'procedural:hair-12-4','procedural','{"key": "hair-12-4", "style": "Long Waves", "color": "#37bf83", "styleIndex": 12, "colorIndex": 4}'::jsonb),
('hair','Long Waves / 6',90,'procedural:hair-12-5','procedural','{"key": "hair-12-5", "style": "Long Waves", "color": "#f4c542", "styleIndex": 12, "colorIndex": 5}'::jsonb),
('hair','Long Waves / 7',95,'procedural:hair-12-6','procedural','{"key": "hair-12-6", "style": "Long Waves", "color": "#9b62d9", "styleIndex": 12, "colorIndex": 6}'::jsonb),
('hair','Long Waves / 8',100,'procedural:hair-12-7','procedural','{"key": "hair-12-7", "style": "Long Waves", "color": "#ef88c0", "styleIndex": 12, "colorIndex": 7}'::jsonb),
('hair','Long Waves / 9',85,'procedural:hair-12-8','procedural','{"key": "hair-12-8", "style": "Long Waves", "color": "#ed8838", "styleIndex": 12, "colorIndex": 8}'::jsonb),
('hair','Long Waves / 10',90,'procedural:hair-12-9','procedural','{"key": "hair-12-9", "style": "Long Waves", "color": "#6b4b35", "styleIndex": 12, "colorIndex": 9}'::jsonb),
('hair','Long Waves / 11',95,'procedural:hair-12-10','procedural','{"key": "hair-12-10", "style": "Long Waves", "color": "#42d8d0", "styleIndex": 12, "colorIndex": 10}'::jsonb),
('hair','Long Waves / 12',100,'procedural:hair-12-11','procedural','{"key": "hair-12-11", "style": "Long Waves", "color": "#a5abb8", "styleIndex": 12, "colorIndex": 11}'::jsonb),
('hair','Ponytail / 1',105,'procedural:hair-13-0','procedural','{"key": "hair-13-0", "style": "Ponytail", "color": "#e6e6e6", "styleIndex": 13, "colorIndex": 0}'::jsonb),
('hair','Ponytail / 2',110,'procedural:hair-13-1','procedural','{"key": "hair-13-1", "style": "Ponytail", "color": "#181818", "styleIndex": 13, "colorIndex": 1}'::jsonb),
('hair','Ponytail / 3',115,'procedural:hair-13-2','procedural','{"key": "hair-13-2", "style": "Ponytail", "color": "#ed4545", "styleIndex": 13, "colorIndex": 2}'::jsonb),
('hair','Ponytail / 4',120,'procedural:hair-13-3','procedural','{"key": "hair-13-3", "style": "Ponytail", "color": "#3689ed", "styleIndex": 13, "colorIndex": 3}'::jsonb),
('hair','Ponytail / 5',105,'procedural:hair-13-4','procedural','{"key": "hair-13-4", "style": "Ponytail", "color": "#37bf83", "styleIndex": 13, "colorIndex": 4}'::jsonb),
('hair','Ponytail / 6',110,'procedural:hair-13-5','procedural','{"key": "hair-13-5", "style": "Ponytail", "color": "#f4c542", "styleIndex": 13, "colorIndex": 5}'::jsonb),
('hair','Ponytail / 7',115,'procedural:hair-13-6','procedural','{"key": "hair-13-6", "style": "Ponytail", "color": "#9b62d9", "styleIndex": 13, "colorIndex": 6}'::jsonb),
('hair','Ponytail / 8',120,'procedural:hair-13-7','procedural','{"key": "hair-13-7", "style": "Ponytail", "color": "#ef88c0", "styleIndex": 13, "colorIndex": 7}'::jsonb),
('hair','Ponytail / 9',105,'procedural:hair-13-8','procedural','{"key": "hair-13-8", "style": "Ponytail", "color": "#ed8838", "styleIndex": 13, "colorIndex": 8}'::jsonb),
('hair','Ponytail / 10',110,'procedural:hair-13-9','procedural','{"key": "hair-13-9", "style": "Ponytail", "color": "#6b4b35", "styleIndex": 13, "colorIndex": 9}'::jsonb),
('hair','Ponytail / 11',115,'procedural:hair-13-10','procedural','{"key": "hair-13-10", "style": "Ponytail", "color": "#42d8d0", "styleIndex": 13, "colorIndex": 10}'::jsonb),
('hair','Ponytail / 12',120,'procedural:hair-13-11','procedural','{"key": "hair-13-11", "style": "Ponytail", "color": "#a5abb8", "styleIndex": 13, "colorIndex": 11}'::jsonb),
('hair','Braids / 1',125,'procedural:hair-14-0','procedural','{"key": "hair-14-0", "style": "Braids", "color": "#e6e6e6", "styleIndex": 14, "colorIndex": 0}'::jsonb),
('hair','Braids / 2',130,'procedural:hair-14-1','procedural','{"key": "hair-14-1", "style": "Braids", "color": "#181818", "styleIndex": 14, "colorIndex": 1}'::jsonb),
('hair','Braids / 3',135,'procedural:hair-14-2','procedural','{"key": "hair-14-2", "style": "Braids", "color": "#ed4545", "styleIndex": 14, "colorIndex": 2}'::jsonb),
('hair','Braids / 4',140,'procedural:hair-14-3','procedural','{"key": "hair-14-3", "style": "Braids", "color": "#3689ed", "styleIndex": 14, "colorIndex": 3}'::jsonb),
('hair','Braids / 5',125,'procedural:hair-14-4','procedural','{"key": "hair-14-4", "style": "Braids", "color": "#37bf83", "styleIndex": 14, "colorIndex": 4}'::jsonb),
('hair','Braids / 6',130,'procedural:hair-14-5','procedural','{"key": "hair-14-5", "style": "Braids", "color": "#f4c542", "styleIndex": 14, "colorIndex": 5}'::jsonb),
('hair','Braids / 7',135,'procedural:hair-14-6','procedural','{"key": "hair-14-6", "style": "Braids", "color": "#9b62d9", "styleIndex": 14, "colorIndex": 6}'::jsonb),
('hair','Braids / 8',140,'procedural:hair-14-7','procedural','{"key": "hair-14-7", "style": "Braids", "color": "#ef88c0", "styleIndex": 14, "colorIndex": 7}'::jsonb),
('hair','Braids / 9',125,'procedural:hair-14-8','procedural','{"key": "hair-14-8", "style": "Braids", "color": "#ed8838", "styleIndex": 14, "colorIndex": 8}'::jsonb),
('hair','Braids / 10',130,'procedural:hair-14-9','procedural','{"key": "hair-14-9", "style": "Braids", "color": "#6b4b35", "styleIndex": 14, "colorIndex": 9}'::jsonb),
('hair','Braids / 11',135,'procedural:hair-14-10','procedural','{"key": "hair-14-10", "style": "Braids", "color": "#42d8d0", "styleIndex": 14, "colorIndex": 10}'::jsonb),
('hair','Braids / 12',140,'procedural:hair-14-11','procedural','{"key": "hair-14-11", "style": "Braids", "color": "#a5abb8", "styleIndex": 14, "colorIndex": 11}'::jsonb),
('hair','Bowl Cut / 1',45,'procedural:hair-15-0','procedural','{"key": "hair-15-0", "style": "Bowl Cut", "color": "#e6e6e6", "styleIndex": 15, "colorIndex": 0}'::jsonb),
('hair','Bowl Cut / 2',50,'procedural:hair-15-1','procedural','{"key": "hair-15-1", "style": "Bowl Cut", "color": "#181818", "styleIndex": 15, "colorIndex": 1}'::jsonb),
('hair','Bowl Cut / 3',55,'procedural:hair-15-2','procedural','{"key": "hair-15-2", "style": "Bowl Cut", "color": "#ed4545", "styleIndex": 15, "colorIndex": 2}'::jsonb),
('hair','Bowl Cut / 4',60,'procedural:hair-15-3','procedural','{"key": "hair-15-3", "style": "Bowl Cut", "color": "#3689ed", "styleIndex": 15, "colorIndex": 3}'::jsonb),
('hair','Bowl Cut / 5',45,'procedural:hair-15-4','procedural','{"key": "hair-15-4", "style": "Bowl Cut", "color": "#37bf83", "styleIndex": 15, "colorIndex": 4}'::jsonb),
('hair','Bowl Cut / 6',50,'procedural:hair-15-5','procedural','{"key": "hair-15-5", "style": "Bowl Cut", "color": "#f4c542", "styleIndex": 15, "colorIndex": 5}'::jsonb),
('hair','Bowl Cut / 7',55,'procedural:hair-15-6','procedural','{"key": "hair-15-6", "style": "Bowl Cut", "color": "#9b62d9", "styleIndex": 15, "colorIndex": 6}'::jsonb),
('hair','Bowl Cut / 8',60,'procedural:hair-15-7','procedural','{"key": "hair-15-7", "style": "Bowl Cut", "color": "#ef88c0", "styleIndex": 15, "colorIndex": 7}'::jsonb),
('hair','Bowl Cut / 9',45,'procedural:hair-15-8','procedural','{"key": "hair-15-8", "style": "Bowl Cut", "color": "#ed8838", "styleIndex": 15, "colorIndex": 8}'::jsonb),
('hair','Bowl Cut / 10',50,'procedural:hair-15-9','procedural','{"key": "hair-15-9", "style": "Bowl Cut", "color": "#6b4b35", "styleIndex": 15, "colorIndex": 9}'::jsonb),
('hair','Bowl Cut / 11',55,'procedural:hair-15-10','procedural','{"key": "hair-15-10", "style": "Bowl Cut", "color": "#42d8d0", "styleIndex": 15, "colorIndex": 10}'::jsonb),
('hair','Bowl Cut / 12',60,'procedural:hair-15-11','procedural','{"key": "hair-15-11", "style": "Bowl Cut", "color": "#a5abb8", "styleIndex": 15, "colorIndex": 11}'::jsonb),
('hats','None',45,'procedural:hats-0-0','procedural','{"key": "hats-0-0", "style": "None", "color": "#e6e6e6", "styleIndex": 0, "colorIndex": 0}'::jsonb),
('hats','Baseball Cap / 1',65,'procedural:hats-1-0','procedural','{"key": "hats-1-0", "style": "Baseball Cap", "color": "#e6e6e6", "styleIndex": 1, "colorIndex": 0}'::jsonb),
('hats','Baseball Cap / 2',70,'procedural:hats-1-1','procedural','{"key": "hats-1-1", "style": "Baseball Cap", "color": "#181818", "styleIndex": 1, "colorIndex": 1}'::jsonb),
('hats','Baseball Cap / 3',75,'procedural:hats-1-2','procedural','{"key": "hats-1-2", "style": "Baseball Cap", "color": "#ed4545", "styleIndex": 1, "colorIndex": 2}'::jsonb),
('hats','Baseball Cap / 4',80,'procedural:hats-1-3','procedural','{"key": "hats-1-3", "style": "Baseball Cap", "color": "#3689ed", "styleIndex": 1, "colorIndex": 3}'::jsonb),
('hats','Baseball Cap / 5',65,'procedural:hats-1-4','procedural','{"key": "hats-1-4", "style": "Baseball Cap", "color": "#37bf83", "styleIndex": 1, "colorIndex": 4}'::jsonb),
('hats','Baseball Cap / 6',70,'procedural:hats-1-5','procedural','{"key": "hats-1-5", "style": "Baseball Cap", "color": "#f4c542", "styleIndex": 1, "colorIndex": 5}'::jsonb),
('hats','Baseball Cap / 7',75,'procedural:hats-1-6','procedural','{"key": "hats-1-6", "style": "Baseball Cap", "color": "#9b62d9", "styleIndex": 1, "colorIndex": 6}'::jsonb),
('hats','Baseball Cap / 8',80,'procedural:hats-1-7','procedural','{"key": "hats-1-7", "style": "Baseball Cap", "color": "#ef88c0", "styleIndex": 1, "colorIndex": 7}'::jsonb),
('hats','Baseball Cap / 9',65,'procedural:hats-1-8','procedural','{"key": "hats-1-8", "style": "Baseball Cap", "color": "#ed8838", "styleIndex": 1, "colorIndex": 8}'::jsonb),
('hats','Baseball Cap / 10',70,'procedural:hats-1-9','procedural','{"key": "hats-1-9", "style": "Baseball Cap", "color": "#6b4b35", "styleIndex": 1, "colorIndex": 9}'::jsonb),
('hats','Baseball Cap / 11',75,'procedural:hats-1-10','procedural','{"key": "hats-1-10", "style": "Baseball Cap", "color": "#42d8d0", "styleIndex": 1, "colorIndex": 10}'::jsonb),
('hats','Baseball Cap / 12',80,'procedural:hats-1-11','procedural','{"key": "hats-1-11", "style": "Baseball Cap", "color": "#a5abb8", "styleIndex": 1, "colorIndex": 11}'::jsonb),
('hats','Beanie / 1',85,'procedural:hats-2-0','procedural','{"key": "hats-2-0", "style": "Beanie", "color": "#e6e6e6", "styleIndex": 2, "colorIndex": 0}'::jsonb),
('hats','Beanie / 2',90,'procedural:hats-2-1','procedural','{"key": "hats-2-1", "style": "Beanie", "color": "#181818", "styleIndex": 2, "colorIndex": 1}'::jsonb),
('hats','Beanie / 3',95,'procedural:hats-2-2','procedural','{"key": "hats-2-2", "style": "Beanie", "color": "#ed4545", "styleIndex": 2, "colorIndex": 2}'::jsonb),
('hats','Beanie / 4',100,'procedural:hats-2-3','procedural','{"key": "hats-2-3", "style": "Beanie", "color": "#3689ed", "styleIndex": 2, "colorIndex": 3}'::jsonb),
('hats','Beanie / 5',85,'procedural:hats-2-4','procedural','{"key": "hats-2-4", "style": "Beanie", "color": "#37bf83", "styleIndex": 2, "colorIndex": 4}'::jsonb),
('hats','Beanie / 6',90,'procedural:hats-2-5','procedural','{"key": "hats-2-5", "style": "Beanie", "color": "#f4c542", "styleIndex": 2, "colorIndex": 5}'::jsonb),
('hats','Beanie / 7',95,'procedural:hats-2-6','procedural','{"key": "hats-2-6", "style": "Beanie", "color": "#9b62d9", "styleIndex": 2, "colorIndex": 6}'::jsonb),
('hats','Beanie / 8',100,'procedural:hats-2-7','procedural','{"key": "hats-2-7", "style": "Beanie", "color": "#ef88c0", "styleIndex": 2, "colorIndex": 7}'::jsonb),
('hats','Beanie / 9',85,'procedural:hats-2-8','procedural','{"key": "hats-2-8", "style": "Beanie", "color": "#ed8838", "styleIndex": 2, "colorIndex": 8}'::jsonb),
('hats','Beanie / 10',90,'procedural:hats-2-9','procedural','{"key": "hats-2-9", "style": "Beanie", "color": "#6b4b35", "styleIndex": 2, "colorIndex": 9}'::jsonb),
('hats','Beanie / 11',95,'procedural:hats-2-10','procedural','{"key": "hats-2-10", "style": "Beanie", "color": "#42d8d0", "styleIndex": 2, "colorIndex": 10}'::jsonb),
('hats','Beanie / 12',100,'procedural:hats-2-11','procedural','{"key": "hats-2-11", "style": "Beanie", "color": "#a5abb8", "styleIndex": 2, "colorIndex": 11}'::jsonb),
('hats','Top Hat / 1',105,'procedural:hats-3-0','procedural','{"key": "hats-3-0", "style": "Top Hat", "color": "#e6e6e6", "styleIndex": 3, "colorIndex": 0}'::jsonb),
('hats','Top Hat / 2',110,'procedural:hats-3-1','procedural','{"key": "hats-3-1", "style": "Top Hat", "color": "#181818", "styleIndex": 3, "colorIndex": 1}'::jsonb),
('hats','Top Hat / 3',115,'procedural:hats-3-2','procedural','{"key": "hats-3-2", "style": "Top Hat", "color": "#ed4545", "styleIndex": 3, "colorIndex": 2}'::jsonb),
('hats','Top Hat / 4',120,'procedural:hats-3-3','procedural','{"key": "hats-3-3", "style": "Top Hat", "color": "#3689ed", "styleIndex": 3, "colorIndex": 3}'::jsonb),
('hats','Top Hat / 5',105,'procedural:hats-3-4','procedural','{"key": "hats-3-4", "style": "Top Hat", "color": "#37bf83", "styleIndex": 3, "colorIndex": 4}'::jsonb),
('hats','Top Hat / 6',110,'procedural:hats-3-5','procedural','{"key": "hats-3-5", "style": "Top Hat", "color": "#f4c542", "styleIndex": 3, "colorIndex": 5}'::jsonb),
('hats','Top Hat / 7',115,'procedural:hats-3-6','procedural','{"key": "hats-3-6", "style": "Top Hat", "color": "#9b62d9", "styleIndex": 3, "colorIndex": 6}'::jsonb),
('hats','Top Hat / 8',120,'procedural:hats-3-7','procedural','{"key": "hats-3-7", "style": "Top Hat", "color": "#ef88c0", "styleIndex": 3, "colorIndex": 7}'::jsonb),
('hats','Top Hat / 9',105,'procedural:hats-3-8','procedural','{"key": "hats-3-8", "style": "Top Hat", "color": "#ed8838", "styleIndex": 3, "colorIndex": 8}'::jsonb),
('hats','Top Hat / 10',110,'procedural:hats-3-9','procedural','{"key": "hats-3-9", "style": "Top Hat", "color": "#6b4b35", "styleIndex": 3, "colorIndex": 9}'::jsonb),
('hats','Top Hat / 11',115,'procedural:hats-3-10','procedural','{"key": "hats-3-10", "style": "Top Hat", "color": "#42d8d0", "styleIndex": 3, "colorIndex": 10}'::jsonb),
('hats','Top Hat / 12',120,'procedural:hats-3-11','procedural','{"key": "hats-3-11", "style": "Top Hat", "color": "#a5abb8", "styleIndex": 3, "colorIndex": 11}'::jsonb),
('hats','Bucket Hat / 1',125,'procedural:hats-4-0','procedural','{"key": "hats-4-0", "style": "Bucket Hat", "color": "#e6e6e6", "styleIndex": 4, "colorIndex": 0}'::jsonb),
('hats','Bucket Hat / 2',130,'procedural:hats-4-1','procedural','{"key": "hats-4-1", "style": "Bucket Hat", "color": "#181818", "styleIndex": 4, "colorIndex": 1}'::jsonb),
('hats','Bucket Hat / 3',135,'procedural:hats-4-2','procedural','{"key": "hats-4-2", "style": "Bucket Hat", "color": "#ed4545", "styleIndex": 4, "colorIndex": 2}'::jsonb),
('hats','Bucket Hat / 4',140,'procedural:hats-4-3','procedural','{"key": "hats-4-3", "style": "Bucket Hat", "color": "#3689ed", "styleIndex": 4, "colorIndex": 3}'::jsonb),
('hats','Bucket Hat / 5',125,'procedural:hats-4-4','procedural','{"key": "hats-4-4", "style": "Bucket Hat", "color": "#37bf83", "styleIndex": 4, "colorIndex": 4}'::jsonb),
('hats','Bucket Hat / 6',130,'procedural:hats-4-5','procedural','{"key": "hats-4-5", "style": "Bucket Hat", "color": "#f4c542", "styleIndex": 4, "colorIndex": 5}'::jsonb),
('hats','Bucket Hat / 7',135,'procedural:hats-4-6','procedural','{"key": "hats-4-6", "style": "Bucket Hat", "color": "#9b62d9", "styleIndex": 4, "colorIndex": 6}'::jsonb),
('hats','Bucket Hat / 8',140,'procedural:hats-4-7','procedural','{"key": "hats-4-7", "style": "Bucket Hat", "color": "#ef88c0", "styleIndex": 4, "colorIndex": 7}'::jsonb),
('hats','Bucket Hat / 9',125,'procedural:hats-4-8','procedural','{"key": "hats-4-8", "style": "Bucket Hat", "color": "#ed8838", "styleIndex": 4, "colorIndex": 8}'::jsonb),
('hats','Bucket Hat / 10',130,'procedural:hats-4-9','procedural','{"key": "hats-4-9", "style": "Bucket Hat", "color": "#6b4b35", "styleIndex": 4, "colorIndex": 9}'::jsonb),
('hats','Bucket Hat / 11',135,'procedural:hats-4-10','procedural','{"key": "hats-4-10", "style": "Bucket Hat", "color": "#42d8d0", "styleIndex": 4, "colorIndex": 10}'::jsonb),
('hats','Bucket Hat / 12',140,'procedural:hats-4-11','procedural','{"key": "hats-4-11", "style": "Bucket Hat", "color": "#a5abb8", "styleIndex": 4, "colorIndex": 11}'::jsonb),
('hats','Cowboy Hat / 1',45,'procedural:hats-5-0','procedural','{"key": "hats-5-0", "style": "Cowboy Hat", "color": "#e6e6e6", "styleIndex": 5, "colorIndex": 0}'::jsonb),
('hats','Cowboy Hat / 2',50,'procedural:hats-5-1','procedural','{"key": "hats-5-1", "style": "Cowboy Hat", "color": "#181818", "styleIndex": 5, "colorIndex": 1}'::jsonb),
('hats','Cowboy Hat / 3',55,'procedural:hats-5-2','procedural','{"key": "hats-5-2", "style": "Cowboy Hat", "color": "#ed4545", "styleIndex": 5, "colorIndex": 2}'::jsonb),
('hats','Cowboy Hat / 4',60,'procedural:hats-5-3','procedural','{"key": "hats-5-3", "style": "Cowboy Hat", "color": "#3689ed", "styleIndex": 5, "colorIndex": 3}'::jsonb),
('hats','Cowboy Hat / 5',45,'procedural:hats-5-4','procedural','{"key": "hats-5-4", "style": "Cowboy Hat", "color": "#37bf83", "styleIndex": 5, "colorIndex": 4}'::jsonb),
('hats','Cowboy Hat / 6',50,'procedural:hats-5-5','procedural','{"key": "hats-5-5", "style": "Cowboy Hat", "color": "#f4c542", "styleIndex": 5, "colorIndex": 5}'::jsonb),
('hats','Cowboy Hat / 7',55,'procedural:hats-5-6','procedural','{"key": "hats-5-6", "style": "Cowboy Hat", "color": "#9b62d9", "styleIndex": 5, "colorIndex": 6}'::jsonb),
('hats','Cowboy Hat / 8',60,'procedural:hats-5-7','procedural','{"key": "hats-5-7", "style": "Cowboy Hat", "color": "#ef88c0", "styleIndex": 5, "colorIndex": 7}'::jsonb),
('hats','Cowboy Hat / 9',45,'procedural:hats-5-8','procedural','{"key": "hats-5-8", "style": "Cowboy Hat", "color": "#ed8838", "styleIndex": 5, "colorIndex": 8}'::jsonb),
('hats','Cowboy Hat / 10',50,'procedural:hats-5-9','procedural','{"key": "hats-5-9", "style": "Cowboy Hat", "color": "#6b4b35", "styleIndex": 5, "colorIndex": 9}'::jsonb) ON CONFLICT (asset_url) WHERE asset_kind='procedural' DO NOTHING;
INSERT INTO store_items(category,name,price,asset_url,asset_kind,metadata) VALUES
('hats','Cowboy Hat / 11',55,'procedural:hats-5-10','procedural','{"key": "hats-5-10", "style": "Cowboy Hat", "color": "#42d8d0", "styleIndex": 5, "colorIndex": 10}'::jsonb),
('hats','Cowboy Hat / 12',60,'procedural:hats-5-11','procedural','{"key": "hats-5-11", "style": "Cowboy Hat", "color": "#a5abb8", "styleIndex": 5, "colorIndex": 11}'::jsonb),
('hats','Fedora / 1',65,'procedural:hats-6-0','procedural','{"key": "hats-6-0", "style": "Fedora", "color": "#e6e6e6", "styleIndex": 6, "colorIndex": 0}'::jsonb),
('hats','Fedora / 2',70,'procedural:hats-6-1','procedural','{"key": "hats-6-1", "style": "Fedora", "color": "#181818", "styleIndex": 6, "colorIndex": 1}'::jsonb),
('hats','Fedora / 3',75,'procedural:hats-6-2','procedural','{"key": "hats-6-2", "style": "Fedora", "color": "#ed4545", "styleIndex": 6, "colorIndex": 2}'::jsonb),
('hats','Fedora / 4',80,'procedural:hats-6-3','procedural','{"key": "hats-6-3", "style": "Fedora", "color": "#3689ed", "styleIndex": 6, "colorIndex": 3}'::jsonb),
('hats','Fedora / 5',65,'procedural:hats-6-4','procedural','{"key": "hats-6-4", "style": "Fedora", "color": "#37bf83", "styleIndex": 6, "colorIndex": 4}'::jsonb),
('hats','Fedora / 6',70,'procedural:hats-6-5','procedural','{"key": "hats-6-5", "style": "Fedora", "color": "#f4c542", "styleIndex": 6, "colorIndex": 5}'::jsonb),
('hats','Fedora / 7',75,'procedural:hats-6-6','procedural','{"key": "hats-6-6", "style": "Fedora", "color": "#9b62d9", "styleIndex": 6, "colorIndex": 6}'::jsonb),
('hats','Fedora / 8',80,'procedural:hats-6-7','procedural','{"key": "hats-6-7", "style": "Fedora", "color": "#ef88c0", "styleIndex": 6, "colorIndex": 7}'::jsonb),
('hats','Fedora / 9',65,'procedural:hats-6-8','procedural','{"key": "hats-6-8", "style": "Fedora", "color": "#ed8838", "styleIndex": 6, "colorIndex": 8}'::jsonb),
('hats','Fedora / 10',70,'procedural:hats-6-9','procedural','{"key": "hats-6-9", "style": "Fedora", "color": "#6b4b35", "styleIndex": 6, "colorIndex": 9}'::jsonb),
('hats','Fedora / 11',75,'procedural:hats-6-10','procedural','{"key": "hats-6-10", "style": "Fedora", "color": "#42d8d0", "styleIndex": 6, "colorIndex": 10}'::jsonb),
('hats','Fedora / 12',80,'procedural:hats-6-11','procedural','{"key": "hats-6-11", "style": "Fedora", "color": "#a5abb8", "styleIndex": 6, "colorIndex": 11}'::jsonb),
('hats','Sun Hat / 1',85,'procedural:hats-7-0','procedural','{"key": "hats-7-0", "style": "Sun Hat", "color": "#e6e6e6", "styleIndex": 7, "colorIndex": 0}'::jsonb),
('hats','Sun Hat / 2',90,'procedural:hats-7-1','procedural','{"key": "hats-7-1", "style": "Sun Hat", "color": "#181818", "styleIndex": 7, "colorIndex": 1}'::jsonb),
('hats','Sun Hat / 3',95,'procedural:hats-7-2','procedural','{"key": "hats-7-2", "style": "Sun Hat", "color": "#ed4545", "styleIndex": 7, "colorIndex": 2}'::jsonb),
('hats','Sun Hat / 4',100,'procedural:hats-7-3','procedural','{"key": "hats-7-3", "style": "Sun Hat", "color": "#3689ed", "styleIndex": 7, "colorIndex": 3}'::jsonb),
('hats','Sun Hat / 5',85,'procedural:hats-7-4','procedural','{"key": "hats-7-4", "style": "Sun Hat", "color": "#37bf83", "styleIndex": 7, "colorIndex": 4}'::jsonb),
('hats','Sun Hat / 6',90,'procedural:hats-7-5','procedural','{"key": "hats-7-5", "style": "Sun Hat", "color": "#f4c542", "styleIndex": 7, "colorIndex": 5}'::jsonb),
('hats','Sun Hat / 7',95,'procedural:hats-7-6','procedural','{"key": "hats-7-6", "style": "Sun Hat", "color": "#9b62d9", "styleIndex": 7, "colorIndex": 6}'::jsonb),
('hats','Sun Hat / 8',100,'procedural:hats-7-7','procedural','{"key": "hats-7-7", "style": "Sun Hat", "color": "#ef88c0", "styleIndex": 7, "colorIndex": 7}'::jsonb),
('hats','Sun Hat / 9',85,'procedural:hats-7-8','procedural','{"key": "hats-7-8", "style": "Sun Hat", "color": "#ed8838", "styleIndex": 7, "colorIndex": 8}'::jsonb),
('hats','Sun Hat / 10',90,'procedural:hats-7-9','procedural','{"key": "hats-7-9", "style": "Sun Hat", "color": "#6b4b35", "styleIndex": 7, "colorIndex": 9}'::jsonb),
('hats','Sun Hat / 11',95,'procedural:hats-7-10','procedural','{"key": "hats-7-10", "style": "Sun Hat", "color": "#42d8d0", "styleIndex": 7, "colorIndex": 10}'::jsonb),
('hats','Sun Hat / 12',100,'procedural:hats-7-11','procedural','{"key": "hats-7-11", "style": "Sun Hat", "color": "#a5abb8", "styleIndex": 7, "colorIndex": 11}'::jsonb),
('hats','Wizard Hat / 1',105,'procedural:hats-8-0','procedural','{"key": "hats-8-0", "style": "Wizard Hat", "color": "#e6e6e6", "styleIndex": 8, "colorIndex": 0}'::jsonb),
('hats','Wizard Hat / 2',110,'procedural:hats-8-1','procedural','{"key": "hats-8-1", "style": "Wizard Hat", "color": "#181818", "styleIndex": 8, "colorIndex": 1}'::jsonb),
('hats','Wizard Hat / 3',115,'procedural:hats-8-2','procedural','{"key": "hats-8-2", "style": "Wizard Hat", "color": "#ed4545", "styleIndex": 8, "colorIndex": 2}'::jsonb),
('hats','Wizard Hat / 4',120,'procedural:hats-8-3','procedural','{"key": "hats-8-3", "style": "Wizard Hat", "color": "#3689ed", "styleIndex": 8, "colorIndex": 3}'::jsonb),
('hats','Wizard Hat / 5',105,'procedural:hats-8-4','procedural','{"key": "hats-8-4", "style": "Wizard Hat", "color": "#37bf83", "styleIndex": 8, "colorIndex": 4}'::jsonb),
('hats','Wizard Hat / 6',110,'procedural:hats-8-5','procedural','{"key": "hats-8-5", "style": "Wizard Hat", "color": "#f4c542", "styleIndex": 8, "colorIndex": 5}'::jsonb),
('hats','Wizard Hat / 7',115,'procedural:hats-8-6','procedural','{"key": "hats-8-6", "style": "Wizard Hat", "color": "#9b62d9", "styleIndex": 8, "colorIndex": 6}'::jsonb),
('hats','Wizard Hat / 8',120,'procedural:hats-8-7','procedural','{"key": "hats-8-7", "style": "Wizard Hat", "color": "#ef88c0", "styleIndex": 8, "colorIndex": 7}'::jsonb),
('hats','Wizard Hat / 9',105,'procedural:hats-8-8','procedural','{"key": "hats-8-8", "style": "Wizard Hat", "color": "#ed8838", "styleIndex": 8, "colorIndex": 8}'::jsonb),
('hats','Wizard Hat / 10',110,'procedural:hats-8-9','procedural','{"key": "hats-8-9", "style": "Wizard Hat", "color": "#6b4b35", "styleIndex": 8, "colorIndex": 9}'::jsonb),
('hats','Wizard Hat / 11',115,'procedural:hats-8-10','procedural','{"key": "hats-8-10", "style": "Wizard Hat", "color": "#42d8d0", "styleIndex": 8, "colorIndex": 10}'::jsonb),
('hats','Wizard Hat / 12',120,'procedural:hats-8-11','procedural','{"key": "hats-8-11", "style": "Wizard Hat", "color": "#a5abb8", "styleIndex": 8, "colorIndex": 11}'::jsonb),
('hats','Beret / 1',125,'procedural:hats-9-0','procedural','{"key": "hats-9-0", "style": "Beret", "color": "#e6e6e6", "styleIndex": 9, "colorIndex": 0}'::jsonb),
('hats','Beret / 2',130,'procedural:hats-9-1','procedural','{"key": "hats-9-1", "style": "Beret", "color": "#181818", "styleIndex": 9, "colorIndex": 1}'::jsonb),
('hats','Beret / 3',135,'procedural:hats-9-2','procedural','{"key": "hats-9-2", "style": "Beret", "color": "#ed4545", "styleIndex": 9, "colorIndex": 2}'::jsonb),
('hats','Beret / 4',140,'procedural:hats-9-3','procedural','{"key": "hats-9-3", "style": "Beret", "color": "#3689ed", "styleIndex": 9, "colorIndex": 3}'::jsonb),
('hats','Beret / 5',125,'procedural:hats-9-4','procedural','{"key": "hats-9-4", "style": "Beret", "color": "#37bf83", "styleIndex": 9, "colorIndex": 4}'::jsonb),
('hats','Beret / 6',130,'procedural:hats-9-5','procedural','{"key": "hats-9-5", "style": "Beret", "color": "#f4c542", "styleIndex": 9, "colorIndex": 5}'::jsonb),
('hats','Beret / 7',135,'procedural:hats-9-6','procedural','{"key": "hats-9-6", "style": "Beret", "color": "#9b62d9", "styleIndex": 9, "colorIndex": 6}'::jsonb),
('hats','Beret / 8',140,'procedural:hats-9-7','procedural','{"key": "hats-9-7", "style": "Beret", "color": "#ef88c0", "styleIndex": 9, "colorIndex": 7}'::jsonb),
('hats','Beret / 9',125,'procedural:hats-9-8','procedural','{"key": "hats-9-8", "style": "Beret", "color": "#ed8838", "styleIndex": 9, "colorIndex": 8}'::jsonb),
('hats','Beret / 10',130,'procedural:hats-9-9','procedural','{"key": "hats-9-9", "style": "Beret", "color": "#6b4b35", "styleIndex": 9, "colorIndex": 9}'::jsonb),
('hats','Beret / 11',135,'procedural:hats-9-10','procedural','{"key": "hats-9-10", "style": "Beret", "color": "#42d8d0", "styleIndex": 9, "colorIndex": 10}'::jsonb),
('hats','Beret / 12',140,'procedural:hats-9-11','procedural','{"key": "hats-9-11", "style": "Beret", "color": "#a5abb8", "styleIndex": 9, "colorIndex": 11}'::jsonb),
('hats','Crown / 1',45,'procedural:hats-10-0','procedural','{"key": "hats-10-0", "style": "Crown", "color": "#e6e6e6", "styleIndex": 10, "colorIndex": 0}'::jsonb),
('hats','Crown / 2',50,'procedural:hats-10-1','procedural','{"key": "hats-10-1", "style": "Crown", "color": "#181818", "styleIndex": 10, "colorIndex": 1}'::jsonb),
('hats','Crown / 3',55,'procedural:hats-10-2','procedural','{"key": "hats-10-2", "style": "Crown", "color": "#ed4545", "styleIndex": 10, "colorIndex": 2}'::jsonb),
('hats','Crown / 4',60,'procedural:hats-10-3','procedural','{"key": "hats-10-3", "style": "Crown", "color": "#3689ed", "styleIndex": 10, "colorIndex": 3}'::jsonb),
('hats','Crown / 5',45,'procedural:hats-10-4','procedural','{"key": "hats-10-4", "style": "Crown", "color": "#37bf83", "styleIndex": 10, "colorIndex": 4}'::jsonb),
('hats','Crown / 6',50,'procedural:hats-10-5','procedural','{"key": "hats-10-5", "style": "Crown", "color": "#f4c542", "styleIndex": 10, "colorIndex": 5}'::jsonb),
('hats','Crown / 7',55,'procedural:hats-10-6','procedural','{"key": "hats-10-6", "style": "Crown", "color": "#9b62d9", "styleIndex": 10, "colorIndex": 6}'::jsonb),
('hats','Crown / 8',60,'procedural:hats-10-7','procedural','{"key": "hats-10-7", "style": "Crown", "color": "#ef88c0", "styleIndex": 10, "colorIndex": 7}'::jsonb),
('hats','Crown / 9',45,'procedural:hats-10-8','procedural','{"key": "hats-10-8", "style": "Crown", "color": "#ed8838", "styleIndex": 10, "colorIndex": 8}'::jsonb),
('hats','Crown / 10',50,'procedural:hats-10-9','procedural','{"key": "hats-10-9", "style": "Crown", "color": "#6b4b35", "styleIndex": 10, "colorIndex": 9}'::jsonb),
('hats','Crown / 11',55,'procedural:hats-10-10','procedural','{"key": "hats-10-10", "style": "Crown", "color": "#42d8d0", "styleIndex": 10, "colorIndex": 10}'::jsonb),
('hats','Crown / 12',60,'procedural:hats-10-11','procedural','{"key": "hats-10-11", "style": "Crown", "color": "#a5abb8", "styleIndex": 10, "colorIndex": 11}'::jsonb),
('hats','Visor / 1',65,'procedural:hats-11-0','procedural','{"key": "hats-11-0", "style": "Visor", "color": "#e6e6e6", "styleIndex": 11, "colorIndex": 0}'::jsonb),
('hats','Visor / 2',70,'procedural:hats-11-1','procedural','{"key": "hats-11-1", "style": "Visor", "color": "#181818", "styleIndex": 11, "colorIndex": 1}'::jsonb),
('hats','Visor / 3',75,'procedural:hats-11-2','procedural','{"key": "hats-11-2", "style": "Visor", "color": "#ed4545", "styleIndex": 11, "colorIndex": 2}'::jsonb),
('hats','Visor / 4',80,'procedural:hats-11-3','procedural','{"key": "hats-11-3", "style": "Visor", "color": "#3689ed", "styleIndex": 11, "colorIndex": 3}'::jsonb),
('hats','Visor / 5',65,'procedural:hats-11-4','procedural','{"key": "hats-11-4", "style": "Visor", "color": "#37bf83", "styleIndex": 11, "colorIndex": 4}'::jsonb),
('hats','Visor / 6',70,'procedural:hats-11-5','procedural','{"key": "hats-11-5", "style": "Visor", "color": "#f4c542", "styleIndex": 11, "colorIndex": 5}'::jsonb),
('hats','Visor / 7',75,'procedural:hats-11-6','procedural','{"key": "hats-11-6", "style": "Visor", "color": "#9b62d9", "styleIndex": 11, "colorIndex": 6}'::jsonb),
('hats','Visor / 8',80,'procedural:hats-11-7','procedural','{"key": "hats-11-7", "style": "Visor", "color": "#ef88c0", "styleIndex": 11, "colorIndex": 7}'::jsonb),
('hats','Visor / 9',65,'procedural:hats-11-8','procedural','{"key": "hats-11-8", "style": "Visor", "color": "#ed8838", "styleIndex": 11, "colorIndex": 8}'::jsonb),
('hats','Visor / 10',70,'procedural:hats-11-9','procedural','{"key": "hats-11-9", "style": "Visor", "color": "#6b4b35", "styleIndex": 11, "colorIndex": 9}'::jsonb),
('hats','Visor / 11',75,'procedural:hats-11-10','procedural','{"key": "hats-11-10", "style": "Visor", "color": "#42d8d0", "styleIndex": 11, "colorIndex": 10}'::jsonb),
('hats','Visor / 12',80,'procedural:hats-11-11','procedural','{"key": "hats-11-11", "style": "Visor", "color": "#a5abb8", "styleIndex": 11, "colorIndex": 11}'::jsonb),
('hats','Helmet / 1',85,'procedural:hats-12-0','procedural','{"key": "hats-12-0", "style": "Helmet", "color": "#e6e6e6", "styleIndex": 12, "colorIndex": 0}'::jsonb),
('hats','Helmet / 2',90,'procedural:hats-12-1','procedural','{"key": "hats-12-1", "style": "Helmet", "color": "#181818", "styleIndex": 12, "colorIndex": 1}'::jsonb),
('hats','Helmet / 3',95,'procedural:hats-12-2','procedural','{"key": "hats-12-2", "style": "Helmet", "color": "#ed4545", "styleIndex": 12, "colorIndex": 2}'::jsonb),
('hats','Helmet / 4',100,'procedural:hats-12-3','procedural','{"key": "hats-12-3", "style": "Helmet", "color": "#3689ed", "styleIndex": 12, "colorIndex": 3}'::jsonb),
('hats','Helmet / 5',85,'procedural:hats-12-4','procedural','{"key": "hats-12-4", "style": "Helmet", "color": "#37bf83", "styleIndex": 12, "colorIndex": 4}'::jsonb),
('hats','Helmet / 6',90,'procedural:hats-12-5','procedural','{"key": "hats-12-5", "style": "Helmet", "color": "#f4c542", "styleIndex": 12, "colorIndex": 5}'::jsonb),
('hats','Helmet / 7',95,'procedural:hats-12-6','procedural','{"key": "hats-12-6", "style": "Helmet", "color": "#9b62d9", "styleIndex": 12, "colorIndex": 6}'::jsonb),
('hats','Helmet / 8',100,'procedural:hats-12-7','procedural','{"key": "hats-12-7", "style": "Helmet", "color": "#ef88c0", "styleIndex": 12, "colorIndex": 7}'::jsonb),
('hats','Helmet / 9',85,'procedural:hats-12-8','procedural','{"key": "hats-12-8", "style": "Helmet", "color": "#ed8838", "styleIndex": 12, "colorIndex": 8}'::jsonb),
('hats','Helmet / 10',90,'procedural:hats-12-9','procedural','{"key": "hats-12-9", "style": "Helmet", "color": "#6b4b35", "styleIndex": 12, "colorIndex": 9}'::jsonb),
('hats','Helmet / 11',95,'procedural:hats-12-10','procedural','{"key": "hats-12-10", "style": "Helmet", "color": "#42d8d0", "styleIndex": 12, "colorIndex": 10}'::jsonb),
('hats','Helmet / 12',100,'procedural:hats-12-11','procedural','{"key": "hats-12-11", "style": "Helmet", "color": "#a5abb8", "styleIndex": 12, "colorIndex": 11}'::jsonb),
('heads','Sphere',45,'procedural:heads-0-0','procedural','{"key": "heads-0-0", "style": "Sphere", "color": "#e6e6e6", "styleIndex": 0, "colorIndex": 0}'::jsonb),
('heads','Cathead / 1',65,'procedural:heads-1-0','procedural','{"key": "heads-1-0", "style": "Cathead", "color": "#e6e6e6", "styleIndex": 1, "colorIndex": 0}'::jsonb),
('heads','Cathead / 2',70,'procedural:heads-1-1','procedural','{"key": "heads-1-1", "style": "Cathead", "color": "#181818", "styleIndex": 1, "colorIndex": 1}'::jsonb),
('heads','Cathead / 3',75,'procedural:heads-1-2','procedural','{"key": "heads-1-2", "style": "Cathead", "color": "#ed4545", "styleIndex": 1, "colorIndex": 2}'::jsonb),
('heads','Cathead / 4',80,'procedural:heads-1-3','procedural','{"key": "heads-1-3", "style": "Cathead", "color": "#3689ed", "styleIndex": 1, "colorIndex": 3}'::jsonb),
('heads','Cathead / 5',65,'procedural:heads-1-4','procedural','{"key": "heads-1-4", "style": "Cathead", "color": "#37bf83", "styleIndex": 1, "colorIndex": 4}'::jsonb),
('heads','Cathead / 6',70,'procedural:heads-1-5','procedural','{"key": "heads-1-5", "style": "Cathead", "color": "#f4c542", "styleIndex": 1, "colorIndex": 5}'::jsonb),
('heads','Cathead / 7',75,'procedural:heads-1-6','procedural','{"key": "heads-1-6", "style": "Cathead", "color": "#9b62d9", "styleIndex": 1, "colorIndex": 6}'::jsonb),
('heads','Cathead / 8',80,'procedural:heads-1-7','procedural','{"key": "heads-1-7", "style": "Cathead", "color": "#ef88c0", "styleIndex": 1, "colorIndex": 7}'::jsonb),
('heads','Cathead / 9',65,'procedural:heads-1-8','procedural','{"key": "heads-1-8", "style": "Cathead", "color": "#ed8838", "styleIndex": 1, "colorIndex": 8}'::jsonb),
('heads','Cathead / 10',70,'procedural:heads-1-9','procedural','{"key": "heads-1-9", "style": "Cathead", "color": "#6b4b35", "styleIndex": 1, "colorIndex": 9}'::jsonb),
('heads','Cathead / 11',75,'procedural:heads-1-10','procedural','{"key": "heads-1-10", "style": "Cathead", "color": "#42d8d0", "styleIndex": 1, "colorIndex": 10}'::jsonb),
('heads','Cathead / 12',80,'procedural:heads-1-11','procedural','{"key": "heads-1-11", "style": "Cathead", "color": "#a5abb8", "styleIndex": 1, "colorIndex": 11}'::jsonb),
('heads','Blocky / 1',85,'procedural:heads-2-0','procedural','{"key": "heads-2-0", "style": "Blocky", "color": "#e6e6e6", "styleIndex": 2, "colorIndex": 0}'::jsonb),
('heads','Blocky / 2',90,'procedural:heads-2-1','procedural','{"key": "heads-2-1", "style": "Blocky", "color": "#181818", "styleIndex": 2, "colorIndex": 1}'::jsonb),
('heads','Blocky / 3',95,'procedural:heads-2-2','procedural','{"key": "heads-2-2", "style": "Blocky", "color": "#ed4545", "styleIndex": 2, "colorIndex": 2}'::jsonb),
('heads','Blocky / 4',100,'procedural:heads-2-3','procedural','{"key": "heads-2-3", "style": "Blocky", "color": "#3689ed", "styleIndex": 2, "colorIndex": 3}'::jsonb),
('heads','Blocky / 5',85,'procedural:heads-2-4','procedural','{"key": "heads-2-4", "style": "Blocky", "color": "#37bf83", "styleIndex": 2, "colorIndex": 4}'::jsonb),
('heads','Blocky / 6',90,'procedural:heads-2-5','procedural','{"key": "heads-2-5", "style": "Blocky", "color": "#f4c542", "styleIndex": 2, "colorIndex": 5}'::jsonb),
('heads','Blocky / 7',95,'procedural:heads-2-6','procedural','{"key": "heads-2-6", "style": "Blocky", "color": "#9b62d9", "styleIndex": 2, "colorIndex": 6}'::jsonb),
('heads','Blocky / 8',100,'procedural:heads-2-7','procedural','{"key": "heads-2-7", "style": "Blocky", "color": "#ef88c0", "styleIndex": 2, "colorIndex": 7}'::jsonb),
('heads','Blocky / 9',85,'procedural:heads-2-8','procedural','{"key": "heads-2-8", "style": "Blocky", "color": "#ed8838", "styleIndex": 2, "colorIndex": 8}'::jsonb),
('heads','Blocky / 10',90,'procedural:heads-2-9','procedural','{"key": "heads-2-9", "style": "Blocky", "color": "#6b4b35", "styleIndex": 2, "colorIndex": 9}'::jsonb),
('heads','Blocky / 11',95,'procedural:heads-2-10','procedural','{"key": "heads-2-10", "style": "Blocky", "color": "#42d8d0", "styleIndex": 2, "colorIndex": 10}'::jsonb),
('heads','Blocky / 12',100,'procedural:heads-2-11','procedural','{"key": "heads-2-11", "style": "Blocky", "color": "#a5abb8", "styleIndex": 2, "colorIndex": 11}'::jsonb),
('heads','Alien / 1',105,'procedural:heads-3-0','procedural','{"key": "heads-3-0", "style": "Alien", "color": "#e6e6e6", "styleIndex": 3, "colorIndex": 0}'::jsonb),
('heads','Alien / 2',110,'procedural:heads-3-1','procedural','{"key": "heads-3-1", "style": "Alien", "color": "#181818", "styleIndex": 3, "colorIndex": 1}'::jsonb),
('heads','Alien / 3',115,'procedural:heads-3-2','procedural','{"key": "heads-3-2", "style": "Alien", "color": "#ed4545", "styleIndex": 3, "colorIndex": 2}'::jsonb),
('heads','Alien / 4',120,'procedural:heads-3-3','procedural','{"key": "heads-3-3", "style": "Alien", "color": "#3689ed", "styleIndex": 3, "colorIndex": 3}'::jsonb),
('heads','Alien / 5',105,'procedural:heads-3-4','procedural','{"key": "heads-3-4", "style": "Alien", "color": "#37bf83", "styleIndex": 3, "colorIndex": 4}'::jsonb),
('heads','Alien / 6',110,'procedural:heads-3-5','procedural','{"key": "heads-3-5", "style": "Alien", "color": "#f4c542", "styleIndex": 3, "colorIndex": 5}'::jsonb),
('heads','Alien / 7',115,'procedural:heads-3-6','procedural','{"key": "heads-3-6", "style": "Alien", "color": "#9b62d9", "styleIndex": 3, "colorIndex": 6}'::jsonb),
('heads','Alien / 8',120,'procedural:heads-3-7','procedural','{"key": "heads-3-7", "style": "Alien", "color": "#ef88c0", "styleIndex": 3, "colorIndex": 7}'::jsonb),
('heads','Alien / 9',105,'procedural:heads-3-8','procedural','{"key": "heads-3-8", "style": "Alien", "color": "#ed8838", "styleIndex": 3, "colorIndex": 8}'::jsonb) ON CONFLICT (asset_url) WHERE asset_kind='procedural' DO NOTHING;
INSERT INTO store_items(category,name,price,asset_url,asset_kind,metadata) VALUES
('heads','Alien / 10',110,'procedural:heads-3-9','procedural','{"key": "heads-3-9", "style": "Alien", "color": "#6b4b35", "styleIndex": 3, "colorIndex": 9}'::jsonb),
('heads','Alien / 11',115,'procedural:heads-3-10','procedural','{"key": "heads-3-10", "style": "Alien", "color": "#42d8d0", "styleIndex": 3, "colorIndex": 10}'::jsonb),
('heads','Alien / 12',120,'procedural:heads-3-11','procedural','{"key": "heads-3-11", "style": "Alien", "color": "#a5abb8", "styleIndex": 3, "colorIndex": 11}'::jsonb),
('heads','Diamond / 1',125,'procedural:heads-4-0','procedural','{"key": "heads-4-0", "style": "Diamond", "color": "#e6e6e6", "styleIndex": 4, "colorIndex": 0}'::jsonb),
('heads','Diamond / 2',130,'procedural:heads-4-1','procedural','{"key": "heads-4-1", "style": "Diamond", "color": "#181818", "styleIndex": 4, "colorIndex": 1}'::jsonb),
('heads','Diamond / 3',135,'procedural:heads-4-2','procedural','{"key": "heads-4-2", "style": "Diamond", "color": "#ed4545", "styleIndex": 4, "colorIndex": 2}'::jsonb),
('heads','Diamond / 4',140,'procedural:heads-4-3','procedural','{"key": "heads-4-3", "style": "Diamond", "color": "#3689ed", "styleIndex": 4, "colorIndex": 3}'::jsonb),
('heads','Diamond / 5',125,'procedural:heads-4-4','procedural','{"key": "heads-4-4", "style": "Diamond", "color": "#37bf83", "styleIndex": 4, "colorIndex": 4}'::jsonb),
('heads','Diamond / 6',130,'procedural:heads-4-5','procedural','{"key": "heads-4-5", "style": "Diamond", "color": "#f4c542", "styleIndex": 4, "colorIndex": 5}'::jsonb),
('heads','Diamond / 7',135,'procedural:heads-4-6','procedural','{"key": "heads-4-6", "style": "Diamond", "color": "#9b62d9", "styleIndex": 4, "colorIndex": 6}'::jsonb),
('heads','Diamond / 8',140,'procedural:heads-4-7','procedural','{"key": "heads-4-7", "style": "Diamond", "color": "#ef88c0", "styleIndex": 4, "colorIndex": 7}'::jsonb),
('heads','Diamond / 9',125,'procedural:heads-4-8','procedural','{"key": "heads-4-8", "style": "Diamond", "color": "#ed8838", "styleIndex": 4, "colorIndex": 8}'::jsonb),
('heads','Diamond / 10',130,'procedural:heads-4-9','procedural','{"key": "heads-4-9", "style": "Diamond", "color": "#6b4b35", "styleIndex": 4, "colorIndex": 9}'::jsonb),
('heads','Diamond / 11',135,'procedural:heads-4-10','procedural','{"key": "heads-4-10", "style": "Diamond", "color": "#42d8d0", "styleIndex": 4, "colorIndex": 10}'::jsonb),
('heads','Diamond / 12',140,'procedural:heads-4-11','procedural','{"key": "heads-4-11", "style": "Diamond", "color": "#a5abb8", "styleIndex": 4, "colorIndex": 11}'::jsonb),
('heads','Heart / 1',45,'procedural:heads-5-0','procedural','{"key": "heads-5-0", "style": "Heart", "color": "#e6e6e6", "styleIndex": 5, "colorIndex": 0}'::jsonb),
('heads','Heart / 2',50,'procedural:heads-5-1','procedural','{"key": "heads-5-1", "style": "Heart", "color": "#181818", "styleIndex": 5, "colorIndex": 1}'::jsonb),
('heads','Heart / 3',55,'procedural:heads-5-2','procedural','{"key": "heads-5-2", "style": "Heart", "color": "#ed4545", "styleIndex": 5, "colorIndex": 2}'::jsonb),
('heads','Heart / 4',60,'procedural:heads-5-3','procedural','{"key": "heads-5-3", "style": "Heart", "color": "#3689ed", "styleIndex": 5, "colorIndex": 3}'::jsonb),
('heads','Heart / 5',45,'procedural:heads-5-4','procedural','{"key": "heads-5-4", "style": "Heart", "color": "#37bf83", "styleIndex": 5, "colorIndex": 4}'::jsonb),
('heads','Heart / 6',50,'procedural:heads-5-5','procedural','{"key": "heads-5-5", "style": "Heart", "color": "#f4c542", "styleIndex": 5, "colorIndex": 5}'::jsonb),
('heads','Heart / 7',55,'procedural:heads-5-6','procedural','{"key": "heads-5-6", "style": "Heart", "color": "#9b62d9", "styleIndex": 5, "colorIndex": 6}'::jsonb),
('heads','Heart / 8',60,'procedural:heads-5-7','procedural','{"key": "heads-5-7", "style": "Heart", "color": "#ef88c0", "styleIndex": 5, "colorIndex": 7}'::jsonb),
('heads','Heart / 9',45,'procedural:heads-5-8','procedural','{"key": "heads-5-8", "style": "Heart", "color": "#ed8838", "styleIndex": 5, "colorIndex": 8}'::jsonb),
('heads','Heart / 10',50,'procedural:heads-5-9','procedural','{"key": "heads-5-9", "style": "Heart", "color": "#6b4b35", "styleIndex": 5, "colorIndex": 9}'::jsonb),
('heads','Heart / 11',55,'procedural:heads-5-10','procedural','{"key": "heads-5-10", "style": "Heart", "color": "#42d8d0", "styleIndex": 5, "colorIndex": 10}'::jsonb),
('heads','Heart / 12',60,'procedural:heads-5-11','procedural','{"key": "heads-5-11", "style": "Heart", "color": "#a5abb8", "styleIndex": 5, "colorIndex": 11}'::jsonb),
('heads','Oval / 1',65,'procedural:heads-6-0','procedural','{"key": "heads-6-0", "style": "Oval", "color": "#e6e6e6", "styleIndex": 6, "colorIndex": 0}'::jsonb),
('heads','Oval / 2',70,'procedural:heads-6-1','procedural','{"key": "heads-6-1", "style": "Oval", "color": "#181818", "styleIndex": 6, "colorIndex": 1}'::jsonb),
('heads','Oval / 3',75,'procedural:heads-6-2','procedural','{"key": "heads-6-2", "style": "Oval", "color": "#ed4545", "styleIndex": 6, "colorIndex": 2}'::jsonb),
('heads','Oval / 4',80,'procedural:heads-6-3','procedural','{"key": "heads-6-3", "style": "Oval", "color": "#3689ed", "styleIndex": 6, "colorIndex": 3}'::jsonb),
('heads','Oval / 5',65,'procedural:heads-6-4','procedural','{"key": "heads-6-4", "style": "Oval", "color": "#37bf83", "styleIndex": 6, "colorIndex": 4}'::jsonb),
('heads','Oval / 6',70,'procedural:heads-6-5','procedural','{"key": "heads-6-5", "style": "Oval", "color": "#f4c542", "styleIndex": 6, "colorIndex": 5}'::jsonb),
('heads','Oval / 7',75,'procedural:heads-6-6','procedural','{"key": "heads-6-6", "style": "Oval", "color": "#9b62d9", "styleIndex": 6, "colorIndex": 6}'::jsonb),
('heads','Oval / 8',80,'procedural:heads-6-7','procedural','{"key": "heads-6-7", "style": "Oval", "color": "#ef88c0", "styleIndex": 6, "colorIndex": 7}'::jsonb),
('heads','Oval / 9',65,'procedural:heads-6-8','procedural','{"key": "heads-6-8", "style": "Oval", "color": "#ed8838", "styleIndex": 6, "colorIndex": 8}'::jsonb),
('heads','Oval / 10',70,'procedural:heads-6-9','procedural','{"key": "heads-6-9", "style": "Oval", "color": "#6b4b35", "styleIndex": 6, "colorIndex": 9}'::jsonb),
('heads','Oval / 11',75,'procedural:heads-6-10','procedural','{"key": "heads-6-10", "style": "Oval", "color": "#42d8d0", "styleIndex": 6, "colorIndex": 10}'::jsonb),
('heads','Oval / 12',80,'procedural:heads-6-11','procedural','{"key": "heads-6-11", "style": "Oval", "color": "#a5abb8", "styleIndex": 6, "colorIndex": 11}'::jsonb),
('heads','Humanoid / 1',85,'procedural:heads-7-0','procedural','{"key": "heads-7-0", "style": "Humanoid", "color": "#e6e6e6", "styleIndex": 7, "colorIndex": 0}'::jsonb),
('heads','Humanoid / 2',90,'procedural:heads-7-1','procedural','{"key": "heads-7-1", "style": "Humanoid", "color": "#181818", "styleIndex": 7, "colorIndex": 1}'::jsonb),
('heads','Humanoid / 3',95,'procedural:heads-7-2','procedural','{"key": "heads-7-2", "style": "Humanoid", "color": "#ed4545", "styleIndex": 7, "colorIndex": 2}'::jsonb),
('heads','Humanoid / 4',100,'procedural:heads-7-3','procedural','{"key": "heads-7-3", "style": "Humanoid", "color": "#3689ed", "styleIndex": 7, "colorIndex": 3}'::jsonb),
('heads','Humanoid / 5',85,'procedural:heads-7-4','procedural','{"key": "heads-7-4", "style": "Humanoid", "color": "#37bf83", "styleIndex": 7, "colorIndex": 4}'::jsonb),
('heads','Humanoid / 6',90,'procedural:heads-7-5','procedural','{"key": "heads-7-5", "style": "Humanoid", "color": "#f4c542", "styleIndex": 7, "colorIndex": 5}'::jsonb),
('heads','Humanoid / 7',95,'procedural:heads-7-6','procedural','{"key": "heads-7-6", "style": "Humanoid", "color": "#9b62d9", "styleIndex": 7, "colorIndex": 6}'::jsonb),
('heads','Humanoid / 8',100,'procedural:heads-7-7','procedural','{"key": "heads-7-7", "style": "Humanoid", "color": "#ef88c0", "styleIndex": 7, "colorIndex": 7}'::jsonb),
('heads','Humanoid / 9',85,'procedural:heads-7-8','procedural','{"key": "heads-7-8", "style": "Humanoid", "color": "#ed8838", "styleIndex": 7, "colorIndex": 8}'::jsonb),
('heads','Humanoid / 10',90,'procedural:heads-7-9','procedural','{"key": "heads-7-9", "style": "Humanoid", "color": "#6b4b35", "styleIndex": 7, "colorIndex": 9}'::jsonb),
('heads','Humanoid / 11',95,'procedural:heads-7-10','procedural','{"key": "heads-7-10", "style": "Humanoid", "color": "#42d8d0", "styleIndex": 7, "colorIndex": 10}'::jsonb),
('heads','Humanoid / 12',100,'procedural:heads-7-11','procedural','{"key": "heads-7-11", "style": "Humanoid", "color": "#a5abb8", "styleIndex": 7, "colorIndex": 11}'::jsonb),
('heads','Robot / 1',105,'procedural:heads-8-0','procedural','{"key": "heads-8-0", "style": "Robot", "color": "#e6e6e6", "styleIndex": 8, "colorIndex": 0}'::jsonb),
('heads','Robot / 2',110,'procedural:heads-8-1','procedural','{"key": "heads-8-1", "style": "Robot", "color": "#181818", "styleIndex": 8, "colorIndex": 1}'::jsonb),
('heads','Robot / 3',115,'procedural:heads-8-2','procedural','{"key": "heads-8-2", "style": "Robot", "color": "#ed4545", "styleIndex": 8, "colorIndex": 2}'::jsonb),
('heads','Robot / 4',120,'procedural:heads-8-3','procedural','{"key": "heads-8-3", "style": "Robot", "color": "#3689ed", "styleIndex": 8, "colorIndex": 3}'::jsonb),
('heads','Robot / 5',105,'procedural:heads-8-4','procedural','{"key": "heads-8-4", "style": "Robot", "color": "#37bf83", "styleIndex": 8, "colorIndex": 4}'::jsonb),
('heads','Robot / 6',110,'procedural:heads-8-5','procedural','{"key": "heads-8-5", "style": "Robot", "color": "#f4c542", "styleIndex": 8, "colorIndex": 5}'::jsonb),
('heads','Robot / 7',115,'procedural:heads-8-6','procedural','{"key": "heads-8-6", "style": "Robot", "color": "#9b62d9", "styleIndex": 8, "colorIndex": 6}'::jsonb),
('heads','Robot / 8',120,'procedural:heads-8-7','procedural','{"key": "heads-8-7", "style": "Robot", "color": "#ef88c0", "styleIndex": 8, "colorIndex": 7}'::jsonb),
('heads','Robot / 9',105,'procedural:heads-8-8','procedural','{"key": "heads-8-8", "style": "Robot", "color": "#ed8838", "styleIndex": 8, "colorIndex": 8}'::jsonb),
('heads','Robot / 10',110,'procedural:heads-8-9','procedural','{"key": "heads-8-9", "style": "Robot", "color": "#6b4b35", "styleIndex": 8, "colorIndex": 9}'::jsonb),
('heads','Robot / 11',115,'procedural:heads-8-10','procedural','{"key": "heads-8-10", "style": "Robot", "color": "#42d8d0", "styleIndex": 8, "colorIndex": 10}'::jsonb),
('heads','Robot / 12',120,'procedural:heads-8-11','procedural','{"key": "heads-8-11", "style": "Robot", "color": "#a5abb8", "styleIndex": 8, "colorIndex": 11}'::jsonb),
('heads','Pumpkin / 1',125,'procedural:heads-9-0','procedural','{"key": "heads-9-0", "style": "Pumpkin", "color": "#e6e6e6", "styleIndex": 9, "colorIndex": 0}'::jsonb),
('heads','Pumpkin / 2',130,'procedural:heads-9-1','procedural','{"key": "heads-9-1", "style": "Pumpkin", "color": "#181818", "styleIndex": 9, "colorIndex": 1}'::jsonb),
('heads','Pumpkin / 3',135,'procedural:heads-9-2','procedural','{"key": "heads-9-2", "style": "Pumpkin", "color": "#ed4545", "styleIndex": 9, "colorIndex": 2}'::jsonb),
('heads','Pumpkin / 4',140,'procedural:heads-9-3','procedural','{"key": "heads-9-3", "style": "Pumpkin", "color": "#3689ed", "styleIndex": 9, "colorIndex": 3}'::jsonb),
('heads','Pumpkin / 5',125,'procedural:heads-9-4','procedural','{"key": "heads-9-4", "style": "Pumpkin", "color": "#37bf83", "styleIndex": 9, "colorIndex": 4}'::jsonb),
('heads','Pumpkin / 6',130,'procedural:heads-9-5','procedural','{"key": "heads-9-5", "style": "Pumpkin", "color": "#f4c542", "styleIndex": 9, "colorIndex": 5}'::jsonb),
('heads','Pumpkin / 7',135,'procedural:heads-9-6','procedural','{"key": "heads-9-6", "style": "Pumpkin", "color": "#9b62d9", "styleIndex": 9, "colorIndex": 6}'::jsonb),
('heads','Pumpkin / 8',140,'procedural:heads-9-7','procedural','{"key": "heads-9-7", "style": "Pumpkin", "color": "#ef88c0", "styleIndex": 9, "colorIndex": 7}'::jsonb),
('heads','Pumpkin / 9',125,'procedural:heads-9-8','procedural','{"key": "heads-9-8", "style": "Pumpkin", "color": "#ed8838", "styleIndex": 9, "colorIndex": 8}'::jsonb),
('heads','Pumpkin / 10',130,'procedural:heads-9-9','procedural','{"key": "heads-9-9", "style": "Pumpkin", "color": "#6b4b35", "styleIndex": 9, "colorIndex": 9}'::jsonb),
('heads','Pumpkin / 11',135,'procedural:heads-9-10','procedural','{"key": "heads-9-10", "style": "Pumpkin", "color": "#42d8d0", "styleIndex": 9, "colorIndex": 10}'::jsonb),
('heads','Pumpkin / 12',140,'procedural:heads-9-11','procedural','{"key": "heads-9-11", "style": "Pumpkin", "color": "#a5abb8", "styleIndex": 9, "colorIndex": 11}'::jsonb),
('eyes','Classic / 1',45,'procedural:eyes-0-0','procedural','{"key": "eyes-0-0", "style": "Classic", "color": "#e6e6e6", "styleIndex": 0, "colorIndex": 0}'::jsonb),
('eyes','Classic / 2',50,'procedural:eyes-0-1','procedural','{"key": "eyes-0-1", "style": "Classic", "color": "#181818", "styleIndex": 0, "colorIndex": 1}'::jsonb),
('eyes','Classic / 3',55,'procedural:eyes-0-2','procedural','{"key": "eyes-0-2", "style": "Classic", "color": "#ed4545", "styleIndex": 0, "colorIndex": 2}'::jsonb),
('eyes','Classic / 4',60,'procedural:eyes-0-3','procedural','{"key": "eyes-0-3", "style": "Classic", "color": "#3689ed", "styleIndex": 0, "colorIndex": 3}'::jsonb),
('eyes','Classic / 5',45,'procedural:eyes-0-4','procedural','{"key": "eyes-0-4", "style": "Classic", "color": "#37bf83", "styleIndex": 0, "colorIndex": 4}'::jsonb),
('eyes','Classic / 6',50,'procedural:eyes-0-5','procedural','{"key": "eyes-0-5", "style": "Classic", "color": "#f4c542", "styleIndex": 0, "colorIndex": 5}'::jsonb),
('eyes','Classic / 7',55,'procedural:eyes-0-6','procedural','{"key": "eyes-0-6", "style": "Classic", "color": "#9b62d9", "styleIndex": 0, "colorIndex": 6}'::jsonb),
('eyes','Classic / 8',60,'procedural:eyes-0-7','procedural','{"key": "eyes-0-7", "style": "Classic", "color": "#ef88c0", "styleIndex": 0, "colorIndex": 7}'::jsonb),
('eyes','Classic / 9',45,'procedural:eyes-0-8','procedural','{"key": "eyes-0-8", "style": "Classic", "color": "#ed8838", "styleIndex": 0, "colorIndex": 8}'::jsonb),
('eyes','Classic / 10',50,'procedural:eyes-0-9','procedural','{"key": "eyes-0-9", "style": "Classic", "color": "#6b4b35", "styleIndex": 0, "colorIndex": 9}'::jsonb),
('eyes','Classic / 11',55,'procedural:eyes-0-10','procedural','{"key": "eyes-0-10", "style": "Classic", "color": "#42d8d0", "styleIndex": 0, "colorIndex": 10}'::jsonb),
('eyes','Classic / 12',60,'procedural:eyes-0-11','procedural','{"key": "eyes-0-11", "style": "Classic", "color": "#a5abb8", "styleIndex": 0, "colorIndex": 11}'::jsonb),
('eyes','Big Sparkle / 1',65,'procedural:eyes-1-0','procedural','{"key": "eyes-1-0", "style": "Big Sparkle", "color": "#e6e6e6", "styleIndex": 1, "colorIndex": 0}'::jsonb),
('eyes','Big Sparkle / 2',70,'procedural:eyes-1-1','procedural','{"key": "eyes-1-1", "style": "Big Sparkle", "color": "#181818", "styleIndex": 1, "colorIndex": 1}'::jsonb),
('eyes','Big Sparkle / 3',75,'procedural:eyes-1-2','procedural','{"key": "eyes-1-2", "style": "Big Sparkle", "color": "#ed4545", "styleIndex": 1, "colorIndex": 2}'::jsonb),
('eyes','Big Sparkle / 4',80,'procedural:eyes-1-3','procedural','{"key": "eyes-1-3", "style": "Big Sparkle", "color": "#3689ed", "styleIndex": 1, "colorIndex": 3}'::jsonb),
('eyes','Big Sparkle / 5',65,'procedural:eyes-1-4','procedural','{"key": "eyes-1-4", "style": "Big Sparkle", "color": "#37bf83", "styleIndex": 1, "colorIndex": 4}'::jsonb),
('eyes','Big Sparkle / 6',70,'procedural:eyes-1-5','procedural','{"key": "eyes-1-5", "style": "Big Sparkle", "color": "#f4c542", "styleIndex": 1, "colorIndex": 5}'::jsonb),
('eyes','Big Sparkle / 7',75,'procedural:eyes-1-6','procedural','{"key": "eyes-1-6", "style": "Big Sparkle", "color": "#9b62d9", "styleIndex": 1, "colorIndex": 6}'::jsonb),
('eyes','Big Sparkle / 8',80,'procedural:eyes-1-7','procedural','{"key": "eyes-1-7", "style": "Big Sparkle", "color": "#ef88c0", "styleIndex": 1, "colorIndex": 7}'::jsonb),
('eyes','Big Sparkle / 9',65,'procedural:eyes-1-8','procedural','{"key": "eyes-1-8", "style": "Big Sparkle", "color": "#ed8838", "styleIndex": 1, "colorIndex": 8}'::jsonb),
('eyes','Big Sparkle / 10',70,'procedural:eyes-1-9','procedural','{"key": "eyes-1-9", "style": "Big Sparkle", "color": "#6b4b35", "styleIndex": 1, "colorIndex": 9}'::jsonb),
('eyes','Big Sparkle / 11',75,'procedural:eyes-1-10','procedural','{"key": "eyes-1-10", "style": "Big Sparkle", "color": "#42d8d0", "styleIndex": 1, "colorIndex": 10}'::jsonb),
('eyes','Big Sparkle / 12',80,'procedural:eyes-1-11','procedural','{"key": "eyes-1-11", "style": "Big Sparkle", "color": "#a5abb8", "styleIndex": 1, "colorIndex": 11}'::jsonb),
('eyes','Sleepy / 1',85,'procedural:eyes-2-0','procedural','{"key": "eyes-2-0", "style": "Sleepy", "color": "#e6e6e6", "styleIndex": 2, "colorIndex": 0}'::jsonb),
('eyes','Sleepy / 2',90,'procedural:eyes-2-1','procedural','{"key": "eyes-2-1", "style": "Sleepy", "color": "#181818", "styleIndex": 2, "colorIndex": 1}'::jsonb),
('eyes','Sleepy / 3',95,'procedural:eyes-2-2','procedural','{"key": "eyes-2-2", "style": "Sleepy", "color": "#ed4545", "styleIndex": 2, "colorIndex": 2}'::jsonb),
('eyes','Sleepy / 4',100,'procedural:eyes-2-3','procedural','{"key": "eyes-2-3", "style": "Sleepy", "color": "#3689ed", "styleIndex": 2, "colorIndex": 3}'::jsonb),
('eyes','Sleepy / 5',85,'procedural:eyes-2-4','procedural','{"key": "eyes-2-4", "style": "Sleepy", "color": "#37bf83", "styleIndex": 2, "colorIndex": 4}'::jsonb),
('eyes','Sleepy / 6',90,'procedural:eyes-2-5','procedural','{"key": "eyes-2-5", "style": "Sleepy", "color": "#f4c542", "styleIndex": 2, "colorIndex": 5}'::jsonb),
('eyes','Sleepy / 7',95,'procedural:eyes-2-6','procedural','{"key": "eyes-2-6", "style": "Sleepy", "color": "#9b62d9", "styleIndex": 2, "colorIndex": 6}'::jsonb),
('eyes','Sleepy / 8',100,'procedural:eyes-2-7','procedural','{"key": "eyes-2-7", "style": "Sleepy", "color": "#ef88c0", "styleIndex": 2, "colorIndex": 7}'::jsonb),
('eyes','Sleepy / 9',85,'procedural:eyes-2-8','procedural','{"key": "eyes-2-8", "style": "Sleepy", "color": "#ed8838", "styleIndex": 2, "colorIndex": 8}'::jsonb),
('eyes','Sleepy / 10',90,'procedural:eyes-2-9','procedural','{"key": "eyes-2-9", "style": "Sleepy", "color": "#6b4b35", "styleIndex": 2, "colorIndex": 9}'::jsonb),
('eyes','Sleepy / 11',95,'procedural:eyes-2-10','procedural','{"key": "eyes-2-10", "style": "Sleepy", "color": "#42d8d0", "styleIndex": 2, "colorIndex": 10}'::jsonb),
('eyes','Sleepy / 12',100,'procedural:eyes-2-11','procedural','{"key": "eyes-2-11", "style": "Sleepy", "color": "#a5abb8", "styleIndex": 2, "colorIndex": 11}'::jsonb),
('eyes','Happy / 1',105,'procedural:eyes-3-0','procedural','{"key": "eyes-3-0", "style": "Happy", "color": "#e6e6e6", "styleIndex": 3, "colorIndex": 0}'::jsonb),
('eyes','Happy / 2',110,'procedural:eyes-3-1','procedural','{"key": "eyes-3-1", "style": "Happy", "color": "#181818", "styleIndex": 3, "colorIndex": 1}'::jsonb),
('eyes','Happy / 3',115,'procedural:eyes-3-2','procedural','{"key": "eyes-3-2", "style": "Happy", "color": "#ed4545", "styleIndex": 3, "colorIndex": 2}'::jsonb),
('eyes','Happy / 4',120,'procedural:eyes-3-3','procedural','{"key": "eyes-3-3", "style": "Happy", "color": "#3689ed", "styleIndex": 3, "colorIndex": 3}'::jsonb),
('eyes','Happy / 5',105,'procedural:eyes-3-4','procedural','{"key": "eyes-3-4", "style": "Happy", "color": "#37bf83", "styleIndex": 3, "colorIndex": 4}'::jsonb),
('eyes','Happy / 6',110,'procedural:eyes-3-5','procedural','{"key": "eyes-3-5", "style": "Happy", "color": "#f4c542", "styleIndex": 3, "colorIndex": 5}'::jsonb),
('eyes','Happy / 7',115,'procedural:eyes-3-6','procedural','{"key": "eyes-3-6", "style": "Happy", "color": "#9b62d9", "styleIndex": 3, "colorIndex": 6}'::jsonb),
('eyes','Happy / 8',120,'procedural:eyes-3-7','procedural','{"key": "eyes-3-7", "style": "Happy", "color": "#ef88c0", "styleIndex": 3, "colorIndex": 7}'::jsonb),
('eyes','Happy / 9',105,'procedural:eyes-3-8','procedural','{"key": "eyes-3-8", "style": "Happy", "color": "#ed8838", "styleIndex": 3, "colorIndex": 8}'::jsonb) ON CONFLICT (asset_url) WHERE asset_kind='procedural' DO NOTHING;
INSERT INTO store_items(category,name,price,asset_url,asset_kind,metadata) VALUES
('eyes','Happy / 10',110,'procedural:eyes-3-9','procedural','{"key": "eyes-3-9", "style": "Happy", "color": "#6b4b35", "styleIndex": 3, "colorIndex": 9}'::jsonb),
('eyes','Happy / 11',115,'procedural:eyes-3-10','procedural','{"key": "eyes-3-10", "style": "Happy", "color": "#42d8d0", "styleIndex": 3, "colorIndex": 10}'::jsonb),
('eyes','Happy / 12',120,'procedural:eyes-3-11','procedural','{"key": "eyes-3-11", "style": "Happy", "color": "#a5abb8", "styleIndex": 3, "colorIndex": 11}'::jsonb),
('eyes','Wide / 1',125,'procedural:eyes-4-0','procedural','{"key": "eyes-4-0", "style": "Wide", "color": "#e6e6e6", "styleIndex": 4, "colorIndex": 0}'::jsonb),
('eyes','Wide / 2',130,'procedural:eyes-4-1','procedural','{"key": "eyes-4-1", "style": "Wide", "color": "#181818", "styleIndex": 4, "colorIndex": 1}'::jsonb),
('eyes','Wide / 3',135,'procedural:eyes-4-2','procedural','{"key": "eyes-4-2", "style": "Wide", "color": "#ed4545", "styleIndex": 4, "colorIndex": 2}'::jsonb),
('eyes','Wide / 4',140,'procedural:eyes-4-3','procedural','{"key": "eyes-4-3", "style": "Wide", "color": "#3689ed", "styleIndex": 4, "colorIndex": 3}'::jsonb),
('eyes','Wide / 5',125,'procedural:eyes-4-4','procedural','{"key": "eyes-4-4", "style": "Wide", "color": "#37bf83", "styleIndex": 4, "colorIndex": 4}'::jsonb),
('eyes','Wide / 6',130,'procedural:eyes-4-5','procedural','{"key": "eyes-4-5", "style": "Wide", "color": "#f4c542", "styleIndex": 4, "colorIndex": 5}'::jsonb),
('eyes','Wide / 7',135,'procedural:eyes-4-6','procedural','{"key": "eyes-4-6", "style": "Wide", "color": "#9b62d9", "styleIndex": 4, "colorIndex": 6}'::jsonb),
('eyes','Wide / 8',140,'procedural:eyes-4-7','procedural','{"key": "eyes-4-7", "style": "Wide", "color": "#ef88c0", "styleIndex": 4, "colorIndex": 7}'::jsonb),
('eyes','Wide / 9',125,'procedural:eyes-4-8','procedural','{"key": "eyes-4-8", "style": "Wide", "color": "#ed8838", "styleIndex": 4, "colorIndex": 8}'::jsonb),
('eyes','Wide / 10',130,'procedural:eyes-4-9','procedural','{"key": "eyes-4-9", "style": "Wide", "color": "#6b4b35", "styleIndex": 4, "colorIndex": 9}'::jsonb),
('eyes','Wide / 11',135,'procedural:eyes-4-10','procedural','{"key": "eyes-4-10", "style": "Wide", "color": "#42d8d0", "styleIndex": 4, "colorIndex": 10}'::jsonb),
('eyes','Wide / 12',140,'procedural:eyes-4-11','procedural','{"key": "eyes-4-11", "style": "Wide", "color": "#a5abb8", "styleIndex": 4, "colorIndex": 11}'::jsonb),
('eyes','Angry / 1',45,'procedural:eyes-5-0','procedural','{"key": "eyes-5-0", "style": "Angry", "color": "#e6e6e6", "styleIndex": 5, "colorIndex": 0}'::jsonb),
('eyes','Angry / 2',50,'procedural:eyes-5-1','procedural','{"key": "eyes-5-1", "style": "Angry", "color": "#181818", "styleIndex": 5, "colorIndex": 1}'::jsonb),
('eyes','Angry / 3',55,'procedural:eyes-5-2','procedural','{"key": "eyes-5-2", "style": "Angry", "color": "#ed4545", "styleIndex": 5, "colorIndex": 2}'::jsonb),
('eyes','Angry / 4',60,'procedural:eyes-5-3','procedural','{"key": "eyes-5-3", "style": "Angry", "color": "#3689ed", "styleIndex": 5, "colorIndex": 3}'::jsonb),
('eyes','Angry / 5',45,'procedural:eyes-5-4','procedural','{"key": "eyes-5-4", "style": "Angry", "color": "#37bf83", "styleIndex": 5, "colorIndex": 4}'::jsonb),
('eyes','Angry / 6',50,'procedural:eyes-5-5','procedural','{"key": "eyes-5-5", "style": "Angry", "color": "#f4c542", "styleIndex": 5, "colorIndex": 5}'::jsonb),
('eyes','Angry / 7',55,'procedural:eyes-5-6','procedural','{"key": "eyes-5-6", "style": "Angry", "color": "#9b62d9", "styleIndex": 5, "colorIndex": 6}'::jsonb),
('eyes','Angry / 8',60,'procedural:eyes-5-7','procedural','{"key": "eyes-5-7", "style": "Angry", "color": "#ef88c0", "styleIndex": 5, "colorIndex": 7}'::jsonb),
('eyes','Angry / 9',45,'procedural:eyes-5-8','procedural','{"key": "eyes-5-8", "style": "Angry", "color": "#ed8838", "styleIndex": 5, "colorIndex": 8}'::jsonb),
('eyes','Angry / 10',50,'procedural:eyes-5-9','procedural','{"key": "eyes-5-9", "style": "Angry", "color": "#6b4b35", "styleIndex": 5, "colorIndex": 9}'::jsonb),
('eyes','Angry / 11',55,'procedural:eyes-5-10','procedural','{"key": "eyes-5-10", "style": "Angry", "color": "#42d8d0", "styleIndex": 5, "colorIndex": 10}'::jsonb),
('eyes','Angry / 12',60,'procedural:eyes-5-11','procedural','{"key": "eyes-5-11", "style": "Angry", "color": "#a5abb8", "styleIndex": 5, "colorIndex": 11}'::jsonb),
('eyes','Round / 1',65,'procedural:eyes-6-0','procedural','{"key": "eyes-6-0", "style": "Round", "color": "#e6e6e6", "styleIndex": 6, "colorIndex": 0}'::jsonb),
('eyes','Round / 2',70,'procedural:eyes-6-1','procedural','{"key": "eyes-6-1", "style": "Round", "color": "#181818", "styleIndex": 6, "colorIndex": 1}'::jsonb),
('eyes','Round / 3',75,'procedural:eyes-6-2','procedural','{"key": "eyes-6-2", "style": "Round", "color": "#ed4545", "styleIndex": 6, "colorIndex": 2}'::jsonb),
('eyes','Round / 4',80,'procedural:eyes-6-3','procedural','{"key": "eyes-6-3", "style": "Round", "color": "#3689ed", "styleIndex": 6, "colorIndex": 3}'::jsonb),
('eyes','Round / 5',65,'procedural:eyes-6-4','procedural','{"key": "eyes-6-4", "style": "Round", "color": "#37bf83", "styleIndex": 6, "colorIndex": 4}'::jsonb),
('eyes','Round / 6',70,'procedural:eyes-6-5','procedural','{"key": "eyes-6-5", "style": "Round", "color": "#f4c542", "styleIndex": 6, "colorIndex": 5}'::jsonb),
('eyes','Round / 7',75,'procedural:eyes-6-6','procedural','{"key": "eyes-6-6", "style": "Round", "color": "#9b62d9", "styleIndex": 6, "colorIndex": 6}'::jsonb),
('eyes','Round / 8',80,'procedural:eyes-6-7','procedural','{"key": "eyes-6-7", "style": "Round", "color": "#ef88c0", "styleIndex": 6, "colorIndex": 7}'::jsonb),
('eyes','Round / 9',65,'procedural:eyes-6-8','procedural','{"key": "eyes-6-8", "style": "Round", "color": "#ed8838", "styleIndex": 6, "colorIndex": 8}'::jsonb),
('eyes','Round / 10',70,'procedural:eyes-6-9','procedural','{"key": "eyes-6-9", "style": "Round", "color": "#6b4b35", "styleIndex": 6, "colorIndex": 9}'::jsonb),
('eyes','Round / 11',75,'procedural:eyes-6-10','procedural','{"key": "eyes-6-10", "style": "Round", "color": "#42d8d0", "styleIndex": 6, "colorIndex": 10}'::jsonb),
('eyes','Round / 12',80,'procedural:eyes-6-11','procedural','{"key": "eyes-6-11", "style": "Round", "color": "#a5abb8", "styleIndex": 6, "colorIndex": 11}'::jsonb),
('eyes','Cat / 1',85,'procedural:eyes-7-0','procedural','{"key": "eyes-7-0", "style": "Cat", "color": "#e6e6e6", "styleIndex": 7, "colorIndex": 0}'::jsonb),
('eyes','Cat / 2',90,'procedural:eyes-7-1','procedural','{"key": "eyes-7-1", "style": "Cat", "color": "#181818", "styleIndex": 7, "colorIndex": 1}'::jsonb),
('eyes','Cat / 3',95,'procedural:eyes-7-2','procedural','{"key": "eyes-7-2", "style": "Cat", "color": "#ed4545", "styleIndex": 7, "colorIndex": 2}'::jsonb),
('eyes','Cat / 4',100,'procedural:eyes-7-3','procedural','{"key": "eyes-7-3", "style": "Cat", "color": "#3689ed", "styleIndex": 7, "colorIndex": 3}'::jsonb),
('eyes','Cat / 5',85,'procedural:eyes-7-4','procedural','{"key": "eyes-7-4", "style": "Cat", "color": "#37bf83", "styleIndex": 7, "colorIndex": 4}'::jsonb),
('eyes','Cat / 6',90,'procedural:eyes-7-5','procedural','{"key": "eyes-7-5", "style": "Cat", "color": "#f4c542", "styleIndex": 7, "colorIndex": 5}'::jsonb),
('eyes','Cat / 7',95,'procedural:eyes-7-6','procedural','{"key": "eyes-7-6", "style": "Cat", "color": "#9b62d9", "styleIndex": 7, "colorIndex": 6}'::jsonb),
('eyes','Cat / 8',100,'procedural:eyes-7-7','procedural','{"key": "eyes-7-7", "style": "Cat", "color": "#ef88c0", "styleIndex": 7, "colorIndex": 7}'::jsonb),
('eyes','Cat / 9',85,'procedural:eyes-7-8','procedural','{"key": "eyes-7-8", "style": "Cat", "color": "#ed8838", "styleIndex": 7, "colorIndex": 8}'::jsonb),
('eyes','Cat / 10',90,'procedural:eyes-7-9','procedural','{"key": "eyes-7-9", "style": "Cat", "color": "#6b4b35", "styleIndex": 7, "colorIndex": 9}'::jsonb),
('eyes','Cat / 11',95,'procedural:eyes-7-10','procedural','{"key": "eyes-7-10", "style": "Cat", "color": "#42d8d0", "styleIndex": 7, "colorIndex": 10}'::jsonb),
('eyes','Cat / 12',100,'procedural:eyes-7-11','procedural','{"key": "eyes-7-11", "style": "Cat", "color": "#a5abb8", "styleIndex": 7, "colorIndex": 11}'::jsonb),
('eyes','Robot / 1',105,'procedural:eyes-8-0','procedural','{"key": "eyes-8-0", "style": "Robot", "color": "#e6e6e6", "styleIndex": 8, "colorIndex": 0}'::jsonb),
('eyes','Robot / 2',110,'procedural:eyes-8-1','procedural','{"key": "eyes-8-1", "style": "Robot", "color": "#181818", "styleIndex": 8, "colorIndex": 1}'::jsonb),
('eyes','Robot / 3',115,'procedural:eyes-8-2','procedural','{"key": "eyes-8-2", "style": "Robot", "color": "#ed4545", "styleIndex": 8, "colorIndex": 2}'::jsonb),
('eyes','Robot / 4',120,'procedural:eyes-8-3','procedural','{"key": "eyes-8-3", "style": "Robot", "color": "#3689ed", "styleIndex": 8, "colorIndex": 3}'::jsonb),
('eyes','Robot / 5',105,'procedural:eyes-8-4','procedural','{"key": "eyes-8-4", "style": "Robot", "color": "#37bf83", "styleIndex": 8, "colorIndex": 4}'::jsonb),
('eyes','Robot / 6',110,'procedural:eyes-8-5','procedural','{"key": "eyes-8-5", "style": "Robot", "color": "#f4c542", "styleIndex": 8, "colorIndex": 5}'::jsonb),
('eyes','Robot / 7',115,'procedural:eyes-8-6','procedural','{"key": "eyes-8-6", "style": "Robot", "color": "#9b62d9", "styleIndex": 8, "colorIndex": 6}'::jsonb),
('eyes','Robot / 8',120,'procedural:eyes-8-7','procedural','{"key": "eyes-8-7", "style": "Robot", "color": "#ef88c0", "styleIndex": 8, "colorIndex": 7}'::jsonb),
('eyes','Robot / 9',105,'procedural:eyes-8-8','procedural','{"key": "eyes-8-8", "style": "Robot", "color": "#ed8838", "styleIndex": 8, "colorIndex": 8}'::jsonb),
('eyes','Robot / 10',110,'procedural:eyes-8-9','procedural','{"key": "eyes-8-9", "style": "Robot", "color": "#6b4b35", "styleIndex": 8, "colorIndex": 9}'::jsonb),
('eyes','Robot / 11',115,'procedural:eyes-8-10','procedural','{"key": "eyes-8-10", "style": "Robot", "color": "#42d8d0", "styleIndex": 8, "colorIndex": 10}'::jsonb),
('eyes','Robot / 12',120,'procedural:eyes-8-11','procedural','{"key": "eyes-8-11", "style": "Robot", "color": "#a5abb8", "styleIndex": 8, "colorIndex": 11}'::jsonb),
('eyes','Anime / 1',125,'procedural:eyes-9-0','procedural','{"key": "eyes-9-0", "style": "Anime", "color": "#e6e6e6", "styleIndex": 9, "colorIndex": 0}'::jsonb),
('eyes','Anime / 2',130,'procedural:eyes-9-1','procedural','{"key": "eyes-9-1", "style": "Anime", "color": "#181818", "styleIndex": 9, "colorIndex": 1}'::jsonb),
('eyes','Anime / 3',135,'procedural:eyes-9-2','procedural','{"key": "eyes-9-2", "style": "Anime", "color": "#ed4545", "styleIndex": 9, "colorIndex": 2}'::jsonb),
('eyes','Anime / 4',140,'procedural:eyes-9-3','procedural','{"key": "eyes-9-3", "style": "Anime", "color": "#3689ed", "styleIndex": 9, "colorIndex": 3}'::jsonb),
('eyes','Anime / 5',125,'procedural:eyes-9-4','procedural','{"key": "eyes-9-4", "style": "Anime", "color": "#37bf83", "styleIndex": 9, "colorIndex": 4}'::jsonb),
('eyes','Anime / 6',130,'procedural:eyes-9-5','procedural','{"key": "eyes-9-5", "style": "Anime", "color": "#f4c542", "styleIndex": 9, "colorIndex": 5}'::jsonb),
('eyes','Anime / 7',135,'procedural:eyes-9-6','procedural','{"key": "eyes-9-6", "style": "Anime", "color": "#9b62d9", "styleIndex": 9, "colorIndex": 6}'::jsonb),
('eyes','Anime / 8',140,'procedural:eyes-9-7','procedural','{"key": "eyes-9-7", "style": "Anime", "color": "#ef88c0", "styleIndex": 9, "colorIndex": 7}'::jsonb),
('eyes','Anime / 9',125,'procedural:eyes-9-8','procedural','{"key": "eyes-9-8", "style": "Anime", "color": "#ed8838", "styleIndex": 9, "colorIndex": 8}'::jsonb),
('eyes','Anime / 10',130,'procedural:eyes-9-9','procedural','{"key": "eyes-9-9", "style": "Anime", "color": "#6b4b35", "styleIndex": 9, "colorIndex": 9}'::jsonb),
('eyes','Anime / 11',135,'procedural:eyes-9-10','procedural','{"key": "eyes-9-10", "style": "Anime", "color": "#42d8d0", "styleIndex": 9, "colorIndex": 10}'::jsonb),
('eyes','Anime / 12',140,'procedural:eyes-9-11','procedural','{"key": "eyes-9-11", "style": "Anime", "color": "#a5abb8", "styleIndex": 9, "colorIndex": 11}'::jsonb),
('mouth','Smile / 1',45,'procedural:mouth-0-0','procedural','{"key": "mouth-0-0", "style": "Smile", "color": "#e6e6e6", "styleIndex": 0, "colorIndex": 0}'::jsonb),
('mouth','Smile / 2',50,'procedural:mouth-0-1','procedural','{"key": "mouth-0-1", "style": "Smile", "color": "#181818", "styleIndex": 0, "colorIndex": 1}'::jsonb),
('mouth','Smile / 3',55,'procedural:mouth-0-2','procedural','{"key": "mouth-0-2", "style": "Smile", "color": "#ed4545", "styleIndex": 0, "colorIndex": 2}'::jsonb),
('mouth','Smile / 4',60,'procedural:mouth-0-3','procedural','{"key": "mouth-0-3", "style": "Smile", "color": "#3689ed", "styleIndex": 0, "colorIndex": 3}'::jsonb),
('mouth','Smile / 5',45,'procedural:mouth-0-4','procedural','{"key": "mouth-0-4", "style": "Smile", "color": "#37bf83", "styleIndex": 0, "colorIndex": 4}'::jsonb),
('mouth','Smile / 6',50,'procedural:mouth-0-5','procedural','{"key": "mouth-0-5", "style": "Smile", "color": "#f4c542", "styleIndex": 0, "colorIndex": 5}'::jsonb),
('mouth','Smile / 7',55,'procedural:mouth-0-6','procedural','{"key": "mouth-0-6", "style": "Smile", "color": "#9b62d9", "styleIndex": 0, "colorIndex": 6}'::jsonb),
('mouth','Smile / 8',60,'procedural:mouth-0-7','procedural','{"key": "mouth-0-7", "style": "Smile", "color": "#ef88c0", "styleIndex": 0, "colorIndex": 7}'::jsonb),
('mouth','Smile / 9',45,'procedural:mouth-0-8','procedural','{"key": "mouth-0-8", "style": "Smile", "color": "#ed8838", "styleIndex": 0, "colorIndex": 8}'::jsonb),
('mouth','Smile / 10',50,'procedural:mouth-0-9','procedural','{"key": "mouth-0-9", "style": "Smile", "color": "#6b4b35", "styleIndex": 0, "colorIndex": 9}'::jsonb),
('mouth','Smile / 11',55,'procedural:mouth-0-10','procedural','{"key": "mouth-0-10", "style": "Smile", "color": "#42d8d0", "styleIndex": 0, "colorIndex": 10}'::jsonb),
('mouth','Smile / 12',60,'procedural:mouth-0-11','procedural','{"key": "mouth-0-11", "style": "Smile", "color": "#a5abb8", "styleIndex": 0, "colorIndex": 11}'::jsonb),
('mouth','Grin / 1',65,'procedural:mouth-1-0','procedural','{"key": "mouth-1-0", "style": "Grin", "color": "#e6e6e6", "styleIndex": 1, "colorIndex": 0}'::jsonb),
('mouth','Grin / 2',70,'procedural:mouth-1-1','procedural','{"key": "mouth-1-1", "style": "Grin", "color": "#181818", "styleIndex": 1, "colorIndex": 1}'::jsonb),
('mouth','Grin / 3',75,'procedural:mouth-1-2','procedural','{"key": "mouth-1-2", "style": "Grin", "color": "#ed4545", "styleIndex": 1, "colorIndex": 2}'::jsonb),
('mouth','Grin / 4',80,'procedural:mouth-1-3','procedural','{"key": "mouth-1-3", "style": "Grin", "color": "#3689ed", "styleIndex": 1, "colorIndex": 3}'::jsonb),
('mouth','Grin / 5',65,'procedural:mouth-1-4','procedural','{"key": "mouth-1-4", "style": "Grin", "color": "#37bf83", "styleIndex": 1, "colorIndex": 4}'::jsonb),
('mouth','Grin / 6',70,'procedural:mouth-1-5','procedural','{"key": "mouth-1-5", "style": "Grin", "color": "#f4c542", "styleIndex": 1, "colorIndex": 5}'::jsonb),
('mouth','Grin / 7',75,'procedural:mouth-1-6','procedural','{"key": "mouth-1-6", "style": "Grin", "color": "#9b62d9", "styleIndex": 1, "colorIndex": 6}'::jsonb),
('mouth','Grin / 8',80,'procedural:mouth-1-7','procedural','{"key": "mouth-1-7", "style": "Grin", "color": "#ef88c0", "styleIndex": 1, "colorIndex": 7}'::jsonb),
('mouth','Grin / 9',65,'procedural:mouth-1-8','procedural','{"key": "mouth-1-8", "style": "Grin", "color": "#ed8838", "styleIndex": 1, "colorIndex": 8}'::jsonb),
('mouth','Grin / 10',70,'procedural:mouth-1-9','procedural','{"key": "mouth-1-9", "style": "Grin", "color": "#6b4b35", "styleIndex": 1, "colorIndex": 9}'::jsonb),
('mouth','Grin / 11',75,'procedural:mouth-1-10','procedural','{"key": "mouth-1-10", "style": "Grin", "color": "#42d8d0", "styleIndex": 1, "colorIndex": 10}'::jsonb),
('mouth','Grin / 12',80,'procedural:mouth-1-11','procedural','{"key": "mouth-1-11", "style": "Grin", "color": "#a5abb8", "styleIndex": 1, "colorIndex": 11}'::jsonb),
('mouth','Tiny Smile / 1',85,'procedural:mouth-2-0','procedural','{"key": "mouth-2-0", "style": "Tiny Smile", "color": "#e6e6e6", "styleIndex": 2, "colorIndex": 0}'::jsonb),
('mouth','Tiny Smile / 2',90,'procedural:mouth-2-1','procedural','{"key": "mouth-2-1", "style": "Tiny Smile", "color": "#181818", "styleIndex": 2, "colorIndex": 1}'::jsonb),
('mouth','Tiny Smile / 3',95,'procedural:mouth-2-2','procedural','{"key": "mouth-2-2", "style": "Tiny Smile", "color": "#ed4545", "styleIndex": 2, "colorIndex": 2}'::jsonb),
('mouth','Tiny Smile / 4',100,'procedural:mouth-2-3','procedural','{"key": "mouth-2-3", "style": "Tiny Smile", "color": "#3689ed", "styleIndex": 2, "colorIndex": 3}'::jsonb),
('mouth','Tiny Smile / 5',85,'procedural:mouth-2-4','procedural','{"key": "mouth-2-4", "style": "Tiny Smile", "color": "#37bf83", "styleIndex": 2, "colorIndex": 4}'::jsonb),
('mouth','Tiny Smile / 6',90,'procedural:mouth-2-5','procedural','{"key": "mouth-2-5", "style": "Tiny Smile", "color": "#f4c542", "styleIndex": 2, "colorIndex": 5}'::jsonb),
('mouth','Tiny Smile / 7',95,'procedural:mouth-2-6','procedural','{"key": "mouth-2-6", "style": "Tiny Smile", "color": "#9b62d9", "styleIndex": 2, "colorIndex": 6}'::jsonb),
('mouth','Tiny Smile / 8',100,'procedural:mouth-2-7','procedural','{"key": "mouth-2-7", "style": "Tiny Smile", "color": "#ef88c0", "styleIndex": 2, "colorIndex": 7}'::jsonb),
('mouth','Tiny Smile / 9',85,'procedural:mouth-2-8','procedural','{"key": "mouth-2-8", "style": "Tiny Smile", "color": "#ed8838", "styleIndex": 2, "colorIndex": 8}'::jsonb),
('mouth','Tiny Smile / 10',90,'procedural:mouth-2-9','procedural','{"key": "mouth-2-9", "style": "Tiny Smile", "color": "#6b4b35", "styleIndex": 2, "colorIndex": 9}'::jsonb),
('mouth','Tiny Smile / 11',95,'procedural:mouth-2-10','procedural','{"key": "mouth-2-10", "style": "Tiny Smile", "color": "#42d8d0", "styleIndex": 2, "colorIndex": 10}'::jsonb),
('mouth','Tiny Smile / 12',100,'procedural:mouth-2-11','procedural','{"key": "mouth-2-11", "style": "Tiny Smile", "color": "#a5abb8", "styleIndex": 2, "colorIndex": 11}'::jsonb),
('mouth','Open / 1',105,'procedural:mouth-3-0','procedural','{"key": "mouth-3-0", "style": "Open", "color": "#e6e6e6", "styleIndex": 3, "colorIndex": 0}'::jsonb),
('mouth','Open / 2',110,'procedural:mouth-3-1','procedural','{"key": "mouth-3-1", "style": "Open", "color": "#181818", "styleIndex": 3, "colorIndex": 1}'::jsonb),
('mouth','Open / 3',115,'procedural:mouth-3-2','procedural','{"key": "mouth-3-2", "style": "Open", "color": "#ed4545", "styleIndex": 3, "colorIndex": 2}'::jsonb),
('mouth','Open / 4',120,'procedural:mouth-3-3','procedural','{"key": "mouth-3-3", "style": "Open", "color": "#3689ed", "styleIndex": 3, "colorIndex": 3}'::jsonb),
('mouth','Open / 5',105,'procedural:mouth-3-4','procedural','{"key": "mouth-3-4", "style": "Open", "color": "#37bf83", "styleIndex": 3, "colorIndex": 4}'::jsonb),
('mouth','Open / 6',110,'procedural:mouth-3-5','procedural','{"key": "mouth-3-5", "style": "Open", "color": "#f4c542", "styleIndex": 3, "colorIndex": 5}'::jsonb),
('mouth','Open / 7',115,'procedural:mouth-3-6','procedural','{"key": "mouth-3-6", "style": "Open", "color": "#9b62d9", "styleIndex": 3, "colorIndex": 6}'::jsonb),
('mouth','Open / 8',120,'procedural:mouth-3-7','procedural','{"key": "mouth-3-7", "style": "Open", "color": "#ef88c0", "styleIndex": 3, "colorIndex": 7}'::jsonb),
('mouth','Open / 9',105,'procedural:mouth-3-8','procedural','{"key": "mouth-3-8", "style": "Open", "color": "#ed8838", "styleIndex": 3, "colorIndex": 8}'::jsonb) ON CONFLICT (asset_url) WHERE asset_kind='procedural' DO NOTHING;
INSERT INTO store_items(category,name,price,asset_url,asset_kind,metadata) VALUES
('mouth','Open / 10',110,'procedural:mouth-3-9','procedural','{"key": "mouth-3-9", "style": "Open", "color": "#6b4b35", "styleIndex": 3, "colorIndex": 9}'::jsonb),
('mouth','Open / 11',115,'procedural:mouth-3-10','procedural','{"key": "mouth-3-10", "style": "Open", "color": "#42d8d0", "styleIndex": 3, "colorIndex": 10}'::jsonb),
('mouth','Open / 12',120,'procedural:mouth-3-11','procedural','{"key": "mouth-3-11", "style": "Open", "color": "#a5abb8", "styleIndex": 3, "colorIndex": 11}'::jsonb),
('mouth','Surprised / 1',125,'procedural:mouth-4-0','procedural','{"key": "mouth-4-0", "style": "Surprised", "color": "#e6e6e6", "styleIndex": 4, "colorIndex": 0}'::jsonb),
('mouth','Surprised / 2',130,'procedural:mouth-4-1','procedural','{"key": "mouth-4-1", "style": "Surprised", "color": "#181818", "styleIndex": 4, "colorIndex": 1}'::jsonb),
('mouth','Surprised / 3',135,'procedural:mouth-4-2','procedural','{"key": "mouth-4-2", "style": "Surprised", "color": "#ed4545", "styleIndex": 4, "colorIndex": 2}'::jsonb),
('mouth','Surprised / 4',140,'procedural:mouth-4-3','procedural','{"key": "mouth-4-3", "style": "Surprised", "color": "#3689ed", "styleIndex": 4, "colorIndex": 3}'::jsonb),
('mouth','Surprised / 5',125,'procedural:mouth-4-4','procedural','{"key": "mouth-4-4", "style": "Surprised", "color": "#37bf83", "styleIndex": 4, "colorIndex": 4}'::jsonb),
('mouth','Surprised / 6',130,'procedural:mouth-4-5','procedural','{"key": "mouth-4-5", "style": "Surprised", "color": "#f4c542", "styleIndex": 4, "colorIndex": 5}'::jsonb),
('mouth','Surprised / 7',135,'procedural:mouth-4-6','procedural','{"key": "mouth-4-6", "style": "Surprised", "color": "#9b62d9", "styleIndex": 4, "colorIndex": 6}'::jsonb),
('mouth','Surprised / 8',140,'procedural:mouth-4-7','procedural','{"key": "mouth-4-7", "style": "Surprised", "color": "#ef88c0", "styleIndex": 4, "colorIndex": 7}'::jsonb),
('mouth','Surprised / 9',125,'procedural:mouth-4-8','procedural','{"key": "mouth-4-8", "style": "Surprised", "color": "#ed8838", "styleIndex": 4, "colorIndex": 8}'::jsonb),
('mouth','Surprised / 10',130,'procedural:mouth-4-9','procedural','{"key": "mouth-4-9", "style": "Surprised", "color": "#6b4b35", "styleIndex": 4, "colorIndex": 9}'::jsonb),
('mouth','Surprised / 11',135,'procedural:mouth-4-10','procedural','{"key": "mouth-4-10", "style": "Surprised", "color": "#42d8d0", "styleIndex": 4, "colorIndex": 10}'::jsonb),
('mouth','Surprised / 12',140,'procedural:mouth-4-11','procedural','{"key": "mouth-4-11", "style": "Surprised", "color": "#a5abb8", "styleIndex": 4, "colorIndex": 11}'::jsonb),
('mouth','Frown / 1',45,'procedural:mouth-5-0','procedural','{"key": "mouth-5-0", "style": "Frown", "color": "#e6e6e6", "styleIndex": 5, "colorIndex": 0}'::jsonb),
('mouth','Frown / 2',50,'procedural:mouth-5-1','procedural','{"key": "mouth-5-1", "style": "Frown", "color": "#181818", "styleIndex": 5, "colorIndex": 1}'::jsonb),
('mouth','Frown / 3',55,'procedural:mouth-5-2','procedural','{"key": "mouth-5-2", "style": "Frown", "color": "#ed4545", "styleIndex": 5, "colorIndex": 2}'::jsonb),
('mouth','Frown / 4',60,'procedural:mouth-5-3','procedural','{"key": "mouth-5-3", "style": "Frown", "color": "#3689ed", "styleIndex": 5, "colorIndex": 3}'::jsonb),
('mouth','Frown / 5',45,'procedural:mouth-5-4','procedural','{"key": "mouth-5-4", "style": "Frown", "color": "#37bf83", "styleIndex": 5, "colorIndex": 4}'::jsonb),
('mouth','Frown / 6',50,'procedural:mouth-5-5','procedural','{"key": "mouth-5-5", "style": "Frown", "color": "#f4c542", "styleIndex": 5, "colorIndex": 5}'::jsonb),
('mouth','Frown / 7',55,'procedural:mouth-5-6','procedural','{"key": "mouth-5-6", "style": "Frown", "color": "#9b62d9", "styleIndex": 5, "colorIndex": 6}'::jsonb),
('mouth','Frown / 8',60,'procedural:mouth-5-7','procedural','{"key": "mouth-5-7", "style": "Frown", "color": "#ef88c0", "styleIndex": 5, "colorIndex": 7}'::jsonb),
('mouth','Frown / 9',45,'procedural:mouth-5-8','procedural','{"key": "mouth-5-8", "style": "Frown", "color": "#ed8838", "styleIndex": 5, "colorIndex": 8}'::jsonb),
('mouth','Frown / 10',50,'procedural:mouth-5-9','procedural','{"key": "mouth-5-9", "style": "Frown", "color": "#6b4b35", "styleIndex": 5, "colorIndex": 9}'::jsonb),
('mouth','Frown / 11',55,'procedural:mouth-5-10','procedural','{"key": "mouth-5-10", "style": "Frown", "color": "#42d8d0", "styleIndex": 5, "colorIndex": 10}'::jsonb),
('mouth','Frown / 12',60,'procedural:mouth-5-11','procedural','{"key": "mouth-5-11", "style": "Frown", "color": "#a5abb8", "styleIndex": 5, "colorIndex": 11}'::jsonb),
('mouth','Cat Smile / 1',65,'procedural:mouth-6-0','procedural','{"key": "mouth-6-0", "style": "Cat Smile", "color": "#e6e6e6", "styleIndex": 6, "colorIndex": 0}'::jsonb),
('mouth','Cat Smile / 2',70,'procedural:mouth-6-1','procedural','{"key": "mouth-6-1", "style": "Cat Smile", "color": "#181818", "styleIndex": 6, "colorIndex": 1}'::jsonb),
('mouth','Cat Smile / 3',75,'procedural:mouth-6-2','procedural','{"key": "mouth-6-2", "style": "Cat Smile", "color": "#ed4545", "styleIndex": 6, "colorIndex": 2}'::jsonb),
('mouth','Cat Smile / 4',80,'procedural:mouth-6-3','procedural','{"key": "mouth-6-3", "style": "Cat Smile", "color": "#3689ed", "styleIndex": 6, "colorIndex": 3}'::jsonb),
('mouth','Cat Smile / 5',65,'procedural:mouth-6-4','procedural','{"key": "mouth-6-4", "style": "Cat Smile", "color": "#37bf83", "styleIndex": 6, "colorIndex": 4}'::jsonb),
('mouth','Cat Smile / 6',70,'procedural:mouth-6-5','procedural','{"key": "mouth-6-5", "style": "Cat Smile", "color": "#f4c542", "styleIndex": 6, "colorIndex": 5}'::jsonb),
('mouth','Cat Smile / 7',75,'procedural:mouth-6-6','procedural','{"key": "mouth-6-6", "style": "Cat Smile", "color": "#9b62d9", "styleIndex": 6, "colorIndex": 6}'::jsonb),
('mouth','Cat Smile / 8',80,'procedural:mouth-6-7','procedural','{"key": "mouth-6-7", "style": "Cat Smile", "color": "#ef88c0", "styleIndex": 6, "colorIndex": 7}'::jsonb),
('mouth','Cat Smile / 9',65,'procedural:mouth-6-8','procedural','{"key": "mouth-6-8", "style": "Cat Smile", "color": "#ed8838", "styleIndex": 6, "colorIndex": 8}'::jsonb),
('mouth','Cat Smile / 10',70,'procedural:mouth-6-9','procedural','{"key": "mouth-6-9", "style": "Cat Smile", "color": "#6b4b35", "styleIndex": 6, "colorIndex": 9}'::jsonb),
('mouth','Cat Smile / 11',75,'procedural:mouth-6-10','procedural','{"key": "mouth-6-10", "style": "Cat Smile", "color": "#42d8d0", "styleIndex": 6, "colorIndex": 10}'::jsonb),
('mouth','Cat Smile / 12',80,'procedural:mouth-6-11','procedural','{"key": "mouth-6-11", "style": "Cat Smile", "color": "#a5abb8", "styleIndex": 6, "colorIndex": 11}'::jsonb),
('mouth','Wavy / 1',85,'procedural:mouth-7-0','procedural','{"key": "mouth-7-0", "style": "Wavy", "color": "#e6e6e6", "styleIndex": 7, "colorIndex": 0}'::jsonb),
('mouth','Wavy / 2',90,'procedural:mouth-7-1','procedural','{"key": "mouth-7-1", "style": "Wavy", "color": "#181818", "styleIndex": 7, "colorIndex": 1}'::jsonb),
('mouth','Wavy / 3',95,'procedural:mouth-7-2','procedural','{"key": "mouth-7-2", "style": "Wavy", "color": "#ed4545", "styleIndex": 7, "colorIndex": 2}'::jsonb),
('mouth','Wavy / 4',100,'procedural:mouth-7-3','procedural','{"key": "mouth-7-3", "style": "Wavy", "color": "#3689ed", "styleIndex": 7, "colorIndex": 3}'::jsonb),
('mouth','Wavy / 5',85,'procedural:mouth-7-4','procedural','{"key": "mouth-7-4", "style": "Wavy", "color": "#37bf83", "styleIndex": 7, "colorIndex": 4}'::jsonb),
('mouth','Wavy / 6',90,'procedural:mouth-7-5','procedural','{"key": "mouth-7-5", "style": "Wavy", "color": "#f4c542", "styleIndex": 7, "colorIndex": 5}'::jsonb),
('mouth','Wavy / 7',95,'procedural:mouth-7-6','procedural','{"key": "mouth-7-6", "style": "Wavy", "color": "#9b62d9", "styleIndex": 7, "colorIndex": 6}'::jsonb),
('mouth','Wavy / 8',100,'procedural:mouth-7-7','procedural','{"key": "mouth-7-7", "style": "Wavy", "color": "#ef88c0", "styleIndex": 7, "colorIndex": 7}'::jsonb),
('mouth','Wavy / 9',85,'procedural:mouth-7-8','procedural','{"key": "mouth-7-8", "style": "Wavy", "color": "#ed8838", "styleIndex": 7, "colorIndex": 8}'::jsonb),
('mouth','Wavy / 10',90,'procedural:mouth-7-9','procedural','{"key": "mouth-7-9", "style": "Wavy", "color": "#6b4b35", "styleIndex": 7, "colorIndex": 9}'::jsonb),
('mouth','Wavy / 11',95,'procedural:mouth-7-10','procedural','{"key": "mouth-7-10", "style": "Wavy", "color": "#42d8d0", "styleIndex": 7, "colorIndex": 10}'::jsonb),
('mouth','Wavy / 12',100,'procedural:mouth-7-11','procedural','{"key": "mouth-7-11", "style": "Wavy", "color": "#a5abb8", "styleIndex": 7, "colorIndex": 11}'::jsonb),
('mouth','Toothy / 1',105,'procedural:mouth-8-0','procedural','{"key": "mouth-8-0", "style": "Toothy", "color": "#e6e6e6", "styleIndex": 8, "colorIndex": 0}'::jsonb),
('mouth','Toothy / 2',110,'procedural:mouth-8-1','procedural','{"key": "mouth-8-1", "style": "Toothy", "color": "#181818", "styleIndex": 8, "colorIndex": 1}'::jsonb),
('mouth','Toothy / 3',115,'procedural:mouth-8-2','procedural','{"key": "mouth-8-2", "style": "Toothy", "color": "#ed4545", "styleIndex": 8, "colorIndex": 2}'::jsonb),
('mouth','Toothy / 4',120,'procedural:mouth-8-3','procedural','{"key": "mouth-8-3", "style": "Toothy", "color": "#3689ed", "styleIndex": 8, "colorIndex": 3}'::jsonb),
('mouth','Toothy / 5',105,'procedural:mouth-8-4','procedural','{"key": "mouth-8-4", "style": "Toothy", "color": "#37bf83", "styleIndex": 8, "colorIndex": 4}'::jsonb),
('mouth','Toothy / 6',110,'procedural:mouth-8-5','procedural','{"key": "mouth-8-5", "style": "Toothy", "color": "#f4c542", "styleIndex": 8, "colorIndex": 5}'::jsonb),
('mouth','Toothy / 7',115,'procedural:mouth-8-6','procedural','{"key": "mouth-8-6", "style": "Toothy", "color": "#9b62d9", "styleIndex": 8, "colorIndex": 6}'::jsonb),
('mouth','Toothy / 8',120,'procedural:mouth-8-7','procedural','{"key": "mouth-8-7", "style": "Toothy", "color": "#ef88c0", "styleIndex": 8, "colorIndex": 7}'::jsonb),
('mouth','Toothy / 9',105,'procedural:mouth-8-8','procedural','{"key": "mouth-8-8", "style": "Toothy", "color": "#ed8838", "styleIndex": 8, "colorIndex": 8}'::jsonb),
('mouth','Toothy / 10',110,'procedural:mouth-8-9','procedural','{"key": "mouth-8-9", "style": "Toothy", "color": "#6b4b35", "styleIndex": 8, "colorIndex": 9}'::jsonb),
('mouth','Toothy / 11',115,'procedural:mouth-8-10','procedural','{"key": "mouth-8-10", "style": "Toothy", "color": "#42d8d0", "styleIndex": 8, "colorIndex": 10}'::jsonb),
('mouth','Toothy / 12',120,'procedural:mouth-8-11','procedural','{"key": "mouth-8-11", "style": "Toothy", "color": "#a5abb8", "styleIndex": 8, "colorIndex": 11}'::jsonb),
('mouth','Smirk / 1',125,'procedural:mouth-9-0','procedural','{"key": "mouth-9-0", "style": "Smirk", "color": "#e6e6e6", "styleIndex": 9, "colorIndex": 0}'::jsonb),
('mouth','Smirk / 2',130,'procedural:mouth-9-1','procedural','{"key": "mouth-9-1", "style": "Smirk", "color": "#181818", "styleIndex": 9, "colorIndex": 1}'::jsonb),
('mouth','Smirk / 3',135,'procedural:mouth-9-2','procedural','{"key": "mouth-9-2", "style": "Smirk", "color": "#ed4545", "styleIndex": 9, "colorIndex": 2}'::jsonb),
('mouth','Smirk / 4',140,'procedural:mouth-9-3','procedural','{"key": "mouth-9-3", "style": "Smirk", "color": "#3689ed", "styleIndex": 9, "colorIndex": 3}'::jsonb),
('mouth','Smirk / 5',125,'procedural:mouth-9-4','procedural','{"key": "mouth-9-4", "style": "Smirk", "color": "#37bf83", "styleIndex": 9, "colorIndex": 4}'::jsonb),
('mouth','Smirk / 6',130,'procedural:mouth-9-5','procedural','{"key": "mouth-9-5", "style": "Smirk", "color": "#f4c542", "styleIndex": 9, "colorIndex": 5}'::jsonb),
('mouth','Smirk / 7',135,'procedural:mouth-9-6','procedural','{"key": "mouth-9-6", "style": "Smirk", "color": "#9b62d9", "styleIndex": 9, "colorIndex": 6}'::jsonb),
('mouth','Smirk / 8',140,'procedural:mouth-9-7','procedural','{"key": "mouth-9-7", "style": "Smirk", "color": "#ef88c0", "styleIndex": 9, "colorIndex": 7}'::jsonb),
('mouth','Smirk / 9',125,'procedural:mouth-9-8','procedural','{"key": "mouth-9-8", "style": "Smirk", "color": "#ed8838", "styleIndex": 9, "colorIndex": 8}'::jsonb),
('mouth','Smirk / 10',130,'procedural:mouth-9-9','procedural','{"key": "mouth-9-9", "style": "Smirk", "color": "#6b4b35", "styleIndex": 9, "colorIndex": 9}'::jsonb),
('mouth','Smirk / 11',135,'procedural:mouth-9-10','procedural','{"key": "mouth-9-10", "style": "Smirk", "color": "#42d8d0", "styleIndex": 9, "colorIndex": 10}'::jsonb),
('mouth','Smirk / 12',140,'procedural:mouth-9-11','procedural','{"key": "mouth-9-11", "style": "Smirk", "color": "#a5abb8", "styleIndex": 9, "colorIndex": 11}'::jsonb),
('skin','Classic / 1',45,'procedural:skin-0-0','procedural','{"key": "skin-0-0", "style": "Classic", "color": "#f5d7bd", "styleIndex": 0, "colorIndex": 0}'::jsonb),
('skin','Classic / 2',50,'procedural:skin-0-1','procedural','{"key": "skin-0-1", "style": "Classic", "color": "#e7b98d", "styleIndex": 0, "colorIndex": 1}'::jsonb),
('skin','Classic / 3',55,'procedural:skin-0-2','procedural','{"key": "skin-0-2", "style": "Classic", "color": "#cf9369", "styleIndex": 0, "colorIndex": 2}'::jsonb),
('skin','Classic / 4',60,'procedural:skin-0-3','procedural','{"key": "skin-0-3", "style": "Classic", "color": "#aa6d48", "styleIndex": 0, "colorIndex": 3}'::jsonb),
('skin','Classic / 5',45,'procedural:skin-0-4','procedural','{"key": "skin-0-4", "style": "Classic", "color": "#7e4b31", "styleIndex": 0, "colorIndex": 4}'::jsonb),
('skin','Classic / 6',50,'procedural:skin-0-5','procedural','{"key": "skin-0-5", "style": "Classic", "color": "#503020", "styleIndex": 0, "colorIndex": 5}'::jsonb),
('skin','Classic / 7',55,'procedural:skin-0-6','procedural','{"key": "skin-0-6", "style": "Classic", "color": "#f6d2c9", "styleIndex": 0, "colorIndex": 6}'::jsonb),
('skin','Classic / 8',60,'procedural:skin-0-7','procedural','{"key": "skin-0-7", "style": "Classic", "color": "#bfa68c", "styleIndex": 0, "colorIndex": 7}'::jsonb),
('skin','Classic / 9',45,'procedural:skin-0-8','procedural','{"key": "skin-0-8", "style": "Classic", "color": "#8b5cf6", "styleIndex": 0, "colorIndex": 8}'::jsonb),
('skin','Classic / 10',50,'procedural:skin-0-9','procedural','{"key": "skin-0-9", "style": "Classic", "color": "#54b5ed", "styleIndex": 0, "colorIndex": 9}'::jsonb),
('skin','Classic / 11',55,'procedural:skin-0-10','procedural','{"key": "skin-0-10", "style": "Classic", "color": "#68cf83", "styleIndex": 0, "colorIndex": 10}'::jsonb),
('skin','Classic / 12',60,'procedural:skin-0-11','procedural','{"key": "skin-0-11", "style": "Classic", "color": "#ff89c5", "styleIndex": 0, "colorIndex": 11}'::jsonb),
('skin','Classic / 13',45,'procedural:skin-0-12','procedural','{"key": "skin-0-12", "style": "Classic", "color": "#e6d85b", "styleIndex": 0, "colorIndex": 12}'::jsonb),
('skin','Classic / 14',50,'procedural:skin-0-13','procedural','{"key": "skin-0-13", "style": "Classic", "color": "#9699a6", "styleIndex": 0, "colorIndex": 13}'::jsonb),
('skin','Warm / 1',65,'procedural:skin-1-0','procedural','{"key": "skin-1-0", "style": "Warm", "color": "#f5d7bd", "styleIndex": 1, "colorIndex": 0}'::jsonb),
('skin','Warm / 2',70,'procedural:skin-1-1','procedural','{"key": "skin-1-1", "style": "Warm", "color": "#e7b98d", "styleIndex": 1, "colorIndex": 1}'::jsonb),
('skin','Warm / 3',75,'procedural:skin-1-2','procedural','{"key": "skin-1-2", "style": "Warm", "color": "#cf9369", "styleIndex": 1, "colorIndex": 2}'::jsonb),
('skin','Warm / 4',80,'procedural:skin-1-3','procedural','{"key": "skin-1-3", "style": "Warm", "color": "#aa6d48", "styleIndex": 1, "colorIndex": 3}'::jsonb),
('skin','Warm / 5',65,'procedural:skin-1-4','procedural','{"key": "skin-1-4", "style": "Warm", "color": "#7e4b31", "styleIndex": 1, "colorIndex": 4}'::jsonb),
('skin','Warm / 6',70,'procedural:skin-1-5','procedural','{"key": "skin-1-5", "style": "Warm", "color": "#503020", "styleIndex": 1, "colorIndex": 5}'::jsonb),
('skin','Warm / 7',75,'procedural:skin-1-6','procedural','{"key": "skin-1-6", "style": "Warm", "color": "#f6d2c9", "styleIndex": 1, "colorIndex": 6}'::jsonb),
('skin','Warm / 8',80,'procedural:skin-1-7','procedural','{"key": "skin-1-7", "style": "Warm", "color": "#bfa68c", "styleIndex": 1, "colorIndex": 7}'::jsonb),
('skin','Warm / 9',65,'procedural:skin-1-8','procedural','{"key": "skin-1-8", "style": "Warm", "color": "#8b5cf6", "styleIndex": 1, "colorIndex": 8}'::jsonb),
('skin','Warm / 10',70,'procedural:skin-1-9','procedural','{"key": "skin-1-9", "style": "Warm", "color": "#54b5ed", "styleIndex": 1, "colorIndex": 9}'::jsonb),
('skin','Warm / 11',75,'procedural:skin-1-10','procedural','{"key": "skin-1-10", "style": "Warm", "color": "#68cf83", "styleIndex": 1, "colorIndex": 10}'::jsonb),
('skin','Warm / 12',80,'procedural:skin-1-11','procedural','{"key": "skin-1-11", "style": "Warm", "color": "#ff89c5", "styleIndex": 1, "colorIndex": 11}'::jsonb),
('skin','Warm / 13',65,'procedural:skin-1-12','procedural','{"key": "skin-1-12", "style": "Warm", "color": "#e6d85b", "styleIndex": 1, "colorIndex": 12}'::jsonb),
('skin','Warm / 14',70,'procedural:skin-1-13','procedural','{"key": "skin-1-13", "style": "Warm", "color": "#9699a6", "styleIndex": 1, "colorIndex": 13}'::jsonb),
('skin','Cool / 1',85,'procedural:skin-2-0','procedural','{"key": "skin-2-0", "style": "Cool", "color": "#f5d7bd", "styleIndex": 2, "colorIndex": 0}'::jsonb),
('skin','Cool / 2',90,'procedural:skin-2-1','procedural','{"key": "skin-2-1", "style": "Cool", "color": "#e7b98d", "styleIndex": 2, "colorIndex": 1}'::jsonb),
('skin','Cool / 3',95,'procedural:skin-2-2','procedural','{"key": "skin-2-2", "style": "Cool", "color": "#cf9369", "styleIndex": 2, "colorIndex": 2}'::jsonb),
('skin','Cool / 4',100,'procedural:skin-2-3','procedural','{"key": "skin-2-3", "style": "Cool", "color": "#aa6d48", "styleIndex": 2, "colorIndex": 3}'::jsonb),
('skin','Cool / 5',85,'procedural:skin-2-4','procedural','{"key": "skin-2-4", "style": "Cool", "color": "#7e4b31", "styleIndex": 2, "colorIndex": 4}'::jsonb),
('skin','Cool / 6',90,'procedural:skin-2-5','procedural','{"key": "skin-2-5", "style": "Cool", "color": "#503020", "styleIndex": 2, "colorIndex": 5}'::jsonb),
('skin','Cool / 7',95,'procedural:skin-2-6','procedural','{"key": "skin-2-6", "style": "Cool", "color": "#f6d2c9", "styleIndex": 2, "colorIndex": 6}'::jsonb),
('skin','Cool / 8',100,'procedural:skin-2-7','procedural','{"key": "skin-2-7", "style": "Cool", "color": "#bfa68c", "styleIndex": 2, "colorIndex": 7}'::jsonb),
('skin','Cool / 9',85,'procedural:skin-2-8','procedural','{"key": "skin-2-8", "style": "Cool", "color": "#8b5cf6", "styleIndex": 2, "colorIndex": 8}'::jsonb),
('skin','Cool / 10',90,'procedural:skin-2-9','procedural','{"key": "skin-2-9", "style": "Cool", "color": "#54b5ed", "styleIndex": 2, "colorIndex": 9}'::jsonb),
('skin','Cool / 11',95,'procedural:skin-2-10','procedural','{"key": "skin-2-10", "style": "Cool", "color": "#68cf83", "styleIndex": 2, "colorIndex": 10}'::jsonb),
('skin','Cool / 12',100,'procedural:skin-2-11','procedural','{"key": "skin-2-11", "style": "Cool", "color": "#ff89c5", "styleIndex": 2, "colorIndex": 11}'::jsonb),
('skin','Cool / 13',85,'procedural:skin-2-12','procedural','{"key": "skin-2-12", "style": "Cool", "color": "#e6d85b", "styleIndex": 2, "colorIndex": 12}'::jsonb),
('skin','Cool / 14',90,'procedural:skin-2-13','procedural','{"key": "skin-2-13", "style": "Cool", "color": "#9699a6", "styleIndex": 2, "colorIndex": 13}'::jsonb),
('skin','Freckles / 1',105,'procedural:skin-3-0','procedural','{"key": "skin-3-0", "style": "Freckles", "color": "#f5d7bd", "styleIndex": 3, "colorIndex": 0}'::jsonb),
('skin','Freckles / 2',110,'procedural:skin-3-1','procedural','{"key": "skin-3-1", "style": "Freckles", "color": "#e7b98d", "styleIndex": 3, "colorIndex": 1}'::jsonb),
('skin','Freckles / 3',115,'procedural:skin-3-2','procedural','{"key": "skin-3-2", "style": "Freckles", "color": "#cf9369", "styleIndex": 3, "colorIndex": 2}'::jsonb) ON CONFLICT (asset_url) WHERE asset_kind='procedural' DO NOTHING;
INSERT INTO store_items(category,name,price,asset_url,asset_kind,metadata) VALUES
('skin','Freckles / 4',120,'procedural:skin-3-3','procedural','{"key": "skin-3-3", "style": "Freckles", "color": "#aa6d48", "styleIndex": 3, "colorIndex": 3}'::jsonb),
('skin','Freckles / 5',105,'procedural:skin-3-4','procedural','{"key": "skin-3-4", "style": "Freckles", "color": "#7e4b31", "styleIndex": 3, "colorIndex": 4}'::jsonb),
('skin','Freckles / 6',110,'procedural:skin-3-5','procedural','{"key": "skin-3-5", "style": "Freckles", "color": "#503020", "styleIndex": 3, "colorIndex": 5}'::jsonb),
('skin','Freckles / 7',115,'procedural:skin-3-6','procedural','{"key": "skin-3-6", "style": "Freckles", "color": "#f6d2c9", "styleIndex": 3, "colorIndex": 6}'::jsonb),
('skin','Freckles / 8',120,'procedural:skin-3-7','procedural','{"key": "skin-3-7", "style": "Freckles", "color": "#bfa68c", "styleIndex": 3, "colorIndex": 7}'::jsonb),
('skin','Freckles / 9',105,'procedural:skin-3-8','procedural','{"key": "skin-3-8", "style": "Freckles", "color": "#8b5cf6", "styleIndex": 3, "colorIndex": 8}'::jsonb),
('skin','Freckles / 10',110,'procedural:skin-3-9','procedural','{"key": "skin-3-9", "style": "Freckles", "color": "#54b5ed", "styleIndex": 3, "colorIndex": 9}'::jsonb),
('skin','Freckles / 11',115,'procedural:skin-3-10','procedural','{"key": "skin-3-10", "style": "Freckles", "color": "#68cf83", "styleIndex": 3, "colorIndex": 10}'::jsonb),
('skin','Freckles / 12',120,'procedural:skin-3-11','procedural','{"key": "skin-3-11", "style": "Freckles", "color": "#ff89c5", "styleIndex": 3, "colorIndex": 11}'::jsonb),
('skin','Freckles / 13',105,'procedural:skin-3-12','procedural','{"key": "skin-3-12", "style": "Freckles", "color": "#e6d85b", "styleIndex": 3, "colorIndex": 12}'::jsonb),
('skin','Freckles / 14',110,'procedural:skin-3-13','procedural','{"key": "skin-3-13", "style": "Freckles", "color": "#9699a6", "styleIndex": 3, "colorIndex": 13}'::jsonb),
('skin','Stripes / 1',125,'procedural:skin-4-0','procedural','{"key": "skin-4-0", "style": "Stripes", "color": "#f5d7bd", "styleIndex": 4, "colorIndex": 0}'::jsonb),
('skin','Stripes / 2',130,'procedural:skin-4-1','procedural','{"key": "skin-4-1", "style": "Stripes", "color": "#e7b98d", "styleIndex": 4, "colorIndex": 1}'::jsonb),
('skin','Stripes / 3',135,'procedural:skin-4-2','procedural','{"key": "skin-4-2", "style": "Stripes", "color": "#cf9369", "styleIndex": 4, "colorIndex": 2}'::jsonb),
('skin','Stripes / 4',140,'procedural:skin-4-3','procedural','{"key": "skin-4-3", "style": "Stripes", "color": "#aa6d48", "styleIndex": 4, "colorIndex": 3}'::jsonb),
('skin','Stripes / 5',125,'procedural:skin-4-4','procedural','{"key": "skin-4-4", "style": "Stripes", "color": "#7e4b31", "styleIndex": 4, "colorIndex": 4}'::jsonb),
('skin','Stripes / 6',130,'procedural:skin-4-5','procedural','{"key": "skin-4-5", "style": "Stripes", "color": "#503020", "styleIndex": 4, "colorIndex": 5}'::jsonb),
('skin','Stripes / 7',135,'procedural:skin-4-6','procedural','{"key": "skin-4-6", "style": "Stripes", "color": "#f6d2c9", "styleIndex": 4, "colorIndex": 6}'::jsonb),
('skin','Stripes / 8',140,'procedural:skin-4-7','procedural','{"key": "skin-4-7", "style": "Stripes", "color": "#bfa68c", "styleIndex": 4, "colorIndex": 7}'::jsonb),
('skin','Stripes / 9',125,'procedural:skin-4-8','procedural','{"key": "skin-4-8", "style": "Stripes", "color": "#8b5cf6", "styleIndex": 4, "colorIndex": 8}'::jsonb),
('skin','Stripes / 10',130,'procedural:skin-4-9','procedural','{"key": "skin-4-9", "style": "Stripes", "color": "#54b5ed", "styleIndex": 4, "colorIndex": 9}'::jsonb),
('skin','Stripes / 11',135,'procedural:skin-4-10','procedural','{"key": "skin-4-10", "style": "Stripes", "color": "#68cf83", "styleIndex": 4, "colorIndex": 10}'::jsonb),
('skin','Stripes / 12',140,'procedural:skin-4-11','procedural','{"key": "skin-4-11", "style": "Stripes", "color": "#ff89c5", "styleIndex": 4, "colorIndex": 11}'::jsonb),
('skin','Stripes / 13',125,'procedural:skin-4-12','procedural','{"key": "skin-4-12", "style": "Stripes", "color": "#e6d85b", "styleIndex": 4, "colorIndex": 12}'::jsonb),
('skin','Stripes / 14',130,'procedural:skin-4-13','procedural','{"key": "skin-4-13", "style": "Stripes", "color": "#9699a6", "styleIndex": 4, "colorIndex": 13}'::jsonb),
('skin','Spots / 1',45,'procedural:skin-5-0','procedural','{"key": "skin-5-0", "style": "Spots", "color": "#f5d7bd", "styleIndex": 5, "colorIndex": 0}'::jsonb),
('skin','Spots / 2',50,'procedural:skin-5-1','procedural','{"key": "skin-5-1", "style": "Spots", "color": "#e7b98d", "styleIndex": 5, "colorIndex": 1}'::jsonb),
('skin','Spots / 3',55,'procedural:skin-5-2','procedural','{"key": "skin-5-2", "style": "Spots", "color": "#cf9369", "styleIndex": 5, "colorIndex": 2}'::jsonb),
('skin','Spots / 4',60,'procedural:skin-5-3','procedural','{"key": "skin-5-3", "style": "Spots", "color": "#aa6d48", "styleIndex": 5, "colorIndex": 3}'::jsonb),
('skin','Spots / 5',45,'procedural:skin-5-4','procedural','{"key": "skin-5-4", "style": "Spots", "color": "#7e4b31", "styleIndex": 5, "colorIndex": 4}'::jsonb),
('skin','Spots / 6',50,'procedural:skin-5-5','procedural','{"key": "skin-5-5", "style": "Spots", "color": "#503020", "styleIndex": 5, "colorIndex": 5}'::jsonb),
('skin','Spots / 7',55,'procedural:skin-5-6','procedural','{"key": "skin-5-6", "style": "Spots", "color": "#f6d2c9", "styleIndex": 5, "colorIndex": 6}'::jsonb),
('skin','Spots / 8',60,'procedural:skin-5-7','procedural','{"key": "skin-5-7", "style": "Spots", "color": "#bfa68c", "styleIndex": 5, "colorIndex": 7}'::jsonb),
('skin','Spots / 9',45,'procedural:skin-5-8','procedural','{"key": "skin-5-8", "style": "Spots", "color": "#8b5cf6", "styleIndex": 5, "colorIndex": 8}'::jsonb),
('skin','Spots / 10',50,'procedural:skin-5-9','procedural','{"key": "skin-5-9", "style": "Spots", "color": "#54b5ed", "styleIndex": 5, "colorIndex": 9}'::jsonb),
('skin','Spots / 11',55,'procedural:skin-5-10','procedural','{"key": "skin-5-10", "style": "Spots", "color": "#68cf83", "styleIndex": 5, "colorIndex": 10}'::jsonb),
('skin','Spots / 12',60,'procedural:skin-5-11','procedural','{"key": "skin-5-11", "style": "Spots", "color": "#ff89c5", "styleIndex": 5, "colorIndex": 11}'::jsonb),
('skin','Spots / 13',45,'procedural:skin-5-12','procedural','{"key": "skin-5-12", "style": "Spots", "color": "#e6d85b", "styleIndex": 5, "colorIndex": 12}'::jsonb),
('skin','Spots / 14',50,'procedural:skin-5-13','procedural','{"key": "skin-5-13", "style": "Spots", "color": "#9699a6", "styleIndex": 5, "colorIndex": 13}'::jsonb),
('skin','Starry / 1',65,'procedural:skin-6-0','procedural','{"key": "skin-6-0", "style": "Starry", "color": "#f5d7bd", "styleIndex": 6, "colorIndex": 0}'::jsonb),
('skin','Starry / 2',70,'procedural:skin-6-1','procedural','{"key": "skin-6-1", "style": "Starry", "color": "#e7b98d", "styleIndex": 6, "colorIndex": 1}'::jsonb),
('skin','Starry / 3',75,'procedural:skin-6-2','procedural','{"key": "skin-6-2", "style": "Starry", "color": "#cf9369", "styleIndex": 6, "colorIndex": 2}'::jsonb),
('skin','Starry / 4',80,'procedural:skin-6-3','procedural','{"key": "skin-6-3", "style": "Starry", "color": "#aa6d48", "styleIndex": 6, "colorIndex": 3}'::jsonb),
('skin','Starry / 5',65,'procedural:skin-6-4','procedural','{"key": "skin-6-4", "style": "Starry", "color": "#7e4b31", "styleIndex": 6, "colorIndex": 4}'::jsonb),
('skin','Starry / 6',70,'procedural:skin-6-5','procedural','{"key": "skin-6-5", "style": "Starry", "color": "#503020", "styleIndex": 6, "colorIndex": 5}'::jsonb),
('skin','Starry / 7',75,'procedural:skin-6-6','procedural','{"key": "skin-6-6", "style": "Starry", "color": "#f6d2c9", "styleIndex": 6, "colorIndex": 6}'::jsonb),
('skin','Starry / 8',80,'procedural:skin-6-7','procedural','{"key": "skin-6-7", "style": "Starry", "color": "#bfa68c", "styleIndex": 6, "colorIndex": 7}'::jsonb),
('skin','Starry / 9',65,'procedural:skin-6-8','procedural','{"key": "skin-6-8", "style": "Starry", "color": "#8b5cf6", "styleIndex": 6, "colorIndex": 8}'::jsonb),
('skin','Starry / 10',70,'procedural:skin-6-9','procedural','{"key": "skin-6-9", "style": "Starry", "color": "#54b5ed", "styleIndex": 6, "colorIndex": 9}'::jsonb),
('skin','Starry / 11',75,'procedural:skin-6-10','procedural','{"key": "skin-6-10", "style": "Starry", "color": "#68cf83", "styleIndex": 6, "colorIndex": 10}'::jsonb),
('skin','Starry / 12',80,'procedural:skin-6-11','procedural','{"key": "skin-6-11", "style": "Starry", "color": "#ff89c5", "styleIndex": 6, "colorIndex": 11}'::jsonb),
('skin','Starry / 13',65,'procedural:skin-6-12','procedural','{"key": "skin-6-12", "style": "Starry", "color": "#e6d85b", "styleIndex": 6, "colorIndex": 12}'::jsonb),
('skin','Starry / 14',70,'procedural:skin-6-13','procedural','{"key": "skin-6-13", "style": "Starry", "color": "#9699a6", "styleIndex": 6, "colorIndex": 13}'::jsonb),
('skin','Marble / 1',85,'procedural:skin-7-0','procedural','{"key": "skin-7-0", "style": "Marble", "color": "#f5d7bd", "styleIndex": 7, "colorIndex": 0}'::jsonb),
('skin','Marble / 2',90,'procedural:skin-7-1','procedural','{"key": "skin-7-1", "style": "Marble", "color": "#e7b98d", "styleIndex": 7, "colorIndex": 1}'::jsonb),
('skin','Marble / 3',95,'procedural:skin-7-2','procedural','{"key": "skin-7-2", "style": "Marble", "color": "#cf9369", "styleIndex": 7, "colorIndex": 2}'::jsonb),
('skin','Marble / 4',100,'procedural:skin-7-3','procedural','{"key": "skin-7-3", "style": "Marble", "color": "#aa6d48", "styleIndex": 7, "colorIndex": 3}'::jsonb),
('skin','Marble / 5',85,'procedural:skin-7-4','procedural','{"key": "skin-7-4", "style": "Marble", "color": "#7e4b31", "styleIndex": 7, "colorIndex": 4}'::jsonb),
('skin','Marble / 6',90,'procedural:skin-7-5','procedural','{"key": "skin-7-5", "style": "Marble", "color": "#503020", "styleIndex": 7, "colorIndex": 5}'::jsonb),
('skin','Marble / 7',95,'procedural:skin-7-6','procedural','{"key": "skin-7-6", "style": "Marble", "color": "#f6d2c9", "styleIndex": 7, "colorIndex": 6}'::jsonb),
('skin','Marble / 8',100,'procedural:skin-7-7','procedural','{"key": "skin-7-7", "style": "Marble", "color": "#bfa68c", "styleIndex": 7, "colorIndex": 7}'::jsonb),
('skin','Marble / 9',85,'procedural:skin-7-8','procedural','{"key": "skin-7-8", "style": "Marble", "color": "#8b5cf6", "styleIndex": 7, "colorIndex": 8}'::jsonb),
('skin','Marble / 10',90,'procedural:skin-7-9','procedural','{"key": "skin-7-9", "style": "Marble", "color": "#54b5ed", "styleIndex": 7, "colorIndex": 9}'::jsonb),
('skin','Marble / 11',95,'procedural:skin-7-10','procedural','{"key": "skin-7-10", "style": "Marble", "color": "#68cf83", "styleIndex": 7, "colorIndex": 10}'::jsonb),
('skin','Marble / 12',100,'procedural:skin-7-11','procedural','{"key": "skin-7-11", "style": "Marble", "color": "#ff89c5", "styleIndex": 7, "colorIndex": 11}'::jsonb),
('skin','Marble / 13',85,'procedural:skin-7-12','procedural','{"key": "skin-7-12", "style": "Marble", "color": "#e6d85b", "styleIndex": 7, "colorIndex": 12}'::jsonb),
('skin','Marble / 14',90,'procedural:skin-7-13','procedural','{"key": "skin-7-13", "style": "Marble", "color": "#9699a6", "styleIndex": 7, "colorIndex": 13}'::jsonb),
('skin','Galaxy / 1',105,'procedural:skin-8-0','procedural','{"key": "skin-8-0", "style": "Galaxy", "color": "#f5d7bd", "styleIndex": 8, "colorIndex": 0}'::jsonb),
('skin','Galaxy / 2',110,'procedural:skin-8-1','procedural','{"key": "skin-8-1", "style": "Galaxy", "color": "#e7b98d", "styleIndex": 8, "colorIndex": 1}'::jsonb),
('skin','Galaxy / 3',115,'procedural:skin-8-2','procedural','{"key": "skin-8-2", "style": "Galaxy", "color": "#cf9369", "styleIndex": 8, "colorIndex": 2}'::jsonb),
('skin','Galaxy / 4',120,'procedural:skin-8-3','procedural','{"key": "skin-8-3", "style": "Galaxy", "color": "#aa6d48", "styleIndex": 8, "colorIndex": 3}'::jsonb),
('skin','Galaxy / 5',105,'procedural:skin-8-4','procedural','{"key": "skin-8-4", "style": "Galaxy", "color": "#7e4b31", "styleIndex": 8, "colorIndex": 4}'::jsonb),
('skin','Galaxy / 6',110,'procedural:skin-8-5','procedural','{"key": "skin-8-5", "style": "Galaxy", "color": "#503020", "styleIndex": 8, "colorIndex": 5}'::jsonb),
('skin','Galaxy / 7',115,'procedural:skin-8-6','procedural','{"key": "skin-8-6", "style": "Galaxy", "color": "#f6d2c9", "styleIndex": 8, "colorIndex": 6}'::jsonb),
('skin','Galaxy / 8',120,'procedural:skin-8-7','procedural','{"key": "skin-8-7", "style": "Galaxy", "color": "#bfa68c", "styleIndex": 8, "colorIndex": 7}'::jsonb),
('skin','Galaxy / 9',105,'procedural:skin-8-8','procedural','{"key": "skin-8-8", "style": "Galaxy", "color": "#8b5cf6", "styleIndex": 8, "colorIndex": 8}'::jsonb),
('skin','Galaxy / 10',110,'procedural:skin-8-9','procedural','{"key": "skin-8-9", "style": "Galaxy", "color": "#54b5ed", "styleIndex": 8, "colorIndex": 9}'::jsonb),
('skin','Galaxy / 11',115,'procedural:skin-8-10','procedural','{"key": "skin-8-10", "style": "Galaxy", "color": "#68cf83", "styleIndex": 8, "colorIndex": 10}'::jsonb),
('skin','Galaxy / 12',120,'procedural:skin-8-11','procedural','{"key": "skin-8-11", "style": "Galaxy", "color": "#ff89c5", "styleIndex": 8, "colorIndex": 11}'::jsonb),
('skin','Galaxy / 13',105,'procedural:skin-8-12','procedural','{"key": "skin-8-12", "style": "Galaxy", "color": "#e6d85b", "styleIndex": 8, "colorIndex": 12}'::jsonb),
('skin','Galaxy / 14',110,'procedural:skin-8-13','procedural','{"key": "skin-8-13", "style": "Galaxy", "color": "#9699a6", "styleIndex": 8, "colorIndex": 13}'::jsonb),
('tops','T Shirt / 1',45,'procedural:tops-0-0','procedural','{"key": "tops-0-0", "style": "T Shirt", "color": "#e6e6e6", "styleIndex": 0, "colorIndex": 0}'::jsonb),
('tops','T Shirt / 2',50,'procedural:tops-0-1','procedural','{"key": "tops-0-1", "style": "T Shirt", "color": "#181818", "styleIndex": 0, "colorIndex": 1}'::jsonb),
('tops','T Shirt / 3',55,'procedural:tops-0-2','procedural','{"key": "tops-0-2", "style": "T Shirt", "color": "#ed4545", "styleIndex": 0, "colorIndex": 2}'::jsonb),
('tops','T Shirt / 4',60,'procedural:tops-0-3','procedural','{"key": "tops-0-3", "style": "T Shirt", "color": "#3689ed", "styleIndex": 0, "colorIndex": 3}'::jsonb),
('tops','T Shirt / 5',45,'procedural:tops-0-4','procedural','{"key": "tops-0-4", "style": "T Shirt", "color": "#37bf83", "styleIndex": 0, "colorIndex": 4}'::jsonb),
('tops','T Shirt / 6',50,'procedural:tops-0-5','procedural','{"key": "tops-0-5", "style": "T Shirt", "color": "#f4c542", "styleIndex": 0, "colorIndex": 5}'::jsonb),
('tops','T Shirt / 7',55,'procedural:tops-0-6','procedural','{"key": "tops-0-6", "style": "T Shirt", "color": "#9b62d9", "styleIndex": 0, "colorIndex": 6}'::jsonb),
('tops','T Shirt / 8',60,'procedural:tops-0-7','procedural','{"key": "tops-0-7", "style": "T Shirt", "color": "#ef88c0", "styleIndex": 0, "colorIndex": 7}'::jsonb),
('tops','T Shirt / 9',45,'procedural:tops-0-8','procedural','{"key": "tops-0-8", "style": "T Shirt", "color": "#ed8838", "styleIndex": 0, "colorIndex": 8}'::jsonb),
('tops','T Shirt / 10',50,'procedural:tops-0-9','procedural','{"key": "tops-0-9", "style": "T Shirt", "color": "#6b4b35", "styleIndex": 0, "colorIndex": 9}'::jsonb),
('tops','T Shirt / 11',55,'procedural:tops-0-10','procedural','{"key": "tops-0-10", "style": "T Shirt", "color": "#42d8d0", "styleIndex": 0, "colorIndex": 10}'::jsonb),
('tops','T Shirt / 12',60,'procedural:tops-0-11','procedural','{"key": "tops-0-11", "style": "T Shirt", "color": "#a5abb8", "styleIndex": 0, "colorIndex": 11}'::jsonb),
('tops','Long Sleeve / 1',65,'procedural:tops-1-0','procedural','{"key": "tops-1-0", "style": "Long Sleeve", "color": "#e6e6e6", "styleIndex": 1, "colorIndex": 0}'::jsonb),
('tops','Long Sleeve / 2',70,'procedural:tops-1-1','procedural','{"key": "tops-1-1", "style": "Long Sleeve", "color": "#181818", "styleIndex": 1, "colorIndex": 1}'::jsonb),
('tops','Long Sleeve / 3',75,'procedural:tops-1-2','procedural','{"key": "tops-1-2", "style": "Long Sleeve", "color": "#ed4545", "styleIndex": 1, "colorIndex": 2}'::jsonb),
('tops','Long Sleeve / 4',80,'procedural:tops-1-3','procedural','{"key": "tops-1-3", "style": "Long Sleeve", "color": "#3689ed", "styleIndex": 1, "colorIndex": 3}'::jsonb),
('tops','Long Sleeve / 5',65,'procedural:tops-1-4','procedural','{"key": "tops-1-4", "style": "Long Sleeve", "color": "#37bf83", "styleIndex": 1, "colorIndex": 4}'::jsonb),
('tops','Long Sleeve / 6',70,'procedural:tops-1-5','procedural','{"key": "tops-1-5", "style": "Long Sleeve", "color": "#f4c542", "styleIndex": 1, "colorIndex": 5}'::jsonb),
('tops','Long Sleeve / 7',75,'procedural:tops-1-6','procedural','{"key": "tops-1-6", "style": "Long Sleeve", "color": "#9b62d9", "styleIndex": 1, "colorIndex": 6}'::jsonb),
('tops','Long Sleeve / 8',80,'procedural:tops-1-7','procedural','{"key": "tops-1-7", "style": "Long Sleeve", "color": "#ef88c0", "styleIndex": 1, "colorIndex": 7}'::jsonb),
('tops','Long Sleeve / 9',65,'procedural:tops-1-8','procedural','{"key": "tops-1-8", "style": "Long Sleeve", "color": "#ed8838", "styleIndex": 1, "colorIndex": 8}'::jsonb),
('tops','Long Sleeve / 10',70,'procedural:tops-1-9','procedural','{"key": "tops-1-9", "style": "Long Sleeve", "color": "#6b4b35", "styleIndex": 1, "colorIndex": 9}'::jsonb),
('tops','Long Sleeve / 11',75,'procedural:tops-1-10','procedural','{"key": "tops-1-10", "style": "Long Sleeve", "color": "#42d8d0", "styleIndex": 1, "colorIndex": 10}'::jsonb),
('tops','Long Sleeve / 12',80,'procedural:tops-1-11','procedural','{"key": "tops-1-11", "style": "Long Sleeve", "color": "#a5abb8", "styleIndex": 1, "colorIndex": 11}'::jsonb),
('tops','Hoodie / 1',85,'procedural:tops-2-0','procedural','{"key": "tops-2-0", "style": "Hoodie", "color": "#e6e6e6", "styleIndex": 2, "colorIndex": 0}'::jsonb),
('tops','Hoodie / 2',90,'procedural:tops-2-1','procedural','{"key": "tops-2-1", "style": "Hoodie", "color": "#181818", "styleIndex": 2, "colorIndex": 1}'::jsonb),
('tops','Hoodie / 3',95,'procedural:tops-2-2','procedural','{"key": "tops-2-2", "style": "Hoodie", "color": "#ed4545", "styleIndex": 2, "colorIndex": 2}'::jsonb),
('tops','Hoodie / 4',100,'procedural:tops-2-3','procedural','{"key": "tops-2-3", "style": "Hoodie", "color": "#3689ed", "styleIndex": 2, "colorIndex": 3}'::jsonb),
('tops','Hoodie / 5',85,'procedural:tops-2-4','procedural','{"key": "tops-2-4", "style": "Hoodie", "color": "#37bf83", "styleIndex": 2, "colorIndex": 4}'::jsonb),
('tops','Hoodie / 6',90,'procedural:tops-2-5','procedural','{"key": "tops-2-5", "style": "Hoodie", "color": "#f4c542", "styleIndex": 2, "colorIndex": 5}'::jsonb),
('tops','Hoodie / 7',95,'procedural:tops-2-6','procedural','{"key": "tops-2-6", "style": "Hoodie", "color": "#9b62d9", "styleIndex": 2, "colorIndex": 6}'::jsonb),
('tops','Hoodie / 8',100,'procedural:tops-2-7','procedural','{"key": "tops-2-7", "style": "Hoodie", "color": "#ef88c0", "styleIndex": 2, "colorIndex": 7}'::jsonb),
('tops','Hoodie / 9',85,'procedural:tops-2-8','procedural','{"key": "tops-2-8", "style": "Hoodie", "color": "#ed8838", "styleIndex": 2, "colorIndex": 8}'::jsonb),
('tops','Hoodie / 10',90,'procedural:tops-2-9','procedural','{"key": "tops-2-9", "style": "Hoodie", "color": "#6b4b35", "styleIndex": 2, "colorIndex": 9}'::jsonb),
('tops','Hoodie / 11',95,'procedural:tops-2-10','procedural','{"key": "tops-2-10", "style": "Hoodie", "color": "#42d8d0", "styleIndex": 2, "colorIndex": 10}'::jsonb),
('tops','Hoodie / 12',100,'procedural:tops-2-11','procedural','{"key": "tops-2-11", "style": "Hoodie", "color": "#a5abb8", "styleIndex": 2, "colorIndex": 11}'::jsonb),
('tops','Crop Top / 1',105,'procedural:tops-3-0','procedural','{"key": "tops-3-0", "style": "Crop Top", "color": "#e6e6e6", "styleIndex": 3, "colorIndex": 0}'::jsonb),
('tops','Crop Top / 2',110,'procedural:tops-3-1','procedural','{"key": "tops-3-1", "style": "Crop Top", "color": "#181818", "styleIndex": 3, "colorIndex": 1}'::jsonb),
('tops','Crop Top / 3',115,'procedural:tops-3-2','procedural','{"key": "tops-3-2", "style": "Crop Top", "color": "#ed4545", "styleIndex": 3, "colorIndex": 2}'::jsonb) ON CONFLICT (asset_url) WHERE asset_kind='procedural' DO NOTHING;
INSERT INTO store_items(category,name,price,asset_url,asset_kind,metadata) VALUES
('tops','Crop Top / 4',120,'procedural:tops-3-3','procedural','{"key": "tops-3-3", "style": "Crop Top", "color": "#3689ed", "styleIndex": 3, "colorIndex": 3}'::jsonb),
('tops','Crop Top / 5',105,'procedural:tops-3-4','procedural','{"key": "tops-3-4", "style": "Crop Top", "color": "#37bf83", "styleIndex": 3, "colorIndex": 4}'::jsonb),
('tops','Crop Top / 6',110,'procedural:tops-3-5','procedural','{"key": "tops-3-5", "style": "Crop Top", "color": "#f4c542", "styleIndex": 3, "colorIndex": 5}'::jsonb),
('tops','Crop Top / 7',115,'procedural:tops-3-6','procedural','{"key": "tops-3-6", "style": "Crop Top", "color": "#9b62d9", "styleIndex": 3, "colorIndex": 6}'::jsonb),
('tops','Crop Top / 8',120,'procedural:tops-3-7','procedural','{"key": "tops-3-7", "style": "Crop Top", "color": "#ef88c0", "styleIndex": 3, "colorIndex": 7}'::jsonb),
('tops','Crop Top / 9',105,'procedural:tops-3-8','procedural','{"key": "tops-3-8", "style": "Crop Top", "color": "#ed8838", "styleIndex": 3, "colorIndex": 8}'::jsonb),
('tops','Crop Top / 10',110,'procedural:tops-3-9','procedural','{"key": "tops-3-9", "style": "Crop Top", "color": "#6b4b35", "styleIndex": 3, "colorIndex": 9}'::jsonb),
('tops','Crop Top / 11',115,'procedural:tops-3-10','procedural','{"key": "tops-3-10", "style": "Crop Top", "color": "#42d8d0", "styleIndex": 3, "colorIndex": 10}'::jsonb),
('tops','Crop Top / 12',120,'procedural:tops-3-11','procedural','{"key": "tops-3-11", "style": "Crop Top", "color": "#a5abb8", "styleIndex": 3, "colorIndex": 11}'::jsonb),
('tops','Suit / 1',125,'procedural:tops-4-0','procedural','{"key": "tops-4-0", "style": "Suit", "color": "#e6e6e6", "styleIndex": 4, "colorIndex": 0}'::jsonb),
('tops','Suit / 2',130,'procedural:tops-4-1','procedural','{"key": "tops-4-1", "style": "Suit", "color": "#181818", "styleIndex": 4, "colorIndex": 1}'::jsonb),
('tops','Suit / 3',135,'procedural:tops-4-2','procedural','{"key": "tops-4-2", "style": "Suit", "color": "#ed4545", "styleIndex": 4, "colorIndex": 2}'::jsonb),
('tops','Suit / 4',140,'procedural:tops-4-3','procedural','{"key": "tops-4-3", "style": "Suit", "color": "#3689ed", "styleIndex": 4, "colorIndex": 3}'::jsonb),
('tops','Suit / 5',125,'procedural:tops-4-4','procedural','{"key": "tops-4-4", "style": "Suit", "color": "#37bf83", "styleIndex": 4, "colorIndex": 4}'::jsonb),
('tops','Suit / 6',130,'procedural:tops-4-5','procedural','{"key": "tops-4-5", "style": "Suit", "color": "#f4c542", "styleIndex": 4, "colorIndex": 5}'::jsonb),
('tops','Suit / 7',135,'procedural:tops-4-6','procedural','{"key": "tops-4-6", "style": "Suit", "color": "#9b62d9", "styleIndex": 4, "colorIndex": 6}'::jsonb),
('tops','Suit / 8',140,'procedural:tops-4-7','procedural','{"key": "tops-4-7", "style": "Suit", "color": "#ef88c0", "styleIndex": 4, "colorIndex": 7}'::jsonb),
('tops','Suit / 9',125,'procedural:tops-4-8','procedural','{"key": "tops-4-8", "style": "Suit", "color": "#ed8838", "styleIndex": 4, "colorIndex": 8}'::jsonb),
('tops','Suit / 10',130,'procedural:tops-4-9','procedural','{"key": "tops-4-9", "style": "Suit", "color": "#6b4b35", "styleIndex": 4, "colorIndex": 9}'::jsonb),
('tops','Suit / 11',135,'procedural:tops-4-10','procedural','{"key": "tops-4-10", "style": "Suit", "color": "#42d8d0", "styleIndex": 4, "colorIndex": 10}'::jsonb),
('tops','Suit / 12',140,'procedural:tops-4-11','procedural','{"key": "tops-4-11", "style": "Suit", "color": "#a5abb8", "styleIndex": 4, "colorIndex": 11}'::jsonb),
('tops','Tank Top / 1',45,'procedural:tops-5-0','procedural','{"key": "tops-5-0", "style": "Tank Top", "color": "#e6e6e6", "styleIndex": 5, "colorIndex": 0}'::jsonb),
('tops','Tank Top / 2',50,'procedural:tops-5-1','procedural','{"key": "tops-5-1", "style": "Tank Top", "color": "#181818", "styleIndex": 5, "colorIndex": 1}'::jsonb),
('tops','Tank Top / 3',55,'procedural:tops-5-2','procedural','{"key": "tops-5-2", "style": "Tank Top", "color": "#ed4545", "styleIndex": 5, "colorIndex": 2}'::jsonb),
('tops','Tank Top / 4',60,'procedural:tops-5-3','procedural','{"key": "tops-5-3", "style": "Tank Top", "color": "#3689ed", "styleIndex": 5, "colorIndex": 3}'::jsonb),
('tops','Tank Top / 5',45,'procedural:tops-5-4','procedural','{"key": "tops-5-4", "style": "Tank Top", "color": "#37bf83", "styleIndex": 5, "colorIndex": 4}'::jsonb),
('tops','Tank Top / 6',50,'procedural:tops-5-5','procedural','{"key": "tops-5-5", "style": "Tank Top", "color": "#f4c542", "styleIndex": 5, "colorIndex": 5}'::jsonb),
('tops','Tank Top / 7',55,'procedural:tops-5-6','procedural','{"key": "tops-5-6", "style": "Tank Top", "color": "#9b62d9", "styleIndex": 5, "colorIndex": 6}'::jsonb),
('tops','Tank Top / 8',60,'procedural:tops-5-7','procedural','{"key": "tops-5-7", "style": "Tank Top", "color": "#ef88c0", "styleIndex": 5, "colorIndex": 7}'::jsonb),
('tops','Tank Top / 9',45,'procedural:tops-5-8','procedural','{"key": "tops-5-8", "style": "Tank Top", "color": "#ed8838", "styleIndex": 5, "colorIndex": 8}'::jsonb),
('tops','Tank Top / 10',50,'procedural:tops-5-9','procedural','{"key": "tops-5-9", "style": "Tank Top", "color": "#6b4b35", "styleIndex": 5, "colorIndex": 9}'::jsonb),
('tops','Tank Top / 11',55,'procedural:tops-5-10','procedural','{"key": "tops-5-10", "style": "Tank Top", "color": "#42d8d0", "styleIndex": 5, "colorIndex": 10}'::jsonb),
('tops','Tank Top / 12',60,'procedural:tops-5-11','procedural','{"key": "tops-5-11", "style": "Tank Top", "color": "#a5abb8", "styleIndex": 5, "colorIndex": 11}'::jsonb),
('tops','Trench Coat / 1',65,'procedural:tops-6-0','procedural','{"key": "tops-6-0", "style": "Trench Coat", "color": "#e6e6e6", "styleIndex": 6, "colorIndex": 0}'::jsonb),
('tops','Trench Coat / 2',70,'procedural:tops-6-1','procedural','{"key": "tops-6-1", "style": "Trench Coat", "color": "#181818", "styleIndex": 6, "colorIndex": 1}'::jsonb),
('tops','Trench Coat / 3',75,'procedural:tops-6-2','procedural','{"key": "tops-6-2", "style": "Trench Coat", "color": "#ed4545", "styleIndex": 6, "colorIndex": 2}'::jsonb),
('tops','Trench Coat / 4',80,'procedural:tops-6-3','procedural','{"key": "tops-6-3", "style": "Trench Coat", "color": "#3689ed", "styleIndex": 6, "colorIndex": 3}'::jsonb),
('tops','Trench Coat / 5',65,'procedural:tops-6-4','procedural','{"key": "tops-6-4", "style": "Trench Coat", "color": "#37bf83", "styleIndex": 6, "colorIndex": 4}'::jsonb),
('tops','Trench Coat / 6',70,'procedural:tops-6-5','procedural','{"key": "tops-6-5", "style": "Trench Coat", "color": "#f4c542", "styleIndex": 6, "colorIndex": 5}'::jsonb),
('tops','Trench Coat / 7',75,'procedural:tops-6-6','procedural','{"key": "tops-6-6", "style": "Trench Coat", "color": "#9b62d9", "styleIndex": 6, "colorIndex": 6}'::jsonb),
('tops','Trench Coat / 8',80,'procedural:tops-6-7','procedural','{"key": "tops-6-7", "style": "Trench Coat", "color": "#ef88c0", "styleIndex": 6, "colorIndex": 7}'::jsonb),
('tops','Trench Coat / 9',65,'procedural:tops-6-8','procedural','{"key": "tops-6-8", "style": "Trench Coat", "color": "#ed8838", "styleIndex": 6, "colorIndex": 8}'::jsonb),
('tops','Trench Coat / 10',70,'procedural:tops-6-9','procedural','{"key": "tops-6-9", "style": "Trench Coat", "color": "#6b4b35", "styleIndex": 6, "colorIndex": 9}'::jsonb),
('tops','Trench Coat / 11',75,'procedural:tops-6-10','procedural','{"key": "tops-6-10", "style": "Trench Coat", "color": "#42d8d0", "styleIndex": 6, "colorIndex": 10}'::jsonb),
('tops','Trench Coat / 12',80,'procedural:tops-6-11','procedural','{"key": "tops-6-11", "style": "Trench Coat", "color": "#a5abb8", "styleIndex": 6, "colorIndex": 11}'::jsonb),
('tops','Sweater / 1',85,'procedural:tops-7-0','procedural','{"key": "tops-7-0", "style": "Sweater", "color": "#e6e6e6", "styleIndex": 7, "colorIndex": 0}'::jsonb),
('tops','Sweater / 2',90,'procedural:tops-7-1','procedural','{"key": "tops-7-1", "style": "Sweater", "color": "#181818", "styleIndex": 7, "colorIndex": 1}'::jsonb),
('tops','Sweater / 3',95,'procedural:tops-7-2','procedural','{"key": "tops-7-2", "style": "Sweater", "color": "#ed4545", "styleIndex": 7, "colorIndex": 2}'::jsonb),
('tops','Sweater / 4',100,'procedural:tops-7-3','procedural','{"key": "tops-7-3", "style": "Sweater", "color": "#3689ed", "styleIndex": 7, "colorIndex": 3}'::jsonb),
('tops','Sweater / 5',85,'procedural:tops-7-4','procedural','{"key": "tops-7-4", "style": "Sweater", "color": "#37bf83", "styleIndex": 7, "colorIndex": 4}'::jsonb),
('tops','Sweater / 6',90,'procedural:tops-7-5','procedural','{"key": "tops-7-5", "style": "Sweater", "color": "#f4c542", "styleIndex": 7, "colorIndex": 5}'::jsonb),
('tops','Sweater / 7',95,'procedural:tops-7-6','procedural','{"key": "tops-7-6", "style": "Sweater", "color": "#9b62d9", "styleIndex": 7, "colorIndex": 6}'::jsonb),
('tops','Sweater / 8',100,'procedural:tops-7-7','procedural','{"key": "tops-7-7", "style": "Sweater", "color": "#ef88c0", "styleIndex": 7, "colorIndex": 7}'::jsonb),
('tops','Sweater / 9',85,'procedural:tops-7-8','procedural','{"key": "tops-7-8", "style": "Sweater", "color": "#ed8838", "styleIndex": 7, "colorIndex": 8}'::jsonb),
('tops','Sweater / 10',90,'procedural:tops-7-9','procedural','{"key": "tops-7-9", "style": "Sweater", "color": "#6b4b35", "styleIndex": 7, "colorIndex": 9}'::jsonb),
('tops','Sweater / 11',95,'procedural:tops-7-10','procedural','{"key": "tops-7-10", "style": "Sweater", "color": "#42d8d0", "styleIndex": 7, "colorIndex": 10}'::jsonb),
('tops','Sweater / 12',100,'procedural:tops-7-11','procedural','{"key": "tops-7-11", "style": "Sweater", "color": "#a5abb8", "styleIndex": 7, "colorIndex": 11}'::jsonb),
('tops','Jacket / 1',105,'procedural:tops-8-0','procedural','{"key": "tops-8-0", "style": "Jacket", "color": "#e6e6e6", "styleIndex": 8, "colorIndex": 0}'::jsonb),
('tops','Jacket / 2',110,'procedural:tops-8-1','procedural','{"key": "tops-8-1", "style": "Jacket", "color": "#181818", "styleIndex": 8, "colorIndex": 1}'::jsonb),
('tops','Jacket / 3',115,'procedural:tops-8-2','procedural','{"key": "tops-8-2", "style": "Jacket", "color": "#ed4545", "styleIndex": 8, "colorIndex": 2}'::jsonb),
('tops','Jacket / 4',120,'procedural:tops-8-3','procedural','{"key": "tops-8-3", "style": "Jacket", "color": "#3689ed", "styleIndex": 8, "colorIndex": 3}'::jsonb),
('tops','Jacket / 5',105,'procedural:tops-8-4','procedural','{"key": "tops-8-4", "style": "Jacket", "color": "#37bf83", "styleIndex": 8, "colorIndex": 4}'::jsonb),
('tops','Jacket / 6',110,'procedural:tops-8-5','procedural','{"key": "tops-8-5", "style": "Jacket", "color": "#f4c542", "styleIndex": 8, "colorIndex": 5}'::jsonb),
('tops','Jacket / 7',115,'procedural:tops-8-6','procedural','{"key": "tops-8-6", "style": "Jacket", "color": "#9b62d9", "styleIndex": 8, "colorIndex": 6}'::jsonb),
('tops','Jacket / 8',120,'procedural:tops-8-7','procedural','{"key": "tops-8-7", "style": "Jacket", "color": "#ef88c0", "styleIndex": 8, "colorIndex": 7}'::jsonb),
('tops','Jacket / 9',105,'procedural:tops-8-8','procedural','{"key": "tops-8-8", "style": "Jacket", "color": "#ed8838", "styleIndex": 8, "colorIndex": 8}'::jsonb),
('tops','Jacket / 10',110,'procedural:tops-8-9','procedural','{"key": "tops-8-9", "style": "Jacket", "color": "#6b4b35", "styleIndex": 8, "colorIndex": 9}'::jsonb),
('tops','Jacket / 11',115,'procedural:tops-8-10','procedural','{"key": "tops-8-10", "style": "Jacket", "color": "#42d8d0", "styleIndex": 8, "colorIndex": 10}'::jsonb),
('tops','Jacket / 12',120,'procedural:tops-8-11','procedural','{"key": "tops-8-11", "style": "Jacket", "color": "#a5abb8", "styleIndex": 8, "colorIndex": 11}'::jsonb),
('tops','Polo / 1',125,'procedural:tops-9-0','procedural','{"key": "tops-9-0", "style": "Polo", "color": "#e6e6e6", "styleIndex": 9, "colorIndex": 0}'::jsonb),
('tops','Polo / 2',130,'procedural:tops-9-1','procedural','{"key": "tops-9-1", "style": "Polo", "color": "#181818", "styleIndex": 9, "colorIndex": 1}'::jsonb),
('tops','Polo / 3',135,'procedural:tops-9-2','procedural','{"key": "tops-9-2", "style": "Polo", "color": "#ed4545", "styleIndex": 9, "colorIndex": 2}'::jsonb),
('tops','Polo / 4',140,'procedural:tops-9-3','procedural','{"key": "tops-9-3", "style": "Polo", "color": "#3689ed", "styleIndex": 9, "colorIndex": 3}'::jsonb),
('tops','Polo / 5',125,'procedural:tops-9-4','procedural','{"key": "tops-9-4", "style": "Polo", "color": "#37bf83", "styleIndex": 9, "colorIndex": 4}'::jsonb),
('tops','Polo / 6',130,'procedural:tops-9-5','procedural','{"key": "tops-9-5", "style": "Polo", "color": "#f4c542", "styleIndex": 9, "colorIndex": 5}'::jsonb),
('tops','Polo / 7',135,'procedural:tops-9-6','procedural','{"key": "tops-9-6", "style": "Polo", "color": "#9b62d9", "styleIndex": 9, "colorIndex": 6}'::jsonb),
('tops','Polo / 8',140,'procedural:tops-9-7','procedural','{"key": "tops-9-7", "style": "Polo", "color": "#ef88c0", "styleIndex": 9, "colorIndex": 7}'::jsonb),
('tops','Polo / 9',125,'procedural:tops-9-8','procedural','{"key": "tops-9-8", "style": "Polo", "color": "#ed8838", "styleIndex": 9, "colorIndex": 8}'::jsonb),
('tops','Polo / 10',130,'procedural:tops-9-9','procedural','{"key": "tops-9-9", "style": "Polo", "color": "#6b4b35", "styleIndex": 9, "colorIndex": 9}'::jsonb),
('tops','Polo / 11',135,'procedural:tops-9-10','procedural','{"key": "tops-9-10", "style": "Polo", "color": "#42d8d0", "styleIndex": 9, "colorIndex": 10}'::jsonb),
('tops','Polo / 12',140,'procedural:tops-9-11','procedural','{"key": "tops-9-11", "style": "Polo", "color": "#a5abb8", "styleIndex": 9, "colorIndex": 11}'::jsonb),
('bottoms','Jeans / 1',45,'procedural:bottoms-0-0','procedural','{"key": "bottoms-0-0", "style": "Jeans", "color": "#e6e6e6", "styleIndex": 0, "colorIndex": 0}'::jsonb),
('bottoms','Jeans / 2',50,'procedural:bottoms-0-1','procedural','{"key": "bottoms-0-1", "style": "Jeans", "color": "#181818", "styleIndex": 0, "colorIndex": 1}'::jsonb),
('bottoms','Jeans / 3',55,'procedural:bottoms-0-2','procedural','{"key": "bottoms-0-2", "style": "Jeans", "color": "#ed4545", "styleIndex": 0, "colorIndex": 2}'::jsonb),
('bottoms','Jeans / 4',60,'procedural:bottoms-0-3','procedural','{"key": "bottoms-0-3", "style": "Jeans", "color": "#3689ed", "styleIndex": 0, "colorIndex": 3}'::jsonb),
('bottoms','Jeans / 5',45,'procedural:bottoms-0-4','procedural','{"key": "bottoms-0-4", "style": "Jeans", "color": "#37bf83", "styleIndex": 0, "colorIndex": 4}'::jsonb),
('bottoms','Jeans / 6',50,'procedural:bottoms-0-5','procedural','{"key": "bottoms-0-5", "style": "Jeans", "color": "#f4c542", "styleIndex": 0, "colorIndex": 5}'::jsonb),
('bottoms','Jeans / 7',55,'procedural:bottoms-0-6','procedural','{"key": "bottoms-0-6", "style": "Jeans", "color": "#9b62d9", "styleIndex": 0, "colorIndex": 6}'::jsonb),
('bottoms','Jeans / 8',60,'procedural:bottoms-0-7','procedural','{"key": "bottoms-0-7", "style": "Jeans", "color": "#ef88c0", "styleIndex": 0, "colorIndex": 7}'::jsonb),
('bottoms','Jeans / 9',45,'procedural:bottoms-0-8','procedural','{"key": "bottoms-0-8", "style": "Jeans", "color": "#ed8838", "styleIndex": 0, "colorIndex": 8}'::jsonb),
('bottoms','Jeans / 10',50,'procedural:bottoms-0-9','procedural','{"key": "bottoms-0-9", "style": "Jeans", "color": "#6b4b35", "styleIndex": 0, "colorIndex": 9}'::jsonb),
('bottoms','Jeans / 11',55,'procedural:bottoms-0-10','procedural','{"key": "bottoms-0-10", "style": "Jeans", "color": "#42d8d0", "styleIndex": 0, "colorIndex": 10}'::jsonb),
('bottoms','Jeans / 12',60,'procedural:bottoms-0-11','procedural','{"key": "bottoms-0-11", "style": "Jeans", "color": "#a5abb8", "styleIndex": 0, "colorIndex": 11}'::jsonb),
('bottoms','Shorts / 1',65,'procedural:bottoms-1-0','procedural','{"key": "bottoms-1-0", "style": "Shorts", "color": "#e6e6e6", "styleIndex": 1, "colorIndex": 0}'::jsonb),
('bottoms','Shorts / 2',70,'procedural:bottoms-1-1','procedural','{"key": "bottoms-1-1", "style": "Shorts", "color": "#181818", "styleIndex": 1, "colorIndex": 1}'::jsonb),
('bottoms','Shorts / 3',75,'procedural:bottoms-1-2','procedural','{"key": "bottoms-1-2", "style": "Shorts", "color": "#ed4545", "styleIndex": 1, "colorIndex": 2}'::jsonb),
('bottoms','Shorts / 4',80,'procedural:bottoms-1-3','procedural','{"key": "bottoms-1-3", "style": "Shorts", "color": "#3689ed", "styleIndex": 1, "colorIndex": 3}'::jsonb),
('bottoms','Shorts / 5',65,'procedural:bottoms-1-4','procedural','{"key": "bottoms-1-4", "style": "Shorts", "color": "#37bf83", "styleIndex": 1, "colorIndex": 4}'::jsonb),
('bottoms','Shorts / 6',70,'procedural:bottoms-1-5','procedural','{"key": "bottoms-1-5", "style": "Shorts", "color": "#f4c542", "styleIndex": 1, "colorIndex": 5}'::jsonb),
('bottoms','Shorts / 7',75,'procedural:bottoms-1-6','procedural','{"key": "bottoms-1-6", "style": "Shorts", "color": "#9b62d9", "styleIndex": 1, "colorIndex": 6}'::jsonb),
('bottoms','Shorts / 8',80,'procedural:bottoms-1-7','procedural','{"key": "bottoms-1-7", "style": "Shorts", "color": "#ef88c0", "styleIndex": 1, "colorIndex": 7}'::jsonb),
('bottoms','Shorts / 9',65,'procedural:bottoms-1-8','procedural','{"key": "bottoms-1-8", "style": "Shorts", "color": "#ed8838", "styleIndex": 1, "colorIndex": 8}'::jsonb),
('bottoms','Shorts / 10',70,'procedural:bottoms-1-9','procedural','{"key": "bottoms-1-9", "style": "Shorts", "color": "#6b4b35", "styleIndex": 1, "colorIndex": 9}'::jsonb),
('bottoms','Shorts / 11',75,'procedural:bottoms-1-10','procedural','{"key": "bottoms-1-10", "style": "Shorts", "color": "#42d8d0", "styleIndex": 1, "colorIndex": 10}'::jsonb),
('bottoms','Shorts / 12',80,'procedural:bottoms-1-11','procedural','{"key": "bottoms-1-11", "style": "Shorts", "color": "#a5abb8", "styleIndex": 1, "colorIndex": 11}'::jsonb),
('bottoms','Short Shorts / 1',85,'procedural:bottoms-2-0','procedural','{"key": "bottoms-2-0", "style": "Short Shorts", "color": "#e6e6e6", "styleIndex": 2, "colorIndex": 0}'::jsonb),
('bottoms','Short Shorts / 2',90,'procedural:bottoms-2-1','procedural','{"key": "bottoms-2-1", "style": "Short Shorts", "color": "#181818", "styleIndex": 2, "colorIndex": 1}'::jsonb),
('bottoms','Short Shorts / 3',95,'procedural:bottoms-2-2','procedural','{"key": "bottoms-2-2", "style": "Short Shorts", "color": "#ed4545", "styleIndex": 2, "colorIndex": 2}'::jsonb),
('bottoms','Short Shorts / 4',100,'procedural:bottoms-2-3','procedural','{"key": "bottoms-2-3", "style": "Short Shorts", "color": "#3689ed", "styleIndex": 2, "colorIndex": 3}'::jsonb),
('bottoms','Short Shorts / 5',85,'procedural:bottoms-2-4','procedural','{"key": "bottoms-2-4", "style": "Short Shorts", "color": "#37bf83", "styleIndex": 2, "colorIndex": 4}'::jsonb),
('bottoms','Short Shorts / 6',90,'procedural:bottoms-2-5','procedural','{"key": "bottoms-2-5", "style": "Short Shorts", "color": "#f4c542", "styleIndex": 2, "colorIndex": 5}'::jsonb),
('bottoms','Short Shorts / 7',95,'procedural:bottoms-2-6','procedural','{"key": "bottoms-2-6", "style": "Short Shorts", "color": "#9b62d9", "styleIndex": 2, "colorIndex": 6}'::jsonb),
('bottoms','Short Shorts / 8',100,'procedural:bottoms-2-7','procedural','{"key": "bottoms-2-7", "style": "Short Shorts", "color": "#ef88c0", "styleIndex": 2, "colorIndex": 7}'::jsonb),
('bottoms','Short Shorts / 9',85,'procedural:bottoms-2-8','procedural','{"key": "bottoms-2-8", "style": "Short Shorts", "color": "#ed8838", "styleIndex": 2, "colorIndex": 8}'::jsonb),
('bottoms','Short Shorts / 10',90,'procedural:bottoms-2-9','procedural','{"key": "bottoms-2-9", "style": "Short Shorts", "color": "#6b4b35", "styleIndex": 2, "colorIndex": 9}'::jsonb),
('bottoms','Short Shorts / 11',95,'procedural:bottoms-2-10','procedural','{"key": "bottoms-2-10", "style": "Short Shorts", "color": "#42d8d0", "styleIndex": 2, "colorIndex": 10}'::jsonb),
('bottoms','Short Shorts / 12',100,'procedural:bottoms-2-11','procedural','{"key": "bottoms-2-11", "style": "Short Shorts", "color": "#a5abb8", "styleIndex": 2, "colorIndex": 11}'::jsonb),
('bottoms','Skirt / 1',105,'procedural:bottoms-3-0','procedural','{"key": "bottoms-3-0", "style": "Skirt", "color": "#e6e6e6", "styleIndex": 3, "colorIndex": 0}'::jsonb),
('bottoms','Skirt / 2',110,'procedural:bottoms-3-1','procedural','{"key": "bottoms-3-1", "style": "Skirt", "color": "#181818", "styleIndex": 3, "colorIndex": 1}'::jsonb),
('bottoms','Skirt / 3',115,'procedural:bottoms-3-2','procedural','{"key": "bottoms-3-2", "style": "Skirt", "color": "#ed4545", "styleIndex": 3, "colorIndex": 2}'::jsonb) ON CONFLICT (asset_url) WHERE asset_kind='procedural' DO NOTHING;
INSERT INTO store_items(category,name,price,asset_url,asset_kind,metadata) VALUES
('bottoms','Skirt / 4',120,'procedural:bottoms-3-3','procedural','{"key": "bottoms-3-3", "style": "Skirt", "color": "#3689ed", "styleIndex": 3, "colorIndex": 3}'::jsonb),
('bottoms','Skirt / 5',105,'procedural:bottoms-3-4','procedural','{"key": "bottoms-3-4", "style": "Skirt", "color": "#37bf83", "styleIndex": 3, "colorIndex": 4}'::jsonb),
('bottoms','Skirt / 6',110,'procedural:bottoms-3-5','procedural','{"key": "bottoms-3-5", "style": "Skirt", "color": "#f4c542", "styleIndex": 3, "colorIndex": 5}'::jsonb),
('bottoms','Skirt / 7',115,'procedural:bottoms-3-6','procedural','{"key": "bottoms-3-6", "style": "Skirt", "color": "#9b62d9", "styleIndex": 3, "colorIndex": 6}'::jsonb),
('bottoms','Skirt / 8',120,'procedural:bottoms-3-7','procedural','{"key": "bottoms-3-7", "style": "Skirt", "color": "#ef88c0", "styleIndex": 3, "colorIndex": 7}'::jsonb),
('bottoms','Skirt / 9',105,'procedural:bottoms-3-8','procedural','{"key": "bottoms-3-8", "style": "Skirt", "color": "#ed8838", "styleIndex": 3, "colorIndex": 8}'::jsonb),
('bottoms','Skirt / 10',110,'procedural:bottoms-3-9','procedural','{"key": "bottoms-3-9", "style": "Skirt", "color": "#6b4b35", "styleIndex": 3, "colorIndex": 9}'::jsonb),
('bottoms','Skirt / 11',115,'procedural:bottoms-3-10','procedural','{"key": "bottoms-3-10", "style": "Skirt", "color": "#42d8d0", "styleIndex": 3, "colorIndex": 10}'::jsonb),
('bottoms','Skirt / 12',120,'procedural:bottoms-3-11','procedural','{"key": "bottoms-3-11", "style": "Skirt", "color": "#a5abb8", "styleIndex": 3, "colorIndex": 11}'::jsonb),
('bottoms','Miniskirt / 1',125,'procedural:bottoms-4-0','procedural','{"key": "bottoms-4-0", "style": "Miniskirt", "color": "#e6e6e6", "styleIndex": 4, "colorIndex": 0}'::jsonb),
('bottoms','Miniskirt / 2',130,'procedural:bottoms-4-1','procedural','{"key": "bottoms-4-1", "style": "Miniskirt", "color": "#181818", "styleIndex": 4, "colorIndex": 1}'::jsonb),
('bottoms','Miniskirt / 3',135,'procedural:bottoms-4-2','procedural','{"key": "bottoms-4-2", "style": "Miniskirt", "color": "#ed4545", "styleIndex": 4, "colorIndex": 2}'::jsonb),
('bottoms','Miniskirt / 4',140,'procedural:bottoms-4-3','procedural','{"key": "bottoms-4-3", "style": "Miniskirt", "color": "#3689ed", "styleIndex": 4, "colorIndex": 3}'::jsonb),
('bottoms','Miniskirt / 5',125,'procedural:bottoms-4-4','procedural','{"key": "bottoms-4-4", "style": "Miniskirt", "color": "#37bf83", "styleIndex": 4, "colorIndex": 4}'::jsonb),
('bottoms','Miniskirt / 6',130,'procedural:bottoms-4-5','procedural','{"key": "bottoms-4-5", "style": "Miniskirt", "color": "#f4c542", "styleIndex": 4, "colorIndex": 5}'::jsonb),
('bottoms','Miniskirt / 7',135,'procedural:bottoms-4-6','procedural','{"key": "bottoms-4-6", "style": "Miniskirt", "color": "#9b62d9", "styleIndex": 4, "colorIndex": 6}'::jsonb),
('bottoms','Miniskirt / 8',140,'procedural:bottoms-4-7','procedural','{"key": "bottoms-4-7", "style": "Miniskirt", "color": "#ef88c0", "styleIndex": 4, "colorIndex": 7}'::jsonb),
('bottoms','Miniskirt / 9',125,'procedural:bottoms-4-8','procedural','{"key": "bottoms-4-8", "style": "Miniskirt", "color": "#ed8838", "styleIndex": 4, "colorIndex": 8}'::jsonb),
('bottoms','Miniskirt / 10',130,'procedural:bottoms-4-9','procedural','{"key": "bottoms-4-9", "style": "Miniskirt", "color": "#6b4b35", "styleIndex": 4, "colorIndex": 9}'::jsonb),
('bottoms','Miniskirt / 11',135,'procedural:bottoms-4-10','procedural','{"key": "bottoms-4-10", "style": "Miniskirt", "color": "#42d8d0", "styleIndex": 4, "colorIndex": 10}'::jsonb),
('bottoms','Miniskirt / 12',140,'procedural:bottoms-4-11','procedural','{"key": "bottoms-4-11", "style": "Miniskirt", "color": "#a5abb8", "styleIndex": 4, "colorIndex": 11}'::jsonb),
('bottoms','Baggy Sweatpants / 1',45,'procedural:bottoms-5-0','procedural','{"key": "bottoms-5-0", "style": "Baggy Sweatpants", "color": "#e6e6e6", "styleIndex": 5, "colorIndex": 0}'::jsonb),
('bottoms','Baggy Sweatpants / 2',50,'procedural:bottoms-5-1','procedural','{"key": "bottoms-5-1", "style": "Baggy Sweatpants", "color": "#181818", "styleIndex": 5, "colorIndex": 1}'::jsonb),
('bottoms','Baggy Sweatpants / 3',55,'procedural:bottoms-5-2','procedural','{"key": "bottoms-5-2", "style": "Baggy Sweatpants", "color": "#ed4545", "styleIndex": 5, "colorIndex": 2}'::jsonb),
('bottoms','Baggy Sweatpants / 4',60,'procedural:bottoms-5-3','procedural','{"key": "bottoms-5-3", "style": "Baggy Sweatpants", "color": "#3689ed", "styleIndex": 5, "colorIndex": 3}'::jsonb),
('bottoms','Baggy Sweatpants / 5',45,'procedural:bottoms-5-4','procedural','{"key": "bottoms-5-4", "style": "Baggy Sweatpants", "color": "#37bf83", "styleIndex": 5, "colorIndex": 4}'::jsonb),
('bottoms','Baggy Sweatpants / 6',50,'procedural:bottoms-5-5','procedural','{"key": "bottoms-5-5", "style": "Baggy Sweatpants", "color": "#f4c542", "styleIndex": 5, "colorIndex": 5}'::jsonb),
('bottoms','Baggy Sweatpants / 7',55,'procedural:bottoms-5-6','procedural','{"key": "bottoms-5-6", "style": "Baggy Sweatpants", "color": "#9b62d9", "styleIndex": 5, "colorIndex": 6}'::jsonb),
('bottoms','Baggy Sweatpants / 8',60,'procedural:bottoms-5-7','procedural','{"key": "bottoms-5-7", "style": "Baggy Sweatpants", "color": "#ef88c0", "styleIndex": 5, "colorIndex": 7}'::jsonb),
('bottoms','Baggy Sweatpants / 9',45,'procedural:bottoms-5-8','procedural','{"key": "bottoms-5-8", "style": "Baggy Sweatpants", "color": "#ed8838", "styleIndex": 5, "colorIndex": 8}'::jsonb),
('bottoms','Baggy Sweatpants / 10',50,'procedural:bottoms-5-9','procedural','{"key": "bottoms-5-9", "style": "Baggy Sweatpants", "color": "#6b4b35", "styleIndex": 5, "colorIndex": 9}'::jsonb),
('bottoms','Baggy Sweatpants / 11',55,'procedural:bottoms-5-10','procedural','{"key": "bottoms-5-10", "style": "Baggy Sweatpants", "color": "#42d8d0", "styleIndex": 5, "colorIndex": 10}'::jsonb),
('bottoms','Baggy Sweatpants / 12',60,'procedural:bottoms-5-11','procedural','{"key": "bottoms-5-11", "style": "Baggy Sweatpants", "color": "#a5abb8", "styleIndex": 5, "colorIndex": 11}'::jsonb),
('bottoms','Cargo Pants / 1',65,'procedural:bottoms-6-0','procedural','{"key": "bottoms-6-0", "style": "Cargo Pants", "color": "#e6e6e6", "styleIndex": 6, "colorIndex": 0}'::jsonb),
('bottoms','Cargo Pants / 2',70,'procedural:bottoms-6-1','procedural','{"key": "bottoms-6-1", "style": "Cargo Pants", "color": "#181818", "styleIndex": 6, "colorIndex": 1}'::jsonb),
('bottoms','Cargo Pants / 3',75,'procedural:bottoms-6-2','procedural','{"key": "bottoms-6-2", "style": "Cargo Pants", "color": "#ed4545", "styleIndex": 6, "colorIndex": 2}'::jsonb),
('bottoms','Cargo Pants / 4',80,'procedural:bottoms-6-3','procedural','{"key": "bottoms-6-3", "style": "Cargo Pants", "color": "#3689ed", "styleIndex": 6, "colorIndex": 3}'::jsonb),
('bottoms','Cargo Pants / 5',65,'procedural:bottoms-6-4','procedural','{"key": "bottoms-6-4", "style": "Cargo Pants", "color": "#37bf83", "styleIndex": 6, "colorIndex": 4}'::jsonb),
('bottoms','Cargo Pants / 6',70,'procedural:bottoms-6-5','procedural','{"key": "bottoms-6-5", "style": "Cargo Pants", "color": "#f4c542", "styleIndex": 6, "colorIndex": 5}'::jsonb),
('bottoms','Cargo Pants / 7',75,'procedural:bottoms-6-6','procedural','{"key": "bottoms-6-6", "style": "Cargo Pants", "color": "#9b62d9", "styleIndex": 6, "colorIndex": 6}'::jsonb),
('bottoms','Cargo Pants / 8',80,'procedural:bottoms-6-7','procedural','{"key": "bottoms-6-7", "style": "Cargo Pants", "color": "#ef88c0", "styleIndex": 6, "colorIndex": 7}'::jsonb),
('bottoms','Cargo Pants / 9',65,'procedural:bottoms-6-8','procedural','{"key": "bottoms-6-8", "style": "Cargo Pants", "color": "#ed8838", "styleIndex": 6, "colorIndex": 8}'::jsonb),
('bottoms','Cargo Pants / 10',70,'procedural:bottoms-6-9','procedural','{"key": "bottoms-6-9", "style": "Cargo Pants", "color": "#6b4b35", "styleIndex": 6, "colorIndex": 9}'::jsonb),
('bottoms','Cargo Pants / 11',75,'procedural:bottoms-6-10','procedural','{"key": "bottoms-6-10", "style": "Cargo Pants", "color": "#42d8d0", "styleIndex": 6, "colorIndex": 10}'::jsonb),
('bottoms','Cargo Pants / 12',80,'procedural:bottoms-6-11','procedural','{"key": "bottoms-6-11", "style": "Cargo Pants", "color": "#a5abb8", "styleIndex": 6, "colorIndex": 11}'::jsonb),
('bottoms','Flared Pants / 1',85,'procedural:bottoms-7-0','procedural','{"key": "bottoms-7-0", "style": "Flared Pants", "color": "#e6e6e6", "styleIndex": 7, "colorIndex": 0}'::jsonb),
('bottoms','Flared Pants / 2',90,'procedural:bottoms-7-1','procedural','{"key": "bottoms-7-1", "style": "Flared Pants", "color": "#181818", "styleIndex": 7, "colorIndex": 1}'::jsonb),
('bottoms','Flared Pants / 3',95,'procedural:bottoms-7-2','procedural','{"key": "bottoms-7-2", "style": "Flared Pants", "color": "#ed4545", "styleIndex": 7, "colorIndex": 2}'::jsonb),
('bottoms','Flared Pants / 4',100,'procedural:bottoms-7-3','procedural','{"key": "bottoms-7-3", "style": "Flared Pants", "color": "#3689ed", "styleIndex": 7, "colorIndex": 3}'::jsonb),
('bottoms','Flared Pants / 5',85,'procedural:bottoms-7-4','procedural','{"key": "bottoms-7-4", "style": "Flared Pants", "color": "#37bf83", "styleIndex": 7, "colorIndex": 4}'::jsonb),
('bottoms','Flared Pants / 6',90,'procedural:bottoms-7-5','procedural','{"key": "bottoms-7-5", "style": "Flared Pants", "color": "#f4c542", "styleIndex": 7, "colorIndex": 5}'::jsonb),
('bottoms','Flared Pants / 7',95,'procedural:bottoms-7-6','procedural','{"key": "bottoms-7-6", "style": "Flared Pants", "color": "#9b62d9", "styleIndex": 7, "colorIndex": 6}'::jsonb),
('bottoms','Flared Pants / 8',100,'procedural:bottoms-7-7','procedural','{"key": "bottoms-7-7", "style": "Flared Pants", "color": "#ef88c0", "styleIndex": 7, "colorIndex": 7}'::jsonb),
('bottoms','Flared Pants / 9',85,'procedural:bottoms-7-8','procedural','{"key": "bottoms-7-8", "style": "Flared Pants", "color": "#ed8838", "styleIndex": 7, "colorIndex": 8}'::jsonb),
('bottoms','Flared Pants / 10',90,'procedural:bottoms-7-9','procedural','{"key": "bottoms-7-9", "style": "Flared Pants", "color": "#6b4b35", "styleIndex": 7, "colorIndex": 9}'::jsonb),
('bottoms','Flared Pants / 11',95,'procedural:bottoms-7-10','procedural','{"key": "bottoms-7-10", "style": "Flared Pants", "color": "#42d8d0", "styleIndex": 7, "colorIndex": 10}'::jsonb),
('bottoms','Flared Pants / 12',100,'procedural:bottoms-7-11','procedural','{"key": "bottoms-7-11", "style": "Flared Pants", "color": "#a5abb8", "styleIndex": 7, "colorIndex": 11}'::jsonb),
('bottoms','Joggers / 1',105,'procedural:bottoms-8-0','procedural','{"key": "bottoms-8-0", "style": "Joggers", "color": "#e6e6e6", "styleIndex": 8, "colorIndex": 0}'::jsonb),
('bottoms','Joggers / 2',110,'procedural:bottoms-8-1','procedural','{"key": "bottoms-8-1", "style": "Joggers", "color": "#181818", "styleIndex": 8, "colorIndex": 1}'::jsonb),
('bottoms','Joggers / 3',115,'procedural:bottoms-8-2','procedural','{"key": "bottoms-8-2", "style": "Joggers", "color": "#ed4545", "styleIndex": 8, "colorIndex": 2}'::jsonb),
('bottoms','Joggers / 4',120,'procedural:bottoms-8-3','procedural','{"key": "bottoms-8-3", "style": "Joggers", "color": "#3689ed", "styleIndex": 8, "colorIndex": 3}'::jsonb),
('bottoms','Joggers / 5',105,'procedural:bottoms-8-4','procedural','{"key": "bottoms-8-4", "style": "Joggers", "color": "#37bf83", "styleIndex": 8, "colorIndex": 4}'::jsonb),
('bottoms','Joggers / 6',110,'procedural:bottoms-8-5','procedural','{"key": "bottoms-8-5", "style": "Joggers", "color": "#f4c542", "styleIndex": 8, "colorIndex": 5}'::jsonb),
('bottoms','Joggers / 7',115,'procedural:bottoms-8-6','procedural','{"key": "bottoms-8-6", "style": "Joggers", "color": "#9b62d9", "styleIndex": 8, "colorIndex": 6}'::jsonb),
('bottoms','Joggers / 8',120,'procedural:bottoms-8-7','procedural','{"key": "bottoms-8-7", "style": "Joggers", "color": "#ef88c0", "styleIndex": 8, "colorIndex": 7}'::jsonb),
('bottoms','Joggers / 9',105,'procedural:bottoms-8-8','procedural','{"key": "bottoms-8-8", "style": "Joggers", "color": "#ed8838", "styleIndex": 8, "colorIndex": 8}'::jsonb),
('bottoms','Joggers / 10',110,'procedural:bottoms-8-9','procedural','{"key": "bottoms-8-9", "style": "Joggers", "color": "#6b4b35", "styleIndex": 8, "colorIndex": 9}'::jsonb),
('bottoms','Joggers / 11',115,'procedural:bottoms-8-10','procedural','{"key": "bottoms-8-10", "style": "Joggers", "color": "#42d8d0", "styleIndex": 8, "colorIndex": 10}'::jsonb),
('bottoms','Joggers / 12',120,'procedural:bottoms-8-11','procedural','{"key": "bottoms-8-11", "style": "Joggers", "color": "#a5abb8", "styleIndex": 8, "colorIndex": 11}'::jsonb),
('shoes','Sneakers / 1',45,'procedural:shoes-0-0','procedural','{"key": "shoes-0-0", "style": "Sneakers", "color": "#e6e6e6", "styleIndex": 0, "colorIndex": 0}'::jsonb),
('shoes','Sneakers / 2',50,'procedural:shoes-0-1','procedural','{"key": "shoes-0-1", "style": "Sneakers", "color": "#181818", "styleIndex": 0, "colorIndex": 1}'::jsonb),
('shoes','Sneakers / 3',55,'procedural:shoes-0-2','procedural','{"key": "shoes-0-2", "style": "Sneakers", "color": "#ed4545", "styleIndex": 0, "colorIndex": 2}'::jsonb),
('shoes','Sneakers / 4',60,'procedural:shoes-0-3','procedural','{"key": "shoes-0-3", "style": "Sneakers", "color": "#3689ed", "styleIndex": 0, "colorIndex": 3}'::jsonb),
('shoes','Sneakers / 5',45,'procedural:shoes-0-4','procedural','{"key": "shoes-0-4", "style": "Sneakers", "color": "#37bf83", "styleIndex": 0, "colorIndex": 4}'::jsonb),
('shoes','Sneakers / 6',50,'procedural:shoes-0-5','procedural','{"key": "shoes-0-5", "style": "Sneakers", "color": "#f4c542", "styleIndex": 0, "colorIndex": 5}'::jsonb),
('shoes','Sneakers / 7',55,'procedural:shoes-0-6','procedural','{"key": "shoes-0-6", "style": "Sneakers", "color": "#9b62d9", "styleIndex": 0, "colorIndex": 6}'::jsonb),
('shoes','Sneakers / 8',60,'procedural:shoes-0-7','procedural','{"key": "shoes-0-7", "style": "Sneakers", "color": "#ef88c0", "styleIndex": 0, "colorIndex": 7}'::jsonb),
('shoes','Sneakers / 9',45,'procedural:shoes-0-8','procedural','{"key": "shoes-0-8", "style": "Sneakers", "color": "#ed8838", "styleIndex": 0, "colorIndex": 8}'::jsonb),
('shoes','Sneakers / 10',50,'procedural:shoes-0-9','procedural','{"key": "shoes-0-9", "style": "Sneakers", "color": "#6b4b35", "styleIndex": 0, "colorIndex": 9}'::jsonb),
('shoes','Sneakers / 11',55,'procedural:shoes-0-10','procedural','{"key": "shoes-0-10", "style": "Sneakers", "color": "#42d8d0", "styleIndex": 0, "colorIndex": 10}'::jsonb),
('shoes','Sneakers / 12',60,'procedural:shoes-0-11','procedural','{"key": "shoes-0-11", "style": "Sneakers", "color": "#a5abb8", "styleIndex": 0, "colorIndex": 11}'::jsonb),
('shoes','Flip Flops / 1',65,'procedural:shoes-1-0','procedural','{"key": "shoes-1-0", "style": "Flip Flops", "color": "#e6e6e6", "styleIndex": 1, "colorIndex": 0}'::jsonb),
('shoes','Flip Flops / 2',70,'procedural:shoes-1-1','procedural','{"key": "shoes-1-1", "style": "Flip Flops", "color": "#181818", "styleIndex": 1, "colorIndex": 1}'::jsonb),
('shoes','Flip Flops / 3',75,'procedural:shoes-1-2','procedural','{"key": "shoes-1-2", "style": "Flip Flops", "color": "#ed4545", "styleIndex": 1, "colorIndex": 2}'::jsonb),
('shoes','Flip Flops / 4',80,'procedural:shoes-1-3','procedural','{"key": "shoes-1-3", "style": "Flip Flops", "color": "#3689ed", "styleIndex": 1, "colorIndex": 3}'::jsonb),
('shoes','Flip Flops / 5',65,'procedural:shoes-1-4','procedural','{"key": "shoes-1-4", "style": "Flip Flops", "color": "#37bf83", "styleIndex": 1, "colorIndex": 4}'::jsonb),
('shoes','Flip Flops / 6',70,'procedural:shoes-1-5','procedural','{"key": "shoes-1-5", "style": "Flip Flops", "color": "#f4c542", "styleIndex": 1, "colorIndex": 5}'::jsonb),
('shoes','Flip Flops / 7',75,'procedural:shoes-1-6','procedural','{"key": "shoes-1-6", "style": "Flip Flops", "color": "#9b62d9", "styleIndex": 1, "colorIndex": 6}'::jsonb),
('shoes','Flip Flops / 8',80,'procedural:shoes-1-7','procedural','{"key": "shoes-1-7", "style": "Flip Flops", "color": "#ef88c0", "styleIndex": 1, "colorIndex": 7}'::jsonb),
('shoes','Flip Flops / 9',65,'procedural:shoes-1-8','procedural','{"key": "shoes-1-8", "style": "Flip Flops", "color": "#ed8838", "styleIndex": 1, "colorIndex": 8}'::jsonb),
('shoes','Flip Flops / 10',70,'procedural:shoes-1-9','procedural','{"key": "shoes-1-9", "style": "Flip Flops", "color": "#6b4b35", "styleIndex": 1, "colorIndex": 9}'::jsonb),
('shoes','Flip Flops / 11',75,'procedural:shoes-1-10','procedural','{"key": "shoes-1-10", "style": "Flip Flops", "color": "#42d8d0", "styleIndex": 1, "colorIndex": 10}'::jsonb),
('shoes','Flip Flops / 12',80,'procedural:shoes-1-11','procedural','{"key": "shoes-1-11", "style": "Flip Flops", "color": "#a5abb8", "styleIndex": 1, "colorIndex": 11}'::jsonb),
('shoes','Sandals / 1',85,'procedural:shoes-2-0','procedural','{"key": "shoes-2-0", "style": "Sandals", "color": "#e6e6e6", "styleIndex": 2, "colorIndex": 0}'::jsonb),
('shoes','Sandals / 2',90,'procedural:shoes-2-1','procedural','{"key": "shoes-2-1", "style": "Sandals", "color": "#181818", "styleIndex": 2, "colorIndex": 1}'::jsonb),
('shoes','Sandals / 3',95,'procedural:shoes-2-2','procedural','{"key": "shoes-2-2", "style": "Sandals", "color": "#ed4545", "styleIndex": 2, "colorIndex": 2}'::jsonb),
('shoes','Sandals / 4',100,'procedural:shoes-2-3','procedural','{"key": "shoes-2-3", "style": "Sandals", "color": "#3689ed", "styleIndex": 2, "colorIndex": 3}'::jsonb),
('shoes','Sandals / 5',85,'procedural:shoes-2-4','procedural','{"key": "shoes-2-4", "style": "Sandals", "color": "#37bf83", "styleIndex": 2, "colorIndex": 4}'::jsonb),
('shoes','Sandals / 6',90,'procedural:shoes-2-5','procedural','{"key": "shoes-2-5", "style": "Sandals", "color": "#f4c542", "styleIndex": 2, "colorIndex": 5}'::jsonb),
('shoes','Sandals / 7',95,'procedural:shoes-2-6','procedural','{"key": "shoes-2-6", "style": "Sandals", "color": "#9b62d9", "styleIndex": 2, "colorIndex": 6}'::jsonb),
('shoes','Sandals / 8',100,'procedural:shoes-2-7','procedural','{"key": "shoes-2-7", "style": "Sandals", "color": "#ef88c0", "styleIndex": 2, "colorIndex": 7}'::jsonb),
('shoes','Sandals / 9',85,'procedural:shoes-2-8','procedural','{"key": "shoes-2-8", "style": "Sandals", "color": "#ed8838", "styleIndex": 2, "colorIndex": 8}'::jsonb),
('shoes','Sandals / 10',90,'procedural:shoes-2-9','procedural','{"key": "shoes-2-9", "style": "Sandals", "color": "#6b4b35", "styleIndex": 2, "colorIndex": 9}'::jsonb),
('shoes','Sandals / 11',95,'procedural:shoes-2-10','procedural','{"key": "shoes-2-10", "style": "Sandals", "color": "#42d8d0", "styleIndex": 2, "colorIndex": 10}'::jsonb),
('shoes','Sandals / 12',100,'procedural:shoes-2-11','procedural','{"key": "shoes-2-11", "style": "Sandals", "color": "#a5abb8", "styleIndex": 2, "colorIndex": 11}'::jsonb),
('shoes','Converse / 1',105,'procedural:shoes-3-0','procedural','{"key": "shoes-3-0", "style": "Converse", "color": "#e6e6e6", "styleIndex": 3, "colorIndex": 0}'::jsonb),
('shoes','Converse / 2',110,'procedural:shoes-3-1','procedural','{"key": "shoes-3-1", "style": "Converse", "color": "#181818", "styleIndex": 3, "colorIndex": 1}'::jsonb),
('shoes','Converse / 3',115,'procedural:shoes-3-2','procedural','{"key": "shoes-3-2", "style": "Converse", "color": "#ed4545", "styleIndex": 3, "colorIndex": 2}'::jsonb),
('shoes','Converse / 4',120,'procedural:shoes-3-3','procedural','{"key": "shoes-3-3", "style": "Converse", "color": "#3689ed", "styleIndex": 3, "colorIndex": 3}'::jsonb),
('shoes','Converse / 5',105,'procedural:shoes-3-4','procedural','{"key": "shoes-3-4", "style": "Converse", "color": "#37bf83", "styleIndex": 3, "colorIndex": 4}'::jsonb),
('shoes','Converse / 6',110,'procedural:shoes-3-5','procedural','{"key": "shoes-3-5", "style": "Converse", "color": "#f4c542", "styleIndex": 3, "colorIndex": 5}'::jsonb),
('shoes','Converse / 7',115,'procedural:shoes-3-6','procedural','{"key": "shoes-3-6", "style": "Converse", "color": "#9b62d9", "styleIndex": 3, "colorIndex": 6}'::jsonb),
('shoes','Converse / 8',120,'procedural:shoes-3-7','procedural','{"key": "shoes-3-7", "style": "Converse", "color": "#ef88c0", "styleIndex": 3, "colorIndex": 7}'::jsonb),
('shoes','Converse / 9',105,'procedural:shoes-3-8','procedural','{"key": "shoes-3-8", "style": "Converse", "color": "#ed8838", "styleIndex": 3, "colorIndex": 8}'::jsonb),
('shoes','Converse / 10',110,'procedural:shoes-3-9','procedural','{"key": "shoes-3-9", "style": "Converse", "color": "#6b4b35", "styleIndex": 3, "colorIndex": 9}'::jsonb),
('shoes','Converse / 11',115,'procedural:shoes-3-10','procedural','{"key": "shoes-3-10", "style": "Converse", "color": "#42d8d0", "styleIndex": 3, "colorIndex": 10}'::jsonb),
('shoes','Converse / 12',120,'procedural:shoes-3-11','procedural','{"key": "shoes-3-11", "style": "Converse", "color": "#a5abb8", "styleIndex": 3, "colorIndex": 11}'::jsonb),
('shoes','Boots / 1',125,'procedural:shoes-4-0','procedural','{"key": "shoes-4-0", "style": "Boots", "color": "#e6e6e6", "styleIndex": 4, "colorIndex": 0}'::jsonb),
('shoes','Boots / 2',130,'procedural:shoes-4-1','procedural','{"key": "shoes-4-1", "style": "Boots", "color": "#181818", "styleIndex": 4, "colorIndex": 1}'::jsonb),
('shoes','Boots / 3',135,'procedural:shoes-4-2','procedural','{"key": "shoes-4-2", "style": "Boots", "color": "#ed4545", "styleIndex": 4, "colorIndex": 2}'::jsonb) ON CONFLICT (asset_url) WHERE asset_kind='procedural' DO NOTHING;
INSERT INTO store_items(category,name,price,asset_url,asset_kind,metadata) VALUES
('shoes','Boots / 4',140,'procedural:shoes-4-3','procedural','{"key": "shoes-4-3", "style": "Boots", "color": "#3689ed", "styleIndex": 4, "colorIndex": 3}'::jsonb),
('shoes','Boots / 5',125,'procedural:shoes-4-4','procedural','{"key": "shoes-4-4", "style": "Boots", "color": "#37bf83", "styleIndex": 4, "colorIndex": 4}'::jsonb),
('shoes','Boots / 6',130,'procedural:shoes-4-5','procedural','{"key": "shoes-4-5", "style": "Boots", "color": "#f4c542", "styleIndex": 4, "colorIndex": 5}'::jsonb),
('shoes','Boots / 7',135,'procedural:shoes-4-6','procedural','{"key": "shoes-4-6", "style": "Boots", "color": "#9b62d9", "styleIndex": 4, "colorIndex": 6}'::jsonb),
('shoes','Boots / 8',140,'procedural:shoes-4-7','procedural','{"key": "shoes-4-7", "style": "Boots", "color": "#ef88c0", "styleIndex": 4, "colorIndex": 7}'::jsonb),
('shoes','Boots / 9',125,'procedural:shoes-4-8','procedural','{"key": "shoes-4-8", "style": "Boots", "color": "#ed8838", "styleIndex": 4, "colorIndex": 8}'::jsonb),
('shoes','Boots / 10',130,'procedural:shoes-4-9','procedural','{"key": "shoes-4-9", "style": "Boots", "color": "#6b4b35", "styleIndex": 4, "colorIndex": 9}'::jsonb),
('shoes','Boots / 11',135,'procedural:shoes-4-10','procedural','{"key": "shoes-4-10", "style": "Boots", "color": "#42d8d0", "styleIndex": 4, "colorIndex": 10}'::jsonb),
('shoes','Boots / 12',140,'procedural:shoes-4-11','procedural','{"key": "shoes-4-11", "style": "Boots", "color": "#a5abb8", "styleIndex": 4, "colorIndex": 11}'::jsonb),
('shoes','Slippers / 1',45,'procedural:shoes-5-0','procedural','{"key": "shoes-5-0", "style": "Slippers", "color": "#e6e6e6", "styleIndex": 5, "colorIndex": 0}'::jsonb),
('shoes','Slippers / 2',50,'procedural:shoes-5-1','procedural','{"key": "shoes-5-1", "style": "Slippers", "color": "#181818", "styleIndex": 5, "colorIndex": 1}'::jsonb),
('shoes','Slippers / 3',55,'procedural:shoes-5-2','procedural','{"key": "shoes-5-2", "style": "Slippers", "color": "#ed4545", "styleIndex": 5, "colorIndex": 2}'::jsonb),
('shoes','Slippers / 4',60,'procedural:shoes-5-3','procedural','{"key": "shoes-5-3", "style": "Slippers", "color": "#3689ed", "styleIndex": 5, "colorIndex": 3}'::jsonb),
('shoes','Slippers / 5',45,'procedural:shoes-5-4','procedural','{"key": "shoes-5-4", "style": "Slippers", "color": "#37bf83", "styleIndex": 5, "colorIndex": 4}'::jsonb),
('shoes','Slippers / 6',50,'procedural:shoes-5-5','procedural','{"key": "shoes-5-5", "style": "Slippers", "color": "#f4c542", "styleIndex": 5, "colorIndex": 5}'::jsonb),
('shoes','Slippers / 7',55,'procedural:shoes-5-6','procedural','{"key": "shoes-5-6", "style": "Slippers", "color": "#9b62d9", "styleIndex": 5, "colorIndex": 6}'::jsonb),
('shoes','Slippers / 8',60,'procedural:shoes-5-7','procedural','{"key": "shoes-5-7", "style": "Slippers", "color": "#ef88c0", "styleIndex": 5, "colorIndex": 7}'::jsonb),
('shoes','Slippers / 9',45,'procedural:shoes-5-8','procedural','{"key": "shoes-5-8", "style": "Slippers", "color": "#ed8838", "styleIndex": 5, "colorIndex": 8}'::jsonb),
('shoes','Slippers / 10',50,'procedural:shoes-5-9','procedural','{"key": "shoes-5-9", "style": "Slippers", "color": "#6b4b35", "styleIndex": 5, "colorIndex": 9}'::jsonb),
('shoes','Slippers / 11',55,'procedural:shoes-5-10','procedural','{"key": "shoes-5-10", "style": "Slippers", "color": "#42d8d0", "styleIndex": 5, "colorIndex": 10}'::jsonb),
('shoes','Slippers / 12',60,'procedural:shoes-5-11','procedural','{"key": "shoes-5-11", "style": "Slippers", "color": "#a5abb8", "styleIndex": 5, "colorIndex": 11}'::jsonb),
('shoes','Heels / 1',65,'procedural:shoes-6-0','procedural','{"key": "shoes-6-0", "style": "Heels", "color": "#e6e6e6", "styleIndex": 6, "colorIndex": 0}'::jsonb),
('shoes','Heels / 2',70,'procedural:shoes-6-1','procedural','{"key": "shoes-6-1", "style": "Heels", "color": "#181818", "styleIndex": 6, "colorIndex": 1}'::jsonb),
('shoes','Heels / 3',75,'procedural:shoes-6-2','procedural','{"key": "shoes-6-2", "style": "Heels", "color": "#ed4545", "styleIndex": 6, "colorIndex": 2}'::jsonb),
('shoes','Heels / 4',80,'procedural:shoes-6-3','procedural','{"key": "shoes-6-3", "style": "Heels", "color": "#3689ed", "styleIndex": 6, "colorIndex": 3}'::jsonb),
('shoes','Heels / 5',65,'procedural:shoes-6-4','procedural','{"key": "shoes-6-4", "style": "Heels", "color": "#37bf83", "styleIndex": 6, "colorIndex": 4}'::jsonb),
('shoes','Heels / 6',70,'procedural:shoes-6-5','procedural','{"key": "shoes-6-5", "style": "Heels", "color": "#f4c542", "styleIndex": 6, "colorIndex": 5}'::jsonb),
('shoes','Heels / 7',75,'procedural:shoes-6-6','procedural','{"key": "shoes-6-6", "style": "Heels", "color": "#9b62d9", "styleIndex": 6, "colorIndex": 6}'::jsonb),
('shoes','Heels / 8',80,'procedural:shoes-6-7','procedural','{"key": "shoes-6-7", "style": "Heels", "color": "#ef88c0", "styleIndex": 6, "colorIndex": 7}'::jsonb),
('shoes','Heels / 9',65,'procedural:shoes-6-8','procedural','{"key": "shoes-6-8", "style": "Heels", "color": "#ed8838", "styleIndex": 6, "colorIndex": 8}'::jsonb),
('shoes','Heels / 10',70,'procedural:shoes-6-9','procedural','{"key": "shoes-6-9", "style": "Heels", "color": "#6b4b35", "styleIndex": 6, "colorIndex": 9}'::jsonb),
('shoes','Heels / 11',75,'procedural:shoes-6-10','procedural','{"key": "shoes-6-10", "style": "Heels", "color": "#42d8d0", "styleIndex": 6, "colorIndex": 10}'::jsonb),
('shoes','Heels / 12',80,'procedural:shoes-6-11','procedural','{"key": "shoes-6-11", "style": "Heels", "color": "#a5abb8", "styleIndex": 6, "colorIndex": 11}'::jsonb),
('shoes','High Tops / 1',85,'procedural:shoes-7-0','procedural','{"key": "shoes-7-0", "style": "High Tops", "color": "#e6e6e6", "styleIndex": 7, "colorIndex": 0}'::jsonb),
('shoes','High Tops / 2',90,'procedural:shoes-7-1','procedural','{"key": "shoes-7-1", "style": "High Tops", "color": "#181818", "styleIndex": 7, "colorIndex": 1}'::jsonb),
('shoes','High Tops / 3',95,'procedural:shoes-7-2','procedural','{"key": "shoes-7-2", "style": "High Tops", "color": "#ed4545", "styleIndex": 7, "colorIndex": 2}'::jsonb),
('shoes','High Tops / 4',100,'procedural:shoes-7-3','procedural','{"key": "shoes-7-3", "style": "High Tops", "color": "#3689ed", "styleIndex": 7, "colorIndex": 3}'::jsonb),
('shoes','High Tops / 5',85,'procedural:shoes-7-4','procedural','{"key": "shoes-7-4", "style": "High Tops", "color": "#37bf83", "styleIndex": 7, "colorIndex": 4}'::jsonb),
('shoes','High Tops / 6',90,'procedural:shoes-7-5','procedural','{"key": "shoes-7-5", "style": "High Tops", "color": "#f4c542", "styleIndex": 7, "colorIndex": 5}'::jsonb),
('shoes','High Tops / 7',95,'procedural:shoes-7-6','procedural','{"key": "shoes-7-6", "style": "High Tops", "color": "#9b62d9", "styleIndex": 7, "colorIndex": 6}'::jsonb),
('shoes','High Tops / 8',100,'procedural:shoes-7-7','procedural','{"key": "shoes-7-7", "style": "High Tops", "color": "#ef88c0", "styleIndex": 7, "colorIndex": 7}'::jsonb),
('shoes','High Tops / 9',85,'procedural:shoes-7-8','procedural','{"key": "shoes-7-8", "style": "High Tops", "color": "#ed8838", "styleIndex": 7, "colorIndex": 8}'::jsonb),
('shoes','High Tops / 10',90,'procedural:shoes-7-9','procedural','{"key": "shoes-7-9", "style": "High Tops", "color": "#6b4b35", "styleIndex": 7, "colorIndex": 9}'::jsonb),
('shoes','High Tops / 11',95,'procedural:shoes-7-10','procedural','{"key": "shoes-7-10", "style": "High Tops", "color": "#42d8d0", "styleIndex": 7, "colorIndex": 10}'::jsonb),
('shoes','High Tops / 12',100,'procedural:shoes-7-11','procedural','{"key": "shoes-7-11", "style": "High Tops", "color": "#a5abb8", "styleIndex": 7, "colorIndex": 11}'::jsonb),
('shoes','Loafers / 1',105,'procedural:shoes-8-0','procedural','{"key": "shoes-8-0", "style": "Loafers", "color": "#e6e6e6", "styleIndex": 8, "colorIndex": 0}'::jsonb),
('shoes','Loafers / 2',110,'procedural:shoes-8-1','procedural','{"key": "shoes-8-1", "style": "Loafers", "color": "#181818", "styleIndex": 8, "colorIndex": 1}'::jsonb),
('shoes','Loafers / 3',115,'procedural:shoes-8-2','procedural','{"key": "shoes-8-2", "style": "Loafers", "color": "#ed4545", "styleIndex": 8, "colorIndex": 2}'::jsonb),
('shoes','Loafers / 4',120,'procedural:shoes-8-3','procedural','{"key": "shoes-8-3", "style": "Loafers", "color": "#3689ed", "styleIndex": 8, "colorIndex": 3}'::jsonb),
('shoes','Loafers / 5',105,'procedural:shoes-8-4','procedural','{"key": "shoes-8-4", "style": "Loafers", "color": "#37bf83", "styleIndex": 8, "colorIndex": 4}'::jsonb),
('shoes','Loafers / 6',110,'procedural:shoes-8-5','procedural','{"key": "shoes-8-5", "style": "Loafers", "color": "#f4c542", "styleIndex": 8, "colorIndex": 5}'::jsonb),
('shoes','Loafers / 7',115,'procedural:shoes-8-6','procedural','{"key": "shoes-8-6", "style": "Loafers", "color": "#9b62d9", "styleIndex": 8, "colorIndex": 6}'::jsonb),
('shoes','Loafers / 8',120,'procedural:shoes-8-7','procedural','{"key": "shoes-8-7", "style": "Loafers", "color": "#ef88c0", "styleIndex": 8, "colorIndex": 7}'::jsonb),
('shoes','Loafers / 9',105,'procedural:shoes-8-8','procedural','{"key": "shoes-8-8", "style": "Loafers", "color": "#ed8838", "styleIndex": 8, "colorIndex": 8}'::jsonb),
('shoes','Loafers / 10',110,'procedural:shoes-8-9','procedural','{"key": "shoes-8-9", "style": "Loafers", "color": "#6b4b35", "styleIndex": 8, "colorIndex": 9}'::jsonb),
('shoes','Loafers / 11',115,'procedural:shoes-8-10','procedural','{"key": "shoes-8-10", "style": "Loafers", "color": "#42d8d0", "styleIndex": 8, "colorIndex": 10}'::jsonb),
('shoes','Loafers / 12',120,'procedural:shoes-8-11','procedural','{"key": "shoes-8-11", "style": "Loafers", "color": "#a5abb8", "styleIndex": 8, "colorIndex": 11}'::jsonb),
('flightsuits','Classic / 2',140,'procedural:flightsuits-0-1','procedural','{"key": "flightsuits-0-1", "style": "Classic", "color": "#181818", "styleIndex": 0, "colorIndex": 1}'::jsonb),
('flightsuits','Classic / 3',145,'procedural:flightsuits-0-2','procedural','{"key": "flightsuits-0-2", "style": "Classic", "color": "#ed4545", "styleIndex": 0, "colorIndex": 2}'::jsonb),
('flightsuits','Classic / 4',150,'procedural:flightsuits-0-3','procedural','{"key": "flightsuits-0-3", "style": "Classic", "color": "#3689ed", "styleIndex": 0, "colorIndex": 3}'::jsonb),
('flightsuits','Classic / 5',135,'procedural:flightsuits-0-4','procedural','{"key": "flightsuits-0-4", "style": "Classic", "color": "#37bf83", "styleIndex": 0, "colorIndex": 4}'::jsonb),
('flightsuits','Classic / 6',140,'procedural:flightsuits-0-5','procedural','{"key": "flightsuits-0-5", "style": "Classic", "color": "#f4c542", "styleIndex": 0, "colorIndex": 5}'::jsonb),
('flightsuits','Classic / 7',145,'procedural:flightsuits-0-6','procedural','{"key": "flightsuits-0-6", "style": "Classic", "color": "#9b62d9", "styleIndex": 0, "colorIndex": 6}'::jsonb),
('flightsuits','Classic / 8',150,'procedural:flightsuits-0-7','procedural','{"key": "flightsuits-0-7", "style": "Classic", "color": "#ef88c0", "styleIndex": 0, "colorIndex": 7}'::jsonb),
('flightsuits','Classic / 9',135,'procedural:flightsuits-0-8','procedural','{"key": "flightsuits-0-8", "style": "Classic", "color": "#ed8838", "styleIndex": 0, "colorIndex": 8}'::jsonb),
('flightsuits','Classic / 10',140,'procedural:flightsuits-0-9','procedural','{"key": "flightsuits-0-9", "style": "Classic", "color": "#6b4b35", "styleIndex": 0, "colorIndex": 9}'::jsonb),
('flightsuits','Classic / 11',145,'procedural:flightsuits-0-10','procedural','{"key": "flightsuits-0-10", "style": "Classic", "color": "#42d8d0", "styleIndex": 0, "colorIndex": 10}'::jsonb),
('flightsuits','Classic / 12',150,'procedural:flightsuits-0-11','procedural','{"key": "flightsuits-0-11", "style": "Classic", "color": "#a5abb8", "styleIndex": 0, "colorIndex": 11}'::jsonb),
('flightsuits','Aero / 1',155,'procedural:flightsuits-1-0','procedural','{"key": "flightsuits-1-0", "style": "Aero", "color": "#e6e6e6", "styleIndex": 1, "colorIndex": 0}'::jsonb),
('flightsuits','Aero / 2',160,'procedural:flightsuits-1-1','procedural','{"key": "flightsuits-1-1", "style": "Aero", "color": "#181818", "styleIndex": 1, "colorIndex": 1}'::jsonb),
('flightsuits','Aero / 3',165,'procedural:flightsuits-1-2','procedural','{"key": "flightsuits-1-2", "style": "Aero", "color": "#ed4545", "styleIndex": 1, "colorIndex": 2}'::jsonb),
('flightsuits','Aero / 4',170,'procedural:flightsuits-1-3','procedural','{"key": "flightsuits-1-3", "style": "Aero", "color": "#3689ed", "styleIndex": 1, "colorIndex": 3}'::jsonb),
('flightsuits','Aero / 5',155,'procedural:flightsuits-1-4','procedural','{"key": "flightsuits-1-4", "style": "Aero", "color": "#37bf83", "styleIndex": 1, "colorIndex": 4}'::jsonb),
('flightsuits','Aero / 6',160,'procedural:flightsuits-1-5','procedural','{"key": "flightsuits-1-5", "style": "Aero", "color": "#f4c542", "styleIndex": 1, "colorIndex": 5}'::jsonb),
('flightsuits','Aero / 7',165,'procedural:flightsuits-1-6','procedural','{"key": "flightsuits-1-6", "style": "Aero", "color": "#9b62d9", "styleIndex": 1, "colorIndex": 6}'::jsonb),
('flightsuits','Aero / 8',170,'procedural:flightsuits-1-7','procedural','{"key": "flightsuits-1-7", "style": "Aero", "color": "#ef88c0", "styleIndex": 1, "colorIndex": 7}'::jsonb),
('flightsuits','Aero / 9',155,'procedural:flightsuits-1-8','procedural','{"key": "flightsuits-1-8", "style": "Aero", "color": "#ed8838", "styleIndex": 1, "colorIndex": 8}'::jsonb),
('flightsuits','Aero / 10',160,'procedural:flightsuits-1-9','procedural','{"key": "flightsuits-1-9", "style": "Aero", "color": "#6b4b35", "styleIndex": 1, "colorIndex": 9}'::jsonb),
('flightsuits','Aero / 11',165,'procedural:flightsuits-1-10','procedural','{"key": "flightsuits-1-10", "style": "Aero", "color": "#42d8d0", "styleIndex": 1, "colorIndex": 10}'::jsonb),
('flightsuits','Aero / 12',170,'procedural:flightsuits-1-11','procedural','{"key": "flightsuits-1-11", "style": "Aero", "color": "#a5abb8", "styleIndex": 1, "colorIndex": 11}'::jsonb),
('flightsuits','Racer / 1',175,'procedural:flightsuits-2-0','procedural','{"key": "flightsuits-2-0", "style": "Racer", "color": "#e6e6e6", "styleIndex": 2, "colorIndex": 0}'::jsonb),
('flightsuits','Racer / 2',180,'procedural:flightsuits-2-1','procedural','{"key": "flightsuits-2-1", "style": "Racer", "color": "#181818", "styleIndex": 2, "colorIndex": 1}'::jsonb),
('flightsuits','Racer / 3',185,'procedural:flightsuits-2-2','procedural','{"key": "flightsuits-2-2", "style": "Racer", "color": "#ed4545", "styleIndex": 2, "colorIndex": 2}'::jsonb),
('flightsuits','Racer / 4',190,'procedural:flightsuits-2-3','procedural','{"key": "flightsuits-2-3", "style": "Racer", "color": "#3689ed", "styleIndex": 2, "colorIndex": 3}'::jsonb),
('flightsuits','Racer / 5',175,'procedural:flightsuits-2-4','procedural','{"key": "flightsuits-2-4", "style": "Racer", "color": "#37bf83", "styleIndex": 2, "colorIndex": 4}'::jsonb),
('flightsuits','Racer / 6',180,'procedural:flightsuits-2-5','procedural','{"key": "flightsuits-2-5", "style": "Racer", "color": "#f4c542", "styleIndex": 2, "colorIndex": 5}'::jsonb),
('flightsuits','Racer / 7',185,'procedural:flightsuits-2-6','procedural','{"key": "flightsuits-2-6", "style": "Racer", "color": "#9b62d9", "styleIndex": 2, "colorIndex": 6}'::jsonb),
('flightsuits','Racer / 8',190,'procedural:flightsuits-2-7','procedural','{"key": "flightsuits-2-7", "style": "Racer", "color": "#ef88c0", "styleIndex": 2, "colorIndex": 7}'::jsonb),
('flightsuits','Racer / 9',175,'procedural:flightsuits-2-8','procedural','{"key": "flightsuits-2-8", "style": "Racer", "color": "#ed8838", "styleIndex": 2, "colorIndex": 8}'::jsonb),
('flightsuits','Racer / 10',180,'procedural:flightsuits-2-9','procedural','{"key": "flightsuits-2-9", "style": "Racer", "color": "#6b4b35", "styleIndex": 2, "colorIndex": 9}'::jsonb),
('flightsuits','Racer / 11',185,'procedural:flightsuits-2-10','procedural','{"key": "flightsuits-2-10", "style": "Racer", "color": "#42d8d0", "styleIndex": 2, "colorIndex": 10}'::jsonb),
('flightsuits','Racer / 12',190,'procedural:flightsuits-2-11','procedural','{"key": "flightsuits-2-11", "style": "Racer", "color": "#a5abb8", "styleIndex": 2, "colorIndex": 11}'::jsonb),
('flightsuits','Winged / 1',195,'procedural:flightsuits-3-0','procedural','{"key": "flightsuits-3-0", "style": "Winged", "color": "#e6e6e6", "styleIndex": 3, "colorIndex": 0}'::jsonb),
('flightsuits','Winged / 2',200,'procedural:flightsuits-3-1','procedural','{"key": "flightsuits-3-1", "style": "Winged", "color": "#181818", "styleIndex": 3, "colorIndex": 1}'::jsonb),
('flightsuits','Winged / 3',205,'procedural:flightsuits-3-2','procedural','{"key": "flightsuits-3-2", "style": "Winged", "color": "#ed4545", "styleIndex": 3, "colorIndex": 2}'::jsonb),
('flightsuits','Winged / 4',210,'procedural:flightsuits-3-3','procedural','{"key": "flightsuits-3-3", "style": "Winged", "color": "#3689ed", "styleIndex": 3, "colorIndex": 3}'::jsonb),
('flightsuits','Winged / 5',195,'procedural:flightsuits-3-4','procedural','{"key": "flightsuits-3-4", "style": "Winged", "color": "#37bf83", "styleIndex": 3, "colorIndex": 4}'::jsonb),
('flightsuits','Winged / 6',200,'procedural:flightsuits-3-5','procedural','{"key": "flightsuits-3-5", "style": "Winged", "color": "#f4c542", "styleIndex": 3, "colorIndex": 5}'::jsonb),
('flightsuits','Winged / 7',205,'procedural:flightsuits-3-6','procedural','{"key": "flightsuits-3-6", "style": "Winged", "color": "#9b62d9", "styleIndex": 3, "colorIndex": 6}'::jsonb),
('flightsuits','Winged / 8',210,'procedural:flightsuits-3-7','procedural','{"key": "flightsuits-3-7", "style": "Winged", "color": "#ef88c0", "styleIndex": 3, "colorIndex": 7}'::jsonb),
('flightsuits','Winged / 9',195,'procedural:flightsuits-3-8','procedural','{"key": "flightsuits-3-8", "style": "Winged", "color": "#ed8838", "styleIndex": 3, "colorIndex": 8}'::jsonb),
('flightsuits','Winged / 10',200,'procedural:flightsuits-3-9','procedural','{"key": "flightsuits-3-9", "style": "Winged", "color": "#6b4b35", "styleIndex": 3, "colorIndex": 9}'::jsonb),
('flightsuits','Winged / 11',205,'procedural:flightsuits-3-10','procedural','{"key": "flightsuits-3-10", "style": "Winged", "color": "#42d8d0", "styleIndex": 3, "colorIndex": 10}'::jsonb),
('flightsuits','Winged / 12',210,'procedural:flightsuits-3-11','procedural','{"key": "flightsuits-3-11", "style": "Winged", "color": "#a5abb8", "styleIndex": 3, "colorIndex": 11}'::jsonb),
('flightsuits','Stealth / 1',215,'procedural:flightsuits-4-0','procedural','{"key": "flightsuits-4-0", "style": "Stealth", "color": "#e6e6e6", "styleIndex": 4, "colorIndex": 0}'::jsonb),
('flightsuits','Stealth / 2',220,'procedural:flightsuits-4-1','procedural','{"key": "flightsuits-4-1", "style": "Stealth", "color": "#181818", "styleIndex": 4, "colorIndex": 1}'::jsonb),
('flightsuits','Stealth / 3',225,'procedural:flightsuits-4-2','procedural','{"key": "flightsuits-4-2", "style": "Stealth", "color": "#ed4545", "styleIndex": 4, "colorIndex": 2}'::jsonb),
('flightsuits','Stealth / 4',230,'procedural:flightsuits-4-3','procedural','{"key": "flightsuits-4-3", "style": "Stealth", "color": "#3689ed", "styleIndex": 4, "colorIndex": 3}'::jsonb),
('flightsuits','Stealth / 5',215,'procedural:flightsuits-4-4','procedural','{"key": "flightsuits-4-4", "style": "Stealth", "color": "#37bf83", "styleIndex": 4, "colorIndex": 4}'::jsonb),
('flightsuits','Stealth / 6',220,'procedural:flightsuits-4-5','procedural','{"key": "flightsuits-4-5", "style": "Stealth", "color": "#f4c542", "styleIndex": 4, "colorIndex": 5}'::jsonb),
('flightsuits','Stealth / 7',225,'procedural:flightsuits-4-6','procedural','{"key": "flightsuits-4-6", "style": "Stealth", "color": "#9b62d9", "styleIndex": 4, "colorIndex": 6}'::jsonb),
('flightsuits','Stealth / 8',230,'procedural:flightsuits-4-7','procedural','{"key": "flightsuits-4-7", "style": "Stealth", "color": "#ef88c0", "styleIndex": 4, "colorIndex": 7}'::jsonb),
('flightsuits','Stealth / 9',215,'procedural:flightsuits-4-8','procedural','{"key": "flightsuits-4-8", "style": "Stealth", "color": "#ed8838", "styleIndex": 4, "colorIndex": 8}'::jsonb),
('flightsuits','Stealth / 10',220,'procedural:flightsuits-4-9','procedural','{"key": "flightsuits-4-9", "style": "Stealth", "color": "#6b4b35", "styleIndex": 4, "colorIndex": 9}'::jsonb),
('flightsuits','Stealth / 11',225,'procedural:flightsuits-4-10','procedural','{"key": "flightsuits-4-10", "style": "Stealth", "color": "#42d8d0", "styleIndex": 4, "colorIndex": 10}'::jsonb),
('flightsuits','Stealth / 12',230,'procedural:flightsuits-4-11','procedural','{"key": "flightsuits-4-11", "style": "Stealth", "color": "#a5abb8", "styleIndex": 4, "colorIndex": 11}'::jsonb),
('flightsuits','Retro / 1',135,'procedural:flightsuits-5-0','procedural','{"key": "flightsuits-5-0", "style": "Retro", "color": "#e6e6e6", "styleIndex": 5, "colorIndex": 0}'::jsonb),
('flightsuits','Retro / 2',140,'procedural:flightsuits-5-1','procedural','{"key": "flightsuits-5-1", "style": "Retro", "color": "#181818", "styleIndex": 5, "colorIndex": 1}'::jsonb),
('flightsuits','Retro / 3',145,'procedural:flightsuits-5-2','procedural','{"key": "flightsuits-5-2", "style": "Retro", "color": "#ed4545", "styleIndex": 5, "colorIndex": 2}'::jsonb),
('flightsuits','Retro / 4',150,'procedural:flightsuits-5-3','procedural','{"key": "flightsuits-5-3", "style": "Retro", "color": "#3689ed", "styleIndex": 5, "colorIndex": 3}'::jsonb) ON CONFLICT (asset_url) WHERE asset_kind='procedural' DO NOTHING;
INSERT INTO store_items(category,name,price,asset_url,asset_kind,metadata) VALUES
('flightsuits','Retro / 5',135,'procedural:flightsuits-5-4','procedural','{"key": "flightsuits-5-4", "style": "Retro", "color": "#37bf83", "styleIndex": 5, "colorIndex": 4}'::jsonb),
('flightsuits','Retro / 6',140,'procedural:flightsuits-5-5','procedural','{"key": "flightsuits-5-5", "style": "Retro", "color": "#f4c542", "styleIndex": 5, "colorIndex": 5}'::jsonb),
('flightsuits','Retro / 7',145,'procedural:flightsuits-5-6','procedural','{"key": "flightsuits-5-6", "style": "Retro", "color": "#9b62d9", "styleIndex": 5, "colorIndex": 6}'::jsonb),
('flightsuits','Retro / 8',150,'procedural:flightsuits-5-7','procedural','{"key": "flightsuits-5-7", "style": "Retro", "color": "#ef88c0", "styleIndex": 5, "colorIndex": 7}'::jsonb),
('flightsuits','Retro / 9',135,'procedural:flightsuits-5-8','procedural','{"key": "flightsuits-5-8", "style": "Retro", "color": "#ed8838", "styleIndex": 5, "colorIndex": 8}'::jsonb),
('flightsuits','Retro / 10',140,'procedural:flightsuits-5-9','procedural','{"key": "flightsuits-5-9", "style": "Retro", "color": "#6b4b35", "styleIndex": 5, "colorIndex": 9}'::jsonb),
('flightsuits','Retro / 11',145,'procedural:flightsuits-5-10','procedural','{"key": "flightsuits-5-10", "style": "Retro", "color": "#42d8d0", "styleIndex": 5, "colorIndex": 10}'::jsonb),
('flightsuits','Retro / 12',150,'procedural:flightsuits-5-11','procedural','{"key": "flightsuits-5-11", "style": "Retro", "color": "#a5abb8", "styleIndex": 5, "colorIndex": 11}'::jsonb),
('flightsuits','Skydiver / 1',155,'procedural:flightsuits-6-0','procedural','{"key": "flightsuits-6-0", "style": "Skydiver", "color": "#e6e6e6", "styleIndex": 6, "colorIndex": 0}'::jsonb),
('flightsuits','Skydiver / 2',160,'procedural:flightsuits-6-1','procedural','{"key": "flightsuits-6-1", "style": "Skydiver", "color": "#181818", "styleIndex": 6, "colorIndex": 1}'::jsonb),
('flightsuits','Skydiver / 3',165,'procedural:flightsuits-6-2','procedural','{"key": "flightsuits-6-2", "style": "Skydiver", "color": "#ed4545", "styleIndex": 6, "colorIndex": 2}'::jsonb),
('flightsuits','Skydiver / 4',170,'procedural:flightsuits-6-3','procedural','{"key": "flightsuits-6-3", "style": "Skydiver", "color": "#3689ed", "styleIndex": 6, "colorIndex": 3}'::jsonb),
('flightsuits','Skydiver / 5',155,'procedural:flightsuits-6-4','procedural','{"key": "flightsuits-6-4", "style": "Skydiver", "color": "#37bf83", "styleIndex": 6, "colorIndex": 4}'::jsonb),
('flightsuits','Skydiver / 6',160,'procedural:flightsuits-6-5','procedural','{"key": "flightsuits-6-5", "style": "Skydiver", "color": "#f4c542", "styleIndex": 6, "colorIndex": 5}'::jsonb),
('flightsuits','Skydiver / 7',165,'procedural:flightsuits-6-6','procedural','{"key": "flightsuits-6-6", "style": "Skydiver", "color": "#9b62d9", "styleIndex": 6, "colorIndex": 6}'::jsonb),
('flightsuits','Skydiver / 8',170,'procedural:flightsuits-6-7','procedural','{"key": "flightsuits-6-7", "style": "Skydiver", "color": "#ef88c0", "styleIndex": 6, "colorIndex": 7}'::jsonb),
('flightsuits','Skydiver / 9',155,'procedural:flightsuits-6-8','procedural','{"key": "flightsuits-6-8", "style": "Skydiver", "color": "#ed8838", "styleIndex": 6, "colorIndex": 8}'::jsonb),
('flightsuits','Skydiver / 10',160,'procedural:flightsuits-6-9','procedural','{"key": "flightsuits-6-9", "style": "Skydiver", "color": "#6b4b35", "styleIndex": 6, "colorIndex": 9}'::jsonb),
('flightsuits','Skydiver / 11',165,'procedural:flightsuits-6-10','procedural','{"key": "flightsuits-6-10", "style": "Skydiver", "color": "#42d8d0", "styleIndex": 6, "colorIndex": 10}'::jsonb),
('flightsuits','Skydiver / 12',170,'procedural:flightsuits-6-11','procedural','{"key": "flightsuits-6-11", "style": "Skydiver", "color": "#a5abb8", "styleIndex": 6, "colorIndex": 11}'::jsonb) ON CONFLICT (asset_url) WHERE asset_kind='procedural' DO NOTHING;
    CREATE TABLE IF NOT EXISTS user_store_items (
      user_id BIGINT NOT NULL REFERENCES users(id) ON DELETE CASCADE,
      item_id BIGINT NOT NULL REFERENCES store_items(id) ON DELETE CASCADE,
      purchased_at TIMESTAMPTZ NOT NULL DEFAULT NOW(),
      PRIMARY KEY (user_id, item_id)
    );

    -- KWG V3.49: permanent, server-authoritative pets and equipped companion.
    CREATE TABLE IF NOT EXISTS pet_catalog (
      pet_key VARCHAR(32) PRIMARY KEY,
      name VARCHAR(40) NOT NULL,
      price INTEGER NOT NULL CHECK (price >= 0),
      species VARCHAR(20) NOT NULL,
      is_visible BOOLEAN NOT NULL DEFAULT TRUE
    );
    CREATE TABLE IF NOT EXISTS user_pets (
      user_id BIGINT NOT NULL REFERENCES users(id) ON DELETE CASCADE,
      pet_key VARCHAR(32) NOT NULL REFERENCES pet_catalog(pet_key),
      purchased_at TIMESTAMPTZ NOT NULL DEFAULT NOW(),
      PRIMARY KEY(user_id,pet_key)
    );
    CREATE TABLE IF NOT EXISTS user_pet_equipment (
      user_id BIGINT PRIMARY KEY REFERENCES users(id) ON DELETE CASCADE,
      pet_key VARCHAR(32) NOT NULL REFERENCES pet_catalog(pet_key),
      equipped_at TIMESTAMPTZ NOT NULL DEFAULT NOW()
    );
    INSERT INTO pet_catalog(pet_key,name,price,species) VALUES
      ('dog_1','Dog 1',75,'dog'),('dog_2','Dog 2',85,'dog'),
      ('dog_3','Dog 3',95,'dog'),('dog_4','Dog 4',110,'dog'),
      ('cat_1','Cat 1',95,'cat'),('cat_2','Cat 2',105,'cat'),
      ('cat_3','Cat 3',115,'cat'),('cat_4','Cat 4',125,'cat'),
      ('monkey_1','Monkey 1',135,'monkey'),('monkey_2','Monkey 2',145,'monkey'),
      ('monkey_3','Monkey 3',155,'monkey'),('monkey_4','Monkey 4',165,'monkey'),
      ('bunny_1','Bunny 1',135,'bunny'),('bunny_2','Bunny 2',145,'bunny'),
      ('bunny_3','Bunny 3',155,'bunny'),('bunny_4','Bunny 4',165,'bunny'),
      ('owl_1','Owl 1',165,'owl'),('owl_2','Owl 2',175,'owl'),
      ('owl_3','Owl 3',185,'owl'),('owl_4','Owl 4',195,'owl'),
      ('alien_1','Alien 1',185,'alien'),('alien_2','Alien 2',195,'alien'),
      ('alien_3','Alien 3',205,'alien'),('alien_4','Alien 4',215,'alien'),
      ('skeleton_1','Skeleton 1',175,'skeleton'),('skeleton_2','Skeleton 2',185,'skeleton'),
      ('skeleton_3','Skeleton 3',195,'skeleton'),('skeleton_4','Skeleton 4',205,'skeleton'),
      ('mummy_1','Mummy 1',175,'mummy'),('mummy_2','Mummy 2',185,'mummy'),
      ('mummy_3','Mummy 3',195,'mummy'),('mummy_4','Mummy 4',205,'mummy'),
      ('pumpkin_1','Jack O Lantern 1',195,'pumpkin'),('pumpkin_2','Jack O Lantern 2',205,'pumpkin'),
      ('pumpkin_3','Jack O Lantern 3',215,'pumpkin'),('pumpkin_4','Jack O Lantern 4',225,'pumpkin'),
      ('zombie_1','Zombie 1',175,'zombie'),('zombie_2','Zombie 2',185,'zombie'),
      ('zombie_3','Zombie 3',195,'zombie'),('zombie_4','Zombie 4',205,'zombie')
    ON CONFLICT(pet_key) DO NOTHING;
    -- Keep shelved pets and past purchases in the database for a future redesign.
    UPDATE pet_catalog SET is_visible=FALSE WHERE species IN ('skeleton','mummy','zombie');

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

    -- One active in-world socket per account. The unique user_id makes this
    -- work even when the game is hosted by multiple Node processes.
    CREATE TABLE IF NOT EXISTS active_world_sessions (
      user_id BIGINT PRIMARY KEY REFERENCES users(id) ON DELETE CASCADE,
      socket_id TEXT NOT NULL,
      world_name TEXT NOT NULL,
      last_seen TIMESTAMPTZ NOT NULL DEFAULT NOW()
    );
    CREATE INDEX IF NOT EXISTS active_world_sessions_seen_idx ON active_world_sessions(last_seen);

    CREATE TABLE IF NOT EXISTS world_likes (
      world_id BIGINT NOT NULL REFERENCES worlds(id) ON DELETE CASCADE,
      user_id BIGINT NOT NULL REFERENCES users(id) ON DELETE CASCADE,
      created_at TIMESTAMPTZ NOT NULL DEFAULT NOW(),
      PRIMARY KEY (world_id, user_id)
    );

    CREATE INDEX IF NOT EXISTS auth_sessions_user_idx ON auth_sessions(user_id);
    CREATE INDEX IF NOT EXISTS auth_sessions_expiry_idx ON auth_sessions(expires_at);
    CREATE INDEX IF NOT EXISTS world_likes_world_idx ON world_likes(world_id);
    CREATE INDEX IF NOT EXISTS world_likes_recent_idx ON world_likes(created_at DESC, world_id);
    CREATE TABLE IF NOT EXISTS user_world_visits (
      user_id BIGINT NOT NULL REFERENCES users(id) ON DELETE CASCADE,
      world_id BIGINT NOT NULL REFERENCES worlds(id) ON DELETE CASCADE,
      last_played_at TIMESTAMPTZ NOT NULL DEFAULT NOW(),
      PRIMARY KEY (user_id,world_id)
    );
    CREATE INDEX IF NOT EXISTS user_world_visits_recent_idx
      ON user_world_visits(user_id,last_played_at DESC);
    CREATE INDEX IF NOT EXISTS chat_world_created_idx ON chat_messages(world_id, created_at DESC);
    CREATE INDEX IF NOT EXISTS store_items_category_visible_idx ON store_items(category, is_visible, created_at DESC);
    CREATE INDEX IF NOT EXISTS user_store_items_user_idx ON user_store_items(user_id);
  `);

  // Curated storefront: hide redundant generated variants without deleting rows,
  // ownership, purchase history, or existing equipped item references.
  await pool.query(`
    UPDATE store_items
    SET is_visible = CASE
      WHEN category = 'skin' THEN
        COALESCE((metadata->>'styleIndex')::int,-1) = 0
        AND COALESCE((metadata->>'colorIndex')::int,-1) IN (0,1,2,3,4,8,9,10,11,12,13)
      WHEN category IN ('hair','hats','heads','eyes','mouth','tops','bottoms','shoes','flightsuits') THEN
        COALESCE((metadata->>'colorIndex')::int,0) < 4
      ELSE is_visible
    END
    WHERE asset_kind = 'procedural'
      AND asset_url LIKE 'procedural:%'
  `);
  await pool.query('DELETE FROM auth_sessions WHERE expires_at <= NOW()');
  await pool.query("DELETE FROM active_world_sessions WHERE last_seen < NOW() - INTERVAL '90 seconds'");

  // Older multiplayer worlds could be created completely empty. The editor places
  // parts onto existing surfaces, so seed a baseplate only when a world has zero blocks.
  const emptyWorlds = await pool.query(`SELECT id,data FROM worlds`);
  for (const row of emptyWorlds.rows) {
    const data = row.data || {};
    data.blocks = data.blocks || {};
    if (Object.keys(data.blocks).length === 0) {
      data.blocks.baseplate = {
        id:'baseplate', shape:'box', actionType:'normal', material:'grid', color:'#555555',
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
    displayName: filterKWGUserText(String(row.data?.displayName || row.name).slice(0,40)),
    description: filterKWGUserText(String(row.data?.description || '').slice(0,300)),
    thumbnailUrl: String(row.data?.thumbnailUrl || ''),
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
function refreshPrimarySocketForUser(userId) {
  // Prefer the in-world socket for friends' online/visit information, even if
  // the same account is signed into other dashboard-only tabs.
  let chosen = null;
  for (const s of io.sockets.sockets.values()) {
    if (s.user && Number(s.user.id) === Number(userId)) {
      if (playersBySocket.has(s.id)) { chosen = s; break; }
      chosen = s;
    }
  }
  if (chosen) socketsByUser.set(userId, chosen);
  else socketsByUser.delete(userId);
}
async function loginSocketUser(socket, user) {
  socket.user = user;
  socket.user.isAdmin = !!user.is_admin;
  refreshPrimarySocketForUser(user.id);
}
function authResponse(user, token) {
  return {success:true,username:user.username,appearance:user.appearance,isAdmin:!!user.is_admin,coins:Number(user.coins || 0),sessionToken:token};
}

// Serialize world-data writes so rapid edits cannot overwrite one another.
// Each world gets its own queue, so different worlds can still save in parallel.
const worldSaveQueues = new Map();

function queueWorldSave(worldName, task) {
  const key = cleanWorldName(worldName).toLowerCase();
  const previous = worldSaveQueues.get(key) || Promise.resolve();

  const next = previous
    .catch(() => {})
    .then(task);

  worldSaveQueues.set(key, next);

  next.finally(() => {
    if (worldSaveQueues.get(key) === next) worldSaveQueues.delete(key);
  }).catch(() => {});

  return next;
}

const worldJoinReservations = new Map();
const accountWorldJoinReservations = new Set();

function inWorldSocketForUser(userId, excludingSocketId) {
  for (const [sid, player] of playersBySocket) {
    if (sid === excludingSocketId || !player.worldName) continue;
    const s = io.sockets.sockets.get(sid);
    if (s?.user && Number(s.user.id) === Number(userId)) return s;
  }
  return null;
}

async function claimWorldSession(userId, socketId, worldName) {
  const result = await pool.query(`
    INSERT INTO active_world_sessions(user_id,socket_id,world_name,last_seen)
    VALUES($1,$2,$3,NOW())
    ON CONFLICT (user_id) DO UPDATE
      SET socket_id=EXCLUDED.socket_id,world_name=EXCLUDED.world_name,last_seen=NOW()
    WHERE active_world_sessions.socket_id=EXCLUDED.socket_id
       OR active_world_sessions.last_seen < NOW() - INTERVAL '90 seconds'
    RETURNING user_id
  `,[userId,socketId,worldName]);
  return result.rowCount === 1;
}
async function releaseWorldSession(userId, socketId) {
  await pool.query('DELETE FROM active_world_sessions WHERE user_id=$1 AND socket_id=$2',[userId,socketId]);
}
// Renew DB leases for connected players even when they stand still.
// A dropped server process stops renewing, so orphaned leases expire.
const worldLeaseHeartbeat = setInterval(() => {
  const byUser = new Map();
  for (const [sid,player] of playersBySocket) {
    const s=io.sockets.sockets.get(sid);
    if (s?.user && player.worldName) byUser.set(s.user.id,sid);
  }
  for (const [userId,sid] of byUser) {
    pool.query('UPDATE active_world_sessions SET last_seen=NOW() WHERE user_id=$1 AND socket_id=$2',[userId,sid])
      .catch(err=>console.error('Could not renew world session:',err));
  }
},20000);
worldLeaseHeartbeat.unref?.();

function worldPlayerCount(worldName) {
  let count = 0;
  for (const [, p] of playersBySocket) if (p.worldName === worldName) count++;
  return count;
}

io.on('connection', (socket) => {
  socket.on('register', async ({ username, password }, cb) => {
    try {
      username = cleanUsername(username);
      password = String(password || '');
      if (!/^[A-Za-z0-9_]{3,16}$/.test(username)) return cb({success:false,message:'Username must be 3-16 letters, numbers, or underscores.'});
      if (/\*/.test(filterKWGUserText(username.replace(/[0-9]/g,'')))) return cb({success:false,message:'Please choose a different username.'});
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
      if (socket.user) {
        const uid=socket.user.id;
        const p=playersBySocket.get(socket.id);
        if (p?.worldName) {
          socket.to(`world:${p.worldName}`).emit('player_left',socket.id);
          socket.leave(`world:${p.worldName}`);
        }
        playersBySocket.delete(socket.id);
        socket.data.worldName=null;
        await releaseWorldSession(uid,socket.id);
        socket.user=null;
        refreshPrimarySocketForUser(uid);
      }
      cb && cb({success:true});
    } catch (e) { console.error(e); cb && cb({success:false}); }
  });

  socket.on('get_notifications', async (_, cb) => {
    if (!requireAuth(socket, cb)) return;
    try {
      const r=await pool.query(`
        SELECT n.id,n.type,n.message,n.is_read AS "isRead",n.created_at AS "createdAt",
               u.username AS "actorUsername"
        FROM notifications n
        LEFT JOIN users u ON u.id=n.actor_user_id
        WHERE n.user_id=$1
        ORDER BY n.created_at DESC
        LIMIT 50
      `,[socket.user.id]);
      cb({success:true,notifications:r.rows,unread:r.rows.filter(x=>!x.isRead).length});
    } catch(e){console.error(e);cb({success:false,message:'Could not load notifications.'});}
  });

  socket.on('mark_notifications_read', async ({ids} = {}, cb) => {
    if (!requireAuth(socket, cb)) return;
    try {
      const clean=[...new Set((Array.isArray(ids)?ids:[]).map(Number).filter(Number.isSafeInteger))];
      if(clean.length) await pool.query(
        'UPDATE notifications SET is_read=TRUE WHERE user_id=$1 AND id=ANY($2::bigint[])',
        [socket.user.id,clean]
      );
      else await pool.query('UPDATE notifications SET is_read=TRUE WHERE user_id=$1',[socket.user.id]);
      cb({success:true});
    } catch(e){console.error(e);cb({success:false,message:'Could not update notifications.'});}
  });

  socket.on('clear_notifications', async (_, cb) => {
    if (!requireAuth(socket, cb)) return;
    try {
      await pool.query('DELETE FROM notifications WHERE user_id=$1',[socket.user.id]);
      cb({success:true});
    } catch(e){console.error(e);cb({success:false,message:'Could not clear notifications.'});}
  });

  socket.on('get_friends', async (_, cb) => {
    if (!requireAuth(socket, cb)) return;
    try {
      const uid=socket.user.id;
      const accepted=await pool.query(`
        SELECT u.id,u.username,u.appearance,f.updated_at AS "friendsSince"
        FROM friendships f
        JOIN users u ON u.id=CASE WHEN f.requester_id=$1 THEN f.addressee_id ELSE f.requester_id END
        WHERE f.status='accepted' AND (f.requester_id=$1 OR f.addressee_id=$1)
        ORDER BY lower(u.username)
      `,[uid]);
      const incoming=await pool.query(`
        SELECT u.username,u.appearance,f.created_at AS "requestedAt"
        FROM friendships f JOIN users u ON u.id=f.requester_id
        WHERE f.addressee_id=$1 AND f.status='pending'
        ORDER BY f.created_at DESC
      `,[uid]);
      const outgoing=await pool.query(`
        SELECT u.username,u.appearance,f.created_at AS "requestedAt"
        FROM friendships f JOIN users u ON u.id=f.addressee_id
        WHERE f.requester_id=$1 AND f.status='pending'
        ORDER BY f.created_at DESC
      `,[uid]);

      const decorate = rows => rows.map(r=>{
        const onlineSocket=socketsByUser.get(r.id);
        const p=onlineSocket ? playersBySocket.get(onlineSocket.id) : null;
        return {...r,online:!!onlineSocket,currentWorld:p?.worldName||null};
      });
      cb({success:true,friends:decorate(accepted.rows),incoming:incoming.rows,outgoing:outgoing.rows});
    } catch(e){console.error(e);cb({success:false,message:'Could not load friends.'});}
  });

  socket.on('send_friend_request', async ({username} = {}, cb) => {
    if (!requireAuth(socket, cb)) return;
    try {
      const name=cleanUsername(username);
      const ur=await pool.query('SELECT id,username FROM users WHERE lower(username)=lower($1)',[name]);
      const target=ur.rows[0];
      if(!target)return cb({success:false,message:'Player not found.'});
      if(Number(target.id)===Number(socket.user.id))return cb({success:false,message:"You can't friend yourself."});
      if(await blockedTogether(socket.user.id,target.id))return cb({success:false,message:'Friend requests are unavailable between blocked players.'});

      const existing=await pool.query(`
        SELECT requester_id,addressee_id,status FROM friendships
        WHERE (requester_id=$1 AND addressee_id=$2) OR (requester_id=$2 AND addressee_id=$1)
        LIMIT 1
      `,[socket.user.id,target.id]);
      const rel=existing.rows[0];
      if(rel?.status==='accepted')return cb({success:false,message:'You are already friends.'});
      if(rel?.status==='pending'){
        if(Number(rel.requester_id)===Number(target.id)){
          await pool.query(`UPDATE friendships SET status='accepted',updated_at=NOW()
            WHERE requester_id=$1 AND addressee_id=$2`,[target.id,socket.user.id]);
          return cb({success:true,state:'friends',message:'Friend request accepted.'});
        }
        return cb({success:false,message:'Friend request already sent.'});
      }
      await pool.query(`INSERT INTO friendships(requester_id,addressee_id,status)
        VALUES($1,$2,'pending')`,[socket.user.id,target.id]);
      await pool.query(`INSERT INTO notifications(user_id,actor_user_id,type,message)
        VALUES($1,$2,'friend_request',$3)`,
        [target.id,socket.user.id,`${socket.user.username} sent you a friend request.`]);
      cb({success:true,state:'outgoing',message:'Friend request sent.'});
    } catch(e){console.error(e);cb({success:false,message:'Could not send friend request.'});}
  });

  socket.on('respond_friend_request', async ({username,accept} = {}, cb) => {
    if (!requireAuth(socket, cb)) return;
    try {
      const ur=await pool.query('SELECT id FROM users WHERE lower(username)=lower($1)',[cleanUsername(username)]);
      const other=ur.rows[0];
      if(!other)return cb({success:false,message:'Player not found.'});
      const result=accept
        ? await pool.query(`UPDATE friendships SET status='accepted',updated_at=NOW()
            WHERE requester_id=$1 AND addressee_id=$2 AND status='pending' RETURNING requester_id`,
            [other.id,socket.user.id])
        : await pool.query(`DELETE FROM friendships
            WHERE requester_id=$1 AND addressee_id=$2 AND status='pending' RETURNING requester_id`,
            [other.id,socket.user.id]);
      if(!result.rowCount)return cb({success:false,message:'Friend request is no longer available.'});
      if(accept){
        await pool.query(`INSERT INTO notifications(user_id,actor_user_id,type,message)
          VALUES($1,$2,'friend_accepted',$3)`,
          [other.id,socket.user.id,`${socket.user.username} accepted your friend request.`]);
      }
      cb({success:true});
    } catch(e){console.error(e);cb({success:false,message:'Could not update friend request.'});}
  });

  socket.on('cancel_friend_request', async ({username} = {}, cb) => {
    if (!requireAuth(socket, cb)) return;
    try {
      const ur=await pool.query('SELECT id FROM users WHERE lower(username)=lower($1)',[cleanUsername(username)]);
      const other=ur.rows[0];
      if(!other)return cb({success:false,message:'Player not found.'});
      await pool.query(`DELETE FROM friendships WHERE requester_id=$1 AND addressee_id=$2 AND status='pending'`,
        [socket.user.id,other.id]);
      cb({success:true});
    } catch(e){console.error(e);cb({success:false,message:'Could not cancel request.'});}
  });

  socket.on('remove_friend', async ({username} = {}, cb) => {
    if (!requireAuth(socket, cb)) return;
    try {
      const ur=await pool.query('SELECT id FROM users WHERE lower(username)=lower($1)',[cleanUsername(username)]);
      const other=ur.rows[0];
      if(!other)return cb({success:false,message:'Player not found.'});
      await pool.query(`DELETE FROM friendships
        WHERE status='accepted' AND ((requester_id=$1 AND addressee_id=$2) OR (requester_id=$2 AND addressee_id=$1))`,
        [socket.user.id,other.id]);
      cb({success:true});
    } catch(e){console.error(e);cb({success:false,message:'Could not remove friend.'});}
  });

  socket.on('get_profile', async ({username} = {}, cb) => {
    if (!requireAuth(socket, cb)) return;
    try {
      const name = cleanUsername(username || socket.user.username);
      const ur = await pool.query(`
        SELECT id,username,appearance,bio,showcased_world_ids,
               created_at AS "createdAt"
        FROM users WHERE lower(username)=lower($1)
      `,[name]);
      const u = ur.rows[0];
      if (!u) return cb({success:false,message:'Player not found.'});

      const [worldCount, likesGiven, inventoryCount, ownedWorlds] = await Promise.all([
        pool.query('SELECT COUNT(*)::int AS n FROM worlds WHERE owner_user_id=$1',[u.id]),
        pool.query('SELECT COUNT(*)::int AS n FROM world_likes WHERE user_id=$1',[u.id]),
        pool.query('SELECT COUNT(*)::int AS n FROM user_store_items WHERE user_id=$1',[u.id]),
        pool.query(`
          SELECT w.name,w.data,w.created_at AS "createdAt",
                 COUNT(wl.user_id)::int AS "likeCount"
          FROM worlds w
          LEFT JOIN world_likes wl ON wl.world_id=w.id
          WHERE w.owner_user_id=$1
          GROUP BY w.id
          ORDER BY w.created_at DESC
        `,[u.id])
      ]);

      const showcaseIds = (u.showcased_world_ids || []).map(Number);
      const byId = new Map();
      const ownedWithIds = await pool.query(`
        SELECT w.id,w.name,w.data,w.created_at AS "createdAt",
               COUNT(wl.user_id)::int AS "likeCount"
        FROM worlds w
        LEFT JOIN world_likes wl ON wl.world_id=w.id
        WHERE w.owner_user_id=$1
        GROUP BY w.id
        ORDER BY w.created_at DESC
      `,[u.id]);
      ownedWithIds.rows.forEach(w => byId.set(Number(w.id), {
        id:Number(w.id), name:w.name, displayName:filterKWGUserText(String(w.data?.displayName||w.name)), thumbnailUrl:String(w.data?.thumbnailUrl||''), createdAt:w.createdAt, likeCount:Number(w.likeCount||0)
      }));
      const showcasedWorlds = showcaseIds.map(id => byId.get(id)).filter(Boolean).slice(0,3);

      let friendship = {state:'none'};
      if (u.id === socket.user.id) {
        friendship = {state:'self'};
      } else {
        const fr = await pool.query(`
          SELECT requester_id,addressee_id,status
          FROM friendships
          WHERE (requester_id=$1 AND addressee_id=$2)
             OR (requester_id=$2 AND addressee_id=$1)
          LIMIT 1
        `,[socket.user.id,u.id]);
        const rel=fr.rows[0];
        if(rel?.status==='accepted') friendship={state:'friends'};
        else if(rel?.status==='pending') friendship={
          state:Number(rel.requester_id)===Number(socket.user.id)?'outgoing':'incoming'
        };
      }

      const blockFlags=await pool.query(`
        SELECT blocker_id,blocked_id FROM user_blocks
        WHERE (blocker_id=$1 AND blocked_id=$2) OR (blocker_id=$2 AND blocked_id=$1)
      `,[socket.user.id,u.id]);
      const blockedByMe=blockFlags.rows.some(x=>Number(x.blocker_id)===Number(socket.user.id));
      const blockBetween=blockFlags.rowCount>0;
      if(blockBetween&&friendship.state!=='self')friendship={state:'none'};

      // Public profile sections: worlds liked by this player, their highest-
      // liked creations, accepted friends, and latest message-board posts.
      const [likedRows, friendRows, messageRows] = await Promise.all([
        pool.query(`
          SELECT w.id,w.name,
                 jsonb_build_object('displayName',w.data->>'displayName',
                                    'thumbnailUrl',w.data->>'thumbnailUrl') AS data,
                 owner.username AS owner_username,
                 liked.created_at AS "likedAt",
                 (SELECT COUNT(*)::int FROM world_likes l2 WHERE l2.world_id=w.id) AS like_count
          FROM world_likes liked
          JOIN worlds w ON w.id=liked.world_id
          LEFT JOIN users owner ON owner.id=w.owner_user_id
          WHERE liked.user_id=$1
          ORDER BY liked.created_at DESC,w.id DESC
        `,[u.id]),
        pool.query(`
          SELECT other.id,other.username,other.appearance,
                 f.updated_at AS "friendsSince"
          FROM friendships f
          JOIN users other ON other.id=CASE WHEN f.requester_id=$1 THEN f.addressee_id ELSE f.requester_id END
          WHERE f.status='accepted' AND (f.requester_id=$1 OR f.addressee_id=$1)
          ORDER BY f.updated_at DESC,lower(other.username) LIMIT 100
        `,[u.id]),
        pool.query(`
          SELECT m.id,m.body,m.created_at AS "createdAt",m.author_user_id AS "authorId",
                 author.username AS "authorUsername",author.appearance AS "authorAppearance"
          FROM profile_messages m
          JOIN users author ON author.id=m.author_user_id
          WHERE m.profile_user_id=$1
          ORDER BY m.created_at DESC,m.id DESC LIMIT 30
        `,[u.id])
      ]);
      const worldCard=w=>({
        id:Number(w.id),name:w.name,
        displayName:filterKWGUserText(String(w.data?.displayName||w.name)),
        likeCount:Number(w.like_count??w.likeCount??0),
        thumbnailUrl:String(w.data?.thumbnailUrl||''),
        createdAt:w.createdAt||null,
        likedAt:w.likedAt||null,
        ownerUsername:w.owner_username||null
      });
      const topWorlds=ownedWithIds.rows.slice().sort((a,b)=>
        Number(b.likeCount)-Number(a.likeCount)||String(a.name).localeCompare(String(b.name))
      ).slice(0,8).map(w=>worldCard({...w,like_count:w.likeCount}));
      const friends=friendRows.rows.map(friend=>({
        username:friend.username,online:!!socketsByUser.get(friend.id),
        appearance:friend.appearance||{},friendsSince:friend.friendsSince
      }));
      const hiddenAuthors=await blockedPeers(socket.user.id,messageRows.rows.map(m=>m.authorId));
      const messages=messageRows.rows.map(m=>({
        id:Number(m.id),authorUsername:hiddenAuthors.has(Number(m.authorId))?KWG_HIDDEN_USER:m.authorUsername,
        authorAppearance:hiddenAuthors.has(Number(m.authorId))?{}:(m.authorAppearance||{}),
        hidden:hiddenAuthors.has(Number(m.authorId)),
        body:hiddenAuthors.has(Number(m.authorId))?KWG_HIDDEN_MESSAGE:filterKWGUserText(m.body),
        createdAt:m.createdAt,
        canDelete:Number(m.authorId)===Number(socket.user.id)||Number(u.id)===Number(socket.user.id)
      }));

      const onlineSocket = socketsByUser.get(u.id);
      const livePlayer = onlineSocket ? playersBySocket.get(onlineSocket.id) : null;
      cb({
        success:true,
        profile:{
          username:u.username,
          bio:filterKWGUserText(u.bio || ''),
          createdAt:u.createdAt,
          appearance:u.appearance || {},
          online:!!onlineSocket,
          currentWorld:(friendship.state==='friends'||friendship.state==='self') ? (livePlayer?.worldName||null) : null,
          isOwnProfile:u.id === socket.user.id,
          friendship,
          blockedByMe,blockBetween,
          stats:{
            worlds:Number(worldCount.rows[0]?.n || 0),
            likesGiven:Number(likesGiven.rows[0]?.n || 0),
            inventory:Number(inventoryCount.rows[0]?.n || 0)
          },
          showcasedWorlds,
          likedWorlds:likedRows.rows.map(worldCard),topWorlds,
          createdWorlds:ownedWithIds.rows.map(w=>worldCard({...w,like_count:w.likeCount})),
          friends,messages,
          ownedWorlds: u.id === socket.user.id ? ownedWithIds.rows.map(w => ({
            id:Number(w.id),name:w.name,displayName:filterKWGUserText(String(w.data?.displayName||w.name)),thumbnailUrl:String(w.data?.thumbnailUrl||''),createdAt:w.createdAt,likeCount:Number(w.likeCount||0)
          })) : []
        }
      });
    } catch (e) { console.error(e); cb({success:false,message:'Could not load profile.'}); }
  });

  socket.on('update_profile', async ({bio,showcaseWorldIds} = {}, cb) => {
    if (!requireAuth(socket, cb)) return;
    try {
      bio = filterKWGUserText(String(bio || '').trim().slice(0,300));
      const ids = [...new Set((Array.isArray(showcaseWorldIds) ? showcaseWorldIds : [])
        .map(Number).filter(Number.isSafeInteger))].slice(0,3);

      if (ids.length) {
        const owned = await pool.query(
          'SELECT id FROM worlds WHERE owner_user_id=$1 AND id = ANY($2::bigint[])',
          [socket.user.id, ids]
        );
        const allowed = new Set(owned.rows.map(r => Number(r.id)));
        if (ids.some(id => !allowed.has(id)))
          return cb({success:false,message:'You can only showcase worlds you own.'});
      }

      if(Array.isArray(showcaseWorldIds)){
        await pool.query('UPDATE users SET bio=$1,showcased_world_ids=$2::bigint[] WHERE id=$3',
          [bio,ids,socket.user.id]);
      }else{
        await pool.query('UPDATE users SET bio=$1 WHERE id=$2',[bio,socket.user.id]);
      }
      cb({success:true});
    } catch (e) { console.error(e); cb({success:false,message:'Could not save profile.'}); }
  });

  socket.on('post_profile_message', async ({username,body} = {}, cb) => {
    if(!requireAuth(socket,cb))return;
    try{
      const targetName=cleanUsername(username);
      const target=await pool.query('SELECT id FROM users WHERE lower(username)=lower($1)',[targetName]);
      if(!target.rowCount)return cb({success:false,message:'Player not found.'});
      if(await blockedTogether(socket.user.id,target.rows[0].id))
        return cb({success:false,message:'You cannot post to this player while either account is blocked.'});
      body=filterKWGUserText(String(body||'').trim().slice(0,240));
      if(!body.trim())return cb({success:false,message:'Message cannot be empty.'});
      const recent=await pool.query(`
        SELECT 1 FROM profile_messages
        WHERE author_user_id=$1 AND created_at>NOW()-INTERVAL '10 seconds' LIMIT 1
      `,[socket.user.id]);
      if(recent.rowCount)return cb({success:false,message:'Wait 10 seconds before posting another message.'});
      await pool.query('INSERT INTO profile_messages(profile_user_id,author_user_id,body) VALUES($1,$2,$3)',
        [target.rows[0].id,socket.user.id,body]);
      cb({success:true});
    }catch(e){console.error('Profile post error:',e);cb({success:false,message:'Could not post message.'});}
  });

  socket.on('delete_profile_message', async ({messageId} = {}, cb) => {
    if(!requireAuth(socket,cb))return;
    try{
      const id=Number(messageId);
      if(!Number.isSafeInteger(id)||id<1)return cb({success:false,message:'Invalid message.'});
      const deleted=await pool.query(`
        DELETE FROM profile_messages m USING users owner
        WHERE m.id=$1 AND owner.id=m.profile_user_id
          AND (m.author_user_id=$2 OR owner.id=$2)
        RETURNING m.id
      `,[id,socket.user.id]);
      if(!deleted.rowCount)return cb({success:false,message:'Message not found or permission denied.'});
      cb({success:true});
    }catch(e){console.error('Profile delete error:',e);cb({success:false,message:'Could not delete message.'});}
  });

  // Home dashboard: recent visits, current rolling-24h like leader,
  // and latest account notifications. All data is scoped to the signed-in user.
  socket.on('get_home_dashboard', async (_payload, cb) => {
    if (!requireAuth(socket, cb)) return;
    try {
      const uid=socket.user.id;
      const [recent,featured,notifications]=await Promise.all([
        pool.query(`
          SELECT w.*, owner.username AS owner_username,
                 (SELECT COUNT(*)::int FROM world_likes wl WHERE wl.world_id=w.id) AS like_count,
                 EXISTS(SELECT 1 FROM world_likes wl WHERE wl.world_id=w.id AND wl.user_id=$1) AS liked_by_me,
                 visits.last_played_at
          FROM user_world_visits visits
          JOIN worlds w ON w.id=visits.world_id
          LEFT JOIN users owner ON owner.id=w.owner_user_id
          WHERE visits.user_id=$1
          ORDER BY visits.last_played_at DESC, w.id DESC
          LIMIT 6
        `,[uid]),
        pool.query(`
          SELECT w.*, owner.username AS owner_username, daily.likes_24h,
                 (SELECT COUNT(*)::int FROM world_likes wl WHERE wl.world_id=w.id) AS like_count,
                 EXISTS(SELECT 1 FROM world_likes wl WHERE wl.world_id=w.id AND wl.user_id=$1) AS liked_by_me
          FROM (
            SELECT world_id, COUNT(*)::int AS likes_24h
            FROM world_likes
            WHERE created_at >= NOW() - INTERVAL '24 hours'
            GROUP BY world_id
            ORDER BY likes_24h DESC, world_id ASC
            LIMIT 1
          ) daily
          JOIN worlds w ON w.id=daily.world_id
          LEFT JOIN users owner ON owner.id=w.owner_user_id
        `,[uid]),
        pool.query(`
          SELECT n.id,n.type,n.message,n.is_read AS "isRead",
                 n.created_at AS "createdAt", u.username AS "actorUsername"
          FROM notifications n
          LEFT JOIN users u ON u.id=n.actor_user_id
          WHERE n.user_id=$1
          ORDER BY n.created_at DESC,n.id DESC
          LIMIT 5
        `,[uid])
      ]);
      cb({success:true,
        recentlyPlayed:await Promise.all(recent.rows.map(async row=>({
          ...await worldSummary(row),lastPlayedAt:row.last_played_at
        }))),
        worldOfTheDay:featured.rows.length?{
          ...await worldSummary(featured.rows[0]),
          likesLast24Hours:Number(featured.rows[0].likes_24h||0)
        }:null,
        notifications:notifications.rows
      });
    } catch(error) {
      console.error('Home dashboard error:',error);
      cb({success:false,message:'Could not load home dashboard.'});
    }
  });

  // KWG V3.45.3: public search, separate from admin account management.
  // Never expose passwords, email/session data or private account settings.
  socket.on('search_public', async ({query,kind} = {}, cb) => {
    if (!requireAuth(socket, cb)) return;
    if (typeof cb !== 'function') return;
    const term=String(query||'').trim().slice(0,60);
    const category=kind==='players'?'players':'worlds';
    if(term.length<2) return cb({success:false,message:'Enter at least two characters.'});
    try {
      if(category==='players'){
        const rows=await pool.query(`
          SELECT id,username,appearance
          FROM users
          WHERE POSITION(lower($1) IN lower(username))>0
          ORDER BY CASE WHEN lower(username)=lower($1) THEN 0
                        WHEN lower(username) LIKE lower($1)||'%' THEN 1 ELSE 2 END,
                   lower(username)
          LIMIT 25
        `,[term]);
        return cb({success:true,kind:category,users:rows.rows.map(u=>({
          username:u.username,appearance:u.appearance||{},
          online:!!socketsByUser.get(u.id)
        }))});
      }
      const rows=await pool.query(`
        SELECT w.name,w.data,w.created_at,u.username AS owner_username,
               (SELECT COUNT(*)::int FROM world_likes wl WHERE wl.world_id=w.id) AS like_count,
               EXISTS(SELECT 1 FROM world_likes wl WHERE wl.world_id=w.id AND wl.user_id=$1) AS liked_by_me
        FROM worlds w LEFT JOIN users u ON u.id=w.owner_user_id
        WHERE POSITION(lower($2) IN lower(w.name))>0
           OR POSITION(lower($2) IN lower(COALESCE(w.data->>'displayName','')))>0
           OR POSITION(lower($2) IN lower(COALESCE(w.data->>'description','')))>0
           OR POSITION(lower($2) IN lower(COALESCE(u.username,'')))>0
        ORDER BY CASE WHEN lower(w.name)=lower($2) THEN 0
                      WHEN lower(w.name) LIKE lower($2)||'%' THEN 1 ELSE 2 END,
                 like_count DESC,w.created_at DESC
        LIMIT 30
      `,[socket.user.id,term]);
      return cb({success:true,kind:category,worlds:await Promise.all(rows.rows.map(worldSummary))});
    }catch(err){
      console.error('Public search failed:',err);
      cb({success:false,message:'Search is temporarily unavailable.'});
    }
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

  // V3.42: Server chooses the initial Spawn so the multiplayer position
  // broadcast and the joining client's avatar always agree.
  function chooseWorldSpawn(data){
    const blocks=Object.values(data?.blocks||{});
    const choices=blocks.filter(b=>b&&b.actionType==='spawn');
    const b=choices.length?choices[Math.floor(Math.random()*choices.length)]:
      blocks.find(b=>b&&(b.id==='baseplate'));
    if(!b)return {x:0,y:.18,z:0};
    const x=Number(b.x)||0,y=Number(b.y)||0,z=Number(b.z)||0;
    const hx=Math.max(.001,Math.abs(Number(b.scaleX)||1)*.5);
    const hy=Math.max(.001,Math.abs(Number(b.scaleY)||1)*.5);
    const hz=Math.max(.001,Math.abs(Number(b.scaleZ)||1)*.5);
    const ax=Number(b.rotationX)||0,ay=Number(b.rotationY)||0;
    // Y extent of an XYZ-rotated block's bounding box.
    const halfHeight=Math.abs(Math.sin(ax)*Math.sin(ay))*hx+
      Math.abs(Math.cos(ax))*hy+Math.abs(Math.sin(ax)*Math.cos(ay))*hz;
    return {x,y:y+halfHeight+.18,z};
  }
  function makeDefaultSpawnBlock(data){
    const base=Object.values(data.blocks||{}).find(b=>b&&(b.id==='baseplate'));
    const x=Number(base?.x)||0,z=Number(base?.z)||0;
    const y=(Number(base?.y)||0)+Math.abs(Number(base?.scaleY)||1)*.5+.5;
    const id='spawn_default';
    return {id,shape:'box',actionType:'spawn',material:'grid',color:'#a86cff',
      transparency:0,canCollide:true,anchored:true,
      x,y,z,scaleX:4,scaleY:1,scaleZ:4,rotationX:0,rotationY:0};
  }

  // Privacy helpers: always consult the database, never client-supplied names.
  const KWG_HIDDEN_USER='Hidden User';
  const KWG_HIDDEN_MESSAGE='This message has been hidden because you or the user are blocked.';
  async function blockedPeers(userId, peerIds){
    const ids=[...new Set(peerIds.map(Number).filter(n=>Number.isSafeInteger(n)&&n!==Number(userId)))];
    if(!ids.length)return new Set();
    const r=await pool.query(`
      SELECT CASE WHEN blocker_id=$1 THEN blocked_id ELSE blocker_id END AS peer_id
      FROM user_blocks
      WHERE (blocker_id=$1 AND blocked_id=ANY($2::bigint[]))
         OR (blocked_id=$1 AND blocker_id=ANY($2::bigint[]))
    `,[userId,ids]);
    return new Set(r.rows.map(x=>Number(x.peer_id)));
  }
  async function blockedTogether(a,b){return (await blockedPeers(a,[b])).has(Number(b));}
  function privatePlayer(p,hidden){return hidden?{...p,username:KWG_HIDDEN_USER,hidden:true}: {...p,hidden:false};}
  function privateChat(msg,hidden){return hidden?{...msg,username:KWG_HIDDEN_USER,message:KWG_HIDDEN_MESSAGE,hidden:true}:msg;}
  function worldPeers(worldName,exceptSid=null){
    return [...playersBySocket.entries()].filter(([sid,p])=>sid!==exceptSid&&p.worldName===worldName)
      .map(([sid,p])=>({sid,p,socket:io.sockets.sockets.get(sid)})).filter(x=>x.socket?.user);
  }
  function refreshPairPrivacy(userA,userB,hidden){
    for(const [sid,p] of playersBySocket){
      const sock=io.sockets.sockets.get(sid);
      if(!sock?.user||![Number(userA),Number(userB)].includes(Number(sock.user.id)))continue;
      const otherId=Number(sock.user.id)===Number(userA)?Number(userB):Number(userA);
      for(const [otherSid,otherP] of playersBySocket){
        const otherSock=io.sockets.sockets.get(otherSid);
        if(otherSock?.user&&Number(otherSock.user.id)===otherId&&otherP.worldName===p.worldName){
          sock.emit('kwg_block_relation_changed',{
            playerId:otherSid,hidden,username:hidden?KWG_HIDDEN_USER:otherP.username
          });
        }
      }
    }
  }

  socket.on('block_player',async ({username}={},cb)=>{
    if(!requireAuth(socket,cb))return;
    try{
      const r=await pool.query('SELECT id FROM users WHERE lower(username)=lower($1)',[cleanUsername(username)]);
      if(!r.rowCount)return cb({success:false,message:'Player not found.'});
      const targetId=Number(r.rows[0].id);
      if(targetId===Number(socket.user.id))return cb({success:false,message:'You cannot block yourself.'});
      await pool.query(`INSERT INTO user_blocks(blocker_id,blocked_id) VALUES($1,$2) ON CONFLICT DO NOTHING`,[socket.user.id,targetId]);
      // Blocking removes existing friendships and pending requests in either direction.
      await pool.query(`DELETE FROM friendships WHERE (requester_id=$1 AND addressee_id=$2) OR (requester_id=$2 AND addressee_id=$1)`,[socket.user.id,targetId]);
      refreshPairPrivacy(socket.user.id,targetId,true);
      cb({success:true,message:'Player blocked. Messages and in-world names are hidden for both players.'});
    }catch(e){console.error('Block player:',e);cb({success:false,message:'Could not block player.'});}
  });
  socket.on('unblock_player',async ({username}={},cb)=>{
    if(!requireAuth(socket,cb))return;
    try{
      const r=await pool.query('SELECT id FROM users WHERE lower(username)=lower($1)',[cleanUsername(username)]);
      if(!r.rowCount)return cb({success:false,message:'Player not found.'});
      const targetId=Number(r.rows[0].id);
      await pool.query('DELETE FROM user_blocks WHERE blocker_id=$1 AND blocked_id=$2',[socket.user.id,targetId]);
      // A block made by the other player still keeps both sides hidden.
      const hidden=await blockedTogether(socket.user.id,targetId);
      refreshPairPrivacy(socket.user.id,targetId,hidden);
      cb({success:true,message:hidden?'Your block was removed; the other player still has you blocked.':'Player unblocked.'});
    }catch(e){console.error('Unblock player:',e);cb({success:false,message:'Could not unblock player.'});}
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
        delete data.displayName; delete data.description; delete data.thumbnailUrl;
      } else {
        data = {
          name,
          blocks: {
            "baseplate": {
              id: "baseplate", shape: "box", actionType: "normal", material: "grid",
              color: "#555555", transparency: 0, canCollide: true, anchored: true,
              x: 0, y: -0.5, z: 0, scaleX: 250, scaleY: 1, scaleZ: 250
            }
          },
          spawnPoint: {x:0,y:0.05,z:0},
          skyColor:'#1e1e7b',
          cloudsEnabled:true,
          cloudSpeed:1.0,
          cloudColor:'#ffffff'
        };
      }
      // New worlds always start with one Spawn unless their template already
      // contains Spawn parts. Existing saved worlds are never modified.
      data.blocks=data.blocks||{};
      if(!Object.values(data.blocks).some(b=>b&&b.actionType==='spawn')){
        const initialSpawn=makeDefaultSpawnBlock(data);
        data.blocks[initialSpawn.id]=initialSpawn;
      }
      await pool.query('INSERT INTO worlds(name,owner_user_id,data) VALUES($1,$2,$3)', [name,socket.user.id,JSON.stringify(data)]);
      cb({success:true});
    } catch (e) { console.error(e); cb({success:false,message:'Could not create world.'}); }
  });

  socket.on('join_world', async ({worldName, appearance, visitUsername, confirmBlocked=false}, cb) => {
    if (!requireAuth(socket, cb)) return;
    const userId=socket.user.id;
    if (accountWorldJoinReservations.has(userId)) {
      return cb({success:false,message:'This account is already joining a world in another session.'});
    }
    if (inWorldSocketForUser(userId,socket.id)) {
      return cb({success:false,message:'Your account is already playing in another session. Leave that world before joining here.'});
    }
    accountWorldJoinReservations.add(userId);
    let leaseClaimed=false;
    let wasAlreadyPlaying=!!playersBySocket.get(socket.id)?.worldName;
    let joinedSuccessfully=false;
    let reservedWorldName=null;
    try {
      // Wait for a preceding leave_world DB cleanup on this socket. This
      // prevents a late release from erasing a newly claimed session lease.
      if (socket.data.worldReleasePromise) await socket.data.worldReleasePromise;
      const world = await getWorldByName(cleanWorldName(worldName));
      if (!world) return cb({success:false,message:'World not found.'});
      // Visiting a player is a friend-only action. Never trust the client to
      // provide the correct world or to claim that the players are friends.
      if(visitUsername){
        const target=await pool.query('SELECT id FROM users WHERE lower(username)=lower($1)',
          [cleanUsername(visitUsername)]);
        if(!target.rowCount||Number(target.rows[0].id)===Number(socket.user.id))
          return cb({success:false,message:'Friend is unavailable.'});
        const friend=await pool.query(`
          SELECT 1 FROM friendships WHERE status='accepted'
            AND ((requester_id=$1 AND addressee_id=$2) OR (requester_id=$2 AND addressee_id=$1))
          LIMIT 1
        `,[socket.user.id,target.rows[0].id]);
        if(!friend.rowCount)return cb({success:false,message:'Only friends can visit players.'});
        const friendSocket=socketsByUser.get(target.rows[0].id);
        const friendPlayer=friendSocket?playersBySocket.get(friendSocket.id):null;
        if(!friendPlayer||friendPlayer.worldName!==world.name)
          return cb({success:false,message:'Your friend is no longer in that world.'});
      }

      // Confirm before entering a world containing anyone blocked in either direction.
      // This check happens on EVERY attempt and precedes the session lease.
      const occupants=worldPeers(world.name,socket.id);
      const blockedOccupants=await blockedPeers(userId,occupants.map(x=>x.socket.user.id));
      if(blockedOccupants.size && !confirmBlocked){
        return cb({success:false,requiresBlockConfirmation:true,
          message:'A blocked user is in this world. Their username and messages will be hidden. Join anyway?',
          blockedCount:occupants.filter(x=>blockedOccupants.has(Number(x.socket.user.id))).length});
      }

      // Claim the account's single in-world lease atomically in PostgreSQL.
      // Unlike a browser-only check, this rejects joins from separate tabs,
      // devices, and separate Node/Render instances.
      leaseClaimed=await claimWorldSession(userId,socket.id,world.name);
      if (!leaseClaimed) {
        return cb({success:false,message:'Your account is already playing in another session. Leave that world before joining here.'});
      }
      // Hard cap: at most 20 connected players per world. Reservations prevent
      // simultaneous joins from briefly pushing the world over the limit.
      const alreadyHere = playersBySocket.get(socket.id)?.worldName === world.name;
      const reserved = worldJoinReservations.get(world.name) || 0;
      const occupied = worldPlayerCount(world.name) - (alreadyHere ? 1 : 0);
      if (occupied + reserved >= 20) {
        return cb({success:false,message:'This world is full (20/20 players).'});
      }
      worldJoinReservations.set(world.name, reserved + 1);
      reservedWorldName=world.name;

      const app = await validateAppearanceForUser(socket.user.id, socket.user.appearance || {});
      const cosmetics = await resolveAppearanceAssets(app);
      const equippedPetRow=await pool.query('SELECT pet_key FROM user_pet_equipment WHERE user_id=$1',[userId]);
      const storedPetKey=equippedPetRow.rows[0]?.pet_key||null;
      const petKey=/^(skeleton|mummy|zombie)_[1-4]$/.test(storedPetKey||'')?null:storedPetKey;
      if (!socket.connected || !socket.user) throw new Error('Disconnected during world join.');
      socket.user.appearance = app;

      const previousWorld=playersBySocket.get(socket.id)?.worldName;
      if (previousWorld && previousWorld!==world.name) {
        socket.to(`world:${previousWorld}`).emit('player_left',socket.id);
      }
      if (socket.data.worldName) socket.leave(`world:${socket.data.worldName}`);
      socket.join(`world:${world.name}`);
      socket.data.worldName = world.name;
      const players = {};
      for (const [sid, p] of playersBySocket) {
        if (p.worldName === world.name) {
          const otherSock=io.sockets.sockets.get(sid);
          players[sid]=privatePlayer(p,!!otherSock?.user&&blockedOccupants.has(Number(otherSock.user.id)));
        }
      }
      const selfSpawn=chooseWorldSpawn(world.data);
      const p = {
        id: socket.id, username: socket.user.username,
        x:selfSpawn.x,y:selfSpawn.y,z:selfSpawn.z,
        rotationY: 0, walkClock: 0, isMoving:false, isGrounded:true,
        appearance: app, cosmetics, petKey, worldName: world.name
      };
      playersBySocket.set(socket.id, p);
      refreshPrimarySocketForUser(userId);
      worldJoinReservations.set(world.name, Math.max(0, (worldJoinReservations.get(world.name) || 1) - 1));
      if (worldJoinReservations.get(world.name) === 0) worldJoinReservations.delete(world.name);
      reservedWorldName=null;
      // Per-recipient join announcements never expose a blocked username.
      for(const peer of occupants){
        if(peer.socket.connected&&peer.p.worldName===world.name)
          peer.socket.emit('player_joined',privatePlayer(p,blockedOccupants.has(Number(peer.socket.user.id))));
      }
      // Record only successful world entries. A history write failure must
      // never prevent a player from joining an otherwise healthy world.
      try {
        await pool.query(`
          INSERT INTO user_world_visits(user_id,world_id,last_played_at)
          VALUES($1,$2,NOW())
          ON CONFLICT(user_id,world_id) DO UPDATE
            SET last_played_at=EXCLUDED.last_played_at
        `,[socket.user.id,world.id]);
      } catch(visitError) {console.error('Could not record recent world visit:',visitError);}
      joinedSuccessfully=true;
      cb({success:true,worldData:world.data,players,selfId:socket.id,selfSpawn,canEdit:canEditWorld(socket, world),selfAppearance:app,selfCosmetics:cosmetics,selfPetKey:petKey});
    } catch (e) {
      console.error(e);
      if (reservedWorldName && worldJoinReservations.has(reservedWorldName)) {
        worldJoinReservations.set(reservedWorldName, Math.max(0, worldJoinReservations.get(reservedWorldName) - 1));
        if (worldJoinReservations.get(reservedWorldName) === 0) worldJoinReservations.delete(reservedWorldName);
      }
      cb({success:false,message:'Could not join world.'});
    } finally {
      accountWorldJoinReservations.delete(userId);
      if (leaseClaimed && !joinedSuccessfully && !wasAlreadyPlaying) {
        await releaseWorldSession(userId,socket.id).catch(err=>console.error('Could not release failed join lease:',err));
      }
    }
  });

  socket.on('leave_world', () => {
    const p = playersBySocket.get(socket.id);
    if (p?.worldName) {
      socket.to(`world:${p.worldName}`).emit('player_left', socket.id);
      socket.leave(`world:${p.worldName}`);
    }
    socket.data.worldName = null;
    playersBySocket.delete(socket.id);
    if (socket.user) {
      const uid=socket.user.id;
      refreshPrimarySocketForUser(uid);
      socket.data.worldReleasePromise=releaseWorldSession(uid,socket.id)
        .catch(err=>console.error('Could not release world session:',err));
    }
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
    socket.to(`world:${p.worldName}`).emit('player_moved',{
      id:p.id,x:p.x,y:p.y,z:p.z,rotationY:p.rotationY,walkClock:p.walkClock,
      verticalVelocity:p.verticalVelocity,isMoving:p.isMoving,isGrounded:p.isGrounded
    });
  });

  // KWG V3.40: One read and one PostgreSQL write for up to 100 ordered edits.
  // The existing single-edit event remains supported for compatibility.
  socket.on('world_edits_batch', async ({worldName,edits} = {}, cb) => {
    if (!requireAuth(socket,cb)) return;
    const key=cleanWorldName(worldName);
    if (socket.data.worldName!==key)
      return cb && cb({success:false,message:'Join the world before saving.'});
    if (!Array.isArray(edits)||edits.length<1||edits.length>100)
      return cb && cb({success:false,message:'Invalid save batch size.'});
    try {
      await queueWorldSave(key,async()=>{
        const world=await getWorldByName(key);
        if(!world){const e=new Error('World not found.');e.clientMessage=e.message;throw e;}
        if(!canEditWorld(socket,world)){
          const e=new Error('Only the world owner or an admin can edit this world.');
          e.clientMessage=e.message;throw e;
        }
        const data=world.data;
        data.blocks=data.blocks||{};
        const notifications=[];
        for(const edit of edits){
          if(!edit||!edit.payload||edit.payload.worldName!==key){
            const e=new Error('Invalid save batch.');e.clientMessage=e.message;throw e;
          }
          const payload=edit.payload;
          if(edit.eventName==='block_update'){
            const {action,blockData,blockId}=payload;
            if(action==='add'||action==='update'){
              if(!blockData||typeof blockData.id!=='string'||!blockData.id){
                const e=new Error('Invalid block data.');e.clientMessage=e.message;throw e;
              }
              if(action==='add'&&!Object.prototype.hasOwnProperty.call(data.blocks,blockData.id)
                 && Object.keys(data.blocks).length>=1400){
                const e=new Error('Part limit reached (1400/1400 parts).');e.clientMessage=e.message;throw e;
              }
              // V3.41: allow normal, kill, checkpoint and spawn types; preserve materials.
              blockData.actionType=['normal','kill','checkpoint','spawn'].includes(blockData.actionType)?blockData.actionType:'normal';
              blockData.material=['grid','brick','wood'].includes(blockData.material)?blockData.material:'grid';
              data.blocks[blockData.id]=blockData;
            }else if(action==='delete'){
              const target=data.blocks[blockId];
              if(blockId==='baseplate'||target?.shape==='baseplate'){
                const e=new Error('The baseplate cannot be deleted.');e.clientMessage=e.message;throw e;
              }
              delete data.blocks[blockId];
            }else{
              const e=new Error('Invalid block action.');e.clientMessage=e.message;throw e;
            }
            notifications.push({type:'block_updated',data:{action,blockData,blockId}});
          }else if(edit.eventName==='world_settings_update'){
            const settings=payload.settings;
            if(!settings||typeof settings!=='object'||Array.isArray(settings)){
              const e=new Error('Invalid world settings.');e.clientMessage=e.message;throw e;
            }
            const allowed=['skyColor','cloudsEnabled','cloudSpeed','cloudColor','spawnPoint'];
            const next={};
            for(const k of allowed)if(Object.prototype.hasOwnProperty.call(settings,k))next[k]=settings[k];
            if(next.skyColor&&!validColor(next.skyColor))delete next.skyColor;
            if(next.cloudColor&&!validColor(next.cloudColor))delete next.cloudColor;
            if(next.cloudSpeed!==undefined)next.cloudSpeed=Math.max(0,Math.min(10,Number(next.cloudSpeed)||0));
            if(next.cloudsEnabled!==undefined)next.cloudsEnabled=!!next.cloudsEnabled;
            if(next.spawnPoint){
              const p=next.spawnPoint;
              if(![p.x,p.y,p.z].every(Number.isFinite))delete next.spawnPoint;
            }
            Object.assign(data,next);
            notifications.push({type:'world_settings_updated',data:next});
          }else{
            const e=new Error('Unsupported save operation.');e.clientMessage=e.message;throw e;
          }
        }
        // All-or-nothing persistence: if any edit fails, none are written.
        await pool.query('UPDATE worlds SET data=$1,updated_at=NOW() WHERE id=$2',
          [JSON.stringify(data),world.id]);
        // Only broadcast AFTER the database confirms the complete batch.
        for(const n of notifications){
          if(n.type==='block_updated')socket.to(`world:${world.name}`).emit(n.type,n.data);
          else io.to(`world:${world.name}`).emit(n.type,n.data);
        }
      });
      cb && cb({success:true,saved:edits.length});
    }catch(e){
      console.error('World batch save:',e);
      cb && cb({success:false,message:e.clientMessage||'Could not save world changes.'});
    }
  });

  socket.on('block_update', async ({worldName, action, blockData, blockId}, cb) => {
    if (!requireAuth(socket)) return;
    if (socket.data.worldName !== cleanWorldName(worldName)) return;

    try {
      await queueWorldSave(worldName, async () => {
        // Keep the original, proven save logic, but run it one edit at a time.
        // This prevents rapid deletes/updates from reading stale copies of the
        // same world and overwriting each other.
        const world = await getWorldByName(worldName);
        if (!world) {
          const err = new Error('World not found.');
          err.clientMessage = 'World not found.';
          throw err;
        }
        if (!canEditWorld(socket, world)) {
          const err = new Error('Not allowed to edit world.');
          err.clientMessage = 'Only the world owner or an admin can edit this world.';
          throw err;
        }

        const data = world.data;
        data.blocks = data.blocks || {};

        if (action === 'add' || action === 'update') {
          if (!blockData || !blockData.id) {
            const err = new Error('Invalid block data.');
            err.clientMessage = 'Could not save changes';
            throw err;
          }
          if (Object.keys(data.blocks).length >= 1400 && action === 'add') {
            const err = new Error('Part limit reached.');
            err.clientMessage = 'Part limit reached (1400/1400 parts).';
            throw err;
          }
          // V3.41: Only the four current block types and three current
          // materials may be saved by clients. Existing legacy worlds are
          // not rewritten on load; their old flags stay intact until edited.
          blockData.actionType = ['normal','kill','checkpoint','spawn'].includes(blockData.actionType) ? blockData.actionType : 'normal';
          blockData.material = ['grid','brick','wood'].includes(blockData.material) ? blockData.material : 'grid';
          data.blocks[blockData.id] = blockData;
        } else if (action === 'delete') {
          const target = data.blocks[blockId];
          if (blockId === 'baseplate') {
            const err = new Error('Baseplate cannot be deleted.');
            err.clientMessage = 'The baseplate cannot be deleted. You can resize it instead.';
            throw err;
          }
          delete data.blocks[blockId];
        } else {
          const err = new Error('Invalid block action.');
          err.clientMessage = 'Could not save changes';
          throw err;
        }

        await pool.query(
          'UPDATE worlds SET data=$1,updated_at=NOW() WHERE id=$2',
          [JSON.stringify(data), world.id]
        );

        socket.to(`world:${world.name}`).emit('block_updated', {action,blockData,blockId});
      });

      cb && cb({success:true});
    } catch (e) {
      console.error(e);
      cb && cb({success:false,message:e.clientMessage || 'Could not save changes'});
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

  socket.on('world_info_update', async ({worldName,displayName,description,thumbnailData} = {}, cb) => {
    if (!requireAuth(socket,cb)) return;
    const key=cleanWorldName(worldName);
    if (socket.data.worldName!==key) return cb && cb({success:false,message:'Join this world before editing its info.'});
    const title=filterKWGUserText(String(displayName||'').trim());
    const desc=filterKWGUserText(String(description||'').trim());
    if (!title || title.length>40 || /[\x00-\x1f\x7f]/.test(title)) return cb && cb({success:false,message:'World title must be 1–40 characters.'});
    if (desc.length>300 || /[\x00-\x08\x0b\x0c\x0e-\x1f]/.test(desc)) return cb && cb({success:false,message:'Description must be 300 characters or fewer.'});
    try {
      const result=await queueWorldSave(key,async()=>{
        const world=await getWorldByName(key);
        if (!world) return {success:false,message:'World not found.'};
        if (!canEditWorld(socket,world)) return {success:false,message:'You cannot edit this world.'};
        const data=world.data||{};
        let thumbnailUrl=data.thumbnailUrl||'';
        if (thumbnailData!==undefined && thumbnailData!==null) {
          thumbnailUrl=await uploadWorldThumbnail(world.id,thumbnailData);
        }
        data.displayName=title;
        data.description=desc;
        data.thumbnailUrl=thumbnailUrl;
        await pool.query('UPDATE worlds SET data=$1,updated_at=NOW() WHERE id=$2',[JSON.stringify(data),world.id]);
        io.to(`world:${key}`).emit('world_info_updated',{worldName:key,displayName:title,description:desc,thumbnailUrl});
        return {success:true,displayName:title,description:desc,thumbnailUrl};
      });
      cb && cb(result);
    } catch(e){console.error('World info update:',e);cb && cb({success:false,message:e.clientMessage||'Could not save world info or thumbnail. Check thumbnail storage configuration.'});}
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
        const peers=worldPeers(p.worldName,socket.id);
        const hiddenPeers=await blockedPeers(socket.user.id,peers.map(x=>x.socket.user.id));
        for(const peer of peers){
          peer.socket.emit('player_appearance_updated',privatePlayer(p,hiddenPeers.has(Number(peer.socket.user.id))));
        }
      }
      cb && cb({success:true,appearance:app,cosmetics});
    } catch (e) {
      console.error(e);
      cb && cb({success:false,message:'Could not save appearance.'});
    }
  });

  // KWG V3.55.6: shelve three species without deleting their purchase records.
  const kwgRetiredPetKey=key=>typeof key==='string' && /^(skeleton|mummy|zombie)_[1-4]$/.test(key);

  // KWG V3.49: pet shop, ownership and equipped companion.
  socket.on('get_pets', async (cb) => {
    if (!requireAuth(socket,cb)) return;
    try {
      const [catalog,owned,equipped]=await Promise.all([
        pool.query(`SELECT pet_key AS "petKey",name,price,species,is_visible AS "isVisible" FROM pet_catalog WHERE species NOT IN ('skeleton','mummy','zombie') AND ($1::boolean OR is_visible=true OR pet_key IN (SELECT pet_key FROM user_pets WHERE user_id=$2)) ORDER BY species,pet_key`,[!!socket.user.isAdmin,socket.user.id]),
        pool.query('SELECT pet_key AS "petKey" FROM user_pets WHERE user_id=$1',[socket.user.id]),
        pool.query('SELECT pet_key AS "petKey" FROM user_pet_equipment WHERE user_id=$1',[socket.user.id])
      ]);
      cb({success:true,pets:catalog.rows,owned:owned.rows.map(r=>r.petKey).filter(k=>!kwgRetiredPetKey(k)),equippedPet:kwgRetiredPetKey(equipped.rows[0]?.petKey)?null:(equipped.rows[0]?.petKey||null)});
    } catch(err){console.error('Get pets failed',err);cb({success:false,message:'Could not load pets.'});}
  });

  socket.on('buy_pet', async ({petKey}={},cb) => {
    if (!requireAuth(socket,cb)) return;
    if (typeof petKey!=='string'||!/^([a-z0-9_]{1,32})$/.test(petKey))
      return cb({success:false,message:'Invalid pet.'});
    if(kwgRetiredPetKey(petKey))return cb({success:false,message:'This pet is temporarily unavailable.'});
    const client=await pool.connect();
    try {
      await client.query('BEGIN');
      const user=await client.query('SELECT coins FROM users WHERE id=$1 FOR UPDATE',[socket.user.id]);
      const pet=await client.query('SELECT price FROM pet_catalog WHERE pet_key=$1 AND is_visible=true',[petKey]);
      if(!pet.rowCount){await client.query('ROLLBACK');return cb({success:false,message:'Pet unavailable.'});}
      const owned=await client.query('SELECT 1 FROM user_pets WHERE user_id=$1 AND pet_key=$2',[socket.user.id,petKey]);
      if(owned.rowCount){await client.query('COMMIT');return cb({success:true,alreadyOwned:true,coins:Number(user.rows[0].coins)});}
      const coins=Number(user.rows[0].coins),price=Number(pet.rows[0].price);
      if(coins<price){await client.query('ROLLBACK');return cb({success:false,message:`You need ${price-coins} more coins.`});}
      const updated=await client.query('UPDATE users SET coins=coins-$1 WHERE id=$2 RETURNING coins',[price,socket.user.id]);
      await client.query('INSERT INTO user_pets(user_id,pet_key) VALUES($1,$2)',[socket.user.id,petKey]);
      await client.query('COMMIT');
      socket.user.coins=Number(updated.rows[0].coins);
      cb({success:true,coins:socket.user.coins});
    } catch(err){await client.query('ROLLBACK').catch(()=>{});console.error('Pet purchase failed',err);cb({success:false,message:'Could not purchase pet.'});}
    finally{client.release();}
  });

  socket.on('equip_pet', async ({petKey}={},cb) => {
    if (!requireAuth(socket,cb)) return;
    if(petKey!==null && (typeof petKey!=='string'||!/^([a-z0-9_]{1,32})$/.test(petKey)))
      return cb({success:false,message:'Invalid pet.'});
    if(kwgRetiredPetKey(petKey))return cb({success:false,message:'This pet is temporarily unavailable.'});
    try {
      if(petKey){
        const owned=await pool.query('SELECT 1 FROM user_pets WHERE user_id=$1 AND pet_key=$2',[socket.user.id,petKey]);
        if(!owned.rowCount)return cb({success:false,message:'You do not own this pet.'});
        await pool.query(`INSERT INTO user_pet_equipment(user_id,pet_key) VALUES($1,$2)
          ON CONFLICT(user_id) DO UPDATE SET pet_key=EXCLUDED.pet_key,equipped_at=NOW()`,[socket.user.id,petKey]);
      }else{
        await pool.query('DELETE FROM user_pet_equipment WHERE user_id=$1',[socket.user.id]);
      }
      const p=playersBySocket.get(socket.id);
      if(p){p.petKey=petKey;io.to(`world:${p.worldName}`).emit('pet_equipped',{id:socket.id,petKey});}
      cb({success:true,equippedPet:petKey});
    }catch(err){console.error('Equip pet failed',err);cb({success:false,message:'Could not change equipped pet.'});}
  });

  socket.on('get_store', async (cb) => {
    if (!requireAuth(socket, cb)) return;
    try {
      await ensureStarterFlightsuit(socket.user.id);
      const [visible, owned, user] = await Promise.all([
        pool.query(`
          SELECT id,category,name,price,asset_url,asset_kind,metadata,is_visible,
                 (created_by IS NOT NULL) AS is_uploaded
          FROM store_items WHERE ($1::boolean OR is_visible=true) AND (asset_kind <> 'avatar_glb' OR $1::boolean)
          ORDER BY category ASC,
                   CASE WHEN asset_kind='procedural' THEN COALESCE((metadata->>'styleIndex')::int,0) ELSE 9999 END ASC,
                   CASE WHEN asset_kind='procedural' THEN COALESCE((metadata->>'colorIndex')::int,0) ELSE 9999 END ASC,
                   name ASC, id ASC
        `,[!!socket.user.isAdmin]),
        pool.query(`
          SELECT s.id,s.category,s.name,s.price,s.asset_url,s.asset_kind,s.metadata,s.is_visible,
                 (s.created_by IS NOT NULL) AS is_uploaded
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

  // KWG V3.55: edit price / shop visibility for any avatar or pet item.
  // Only the authenticated admin flag from the database is trusted.
  socket.on('admin_catalog_edit', async (payload = {}, cb) => {
    if (!requireAdmin(socket, cb)) return;
    if (typeof cb !== 'function') return;
    const {kind, itemId, petKey, price, isVisible} = payload || {};
    if (!Number.isSafeInteger(price) || price < 0 || price > 1000000 || typeof isVisible !== 'boolean')
      return cb({success:false,message:'Price must be a whole number from 0 to 1,000,000.'});
    try {
      let updated;
      if (kind === 'pet') {
        if (typeof petKey !== 'string' || !/^[a-z0-9_]{1,32}$/.test(petKey))
          return cb({success:false,message:'Invalid pet.'});
        if(kwgRetiredPetKey(petKey))return cb({success:false,message:'This pet is temporarily unavailable.'});
        updated=await pool.query('UPDATE pet_catalog SET price=$1,is_visible=$2 WHERE pet_key=$3 RETURNING pet_key',[price,isVisible,petKey]);
      } else if (kind === 'avatar') {
        const id=cleanStoreItemId(itemId);
        if (!id) return cb({success:false,message:'Invalid avatar item.'});
        updated=await pool.query('UPDATE store_items SET price=$1,is_visible=$2,updated_at=NOW() WHERE id=$3 RETURNING id',[price,isVisible,id]);
      } else return cb({success:false,message:'Unknown store type.'});
      if (!updated.rowCount) return cb({success:false,message:'Item not found.'});
      cb({success:true});
    } catch(err){console.error('Catalog edit failed',err);cb({success:false,message:'Could not update store item.'});}
  });

  socket.on('admin_store_list', async (cb) => {
    if (!requireAdmin(socket, cb)) return;
    try {
      const r = await pool.query(`
        SELECT id,category,name,price,asset_url,asset_kind,metadata,is_visible,
               (created_by IS NOT NULL) AS is_uploaded
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

  // V3.56.5: hard delete admin-uploader items only. Deleting the catalog row
  // cascades user_store_items purchases; no pet/builtin item is deletable here.
  socket.on('admin_store_delete', async (payload = {}, cb) => {
    if (!requireAdmin(socket, cb)) return;
    if (typeof cb !== 'function') return;
    const itemId = cleanStoreItemId(payload?.itemId);
    if (!itemId) return cb({success:false,message:'Invalid uploaded item.'});
    const client = await pool.connect();
    let deleted;
    try {
      await client.query('BEGIN');
      const item = await client.query(`
        SELECT id,category,name,asset_url,created_by FROM store_items
        WHERE id=$1 FOR UPDATE
      `,[itemId]);
      if (!item.rowCount || item.rows[0].created_by == null) {
        await client.query('ROLLBACK');
        return cb({success:false,message:'Only items created with the admin item uploader can be deleted.'});
      }
      deleted=item.rows[0];
      // Clear equipped cosmetics for all owners before their purchase records cascade.
      const slotByCategory={eyes:'eyesItemId',mouth:'mouthItemId',torso_decal:'torsoDecalItemId',hat:'hatItemId',head_shape:'headShapeItemId'};
      const slot=slotByCategory[deleted.category];
      if (slot) await client.query(`
        UPDATE users SET appearance=appearance-$2::text
        WHERE (appearance->>$2::text)=$1::text
      `,[itemId,slot]);
      await client.query('DELETE FROM store_items WHERE id=$1',[itemId]);
      await client.query('COMMIT');
      // Update cached online appearances too; deleted items cannot be equipped again.
      if(slot){
        for(const peer of io.sockets.sockets.values()){
          if(peer.user?.appearance && Number(peer.user.appearance[slot])===itemId){
            peer.user.appearance={...peer.user.appearance,[slot]:null};
            const player=playersBySocket.get(peer.id);
            if(player){
              player.appearance={...player.appearance,[slot]:null};
              if(player.cosmetics)delete player.cosmetics[deleted.category];
            }
          }
        }
      }
    }catch(err){
      await client.query('ROLLBACK').catch(()=>{});
      console.error('Admin uploaded-item delete failed',err);
      return cb({success:false,message:'Could not delete uploaded item.'});
    }finally{client.release();}

    // Remove only the exact file created by our uploader in our own store bucket.
    // The catalog deletion is authoritative even if Supabase Storage is unavailable.
    let assetCleanupFailed=false;
    if(storeStorageConfigured()){
      const prefix=`${SUPABASE_URL}/storage/v1/object/public/${encodeURIComponent(SUPABASE_STORE_BUCKET)}/`;
      const assetUrl=String(deleted.asset_url||'');
      if(assetUrl.startsWith(prefix)){
        const key=assetUrl.slice(prefix.length);
        if(/^(eyes|mouth|torso_decal|hat|head_shape)\/\d+-[a-f0-9]{16}\.(png|jpg|webp|glb)$/.test(key)){
          try{
            const bucket=encodeURIComponent(SUPABASE_STORE_BUCKET);
            const path=key.split('/').map(encodeURIComponent).join('/');
            const response=await fetch(`${SUPABASE_URL}/storage/v1/object/${bucket}/${path}`,{
              method:'DELETE',headers:storageHeaders()
            });
            if(!response.ok&&response.status!==404){
              assetCleanupFailed=true;
              console.error('Uploaded asset cleanup failed',response.status,deleted.id);
            }
          }catch(err){assetCleanupFailed=true;console.error('Uploaded asset cleanup failed',deleted.id,err);}
        }else{assetCleanupFailed=true;console.error('Uploaded asset path did not match uploader format',deleted.id);}
      }else{assetCleanupFailed=true;console.error('Uploaded asset is outside the configured store bucket',deleted.id);}
    }else{assetCleanupFailed=true;console.error('Storage not configured; uploaded asset cleanup skipped',deleted.id);}
    cb({success:true,assetCleanupFailed});
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
        SELECT user_id AS "userId",username,message,created_at AS "createdAt"
        FROM chat_messages WHERE world_id=$1
        ORDER BY created_at DESC LIMIT 100
      `,[world.id]);
      const hiddenAuthors=await blockedPeers(socket.user.id,r.rows.map(x=>x.userId));
      cb({success:true,messages:r.rows.reverse().map(x=>privateChat({
        username:x.username,message:filterKWGUserText(x.message),createdAt:x.createdAt,worldName:world.name
      },hiddenAuthors.has(Number(x.userId))))});
    } catch (e) { console.error(e); cb({success:false,message:'Could not load chat.'}); }
  });

  socket.on('send_world_chat', async ({worldName,message},cb) => {
    if (!requireAuth(socket, cb)) return;
    worldName = cleanWorldName(worldName);
    message = filterKWGUserText(String(message || '').trim().slice(0,300));
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
      const peers=worldPeers(world.name);
      const hiddenPeers=await blockedPeers(socket.user.id,peers.map(x=>x.socket.user.id));
      const event={worldName:world.name,username:socket.user.username,message,createdAt:r.rows[0].createdAt};
      for(const peer of peers){
        peer.socket.emit('world_chat_message',privateChat(event,hiddenPeers.has(Number(peer.socket.user.id))));
      }
      cb({success:true});
    } catch (e) { console.error(e); cb({success:false,message:'Could not send message.'}); }
  });

  // V3.50: test coins can ONLY be added by an authenticated server-side admin,
  // and ONLY to that admin's own account. Never trust a client-provided user ID.
  socket.on('admin_grant_self_coins', async ({amount} = {}, cb) => {
    if (!requireAdmin(socket, cb)) return;
    if (typeof cb !== 'function') return;
    if (!Number.isSafeInteger(amount) || amount < 1 || amount > 100000)
      return cb({success:false,message:'Amount must be a whole number from 1 to 100,000.'});
    try {
      const result = await pool.query(`
        UPDATE users SET coins=coins+$1
        WHERE id=$2 AND coins <= 2147483647-$1
        RETURNING coins
      `,[amount,socket.user.id]);
      if (!result.rowCount)
        return cb({success:false,message:'Coin balance limit reached.'});
      socket.user.coins=Number(result.rows[0].coins);
      cb({success:true,coins:socket.user.coins});
    } catch (e) { console.error('Admin coin grant failed:',e); cb({success:false,message:'Could not add coins.'}); }
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
          if (target?.user) refreshPrimarySocketForUser(target.user.id);
        }
      }
      await pool.query('DELETE FROM active_world_sessions WHERE world_name=$1',[world.name]);
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
          if (s?.user) refreshPrimarySocketForUser(s.user.id);
        }
      }
      await pool.query('DELETE FROM active_world_sessions WHERE world_name=$1',[world.name]);
      await pool.query('DELETE FROM worlds WHERE id=$1',[world.id]);
      cb({success:true});
    } catch (e) { console.error(e); cb({success:false,message:'Could not delete world.'}); }
  });

  socket.on('disconnect', () => {
    const p = playersBySocket.get(socket.id);
    if (p?.worldName) socket.to(`world:${p.worldName}`).emit('player_left', socket.id);
    playersBySocket.delete(socket.id);
    if (socket.user) {
      const uid=socket.user.id;
      refreshPrimarySocketForUser(uid);
      releaseWorldSession(uid,socket.id).catch(err=>console.error('Could not release disconnected world session:',err));
    }
  });
});

migrate().then(() => {
  server.listen(PORT, () => console.log(`KWG 3D server listening on port ${PORT}`));
}).catch(err => {
  console.error('Database migration failed:', err);
  process.exit(1);
});
