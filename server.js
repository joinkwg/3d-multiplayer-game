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

function normalizeEnemySpawner(block){
  if(!block || block.actionType!=='enemy_spawner')return;
  const bounded=(v,lo,hi,fallback)=>{
    const n=Number(v);
    return Number.isFinite(n)?Math.min(hi,Math.max(lo,n)):fallback;
  };
  block.noticeRange=bounded(block.noticeRange,2,100,18);
  block.enemySpeed=bounded(block.enemySpeed,.5,15,3);
  block.enemyCount=Math.round(bounded(block.enemyCount,1,12,1));
  block.enemyRespawn=bounded(block.enemyRespawn,0,300,5);
  block.enemyDamage=Math.round(bounded(block.enemyDamage,1,100,25));
  block.enemyCharacter=['devil','sniper','hops','spider','alien','bot_bus','balloon_baboon'].includes(block.enemyCharacter)?block.enemyCharacter:'devil';
  block.enemyKillable=block.enemyCharacter!=='hops'&&block.enemyKillable!==false;
}
const SUPABASE_WORLD_IMAGE_BUCKET=String(process.env.SUPABASE_WORLD_IMAGE_BUCKET||'world-images');
const KWG_IMAGE_MODERATION_KEY=String(process.env.OPENAI_API_KEY||'');
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
// V47: simple avatar appearance. Old purchased items remain owned but cannot be equipped.
const KWG_HAIR_CHOICES = new Set(['none','short','shaggy','straight','wavy']);
function sanitizeAppearance(a = {}) {
  const hairLegacy={classic:'short',sidepart:'shaggy',spiky:'short',bob:'shaggy',ponytail:'straight',flattop:'short',mohawk:'short'};
  const requestedHair=String(a.hairStyle||'none').toLowerCase();
  const hairStyle=KWG_HAIR_CHOICES.has(requestedHair)?requestedHair:(hairLegacy[requestedHair]||'none');
  const skinColor=validColor(a.skinColor)?a.skinColor:(validColor(a.headColor)?a.headColor:defaultAppearance.headColor);
  const shirtColor=validColor(a.shirtColor)?a.shirtColor:(validColor(a.torsoColor)?a.torsoColor:defaultAppearance.torsoColor);
  const pantsColor=validColor(a.pantsColor)?a.pantsColor:(validColor(a.leftLegColor)?a.leftLegColor:defaultAppearance.leftLegColor);
  const shoesColor=validColor(a.shoesColor)?a.shoesColor:'#15191f';
  return {
    ...Object.fromEntries(Object.values(PROCEDURAL_SLOTS).map(slot=>[slot,null])),
    hairStyle,hairColor:validColor(a.hairColor)?a.hairColor:'#3a261b',
    hat:'none',headShape:'sphere',builtinEyes:'none',builtinMouth:'none',
    skinColor,shirtColor,pantsColor,shoesColor,
    shirtStyle:['short','long'].includes(a.shirtStyle)?a.shirtStyle:'short',
    bottomStyle:['pants','shorts','skirt'].includes(a.bottomStyle)?a.bottomStyle:'pants',
    shoeStyle:['shoes','sandals'].includes(a.shoeStyle)?a.shoeStyle:'shoes',
    headColor:skinColor,torsoColor:shirtColor,leftArmColor:skinColor,rightArmColor:skinColor,
    leftLegColor:pantsColor,rightLegColor:pantsColor,
    eyesItemId:null,mouthItemId:null,torsoDecalItemId:null,hatItemId:null,headShapeItemId:null
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
    isUploaded: !!row.is_uploaded,
    creatorUsername: row.creator_username || (row.created_by ? 'Player' : 'KWG')
  };
}

async function ensureStarterFlightsuit(userId){
  // Starter inventory grants are idempotent and server-authoritative.
  await pool.query(`INSERT INTO user_store_items(user_id,item_id)
    SELECT $1,id FROM store_items WHERE metadata->>'distribution'='starter'
    ON CONFLICT DO NOTHING`,[userId]);
}
async function validateAppearanceForUser(userId, rawAppearance = {}) {
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

// V34: Fail-closed moderation. Never place unreviewed bytes in public storage.
async function kwgModerateWorldImage(bytes,mime){
  if(!KWG_IMAGE_MODERATION_KEY)throw new Error('AI moderation is not configured. Set OPENAI_API_KEY on the server.');
  const res=await fetch('https://api.openai.com/v1/moderations',{
    method:'POST',headers:{Authorization:`Bearer ${KWG_IMAGE_MODERATION_KEY}`,'Content-Type':'application/json'},
    body:JSON.stringify({model:'omni-moderation-latest',input:[{type:'image_url',image_url:{url:`data:${mime};base64,${bytes.toString('base64')}`}}]}),
    signal:AbortSignal.timeout(25000)
  });
  if(!res.ok)throw new Error(`Image moderation unavailable (${res.status}).`);
  const result=(await res.json()).results?.[0];
  if(!result||typeof result.flagged!=='boolean')throw new Error('Invalid image moderation result.');
  return !result.flagged && !result.categories?.sexual && !result.categories?.['sexual/minors'];
}
async function kwgUploadApprovedWorldImage(worldId,bytes,mime){
  if(!SUPABASE_URL||!SUPABASE_SERVICE_ROLE_KEY)throw new Error('Image storage is not configured.');
  const bucket=encodeURIComponent(SUPABASE_WORLD_IMAGE_BUCKET);
  const check=await fetch(`${SUPABASE_URL}/storage/v1/bucket/${bucket}`,{headers:storageHeaders()});
  if(check.status===404){
    const created=await fetch(`${SUPABASE_URL}/storage/v1/bucket`,{method:'POST',headers:storageHeaders({'Content-Type':'application/json'}),body:JSON.stringify({id:SUPABASE_WORLD_IMAGE_BUCKET,name:SUPABASE_WORLD_IMAGE_BUCKET,public:true})});
    if(!created.ok&&created.status!==409)throw new Error('Cannot create image storage bucket.');
  }else if(!check.ok)throw new Error('Cannot access image storage bucket.');
  const ext=mime==='image/png'?'png':mime==='image/webp'?'webp':'jpg';
  const key=`world-${Number(worldId)}/${crypto.randomUUID()}.${ext}`;
  const uploaded=await fetch(`${SUPABASE_URL}/storage/v1/object/${bucket}/${key}`,{method:'POST',headers:storageHeaders({'Content-Type':mime,'x-upsert':'false'}),body:bytes});
  if(!uploaded.ok)throw new Error(`Approved image upload failed (${uploaded.status}).`);
  return `${SUPABASE_URL}/storage/v1/object/public/${bucket}/${key}`;
}
function kwgValidImageBytes(bytes,mime){
  if(!bytes||bytes.length<100||bytes.length>1500000)return false;
  if(mime==='image/png')return bytes.subarray(0,8).equals(Buffer.from([137,80,78,71,13,10,26,10]));
  if(mime==='image/jpeg')return bytes[0]===255&&bytes[1]===216&&bytes[bytes.length-2]===255&&bytes[bytes.length-1]===217;
  if(mime==='image/webp')return bytes.toString('ascii',0,4)==='RIFF'&&bytes.toString('ascii',8,12)==='WEBP';
  return false;
}
function kwgPreserveApprovedDecals(block,previous){
  // Client-authored image URLs/statuses are untrusted, even from world owners.
  if(previous?.decals)block.decals=structuredClone(previous.decals);
  else delete block.decals;
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
  const isImage = ['torso_decal','skin'].includes(category) || (['eyes','mouth'].includes(category) && !String(fileName||'').toLowerCase().endsWith('.glb'));
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
      coins INTEGER NOT NULL DEFAULT 950,
      created_at TIMESTAMPTZ NOT NULL DEFAULT NOW()
    );
    CREATE TABLE IF NOT EXISTS worlds (
      id BIGSERIAL PRIMARY KEY,
      name VARCHAR(20) UNIQUE NOT NULL,
      owner_user_id BIGINT REFERENCES users(id) ON DELETE SET NULL,
      data JSONB NOT NULL,
      created_at TIMESTAMPTZ NOT NULL DEFAULT NOW(),
      updated_at TIMESTAMPTZ NOT NULL DEFAULT NOW(),
      plays BIGINT NOT NULL DEFAULT 0,
      bumped_at TIMESTAMPTZ
    );
    ALTER TABLE worlds ADD COLUMN IF NOT EXISTS plays BIGINT NOT NULL DEFAULT 0;
    ALTER TABLE worlds ADD COLUMN IF NOT EXISTS bumped_at TIMESTAMPTZ;
    CREATE INDEX IF NOT EXISTS worlds_bumped_at_idx ON worlds(bumped_at DESC NULLS LAST, created_at DESC);
    -- V49: Persistent, account-wide progression. XP is awarded only on the server.
    CREATE TABLE IF NOT EXISTS kwg_groups (
      id BIGSERIAL PRIMARY KEY,
      name VARCHAR(32) NOT NULL,
      description VARCHAR(300) NOT NULL DEFAULT '',
      icon_key VARCHAR(16) NOT NULL DEFAULT 'shield',
      primary_color VARCHAR(7) NOT NULL DEFAULT '#287eab',
      secondary_color VARCHAR(7) NOT NULL DEFAULT '#ffffff',
      join_policy VARCHAR(8) NOT NULL DEFAULT 'open' CHECK(join_policy IN ('open','invite','closed')),
      min_level INTEGER NOT NULL DEFAULT 1 CHECK(min_level BETWEEN 1 AND 999),
      owner_id BIGINT NOT NULL REFERENCES users(id) ON DELETE CASCADE,
      created_at TIMESTAMPTZ NOT NULL DEFAULT NOW()
    );
    CREATE UNIQUE INDEX IF NOT EXISTS kwg_groups_name_lower_idx ON kwg_groups(lower(name));
    CREATE INDEX IF NOT EXISTS kwg_groups_owner_idx ON kwg_groups(owner_id);
    CREATE TABLE IF NOT EXISTS kwg_group_members (
      group_id BIGINT NOT NULL REFERENCES kwg_groups(id) ON DELETE CASCADE,
      user_id BIGINT NOT NULL REFERENCES users(id) ON DELETE CASCADE,
      role VARCHAR(8) NOT NULL DEFAULT 'member' CHECK(role IN ('owner','elder','member')),
      joined_at TIMESTAMPTZ NOT NULL DEFAULT NOW(),
      PRIMARY KEY(group_id,user_id)
    );
    CREATE INDEX IF NOT EXISTS kwg_group_members_user_idx ON kwg_group_members(user_id);
    CREATE TABLE IF NOT EXISTS kwg_group_invites (
      group_id BIGINT NOT NULL REFERENCES kwg_groups(id) ON DELETE CASCADE,
      user_id BIGINT NOT NULL REFERENCES users(id) ON DELETE CASCADE,
      invited_by BIGINT NOT NULL REFERENCES users(id) ON DELETE CASCADE,
      created_at TIMESTAMPTZ NOT NULL DEFAULT NOW(),
      PRIMARY KEY(group_id,user_id)
    );
    CREATE TABLE IF NOT EXISTS kwg_group_posts (
      id BIGSERIAL PRIMARY KEY,
      group_id BIGINT NOT NULL REFERENCES kwg_groups(id) ON DELETE CASCADE,
      author_id BIGINT NOT NULL REFERENCES users(id) ON DELETE CASCADE,
      body VARCHAR(500) NOT NULL,
      created_at TIMESTAMPTZ NOT NULL DEFAULT NOW()
    );
    CREATE INDEX IF NOT EXISTS kwg_group_posts_recent_idx ON kwg_group_posts(group_id,created_at DESC);
    CREATE TABLE IF NOT EXISTS user_xp_progress (
      user_id BIGINT PRIMARY KEY REFERENCES users(id) ON DELETE CASCADE,
      total_xp BIGINT NOT NULL DEFAULT 0 CHECK(total_xp >= 0),
      finishes BIGINT NOT NULL DEFAULT 0 CHECK(finishes >= 0),
      updated_at TIMESTAMPTZ NOT NULL DEFAULT NOW()
    );
    CREATE INDEX IF NOT EXISTS user_xp_progress_ranking_idx ON user_xp_progress(total_xp DESC,user_id ASC);
    CREATE TABLE IF NOT EXISTS user_achievement_peaks (
      user_id BIGINT NOT NULL REFERENCES users(id) ON DELETE CASCADE,
      achievement_key VARCHAR(32) NOT NULL,
      best_progress BIGINT NOT NULL DEFAULT 0 CHECK(best_progress >= 0),
      PRIMARY KEY(user_id,achievement_key)
    );
    CREATE TABLE IF NOT EXISTS user_achievement_awards (
      user_id BIGINT NOT NULL REFERENCES users(id) ON DELETE CASCADE,
      achievement_key VARCHAR(32) NOT NULL,
      tier SMALLINT NOT NULL CHECK(tier BETWEEN 1 AND 4),
      xp_awarded INTEGER NOT NULL CHECK(xp_awarded > 0),
      unlocked_at TIMESTAMPTZ NOT NULL DEFAULT NOW(),
      PRIMARY KEY(user_id,achievement_key,tier)
    );
    CREATE TABLE IF NOT EXISTS world_level_scores (
      world_id BIGINT NOT NULL REFERENCES worlds(id) ON DELETE CASCADE,
      user_id BIGINT NOT NULL REFERENCES users(id) ON DELETE CASCADE,
      mode VARCHAR(10) NOT NULL CHECK(mode IN ('speed','survival','wins')),
      best_score BIGINT NOT NULL DEFAULT 0,
      updated_at TIMESTAMPTZ NOT NULL DEFAULT NOW(),
      PRIMARY KEY(world_id,user_id,mode)
    );
    CREATE INDEX IF NOT EXISTS world_level_scores_ranking_idx ON world_level_scores(world_id,mode,best_score);
    CREATE TABLE IF NOT EXISTS chat_messages (
      id BIGSERIAL PRIMARY KEY,
      world_id BIGINT NOT NULL REFERENCES worlds(id) ON DELETE CASCADE,
      user_id BIGINT REFERENCES users(id) ON DELETE SET NULL,
      username VARCHAR(16) NOT NULL,
      message VARCHAR(300) NOT NULL,
      created_at TIMESTAMPTZ NOT NULL DEFAULT NOW()
    );

    ALTER TABLE users ADD COLUMN IF NOT EXISTS coins INTEGER NOT NULL DEFAULT 950;
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
    CREATE TABLE IF NOT EXISTS feed_posts (
      id BIGSERIAL PRIMARY KEY,
      author_user_id BIGINT NOT NULL REFERENCES users(id) ON DELETE CASCADE,
      body VARCHAR(500) NOT NULL,
      created_at TIMESTAMPTZ NOT NULL DEFAULT NOW()
    );
    CREATE INDEX IF NOT EXISTS feed_posts_author_idx ON feed_posts(author_user_id,created_at DESC,id DESC);
    CREATE INDEX IF NOT EXISTS feed_posts_recent_idx ON feed_posts(created_at DESC,id DESC);
    ALTER TABLE profile_messages ALTER COLUMN body TYPE VARCHAR(500);
    ALTER TABLE profile_messages ADD COLUMN IF NOT EXISTS source_feed_post_id BIGINT;
    CREATE UNIQUE INDEX IF NOT EXISTS profile_messages_source_feed_post_idx
      ON profile_messages(source_feed_post_id) WHERE source_feed_post_id IS NOT NULL;
    INSERT INTO profile_messages(profile_user_id,author_user_id,body,created_at,source_feed_post_id)
      SELECT author_user_id,author_user_id,body,created_at,id FROM feed_posts
      ON CONFLICT (source_feed_post_id) WHERE source_feed_post_id IS NOT NULL DO NOTHING;
    CREATE TABLE IF NOT EXISTS notifications (
      id BIGSERIAL PRIMARY KEY,
      user_id BIGINT NOT NULL REFERENCES users(id) ON DELETE CASCADE,
      actor_user_id BIGINT REFERENCES users(id) ON DELETE SET NULL,
      type VARCHAR(40) NOT NULL,
      message VARCHAR(240) NOT NULL,
      is_read BOOLEAN NOT NULL DEFAULT FALSE,
      created_at TIMESTAMPTZ NOT NULL DEFAULT NOW()
    );
    ALTER TABLE notifications ADD COLUMN IF NOT EXISTS related_group_id BIGINT;
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
-- Legacy item seeding retired: all items now come from Item Creator.
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

  await pool.query(`CREATE TABLE IF NOT EXISTS item_creator_drafts (
    id BIGSERIAL PRIMARY KEY, owner_id BIGINT NOT NULL REFERENCES users(id) ON DELETE CASCADE,
    name VARCHAR(40) NOT NULL, category VARCHAR(32) NOT NULL, document JSONB NOT NULL,
    updated_at TIMESTAMPTZ NOT NULL DEFAULT NOW()
  )`);

  // Four intentionally curated hair shades per hairstyle. Keep stable item IDs so
  // existing ownership/equipment references continue to resolve.
  await pool.query(`
    UPDATE store_items
    SET metadata = jsonb_set(metadata, '{color}',
      to_jsonb((CASE (metadata->>'colorIndex')::int
        WHEN 0 THEN '#35231D'  -- dark brown
        WHEN 1 THEN '#91492F'  -- auburn
        WHEN 2 THEN '#E6C36D'  -- blonde
        WHEN 3 THEN '#7850AE'  -- purple
      END)::text), true),
      name = (metadata->>'style') || ' / ' ||
        (CASE (metadata->>'colorIndex')::int
          WHEN 0 THEN 'Dark Brown' WHEN 1 THEN 'Auburn'
          WHEN 2 THEN 'Blonde' WHEN 3 THEN 'Purple' END)
    WHERE category='hair' AND asset_kind='procedural'
      AND (metadata->>'styleIndex')::int > 0
      AND (metadata->>'colorIndex')::int BETWEEN 0 AND 3
  `);
  // Curated storefront: hide redundant generated variants without deleting rows,
  // ownership, purchase history, or existing equipped item references.
  await pool.query(`
    UPDATE store_items
    SET is_visible = CASE
      WHEN category = 'hair' THEN
        COALESCE((metadata->>'styleIndex')::int,-1) > 0
        AND COALESCE((metadata->>'colorIndex')::int,-1) BETWEEN 0 AND 3
        OR COALESCE((metadata->>'styleIndex')::int,-1) = 0
        AND COALESCE((metadata->>'colorIndex')::int,-1) = 0
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
  // V53: repair pending invitations that were saved while V52's notification
  // sender was broken. Re-running this migration cannot duplicate an invite.
  await pool.query(`
    INSERT INTO notifications(user_id,actor_user_id,type,message,related_group_id,created_at)
    SELECT i.user_id,i.invited_by,'group_invite',
           LEFT(u.username || ' invited you to ' || g.name || '.',240),
           i.group_id,i.created_at
    FROM kwg_group_invites i
    JOIN kwg_groups g ON g.id=i.group_id
    JOIN users u ON u.id=i.invited_by
    WHERE NOT EXISTS (
      SELECT 1 FROM notifications n
      WHERE n.user_id=i.user_id AND n.type='group_invite'
        AND n.related_group_id=i.group_id AND n.created_at>=i.created_at
    )
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
    plays: Number(row.plays || 0),
    bumpedAt: row.bumped_at || null,
    likedByMe: !!row.liked_by_me,
    createdAt: row.created_at,
    updatedAt: row.updated_at
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
  return {success:true,username:user.username,appearance:user.appearance,level:kwgLevelFromXP(Number(user.total_xp||0)),isAdmin:!!user.is_admin,coins:Number(user.coins || 0),sessionToken:token};
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


// V49: Account-wide XP and four-tier achievements. No client-provided XP or
// progress values are accepted. Existing world visits/likes/worlds/friendships
// count toward achievements, and historical Wins scores seed finish counts once.
const KWG_ACHIEVEMENTS = Object.freeze([
  {key:'explorer',title:'Explorer',description:'Unique worlds visited',goals:[1,3,10,25],xp:[50,150,400,1000]},
  {key:'finisher',title:'Finisher',description:'Levels completed',goals:[1,5,20,75],xp:[75,200,500,1250]},
  {key:'builder',title:'Builder',description:'Worlds created',goals:[1,3,8,20],xp:[100,250,600,1500]},
  {key:'supporter',title:'Supporter',description:'Worlds liked',goals:[1,5,15,40],xp:[40,125,350,900]},
  {key:'social',title:'Social Star',description:'Friends made',goals:[1,3,10,25],xp:[60,175,450,1100]}
]);
const KWG_TIER_NAMES=['Bronze','Silver','Gold','Platinum'];
function kwgXPForLevel(level){const n=Math.max(1,Math.floor(level));return 50*n*(n-1);}
function kwgLevelFromXP(xp){return Math.max(1,Math.floor((1+Math.sqrt(1+Number(xp)/12.5))/2));}
async function kwgRefreshProgress(userId){
  const client=await pool.connect();
  let gained=0,unlocked=[];
  try{
    await client.query('BEGIN');
    // First use backfills the historical Wins leaderboard where available.
    await client.query(`INSERT INTO user_xp_progress(user_id,finishes)
      SELECT $1,COALESCE(SUM(best_score),0)::bigint FROM world_level_scores
      WHERE user_id=$1 AND mode='wins' ON CONFLICT(user_id) DO NOTHING`,[userId]);
    // Serialize award calculation per account, including concurrent sockets.
    const current=await client.query('SELECT total_xp,finishes FROM user_xp_progress WHERE user_id=$1 FOR UPDATE',[userId]);
    if(!current.rowCount)throw new Error('Progress account missing');
    const countsResult=await client.query(`SELECT
      (SELECT COUNT(*) FROM user_world_visits WHERE user_id=$1)::bigint AS explorer,
      $2::bigint AS finisher,
      (SELECT COUNT(*) FROM worlds WHERE owner_user_id=$1)::bigint AS builder,
      (SELECT COUNT(*) FROM world_likes WHERE user_id=$1)::bigint AS supporter,
      (SELECT COUNT(*) FROM friendships WHERE status='accepted' AND (requester_id=$1 OR addressee_id=$1))::bigint AS social`,
      [userId,current.rows[0].finishes]);
    const counts=countsResult.rows[0];
    for(const a of KWG_ACHIEVEMENTS){
      // Once earned, progress never falls when a world is deleted or a
      // friendship/like changes. Rewards themselves are awarded once.
      const peak=await client.query(`INSERT INTO user_achievement_peaks(user_id,achievement_key,best_progress)
        VALUES($1,$2,$3) ON CONFLICT(user_id,achievement_key)
        DO UPDATE SET best_progress=GREATEST(user_achievement_peaks.best_progress,EXCLUDED.best_progress)
        RETURNING best_progress`,[userId,a.key,counts[a.key]||0]);
      counts[a.key]=peak.rows[0].best_progress;
      const progress=Number(counts[a.key]||0);
      for(let i=0;i<4;i++){
        if(progress<a.goals[i])break;
        const inserted=await client.query(`INSERT INTO user_achievement_awards(user_id,achievement_key,tier,xp_awarded)
          VALUES($1,$2,$3,$4) ON CONFLICT DO NOTHING RETURNING xp_awarded`,[userId,a.key,i+1,a.xp[i]]);
        if(inserted.rowCount){
          gained+=a.xp[i];unlocked.push({key:a.key,title:a.title,tier:KWG_TIER_NAMES[i],xp:a.xp[i]});
          await client.query(`INSERT INTO notifications(user_id,type,message)
            VALUES($1,'achievement',$2)`,[userId,`Achievement unlocked: ${a.title} ${KWG_TIER_NAMES[i]} (+${a.xp[i]} XP)!`]);
        }
      }
    }
    if(gained)await client.query('UPDATE user_xp_progress SET total_xp=total_xp+$2,updated_at=NOW() WHERE user_id=$1',[userId,gained]);
    const totalXP=Number(current.rows[0].total_xp)+gained;
    const level=kwgLevelFromXP(totalXP);
    const awards=await client.query('SELECT achievement_key,tier FROM user_achievement_awards WHERE user_id=$1',[userId]);
    const earned=new Set(awards.rows.map(r=>r.achievement_key+':'+r.tier));
    const achievements=KWG_ACHIEVEMENTS.map(a=>({
      key:a.key,title:a.title,description:a.description,progress:Number(counts[a.key]||0),
      tiers:a.goals.map((goal,i)=>({name:KWG_TIER_NAMES[i],goal,xp:a.xp[i],unlocked:earned.has(a.key+':'+(i+1))}))
    }));
    await client.query('COMMIT');
    const state={totalXP,level,levelStartXP:kwgXPForLevel(level),nextLevelXP:kwgXPForLevel(level+1),achievements};
    if(gained){
      kwgPingNotifications([userId]);
      for(const s of io.sockets.sockets.values()){
        if(s.user&&Number(s.user.id)===Number(userId)){
          s.emit('kwg_progress_updated',{...state,gained,unlocked});
          const p=playersBySocket.get(s.id);
          if(p&&p.level!==level){p.level=level;io.to(`world:${p.worldName}`).emit('kwg_player_level',{id:s.id,level});}
        }
      }
    }
    return state;
  }catch(err){await client.query('ROLLBACK').catch(()=>{});throw err;}
  finally{client.release();}
}
async function kwgCreditFinish(userId,mode){
  // On first use, backfill historical Wins, including the current win if this
  // was a Wins level. Otherwise count this completion as one new finish.
  await pool.query(`INSERT INTO user_xp_progress(user_id,finishes)
    SELECT $1,COALESCE(SUM(best_score),0)::bigint+CASE WHEN $2='wins' THEN 0 ELSE 1 END
    FROM world_level_scores WHERE user_id=$1 AND mode='wins'
    ON CONFLICT(user_id) DO UPDATE SET finishes=user_xp_progress.finishes+1,updated_at=NOW()`,[userId,mode]);
  return kwgRefreshProgress(userId);
}
function kwgProgressLater(userId){
  kwgRefreshProgress(userId).catch(err=>console.error('Achievement progress:',err));
}

// V50: persistent groups, level-gated membership and server-owned shirt emblems.
const KWG_GROUP_ICONS=new Set(['shield','star','bolt','flame','crown','moon','paw','leaf']);
const KWG_GROUP_POLICIES=new Set(['open','invite','closed']);
const KWG_GROUP_COLOR=/^#[0-9a-f]{6}$/i;
function kwgGroupId(value){const n=Number(value);return Number.isSafeInteger(n)&&n>0?n:null;}
// V53: persisted, server-generated notifications. A group ID enables a safe
// action on the Notifications page without trusting a URL or message text.
async function kwgNotify(userId,actorId,type,message,groupId=null,db=pool){
  if(!userId||Number(userId)===Number(actorId))return;
  try{
    // This helper is defined outside io.on('connection'), so it cannot call
    // blockedTogether(), which is scoped inside that handler. Check the same
    // mutual block rule directly with the supplied database connection.
    if(actorId){
      const blocked=await db.query(`SELECT 1 FROM user_blocks
        WHERE (blocker_id=$1 AND blocked_id=$2)
           OR (blocker_id=$2 AND blocked_id=$1) LIMIT 1`,[actorId,userId]);
      if(blocked.rowCount)return false;
    }
    const clean=String(message).slice(0,240);
    await db.query(`INSERT INTO notifications(user_id,actor_user_id,type,message,related_group_id)
      VALUES($1,$2,$3,$4,$5)`,[userId,actorId||null,type,clean,groupId]);
    if(db===pool)kwgPingNotifications([userId]);
    return true;
  }catch(e){console.error('Notification delivery:',e);return false;}
}
function kwgPingNotifications(ids){
  const wanted=new Set(ids.map(Number));
  for(const sock of io.sockets.sockets.values())if(wanted.has(Number(sock.user?.id)))sock.emit('kwg_notification_new');
}
async function kwgNotifyGroupStaff(groupId,actorId,type,message){
  try{
    const r=await pool.query(`SELECT user_id FROM kwg_group_members
      WHERE group_id=$1 AND role IN ('owner','elder') AND user_id!=$2`,[groupId,actorId]);
    for(const m of r.rows)await kwgNotify(m.user_id,actorId,type,message,groupId);
  }catch(e){console.error('Group staff notifications:',e);}
}
function kwgGroupDesign(raw={}){
  return {
    iconKey:KWG_GROUP_ICONS.has(raw.iconKey)?raw.iconKey:'shield',
    primaryColor:KWG_GROUP_COLOR.test(raw.primaryColor||'')?raw.primaryColor:'#287eab',
    secondaryColor:KWG_GROUP_COLOR.test(raw.secondaryColor||'')?raw.secondaryColor:'#ffffff',
    joinPolicy:KWG_GROUP_POLICIES.has(raw.joinPolicy)?raw.joinPolicy:'open',
    minLevel:Math.max(1,Math.min(999,Math.floor(Number(raw.minLevel)||1)))
  };
}
async function kwgGroupRole(groupId,userId,db=pool){
  const r=await db.query('SELECT role FROM kwg_group_members WHERE group_id=$1 AND user_id=$2',[groupId,userId]);
  return r.rows[0]?.role||null;
}
async function kwgGroupMemberLevel(userId){
  const r=await pool.query('SELECT total_xp FROM user_xp_progress WHERE user_id=$1',[userId]);
  return kwgLevelFromXP(Number(r.rows[0]?.total_xp||0));
}
async function kwgGroupSyncBadge(userId){
  // A badge is valid only while its owner remains a member of that group.
  const row=await pool.query(`SELECT u.appearance->'groupBadge' AS badge FROM users u WHERE u.id=$1`,[userId]);
  const current=row.rows[0]?.badge;
  let badge=null;
  if(current?.id){
    const r=await pool.query(`SELECT g.id,g.icon_key,g.primary_color,g.secondary_color FROM kwg_groups g
      JOIN kwg_group_members m ON m.group_id=g.id AND m.user_id=$1 WHERE g.id=$2`,[userId,current.id]);
    if(r.rowCount){const g=r.rows[0];badge={id:Number(g.id),iconKey:g.icon_key,primaryColor:g.primary_color,secondaryColor:g.secondary_color};}
  }
  if(badge)await pool.query(`UPDATE users SET appearance=jsonb_set(COALESCE(appearance,'{}'::jsonb),'{groupBadge}',$2::jsonb,true) WHERE id=$1`,[userId,JSON.stringify(badge)]);
  else await pool.query(`UPDATE users SET appearance=COALESCE(appearance,'{}'::jsonb)-'groupBadge' WHERE id=$1`,[userId]);
  for(const sock of io.sockets.sockets.values()){
    if(Number(sock.user?.id)!==Number(userId))continue;
    if(sock.user.appearance)sock.user.appearance.groupBadge=badge;
    sock.emit('kwg_group_badge_changed',{badge});
    const p=playersBySocket.get(sock.id);
    if(p){p.appearance={...p.appearance,groupBadge:badge};io.to(`world:${p.worldName}`).emit('kwg_group_badge_update',{id:sock.id,badge});}
  }
  return badge;
}
async function kwgGroupPublic(groupId,userId){
  const r=await pool.query(`SELECT g.id,g.name,g.description,g.icon_key AS "iconKey",
    g.primary_color AS "primaryColor",g.secondary_color AS "secondaryColor",
    g.join_policy AS "joinPolicy",g.min_level AS "minLevel",g.created_at AS "createdAt",
    owner.username AS "ownerName",g.owner_id AS "ownerId",
    (SELECT COUNT(*)::int FROM kwg_group_members m WHERE m.group_id=g.id) AS "memberCount",
    (SELECT role FROM kwg_group_members m WHERE m.group_id=g.id AND m.user_id=$2) AS "myRole",
    ((SELECT u.appearance->'groupBadge'->>'id' FROM users u WHERE u.id=$2)=g.id::text) AS "badgeEquipped",
    EXISTS(SELECT 1 FROM kwg_group_invites i WHERE i.group_id=g.id AND i.user_id=$2) AS "invited"
    FROM kwg_groups g JOIN users owner ON owner.id=g.owner_id WHERE g.id=$1`,[groupId,userId]);
  return r.rows[0]||null;
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
          kwgAnnounce(p.worldName,`${p.username} left the world.`,socket.user?.id);
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
               n.related_group_id AS "relatedGroupId",
               (n.type='group_invite' AND EXISTS(SELECT 1 FROM kwg_group_invites i
                 WHERE i.group_id=n.related_group_id AND i.user_id=n.user_id)) AS "isInvitePending",
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
      if(accept){kwgProgressLater(socket.user.id);kwgProgressLater(other.id);}
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

  // V50 groups: every mutation checks identity and role on the server.
  socket.on('kwg_group_list',async ({query}={},cb)=>{
    if(!requireAuth(socket,cb))return;
    try{
      const r=await pool.query(`SELECT g.id,g.name,g.description,g.icon_key AS "iconKey",g.primary_color AS "primaryColor",
        g.secondary_color AS "secondaryColor",g.join_policy AS "joinPolicy",g.min_level AS "minLevel",
        owner.username AS "ownerName",(SELECT COUNT(*)::int FROM kwg_group_members m WHERE m.group_id=g.id) AS "memberCount",
        (SELECT role FROM kwg_group_members m WHERE m.group_id=g.id AND m.user_id=$1) AS "myRole",
        EXISTS(SELECT 1 FROM kwg_group_invites i WHERE i.group_id=g.id AND i.user_id=$1) AS "invited"
        FROM kwg_groups g JOIN users owner ON owner.id=g.owner_id
        WHERE g.name ILIKE '%'||$2||'%' OR EXISTS(SELECT 1 FROM kwg_group_members m WHERE m.group_id=g.id AND m.user_id=$1)
        OR EXISTS(SELECT 1 FROM kwg_group_invites i WHERE i.group_id=g.id AND i.user_id=$1)
        ORDER BY CASE WHEN EXISTS(SELECT 1 FROM kwg_group_members m WHERE m.group_id=g.id AND m.user_id=$1)
          OR EXISTS(SELECT 1 FROM kwg_group_invites i WHERE i.group_id=g.id AND i.user_id=$1) THEN 0 ELSE 1 END,
          g.created_at DESC LIMIT 200`,[socket.user.id,String(query||'').trim().slice(0,60)]);
      cb({success:true,groups:r.rows});
    }catch(e){console.error('Group list:',e);cb({success:false,message:'Could not load groups.'});}
  });
  socket.on('kwg_group_detail',async ({groupId}={},cb)=>{
    if(!requireAuth(socket,cb))return;
    const id=kwgGroupId(groupId);if(!id)return cb({success:false,message:'Invalid group.'});
    try{
      const group=await kwgGroupPublic(id,socket.user.id);
      if(!group)return cb({success:false,message:'Group not found.'});
      const members=await pool.query(`SELECT m.user_id AS "userId",u.username,m.role,
        COALESCE(p.total_xp,0) AS xp FROM kwg_group_members m JOIN users u ON u.id=m.user_id
        LEFT JOIN user_xp_progress p ON p.user_id=u.id WHERE m.group_id=$1
        ORDER BY CASE m.role WHEN 'owner' THEN 0 WHEN 'elder' THEN 1 ELSE 2 END,u.username LIMIT 150`,[id]);
      const posts=await pool.query(`SELECT p.id,p.body,p.created_at AS "createdAt",p.author_id AS "authorId",u.username
        FROM kwg_group_posts p JOIN users u ON u.id=p.author_id WHERE p.group_id=$1
        ORDER BY p.created_at DESC LIMIT 40`,[id]);
      const hidden=await blockedPeers(socket.user.id,posts.rows.map(p=>p.authorId));
      cb({success:true,group,members:members.rows.map(m=>({...m,level:kwgLevelFromXP(Number(m.xp)),xp:undefined})),
        posts:posts.rows.map(p=>hidden.has(Number(p.authorId))?{...p,username:'Hidden User',body:'Message hidden.'}:p),
        myId:socket.user.id});
    }catch(e){console.error('Group detail:',e);cb({success:false,message:'Could not load group.'});}
  });
  socket.on('kwg_group_create',async (raw={},cb)=>{
    if(!requireAuth(socket,cb))return;
    const name=filterKWGUserText(String(raw.name||'').trim());
    const description=filterKWGUserText(String(raw.description||'').trim());
    if(name.length<3||name.length>32||description.length>300||/[\x00-\x1f<>]/.test(name))return cb({success:false,message:'Group name must be 3–32 characters.'});
    const d=kwgGroupDesign(raw);let db;
    try{
      db=await pool.connect();await db.query('BEGIN');
      await db.query('SELECT id FROM users WHERE id=$1 FOR UPDATE',[socket.user.id]);
      const count=await db.query('SELECT COUNT(*)::int AS n FROM kwg_groups WHERE owner_id=$1',[socket.user.id]);
      if(Number(count.rows[0].n)>=3){await db.query('ROLLBACK');return cb({success:false,message:'You can own up to three groups.'});}
      const r=await db.query(`INSERT INTO kwg_groups(name,description,icon_key,primary_color,secondary_color,join_policy,min_level,owner_id)
        VALUES($1,$2,$3,$4,$5,$6,$7,$8) RETURNING id`,[name,description,d.iconKey,d.primaryColor,d.secondaryColor,d.joinPolicy,d.minLevel,socket.user.id]);
      await db.query(`INSERT INTO kwg_group_members(group_id,user_id,role) VALUES($1,$2,'owner')`,[r.rows[0].id,socket.user.id]);
      await db.query('COMMIT');cb({success:true,groupId:Number(r.rows[0].id)});
    }catch(e){if(db)await db.query('ROLLBACK').catch(()=>{});console.error('Group create:',e);
      cb({success:false,message:e.code==='23505'?'A group with that name already exists.':'Could not create group.'});}
    finally{db?.release();}
  });
  socket.on('kwg_group_update',async (raw={},cb)=>{
    if(!requireAuth(socket,cb))return;
    const id=kwgGroupId(raw.groupId),d=kwgGroupDesign(raw);
    const name=filterKWGUserText(String(raw.name||'').trim()),description=filterKWGUserText(String(raw.description||'').trim());
    if(!id||name.length<3||name.length>32||description.length>300)return cb({success:false,message:'Invalid group details.'});
    try{
      const r=await pool.query(`UPDATE kwg_groups SET name=$3,description=$4,icon_key=$5,primary_color=$6,secondary_color=$7,
        join_policy=$8,min_level=$9 WHERE id=$1 AND owner_id=$2 RETURNING id`,
        [id,socket.user.id,name,description,d.iconKey,d.primaryColor,d.secondaryColor,d.joinPolicy,d.minLevel]);
      if(!r.rowCount)return cb({success:false,message:'Only the owner can edit this group.'});
      const users=await pool.query(`SELECT u.id FROM kwg_group_members m JOIN users u ON u.id=m.user_id
        WHERE m.group_id=$1 AND (u.appearance->'groupBadge'->>'id')=$2`,[id,String(id)]);
      for(const row of users.rows)await kwgGroupSyncBadge(row.id);
      const updated=await pool.query('SELECT name FROM kwg_groups WHERE id=$1',[id]);
      const members=await pool.query('SELECT user_id FROM kwg_group_members WHERE group_id=$1 AND user_id!=$2',[id,socket.user.id]);
      for(const m of members.rows)await kwgNotify(m.user_id,socket.user.id,'group_edited',`${socket.user.username} edited ${updated.rows[0]?.name||'your group'}.`,id);
      cb({success:true});
    }catch(e){console.error('Group update:',e);cb({success:false,message:e.code==='23505'?'Group name already exists.':'Could not update group.'});}
  });
  socket.on('kwg_group_join',async ({groupId}={},cb)=>{
    if(!requireAuth(socket,cb))return;
    const id=kwgGroupId(groupId);if(!id)return cb({success:false,message:'Invalid group.'});
    try{
      const group=await kwgGroupPublic(id,socket.user.id);
      if(!group)return cb({success:false,message:'Group not found.'});
      if(group.myRole)return cb({success:false,message:'You are already a member.'});
      if(group.joinPolicy==='closed')return cb({success:false,message:'This group is closed.'});
      if(group.joinPolicy==='invite'&&!group.invited)return cb({success:false,message:'An invitation is required.'});
      if(await kwgGroupMemberLevel(socket.user.id)<Number(group.minLevel))return cb({success:false,message:'Your level is too low to join.'});
      const count=await pool.query('SELECT COUNT(*)::int AS n FROM kwg_group_members WHERE user_id=$1',[socket.user.id]);
      if(Number(count.rows[0].n)>=20)return cb({success:false,message:'You can join up to 20 groups.'});
      await pool.query(`INSERT INTO kwg_group_members(group_id,user_id,role)
        SELECT id,$2,'member' FROM kwg_groups WHERE id=$1 AND join_policy!='closed'
        AND (join_policy='open' OR EXISTS(SELECT 1 FROM kwg_group_invites WHERE group_id=$1 AND user_id=$2))
        ON CONFLICT DO NOTHING`,[id,socket.user.id]);
      const role=await kwgGroupRole(id,socket.user.id);
      if(!role)return cb({success:false,message:'Group is no longer accepting members.'});
      const pending=await pool.query('DELETE FROM kwg_group_invites WHERE group_id=$1 AND user_id=$2 RETURNING invited_by',[id,socket.user.id]);
      await kwgNotifyGroupStaff(id,socket.user.id,'group_joined',`${socket.user.username} joined ${group.name}.`);
      for(const invite of pending.rows)await kwgNotify(invite.invited_by,socket.user.id,'group_invite_accepted',`${socket.user.username} accepted your invitation to ${group.name}.`,id);
      cb({success:true});
    }catch(e){console.error('Group join:',e);cb({success:false,message:'Could not join group.'});}
  });
  socket.on('kwg_group_invite',async ({groupId,username}={},cb)=>{
    if(!requireAuth(socket,cb))return;
    const id=kwgGroupId(groupId);if(!id)return cb({success:false,message:'Invalid group.'});
    try{
      const role=await kwgGroupRole(id,socket.user.id);
      if(!['owner','elder'].includes(role))return cb({success:false,message:'Only owners and elders can invite.'});
      const g=await pool.query('SELECT join_policy FROM kwg_groups WHERE id=$1',[id]);
      if(g.rows[0]?.join_policy==='closed')return cb({success:false,message:'Group is closed.'});
      const u=await pool.query('SELECT id FROM users WHERE lower(username)=lower($1)',[cleanUsername(username)]);
      if(!u.rowCount)return cb({success:false,message:'Player not found.'});
      if(await blockedTogether(socket.user.id,u.rows[0].id))return cb({success:false,message:'Cannot invite this player.'});
      if(await kwgGroupRole(id,u.rows[0].id))return cb({success:false,message:'Player is already a member.'});
      if(Date.now()-(socket.data.kwgLastGroupInvite||0)<10000)return cb({success:false,message:'Please wait before sending another invitation.'});
      await pool.query(`INSERT INTO kwg_group_invites(group_id,user_id,invited_by) VALUES($1,$2,$3)
        ON CONFLICT(group_id,user_id) DO UPDATE SET invited_by=EXCLUDED.invited_by,created_at=NOW()`,[id,u.rows[0].id,socket.user.id]);
      socket.data.kwgLastGroupInvite=Date.now();
      const group=await pool.query('SELECT name FROM kwg_groups WHERE id=$1',[id]);
      await kwgNotify(u.rows[0].id,socket.user.id,'group_invite',`${socket.user.username} invited you to ${group.rows[0]?.name||'a group'}.`,id);
      cb({success:true});
    }catch(e){console.error('Group invite:',e);cb({success:false,message:'Could not invite player.'});}
  });
  socket.on('kwg_group_decline',async ({groupId}={},cb)=>{
    if(!requireAuth(socket,cb))return;
    try{await pool.query('DELETE FROM kwg_group_invites WHERE group_id=$1 AND user_id=$2',[kwgGroupId(groupId),socket.user.id]);cb({success:true});}
    catch(e){console.error(e);cb({success:false,message:'Could not decline invitation.'});}
  });
  socket.on('kwg_group_manage_member',async ({groupId,userId,action}={},cb)=>{
    if(!requireAuth(socket,cb))return;
    const id=kwgGroupId(groupId),target=kwgGroupId(userId);
    if(!id||!target||!['promote','demote','kick'].includes(action))return cb({success:false,message:'Invalid action.'});
    try{
      const myRole=await kwgGroupRole(id,socket.user.id),theirRole=await kwgGroupRole(id,target);
      if(!theirRole||theirRole==='owner')return cb({success:false,message:'Cannot manage this member.'});
      if(myRole!=='owner'&&!(myRole==='elder'&&action==='kick'&&theirRole==='member'))
        return cb({success:false,message:'Insufficient permissions.'});
      if(action==='promote'&&theirRole==='member')await pool.query(`UPDATE kwg_group_members SET role='elder' WHERE group_id=$1 AND user_id=$2 AND role='member'`,[id,target]);
      else if(action==='demote'&&theirRole==='elder')await pool.query(`UPDATE kwg_group_members SET role='member' WHERE group_id=$1 AND user_id=$2 AND role='elder'`,[id,target]);
      else if(action==='kick'){
        await pool.query(`DELETE FROM kwg_group_members WHERE group_id=$1 AND user_id=$2 AND role=$3`,[id,target,theirRole]);
        await kwgGroupSyncBadge(target);
      }
      else return cb({success:false,message:'No role change needed.'});
      const group=await pool.query('SELECT name FROM kwg_groups WHERE id=$1',[id]);
      const name=group.rows[0]?.name||'your group';
      const verb=action==='promote'?'promoted you to Elder in':action==='demote'?'demoted you to Member in':'removed you from';
      await kwgNotify(target,socket.user.id,action==='kick'?'group_kicked':action==='promote'?'group_promoted':'group_demoted',`${socket.user.username} ${verb} ${name}.`,id);
      cb({success:true});
    }catch(e){console.error('Group member action:',e);cb({success:false,message:'Could not manage member.'});}
  });
  socket.on('kwg_group_leave',async ({groupId}={},cb)=>{
    if(!requireAuth(socket,cb))return;
    const id=kwgGroupId(groupId);if(!id)return cb({success:false,message:'Invalid group.'});
    try{
      const r=await pool.query(`DELETE FROM kwg_group_members WHERE group_id=$1 AND user_id=$2 AND role!='owner' RETURNING user_id`,[id,socket.user.id]);
      if(!r.rowCount)return cb({success:false,message:'Owners must delete their group to leave.'});
      await kwgGroupSyncBadge(socket.user.id);
      const group=await pool.query('SELECT name FROM kwg_groups WHERE id=$1',[id]);
      await kwgNotifyGroupStaff(id,socket.user.id,'group_left',`${socket.user.username} left ${group.rows[0]?.name||'your group'}.`);
      cb({success:true});
    }catch(e){console.error(e);cb({success:false,message:'Could not leave group.'});}
  });
  socket.on('kwg_group_delete',async ({groupId}={},cb)=>{
    if(!requireAuth(socket,cb))return;
    const id=kwgGroupId(groupId);if(!id)return cb({success:false,message:'Invalid group.'});
    try{
      const members=await pool.query(`SELECT u.id FROM kwg_group_members m JOIN users u ON u.id=m.user_id
        WHERE m.group_id=$1 AND (u.appearance->'groupBadge'->>'id')=$2`,[id,String(id)]);
      const r=await pool.query('DELETE FROM kwg_groups WHERE id=$1 AND owner_id=$2 RETURNING id',[id,socket.user.id]);
      if(!r.rowCount)return cb({success:false,message:'Only the owner can delete this group.'});
      for(const m of members.rows)await kwgGroupSyncBadge(m.id);
      cb({success:true});
    }catch(e){console.error('Group delete:',e);cb({success:false,message:'Could not delete group.'});}
  });
  socket.on('kwg_group_post',async ({groupId,body}={},cb)=>{
    if(!requireAuth(socket,cb))return;
    const id=kwgGroupId(groupId),text=filterKWGUserText(String(body||'').trim());
    if(!id||text.length<1||text.length>500)return cb({success:false,message:'Post must be 1–500 characters.'});
    if(Date.now()-(socket.data.kwgLastGroupPost||0)<10000)return cb({success:false,message:'Please wait before posting again.'});
    try{
      const r=await pool.query(`INSERT INTO kwg_group_posts(group_id,author_id,body)
        SELECT $1,$2,$3 WHERE EXISTS(SELECT 1 FROM kwg_group_members WHERE group_id=$1 AND user_id=$2) RETURNING id`,[id,socket.user.id,text]);
      if(!r.rowCount)return cb({success:false,message:'Join the group before posting.'});
      socket.data.kwgLastGroupPost=Date.now();cb({success:true});
    }catch(e){console.error('Group post:',e);cb({success:false,message:'Could not post message.'});}
  });
  socket.on('kwg_group_delete_post',async ({groupId,postId}={},cb)=>{
    if(!requireAuth(socket,cb))return;
    const id=kwgGroupId(groupId),pid=kwgGroupId(postId);if(!id||!pid)return cb({success:false,message:'Invalid post.'});
    try{
      const role=await kwgGroupRole(id,socket.user.id);
      const r=await pool.query(`DELETE FROM kwg_group_posts WHERE id=$1 AND group_id=$2
        AND (author_id=$3 OR $4::text IN ('owner','elder')) RETURNING id`,[pid,id,socket.user.id,role||'']);
      cb(r.rowCount?{success:true}:{success:false,message:'Cannot remove this post.'});
    }catch(e){console.error(e);cb({success:false,message:'Could not remove post.'});}
  });
  socket.on('kwg_group_my_badges',async (_payload,cb)=>{
    if(!requireAuth(socket,cb))return;
    try{
      const r=await pool.query(`SELECT g.id,g.name,g.icon_key AS "iconKey",
        g.primary_color AS "primaryColor",g.secondary_color AS "secondaryColor"
        FROM kwg_groups g JOIN kwg_group_members m ON m.group_id=g.id
        WHERE m.user_id=$1 ORDER BY g.name LIMIT 20`,[socket.user.id]);
      cb({success:true,badges:r.rows});
    }catch(e){console.error('Group shirt choices:',e);cb({success:false,message:'Could not load group emblems.'});}
  });
  socket.on('kwg_group_badge',async ({groupId,enabled}={},cb)=>{
    if(!requireAuth(socket,cb))return;
    const id=kwgGroupId(groupId);
    try{
      if(enabled){
        if(!id||!await kwgGroupRole(id,socket.user.id))return cb({success:false,message:'Join the group first.'});
        const r=await pool.query('SELECT icon_key,primary_color,secondary_color FROM kwg_groups WHERE id=$1',[id]);
        if(!r.rowCount)return cb({success:false,message:'Group not found.'});
        const g=r.rows[0],badge={id,iconKey:g.icon_key,primaryColor:g.primary_color,secondaryColor:g.secondary_color};
        await pool.query(`UPDATE users SET appearance=jsonb_set(COALESCE(appearance,'{}'::jsonb),'{groupBadge}',$2::jsonb,true) WHERE id=$1`,[socket.user.id,JSON.stringify(badge)]);
      }else await pool.query(`UPDATE users SET appearance=COALESCE(appearance,'{}'::jsonb)-'groupBadge' WHERE id=$1`,[socket.user.id]);
      const badge=await kwgGroupSyncBadge(socket.user.id);cb({success:true,badge});
    }catch(e){console.error('Group badge:',e);cb({success:false,message:'Could not update badge.'});}
  });

  socket.on('get_my_progress',async (_payload,cb)=>{
    if(!requireAuth(socket,cb)||typeof cb!=='function')return;
    try{cb({success:true,progression:await kwgRefreshProgress(socket.user.id)});}
    catch(err){console.error('Progress lookup:',err);cb({success:false,message:'Could not load XP.'});}
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

      const progression=await kwgRefreshProgress(u.id);
      const topXP=await pool.query(`SELECT p.user_id,u.username,p.total_xp
        FROM user_xp_progress p JOIN users u ON u.id=p.user_id
        ORDER BY p.total_xp DESC,p.user_id ASC LIMIT 10`);
      const rankBlocked=await blockedPeers(socket.user.id,topXP.rows.map(r=>r.user_id));
      const globalRank=await pool.query(`SELECT 1+COUNT(*)::int AS rank FROM user_xp_progress
        WHERE total_xp>$1 OR (total_xp=$1 AND user_id<$2)`,[progression.totalXP,u.id]);
      const rankings=topXP.rows.map((r,i)=>({position:i+1,
        username:rankBlocked.has(Number(r.user_id))?'Hidden User':r.username,
        hidden:rankBlocked.has(Number(r.user_id)),totalXP:Number(r.total_xp),
        level:kwgLevelFromXP(Number(r.total_xp)),isViewed:Number(r.user_id)===Number(u.id)}));
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
          progression,globalRank:Number(globalRank.rows[0]?.rank||1),rankings,
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
        RETURNING m.id,m.source_feed_post_id
      `,[id,socket.user.id]);
      if(!deleted.rowCount)return cb({success:false,message:'Message not found or permission denied.'});
      // Also retire migrated V16 feed record, if this message came from one.
      if(deleted.rows[0].source_feed_post_id)await pool.query('DELETE FROM feed_posts WHERE id=$1',[deleted.rows[0].source_feed_post_id]);
      cb({success:true});
    }catch(e){console.error('Profile delete error:',e);cb({success:false,message:'Could not delete message.'});}
  });

  // One source of truth: feed posts are self-authored messages on the
  // poster's existing profile message board. Other people's board messages
  // remain on that board, and are never misattributed to its owner.
  socket.on('post_feed_post',async ({body}={},cb)=>{
    if(!requireAuth(socket,cb))return;
    if(typeof cb!=='function')return;
    try{
      body=filterKWGUserText(String(body||'').trim().slice(0,500));
      if(!body)return cb({success:false,message:'Write a post first.'});
      const recent=await pool.query("SELECT 1 FROM profile_messages WHERE author_user_id=$1 AND created_at>NOW()-INTERVAL '10 seconds' LIMIT 1",[socket.user.id]);
      if(recent.rowCount)return cb({success:false,message:'Wait a few seconds before posting again.'});
      await pool.query('INSERT INTO profile_messages(profile_user_id,author_user_id,body) VALUES($1,$1,$2)',[socket.user.id,body]);
      cb({success:true});
    }catch(e){console.error('Feed post error:',e);cb({success:false,message:'Could not publish post.'});}
  });
  socket.on('get_feed_posts',async (_payload,cb)=>{
    if(!requireAuth(socket,cb))return;
    if(typeof cb!=='function')return;
    try{
      const result=await pool.query(`
        SELECT m.id,m.body,m.created_at AS "createdAt",u.username AS "authorUsername",m.author_user_id AS "authorId"
        FROM profile_messages m JOIN users u ON u.id=m.author_user_id
        WHERE m.profile_user_id=m.author_user_id AND
          (m.author_user_id=$1 OR EXISTS(
            SELECT 1 FROM friendships f WHERE f.status='accepted' AND
              ((f.requester_id=$1 AND f.addressee_id=m.author_user_id) OR
               (f.addressee_id=$1 AND f.requester_id=m.author_user_id))
          )) AND NOT EXISTS(
            SELECT 1 FROM user_blocks b
            WHERE (b.blocker_id=$1 AND b.blocked_id=m.author_user_id)
               OR (b.blocked_id=$1 AND b.blocker_id=m.author_user_id)
          )
        ORDER BY m.created_at DESC,m.id DESC LIMIT 50
      `,[socket.user.id]);
      cb({success:true,posts:result.rows.map(p=>({
        id:Number(p.id),body:filterKWGUserText(p.body),createdAt:p.createdAt,
        authorUsername:p.authorUsername,canDelete:Number(p.authorId)===Number(socket.user.id)
      }))});
    }catch(e){console.error('Feed load error:',e);cb({success:false,message:'Could not load feed.'});}
  });
  socket.on('delete_feed_post',async ({postId}={},cb)=>{
    if(!requireAuth(socket,cb))return;
    if(typeof cb!=='function')return;
    const id=Number(postId);
    if(!Number.isSafeInteger(id)||id<1)return cb({success:false,message:'Invalid post.'});
    try{
      const result=await pool.query('DELETE FROM profile_messages WHERE id=$1 AND author_user_id=$2 AND profile_user_id=$2 RETURNING id,source_feed_post_id',[id,socket.user.id]);
      if(result.rows[0]?.source_feed_post_id)await pool.query('DELETE FROM feed_posts WHERE id=$1',[result.rows[0].source_feed_post_id]);
      cb(result.rowCount?{success:true}:{success:false,message:'Post not found or not yours.'});
    }catch(e){console.error('Feed delete error:',e);cb({success:false,message:'Could not delete post.'});}
  });
  socket.on('get_top_rated_worlds',async (_payload,cb)=>{
    if(!requireAuth(socket,cb))return;
    if(typeof cb!=='function')return;
    try{
      const result=await pool.query(`
        SELECT w.*,u.username AS owner_username,COUNT(wl.user_id)::int AS like_count,
               BOOL_OR(wl.user_id=$1) AS liked_by_me
        FROM worlds w LEFT JOIN users u ON u.id=w.owner_user_id
        LEFT JOIN world_likes wl ON wl.world_id=w.id
        GROUP BY w.id,u.username
        ORDER BY like_count DESC,w.created_at DESC LIMIT 8
      `,[socket.user.id]);
      cb({success:true,worlds:await Promise.all(result.rows.map(worldSummary))});
    }catch(e){console.error('Top worlds error:',e);cb({success:false,message:'Could not load top worlds.'});}
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
        SELECT w.name,w.data,w.created_at,w.updated_at,w.plays,u.username AS owner_username,
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
      const sort = ['liked','recent','bumped'].includes(payload?.sort) ? payload.sort : 'bumped';
      const order = sort === 'liked' ? 'like_count DESC, w.created_at DESC' : sort === 'recent' ? 'w.created_at DESC' : 'COALESCE(w.bumped_at,w.created_at) DESC, w.created_at DESC';
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

  // V45: World bumps are server-authoritative and paid atomically.
  socket.on('bump_world',async ({worldName}={},cb)=>{
    if(!requireAuth(socket,cb))return;
    if(typeof cb!=='function')return;
    const client=await pool.connect();
    try{
      await client.query('BEGIN');
      const r=await client.query('SELECT id,owner_user_id,bumped_at FROM worlds WHERE name=$1 FOR UPDATE',[cleanWorldName(worldName)]);
      const world=r.rows[0];
      if(!world||Number(world.owner_user_id)!==Number(socket.user.id)){
        await client.query('ROLLBACK');return cb({success:false,message:'You can only bump worlds you own.'});
      }
      const paid=await client.query('UPDATE users SET coins=coins-75 WHERE id=$1 AND coins>=75 RETURNING coins',[socket.user.id]);
      if(!paid.rowCount){await client.query('ROLLBACK');return cb({success:false,message:'You need 75 coins to bump this world.'});}
      await client.query('UPDATE worlds SET bumped_at=NOW() WHERE id=$1',[world.id]);
      await client.query('COMMIT');
      socket.user.coins=Number(paid.rows[0].coins);
      cb({success:true,coins:socket.user.coins,bumpedAt:new Date().toISOString()});
    }catch(err){await client.query('ROLLBACK').catch(()=>{});console.error('World bump:',err);cb({success:false,message:'Could not bump world.'});}
    finally{client.release();}
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
        const added=await pool.query('INSERT INTO world_likes(world_id,user_id) VALUES($1,$2) ON CONFLICT DO NOTHING RETURNING world_id',[world.id,socket.user.id]);
        liked=true;
        if(added.rowCount && Number(world.owner_user_id)!==Number(socket.user.id))
          await kwgNotify(world.owner_user_id,socket.user.id,'world_liked',`${socket.user.username} liked your world ${filterKWGUserText(world.name)}.`);
      }
      const count=await pool.query('SELECT COUNT(*)::int AS n FROM world_likes WHERE world_id=$1',[world.id]);
      cb({success:true,liked,likes:Number(count.rows[0].n||0)});
      kwgProgressLater(socket.user.id);
    } catch(e){ console.error(e); cb({success:false,message:'Could not update like.'}); }
  });

  // V40: server-timed per-world runs. Client submits only finish/death
  // events; never a score. Finish requires proximity to a saved Finish part.
  const kwgLevelType=data=>['casual','speed','survival','wins'].includes(data?.levelType)?data.levelType:'casual';
  const kwgElapsed=p=>Math.max(0,Math.min(86400000,Date.now()-(p.runStartedAt||Date.now())));
  async function kwgSaveLevelScore(world,userId,mode,score){
    if(mode==='casual')return {score:null,newRecord:false};
    const old=await pool.query('SELECT best_score FROM world_level_scores WHERE world_id=$1 AND user_id=$2 AND mode=$3',[world.id,userId,mode]);
    const before=old.rows.length?Number(old.rows[0].best_score):null;
    const next=mode==='wins'?(before||0)+1:mode==='speed'?(before===null?score:Math.min(before,score)):(before===null?score:Math.max(before,score));
    const newRecord=before===null||mode==='wins'||(mode==='speed'?score<before:score>before);
    await pool.query(`INSERT INTO world_level_scores(world_id,user_id,mode,best_score) VALUES($1,$2,$3,$4)
      ON CONFLICT(world_id,user_id,mode) DO UPDATE SET best_score=EXCLUDED.best_score,updated_at=NOW()`,[world.id,userId,mode,next]);
    io.to(`world:${world.name}`).emit('world_leaderboard_changed',{worldName:world.name});
    return {score:mode==='wins'?next:score,newRecord,bestScore:next};
  }
  async function kwgAnnounce(worldName,message,actorId=null){
    const peers=worldPeers(worldName);
    try{
      const hidden=actorId?await blockedPeers(actorId,peers.map(x=>x.socket.user.id)):new Set();
      for(const peer of peers){
        const blocked=hidden.has(Number(peer.socket.user.id));
        peer.socket.emit('world_system_message',{worldName,
          message:blocked?'A player had a world event.':message});
      }
    }catch(err){console.error('World event announcement:',err);}
  }
  function kwgNearFinish(p,blocks){
    return Object.values(blocks||{}).some(b=>{
      if(b?.actionType!=='finish')return false;
      const x=Number(b.x)||0,y=Number(b.y)||0,z=Number(b.z)||0;
      const hx=Math.max(.5,Math.abs(Number(b.scaleX)||1)/2)+1.1;
      const hy=Math.max(.5,Math.abs(Number(b.scaleY)||1)/2)+2.4;
      const hz=Math.max(.5,Math.abs(Number(b.scaleZ)||1)/2)+1.1;
      return Math.abs(p.x-x)<=hx&&Math.abs(p.y-y)<=hy&&Math.abs(p.z-z)<=hz;
    });
  }
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

  // V18: every new world starts on a blank baseplate. Names may be omitted;
  // random names are generated server-side so duplicate creation is handled safely.
  socket.on('create_world', async ({name='',description=''}={}, cb) => {
    if (!requireAuth(socket, cb)) return;
    if(typeof cb!=='function')return;
    const supplied=String(name||'').trim();
    if(supplied && !/^[A-Za-z0-9 _-]{1,20}$/.test(supplied))
      return cb({success:false,message:'Use letters, numbers, spaces, _ or - in world names.'});
    const desc=filterKWGUserText(String(description||'').trim());
    if(desc.length>300||/[\x00-\x08\x0b\x0c\x0e-\x1f]/.test(desc))
      return cb({success:false,message:'Description must be 300 characters or fewer.'});
    const adjectives=['Cozy','Sunny','Dreamy','Little','Magic','Cloudy','Happy','Hidden','Misty','Pixel','Golden','Secret'];
    const places=['Garden','Valley','Island','Castle','Meadow','Forest','Village','Planet','Harbor','Cove','Haven','World'];
    function randomWorldName(){
      const prefix=adjectives[crypto.randomInt(adjectives.length)]+' '+places[crypto.randomInt(places.length)];
      const letters=Array.from({length:3},()=>String.fromCharCode(65+crypto.randomInt(26))).join('');
      return `${prefix} ${letters}`.slice(0,20);
    }
    try {
      for(let attempt=0;attempt<(supplied?1:15);attempt++){
        const key=supplied||randomWorldName();
        // Existing worlds are looked up case-insensitively throughout KWG.
        // Keep new names unique under those same lookup rules.
        const existing=await pool.query('SELECT id FROM worlds WHERE lower(name)=lower($1) LIMIT 1',[key]);
        if(existing.rowCount){
          if(supplied)return cb({success:false,message:'That world already exists.'});
          continue;
        }
        const data={
          name:key,displayName:filterKWGUserText(key),description:desc,
          thumbnailUrl:'',thumbnailAuto:false,
          blocks:{
            baseplate:{
              id:'baseplate',shape:'box',actionType:'normal',material:'grid',
              color:'#555555',transparency:0,canCollide:true,anchored:true,
              x:0,y:-0.5,z:0,scaleX:250,scaleY:1,scaleZ:250
            }
          },
          spawnPoint:{x:0,y:0.05,z:0},skyColor:'#1e1e7b',
          brightness:1,saturation:1,resolution:'1080p',lightColor:'#ffffff',lightDirection:'noon'
        };
        const initialSpawn=makeDefaultSpawnBlock(data);
        data.blocks[initialSpawn.id]=initialSpawn;
        const client=await pool.connect();
        try{
          await client.query('BEGIN');
          // Lock the account to prevent concurrent purchases from overdrawing coins.
          const charged=await client.query('UPDATE users SET coins=coins-750 WHERE id=$1 AND coins>=750 RETURNING coins',[socket.user.id]);
          if(!charged.rowCount){await client.query('ROLLBACK');return cb({success:false,message:'You need 750 coins to create a world.'});}
          await client.query('INSERT INTO worlds(name,owner_user_id,data) VALUES($1,$2,$3)',[key,socket.user.id,JSON.stringify(data)]);
          await client.query('COMMIT');
          socket.user.coins=Number(charged.rows[0].coins);
          cb({success:true,worldName:key,displayName:data.displayName,description:desc,coins:socket.user.coins});
          kwgProgressLater(socket.user.id);
          return;
        }catch(err){
          await client.query('ROLLBACK').catch(()=>{});
          if(err.code==='23505'){
            if(supplied)return cb({success:false,message:'That world already exists.'});
            continue;
          }
          throw err;
        }finally{client.release();}
      }
      cb({success:false,message:'Could not find an available random world name. Please retry.'});
    } catch(e){console.error('Create world:',e);cb({success:false,message:'Could not create world.'});}
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
      const badgeResult=await pool.query("SELECT appearance->'groupBadge' AS badge FROM users WHERE id=$1",[socket.user.id]);
      if(badgeResult.rows[0]?.badge)app.groupBadge=badgeResult.rows[0].badge;
      const cosmetics = await resolveAppearanceAssets(app);
      const equippedPetRow=await pool.query('SELECT pet_key FROM user_pet_equipment WHERE user_id=$1',[userId]);
      const storedPetKey=equippedPetRow.rows[0]?.pet_key||null;
      const petKey=null; // V24: companions temporarily disabled, keep stored equipment untouched.
      if (!socket.connected || !socket.user) throw new Error('Disconnected during world join.');
      socket.user.appearance = app;

      const previousWorld=playersBySocket.get(socket.id)?.worldName;
      if (previousWorld && previousWorld!==world.name) {
        socket.to(`world:${previousWorld}`).emit('player_left',socket.id);
        kwgAnnounce(previousWorld,`${socket.user.username} left the world.`,socket.user.id);
      }
      if (socket.data.worldName) socket.leave(`world:${socket.data.worldName}`);
      socket.join(`world:${world.name}`);
      socket.data.worldName = world.name;
      kwgServerTools.clear(); // Dispenser tools belong only to this world session.
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
        appearance: app, cosmetics, petKey, worldName: world.name,
        level:kwgLevelFromXP(Number((await pool.query('SELECT total_xp FROM user_xp_progress WHERE user_id=$1',[socket.user.id])).rows[0]?.total_xp||0)),
        runStartedAt:Date.now(),lastFinishAt:0,lastDeathAt:0
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
      kwgProgressLater(socket.user.id);
      try{await pool.query('UPDATE worlds SET plays=plays+1 WHERE id=$1',[world.id]);}
      catch(playError){console.error('Could not increment world plays:',playError);}
      kwgAnnounce(world.name,`${socket.user.username} joined the world.`,socket.user.id);
      cb({success:true,worldData:world.data,players,selfId:socket.id,selfSpawn,runStartedAt:p.runStartedAt,canEdit:canEditWorld(socket, world),selfAppearance:app,selfCosmetics:cosmetics,selfPetKey:petKey});
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

  // V48: Recover from lost/racing player_joined packets or late world loading.
  // The roster is scoped to the caller's active world and respects existing
  // two-way block privacy. No client can request a different world's roster.
  socket.on('get_world_players', async ({worldName} = {}, cb) => {
    if (typeof cb !== 'function') return;
    if (!requireAuth(socket,cb)) return;
    const p=playersBySocket.get(socket.id);
    const key=cleanWorldName(worldName);
    if(!p || !p.worldName || p.worldName!==key || socket.data.worldName!==key)
      return cb({success:false,message:'Join this world first.'});
    try {
      const peers=worldPeers(key,socket.id);
      const hiddenIds=await blockedPeers(socket.user.id,peers.map(peer=>peer.socket.user.id));
      // A peer may leave while the privacy query is in flight.
      const players={};
      for(const peer of peers){
        if(!peer.socket.connected || playersBySocket.get(peer.sid)!==peer.p || peer.p.worldName!==key)continue;
        players[peer.sid]=privatePlayer(peer.p,hiddenIds.has(Number(peer.socket.user.id)));
      }
      cb({success:true,worldName:key,players});
    } catch(e){console.error('World player roster:',e);cb({success:false,message:'Could not sync players.'});}
  });

  socket.on('leave_world', () => {
    kwgServerTools.clear();
    const p = playersBySocket.get(socket.id);
    if (p?.worldName) {
      socket.to(`world:${p.worldName}`).emit('player_left', socket.id);
      kwgAnnounce(p.worldName,`${p.username} left the world.`,socket.user?.id);
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

  // V26: Tool ownership is server-verified at the dispenser and only lasts
  // for this world session. PVP is opt-in per world, with range, cooldown,
  // aiming and wall checks. This is not a full authoritative combat engine.
  const kwgServerTools=new Set();
  const kwgShotAt={pistol:0,minigun:0,laser:0,ufo:0,balloon:0};
  let kwgPvpLaserTarget=null,kwgPvpLaserSince=0,kwgPvpLaserLastAt=0;
  socket.on('tool_pickup',async ({worldName,blockId}={},cb)=>{
    const player=playersBySocket.get(socket.id);
    const key=cleanWorldName(worldName);
    if(!player||player.worldName!==key||socket.data.worldName!==key||typeof blockId!=='string')return cb?.({success:false});
    try{
      const world=await getWorldByName(key),block=world?.data?.blocks?.[blockId];
      if(!block||block.actionType!=='tool_dispenser')return cb?.({success:false});
      const hx=Math.max(.5,Math.abs(Number(block.scaleX)||1)/2+.75),hy=Math.max(.5,Math.abs(Number(block.scaleY)||1)/2+2.5),hz=Math.max(.5,Math.abs(Number(block.scaleZ)||1)/2+.75);
      if(Math.abs(player.x-(Number(block.x)||0))>hx||Math.abs(player.y-(Number(block.y)||0))>hy||Math.abs(player.z-(Number(block.z)||0))>hz)return cb?.({success:false});
      const kind=['pistol','minigun','laser','ufo','balloon'].includes(block.toolKind)?block.toolKind:'pistol';
      kwgServerTools.add(kind);
      cb?.({success:true,kind});
    }catch(err){console.warn('Tool pickup:',err.message);cb?.({success:false});}
  });
  function kwgRayBoxDistance(o,d,box){
    let tmin=0,tmax=115;
    for(const axis of ['x','y','z']){
      if(Math.abs(d[axis])<1e-7){if(o[axis]<box['min'+axis.toUpperCase()]||o[axis]>box['max'+axis.toUpperCase()])return Infinity;continue;}
      const a=(box['min'+axis.toUpperCase()]-o[axis])/d[axis],b=(box['max'+axis.toUpperCase()]-o[axis])/d[axis];
      tmin=Math.max(tmin,Math.min(a,b));tmax=Math.min(tmax,Math.max(a,b));
      if(tmax<tmin)return Infinity;
    }
    return tmin;
  }
  socket.on('tool_hit_player',async ({worldName,targetId,toolKind,origin,direction}={})=>{
    if(toolKind==='balloon'||!kwgServerTools.has(toolKind)||!['pistol','minigun','laser','ufo'].includes(toolKind))return;
    const equipped=playersBySocket.get(socket.id)?.equippedTool;
    if(equipped!==toolKind)return;
    const shooter=playersBySocket.get(socket.id),target=playersBySocket.get(targetId),key=cleanWorldName(worldName);
    if(!shooter||!target||shooter.worldName!==key||target.worldName!==key||shooter.id===target.id||socket.data.worldName!==key)return;
    const now=Date.now(),interval=({pistol:360,minigun:90,laser:220,ufo:1200})[toolKind];
    if(now-kwgShotAt[toolKind]<interval)return;
    if(!origin||!direction||!['x','y','z'].every(k=>Number.isFinite(origin[k])&&Number.isFinite(direction[k])))return;
    const magnitude=Math.hypot(direction.x,direction.y,direction.z);
    if(magnitude<.9||magnitude>1.1)return;
    if(toolKind==='ufo'){
      if(Math.hypot(origin.x-shooter.x,origin.y-(shooter.y-.65),origin.z-shooter.z)>1.6)return;
      if(direction.y>-.985||Math.abs(direction.x)>.14||Math.abs(direction.z)>.14)return;
      if(shooter.y<2.1)return;
    }else if(Math.hypot(origin.x-shooter.x,origin.y-(shooter.y+1.5),origin.z-shooter.z)>8)return;
    const distance=Math.hypot(target.x-origin.x,target.y+1.1-origin.y,target.z-origin.z);
    if(distance>115||distance<.4)return;
    const toTarget={x:target.x-origin.x,y:target.y+1.1-origin.y,z:target.z-origin.z};
    const dot=(toTarget.x*direction.x+toTarget.y*direction.y+toTarget.z*direction.z)/distance;
    if(toolKind!=='ufo'&&dot<Math.cos(Math.atan2(1.2,Math.max(1,distance))))return;
    if(toolKind==='ufo'&&(Math.hypot(target.x-origin.x,target.z-origin.z)>2.85||target.y>origin.y+.2))return;
    try{
      const world=await getWorldByName(key);
      if(world?.data?.friendlyFire!==true)return;
      const targetBox={minX:target.x-.55,maxX:target.x+.55,minY:target.y-.2,maxY:target.y+2.45,minZ:target.z-.55,maxZ:target.z+.55};
       if(toolKind==='ufo'){targetBox.minX-=2.35;targetBox.maxX+=2.35;targetBox.minZ-=2.35;targetBox.maxZ+=2.35;}
       const hit=kwgRayBoxDistance(origin,direction,targetBox);
      if(!Number.isFinite(hit)||hit>115)return;
      for(const block of Object.values(world.data.blocks||{})){
        if(block.canCollide===false||block.actionType==='tool_dispenser')continue;
        const bx=Number(block.x)||0,by=Number(block.y)||0,bz=Number(block.z)||0;
        const hx=Math.max(.01,Math.abs(Number(block.scaleX)||1)/2),hy=Math.max(.01,Math.abs(Number(block.scaleY)||1)/2),hz=Math.max(.01,Math.abs(Number(block.scaleZ)||1)/2);
        const box={minX:bx-hx,maxX:bx+hx,minY:by-hy,maxY:by+hy,minZ:bz-hz,maxZ:bz+hz};
        if(kwgRayBoxDistance(origin,direction,box)<hit-.12)return;
      }
      kwgShotAt[toolKind]=now;
      if(toolKind!=='laser'){kwgPvpLaserTarget=null;kwgPvpLaserSince=0;}
      else if(kwgPvpLaserTarget!==targetId||now-kwgPvpLaserLastAt>650){kwgPvpLaserTarget=targetId;kwgPvpLaserSince=now;}
      if(toolKind==='laser')kwgPvpLaserLastAt=now;
      const laserRamp=toolKind==='laser'?Math.min(1,(now-kwgPvpLaserSince)/4700):0;
      const damage=toolKind==='ufo'?100:toolKind==='laser'?Math.round(2+6*laserRamp):toolKind==='minigun'?9:32;
      io.to(targetId).emit('tool_damage_taken',{damage,shooterPosition:{x:shooter.x,y:shooter.y,z:shooter.z}});
    }catch(err){console.warn('PVP hit validation:',err.message);}
  });


  // V39: Death invalidates server-side tool grants. A client may drop its own
  // grants at any time, but cannot affect another player's inventory.
  socket.on('kwg_tools_lost',({worldName}={})=>{
    const p=playersBySocket.get(socket.id),key=cleanWorldName(worldName);
    if(!p||p.worldName!==key||socket.data.worldName!==key)return;
    kwgServerTools.clear();p.equippedTool=null;
  });

  let kwgLastBalloonDrop=0;
  socket.on('kwg_balloon_drop',({worldName,origin}={})=>{
    const shooter=playersBySocket.get(socket.id),key=cleanWorldName(worldName),now=Date.now();
    if(!shooter||shooter.worldName!==key||socket.data.worldName!==key||
       !kwgServerTools.has('balloon')||shooter.equippedTool!=='balloon'||shooter.health<=0||
       now-kwgLastBalloonDrop<950||!origin||!['x','y','z'].every(k=>Number.isFinite(origin[k])))return;
    if(Math.hypot(origin.x-shooter.x,origin.z-shooter.z)>2||Math.abs(origin.y-(shooter.y-1.15))>2)return;
    kwgLastBalloonDrop=now;
    socket.to(`world:${key}`).emit('kwg_balloon_dropped',{origin});
  });
  let kwgLastBalloonBlast=0;
  socket.on('kwg_balloon_blast',async ({worldName,impact,origin}={})=>{
    const shooter=playersBySocket.get(socket.id),key=cleanWorldName(worldName);
    if(!shooter||shooter.worldName!==key||socket.data.worldName!==key||
       !kwgServerTools.has('balloon')||shooter.equippedTool!=='balloon'||shooter.health<=0)return;
    const now=Date.now();if(now-kwgLastBalloonBlast<1000)return;
    if(!impact||!origin||!['x','y','z'].every(k=>Number.isFinite(impact[k])&&Number.isFinite(origin[k])))return;
    // Prevent arbitrary map-wide explosions. Bombs only drop vertically from
    // the pilot and must fall below the balloon's launch point.
    if(Math.hypot(origin.x-shooter.x,origin.z-shooter.z)>10||
       Math.hypot(impact.x-origin.x,impact.z-origin.z)>1.0||
       origin.y<impact.y+1.2||origin.y>shooter.y+1.2||origin.y<shooter.y-13)return;
    try{
      const world=await getWorldByName(key);
      if(!world?.data||world.data.friendlyFire!==true)return;
      // Confirm a collidable surface at the reported landing point.
      const blocks=Object.values(world.data.blocks||{});
      const landed=blocks.some(b=>{
        if(b.canCollide===false||b.actionType==='tool_dispenser'||b.actionType==='enemy_spawner')return false;
        const x=Number(b.x)||0,y=Number(b.y)||0,z=Number(b.z)||0;
        const hx=Math.max(.05,Math.abs(Number(b.scaleX)||1)/2),hy=Math.max(.05,Math.abs(Number(b.scaleY)||1)/2),hz=Math.max(.05,Math.abs(Number(b.scaleZ)||1)/2);
        return Math.abs(impact.x-x)<hx+.3&&Math.abs(impact.z-z)<hz+.3&&Math.abs(impact.y-(y+hy+.18))<.9;
      });
      if(!landed)return;
      kwgLastBalloonBlast=now;
      for(const target of playersBySocket.values()){
        if(target.id===shooter.id||target.worldName!==key||target.health<=0)continue;
        const dist=Math.hypot(target.x-impact.x,target.y+1-impact.y,target.z-impact.z);
        if(dist>=4.2)continue;
        const damage=Math.max(8,Math.round(70*(1-dist/4.2)));
        io.to(target.id).emit('tool_damage_taken',{damage,shooterPosition:{x:impact.x,y:impact.y,z:impact.z}});
      }
    }catch(err){console.warn('Balloon blast validation:',err.message);}
  });

  // Stomp events are room-scoped and validated against saved spawner settings.
  // Movement/AI remain client-side in this version; defeat broadcasts keep
  // active visitors' respawn timers consistent.
  let lastEnemyStomp=0;
  socket.on('enemy_stomped',async ({worldName,spawnerId,index,method}={})=>{
    if(!requireAuth(socket))return;
    const p=playersBySocket.get(socket.id);
    const key=cleanWorldName(worldName);
    if(!p||p.worldName!==key||socket.data.worldName!==key)return;
    if(typeof spawnerId!=='string'||spawnerId.length>160||!Number.isInteger(index)||index<0||index>=12)return;
    const now=Date.now();
    if(now-lastEnemyStomp<180)return;
    lastEnemyStomp=now;
    try{
      const world=await getWorldByName(key);
      const block=world?.data?.blocks?.[spawnerId];
      if(!block||block.actionType!=='enemy_spawner')return;
      normalizeEnemySpawner(block);
      // Hops is stomp-immune but can still be defeated with a collected tool.
      // This remains client-simulated combat, not authoritative hit validation.
      if(method==='weapon'){
        if(!kwgServerTools.size||!p.equippedTool||!kwgServerTools.has(p.equippedTool))return;
      }else if(block.enemyKillable===false||block.enemyCharacter==='hops')return;
      if(index>=block.enemyCount)return;
      const dx=p.x-(Number(block.x)||0),dz=p.z-(Number(block.z)||0);
      const maxRange=block.noticeRange+5;
      if(Math.hypot(dx,dz)>maxRange||Math.abs(p.y-(Number(block.y)||0))>maxRange+5)return;
      socket.to(`world:${key}`).emit('enemy_stomped',{worldName:key,spawnerId,index});
    }catch(err){console.warn('Enemy stomp validation:',err.message);}
  });

  // V42: a player's own best is available even when outside the Top 50.
  socket.on('get_world_player_score',async ({worldName}={},cb)=>{
    if(!requireAuth(socket,cb)||typeof cb!=='function')return;
    const p=playersBySocket.get(socket.id),key=cleanWorldName(worldName);
    if(!p||p.worldName!==key)return cb({success:false,message:'Join this world first.'});
    try{
      const world=await getWorldByName(key);
      if(!world)return cb({success:false,message:'World not found.'});
      const mode=kwgLevelType(world.data);
      let bestScore=null;
      if(mode!=='casual'){
        const r=await pool.query('SELECT best_score FROM world_level_scores WHERE world_id=$1 AND user_id=$2 AND mode=$3',[world.id,socket.user.id,mode]);
        if(r.rows.length)bestScore=Number(r.rows[0].best_score);
      }
      cb({success:true,mode,bestScore,runStartedAt:p.runStartedAt});
    }catch(e){console.error('Player score:',e);cb({success:false,message:'Could not load personal score.'});}
  });

  socket.on('get_world_leaderboard',async ({worldName}={},cb)=>{
    if(!requireAuth(socket,cb)||typeof cb!=='function')return;
    const p=playersBySocket.get(socket.id),key=cleanWorldName(worldName);
    if(!p||p.worldName!==key)return cb({success:false,message:'Join the world first.'});
    try{
      const world=await getWorldByName(key),mode=kwgLevelType(world?.data);
      if(!world)return cb({success:false,message:'World not found.'});
      if(mode==='casual')return cb({success:true,mode,entries:[]});
      const order=mode==='speed'?'ASC':'DESC';
      const result=await pool.query(`SELECT u.username,s.user_id,s.best_score AS score FROM world_level_scores s
        JOIN users u ON u.id=s.user_id WHERE s.world_id=$1 AND s.mode=$2
        ORDER BY s.best_score ${order},s.updated_at ASC LIMIT 50`,[world.id,mode]);
      const hidden=await blockedPeers(socket.user.id,result.rows.map(r=>r.user_id));
      cb({success:true,mode,entries:result.rows.map(r=>({username:hidden.has(Number(r.user_id))?'Hidden User':r.username,score:Number(r.score)}))});
    }catch(e){console.error('Leaderboard:',e);cb({success:false,message:'Could not load leaderboard.'});}
  });
  socket.on('world_finish',async ({worldName}={},cb)=>{
    if(!requireAuth(socket,cb)||typeof cb!=='function')return;
    const p=playersBySocket.get(socket.id),key=cleanWorldName(worldName),now=Date.now();
    if(!p||p.worldName!==key)return cb({success:false,message:'Join this world first.'});
    if(now-(p.lastFinishAt||0)<2800)return cb({success:false,message:'Finish is on cooldown.'});
    try{
      const world=await getWorldByName(key);
      if(!world||!kwgNearFinish(p,world.data.blocks))return cb({success:false,message:'Touch the Finish block to complete the run.'});
      const mode=kwgLevelType(world.data),elapsed=kwgElapsed(p);
      // A minimum duration avoids zero-time entries on maps with Finish at spawn.
      const score=mode==='speed'?Math.max(250,elapsed):mode==='survival'?elapsed:1;
      p.lastFinishAt=now;
      const result=await kwgSaveLevelScore(world,socket.user.id,mode,score);
      // Finish XP is independent of per-world leaderboard resets.
      try{await kwgCreditFinish(socket.user.id,mode);}catch(err){console.error('Finish achievement:',err);}
      p.runStartedAt=now;
      const scoreText=mode==='wins'?`${result.score} wins`:mode==='speed'?`${(score/1000).toFixed(2)}s`:mode==='survival'?`${Math.floor(score/1000)}s survived`:'';
      kwgAnnounce(key,`${p.username} reached the finish${scoreText?' — '+scoreText:''}!${result.newRecord?' NEW HIGH SCORE!':''}`,socket.user.id);
      cb({success:true,mode,score:result.score,newRecord:result.newRecord,bestScore:result.bestScore});
    }catch(e){console.error('Finish:',e);cb({success:false,message:'Could not record finish.'});}
  });
  socket.on('player_died',async ({worldName}={})=>{
    if(!requireAuth(socket))return;
    const p=playersBySocket.get(socket.id),key=cleanWorldName(worldName),now=Date.now();
    if(!p||p.worldName!==key||now-(p.lastDeathAt||0)<1800)return;
    p.lastDeathAt=now;
    kwgAnnounce(key,`${p.username} died.`,socket.user.id);
    try{
      const world=await getWorldByName(key);
      if(world&&kwgLevelType(world.data)==='survival'){
        const elapsed=kwgElapsed(p);
        const result=await kwgSaveLevelScore(world,socket.user.id,'survival',elapsed);
        if(result.newRecord)kwgAnnounce(key,`${p.username} set a NEW SURVIVAL HIGH SCORE — ${Math.floor(elapsed/1000)}s!`,socket.user.id);
      }
    }catch(e){console.error('Survival score:',e);}
  });
  socket.on('player_respawned',({worldName}={})=>{
    if(!requireAuth(socket))return;
    const p=playersBySocket.get(socket.id),key=cleanWorldName(worldName);
    if(!p||p.worldName!==key)return;
    // A checkpoint death is part of the same Speed attempt. Survival is a
    // separate life-based attempt and still resets after a death.
    getWorldByName(key).then(world=>{
      if(world&&kwgLevelType(world.data)==='survival'&&playersBySocket.get(socket.id)===p&&p.worldName===key)
        p.runStartedAt=Date.now();
    }).catch(e=>console.error('Respawn timer:',e));
  });
  socket.on('world_restart',async ({worldName}={},cb)=>{
    if(!requireAuth(socket,cb))return;
    const p=playersBySocket.get(socket.id),key=cleanWorldName(worldName);
    if(!p||p.worldName!==key)return cb&&cb({success:false,message:'Join this world first.'});
    p.runStartedAt=Date.now();
    cb&&cb({success:true,runStartedAt:p.runStartedAt});
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
    // Cosmetic front-flip pose only; never affects authoritative position.
    p.stompAngle = (typeof data.stompAngle==='number' && Number.isFinite(data.stompAngle))
      ? Math.max(-8,Math.min(8,data.stompAngle)) : 0;
    p.ragdollPose=(typeof data.ragdollPose==='number'&&Number.isFinite(data.ragdollPose))
      ?Math.max(0,Math.min(1,data.ragdollPose)):0;
    for(const key of ['ragdollX','ragdollY','ragdollZ'])
      p[key]=(typeof data[key]==='number'&&Number.isFinite(data[key]))?Math.max(-4,Math.min(4,data[key])):0;
    p.health=(typeof data.health==='number'&&Number.isFinite(data.health))?Math.max(0,Math.min(100,Math.round(data.health))):100;
    // Never broadcast a held weapon that this connection hasn't collected.
    p.equippedTool=['pistol','minigun','laser','ufo','balloon'].includes(data.equippedTool)&&kwgServerTools.has(data.equippedTool)&&p.health>0?data.equippedTool:null;
    socket.to(`world:${p.worldName}`).emit('player_moved',{
      id:p.id,x:p.x,y:p.y,z:p.z,rotationY:p.rotationY,walkClock:p.walkClock,
      verticalVelocity:p.verticalVelocity,isMoving:p.isMoving,isGrounded:p.isGrounded,
      stompAngle:p.stompAngle,ragdollPose:p.ragdollPose,
      ragdollX:p.ragdollX,ragdollY:p.ragdollY,ragdollZ:p.ragdollZ,health:p.health,
      equippedTool:p.equippedTool
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
              // Preserve standard and enemy spawner types, with validated enemy limits.
              blockData.actionType=['normal','kill','checkpoint','finish','spawn','enemy_spawner','health','tool_dispenser'].includes(blockData.actionType)?blockData.actionType:'normal';
              blockData.material=['grid','brick','wood'].includes(blockData.material)?blockData.material:'grid';
              normalizeEnemySpawner(blockData);
              kwgPreserveApprovedDecals(blockData,data.blocks[blockData.id]);
               if(blockData.actionType==='health')blockData.healAmount=Math.max(1,Math.min(100,Math.round(Number(blockData.healAmount)||25)));
              if(blockData.actionType==='tool_dispenser')blockData.toolKind=['pistol','minigun','laser','ufo','balloon'].includes(blockData.toolKind)?blockData.toolKind:'pistol';
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
            const allowed=['skyColor','spawnPoint','friendlyFire','brightness','saturation','resolution','lightColor','lightDirection'];
            const next={};
            for(const k of allowed)if(Object.prototype.hasOwnProperty.call(settings,k))next[k]=settings[k];
            if(next.skyColor&&!validColor(next.skyColor))delete next.skyColor;
            if(next.lightColor&&!validColor(next.lightColor))delete next.lightColor;
            if(next.brightness!==undefined)next.brightness=Math.max(.4,Math.min(2,Number(next.brightness)||1));
            if(next.saturation!==undefined)next.saturation=Math.max(0,Math.min(2,Number(next.saturation)||0));
            if(next.resolution!==undefined)next.resolution=['120p','240p','480p','720p','1080p'].includes(next.resolution)?next.resolution:'1080p';
            if(next.lightDirection!==undefined)next.lightDirection=['east','overhead','west','north','south'].includes(next.lightDirection)?next.lightDirection:({morning:'east',noon:'overhead',evening:'west'}[next.lightDirection]||'overhead');
            if(next.cloudsEnabled!==undefined)next.cloudsEnabled=!!next.cloudsEnabled;
            if(next.friendlyFire!==undefined)next.friendlyFire=next.friendlyFire===true;
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
          // Only supported block types and three current
          // materials may be saved by clients. Existing legacy worlds are
          // not rewritten on load; their old flags stay intact until edited.
          blockData.actionType = ['normal','kill','checkpoint','finish','spawn','enemy_spawner','health','tool_dispenser'].includes(blockData.actionType) ? blockData.actionType : 'normal';
          blockData.material = ['grid','brick','wood'].includes(blockData.material) ? blockData.material : 'grid';
          normalizeEnemySpawner(blockData);
          kwgPreserveApprovedDecals(blockData,data.blocks[blockData.id]);
           if(blockData.actionType==='health')blockData.healAmount=Math.max(1,Math.min(100,Math.round(Number(blockData.healAmount)||25)));
          if(blockData.actionType==='tool_dispenser')blockData.toolKind=['pistol','minigun','laser','ufo','balloon'].includes(blockData.toolKind)?blockData.toolKind:'pistol';
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

  // V34: server-owned image reviews. Pending/rejected images are NEVER public.
  socket.on('kwg_image_submit',async ({worldName,kind,blockId,side,mimeType,fileName,bytes:raw}={},cb)=>{
    if(!requireAuth(socket,cb))return;
    const key=cleanWorldName(worldName);
    if(socket.data.worldName!==key)return cb?.({success:false,message:'Join the world before uploading.'});
    if(!['sky','decal'].includes(kind)||!['front','back','left','right','top','bottom'].includes(side))return cb?.({success:false,message:'Invalid image target.'});
    const bytes=fileBufferFromSocket(raw);
    if(!kwgValidImageBytes(bytes,mimeType))return cb?.({success:false,message:'Use PNG, JPEG, or WebP under 1.5 MB.'});
    if(!KWG_IMAGE_MODERATION_KEY||!SUPABASE_URL||!SUPABASE_SERVICE_ROLE_KEY)return cb?.({success:false,message:'Image moderation/storage not configured: set OPENAI_API_KEY and Supabase storage environment variables.'});
    // Display-only name; never used as a storage path or an approval signal.
    const safeFileName=String(fileName||'Image').replace(/[\x00-\x1f\x7f<>]/g,'').replace(/[\/\\]/g,'_').trim().slice(0,80)||'Image';
    const token=crypto.randomUUID();let worldId;
    try{
      await queueWorldSave(key,async()=>{
        const world=await getWorldByName(key);
        if(!world||!canEditWorld(socket,world))throw new Error('Not allowed to upload to this world.');
        worldId=world.id;
        if(kind==='decal'&&!world.data.blocks?.[blockId])throw new Error('Select a saved part first.');
        const review={status:'pending',token,fileName:safeFileName};
        if(kind==='sky'){world.data.skyboxFaces=world.data.skyboxFaces||{};world.data.skyboxFaces[side]=review;}
        else{const block=world.data.blocks[blockId];block.decals=block.decals||{};block.decals[side]=review;}
        await pool.query('UPDATE worlds SET data=$1,updated_at=NOW() WHERE id=$2',[JSON.stringify(world.data),world.id]);
        io.to(`world:${key}`).emit('kwg_image_review_updated',{kind,blockId,side,review});
      });
      cb?.({success:true,status:'pending'});
    }catch(e){return cb?.({success:false,message:e.message||'Could not submit image.'});}
    // Complete review asynchronously; compare token so an older result cannot
    // overwrite a newer image or a removal. If review fails, stay non-public.
    (async()=>{
      let approved=false,url=null,failed=false;
      try{approved=await kwgModerateWorldImage(bytes,mimeType);
        if(approved)url=await kwgUploadApprovedWorldImage(worldId,bytes,mimeType);
      }catch(e){failed=true;console.error('KWG world image review:',e.message);}
      try{await queueWorldSave(key,async()=>{
        const world=await getWorldByName(key);if(!world)return;
        const record=kind==='sky'?world.data.skyboxFaces?.[side]:world.data.blocks?.[blockId]?.decals?.[side];
        if(record?.token!==token||record.status!=='pending')return;
        const review={status:failed?'error':approved?'approved':'rejected',token,fileName:record.fileName||'Image'};
        if(url)review.url=url;
        if(kind==='sky'){world.data.skyboxFaces=world.data.skyboxFaces||{};world.data.skyboxFaces[side]=review;}
        else world.data.blocks[blockId].decals[side]=review;
        await pool.query('UPDATE worlds SET data=$1,updated_at=NOW() WHERE id=$2',[JSON.stringify(world.data),world.id]);
        io.to(`world:${key}`).emit('kwg_image_review_updated',{kind,blockId,side,review});
      });}catch(e){console.error('KWG image review persistence:',e.message);}
    })();
  });
  socket.on('kwg_image_clear',async ({worldName,kind,blockId,side}={},cb)=>{
    if(!requireAuth(socket,cb))return;
    const key=cleanWorldName(worldName);
    if(socket.data.worldName!==key)return cb?.({success:false,message:'Join the world first.'});
    if(!['sky','decal'].includes(kind)||!['front','back','left','right','top','bottom'].includes(side))return cb?.({success:false,message:'Invalid image target.'});
    try{await queueWorldSave(key,async()=>{
      const world=await getWorldByName(key);if(!world||!canEditWorld(socket,world))throw new Error('Not allowed to edit images.');
      if(kind==='sky'&&world.data.skyboxFaces)delete world.data.skyboxFaces[side];
      else if(world.data.blocks?.[blockId]?.decals)delete world.data.blocks[blockId].decals[side];
      await pool.query('UPDATE worlds SET data=$1,updated_at=NOW() WHERE id=$2',[JSON.stringify(world.data),world.id]);
      io.to(`world:${key}`).emit('kwg_image_review_updated',{kind,blockId,side,review:null});
    });cb?.({success:true});}catch(e){cb?.({success:false,message:e.message});}
  });

  socket.on('world_settings_update', async ({worldName,settings}, cb) => {
    if (!requireAuth(socket)) return;
    if (socket.data.worldName !== cleanWorldName(worldName) || !settings) return;
    try {
      const world = await getWorldByName(worldName);
      if (!world) return cb && cb({success:false,message:'World not found.'});
      if (!canEditWorld(socket, world)) return cb && cb({success:false,message:'Only the world owner or an admin can edit this world.'});
      const allowed = ['skyColor','spawnPoint','friendlyFire','brightness','saturation','resolution','lightColor','lightDirection'];
      const next = {};
      for (const k of allowed) if (Object.prototype.hasOwnProperty.call(settings,k)) next[k] = settings[k];
      if (next.skyColor && !validColor(next.skyColor)) delete next.skyColor;
      if (next.lightColor && !validColor(next.lightColor)) delete next.lightColor;
      if(next.brightness!==undefined)next.brightness=Math.max(.4,Math.min(2,Number(next.brightness)||1));
      if(next.saturation!==undefined)next.saturation=Math.max(0,Math.min(2,Number(next.saturation)||0));
      if(next.resolution!==undefined)next.resolution=['120p','240p','480p','720p','1080p'].includes(next.resolution)?next.resolution:'1080p';
      if(next.lightDirection!==undefined)next.lightDirection=['east','overhead','west','north','south'].includes(next.lightDirection)?next.lightDirection:({morning:'east',noon:'overhead',evening:'west'}[next.lightDirection]||'overhead');
      if (next.cloudsEnabled !== undefined) next.cloudsEnabled = !!next.cloudsEnabled;
      if (next.friendlyFire !== undefined) next.friendlyFire = next.friendlyFire === true;
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

  socket.on('world_info_update', async ({worldName,displayName,description,thumbnailData,levelType,confirmLeaderboardReset=false} = {}, cb) => {
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
          data.thumbnailAuto=false;
        }
        const previousMode=kwgLevelType(data);
        const newMode=['casual','speed','survival','wins'].includes(levelType)?levelType:previousMode;
        const leaderstatsReset=newMode!==previousMode;
        if(leaderstatsReset&&confirmLeaderboardReset!==true)
          return {success:false,message:'Confirm the leaderboard reset before changing the level type.'};
        data.displayName=title;
        data.description=desc;
        data.levelType=newMode;
        data.thumbnailUrl=thumbnailUrl;
        // Metadata update and score deletion must succeed or fail together.
        const client=await pool.connect();
        try{
          await client.query('BEGIN');
          await client.query('UPDATE worlds SET data=$1,updated_at=NOW() WHERE id=$2',[JSON.stringify(data),world.id]);
          if(leaderstatsReset)await client.query('DELETE FROM world_level_scores WHERE world_id=$1',[world.id]);
          await client.query('COMMIT');
        }catch(error){await client.query('ROLLBACK');throw error;}
        finally{client.release();}
        // A newly selected scoring mode starts a fresh clock for every player.
        const newRunStartedAt=leaderstatsReset?Date.now():null;
        if(leaderstatsReset)for(const peer of worldPeers(key))peer.p.runStartedAt=newRunStartedAt;
        io.to(`world:${key}`).emit('world_info_updated',{worldName:key,displayName:title,description:desc,levelType:data.levelType,thumbnailUrl,thumbnailAuto:data.thumbnailAuto===true,runStartedAt:newRunStartedAt});
        if(leaderstatsReset)io.to(`world:${key}`).emit('world_leaderboard_changed',{worldName:key,reset:true});
        return {success:true,displayName:title,description:desc,levelType:data.levelType,thumbnailUrl,thumbnailAuto:data.thumbnailAuto===true,leaderstatsReset};
      });
      cb && cb(result);
    } catch(e){console.error('World info update:',e);cb && cb({success:false,message:e.clientMessage||'Could not save world info or thumbnail. Check thumbnail storage configuration.'});}
  });

  // Owner-only destructive reset. All modes are cleared, not just the
  // currently active mode; the server never trusts client-supplied user IDs.
  socket.on('reset_world_leaderstats',async ({worldName}={},cb)=>{
    if(!requireAuth(socket,cb)||typeof cb!=='function')return;
    const key=cleanWorldName(worldName);
    if(socket.data.worldName!==key)return cb({success:false,message:'Join this world before resetting scores.'});
    try{
      const result=await queueWorldSave(key,async()=>{
        const world=await getWorldByName(key);
        if(!world)return {success:false,message:'World not found.'};
        if(!canEditWorld(socket,world))return {success:false,message:'Only the world owner or an admin can reset scores.'};
        const deleted=await pool.query('DELETE FROM world_level_scores WHERE world_id=$1',[world.id]);
        io.to(`world:${key}`).emit('world_leaderboard_changed',{worldName:key,reset:true});
        return {success:true,deleted:deleted.rowCount};
      });
      cb(result);
    }catch(error){console.error('Leaderboard reset:',error);cb({success:false,message:'Could not reset leaderboard scores.'});}
  });

  // World owners can edit display metadata directly from the Worlds page.
  // The internal world key remains stable so existing visits/likes are preserved.
  socket.on('update_owned_world_info',async ({worldName,displayName,description}={},cb)=>{
    if(!requireAuth(socket,cb))return;
    if(typeof cb!=='function')return;
    const key=cleanWorldName(worldName);
    const title=filterKWGUserText(String(displayName||'').trim());
    const desc=filterKWGUserText(String(description||'').trim());
    if(!key||!title||title.length>40||/[\x00-\x1f\x7f]/.test(title))return cb({success:false,message:'Name must be 1–40 characters.'});
    if(desc.length>300||/[\x00-\x08\x0b\x0c\x0e-\x1f]/.test(desc))return cb({success:false,message:'Description must be 300 characters or fewer.'});
    try{
      const result=await queueWorldSave(key,async()=>{
        const world=await getWorldByName(key);
        if(!world)return {success:false,message:'World not found.'};
        if(Number(world.owner_user_id)!==Number(socket.user.id))return {success:false,message:'Only the owner can edit this world.'};
        const data=world.data||{};
        let thumbnailUrl=data.thumbnailUrl||'';
        data.displayName=title;data.description=desc;data.thumbnailUrl=thumbnailUrl;
        await pool.query('UPDATE worlds SET data=$1,updated_at=NOW() WHERE id=$2',[JSON.stringify(data),world.id]);
        io.to(`world:${key}`).emit('world_info_updated',{worldName:key,displayName:title,description:desc,thumbnailUrl,thumbnailAuto:data.thumbnailAuto===true});
        return {success:true,displayName:title,description:desc,thumbnailUrl,thumbnailAuto:data.thumbnailAuto===true};
      });
      cb(result);
    }catch(e){console.error('Owner world edit error:',e);cb({success:false,message:e.clientMessage||'Could not save world info.'});}
  });

  // Auto thumbnails are captured by the world owner's browser from spawn view.
  // Never allow a visitor to upload a thumbnail or overwrite a manually chosen one.
  socket.on('set_auto_world_thumbnail',async ({worldName,thumbnailData}={},cb)=>{
    if(!requireAuth(socket,cb))return;
    if(typeof cb!=='function')return;
    const key=cleanWorldName(worldName);
    if(!key||socket.data.worldName!==key)return cb({success:false,message:'Join your world to generate its thumbnail.'});
    try{
      const result=await queueWorldSave(key,async()=>{
        const world=await getWorldByName(key);
        if(!world)return {success:false,message:'World not found.'};
        if(Number(world.owner_user_id)!==Number(socket.user.id))return {success:false,message:'Only the owner can generate a thumbnail.'};
        const data=world.data||{};
        if(data.thumbnailUrl&&!data.thumbnailAuto)return {success:true,thumbnailUrl:data.thumbnailUrl,thumbnailAuto:false};
        const thumbnailUrl=await uploadWorldThumbnail(world.id,thumbnailData);
        data.thumbnailUrl=thumbnailUrl;
        data.thumbnailAuto=true;
        await pool.query('UPDATE worlds SET data=$1,updated_at=NOW() WHERE id=$2',[JSON.stringify(data),world.id]);
        io.to(`world:${key}`).emit('world_info_updated',{worldName:key,displayName:data.displayName||key,description:data.description||'',thumbnailUrl,thumbnailAuto:true});
        return {success:true,thumbnailUrl,thumbnailAuto:true};
      });
      cb(result);
    }catch(err){console.warn('Automatic world thumbnail:',err);cb({success:false,message:err.clientMessage||'Automatic thumbnail could not be saved.'});}
  });

  socket.on('save_appearance', async (appearance, cb) => {
    if (!requireAuth(socket, cb)) return;
    try {
      const app = await validateAppearanceForUser(socket.user.id, appearance);
      const badgeRow=await pool.query("SELECT appearance->'groupBadge' AS badge FROM users WHERE id=$1",[socket.user.id]);
      if(badgeRow.rows[0]?.badge)app.groupBadge=badgeRow.rows[0].badge;
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
    if(typeof cb==='function')return cb({success:true,pets:[],owned:[],equippedPet:null});
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
    if(typeof cb==='function')return cb({success:false,message:'Pets are temporarily unavailable.'});
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
    if(typeof cb==='function')return cb({success:false,message:'Pets are temporarily unavailable.'});
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
                 (created_by IS NOT NULL) AS is_uploaded,
                 COALESCE((SELECT username FROM users WHERE id=store_items.created_by),'KWG') AS creator_username
          FROM store_items WHERE category IN ('hair','hats','heads','eyes','mouth','hat','head_shape') AND ($1::boolean OR is_visible=true) AND (asset_kind <> 'avatar_glb' OR $1::boolean)
          ORDER BY category ASC,
                   CASE WHEN asset_kind='procedural' THEN COALESCE((metadata->>'styleIndex')::int,0) ELSE 9999 END ASC,
                   CASE WHEN asset_kind='procedural' THEN COALESCE((metadata->>'colorIndex')::int,0) ELSE 9999 END ASC,
                   name ASC, id ASC
        `,[!!socket.user.isAdmin]),
        pool.query(`
          SELECT s.id,s.category,s.name,s.price,s.asset_url,s.asset_kind,s.metadata,s.is_visible,
                 (s.created_by IS NOT NULL) AS is_uploaded,
                 COALESCE((SELECT username FROM users WHERE id=s.created_by),'KWG') AS creator_username
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
    if (typeof cb === 'function') cb({success:false,message:'Avatar marketplace is retired.'});
    return;
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

  // Item Creator administrative drafts: editable mesh primitives or pixel painting.
  socket.on('item_creator_save_draft', async (payload={},cb)=>{
    if(!requireAdmin(socket,cb))return;
    if(typeof cb!=='function')return;
    const category=String(payload.category||'');
    const name=String(payload.name||'').trim().slice(0,40);
    const document=payload.document;
    if(!STORE_CATEGORIES.has(category)||!name||!document||typeof document!=='object')return cb({success:false,message:'Invalid item draft.'});
    const raw=JSON.stringify(document);
    if(raw.length>220000)return cb({success:false,message:'Draft exceeds 220 KB.'});
    try{
      const id=Number(payload.id);
      let r;
      if(Number.isSafeInteger(id)&&id>0){
        r=await pool.query('UPDATE item_creator_drafts SET name=$1,category=$2,document=$3::jsonb,updated_at=NOW() WHERE id=$4 AND owner_id=$5 RETURNING id',[name,category,raw,id,socket.user.id]);
        if(!r.rowCount)return cb({success:false,message:'Draft not found.'});
      }else{
        r=await pool.query('INSERT INTO item_creator_drafts(owner_id,name,category,document) VALUES($1,$2,$3,$4::jsonb) RETURNING id',[socket.user.id,name,category,raw]);
      }
      cb({success:true,id:Number(r.rows[0].id)});
    }catch(e){console.error(e);cb({success:false,message:'Could not save draft.'});}
  });
  socket.on('item_creator_list_drafts',async(cb)=>{
    if(!requireAdmin(socket,cb))return;
    try{const r=await pool.query('SELECT id,name,category,document,updated_at FROM item_creator_drafts WHERE owner_id=$1 ORDER BY updated_at DESC LIMIT 100',[socket.user.id]);cb({success:true,drafts:r.rows});}
    catch(e){console.error(e);cb({success:false,message:'Could not load drafts.'});}
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
      const slotByCategory={eyes:'eyesItemId',mouth:'mouthItemId',torso_decal:'torsoDecalItemId',hat:'hatItemId',head_shape:'headShapeItemId',hair:'hairItemId',hats:'hatsItemId',heads:'headsItemId',skin:'skinItemId',tops:'topsItemId',bottoms:'bottomsItemId',shoes:'shoesItemId',flightsuits:'flightsuitsItemId'};
      const slots=new Set([slotByCategory[deleted.category]].filter(Boolean));
      if(deleted.category==='heads')slots.add('headShapeItemId');
      if(deleted.category==='hats')slots.add('hatItemId');
      for(const slot of slots)await client.query(`
        UPDATE users SET appearance=appearance-$2::text
        WHERE (appearance->>$2::text)=$1::text
      `,[itemId,slot]);
      await client.query('DELETE FROM store_items WHERE id=$1',[itemId]);
      await client.query('COMMIT');
      // Update cached online appearances too; deleted items cannot be equipped again.
      for(const peer of io.sockets.sockets.values()){
        let changed=false;
        if(peer.user?.appearance)for(const slot of slots){if(Number(peer.user.appearance[slot])===itemId){peer.user.appearance[slot]=null;changed=true;}}
        const player=playersBySocket.get(peer.id);
        if(player){if(player.appearance)for(const slot of slots)if(Number(player.appearance[slot])===itemId){player.appearance[slot]=null;changed=true;}
          if(changed&&player.cosmetics)delete player.cosmetics[deleted.category];}
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
        if(/^(eyes|mouth|torso_decal|hat|head_shape|hair|hats|heads|skin|tops|bottoms|shoes|flightsuits)\/\d+-[a-f0-9]{16}\.(png|jpg|webp|glb)$/.test(key)){
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

  socket.on('create_avatar_item', async (payload = {}, cb) => {
    if (typeof cb === 'function') cb({success:false,message:'Avatar marketplace is retired.'});
    return;
    if (!requireAuth(socket, cb)) return;
    try {
      const category = String(payload.category || '').trim();
      const name = filterKWGUserText(String(payload.name || '').trim().slice(0, 40));
      const price = Number(payload.price);
      if (!['hair','hats','heads','eyes','mouth'].includes(category)) return cb({success:false,message:'Choose hats, hair, heads, eyes, or mouths.'});
      if (!name) return cb({success:false,message:'Item name is required.'});
      if (!Number.isInteger(price) || price < 0 || price > 100000000) return cb({success:false,message:'Price must be a whole number of coins.'});
      if(socket.data.lastAvatarPublishAt&&Date.now()-socket.data.lastAvatarPublishAt<20000)
        return cb({success:false,message:'Wait 20 seconds between item uploads.'});
      socket.data.lastAvatarPublishAt=Date.now();
      const buffer = fileBufferFromSocket(payload.fileData);
      if (!buffer || !buffer.length) return cb({success:false,message:'Choose a file to upload.'});
      if (!storeStorageConfigured()) {
        return cb({success:false,message:'Store uploads need SUPABASE_URL and SUPABASE_SERVICE_ROLE_KEY configured on Render first.'});
      }

      const metadata = {...cleanUploadMeta(category, payload.metadata || {}), distribution:'store', creatorVersion:2};
      // Images are public only after the server has approved them.
      if(['eyes','mouth'].includes(category)){
        const mime=String(payload.mimeType||'').toLowerCase();
        if(!kwgValidImageBytes(buffer,mime))return cb({success:false,message:'Invalid image or image is too large (1.5 MB max).'});
        if(!await kwgModerateWorldImage(buffer,mime))return cb({success:false,message:'Image was not approved for the store.'});
      }else{
        // GLB v2 header, declared length, and bounded upload. Reject malformed binary.
        if(buffer.length<20||buffer.length>8*1024*1024||buffer.toString('ascii',0,4)!=='glTF'||buffer.readUInt32LE(4)!==2||buffer.readUInt32LE(8)!==buffer.length)
          return cb({success:false,message:'Invalid 3D model. Export a valid GLB (max 8 MB).'});
        // Reject GLB files with external asset references; all geometry/textures must be self-contained.
        const jsonSize=buffer.readUInt32LE(12),jsonType=buffer.toString('ascii',16,20);
        if(jsonType!=='JSON'||jsonSize<2||jsonSize>buffer.length-20)return cb({success:false,message:'Invalid GLB JSON chunk.'});
        let document;
        try{document=JSON.parse(buffer.toString('utf8',20,20+jsonSize));}catch{return cb({success:false,message:'Invalid GLB model JSON.'});}
        const external=[...(document.buffers||[]),...(document.images||[])].some(a=>a.uri&&!String(a.uri).startsWith('data:'));
        if(external)return cb({success:false,message:'Models must contain their own textures and geometry.'});

      }
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
      const assetKind = String(payload.fileName||'').toLowerCase().endsWith('.glb') ? 'glb' : 'image';
      const r = await pool.query(`
        INSERT INTO store_items(category,name,price,asset_url,asset_kind,metadata,is_visible,created_by)
        VALUES($1,$2,$3,$4,$5,$6,$7,$8)
        RETURNING id,category,name,price,asset_url,asset_kind,metadata,is_visible
      `, [category,name,price,assetUrl,assetKind,JSON.stringify(metadata),true,socket.user.id]);
      await pool.query('INSERT INTO user_store_items(user_id,item_id) VALUES($1,$2) ON CONFLICT DO NOTHING',[socket.user.id,r.rows[0].id]);
      cb({success:true,item:rowToStoreItem({...r.rows[0],creator_username:socket.user.username})});
    } catch (e) {
      console.error(e);
      cb({success:false,message:e.message || 'Could not create store item.'});
    }
  });

  socket.on('get_my_creations',async(cb)=>{
    if(!requireAuth(socket,cb))return;
    try{
      const [worlds,items]=await Promise.all([
        pool.query('SELECT id,name,data,created_at,updated_at FROM worlds WHERE owner_user_id=$1 ORDER BY updated_at DESC',[socket.user.id]),
        pool.query("SELECT id,name,category,price,asset_url,asset_kind,metadata,is_visible,created_at,updated_at FROM store_items WHERE created_by=$1 AND category IN ('hair','hats','heads','eyes','mouth') ORDER BY updated_at DESC",[socket.user.id])
      ]);
      cb({success:true,worlds:worlds.rows.map(w=>({name:w.name,displayName:w.data?.displayName||w.name,description:w.data?.description||'',thumbnailUrl:w.data?.thumbnailUrl||''})),items:items.rows.map(rowToStoreItem)});
    }catch(e){console.error('Creations list:',e);cb({success:false,message:'Could not load creations.'});}
  });
  socket.on('update_my_avatar_item',async({itemId,name,price,isVisible}={},cb)=>{
    if (typeof cb === 'function') cb({success:false,message:'Avatar marketplace is retired.'});
    return;
    if(!requireAuth(socket,cb))return;
    const id=cleanStoreItemId(itemId),clean=filterKWGUserText(String(name||'').trim());
    const n=Number(price);
    if(!id||!clean||clean.length>40||!Number.isInteger(n)||n<0||n>1000000)return cb({success:false,message:'Enter a valid name and price.'});
    try{
      const r=await pool.query('UPDATE store_items SET name=$1,price=$2,is_visible=$3,updated_at=NOW() WHERE id=$4 AND created_by=$5 RETURNING id',[clean,n,isVisible!==false,id,socket.user.id]);
      cb(r.rowCount?{success:true}:{success:false,message:'Item not found or not yours.'});
    }catch(e){console.error('Update creation:',e);cb({success:false,message:'Could not update item.'});}
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
    if (p?.worldName){socket.to(`world:${p.worldName}`).emit('player_left', socket.id);kwgAnnounce(p.worldName,`${p.username} left the world.`,socket.user?.id);}
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
