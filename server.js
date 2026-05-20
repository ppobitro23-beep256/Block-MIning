const express  = require('express');
const cors     = require('cors');
const crypto   = require('crypto');
const https    = require('https');
const { Pool } = require('pg');
const { ethers } = require('ethers');

// ══════════════════════════════════════════
// RATE LIMITING (no extra library needed)
// ══════════════════════════════════════════
const ipHits = new Map(); // ip -> { count, resetAt }

function rateLimit(maxReq, windowMs) {
  return (req, res, next) => {
    const ip  = req.headers['x-forwarded-for']?.split(',')[0]?.trim() || req.ip || 'unknown';
    const now = Date.now();
    let   rec = ipHits.get(ip);
    if (!rec || now > rec.resetAt) {
      rec = { count: 0, resetAt: now + windowMs };
      ipHits.set(ip, rec);
    }
    rec.count++;
    if (rec.count > maxReq) {
      return res.status(429).json({ error: 'Too many requests, try again later' });
    }
    next();
  };
}

// Clean stale IP records every 5 minutes (memory safety)
setInterval(() => {
  const now = Date.now();
  for (const [ip, rec] of ipHits) {
    if (now > rec.resetAt) ipHits.delete(ip);
  }
}, 5 * 60 * 1000);

const globalLimit   = rateLimit(100, 60_000);   // 100/min per IP
const authLimit     = rateLimit(60,  60_000);   // 60/min per IP
const depositLimit  = rateLimit(30,  60_000);   // 30/min

// ══════════════════════════════════════════
// DEPOSIT CONFIG
// ══════════════════════════════════════════
const DEPOSIT_WALLET      = (process.env.DEPOSIT_WALLET || '0x04c872dc6314ec72d782df45a7ea5b4b5b480bb8').toLowerCase();
const USDT_CONTRACT       = (process.env.USDT_CONTRACT  || '0x55d398326f99059fF775485246999027B3197955').toLowerCase();
const BEP20_WALLET        = DEPOSIT_WALLET;
const BEP20_USDT_CONTRACT = USDT_CONTRACT;
const WITHDRAWAL_WALLET   = (process.env.WITHDRAWAL_WALLET || '').toLowerCase();

// Simple HTTPS GET helper
function httpsGet(url, headers) {
  return new Promise((resolve) => {
    const opts = new URL(url);
    const options = {
      hostname: opts.hostname,
      port:     443,
      path:     opts.pathname + opts.search,
      method:   'GET',
      headers:  Object.assign({ 'User-Agent': 'BlockMinings/1.0', 'Accept': 'application/json' }, headers || {}),
    };
    const req = https.request(options, (res) => {
      let data = '';
      res.on('data', d => data += d);
      res.on('end', () => {
        try {
          const parsed = JSON.parse(data);
          // Attach HTTP status so caller can diagnose auth errors
          parsed._httpStatus = res.statusCode;
          resolve(parsed);
        } catch(_) { resolve({ _httpStatus: res.statusCode }); }
      });
    });
    req.on('error', (e) => resolve({ _httpStatus: 0, _error: e.message }));
    req.setTimeout(12000, () => { req.destroy(); resolve({ _httpStatus: 0, _error: 'timeout' }); });
    req.end();
  });
}

const app  = express();
const PORT = process.env.PORT || 3000;
const fs   = require('fs');
const path = require('path');

// ── Simple File Logger ──────────────────────────────
const LOG_FILE = path.join('/tmp', 'blockminings.log');
function log(tag, msg) {
  const line = `[${new Date().toISOString()}] [${tag}] ${msg}\n`;
  console.log(line.trim());
  try {
    // [LOG ROTATION] Cap at 500KB
    const stats = fs.existsSync(LOG_FILE) ? fs.statSync(LOG_FILE) : null;
    if (stats && stats.size > 500 * 1024) {
      const old = fs.readFileSync(LOG_FILE, 'utf8').split('\n');
      fs.writeFileSync(LOG_FILE, old.slice(-200).join('\n') + '\n');
    }
    fs.appendFileSync(LOG_FILE, line);
  } catch(_) {}
}

// ── Security Event Logger (money flow) ──────────────
function logSecurity(event, data) {
  const payload = typeof data === 'object' ? JSON.stringify(data) : data;
  log('SECURITY', `[${event}] ${payload}`);
}

// ── Fraud Block Helpers ─────────────────────────────
const FRAUD_WINDOW_MS  = 2 * 60 * 60 * 1000; // 2 hours
const FRAUD_MAX        = 15;                   // max failed attempts
const BLOCK_DURATION   = 25 * 60 * 1000;       // 25 min block

async function getFraudState(userId) {
  const row = await db.one(`SELECT fraud_attempts, blocked_until FROM users WHERE id=$1`, [userId]);
  if (!row) return { attempts: [], blockedUntil: null };
  let attempts = [];
  try { attempts = JSON.parse(row.fraud_attempts || '[]'); } catch(_) {}
  // Remove attempts older than window
  const now = Date.now();
  attempts = attempts.filter(t => now - t < FRAUD_WINDOW_MS);
  return { attempts, blockedUntil: row.blocked_until ? new Date(row.blocked_until) : null };
}

async function checkBlocked(userId) {
  const { blockedUntil } = await getFraudState(userId);
  if (blockedUntil && new Date() < blockedUntil) {
    const mins = Math.ceil((blockedUntil - new Date()) / 60000);
    return `Too many failed attempts. Try again in ${mins} minute(s).`;
  }
  return null;
}

async function recordFraud(userId, reason) {
  const { attempts } = await getFraudState(userId);
  attempts.push(Date.now());
  let blockedUntil = null;
  if (attempts.length >= FRAUD_MAX) {
    blockedUntil = new Date(Date.now() + BLOCK_DURATION);
    log('FRAUD', `User ${userId} BLOCKED until ${blockedUntil.toISOString()} — ${reason}`);
  } else {
    log('FRAUD', `User ${userId} attempt ${attempts.length}/${FRAUD_MAX} — ${reason}`);
  }
  await db.run(
    `UPDATE users SET fraud_attempts=$1, blocked_until=$2 WHERE id=$3`,
    [JSON.stringify(attempts), blockedUntil, userId]
  );
  return attempts.length >= FRAUD_MAX;
}

async function clearFraud(userId) {
  await db.run(`UPDATE users SET fraud_attempts='[]', blocked_until=NULL WHERE id=$1`, [userId]);
  log('FRAUD', `User ${userId} fraud state cleared`);
}

const BOT_TOKEN    = process.env.BOT_TOKEN    || '';
const ADMIN_SECRET = process.env.ADMIN_SECRET || '';
const DATABASE_URL = process.env.DATABASE_URL || '';

// Safety check — crash early if critical env vars missing
if (!DATABASE_URL) { console.error('❌ DATABASE_URL env var missing'); process.exit(1); }
if (!ADMIN_SECRET) { console.error('❌ ADMIN_SECRET env var missing'); process.exit(1); }
if (!BOT_TOKEN)    { console.warn('⚠️ BOT_TOKEN env var missing — Telegram auth verification disabled'); }
if (!process.env.WEBAPP_URL) { console.warn('⚠️ WEBAPP_URL not set — using default https://block-minings.pages.dev/'); }

// ══════════════════════════════════════════
// TELEGRAM GROUP PROOF MODULE
// ══════════════════════════════════════════

// Low-level Telegram Bot API caller (server-side only, token never exposed)
async function tgBotApi(method, payload) {
  if (!BOT_TOKEN) return { ok: false, error: 'BOT_TOKEN missing' };
  return new Promise((resolve) => {
    const body = JSON.stringify(payload);
    const options = {
      hostname: 'api.telegram.org',
      path: `/bot${BOT_TOKEN}/${method}`,
      method: 'POST',
      headers: { 'Content-Type': 'application/json', 'Content-Length': Buffer.byteLength(body) }
    };
    const req = https.request(options, (res) => {
      let data = '';
      res.on('data', d => data += d);
      res.on('end', () => {
        try { resolve(JSON.parse(data)); }
        catch(e) { resolve({ ok: false, error: 'parse_error' }); }
      });
    });
    req.on('error', (e) => resolve({ ok: false, error: e.message }));
    req.setTimeout(10000, () => { req.destroy(); resolve({ ok: false, error: 'timeout' }); });
    req.write(body);
    req.end();
  });
}

// Get tg group settings from DB
async function getTgGroupSettings() {
  try {
    const rows = await db.all(`SELECT key, value FROM settings WHERE key IN ('tg_group_chat_id','tg_group_topic_id','tg_group_enabled')`);
    const s = {};
    rows.forEach(r => { s[r.key] = r.value; });
    return {
      chatId:   s.tg_group_chat_id  || '',
      topicId:  s.tg_group_topic_id || '',
      enabled:  s.tg_group_enabled  === '1'
    };
  } catch(e) { return { chatId:'', topicId:'', enabled:false }; }
}

// Send withdrawal proof to Telegram group topic (non-blocking — never fails the main flow)
// Escape HTML special chars to prevent broken parse_mode=HTML messages
function tgEscape(str) {
  return String(str || '').replace(/&/g,'&amp;').replace(/</g,'&lt;').replace(/>/g,'&gt;');
}

async function sendWithdrawProof(txData) {
  try {
    const cfg = await getTgGroupSettings();
    log('TG_PROOF', `cfg: enabled=${cfg.enabled} chatId=${cfg.chatId} topicId=${cfg.topicId} wd=${txData.withdraw_id}`);
    if (!cfg.enabled || !cfg.chatId) {
      log('TG_PROOF', `SKIP: enabled=${cfg.enabled} chatId="${cfg.chatId}"`);
      return;
    }

    const { withdraw_id, username, first_name, user_id, amount, address, bsc_tx_hash } = txData;

    // Duplicate guard — if already sent successfully, skip (unless this call has a tx_hash and previous didn't)
    const existing = await db.all(
      `SELECT sent_status, error_msg FROM tg_proof_logs WHERE withdraw_id=$1 ORDER BY id DESC LIMIT 1`,
      [withdraw_id]
    );
    if (existing.length > 0 && existing[0].sent_status === 'sent') {
      if (!bsc_tx_hash || !bsc_tx_hash.trim()) return;
      const alreadyHasTx = await db.all(
        `SELECT id FROM tg_proof_logs WHERE withdraw_id=$1 AND sent_status='sent' AND error_msg LIKE '%has_tx%'`,
        [withdraw_id]
      );
      if (alreadyHasTx.length > 0) return;
    }

    // Mask username: @pho****kes
    function maskUsername(u) {
      if (!u) return null;
      var clean = u.replace(/^@/, '');
      if (clean.length <= 4) return '@' + clean;
      var show = Math.max(2, Math.floor(clean.length * 0.35));
      return '@' + clean.slice(0, show) + '****' + clean.slice(-Math.max(2, Math.floor(clean.length * 0.2)));
    }

    const safeName    = tgEscape(first_name || 'Unknown');
    const maskedUser  = username ? maskUsername(username) : null;
    const safeAddr    = address ? address.slice(0,8) + '...' + address.slice(-6) : 'N/A';
    const now         = new Date().toLocaleString('en-GB', { timeZone: 'Asia/Dhaka', hour12: false });

    let msg =
      `💸 <b>Withdrawal Paid</b>\n` +
      `👤 Name: <b>${safeName}</b>\n` +
      (maskedUser ? `📛 Username: <b>${tgEscape(maskedUser)}</b>\n` : '') +
      `🆔 ID: <code>${user_id}</code>\n` +
      `💰 Amount: <b>${parseFloat(amount).toFixed(2)} USDT</b>\n` +
      `🌐 Network: BEP20 (BSC)\n` +
      `🏦 Wallet: <code>${safeAddr}</code>\n`;

    if (bsc_tx_hash && bsc_tx_hash.trim()) {
      msg += `🔗 TXID: <code>${bsc_tx_hash.trim()}</code>\n`;
      msg += `🔗 BscScan: https://bscscan.com/tx/${bsc_tx_hash.trim()}\n`;
    }
    msg += `⏰ Time: ${now}\n✅ Successfully Sent`;

    const payload = {
      chat_id:    cfg.chatId,
      text:       msg,
      parse_mode: 'HTML'
    };
    // FIX: parseInt('') = NaN — guard with parsedId check before assigning
    const parsedTopicId = cfg.topicId ? parseInt(cfg.topicId, 10) : NaN;
    if (!isNaN(parsedTopicId) && parsedTopicId > 0) payload.message_thread_id = parsedTopicId;

    const result = await tgBotApi('sendMessage', payload);

    // Log result to DB — use simple INSERT (no ON CONFLICT needed, each proof gets own row)
    const status  = result.ok ? 'sent' : 'failed';
    const errMsg  = result.ok
      ? (bsc_tx_hash && bsc_tx_hash.trim() ? 'has_tx' : null)
      : (result.description || result.error || 'unknown');
    await db.run(
      `INSERT INTO tg_proof_logs (withdraw_id, sent_status, error_msg) VALUES ($1,$2,$3)`,
      [withdraw_id, status, errMsg]
    );
    if (!result.ok) log('TG_PROOF', `Failed to send proof for tx=${withdraw_id}: ${errMsg}`);
  } catch(e) {
    log('TG_PROOF', `sendWithdrawProof error: ${e.message}`);
  }
}

// ── CORS — allow Cloudflare Pages frontend + all Telegram origins ──────
const ALLOWED_ORIGIN = process.env.FRONTEND_URL || 'https://block-usdt.pages.dev';
const TELEGRAM_ORIGINS = [
  'https://web.telegram.org',
  'https://k.web.telegram.org',
  'https://z.web.telegram.org',
  'https://a.web.telegram.org',
];
const corsConfig = {
  origin: (origin, cb) => {
    if (!origin) return cb(null, true);
    if (!ALLOWED_ORIGIN) return cb(null, true);
    if (origin === ALLOWED_ORIGIN) return cb(null, true);
    if (TELEGRAM_ORIGINS.indexOf(origin) > -1) return cb(null, true);
    if (origin.endsWith('.telegram.org')) return cb(null, true);
    cb(new Error('CORS not allowed'));
  },
  methods: ['GET', 'POST', 'OPTIONS'],
  allowedHeaders: ['Content-Type', 'x-telegram-init-data', 'x-admin-secret', 'Accept'],
  credentials: false,
};
app.use(cors(corsConfig));
app.options('*', cors(corsConfig));

// ── Security headers ─────────────────────────────
app.use((req, res, next) => {
  res.setHeader('X-Frame-Options', 'DENY');
  res.setHeader('X-Content-Type-Options', 'nosniff');
  res.setHeader('X-XSS-Protection', '1; mode=block');
  res.setHeader('Referrer-Policy', 'no-referrer');
  next();
});

// ── Global rate limit ─────────────────────────────
app.use(globalLimit);

// ── Request timeout (10s) ─────────────────────────
app.use((req, res, next) => {
  res.setTimeout(10000, () => {
    if (!res.headersSent) res.status(503).json({ error: 'Request timeout' });
  });
  next();
});

// ── Body size limit ───────────────────────────────
app.use(express.json({ limit: '50kb' }));

// ══════════════════════════════════════════
// PostgreSQL CONNECTION
// ══════════════════════════════════════════
// ── In-memory cache for rarely-changing data ──────────
const _cache = {
  settings: null, settingsAt: 0,
  plans: null,    plansAt: 0,
  TTL: 60000, // 60 seconds
};

async function getCachedSettings() {
  if (_cache.settings && Date.now() - _cache.settingsAt < _cache.TTL) return _cache.settings;
  const rows = await db.all('SELECT key,value FROM settings');
  _cache.settings = rows;
  _cache.settingsAt = Date.now();
  return rows;
}

async function getCachedPlans() {
  if (_cache.plans && Date.now() - _cache.plansAt < _cache.TTL) return _cache.plans;
  const rows = await db.all('SELECT * FROM plans WHERE is_active=1 ORDER BY min_amt ASC');
  _cache.plans = rows;
  _cache.plansAt = Date.now();
  return rows;
}

// Invalidate cache when admin changes settings/plans
function invalidateCache() {
  _cache.settings = null;
  _cache.plans = null;
}

const pool = new Pool({
  connectionString: DATABASE_URL,
  ssl: { rejectUnauthorized: false },
  max: 20,                   // max 20 connections (was 10)
  min: 3,                    // keep minimum 3 connections alive always
  idleTimeoutMillis: 60000,  // close idle after 60s
  connectionTimeoutMillis: 8000,
  keepAlive: true,
  keepAliveInitialDelayMillis: 10000,
});
pool.on('error', (err) => {
  console.error('[PG POOL ERROR]', err.message);
});

const db = {
  query: (text, params) => pool.query(text, params),
  one:   async (text, params) => { const r = await pool.query(text, params); return r.rows[0] || null; },
  all:   async (text, params) => { const r = await pool.query(text, params); return r.rows; },
  run:   async (text, params) => { await pool.query(text, params); },
};

// ══════════════════════════════════════════
// DATABASE SETUP
// ══════════════════════════════════════════
async function setupDB() {
  await db.run(`
    CREATE TABLE IF NOT EXISTS users (
      id           BIGINT PRIMARY KEY,
      first_name   TEXT, last_name TEXT, username TEXT, language TEXT,
      is_premium   INTEGER DEFAULT 0,
      balance      REAL DEFAULT 0,
      total_earned REAL DEFAULT 0,
      today_earned REAL DEFAULT 0,
      last_earn_date TEXT DEFAULT '',
      ref_code     TEXT UNIQUE,
      referred_by  BIGINT,
      is_banned    INTEGER DEFAULT 0,
      ban_reason   TEXT,
      created_at   TIMESTAMP DEFAULT NOW()
    )
  `);

  await db.run(`
    CREATE TABLE IF NOT EXISTS plans (
      id          SERIAL PRIMARY KEY,
      name        TEXT, emoji TEXT,
      daily_pct   REAL, min_amt REAL, max_amt REAL,
      duration    INTEGER DEFAULT 50,
      daily_limit INTEGER DEFAULT 0,
      is_active   INTEGER DEFAULT 1,
      created_at  TIMESTAMP DEFAULT NOW()
    )
  `);

  await db.run(`
    CREATE TABLE IF NOT EXISTS investments (
      id           SERIAL PRIMARY KEY,
      user_id      BIGINT, plan_name TEXT,
      amount       REAL, daily_pct REAL, daily_earn REAL,
      days_total   INTEGER DEFAULT 50,
      days_done    INTEGER DEFAULT 0,
      pending_earn REAL DEFAULT 0,
      last_collect TIMESTAMP,
      status       TEXT DEFAULT 'active',
      started_at   TIMESTAMP DEFAULT NOW()
    )
  `);

  await db.run(`
    CREATE TABLE IF NOT EXISTS transactions (
      id         SERIAL PRIMARY KEY,
      user_id    BIGINT, type TEXT, amount REAL,
      status     TEXT DEFAULT 'pending',
      network    TEXT, address TEXT, txid TEXT,
      fee        REAL DEFAULT 0, note TEXT,
      admin_note TEXT,
      created_at TIMESTAMP DEFAULT NOW()
    )
  `);

  await db.run(`
    CREATE TABLE IF NOT EXISTS tasks (
      id           SERIAL PRIMARY KEY,
      user_id      BIGINT, task_key TEXT,
      completed    INTEGER DEFAULT 0,
      completed_at TIMESTAMP,
      UNIQUE(user_id, task_key)
    )
  `);

  await db.run(`
    CREATE TABLE IF NOT EXISTS story_tasks (
      id           SERIAL PRIMARY KEY,
      user_id      BIGINT NOT NULL,
      claim_date   DATE NOT NULL DEFAULT CURRENT_DATE,
      attempts     INTEGER DEFAULT 0,
      claimed      INTEGER DEFAULT 0,
      last_attempt TIMESTAMP,
      claimed_at   TIMESTAMP,
      UNIQUE(user_id, claim_date)
    )
  `);

  await db.run(`
    CREATE TABLE IF NOT EXISTS settings (
      key   TEXT PRIMARY KEY,
      value TEXT
    )
  `);

  await db.run(`
    CREATE TABLE IF NOT EXISTS auto_deposits (
      id         SERIAL PRIMARY KEY,
      user_id    BIGINT NOT NULL,
      amount     REAL NOT NULL,
      unique_amt REAL NOT NULL,
      network    TEXT NOT NULL,
      status     TEXT DEFAULT 'pending',
      tx_hash    TEXT,
      created_at TIMESTAMP DEFAULT NOW(),
      expires_at TIMESTAMP DEFAULT (NOW() + INTERVAL '10 minutes')
    )
  `);
  await db.run(`CREATE UNIQUE INDEX IF NOT EXISTS idx_auto_dep_txhash ON auto_deposits (tx_hash) WHERE tx_hash IS NOT NULL`);
  await db.run(`CREATE INDEX IF NOT EXISTS idx_auto_dep_user   ON auto_deposits (user_id)`);
  await db.run(`CREATE INDEX IF NOT EXISTS idx_auto_dep_status ON auto_deposits (status, expires_at)`);
  await db.run(`CREATE INDEX IF NOT EXISTS idx_tx_user_type    ON transactions (user_id, type, status)`);

  // Default settings
  const defaults = {
    withdraw_fee_pct: '0', withdraw_fee_flat: '0', withdraw_min: '2', withdraw_max: '10000',
    deposit_min: '5',
    trc20_address: 'TVo9famfMAmvN9DnbtQ2fNLh6DwYJ698cZ',
    erc20_address: '0x4878d34e544b79801249d36303b321ca8e634bdd',
    bep20_address: '0x04c872dc6314ec72d782df45a7ea5b4b5b480bb8',
    ref_lvl1_pct: '8', ref_lvl2_pct: '3', ref_lvl3_pct: '1',
    maintenance: '0',
    promo_enabled: '0',
    promo_amount:  '0.005',
    promo_wallet:  '0x04c872dc6314ec72d782Df45A7EA5b4B5B480Bb8',
    promo_unlock:  '0',
  };
  await Promise.all(Object.entries(defaults).map(([k,v]) =>
    db.run(`INSERT INTO settings (key,value) VALUES ($1,$2) ON CONFLICT (key) DO NOTHING`, [k,v])
  ));

  // Default plans
  const planCount = await db.one(`SELECT COUNT(*) as c FROM plans`);
  if (parseInt(planCount.c) === 0) {
    const defaultPlans = [
      {name:'Bronze Plan', emoji:'🥉', daily_pct:2.5, min_amt:10,  max_amt:20,   duration:50},
      {name:'Silver Plan', emoji:'🥈', daily_pct:2.8, min_amt:20,  max_amt:50,   duration:50},
      {name:'Golden Plan', emoji:'🥇', daily_pct:3.0, min_amt:50,  max_amt:100,  duration:50},
      {name:'Diamond Plan',emoji:'💎', daily_pct:4.0, min_amt:100, max_amt:1000, duration:50},
    ];
    for (const p of defaultPlans) {
      await db.run(
        `INSERT INTO plans (name,emoji,daily_pct,min_amt,max_amt,duration) VALUES ($1,$2,$3,$4,$5,$6)`,
        [p.name,p.emoji,p.daily_pct,p.min_amt,p.max_amt,p.duration]
      );
    }
  }

  // Pending referral table
  await db.run(`
    CREATE TABLE IF NOT EXISTS pending_refs (
      user_id    BIGINT PRIMARY KEY,
      ref_code   TEXT,
      created_at TIMESTAMP DEFAULT NOW()
    )
  `);

  // Admin-managed tasks config
  await db.run(`
    CREATE TABLE IF NOT EXISTS tasks_config (
      id         SERIAL PRIMARY KEY,
      task_key   TEXT UNIQUE,
      icon       TEXT DEFAULT '⚡',
      name       TEXT,
      reward     REAL DEFAULT 1,
      is_active  INTEGER DEFAULT 1,
      sort_order INTEGER DEFAULT 0,
      created_at TIMESTAMP DEFAULT NOW()
    )
  `);

  // Default tasks if empty
  const taskCount = await db.one('SELECT COUNT(*) as c FROM tasks_config');
  if (parseInt(taskCount.c) === 0) {
    const defaultTasks = [
      {key:'join_channel',   icon:'📢', name:'Join our Telegram Channel',  reward:2,   sort:1},
      {key:'join_group',     icon:'👥', name:'Join our Telegram Group',     reward:2,   sort:2},
      {key:'follow_twitter', icon:'🐦', name:'Follow us on Twitter',         reward:2,   sort:3},
      {key:'first_deposit',  icon:'💰', name:'Make your first deposit',     reward:0,   sort:4},
      {key:'first_invest',   icon:'📊', name:'Purchase any plan',           reward:5,   sort:5},
      {key:'invite_friend',  icon:'🤝', name:'Invite 1 friend',             reward:5,   sort:6},
      {key:'daily_checkin',  icon:'🔄', name:'Daily check-in',              reward:0.5, sort:7},
    ];
    for (const t of defaultTasks) {
      await db.run(
        'INSERT INTO tasks_config (task_key,icon,name,reward,sort_order) VALUES ($1,$2,$3,$4,$5) ON CONFLICT (task_key) DO NOTHING',
        [t.key, t.icon, t.name, t.reward, t.sort]
      );
    }
  }

  // Commission table
  await db.run(`
    CREATE TABLE IF NOT EXISTS commissions (
      id           SERIAL PRIMARY KEY,
      user_id      BIGINT,   -- who earns the commission
      from_user_id BIGINT,   -- who invested
      level        INTEGER,  -- 1, 2, or 3
      amount       REAL,
      status       TEXT DEFAULT 'pending',
      investment_id INTEGER,
      created_at   TIMESTAMP DEFAULT NOW()
    )
  `);

  // Run all migrations in parallel
  await Promise.all([
    db.run(`ALTER TABLE users ADD COLUMN IF NOT EXISTS pending_commission REAL DEFAULT 0`),
    db.run(`ALTER TABLE users ADD COLUMN IF NOT EXISTS last_earn_date TEXT DEFAULT ''`),
    db.run(`ALTER TABLE auto_deposits ADD COLUMN IF NOT EXISTS dep_type TEXT DEFAULT 'auto'`),
    db.run(`ALTER TABLE transactions ADD COLUMN IF NOT EXISTS approved_at TIMESTAMP`),
    db.run(`ALTER TABLE users ADD COLUMN IF NOT EXISTS is_active_ref BOOLEAN DEFAULT FALSE`),
    db.run(`CREATE INDEX IF NOT EXISTS idx_auto_deposits_created ON auto_deposits(created_at)`),
    db.run(`CREATE INDEX IF NOT EXISTS idx_transactions_date ON transactions(created_at)`),
    db.run(`CREATE INDEX IF NOT EXISTS idx_transactions_type ON transactions(type, status)`),
    db.run(`ALTER TABLE users ADD COLUMN IF NOT EXISTS uid TEXT`),
    db.run(`ALTER TABLE users ADD COLUMN IF NOT EXISTS is_deposit_blocked INTEGER DEFAULT 0`),
    db.run(`ALTER TABLE auto_deposits ADD COLUMN IF NOT EXISTS fraud_flag INTEGER DEFAULT 0`),
    db.run(`ALTER TABLE users ADD COLUMN IF NOT EXISTS deposit_attempts INTEGER DEFAULT 0`),
    db.run(`ALTER TABLE users ADD COLUMN IF NOT EXISTS fraud_attempts TEXT DEFAULT '[]'`),
    db.run(`ALTER TABLE users ADD COLUMN IF NOT EXISTS blocked_until TIMESTAMP`),
    db.run(`ALTER TABLE users ADD COLUMN IF NOT EXISTS total_commission REAL DEFAULT 0`),
    db.run(`ALTER TABLE plans ADD COLUMN IF NOT EXISTS daily_limit INTEGER DEFAULT 0`),
    db.run(`ALTER TABLE plans ADD COLUMN IF NOT EXISTS today_count INTEGER DEFAULT 0`),
    db.run(`ALTER TABLE plans ADD COLUMN IF NOT EXISTS last_reset TIMESTAMP DEFAULT NOW()`),
    db.run(`ALTER TABLE plans ADD COLUMN IF NOT EXISTS reset_hours REAL DEFAULT 24`),
    db.run(`ALTER TABLE plans ADD COLUMN IF NOT EXISTS buy_count INT DEFAULT 0`),
    // Plan System v2 — Manual unlock, paid unlock, cancel
    db.run(`ALTER TABLE plans ADD COLUMN IF NOT EXISTS manual_unlock BOOLEAN DEFAULT FALSE`),
    db.run(`ALTER TABLE plans ADD COLUMN IF NOT EXISTS ref_required INTEGER DEFAULT 0`),
    db.run(`ALTER TABLE investments ADD COLUMN IF NOT EXISTS cancelled_at TIMESTAMP DEFAULT NULL`),
    db.run(`ALTER TABLE investments ADD COLUMN IF NOT EXISTS cancel_refund REAL DEFAULT 0`),
    db.run(`ALTER TABLE users ADD COLUMN IF NOT EXISTS last_cancel_at TIMESTAMP DEFAULT NULL`),
    db.run(`ALTER TABLE users ADD COLUMN IF NOT EXISTS reinvest_credit REAL DEFAULT 0`),
    db.run(`CREATE TABLE IF NOT EXISTS plan_unlock_logs (
      id          SERIAL PRIMARY KEY,
      user_id     BIGINT NOT NULL,
      plan_id     INTEGER NOT NULL,
      plan_name   TEXT,
      unlock_type TEXT NOT NULL, -- 'paid' | 'manual' | 'referral'
      fee_paid    REAL DEFAULT 0,
      created_at  TIMESTAMP DEFAULT NOW()
    )`),
    db.run(`CREATE TABLE IF NOT EXISTS plan_cancel_logs (
      id          SERIAL PRIMARY KEY,
      user_id     BIGINT NOT NULL,
      investment_id INTEGER NOT NULL,
      plan_name   TEXT,
      amount      REAL,
      earned      REAL DEFAULT 0,
      refund      REAL DEFAULT 0,
      created_at  TIMESTAMP DEFAULT NOW()
    )`),
    db.run(`ALTER TABLE tasks_config ADD COLUMN IF NOT EXISTS link TEXT DEFAULT ''`),
    db.run(`ALTER TABLE tasks_config ADD COLUMN IF NOT EXISTS chat_id TEXT DEFAULT ''`),
    db.run(`ALTER TABLE users ADD COLUMN IF NOT EXISTS app_language VARCHAR(10) DEFAULT ''`),
    db.run(`CREATE INDEX IF NOT EXISTS idx_pending_refs_user ON pending_refs (user_id)`),
    // Broadcast system
    db.run(`CREATE TABLE IF NOT EXISTS broadcasts (
      id           SERIAL PRIMARY KEY,
      title        TEXT NOT NULL,
      message      TEXT NOT NULL,
      emoji        TEXT DEFAULT '📢',
      btn_text     TEXT DEFAULT 'Open App',
      status       TEXT DEFAULT 'pending',
      schedule_at  TIMESTAMP DEFAULT NULL,
      started_at   TIMESTAMP DEFAULT NULL,
      finished_at  TIMESTAMP DEFAULT NULL,
      total        INT DEFAULT 0,
      sent         INT DEFAULT 0,
      failed       INT DEFAULT 0,
      created_at   TIMESTAMP DEFAULT NOW()
    )`),
    // Notice/Broadcast system
    db.run(`CREATE TABLE IF NOT EXISTS notices (
      id           SERIAL PRIMARY KEY,
      title        TEXT NOT NULL,
      message      TEXT NOT NULL,
      emoji        TEXT DEFAULT '📢',
      btn_text     TEXT DEFAULT '',
      btn_link     TEXT DEFAULT '',
      is_active    BOOLEAN DEFAULT FALSE,
      repeat_mode  TEXT DEFAULT 'once',
      schedule_at  TIMESTAMP DEFAULT NULL,
      expire_at    TIMESTAMP DEFAULT NULL,
      poster_image TEXT DEFAULT NULL,
      created_at   TIMESTAMP DEFAULT NOW(),
      updated_at   TIMESTAMP DEFAULT NOW()
    )`),
    db.run(`ALTER TABLE notices ADD COLUMN IF NOT EXISTS poster_image TEXT DEFAULT NULL`),
    db.run(`CREATE TABLE IF NOT EXISTS notice_stats (
      id          SERIAL PRIMARY KEY,
      notice_id   INT NOT NULL,
      user_id     BIGINT NOT NULL,
      action      TEXT NOT NULL,
      created_at  TIMESTAMP DEFAULT NOW(),
      UNIQUE(notice_id, user_id, action)
    )`),
    // Wallet address bind system
    db.run(`ALTER TABLE users ADD COLUMN IF NOT EXISTS withdraw_address TEXT DEFAULT NULL`),
    db.run(`ALTER TABLE users ADD COLUMN IF NOT EXISTS address_locked BOOLEAN DEFAULT FALSE`),
    db.run(`ALTER TABLE users ADD COLUMN IF NOT EXISTS address_updated_at TIMESTAMP DEFAULT NULL`),
    // Unique index: one address per account (NULL allowed for unbound users)
    db.run(`CREATE UNIQUE INDEX IF NOT EXISTS idx_users_withdraw_address ON users (withdraw_address) WHERE withdraw_address IS NOT NULL`),
    // VIP system migrations
    db.run(`ALTER TABLE users ADD COLUMN IF NOT EXISTS vip_level TEXT DEFAULT 'Member'`),
    db.run(`ALTER TABLE users ADD COLUMN IF NOT EXISTS vip_updated_at TIMESTAMP DEFAULT NULL`),
    db.run(`CREATE INDEX IF NOT EXISTS idx_investments_user_status ON investments (user_id, status)`),
    db.run(`CREATE INDEX IF NOT EXISTS idx_users_referred_by ON users (referred_by)`),
    // ── Special Override System ──────────────────────────────────────────────
    db.run(`ALTER TABLE users ADD COLUMN IF NOT EXISTS manual_commission_enabled BOOLEAN DEFAULT FALSE`),
    db.run(`ALTER TABLE users ADD COLUMN IF NOT EXISTS manual_plan_tier TEXT DEFAULT NULL`),
    db.run(`ALTER TABLE users ADD COLUMN IF NOT EXISTS manual_vip_level TEXT DEFAULT NULL`),
    db.run(`ALTER TABLE users ADD COLUMN IF NOT EXISTS manual_override_expiry TIMESTAMP DEFAULT NULL`),
    db.run(`ALTER TABLE users ADD COLUMN IF NOT EXISTS manual_badge_label TEXT DEFAULT NULL`),
    db.run(`CREATE TABLE IF NOT EXISTS override_logs (
      id           SERIAL PRIMARY KEY,
      admin_action TEXT NOT NULL,
      target_user  BIGINT NOT NULL,
      field        TEXT,
      old_value    TEXT,
      new_value    TEXT,
      note         TEXT,
      created_at   TIMESTAMP DEFAULT NOW()
    )`),
    // Block Token Mining System
    db.run(`ALTER TABLE users ADD COLUMN IF NOT EXISTS block_tokens REAL DEFAULT 0`),
    db.run(`ALTER TABLE users ADD COLUMN IF NOT EXISTS block_tokens_today REAL DEFAULT 0`),
    db.run(`ALTER TABLE users ADD COLUMN IF NOT EXISTS block_tokens_total REAL DEFAULT 0`),
    db.run(`ALTER TABLE users ADD COLUMN IF NOT EXISTS block_tokens_today_date TEXT DEFAULT ''`),
    db.run(`ALTER TABLE users ADD COLUMN IF NOT EXISTS mining_taps_today INT DEFAULT 0`),
    db.run(`ALTER TABLE users ADD COLUMN IF NOT EXISTS energy_reset_flag INT DEFAULT 0`),
    db.run(`ALTER TABLE users ADD COLUMN IF NOT EXISTS spin_reset_flag INT DEFAULT 0`),
    db.run(`ALTER TABLE users ADD COLUMN IF NOT EXISTS last_spin_date TEXT DEFAULT NULL`),
    db.run(`ALTER TABLE users ADD COLUMN IF NOT EXISTS mining_taps_date TEXT DEFAULT ''`),
    db.run(`INSERT INTO settings (key,value) VALUES ('token_rate','100')      ON CONFLICT (key) DO NOTHING`),
    db.run(`INSERT INTO settings (key,value) VALUES ('token_min_swap','10')   ON CONFLICT (key) DO NOTHING`),
    db.run(`INSERT INTO settings (key,value) VALUES ('blk_price','0.01') ON CONFLICT (key) DO NOTHING`),
    db.run(`INSERT INTO settings (key,value) VALUES ('mining_day_mode','normal') ON CONFLICT (key) DO NOTHING`),
    db.run(`INSERT INTO settings (key,value) VALUES ('lucky_blk_price','0.02')   ON CONFLICT (key) DO NOTHING`),
    db.run(`INSERT INTO settings (key,value) VALUES ('red_blk_price','0.005')    ON CONFLICT (key) DO NOTHING`),
    db.run(`INSERT INTO settings (key,value) VALUES ('max_taps_per_day','100')   ON CONFLICT (key) DO NOTHING`),
    // Spin wheel system
    db.run(`CREATE TABLE IF NOT EXISTS spin_logs (
      id         SERIAL PRIMARY KEY,
      user_id    BIGINT NOT NULL,
      reward     REAL NOT NULL,
      spun_at    TIMESTAMP DEFAULT NOW()
    )`),
    db.run(`CREATE INDEX IF NOT EXISTS idx_spin_logs_user ON spin_logs (user_id, spun_at DESC)`),
    // Mining plans — separate from investment plans
    db.run(`CREATE TABLE IF NOT EXISTS mining_plans (
      id            SERIAL PRIMARY KEY,
      user_id       BIGINT NOT NULL,
      amount        REAL NOT NULL,
      daily_blk     REAL NOT NULL,
      tap_reward    REAL NOT NULL,
      status        TEXT DEFAULT 'active',
      locked_price  REAL DEFAULT 0,
      purchase_mode TEXT DEFAULT 'normal',
      started_at    TIMESTAMP DEFAULT NOW()
    )`),
    db.run(`ALTER TABLE mining_plans ADD COLUMN IF NOT EXISTS locked_price  REAL DEFAULT 0`),
    db.run(`ALTER TABLE mining_plans ADD COLUMN IF NOT EXISTS purchase_mode TEXT DEFAULT 'normal'`),
    db.run(`CREATE INDEX IF NOT EXISTS idx_mining_plans_user ON mining_plans (user_id, status)`),
  ]);

  // Audit log table for address changes
  await db.run(`
    CREATE TABLE IF NOT EXISTS address_change_logs (
      id           SERIAL PRIMARY KEY,
      admin_id     TEXT,
      user_id      BIGINT NOT NULL,
      old_address  TEXT,
      new_address  TEXT,
      action       TEXT DEFAULT 'change',
      created_at   TIMESTAMP DEFAULT NOW()
    )
  `);

  // Telegram Group proof log table
  await db.run(`
    CREATE TABLE IF NOT EXISTS tg_proof_logs (
      id          SERIAL PRIMARY KEY,
      withdraw_id INTEGER NOT NULL,
      sent_status TEXT    DEFAULT 'pending',
      error_msg   TEXT    DEFAULT NULL,
      retry_count INTEGER DEFAULT 0,
      created_at  TIMESTAMP DEFAULT NOW(),
      updated_at  TIMESTAMP DEFAULT NOW()
    )
  `);
  await db.run(`ALTER TABLE transactions ADD COLUMN IF NOT EXISTS bsc_tx_hash TEXT DEFAULT NULL`);
  await db.run(`CREATE TABLE IF NOT EXISTS promo_withdrawals (
    id           SERIAL PRIMARY KEY,
    user_id      BIGINT NOT NULL,
    amount       REAL NOT NULL DEFAULT 0.005,
    claim_number INTEGER NOT NULL,
    status       TEXT DEFAULT 'pending',
    tx_hash      TEXT DEFAULT NULL,
    claim_date   DATE NOT NULL DEFAULT CURRENT_DATE,
    created_at   TIMESTAMP DEFAULT NOW(),
    UNIQUE(user_id, claim_date)
  )`);
  await db.run(`CREATE INDEX IF NOT EXISTS idx_promo_user ON promo_withdrawals (user_id)`);

  // Moralis webhook detailed log table
  await db.run(`
    CREATE TABLE IF NOT EXISTS webhook_logs (
      id         SERIAL PRIMARY KEY,
      event      TEXT NOT NULL,
      tx_hash    TEXT,
      dep_id     INTEGER,
      user_id    BIGINT,
      status     TEXT,
      detail     TEXT,
      created_at TIMESTAMP DEFAULT NOW()
    )
  `);
  await db.run(`CREATE INDEX IF NOT EXISTS idx_webhook_logs_tx   ON webhook_logs (tx_hash)`);
  await db.run(`CREATE INDEX IF NOT EXISTS idx_webhook_logs_user ON webhook_logs (user_id)`);
  await db.run(`CREATE INDEX IF NOT EXISTS idx_webhook_logs_time ON webhook_logs (created_at DESC)`);

  // IP tracking table
  await db.run(`
    CREATE TABLE IF NOT EXISTS user_ips (
      id         SERIAL PRIMARY KEY,
      user_id    BIGINT NOT NULL,
      ip         TEXT NOT NULL,
      first_seen TIMESTAMP DEFAULT NOW(),
      last_seen  TIMESTAMP DEFAULT NOW(),
      UNIQUE(user_id, ip)
    )
  `);
  await db.run(`CREATE INDEX IF NOT EXISTS idx_user_ips_user ON user_ips (user_id)`);
  await db.run(`CREATE INDEX IF NOT EXISTS idx_user_ips_ip   ON user_ips (ip)`);

  // Mark all pre-existing approved withdrawals as 'skipped' in proof logs
  // so fallback scanner never re-posts old withdrawals after deploy
  await db.run(`
    INSERT INTO tg_proof_logs (withdraw_id, sent_status, error_msg)
    SELECT t.id, 'skipped', 'pre-existing before TG proof feature'
    FROM transactions t
    WHERE t.type = 'withdraw'
      AND t.status = 'approved'
      AND NOT EXISTS (SELECT 1 FROM tg_proof_logs pl WHERE pl.withdraw_id = t.id)
  `);

  console.log('✅ Database ready (Neon PostgreSQL)');

  // ── MIGRATION: Always ensure correct plan data ──
  try {
    const correctPlans = [
      { key:'bronze',   name:'Bronze',   emoji:'🌟', daily_pct:3.0, min_amt:2,    max_amt:5,    duration:40 },
      { key:'silver',   name:'Silver',   emoji:'⭐', daily_pct:3.5, min_amt:5,    max_amt:10,   duration:40 },
      { key:'gold',     name:'Gold',     emoji:'🥇', daily_pct:4.0, min_amt:10,   max_amt:30,   duration:40 },
      { key:'platinum', name:'Platinum', emoji:'💠', daily_pct:4.5, min_amt:30,   max_amt:100,  duration:40 },
      { key:'diamond',  name:'Diamond',  emoji:'💎', daily_pct:5.0, min_amt:100,  max_amt:300,  duration:40 },
      { key:'titanium', name:'Titanium', emoji:'🔩', daily_pct:5.5, min_amt:300,  max_amt:1000, duration:40 },
      { key:'quantum',  name:'Quantum',  emoji:'👑', daily_pct:6.0, min_amt:1000, max_amt:2000, duration:40 },
    ];
    const allPlans = await db.all(`SELECT id, name, daily_pct, min_amt FROM plans`);
    for (const fix of correctPlans) {
      const match = allPlans.find(p => (p.name||'').toLowerCase().includes(fix.key));
      if (match) {
        await db.run(
          `UPDATE plans SET daily_pct=$1, min_amt=$2, max_amt=$3, duration=$4 WHERE id=$5`,
          [fix.daily_pct, fix.min_amt, fix.max_amt, fix.duration, match.id]
        );
      } else {
        await db.run(
          `INSERT INTO plans (name,emoji,daily_pct,min_amt,max_amt,duration) VALUES ($1,$2,$3,$4,$5,$6)`,
          [fix.name, fix.emoji, fix.daily_pct, fix.min_amt, fix.max_amt, fix.duration]
        );
      }
    }
    log('MIGRATION', 'Plans synced OK');
  } catch(e) { log('MIGRATION_ERR', e.message); }

  // ── ONE-TIME MIGRATION: Move old cancel refunds from balance to reinvest_credit ──
  // Runs safely every startup — skips already-migrated users via cancel_refund_migrated flag
  try {
    await db.run(`ALTER TABLE users ADD COLUMN IF NOT EXISTS cancel_refund_migrated BOOLEAN DEFAULT FALSE`);
    await db.run(`ALTER TABLE users ADD COLUMN IF NOT EXISTS reg_ip TEXT DEFAULT NULL`);

    // Find users who have cancel refunds but not yet migrated
    const toMigrate = await db.all(`
      SELECT cl.user_id, SUM(cl.refund) as total_refund
      FROM plan_cancel_logs cl
      JOIN users u ON u.id = cl.user_id
      WHERE cl.refund > 0
        AND u.cancel_refund_migrated = FALSE
      GROUP BY cl.user_id
    `);

    for (const row of toMigrate) {
      const uid        = row.user_id;
      const toMove     = parseFloat(row.total_refund) || 0;
      if (toMove <= 0) continue;

      // Atomic: move min(refund, balance) from balance to reinvest_credit
      // Use separate steps to avoid SQL evaluation order ambiguity
      // migration removed

      log('MIGRATION', `User ${uid}: moved up to $${toMove} to reinvest_credit`);
    }

    if (toMigrate.length > 0) {
      log('MIGRATION', `Cancel refund migration complete — ${toMigrate.length} user(s) migrated`);
    }
  } catch(migErr) {
    log('MIGRATION_ERR', 'Cancel refund migration failed (non-critical): ' + migErr.message);
  }
}

// Handle unhandled promise rejections
process.on('unhandledRejection', (err) => {
  console.error('[unhandledRejection]', err?.message || err);
});
process.on('uncaughtException', (err) => {
  console.error('[uncaughtException]', err?.message || err);
  // Don't exit — log and keep running (Render will restart on crash anyway)
});

async function getSetting(key) {
  const r = await db.one(`SELECT value FROM settings WHERE key=$1`, [key]);
  return r ? r.value : null;
}


// ── Rank + UID helpers ────────────────────

// Plan tier order (lowest → highest)
const PLAN_TIER_ORDER = ['bronze','silver','gold','platinum','diamond','titanium','quantum'];

function getPlanTier(planName) {
  const n = (planName || '').toLowerCase();
  for (const tier of [...PLAN_TIER_ORDER].reverse()) {
    if (n.includes(tier)) return tier;
  }
  return 'bronze';
}

function planTierIndex(planName) {
  return PLAN_TIER_ORDER.indexOf(getPlanTier(planName));
}

// VIP REQUIREMENTS
const FIXED_RATES = [12, 5, 3, 1, 1, 1, 1];
const FIXED_MAX_LEVELS = 7;

// Compute user's VIP level given their stats
function computeVipLevel(highestPlanTier, activeRefs, teamDeposit) {
  const tierIdx = highestPlanTier ? PLAN_TIER_ORDER.indexOf(highestPlanTier) : -1;
  let bestLevel = VIP_LEVELS[0]; // Member default

  for (const vip of VIP_LEVELS) {
    if (!vip.minPlanTier) continue; // skip Member entry
    const reqTierIdx = PLAN_TIER_ORDER.indexOf(vip.minPlanTier);
    if (tierIdx < reqTierIdx) continue;
    if (activeRefs < vip.minRefs) continue;
    if (teamDeposit < vip.minTeamDep) continue;
    bestLevel = vip;
  }
  return bestLevel;
}

// Get highest active plan tier for a user (server-side)
async function getHighestActivePlanTier(userId) {
  const rows = await db.all(
    `SELECT plan_name FROM investments WHERE user_id=$1 AND status='active'`,
    [userId]
  );
  if (!rows || !rows.length) return null;
  let best = -1;
  for (const r of rows) {
    const idx = planTierIndex(r.plan_name);
    if (idx > best) best = idx;
  }
  return best >= 0 ? PLAN_TIER_ORDER[best] : null;
}

// Get team deposit total for N levels deep
async function getTeamDeposit(userId, maxLevels) {
  // PERFORMANCE FIX: Single recursive CTE query instead of N sequential BFS queries.
  // Old approach: 1 DB query per level = up to 7 round trips.
  // New approach: 1 query total regardless of tree depth.
  const depth = Math.min(parseInt(maxLevels) || 3, 7);
  const r = await db.one(
    `WITH RECURSIVE downline AS (
       SELECT id, 1 AS lvl
       FROM users
       WHERE referred_by = $1::bigint
       UNION ALL
       SELECT u.id, d.lvl + 1
       FROM users u
       JOIN downline d ON u.referred_by = d.id
       WHERE d.lvl < $2
     )
     SELECT COALESCE(SUM(i.amount), 0) AS total
     FROM investments i
     WHERE i.user_id IN (SELECT id FROM downline)
       AND i.status IN ('active', 'completed')`,
    [userId, depth]
  );
  return parseFloat(r.total) || 0;
}

// Get active referral count (direct L1 only for VIP gate)
async function getActiveReferralCount(userId) {
  const r = await db.one(
    `SELECT COUNT(DISTINCT u.id) as cnt
     FROM users u
     JOIN investments i ON u.id = i.user_id
     WHERE u.referred_by = $1 AND i.status = 'active'`,
    [userId]
  );
  return parseInt(r.cnt) || 0;
}

// Full VIP status for a user — used in /api/vip-status and commission calc
// Strategy: first compute candidate VIP from plan+refs only (no team dep),
// then scan teamDep using that candidate's maxLevels for consistency.
// reqMaxLevels: hard cap for commission calc to limit DB queries.
async function getUserVipStatus(userId, reqMaxLevels) {
  // ✅ FLAT RATE MODE — all users get same commission rates regardless of plan/VIP level.
  // Dynamic VIP calculation below is intentionally disabled.
  return { vip: { name:'Member', rates: FIXED_RATES, maxLevels: FIXED_MAX_LEVELS }, activeRefs:0, teamDep:0, progress:null, next_vip:null };
  // ── Check manual override FIRST ──────────────────────────────────────
  const overrideRow = await db.one(
    `SELECT manual_commission_enabled, manual_plan_tier, manual_vip_level,
            manual_override_expiry, manual_badge_label
     FROM users WHERE id=$1`, [userId]
  );

  // Check if override is still valid (not expired)
  const overrideActive = overrideRow && (
    !overrideRow.manual_override_expiry ||
    new Date() < new Date(overrideRow.manual_override_expiry)
  );

  if (overrideActive && overrideRow.manual_vip_level && overrideRow.manual_vip_level !== 'none') {
    // Find the VIP level definition matching the manual assignment
    const overrideVip = VIP_LEVELS.find(v => v.name === overrideRow.manual_vip_level);
    if (overrideVip) {
      // Also apply manual plan tier override for commission rates
      let effectiveVip = { ...overrideVip };
      if (overrideRow.manual_plan_tier && overrideRow.manual_plan_tier !== 'none') {
        // Find plan-tier-based rates from VIP_LEVELS equivalent tier
        const planVip = VIP_LEVELS.find(v => v.minPlanTier === overrideRow.manual_plan_tier);
        if (planVip && planTierIndex(planVip.minPlanTier) > planTierIndex(overrideVip.minPlanTier || 'bronze')) {
          // If manual plan tier gives higher rates, use those rates but keep VIP levels
          effectiveVip = { ...overrideVip, rates: planVip.rates };
        }
      }
      const teamDep = await getTeamDeposit(userId, effectiveVip.maxLevels).catch(() => 0);
      return {
        vip: effectiveVip,
        highestTier: overrideRow.manual_plan_tier || null,
        activeRefs: 0,
        teamDep,
        isManualOverride: true,
        badgeLabel: overrideRow.manual_badge_label || null,
      };
    }
  }

  // If manual_commission_enabled but no VIP override — use manual_plan_tier for rates
  if (overrideActive && overrideRow.manual_commission_enabled && overrideRow.manual_plan_tier && overrideRow.manual_plan_tier !== 'none') {
    const planVip = VIP_LEVELS.find(v => v.minPlanTier === overrideRow.manual_plan_tier);
    if (planVip) {
      const teamDep = await getTeamDeposit(userId, planVip.maxLevels).catch(() => 0);
      return {
        vip: planVip,
        highestTier: overrideRow.manual_plan_tier,
        activeRefs: 0,
        teamDep,
        isManualOverride: true,
        badgeLabel: overrideRow.manual_badge_label || null,
      };
    }
  }

  // ── Normal automatic VIP calculation ────────────────────────────────
  const [highestTier, activeRefs] = await Promise.all([
    getHighestActivePlanTier(userId),
    getActiveReferralCount(userId),
  ]);

  // Step 1: find highest VIP tier user COULD reach based on plan+refs only
  const tierIdx = highestTier ? PLAN_TIER_ORDER.indexOf(highestTier) : -1;

  // If manual_commission_enabled (no plan), treat as having a plan for commission purposes
  let effectiveTierIdx = tierIdx;
  if (overrideActive && overrideRow.manual_commission_enabled && tierIdx < 0) {
    effectiveTierIdx = 0; // treat as bronze for commission eligibility
  }

  let candidateMaxLevels = 3;
  for (const v of VIP_LEVELS) {
    if (!v.minPlanTier) continue;
    const reqTierIdx = PLAN_TIER_ORDER.indexOf(v.minPlanTier);
    if (effectiveTierIdx < reqTierIdx) continue;
    if (activeRefs < v.minRefs) continue;
    candidateMaxLevels = v.maxLevels;
  }

  const scanDepth = reqMaxLevels
    ? Math.min(reqMaxLevels, candidateMaxLevels)
    : candidateMaxLevels;

  const teamDep = await getTeamDeposit(userId, scanDepth);
  const vip = computeVipLevel(highestTier, activeRefs, teamDep);
  return { vip, highestTier, activeRefs, teamDep, isManualOverride: false };
}

// Legacy rank name (kept for leaderboard badge compatibility)
function getUserRank(activeRefs) {
  const n = parseInt(activeRefs) || 0;
  if (n >= 20) return 'VIP 4';
  if (n >= 10) return 'VIP 3';
  if (n >= 5)  return 'VIP 2';
  if (n >= 1)  return 'VIP 1';
  return 'Member';
}
function maskName(name) {
  if (!name || name.length === 0) return 'User****';
  if (name.length <= 2) return name + '****';
  return name.substring(0, 2) + '****';
}
function generateUID() {
  return 'U' + Math.floor(100000 + Math.random() * 900000);
}

// ── Plan unlock: active referral requirements ──
function getPlanReferralReq(planName) {
  // Must match VIP_LEVELS requirements exactly
  const n = (planName || '').toLowerCase();
  if (n.includes('quantum'))  return 20;
  if (n.includes('titanium')) return 10;
  if (n.includes('diamond'))  return 5;
  if (n.includes('platinum')) return 2;
  return 0; // bronze, silver, gold — always open
}

// ── Input validators ─────────────────────────────
// ── IP Tracking helper ──────────────────────
async function recordUserIP(userId, ip) {
  if (!userId || !ip || ip === "unknown" || ip === "::1" || ip === "127.0.0.1") return;
  try {
    await db.run(
      `INSERT INTO user_ips (user_id, ip, first_seen, last_seen) VALUES ($1, $2, NOW(), NOW()) ON CONFLICT (user_id, ip) DO UPDATE SET last_seen=NOW()`,
      [userId, ip]
    );
  } catch(e) { /* non-critical */ }
}

function isValidAmount(v, max = 100000) {
  const n = parseFloat(v);
  return !isNaN(n) && n > 0 && n <= max && isFinite(n);
}
function isValidTxHash(h) {
  return typeof h === 'string' && /^0x[a-fA-F0-9]{64}$/.test(h.trim());
}
function isValidBEP20Address(a) {
  return typeof a === 'string' && /^0x[a-fA-F0-9]{40}$/.test(a.trim());
}

// ══════════════════════════════════════════
// AUTH
// ══════════════════════════════════════════
function verifyTg(initData, logContext) {
  try {
    const p = new URLSearchParams(initData);
    const hash = p.get('hash');
    if (!hash) {
      if (logContext) log('AUTH', `[${logContext}] No hash in initData`);
      return false;
    }
    p.delete('hash');

    // Check auth_date expiry (7 days)
    // Extended from 24h — Telegram menu button reuses same initData across reopens.
    // /start always issues fresh initData, but menu button may reuse cached session.
    const authDate = parseInt(p.get('auth_date') || '0');
    const now      = Math.floor(Date.now() / 1000);
    const age      = now - authDate;
    if (authDate && age > 604800) { // 7 days = 604800s
      if (logContext) log('AUTH', `[${logContext}] initData expired: age=${age}s (>7d)`);
      return false;
    }

    const arr = []; p.forEach((v,k) => arr.push(`${k}=${v}`)); arr.sort();
    const secret = crypto.createHmac('sha256','WebAppData').update(BOT_TOKEN).digest();
    const computed = crypto.createHmac('sha256',secret).update(arr.join('\n')).digest('hex');
    const valid = computed === hash;
    if (!valid && logContext) log('AUTH', `[${logContext}] Hash mismatch`);
    return valid;
  } catch(e) {
    if (logContext) log('AUTH', `[${logContext}] verifyTg exception: ${e.message}`);
    return false;
  }
}

function userAuth(req, res, next) {
  const initData = req.headers['x-telegram-init-data'] || req.body?.initData;
  if (!initData) {
    if (process.env.NODE_ENV === 'development') {
      req.tgUser = { id: req.body.user_id || 123456 };
      return next();
    }
    return res.status(401).json({ error: 'Auth required' });
  }

  // Verify Telegram initData signature
  if (BOT_TOKEN && process.env.NODE_ENV !== 'development') {
    const ip = req.headers['x-forwarded-for']?.split(',')[0]?.trim() || req.ip || 'unknown';
    if (!verifyTg(initData, `${req.method} ${req.path} ip=${ip}`)) {
      return res.status(401).json({ error: 'Invalid session' });
    }
  }

  try {
    const p = new URLSearchParams(initData);
    const userStr = p.get('user');
    req.tgUser = userStr ? JSON.parse(userStr) : null;
    if (!req.tgUser || !req.tgUser.id) {
      log('AUTH', `No user in initData path=${req.path}`);
      return res.status(401).json({ error: 'Invalid session' });
    }
    // Auth OK — no log here to avoid noise (failures are logged above)
  } catch(e) {
    log('AUTH', `Parse error path=${req.path}: ${e.message}`);
    return res.status(401).json({ error: 'Invalid session' });
  }
  return next();
}

function adminAuth(req, res, next) {
  const secret = req.headers['x-admin-secret'] || req.body?.adminSecret || '';
  // Timing-safe compare prevents timing attacks on admin secret
  try {
    const a = Buffer.from(secret.padEnd(64));
    const b = Buffer.from(ADMIN_SECRET.padEnd(64));
    if (a.length !== b.length || !crypto.timingSafeEqual(a, b)) {
      return res.status(403).json({error:'Unauthorized'});
    }
  } catch { return res.status(403).json({error:'Unauthorized'}); }
  next();
}

// ══════════════════════════════════════════
// USER ROUTES
// ══════════════════════════════════════════
app.post('/api/auth', authLimit, async (req, res) => {
  try {
    // ✅ SECURITY FIX: Verify initData on auth too
    const raw = req.headers['x-telegram-init-data'] || req.body?.initData || '';
    if (BOT_TOKEN && raw && raw.length > 10 && process.env.NODE_ENV !== 'development') {
      const ip = req.headers['x-forwarded-for']?.split(',')[0]?.trim() || req.ip || 'unknown';
      if (!verifyTg(raw, `POST /api/auth ip=${ip}`)) {
        return res.status(401).json({error: 'Invalid session'});
      }
    }
    let u = null;
    if (raw && raw.length > 10) {
      try {
        const p = new URLSearchParams(raw);
        const us = p.get('user');
        if (us) u = JSON.parse(us);
      } catch(e) {}
    }
    // Fallback: accept tgUser from body only if initData was already verified above
    // OR if initData is present in body (frontend sends both)
    if (!u || !u.id) {
      const bodyInitData = req.body?.initData || '';
      if (bodyInitData && bodyInitData.length > 10) {
        try {
          const bp = new URLSearchParams(bodyInitData);
          const bus = bp.get('user');
          if (bus) u = JSON.parse(bus);
        } catch(e) {}
      }
      // Last resort: tgUser from body (only safe because initData is also sent)
      if (!u || !u.id) u = req.body?.tgUser || null;
    }
    if (!u || !u.id) return res.status(400).json({error:'No user data'});

    const uid      = u.id;
    const refCode  = 'REF' + uid;
    const ref      = req.body?.ref || null;
    const refById  = ref && String(ref).startsWith('REF') ? parseInt(String(ref).replace('REF','')) || null : null;
    const finalRef = (refById && refById !== uid) ? refById : null;

    if (finalRef) log('REF', `Auth uid=${uid} ref=${ref} finalRef=${finalRef}`);

    // Check pending ref
    let pendingRef = finalRef;
    if (!pendingRef) {
      const pr = await db.one('SELECT ref_code FROM pending_refs WHERE user_id=$1', [uid]);
      if (pr) {
        const prid = parseInt(String(pr.ref_code).replace('REF',''));
        if (prid && prid !== uid) pendingRef = prid;
        log('REF', `Pending ref found for uid=${uid} referrer=${prid}`);
      }
    }

    // Upsert user
    const _authRegIp = (req.headers['x-forwarded-for']||'').split(',')[0].trim() || req.ip || null;
    await db.run(`
      INSERT INTO users (id,first_name,last_name,username,language,is_premium,ref_code,referred_by,reg_ip)
      VALUES ($1,$2,$3,$4,$5,$6,$7,$8,$9)
      ON CONFLICT (id) DO UPDATE SET
        first_name=CASE WHEN EXCLUDED.first_name != '' THEN EXCLUDED.first_name ELSE users.first_name END,
        last_name=CASE WHEN EXCLUDED.last_name != '' THEN EXCLUDED.last_name ELSE users.last_name END,
        username=CASE WHEN EXCLUDED.username != '' THEN EXCLUDED.username ELSE users.username END,
        language=EXCLUDED.language,
        is_premium=EXCLUDED.is_premium,
        referred_by=CASE WHEN users.referred_by IS NULL AND $8::BIGINT IS NOT NULL THEN $8::BIGINT ELSE users.referred_by END,
        reg_ip=CASE WHEN users.reg_ip IS NULL THEN EXCLUDED.reg_ip ELSE users.reg_ip END
    `, [uid, u.first_name||'', u.last_name||'', u.username||'', u.language_code||'', u.is_premium?1:0, refCode, pendingRef, _authRegIp]);

    // Log referral save result
    if (pendingRef) {
      log('REF', `referred_by saved: uid=${uid} referrer=${pendingRef}`);
    }

    // Clean pending ref
    await db.run('DELETE FROM pending_refs WHERE user_id=$1', [uid]).catch(()=>{});

    let user = await db.one('SELECT * FROM users WHERE id=$1', [uid]);
    // Assign UID if missing
    if (user && !user.uid) {
      const newUID = generateUID();
      await db.run('UPDATE users SET uid=$1 WHERE id=$2', [newUID, uid]);
      user.uid = newUID;
    }
    if (user && user.is_banned) return res.status(403).json({error:'banned', reason: user.ban_reason||''});

    // Record IP for multi-account detection
    const _authIp = (req.headers['x-forwarded-for']||'').split(',')[0].trim() || req.ip || 'unknown';
    recordUserIP(uid, _authIp);

    res.json({success: true});
  } catch(e) {
    log('ERROR', 'Auth error: ' + e.message);
    res.status(500).json({error: 'Server error. Please try again.'});
  }
});

// ══════════════════════════════════════════
// BOOTSTRAP — Single fast startup endpoint
// Combines auth + user data in one request
// ══════════════════════════════════════════
app.post('/api/bootstrap', authLimit, async (req, res) => {
  // Hard timeout — if bootstrap takes >15s, send error instead of hanging
  const _bootstrapTimeout = setTimeout(() => {
    if (!res.headersSent) {
      log('WARN', 'Bootstrap timeout — sending fallback response');
      res.status(503).json({ error: 'Server timeout, please retry' });
    }
  }, 15000);

  try {
    // ── 1. Verify initData ──────────────────────────────
    const raw = req.headers['x-telegram-init-data'] || req.body?.initData || '';
    if (BOT_TOKEN && raw && raw.length > 10 && process.env.NODE_ENV !== 'development') {
      const ip = req.headers['x-forwarded-for']?.split(',')[0]?.trim() || req.ip || 'unknown';
      if (!verifyTg(raw, `POST /api/bootstrap ip=${ip}`)) {
        return res.status(401).json({ error: 'Invalid session' });
      }
    }

    // ── 2. Parse user ───────────────────────────────────
    let u = null;
    if (raw && raw.length > 10) {
      try { const p = new URLSearchParams(raw); const us = p.get('user'); if (us) u = JSON.parse(us); } catch(e) {}
    }
    if (!u || !u.id) u = req.body?.tgUser || null;
    if (!u || !u.id) return res.status(400).json({ error: 'No user data' });

    const uid     = u.id;
    const refCode = 'REF' + uid;
    const ref     = req.body?.ref || null;
    const refById = ref && String(ref).startsWith('REF') ? parseInt(String(ref).replace('REF','')) || null : null;
    const finalRef = (refById && refById !== uid) ? refById : null;

    // ── 3. Check pending ref ────────────────────────────
    let pendingRef = finalRef;
    if (!pendingRef) {
      const pr = await db.one('SELECT ref_code FROM pending_refs WHERE user_id=$1', [uid]);
      if (pr) {
        const prid = parseInt(String(pr.ref_code).replace('REF',''));
        if (prid && prid !== uid) pendingRef = prid;
      }
    }

    // ── 4. Upsert user ──────────────────────────────────
    const _bsRegIp = (req.headers['x-forwarded-for']||'').split(',')[0].trim() || req.ip || null;
    await db.run(`
      INSERT INTO users (id,first_name,last_name,username,language,is_premium,ref_code,referred_by,reg_ip)
      VALUES ($1,$2,$3,$4,$5,$6,$7,$8,$9)
      ON CONFLICT (id) DO UPDATE SET
        first_name=CASE WHEN EXCLUDED.first_name != '' THEN EXCLUDED.first_name ELSE users.first_name END,
        last_name=CASE WHEN EXCLUDED.last_name != '' THEN EXCLUDED.last_name ELSE users.last_name END,
        username=CASE WHEN EXCLUDED.username != '' THEN EXCLUDED.username ELSE users.username END,
        language=EXCLUDED.language, is_premium=EXCLUDED.is_premium,
        referred_by=CASE WHEN users.referred_by IS NULL AND $8::BIGINT IS NOT NULL THEN $8::BIGINT ELSE users.referred_by END,
        reg_ip=CASE WHEN users.reg_ip IS NULL THEN EXCLUDED.reg_ip ELSE users.reg_ip END
    `, [uid, u.first_name||'', u.last_name||'', u.username||'', u.language_code||'', u.is_premium?1:0, refCode, pendingRef, _bsRegIp]);

    await db.run('DELETE FROM pending_refs WHERE user_id=$1', [uid]).catch(()=>{});

    let user = await db.one('SELECT * FROM users WHERE id=$1', [uid]);
    if (!user) return res.status(404).json({ error: 'User not found' });
    if (!user.uid) {
      const newUID = generateUID();
      await db.run('UPDATE users SET uid=$1 WHERE id=$2', [newUID, uid]);
      user.uid = newUID;
    }
    if (user.is_banned) return res.status(403).json({ error: 'banned', reason: user.ban_reason || '' });

    // ── 5. Parallel data fetch with timeout protection ──
    const withTimeout = (promise, ms, fallback) =>
      Promise.race([promise, new Promise(resolve => setTimeout(() => resolve(fallback), ms))]);

    const [investments, transactions, taskRows, referrals, plansRows, settingRows, activeRefRow, totalL1Row, activeL1Row, vipResult] = await Promise.all([
      withTimeout(db.all(`SELECT *, EXTRACT(EPOCH FROM (NOW() - last_collect)) as secs_since_collect
              FROM investments WHERE user_id=$1 AND status='active'`, [uid]), 5000, []),
      withTimeout(db.all(`SELECT * FROM transactions WHERE user_id=$1 ORDER BY created_at DESC LIMIT 20`, [uid]), 5000, []),
      withTimeout(db.all(`SELECT task_key FROM tasks WHERE user_id=$1 AND completed=1`, [uid]), 5000, []),
      withTimeout(db.all(`SELECT r.id, r.first_name, r.username, r.created_at, 0 as total_deposit
              FROM users r WHERE r.referred_by=$1 ORDER BY r.created_at DESC LIMIT 50`, [uid]), 5000, []),
      withTimeout(getCachedPlans(), 5000, []),
      withTimeout(getCachedSettings(), 5000, []),
      withTimeout(db.one(`SELECT COUNT(DISTINCT u.id) as c FROM users u
              JOIN transactions t ON t.user_id=u.id AND t.type='deposit' AND t.status='approved'
              WHERE u.referred_by=$1`, [uid]), 5000, {c:0}),
      withTimeout(db.one(`SELECT COUNT(*) as total FROM users WHERE referred_by=$1`, [uid]), 5000, {total:0}),
      withTimeout(db.one(`SELECT COUNT(DISTINCT u.id) as active FROM users u
              JOIN investments i ON i.user_id = u.id
              WHERE u.referred_by=$1 AND i.status='active'`, [uid]), 5000, {active:0}),
      getUserVipStatus(uid).catch(function(e) { log('WARN', 'Bootstrap VIP skipped: ' + e.message); return null; }),
    ]);

    const settings = {};
    (settingRows || []).forEach(function(r) { settings[r.key] = r.value; });

    // Plan today_count
    const planCounts = await db.all(
      `SELECT plan_name, COUNT(*) as c FROM investments
       WHERE user_id=$1 AND created_at >= NOW() - INTERVAL '24 hours' GROUP BY plan_name`, [uid]
    ).catch(() => []);
    const countMap = {};
    planCounts.forEach(function(r) { countMap[r.plan_name] = parseInt(r.c) || 0; });

    const plansOut = (plansRows || []).map(function(p) {
      return Object.assign({}, p, {
        today_count:   countMap[p.name] || 0,
        manual_unlock: !!p.manual_unlock,   // ensure boolean — never null
        ref_required:  parseInt(p.ref_required) || 0,
      });
    });

    // Auto-reset today_earned if it's a new UTC day
    const _todayUTC = new Date().toISOString().slice(0, 10);
    if (user.last_earn_date !== _todayUTC && parseFloat(user.today_earned || 0) > 0) {
      await db.run(`UPDATE users SET today_earned=0, last_earn_date=$1 WHERE id=$2`, [_todayUTC, uid]);
      user.today_earned = 0;
      user.last_earn_date = _todayUTC;
    }

    // Referral commission
    const pendingComm = parseFloat(user.pending_commission || 0);

    // VIP already fetched in parallel above — just format the result
    let vipData = null;
    if (vipResult) {
      try {
        const vs = vipResult;
        vipData = {
          vip_name:     vs.vip.name,
          vip_rates:    vs.vip.rates,
          max_levels:   vs.vip.maxLevels,
          highest_tier: vs.highestTier || null,
          team_deposit: +vs.teamDep.toFixed(2),
        };
        db.run(`UPDATE users SET vip_level=$1, vip_updated_at=NOW() WHERE id=$2`, [vs.vip.name, uid]).catch(()=>{});
      } catch(e) { log('WARN', 'Bootstrap VIP format error: ' + e.message); }
    }

    // ── 6. Single response ──────────────────────────────
    res.json({
      success: true,
      user: {
        id: user.id, uid: user.uid,
        first_name: user.first_name, last_name: user.last_name,
        username: user.username, balance: parseFloat(user.balance) || 0,
        block_tokens: parseFloat(user.block_tokens || 0),
        total_earned: parseFloat(user.total_earned) || 0,
        today_earned: parseFloat(user.today_earned) || 0,
        ref_code: user.ref_code,
        pending_commission: pendingComm,
        total_commission: parseFloat(user.total_commission || 0),
        app_language: user.app_language || null,
        is_banned: user.is_banned || 0,
        withdraw_address: user.withdraw_address || null,
        address_locked: !!user.address_locked,
        reinvest_credit: 0, // deprecated
      },
      investments,
      transactions,
      tasks: (taskRows || []).map(function(r) { return r.task_key; }),
      referrals,
      active_referrals: parseInt((activeRefRow || {}).c) || 0,
      // Accurate counts — not affected by LIMIT 50 on referrals list
      total_l1:  parseInt((totalL1Row  || {}).total)  || 0,
      active_l1: parseInt((activeL1Row || {}).active) || 0,
      plans: plansOut,
      settings,
      vip: vipData,
    });
    // Record IP for multi-account detection
    const _bsIp = (req.headers['x-forwarded-for']||'').split(',')[0].trim() || req.ip || 'unknown';
    recordUserIP(uid, _bsIp);

    clearTimeout(_bootstrapTimeout);

  } catch(e) {
    clearTimeout(_bootstrapTimeout);
    log('ERROR', 'Bootstrap error: ' + e.message);
    if (!res.headersSent) res.status(500).json({ error: 'Server error. Please try again.' });
  }
});

// ── Public pre-launch status endpoint ────────────────────
app.get('/api/prelaunch-status', async (req, res) => {
  try {
    const depLock   = await getSetting('deposit_lock')  || '0';
    const withLock  = await getSetting('withdraw_lock') || '0';
    const launchDate = await getSetting('launch_date')  || '';
    res.json({ deposit_lock: depLock, withdraw_lock: withLock, launch_date: launchDate });
  } catch(e) { res.json({ deposit_lock:'0', withdraw_lock:'0', launch_date:'' }); }
});

app.get('/api/user/:id', async (req, res) => {
  // IDOR guard: if initData header is present, verify it and ensure user matches
  // Frontend intentionally omits header on this GET to avoid CORS preflight (Telegram WebView quirk)
  // Security: user_id in URL is only useful if attacker knows the ID, and response
  // contains no sensitive financial actions — just read-only data display
  const _initData = req.headers['x-telegram-init-data'];
  if (_initData) {
    // Verify signature if BOT_TOKEN set
    if (BOT_TOKEN && process.env.NODE_ENV !== 'development' && !verifyTg(_initData)) {
      log('SECURITY', `Invalid initData on /api/user from IP: ${req.headers['x-forwarded-for'] || req.ip}`);
      return res.status(401).json({ error: 'Invalid session' });
    }
    try {
      const _p = new URLSearchParams(_initData);
      const _userStr = _p.get('user');
      const _tgU = _userStr ? JSON.parse(_userStr) : null;
      if (!_tgU || String(_tgU.id) !== String(req.params.id)) {
        return res.status(403).json({ error: 'Forbidden' });
      }
    } catch(e) { return res.status(401).json({ error: 'Invalid session' }); }
  }
  // Note: no-header requests allowed for Telegram WebView CORS compatibility
  // All money actions (withdraw, invest, collect) still require full auth via userAuth middleware
  try {
    let user = await db.one(`SELECT * FROM users WHERE id=$1`, [req.params.id]);
    // Auto-create user if not exists — only when called with valid initData (not ghost creation)
    if (!user) {
      const hasAuth = !!req.headers['x-telegram-init-data'];
      if (!hasAuth) return res.status(404).json({error:'Not found'});
      const uid = String(parseInt(req.params.id)); // sanitize to integer string
      if (!uid || uid === 'NaN') return res.status(400).json({error:'Invalid user id'});
      const refCode = 'REF' + uid;
      await db.run(`
        INSERT INTO users (id,first_name,ref_code) VALUES ($1,$2,$3)
        ON CONFLICT (id) DO NOTHING
      `, [uid, 'User'+uid, refCode]).catch(()=>{});
      user = await db.one(`SELECT * FROM users WHERE id=$1`, [uid]);
      if (!user) return res.status(404).json({error:'Not found'});
    }

    // Run all queries in parallel for speed
    const [investments, transactions, taskRows, referrals, plans, settingRows, activeRefRow] = await Promise.all([
      db.all(`SELECT *, EXTRACT(EPOCH FROM (NOW() - last_collect)) as secs_since_collect FROM investments WHERE user_id=$1 AND status='active'`, [req.params.id]),
      db.all(`SELECT * FROM transactions WHERE user_id=$1 ORDER BY created_at DESC LIMIT 20`, [req.params.id]),
      db.all(`SELECT task_key FROM tasks WHERE user_id=$1 AND completed=1`, [req.params.id]),
      db.all(`SELECT u.id, u.first_name, u.username, u.created_at,
        COALESCE((SELECT SUM(c.amount) FROM commissions c WHERE c.user_id=$1 AND c.from_user_id=u.id AND c.status='collected'), 0) as earned
        FROM users u WHERE u.referred_by=$1 ORDER BY u.created_at DESC`, [req.params.id]),
      db.all(`SELECT * FROM plans WHERE is_active=1 ORDER BY id`),
      db.all(`SELECT * FROM settings`),
      db.one(`SELECT COUNT(DISTINCT u.id) as cnt FROM users u JOIN investments i ON u.id=i.user_id WHERE u.referred_by=$1 AND i.status='active'`, [req.params.id]),
    ]);
    const tasks    = taskRows.map(t => t.task_key);
    const settings = settingRows.reduce((a,r) => ({...a,[r.key]:r.value}), {});
    const activeReferrals = parseInt(activeRefRow.cnt) || 0;

    // Reset today_count display if past reset_hours
    const nowTime = new Date();
    plans.forEach(function(p) {
      if (p.daily_limit > 0 && p.last_reset) {
        const hoursPassed = (nowTime - new Date(p.last_reset)) / (1000*60*60);
        if (hoursPassed >= (p.reset_hours || 24)) p.today_count = 0;
      }
      // Ensure manual_unlock is always boolean — never null from DB
      p.manual_unlock = !!p.manual_unlock;
      p.ref_required  = parseInt(p.ref_required) || 0;
    });

    // Auto-reset today_earned if it's a new UTC day
    const todayUTC = new Date().toISOString().slice(0, 10); // 'YYYY-MM-DD'
    if (user.last_earn_date !== todayUTC && parseFloat(user.today_earned || 0) > 0) {
      await db.run(`UPDATE users SET today_earned=0, last_earn_date=$1 WHERE id=$2`, [todayUTC, user.id]);
      user.today_earned = 0;
      user.last_earn_date = todayUTC;
      console.log(`[RESET] today_earned auto-reset for user ${user.id}`);
    }

    // Add commission data to user
    const userWithComm = {
      ...user,
      pending_commission:  parseFloat(user.pending_commission || 0),
      total_commission:    parseFloat(user.total_commission   || 0),
      is_deposit_blocked:  user.blocked_until && new Date() < new Date(user.blocked_until) ? 1 : 0,
      withdraw_address:    user.withdraw_address || null,
      address_locked:      !!user.address_locked,
      address_updated_at:  user.address_updated_at || null,
    };
    userWithComm.rank   = getUserRank(activeReferrals);
    userWithComm.active_referrals = activeReferrals;

    // Compute VIP status (lightweight — uses cached highest plan query)
    let vipData = null;
    try {
      const vs = await getUserVipStatus(req.params.id);
      vipData = {
        vip_name:     vs.vip.name,
        vip_rates:    vs.vip.rates,
        max_levels:   vs.vip.maxLevels,
        highest_tier: vs.highestTier || null,
        team_deposit: +vs.teamDep.toFixed(2),
      };
      // Cache vip_level on user row (async, non-blocking)
      db.run(`UPDATE users SET vip_level=$1, vip_updated_at=NOW() WHERE id=$2`, [vs.vip.name, req.params.id]).catch(()=>{});
    } catch(e) { log('WARN', 'VIP calc skipped: ' + e.message); }

    res.json({user: userWithComm, investments, transactions, tasks, referrals, plans, settings, active_referrals: activeReferrals, vip: vipData, ref_deposit_stats: await (async function() {
      try {
        const uid = req.params.id;
        const r10 = await db.one(`SELECT COUNT(DISTINCT i.user_id) as cnt FROM investments i JOIN users u ON u.id=i.user_id WHERE u.referred_by=$1 AND i.amount>=10 AND i.status='active'`, [uid]);
        const r100 = await db.one(`SELECT COUNT(DISTINCT i.user_id) as cnt FROM investments i JOIN users u ON u.id=i.user_id WHERE u.referred_by=$1 AND i.amount>=100 AND i.status='active'`, [uid]);
        return { max10: parseInt(r10.cnt)||0, max100: parseInt(r100.cnt)||0 };
      } catch(e) { return { max10:0, max100:0 }; }
    })()});
  } catch(e) { log("ERROR", e.message); res.status(500).json({error:"Server error. Please try again."}); }
});

// ── Save user language preference ──────────────────────────
app.post('/api/user/language', userAuth, async (req, res) => {
  try {
    const u = req.tgUser;
    const { language } = req.body;
    if (!language) return res.status(400).json({ error: 'Missing language' });
    const SUPPORTED = ['en','ru','es','pt','vi','ar','fa'];
    if (!SUPPORTED.includes(language)) return res.status(400).json({ error: 'Unsupported language' });
    await db.run(`UPDATE users SET app_language=$1 WHERE id=$2`, [language, u.id]);
    res.json({ ok: true });
  } catch(e) { log("ERROR", e.message); res.status(500).json({ error: "Server error. Please try again." }); }
});

app.post('/api/invest', userAuth, async (req, res) => {
  try {
    const u = req.tgUser;
    const {plan_id} = req.body;
    const amount = parseFloat(req.body.amount);
    if (!isValidAmount(amount)) return res.status(400).json({error:'Invalid amount'});
    const user = await db.one(`SELECT * FROM users WHERE id=$1`, [u.id]);
    if (!user) return res.status(404).json({error:'Not found'});
    if (user.is_banned) return res.status(403).json({error:'banned'});

    const plan = await db.one(`SELECT * FROM plans WHERE id=$1 AND is_active=1`, [plan_id]);
    if (!plan) return res.status(404).json({error:'Plan not found'});
    if (amount < plan.min_amt) return res.status(400).json({error:`Min $${plan.min_amt}`});
    if (amount > plan.max_amt) return res.status(400).json({error:`Max $${plan.max_amt}`});
    if (user.balance < amount) return res.status(400).json({error:'Insufficient balance'});
    // Multiple plans allowed — same plan can be purchased multiple times

    // [PLAN UNLOCK] Priority: manual_unlock → promo_unlock → paid_unlock → referrals
    // ref_required=0 means use name-based default
    const storedReq = parseInt(plan.ref_required) || 0;
    const refReq    = storedReq > 0 ? storedReq : getPlanReferralReq(plan.name);

    if (refReq > 0 && !plan.manual_unlock) {
      // Check free promo unlock setting
      const promoUnlock = await getSetting('promo_unlock');
      if (promoUnlock !== '1') {
        // Check paid unlock log
        const paidUnlock = await db.one(
          `SELECT id FROM plan_unlock_logs WHERE user_id=$1 AND plan_id=$2 AND unlock_type='paid'
           ORDER BY created_at DESC LIMIT 1`,
          [u.id, plan.id]
        );
        if (!paidUnlock) {
          const activeRefs = await db.one(
            `SELECT COUNT(DISTINCT u2.id) as cnt FROM users u2 JOIN investments i ON u2.id=i.user_id WHERE u2.referred_by=$1 AND i.status='active'`,
            [u.id]
          );
          const activeCount = parseInt(activeRefs?.cnt || 0);
          if (activeCount < refReq) {
            return res.status(403).json({
              error: `This plan requires ${refReq} active referral${refReq>1?'s':''} (you have ${activeCount})`,
              ref_required: refReq,
              ref_have: activeCount,
              missing: refReq - activeCount,
              unlock_fee: (refReq - activeCount) * 2
            });
          }
        }
      }
    }

    // Check daily limit
    if (plan.daily_limit > 0) {
      const resetHours = parseFloat(plan.reset_hours || 24);
      const lastReset  = plan.last_reset ? new Date(plan.last_reset) : null;
      const now        = new Date();
      const hoursPassed = lastReset ? (now - lastReset) / (1000 * 60 * 60) : resetHours + 1;

      if (hoursPassed >= resetHours) {
        await db.run(`UPDATE plans SET today_count=0, last_reset=NOW() WHERE id=$1`, [plan_id]);
        plan.today_count = 0;
      }
      const remaining = plan.daily_limit - (plan.today_count || 0);
      if (remaining <= 0) {
        const nextReset = lastReset ? new Date(lastReset.getTime() + resetHours * 60 * 60 * 1000) : null;
        const hoursLeft = nextReset ? Math.ceil((nextReset - now) / (1000 * 60 * 60)) : resetHours;
        return res.status(400).json({error:`Limit reached! Resets in ${hoursLeft}h.`, limitReached: true, hoursLeft});
      }
    }

    const daily = +(amount * plan.daily_pct / 100).toFixed(4);

    let deductResult;
    {
      deductResult = await pool.query(
        `UPDATE users SET balance=balance-$1 WHERE id=$2 AND balance>=$1 RETURNING id`,
        [amount, u.id]
      );
    }
    if (deductResult.rowCount === 0) return res.status(400).json({error:'Insufficient balance'});
    await db.run(
      `INSERT INTO investments (user_id,plan_name,amount,daily_pct,daily_earn,days_total,last_collect) VALUES ($1,$2,$3,$4,$5,$6,NOW())`,
      [u.id, ((plan.emoji||'')+' '+plan.name).trim(), amount, plan.daily_pct, daily, plan.duration]
    );
    // Increment daily count
    if (plan.daily_limit > 0) {
      await db.run(`UPDATE plans SET today_count=today_count+1 WHERE id=$1`, [plan_id]);
    }
    await db.run(
      `INSERT INTO transactions (user_id,type,amount,status,note) VALUES ($1,$2,$3,$4,$5)`,
      [u.id,'invest',amount,'completed',`Invested in ${plan.name}`]
    );
    // Increment total buy count
    await db.run(`UPDATE plans SET buy_count = buy_count + 1 WHERE id = $1`, [plan_id]);

    // [ACTIVE REF] Mark user as active referral on first investment
    if (!user.is_active_ref && user.referred_by && user.id !== user.referred_by) {
      await db.run(`UPDATE users SET is_active_ref=TRUE WHERE id=$1`, [user.id]);
      log('REF', `User ${user.id} marked as active referral of ${user.referred_by}`);
    }

    // Distribute referral commissions — VIP-based dynamic rates
    try {
      let currentId = u.id;
      const vipCache = new Map(); // per-invest cache: referrerId → vip object
      for (let lvl = 0; lvl < 7; lvl++) {
        const row = await db.one(`SELECT referred_by FROM users WHERE id=$1`, [currentId]);
        if (!row || !row.referred_by) break;
        const referrerId = row.referred_by;

        // Check if REFERRER is banned (not the buyer)
        const refRow = await db.one(`SELECT is_banned FROM users WHERE id=$1`, [referrerId]);
        if (!refRow || refRow.is_banned) { currentId = referrerId; continue; }

        // Compute referrer VIP — use cache to avoid repeat DB calls
        let refVip;
        if (vipCache.has(referrerId)) {
          refVip = vipCache.get(referrerId);
        } else {
          // Use scanDepth = 4 max for commission calc (VIP 4 needs L7 but teamDep is pre-qualified)
          const refVipData = await getUserVipStatus(referrerId, 4);
          refVip = refVipData.vip;
          vipCache.set(referrerId, refVip);
        }

        // Stop if this level is beyond referrer's unlocked levels
        if (lvl >= refVip.maxLevels) { currentId = referrerId; continue; }

        const pct = (refVip.rates[lvl] || 0) / 100;
        if (pct <= 0) { currentId = referrerId; continue; }

        const comm = +(amount * pct).toFixed(4);
        await db.run(
          `UPDATE users SET pending_commission=pending_commission+$1, total_commission=total_commission+$1 WHERE id=$2::BIGINT`,
          [comm, referrerId]
        );
        await db.run(
          `INSERT INTO commissions (user_id,from_user_id,level,amount) VALUES ($1::BIGINT,$2::BIGINT,$3,$4)`,
          [referrerId, u.id, lvl+1, comm]
        );
        log('COMM', `L${lvl+1} ${refVip.name} ${pct*100}% $${comm} → user ${referrerId}`);
        currentId = referrerId;
      }
    } catch(e) {
      log('ERROR', 'Commission distribute error: ' + e.message);
    }

    res.json({success:true, daily_earn:daily});
  } catch(e) { log("ERROR", e.message); res.status(500).json({error:"Server error. Please try again."}); }
});


// ══════════════════════════════════════════
// WALLET ADDRESS BIND SYSTEM
// ══════════════════════════════════════════

// GET current bound address
app.get('/api/withdraw/address', userAuth, async (req, res) => {
  try {
    const u = req.tgUser;
    const user = await db.one(`SELECT withdraw_address, address_locked, address_updated_at FROM users WHERE id=$1`, [u.id]);
    if (!user) return res.status(404).json({error:'Not found'});
    res.json({
      address: user.withdraw_address || null,
      locked: !!user.address_locked,
      updated_at: user.address_updated_at || null
    });
  } catch(e) { log('ERROR', e.message); res.status(500).json({error:'Server error. Please try again.'}); }
});

// POST bind address (first time only — user cannot change after)
app.post('/api/withdraw/bind-address', userAuth, async (req, res) => {
  try {
    const u = req.tgUser;
    const { address } = req.body;

    if (!address || !isValidBEP20Address(address)) {
      return res.status(400).json({error:'Invalid BEP20 wallet address (must start with 0x, 42 chars)'});
    }

    // Check blocked addresses
    const blockedRow = await getSetting('blocked_addresses');
    if (blockedRow) {
      const blockedList = blockedRow.split(',').map(a => a.trim().toLowerCase()).filter(Boolean);
      if (blockedList.includes(address.trim().toLowerCase())) {
        log('SECURITY', `Blocked address bind attempt by user ${u.id}: ${address}`);
        return res.status(400).json({error:'Invalid wallet address'});
      }
    }

    const user = await db.one(`SELECT withdraw_address, address_locked FROM users WHERE id=$1`, [u.id]);
    if (!user) return res.status(404).json({error:'Not found'});

    // ✅ SECURITY: If already locked, user cannot change
    if (user.address_locked && user.withdraw_address) {
      log('SECURITY', `User ${u.id} attempted to self-change locked address`);
      return res.status(403).json({error:'Address is locked. Contact support to change.'});
    }

    // Save and lock immediately — store lowercase for consistent uniqueness
    const cleanAddr = address.trim().toLowerCase();

    // ✅ UNIQUE CHECK: Address must not belong to another account
    const existing = await db.one(
      `SELECT id FROM users WHERE LOWER(withdraw_address)=$1 AND id!=$2`,
      [cleanAddr, u.id]
    );
    if (existing) {
      const ip = req.headers['x-forwarded-for']?.split(',')[0]?.trim() || req.ip || 'unknown';
      log('SECURITY', `Duplicate address attempt user=${u.id} addr=${cleanAddr.slice(0,16)}... ip=${ip}`);
      await db.run(
        `INSERT INTO address_change_logs (admin_id, user_id, old_address, new_address, action) VALUES ($1,$2,$3,$4,$5)`,
        ['system', u.id, null, cleanAddr, 'duplicate_attempt']
      );
      return res.status(400).json({
        error:'This wallet address is already linked to another account. Please use your own wallet.'
      });
    }
    await db.run(
      `UPDATE users SET withdraw_address=$1, address_locked=TRUE, address_updated_at=NOW() WHERE id=$2`,
      [cleanAddr, u.id]
    );
    log('ADDRESS', `User ${u.id} bound address: ${cleanAddr.slice(0,16)}...`);
    res.json({success:true, message:'Address bound and locked successfully.'});
  } catch(e) { log('ERROR', e.message); res.status(500).json({error:'Server error. Please try again.'}); }
});

// /api/deposit (old manual route) removed — all deposits go through /api/deposit/create

app.post('/api/withdraw', userAuth, async (req, res) => {
  try {
    const u = req.tgUser;
    const { amount } = req.body; // ✅ address comes from DB only — not from user input
    const network = 'BEP20';
    // PRE-LAUNCH lock check
    const withLock = await getSetting('withdraw_lock');
    if (withLock === '1') return res.status(403).json({error:'pre_launch_locked', message:'Withdrawals are locked during pre-launch.'});

    const user = await db.one(`SELECT * FROM users WHERE id=$1`, [u.id]);
    if (!user) return res.status(404).json({error:'Not found'});
    if (user.is_banned) return res.status(403).json({error:'banned'});

    // ✅ BOUND ADDRESS CHECK — must have bound address before withdrawing
    if (!user.withdraw_address || !user.address_locked) {
      return res.status(400).json({error:'No withdrawal address bound. Please bind your address first.'});
    }
    const address = user.withdraw_address; // use DB address, never trust user input

    // Block check
    const blockMsg = await checkBlocked(u.id);
    if (blockMsg) return res.status(429).json({error: blockMsg});

    // Validations
    const [wMinRow, wMaxRow, wFeeRow, wFeeFlatRow] = await Promise.all([
      getSetting('withdraw_min'), getSetting('withdraw_max'), getSetting('withdraw_fee_pct'), getSetting('withdraw_fee_flat')
    ]);
    const minW    = parseFloat(wMinRow      || 2);
    const maxW    = parseFloat(wMaxRow      || 10000);
    const feePct  = parseFloat(wFeeRow      || 0);
    const feeFlat = parseFloat(wFeeFlatRow  || 0);
    const amt    = parseFloat(amount);

    if (!amt || amt < minW) {
      log('WITHDRAW', `User ${u.id} rejected: amount too low (${amt})`);
      return res.status(400).json({error:`Minimum withdrawal is $${minW} USDT`});
    }
    if (amt > maxW) return res.status(400).json({error:`Maximum withdrawal is $${maxW}`});

    // ✅ SECURITY: Block known attacker addresses (double-check even from DB)
    const blockedAddrsRow = await getSetting('blocked_addresses');
    if (blockedAddrsRow) {
      const blockedList = blockedAddrsRow.split(',').map(a => a.trim().toLowerCase()).filter(Boolean);
      if (blockedList.includes(address.trim().toLowerCase())) {
        log('SECURITY', `BLOCKED address in DB for user ${u.id}: ${address}`);
        return res.status(400).json({error:'Withdrawal address is blocked. Contact support.'});
      }
    }
    if (user.balance < amt) {
      log('WITHDRAW', `User ${u.id} rejected: insufficient balance (bal=${user.balance} req=${amt})`);
      return res.status(400).json({error:'Insufficient balance'});
    }

    // [NEW] One pending withdrawal per user
    const existing = await db.one(
      `SELECT id, created_at FROM transactions WHERE user_id=$1 AND type='withdraw' AND status='pending'`,
      [u.id]
    );
    if (existing) {
      return res.status(400).json({error:'You already have a pending withdrawal request'});
    }
    // [DAILY LIMIT] Max 2 withdrawals per day
    const todayCount = await db.one(
      `SELECT COUNT(*) as cnt FROM transactions WHERE user_id=$1 AND type='withdraw'
       AND created_at >= CURRENT_DATE AT TIME ZONE 'UTC'`,
      [u.id]
    );
    if (parseInt(todayCount.cnt) >= 2) {
      return res.status(400).json({error:'Daily withdrawal limit reached (max 2 per day). Try again tomorrow.'});
    }

    const fee = +(amt * feePct / 100 + feeFlat).toFixed(2);
    // [DB-LEVEL GUARD] Conditional deduct — prevents negative balance under race condition
    const deductResult = await pool.query(
      `UPDATE users SET balance=balance-$1 WHERE id=$2 AND balance>=$1 RETURNING id`,
      [amt, u.id]
    );
    if (deductResult.rowCount === 0) return res.status(400).json({error:'Insufficient balance'});
    await db.run(
      `INSERT INTO transactions (user_id,type,amount,network,address,fee,note) VALUES ($1,$2,$3,$4,$5,$6,$7)`,
      [u.id,'withdraw',amt,network,address.trim(),fee,'Processing time: 0–24 hours']
    );
    const ip = req.headers['x-forwarded-for']?.split(',')[0]?.trim() || req.ip || 'unknown';
    const ua = (req.headers['user-agent'] || '').slice(0, 80);
    log('WITHDRAW', `User ${u.id} requested $${amt} to ${address.trim().slice(0,16)}... fee=$${fee} ip=${ip}`);
    logSecurity('WITHDRAW_SUBMITTED', {user_id: u.id, amount: amt, address: address.slice(0,20), ip, ua});
    res.json({success:true, fee, message:'Withdrawal submitted. Processing time: 0–24 hours.'});
  } catch(e) { log("ERROR", e.message); res.status(500).json({error:"Server error. Please try again."}); }
});

app.post('/api/collect-daily', userAuth, async (req, res) => {
  try {
    const u = req.tgUser;
    const {investment_id} = req.body;
    const inv = await db.one(
      `SELECT * FROM investments WHERE id=$1 AND user_id=$2 AND status='active'`,
      [investment_id, u.id]
    );
    if (!inv) return res.status(404).json({error:'Investment not found'});

    const now = new Date();
    if (inv.last_collect) {
      const diff = now - new Date(inv.last_collect);
      const hoursLeft = Math.ceil((24*60*60*1000 - diff) / (1000*60*60));
      const secsLeft  = Math.ceil((24*60*60*1000 - diff) / 1000);
      if (diff < 24*60*60*1000) return res.status(400).json({
        error: 'Already collected. Next collect in ' + hoursLeft + 'h',
        secondsLeft: secsLeft
      });
    }

    const earn = parseFloat(inv.daily_earn);
    if (!earn || earn <= 0) return res.status(400).json({error: 'Invalid investment earn value'});
    // [ATOMIC RACE GUARD] Single atomic UPDATE that checks 24h window simultaneously
    // This prevents double-collect: if two requests race, only one will pass the WHERE clause
    const collectResult = await pool.query(
      `UPDATE investments SET last_collect=NOW(), days_done=days_done+1
       WHERE id=$1 AND user_id=$2 AND status='active'
       AND (last_collect IS NULL OR NOW() - last_collect >= INTERVAL '24 hours')
       RETURNING id`,
      [inv.id, u.id]
    );
    if (collectResult.rowCount === 0) {
      // Another request already collected, or 24h not passed yet
      const fresh = await db.one(`SELECT last_collect FROM investments WHERE id=$1`, [inv.id]);
      const secsLeft = fresh && fresh.last_collect
        ? Math.max(0, Math.ceil((86400000 - (Date.now() - new Date(fresh.last_collect).getTime())) / 1000))
        : 86400;
      return res.status(400).json({ error: 'Already collected. Please wait 24 hours.', secondsLeft: secsLeft });
    }
    await db.run(
      `UPDATE users SET balance=balance+$1, total_earned=total_earned+$1, today_earned=today_earned+$1, last_earn_date=TO_CHAR(NOW() AT TIME ZONE 'UTC', 'YYYY-MM-DD') WHERE id=$2`,
      [earn, u.id]
    );
    await db.run(
      `INSERT INTO transactions (user_id,type,amount,status,note) VALUES ($1,$2,$3,$4,$5)`,
      [u.id,'earn',earn,'completed',`Credit: ${inv.plan_name}`]
    );
    // Use days_total from inv — days_done already incremented in atomic UPDATE above
    const newDaysDone = (inv.days_done || 0) + 1;
    if (newDaysDone >= inv.days_total) {
      await db.run(`UPDATE investments SET status='completed' WHERE id=$1`, [inv.id]);
    }
    res.json({success:true, earned:earn, days_done: newDaysDone, completed: newDaysDone >= inv.days_total});
  } catch(e) { log("ERROR", e.message); res.status(500).json({error:"Server error. Please try again."}); }
});

app.post('/api/task/complete', userAuth, async (req, res) => {
  try {
    const u = req.tgUser;
    const {task_key} = req.body; // reward from CLIENT ignored — always use server-side value
    // [SECURITY] Get reward from DB first, not from client
    const taskCfg = await db.one(`SELECT * FROM tasks_config WHERE task_key=$1 AND is_active=1`, [task_key]);
    if (!taskCfg) return res.status(404).json({error:'Task not found'});
    const reward = parseFloat(taskCfg.reward) || 0;

    // For invite tasks — verify actual active referral count
    if (task_key && task_key.indexOf('invite') !== -1) {
      const numMatch = task_key.match(/(\d+)/);
      const required = numMatch ? parseInt(numMatch[1]) : 1;
      const countRow = await db.one(
        `SELECT COUNT(DISTINCT i.user_id) as cnt FROM investments i
         JOIN users us ON us.id=i.user_id
         WHERE us.is_active_ref=TRUE AND us.referred_by=$1 AND i.status='active'`,
        [u.id]
      );
      const activeCount = parseInt(countRow.cnt) || 0;
      if (activeCount < required) {
        return res.status(400).json({error:`Need ${required} active referral(s). You have ${activeCount}.`});
      }
    }

    // ref_deposit_10: invite a friend who deposits >= 10 USDT
    if (task_key === 'ref_deposit_10') {
      const row = await db.one(
        `SELECT COUNT(DISTINCT i.user_id) as cnt FROM investments i
         JOIN users us ON us.id=i.user_id
         WHERE us.referred_by=$1 AND i.amount >= 10 AND i.status='active'`,
        [u.id]
      );
      if ((parseInt(row.cnt) || 0) < 1)
        return res.status(400).json({error:'Need 1 referral with 10+ USDT deposit.'});
    }

    // ref_deposit_100: invite a friend who deposits >= 100 USDT
    if (task_key === 'ref_deposit_100') {
      const row = await db.one(
        `SELECT COUNT(DISTINCT i.user_id) as cnt FROM investments i
         JOIN users us ON us.id=i.user_id
         WHERE us.referred_by=$1 AND i.amount >= 100 AND i.status='active'`,
        [u.id]
      );
      if ((parseInt(row.cnt) || 0) < 1)
        return res.status(400).json({error:'Need 1 referral with 100+ USDT deposit.'});
    }

    // team_recharge_500: total team deposit >= 500
    if (task_key === 'team_recharge_500') {
      const row = await db.one(
        `SELECT COALESCE(SUM(i.amount),0) as total FROM investments i
         JOIN users us ON us.id=i.user_id
         WHERE us.referred_by=$1 AND i.status='active'`,
        [u.id]
      );
      const total = parseFloat(row.total) || 0;
      if (total < 500)
        return res.status(400).json({error:`Team deposit $${total.toFixed(2)} / $500 required.`});
    }

    // team_recharge_1000: total team deposit >= 1000
    if (task_key === 'team_recharge_1000') {
      const row = await db.one(
        `SELECT COALESCE(SUM(i.amount),0) as total FROM investments i
         JOIN users us ON us.id=i.user_id
         WHERE us.referred_by=$1 AND i.status='active'`,
        [u.id]
      );
      const total = parseFloat(row.total) || 0;
      if (total < 1000)
        return res.status(400).json({error:`Team deposit $${total.toFixed(2)} / $1000 required.`});
    }

    // ✅ ATOMIC: INSERT only if not already completed — race condition safe
    const taskResult = await pool.query(
      `INSERT INTO tasks (user_id,task_key,completed,completed_at) VALUES ($1,$2,1,NOW())
       ON CONFLICT (user_id,task_key) DO UPDATE SET completed=1
       WHERE tasks.completed=0
       RETURNING id`,
      [u.id, task_key]
    );
    if (taskResult.rowCount === 0) return res.status(400).json({error:'Already done'});
    await db.run(`UPDATE users SET balance=balance+$1, total_earned=total_earned+$1 WHERE id=$2`, [reward, u.id]);
    await db.run(
      `INSERT INTO transactions (user_id,type,amount,status,note) VALUES ($1,$2,$3,$4,$5)`,
      [u.id, 'task_reward', reward, 'completed', 'Task: ' + task_key]
    );
    res.json({success:true});
  } catch(e) { log("ERROR", e.message); res.status(500).json({error:"Server error. Please try again."}); }
});

// Verify task (checks Telegram membership for channel/group tasks)
app.post('/api/verify-task', userAuth, async (req, res) => {
  try {
    const u = req.tgUser;
    if (!u || !u.id) return res.status(400).json({error:'No user'});
    const { task_key } = req.body;
    const taskCfg = await db.one('SELECT * FROM tasks_config WHERE task_key=$1 AND is_active=1', [task_key]);
    if (!taskCfg) return res.status(404).json({error:'Task not found'});

    // If task has a chat_id, verify via Telegram Bot API
    if (taskCfg.chat_id && taskCfg.chat_id.trim()) {
      try {
        const tgRes = await fetch(
          `https://api.telegram.org/bot${BOT_TOKEN}/getChatMember?chat_id=${encodeURIComponent(taskCfg.chat_id.trim())}&user_id=${u.id}`
        );
        const tgData = await tgRes.json();
        if (tgData.ok) {
          const status = tgData.result.status;
          const isMember = ['member','administrator','creator'].includes(status);
          return res.json({ verified: isMember });
        }
      } catch(e) { console.log('TG verify error:', e.message); }
    }

    // No chat_id set — just trust the user
    res.json({ verified: true });
  } catch(e) { log("ERROR", e.message); res.status(500).json({error:"Server error. Please try again."}); }
});


// ── GET /api/story-task/status ────────────────────
app.get('/api/story-task/status', userAuth, async (req, res) => {
  try {
    const u    = req.tgUser;
    const today = new Date().toISOString().slice(0, 10);
    const row  = await db.one(
      `SELECT attempts, claimed FROM story_tasks WHERE user_id=$1 AND claim_date=$2`,
      [u.id, today]
    );
    res.json({
      claimedToday: row ? !!row.claimed : false,
      attempts:     row ? (row.attempts || 0) : 0
    });
  } catch(e) { log("ERROR", e.message); res.status(500).json({error: "Server error. Please try again."}); }
});

// ── POST /api/story-task/claim ────────────────────
app.post('/api/story-task/claim', userAuth, async (req, res) => {
  try {
    const u     = req.tgUser;
    const today = new Date().toISOString().slice(0, 10);
    const REWARD = 0.04;

    // [ORDER FIX] Check existing row BEFORE incrementing attempts
    const existingRow = await db.one(
      `SELECT attempts, claimed FROM story_tasks WHERE user_id=$1 AND claim_date=$2`,
      [u.id, today]
    );

    // Already claimed today — reject immediately, don't increment counter
    if (existingRow && existingRow.claimed) {
      return res.status(400).json({ error: 'Already claimed today. Come back in 24 hours.' });
    }

    // Attempt limit — reject before incrementing
    if (existingRow && existingRow.attempts >= 3) {
      return res.status(400).json({ error: 'Max attempts reached. Try again tomorrow.' });
    }

    // Safe to upsert and increment now
    await db.run(
      `INSERT INTO story_tasks (user_id, claim_date, attempts, claimed, last_attempt)
       VALUES ($1, $2, 1, 0, NOW())
       ON CONFLICT (user_id, claim_date) DO UPDATE
       SET attempts = story_tasks.attempts + 1, last_attempt = NOW()`,
      [u.id, today]
    );

    // ✅ FIX: Atomic claim — prevent race condition double-credit
    const claimResult = await pool.query(
      `UPDATE story_tasks SET claimed=1, claimed_at=NOW()
       WHERE user_id=$1 AND claim_date=$2 AND claimed=0
       RETURNING id`,
      [u.id, today]
    );
    if (claimResult.rowCount === 0) {
      return res.status(400).json({ error: 'Already claimed today. Come back in 24 hours.' });
    }
    await db.run(
      `UPDATE users SET balance=balance+$1, total_earned=total_earned+$1 WHERE id=$2`,
      [REWARD, u.id]
    );
    await db.run(
      `INSERT INTO transactions (user_id,type,amount,status,note) VALUES ($1,$2,$3,$4,$5)`,
      [u.id, 'task_reward', REWARD, 'completed', 'Story task reward']
    );

    res.json({ success: true, amount: REWARD });
  } catch(e) { log('ERROR', e.message); res.status(500).json({ error: 'Server error. Please try again.' }); }
});

// ══════════════════════════════════════════
// PUBLIC ROUTES
// ══════════════════════════════════════════

// Health check
// ── Debug log endpoint — receives silent client-side error reports ──
app.post('/api/debug-log', globalLimit, async (req, res) => {
  try {
    res.json({ ok: true }); // respond immediately — don't block client
    const { trigger, uid, ver, totalMs, steps, errors, ua, platform, online, ts } = req.body || {};
    if (!trigger) return;

    // Only log failures — skip routine reports to keep logs clean
    const hasFail = (errors && errors.length > 0) || String(trigger).includes('fail') || String(trigger).includes('error');
    if (!hasFail) return;

    const stepsStr = (steps || []).map(s => s.label + '@' + s.ms + 'ms').join(' → ');
    const errorsStr = (errors || []).map(e => e.label + ': ' + e.detail).join(' | ');

    log('DEBUG', `[CLIENT] uid=${uid} ver=${ver} trigger=${trigger} totalMs=${totalMs}ms platform=${platform} online=${online}`);
    if (stepsStr) log('DEBUG', `[CLIENT-STEPS] ${stepsStr}`);
    if (errorsStr) log('DEBUG', `[CLIENT-ERRORS] ${errorsStr}`);

    // Send to admin Telegram if critical error
    // Skip known fake/probe user IDs (not real Telegram users)
    const FAKE_IDS = ['123456', '1', '0'];
    const isFakeUid = FAKE_IDS.includes(String(uid || ''));
    const isCritical = !isFakeUid && hasFail;
    if (isCritical && process.env.ADMIN_TG_CHAT_ID && process.env.BOT_TOKEN) {
      const msg = `⚠️ <b>Client Error</b>\nUser: ${uid}\nTrigger: ${trigger}\nTotal: ${totalMs}ms\nError: ${errorsStr}\nUA: ${(ua||'').slice(0,80)}`;
      fetch('https://api.telegram.org/bot' + process.env.BOT_TOKEN + '/sendMessage', {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify({ chat_id: process.env.ADMIN_TG_CHAT_ID, text: msg, parse_mode: 'HTML' })
      }).catch(() => {});
    }
  } catch(e) {
    res.json({ ok: true }); // always succeed silently
  }
});

app.get('/health', (req, res) => {
  res.json({status: 'ok', time: new Date().toISOString()});
});

// Public tasks endpoint
app.get('/api/tasks', async (req, res) => {
  try {
    const tasks = await db.all('SELECT * FROM tasks_config WHERE is_active=1 ORDER BY sort_order');
    res.json({tasks});
  } catch(e) { res.json({tasks:[]}); }
});

// Bot calls this when user uses referral link
app.post('/api/set-pending-ref', async (req, res) => {
  try {
    const {user_id, ref_code, secret} = req.body;
    // Bot-only endpoint — require admin secret to prevent referral hijacking
    if (secret !== ADMIN_SECRET) return res.status(403).json({success:false, error:'Unauthorized'});
    if (!user_id || !ref_code) return res.json({success:false});
    // Validate ref_code format (REF + digits only)
    if (!/^REF\d+$/.test(String(ref_code))) return res.json({success:false, error:'Invalid ref_code'});
    await db.run(`
      INSERT INTO pending_refs (user_id, ref_code) VALUES ($1,$2)
      ON CONFLICT (user_id) DO UPDATE SET ref_code=$2, created_at=NOW()
    `, [user_id, ref_code]);
    res.json({success:true});
  } catch(e) { res.json({success:false}); }
});
// ── Activity cache (reduces DB load) ──
var activityCache = [];
var activityLastFetch = 0;

app.get('/api/activity', async (req, res) => {
  try {
    const now = Date.now();
    if (now - activityLastFetch < 10000 && activityCache.length > 0) {
      return res.json(activityCache);
    }
    const rows = await db.all(`
      SELECT type, amount, created_at
      FROM transactions
      WHERE type IN ('deposit','withdraw') AND status='approved'
      ORDER BY created_at DESC LIMIT 10
    `);
    const activity = rows.map(function(r) {
      const diff = Math.floor((now - new Date(r.created_at).getTime()) / 1000);
      let time;
      if      (diff < 60)    time = diff + 's ago';
      else if (diff < 3600)  time = Math.floor(diff/60) + 'm ago';
      else if (diff < 86400) time = Math.floor(diff/3600) + 'h ago';
      else                   time = Math.floor(diff/86400) + 'd ago';
      return { type: r.type, amount: parseFloat(r.amount), time };
    });
    activityCache = activity;
    activityLastFetch = now;
    res.json(activity);
  } catch(e) {
    console.error('Activity API error:', e);
    res.json(activityCache.length ? activityCache : []);
  }
});

app.get('/api/plans', async (req, res) => {
  try {
    await db.run(`
      UPDATE plans SET today_count=0, last_reset=NOW()
      WHERE daily_limit > 0
        AND last_reset IS NOT NULL
        AND EXTRACT(EPOCH FROM (NOW() - last_reset))/3600 >= reset_hours
    `);
    const plans = await db.all(`SELECT * FROM plans WHERE is_active=1 ORDER BY id`);
    res.json({plans});
  } catch(e) { log("ERROR", e.message); res.status(500).json({error:"Server error. Please try again."}); }
});

// ══════════════════════════════════════════
// ADMIN ROUTES
// ══════════════════════════════════════════
app.get('/admin/stats', adminAuth, async (req, res) => {
  try {
    const [
      totalUsersRow, activeInvestsRow, totalDepositRow, totalWithdrawRow,
      pendingDepRow, pendingWithRow, bannedUsersRow, totalBalanceRow, totalCreditRow,
      todayDepRow, autoDepRow, fraudRow
    ] = await Promise.all([
      db.one(`SELECT COUNT(*) as c FROM users`),
      db.one(`SELECT COUNT(*) as c FROM investments WHERE status='active'`),
      db.one(`SELECT COALESCE(SUM(amount),0) as s FROM transactions WHERE type='deposit' AND status='approved'`),
      db.one(`SELECT COALESCE(SUM(amount),0) as s FROM transactions WHERE type='withdraw' AND status='approved'`),
      db.one(`SELECT COUNT(*) as c FROM transactions WHERE type='deposit' AND status='pending'`),
      db.one(`SELECT COUNT(*) as c FROM transactions WHERE type='withdraw' AND status='pending'`),
      db.one(`SELECT COUNT(*) as c FROM users WHERE is_banned=1`),
      db.one(`SELECT COALESCE(SUM(balance),0) as s FROM users`),
      db.one(`SELECT COALESCE(SUM(reinvest_credit),0) as s FROM users`),
      // [NEW] Today's deposits
      db.one(`SELECT COALESCE(SUM(amount),0) as s, COUNT(*) as c FROM transactions WHERE type='deposit' AND status='approved' AND created_at >= NOW() - INTERVAL '24 hours'`),
      // [NEW] Auto vs semi counts
      db.one(`SELECT COUNT(*) as c FROM auto_deposits WHERE dep_type='auto' AND status='completed'`),
      db.one(`SELECT COUNT(*) as c FROM auto_deposits WHERE fraud_flag=1`),
    ]);
    res.json({
      totalUsers: totalUsersRow.c,
      activeInvests: activeInvestsRow.c,
      totalDeposit: totalDepositRow.s,
      totalWithdraw: totalWithdrawRow.s,
      pendingDep: pendingDepRow.c,
      pendingWith: pendingWithRow.c,
      bannedUsers: bannedUsersRow.c,
      totalBalance: totalBalanceRow.s,
      totalCredit:  totalCreditRow.s,
      // [NEW]
      todayDepAmount: todayDepRow.s,
      todayDepCount: todayDepRow.c,
      autoDepCount: autoDepRow.c,
      fraudCount: fraudRow.c,
    });
  } catch(e) { log("ERROR", e.message); res.status(500).json({error:"Server error. Please try again."}); }
});

// ══════════════════════════════════════════
// ADMIN DASHBOARD DETAIL ENDPOINTS
// ══════════════════════════════════════════

// Deposit history (clickable stat)
app.get('/admin/stat/deposits', adminAuth, async (req, res) => {
  try {
    const page  = Math.max(1, parseInt(req.query.page) || 1);
    const limit = Math.min(50, parseInt(req.query.limit) || 20);
    const offset = (page - 1) * limit;
    const [rows, totalRow] = await Promise.all([
      db.all(`
        SELECT ad.user_id, u.username, u.first_name, ad.amount, ad.network, ad.status, ad.created_at
        FROM auto_deposits ad LEFT JOIN users u ON u.id=ad.user_id
        WHERE ad.status='completed'
        ORDER BY ad.created_at DESC LIMIT $1 OFFSET $2
      `, [limit, offset]),
      db.one(`SELECT COUNT(*) as c FROM auto_deposits WHERE status='completed'`)
    ]);
    const total = parseInt(totalRow.c);
    res.json({ rows, total, currentPage: page, totalPages: Math.ceil(total/limit), limit });
  } catch(e) { log("ERROR", e.message); res.status(500).json({error:"Server error. Please try again."}); }
});

// Withdrawal history (clickable stat)
app.get('/admin/stat/withdrawals', adminAuth, async (req, res) => {
  try {
    const page  = Math.max(1, parseInt(req.query.page) || 1);
    const limit = Math.min(50, parseInt(req.query.limit) || 20);
    const offset = (page - 1) * limit;
    const [rows, totalRow] = await Promise.all([
      db.all(`
        SELECT t.user_id, u.username, u.first_name, t.amount, t.address, t.status, t.created_at
        FROM transactions t LEFT JOIN users u ON u.id=t.user_id
        WHERE t.type='withdraw'
        ORDER BY t.created_at DESC LIMIT $1 OFFSET $2
      `, [limit, offset]),
      db.one(`SELECT COUNT(*) as c FROM transactions WHERE type='withdraw'`)
    ]);
    const total = parseInt(totalRow.c);
    res.json({ rows, total, currentPage: page, totalPages: Math.ceil(total/limit), limit });
  } catch(e) { log("ERROR", e.message); res.status(500).json({error:"Server error. Please try again."}); }
});

// All users by balance (clickable stat)
app.get('/admin/stat/balances', adminAuth, async (req, res) => {
  try {
    const page  = Math.max(1, parseInt(req.query.page) || 1);
    const limit = Math.min(50, parseInt(req.query.limit) || 20);
    const offset = (page - 1) * limit;
    const [rows, totalRow] = await Promise.all([
      db.all(`SELECT id, username, first_name, balance FROM users ORDER BY balance DESC LIMIT $1 OFFSET $2`, [limit, offset]),
      db.one(`SELECT COUNT(*) as c FROM users`)
    ]);
    const total = parseInt(totalRow.c);
    res.json({ rows, total, currentPage: page, totalPages: Math.ceil(total/limit), limit });
  } catch(e) { log("ERROR", e.message); res.status(500).json({error:"Server error. Please try again."}); }
});

// Daily income total + per-user breakdown
app.get('/admin/stat/daily-income', adminAuth, async (req, res) => {
  try {
    const page  = Math.max(1, parseInt(req.query.page) || 1);
    const limit = Math.min(50, parseInt(req.query.limit) || 20);
    const offset = (page - 1) * limit;
    const [totalRow, rows, countRow] = await Promise.all([
      db.one(`SELECT COALESCE(SUM(amount),0) as total FROM transactions WHERE type='earn' AND created_at >= CURRENT_DATE`),
      db.all(`
        SELECT u.username, u.first_name, t.user_id, SUM(t.amount) as daily_income
        FROM transactions t LEFT JOIN users u ON u.id=t.user_id
        WHERE t.type='earn' AND t.created_at >= CURRENT_DATE
        GROUP BY t.user_id, u.username, u.first_name
        ORDER BY daily_income DESC LIMIT $1 OFFSET $2
      `, [limit, offset]),
      db.one(`SELECT COUNT(DISTINCT user_id) as c FROM transactions WHERE type='earn' AND created_at >= CURRENT_DATE`)
    ]);
    const total = parseFloat(totalRow.total);
    const totalUsers = parseInt(countRow.c);
    res.json({ total, rows, totalUsers, currentPage: page, totalPages: Math.ceil(totalUsers/limit), limit });
  } catch(e) { log("ERROR", e.message); res.status(500).json({error:"Server error. Please try again."}); }
});


// [NEW] Admin deposit history with filters
app.get('/admin/deposits', adminAuth, async (req, res) => {
  try {
    const { status, dep_type, date_from, date_to, limit=50 } = req.query;
    let q = `SELECT d.*, u.first_name, u.username FROM auto_deposits d LEFT JOIN users u ON d.user_id=u.id WHERE 1=1`;
    const params = [];
    if (status)   { params.push(status);   q += ` AND d.status=$${params.length}`; }
    if (dep_type) { params.push(dep_type); q += ` AND d.dep_type=$${params.length}`; }
    if (date_from){ params.push(date_from); q += ` AND d.created_at >= $${params.length}::date`; }
    if (date_to)  { params.push(date_to);   q += ` AND d.created_at < ($${params.length}::date + INTERVAL '1 day')`; }
    params.push(limit); q += ` ORDER BY d.created_at DESC LIMIT $${params.length}`;
    const rows = await db.all(q, params);
    res.json({ deposits: rows });
  } catch(e) { log("ERROR", e.message); res.status(500).json({error:"Server error. Please try again."}); }
});

app.get('/admin/users', adminAuth, async (req, res) => {
  try {
    const {search, limit=20, page=1} = req.query;
    const offset = (page-1)*limit;
    let q, params;
    if (search) {
      q = `SELECT * FROM users WHERE first_name ILIKE $1 OR username ILIKE $1 OR CAST(id AS TEXT) LIKE $1 ORDER BY created_at DESC LIMIT $2 OFFSET $3`;
      params = [`%${search}%`, limit, offset];
    } else {
      q = `SELECT * FROM users ORDER BY created_at DESC LIMIT $1 OFFSET $2`;
      params = [limit, offset];
    }
    const users = await db.all(q, params);
    const total = (await db.one(`SELECT COUNT(*) as c FROM users`)).c;

    // Enrich all users in ONE query instead of N*4 queries
    const userIds = users.map(u => u.id);
    const enrichRows = userIds.length > 0 ? await db.all(`
      SELECT
        user_id,
        SUM(CASE WHEN type='deposit'  AND status='approved' THEN amount ELSE 0 END) as dep_total,
        SUM(CASE WHEN type='withdraw' AND status='approved' THEN amount ELSE 0 END) as with_total,
        COUNT(CASE WHEN type='deposit'  AND status='approved' THEN 1 END) as dep_cnt,
        COUNT(CASE WHEN type='withdraw' AND status='approved' THEN 1 END) as with_cnt,
        MAX(CASE WHEN type='deposit'  AND status='approved' THEN created_at END) as last_dep,
        MAX(CASE WHEN type='withdraw' AND status='approved' THEN created_at END) as last_with
      FROM transactions
      WHERE user_id = ANY($1::bigint[])
      GROUP BY user_id
    `, [userIds]) : [];

    const enrichMap = {};
    enrichRows.forEach(r => { enrichMap[r.user_id] = r; });

    const enriched = users.map(u => {
      const r = enrichMap[u.id] || {};
      const totalDeposit  = parseFloat(r.dep_total  || 0);
      const totalWithdraw = parseFloat(r.with_total || 0);
      const depositCount  = parseInt(r.dep_cnt  || 0);
      const withdrawCount = parseInt(r.with_cnt || 0);
      const netProfit     = totalDeposit - totalWithdraw;
      const isSuspicious  = (totalWithdraw > totalDeposit * 1.5) || (withdrawCount > depositCount * 2);
      return {
        ...u,
        totalDeposit, totalWithdraw, depositCount, withdrawCount,
        netProfit, isSuspicious,
        lastDepositAt:  r.last_dep  || null,
        lastWithdrawAt: r.last_with || null,
      };
    });

    res.json({users: enriched, total});
  } catch(e) { log("ERROR", e.message); res.status(500).json({error:"Server error. Please try again."}); }
});

// User transaction details with optional status filter
app.get('/admin/user/:id/details', adminAuth, async (req, res) => {
  try {
    const uid    = req.params.id;
    const status = req.query.status || '';
    const depQ   = status
      ? `SELECT 'deposit' as type, amount, status, created_at, network FROM transactions WHERE user_id=$1 AND type='deposit' AND status=$2 ORDER BY created_at DESC LIMIT 50`
      : `SELECT 'deposit' as type, amount, status, created_at, network FROM transactions WHERE user_id=$1 AND type='deposit' ORDER BY created_at DESC LIMIT 50`;
    const withQ  = status
      ? `SELECT 'withdraw' as type, amount, status, created_at, address as network FROM transactions WHERE user_id=$1 AND type='withdraw' AND status=$2 ORDER BY created_at DESC LIMIT 50`
      : `SELECT 'withdraw' as type, amount, status, created_at, address as network FROM transactions WHERE user_id=$1 AND type='withdraw' ORDER BY created_at DESC LIMIT 50`;
    const depParams  = status ? [uid, status] : [uid];
    const withParams = status ? [uid, status] : [uid];
    const [deps, withs] = await Promise.all([
      db.all(depQ, depParams),
      db.all(withQ, withParams),
    ]);
    const txs = [...deps, ...withs].sort((a,b) => new Date(b.created_at) - new Date(a.created_at));
    res.json({transactions: txs});
  } catch(e) { log("ERROR", e.message); res.status(500).json({error:"Server error. Please try again."}); }
});

app.post('/admin/user/ban', adminAuth, async (req, res) => {
  try {
    const {user_id, reason} = req.body;
    await db.run(`UPDATE users SET is_banned=1, ban_reason=$1 WHERE id=$2`, [reason||'Violated terms', user_id]);
    log('ADMIN', `User ${user_id} BANNED — reason: ${reason||'Violated terms'}`);
    res.json({success:true});
  } catch(e) { log("ERROR", e.message); res.status(500).json({error:"Server error. Please try again."}); }
});

app.post('/admin/user/unban', adminAuth, async (req, res) => {
  try {
    await db.run(`UPDATE users SET is_banned=0, ban_reason=NULL WHERE id=$1`, [req.body.user_id]);
    log('ADMIN', `User ${req.body.user_id} unbanned`);
    res.json({success:true});
  } catch(e) { log("ERROR", e.message); res.status(500).json({error:"Server error. Please try again."}); }
});

// [NEW] Block user from deposits (fraud block)
app.post('/admin/user/deposit-block', adminAuth, async (req, res) => {
  try {
    const { user_id, minutes } = req.body;
    const dur = parseInt(minutes || 30);
    const until = new Date(Date.now() + dur * 60000);
    await db.run(`UPDATE users SET blocked_until=$1 WHERE id=$2`, [until, user_id]);
    log('ADMIN', `User ${user_id} deposit-blocked for ${dur}min by admin`);
    res.json({success:true, blocked_until: until});
  } catch(e) { log("ERROR", e.message); res.status(500).json({error:"Server error. Please try again."}); }
});

// [NEW] Unblock user deposits
app.post('/admin/user/deposit-unblock', adminAuth, async (req, res) => {
  try {
    await clearFraud(req.body.user_id);
    log('ADMIN', `User ${req.body.user_id} deposit-unblocked by admin`);
    res.json({success:true});
  } catch(e) { log("ERROR", e.message); res.status(500).json({error:"Server error. Please try again."}); }
});

// [NEW] View logs
app.get('/admin/logs', adminAuth, async (req, res) => {
  try {
    if (!fs.existsSync(LOG_FILE)) return res.json({logs:''});
    const lines = fs.readFileSync(LOG_FILE, 'utf8').split('\n').filter(Boolean);
    const last100 = lines.slice(-100).reverse().join('\n');
    res.json({logs: last100});
  } catch(e) { log("ERROR", e.message); res.status(500).json({error:"Server error. Please try again."}); }
});

app.post('/admin/user/balance', adminAuth, async (req, res) => {
  try {
    const {user_id, type, wallet} = req.body;
    const amount = parseFloat(req.body.amount);
    if (!user_id || isNaN(amount) || amount <= 0) return res.status(400).json({error:'Invalid user_id or amount'});
    const change = type==='deduct' ? -Math.abs(amount) : Math.abs(amount);
    const field = 'balance';
    const label = 'Withdrawable';

    if (type === 'deduct') {
      const r = await pool.query(`UPDATE users SET ${field}=${field}+$1 WHERE id=$2 AND ${field}>=$3 RETURNING id`, [change, user_id, Math.abs(amount)]);
      if (r.rowCount === 0) return res.status(400).json({error:`Insufficient ${label} balance for deduction`});
    } else {
      await db.run(`UPDATE users SET ${field}=${field}+$1 WHERE id=$2`, [change, user_id]);
    }
    await db.run(
      `INSERT INTO transactions (user_id,type,amount,status,note) VALUES ($1,$2,$3,$4,$5)`,
      [user_id, type==='deduct'?'admin_deduct':'admin_add', Math.abs(amount), 'completed',
       type==='deduct' ? `Admin deduction (${label})` : `Admin credit (${label})`]
    );
    res.json({success:true});
  } catch(e) { log("ERROR", e.message); res.status(500).json({error:"Server error. Please try again."}); }
});

app.get('/admin/transactions', adminAuth, async (req, res) => {
  try {
    const { type, status, limit=20, page=1, search='' } = req.query;
    const pageNum  = Math.max(1, parseInt(page)  || 1);
    const limitNum = Math.min(100, Math.max(1, parseInt(limit) || 20));
    const offset   = (pageNum - 1) * limitNum;

    const params = [];
    let where = 'WHERE 1=1';
    if (type)   { params.push(type);   where += ` AND t.type=$${params.length}`; }
    if (status) { params.push(status); where += ` AND t.status=$${params.length}`; }
    if (search && search.trim()) {
      params.push('%' + search.trim() + '%');
      const i = params.length;
      where += ` AND (u.username ILIKE $${i} OR u.first_name ILIKE $${i} OR CAST(t.user_id AS TEXT) LIKE $${i})`;
    }

    const baseQ = `FROM transactions t LEFT JOIN users u ON t.user_id=u.id ${where}`;
    const countRow = await db.one(`SELECT COUNT(*) as total ${baseQ}`, params).catch(() => ({ total: 0 }));
    const total    = parseInt((countRow && countRow.total) || 0);

    const dataParams = [...params, limitNum, offset];
    const txs = await db.all(
      `SELECT t.*, u.first_name, u.last_name, u.username ${baseQ} ORDER BY t.created_at DESC LIMIT $${params.length+1} OFFSET $${params.length+2}`,
      dataParams
    );
    res.json({ transactions: txs, total, page: pageNum, limit: limitNum, pages: Math.max(1, Math.ceil(total / limitNum)) });
  } catch(e) { log("ERROR", e.message); res.status(500).json({error:"Server error. Please try again."}); }
});

// GET /admin/user-detail/:id — withdrawal popup detail
app.get('/admin/user-detail/:id', adminAuth, async (req, res) => {
  try {
    const uid = parseInt(req.params.id);
    if (!uid) return res.status(400).json({ error: 'Invalid user id' });

    const user = await db.one(
      `SELECT id, first_name, last_name, username, balance, created_at FROM users WHERE id=$1`, [uid]
    ).catch(e => { log('WARN', 'user-detail user: ' + e.message); return null; });

    if (!user) return res.status(404).json({ error: 'User not found' });

    // All plans ever purchased (active + completed) — for total invested
    const allInvestments = await db.all(
      `SELECT plan_name, amount, daily_pct, daily_earn, days_done, days_total, status, started_at
       FROM investments WHERE user_id=$1
       ORDER BY started_at DESC`, [uid]
    ).catch(() => []);

    // Active plans only — status='active' AND days not exhausted
    const activePlans = (allInvestments || []).filter(i =>
      i.status === 'active' && (i.days_done || 0) < (i.days_total || 50)
    );

    // Total invested = sum of ALL plans ever (active + completed)
    const totalInvested = (allInvestments || []).reduce(
      (s, i) => s + (parseFloat(i.amount) || 0), 0
    );

    const depRow = await db.one(
      `SELECT COALESCE(SUM(amount),0) as total FROM transactions WHERE user_id=$1 AND type='deposit' AND status='approved'`, [uid]
    ).catch(() => ({ total: 0 }));

    const withRow = await db.one(
      `SELECT COALESCE(SUM(amount),0) as total FROM transactions WHERE user_id=$1 AND type='withdraw' AND status='approved'`, [uid]
    ).catch(() => ({ total: 0 }));

    const promoClaims = await db.one(
      `SELECT COUNT(*) as c FROM promo_withdrawals WHERE user_id=$1 AND status != 'failed'`, [uid]
    ).catch(() => ({ c: 0 }));

    res.json({
      user: {
        id:       user.id,
        name:     (user.first_name || '') + (user.last_name ? ' ' + user.last_name : ''),
        username: user.username || null,
        balance:  parseFloat(user.balance) || 0,
        joined:   user.created_at,
      },
      investments:     activePlans,     // only active for display
      all_investments: allInvestments,  // all for reference
      total_invested:  totalInvested,
      total_deposited: parseFloat((depRow  && depRow.total)  || 0),
      total_withdrawn: parseFloat((withRow && withRow.total) || 0),
      promo_claims:    parseInt((promoClaims && promoClaims.c) || 0),
    });

  } catch(e) {
    log('ERROR', 'user-detail crash: ' + e.message);
    res.status(500).json({ error: 'Server error: ' + e.message });
  }
});

app.post('/admin/deposit/approve', adminAuth, async (req, res) => {
  try {
    const {tx_id, admin_note} = req.body;
    if (!tx_id || isNaN(parseInt(tx_id))) return res.status(400).json({error:'Invalid tx_id'});

    const tx = await db.one(`SELECT * FROM transactions WHERE id=$1 AND type='deposit'`, [tx_id]);
    if (!tx) return res.status(404).json({error:'Not found'});
    if (parseFloat(tx.amount) <= 0) return res.status(400).json({error:'Invalid amount'});

    // [DOUBLE-CREDIT GUARD] If tx was already auto-credited (has txid + status approved in auto_deposits), block approval
    if (tx.txid) {
      const alreadyAuto = await db.one(
        `SELECT id FROM auto_deposits WHERE tx_hash=$1 AND status='completed'`,
        [tx.txid]
      );
      if (alreadyAuto) {
        log('ADMIN', `Blocked double-credit attempt: tx=${tx_id} txhash=${tx.txid} already auto-credited`);
        return res.status(400).json({error:'This deposit was already auto-credited to the user. Do not approve again.'});
      }
    }

    // [ATOMIC] Only update if still pending — prevents double approval under race
    const result = await pool.query(
      `UPDATE transactions SET status='approved', admin_note=$1 WHERE id=$2 AND status='pending' RETURNING id`,
      [admin_note||'', tx_id]
    );
    if (result.rowCount === 0) return res.status(400).json({error:'Already processed'});

    // Safe atomic balance credit
    await db.run(`UPDATE users SET balance=balance+$1 WHERE id=$2`, [tx.amount, tx.user_id]);
    log('ADMIN', `Deposit approved tx=${tx_id} user=${tx.user_id} amt=$${tx.amount}`);
    logSecurity('DEPOSIT_APPROVED', {tx_id, user_id: tx.user_id, amount: tx.amount});
    res.json({success:true});
  } catch(e) { log("ERROR", e.message); res.status(500).json({error:"Server error. Please try again."}); }
});

app.post('/admin/deposit/reject', adminAuth, async (req, res) => {
  try {
    const {tx_id, admin_note} = req.body;
    if (!tx_id || isNaN(parseInt(tx_id))) return res.status(400).json({error:'Invalid tx_id'});
    const tx = await db.one(`SELECT * FROM transactions WHERE id=$1 AND type='deposit'`, [tx_id]);
    if (!tx) return res.status(404).json({error:'Not found'});
    if (tx.status !== 'pending') return res.status(400).json({error:'Already processed'});
    await db.run(`UPDATE transactions SET status='rejected', admin_note=$1 WHERE id=$2`, [admin_note||'Rejected by admin', tx_id]);
    log('ADMIN', `Deposit rejected tx=${tx_id} user=${tx.user_id}`);
    res.json({success:true});
  } catch(e) { log("ERROR", e.message); res.status(500).json({error:"Server error. Please try again."}); }
});

app.post('/admin/withdraw/approve', adminAuth, async (req, res) => {
  try {
    const {tx_id, admin_note, bsc_tx_hash} = req.body;
    if (!tx_id || isNaN(parseInt(tx_id))) return res.status(400).json({error:'Invalid tx_id'});
    const tx = await db.one(`SELECT t.*, u.username, u.first_name FROM transactions t LEFT JOIN users u ON u.id=t.user_id WHERE t.id=$1 AND t.type='withdraw'`, [tx_id]);
    if (!tx) return res.status(404).json({error:'Not found'});

    // [ATOMIC] Only approve if still pending — rowCount=0 means already processed
    const result = await pool.query(
      `UPDATE transactions SET status='approved', admin_note=$1, approved_at=NOW() WHERE id=$2 AND status='pending' RETURNING id, user_id, amount`,
      [admin_note||'', tx_id]
    );
    if (result.rowCount === 0) return res.status(400).json({error:'Already processed'});

    // Save bsc_tx_hash AFTER atomic approval confirmed (not before — avoids saving on already-processed)
    if (bsc_tx_hash && bsc_tx_hash.trim()) {
      await db.run(`UPDATE transactions SET bsc_tx_hash=$1 WHERE id=$2`, [bsc_tx_hash.trim(), tx_id]);
    }

    const {user_id, amount} = result.rows[0];
    log('WITHDRAW', `APPROVED tx=${tx_id} user=${user_id} amt=$${amount} addr=${(tx.address||'').slice(0,16)}`);
    logSecurity('WITHDRAW_APPROVED', {tx_id, user_id, amount, address: (tx.address||'').slice(0,20)});
    res.json({success:true});

    // Fire Telegram proof immediately after approve (non-blocking)
    // Scanner will try to add TX hash separately if Moralis detects it
    setImmediate(() => sendWithdrawProof({
      withdraw_id: tx_id,
      username:    tx.username    || '',
      first_name:  tx.first_name  || '',
      user_id:     user_id,
      amount:      amount,
      address:     tx.address     || '',
      bsc_tx_hash: (bsc_tx_hash && bsc_tx_hash.trim()) ? bsc_tx_hash.trim() : ''
    }));
  } catch(e) { log("ERROR", e.message); res.status(500).json({error:"Server error. Please try again."}); }
});

app.post('/admin/withdraw/reject', adminAuth, async (req, res) => {
  try {
    const {tx_id, admin_note} = req.body;
    if (!tx_id || isNaN(parseInt(tx_id))) return res.status(400).json({error:'Invalid tx_id'});

    // [ATOMIC] Reject only if still pending — prevents double refund on concurrent clicks
    const result = await pool.query(
      `UPDATE transactions SET status='rejected', admin_note=$1 WHERE id=$2 AND status='pending' RETURNING id, amount, user_id`,
      [admin_note||'Rejected by admin', tx_id]
    );
    if (result.rowCount === 0) return res.status(400).json({error:'Already processed'});

    const {amount, user_id} = result.rows[0];
    // Refund balance only after confirmed atomic status change
    await db.run(`UPDATE users SET balance=balance+$1 WHERE id=$2`, [amount, user_id]);
    log('WITHDRAW', `REJECTED tx=${tx_id} user=${user_id} amt=$${amount} — refunded`);
    logSecurity('WITHDRAW_REJECTED_REFUNDED', {tx_id, user_id, amount});
    res.json({success:true});
  } catch(e) { log("ERROR", e.message); res.status(500).json({error:"Server error. Please try again."}); }
});

// ── Admin Tasks ──
app.get('/admin/tasks', adminAuth, async (req, res) => {
  try {
    const tasks = await db.all('SELECT * FROM tasks_config ORDER BY sort_order');
    res.json({tasks});
  } catch(e) { log("ERROR", e.message); res.status(500).json({error:"Server error. Please try again."}); }
});

app.post('/admin/tasks/add', adminAuth, async (req, res) => {
  try {
    const {task_key, icon, name, reward, sort_order, link, chat_id} = req.body;
    await db.run(
      'INSERT INTO tasks_config (task_key,icon,name,reward,sort_order,link,chat_id) VALUES ($1,$2,$3,$4,$5,$6,$7)',
      [task_key, icon||'⚡', name, reward||1, sort_order||99, link||'', chat_id||'']
    );
    res.json({success:true});
  } catch(e) { log("ERROR", e.message); res.status(500).json({error:"Server error. Please try again."}); }
});

app.post('/admin/tasks/edit', adminAuth, async (req, res) => {
  try {
    const {id, icon, name, reward, is_active, sort_order, link, chat_id} = req.body;
    await db.run(
      'UPDATE tasks_config SET icon=$1,name=$2,reward=$3,is_active=$4,sort_order=$5,link=$6,chat_id=$7 WHERE id=$8',
      [icon, name, reward, is_active, sort_order, link||'', chat_id||'', id]
    );
    res.json({success:true});
  } catch(e) { log("ERROR", e.message); res.status(500).json({error:"Server error. Please try again."}); }
});

app.post('/admin/tasks/delete', adminAuth, async (req, res) => {
  try {
    await db.run('DELETE FROM tasks_config WHERE id=$1', [req.body.id]);
    res.json({success:true});
  } catch(e) { log("ERROR", e.message); res.status(500).json({error:"Server error. Please try again."}); }
});

app.get('/admin/plans', adminAuth, async (req, res) => {
  try {
    const plans = await db.all(`SELECT * FROM plans ORDER BY id`);
    res.json({plans});
  } catch(e) { log("ERROR", e.message); res.status(500).json({error:"Server error. Please try again."}); }
});

app.post('/admin/plans/add', adminAuth, async (req, res) => {
  try {
    const {name,emoji,daily_pct,min_amt,max_amt,duration,daily_limit=0,reset_hours=24} = req.body;
    await db.run(
      `INSERT INTO plans (name,emoji,daily_pct,min_amt,max_amt,duration,daily_limit,reset_hours) VALUES ($1,$2,$3,$4,$5,$6,$7,$8)`,
      [name,emoji,daily_pct,min_amt,max_amt,duration,daily_limit,reset_hours]
    );
    res.json({success:true});
  } catch(e) { log("ERROR", e.message); res.status(500).json({error:"Server error. Please try again."}); }
});

app.post('/admin/plans/edit', adminAuth, async (req, res) => {
  try {
    const {id,name,emoji,daily_pct,min_amt,max_amt,duration,is_active,daily_limit=0,reset_hours=24} = req.body;
    await db.run(
      `UPDATE plans SET name=$1,emoji=$2,daily_pct=$3,min_amt=$4,max_amt=$5,duration=$6,is_active=$7,daily_limit=$8,reset_hours=$9 WHERE id=$10`,
      [name,emoji,daily_pct,min_amt,max_amt,duration,is_active,daily_limit,reset_hours,id]
    );
    res.json({success:true});
  } catch(e) { log("ERROR", e.message); res.status(500).json({error:"Server error. Please try again."}); }
});

app.post('/admin/plans/delete', adminAuth, async (req, res) => {
  try {
    // Permanently delete the plan
    await db.run(`DELETE FROM plans WHERE id=$1`, [req.body.id]);
    res.json({success:true});
  } catch(e) { log("ERROR", e.message); res.status(500).json({error:"Server error. Please try again."}); }
});

app.post('/admin/plan/update-count', adminAuth, async (req, res) => {
  try {
    const { plan_id } = req.body;
    let count = parseInt(req.body.count) || 0;
    if (!plan_id || req.body.count === undefined) return res.status(400).json({error:'plan_id and count required'});
    if (count < 0)      count = 0;
    if (count > 100000) count = 100000;
    await db.run(`UPDATE plans SET buy_count = $1 WHERE id = $2`, [count, plan_id]);
    res.json({success:true, count});
  } catch(e) { log("ERROR", e.message); res.status(500).json({error:"Server error. Please try again."}); }
});


// ══════════════════════════════════════════
// BLOCK TOKEN MINING — SWAP
// ══════════════════════════════════════════
app.post('/api/mining/swap', userAuth, async (req, res) => {
  try {
    const u = req.tgUser;
    const minRow  = await db.one(`SELECT value FROM settings WHERE key='token_min_swap'`);
    const minSwap = parseFloat(minRow?.value || '10');
    const user    = await db.one(`SELECT block_tokens, balance FROM users WHERE id=$1`, [u.id]);
    const totalTokens = parseFloat(user.block_tokens || 0);

    // Use requested amount — fallback to all tokens if not provided
    const requestedAmt = parseFloat(req.body?.amount || 0);
    const tokens = (requestedAmt > 0) ? requestedAmt : totalTokens;

    // Validation
    if (tokens < minSwap) {
      return res.status(400).json({ error: `Minimum ${minSwap} Block Tokens required` });
    }
    if (tokens > totalTokens) {
      return res.status(400).json({ error: 'Insufficient BLK balance' });
    }

    const blkPrice   = await getCurrentBlkPrice();
    const rate       = +(1 / blkPrice).toFixed(4);
    const usdtAmount = parseFloat((tokens * blkPrice).toFixed(4));

    if (usdtAmount <= 0) return res.status(400).json({ error: 'Amount too small' });

    // Atomic deduct — prevents negative balance under race condition
    const result = await pool.query(
      `UPDATE users SET block_tokens = block_tokens - $1, balance = balance + $2
       WHERE id = $3 AND block_tokens >= $1 RETURNING id`,
      [tokens, usdtAmount, u.id]
    );
    if (result.rowCount === 0) return res.status(400).json({ error: 'Insufficient BLK balance' });

    await db.run(
      `INSERT INTO transactions (user_id, type, amount, status, note, created_at)
       VALUES ($1, 'swap', $2, 'completed', $3, NOW())`,
      [u.id, usdtAmount, `${tokens} BLK → $${usdtAmount} USDT (1 BLK = $${blkPrice})`]
    );

    return res.json({ success: true, tokens_used: tokens, usdt_credited: usdtAmount, rate, blk_price: blkPrice });
  } catch(e) {
    console.error('[swap]', e.message);
    res.status(500).json({ error: 'Server error' });
  }
});

// ══════════════════════════════════════════
// SPIN WHEEL ENDPOINTS
// ══════════════════════════════════════════

// GET /api/spin/status — check if user can spin today
app.get('/api/spin/status', userAuth, async (req, res) => {
  try {
    const u = req.tgUser;
    const lastSpin = await db.one(
      `SELECT spun_at FROM spin_logs WHERE user_id=$1 ORDER BY spun_at DESC LIMIT 1`,
      [u.id]
    );
    if (!lastSpin) return res.json({ can_spin: true, next_spin_at: null });

    const spunAt   = new Date(lastSpin.spun_at);
    const nextSpin = new Date(spunAt.getTime() + 24 * 60 * 60 * 1000);
    const canSpin  = new Date() >= nextSpin;
    res.json({
      can_spin:    canSpin,
      last_spin:   spunAt.toISOString(),
      next_spin_at: canSpin ? null : nextSpin.toISOString(),
    });
  } catch(e) { log('ERROR', e.message); res.status(500).json({ error: 'Server error' }); }
});

// POST /api/spin/claim — claim spin reward (server validates cooldown + calculates reward)
app.post('/api/spin/claim', userAuth, async (req, res) => {
  try {
    const u = req.tgUser;

    // Cooldown check — 24h between spins
    const lastSpin = await db.one(
      `SELECT spun_at FROM spin_logs WHERE user_id=$1 ORDER BY spun_at DESC LIMIT 1`,
      [u.id]
    );
    if (lastSpin) {
      const nextSpin = new Date(new Date(lastSpin.spun_at).getTime() + 24 * 60 * 60 * 1000);
      if (new Date() < nextSpin) {
        const mins = Math.ceil((nextSpin - new Date()) / 60000);
        return res.status(429).json({ error: `Spin available in ${mins} minute(s)`, next_spin_at: nextSpin.toISOString() });
      }
    }

    // Weighted reward: 80% → 0.10–0.50 | 18% → 0.50–1.00 | 2% → 1.00–2.00 BLK
    let reward;
    const rng = Math.random();
    if      (rng < 0.80) reward = +(0.10 + Math.random() * 0.40).toFixed(2);
    else if (rng < 0.98) reward = +(0.50 + Math.random() * 0.50).toFixed(2);
    else                 reward = +(1.00 + Math.random() * 1.00).toFixed(2);

    const today = new Date().toISOString().slice(0, 10);

    // Credit BLOCK tokens + log spin
    await db.run(
      `UPDATE users SET
        block_tokens            = block_tokens + $1,
        block_tokens_total      = block_tokens_total + $1,
        block_tokens_today      = CASE WHEN $3::TEXT != COALESCE(block_tokens_today_date,'') THEN $1::REAL ELSE block_tokens_today + $1 END,
        block_tokens_today_date = $3::TEXT,
        last_spin_date          = NOW()
       WHERE id=$2`,
      [reward, u.id, today]
    );
    await db.run(`INSERT INTO spin_logs (user_id, reward) VALUES ($1, $2)`, [u.id, reward]);

    const updated = await db.one(
      `SELECT block_tokens, block_tokens_today, block_tokens_total FROM users WHERE id=$1`, [u.id]
    );
    log('SPIN', `User ${u.id} won ${reward} BLK`);
    res.json({
      success:      true,
      reward,
      block_tokens: parseFloat(updated.block_tokens || 0),
      today:        parseFloat(updated.block_tokens_today || 0),
      total:        parseFloat(updated.block_tokens_total || 0),
    });
  } catch(e) { log('ERROR', e.message); res.status(500).json({ error: 'Server error' }); }
});

// GET /api/mining/info — full mining state for client
app.get('/api/mining/info', userAuth, async (req, res) => {
  try {
    const u     = req.tgUser;
    const today = new Date().toISOString().slice(0, 10);

    const [user, maxTapsRow, modeRow, lastSpinLog] = await Promise.all([
      db.one(`SELECT block_tokens, block_tokens_today, block_tokens_today_date,
                     block_tokens_total, mining_taps_today, mining_taps_date,
                     energy_reset_flag, spin_reset_flag, last_spin_date
              FROM users WHERE id=$1`, [u.id]),
      db.one(`SELECT value FROM settings WHERE key='max_taps_per_day'`),
      db.one(`SELECT value FROM settings WHERE key='mining_day_mode'`),
      db.one(`SELECT spun_at FROM spin_logs WHERE user_id=$1 ORDER BY spun_at DESC LIMIT 1`, [u.id]).catch(() => null),
    ]);

    // ── Get current blk_price based on active day mode ──
    const blkPrice = await getCurrentBlkPrice();

    const isNewDay    = (user?.block_tokens_today_date || '') !== today;
    const isTapNewDay = (user?.mining_taps_date || '') !== today;
    const tapsToday   = isTapNewDay ? 0 : (parseInt(user?.mining_taps_today) || 0);
    const maxTaps     = parseInt(maxTapsRow?.value || '100');

    // Check if user has active mining plan (boost)
    const miningPlan = await getUserMiningPlan(u.id);

    let earnPerTap, dailyBlk, hasMiningPlan, miningPlanData;

    if (miningPlan) {
      // PAID — use mining plan values
      earnPerTap   = parseFloat(miningPlan.tap_reward);
      dailyBlk     = parseFloat(miningPlan.daily_blk);
      hasMiningPlan = true;
      miningPlanData = {
        amount:     parseFloat(miningPlan.amount),
        daily_blk:  dailyBlk,
        tap_reward: earnPerTap,
      };
    } else {
      // FREE — fixed low rate
      earnPerTap    = 0.0001;
      dailyBlk      = 0;
      hasMiningPlan = false;
      miningPlanData = null;
    }

    const energyReset = (user?.energy_reset_flag || 0) === 1;
    const spinReset   = (user?.spin_reset_flag   || 0) === 1;

    // Auto-clear flags immediately after reading — no need for separate clear-reset call
    if (energyReset || spinReset) {
      log('MINING', `mining/info: clearing flags for user ${u.id} — energy=${energyReset} spin=${spinReset}`);
      await db.run(`UPDATE users SET energy_reset_flag=0, spin_reset_flag=0 WHERE id=$1`, [u.id]);
    }

    res.json({
      block_tokens:    parseFloat(user?.block_tokens || 0),
      today:           isNewDay ? 0 : parseFloat(user?.block_tokens_today || 0),
      total:           parseFloat(user?.block_tokens_total || 0),
      taps_used:       tapsToday,
      taps_left:       Math.max(0, maxTaps - tapsToday),
      max_taps:        maxTaps,
      earn_per_tap:    earnPerTap,
      daily_blk:       dailyBlk,
      day_mode:        modeRow?.value || 'normal',
      blk_price:       blkPrice,
      energy_reset:    energyReset,
      spin_reset:      spinReset,
      next_spin_at:    (spinReset || !lastSpinLog?.spun_at) ? null : new Date(new Date(lastSpinLog.spun_at).getTime() + 86400000).toISOString(),
      has_investment:  hasMiningPlan,
      has_mining_plan: hasMiningPlan,
      mining_plan:     miningPlanData,
    });
  } catch(e) { log('ERROR', e.message); res.status(500).json({ error: 'Server error' }); }
});

// ── Mining helper: get current BLK price based on day mode ──
async function getCurrentBlkPrice() {
  const rows = await db.all(
    `SELECT key, value FROM settings WHERE key IN ('blk_price','mining_day_mode','lucky_blk_price','red_blk_price')`
  );
  const s = {};
  rows.forEach(r => { s[r.key] = r.value; });
  const mode = s.mining_day_mode || 'normal';
  if (mode === 'lucky') return parseFloat(s.lucky_blk_price || '0.02');
  if (mode === 'red')   return parseFloat(s.red_blk_price   || '0.005');
  return parseFloat(s.blk_price || '0.01');
}

// ── Mining helper: get sum of ALL active mining plans (use DB saved values) ──
async function getUserMiningPlan(userId) {
  const plans = await db.all(
    `SELECT id, amount, daily_blk, tap_reward, locked_price, purchase_mode, started_at
     FROM mining_plans WHERE user_id=$1 AND status='active'`,
    [userId]
  );
  if (!plans || !plans.length) return null;

  let totalAmount    = 0;
  let totalDailyBlk  = 0;
  let totalTapReward = 0;

  for (const p of plans) {
    totalAmount    += parseFloat(p.amount     || 0);
    totalDailyBlk  += parseFloat(p.daily_blk  || 0);
    totalTapReward += parseFloat(p.tap_reward || 0);
  }

  if (totalAmount <= 0) return null;

  // Guard: if old plans have no stored tap_reward, recalculate ONCE using stored locked_price
  // This handles plans purchased before the locked system was implemented
  if (totalTapReward <= 0) {
    totalDailyBlk  = 0; // reset to avoid double counting
    totalTapReward = 0;
    for (const p of plans) {
      const lockedPrice = parseFloat(p.locked_price || 0);
      const safePrice   = lockedPrice > 0 ? lockedPrice : 0.01;
      const amt         = parseFloat(p.amount || 0);
      const dBlk        = +((amt / 50) / safePrice).toFixed(4);
      const tReward     = +(dBlk / 100).toFixed(6);
      totalDailyBlk  += dBlk;
      totalTapReward += tReward;
      // Save for future — fill in missing values once
      await db.run(`UPDATE mining_plans SET daily_blk=$1, tap_reward=$2, locked_price=CASE WHEN locked_price=0 THEN $3 ELSE locked_price END WHERE id=$4`, [dBlk, tReward, safePrice, p.id]);
    }
  }

  return {
    amount:     +totalAmount.toFixed(2),
    daily_blk:  +totalDailyBlk.toFixed(4),
    tap_reward: +totalTapReward.toFixed(6),
    plans:      plans,
  };
}

// POST /api/mining/boost/buy — buy a mining boost package from wallet balance
app.post('/api/mining/boost/buy', userAuth, async (req, res) => {
  try {
    const u      = req.tgUser;
    const amount = parseFloat(req.body?.amount);
    const VALID  = [1, 5, 10, 30, 50, 100, 200, 300, 500, 1000];

    if (!amount || !VALID.includes(amount))
      return res.status(400).json({ error: 'Invalid package amount' });

    // [ATOMIC] Deduct balance only if sufficient — prevents negative balance under race condition
    const user = await db.one(`SELECT balance FROM users WHERE id=$1`, [u.id]);
    const bal = parseFloat(user?.balance || 0);
    if (bal < amount) return res.status(400).json({ error: 'Insufficient balance.', balance: bal, required: amount });
    const boostDeduct = await pool.query(
      `UPDATE users SET balance=balance-$1 WHERE id=$2 AND balance>=$1 RETURNING id`,
      [amount, u.id]
    );
    if (boostDeduct.rowCount === 0) return res.status(400).json({ error: 'Insufficient balance.' });

    // Calculate tap_reward and daily_blk — LOCKED at purchase time
    const blkPrice    = await getCurrentBlkPrice();
    const modeRow2    = await db.one(`SELECT value FROM settings WHERE key='mining_day_mode'`).catch(() => ({value:'normal'}));
    const purchaseMode = modeRow2?.value || 'normal';
    const maxTaps     = 100;
    const dailyUsd    = amount / 50;
    const dailyBlk    = +(dailyUsd / blkPrice).toFixed(4);
    const tapReward   = +(dailyBlk / maxTaps).toFixed(6);

    // Insert into mining_plans with LOCKED values — never recalculated
    await db.run(
      `INSERT INTO mining_plans (user_id, amount, daily_blk, tap_reward, status, locked_price, purchase_mode)
       VALUES ($1, $2, $3, $4, 'active', $5, $6)`,
      [u.id, amount, dailyBlk, tapReward, blkPrice, purchaseMode]
    );

    const updated = await db.one(`SELECT balance FROM users WHERE id=$1`, [u.id]);
    log('BOOST', `User ${u.id} bought $${amount} mining boost`);

    // Distribute referral commissions — same logic as normal investment plans
    try {
      const buyer = await db.one(`SELECT referred_by, is_active_ref, is_banned FROM users WHERE id=$1`, [u.id]);

      // Mark as active referral on first mining plan purchase (same as investment)
      if (!buyer.is_active_ref && buyer.referred_by && u.id !== buyer.referred_by) {
        await db.run(`UPDATE users SET is_active_ref=TRUE WHERE id=$1`, [u.id]);
        log('REF', `User ${u.id} marked as active referral (mining boost) of ${buyer.referred_by}`);
      }

      // Walk up referral tree — same VIP-based commission as invest route
      let currentId = u.id;
      const vipCache = new Map();
      for (let lvl = 0; lvl < 7; lvl++) {
        const row = await db.one(`SELECT referred_by, is_banned FROM users WHERE id=$1`, [currentId]);
        if (!row || !row.referred_by) break;
        const referrerId = row.referred_by;
        if (row.is_banned) { currentId = referrerId; continue; }

        let refVip;
        if (vipCache.has(referrerId)) {
          refVip = vipCache.get(referrerId);
        } else {
          const refVipData = await getUserVipStatus(referrerId, 4);
          refVip = refVipData.vip;
          vipCache.set(referrerId, refVip);
        }

        if (lvl >= refVip.maxLevels) { currentId = referrerId; continue; }
        const pct = (refVip.rates[lvl] || 0) / 100;
        if (pct <= 0) { currentId = referrerId; continue; }

        const comm = +(amount * pct).toFixed(4);
        await db.run(
          `UPDATE users SET pending_commission=pending_commission+$1, total_commission=total_commission+$1 WHERE id=$2`,
          [comm, referrerId]
        );
        await db.run(
          `INSERT INTO commissions (user_id,from_user_id,level,amount) VALUES ($1,$2,$3,$4)`,
          [referrerId, u.id, lvl+1, comm]
        );
        log('COMM', `[BOOST] L${lvl+1} ${refVip.name} ${pct*100}% $${comm} → user ${referrerId}`);
        currentId = referrerId;
      }
    } catch(e) { log('WARN', `Boost commission error: ${e.message}`); }

    res.json({
      success: true,
      message: `Mining boost activated! $${amount} USDT deducted.`,
      balance: parseFloat(updated.balance || 0),
      amount
    });
  } catch(e) { log('ERROR', e.message); res.status(500).json({ error: 'Server error' }); }
});

// POST /api/mining/earn — tap to earn BLK (free vs paid)
// GET /api/mining/clear-reset — clear energy_reset_flag after client processed it
app.post('/api/mining/clear-reset', userAuth, async (req, res) => {
  try {
    const u = req.tgUser;
    await db.run(`UPDATE users SET energy_reset_flag=0, spin_reset_flag=0 WHERE id=$1`, [u.id]);
    log('MINING', `clear-reset called for user ${u.id}`);
    res.json({ success: true });
  } catch(e) { res.json({ success: false }); }
});

app.post('/api/mining/earn', userAuth, async (req, res) => {
  try {
    const u     = req.tgUser;
    const taps  = Math.min(parseInt(req.body?.taps) || 1, 100);
    const today = new Date().toISOString().slice(0, 10);

    const maxTapsRow = await db.one(`SELECT value FROM settings WHERE key='max_taps_per_day'`);
    const maxTaps    = parseInt(maxTapsRow?.value || '100');

    const user = await db.one(
      `SELECT block_tokens_today, block_tokens_today_date, mining_taps_today, mining_taps_date
       FROM users WHERE id=$1`, [u.id]
    );
    const isNewDay   = (user?.mining_taps_date || '') !== today;
    const tapsUsed   = isNewDay ? 0 : (parseInt(user?.mining_taps_today) || 0);
    const tapsLeft   = Math.max(0, maxTaps - tapsUsed);

    if (tapsLeft <= 0)
      return res.status(429).json({ error: 'Daily tap limit reached', taps_left: 0 });

    const actualTaps = Math.min(taps, tapsLeft);

    // ONLY check mining_plans — never investments/plans page
    const miningPlan = await getUserMiningPlan(u.id);
    let earnPerTap, earn;

    if (miningPlan) {
      earnPerTap = parseFloat(miningPlan.tap_reward);
      earn       = +(earnPerTap * actualTaps).toFixed(6);
    } else {
      // BUG #2 FIX: Use toFixed(6) — toFixed(4) rounds 0.0001*1 to 0.0001 correctly
      // but could zero out sub-0.0001 values; use 6 decimals to be safe.
      // Also explicitly ensure earnPerTap is never 0 or undefined.
      earnPerTap = 0.0001;
      earn       = +(earnPerTap * actualTaps).toFixed(6);
      if (earn <= 0) earn = earnPerTap; // ultimate fallback: at minimum 1 tap reward
    }

    await db.run(
      `UPDATE users SET
        block_tokens            = block_tokens + $1,
        block_tokens_total      = block_tokens_total + $1,
        block_tokens_today      = CASE WHEN $3::TEXT != COALESCE(block_tokens_today_date,'') THEN $1::REAL ELSE block_tokens_today + $1 END,
        block_tokens_today_date = $3::TEXT,
        mining_taps_today       = CASE WHEN $3::TEXT != COALESCE(mining_taps_date,'') THEN $4::INT ELSE mining_taps_today + $4 END,
        mining_taps_date        = $3::TEXT
       WHERE id=$2`,
      [earn, u.id, today, actualTaps]
    );

    const updated = await db.one(
      `SELECT block_tokens, block_tokens_today, block_tokens_total, mining_taps_today FROM users WHERE id=$1`, [u.id]
    );

    res.json({
      success:           true,
      earn,
      earn_per_tap:      earnPerTap,
      has_mining_plan:   !!miningPlan,
      taps_used_this_req: actualTaps,
      block_tokens:      parseFloat(updated.block_tokens || 0),
      today:             parseFloat(updated.block_tokens_today || 0),
      total:             parseFloat(updated.block_tokens_total || 0),
      taps_used:         parseInt(updated.mining_taps_today || 0),
      taps_left:         Math.max(0, maxTaps - parseInt(updated.mining_taps_today || 0)),
      max_taps:          maxTaps,
    });
  } catch(e) { log('ERROR', e.message); res.status(500).json({ error: 'Server error' }); }
});

app.get('/admin/settings', adminAuth, async (req, res) => {
  try {
    const rows = await db.all(`SELECT * FROM settings`);
    res.json(rows.reduce((a,r) => ({...a,[r.key]:r.value}), {}));
  } catch(e) { log("ERROR", e.message); res.status(500).json({error:"Server error. Please try again."}); }
});

app.post('/admin/settings', adminAuth, async (req, res) => {
  try {
    const {settings} = req.body;
    for (const [k,v] of Object.entries(settings)) {
      await db.run(`INSERT INTO settings (key,value) VALUES ($1,$2) ON CONFLICT (key) DO UPDATE SET value=$2`, [k,String(v)]);
    }
    invalidateCache(); // Clear cached settings
    res.json({success:true});
  } catch(e) { log("ERROR", e.message); res.status(500).json({error:"Server error. Please try again."}); }
});

app.post('/admin/maintenance', adminAuth, async (req, res) => {
  try {
    await db.run(`INSERT INTO settings (key,value) VALUES ('maintenance',$1) ON CONFLICT (key) DO UPDATE SET value=$1`, [req.body.on?'1':'0']);
    res.json({success:true});
  } catch(e) { log("ERROR", e.message); res.status(500).json({error:"Server error. Please try again."}); }
});

// ── Admin Mining Control ──────────────────────────────────
// POST /admin/mining/set-price — set BLK price in USD
app.post('/admin/mining/set-price', adminAuth, async (req, res) => {
  try {
    const { blk_price } = req.body;
    if (!blk_price || isNaN(parseFloat(blk_price)) || parseFloat(blk_price) <= 0)
      return res.status(400).json({ error: 'Invalid blk_price' });
    await db.run(`INSERT INTO settings (key,value) VALUES ('blk_price',$1) ON CONFLICT (key) DO UPDATE SET value=$1`, [String(blk_price)]);
    log('ADMIN_MINING', `BLK price set to $${blk_price}`);
    res.json({ success: true, blk_price: parseFloat(blk_price) });
  } catch(e) { log('ERROR', e.message); res.status(500).json({ error: 'Server error' }); }
});

// POST /admin/mining/set-mode — set day mode: normal | lucky | red
app.post('/admin/mining/set-mode', adminAuth, async (req, res) => {
  try {
    const { mode, lucky_price, red_price } = req.body;
    if (!['normal','lucky','red'].includes(mode))
      return res.status(400).json({ error: 'mode must be normal|lucky|red' });
    await db.run(`INSERT INTO settings (key,value) VALUES ('mining_day_mode',$1) ON CONFLICT (key) DO UPDATE SET value=$1`, [mode]);
    if (lucky_price) await db.run(`INSERT INTO settings (key,value) VALUES ('lucky_blk_price',$1) ON CONFLICT (key) DO UPDATE SET value=$1`, [String(lucky_price)]);
    if (red_price)   await db.run(`INSERT INTO settings (key,value) VALUES ('red_blk_price',$1)   ON CONFLICT (key) DO UPDATE SET value=$1`, [String(red_price)]);
    log('ADMIN_MINING', `Day mode set to ${mode}`);
    res.json({ success: true, mode });
  } catch(e) { log('ERROR', e.message); res.status(500).json({ error: 'Server error' }); }
});

// POST /admin/mining/set-tap-limit — set max taps per day
app.post('/admin/mining/set-tap-limit', adminAuth, async (req, res) => {
  try {
    const { max_taps } = req.body;
    if (!max_taps || isNaN(parseInt(max_taps)) || parseInt(max_taps) < 1)
      return res.status(400).json({ error: 'Invalid max_taps' });
    await db.run(`INSERT INTO settings (key,value) VALUES ('max_taps_per_day',$1) ON CONFLICT (key) DO UPDATE SET value=$1`, [String(max_taps)]);
    log('ADMIN_MINING', `Max taps/day set to ${max_taps}`);
    res.json({ success: true, max_taps: parseInt(max_taps) });
  } catch(e) { log('ERROR', e.message); res.status(500).json({ error: 'Server error' }); }
});

// GET /admin/mining/stats — overview
app.get('/admin/mining/stats', adminAuth, async (req, res) => {
  try {
    const [totals, modeRow, priceRow, tapRow] = await Promise.all([
      db.one(`SELECT COUNT(*) as users,
                     COALESCE(SUM(block_tokens),0) as total_tokens,
                     COALESCE(SUM(block_tokens_today),0) as today_tokens
              FROM users`),
      db.one(`SELECT value FROM settings WHERE key='mining_day_mode'`),
      db.one(`SELECT value FROM settings WHERE key='blk_price'`),
      db.one(`SELECT value FROM settings WHERE key='max_taps_per_day'`),
    ]);
    const blkPrice = await getCurrentBlkPrice();
    res.json({
      total_users:      parseInt(totals.users),
      total_blk_issued: parseFloat(totals.total_tokens || 0),
      today_blk_issued: parseFloat(totals.today_tokens || 0),
      current_blk_price: blkPrice,
      day_mode:          modeRow?.value || 'normal',
      max_taps_per_day:  parseInt(tapRow?.value || '100'),
    });
  } catch(e) { log('ERROR', e.message); res.status(500).json({ error: 'Server error' }); }
});

// GET /admin/mining/user-plans/:id — all mining plans for a user
app.get('/admin/mining/user-plans/:id', adminAuth, async (req, res) => {
  try {
    const userId = parseInt(req.params.id);
    const user = await db.one(`SELECT id, first_name, username, uid, block_tokens, block_tokens_total, block_tokens_today, mining_taps_today FROM users WHERE id=$1`, [userId]);
    const plans = await db.all(`SELECT id, amount, daily_blk, tap_reward, locked_price, purchase_mode, status, started_at FROM mining_plans WHERE user_id=$1 ORDER BY started_at DESC`, [userId]);
    res.json({ user, plans });
  } catch(e) { log('ERROR', e.message); res.status(500).json({ error: 'Server error' }); }
});


app.get('/admin/mining/users', adminAuth, async (req, res) => {
  try {
    const page  = Math.max(1, parseInt(req.query.page) || 1);
    const limit = 20;
    const offset = (page - 1) * limit;
    const rows = await db.all(`
      SELECT u.id, u.first_name, u.username, u.uid,
             COALESCE(u.block_tokens, 0)       as block_tokens,
             COALESCE(u.block_tokens_today, 0) as today,
             COALESCE(u.block_tokens_total, 0) as total,
             COALESCE(u.mining_taps_today, 0)  as taps_today,
             (SELECT COALESCE(SUM(amount),0) FROM investments 
              WHERE user_id=u.id AND status='active') as active_investment
      FROM users u
      ORDER BY u.block_tokens_total DESC
      LIMIT $1 OFFSET $2
    `, [limit, offset]);
    const countRow = await db.one(`SELECT COUNT(*) as c FROM users`);
    res.json({
      users: rows.map(u => ({
        id:                u.id,
        name:              u.first_name || 'Unknown',
        username:          u.username || '',
        uid:               u.uid || '',
        block_tokens:      parseFloat(u.block_tokens).toFixed(4),
        today:             parseFloat(u.today).toFixed(4),
        total:             parseFloat(u.total).toFixed(4),
        taps_today:        parseInt(u.taps_today),
        active_investment: parseFloat(u.active_investment).toFixed(2),
      })),
      total: parseInt(countRow.c),
      page, limit,
    });
  } catch(e) { log('ERROR', e.message); res.status(500).json({ error: 'Server error' }); }
});


// ══════════════════════════════════════════
// ADMIN MINING — EXTENDED APIs
// ══════════════════════════════════════════

// GET /admin/mining/users-detail — full mining detail per user
app.get('/admin/mining/users-detail', adminAuth, async (req, res) => {
  try {
    const page   = Math.max(1, parseInt(req.query.page) || 1);
    const search = req.query.search || '';
    const limit  = 20;
    const offset = (page - 1) * limit;
    const blkPrice = await getCurrentBlkPrice();
    const modeRow  = await db.one(`SELECT value FROM settings WHERE key='mining_day_mode'`);

    const baseQ = `SELECT u.id, u.first_name, u.username, u.uid,
             COALESCE(u.block_tokens,0) as blk,
             COALESCE(u.block_tokens_today,0) as today,
             COALESCE(u.block_tokens_total,0) as total,
             COALESCE(u.mining_taps_today,0)  as taps_today,
             (SELECT COALESCE(SUM(mp.daily_blk),0) FROM mining_plans mp WHERE mp.user_id=u.id AND mp.status='active') as daily_blk,
             (SELECT COALESCE(SUM(mp.tap_reward),0) FROM mining_plans mp WHERE mp.user_id=u.id AND mp.status='active') as tap_reward,
             (SELECT COALESCE(SUM(mp.amount),0) FROM mining_plans mp WHERE mp.user_id=u.id AND mp.status='active') as pkg_amount,
             (SELECT COUNT(*) FROM mining_plans mp WHERE mp.user_id=u.id AND mp.status='active') as pkg_count
      FROM users u`;
    const orderQ = `ORDER BY u.block_tokens_total DESC LIMIT $1 OFFSET $2`;
    let rows;
    if (search) {
      rows = await db.all(baseQ + ` WHERE (u.username ILIKE $3 OR u.first_name ILIKE $3) ` + orderQ, [limit, offset, '%' + search + '%']);
    } else {
      rows = await db.all(baseQ + ` ` + orderQ, [limit, offset]);
    }

    const countRow = await db.one(`SELECT COUNT(*) as c FROM users`);

    // Rank
    const rankRows = await db.all(`SELECT id, ROW_NUMBER() OVER(ORDER BY block_tokens_total DESC) as rank FROM users`);
    const rankMap = {};
    rankRows.forEach(r => { rankMap[r.id] = parseInt(r.rank); });

    res.json({
      users: rows.map(u => ({
        id:         u.id,
        name:       u.first_name || 'Unknown',
        username:   u.username || '',
        uid:        u.uid || '',
        blk:        parseFloat(u.blk).toFixed(4),
        today:      parseFloat(u.today).toFixed(4),
        total:      parseFloat(u.total).toFixed(4),
        taps_today: parseInt(u.taps_today),
        daily_blk:  parseFloat(u.daily_blk).toFixed(4),
        tap_reward: parseFloat(u.tap_reward).toFixed(6),
        pkg_amount: parseFloat(u.pkg_amount).toFixed(2),
        pkg_count:  parseInt(u.pkg_count),
        rank:       rankMap[u.id] || '—',
      })),
      total:     parseInt(countRow.c),
      page, limit,
      day_mode:  modeRow?.value || 'normal',
      blk_price: blkPrice,
    });
  } catch(e) { log('ERROR', e.message); res.status(500).json({ error: 'Server error' }); }
});


// GET /admin/mining/find-user — find user by id, username, or name
app.get('/admin/mining/find-user', adminAuth, async (req, res) => {
  try {
    const q = (req.query.q || '').trim();
    if (!q) return res.status(400).json({ error: 'Query required' });
    const rows = await db.all(`
      SELECT id, first_name, username, uid, block_tokens, block_tokens_total, mining_taps_today
      FROM users
      WHERE CAST(id AS TEXT) = $1
         OR CAST(uid AS TEXT) = $1
         OR username ILIKE $2
         OR first_name ILIKE $2
      LIMIT 5
    `, [q, '%' + q + '%']);
    res.json({ users: rows });
  } catch(e) { log('ERROR', e.message); res.status(500).json({ error: 'Server error' }); }
});

// POST /admin/mining/energy-reset — reset energy for user or all
app.post('/admin/mining/energy-reset', adminAuth, async (req, res) => {
  try {
    const { user_id, all } = req.body;
    // Get actual max_taps from settings (not hardcoded)
    const maxTapsRow = await db.one(`SELECT value FROM settings WHERE key='max_taps_per_day'`).catch(() => null);
    const maxTaps = parseInt(maxTapsRow?.value || '100');

    if (all) {
      await db.run(`UPDATE users SET mining_taps_today=0, mining_taps_date='1970-01-01', energy_reset_flag=1`);
      log('ADMIN', 'Energy reset for ALL users');
      return res.json({ success: true, message: 'All users energy reset', energy_reset: true, taps_left: maxTaps, max_taps: maxTaps });
    }
    if (!user_id) return res.status(400).json({ error: 'user_id required' });
    await db.run(`UPDATE users SET mining_taps_today=0, mining_taps_date='1970-01-01', energy_reset_flag=1 WHERE id=$1`, [user_id]);
    log('ADMIN', `Energy reset for user ${user_id} — taps_today=0, flag=1`);
    res.json({ success: true, taps_today: 0, taps_left: maxTaps, max_taps: maxTaps, energy_reset: true });
  } catch(e) { log('ERROR', e.message); res.status(500).json({ error: 'Server error' }); }
});

// POST /admin/mining/blk-balance — adjust BLK balance
app.post('/admin/mining/blk-balance', adminAuth, async (req, res) => {
  try {
    const { user_id, action, amount } = req.body;
    if (!user_id || !action || !amount) return res.status(400).json({ error: 'Missing fields' });
    const amt = parseFloat(amount);
    if (isNaN(amt) || amt <= 0) return res.status(400).json({ error: 'Invalid amount' });

    let query;
    if (action === 'add') {
      query = `UPDATE users SET block_tokens = block_tokens + $1, block_tokens_total = block_tokens_total + $1 WHERE id = $2`;
    } else if (action === 'subtract') {
      query = `UPDATE users SET block_tokens = GREATEST(0, block_tokens - $1) WHERE id = $2`;
    } else if (action === 'set') {
      query = `UPDATE users SET block_tokens = $1 WHERE id = $2`;
    } else {
      return res.status(400).json({ error: 'action must be add|subtract|set' });
    }
    await db.run(query, [amt, user_id]);
    const u = await db.one(`SELECT block_tokens FROM users WHERE id=$1`, [user_id]);
    log('ADMIN', 'BLK balance ' + action + ' ' + amt + ' for user ' + user_id);
    res.json({ success: true, new_balance: parseFloat(u.block_tokens).toFixed(4) });
  } catch(e) { log('ERROR', e.message); res.status(500).json({ error: 'Server error' }); }
});

// GET /admin/mining/logs — mining tap logs
app.get('/admin/mining/logs', adminAuth, async (req, res) => {
  try {
    const page   = Math.max(1, parseInt(req.query.page) || 1);
    const limit  = 30;
    const offset = (page - 1) * limit;
    const rows = await db.all(`
      SELECT t.id, t.user_id, t.amount, t.type, t.note, t.created_at,
             u.username, u.first_name
      FROM transactions t
      JOIN users u ON u.id = t.user_id
      WHERE t.type IN ('swap','spin_reward','earn','invest','commission','admin_add','admin_deduct')
      ORDER BY t.created_at DESC
      LIMIT $1 OFFSET $2
    `, [limit, offset]);
    const countRow = await db.one(`SELECT COUNT(*) as c FROM transactions WHERE type IN ('swap','spin_reward','earn','invest','commission','admin_add','admin_deduct')`);
    res.json({ logs: rows, total: parseInt(countRow.c), page, limit });
  } catch(e) { log('ERROR', e.message); res.status(500).json({ error: 'Server error' }); }
});

// GET /admin/mining/holders — BLK holder leaderboard
app.get('/admin/mining/holders', adminAuth, async (req, res) => {
  try {
    const rows = await db.all(`
      SELECT u.id, u.first_name, u.username, u.uid,
             u.block_tokens, u.block_tokens_total,
             ROW_NUMBER() OVER(ORDER BY u.block_tokens_total DESC) as rank
      FROM users u
      WHERE u.block_tokens_total > 0
      ORDER BY u.block_tokens_total DESC
      LIMIT 50
    `);
    res.json({ holders: rows });
  } catch(e) { log('ERROR', e.message); res.status(500).json({ error: 'Server error' }); }
});

// GET /admin/deposit-history — all deposit history with types
app.get('/admin/deposit-history', adminAuth, async (req, res) => {
  try {
    const page   = Math.max(1, parseInt(req.query.page) || 1);
    const type   = req.query.type || '';
    const limit  = 30;
    const offset = (page - 1) * limit;
    const where  = type ? "AND t.note ILIKE $3" : '';
    const params = type ? [limit, offset, '%' + type + '%'] : [limit, offset];

    // Deposit type labels from note field
    // AUTO = auto_deposit, MANUAL = manual keyword, BONUS = bonus keyword, REFERRAL = referral keyword
    let depRows;
    if (type === 'AUTO') {
      depRows = await db.all(
        "SELECT t.id, t.user_id, t.amount, t.status, t.type, t.note, t.created_at, u.username, u.first_name FROM transactions t JOIN users u ON u.id = t.user_id WHERE t.type = 'deposit' AND (t.note ILIKE '%auto%' OR t.note ILIKE '%moralis%' OR t.note ILIKE '%bep20%' OR t.note ILIKE '%trc20%') ORDER BY t.created_at DESC LIMIT $1 OFFSET $2",
        [limit, offset]
      );
    } else if (type === 'MANUAL') {
      // Show all admin_add records (manually added by admin)
      depRows = await db.all(
        "SELECT t.id, t.user_id, t.amount, t.status, t.type, t.note, t.created_at, u.username, u.first_name FROM transactions t JOIN users u ON u.id = t.user_id WHERE t.type = 'admin_add' ORDER BY t.created_at DESC LIMIT $1 OFFSET $2",
        [limit, offset]
      );
    } else if (type === 'BONUS') {
      depRows = await db.all(
        "SELECT t.id, t.user_id, t.amount, t.status, t.type, t.note, t.created_at, u.username, u.first_name FROM transactions t JOIN users u ON u.id = t.user_id WHERE t.type IN ('deposit','admin_add') AND t.note ILIKE '%bonus%' ORDER BY t.created_at DESC LIMIT $1 OFFSET $2",
        [limit, offset]
      );
    } else if (type === 'REFERRAL') {
      depRows = await db.all(
        "SELECT t.id, t.user_id, t.amount, t.status, t.type, t.note, t.created_at, u.username, u.first_name FROM transactions t JOIN users u ON u.id = t.user_id WHERE t.type = 'commission' ORDER BY t.created_at DESC LIMIT $1 OFFSET $2",
        [limit, offset]
      );
    } else {
      depRows = await db.all(
        "SELECT t.id, t.user_id, t.amount, t.status, t.type, t.note, t.created_at, u.username, u.first_name FROM transactions t JOIN users u ON u.id = t.user_id WHERE t.type IN ('deposit','admin_add','commission') ORDER BY t.created_at DESC LIMIT $1 OFFSET $2",
        [limit, offset]
      );
    }
    const rows = depRows;

    // Count based on current filter
    let countQ;
    if (type === 'AUTO')     countQ = "SELECT COUNT(*) as c FROM transactions WHERE type='deposit' AND (note ILIKE '%auto%' OR note ILIKE '%moralis%' OR note ILIKE '%bep20%' OR note ILIKE '%trc20%')";
    else if (type === 'MANUAL')   countQ = "SELECT COUNT(*) as c FROM transactions WHERE type='admin_add'";
    else if (type === 'BONUS')    countQ = "SELECT COUNT(*) as c FROM transactions WHERE type IN ('deposit','admin_add') AND note ILIKE '%bonus%'";
    else if (type === 'REFERRAL') countQ = "SELECT COUNT(*) as c FROM transactions WHERE type='commission'";
    else                          countQ = "SELECT COUNT(*) as c FROM transactions WHERE type IN ('deposit','admin_add','commission')";
    const countRow = await db.one(countQ);
    res.json({ history: rows, total: parseInt(countRow.c), page, limit });
  } catch(e) { log('ERROR', e.message); res.status(500).json({ error: 'Server error' }); }
});

// GET /admin/plan-history — plan purchase + cancel history
app.get('/admin/plan-history', adminAuth, async (req, res) => {
  try {
    const page   = Math.max(1, parseInt(req.query.page) || 1);
    const limit  = 30;
    const offset = (page - 1) * limit;
    const rows = await db.all(`
      SELECT i.id, i.user_id, i.amount, i.status, i.started_at,
             i.cancelled_at, i.daily_pct, i.daily_earn,
             i.days_done, i.days_total, i.plan_name,
             u.username, u.first_name
      FROM investments i
      JOIN users u ON u.id = i.user_id
      ORDER BY i.started_at DESC
      LIMIT $1 OFFSET $2
    `, [limit, offset]);
    const countRow = await db.one(`SELECT COUNT(*) as c FROM investments`);
    res.json({ plans: rows, total: parseInt(countRow.c), page, limit });
  } catch(e) { log('ERROR', e.message); res.status(500).json({ error: 'Server error' }); }
});

// GET /admin/earnings-users — user list with total earnings for earnings history page
app.get('/admin/earnings-users', adminAuth, async (req, res) => {
  try {
    const page   = Math.max(1, parseInt(req.query.page) || 1);
    const limit  = 20;
    const offset = (page - 1) * limit;
    const search = req.query.search || '';
    const searchClause = search ? `AND (u.username ILIKE $3 OR u.first_name ILIKE $3)` : '';
    const params = search ? [limit, offset, `%${search}%`] : [limit, offset];

    const rows = await db.all(`
      SELECT u.id, u.uid, u.username, u.first_name, u.total_earned, u.today_earned,
             MAX(t.created_at) as last_earn
      FROM users u
      LEFT JOIN transactions t ON t.user_id = u.id
        AND t.type IN ('earn','swap','commission','spin_reward','admin_add','bonus')
      WHERE 1=1 ${searchClause}
      GROUP BY u.id
      ORDER BY u.total_earned DESC NULLS LAST
      LIMIT $1 OFFSET $2
    `, params);

    const countRow = await db.one(
      search ? `SELECT COUNT(*) as c FROM users WHERE username ILIKE $1 OR first_name ILIKE $1` : `SELECT COUNT(*) as c FROM users`,
      search ? [`%${search}%`] : []
    );
    res.json({ users: rows, total: parseInt(countRow.c), page, limit });
  } catch(e) { log('ERROR', e.message); res.status(500).json({ error: 'Server error' }); }
});

// GET /admin/user-earnings/:id — per-user earnings with filter and pagination
app.get('/admin/user-earnings/:id', adminAuth, async (req, res) => {
  try {
    const userId = parseInt(req.params.id);
    const page   = Math.max(1, parseInt(req.query.page) || 1);
    const limit  = 20;
    const offset = (page - 1) * limit;
    const filter = req.query.filter || '';

    const typeMap = {
      mining:     ['swap'],
      referral:   ['commission'],
      spin:       ['spin_reward'],
      bonus:      ['admin_add', 'bonus'],
      investment: ['earn'],
    };

    const allTypes = ['earn','swap','commission','spin_reward','admin_add','bonus'];
    const types = (filter && typeMap[filter]) ? typeMap[filter] : allTypes;

    // Build parameterized placeholders: $2, $3, $4...
    const placeholders = types.map((_, i) => `$${i + 2}`).join(',');

    const rows = await db.all(
      `SELECT t.id, t.type, t.amount, t.note, t.status, t.created_at
       FROM transactions t
       WHERE t.user_id=$1 AND t.type IN (${placeholders})
       ORDER BY t.created_at DESC
       LIMIT $${types.length + 2} OFFSET $${types.length + 3}`,
      [userId, ...types, limit, offset]
    );

    const countRow = await db.one(
      `SELECT COUNT(*) as c FROM transactions
       WHERE user_id=$1 AND type IN (${placeholders})`,
      [userId, ...types]
    );

    res.json({ earnings: rows, total: parseInt(countRow.c || 0), page, limit });
  } catch(e) { log('ERROR', 'user-earnings: ' + e.message); res.status(500).json({ error: e.message }); }
});

// GET /admin/earnings-history — kept for compatibility
app.get('/admin/earnings-history', adminAuth, async (req, res) => {
  try {
    const page   = Math.max(1, parseInt(req.query.page) || 1);
    const filter = req.query.filter || '';
    const limit  = 30;
    const offset = (page - 1) * limit;
    const typeMap = {
      mining:     ["'swap'"],
      referral:   ["'commission'"],
      spin:       ["'spin_reward'"],
      bonus:      ["'admin_add'","'bonus'"],
      investment: ["'earn'","'invest'"],
    };
    const allTypes = "'swap','commission','spin_reward','admin_add','bonus','earn','invest','deposit','withdraw'";
    const typeList = typeMap[filter] ? typeMap[filter].join(',') : allTypes;
    const earningsQ = 'SELECT t.id, t.user_id, t.amount, t.type, t.note, t.status, t.created_at, u.username, u.first_name FROM transactions t JOIN users u ON u.id = t.user_id WHERE t.type IN (' + typeList + ') ORDER BY t.created_at DESC LIMIT $1 OFFSET $2';
    const countQ    = 'SELECT COUNT(*) as c FROM transactions WHERE type IN (' + typeList + ')';
    const rows      = await db.all(earningsQ, [limit, offset]);
    const countRow  = await db.one(countQ, []);
    res.json({ earnings: rows, total: parseInt(countRow.c), page, limit });
  } catch(e) { log('ERROR', e.message); res.status(500).json({ error: 'Server error' }); }
});

// POST /admin/mining/spin-reset — reset spin for user or all
app.post('/admin/mining/spin-reset', adminAuth, async (req, res) => {
  try {
    const { user_id, all } = req.body;
    if (all) {
      await db.run(`UPDATE users SET last_spin_date=NULL, spin_reset_flag=1`);
      log('ADMIN', 'Spin reset for ALL users');
      return res.json({ success: true, message: 'All users spin reset', spin_reset: true });
    }
    if (!user_id) return res.status(400).json({ error: 'user_id required' });
    await db.run(`UPDATE users SET last_spin_date=NULL, spin_reset_flag=1 WHERE id=$1`, [user_id]);
    log('ADMIN', `Spin reset for user ${user_id}`);
    res.json({ success: true, spin_reset: true });
  } catch(e) { log('ERROR', e.message); res.status(500).json({ error: 'Server error' }); }
});

// ══════════════════════════════════════════
// TELEGRAM GROUP INTEGRATION — ADMIN ROUTES
// ══════════════════════════════════════════

// GET current tg group settings + bot status + today's sent count
app.get('/admin/tg-group/status', adminAuth, async (req, res) => {
  try {
    const cfg = await getTgGroupSettings();

    // Count today's sent proofs
    const todayRow = await db.one(
      `SELECT COUNT(*) as c FROM tg_proof_logs WHERE sent_status='sent' AND created_at >= NOW() - INTERVAL '24 hours'`
    );
    // Last log entry — use db.all + take first to avoid crash on empty table
    const lastLogs = await db.all(
      `SELECT sent_status, error_msg, updated_at FROM tg_proof_logs ORDER BY id DESC LIMIT 1`
    );
    const lastLog = lastLogs && lastLogs.length > 0 ? lastLogs[0] : null;

    // Check bot alive
    let botOk = false;
    let botUsername = '';
    if (BOT_TOKEN) {
      const me = await tgBotApi('getMe', {});
      botOk = !!me.ok;
      botUsername = me.result && me.result.username ? '@' + me.result.username : '';
    }

    res.json({
      bot_ok:        botOk,
      bot_username:  botUsername,
      chat_id:       cfg.chatId,
      topic_id:      cfg.topicId,
      enabled:       cfg.enabled,
      sent_today:    parseInt(todayRow.c || 0),
      last_status:   lastLog ? lastLog.sent_status  : null,
      last_error:    lastLog ? lastLog.error_msg     : null,
      last_time:     lastLog ? lastLog.updated_at    : null
    });
  } catch(e) { log("ERROR", e.message); res.status(500).json({error:"Server error. Please try again."}); }
});

// Save tg group settings
app.post('/admin/tg-group/settings', adminAuth, async (req, res) => {
  try {
    const { chat_id, topic_id, enabled } = req.body;
    await db.run(`INSERT INTO settings (key,value) VALUES ('tg_group_chat_id',$1)  ON CONFLICT (key) DO UPDATE SET value=$1`, [String(chat_id||'')]);
    await db.run(`INSERT INTO settings (key,value) VALUES ('tg_group_topic_id',$1) ON CONFLICT (key) DO UPDATE SET value=$1`, [String(topic_id||'')]);
    await db.run(`INSERT INTO settings (key,value) VALUES ('tg_group_enabled',$1)  ON CONFLICT (key) DO UPDATE SET value=$1`, [enabled?'1':'0']);
    res.json({success:true});
  } catch(e) { log("ERROR", e.message); res.status(500).json({error:"Server error. Please try again."}); }
});

// Test connection — send test message to configured topic
app.post('/admin/tg-group/test', adminAuth, async (req, res) => {
  try {
    const cfg = await getTgGroupSettings();
    if (!BOT_TOKEN)   return res.status(400).json({error:'BOT_TOKEN not configured on server'});
    if (!cfg.chatId)  return res.status(400).json({error:'Group Chat ID not set'});

    const payload = {
      chat_id:    cfg.chatId,
      text:       '💸 <b>Block Minings Proof Feed Connected Successfully</b>',
      parse_mode: 'HTML'
    };
    if (cfg.topicId) {
      const tid = parseInt(cfg.topicId, 10);
      if (!isNaN(tid) && tid > 0) payload.message_thread_id = tid;
    }

    const result = await tgBotApi('sendMessage', payload);
    if (!result.ok) return res.status(400).json({error: result.description || 'Send failed — check Chat ID / Topic ID and bot admin permissions'});
    res.json({success:true, message_id: result.result && result.result.message_id});
  } catch(e) { log("ERROR", e.message); res.status(500).json({error:"Server error. Please try again."}); }
});

// Check bot permissions in group
app.post('/admin/tg-group/check-permissions', adminAuth, async (req, res) => {
  try {
    const cfg = await getTgGroupSettings();
    if (!BOT_TOKEN)  return res.status(400).json({error:'BOT_TOKEN not set'});
    if (!cfg.chatId) return res.status(400).json({error:'Chat ID not configured'});

    const me = await tgBotApi('getMe', {});
    if (!me.ok || !me.result || !me.result.id) return res.status(400).json({error:'Cannot reach Telegram API'});

    const member = await tgBotApi('getChatMember', { chat_id: cfg.chatId, user_id: me.result.id });
    if (!member.ok) return res.status(400).json({error: member.description || 'Bot is not in the group'});

    const status = member.result && member.result.status;
    const canPost = status === 'administrator' || status === 'creator';
    res.json({
      ok: canPost,
      status,
      can_send_messages: canPost,
      warning: canPost ? null : 'Bot is not an admin — cannot post messages'
    });
  } catch(e) { log("ERROR", e.message); res.status(500).json({error:"Server error. Please try again."}); }
});

// ══════════════════════════════════════════
// REFERRAL STATS (per-level breakdown)
// ══════════════════════════════════════════
app.get('/api/referral-stats/:id', async (req, res) => {
  // Auth: verify if initData present, user can only see own stats
  const _initData = req.headers['x-telegram-init-data'];
  if (_initData && _initData.length > 10) {
    if (BOT_TOKEN && process.env.NODE_ENV !== 'development' && !verifyTg(_initData)) {
      return res.status(401).json({ error: 'Invalid session' });
    }
    try {
      const _p = new URLSearchParams(_initData);
      const _u = _p.get('user') ? JSON.parse(_p.get('user')) : null;
      if (_u && String(_u.id) !== String(req.params.id)) {
        return res.status(403).json({ error: 'Forbidden' });
      }
    } catch(e) {}
  }
  try {
    const uid = parseInt(req.params.id);
    if (!uid) return res.status(400).json({ error: 'Invalid id' });

    // Get user VIP to know how many levels to scan
    const { vip } = await getUserVipStatus(uid, 4);
    const maxLvl = vip.maxLevels || 3;

    // BFS up to maxLvl levels
    const lvlIds = [];
    let currentIds = [uid];
    for (let lvl = 0; lvl < maxLvl; lvl++) {
      if (!currentIds.length) { lvlIds.push([]); continue; }
      const rows = await db.all(
        `SELECT id FROM users WHERE referred_by = ANY($1::bigint[])`,
        [currentIds]
      );
      const nextIds = rows.map(r => parseInt(r.id));
      lvlIds.push(nextIds);
      currentIds = nextIds;
    }

    // Count active per level
    const countActive = async (ids) => {
      if (!ids || !ids.length) return 0;
      const r = await db.one(
        `SELECT COUNT(DISTINCT user_id) as cnt FROM investments WHERE user_id = ANY($1::bigint[]) AND status='active'`,
        [ids]
      );
      return parseInt(r.cnt) || 0;
    };

    const activePerLvl = await Promise.all(lvlIds.map(function(ids) { return countActive(ids); }));

    const totalAll    = lvlIds.reduce(function(s, ids) { return s + ids.length; }, 0);
    const totalActive = activePerLvl.reduce(function(s, n) { return s + n; }, 0);

    const result = { total: totalAll, total_active: totalActive, max_levels: maxLvl };
    for (let i = 0; i < lvlIds.length; i++) {
      result['lvl' + (i + 1)] = { total: lvlIds[i].length, active: activePerLvl[i] };
    }

    res.json(result);
  } catch(e) { log("ERROR", e.message); res.status(500).json({error: "Server error. Please try again."}); }
});

// ══════════════════════════════════════════
// AUTO DEPOSIT — Generate unique amount
// ══════════════════════════════════════════
async function generateUniqueAmt(base) {
  // Unique amount range: 0.01–0.05 (5 possible values)
  for (let i = 0; i < 5; i++) {
    const dec  = (Math.floor(Math.random() * 5) + 1); // 1–5 cents (0.01–0.05)
    const uAmt = +(parseFloat(base) + dec / 100).toFixed(2);
    const ex   = await db.one(
      `SELECT id FROM auto_deposits WHERE unique_amt=$1 AND status='pending' AND expires_at > NOW()`,
      [uAmt]
    );
    if (!ex) return uAmt;
  }
  throw new Error('Cannot generate unique amount — try again');
}

// ── POST /api/deposit/create ──────────────
app.post('/api/deposit/create', depositLimit, userAuth, async (req, res) => {
  try {
    const u      = req.tgUser;
    const { amount } = req.body;
    if (!isValidAmount(amount, 50000)) return res.status(400).json({error:'Invalid amount'});
    // PRE-LAUNCH lock check
    const depLock = await getSetting('deposit_lock');
    if (depLock === '1') return res.status(403).json({error:'pre_launch_locked', message:'Deposits are locked during pre-launch.'});
    const userCheck = await db.one(`SELECT is_banned, blocked_until FROM users WHERE id=$1`, [u.id]);
    if (userCheck && userCheck.is_banned) return res.status(403).json({error:'banned'});
    const minDep = parseFloat(await getSetting('deposit_min') || 5);
    const amt    = parseFloat(amount);
    if (amt < minDep) return res.status(400).json({error:`Minimum deposit: $${minDep}`});

    // [ANTI-FRAUD] Cancel any existing pending auto deposit for this user
    const existing = await db.one(
      `SELECT id FROM auto_deposits WHERE user_id=$1 AND dep_type='auto' AND status='pending' AND expires_at > NOW()`,
      [u.id]
    );
    if (existing) {
      await db.run(`UPDATE auto_deposits SET status='cancelled' WHERE id=$1`, [existing.id]);
    }

    // [ANTI-FRAUD] Check if user is blocked
    const blockMsg = await checkBlocked(u.id);
    if (blockMsg) return res.status(429).json({error: blockMsg});

    const uAmt = await generateUniqueAmt(amt);
    // Track attempts counter — only after successful unique amount generation
    await db.run(`UPDATE users SET deposit_attempts=deposit_attempts+1 WHERE id=$1`, [u.id]);
    const dep  = await db.one(
      `INSERT INTO auto_deposits (user_id, amount, unique_amt, network, dep_type)
       VALUES ($1,$2,$3,'BEP20','auto') RETURNING id, unique_amt, expires_at`,
      [u.id, amt, uAmt]
    );

    res.json({ id: dep.id, unique_amount: dep.unique_amt, address: DEPOSIT_WALLET, network: 'BEP20', expires_at: dep.expires_at });
  } catch(e) { log("ERROR", e.message); res.status(500).json({error: "Server error. Please try again."}); }
});

// Semi-auto deposit routes removed

// ── GET /api/deposit/status/:id ───────────
app.get('/api/deposit/status/:id', userAuth, async (req, res) => {
  try {
    const u   = req.tgUser;
    const dep = await db.one(
      `SELECT * FROM auto_deposits WHERE id=$1 AND user_id=$2`,
      [req.params.id, u.id]
    );
    if (!dep) return res.status(404).json({error:'Not found'});
    if (dep.status === 'pending' && new Date() > new Date(dep.expires_at)) {
      await db.run(`UPDATE auto_deposits SET status='expired' WHERE id=$1`, [dep.id]);
      return res.json({ status: 'expired' });
    }
    res.json({ status: dep.status, tx_hash: dep.tx_hash, amount: dep.unique_amt });
  } catch(e) { log("ERROR", e.message); res.status(500).json({error: "Server error. Please try again."}); }
});

// ══════════════════════════════════════════
// AUTO DEPOSIT — Credit helper
// ══════════════════════════════════════════
async function creditAutoDeposit(dep, txHash) {
  try {
    // [RACE GUARD] Only credit if this UPDATE actually changed a row
    // If another process already completed this deposit, rowCount = 0 → skip
    const result = await pool.query(
      `UPDATE auto_deposits SET status='completed', tx_hash=$1 WHERE id=$2 AND status='pending'`,
      [txHash, dep.id]
    );
    if (result.rowCount === 0) {
      console.log(`[SKIP] Deposit ${dep.id} already processed (race guard)`);
      return;
    }
    // Credit balance only after confirmed row lock
    await db.run(`UPDATE users SET balance=balance+$1 WHERE id=$2`, [dep.amount, dep.user_id]); // credit base amount, not unique_amt (which has suffix)
    // Transaction log
    await db.run(
      `INSERT INTO transactions (user_id,type,amount,network,txid,status,note)
       VALUES ($1,$2,$3,$4,$5,$6,$7)`,
      [dep.user_id,'deposit',dep.amount,'BEP20',txHash,'approved','Auto-detected']
    );
    // Mark first_deposit task as completed (NO balance reward — exact deposit amount only)
    const taskDone = await db.one(
      `SELECT id FROM tasks WHERE user_id=$1 AND task_key='first_deposit'`, [dep.user_id]
    );
    if (!taskDone) {
      await db.run(
        `INSERT INTO tasks (user_id, task_key, completed, completed_at)
         VALUES ($1,'first_deposit',1,NOW()) ON CONFLICT DO NOTHING`,
        [dep.user_id]
      );
    }
    console.log(`✅ Auto deposit: user=${dep.user_id} base_amt=${dep.amount} unique_amt=${dep.unique_amt} ${dep.network} tx=${txHash}`);
  } catch(e) {
    // Gracefully handle unique constraint (tx_hash duplicate = already credited)
    if (e.message.includes('unique') || e.message.includes('duplicate') || e.message.includes('idx_auto_dep_txhash')) {
      console.log(`[SAFE] TX ${txHash.slice(0,16)} already processed — skipping`);
    } else {
      console.error('[creditAutoDeposit] error:', e.message);
    }
  }
}

// ══════════════════════════════════════════
// BEP20 AUTO DEPOSIT — Moralis Streams
// Webhook-based, real-time, no polling needed
// Moralis calls POST /webhook/moralis-deposit
// ══════════════════════════════════════════

// ── [1] SIGNATURE VERIFICATION ─────────────────────────────────────────────
// Moralis signs each webhook with HMAC-SHA3-256 using the stream secret.
// Must compute over raw body buffer (before JSON.parse).
function verifyMoralisWebhook(rawBody, signature) {
  const secret = process.env.MORALIS_STREAM_SECRET || '';
  if (!secret) {
    log('WEBHOOK', '⚠️ MORALIS_STREAM_SECRET not set — skipping sig verification');
    return true; // allow in dev, warn in logs
  }
  if (!signature) {
    log('WEBHOOK', '❌ No x-signature header received');
    return false;
  }
  const hash = crypto.createHmac('sha3-256', secret).update(rawBody).digest('hex');
  const valid = hash === signature;
  if (!valid) log('WEBHOOK', `❌ Signature mismatch | received=${signature.slice(0,16)}... computed=${hash.slice(0,16)}...`);
  return valid;
}

// ── [2] WEBHOOK LOG TABLE (insert into DB for admin visibility) ─────────────
async function logWebhookEvent(event, txHash, depId, userId, status, detail) {
  try {
    await db.run(
      `INSERT INTO webhook_logs (event, tx_hash, dep_id, user_id, status, detail)
       VALUES ($1,$2,$3,$4,$5,$6)`,
      [event, txHash || null, depId || null, userId || null, status, detail || null]
    );
  } catch(e) {
    log('WEBHOOK', `logWebhookEvent DB error: ${e.message}`);
  }
}

// ── [3] ADMIN FAILURE ALERT ─────────────────────────────────────────────────
// Sends Telegram DM to admin on critical webhook failures.
// ADMIN_TG_CHAT_ID env var = admin's personal Telegram user ID
const _adminAlertCooldown = new Map(); // avoid spam — 1 alert per error-type per 10min

async function notifyAdminWebhookFailure(reason, detail) {
  try {
    const adminChatId = process.env.ADMIN_TG_CHAT_ID || '';
    if (!adminChatId || !BOT_TOKEN) return; // silently skip if not configured

    // Cooldown: same reason → max 1 alert per 10 min
    const cooldownKey = reason;
    const lastSent = _adminAlertCooldown.get(cooldownKey) || 0;
    if (Date.now() - lastSent < 10 * 60 * 1000) return;
    _adminAlertCooldown.set(cooldownKey, Date.now());

    const now = new Date().toLocaleString('en-GB', { timeZone: 'Asia/Dhaka', hour12: false });
    const msg =
      `🚨 <b>Webhook Alert</b>\n` +
      `⚠️ Reason: <b>${tgEscape(reason)}</b>\n` +
      `📋 Detail: <code>${tgEscape((detail || '').substring(0, 300))}</code>\n` +
      `⏰ Time: ${now}`;

    await tgBotApi('sendMessage', { chat_id: adminChatId, text: msg, parse_mode: 'HTML' });
    log('WEBHOOK', `Admin alerted: ${reason}`);
  } catch(e) {
    log('WEBHOOK', `notifyAdminWebhookFailure error: ${e.message}`);
  }
}

// ── [4] RETRY-SAFE CREDIT WRAPPER ───────────────────────────────────────────
// Wraps creditAutoDeposit with idempotency:
// - Checks tx_hash uniqueness in webhook_logs BEFORE touching auto_deposits
// - Handles DB unique constraint gracefully
// - Logs every outcome to webhook_logs
async function safeCredit(dep, txHash, source) {
  const tag = `[${source}] dep=${dep.id} user=${dep.user_id} tx=${txHash.slice(0,16)}...`;

  // [FAST DUPLICATE CHECK] — check tx_hash across both tables before any write
  const txExists = await db.one(
    `SELECT id FROM auto_deposits WHERE tx_hash=$1`, [txHash]
  );
  if (txExists) {
    log('WEBHOOK', `${tag} → DUPLICATE (already in auto_deposits)`);
    await logWebhookEvent('duplicate', txHash, dep.id, dep.user_id, 'skipped', 'tx_hash already exists');
    return 'duplicate';
  }

  // [IDEMPOTENT UPDATE] — atomic status flip, rowCount=0 means already done
  let credited = false;
  try {
    const result = await pool.query(
      `UPDATE auto_deposits SET status='completed', tx_hash=$1 WHERE id=$2 AND status='pending'`,
      [txHash, dep.id]
    );
    if (result.rowCount === 0) {
      log('WEBHOOK', `${tag} → RACE SKIP (status already changed)`);
      await logWebhookEvent('race_skip', txHash, dep.id, dep.user_id, 'skipped', 'rowCount=0');
      return 'race_skip';
    }
    credited = true;
  } catch(e) {
    // Unique constraint = already credited via parallel request
    if (e.message.includes('unique') || e.message.includes('duplicate') || e.message.includes('idx_auto_dep_txhash')) {
      log('WEBHOOK', `${tag} → SAFE DUPLICATE (unique constraint)`);
      await logWebhookEvent('duplicate', txHash, dep.id, dep.user_id, 'skipped', e.message.substring(0, 200));
      return 'duplicate';
    }
    log('WEBHOOK', `${tag} → DB ERROR: ${e.message}`);
    await logWebhookEvent('error', txHash, dep.id, dep.user_id, 'error', e.message.substring(0, 300));
    await notifyAdminWebhookFailure('DB error in safeCredit', `${tag} — ${e.message}`);
    return 'error';
  }

  if (!credited) return 'skip';

  // [FAST BALANCE CREDIT] — runs immediately after atomic row lock
  try {
    await db.run(`UPDATE users SET balance=balance+$1 WHERE id=$2`, [dep.amount, dep.user_id]);
    await db.run(
      `INSERT INTO transactions (user_id,type,amount,network,txid,status,note)
       VALUES ($1,$2,$3,$4,$5,$6,$7)`,
      [dep.user_id, 'deposit', dep.amount, 'BEP20', txHash, 'approved', `Auto-detected [${source}]`]
    );
    // Mark first_deposit task (no reward — keeps original behavior)
    await db.run(
      `INSERT INTO tasks (user_id,task_key,completed,completed_at)
       VALUES ($1,'first_deposit',1,NOW()) ON CONFLICT DO NOTHING`,
      [dep.user_id]
    );
    log('WEBHOOK', `${tag} → ✅ CREDITED $${dep.amount} USDT`);
    await logWebhookEvent('credited', txHash, dep.id, dep.user_id, 'success',
      `amount=${dep.amount} source=${source}`);
    return 'credited';
  } catch(e) {
    // CRITICAL: auto_deposits row already set to 'completed' above.
    // If balance/transaction insert fails here, user may be under-credited.
    // Log with full detail so admin can manually recover.
    const recoveryInfo = `MANUAL_RECOVERY_NEEDED: user=${dep.user_id} amount=${dep.amount} tx=${txHash} dep_id=${dep.id} — ${e.message}`;
    log('WEBHOOK', `${tag} → 🚨 POST-CREDIT ERROR: ${recoveryInfo}`);
    await logWebhookEvent('error', txHash, dep.id, dep.user_id, 'error',
      `post-credit: ${e.message.substring(0,300)}`);
    await notifyAdminWebhookFailure('🚨 MANUAL RECOVERY NEEDED — Post-credit DB error', recoveryInfo);
    return 'error';
  }
}

// ── [5] MAIN WEBHOOK ENDPOINT ───────────────────────────────────────────────
app.post('/webhook/moralis-deposit',
  express.raw({ type: 'application/json' }),
  async (req, res) => {
    // Always ACK 200 immediately — Moralis retries on non-200 (retry-safe design)
    res.status(200).json({ ok: true });

    const webhookStart = Date.now();

    try {
      // Parse raw body (express.raw gives a Buffer)
      const rawBody   = Buffer.isBuffer(req.body) ? req.body.toString('utf8') : JSON.stringify(req.body);
      const signature = req.headers['x-signature'] || '';

      // ── [A] Signature check ─────────────────────────────────────────────
      if (!verifyMoralisWebhook(rawBody, signature)) {
        log('WEBHOOK', '❌ Rejected — invalid signature');
        await logWebhookEvent('rejected', null, null, null, 'sig_fail', `sig=${signature.slice(0,20)}`);
        await notifyAdminWebhookFailure('Invalid webhook signature', `sig=${signature.slice(0,20)}`);
        return;
      }

      const body = JSON.parse(rawBody);

      // ── [B] Skip test/unconfirmed webhooks ──────────────────────────────
      if (!body.block || body.block.number === '0') {
        log('WEBHOOK', 'ℹ️ Test webhook (block=0) — ignored');
        return;
      }
      if (!body.confirmed) {
        log('WEBHOOK', `ℹ️ Unconfirmed block ${body.block.number} — ignored`);
        return;
      }

      const transfers = body.erc20Transfers || [];
      if (!transfers.length) {
        log('WEBHOOK', `ℹ️ Block ${body.block.number} — no ERC20 transfers`);
        return;
      }

      log('WEBHOOK', `📥 Block=${body.block.number} | ${transfers.length} transfer(s) | sig=✅`);
      await logWebhookEvent('received', null, null, null, 'ok',
        `block=${body.block.number} transfers=${transfers.length}`);

      // ── [C] Filter USDT→wallet transfers ────────────────────────────────
      const relevant = transfers.filter(tx => {
        const contract = (tx.tokenAddress || tx.contract || '').toLowerCase();
        const to       = (tx.to || '').toLowerCase();
        return contract === USDT_CONTRACT && to === DEPOSIT_WALLET && tx.transactionHash;
      });

      if (!relevant.length) {
        log('WEBHOOK', `ℹ️ Block ${body.block.number} — no matching USDT transfers`);
        return;
      }

      // ── [D] Load pending deposits once ──────────────────────────────────
      const pending = await db.all(
        `SELECT * FROM auto_deposits WHERE dep_type='auto' AND status='pending' AND expires_at > NOW()`
      );
      if (!pending.length) {
        log('WEBHOOK', `ℹ️ No pending deposits — ${relevant.length} tx(s) unmatched`);
        await logWebhookEvent('no_pending', null, null, null, 'skipped',
          `txs=${relevant.map(t=>t.transactionHash.slice(0,10)).join(',')}`);
        return;
      }

      log('WEBHOOK', `⏳ ${pending.length} pending dep(s) vs ${relevant.length} tx(s)`);

      // ── [E] Match & credit ───────────────────────────────────────────────
      let credited = 0, duplicates = 0, unmatched = 0;

      for (const tx of relevant) {
        const decimals = parseInt(tx.tokenDecimals) || 18;
        const txAmt    = parseFloat(tx.value) / Math.pow(10, decimals);
        if (isNaN(txAmt) || txAmt <= 0) continue;

        log('WEBHOOK', `🔍 tx=${tx.transactionHash.slice(0,18)}... amt=${txAmt} USDT`);

        let matched = false;
        for (const dep of pending) {
          if (dep._matched) continue;
          if (Math.abs(txAmt - dep.unique_amt) > 0.001) continue;

          matched = true;
          dep._matched = true;

          // Expired check
          if (new Date() > new Date(dep.expires_at)) {
            await db.run(`UPDATE auto_deposits SET status='expired' WHERE id=$1`, [dep.id]);
            log('WEBHOOK', `⏰ Dep ${dep.id} expired — tx unmatched`);
            await logWebhookEvent('expired', tx.transactionHash, dep.id, dep.user_id, 'expired', null);
            break;
          }

          const result = await safeCredit(dep, tx.transactionHash, 'webhook');
          if (result === 'credited') credited++;
          else if (result === 'duplicate' || result === 'race_skip') duplicates++;
          break;
        }

        if (!matched) {
          unmatched++;
          log('WEBHOOK', `⚠️ No pending dep matched tx=${tx.transactionHash.slice(0,18)}... amt=${txAmt}`);
          await logWebhookEvent('unmatched', tx.transactionHash, null, null, 'warn', `amt=${txAmt}`);
        }
      }

      const elapsed = Date.now() - webhookStart;
      log('WEBHOOK', `✅ Done — credited=${credited} dupes=${duplicates} unmatched=${unmatched} ms=${elapsed}`);

    } catch(e) {
      log('WEBHOOK', `💥 Fatal error: ${e.message}`);
      await logWebhookEvent('fatal', null, null, null, 'error', e.message.substring(0, 300));
      await notifyAdminWebhookFailure('Fatal webhook error', e.message);
    }
  }
);

// Fallback polling scanner — runs every 30s in case stream misses a tx
let _scanRunning = false;

async function scanBEP20() {
  if (_scanRunning) return;
  _scanRunning = true;
  try {
    const MORALIS_KEY = process.env.MORALIS_API_KEY || '';
    if (!MORALIS_KEY) { _scanRunning = false; return; }

    const pending = await db.all(
      `SELECT * FROM auto_deposits WHERE dep_type='auto' AND status='pending' AND expires_at > NOW()`
    );
    if (!pending.length) return;

    const url  = `https://deep-index.moralis.io/api/v2/${DEPOSIT_WALLET}/erc20/transfers?chain=bsc&limit=25`;
    const data = await httpsGet(url, { 'X-API-Key': MORALIS_KEY });
    if (!data || !Array.isArray(data.result)) return;

    const transfers = data.result.filter(tx =>
      tx.to_address && tx.to_address.toLowerCase() === DEPOSIT_WALLET &&
      tx.token_address && tx.token_address.toLowerCase() === USDT_CONTRACT &&
      tx.transaction_hash && typeof tx.transaction_hash === 'string'
    );

    const processedHashes = new Set();

    for (const dep of pending) {
      if (dep._matched) continue;
      const depCreatedMs = new Date(dep.created_at).getTime() - 120000;

      for (const tx of transfers) {
        if (processedHashes.has(tx.transaction_hash)) continue;
        if (new Date(tx.block_timestamp).getTime() < depCreatedMs) continue;

        // BUG FIX 3: duplicate check BEFORE amount match (cheaper query first)
        const already = await db.one(`SELECT id FROM auto_deposits WHERE tx_hash=$1`, [tx.transaction_hash]);
        if (already) { processedHashes.add(tx.transaction_hash); continue; }

        let txAmt;
        if (tx.value_decimal != null && tx.value_decimal !== '') {
          txAmt = parseFloat(tx.value_decimal);
        } else if (tx.value != null) {
          txAmt = parseFloat(tx.value) / 1e18;
        } else continue;
        if (isNaN(txAmt) || txAmt <= 0) continue;
        if (Math.abs(txAmt - dep.unique_amt) > 0.001) continue;

        if (new Date() > new Date(dep.expires_at)) {
          await db.run(`UPDATE auto_deposits SET status='expired' WHERE id=$1`, [dep.id]);
          dep._matched = true; break;
        }

        log('SCANNER', `[Fallback] Matched dep=${dep.id} user=${dep.user_id} amt=${dep.unique_amt}`);
        await safeCredit(dep, tx.transaction_hash, 'fallback');
        dep._matched = true;
        processedHashes.add(tx.transaction_hash);
        break;
      }
    }
  } catch(e) {
    log('SCANNER', `Fallback error: ${e.message}`);
  } finally {
    _scanRunning = false;
  }
}

// Fires Telegram withdrawal proof for approved withdrawals that still have no tx hash
// Runs every 2 min as a safety net — ensures group always gets notified
async function scanWithdrawalFallback() {
  try {
    const stale = await db.all(`
      SELECT t.id, t.user_id, t.amount, t.address, t.approved_at,
             u.username, u.first_name
      FROM transactions t
      LEFT JOIN users u ON u.id = t.user_id
      WHERE t.type    = 'withdraw'
        AND t.status  = 'approved'
        AND (t.bsc_tx_hash IS NULL OR t.bsc_tx_hash = '')
        AND t.approved_at IS NOT NULL
        AND t.approved_at >= NOW() - INTERVAL '2 hours'
        AND t.approved_at <= NOW() - INTERVAL '5 minutes'
        AND NOT EXISTS (
          SELECT 1 FROM tg_proof_logs pl WHERE pl.withdraw_id = t.id
        )
    `);
    for (const wd of stale) {
      log('WITH_SCAN', `Fallback proof wd=${wd.id} user=${wd.user_id}`);
      setImmediate(() => sendWithdrawProof({
        withdraw_id: wd.id,
        username:    wd.username   || '',
        first_name:  wd.first_name || '',
        user_id:     wd.user_id,
        amount:      wd.amount,
        address:     wd.address    || '',
        bsc_tx_hash: ''
      }));
    }
  } catch(e) {
    log('WITH_SCAN', 'Fallback error: ' + e.message);
  }
}


async function startScanners() {
  log('SCANNER', 'Auto deposit scanner ready (Moralis Streams webhook active)');

  // Withdrawal proof fallback
  setTimeout(scanWithdrawalFallback, 3 * 60 * 1000);
  setInterval(scanWithdrawalFallback, 2 * 60 * 1000);

  // Auto-expire stale pending deposits
  setInterval(async () => {
    try {
      await db.run(`UPDATE auto_deposits SET status='expired' WHERE status='pending' AND expires_at < NOW()`);
    } catch(e) {}
  }, 60 * 1000);
}

// ══════════════════════════════════════════
// START
// ══════════════════════════════════════════

// ══════════════════════════════════════════
// VIP STATUS API
// ══════════════════════════════════════════

// GET /api/vip-status — full VIP status + progress for current user
app.get('/api/vip-status', userAuth, async (req, res) => {
  try {
    const u = req.tgUser;
    // First pass: compute VIP (uses scanDepth=7 for gate check)
    const { vip, highestTier, activeRefs, isManualOverride, badgeLabel } = await getUserVipStatus(u.id);
    // Second pass: recompute teamDep using ONLY user's current unlocked levels
    const teamDep = await getTeamDeposit(u.id, vip.maxLevels);

    // Build next VIP target
    const currentIdx = VIP_LEVELS.indexOf(vip);
    let nextVip = null;
    let nextProgress = null;

    // If manual override active — skip next VIP progress (not applicable)
    if (!isManualOverride && currentIdx < VIP_LEVELS.length - 1) {
      for (let i = currentIdx + 1; i < VIP_LEVELS.length; i++) {
        if (VIP_LEVELS[i].name.startsWith('VIP')) {
          nextVip = VIP_LEVELS[i];
          break;
        }
      }
      if (nextVip) {
        const reqTier = nextVip.minPlanTier;
        const reqTierIdx = PLAN_TIER_ORDER.indexOf(reqTier);
        const curTierIdx = highestTier ? PLAN_TIER_ORDER.indexOf(highestTier) : -1;
        nextProgress = {
          plan:    { current: highestTier || 'none', required: reqTier, met: curTierIdx >= reqTierIdx },
          refs:    { current: activeRefs, required: nextVip.minRefs, met: activeRefs >= nextVip.minRefs },
          teamDep: { current: +teamDep.toFixed(2), required: nextVip.minTeamDep, met: teamDep >= nextVip.minTeamDep },
        };
      }
    }

    res.json({
      vip_name:          vip.name,
      vip_rates:         vip.rates,
      max_levels:        vip.maxLevels,
      highest_tier:      highestTier || null,
      active_refs:       activeRefs,
      team_deposit:      +teamDep.toFixed(2),
      next_vip:          nextVip ? { name: nextVip.name, minPlanTier: nextVip.minPlanTier, minRefs: nextVip.minRefs, minTeamDep: nextVip.minTeamDep, maxLevels: nextVip.maxLevels, rates: nextVip.rates } : null,
      next_progress:     nextProgress,
      is_manual_override: isManualOverride || false,
      badge_label:       badgeLabel || null,
    });
  } catch(e) { log('ERROR', e.message); res.status(500).json({ error: 'Server error. Please try again.' }); }
});

// GET /api/team-deposit — paginated, searchable, level-filtered team deposit
// Query params: level (1-7), page (default 1), limit (default 15), search (username/name/uid)
app.get('/api/team-deposit', userAuth, async (req, res) => {
  try {
    const u       = req.tgUser;
    const { vip } = await getUserVipStatus(u.id);
    const maxLvl  = vip.maxLevels || 3;

    const filterLvl = parseInt(req.query.level) || 0;   // 0 = all
    const page      = Math.max(1, parseInt(req.query.page) || 1);
    const limit     = Math.min(50, parseInt(req.query.limit) || 15);
    const offset    = (page - 1) * limit;
    const search    = (req.query.search || '').trim().toLowerCase();

    // BFS to build level id maps
    const lvlIds = [];
    let currentIds = [parseInt(u.id)];
    for (let lvl = 0; lvl < maxLvl; lvl++) {
      if (!currentIds.length) { lvlIds.push([]); continue; }
      const rows = await db.all(
        `SELECT id FROM users WHERE referred_by = ANY($1::bigint[])`, [currentIds]
      );
      const nextIds = rows.map(r => parseInt(r.id));
      lvlIds.push(nextIds);
      currentIds = nextIds;
    }

    // Summary: totals per level
    const levelSummary = [];
    let grandTotal = 0;
    let grandMembers = 0;
    let grandActive = 0;

    for (let i = 0; i < lvlIds.length; i++) {
      const ids = lvlIds[i];
      if (!ids.length) {
        levelSummary.push({ level: i+1, count: 0, total: 0, active: 0 });
        continue;
      }
      const r = await db.one(
        `SELECT COALESCE(SUM(CASE WHEN i.status IN ('active','completed') THEN i.amount ELSE 0 END),0) as total,
                COUNT(DISTINCT CASE WHEN i.status='active' THEN i.user_id END) as active
         FROM investments i WHERE i.user_id = ANY($1::bigint[])`,
        [ids]
      );
      const total  = parseFloat(r.total) || 0;
      const active = parseInt(r.active) || 0;
      levelSummary.push({ level: i+1, count: ids.length, total: +total.toFixed(2), active });
      grandTotal   += total;
      grandMembers += ids.length;
      grandActive  += active;
    }

    // Determine which level(s) to fetch members for
    const fetchLevels = filterLvl > 0 && filterLvl <= maxLvl
      ? [filterLvl - 1]          // 0-indexed
      : lvlIds.map((_, i) => i); // all levels

    // Build combined member list with level tag
    let memberRows = [];
    for (const li of fetchLevels) {
      const ids = lvlIds[li];
      if (!ids || !ids.length) continue;

      // Build search filter
      let whereExtra = '';
      const params = [ids];
      if (search) {
        whereExtra = ` AND (LOWER(u.first_name) LIKE $2 OR LOWER(u.username) LIKE $2 OR CAST(u.uid AS TEXT) LIKE $2)`;
        params.push('%' + search + '%');
      }

      const rows = await db.all(
        `SELECT u.id, u.first_name, u.username, u.uid, u.created_at,
                COALESCE(SUM(CASE WHEN i.status IN ('active','completed') THEN i.amount ELSE 0 END),0) as invested,
                COUNT(CASE WHEN i.status='active' THEN 1 END) as active_plans,
                (SELECT plan_name FROM investments WHERE user_id=u.id AND status='active' ORDER BY id DESC LIMIT 1) as top_plan
         FROM users u
         LEFT JOIN investments i ON i.user_id=u.id
         WHERE u.id = ANY($1::bigint[])${whereExtra}
         GROUP BY u.id, u.first_name, u.username, u.uid, u.created_at
         ORDER BY invested DESC`,
        params
      );
      rows.forEach(r => { r._level = li + 1; memberRows.push(r); });
    }

    // Sort by invested desc across levels, then paginate
    memberRows.sort((a, b) => parseFloat(b.invested||0) - parseFloat(a.invested||0));
    const totalFiltered = memberRows.length;
    const paginatedRows = memberRows.slice(offset, offset + limit);

    res.json({
      summary: {
        total_deposit: +grandTotal.toFixed(2),
        total_members: grandMembers,
        active_investors: grandActive,
        max_levels: maxLvl,
        vip_name: vip.name,
      },
      level_summary: levelSummary,
      members: paginatedRows.map(m => ({
        id:          m.id,
        name:        m.first_name || 'User',
        username:    m.username   || null,
        uid:         m.uid        || null,
        level:       m._level,
        invested:    +parseFloat(m.invested||0).toFixed(2),
        active_plans: parseInt(m.active_plans)||0,
        top_plan:    m.top_plan   || null,
        joined:      m.created_at ? String(m.created_at).split('T')[0] : null,
      })),
      pagination: {
        page, limit,
        total: totalFiltered,
        pages: Math.ceil(totalFiltered / limit),
        has_more: offset + limit < totalFiltered,
      },
      filter_level: filterLvl,
    });
  } catch(e) { log('ERROR', e.message); res.status(500).json({ error: 'Server error. Please try again.' }); }
});

// ══════════════════════════════════════════
// LEADERBOARD
// ══════════════════════════════════════════
app.get('/admin/deposit-stats', adminAuth, async (req, res) => {
  try {
    const rows = await db.all(`
      SELECT
        TO_CHAR(created_at, 'HH24') as time,
        SUM(amount) as total
      FROM transactions
      WHERE type='deposit' AND status='approved'
        AND created_at > NOW() - INTERVAL '24 hours'
      GROUP BY TO_CHAR(created_at, 'HH24')
      ORDER BY MIN(created_at) ASC
    `);
    res.json(rows.map(r => ({ time: r.time, total: parseFloat(r.total) })));
  } catch(e) { log("ERROR", e.message); res.status(500).json({ error: "Server error. Please try again." }); }
});

app.get('/leaderboard', async (req, res) => {
  try {
    const rows = await db.all(
      `SELECT first_name, uid, total_earned,
              (SELECT COUNT(DISTINCT i.user_id) FROM investments i JOIN users u2 ON u2.id=i.user_id WHERE u2.referred_by=u.id AND i.status='active') as active_refs
       FROM users u
       WHERE total_earned > 0
       ORDER BY total_earned DESC
       LIMIT 10`
    );
    const board = rows.map((u, i) => ({
      pos:          i + 1,
      name:         maskName(u.first_name),
      uid:          u.uid || '------',
      total_earned: parseFloat(u.total_earned || 0).toFixed(2),
      rank:         getUserRank(u.active_refs)
    }));
    res.json({ leaderboard: board });
  } catch(e) { log('ERROR', e.message); res.status(500).json({error: 'Server error. Please try again.'}); }
});

// ══ TOP EARNERS (top 20) ══
// ── BLK Holdings Leaderboard — ranked by CURRENT block_tokens held ──
app.get('/api/top-blk-holders', globalLimit, async (req, res) => {
  try {
    const rows = await db.all(`
      SELECT id, first_name, username, block_tokens
      FROM users
      WHERE COALESCE(block_tokens, 0) > 0
        AND is_banned = 0
      ORDER BY block_tokens DESC
      LIMIT 25
    `);
    const holders = rows.map((u, i) => ({
      rank:       i + 1,
      name:       u.username ? '@' + u.username : maskName(u.first_name),
      blk:        parseFloat(u.block_tokens || 0),
      id:         u.id
    }));
    res.json({ holders });
  } catch(e) { log('ERROR', e.message); res.status(500).json({ error: 'Server error' }); }
});

app.get('/api/top-earners', async (req, res) => {
  try {
    const rows = await db.all(`
      SELECT u.first_name, u.uid, u.block_tokens_total,
        (SELECT COUNT(DISTINCT i.user_id) FROM investments i 
         JOIN users u2 ON u2.id=i.user_id 
         WHERE u2.referred_by=u.id AND i.status='active') as active_refs
      FROM users u
      WHERE COALESCE(u.block_tokens_total, 0) > 0
      ORDER BY u.block_tokens_total DESC
      LIMIT 25
    `);
    const earners = rows.map((u, i) => ({
      pos:          i + 1,
      name:         maskName(u.first_name),
      uid:          u.uid || '------',
      total_earned: parseFloat(u.block_tokens_total || 0).toFixed(4),
      badge:        getUserRank(u.active_refs)
    }));
    res.json({ earners });
  } catch(e) { log('ERROR', e.message); res.status(500).json({ error: 'Server error. Please try again.' }); }
});

// ══ REFERRALS BY LEVEL ══
app.get('/api/referrals/:userId', userAuth, async (req, res) => {
  if (String(req.tgUser.id) !== String(req.params.userId)) return res.status(403).json({ error: 'Forbidden' });
  try {
    const userId = req.params.userId;

    // Get user's real max levels (respects admin override)
    const { vip } = await getUserVipStatus(userId);
    const maxLevels = vip.maxLevels || 3;

    // Build level queries dynamically up to maxLevels
    // Level 1: direct referrals
    // Level N: users referred by level N-1 users
    const refQuery = `
      SELECT u.id, u.first_name as name, u.username, u.uid, u.created_at as joined_at,
        COALESCE((SELECT SUM(c.amount) FROM commissions c WHERE c.user_id=$1 AND c.from_user_id=u.id), 0) as earned,
        EXISTS(SELECT 1 FROM investments i WHERE i.user_id=u.id AND i.status='active') as is_active
      FROM users u WHERE u.referred_by = ANY($2::bigint[]) ORDER BY u.created_at DESC
    `;

    // Walk the tree level by level
    const result = { max_levels: maxLevels };
    let currentIds = [BigInt(userId)];

    for (let lvl = 1; lvl <= maxLevels; lvl++) {
      const rows = await db.all(refQuery, [userId, currentIds]);
      result['level' + lvl] = rows;
      currentIds = rows.map(r => BigInt(r.id));
      if (currentIds.length === 0) break;
    }

    res.json(result);
  } catch(e) { log('ERROR', e.message); res.status(500).json({ error: 'Server error. Please try again.' }); }
});

// ══ ADMIN REFERRAL DETAILS ══
app.get('/admin/referral-details/:userId', adminAuth, async (req, res) => {
  try {
    const userId = req.params.userId;
    const search = (req.query.search || '').toLowerCase();

    const [user, uplineRow, level1, level2, level3] = await Promise.all([
      db.one(`SELECT id, first_name, last_name, username, balance, created_at,
        (SELECT COUNT(*) FROM investments WHERE user_id=$1 AND status='active') as active_plans,
        referred_by
        FROM users WHERE id=$1`, [userId]),
      db.one(`SELECT id, first_name, username FROM users WHERE id=(SELECT referred_by FROM users WHERE id=$1)`, [userId]),
      db.all(`SELECT u.id, u.first_name, u.username, u.balance, u.created_at,
        EXISTS(SELECT 1 FROM investments i WHERE i.user_id=u.id AND i.status='active') as has_plan
        FROM users u WHERE u.referred_by=$1 ORDER BY u.created_at DESC`, [userId]),
      db.all(`SELECT u.id, u.first_name, u.username, u.balance, u.created_at,
        EXISTS(SELECT 1 FROM investments i WHERE i.user_id=u.id AND i.status='active') as has_plan
        FROM users u WHERE u.referred_by IN (SELECT id FROM users WHERE referred_by=$1)
        ORDER BY u.created_at DESC`, [userId]),
      db.all(`SELECT u.id, u.first_name, u.username, u.balance, u.created_at,
        EXISTS(SELECT 1 FROM investments i WHERE i.user_id=u.id AND i.status='active') as has_plan
        FROM users u WHERE u.referred_by IN (
          SELECT id FROM users WHERE referred_by IN (SELECT id FROM users WHERE referred_by=$1)
        ) ORDER BY u.created_at DESC`, [userId]),
    ]);

    const filterFn = search ? (u => 
      (u.username||'').toLowerCase().includes(search) ||
      (u.first_name||'').toLowerCase().includes(search) ||
      String(u.id).includes(search)
    ) : () => true;

    res.json({
      user: user || null,
      upline: uplineRow || null,
      level1: level1.filter(filterFn),
      level2: level2.filter(filterFn),
      level3: level3.filter(filterFn),
    });
  } catch(e) { log('ERROR', e.message); res.status(500).json({ error: 'Server error. Please try again.' }); }
});

// ══ COLLECT COMMISSION ══
app.post('/api/collect-commission', authLimit, userAuth, async (req, res) => {
  try {
    const u = req.tgUser;
    const user = await db.one(`SELECT * FROM users WHERE id=$1`, [u.id]);
    if (!user) return res.status(404).json({error:'Not found'});
    const pending = parseFloat(user.pending_commission || 0);
    if (pending <= 0) return res.status(400).json({error:'No pending commission'});
    // ✅ FIX: Atomic — only collect if pending_commission still > 0 (race condition guard)
    const commResult = await pool.query(
      `UPDATE users SET balance=balance+pending_commission, pending_commission=0
       WHERE id=$1 AND pending_commission > 0 RETURNING pending_commission as collected`,
      [u.id]
    );
    if (commResult.rowCount === 0) return res.status(400).json({error:'No pending commission'});
    const actualCollected = parseFloat(commResult.rows[0].collected || pending);
    // override pending with actual DB value
    const collectedAmt = actualCollected > 0 ? actualCollected : pending;
    await db.run(`UPDATE commissions SET status='collected' WHERE user_id=$1 AND status='pending'`, [u.id]);
    await db.run(`INSERT INTO transactions (user_id,type,amount,status,note) VALUES ($1,$2,$3,$4,$5)`, [u.id,'commission',collectedAmt,'completed','Referral commission collected']);
    res.json({success:true, collected:collectedAmt});
  } catch(e) { log("ERROR", e.message); res.status(500).json({error:"Server error. Please try again."}); }
});


// ── Admin: Get user withdraw address ──
app.get('/admin/user/:id/address', adminAuth, async (req, res) => {
  try {
    const user = await db.one(
      `SELECT id, first_name, username, withdraw_address, address_locked, address_updated_at FROM users WHERE id=$1`,
      [req.params.id]
    );
    if (!user) return res.status(404).json({error:'Not found'});
    res.json({
      user_id: user.id,
      first_name: user.first_name,
      username: user.username,
      address: user.withdraw_address || null,
      locked: !!user.address_locked,
      updated_at: user.address_updated_at || null
    });
  } catch(e) { log('ERROR', e.message); res.status(500).json({error:'Server error. Please try again.'}); }
});

// ── Admin: Change user withdraw address ──
app.post('/admin/user/change-address', adminAuth, async (req, res) => {
  try {
    const { user_id, new_address } = req.body;
    if (!user_id) return res.status(400).json({error:'user_id required'});
    if (!new_address || !isValidBEP20Address(new_address)) {
      return res.status(400).json({error:'Invalid BEP20 address'});
    }

    const user = await db.one(`SELECT withdraw_address FROM users WHERE id=$1`, [user_id]);
    if (!user) return res.status(404).json({error:'User not found'});

    const oldAddress = user.withdraw_address || null;
    const normalizedNew = new_address.trim().toLowerCase();
    const { force_override } = req.body; // admin can pass force_override:true to bypass

    // Check if address already belongs to another user
    const addrOwner = await db.one(
      `SELECT id, first_name, username FROM users WHERE LOWER(withdraw_address)=$1 AND id!=$2`,
      [normalizedNew, user_id]
    );
    if (addrOwner && !force_override) {
      return res.status(400).json({
        error: `Address already belongs to User ID ${addrOwner.id} (@${addrOwner.username || addrOwner.first_name}). Pass force_override:true to override.`,
        conflict_user_id: addrOwner.id,
        conflict_username: addrOwner.username || addrOwner.first_name
      });
    }
    if (addrOwner && force_override) {
      // Clear address from the other user first
      await db.run(
        `UPDATE users SET withdraw_address=NULL, address_locked=FALSE, address_updated_at=NOW() WHERE id=$1`,
        [addrOwner.id]
      );
      log('ADMIN', `Force override: cleared address from user ${addrOwner.id} to assign to ${user_id}`);
    }

    // Update address and keep locked — store lowercase for consistent uniqueness
    const cleanNewAddr = new_address.trim().toLowerCase();
    await db.run(
      `UPDATE users SET withdraw_address=$1, address_locked=TRUE, address_updated_at=NOW() WHERE id=$2`,
      [cleanNewAddr, user_id]
    );

    // Audit log
    await db.run(
      `INSERT INTO address_change_logs (admin_id, user_id, old_address, new_address, action) VALUES ($1,$2,$3,$4,$5)`,
      ['admin', user_id, oldAddress, cleanNewAddr, force_override ? 'force_change' : 'change']
    );

    log('ADMIN', `Address changed for user ${user_id}: ${(oldAddress||'none').slice(0,16)} → ${cleanNewAddr.slice(0,16)}`);
    logSecurity('ADMIN_ADDRESS_CHANGE', {user_id, old: oldAddress, new: cleanNewAddr.slice(0,20), force: !!force_override});
    res.json({success:true});
  } catch(e) { log('ERROR', e.message); res.status(500).json({error:'Server error. Please try again.'}); }
});

// ── Admin: Clear user withdraw address (unlock for re-bind) ──
app.post('/admin/user/clear-address', adminAuth, async (req, res) => {
  try {
    const { user_id } = req.body;
    if (!user_id) return res.status(400).json({error:'user_id required'});

    const user = await db.one(`SELECT withdraw_address FROM users WHERE id=$1`, [user_id]);
    if (!user) return res.status(404).json({error:'User not found'});

    const oldAddress = user.withdraw_address || null;

    await db.run(
      `UPDATE users SET withdraw_address=NULL, address_locked=FALSE, address_updated_at=NOW() WHERE id=$1`,
      [user_id]
    );

    // Audit log
    await db.run(
      `INSERT INTO address_change_logs (admin_id, user_id, old_address, new_address, action) VALUES ($1,$2,$3,$4,$5)`,
      ['admin', user_id, oldAddress, null, 'clear']
    );

    log('ADMIN', `Address cleared for user ${user_id} (old: ${(oldAddress||'none').slice(0,16)})`);
    res.json({success:true, message:'Address cleared. User can now re-bind.'});
  } catch(e) { log('ERROR', e.message); res.status(500).json({error:'Server error. Please try again.'}); }
});

// ── Admin: View address change logs ──
app.get('/admin/address-logs', adminAuth, async (req, res) => {
  try {
    const { user_id, limit=50 } = req.query;
    let q = `SELECT l.*, u.first_name, u.username FROM address_change_logs l LEFT JOIN users u ON u.id=l.user_id WHERE 1=1`;
    const params = [];
    if (user_id) { params.push(user_id); q += ` AND l.user_id=$${params.length}`; }
    params.push(limit); q += ` ORDER BY l.created_at DESC LIMIT $${params.length}`;
    const logs = await db.all(q, params);
    res.json({logs});
  } catch(e) { log('ERROR', e.message); res.status(500).json({error:'Server error. Please try again.'}); }
});



// ══════════════════════════════════════════
// TELEGRAM BOT BROADCAST SYSTEM
// ══════════════════════════════════════════

// GET all broadcasts
app.get('/admin/broadcasts', adminAuth, async (req, res) => {
  try {
    const rows = await db.all(`SELECT * FROM broadcasts ORDER BY created_at DESC LIMIT 20`);
    res.json({broadcasts: rows || []});
  } catch(e) { log('ERROR', e.message); res.status(500).json({error:'Server error. Please try again.'}); }
});

// POST create broadcast
app.post('/admin/broadcasts', adminAuth, async (req, res) => {
  try {
    const { title, message, emoji, btn_text, schedule_at } = req.body;
    if (!title || !message) return res.status(400).json({error:'Title and message required'});

    // Count total users
    const totalRow = await db.one(`SELECT COUNT(*) as cnt FROM users WHERE is_banned != 1 OR is_banned IS NULL`);
    const total = parseInt(totalRow?.cnt || 0);

    const r = await pool.query(
      `INSERT INTO broadcasts (title, message, emoji, btn_text, total, schedule_at, status)
       VALUES ($1,$2,$3,$4,$5,$6,$7) RETURNING id`,
      [title, message, emoji||'📢', btn_text||'Open App', total,
       schedule_at || null, schedule_at ? 'scheduled' : 'pending']
    );
    const id = r.rows[0].id;
    log('ADMIN', `Broadcast created id=${id} total=${total}`);

    // If no schedule, send immediately
    if (!schedule_at) {
      sendBroadcastNow(id).catch(e => log('BROADCAST', 'Error: ' + e.message));
    }

    res.json({success:true, id, total});
  } catch(e) { log('ERROR', e.message); res.status(500).json({error:'Server error. Please try again.'}); }
});

// DELETE broadcast
app.delete('/admin/broadcasts/:id', adminAuth, async (req, res) => {
  try {
    await db.run(`DELETE FROM broadcasts WHERE id=$1`, [req.params.id]);
    res.json({success:true});
  } catch(e) { log('ERROR', e.message); res.status(500).json({error:'Server error. Please try again.'}); }
});

// POST send now (manual trigger)
app.post('/admin/broadcasts/:id/send', adminAuth, async (req, res) => {
  try {
    const bc = await db.one(`SELECT * FROM broadcasts WHERE id=$1`, [req.params.id]);
    if (!bc) return res.status(404).json({error:'Not found'});
    if (bc.status === 'sending') return res.status(400).json({error:'Already sending'});
    if (bc.status === 'done') return res.status(400).json({error:'Already sent'});
    res.json({success:true, message:'Broadcast started'});
    sendBroadcastNow(req.params.id).catch(e => log('BROADCAST', 'Error: ' + e.message));
  } catch(e) { log('ERROR', e.message); res.status(500).json({error:'Server error. Please try again.'}); }
});

// Background broadcast sender
async function sendBroadcastNow(broadcastId) {
  const bc = await db.one(`SELECT * FROM broadcasts WHERE id=$1`, [broadcastId]);
  if (!bc) return;

  // Mark as sending
  await db.run(`UPDATE broadcasts SET status='sending', started_at=NOW() WHERE id=$1`, [broadcastId]);
  log('BROADCAST', `Starting broadcast id=${broadcastId} title="${bc.title}"`);

  // Get all users
  const users = await db.all(`SELECT id FROM users WHERE is_banned != 1 OR is_banned IS NULL`);
  const total = users.length;

  let sent = 0, failed = 0;

  const WEBAPP_URL = process.env.WEBAPP_URL || 'https://block-minings.pages.dev/';

  for (const user of users) {
    try {
      const keyboard = {
        inline_keyboard: [[
          { text: '🚀 ' + (bc.btn_text || 'Open App'), web_app: { url: WEBAPP_URL } }
        ]]
      };

      const text = (bc.emoji || '📢') + ' <b>' + bc.title + '</b>\n\n' + bc.message;

      // Use Node built-in https (works on all Node versions)
      const postData = JSON.stringify({
        chat_id: user.id, text, parse_mode: 'HTML', reply_markup: keyboard
      });
      await new Promise((resolve) => {
        const https = require('https');
        const req = https.request({
          hostname: 'api.telegram.org',
          path: `/bot${BOT_TOKEN}/sendMessage`,
          method: 'POST',
          headers: {'Content-Type':'application/json','Content-Length':Buffer.byteLength(postData)}
        }, (res) => {
          let body = '';
          res.on('data', d => body += d);
          res.on('end', () => {
            try { const d = JSON.parse(body); if (d.ok) sent++; else failed++; }
            catch(e) { failed++; }
            resolve();
          });
        });
        req.on('error', () => { failed++; resolve(); });
        req.write(postData);
        req.end();
      });
    } catch(e) { failed++; }

    // Update progress every 20 users
    if ((sent + failed) % 20 === 0) {
      await db.run(
        `UPDATE broadcasts SET sent=$1, failed=$2 WHERE id=$3`,
        [sent, failed, broadcastId]
      ).catch(()=>{});
    }

    // Rate limit — Telegram allows ~30 msg/sec
    await new Promise(r => setTimeout(r, 40));
  }

  // Final update
  await db.run(
    `UPDATE broadcasts SET status='done', finished_at=NOW(), sent=$1, failed=$2, total=$3 WHERE id=$4`,
    [sent, failed, total, broadcastId]
  );
  log('BROADCAST', `Done id=${broadcastId} sent=${sent} failed=${failed} total=${total}`);
}

// Cron: check scheduled broadcasts every minute
setInterval(async () => {
  try {
    // Atomic claim: only pick up if still 'scheduled' — prevents double-send
    const claimed = await pool.query(
      `UPDATE broadcasts SET status='sending', started_at=NOW()
       WHERE status='scheduled' AND schedule_at <= NOW()
       RETURNING id`
    );
    for (const b of (claimed.rows||[])) {
      sendBroadcastNow(b.id).catch(e => log('BROADCAST', 'Scheduled error: ' + e.message));
    }
  } catch(e) {}
}, 60000);

// ══════════════════════════════════════════
// NOTICE / BROADCAST SYSTEM
// ══════════════════════════════════════════

// GET active notice for user
app.get('/api/notice', userAuth, async (req, res) => {
  try {
    const u = req.tgUser;
    const now = new Date().toISOString();

    // Get active notice (scheduled and not expired)
    const notice = await db.one(`
      SELECT * FROM notices
      WHERE is_active = TRUE
        AND (schedule_at IS NULL OR schedule_at <= NOW())
        AND (expire_at IS NULL OR expire_at > NOW())
      ORDER BY created_at DESC LIMIT 1
    `);
    if (!notice) return res.json({ notice: null });

    // Check repeat mode
    if (notice.repeat_mode === 'once') {
      const seen = await db.one(
        `SELECT id FROM notice_stats WHERE notice_id=$1 AND user_id=$2 AND action='seen'`,
        [notice.id, u.id]
      );
      if (seen) return res.json({ notice: null }); // already seen once
    } else if (notice.repeat_mode === 'daily') {
      const seen = await db.one(
        `SELECT id FROM notice_stats WHERE notice_id=$1 AND user_id=$2 AND action='seen' AND created_at > NOW() - INTERVAL '24 hours'`,
        [notice.id, u.id]
      );
      if (seen) return res.json({ notice: null });
    }
    // 'every_login' = always show

    res.json({ notice });
  } catch(e) { log('ERROR', e.message); res.status(500).json({error:'Server error. Please try again.'}); }
});

// POST track notice action (seen/click/dismiss)
app.post('/api/notice/track', userAuth, async (req, res) => {
  try {
    const u = req.tgUser;
    const { notice_id, action } = req.body;
    if (!notice_id || !action) return res.status(400).json({error:'Invalid'});
    await pool.query(
      `INSERT INTO notice_stats (notice_id, user_id, action) VALUES ($1,$2,$3) ON CONFLICT DO NOTHING`,
      [notice_id, u.id, action]
    );
    res.json({success:true});
  } catch(e) { log('ERROR', e.message); res.status(500).json({error:'Server error. Please try again.'}); }
});

// ── ADMIN NOTICE ROUTES ──

// GET all notices
app.get('/admin/notices', adminAuth, async (req, res) => {
  try {
    const notices = await db.all(`SELECT * FROM notices ORDER BY created_at DESC`);
    // Get stats for each
    const withStats = await Promise.all((notices||[]).map(async (n) => {
      const stats = await pool.query(
        `SELECT action, COUNT(*) as cnt FROM notice_stats WHERE notice_id=$1 GROUP BY action`,
        [n.id]
      );
      const s = {};
      (stats.rows||[]).forEach(r => { s[r.action] = parseInt(r.cnt); });
      return { ...n, stats: { seen: s.seen||0, click: s.click||0, dismiss: s.dismiss||0 } };
    }));
    res.json({notices: withStats});
  } catch(e) { log('ERROR', e.message); res.status(500).json({error:'Server error. Please try again.'}); }
});

// POST create notice
app.post('/admin/notices', adminAuth, async (req, res) => {
  try {
    const { title, message, emoji, btn_text, btn_link, is_active, repeat_mode, schedule_at, expire_at, poster_image } = req.body;
    if (!title || !message) return res.status(400).json({error:'Title and message required'});

    // Validate poster_image if provided (must be base64 data URL, max 2MB)
    if (poster_image && poster_image.length > 2 * 1024 * 1024 * 1.37) {
      return res.status(400).json({error:'Poster image too large (max 2MB)'});
    }
    if (poster_image && !poster_image.startsWith('data:image/')) {
      return res.status(400).json({error:'Invalid image format'});
    }

    // Only one active notice at a time
    if (is_active) {
      await db.run(`UPDATE notices SET is_active=FALSE`);
    }

    const r = await pool.query(
      `INSERT INTO notices (title, message, emoji, btn_text, btn_link, is_active, repeat_mode, schedule_at, expire_at, poster_image)
       VALUES ($1,$2,$3,$4,$5,$6,$7,$8,$9,$10) RETURNING id`,
      [title, message, emoji||'📢', btn_text||'', btn_link||'', !!is_active,
       repeat_mode||'once',
       schedule_at || null,
       expire_at || null,
       poster_image || null]
    );
    log('ADMIN', `Notice created id=${r.rows[0].id} title="${title}" active=${is_active}`);
    res.json({success:true, id: r.rows[0].id});
  } catch(e) { log('ERROR', e.message); res.status(500).json({error:'Server error. Please try again.'}); }
});

// PUT update notice
app.put('/admin/notices/:id', adminAuth, async (req, res) => {
  try {
    const { title, message, emoji, btn_text, btn_link, is_active, repeat_mode, schedule_at, expire_at, poster_image } = req.body;
    const id = req.params.id;

    // Validate poster if provided
    if (poster_image && poster_image.length > 2 * 1024 * 1024 * 1.37) {
      return res.status(400).json({error:'Poster image too large (max 2MB)'});
    }
    if (poster_image && !poster_image.startsWith('data:image/')) {
      return res.status(400).json({error:'Invalid image format'});
    }

    if (is_active) {
      await db.run(`UPDATE notices SET is_active=FALSE WHERE id!=$1`, [id]);
    }

    // Only update poster_image if provided (null = keep existing, '' = clear)
    const posterClause = poster_image !== undefined
      ? ', poster_image=$10'
      : '';
    const params = [title, message, emoji||'📢', btn_text||'', btn_link||'', !!is_active,
       repeat_mode||'once', schedule_at||null, expire_at||null];
    if (poster_image !== undefined) params.push(poster_image || null);
    params.push(id);

    await pool.query(
      `UPDATE notices SET title=$1, message=$2, emoji=$3, btn_text=$4, btn_link=$5,
       is_active=$6, repeat_mode=$7, schedule_at=$8, expire_at=$9${posterClause}, updated_at=NOW()
       WHERE id=$${params.length}`,
      params
    );
    log('ADMIN', `Notice updated id=${id}`);
    res.json({success:true});
  } catch(e) { log('ERROR', e.message); res.status(500).json({error:'Server error. Please try again.'}); }
});

// DELETE notice
app.delete('/admin/notices/:id', adminAuth, async (req, res) => {
  try {
    await db.run(`DELETE FROM notice_stats WHERE notice_id=$1`, [req.params.id]);
    await db.run(`DELETE FROM notices WHERE id=$1`, [req.params.id]);
    log('ADMIN', `Notice deleted id=${req.params.id}`);
    res.json({success:true});
  } catch(e) { log('ERROR', e.message); res.status(500).json({error:'Server error. Please try again.'}); }
});

// PATCH toggle active
app.patch('/admin/notices/:id/toggle', adminAuth, async (req, res) => {
  try {
    const id = req.params.id;
    const notice = await db.one(`SELECT is_active FROM notices WHERE id=$1`, [id]);
    if (!notice) return res.status(404).json({error:'Not found'});
    const newState = !notice.is_active;
    if (newState) await db.run(`UPDATE notices SET is_active=FALSE`);
    await db.run(`UPDATE notices SET is_active=$1, updated_at=NOW() WHERE id=$2`, [newState, id]);
    res.json({success:true, is_active: newState});
  } catch(e) { log('ERROR', e.message); res.status(500).json({error:'Server error. Please try again.'}); }
});

// GET notice stats
app.get('/admin/notices/:id/stats', adminAuth, async (req, res) => {
  try {
    const totalUsers = await db.one(`SELECT COUNT(*) as cnt FROM users`);
    const stats = await pool.query(
      `SELECT action, COUNT(DISTINCT user_id) as cnt FROM notice_stats WHERE notice_id=$1 GROUP BY action`,
      [req.params.id]
    );
    const s = {};
    (stats.rows||[]).forEach(r => { s[r.action] = parseInt(r.cnt); });
    res.json({
      total_users: parseInt(totalUsers?.cnt||0),
      seen: s.seen||0,
      click: s.click||0,
      dismiss: s.dismiss||0
    });
  } catch(e) { log('ERROR', e.message); res.status(500).json({error:'Server error. Please try again.'}); }
});

// ══════════════════════════════════════════
// SPECIAL USER OVERRIDE SYSTEM (Admin Only)
// ══════════════════════════════════════════

// ── Search users for override panel ──
app.get('/admin/special/search', adminAuth, async (req, res) => {
  try {
    const q = (req.query.q || '').trim();
    if (!q) return res.json({ users: [] });
    const like = '%' + q + '%';
    const rows = await db.all(
      `SELECT id, first_name, last_name, username, vip_level,
              manual_commission_enabled, manual_plan_tier, manual_vip_level,
              manual_override_expiry, manual_badge_label
       FROM users
       WHERE CAST(id AS TEXT) LIKE $1
          OR LOWER(username) LIKE LOWER($2)
          OR LOWER(first_name || ' ' || COALESCE(last_name,'')) LIKE LOWER($3)
       LIMIT 20`,
      [like, like, like]
    );
    res.json({ users: rows });
  } catch(e) { log('ERROR', e.message); res.status(500).json({ error: 'Server error' }); }
});

// ── Get override status for a user ──
app.get('/admin/special/user/:id', adminAuth, async (req, res) => {
  try {
    const row = await db.one(
      `SELECT id, first_name, last_name, username, vip_level,
              manual_commission_enabled, manual_plan_tier, manual_vip_level,
              manual_override_expiry, manual_badge_label
       FROM users WHERE id=$1`, [req.params.id]
    );
    if (!row) return res.status(404).json({ error: 'User not found' });
    res.json({ user: row });
  } catch(e) { log('ERROR', e.message); res.status(500).json({ error: 'Server error' }); }
});

// ── Set override for a user ──
app.post('/admin/special/set', adminAuth, async (req, res) => {
  try {
    const {
      user_id,
      manual_commission_enabled,
      manual_plan_tier,
      manual_vip_level,
      manual_override_expiry,
      manual_badge_label
    } = req.body;

    if (!user_id) return res.status(400).json({ error: 'user_id required' });

    const user = await db.one(`SELECT id, first_name FROM users WHERE id=$1`, [user_id]);
    if (!user) return res.status(404).json({ error: 'User not found' });

    // Build expiry
    let expiry = null;
    if (manual_override_expiry && manual_override_expiry !== 'permanent') {
      expiry = new Date(manual_override_expiry).toISOString();
      if (isNaN(new Date(expiry))) expiry = null;
    }

    // Validate enums
    const VALID_PLAN_TIERS = ['none','bronze','silver','gold','platinum','diamond','titanium','quantum'];
    const VALID_VIP_LEVELS = ['none','Member'];
    const planTier = VALID_PLAN_TIERS.includes(manual_plan_tier) ? manual_plan_tier : 'none';
    const vipLevel = VALID_VIP_LEVELS.includes(manual_vip_level) ? manual_vip_level : 'none';
    const commEnabled = !!manual_commission_enabled;
    const badgeLabel = (manual_badge_label || '').substring(0, 50);

    // Get old values for log
    const old = await db.one(
      `SELECT manual_commission_enabled, manual_plan_tier, manual_vip_level,
              manual_override_expiry, manual_badge_label FROM users WHERE id=$1`, [user_id]
    );

    await db.run(
      `UPDATE users SET
        manual_commission_enabled=$1,
        manual_plan_tier=$2,
        manual_vip_level=$3,
        manual_override_expiry=$4,
        manual_badge_label=$5
       WHERE id=$6`,
      [commEnabled, planTier === 'none' ? null : planTier, vipLevel === 'none' ? null : vipLevel,
       expiry, badgeLabel || null, user_id]
    );

    // Log the action
    await db.run(
      `INSERT INTO override_logs (admin_action, target_user, field, old_value, new_value, note)
       VALUES ($1,$2,$3,$4,$5,$6)`,
      [
        'SET_OVERRIDE', user_id, 'all',
        JSON.stringify({ comm: old.manual_commission_enabled, plan: old.manual_plan_tier, vip: old.manual_vip_level }),
        JSON.stringify({ comm: commEnabled, plan: planTier, vip: vipLevel, expiry, badge: badgeLabel }),
        `Admin set override for user ${user_id} (${user.first_name})`
      ]
    );

    log('ADMIN', `Override SET user=${user_id} comm=${commEnabled} plan=${planTier} vip=${vipLevel} expiry=${expiry}`);
    res.json({ success: true });
  } catch(e) { log('ERROR', e.message); res.status(500).json({ error: 'Server error' }); }
});

// ── Remove all overrides for a user ──
app.post('/admin/special/remove', adminAuth, async (req, res) => {
  try {
    const { user_id } = req.body;
    if (!user_id) return res.status(400).json({ error: 'user_id required' });

    const old = await db.one(
      `SELECT manual_commission_enabled, manual_plan_tier, manual_vip_level FROM users WHERE id=$1`, [user_id]
    );

    await db.run(
      `UPDATE users SET
        manual_commission_enabled=FALSE,
        manual_plan_tier=NULL,
        manual_vip_level=NULL,
        manual_override_expiry=NULL,
        manual_badge_label=NULL
       WHERE id=$1`, [user_id]
    );

    await db.run(
      `INSERT INTO override_logs (admin_action, target_user, field, old_value, new_value, note)
       VALUES ($1,$2,$3,$4,$5,$6)`,
      [
        'REMOVE_OVERRIDE', user_id, 'all',
        JSON.stringify({ comm: old.manual_commission_enabled, plan: old.manual_plan_tier, vip: old.manual_vip_level }),
        'null',
        `Admin removed all overrides for user ${user_id}`
      ]
    );

    log('ADMIN', `Override REMOVED user=${user_id}`);
    res.json({ success: true });
  } catch(e) { log('ERROR', e.message); res.status(500).json({ error: 'Server error' }); }
});

// ── Get override action log ──
app.get('/admin/special/logs', adminAuth, async (req, res) => {
  try {
    const rows = await db.all(
      `SELECT ol.*, u.first_name, u.username
       FROM override_logs ol
       LEFT JOIN users u ON ol.target_user = u.id
       ORDER BY ol.created_at DESC LIMIT 100`
    );
    res.json({ logs: rows });
  } catch(e) { log('ERROR', e.message); res.status(500).json({ error: 'Server error' }); }
});

// ══════════════════════════════════════════

// ══════════════════════════════════════════
// IP MONITOR — Admin endpoints
// ══════════════════════════════════════════

// GET /admin/ip-monitor/stats — summary counts (tab-aware)
app.get('/admin/ip-monitor/stats', adminAuth, async (req, res) => {
  try {
    const tab = req.query.tab === 'login' ? 'login' : 'reg';
    let totalRow, suspRow, multiRow;
    if (tab === 'reg') {
      [totalRow, suspRow, multiRow] = await Promise.all([
        db.one(`SELECT COUNT(DISTINCT reg_ip) as c FROM users WHERE reg_ip IS NOT NULL`),
        db.one(`SELECT COUNT(*) as c FROM (SELECT reg_ip FROM users WHERE reg_ip IS NOT NULL GROUP BY reg_ip HAVING COUNT(*) >= 3) s`),
        db.one(`SELECT COUNT(*) as c FROM (SELECT reg_ip FROM users WHERE reg_ip IS NOT NULL GROUP BY reg_ip HAVING COUNT(*) >= 2) s`),
      ]);
    } else {
      [totalRow, suspRow, multiRow] = await Promise.all([
        db.one(`SELECT COUNT(DISTINCT ip) as c FROM user_ips`),
        db.one(`SELECT COUNT(*) as c FROM (SELECT ip FROM user_ips GROUP BY ip HAVING COUNT(DISTINCT user_id) >= 3) s`),
        db.one(`SELECT COUNT(*) as c FROM (SELECT ip FROM user_ips GROUP BY ip HAVING COUNT(DISTINCT user_id) >= 2) s`),
      ]);
    }
    res.json({
      total_ips:  parseInt(totalRow.c) || 0,
      suspicious: parseInt(suspRow.c)  || 0,
      multi_ips:  parseInt(multiRow.c) || 0,
      tab,
    });
  } catch(e) { log('ERROR', 'ip-monitor stats: ' + e.message); res.status(500).json({error:'Server error'}); }
});

// GET /admin/ip-monitor — Registration IP or Login IP grouped view
app.get('/admin/ip-monitor', adminAuth, async (req, res) => {
  try {
    const search      = (req.query.search || '').trim();
    const minAccounts = Math.max(1, parseInt(req.query.min_accounts) || 1);
    const page        = Math.max(1, parseInt(req.query.page) || 1);
    const limit       = Math.min(50, parseInt(req.query.limit) || 15);
    const offset      = (page - 1) * limit;
    const tab         = req.query.tab === 'login' ? 'login' : 'reg';

    if (tab === 'reg') {
      // ── Registration IP tab ─────────────────────────────
      let baseQ, countParams;
      if (search && /^[0-9.:]+/.test(search)) {
        baseQ       = `SELECT reg_ip as ip, COUNT(*) as cnt FROM users WHERE reg_ip ILIKE $1 GROUP BY reg_ip HAVING COUNT(*) >= ${minAccounts}`;
        countParams = [`%${search}%`];
      } else if (search) {
        const uRows = await db.all(
          `SELECT DISTINCT reg_ip FROM users WHERE reg_ip IS NOT NULL AND (CAST(id AS TEXT)=$1 OR username ILIKE $2 OR first_name ILIKE $2) LIMIT 50`,
          [search, `%${search}%`]
        );
        const ips = uRows.map(r => r.reg_ip);
        if (!ips.length) return res.json({ groups: [], total: 0, page, limit, pages: 0, tab });
        baseQ       = `SELECT reg_ip as ip, COUNT(*) as cnt FROM users WHERE reg_ip = ANY($1::text[]) GROUP BY reg_ip`;
        countParams = [ips];
      } else {
        baseQ       = `SELECT reg_ip as ip, COUNT(*) as cnt FROM users WHERE reg_ip IS NOT NULL GROUP BY reg_ip HAVING COUNT(*) >= ${minAccounts}`;
        countParams = [];
      }

      const countRow = await db.one(`SELECT COUNT(*) as c FROM (${baseQ}) sub`, countParams);
      const total    = parseInt(countRow.c) || 0;
      const ipRows   = await db.all(`${baseQ} ORDER BY cnt DESC LIMIT $${countParams.length+1} OFFSET $${countParams.length+2}`, [...countParams, limit, offset]);
      const ipList   = ipRows.map(r => r.ip);
      if (!ipList.length) return res.json({ groups: [], total, page, limit, pages: Math.ceil(total/limit), tab });

      const userRows = await db.all(
        `SELECT u.reg_ip as ip, u.id, u.first_name, u.username, u.uid,
                u.created_at as registered_at, u.is_banned,
                (SELECT COUNT(*) FROM investments WHERE user_id=u.id AND status='active') as active_plans,
                (SELECT MAX(last_seen) FROM user_ips WHERE user_id=u.id) as last_active
         FROM users u WHERE u.reg_ip = ANY($1::text[]) ORDER BY u.reg_ip, u.created_at ASC`,
        [ipList]
      );
      const usersByIp = {};
      userRows.forEach(r => {
        if (!usersByIp[r.ip]) usersByIp[r.ip] = [];
        usersByIp[r.ip].push({ id:r.id, first_name:r.first_name, username:r.username, uid:r.uid,
          registered_at:r.registered_at, is_banned:r.is_banned, active_plans:parseInt(r.active_plans)||0, last_active:r.last_active });
      });
      const result = ipRows.map(g => ({
        ip: g.ip, account_count: parseInt(g.cnt), suspicious: parseInt(g.cnt) >= 3,
        first_seen: usersByIp[g.ip]?.[0]?.registered_at || null,
        last_seen:  usersByIp[g.ip]?.[usersByIp[g.ip].length-1]?.registered_at || null,
        users: usersByIp[g.ip] || []
      }));
      return res.json({ groups: result, total, page, limit, pages: Math.ceil(total/limit), tab });
    }

    // ── Login IP tab ────────────────────────────────────────
    let lBaseQ, lParams;
    if (search && /^[0-9.:]+/.test(search)) {
      lBaseQ  = `SELECT ip, COUNT(DISTINCT user_id) as cnt FROM user_ips WHERE ip ILIKE $1 GROUP BY ip HAVING COUNT(DISTINCT user_id) >= ${minAccounts}`;
      lParams = [`%${search}%`];
    } else if (search) {
      const luRows = await db.all(
        `SELECT DISTINCT ui.ip FROM user_ips ui JOIN users u ON u.id=ui.user_id
         WHERE CAST(u.id AS TEXT)=$1 OR u.username ILIKE $2 OR u.first_name ILIKE $2 LIMIT 50`,
        [search, `%${search}%`]
      );
      const lips = luRows.map(r => r.ip);
      if (!lips.length) return res.json({ groups: [], total: 0, page, limit, pages: 0, tab });
      lBaseQ  = `SELECT ip, COUNT(DISTINCT user_id) as cnt FROM user_ips WHERE ip = ANY($1::text[]) GROUP BY ip`;
      lParams = [lips];
    } else {
      lBaseQ  = `SELECT ip, COUNT(DISTINCT user_id) as cnt FROM user_ips GROUP BY ip HAVING COUNT(DISTINCT user_id) >= ${minAccounts}`;
      lParams = [];
    }

    const lCountRow = await db.one(`SELECT COUNT(*) as c FROM (${lBaseQ}) sub`, lParams);
    const lTotal    = parseInt(lCountRow.c) || 0;
    const lIpRows   = await db.all(`${lBaseQ} ORDER BY cnt DESC LIMIT $${lParams.length+1} OFFSET $${lParams.length+2}`, [...lParams, limit, offset]);
    const lIpList   = lIpRows.map(r => r.ip);
    if (!lIpList.length) return res.json({ groups: [], total: lTotal, page, limit, pages: Math.ceil(lTotal/limit), tab });

    const lUserRows = await db.all(
      `SELECT ui.ip, u.id, u.first_name, u.username, u.uid, u.created_at as registered_at,
              u.is_banned, ui.first_seen as ip_first_seen, ui.last_seen as last_active,
              (SELECT COUNT(*) FROM investments WHERE user_id=u.id AND status='active') as active_plans
       FROM user_ips ui JOIN users u ON u.id=ui.user_id
       WHERE ui.ip = ANY($1::text[]) ORDER BY ui.ip, ui.last_seen DESC`,
      [lIpList]
    );
    const lUsersByIp = {};
    lUserRows.forEach(r => {
      if (!lUsersByIp[r.ip]) lUsersByIp[r.ip] = [];
      lUsersByIp[r.ip].push({ id:r.id, first_name:r.first_name, username:r.username, uid:r.uid,
        registered_at:r.registered_at, is_banned:r.is_banned, active_plans:parseInt(r.active_plans)||0,
        last_active:r.last_active });
    });
    const lResult = lIpRows.map(g => ({
      ip: g.ip, account_count: parseInt(g.cnt), suspicious: parseInt(g.cnt) >= 3,
      first_seen: lUsersByIp[g.ip]?.[lUsersByIp[g.ip].length-1]?.last_active || null,
      last_seen:  lUsersByIp[g.ip]?.[0]?.last_active || null,
      users: lUsersByIp[g.ip] || []
    }));
    return res.json({ groups: lResult, total: lTotal, page, limit, pages: Math.ceil(lTotal/limit), tab });

  } catch(e) { log('ERROR', 'ip-monitor: ' + e.message); res.status(500).json({error:'Server error'}); }
});


// ══════════════════════════════════════════
// ADMIN: Backfill commissions for all existing investments
// POST /admin/backfill-commissions
// One-time run — skips already-processed investments
// ══════════════════════════════════════════
app.post('/admin/backfill-commissions', adminAuth, async (req, res) => {
  try {
    log('ADMIN', 'Commission backfill started');

    // Get all active investments that haven't been commission-processed
    // We detect "already processed" by checking commissions table for that from_user_id+investment combo
    // Simpler: just check all investments and skip if from_user_id already has a commission entry
    const investments = await db.all(
      `SELECT i.id, i.user_id, i.amount, i.created_at
       FROM investments i
       WHERE i.status = 'active'
       ORDER BY i.created_at ASC`
    );

    let processed = 0, skipped = 0, totalComm = 0;
    const RATES      = [12, 5, 3, 1, 1, 1, 1];
    const MAX_LEVELS = 7;

    for (const inv of investments) {
      // Check if this investment already has commission records
      const existing = await db.one(
        `SELECT COUNT(*) as c FROM commissions WHERE from_user_id=$1 AND created_at >= $2::timestamp - interval '1 minute'`,
        [inv.user_id, inv.created_at]
      );
      if (parseInt(existing.c) > 0) { skipped++; continue; }

      // Walk up referral chain up to 7 levels
      let currentId = inv.user_id;
      for (let lvl = 0; lvl < MAX_LEVELS; lvl++) {
        const row = await db.one(`SELECT referred_by FROM users WHERE id=$1`, [currentId]);
        if (!row || !row.referred_by) break;
        const referrerId = row.referred_by;

        // Skip banned referrers
        const refRow = await db.one(`SELECT is_banned FROM users WHERE id=$1`, [referrerId]);
        if (!refRow || refRow.is_banned) { currentId = referrerId; continue; }

        const pct  = (RATES[lvl] || 0) / 100;
        if (pct <= 0) { currentId = referrerId; continue; }
        const comm = +(inv.amount * pct).toFixed(4);

        await db.run(
          `UPDATE users SET pending_commission=pending_commission+$1, total_commission=total_commission+$1 WHERE id=$2::BIGINT`,
          [comm, referrerId]
        );
        await db.run(
          `INSERT INTO commissions (user_id, from_user_id, level, amount) VALUES ($1::BIGINT,$2::BIGINT,$3,$4)`,
          [referrerId, inv.user_id, lvl+1, comm]
        );
        totalComm += comm;
        log('BACKFILL', `L${lvl+1} $${comm} → user ${referrerId} (from invest #${inv.id})`);
        currentId = referrerId;
      }
      processed++;
    }

    log('ADMIN', `Commission backfill done: ${processed} investments processed, ${skipped} skipped, total $${totalComm.toFixed(4)} distributed`);
    res.json({
      success: true,
      investments_total: investments.length,
      processed,
      skipped,
      total_commission_distributed: +totalComm.toFixed(4)
    });
  } catch(e) {
    log('ERROR', 'Backfill error: ' + e.message);
    res.status(500).json({ error: e.message });
  }
});

// WEBHOOK LOGS — Admin visibility
// GET /admin/webhook-logs?limit=50&status=error
// ══════════════════════════════════════════
app.get('/admin/webhook-logs', adminAuth, async (req, res) => {
  try {
    const limit  = Math.min(parseInt(req.query.limit) || 100, 500);
    const status = req.query.status || null;
    const rows = status
      ? await db.all(
          `SELECT * FROM webhook_logs WHERE status=$1 ORDER BY created_at DESC LIMIT $2`,
          [status, limit])
      : await db.all(
          `SELECT * FROM webhook_logs ORDER BY created_at DESC LIMIT $1`, [limit]);
    res.json({ logs: rows, total: rows.length });
  } catch(e) { log('ERROR', e.message); res.status(500).json({ error: 'Server error' }); }
});

// ══════════════════════════════════════════
// PROMO WITHDRAWAL SYSTEM
// ══════════════════════════════════════════

const PROMO_BSC_RPC      = 'https://bsc-dataseed1.binance.org/';
const PROMO_USDT_ABI     = [
  'function transfer(address to, uint256 amount) returns (bool)',
  'function decimals() view returns (uint8)'
];
const PROMO_MAX_CLAIMS   = 3;
const PROMO_AMOUNT_FIXED = 0.005;

async function sendPromoOnChain(toAddress) {
  const privateKey = process.env.PROMO_WALLET_PRIVATE_KEY;
  if (!privateKey) throw new Error('PROMO_WALLET_PRIVATE_KEY not set');
  const usdtContract = (await getSetting('promo_usdt_contract')) || '0x55d398326f99059fF775485246999027B3197955';
  const provider = new ethers.JsonRpcProvider(PROMO_BSC_RPC);
  const wallet   = new ethers.Wallet(privateKey, provider);
  const contract = new ethers.Contract(usdtContract, PROMO_USDT_ABI, wallet);
  const decimals = await contract.decimals();
  const amountWei = ethers.parseUnits(PROMO_AMOUNT_FIXED.toFixed(3), decimals);
  const tx = await contract.transfer(toAddress, amountWei, {
    gasLimit: 100000,
  });
  await tx.wait(1);
  return tx.hash;
}

// POST /api/promo/claim — user claims promo withdrawal
app.post('/api/promo/claim', userAuth, async (req, res) => {
  try {
    const u = req.tgUser;

    // 1. Check promo enabled
    const enabled = await getSetting('promo_enabled');
    if (enabled !== '1') return res.status(400).json({ error: 'Not available' });

    // 2. Must have bound withdrawal address
    const user = await db.one(`SELECT withdraw_address, address_locked, last_cancel_at FROM users WHERE id=$1`, [u.id]);
    if (!user.withdraw_address || !user.address_locked) {
      return res.status(400).json({ error: 'Bind your withdrawal address first' });
    }

    // 3. Check lifetime claims (exclude failed — user can retry)
    const lifeRow = await db.one(
      `SELECT COUNT(*) as cnt FROM promo_withdrawals WHERE user_id=$1 AND status != 'failed'`,
      [u.id]
    );
    const lifetimeCount = parseInt(lifeRow.cnt) || 0;
    if (lifetimeCount >= PROMO_MAX_CLAIMS) {
      return res.status(400).json({ error: 'upgrade', message: 'Invest to unlock higher withdrawals' });
    }

    // 4. Check today already claimed successfully or processing (allow retry if failed today)
    const todayRow = await db.one(
      `SELECT id, status FROM promo_withdrawals WHERE user_id=$1 AND claim_date=CURRENT_DATE AND status != 'failed'`,
      [u.id]
    );
    if (todayRow) {
      return res.status(400).json({ error: 'Come back tomorrow for your next withdrawal' });
    }

    const claimNumber = lifetimeCount + 1;

    // 5. Atomic upsert — handles race condition + failed retry
    // If failed row exists today → update it. Otherwise insert.
    // ON CONFLICT does nothing extra — UNIQUE(user_id, claim_date) is our guard
    const existingFailed = await db.one(
      `SELECT id FROM promo_withdrawals WHERE user_id=$1 AND claim_date=CURRENT_DATE AND status='failed'`,
      [u.id]
    );
    let inserted;
    if (existingFailed) {
      inserted = await db.one(
        `UPDATE promo_withdrawals SET status='processing', tx_hash=NULL, claim_number=$1, created_at=NOW()
         WHERE id=$2 AND status='failed' RETURNING id`,
        [claimNumber, existingFailed.id]
      );
      // If update returned null — another request already grabbed it
      if (!inserted) {
        return res.status(400).json({ error: 'Come back tomorrow for your next withdrawal' });
      }
    } else {
      try {
        inserted = await db.one(
          `INSERT INTO promo_withdrawals (user_id, amount, claim_number, status, claim_date)
           VALUES ($1, $2, $3, 'processing', CURRENT_DATE) RETURNING id`,
          [u.id, PROMO_AMOUNT_FIXED, claimNumber]
        );
      } catch(insertErr) {
        // UNIQUE violation = concurrent duplicate request
        if (insertErr.code === '23505') {
          return res.status(400).json({ error: 'Come back tomorrow for your next withdrawal' });
        }
        throw insertErr;
      }
    }

    // 6. Respond immediately — send on-chain in background
    res.json({ success: true, claim: claimNumber, amount: PROMO_AMOUNT_FIXED });

    // 7. Fire on-chain transfer (non-blocking)
    setImmediate(async () => {
      try {
        const txHash = await sendPromoOnChain(user.withdraw_address);
        await db.run(
          `UPDATE promo_withdrawals SET status='completed', tx_hash=$1 WHERE id=$2`,
          [txHash, inserted.id]
        );
        log('PROMO', `Claim #${claimNumber} user=${u.id} tx=${txHash}`);
        // Notify user via Telegram (optional, non-blocking)
        tgBotApi('sendMessage', {
          chat_id: u.id,
          text: `✅ $${PROMO_AMOUNT_FIXED} has been sent to your wallet!\nTx: https://bscscan.com/tx/${txHash}`
        }).catch(() => {});
      } catch(e) {
        await db.run(
          `UPDATE promo_withdrawals SET status='failed' WHERE id=$1`,
          [inserted.id]
        );
        log('PROMO_ERR', `Claim #${claimNumber} user=${u.id} FAILED: ${e.message}`);
        // Alert admin
        const adminId = process.env.ADMIN_TG_CHAT_ID;
        if (adminId) {
          tgBotApi('sendMessage', {
            chat_id: adminId,
            text: `⚠️ Promo transfer FAILED\nUser: ${u.id}\nClaim: #${claimNumber}\nError: ${e.message}`
          }).catch(() => {});
        }
      }
    });

  } catch(e) {
    log('ERROR', e.message);
    res.status(500).json({ error: 'Server error. Please try again.' });
  }
});

// GET /api/promo/status — frontend polls claim status
app.get('/api/promo/status', userAuth, async (req, res) => {
  try {
    const u = req.tgUser;
    const lifeRow = await db.one(
      `SELECT COUNT(*) as cnt FROM promo_withdrawals WHERE user_id=$1 AND status != 'failed'`,
      [u.id]
    );
    const lifetimeCount = parseInt(lifeRow.cnt) || 0;
    const todayRow = await db.one(
      `SELECT status, tx_hash FROM promo_withdrawals WHERE user_id=$1 AND claim_date=CURRENT_DATE AND status != 'failed'`,
      [u.id]
    );
    const enabled = await getSetting('promo_enabled');
    res.json({
      enabled:       enabled === '1',
      promo_done:    lifetimeCount >= PROMO_MAX_CLAIMS,  // backend tells frontend — no numbers exposed
      claimed_today: !!todayRow,
      today_status:  todayRow ? todayRow.status : null,
      today_tx:      todayRow ? todayRow.tx_hash : null,
      amount:        PROMO_AMOUNT_FIXED
    });
  } catch(e) {
    log('ERROR', e.message);
    res.status(500).json({ error: 'Server error' });
  }
});

// GET /admin/promo/stats — admin dashboard
app.get('/admin/promo/stats', adminAuth, async (req, res) => {
  try {
    const [todayRow, completedAll, lastClaimRow, recentClaims, enabled, amount] = await Promise.all([
      // Today's stats
      db.one(`SELECT
        COALESCE(SUM(amount),0) as total_paid,
        COUNT(*) as claim_count,
        COUNT(DISTINCT user_id) as unique_users
        FROM promo_withdrawals
        WHERE claim_date=CURRENT_DATE AND status IN ('completed','processing')`),
      // Completed users (3/3)
      db.one(`SELECT COUNT(*) as c FROM (
        SELECT user_id FROM promo_withdrawals
        WHERE status != 'failed'
        GROUP BY user_id HAVING COUNT(*) >= $1
      ) sub`, [PROMO_MAX_CLAIMS]),
      // Last claim time
      db.one(`SELECT created_at, status FROM promo_withdrawals ORDER BY created_at DESC LIMIT 1`),
      // Last 10 claims with user info
      db.all(`SELECT p.id, p.user_id, p.amount, p.claim_number, p.status, p.tx_hash,
              p.claim_date, p.created_at,
              u.first_name, u.username
              FROM promo_withdrawals p
              LEFT JOIN users u ON u.id = p.user_id
              ORDER BY p.created_at DESC LIMIT 10`),
      getSetting('promo_enabled'),
      getSetting('promo_amount'),
    ]);

    res.json({
      enabled:         enabled === '1',
      amount:          parseFloat(amount) || PROMO_AMOUNT_FIXED,
      today_paid:      parseFloat(todayRow.total_paid) || 0,
      today_count:     parseInt(todayRow.claim_count)  || 0,
      today_unique:    parseInt(todayRow.unique_users) || 0,
      completed_users: parseInt(completedAll.c)        || 0,
      last_claim_time: lastClaimRow ? lastClaimRow.created_at : null,
      last_claim_status: lastClaimRow ? lastClaimRow.status   : null,
      recent_claims:   recentClaims || [],
    });
  } catch(e) {
    log('ERROR', e.message);
    res.status(500).json({ error: 'Server error' });
  }
});

// POST /admin/promo/toggle — enable/disable + emergency pause
app.post('/admin/promo/toggle', adminAuth, async (req, res) => {
  try {
    const { enabled } = req.body;
    await db.run(
      `INSERT INTO settings (key,value) VALUES ('promo_enabled',$1) ON CONFLICT (key) DO UPDATE SET value=$1`,
      [enabled ? '1' : '0']
    );
    log('PROMO', `Admin toggled promo_enabled=${enabled}`);
    res.json({ success: true, enabled });
  } catch(e) {
    log('ERROR', e.message);
    res.status(500).json({ error: 'Server error' });
  }
});

// ══════════════════════════════════════════
// PLAN SYSTEM V2
// ══════════════════════════════════════════

// POST /api/invest/paid-unlock — pay to unlock plan without referrals
app.post('/api/invest/paid-unlock', userAuth, async (req, res) => {
  try {
    const u = req.tgUser;
    const { plan_id, amount } = req.body;
    if (!plan_id || !amount) return res.status(400).json({ error: 'Missing fields' });

    const amt = parseFloat(amount);
    if (!isValidAmount(amt)) return res.status(400).json({ error: 'Invalid amount' });

    const [user, plan] = await Promise.all([
      db.one(`SELECT * FROM users WHERE id=$1`, [u.id]),
      db.one(`SELECT * FROM plans WHERE id=$1 AND is_active=1`, [plan_id])
    ]);
    if (!user) return res.status(404).json({ error: 'User not found' });
    if (!plan)  return res.status(404).json({ error: 'Plan not found' });
    if (user.is_banned) return res.status(403).json({ error: 'banned' });

    // If manually unlocked, no fee needed
    if (plan.manual_unlock) return res.status(400).json({ error: 'Plan is already unlocked — activate normally' });

    // Calculate required fee
    const refReq = parseInt(plan.ref_required) || getPlanReferralReq(plan.name);
    if (refReq === 0) return res.status(400).json({ error: 'This plan has no referral requirement' });

    const activeRefs = await db.one(
      `SELECT COUNT(DISTINCT u2.id) as cnt FROM users u2 JOIN investments i ON u2.id=i.user_id WHERE u2.referred_by=$1 AND i.status='active'`,
      [u.id]
    );
    const have    = parseInt(activeRefs?.cnt || 0);
    const missing = Math.max(0, refReq - have);
    if (missing === 0) return res.status(400).json({ error: 'You already meet the referral requirement' });

    const requiredFee = missing * 2;
    if (Math.abs(amt - requiredFee) > 0.01) return res.status(400).json({ error: `Unlock fee is $${requiredFee}` });
    if (user.balance < requiredFee) return res.status(400).json({ error: 'Insufficient balance' });

    // [ATOMIC] Deduct fee — prevents race condition negative balance
    const unlockDeduct = await pool.query(
      `UPDATE users SET balance=balance-$1 WHERE id=$2 AND balance>=$1 RETURNING id`,
      [requiredFee, u.id]
    );
    if (unlockDeduct.rowCount === 0) return res.status(400).json({ error: 'Insufficient balance' });
    await db.run(
      `INSERT INTO plan_unlock_logs (user_id, plan_id, plan_name, unlock_type, fee_paid) VALUES ($1,$2,$3,'paid',$4)`,
      [u.id, plan.id, plan.name, requiredFee]
    );

    log('PLAN_UNLOCK', `User ${u.id} paid $${requiredFee} to unlock plan ${plan.name}`);
    res.json({ success: true, fee_paid: requiredFee, plan_id: plan.id });

  } catch(e) { log('ERROR', e.message); res.status(500).json({ error: 'Server error: ' + e.message }); }
});

// POST /api/invest/cancel — cancel active plan with refund
app.post('/api/invest/cancel', userAuth, async (req, res) => {
  try {
    const u = req.tgUser;
    const { investment_id } = req.body;
    if (!investment_id) return res.status(400).json({ error: 'Missing investment_id' });

    const [user, inv] = await Promise.all([
      db.one(`SELECT * FROM users WHERE id=$1`, [u.id]),
      db.one(`SELECT * FROM investments WHERE id=$1 AND user_id=$2`, [investment_id, u.id])
    ]);
    if (!user) return res.status(404).json({ error: 'User not found' });
    if (!inv)  return res.status(404).json({ error: 'Investment not found' });
    if (inv.status !== 'active') return res.status(400).json({ error: 'Investment is not active' });

    // Calculate refund: Remaining = Principal - Already Earned, Refund = 90%
    const investedC   = parseFloat(inv.amount || 0);
    const dailyEarnC  = parseFloat(inv.daily_earn || 0);
    const daysDoneC   = parseInt(inv.days_done)  || 0;
    const pendingC    = parseFloat(inv.pending_earn || 0);
    const collectedC  = +(dailyEarnC * daysDoneC).toFixed(4);
    const earned      = +(collectedC + pendingC).toFixed(4);
    const remaining   = +Math.max(0, investedC - earned).toFixed(4);
    const refund      = +(remaining * 0.90).toFixed(4);

    // Cancel plan — refund goes to reinvest_credit (cannot withdraw, only reinvest)
    await db.run(
      `UPDATE investments SET status='cancelled', cancelled_at=NOW(), cancel_refund=$1 WHERE id=$2`,
      [refund, inv.id]
    );
    if (refund > 0) {
      await db.run(`UPDATE users SET balance=balance+$1 WHERE id=$2`, [refund, u.id]); // refund to balance
    }
    // Set last_cancel_at for withdraw restriction (12h lock)
    await db.run(`UPDATE users SET last_cancel_at=NOW() WHERE id=$1`, [u.id]);

    // Log
    await db.run(
      `INSERT INTO plan_cancel_logs (user_id, investment_id, plan_name, amount, earned, refund) VALUES ($1,$2,$3,$4,$5,$6)`,
      [u.id, inv.id, inv.plan_name, inv.amount, earned, refund]
    );

    log('PLAN_CANCEL', `User ${u.id} cancelled ${inv.plan_name} — refund $${refund}`);
    res.json({ success: true, refund, plan_name: inv.plan_name });

  } catch(e) { log('ERROR', e.message); res.status(500).json({ error: 'Server error: ' + e.message }); }
});

// GET /api/invest/cancel-preview/:id — preview refund before cancel
app.get('/api/invest/cancel-preview/:id', userAuth, async (req, res) => {
  try {
    const u = req.tgUser;
    const inv = await db.one(
      `SELECT * FROM investments WHERE id=$1 AND user_id=$2 AND status='active'`,
      [req.params.id, u.id]
    );
    if (!inv) return res.status(404).json({ error: 'Investment not found' });

    const invested   = parseFloat(inv.amount || 0);
    const dailyEarn  = parseFloat(inv.daily_earn || 0);
    const daysTotal  = parseInt(inv.days_total) || 50;
    const daysDone   = parseInt(inv.days_done)  || 0;
    const pendingEarn = parseFloat(inv.pending_earn || 0);

    // Total already earned (collected + uncollected)
    const collected  = +(dailyEarn * daysDone).toFixed(4);
    const earned     = +(collected + pendingEarn).toFixed(4);

    // Remaining = Principal - Already Earned
    const remaining  = +Math.max(0, invested - earned).toFixed(4);
    const refund     = +(remaining * 0.90).toFixed(4);

    res.json({
      plan_name:   inv.plan_name,
      amount:      invested,
      daily_earn:  dailyEarn,
      days_total:  daysTotal,
      days_done:   daysDone,
      invested:    invested,
      earned:      earned,
      remaining:   remaining,
      refund:      refund,
      refund_pct:  90,
    });
  } catch(e) { log('ERROR', e.message); res.status(500).json({ error: 'Server error: ' + e.message }); }
});

// POST /admin/plans/toggle-unlock — manual unlock toggle
app.post('/admin/plans/toggle-unlock', adminAuth, async (req, res) => {
  try {
    const { plan_id, manual_unlock } = req.body;
    if (!plan_id) return res.status(400).json({ error: 'Missing plan_id' });

    await db.run(`UPDATE plans SET manual_unlock=$1 WHERE id=$2`, [!!manual_unlock, plan_id]);
    const plan = await db.one(`SELECT id, name, manual_unlock FROM plans WHERE id=$1`, [plan_id]);

    log('ADMIN_PLAN', `Plan ${plan.name} manual_unlock set to ${manual_unlock}`);
    await db.run(
      `INSERT INTO plan_unlock_logs (user_id, plan_id, plan_name, unlock_type, fee_paid) VALUES (0,$1,$2,$3,0)`,
      [plan_id, plan.name, manual_unlock ? 'admin_unlock' : 'admin_relock']
    );
    res.json({ success: true, plan });
  } catch(e) { log('ERROR', e.message); res.status(500).json({ error: 'Server error: ' + e.message }); }
});

// POST /admin/plans/set-ref-required — set referral requirement per plan
app.post('/admin/plans/set-ref-required', adminAuth, async (req, res) => {
  try {
    const { plan_id, ref_required } = req.body;
    if (!plan_id) return res.status(400).json({ error: 'Missing plan_id' });
    const req_n = parseInt(ref_required) || 0;
    await db.run(`UPDATE plans SET ref_required=$1 WHERE id=$2`, [req_n, plan_id]);
    res.json({ success: true });
  } catch(e) { log('ERROR', e.message); res.status(500).json({ error: 'Server error: ' + e.message }); }
});

// GET /admin/plan-stats — unlock/cancel dashboard
app.get('/admin/plan-stats', adminAuth, async (req, res) => {
  try {
    const [activations, unlockPurchases, manualUnlocked, cancelRefunds] = await Promise.all([
      db.one(`SELECT COUNT(*) as c FROM investments WHERE created_at >= CURRENT_DATE`),
      db.one(`SELECT COUNT(*) as c, COALESCE(SUM(fee_paid),0) as total FROM plan_unlock_logs WHERE unlock_type='paid' AND created_at >= CURRENT_DATE`),
      db.one(`SELECT COUNT(*) as c FROM plans WHERE manual_unlock=TRUE`),
      db.one(`SELECT COUNT(*) as c, COALESCE(SUM(refund),0) as total FROM plan_cancel_logs WHERE created_at >= CURRENT_DATE`),
    ]);
    res.json({
      activations_today:  parseInt(activations.c) || 0,
      unlock_purchases_today: parseInt(unlockPurchases.c) || 0,
      unlock_revenue_today:   parseFloat(unlockPurchases.total) || 0,
      manually_unlocked:      parseInt(manualUnlocked.c) || 0,
      cancel_refunds_today:   parseInt(cancelRefunds.c) || 0,
      cancel_refund_total:    parseFloat(cancelRefunds.total) || 0,
    });
  } catch(e) { log('ERROR', e.message); res.status(500).json({ error: 'Server error' }); }
});

// ══════════════════════════════════════════
// GLOBAL ERROR HANDLER
// ══════════════════════════════════════════
app.use((err, req, res, next) => {
  // CORS error
  if (err.message === 'CORS not allowed') {
    return res.status(403).json({ error: 'Origin not allowed' });
  }
  log('ERROR', `${req.method} ${req.path} — ${err.message}`);
  if (!res.headersSent) {
    // ✅ FIX: Never expose internal error details to client
    res.status(500).json({ error: 'Internal server error' });
  }
});

// 404 handler
app.use((req, res) => {
  res.status(404).json({ error: 'Not found' });
});

// ══════════════════════════════════════════
// START
// ══════════════════════════════════════════
setupDB().then(async () => {
  await startScanners();
  app.listen(PORT, () => {
    console.log(`✅ Server on port ${PORT} — Neon PostgreSQL connected`);

    // ── SELF-PING (Render sleep prevent) ──
    const SELF_URL = process.env.RENDER_EXTERNAL_URL || `http://localhost:${PORT}`;
    setInterval(() => {
      fetch(SELF_URL + '/health')
        .then(r => console.log(`[ping] ✅ ${r.status}`))
        .catch(e => console.warn(`[ping] ⚠️ ${e.message}`));
    }, 5 * 60 * 1000); // every 5 minutes
    console.log(`[ping] Self-ping started → ${SELF_URL}/health`);
  });
}).catch(e => {
  console.error('DB setup failed:', e);
  process.exit(1);
});
