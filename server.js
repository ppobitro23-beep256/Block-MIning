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
      expires_at TIMESTAMP DEFAULT (NOW() + INTERVAL '30 minutes')
    )
  `);
  await db.run(`CREATE UNIQUE INDEX IF NOT EXISTS idx_auto_dep_txhash ON auto_deposits (tx_hash) WHERE tx_hash IS NOT NULL`);
  await db.run(`CREATE INDEX IF NOT EXISTS idx_auto_dep_user   ON auto_deposits (user_id)`);
  await db.run(`CREATE INDEX IF NOT EXISTS idx_auto_dep_status ON auto_deposits (status, expires_at)`);
  await db.run(`CREATE INDEX IF NOT EXISTS idx_tx_user_type    ON transactions (user_id, type, status)`);

  // Default settings
  const defaults = {
    withdraw_fee_pct: '0', withdraw_min: '2', withdraw_max: '10000',
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

  // cancel_refund migration removed — reinvest_credit deprecated
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
// Fixed referral commission rates for ALL users — VIP system removed
const FIXED_RATES = [12, 5, 3, 1, 1, 1, 1]; // L1-L7
const FIXED_MAX_LEVELS = 7;
// computeVipLevel removed — VIP system deprecatednst express  = require('express');
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
      expires_at TIMESTAMP DEFAULT (NOW() + INTERVAL '30 minutes')
    )
  `);
  await db.run(`CREATE UNIQUE INDEX IF NOT EXISTS idx_auto_dep_txhash ON auto_deposits (tx_hash) WHERE tx_hash IS NOT NULL`);
  await db.run(`CREATE INDEX IF NOT EXISTS idx_auto_dep_user   ON auto_deposits (user_id)`);
  await db.run(`CREATE INDEX IF NOT EXISTS idx_auto_dep_status ON auto_deposits (status, expires_at)`);
  await db.run(`CREATE INDEX IF NOT EXISTS idx_tx_user_type    ON transactions (user_id, type, status)`);

  // Default settings
  const defaults = {
    withdraw_fee_pct: '0', withdraw_min: '2', withdraw_max: '10000',
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

  // cancel_refund migration removed — reinvest_credit deprecated
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

// VIP system removed — computeVipLevel deprecated

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
  // VIP system removed — all users get fixed rates
  return {
    vip:       { name: 'Member', rates: FIXED_RATES, maxLevels: FIXED_MAX_LEVELS },
    activeRefs: 0,
    teamDep:   0,
    progress:  null,
    next_vip:  null
  };
}


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

    // Check and deduct from balance only
    const user = await db.one(`SELECT balance FROM users WHERE id=$1`, [u.id]);
    const bal = parseFloat(user?.balance || 0);

    if (bal < amount)
      return res.status(400).json({
        error: 'Insufficient balance.',
        balance: bal,
        required: amount
      });

    await db.run(`UPDATE users SET balance=balance-$1 WHERE id=$2`, [amount, u.id]);

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
      if (!buyer.is_active_ref && buyer.referred_by && buyer.id !== buyer.referred_by) {
        await db.run(`UPDATE users SET is_active_ref=TRUE WHERE id=$1`, [u.id]);
        log('REF', `User ${u.id} marked as active referral (mining boost) of ${buyer.referred_by}`);
      }

      // Walk up referral tree — fixed rates for all users (VIP removed)
      let currentId = u.id;
      for (let lvl = 0; lvl < FIXED_MAX_LEVELS; lvl++) {
        const row = await db.one(`SELECT referred_by, is_banned FROM users WHERE id=$1`, [currentId]);
        if (!row || !row.referred_by) break;
        const referrerId = row.referred_by;
        if (row.is_banned) { currentId = referrerId; continue; }

        const pct = (FIXED_RATES[lvl] || 0) / 100;
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
        log('COMM', `[BOOST] L${lvl+1} ${FIXED_RATES[lvl]}% $${comm} → user ${referrerId}`);
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
    const maxLvl = FIXED_MAX_LEVELS;

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
  // ✅ FIX: expanded from 5 → 99 possible suffix values (0.01–0.99)
  // This dramatically reduces collision chance when many deposits are pending
  for (let i = 0; i < 99; i++) {
    const dec  = (Math.floor(Math.random() * 99) + 1); // 1–99 cents (0.01–0.99)
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
  // VIP system removed — return fixed rates for all users
  res.json({
    vip_name:   'Member',
    vip_rates:  FIXED_RATES,
    max_levels: FIXED_MAX_LEVELS,
    next_vip:   null,
    next_progress: null,
  });
});

// GET /api/team-deposit — paginated, searchable, level-filtered team deposit
// Query params: level (1-7), page (default 1), limit (default 15), search (username/name/uid)
app.get('/api/team-deposit', userAuth, async (req, res) => {
  try {
    const u       = req.tgUser;
    const maxLvl = FIXED_MAX_LEVELS;

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
    const maxLevels = FIXED_MAX_LEVELS;

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
    const VALID_VIP_LEVELS = ['none','Member']; // VIP tiers removed
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
    const user = await db.one(`SELECT withdraw_address, address_locked FROM users WHERE id=$1`, [u.id]);
    if (!user.withdraw_address || !user.address_locked) {
      return res.status(400).json({ error: 'Bind your withdrawal address first' });
    }

    // 2b. Active plan check
    const activePlanCheck = await db.one(
      `SELECT id FROM investments WHERE user_id=$1 AND status='active' LIMIT 1`, [u.id]
    );
    if (!activePlanCheck) {
      return res.status(400).json({ error: '⚠️ Withdrawal requires at least 1 active investment plan.' });
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

    // Deduct fee and log
    await db.run(`UPDATE users SET balance=balance-$1 WHERE id=$2`, [requiredFee, u.id]);
    await db.run(
      `INSERT INTO plan_unlock_logs (user_id, plan_id, plan_name, unlock_type, fee_paid) VALUES ($1,$2,$3,'paid',$4)`,
      [u.id, plan.id, plan.name, requiredFee]
    );

    log('PLAN_UNLOCK', `User ${u.id} paid $${requiredFee} to unlock plan ${plan.name}`);
    res.json({ success: true, fee_paid: requiredFee, plan_id: plan.id });

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
