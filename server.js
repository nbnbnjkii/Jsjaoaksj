'use strict';

/**
 * VPS backend for «Шашки Мастер».
 * The Android client uses port 8085 by default. Each authenticated room has stable roles:
 * player1 = host/white, player2 = guest/black.
 */
const http = require('http');
const fs = require('fs');
const path = require('path');
const crypto = require('crypto');
const WebSocket = require('ws');
const WebSocketServer = WebSocket.WebSocketServer || WebSocket.Server;
const url = require('url');

const PORT = Number(process.env.PORT || 8085);
const TURN_DURATION_MS = Math.max(1_000, Number(process.env.TURN_DURATION_MS || 20_000));
const SESSION_TTL_MS = 24 * 60 * 60 * 1000;
const USERS_DB_FILE = process.env.USERS_DB_FILE || path.join(__dirname, 'users_db.json');
const SCRYPT_PARAMS = { N: 16_384, r: 8, p: 1 };
const SCRYPT_KEY_LENGTH = 64;
const sessions = new Map(); // Map<token, { nickname, expiresAt }>
const usersDb = new Map(); // Map<nicknameLower, UserRecord>
const rooms = new Map(); // Map<roomCode, GameState>
const pendingInvites = new Map(); // Map<nicknameLower, Array<Invite>>

function loadUsersDb() {
  try {
    if (!fs.existsSync(USERS_DB_FILE)) return;
    const raw = fs.readFileSync(USERS_DB_FILE, 'utf8');
    const records = JSON.parse(raw);
    if (Array.isArray(records)) {
      for (const user of records) {
        if (user && user.nickname) usersDb.set(String(user.nickname).toLowerCase(), user);
      }
    }
  } catch (error) {
    console.error('Ошибка чтения users_db.json:', error.message);
  }
}

function saveUsersDb() {
  try {
    const directory = path.dirname(USERS_DB_FILE);
    fs.mkdirSync(directory, { recursive: true });
    const temporaryFile = `${USERS_DB_FILE}.tmp`;
    fs.writeFileSync(temporaryFile, JSON.stringify(Array.from(usersDb.values()), null, 2), { encoding: 'utf8', mode: 0o600 });
    fs.renameSync(temporaryFile, USERS_DB_FILE);
    try { fs.chmodSync(USERS_DB_FILE, 0o600); } catch (_error) {}
  } catch (error) {
    console.error('Ошибка сохранения users_db.json:', error.message);
  }
}

function derivePassword(password, salt) {
  return new Promise((resolve, reject) => {
    crypto.scrypt(password, salt, SCRYPT_KEY_LENGTH, SCRYPT_PARAMS, (error, derivedKey) => {
      if (error) return reject(error);
      resolve(derivedKey);
    });
  });
}

async function hashPassword(password) {
  const salt = crypto.randomBytes(16);
  const derivedKey = await derivePassword(password, salt);
  return `scrypt$${SCRYPT_PARAMS.N}$${SCRYPT_PARAMS.r}$${SCRYPT_PARAMS.p}$${salt.toString('hex')}$${derivedKey.toString('hex')}`;
}

async function verifyPassword(password, storedValue) {
  const parts = String(storedValue || '').split('$');
  if (parts.length !== 6 || parts[0] !== 'scrypt') return false;
  const [, cost, blockSize, parallelism, saltHex, expectedHex] = parts;
  if (Number(cost) !== SCRYPT_PARAMS.N || Number(blockSize) !== SCRYPT_PARAMS.r ||
      Number(parallelism) !== SCRYPT_PARAMS.p || !/^[0-9a-f]{32}$/i.test(saltHex) ||
      !/^[0-9a-f]{128}$/i.test(expectedHex)) return false;
  const expected = Buffer.from(expectedHex, 'hex');
  const actual = await derivePassword(password, Buffer.from(saltHex, 'hex'));
  return crypto.timingSafeEqual(actual, expected);
}

async function verifyAndUpgradeUserPassword(user, password) {
  if (typeof user.passwordHash === 'string') {
    return verifyPassword(password, user.passwordHash);
  }
  if (typeof user.password !== 'string') return false;
  const actualDigest = crypto.createHash('sha256').update(password, 'utf8').digest();
  const legacyDigest = crypto.createHash('sha256').update(user.password, 'utf8').digest();
  if (!crypto.timingSafeEqual(actualDigest, legacyDigest)) return false;
  user.passwordHash = await hashPassword(password);
  delete user.password;
  return true;
}

loadUsersDb();

function sendJson(res, statusCode, payload) {
  res.writeHead(statusCode, {
    'Content-Type': 'application/json; charset=utf-8',
    'Access-Control-Allow-Origin': '*',
    'Access-Control-Allow-Methods': 'GET, POST, OPTIONS',
    'Access-Control-Allow-Headers': 'Content-Type, Authorization'
  });
  res.end(JSON.stringify(payload));
}

function readJsonBody(req) {
  return new Promise((resolve) => {
    let data = '';
    req.on('data', (chunk) => {
      data += chunk;
      if (data.length > 1e6) req.destroy();
    });
    req.on('end', () => {
      if (!data) return resolve({});
      try {
        resolve(JSON.parse(data));
      } catch (_error) {
        resolve({});
      }
    });
    req.on('error', () => resolve({}));
  });
}

function bearerToken(req) {
  const match = /^Bearer\s+(\S+)$/i.exec(String(req.headers.authorization || ''));
  return match ? match[1] : null;
}

function getSession(req) {
  const token = bearerToken(req);
  if (!token) return null;
  const session = sessions.get(token);
  if (!session) return null;
  if (session.expiresAt <= Date.now()) {
    sessions.delete(token);
    return null;
  }
  return { token, nickname: session.nickname, expiresAt: session.expiresAt };
}

function requireSession(req, res) {
  const session = getSession(req);
  if (!session) {
    sendJson(res, 401, {
      ok: false,
      code: 'AUTH_REQUIRED',
      error: 'Сессия истекла. Войдите в аккаунт повторно.'
    });
    return null;
  }
  return session;
}

function createSession(user) {
  const token = crypto.randomBytes(32).toString('hex');
  sessions.set(token, { nickname: user.nickname, expiresAt: Date.now() + SESSION_TTL_MS });
  return token;
}

function normalizePlayerId(value) {
  switch (String(value || '').trim().toUpperCase()) {
    case 'PLAYER1':
    case 'HOST':
    case 'WHITE':
    case '1':
      return 'PLAYER1';
    case 'PLAYER2':
    case 'GUEST':
    case 'BLACK':
    case '2':
      return 'PLAYER2';
    default:
      return null;
  }
}

function otherPlayer(playerId) {
  return playerId === 'PLAYER1' ? 'PLAYER2' : 'PLAYER1';
}

function generateFourDigitCode() {
  for (let attempt = 0; attempt < 9_000; attempt += 1) {
    const code = String(Math.floor(1_000 + Math.random() * 9_000));
    if (!rooms.has(code)) return code;
  }
  return String(Math.floor(1_000 + Math.random() * 9_000));
}

function broadcastToRoom(room, message) {
  const raw = JSON.stringify(message);
  for (const client of room.wsClients) {
    if (client.readyState === WebSocket.OPEN) {
      try {
        client.send(raw);
      } catch (_error) {
        room.wsClients.delete(client);
      }
    }
  }
}

function roomPlayerRole(room, nickname) {
  const key = String(nickname || '').toLowerCase();
  if (key && room.hostName.toLowerCase() === key) return 'PLAYER1';
  if (key && room.guestName && room.guestName.toLowerCase() === key) return 'PLAYER2';
  return null;
}

function serializeRoom(room) {
  return {
    roomCode: room.roomCode,
    hostName: room.hostName,
    hostAvatarId: room.hostAvatarId,
    guestName: room.guestName,
    guestAvatarId: room.guestAvatarId,
    player1: { playerId: 'PLAYER1', color: 'WHITE', nickname: room.hostName, avatarId: room.hostAvatarId },
    player2: room.guestName
      ? { playerId: 'PLAYER2', color: 'BLACK', nickname: room.guestName, avatarId: room.guestAvatarId }
      : null,
    betAmount: room.betAmount,
    variant: room.variant,
    speed: room.speed,
    isPrivate: room.isPrivate,
    hostReady: room.hostReady,
    guestReady: room.guestReady,
    gameStarted: room.gameStarted,
    roundId: room.roundId,
    currentTurn: room.currentTurn,
    currentPlayerId: room.currentTurn,
    turnStartedAt: room.turnStartedAt,
    turnDeadlineAt: room.turnDeadlineAt,
    turnDurationMs: room.turnDurationMs,
    winner: room.winner,
    movesCount: room.moves.length,
    moves: room.moves,
    commands: room.commands,
    serverNow: Date.now(),
    updatedAt: room.updatedAt
  };
}

function clearTurnTimeout(room) {
  if (room.turnTimeoutHandle) {
    clearTimeout(room.turnTimeoutHandle);
    room.turnTimeoutHandle = null;
  }
}

function scheduleTurnTimeout(room) {
  clearTurnTimeout(room);
  if (!room.gameStarted || !room.turnDeadlineAt) return;
  const expectedDeadline = room.turnDeadlineAt;
  room.turnTimeoutHandle = setTimeout(() => expireTurn(room, expectedDeadline), Math.max(0, expectedDeadline - Date.now()));
  if (room.turnTimeoutHandle && typeof room.turnTimeoutHandle.unref === 'function') {
    room.turnTimeoutHandle.unref();
  }
}

function expireTurn(room, expectedDeadline = room.turnDeadlineAt) {
  if (!room.gameStarted || !room.turnDeadlineAt || room.turnDeadlineAt !== expectedDeadline) return false;
  if (Date.now() < expectedDeadline) {
    scheduleTurnTimeout(room);
    return false;
  }

  const timedOutPlayer = room.currentTurn || 'PLAYER1';
  const winner = otherPlayer(timedOutPlayer);
  const now = Date.now();
  clearTurnTimeout(room);
  room.gameStarted = false;
  room.winner = winner;
  room.turnStartedAt = null;
  room.turnDeadlineAt = null;
  room.commands.push({
    id: room.commands.length,
    command: 'TIMEOUT',
    sender: 'SERVER',
    timedOutPlayer,
    winner,
    ts: now
  });
  room.updatedAt = now;
  broadcastToRoom(room, {
    type: 'turn_timeout',
    timedOutPlayer,
    winner,
    roundId: room.roundId,
    room: serializeRoom(room)
  });
  return true;
}

function startTurn(room, now = Date.now()) {
  clearTurnTimeout(room);
  room.turnStartedAt = now;
  room.turnDeadlineAt = now + room.turnDurationMs;
  scheduleTurnTimeout(room);
}

function startMatch(room) {
  const now = Date.now();
  // A match only starts from the lobby/finished state. Repeated READY requests never reset a live board.
  if (room.gameStarted) return false;

  clearTurnTimeout(room);
  room.roundId += 1;
  room.gameStarted = true;
  room.winner = null;
  room.moves = [];
  room.commands = [];
  room.processedMoveIds = new Map();
  room.currentTurn = 'PLAYER1';
  room.roundStartedAt = now;
  room.updatedAt = now;
  startTurn(room, now);
  return true;
}

function finishMatch(room, winner = null) {
  clearTurnTimeout(room);
  room.gameStarted = false;
  room.turnStartedAt = null;
  room.turnDeadlineAt = null;
  if (winner === 'PLAYER1' || winner === 'PLAYER2') room.winner = winner;
  room.updatedAt = Date.now();
}

function validateMove(move) {
  if (!move || typeof move !== 'object') return false;
  const coordinates = ['fromX', 'fromY', 'toX', 'toY'];
  return coordinates.every((key) => Number.isInteger(Number(move[key])) && Number(move[key]) >= 0 && Number(move[key]) < 8);
}

function recordMove(room, envelope, sender) {
  if (!sender) return { statusCode: 403, body: { ok: false, error: 'Не удалось определить игрока' } };
  if (!validateMove(envelope.move)) {
    return { statusCode: 400, body: { ok: false, error: 'Некорректный ход' } };
  }

  const moveId = String(envelope.moveId || '').slice(0, 100);
  if (moveId && room.processedMoveIds.has(moveId)) {
    const previousIndex = room.processedMoveIds.get(moveId);
    const previousMove = room.moves[previousIndex];
    if (!previousMove || previousMove.sender !== sender) {
      return { statusCode: 409, body: { ok: false, error: 'Идентификатор хода уже использован' } };
    }
    return {
      statusCode: 200,
      body: { ok: true, duplicate: true, moveIndex: previousIndex, room: serializeRoom(room) }
    };
  }

  // The server is authoritative for turn order/deadlines. Starting here also covers a client
  // that submits its first move before the READY response has reached it.
  if (!room.gameStarted && !room.winner) startMatch(room);
  if (room.turnDeadlineAt && expireTurn(room)) {
    return { statusCode: 409, body: { ok: false, error: 'Время хода истекло', room: serializeRoom(room) } };
  }
  if (room.winner) {
    return { statusCode: 409, body: { ok: false, error: 'Партия завершена', room: serializeRoom(room) } };
  }
  if (sender !== room.currentTurn) {
    return {
      statusCode: 409,
      body: { ok: false, error: 'Сейчас ход другого игрока', currentTurn: room.currentTurn, room: serializeRoom(room) }
    };
  }

  const now = Date.now();
  const nextTurn = normalizePlayerId(envelope.nextTurn || envelope.move.nextTurn) || otherPlayer(sender);
  const savedMove = {
    fromX: Number(envelope.move.fromX),
    fromY: Number(envelope.move.fromY),
    toX: Number(envelope.move.toX),
    toY: Number(envelope.move.toY),
    isCapture: Boolean(envelope.move.isCapture),
    capturedX: Number.isInteger(Number(envelope.move.capturedX)) ? Number(envelope.move.capturedX) : -1,
    capturedY: Number.isInteger(Number(envelope.move.capturedY)) ? Number(envelope.move.capturedY) : -1,
    index: room.moves.length,
    sender,
    nextTurn,
    moveId: moveId || null,
    ts: now
  };
  room.moves.push(savedMove);
  if (moveId) {
    room.processedMoveIds.set(moveId, savedMove.index);
    while (room.processedMoveIds.size > 500) {
      room.processedMoveIds.delete(room.processedMoveIds.keys().next().value);
    }
  }

  const turnChanged = nextTurn !== room.currentTurn;
  room.currentTurn = nextTurn;
  if (turnChanged || !room.turnDeadlineAt) startTurn(room, now);
  room.updatedAt = now;

  const roomState = serializeRoom(room);
  broadcastToRoom(room, {
    type: 'move_made',
    move: savedMove,
    moveIndex: savedMove.index,
    sender,
    currentTurn: room.currentTurn,
    turnDeadlineAt: room.turnDeadlineAt,
    room: roomState
  });
  return {
    statusCode: 200,
    body: { ok: true, moveIndex: savedMove.index, move: savedMove, room: roomState }
  };
}

function recordCommand(room, command, sender, body = {}) {
  const now = Date.now();
  if (command === 'START_MATCH' || command === 'NEW_GAME') {
    startMatch(room);
  } else if (command === 'MATCH_FINISHED') {
    finishMatch(room, normalizePlayerId(body.winner));
  } else if (command === 'RESIGN' && sender) {
    finishMatch(room, otherPlayer(sender));
  }

  const commandRecord = {
    id: room.commands.length,
    command,
    sender: sender || 'SERVER',
    ts: now
  };
  if (command === 'MATCH_FINISHED' && normalizePlayerId(body.winner)) {
    commandRecord.winner = normalizePlayerId(body.winner);
  }
  room.commands.push(commandRecord);
  room.updatedAt = now;
  broadcastToRoom(room, {
    type: 'COMMAND',
    command,
    sender: sender || 'SERVER',
    room: serializeRoom(room)
  });
  return commandRecord;
}

function makeRoom(body, session) {
  const roomCode = generateFourDigitCode();
  const room = {
    roomCode,
    hostName: session.nickname,
    hostAvatarId: Number(body.hostAvatarId ?? 0),
    guestName: null,
    guestAvatarId: -1,
    betAmount: Number(body.betAmount || 100),
    variant: String(body.variant || 'RUSSIAN'),
    speed: String(body.speed || 'NORMAL'),
    isPrivate: Boolean(body.isPrivate),
    hostReady: false,
    guestReady: false,
    gameStarted: false,
    roundId: 0,
    roundStartedAt: 0,
    currentTurn: 'PLAYER1',
    turnStartedAt: null,
    turnDeadlineAt: null,
    turnDurationMs: TURN_DURATION_MS,
    winner: null,
    moves: [],
    commands: [],
    processedMoveIds: new Map(),
    updatedAt: Date.now(),
    wsClients: new Set(),
    turnTimeoutHandle: null
  };
  rooms.set(roomCode, room);
  return room;
}

const server = http.createServer(async (req, res) => {
  if (req.method === 'OPTIONS') return sendJson(res, 200, { ok: true });
  const parsedUrl = url.parse(req.url, true);
  const pathname = parsedUrl.pathname || '/';

  if (req.method === 'GET' && (pathname === '/' || pathname === '/health')) {
    return sendJson(res, 200, {
      ok: true,
      service: 'checkers-master-vps',
      activeRooms: rooms.size,
      registeredUsers: usersDb.size
    });
  }

  // Registration and login both issue a fresh, in-memory session token. It is never persisted.
  if (req.method === 'POST' && (pathname === '/auth/register' || pathname === '/auth/login')) {
    const body = await readJsonBody(req);
    const nickname = String(body.nickname || '').trim();
    const password = String(body.password || '').trim();
    const avatarId = Number(body.avatarId ?? 0);
    if (nickname.length < 2 || password.length < 3) {
      return sendJson(res, 400, { ok: false, error: 'Ник должен быть от 2 символов, а пароль от 3 символов' });
    }

    const key = nickname.toLowerCase();
    let user = usersDb.get(key);
    let isNewUser = false;
    if (user) {
      if (!await verifyAndUpgradeUserPassword(user, password)) {
        return sendJson(res, 403, { ok: false, error: 'Неверный пароль для этого ника' });
      }
      user.lastSeen = Date.now();
      if (avatarId >= 0 && avatarId <= 4) user.avatarId = avatarId;
    } else {
      if (pathname === '/auth/login') {
        return sendJson(res, 404, { ok: false, error: 'Аккаунт не найден. Проверьте ник или создайте аккаунт.' });
      }
      isNewUser = true;
      user = {
        nickname,
        passwordHash: await hashPassword(password),
        avatarId: Number.isInteger(avatarId) ? Math.max(0, Math.min(4, avatarId)) : 0,
        balance: 10_000,
        goldCoins: 20,
        winsCount: 0,
        rating: 15,
        createdAt: Date.now(),
        lastSeen: Date.now()
      };
      usersDb.set(key, user);
    }
    saveUsersDb();

    const sessionToken = createSession(user);
    return sendJson(res, 200, {
      ok: true,
      isNewUser,
      sessionToken,
      expiresAt: Date.now() + SESSION_TTL_MS,
      user: {
        nickname: user.nickname,
        avatarId: user.avatarId,
        balance: user.balance,
        goldCoins: user.goldCoins,
        winsCount: user.winsCount,
        rating: user.rating
      }
    });
  }

  if (req.method === 'POST' && pathname === '/auth/logout') {
    const token = bearerToken(req);
    if (token) sessions.delete(token);
    return sendJson(res, 200, { ok: true });
  }

  if (req.method === 'POST' && pathname === '/users/heartbeat') {
    const body = await readJsonBody(req);
    const session = getSession(req);
    const hasAuthorizationHeader = Boolean(req.headers.authorization);
    if (hasAuthorizationHeader && !session) {
      return sendJson(res, 401, { ok: false, code: 'AUTH_REQUIRED', error: 'Сессия истекла' });
    }
    const nickname = String(body.nickname || '').trim();
    if (session && nickname.toLowerCase() !== session.nickname.toLowerCase()) {
      return sendJson(res, 403, { ok: false, error: 'Ник не совпадает с аккаунтом сессии' });
    }
    if (nickname) {
      const user = usersDb.get(nickname.toLowerCase());
      if (user && session) {
        user.lastSeen = Date.now();
        if (typeof body.balance === 'number') user.balance = body.balance;
        if (typeof body.goldCoins === 'number') user.goldCoins = body.goldCoins;
      }
      return sendJson(res, 200, { ok: true, invites: pendingInvites.get(nickname.toLowerCase()) || [] });
    }
    return sendJson(res, 200, { ok: true, invites: [] });
  }

  if (req.method === 'GET' && pathname === '/users/search') {
    const session = requireSession(req, res);
    if (!session) return;
    const query = String(parsedUrl.query.q || '').trim().toLowerCase();
    const users = [];
    for (const user of usersDb.values()) {
      if (!query || user.nickname.toLowerCase().includes(query)) {
        users.push({
          nickname: user.nickname,
          avatarId: typeof user.avatarId === 'number' ? user.avatarId : 0,
          rating: typeof user.rating === 'number' ? user.rating : 15,
          online: Date.now() - (user.lastSeen || 0) < 120_000
        });
      }
    }
    return sendJson(res, 200, { ok: true, users: users.slice(0, 30) });
  }

  if (req.method === 'POST' && pathname === '/create') {
    const session = requireSession(req, res);
    if (!session) return;
    const body = await readJsonBody(req);
    const room = makeRoom(body, session);
    return sendJson(res, 200, { ok: true, roomCode: room.roomCode, room: serializeRoom(room) });
  }

  if (req.method === 'POST' && pathname.startsWith('/join/')) {
    const session = requireSession(req, res);
    if (!session) return;
    const code = pathname.split('/')[2] || '';
    const room = rooms.get(code);
    if (!room) return sendJson(res, 404, { ok: false, error: `Комната ${code} не найдена` });
    const body = await readJsonBody(req);
    if (session.nickname.toLowerCase() === room.hostName.toLowerCase()) {
      return sendJson(res, 409, { ok: false, error: 'Хост не может подключиться к своей комнате как игрок 2' });
    }
    if (room.guestName && room.guestName.toLowerCase() !== session.nickname.toLowerCase()) {
      return sendJson(res, 409, { ok: false, error: 'В комнате уже есть второй игрок' });
    }
    room.guestName = session.nickname;
    room.guestAvatarId = Number(body.guestAvatarId ?? 0);
    room.updatedAt = Date.now();
    const roomState = serializeRoom(room);
    broadcastToRoom(room, { type: 'PLAYER_JOINED', room: roomState });
    return sendJson(res, 200, { ok: true, room: roomState });
  }

  if (req.method === 'POST' && pathname.startsWith('/ready/')) {
    const session = requireSession(req, res);
    if (!session) return;
    const code = pathname.split('/')[2] || '';
    const room = rooms.get(code);
    if (!room) return sendJson(res, 404, { ok: false, error: 'Комната не найдена' });
    const role = roomPlayerRole(room, session.nickname);
    if (!role) return sendJson(res, 403, { ok: false, error: 'Игрок не состоит в этой комнате' });
    const body = await readJsonBody(req);
    const requestedRole = normalizePlayerId(body.role);
    if (requestedRole && requestedRole !== role) {
      return sendJson(res, 403, { ok: false, error: 'Роль игрока не совпадает с комнатой' });
    }
    if (role === 'PLAYER2') room.guestReady = true;
    else room.hostReady = true;
    if (!room.gameStarted && room.hostReady && (room.guestReady || room.guestName !== null)) {
      startMatch(room);
    }
    room.updatedAt = Date.now();
    const roomState = serializeRoom(room);
    broadcastToRoom(room, { type: 'READY_STATE', room: roomState });
    return sendJson(res, 200, { ok: true, room: roomState });
  }

  if (req.method === 'POST' && pathname.startsWith('/move/')) {
    const session = requireSession(req, res);
    if (!session) return;
    const code = pathname.split('/')[2] || '';
    const room = rooms.get(code);
    if (!room) return sendJson(res, 404, { ok: false, error: 'Комната не найдена' });
    const role = roomPlayerRole(room, session.nickname);
    if (!role) return sendJson(res, 403, { ok: false, error: 'Игрок не состоит в этой комнате' });
    const body = await readJsonBody(req);
    const requestedRole = normalizePlayerId(body.sender || body.role);
    if (requestedRole && requestedRole !== role) {
      return sendJson(res, 403, { ok: false, error: 'Нельзя отправить ход от имени другого игрока' });
    }
    const result = recordMove(room, body, role);
    return sendJson(res, result.statusCode, result.body);
  }

  if (req.method === 'POST' && pathname.startsWith('/command/')) {
    const session = requireSession(req, res);
    if (!session) return;
    const code = pathname.split('/')[2] || '';
    const room = rooms.get(code);
    if (!room) return sendJson(res, 404, { ok: false, error: 'Комната не найдена' });
    const role = roomPlayerRole(room, session.nickname);
    if (!role) return sendJson(res, 403, { ok: false, error: 'Игрок не состоит в этой комнате' });
    const body = await readJsonBody(req);
    const requestedRole = normalizePlayerId(body.sender || body.role);
    if (requestedRole && requestedRole !== role) {
      return sendJson(res, 403, { ok: false, error: 'Нельзя отправить команду от имени другого игрока' });
    }
    const command = String(body.command || '').trim();
    if (!command) return sendJson(res, 400, { ok: false, error: 'Команда не указана' });
    recordCommand(room, command, role, body);
    return sendJson(res, 200, { ok: true, room: serializeRoom(room) });
  }

  const roomPath = /^\/room\/([^/]+)(?:\/state)?$/.exec(pathname);
  if (req.method === 'GET' && roomPath) {
    const session = requireSession(req, res);
    if (!session) return;
    const code = roomPath[1];
    const room = rooms.get(code);
    if (!room) return sendJson(res, 404, { ok: false, error: 'Комната не найдена' });
    if (!roomPlayerRole(room, session.nickname)) {
      return sendJson(res, 403, { ok: false, error: 'Игрок не состоит в этой комнате' });
    }
    if (room.turnDeadlineAt) expireTurn(room);
    return sendJson(res, 200, { ok: true, room: serializeRoom(room) });
  }

  if (req.method === 'POST' && pathname === '/invite') {
    const session = requireSession(req, res);
    if (!session) return;
    const body = await readJsonBody(req);
    const toNickname = String(body.toNickname || '').trim();
    const roomCode = String(body.roomCode || '').trim();
    if (!toNickname || !roomCode) {
      return sendJson(res, 400, { ok: false, error: 'Не указан ник друга или код комнаты' });
    }
    const room = rooms.get(roomCode);
    if (!room || !roomPlayerRole(room, session.nickname)) {
      return sendJson(res, 404, { ok: false, error: 'Комната не найдена или игрок не является её участником' });
    }
    const targetKey = toNickname.toLowerCase();
    if (!usersDb.has(targetKey)) {
      return sendJson(res, 404, { ok: false, error: 'Аккаунт друга не найден' });
    }
    const invites = pendingInvites.get(targetKey) || [];
    const invite = {
      inviteId: `${Date.now()}_${crypto.randomInt(0, 1_000_000)}`,
      fromNickname: session.nickname,
      fromAvatarId: Number(body.fromAvatarId ?? 0),
      toNickname,
      roomCode,
      betAmount: Number(body.betAmount || 100),
      variant: String(body.variant || 'RUSSIAN'),
      speed: String(body.speed || 'NORMAL'),
      createdAt: Date.now()
    };
    invites.push(invite);
    pendingInvites.set(targetKey, invites);
    return sendJson(res, 200, { ok: true, invite });
  }

  if (req.method === 'POST' && pathname === '/invite/ack') {
    const session = requireSession(req, res);
    if (!session) return;
    const body = await readJsonBody(req);
    const nickname = String(body.nickname || session.nickname).trim().toLowerCase();
    if (nickname !== session.nickname.toLowerCase()) {
      return sendJson(res, 403, { ok: false, error: 'Ник не совпадает с аккаунтом сессии' });
    }
    const inviteId = String(body.inviteId || '');
    const invites = pendingInvites.get(nickname) || [];
    pendingInvites.set(nickname, invites.filter((invite) => invite.inviteId !== inviteId));
    return sendJson(res, 200, { ok: true });
  }

  return sendJson(res, 404, { ok: false, error: 'Not found' });
});

const wss = new WebSocketServer({ server, path: '/ws' });
wss.on('connection', (socket, req) => {
  const parsed = url.parse(req.url, true);
  const roomCode = String(parsed.query.room || '');
  const room = rooms.get(roomCode);
  const session = getSession(req);
  if (!session) {
    socket.send(JSON.stringify({ type: 'ERROR', code: 'AUTH_REQUIRED', message: 'Войдите в аккаунт повторно' }));
    socket.close(1008, 'Authentication required');
    return;
  }
  if (!room) {
    socket.send(JSON.stringify({ type: 'ERROR', message: 'Комната не найдена' }));
    socket.close(1008, 'Room not found');
    return;
  }

  const playerRole = roomPlayerRole(room, session.nickname);
  const requestedRole = normalizePlayerId(parsed.query.role);
  if (!playerRole || (requestedRole && requestedRole !== playerRole)) {
    socket.send(JSON.stringify({ type: 'ERROR', message: 'Игрок не состоит в этой комнате' }));
    socket.close(1008, 'Not a room player');
    return;
  }

  socket.playerRole = playerRole;
  socket.roomCode = roomCode;
  room.wsClients.add(socket);
  if (room.turnDeadlineAt) expireTurn(room);
  socket.send(JSON.stringify({ type: 'SYNC', room: serializeRoom(room) }));

  socket.on('message', (rawMessage) => {
    try {
      const data = JSON.parse(String(rawMessage));
      if (data.type === 'MOVE' && data.move) {
        const requestedSender = normalizePlayerId(data.sender);
        if (requestedSender && requestedSender !== socket.playerRole) {
          socket.send(JSON.stringify({ type: 'ERROR', message: 'Нельзя отправить ход от имени другого игрока' }));
          return;
        }
        const result = recordMove(room, data, socket.playerRole);
        if (result.statusCode !== 200) {
          socket.send(JSON.stringify({ type: 'ERROR', ...result.body }));
        }
      } else if (data.type === 'READY') {
        if (socket.playerRole === 'PLAYER2') room.guestReady = true;
        else room.hostReady = true;
        if (!room.gameStarted && room.hostReady && (room.guestReady || room.guestName !== null)) startMatch(room);
        room.updatedAt = Date.now();
        broadcastToRoom(room, { type: 'READY_STATE', room: serializeRoom(room) });
      } else if (data.type === 'COMMAND' && data.command) {
        recordCommand(room, String(data.command), socket.playerRole, data);
      }
    } catch (_error) {
      socket.send(JSON.stringify({ type: 'ERROR', message: 'Некорректное сообщение' }));
    }
  });

  socket.on('close', () => room.wsClients.delete(socket));
  socket.on('error', () => room.wsClients.delete(socket));
});

server.listen(PORT, '0.0.0.0', () => {
  console.log(`Checkers VPS Server started on 0.0.0.0:${PORT}`);
});
