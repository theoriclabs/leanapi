// LeanDB's migration gate at app startup, on a real old SQLite database.
// Usage: node scripts/ddd_migration_acceptance.mjs [WORKSPACE]  (default: this repository)
import assert from 'node:assert/strict';
import {spawn, spawnSync} from 'node:child_process';
import {createServer} from 'node:net';
import {mkdir} from 'node:fs/promises';
import {existsSync} from 'node:fs';
import {resolve, join} from 'node:path';
import {randomBytes} from 'node:crypto';

const workspace = resolve(process.argv[2] ?? '.');
const bin = join(workspace, '.lake/build/bin/leanapi_apps');
const run = resolve('.lake/ddd-migration-acceptance', randomBytes(8).toString('hex'));
await mkdir(run, {recursive: true});
const database = join(run, 'evolving.sqlite');
const socket = createServer();
await new Promise(done => socket.listen(0, '127.0.0.1', done));
const port = socket.address().port;
await new Promise(done => socket.close(done));
const origin = `http://127.0.0.1:${port}`;
const env = {...process.env, LEANAPP_DATABASE: database, LEANAPP_PORT: String(port)};
let checks = 0;
const eq = (actual, expected, label) => {checks++; assert.deepEqual(actual, expected, label);};
const check = (condition, label) => {checks++; assert.ok(condition, label);};

const command = (...args) => spawnSync(bin, ['evolving', ...args], {cwd: run, env, encoding: 'utf8'});
function sql(statement, parameters = []) {
  const result = spawnSync('python3', ['-c',
    'import sqlite3,json,sys\nc=sqlite3.connect(sys.argv[1]); q=json.loads(sys.argv[2]); print(json.dumps(c.execute(q[0],q[1]).fetchall()))',
    database, JSON.stringify([statement, parameters])], {encoding: 'utf8'});
  if (result.status !== 0) throw new Error(`sqlite: ${result.stderr}`);
  return JSON.parse(result.stdout);
}
const columns = table => sql(`PRAGMA table_info("${table}")`).map(row => row[1]);

// Start a version; resolve when it is ready, or with its exit code if it stops first.
async function start(version) {
  const server = spawn(bin, ['evolving', version], {cwd: run, env, stdio: ['ignore', 'pipe', 'pipe']});
  let out = '', err = '';
  server.stdout.on('data', bytes => {out += bytes;});
  server.stderr.on('data', bytes => {err += bytes;});
  const exited = new Promise(done => server.once('exit', code => done(code)));
  const deadline = performance.now() + 15000;  // awake time: a system sleep does not count
  while (!(out + err).includes('leanapi.ready')) {
    if (server.exitCode !== null) return {exitCode: await exited, out, err};
    if (performance.now() > deadline) throw new Error(`${version} readiness timeout\n${out}\n${err}`);
    await new Promise(done => setTimeout(done, 20));
  }
  return {server, out: () => out, err: () => err,
    stop: async () => {server.kill('SIGTERM'); await exited;}};
}
async function post(path, body, headers = {}) {
  const response = await fetch(origin + path, {method: 'POST', body: JSON.stringify(body),
    headers: {'content-type': 'application/json', ...headers}});
  return {status: response.status, body: await response.json()};
}
const get = async path => {
  const response = await fetch(origin + path);
  return {status: response.status, body: await response.json()};
};
const token = {accept: 'application/vnd.leanapp.token'};
const bearer = value => ({authorization: `Bearer ${value}`});
const password = 'correct horse battery staple';

// 1. Read-only check on a missing file creates nothing.
let result = command('v1', 'migrate', '--check');
eq(result.status, 0, 'migrate --check on a missing database exits 0');
check(result.stdout.startsWith('status: fresh'), 'fresh status line');
check(!existsSync(database), 'migrate --check creates no file');

// 2. The first deployment: real rows and a session.
let app = await start('v1');
check(app.server, 'v1 starts on a fresh database');
const asha = await post('/sign-up', {name: 'Asha', email: 'asha@example.com', password}, token);
eq(asha.status, 200, 'v1 token sign-up');
const ashaToken = asha.body.ok.token;
const party = await post('/parties', {title: 'Housewarming', date: '2096-10-02T07:06:40Z'}, bearer(ashaToken));
eq(party.status, 200, 'v1 host with bearer');
const key = party.body.ok;
await post('/parties', {title: 'Picnic', date: {tag: 'int', value: '4000000001'}}, bearer(ashaToken));  // the old time form is still accepted
eq((await get(`/parties/${key}`)).body.ok, 'Housewarming', 'v1 serves the party');
await app.stop();
check(!columns('party').includes('guestList'), 'old database has no guestList column');
const before = sql('SELECT id, host, title, date FROM party ORDER BY id');
const fingerprint = () => sql("SELECT name FROM sqlite_master WHERE name LIKE '_leandb%' ORDER BY name");
const metaBefore = fingerprint();

// 3. The changed schema without its migration: refused, nothing changed.
result = command('v2-unmigrated', 'migrate', '--check');
eq(result.status, 3, 'migrate --check refuses an uncovered change with exit 3');
check(result.stdout.startsWith('status: refused') && result.stdout.includes('Party.guestList'),
  'refusal names Party.guestList');
result = command('v2-unmigrated', 'migrate');
eq(result.status, 3, 'migrate refuses an uncovered change with exit 3');
const refused = await start('v2-unmigrated');
eq(refused.exitCode, 3, 'the app refuses to start on an uncovered schema change');
check(refused.err.includes('refused') && refused.err.includes('Party.guestList'), 'startup prints the gate message');
check(!(refused.out + refused.err).includes('leanapi.ready'), 'nothing was served');
check(!columns('party').includes('guestList'), 'refusal leaves the table unchanged');
eq(sql('SELECT id, host, title, date FROM party ORDER BY id'), before, 'refusal leaves the rows unchanged');
eq(fingerprint(), metaBefore, 'refusal records nothing');
eq(command('v1', 'migrate', '--check').stdout.split('\n')[0],
  'status: up to date — the database is at the compiled schema.', 'the old build still matches after a refusal');

// 4. With the migration listed in app%: pending, then applied at startup.
result = command('v2', 'migrate', '--check');
eq(result.status, 0, 'migrate --check exits 0 for a covered change');
check(result.stdout.startsWith('status: pending'), 'covered change is pending');
eq(columns('party').includes('guestList'), false, 'migrate --check is read-only');
app = await start('v2');
check(app.server, 'the app starts once the migration exists');
check(app.out().includes('status: migrated'), 'startup reports the applied migration');
eq((await get(`/parties/${key}/guest-list`)).body.ok, 'everyone', 'existing party backfilled to everyone');
eq((await get(`/parties/${key}`)).body.ok, 'Housewarming', 'existing fields kept');
eq(sql('SELECT id, host, title, date FROM party ORDER BY id'), before, 'every old row and value kept');
eq(sql('SELECT DISTINCT guestList FROM party').length, 1, 'every row has the fill');
const after = await post('/parties', {title: 'Dinner', date: '2096-10-02T07:06:42Z'}, bearer(ashaToken));
eq(after.status, 200, 'a session issued before the migration still works');
eq(after.body.ok, 3, 'the id counter carried across the rebuild');
eq(sql('SELECT name FROM _leandb_applied_migrations').map(row => row[0]), ['addGuestList'], 'migration recorded by name');
await app.stop();

// 5. Up to date afterwards; the old build now refuses the newer database.
result = command('v2', 'migrate', '--check');
eq([result.status, result.stdout.split('\n')[0]], [0, 'status: up to date — the database is at the compiled schema.'], 'up to date after startup');
eq(command('v2', 'migrate').status, 0, 'migrate is idempotent');
app = await start('v2');
check(app.server && !app.out().includes('status: migrated'), 'restart applies nothing');
await app.stop();
const old = await start('v1');
eq(old.exitCode, 3, 'the old build refuses a database that dropped its field');
eq(command('v2', 'bogus').status, 2, 'unknown arguments are refused');
console.log(`PASS: ${checks} migration gate checks on a real database; run ${run}`);
