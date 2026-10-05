// An app with no accounts (`app% counters where api := api`, tests/CounterApp.lean) over real
// curl and SQLite: the first deployment (v1), the schema change refused without its migration
// and applied with it (v2), the {"ok"}/{"error"} bodies, a 400 for an undecodable body, POST
// without Origin, presented credentials ignored, no account tables, and restart persistence.
// Usage: node scripts/ddd_counter_acceptance.mjs COMMON_WORKSPACE
import assert from 'node:assert/strict';
import {spawn, spawnSync} from 'node:child_process';
import {createServer} from 'node:net';
import {mkdir} from 'node:fs/promises';
import {existsSync} from 'node:fs';
import {resolve, join} from 'node:path';
import {randomBytes} from 'node:crypto';

const workspace = resolve(process.argv[2] ?? '.lake/ddd-common');
const bin = join(workspace, '.lake/build/bin/domain_counter_app');
const run = resolve('.lake/ddd-counter-acceptance', randomBytes(8).toString('hex'));
await mkdir(run, {recursive: true});
const database = join(run, 'counters.sqlite');
const socket = createServer();
await new Promise(done => socket.listen(0, '127.0.0.1', done));
const port = socket.address().port;
await new Promise(done => socket.close(done));
const origin = `http://127.0.0.1:${port}`;
const {LEANAPP_BROWSER_DIR, ...inherited} = process.env;
const env = {...inherited, LEANAPP_DATABASE: database, LEANAPP_PORT: String(port)};
let checks = 0;
const eq = (actual, expected, label) => {checks++; assert.deepEqual(actual, expected, label);};
const check = (condition, label) => {checks++; assert.ok(condition, label);};
const command = (...args) => spawnSync(bin, args, {cwd: run, env, encoding: 'utf8'});
function sql(statement) {
  const result = spawnSync('python3', ['-c',
    'import sqlite3,json,sys\nc=sqlite3.connect(sys.argv[1]); r=c.execute(sys.argv[2]).fetchall(); print(json.dumps(r))',
    database, statement], {encoding: 'utf8'});
  if (result.status !== 0) throw new Error(`sqlite: ${result.stderr}`);
  return JSON.parse(result.stdout);
}
async function start(version) {
  const server = spawn(bin, [version], {cwd: run, env, stdio: ['ignore', 'pipe', 'pipe']});
  let out = '';
  server.stdout.on('data', bytes => {out += bytes;});
  server.stderr.on('data', bytes => {out += bytes;});
  const exited = new Promise(done => server.once('exit', done));
  const deadline = performance.now() + 15000;  // awake time: a system sleep does not count
  while (!out.includes('leanapi.ready')) {
    if (server.exitCode !== null) return {exitCode: await exited, out};
    if (performance.now() > deadline) throw new Error(`${version} readiness timeout\n${out}`);
    await new Promise(done => setTimeout(done, 20));
  }
  return {out: () => out, stop: async () => {server.kill('SIGTERM'); await exited;}};
}
// Real curl, as a reader of the post would type it: no Origin, no Content-Type.
function curl(...args) {
  const result = spawnSync('curl', ['-s', '-w', '\n%{http_code}', ...args], {encoding: 'utf8'});
  if (result.status !== 0) throw new Error(`curl failed: ${result.stderr}`);
  const at = result.stdout.lastIndexOf('\n');
  const body = result.stdout.slice(0, at);
  let json = null;
  try {json = JSON.parse(body);} catch {}
  return {status: Number(result.stdout.slice(at + 1)), body, json};
}
const url = path => origin + path;
const reply = (result, status, json, label) => eq([result.status, result.json], [status, json], label);

// 1. First deployment.
eq(command('v1', 'migrate', '--check').status, 0, 'migrate --check on a missing database');
check(!existsSync(database), 'migrate --check creates nothing');
let app = await start('v1');
check(app.stop, 'v1 serves');
reply(curl('-X', 'POST', url('/counters'), '-d', '{"name":"visits"}'), 200, {ok: 1}, 'v1: create, POST without Origin');
reply(curl('-X', 'POST', url('/counters'), '-d', '{"name":"visits"}'), 422, {error: 'nameTaken'}, 'v1: the unique constraint as a typed error');
await app.stop();
eq(sql("SELECT name FROM sqlite_master WHERE type = 'table' AND name NOT LIKE '\\_%' ESCAPE '\\' AND name <> 'sqlite_sequence' ORDER BY name"),
  [['counter']], 'no account tables: the schema is the domain entities only');

// 2. The new field without its migration is refused; with it, applied at startup.
const refused = await start('v2-unmigrated');
eq(refused.exitCode, 3, 'an uncovered schema change refuses to start');
check(refused.out.includes('Counter.step'), 'the refusal names Counter.step');
const pending = command('v2', 'migrate', '--check');
check(pending.status === 0 && pending.stdout.startsWith('status: pending'), 'the covered change is pending');
app = await start('v2');
check(app.out().includes('status: migrated') && app.out().includes('addStep'), 'startup applies addStep');
eq(sql('SELECT name, count, step FROM counter'), [['visits', 0, 1]], 'the old counter is backfilled with step 1');

try {
  // 3. The current api: {"ok"} and {"error"} bodies.
  reply(curl(url('/counters/1')), 200, {ok: {name: 'visits', count: 0, step: 1}}, 'GET a counter (ReadOp)');
  reply(curl('-X', 'POST', url('/counters/1/increment')), 200, {ok: 1}, 'increment, POST without Origin or body');
  reply(curl('-X', 'POST', url('/counters/1/increment')), 200, {ok: 2}, 'increment again');
  reply(curl('-X', 'POST', url('/counters'), '-d', '{"name":"laps","step":5}'), 200, {ok: 2}, 'create with a step');
  reply(curl('-X', 'POST', url('/counters/2/increment')), 200, {ok: 5}, 'the step applies');
  reply(curl('-X', 'POST', url('/counters'), '-d', '{"name":"laps","step":1}'), 422, {error: 'nameTaken'}, 'nameTaken');
  reply(curl('-X', 'POST', url('/counters/99/increment')), 422, {error: 'notFound'}, 'increment a missing counter');
  reply(curl(url('/counters/99')), 422, {error: 'notFound'}, 'GET a missing counter');
  // 4. Undecodable requests are a 400, and change nothing.
  const before = sql('SELECT count(*) FROM counter');
  reply(curl('-X', 'POST', url('/counters'), '-d', '{"name":'), 400, {error: 'badRequest'}, 'malformed JSON');
  reply(curl('-X', 'POST', url('/counters'), '-d', '{"name":7,"step":1}'), 400, {error: 'badRequest'}, 'a field of the wrong type');
  reply(curl('-X', 'POST', url('/counters'), '-d', '{"name":"x","step":1,"count":9}'), 400, {error: 'badRequest'}, 'an unknown field');
  reply(curl('-X', 'POST', url('/counters'), '-d', '{"step":1}'), 400, {error: 'badRequest'}, 'a missing field');
  reply(curl('-X', 'POST', url('/counters/abc/increment')), 400, {error: 'badRequest'}, 'a path segment that is not a reference');
  eq(sql('SELECT count(*) FROM counter'), before, 'refused requests wrote nothing');
  const decode = spawnSync('curl', ['-s', '-o', '/dev/null', '-w', '%header{x-leanapp-error}', '-X', 'POST', url('/counters'), '-d', '{'], {encoding: 'utf8'});
  eq(decode.stdout, 'request.invalid_json', 'the precise code is in x-leanapp-error');
  // 5. No accounts: presented credentials mean nothing, and no Origin or CSRF is needed.
  reply(curl('-X', 'POST', url('/counters/1/increment'), '-H', 'Authorization: Bearer not-a-session'), 200, {ok: 3},
    'an Authorization header is ignored');
  reply(curl('-X', 'POST', url('/counters/1/increment'), '-H', 'Cookie: leanapp_session=AAAA; leanapp_csrf=BBBB'), 200, {ok: 4},
    'cookies are ignored (a browser sends the host\'s cookies to every port)');
  reply(curl('-X', 'POST', url('/counters/1/increment'), '-H', 'Origin: http://elsewhere.example'), 200, {ok: 5},
    'a cross-site POST can do what any client can: there is no ambient credential');
  reply(curl(url('/counters/1'), '-H', 'Authorization: Bearer not-a-session'), 200, {ok: {name: 'visits', count: 5, step: 1}},
    'reads ignore credentials too');
  reply(curl(url('/nowhere')), 404, {error: 'notFound'}, 'an unknown route is the framework notFound at 404');
  const manifest = curl(url('/api/manifest')).json;
  eq(manifest.operations.map(operation => operation.name), ['newCounter', 'getCounter', 'increment'],
    'the manifest lists exactly the api');
  const signUp = curl('-X', 'POST', url('/sign-up'), '-d', '{"name":"a","email":"a@example.com","password":"correct horse battery"}');
  eq(signUp.status, 404, 'there is no sign-up route');
  // 6. Restart: the data persists and no migration runs again.
  await app.stop();
  app = await start('v2');
  check(!app.out().includes('status: migrated'), 'a current database needs no migration');
  reply(curl(url('/counters/1')), 200, {ok: {name: 'visits', count: 5, step: 1}}, 'counts persist across a restart');
  reply(curl(url('/counters/2')), 200, {ok: {name: 'laps', count: 5, step: 5}}, 'every counter persists');
  reply(curl('-X', 'POST', url('/counters/2/increment')), 200, {ok: 10}, 'and keeps counting');
  eq(sql('SELECT name FROM _leandb_applied_migrations'), [['addStep']], 'the migration is recorded once, by name');
  const current = command('v2', 'migrate', '--check');
  check(current.status === 0 && !current.stdout.startsWith('status: pending'), 'migrate --check: nothing to do');
  console.log(`PASS: ${checks} no-accounts app checks (curl, SQLite, migration, restart); run ${run}`);
} finally {
  await app.stop();
}
