// Entities nested under entities (`app% ShopApp where api := Shop.api`, TestsNative/ShopApp.lean,
// theoriclabs/leanapi#6) over real curl and SQLite: `migrate` creates a table for the order, its
// lines (`Shop.Order.Line`), their allocations (`Shop.Order.Line.Allocation`) and the refunds, and
// none for `Shop.Legacy.Order`; nested entities are inserted and read back, a line is read through
// a refund's reference, missing references are the typed notFound, and the data survives a restart.
// Usage: node scripts/ddd_shop_acceptance.mjs [WORKSPACE]  (default: this repository)
import assert from 'node:assert/strict';
import {spawn, spawnSync} from 'node:child_process';
import {createServer} from 'node:net';
import {mkdir} from 'node:fs/promises';
import {existsSync} from 'node:fs';
import {resolve, join} from 'node:path';
import {randomBytes} from 'node:crypto';

const workspace = resolve(process.argv[2] ?? '.');
const bin = join(workspace, '.lake/build/bin/leanapi_apps');
const run = resolve('.lake/ddd-shop-acceptance', randomBytes(8).toString('hex'));
await mkdir(run, {recursive: true});
const database = join(run, 'shop.sqlite');
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
const command = (...args) => spawnSync(bin, ['shop', ...args], {cwd: run, env, encoding: 'utf8'});
function sql(statement) {
  const result = spawnSync('python3', ['-c',
    'import sqlite3,json,sys\nc=sqlite3.connect(sys.argv[1]); r=c.execute(sys.argv[2]).fetchall(); c.commit(); print(json.dumps(r))',
    database, statement], {encoding: 'utf8'});
  if (result.status !== 0) throw new Error(`sqlite: ${result.stderr}`);
  return JSON.parse(result.stdout);
}
async function start() {
  const server = spawn(bin, ['shop'], {cwd: run, env, stdio: ['ignore', 'pipe', 'pipe']});
  let out = '';
  server.stdout.on('data', bytes => {out += bytes;});
  server.stderr.on('data', bytes => {out += bytes;});
  const exited = new Promise(done => server.once('exit', done));
  const deadline = performance.now() + 15000;  // awake time: a system sleep does not count
  while (!out.includes('leanapi.ready')) {
    if (server.exitCode !== null) throw new Error(`shop exited with ${await exited}\n${out}`);
    if (performance.now() > deadline) throw new Error(`shop readiness timeout\n${out}`);
    await new Promise(done => setTimeout(done, 20));
  }
  return {out: () => out, stop: async () => {server.kill('SIGTERM'); await exited;}};
}
// Real curl, as a reader would type it: no Origin, no Content-Type.
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
const tables = () => sql("SELECT name FROM sqlite_master WHERE type = 'table' AND name NOT LIKE '\\_%' ESCAPE '\\' " +
  "AND name <> 'sqlite_sequence' ORDER BY name");
const counts = () => sql('SELECT (SELECT count(*) FROM "order"), (SELECT count(*) FROM line), ' +
  '(SELECT count(*) FROM allocation), (SELECT count(*) FROM refund)');

// 1. `migrate` creates the schema: one table per domain entity, nested ones included.
let result = command('migrate', '--check');
check(result.status === 0 && result.stdout.startsWith('status: fresh'), 'migrate --check on a missing database: fresh');
check(!existsSync(database), 'migrate --check creates nothing');
result = command('migrate');
eq(result.status, 0, `migrate creates the database\n${result.stdout}${result.stderr}`);
eq(tables(), [['allocation'], ['line'], ['order'], ['refund']],
  'a table for the order, its lines, their allocations and the refunds; none for Shop.Legacy.Order');
result = command('migrate', '--check');
check(result.status === 0 && result.stdout.startsWith('status: up to date'), 'migrate --check after migrate: up to date');
eq(command('migrate').status, 0, 'migrate is idempotent');

let app = await start();
try {
  // 2. Insert nested entities: an order, its lines, a line's allocation, and a refund of a line.
  reply(curl('-X', 'POST', url('/orders'), '-d', '{"customer":"Ada"}'), 200, {ok: 1}, 'place an order');
  reply(curl('-X', 'POST', url('/orders/1/lines'), '-d', '{"item":"Lamp","quantity":2}'), 200, {ok: 1},
    'add a line (Shop.Order.Line)');
  reply(curl('-X', 'POST', url('/orders/1/lines'), '-d', '{"item":"Desk","quantity":1}'), 200, {ok: 2}, 'add another line');
  reply(curl('-X', 'POST', url('/lines/1/allocations'), '-d', '{"warehouse":"North","quantity":2}'), 200, {ok: 1},
    'allocate a line (Shop.Order.Line.Allocation, two levels deep)');
  reply(curl('-X', 'POST', url('/lines/2/refunds'), '-d', '{"reason":"Damaged"}'), 200, {ok: 1},
    'refund a line (a top-level entity holding a Ref Order.Line)');
  // 3. Read them back.
  reply(curl(url('/orders/1')), 200, {ok: {customer: 'Ada'}}, 'GET the order');
  reply(curl(url('/lines/1')), 200, {ok: {order: 1, item: 'Lamp', quantity: 2}}, 'GET a nested line');
  reply(curl(url('/lines/2')), 200, {ok: {order: 1, item: 'Desk', quantity: 1}}, 'GET the other line');
  reply(curl(url('/allocations/1')), 200, {ok: {line: 1, warehouse: 'North', quantity: 2}}, 'GET a doubly nested allocation');
  reply(curl(url('/refunds/1')), 200, {ok: {reason: 'Damaged', item: 'Desk', quantity: 1}},
    'GET a refund reads its line through the reference');
  eq(sql('SELECT item, quantity FROM line ORDER BY id'), [['Lamp', 2], ['Desk', 1]], 'the lines are rows of table line');
  eq(sql('SELECT warehouse, quantity FROM allocation'), [['North', 2]], 'the allocation is a row of table allocation');
  eq(sql('SELECT reason FROM refund'), [['Damaged']], 'the refund is a row of table refund');
  eq(counts(), [[1, 2, 1, 1]], 'one order, two lines, one allocation, one refund');
  // 4. Missing references are the typed notFound, and change nothing.
  reply(curl('-X', 'POST', url('/orders/99/lines'), '-d', '{"item":"Lamp","quantity":1}'), 422, {error: 'notFound'},
    'a line of a missing order');
  reply(curl('-X', 'POST', url('/lines/99/allocations'), '-d', '{"warehouse":"North","quantity":1}'), 422,
    {error: 'notFound'}, 'an allocation of a missing line');
  reply(curl('-X', 'POST', url('/lines/99/refunds'), '-d', '{"reason":"Late"}'), 422, {error: 'notFound'},
    'a refund of a missing line');
  reply(curl(url('/orders/99')), 422, {error: 'notFound'}, 'GET a missing order');
  reply(curl(url('/lines/99')), 422, {error: 'notFound'}, 'GET a missing line');
  reply(curl(url('/allocations/99')), 422, {error: 'notFound'}, 'GET a missing allocation');
  reply(curl(url('/refunds/99')), 422, {error: 'notFound'}, 'GET a missing refund');
  eq(counts(), [[1, 2, 1, 1]], 'the refused requests wrote nothing');
  const manifest = curl(url('/api/manifest')).json;
  eq(manifest.operations.map(operation => operation.name),
    ['placeOrder', 'getOrder', 'addLine', 'getLine', 'allocate', 'getAllocation', 'refund', 'getRefund'],
    'the manifest lists exactly the api');
  // 5. Restart: the nested data persists and no migration runs.
  await app.stop();
  app = await start();
  check(!app.out().includes('status: migrated'), 'a current database needs no migration');
  reply(curl(url('/lines/1')), 200, {ok: {order: 1, item: 'Lamp', quantity: 2}}, 'the line persists across a restart');
  reply(curl(url('/allocations/1')), 200, {ok: {line: 1, warehouse: 'North', quantity: 2}}, 'the allocation persists');
  reply(curl(url('/refunds/1')), 200, {ok: {reason: 'Damaged', item: 'Desk', quantity: 1}},
    'the refund still reads its line');
  reply(curl('-X', 'POST', url('/lines/2/allocations'), '-d', '{"warehouse":"South","quantity":1}'), 200, {ok: 2},
    'and nested entities can still be added');
  reply(curl(url('/allocations/2')), 200, {ok: {line: 2, warehouse: 'South', quantity: 1}}, 'and read');
  eq(counts(), [[1, 2, 2, 1]], 'one more allocation');
} finally {
  await app.stop();
}
console.log(`PASS: ${checks} nested-entity app checks (curl, SQLite, migrate, restart); run ${run}`);
