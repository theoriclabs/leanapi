// The generated client for an app served with explicit routes: path templates, GET, plain
// bodies and the {"ok"}/{"error"} envelope, against the real server.
// The client's runtime is this repository's `LeanContract/Fetch.mjs` and `Codecs.mjs`.
// Usage: node scripts/ddd_client_acceptance.mjs [post | library]
import assert from 'node:assert/strict';
import {spawn, spawnSync} from 'node:child_process';
import {createServer} from 'node:net';
import {mkdir, readFile, copyFile} from 'node:fs/promises';
import {resolve, join} from 'node:path';
import {randomBytes} from 'node:crypto';
import {pathToFileURL} from 'node:url';

const workspace = resolve(new URL('..', import.meta.url).pathname);
const which = process.argv[2] ?? 'post';
const library = which === 'library';
const [exeName, appArgs] = library ? ['leanapi_apps', ['library', 'v2']] : ['leanapi_native_checks', ['post', 'serve']];
const exe = join(workspace, '.lake/build/bin', exeName);
const run = resolve('.lake/ddd-client-acceptance', randomBytes(8).toString('hex'));
const out = join(run, 'client');
await mkdir(join(out, 'runtime'), {recursive: true});
let checks = 0;
const eq = (actual, expected, label) => {checks++; assert.deepEqual(actual, expected, label);};
const check = (condition, label) => {checks++; assert.ok(condition, label);};

// 1. Emit the client (the app executable in emit mode) and stage its runtime.
const emitted = spawnSync(exe, appArgs, {cwd: run, env: {...process.env, LEANAPP_EMIT_CLIENT: out}, encoding: 'utf8'});
eq(emitted.status, 0, `client emitted: ${emitted.stderr}`);
for (const name of ['Fetch.mjs', 'Codecs.mjs']) await copyFile(join(workspace, 'LeanContract', name), join(out, 'runtime', name));

// 2. Serve the same app.
const socket = createServer();
await new Promise(done => socket.listen(0, '127.0.0.1', done));
const port = socket.address().port;
await new Promise(done => socket.close(done));
const origin = `http://127.0.0.1:${port}`;
const server = spawn(exe, appArgs, {cwd: run, env: {...process.env, LEANAPP_PORT: String(port),
  LEANAPP_DATABASE: join(run, 'app.sqlite')}, stdio: ['ignore', 'pipe', 'pipe']});
let log = '';
server.stdout.on('data', bytes => {log += bytes;});
server.stderr.on('data', bytes => {log += bytes;});
while (!log.includes('leanapi.ready')) {
  if (server.exitCode !== null) throw new Error(`server exited: ${log}`);
  await new Promise(done => setTimeout(done, 20));
}
try {
  const generated = await import(pathToFileURL(join(out, 'operations.mjs')));
  const served = await (await fetch(`${origin}/api/manifest`)).json();
  eq(generated.canonical(served), generated.canonical(generated.manifest), 'the embedded manifest is the served manifest');
  eq(JSON.parse(await readFile(join(out, 'manifest.json'), 'utf8')), served, 'manifest.json is the served manifest');
  const routes = Object.fromEntries(Object.entries(generated.operations).map(([key, op]) => [key, `${op.method} ${op.path}`]));
  const signUpPath = library ? '/join' : '/sign-up';
  // Sessions for a non-browser test client: token-mode sign-up (raw fetch), then bearer.
  const token = async (name, email) => (await (await fetch(`${origin}${signUpPath}`, {method: 'POST',
    headers: {accept: 'application/vnd.leanapp.token'}, body: JSON.stringify({name, email,
      password: 'correct horse battery staple'})})).json()).ok.token;
  const as = bearer => generated.createClient({baseURL: origin, verify: true,
    fetch: (url, init = {}) => fetch(url, {...init, headers: {...(init.headers ?? {}), authorization: `Bearer ${bearer}`}})});
  const ops = generated.operations;
  const anonymous = generated.createClient({baseURL: origin});
  if (library) {
    check(routes.bookPage === 'GET /books/:book' && routes.borrow === 'POST /books/:book/loans', 'templates and GET reach the client');
    const ada = await token('Ada', 'ada@example.com'), bea = await token('Bea', 'bea@example.com');
    spawnSync('python3', ['-c', 'import sqlite3,sys; c=sqlite3.connect(sys.argv[1]); c.execute("UPDATE member SET librarian=1 WHERE id=1"); c.commit()',
      join(run, 'app.sqlite')]);
    eq(await as(ada).call(ops.addBook.identity, {title: 'Dune', shelf: {tag: 'general', value: null}}), {ok: true, value: 1n}, 'POST plain body');
    eq(await as(bea).call(ops.borrow.identity, {book: 1n}), {ok: true, value: 1n}, 'POST template');
    const again = await as(bea).call(ops.borrow.identity, {book: 1n});
    check(!again.ok && again.error.tag === 'alreadyBorrowed', 'typed conflict as a domain error');
    const page = await anonymous.call(ops.bookPage.identity, {book: 1n});
    check(page.ok && page.value.title === 'Dune' && page.value.borrowers.length === 1, 'GET template, anonymous Option SignedIn');
    const failure = await anonymous.call(ops.borrow.identity, {book: 1n}).then(() => null, failure => failure);
    check(failure?.kind === 'unauthenticated', 'framework {"error": "unauthorized"} is a CallFailure');
  } else {
    check(routes.getParty === 'GET /parties/:party' && routes.rsvp === 'POST /parties/:party/rsvp', 'templates and GET reach the client');
    const asha = await token('Asha', 'asha@example.com'), ben = await token('Ben', 'ben@example.com');
    const hosted = await as(asha).call(ops.hostParty.identity, {title: 'Housewarming', description: 'Bring a plant',
      date: '2100-01-01T00:00:00Z', guestList: {tag: 'everyone', value: null}});
    eq(hosted, {ok: true, value: 1n}, 'POST plain body: the new party, a bigint ref');
    eq(await as(ben).call(ops.rsvp.identity, {party: 1n}), {ok: true, value: null}, 'POST template: the path field from the input');
    const page = await as(ben).call(ops.getParty.identity, {party: 1n});
    check(page.ok && page.value.title === 'Housewarming' && page.value.date === '2100-01-01T00:00:00Z' &&
      page.value.guests.tag === 'visible', 'GET template: decoded {"ok": …} with an RFC 3339 date and the guest list');
    const missing = await as(ben).call(ops.getParty.identity, {party: 99n});
    check(!missing.ok && missing.error.tag === 'notFound', 'domain error from {"error": "notFound"} at 422');
    const unauthorized = await anonymous.call(ops.rsvp.identity, {party: 1n}).then(() => null, failure => failure);
    check(unauthorized?.kind === 'unauthenticated', 'framework {"error": "unauthorized"} is a CallFailure');
  }
  console.log(`PASS: ${checks} generated-client checks against the served app; run ${run}`);
} finally {
  server.kill('SIGTERM');
}
