// Explicit routes + bearer over a real socket and SQLite, driven by real curl.
// Usage: node scripts/ddd_route_acceptance.mjs [COMMON_WORKSPACE]
import assert from 'node:assert/strict';
import {spawn, spawnSync} from 'node:child_process';
import {createServer} from 'node:net';
import {mkdir, writeFile} from 'node:fs/promises';
import {resolve, join} from 'node:path';
import {randomBytes} from 'node:crypto';

const workspace = resolve(process.argv[2] ?? '.lake/ddd-common');
const run = resolve('.lake/ddd-route-acceptance', randomBytes(8).toString('hex'));
await mkdir(run, {recursive: true});
await writeFile(join(run, 'app.mjs'), 'export {};\n');
await writeFile(join(run, 'clock'), '100');
const socket = createServer();
await new Promise(done => socket.listen(0, '127.0.0.1', done));
const port = socket.address().port;
await new Promise(done => socket.close(done));
const origin = `http://127.0.0.1:${port}`;
let checks = 0, log = '';
const eq = (actual, expected, label) => {checks++; assert.deepEqual(actual, expected, label);};
const check = (condition, label) => {checks++; assert.ok(condition, label);};

const server = spawn(join(workspace, '.lake/build/bin/domain_route_checks'), ['--serve'], {cwd: run,
  env: {...process.env, LEANAPP_PORT: String(port), LEANAPP_DATABASE: join(run, 'routes.sqlite'),
    LEANAPP_BROWSER_DIR: run, LEANAPP_CLOCK_FILE: join(run, 'clock')}, stdio: ['ignore', 'pipe', 'pipe']});
server.stdout.on('data', bytes => {log += bytes;});
server.stderr.on('data', bytes => {log += bytes;});
const deadline = performance.now() + 15000;  // awake time: a system sleep does not count
while (!log.includes('leanapi.ready')) {
  if (server.exitCode !== null) throw new Error(`route server exited ${server.exitCode}: ${log}`);
  if (performance.now() > deadline) throw new Error('route server readiness timeout');
  await new Promise(done => setTimeout(done, 20));
}

// One real curl invocation per request: status, headers and body.
function curl(...args) {
  const result = spawnSync('curl', ['-s', '-D', '-', ...args], {encoding: 'utf8'});
  if (result.status !== 0) throw new Error(`curl failed: ${result.stderr}`);
  const [head, ...rest] = result.stdout.split('\r\n\r\n');
  const lines = head.split('\r\n');
  const status = Number(lines[0].split(' ')[1]);
  const headers = lines.slice(1).map(line => [line.slice(0, line.indexOf(':')).toLowerCase(), line.slice(line.indexOf(':') + 1).trim()]);
  const text = rest.join('\r\n');
  let body = null; try { body = JSON.parse(text); } catch {}
  return {status, headers, text, body, cookies: headers.filter(([key]) => key === 'set-cookie').map(([, value]) => value)};
}
const url = path => origin + path;
const password = 'correct horse battery staple';
const token = ['-H', 'Accept: application/vnd.leanapp.token'];
const bearer = value => ['-H', `Authorization: Bearer ${value}`];

const transcript = [];
// Like the post: `$ curl …` then the body. Recorded in RUN/transcript.txt.
function say(args, result) {
  const shown = args.map(arg => /^[A-Za-z0-9_\-:/.=]+$/.test(arg) ? arg : `'${arg}'`).join(' ');
  transcript.push(`$ curl ${shown.replace(origin, 'localhost:8080').replaceAll(origin, 'localhost:8080')}`, result.text);
  return result;
}
const step = (...args) => say(args, curl(...args));

try {
  // The post's transcript, end to end, in token mode (decision 9: no Origin needed).
  const asha = step('-X', 'POST', url('/sign-up'), ...token, '-d', JSON.stringify({name: 'Asha', email: 'asha@example.com', password}));
  eq(asha.status, 200, 'transcript: token sign-up without Origin');
  eq(asha.cookies, [], 'token sign-up sets no cookie');
  const ashaToken = asha.body.ok.token;
  check(/^[A-Za-z0-9_-]{43}$/.test(ashaToken), 'raw token in the token reply');
  const ben = step('-X', 'POST', url('/sign-up'), ...token, '-d', JSON.stringify({name: 'Ben', email: 'ben@example.com', password}));
  eq(ben.status, 200, 'transcript: second token sign-up');
  const benToken = ben.body.ok.token;
  const party = step('-X', 'POST', url('/parties'), ...bearer(ashaToken),
    '-d', JSON.stringify({title: 'Housewarming', date: '1970-01-01T00:08:20Z'}));
  eq(party.status, 200, 'transcript: host a party with bearer');
  const key = party.body.ok;
  eq(party.body, {ok: 1}, 'transcript: the party is a bare integer ref');
  const rsvp = step('-X', 'POST', url(`/parties/${key}/rsvp`), ...bearer(benToken));
  eq([rsvp.status, rsvp.body], [200, {ok: null}], 'transcript: second user RSVPs with bearer, no CSRF, no Origin, no body');
  const taken = step('-X', 'POST', url('/sign-up'), ...token, '-d', JSON.stringify({name: 'Not Asha', email: 'asha@example.com', password}));
  eq([taken.status, taken.body], [422, {error: 'emailTaken'}], 'transcript: duplicate email refused');
  const anonymous = step('-X', 'POST', url(`/parties/${key}/rsvp`));
  eq([anonymous.status, anonymous.body], [401, {error: 'unauthorized'}], 'transcript: RSVP with no credential is unauthorized');
  await writeFile(join(run, 'transcript.txt'), transcript.join('\n') + '\n');
  const signIn = curl('-X', 'POST', url('/sign-in'), ...token, '-d', JSON.stringify({email: 'ben@example.com', password}));
  check(signIn.status === 200 && signIn.body.ok.token && signIn.cookies.length === 0, 'token sign-in with no Origin succeeds');
  const cookieNoOrigin = curl('-X', 'POST', url('/sign-up'), '-d', JSON.stringify({name: 'Cleo', email: 'cleo@example.com', password}));
  eq([cookieNoOrigin.status, cookieNoOrigin.cookies], [403, []], 'cookie-mode sign-up with no Origin is refused');
  const cookieWrongOrigin = curl('-X', 'POST', url('/sign-up'), '-H', 'Origin: http://evil.test',
    '-d', JSON.stringify({name: 'Cleo', email: 'cleo@example.com', password}));
  eq([cookieWrongOrigin.status, cookieWrongOrigin.cookies], [403, []], 'cookie-mode sign-up with a wrong Origin is refused');
  eq(curl('-X', 'POST', url('/sign-in'), '-H', 'Origin: http://evil.test', '-d', JSON.stringify({email: 'ben@example.com', password})).status,
    403, 'cookie-mode sign-in with a wrong Origin is refused');

  const manifest = curl(url('/api/manifest')).body;
  eq(manifest.operations.map(op => `${op.http.method} ${op.http.path}`),
    ['POST /sign-up', 'POST /sign-in', 'POST /parties', 'GET /parties/:party', 'POST /parties/:party/rsvp'], 'exact route list');
  eq(curl('-X', 'POST', url('/api/routechecks/cancel')).status, 404, 'unlisted operation not routable');
  eq(curl('-X', 'POST', url(`/parties/${key}/rsvp`), ...bearer('A'.repeat(43))).status, 401, 'invalid bearer is 401');
  const title = curl(url(`/parties/${key}`));
  eq([title.status, title.body], [200, {ok: 'Housewarming'}], 'GET reads the path parameter');
  const page = curl(url(`/parties/${key}`), '-H', 'Accept: text/html');
  check(page.status === 200 && page.text.includes('/assets/app.mjs'), 'browser navigation gets the page on the same path');
  eq(curl('-X', 'POST', url('/sign-in'), '-d', JSON.stringify({email: 'ben@example.com', password})).status, 403,
    'default sign-in needs the browser Origin');
  const browser = curl('-X', 'POST', url('/sign-in'), '-H', `Origin: ${origin}`, '-d', JSON.stringify({email: 'ben@example.com', password}));
  const session = browser.cookies.map(value => value.split(';')[0]).find(value => value.startsWith('leanapp_session='));
  check(browser.status === 200 && session && !browser.text.includes(session.split('=')[1]) && !browser.text.includes('token'),
    'default sign-in: HttpOnly cookie only, no token in the body');
  const csrf = browser.cookies.map(value => value.split(';')[0]).find(value => value.startsWith('leanapp_csrf=')).split('=')[1];
  eq(curl('-X', 'POST', url(`/parties/${key}/rsvp`), '-H', `Cookie: ${session}`, '-H', `Origin: ${origin}`).status, 403,
    'cookie request without CSRF fails');
  eq(curl('-X', 'POST', url(`/parties/${key}/rsvp`), '-H', `Cookie: ${session}`, '-H', `Origin: ${origin}`, '-H', `x-csrf-token: ${csrf}`).status, 200,
    'cookie request with CSRF and Origin succeeds');
  const both = curl('-X', 'POST', url(`/parties/${key}/rsvp`), '-H', `Cookie: ${session}`, '-H', `Origin: ${origin}`,
    '-H', `x-csrf-token: ${csrf}`, ...bearer(benToken));
  eq([both.status, both.body], [400, {error: 'badRequest'}], 'cookie and bearer together are 400');
  check(both.headers.some(([k, v]) => k === 'x-leanapp-error' && v === 'auth.ambiguous_credentials'), 'the precise code is a header');
  console.log(`PASS: ${checks} real-curl route/bearer checks; run ${run}`);
} finally {
  server.kill('SIGTERM');
}
