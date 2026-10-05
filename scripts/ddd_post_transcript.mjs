// The post's curl transcript, with real curl, in the {"ok"}/{"error"} envelope. Tokens are
// shown as $ASHA/$BEN. By default it runs the post-shaped fixture (`leanapi_native_checks post
// serve`); `--exe leanapi_partiful_api` runs the post's own api (`partiful_v2/Domain.lean`). The server clock is pinned to
// 2026-10-01T00:00:00Z (LEANAPP_CLOCK_FILE) so the post's party date stays in the future.
// Writes RUN/transcript.txt and, with --save PATH, a copy at PATH.
// Usage: node scripts/ddd_post_transcript.mjs [WORKSPACE] [--exe NAME] [--save PATH]  (default: this repository)
import assert from 'node:assert/strict';
import {spawn, spawnSync} from 'node:child_process';
import {createServer} from 'node:net';
import {mkdir, writeFile} from 'node:fs/promises';
import {resolve, join} from 'node:path';
import {randomBytes} from 'node:crypto';

const workspace = resolve(process.argv[2] && !process.argv[2].startsWith('--') ? process.argv[2] : '.');
const option = name => process.argv.indexOf(name) > 0 ? process.argv[process.argv.indexOf(name) + 1] : null;
const save = option('--save') ? resolve(option('--save')) : null;
const exe = option('--exe') ?? 'leanapi_native_checks';
const run = resolve('.lake/ddd-post-transcript', randomBytes(8).toString('hex'));
await mkdir(run, {recursive: true});
const clock = join(run, 'clock');
await writeFile(clock, String(Date.parse('2026-10-01T00:00:00Z') / 1000));
const socket = createServer();
await new Promise(done => socket.listen(0, '127.0.0.1', done));
const port = socket.address().port;
await new Promise(done => socket.close(done));
const origin = `http://127.0.0.1:${port}`;
const {LEANAPP_BROWSER_DIR, ...inherited} = process.env;
const server = spawn(join(workspace, '.lake/build/bin', exe), exe === 'leanapi_native_checks' ? ['post', 'serve'] : [], {cwd: run,
  env: {...inherited, LEANAPP_PORT: String(port), LEANAPP_DATABASE: join(run, 'post.sqlite'), LEANAPP_CLOCK_FILE: clock},
  stdio: ['ignore', 'pipe', 'pipe']});
let log = '';
server.stdout.on('data', bytes => {log += bytes;});
server.stderr.on('data', bytes => {log += bytes;});
while (!log.includes('leanapi.ready')) {
  if (server.exitCode !== null) throw new Error(`server exited: ${log}`);
  await new Promise(done => setTimeout(done, 20));
}
let checks = 0;
const eq = (actual, expected, label) => {checks++; assert.deepEqual(actual, expected, label);};
const lines = [];
const tokens = {};
const shown = text => Object.entries(tokens).reduce((acc, [name, value]) => acc.replaceAll(value, `$${name}`), text)
  .replaceAll(origin, 'localhost:8080');
function curl(...args) {
  const result = spawnSync('curl', ['-s', '-w', '\n%{http_code}', ...args], {encoding: 'utf8'});
  if (result.status !== 0) throw new Error(`curl failed: ${result.stderr}`);
  const at = result.stdout.lastIndexOf('\n');
  const body = result.stdout.slice(0, at), status = Number(result.stdout.slice(at + 1));
  const quoted = args.map(arg => /^[A-Za-z0-9_\-:/.=]+$/.test(arg) ? arg : (arg.startsWith('Authorization:') ? `"${arg}"` : `'${arg}'`));
  lines.push(shown(`$ curl ${quoted.join(' ')}`), shown(body));
  return {status, body, json: JSON.parse(body)};
}
const url = path => origin + path;
const password = 'correct horse battery staple';
const token = ['-H', 'Accept: application/vnd.leanapp.token'];
try {
  const asha = curl('-X', 'POST', url('/sign-up'), ...token, '-d', JSON.stringify({name: 'Asha', email: 'asha@example.com', password}));
  tokens.ASHA = asha.json.ok.token;
  lines[lines.length - 1] = shown(asha.body);
  eq([asha.status, asha.json.ok.profile], [200, 1], 'sign-up');
  const ben = curl('-X', 'POST', url('/sign-up'), ...token, '-d', JSON.stringify({name: 'Ben', email: 'ben@example.com', password}));
  tokens.BEN = ben.json.ok.token;
  lines[lines.length - 1] = shown(ben.body);
  const party = curl('-X', 'POST', url('/parties'), '-H', `Authorization: Bearer ${tokens.ASHA}`, '-d', JSON.stringify(
    {title: 'Housewarming', description: 'Bring a plant', date: '2026-10-17T19:00:00Z', guestList: 'everyone'}));
  eq([party.status, party.json], [200, {ok: 1}], 'host');
  const rsvp = curl('-X', 'POST', url('/parties/1/rsvp'), '-H', `Authorization: Bearer ${tokens.BEN}`);
  eq([rsvp.status, rsvp.json], [200, {ok: null}], 'rsvp');
  const page = curl(url('/parties/1'));
  eq([page.status, page.json.ok.guests], [200, {tag: 'visible', value: {guests: [{name: 'Ben'}]}}], 'party page');
  const taken = curl('-X', 'POST', url('/sign-up'), ...token, '-d', JSON.stringify({name: 'Not Asha', email: 'asha@example.com', password}));
  eq([taken.status, taken.json], [422, {error: 'emailTaken'}], 'duplicate email');
  const anonymous = curl('-X', 'POST', url('/parties/1/rsvp'));
  eq([anonymous.status, anonymous.json], [401, {error: 'unauthorized'}], 'no credential');
  const text = lines.join('\n') + '\n';
  await writeFile(join(run, 'transcript.txt'), text);
  if (save) await writeFile(save, text);
  process.stdout.write(text);
  console.log(`PASS: ${checks} transcript checks; run ${run}`);
} finally {
  server.kill('SIGTERM');
}
