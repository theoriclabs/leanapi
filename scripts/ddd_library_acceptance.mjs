// Generality fixture: the library-loans app over real curl and SQLite. The first deployment
// (v1), a schema change refused without its migration, then applied at startup (v2), a
// curl transcript of the current app in the {"ok"}/{"error"} envelope. (Its pages are LeanReact's.)
// Usage: node scripts/ddd_library_acceptance.mjs [WORKSPACE] [--save PATH]  (default: this repository)
import assert from 'node:assert/strict';
import {spawn, spawnSync} from 'node:child_process';
import {createServer} from 'node:net';
import {mkdir, writeFile} from 'node:fs/promises';
import {existsSync} from 'node:fs';
import {resolve, join} from 'node:path';
import {randomBytes} from 'node:crypto';

const workspace = resolve(process.argv[2] && !process.argv[2].startsWith('--') ? process.argv[2] : '.');
const option = name => process.argv.indexOf(name) > 0 ? resolve(process.argv[process.argv.indexOf(name) + 1]) : null;
const save = option('--save');
const bin = join(workspace, '.lake/build/bin/leanapi_apps');
const run = resolve('.lake/ddd-library-acceptance', randomBytes(8).toString('hex'));
await mkdir(run, {recursive: true});
const database = join(run, 'library.sqlite');
const socket = createServer();
await new Promise(done => socket.listen(0, '127.0.0.1', done));
const port = socket.address().port;
await new Promise(done => socket.close(done));
const origin = `http://127.0.0.1:${port}`;
// The binary finds its own browser bundle (no LEANAPP_BROWSER_DIR).
const {LEANAPP_BROWSER_DIR, ...inherited} = process.env;
const env = {...inherited, LEANAPP_DATABASE: database, LEANAPP_PORT: String(port)};
let checks = 0;
const eq = (actual, expected, label) => {checks++; assert.deepEqual(actual, expected, label);};
const check = (condition, label) => {checks++; assert.ok(condition, label);};
const command = (...args) => spawnSync(bin, ['library', ...args], {cwd: run, env, encoding: 'utf8'});
function sql(statement) {
  const result = spawnSync('python3', ['-c',
    'import sqlite3,json,sys\nc=sqlite3.connect(sys.argv[1]); r=c.execute(sys.argv[2]).fetchall(); c.commit(); print(json.dumps(r))',
    database, statement], {encoding: 'utf8'});
  if (result.status !== 0) throw new Error(`sqlite: ${result.stderr}`);
  return JSON.parse(result.stdout);
}
async function start(version) {
  const server = spawn(bin, ['library', version], {cwd: run, env, stdio: ['ignore', 'pipe', 'pipe']});
  let out = '', err = '';
  server.stdout.on('data', bytes => {out += bytes;});
  server.stderr.on('data', bytes => {err += bytes;});
  const exited = new Promise(done => server.once('exit', done));
  while (!(out + err).includes('leanapi.ready')) {
    if (server.exitCode !== null) return {exitCode: await exited, out, err};
    await new Promise(done => setTimeout(done, 20));
  }
  return {out: () => out, stop: async () => {server.kill('SIGTERM'); await exited;}};
}
const lines = [];
const tokens = {};
const shown = text => Object.entries(tokens).reduce((acc, [name, value]) => acc.replaceAll(value, `$${name}`), text)
  .replaceAll(origin, 'localhost:8080');
function curl(record, ...args) {
  const result = spawnSync('curl', ['-s', '-w', '\n%{http_code}', ...args], {encoding: 'utf8'});
  if (result.status !== 0) throw new Error(`curl failed: ${result.stderr}`);
  const at = result.stdout.lastIndexOf('\n');
  const body = result.stdout.slice(0, at), status = Number(result.stdout.slice(at + 1));
  if (record) {
    const quoted = args.map(arg => /^[A-Za-z0-9_\-:/.=]+$/.test(arg) ? arg : (arg.startsWith('Authorization:') ? `"${arg}"` : `'${arg}'`));
    lines.push(`$ curl ${quoted.join(' ')}`, body);
  }
  return {status, body, json: body ? JSON.parse(body) : null};
}
const url = path => origin + path;
const password = 'correct horse battery staple';
const token = ['-H', 'Accept: application/vnd.leanapp.token'];
const bearer = name => ['-H', `Authorization: Bearer ${tokens[name]}`];

// 1. First deployment: members, a librarian, a book.
eq(command('v1', 'migrate', '--check').status, 0, 'migrate --check on a missing database');
check(!existsSync(database), 'migrate --check creates nothing');
let app = await start('v1');
tokens.ADA = curl(false, '-X', 'POST', url('/join'), ...token, '-d', JSON.stringify({name: 'Ada', email: 'ada@example.com', password})).json.ok.token;
tokens.BEA = curl(false, '-X', 'POST', url('/join'), ...token, '-d', JSON.stringify({name: 'Bea', email: 'bea@example.com', password})).json.ok.token;
sql("UPDATE member SET librarian = 1 WHERE email = 'ada@example.com'");
eq(curl(false, '-X', 'POST', url('/books'), ...bearer('BEA'), '-d', JSON.stringify({title: 'Dune'})).json, {error: 'librarianOnly'}, 'v1: librarian-only rule');
eq(curl(false, '-X', 'POST', url('/books'), ...bearer('ADA'), '-d', JSON.stringify({title: 'Dune'})).json, {ok: 1}, 'v1: a librarian shelves a book');
await app.stop();

// 2. The new schema (Book.shelf) without its migration is refused; with it, applied at startup.
const refused = await start('v2-unmigrated');
eq(refused.exitCode, 3, 'an uncovered schema change refuses to start');
check(refused.err.includes('Book.shelf'), 'the refusal names Book.shelf');
check(command('v2', 'migrate', '--check').stdout.startsWith('status: pending'), 'covered change is pending');
app = await start('v2');
check(app.out().includes('status: migrated'), 'startup applies addShelf');

// 3. The current app, as a transcript.
try {
  const page = curl(true, url('/books/1'));
  eq(page.json, {ok: {borrowers: [], shelf: 'general', title: 'Dune'}}, 'the old book is on the general shelf (a bare string)');
  const signIn = curl(true, '-X', 'POST', url('/sign-in'), ...token, '-d', JSON.stringify({email: 'bea@example.com', password}));
  tokens.BEA2 = signIn.json.ok.token;
  lines[lines.length - 1] = shown(signIn.body);
  eq(signIn.json.ok.profile, 2, 'sign-in: profile ref 2');
  eq(curl(true, '-X', 'POST', url('/books/1/loans'), ...bearer('BEA2')).json, {ok: 1}, 'borrow');
  eq(curl(true, '-X', 'POST', url('/books/1/loans'), ...bearer('BEA2')).json, {error: 'alreadyBorrowed'}, 'the composite unique as a typed error');
  eq(curl(true, url('/books/1')).json.ok.borrowers, [{name: 'Bea'}], 'the loan-history join');
  eq(curl(true, '-X', 'POST', url('/books'), ...bearer('BEA2'), '-d', JSON.stringify({title: 'Emma', shelf: 'reference'})).json,
    {error: 'librarianOnly'}, 'librarian-only rule');
  eq(curl(true, '-X', 'POST', url('/books'), ...bearer('ADA'), '-d', JSON.stringify({title: 'Emma', shelf: 'reference'})).json,
    {ok: 2}, 'a session from before the migration still works');
  eq(curl(true, '-X', 'POST', url('/books/1/loans')).json, {error: 'unauthorized'}, 'no credential');
  eq(curl(true, '-X', 'POST', url('/join'), ...token, '-d', JSON.stringify({name: 'Ada again', email: 'ADA@example.com', password})).json,
    {error: 'emailTaken'}, 'duplicate email');
  const unknown = curl(false, '-X', 'POST', url('/sign-in'), ...token, '-d', JSON.stringify({email: 'nobody@example.com', password}));
  const wrong = curl(false, '-X', 'POST', url('/sign-in'), ...token, '-d', JSON.stringify({email: 'bea@example.com', password: 'wrong password but long'}));
  eq([unknown.status, unknown.body], [wrong.status, wrong.body], 'unknown email and wrong password: identical bytes');
  eq(unknown.json, {error: 'wrongEmailOrPassword'}, 'sign-in failure');
  eq(curl(false, '-X', 'POST', url('/me'), ...bearer('BEA2'), '-d', JSON.stringify({changes: {name: 'Beatrice'}})).json, {ok: null},
    'editProfile through Member.Changes');
  eq(curl(true, '-X', 'POST', url('/books/1/remove'), ...bearer('ADA')).json, {ok: null}, 'remove a book');
  eq(sql('SELECT count(*) FROM loan WHERE book = 1'), [[0]], 'its loans are gone (cascade)');
  eq(sql('SELECT count(*) FROM member'), [[2]], 'members stay');
  const gone = curl(true, url('/books/1'));
  eq([gone.status, gone.json], [422, {error: 'notFound'}], 'a removed book: the domain notFound at 422');
  const route = curl(false, url('/nowhere'));
  eq([route.status, route.json], [404, {error: 'notFound'}], 'an unknown route: the framework notFound at 404');
  eq(curl(false, url('/books/2'), '-H', 'Authorization: Bearer nope').status, 401, 'an invalid bearer never reads anonymously');
  const text = lines.map(shown).join('\n') + '\n';
  await writeFile(join(run, 'transcript.txt'), text);
  if (save) await writeFile(save, text);

  console.log(`PASS: ${checks} library checks (migration, envelope, auth, rules); run ${run}`);
} finally {
  await app.stop();
}
