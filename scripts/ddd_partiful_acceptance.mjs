// Milestone 1 Partiful (`partiful/`, executable `partiful_m1`): native HTTP, SQLite and
// compiled-browser qualification. Usage: node … WORKSPACE PEER NODE_MODULES [--exe NAME]
import assert from 'node:assert/strict';
import {spawn, spawnSync} from 'node:child_process';
import {createServer} from 'node:net';
import {mkdir, writeFile, readFile} from 'node:fs/promises';
import {resolve, join} from 'node:path';
import {pathToFileURL} from 'node:url';
import {randomBytes, createHash} from 'node:crypto';

const workspace = resolve(process.argv[2] ?? '.lake/ddd-common');
const peer = resolve(process.argv[3]);
// Installed LeanReact node_modules (Playwright); a frozen peer copy has none.
const nodeModules = resolve(process.argv[4] ?? join(peer, 'node_modules'));
// Milestone 1's `partiful/`, staged as `partiful_m1` beside milestone 2's `partiful`.
const exe = process.argv.indexOf('--exe') > 0 ? process.argv[process.argv.indexOf('--exe') + 1] : 'partiful_m1';
const run = resolve('.lake/ddd-acceptance', randomBytes(8).toString('hex'));
await mkdir(run, {recursive:true});
const database = join(run, 'partiful.sqlite'), clock = join(run, 'clock');
await writeFile(clock, '100');
const socket = createServer();
await new Promise(done => socket.listen(0, '127.0.0.1', done));
const port = socket.address().port;
await new Promise(done => socket.close(done));
const origin = `http://127.0.0.1:${port}`;
let server, serverLog = '', checks = 0, manifest;
const eq = (actual, expected, label) => {checks++; assert.deepEqual(actual, expected, label);};
const check = (condition, label) => {checks++; assert.ok(condition, label);};
const pause = ms => new Promise(done => setTimeout(done, ms));
async function start() {
  // No LEANAPP_BROWSER_DIR: the binary finds its bundle from its own build tree.
  const {LEANAPP_BROWSER_DIR, ...inherited} = process.env;
  server = spawn(join(workspace, '.lake/build/bin', exe), [], {cwd:run,
    env:{...inherited, LEANAPP_DATABASE:database, LEANAPP_CLOCK_FILE:clock,
      LEANAPP_PORT:String(port)}, stdio:['ignore','pipe','pipe']});
  server.stdout.on('data', bytes => {serverLog += bytes.toString();});
  server.stderr.on('data', bytes => {serverLog += bytes.toString();});
  const deadline = performance.now() + 15000;  // awake time: a system sleep does not count
  while (!serverLog.includes('leanapi.ready')) {
    if (server.exitCode !== null) throw new Error(`native server exited ${server.exitCode}`);
    if (performance.now() > deadline) throw new Error(`native server readiness timeout (${exe})\n${serverLog}`);
    await pause(20);
  }
  manifest = await (await fetch(`${origin}/api/manifest`)).json();
  manifest.operations = manifest.operations.map(operation => ({...operation,
    identity:{namespace:operation.namespace,name:operation.name,version:operation.version}}));
}
async function stop() {
  const process = server;
  if (process.exitCode === null) {
    const exit = new Promise(done => process.once('exit', done));
    process.kill('SIGTERM'); await exit;
  }
  server = null; serverLog = '';
}
class Jar {
  cookies = new Map();
  header() {return [...this.cookies].map(([key,value]) => `${key}=${value}`).join('; ');}
  csrf() {return this.cookies.get('leanapp_csrf');}
  receive(response) {
    for (const raw of response.headers.getSetCookie()) {
      const pair = raw.split(';')[0], index = pair.indexOf('=');
      this.cookies.set(pair.slice(0,index), pair.slice(index+1));
    }
  }
}
const op = name => {
  const operation = manifest.operations.find(operation => operation.identity.name === name);
  if (!operation) throw new Error(`missing published operation ${name}`);
  return operation;
};
async function call(name, input, jar = new Jar(), options = {}) {
  const operation = op(name);
  const headers = {'content-type':'application/json', origin,
    ...(jar.header() ? {cookie:jar.header()} : {}),
    ...(jar.csrf() ? {'x-csrf-token':jar.csrf()} : {}), ...options.headers};
  for (const key of options.omit ?? []) delete headers[key];
  const response = await fetch(origin + operation.http.path, {method:'POST', headers,
    body:JSON.stringify({operation:operation.identity, kind:operation.kind, input})});
  const text = await response.text();
  jar.receive(response);
  eq(response.headers.get('cache-control'), 'private, no-store', `${name}: no store`);
  const marker=response.headers.get('x-leanapp-auth-csrf');
  if(marker!==null)check(marker===jar.csrf(),'committed auth response marker matches readable CSRF cookie');
  return {status:response.status, body:JSON.parse(text), text, cookies:response.headers.getSetCookie(),authMarker:marker!==null};
}
function success(result) {eq(result.status, 200, 'operation succeeds'); eq(result.body.tag, 'success', 'success envelope'); return result.body.value;}
function failure(result, name, status=422) {
  eq(result.status, status, `failure status ${name}`);
  eq(result.body.tag, 'domainError', `closed domain envelope ${name}`);
  // Payload-free constructors are bare strings on the wire (decision 15 extension).
  eq(result.body.value, name, `closed domain constructor ${name}`);
  eq(result.cookies.length, 0, 'failed command has no cookies');
  eq(result.authMarker,false,'failed command has no committed auth metadata');
}
const int = value => ({tag:'int', value:String(value)});
const variant = tag => ({tag,value:null});
const password = '  Disposable fixture password 😀  ';
const signup = (name,email) => ({name,email,password});
const host = (date=200, visibility='public') => ({title:'Dinner', description:'At the table', date:int(date), visibility:variant(visibility)});
function sql(statement, parameters = []) {
  const result = spawnSync('python3', ['-c',
    'import sqlite3,json,sys\nc=sqlite3.connect(sys.argv[1]); q=json.loads(sys.argv[2]); r=c.execute(q[0],q[1]); rows=r.fetchall(); c.commit(); print(json.dumps(rows))',
    database, JSON.stringify([statement,parameters])], {encoding:'utf8'});
  if (result.status !== 0) throw new Error('SQLite acceptance query failed');
  return JSON.parse(result.stdout);
}
function counts() {return Object.fromEntries(['person','party','party_guests','credential','session'].map(table => [table,sql(`SELECT count(*) FROM "${table}"`)[0][0]]));}
function counters() {return sql('SELECT name,seq FROM sqlite_sequence ORDER BY name');}
async function holdWriter(statement = 'SELECT 1', parameters = []) {
  const held = spawn('python3',['-u','-c',
    'import sqlite3,json,sys\nc=sqlite3.connect(sys.argv[1]); c.execute("BEGIN IMMEDIATE"); q=json.loads(sys.argv[2]); c.execute(q[0],q[1]); print("held",flush=True); sys.stdin.readline(); c.commit()',
    database,JSON.stringify([statement,parameters])],{stdio:['pipe','pipe','pipe']});
  await new Promise((done,reject) => {
    held.stdout.once('data',done); held.once('error',reject);
    held.once('exit',code=>{if(code!==0)reject(new Error('writer fixture could not acquire transaction'));});
  });
  return async () => {
    const exited = new Promise(done=>held.once('exit',done));
    held.stdin.end('\n'); eq(await exited,0,'external writer commits');
  };
}

let browser;
try {
  await start();
  eq(manifest.operations.length, 8, 'exact two auth plus six business operations');
  eq(manifest.operations.map(value => value.identity.name).sort(),
    ['account.signUp','account.signIn','host','rsvp','edit','reschedule','cancel','partyPage'].sort(), 'exact allowlist');
  check(!JSON.stringify(manifest).includes('.Native.Credential') && !JSON.stringify(manifest).includes('passwordHash'), 'private storage absent from manifest');
  eq(await (await fetch(`${origin}/api/whoami`)).status, 404, 'no ninth operation');
  for (const path of ['/sign-up','/sign-in','/parties/new','/parties/1']) {
    const response = await fetch(origin+path);
    eq(response.status,200,'derived page URL '+path);
    check((await response.text()).includes('/assets/app.mjs'),'derived compiled browser entry '+path);
  }
  const alice = new Jar(), bob = new Jar(), carol = new Jar();
  const aliceRef = success(await call('account.signUp', signup('Alice',' ALICE@Example.COM '), alice));
  const initial = counts(); eq(initial, {person:1,party:0,party_guests:0,credential:1,session:1}, 'atomic signup rows');
  const party = success(await call('host', host(), alice));
  success(await call('account.signUp', signup('Bob','bob@example.com'), bob));
  success(await call('rsvp', {id:party}, bob));
  const enrolled = counts();
  success(await call('rsvp', {id:party}, bob)); eq(counts(), enrolled, 'RSVP set retry preserves all counts');
  success(await call('account.signUp', signup('Carol','carol@example.com'), carol));
  const page = async jar => success(await call('partyPage', {id:party}, jar));
  for (const visibility of ['public','attendees','private']) {
    success(await call('edit', {id:party,title:'Dinner',description:'At the table',visibility:variant(visibility)}, alice));
    for (const [label, jar, visible] of [['anonymous',new Jar(),visibility==='public'],
      ['host',alice,visibility==='public'], ['attendee',bob,visibility!=='private'],
      ['other',carol,visibility==='public']]) {
      const result = await page(jar);
      eq(result.guests, visible ? {tag:'visible',value:[{name:'Bob'}]} : 'hidden', `${visibility}/${label}`);
      check(!JSON.stringify(result.guests).includes('email') && !JSON.stringify(result.guests).includes('key'), 'names only');
    }
  }
  const hiddenBefore = await call('partyPage', {id:party}, alice);
  success(await call('rsvp', {id:party}, carol));
  const hiddenAfter = await call('partyPage', {id:party}, alice);
  eq(hiddenBefore.text, hiddenAfter.text, 'hidden bytes independent of membership/count');
  failure(await call('edit', {id:party,title:'No',description:'',visibility:variant('public')}, bob), 'hostOnly');
  failure(await call('reschedule', {id:party,date:int(99)}, bob), 'hostOnly');
  failure(await call('cancel', {id:party}, bob), 'hostOnly');
  failure(await call('reschedule', {id:party,date:int(100)}, alice), 'dateMustBeFuture');
  const beforeCollision = counts();
  const countersBeforeCollision = counters();
  failure(await call('account.signUp', signup('Duplicate','alice@EXAMPLE.com')), 'emailTaken');
  eq(counts(), beforeCollision, 'canonical signup collision has no orphan/counter changes');
  eq(counters(), countersBeforeCollision, 'canonical collision restores all counters');
  const malformed = await call('host', {...host(),title:''}, alice);
  eq(malformed.status,400,'invalid draft decode'); eq(malformed.body.tag,'decode','typed decode envelope');
  eq((await call('host', host())).status,401,'anonymous write denied');
  eq((await call('host', host(),alice,{omit:['x-csrf-token']})).status,403,'missing CSRF denied');
  eq((await call('host', host(),alice,{headers:{'x-csrf-token':'A'.repeat(43)}})).status,403,'wrong stored CSRF digest denied');
  eq((await call('host', host(),alice,{headers:{origin:'http://evil.invalid'}})).status,403,'exact Origin denied');
  eq((await call('host',{...host(),me:aliceRef},alice)).status,400,'actor cannot be supplied through JSON');
  const invalid = new Jar(); invalid.cookies.set('leanapp_session','A'.repeat(43));
  eq((await call('partyPage',{id:party},invalid)).status,401,'invalid supplied credential never becomes anonymous');
  eq((await fetch(origin+'/parties/'+party,{headers:{cookie:invalid.header()}})).status,401,'invalid supplied page cookie fails hydration');
  // Decision 15: refs are bare integers on the wire; the old object form is still accepted.
  const missing = 999999;
  failure(await call('partyPage',{id:missing}), 'partyMissing');
  const unsupported = {type:{package:'domain',name:'Partiful.Party'},scope:'other',key:String(party)};
  eq((await call('partyPage',{id:unsupported})).status,400,'unsupported storage scope fails');
  failure(await call('account.signIn',{email:'unknown@example.com',password}), 'invalidCredentials');
  failure(await call('account.signIn',{email:'alice@example.com',password:password.trim()}), 'invalidCredentials');
  const login = new Jar(); success(await call('account.signIn',{email:'ALICE@example.com',password},login));
  const oldSession = new Jar(); oldSession.cookies = new Map(login.cookies);
  success(await call('account.signIn',{email:'alice@example.com',password},login));
  eq((await call('partyPage',{id:party},oldSession)).status,401,'auth change revokes presented session');
  success(await call('edit',{id:party,title:'Dinner',description:'At the table',visibility:variant('public')},alice));
  // A corrupt unselected email must not make the name projection hydrate Person.
  sql('UPDATE person SET email=? WHERE email=?',['not-an-email','bob@example.com']);
  eq((await page(new Jar())).guests.value.map(value=>value.name),['Bob','Carol'],'guarded SQL selects names only');
  sql('UPDATE person SET email=? WHERE name=?',['bob@example.com','Bob']);
  success(await call('reschedule',{id:party,date:int(300)},alice));
  // A host becomes an attendee only through RSVP, and private still denies it.
  success(await call('rsvp',{id:party},alice));
  success(await call('edit',{id:party,title:'Dinner',description:'At the table',visibility:variant('attendees')},alice));
  eq((await page(alice)).guests.value.map(value=>value.name),['Alice','Bob','Carol'],'attending host receives actual membership projection');
  success(await call('edit',{id:party,title:'Dinner',description:'At the table',visibility:variant('private')},alice));
  eq((await page(alice)).guests,'hidden','private hides from attending host');
  success(await call('edit',{id:party,title:'Dinner',description:'At the table',visibility:variant('public')},alice));
  // An external SQLite writer delays acquisition until the exact start cutoff.
  const clockParty = success(await call('host',host(150),alice));
  const releaseClock = await holdWriter();
  let clockSettled = false;
  const queued = call('rsvp',{id:clockParty},bob).then(result=>{clockSettled=true;return result;});
  await pause(200); check(!clockSettled,'command waits for actual writer acquisition');
  await writeFile(clock,'150'); await releaseClock();
  failure(await queued,'partyStarted');
  eq(sql('SELECT count(*) FROM party_guests WHERE parent=?',[Number(clockParty)])[0][0],0,'queued cutoff refuses edge write');
  await writeFile(clock,'100'); success(await call('cancel',{id:clockParty},alice));
  // Signin preparation observes an old credential; final admission must recheck.
  const releaseVersion = await holdWriter('UPDATE credential SET version=version+1 WHERE profile=?',[Number(aliceRef)]);
  const staleLogin = call('account.signIn',{email:'alice@example.com',password});
  await pause(200); await releaseVersion(); failure(await staleLogin,'invalidCredentials');
  eq((await call('partyPage',{id:party},alice)).status,401,'credential version invalidates existing live sessions');
  sql('UPDATE credential SET version=1 WHERE profile=?',[Number(aliceRef)]);
  const priorHash = sql('SELECT passwordHash FROM credential WHERE profile=?',[Number(aliceRef)])[0][0];
  const releaseHash = await holdWriter('UPDATE credential SET passwordHash=? WHERE profile=?',['changed-by-fixture',Number(aliceRef)]);
  const staleHashLogin = call('account.signIn',{email:'alice@example.com',password});
  await pause(200); await releaseHash(); failure(await staleHashLogin,'invalidCredentials');
  sql('UPDATE credential SET passwordHash=? WHERE profile=?',[priorHash,Number(aliceRef)]);
  sql('UPDATE credential SET enabled=0 WHERE profile=?',[Number(aliceRef)]);
  eq((await call('partyPage',{id:party},alice)).status,401,'disabled credential rejects session');
  failure(await call('account.signIn',{email:'alice@example.com',password}),'invalidCredentials');
  sql('UPDATE credential SET enabled=1 WHERE profile=?',[Number(aliceRef)]);
  await writeFile(clock,'86500');
  eq((await call('partyPage',{id:party},alice)).status,401,'exact session expiry fails viewer');
  eq((await call('host',host(90000),alice)).status,401,'expired session cannot mutate');
  await writeFile(clock,'100');
  // Deliberate broken FK fixture: loss of the live profile invalidates auth.
  const carolRow = sql('SELECT id,name,email FROM person WHERE email=?',['carol@example.com'])[0];
  sql('DELETE FROM person WHERE id=?',[carolRow[0]]);
  eq((await call('partyPage',{id:party},carol)).status,401,'deleted live profile does not become anonymous');
  eq((await call('rsvp',{id:party},carol)).status,401,'deleted live profile cannot mutate');
  sql('INSERT INTO person(id,name,email) VALUES(?,?,?)',carolRow);
  await writeFile(clock,'300');
  failure(await call('rsvp',{id:party},bob),'partyStarted');
  failure(await call('reschedule',{id:party,date:int(400)},alice),'partyStarted');
  success(await call('edit',{id:party,title:'After start',description:'Still editable',visibility:variant('public')},alice));
  eq((await page(alice)).date,'1970-01-01T00:05:00Z','post-start edit preserves date (RFC 3339 on the wire)');
  eq((await page(alice)).guests.value.map(value=>value.name),['Alice','Bob','Carol'],'edit preserves member set');
  await writeFile(clock,'100');
  await stop(); await start();
  eq((await page(bob)).guests.value.map(value=>value.name),['Alice','Bob','Carol'],'restart persists people, sessions and member set');
  eq((await page(alice)).date,'1970-01-01T00:05:00Z','restart persists date');
  success(await call('cancel',{id:party},alice));
  eq(counts().party_guests,0,'cancel cascades only member edges'); eq(counts().person,3,'cancel retains people');
  failure(await call('partyPage',{id:party}), 'partyMissing');
  const collision = await Promise.all([
    call('account.signUp',signup('Race A',' Race@Example.com ')),
    call('account.signUp',signup('Race B','race@example.COM'))]);
  eq(collision.filter(result=>result.body.tag==='success').length,1,'one concurrent canonical signup succeeds');
  eq(collision.filter(result=>result.body.value==='emailTaken').length,1,'other concurrent signup has exact business error');
  eq(sql('SELECT count(*) FROM person WHERE email=?',['race@example.com'])[0][0],1,'one canonical persisted profile');
  eq(sql('SELECT count(*) FROM credential WHERE profile=(SELECT id FROM person WHERE email=?)',['race@example.com'])[0][0],1,'one credential, no orphan');
  // A native session failure after profile/credential insertion must roll back.
  const beforeAbortCounters = counters();
  sql('ALTER TABLE session RENAME TO session_hold');
  const peopleBefore = sql('SELECT count(*) FROM person')[0][0], credentialsBefore = sql('SELECT count(*) FROM credential')[0][0];
  const aborted = await call('account.signUp',signup('Rollback','rollback@example.com'));
  eq(aborted.status,500,'late native storage failure is infrastructure'); eq(aborted.cookies.length,0,'late abort issues no cookie');
  eq(sql('SELECT count(*) FROM person')[0][0],peopleBefore,'late abort restores profiles');
  eq(sql('SELECT count(*) FROM credential')[0][0],credentialsBefore,'late abort restores credentials');
  sql('ALTER TABLE session_hold RENAME TO session');
  eq(counters(),beforeAbortCounters,'late session failure restores all counters');
  // Bearer transport (decision 1): curl-style clients present Authorization: Bearer over
  // the same session table; no CSRF or Origin. The token leaves only on a token request.
  async function bare(name, input, headers = {}) {
    const operation = op(name);
    const response = await fetch(origin + operation.http.path, {method:'POST',
      headers:{'content-type':'application/json', ...headers},
      body:JSON.stringify({operation:operation.identity, kind:operation.kind, input})});
    const text = await response.text();
    eq(response.headers.get('cache-control'), 'private, no-store', `${name}: no store`);
    return {status:response.status, body:JSON.parse(text), text, cookies:response.headers.getSetCookie(),
      marker:response.headers.get('x-leanapp-auth-csrf')};
  }
  const tokenAccept = {accept:'application/vnd.leanapp.token'};
  const bearer = token => ({authorization:`Bearer ${token}`});
  const digest = token => createHash('sha256').update(token).digest('hex');
  const dana = await bare('account.signUp', signup('Dana','dana@example.com'), tokenAccept);
  eq(dana.status, 200, 'curl-style token sign-up needs no Origin or cookie');
  eq(dana.cookies.length, 0, 'token sign-up sets no cookie'); eq(dana.marker, null, 'token sign-up has no CSRF marker');
  const danaToken = dana.body.value.token;
  check(/^[A-Za-z0-9_-]{43}$/.test(danaToken), 'token reply carries the raw session token');
  eq(Object.keys(dana.body.value).sort(), ['profile','token'], 'token reply is {profile, token}');
  eq(sql('SELECT count(*) FROM session WHERE digest=?',[digest(danaToken)])[0][0], 1, 'token session stored by digest only');
  const eve = await bare('account.signUp', signup('Eve','eve@example.com'), tokenAccept);
  const eveToken = eve.body.value.token;
  const bearerParty = success(await bare('host', host(500), bearer(danaToken)));
  const rsvpBearer = await bare('rsvp', {id:bearerParty}, bearer(eveToken));
  eq(rsvpBearer.status, 200, 'bearer RSVP succeeds with no CSRF and no Origin');
  eq(sql('SELECT count(*) FROM party_guests WHERE parent=?',[Number(bearerParty)])[0][0], 1, 'bearer RSVP persisted');
  const anonymousRsvp = await bare('rsvp', {id:bearerParty});
  eq(anonymousRsvp.status, 401, 'missing bearer is 401'); eq(anonymousRsvp.body, {tag:'unauthenticated'}, 'unauthenticated envelope');
  eq((await bare('rsvp', {id:bearerParty}, bearer('A'.repeat(43)))).status, 401, 'unknown bearer token is 401');
  eq((await bare('rsvp', {id:bearerParty}, {authorization:'Bearer short'})).status, 401, 'malformed bearer token is 401');
  eq((await bare('partyPage', {id:bearerParty}, bearer('A'.repeat(43)))).status, 401, 'invalid bearer never becomes anonymous');
  eq((await call('rsvp', {id:bearerParty}, bob, {omit:['x-csrf-token']})).status, 403, 'cookie request without CSRF still fails');
  const both = await bare('rsvp', {id:bearerParty}, {...bearer(eveToken), cookie:bob.header(), origin, 'x-csrf-token':bob.csrf()});
  eq(both.status, 400, 'cookie and bearer together are 400');
  eq(both.body, {tag:'protocol', code:'auth.ambiguous_credentials'}, 'ambiguous credentials envelope');
  const quiet = new Jar(), plain = await call('account.signIn', {email:'dana@example.com',password}, quiet);
  success(plain); const cookieToken = quiet.cookies.get('leanapp_session');
  check(cookieToken && !plain.text.includes(cookieToken) && !plain.text.includes('token'), 'default sign-in never puts the token in the body');
  eq(plain.body.value, dana.body.value.profile, 'default sign-in body is the profile ref');
  eq((await bare('account.signIn', {email:'dana@example.com',password})).status, 403, 'default sign-in without Origin is refused');
  const rotated = await bare('account.signIn', {email:'dana@example.com',password}, {...tokenAccept, ...bearer(danaToken)});
  eq(rotated.status, 200, 'token sign-in'); eq(rotated.cookies.length, 0, 'token sign-in sets no cookie');
  const danaNext = rotated.body.value.token; check(danaNext !== danaToken, 'token sign-in issues a new token');
  eq((await bare('rsvp', {id:bearerParty}, bearer(danaToken))).status, 401, 'rotated (revoked) bearer session is refused');
  eq((await bare('rsvp', {id:bearerParty}, bearer(danaNext))).status, 200, 'new bearer session works');
  sql('UPDATE session SET revoked=1 WHERE digest=?', [digest(danaNext)]);
  eq((await bare('rsvp', {id:bearerParty}, bearer(danaNext))).status, 401, 'revoked bearer session is refused');
  const wrongToken = await bare('account.signIn', {email:'eve@example.com',password:password.trim()}, tokenAccept);
  eq(wrongToken.status, 422, 'wrong password over token request'); check(!wrongToken.text.includes('"token"'), 'failed token sign-in has no token');
  await writeFile(clock, '86499');
  eq((await bare('partyPage', {id:bearerParty}, bearer(eveToken))).status, 200, 'bearer valid before its exact expiry');
  await writeFile(clock, '86500');
  eq((await bare('partyPage', {id:bearerParty}, bearer(eveToken))).status, 401, 'expired bearer session is refused');
  eq((await bare('cancel', {id:bearerParty}, bearer(eveToken))).status, 401, 'expired bearer session cannot mutate');
  await writeFile(clock, '100');
  // Generated browser, real Chromium, same native server/SQLite.
  const {chromium} = await import(pathToFileURL(join(nodeModules,'playwright-core/index.mjs')));
  browser = await chromium.launch({headless:true});
  const aliceContext = await browser.newContext(), bobContext = await browser.newContext();
  const alicePage = await aliceContext.newPage(), bobPage = await bobContext.newPage();
  const errors = [];
  for (const page of [alicePage,bobPage]) page.on('pageerror', error => errors.push(error.message));
  async function browserSignup(page,name,email,navigate=true) {
    if (navigate) await page.goto(origin+'/sign-up');
    await page.locator('input[name=name]').fill(name); await page.locator('input[name=email]').fill(email);
    await page.locator('input[name=password]').fill(password); await page.locator('button[type=submit]').click();
    await page.waitForURL('**/parties/new');
  }
  await browserSignup(alicePage,'Browser Alice','browser-alice@example.com');
  const invalidPage = await browser.newPage();
  await invalidPage.goto(origin+'/sign-up');
  await invalidPage.locator('input[name=name]').fill('Duplicate');
  await invalidPage.locator('input[name=email]').fill(' BROWSER-ALICE@EXAMPLE.COM ');
  await invalidPage.locator('input[name=password]').fill(password);
  await invalidPage.locator('button[type=submit]').click();
  await invalidPage.waitForFunction(()=>document.querySelector('main').innerText.includes('This email already has an account.'));
  eq(await invalidPage.locator('input[name=email]').inputValue(),'BROWSER-ALICE@EXAMPLE.COM','canonical collision retains browser email draft without lowercasing');
  eq((await invalidPage.context().cookies()).length,0,'UI collision issues no auth cookies');
  let invalidSubmissions = 0;
  invalidPage.on('request',request=>{if(request.url().endsWith('/account.signUp'))invalidSubmissions++;});
  await invalidPage.locator('input[name=email]').fill('invalid-draft@example.com');
  await invalidPage.locator('input[name=password]').fill('x');
  await invalidPage.locator('button[type=submit]').click();
  await pause(100);
  eq(invalidSubmissions,0,'derived shared parser blocks invalid password draft before transport');
  eq(await invalidPage.locator('input[name=password]').inputValue(),'x','invalid checked draft is retained');
  await invalidPage.close();
  await alicePage.locator('input[name=title]').fill('Browser dinner');
  await alicePage.locator('[name=description]').fill('Together');
  await alicePage.locator('input[name=date]').fill('1970-01-01T00:08:20');
  await alicePage.locator('button[type=submit]').click(); await alicePage.waitForURL(/\/parties\/\d+$/);
  const partyURL = alicePage.url();
  await browserSignup(bobPage,'Browser Bob','browser-bob@example.com');
  await bobPage.goto(partyURL);
  await bobPage.getByRole('button',{name:"I'm going",exact:true}).click();
  await bobPage.getByText('Browser Bob',{exact:true}).waitFor();
  await bobPage.reload();
  await bobPage.getByRole('button',{name:"I'm going",exact:true}).click();
  await bobPage.getByText('Browser Bob',{exact:true}).waitFor();
  check(true,'CSRF restored and mutation injected after browser reload');
  const editForm = alicePage.locator('form').filter({has:alicePage.locator('input[name=title]')});
  await editForm.locator('input[name=title]').fill('Browser dinner');
  await editForm.locator('[name=description]').fill('Together');
  await editForm.locator('select[name=visibility]').selectOption('attendees');
  await editForm.locator('button[type=submit]').click();
  await bobPage.reload(); await bobPage.getByText('Browser Bob',{exact:true}).waitFor();
  let authQueryResponses = 0;
  bobPage.on('response',response=>{if(response.url().endsWith('/partyPage'))authQueryResponses++;});
  sql('UPDATE credential SET enabled=0 WHERE profile=(SELECT id FROM person WHERE email=?)',['browser-bob@example.com']);
  const priorResponses = authQueryResponses;
  await bobPage.getByRole('button',{name:"I'm going",exact:true}).click();
  await bobPage.getByRole('alert').filter({hasText:'Please sign in.'}).waitFor();
  await bobPage.waitForFunction(()=>!document.querySelector('main').innerText.includes('Browser Bob'));
  await pause(300); check(authQueryResponses-priorResponses<=2,'framework invalidation does not loop unauthorized queries');
  check(true,'framework unauthenticated clears protected mounted resource');
  sql('UPDATE credential SET enabled=1 WHERE profile=(SELECT id FROM person WHERE email=?)',['browser-bob@example.com']);
  await bobPage.reload(); await bobPage.getByText('Browser Bob',{exact:true}).waitFor();
  // Hold a genuinely authorized nonempty response, then change policy and auth.
  let releaseResponse, enteredResponse, routeFinished, intercepted=false, abortedResource=false;
  const heldResponse = new Promise(done=>{releaseResponse=done;});
  const entered = new Promise(done=>{enteredResponse=done;});
  const routeDone = new Promise(done=>{routeFinished=done;});
  const routePattern = '**/api/partiful/partyPage';
  bobPage.on('requestfailed',request=>{
    if(request.url().endsWith('/partyPage') && request.failure()?.errorText.includes('ABORTED'))abortedResource=true;
  });
  await bobPage.route(routePattern,async route=>{
    if(intercepted){await route.continue();return;}
    intercepted=true;
    const response=await route.fetch(); enteredResponse(await response.json());
    await heldResponse; await route.fulfill({response}); routeFinished();
  });
  async function spa(page,path) {
    await page.evaluate(path=>{history.pushState({},'',path);dispatchEvent(new PopStateEvent('popstate'));},path);
  }
  await spa(bobPage,'/parties/new'); await bobPage.locator('input[name=title]').waitFor();
  await spa(bobPage,new URL(partyURL).pathname);
  const obsolete = await entered;
  eq(obsolete.value.guests.value.map(value=>value.name),['Browser Bob'],'delayed response holds real authorized names');
  await editForm.locator('select[name=visibility]').selectOption('private');
  await editForm.locator('button[type=submit]').click();
  try { await alicePage.waitForFunction(() => document.querySelector('main').innerText.includes('The guest list is private.')); }
  catch (error) {
    console.log('Browser private update text:', await alicePage.locator('main').innerText());
    console.log('Browser programming errors:', errors);
    throw error;
  }
  await spa(bobPage,'/sign-up');
  await browserSignup(bobPage,'New Viewer','browser-new-viewer@example.com',false);
  await spa(bobPage,new URL(partyURL).pathname);
  releaseResponse(); await routeDone; await bobPage.unroute(routePattern);
  try { await bobPage.waitForFunction(() => document.querySelector('main').innerText.includes('The guest list is private.')); }
  catch (error) {
    console.log('Browser private reload text:', await bobPage.locator('main').innerText());
    console.log('Browser programming errors:', errors);
    throw error;
  }
  check(!(await bobPage.locator('main').innerText()).includes('Browser Bob'),'private browser list has no payload');
  check(abortedResource,'actual scoped query fetch aborts on screen/auth change');
  await pause(100);
  check(!(await bobPage.locator('main').innerText()).includes('Browser Bob'),'late authorized response cannot repopulate new auth scope');
  const dateForm = alicePage.locator('form').filter({has:alicePage.locator('input[name=date]')});
  await dateForm.locator('input[name=date]').fill('1970-01-01T00:10');
  await dateForm.locator('button[type=submit]').click();
  await alicePage.waitForTimeout(100);
  await stop(); await start(); await alicePage.reload();
  await alicePage.waitForFunction(() => document.querySelector('main').innerText.includes('The guest list is private.'));
  check((await alicePage.locator('main').innerText()).includes('1970'),'human date survives browser/server restart');
  await alicePage.getByRole('button',{name:'Cancel party',exact:true}).click();
  await alicePage.waitForURL('**/parties/new');
  await alicePage.goto(origin+'/sign-in');
  await alicePage.locator('input[name=email]').fill('BROWSER-ALICE@example.com');
  await alicePage.locator('input[name=password]').fill(password);
  await alicePage.locator('button[type=submit]').click(); await alicePage.waitForURL('**/parties/new');
  check(true,'compiled signin rotates live auth and returns derived host page');
  await alicePage.goto(origin+'/sign-in');
  const authRace = await alicePage.evaluate(async ({identity,password})=>{
    const module=await import('/assets/app.mjs');
    const root=document.createElement('aside');document.body.append(root);
    let releaseBody, enteredBody, first=true;
    const held=new Promise(done=>{releaseBody=done;});
    const entered=new Promise(done=>{enteredBody=done;});
    const fetchImpl=async (url,init)=>{
      const response=await fetch(url,init);
      if(first && url.endsWith('/account.signIn')){
        first=false; enteredBody();
        return {status:response.status,headers:response.headers,json:async()=>{await held;return response.json();}};
      }
      return response;
    };
    const app=module.mountApp({root,fetchImpl});
    const old=app.client.call(identity,{email:'browser-bob@example.com',password});
    await entered;
    const newer=await app.client.call(identity,{email:'browser-alice@example.com',password});
    await new Promise(done=>setTimeout(done,20));
    const actor=app.snapshot().actor, generation=app.snapshot().generation;
    releaseBody();const older=await old;
    await new Promise(done=>setTimeout(done,20));
    const result={nonempty:newer.ok && older.ok && String(newer.value?.key ?? newer.value)!==String(older.value?.key ?? older.value),
      scoped:actor.tag==='Option.some',stable:app.snapshot().actor===actor && app.snapshot().generation===generation};
    app.close();root.remove();return result;
  },{identity:op('account.signIn').identity,password});
  check(authRace.nonempty,'out-of-order auth uses two actual distinct profile results');
  check(authRace.scoped && authRace.stable,'older auth body cannot overwrite newer committed cookie actor scope');
  eq(errors,[],'compiled browser has no programming exceptions');
  const cookieMetadata = await aliceContext.cookies();
  check(cookieMetadata.some(cookie=>cookie.name==='leanapp_session' && cookie.httpOnly),'session cookie is HTTP only');
  check(cookieMetadata.some(cookie=>cookie.name==='leanapp_csrf' && !cookie.httpOnly),'paired CSRF cookie is readable');
  const profiles = sql('SELECT name,email FROM person');
  check(profiles.some(row=>row[0]==='Browser Bob'),'nonempty browser rows persisted');
  const hashes = sql('SELECT passwordHash FROM credential').map(row=>row[0]);
  check(hashes.every(hash=>hash!==password && hash.length>50),'only password hashes persisted');
  const digests = sql('SELECT digest,csrfDigest FROM session');
  check(digests.every(row=>row.every(value=>/^[a-f0-9]{64}$/.test(value))),'only opaque digests persisted');
  // LeanDB's migration gate through the app executable (`partiful migrate [--check]`).
  const {LEANAPP_BROWSER_DIR: _, ...gateEnv} = process.env;
  const migrate = (...args) => spawnSync(join(workspace, '.lake/build/bin', exe), args,
    {cwd:run, env:{...gateEnv, LEANAPP_DATABASE:database}, encoding:'utf8'});
  let gate = migrate('migrate','--check');
  eq([gate.status, gate.stdout.split('\n')[0]], [0,'status: up to date — the database is at the compiled schema.'], 'partiful migrate --check');
  gate = migrate('migrate');
  eq([gate.status, gate.stdout.split('\n')[0]], [0,'status: up to date — the database is at the compiled schema.'], 'partiful migrate');
  eq(migrate('bogus').status, 2, 'partiful refuses unknown arguments');
  await writeFile(join(run,'receipt.json'),JSON.stringify({checks,operations:manifest.operations.length,
    native:true,sqlite:true,chromium:true,restart:true},null,2));
  console.log(`PASS: ${checks} HTTP/SQLite/compiled Chromium checks; receipt ${run}/receipt.json`);
} finally {
  if (browser) await browser.close();
  if (server) await stop();
}
