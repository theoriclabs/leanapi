import assert from 'node:assert/strict';
import test from 'node:test';
import { readFileSync } from 'node:fs';
import { pathToFileURL } from 'node:url';
const out = process.env.DDD_CLIENT_OUT;
assert.ok(out, 'DDD_CLIENT_OUT is the native fixture output directory');
const { createClient, operations, manifest, decodeHttpReply } = await import(pathToFileURL(`${out}/operations.mjs`));
// Numbers are bare JSON numbers now; read the recorded bytes exactly (big integers stay exact).
const { parseJson } = await import(pathToFileURL(`${out}/Fetch.mjs`));
const fixture = parseJson(readFileSync(`${out}/fixture.json`, 'utf8'));
const op = Object.values(operations)[0];
assert.ok(op);
const response = (body, status) => ({ status, ok: status >= 200 && status < 300,
  json: async () => body });

test('generated client consumes success and non-2xx domain replies from real LeanAPI HTTP', async () => {
  const client = createClient({ verify: false, fetch: async () => response(fixture.success, 200) });
  assert.deepEqual(await client.call(op.identity, {label: 'persisted'}), {ok: true, value: 9007199254741000n});
  const denied = createClient({ verify: false, fetch: async () => response(fixture.domain, 409) });
  assert.deepEqual(await denied.call(op.identity, {label: 'abort'}), {ok: false, error: {tag: 'denied', value: null}});
});

test('generated client retains typed framework outcomes', async () => {
  for (const [key, status] of [['decode', 400], ['unauthenticated', 401], ['forbidden', 403],
    ['incompatible', 409], ['protocol', 400]]) {
    const client = createClient({ verify: false, fetch: async () => response(fixture[key], status) });
    await assert.rejects(client.call(key === 'incompatible' ? {...op.identity, version: '0'} : op.identity, {label: 'x'}), e => e.kind === key);
  }
});

test('stale manifest refuses a call before mutation and cancellation remains typed', async () => {
  let calls = 0;
  const client = createClient({ verify: true, fetch: async () => {
    calls++; return response({operations: []}, 200);
  }});
  await assert.rejects(client.call(op.identity, {label: 'x'}), e => e.kind === 'incompatible');
  assert.equal(calls, 1);
  assert.equal(manifest.operations.length, 2);
  const controller = new AbortController();
  controller.abort();
  const cancelled = createClient({ verify: false, fetch: async () => {
    throw new DOMException('cancelled', 'AbortError');
  }});
  await assert.rejects(cancelled.call(op.identity, {label: 'x'}, {signal: controller.signal}), e => e.kind === 'cancelled');
});


test('shared generated disclosure codec handles actual hidden and nonempty visible responses', async () => {
  const list = Object.values(operations).find(operation => operation.identity.name === 'list');
  const client = createClient({verify: false, fetch: async () => response(fixture.hidden, 200)});
  assert.deepEqual(await client.call(list.identity, null), {ok: true, value: {tag: 'hidden', value: null}});
  const visible = createClient({verify: false, fetch: async () => response(fixture.visible, 200)});
  assert.deepEqual(await visible.call(list.identity, null), {
    ok: true, value: {tag: 'visible', value: ['persisted', 'native']}
  });
  // `hidden` is a bare string now; its old object form with an extra field must still fail.
  const tampered = structuredClone(fixture.hidden);
  tampered.value = {tag: 'hidden', value: null, count: 2};
  const unsafe = createClient({verify: false, fetch: async () => response(tampered, 200)});
  await assert.rejects(unsafe.call(list.identity, null), e => e.kind === 'decode');
});


test('server incompatibility and database fault fixture bytes retain framework channels', async () => {
  assert.throws(() => decodeHttpReply({...op, identity: {...op.identity, version: '0'}},
    409, fixture.incompatible), error => error.kind === 'incompatible');
  assert.throws(() => decodeHttpReply(op, 500, fixture.database),
    error => error.kind === 'protocol' && error.code === 'database.unavailable');
});
