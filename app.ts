// forge — a standalone GitHub-compatible git forge in one Node 22 process.
// Standard library only: node:http, node:crypto (SHA-1), node:zlib.
//
// The whole state lives in memory (Maps). Nothing is written to disk per
// request and no clock or randomness reaches any stored object: commit
// timestamps come from a deterministic counter, so two runs fed the same
// requests in the same order produce the same object ids.
//
// Surfaces, all on the one server createApp() builds:
//   GET  /healthz                          200 {"ok": true}
//   GET  /api/v3/  /api/v3/meta            REST v3 root and meta
//   /api/v3/...                            REST v3: repos, branches, commits,
//                                          contents, labels, issues, comments,
//                                          pull requests and merges
//   POST /api/graphql                     GraphQL v4 (viewer, repository,
//                                          issue / pull-request reads and
//                                          mutations, __type introspection,
//                                          node(id:), batched operations)
//   POST /mcp                             MCP over Streamable HTTP
//                                          (server/discover, tools/list,
//                                          tools/call; legacy initialize
//                                          handshake also accepted)
//   /{owner}/{repo}.git/...               git smart HTTP: upload-pack
//                                          protocol v2 (ls-refs, fetch,
//                                          shallow / deepen) and receive-pack
//                                          v0 (report-status, side-band-64k,
//                                          delete-refs), with full packfile
//                                          read (OFS_DELTA and REF_DELTA) and
//                                          write (plain objects, no deltas).

import { createServer, type IncomingMessage, type Server, type ServerResponse } from 'node:http';
import { createHash } from 'node:crypto';
import { deflateSync, inflateSync } from 'node:zlib';

// ---------------------------------------------------------------------------
// small utilities
// ---------------------------------------------------------------------------

const ZERO_OID = '0'.repeat(40);
const JSON_TYPE = 'application/json; charset=utf-8';
const TOKEN = process.env.MAKEFUN_SHOP_TOKEN ?? '';
const AGENT_NAME = 'forge/1.0';

let requestCounter = 0;
let clockSeq = 0;

/** Deterministic "now": seconds since a fixed epoch, one tick per call. */
function tickEpoch(): number {
  clockSeq += 1;
  return 1_700_000_000 + clockSeq;
}

function isoOf(epochSec: number): string {
  return new Date(epochSec * 1000).toISOString();
}

function isOid(value: unknown): value is string {
  return typeof value === 'string' && /^[0-9a-f]{40}$/.test(value);
}

function sha1(data: Buffer): string {
  return createHash('sha1').update(data).digest('hex');
}

function b64encode(text: string): string {
  return Buffer.from(text, 'utf8').toString('base64');
}

function b64decode(content: string): Buffer {
  return Buffer.from(content.replace(/[\r\n\t ]+/g, ''), 'base64');
}

let nextNumericId = 1000;
function allocId(): number {
  nextNumericId += 1;
  return nextNumericId;
}

/** Opaque Relay-style global id: base64url of "Kind:payload". */
function globalId(kind: string, payload: string): string {
  return Buffer.from(`${kind}:${payload}`, 'utf8').toString('base64url');
}

function parseGlobalId(id: string): { kind: string; payload: string } | null {
  try {
    const text = Buffer.from(id, 'base64url').toString('utf8');
    const colon = text.indexOf(':');
    if (colon < 0) return null;
    return { kind: text.slice(0, colon), payload: text.slice(colon + 1) };
  } catch {
    return null;
  }
}

// ---------------------------------------------------------------------------
// git object model
// ---------------------------------------------------------------------------

type ObjType = 'commit' | 'tree' | 'blob' | 'tag';

interface GitObject {
  type: ObjType;
  data: Buffer;
}

function hashObject(type: ObjType, data: Buffer): string {
  const header = Buffer.from(`${type} ${data.length}\u0000`, 'utf8');
  return sha1(Buffer.concat([header, data]));
}

interface TreeEntry {
  mode: string;
  name: string;
  oid: string;
}

function parseTree(data: Buffer): TreeEntry[] {
  const entries: TreeEntry[] = [];
  let offset = 0;
  while (offset < data.length) {
    const space = data.indexOf(0x20, offset);
    const nul = data.indexOf(0x00, space + 1);
    if (space < 0 || nul < 0 || nul + 21 > data.length) break;
    entries.push({
      mode: data.subarray(offset, space).toString('ascii'),
      name: data.subarray(space + 1, nul).toString('utf8'),
      oid: data.subarray(nul + 1, nul + 21).toString('hex'),
    });
    offset = nul + 21;
  }
  return entries;
}

function compareTreeNames(a: TreeEntry, b: TreeEntry): number {
  const left = Buffer.from(a.mode === '40000' ? `${a.name}/` : a.name, 'utf8');
  const right = Buffer.from(b.mode === '40000' ? `${b.name}/` : b.name, 'utf8');
  return Buffer.compare(left, right);
}

function buildTree(entries: readonly TreeEntry[]): Buffer {
  const sorted = [...entries].sort(compareTreeNames);
  const parts: Buffer[] = [];
  for (const entry of sorted) {
    parts.push(Buffer.from(`${entry.mode} ${entry.name}\u0000`, 'utf8'));
    parts.push(Buffer.from(entry.oid, 'hex'));
  }
  return Buffer.concat(parts);
}

interface CommitView {
  tree: string;
  parents: string[];
  author: string;
  committer: string;
  message: string;
}

function parseCommit(data: Buffer): CommitView {
  const blank = data.indexOf('\n\n');
  const headerText = data.subarray(0, blank < 0 ? data.length : blank).toString('utf8');
  const message = blank < 0 ? '' : data.subarray(blank + 2).toString('utf8');
  let tree = '';
  const parents: string[] = [];
  let author = '';
  let committer = '';
  for (const line of headerText.split('\n')) {
    if (!line) continue;
    const space = line.indexOf(' ');
    const key = space < 0 ? line : line.slice(0, space);
    const value = space < 0 ? '' : line.slice(space + 1);
    if (key === 'tree') tree = value;
    else if (key === 'parent') parents.push(value);
    else if (key === 'author') author = value;
    else if (key === 'committer') committer = value;
  }
  return { tree, parents, author, committer, message };
}

interface TagView {
  object: string;
  type: ObjType;
  tag: string;
  tagger: string;
  message: string;
}

function parseTag(data: Buffer): TagView {
  const blank = data.indexOf('\n\n');
  const headers = new Map<string, string>();
  for (const line of data.subarray(0, blank < 0 ? data.length : blank).toString('utf8').split('\n')) {
    if (!line) continue;
    const space = line.indexOf(' ');
    if (space >= 0) headers.set(line.slice(0, space), line.slice(space + 1));
  }
  const type = headers.get('type') ?? 'commit';
  return {
    object: headers.get('object') ?? '',
    type: type === 'tree' || type === 'blob' || type === 'tag' ? type : 'commit',
    tag: headers.get('tag') ?? '',
    tagger: headers.get('tagger') ?? '',
    message: blank < 0 ? '' : data.subarray(blank + 2).toString('utf8'),
  };
}

/** Every object reachable from `roots` in `lookup` (gitlinks skipped). */
function collectReachable(roots: Iterable<string>, lookup: (oid: string) => GitObject | undefined): Set<string> {
  const seen = new Set<string>();
  const queue: string[] = [];
  for (const root of roots) if (isOid(root)) queue.push(root);
  while (queue.length > 0) {
    const oid = queue.pop()!;
    if (seen.has(oid)) continue;
    const object = lookup(oid);
    if (!object) continue;
    seen.add(oid);
    if (object.type === 'commit') {
      const commit = parseCommit(object.data);
      queue.push(commit.tree);
      for (const parent of commit.parents) queue.push(parent);
    } else if (object.type === 'tag') {
      queue.push(parseTag(object.data).object);
    } else if (object.type === 'tree') {
      for (const entry of parseTree(object.data)) {
        if (entry.mode !== '160000') queue.push(entry.oid);
      }
    }
  }
  return seen;
}

/** True when `ancestor` is reachable from `tip` (or equal to it). */
function isAncestor(lookup: (oid: string) => GitObject | undefined, ancestor: string, tip: string): boolean {
  if (ancestor === tip) return true;
  const seen = new Set<string>();
  const queue = [tip];
  while (queue.length > 0) {
    const oid = queue.pop()!;
    if (seen.has(oid)) continue;
    seen.add(oid);
    const object = lookup(oid);
    if (!object || object.type !== 'commit') continue;
    for (const parent of parseCommit(object.data).parents) {
      if (parent === ancestor) return true;
      queue.push(parent);
    }
  }
  return false;
}

// ---------------------------------------------------------------------------
// pkt-line framing
// ---------------------------------------------------------------------------

function pktLine(payload: string | Buffer): Buffer {
  const data = typeof payload === 'string' ? Buffer.from(payload, 'utf8') : payload;
  const header = Buffer.alloc(4);
  header.write((data.length + 4).toString(16).padStart(4, '0'), 0, 4, 'ascii');
  return Buffer.concat([header, data]);
}

const PKT_FLUSH = Buffer.from('0000', 'ascii');
const PKT_DELIM = Buffer.from('0001', 'ascii');

interface Pkt {
  kind: 'data' | 'flush' | 'delim' | 'end';
  payload: Buffer;
}

/** Decode a whole buffer of pkt-lines; stops at the first malformed header. */
function decodePktLines(bytes: Buffer): { packets: Pkt[]; ok: boolean; rest: Buffer } {
  const packets: Pkt[] = [];
  let offset = 0;
  while (offset + 4 <= bytes.length) {
    const head = bytes.subarray(offset, offset + 4).toString('ascii');
    if (!/^[0-9a-fA-F]{4}$/.test(head)) return { packets, ok: false, rest: bytes.subarray(offset) };
    const length = Number.parseInt(head, 16);
    if (length === 0) {
      packets.push({ kind: 'flush', payload: Buffer.alloc(0) });
      offset += 4;
      continue;
    }
    if (length === 1) {
      packets.push({ kind: 'delim', payload: Buffer.alloc(0) });
      offset += 4;
      continue;
    }
    if (length === 2) {
      packets.push({ kind: 'end', payload: Buffer.alloc(0) });
      offset += 4;
      continue;
    }
    if (length < 4 || offset + length > bytes.length) return { packets, ok: false, rest: bytes.subarray(offset) };
    packets.push({ kind: 'data', payload: bytes.subarray(offset + 4, offset + length) });
    offset += length;
  }
  return { packets, ok: offset === bytes.length, rest: bytes.subarray(offset) };
}

function pktLinesText(packets: readonly Pkt[]): string[] {
  const lines: string[] = [];
  for (const packet of packets) if (packet.kind === 'data') lines.push(packet.payload.toString('utf8'));
  return lines;
}

// ---------------------------------------------------------------------------
// packfile read / write
// ---------------------------------------------------------------------------

const TYPE_CODE: Record<ObjType, number> = { commit: 1, tree: 2, blob: 3, tag: 4 };
const CODE_TYPE: Record<number, ObjType> = { 1: 'commit', 2: 'tree', 3: 'blob', 4: 'tag' };

function writePackHeader(type: ObjType, size: number): Buffer {
  const code = TYPE_CODE[type];
  const bytes: number[] = [];
  let remaining = size;
  let first = (code << 4) | (remaining & 0x0f);
  remaining = Math.floor(remaining / 16);
  while (remaining > 0) {
    bytes.push(first | 0x80);
    first = remaining & 0x7f;
    remaining = Math.floor(remaining / 128);
  }
  bytes.push(first);
  return Buffer.from(bytes);
}

/** Build a packfile from plain objects only (no deltas). */
function writePack(objects: Iterable<GitObject>): Buffer {
  const list = [...objects];
  const parts: Buffer[] = [];
  const header = Buffer.alloc(12);
  header.write('PACK', 0, 4, 'ascii');
  header.writeUInt32BE(2, 4);
  header.writeUInt32BE(list.length, 8);
  parts.push(header);
  for (const object of list) {
    parts.push(writePackHeader(object.type, object.data.length));
    parts.push(deflateSync(object.data));
  }
  const body = Buffer.concat(parts);
  return Buffer.concat([body, createHash('sha1').update(body).digest()]);
}

function readVarint(buffer: Buffer, start: number): { size: number; next: number; first: number } {
  let byte = buffer[start];
  const first = byte;
  let size = byte & 0x0f;
  let shift = 4;
  let offset = start + 1;
  while (byte & 0x80) {
    byte = buffer[offset++];
    size += (byte & 0x7f) * 2 ** shift;
    shift += 7;
  }
  return { size, next: offset, first };
}

function readOfsBase(buffer: Buffer, start: number): { baseOffset: number; next: number } {
  let byte = buffer[start];
  let offset = start + 1;
  let value = byte & 0x7f;
  while (byte & 0x80) {
    byte = buffer[offset++];
    value = ((value + 1) * 128) + (byte & 0x7f);
  }
  return { baseOffset: value, next: offset };
}

function inflateAt(buffer: Buffer, offset: number): { data: Buffer; next: number } {
  const result = inflateSync(buffer.subarray(offset), { info: true }) as unknown as {
    buffer: Buffer;
    engine: { bytesWritten: number };
  };
  return { data: result.buffer, next: offset + result.engine.bytesWritten };
}

function applyDelta(base: Buffer, delta: Buffer): Buffer {
  let offset = 0;
  const readSize = (): number => {
    let value = 0;
    let shift = 0;
    for (;;) {
      const byte = delta[offset++];
      value += (byte & 0x7f) * 2 ** shift;
      shift += 7;
      if (!(byte & 0x80)) break;
    }
    return value;
  };
  const sourceSize = readSize();
  const targetSize = readSize();
  if (sourceSize !== base.length) throw new Error('delta base size mismatch');
  const out = Buffer.alloc(targetSize);
  let written = 0;
  while (offset < delta.length) {
    const op = delta[offset++];
    if (op & 0x80) {
      let copyOffset = 0;
      let copySize = 0;
      let shift = 0;
      for (let bit = 0; bit < 4; bit += 1) {
        if (op & (1 << bit)) copyOffset += delta[offset++] * 2 ** shift;
        shift += 8;
      }
      shift = 0;
      for (let bit = 4; bit < 7; bit += 1) {
        if (op & (1 << bit)) copySize += delta[offset++] * 2 ** shift;
        shift += 8;
      }
      if (copySize === 0) copySize = 0x10000;
      base.copy(out, written, copyOffset, copyOffset + copySize);
      written += copySize;
    } else if (op !== 0) {
      const literal = op & 0x7f;
      delta.copy(out, written, offset, offset + literal);
      offset += literal;
      written += literal;
    } else {
      throw new Error('delta opcode 0');
    }
  }
  if (written !== targetSize) throw new Error('delta size mismatch');
  return out;
}

interface PackRead {
  objects: Map<string, GitObject>;
  deltaCount: number;
}

/** Read a packfile, resolving OFS_DELTA and REF_DELTA (thin-pack bases via `resolveBase`). */
function readPack(pack: Buffer, resolveBase?: (oid: string) => GitObject | undefined): PackRead {
  if (pack.length < 32 || pack.subarray(0, 4).toString('ascii') !== 'PACK') throw new Error('bad pack header');
  const version = pack.readUInt32BE(4);
  if (version !== 2 && version !== 3) throw new Error(`unsupported pack version ${version}`);
  const declaredCount = pack.readUInt32BE(8);
  const trailerStart = pack.length - 20;
  interface Raw {
    offset: number;
    typeCode: number;
    size: number;
    data: Buffer;
    baseOffset?: number;
    baseOid?: string;
  }
  const raw: Raw[] = [];
  const byOffset = new Map<number, Raw>();
  let offset = 12;
  for (let index = 0; index < declaredCount; index += 1) {
    const entryOffset = offset;
    const header = readVarint(pack, offset);
    offset = header.next;
    const typeCode = (header.first >> 4) & 0x07;
    const entry: Raw = { offset: entryOffset, typeCode, size: header.size, data: Buffer.alloc(0) };
    if (typeCode === 6) {
      const base = readOfsBase(pack, offset);
      offset = base.next;
      entry.baseOffset = entryOffset - base.baseOffset;
    } else if (typeCode === 7) {
      entry.baseOid = pack.subarray(offset, offset + 20).toString('hex');
      offset += 20;
    } else if (!CODE_TYPE[typeCode]) {
      throw new Error(`unknown pack type code ${typeCode}`);
    }
    const inflated = inflateAt(pack.subarray(0, trailerStart), offset);
    if (inflated.data.length !== header.size) throw new Error('pack entry size mismatch');
    entry.data = inflated.data;
    offset = inflated.next;
    raw.push(entry);
    byOffset.set(entryOffset, entry);
  }
  const objects = new Map<string, GitObject>();
  const resolved = new Map<number, { type: ObjType; data: Buffer; oid: string }>();
  const byOid = new Map<string, number>();
  const resolving = new Set<number>();
  const resolve = (entry: Raw): { type: ObjType; data: Buffer; oid: string } => {
    const done = resolved.get(entry.offset);
    if (done) return done;
    if (resolving.has(entry.offset)) throw new Error('delta cycle');
    resolving.add(entry.offset);
    let type: ObjType;
    let data: Buffer;
    if (entry.typeCode === 6) {
      const baseEntry = byOffset.get(entry.baseOffset!);
      if (!baseEntry) throw new Error('ofs-delta base missing');
      const base = resolve(baseEntry);
      type = base.type;
      data = applyDelta(base.data, entry.data);
    } else if (entry.typeCode === 7) {
      const wanted = entry.baseOid!;
      const baseOffset = byOid.get(wanted);
      if (baseOffset !== undefined) {
        const base = resolve(byOffset.get(baseOffset)!);
        type = base.type;
        data = applyDelta(base.data, entry.data);
      } else {
        const external = resolveBase?.(wanted);
        if (!external) throw new Error(`ref-delta base ${wanted} missing`);
        type = external.type;
        data = applyDelta(external.data, entry.data);
      }
    } else {
      type = CODE_TYPE[entry.typeCode];
      data = entry.data;
    }
    const oid = hashObject(type, data);
    const result = { type, data, oid };
    resolved.set(entry.offset, result);
    byOid.set(oid, entry.offset);
    resolving.delete(entry.offset);
    return result;
  };
  let deltaCount = 0;
  for (const entry of raw) {
    const r = resolve(entry);
    if (entry.typeCode === 6 || entry.typeCode === 7) deltaCount += 1;
    if (!objects.has(r.oid)) objects.set(r.oid, { type: r.type, data: r.data });
  }
  return { objects, deltaCount };
}

// ---------------------------------------------------------------------------
// the store
// ---------------------------------------------------------------------------

interface Label {
  name: string;
  color: string;
  description: string;
}

interface Issue {
  id: number;
  number: number;
  title: string;
  body: string;
  state: 'open' | 'closed';
  labels: string[];
  seq: number;
  createdEpoch: number;
  comments: Comment[];
}

interface Comment {
  id: number;
  body: string;
  createdEpoch: number;
}

interface Pull {
  id: number;
  number: number;
  title: string;
  body: string;
  state: 'open' | 'closed';
  merged: boolean;
  mergedAt: string;
  mergeCommitSha: string;
  headRef: string;
  baseRef: string;
  headSha: string;
  baseSha: string;
  mergeBaseSha: string;
  seq: number;
  createdEpoch: number;
}

interface Repo {
  id: number;
  name: string;
  owner: string | null;
  description: string;
  priv: boolean;
  defaultBranch: string;
  seq: number;
  createdEpoch: number;
  refs: Map<string, string>;
  objects: Map<string, GitObject>;
  labels: Map<string, Label>;
  issues: Issue[];
  pulls: Pull[];
  nextNumber: number;
  nextCommentId: number;
  /** Bumped whenever repo.objects gains an entry; fetch responses are cached against it. */
  packVersion: number;
  /** One-entry cache of the last upload-pack response (key = parsed fetch args). */
  fetchCache: { key: string; version: number; body: Buffer } | null;
}

const reposByName = new Map<string, Repo>();
let viewerLogin: string | null = null;

function getRepo(name: string): Repo | undefined {
  return reposByName.get(name);
}

function createRepoRecord(name: string, description: string, priv: boolean): Repo {
  const epoch = tickEpoch();
  const repo: Repo = {
    id: allocId(),
    name,
    owner: null,
    description,
    priv,
    defaultBranch: 'main',
    seq: reposByName.size,
    createdEpoch: epoch,
    refs: new Map(),
    objects: new Map(),
    labels: new Map(),
    issues: [],
    pulls: [],
    nextNumber: 1,
    nextCommentId: 1,
    packVersion: 0,
    fetchCache: null,
  };
  reposByName.set(name, repo);
  return repo;
}

/** Learn the token owner's login from the first owner string seen on a repo path. */
function learnViewer(owner: string): void {
  if (viewerLogin === null && owner !== '') viewerLogin = owner;
}

/**
 * Resolve a repo for a request that names an owner: returns the repo when it
 * exists and the owner matches (or the owner is learned now), else null.
 * A repo whose owner was never learned adopts the first owner that asks.
 */
function repoForOwner(name: string, owner: string): Repo | null {
  const repo = reposByName.get(name);
  if (!repo) return null;
  learnViewer(owner);
  if (repo.owner === null) {
    repo.owner = owner;
  } else if (repo.owner !== owner) {
    return null;
  }
  return repo;
}

function storeObject(repo: Repo, type: ObjType, data: Buffer): string {
  const oid = hashObject(type, data);
  if (!repo.objects.has(oid)) {
    repo.objects.set(oid, { type, data });
    repo.packVersion += 1;
  }
  return oid;
}

/** Flatten a tree into path -> {oid, mode}, walking subtrees. */
function flattenTree(repo: Repo, treeOid: string, prefix: string, out: Map<string, { oid: string; mode: string }>): void {
  const tree = repo.objects.get(treeOid);
  if (!tree || tree.type !== 'tree') return;
  for (const entry of parseTree(tree.data)) {
    const path = prefix === '' ? entry.name : `${prefix}/${entry.name}`;
    if (entry.mode === '40000') flattenTree(repo, entry.oid, path, out);
    else out.set(path, { oid: entry.oid, mode: entry.mode });
  }
}

function flatTreeOfCommit(repo: Repo, commitOid: string): Map<string, { oid: string; mode: string }> {
  const out = new Map<string, { oid: string; mode: string }>();
  const commit = repo.objects.get(commitOid);
  if (!commit || commit.type !== 'commit') return out;
  flattenTree(repo, parseCommit(commit.data).tree, '', out);
  return out;
}

/** Build (and store) a tree object from a flat path map. */
function buildTreeFromFlat(repo: Repo, flat: Map<string, { oid: string; mode: string }>): string {
  interface Node {
    files: Map<string, { oid: string; mode: string }>;
    dirs: Map<string, Node>;
  }
  const make = (): Node => ({ files: new Map(), dirs: new Map() });
  const root = make();
  for (const [path, value] of flat) {
    const segments = path.split('/');
    let node = root;
    for (let i = 0; i < segments.length - 1; i += 1) {
      const name = segments[i];
      if (!node.dirs.has(name)) node.dirs.set(name, make());
      node = node.dirs.get(name)!;
    }
    node.files.set(segments[segments.length - 1], value);
  }
  const build = (node: Node): string => {
    const entries: TreeEntry[] = [];
    for (const [name, value] of node.files) entries.push({ mode: value.mode, name, oid: value.oid });
    for (const [name, child] of node.dirs) entries.push({ mode: '40000', name, oid: build(child) });
    return storeObject(repo, 'tree', buildTree(entries));
  };
  return build(root);
}

/** Create a commit object on `repo` and store it; returns its oid. */
function makeCommit(repo: Repo, treeOid: string, parents: string[], message: string): string {
  const epoch = tickEpoch();
  const who = `forge <forge@example.invalid> ${epoch} +0000`;
  const lines = [`tree ${treeOid}`];
  for (const parent of parents) lines.push(`parent ${parent}`);
  lines.push(`author ${who}`, `committer ${who}`, '');
  const text = message.endsWith('\n') ? message : `${message}\n`;
  return storeObject(repo, 'commit', Buffer.from(`${lines.join('\n')}\n${text}`, 'utf8'));
}

/** Resolve a ref-ish (branch name, full ref, or oid) to a commit oid, or null. */
function resolveRef(repo: Repo, refish: string): string | null {
  if (isOid(refish)) return repo.objects.has(refish) ? refish : null;
  const candidates = [
    refish,
    `refs/heads/${refish}`,
    `refs/tags/${refish}`,
  ];
  for (const candidate of candidates) {
    const oid = repo.refs.get(candidate);
    if (oid) {
      const object = repo.objects.get(oid);
      if (object && object.type === 'tag') return parseTag(object.data).object;
      return oid;
    }
  }
  return null;
}

/** The tip commit oid of a branch (refs/heads/<branch>), or null. */
function branchTip(repo: Repo, branch: string): string | null {
  const oid = repo.refs.get(`refs/heads/${branch}`);
  return oid ?? null;
}

/** Commits reachable from `tip`, newest first (BFS by parent links). */
function commitsFrom(repo: Repo, tip: string): string[] {
  const out: string[] = [];
  const seen = new Set<string>();
  const queue = [tip];
  while (queue.length > 0) {
    const oid = queue.shift()!;
    if (seen.has(oid)) continue;
    seen.add(oid);
    const object = repo.objects.get(oid);
    if (!object || object.type !== 'commit') continue;
    out.push(oid);
    for (const parent of parseCommit(object.data).parents) queue.push(parent);
  }
  return out;
}

/** Peel a ref oid to its commit (annotated tags unwrap one level at a time). */
function peelToCommit(repo: Repo, oid: string): string {
  let current = oid;
  for (let i = 0; i < 8; i += 1) {
    const object = repo.objects.get(current);
    if (!object || object.type !== 'tag') break;
    current = parseTag(object.data).object;
  }
  return current;
}

// ---------------------------------------------------------------------------
// HTTP helpers
// ---------------------------------------------------------------------------

function sendJson(res: ServerResponse, status: number, body: unknown, headers: Record<string, string> = {}): void {
  requestCounter += 1;
  const text = status === 204 ? '' : `${JSON.stringify(body)}\n`;
  const out: Record<string, string> = {
    'x-github-request-id': `req-${requestCounter}`,
    ...headers,
  };
  if (status !== 204) {
    out['content-type'] = JSON_TYPE;
    out['content-length'] = String(Buffer.byteLength(text));
  }
  res.writeHead(status, out);
  res.end(text);
}

function sendRaw(res: ServerResponse, status: number, body: Buffer, contentType: string): void {
  res.writeHead(status, { 'content-type': contentType, 'content-length': String(body.length) });
  res.end(body);
}

function readBody(req: IncomingMessage): Promise<Buffer> {
  return new Promise((resolve, reject) => {
    const chunks: Buffer[] = [];
    req.on('data', (chunk: Buffer) => chunks.push(chunk));
    req.on('end', () => resolve(Buffer.concat(chunks)));
    req.on('error', reject);
  });
}

function pathOf(req: IncomingMessage): string {
  try {
    return new URL(req.url ?? '/', 'http://forge').pathname;
  } catch {
    return '/';
  }
}

function queryOf(req: IncomingMessage): URLSearchParams {
  try {
    return new URL(req.url ?? '/', 'http://forge').searchParams;
  } catch {
    return new URLSearchParams();
  }
}

/** Split a pathname into decoded segments (empty segments dropped). */
function segmentsOf(path: string): string[] {
  const out: string[] = [];
  for (const piece of path.split('/')) {
    if (piece === '') continue;
    try {
      out.push(decodeURIComponent(piece));
    } catch {
      out.push(piece);
    }
  }
  return out;
}

function bearerToken(req: IncomingMessage): string | null {
  const header = req.headers.authorization ?? '';
  const match = /^Bearer\s+(.+)$/.exec(header);
  return match ? match[1]! : null;
}

function authed(req: IncomingMessage): boolean {
  if (TOKEN === '') return true;
  const token = bearerToken(req);
  return token !== null && token === TOKEN;
}

function repoJson(repo: Repo): Record<string, unknown> {
  const owner = repo.owner ?? viewerLogin ?? 'viewer';
  return {
    id: repo.id,
    node_id: globalId('Repository', String(repo.id)),
    name: repo.name,
    full_name: `${owner}/${repo.name}`,
    owner: { login: owner, id: 1, type: 'User' },
    private: repo.priv,
    description: repo.description,
    default_branch: repo.defaultBranch,
    html_url: `https://example.invalid/${owner}/${repo.name}`,
    url: `/api/v3/repos/${owner}/${repo.name}`,
    created_at: isoOf(repo.createdEpoch),
    updated_at: isoOf(repo.createdEpoch),
    has_issues: true,
    has_projects: false,
    has_wiki: false,
    forks_count: 0,
    open_issues_count: repo.issues.filter((issue) => issue.state === 'open').length,
  };
}

function issueJson(repo: Repo, issue: Issue): Record<string, unknown> {
  const owner = repo.owner ?? viewerLogin ?? 'viewer';
  return {
    id: issue.id,
    node_id: globalId('Issue', `${repo.id}:${issue.number}`),
    number: issue.number,
    title: issue.title,
    body: issue.body,
    state: issue.state,
    labels: issue.labels.map((name) => {
      const label = repo.labels.get(name);
      return { name, color: label?.color ?? 'ededed', description: label?.description ?? '' };
    }),
    user: { login: owner, id: 1, type: 'User' },
    created_at: isoOf(issue.createdEpoch),
    updated_at: isoOf(issue.createdEpoch),
    comments: issue.comments.length,
    html_url: `https://example.invalid/${owner}/${repo.name}/issues/${issue.number}`,
    url: `/api/v3/repos/${owner}/${repo.name}/issues/${issue.number}`,
  };
}

function pullJson(repo: Repo, pull: Pull): Record<string, unknown> {
  const owner = repo.owner ?? viewerLogin ?? 'viewer';
  return {
    id: pull.id,
    node_id: globalId('PullRequest', `${repo.id}:${pull.number}`),
    number: pull.number,
    title: pull.title,
    body: pull.body,
    state: pull.state,
    merged: pull.merged,
    merged_at: pull.merged ? pull.mergedAt : null,
    merge_commit_sha: pull.merged ? pull.mergeCommitSha : null,
    mergeable: prMergeable(repo, pull) === 'MERGEABLE',
    head: { ref: pull.headRef, sha: pull.headSha, label: `${owner}:${pull.headRef}` },
    base: { ref: pull.baseRef, sha: pull.baseSha, label: `${owner}:${pull.baseRef}` },
    user: { login: owner, id: 1, type: 'User' },
    created_at: isoOf(pull.createdEpoch),
    updated_at: isoOf(pull.createdEpoch),
    html_url: `https://example.invalid/${owner}/${repo.name}/pull/${pull.number}`,
    url: `/api/v3/repos/${owner}/${repo.name}/pulls/${pull.number}`,
  };
}

/** 'MERGEABLE' | 'CONFLICTING': a file changed on both sides of the merge-base differently. */
function prMergeable(repo: Repo, pull: Pull): 'MERGEABLE' | 'CONFLICTING' {
  const baseFlat = flatTreeOfCommit(repo, pull.mergeBaseSha);
  const headFlat = flatTreeOfCommit(repo, pull.headSha);
  const currentBaseTip = branchTip(repo, pull.baseRef);
  const currentFlat = currentBaseTip ? flatTreeOfCommit(repo, currentBaseTip) : baseFlat;
  const paths = new Set([...baseFlat.keys(), ...headFlat.keys(), ...currentFlat.keys()]);
  for (const path of paths) {
    const baseOid = baseFlat.get(path)?.oid ?? null;
    const headOid = headFlat.get(path)?.oid ?? null;
    const currentOid = currentFlat.get(path)?.oid ?? null;
    if (headOid !== baseOid && currentOid !== baseOid && headOid !== currentOid) return 'CONFLICTING';
  }
  return 'MERGEABLE';
}

/** Files changed between the merge-base tree and the head tree. */
function prFiles(repo: Repo, pull: Pull): Array<{ filename: string; status: string; additions: number; deletions: number; changes: number }> {
  const baseFlat = flatTreeOfCommit(repo, pull.mergeBaseSha);
  const headFlat = flatTreeOfCommit(repo, pull.headSha);
  const paths = new Set([...baseFlat.keys(), ...headFlat.keys()]);
  const out: Array<{ filename: string; status: string; additions: number; deletions: number; changes: number }> = [];
  for (const path of [...paths].sort()) {
    const baseEntry = baseFlat.get(path);
    const headEntry = headFlat.get(path);
    if (!baseEntry && headEntry) {
      const blob = repo.objects.get(headEntry.oid);
      const lines = blob ? blob.data.toString('utf8').split('\n').length : 0;
      out.push({ filename: path, status: 'added', additions: Math.max(1, lines), deletions: 0, changes: Math.max(1, lines) });
    } else if (baseEntry && !headEntry) {
      const blob = repo.objects.get(baseEntry.oid);
      const lines = blob ? blob.data.toString('utf8').split('\n').length : 0;
      out.push({ filename: path, status: 'removed', additions: 0, deletions: Math.max(1, lines), changes: Math.max(1, lines) });
    } else if (baseEntry && headEntry && baseEntry.oid !== headEntry.oid) {
      const oldBlob = repo.objects.get(baseEntry.oid);
      const newBlob = repo.objects.get(headEntry.oid);
      const oldLines = oldBlob ? oldBlob.data.toString('utf8').split('\n').length : 0;
      const newLines = newBlob ? newBlob.data.toString('utf8').split('\n').length : 0;
      const additions = Math.max(1, newLines);
      const deletions = Math.max(0, oldLines);
      out.push({ filename: path, status: 'modified', additions, deletions, changes: additions + deletions });
    }
  }
  return out;
}

/** Squash-merge a pull request onto its base branch; returns the merge commit oid or null on conflict. */
function mergePullRequest(repo: Repo, pull: Pull): string | null {
  if (prMergeable(repo, pull) === 'CONFLICTING') return null;
  const baseTip = branchTip(repo, pull.baseRef);
  if (!baseTip) return null;
  const baseFlat = flatTreeOfCommit(repo, baseTip);
  const mergeBaseFlat = flatTreeOfCommit(repo, pull.mergeBaseSha);
  const headFlat = flatTreeOfCommit(repo, pull.headSha);
  const merged = new Map(baseFlat);
  for (const [path, entry] of headFlat) {
    if (mergeBaseFlat.get(path)?.oid !== entry.oid) merged.set(path, entry);
  }
  for (const path of mergeBaseFlat.keys()) {
    if (!headFlat.has(path)) merged.delete(path);
  }
  const treeOid = buildTreeFromFlat(repo, merged);
  const epoch = tickEpoch();
  const commitOid = makeCommit(repo, treeOid, [baseTip], `Merge pull request #${pull.number} from ${pull.headRef}\n\n${pull.title}`);
  repo.refs.set(`refs/heads/${pull.baseRef}`, commitOid);
  pull.headSha = branchTip(repo, pull.headRef) ?? pull.headSha;
  pull.baseSha = commitOid;
  pull.state = 'closed';
  pull.merged = true;
  pull.mergedAt = isoOf(epoch);
  pull.mergeCommitSha = commitOid;
  return commitOid;
}

/** Create an issue on a repo (shared numbering with pull requests). */
function createIssueRecord(repo: Repo, title: string, body: string, labels: string[]): Issue {
  const epoch = tickEpoch();
  const issue: Issue = {
    id: allocId(),
    number: repo.nextNumber,
    title,
    body,
    state: 'open',
    labels: [...labels],
    seq: repo.nextNumber,
    createdEpoch: epoch,
    comments: [],
  };
  repo.nextNumber += 1;
  repo.issues.push(issue);
  return issue;
}

function createPullRecord(repo: Repo, title: string, body: string, headRef: string, baseRef: string): Pull | null {
  const headSha = branchTip(repo, headRef);
  const baseSha = branchTip(repo, baseRef);
  if (!headSha || !baseSha) return null;
  const epoch = tickEpoch();
  const pull: Pull = {
    id: allocId(),
    number: repo.nextNumber,
    title,
    body,
    state: 'open',
    merged: false,
    mergedAt: '',
    mergeCommitSha: '',
    headRef,
    baseRef,
    headSha,
    baseSha,
    mergeBaseSha: baseSha,
    seq: repo.nextNumber,
    createdEpoch: epoch,
  };
  repo.nextNumber += 1;
  repo.pulls.push(pull);
  return pull;
}

// ---------------------------------------------------------------------------
// git smart HTTP
// ---------------------------------------------------------------------------

function sortedRefs(repo: Repo): Array<{ name: string; oid: string }> {
  const out: Array<{ name: string; oid: string }> = [];
  for (const [name, oid] of repo.refs) out.push({ name, oid });
  out.sort((a, b) => (a.name < b.name ? -1 : a.name > b.name ? 1 : 0));
  return out;
}

/** The v0 ref advertisement body for a service, with the service preamble. */
function v0Advertisement(repo: Repo, service: 'git-upload-pack' | 'git-receive-pack'): Buffer {
  const parts: Buffer[] = [];
  parts.push(pktLine(`# service=${service}\n`));
  parts.push(PKT_FLUSH);
  const caps =
    service === 'git-upload-pack'
      ? 'side-band-64k thin-pack ofs-delta multi_ack multi_ack_detailed shallow filter agent=forge/1.0 symref=HEAD:refs/heads/main'
      : 'report-status report-status-v2 side-band-64k delete-refs ofs-delta thin-pack agent=forge/1.0 symref=HEAD:refs/heads/main';
  const refs = sortedRefs(repo);
  const headOid = repo.refs.get('refs/heads/main') ?? ZERO_OID;
  if (refs.length === 0) {
    parts.push(pktLine(`${ZERO_OID} capabilities^{}\u0000${caps}\n`));
  } else {
    let first = true;
    const headLine = `${headOid} HEAD${first ? `\u0000${caps}` : ''}\n`;
    parts.push(pktLine(headLine));
    first = false;
    for (const ref of refs) {
      const suffix = first ? `\u0000${caps}` : '';
      parts.push(pktLine(`${ref.oid} ${ref.name}${suffix}\n`));
      first = false;
      const object = repo.objects.get(ref.oid);
      if (ref.name.startsWith('refs/tags/') && object && object.type === 'tag') {
        parts.push(pktLine(`${peelToCommit(repo, ref.oid)} ${ref.name}^{}\n`));
      }
    }
  }
  parts.push(PKT_FLUSH);
  return Buffer.concat(parts);
}

function v2Advertisement(): Buffer {
  const parts: Buffer[] = [
    pktLine('version 2\n'),
    pktLine('ls-refs=unborn\n'),
    pktLine('fetch=shallow wait-for-done filter\n'),
    pktLine('object-format=sha1\n'),
    pktLine(`agent=${AGENT_NAME}\n`),
    PKT_FLUSH,
  ];
  return Buffer.concat(parts);
}

function handleInfoRefs(req: IncomingMessage, res: ServerResponse, repo: Repo, service: 'git-upload-pack' | 'git-receive-pack'): void {
  const wantsV2 = service === 'git-upload-pack' && (req.headers['git-protocol'] ?? '') === 'version=2';
  const body = wantsV2 ? v2Advertisement() : v0Advertisement(repo, service);
  sendRaw(res, 200, body, `application/x-${service}-advertisement`);
}

interface LsRefLine {
  oid: string;
  name: string;
  symrefTarget?: string;
  peeled?: string;
  unborn?: boolean;
}

/** The refs a v2 ls-refs answer lists, before prefix filtering. */
function lsRefsLines(repo: Repo): LsRefLine[] {
  const out: LsRefLine[] = [];
  const headOid = repo.refs.get('refs/heads/main');
  if (headOid) {
    out.push({ oid: headOid, name: 'HEAD', symrefTarget: 'refs/heads/main' });
  } else {
    out.push({ oid: ZERO_OID, name: 'HEAD', symrefTarget: 'refs/heads/main', unborn: true });
  }
  for (const ref of sortedRefs(repo)) {
    const line: LsRefLine = { oid: ref.oid, name: ref.name };
    if (ref.name === 'refs/heads/main') line.symrefTarget = undefined;
    const object = repo.objects.get(ref.oid);
    if (ref.name.startsWith('refs/tags/') && object && object.type === 'tag') {
      line.peeled = peelToCommit(repo, ref.oid);
    }
    out.push(line);
  }
  return out;
}

function handleLsRefs(repo: Repo, args: string[]): Buffer {
  const peel = args.includes('peel');
  const symrefs = args.includes('symrefs');
  const prefixes: string[] = [];
  for (const arg of args) {
    if (arg.startsWith('ref-prefix ')) prefixes.push(arg.slice('ref-prefix '.length));
  }
  const keep = (name: string): boolean => prefixes.length === 0 || prefixes.some((prefix) => name.startsWith(prefix));
  const parts: Buffer[] = [];
  for (const ref of lsRefsLines(repo)) {
    if (!keep(ref.name)) continue;
    if (ref.unborn) {
      parts.push(pktLine(`unborn ${ref.name}${symrefs && ref.symrefTarget ? ` symref-target:${ref.symrefTarget}` : ''}\n`));
      continue;
    }
    let line = `${ref.oid} ${ref.name}`;
    if (symrefs && ref.symrefTarget) line += ` symref-target:${ref.symrefTarget}`;
    if (peel && ref.peeled) line += ` peeled:${ref.peeled}`;
    parts.push(pktLine(`${line}\n`));
  }
  parts.push(PKT_FLUSH);
  return Buffer.concat(parts);
}

interface FetchPlan {
  /** Commit oids to include (depth-limited when `depth` is set). */
  commits: Set<string>;
  /** Boundary commits: included commits with a parent outside the set. */
  shallow: string[];
  /** Previously shallow commits that are now fully included. */
  unshallow: string[];
  /** Objects to pack: the included commits' trees plus any wanted tag objects. */
  objects: GitObject[];
}

/** Plan a fetch: which commits (and therefore objects) to send.
 *
 * The object set is built from the included commits' own trees only — never
 * by walking parents past the included set — and anything the client
 * already holds (reachable from its haves) is left out. That is what keeps
 * a shallow clone at depth 1 and an incremental fetch from re-sending the
 * old tip. */
function planFetch(repo: Repo, wants: string[], haves: string[], shallowIn: string[], depth: number | null): FetchPlan {
  const lookup = (oid: string): GitObject | undefined => repo.objects.get(oid);
  const wantCommits = wants.map((oid) => peelToCommit(repo, oid)).filter((oid) => {
    const object = lookup(oid);
    return object !== undefined && object.type === 'commit';
  });
  // Commits reachable from `roots` by following parent links only.
  const parentClosure = (roots: readonly string[]): Set<string> => {
    const out = new Set<string>();
    const queue = [...roots];
    while (queue.length > 0) {
      const oid = queue.pop()!;
      if (out.has(oid)) continue;
      const object = lookup(oid);
      if (!object || object.type !== 'commit') continue;
      out.add(oid);
      for (const parent of parseCommit(object.data).parents) queue.push(parent);
    }
    return out;
  };
  const included = new Set<string>();
  if (depth !== null) {
    // Breadth-first from the wants, at most `depth` generations deep.
    const queue: Array<{ oid: string; dist: number }> = wantCommits.map((oid) => ({ oid, dist: 0 }));
    const seen = new Set<string>();
    while (queue.length > 0) {
      const { oid, dist } = queue.shift()!;
      if (seen.has(oid) || dist >= depth) continue;
      seen.add(oid);
      const object = lookup(oid);
      if (!object || object.type !== 'commit') continue;
      included.add(oid);
      if (dist + 1 < depth) {
        for (const parent of parseCommit(object.data).parents) queue.push({ oid: parent, dist: dist + 1 });
      }
    }
  } else {
    const wanted = parentClosure(wantCommits);
    const held = parentClosure(haves.map((oid) => peelToCommit(repo, oid)));
    for (const oid of wanted) if (!held.has(oid)) included.add(oid);
  }
  const shallow: string[] = [];
  for (const oid of included) {
    const object = lookup(oid);
    if (!object || object.type !== 'commit') continue;
    const parents = parseCommit(object.data).parents;
    if (parents.some((parent) => !included.has(parent))) shallow.push(oid);
  }
  const unshallow: string[] = [];
  for (const boundary of shallowIn) {
    if (!included.has(boundary)) continue;
    const object = lookup(boundary);
    if (!object || object.type !== 'commit') continue;
    const parents = parseCommit(object.data).parents;
    if (parents.every((parent) => included.has(parent))) unshallow.push(boundary);
  }
  // Objects the client already holds. In a normal fetch a have means the
  // client holds that commit's whole history, so the full closure applies.
  // In a depth-limited fetch a have is a shallow boundary: the client holds
  // that commit and its tree, but NOT its parents — walking past the
  // boundary would mark the very commits a deepen is asking for as held.
  const heldObjects = new Set<string>();
  if (depth === null) {
    for (const oid of collectReachable(haves, lookup)) heldObjects.add(oid);
  } else {
    for (const oid of haves) {
      const object = lookup(oid);
      if (!object) continue;
      heldObjects.add(oid);
      if (object.type === 'commit') {
        const treeOid = parseCommit(object.data).tree;
        heldObjects.add(treeOid);
        const addHeldTree = (tree: string): void => {
          const treeObject = lookup(tree);
          if (!treeObject || treeObject.type !== 'tree') return;
          for (const entry of parseTree(treeObject.data)) {
            heldObjects.add(entry.oid);
            if (entry.mode === '40000') addHeldTree(entry.oid);
          }
        };
        addHeldTree(treeOid);
      }
    }
  }
  const send = new Set<string>();
  const addTree = (treeOid: string): void => {
    const tree = lookup(treeOid);
    if (!tree || tree.type !== 'tree') return;
    send.add(treeOid);
    for (const entry of parseTree(tree.data)) {
      if (entry.mode === '40000') addTree(entry.oid);
      else send.add(entry.oid);
    }
  };
  for (const oid of included) {
    send.add(oid);
    const object = lookup(oid);
    if (object && object.type === 'commit') addTree(parseCommit(object.data).tree);
  }
  // A wanted tag (or tree/blob) travels with its own object, even though it
  // is not a commit; its target is already covered when it is a commit.
  for (const oid of wants) {
    const object = lookup(oid);
    if (!object) continue;
    if (object.type === 'tag') {
      send.add(oid);
      const target = parseTag(object.data).object;
      const targetObject = lookup(target);
      if (targetObject && targetObject.type === 'tree') addTree(target);
      else if (targetObject) send.add(target);
    } else if (object.type !== 'commit') {
      send.add(oid);
      if (object.type === 'tree') addTree(oid);
    }
  }
  for (const oid of heldObjects) send.delete(oid);
  const objects: GitObject[] = [];
  for (const oid of send) {
    const object = lookup(oid);
    if (object) objects.push(object);
  }
  return { commits: included, shallow, unshallow, objects };
}

function sidebandPack(pack: Buffer): Buffer {
  const parts: Buffer[] = [];
  const CHUNK = 65515;
  for (let offset = 0; offset < pack.length; offset += CHUNK) {
    const slice = pack.subarray(offset, Math.min(pack.length, offset + CHUNK));
    parts.push(pktLine(Buffer.concat([Buffer.from([1]), slice])));
  }
  return Buffer.concat(parts);
}

function handleFetchV2(repo: Repo, args: string[]): Buffer {
  const wants: string[] = [];
  const haves: string[] = [];
  const shallowIn: string[] = [];
  let depth: number | null = null;
  for (const arg of args) {
    if (arg.startsWith('want ')) wants.push(arg.slice(5).trim());
    else if (arg.startsWith('have ')) haves.push(arg.slice(5).trim());
    else if (arg.startsWith('shallow ')) shallowIn.push(arg.slice(8).trim());
    else if (arg.startsWith('deepen ')) depth = Number.parseInt(arg.slice(7).trim(), 10);
  }
  // The response is a pure function of the parsed fetch args and the object
  // store; identical fetches (e.g. 50 concurrent shallow clones of one tip)
  // reuse the built pack instead of re-walking and re-deflating it.
  const cacheKey = `v2|${wants.join(',')}|${haves.join(',')}|${shallowIn.join(',')}|${depth}`;
  const cachedV2 = repo.fetchCache;
  if (cachedV2 !== null && cachedV2.key === cacheKey && cachedV2.version === repo.packVersion) return cachedV2.body;
  const plan = planFetch(repo, wants, haves, shallowIn, depth);
  const pack = writePack(plan.objects);
  const parts: Buffer[] = [];
  parts.push(pktLine('acknowledgments\n'));
  parts.push(pktLine('NAK\n'));
  parts.push(PKT_FLUSH);
  if (plan.shallow.length > 0 || plan.unshallow.length > 0) {
    parts.push(pktLine('shallow-info\n'));
    for (const oid of plan.shallow) parts.push(pktLine(`shallow ${oid}\n`));
    for (const oid of plan.unshallow) parts.push(pktLine(`unshallow ${oid}\n`));
    parts.push(PKT_FLUSH);
  }
  parts.push(pktLine('packfile\n'));
  parts.push(sidebandPack(pack));
  parts.push(PKT_FLUSH);
  const bodyV2 = Buffer.concat(parts);
  repo.fetchCache = { key: cacheKey, version: repo.packVersion, body: bodyV2 };
  return bodyV2;
}

function handleFetchV0(repo: Repo, lines: string[]): Buffer {
  const wants: string[] = [];
  const haves: string[] = [];
  const shallowIn: string[] = [];
  let depth: number | null = null;
  for (const line of lines) {
    const text = line.replace(/\n$/, '');
    if (text.startsWith('want ')) wants.push(text.slice(5).split(' ')[0]!);
    else if (text.startsWith('have ')) haves.push(text.slice(5).trim());
    else if (text.startsWith('shallow ')) shallowIn.push(text.slice(8).trim());
    else if (text.startsWith('deepen ')) depth = Number.parseInt(text.slice(7).trim(), 10);
  }
  const cacheKey = `v0|${wants.join(',')}|${haves.join(',')}|${shallowIn.join(',')}|${depth}`;
  const cachedV0 = repo.fetchCache;
  if (cachedV0 !== null && cachedV0.key === cacheKey && cachedV0.version === repo.packVersion) return cachedV0.body;
  const plan = planFetch(repo, wants, haves, shallowIn, depth);
  const pack = writePack(plan.objects);
  const parts: Buffer[] = [pktLine('NAK\n')];
  for (const oid of plan.shallow) parts.push(pktLine(`shallow ${oid}\n`));
  for (const oid of plan.unshallow) parts.push(pktLine(`unshallow ${oid}\n`));
  parts.push(PKT_FLUSH);
  parts.push(sidebandPack(pack));
  parts.push(PKT_FLUSH);
  const bodyV0 = Buffer.concat(parts);
  repo.fetchCache = { key: cacheKey, version: repo.packVersion, body: bodyV0 };
  return bodyV0;
}

function handleUploadPack(req: IncomingMessage, res: ServerResponse, repo: Repo, body: Buffer): void {
  const isV2 = (req.headers['git-protocol'] ?? '') === 'version=2';
  const decoded = decodePktLines(body);
  if (!decoded.ok && decoded.packets.length === 0) {
    sendJson(res, 400, { message: 'malformed pkt-line stream' });
    return;
  }
  const lines = pktLinesText(decoded.packets);
  if (isV2) {
    const commandLine = lines[0] ?? '';
    const delimIndex = decoded.packets.findIndex((packet) => packet.kind === 'delim');
    const argPackets = delimIndex >= 0 ? decoded.packets.slice(delimIndex + 1) : decoded.packets.slice(1);
    const args = pktLinesText(argPackets).map((line) => line.replace(/\n$/, ''));
    if (commandLine.startsWith('command=ls-refs')) {
      sendRaw(res, 200, handleLsRefs(repo, args), 'application/x-git-upload-pack-result');
      return;
    }
    if (commandLine.startsWith('command=fetch')) {
      sendRaw(res, 200, handleFetchV2(repo, args), 'application/x-git-upload-pack-result');
      return;
    }
    sendJson(res, 400, { message: `unknown v2 command ${commandLine.trim()}` });
    return;
  }
  sendRaw(res, 200, handleFetchV0(repo, lines), 'application/x-git-upload-pack-result');
}

interface PushCommand {
  oldOid: string;
  newOid: string;
  ref: string;
}

function handleReceivePack(req: IncomingMessage, res: ServerResponse, repo: Repo, body: Buffer): void {
  const decoded = decodePktLines(body);
  if (!decoded.ok && decoded.packets.length === 0) {
    sendJson(res, 400, { message: 'malformed pkt-line stream' });
    return;
  }
  const commands: PushCommand[] = [];
  for (const packet of decoded.packets) {
    if (packet.kind === 'flush') break;
    if (packet.kind !== 'data') continue;
    const text = packet.payload.toString('utf8').replace(/\n$/, '');
    const nul = text.indexOf('\u0000');
    const head = nul >= 0 ? text.slice(0, nul) : text;
    const parts = head.split(' ');
    if (parts.length >= 3 && isOid(parts[0]) && isOid(parts[1])) {
      commands.push({ oldOid: parts[0]!, newOid: parts[1]!, ref: parts[2]! });
    }
  }
  // Locate the byte just past the flush packet that ends the command list.
  let offset = 0;
  let flushEnd = -1;
  while (offset + 4 <= body.length) {
    const head = body.subarray(offset, offset + 4).toString('ascii');
    if (!/^[0-9a-fA-F]{4}$/.test(head)) break;
    const length = Number.parseInt(head, 16);
    if (length === 0) {
      flushEnd = offset + 4;
      break;
    }
    if (length < 4 || offset + length > body.length) break;
    offset += length;
  }
  let unpackOk = true;
  let unpackDetail = 'ok';
  if (flushEnd >= 0 && flushEnd < body.length) {
    try {
      const pack = readPack(body.subarray(flushEnd), (oid) => repo.objects.get(oid));
      for (const [oid, object] of pack.objects) {
        if (!repo.objects.has(oid)) {
          repo.objects.set(oid, object);
          repo.packVersion += 1;
        }
      }
    } catch (err) {
      unpackOk = false;
      unpackDetail = err instanceof Error ? err.message : 'unpack failed';
    }
  }
  const reportLines: string[] = [];
  reportLines.push(`unpack ${unpackOk ? 'ok' : unpackDetail}\n`);
  const lookup = (oid: string): GitObject | undefined => repo.objects.get(oid);
  for (const command of commands) {
    const current = repo.refs.get(command.ref);
    if (!unpackOk) {
      reportLines.push(`ng ${command.ref} unpacker error\n`);
      continue;
    }
    if (command.newOid === ZERO_OID) {
      // Delete.
      if (current === undefined) {
        reportLines.push(`ng ${command.ref} no such ref\n`);
      } else if (command.oldOid !== ZERO_OID && current !== command.oldOid) {
        reportLines.push(`ng ${command.ref} non-fast-forward\n`);
      } else {
        repo.refs.delete(command.ref);
        reportLines.push(`ok ${command.ref}\n`);
      }
      continue;
    }
    if (!repo.objects.has(command.newOid)) {
      reportLines.push(`ng ${command.ref} object not found\n`);
      continue;
    }
    if (current === undefined) {
      if (command.oldOid !== ZERO_OID) {
        reportLines.push(`ng ${command.ref} non-fast-forward\n`);
        continue;
      }
      repo.refs.set(command.ref, command.newOid);
      reportLines.push(`ok ${command.ref}\n`);
      continue;
    }
    if (current !== command.oldOid) {
      reportLines.push(`ng ${command.ref} non-fast-forward\n`);
      continue;
    }
    if (!isAncestor(lookup, current, command.newOid)) {
      reportLines.push(`ng ${command.ref} non-fast-forward\n`);
      continue;
    }
    repo.refs.set(command.ref, command.newOid);
    reportLines.push(`ok ${command.ref}\n`);
  }
  const reportBody = Buffer.concat(reportLines.map((line) => pktLine(line)));
  const parts: Buffer[] = [];
  parts.push(pktLine(Buffer.concat([Buffer.from([1]), reportBody])));
  parts.push(PKT_FLUSH);
  sendRaw(res, 200, Buffer.concat(parts), 'application/x-git-receive-pack-result');
}

// ---------------------------------------------------------------------------
// REST v3
// ---------------------------------------------------------------------------

type JsonRecord = Record<string, unknown>;

function jsonBodyOf(text: string): { ok: true; value: unknown } | { ok: false } {
  if (text.trim() === '') return { ok: true, value: {} };
  try {
    return { ok: true, value: JSON.parse(text) };
  } catch {
    return { ok: false };
  }
}

function asRecord(value: unknown): JsonRecord {
  return typeof value === 'object' && value !== null && !Array.isArray(value) ? (value as JsonRecord) : {};
}

function strField(value: unknown, field: string): string {
  const record = asRecord(value);
  return typeof record[field] === 'string' ? (record[field] as string) : '';
}

function paginate<T>(items: readonly T[], query: URLSearchParams): { page: T[]; hasNext: boolean; nextPage: number; perPage: number; pageNum: number } {
  const perPage = Math.max(1, Math.min(100, Number.parseInt(query.get('per_page') ?? '30', 10) || 30));
  const pageNum = Math.max(1, Number.parseInt(query.get('page') ?? '1', 10) || 1);
  const start = (pageNum - 1) * perPage;
  const page = items.slice(start, start + perPage);
  return { page, hasNext: start + perPage < items.length, nextPage: pageNum + 1, perPage, pageNum };
}

function linkHeader(req: IncomingMessage, query: URLSearchParams, hasNext: boolean, nextPage: number, perPage: number): string | null {
  if (!hasNext) return null;
  const host = req.headers.host ?? '127.0.0.1';
  const path = pathOf(req);
  const params = new URLSearchParams(query);
  params.set('page', String(nextPage));
  params.set('per_page', String(perPage));
  return `<http://${host}${path}?${params.toString()}>; rel="next"`;
}

/** Commit a file change on a branch through the contents model; returns the commit oid. */
function contentsCommit(repo: Repo, branch: string, path: string, content: Buffer, message: string): { commitOid: string; blobOid: string; isNew: boolean } {
  const tip = branchTip(repo, branch);
  const flat = tip ? flatTreeOfCommit(repo, tip) : new Map<string, { oid: string; mode: string }>();
  const isNew = !flat.has(path);
  const blobOid = storeObject(repo, 'blob', content);
  flat.set(path, { oid: blobOid, mode: '100644' });
  const treeOid = buildTreeFromFlat(repo, flat);
  const parents = tip ? [tip] : [];
  const commitOid = makeCommit(repo, treeOid, parents, message);
  repo.refs.set(`refs/heads/${branch}`, commitOid);
  return { commitOid, blobOid, isNew };
}

/** Delete a file on a branch; returns the commit oid, or null when the file is absent. */
function contentsDelete(repo: Repo, branch: string, path: string, message: string): string | null {
  const tip = branchTip(repo, branch);
  if (!tip) return null;
  const flat = flatTreeOfCommit(repo, tip);
  if (!flat.has(path)) return null;
  flat.delete(path);
  const treeOid = buildTreeFromFlat(repo, flat);
  const commitOid = makeCommit(repo, treeOid, [tip], message);
  repo.refs.set(`refs/heads/${branch}`, commitOid);
  return commitOid;
}

async function handleRest(req: IncomingMessage, res: ServerResponse): Promise<void> {
  const method = req.method ?? 'GET';
  const path = pathOf(req);
  const query = queryOf(req);
  const segments = segmentsOf(path);
  // segments[0] = 'api', segments[1] = 'v3', the rest is the route.
  const route = segments.slice(2);
  const rawBody = ['POST', 'PUT', 'PATCH', 'DELETE'].includes(method) ? await readBody(req) : Buffer.alloc(0);
  if (rawBody.length > 0) {
    const parsed = jsonBodyOf(rawBody.toString('utf8'));
    if (!parsed.ok) {
      sendJson(res, 400, { message: 'Invalid JSON body' });
      return;
    }
    (req as unknown as { __json: unknown }).__json = parsed.value;
  } else {
    (req as unknown as { __json: unknown }).__json = {};
  }
  const body = (req as unknown as { __json: unknown }).__json;
  const bodyRecord = asRecord(body);

  if (!authed(req)) {
    sendJson(res, 401, { message: 'Requires authentication' });
    return;
  }

  // GET /api/v3/ — the API root.
  if (method === 'GET' && route.length === 0) {
    sendJson(res, 200, { current_user_url: '/api/v3/user', rate_limit_url: '/api/v3/rate_limit' }, { 'x-oauth-scopes': 'repo, read:org' });
    return;
  }

  // GET /api/v3/meta
  if (method === 'GET' && route.length === 1 && route[0] === 'meta') {
    sendJson(res, 200, { verifiable_password_authentication: true, installed_version: '1.0.0' });
    return;
  }

  // GET /api/v3/user
  if (method === 'GET' && route.length === 1 && route[0] === 'user') {
    const login = viewerLogin ?? 'viewer';
    sendJson(res, 200, { login, id: 1, type: 'User', name: login });
    return;
  }

  // GET /api/v3/user/repos  |  POST /api/v3/user/repos
  if (route.length === 2 && route[0] === 'user' && route[1] === 'repos') {
    if (method === 'GET') {
      const all = [...reposByName.values()].sort((a, b) => a.seq - b.seq).map(repoJson);
      const { page, hasNext, nextPage, perPage } = paginate(all, query);
      const link = linkHeader(req, query, hasNext, nextPage, perPage);
      sendJson(res, 200, page, link ? { link } : {});
      return;
    }
    if (method === 'POST') {
      const name = strField(body, 'name');
      if (name === '') {
        sendJson(res, 422, { message: 'Validation Failed: name is required' });
        return;
      }
      if (reposByName.has(name)) {
        sendJson(res, 422, { message: 'Repository already exists' });
        return;
      }
      const repo = createRepoRecord(name, strField(body, 'description'), bodyRecord.private === true);
      sendJson(res, 201, repoJson(repo));
      return;
    }
  }

  // /api/v3/repos/{owner}/{repo}...
  if (route.length >= 3 && route[0] === 'repos') {
    const owner = route[1]!;
    const repoName = route[2]!;
    const rest = route.slice(3);

    // GET /repos/{o}/{r}
    if (rest.length === 0) {
      const repo = repoForOwner(repoName, owner);
      if (!repo) {
        sendJson(res, 404, { message: 'Not Found' });
        return;
      }
      if (method === 'GET') {
        sendJson(res, 200, repoJson(repo));
        return;
      }
      if (method === 'PATCH') {
        const description = strField(body, 'description');
        if (description !== '') repo.description = description;
        if (typeof bodyRecord.private === 'boolean') repo.priv = bodyRecord.private;
        sendJson(res, 200, repoJson(repo));
        return;
      }
      if (method === 'DELETE') {
        reposByName.delete(repoName);
        sendJson(res, 204, null);
        return;
      }
    }

    const repo = repoForOwner(repoName, owner);
    if (!repo) {
      sendJson(res, 404, { message: 'Not Found' });
      return;
    }

    // GET /repos/{o}/{r}/branches
    if (method === 'GET' && rest.length === 1 && rest[0] === 'branches') {
      const branches = [...repo.refs.keys()]
        .filter((name) => name.startsWith('refs/heads/'))
        .map((name) => name.slice('refs/heads/'.length))
        .sort()
        .map((name) => ({ name, commit: { sha: repo.refs.get(`refs/heads/${name}`) ?? '' }, protected: false }));
      sendJson(res, 200, branches);
      return;
    }

    // GET /repos/{o}/{r}/branches/{branch}
    if (method === 'GET' && rest.length === 2 && rest[0] === 'branches') {
      const tip = branchTip(repo, rest[1]!);
      if (!tip) {
        sendJson(res, 404, { message: 'Not Found' });
        return;
      }
      sendJson(res, 200, { name: rest[1], commit: { sha: tip }, protected: false });
      return;
    }

    // GET /repos/{o}/{r}/commits[?sha=]
    if (method === 'GET' && rest.length === 1 && rest[0] === 'commits') {
      const refish = query.get('sha') ?? repo.defaultBranch;
      const tip = resolveRef(repo, refish);
      if (!tip) {
        sendJson(res, 200, []);
        return;
      }
      const commits = commitsFrom(repo, tip).map((oid) => {
        const commit = parseCommit(repo.objects.get(oid)!.data);
        return {
          sha: oid,
          commit: {
            message: commit.message.replace(/\n+$/, ''),
            author: { name: 'forge', email: 'forge@example.invalid', date: isoOf(repo.createdEpoch) },
            committer: { name: 'forge', email: 'forge@example.invalid', date: isoOf(repo.createdEpoch) },
          },
          author: { login: viewerLogin ?? 'viewer' },
        };
      });
      sendJson(res, 200, commits);
      return;
    }

    // POST /repos/{o}/{r}/git/refs
    if (method === 'POST' && rest.length === 2 && rest[0] === 'git' && rest[1] === 'refs') {
      const ref = strField(body, 'ref');
      const sha = strField(body, 'sha');
      if (!ref.startsWith('refs/') || !isOid(sha) || !repo.objects.has(sha)) {
        sendJson(res, 422, { message: 'Validation Failed' });
        return;
      }
      repo.refs.set(ref, sha);
      sendJson(res, 201, { ref, object: { sha, type: 'commit' } });
      return;
    }

    // GET /repos/{o}/{r}/git/refs/heads/{branch}
    if (method === 'GET' && rest.length >= 3 && rest[0] === 'git' && rest[1] === 'refs') {
      const ref = `refs/${rest.slice(2).join('/')}`;
      const oid = repo.refs.get(ref);
      if (!oid) {
        sendJson(res, 404, { message: 'Not Found' });
        return;
      }
      sendJson(res, 200, { ref, object: { sha: oid, type: 'commit' } });
      return;
    }

    // Contents: /repos/{o}/{r}/contents/{path...}
    if (rest.length >= 1 && rest[0] === 'contents') {
      const contentPath = rest.slice(1).join('/');
      const refish = query.get('ref') ?? repo.defaultBranch;
      if (method === 'PUT') {
        const branch = strField(body, 'branch') || repo.defaultBranch;
        const message = strField(body, 'message') || 'Update file';
        const contentB64 = strField(body, 'content');
        const sha = strField(body, 'sha');
        let effectiveBranch = branch;
        if (!repo.refs.has(`refs/heads/${branch}`)) {
          if (repo.refs.size === 0) {
            // Unborn repository: the first contents write creates the branch.
            effectiveBranch = branch;
          } else if (branch !== repo.defaultBranch) {
            // A new branch starts from the default branch tip.
            const baseTip = branchTip(repo, repo.defaultBranch);
            if (baseTip) repo.refs.set(`refs/heads/${branch}`, baseTip);
            effectiveBranch = branch;
          }
        }
        const tip = branchTip(repo, effectiveBranch);
        if (sha !== '' && tip) {
          const flat = flatTreeOfCommit(repo, tip);
          const current = flat.get(contentPath);
          if (!current || current.oid !== sha) {
            sendJson(res, 409, { message: 'Conflict: sha does not match the current file' });
            return;
          }
        }
        const content = b64decode(contentB64);
        const { commitOid, blobOid, isNew } = contentsCommit(repo, effectiveBranch, contentPath, content, message);
        sendJson(res, isNew ? 201 : 200, {
          content: {
            name: contentPath.split('/').pop() ?? contentPath,
            path: contentPath,
            sha: blobOid,
            size: content.length,
            type: 'file',
            encoding: 'base64',
            content: contentB64,
          },
          commit: { sha: commitOid, message },
        });
        return;
      }
      if (method === 'GET') {
        const tip = resolveRef(repo, refish);
        if (!tip) {
          sendJson(res, 404, { message: 'Not Found' });
          return;
        }
        const flat = flatTreeOfCommit(repo, tip);
        const entry = flat.get(contentPath);
        if (entry) {
          const blob = repo.objects.get(entry.oid);
          const bytes = blob ? blob.data : Buffer.alloc(0);
          sendJson(res, 200, {
            type: 'file',
            encoding: 'base64',
            content: bytes.toString('base64'),
            sha: entry.oid,
            size: bytes.length,
            name: contentPath.split('/').pop() ?? contentPath,
            path: contentPath,
          });
          return;
        }
        // Directory listing: entries directly under contentPath.
        const prefix = contentPath === '' ? '' : `${contentPath}/`;
        const children = new Map<string, { type: string; oid: string; path: string }>();
        for (const [path, value] of flat) {
          if (contentPath !== '' && !path.startsWith(prefix)) continue;
          const restPath = contentPath === '' ? path : path.slice(prefix.length);
          const first = restPath.split('/')[0]!;
          if (restPath.includes('/')) {
            if (!children.has(first)) children.set(first, { type: 'dir', oid: '', path: `${prefix}${first}` });
          } else {
            children.set(first, { type: 'file', oid: value.oid, path });
          }
        }
        if (children.size === 0) {
          sendJson(res, 404, { message: 'Not Found' });
          return;
        }
        const listing = [...children.entries()]
          .sort(([a], [b]) => (a < b ? -1 : 1))
          .map(([name, child]) => ({ type: child.type, name, path: child.path, sha: child.oid || '0'.repeat(40) }));
        sendJson(res, 200, listing);
        return;
      }
      if (method === 'DELETE') {
        const branch = strField(body, 'branch') || repo.defaultBranch;
        const message = strField(body, 'message') || 'Delete file';
        const commitOid = contentsDelete(repo, branch, contentPath, message);
        if (!commitOid) {
          sendJson(res, 404, { message: 'Not Found' });
          return;
        }
        sendJson(res, 200, { commit: { sha: commitOid, message } });
        return;
      }
    }

    // POST /repos/{o}/{r}/labels
    if (method === 'POST' && rest.length === 1 && rest[0] === 'labels') {
      const name = strField(body, 'name');
      if (name === '') {
        sendJson(res, 422, { message: 'Validation Failed: name is required' });
        return;
      }
      const label: Label = {
        name,
        color: strField(body, 'color') || 'ededed',
        description: strField(body, 'description'),
      };
      repo.labels.set(name, label);
      sendJson(res, 201, { name: label.name, color: label.color, description: label.description });
      return;
    }

    // Issues: /repos/{o}/{r}/issues[/{n}[/comments]]
    if (rest.length >= 1 && rest[0] === 'issues') {
      if (rest.length === 1) {
        if (method === 'POST') {
          const title = strField(body, 'title');
          const bodyText = strField(body, 'body');
          const rawLabels = bodyRecord.labels;
          const labelNames: string[] = [];
          if (Array.isArray(rawLabels)) {
            for (const entry of rawLabels) {
              if (typeof entry === 'string') labelNames.push(entry);
              else if (typeof entry === 'object' && entry !== null) labelNames.push(strField(entry, 'name'));
            }
          }
          for (const name of labelNames) {
            if (!repo.labels.has(name)) {
              sendJson(res, 422, { message: `Validation Failed: label "${name}" does not exist` });
              return;
            }
          }
          const issue = createIssueRecord(repo, title, bodyText, labelNames);
          sendJson(res, 201, issueJson(repo, issue));
          return;
        }
        if (method === 'GET') {
          const state = (query.get('state') ?? 'open').toLowerCase();
          const sort = (query.get('sort') ?? 'created').toLowerCase();
          const direction = (query.get('direction') ?? 'desc').toLowerCase();
          let list = [...repo.issues];
          if (state === 'open') list = list.filter((issue) => issue.state === 'open');
          else if (state === 'closed') list = list.filter((issue) => issue.state === 'closed');
          if (sort === 'created') {
            list.sort((a, b) => (direction === 'asc' ? a.seq - b.seq : b.seq - a.seq));
          }
          const { page, hasNext, nextPage, perPage } = paginate(list.map((issue) => issueJson(repo, issue)), query);
          const link = linkHeader(req, query, hasNext, nextPage, perPage);
          sendJson(res, 200, page, link ? { link } : {});
          return;
        }
      }
      const number = Number.parseInt(rest[1] ?? '', 10);
      const issue = repo.issues.find((entry) => entry.number === number);
      if (rest.length === 2) {
        if (!issue) {
          sendJson(res, 404, { message: 'Not Found' });
          return;
        }
        if (method === 'GET') {
          sendJson(res, 200, issueJson(repo, issue));
          return;
        }
        if (method === 'PATCH') {
          const state = strField(body, 'state');
          if (state === 'open' || state === 'closed') issue.state = state;
          const title = strField(body, 'title');
          if (title !== '') issue.title = title;
          const bodyText = strField(body, 'body');
          if (bodyText !== '') issue.body = bodyText;
          sendJson(res, 200, issueJson(repo, issue));
          return;
        }
      }
      if (rest.length === 3 && rest[2] === 'comments') {
        if (!issue) {
          sendJson(res, 404, { message: 'Not Found' });
          return;
        }
        if (method === 'POST') {
          const commentBody = strField(body, 'body');
          const comment: Comment = { id: repo.nextCommentId, body: commentBody, createdEpoch: tickEpoch() };
          repo.nextCommentId += 1;
          issue.comments.push(comment);
          sendJson(res, 201, { id: comment.id, body: comment.body, created_at: isoOf(comment.createdEpoch) });
          return;
        }
        if (method === 'GET') {
          sendJson(res, 200, issue.comments.map((comment) => ({ id: comment.id, body: comment.body, created_at: isoOf(comment.createdEpoch) })));
          return;
        }
      }
    }

    // Pulls: /repos/{o}/{r}/pulls[/{n}[/files|/merge]]
    if (rest.length >= 1 && rest[0] === 'pulls') {
      if (rest.length === 1) {
        if (method === 'POST') {
          const title = strField(body, 'title');
          const bodyText = strField(body, 'body');
          const head = strField(body, 'head');
          const base = strField(body, 'base') || repo.defaultBranch;
          const pull = createPullRecord(repo, title, bodyText, head, base);
          if (!pull) {
            sendJson(res, 422, { message: 'Validation Failed: head or base branch does not exist' });
            return;
          }
          sendJson(res, 201, pullJson(repo, pull));
          return;
        }
        if (method === 'GET') {
          const state = (query.get('state') ?? 'open').toLowerCase();
          let list = [...repo.pulls];
          if (state === 'open') list = list.filter((pull) => pull.state === 'open');
          else if (state === 'closed') list = list.filter((pull) => pull.state === 'closed');
          list.sort((a, b) => b.seq - a.seq);
          const { page, hasNext, nextPage, perPage } = paginate(list.map((pull) => pullJson(repo, pull)), query);
          const link = linkHeader(req, query, hasNext, nextPage, perPage);
          sendJson(res, 200, page, link ? { link } : {});
          return;
        }
      }
      const number = Number.parseInt(rest[1] ?? '', 10);
      const pull = repo.pulls.find((entry) => entry.number === number);
      if (rest.length === 2) {
        if (!pull || method !== 'GET') {
          sendJson(res, 404, { message: 'Not Found' });
          return;
        }
        sendJson(res, 200, pullJson(repo, pull));
        return;
      }
      if (rest.length === 3 && rest[2] === 'files') {
        if (!pull) {
          sendJson(res, 404, { message: 'Not Found' });
          return;
        }
        sendJson(res, 200, prFiles(repo, pull));
        return;
      }
      if (rest.length === 3 && rest[2] === 'merge') {
        if (!pull) {
          sendJson(res, 404, { message: 'Not Found' });
          return;
        }
        if (method !== 'PUT') {
          sendJson(res, 404, { message: 'Not Found' });
          return;
        }
        if (pull.merged) {
          sendJson(res, 200, { sha: pull.mergeCommitSha, merged: true, message: 'Pull request successfully merged' });
          return;
        }
        const sha = mergePullRequest(repo, pull);
        if (!sha) {
          sendJson(res, 405, { message: 'Merge conflict: the pull request cannot be merged cleanly' });
          return;
        }
        sendJson(res, 200, { sha, merged: true, message: 'Pull request successfully merged' });
        return;
      }
    }
  }

  sendJson(res, 404, { message: 'Not Found' });
}

// ---------------------------------------------------------------------------
// GraphQL v4
// ---------------------------------------------------------------------------

interface GqlField {
  alias: string | null;
  name: string;
  args: Record<string, unknown>;
  selection: GqlSelection[] | null;
  fragmentType: string | null;
}

type GqlSelection = GqlField;

interface GqlOperation {
  type: 'query' | 'mutation';
  name: string | null;
  selection: GqlSelection[];
}

class GqlTokenizer {
  private pos = 0;
  private readonly text: string;
  constructor(text: string) {
    this.text = text;
  }

  tokenize(): string[] {
    const tokens: string[] = [];
    const text = this.text;
    while (this.pos < text.length) {
      const ch = text[this.pos]!;
      if (ch === ' ' || ch === '\n' || ch === '\r' || ch === '\t' || ch === ',') {
        this.pos += 1;
        continue;
      }
      if (ch === '#') {
        while (this.pos < text.length && text[this.pos] !== '\n') this.pos += 1;
        continue;
      }
      if (ch === '.' && text.startsWith('...', this.pos)) {
        tokens.push('...');
        this.pos += 3;
        continue;
      }
      if ('{}()[]:!=$'.includes(ch)) {
        tokens.push(ch);
        this.pos += 1;
        continue;
      }
      if (ch === '"') {
        let out = '';
        this.pos += 1;
        while (this.pos < text.length && text[this.pos] !== '"') {
          if (text[this.pos] === '\\' && this.pos + 1 < text.length) {
            const next = text[this.pos + 1]!;
            out += next === 'n' ? '\n' : next === 't' ? '\t' : next === 'r' ? '\r' : next;
            this.pos += 2;
          } else {
            out += text[this.pos];
            this.pos += 1;
          }
        }
        this.pos += 1;
        tokens.push(JSON.stringify(out));
        continue;
      }
      if (/[0-9-]/.test(ch)) {
        let start = this.pos;
        while (this.pos < text.length && /[0-9.]/.test(text[this.pos]!)) this.pos += 1;
        tokens.push(text.slice(start, this.pos));
        continue;
      }
      if (/[A-Za-z_]/.test(ch)) {
        let start = this.pos;
        while (this.pos < text.length && /[A-Za-z0-9_]/.test(text[this.pos]!)) this.pos += 1;
        tokens.push(text.slice(start, this.pos));
        continue;
      }
      this.pos += 1;
    }
    return tokens;
  }
}

class GqlParser {
  private pos = 0;
  private readonly tokens: string[];
  constructor(tokens: string[]) {
    this.tokens = tokens;
  }

  private peek(): string | undefined {
    return this.tokens[this.pos];
  }

  private next(): string {
    return this.tokens[this.pos++] ?? '';
  }

  private expect(token: string): void {
    if (this.next() !== token) throw new Error(`expected ${token}`);
  }

  parseDocument(): GqlOperation[] {
    const operations: GqlOperation[] = [];
    while (this.pos < this.tokens.length) {
      const token = this.peek();
      if (token === 'query' || token === 'mutation') {
        const type = this.next() as 'query' | 'mutation';
        let name: string | null = null;
        if (this.peek() !== undefined && this.peek() !== '{' && this.peek() !== '(') name = this.next();
        if (this.peek() === '(') this.skipParens();
        const selection = this.parseSelectionSet();
        operations.push({ type, name, selection });
      } else if (token === '{') {
        operations.push({ type: 'query', name: null, selection: this.parseSelectionSet() });
      } else {
        this.pos += 1;
      }
    }
    return operations;
  }

  private skipParens(): void {
    let depth = 0;
    while (this.pos < this.tokens.length) {
      const token = this.next();
      if (token === '(') depth += 1;
      else if (token === ')') {
        depth -= 1;
        if (depth === 0) break;
      }
    }
  }

  private parseSelectionSet(): GqlSelection[] {
    this.expect('{');
    const fields: GqlSelection[] = [];
    while (this.peek() !== undefined && this.peek() !== '}') {
      fields.push(this.parseField());
    }
    this.expect('}');
    return fields;
  }

  private parseField(): GqlField {
    if (this.peek() === '...') {
      this.next();
      let fragmentType: string | null = null;
      if (this.peek() === 'on') {
        this.next();
        fragmentType = this.next();
      }
      const selection = this.parseSelectionSet();
      return { alias: null, name: '__fragment', args: {}, selection, fragmentType };
    }
    let name = this.next();
    let alias: string | null = null;
    if (this.peek() === ':') {
      this.next();
      alias = name;
      name = this.next();
    }
    let args: Record<string, unknown> = {};
    if (this.peek() === '(') args = this.parseArgs();
    let selection: GqlSelection[] | null = null;
    if (this.peek() === '{') selection = this.parseSelectionSet();
    return { alias, name, args, selection, fragmentType: null };
  }

  private parseArgs(): Record<string, unknown> {
    this.expect('(');
    const args: Record<string, unknown> = {};
    while (this.peek() !== undefined && this.peek() !== ')') {
      const key = this.next();
      this.expect(':');
      args[key] = this.parseValue();
    }
    this.expect(')');
    return args;
  }

  private parseValue(): unknown {
    const token = this.next();
    if (token === '$') return { __var: this.next() };
    if (token === '[') {
      const list: unknown[] = [];
      while (this.peek() !== undefined && this.peek() !== ']') list.push(this.parseValue());
      this.expect(']');
      return list;
    }
    if (token === '{') {
      const object: Record<string, unknown> = {};
      while (this.peek() !== undefined && this.peek() !== '}') {
        const key = this.next();
        this.expect(':');
        object[key] = this.parseValue();
      }
      this.expect('}');
      return object;
    }
    if (token.startsWith('"')) return JSON.parse(token) as string;
    if (token === 'true') return true;
    if (token === 'false') return false;
    if (token === 'null') return null;
    if (/^-?\d+$/.test(token)) return Number.parseInt(token, 10);
    if (/^-?\d+\.\d+$/.test(token)) return Number.parseFloat(token);
    return token;
  }
}

function resolveVariables(value: unknown, variables: Record<string, unknown>): unknown {
  if (value !== null && typeof value === 'object') {
    if ('__var' in (value as Record<string, unknown>)) {
      const name = (value as { __var: string }).__var;
      return variables[name] ?? null;
    }
    if (Array.isArray(value)) return value.map((entry) => resolveVariables(entry, variables));
    const out: Record<string, unknown> = {};
    for (const [key, entry] of Object.entries(value as Record<string, unknown>)) out[key] = resolveVariables(entry, variables);
    return out;
  }
  return value;
}

const TYPE_FIELDS: Record<string, readonly string[]> = {
  Query: ['viewer', 'repository', 'node', '__type', '__schema'],
  Mutation: ['createIssue', 'closeIssue', 'createPullRequest', 'mergePullRequest', 'addComment'],
  User: ['login', 'id'],
  Repository: ['id', 'databaseId', 'name', 'nameWithOwner', 'owner', 'defaultBranchRef', 'viewerPermission', 'hasIssuesEnabled', 'issue', 'issues', 'pullRequests', 'pullRequest', 'description', 'createdAt', 'url'],
  Issue: ['id', 'number', 'title', 'state', 'body', 'createdAt', 'url', 'author', 'labels', 'comments'],
  PullRequest: ['id', 'number', 'title', 'body', 'state', 'merged', 'mergeable', 'headRefName', 'baseRefName', 'headRefOid', 'files', 'createdAt', 'url', 'author'],
  IssueConnection: ['nodes', 'edges', 'pageInfo', 'totalCount'],
  PullRequestConnection: ['nodes', 'edges', 'pageInfo', 'totalCount'],
  PullRequestChangedFile: ['path', 'filename', 'additions', 'deletions', 'changes', 'status'],
  Ref: ['name'],
  __Type: ['name', 'kind', 'fields', 'enumValues', 'description'],
  __Field: ['name', 'description'],
  __EnumValue: ['name', 'description'],
  PageInfo: ['hasNextPage', 'endCursor', 'hasPreviousPage', 'startCursor'],
  CreateIssuePayload: ['issue', 'clientMutationId'],
  CloseIssuePayload: ['issue', 'clientMutationId'],
  CreatePullRequestPayload: ['pullRequest', 'clientMutationId'],
  MergePullRequestPayload: ['pullRequest', 'clientMutationId'],
  AddCommentPayload: ['commentEdge', 'comment', 'clientMutationId'],
  IssueCommentEdge: ['node', 'cursor'],
  IssueComment: ['id', 'body', 'author'],
};

const INTROSPECTION_FIELDS: Record<string, string[]> = {
  Issue: ['id', 'number', 'title', 'state', 'body', 'createdAt', 'updatedAt', 'author', 'labels', 'comments', 'url', 'closedAt'],
  PullRequest: ['id', 'number', 'title', 'body', 'state', 'merged', 'mergeable', 'headRefName', 'baseRefName', 'headRefOid', 'files', 'createdAt', 'updatedAt', 'author', 'labels', 'url'],
  Repository: ['id', 'databaseId', 'name', 'nameWithOwner', 'owner', 'defaultBranchRef', 'viewerPermission', 'hasIssuesEnabled', 'issue', 'issues', 'pullRequests', 'pullRequest', 'description', 'createdAt', 'url', 'defaultBranch'],
  SearchType: [],
};

const INTROSPECTION_ENUMS: Record<string, string[]> = {
  SearchType: ['ISSUE', 'REPOSITORY', 'USER', 'DISCUSSION', 'COMMIT', 'CODE', 'WIKI', 'PACKAGE'],
  IssueState: ['OPEN', 'CLOSED'],
  PullRequestState: ['OPEN', 'CLOSED', 'MERGED'],
  MergeableState: ['MERGEABLE', 'CONFLICTING', 'UNKNOWN'],
  OrderDirection: ['ASC', 'DESC'],
  IssueOrderField: ['CREATED_AT', 'UPDATED_AT', 'COMMENTS'],
};

interface GqlNode {
  __type: string;
  value: unknown;
}

function repoById(id: number): Repo | null {
  for (const repo of reposByName.values()) if (repo.id === id) return repo;
  return null;
}

function issueByGlobalId(id: string): { repo: Repo; issue: Issue } | null {
  const parsed = parseGlobalId(id);
  if (!parsed || parsed.kind !== 'Issue') return null;
  const [repoId, number] = parsed.payload.split(':');
  const repo = repoById(Number(repoId));
  if (!repo) return null;
  const issue = repo.issues.find((entry) => entry.number === Number(number));
  return issue ? { repo, issue } : null;
}

function pullByGlobalId(id: string): { repo: Repo; pull: Pull } | null {
  const parsed = parseGlobalId(id);
  if (!parsed || parsed.kind !== 'PullRequest') return null;
  const [repoId, number] = parsed.payload.split(':');
  const repo = repoById(Number(repoId));
  if (!repo) return null;
  const pull = repo.pulls.find((entry) => entry.number === Number(number));
  return pull ? { repo, pull } : null;
}

function issueCursor(number: number): string {
  return Buffer.from(`cursor:${number}`, 'utf8').toString('base64');
}

function cursorNumber(cursor: string): number | null {
  try {
    const text = Buffer.from(cursor, 'base64').toString('utf8');
    if (!text.startsWith('cursor:')) return null;
    const value = Number.parseInt(text.slice(7), 10);
    return Number.isFinite(value) ? value : null;
  } catch {
    return null;
  }
}

class GqlExecutor {
  readonly errors: Array<{ message: string }> = [];
  private readonly variables: Record<string, unknown>;
  constructor(variables: Record<string, unknown>) {
    this.variables = variables;
  }

  private resolveArgs(field: GqlField): Record<string, unknown> {
    const out: Record<string, unknown> = {};
    for (const [key, value] of Object.entries(field.args)) out[key] = resolveVariables(value, this.variables);
    return out;
  }

  executeOperation(operation: GqlOperation): Record<string, unknown> {
    const rootType = operation.type === 'mutation' ? 'Mutation' : 'Query';
    const root: GqlNode = { __type: rootType, value: null };
    const data: Record<string, unknown> = {};
    for (const field of operation.selection) {
      const key = field.alias ?? field.name;
      data[key] = this.executeField(root, field);
    }
    return data;
  }

  private executeField(parent: GqlNode, field: GqlField): unknown {
    if (field.name === '__fragment') {
      if (field.fragmentType && field.fragmentType !== parent.__type) return undefined;
      const out: Record<string, unknown> = {};
      let any = false;
      for (const sub of field.selection ?? []) {
        const value = this.executeField(parent, sub);
        if (value !== undefined) {
          out[sub.alias ?? sub.name] = value;
          any = true;
        }
      }
      return any ? out : undefined;
    }
    if (field.name === '__typename') return parent.__type;
    const allowed = TYPE_FIELDS[parent.__type] ?? [];
    if (!allowed.includes(field.name)) {
      this.errors.push({ message: `Cannot query field "${field.name}" on type "${parent.__type}".` });
      return null;
    }
    const args = this.resolveArgs(field);
    const value = this.resolve(parent, field, args);
    if (value === undefined) return null;
    if (field.selection && Array.isArray(value)) {
      return value.map((entry) =>
        entry !== null && typeof entry === 'object' && '__type' in (entry as Record<string, unknown>)
          ? this.applySelection(entry as GqlNode, field.selection!)
          : entry,
      );
    }
    if (field.selection && value !== null && typeof value === 'object') {
      return this.applySelection(value as GqlNode, field.selection);
    }
    return value;
  }

  /** Apply a selection set to a node, merging fragment fields into the object. */
  private applySelection(node: GqlNode, selection: GqlSelection[]): Record<string, unknown> {
    const out: Record<string, unknown> = {};
    for (const field of selection) {
      const value = this.executeField(node, field);
      if (value === undefined) continue;
      if (field.name === '__fragment') {
        if (value !== null && typeof value === 'object') Object.assign(out, value);
        continue;
      }
      out[field.alias ?? field.name] = value;
    }
    return out;
  }

  private resolve(parent: GqlNode, field: GqlField, args: Record<string, unknown>): unknown {
    const type = parent.__type;
    const value = parent.value;
    if (type === 'Query') return this.resolveQuery(field, args);
    if (type === 'Mutation') return this.resolveMutation(field, args);
    if (type === 'User') {
      const user = value as { login: string };
      if (field.name === 'login') return user.login;
      if (field.name === 'id') return globalId('User', user.login);
      return null;
    }
    if (type === 'Repository') return this.resolveRepository(value as Repo, field, args);
    if (type === 'Issue') {
      const issue = (value as { repo: Repo; issue: Issue }).issue;
      const repo = (value as { repo: Repo; issue: Issue }).repo;
      if (field.name === 'id') return globalId('Issue', `${repo.id}:${issue.number}`);
      if (field.name === 'number') return issue.number;
      if (field.name === 'title') return issue.title;
      if (field.name === 'state') return issue.state === 'open' ? 'OPEN' : 'CLOSED';
      if (field.name === 'body') return issue.body;
      if (field.name === 'createdAt') return isoOf(issue.createdEpoch);
      if (field.name === 'url') return '';
      if (field.name === 'author') return { __type: 'User', value: { login: viewerLogin ?? 'viewer' } } as unknown as GqlNode;
      if (field.name === 'labels') return { __type: 'IssueConnection', value: [] };
      if (field.name === 'comments') return { __type: 'IssueConnection', value: [] };
      return null;
    }
    if (type === 'PullRequest') {
      const pull = (value as { repo: Repo; pull: Pull }).pull;
      const repo = (value as { repo: Repo; pull: Pull }).repo;
      if (field.name === 'id') return globalId('PullRequest', `${repo.id}:${pull.number}`);
      if (field.name === 'number') return pull.number;
      if (field.name === 'title') return pull.title;
      if (field.name === 'body') return pull.body;
      if (field.name === 'state') return pull.merged ? 'MERGED' : pull.state === 'open' ? 'OPEN' : 'CLOSED';
      if (field.name === 'merged') return pull.merged;
      if (field.name === 'mergeable') return prMergeable(repo, pull);
      if (field.name === 'headRefName') return pull.headRef;
      if (field.name === 'baseRefName') return pull.baseRef;
      if (field.name === 'headRefOid') return pull.headSha;
      if (field.name === 'createdAt') return isoOf(pull.createdEpoch);
      if (field.name === 'url') return '';
      if (field.name === 'author') return { __type: 'User', value: { login: viewerLogin ?? 'viewer' } } as unknown as GqlNode;
      if (field.name === 'files') {
        const first = typeof args.first === 'number' ? args.first : 100;
        const files = prFiles(repo, pull).slice(0, first);
        return {
          __type: 'PullRequestConnection',
          value: {
            nodes: files.map((file) => ({ __type: 'PullRequestChangedFile', value: file })),
            pageInfo: { hasNextPage: false, endCursor: null },
          },
        } as unknown as GqlNode;
      }
      return null;
    }
    if (type === 'IssueConnection' || type === 'PullRequestConnection') {
      const connection = value as { nodes: GqlNode[]; pageInfo: { hasNextPage: boolean; endCursor: string | null } };
      if (field.name === 'nodes') return connection.nodes;
      if (field.name === 'edges') return connection.nodes.map((node) => ({ __type: 'IssueCommentEdge', value: node }));
      if (field.name === 'totalCount') return connection.nodes.length;
      if (field.name === 'pageInfo') return { __type: 'PageInfo', value: connection.pageInfo } as unknown as GqlNode;
      return null;
    }
    if (type === 'PullRequestChangedFile') {
      const file = value as { filename: string; status: string; additions: number; deletions: number; changes: number };
      if (field.name === 'path' || field.name === 'filename') return file.filename;
      if (field.name === 'status') return file.status;
      if (field.name === 'additions') return file.additions;
      if (field.name === 'deletions') return file.deletions;
      if (field.name === 'changes') return file.changes;
      return null;
    }
    if (type === 'Ref') {
      if (field.name === 'name') return (value as { name: string }).name;
      return null;
    }
    if (type === '__Type') {
      const info = value as { name: string };
      if (field.name === 'name') return info.name;
      if (field.name === 'kind') return INTROSPECTION_ENUMS[info.name] ? 'ENUM' : 'OBJECT';
      if (field.name === 'fields') {
        return (INTROSPECTION_FIELDS[info.name] ?? []).map((name) => ({ __type: '__Field', value: { name } }));
      }
      if (field.name === 'enumValues') {
        return (INTROSPECTION_ENUMS[info.name] ?? []).map((name) => ({ __type: '__EnumValue', value: { name } }));
      }
      if (field.name === 'description') return null;
      return null;
    }
    if (type === '__Field' || type === '__EnumValue') {
      if (field.name === 'name') return (value as { name: string }).name;
      if (field.name === 'description') return null;
      return null;
    }
    if (type === 'PageInfo') {
      const info = value as { hasNextPage?: boolean; endCursor?: string | null; hasPreviousPage?: boolean; startCursor?: string | null };
      if (field.name === 'hasNextPage') return info.hasNextPage ?? false;
      if (field.name === 'endCursor') return info.endCursor ?? null;
      if (field.name === 'hasPreviousPage') return info.hasPreviousPage ?? false;
      if (field.name === 'startCursor') return info.startCursor ?? null;
      return null;
    }
    if (type === 'CreateIssuePayload' || type === 'CloseIssuePayload') {
      if (field.name === 'issue') return value as GqlNode;
      return null;
    }
    if (type === 'CreatePullRequestPayload' || type === 'MergePullRequestPayload') {
      if (field.name === 'pullRequest') return value as GqlNode;
      return null;
    }
    if (type === 'AddCommentPayload') {
      if (field.name === 'commentEdge') {
        return { __type: 'IssueCommentEdge', value: value as GqlNode } as unknown as GqlNode;
      }
      if (field.name === 'comment') return value as GqlNode;
      return null;
    }
    if (type === 'IssueCommentEdge') {
      if (field.name === 'node') return value as GqlNode;
      if (field.name === 'cursor') return '';
      return null;
    }
    if (type === 'IssueComment') {
      const comment = value as Comment;
      if (field.name === 'id') return globalId('IssueComment', String(comment.id));
      if (field.name === 'body') return comment.body;
      if (field.name === 'author') return { __type: 'User', value: { login: viewerLogin ?? 'viewer' } } as unknown as GqlNode;
      return null;
    }
    return null;
  }

  private resolveQuery(field: GqlField, args: Record<string, unknown>): unknown {
    if (field.name === 'viewer') {
      return { __type: 'User', value: { login: viewerLogin ?? 'viewer' } } as unknown as GqlNode;
    }
    if (field.name === 'repository') {
      const owner = String(args.owner ?? '');
      const name = String(args.name ?? '');
      const repo = repoForOwner(name, owner);
      if (!repo) return null;
      return { __type: 'Repository', value: repo } as unknown as GqlNode;
    }
    if (field.name === 'node') {
      const id = String(args.id ?? '');
      const parsed = parseGlobalId(id);
      if (!parsed) return null;
      if (parsed.kind === 'Repository') {
        const repo = repoById(Number(parsed.payload));
        if (!repo) return null;
        return { __type: 'Repository', value: repo } as unknown as GqlNode;
      }
      if (parsed.kind === 'Issue') {
        const found = issueByGlobalId(id);
        if (!found) return null;
        return { __type: 'Issue', value: found } as unknown as GqlNode;
      }
      if (parsed.kind === 'PullRequest') {
        const found = pullByGlobalId(id);
        if (!found) return null;
        return { __type: 'PullRequest', value: found } as unknown as GqlNode;
      }
      return null;
    }
    if (field.name === '__type') {
      const name = String(args.name ?? '');
      return { __type: '__Type', value: { name } } as unknown as GqlNode;
    }
    if (field.name === '__schema') {
      return { __type: '__Type', value: { name: 'Query' } } as unknown as GqlNode;
    }
    return null;
  }

  private resolveRepository(repo: Repo, field: GqlField, args: Record<string, unknown>): unknown {
    const owner = repo.owner ?? viewerLogin ?? 'viewer';
    if (field.name === 'id') return globalId('Repository', String(repo.id));
    if (field.name === 'databaseId') return repo.id;
    if (field.name === 'name') return repo.name;
    if (field.name === 'nameWithOwner') return `${owner}/${repo.name}`;
    if (field.name === 'owner') return { __type: 'User', value: { login: owner } } as unknown as GqlNode;
    if (field.name === 'defaultBranchRef') {
      return { __type: 'Ref', value: { name: repo.defaultBranch } } as unknown as GqlNode;
    }
    if (field.name === 'viewerPermission') return 'ADMIN';
    if (field.name === 'hasIssuesEnabled') return true;
    if (field.name === 'description') return repo.description;
    if (field.name === 'createdAt') return isoOf(repo.createdEpoch);
    if (field.name === 'url') return '';
    if (field.name === 'issue') {
      const number = Number(args.number);
      const issue = repo.issues.find((entry) => entry.number === number);
      if (!issue) return null;
      return { __type: 'Issue', value: { repo, issue } } as unknown as GqlNode;
    }
    if (field.name === 'issues') {
      let list = [...repo.issues];
      const states = args.states;
      if (Array.isArray(states) && states.length > 0) {
        const wanted = new Set(states.map((state) => String(state).toLowerCase()));
        list = list.filter((issue) => wanted.has(issue.state));
      }
      const orderBy = asRecord(args.orderBy);
      const direction = String(orderBy.direction ?? 'DESC').toUpperCase();
      list.sort((a, b) => {
        if (a.seq !== b.seq) return direction === 'DESC' ? b.seq - a.seq : a.seq - b.seq;
        return direction === 'DESC' ? b.number - a.number : a.number - b.number;
      });
      const first = typeof args.first === 'number' ? args.first : 100;
      let startIndex = 0;
      if (typeof args.after === 'string' && args.after !== '') {
        const afterNumber = cursorNumber(args.after);
        if (afterNumber !== null) {
          const index = list.findIndex((issue) => issue.number === afterNumber);
          if (index >= 0) startIndex = index + 1;
        }
      }
      const sliced = list.slice(startIndex, startIndex + first);
      const hasNextPage = startIndex + first < list.length;
      const endCursor = sliced.length > 0 ? issueCursor(sliced[sliced.length - 1]!.number) : null;
      return {
        __type: 'IssueConnection',
        value: {
          nodes: sliced.map((issue) => ({ __type: 'Issue', value: { repo, issue } }) as GqlNode),
          pageInfo: { hasNextPage, endCursor },
        },
      } as unknown as GqlNode;
    }
    if (field.name === 'pullRequests') {
      const first = typeof args.first === 'number' ? args.first : 100;
      const list = [...repo.pulls].sort((a, b) => b.seq - a.seq).slice(0, first);
      return {
        __type: 'PullRequestConnection',
        value: {
          nodes: list.map((pull) => ({ __type: 'PullRequest', value: { repo, pull } }) as GqlNode),
          pageInfo: { hasNextPage: false, endCursor: null },
        },
      } as unknown as GqlNode;
    }
    if (field.name === 'pullRequest') {
      const number = Number(args.number);
      const pull = repo.pulls.find((entry) => entry.number === number);
      if (!pull) return null;
      return { __type: 'PullRequest', value: { repo, pull } } as unknown as GqlNode;
    }
    return null;
  }

  private resolveMutation(field: GqlField, args: Record<string, unknown>): unknown {
    const input = asRecord(args.input);
    if (field.name === 'createIssue') {
      const repoId = Number(parseGlobalId(String(input.repositoryId ?? ''))?.payload ?? NaN);
      const repo = repoById(repoId);
      if (!repo) {
        this.errors.push({ message: 'createIssue: repository not found' });
        return null;
      }
      const issue = createIssueRecord(repo, String(input.title ?? ''), String(input.body ?? ''), []);
      return { __type: 'CreateIssuePayload', value: { __type: 'Issue', value: { repo, issue } } } as unknown as GqlNode;
    }
    if (field.name === 'closeIssue') {
      const found = issueByGlobalId(String(input.issueId ?? ''));
      if (!found) {
        this.errors.push({ message: 'closeIssue: issue not found' });
        return null;
      }
      found.issue.state = 'closed';
      return { __type: 'CloseIssuePayload', value: { __type: 'Issue', value: found } } as unknown as GqlNode;
    }
    if (field.name === 'createPullRequest') {
      const repoId = Number(parseGlobalId(String(input.repositoryId ?? ''))?.payload ?? NaN);
      const repo = repoById(repoId);
      if (!repo) {
        this.errors.push({ message: 'createPullRequest: repository not found' });
        return null;
      }
      const pull = createPullRecord(repo, String(input.title ?? ''), String(input.body ?? ''), String(input.headRefName ?? ''), String(input.baseRefName ?? ''));
      if (!pull) {
        this.errors.push({ message: 'createPullRequest: head or base branch does not exist' });
        return null;
      }
      return { __type: 'CreatePullRequestPayload', value: { __type: 'PullRequest', value: { repo, pull } } } as unknown as GqlNode;
    }
    if (field.name === 'mergePullRequest') {
      const found = pullByGlobalId(String(input.pullRequestId ?? ''));
      if (!found) {
        this.errors.push({ message: 'mergePullRequest: pull request not found' });
        return null;
      }
      const sha = mergePullRequest(found.repo, found.pull);
      if (!sha) {
        this.errors.push({ message: 'mergePullRequest: merge conflict' });
        return null;
      }
      return { __type: 'MergePullRequestPayload', value: { __type: 'PullRequest', value: found } } as unknown as GqlNode;
    }
    if (field.name === 'addComment') {
      const found = issueByGlobalId(String(input.subjectId ?? ''));
      if (!found) {
        this.errors.push({ message: 'addComment: subject not found' });
        return null;
      }
      const comment: Comment = { id: found.repo.nextCommentId, body: String(input.body ?? ''), createdEpoch: tickEpoch() };
      found.repo.nextCommentId += 1;
      found.issue.comments.push(comment);
      return { __type: 'AddCommentPayload', value: { __type: 'IssueComment', value: comment } } as unknown as GqlNode;
    }
    return null;
  }
}

function runGraphQLOperation(query: string, variables: Record<string, unknown>, operationName?: string): { data: Record<string, unknown> | null; errors: Array<{ message: string }> } {
  const tokens = new GqlTokenizer(query).tokenize();
  const operations = new GqlParser(tokens).parseDocument();
  if (operations.length === 0) return { data: null, errors: [{ message: 'No operation found in query' }] };
  let operation = operations[0]!;
  if (operationName) {
    const named = operations.find((entry) => entry.name === operationName);
    if (named) operation = named;
  }
  const executor = new GqlExecutor(variables);
  const data = executor.executeOperation(operation);
  return { data, errors: executor.errors };
}

async function handleGraphQL(req: IncomingMessage, res: ServerResponse): Promise<void> {
  if (!authed(req)) {
    sendJson(res, 401, { message: 'Requires authentication' });
    return;
  }
  const raw = await readBody(req);
  const parsed = jsonBodyOf(raw.toString('utf8'));
  if (!parsed.ok) {
    sendJson(res, 400, { message: 'Invalid JSON body' });
    return;
  }
  const value = parsed.value;
  const runOne = (entry: unknown): Record<string, unknown> => {
    const record = asRecord(entry);
    const query = typeof record.query === 'string' ? record.query : '';
    const variables = asRecord(record.variables);
    const operationName = typeof record.operationName === 'string' ? record.operationName : undefined;
    if (query === '') return { data: null, errors: [{ message: 'No query provided' }] };
    try {
      const result = runGraphQLOperation(query, variables, operationName);
      const out: Record<string, unknown> = { data: result.data };
      if (result.errors.length > 0) out.errors = result.errors;
      return out;
    } catch (err) {
      return { data: null, errors: [{ message: err instanceof Error ? err.message : String(err) }] };
    }
  };
  if (Array.isArray(value)) {
    sendJson(res, 200, value.map(runOne));
    return;
  }
  sendJson(res, 200, runOne(value));
}

// ---------------------------------------------------------------------------
// MCP over Streamable HTTP
// ---------------------------------------------------------------------------

const MCP_REVISION = '2026-07-28';
const MCP_SUPPORTED = ['2026-07-28', '2025-11-25', '2025-06-18', '2025-03-26', '2024-11-05'];

interface McpToolDef {
  name: string;
  description: string;
  inputSchema: {
    type: 'object';
    properties: Record<string, Record<string, unknown>>;
    required: string[];
  };
}

/** The tools list, built once so two tools/list calls answer byte for byte. */
const MCP_TOOLS: readonly McpToolDef[] = Object.freeze([
  Object.freeze({
    name: 'create_repo',
    description: 'Create a new repository owned by the authenticated user.',
    inputSchema: Object.freeze({
      type: 'object',
      properties: Object.freeze({
        name: Object.freeze({ type: 'string', description: 'The repository name.' }),
        description: Object.freeze({ type: 'string', description: 'A short description of the repository.' }),
        private: Object.freeze({ type: 'boolean', description: 'Whether the repository is private.' }),
      }),
      required: Object.freeze(['name']),
    }),
  }),
  Object.freeze({
    name: 'get_repo',
    description: 'Get a repository by owner and name.',
    inputSchema: Object.freeze({
      type: 'object',
      properties: Object.freeze({
        owner: Object.freeze({ type: 'string', description: 'The repository owner login.' }),
        repo: Object.freeze({ type: 'string', description: 'The repository name.' }),
        full_name: Object.freeze({ type: 'string', description: 'The repository full name, owner/repo.' }),
      }),
      required: Object.freeze(['owner', 'repo']),
    }),
  }),
  Object.freeze({
    name: 'create_issue',
    description: 'Create an issue in a repository.',
    inputSchema: Object.freeze({
      type: 'object',
      properties: Object.freeze({
        owner: Object.freeze({ type: 'string', description: 'The repository owner login.' }),
        repo: Object.freeze({ type: 'string', description: 'The repository name.' }),
        full_name: Object.freeze({ type: 'string', description: 'The repository full name, owner/repo.' }),
        title: Object.freeze({ type: 'string', description: 'The issue title.' }),
        body: Object.freeze({ type: 'string', description: 'The issue body.' }),
      }),
      required: Object.freeze(['owner', 'repo', 'title']),
    }),
  }),
  Object.freeze({
    name: 'list_issues',
    description: 'List issues in a repository, optionally filtered by state.',
    inputSchema: Object.freeze({
      type: 'object',
      properties: Object.freeze({
        owner: Object.freeze({ type: 'string', description: 'The repository owner login.' }),
        repo: Object.freeze({ type: 'string', description: 'The repository name.' }),
        full_name: Object.freeze({ type: 'string', description: 'The repository full name, owner/repo.' }),
        state: Object.freeze({ type: 'string', description: 'Issue state: open, closed or all.' }),
      }),
      required: Object.freeze(['owner', 'repo']),
    }),
  }),
  Object.freeze({
    name: 'create_pull_request',
    description: 'Create a pull request from a head branch into a base branch.',
    inputSchema: Object.freeze({
      type: 'object',
      properties: Object.freeze({
        owner: Object.freeze({ type: 'string', description: 'The repository owner login.' }),
        repo: Object.freeze({ type: 'string', description: 'The repository name.' }),
        full_name: Object.freeze({ type: 'string', description: 'The repository full name, owner/repo.' }),
        title: Object.freeze({ type: 'string', description: 'The pull request title.' }),
        body: Object.freeze({ type: 'string', description: 'The pull request body.' }),
        head: Object.freeze({ type: 'string', description: 'The head branch name.' }),
        base: Object.freeze({ type: 'string', description: 'The base branch name.' }),
      }),
      required: Object.freeze(['owner', 'repo', 'title', 'head', 'base']),
    }),
  }),
  Object.freeze({
    name: 'merge_pull_request',
    description: 'Merge a pull request by number.',
    inputSchema: Object.freeze({
      type: 'object',
      properties: Object.freeze({
        owner: Object.freeze({ type: 'string', description: 'The repository owner login.' }),
        repo: Object.freeze({ type: 'string', description: 'The repository name.' }),
        full_name: Object.freeze({ type: 'string', description: 'The repository full name, owner/repo.' }),
        pull_number: Object.freeze({ type: 'integer', description: 'The pull request number.' }),
      }),
      required: Object.freeze(['owner', 'repo', 'pull_number']),
    }),
  }),
]);

function mcpToolResult(payload: unknown): Record<string, unknown> {
  const text = typeof payload === 'string' ? payload : JSON.stringify(payload);
  return { content: [{ type: 'text', text }], structuredContent: payload, isError: false };
}

function mcpToolError(message: string): Record<string, unknown> {
  return { content: [{ type: 'text', text: message }], isError: true };
}

/** Split "owner/repo" from a full_name argument, or null. */
function splitFullName(args: Record<string, unknown>): { owner: string; repo: string } | null {
  const full = typeof args.full_name === 'string' ? args.full_name : '';
  const slash = full.indexOf('/');
  if (slash <= 0) return null;
  return { owner: full.slice(0, slash), repo: full.slice(slash + 1) };
}

function mcpOwnerRepo(args: Record<string, unknown>): { owner: string; repo: string } | null {
  const owner = typeof args.owner === 'string' && args.owner !== '' ? args.owner : '';
  const repo = typeof args.repo === 'string' && args.repo !== '' ? args.repo : '';
  if (owner !== '' && repo !== '') return { owner, repo };
  return splitFullName(args);
}

function mcpCallTool(name: string, args: Record<string, unknown>): { result?: Record<string, unknown>; error?: { code: number; message: string } } {
  const tool = MCP_TOOLS.find((entry) => entry.name === name);
  if (!tool) return { error: { code: -32601, message: `Method not found: ${name}` } };
  for (const required of tool.inputSchema.required) {
    if (required === 'owner' || required === 'repo') continue; // full_name may stand in
    if (args[required] === undefined || args[required] === null || args[required] === '') {
      return { result: mcpToolError(`Missing required argument: ${required}`) };
    }
  }
  if (name === 'create_repo') {
    const repoName = String(args.name ?? '');
    if (repoName === '') return { result: mcpToolError('Missing required argument: name') };
    if (reposByName.has(repoName)) {
      const existing = reposByName.get(repoName)!;
      return { result: mcpToolResult(repoJson(existing)) };
    }
    const repo = createRepoRecord(repoName, typeof args.description === 'string' ? args.description : '', args.private === true);
    return { result: mcpToolResult(repoJson(repo)) };
  }
  const ownerRepo = mcpOwnerRepo(args);
  if (!ownerRepo) return { result: mcpToolError('Missing required arguments: owner and repo (or full_name)') };
  const repo = repoForOwner(ownerRepo.repo, ownerRepo.owner);
  if (name === 'get_repo') {
    if (!repo) return { result: mcpToolError(`Repository not found: ${ownerRepo.owner}/${ownerRepo.repo}`) };
    return { result: mcpToolResult(repoJson(repo)) };
  }
  if (!repo) return { result: mcpToolError(`Repository not found: ${ownerRepo.owner}/${ownerRepo.repo}`) };
  if (name === 'create_issue') {
    const title = String(args.title ?? '');
    if (title === '') return { result: mcpToolError('Missing required argument: title') };
    const issue = createIssueRecord(repo, title, typeof args.body === 'string' ? args.body : '', []);
    return { result: mcpToolResult(issueJson(repo, issue)) };
  }
  if (name === 'list_issues') {
    const state = typeof args.state === 'string' ? args.state.toLowerCase() : 'open';
    let list = [...repo.issues];
    if (state === 'open') list = list.filter((issue) => issue.state === 'open');
    else if (state === 'closed') list = list.filter((issue) => issue.state === 'closed');
    return { result: mcpToolResult(list.map((issue) => issueJson(repo, issue))) };
  }
  if (name === 'create_pull_request') {
    const title = String(args.title ?? '');
    const head = String(args.head ?? '');
    const base = String(args.base ?? '');
    if (title === '' || head === '' || base === '') return { result: mcpToolError('Missing required arguments: title, head and base') };
    const pull = createPullRecord(repo, title, typeof args.body === 'string' ? args.body : '', head, base);
    if (!pull) return { result: mcpToolError('head or base branch does not exist') };
    return { result: mcpToolResult(pullJson(repo, pull)) };
  }
  if (name === 'merge_pull_request') {
    const number = typeof args.pull_number === 'number' ? args.pull_number : Number(args.pull_number);
    const pull = repo.pulls.find((entry) => entry.number === number);
    if (!pull) return { result: mcpToolError(`Pull request not found: ${number}`) };
    if (pull.merged) return { result: mcpToolResult({ sha: pull.mergeCommitSha, merged: true, message: 'Pull request successfully merged' }) };
    const sha = mergePullRequest(repo, pull);
    if (!sha) return { result: mcpToolError('Merge conflict: the pull request cannot be merged cleanly') };
    return { result: mcpToolResult({ sha, merged: true, message: 'Pull request successfully merged' }) };
  }
  return { error: { code: -32601, message: `Method not found: ${name}` } };
}

async function handleMcp(req: IncomingMessage, res: ServerResponse): Promise<void> {
  const method = req.method ?? 'GET';
  if (method === 'DELETE') {
    res.writeHead(204);
    res.end();
    return;
  }
  if (method !== 'POST') {
    sendJson(res, 405, { message: 'Method Not Allowed' });
    return;
  }
  if (!authed(req)) {
    sendJson(res, 401, { message: 'Requires authentication' });
    return;
  }
  const raw = await readBody(req);
  const text = raw.toString('utf8');
  let parsed: unknown;
  try {
    parsed = JSON.parse(text);
  } catch {
    sendJson(res, 400, { jsonrpc: '2.0', id: null, error: { code: -32700, message: 'Parse error' } });
    return;
  }
  const record = asRecord(parsed);
  const id = record.id ?? null;
  const rpcMethod = typeof record.method === 'string' ? record.method : '';
  const params = asRecord(record.params);

  // A notification (no id) is answered with 202 and no body.
  if (record.id === undefined) {
    res.writeHead(202);
    res.end();
    return;
  }

  const answer = (result: unknown): void => {
    sendJson(res, 200, { jsonrpc: '2.0', id, result });
  };
  const answerError = (code: number, message: string): void => {
    sendJson(res, 200, { jsonrpc: '2.0', id, error: { code, message } });
  };

  if (rpcMethod === 'server/discover') {
    answer({
      resultType: 'discover',
      supportedVersions: [...MCP_SUPPORTED],
      capabilities: { tools: {} },
      serverInfo: { name: 'forge', version: '1.0.0' },
      instructions: 'A GitHub-compatible git forge: repositories, issues, pull requests, git smart HTTP.',
      _meta: { 'io.modelcontextprotocol/serverInfo': { name: 'forge', version: '1.0.0' } },
    });
    return;
  }
  if (rpcMethod === 'initialize') {
    const requested = typeof params.protocolVersion === 'string' ? params.protocolVersion : MCP_REVISION;
    const negotiated = MCP_SUPPORTED.includes(requested) ? requested : MCP_REVISION;
    answer({
      protocolVersion: negotiated,
      capabilities: { tools: {} },
      serverInfo: { name: 'forge', version: '1.0.0' },
    });
    return;
  }
  if (rpcMethod === 'ping') {
    answer({});
    return;
  }
  if (rpcMethod === 'tools/list') {
    answer({ tools: MCP_TOOLS });
    return;
  }
  if (rpcMethod === 'tools/call') {
    const toolName = typeof params.name === 'string' ? params.name : '';
    const args = asRecord(params.arguments);
    const outcome = mcpCallTool(toolName, args);
    if (outcome.error) {
      answerError(outcome.error.code, outcome.error.message);
      return;
    }
    answer(outcome.result ?? {});
    return;
  }
  answerError(-32601, `Method not found: ${rpcMethod}`);
}

// ---------------------------------------------------------------------------
// router
// ---------------------------------------------------------------------------

export function createApp(): Server {
  return createServer((req: IncomingMessage, res: ServerResponse) => {
    void (async () => {
      try {
        const method = req.method ?? 'GET';
        const path = pathOf(req);
        const segments = segmentsOf(path);

        if (method === 'GET' && path === '/healthz') {
          sendJson(res, 200, { ok: true });
          return;
        }

        // Git smart HTTP: /{owner}/{repo}.git/...
        const gitMatch = /^\/([^/]+)\/([^/]+)\.git(\/.*)?$/.exec(path);
        if (gitMatch) {
          const owner = decodeURIComponent(gitMatch[1]!);
          const repoName = decodeURIComponent(gitMatch[2]!);
          const suffix = gitMatch[3] ?? '';
          const repo = repoForOwner(repoName, owner);
          if (!repo) {
            sendJson(res, 404, { message: 'Not Found' });
            return;
          }
          if (method === 'GET' && suffix.startsWith('/info/refs')) {
            const service = queryOf(req).get('service');
            if (service !== 'git-upload-pack' && service !== 'git-receive-pack') {
              sendJson(res, 400, { message: 'Unknown service' });
              return;
            }
            handleInfoRefs(req, res, repo, service);
            return;
          }
          if (method === 'POST' && suffix === '/git-upload-pack') {
            const body = await readBody(req);
            handleUploadPack(req, res, repo, body);
            return;
          }
          if (method === 'POST' && suffix === '/git-receive-pack') {
            const body = await readBody(req);
            handleReceivePack(req, res, repo, body);
            return;
          }
          sendJson(res, 404, { message: 'Not Found' });
          return;
        }

        if (segments[0] === 'api' && segments[1] === 'v3') {
          await handleRest(req, res);
          return;
        }

        if (method === 'POST' && path === '/api/graphql') {
          await handleGraphQL(req, res);
          return;
        }

        if (path === '/mcp') {
          await handleMcp(req, res);
          return;
        }

        sendJson(res, 404, { message: 'Not Found' });
      } catch (err) {
        try {
          sendJson(res, 500, { message: err instanceof Error ? err.message : 'Internal Server Error' });
        } catch {
          // The peer is already gone.
        }
      }
    })();
  });
}
