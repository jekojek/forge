# forge

[![github-core-clone-01](https://make.fun/badge/github-core-clone-01.svg)](https://make.fun/bounty/github-core-clone-01?utm_source=github&utm_medium=readme&utm_campaign=github-core-clone-01)
[![rank](https://make.fun/badge/github-core-clone-01-rank.svg)](https://make.fun/bounty/github-core-clone-01?utm_source=github&utm_medium=readme&utm_campaign=github-core-clone-01)
[![reward](https://make.fun/badge/github-core-clone-01-reward.svg)](https://make.fun/bounty/github-core-clone-01?utm_source=github&utm_medium=readme&utm_campaign=github-core-clone-01)

A standalone GitHub-compatible git forge in one Node 22 process, standard
library only: git smart HTTP (upload-pack protocol v2 with ls-refs, fetch,
shallow and deepen; receive-pack v0 with report-status, side-band-64k and
delete-refs), the REST v3 API (repositories, branches, commits, contents,
labels, issues, comments and pull requests with squash merges), GraphQL v4
(viewer, repository, issue and pull-request reads and mutations,
introspection, node(id:) and batched operations) and MCP over Streamable
HTTP (server/discover plus tools/list and tools/call). Everything lives in
memory; there is no git binary, no database and no outside service.

## Run it

```sh
node --experimental-strip-types main.ts
```

The program binds an ephemeral port, registers it with the environment at
`$MAKEFUN_ENV_URL` (`POST /register {"port": N}`), then polls
`GET $MAKEFUN_ENV_URL/done` until the environment answers `{"done": true}`
and exits 0. Without `MAKEFUN_ENV_URL` it exits 1. The bearer token for the
APIs is `MAKEFUN_SHOP_TOKEN`. There is nothing to install: the program
imports `node:http`, `node:crypto` and `node:zlib` plus its own `app.ts`.

## Layout

- `main.ts`: the entrypoint — the bind / register / poll-for-done lifecycle.
- `app.ts`: the whole forge — the in-memory store, the git object model and
  packfile codec, git smart HTTP, REST v3, GraphQL v4 and MCP.
- `package.json`, `tsconfig.json`, `LICENSE` (MIT): metadata and licence.

Built for the make.fun bounty below.

---

Built for [github-core-clone-01](https://make.fun/bounty/github-core-clone-01?utm_source=github&utm_medium=readme&utm_campaign=github-core-clone-01) on [make.fun](https://make.fun).
