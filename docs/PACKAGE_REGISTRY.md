# Cure Package Registry
*Status: shipped as of v0.23.0.*

This document describes the on-the-wire protocol, manifest schema,
lockfile format, and trust model that the Cure package registry
speaks. It is the authoritative contract for both the server side (any
compatible index service) and the client side (`Cure.Project.Registry`,
`Cure.Project.Lock`, `Cure.Project.Signing`,
`Cure.Project.Transparency`).

## Goals
1. Users can publish reusable Cure modules under stable names.
2. `Cure.toml` declares dependencies by name and version constraint.
3. Reproducible builds via `Cure.lock` (v0.23.0 implementation lives
   in `Cure.Project.Lock`).
4. The trust model mirrors Hex.pm: maintainer keys + transparency log.

## Non-goals (for v1)
- Private packages (enterprise registries are out of scope).
- Binary artefacts beyond `.beam` files.
- Cross-language dependencies (Erlang/Elixir packages stay on Hex.pm).
  `cure publish --hex` exports *from* Cure *into* Hex; it does not
  reverse the flow.

## Directory layout for a published package
```
my_pkg-0.1.0/
  Cure.toml
  README.md
  LICENSE
  lib/
    *.cure
  docs/
    *.md
```
The tarball is gzipped and content-addressed by the SHA-256 of its
canonical bytes.

## Cure.toml manifest
```toml
[project]
name = "my_pkg"
version = "0.1.0"
description = "..."
license = "MIT"

[dependencies]
result = "~> 0.2"
length_indexed = ">= 0.1.0"
local = { path = "../shared/local" }
mirror = { git = "https://github.com/me/mirror.git", tag = "v0.3.1" }
```
- `~>` is the pessimistic operator: `~> 0.2` expands to
  `>= 0.2.0 and < 0.3.0`.
- `>=`, `<`, `==` are accepted directly.
- `path` and `git` deps bypass the registry index; they are not
  signed and do not enter the transparency log.

## Registry HTTP endpoints
All endpoints are read-only except `POST /packages`. Requests and
responses are JSON unless otherwise noted; content-addressed bodies
(`tarball`, `metadata`) are served as `application/octet-stream`.

- `GET /packages/:name` -> `%{ "versions" => [...] }` with each entry
  `{version, tarball_url, manifest_url, sha256}`.
- `GET /packages/:name/:version` -> `%{ "manifest" => %{...} }` where
  the manifest is the inline form of the `Cure.toml` metadata plus a
  list of `{name, constraint}` dependency pairs.
- `GET /packages/:name/:version/tarball` -> raw gzipped tarball bytes.
  Clients must verify SHA-256 against the declared `sha256` from the
  version entry. Mismatch is `E039`.
- `GET /packages?q=<query>` -> `%{ "hits" => [...] }` with substring
  search over package names and descriptions.
- `GET /log` -> `%{ "entries" => [...] }` transparency-log tip.
- `POST /packages` -> sign-in-required upload. Body is a JSON envelope
  (see below) carrying base64-encoded tarball and signature plus the
  manifest.

## Resolution algorithm
Implemented in `Cure.Project.Resolver` (deterministic backtracking
resolver, runs locally against the flat registry snapshot).

1. Build a dependency graph from `[dependencies]` recursively.
2. Pick the newest version per package that satisfies every active
   constraint.
3. On conflict, the resolver surfaces `E030: Package Version Conflict`
   with every conflicting caller.
4. Cache the resolved versions in `Cure.lock` and reuse them on
   subsequent `cure deps` runs. `cure deps update` forces a fresh
   resolution.

## `Cure.lock` format
```toml
[lock.result]
version = "0.2.3"
hash = "sha256:..."
dependencies = ["std_core ~> 0.5"]

[lock.length_indexed]
version = "0.1.4"
hash = "sha256:..."
dependencies = []
```
The hash column is the SHA-256 of the package tarball's canonical
bytes. When a locked version no longer satisfies its top-level
constraint, the resolver falls back to a fresh run and rewrites the
lockfile.

## Signing (v0.23.0)
Every publish is signed with an Ed25519 private key held by the
maintainer. The signing message is:
```
name || NUL || version || NUL || sha256(tarball)
```
Keys live under `~/.cure/keys/`:
```
~/.cure/keys/<handle>.sec      (chmod 600)
~/.cure/keys/<handle>.pub      (chmod 644)
~/.cure/keys/trusted.toml      (handle = "<hex pub bytes>")
```
Verification happens on every `cure deps` install against the locally
trusted key list. Unknown or rotated publishers surface as
`E041: Registry Signature Invalid`.

## Transparency log (v0.23.0)
The registry publishes a Rekor-style append-only log. Every publish
event is a JSON entry:
```
{
  "index":     non_neg_integer,
  "previous":  sha256_hex,           # hash of entry at index - 1
  "name":      package_name,
  "version":   version_string,
  "sha256":    tarball_sha256_hex,
  "signature": base64(ed25519_sig),
  "publisher": maintainer_handle,
  "timestamp": iso8601,
  "hash":      sha256_of_this_entry  # over canonical encoding without the :hash field
}
```
The client verifies, for every tarball install:

1. The log contains an entry matching the tarball's SHA-256.
2. The entry's `hash` equals
   `sha256(canonical_encoding(entry - :hash))`.
3. The entry's `previous` equals the prior entry's `hash`.

When the log URL is unreachable, `Cure.Project.Transparency.verify/3`
returns `{:ok, :unverified}` and emits a warning on the `:registry`
pipeline stage under code `E042`. Users can promote the check to a
hard failure via `config :cure, strict_transparency: true`.

## CLI surface
Every command below ships in v0.23.0:
- `cure publish`        -- build, sign, upload.
- `cure publish --dry-run` -- print what would be uploaded.
- `cure publish --hex`  -- produce a Hex-compatible tarball under
  `_build/cure/publish/hex.tar` for cross-publishing via
  `mix hex.publish package --replace`.
- `cure search <query>` -- substring search against the index.
- `cure info <name>[:ver]` -- print manifest / version list.
- `cure keys generate <handle>` -- create an Ed25519 keypair.
- `cure keys list`      -- enumerate trusted keys.
- `cure deps` / `deps update` / `deps tree` -- unchanged except for
  implicit registry fetch when a dependency lacks both `path` and
  `git`.

## Trust model
- Maintainer accounts are GitHub-OAuth backed.
- Each publish is signed with the maintainer's Ed25519 key.
- The transparency log provides tamper-evident auditability: any
  client can cross-check publish events against the public chain.

## Phasing recap
- **v0.18.0**: shipped the `~>`/`>=`/`==` constraint solver, resolver,
  and `Cure.lock` shape. Consumed only `path` / `git` deps.
- **v0.23.0** (this release): shipped `Cure.Project.Registry` HTTP
  client, `Cure.Project.Lock` reader / writer with resolver
  integration, `Cure.Project.Signing` Ed25519 keys, and
  `Cure.Project.Transparency` chain verifier.

## Open questions (future work)
1. Federated vs. single registry instance. (Leaning federated.)
2. Yank semantics. (Deprecation flag, no hard removal.)
3. Storage cost. (Negligible until 5K packages.)
