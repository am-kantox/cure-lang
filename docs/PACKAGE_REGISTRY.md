# Cure Package Registry -- Design Document
This document outlines the eventual Cure package registry. **No code
ships in v0.17.0**: this is a design contract for v0.18.0+ work.
## Goals
1. Let users publish reusable Cure modules under stable names.
2. Let `Cure.toml` declare dependencies by name and version constraint.
3. Reproducible builds via `Cure.lock`.
4. Mirror trust assumptions of Hex.pm rather than inventing new ones.
## Non-goals (for v1)
- Private packages (defer to enterprise registries).
- Binary artefacts beyond `.beam` files.
- Cross-language dependencies (Erlang/Elixir packages stay on Hex.pm).
## Directory Layout for a Published Package
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
The tarball is gzipped and content-addressed by SHA-256 of its
canonical bytes.
## Cure.toml Manifest
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
- `~>` constraint expands per Elixir-style semver: `~> 0.2 <=> >= 0.2.0 and < 0.3.0`.
- `>=` / `<` / `==` are accepted directly.
- `path` and `git` deps are *not* registered with the index.
## Resolution Algorithm
- Build a dependency graph from `[dependencies]` recursively.
- Pick the *highest* version for each package that satisfies every
  constraint imposed on it across the graph.
- Fail with a structured `E021: Dependency Resolution Conflict` error
  when no version satisfies all constraints, listing each conflicting
  caller.
- Cache resolved versions in `Cure.lock` and reuse them on subsequent
  `cure deps` runs unless `cure deps update` is invoked.
## `Cure.lock` Format
```toml
[lock.result]
version = "0.2.3"
hash = "sha256:..."
dependencies = ["std_core ~> 0.5"]

[lock.length_indexed]
version = "0.1.4"
hash = "sha256:..."
```
## Index Service
The registry exposes:
- `GET /packages/:name` -- list available versions.
- `GET /packages/:name/:version` -- manifest + tarball URL.
- `GET /packages/:name/:version/tarball` -- tarball bytes.
- `POST /packages` -- upload a new version (signed).
The index is content-served from a CDN; mutations go through a small
authority service that signs entries with an Ed25519 key. We borrow
Hex.pm's diff-by-default model.
## CLI surface
- `cure publish` -- build the tarball, prompt for credentials, upload.
- `cure search <query>` -- query the index.
- `cure info <name>[:version]` -- show manifest and dependencies.
- `cure deps update` -- recompute resolution and rewrite `Cure.lock`.
- `cure deps tree` -- already shipped in v0.17.0; accepts registry deps.
## Trust model
- Maintainer accounts are GitHub-OAuth backed.
- Each upload is signed by the maintainer's Ed25519 key.
- The registry exposes a transparency log of every publish action,
  modelled on `sigstore/rekor`.
## Phasing
- **v0.18.0**: ship the `~>`/`>=`/`==` constraint solver, resolver,
  and `Cure.lock`. Continue to consume only `path` and `git` deps.
- **v0.19.0**: stand up the index service against a small static
  S3 bucket; add `cure publish` + `cure search`.
- **v0.20.0**: signing and transparency log.
## Open questions
1. Single registry instance vs. federated mirrors? (Probably federated.)
2. Yanking semantics? (Deprecation flag, no hard removal.)
3. Storage in cents per GiB-month? (Negligible until 5K packages.)
