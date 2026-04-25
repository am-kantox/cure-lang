# REPL session snapshots (`cure snap`, v0.32.0)

`cure snap` lets you freeze the entire interactive REPL environment into
a `.cure-snap` file, share it, and restore it in a later session or on
a different machine.

## REPL meta-commands

Inside a running REPL session:

```
:snap save [path]   -- save the session (default: cure.snap in the current dir)
:snap load <path>   -- load and merge a session from a .cure-snap file
:snap list [dir]    -- list .cure-snap files in dir (default: .)
```

## CLI / Mix task

From the shell:

```bash
# Inspect a snap file without starting a REPL
mix cure.snap load my_session.cure-snap

# List snap files in a directory
mix cure.snap list sessions/

# Save an empty snap (for scripting)
mix cure.snap save --out empty.cure-snap
```

## File format

A `.cure-snap` file is a binary with a fixed header followed by a
gzip-compressed Erlang term:

    "CURESNAP\0" <> <<0x01>> <> gzip(term_to_binary(snap_map))

The `snap_map` fields:

| Field | Type | Description |
|-------|------|-------------|
| `session_entries` | list | All named declarations (fn, type, rec, ...) |
| `history_entries` | list | Up to 500 most-recent history lines |
| `uses` | list | Imported module names |
| `defs` | list | Compiled definition keyword list |
| `holes` | list | Outstanding typed-hole records |
| `stdlib_kind` | atom | `:none`, `:all`, or a list |
| `theme` | atom | `:dark`, `:light`, or `:mono` |
| `mode` | atom | `:emacs` or `:vi_insert` |
| `loaded_paths` | list | Paths given to `:load` during the session |
| `snap_vsn` | string | Schema version `"0.1"` |

## Merge semantics on `:snap load`

Loading a snap does not replace the current session wholesale; it merges
the two:

- **Definitions** (`defs`): last-writer-wins per key. The snap's entries
  overwrite the current session's entries when they share the same
  `{:fn, name, arity, visibility}` or `{:type, name}` key.
- **History**: the snap's history is prepended to the current session's
  history. Duplicates are removed.
- **Imports** (`uses`): union, no duplicates.
- **Holes**, **theme**, **mode**, **stdlib_kind**: replaced by the snap's
  values.
- **Loaded paths**: advisory -- E070 is emitted for each path in
  `loaded_paths` that no longer exists at its saved path. The rest of
  the session restores normally; the missing bindings are simply absent.

## Error codes

| Code | Meaning |
|------|---------|
| E069 | Snap schema incompatible -- `snap_vsn` does not match this Cure release |
| E070 | Snap module missing -- a `:load`-ed file path no longer exists |

## Sharing REPL environments

Snap files are self-contained binary blobs suitable for sharing via
version control or direct transfer. The session entries include the raw
source strings of every definition so the session can be fully
reconstructed even without the original `.cure` source files.

Snap files do not include compiled `.beam` bytecode. BEAM modules loaded
via `:load` during the session are referenced only by path; loading a
snap on a machine where those files are absent will produce E070 warnings
for the missing files.

## Working with snap files in CI

```bash
# Create a baseline snap for a project with pre-warmed definitions
mix cure.snap save --out baseline.cure-snap

# Verify it loads without warnings
mix cure.snap load baseline.cure-snap
```
