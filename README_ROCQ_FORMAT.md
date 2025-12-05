# Rocq World Format

The application now supports defining worlds directly in Rocq files (`.v` files) instead of JSON. This provides several advantages:

## Benefits

1. **Single Source of Truth**: Theory, examples, and code all in one file
2. **Executable**: Rocq files can be validated and executed directly
3. **Maintainable**: Edit one file instead of maintaining separate JSON
4. **Leverages Existing Structure**: Use your existing lecture files with minimal changes

## Quick Start

### Format Overview

A Rocq world file uses special comments to mark metadata and sections:

```coq
(*@WORLD: { "id": "world1", "name": "My World", ... }*)

(*@LEVEL: 1.1*)
(*@LEVEL_META: { "id": "1.1", "name": "Level 1", ... }*)

(*@THEORY:
# Theory Content
*)

(*@START:
(* Starting code *)
*)

(*@SOLUTION:
(* Solution code *)
*)
```

### Converting Existing Worlds

To convert a JSON world to Rocq format:

```bash
npx ts-node scripts/convert-json-to-rocq.ts public/worlds/world2-lectures.json
```

This will create `world2-lectures.v` with the same content in Rocq format.

### Using in Manifest

Update `public/config/worlds-manifest.json` to reference the `.v` file:

```json
{
  "file": "world2-lectures.v",
  "enabled": true
}
```

The application automatically detects and parses both `.json` and `.v` formats.

## Documentation

See [docs/ROCQ_WORLD_FORMAT.md](docs/ROCQ_WORLD_FORMAT.md) for complete documentation.

## Example

See [public/worlds/example-world.v](public/worlds/example-world.v) for a complete example.

