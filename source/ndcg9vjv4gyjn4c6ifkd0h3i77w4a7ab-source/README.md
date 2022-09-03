# Preserves

Nim implementation of the [Preserves data language](https://preserves.dev/).

## Library

To parse or produce Preserves one should write a [schema](https://preserves.dev/preserves-schema.html) and generate a Nim module using the [preserves_schema_nim](./src/preserves/preserves_schema_nim.nim) utility. This module will contain Nim types corresponding to schema definitions. The `toPreserve` and`fromPreserve` routines will convert Nim types to and from Preserves. The `decodePreserves`, `parsePreserves`, `encode`, and `$` routines will convert `Preserve` objects to and from binary and textual encoding.

To debug the `toPreserves` and `fromPreserves` routines compile with `-d:tracePreserves`.

## Utilities
* preserves_schema_nim
* preserves_encode
* preserves_decode
* preserves_from_json
* preserves_to_json

### Installation
`preserves_encode` is a multi-call binary that implements `preserves_encode`, `preserves_decode`, `preserves_from_json`, and `preserves_to_json`, so the appropriate symlinks should be created during packaging.
