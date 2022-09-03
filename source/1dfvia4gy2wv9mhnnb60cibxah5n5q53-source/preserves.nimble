# Package

version       = "1.0.0"
author        = "Emery Hemingway"
description   = "data model and serialization format"
license       = "Unlicense"
srcDir        = "src"

bin           = @["preserves/private/preserves_schema_nim", "preserves/private/preserves_encode"]


# Dependencies

requires "nim >= 1.4.8", "compiler >= 1.4.8", "bigints", "npeg"
