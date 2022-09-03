# Package

version       = "20220709"
author        = "Emery Hemingway"
description   = "data model and serialization format"
license       = "Unlicense"
srcDir        = "src"

# bin           = @["preserves/preserves_schema_nim", "preserves/private/preserves_encode"]
# Nimble can't build these, because it sucks


# Dependencies

requires "nim >= 1.4.8", "compiler >= 1.4.8", "npeg"
