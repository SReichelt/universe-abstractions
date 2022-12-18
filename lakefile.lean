import Lake

open Lake DSL

package UniverseAbstractions

require Qq from git
  "https://github.com/gebner/quote4.git"@"81be563ea260ef89fe7f26998811f44816998238"

@[defaultTarget] lean_lib UniverseAbstractions
