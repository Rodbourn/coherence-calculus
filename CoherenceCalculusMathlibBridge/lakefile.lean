import Lake
open Lake DSL

package «CoherenceCalculusMathlibBridge»

require «CoherenceCalculus» from "../CoherenceCalculus"
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.26.0"

@[default_target]
lean_lib CoherenceCalculusMathlibBridge
