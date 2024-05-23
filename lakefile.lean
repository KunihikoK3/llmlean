import Lake
open Lake DSL

package «llmlean» {
  moreLinkArgs := #[
    "-L./.lake/packages/LeanCopilot/.lake/build/lib",
    "-lctranslate2"
  ]
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"
require LeanCopilot from git "https://github.com/lean-dojo/LeanCopilot.git" @ "v1.2.0"
@[default_target]
lean_lib «LLMlean» {
  -- add any library configuration options here
}
