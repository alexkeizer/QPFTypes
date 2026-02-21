import Lake
open Lake DSL

package qpf {
}

@[default_target]
lean_lib Qpf

lean_lib Test

lean_lib ITree

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"@"v4.24.0"
