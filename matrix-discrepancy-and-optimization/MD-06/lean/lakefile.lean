import Lake
open Lake DSL

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
  "0df444a360eaa60ab8c11dca51a86af692955474"

require LeanCert from git
  "https://github.com/Verified-Builders/leancert.git" @
  "621a43d7cf21f87872392a01e874f2f1dbddc926"

package md06 where
  version := v!"0.1.0"

lean_lib Definitions
lean_lib Challenge

@[default_target]
lean_lib Solution
