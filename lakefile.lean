import Lake
open Lake DSL

package «NavierStokesRefereeAudit» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]

require batteries from ".lake/packages/batteries"
require Qq from ".lake/packages/Qq"
require aesop from ".lake/packages/aesop"
require proofwidgets from ".lake/packages/proofwidgets"
require importGraph from ".lake/packages/importGraph"
require LeanSearchClient from ".lake/packages/LeanSearchClient"
require plausible from ".lake/packages/plausible"
require Cli from ".lake/packages/Cli"
require mathlib from ".lake/packages/mathlib"

@[default_target]
lean_lib «NavierStokesRefereeAudit» where
  globs := #[.andSubmodules `NavierStokesRefereeAudit]

lean_exe «verify_ast_integrity» where
  root := `scripts.verify_ast_integrity
  supportInterpreter := true
