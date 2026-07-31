import Lake
open Lake DSL

package «Realizability» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

/-
This project depends on the Kleene–Kreisel development directly (per its
brief): the realizability interpretation reuses `PureType`, `Assoc`,
`Ct`, `CtPer`, `ctPer_iff_assoc`, and `CtQ` rather than reimplementing
finite types.
-/
require ContinuousFunctionals from "Realizability/Core/ContinuousFunctionals"

@[default_target]
lean_lib «Realizability» where
