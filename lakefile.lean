import Lake
open Lake DSL

package OmegaSqrt3 where
  version := v!"0.1.0"
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`backward.isDefEq.respectTransparency, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "d13f23b723b8a846827a245b89c10fc7d3f11612"

lean_lib Foundations where
  leanOptions := #[⟨`maxSynthPendingDepth, (3 : Nat)⟩]

lean_lib Lib
lean_lib PLATFORM

lean_lib Rect where
  roots := #[`Rect.RankModel.Basic, `Rect.RankModel.Defs3]
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`backward.isDefEq.respectTransparency, true⟩,
    ⟨`relaxedAutoImplicit, true⟩,
    ⟨`pp.unicode.fun, false⟩]

@[default_target] lean_lib Paper where
  roots := #[`Main, `Checks.Axioms]
