import PLATFORM.Statements.«R113.1»

namespace P2M.R113

open Semicontinuity

/-- The partial-transpose rank of the crossing. -/
noncomputable def P (D : ℕ+) : ℕ :=
  sInf {k : ℕ | ∃ R S : KTensor ℂ (fun _ : Fin 4 => D),
    R + S = matching D 0 3 1 2 ∧ k = flatRank R {0, 1} + flatRank S {0, 2}}

end P2M.R113
