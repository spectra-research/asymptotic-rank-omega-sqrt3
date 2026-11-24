import PLATFORM.Statements.«R114.10»

open P2M.R114 Semicontinuity

def S_R114_12 : Prop :=
  ∀ H : ℕ, 2 ≤ H →
    let D := (partitionSide H : ℕ)
    let r := (pivotColumns (rowPiece H)).length
    r = flatRank (rowPiece H) {0, 1} ∧
    (∀ c e : Fin D, ∃! v : Fin D → ℂ,
      (∀ j : Fin D, r ≤ j.val → v j = 0) ∧
      ∀ i b : Fin D, rowPiece H ![i, b, e, c] = ∑ j, leftFactor H ![i, b, j] * v j) ∧
    ∀ a : Fin 4 → Fin (partitionSide H : ℕ),
      rowPiece H a = ∑ j, leftFactor H ![a 0, a 1, j] * rightFactor H ![a 3, a 2, j]
