import Lib.OM.PolMul.Defs
import Foundations.Tensors.PairUnitExponents

/-! # Sizes, rank growth and spectral weights for rectangular matrix multiplication -/

namespace OM.PolMulRect

open Semicontinuity Foundations.PairUnitExponents

/-- The positive integral side length at aspect `a` and input size `n ≥ 1`. -/
noncomputable def ceilSide (n : ℕ) (hn : 1 ≤ n) (a : ℝ) : ℕ+ :=
  ⟨⌈(n : ℝ) ^ a⌉₊, Nat.ceil_pos.mpr (Real.rpow_pos_of_pos (by exact_mod_cast hn) a)⟩

/-- The predicate in the defining infimum of `PolMul.omegaRect`. -/
def RectAdmissible (F : Type*) [Field F] (a b c τ : ℝ) : Prop :=
  ∃ C : ℝ, ∀ (n : ℕ) (hn : 1 ≤ n),
    (tensorRank (PolMul.matMul (F := F) (ceilSide n hn a) (ceilSide n hn b)
      (ceilSide n hn c)) : ℝ) ≤ C * (n : ℝ) ^ τ

/-- The three matrix dimensions have singleton legs 1, 2 and 0, respectively,
as in `OM.Omega.eval_matMul`. -/
noncomputable def mmWeight {F : Type*} [Field F] (φ : PolMul.Spectral F) (a b c : ℝ) : ℝ :=
  a * theta φ 1 + b * theta φ 2 + c * theta φ 0

end OM.PolMulRect
