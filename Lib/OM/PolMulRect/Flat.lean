import Lib.OM.PolMulRect.Cap
import Lib.OM.PolMulRect.Maximum
import Lib.OM.PolMulRect.Numerics

/-! # The flat case of AvdBZ Theorem 1.2 -/

namespace OM.PolMulRect

open Foundations.PairUnitExponents

/-- Each spectral weight is at most the sum of the two largest dimensions
on the flat branch (AvdBZ, Lemma 4.15). -/
theorem mmWeight_le_add_of_flat {F : Type*} [Field F] (φ : PolMul.Spectral F) {a b c : ℝ}
    (hc : 0 ≤ c) (hcb : c ≤ b) (hba : b ≤ a) (hflat : c * (a + b) ≤ a * b) :
    mmWeight φ a b c ≤ a + b :=
  weight_le_add_of_quadratic_bound (theta φ) (theta_mem_Icc φ 0).1
    (quadratic_bound φ) hc hcb hba hflat

/-- The maximum is attained by a spectral point, and the first flattening gives the reverse bound. -/
theorem omegaRect_eq_add (F : Type*) [Field F] {a b c : ℝ}
    (hc : 0 ≤ c) (hcb : c ≤ b) (hba : b ≤ a) (hflat : c * (a + b) ≤ a * b) :
    PolMul.omegaRect F a b c = a + b := by
  have hb := hc.trans hcb
  have ha := hb.trans hba
  obtain ⟨φ, hφ⟩ := (omegaRect_isGreatest F ha hb hc).1
  exact le_antisymm (hφ ▸ mmWeight_le_add_of_flat φ hc hcb hba hflat)
    (add_le_omegaRect F ha hb hc)

end OM.PolMulRect
