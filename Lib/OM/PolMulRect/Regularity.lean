import Lib.OM.PolMulRect.Maximum
import Foundations.Tensors.OrientationTransport

/-! # Orientation and regularity of the rectangular exponent -/

namespace OM.PolMulRect

open Foundations.PairUnitExponents Foundations.OrientationTransport
open PolMul (omegaRect)

universe u
variable {F : Type u} [Field F]

/-- Cropping gives monotonicity, including when some of the smaller widths are negative. -/
theorem omegaRect_mono {a b c a' b' c' : ℝ}
    (ha' : 0 ≤ a') (hb' : 0 ≤ b') (hc' : 0 ≤ c')
    (ha : a ≤ a') (hb : b ≤ b') (hc : c ≤ c') :
    omegaRect F a b c ≤ omegaRect F a' b' c' := by
  apply le_csInf (rectAdmissible_nonempty F ha' hb' hc')
  rintro τ ⟨K, hK⟩
  apply csInf_le (rectAdmissible_bddBelow F a b c)
  refine ⟨K, fun n hn => ?_⟩
  have side {x y : ℝ} (hxy : x ≤ y) : ceilSide n hn x ≤ ceilSide n hn y :=
    Nat.ceil_mono (Real.rpow_le_rpow_of_exponent_le (Nat.one_le_cast.mpr hn) hxy)
  exact le_trans (by exact_mod_cast tensorRank_matMul_mono (F := F) (side ha) (side hb) (side hc))
    (hK n hn)

/-- Cyclic relabelling gives the geometric order of the three opposite-edge prices. -/
theorem theta_dot_le_omegaRect (φ : PolMul.Spectral F) {a b c : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    a * theta φ 0 + b * theta φ 1 + c * theta φ 2 ≤ omegaRect F a b c := by
  let σ : Equiv.Perm (Fin 3) := (Equiv.swap 0 1).trans (Equiv.swap 0 2)
  have hθ (i : Fin 3) : theta (pullPoint φ σ) i = theta φ (σ.symm i) := theta_legReindex φ σ i
  calc
    _ = mmWeight (pullPoint φ σ) a b c := by
      unfold mmWeight
      rw [hθ 1, hθ 2, hθ 0]
      rfl
    _ ≤ _ := mmWeight_le_omegaRect (pullPoint φ σ) ha hb hc

/-- Increasing each width by at most `δ` increases the exponent by at most `3δ`. -/
theorem omegaRect_le_add {a b c a' b' c' δ : ℝ} (hδ : 0 ≤ δ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (ha' : a' ≤ a + δ) (hb' : b' ≤ b + δ) (hc' : c' ≤ c + δ) :
    omegaRect F a' b' c' ≤ omegaRect F a b c + 3 * δ := by
  have hA := add_nonneg ha hδ
  have hB := add_nonneg hb hδ
  have hC := add_nonneg hc hδ
  apply (omegaRect_mono hA hB hC ha' hb' hc').trans
  obtain ⟨φ, hφ⟩ := (omegaRect_isGreatest F hA hB hC).1
  rw [← hφ]
  have hsource := mmWeight_le_omegaRect φ ha hb hc
  have price (i : Fin 3) : δ * theta φ i ≤ δ := mul_le_of_le_one_right hδ (theta_mem_Icc φ i).2
  simp only [mmWeight, add_mul] at hsource ⊢
  linarith only [hsource, price 0, price 1, price 2]

/-- The cost at the distances to three fixed vertices is 3-Lipschitz. -/
theorem lipschitzWith_rectangular_cost {X : Type*} [PseudoMetricSpace X] (q₁ q₂ q₃ : X) :
    LipschitzWith 3 (fun z => omegaRect F (dist z q₁) (dist z q₂) (dist z q₃)) := by
  apply LipschitzWith.of_dist_le_mul
  intro z y
  have bound (u v : X) :
      omegaRect F (dist u q₁) (dist u q₂) (dist u q₃) ≤
        omegaRect F (dist v q₁) (dist v q₂) (dist v q₃) + 3 * dist u v :=
    omegaRect_le_add dist_nonneg dist_nonneg dist_nonneg dist_nonneg
      ((dist_triangle u v q₁).trans_eq (add_comm _ _))
      ((dist_triangle u v q₂).trans_eq (add_comm _ _))
      ((dist_triangle u v q₃).trans_eq (add_comm _ _))
  rw [Real.dist_eq, abs_le]
  have h := bound y z
  rw [dist_comm y z] at h
  change -(3 * dist z y) ≤ _ ∧ _ ≤ 3 * dist z y
  constructor <;> linarith only [h, bound z y]

theorem continuous_rectangular_cost {X : Type*} [PseudoMetricSpace X] (q₁ q₂ q₃ : X) :
    Continuous (fun z => omegaRect F (dist z q₁) (dist z q₂) (dist z q₃)) :=
  (lipschitzWith_rectangular_cost q₁ q₂ q₃).continuous

end OM.PolMulRect
