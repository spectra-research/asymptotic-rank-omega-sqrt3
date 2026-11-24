import Lib.OM.NNN18.PackedUEntries
import Lib.OM.NNN18.PackedBase

/-!
The curvature quantities (8.1), (8.5), (8.10), the fourteen endpoint inequalities
(8.6), (8.10), (8.12) exactly as stated there, and the identities linking them to the
partial-fraction coefficients, which give the hypotheses of `packed_base`.
-/

noncomputable section
namespace OM.NNN18.PackU

def mu : ℝ := (13637 / 50000 : ℝ)
def kap : ℝ := (2003 / 2500 : ℝ)
def bst : ℝ := (21841 / 25000 : ℝ)
def Rr : ℝ := (10001 / 100000 : ℝ)
def T0 (d : ℝ) : ℝ := (376682399 / 2500000000 : ℝ) + (-162243 / 3125000 : ℝ) * d
def Sd (d : ℝ) : ℝ := (149142861 / 2500000000 : ℝ) + (-16923347 / 125000000 : ℝ) * d
def A1d (d : ℝ) : ℝ := (4746113 / 200000000 : ℝ) + (-18321441 / 250000000 : ℝ) * d
def A2d (d : ℝ) : ℝ := (-2990619649 / 5000000000 : ℝ) + (-18321441 / 250000000 : ℝ) * d
def Ud (d : ℝ) : ℝ := (33367747 / 250000000 : ℝ) + (-16923347 / 250000000 : ℝ) * d
def Vd (d : ℝ) : ℝ := (184534609 / 2500000000 : ℝ) + (16923347 / 250000000 : ℝ) * d
/-- `z_-` (8.4) and `L'(z_-)` for the packed majorant. -/
def zminus : ℝ := (-40850994 / 89172997 : ℝ)
def Lpz : ℝ := (13317570272083479 / 5667835689320000 : ℝ)

/-! ## The fourteen endpoint inequalities -/

theorem ineq_T0 : 0 < T0 (-2 * Rr) ∧ 0 < T0 Rr := by norm_num [T0, Rr]
theorem ineq_S : 0 < Sd (-2 * Rr) ∧ 0 < Sd Rr := by norm_num [Sd, Rr]
theorem ineq_A1 : 0 < A1d (-2 * Rr) ∧ 0 < A1d Rr := by norm_num [A1d, Rr]
theorem ineq_A2 : 0 < A2d (-2 * Rr) + mu * Lpz ∧ 0 < A2d Rr + mu * Lpz := by
  norm_num [A2d, Rr, mu, Lpz]
theorem ineq_U : 0 < Ud (-2 * Rr) ∧ 0 < Ud Rr := by norm_num [Ud, Rr]
theorem ineq_V : 0 < Vd (-2 * Rr) ∧ 0 < Vd Rr := by norm_num [Vd, Rr]
/-- (8.12): `g(R,H) < 0` and `g(R,3R) < 2K = 3/50`. -/
theorem ineq_gH : 5 * mu / 2 * (Vd Rr / (bst - kap * Rr / 2 - kap / 2 * (7 / 50)) ^ 3
    - Ud Rr / (bst - kap * Rr / 2 + kap / 2 * (7 / 50)) ^ 3) < 0 := by
  norm_num [Vd, Ud, Rr, mu, kap, bst]
theorem ineq_g3 : 5 * mu / 2 * (Vd Rr / (bst - 2 * kap * Rr) ^ 3
    - Ud Rr / (bst + kap * Rr) ^ 3) < 3 / 50 := by
  norm_num [Vd, Ud, Rr, mu, kap, bst]

/-! ## Links with the partial-fraction coefficients -/

lemma R00_eq (d : ℝ) : R00 d = 6 * mu / kap ^ 2 * T0 d := by
  simp only [R00, T0, mu, kap]; ring
lemma R12_eq (d : ℝ) : R12 d = -(5 * mu / (2 * kap ^ 2)) * Sd d := by
  simp only [R12, Sd, mu, kap]; ring
lemma R101_eq (d : ℝ) : R101 d = -(mu / kap ^ 2) * A1d d := by
  simp only [R101, A1d, mu, kap]; ring
lemma R111_eq (d : ℝ) : R111 d = -(5 * mu / kap ^ 2) * Ud d := by
  simp only [R111, Ud, mu, kap]; ring
lemma R211_eq (d : ℝ) : R211 d = 5 * mu / kap ^ 2 * Vd d := by
  simp only [R211, Vd, mu, kap]; ring
lemma k_eq : k = kap / 2 := by simp only [k, kap]; norm_num
lemma h_eq (d : ℝ) : h d = bst - k * d := by simp only [h, bst, k]
lemma R201_bracket (d β : ℝ) (hβ : β ≠ 0) :
    R201 d * β + 3 * S201 d = -(mu * β / kap ^ 2) * (A2d d
      + mu * ((101663 / 40000 : ℝ) + 2 * (11 / 20 : ℝ) * ((-2 + 2 * ((β - mu) / kap) / β) - (-4958 / 17479 : ℝ)))
      + 2 * (11 / 20 : ℝ) * mu * ((β - mu) / kap) / β) := by
  simp only [R201, S201, A2d, mu, kap]
  field_simp
  ring

lemma affine_pos {p q l u d : ℝ} (hl : 0 < p + q * l) (hu : 0 < p + q * u) (hd₁ : l ≤ d)
    (hd₂ : d ≤ u) : 0 < p + q * d := by
  rcases le_total 0 q with hq | hq
  · nlinarith [mul_le_mul_of_nonneg_left hd₁ hq]
  · nlinarith [mul_le_mul_of_nonpos_left hd₂ hq]

/-! ## The hypotheses of `packed_base` -/

theorem hyp00 : ∀ d, -2 * Rr ≤ d → d ≤ Rr → 0 ≤ R00 d := by
  intro d hd₁ hd₂
  have := affine_pos (p := T0 0) (q := T0 1 - T0 0) (by have := ineq_T0.1; simp only [T0] at this ⊢; linarith)
    (by have := ineq_T0.2; simp only [T0] at this ⊢; linarith) hd₁ hd₂
  rw [R00_eq]
  have hT : T0 d = T0 0 + (T0 1 - T0 0) * d := by simp only [T0]; ring
  rw [hT]; apply mul_nonneg (by norm_num [mu, kap]) this.le

theorem hyp12 : ∀ d, -2 * Rr ≤ d → d ≤ Rr → R12 d ≤ 0 := by
  intro d hd₁ hd₂
  have := affine_pos (p := Sd 0) (q := Sd 1 - Sd 0)
    (by have := ineq_S.1; simp only [Sd] at this ⊢; linarith)
    (by have := ineq_S.2; simp only [Sd] at this ⊢; linarith) hd₁ hd₂
  rw [R12_eq]
  have hT : Sd d = Sd 0 + (Sd 1 - Sd 0) * d := by simp only [Sd]; ring
  rw [hT]
  have hc : 0 < 5 * mu / (2 * kap ^ 2) := by norm_num [mu, kap]
  nlinarith

theorem hyp01a : ∀ d, -2 * Rr ≤ d → d ≤ Rr → R101 d ≤ 0 := by
  intro d hd₁ hd₂
  have := affine_pos (p := A1d 0) (q := A1d 1 - A1d 0)
    (by have := ineq_A1.1; simp only [A1d] at this ⊢; linarith)
    (by have := ineq_A1.2; simp only [A1d] at this ⊢; linarith) hd₁ hd₂
  rw [R101_eq]
  have hT : A1d d = A1d 0 + (A1d 1 - A1d 0) * d := by simp only [A1d]; ring
  rw [hT]
  have hc : 0 < mu / kap ^ 2 := by norm_num [mu, kap]
  nlinarith

theorem hyp01b : ∀ d β, -2 * Rr ≤ d → d ≤ Rr → bst - 4 * k * Rr ≤ β →
    β ≤ bst + 2 * k * Rr → R201 d * β + 3 * S201 d ≤ 0 := by
  intro d β hd₁ hd₂ hβ₁ _
  have hk : k = kap / 2 := k_eq
  have hβpos : 0 < β := by rw [hk] at hβ₁; norm_num [bst, kap, Rr] at hβ₁ ⊢; linarith
  rw [R201_bracket d β hβpos.ne']
  have hA2 := affine_pos (p := A2d 0 + mu * Lpz) (q := A2d 1 - A2d 0)
    (by have := ineq_A2.1; simp only [A2d] at this ⊢; linarith)
    (by have := ineq_A2.2; simp only [A2d] at this ⊢; linarith) hd₁ hd₂
  have hA2d : A2d d = A2d 0 + (A2d 1 - A2d 0) * d := by simp only [A2d]; ring
  -- z(β) ≥ z₋ and θ(β) ≥ 0 for β ≥ β* - 2κR
  have hθ : 0 ≤ (β - mu) / kap := by
    apply div_nonneg _ (by norm_num [kap])
    rw [hk] at hβ₁; norm_num [bst, kap, Rr, mu] at hβ₁ ⊢; linarith
  have hz : zminus ≤ -2 + 2 * ((β - mu) / kap) / β := by
    rw [hk] at hβ₁
    have e : -2 + 2 * ((β - mu) / kap) / β = -2 + 2 / kap - 2 * mu / (kap * β) := by
      field_simp
      ring
    rw [e]
    have hb0 : (0 : ℝ) < bst - 4 * (kap / 2) * Rr := by norm_num [bst, kap, Rr]
    have : 2 * mu / (kap * β) ≤ 2 * mu / (kap * (bst - 4 * (kap / 2) * Rr)) := by
      apply div_le_div_of_nonneg_left (by norm_num [mu]) (by norm_num [kap, bst, Rr])
      exact mul_le_mul_of_nonneg_left hβ₁ (by norm_num [kap])
    have hzm : zminus = -2 + 2 / kap - 2 * mu / (kap * (bst - 4 * (kap / 2) * Rr)) := by
      norm_num [zminus, kap, mu, bst, Rr]
    linarith
  have hLpz : Lpz = (101663 / 40000 : ℝ) + 2 * (11 / 20 : ℝ) * (zminus - (-4958 / 17479 : ℝ)) := by
    norm_num [Lpz, zminus]
  have hbr : 0 ≤ A2d d + mu * ((101663 / 40000 : ℝ) + 2 * (11 / 20 : ℝ) * ((-2 + 2 * ((β - mu) / kap) / β) - (-4958 / 17479 : ℝ)))
      + 2 * (11 / 20 : ℝ) * mu * ((β - mu) / kap) / β := by
    have hmu : (0 : ℝ) < mu := by norm_num [mu]
    have h1 : mu * (zminus - (-4958 / 17479 : ℝ)) ≤ mu * ((-2 + 2 * ((β - mu) / kap) / β) - (-4958 / 17479 : ℝ)) :=
      mul_le_mul_of_nonneg_left (by linarith) hmu.le
    have h2 : 0 ≤ 2 * (11 / 20 : ℝ) * mu * ((β - mu) / kap) / β := by positivity
    rw [hA2d]; rw [hLpz] at hA2; nlinarith
  have hc : 0 ≤ mu * β / kap ^ 2 := by
    have : (0 : ℝ) < mu := by norm_num [mu]
    positivity
  nlinarith

theorem hyp11 : ∀ d y, -2 * Rr ≤ d → d ≤ Rr → -(d + 2 * Rr) ≤ y → y ≤ d + 2 * Rr →
    (y ≤ 7 / 50 → hingeCurv (R111 d) (R211 d) (h d) k y ≤ 0) ∧
    (7 / 50 ≤ y → hingeCurv (R111 d) (R211 d) (h d) k y ≤ 2 * (3 / 100)) := by
  intro d y hd₁ hd₂ hy₁ hy₂
  have hk : k = kap / 2 := k_eq
  have hcurv : hingeCurv (R111 d) (R211 d) (h d) k y =
      5 * mu / 2 * ((Vd 0 + (Vd 1 - Vd 0) * d) / (bst - kap * d / 2 - kap / 2 * y) ^ 3
        - (Ud 0 + (Ud 1 - Ud 0) * d) / (bst - kap * d / 2 + kap / 2 * y) ^ 3) := by
    rw [R111_eq, R211_eq, hk, hingeCurv_eq (by norm_num [kap])]
    have e1 : h d - kap / 2 * y = bst - kap * d / 2 - kap / 2 * y := by
      rw [h_eq, hk]; ring
    have e2 : h d + kap / 2 * y = bst - kap * d / 2 + kap / 2 * y := by
      rw [h_eq, hk]; ring
    rw [e1, e2]
    simp only [Vd, Ud]; ring_nf
  rw [hcurv]
  have hgH := ineq_gH
  have hg3 := ineq_g3
  apply hinge_curv_bounds (μ := mu) (κ := kap) (bs := bst) (R := Rr) (H := 7 / 50) (K := 3 / 100)
    (by norm_num [mu]) (by norm_num [kap]) (by norm_num [Rr]) (by norm_num)
    (by norm_num [Ud]) (by norm_num [Vd]) (by norm_num [Ud, Rr]) (by norm_num [Vd, Rr])
    (by norm_num [bst, kap, Rr]) (by norm_num [bst, kap, Rr])
    _ _ hd₁ hd₂ hy₁ hy₂
  · -- (8.12) first inequality, rearranged
    have hb1 : (0 : ℝ) < bst - kap / 2 * Rr + kap / 2 * (7 / 50) := by norm_num [bst, kap, Rr]
    have hb2 : (0 : ℝ) < bst - kap / 2 * Rr - kap / 2 * (7 / 50) := by norm_num [bst, kap, Rr]
    have e1 : bst - kap * Rr / 2 - kap / 2 * (7 / 50) = bst - kap / 2 * Rr - kap / 2 * (7 / 50) := by ring
    have e2 : bst - kap * Rr / 2 + kap / 2 * (7 / 50) = bst - kap / 2 * Rr + kap / 2 * (7 / 50) := by ring
    rw [e1, e2] at hgH
    have hmu : (0 : ℝ) < 5 * mu / 2 := by norm_num [mu]
    have h3 : Vd Rr / (bst - kap / 2 * Rr - kap / 2 * (7 / 50)) ^ 3
        < Ud Rr / (bst - kap / 2 * Rr + kap / 2 * (7 / 50)) ^ 3 := by
      by_contra hc; push_neg at hc; nlinarith
    rw [div_lt_div_iff₀ (by positivity) (by positivity)] at h3
    rw [div_pow, mul_div_assoc']
    rw [le_div_iff₀ (by positivity)]
    have eV : Vd Rr = Vd 0 + (Vd 1 - Vd 0) * Rr := by simp only [Vd]; ring
    have eU : Ud Rr = Ud 0 + (Ud 1 - Ud 0) * Rr := by simp only [Ud]; ring
    rw [eV, eU] at h3
    linarith
  · have eV : Vd Rr = Vd 0 + (Vd 1 - Vd 0) * Rr := by simp only [Vd]; ring
    have eU : Ud Rr = Ud 0 + (Ud 1 - Ud 0) * Rr := by simp only [Ud]; ring
    rw [eV, eU] at hg3
    linarith

end OM.NNN18.PackU
