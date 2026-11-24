import Lib.OM.NNN30.Net.Sandwich

/-! # The midpoint extension: one level of the tower

From minimal admissible prices `d` on `V` (with a linear order on `V`), minimal admissible prices
`D` on `V × V` (terminals on the diagonal) with
* (6) `D((a,b),(c,b)) ≤ d(a,c)/2` and `D((a,b),(a,e)) ≤ d(b,e)/2`,
* (7) `D((a,b),(c,e))² + D((a,e),(c,b))² ≤ (d(a,c)² + d(b,e)²)/2`,
* the diagonal copy of `V` is isometric: `D((a,a),(c,c)) = d(a,c)` (minimality of `d`). -/

noncomputable section
open scoped BigOperators Classical

namespace OM.NNN30.Net

open CoordinateTensor OM.NNN.Raw

variable {V : Type} [Fintype V] [LinearOrder V]

lemma classify_axis_row (a c b : V) : classify (a, b) (c, b) = none :=
  (classify_eq_none_iff _ _).2 (Or.inr rfl)

lemma classify_axis_col (a b e : V) : classify (a, b) (a, e) = none :=
  (classify_eq_none_iff _ _).2 (Or.inl rfl)

/-- Sorting the row and column endpoints identifies the two complementary diagonal classes. -/
lemma classify_diagonals (d : V → V → ℝ) (hsym : ∀ s t, d s t = d t s)
    {a b c e : V} (hac : a ≠ c) (hbe : b ≠ e) :
    ∃ (R : Rect V) (side : Bool), classify (a,b) (c,e) = some (R,side) ∧
      classify (a,e) (c,b) = some (R,!side) ∧ d R.a R.c = d a c ∧ d R.b R.e = d b e := by
  let R : Rect V := ⟨(min a c, max a c, min b e, max b e), min_lt_max.2 hac, min_lt_max.2 hbe⟩
  have h1 : classify (a, b) (c, e) = some (R, decide (a < c ↔ b < e)) := by
    unfold classify
    rw [dif_pos ⟨hac, hbe⟩]
  have h2 : classify (a, e) (c, b) = some (R, !decide (a < c ↔ b < e)) := by
    unfold classify
    rw [dif_pos ⟨hac, Ne.symm hbe⟩]
    congr 2
    · apply Subtype.ext
      show (min a c, max a c, min e b, max e b) = (min a c, max a c, min b e, max b e)
      rw [min_comm e b, max_comm e b]
    · rcases lt_or_gt_of_ne hac with h | h <;> rcases lt_or_gt_of_ne hbe with h' | h' <;>
        simp [h, h', h.le, h'.le, not_lt.2 h.le, not_lt.2 h'.le]
  have hsorted (x y : V) : d (min x y) (max x y) = d x y := by
    rcases le_total x y with h | h
    · rw [min_eq_left h, max_eq_right h]
    · rw [min_eq_right h, max_eq_left h, hsym]
  exact ⟨R, _, h1, h2, hsorted _ _, hsorted _ _⟩

/-- the two diagonals of a proper rectangle -/
lemma Dlam_diag (d : V → V → ℝ) (hsym : ∀ s t, d s t = d t s) (lam : Rect V → ℝ × ℝ)
    (hlam : lam ∈ Lam V) {a b c e : V} (hac : a ≠ c) (hbe : b ≠ e) :
    Dlam d lam (a, b) (c, e) ^ 2 + Dlam d lam (a, e) (c, b) ^ 2 ≤ (d a c ^ 2 + d b e ^ 2) / 2 := by
  obtain ⟨R, side, h1, h2, hr, hc⟩ := classify_diagonals d hsym hac hbe
  have hcrad : crad d R ^ 2 = (d a c ^ 2 + d b e ^ 2) / 2 := by
    rw [crad, Real.sq_sqrt (by positivity), hr, hc]
  obtain ⟨hl1, hl2, hl3⟩ := hlam R
  unfold Dlam
  rw [h1, h2]
  cases side
  · simp only [Bool.not_false]
    calc (crad d R * (lam R).2) ^ 2 + (crad d R * (lam R).1) ^ 2
        = crad d R ^ 2 * ((lam R).1 ^ 2 + (lam R).2 ^ 2) := by ring
      _ ≤ crad d R ^ 2 * 1 := mul_le_mul_of_nonneg_left hl3 (sq_nonneg _)
      _ = _ := by rw [mul_one, hcrad]
  · simp only [Bool.not_true]
    calc (crad d R * (lam R).1) ^ 2 + (crad d R * (lam R).2) ^ 2
        = crad d R ^ 2 * ((lam R).1 ^ 2 + (lam R).2 ^ 2) := by ring
      _ ≤ crad d R ^ 2 * 1 := mul_le_mul_of_nonneg_left hl3 (sq_nonneg _)
      _ = _ := by rw [mul_one, hcrad]

lemma Dlam_nonneg {d : V → V → ℝ} (hd0 : ∀ s t, 0 ≤ d s t) {lam : Rect V → ℝ × ℝ}
    (hlam : lam ∈ Lam V) (s t : V × V) : 0 ≤ Dlam d lam s t := by
  unfold Dlam
  rcases h : classify s t with _ | ⟨R, _ | _⟩
  · exact div_nonneg (add_nonneg (hd0 _ _) (hd0 _ _)) (by norm_num)
  · exact mul_nonneg (crad_nonneg d R) (hlam R).2.1
  · exact mul_nonneg (crad_nonneg d R) (hlam R).1

lemma Dlam_diag_zero {d : V → V → ℝ} (hdiag : ∀ s, d s s = 0) (lam : Rect V → ℝ × ℝ)
    (s : V × V) : Dlam d lam s s = 0 := by
  unfold Dlam
  rw [(classify_eq_none_iff s s).2 (Or.inl rfl)]
  show (d s.1 s.1 + d s.2 s.2) / 2 = 0
  rw [hdiag, hdiag]; norm_num

lemma Dlam_row (d : V → V → ℝ) (hdiag : ∀ s, d s s = 0) (lam : Rect V → ℝ × ℝ) (a c b : V) :
    Dlam d lam (a, b) (c, b) = d a c / 2 := by
  unfold Dlam
  rw [classify_axis_row]
  show (d a c + d b b) / 2 = _
  rw [hdiag, add_zero]

lemma Dlam_col (d : V → V → ℝ) (hdiag : ∀ s, d s s = 0) (lam : Rect V → ℝ × ℝ) (a b e : V) :
    Dlam d lam (a, b) (a, e) = d b e / 2 := by
  unfold Dlam
  rw [classify_axis_col]
  show (d a a + d b e) / 2 = _
  rw [hdiag, zero_add]

/-- All coordinatewise smaller nonnegative prices inherit the axis bounds
and the rectangle inequality of a quarter-disc price. -/
lemma rectangle_geometry {d : V → V → ℝ} (hsym : ∀ s t, d s t = d t s)
    (h0 : ∀ s t, 0 ≤ d s t) (hdiag : ∀ s, d s s = 0) {lam : Rect V → ℝ × ℝ}
    (hlam : lam ∈ Lam V) {D : V × V → V × V → ℝ} (hD0 : ∀ s t, 0 ≤ D s t)
    (hDle : ∀ s t, D s t ≤ Dlam d lam s t) :
    (∀ a b c, D (a,b) (c,b) ≤ d a c/2) ∧
    (∀ a b e, D (a,b) (a,e) ≤ d b e/2) ∧
    (∀ a b c e, D (a,b) (c,e)^2 + D (a,e) (c,b)^2 ≤ (d a c^2 + d b e^2)/2) ∧
    (∀ a c, D (a,a) (c,c) ≤ d a c) := by
  have hrow : ∀ a b c, D (a, b) (c, b) ≤ d a c / 2 := fun a b c =>
    (hDle _ _).trans (Dlam_row d hdiag lam a c b).le
  have hcol : ∀ a b e, D (a, b) (a, e) ≤ d b e / 2 := fun a b e =>
    (hDle _ _).trans (Dlam_col d hdiag lam a b e).le
  have hsq : ∀ a b c e, D (a, b) (c, e) ^ 2 + D (a, e) (c, b) ^ 2 ≤ (d a c ^ 2 + d b e ^ 2) / 2 := by
    intro a b c e
    by_cases hac : a = c
    · subst hac
      have h1 := hcol a b e
      have h2 := hcol a e b
      rw [hsym e b] at h2
      have := pow_le_pow_left₀ (hD0 _ _) h1 2
      have := pow_le_pow_left₀ (hD0 _ _) h2 2
      rw [hdiag a]
      nlinarith
    by_cases hbe : b = e
    · subst hbe
      have h1 := hrow a b c
      have h2 := hrow a b c
      have := pow_le_pow_left₀ (hD0 _ _) h1 2
      rw [hdiag b]
      nlinarith
    have h1 := pow_le_pow_left₀ (hD0 _ _) (hDle (a, b) (c, e)) 2
    have h2 := pow_le_pow_left₀ (hD0 _ _) (hDle (a, e) (c, b)) 2
    have := Dlam_diag d hsym lam hlam hac hbe
    linarith
  -- the diagonal is isometric
  have hdiag_le : ∀ a c, D (a, a) (c, c) ≤ d a c := by
    intro a c
    have h := hsq a a c c
    have h0 := h0 a c
    have hsq' : D (a, a) (c, c) ^ 2 ≤ d a c ^ 2 := by nlinarith [sq_nonneg (D (a, c) (c, a))]
    exact (pow_le_pow_iff_left₀ (hD0 _ _) h0 (by norm_num)).1 hsq'
  exact ⟨hrow,hcol,hsq,hdiag_le⟩

/-- **The midpoint extension** with its distance bounds and isometric diagonal -/
theorem midpoint_extension (h3 : S_R108_3) {φ : OM.PolMul.Spectral ℂ} {τ : Fin 3 → V}
    {d : V → V → ℝ} (hd : MinAdm φ τ d) :
    ∃ D : V × V → V × V → ℝ, MinAdm φ (fun i => (τ i, τ i)) D ∧
      (∀ a b c, D (a, b) (c, b) ≤ d a c / 2) ∧
      (∀ a b e, D (a, b) (a, e) ≤ d b e / 2) ∧
      (∀ a b c e, D (a, b) (c, e) ^ 2 + D (a, e) (c, b) ^ 2 ≤ (d a c ^ 2 + d b e ^ 2) / 2) ∧
      (∀ a c, D (a, a) (c, c) = d a c) := by
  have hsym := hd.symm
  obtain ⟨lam, hlam, hadm⟩ := exists_adm_Dlam h3 hd.1
  obtain ⟨D, hD, hDle⟩ := exists_minAdm hadm (Dlam_nonneg hd.2.1 hlam) (Dlam_diag_zero hd.2.2.1 lam)
  have hD0 := hD.2.1
  obtain ⟨hrow,hcol,hsq,hdiag_le⟩ := rectangle_geometry hsym hd.2.1 hd.2.2.1 hlam hD0 hDle
  have hdiag_adm : Adm φ τ (fun a c => D (a, a) (c, c)) := by
    intro O0 O1 O2 _ _ _ N hN hv
    have h := hD.1 O0 O1 O2 (N.relocate fun s => (s, s)) (hN.relocate _ fun i => rfl)
      (by rw [TN.Z_relocate]; exact hv)
    rw [TN.Z_relocate, TN.cost_relocate] at h
    exact h
  have hdiag_eq := hd.2.2.2 (fun a c => D (a, a) (c, c)) hdiag_adm (fun a c => hD0 _ _)
    (fun a => hD.2.2.1 _) hdiag_le
  refine ⟨D, hD, hrow, hcol, hsq, fun a c => ?_⟩
  exact congrFun (congrFun hdiag_eq a) c

end OM.NNN30.Net
