import Lib.OM.NNN30.Net.Cube

/-! # Rectangles of the grid `V × V` and the extension prices

With a linear order on `V`, a rectangle has rows `a < c` and columns `b < e`; its corners are
`z = (a,b)`, `∞ = (c,e)` (`w`), `0 = (a,e)`, `1 = (c,b)`.  `classify s t` sorts an ordered pair of
sites: `none` for an axis pair (same row or same column, including equal sites), `some (R, true)`
for the diagonal `{z, ∞}` of `R` and `some (R, false)` for the diagonal `{0, 1}`.

For prices `d` on `V`, an axis pair costs `(d(s.1,t.1) + d(s.2,t.2))/2` (one of the two terms is
zero), and a rectangle has radius `crad R = √((d(a,c)² + d(b,e)²)/2)`.  `Dlam d λ` uses the axis
prices and, on the two diagonals of `R`, `crad R · λ R`; its cost on a network is
`ndCost + Σ_R crad R (λ₁ U_R + λ₂ V_R)` (`cost_Dlam`), where `U_R`, `V_R` are the log-sizes of the
factors on the two diagonals. -/

noncomputable section
open scoped BigOperators Classical

namespace OM.NNN30.Net

/-- rectangles of the grid: rows `a < c`, columns `b < e` -/
abbrev Rect (V : Type) [LinearOrder V] : Type :=
  {q : V × V × V × V // q.1 < q.2.1 ∧ q.2.2.1 < q.2.2.2}

variable {V : Type} [LinearOrder V]

instance [Fintype V] : Fintype (Rect V) := Subtype.fintype _

namespace Rect

variable (R : Rect V)

def a : V := R.1.1
def c : V := R.1.2.1
def b : V := R.1.2.2.1
def e : V := R.1.2.2.2

lemma a_lt_c : R.a < R.c := R.2.1
lemma b_lt_e : R.b < R.e := R.2.2

/-- corner `z` -/
def z : V × V := (R.a, R.b)
/-- corner `∞` -/
def w : V × V := (R.c, R.e)
/-- corner `0` -/
def p0 : V × V := (R.a, R.e)
/-- corner `1` -/
def p1 : V × V := (R.c, R.b)

lemma ext' {R R' : Rect V} (h1 : R.a = R'.a) (h2 : R.c = R'.c) (h3 : R.b = R'.b)
    (h4 : R.e = R'.e) : R = R' := by
  obtain ⟨⟨a, c, b, e⟩, _⟩ := R
  obtain ⟨⟨a', c', b', e'⟩, _⟩ := R'
  simp only [Rect.a, Rect.b, Rect.c, Rect.e] at h1 h2 h3 h4
  subst h1 h2 h3 h4
  rfl

end Rect

/-- the rectangle and the diagonal of an ordered pair of sites; `none` for axis pairs -/
def classify (s t : V × V) : Option (Rect V × Bool) :=
  if h : s.1 ≠ t.1 ∧ s.2 ≠ t.2 then
    some (⟨(min s.1 t.1, max s.1 t.1, min s.2 t.2, max s.2 t.2), min_lt_max.2 h.1, min_lt_max.2 h.2⟩,
      decide (s.1 < t.1 ↔ s.2 < t.2))
  else none

lemma classify_eq_none_iff (s t : V × V) : classify s t = none ↔ s.1 = t.1 ∨ s.2 = t.2 := by
  unfold classify
  split_ifs with h
  · simp only [reduceCtorEq, false_iff, not_or]; exact h
  · simp only [true_iff]
    by_contra h'
    push Not at h'
    exact h h'

lemma classify_symm (s t : V × V) : classify t s = classify s t := by
  unfold classify
  by_cases h : s.1 ≠ t.1 ∧ s.2 ≠ t.2
  · have h' : t.1 ≠ s.1 ∧ t.2 ≠ s.2 := ⟨Ne.symm h.1, Ne.symm h.2⟩
    rw [dif_pos h, dif_pos h']
    congr 2
    · apply Subtype.ext
      simp only [min_comm, max_comm]
    · rcases lt_or_gt_of_ne h.1 with h1 | h1 <;> rcases lt_or_gt_of_ne h.2 with h2 | h2 <;>
        simp [h1, h2, h1.le, h2.le, not_lt.2 h1.le, not_lt.2 h2.le]
  · have h' : ¬ (t.1 ≠ s.1 ∧ t.2 ≠ s.2) := fun h' => h ⟨Ne.symm h'.1, Ne.symm h'.2⟩
    rw [dif_neg h, dif_neg h']

lemma classify_z_w (R : Rect V) : classify R.z R.w = some (R, true) := by
  unfold classify
  have h : R.z.1 ≠ R.w.1 ∧ R.z.2 ≠ R.w.2 := ⟨R.a_lt_c.ne, R.b_lt_e.ne⟩
  rw [dif_pos h]
  congr 2
  · apply Subtype.ext
    show (min R.a R.c, max R.a R.c, min R.b R.e, max R.b R.e) = R.1
    rw [min_eq_left R.a_lt_c.le, max_eq_right R.a_lt_c.le, min_eq_left R.b_lt_e.le,
      max_eq_right R.b_lt_e.le]
    rfl
  · show decide (R.a < R.c ↔ R.b < R.e) = true
    simp [R.a_lt_c, R.b_lt_e]

lemma classify_p0_p1 (R : Rect V) : classify R.p0 R.p1 = some (R, false) := by
  unfold classify
  have h : R.p0.1 ≠ R.p1.1 ∧ R.p0.2 ≠ R.p1.2 := ⟨R.a_lt_c.ne, R.b_lt_e.ne'⟩
  rw [dif_pos h]
  congr 2
  · apply Subtype.ext
    show (min R.a R.c, max R.a R.c, min R.e R.b, max R.e R.b) = R.1
    rw [min_eq_left R.a_lt_c.le, max_eq_right R.a_lt_c.le, min_eq_right R.b_lt_e.le,
      max_eq_left R.b_lt_e.le]
    rfl
  · show decide (R.a < R.c ↔ R.e < R.b) = false
    simp [R.a_lt_c, not_lt.2 R.b_lt_e.le]

/-- a diagonal pair of type `true` is `{z, ∞}` of its rectangle -/
lemma classify_eq_true {s t : V × V} {R : Rect V} (h : classify s t = some (R, true)) :
    (s = R.z ∧ t = R.w) ∨ (s = R.w ∧ t = R.z) := by
  unfold classify at h
  split_ifs at h with hst
  simp only [Option.some.injEq, Prod.mk.injEq, decide_eq_true_eq] at h
  obtain ⟨hR, hb⟩ := h
  subst hR
  obtain ⟨s1, s2⟩ := s
  obtain ⟨t1, t2⟩ := t
  simp only at hst hb ⊢
  simp only [Rect.z, Rect.w, Rect.a, Rect.b, Rect.c, Rect.e, Prod.mk.injEq]
  rcases lt_or_gt_of_ne hst.1 with h1 | h1
  · have h2 : s2 < t2 := hb.1 h1
    left
    exact ⟨⟨(min_eq_left h1.le).symm, (min_eq_left h2.le).symm⟩,
      ⟨(max_eq_right h1.le).symm, (max_eq_right h2.le).symm⟩⟩
  · have h2 : t2 < s2 := by
      rcases lt_or_gt_of_ne hst.2 with h2 | h2
      · exact absurd (hb.2 h2) (not_lt.2 h1.le)
      · exact h2
    right
    exact ⟨⟨(max_eq_left h1.le).symm, (max_eq_left h2.le).symm⟩,
      ⟨(min_eq_right h1.le).symm, (min_eq_right h2.le).symm⟩⟩

/-- a diagonal pair of type `false` is `{0, 1}` of its rectangle -/
lemma classify_eq_false {s t : V × V} {R : Rect V} (h : classify s t = some (R, false)) :
    (s = R.p0 ∧ t = R.p1) ∨ (s = R.p1 ∧ t = R.p0) := by
  unfold classify at h
  split_ifs at h with hst
  simp only [Option.some.injEq, Prod.mk.injEq, decide_eq_false_iff_not] at h
  obtain ⟨hR, hb⟩ := h
  subst hR
  obtain ⟨s1, s2⟩ := s
  obtain ⟨t1, t2⟩ := t
  simp only at hst hb ⊢
  simp only [Rect.p0, Rect.p1, Rect.a, Rect.b, Rect.c, Rect.e, Prod.mk.injEq]
  rcases lt_or_gt_of_ne hst.1 with h1 | h1
  · have h2 : t2 < s2 := by
      rcases lt_or_gt_of_ne hst.2 with h2 | h2
      · exact absurd ⟨fun _ => h2, fun _ => h1⟩ hb
      · exact h2
    left
    exact ⟨⟨(min_eq_left h1.le).symm, (max_eq_left h2.le).symm⟩,
      ⟨(max_eq_right h1.le).symm, (min_eq_right h2.le).symm⟩⟩
  · have h2 : s2 < t2 := by
      rcases lt_or_gt_of_ne hst.2 with h2 | h2
      · exact h2
      · exact absurd ⟨fun h => absurd h (not_lt.2 h1.le), fun h => absurd h (not_lt.2 h2.le)⟩ hb
    right
    exact ⟨⟨(max_eq_left h1.le).symm, (min_eq_left h2.le).symm⟩,
      ⟨(min_eq_right h1.le).symm, (max_eq_right h2.le).symm⟩⟩

/-! ## Prices on the grid -/

/-- the price of an axis pair: half the distance along the changing coordinate -/
def ap (d : V → V → ℝ) (s t : V × V) : ℝ := (d s.1 t.1 + d s.2 t.2) / 2

/-- the radius of a rectangle -/
def crad (d : V → V → ℝ) (R : Rect V) : ℝ := Real.sqrt ((d R.a R.c ^ 2 + d R.b R.e ^ 2) / 2)

lemma crad_nonneg (d : V → V → ℝ) (R : Rect V) : 0 ≤ crad d R := Real.sqrt_nonneg _

/-- the extension prices with disc parameters `lam` -/
def Dlam (d : V → V → ℝ) (lam : Rect V → ℝ × ℝ) (s t : V × V) : ℝ :=
  match classify s t with
  | none => ap d s t
  | some (R, true) => crad d R * (lam R).1
  | some (R, false) => crad d R * (lam R).2

/-! ## Network data on the grid -/

variable [Fintype V] {O0 O1 O2 : Type}

namespace TN

/-- the class of a factor of a network on the grid -/
def cls (N : TN (V × V) O0 O1 O2) (k : N.K) : Option (Rect V × Bool) :=
  classify (N.e1 k) (N.e2 k)

/-- the cost of the axis factors -/
def ndCost (d : V → V → ℝ) (N : TN (V × V) O0 O1 O2) : ℝ :=
  ∑ k, if N.cls k = none then ap d (N.e1 k) (N.e2 k) * Real.logb 2 (N.r k) else 0

/-- the log-size of the factors on the diagonal `{z, ∞}` of `R` -/
def Uw (N : TN (V × V) O0 O1 O2) (R : Rect V) : ℝ :=
  ∑ k, if N.cls k = some (R, true) then Real.logb 2 (N.r k) else 0

/-- the log-size of the factors on the diagonal `{0, 1}` of `R` -/
def Vw (N : TN (V × V) O0 O1 O2) (R : Rect V) : ℝ :=
  ∑ k, if N.cls k = some (R, false) then Real.logb 2 (N.r k) else 0

end TN

/-- the bound of the extension: axis costs plus `crad R · |(U_R, V_R)|` -/
def Hd (d : V → V → ℝ) (A : ℝ) (U W : Rect V → ℝ) : ℝ :=
  A + ∑ R, crad d R * Real.sqrt (U R ^ 2 + W R ^ 2)

lemma cost_Dlam (d : V → V → ℝ) (lam : Rect V → ℝ × ℝ) (N : TN (V × V) O0 O1 O2) :
    N.cost (Dlam d lam) =
      N.ndCost d + ∑ R, crad d R * ((lam R).1 * N.Uw R + (lam R).2 * N.Vw R) := by
  have key : ∀ k, Dlam d lam (N.e1 k) (N.e2 k) * Real.logb 2 (N.r k) =
      (if N.cls k = none then ap d (N.e1 k) (N.e2 k) * Real.logb 2 (N.r k) else 0) +
        ∑ R, crad d R * ((lam R).1 * (if N.cls k = some (R, true) then Real.logb 2 (N.r k) else 0) +
          (lam R).2 * (if N.cls k = some (R, false) then Real.logb 2 (N.r k) else 0)) := by
    intro k
    unfold Dlam
    show (match N.cls k with
      | none => ap d (N.e1 k) (N.e2 k)
      | some (R, true) => crad d R * (lam R).1
      | some (R, false) => crad d R * (lam R).2) * Real.logb 2 (N.r k) = _
    rcases hk : N.cls k with _ | ⟨R0, _ | _⟩
    · simp
    · simp only [reduceCtorEq, if_false, zero_add, Option.some.injEq, Prod.mk.injEq,
        Bool.false_eq_true, and_false, mul_zero, add_zero]
      rw [Finset.sum_eq_single R0]
      · simp; ring
      · intro R _ hR
        simp [Ne.symm hR]
      · simp
    · simp only [reduceCtorEq, if_false, zero_add, Option.some.injEq, Prod.mk.injEq,
        Bool.true_eq_false, and_false, mul_zero, zero_add]
      rw [Finset.sum_eq_single R0]
      · simp; ring
      · intro R _ hR
        simp [Ne.symm hR]
      · simp
  unfold TN.cost
  simp only [key]
  rw [Finset.sum_add_distrib, Finset.sum_comm]
  unfold TN.ndCost TN.Uw TN.Vw
  congr 1
  refine Finset.sum_congr rfl fun R _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum]

end OM.NNN30.Net
