import Lib.OM.NNN12.Stars
import Lib.OM.NNN3.Values
import Lib.OM.NNN13.AffineExtraction
import Lib.OM.NNN20.CRecipe
import Lib.OM.NNN.EdgeValues
import Lib.OM.NNN7.Values

/-!
For a spectral point `φ` and a shape `y ∈ ℝ³`,
`F(y)` is the supremum of `log₂ φ(W) / D` over `D ≥ 1` and dyadic tensors `W` (local dimensions
`2^{w_u}`) whose log-format `w` is at most `D y` coordinatewise. Here (`Fv φ y`) the supremum is
over `Fset φ y`, with `0` adjoined (so `Fv ≥ 0`; for `y ≥ 0` the all-ones `1 × 1 × 1` tensor has
value one anyway), and with `w ≤ D y` in place of `w = D y` (allowing smaller formats accounts for padding).

* `value_le_Fv`, `Fv_le_of`: `Fv` controls every dyadic tensor of format at most `D y`, and is
  the least such bound.
* `Fv_mono` (F2), `Fv_add` (F1, superadditivity: Kronecker products of tensor powers),
  `Fv_smul` (homogeneity for real `λ ≥ 0`: integers by powers, rationals by division, reals by
  monotonicity), `Fv_concave`, `Fv_lipschitz` (slicing: one more bit at one party at most
  doubles the value).
* Bridges to the library: `Fv_le_plane` (an `NNN13.AffineBound` is a plane bound for `F`),
  `cube_gt` (a cube with value above `2^{B l}` gives `B < F(1,1,1)`),
  `cubeBound_of_Fv`.
* Pair exponents `v i = theta φ i` (the orientation whose singleton mode is `i`): `Fv_star`
  (coefficient stars), `Fv_pair` and `Fv_unit` (unit padding),
  `two_le_sum_v` (`Σ v ≥ 2`).
-/

noncomputable section
open scoped BigOperators Classical

namespace OM.NNN22

open CoordinateTensor OM.NNN.Raw Foundations.PairUnitExponents
open Semicontinuity (unitPairTensor)
open Foundations.HyperbolicLift (idx3 idx3_zero idx3_one idx3_two)
open OM.NNN12 (Shape DyadicTensor value_le_volume volume)
open OM.NNN8 (BinaryWord binary_word_card)

set_option maxHeartbeats 1000000

variable (φ : PolMul.Spectral ℂ)

/-- normalised log-values of the dyadic tensors of format at most `D y` (zero adjoined) -/
def Fset (y : Fin 3 → ℝ) : Set ℝ :=
  insert 0 {r | ∃ (D : ℕ) (w : Shape) (W : DyadicTensor w), 0 < D ∧ (∀ i, (w i : ℝ) ≤ D * y i) ∧
    0 < value φ W ∧ r = Real.logb 2 (value φ W) / D}

/-- the value function `F(y)` -/
def Fv (y : Fin 3 → ℝ) : ℝ := sSup (Fset φ y)

lemma Fset_le (y : Fin 3 → ℝ) : ∀ r ∈ Fset φ y, r ≤ |y 0| + |y 1| + |y 2| := by
  rintro r (rfl | ⟨D, w, W, hD, hw, hv, rfl⟩)
  · positivity
  · have hDpos : (0 : ℝ) < D := by exact_mod_cast hD
    have hlog : Real.logb 2 (value φ W) ≤ volume w :=
      (Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ) < 2) hv).2 (value_le_volume φ w W)
    have h0 := (hw 0).trans (mul_le_mul_of_nonneg_left (le_abs_self (y 0)) hDpos.le)
    have h1 := (hw 1).trans (mul_le_mul_of_nonneg_left (le_abs_self (y 1)) hDpos.le)
    have h2 := (hw 2).trans (mul_le_mul_of_nonneg_left (le_abs_self (y 2)) hDpos.le)
    rw [div_le_iff₀ hDpos]
    unfold volume at hlog
    linarith

lemma Fset_bddAbove (y : Fin 3 → ℝ) : BddAbove (Fset φ y) := ⟨_, Fset_le φ y⟩

lemma Fset_nonempty (y : Fin 3 → ℝ) : (Fset φ y).Nonempty := ⟨0, Set.mem_insert _ _⟩

lemma Fv_nonneg (y : Fin 3 → ℝ) : 0 ≤ Fv φ y :=
  le_csSup (Fset_bddAbove φ y) (Set.mem_insert _ _)

lemma le_Fv {y : Fin 3 → ℝ} {D : ℕ} (hD : 0 < D) {w : Shape} (hw : ∀ i, (w i : ℝ) ≤ D * y i)
    (W : DyadicTensor w) (hv : 0 < value φ W) : Real.logb 2 (value φ W) / D ≤ Fv φ y :=
  le_csSup (Fset_bddAbove φ y) (Or.inr ⟨D, w, W, hD, hw, hv, rfl⟩)

/-- **`F` controls every dyadic tensor of format at most `D y`.** -/
theorem value_le_Fv {y : Fin 3 → ℝ} {D : ℕ} (hD : 0 < D) {w : Shape}
    (hw : ∀ i, (w i : ℝ) ≤ D * y i) (W : DyadicTensor w) :
    value φ W ≤ (2 : ℝ) ^ ((D : ℝ) * Fv φ y) := by
  by_cases hv : 0 < value φ W
  · have hDpos : (0 : ℝ) < D := by exact_mod_cast hD
    have h := le_Fv φ hD hw W hv
    rw [div_le_iff₀ hDpos] at h
    rw [← Real.rpow_logb (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1) hv]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  · push Not at hv
    exact hv.trans (by positivity)

/-- **`F` is the least bound**: a nonnegative `v` that bounds every dyadic tensor of format at
most `D y` by `2^{D v}` bounds `F(y)`. -/
theorem Fv_le_of {y : Fin 3 → ℝ} {v : ℝ} (hv : 0 ≤ v)
    (h : ∀ (D : ℕ) (w : Shape) (W : DyadicTensor w), 0 < D → (∀ i, (w i : ℝ) ≤ D * y i) →
      value φ W ≤ (2 : ℝ) ^ ((D : ℝ) * v)) : Fv φ y ≤ v := by
  apply csSup_le (Fset_nonempty φ y)
  rintro r (rfl | ⟨D, w, W, hD, hw, hval, rfl⟩)
  · exact hv
  · have hDpos : (0 : ℝ) < D := by exact_mod_cast hD
    have hlog : Real.logb 2 (value φ W) ≤ D * v :=
      (Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ) < 2) hval).2 (h D w W hD hw)
    rw [div_le_iff₀ hDpos]
    linarith

/-- **Monotonicity** under padding. -/
theorem Fv_mono {y y' : Fin 3 → ℝ} (h : ∀ i, y i ≤ y' i) : Fv φ y ≤ Fv φ y' := by
  apply csSup_le_csSup (Fset_bddAbove φ y') (Fset_nonempty φ y)
  rintro r (rfl | ⟨D, w, W, hD, hw, hval, rfl⟩)
  · exact Set.mem_insert _ _
  · refine Or.inr ⟨D, w, W, hD, fun i => ?_, hval, rfl⟩
    exact (hw i).trans (mul_le_mul_of_nonneg_left (h i) (Nat.cast_nonneg D))

/-! ## Kronecker products and powers of dyadic tensors -/

/-- `BinaryWord (a + b) ≃ BinaryWord a × BinaryWord b` -/
def bwSplit (a b : ℕ) : BinaryWord (a + b) ≃ BinaryWord a × BinaryWord b :=
  (Equiv.arrowCongr finSumFinEquiv.symm (Equiv.refl _)).trans (Equiv.sumArrowEquivProdArrow _ _ _)

/-- the Kronecker product of two dyadic tensors -/
def dkron {w w' : Shape} (W : DyadicTensor w) (W' : DyadicTensor w') :
    DyadicTensor (fun i => w i + w' i) :=
  fun a b c => tensorProduct W W' (bwSplit _ _ a) (bwSplit _ _ b) (bwSplit _ _ c)

instance (a : ℕ) : Nonempty (BinaryWord a) := ⟨fun _ => 0⟩

theorem value_dkron {w w' : Shape} (W : DyadicTensor w) (W' : DyadicTensor w') :
    value φ (dkron W W') = value φ W * value φ W' := by
  unfold dkron
  rw [value_reindex φ (tensorProduct W W') (bwSplit _ _) (bwSplit _ _) (bwSplit _ _)]
  exact OM.NNN3.value_product' φ W W'

/-- a dyadic tensor transported along an equality of formats -/
lemma exists_shape_eq {w w' : Shape} (h : w = w') (W : DyadicTensor w) :
    ∃ W' : DyadicTensor w', value φ W' = value φ W := by
  subst h
  exact ⟨W, rfl⟩

/-- tensor powers: `W^{⊗(k+1)}` has format `(k+1) w` and value `φ(W)^{k+1}` -/
lemma exists_dpow {w : Shape} (W : DyadicTensor w) :
    ∀ k : ℕ, ∃ W' : DyadicTensor (fun i => (k + 1) * w i), value φ W' = value φ W ^ (k + 1)
  | 0 => by
    obtain ⟨W', h⟩ := exists_shape_eq φ (show w = fun i => (0 + 1) * w i by funext i; ring) W
    exact ⟨W', by rw [h, zero_add, pow_one]⟩
  | k + 1 => by
    obtain ⟨P, hP⟩ := exists_dpow W k
    obtain ⟨W', h⟩ := exists_shape_eq φ
      (show (fun i => (k + 1) * w i + w i) = fun i => (k + 1 + 1) * w i by funext i; ring)
      (dkron P W)
    exact ⟨W', by rw [h, value_dkron, hP]; ring⟩

/-- powers with a positive exponent -/
lemma exists_dpow' {w : Shape} (W : DyadicTensor w) {k : ℕ} (hk : 0 < k) :
    ∃ W' : DyadicTensor (fun i => k * w i), value φ W' = value φ W ^ k := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  exact exists_dpow φ W n

/-! ## Superadditivity and homogeneity -/

/-- two elements of the generating sets add up below `F(y + y')` -/
lemma add_le_Fv {y y' : Fin 3 → ℝ} (hy : ∀ i, 0 ≤ y i) (hy' : ∀ i, 0 ≤ y' i) {r r' : ℝ}
    (hr : r ∈ Fset φ y) (hr' : r' ∈ Fset φ y') : r + r' ≤ Fv φ (fun i => y i + y' i) := by
  have hsub : ∀ {z z' : Fin 3 → ℝ}, (∀ i, 0 ≤ z' i) → ∀ s ∈ Fset φ z,
      s ≤ Fv φ (fun i => z i + z' i) := by
    intro z z' hz' s hs
    refine le_csSup (Fset_bddAbove φ _) ?_
    rcases hs with rfl | ⟨D, w, W, hD, hw, hval, rfl⟩
    · exact Set.mem_insert _ _
    · refine Or.inr ⟨D, w, W, hD, fun i => ?_, hval, rfl⟩
      have := mul_nonneg (Nat.cast_nonneg D : (0 : ℝ) ≤ D) (hz' i)
      nlinarith [hw i]
  rcases hr with rfl | ⟨D, w, W, hD, hw, hval, rfl⟩
  · rw [zero_add]
    have := hsub hy r' hr'
    simpa only [add_comm] using this
  · rcases hr' with rfl | ⟨D', w', W', hD', hw', hval', rfl⟩
    · rw [add_zero]
      exact hsub hy' _ (Or.inr ⟨D, w, W, hD, hw, hval, rfl⟩)
    · obtain ⟨P, hP⟩ := exists_dpow' φ W hD'
      obtain ⟨P', hP'⟩ := exists_dpow' φ W' hD
      have hK := value_dkron φ P P'
      rw [hP, hP'] at hK
      have hpos : 0 < value φ (dkron P P') := by rw [hK]; positivity
      have hDD : 0 < D * D' := Nat.mul_pos hD hD'
      have hfmt : ∀ i, ((D' * w i + D * w' i : ℕ) : ℝ) ≤ ((D * D' : ℕ) : ℝ) * (y i + y' i) := by
        intro i
        push_cast
        have h1 := mul_le_mul_of_nonneg_left (hw i) (Nat.cast_nonneg D' : (0 : ℝ) ≤ D')
        have h2 := mul_le_mul_of_nonneg_left (hw' i) (Nat.cast_nonneg D : (0 : ℝ) ≤ D)
        nlinarith
      have hle := le_Fv φ hDD hfmt (dkron P P') hpos
      have hDpos : (0 : ℝ) < D := by exact_mod_cast hD
      have hD'pos : (0 : ℝ) < D' := by exact_mod_cast hD'
      have hlog : Real.logb 2 (value φ (dkron P P')) =
          D' * Real.logb 2 (value φ W) + D * Real.logb 2 (value φ W') := by
        rw [hK, Real.logb_mul (by positivity) (by positivity), Real.logb_pow, Real.logb_pow]
      rw [hlog] at hle
      have heq : (D' * Real.logb 2 (value φ W) + D * Real.logb 2 (value φ W')) /
          ((D * D' : ℕ) : ℝ) = Real.logb 2 (value φ W) / D + Real.logb 2 (value φ W') / D' := by
        push_cast
        field_simp
      rw [heq] at hle
      exact hle

/-- **Superadditivity**. -/
theorem Fv_add {y y' : Fin 3 → ℝ} (hy : ∀ i, 0 ≤ y i) (hy' : ∀ i, 0 ≤ y' i) :
    Fv φ y + Fv φ y' ≤ Fv φ (fun i => y i + y' i) := by
  have h1 : ∀ r ∈ Fset φ y, r ≤ Fv φ (fun i => y i + y' i) - Fv φ y' := by
    intro r hr
    have : Fv φ y' ≤ Fv φ (fun i => y i + y' i) - r := by
      apply csSup_le (Fset_nonempty φ y')
      intro r' hr'
      have := add_le_Fv φ hy hy' hr hr'
      linarith
    linarith
  have := csSup_le (Fset_nonempty φ y) h1
  unfold Fv at this ⊢
  linarith

lemma Fv_zero_smul (y : Fin 3 → ℝ) : Fv φ (fun i => (0 : ℝ) * y i) = 0 := by
  apply le_antisymm _ (Fv_nonneg φ _)
  apply Fv_le_of φ le_rfl
  intro D w W hD hw
  have hw0 : ∀ i, w i = 0 := by
    intro i
    have := hw i
    simp only [zero_mul, mul_zero] at this
    exact_mod_cast le_antisymm this (Nat.cast_nonneg _)
  have h := value_le_volume φ w W
  simp only [volume, hw0, Nat.cast_zero, add_zero, Real.rpow_zero] at h
  simpa using h

lemma Fv_nsmul_le (y : Fin 3 → ℝ) {k : ℕ} (hk : 0 < k) :
    Fv φ (fun i => (k : ℝ) * y i) ≤ k * Fv φ y := by
  apply Fv_le_of φ (mul_nonneg (Nat.cast_nonneg k) (Fv_nonneg φ y))
  intro D w W hD hw
  have hDk : 0 < D * k := Nat.mul_pos hD hk
  have h := value_le_Fv φ (y := y) hDk (w := w) (fun i => by push_cast; linarith [hw i]) W
  calc value φ W ≤ (2 : ℝ) ^ (((D * k : ℕ) : ℝ) * Fv φ y) := h
    _ = (2 : ℝ) ^ ((D : ℝ) * (k * Fv φ y)) := by push_cast; ring_nf

lemma Fv_nsmul_ge {y : Fin 3 → ℝ} (hy : ∀ i, 0 ≤ y i) :
    ∀ k : ℕ, (k : ℝ) * Fv φ y ≤ Fv φ (fun i => (k : ℝ) * y i)
  | 0 => by rw [Nat.cast_zero, zero_mul]; exact Fv_nonneg φ _
  | k + 1 => by
    have ih := Fv_nsmul_ge hy k
    have hk : ∀ i, 0 ≤ (k : ℝ) * y i := fun i => mul_nonneg (Nat.cast_nonneg k) (hy i)
    have h := Fv_add φ hk hy
    have he : (fun i => (k : ℝ) * y i + y i) = fun i => ((k : ℝ) + 1) * y i := by
      funext i; ring
    rw [he] at h
    push_cast
    linarith

/-- homogeneity for natural numbers -/
theorem Fv_nsmul {y : Fin 3 → ℝ} (hy : ∀ i, 0 ≤ y i) (k : ℕ) :
    Fv φ (fun i => (k : ℝ) * y i) = k * Fv φ y := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [Nat.cast_zero, zero_mul]; exact Fv_zero_smul φ y
  · exact le_antisymm (Fv_nsmul_le φ y hk) (Fv_nsmul_ge φ hy k)

/-- homogeneity for nonnegative rationals -/
theorem Fv_qsmul {y : Fin 3 → ℝ} (hy : ∀ i, 0 ≤ y i) {q : ℚ} (hq : 0 ≤ q) :
    Fv φ (fun i => (q : ℝ) * y i) = q * Fv φ y := by
  have hden : 0 < q.den := q.den_pos
  have hnum : 0 ≤ q.num := Rat.num_nonneg.2 hq
  set a : ℕ := q.num.toNat with ha
  have hqa : (q : ℝ) = (a : ℝ) / q.den := by
    rw [ha]
    have : ((q.num.toNat : ℤ) : ℝ) = (q.num : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hnum
    rw [show ((q.num.toNat : ℕ) : ℝ) = ((q.num.toNat : ℤ) : ℝ) from rfl, this]
    exact_mod_cast (Rat.num_div_den q).symm
  have hdpos : (0 : ℝ) < q.den := by exact_mod_cast hden
  have hqy : ∀ i, 0 ≤ (q : ℝ) * y i := fun i => mul_nonneg (by exact_mod_cast hq) (hy i)
  have h1 := Fv_nsmul φ hqy q.den
  have he : (fun i => (q.den : ℝ) * ((q : ℝ) * y i)) = fun i => (a : ℝ) * y i := by
    funext i; rw [hqa]; field_simp
  rw [he, Fv_nsmul φ hy a] at h1
  calc Fv φ (fun i => (q : ℝ) * y i)
      = ((q.den : ℝ) * Fv φ (fun i => (q : ℝ) * y i)) / q.den :=
        (mul_div_cancel_left₀ _ hdpos.ne').symm
    _ = (a * Fv φ y) / q.den := by rw [h1]
    _ = q * Fv φ y := by rw [hqa]; ring

/-- **Homogeneity** for real `λ ≥ 0`. -/
theorem Fv_smul {y : Fin 3 → ℝ} (hy : ∀ i, 0 ≤ y i) {l : ℝ} (hl : 0 ≤ l) :
    Fv φ (fun i => l * y i) = l * Fv φ y := by
  have hF0 := Fv_nonneg φ y
  apply le_antisymm
  · -- above every rational `q ≥ l`
    apply le_of_forall_pos_lt_add
    intro ε hε
    have hε' : 0 < ε / (Fv φ y + 1) := div_pos hε (by linarith)
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show l < l + ε / (Fv φ y + 1) by linarith)
    have hq0 : (0 : ℝ) ≤ q := hl.trans hq1.le
    have hmono : Fv φ (fun i => l * y i) ≤ Fv φ (fun i => (q : ℝ) * y i) :=
      Fv_mono φ (fun i => mul_le_mul_of_nonneg_right hq1.le (hy i))
    rw [Fv_qsmul φ hy (by exact_mod_cast hq0)] at hmono
    have : (q : ℝ) * Fv φ y ≤ (l + ε / (Fv φ y + 1)) * Fv φ y :=
      mul_le_mul_of_nonneg_right hq2.le hF0
    have h3 : ε / (Fv φ y + 1) * Fv φ y < ε := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
      nlinarith
    nlinarith
  · -- below every rational `q ≤ l`
    rcases eq_or_lt_of_le hl with hl0 | hlpos
    · rw [← hl0, zero_mul]; exact Fv_nonneg φ _
    apply le_of_forall_pos_lt_add
    intro ε hε
    have hε' : 0 < ε / (Fv φ y + 1) := div_pos hε (by linarith)
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn
      (show max 0 (l - ε / (Fv φ y + 1)) < l from max_lt hlpos (by linarith))
    have hq0 : (0 : ℝ) ≤ q := (le_max_left _ _).trans hq1.le
    have hmono : Fv φ (fun i => (q : ℝ) * y i) ≤ Fv φ (fun i => l * y i) :=
      Fv_mono φ (fun i => mul_le_mul_of_nonneg_right hq2.le (hy i))
    rw [Fv_qsmul φ hy (by exact_mod_cast hq0)] at hmono
    have h4 : l - ε / (Fv φ y + 1) < q := lt_of_le_of_lt (le_max_right _ _) hq1
    have : (l - ε / (Fv φ y + 1)) * Fv φ y ≤ (q : ℝ) * Fv φ y :=
      mul_le_mul_of_nonneg_right h4.le hF0
    have h3 : ε / (Fv φ y + 1) * Fv φ y < ε := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
      nlinarith
    nlinarith

/-- **Concavity** of `F` on nonnegative shapes. -/
theorem Fv_concave {y y' : Fin 3 → ℝ} (hy : ∀ i, 0 ≤ y i) (hy' : ∀ i, 0 ≤ y' i) {l : ℝ}
    (hl0 : 0 ≤ l) (hl1 : l ≤ 1) :
    l * Fv φ y + (1 - l) * Fv φ y' ≤ Fv φ (fun i => l * y i + (1 - l) * y' i) := by
  have h1 := Fv_add φ (y := fun i => l * y i) (y' := fun i => (1 - l) * y' i)
    (fun i => mul_nonneg hl0 (hy i)) (fun i => mul_nonneg (by linarith) (hy' i))
  rw [Fv_smul φ hy hl0, Fv_smul φ hy' (by linarith)] at h1
  exact h1

/-! ## Bridges to the tariffs and cube bounds of the library -/

/-- the `1 × 1 × 1` all-ones tensor has value one -/
lemma value_one111 : value φ (fun (_ : Unit) (_ : Unit) (_ : Unit) => (1 : ℂ)) = 1 := by
  have h := value_pair φ (I := Unit)
  have he : pair Unit = fun (_ : Unit) (_ : Unit) (_ : Unit) => (1 : ℂ) := by
    funext a b c; simp [pair]
  rw [he] at h
  rw [h]
  simp

/-- every dyadic tensor with entry one at the zero words has value at least one -/
lemma one_le_value_of_zero {w : Shape} (W : DyadicTensor w) (h0 : W 0 0 0 = 1) :
    1 ≤ value φ W := by
  have hr : Restricts W (fun (_ : Unit) (_ : Unit) (_ : Unit) => (1 : ℂ)) := by
    refine ⟨fun _ x => if x = 0 then 1 else 0, fun _ x => if x = 0 then 1 else 0,
      fun _ x => if x = 0 then 1 else 0, ?_⟩
    funext a b c
    simp [mapTensor, ite_mul, mul_ite, Finset.sum_ite_eq', h0]
  have := value_mono φ (restricts_degenerates _ _ hr)
  rwa [value_one111] at this

/-- the coordinate format `e_i` -/
def unitShape (i : Fin 3) : Shape := fun l => if l = i then 1 else 0

/-- an affine tariff has nonnegative coefficients -/
lemma affine_nonneg {c : Fin 3 → ℝ} (hc : NNN13.AffineBound φ c) (i : Fin 3) : 0 ≤ c i := by
  have h1 := one_le_value_of_zero φ (w := unitShape i) (fun _ _ _ => 1) rfl
  have h2 := (h1.trans (hc (unitShape i) (fun _ _ _ => 1)))
  have hp : NNN13.plane c (fun l => ((unitShape i l : ℕ) : ℝ)) = c i := by
    fin_cases i <;> simp [NNN13.plane, unitShape]
  rw [hp] at h2
  by_contra hneg
  push Not at hneg
  have : (2 : ℝ) ^ c i < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) hneg
  linarith

/-- **An affine tariff bounds `F`** at every nonnegative shape. -/
theorem Fv_le_plane {c : Fin 3 → ℝ} (hc : NNN13.AffineBound φ c) {y : Fin 3 → ℝ}
    (hy : ∀ i, 0 ≤ y i) : Fv φ y ≤ NNN13.plane c y := by
  have hc0 := affine_nonneg φ hc
  have hv0 : 0 ≤ NNN13.plane c y := by
    unfold NNN13.plane
    have := mul_nonneg (hc0 0) (hy 0)
    have := mul_nonneg (hc0 1) (hy 1)
    have := mul_nonneg (hc0 2) (hy 2)
    linarith
  apply Fv_le_of φ hv0
  intro D w W hD hw
  refine (hc w W).trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_)
  unfold NNN13.plane
  have h0 := mul_le_mul_of_nonneg_left (hw 0) (hc0 0)
  have h1 := mul_le_mul_of_nonneg_left (hw 1) (hc0 1)
  have h2 := mul_le_mul_of_nonneg_left (hw 2) (hc0 2)
  nlinarith

/-- **(G_B) in terms of `F`**: a cube above `2^{B l}` gives `B < F(1,1,1)`. -/
theorem cube_gt {B : ℝ} {l : ℕ} (hl : 0 < l) (S : DyadicTensor (fun _ => l))
    (h : (2 : ℝ) ^ (B * l) < value φ S) : B < Fv φ (fun _ => 1) := by
  have hle := value_le_Fv φ (y := fun _ => 1) hl (w := fun _ => l) (fun i => by simp) S
  have hlt := h.trans_le hle
  rw [Real.rpow_lt_rpow_left_iff (by norm_num : (1 : ℝ) < 2)] at hlt
  have hlpos : (0 : ℝ) < l := by exact_mod_cast hl
  nlinarith

/-- **A bound on `F(1,1,1)` is a cube bound.** -/
theorem cubeBound_of_Fv {B : ℝ} (h : Fv φ (fun _ => 1) ≤ B) : NNN20.CubeBound B φ := by
  intro l S
  rcases Nat.eq_zero_or_pos l with rfl | hl
  · have := value_le_volume φ _ S
    simpa [volume] using this
  · refine (value_le_Fv φ (y := fun _ => 1) hl (w := fun _ => l) (fun i => by simp) S).trans
      (Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_)
    have hlpos : (0 : ℝ) ≤ l := Nat.cast_nonneg l
    nlinarith

/-! ## Pair exponents -/

/-- the true pair exponents satisfy `Σ v ≥ 2` (`two_le_theta_sum`) -/
theorem two_le_sum_v : 2 ≤ theta φ 0 + theta φ 1 + theta φ 2 := two_le_theta_sum φ

lemma theta_nonneg (i : Fin 3) : 0 ≤ theta φ i := (theta_mem_Icc φ i).1

/-- the coefficient star at party `i`: `v_j y_k + v_k y_j` -/
def starV (i : Fin 3) (y : Fin 3 → ℝ) : ℝ :=
  if i = 0 then theta φ 2 * y 1 + theta φ 1 * y 2
  else if i = 1 then theta φ 2 * y 0 + theta φ 0 * y 2
  else theta φ 1 * y 0 + theta φ 0 * y 1

lemma Fv_star_aux {y : Fin 3 → ℝ} {s : ℝ} (hs : 0 ≤ s)
    (h : ∀ (D : ℕ) (w : Shape) (W : DyadicTensor w), 0 < D → (∀ i, (w i : ℝ) ≤ D * y i) →
      value φ W ≤ (2 : ℝ) ^ ((D : ℝ) * s)) : Fv φ y ≤ s := Fv_le_of φ hs h

/-- **The coefficient stars**: `F(y) ≤ v_j y_k + v_k y_j`. -/
theorem Fv_star {y : Fin 3 → ℝ} (hy : ∀ i, 0 ≤ y i) (i : Fin 3) : Fv φ y ≤ starV φ i y := by
  have h0 := theta_nonneg φ 0
  have h1 := theta_nonneg φ 1
  have h2 := theta_nonneg φ 2
  have hy0 := hy 0
  have hy1 := hy 1
  have hy2 := hy 2
  fin_cases i
  · show Fv φ y ≤ theta φ 2 * y 1 + theta φ 1 * y 2
    apply Fv_le_of φ (by positivity)
    intro D w W hD hw
    refine (OM.NNN12.value_le_star_A φ w W (theta φ) (fun _ => le_rfl)).trans
      (Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_)
    nlinarith [mul_le_mul_of_nonneg_left (hw 1) h2, mul_le_mul_of_nonneg_left (hw 2) h1]
  · show Fv φ y ≤ theta φ 2 * y 0 + theta φ 0 * y 2
    apply Fv_le_of φ (by positivity)
    intro D w W hD hw
    refine (OM.NNN12.value_le_star_B φ w W (theta φ) (fun _ => le_rfl)).trans
      (Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_)
    nlinarith [mul_le_mul_of_nonneg_left (hw 0) h2, mul_le_mul_of_nonneg_left (hw 2) h0]
  · show Fv φ y ≤ theta φ 1 * y 0 + theta φ 0 * y 1
    apply Fv_le_of φ (by positivity)
    intro D w W hD hw
    refine (OM.NNN12.value_le_star_C φ w W (theta φ) (fun _ => le_rfl)).trans
      (Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_)
    nlinarith [mul_le_mul_of_nonneg_left (hw 0) h1, mul_le_mul_of_nonneg_left (hw 1) h0]

/-- the cube is at most the sum of any two pair exponents (the star at the third party) -/
theorem Fv_one_le_pair (i : Fin 3) : Fv φ (fun _ => 1) ≤ starV φ i (fun _ => 1) :=
  Fv_star φ (fun _ => zero_le_one) i

/-- the pair unit with singleton mode 0 on general index types -/
theorem value_pair0 {I U : Type} [Fintype I] [DecidableEq I] [Nonempty I] [Unique U] [Fintype U] :
    value φ (fun (_ : U) (j k : I) => if j = k then (1 : ℂ) else 0) =
      (Fintype.card I : ℝ) ^ theta φ 0 := by
  let n : ℕ+ := ⟨Fintype.card I, Fintype.card_pos⟩
  let e : Fin n ≃ I := (Fintype.equivFin I).symm
  let f : Fin 1 ≃ U := Equiv.ofUnique _ _
  have hr := value_reindex φ (fun (_ : U) (j k : I) => if j = k then (1 : ℂ) else 0) f e e
  have he : (fun a b c => (fun (_ : U) (j k : I) => if j = k then (1 : ℂ) else 0) (f a) (e b) (e c)) =
      (fun a b c => unitPairTensor (F := ℂ) n (1 : Fin 3) 2 (by decide +kernel)
        (idx3 a b c)) := by
    funext a b c
    simp only [unitPairTensor, idx3_one, idx3_two, e.injective.eq_iff, Fin.ext_iff]
  rw [he, value_encode] at hr
  rw [← hr]
  have hpow := eval_orientedPairUnit_eq_rpow φ 0 n n.pos
  rw [orientedPairUnit, pairUnitTT_complementary_eq 0 n n.pos] at hpow
  exact hpow

/-- the pair unit with singleton mode 1 on general index types -/
theorem value_pair1 {I U : Type} [Fintype I] [DecidableEq I] [Nonempty I] [Unique U] [Fintype U] :
    value φ (fun (i : I) (_ : U) (k : I) => if i = k then (1 : ℂ) else 0) =
      (Fintype.card I : ℝ) ^ theta φ 1 := by
  let n : ℕ+ := ⟨Fintype.card I, Fintype.card_pos⟩
  let e : Fin n ≃ I := (Fintype.equivFin I).symm
  let f : Fin 1 ≃ U := Equiv.ofUnique _ _
  have hr := value_reindex φ (fun (i : I) (_ : U) (k : I) => if i = k then (1 : ℂ) else 0) e f e
  have he : (fun a b c => (fun (i : I) (_ : U) (k : I) => if i = k then (1 : ℂ) else 0) (e a) (f b) (e c)) =
      (fun a b c => unitPairTensor (F := ℂ) n (0 : Fin 3) 2 (by decide +kernel)
        (idx3 a b c)) := by
    funext a b c
    simp only [unitPairTensor, idx3_zero, idx3_two, e.injective.eq_iff, Fin.ext_iff]
  rw [he, value_encode] at hr
  rw [← hr]
  have hpow := eval_orientedPairUnit_eq_rpow φ 1 n n.pos
  rw [orientedPairUnit, pairUnitTT_complementary_eq 1 n n.pos] at hpow
  exact hpow

/-- the pair unit with singleton mode 2 on general index types -/
theorem value_pair2 {I U : Type} [Fintype I] [DecidableEq I] [Nonempty I] [Unique U] [Fintype U] :
    value φ (fun (i j : I) (_ : U) => if i = j then (1 : ℂ) else 0) =
      (Fintype.card I : ℝ) ^ theta φ 2 := by
  let n : ℕ+ := ⟨Fintype.card I, Fintype.card_pos⟩
  let e : Fin n ≃ I := (Fintype.equivFin I).symm
  let f : Fin 1 ≃ U := Equiv.ofUnique _ _
  have hr := value_reindex φ (fun (i j : I) (_ : U) => if i = j then (1 : ℂ) else 0) e e f
  have he : (fun a b c => (fun (i j : I) (_ : U) => if i = j then (1 : ℂ) else 0) (e a) (e b) (f c)) =
      (fun a b c => unitPairTensor (F := ℂ) n (0 : Fin 3) 1 (by decide +kernel)
        (idx3 a b c)) := by
    funext a b c
    simp only [unitPairTensor, idx3_zero, idx3_one, e.injective.eq_iff, Fin.ext_iff]
  rw [he, value_encode] at hr
  rw [← hr]
  have hpow := eval_orientedPairUnit_eq_rpow φ 2 n n.pos
  rw [orientedPairUnit, pairUnitTT_complementary_eq 2 n n.pos] at hpow
  exact hpow

/-- the format `e_j + e_k` of the pair unit with singleton mode `i` -/
def pairShape (i : Fin 3) : Fin 3 → ℝ := fun l => if l = i then 0 else 1

lemma pairShape_nonneg (i l : Fin 3) : 0 ≤ pairShape i l := by
  unfold pairShape; split_ifs <;> norm_num

instance : Unique (BinaryWord 0) := Pi.uniqueOfIsEmpty _

/-- a dyadic tensor of value `2^{v}` and format at most `pairShape i` gives `v ≤ F(pairShape i)` -/
lemma Fv_pair_of (i : Fin 3) (w : Shape) (W : DyadicTensor w)
    (hw : ∀ l, (w l : ℝ) ≤ ((1 : ℕ) : ℝ) * pairShape i l) {v : ℝ} (hv : value φ W = (2 : ℝ) ^ v) :
    v ≤ Fv φ (pairShape i) := by
  have hpos : 0 < value φ W := by rw [hv]; positivity
  have := le_Fv φ (y := pairShape i) one_pos (w := w) hw W hpos
  rwa [hv, Real.logb_rpow (by norm_num) (by norm_num), Nat.cast_one, div_one] at this

lemma Fv_pair0 : theta φ 0 ≤ Fv φ (pairShape 0) := by
  let W : DyadicTensor ![0, 1, 1] := fun _ j k => if j = k then 1 else 0
  have hv : value φ W = (2 : ℝ) ^ theta φ 0 := by
    have h := value_pair0 φ (I := BinaryWord 1) (U := BinaryWord 0)
    simp only [binary_word_card, pow_one, Nat.cast_ofNat] at h
    exact h
  exact Fv_pair_of φ 0 ![0, 1, 1] W (fun l => by fin_cases l <;> simp [pairShape]) hv

lemma Fv_pair1 : theta φ 1 ≤ Fv φ (pairShape 1) := by
  let W : DyadicTensor ![1, 0, 1] := fun i _ k => if i = k then 1 else 0
  have hv : value φ W = (2 : ℝ) ^ theta φ 1 := by
    have h := value_pair1 φ (I := BinaryWord 1) (U := BinaryWord 0)
    simp only [binary_word_card, pow_one, Nat.cast_ofNat] at h
    exact h
  exact Fv_pair_of φ 1 ![1, 0, 1] W (fun l => by fin_cases l <;> simp [pairShape]) hv

lemma Fv_pair2 : theta φ 2 ≤ Fv φ (pairShape 2) := by
  let W : DyadicTensor ![1, 1, 0] := fun i j _ => if i = j then 1 else 0
  have hv : value φ W = (2 : ℝ) ^ theta φ 2 := by
    have h := value_pair2 φ (I := BinaryWord 1) (U := BinaryWord 0)
    simp only [binary_word_card, pow_one, Nat.cast_ofNat] at h
    exact h
  exact Fv_pair_of φ 2 ![1, 1, 0] W (fun l => by fin_cases l <;> simp [pairShape]) hv

/-- **The pair unit**: `v_i ≤ F(e_j + e_k)`. -/
theorem Fv_pair (i : Fin 3) : theta φ i ≤ Fv φ (pairShape i) := by
  fin_cases i
  · exact Fv_pair0 φ
  · exact Fv_pair1 φ
  · exact Fv_pair2 φ

/-- **Unit padding**: `F(z + a (e_j + e_k)) ≥ F(z) + a v_i`. -/
theorem Fv_unit {z : Fin 3 → ℝ} (hz : ∀ l, 0 ≤ z l) {a : ℝ} (ha : 0 ≤ a) (i : Fin 3) :
    Fv φ z + a * theta φ i ≤ Fv φ (fun l => z l + a * pairShape i l) := by
  have h1 := Fv_add φ (y := z) (y' := fun l => a * pairShape i l) hz
    (fun l => mul_nonneg ha (pairShape_nonneg i l))
  rw [Fv_smul φ (pairShape_nonneg i) ha] at h1
  have := mul_le_mul_of_nonneg_left (Fv_pair φ i) ha
  linarith

/-! ## Slicing and the Lipschitz bound -/

section Slice

variable {I J K : Type} [Fintype I] [Fintype J] [Fintype K]

/-- subadditivity of the value -/
lemma value_add_le (S T : Tensor ℂ I J K) : value φ (S + T) ≤ value φ S + value φ T := by
  have h := OM.NNN7.remove_correction_value φ (S + T) (-T) T
    (OM.NNN3.restricts_neg (OM.NNN7.identity_restriction T))
  simpa using h

lemma value_sum_le {V : Type} (s : Finset V) (T : V → Tensor ℂ I J K) :
    value φ (∑ v ∈ s, T v) ≤ ∑ v ∈ s, value φ (T v) := by
  induction s using Finset.induction_on with
  | empty => simp [value_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (value_add_le φ _ _).trans (by linarith)

/-- slicing party 0 along `e : I ≃ I' × V` -/
lemma slice0_le {I' V : Type} [Fintype I'] [Fintype V] (e : I ≃ I' × V) (T : Tensor ℂ I J K)
    {M : ℝ} (hM : ∀ v, value φ (fun x y z => T (e.symm (x, v)) y z : Tensor ℂ I' J K) ≤ M) :
    value φ T ≤ Fintype.card V * M := by
  let Tv : V → Tensor ℂ I J K := fun v x y z => if (e x).2 = v then T x y z else 0
  have hdec : T = ∑ v, Tv v := by
    funext x y z
    simp [Tv, Finset.sum_apply]
  have hres : ∀ v, value φ (Tv v) ≤ M := by
    intro v
    have hr : Restricts (fun x y z => T (e.symm (x, v)) y z : Tensor ℂ I' J K) (Tv v) := by
      refine ⟨fun x x' => if e x = (x', v) then 1 else 0, fun y y' => if y = y' then 1 else 0,
        fun z z' => if z = z' then 1 else 0, ?_⟩
      funext x y z
      obtain ⟨⟨x0, v0⟩, rfl⟩ : ∃ p, x = e.symm p := ⟨e x, (e.symm_apply_apply x).symm⟩
      by_cases hv : v0 = v
      · subst hv
        simp [mapTensor, Tv, ite_mul, mul_ite, Finset.sum_ite_eq]
      · simp [mapTensor, Tv, mul_ite, hv, Prod.mk.injEq]
    exact (value_mono φ (restricts_degenerates _ _ hr)).trans (hM v)
  calc value φ T = value φ (∑ v, Tv v) := by rw [← hdec]
    _ ≤ ∑ v, value φ (Tv v) := value_sum_le φ _ _
    _ ≤ ∑ _v : V, M := Finset.sum_le_sum (fun v _ => hres v)
    _ = Fintype.card V * M := by simp

/-- slicing party 1 along `e : J ≃ J' × V` -/
lemma slice1_le {J' V : Type} [Fintype J'] [Fintype V] (e : J ≃ J' × V) (T : Tensor ℂ I J K)
    {M : ℝ} (hM : ∀ v, value φ (fun x y z => T x (e.symm (y, v)) z : Tensor ℂ I J' K) ≤ M) :
    value φ T ≤ Fintype.card V * M := by
  let Tv : V → Tensor ℂ I J K := fun v x y z => if (e y).2 = v then T x y z else 0
  have hdec : T = ∑ v, Tv v := by
    funext x y z
    simp [Tv, Finset.sum_apply]
  have hres : ∀ v, value φ (Tv v) ≤ M := by
    intro v
    have hr : Restricts (fun x y z => T x (e.symm (y, v)) z : Tensor ℂ I J' K) (Tv v) := by
      refine ⟨fun x x' => if x = x' then 1 else 0, fun y y' => if e y = (y', v) then 1 else 0,
        fun z z' => if z = z' then 1 else 0, ?_⟩
      funext x y z
      obtain ⟨⟨y0, v0⟩, rfl⟩ : ∃ p, y = e.symm p := ⟨e y, (e.symm_apply_apply y).symm⟩
      by_cases hv : v0 = v
      · subst hv
        simp [mapTensor, Tv, ite_mul, mul_ite, Finset.sum_ite_eq]
      · simp [mapTensor, Tv, mul_ite, hv, Prod.mk.injEq]
    exact (value_mono φ (restricts_degenerates _ _ hr)).trans (hM v)
  calc value φ T = value φ (∑ v, Tv v) := by rw [← hdec]
    _ ≤ ∑ v, value φ (Tv v) := value_sum_le φ _ _
    _ ≤ ∑ _v : V, M := Finset.sum_le_sum (fun v _ => hres v)
    _ = Fintype.card V * M := by simp

/-- slicing party 2 along `e : K ≃ K' × V` -/
lemma slice2_le {K' V : Type} [Fintype K'] [Fintype V] (e : K ≃ K' × V) (T : Tensor ℂ I J K)
    {M : ℝ} (hM : ∀ v, value φ (fun x y z => T x y (e.symm (z, v)) : Tensor ℂ I J K') ≤ M) :
    value φ T ≤ Fintype.card V * M := by
  let Tv : V → Tensor ℂ I J K := fun v x y z => if (e z).2 = v then T x y z else 0
  have hdec : T = ∑ v, Tv v := by
    funext x y z
    simp [Tv, Finset.sum_apply]
  have hres : ∀ v, value φ (Tv v) ≤ M := by
    intro v
    have hr : Restricts (fun x y z => T x y (e.symm (z, v)) : Tensor ℂ I J K') (Tv v) := by
      refine ⟨fun x x' => if x = x' then 1 else 0, fun y y' => if y = y' then 1 else 0,
        fun z z' => if e z = (z', v) then 1 else 0, ?_⟩
      funext x y z
      obtain ⟨⟨z0, v0⟩, rfl⟩ : ∃ p, z = e.symm p := ⟨e z, (e.symm_apply_apply z).symm⟩
      by_cases hv : v0 = v
      · subst hv
        simp [mapTensor, Tv, ite_mul, mul_ite, Finset.sum_ite_eq]
      · simp [mapTensor, Tv, mul_ite, hv, Prod.mk.injEq]
    exact (value_mono φ (restricts_degenerates _ _ hr)).trans (hM v)
  calc value φ T = value φ (∑ v, Tv v) := by rw [← hdec]
    _ ≤ ∑ v, value φ (Tv v) := value_sum_le φ _ _
    _ ≤ ∑ _v : V, M := Finset.sum_le_sum (fun v _ => hres v)
    _ = Fintype.card V * M := by simp

end Slice

lemma card_bw1 : (Fintype.card (BinaryWord 1) : ℝ) = 2 := by simp

/-- `s` more bits at party 0 multiply the value by at most `2^s` -/
lemma bits0_le {a b c : ℕ} {M : ℝ}
    (hM : ∀ W : Tensor ℂ (BinaryWord a) (BinaryWord b) (BinaryWord c), value φ W ≤ M) :
    ∀ s : ℕ, ∀ W : Tensor ℂ (BinaryWord (a + s)) (BinaryWord b) (BinaryWord c),
      value φ W ≤ 2 ^ s * M
  | 0 => fun W => by simpa using hM W
  | s + 1 => fun W => by
    have h := slice0_le φ (bwSplit (a + s) 1) W (M := 2 ^ s * M) (fun v => bits0_le hM s _)
    rw [card_bw1] at h
    rw [pow_succ]; linarith

lemma bits1_le {a b c : ℕ} {M : ℝ}
    (hM : ∀ W : Tensor ℂ (BinaryWord b) (BinaryWord a) (BinaryWord c), value φ W ≤ M) :
    ∀ s : ℕ, ∀ W : Tensor ℂ (BinaryWord b) (BinaryWord (a + s)) (BinaryWord c),
      value φ W ≤ 2 ^ s * M
  | 0 => fun W => by simpa using hM W
  | s + 1 => fun W => by
    have h := slice1_le φ (bwSplit (a + s) 1) W (M := 2 ^ s * M) (fun v => bits1_le hM s _)
    rw [card_bw1] at h
    rw [pow_succ]; linarith

lemma bits2_le {a b c : ℕ} {M : ℝ}
    (hM : ∀ W : Tensor ℂ (BinaryWord b) (BinaryWord c) (BinaryWord a), value φ W ≤ M) :
    ∀ s : ℕ, ∀ W : Tensor ℂ (BinaryWord b) (BinaryWord c) (BinaryWord (a + s)),
      value φ W ≤ 2 ^ s * M
  | 0 => fun W => by simpa using hM W
  | s + 1 => fun W => by
    have h := slice2_le φ (bwSplit (a + s) 1) W (M := 2 ^ s * M) (fun v => bits2_le hM s _)
    rw [card_bw1] at h
    rw [pow_succ]; linarith

/-- `s` more bits at party `i` (the other two parties fixed) multiply the value by at most `2^s` -/
lemma bits_le (i : Fin 3) {w : Shape} {a s : ℕ} (hs : w i = a + s) {M : ℝ}
    (hbase : ∀ w' : Shape, w' i = a → (∀ l, l ≠ i → w' l = w l) → ∀ W' : DyadicTensor w',
      value φ W' ≤ M) (W : DyadicTensor w) : value φ W ≤ 2 ^ s * M := by
  fin_cases i
  · have hb : ∀ W' : Tensor ℂ (BinaryWord a) (BinaryWord (w 1)) (BinaryWord (w 2)),
        value φ W' ≤ M := fun W' => hbase ![a, w 1, w 2] rfl
          (fun l hl => by fin_cases l <;> simp_all) W'
    have key : ∀ (n : ℕ) (W : Tensor ℂ (BinaryWord n) (BinaryWord (w 1)) (BinaryWord (w 2))),
        n = a + s → value φ W ≤ 2 ^ s * M := by
      intro n W hn; subst hn; exact bits0_le φ hb s W
    exact key (w 0) W hs
  · have hb : ∀ W' : Tensor ℂ (BinaryWord (w 0)) (BinaryWord a) (BinaryWord (w 2)),
        value φ W' ≤ M := fun W' => hbase ![w 0, a, w 2] rfl
          (fun l hl => by fin_cases l <;> simp_all) W'
    have key : ∀ (n : ℕ) (W : Tensor ℂ (BinaryWord (w 0)) (BinaryWord n) (BinaryWord (w 2))),
        n = a + s → value φ W ≤ 2 ^ s * M := by
      intro n W hn; subst hn; exact bits1_le φ hb s W
    exact key (w 1) W hs
  · have hb : ∀ W' : Tensor ℂ (BinaryWord (w 0)) (BinaryWord (w 1)) (BinaryWord a),
        value φ W' ≤ M := fun W' => hbase ![w 0, w 1, a] rfl
          (fun l hl => by fin_cases l <;> simp_all) W'
    have key : ∀ (n : ℕ) (W : Tensor ℂ (BinaryWord (w 0)) (BinaryWord (w 1)) (BinaryWord n)),
        n = a + s → value φ W ≤ 2 ^ s * M := by
      intro n W hn; subst hn; exact bits2_le φ hb s W
    exact key (w 2) W hs

/-- one slicing step with rounding: `φ(W) ≤ 2^{D (F(y) + ε) + 1}` for `w ≤ D (y + ε e_i)` -/
lemma lip_step {y : Fin 3 → ℝ} (hy : ∀ l, 0 ≤ y l) {ε : ℝ} (hε : 0 ≤ ε) (i : Fin 3)
    {D : ℕ} (hD : 0 < D) {w : Shape}
    (hw : ∀ l, (w l : ℝ) ≤ D * (y l + (if l = i then ε else 0))) (W : DyadicTensor w) :
    value φ W ≤ (2 : ℝ) ^ ((D : ℝ) * (Fv φ y + ε) + 1) := by
  have hDpos : (0 : ℝ) < D := by exact_mod_cast hD
  have hyi := hy i
  set a := Nat.floor ((D : ℝ) * y i) with ha
  have ha_le : (a : ℝ) ≤ D * y i := Nat.floor_le (by positivity)
  have ha_gt : (D : ℝ) * y i < a + 1 := Nat.lt_floor_add_one _
  have hother : ∀ l, l ≠ i → (w l : ℝ) ≤ D * y l := by
    intro l hl; have := hw l; simpa [hl] using this
  have hwi : (w i : ℝ) ≤ D * (y i + ε) := by have := hw i; simpa using this
  have hF0 := Fv_nonneg φ y
  by_cases hwa : w i ≤ a
  · have hfmt : ∀ l, (w l : ℝ) ≤ D * y l := by
      intro l
      by_cases hl : l = i
      · subst hl; exact (Nat.cast_le.2 hwa).trans ha_le
      · exact hother l hl
    refine (value_le_Fv φ hD hfmt W).trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_)
    nlinarith
  · push Not at hwa
    obtain ⟨s, hs⟩ : ∃ s, w i = a + s := ⟨w i - a, by omega⟩
    have hsR : (w i : ℝ) = a + s := by exact_mod_cast hs
    have hsb : (s : ℝ) ≤ D * ε + 1 := by nlinarith
    have hbound := bits_le φ i hs (M := (2 : ℝ) ^ ((D : ℝ) * Fv φ y))
      (fun w' hw'i hw'o W' => by
        refine value_le_Fv φ hD (fun l => ?_) W'
        by_cases hl : l = i
        · subst hl; rw [hw'i]; exact ha_le
        · rw [hw'o l hl]; exact hother l hl) W
    refine hbound.trans ?_
    rw [← Real.rpow_natCast, ← Real.rpow_add (by norm_num)]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith)

/-- **Lipschitz bound** (slicing): `F(y + ε e_i) ≤ F(y) + ε` for `y ≥ 0`, `ε ≥ 0`. -/
theorem Fv_lipschitz {y : Fin 3 → ℝ} (hy : ∀ l, 0 ≤ y l) {ε : ℝ} (hε : 0 ≤ ε) (i : Fin 3) :
    Fv φ (fun l => y l + (if l = i then ε else 0)) ≤ Fv φ y + ε := by
  have hF0 := Fv_nonneg φ y
  apply Fv_le_of φ (by linarith)
  intro D w W hD hw
  set P := (2 : ℝ) ^ ((D : ℝ) * (Fv φ y + ε)) with hP
  have hP0 : 0 < P := by positivity
  by_contra hcon
  push Not at hcon
  have hr : 1 < value φ W / P := by rw [one_lt_div hP0]; exact hcon
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (2 : ℝ) hr
  have hk1 : 0 < k := by
    rcases Nat.eq_zero_or_pos k with rfl | h
    · rw [pow_zero] at hk; linarith
    · exact h
  obtain ⟨Wk, hWk⟩ := exists_dpow' φ W hk1
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hfmt : ∀ l, (((fun l => k * w l) l : ℕ) : ℝ) ≤
      ((k * D : ℕ) : ℝ) * (y l + (if l = i then ε else 0)) := by
    intro l
    have := mul_le_mul_of_nonneg_left (hw l) hk0
    push_cast
    linarith
  have hstep := lip_step φ hy hε i (Nat.mul_pos hk1 hD) hfmt Wk
  rw [hWk] at hstep
  have hpow : (2 : ℝ) ^ (((k * D : ℕ) : ℝ) * (Fv φ y + ε) + 1) = 2 * P ^ k := by
    rw [hP, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), Real.rpow_add (by norm_num),
      Real.rpow_one]
    push_cast
    ring_nf
  rw [hpow] at hstep
  have : (value φ W / P) ^ k ≤ 2 := by
    rw [div_pow, div_le_iff₀ (by positivity)]
    linarith
  linarith

end OM.NNN22
