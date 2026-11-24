import Lib.OM.NNN30.Net.Cross
import PLATFORM.Statements.«R108.3»

/-! # The core inequality of the midpoint extension

For admissible, nonnegative prices `d` on `V` and a local network `M` on `V × V` with positive
value, `log₂ value ≤ ndCost + Σ_R crad R · |(U_R, V_R)|` (`core`), where `U_R`, `V_R` are the
log-sizes of `M`'s factors on the two diagonals of `R`.  Proof: the crossing step at scale
`L = q j` for the power `M^L` with the rectangular pieces (R108.3) at rational widths just
above `U_R`, `V_R`; Cauchy-Schwarz with the circle `r² + c² ≤ 2(a² + b²) + ε`; `j → ∞`, then the
widths and `ε` to their limits. -/

noncomputable section
open scoped BigOperators Classical
open Filter Topology

namespace OM.NNN30.Net

open CoordinateTensor OM.NNN.Raw

variable {V : Type} [Fintype V] [LinearOrder V] {O0 O1 O2 P0 P1 P2 : Type}

/-! ## Data of products and powers -/

namespace TN

lemma ndCost_kron (d : V → V → ℝ) (N : TN (V × V) O0 O1 O2) (N' : TN (V × V) P0 P1 P2) :
    (N.kron N').ndCost d = N.ndCost d + N'.ndCost d :=
  Fintype.sum_sum_type _

lemma Uw_kron (N : TN (V × V) O0 O1 O2) (N' : TN (V × V) P0 P1 P2) (R : Rect V) :
    (N.kron N').Uw R = N.Uw R + N'.Uw R :=
  Fintype.sum_sum_type _

lemma Vw_kron (N : TN (V × V) O0 O1 O2) (N' : TN (V × V) P0 P1 P2) (R : Rect V) :
    (N.kron N').Vw R = N.Vw R + N'.Vw R :=
  Fintype.sum_sum_type _

lemma ndCost_one (d : V → V → ℝ) : (one (V × V)).ndCost d = 0 := Fintype.sum_empty _
lemma Uw_one (R : Rect V) : (one (V × V)).Uw R = 0 := Fintype.sum_empty _
lemma Vw_one (R : Rect V) : (one (V × V)).Vw R = 0 := Fintype.sum_empty _

lemma ndCost_pow (d : V → V → ℝ) (N : TN (V × V) O0 O1 O2) (p : ℕ) :
    (N.pow p).ndCost d = p * N.ndCost d := by
  induction p with
  | zero =>
    have h : (N.pow 0).ndCost d = 0 := ndCost_one d
    rw [h]; simp
  | succ p ih =>
    have h : (N.pow (p + 1)).ndCost d = (N.pow p).ndCost d + N.ndCost d :=
      ndCost_kron d (N.pow p) N
    rw [h, ih]; push_cast; ring

lemma Uw_pow (N : TN (V × V) O0 O1 O2) (p : ℕ) (R : Rect V) :
    (N.pow p).Uw R = p * N.Uw R := by
  induction p with
  | zero =>
    have h : (N.pow 0).Uw R = 0 := Uw_one R
    rw [h]; simp
  | succ p ih =>
    have h : (N.pow (p + 1)).Uw R = (N.pow p).Uw R + N.Uw R := Uw_kron (N.pow p) N R
    rw [h, ih]; push_cast; ring

lemma Vw_pow (N : TN (V × V) O0 O1 O2) (p : ℕ) (R : Rect V) :
    (N.pow p).Vw R = p * N.Vw R := by
  induction p with
  | zero =>
    have h : (N.pow 0).Vw R = 0 := Vw_one R
    rw [h]; simp
  | succ p ih =>
    have h : (N.pow (p + 1)).Vw R = (N.pow p).Vw R + N.Vw R := Vw_kron (N.pow p) N R
    rw [h, ih]; push_cast; ring

/-- the log of the size of the index set of a diagonal is its width -/
lemma logb_card_I1_of_pos (N : TN (V × V) O0 O1 O2) (hr : ∀ k, 0 < N.r k) (R : Rect V) :
    Real.logb 2 (Fintype.card (N.I1 R)) = N.Uw R := by
  rw [Fintype.card_pi]
  simp only [Fintype.card_fin]
  push_cast
  rw [Real.logb_prod _ _ fun k _ => by exact_mod_cast (hr k.1).ne']
  unfold Uw
  rw [← Finset.sum_filter]
  exact (Finset.sum_subtype (p := fun k => N.cls k = some (R, true))
    (Finset.univ.filter (fun k => N.cls k = some (R, true)))
    (fun k => by simp) (fun k => Real.logb 2 (N.r k))).symm

lemma logb_card_I1 [Fintype O0] [Fintype O1] [Fintype O2] {φ : OM.PolMul.Spectral ℂ}
    (N : TN (V × V) O0 O1 O2) (hv : 0 < value φ N.Z) (R : Rect V) :
    Real.logb 2 (Fintype.card (N.I1 R)) = N.Uw R :=
  N.logb_card_I1_of_pos (N.r_pos_of_value hv) R

lemma logb_card_I2_of_pos (N : TN (V × V) O0 O1 O2) (hr : ∀ k, 0 < N.r k) (R : Rect V) :
    Real.logb 2 (Fintype.card (N.I2 R)) = N.Vw R := by
  rw [Fintype.card_pi]
  simp only [Fintype.card_fin]
  push_cast
  rw [Real.logb_prod _ _ fun k _ => by exact_mod_cast (hr k.1).ne']
  unfold Vw
  rw [← Finset.sum_filter]
  exact (Finset.sum_subtype (p := fun k => N.cls k = some (R, false))
    (Finset.univ.filter (fun k => N.cls k = some (R, false)))
    (fun k => by simp) (fun k => Real.logb 2 (N.r k))).symm

lemma logb_card_I2 [Fintype O0] [Fintype O1] [Fintype O2] {φ : OM.PolMul.Spectral ℂ}
    (N : TN (V × V) O0 O1 O2) (hv : 0 < value φ N.Z) (R : Rect V) :
    Real.logb 2 (Fintype.card (N.I2 R)) = N.Vw R :=
  N.logb_card_I2_of_pos (N.r_pos_of_value hv) R

lemma Uw_nonneg [Fintype O0] [Fintype O1] [Fintype O2] {φ : OM.PolMul.Spectral ℂ}
    (N : TN (V × V) O0 O1 O2) (hv : 0 < value φ N.Z) (R : Rect V) : 0 ≤ N.Uw R :=
  Finset.sum_nonneg fun k _ => by split_ifs; exact N.logb_r_nonneg hv k; exact le_rfl

lemma Vw_nonneg [Fintype O0] [Fintype O1] [Fintype O2] {φ : OM.PolMul.Spectral ℂ}
    (N : TN (V × V) O0 O1 O2) (hv : 0 < value φ N.Z) (R : Rect V) : 0 ≤ N.Vw R :=
  Finset.sum_nonneg fun k _ => by split_ifs; exact N.logb_r_nonneg hv k; exact le_rfl

end TN

/-! ## Elementary inequalities -/

lemma cs_two (a b x y : ℝ) : a * x + b * y ≤ Real.sqrt (a ^ 2 + b ^ 2) * Real.sqrt (x ^ 2 + y ^ 2) := by
  rw [← Real.sqrt_mul (by positivity)]
  refine (le_abs_self _).trans (Real.abs_le_sqrt ?_)
  nlinarith [sq_nonneg (a * y - b * x)]

lemma rank_pos_of_ne_zero {m n : Type} [Fintype m] [Fintype n] {M : Matrix m n ℂ} (h : M ≠ 0) :
    0 < M.rank := by
  rcases Nat.eq_zero_or_pos M.rank with h0 | h0
  · obtain ⟨U, W, hUW⟩ := exists_rank_factor M
    exfalso; apply h
    funext i j
    rw [hUW i j]
    have : IsEmpty (Fin M.rank) := by rw [h0]; infer_instance
    exact Finset.sum_of_isEmpty _
  · exact h0

lemma rowMat_ne_zero {A B : ℕ} {f : Fin A → Fin B → Fin B → Fin A → ℂ} (h : f ≠ 0) :
    (Matrix.of fun (zx : Fin A × Fin B) (yw : Fin B × Fin A) => f zx.1 zx.2 yw.1 yw.2) ≠ 0 := by
  intro h0; apply h
  funext z x y w
  have := congrFun (congrFun h0 (z, x)) (y, w)
  simpa using this

lemma colMat_ne_zero {A B : ℕ} {f : Fin A → Fin B → Fin B → Fin A → ℂ} (h : f ≠ 0) :
    (Matrix.of fun (zy : Fin A × Fin B) (xw : Fin B × Fin A) => f zy.1 xw.1 zy.2 xw.2) ≠ 0 := by
  intro h0; apply h
  funext z x y w
  have := congrFun (congrFun h0 (z, y)) (x, w)
  simpa using this

lemma half_cs (d1 d2 x y A s : ℝ) (hs : x ^ 2 + y ^ 2 ≤ 2 * A + s) (hs0 : 0 ≤ s) :
    (d1 * x + d2 * y) / 2 ≤ Real.sqrt ((d1 ^ 2 + d2 ^ 2) / 2) * Real.sqrt (A + s) := by
  rw [← Real.sqrt_mul (by positivity)]
  refine (le_abs_self _).trans (Real.abs_le_sqrt ?_)
  have h1 := mul_nonneg (add_nonneg (sq_nonneg d1) (sq_nonneg d2)) (sub_nonneg.2 hs)
  have h2 := mul_nonneg (add_nonneg (sq_nonneg d1) (sq_nonneg d2)) hs0
  nlinarith [sq_nonneg (d1 * y - d2 * x)]

/-- `log₂ (c (n+1)²) / n → 0` -/
lemma tendsto_count {q : ℕ} (hq : 0 < q) {ι : Type} [Fintype ι] (C : ι → ℝ) (hC : ∀ i, 0 < C i) :
    Tendsto (fun j : ℕ => (∑ i, Real.logb 2 (C i * ((q * j : ℕ) + 1 : ℝ) ^ 2)) / (q * j : ℕ))
      atTop (𝓝 0) := by
  have hqj : Tendsto (fun j : ℕ => ((q * j : ℕ) : ℝ)) atTop atTop := by
    have : Tendsto (fun j : ℕ => q * j) atTop atTop :=
      tendsto_id.const_mul_atTop' hq
    exact tendsto_natCast_atTop_atTop.comp this
  have e : ∀ j : ℕ, (∑ i, Real.logb 2 (C i * ((q * j : ℕ) + 1 : ℝ) ^ 2)) / (q * j : ℕ) =
      (∑ i, Real.logb 2 (C i)) / (q * j : ℕ) +
        (2 * Fintype.card ι / Real.log 2) * (Real.log ((q * j : ℕ) + 1 : ℝ) / (q * j : ℕ)) := by
    intro j
    have hpos : (0 : ℝ) < ((q * j : ℕ) : ℝ) + 1 := by positivity
    have : ∀ i, Real.logb 2 (C i * ((q * j : ℕ) + 1 : ℝ) ^ 2) =
        Real.logb 2 (C i) + 2 * (Real.log ((q * j : ℕ) + 1 : ℝ) / Real.log 2) := by
      intro i
      rw [Real.logb_mul (hC i).ne' (by positivity), Real.logb_pow]
      simp only [Real.logb]
      ring
    simp only [this, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    ring
  simp only [e]
  have h1 : Tendsto (fun j : ℕ => (∑ i, Real.logb 2 (C i)) / (q * j : ℕ)) atTop (𝓝 0) :=
    (tendsto_const_div_atTop_nhds_zero_nat _).comp (tendsto_id.const_mul_atTop' hq)
  have h2 : Tendsto (fun j : ℕ => Real.log ((q * j : ℕ) + 1 : ℝ) / (q * j : ℕ)) atTop (𝓝 0) := by
    have hlog := Real.tendsto_pow_log_div_mul_add_atTop 1 (-1) 1 one_ne_zero
    have hx : Tendsto (fun j : ℕ => ((q * j : ℕ) : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right _ 1 hqj
    refine (hlog.comp hx).congr fun j => ?_
    simp only [Function.comp, pow_one, one_mul]
    ring_nf
  simpa using h1.add (h2.const_mul (2 * Fintype.card ι / Real.log 2))

/-! ## The core inequality -/

/-- The network-dependent input at a powered scale. The two widths are measured
in bits and the selected summand can be realized on either axis. -/
def ScaleBounds (d : V → V → ℝ) (price axisCost : ℝ) (U W : Rect V → ℝ) : Prop :=
  ∀ (q j : ℕ), 0 < q*j → ∀ α β : Rect V → ℕ,
    (∀ R, q * U R ≤ α R) → (∀ R, q * W R ≤ β R) →
    ∀ (K : Rect V → ℕ)
      (B : (R : Rect V) → Fin (K R) → Fin (2^(α R*j)) → Fin (2^(β R*j)) →
        Fin (2^(β R*j)) → Fin (2^(α R*j)) → ℂ),
      (∀ R z y y' z', ∑ m, B R m z y y' z' = if z=z' ∧ y=y' then 1 else 0) →
      ∃ μ : (R : Rect V) → Fin (K R), (∀ R, B R (μ R) ≠ 0) ∧
        ((q*j:ℕ):ℝ)*price ≤ Real.logb 2 (Fintype.card ((R : Rect V) → Fin (K R))) +
          (((q*j:ℕ):ℝ)*axisCost + ∑ R, (d R.a R.c * Real.logb 2 (TN.rowMat B R (μ R)).rank +
            d R.b R.e * Real.logb 2 (TN.colMat B R (μ R)).rank)/2)

/-- The analytic argument for a rectangle expansion, independent of its boundary format. -/
theorem core_t_of_scales (h3 : S_R108_3) {d : V → V → ℝ} {price axisCost : ℝ}
    {U W : Rect V → ℝ} (hU : ∀ R, 0 ≤ U R) (hW : ∀ R, 0 ≤ W R)
    (scales : ScaleBounds d price axisCost U W) {t : ℝ} (ht : 0 < t) :
    price ≤ axisCost + ∑ R, crad d R * Real.sqrt ((U R+t)^2+(W R+t)^2+t) := by
  -- the denominator and the integral widths
  set q : ℕ := ⌈2 / t⌉₊ + 1 with hq
  have hq0 : 0 < q := Nat.succ_pos _
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq0
  have hqt : 2 / (q : ℝ) ≤ t := by
    rw [div_le_iff₀ hqR]
    have h1 : 2 / t ≤ (⌈2 / t⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (⌈2 / t⌉₊ : ℝ) + 1 = q := by rw [hq]; push_cast; ring
    have h3' : 2 / t * t = 2 := div_mul_cancel₀ 2 ht.ne'
    nlinarith
  let α : Rect V → ℕ := fun R => ⌈(q : ℝ) * U R⌉₊ + 1
  let β : Rect V → ℕ := fun R => ⌈(q : ℝ) * W R⌉₊ + 1
  have hαq : ∀ R, (α R : ℝ) / q ≤ U R + t := by
    intro R
    rw [div_le_iff₀ hqR]
    have h1 : (⌈(q : ℝ) * U R⌉₊ : ℝ) < (q : ℝ) * U R + 1 :=
      Nat.ceil_lt_add_one (mul_nonneg hqR.le (hU R))
    have h2 : 2 ≤ t * q := by rw [div_le_iff₀ hqR] at hqt; linarith
    show ((⌈(q : ℝ) * U R⌉₊ + 1 : ℕ) : ℝ) ≤ _
    push_cast
    nlinarith
  have hβq : ∀ R, (β R : ℝ) / q ≤ W R + t := by
    intro R
    rw [div_le_iff₀ hqR]
    have h1 : (⌈(q : ℝ) * W R⌉₊ : ℝ) < (q : ℝ) * W R + 1 :=
      Nat.ceil_lt_add_one (mul_nonneg hqR.le (hW R))
    have h2 : 2 ≤ t * q := by rw [div_le_iff₀ hqR] at hqt; linarith
    show ((⌈(q : ℝ) * W R⌉₊ + 1 : ℕ) : ℝ) ≤ _
    push_cast
    nlinarith
  have hαU : ∀ R, (q : ℝ) * U R ≤ α R := fun R => by
    show _ ≤ ((⌈(q : ℝ) * U R⌉₊ + 1 : ℕ) : ℝ)
    push_cast
    linarith [Nat.le_ceil ((q : ℝ) * U R)]
  have hβV : ∀ R, (q : ℝ) * W R ≤ β R := fun R => by
    show _ ≤ ((⌈(q : ℝ) * W R⌉₊ + 1 : ℕ) : ℝ)
    push_cast
    linarith [Nat.le_ceil ((q : ℝ) * W R)]
  -- Rectangular crossing expansions, one per rectangle
  have hR := fun R : Rect V => h3 (α R) (β R) q (Nat.succ_pos _) (Nat.succ_pos _) hq0
  choose K B hC hsum hε using hR
  choose C hC using hC
  choose j0 hj0 using fun R => hε R t ht
  -- every expansion has at least one piece, so `C R > 0`
  have hKpos : ∀ R j, 0 < K R j := by
    intro R j
    rcases Nat.eq_zero_or_pos (K R j) with h0 | h0
    · have hs := hsum R j ⟨0, by positivity⟩ ⟨0, by positivity⟩ ⟨0, by positivity⟩
        ⟨0, by positivity⟩
      have : IsEmpty (Fin (K R j)) := by rw [h0]; infer_instance
      rw [Finset.sum_of_isEmpty] at hs
      simp at hs
    · exact h0
  have hCpos : ∀ R, 0 < C R := by
    intro R
    have h1 := hC R 0
    have h2 : (0 : ℝ) < K R 0 := by exact_mod_cast hKpos R 0
    have h3' : (0 : ℝ) < ((q * 0 : ℕ) + 1 : ℝ) ^ 2 := by positivity
    by_contra hc
    have : C R * ((q * 0 : ℕ) + 1 : ℝ) ^ 2 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (not_lt.mp hc) h3'.le
    linarith
  -- the bound at every large scale
  have key : ∀ j : ℕ, 1 ≤ j → (∀ R, j0 R ≤ j) →
      price ≤
        (∑ R, Real.logb 2 (C R * ((q * j : ℕ) + 1 : ℝ) ^ 2)) / (q * j : ℕ) +
          (axisCost + ∑ R, crad d R * Real.sqrt ((U R + t) ^ 2 + (W R + t) ^ 2 + t)) := by
    intro j hj1 hjj
    have hL : 0 < q * j := Nat.mul_pos hq0 hj1
    have hLR : (0 : ℝ) < ((q * j : ℕ) : ℝ) := by exact_mod_cast hL
    obtain ⟨μ,hμ,hbound⟩ := scales q j hL α β hαU hβV (fun R => K R j)
      (fun R => B R j) (fun R => hsum R j)
    -- the number of choices
    have hcount : Real.logb 2 (Fintype.card ((R : Rect V) → Fin (K R j))) ≤
        ∑ R, Real.logb 2 (C R * ((q * j : ℕ) + 1 : ℝ) ^ 2) := by
      rw [Fintype.card_pi]
      simp only [Fintype.card_fin]
      rw [Nat.cast_prod, Real.logb_prod _ _ fun R _ => by exact_mod_cast (hKpos R j).ne']
      refine Finset.sum_le_sum fun R _ => ?_
      have hK : (0 : ℝ) < K R j := by exact_mod_cast hKpos R j
      exact Real.logb_le_logb_of_le (by norm_num) hK (hC R j)
    -- each rectangle
    have hrect : ∀ R : Rect V,
        (d R.a R.c * Real.logb 2 ((TN.rowMat (fun R => B R j) R (μ R)).rank) +
          d R.b R.e * Real.logb 2 ((TN.colMat (fun R => B R j) R (μ R)).rank)) / 2 ≤
        ((q * j : ℕ) : ℝ) * (crad d R * Real.sqrt ((U R + t) ^ 2 + (W R + t) ^ 2 + t)) := by
      intro R
      have hcirc := hj0 R j (hjj R) (μ R) (hμ R)
      have hcs := half_cs (d R.a R.c) (d R.b R.e) _ _
        (((α R : ℝ) / q) ^ 2 + ((β R : ℝ) / q) ^ 2) t hcirc ht.le
      have hA : ((α R : ℝ) / q) ^ 2 + ((β R : ℝ) / q) ^ 2 + t ≤
          (U R + t) ^ 2 + (W R + t) ^ 2 + t := by
        have h1 : 0 ≤ (α R : ℝ) / q := by positivity
        have h2 : 0 ≤ (β R : ℝ) / q := by positivity
        have := pow_le_pow_left₀ h1 (hαq R) 2
        have := pow_le_pow_left₀ h2 (hβq R) 2
        linarith
      have hsq := Real.sqrt_le_sqrt hA
      have hcr := crad_nonneg d R
      have hcs' := hcs.trans (mul_le_mul_of_nonneg_left hsq (Real.sqrt_nonneg _))
      show (d R.a R.c * Real.logb 2 ((Matrix.of fun (zx : Fin (2 ^ (α R * j)) × Fin (2 ^ (β R * j)))
          (yw : Fin (2 ^ (β R * j)) × Fin (2 ^ (α R * j))) => B R j (μ R) zx.1 zx.2 yw.1 yw.2).rank) +
        d R.b R.e * Real.logb 2 ((Matrix.of fun (zy : Fin (2 ^ (α R * j)) × Fin (2 ^ (β R * j)))
          (xw : Fin (2 ^ (β R * j)) × Fin (2 ^ (α R * j))) => B R j (μ R) zy.1 xw.1 zy.2 xw.2).rank))
          / 2 ≤ _
      generalize Real.logb 2 ((Matrix.of fun (zx : Fin (2 ^ (α R * j)) × Fin (2 ^ (β R * j)))
          (yw : Fin (2 ^ (β R * j)) × Fin (2 ^ (α R * j))) => B R j (μ R) zx.1 zx.2 yw.1 yw.2).rank)
        = X at hcs' ⊢
      generalize Real.logb 2 ((Matrix.of fun (zy : Fin (2 ^ (α R * j)) × Fin (2 ^ (β R * j)))
          (xw : Fin (2 ^ (β R * j)) × Fin (2 ^ (α R * j))) => B R j (μ R) zy.1 xw.1 zy.2 xw.2).rank)
        = Y at hcs' ⊢
      have hexp : (d R.a R.c * X + d R.b R.e * Y) / 2 =
          ((q * j : ℕ) : ℝ) * ((d R.a R.c * (X / ((q * j : ℕ) : ℝ)) +
            d R.b R.e * (Y / ((q * j : ℕ) : ℝ))) / 2) := by
        field_simp
      rw [hexp]
      exact mul_le_mul_of_nonneg_left hcs' hLR.le
    have hsumR := Finset.sum_le_sum fun R (_ : R ∈ Finset.univ) => hrect R
    rw [← Finset.mul_sum] at hsumR
    have htot : ((q * j : ℕ) : ℝ) * price ≤
        (∑ R, Real.logb 2 (C R * ((q * j : ℕ) + 1 : ℝ) ^ 2)) +
          ((q * j : ℕ) : ℝ) * (axisCost + ∑ R, crad d R *
            Real.sqrt ((U R + t) ^ 2 + (W R + t) ^ 2 + t)) := by
      nlinarith
    rw [div_add' _ _ _ hLR.ne', le_div_iff₀ hLR]
    linarith
  -- let the scale grow
  set J := max 1 (Finset.univ.sup j0)
  have hev : ∀ᶠ j in atTop, price ≤
      (∑ R, Real.logb 2 (C R * ((q * j : ℕ) + 1 : ℝ) ^ 2)) / (q * j : ℕ) +
        (axisCost + ∑ R, crad d R * Real.sqrt ((U R + t) ^ 2 + (W R + t) ^ 2 + t)) := by
    refine eventually_atTop.2 ⟨J, fun j hj => key j ?_ fun R => ?_⟩
    · exact (le_max_left _ _).trans hj
    · exact (Finset.le_sup (Finset.mem_univ R)).trans ((le_max_right _ _).trans hj)
  have hlim := (tendsto_count hq0 C hCpos).add (tendsto_const_nhds (x :=
    axisCost + ∑ R, crad d R * Real.sqrt ((U R + t) ^ 2 + (W R + t) ^ 2 + t)))
  rw [zero_add] at hlim
  exact ge_of_tendsto hlim hev

/-- Turn a log-cardinality bound into an index embedding. -/
def dyadicEmbedding {I : Type} [Fintype I] (hn : Nonempty I) (w : ℕ)
    (h : Real.logb 2 (Fintype.card I) ≤ w) : I ↪ Fin (2^w) := by
  have hp : (0:ℝ) < Fintype.card I := by exact_mod_cast Fintype.card_pos_iff.2 hn
  have hb := (Real.logb_le_logb (by norm_num : (1:ℝ)<2) hp (by positivity : (0:ℝ)<(2:ℝ)^w)).1
    (by simpa [Real.logb_pow,Real.logb_self_eq_one (by norm_num : (1:ℝ)<2)] using h)
  apply (Function.Embedding.nonempty_of_card_le ?_).some
  rw [Fintype.card_fin]
  exact_mod_cast hb

/-- the core inequality with slack `t`: widths enlarged by `t` and the circle by `t` -/
theorem core_t (h3 : S_R108_3) {φ : OM.PolMul.Spectral ℂ} {τ : Fin 3 → V} {d : V → V → ℝ}
    (hd : Adm φ τ d)
    [Fintype O0] [Fintype O1] [Fintype O2] (M : TN (V × V) O0 O1 O2)
    (hM : M.Local (fun i => (τ i, τ i))) (hv : 0 < value φ M.Z) {t : ℝ} (ht : 0 < t) :
    Real.logb 2 (value φ M.Z) ≤ M.ndCost d +
      ∑ R, crad d R * Real.sqrt ((M.Uw R + t) ^ 2 + (M.Vw R + t) ^ 2 + t) := by
  apply core_t_of_scales h3 (M.Uw_nonneg hv) (M.Vw_nonneg hv) _ ht
  intro q j hL α β hα hβ K B hB
  let N := M.pow (q*j)
  have hp : value φ N.Z = value φ M.Z ^ (q*j) := value_pow φ M hv _
  have hvN : 0 < value φ N.Z := hp ▸ pow_pos hv _
  let u (R : Rect V) : N.I1 R ↪ Fin (2^(α R*j)) := dyadicEmbedding
    ⟨fun k => ⟨0,N.r_pos_of_value hvN k.1⟩⟩ _ (by
      rw [N.logb_card_I1 hvN,TN.Uw_pow]
      push_cast
      nlinarith [mul_le_mul_of_nonneg_right (hα R) (Nat.cast_nonneg j)])
  let v (R : Rect V) : N.I2 R ↪ Fin (2^(β R*j)) := dyadicEmbedding
    ⟨fun k => ⟨0,N.r_pos_of_value hvN k.1⟩⟩ _ (by
      rw [N.logb_card_I2 hvN,TN.Vw_pow]
      push_cast
      nlinarith [mul_le_mul_of_nonneg_right (hβ R) (Nat.cast_nonneg j)])
  obtain ⟨μ,hm,hp'⟩ := single_scale hd N (hM.pow _) hvN B hB u v
  exact ⟨μ,hm,by simpa only [hp,Real.logb_pow,N,TN.ndCost_pow] using hp'⟩

/-- **The core inequality** summed over the rectangles: at admissible prices
`d` on `V`, every local network on `V × V` with positive value has
`log₂ value ≤ ndCost + Σ_R crad R · √(U_R² + V_R²)`. -/
theorem core (h3 : S_R108_3) {φ : OM.PolMul.Spectral ℂ} {τ : Fin 3 → V} {d : V → V → ℝ}
    (hd : Adm φ τ d) [Fintype O0] [Fintype O1] [Fintype O2] (M : TN (V × V) O0 O1 O2)
    (hM : M.Local (fun i => (τ i, τ i))) (hv : 0 < value φ M.Z) :
    Real.logb 2 (value φ M.Z) ≤ Hd d (M.ndCost d) M.Uw M.Vw := by
  have hg : Continuous fun t : ℝ => M.ndCost d +
      ∑ R, crad d R * Real.sqrt ((M.Uw R + t) ^ 2 + (M.Vw R + t) ^ 2 + t) := by
    fun_prop
  have hlim := (hg.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), Real.logb 2 (value φ M.Z) ≤ M.ndCost d +
      ∑ R, crad d R * Real.sqrt ((M.Uw R + t) ^ 2 + (M.Vw R + t) ^ 2 + t) :=
    eventually_nhdsWithin_of_forall fun t ht => core_t h3 hd M hM hv ht
  have := ge_of_tendsto hlim hev
  simpa [Hd] using this

end OM.NNN30.Net
