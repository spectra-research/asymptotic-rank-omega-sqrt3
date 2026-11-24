import Lib.OM.Omega

/-! # Weighted polynomial multiplication profiles

The product in the proof of Amanov–van den Berg–Zuiddam, Proposition 4.14.
The two arguments of the product scale its two polynomial inputs independently.
-/

namespace OM.PolMulRect

open OM.PolMul Semicontinuity
open scoped BigOperators

universe u
variable {F : Type u} [Field F]

/-- The polynomial profile after moving leg `i` to `π i`. -/
noncomputable def profile (φ : Spectral F) (π : Equiv.Perm (Fin 3)) (a b : ℕ+) : ℝ :=
  Spectral.eval (Spectral.perm π φ) (polmul a b)

/-- On the diagonal this is the six-permutation product `Gₙ` of Proposition 4.14. -/
noncomputable def weightedProduct (φ : Spectral F) (x : Fin 3 → ℕ+) (a b : ℕ+) : ℝ :=
  ∏ π : Equiv.Perm (Fin 3), profile φ π (a * x (π 0)) (b * x (π 1)) ^ (x (π 2) : ℕ)

/-- Exchanging the inputs of polynomial multiplication permutes its first two legs. -/
theorem profile_swap (φ : Spectral F) (π : Equiv.Perm (Fin 3)) (a b : ℕ+) :
    profile φ (π * Equiv.swap 0 1) b a = profile φ π a b := by
  let s : Equiv.Perm (Fin 3) := Equiv.swap 0 1
  have hfmt (i : Fin 3) :
      ((fmt b a (b + a - 1) ∘ s.symm) i : ℕ) = (fmt a b (a + b - 1) i : ℕ) := by
    fin_cases i <;> simp [fmt, s, Equiv.swap_apply_def, add_comm]
  have hswap : perm s (polmul (F := F) b a) ∼ₜ polmul a b := by
    apply SpectralFacts.restrictsEquiv_of_index_equiv (fun i => finCongr (hfmt i))
    intro idx
    simp only [perm, KTensor.legReindex_apply, polmul]
    congr 1
    apply propext
    change (idx 2).val = (idx 1).val + (idx 0).val ↔
      (idx 2).val = (idx 0).val + (idx 1).val
    omega
  change Spectral.eval (Spectral.perm (π * s) φ) (polmul b a) = _
  rw [← Superadditivity.eval_perm_perm, Superadditivity.eval_perm (Spectral.perm π φ)]
  exact Superadditivity.eval_restrictsEquiv _ hswap

/-- Exchanging the two scaling arguments reindexes the product by the input swap. -/
theorem weightedProduct_swap (φ : Spectral F) (x : Fin 3 → ℕ+) (a b : ℕ+) :
    weightedProduct φ x a b = weightedProduct φ x b a := by
  let s : Equiv.Perm (Fin 3) := Equiv.swap 0 1
  let f (π : Equiv.Perm (Fin 3)) :=
    profile φ π (b * x (π 0)) (a * x (π 1)) ^ (x (π 2) : ℕ)
  calc
    _ = ∏ π : Equiv.Perm (Fin 3), f (π * s) := by
      apply Finset.prod_congr rfl
      intro π _
      simp only [f, Equiv.Perm.coe_mul, Function.comp_apply, s, Equiv.swap_apply_left,
        Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne (by decide +kernel : (2 : Fin 3) ≠ 0)
          (by decide +kernel : (2 : Fin 3) ≠ 1), profile_swap]
    _ = _ := Equiv.prod_comp (Equiv.mulRight s) f

private lemma one_le_profile_eval (φ : Spectral F) (a b : ℕ+) :
    1 ≤ Spectral.eval φ (polmul a b) :=
  (show (1 : ℝ) ≤ ((min a b : ℕ+) : ℕ) by exact_mod_cast (min a b).pos).trans
    (Profiles.proof_PR_1 F φ a b).1

theorem one_le_weightedProduct (φ : Spectral F) (x : Fin 3 → ℕ+) (a b : ℕ+) :
    1 ≤ weightedProduct φ x a b :=
  Finset.one_le_prod₀ fun π _ => one_le_pow₀ (one_le_profile_eval (Spectral.perm π φ) _ _)

/-- The two discrete growth hypotheses for a rooted oriented profile, in the
natural-number indexing used by AN.2. -/
private lemma rooted_profile_laws (φ ψ : Spectral F) (a : ℕ+) {p : ℝ}
    (hp : 0 < p) (he : Real.logb 2 (Spectral.eval φ (matMul 1 1 2)) = p)
    (hswap : ∀ m : ℕ+, Spectral.eval φ (swap23 (polmul a m)) =
      Spectral.eval ψ (polmul a m)) :
    let g := fun m : ℕ => Spectral.eval φ (polmul a m.toPNat') ^ (1 / p)
    let h := fun m : ℕ => Spectral.eval ψ (polmul a m.toPNat') ^ (1 / p)
    (∀ m : ℕ, 2 ≤ m → g (m + 1) + g (m - 1) ≤ 2 * g m) ∧
    (∀ m : ℕ, 1 ≤ m → 2 * g m + h m ≤ g (3 * m + (a : ℕ) - 1)) := by
  have hpφ := he.symm ▸ hp
  constructor
  · intro m hm
    let b := m.toPNat'
    have hb : (b : ℕ) = m := PNat.toPNat'_coe (by omega)
    have h2 : 2 ≤ b := (PNat.coe_le_coe _ _).mp (by simpa only [hb, PNat.val_ofNat] using hm)
    have H := Profiles.proof_PR_2 F φ hpφ a b h2
    change Spectral.eval φ (polmul a (b + 1)) ^ (1 / Real.logb 2 (Spectral.eval φ (matMul 1 1 2))) +
        Spectral.eval φ (polmul a (b - 1)) ^ (1 / Real.logb 2 (Spectral.eval φ (matMul 1 1 2))) ≤
      2 * Spectral.eval φ (polmul a b) ^ (1 / Real.logb 2 (Spectral.eval φ (matMul 1 1 2))) at H
    have hs : (m + 1).toPNat' = b + 1 := by
      apply PNat.eq
      simp only [PNat.toPNat'_coe (by omega : 0 < m + 1), PNat.add_coe, PNat.val_ofNat, hb]
    have hd : (m - 1).toPNat' = b - 1 := by
      change _ = ((b : ℕ) - 1).toPNat'
      rw [hb]
    rw [← hs, ← hd, he] at H
    exact H
  · intro m hm
    let b := m.toPNat'
    have hb : (b : ℕ) = m := PNat.toPNat'_coe hm
    have ht : (3 * m + (a : ℕ) - 1).toPNat' = 3 * b + a - 1 := by
      change _ = (3 * (b : ℕ) + (a : ℕ) - 1).toPNat'
      rw [hb]
    have H := Profiles.proof_PR_3 F φ hpφ a b
    change 2 * Spectral.eval φ (polmul a b) ^ (1 / Real.logb 2 (Spectral.eval φ (matMul 1 1 2))) +
        Spectral.eval φ (swap23 (polmul a b)) ^ (1 / Real.logb 2 (Spectral.eval φ (matMul 1 1 2))) ≤
      Spectral.eval φ (polmul a (3 * b + a - 1)) ^
        (1 / Real.logb 2 (Spectral.eval φ (matMul 1 1 2))) at H
    rw [← ht, he, hswap] at H
    exact H

/-- Unequal steps in a pair of profiles with a common first leg.
The exponent on each ratio is the step taken by the other profile. -/
theorem paired_profile_ratio (φ : Spectral F) (a u v r s : ℕ+) :
    let ψ := Spectral.perm (Equiv.swap 1 2) φ
    let p := Real.logb 2 (Spectral.eval φ (matMul 1 1 2))
    let D : ℝ := (u : ℝ) + v + r + s + a - 1
    let c : ℝ := 4 * r * s / ((r : ℝ) + s)
    (D / (D - c)) ^ (((r : ℝ) + s) * p) ≤
      (Spectral.eval φ (polmul a (u + r)) / Spectral.eval φ (polmul a u)) ^ (s : ℕ) *
      (Spectral.eval ψ (polmul a (v + s)) / Spectral.eval ψ (polmul a v)) ^ (r : ℕ) := by
  intro ψ p D c
  have evpos (χ : Spectral F) (m : ℕ+) : 0 < Spectral.eval χ (polmul a m) :=
    zero_lt_one.trans_le (one_le_profile_eval χ a m)
  have hp0 : 0 ≤ p := Superadditivity.spectral_exponent_nonneg φ
  rcases hp0.eq_or_lt with hp | hp
  · have mono (χ : Spectral F) (b k : ℕ+) :
        1 ≤ Spectral.eval χ (polmul a (b + k)) / Spectral.eval χ (polmul a b) :=
      (one_le_div (evpos χ b)).2 ((Profiles.proof_PR_1 F χ a b).2.2.2 _ (PNat.lt_add_right b k).le)
    rw [← hp, mul_zero, Real.rpow_zero]
    exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ (mono φ u r)) (one_le_pow₀ (mono ψ v s))
  · let g (m : ℕ) := Spectral.eval φ (polmul a m.toPNat') ^ (1 / p)
    let h (m : ℕ) := Spectral.eval ψ (polmul a m.toPNat') ^ (1 / p)
    have heψ : Real.logb 2 (Spectral.eval ψ (matMul 1 1 2)) = p :=
      congrArg (Real.logb 2) (Superadditivity.eval_swap_matMul_11 φ 2)
    have hg := rooted_profile_laws φ ψ a hp rfl fun m =>
      (Superadditivity.eval_perm φ (Equiv.swap 1 2) (polmul a m)).symm
    have hh := rooted_profile_laws ψ φ a hp heψ fun m => Superadditivity.eval_swap_swap φ (polmul a m)
    have H := Analysis.proof_AN_2 (a : ℕ) a.pos g h
      (fun m _ => Real.rpow_pos_of_pos (evpos φ m.toPNat') _)
      (fun m _ => Real.rpow_pos_of_pos (evpos ψ m.toPNat') _)
      hg.1 hh.1 hg.2 hh.2 u v r s u.pos v.pos r.pos s.pos
    have hD : (((u : ℕ) + v + r + s + a - 1 : ℕ) : ℝ) = D := by
      have ha := a.pos
      rw [Nat.cast_sub (by omega)]
      push_cast
      rfl
    have hc : c ≤ (r : ℝ) + s := by
      apply (div_le_iff₀ (by positivity)).2
      nlinarith only [sq_nonneg ((r : ℝ) - s)]
    have hden : 0 < D - c := by
      have ha : (1 : ℝ) ≤ a := by exact_mod_cast a.pos
      have hu : (0 : ℝ) < u := by positivity
      have hv : (0 : ℝ) < v := by positivity
      dsimp [D]
      linarith
    have hc0 : 0 ≤ c := by dsimp [c]; positivity
    have hbase : 0 ≤ D / (D - c) := div_nonneg (by linarith) hden.le
    rw [hD, Nat.cast_add] at H
    change (D / (D - c)) ^ ((r : ℝ) + s) ≤ _ at H
    have Hpow := Real.rpow_le_rpow (Real.rpow_nonneg hbase _) H hp.le
    have hroot {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (k : ℕ) :
        ((x ^ (1 / p) / y ^ (1 / p)) ^ (k : ℝ)) ^ p = (x / y) ^ k := by
      rw [← Real.div_rpow hx hy, ← Real.rpow_mul (div_nonneg hx hy),
        ← Real.rpow_mul (div_nonneg hx hy)]
      rw [show 1 / p * (k : ℝ) * p = k by field_simp, Real.rpow_natCast]
    have hrpos (χ : Spectral F) (i j : ℕ) :
        0 ≤ Spectral.eval χ (polmul a i.toPNat') ^ (1 / p) /
          Spectral.eval χ (polmul a j.toPNat') ^ (1 / p) :=
      div_nonneg (Real.rpow_nonneg (evpos χ _).le _) (Real.rpow_nonneg (evpos χ _).le _)
    dsimp only [g, h] at Hpow
    rw [← Real.rpow_mul hbase,
      Real.mul_rpow (Real.rpow_nonneg (hrpos φ _ _) _) (Real.rpow_nonneg (hrpos ψ _ _) _),
      hroot (evpos φ _).le (evpos φ _).le, hroot (evpos ψ _).le (evpos ψ _).le] at Hpow
    rw [← PNat.add_coe, ← PNat.add_coe, PNat.coe_toPNat', PNat.coe_toPNat',
      PNat.coe_toPNat', PNat.coe_toPNat'] at Hpow
    exact Hpow

/-- Bernoulli's inequality compares the AN.2 denominator with a common
base for all six orientations. -/
private lemma step_base_le {k S D c : ℝ} (hk : 0 < k) (hS : 0 < S)
    (hc : 0 ≤ c) (hcS : c ≤ S) (hcD : c < D) (hD : D ≤ k * S) :
    ((k + 1) / k) ^ (c / S) ≤ D / (D - c) := by
  have hDpos := hc.trans_lt hcD
  have he : (k + 1) / k = 1 + 1 / k := by field_simp
  calc
    _ ≤ 1 + c / S * (1 / k) := by
      rw [he]
      apply rpow_one_add_le_one_add_mul_self _ (div_nonneg hc hS.le) ((div_le_one hS).2 hcS)
      linarith [one_div_pos.mpr hk]
    _ = 1 + c / (k * S) := by ring
    _ ≤ 1 + c / D := by gcongr
    _ ≤ D / (D - c) := by
      rw [le_div_iff₀ (sub_pos.mpr hcD)]
      field_simp [hDpos.ne']
      nlinarith only [sq_nonneg c]

private lemma paired_weighted_step (φ : Spectral F) (a n i j k : ℕ+) (ha : a ≤ n + 1) :
    let p := Real.logb 2 (Spectral.eval φ (matMul 1 1 2))
    let ψ := Spectral.perm (Equiv.swap 1 2) φ
    (((n : ℝ) + 2) / (n + 1)) ^ (4 * p * j * k / ((i : ℝ) + j + k)) ≤
      (Spectral.eval φ (polmul (a * i) ((n + 1) * j)) /
        Spectral.eval φ (polmul (a * i) (n * j))) ^ (k : ℕ) *
      (Spectral.eval ψ (polmul (a * i) ((n + 1) * k)) /
        Spectral.eval ψ (polmul (a * i) (n * k))) ^ (j : ℕ) := by
  intro p ψ
  let S : ℝ := (i : ℝ) + j + k
  let D : ℝ := (n : ℝ) * j + n * k + j + k + a * i - 1
  let c : ℝ := 4 * j * k / ((j : ℝ) + k)
  let b : ℝ := ((n : ℝ) + 2) / (n + 1)
  have hS : 0 < S := by dsimp [S]; positivity
  have hc0 : 0 ≤ c := by dsimp [c]; positivity
  have hjk : 0 < (j : ℝ) + k := by positivity
  have hc : c ≤ (j : ℝ) + k := by
    apply (div_le_iff₀ hjk).2
    nlinarith only [sq_nonneg ((j : ℝ) - k)]
  have hcS : c ≤ S := by dsimp [S]; linarith [show (0 : ℝ) < i by positivity]
  have hcD : c < D := by
    have hai : (1 : ℝ) ≤ (a : ℝ) * i := by exact_mod_cast (a * i).pos
    dsimp [D]
    linarith [show 0 < (n : ℝ) * j by positivity, show 0 < (n : ℝ) * k by positivity]
  have hD : D ≤ ((n : ℝ) + 1) * S := by
    have ha' : (a : ℝ) ≤ n + 1 := by exact_mod_cast ha
    dsimp [D, S]
    nlinarith only [mul_le_mul_of_nonneg_right ha' (show 0 ≤ (i : ℝ) by positivity)]
  have hbase : b ^ (c / S) ≤ D / (D - c) := by
    simpa only [b, show (n : ℝ) + 1 + 1 = n + 2 by ring] using
      step_base_le (by positivity : 0 < (n : ℝ) + 1) hS hc0 hcS hcD hD
  have hp : 0 ≤ p := Superadditivity.spectral_exponent_nonneg φ
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have h := Real.rpow_le_rpow (Real.rpow_nonneg hb _) hbase (mul_nonneg hjk.le hp)
  rw [← Real.rpow_mul hb] at h
  have hexp : c / S * (((j : ℝ) + k) * p) = 4 * p * j * k / S := by
    dsimp [c]
    field_simp [hjk.ne']
  rw [hexp] at h
  have pair := paired_profile_ratio φ (a * i) (n * j) (n * k) j k
  dsimp only at pair
  rw [← add_one_mul, ← add_one_mul] at pair
  simpa only [D, S, c, b, p, ψ, PNat.mul_coe, Nat.cast_mul, add_comm (1 : ℕ+) n] using h.trans (by
    simpa only [D, c, p, PNat.mul_coe, Nat.cast_mul] using pair)

private def cycle : Fin 3 → Equiv.Perm (Fin 3)
  | 0 => 1
  | 1 => finRotate 3
  | 2 => (finRotate 3)⁻¹

private def pairedPerm : Fin 3 × Fin 2 → Equiv.Perm (Fin 3)
  | (i, 0) => cycle i
  | (i, 1) => cycle i * Equiv.swap 1 2

private noncomputable def pairedEquiv : (Fin 3 × Fin 2) ≃ Equiv.Perm (Fin 3) :=
  Equiv.ofBijective pairedPerm (by decide +kernel)

private lemma product_pairs (f : Equiv.Perm (Fin 3) → ℝ) :
    (∏ i : Fin 3, f (cycle i) * f (cycle i * Equiv.swap 1 2)) = ∏ π, f π := by
  calc
    _ = ∏ t : Fin 3 × Fin 2, f (pairedPerm t) := by
      rw [Fintype.prod_prod_type]
      apply Finset.prod_congr rfl
      intro i _
      rw [Fin.prod_univ_two]
      rfl
    _ = _ := Equiv.prod_comp pairedEquiv f

/-- Sum of the three integral weights. -/
def weightSum (x : Fin 3 → ℕ+) : ℕ := (x 0 : ℕ) + x 1 + x 2

private lemma weightSum_perm (x : Fin 3 → ℕ+) (π : Equiv.Perm (Fin 3)) :
    (x (π 0) : ℕ) + x (π 1) + x (π 2) = weightSum x := by
  simpa only [weightSum, Fin.sum_univ_three] using Equiv.sum_comp π (fun i => (x i : ℕ))

/-- Each omitted leg occurs twice among the six permutations. -/
private lemma sum_omitted_weights (x : Fin 3 → ℕ+) :
    (∑ π : Equiv.Perm (Fin 3), (x (π 2) : ℕ)) = 2 * weightSum x := by
  rw [← Equiv.sum_comp pairedEquiv (fun π => (x (π 2) : ℕ)), Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two, Fin.sum_univ_three]
  change ((x 2 : ℕ) + x 1) + (x 0 + (x 2 : ℕ)) + (x 1 + (x 0 : ℕ)) =
    2 * ((x 0 : ℕ) + x 1 + x 2)
  omega

/-- PR.1 bounds the diagonal product by a power of the total input size. -/
theorem weightedProduct_upper (φ : Spectral F) (x : Fin 3 → ℕ+) (n : ℕ+) :
    weightedProduct φ x n n ≤ ((n : ℝ) * weightSum x) ^ (2 * weightSum x) := by
  calc
    _ ≤ ∏ π : Equiv.Perm (Fin 3), ((n : ℝ) * weightSum x) ^ (x (π 2) : ℕ) := by
      apply Finset.prod_le_prod₀
      · intro π _
        exact pow_nonneg (zero_le_one.trans (one_le_profile_eval _ _ _)) _
      · intro π _
        apply pow_le_pow_left₀ (zero_le_one.trans (one_le_profile_eval _ _ _))
        refine (Profiles.proof_PR_1 F (Spectral.perm π φ) _ _).2.1.trans ?_
        have hsum : (x (π 0) : ℕ) + x (π 1) ≤ weightSum x := by
          rw [← weightSum_perm x π]
          omega
        have hd : ((n * x (π 0) + n * x (π 1) - 1 : ℕ+) : ℕ) ≤ (n : ℕ) * weightSum x := calc
          _ ≤ ((n * x (π 0) + n * x (π 1) : ℕ+) : ℕ) := PNat.sub_le _ _
          _ = (n : ℕ) * ((x (π 0) : ℕ) + x (π 1)) := by
            simp only [PNat.add_coe, PNat.mul_coe, Nat.mul_add]
          _ ≤ _ := Nat.mul_le_mul_left _ hsum
        exact_mod_cast hd
    _ = _ := by rw [Finset.prod_pow_eq_pow_sum, sum_omitted_weights]

open Foundations.PairUnitExponents

/-- The singleton leg of the matrix pair used by PR.2 moves to `i`. -/
private lemma cycle_exponent (φ : Spectral F) (i : Fin 3) :
    Real.logb 2 (Spectral.eval (Spectral.perm (cycle i) φ) (matMul 1 1 2)) = theta φ i := by
  rw [Superadditivity.eval_perm]
  fin_cases i
  · change Real.logb 2 (Spectral.eval φ (matMul 1 1 2)) = _
    rw [OM.Omega.eval_matMul_11n]
    norm_num [Real.logb_rpow]
  · change Real.logb 2 (Spectral.eval φ (perm (finRotate 3) (matMul 1 1 2))) = theta φ 1
    rw [Superadditivity.eval_rotate_matMul, OM.Omega.eval_matMul_n11]
    norm_num [Real.logb_rpow]
  · change Real.logb 2 (Spectral.eval φ (perm (finRotate 3)⁻¹ (matMul 1 1 2))) = theta φ 2
    rw [Superadditivity.eval_rotate_inv_matMul,
      OM.Omega.eval_matMul_1n1]
    norm_num [Real.logb_rpow]

/-- Weighted sum of the three pair exponents in omitted-leg order. -/
noncomputable def quadraticWeight (φ : Spectral F) (x : Fin 3 → ℕ+) : ℝ :=
  theta φ 0 * x 1 * x 2 + theta φ 1 * x 0 * x 2 + theta φ 2 * x 0 * x 1

/-- Increase the second polynomial input, and multiply the three paired
inequalities at a fixed scale for the first input. -/
private lemma second_profile_step (φ : Spectral F) (x : Fin 3 → ℕ+) (a n : ℕ+)
    (ha : a ≤ n + 1) :
    (((n : ℝ) + 2) / (n + 1)) ^ (4 * quadraticWeight φ x / weightSum x) ≤
      weightedProduct φ x a (n + 1) / weightedProduct φ x a n := by
  let b : ℝ := ((n : ℝ) + 2) / (n + 1)
  let e (i : Fin 3) : ℝ := 4 * theta φ i * x (cycle i 1) * x (cycle i 2) / weightSum x
  let R (π : Equiv.Perm (Fin 3)) : ℝ :=
    (profile φ π (a * x (π 0)) ((n + 1) * x (π 1)) /
      profile φ π (a * x (π 0)) (n * x (π 1))) ^ (x (π 2) : ℕ)
  have hpair (i : Fin 3) : b ^ e i ≤ R (cycle i) * R (cycle i * Equiv.swap 1 2) := by
    let σ := cycle i
    have H := paired_weighted_step (Spectral.perm σ φ) a n (x (σ 0)) (x (σ 1)) (x (σ 2)) ha
    dsimp only at H
    have hsum : (x (σ 0) : ℝ) + x (σ 1) + x (σ 2) = weightSum x := by
      exact_mod_cast weightSum_perm x σ
    rw [cycle_exponent φ i, hsum] at H
    simpa only [R, profile, Equiv.Perm.coe_mul, Function.comp_apply, Equiv.swap_apply_left,
      Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne (by decide +kernel : (0 : Fin 3) ≠ 1)
        (by decide +kernel : (0 : Fin 3) ≠ 2), Superadditivity.eval_perm_perm] using! H
  have hb : 0 < b := by dsimp [b]; positivity
  have hprod : (∏ i : Fin 3, b ^ e i) ≤ ∏ i : Fin 3, R (cycle i) * R (cycle i * Equiv.swap 1 2) :=
    Finset.prod_le_prod₀ (fun _ _ => Real.rpow_nonneg hb.le _) fun i _ => hpair i
  have hsum : e 0 + e 1 + e 2 = 4 * quadraticWeight φ x / weightSum x := by
    change 4 * theta φ 0 * x 1 * x 2 / _ + 4 * theta φ 1 * x 2 * x 0 / _ +
      4 * theta φ 2 * x 0 * x 1 / _ = _
    unfold quadraticWeight
    ring
  rw [Fin.prod_univ_three, ← Real.rpow_add hb, ← Real.rpow_add hb, hsum, product_pairs] at hprod
  simpa only [R, weightedProduct, div_pow, Finset.prod_div_distrib] using hprod

/-- The full diagonal step of the weighted six-permutation product. -/
theorem weightedProduct_step (φ : Spectral F) (x : Fin 3 → ℕ+) (n : ℕ+) :
    (((n : ℝ) + 2) / (n + 1)) ^ (8 * quadraticWeight φ x / weightSum x) ≤
      weightedProduct φ x (n + 1) (n + 1) / weightedProduct φ x n n := by
  let b : ℝ := ((n : ℝ) + 2) / (n + 1)
  let E : ℝ := 4 * quadraticWeight φ x / weightSum x
  have hb : 0 < b := by dsimp [b]; positivity
  have pos (a d : ℕ+) := zero_lt_one.trans_le (one_le_weightedProduct φ x a d)
  calc
    _ = b ^ E * b ^ E := by
      rw [← Real.rpow_add hb]
      congr 1
      dsimp [E]
      ring
    _ ≤ (weightedProduct φ x n (n + 1) / weightedProduct φ x n n) *
        (weightedProduct φ x (n + 1) (n + 1) / weightedProduct φ x (n + 1) n) :=
      mul_le_mul (second_profile_step φ x n n (PNat.lt_add_right n 1).le)
        (second_profile_step φ x (n + 1) n le_rfl) (Real.rpow_nonneg hb.le _)
        (div_nonneg (pos _ _).le (pos _ _).le)
    _ = _ := by
      rw [weightedProduct_swap φ x n (n + 1)]
      field_simp [(pos (n + 1) n).ne', (pos n n).ne']

end OM.PolMulRect
