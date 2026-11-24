import Lib.OM.NNN30.Crossing.Wick

/-! # The basis `X^k (cX + d)^(D-k)` of polynomials of degree at most `D`

`trL c d D P = Σ_{j ≤ D} p_j X^j (cX + d)^(D-j)` is an involution on polynomials of degree at most
`D` when `c (1 + d) = 0` and `d² = 1` (for `X - 1` and for `-X - 1`). -/

namespace OM.NNN30.Crossing

open Polynomial

noncomputable def trL (c d : ℂ) (D : ℕ) : ℂ[X] →ₗ[ℂ] ℂ[X] :=
  ∑ j ∈ Finset.range (D + 1), (lcoeff ℂ j).smulRight (X ^ j * (C c * X + C d) ^ (D - j))

theorem trL_apply (c d : ℂ) (D : ℕ) (P : ℂ[X]) :
    trL c d D P = ∑ j ∈ Finset.range (D + 1), P.coeff j • (X ^ j * (C c * X + C d) ^ (D - j)) := by
  simp [trL, LinearMap.sum_apply, LinearMap.smulRight_apply]

theorem trL_X_pow (c d : ℂ) (D m : ℕ) (hm : m ≤ D) :
    trL c d D (X ^ m) = X ^ m * (C c * X + C d) ^ (D - m) := by
  rw [trL_apply]
  simp only [coeff_X_pow]
  rw [Finset.sum_eq_single m]
  · simp
  · intro j _ hj; simp [hj]
  · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h

theorem eq_sum_coeff_smul (P : ℂ[X]) (D : ℕ) (hP : P.natDegree ≤ D) :
    P = ∑ j ∈ Finset.range (D + 1), P.coeff j • (X ^ j : ℂ[X]) := by
  conv_lhs => rw [P.as_sum_range' (D + 1) (by omega)]
  apply Finset.sum_congr rfl
  intro j _
  rw [← C_mul_X_pow_eq_monomial, smul_eq_C_mul]

theorem trL_trL_X_pow (c d : ℂ) (hc : c * (1 + d) = 0) (hd : d * d = 1) (D j : ℕ) (hj : j ≤ D) :
    trL c d D (trL c d D (X ^ j)) = X ^ j := by
  rw [trL_X_pow c d D j hj]
  set n := D - j with hn
  have hexp : (X ^ j * (C c * X + C d) ^ n : ℂ[X]) =
      ∑ i ∈ Finset.range (n + 1), ((n.choose i : ℂ) * c ^ i * d ^ (n - i)) • (X ^ (j + i) : ℂ[X]) := by
    rw [add_pow, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [smul_eq_C_mul, mul_pow, ← C_pow, ← C_pow, pow_add]
    simp only [map_mul, map_natCast]
    ring
  rw [hexp, map_sum]
  have hstep : ∀ i ∈ Finset.range (n + 1),
      trL c d D (((n.choose i : ℂ) * c ^ i * d ^ (n - i)) • (X ^ (j + i) : ℂ[X])) =
        X ^ j * ((C c * X) ^ i * (C d * (C c * X + C d)) ^ (n - i) * (n.choose i : ℂ[X])) := by
    intro i hi
    have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    rw [map_smul, trL_X_pow c d D (j + i) (by omega), show D - (j + i) = n - i by omega,
      smul_eq_C_mul, mul_pow, mul_pow, ← C_pow, ← C_pow, pow_add]
    simp only [map_mul, map_natCast]
    ring
  rw [Finset.sum_congr rfl hstep, ← Finset.mul_sum, ← add_pow]
  have : (C c * X + C d * (C c * X + C d) : ℂ[X]) = 1 := by
    have e : (C c * X + C d * (C c * X + C d) : ℂ[X]) = C (c * (1 + d)) * X + C (d * d) := by
      simp only [map_mul, map_add, map_one]; ring
    rw [e, hc, hd]; simp
  rw [this, one_pow, mul_one]

/-- The involution property. -/
theorem trL_trL (c d : ℂ) (hc : c * (1 + d) = 0) (hd : d * d = 1) (D : ℕ) (P : ℂ[X])
    (hP : P.natDegree ≤ D) : trL c d D (trL c d D P) = P := by
  conv_lhs => rw [eq_sum_coeff_smul P D hP]
  rw [map_sum, map_sum]
  conv_rhs => rw [eq_sum_coeff_smul P D hP]
  apply Finset.sum_congr rfl
  intro j hj
  rw [map_smul, map_smul, trL_trL_X_pow c d hc hd D j (by
    have := Finset.mem_range.mp hj; omega)]

theorem coeff_trL (c d : ℂ) (D : ℕ) (P : ℂ[X]) (k : ℕ) (hk : k ≤ D) :
    (trL c d D P).coeff k =
      ∑ j ∈ Finset.range (k + 1), P.coeff j * (X ^ j * (C c * X + C d) ^ (D - j) : ℂ[X]).coeff k := by
  rw [trL_apply, finsetSum_coeff]
  have hsub : Finset.range (k + 1) ⊆ Finset.range (D + 1) :=
    Finset.range_subset_range.mpr (by omega)
  rw [← Finset.sum_subset hsub]
  · apply Finset.sum_congr rfl
    intro j _
    rw [coeff_smul, smul_eq_mul]
  · intro j hj hjk
    have : k < j := by simp at hjk; omega
    rw [coeff_smul, coeff_X_pow_mul', if_neg (by omega), smul_zero]

theorem X_sub_one_eq : (C (1 : ℂ) * X + C (-1) : ℂ[X]) = X - 1 := by simp; ring

theorem coeff_X_sub_one_pow_top (n : ℕ) : ((X - 1 : ℂ[X]) ^ n).coeff n = 1 := by
  have hm : ((X - C 1 : ℂ[X]) ^ n).Monic := (monic_X_sub_C 1).pow n
  have hd : ((X - C 1 : ℂ[X]) ^ n).natDegree = n := by
    rw [natDegree_pow, natDegree_X_sub_C, mul_one]
  have := hm.coeff_natDegree
  rw [hd] at this
  simpa using this

/-- The decomposition in the basis `X^k (X-1)^(D-k)`. -/
theorem basis_decomp (D : ℕ) (P : ℂ[X]) (hP : P.natDegree ≤ D) :
    P = ∑ k ∈ Finset.range (D + 1),
      (trL 1 (-1) D P).coeff k • (X ^ k * (X - 1) ^ (D - k) : ℂ[X]) := by
  conv_lhs => rw [← trL_trL 1 (-1) (by ring) (by ring) D P hP]
  rw [trL_apply, X_sub_one_eq]

/-- The coefficients sum to the leading coefficient. -/
theorem basis_sum (D : ℕ) (P : ℂ[X]) (hP : P.natDegree ≤ D) :
    ∑ k ∈ Finset.range (D + 1), (trL 1 (-1) D P).coeff k = P.coeff D := by
  conv_rhs => rw [basis_decomp D P hP]
  rw [finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k ≤ D := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  rw [coeff_smul, smul_eq_mul, coeff_X_pow_mul', if_pos hk', coeff_X_sub_one_pow_top, mul_one]

/-- The coefficients in terms of the Taylor coefficients at `1`. -/
theorem basis_coeff_at_one (D : ℕ) (P : ℂ[X]) (hP : P.natDegree ≤ D) (k : ℕ) (hk : k ≤ D) :
    (trL 1 (-1) D P).coeff k =
      (-1) ^ k * (trL (-1) (-1) D (P.comp (X + 1))).coeff (D - k) := by
  set b := fun k => (trL 1 (-1) D P).coeff k with hb
  set R := P.comp (X + 1) with hR
  -- `R` in the basis `X^k' (-X-1)^(D-k')`
  set E : ℂ[X] := ∑ k' ∈ Finset.range (D + 1), ((-1) ^ (D - k') * b (D - k')) • (X ^ k' : ℂ[X])
    with hE
  have hEdeg : E.natDegree ≤ D := by
    rw [hE]
    apply natDegree_sum_le_of_forall_le
    intro k' hk'
    refine (natDegree_smul_le _ _).trans ?_
    rw [natDegree_X_pow]
    exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hk')
  have hRE : trL (-1) (-1) D E = R := by
    rw [hE, map_sum]
    have h1 : ∀ k' ∈ Finset.range (D + 1), trL (-1) (-1) D (((-1) ^ (D - k') * b (D - k')) •
        (X ^ k' : ℂ[X])) = b (D - k') • (X ^ k' * (X + 1) ^ (D - k')) := by
      intro k' hk'
      have hk'' : k' ≤ D := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk')
      rw [map_smul, trL_X_pow _ _ D k' hk'']
      have : (C (-1 : ℂ) * X + C (-1) : ℂ[X]) = C (-1) * (X + 1) := by simp; ring
      rw [this, mul_pow, ← C_pow, smul_eq_C_mul, smul_eq_C_mul, map_mul]
      have hsq : C ((-1 : ℂ) ^ (D - k')) * C ((-1) ^ (D - k')) = (1 : ℂ[X]) := by
        rw [← map_mul, ← mul_pow]; simp
      calc C ((-1 : ℂ) ^ (D - k')) * C (b (D - k')) * (X ^ k' * (C ((-1) ^ (D - k')) * (X + 1) ^ (D - k')))
          = (C ((-1 : ℂ) ^ (D - k')) * C ((-1) ^ (D - k'))) * C (b (D - k')) *
              (X ^ k' * (X + 1) ^ (D - k')) := by ring
        _ = C (b (D - k')) * (X ^ k' * (X + 1) ^ (D - k')) := by rw [hsq, one_mul]
    rw [Finset.sum_congr rfl h1]
    -- reflect the sum and compare with `R`
    have hRsum : R = ∑ k ∈ Finset.range (D + 1), b k • ((X + 1) ^ k * X ^ (D - k) : ℂ[X]) := by
      rw [hR]
      conv_lhs => rw [basis_decomp D P hP]
      rw [← Polynomial.coe_compRingHom_apply, map_sum]
      apply Finset.sum_congr rfl
      intro k _
      rw [Polynomial.coe_compRingHom_apply, smul_comp, mul_comp, pow_comp, pow_comp, X_comp,
        sub_comp, one_comp, X_comp]
      congr 1
      ring
    rw [hRsum, ← Finset.sum_range_reflect]
    apply Finset.sum_congr rfl
    intro k hk
    have hk' : k < D + 1 := Finset.mem_range.mp hk
    rw [show D + 1 - 1 - k = D - k by omega, show D - (D - k) = k by omega]
    ring_nf
  have hEval := trL_trL (-1) (-1) (by ring) (by ring) D E hEdeg
  rw [hRE] at hEval
  rw [hEval, hE, finsetSum_coeff]
  rw [Finset.sum_eq_single (D - k)]
  · rw [coeff_smul, coeff_X_pow, if_pos rfl, smul_eq_mul, mul_one,
      show D - (D - k) = k by omega, ← mul_assoc, ← pow_add]
    simp [Even.neg_one_pow ⟨k, rfl⟩, hb]
  · intro j _ hj
    rw [coeff_smul, coeff_X_pow, if_neg (Ne.symm hj), smul_zero]
  · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h

end OM.NNN30.Crossing
