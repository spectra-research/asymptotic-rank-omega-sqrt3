/- Adapted from PolMul/Superadditivity/SA4.lean of an earlier formalisation
   (commit 51c6e6b6e8b8d7226c6a828dba618ae1de5b5f8a).
   Amanov, van den Berg and Zuiddam (2026),
   “Multiplying matrices via polynomials: exposition and barriers”.
   Uses Foundations tensor definitions; declarations are renamed under OM. -/
import Lib.OM.PolMul.Superadditivity.Permutations
import Lib.OM.PolMulStatements.SA_4

/-! # Symmetrised shared-leg sums -/

namespace OM.PolMul.Superadditivity

open AsymptoticSpectrumDuality Semicontinuity
open scoped BigOperators

universe u
variable {F : Type u} [Field F]

/-- The elementary product inequality used for a pair of swapped spectra. -/
lemma paired_power_bound {s t x y U V p : ℝ}
    (hs : 0 ≤ s) (ht : 0 ≤ t) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hU : 0 ≤ U) (hV : 0 ≤ V) (hp : 0 < p)
    (h₁ : s * x ^ p⁻¹ + t * y ^ p⁻¹ ≤ U ^ p⁻¹)
    (h₂ : s * y ^ p⁻¹ + t * x ^ p⁻¹ ≤ V ^ p⁻¹) :
    x * (s + t) ^ p * (y * (s + t) ^ p) ≤ U * V := by
  have ha := Real.rpow_nonneg hx p⁻¹
  have hb := Real.rpow_nonneg hy p⁻¹
  have hm := mul_le_mul h₁ h₂ (add_nonneg (mul_nonneg hs hb) (mul_nonneg ht ha))
    (Real.rpow_nonneg hU p⁻¹)
  have hsq := mul_nonneg (mul_nonneg hs ht) (sq_nonneg (x ^ p⁻¹ - y ^ p⁻¹))
  have H : (s + t) ^ 2 * (x ^ p⁻¹ * y ^ p⁻¹) ≤ U ^ p⁻¹ * V ^ p⁻¹ := by
    nlinarith
  have HH := Real.rpow_le_rpow (mul_nonneg (sq_nonneg _) (mul_nonneg ha hb)) H hp.le
  rw [Real.mul_rpow (sq_nonneg _) (mul_nonneg ha hb),
    ← Real.rpow_pow_comm (add_nonneg hs ht), Real.mul_rpow ha hb,
    Real.rpow_inv_rpow hx hp.ne', Real.rpow_inv_rpow hy hp.ne',
    Real.mul_rpow (Real.rpow_nonneg hU _) (Real.rpow_nonneg hV _),
    Real.rpow_inv_rpow hU hp.ne', Real.rpow_inv_rpow hV hp.ne'] at HH
  nlinarith

noncomputable def mixedSum {d : Fin 3 → ℕ+} (S : T3 F d) (s t : ℕ+) :=
  pdsum (kron S (matMul (F := F) 1 1 s))
    (kron (swap23 S) (matMul (F := F) 1 1 t)) (by
      change d 0 * 1 = d ((Equiv.swap 1 2).symm 0) * 1
      rw [Equiv.symm_swap, Equiv.swap_apply_of_ne_of_ne (by decide +kernel) (by decide +kernel)])

-- Normalize the four spectral values before applying the real inequality.
set_option maxHeartbeats 400000 in
lemma mixedSum_pair_bound (φ : Spectral F) {d : Fin 3 → ℕ+}
    (S : T3 F d) (s t : ℕ+) :
    Spectral.eval φ (kron S (matMul (F := F) 1 1 (s + t))) *
      Spectral.eval (Spectral.perm (Equiv.swap 1 2) φ)
        (kron S (matMul (F := F) 1 1 (s + t))) ≤
    Spectral.eval φ (mixedSum S s t) *
      Spectral.eval (Spectral.perm (Equiv.swap 1 2) φ) (mixedSum S s t) := by
  let ψ := Spectral.perm (Equiv.swap 1 2) φ
  let p := Real.logb 2 (Spectral.eval φ (matMul (F := F) 1 1 2))
  let x := Spectral.eval φ S
  let y := Spectral.eval ψ S
  have hpψ : Real.logb 2 (Spectral.eval ψ (matMul (F := F) 1 1 2)) = p := by
    rw [eval_swap_matMul_11]
  have hq (q : ℕ+) : Spectral.eval ψ (matMul (F := F) 1 1 q) = ((q : ℕ) : ℝ) ^ p := by
    rw [eval_swap_matMul_11, eval_matMul_11]
  have hsφ : Spectral.eval φ (swap23 S) = y := (eval_perm φ (Equiv.swap 1 2) S).symm
  have hsψ : Spectral.eval ψ (swap23 S) = x := eval_swap_swap φ S
  have hx := eval_nonneg φ S
  have hy := eval_nonneg ψ S
  have hU := eval_nonneg φ (mixedSum S s t)
  have hV := eval_nonneg ψ (mixedSum S s t)
  rw [eval_kron, eval_kron, eval_matMul_11, hq]
  change x * ((((s + t : ℕ+) : ℕ) : ℝ) ^ p) *
    (y * ((((s + t : ℕ+) : ℕ) : ℝ) ^ p)) ≤ _
  rw [PNat.add_coe, Nat.cast_add]
  by_cases hp : 0 < p
  · have h₁ := superadd_binary φ hp (kron S (matMul (F := F) 1 1 s))
      (kron (swap23 S) (matMul (F := F) 1 1 t)) (by
        change d 0 * 1 = d ((Equiv.swap 1 2).symm 0) * 1
        rw [Equiv.symm_swap, Equiv.swap_apply_of_ne_of_ne (by decide +kernel) (by decide +kernel)])
    have h₂ := superadd_binary ψ (by rw [hpψ]; exact hp)
      (kron S (matMul (F := F) 1 1 s))
      (kron (swap23 S) (matMul (F := F) 1 1 t)) (by
        change d 0 * 1 = d ((Equiv.swap 1 2).symm 0) * 1
        rw [Equiv.symm_swap, Equiv.swap_apply_of_ne_of_ne (by decide +kernel) (by decide +kernel)])
    rw [eval_kron, eval_kron, eval_matMul_11 φ s, eval_matMul_11 φ t, hsφ] at h₁
    rw [hpψ, eval_kron, eval_kron, hq s, hq t, hsψ] at h₂
    change (x * ((s : ℕ) : ℝ) ^ p) ^ p⁻¹ + (y * ((t : ℕ) : ℝ) ^ p) ^ p⁻¹ ≤ _ at h₁
    change (y * ((s : ℕ) : ℝ) ^ p) ^ p⁻¹ + (x * ((t : ℕ) : ℝ) ^ p) ^ p⁻¹ ≤ _ at h₂
    rw [Real.mul_rpow hx (Real.rpow_nonneg (by positivity) _),
      Real.mul_rpow hy (Real.rpow_nonneg (by positivity) _),
      Real.rpow_rpow_inv (by positivity) hp.ne', Real.rpow_rpow_inv (by positivity) hp.ne'] at h₁
    rw [Real.mul_rpow hy (Real.rpow_nonneg (by positivity) _),
      Real.mul_rpow hx (Real.rpow_nonneg (by positivity) _),
      Real.rpow_rpow_inv (by positivity) hp.ne', Real.rpow_rpow_inv (by positivity) hp.ne'] at h₂
    apply paired_power_bound (by positivity) (by positivity) hx hy hU hV hp
    · simpa only [mul_comm] using! h₁
    · simpa only [mul_comm] using! h₂
  · have hp0 : p = 0 := le_antisymm (le_of_not_gt hp) (spectral_exponent_nonneg φ)
    simp only [hp0, Real.rpow_zero, mul_one]
    have hr := left_restricts_pdsum (kron S (matMul (F := F) 1 1 s))
      (kron (swap23 S) (matMul (F := F) 1 1 t)) (by
        change d 0 * 1 = d ((Equiv.swap 1 2).symm 0) * 1
        rw [Equiv.symm_swap, Equiv.swap_apply_of_ne_of_ne (by decide +kernel) (by decide +kernel)])
    have h₁ := eval_restricts φ hr
    have h₂ := eval_restricts ψ hr
    rw [eval_kron, eval_matMul_11] at h₁
    rw [eval_kron, hq] at h₂
    change x * ((s : ℕ) : ℝ) ^ p ≤ _ at h₁
    simp only [hp0, Real.rpow_zero, mul_one] at h₁ h₂
    exact mul_le_mul h₁ h₂ hy hU

-- Taking the product over all six permutations pairs each one with its swap.
set_option maxHeartbeats 300000 in
/-- The bound for symmetrised shared-leg sums. -/
theorem proof_SA_4 : OM_S_SA_4 := by
  intro F _ d S s t
  change AsympRestricts (symm (kron S (matMul (F := F) 1 1 (s + t))))
    (symm (mixedSum S s t))
  apply (StrassenPreorder.asympRel_iff_forall_spectrum
    (tensorStrassenPreorder (F := F) (k := 3) (by norm_num)) _ _).mpr
  intro φ
  change Spectral.eval φ (symm (kron S (matMul (F := F) 1 1 (s + t)))) ≤
    Spectral.eval φ (symm (mixedSum S s t))
  rw [eval_symm, eval_symm]
  let A := kron S (matMul (F := F) 1 1 (s + t))
  let B := mixedSum S s t
  let τ : Equiv.Perm (Fin 3) := Equiv.swap 1 2
  have hp (π : Equiv.Perm (Fin 3)) :
      Spectral.eval (Spectral.perm π φ) A * Spectral.eval (Spectral.perm (π * τ) φ) A ≤
      Spectral.eval (Spectral.perm π φ) B * Spectral.eval (Spectral.perm (π * τ) φ) B := by
    simpa only [eval_perm_perm] using! mixedSum_pair_bound (Spectral.perm π φ) S s t
  have H := Finset.prod_le_prod₀ (s := Finset.univ)
    (fun π _ => mul_nonneg (eval_nonneg (Spectral.perm π φ) A)
      (eval_nonneg (Spectral.perm (π * τ) φ) A)) (fun π _ => hp π)
  have hright (f : Equiv.Perm (Fin 3) → ℝ) : (∏ π, f (π * τ)) = ∏ π, f π := by
    exact Equiv.prod_comp (Equiv.mulRight τ) f
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib,
    hright (fun π => Spectral.eval (Spectral.perm π φ) A),
    hright (fun π => Spectral.eval (Spectral.perm π φ) B)] at H
  have hA : 0 ≤ ∏ π : Equiv.Perm (Fin 3), Spectral.eval (Spectral.perm π φ) A :=
    Finset.prod_nonneg (fun π _ => eval_nonneg _ _)
  have hB : 0 ≤ ∏ π : Equiv.Perm (Fin 3), Spectral.eval (Spectral.perm π φ) B :=
    Finset.prod_nonneg (fun π _ => eval_nonneg _ _)
  nlinarith

end OM.PolMul.Superadditivity

