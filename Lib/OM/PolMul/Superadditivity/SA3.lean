/- Adapted from PolMul/Superadditivity/SA3.lean of an earlier formalisation
   (commit 51c6e6b6e8b8d7226c6a828dba618ae1de5b5f8a).
   Amanov, van den Berg and Zuiddam (2026),
   “Multiplying matrices via polynomials: exposition and barriers”.
   Uses Foundations tensor definitions; declarations are renamed under OM. -/
import Lib.OM.PolMul.Superadditivity.Strassen
import Lib.OM.PolMul.Superadditivity.Permutations
import Lib.OM.PolMulStatements.SA_3

/-! # The laser separation bound -/

namespace OM.PolMul.Superadditivity

open AsymptoticSpectrumDuality Semicontinuity
open scoped BigOperators

universe u
variable {F : Type u} [Field F]

lemma eval_rotate_matMul (φ : Spectral F) (a b c : ℕ+) :
    Spectral.eval φ (perm (finRotate 3) (matMul (F := F) a b c)) =
      Spectral.eval φ (matMul (F := F) c a b) :=
  eval_iso φ (RestrictionFacts.proof_RF_5 F a b c).1

lemma eval_rotate_inv_matMul (φ : Spectral F) (a b c : ℕ+) :
    Spectral.eval φ (perm (finRotate 3)⁻¹ (matMul (F := F) a b c)) =
      Spectral.eval φ (matMul (F := F) b c a) :=
  eval_iso φ (RestrictionFacts.proof_RF_5 F a b c).2.1

lemma eval_matMul_n11 (φ : Spectral F) (q : ℕ+) :
    Spectral.eval φ (matMul (F := F) q 1 1) =
      ((q : ℕ) : ℝ) ^ Real.logb 2 (Spectral.eval φ (matMul (F := F) 2 1 1)) := by
  have H := eval_matMul_11 (Spectral.perm (finRotate 3) φ) q
  rw [eval_perm, eval_perm, eval_rotate_matMul φ 1 1 q,
    eval_rotate_matMul φ 1 1 2] at H
  exact H

lemma eval_matMul_1n1 (φ : Spectral F) (q : ℕ+) :
    Spectral.eval φ (matMul (F := F) 1 q 1) =
      ((q : ℕ) : ℝ) ^ Real.logb 2 (Spectral.eval φ (matMul (F := F) 1 2 1)) := by
  have H := eval_matMul_11 (Spectral.perm (finRotate 3)⁻¹ φ) q
  rw [eval_perm, eval_perm, eval_rotate_inv_matMul φ 1 1 q,
    eval_rotate_inv_matMul φ 1 1 2] at H
  exact H

/-- AM-GM for the two positive real powers appearing in the proof. -/
lemma power_amgm {q a b p : ℝ} (hq : 0 < q) (hp : 0 < p) :
    2 * q ^ ((a + b) / (2 * p)) ≤ q ^ (a / p) + q ^ (b / p) := by
  have hx : (q ^ (a / (2 * p))) ^ 2 = q ^ (a / p) := by
    rw [← Real.rpow_mul_natCast hq.le]
    congr 1
    norm_num only [Nat.cast_ofNat]
    field_simp
  have hy : (q ^ (b / (2 * p))) ^ 2 = q ^ (b / p) := by
    rw [← Real.rpow_mul_natCast hq.le]
    congr 1
    norm_num only [Nat.cast_ofNat]
    field_simp
  have hxy : q ^ (a / (2 * p)) * q ^ (b / (2 * p)) = q ^ ((a + b) / (2 * p)) := by
    rw [← Real.rpow_add hq]
    congr 1
    ring
  nlinarith [sq_nonneg (q ^ (a / (2 * p)) - q ^ (b / (2 * p)))]

-- Normalize the SA.2 bound and raise both sides to its positive exponent.
set_option maxHeartbeats 300000 in
lemma strassen_spectral_bound (φ : Spectral F) (q : ℕ+) :
    (2 : ℝ) ^ Real.logb 2 (Spectral.eval φ (matMul (F := F) 1 1 2)) *
      ((q : ℕ) : ℝ) ^ ((Real.logb 2 (Spectral.eval φ (matMul (F := F) 2 1 1)) +
        Real.logb 2 (Spectral.eval φ (matMul (F := F) 1 2 1))) / 2) ≤
      ((q : ℕ) : ℝ) + 1 := by
  let p := Real.logb 2 (Spectral.eval φ (matMul (F := F) 1 1 2))
  let a := Real.logb 2 (Spectral.eval φ (matMul (F := F) 2 1 1))
  let b := Real.logb 2 (Spectral.eval φ (matMul (F := F) 1 2 1))
  let Q : ℝ := ((q : ℕ) : ℝ)
  have hQ : 0 < Q := by dsimp [Q]; exact_mod_cast q.pos
  have hQ1 : 1 ≤ Q := by dsimp [Q]; exact_mod_cast (show 1 ≤ (q : ℕ) from q.pos)
  change 2 ^ p * Q ^ ((a + b) / 2) ≤ Q + 1
  by_cases hp : 0 < p
  · have H := superadd_binary φ hp (leftPair (F := F) q) (rightPair (F := F) q) rfl
    rw [eval_iso φ (leftPair_iso q), eval_iso φ (rightPair_iso q),
      eval_matMul_n11, eval_matMul_1n1] at H
    have Hu := Real.rpow_le_rpow (eval_nonneg φ _) (eval_strassenTensor_le φ q)
      (inv_nonneg.mpr hp.le)
    have H' : (Q ^ a) ^ p⁻¹ + (Q ^ b) ^ p⁻¹ ≤ (Q + 1) ^ p⁻¹ := H.trans Hu
    rw [← Real.rpow_mul hQ.le, ← Real.rpow_mul hQ.le] at H'
    have Hmean := (power_amgm (a := a) (b := b) hQ hp).trans (by
      simpa only [div_eq_mul_inv] using! H')
    have Hpow := Real.rpow_le_rpow (mul_nonneg (by norm_num) (Real.rpow_nonneg hQ.le _)) Hmean hp.le
    rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hQ.le _),
      ← Real.rpow_mul hQ.le, Real.rpow_inv_rpow (by linarith) hp.ne'] at Hpow
    have he : ((a + b) / (2 * p)) * p = (a + b) / 2 := by field_simp
    rwa [he] at Hpow
  · have hp0 : p = 0 := le_antisymm (le_of_not_gt hp) (spectral_exponent_nonneg φ)
    have ha : a ≤ 1 := by
      have H := (SpectralFacts.proof_SP_5 F φ).2.1
      have Hlog := (Real.logb_le_logb (b := 2) (by norm_num)
        (lt_of_lt_of_le zero_lt_one H.1) (by norm_num)).mpr H.2
      simpa [a] using! Hlog
    have hb : b ≤ 1 := by
      have H := (SpectralFacts.proof_SP_5 F φ).2.2.1
      have Hlog := (Real.logb_le_logb (b := 2) (by norm_num)
        (lt_of_lt_of_le zero_lt_one H.1) (by norm_num)).mpr H.2
      simpa [b] using! Hlog
    rw [hp0, Real.rpow_zero, one_mul]
    calc
      Q ^ ((a + b) / 2) ≤ Q ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith)
      _ ≤ Q + 1 := by rw [Real.rpow_one]; linarith

-- Three cyclic instances give the symmetric bound on the sum of exponents.
set_option maxHeartbeats 400000 in
lemma laser_spectral_bound (φ : Spectral F) (q : ℕ+) :
    (2 * ((q : ℕ) : ℝ)) ^
      (Real.logb 2 (Spectral.eval φ (matMul (F := F) 1 1 2)) +
       Real.logb 2 (Spectral.eval φ (matMul (F := F) 2 1 1)) +
       Real.logb 2 (Spectral.eval φ (matMul (F := F) 1 2 1))) ≤
      (((q : ℕ) : ℝ) + 1) ^ (3 : ℕ) := by
  have H₀ := strassen_spectral_bound φ q
  have H₁ := strassen_spectral_bound (Spectral.perm (finRotate 3) φ) q
  have H₂ := strassen_spectral_bound (Spectral.perm (finRotate 3)⁻¹ φ) q
  simp only [eval_perm] at H₁ H₂
  rw [eval_rotate_matMul φ 1 1 2,
    eval_rotate_matMul φ 2 1 1,
    eval_rotate_matMul φ 1 2 1] at H₁
  rw [eval_rotate_inv_matMul φ 1 1 2,
    eval_rotate_inv_matMul φ 2 1 1,
    eval_rotate_inv_matMul φ 1 2 1] at H₂
  let p := Real.logb 2 (Spectral.eval φ (matMul (F := F) 1 1 2))
  let a := Real.logb 2 (Spectral.eval φ (matMul (F := F) 2 1 1))
  let b := Real.logb 2 (Spectral.eval φ (matMul (F := F) 1 2 1))
  let Q : ℝ := ((q : ℕ) : ℝ)
  have hQ : 0 < Q := by dsimp [Q]; exact_mod_cast q.pos
  change (2 * Q) ^ (p + a + b) ≤ (Q + 1) ^ (3 : ℕ)
  change 2 ^ p * Q ^ ((a + b) / 2) ≤ Q + 1 at H₀
  change 2 ^ a * Q ^ ((b + p) / 2) ≤ Q + 1 at H₁
  change 2 ^ b * Q ^ ((p + a) / 2) ≤ Q + 1 at H₂
  have HH := mul_le_mul (mul_le_mul H₀ H₁ (by positivity) (by positivity)) H₂
    (by positivity) (by positivity)
  have he : (2 ^ p * Q ^ ((a + b) / 2)) * (2 ^ a * Q ^ ((b + p) / 2)) *
      (2 ^ b * Q ^ ((p + a) / 2)) = (2 * Q) ^ (p + a + b) := by
    calc
      _ = (2 ^ p * 2 ^ a * 2 ^ b) *
          (Q ^ ((a + b) / 2) * Q ^ ((b + p) / 2) * Q ^ ((p + a) / 2)) := by ring
      _ = _ := by
        rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
          ← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
          ← Real.rpow_add hQ, ← Real.rpow_add hQ, Real.mul_rpow (by norm_num) hQ.le]
        congr 2
        ring
  rw [he] at HH
  simpa [pow_succ, pow_two] using! HH

/-- The laser bound for separated summands. -/
theorem proof_SA_3 : OM_S_SA_3 := by
  intro F _ q hq
  obtain ⟨φ, hφ⟩ := (SpectralFacts.proof_SP_1 F).1
  let q' : ℕ+ := ⟨q, hq⟩
  have H := laser_spectral_bound φ q'
  have hval := (SpectralFacts.proof_SP_5 F φ).2.2.2 2 2 2
  change Spectral.eval φ (matMul (F := F) 2 2 2) = _ at hval
  simp only [PNat.val_ofNat, Nat.cast_ofNat, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), Real.rpow_one] at hval
  change Spectral.eval φ (matMul (F := F) 2 2 2) =
    Spectral.eval φ (matMul (F := F) 2 1 1) * Spectral.eval φ (matMul (F := F) 1 2 1) *
    Spectral.eval φ (matMul (F := F) 1 1 2) at hval
  have hA := (SpectralFacts.proof_SP_5 F φ).1.1
  have hB := (SpectralFacts.proof_SP_5 F φ).2.1.1
  have hC := (SpectralFacts.proof_SP_5 F φ).2.2.1.1
  have ha : 0 < Spectral.eval φ (matMul (F := F) 1 1 2) := lt_of_lt_of_le zero_lt_one hA
  have hb : 0 < Spectral.eval φ (matMul (F := F) 2 1 1) := lt_of_lt_of_le zero_lt_one hB
  have hc : 0 < Spectral.eval φ (matMul (F := F) 1 2 1) := lt_of_lt_of_le zero_lt_one hC
  have he : omegaF F = Real.logb 2 (Spectral.eval φ (matMul (F := F) 1 1 2)) +
      Real.logb 2 (Spectral.eval φ (matMul (F := F) 2 1 1)) +
      Real.logb 2 (Spectral.eval φ (matMul (F := F) 1 2 1)) := by
    change omegaF F = Real.logb 2 (Spectral.eval φ (matMul (F := F) 2 2 2)) at hφ
    rw [hφ, hval, Real.logb_mul (mul_pos hb hc).ne' ha.ne',
      Real.logb_mul hb.ne' hc.ne']
    ring
  change (((2 * q : ℕ) : ℝ) ^ omegaF F) ≤ (((q + 1 : ℕ) : ℝ) ^ (3 : ℝ))
  rw [he]
  simpa [q', Nat.cast_mul, Nat.cast_add, Real.rpow_natCast] using! H

end OM.PolMul.Superadditivity

