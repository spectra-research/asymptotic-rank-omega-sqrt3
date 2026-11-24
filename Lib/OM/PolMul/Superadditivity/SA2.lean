/- Adapted from PolMul/Superadditivity/SA2.lean of an earlier formalisation
   (commit 51c6e6b6e8b8d7226c6a828dba618ae1de5b5f8a).
   Amanov, van den Berg and Zuiddam (2026),
   “Multiplying matrices via polynomials: exposition and barriers”.
   Uses Foundations tensor definitions; declarations are renamed under OM. -/
import Lib.OM.PolMul.Superadditivity.Words
import Lib.OM.PolMul.Superadditivity.Rate
import Lib.OM.PolMulStatements.SA_2
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-! # Superadditivity by word types

Instead of introducing factorials, we sum over words and partition that sum
by the multiplicity vector. This is the multinomial expansion with its
coefficients represented by the cardinalities of their word fibers.
-/

namespace OM.PolMul.Superadditivity

open AsymptoticSpectrumDuality Semicontinuity
open scoped BigOperators

universe u
variable {F : Type u} [Field F]

/-- The multiplicity vector of a word. Each count lies between zero and k. -/
noncomputable def wordType {k m : ℕ} (w : Fin k → Fin m) : Fin m → Fin (k + 1) := by
  classical
  exact fun i => ⟨Fintype.card {j // w j = i}, Nat.lt_succ_of_le (by
    simpa using! Fintype.card_subtype_le (fun j => w j = i))⟩

lemma wordType_counts {k m : ℕ} {a b : Fin k → Fin m} (h : wordType a = wordType b)
    (i : Fin m) : Fintype.card {j // a j = i} = Fintype.card {j // b j = i} :=
  congrArg (fun v => (v i).val) h

-- The type-fiber enumeration introduces several dependent tensor formats.
set_option maxHeartbeats 400000 in
/-- SA.1 and the word projection bound the entire contribution of each type. -/
lemma wordType_bound (φ : Spectral F)
    (hp : 0 < Real.logb 2 (Spectral.eval φ (matMul (F := F) 1 1 2)))
    (m : ℕ+) (d : Fin m → Fin 3 → ℕ+) (n : ℕ+) (h : ∀ i, d i 0 = n)
    (T : ∀ i, T3 F (d i)) (k : ℕ) (κ : Fin m → Fin (k + 1)) :
    (∑ w : {w : Fin k → Fin m // wordType w = κ},
      Spectral.eval φ (wordTensor d n h T w.val) ^
        (Real.logb 2 (Spectral.eval φ (matMul (F := F) 1 1 2)))⁻¹) ≤
      (2 : ℝ) ^ (Real.logb 2 (Spectral.eval φ (matMul (F := F) 1 1 2)))⁻¹ *
        (Spectral.eval φ (pdsumFamily d n h T) ^
          (Real.logb 2 (Spectral.eval φ (matMul (F := F) 1 1 2)))⁻¹) ^ k := by
  classical
  let p := Real.logb 2 (Spectral.eval φ (matMul (F := F) 1 1 2))
  let J := {w : Fin k → Fin m // wordType w = κ}
  by_cases hn : Nonempty J
  · letI := hn
    let r : ℕ+ := ⟨Fintype.card J, Fintype.card_pos⟩
    let e : Fin r ≃ J := (Fintype.equivFin J).symm
    let w : Fin r → Fin k → Fin m := fun b => (e b).val
    have hw : Function.Injective w := Subtype.val_injective.comp e.injective
    have hi : ∀ b, Iso (wordTensor d n h T (w b)) (wordTensor d n h T (w 0)) := by
      intro b
      apply wordTensor_iso
      apply wordType_counts
      exact (e b).property.trans (e 0).property.symm
    have hsa := proof_SA_1 F φ hp r (fun b => wordDims d n (w b))
      (∏ _ : Fin k, n) (fun _ => rfl) (fun b => wordTensor d n h T (w b)) hi
    have hr := eval_restricts φ (words_restricts d n h T r w hw)
    rw [eval_productTensor] at hr
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hr
    have H : (1 / 2 : ℝ) * ((r : ℕ) : ℝ) ^ p *
        Spectral.eval φ (wordTensor d n h T (w 0)) ≤
        Spectral.eval φ (pdsumFamily d n h T) ^ k := hsa.trans hr
    have H' : ((r : ℕ) : ℝ) ^ p * Spectral.eval φ (wordTensor d n h T (w 0)) ≤
        2 * Spectral.eval φ (pdsumFamily d n h T) ^ k := by linarith
    have Hroot := Real.rpow_le_rpow (mul_nonneg (Real.rpow_nonneg (by positivity) _)
      (eval_nonneg φ _)) H' (inv_nonneg.mpr hp.le)
    rw [Real.mul_rpow (Real.rpow_nonneg (by positivity) _) (eval_nonneg φ _),
      Real.rpow_rpow_inv (by positivity) hp.ne',
      Real.mul_rpow (by norm_num) (pow_nonneg (eval_nonneg φ _) k),
      ← Real.rpow_pow_comm (eval_nonneg φ _)] at Hroot
    change (∑ a : J, Spectral.eval φ (wordTensor d n h T a.val) ^ p⁻¹) ≤ _
    rw [← e.sum_comp (fun a : J => Spectral.eval φ (wordTensor d n h T a.val) ^ p⁻¹)]
    calc
      (∑ b : Fin r, Spectral.eval φ (wordTensor d n h T (e b).val) ^ p⁻¹) =
          ∑ _b : Fin r, Spectral.eval φ (wordTensor d n h T (w 0)) ^ p⁻¹ := by
        apply Finset.sum_congr rfl
        intro b _
        rw [eval_iso φ (hi b)]
      _ = ((r : ℕ) : ℝ) * Spectral.eval φ (wordTensor d n h T (w 0)) ^ p⁻¹ := by simp
      _ ≤ _ := Hroot
  · haveI : IsEmpty J := not_nonempty_iff.mp hn
    change (∑ a : J, _) ≤ _
    rw [Fintype.sum_empty]
    exact mul_nonneg (Real.rpow_nonneg (by norm_num) _)
      (pow_nonneg (Real.rpow_nonneg (eval_nonneg φ _) _) _)

-- Partitioning the full word sum is the finite multinomial expansion.
set_option maxHeartbeats 300000 in
/-- Superadditivity on partial direct sums. -/
theorem proof_SA_2 : OM_S_SA_2 := by
  intro F _ φ hp m d n h T
  change 0 < Real.logb 2 (Spectral.eval φ (matMul (F := F) 1 1 2)) at hp
  change (∑ i : Fin m, Spectral.eval φ (T i) ^
      (1 / Real.logb 2 (Spectral.eval φ (matMul (F := F) 1 1 2)))) ≤ _
  simp only [one_div]
  let p := Real.logb 2 (Spectral.eval φ (matMul (F := F) 1 1 2))
  let a : Fin m → ℝ := fun i => Spectral.eval φ (T i) ^ p⁻¹
  let B := Spectral.eval φ (pdsumFamily d n h T) ^ p⁻¹
  change (∑ i, a i) ≤ B
  apply le_of_power_le_polynomial
    (Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (eval_nonneg φ _) _))
    (Real.rpow_nonneg (eval_nonneg φ _) _) (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) p⁻¹) m
  intro k _hk
  have hsum : (∑ i, a i) ^ k =
      ∑ w : Fin k → Fin m, Spectral.eval φ (wordTensor d n h T w) ^ p⁻¹ := by
    rw [show (∑ i, a i) ^ k = ∏ _j : Fin k, ∑ i, a i by simp, Fintype.prod_sum]
    apply Finset.sum_congr rfl
    intro w _
    rw [eval_wordTensor]
    exact Real.finset_prod_rpow Finset.univ (fun j => Spectral.eval φ (T (w j)))
      (fun j _ => eval_nonneg φ _) p⁻¹
  rw [hsum, ← Fintype.sum_fiberwise wordType]
  calc
    (∑ κ : Fin m → Fin (k + 1),
        ∑ w : {w : Fin k → Fin m // wordType w = κ},
          Spectral.eval φ (wordTensor d n h T w.val) ^ p⁻¹) ≤
        ∑ _κ : Fin m → Fin (k + 1), (2 : ℝ) ^ p⁻¹ * B ^ k := by
      apply Finset.sum_le_sum
      intro κ _
      exact wordType_bound φ hp m d n h T k κ
    _ = (2 : ℝ) ^ p⁻¹ * ((k + 1 : ℕ) : ℝ) ^ (m : ℕ) * B ^ k := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun,
        Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow]
      ring

end OM.PolMul.Superadditivity

