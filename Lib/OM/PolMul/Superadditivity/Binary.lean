/- Adapted from PolMul/Superadditivity/Binary.lean of an earlier formalisation
   (commit 51c6e6b6e8b8d7226c6a828dba618ae1de5b5f8a).
   Uses Foundations tensor definitions; declarations are renamed under OM. -/
import Lib.OM.PolMul.Superadditivity.SA2

/-! # Binary shared-leg sums and spectral evaluation -/

namespace OM.PolMul.Superadditivity

open AsymptoticSpectrumDuality Semicontinuity
open scoped BigOperators

universe u
variable {F : Type u} [Field F]

/-- Two tensors as a dependently typed two-element family. -/
def pairTensors {dA dB : Fin 3 → ℕ+} (A : T3 F dA) (B : T3 F dB) :
    ∀ i : Fin 2, T3 F (![dA, dB] i)
  | 0 => A
  | 1 => B

-- The four combinations of block labels determine the entrywise proof.
set_option maxHeartbeats 400000 in
/-- The family and binary shared-leg sums differ only by format casts. -/
lemma pairFamily_restricts {dA dB : Fin 3 → ℕ+} (A : T3 F dA) (B : T3 F dB)
    (h : dA 0 = dB 0) :
    Restricts
      (pdsumFamily ![dA, dB] (dA 0)
        (fun i => by fin_cases i; rfl; exact h.symm) (pairTensors A B))
      (pdsum A B h) := by
  classical
  let D := fmt (dA 0)
    ⟨∑ i : Fin 2, (![dA, dB] i 1 : ℕ), by simp⟩
    ⟨∑ i : Fin 2, (![dA, dB] i 2 : ℕ), by simp⟩
  let e : ∀ i, Fin (D i) → Fin (fmt (dA 0) (dA 1 + dB 1) (dA 2 + dB 2) i) :=
    fun i => Fin.cast (by fin_cases i <;> simp [D, fmt, Fin.sum_univ_two])
  apply restricts_of_coordinates e
  intro x
  obtain ⟨⟨b, v⟩, hv⟩ := (finSigmaFinEquiv (n := fun b : Fin 2 =>
    (![dA, dB] b 1 : ℕ))).surjective (x 1)
  obtain ⟨⟨c, z⟩, hz⟩ := (finSigmaFinEquiv (n := fun b : Fin 2 =>
    (![dA, dB] b 2 : ℕ))).surjective (x 2)
  have hx : x = (fun | 0 => x 0 | 1 => finSigmaFinEquiv ⟨b, v⟩ | 2 => finSigmaFinEquiv ⟨c, z⟩) := by
    funext i
    fin_cases i
    · rfl
    · exact hv.symm
    · exact hz.symm
  rw [hx]
  refine (pdsumFamily_blocks ![dA, dB] (dA 0)
    (fun i => by fin_cases i; rfl; exact h.symm) (pairTensors A B) (x 0) b c v z).trans ?_
  have hvlt := v.isLt
  have hzlt := z.isLt
  fin_cases b <;> fin_cases c <;>
    simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, Fin.reduceFinMk,
      Matrix.cons_val_zero, Matrix.cons_val_one] at hvlt hzlt ⊢ <;>
    simp [pdsum, e, finSigmaFinEquiv_apply, Fin.sum_univ_one,
      hvlt, hzlt, pairTensors, sharedTensor, Fin.ext_iff, h, Nat.not_lt.mpr (Nat.le_add_right _ _)] <;>
    rfl

/-- The usual binary form of SA.2. -/
lemma superadd_binary (φ : Spectral F)
    (hp : 0 < Real.logb 2 (Spectral.eval φ (matMul (F := F) 1 1 2)))
    {dA dB : Fin 3 → ℕ+} (A : T3 F dA) (B : T3 F dB) (h : dA 0 = dB 0) :
    Spectral.eval φ A ^ (Real.logb 2 (Spectral.eval φ (matMul (F := F) 1 1 2)))⁻¹ +
      Spectral.eval φ B ^ (Real.logb 2 (Spectral.eval φ (matMul (F := F) 1 1 2)))⁻¹ ≤
      Spectral.eval φ (pdsum A B h) ^
        (Real.logb 2 (Spectral.eval φ (matMul (F := F) 1 1 2)))⁻¹ := by
  have hsa := proof_SA_2 F φ hp 2 ![dA, dB] (dA 0)
    (fun i => by fin_cases i; rfl; exact h.symm) (pairTensors A B)
  change (∑ i : Fin 2, Spectral.eval φ (pairTensors A B i) ^
    (1 / Real.logb 2 (Spectral.eval φ (matMul (F := F) 1 1 2)))) ≤ _ at hsa
  simp only [Fin.sum_univ_two, pairTensors, one_div] at hsa
  exact hsa.trans (Real.rpow_le_rpow (eval_nonneg φ _)
    (eval_restricts φ (pairFamily_restricts A B h)) (inv_nonneg.mpr hp.le))

/-- Either binary summand is obtained by a coordinate projection. -/
lemma left_restricts_pdsum {dA dB : Fin 3 → ℕ+}
    (A : T3 F dA) (B : T3 F dB) (h : dA 0 = dB 0) : Restricts A (pdsum A B h) := by
  let e : ∀ i, Fin (dA i) → Fin (fmt (dA 0) (dA 1 + dB 1) (dA 2 + dB 2) i)
    | 0 => fun x => x
    | 1 => fun x => ⟨x.val, by simpa using! x.isLt.trans_le (Nat.le_add_right _ _)⟩
    | 2 => fun x => ⟨x.val, by simpa using! x.isLt.trans_le (Nat.le_add_right _ _)⟩
  apply restricts_of_coordinates e
  intro x
  simp only [pdsum, e, dif_pos (x 1).isLt, dif_pos (x 2).isLt]
  congr 1
  funext i
  fin_cases i <;> rfl

/-- Evaluation at `⟨1,1,q⟩` in the exponent convention used by SA.2. -/
lemma eval_matMul_11 (φ : Spectral F) (q : ℕ+) :
    Spectral.eval φ (matMul (F := F) 1 1 q) =
      ((q : ℕ) : ℝ) ^ Real.logb 2 (Spectral.eval φ (matMul (F := F) 1 1 2)) := by
  have h := (SpectralFacts.proof_SP_5 F φ).2.2.2 1 1 q
  change Spectral.eval φ (matMul (F := F) 1 1 q) = _ at h
  rw [h]
  simp only [PNat.val_ofNat, Nat.cast_one, Real.logb_one, Real.rpow_zero, one_mul]
  have hx := (SpectralFacts.proof_SP_5 F φ).1.1
  have hxpos : 0 < Spectral.eval φ (matMul (F := F) 1 1 2) := lt_of_lt_of_le zero_lt_one hx
  apply Real.log_injOn_pos (Real.rpow_pos_of_pos hxpos _)
    (Real.rpow_pos_of_pos (by exact_mod_cast q.pos) _)
  rw [Real.log_rpow hxpos, Real.log_rpow (by exact_mod_cast q.pos)]
  simp only [Real.logb]
  ring

lemma spectral_exponent_nonneg (φ : Spectral F) :
    0 ≤ Real.logb 2 (Spectral.eval φ (matMul (F := F) 1 1 2)) :=
  Real.logb_nonneg (by norm_num) (SpectralFacts.proof_SP_5 F φ).1.1

end OM.PolMul.Superadditivity

