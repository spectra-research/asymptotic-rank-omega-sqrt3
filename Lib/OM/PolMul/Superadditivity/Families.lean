/- Adapted from PolMul/Superadditivity/Families.lean of an earlier formalisation
   (commit 51c6e6b6e8b8d7226c6a828dba618ae1de5b5f8a).
   Amanov, van den Berg and Zuiddam (2026),
   “Multiplying matrices via polynomials: exposition and barriers”.
   Uses Foundations tensor definitions; declarations are renamed under OM. -/
import Lib.OM.PolMul.Superadditivity.Core

/-!
# Block-family lemmas for superadditivity

The project uses a single `Fin m`-indexed direct-sum tensor rather than a
binary fold.  The main lemma below gives the only comparison needed for SA.1:
if all blocks are isomorphic, their direct sum contains the tensor product of
one block with the size-`m` unit tensor.
-/

namespace OM.PolMul.Superadditivity

open AsymptoticSpectrumDuality
open Semicontinuity
open scoped BigOperators

universe u

variable {F : Type u} [Field F]

/-- A family direct sum of tensors isomorphic to `T 0` restricts from the
Kronecker product `⟨m⟩ ⊗ T 0`.  This is the block-diagonal basis-map
argument used in the proof of the isomorphic-summands lemma. -/
lemma unit_kron_restricts_dsumFamily (m : ℕ+) (d : Fin m → Fin 3 → ℕ+)
    (T : ∀ i, T3 F (d i)) (hiso : ∀ i, Iso (T i) (T 0)) :
    Restricts (kron (unit (F := F) m) (T 0)) (dsumFamily d T) := by
  classical
  have hr : ∀ i, Restricts (T 0) (T i) := fun i ↦
    (restrictsEquiv_of_iso (T := T i) (S := T 0) (hiso i)).2
  choose B hB using hr
  let D : Fin 3 → ℕ+ := fun j ↦
    ⟨∑ i : Fin m, (d i j : ℕ),
      Finset.sum_pos (fun i _ ↦ (d i j).pos) Finset.univ_nonempty⟩
  let block : ∀ j : Fin 3, Fin (D j) → (i : Fin m) × Fin (d i j) :=
    fun _ z ↦ finSigmaFinEquiv.symm z
  let mcast : ∀ j : Fin 3, Fin (fmt m m m j) ≃ Fin m := fun j ↦
    finCongr (by fin_cases j <;> rfl)
  let C : ∀ j : Fin 3, Matrix (Fin (fmt m m m j * d 0 j)) (Fin (D j)) F :=
    fun j x z ↦
      if h : (block j z).1 = mcast j (kronDecodeL x) then
        B (block j z).1 j (kronDecodeR x) (block j z).2
      else 0
  let emb (i : Fin m) (y : ∀ j : Fin 3, Fin (d i j)) :
      ∀ j : Fin 3, Fin (D j) := fun j ↦ finSigmaFinEquiv ⟨i, y j⟩
  have hblock_emb (i : Fin m) (y : ∀ j : Fin 3, Fin (d i j)) (j : Fin 3) :
      block j (emb i y j) = ⟨i, y j⟩ := by
    exact Equiv.symm_apply_apply _ _
  have hemb_inj (i : Fin m) : Function.Injective (emb i) := by
    intro y z hyz
    funext j
    apply Fin.ext
    have hj := congrArg Fin.val (congrFun hyz j)
    simp only [emb, finSigmaFinEquiv_apply] at hj
    omega
  have hdsum_emb (i : Fin m) (y : ∀ j : Fin 3, Fin (d i j)) :
      dsumFamily d T (emb i y) = T i y := by
    unfold dsumFamily
    let b : ∀ j : Fin 3, (a : Fin m) × Fin (d a j) :=
      fun j ↦ finSigmaFinEquiv.symm (emb i y j)
    have hb : b = fun j ↦ ⟨i, y j⟩ := by
      funext j
      exact Equiv.symm_apply_apply _ _
    change (if h : ∀ j, (b j).1 = (b 0).1 then
        T (b 0).1 (fun j ↦ Fin.cast (by rw [h j]) (b j).2) else 0) = T i y
    rw [hb]
    simp
  refine ⟨C, fun idx ↦ ?_⟩
  let ℓ : ∀ j : Fin 3, Fin m := fun j ↦ mcast j (kronDecodeL (idx j))
  let x : ∀ j : Fin 3, Fin (d 0 j) := fun j ↦ kronDecodeR (idx j)
  by_cases hall : ∀ j : Fin 3, ℓ j = ℓ 0
  · have hunit : unit (F := F) m (kronLeftIndex idx) = 1 := by
      simp only [unit]
      rw [if_pos]
      intro i j
      rw [← kronDecodeL_eq_kronLeftIndex idx i,
        ← kronDecodeL_eq_kronLeftIndex idx j]
      have hij := (hall i).trans (hall j).symm
      simpa [ℓ, mcast] using! congrArg Fin.val hij
    rw [show kron (unit (F := F) m) (T 0) idx = T 0 x by
      simp only [kron, kroneckerTensor, hunit, one_mul]
      congr 1]
    have hC_emb (y : ∀ j, Fin (d (ℓ 0) j)) (j : Fin 3) :
        C j (idx j) (emb (ℓ 0) y j) = B (ℓ 0) j (x j) (y j) := by
      simp only [C]
      rw [hblock_emb]
      rw [dif_pos (hall j).symm]
    rw [← Finset.sum_subset
      (Finset.subset_univ ((Finset.univ : Finset (∀ j, Fin (d (ℓ 0) j))).image
        (emb (ℓ 0))))]
    · rw [Finset.sum_image]
      · simp_rw [hdsum_emb, hC_emb]
        exact hB (ℓ 0) x
      · exact fun a _ b _ hab ↦ hemb_inj (ℓ 0) hab
    · intro z _ hz
      have hex : ∃ j : Fin 3, (block j (z j)).1 ≠ ℓ 0 := by
        by_contra hnone
        push_neg at hnone
        apply hz
        let y : ∀ j, Fin (d (ℓ 0) j) := fun j ↦
          Fin.cast (congrArg (fun i ↦ (d i j : ℕ)) (hnone j)) (block j (z j)).2
        refine Finset.mem_image.2 ⟨y, Finset.mem_univ _, ?_⟩
        funext j
        rw [← Equiv.apply_symm_apply finSigmaFinEquiv (z j)]
        apply congrArg finSigmaFinEquiv
        rcases hblk : block j (z j) with ⟨k, w⟩
        change ⟨ℓ 0, y j⟩ = block j (z j)
        rw [hblk]
        have hk := hnone j
        rw [hblk] at hk
        change k = ℓ 0 at hk
        subst k
        congr 1
        apply Fin.ext
        change (block j (z j)).2.val = w.val
        exact congrArg (fun s : (i : Fin m) × Fin (d i j) ↦ s.2.val) hblk
      obtain ⟨j, hlabel⟩ := hex
      have hCzero : C j (idx j) (z j) = 0 := by
        simp [C, ℓ, hlabel, hall j]
      rw [show (∏ k : Fin 3, C k (idx k) (z k)) = 0 from
        Finset.prod_eq_zero (Finset.mem_univ j) hCzero, zero_mul]
  · have hunit : unit (F := F) m (kronLeftIndex idx) = 0 := by
      simp only [unit]
      rw [if_neg]
      intro heq
      apply hall
      intro j
      apply Fin.ext
      change (kronDecodeL (idx j)).val = (kronDecodeL (idx 0)).val
      rw [kronDecodeL_eq_kronLeftIndex, kronDecodeL_eq_kronLeftIndex]
      exact heq j 0
    rw [show kron (unit (F := F) m) (T 0) idx = 0 by
      simp [kron, kroneckerTensor, hunit]]
    symm
    apply Finset.sum_eq_zero
    intro z _
    unfold dsumFamily
    simp only
    by_cases hdiag : ∀ j : Fin 3,
        (finSigmaFinEquiv.symm (z j)).1 = (finSigmaFinEquiv.symm (z 0)).1
    · rw [dif_pos hdiag]
      have hex : ∃ j : Fin 3, ℓ j ≠ (block 0 (z 0)).1 := by
        by_contra hnone
        push_neg at hnone
        apply hall
        intro j
        exact (hnone j).trans (hnone 0).symm
      obtain ⟨j, hj⟩ := hex
      have hCzero : C j (idx j) (z j) = 0 := by
        simp only [C]
        rw [dif_neg]
        intro heq
        apply hj
        exact heq.symm.trans (by simpa [block] using! hdiag j)
      rw [show (∏ k : Fin 3, C k (idx k) (z k)) = 0 from
        Finset.prod_eq_zero (Finset.mem_univ j) hCzero, zero_mul]
    · rw [dif_neg hdiag, mul_zero]

/-- Spectral consequence of `unit_kron_restricts_dsumFamily`. -/
lemma card_mul_eval_le_eval_dsumFamily (φ : Spectral F) (m : ℕ+)
    (d : Fin m → Fin 3 → ℕ+) (T : ∀ i, T3 F (d i))
    (hiso : ∀ i, Iso (T i) (T 0)) :
    ((m : ℕ) : ℝ) * Spectral.eval φ (T 0) ≤
      Spectral.eval φ (dsumFamily d T) := by
  have h := eval_restricts φ (unit_kron_restricts_dsumFamily m d T hiso)
  rw [eval_kron] at h
  have hu := (OM.PolMul.SpectralFacts.proof_SP_3 F φ).2 m
  change Spectral.eval φ (unit (F := F) m) = ((m : ℕ) : ℝ) at hu
  rw [hu] at h
  exact h

end OM.PolMul.Superadditivity
