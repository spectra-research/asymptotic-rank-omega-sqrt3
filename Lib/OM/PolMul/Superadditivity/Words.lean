/- Adapted from PolMul/Superadditivity/Words.lean of an earlier formalisation
   (commit 51c6e6b6e8b8d7226c6a828dba618ae1de5b5f8a).
   Uses Foundations tensor definitions; declarations are renamed under OM. -/
import Lib.OM.PolMul.Superadditivity.Products

/-! # Word tensors and restrictions to sets of words

A word is a function from the tensor-factor positions to the summand labels.
The coordinate-selection lemma below simultaneously distributes the tensor
product over the shared-leg sum and projects onto any chosen set of words.
-/

namespace OM.PolMul.Superadditivity

open AsymptoticSpectrumDuality Semicontinuity
open scoped BigOperators

universe u v
variable {F : Type u} [Field F]

/-- Present a tensor with the common first dimension made explicit. -/
noncomputable def sharedTensor {d : Fin 3 → ℕ+} (n : ℕ+) (h : d 0 = n)
    (T : T3 F d) : T3 F (fmt n (d 1) (d 2)) :=
  fun x => T (fun | 0 => Fin.cast (congrArg PNat.val h.symm) (x 0)
                  | 1 => x 1 | 2 => x 2)

lemma sharedTensor_iso {d : Fin 3 → ℕ+} (n : ℕ+) (h : d 0 = n)
    (T : T3 F d) : Iso (sharedTensor n h T) T := by
  apply iso_of_coordinates _ _ (fun i => finCongr (by fin_cases i <;> simp [fmt, h]))
  intro x
  unfold sharedTensor
  congr 1
  funext i
  fin_cases i <;> rfl

/-- A convenient coordinate formula for a shared-leg sum. -/
lemma pdsumFamily_blocks {m : ℕ} [NeZero m] (d : Fin m → Fin 3 → ℕ+)
    (n : ℕ+) (h : ∀ i, d i 0 = n) (T : ∀ i, T3 F (d i))
    (x : Fin n) (a b : Fin m) (v : Fin (d a 1)) (w : Fin (d b 2)) :
    pdsumFamily d n h T
      (fun | 0 => x | 1 => finSigmaFinEquiv ⟨a, v⟩ | 2 => finSigmaFinEquiv ⟨b, w⟩) =
    if hab : a = b then
      sharedTensor n (h a) (T a)
        (fun | 0 => x | 1 => v | 2 => Fin.cast (by change (d b 2 : ℕ) = (d a 2 : ℕ); rw [hab]) w)
    else 0 := by
  classical
  simp only [pdsumFamily, Equiv.symm_apply_apply]
  split_ifs with hab
  · subst b
    simp only [sharedTensor]
    congr 1
    · simp
    · refine Function.hfunext rfl ?_
      intro i j hij
      have he : i = j := eq_of_heq hij
      subst j
      apply (Fin.heq_ext_iff (by simp)).2
      fin_cases i
      · rfl
      · exact congrArg (fun q : (a : Fin m) × Fin (d a 1) => q.2.val)
          (Equiv.symm_apply_apply finSigmaFinEquiv ⟨a, v⟩)
      · exact congrArg (fun q : (a : Fin m) × Fin (d a 2) => q.2.val)
          (Equiv.symm_apply_apply finSigmaFinEquiv ⟨a, w⟩)
  · rfl

/-- The normalized word format. Its first dimension is independent of the word. -/
noncomputable def wordDims {ι : Type v} [Fintype ι] {m : ℕ}
    (d : Fin m → Fin 3 → ℕ+) (n : ℕ+) (w : ι → Fin m) : Fin 3 → ℕ+ :=
  fun i => ∏ a, fmt n (d (w a) 1) (d (w a) 2) i

/-- Tensor product of the summands selected by a word. -/
noncomputable def wordTensor {ι : Type v} [Fintype ι] {m : ℕ}
    (d : Fin m → Fin 3 → ℕ+) (n : ℕ+) (h : ∀ i, d i 0 = n)
    (T : ∀ i, T3 F (d i)) (w : ι → Fin m) : T3 F (wordDims d n w) :=
  productTensor (fun a => fmt n (d (w a) 1) (d (w a) 2))
    (fun a => sharedTensor n (h (w a)) (T (w a)))

lemma eval_wordTensor {ι : Type v} [Fintype ι] {m : ℕ} (φ : Spectral F)
    (d : Fin m → Fin 3 → ℕ+) (n : ℕ+) (h : ∀ i, d i 0 = n)
    (T : ∀ i, T3 F (d i)) (w : ι → Fin m) :
    Spectral.eval φ (wordTensor d n h T w) = ∏ a, Spectral.eval φ (T (w a)) := by
  rw [wordTensor, eval_productTensor]
  apply Finset.prod_congr rfl
  intro a _
  exact eval_iso φ (sharedTensor_iso n (h (w a)) (T (w a)))

/-- Equal multiplicities give a permutation of the factor positions. -/
lemma word_permutation {ι : Type v} [Fintype ι] {m : ℕ}
    (a b : ι → Fin m)
    (h : ∀ i, Fintype.card {j // a j = i} = Fintype.card {j // b j = i}) :
    ∃ e : Equiv.Perm ι, ∀ j, b (e j) = a j := by
  classical
  let E := fun i => Fintype.equivOfCardEq (h i)
  exact ⟨Equiv.ofFiberEquiv E, Equiv.ofFiberEquiv_map E⟩

/-- Word tensors with equal multiplicities are ambient-isomorphic. -/
lemma wordTensor_iso {ι : Type v} [Fintype ι] {m : ℕ}
    (d : Fin m → Fin 3 → ℕ+) (n : ℕ+) (h : ∀ i, d i 0 = n)
    (T : ∀ i, T3 F (d i)) (a b : ι → Fin m)
    (hc : ∀ i, Fintype.card {j // a j = i} = Fintype.card {j // b j = i}) :
    Iso (wordTensor d n h T a) (wordTensor d n h T b) := by
  obtain ⟨e, he⟩ := word_permutation a b hc
  have hi := productTensor_reindex e (fun j => fmt n (d (b j) 1) (d (b j) 2))
    (fun j => sharedTensor n (h (b j)) (T (b j)))
  change Iso (wordTensor d n h T (fun j => b (e j))) (wordTensor d n h T b) at hi
  have hw : (fun j => b (e j)) = a := funext he
  rw [hw] at hi
  exact hi

-- Dependent block decoding and the three coordinate maps are elaborated together.
set_option maxHeartbeats 400000 in
/-- Tensor powers distribute over the shared-leg sum, followed by projection
onto any injectively indexed collection of words. The first-leg selection is
identically the identity in the common product-coordinate representation. -/
lemma words_restricts {ι : Type v} [Fintype ι] {m : ℕ} [NeZero m]
    (d : Fin m → Fin 3 → ℕ+) (n : ℕ+) (h : ∀ i, d i 0 = n)
    (T : ∀ i, T3 F (d i)) (r : ℕ+) (w : Fin r → ι → Fin m)
    (hw : Function.Injective w) :
    Restricts
      (pdsumFamily (fun b => wordDims d n (w b)) (∏ _ : ι, n) (fun _ => rfl)
        (fun b => wordTensor d n h T (w b)))
      (productTensor (fun _ : ι => _) (fun _ => pdsumFamily d n h T)) := by
  classical
  let V : ℕ+ := ⟨∑ i, (d i 1 : ℕ),
    Finset.sum_pos (fun i _ => (d i 1).pos) Finset.univ_nonempty⟩
  let W : ℕ+ := ⟨∑ i, (d i 2 : ℕ),
    Finset.sum_pos (fun i _ => (d i 2).pos) Finset.univ_nonempty⟩
  let D : Fin 3 → ℕ+ := fmt (∏ _ : ι, n)
    ⟨∑ b : Fin r, (wordDims d n (w b) 1 : ℕ),
      Finset.sum_pos (fun b _ => (wordDims d n (w b) 1).pos) Finset.univ_nonempty⟩
    ⟨∑ b : Fin r, (wordDims d n (w b) 2 : ℕ),
      Finset.sum_pos (fun b _ => (wordDims d n (w b) 2).pos) Finset.univ_nonempty⟩
  let e : ∀ i, Fin (D i) → Fin (∏ _ : ι, fmt n V W i : ℕ+)
    | 0 => fun x => x
    | 1 => fun x =>
        let b : (b : Fin r) × Fin (wordDims d n (w b) 1) := finSigmaFinEquiv.symm x
        (productDecode (fun _ : ι => V)).symm (fun a => finSigmaFinEquiv
          ⟨w b.1 a, productDecode (fun a => d (w b.1 a) 1) b.2 a⟩)
    | 2 => fun x =>
        let b : (b : Fin r) × Fin (wordDims d n (w b) 2) := finSigmaFinEquiv.symm x
        (productDecode (fun _ : ι => W)).symm (fun a => finSigmaFinEquiv
          ⟨w b.1 a, productDecode (fun a => d (w b.1 a) 2) b.2 a⟩)
  apply restricts_of_coordinates e
  intro x
  obtain ⟨⟨b, v⟩, hv⟩ := (finSigmaFinEquiv (n := fun b : Fin r =>
    (wordDims d n (w b) 1 : ℕ))).surjective (x 1)
  obtain ⟨⟨c, z⟩, hz⟩ := (finSigmaFinEquiv (n := fun b : Fin r =>
    (wordDims d n (w b) 2 : ℕ))).surjective (x 2)
  have hx : x = (fun | 0 => x 0 | 1 => finSigmaFinEquiv ⟨b, v⟩ | 2 => finSigmaFinEquiv ⟨c, z⟩) := by
    funext i
    fin_cases i
    · rfl
    · exact hv.symm
    · exact hz.symm
  rw [hx]
  rw [pdsumFamily_blocks]
  have hright : productTensor (fun _ : ι => fmt n V W)
      (fun _ => pdsumFamily d n h T)
      (fun i => e i (((fun | 0 => x 0 | 1 => finSigmaFinEquiv ⟨b, v⟩ | 2 => finSigmaFinEquiv ⟨c, z⟩) : ∀ i, Fin (D i)) i)) =
      ∏ a, pdsumFamily d n h T
        (fun | 0 => productDecode (fun _ : ι => n) (x 0) a
             | 1 => finSigmaFinEquiv ⟨w b a, productDecode (fun a => d (w b a) 1) v a⟩
             | 2 => finSigmaFinEquiv ⟨w c a, productDecode (fun a => d (w c a) 2) z a⟩) := by
    unfold productTensor
    apply Finset.prod_congr rfl
    intro a _
    apply congrArg (pdsumFamily d n h T)
    funext i
    fin_cases i
    · rfl
    · simp only [e, fmt, Equiv.apply_symm_apply]
      exact congrArg (fun q : (b : Fin r) × Fin (wordDims d n (w b) 1) =>
        finSigmaFinEquiv (n := fun i => (d i 1 : ℕ))
          ⟨w q.1 a, productDecode (fun a => d (w q.1 a) 1) q.2 a⟩)
        (Equiv.symm_apply_apply finSigmaFinEquiv ⟨b, v⟩)
    · simp only [e, fmt, Equiv.apply_symm_apply]
      exact congrArg (fun q : (b : Fin r) × Fin (wordDims d n (w b) 2) =>
        finSigmaFinEquiv (n := fun i => (d i 2 : ℕ))
          ⟨w q.1 a, productDecode (fun a => d (w q.1 a) 2) q.2 a⟩)
        (Equiv.symm_apply_apply finSigmaFinEquiv ⟨c, z⟩)
  rw [hright]
  by_cases hbc : b = c
  · subst c
    rw [dif_pos rfl]
    simp only [pdsumFamily_blocks, dif_pos rfl, Fin.cast_refl]
    unfold sharedTensor wordTensor productTensor
    apply Finset.prod_congr rfl
    intro a _
    congr 1
  · rw [dif_neg hbc]
    symm
    obtain ⟨a, ha⟩ : ∃ a, w b a ≠ w c a := by
      by_contra hn
      push_neg at hn
      exact hbc (hw (funext hn))
    apply Finset.prod_eq_zero (Finset.mem_univ a)
    rw [pdsumFamily_blocks, dif_neg ha]

end OM.PolMul.Superadditivity
