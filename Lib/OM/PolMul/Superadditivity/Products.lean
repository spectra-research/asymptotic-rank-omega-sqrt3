/- Adapted from PolMul/Superadditivity/Products.lean of an earlier formalisation
   (commit 51c6e6b6e8b8d7226c6a828dba618ae1de5b5f8a).
   Uses Foundations tensor definitions; declarations are renamed under OM. -/
import Lib.OM.PolMul.Superadditivity.SA1
import Mathlib.Data.Fintype.Option

/-! # Finite tensor products and coordinate selections

The finite product uses the same `Fintype.equivFin` encoding as `OM.PolMul.symm`.
No choice of enumeration enters the resulting tensor isomorphism class.
-/

namespace OM.PolMul.Superadditivity

open AsymptoticSpectrumDuality Semicontinuity
open scoped BigOperators

universe u v w
variable {F : Type u} [Field F]

lemma iso_of_coordinates {dT dS : Fin 3 → ℕ+}
    (T : OM.PolMul.T3 F dT) (S : OM.PolMul.T3 F dS)
    (e : ∀ i : Fin 3, Fin (dT i) ≃ Fin (dS i))
    (h : ∀ idx, T idx = S (fun i => e i (idx i))) : OM.PolMul.Iso T S := by
  classical
  let A : ∀ i : Fin 3, Matrix (Fin (dT i)) (Fin (dS i)) F :=
    fun i x y => if e i x = y then 1 else 0
  let B : ∀ i : Fin 3, Matrix (Fin (dS i)) (Fin (dT i)) F :=
    fun i y x => if y = e i x then 1 else 0
  refine ⟨A, B, ?_, ?_, ?_⟩
  · intro i
    ext x x'
    simp only [Matrix.mul_apply, Matrix.one_apply]
    by_cases hxx : x = x'
    · subst x'
      simp [A, B]
    · have he : e i x ≠ e i x' := fun heq => hxx ((e i).injective heq)
      simp [A, B, hxx, he]
  · intro i
    ext y y'
    simp only [Matrix.mul_apply, Matrix.one_apply]
    by_cases hyy : y = y'
    · subst y'
      rw [Finset.sum_eq_single ((e i).symm y)]
      · simp [A, B]
      · intro x _ hx
        have hne : y ≠ e i x := by
          intro heq
          apply hx
          apply (e i).injective
          simpa using! heq.symm
        simp [A, B, hne]
      · simp
    · rw [if_neg hyy, Finset.sum_eq_zero]
      intro x _
      by_cases hy'x : e i x = y'
      · have hyx : y ≠ e i x := fun heq => hyy (heq.trans hy'x)
        simp [A, B, hy'x, hyx]
        exact hyy
      · simp [A, B, hy'x]
  · intro idx
    rw [h idx]
    rw [Finset.sum_eq_single (fun i => e i (idx i))]
    · simp [A]
    · intro sidx _ hsidx
      have hex : ∃ i : Fin 3, e i (idx i) ≠ sidx i := by
        by_contra hall
        push_neg at hall
        exact hsidx (funext fun i => (hall i).symm)
      obtain ⟨i, hi⟩ := hex
      have hz : A i (idx i) (sidx i) = 0 := by simp [A, hi]
      rw [show (∏ j : Fin 3, A j (idx j) (sidx j)) = 0 from
        Finset.prod_eq_zero (Finset.mem_univ i) hz, zero_mul]
    · simp

/-- Selecting one source coordinate for each target coordinate is a restriction.
The selections need not be injective. -/
lemma restricts_of_coordinates {dT dS : Fin 3 → ℕ+}
    {T : T3 F dT} {S : T3 F dS}
    (e : ∀ i, Fin (dT i) → Fin (dS i))
    (h : ∀ x, T x = S (fun i => e i (x i))) : Restricts T S := by
  classical
  refine ⟨fun i x y => if e i x = y then 1 else 0, fun x => ?_⟩
  rw [Finset.sum_eq_single (fun i => e i (x i))]
  · simpa using! h x
  · intro y _ hy
    obtain ⟨i, hi⟩ : ∃ i, e i (x i) ≠ y i := by
      by_contra hn
      push_neg at hn
      exact hy (funext fun i => (hn i).symm)
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi), zero_mul]
  · simp

/-- Decode a grouped coordinate as one coordinate in each factor. -/
noncomputable def productDecode {ι : Type v} [Fintype ι] (d : ι → ℕ+) :
    Fin (∏ a, d a : ℕ+) ≃ (∀ a, Fin (d a)) := by
  classical
  exact (finCongr (by
    rw [Fintype.card_pi]
    simpa only [Fintype.card_fin] using!
      (map_prod PNat.coeMonoidHom d Finset.univ))).trans
    (Fintype.equivFin _).symm

/-- An entrywise finite Kronecker product. -/
noncomputable def productTensor {ι : Type v} [Fintype ι]
    (d : ι → Fin 3 → ℕ+) (T : ∀ a, T3 F (d a)) :
    T3 F (fun i => ∏ a, d a i) :=
  fun x => ∏ a, T a (fun i => productDecode (fun a => d a i) (x i) a)

/-- Reordering factors is an ambient tensor isomorphism. -/
lemma productTensor_reindex {ι : Type v} {κ : Type w} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (d : κ → Fin 3 → ℕ+) (T : ∀ a, T3 F (d a)) :
    Iso (productTensor (fun a => d (e a)) (fun a => T (e a))) (productTensor d T) := by
  let E : ∀ i, Fin (∏ a, d (e a) i : ℕ+) ≃ Fin (∏ a, d a i : ℕ+) :=
    fun i => (productDecode _).trans
      ((Equiv.piCongrLeft (fun a => Fin (d a i)) e).trans (productDecode _).symm)
  apply iso_of_coordinates _ _ E
  intro x
  unfold productTensor
  rw [← e.prod_comp]
  apply Finset.prod_congr rfl
  intro a _
  congr 1
  funext i
  simp [E, Equiv.piCongrLeft_apply_apply]

/-- Splitting an `Option`-indexed product isolates its distinguished factor. -/
lemma productTensor_option {ι : Type v} [Fintype ι]
    (d : Option ι → Fin 3 → ℕ+) (T : ∀ a, T3 F (d a)) :
    Iso (productTensor d T)
      (kron (T none) (productTensor (fun a => d (some a)) (fun a => T (some a)))) := by
  let E : ∀ i, Fin (∏ a, d a i : ℕ+) ≃
      Fin (d none i * ∏ a, d (some a) i : ℕ+) :=
    fun i => (productDecode _).trans (Equiv.piOptionEquivProd.trans
      ((Equiv.prodCongr (Equiv.refl _) (productDecode _).symm).trans
        (kronDecodeEquiv).symm))
  apply iso_of_coordinates _ _ E
  intro x
  unfold productTensor
  rw [Fintype.prod_option]
  change _ = T none (kronLeftIndex (fun i => E i (x i))) *
    ∏ a, T (some a) (fun i => productDecode _ (kronRightIndex (fun i => E i (x i)) i) a)
  congr 1
  · congr 1
    funext i
    change _ = (kronDecodeEquiv (E i (x i))).1
    simp [E]
  · apply Finset.prod_congr rfl
    intro a _
    congr 1
    funext i
    change _ = productDecode _ ((kronDecodeEquiv (E i (x i))).2) a
    simp [E]

/-- Spectral evaluation turns a finite tensor product into a real product. -/
lemma eval_productTensor {ι : Type v} [Fintype ι] (φ : Spectral F)
    (d : ι → Fin 3 → ℕ+) (T : ∀ a, T3 F (d a)) :
    Spectral.eval φ (productTensor d T) = ∏ a, Spectral.eval φ (T a) := by
  classical
  revert d T
  refine Fintype.induction_empty_option
    (P := fun α _ => ∀ (d : α → Fin 3 → ℕ+) (T : ∀ a, T3 F (d a)),
      Spectral.eval φ (productTensor d T) = ∏ a, Spectral.eval φ (T a))
    ?_ ?_ ?_ ι
  · intro α β _ e ih d T
    letI : Fintype α := Fintype.ofEquiv β e.symm
    rw [← eval_iso φ (productTensor_reindex e d T), ih]
    exact e.prod_comp (fun a => Spectral.eval φ (T a))
  · intro d T
    have hi : Iso (productTensor d T) (unit (F := F) 1) := by
      apply iso_of_coordinates _ _ (fun i => finCongr (by fin_cases i <;> simp [fmt]))
      intro x
      simp [productTensor, unit, Fin.eq_zero]
    rw [eval_iso φ hi]
    simpa using! (SpectralFacts.proof_SP_3 F φ).2 1
  · intro α _ ih d T
    rw [eval_iso φ (productTensor_option d T), eval_kron, ih, Fintype.prod_option]

end OM.PolMul.Superadditivity

