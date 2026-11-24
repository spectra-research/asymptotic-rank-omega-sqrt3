import Lib.OM.NNN.Extraction

noncomputable section
open scoped BigOperators Classical
set_option maxHeartbeats 1000000

namespace OM.NNN.Raw

open CoordinateTensor

variable {X R A B C L : Type}

/-- The rectangular matrix-multiplication source for a tensor square. -/
def squareSource (X R : Type) : Tensor ℂ (X × R) (X × R) (X × X) :=
  fun i j k => if i.1 = k.1 ∧ j.1 = k.2 ∧ i.2 = j.2 then 1 else 0

/-- A direct sum of pair units, on coordinate sets `E l`. -/
def edges (E : L → Type) : Tensor ℂ (Σ l, E l) (Σ l, E l) L :=
  fun i j k => if i = j ∧ i.1 = k then 1 else 0

theorem map_squareSource [Fintype X] [Fintype R]
    (U : A → X × R → ℂ) (V : B → X × R → ℂ) (W : C → X × X → ℂ)
    (a : A) (b : B) (c : C) :
    mapTensor U V W (squareSource X R) a b c =
      ∑ x : X, ∑ y : X, ∑ r : R, U a (x, r) * V b (y, r) * W c (x, y) := by
  simp only [mapTensor, squareSource, Fintype.sum_prod_type, mul_ite, mul_one, mul_zero,
    ite_and]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq',
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_comm]

theorem map_edges [Fintype L] (E : L → Type) [∀ l, Fintype (E l)]
    (U : A → (Σ l, E l) → ℂ) (V : B → (Σ l, E l) → ℂ) (W : C → L → ℂ)
    (a : A) (b : B) (c : C) :
    mapTensor U V W (edges E) a b c =
      ∑ i : (Σ l, E l), U a i * V b i * W c i.1 := by
  simp [mapTensor, edges, mul_ite, ite_and, Finset.sum_ite_irrel]

theorem map_source_reindex {I J K I' J' K' : Type}
    [Fintype I] [Fintype J] [Fintype K] [Fintype I'] [Fintype J'] [Fintype K']
    (S : Tensor ℂ I J K) (e : I' ≃ I) (f : J' ≃ J) (g : K' ≃ K)
    (U : A → I' → ℂ) (V : B → J' → ℂ) (W : C → K' → ℂ)
    (a : A) (b : B) (c : C) :
    mapTensor U V W (fun i j k => S (e i) (f j) (g k)) a b c =
      mapTensor (fun a i => U a (e.symm i)) (fun b j => V b (f.symm j))
        (fun c k => W c (g.symm k)) S a b c := by
  unfold mapTensor
  refine Fintype.sum_equiv e _ _ (fun i => ?_)
  refine Fintype.sum_equiv f _ _ (fun j => ?_)
  refine Fintype.sum_equiv g _ _ (fun k => ?_)
  simp

def sourceEquiv (E : L → Type) (R : Type) :
    (Σ l, (E l × R) ⊕ R) ≃ ((Σ l, E l) × R) ⊕ (Σ _ : L, R) where
  toFun
    | ⟨l, .inl (i, r)⟩ => .inl (⟨l, i⟩, r)
    | ⟨l, .inr r⟩ => .inr ⟨l, r⟩
  invFun
    | .inl (⟨l, i⟩, r) => ⟨l, .inl (i, r)⟩
    | .inr ⟨l, r⟩ => ⟨l, .inr r⟩
  left_inv x := by rcases x with ⟨l, (⟨i, r⟩ | r)⟩ <;> rfl
  right_inv x := by rcases x with ⟨⟨l, i⟩, r⟩ | ⟨l, r⟩ <;> rfl

def augmentedSource (E : L → Type) (R : Type) :
    Tensor ℂ (Σ l, (E l × R) ⊕ R) (Σ l, (E l × R) ⊕ R)
      (((Σ l, E l) × (Σ l, E l)) ⊕ L) :=
  fun i j k => directSum (squareSource (Σ l, E l) R) (edges (fun _ : L => R))
    (sourceEquiv E R i) (sourceEquiv E R j) k

def blockSlice (E : L → Type) : L → (((Σ l, E l) × (Σ l, E l)) ⊕ L) → ℂ
  | l, .inl (i, j) => if i = j ∧ i.1 = l then 1 else 0
  | l, .inr k => if k = l then 1 else 0

theorem map_augmented_block [Fintype L] [Fintype R]
    (E : L → Type) [∀ l, Fintype (E l)]
    (U : A → (Σ l, (E l × R) ⊕ R) → ℂ)
    (V : B → (Σ l, (E l × R) ⊕ R) → ℂ) (a : A) (b : B) (l : L) :
    mapTensor U V (blockSlice E) (augmentedSource E R) a b l =
      ∑ i : (E l × R) ⊕ R, U a ⟨l, i⟩ * V b ⟨l, i⟩ := by
  unfold augmentedSource
  have hr := map_source_reindex
    (directSum (squareSource (Σ l, E l) R) (edges (fun _ : L => R)))
    (sourceEquiv E R) (sourceEquiv E R)
    (Equiv.refl _) U V (blockSlice E) a b l
  simp only [Equiv.refl_symm, Equiv.refl_apply] at hr
  rw [hr, mapTensor_directSum, map_squareSource, map_edges]
  simp only [Equiv.refl_symm, Equiv.refl_apply, sourceEquiv, Equiv.coe_fn_symm_mk,
    blockSlice, mul_ite, mul_one, mul_zero, ite_and]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq',
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  simp [Fintype.sum_sigma, Fintype.sum_sum_type, Fintype.sum_prod_type,
    Finset.sum_ite_irrel]

end OM.NNN.Raw
