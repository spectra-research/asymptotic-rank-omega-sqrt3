import Lib.OM.NNN34.BlockNetworks

/-! # Ordinary four-output realizations of local triangle models -/

noncomputable section
open scoped Classical

namespace OM.NNN34

open NNN32 NNN30.Net Semicontinuity

variable {V : Type} {f : Fin 4 → ℕ+} {m : ℕ} (N : FourNetwork V f)
variable {d : Fin m → Fin 3 → ℕ+} {w : Fin m → ℕ+}
variable (A : (j : Fin m) → TriangleModel (w j) (d j)) (p : Fin m → Fin 3 → V) (r : Reads N d)

private abbrev ValTy : N.graph.V ⊕ (Fin m × Fin 3) → Type
  | .inl v => N.graph.T v
  | .inr (j,i) => (A j).reg i

private abbrev old (x : ∀ v, ValTy N A v) : Env N := fun v => x (.inl v)
private abbrev regs (x : ∀ v, ValTy N A v) (j i) : (A j).reg i := x (.inr (j,i))

private def width : N.graph.K ⊕ (Fin m × Fin 3) → ℕ
  | .inl k => N.graph.r k
  | .inr (j,_) => w j

def realizeTriangles : FourNetwork V f where
  graph := {
    V := N.graph.V ⊕ (Fin m × Fin 3)
    T := ValTy N A
    fT := by rintro (v | ⟨j,i⟩) <;> dsimp [ValTy] <;> infer_instance
    loc := Sum.elim N.graph.loc (fun z => p z.1 z.2)
    K := N.graph.K ⊕ (Fin m × Fin 3)
    r := width N (w := w)
    e1 := Sum.elim N.graph.e1 (fun z => p z.1 z.2)
    e2 := Sum.elim N.graph.e2 (fun z => p z.1 (z.2+1))
    g := fun k => match k with
      | .inl t => fun i x => N.graph.g t i (old N A x)
      | .inr (j,i) => fun q x => if (A j).outgoing i (regs N A x j i) = q then
          (A j).localWeight i (r j i (old N A x)) (regs N A x j i) else 0
    h := fun k => match k with
      | .inl t => fun i x => N.graph.h t i (old N A x)
      | .inr (j,i) => fun q x => if (A j).incoming (i+1) (regs N A x j (i+1)) = q then 1 else 0
    out0 := fun _ _ => 1
    out1 := fun _ _ => 1
    out2 := fun _ _ => 1 }
  out := fun i x a => N.out i (old N A x) a

lemma realizeTriangles_local {τ} (hN : N.Local τ) (hr : ∀ j i, N.graph.DepAt (p j i) (r j i)) :
    (realizeTriangles N A p r).Local τ := by
  refine ⟨?_,?_,?_⟩
  · rintro (k | ⟨j,i⟩) q x y h
    · exact hN.1 k q _ _ fun v hv => h (.inl v) hv
    · have hz : regs N A x j i = regs N A y j i := h (.inr (j,i)) rfl
      have he := hr j i (old N A x) (old N A y) (fun v hv => h (.inl v) hv)
      change (if (A j).outgoing i _ = q then (A j).localWeight i _ _ else 0) = _
      rw [hz,he]; rfl
  · rintro (k | ⟨j,i⟩) q x y h
    · exact hN.2.1 k q _ _ fun v hv => h (.inl v) hv
    · exact congrArg (fun z => if (A j).incoming (i+1) z = q then (1:ℂ) else 0)
        (h (.inr (j,i+1)) rfl)
  · intro i a x y h
    exact hN.2.2 i a _ _ fun v hv => h (.inl v) hv

def perimeter (δ : V → V → ℝ) (t : Fin 3 → V) := δ (t 0) (t 1) + δ (t 1) (t 2) + δ (t 2) (t 0)

lemma realizeTriangles_cost (δ : V → V → ℝ) : (realizeTriangles N A p r).graph.cost δ =
    N.graph.cost δ + ∑ j, Real.logb 2 (w j : ℕ) * perimeter δ (p j) := by
  unfold TN.cost
  simp only [realizeTriangles, Fintype.sum_sum_type, Fintype.sum_prod_type, Sum.elim_inl, Sum.elim_inr, width]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [Fin.sum_univ_three]
  change δ (p j 0) (p j 1) * _ + δ (p j 1) (p j 2) * _ + δ (p j 2) (p j 0) * _ = _
  dsimp [perimeter, realizeTriangles, width]
  ring

private lemma edge_sum {q : ℕ} (s t : Fin q) (a : ℂ) :
    (∑ z : Fin q, (if s=z then a else 0) * (if t=z then 1 else 0)) = if s=t then a else 0 := by
  by_cases h : s=t
  · subst t; simp
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro z _
    split_ifs <;> simp_all

lemma realizeTriangles_tensor (U : (j : Fin m) → KTensor ℂ (d j))
    (hu : ∀ j a, U j a = (A j).coeff a) :
    (realizeTriangles N A p r).tensor = insertCubes N U r := by
  funext a
  let M := realizeTriangles N A p r
  let Y := (j : Fin m) → (i : Fin 3) → (A j).reg i
  let E : Env M ≃ Env N × Y := {
    toFun := fun x => (old N A x, regs N A x)
    invFun := fun z v => match v with | .inl u => z.1 u | .inr (j,i) => z.2 j i
    left_inv := fun x => funext fun v => by cases v <;> rfl
    right_inv := fun _ => rfl }
  let edge (x : Env N) (y : Y) (j i) :=
    if (A j).outgoing i (y j i) = (A j).incoming (i+1) (y j (i+1)) then
      (A j).localWeight i (r j i x) (y j i) else 0
  let ext (x : Env N) := (∏ i, N.out i x (a i)) * ∏ k, N.graph.F k x
  have expand : M.tensor a = ∑ z : Env N × Y, ext z.1 * ∏ j, ∏ i, edge z.1 z.2 j i := by
    rw [← E.sum_comp]
    apply Finset.sum_congr rfl
    intro x _
    have eqedge (j i) : M.graph.F (.inr (j,i)) x = edge (old N A x) (regs N A x) j i :=
      edge_sum _ _ _
    have eqold (k : N.graph.K) : M.graph.F (.inl k) x = N.graph.F k (old N A x) := rfl
    change (∏ i, N.out i (old N A x) (a i)) * 1 * 1 * (∏ k, M.graph.F k x) = _
    have split : (∏ k, M.graph.F k x) = (∏ k : N.graph.K, M.graph.F (.inl k) x) *
        ∏ z : Fin m × Fin 3, M.graph.F (.inr z) x :=
      Fintype.prod_sum_type (fun k : N.graph.K ⊕ (Fin m × Fin 3) => M.graph.F k x)
    rw [split, Fintype.prod_prod_type]
    simp only [eqold, eqedge, mul_one,ext]
    rw [← mul_assoc]
    rfl
  rw [expand,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro x _
  change (∑ y : Y, ext x * (∏ j, ∏ i, edge x y j i)) = ext x * _
  rw [← Finset.mul_sum]
  apply congrArg (ext x * ·)
  simp_rw [hu, TriangleModel.coeff]
  rw [Fintype.prod_sum]

end OM.NNN34
