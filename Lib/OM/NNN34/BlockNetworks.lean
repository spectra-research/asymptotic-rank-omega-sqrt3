import Lib.OM.NNN34.TriangleModel
import Lib.OM.NNN32.FourPrices

/-! # Simultaneous powers of a network and its locally read resource tensors -/

noncomputable section
open scoped Classical

namespace OM.NNN34

open Semicontinuity NNN32 NNN30.Net

variable {V : Type} {f : Fin 4 → ℕ+} {m : ℕ} (N : FourNetwork V f)

abbrev Env := (v : N.graph.V) → N.graph.T v

abbrev Reads (d : Fin m → Fin 3 → ℕ+) := (j : Fin m) → (i : Fin 3) → Env N → Fin (d j i)

def insertCubes {d : Fin m → Fin 3 → ℕ+} (U : (j : Fin m) → KTensor ℂ (d j))
    (r : Reads N d) : KTensor ℂ f := fun a => ∑ x : Env N,
  (∏ i, N.out i x (a i)) * (∏ k, N.graph.F k x) * ∏ j, U j (fun i => r j i x)

private def unpack (n : ℕ+) :
    ((v : Fin (n : ℕ) × N.graph.V) → N.graph.T v.2) ≃ (Fin (n : ℕ) → Env N) where
  toFun x i v := x (i,v)
  invFun x v := x v.1 v.2
  left_inv _ := rfl
  right_inv _ := rfl

def repeatNet (n : ℕ+) : FourNetwork V (formatPow f n) where
  graph := {
    V := Fin (n : ℕ) × N.graph.V
    T := fun v => N.graph.T v.2
    loc := fun v => N.graph.loc v.2
    K := Fin (n : ℕ) × N.graph.K
    e1 := fun k => N.graph.e1 k.2
    e2 := fun k => N.graph.e2 k.2
    r := fun k => N.graph.r k.2
    g := fun k i x => N.graph.g k.2 i (unpack N n x k.1)
    h := fun k i x => N.graph.h k.2 i (unpack N n x k.1)
    out0 := fun _ _ => 1
    out1 := fun _ _ => 1
    out2 := fun _ _ => 1 }
  out := fun i x a => ∏ j, N.out i (unpack N n x j) (powIndexEquiv (f i) n a j)

lemma repeat_local {τ} (hN : N.Local τ) (n : ℕ+) : (repeatNet N n).Local τ := by
  refine ⟨?_,?_,?_⟩
  · intro k i x y h
    exact hN.1 k.2 i _ _ fun v hv => h (k.1,v) hv
  · intro k i x y h
    exact hN.2.1 k.2 i _ _ fun v hv => h (k.1,v) hv
  · intro i a x y h
    change (∏ j, N.out i (unpack N n x j) (powIndexEquiv (f i) n a j)) = ∏ j, N.out i (unpack N n y j) _
    apply Finset.prod_congr rfl
    intro j _
    exact hN.2.2 i _ _ _ fun v hv => h (j,v) hv

lemma repeat_cost (d : V → V → ℝ) (n : ℕ+) :
    (repeatNet N n).graph.cost d = (n : ℕ) * N.graph.cost d := by
  change (∑ k : Fin (n : ℕ) × N.graph.K, d (N.graph.e1 k.2) (N.graph.e2 k.2) *
    Real.logb 2 (N.graph.r k.2)) = _
  rw [Fintype.sum_prod_type]
  simp [TN.cost]

def blockRead {d : Fin m → Fin 3 → ℕ+} (r : Reads N d) (n : ℕ+) :
    Reads (repeatNet N n) (fun j => formatPow (d j) n) :=
  fun j i x => (powIndexEquiv (d j i) n).symm (fun h => r j i (unpack N n x h))

lemma blockRead_local {d : Fin m → Fin 3 → ℕ+} (r : Reads N d) (p : Fin m → Fin 3 → V)
    (hr : ∀ j i, N.graph.DepAt (p j i) (r j i)) (n : ℕ+) (j i) :
    (repeatNet N n).graph.DepAt (p j i) (blockRead N r n j i) := by
  intro x y h
  apply congrArg (powIndexEquiv (d j i) n).symm
  funext t
  exact hr j i _ _ fun v hv => h (t,v) hv

lemma repeat_insert {d : Fin m → Fin 3 → ℕ+} (U : (j : Fin m) → KTensor ℂ (d j))
    (r : Reads N d) (n : ℕ+) :
    insertCubes (repeatNet N n) (fun j => blockPower (U j) n) (blockRead N r n) =
      blockPower (insertCubes N U r) n := by
  funext a
  let term (h : Fin (n : ℕ)) (x : Env N) := (∏ i, N.out i x (sliceFun f n a h i)) *
    (∏ k, N.graph.F k x) * ∏ j, U j (fun i => r j i x)
  change (∑ x : Env (repeatNet N n), _) = ∏ h, ∑ x : Env N, term h x
  rw [Fintype.prod_sum, ← (unpack N n).sum_comp]
  apply Finset.sum_congr (by ext; simp)
  intro x _
  let X := unpack N n x
  have out : (∏ i, (repeatNet N n).out i x (a i)) =
      ∏ h, ∏ i, N.out i (X h) (sliceFun f n a h i) := by
    change (∏ i, ∏ h, N.out i (X h) (sliceFun f n a h i)) = _
    exact Finset.prod_comm
  have bonds : (∏ k, (repeatNet N n).graph.F k x) = ∏ h, ∏ k, N.graph.F k (X h) := by
    exact Fintype.prod_prod_type (fun k : Fin (n : ℕ) × N.graph.K => N.graph.F k.2 (X k.1))
  have pieces : (∏ j, blockPower (U j) n (fun i => blockRead N r n j i x)) =
      ∏ h, ∏ j, U j (fun i => r j i (X h)) := by
    unfold blockPower
    have hs (j : Fin m) (h : Fin (n : ℕ)) : sliceFun (d j) n (fun i => blockRead N r n j i x) h =
        fun i => r j i (X h) := by
      funext i
      exact congrFun ((powIndexEquiv (d j i) n).apply_symm_apply _) h
    simp_rw [hs]
    exact Finset.prod_comm
  rw [out,bonds,pieces]
  simp only [term, Finset.prod_mul_distrib, X]

end OM.NNN34
