import Lib.OM.NNN32.CutContext

/-! # Isolating two ordered bundles of factors, including their exact bill -/

noncomputable section
open scoped Classical

namespace OM.NNN32.FourNetwork

open Semicontinuity OM.NNN30.Net

variable {V : Type} {f : Fin 4 → ℕ+} (N : FourNetwork V f) (t : Fin 4 → V)

def tag (k : N.graph.K) : Fin 3 :=
  if N.graph.e1 k=t 0 ∧ N.graph.e2 k=t 3 then 0 else
  if N.graph.e1 k=t 1 ∧ N.graph.e2 k=t 2 then 1 else 2

abbrev edges (i : Fin 3) := {k : N.graph.K // N.tag t k = i}
abbrev bundle (i : Fin 3) := (k : N.edges t i) → Fin (N.graph.r k.1)

lemma tag_zero (k : N.graph.K) : N.tag t k = 0 ↔ N.graph.e1 k = t 0 ∧ N.graph.e2 k = t 3 := by
  unfold tag; split_ifs <;> simp_all

lemma tag_one (ht : t 0 ≠ t 1) (k : N.graph.K) :
    N.tag t k = 1 ↔ N.graph.e1 k = t 1 ∧ N.graph.e2 k = t 2 := by
  unfold tag
  split_ifs with h k' <;> simp_all

def leftHalf (i : Fin 3) (z : N.bundle t i) (x : assignments N) :=
  ∏ k, N.graph.g k.1 (z k) x

def rightHalf (i : Fin 3) (z : N.bundle t i) (x : assignments N) :=
  ∏ k, N.graph.h k.1 (z k) x

def unmarked : FourNetwork V f where
  graph := { N.graph with
    K := N.edges t 2
    fK := inferInstance
    e1 := fun k => N.graph.e1 k.1
    e2 := fun k => N.graph.e2 k.1
    r := fun k => N.graph.r k.1
    g := fun k => N.graph.g k.1
    h := fun k => N.graph.h k.1 }
  out := N.out

def context : CutContext V f (N.bundle t 0) (N.bundle t 1) where
  net := N.unmarked t
  sites := t
  half
    | 0 => N.leftHalf t 0
    | 1 => N.leftHalf t 1
    | 2 => N.rightHalf t 1
    | 3 => N.rightHalf t 0

lemma context_local {τ : Fin 4 → V} (h : N.Local τ) (ht : t 0 ≠ t 1) : (N.context t).Local τ := by
  refine ⟨⟨fun k z => h.1 k.1 z,fun k z => h.2.1 k.1 z,h.2.2⟩,?_⟩
  intro i
  fin_cases i <;> intro z x y hxy <;> apply Finset.prod_congr rfl <;> intro k _
  · exact h.1 k.1 _ _ _ fun s hs => hxy s (hs.trans (((N.tag_zero t _).1 k.2).1))
  · exact h.1 k.1 _ _ _ fun s hs => hxy s (hs.trans (((N.tag_one t ht _).1 k.2).1))
  · exact h.2.1 k.1 _ _ _ fun s hs => hxy s (hs.trans (((N.tag_one t ht _).1 k.2).2))
  · exact h.2.1 k.1 _ _ _ fun s hs => hxy s (hs.trans (((N.tag_zero t _).1 k.2).2))

lemma context_closed : (N.context t).closed = N.tensor := by
  funext a
  apply Finset.sum_congr rfl
  intro x _
  have part i : (∏ k : N.edges t i, N.graph.F k.1 x) =
      ∑ z : N.bundle t i, N.leftHalf t i z x * N.rightHalf t i z x := by
    unfold TN.F leftHalf rightHalf
    rw [Fintype.prod_sum]
    exact Finset.sum_congr rfl fun z _ => Finset.prod_mul_distrib
  have h := Fintype.prod_fiberwise (N.tag t) (fun k => N.graph.F k x)
  rw [Fin.prod_univ_three,part 0,part 1] at h
  change ((∏ i,N.out i x (a i)) * (∏ k : N.edges t 2,N.graph.F k.1 x)) *
    ((∑ z,N.leftHalf t 0 z x * N.rightHalf t 0 z x) * (∑ z,N.leftHalf t 1 z x * N.rightHalf t 1 z x)) =
      (∏ i,N.out i x (a i)) * 1 * 1 * (∏ k,N.graph.F k x)
  rw [← h]
  ring

private lemma bits (i : Fin 3) (hp : ∀ k, 0 < N.graph.r k) :
    Real.logb 2 (Fintype.card (N.bundle t i)) = ∑ k : N.edges t i, Real.logb 2 (N.graph.r k.1) := by
  rw [Fintype.card_pi]
  simp only [Fintype.card_fin,Nat.cast_prod]
  rw [Real.logb_prod _ _ fun k _ => by exact_mod_cast (hp k.1).ne']

private lemma width_indicator (i : Fin 3) (hp : ∀ k, 0 < N.graph.r k) :
    Real.logb 2 (Fintype.card (N.bundle t i)) = ∑ k, if N.tag t k = i then Real.logb 2 (N.graph.r k) else 0 := by
  rw [bits N t i hp,← Finset.sum_filter]
  exact (Finset.sum_subtype (Finset.univ.filter fun k => N.tag t k=i)
    (fun _ => by simp) (fun k => Real.logb 2 (N.graph.r k))).symm

lemma bundle_widths (ht : t 0 ≠ t 1) (hp : ∀ k, 0 < N.graph.r k) :
    Real.logb 2 (Fintype.card (N.bundle t 0)) = N.graph.wid (t 0) (t 3) ∧
    Real.logb 2 (Fintype.card (N.bundle t 1)) = N.graph.wid (t 1) (t 2) := by
  rw [width_indicator N t 0 hp,width_indicator N t 1 hp]
  simp only [TN.wid,N.tag_zero,N.tag_one t ht,and_self]

lemma unmarked_cost (d : V → V → ℝ) (ht : t 0 ≠ t 1) (hp : ∀ k, 0 < N.graph.r k) :
    N.graph.cost d = (N.unmarked t).graph.cost d +
      d (t 0) (t 3) * N.graph.wid (t 0) (t 3) + d (t 1) (t 2) * N.graph.wid (t 1) (t 2) := by
  let F k := d (N.graph.e1 k) (N.graph.e2 k) * Real.logb 2 (N.graph.r k)
  have widths := N.bundle_widths t ht hp
  rw [← widths.1,← widths.2,bits N t 0 hp,bits N t 1 hp,Finset.mul_sum,Finset.mul_sum]
  have h := Fintype.sum_fiberwise (N.tag t) F
  rw [Fin.sum_univ_three] at h
  have h0 (k : N.edges t 0) : F k.1 = _ := congrArg₂ (fun x y => d x y * Real.logb 2 (N.graph.r k.1))
    (((N.tag_zero t _).1 k.2).1) (((N.tag_zero t _).1 k.2).2)
  have h1 (k : N.edges t 1) : F k.1 = _ := congrArg₂ (fun x y => d x y * Real.logb 2 (N.graph.r k.1))
    (((N.tag_one t ht _).1 k.2).1) (((N.tag_one t ht _).1 k.2).2)
  change ∑ k, F k = (∑ k : N.edges t 2,F k.1) + _ + _
  rw [← h]
  simp only [h0,h1]
  ring

end OM.NNN32.FourNetwork
