import Lib.OM.NNN32.WirePrices
import Lib.OM.NNN30.Net.Adm

/-! # Networks with a free leg at each of four marked sites

Bond factors and changes of graph use the network on sites. The boundary
observation at each leg depends only on variables at that leg's own site.
For coefficient identities the four observations can be multiplied and fed
to the existing partition function as one array indexed by a full tuple.
-/

noncomputable section
open scoped Classical

namespace OM.NNN32

open OM.NNN30.Net Semicontinuity AsymptoticSpectrumDuality

structure FourNetwork (V : Type) (d : Fin 4 → ℕ+) where
  graph : TN V Unit Unit Unit
  out : (i : Fin 4) → ((v : graph.V) → graph.T v) → Fin (d i) → ℂ

namespace FourNetwork

variable {V V' : Type} {d e : Fin 4 → ℕ+}

def packed (N : FourNetwork V d) : TN V ((i : Fin 4) → Fin (d i)) Unit Unit :=
  { N.graph with out0 := fun x a => ∏ i, N.out i x (a i), out1 := fun _ _ => 1, out2 := fun _ _ => 1 }

def tensor (N : FourNetwork V d) : KTensor ℂ d := fun a => N.packed.Z a () ()

def Local (N : FourNetwork V d) (τ : Fin 4 → V) : Prop :=
  (∀ k i, N.graph.DepAt (N.graph.e1 k) (N.graph.g k i)) ∧
  (∀ k i, N.graph.DepAt (N.graph.e2 k) (N.graph.h k i)) ∧
  ∀ i a, N.graph.DepAt (τ i) (fun x => N.out i x a)

/-- The graph with trivial output data has the site locality property. -/
def silent (N : FourNetwork V d) : TN V Unit Unit Unit :=
  { N.graph with out0 := fun _ _ => 1, out1 := fun _ _ => 1, out2 := fun _ _ => 1 }

lemma silent_local {N : FourNetwork V d} {τ : Fin 4 → V} (h : N.Local τ) :
    N.silent.Local (fun i => τ i.castSucc) :=
  ⟨h.1,h.2.1,fun _ _ _ _ => rfl,fun _ _ _ _ => rfl,fun _ _ _ _ => rfl⟩

def relocate (N : FourNetwork V d) (f : V → V') : FourNetwork V' d :=
  ⟨N.graph.relocate f,N.out⟩

lemma tensor_relocate (N : FourNetwork V d) (f : V → V') : (N.relocate f).tensor = N.tensor := rfl

lemma Local.relocate {N : FourNetwork V d} {τ : Fin 4 → V} (h : N.Local τ) (f : V → V') :
    (N.relocate f).Local (f ∘ τ) :=
  ⟨fun k i => (h.1 k i).relocate f,fun k i => (h.2.1 k i).relocate f,fun i a => (h.2.2 i a).relocate f⟩

def rev (N : FourNetwork V d) (P : N.graph.K → Prop) : FourNetwork V d :=
  ⟨N.graph.rev P,N.out⟩

lemma tensor_rev (N : FourNetwork V d) (P : N.graph.K → Prop) : (N.rev P).tensor = N.tensor := by
  funext x
  exact congrFun (congrFun (congrFun (N.packed.Z_rev P) x) ()) ()

lemma Local.rev {N : FourNetwork V d} {τ : Fin 4 → V} (h : N.Local τ) (P : N.graph.K → Prop) :
    (N.rev P).Local τ :=
  ⟨((silent_local h).rev P).1,((silent_local h).rev P).2.1,h.2.2⟩

def reroute (N : FourNetwork V d) (P : N.graph.K → Prop) (v : V) : FourNetwork V d :=
  ⟨{ N.packed.reroute P v with out0 := fun _ _ => 1, out1 := fun _ _ => 1, out2 := fun _ _ => 1 },
    fun i x a => N.out i (fun s => x (.inl s)) a⟩

lemma tensor_reroute (N : FourNetwork V d) (P : N.graph.K → Prop) (v : V) :
    (N.reroute P v).tensor = N.tensor := by
  funext x
  exact congrFun (congrFun (congrFun (N.packed.Z_reroute P v) x) ()) ()

lemma Local.reroute {N : FourNetwork V d} {τ : Fin 4 → V} (h : N.Local τ)
    (P : N.graph.K → Prop) (v : V) : (N.reroute P v).Local τ := by
  have b := (silent_local h).reroute P v
  refine ⟨?_,?_,fun i a x y hxy => h.2.2 i a _ _ fun s hs => hxy (.inl s) hs⟩
  · rintro (k|k) l
    · exact b.1 (.inl k) l
    · exact b.1 (.inr k) l
  · rintro (k|k) l
    · exact b.2.1 (.inl k) l
    · exact b.2.1 (.inr k) l

def kron (N : FourNetwork V d) (M : FourNetwork V e) : FourNetwork V (fun i => d i * e i) where
  graph := { N.packed.kron M.packed with
    out0 := fun _ _ => 1, out1 := fun _ _ => 1, out2 := fun _ _ => 1 }
  out i x a := N.out i (fun s => x (.inl s)) (finProdFinEquiv.symm a).1 *
    M.out i (fun s => x (.inr s)) (finProdFinEquiv.symm a).2

lemma Local.kron {N : FourNetwork V d} {M : FourNetwork V e} {τ : Fin 4 → V}
    (h : N.Local τ) (k : M.Local τ) : (N.kron M).Local τ := by
  have b := (silent_local h).kron (silent_local k)
  refine ⟨?_,?_,fun i a x y hxy => ?_⟩
  · rintro (s|s) l
    · exact b.1 (.inl s) l
    · exact b.1 (.inr s) l
  · rintro (s|s) l
    · exact b.2.1 (.inl s) l
    · exact b.2.1 (.inr s) l
  exact congrArg₂ (· * ·) (h.2.2 i _ _ _ (fun s hs => hxy (.inl s) hs))
    (k.2.2 i _ _ _ (fun s hs => hxy (.inr s) hs))

theorem tensor_kron (N : FourNetwork V d) (M : FourNetwork V e) :
    (N.kron M).tensor = kroneckerTensor N.tensor M.tensor := by
  funext a
  have h := congrFun (congrFun (congrFun (N.packed.Z_kron M.packed)
    (kronLeftIndex a,kronRightIndex a)) ((),())) ((),())
  refine Eq.trans ?_ h
  unfold tensor TN.Z
  apply Finset.sum_congr rfl
  intro x _
  simp only [packed,kron,TN.kron,Finset.prod_mul_distrib,mul_one,one_mul]
  rfl

lemma r_pos {N : FourNetwork V d} (h : N.tensor ≠ 0) (k : N.graph.K) : 0 < N.graph.r k := by
  by_contra! h0
  have hz := N.packed.Z_eq_zero_of_r (k := k) (Nat.eq_zero_of_le_zero h0)
  exact h (by funext x; exact congrFun (congrFun (congrFun hz x) ()) ())

end FourNetwork

end OM.NNN32
