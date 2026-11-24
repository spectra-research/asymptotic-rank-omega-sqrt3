import Lib.OM.NNN30.Net.Cube

/-! # A four-site network in coordinates

Group the variables by site and the factors by ordered pair of ends. Each off-diagonal pair of
sites then has one index for all the wires running between them in either direction. Summing over
the fourth site leaves a tensor on the three terminal configurations. Its star part is a
restriction of the array at the fourth site, and its other three factors are two-terminal kernels. -/

noncomputable section
open scoped BigOperators Classical

namespace OM.NNN30.Net.TN

open CoordinateTensor OM.NNN.Raw

variable {O₀ O₁ O₂ : Type} (N : TN (Fin 4) O₀ O₁ O₂)

abbrev Assignment := (v : N.V) → N.T v
abbrev Config (s : Fin 4) := (v : {v : N.V // N.loc v = s}) → N.T v.val
abbrev Wires (s t : Fin 4) := {k : N.K // (N.e1 k, N.e2 k) = (s, t)}
abbrev Label (s t : Fin 4) := (k : N.Wires s t) → Fin (N.r k.val)
abbrev BondIndex (s t : Fin 4) := N.Label s t × N.Label t s

def atSite (x : N.Assignment) (s : Fin 4) : N.Config s := fun v => x v.val

/-- Complete a single site's configuration using the fixed assignment elsewhere. -/
def fill (u : N.Assignment) (s : Fin 4) (a : N.Config s) : N.Assignment :=
  fun v => if h : N.loc v = s then a ⟨v, h⟩ else u v

lemma DepAt.fill {α : Type*} {s : Fin 4} {f : N.Assignment → α} (hf : N.DepAt s f)
    (u x : N.Assignment) : f x = f (N.fill u s (N.atSite x s)) :=
  hf _ _ fun v hv => by simp [TN.fill, atSite, hv]

variable (u : N.Assignment)

def leftHalf (s t : Fin 4) (a : N.Config s) (i : N.Label s t) : ℂ :=
  ∏ k, N.g k.val (i k) (N.fill u s a)

def rightHalf (s t : Fin 4) (b : N.Config t) (i : N.Label s t) : ℂ :=
  ∏ k, N.h k.val (i k) (N.fill u t b)

def directed (s t : Fin 4) (a : N.Config s) (b : N.Config t) : ℂ :=
  ∑ i, N.leftHalf u s t a i * N.rightHalf u s t b i

def edge (s t : Fin 4) (a : N.Config s) (b : N.Config t) : ℂ :=
  N.directed u s t a b * N.directed u t s b a

def leftEnd (s t : Fin 4) (a : N.Config s) (i : N.BondIndex s t) : ℂ :=
  N.leftHalf u s t a i.1 * N.rightHalf u t s a i.2

def rightEnd (s t : Fin 4) (b : N.Config t) (i : N.BondIndex s t) : ℂ :=
  N.rightHalf u s t b i.1 * N.leftHalf u t s b i.2

lemma edge_eq (s t : Fin 4) (a : N.Config s) (b : N.Config t) :
    N.edge u s t a b = ∑ i, N.leftEnd u s t a i * N.rightEnd u s t b i := by
  rw [edge, directed, directed, Finset.sum_mul_sum, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  dsimp only [leftEnd, rightEnd]
  ring

lemma prod_directed (hN : N.Local Fin.castSucc) (x : N.Assignment) :
    ∏ k, N.F k x = ∏ s, ∏ t, N.directed u s t (N.atSite x s) (N.atSite x t) := by
  rw [← Fintype.prod_fiberwise (fun k => (N.e1 k, N.e2 k)) (fun k => N.F k x),
    Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun s _ => Finset.prod_congr rfl fun t _ => ?_
  change (∏ k : N.Wires s t, ∑ i, N.g k.val i x * N.h k.val i x) = _
  rw [Fintype.prod_sum, directed]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [leftHalf, rightHalf, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  have hg := hN.1 k.val (i k)
  have hh := hN.2.1 k.val (i k)
  rw [show N.e1 k.val = s from congrArg Prod.fst k.property] at hg
  rw [show N.e2 k.val = t from congrArg Prod.snd k.property] at hh
  rw [hg.fill N u x, hh.fill N u x]

private def tupleEquiv (A : Fin 4 → Type) : ((s : Fin 4) → A s) ≃ (A 0 × A 1 × A 2 × A 3) where
  toFun a := (a 0, a 1, a 2, a 3)
  invFun a
    | 0 => a.1
    | 1 => a.2.1
    | 2 => a.2.2.1
    | 3 => a.2.2.2
  left_inv a := by funext s; fin_cases s <;> rfl
  right_inv _ := rfl

private theorem sum_configs (f : N.Assignment → ℂ)
    (g : N.Config 0 → N.Config 1 → N.Config 2 → N.Config 3 → ℂ)
    (hf : ∀ x, f x = g (N.atSite x 0) (N.atSite x 1) (N.atSite x 2) (N.atSite x 3)) :
    ∑ x, f x = ∑ a, ∑ b, ∑ c, ∑ d, g a b c d := by
  let e : N.Assignment ≃ ((s : Fin 4) → N.Config s) :=
    Equiv.piCongrFiberwise (f := N.loc) (fun _ => Equiv.refl _)
  calc
    _ = ∑ q : N.Config 0 × N.Config 1 × N.Config 2 × N.Config 3,
        g q.1 q.2.1 q.2.2.1 q.2.2.2 :=
      Fintype.sum_equiv (e.trans (tupleEquiv N.Config)) _ _ (fun x => hf x)
    _ = _ := by simp only [Fintype.sum_prod_type]

/-- Contraction of the three centre-to-terminal kernels. -/
def starTensor : Tensor ℂ (N.Config 0) (N.Config 1) (N.Config 2) := fun a b c =>
  ∑ d, N.directed u 3 3 d d * N.edge u 0 3 a d * N.edge u 1 3 b d * N.edge u 2 3 c d

def terminalTensor : Tensor ℂ (N.Config 0) (N.Config 1) (N.Config 2) := fun a b c =>
  N.starTensor u a b c * N.edge u 0 1 a b * N.edge u 0 2 a c * N.edge u 1 2 b c

lemma Z_four_sites (hN : N.Local Fin.castSucc) :
    N.Z = mapTensor
      (fun o a => N.out0 (N.fill u 0 a) o * N.directed u 0 0 a a)
      (fun o b => N.out1 (N.fill u 1 b) o * N.directed u 1 1 b b)
      (fun o c => N.out2 (N.fill u 2 c) o * N.directed u 2 2 c c) (N.terminalTensor u) := by
  funext o p q
  simp only [Z, mapTensor, terminalTensor, starTensor, Finset.sum_mul, Finset.mul_sum]
  apply N.sum_configs
  intro x
  have h0 : N.DepAt 0 (fun x => N.out0 x o) := hN.2.2.1 o
  have h1 : N.DepAt 1 (fun x => N.out1 x p) := hN.2.2.2.1 p
  have h2 : N.DepAt 2 (fun x => N.out2 x q) := hN.2.2.2.2 q
  rw [N.prod_directed u hN x]
  simp only [Fin.prod_univ_four, edge]
  rw [show N.out0 x o = _ from h0.fill N u x, show N.out1 x p = _ from h1.fill N u x,
    show N.out2 x q = _ from h2.fill N u x]
  ring

/-- The unrestricted coefficient array at the centre. -/
def hub : Tensor ℂ (N.BondIndex 0 3) (N.BondIndex 1 3) (N.BondIndex 2 3) := fun i j k =>
  ∑ d, N.directed u 3 3 d d * N.rightEnd u 0 3 d i *
    N.rightEnd u 1 3 d j * N.rightEnd u 2 3 d k

lemma starTensor_eq_map :
    N.starTensor u = mapTensor (N.leftEnd u 0 3) (N.leftEnd u 1 3) (N.leftEnd u 2 3) (N.hub u) := by
  funext a b c
  simp only [starTensor, N.edge_eq, hub, mapTensor, Finset.sum_mul, Finset.mul_sum]
  conv_lhs =>
    rw [Finset.sum_comm]
    arg 2; ext i
    rw [Finset.sum_comm]
    arg 2; ext j
    rw [Finset.sum_comm]
  conv_lhs =>
    rw [Finset.sum_comm]
    arg 2; ext j
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro d _
  ring

end OM.NNN30.Net.TN
