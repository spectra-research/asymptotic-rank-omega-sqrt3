import Lib.OM.NNN22.F

/-! # Networks on sites: definitions, relocation, Kronecker products

A network on the site type `S` has variables `V` (each with a finite type `T v` and a site `loc v`)
and factors `K`; factor `k` joins the sites `e1 k`, `e2 k` and is given with a decomposition
`Σ_{i < r k} g k i · h k i`, where `g k i` reads only the variables at `e1 k` and `h k i` only the
variables at `e2 k` (locality, `Local`).  Three output factors `out_j` sit at the terminals.  The
output `Z` sums the product of all factors over the variables.  The cost at prices `d` is
`Σ_k d(e1 k, e2 k) log₂ (r k)`: a factor of decomposition size `r` between two sites is an
equality wire of dimension `r`.  Merging sites (`relocate`) changes only the
locations, so the output is unchanged by definition. -/

noncomputable section
open scoped BigOperators Classical

namespace OM.NNN30.Net

open CoordinateTensor OM.NNN.Raw

/-- A tensor network on the site type `S` with output types `O0 O1 O2`. -/
structure TN (S O0 O1 O2 : Type) where
  V : Type
  [fV : Fintype V]
  T : V → Type
  [fT : ∀ v, Fintype (T v)]
  loc : V → S
  K : Type
  [fK : Fintype K]
  e1 : K → S
  e2 : K → S
  r : K → ℕ
  g : (k : K) → Fin (r k) → ((v : V) → T v) → ℂ
  h : (k : K) → Fin (r k) → ((v : V) → T v) → ℂ
  out0 : ((v : V) → T v) → O0 → ℂ
  out1 : ((v : V) → T v) → O1 → ℂ
  out2 : ((v : V) → T v) → O2 → ℂ

attribute [instance] TN.fV TN.fT TN.fK

namespace TN

variable {S S' O0 O1 O2 P0 P1 P2 : Type}

/-- the factor `k` -/
def F (N : TN S O0 O1 O2) (k : N.K) (x : (v : N.V) → N.T v) : ℂ :=
  ∑ i, N.g k i x * N.h k i x

/-- the output tensor -/
def Z (N : TN S O0 O1 O2) : Tensor ℂ O0 O1 O2 := fun a b c =>
  ∑ x : (v : N.V) → N.T v, N.out0 x a * N.out1 x b * N.out2 x c * ∏ k, N.F k x

/-- `f` reads only the variables at the site `s` -/
def DepAt (N : TN S O0 O1 O2) (s : S) {α : Type*} (f : ((v : N.V) → N.T v) → α) : Prop :=
  ∀ x y : (v : N.V) → N.T v, (∀ v, N.loc v = s → x v = y v) → f x = f y

/-- locality, with terminals `τ` -/
def Local (τ : Fin 3 → S) (N : TN S O0 O1 O2) : Prop :=
  (∀ k i, N.DepAt (N.e1 k) (N.g k i)) ∧ (∀ k i, N.DepAt (N.e2 k) (N.h k i)) ∧
  (∀ a, N.DepAt (τ 0) (fun x => N.out0 x a)) ∧ (∀ b, N.DepAt (τ 1) (fun x => N.out1 x b)) ∧
  (∀ c, N.DepAt (τ 2) (fun x => N.out2 x c))

/-- the cost at prices `d` -/
def cost (d : S → S → ℝ) (N : TN S O0 O1 O2) : ℝ :=
  ∑ k, d (N.e1 k) (N.e2 k) * Real.logb 2 (N.r k)

/-- the widths: `log₂` of the total decomposition size on each ordered pair of sites -/
def wid (N : TN S O0 O1 O2) (s t : S) : ℝ :=
  ∑ k, if N.e1 k = s ∧ N.e2 k = t then Real.logb 2 (N.r k) else 0

lemma cost_eq_wid (d : S → S → ℝ) [Fintype S] (N : TN S O0 O1 O2) :
    N.cost d = ∑ s, ∑ t, d s t * N.wid s t := by
  have h : ∀ k, d (N.e1 k) (N.e2 k) * Real.logb 2 (N.r k) =
      ∑ s, ∑ t, d s t * (if N.e1 k = s ∧ N.e2 k = t then Real.logb 2 (N.r k) else 0) := by
    intro k
    rw [Finset.sum_eq_single (N.e1 k)
      (fun s _ hs => Finset.sum_eq_zero fun t _ => by simp [Ne.symm hs]) (by simp)]
    rw [Finset.sum_eq_single (N.e2 k) (fun t _ ht => by simp [Ne.symm ht]) (by simp)]
    simp
  unfold cost wid
  rw [Finset.sum_congr rfl fun k _ => h k, Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Finset.mul_sum]

/-! ## Relocation (merging sites) -/

/-- move every variable and factor end along `π` -/
def relocate (N : TN S O0 O1 O2) (π : S → S') : TN S' O0 O1 O2 where
  V := N.V
  T := N.T
  loc := π ∘ N.loc
  K := N.K
  e1 := π ∘ N.e1
  e2 := π ∘ N.e2
  r := N.r
  g := N.g
  h := N.h
  out0 := N.out0
  out1 := N.out1
  out2 := N.out2

@[simp] lemma Z_relocate (N : TN S O0 O1 O2) (π : S → S') : (N.relocate π).Z = N.Z := rfl

lemma cost_relocate (N : TN S O0 O1 O2) (π : S → S') (d : S' → S' → ℝ) :
    (N.relocate π).cost d = ∑ k, d (π (N.e1 k)) (π (N.e2 k)) * Real.logb 2 (N.r k) := rfl

lemma DepAt.relocate {N : TN S O0 O1 O2} {s : S} {α : Type*} {f : ((v : N.V) → N.T v) → α}
    (h : N.DepAt s f) (π : S → S') : (N.relocate π).DepAt (π s) f := by
  intro x y hxy
  exact h x y fun v hv => hxy v (show π (N.loc v) = π s by rw [hv])

lemma Local.relocate {τ : Fin 3 → S} {N : TN S O0 O1 O2} (hN : N.Local τ) (π : S → S')
    {τ' : Fin 3 → S'} (hτ : ∀ i, π (τ i) = τ' i) : (N.relocate π).Local τ' := by
  obtain ⟨hg, hh, h0, h1, h2⟩ := hN
  refine ⟨fun k i => (hg k i).relocate π, fun k i => (hh k i).relocate π, fun a => ?_,
    fun b => ?_, fun c => ?_⟩
  · rw [← hτ 0]; exact (h0 a).relocate π
  · rw [← hτ 1]; exact (h1 b).relocate π
  · rw [← hτ 2]; exact (h2 c).relocate π

/-! ## Kronecker products -/

/-- the Kronecker product of two networks on the same sites -/
def kron (N : TN S O0 O1 O2) (N' : TN S P0 P1 P2) : TN S (O0 × P0) (O1 × P1) (O2 × P2) where
  V := N.V ⊕ N'.V
  T := Sum.elim N.T N'.T
  fT := fun v => match v with
    | .inl v => N.fT v
    | .inr v => N'.fT v
  loc := Sum.elim N.loc N'.loc
  K := N.K ⊕ N'.K
  e1 := Sum.elim N.e1 N'.e1
  e2 := Sum.elim N.e2 N'.e2
  r := Sum.elim N.r N'.r
  g := fun k => match k with
    | .inl k => fun i x => N.g k i (fun v => x (.inl v))
    | .inr k => fun i x => N'.g k i (fun v => x (.inr v))
  h := fun k => match k with
    | .inl k => fun i x => N.h k i (fun v => x (.inl v))
    | .inr k => fun i x => N'.h k i (fun v => x (.inr v))
  out0 := fun x a => N.out0 (fun v => x (.inl v)) a.1 * N'.out0 (fun v => x (.inr v)) a.2
  out1 := fun x b => N.out1 (fun v => x (.inl v)) b.1 * N'.out1 (fun v => x (.inr v)) b.2
  out2 := fun x c => N.out2 (fun v => x (.inl v)) c.1 * N'.out2 (fun v => x (.inr v)) c.2

lemma Z_kron (N : TN S O0 O1 O2) (N' : TN S P0 P1 P2) :
    (N.kron N').Z = tensorProduct N.Z N'.Z := by
  funext a b c
  let e : ((v : (N.kron N').V) → (N.kron N').T v) ≃
      ((v : N.V) → N.T v) × ((v : N'.V) → N'.T v) := Equiv.sumPiEquivProdPi _
  show (∑ x : (v : (N.kron N').V) → (N.kron N').T v,
      (N.kron N').out0 x a * (N.kron N').out1 x b * (N.kron N').out2 x c *
        ∏ k, (N.kron N').F k x) =
    (∑ x : (v : N.V) → N.T v, N.out0 x a.1 * N.out1 x b.1 * N.out2 x c.1 * ∏ k, N.F k x) *
    (∑ x : (v : N'.V) → N'.T v, N'.out0 x a.2 * N'.out1 x b.2 * N'.out2 x c.2 * ∏ k, N'.F k x)
  rw [Finset.sum_mul_sum, ← Fintype.sum_prod_type']
  refine Fintype.sum_equiv e _ _ fun x => ?_
  have hp : (∏ k : (N.kron N').K, (N.kron N').F k x) =
      (∏ k : N.K, (N.kron N').F (.inl k) x) * ∏ k : N'.K, (N.kron N').F (.inr k) x :=
    Fintype.prod_sum_type _
  have hx1 : (e x).1 = fun v => x (.inl v) := rfl
  have hx2 : (e x).2 = fun v => x (.inr v) := rfl
  have hF1 : ∀ k, (N.kron N').F (.inl k) x = N.F k (fun v => x (.inl v)) := fun k => rfl
  have hF2 : ∀ k, (N.kron N').F (.inr k) x = N'.F k (fun v => x (.inr v)) := fun k => rfl
  have ho0 : (N.kron N').out0 x a = N.out0 (fun v => x (.inl v)) a.1 *
      N'.out0 (fun v => x (.inr v)) a.2 := rfl
  have ho1 : (N.kron N').out1 x b = N.out1 (fun v => x (.inl v)) b.1 *
      N'.out1 (fun v => x (.inr v)) b.2 := rfl
  have ho2 : (N.kron N').out2 x c = N.out2 (fun v => x (.inl v)) c.1 *
      N'.out2 (fun v => x (.inr v)) c.2 := rfl
  rw [hp, hx1, hx2, ho0, ho1, ho2]
  simp only [hF1, hF2]
  ring

lemma cost_kron (d : S → S → ℝ) (N : TN S O0 O1 O2) (N' : TN S P0 P1 P2) :
    (N.kron N').cost d = N.cost d + N'.cost d :=
  Fintype.sum_sum_type _

lemma wid_kron (N : TN S O0 O1 O2) (N' : TN S P0 P1 P2) (s t : S) :
    (N.kron N').wid s t = N.wid s t + N'.wid s t :=
  Fintype.sum_sum_type _

lemma Local.kron {τ : Fin 3 → S} {N : TN S O0 O1 O2} {N' : TN S P0 P1 P2} (hN : N.Local τ)
    (hN' : N'.Local τ) : (N.kron N').Local τ := by
  obtain ⟨hg, hh, h0, h1, h2⟩ := hN
  obtain ⟨hg', hh', h0', h1', h2'⟩ := hN'
  refine ⟨fun k i => ?_, fun k i => ?_, fun a => ?_, fun b => ?_, fun c => ?_⟩
  · rcases k with k | k
    · intro x y hxy
      exact hg k i _ _ fun v hv => hxy (.inl v) hv
    · intro x y hxy
      exact hg' k i _ _ fun v hv => hxy (.inr v) hv
  · rcases k with k | k
    · intro x y hxy
      exact hh k i _ _ fun v hv => hxy (.inl v) hv
    · intro x y hxy
      exact hh' k i _ _ fun v hv => hxy (.inr v) hv
  · intro x y hxy
    have e1 : N.out0 (fun v => x (.inl v)) a.1 = N.out0 (fun v => y (.inl v)) a.1 :=
      h0 a.1 _ _ fun v hv => hxy (.inl v) hv
    have e2 : N'.out0 (fun v => x (.inr v)) a.2 = N'.out0 (fun v => y (.inr v)) a.2 :=
      h0' a.2 _ _ fun v hv => hxy (.inr v) hv
    show N.out0 (fun v => x (.inl v)) a.1 * N'.out0 (fun v => x (.inr v)) a.2 =
      N.out0 (fun v => y (.inl v)) a.1 * N'.out0 (fun v => y (.inr v)) a.2
    rw [e1, e2]
  · intro x y hxy
    have e1 : N.out1 (fun v => x (.inl v)) b.1 = N.out1 (fun v => y (.inl v)) b.1 :=
      h1 b.1 _ _ fun v hv => hxy (.inl v) hv
    have e2 : N'.out1 (fun v => x (.inr v)) b.2 = N'.out1 (fun v => y (.inr v)) b.2 :=
      h1' b.2 _ _ fun v hv => hxy (.inr v) hv
    show N.out1 (fun v => x (.inl v)) b.1 * N'.out1 (fun v => x (.inr v)) b.2 =
      N.out1 (fun v => y (.inl v)) b.1 * N'.out1 (fun v => y (.inr v)) b.2
    rw [e1, e2]
  · intro x y hxy
    have e1 : N.out2 (fun v => x (.inl v)) c.1 = N.out2 (fun v => y (.inl v)) c.1 :=
      h2 c.1 _ _ fun v hv => hxy (.inl v) hv
    have e2 : N'.out2 (fun v => x (.inr v)) c.2 = N'.out2 (fun v => y (.inr v)) c.2 :=
      h2' c.2 _ _ fun v hv => hxy (.inr v) hv
    show N.out2 (fun v => x (.inl v)) c.1 * N'.out2 (fun v => x (.inr v)) c.2 =
      N.out2 (fun v => y (.inl v)) c.1 * N'.out2 (fun v => y (.inr v)) c.2
    rw [e1, e2]

/-- the network with no variables and no factors, output `1` -/
def one (S : Type) : TN S Unit Unit Unit where
  V := Empty
  T := Empty.elim
  fT := fun v => Empty.elim v
  loc := Empty.elim
  K := Empty
  e1 := Empty.elim
  e2 := Empty.elim
  r := Empty.elim
  g := fun k => Empty.elim k
  h := fun k => Empty.elim k
  out0 := fun _ _ => 1
  out1 := fun _ _ => 1
  out2 := fun _ _ => 1

instance (S : Type) : IsEmpty (one S).K := inferInstanceAs (IsEmpty Empty)

instance (S : Type) : IsEmpty (one S).V := inferInstanceAs (IsEmpty Empty)

lemma Z_one : (one S).Z = fun _ _ _ => 1 := by
  funext a b c
  show (∑ x : (v : Empty) → Empty.elim v, (1 : ℂ) * 1 * 1 * ∏ k : Empty, (one S).F k x) = 1
  simp

lemma Local_one (τ : Fin 3 → S) : (one S).Local τ := by
  refine ⟨fun k => Empty.elim (show Empty from k), fun k => Empty.elim (show Empty from k),
    fun _ _ _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ _ _ => rfl⟩

lemma cost_one (d : S → S → ℝ) : (one S).cost d = 0 :=
  Fintype.sum_empty _

lemma wid_one (s t : S) : (one S).wid s t = 0 :=
  Fintype.sum_empty _

/-- output types of powers -/
def PowT (O : Type) : ℕ → Type
  | 0 => Unit
  | p + 1 => PowT O p × O

instance instFintypePowT (O : Type) [Fintype O] : (p : ℕ) → Fintype (PowT O p)
  | 0 => (inferInstance : Fintype Unit)
  | p + 1 => @instFintypeProd _ _ (instFintypePowT O p) _

/-- the `p`-th Kronecker power -/
def pow (N : TN S O0 O1 O2) : (p : ℕ) → TN S (PowT O0 p) (PowT O1 p) (PowT O2 p)
  | 0 => one S
  | p + 1 => (pow N p).kron N

lemma cost_pow (d : S → S → ℝ) (N : TN S O0 O1 O2) (p : ℕ) :
    (N.pow p).cost d = p * N.cost d := by
  induction p with
  | zero =>
    have h : (N.pow 0).cost d = 0 := cost_one d
    rw [h]; simp
  | succ p ih =>
    have h : (N.pow (p + 1)).cost d = (N.pow p).cost d + N.cost d := cost_kron d (N.pow p) N
    rw [h, ih]; push_cast; ring

lemma wid_pow (N : TN S O0 O1 O2) (p : ℕ) (s t : S) : (N.pow p).wid s t = p * N.wid s t := by
  induction p with
  | zero =>
    have h : (N.pow 0).wid s t = 0 := wid_one s t
    rw [h]; simp
  | succ p ih =>
    have h : (N.pow (p + 1)).wid s t = (N.pow p).wid s t + N.wid s t := wid_kron (N.pow p) N s t
    rw [h, ih]; push_cast; ring

lemma Local.pow {τ : Fin 3 → S} {N : TN S O0 O1 O2} (hN : N.Local τ) (p : ℕ) :
    (N.pow p).Local τ := by
  induction p with
  | zero => exact Local_one τ
  | succ p ih => exact ih.kron hN

end TN

end OM.NNN30.Net
