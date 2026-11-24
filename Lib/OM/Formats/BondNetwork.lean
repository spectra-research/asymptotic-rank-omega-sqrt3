import Lib.OM.Formats.TwoBonds
import Lib.OM.Formats.Insertion

/-! # A network implementing a factorization across either crossing cut -/

noncomputable section
open scoped Classical
namespace OM.Formats.BondNetwork

open NNN32 NNN30.Net NNN34 Semicontinuity TwoBonds Foundations.HyperbolicLift

variable {V A B : Type} [Fintype A] [Fintype B] {f : Fin 4 → ℕ+} {D E J : ℕ+} {r s : ℕ}
variable (C : CutContext V f A B) (p : A ↪ Index D × Fin r) (q : B ↪ Index E × Fin s)
variable (flip : Bool) (R : Fin (J:ℕ) → Index E → Index D → ℂ)
variable (ports : Fin 4 → V) (o v : V)

private abbrev Vars := C.net.graph.V ⊕ (Fin 4 ⊕ (Fin 4 ⊕ Unit))
private abbrev Ty : Vars C → Type :=
  Sum.elim C.net.graph.T (Sum.elim (registers A B)
    (Sum.elim (fun i => Fin (ends D E i)) (fun _ => Fin (J:ℕ))))
private abbrev Assignment := (i : Vars C) → Ty (D := D) (E := E) (J := J) C i
private abbrev old (x : Assignment (D := D) (E := E) (J := J) C) : assignments C.net :=
  fun i => x (.inl i)
private abbrev regs (x : Assignment (D := D) (E := E) (J := J) C) : C.labels :=
  fun i => x (.inr (.inl i))
private abbrev atPort (x : Assignment (D := D) (E := E) (J := J) C) : Channels D E :=
  fun i => x (.inr (.inr (.inl i)))
private abbrev shared (x : Assignment (D := D) (E := E) (J := J) C) : Fin (J:ℕ) :=
  x (.inr (.inr (.inr ())))
private abbrev Bonds := C.net.graph.K ⊕ (Fin 4 ⊕ Fin 3)
private def width : Bonds C → ℕ := Sum.elim C.net.graph.r (Sum.elim (fun i => (ends D E i : ℕ)) ![r,s,(J:ℕ)])

private def first : (k : Bonds C) → Fin (width (D := D) (E := E) (J := J) (r := r) (s := s) C k) →
    Assignment (D := D) (E := E) (J := J) C → ℂ
  | .inl k,z,x => C.net.graph.g k z (old C x)
  | .inr (.inl i),z,x => if channel p q i (regs C x i) = z then C.half i (regs C x i) (old C x) else 0
  | .inr (.inr 0),z,x => if (p (regs C x 0)).2=z then 1 else 0
  | .inr (.inr 1),z,x => if (q (regs C x 1)).2=z then 1 else 0
  | .inr (.inr 2),z,x => if shared C x=z then 1 else 0

private def second : (k : Bonds C) → Fin (width (D := D) (E := E) (J := J) (r := r) (s := s) C k) →
    Assignment (D := D) (E := E) (J := J) C → ℂ
  | .inl k,z,x => C.net.graph.h k z (old C x)
  | .inr (.inl i),z,x => if atPort C x i=z then 1 else 0
  | .inr (.inr 0),z,x => if (p (regs C x 3)).2=z then 1 else 0
  | .inr (.inr 1),z,x => if (q (regs C x 2)).2=z then 1 else 0
  | .inr (.inr 2),z,x => R z (if flip then atPort C x 1 else atPort C x 2) (atPort C x 3)

def network : FourNetwork V f where
  graph := {
    V := Vars C
    T := Ty (D := D) (E := E) (J := J) C
    fT := fun a => match a with
      | .inl k => C.net.graph.fT k
      | .inr (.inl i) => CutContext.regFinite i
      | .inr (.inr (.inl i)) => inferInstanceAs (Fintype (Fin (ends D E i)))
      | .inr (.inr (.inr _)) => inferInstanceAs (Fintype (Fin (J:ℕ)))
    loc := Sum.elim C.net.graph.loc (Sum.elim C.sites (Sum.elim ports (fun _ => o)))
    K := Bonds C
    e1 := Sum.elim C.net.graph.e1 (Sum.elim C.sites ![C.sites 0,C.sites 1,o])
    e2 := Sum.elim C.net.graph.e2 (Sum.elim ports ![C.sites 3,C.sites 2,v])
    r := width (D := D) (E := E) (J := J) (r := r) (s := s) C
    g := first C p q
    h := second C p q flip R
    out0 := fun _ _ => 1
    out1 := fun _ _ => 1
    out2 := fun _ _ => 1 }
  out i x a := C.net.out i (old C x) a

theorem local_net {τ} (hl : C.Local τ) (h₃ : ports 3 = v)
    (hE : (if flip then ports 1 else ports 2) = v) : (network C p q flip R ports o v).Local τ := by
  refine ⟨?_,?_,fun i a x y h => hl.1.2.2 i a _ _ (fun z hz => h (.inl z) hz)⟩
  · rintro (k | i | j) z x y h
    · exact hl.1.1 k z _ _ fun w hw => h (.inl w) hw
    · have e : regs C x i = regs C y i := h (.inr (.inl i)) rfl
      change (if channel p q i (regs C x i) = z then C.half i _ _ else 0) = _
      rw [e,hl.2 i (regs C y i) (old C x) (old C y) (fun k hk => h (.inl k) hk)]
      rfl
    · fin_cases j
      · exact congrArg (fun l => if (p l).2=z then (1:ℂ) else 0) (h (.inr (.inl 0)) rfl)
      · exact congrArg (fun l => if (q l).2=z then (1:ℂ) else 0) (h (.inr (.inl 1)) rfl)
      · exact congrArg (fun l => if l=z then (1:ℂ) else 0) (h (.inr (.inr (.inr ()))) rfl)
  · rintro (k | i | j) z x y h
    · exact hl.1.2.1 k z _ _ fun w hw => h (.inl w) hw
    · exact congrArg (fun b => if b=z then (1:ℂ) else 0) (h (.inr (.inr (.inl i))) rfl)
    · fin_cases j
      · exact congrArg (fun l => if (p l).2=z then (1:ℂ) else 0) (h (.inr (.inl 3)) rfl)
      · exact congrArg (fun l => if (q l).2=z then (1:ℂ) else 0) (h (.inr (.inl 2)) rfl)
      · cases flip <;> exact congrArg₂ (R z) (h (.inr (.inr (.inl _))) hE) (h (.inr (.inr (.inl 3))) h₃)

theorem cost (d : V → V → ℝ) : (network C p q flip R ports o v).graph.cost d =
    C.net.graph.cost d + ∑ i, d (C.sites i) (ports i)*Real.logb 2 (ends D E i : ℕ) +
      (d (C.sites 0) (C.sites 3)*Real.logb 2 r + d (C.sites 1) (C.sites 2)*Real.logb 2 s +
       d o v*Real.logb 2 (J:ℕ)) := by
  unfold TN.cost
  simp only [network,width,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,Fin.sum_univ_three]
  simp; ring

abbrev leftSite : Fin 3 → V := ![ports 0, if flip then ports 2 else ports 1, o]

def read (i : Fin 3) (x : Env (network C p q flip R ports o v)) : Fin (PolMul.fmt D E J i) :=
  match i with
  | 0 => atPort C x 0
  | 1 => if flip then atPort C x 2 else atPort C x 1
  | 2 => shared C x

theorem read_local (i : Fin 3) : (network C p q flip R ports o v).graph.DepAt (leftSite flip ports o i)
    (read C p q flip R ports o v i) := by
  intro x y h
  fin_cases i
  · exact h (.inr (.inr (.inl 0))) rfl
  · cases flip <;> exact h (.inr (.inr (.inl _))) rfl
  · exact h (.inr (.inr (.inr ()))) rfl

private lemma link {n : ℕ} (x y : Fin n) (w : ℂ) :
    (∑ z, (if x=z then w else 0) * (if y=z then 1 else 0)) = if x=y then w else 0 := by
  simp [mul_ite]

theorem evaluate (L : KTensor ℂ (PolMul.fmt D E J)) (P : Piece D E)
    (hP : ∀ (h : Channels D E), P (h 0) (h 1) (h 2) (h 3) =
      ∑ j, L (idx3 (h 0) (if flip then h 2 else h 1) j) * R j (if flip then h 1 else h 2) (h 3)) :
    let M := network C p q flip R ports o v
    (fun a => ∑ x : Env M, (∏ i, M.out i x (a i)) * (∏ k, M.graph.F k x) *
      L (fun i => read C p q flip R ports o v i x)) = insert C p q P := by
  intro M
  let : Fintype (Assignment (D := D) (E := E) (J := J) C) := inferInstanceAs (Fintype (Env M))
  let Equ : Env M ≃ assignments C.net × (C.labels × (Channels D E × Index J)) := {
    toFun := fun x => (old C x,regs C x,atPort C x,shared C x)
    invFun := fun z w => match w with
      | .inl k => z.1 k
      | .inr (.inl i) => z.2.1 i
      | .inr (.inr (.inl i)) => z.2.2.1 i
      | .inr (.inr (.inr _)) => z.2.2.2
    left_inv := by intro x; funext w; rcases w with k | i | j | ⟨⟩ <;> rfl
    right_inv := fun _ => rfl }
  funext a
  let inner (x : assignments C.net) (c : C.labels) (h : Channels D E) (j : Index J) :=
    if wires C p q c = h then C.exterior x a * ((∏ i, C.half i (c i) x)*rest C p q c) *
      (L (idx3 (h 0) (if flip then h 2 else h 1) j) * R j (if flip then h 1 else h 2) (h 3)) else 0
  have expn : (∑ x : Env M, (∏ i, M.out i x (a i)) * (∏ k, M.graph.F k x) *
      L (fun i => read C p q flip R ports o v i x)) =
      ∑ z : assignments C.net × (C.labels × (Channels D E × Index J)),
        inner z.1 z.2.1 z.2.2.1 z.2.2.2 := by
    apply Fintype.sum_equiv Equ
    intro x
    let c := regs C x
    let h := atPort C x
    have leaf i : M.graph.F (.inr (.inl i)) x =
        if wires C p q c i = h i then C.half i (c i) (old C x) else 0 := link _ _ _
    have leaves : (∏ i, M.graph.F (.inr (.inl i)) x) =
        if wires C p q c = h then ∏ i,C.half i (c i) (old C x) else 0 := by
      simp_rw [leaf]
      by_cases he : wires C p q c = h
      · simp [he]
      · obtain ⟨i,hi⟩ : ∃ i, wires C p q c i ≠ h i := by
          by_contra! hh; exact he (funext hh)
        rw [ite_eq_right he,Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)]
    have res0 : M.graph.F (.inr (.inr 0)) x = if (p (c 0)).2=(p (c 3)).2 then 1 else 0 := link _ _ _
    have res1 : M.graph.F (.inr (.inr 1)) x = if (q (c 1)).2=(q (c 2)).2 then 1 else 0 := link _ _ _
    have factor : M.graph.F (.inr (.inr 2)) x = R (shared C x) (if flip then h 1 else h 2) (h 3) := by
      change (∑ j, (if shared C x = j then (1:ℂ) else 0) * R j _ _) = _
      simp [ite_mul, h]
    have oldF k : M.graph.F (.inl k) x = C.net.graph.F k (old C x) := rfl
    have bonds_eq : (∏ k, M.graph.F k x) = (∏ k : C.net.graph.K, M.graph.F (.inl k) x) *
        (∏ z : Fin 4 ⊕ Fin 3, M.graph.F (.inr z) x) := Fintype.prod_sum_type (fun k : C.net.graph.K ⊕ (Fin 4 ⊕ Fin 3) => M.graph.F k x)
    have hread : (fun i => read C p q flip R ports o v i x) =
        idx3 (d := PolMul.fmt D E J) (h 0) (if flip then h 2 else h 1) (shared (D:=D) (E:=E) (J:=J) C x) := by funext i; fin_cases i <;> rfl
    change (∏ i,C.net.out i (old C x) (a i)) * (∏ k, M.graph.F k x) * L _ = inner (old C x) c h (shared C x)
    rw [bonds_eq,Fintype.prod_sum_type,Fin.prod_univ_three,leaves,res0,res1,factor,hread]
    simp only [oldF,inner,CutContext.exterior,rest]
    split_ifs <;> ring
  change (∑ x : Env M, _) = _
  rw [expn,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl; intro x _
  rw [Fintype.sum_prod_type,Finset.mul_sum]
  apply Finset.sum_congr rfl; intro c _
  rw [Fintype.sum_prod_type]
  change _ = _ * (_ * P (wires C p q c 0) (wires C p q c 1) (wires C p q c 2) (wires C p q c 3))
  rw [hP]
  simp [inner,Finset.mul_sum,mul_assoc]
  rfl

end OM.Formats.BondNetwork
