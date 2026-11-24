import Lib.OM.NNN34.BlockNetworks
import Lib.OM.NNN32.InsertionBill

/-! # A cut context with four separate row ports and one shared contraction index -/

noncomputable section
open scoped Classical

namespace OM.NNN34.RowNetwork

open NNN32 NNN32.CutContext OM.NNN30.Net Semicontinuity

variable {V A B : Type} {f : Fin 4 → ℕ+} {D : ℕ+} {r s : ℕ}
variable [Fintype A] [Fintype B] (C : CutContext V f A B)
variable (p : A ↪ Index D × Fin r) (q : B ↪ Index D × Fin s)
variable (ports : Fin 4 → V) (o : V)

private abbrev vars := C.net.graph.V ⊕ (Fin 4 ⊕ (Fin 4 ⊕ Unit))
private abbrev ty : vars C → Type :=
  Sum.elim C.net.graph.T (Sum.elim (registers A B) (fun _ => Index D))
private abbrev env := (v : vars C) → ty (D := D) C v
private abbrev old (x : env (D := D) C) : assignments C.net := fun i => x (.inl i)
private abbrev ends (x : env (D := D) C) : C.labels := fun i => x (.inr (.inl i))
private abbrev atPort (x : env (D := D) C) (i : Fin 4) : Index D := x (.inr (.inr (.inl i)))
private abbrev shared (x : env (D := D) C) : Index D := x (.inr (.inr (.inr ())))
private abbrev bonds := C.net.graph.K ⊕ (Fin 4 ⊕ Fin 2)
private def width : bonds C → ℕ := Sum.elim C.net.graph.r (Sum.elim (fun _ => D) ![r,s])

private def first : (k : bonds C) → Fin (width (r := r) (s := s) (D := D) C k) → env (D := D) C → ℂ
  | .inl k,z,x => C.net.graph.g k z (old C x)
  | .inr (.inl i),z,x => if channel p q i (ends C x i) = z then C.half i (ends C x i) (old C x) else 0
  | .inr (.inr 0),z,x => if (p (ends C x 0)).2=z then 1 else 0
  | .inr (.inr 1),z,x => if (q (ends C x 1)).2=z then 1 else 0

private def second : (k : bonds C) → Fin (width (r := r) (s := s) (D := D) C k) → env (D := D) C → ℂ
  | .inl k,z,x => C.net.graph.h k z (old C x)
  | .inr (.inl i),z,x => if atPort C x i=z then 1 else 0
  | .inr (.inr 0),z,x => if (p (ends C x 3)).2=z then 1 else 0
  | .inr (.inr 1),z,x => if (q (ends C x 2)).2=z then 1 else 0

def network : FourNetwork V f where
  graph := {
    V := vars C
    T := ty (D := D) C
    fT := fun z => match z with
      | .inl k => C.net.graph.fT k
      | .inr (.inl i) => regFinite i
      | .inr (.inr _) => inferInstanceAs (Fintype (Index D))
    loc := Sum.elim C.net.graph.loc (Sum.elim C.sites (Sum.elim ports (fun _ => o)))
    K := bonds C
    e1 := Sum.elim C.net.graph.e1 (Sum.elim C.sites ![C.sites 0,C.sites 1])
    e2 := Sum.elim C.net.graph.e2 (Sum.elim ports ![C.sites 3,C.sites 2])
    r := width (r := r) (s := s) (D := D) C
    g := first C p q
    h := second C p q
    out0 := fun _ _ => 1
    out1 := fun _ _ => 1
    out2 := fun _ _ => 1 }
  out i x a := C.net.out i (old C x) a

lemma network_local {τ} (hl : C.Local τ) : (network C p q ports o).Local τ := by
  refine ⟨?_,?_,fun i a x y he => hl.1.2.2 i a _ _ (fun z hz => he (.inl z) hz)⟩
  · rintro (k | i | j) z x y he
    · exact hl.1.1 k z _ _ fun v hv => he (.inl v) hv
    · have h : ends C x i = ends C y i := he (.inr (.inl i)) rfl
      change (if channel p q i (ends C x i) = z then C.half i _ _ else 0) = _
      rw [h,hl.2 i (ends C y i) (old C x) (old C y) (fun k hk => he (.inl k) hk)]
      rfl
    · fin_cases j
      · exact congrArg (fun l => if (p l).2=z then (1:ℂ) else 0) (he (.inr (.inl 0)) rfl)
      · exact congrArg (fun l => if (q l).2=z then (1:ℂ) else 0) (he (.inr (.inl 1)) rfl)
  · rintro (k | i | j) z x y he
    · exact hl.1.2.1 k z _ _ fun v hv => he (.inl v) hv
    · exact congrArg (fun b => if b=z then (1:ℂ) else 0) (he (.inr (.inr (.inl i))) rfl)
    · fin_cases j
      · exact congrArg (fun l => if (p l).2=z then (1:ℂ) else 0) (he (.inr (.inl 3)) rfl)
      · exact congrArg (fun l => if (q l).2=z then (1:ℂ) else 0) (he (.inr (.inl 2)) rfl)

lemma network_cost (d : V → V → ℝ) : (network C p q ports o).graph.cost d =
    C.net.graph.cost d + (∑ i, d (C.sites i) (ports i))*Real.logb 2 (D:ℕ) +
      d (C.sites 0) (C.sites 3)*Real.logb 2 r + d (C.sites 1) (C.sites 2)*Real.logb 2 s := by
  unfold TN.cost
  simp only [network,width,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,Fin.sum_univ_two]
  simp [Finset.sum_mul]
  ring

def locations : Fin 2 → Fin 3 → V := ![![ports 0,ports 1,o], ![ports 3,ports 2,o]]

def readIndex : Reads (network C p q ports o) (m := 2) (fun _ _ => D) := fun j i x =>
  ![![atPort C x 0,atPort C x 1,shared C x], ![atPort C x 3,atPort C x 2,shared C x]] j i

lemma read_local (j i) : (network C p q ports o).graph.DepAt (locations ports o j i)
    (readIndex C p q ports o j i) := by
  intro x y h
  fin_cases j <;> fin_cases i
  · exact h (.inr (.inr (.inl 0))) rfl
  · exact h (.inr (.inr (.inl 1))) rfl
  · exact h (.inr (.inr (.inr ()))) rfl
  · exact h (.inr (.inr (.inl 3))) rfl
  · exact h (.inr (.inr (.inl 2))) rfl
  · exact h (.inr (.inr (.inr ()))) rfl

private lemma link {n : ℕ} (x y : Fin n) (w : ℂ) :
    (∑ z, (if x=z then w else 0) * (if y=z then 1 else 0)) = if x=y then w else 0 := by
  simp [mul_ite]

theorem insert_eq (L N : KTensor ℂ (fun _ : Fin 3 => D)) (R : Four D)
    (contract : ∀ h, R h = ∑ j, L ![h 0,h 1,j] * N ![h 3,h 2,j]) :
    insertCubes (network C p q ports o) (m := 2) (d := fun _ _ => D) ![L,N] (readIndex C p q ports o) =
      C.insert p q R := by
  let M := network C p q ports o
  letI : Fintype (env (D := D) C) := inferInstanceAs (Fintype (Env M))
  let E : env (D := D) C ≃ assignments C.net × (C.labels × ((Fin 4 → Index D) × Index D)) := {
    toFun := fun x => (old C x,ends C x,atPort C x,shared C x)
    invFun := fun z v => match v with
      | .inl k => z.1 k
      | .inr (.inl i) => z.2.1 i
      | .inr (.inr (.inl i)) => z.2.2.1 i
      | .inr (.inr (.inr _)) => z.2.2.2
    left_inv := by intro x; funext v; rcases v with k | i | j | ⟨⟩ <;> rfl
    right_inv := fun _ => rfl }
  funext a
  let inner (x : assignments C.net) (c : C.labels) (h : Fin 4 → Index D) (j : Index D) :=
    if common p q c = h then C.exterior x a * ((∏ i,C.half i (c i) x)*residual p q c) *
      (L ![h 0,h 1,j]*N ![h 3,h 2,j]) else 0
  have expn : insertCubes M (d := fun (_ : Fin 2) _ => D) ![L,N] (readIndex C p q ports o) a =
      ∑ z : assignments C.net × (C.labels × ((Fin 4 → Index D) × Index D)),
        inner z.1 z.2.1 z.2.2.1 z.2.2.2 := by
    apply Fintype.sum_equiv E
    intro x
    let c := ends C x
    let h := atPort C x
    have leaf i : M.graph.F (.inr (.inl i)) x =
        if common p q c i = h i then C.half i (c i) (old C x) else 0 := link _ _ _
    have leaves : (∏ i, M.graph.F (.inr (.inl i)) x) =
        if common p q c = h then ∏ i,C.half i (c i) (old C x) else 0 := by
      simp_rw [leaf]
      by_cases he : common p q c=h
      · simp [he]
      · obtain ⟨i,hi⟩ : ∃ i, common p q c i ≠ h i := by by_contra! hh; exact he (funext hh)
        rw [if_neg he,Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)]
    have res0 : M.graph.F (.inr (.inr 0)) x = if (p (c 0)).2=(p (c 3)).2 then 1 else 0 := link _ _ _
    have res1 : M.graph.F (.inr (.inr 1)) x = if (q (c 1)).2=(q (c 2)).2 then 1 else 0 := link _ _ _
    have oldF k : M.graph.F (.inl k) x = C.net.graph.F k (old C x) := rfl
    have bonds_eq : (∏ k, M.graph.F k x) = (∏ k : C.net.graph.K, M.graph.F (.inl k) x) *
        (∏ z : Fin 4 ⊕ Fin 2, M.graph.F (.inr z) x) := Fintype.prod_sum_type (fun k : C.net.graph.K ⊕ (Fin 4 ⊕ Fin 2) => M.graph.F k x)
    change (∏ i,C.net.out i (old C x) (a i)) * (∏ k, M.graph.F k x) *
      (∏ j : Fin 2, _ ) = inner (old C x) c h (shared C x)
    rw [bonds_eq,Fintype.prod_sum_type,Fin.prod_univ_two,leaves,res0,res1,Fin.prod_univ_two]
    change _ * (L ![h 0,h 1,shared C x]*N ![h 3,h 2,shared C x]) = _
    simp only [oldF,inner,exterior,CutContext.residual]
    split_ifs <;> ring
  rw [expn,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl; intro x _
  rw [Fintype.sum_prod_type,Finset.mul_sum]
  apply Finset.sum_congr rfl; intro c _
  rw [Fintype.sum_prod_type,contract]
  simp [inner,Finset.mul_sum,mul_assoc]

end OM.NNN34.RowNetwork
