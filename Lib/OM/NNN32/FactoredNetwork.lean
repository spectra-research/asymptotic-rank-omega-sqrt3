import Lib.OM.NNN32.CutContext

/-! # Inserting a rank factorization at two arbitrary sites -/

noncomputable section
open scoped Classical

namespace OM.NNN32

open Semicontinuity OM.NNN30.Net

structure FactorSites (V : Type) (D : ℕ+) where
  order : Equiv.Perm (Fin 4)
  u : V
  v : V
  rank : ℕ
  left : Index D × Index D → Fin rank → ℂ
  right : Fin rank → Index D × Index D → ℂ

namespace FactorSites

variable {V : Type} {D : ℕ+} (F : FactorSites V D)

def hub (i : Fin 4) := if i=F.order 0 ∨ i=F.order 1 then F.u else F.v

def kernel : Four D := fun y => ∑ z, F.left (y (F.order 0),y (F.order 1)) z *
  F.right z (y (F.order 2),y (F.order 3))

def leaves (d : V → V → ℝ) (t : Fin 4 → V) := ∑ i, d (t i) (F.hub i)

end FactorSites

namespace CutContext

variable {V A B : Type} {f : Fin 4 → ℕ+} {D : ℕ+} {r s : ℕ}
variable [Fintype A] [Fintype B] (C : CutContext V f A B)
variable (p : A ↪ Index D × Fin r) (q : B ↪ Index D × Fin s) (F : FactorSites V D)

private abbrev varType : C.net.graph.V ⊕ (Fin 4 ⊕ Fin 4) → Type :=
  Sum.elim C.net.graph.T (Sum.elim (registers A B) (fun _ => Index D))

private abbrev env := (k : C.net.graph.V ⊕ (Fin 4 ⊕ Fin 4)) → varType (D := D) C k
private abbrev old (x : env (D := D) C) : assignments C.net := fun z => x (.inl z)
private abbrev corners (x : env (D := D) C) : C.labels := fun i => x (.inr (.inl i))
private abbrev hubs (x : env (D := D) C) : Fin 4 → Index D := fun i => x (.inr (.inr i))

private def size : C.net.graph.K ⊕ (Fin 4 ⊕ Fin 3) → ℕ :=
  Sum.elim C.net.graph.r (Sum.elim (fun _ => D) ![r,s,F.rank])

private def first : (k : C.net.graph.K ⊕ (Fin 4 ⊕ Fin 3)) → Fin (size (r := r) (s := s) C F k) → env (D := D) C → ℂ
  | .inl k,z,x => C.net.graph.g k z (C.old x)
  | .inr (.inl i),z,x => if channel p q i (C.corners x i)=z then C.half i (C.corners x i) (C.old x) else 0
  | .inr (.inr 0),z,x => if (p (C.corners x 0)).2=z then 1 else 0
  | .inr (.inr 1),z,x => if (q (C.corners x 1)).2=z then 1 else 0
  | .inr (.inr 2),z,x => F.left (C.hubs x (F.order 0),C.hubs x (F.order 1)) z

private def second : (k : C.net.graph.K ⊕ (Fin 4 ⊕ Fin 3)) → Fin (size (r := r) (s := s) C F k) → env (D := D) C → ℂ
  | .inl k,z,x => C.net.graph.h k z (C.old x)
  | .inr (.inl i),z,x => if C.hubs x i=z then 1 else 0
  | .inr (.inr 0),z,x => if (p (C.corners x 3)).2=z then 1 else 0
  | .inr (.inr 1),z,x => if (q (C.corners x 2)).2=z then 1 else 0
  | .inr (.inr 2),z,x => F.right z (C.hubs x (F.order 2),C.hubs x (F.order 3))

def realize : FourNetwork V f where
  graph := {
    V := C.net.graph.V ⊕ (Fin 4 ⊕ Fin 4)
    T := C.varType (D := D)
    fT := fun z => match z with
      | .inl k => C.net.graph.fT k
      | .inr (.inl i) => regFinite i
      | .inr (.inr _) => inferInstanceAs (Fintype (Index D))
    loc := Sum.elim C.net.graph.loc (Sum.elim C.sites F.hub)
    K := C.net.graph.K ⊕ (Fin 4 ⊕ Fin 3)
    e1 := Sum.elim C.net.graph.e1 (Sum.elim C.sites ![C.sites 0,C.sites 1,F.u])
    e2 := Sum.elim C.net.graph.e2 (Sum.elim F.hub ![C.sites 3,C.sites 2,F.v])
    r := size (r := r) (s := s) C F
    g := C.first p q F
    h := C.second p q F
    out0 := fun _ _ => 1
    out1 := fun _ _ => 1
    out2 := fun _ _ => 1 }
  out i x a := C.net.out i (C.old x) a

lemma realize_local {τ : Fin 4 → V} (hl : C.Local τ) : (C.realize p q F).Local τ := by
  have fu (i : Fin 4) (h : i=0 ∨ i=1) : F.hub (F.order i) = F.u := by
    rcases h with rfl | rfl <;> simp [FactorSites.hub]
  have fv (i : Fin 4) (h : i=2 ∨ i=3) : F.hub (F.order i) = F.v := by
    rcases h with rfl | rfl <;> simp [FactorSites.hub]
  refine ⟨?_,?_,fun i a x y he => hl.1.2.2 i a _ _ (fun z hz => he (.inl z) hz)⟩
  · rintro (k|i|j) z x y he
    · exact hl.1.1 k z _ _ (fun v hv => he (.inl v) hv)
    · have h : C.corners x i = C.corners y i := he (.inr (.inl i)) rfl
      change (if channel p q i (C.corners x i) = z then C.half i _ _ else 0) = _
      rw [h,hl.2 i (C.corners y i) (C.old x) (C.old y) (fun k hk => he (.inl k) hk)]
      rfl
    · fin_cases j
      · exact congrArg (fun l => if (p l).2=z then (1:ℂ) else 0) (he (.inr (.inl 0)) rfl)
      · exact congrArg (fun l => if (q l).2=z then (1:ℂ) else 0) (he (.inr (.inl 1)) rfl)
      · exact congrArg (fun l => F.left l z) (Prod.ext
          (he (.inr (.inr (F.order 0))) (fu 0 (Or.inl rfl)))
          (he (.inr (.inr (F.order 1))) (fu 1 (Or.inr rfl))))
  · rintro (k|i|j) z x y he
    · exact hl.1.2.1 k z _ _ (fun v hv => he (.inl v) hv)
    · exact congrArg (fun l => if l=z then (1:ℂ) else 0) (he (.inr (.inr i)) rfl)
    · fin_cases j
      · exact congrArg (fun l => if (p l).2=z then (1:ℂ) else 0) (he (.inr (.inl 3)) rfl)
      · exact congrArg (fun l => if (q l).2=z then (1:ℂ) else 0) (he (.inr (.inl 2)) rfl)
      · exact congrArg (F.right z) (Prod.ext
          (he (.inr (.inr (F.order 2))) (fv 2 (Or.inl rfl)))
          (he (.inr (.inr (F.order 3))) (fv 3 (Or.inr rfl))))

lemma realize_cost (d : V → V → ℝ) : (C.realize p q F).graph.cost d =
    C.net.graph.cost d + F.leaves d C.sites * Real.logb 2 (D:ℕ) +
      d (C.sites 0) (C.sites 3) * Real.logb 2 r + d (C.sites 1) (C.sites 2) * Real.logb 2 s +
      d F.u F.v * Real.logb 2 F.rank := by
  unfold TN.cost
  simp only [realize,size,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,Fin.sum_univ_three]
  simp [FactorSites.leaves,Finset.sum_mul]
  ring

private lemma link {n : ℕ} (x y : Fin n) (w : ℂ) :
    (∑ z, (if x=z then w else 0)*(if y=z then 1 else 0)) = if x=y then w else 0 := by
  rw [Finset.sum_eq_single x]
  · by_cases h : x=y <;> simp_all [eq_comm]
  · intro z _ hz; simp [Ne.symm hz]
  · simp

theorem realize_tensor : (C.realize p q F).tensor = C.insert p q F.kernel := by
  let M := C.realize p q F
  let _ : Fintype (env (D := D) C) := inferInstanceAs (Fintype ((z : M.graph.V) → M.graph.T z))
  let E : env (D := D) C ≃ assignments C.net × (C.labels × (Fin 4 → Index D)) :=
    (Equiv.sumPiEquivProdPi _).trans ((Equiv.refl _).prodCongr (Equiv.sumPiEquivProdPi _))
  funext a
  let inner (x : assignments C.net) (c : C.labels) (h : Fin 4 → Index D) :=
    if common p q c = h then C.exterior x a * (((∏ i,C.half i (c i) x)*residual p q c)*F.kernel h) else 0
  have sum_eq : M.tensor a = ∑ z : assignments C.net × (C.labels × (Fin 4 → Index D)), inner z.1 z.2.1 z.2.2 := by
    apply Fintype.sum_equiv E
    intro x
    let c := C.corners x
    let h := C.hubs x
    have leaf i : M.graph.F (.inr (.inl i)) x =
        if common p q c i = h i then C.half i (c i) (C.old x) else 0 :=
      link _ _ _
    have all_leaves : (∏ i, M.graph.F (.inr (.inl i)) x) =
        if common p q c = h then ∏ i,C.half i (c i) (C.old x) else 0 := by
      simp_rw [leaf]
      by_cases e : common p q c=h
      · simp [e]
      · obtain ⟨i,hi⟩ : ∃ i, common p q c i ≠ h i := by by_contra! he; exact e (funext he)
        rw [ite_eq_right e,Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)]
    have res0 : M.graph.F (.inr (.inr 0)) x = if (p (c 0)).2=(p (c 3)).2 then 1 else 0 := link _ _ _
    have res1 : M.graph.F (.inr (.inr 1)) x = if (q (c 1)).2=(q (c 2)).2 then 1 else 0 := link _ _ _
    have mid : M.graph.F (.inr (.inr 2)) x = F.kernel h := rfl
    change (∏ i,C.net.out i (C.old x) (a i)) * 1 * 1 * (∏ k, M.graph.F k x) =
      inner (C.old x) c h
    have bonds : (∏ k, M.graph.F k x) =
        (∏ k : C.net.graph.K,M.graph.F (.inl k) x) *
          ∏ k : Fin 4 ⊕ Fin 3,M.graph.F (.inr k) x :=
      Fintype.prod_sum_type (fun k : C.net.graph.K ⊕ (Fin 4 ⊕ Fin 3) => M.graph.F k x)
    rw [bonds,Fintype.prod_sum_type,Fin.prod_univ_three,all_leaves,res0,res1,mid]
    have oldF k : M.graph.F (.inl k) x = C.net.graph.F k (C.old x) := rfl
    simp only [oldF,inner,exterior,residual]
    split_ifs <;> ring
  rw [sum_eq,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro x _
  rw [Fintype.sum_prod_type,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  simp [inner]

end CutContext

end OM.NNN32
