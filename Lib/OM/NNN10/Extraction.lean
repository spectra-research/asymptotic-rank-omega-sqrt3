import Lib.OM.NNN10.Payload

/-! Star extraction of a digit mask with arbitrary operators on the other bonds.
The final AB group is the square correction tensored with the ordered input. -/
noncomputable section
open scoped BigOperators Classical
namespace OM.NNN10
open CoordinateTensor OM.NNN.Raw OM.NNN2 OM.NNN3
open NNN8 (maskKernel Selected Remaining fill maskKernel_fill maskKernel_eq_zero)
set_option maxHeartbeats 1000000

section Stars
variable {A B C R P E : Type} [Fintype R] [Fintype P] [Fintype E]

lemma starBC (ry : B → P) (sy : B → E) (rz : C → R) (sz : C → E)
    (W : A → R → P → ℂ) :
    Restricts (mm R E P) (fun x y z => if sy y = sz z then W x (rz z) (ry y) else 0) := by
  refine ⟨(fun x r => W x r.1 r.2), (fun y => identityRows _ (sy y, ry y)),
    (fun z => identityRows _ (rz z, sz z)), ?_⟩
  funext x y z
  simp [map_mm_rect, identityRows, Prod.ext_iff, ite_mul, mul_ite, ite_and,
    Finset.sum_ite_irrel, eq_comm]

lemma starCA (rx : A → P) (sx : A → E) (rz : C → R) (sz : C → E)
    (W : P → B → R → ℂ) :
    Restricts (mm E R P) (fun x y z => if sx x = sz z then W (rx x) y (rz z) else 0) := by
  refine ⟨(fun x => identityRows _ (sx x, rx x)), (fun y r => W r.2 y r.1),
    (fun z => identityRows _ (sz z, rz z)), ?_⟩
  funext x y z
  simp [map_mm_rect, identityRows, Prod.ext_iff, ite_mul, mul_ite, ite_and,
    Finset.sum_ite_irrel, eq_comm]
end Stars

variable {D : Type} [Fintype D] [LinearOrder D] {X : D → Type}
  [∀ h, Fintype (X h)]

abbrev FullResidual (X : D → Type) (s : Finset D) := ((∀ h, X h) × (∀ h, X h)) × Remaining X s

lemma fullBC_factorization (T : Cube ℂ (∀ h, X h)) (s : Finset D)
    (A C : Kernel (∀ h, X h)) (e : Selected X s) (x y z : Triple (∀ h, X h)) :
    contract T A (maskKernel s) C x y z =
      if (fun h : {h // h ∈ s} => y.2.2 h) = (fun h : {h // h ∈ s} => z.2.1 h) then
        contract T A (maskKernel s) C x
          (y.1, y.2.1, fill s e (fun h => y.2.2 h))
          (z.1, fill s e (fun h => z.2.1 h), z.2.2) else 0 := by
  split_ifs with he
  · unfold contract
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro c _
    rw [maskKernel_fill s b.2 y.2.2 z.2.1 c.2 e he]
  · simp [contract, maskKernel_eq_zero s _ y.2.2 z.2.1 _ he]

lemma fullCA_factorization (T : Cube ℂ (∀ h, X h)) (s : Finset D)
    (A B : Kernel (∀ h, X h)) (e : Selected X s) (x y z : Triple (∀ h, X h)) :
    contract T A B (maskKernel s) x y z =
      if (fun h : {h // h ∈ s} => x.2.2 h) = (fun h : {h // h ∈ s} => z.1 h) then
        contract T A B (maskKernel s)
          (x.1, x.2.1, fill s e (fun h => x.2.2 h)) y
          (fill s e (fun h => z.1 h), z.2.1, z.2.2) else 0 := by
  split_ifs with he
  · unfold contract
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro c _
    rw [maskKernel_fill s c.1 z.1 x.2.2 a.2 e he.symm]
  · simp [contract, maskKernel_eq_zero s _ z.1 x.2.2 _ (Ne.symm he)]

theorem fullBC_restriction (T : Cube ℂ (∀ h, X h)) (s : Finset D)
    (A C : Kernel (∀ h, X h)) (e : Selected X s) :
    Restricts (mm (FullResidual X s) (Selected X s) (FullResidual X s))
      (contract T A (maskKernel s) C) := by
  have h := starBC
    (fun y : Triple (∀ h, X h) => ((y.1, y.2.1), fun h : {h // h ∉ s} => y.2.2 h))
    (fun y => fun h : {h // h ∈ s} => y.2.2 h)
    (fun z : Triple (∀ h, X h) => ((z.1, z.2.2), fun h : {h // h ∉ s} => z.2.1 h))
    (fun z => fun h : {h // h ∈ s} => z.2.1 h)
    (fun x r p => contract T A (maskKernel s) C x
      (p.1.1, p.1.2, fill s e p.2) (r.1.1, fill s e r.2, r.1.2))
  convert! h using 1
  funext x y z
  simpa only using! fullBC_factorization T s A C e x y z

theorem fullCA_restriction (T : Cube ℂ (∀ h, X h)) (s : Finset D)
    (A B : Kernel (∀ h, X h)) (e : Selected X s) :
    Restricts (mm (Selected X s) (FullResidual X s) (FullResidual X s))
      (contract T A B (maskKernel s)) := by
  have h := starCA
    (fun x : Triple (∀ h, X h) => ((x.1, x.2.1), fun h : {h // h ∉ s} => x.2.2 h))
    (fun x => fun h : {h // h ∈ s} => x.2.2 h)
    (fun z : Triple (∀ h, X h) => ((z.2.1, z.2.2), fun h : {h // h ∉ s} => z.1 h))
    (fun z => fun h : {h // h ∈ s} => z.1 h)
    (fun p y r => contract T A B (maskKernel s)
      (p.1.1, p.1.2, fill s e p.2) y (fill s e r.2, r.1.1, r.1.2))
  convert! h using 1
  funext x y z
  simpa only using! fullCA_factorization T s A B e x y z

theorem retainedAB (T : Cube ℂ (∀ h, X h)) (s : Finset D) :
    contract T (maskKernel s) straight straight =
      fun x y z => NNN8.correction T s (x.1, x.2.1) (y.1, y.2.1) (z.1, z.2.1) *
        T x.2.2 y.2.2 z.2.2 := by
  funext x y z
  simp [contract, straight, NNN8.correction, Fintype.sum_prod_type,
    mul_ite, ite_mul, ite_and, Finset.sum_ite_irrel, Finset.sum_mul, Finset.mul_sum,
    mul_comm, mul_left_comm, mul_assoc]

theorem value_retainedAB [∀ h, Nonempty (X h)] (φ : PolMul.Spectral ℂ)
    (T : Cube ℂ (∀ h, X h)) (s : Finset D) :
    value φ (contract T (maskKernel s) straight straight) =
      value φ (NNN8.correction T s) * value φ T := by
  rw [retainedAB]
  have h := value_reindex φ (tensorProduct (NNN8.correction T s) T)
    (Equiv.prodAssoc _ _ _).symm (Equiv.prodAssoc _ _ _).symm (Equiv.prodAssoc _ _ _).symm
  rw [value_product'] at h
  simpa only [tensorProduct, Equiv.prodAssoc_symm_apply] using! h

end OM.NNN10
