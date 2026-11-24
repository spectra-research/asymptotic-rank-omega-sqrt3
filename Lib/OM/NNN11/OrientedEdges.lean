import Lib.OM.NNN11.EdgeFactor

/-! Equality factors on the other two bonds, priced at the original spectral
point. No invariance under a permutation of tensor parties is used. -/
noncomputable section
open scoped BigOperators Classical
namespace OM.NNN11
open CoordinateTensor OM.NNN.Raw OM.NNN2 OM.NNN3
open Foundations.PairUnitExponents
set_option maxHeartbeats 1000000

def pairBC (E : Type) : Tensor ℂ Unit E E := fun _ y z => if y = z then 1 else 0
def pairCA (E : Type) : Tensor ℂ E Unit E := fun x _ z => if x = z then 1 else 0

theorem value_pairBC {E : Type} [Fintype E] [Nonempty E] (φ : PolMul.Spectral ℂ) :
    value φ (pairBC E) = (Fintype.card E : ℝ) ^ theta φ 0 := by
  have h := value_reindex φ (mm Unit E Unit)
    (unitProd Unit) (prodUnit E) (unitProd E)
  have he : (fun x y z => mm Unit E Unit (unitProd Unit x) (prodUnit E y)
      (unitProd E z)) = pairBC E := by
    funext x y z
    simp [mm, unitProd, prodUnit, pairBC]
  rw [he, value_mm φ (n := 1) (p := ⟨Fintype.card E, Fintype.card_pos⟩) (m := 1)
    (Equiv.ofUnique (Fin 1) Unit) (Fintype.equivFin E).symm
    (Equiv.ofUnique (Fin 1) Unit)] at h
  simpa using! h

theorem value_pairCA {E : Type} [Fintype E] [Nonempty E] (φ : PolMul.Spectral ℂ) :
    value φ (pairCA E) = (Fintype.card E : ℝ) ^ theta φ 1 := by
  have h := value_reindex φ (mm E Unit Unit)
    (prodUnit E) (unitProd Unit) (prodUnit E)
  have he : (fun x y z => mm E Unit Unit (prodUnit E x) (unitProd Unit y)
      (prodUnit E z)) = pairCA E := by
    funext x y z
    simp [mm, unitProd, prodUnit, pairCA]
  rw [he, value_mm φ (n := ⟨Fintype.card E, Fintype.card_pos⟩) (p := 1) (m := 1)
    (Fintype.equivFin E).symm (Equiv.ofUnique (Fin 1) Unit)
    (Equiv.ofUnique (Fin 1) Unit)] at h
  simpa using! h

def edgeFactorBC {X R Q E : Type} (W : Tensor ℂ X R Q) :
    Tensor ℂ X (R × E) (Q × E) :=
  fun x y z => if y.2 = z.2 then W x y.1 z.1 else 0

def edgeFactorCA {R Y Q E : Type} (W : Tensor ℂ R Y Q) :
    Tensor ℂ (R × E) Y (Q × E) :=
  fun x y z => if z.2 = x.2 then W x.1 y z.1 else 0

theorem value_edgeFactorBC {X R Q E : Type} [Fintype X] [Fintype R] [Fintype Q]
    [Fintype E] [Nonempty X] [Nonempty R] [Nonempty Q] [Nonempty E]
    (φ : PolMul.Spectral ℂ) (W : Tensor ℂ X R Q) :
    value φ (edgeFactorBC (E := E) W) = value φ W * (Fintype.card E : ℝ) ^ theta φ 0 := by
  have h := value_reindex φ (tensorProduct W (pairBC E))
    (prodUnit X) (Equiv.refl _) (Equiv.refl _)
  have he : (fun x y z => tensorProduct W (pairBC E) (prodUnit X x) y z) =
      edgeFactorBC W := by
    funext x y z
    simp [tensorProduct, pairBC, prodUnit, unitProd, edgeFactorBC]
  simpa only [Equiv.refl_apply, he, value_product', value_pairBC] using! h

theorem value_edgeFactorCA {R Y Q E : Type} [Fintype R] [Fintype Y] [Fintype Q]
    [Fintype E] [Nonempty R] [Nonempty Y] [Nonempty Q] [Nonempty E]
    (φ : PolMul.Spectral ℂ) (W : Tensor ℂ R Y Q) :
    value φ (edgeFactorCA (E := E) W) = value φ W * (Fintype.card E : ℝ) ^ theta φ 1 := by
  have h := value_reindex φ (tensorProduct W (pairCA E))
    (Equiv.refl _) (prodUnit Y) (Equiv.refl _)
  have he : (fun x y z => tensorProduct W (pairCA E) x (prodUnit Y y) z) =
      edgeFactorCA W := by
    funext x y z
    simp [tensorProduct, pairCA, prodUnit, unitProd, edgeFactorCA, eq_comm]
  simpa only [Equiv.refl_apply, he, value_product', value_pairCA] using! h

end OM.NNN11
