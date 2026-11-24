import Lib.OM.NNN3.Compression

/-! All seven correction sources, with the ordered copy of `T` in the three
single-swap sources. The two-swap maps are the explicit maps. -/
noncomputable section
open scoped BigOperators Classical
namespace OM.NNN3
open CoordinateTensor OM.NNN.Raw OM.NNN2
set_option maxHeartbeats 2000000
variable {X : Type} [Fintype X]

lemma singleAB_restricts (T : Cube ℂ X) :
    Restricts (tensorProduct (mm X X X) T) (singleAB T) := by
  refine ⟨(fun x a => if x.1 = a.1.1 ∧ x.2.1 = a.1.2 ∧ x.2.2 = a.2 then 1 else 0),
    (fun y b => if y.1 = b.1.2 ∧ y.2.1 = b.1.1 ∧ y.2.2 = b.2 then 1 else 0),
    (fun z c => if z.2.2 = c.2 then ∑ a, T c.1.1 a z.1 * T a c.1.2 z.2.1 else 0), ?_⟩
  funext x y z
  simp [map_mm_product, singleAB, ite_mul, mul_ite, ite_and, Finset.sum_ite_irrel,
    Finset.sum_mul, Finset.mul_sum, eq_comm]

lemma singleBC_restricts (T : Cube ℂ X) :
    Restricts (tensorProduct (mm X X X) T) (singleBC T) := by
  refine ⟨(fun x a => if x.1 = a.2 then ∑ c, T x.2.1 a.1.2 c * T x.2.2 c a.1.1 else 0),
    (fun y b => if y.1 = b.2 ∧ y.2.1 = b.1.2 ∧ y.2.2 = b.1.1 then 1 else 0),
    (fun z c => if z.1 = c.2 ∧ z.2.1 = c.1.2 ∧ z.2.2 = c.1.1 then 1 else 0), ?_⟩
  funext x y z
  simp [map_mm_product, singleBC, ite_mul, mul_ite, ite_and, Finset.sum_ite_irrel,
    Finset.sum_mul, Finset.mul_sum, eq_comm, mul_comm, mul_left_comm, mul_assoc]

lemma singleCA_restricts (T : Cube ℂ X) :
    Restricts (tensorProduct (mm X X X) T) (singleCA T) := by
  refine ⟨(fun x a => if x.1 = a.1.2 ∧ x.2.1 = a.2 ∧ x.2.2 = a.1.1 then 1 else 0),
    (fun y b => if y.2.1 = b.2 then ∑ e, T b.1.2 y.1 e * T e y.2.2 b.1.1 else 0),
    (fun z c => if z.1 = c.1.1 ∧ z.2.1 = c.2 ∧ z.2.2 = c.1.2 then 1 else 0), ?_⟩
  funext x y z
  simp [map_mm_product, singleCA, ite_mul, mul_ite, ite_and, Finset.sum_ite_irrel,
    Finset.sum_mul, Finset.mul_sum, eq_comm, mul_comm, mul_left_comm, mul_assoc]

lemma doubleABBC_restricts (T : Cube ℂ X) :
    Restricts (tensorProduct (mm X X X) (diagonal ℂ (X × X))) (doubleABBC T) := by
  refine ⟨(fun x a => if x.1 = a.1.1 ∧ x.2.1 = a.1.2 ∧ x.2.2 = a.2.1 then 1 else 0),
    (fun y b => if y.1 = b.1.2 ∧ y.2.1 = b.2.2 ∧ y.2.2 = b.1.1 then 1 else 0),
    (fun z c => if z.2.1 = c.1.2 then
      ∑ a, ∑ d, T c.1.1 a z.1 * T a c.2.2 d * T c.2.1 d z.2.2 else 0), ?_⟩
  funext x y z
  simp [map_mm_product, diagonal, Fintype.sum_prod_type, Prod.ext_iff,
    doubleABBC, ite_mul, mul_ite, ite_and, Finset.sum_ite_irrel, eq_comm]
  split_ifs <;> rfl

lemma doubleABCA_restricts (T : Cube ℂ X) :
    Restricts (tensorProduct (mm X X X) (diagonal ℂ (X × X))) (doubleABCA T) := by
  refine ⟨(fun x a => if x.1 = a.2.1 ∧ x.2.1 = a.1.2 ∧ x.2.2 = a.1.1 then 1 else 0),
    (fun y b => if y.1 = b.1.2 ∧ y.2.1 = b.1.1 ∧ y.2.2 = b.2.2 then 1 else 0),
    (fun z c => if z.1 = c.1.1 then
      ∑ a, ∑ e, T c.2.1 a e * T a c.1.2 z.2.1 * T e c.2.2 z.2.2 else 0), ?_⟩
  funext x y z
  simp [map_mm_product, diagonal, Fintype.sum_prod_type, Prod.ext_iff,
    doubleABCA, ite_mul, mul_ite, ite_and, Finset.sum_ite_irrel, eq_comm]

lemma doubleBCCA_restricts (T : Cube ℂ X) :
    Restricts (tensorProduct (mm X X X) (diagonal ℂ (X × X))) (doubleBCCA T) := by
  refine ⟨(fun x a => if x.2.2 = a.1.1 then
      ∑ e, ∑ c, T x.1 a.1.2 e * T x.2.1 a.2.1 c * T e c a.2.2 else 0),
    (fun y b => if y.1 = b.1.2 ∧ y.2.1 = b.2.1 ∧ y.2.2 = b.1.1 then 1 else 0),
    (fun z c => if z.1 = c.1.1 ∧ z.2.1 = c.1.2 ∧ z.2.2 = c.2.2 then 1 else 0), ?_⟩
  funext x y z
  simp [map_mm_product, diagonal, Fintype.sum_prod_type, Prod.ext_iff,
    doubleBCCA, ite_mul, mul_ite, ite_and, Finset.sum_ite_irrel, eq_comm]

lemma tripleSwap_restricts (T : Cube ℂ X) :
    Restricts (tensorProduct (mm X X X) (diagonal ℂ (X × X))) (tripleSwap T) := by
  refine ⟨(fun x a => if x.1 = a.2.1 ∧ x.2.1 = a.1.2 ∧ x.2.2 = a.1.1 then 1 else 0),
    (fun y b => if y.1 = b.1.2 ∧ y.2.1 = b.2.2 ∧ y.2.2 = b.1.1 then 1 else 0),
    (fun z d => if z.1 = d.1.1 ∧ z.2.1 = d.1.2 then
      ∑ a, ∑ e, ∑ c, T d.2.1 a e * T a d.2.2 c * T e c z.2.2 else 0), ?_⟩
  funext x y z
  simp [map_mm_product, diagonal, Fintype.sum_prod_type, Prod.ext_iff,
    tripleSwap, ite_mul, mul_ite, ite_and, Finset.sum_ite_irrel, eq_comm]
  split_ifs <;> rfl


end OM.NNN3
