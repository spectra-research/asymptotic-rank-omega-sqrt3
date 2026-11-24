import Lib.OM.NNN3.Values
import Lib.OM.NNN8.Compression

/-! Separate factorizations of all three cubic bonds and the exact telescope. -/
noncomputable section
open scoped BigOperators Classical
namespace OM.NNN10
open CoordinateTensor OM.NNN.Raw OM.NNN2 OM.NNN3
set_option maxHeartbeats 2000000

variable {X A B C R Q P : Type} [Fintype X] [Fintype R] [Fintype Q] [Fintype P]

lemma map_mm_rect (U : A → R × P → ℂ) (V : B → Q × P → ℂ)
    (W : C → R × Q → ℂ) (a : A) (b : B) (c : C) :
    mapTensor U V W (mm R Q P) a b c =
      ∑ r, ∑ q, ∑ p, U a (r, p) * V b (q, p) * W c (r, q) := by
  simp only [mapTensor, mm, Fintype.sum_prod_type, mul_ite, mul_one, mul_zero, ite_and]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq',
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  apply Finset.sum_congr rfl
  intro r _
  rw [Finset.sum_comm]

def bondKernel (U V : R → X → X → ℂ) : Kernel X := fun a b c d => ∑ r, U r a b * V r c d

def headLeft (T : Cube ℂ X) (U : P → X → X → ℂ) (V : R → X → X → ℂ) :
    Triple X → R × P → ℂ := fun x rp => ∑ a : X × X,
      U rp.2 a.1 x.2.1 * V rp.1 x.2.2 a.2 * T x.1 a.1 a.2

def headMid (T : Cube ℂ X) (V : P → X → X → ℂ) (U : Q → X → X → ℂ) :
    Triple X → Q × P → ℂ := fun y qp => ∑ b : X × X,
      V qp.2 y.1 b.1 * U qp.1 b.2 y.2.2 * T b.1 y.2.1 b.2

def headRight (T : Cube ℂ X) (U : R → X → X → ℂ) (V : Q → X → X → ℂ) :
    Triple X → R × Q → ℂ := fun z rq => ∑ c : X × X,
      U rq.1 c.1 z.1 * V rq.2 z.2.1 c.2 * T c.1 c.2 z.2.2

theorem factorized_payload (T : Cube ℂ X)
    (Uab Vab : P → X → X → ℂ) (Ubc Vbc : Q → X → X → ℂ)
    (Uca Vca : R → X → X → ℂ) :
    mapTensor (headLeft T Uab Vca) (headMid T Vab Ubc) (headRight T Uca Vbc)
      (mm R Q P) = contract T (bondKernel Uab Vab) (bondKernel Ubc Vbc) (bondKernel Uca Vca) := by
  funext x y z
  rw [map_mm_rect]
  simp only [headLeft, headMid, headRight, contract, bondKernel, Finset.sum_mul, Finset.mul_sum]
  conv_lhs =>
    arg 2; ext r
    arg 2; ext q
    arg 2; ext p
    rw [sum_reverse]
  conv_rhs =>
    arg 2; ext a
    arg 2; ext b
    arg 2; ext c
    rw [sum_reverse]
  calc
    _ = ∑ s : R × Q × P, ∑ t : (X × X) × (X × X) × (X × X),
      (Uab s.2.2 t.1.1 x.2.1 * Vca s.1 x.2.2 t.1.2 * T x.1 t.1.1 t.1.2) *
      (Vab s.2.2 y.1 t.2.1.1 * Ubc s.2.1 t.2.1.2 y.2.2 * T t.2.1.1 y.2.1 t.2.1.2) *
      (Uca s.1 t.2.2.1 z.1 * Vbc s.2.1 z.2.1 t.2.2.2 * T t.2.2.1 t.2.2.2 z.2.2) := by
        simp only [Fintype.sum_prod_type]
    _ = ∑ t : (X × X) × (X × X) × (X × X), ∑ s : R × Q × P,
      (Uab s.2.2 t.1.1 x.2.1 * Vca s.1 x.2.2 t.1.2 * T x.1 t.1.1 t.1.2) *
      (Vab s.2.2 y.1 t.2.1.1 * Ubc s.2.1 t.2.1.2 y.2.2 * T t.2.1.1 y.2.1 t.2.1.2) *
      (Uca s.1 t.2.2.1 z.1 * Vbc s.2.1 z.2.1 t.2.2.2 * T t.2.2.1 t.2.2.2 z.2.2) := Finset.sum_comm
    _ = _ := by
      simp only [Fintype.sum_prod_type, Finset.sum_mul, Finset.mul_sum]
      repeat' (apply Finset.sum_congr rfl; intro _ _)
      ac_rfl

def contractAB (T : Cube ℂ X) (B C : Kernel X) : Kernel X →ₗ[ℂ] Cube ℂ (Triple X) where
  toFun A := contract T A B C
  map_add' A A' := contract_add_AB T A B C A'
  map_smul' z A := by
    funext x y w
    simp only [contract, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, RingHom.id_apply]
    repeat' (apply Finset.sum_congr rfl; intro _ _)
    ring

def contractBC (T : Cube ℂ X) (A C : Kernel X) : Kernel X →ₗ[ℂ] Cube ℂ (Triple X) where
  toFun B := contract T A B C
  map_add' B B' := contract_add_BC T A B C B'
  map_smul' z B := by
    funext x y w
    simp only [contract, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, RingHom.id_apply]
    repeat' (apply Finset.sum_congr rfl; intro _ _)
    ring

def contractCA (T : Cube ℂ X) (A B : Kernel X) : Kernel X →ₗ[ℂ] Cube ℂ (Triple X) where
  toFun C := contract T A B C
  map_add' C C' := contract_add_CA T A B C C'
  map_smul' z C := by
    funext x y w
    simp only [contract, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, RingHom.id_apply]
    repeat' (apply Finset.sum_congr rfl; intro _ _)
    ring

/-- BC first, CA second, AB last. All mixed terms remain in the first two groups. -/
theorem telescope (T : Cube ℂ X) (A B C : Kernel X) :
    contract T (straight + A) (straight + B) (straight + C) =
      cube T + contract T A straight straight +
        contract T (straight + A) straight C + contract T (straight + A) B (straight + C) := by
  rw [contract_add_BC, contract_add_CA, contract_add_AB, contract_000]

/-- The correction count is a sum of three lists, with no products of list sizes. -/
theorem telescope_sum {I J K : Type} (T : Cube ℂ X)
    (s : Finset I) (t : Finset J) (u : Finset K)
    (A : I → Kernel X) (B : J → Kernel X) (C : K → Kernel X) :
    contract T (straight + ∑ i ∈ s, A i) (straight + ∑ j ∈ t, B j) (straight + ∑ k ∈ u, C k) =
      cube T + (∑ i ∈ s, contract T (A i) straight straight) +
        (∑ k ∈ u, contract T (straight + ∑ i ∈ s, A i) straight (C k)) +
        ∑ j ∈ t, contract T (straight + ∑ i ∈ s, A i) (B j) (straight + ∑ k ∈ u, C k) := by
  rw [telescope]
  have hAB := map_sum (contractAB T straight straight) A s
  have hCA := map_sum (contractCA T (straight + ∑ i ∈ s, A i) straight) C u
  have hBC := map_sum (contractBC T (straight + ∑ i ∈ s, A i)
    (straight + ∑ k ∈ u, C k)) B t
  change contract T (∑ i ∈ s, A i) straight straight = _ at hAB
  change contract T (straight + ∑ i ∈ s, A i) straight (∑ k ∈ u, C k) = _ at hCA
  change contract T (straight + ∑ i ∈ s, A i) (∑ j ∈ t, B j) (straight + ∑ k ∈ u, C k) = _ at hBC
  rw [hAB, hCA, hBC]
  rfl

end OM.NNN10
