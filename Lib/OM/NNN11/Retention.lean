import Lib.OM.NNN11.NetworkPowers

/-! Literal retention with identity complementary bonds, for every choice of
the heavy party. Only copy positions, never tensor parties, are rearranged. -/
noncomputable section
open scoped BigOperators Classical
namespace OM.NNN11.Network
open CoordinateTensor OM.NNN.Raw OM.NNN2 OM.NNN3
set_option maxHeartbeats 1000000

variable {A B C X Y Z : Type}
  [Fintype A] [Fintype B] [Fintype C]
  [Fintype X] [Fintype Y] [Fintype Z]

def pairAB (T : Tensor ℂ X Y Z) (P : Operator (BondAB A B X Y)) :
    Tensor ℂ ((A → X) × (B → X)) ((A → Y) × (B → Y)) ((A → Z) × (B → Z)) :=
  fun x y z => ∑ a, ∑ b,
    P (a, x.2) (y.1, b) * ordered T x.1 a z.1 * ordered T b y.2 z.2

def pairBC (T : Tensor ℂ X Y Z) (Q : Operator (BondBC B C Y Z)) :
    Tensor ℂ ((B → X) × (C → X)) ((B → Y) × (C → Y)) ((B → Z) × (C → Z)) :=
  fun x y z => ∑ b, ∑ c,
    Q (b, y.2) (z.1, c) * ordered T x.1 y.1 b * ordered T x.2 c z.2

def pairCA (T : Tensor ℂ X Y Z) (R : Operator (BondCA C A Z X)) :
    Tensor ℂ ((A → X) × (C → X)) ((A → Y) × (C → Y)) ((A → Z) × (C → Z)) :=
  fun x y z => ∑ c, ∑ a,
    R (c, z.1) (x.2, a) * ordered T x.1 y.1 a * ordered T c y.2 z.2

theorem retainedAB (T : Tensor ℂ X Y Z) (P : Operator (BondAB A B X Y)) :
    contract (C := C) T P (identity _) (identity _) =
      fun x y z => pairAB T P (x.1, x.2.1) (y.1, y.2.1) (z.1, z.2.1) *
        ordered T x.2.2 y.2.2 z.2.2 := by
  funext x y z
  simp [contract, identity, pairAB, Prod.ext_iff, Fintype.sum_prod_type,
    ite_mul, mul_ite, ite_and, Finset.sum_ite_irrel, Finset.sum_mul, Finset.mul_sum,
    mul_comm, mul_left_comm, mul_assoc]

theorem retainedBC (T : Tensor ℂ X Y Z) (Q : Operator (BondBC B C Y Z)) :
    contract (A := A) T (identity _) Q (identity _) =
      fun x y z => pairBC T Q x.2 y.2 z.2 * ordered T x.1 y.1 z.1 := by
  funext x y z
  simp [contract, identity, pairBC, Prod.ext_iff, Fintype.sum_prod_type,
    ite_mul, mul_ite, ite_and, Finset.sum_ite_irrel, Finset.sum_mul, Finset.mul_sum,
    mul_comm, mul_left_comm, mul_assoc]

theorem retainedCA (T : Tensor ℂ X Y Z) (R : Operator (BondCA C A Z X)) :
    contract (B := B) T (identity _) (identity _) R =
      fun x y z => pairCA T R (x.1, x.2.2) (y.1, y.2.2) (z.1, z.2.2) *
        ordered T x.2.1 y.2.1 z.2.1 := by
  funext x y z
  simp only [contract, identity, Prod.ext_iff, Fintype.sum_prod_type,
    ite_mul, mul_ite, ite_and, Finset.sum_ite_irrel,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
    Finset.sum_const_zero, one_mul, mul_one, zero_mul, mul_zero]
  rw [Finset.sum_comm]
  simp only [pairCA, Finset.sum_mul]
  repeat' (apply Finset.sum_congr rfl; intro _ _)
  ring

def takeMiddle (E F G : Type) : E × F × G ≃ (E × G) × F where
  toFun x := ((x.1, x.2.2), x.2.1)
  invFun x := (x.1.1, x.2, x.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

variable [Nonempty X] [Nonempty Y] [Nonempty Z]
  [DecidableEq A] [DecidableEq B] [DecidableEq C]

theorem value_retainedAB (φ : PolMul.Spectral ℂ) (T : Tensor ℂ X Y Z)
    (P : Operator (BondAB A B X Y)) :
    value φ (contract (C := C) T P (identity _) (identity _)) =
      value φ (pairAB T P) * value φ T ^ Fintype.card C := by
  rw [retainedAB]
  have h := value_reindex φ (tensorProduct (pairAB T P) (ordered (D := C) T))
    (Equiv.prodAssoc _ _ _).symm (Equiv.prodAssoc _ _ _).symm (Equiv.prodAssoc _ _ _).symm
  rw [value_product', value_ordered] at h
  exact h

theorem value_retainedBC (φ : PolMul.Spectral ℂ) (T : Tensor ℂ X Y Z)
    (Q : Operator (BondBC B C Y Z)) :
    value φ (contract (A := A) T (identity _) Q (identity _)) =
      value φ (pairBC T Q) * value φ T ^ Fintype.card A := by
  rw [retainedBC]
  have h := value_reindex φ (tensorProduct (pairBC T Q) (ordered (D := A) T))
    (Equiv.prodComm _ _) (Equiv.prodComm _ _) (Equiv.prodComm _ _)
  rw [value_product', value_ordered] at h
  exact h

theorem value_retainedCA (φ : PolMul.Spectral ℂ) (T : Tensor ℂ X Y Z)
    (R : Operator (BondCA C A Z X)) :
    value φ (contract (B := B) T (identity _) (identity _) R) =
      value φ (pairCA T R) * value φ T ^ Fintype.card B := by
  rw [retainedCA]
  have h := value_reindex φ (tensorProduct (pairCA T R) (ordered (D := B) T))
    (takeMiddle _ _ _) (takeMiddle _ _ _) (takeMiddle _ _ _)
  rw [value_product', value_ordered] at h
  exact h

end OM.NNN11.Network
