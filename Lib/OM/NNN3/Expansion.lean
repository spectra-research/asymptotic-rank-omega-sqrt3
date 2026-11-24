import Lib.OM.NNN3.Compression

/-! Expand the three bonds by multilinearity, then contract the eight kernels
separately. This keeps every coefficient proof small. -/
noncomputable section
open scoped BigOperators Classical
namespace OM.NNN3
open CoordinateTensor OM.NNN.Raw OM.NNN2
set_option maxHeartbeats 400000
variable {X : Type} [Fintype X]

abbrev Kernel (X : Type) := X → X → X → X → ℂ

def straight : Kernel X := fun a b c d => if a = c ∧ b = d then 1 else 0

def crossed : Kernel X := fun a b c d => if a = d ∧ b = c then 1 else 0

def contract (T : Cube ℂ X) (A B C : Kernel X) : Cube ℂ (Triple X) := fun x y z =>
  ∑ a : X × X, ∑ b : X × X, ∑ c : X × X,
    T x.1 a.1 a.2 * T b.1 y.2.1 b.2 * T c.1 c.2 z.2.2 *
    C c.1 z.1 x.2.2 a.2 * B b.2 y.2.2 z.2.1 c.2 * A a.1 x.2.1 y.1 b.1

lemma compressed_contract (T : Cube ℂ X) :
    compressed T = contract T (straight + crossed) (straight + crossed) (straight + crossed) := by
  funext x y z
  simp only [compressed_contraction, sym_pairing, contract, Pi.add_apply, straight, crossed]

lemma contract_add_AB (T : Cube ℂ X) (A B C A' : Kernel X) :
    contract T (A + A') B C = contract T A B C + contract T A' B C := by
  funext x y z
  simp only [contract, Pi.add_apply, mul_add, add_mul, Finset.sum_add_distrib]

lemma contract_add_BC (T : Cube ℂ X) (A B C B' : Kernel X) :
    contract T A (B + B') C = contract T A B C + contract T A B' C := by
  funext x y z
  simp only [contract, Pi.add_apply, mul_add, add_mul, Finset.sum_add_distrib]

lemma contract_add_CA (T : Cube ℂ X) (A B C C' : Kernel X) :
    contract T A B (C + C') = contract T A B C + contract T A B C' := by
  funext x y z
  simp only [contract, Pi.add_apply, mul_add, add_mul, Finset.sum_add_distrib]

lemma contract_000 (T : Cube ℂ X) :
    contract T straight straight straight = cube T := by
  funext x y z
  simp [contract, straight, crossed, cube, Fintype.sum_prod_type,
    mul_ite, ite_mul, ite_and, Finset.sum_ite_irrel, Finset.sum_mul, Finset.mul_sum,
    eq_comm, mul_comm, mul_left_comm, mul_assoc]
  all_goals split_ifs <;> rfl

lemma contract_100 (T : Cube ℂ X) :
    contract T crossed straight straight = singleAB T := by
  funext x y z
  simp [contract, straight, crossed, singleAB, Fintype.sum_prod_type,
    mul_ite, ite_mul, ite_and, Finset.sum_ite_irrel, Finset.sum_mul, Finset.mul_sum,
    eq_comm, mul_comm, mul_left_comm, mul_assoc]
  all_goals split_ifs <;> rfl

lemma contract_010 (T : Cube ℂ X) :
    contract T straight crossed straight = singleBC T := by
  funext x y z
  simp [contract, straight, crossed, singleBC, Fintype.sum_prod_type,
    mul_ite, ite_mul, ite_and, Finset.sum_ite_irrel, Finset.sum_mul, Finset.mul_sum,
    eq_comm, mul_comm, mul_left_comm, mul_assoc]
  all_goals split_ifs <;> rfl

lemma contract_001 (T : Cube ℂ X) :
    contract T straight straight crossed = singleCA T := by
  funext x y z
  simp [contract, straight, crossed, singleCA, Fintype.sum_prod_type,
    mul_ite, ite_mul, ite_and, Finset.sum_ite_irrel, Finset.sum_mul, Finset.mul_sum,
    eq_comm, mul_comm, mul_left_comm, mul_assoc]
  all_goals split_ifs <;> rfl

lemma contract_110 (T : Cube ℂ X) :
    contract T crossed crossed straight = doubleABBC T := by
  funext x y z
  simp [contract, straight, crossed, doubleABBC, Fintype.sum_prod_type,
    mul_ite, ite_mul, ite_and, Finset.sum_ite_irrel, Finset.sum_mul, Finset.mul_sum,
    eq_comm, mul_comm, mul_left_comm, mul_assoc]
  all_goals split_ifs <;> rfl

lemma contract_101 (T : Cube ℂ X) :
    contract T crossed straight crossed = doubleABCA T := by
  funext x y z
  simp [contract, straight, crossed, doubleABCA, Fintype.sum_prod_type,
    mul_ite, ite_mul, ite_and, Finset.sum_ite_irrel, Finset.sum_mul, Finset.mul_sum,
    eq_comm, mul_comm, mul_left_comm, mul_assoc]
  all_goals split_ifs <;> rfl

lemma contract_011 (T : Cube ℂ X) :
    contract T straight crossed crossed = doubleBCCA T := by
  funext x y z
  simp [contract, straight, crossed, doubleBCCA, Fintype.sum_prod_type,
    mul_ite, ite_mul, ite_and, Finset.sum_ite_irrel, Finset.sum_mul, Finset.mul_sum,
    eq_comm, mul_comm, mul_left_comm, mul_assoc]
  all_goals split_ifs <;> rfl

lemma contract_111 (T : Cube ℂ X) :
    contract T crossed crossed crossed = tripleSwap T := by
  funext x y z
  simp [contract, straight, crossed, tripleSwap, Fintype.sum_prod_type,
    mul_ite, ite_mul, ite_and, Finset.sum_ite_irrel, Finset.sum_mul, Finset.mul_sum,
    eq_comm, mul_comm, mul_left_comm, mul_assoc]
  all_goals split_ifs <;> rfl

/-- Every coefficient of the compressed image, including all seven corrections. -/
theorem compressed_expansion (T : Cube ℂ X) :
    compressed T = cube T + singleAB T + singleBC T + singleCA T +
      doubleABBC T + doubleABCA T + doubleBCCA T + tripleSwap T := by
  rw [compressed_contract]
  simp only [contract_add_AB, contract_add_BC, contract_add_CA,
    contract_000, contract_100, contract_010, contract_001,
    contract_110, contract_101, contract_011, contract_111]
  abel

end OM.NNN3
