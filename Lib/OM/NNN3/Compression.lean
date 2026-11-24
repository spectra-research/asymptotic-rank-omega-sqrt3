import Lib.OM.NNN3.Basic

/-! Literal expansion of the three symmetric bonds. Output coordinates are the
ordered triples `(i,b,e)`, `(a,j,d)`, `(f,c,k)` of the paper. -/
noncomputable section
open scoped BigOperators Classical
namespace OM.NNN3
open CoordinateTensor OM.NNN.Raw OM.NNN2
set_option maxHeartbeats 200000
variable {X : Type} [Fintype X]
abbrev Triple (X : Type) := X × X × X

def cube (T : Cube ℂ X) : Cube ℂ (Triple X) :=
  fun x y z => T x.1 y.1 z.1 * T x.2.1 y.2.1 z.2.1 * T x.2.2 y.2.2 z.2.2

def compressedLeft (T : Cube ℂ X) : Triple X → Sym2 X × Sym2 X → ℂ :=
  fun x rp => ∑ a : X × X,
    symU rp.2 a.1 x.2.1 * symV rp.1 x.2.2 a.2 * T x.1 a.1 a.2

def compressedMid (T : Cube ℂ X) : Triple X → Sym2 X × Sym2 X → ℂ :=
  fun y qp => ∑ b : X × X,
    symV qp.2 y.1 b.1 * symU qp.1 b.2 y.2.2 * T b.1 y.2.1 b.2

def compressedRight (T : Cube ℂ X) : Triple X → Sym2 X × Sym2 X → ℂ :=
  fun z rq => ∑ c : X × X,
    symU rq.1 c.1 z.1 * symV rq.2 z.2.1 c.2 * T c.1 c.2 z.2.2

def compressed (T : Cube ℂ X) : Cube ℂ (Triple X) :=
  mapTensor (compressedLeft T) (compressedMid T) (compressedRight T)
    (mm (Sym2 X) (Sym2 X) (Sym2 X))

lemma sum_reverse {A B C : Type} [Fintype A] [Fintype B] [Fintype C]
    (f : A → B → C → ℂ) : (∑ a, ∑ b, ∑ c, f a b c) = ∑ c, ∑ b, ∑ a, f a b c := by
  calc
    _ = ∑ a, ∑ c, ∑ b, f a b c := by
      apply Finset.sum_congr rfl
      intro a _
      exact Finset.sum_comm
    _ = ∑ c, ∑ a, ∑ b, f a b c := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro c _
      exact Finset.sum_comm

/-- Contraction before evaluating the three identity-plus-swap kernels. -/
lemma compressed_contraction (T : Cube ℂ X) (x y z : Triple X) :
    compressed T x y z =
      ∑ a : X × X, ∑ b : X × X, ∑ c : X × X,
        T x.1 a.1 a.2 * T b.1 y.2.1 b.2 * T c.1 c.2 z.2.2 *
        (∑ r : Sym2 X, symU r c.1 z.1 * symV r x.2.2 a.2) *
        (∑ q : Sym2 X, symU q b.2 y.2.2 * symV q z.2.1 c.2) *
        (∑ p : Sym2 X, symU p a.1 x.2.1 * symV p y.1 b.1) := by
  unfold compressed
  rw [map_mm]
  simp only [compressedLeft, compressedMid, compressedRight]
  simp only [Finset.sum_mul, Finset.mul_sum]
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
    _ = ∑ s : Sym2 X × Sym2 X × Sym2 X, ∑ t : (X × X) × (X × X) × (X × X),
      (symU s.2.2 t.1.1 x.2.1 * symV s.1 x.2.2 t.1.2 * T x.1 t.1.1 t.1.2) *
      (symV s.2.2 y.1 t.2.1.1 * symU s.2.1 t.2.1.2 y.2.2 * T t.2.1.1 y.2.1 t.2.1.2) *
      (symU s.1 t.2.2.1 z.1 * symV s.2.1 z.2.1 t.2.2.2 * T t.2.2.1 t.2.2.2 z.2.2) := by
        simp only [Fintype.sum_prod_type]
    _ = ∑ t : (X × X) × (X × X) × (X × X), ∑ s : Sym2 X × Sym2 X × Sym2 X,
      (symU s.2.2 t.1.1 x.2.1 * symV s.1 x.2.2 t.1.2 * T x.1 t.1.1 t.1.2) *
      (symV s.2.2 y.1 t.2.1.1 * symU s.2.1 t.2.1.2 y.2.2 * T t.2.1.1 y.2.1 t.2.1.2) *
      (symU s.1 t.2.2.1 z.1 * symV s.2.1 z.2.1 t.2.2.2 * T t.2.2.1 t.2.2.2 z.2.2) := Finset.sum_comm
    _ = _ := by
      simp only [Fintype.sum_prod_type, Finset.sum_mul, Finset.mul_sum]
      repeat' (apply Finset.sum_congr rfl; intro _ _)
      ac_rfl

def singleAB (T : Cube ℂ X) : Cube ℂ (Triple X) := fun x y z =>
  if x.2.1 = y.1 then (∑ a, T x.1 a z.1 * T a y.2.1 z.2.1) * T x.2.2 y.2.2 z.2.2 else 0

def singleBC (T : Cube ℂ X) : Cube ℂ (Triple X) := fun x y z =>
  if y.2.2 = z.2.1 then T x.1 y.1 z.1 * (∑ c, T x.2.1 y.2.1 c * T x.2.2 c z.2.2) else 0

def singleCA (T : Cube ℂ X) : Cube ℂ (Triple X) := fun x y z =>
  if x.2.2 = z.1 then (∑ e, T x.1 y.1 e * T e y.2.2 z.2.2) * T x.2.1 y.2.1 z.2.1 else 0

def doubleABBC (T : Cube ℂ X) : Cube ℂ (Triple X) := fun x y z =>
  if x.2.1 = y.1 ∧ y.2.2 = z.2.1 then
    ∑ a, ∑ c, T x.1 a z.1 * T a y.2.1 c * T x.2.2 c z.2.2 else 0

def doubleABCA (T : Cube ℂ X) : Cube ℂ (Triple X) := fun x y z =>
  if x.2.1 = y.1 ∧ x.2.2 = z.1 then
    ∑ a, ∑ e, T x.1 a e * T a y.2.1 z.2.1 * T e y.2.2 z.2.2 else 0

def doubleBCCA (T : Cube ℂ X) : Cube ℂ (Triple X) := fun x y z =>
  if y.2.2 = z.2.1 ∧ x.2.2 = z.1 then
    ∑ e, ∑ c, T x.1 y.1 e * T x.2.1 y.2.1 c * T e c z.2.2 else 0

def tripleSwap (T : Cube ℂ X) : Cube ℂ (Triple X) := fun x y z =>
  if x.2.1 = y.1 ∧ y.2.2 = z.2.1 ∧ x.2.2 = z.1 then
    ∑ a, ∑ e, ∑ c, T x.1 a e * T a y.2.1 c * T e c z.2.2 else 0

end OM.NNN3
