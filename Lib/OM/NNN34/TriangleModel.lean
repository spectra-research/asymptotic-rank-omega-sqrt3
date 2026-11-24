import Lib.OM.NNN34.RelativePrice
import Lib.OM.NNN34.Copies

/-! # Local matrix realizations of powers of a triangle with synchronized copies -/

noncomputable section

namespace OM.NNN34

open Semicontinuity AsymptoticSpectrumDuality PolMul

/-- The two ends of each cyclic wire carry a common label, and each vertex
contributes its own matrix coefficient. -/
structure TriangleModel (w : ℕ+) (d : Fin 3 → ℕ+) where
  reg : Fin 3 → Type
  [fin : ∀ i, Fintype (reg i)]
  incoming : (i : Fin 3) → reg i → Fin (w : ℕ)
  outgoing : (i : Fin 3) → reg i → Fin (w : ℕ)
  localWeight : (i : Fin 3) → Fin (d i) → reg i → ℂ

attribute [instance] TriangleModel.fin

namespace TriangleModel

def coeff {w d} (A : TriangleModel w d) (a : ∀ i, Fin (d i)) : ℂ :=
  ∑ y : (i : Fin 3) → A.reg i, ∏ i,
    if A.outgoing i (y i) = A.incoming (i+1) (y (i+1)) then A.localWeight i (a i) (y i) else 0

private abbrev square (b : ℕ+) := fmt (b*b) (b*b) (b*b)

private def splitReg (m b : ℕ+) (i : Fin 3) (z : Fin ((m * square b i : ℕ+) : ℕ)) :
    Fin (m : ℕ) × (Fin (b : ℕ) × Fin (b : ℕ)) := by
  let y := kronDecodeEquiv (d₁ := m) (d₂ := square b i) z
  have hf : (square b i : ℕ) = (b : ℕ)*(b : ℕ) := by fin_cases i <;> rfl
  exact (y.1, finProdFinEquiv.symm (Fin.cast hf y.2))

/-- The copy label accompanies the matrix index on each edge. Its logarithm
will disappear after division by the number of powered blocks. -/
theorem of_restriction {d : Fin 3 → ℕ+} {T : KTensor ℂ d} {m b : ℕ+}
    (hr : Restricts T (kroneckerTensor (unitTensor ℂ (k := 3) m) (matMul b b b))) :
    ∃ A : TriangleModel (m*b) d, ∀ a, T a = A.coeff a := by
  classical
  obtain ⟨B,hB⟩ := hr
  let A : TriangleModel (m*b) d := {
    reg := fun i => Fin ((m * square b i : ℕ+) : ℕ)
    incoming := fun i z => finProdFinEquiv ((splitReg m b i z).1, (splitReg m b i z).2.1)
    outgoing := fun i z => finProdFinEquiv ((splitReg m b i z).1, (splitReg m b i z).2.2)
    localWeight := fun i a z => B i a z }
  refine ⟨A, fun a => ?_⟩
  rw [hB]
  apply Finset.sum_congr rfl
  intro y _
  let z (i : Fin 3) := splitReg m b i (y i)
  let edge (i : Fin 3) : Prop := (z i).1 = (z (i+1)).1 ∧ (z i).2.2 = (z (i+1)).2.1
  have hsum : ∀ i, (A.outgoing i (y i) = A.incoming (i+1) (y (i+1))) ↔ edge i := by
    intro i
    change finProdFinEquiv (_,_) = finProdFinEquiv (_,_) ↔ _
    rw [Equiv.apply_eq_iff_eq, Prod.mk.injEq]
  have heq : ((∀ i j, (z i).1 = (z j).1) ∧ ((z 0).2.2 = (z 1).2.1 ∧
      (z 1).2.2 = (z 2).2.1 ∧ (z 2).2.2 = (z 0).2.1)) ↔ ∀ i, edge i := by
    constructor
    · rintro ⟨hc,h0,h1,h2⟩ i
      refine ⟨hc _ _,?_⟩
      fin_cases i <;> first | exact h0 | exact h1 | exact h2
    · intro he
      have h0 := he 0
      have h1 := he 1
      have h2 := he 2
      refine ⟨?_,h0.2,h1.2,h2.2⟩
      intro i j
      fin_cases i <;> fin_cases j <;> first | rfl | exact h0.1 | exact h0.1.symm | exact h1.1 | exact h1.1.symm | exact h2.1 | exact h2.1.symm
  have src : kroneckerTensor (unitTensor ℂ (k := 3) m) (matMul b b b) y =
      (if ∀ i, edge i then 1 else 0) := by
    change (if ∀ i j, (z i).1 = (z j).1 then (1:ℂ) else 0) *
      (if ((z 0).2.2 = (z 1).2.1 ∧ (z 1).2.2 = (z 2).2.1 ∧ (z 2).2.2 = (z 0).2.1)
        then 1 else 0) = _
    split_ifs <;> norm_num <;> tauto
  rw [src]
  simp_rw [hsum]
  by_cases he : ∀ i, edge i
  · simp [he, A]
  · obtain ⟨i,hi⟩ := not_forall.mp he
    rw [if_neg he, mul_zero]
    exact (Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)).symm

end TriangleModel

/-- The regrouped power with its canonical word indices, in any number of parties. -/
def blockPower {k : ℕ} {d : Fin k → ℕ+} (T : KTensor ℂ d) (n : ℕ+) :
    KTensor ℂ (formatPow d n) := fun a => ∏ j, T (sliceFun d n a j)

lemma class_blockPower {k : ℕ} [NeZero k] {d : Fin k → ℕ+} (T : KTensor ℂ d) (n : ℕ+) :
    TensorClass.mk ⟨_, blockPower T n⟩ = (TensorClass.mk ⟨d,T⟩ : TensorClass ℂ k)^(n : ℕ) := by
  rw [← Foundations.AsympRankBridge.mk_regrouping_pow T n]
  congr 2
  funext a
  exact (regroupingMap_tprod_apply d n (fun _ => T) a).symm

/-- A concrete equal-width triangle after any positive number of repetitions
of one rational comparison. -/
theorem powered_triangle_model {d : Fin 3 → ℕ+} (T : KTensor ℂ d)
    {k l n m : ℕ+} (h : (OmegaBridge.pF ℂ).rel
      ((TensorClass.mk ⟨_,kronPow T k⟩)^ (n : ℕ))
      ((TensorClass.mk ⟨_,kronPow (matMul (F := ℂ) 2 2 2) l⟩ ^ (n : ℕ)) * ((m : ℕ) : TensorClass ℂ 3))) :
    let b := OmegaBridge.powTwoPNat ((l : ℕ)*(n : ℕ))
    ∃ A : TriangleModel (m*b) (formatPow d (k*n)), ∀ a, blockPower T (k*n) a = A.coeff a := by
  intro b
  apply TriangleModel.of_restriction (b := b) (m := m)
  change (OmegaBridge.pF ℂ).rel (TensorClass.mk ⟨_, blockPower T (k*n)⟩)
    (TensorClass.mk ⟨_,kroneckerTensor (unitTensor ℂ m) (matMul b b b)⟩)
  rw [class_blockPower]
  change (OmegaBridge.pF ℂ).rel _ ((TensorClass.mk ⟨_,unitTensor ℂ (k := 3) m⟩) * (TensorClass.mk ⟨_,matMul b b b⟩))
  have mm : (TensorClass.mk ⟨_,matMul (F := ℂ) b b b⟩ : TensorClass ℂ 3) =
      (TensorClass.mk ⟨_,matMul (F := ℂ) 2 2 2⟩)^((l : ℕ)*(n : ℕ)) := by
    have hp : 0 < (l : ℕ)*(n : ℕ) := Nat.mul_pos l.pos n.pos
    obtain ⟨j,hj⟩ := Nat.exists_eq_succ_of_ne_zero hp.ne'
    dsimp only [b]; rw [hj]; exact OmegaBridge.matMul_two_pow_class_succ j
  have unit : (TensorClass.mk ⟨_,unitTensor ℂ (k := 3) m⟩ : TensorClass ℂ 3) = ((m : ℕ) : TensorClass ℂ 3) := by
    rw [natCast_eq_unitClass, unitClass, dif_pos m.pos]
    rfl
  simpa only [DegenAsymp.mk_kronPow, ← pow_mul, PNat.mul_coe, unit, mm, mul_comm] using! h

end OM.NNN34
