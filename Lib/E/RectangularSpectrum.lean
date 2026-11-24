import Lib.E.RectangularBridge

/-! The coordinate tensor operations, with independent mode dimensions,
as operations in the existing tensor-class semiring. -/

namespace Lib.E.RectangularSpectrum
noncomputable section
open scoped BigOperators Classical Semicontinuity
open Semicontinuity Foundations.HyperbolicLift AsymptoticSpectrumDuality

private theorem forall_three (P : Fin 3 → Prop) : (∀ i, P i) ↔ P 0 ∧ P 1 ∧ P 2 := by
  constructor
  · intro h
    exact ⟨h 0, h 1, h 2⟩
  · rintro ⟨h0, h1, h2⟩ i
    fin_cases i <;> assumption

private def prodEnum {I J : Type} {n m : ℕ+} (e : Fin n ≃ I) (f : Fin m ≃ J) :
    Fin (n * m : ℕ+) ≃ I × J :=
  kronDecodeEquiv.trans (Equiv.prodCongr e f)

private def sumEnum {I J : Type} {n m : ℕ+} (e : Fin n ≃ I) (f : Fin m ≃ J) :
    Fin (n + m : ℕ+) ≃ I ⊕ J :=
  (finCongr (PNat.add_coe n m)).trans
    (finSumFinEquiv.symm.trans (Equiv.sumCongr e f))

abbrev size (I : Type) [Fintype I] [Nonempty I] : ℕ+ :=
  ⟨Fintype.card I, Fintype.card_pos⟩

def enumeration (I : Type) [Fintype I] [Nonempty I] : Fin (size I) ≃ I :=
  (Fintype.equivFin I).symm

def cls {I J H : Type} [Fintype I] [Fintype J] [Fintype H]
    [Nonempty I] [Nonempty J] [Nonempty H] (S : CoordinateTensor.Tensor ℂ I J H) :
    TensorClass ℂ 3 :=
  TensorClass.mk ⟨_, tensorToK (enumeration I) (enumeration J) (enumeration H) S⟩

def indices {d e : Fin 3 → ℕ+}
    (f : Fin (d 0) → Fin (e 0)) (g : Fin (d 1) → Fin (e 1))
    (h : Fin (d 2) → Fin (e 2)) : ∀ i, Fin (d i) → Fin (e i) :=
  Fin.cases f (Fin.cases g (Fin.cases h (fun i => Fin.elim0 i)))

@[simp] theorem indices_zero {d e : Fin 3 → ℕ+}
    (f : Fin (d 0) → Fin (e 0)) (g : Fin (d 1) → Fin (e 1))
    (h : Fin (d 2) → Fin (e 2)) : indices f g h 0 = f := rfl

@[simp] theorem indices_one {d e : Fin 3 → ℕ+}
    (f : Fin (d 0) → Fin (e 0)) (g : Fin (d 1) → Fin (e 1))
    (h : Fin (d 2) → Fin (e 2)) : indices f g h 1 = g := rfl

@[simp] theorem indices_two {d e : Fin 3 → ℕ+}
    (f : Fin (d 0) → Fin (e 0)) (g : Fin (d 1) → Fin (e 1))
    (h : Fin (d 2) → Fin (e 2)) : indices f g h 2 = h := rfl

theorem cls_eq {I J H : Type} [Fintype I] [Fintype J] [Fintype H]
    [Nonempty I] [Nonempty J] [Nonempty H]
    (S : CoordinateTensor.Tensor ℂ I J H) {d : Fin 3 → ℕ+} (T : KTensor ℂ d)
    (ei : Fin (d 0) ≃ I) (ej : Fin (d 1) ≃ J) (eh : Fin (d 2) ≃ H)
    (h : ∀ idx, T idx = S (ei (idx 0)) (ej (idx 1)) (eh (idx 2))) :
    cls S = TensorClass.mk ⟨d, T⟩ := by
  apply TensorClass.mk_eq_of_equiv
  constructor
  · apply restricts_of_indices (indices
      (ei.symm ∘ enumeration I) (ej.symm ∘ enumeration J) (eh.symm ∘ enumeration H))
    intro idx
    simp [h, tensorToK]
  · apply restricts_of_indices (indices
      ((enumeration I).symm ∘ ei) ((enumeration J).symm ∘ ej)
      ((enumeration H).symm ∘ eh))
    intro idx
    simp [h, tensorToK]

theorem cls_eq_tensorToK {I J H : Type} [Fintype I] [Fintype J] [Fintype H]
    [Nonempty I] [Nonempty J] [Nonempty H]
    (S : CoordinateTensor.Tensor ℂ I J H) {a b c : ℕ+}
    (ei : Fin a ≃ I) (ej : Fin b ≃ J) (eh : Fin c ≃ H) :
    cls S = TensorClass.mk ⟨_, tensorToK ei ej eh S⟩ :=
  cls_eq S _ ei ej eh (fun _ => rfl)

section Operations
variable {I J H A B O : Type}
variable [Fintype I] [Fintype J] [Fintype H]
variable [Fintype A] [Fintype B] [Fintype O]
variable [Nonempty I] [Nonempty J] [Nonempty H]
variable [Nonempty A] [Nonempty B] [Nonempty O]

theorem cls_reindex (ei : I ≃ A) (ej : J ≃ B) (eh : H ≃ O)
    (S : CoordinateTensor.Tensor ℂ A B O) :
    cls (CoordinateTensor.restrict S ei ej eh) = cls S := by
  rw [cls_eq_tensorToK S ((enumeration I).trans ei) ((enumeration J).trans ej)
    ((enumeration H).trans eh)]
  rfl

theorem cls_mul (S : CoordinateTensor.Tensor ℂ I J H) (T : CoordinateTensor.Tensor ℂ A B O) :
    cls (CoordinateTensor.tensorProduct S T) = cls S * cls T := by
  change cls _ = TensorClass.mk ⟨_,
    tensorToK (enumeration I) (enumeration J) (enumeration H) S ⊠
    tensorToK (enumeration A) (enumeration B) (enumeration O) T⟩
  apply cls_eq _ _
    (prodEnum (enumeration I) (enumeration A))
    (prodEnum (enumeration J) (enumeration B))
    (prodEnum (enumeration H) (enumeration O))
  intro idx
  rw [kron_apply]
  rfl

theorem cls_add (S : CoordinateTensor.Tensor ℂ I J H) (T : CoordinateTensor.Tensor ℂ A B O) :
    cls (CoordinateTensor.directSum S T) = cls S + cls T := by
  change cls _ = TensorClass.mk ⟨_,
    tensorToK (enumeration I) (enumeration J) (enumeration H) S ⊕ₜ
    tensorToK (enumeration A) (enumeration B) (enumeration O) T⟩
  apply cls_eq _ _
    (sumEnum (enumeration I) (enumeration A))
    (sumEnum (enumeration J) (enumeration B))
    (sumEnum (enumeration H) (enumeration O))
  intro idx
  rw [← idx3_eta idx]
  generalize idx 0 = a, idx 1 = b, idx 2 = c
  refine Fin.addCases (fun a => ?_) (fun a => ?_) a <;>
    refine Fin.addCases (fun b => ?_) (fun b => ?_) b <;>
    refine Fin.addCases (fun c => ?_) (fun c => ?_) c
  all_goals
    rename_i a b c
    simp only [tensorToK, directSumTensor_apply_block', forall_three, idx3_zero,
      idx3_one, idx3_two]
    simp! [CoordinateTensor.directSum, sumEnum, finSumFinEquiv, Fin.addCases,
      a.isLt, b.isLt, c.isLt, Nat.not_le_of_lt a.isLt,
      Nat.not_le_of_lt b.isLt, Nat.not_le_of_lt c.isLt]

theorem eval_mono (φ : OM.PolMul.Spectral ℂ) {S : CoordinateTensor.Tensor ℂ I J H}
    {T : CoordinateTensor.Tensor ℂ A B O} (h : CoordinateTensor.Degenerates S T) :
    AsymptoticSpectrum.eval _ (cls T) φ ≤
      AsymptoticSpectrum.eval _ (cls S) φ :=
  eval_tensorToK_mono (enumeration I) (enumeration J) (enumeration H)
    (enumeration A) (enumeration B) (enumeration O) h φ

end Operations

end
end Lib.E.RectangularSpectrum
