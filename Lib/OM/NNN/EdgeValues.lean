import Lib.OM.NNN.SquareSource

noncomputable section
open scoped BigOperators Classical
set_option maxHeartbeats 1000000

namespace OM.NNN.Raw

open CoordinateTensor Semicontinuity Foundations.HyperbolicLift Foundations.PairUnitExponents
variable {L : Type}

def pair (I : Type) : Tensor ℂ I I Unit := fun i j _ => if i = j then 1 else 0

theorem value_pair (φ : PolMul.Spectral ℂ) {I : Type} [Fintype I] [Nonempty I] :
    value φ (pair I) = (Fintype.card I : ℝ) ^ theta φ 2 := by
  let n : ℕ+ := ⟨Fintype.card I, Fintype.card_pos⟩
  let e : Fin n ≃ I := (Fintype.equivFin I).symm
  let f : Fin 1 ≃ Unit := Equiv.ofUnique _ _
  have hr := value_reindex φ (pair I) e e f
  have he : (fun a b c => pair I (e a) (e b) (f c)) =
      (fun a b c => unitPairTensor (F := ℂ) n (0 : Fin 3) 1 (by decide +kernel)
        (idx3 a b c)) := by
    funext a b c
    simp only [pair, unitPairTensor, idx3_zero, idx3_one, e.injective.eq_iff,
      Fin.ext_iff]
  rw [he, value_encode] at hr
  rw [← hr]
  have hpow := eval_orientedPairUnit_eq_rpow φ 2 n n.pos
  rw [orientedPairUnit, pairUnitTT_complementary_eq 2 n n.pos] at hpow
  exact hpow

def optionSigma (E : Option L → Type) :
    E none ⊕ (Σ l : L, E (some l)) ≃ (Σ l, E l) where
  toFun
    | .inl x => ⟨none, x⟩
    | .inr ⟨l, x⟩ => ⟨some l, x⟩
  invFun
    | ⟨none, x⟩ => .inl x
    | ⟨some l, x⟩ => .inr ⟨l, x⟩
  left_inv x := by rcases x with x | ⟨l, x⟩ <;> rfl
  right_inv x := by rcases x with ⟨(_ | l), x⟩ <;> rfl

def optionLabels (L : Type) : Unit ⊕ L ≃ Option L where
  toFun | .inl _ => none | .inr l => some l
  invFun | none => .inl () | some l => .inr l
  left_inv x := by rcases x with ⟨⟩ | l <;> rfl
  right_inv x := by cases x <;> rfl

theorem value_edges (φ : PolMul.Spectral ℂ) (L : Type) [Fintype L]
    (E : L → Type) [∀ l, Fintype (E l)] [∀ l, Nonempty (E l)] :
    value φ (edges E) = ∑ l, (Fintype.card (E l) : ℝ) ^ theta φ 2 := by
  classical
  revert E
  refine Fintype.induction_empty_option
    (P := fun L _ => ∀ (E : L → Type) [∀ l, Fintype (E l)] [∀ l, Nonempty (E l)],
      value φ (edges E) = ∑ l, (Fintype.card (E l) : ℝ) ^ theta φ 2) ?_ ?_ ?_ L
  · intro α β _ e ih E _ _
    letI : Fintype α := Fintype.ofEquiv β e.symm
    have h := value_reindex φ (edges E) (Equiv.sigmaCongrLeft e)
      (Equiv.sigmaCongrLeft e) e
    have he : (fun a b c => edges E (Equiv.sigmaCongrLeft e a)
        (Equiv.sigmaCongrLeft e b) (e c)) = edges (fun a => E (e a)) := by
      funext a b c
      change (if (Equiv.sigmaCongrLeft e) a = (Equiv.sigmaCongrLeft e) b ∧
          e a.1 = e c then (1 : ℂ) else 0) = (if a = b ∧ a.1 = c then 1 else 0)
      simp only [(Equiv.sigmaCongrLeft e).injective.eq_iff, e.injective.eq_iff]
    rw [he, ih] at h
    rw [← h]
    exact Fintype.sum_equiv e _ _ (fun _ => rfl)
  · intro E _ _
    have h : edges E = 0 := by funext a; exact a.1.elim
    simp [h, value_zero]
  · intro α _ ih E _ _
    have h := value_reindex φ (edges E) (optionSigma E) (optionSigma E) (optionLabels α)
    have he : (fun a b c => edges E (optionSigma E a) (optionSigma E b)
        (optionLabels α c)) = directSum (pair (E none)) (edges (fun l => E (some l))) := by
      funext a b c
      rcases a with a | ⟨i, a⟩ <;> rcases b with b | ⟨j, b⟩ <;>
        rcases c with ⟨⟩ | c <;>
        simp [edges, pair, optionSigma, optionLabels, directSum, Sigma.mk.inj_iff]
    rw [he, value_add, value_pair, ih] at h
    rw [← h, Fintype.sum_option]

end OM.NNN.Raw
