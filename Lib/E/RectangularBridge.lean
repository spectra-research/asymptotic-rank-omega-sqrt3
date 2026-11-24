import Lib.Tensor.ModeMaps
import Foundations.Tensors.Coordinates
import Lib.OM.PolMul.DegenAsymp

namespace Lib.E
noncomputable section
open scoped BigOperators Classical
open Semicontinuity Foundations.HyperbolicLift AsymptoticSpectrumDuality

variable {F : Type*} [Field F]
variable {I J H A B O : Type*}
variable {ni nj nh na nb no : ℕ+}

/-- Selecting one index map on each leg is a tensor restriction. -/
theorem restricts_of_indices {dS dT : Fin 3 → ℕ+}
    {S : KTensor F dS} {T : KTensor F dT}
    (f : ∀ i, Fin (dS i) → Fin (dT i))
    (h : ∀ g, S g = T (fun i => f i (g i))) : Restricts S T := by
  refine ⟨fun i a b => if f i a = b then 1 else 0, ?_⟩
  intro g
  rw [Finset.sum_eq_single (fun i => f i (g i))]
  · simp [h g]
  · intro j _ hj
    have hn : ∃ i, f i (g i) ≠ j i := by
      by_contra hn
      push Not at hn
      exact hj (funext fun i => (hn i).symm)
    obtain ⟨i, hi⟩ := hn
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi), zero_mul]
  · simp

def tensorToK (ei : Fin ni ≃ I) (ej : Fin nj ≃ J) (eh : Fin nh ≃ H)
    (S : CoordinateTensor.Tensor F I J H) : KTensor F (![ni, nj, nh] : Fin 3 → ℕ+) :=
  fun g => S (ei (g 0)) (ej (g 1)) (eh (g 2))

theorem contraction_tensorToK [Fintype I] [Fintype J] [Fintype H]
    (ei : Fin ni ≃ I) (ej : Fin nj ≃ J) (eh : Fin nh ≃ H)
    (ea : Fin na ≃ A) (eb : Fin nb ≃ B) (eo : Fin no ≃ O)
    (S : CoordinateTensor.Tensor F I J H)
    (U : A → I → Polynomial F) (V : B → J → Polynomial F) (W : O → H → Polynomial F)
    (g : ∀ i, Fin ((![na, nb, no] : Fin 3 → ℕ+) i)) :
    (∑ s : ∀ i, Fin ((![ni, nj, nh] : Fin 3 → ℕ+) i),
      (∏ i, legTriple (dS := ![na, nb, no]) (d := ![ni, nj, nh])
        (fun a b => U (ea a) (ei b)) (fun a b => V (eb a) (ej b))
        (fun a b => W (eo a) (eh b)) i (g i) (s i)) *
          Polynomial.C (tensorToK ei ej eh S s)) =
      CoordinateTensor.mapTensor U V W (CoordinateTensor.polyLift S)
        (ea (g 0)) (eb (g 1)) (eo (g 2)) := by
  rw [sum_pi_fin3]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one,
    legTriple_zero, legTriple_one, legTriple_two,
    idx3_zero, idx3_one, idx3_two, tensorToK,
    CoordinateTensor.mapTensor, CoordinateTensor.polyLift]
  simp_rw [← mul_assoc]
  refine Fintype.sum_equiv ei _ _ (fun i => ?_)
  refine Fintype.sum_equiv ej _ _ (fun j => ?_)
  exact Fintype.sum_equiv eh _ _ (fun h => rfl)

/-- Encode a polynomial degeneration of rectangular tensors by its leading coefficient. -/
theorem borderDegen_tensorToK [Fintype I] [Fintype J] [Fintype H]
    (ei : Fin ni ≃ I) (ej : Fin nj ≃ J) (eh : Fin nh ≃ H)
    (ea : Fin na ≃ A) (eb : Fin nb ≃ B) (eo : Fin no ≃ O)
    {S : CoordinateTensor.Tensor F I J H} {X : CoordinateTensor.Tensor F A B O}
    (h : CoordinateTensor.Degenerates S X) :
    ∃ q, OM.PolMul.DegenAsymp.Leading (tensorToK ea eb eo X) (tensorToK ei ej eh S) q := by
  obtain ⟨q, U, V, W, h⟩ := h
  refine ⟨q, OM.PolMul.DegenAsymp.leading_of_coeff q (legTriple
    (fun a b => U (ea a) (ei b)) (fun a b => V (eb a) (ej b))
    (fun a b => W (eo a) (eh b))) ?_ ?_⟩
  · intro g d hd
    rw [OM.PolMul.DegenAsymp.contraction, contraction_tensorToK]
    exact (h _ _ _).2 d hd
  · intro g
    rw [OM.PolMul.DegenAsymp.contraction, contraction_tensorToK]
    exact (h _ _ _).1

/-- Spectral monotonicity of the rectangular polynomial certificate. -/
theorem eval_tensorToK_mono [Fintype I] [Fintype J] [Fintype H]
    (ei : Fin ni ≃ I) (ej : Fin nj ≃ J) (eh : Fin nh ≃ H)
    (ea : Fin na ≃ A) (eb : Fin nb ≃ B) (eo : Fin no ≃ O)
    {S : CoordinateTensor.Tensor F I J H} {X : CoordinateTensor.Tensor F A B O}
    (h : CoordinateTensor.Degenerates S X)
    (φ : AsymptoticSpectrum (tensorStrassenPreorder (F := F) (k := 3) (by omega))) :
    AsymptoticSpectrum.eval _ (TensorClass.mk ⟨_, tensorToK ea eb eo X⟩) φ ≤
      AsymptoticSpectrum.eval _ (TensorClass.mk ⟨_, tensorToK ei ej eh S⟩) φ := by
  obtain ⟨_, hlead⟩ := borderDegen_tensorToK ei ej eh ea eb eo h
  exact hlead.eval_le φ

end
end Lib.E
