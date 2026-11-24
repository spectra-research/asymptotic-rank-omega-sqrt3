import Lib.OM.NNN.SquareSource
import Foundations.Tensors.Coordinates

noncomputable section
open scoped BigOperators Classical
set_option maxHeartbeats 1000000

namespace OM.NNN.Raw

open CoordinateTensor Semicontinuity Foundations.HyperbolicLift Foundations.PairUnitExponents

theorem value_squareSource (φ : PolMul.Spectral ℂ) {X R : Type}
    [Fintype X] [Fintype R] {n m : ℕ+} (e : Fin n ≃ X) (f : Fin m ≃ R) :
    value φ (squareSource X R) = PolMul.Spectral.eval φ (PolMul.matMul n m n) := by
  let e0 : Fin (n * m : ℕ+) ≃ X × R :=
    finProdFinEquiv.symm.trans (Equiv.prodCongr e f)
  let e1 : Fin (m * n : ℕ+) ≃ X × R :=
    finProdFinEquiv.symm.trans ((Equiv.prodComm _ _).trans (Equiv.prodCongr e f))
  let e2 : Fin (n * n : ℕ+) ≃ X × X :=
    finProdFinEquiv.symm.trans ((Equiv.prodComm _ _).trans (Equiv.prodCongr e e))
  have h := value_reindex φ (squareSource X R) e0 e1 e2
  have he : (fun a b c => squareSource X R (e0 a) (e1 b) (e2 c)) =
      (fun a b c => PolMul.matMul (F := ℂ) n m n (idx3 a b c)) := by
    funext a b c
    let p : Fin n × Fin m := finProdFinEquiv.symm a
    let q : Fin m × Fin n := finProdFinEquiv.symm b
    let r : Fin n × Fin n := finProdFinEquiv.symm c
    change (if e p.1 = e r.2 ∧ e q.2 = e r.1 ∧ f p.2 = f q.1 then (1 : ℂ) else 0) =
      (if p.2 = q.1 ∧ q.2 = r.1 ∧ r.2 = p.1 then 1 else 0)
    simp only [e.injective.eq_iff, f.injective.eq_iff]
    congr 1
    simp [eq_comm, and_comm, and_left_comm, and_assoc]
  rw [he, value_encode φ (PolMul.matMul n m n)] at h
  exact h.symm

theorem value_cubeSquare (φ : PolMul.Spectral ℂ) {X : Type} [Fintype X]
    {n : ℕ+} (e : Fin n ≃ X) (T : Cube ℂ X) :
    value φ (tensorProduct T T) = value φ T ^ 2 := by
  let S : KTensor ℂ (fun _ : Fin 3 => n) :=
    fun g => T (e (g 0)) (e (g 1)) (e (g 2))
  have hv : value φ T = PolMul.Spectral.eval φ S := by
    rw [← value_reindex φ T e e e]
    exact value_encode φ S
  let f : Fin (n * n : ℕ+) ≃ X × X :=
    kronDecodeEquiv.trans (Equiv.prodCongr e e)
  have h := value_reindex φ (tensorProduct T T) f f f
  have he : (fun a b c => tensorProduct T T (f a) (f b) (f c)) =
      (fun a b c => (S ⊠ S) (idx3 a b c)) := by
    funext a b c
    rw [Foundations.CornerSquare.kron_idx3]
    rfl
  rw [he, value_encode φ (S ⊠ S)] at h
  rw [← h, hv, pow_two]
  exact φ.map_mul (TensorClass.mk ⟨_, S⟩) (TensorClass.mk ⟨_, S⟩)

end OM.NNN.Raw
