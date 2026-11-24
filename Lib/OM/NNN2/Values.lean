import Lib.OM.NNN2.Cancellation
import Lib.OM.NNN.SourceValues
import Lib.OM.NNN.EdgeValues

noncomputable section
open scoped BigOperators Classical
set_option maxHeartbeats 1000000
namespace OM.NNN2
open CoordinateTensor OM.NNN.Raw Semicontinuity Foundations.HyperbolicLift Foundations.PairUnitExponents

variable {I J K I' J' K' : Type}

/-- Rectangular Kronecker products have their exact multiplicative spectral value. -/
theorem value_product [Fintype I] [Fintype J] [Fintype K]
    [Fintype I'] [Fintype J'] [Fintype K']
    {d d' : Fin 3 → ℕ+}
    (e0 : Fin (d 0) ≃ I) (e1 : Fin (d 1) ≃ J) (e2 : Fin (d 2) ≃ K)
    (f0 : Fin (d' 0) ≃ I') (f1 : Fin (d' 1) ≃ J') (f2 : Fin (d' 2) ≃ K')
    (φ : PolMul.Spectral ℂ) (S : Tensor ℂ I J K) (T : Tensor ℂ I' J' K') :
    value φ (tensorProduct S T) = value φ S * value φ T := by
  let S' : KTensor ℂ d := fun g => S (e0 (g 0)) (e1 (g 1)) (e2 (g 2))
  let T' : KTensor ℂ d' := fun g => T (f0 (g 0)) (f1 (g 1)) (f2 (g 2))
  have hs : value φ S = PolMul.Spectral.eval φ S' := by
    rw [← value_reindex φ S e0 e1 e2]
    exact value_encode φ S'
  have ht : value φ T = PolMul.Spectral.eval φ T' := by
    rw [← value_reindex φ T f0 f1 f2]
    exact value_encode φ T'
  let g0 := kronDecodeEquiv.trans (Equiv.prodCongr e0 f0)
  let g1 := kronDecodeEquiv.trans (Equiv.prodCongr e1 f1)
  let g2 := kronDecodeEquiv.trans (Equiv.prodCongr e2 f2)
  have h := value_reindex φ (tensorProduct S T) g0 g1 g2
  have he : (fun a b c => tensorProduct S T (g0 a) (g1 b) (g2 c)) =
      (fun a b c => (S' ⊠ T') (idx3 a b c)) := by
    funext a b c
    rw [Foundations.CornerSquare.kron_idx3]
    rfl
  rw [he, value_encode φ (S' ⊠ T')] at h
  rw [← h, hs, ht]
  exact φ.map_mul (TensorClass.mk ⟨_, S'⟩) (TensorClass.mk ⟨_, T'⟩)

/-- Coordinate convention `K(|X|,|Y|,|R|)`. -/
def mm (X Y R : Type) : Tensor ℂ (X × R) (Y × R) (X × Y) :=
  fun i j k => if i.1 = k.1 ∧ j.1 = k.2 ∧ i.2 = j.2 then 1 else 0

theorem value_mm (φ : PolMul.Spectral ℂ) {X Y R : Type}
    [Fintype X] [Fintype Y] [Fintype R] {n p m : ℕ+}
    (e : Fin n ≃ X) (f : Fin p ≃ Y) (g : Fin m ≃ R) :
    value φ (mm X Y R) =
      (n : ℝ) ^ theta φ 1 * (m : ℝ) ^ theta φ 2 * (p : ℝ) ^ theta φ 0 := by
  let e0 : Fin (n * m : ℕ+) ≃ X × R :=
    finProdFinEquiv.symm.trans (Equiv.prodCongr e g)
  let e1 : Fin (m * p : ℕ+) ≃ Y × R :=
    finProdFinEquiv.symm.trans ((Equiv.prodComm _ _).trans (Equiv.prodCongr f g))
  let e2 : Fin (p * n : ℕ+) ≃ X × Y :=
    finProdFinEquiv.symm.trans ((Equiv.prodComm _ _).trans (Equiv.prodCongr e f))
  have h := value_reindex φ (mm X Y R) e0 e1 e2
  have he : (fun a b c => mm X Y R (e0 a) (e1 b) (e2 c)) =
      (fun a b c => PolMul.matMul (F := ℂ) n m p (idx3 a b c)) := by
    funext a b c
    let a' : Fin n × Fin m := finProdFinEquiv.symm a
    let b' : Fin m × Fin p := finProdFinEquiv.symm b
    let c' : Fin p × Fin n := finProdFinEquiv.symm c
    change (if e a'.1 = e c'.2 ∧ f b'.2 = f c'.1 ∧ g a'.2 = g b'.1 then (1 : ℂ) else 0) =
      (if a'.2 = b'.1 ∧ b'.2 = c'.1 ∧ c'.2 = a'.1 then 1 else 0)
    simp only [e.injective.eq_iff, f.injective.eq_iff, g.injective.eq_iff]
    congr 1
    simp [eq_comm, and_comm, and_left_comm, and_assoc]
  rw [he, value_encode, Omega.eval_matMul] at h
  exact h.symm

def unitProd (A : Type) : A ≃ Unit × A where
  toFun a := ((), a)
  invFun a := a.2
  left_inv _ := rfl
  right_inv a := by rcases a with ⟨⟨⟩, a⟩; rfl

def prodUnit (A : Type) : A ≃ A × Unit :=
  (unitProd A).trans (Equiv.prodComm _ _)

theorem value_auxLeft (φ : PolMul.Spectral ℂ) {A H : Type}
    [Fintype A] [Fintype H] {n h : ℕ+} (e : Fin n ≃ A) (f : Fin h ≃ H) :
    value φ (auxLeft A H) = (n : ℝ) ^ theta φ 2 * (h : ℝ) ^ theta φ 0 := by
  have hr := value_reindex φ (mm Unit H A) (unitProd A) (Equiv.prodComm A H) (unitProd H)
  have he : (fun a b c => mm Unit H A (unitProd A a) ((Equiv.prodComm A H) b)
      (unitProd H c)) = auxLeft A H := by
    funext a b c
    simp [mm, auxLeft, unitProd, and_comm]
  rw [he, value_mm φ (n := 1) (p := h) (m := n) (Equiv.ofUnique (Fin 1) Unit) f e] at hr
  simpa using! hr

theorem value_auxRight (φ : PolMul.Spectral ℂ) {B H : Type}
    [Fintype B] [Fintype H] {n h : ℕ+} (e : Fin n ≃ B) (f : Fin h ≃ H) :
    value φ (auxRight B H) = (n : ℝ) ^ theta φ 2 * (h : ℝ) ^ theta φ 1 := by
  have hr := value_reindex φ (mm H Unit B) (Equiv.prodComm B H) (unitProd B) (prodUnit H)
  have he : (fun a b c => mm H Unit B ((Equiv.prodComm B H) a) (unitProd B b)
      (prodUnit H c)) = auxRight B H := by
    funext a b c
    simp [mm, auxRight, unitProd, prodUnit, and_comm]
  rw [he, value_mm φ (n := h) (p := 1) (m := n) f (Equiv.ofUnique (Fin 1) Unit) e] at hr
  simpa [mul_comm] using! hr

end OM.NNN2
