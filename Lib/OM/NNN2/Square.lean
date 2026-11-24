import Lib.OM.NNN2.Values

noncomputable section
open scoped BigOperators Classical
set_option maxHeartbeats 1000000
namespace OM.NNN2
open CoordinateTensor OM.NNN.Raw Semicontinuity Foundations.HyperbolicLift Foundations.PairUnitExponents

variable {X H R : Type}

def squareLeft (T : Cube ℂ X) : (X × X) → (X × (X × X)) → ℂ :=
  fun a r => if a.2 = r.2.2 then T a.1 r.2.1 r.1 else 0

def squareRight (T : Cube ℂ X) : (X × X) → (X × (X × X)) → ℂ :=
  fun b r => if b.1 = r.2.1 then T r.2.2 b.2 r.1 else 0

def identityRows (X : Type) : X → X → ℂ := fun a b => if a = b then 1 else 0

def headRows (F : Tensor ℂ X X H) : H → (X × X) → ℂ := fun h k => F k.1 k.2 h

/-- The same ordered head tensor tensored with an edge on its first two modes. -/
def retained (F : Tensor ℂ X X H) (R : Type) : Tensor ℂ (X × R) (X × R) H :=
  fun a b h => if a.2 = b.2 then F a.1 b.1 h else 0

theorem square_payload [Fintype X] (T : Cube ℂ X) :
    mapTensor (squareLeft T) (squareRight T) (identityRows (X × X))
      (squareSource X (X × X)) = tensorProduct T T := by
  funext a b c
  simp [map_squareSource, squareLeft, squareRight, identityRows, tensorProduct,
    Fintype.sum_prod_type, Prod.ext_iff, ite_mul, mul_ite, ite_and,
    Finset.sum_ite_irrel]

theorem square_retained [Fintype X] [Fintype R] (F : Tensor ℂ X X H) :
    mapTensor (identityRows (X × R)) (identityRows (X × R)) (headRows F)
      (squareSource X R) = retained F R := by
  funext a b h
  simp [map_squareSource, identityRows, headRows, retained, Prod.ext_iff,
    ite_mul, mul_ite, ite_and, Finset.sum_ite_irrel, eq_comm]

/-- Equation (16), for arbitrary coefficients of both input and head. -/
theorem square_degeneration [Fintype X] [Fintype H]
    (T : Cube ℂ X) (F : Tensor ℂ X X H) :
    Degenerates
      (directSum (squareSource X (X × X))
        (directSum (auxLeft (X × X) H) (auxRight (X × X) H)))
      (directSum (tensorProduct T T) (retained F (X × X))) := by
  simpa only [square_payload, square_retained] using!
    arbitrary_head (squareSource X (X × X)) (squareLeft T) (squareRight T)
      (identityRows (X × X)) (identityRows (X × (X × X)))
      (identityRows (X × (X × X))) (headRows F)

theorem value_retained (φ : PolMul.Spectral ℂ) {n m : ℕ+}
    [Fintype X] [Fintype R] [Nonempty R]
    (e : Fin n ≃ X) (f : Fin m ≃ R) (T : Cube ℂ X) :
    value φ (retained T R) = value φ T * (Fintype.card R : ℝ) ^ theta φ 2 := by
  have h := value_reindex φ (tensorProduct T (pair R))
    (Equiv.refl (X × R)) (Equiv.refl (X × R)) (prodUnit X)
  have he : (fun a b c => tensorProduct T (pair R) a b (prodUnit X c)) = retained T R := by
    funext a b c
    simp [tensorProduct, pair, prodUnit, unitProd, retained, mul_ite]
  simp only [Equiv.refl_apply] at h
  rw [he] at h
  rw [h, value_product (d := fun _ => n) (d' := ![m, m, 1])
    e e e f f (Equiv.ofUnique (Fin 1) Unit), value_pair]

/-- Both inequalities in the third orientation, with exact source prices. -/
theorem square_inequalities (φ : PolMul.Spectral ℂ) (n : ℕ+)
    (T : KTensor ℂ (fun _ : Fin 3 => n)) :
    let x := PolMul.Spectral.eval φ T
    let v := fun i => (n : ℝ) ^ theta φ i
    (x ^ 2 + (v 2) ^ 2 * x ≤ v 0 * v 1 * (v 2) ^ 2 + (v 2) ^ 2 * (v 0 + v 1)) ∧
    x ^ 2 ≤ v 0 * v 1 * (v 2) ^ 2 := by
  let S : Cube ℂ (Fin n) := fun a b c => T (idx3 a b c)
  let e : Fin (n * n : ℕ+) ≃ Fin n × Fin n := finProdFinEquiv.symm
  have h := value_mono φ (square_degeneration S S)
  rw [value_add, value_add, value_add, value_cubeSquare φ (Equiv.refl _),
    value_retained φ (Equiv.refl _) e,
    value_squareSource φ (Equiv.refl _) e, Omega.eval_matMul,
    value_auxLeft φ e (Equiv.refl _), value_auxRight φ e (Equiv.refl _)] at h
  have ho := value_map_le φ (squareSource (Fin n) (Fin n × Fin n))
    (squareLeft S) (squareRight S) (identityRows (Fin n × Fin n))
  rw [square_payload, value_cubeSquare φ (Equiv.refl _),
    value_squareSource φ (Equiv.refl _) e, Omega.eval_matMul] at ho
  have hn : (0 : ℝ) ≤ (n : ℝ) := by positivity
  have hv : value φ S = PolMul.Spectral.eval φ T := value_encode φ T
  simp only [Fintype.card_prod, Fintype.card_fin, PNat.mul_coe, Nat.cast_mul,
    Real.mul_rpow hn hn, hv] at h ho
  dsimp only
  constructor <;> nlinarith [h, ho]

end OM.NNN2
