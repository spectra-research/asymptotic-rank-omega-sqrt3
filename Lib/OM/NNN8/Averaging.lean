import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.GroupTheory.Coset.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-! Exact finite averaging over all linear generator maps. Dependent generators
are retained; the tensor lemmas charge their nonzero messages, even if their
image is zero. No probabilistic or asymptotic coding theorem is assumed. -/
noncomputable section
open scoped BigOperators Classical
namespace OM.NNN8
set_option maxHeartbeats 1000000

lemma sum_surjective_addHom {A B : Type} [AddCommGroup A] [AddCommGroup B]
    [Fintype A] [Fintype B] (f : A →+ B) (hf : Function.Surjective f) (w : B → ℝ) :
    (∑ a, w (f a)) * Fintype.card B = (Fintype.card A : ℝ) * ∑ b, w b := by
  have hsum (v : B → ℝ) : (∑ a, v (f a)) = (Fintype.card f.ker : ℝ) * ∑ b, v b := by
    rw [← Fintype.sum_fiberwise' f v, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    have hc : Fintype.card {a // f a = b} = Fintype.card f.ker :=
      Fintype.card_congr (AddMonoidHom.fiberEquivKerOfSurjective hf b)
    simp [hc]
  have hc := hsum (fun _ => 1)
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at hc
  rw [hsum, hc]
  ring

section Linear
variable {K V W : Type} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W] [Fintype V] [Fintype W]

local instance : Fintype (V →ₗ[K] W) := Fintype.ofInjective DFunLike.coe DFunLike.coe_injective

def generatorEval (v : V) : (V →ₗ[K] W) →+ W where
  toFun f := f v
  map_zero' := rfl
  map_add' _ _ := rfl

lemma generatorEval_surjective {v : V} (hv : v ≠ 0) :
    Function.Surjective (generatorEval (K := K) (W := W) v) := by
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one K hv
  intro w
  refine ⟨f.smulRight w, ?_⟩
  simp [generatorEval, hf]

/-- Every nonzero message has a uniformly distributed image under all linear maps. -/
theorem sum_generator_image {v : V} (hv : v ≠ 0) (w : W → ℝ) :
    (∑ f : V →ₗ[K] W, w (f v)) * Fintype.card W =
      (Fintype.card (V →ₗ[K] W) : ℝ) * ∑ y, w y :=
  sum_surjective_addHom (generatorEval v) (generatorEval_surjective hv) w

/-- A single generator map attains the exact mean nonzero-message cost. -/
theorem exists_generator_sum_le [DecidableEq V] (w : W → ℝ) :
    ∃ f : V →ₗ[K] W,
      (∑ v ∈ Finset.univ.erase (0 : V), w (f v)) ≤
        ((Fintype.card V : ℝ) - 1) / Fintype.card W * ∑ y, w y := by
  have hnW : (0 : ℝ) < Fintype.card W := Nat.cast_pos.mpr Fintype.card_pos
  have hs : (∑ f : V →ₗ[K] W, ∑ v ∈ Finset.univ.erase (0 : V), w (f v)) *
      Fintype.card W =
      (Fintype.card (V →ₗ[K] W) : ℝ) * ((Fintype.card V : ℝ) - 1) * ∑ y, w y := by
    rw [Finset.sum_comm, Finset.sum_mul]
    have he (v : V) (hv : v ∈ Finset.univ.erase (0 : V)) :=
      sum_generator_image (K := K) (Finset.mem_erase.mp hv).1 w
    rw [Finset.sum_congr rfl he]
    simp only [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ (0 : V)),
      Finset.card_univ, nsmul_eq_mul, Nat.cast_sub (Fintype.card_pos : 0 < Fintype.card V),
      Nat.cast_one]
    ring
  have hmean : (∑ f : V →ₗ[K] W, ∑ v ∈ Finset.univ.erase (0 : V), w (f v)) ≤
      ∑ _f : V →ₗ[K] W,
        ((Fintype.card V : ℝ) - 1) / Fintype.card W * ∑ y, w y := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    apply le_of_eq
    apply mul_right_cancel₀ hnW.ne'
    rw [hs]
    field_simp
  obtain ⟨f, _, hf⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty hmean
  exact ⟨f, hf⟩
end Linear

end OM.NNN8
