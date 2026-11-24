import Lib.OM.NNN30.Net.Cube
import Lib.OM.NNN22.NE.Labels

/-! # Spectral costs of the four-site contraction factors

A two-terminal kernel of decomposition size `r` is a restriction of the corresponding equality
tensor. Pointwise multiplication of tensors is a restriction of their Kronecker product. For the
array at the centre, padding each index set to a power of two costs at most one bit per leg. -/

noncomputable section
open scoped BigOperators Classical

namespace OM.NNN30.Net

open CoordinateTensor OM.NNN.Raw OM.NNN22 Foundations.PairUnitExponents

def bits (I : Type) [Fintype I] : ℝ := Real.logb 2 (Fintype.card I)

private lemma cost_rpow (E : Type) [Fintype E] [Nonempty E] (t : ℝ) :
    (Fintype.card E : ℝ) ^ t = (2 : ℝ) ^ (t * bits E) := by
  have hp : 0 < (Fintype.card E : ℝ) := by exact_mod_cast Fintype.card_pos
  rw [bits, mul_comm t, Real.rpow_mul (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) hp]

variable {A B C E : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype E] [Nonempty E]

lemma cost_pair01 (φ : OM.PolMul.Spectral ℂ) (L : A → E → ℂ) (R : B → E → ℂ) :
    value φ (fun a b (_ : C) => ∑ i, L a i * R b i) ≤ (2 : ℝ) ^ (theta φ 2 * bits E) := by
  let T := fun (i j : E) (_ : Unit) => if i = j then (1 : ℂ) else 0
  have h : mapTensor L R (fun (_ : C) (_ : Unit) => (1 : ℂ)) T =
      fun a b _ => ∑ i, L a i * R b i := by
    funext a b c
    simp [T, mapTensor, mul_ite]
  rw [← h]
  exact (value_map_le φ _ _ _ _).trans_eq ((value_pair2 φ).trans (cost_rpow E _))

lemma cost_pair02 (φ : OM.PolMul.Spectral ℂ) (L : A → E → ℂ) (R : C → E → ℂ) :
    value φ (fun a (_ : B) c => ∑ i, L a i * R c i) ≤ (2 : ℝ) ^ (theta φ 1 * bits E) := by
  let T := fun (i : E) (_ : Unit) (k : E) => if i = k then (1 : ℂ) else 0
  have h : mapTensor L (fun (_ : B) (_ : Unit) => (1 : ℂ)) R T =
      fun a _ c => ∑ i, L a i * R c i := by
    funext a b c
    simp [T, mapTensor, mul_ite]
  rw [← h]
  exact (value_map_le φ _ _ _ _).trans_eq ((value_pair1 φ).trans (cost_rpow E _))

lemma cost_pair12 (φ : OM.PolMul.Spectral ℂ) (L : B → E → ℂ) (R : C → E → ℂ) :
    value φ (fun (_ : A) b c => ∑ i, L b i * R c i) ≤ (2 : ℝ) ^ (theta φ 0 * bits E) := by
  let T := fun (_ : Unit) (j k : E) => if j = k then (1 : ℂ) else 0
  have h : mapTensor (fun (_ : A) (_ : Unit) => (1 : ℂ)) L R T =
      fun _ b c => ∑ i, L b i * R c i := by
    funext a b c
    simp [T, mapTensor, mul_ite]
  rw [← h]
  exact (value_map_le φ _ _ _ _).trans_eq ((value_pair0 φ).trans (cost_rpow E _))

lemma cost_pointwise [Nonempty A] [Nonempty B] [Nonempty C] (φ : OM.PolMul.Spectral ℂ)
    {T U : Tensor ℂ A B C} {t v : ℝ} (ht : value φ T ≤ (2 : ℝ) ^ t)
    (hu : value φ U ≤ (2 : ℝ) ^ v) :
    value φ (fun a b c => T a b c * U a b c) ≤ (2 : ℝ) ^ (t + v) := by
  have h := OM.NNN18.mapTensor_indicator (fun a : A => (a, a)) (fun b : B => (b, b))
    (fun c : C => (c, c)) (tensorProduct T U)
  change _ = (fun a b c => T a b c * U a b c) at h
  rw [← h, Real.rpow_add (by norm_num)]
  apply (value_map_le φ _ _ _ _).trans
  rw [OM.NNN3.value_product']
  exact mul_le_mul ht hu (φ.nonneg _) (by positivity)

/-- Padding the central array to three dyadic index sets loses at most `∑ h` in log value. -/
lemma cost_hub (φ : OM.PolMul.Spectral ℂ) (h : Fin 3 → ℝ) (hn : ∀ i, 0 ≤ h i)
    (hs : ∀ y : Fin 3 → ℝ, (∀ i, 0 ≤ y i) → Fv φ y ≤ ∑ i, h i * y i)
    (I : Fin 3 → Type) [∀ i, Fintype (I i)] [∀ i, Nonempty (I i)]
    (T : Tensor ℂ (I 0) (I 1) (I 2)) :
    value φ T ≤ (2 : ℝ) ^ ((∑ i, h i * bits (I i)) + ∑ i, h i) := by
  let w := fun i => Nat.clog 2 (Fintype.card (I i))
  have hfmt (i) : Fintype.card (I i) ≤ 2 ^ w i := Nat.le_pow_clog one_lt_two _
  apply OM.NNN20.Mix.value_le_of_card_le_at φ w _ (hfmt 0) (hfmt 1) (hfmt 2) T
  intro U
  have hw := value_le_Fv φ (y := fun i => (w i : ℝ)) (D := 1) Nat.zero_lt_one
    (w := w) (fun i => by simp) U
  simp only [Nat.cast_one, one_mul] at hw
  apply hw.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) _)
  apply (hs _ (fun i => Nat.cast_nonneg _)).trans
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  have hc := OM.NNN22.NE.clog_le (Fintype.card (I i)) Fintype.card_pos
  exact (mul_le_mul_of_nonneg_left hc (hn i)).trans_eq (by simp [bits, mul_add])

end OM.NNN30.Net
