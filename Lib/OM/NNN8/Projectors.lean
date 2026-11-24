import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Mathlib.LinearAlgebra.Trace

/-! Character projectors of a finite abelian representation. This module is
independent of tensors and does not require that the representation be faithful. -/
noncomputable section
open scoped BigOperators Classical
namespace OM.NNN8
open Module LinearMap
set_option maxHeartbeats 1000000

variable {G V : Type} [AddCommGroup G] [Fintype G]
  [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

def characterSum (P : G → Module.End ℂ V) (χ : AddChar G ℂ) : Module.End ℂ V :=
  ∑ g, χ g • P g

def characterProjector (P : G → Module.End ℂ V) (χ : AddChar G ℂ) : Module.End ℂ V :=
  (Fintype.card G : ℂ)⁻¹ • characterSum P χ

theorem characterSum_mul_self (P : G → Module.End ℂ V)
    (hadd : ∀ a b, P (a + b) = P a * P b) (χ : AddChar G ℂ) :
    characterSum P χ * characterSum P χ =
      (Fintype.card G : ℂ) • characterSum P χ := by
  calc
    _ = ∑ a : G, ∑ b : G, χ (a + b) • P (a + b) := by
      simp only [characterSum, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc,
        mul_smul_comm, Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      rw [hadd, AddChar.map_add_eq_mul, mul_comm (χ b) (χ a)]
    _ = ∑ _a : G, characterSum P χ := by
      apply Finset.sum_congr rfl
      intro a _
      exact Fintype.sum_equiv (Equiv.addLeft a) _ _ (fun _ => rfl)
    _ = _ := by simp [Nat.cast_smul_eq_nsmul]

theorem characterProjector_idempotent (P : G → Module.End ℂ V)
    (hadd : ∀ a b, P (a + b) = P a * P b) (χ : AddChar G ℂ) :
    characterProjector P χ * characterProjector P χ = characterProjector P χ := by
  have hn : (Fintype.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp only [characterProjector, smul_mul_assoc, mul_smul_comm, smul_smul,
    characterSum_mul_self P hadd]
  congr 1
  field_simp

theorem sum_characterProjector (P : G → Module.End ℂ V) (hzero : P 0 = 1) :
    ∑ χ : AddChar G ℂ, characterProjector P χ = 1 := by
  have hn : (Fintype.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp only [characterProjector, characterSum, ← Finset.smul_sum]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul, AddChar.sum_apply_eq_ite]
  simp [hzero, hn]

theorem characterProjector_trace (P : G → Module.End ℂ V)
    (hadd : ∀ a b, P (a + b) = P a * P b) (χ : AddChar G ℂ) :
    LinearMap.trace ℂ V (characterProjector P χ) =
      (finrank ℂ (LinearMap.range (characterProjector P χ)) : ℂ) := by
  apply LinearMap.IsProj.trace
  exact (LinearMap.isProj_range_iff_isIdempotentElem _).mpr
    (characterProjector_idempotent P hadd χ)

/-- The ranks of all character projectors sum to the ambient dimension. -/
theorem sum_characterProjector_rank (P : G → Module.End ℂ V) (hzero : P 0 = 1)
    (hadd : ∀ a b, P (a + b) = P a * P b) :
    (∑ χ : AddChar G ℂ, finrank ℂ (LinearMap.range (characterProjector P χ))) =
      finrank ℂ V := by
  have ht := congrArg (LinearMap.trace ℂ V) (sum_characterProjector P hzero)
  simp only [map_sum, characterProjector_trace P hadd, LinearMap.trace_one] at ht
  exact_mod_cast ht

/-- Some character has at most the average rank; no assertion is made for every character. -/
theorem exists_characterProjector_rank_le (P : G → Module.End ℂ V) (hzero : P 0 = 1)
    (hadd : ∀ a b, P (a + b) = P a * P b) :
    ∃ χ : AddChar G ℂ,
      finrank ℂ (LinearMap.range (characterProjector P χ)) * Fintype.card G ≤ finrank ℂ V := by
  have hs : (∑ χ : AddChar G ℂ,
      finrank ℂ (LinearMap.range (characterProjector P χ)) * Fintype.card G) ≤
      ∑ _χ : AddChar G ℂ, finrank ℂ V := by
    rw [← Finset.sum_mul, sum_characterProjector_rank P hzero hadd]
    simp [Nat.mul_comm]
  obtain ⟨χ, _, hχ⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty hs
  exact ⟨χ, hχ⟩

end OM.NNN8
