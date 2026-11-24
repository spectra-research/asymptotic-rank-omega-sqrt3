/- Adapted from PolMul/SpectralFacts/SP5.lean of an earlier formalisation
   (commit 51c6e6b6e8b8d7226c6a828dba618ae1de5b5f8a).
   Uses Foundations tensor definitions; declarations are renamed under OM. -/
import Lib.OM.PolMul.SpectralFacts.Basic
import Lib.OM.PolMul.SpectralFacts.Tensors

namespace OM.PolMul.SpectralFacts

open AsymptoticSpectrumDuality
open Semicontinuity
open OM.PolMulDef

universe u

private lemma pair_two_bounds {F : Type u} [Field F]
    (Fspec : Semicontinuity.SpectralPoint 3 F)
    (i j : Fin 3) (hij : i ≠ j) :
    1 ≤ Fspec.toFun (unitPairTensor (F := F) 2 i j hij) ∧
      Fspec.toFun (unitPairTensor (F := F) 2 i j hij) ≤ 2 := by
  constructor
  · have hmono := Fspec.mono
        (unitPairTensor (F := F) 1 i j hij)
        (unitPairTensor (F := F) 2 i j hij)
        (unitPairTensor_restricts_of_le (F := F) i j hij (by norm_num))
    simpa [Fspec.unitPair_one i j hij] using! hmono
  · calc
      Fspec.toFun (unitPairTensor (F := F) 2 i j hij) ≤
          Fspec.toFun (unitTensor F (k := 3) 2) :=
        Fspec.mono _ _ (unitPair_restricts_unitTensor (F := F) 2 i j hij)
      _ = 2 := by simpa using! Fspec.normalize (2 : ℕ+)

theorem proof_SP_5 : OM_S_SP_5 := by
  intro F _instF φ
  let Fspec : Semicontinuity.SpectralPoint 3 F :=
    ofAbstractSpectralPoint (K := F) (k := 3) (by norm_num) φ
  have h112 : 1 ≤ Spectral.eval φ (matMul (F := F) 1 1 2) ∧
      Spectral.eval φ (matMul (F := F) 1 1 2) ≤ 2 := by
    change 1 ≤ Fspec.toFun (matMul (F := F) 1 1 2) ∧
      Fspec.toFun (matMul (F := F) 1 1 2) ≤ 2
    rw [eval_matMul_11n_eq_pair]
    exact pair_two_bounds Fspec 1 2 (by decide +kernel)
  have h211 : 1 ≤ Spectral.eval φ (matMul (F := F) 2 1 1) ∧
      Spectral.eval φ (matMul (F := F) 2 1 1) ≤ 2 := by
    change 1 ≤ Fspec.toFun (matMul (F := F) 2 1 1) ∧
      Fspec.toFun (matMul (F := F) 2 1 1) ≤ 2
    rw [eval_matMul_n11_eq_pair]
    exact pair_two_bounds Fspec 0 2 (by decide +kernel)
  have h121 : 1 ≤ Spectral.eval φ (matMul (F := F) 1 2 1) ∧
      Spectral.eval φ (matMul (F := F) 1 2 1) ≤ 2 := by
    change 1 ≤ Fspec.toFun (matMul (F := F) 1 2 1) ∧
      Fspec.toFun (matMul (F := F) 1 2 1) ≤ 2
    rw [eval_matMul_1n1_eq_pair]
    exact pair_two_bounds Fspec 0 1 (by decide +kernel)
  refine ⟨h112, h211, h121, ?_⟩
  intro n₁ n₂ n₃
  change Fspec.toFun (matMul (F := F) n₁ n₂ n₃) =
    Fspec.toFun (matMul (F := F) 2 1 1) ^ Real.logb 2 (((n₁ : ℕ) : ℝ)) *
    Fspec.toFun (matMul (F := F) 1 2 1) ^ Real.logb 2 (((n₂ : ℕ) : ℝ)) *
    Fspec.toFun (matMul (F := F) 1 1 2) ^ Real.logb 2 (((n₃ : ℕ) : ℝ))
  have hn₁ := unitPair_value_eq_rpow Fspec (0 : Fin 3) (2 : Fin 3) (by decide +kernel) n₁
  have hn₂ := unitPair_value_eq_rpow Fspec (0 : Fin 3) (1 : Fin 3) (by decide +kernel) n₂
  have hn₃ := unitPair_value_eq_rpow Fspec (1 : Fin 3) (2 : Fin 3) (by decide +kernel) n₃
  rw [eval_matMul_factor,
    eval_matMul_n11_eq_pair Fspec n₁,
    eval_matMul_1n1_eq_pair Fspec n₂,
    eval_matMul_11n_eq_pair Fspec n₃,
    hn₁, hn₂, hn₃,
    ← eval_matMul_n11_eq_pair Fspec 2,
    ← eval_matMul_1n1_eq_pair Fspec 2,
    ← eval_matMul_11n_eq_pair Fspec 2]

end OM.PolMul.SpectralFacts
