/- Adapted from PolMul/SpectralFacts/Basic.lean of an earlier formalisation
   (commit 51c6e6b6e8b8d7226c6a828dba618ae1de5b5f8a).
   Uses Foundations tensor definitions; declarations are renamed under OM. -/
import Lib.OM.PolMulStatements.SP_3
import Lib.OM.PolMulStatements.SP_4
import Lib.OM.PolMulStatements.SP_6

namespace OM.PolMul.SpectralFacts

open AsymptoticSpectrumDuality
open Semicontinuity
open OM.PolMulDef

universe u

private lemma unit_class_eq_natCast (F : Type u) [Field F] (n : ℕ+) :
    (TensorClass.mk ⟨fmt n n n, unit (F := F) n⟩ : TensorClass F 3) =
      ((n : ℕ) : TensorClass F 3) := by
  rw [natCast_eq_unitClass, unitClass, dif_pos n.pos]
  apply TensorClass.mk_eq_of_equiv
  let hfmt : ∀ i : Fin 3, ((fmt n n n i : ℕ)) = n := by
    intro i
    fin_cases i <;> rfl
  constructor
  · refine Restricts.of_eq_cast hfmt (fun idx => ?_)
    simp only [unit, unitTensor]
    congr 1
    apply propext
    constructor
    · intro h i j
      apply Fin.ext
      simpa only [Fin.val_cast] using! h i j
    · intro h i j
      have hij := congrArg Fin.val (h i j)
      simpa only [Fin.val_cast] using! hij
  · refine Restricts.of_eq_cast (fun i => (hfmt i).symm) (fun idx => ?_)
    simp only [unit, unitTensor]
    congr 1
    apply propext
    constructor
    · intro h i j
      simpa only [Fin.val_cast] using! congrArg Fin.val (h i j)
    · intro h i j
      apply Fin.ext
      simpa only [Fin.val_cast] using! h i j

theorem proof_SP_3 : OM_S_SP_3 := by
  intro F _instF φ
  constructor
  · intro d
    change AsymptoticSpectrum.eval
      (tensorStrassenPreorder (F := F) (k := 3) (by norm_num))
      (TensorClass.mk ⟨d, (0 : T3 F d)⟩) φ = 0
    rw [show (TensorClass.mk ⟨d, (0 : T3 F d)⟩ : TensorClass F 3) = 0 by
      rw [TensorClass.zero_def]
      exact TensorClass.mk_eq_of_equiv (zeroT_equiv_zero (F := F) (d := d)).symm]
    exact AsymptoticSpectrum.eval_zero _ φ
  · intro n
    change AsymptoticSpectrum.eval
      (tensorStrassenPreorder (F := F) (k := 3) (by norm_num))
      (TensorClass.mk ⟨fmt n n n, unit (F := F) n⟩) φ = ((n : ℕ) : ℝ)
    rw [unit_class_eq_natCast]
    exact AsymptoticSpectrum.eval_natCast _ φ (n : ℕ)

private lemma tensorClass_mk_ne_zero_of_ne_zero
    (F : Type u) [Field F] {d : Fin 3 → ℕ+} (T : T3 F d) (hT : T ≠ 0) :
    (TensorClass.mk ⟨d, T⟩ : TensorClass F 3) ≠ 0 := by
  intro hclass
  apply hT
  funext idx
  have hrel : (tensorStrassenPreorder (F := F) (k := 3) (by norm_num)).rel
      (TensorClass.mk ⟨d, T⟩) 0 := by
    rw [hclass]
    exact (tensorStrassenPreorder (F := F) (k := 3) (by norm_num)).refl 0
  rw [TensorClass.zero_def] at hrel
  obtain ⟨A, hA⟩ := hrel
  have h := hA idx
  change T idx = _ at h
  change T idx = 0
  rw [h]
  simp [zeroT]

theorem proof_SP_4 : OM_S_SP_4 := by
  intro F _instF φ d T hT
  let p := tensorStrassenPreorder (F := F) (k := 3) (by norm_num)
  have hne : (TensorClass.mk ⟨d, T⟩ : TensorClass F 3) ≠ 0 :=
    tensorClass_mk_ne_zero_of_ne_zero F T hT
  have hres : Restricts (unitTensor F (k := 3) 1) T :=
    unitTensor_one_restricts_of_ne_zero T hne
  have hmono := AsymptoticSpectrum.eval_mono p φ (a := (1 : TensorClass F 3))
    (b := TensorClass.mk ⟨d, T⟩) (by
      rw [TensorClass.one_def]
      exact hres)
  simpa [p, Spectral.eval, AsymptoticSpectrum.eval_one] using! hmono

theorem proof_SP_6 : OM_S_SP_6 := by
  intro F _instF π φ d T
  rfl

end OM.PolMul.SpectralFacts
