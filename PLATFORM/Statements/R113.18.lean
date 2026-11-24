import PLATFORM.Statements.«R113.5»
import PLATFORM.Statements.«R113.17»
import Foundations.Tensors.Semicontinuity.TensorStrassenPreorder
import Foundations.AsymptoticSpectrumDuality.AsymptoticSpectrum
import Lib.OM.NNN30.Geom.Basic

open P2M.R113 OM.NNN30.Geom Semicontinuity AsymptoticSpectrumDuality

def S_R113_18 : Prop :=
  ∀ κ : ℝ, 0 ≤ κ → κ < Real.sqrt 2 →
    (∀ M : ℕ+, ∃ D : ℕ+, M ≤ D ∧ (P D : ℝ) ≤ ((D : ℕ) : ℝ) ^ κ) →
    let p := tensorStrassenPreorder (F := ℂ) (k := 4) (by decide +kernel)
    ∀ φ : AsymptoticSpectrum p, ∃ (X : Type) (S : MidSpace X) (t : Fin 4 → X),
      twoTermBound S.d κ ∧ ∀ (D : ℕ+) (i j : Fin 4) (hij : i ≠ j),
        AsymptoticSpectrum.eval p (TensorClass.mk ⟨_, unitPairTensor (F := ℂ) D i j hij⟩) φ =
          ((D : ℕ) : ℝ) ^ S.d (t i) (t j)
