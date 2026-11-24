import PLATFORM.Statements.«R113.1»
import Foundations.Tensors.Semicontinuity.TensorStrassenPreorder
import Foundations.AsymptoticSpectrumDuality.AsymptoticSpectrum

namespace P2M.R113

open Semicontinuity AsymptoticSpectrumDuality

/-- The multiplicative four-point inequality in the ordinary spectrum of four-tensor restriction. -/
def spectralFourPoint : Prop :=
  let p := tensorStrassenPreorder (F := ℂ) (k := 4) (by decide +kernel)
  ∀ (D : ℕ+) (φ : AsymptoticSpectrum p),
    let value := fun (i j k l : Fin 4) =>
      AsymptoticSpectrum.eval p (TensorClass.mk ⟨_, matching D i j k l⟩) φ
    value 0 3 1 2 ≤ max (value 0 1 2 3) (value 0 2 1 3)

end P2M.R113
