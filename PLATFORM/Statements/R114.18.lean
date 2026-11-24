import PLATFORM.Statements.«R114.3»
import PLATFORM.Statements.«R114.10»
import PLATFORM.Statements.«R114.17»
import Lib.OM.NNN32.FourPrices

open P2M.R114 AsymptoticSpectrumDuality OM.NNN32

def S_R114_18 : Prop :=
  ∀ bL bN : ℝ, 0 ≤ bL → 0 ≤ bN →
    (∀ M : ℕ, ∃ H ≥ max 2 M,
      relativeCost (leftFactor H) ≤ bL ∧ relativeCost (rightFactor H) ≤ bN) →
    ∀ (V : Type) [Fintype V] (φ : AsymptoticSpectrum fourPreorder) (τ : Fin 4 → V) (d : V → V → ℝ),
      FourNetwork.Minimal φ τ d → triangleBillBound d bL bN
