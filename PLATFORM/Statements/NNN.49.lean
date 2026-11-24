import PLATFORM.Statements.«R113.7»
import PLATFORM.Statements.«R116.1»
import PLATFORM.Statements.«R116.2»

def S_NNN_49 : Prop :=
  P2M.R113.gamma = Real.sqrt 2 → OM.PolMul.omegaF ℂ = 2 →
    ∀ a b c : ℝ, 0 < a → a ≤ b → b ≤ c → c < a + b →
      P2M.R116.formatBeta a b c = 2 * P2M.R116.discRadius a b c
