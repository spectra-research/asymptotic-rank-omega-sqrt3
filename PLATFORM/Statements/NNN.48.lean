import PLATFORM.Statements.«R113.7»
import PLATFORM.Statements.«R116.1»
import PLATFORM.Statements.«R116.2»

def S_NNN_48 : Prop :=
  P2M.R113.gamma = Real.sqrt 2 → ∀ a b c : ℝ, 0 < a → a ≤ b → b ≤ c → c < a + b →
    2 * P2M.R116.discRadius a b c ≤ P2M.R116.formatBeta a b c
