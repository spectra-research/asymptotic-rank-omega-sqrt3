import PLATFORM.Statements.«R113.7»
import PLATFORM.Statements.«R116.1»
import Rect.RankModel.Defs3

def S_NNN_47 : Prop :=
  P2M.R113.gamma = 1 → ∀ a b c : ℝ, 0 < a → a ≤ b → b ≤ c → c < a + b →
    let s := (a + b + c) / 2
    P2M.R116.formatBeta a b c = OmegaBound.omegaRect3 ℂ (s - a) (s - b) (s - c)
