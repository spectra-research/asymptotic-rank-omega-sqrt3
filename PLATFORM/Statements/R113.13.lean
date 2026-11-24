import PLATFORM.Statements.«R113.4»

open P2M.R113

def S_R113_13 : Prop :=
  ∀ D : ℕ+, IsLeast (expansionCosts (matching D 0 3 1 2)) (W D)
