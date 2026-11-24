import PLATFORM.Statements.«R115.1»

open P2M.R115

def S_R115_6 : Prop :=
  ∀ (n n₃ : ℕ+), ((n : ℕ) : ℝ) ^ (4 / Real.sqrt 5) ≤ ((n₃ : ℕ) : ℝ) →
    (n₃ : ℕ) ≤ (n : ℕ) ^ 2 → formatRankSup n n n₃ = ((n₃ : ℕ) : ℝ)
