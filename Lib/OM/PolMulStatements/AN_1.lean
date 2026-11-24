/- Adapted from PLATFORM/Statements/AN.1.lean of an earlier formalisation
   (commit 51c6e6b6e8b8d7226c6a828dba618ae1de5b5f8a).
   Uses Foundations tensor definitions; declarations are renamed under OM. -/
import Mathlib.Analysis.SpecialFunctions.Pow.Real

def OM_S_AN_1 : Prop :=
  ∀ (a : ℕ), 1 ≤ a → ∀ (g h : ℕ → ℝ),
    (∀ m : ℕ, 1 ≤ m → 0 < g m) →
    (∀ m : ℕ, 1 ≤ m → 0 < h m) →
    (∀ m : ℕ, 2 ≤ m → g (m + 1) + g (m - 1) ≤ 2 * g m) →
    (∀ m : ℕ, 2 ≤ m → h (m + 1) + h (m - 1) ≤ 2 * h m) →
    (∀ m : ℕ, 1 ≤ m → 2 * g m + h m ≤ g (3 * m + a - 1)) →
    (∀ m : ℕ, 1 ≤ m → 2 * h m + g m ≤ h (3 * m + a - 1)) →
    ∀ (b : ℕ), 1 ≤ b →
      g (b + 1) / g b * (h (b + 1) / h b) ≥
        ((((2 * b + a + 1 : ℕ) : ℝ) /
          ((2 * b + a - 1 : ℕ) : ℝ)) ^ (2 : ℝ))
