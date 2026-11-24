/- Adapted from PLATFORM/Statements/AN.2.lean of an earlier formalisation
   (commit 51c6e6b6e8b8d7226c6a828dba618ae1de5b5f8a).
   Uses Foundations tensor definitions; declarations are renamed under OM. -/
import Mathlib.Analysis.SpecialFunctions.Pow.Real

def OM_S_AN_2 : Prop :=
  ∀ (a : ℕ), 1 ≤ a → ∀ (g h : ℕ → ℝ),
    (∀ m : ℕ, 1 ≤ m → 0 < g m) →
    (∀ m : ℕ, 1 ≤ m → 0 < h m) →
    (∀ m : ℕ, 2 ≤ m → g (m + 1) + g (m - 1) ≤ 2 * g m) →
    (∀ m : ℕ, 2 ≤ m → h (m + 1) + h (m - 1) ≤ 2 * h m) →
    (∀ m : ℕ, 1 ≤ m → 2 * g m + h m ≤ g (3 * m + a - 1)) →
    (∀ m : ℕ, 1 ≤ m → 2 * h m + g m ≤ h (3 * m + a - 1)) →
    ∀ (u v r s : ℕ), 1 ≤ u → 1 ≤ v → 1 ≤ r → 1 ≤ s →
      (g (u + r) / g u) ^ ((s : ℕ) : ℝ) *
          (h (v + s) / h v) ^ ((r : ℕ) : ℝ) ≥
        (((((u + v + r + s + a - 1 : ℕ) : ℝ)) /
          ((((u + v + r + s + a - 1 : ℕ) : ℝ)) -
            4 * ((r : ℕ) : ℝ) * ((s : ℕ) : ℝ) /
              (((r + s : ℕ) : ℝ)))) ^ (((r + s : ℕ) : ℝ)))
