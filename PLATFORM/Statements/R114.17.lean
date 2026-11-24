import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Fintype.Fin

namespace P2M.R114

def triangleBillBound {X : Type*} (d : X → X → ℝ) (bL bN : ℝ) : Prop :=
  let per := fun p q o => d p q + d q o + d o p
  ∀ t : Fin 4 → X, (∀ i j, i ≠ j → 0 < d (t i) (t j)) →
    ∀ (p : Fin 4 → X) (o u v : X),
      d (t 0) (t 3) + d (t 1) (t 2) ≤
        max ((∑ i, d (t i) (p i)) + bL * per (p 0) (p 1) o + bN * per (p 3) (p 2) o)
          (d (t 0) u + d (t 2) u + d (t 1) v + d (t 3) v + Real.sqrt 3 * d u v)

end P2M.R114
