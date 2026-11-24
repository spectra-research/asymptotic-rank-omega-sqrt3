import Mathlib.Analysis.Real.Sqrt

namespace P2M.R113

/-- The two factorizations use cuts `xy|uv` and `xu|yv`, with arbitrary factor sites. -/
def twoTermBound {X : Type*} (d : X → X → ℝ) (κ : ℝ) : Prop :=
  let charge := fun a b c e u v => d a u + d b u + d c v + d e v + κ * d u v
  ∀ t : Fin 4 → X, (∀ i j, i ≠ j → 0 < d (t i) (t j)) →
    ∀ u v u' v' : X,
      d (t 0) (t 3) + d (t 1) (t 2) ≤
        max (charge (t 0) (t 1) (t 2) (t 3) u v)
            (charge (t 0) (t 2) (t 1) (t 3) u' v')

end P2M.R113
