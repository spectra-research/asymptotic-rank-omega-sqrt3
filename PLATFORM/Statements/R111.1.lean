import Mathlib.Basic.Real.Basic
import Mathlib.Data.Fin.Basic

/-- The angle condition in a pseudometric space `(X, d)` with a midpoint map `m`
satisfying the axial bounds (6), `m a a ≈ a` and the quadrilateral inequality (10): at a point
`o` minimising the sum of the distances to the terminals `p 0, p 1, p 2`, every two terminals
satisfy `d(p i, p j)² ≥ h_i² + h_i h_j + h_j²` with `h_i = d(o, p i)`. -/
def S_R111_1 : Prop :=
  ∀ (X : Type) (d : X → X → ℝ) (m : X → X → X) (p : Fin 3 → X) (o : X),
    (∀ x, d x x = 0) → (∀ x y, d x y = d y x) → (∀ x y z, d x z ≤ d x y + d y z) →
    (∀ a b c, d (m a b) (m c b) ≤ d a c / 2) →
    (∀ a b e, d (m a b) (m a e) ≤ d b e / 2) →
    (∀ a, d (m a a) a = 0) →
    (∀ a b c e, d (m a b) (m c e) ^ 2 + d (m a e) (m c b) ^ 2 ≤ (d a c ^ 2 + d b e ^ 2) / 2) →
    (∀ q, d o (p 0) + d o (p 1) + d o (p 2) ≤ d q (p 0) + d q (p 1) + d q (p 2)) →
    ∀ i j : Fin 3, i ≠ j →
      d o (p i) ^ 2 + d o (p i) * d o (p j) + d o (p j) ^ 2 ≤ d (p i) (p j) ^ 2
