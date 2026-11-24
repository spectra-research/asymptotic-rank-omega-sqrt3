import PLATFORM.Statements.«R88.1»
import Foundations.Tensors.PairUnitExponents

/-- The price metric at a spectral point `φ`, in abstract form: a pseudometric space
`(X, d)` with a midpoint map `m` satisfying the axial bounds (6), `m a a ≈ a` and the
quadrilateral inequality (7)/(10); the terminals `p 0, p 1, p 2` have pairwise distances at most
the edge prices (`θ` of the third party); every point `q` has distance sum at least
`g = F(1,1,1)` (5), and the initial site `o` has distance sum at most `g`. -/
def S_R111_2 : Prop :=
  ∀ φ : OM.PolMul.Spectral ℂ,
    ∃ (X : Type) (d : X → X → ℝ) (m : X → X → X) (p : Fin 3 → X) (o : X),
      (∀ x, d x x = 0) ∧ (∀ x y, d x y = d y x) ∧ (∀ x y z, d x z ≤ d x y + d y z) ∧
      (∀ a b c, d (m a b) (m c b) ≤ d a c / 2) ∧
      (∀ a b e, d (m a b) (m a e) ≤ d b e / 2) ∧
      (∀ a, d (m a a) a = 0) ∧
      (∀ a b c e, d (m a b) (m c e) ^ 2 + d (m a e) (m c b) ^ 2 ≤ (d a c ^ 2 + d b e ^ 2) / 2) ∧
      (∀ q, P2M.R88.Fv φ (fun _ => 1) ≤ d q (p 0) + d q (p 1) + d q (p 2)) ∧
      d o (p 0) + d o (p 1) + d o (p 2) ≤ P2M.R88.Fv φ (fun _ => 1) ∧
      d (p 1) (p 2) ≤ Foundations.PairUnitExponents.theta φ 0 ∧
      d (p 0) (p 2) ≤ Foundations.PairUnitExponents.theta φ 1 ∧
      d (p 0) (p 1) ≤ Foundations.PairUnitExponents.theta φ 2
