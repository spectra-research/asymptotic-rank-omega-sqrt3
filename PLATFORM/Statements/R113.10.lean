import Lib.OM.NNN30.Geom.Basic
import Mathlib.Analysis.Real.Sqrt

open OM.NNN30.Geom

universe u

/-- A Fermat point lies between every pair of terminals under the strict rectangle estimate. -/
def S_R113_10 : Prop :=
  ∀ (X : Type u) (S : MidSpace X) (c : ℝ), 1 ≤ c → c < Real.sqrt 2 →
    (∀ a b z e, S.d (S.m a b) (S.m z e) + S.d (S.m a e) (S.m z b)
      ≤ c * max (S.d a z) (S.d b e)) →
    ∀ (p : Fin 3 → X) (o : X), (∀ q, (∑ i, S.d o (p i)) ≤ ∑ i, S.d q (p i)) →
      ∀ i j : Fin 3, i ≠ j → S.d (p i) (p j) = S.d o (p i) + S.d o (p j)
