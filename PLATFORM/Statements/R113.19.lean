import PLATFORM.Statements.«R113.17»
import Lib.OM.NNN30.Geom.Basic

open P2M.R113 OM.NNN30.Geom

universe u

def S_R113_19 : Prop :=
  ∀ (X : Type u) (S : MidSpace X) (κ : ℝ), 0 ≤ κ → κ < Real.sqrt 2 →
    twoTermBound S.d κ → ∀ a b c e : X,
      S.d a c + S.d b e ≤ max (S.d a b + S.d c e) (S.d a e + S.d b c)
