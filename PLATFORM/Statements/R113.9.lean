import PLATFORM.Statements.«R113.3»
import PLATFORM.Statements.«R88.1»
import Foundations.Tensors.PairUnitExponents
import Lib.OM.NNN30.Geom.Basic

open OM.NNN30.Geom Foundations.PairUnitExponents

/-- Under a saving, the squared and linear rectangle estimates hold in the same price space. -/
def S_R113_9 : Prop :=
  P2M.R113.finiteWitness →
  ∃ c : ℝ, 1 ≤ c ∧ c < Real.sqrt 2 ∧ ∀ φ : OM.PolMul.Spectral ℂ,
    ∃ (X : Type) (S : MidSpace X) (p : Fin 3 → X) (o : X),
      (∀ a b z e, S.d (S.m a b) (S.m z e) + S.d (S.m a e) (S.m z b)
        ≤ c * max (S.d a z) (S.d b e)) ∧
      (∀ q, P2M.R88.Fv φ (fun _ => 1) ≤ ∑ i, S.d q (p i)) ∧
      (∑ i, S.d o (p i)) = P2M.R88.Fv φ (fun _ => 1) ∧
      S.d (p 1) (p 2) ≤ theta φ 0 ∧ S.d (p 0) (p 2) ≤ theta φ 1 ∧
      S.d (p 0) (p 1) ≤ theta φ 2
