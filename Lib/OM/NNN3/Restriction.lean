import Lib.OM.NNN3.Corrections
import Lib.OM.NNN3.Expansion
noncomputable section
open scoped BigOperators Classical
namespace OM.NNN3
open CoordinateTensor OM.NNN.Raw OM.NNN2
variable {X : Type} [Fintype X]

/-- A direct-sum source for the seven signed corrections. -/
def correctionSource (T : Cube ℂ X) :=
  let A := tensorProduct (mm X X X) T
  let B := tensorProduct (mm X X X) (diagonal ℂ (X × X))
  directSum (directSum (directSum (directSum (directSum (directSum A A) A) B) B) B) B

/-- Equation (20), as an ordinary restriction. The seven minus signs belong to
local linear maps. No cancellation property of the restriction order is used. -/
theorem symmetric_restriction (T : Cube ℂ X) :
    Restricts (directSum (mm (Sym2 X) (Sym2 X) (Sym2 X)) (correctionSource T)) (cube T) := by
  have h := restricts_add (restricts_add (restricts_add (restricts_add (restricts_add
    (restricts_add (restricts_neg (singleAB_restricts T)) (restricts_neg (singleBC_restricts T)))
    (restricts_neg (singleCA_restricts T))) (restricts_neg (doubleABBC_restricts T)))
    (restricts_neg (doubleABCA_restricts T))) (restricts_neg (doubleBCCA_restricts T)))
    (restricts_neg (tripleSwap_restricts T))
  have h' := restricts_add (show Restricts (mm (Sym2 X) (Sym2 X) (Sym2 X)) (compressed T) from
    ⟨compressedLeft T, compressedMid T, compressedRight T, rfl⟩) h
  convert! h' using 1
  rw [compressed_expansion]
  abel

end OM.NNN3
