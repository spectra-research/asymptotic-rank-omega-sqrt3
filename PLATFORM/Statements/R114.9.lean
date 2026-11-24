import PLATFORM.Statements.«R114.7»
import PLATFORM.Statements.«R114.8»

namespace P2M.R114

noncomputable def leftFactor (H : ℕ) : Semicontinuity.KTensor ℂ (fun _ : Fin 3 => partitionSide H) :=
  fun a => match (pivotColumns (rowPiece H))[(a 2).val]? with
    | some (c, e) => rowPiece H ![a 0, a 1, e, c]
    | none => 0

end P2M.R114
