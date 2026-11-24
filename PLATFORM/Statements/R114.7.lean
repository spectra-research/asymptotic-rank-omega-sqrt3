import PLATFORM.Statements.«R114.5»
import PLATFORM.Statements.«R114.6»
import Lib.OM.NNN30.Crossing.Main
import Foundations.Tensors.Semicontinuity.MaxRankBound

namespace P2M.R114

noncomputable def rowPiece (H : ℕ) : Semicontinuity.KTensor ℂ (fun _ : Fin 4 => partitionSide H) :=
  fun a => ∑ j ∈ Finset.range (cutoff H + 1),
    OM.NNN30.Crossing.Bfin H H j (partitionAt H (a 0)) (partitionAt H (a 1))
      (partitionAt H (a 2)) (partitionAt H (a 3))

end P2M.R114
