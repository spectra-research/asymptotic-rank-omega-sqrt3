import PLATFORM.Statements.«R114.4»
import Lib.OM.NNN30.Rect
import Mathlib.Data.Nat.Find

namespace P2M.R114

noncomputable def cutoff (H : ℕ) : ℕ :=
  Nat.findGreatest (fun k => OM.NNN30.Rect.Qn k ≤ (partitionSide H : ℕ)) H

end P2M.R114
