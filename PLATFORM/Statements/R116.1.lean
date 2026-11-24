import PLATFORM.Statements.«R115.1»
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Order.LiminfLimsup

namespace P2M.R116

noncomputable def formatBeta (a b c : ℝ) : ℝ :=
  let dim (n : ℕ+) (x : ℝ) : ℕ+ :=
    ⟨⌈((n : ℕ) : ℝ) ^ x⌉₊, Nat.ceil_pos.mpr (Real.rpow_pos_of_pos (by exact_mod_cast n.2) x)⟩
  Filter.limsup (fun n : ℕ+ => Real.logb (n : ℕ)
    (P2M.R115.formatRankSup (dim n a) (dim n b) (dim n c))) Filter.atTop

end P2M.R116
