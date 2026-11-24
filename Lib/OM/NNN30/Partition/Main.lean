import Lib.OM.NNN30.Partition.Growth
import PLATFORM.Statements.«R108.2»

/-! # R108.2: growth of the partition numbers

`log₂ p(h)/√h` and `log₂ Q(h)/√h` both tend to `C = 2 √I / ln 2` with `I = ∑_{m ≥ 1} 1/m²`
(`Lib/OM/NNN30/Partition/Growth.lean`: the upper bound `ln Q(h) ≤ 2 √(I h)` from the truncated
generating function, the lower bound by Rankin's trick on both tails, and
`p(h) ≤ Q(h) ≤ (h+1) p(h)`). -/

namespace OM.NNN30.Partition

open Filter Topology

theorem proof_R108_2 : S_R108_2 := by
  have hI : 0 < Real.sqrt Isum := Real.sqrt_pos.mpr Isum_pos
  have hl : 0 < Real.log 2 := Real.log_pos one_lt_two
  refine ⟨2 * Real.sqrt Isum / Real.log 2, by positivity, ?_, ?_⟩
  · refine (tendsto_log_p.div_const (Real.log 2)).congr' (Eventually.of_forall (fun h => ?_))
    simp only [Real.logb]
    ring
  · refine (tendsto_log_Q.div_const (Real.log 2)).congr' (Eventually.of_forall (fun h => ?_))
    simp only [Real.logb, Qr]
    ring

end OM.NNN30.Partition

