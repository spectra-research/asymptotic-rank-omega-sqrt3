import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-- Partition growth: `log₂ p(h) / √h` and `log₂ Q(h) / √h` converge to the same
positive constant, where `p(h)` is the number of partitions of `h` and `Q(h) = ∑_{j ≤ h} p(j)`. -/
def S_R108_2 : Prop :=
  ∃ C : ℝ, 0 < C ∧
    Filter.Tendsto (fun h : ℕ => Real.logb 2 (Fintype.card h.Partition) / Real.sqrt h)
      Filter.atTop (nhds C) ∧
    Filter.Tendsto (fun h : ℕ =>
        Real.logb 2 (∑ j ∈ Finset.range (h + 1), Fintype.card j.Partition) / Real.sqrt h)
      Filter.atTop (nhds C)
