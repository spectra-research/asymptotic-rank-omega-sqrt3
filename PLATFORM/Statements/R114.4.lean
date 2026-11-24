import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Data.PNat.Basic

namespace P2M.R114

def partitionSide (H : ℕ) : ℕ+ :=
  ⟨Fintype.card H.Partition, Fintype.card_pos⟩

end P2M.R114
