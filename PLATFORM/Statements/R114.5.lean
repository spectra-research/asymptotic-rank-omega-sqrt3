import PLATFORM.Statements.«R114.4»
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.Lex

namespace P2M.R114

noncomputable def partitionAt (H : ℕ) : Fin (partitionSide H : ℕ) ≃ H.Partition := by
  let parts := fun p : H.Partition => p.parts.sort (· ≥ ·)
  letI : LinearOrder H.Partition := LinearOrder.lift' parts (by
    intro p q h
    apply Nat.Partition.ext
    simpa only [parts, Multiset.sort_eq] using congrArg (fun l : List ℕ => (l : Multiset ℕ)) h)
  exact (Fintype.orderIsoFinOfCardEq H.Partition rfl).toEquiv

end P2M.R114
