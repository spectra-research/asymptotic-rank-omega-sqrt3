import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Sets
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-! # Pivot columns in a finite ordered family -/

namespace OM.NNN34

open Submodule

/-- Retaining a column exactly when it is outside the span of its
predecessors gives an independent spanning family for the column space. -/
theorem ordered_pivots {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]
    {n : ℕ} (v : Fin n → V) :
    let p := {i | v i ∉ span K (v '' Set.Iio i)}
    LinearIndepOn K v p ∧ span K (v '' p) = span K (Set.range v) := by
  classical
  intro p
  have independent (s : Finset (Fin n)) (hs : ∀ i ∈ s, i ∈ p) :
      LinearIndepOn K v (s : Set (Fin n)) := by
    induction s using Finset.induction_on_max with
    | empty => simp
    | insert i s hlt ih =>
      rw [Finset.coe_insert]
      apply (ih fun j hj => hs j (Finset.mem_insert_of_mem hj)).insert
      have earlier : (s : Set (Fin n)) ⊆ Set.Iio i := fun j hj => hlt j hj
      exact fun h => hs i (Finset.mem_insert_self i s) (span_mono (Set.image_mono earlier) h)
  constructor
  · simpa only [Set.coe_toFinset] using independent p.toFinset (fun _ hj => Set.mem_toFinset.mp hj)
  · apply le_antisymm (span_mono (Set.image_subset_range v p))
    apply span_le.mpr
    rintro _ ⟨i, rfl⟩
    induction i using WellFoundedLT.induction with
    | ind i ih =>
      by_cases hi : i ∈ p
      · exact subset_span ⟨i, hi, rfl⟩
      · have hprev : v i ∈ span K (v '' Set.Iio i) := by
          by_contra hn
          exact hi hn
        apply span_le.mpr _ hprev
        rintro _ ⟨j, hj, rfl⟩
        exact ih j hj

end OM.NNN34

