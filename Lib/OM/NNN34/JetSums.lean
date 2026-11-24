import Lib.OM.NNN30.Crossing.Jets
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! # Linear combinations of truncated jets in the crossing expansion -/

namespace OM.NNN34

open OM.NNN30.Crossing PowerSeries

/-- If the weight-`m` jet has a common right factor indexed by partitions
of `m`, a linear combination of basis coefficients through `k` uses just
one copy of each such space through `k`. -/
theorem weighted_jet_factor {I J : Type} (c d : ℂ) (D k : ℕ) (hk : k ≤ D)
    (w : Fin (k + 1) → ℂ) (A : ℂ⟦X⟧) (P : I → J → Polynomial ℂ) (U : I → J → ℂ⟦X⟧)
    (R : (m : ℕ) → m.Partition → J → ℂ)
    (hP : ∀ i j, (P i j : ℂ⟦X⟧) = A * U i j)
    (hU : ∀ i m, ∃ l : m.Partition → ℂ, ∀ j, coeff m (U i j) = ∑ t, l t * R m t j) :
    ∃ L : I → States k → ℂ, ∀ i j,
      ∑ h : Fin (k + 1), w h * (trL c d D (P i j)).coeff h =
        ∑ s : States k, L i s * R s.1.val s.2 j := by
  classical
  let rows (s : States k) := R s.1.val s.2
  let W := Submodule.span ℂ (Set.range rows)
  let jet (i : I) (h : Fin (k + 1)) (j : J) := w h * (trL c d D (P i j)).coeff h
  have member (i : I) (h : Fin (k + 1)) : jet i h ∈ W := by
    obtain ⟨L, hL⟩ := jet_factor c d (w h) D h.val (by omega) A P U R hP hU
    have eqn : jet i h = ∑ t : States h.val, L i t • R t.1.val t.2 := by
      funext j
      simpa only [jet, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using hL i j
    rw [eqn]
    apply W.sum_mem
    intro t _
    apply W.smul_mem
    exact Submodule.subset_span ⟨⟨⟨t.1.val, t.1.isLt.trans_le (Nat.succ_le_of_lt h.isLt)⟩, t.2⟩, rfl⟩
  have combined (i : I) : ∑ h, jet i h ∈ W := W.sum_mem fun h _ => member i h
  choose L hL using fun i => (Submodule.mem_span_range_iff_exists_fun ℂ).mp (combined i)
  refine ⟨L, fun i j => ?_⟩
  simpa only [jet, rows, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using
    (congrFun (hL i) j).symm

end OM.NNN34

