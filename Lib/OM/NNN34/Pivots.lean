import Lib.OM.NNN34.Crossing
import Lib.OM.NNN34.PivotSpan
import PLATFORM.Statements.«R114.12»
import Mathlib.Data.List.NodupEquivFin

/-! # Ordered pivot columns and unique padded coordinates -/

noncomputable section

namespace OM.NNN34

open P2M.R114 Semicontinuity OM.NNN32 Module Submodule

private abbrev columns {D : ℕ+} (R : Four D) (ce : Index D × Index D) :=
  (rowMatrix R).col ce.swap

private abbrev chosen {D : ℕ+} (R : Four D) (j : Fin (pivotColumns R).length) :=
  columns R ((pivotColumns R).get j)

private lemma pivot_basis {D : ℕ+} (R : Four D) :
    LinearIndependent ℂ (chosen R) ∧
    span ℂ (Set.range (chosen R)) = span ℂ (Set.range (rowMatrix R).col) := by
  classical
  let key : (Index D × Index D) ≃ Fin ((D : ℕ)*(D : ℕ)) := finProdFinEquiv
  let v := fun j => columns R (key.symm j)
  let good := {j | v j ∉ span ℂ (v '' Set.Iio j)}
  let ids := (List.finRange ((D : ℕ)*(D : ℕ))).filter (fun j => decide (j ∈ good))
  have list_eq : pivotColumns R = ids.map key.symm := rfl
  have mem (c : Index D × Index D) : c ∈ pivotColumns R ↔ key c ∈ good := by
    rw [list_eq]
    simp only [List.mem_map, List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq, ids]
    constructor
    · rintro ⟨j,hj,rfl⟩; simpa using hj
    · intro h; exact ⟨key c,h,key.symm_apply_apply c⟩
  have nd : (pivotColumns R).Nodup := by
    rw [list_eq]
    exact ((List.nodup_finRange _).filter _).map key.symm.injective
  let e := nd.getEquiv (pivotColumns R)
  let f (i : Fin (pivotColumns R).length) : good := ⟨key (e i).val, (mem _).mp (e i).property⟩
  have fv (i : Fin (pivotColumns R).length) : v (f i) = chosen R i := by
    change columns R (key.symm (key _)) = _; rw [key.symm_apply_apply]; rfl
  obtain ⟨hlin,hspan⟩ := ordered_pivots (K := ℂ) v
  have hf : Function.Injective f := fun i j h =>
    e.injective (Subtype.ext (key.injective (congrArg Subtype.val h)))
  have lin := hlin.comp f hf
  have eqv : (fun i => v (f i).val) = chosen R := funext fv
  change LinearIndependent ℂ (fun i => v (f i).val) at lin
  rw [eqv] at lin
  refine ⟨lin, ?_⟩
  have left : Set.range (chosen R) = v '' good := by
    ext x
    constructor
    · rintro ⟨i,rfl⟩
      exact ⟨f i,(f i).property, fv i⟩
    · rintro ⟨j,hj,rfl⟩
      let c := key.symm j
      have hc : c ∈ pivotColumns R := (mem c).mpr (by simpa [c] using hj)
      let i := e.symm ⟨c,hc⟩
      refine ⟨i, ?_⟩
      change columns R ((e i).val) = columns R c
      rw [show e i = ⟨c,hc⟩ from e.apply_symm_apply _]
  have right : Set.range v = Set.range (rowMatrix R).col := by
    ext x
    constructor
    · rintro ⟨i,rfl⟩; exact ⟨(key.symm i).swap,rfl⟩
    · rintro ⟨ce,rfl⟩
      exact ⟨key ce.swap, by simp [v, columns]⟩
  rw [left, hspan, right]

set_option maxHeartbeats 3500000 in
theorem proof_R114_12 : S_R114_12 := by
  classical
  intro H hH
  let D := partitionSide H
  let R := rowPiece H
  let piv := pivotColumns R
  let r := piv.length
  let w := chosen R
  obtain ⟨lin, span_eq⟩ := pivot_basis R
  have hrank : r = flatRank R {0,1} := by
    rw [← rowMatrix_rank, Matrix.rank_eq_finrank_span_cols, ← span_eq, finrank_span_eq_card lin,
      Fintype.card_fin]
  obtain ⟨_,hrow,hside,_⟩ := proof_R114_11 H hH
  have hr : r ≤ (D : ℕ) := hrank.le.trans (hrow.trans hside)
  let inc : Fin r → Fin (D : ℕ) := Fin.castLE hr
  have padded (v : Fin (D : ℕ) → ℂ) (i b : Fin (D : ℕ)) :
      (∑ j, v (inc j) * w j (i,b)) = ∑ j, leftFactor H ![i,b,j] * v j := by
    apply Fintype.sum_of_injective inc (Fin.castLE_injective hr)
      (fun j => v (inc j) * w j (i,b)) (fun j => leftFactor H ![i,b,j] * v j)
    · intro j hj
      have hout : r ≤ j.val := le_of_not_gt (fun h => hj ⟨⟨j.val,h⟩,Fin.ext rfl⟩)
      change (match piv[j.val]? with | some (c,e) => R ![i,b,e,c] | none => 0) * v j = 0
      rw [List.getElem?_eq_none hout]; exact zero_mul _
    · intro j
      change v (inc j) * columns R (piv.get j) (i,b) =
        (match piv[j.val]? with | some (c,e) => R ![i,b,e,c] | none => 0) * v (inc j)
      rw [List.getElem?_eq_getElem j.isLt, mul_comm]
      rfl
  let coords (c e : Fin (D : ℕ)) (v : Fin (D : ℕ) → ℂ) :=
    (∀ j : Fin (D : ℕ), r ≤ j.val → v j = 0) ∧
    ∀ i b, R ![i,b,e,c] = ∑ j, leftFactor H ![i,b,j] * v j
  have uniq (c e : Fin (D : ℕ)) : ∃! v, coords c e v := by
    have mem : columns R (c,e) ∈ span ℂ (Set.range w) := by
      rw [show span ℂ (Set.range w) = _ from span_eq]
      exact subset_span ⟨(e,c),rfl⟩
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp mem
    let v (j : Fin (D : ℕ)) := if hj : j.val < r then a ⟨j.val,hj⟩ else 0
    have hv (j : Fin r) : v (inc j) = a j := dif_pos j.isLt
    have hcoeff (i b : Fin (D : ℕ)) : R ![i,b,e,c] = ∑ j, a j * w j (i,b) := by
      change columns R (c,e) (i,b) = _
      simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using! (congrFun ha (i,b)).symm
    refine ⟨v, ⟨fun j hj => dif_neg (not_lt.mpr hj), fun i b => ?_⟩, ?_⟩
    · exact (hcoeff i b).trans ((Finset.sum_congr rfl (fun j _ => congrArg (fun u => u * w j (i,b)) (hv j).symm)).trans (padded v i b))
    · intro v' hv'
      have same : (fun j => v' (inc j)) = a := by
        apply lin.fintypeLinearCombination_injective
        funext ab
        obtain ⟨i,b⟩ := ab
        simp only [Fintype.linearCombination_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
        exact (padded v' i b).trans ((hv'.2 i b).symm.trans (hcoeff i b))
      funext j
      by_cases hj : j.val < r
      · rw [show v j = a ⟨j.val,hj⟩ from dif_pos hj]; exact congrFun same ⟨j.val,hj⟩
      · rw [show v j = 0 from dif_neg hj]; exact hv'.1 j (le_of_not_gt hj)
  refine ⟨hrank, uniq, ?_⟩
  intro a
  let h := uniq (a 3) (a 2)
  have heq (j : Fin (D : ℕ)) : rightFactor H ![a 3,a 2,j] = h.choose j := by
    unfold rightFactor
    exact dif_pos h
  simp_rw [heq]
  have he := h.choose_spec.1.2 (a 0) (a 1)
  convert he using 2
  congr 1
  funext i
  fin_cases i <;> rfl

end OM.NNN34

