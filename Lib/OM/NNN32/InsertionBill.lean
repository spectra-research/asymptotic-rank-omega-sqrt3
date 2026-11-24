import Lib.OM.NNN32.MarkedBonds
import Lib.OM.NNN32.FactoredNetwork

/-! # The bill after replacing two bundles by a split crossing -/

noncomputable section
open scoped Classical

namespace OM.NNN32

open Semicontinuity AsymptoticSpectrumDuality OM.NNN30.Net

/-- Split off a common register. Rounding its residual multiplicity costs at most one bit. -/
lemma residual_embedding (A : Type) [Fintype A] (D : ℕ+)
    (hD : 0 < Real.logb 2 (D:ℕ))
    (h : Real.logb 2 (D:ℕ) ≤ Real.logb 2 (Fintype.card A)) :
    ∃ r : ℕ, Nonempty (A ↪ Index D × Fin r) ∧
      Real.logb 2 r ≤ Real.logb 2 (Fintype.card A) - Real.logb 2 (D:ℕ) + 1 := by
  let n := Fintype.card A
  have hn : 0 < n := by
    by_contra! hz
    have hz' : Fintype.card A = 0 := Nat.eq_zero_of_le_zero hz
    simp [hz'] at h
    linarith
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have hd : (0:ℝ) < (D:ℕ) := by exact_mod_cast D.2
  have hnD : ((D:ℕ):ℝ) ≤ n := (Real.logb_le_logb (by norm_num : (1:ℝ)<2) hd hn').mp h
  let r := ⌈(n:ℝ)/(D:ℕ)⌉₊
  have hq : 1 ≤ (n:ℝ)/(D:ℕ) := (one_le_div hd).2 hnD
  have hr : (n:ℝ)/(D:ℕ) ≤ r := Nat.le_ceil _
  have hre : (0:ℝ) < r := zero_lt_one.trans_le (hq.trans hr)
  refine ⟨r,Function.Embedding.nonempty_of_card_le ?_,?_⟩
  · simp only [Fintype.card_prod,Fintype.card_fin]
    have hmul := (div_le_iff₀ hd).1 hr
    rw [mul_comm] at hmul
    exact_mod_cast hmul
  · have hh : (r:ℝ) ≤ 2*((n:ℝ)/(D:ℕ)) := by
      have h' := Nat.ceil_lt_add_one (div_nonneg hn'.le hd.le)
      dsimp [r]
      linarith
    have hl := Real.logb_le_logb_of_le (by norm_num : (1:ℝ)<2) hre hh
    rw [Real.logb_mul (by norm_num) (div_pos hn' hd).ne',Real.logb_self_eq_one (by norm_num),
      Real.logb_div hn'.ne' hd.ne'] at hl
    dsimp [n] at hl
    linarith

namespace FourNetwork

variable {V : Type} {f : Fin 4 → ℕ+} {φ : AsymptoticSpectrum fourPreorder} {τ : Fin 4 → V}
  {d : V → V → ℝ}

lemma ranks_positive {N : FourNetwork V f} (hp : 0 < value φ N) : ∀ k, 0 < N.graph.r k := by
  apply N.r_pos
  intro h
  change 0 < fourValue φ N.tensor at hp
  rw [h,fourValue_zero] at hp
  exact lt_irrefl _ hp

/-- The powered network saves the common width times the hypothesized local
discount, up to two residual roundings and one bit for adding the branches. -/
theorem gap_from_split (hd : Valid φ τ d) (hn : 0 ≤ d) (N : FourNetwork V f)
    (hl : N.Local τ) (hp : 0 < value φ N) (t : Fin 4 → V) (ht : t 0 ≠ t 1)
    {D : ℕ+} (hD : 0 < Real.logb 2 (D:ℕ))
    (hw₀ : Real.logb 2 (D:ℕ) ≤ N.graph.wid (t 0) (t 3))
    (hw₁ : Real.logb 2 (D:ℕ) ≤ N.graph.wid (t 1) (t 2))
    (F G : FactorSites V D) (hf : crossing D = F.kernel + G.kernel)
    {K η : ℝ}
    (rankF : Real.logb 2 F.rank ≤ K * Real.logb 2 (D:ℕ))
    (rankG : Real.logb 2 G.rank ≤ K * Real.logb 2 (D:ℕ))
    (chargeF : F.leaves d t + K * d F.u F.v ≤ d (t 0) (t 3) + d (t 1) (t 2) - η)
    (chargeG : G.leaves d t + K * d G.u G.v ≤ d (t 0) (t 3) + d (t 1) (t 2) - η) :
    η * Real.logb 2 (D:ℕ) - (1+d (t 0) (t 3)+d (t 1) (t 2)) ≤ gap N φ d := by
  have hr := ranks_positive hp
  obtain ⟨wa,wb⟩ := N.bundle_widths t ht hr
  obtain ⟨r,⟨p⟩,hpr⟩ := residual_embedding (N.bundle t 0) D hD (hw₀.trans_eq wa.symm)
  obtain ⟨s,⟨q⟩,hqs⟩ := residual_embedding (N.bundle t 1) D hD (hw₁.trans_eq wb.symm)
  rw [wa] at hpr
  rw [wb] at hqs
  let C := N.context t
  have split : N.tensor = (C.realize p q F).tensor + (C.realize p q G).tensor := by
    rw [CutContext.realize_tensor,CutContext.realize_tensor,← CutContext.insert_add,← hf,
      CutContext.insert_crossing,N.context_closed]
  have val : value φ N ≤ value φ (C.realize p q F) + value φ (C.realize p q G) := by
    change fourValue φ N.tensor ≤ _
    rw [split]
    exact fourValue_add _ _ _
  have hc := N.unmarked_cost t d ht hr
  have estimate (J : FactorSites V D)
      (rankJ : Real.logb 2 J.rank ≤ K * Real.logb 2 (D:ℕ))
      (chargeJ : J.leaves d t + K * d J.u J.v ≤ d (t 0) (t 3) + d (t 1) (t 2) - η)
      (hv : value φ N ≤ 2 * value φ (C.realize p q J)) :
      η * Real.logb 2 (D:ℕ) - (1+d (t 0) (t 3)+d (t 1) (t 2)) ≤ gap N φ d := by
    have hv' : 0 < value φ (C.realize p q J) := by linarith
    have hlog := Real.logb_le_logb_of_le (by norm_num : (1:ℝ)<2) hp hv
    rw [Real.logb_mul (by norm_num) hv'.ne',Real.logb_self_eq_one (by norm_num)] at hlog
    have hprice := hd _ (C.realize_local p q J (N.context_local t hl ht)) hv'
    rw [CutContext.realize_cost] at hprice
    change Real.logb 2 _ ≤ (N.unmarked t).graph.cost d + J.leaves d t * _ +
      d (t 0) (t 3)*_ + d (t 1) (t 2)*_ + d J.u J.v*_ at hprice
    unfold gap
    linarith only [hc,hlog,hprice,mul_le_mul_of_nonneg_left hpr (hn (t 0) (t 3)),
      mul_le_mul_of_nonneg_left hqs (hn (t 1) (t 2)),mul_le_mul_of_nonneg_left rankJ (hn J.u J.v),
      mul_le_mul_of_nonneg_right chargeJ hD.le]
  rcases le_total (value φ (C.realize p q F)) (value φ (C.realize p q G)) with h | h
  · exact estimate G rankG chargeG (by linarith)
  · exact estimate F rankF chargeF (by linarith)

end FourNetwork

end OM.NNN32
