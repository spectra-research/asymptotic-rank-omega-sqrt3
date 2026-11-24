import Lib.OM.NNN36.SupportingPrice
import Lib.OM.NNN30.Net.Main
import Lib.OM.NNN30.Geom.Basic
import Lib.OM.NNN8.Transfer

/-! # The price space at rectangular log-dimensions -/

noncomputable section
namespace OM.NNN36

open NNN22 NNN30.Net NNN30.Geom NNN.Raw Semicontinuity
open Foundations.PairUnitExponents Foundations.HyperbolicLift

/-- Powering a fixed tensor removes the cost of rounding each width up to whole bits. -/
theorem log_eval_le_Fv (φ : PolMul.Spectral ℂ) {d : Fin 3 → ℕ+} (T : KTensor ℂ d)
    (hT : 0 < φ.eval T) (hw : ∀ i, 0 < Real.logb 2 (d i : ℕ)) :
    Real.logb 2 (φ.eval T) ≤ Fv φ (fun i => Real.logb 2 (d i : ℕ)) := by
  let w := fun i => Real.logb 2 (d i : ℕ)
  obtain ⟨h, hn, hsum, hs⟩ := supporting_price_at φ w hw
  change Real.logb 2 (φ.eval T) ≤ Fv φ w
  rw [← hsum]
  by_contra! hlt
  obtain ⟨n,hbig⟩ := exists_nat_gt ((∑ i, h i) / (Real.logb 2 (φ.eval T) - ∑ i, h i * w i))
  rw [div_lt_iff₀ (sub_pos.mpr hlt)] at hbig
  let Tn := PolMul.kronPow T n
  let I := fun i => Fin (((d i)^n : ℕ+) : ℕ)
  have hbound := cost_hub φ h hn hs I (fun a b c => Tn (idx3 a b c))
  rw [value_encode φ Tn, show φ.eval Tn = (φ.eval T)^n from NNN8.eval_kronPow φ T n] at hbound
  have hlog := (Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ) < 2) (pow_pos hT n)).2 hbound
  have hb (i) : bits (I i) = n * w i := by
    simp [bits, I, w, Real.logb_pow]
  simp only [Real.logb_pow, hb] at hlog
  rw [show (∑ i, h i * ((n : ℝ)*w i)) = n * ∑ i, h i * w i by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring] at hlog
  linarith only [hbig, hlog]

/-- A dyadic star stored at any site tests its three weighted distances. -/
private theorem format_le_site {V : Type} [LinearOrder V] {φ : PolMul.Spectral ℂ}
    {τ : Fin 3 → V} {d : V → V → ℝ} (hd : MinAdm φ τ d)
    (w : Fin 3 → ℝ) (hw : ∀ i, 0 ≤ w i) (q : V) :
    Fv φ w ≤ ∑ i, w i * d q (τ i) := by
  apply Fv_le_of φ (Finset.sum_nonneg fun i _ => mul_nonneg (hw i) (hd.2.1 _ _))
  intro D k W _ hk
  by_cases hpos : 0 < value φ W
  · have hval := hd.1 _ _ _ (starNet τ q W) (Local_starNet τ q W) (by rwa [Z_starNet])
    rw [Z_starNet, cost_starNet d hd.2.2.1] at hval
    apply (Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ) < 2) hpos).mp
    apply hval.trans
    rw [Finset.mul_sum, Fin.sum_univ_three]
    have leg (i) : d q (τ i) * (k i : ℝ) ≤ D * (w i * d q (τ i)) :=
      (mul_le_mul_of_nonneg_left (hk i) (hd.2.1 _ _)).trans_eq (by ring)
    exact add_le_add (add_le_add (leg 0) (leg 1)) (leg 2)
  · exact (not_lt.mp hpos).trans (by positivity)

/-- The supporting site minimizes the weighted sum. The three terminal distances
are bounded by the prices of their corresponding equality tensors. -/
theorem weighted_price_space (crossing : S_R108_3) (φ : PolMul.Spectral ℂ)
    (w : Fin 3 → ℝ) (hw : ∀ i, 0 < w i) :
    ∃ (S : MidSpace Tm) (o : Tm) (p : Fin 3 → Tm),
      (∀ x, Fv φ w ≤ ∑ i, w i * S.d x (p i)) ∧ (∑ i, w i * S.d o (p i)) ≤ Fv φ w ∧
      S.d (p 1) (p 2) ≤ theta φ 0 ∧ S.d (p 2) (p 0) ≤ theta φ 1 ∧ S.d (p 0) (p 1) ≤ theta φ 2 := by
  obtain ⟨h, hn, hsum, hs⟩ := supporting_price_at φ w hw
  obtain ⟨d,hd,hle⟩ := exists_minAdm (initial_admissible φ h hn hs)
    (fun s t => by fin_cases s <;> fin_cases t <;> first | exact le_rfl | exact hn _ | exact theta_nonneg φ _)
    (fun s => by fin_cases s <;> rfl)
  let base : {d : Lv 0 → Lv 0 → ℝ // MinAdm φ (τL 0) d} := ⟨d,hd⟩
  let S : MidSpace Tm :=
    ⟨dX crossing base, Tm.node, dX_self crossing base, dX_symm crossing base,
      dX_tri crossing base, dX_node_row crossing base, dX_node_col crossing base,
      dX_node_self crossing base, dX_quad crossing base⟩
  refine ⟨S,Tm.leaf 3,fun i => Tm.leaf i.castSucc,?_,?_,hle 1 2,hle 2 0,hle 0 1⟩
  · intro x
    change Fv φ w ≤ ∑ i, w i * dX crossing base x (Tm.leaf i.castSucc)
    simp only [dX_leaf]
    exact format_le_site (tower crossing base x.depth).2 w (fun i => (hw i).le) _
  · rw [← hsum]
    refine Finset.sum_le_sum fun i _ => ?_
    change w i * d 3 i.castSucc ≤ h i * w i
    have hb : d 3 i.castSucc ≤ h i := by fin_cases i <;> exact hle _ _
    exact (mul_le_mul_of_nonneg_left hb (hw i).le).trans_eq (mul_comm _ _)

end OM.NNN36

