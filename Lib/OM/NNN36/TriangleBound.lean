import Lib.OM.NNN30.RectMain
import Lib.OM.NNN36.TrianglePrice
import Lib.OM.NNN36.RectExponent
import Lib.OM.NNN36.Wide
import Lib.OM.NNN36.Coordinates
import PLATFORM.Statements.«R115.4»
import Mathlib.Analysis.Convex.Topology

/-! # The rectangular exponent bound on the closed triangle -/

namespace OM.NNN36

open P2M.R115 Semicontinuity

noncomputable abbrev sideLog (n : ℕ+) := Real.logb 2 (n : ℕ)

theorem sideLog_mono {m n : ℕ+} (h : m ≤ n) : sideLog m ≤ sideLog n :=
  Real.logb_le_logb_of_le one_lt_two (by positivity) (by exact_mod_cast h)

theorem rank_at_point (n₁ n₂ n₃ : ℕ+) (h₁₂ : n₁ ≤ n₂) (h₂₃ : n₂ ≤ n₃)
    (ht : sideLog n₃ < sideLog n₁ + sideLog n₂) (z : ℂ) :
    let q := (sideLog n₃ : ℂ) * normalizedApex (sideLog n₁) (sideLog n₂) (sideLog n₃)
    Real.logb 2 (formatRankSup n₁ n₂ n₃) ≤
      OmegaBound.omegaRect3 ℂ (dist z 0) (dist z (sideLog n₃ : ℂ)) (dist z q) := by
  let a := sideLog n₁
  let b := sideLog n₂
  let c := sideLog n₃
  let q := (c : ℂ)*normalizedApex a b c
  let d := PolMul.fmt n₁ n₂ n₃
  have hab : a ≤ b := sideLog_mono h₁₂
  have hbc : b ≤ c := sideLog_mono h₂₃
  have ha : 0 < a := by change c < a+b at ht; linarith
  have hb := ha.trans_le hab
  have hc := hb.trans_le hbc
  obtain ⟨_,_,hside₁,hside₂⟩ := apex_geometry ha hab hbc ht
  have hside₃ : ‖(0 : ℂ) - (c : ℂ)‖ = c := by simp [abs_of_pos hc]
  have widths : (fun i => Real.logb 2 (d i : ℕ)) = ![a,b,c] := by funext i; fin_cases i <;> rfl
  have hpos (i) : 0 < Real.logb 2 (d i : ℕ) := by
    change 0 < (fun j => Real.logb 2 (d j : ℕ)) i
    rw [widths]; fin_cases i <;> first | exact ha | exact hb | exact hc
  apply (Real.logb_le_iff_le_rpow one_lt_two (formatRankSup_pos ..)).mpr
  refine csSup_le (Set.range_nonempty _) ?_
  rintro _ ⟨T,rfl⟩
  apply NNN.asympRank_le_of_spectral_bound T _ (by positivity)
  intro φ
  by_cases hval : 0 < φ.eval T
  · apply (Real.logb_le_iff_le_rpow one_lt_two hval).mp
    have heval := log_eval_le_Fv (d := d) φ T hval hpos
    rw [widths] at heval
    have hprice := triangle_price NNN30.proof_R108_3 φ 0 c q z ha hb hc hside₁
      (by simpa only [sub_zero] using hside₂) hside₃
    exact (heval.trans hprice).trans (theta_dot_le_omegaRect3 φ dist_nonneg dist_nonneg dist_nonneg)
  · exact (not_lt.mp hval).trans (by positivity)

theorem proof_R115_4 : S_R115_4 := by
  intro n₁ n₂ n₃ h₁₂ h₂₃
  dsimp only
  intro ht
  let c := sideLog n₃
  let q := (c : ℂ)*normalizedApex (sideLog n₁) (sideLog n₂) c
  let V : Set ℂ := {0,(c : ℂ),q}
  have hV : V.Finite := by simp [V]
  have hne : (convexHull ℝ V).Nonempty :=
    ⟨0, subset_convexHull ℝ V (by simp [V])⟩
  obtain ⟨z,hz,hmin⟩ := (hV.isCompact_convexHull ℝ).exists_isMinOn hne
    (continuous_rectangular_cost (F := ℂ) (0 : ℂ) (c : ℂ) q).continuousOn
  exact ⟨z,hz,fun _ hy => hmin hy, rank_at_point n₁ n₂ n₃ h₁₂ h₂₃ ht z⟩

end OM.NNN36

