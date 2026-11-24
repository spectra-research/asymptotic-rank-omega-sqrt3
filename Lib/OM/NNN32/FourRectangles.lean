import Lib.OM.NNN32.FourPrices
import Lib.OM.NNN32.FourSums
import Lib.OM.NNN30.Net.Cross

/-! # Row and column realizations retaining all four outputs -/

noncomputable section
open scoped Classical

namespace OM.NNN32.FourNetwork

open Semicontinuity AsymptoticSpectrumDuality OM.NNN30.Net

variable {V : Type} [Fintype V] [LinearOrder V] {f : Fin 4 → ℕ+}
variable (N : FourNetwork (V × V) f) {K A B : Rect V → ℕ}
variable (pieces : (R : Rect V) → Fin (K R) → Fin (A R) → Fin (B R) → Fin (B R) → Fin (A R) → ℂ)
variable (u : (R : Rect V) → N.packed.I1 R ↪ Fin (A R))
variable (v : (R : Rect V) → N.packed.I2 R ↪ Fin (B R))

private def rows (m : (R : Rect V) → Fin (K R)) : FourNetwork V f :=
  ⟨{ N.packed.rowNet pieces u v m with out0 := fun _ _ => 1, out1 := fun _ _ => 1, out2 := fun _ _ => 1 },N.out⟩

private def cols (m : (R : Rect V) → Fin (K R)) : FourNetwork V f :=
  ⟨{ N.packed.colNet pieces u v m with out0 := fun _ _ => 1, out1 := fun _ _ => 1, out2 := fun _ _ => 1 },N.out⟩

private def piece (m : (R : Rect V) → Fin (K R)) : KTensor ℂ f :=
  fun a => N.packed.Zmu pieces u v m a () ()

private lemma rows_local {τ : Fin 4 → V} (h : N.Local (fun i => (τ i,τ i))) (m) :
    (N.rows pieces u v m).Local τ := by
  have b := N.silent.Local_rowNet pieces u v (silent_local h) m
  refine ⟨?_,?_,fun i a x y e => h.2.2 i a x y (fun z hz => e z (congrArg Prod.fst hz))⟩
  · rintro (k|k) z
    · exact b.1 (.inl k) z
    · exact b.1 (.inr k) z
  · rintro (k|k) z
    · exact b.2.1 (.inl k) z
    · exact b.2.1 (.inr k) z

private lemma cols_local {τ : Fin 4 → V} (h : N.Local (fun i => (τ i,τ i))) (m) :
    (N.cols pieces u v m).Local τ := by
  have b := N.silent.Local_colNet pieces u v (silent_local h) m
  refine ⟨?_,?_,fun i a x y e => h.2.2 i a x y (fun z hz => e z (congrArg Prod.snd hz))⟩
  · rintro (k|k) z
    · exact b.1 (.inl k) z
    · exact b.1 (.inr k) z
  · rintro (k|k) z
    · exact b.2.1 (.inl k) z
    · exact b.2.1 (.inr k) z

include u v in
theorem rectangle_price {φ : AsymptoticSpectrum fourPreorder} {τ : Fin 4 → V} {d : V → V → ℝ}
    (hd : Valid φ τ d) (hl : N.Local (fun i => (τ i,τ i))) (hp : 0 < value φ N)
    (hs : ∀ R z y y' z', ∑ m, pieces R m z y y' z' = if z=z' ∧ y=y' then 1 else 0) :
    ∃ m : (R : Rect V) → Fin (K R), (∀ R, pieces R (m R) ≠ 0) ∧
      Real.logb 2 (value φ N) ≤ Real.logb 2 (Fintype.card ((R : Rect V) → Fin (K R))) +
        (N.packed.ndCost d + ∑ R, (d R.a R.c * Real.logb 2 (TN.rowMat pieces R (m R)).rank +
          d R.b R.e * Real.logb 2 (TN.colMat pieces R (m R)).rank)/2) := by
  classical
  let F := N.piece pieces u v
  have hZ : N.tensor = ∑ m, F m := by
    funext a
    simpa only [Finset.sum_apply,tensor,F,piece] using congrFun (congrFun (congrFun (N.packed.Z_eq_sum_Zmu pieces u v hs) a) ()) ()
  change 0 < fourValue φ N.tensor at hp
  have hn : (Finset.univ : Finset ((R : Rect V) → Fin (K R))).Nonempty := by
    by_contra! he
    rw [hZ,he,Finset.sum_empty,fourValue_zero] at hp
    exact lt_irrefl _ hp
  obtain ⟨m,_,hm⟩ := Finset.exists_max_image Finset.univ (fun m => fourValue φ (F m)) hn
  have hcard : (0:ℝ) < Fintype.card ((R : Rect V) → Fin (K R)) := by exact_mod_cast Fintype.card_pos_iff.2 ⟨m⟩
  have hsum : fourValue φ N.tensor ≤ Fintype.card ((R : Rect V) → Fin (K R)) * fourValue φ (F m) := by
    rw [hZ]
    apply (fourValue_sum _ _ _).trans
    simpa using Finset.sum_le_sum (fun n hn => hm n hn)
  have hpos : 0 < fourValue φ (F m) := pos_of_mul_pos_right (hp.trans_le hsum) hcard.le
  refine ⟨m,?_,?_⟩
  · intro R hR
    have hz : F m = 0 := by
      funext a
      apply Finset.sum_eq_zero
      intro x _
      have hphi : N.packed.Phi pieces u v R (m R) x = 0 := by unfold TN.Phi; simp [hR]
      rw [Finset.prod_eq_zero (Finset.mem_univ R) hphi]; simp
    rw [hz,fourValue_zero] at hpos
    exact lt_irrefl _ hpos
  · have er : (N.rows pieces u v m).tensor = F m := by
      funext a
      exact congrFun (congrFun (congrFun (N.packed.Z_rowNet pieces u v m) a) ()) ()
    have ec : (N.cols pieces u v m).tensor = F m := by
      funext a
      exact congrFun (congrFun (congrFun (N.packed.Z_colNet pieces u v m) a) ()) ()
    have hr : Real.logb 2 (fourValue φ (F m)) ≤ (N.packed.rowNet pieces u v m).cost d := by
      rw [← er]
      exact hd _ (N.rows_local pieces u v hl m) (by simpa [value,er] using hpos)
    have hc : Real.logb 2 (fourValue φ (F m)) ≤ (N.packed.colNet pieces u v m).cost d := by
      rw [← ec]
      exact hd _ (N.cols_local pieces u v hl m) (by simpa [value,ec] using hpos)
    have havg := N.packed.avg_cost pieces u v d m
    have hlog := Real.logb_le_logb_of_le (by norm_num : (1:ℝ)<2) hp hsum
    rw [Real.logb_mul hcard.ne' hpos.ne'] at hlog
    change Real.logb 2 (fourValue φ N.tensor) ≤ _
    linarith

end OM.NNN32.FourNetwork
