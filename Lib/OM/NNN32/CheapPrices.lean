import Lib.OM.NNN32.InsertionBill
import Lib.OM.NNN32.SplitScale
import Lib.OM.NNN32.FourTower
import PLATFORM.Statements.«R113.18»

/-! # Cheap crossing splits enforce the two-term inequality at every minimal price -/

noncomputable section
open scoped Classical

namespace OM.NNN32

open Semicontinuity AsymptoticSpectrumDuality OM.NNN30.Net

private lemma two_le_of_bits (n : ℕ) (h : 0 < Real.logb 2 n) : 2 ≤ n := by
  by_contra! hn
  interval_cases n <;> norm_num at h

private lemma log_rank_le {b : ℕ+} {p n : ℕ} {K : ℝ}
    (hb : 0 < Real.logb 2 (b:ℕ)) (hK : 0 ≤ K)
    (hn : (n:ℝ) ≤ ((b:ℕ):ℝ)^((p:ℝ)*K)) :
    Real.logb 2 n ≤ K * Real.logb 2 ((b^p:ℕ+):ℕ) := by
  have he : Real.logb 2 ((b^p:ℕ+):ℕ) = (p:ℝ) * Real.logb 2 (b:ℕ) := by
    change Real.logb 2 (((b:ℕ)^p:ℕ):ℝ) = _
    rw [Nat.cast_pow,Real.logb_pow]
  rw [he]
  rcases Nat.eq_zero_or_pos n with rfl | hp
  · simp only [Nat.cast_zero,Real.logb_zero]
    positivity
  · have h := Real.logb_le_logb_of_le (by norm_num : (1:ℝ)<2) (show (0:ℝ)<n by exact_mod_cast hp) hn
    rw [Real.logb_rpow_eq_mul_logb_of_pos (by exact_mod_cast b.2)] at h
    linarith

namespace FourNetwork

private lemma common_base {V : Type} {f : Fin 4 → ℕ+} {φ : AsymptoticSpectrum fourPreorder}
    (M : FourNetwork V f) (hp : 0 < value φ M) (t : Fin 4 → V) (ht : t 0 ≠ t 1)
    (hw : 0 < min (M.graph.wid (t 0) (t 3)) (M.graph.wid (t 1) (t 2))) :
    ∃ b : ℕ+, 2 ≤ b ∧ Real.logb 2 (b:ℕ) = min (M.graph.wid (t 0) (t 3)) (M.graph.wid (t 1) (t 2)) := by
  obtain ⟨ha,hb⟩ := M.bundle_widths t ht (ranks_positive hp)
  rw [← ha,← hb] at hw ⊢
  let a := Fintype.card (M.bundle t 0)
  let b := Fintype.card (M.bundle t 1)
  have ha' := two_le_of_bits a (hw.trans_le (min_le_left _ _))
  have hb' := two_le_of_bits b (hw.trans_le (min_le_right _ _))
  rcases le_total a b with h | h
  · refine ⟨⟨a,by omega⟩,ha',?_⟩
    exact (min_eq_left (Real.logb_le_logb_of_le (by norm_num) (by exact_mod_cast (show 0<a by omega))
      (by exact_mod_cast h))).symm
  · refine ⟨⟨b,by omega⟩,hb',?_⟩
    exact (min_eq_right (Real.logb_le_logb_of_le (by norm_num) (by exact_mod_cast (show 0<b by omega))
      (by exact_mod_cast h))).symm

/-- A local charge strictly below the two diagonal prices would give a
positive discount linear in the common width. A near-tight network and all
its powers contradict this estimate along the favorable split scales. -/
theorem finite_twoTerm {V : Type} {φ : AsymptoticSpectrum fourPreorder}
    {τ : Fin 4 → V} {d : V → V → ℝ} (hd : Minimal φ τ d) {κ : ℝ} (hk : 0 ≤ κ)
    (hcheap : ∀ M : ℕ+, ∃ D : ℕ+, M ≤ D ∧ (P D : ℝ) ≤ ((D:ℕ):ℝ)^κ) :
    twoTermBound d κ := by
  intro t hsep u v w x
  let L := d (t 0) (t 3) + d (t 1) (t 2)
  let row := d (t 0) u + d (t 1) u + d (t 2) v + d (t 3) v
  let col := d (t 0) w + d (t 2) w + d (t 1) x + d (t 3) x
  let U := max (row + κ*d u v) (col + κ*d w x)
  change L ≤ U
  by_contra! hu
  let δ := (L-U)/4
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hd0 := hd.2.1
  have huv := hd0 u v
  have hwx := hd0 w x
  let ε := δ / (1+d u v+d w x)
  have hden : 0 < 1+d u v+d w x := by change 0 ≤ d u v at huv; change 0 ≤ d w x at hwx; linarith
  have hε : 0 < ε := div_pos hδ hden
  have herr : ε*(1+d u v+d w x) = δ := div_mul_cancel₀ _ hden.ne'
  have chR : row + (κ+ε)*d u v ≤ L-2*δ := by
    have h := mul_le_mul_of_nonneg_left (show d u v ≤ 1+d u v+d w x by
      change 0 ≤ d w x at hwx; linarith) hε.le
    have hm : row + κ*d u v ≤ U := le_max_left _ _
    dsimp [δ] at herr ⊢
    linarith
  have chS : col + (κ+ε)*d w x ≤ L-2*δ := by
    have h := mul_le_mul_of_nonneg_left (show d w x ≤ 1+d u v+d w x by
      change 0 ≤ d u v at huv; linarith) hε.le
    have hm : col + κ*d w x ≤ U := le_max_right _ _
    dsimp [δ] at herr ⊢
    linarith
  have ht : t 0 ≠ t 1 := by
    intro h
    have z := hsep 0 1 (by decide)
    rw [h,hd.2.2.1] at z
    exact lt_irrefl _ z
  obtain ⟨_,M,hM,hp,hgap⟩ := small_gap hd (hsep 0 3 (by decide)) (hsep 1 2 (by decide)) hδ
  have hwidth := pos_of_mul_pos_right ((gap_nonneg hd.1 hM hp).trans_lt hgap) hδ.le
  obtain ⟨b,hb,he⟩ := common_base M hp t ht hwidth
  let B := Real.logb 2 (b:ℕ)
  have hB : 0 < B := he.trans_gt hwidth
  rw [← he] at hgap
  obtain ⟨m,hm⟩ := exists_nat_gt ((1+L)/(δ*B))
  obtain ⟨p,hm',r,s,hrs,A,E,A',E',hfac⟩ := cheap_split_factors hk hcheap b hb hε (m+1)
  have hpp : (0:ℝ) < p := by exact_mod_cast (show 0<p by omega)
  have hlarge : 1+L < (p:ℝ)*(δ*B) := (div_lt_iff₀ (mul_pos hδ hB)).1
    (hm.trans_le (by exact_mod_cast (show m ≤ p by omega)))
  let D := b^p
  have bits : Real.logb 2 (D:ℕ) = (p:ℝ)*B := by
    change Real.logb 2 (((b:ℕ)^p:ℕ):ℝ) = _
    rw [Nat.cast_pow,Real.logb_pow]
  obtain ⟨_,N,hN,hq,hg,hw₀,hw₁⟩ := M.powered_data hM hp (t 0) (t 3) (t 1) (t 2) d p
  have width₀ : Real.logb 2 (D:ℕ) ≤ N.graph.wid (t 0) (t 3) := by
    rw [bits,hw₀]
    exact mul_le_mul_of_nonneg_left (he.trans_le (min_le_left _ _)) hpp.le
  have width₁ : Real.logb 2 (D:ℕ) ≤ N.graph.wid (t 1) (t 2) := by
    rw [bits,hw₁]
    exact mul_le_mul_of_nonneg_left (he.trans_le (min_le_right _ _)) hpp.le
  let F : FactorSites V D := ⟨Equiv.refl _,u,v,r,A,E⟩
  let G : FactorSites V D := ⟨Equiv.swap 1 2,w,x,s,A',E'⟩
  have sums : crossing D = F.kernel + G.kernel := by
    funext y
    simpa [F,G,FactorSites.kernel,crossing,matching,Equiv.swap_apply_def] using
      hfac (y 0) (y 1) (y 2) (y 3)
  have leavesF : F.leaves d t = row := by
    simp [F,FactorSites.leaves,FactorSites.hub,Fin.sum_univ_four,row]
  have leavesG : G.leaves d t = col := by
    simp [G,FactorSites.leaves,FactorSites.hub,Fin.sum_univ_four,Equiv.swap_apply_def,col]
    ring
  have hr : (r:ℝ) ≤ ((r+s : ℕ):ℝ) := by exact_mod_cast Nat.le_add_right r s
  have hs : (s:ℝ) ≤ ((r+s : ℕ):ℝ) := by exact_mod_cast Nat.le_add_left s r
  have bound := gap_from_split hd.1 hd0 N hN hq t ht (bits.trans_gt (mul_pos hpp hB)) width₀ width₁ F G sums
    (log_rank_le hB (add_nonneg hk hε.le) (hr.trans hrs))
    (log_rank_le hB (add_nonneg hk hε.le) (hs.trans hrs))
    (by rw [leavesF]; exact chR) (by rw [leavesG]; exact chS)
  rw [bits,hg] at bound
  have hover := mul_lt_mul_of_pos_left hgap hpp
  change (p:ℝ)*gap M φ d < (p:ℝ)*(δ*B) at hover
  dsimp [L] at hlarge
  linarith only [bound,hlarge,hover]

end FourNetwork

theorem proof_R113_18 : S_R113_18 := by
  intro κ hk _ hcheap _ φ
  exact ⟨_,FourNetwork.space φ,Tm.leaf,
    FourNetwork.twoTerm_of_levels (fun k => FourNetwork.finite_twoTerm (FourNetwork.level φ k).2 hk hcheap),
    FourNetwork.terminal_value φ⟩

end OM.NNN32
