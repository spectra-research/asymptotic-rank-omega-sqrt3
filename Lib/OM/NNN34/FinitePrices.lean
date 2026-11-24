import Lib.OM.NNN34.Insertion
import Lib.OM.NNN34.NetworkPricing
import Lib.OM.NNN34.PartitionGrowth
import PLATFORM.Statements.«R114.18»

/-! # Minimal finite prices at cofinally cheap partition weights -/

namespace OM.NNN34

open NNN32 FourNetwork AsymptoticSpectrumDuality P2M.R114 Filter Topology

theorem proof_R114_18 : S_R114_18 := by
  intro bL bN _ _ cheap V _ φ τ d hd t separated ports o u v
  let L := d (t 0) (t 3)+d (t 1) (t 2)
  let C := d (t 0) u+d (t 2) u+d (t 1) v+d (t 3) v
  let R := rowCharge d t ports o bL bN
  let U := max R (C+Real.sqrt 3*d u v)
  change L ≤ U
  by_contra! hU
  let δ := (L-U)/4
  have hg : 0 < δ := by dsimp [δ]; linarith
  have hdv : 0 ≤ d u v := hd.2.1 u v
  let ε := δ/(1+d u v)
  have hden : 0 < 1+d u v := by linarith
  have hε : 0 < ε := div_pos hg hden
  have herr : ε*(1+d u v) = δ := div_mul_cancel₀ _ hden.ne'
  have hR : R ≤ L-2*δ := by
    have h : R ≤ U := le_max_left _ _
    dsimp [δ]; linarith
  have hC : C+(Real.sqrt 3+ε)*d u v ≤ L-2*δ := by
    have h : C+Real.sqrt 3*d u v ≤ U := le_max_right _ _
    dsimp only [δ] at herr ⊢
    linarith only [h,herr,hε.le,hU.le]
  have ht : t 0 ≠ t 1 := by
    intro he
    have h := separated 0 1 (by decide +kernel)
    rw [he,hd.2.2.1] at h
    exact lt_irrefl _ h
  obtain ⟨_,M,hM,hp,hgap⟩ := small_gap hd (separated 0 3 (by decide +kernel)) (separated 1 2 (by decide +kernel)) hg
  let w := min (M.graph.wid (t 0) (t 3)) (M.graph.wid (t 1) (t 2))
  have hw : 0 < w := pos_of_mul_pos_right ((gap_nonneg hd.1 hM hp).trans_lt hgap) hg.le
  have hbits : Tendsto (fun H : ℕ => Real.logb 2 (partitionSide H : ℕ)) atTop atTop :=
    (Real.tendsto_logb_atTop one_lt_two).comp (tendsto_natCast_atTop_atTop.comp proof_R114_13.1)
  have large := hbits.eventually_gt_atTop (w+(1+L)/δ)
  have suffix := proof_R114_13.2.2.eventually (Iio_mem_nhds (show Real.sqrt 3 < Real.sqrt 3+ε by linarith))
  obtain ⟨H₀,h₀⟩ := eventually_atTop.mp ((large.and suffix).and (proof_R114_13.1.eventually_ge_atTop 2))
  obtain ⟨H,hH,hleft,hright⟩ := cheap H₀
  obtain ⟨⟨hlarge,hrank⟩,hD⟩ := h₀ H ((le_max_right _ _).trans hH)
  let B := Real.logb 2 (partitionSide H : ℕ)
  have hB : 0 < B := Real.logb_pos one_lt_two (by exact_mod_cast (show 1 < (partitionSide H : ℕ) from hD))
  change w+(1+L)/δ < B at hlarge
  let p := ⌈B/w⌉₊
  have low : B ≤ (p : ℝ)*w := (div_le_iff₀ hw).mp (Nat.le_ceil _)
  have high : (p : ℝ)*w < B+w := by
    have h := mul_lt_mul_of_pos_right (Nat.ceil_lt_add_one (div_nonneg hB.le hw.le)) hw
    rwa [add_mul,one_mul,div_mul_cancel₀ _ hw.ne'] at h
  have hpp : 0 < (p : ℝ) := pos_of_mul_pos_left (hB.trans_le low) hw.le
  obtain ⟨_,N,hN,hq,hgN,hw₀,hw₁⟩ := M.powered_data hM hp (t 0) (t 3) (t 1) (t 2) d p
  have bound := insertion_gap proof_R114_16 hd N hN hq t ports o u v ht
    ((le_max_left _ _).trans hH) hD
    (hw₀.symm ▸ low.trans (mul_le_mul_of_nonneg_left (min_le_left _ _) hpp.le))
    (hw₁.symm ▸ low.trans (mul_le_mul_of_nonneg_left (min_le_right _ _) hpp.le))
    hleft hright (le_of_lt hrank) hR hC
  rw [hgN] at bound
  have small : (p : ℝ)*gap M φ d < δ*((p : ℝ)*w) := by
    exact (mul_lt_mul_of_pos_left hgap hpp).trans_eq (by ring)
  have margin : 1+L < (B-w)*δ := (div_lt_iff₀ hg).mp (by linarith only [hlarge])
  change 2*δ*B-(1+d (t 0) (t 3)+d (t 1) (t 2)) ≤ (p : ℝ)*gap M φ d at bound
  dsimp only [L] at margin
  nlinarith only [bound,small,margin,mul_lt_mul_of_pos_left high hg]

end OM.NNN34

