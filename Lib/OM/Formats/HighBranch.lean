import Lib.OM.Formats.DiscWitness
import Lib.OM.Formats.PlanarWork
import Lib.OM.Formats.SpectralRate
import PLATFORM.Statements.«NNN.48»
import PLATFORM.Statements.«NNN.49»

/-! # The high branch of the format dichotomy -/

noncomputable section
namespace OM.Formats

open scoped InnerProductSpace
open NNN34 NNN22 Foundations.PairUnitExponents

theorem proof_NNN_48 : S_NNN_48 := by
  intro hg a b c ha hab hbc ht
  have hb := ha.trans_le hab
  have hc := hb.trans_le hbc
  have flat := flattening_rate ha.le hb.le ht.le
  by_cases acute : c^2 < a^2+b^2
  · obtain ⟨p,q,l,r,hp,hq,hs,hd,per,work⟩ := acute_witness ha hab hbc ht acute
    have H := boundary_work hg hc (hc.le.trans flat) p q l r (hp.symm ▸ ha) (hq.symm ▸ hb) hp.le hq.le hs.le hd
    rw [work] at H
    have bound := le_of_mul_le_mul_right H per
    change 2 * P2M.R116.discRadius a b c ≤ formatBeta a b c
    linarith only [bound]
  · rw [show P2M.R116.discRadius a b c = c/2 from ite_eq_right acute]
    change 2 * (c/2) ≤ formatBeta a b c
    linarith only [flat]

theorem proof_NNN_49 : S_NNN_49 := by
  intro hg hω a b c ha hab hbc ht
  apply le_antisymm _ (proof_NNN_48 hg a b c ha hab hbc ht)
  have hb := ha.trans_le hab
  have hc := hb.trans_le hbc
  obtain ⟨q,o,hq,hbq,h₀,h₁,h₂⟩ := enclosing_disc ha hab hbc ht
  have hr := (dist_nonneg (x:=o) (y:=(0:ℂ))).trans h₀
  apply beta_le_of_price (y := ![a,b,c]) (fun i => by fin_cases i <;> assumption)
  intro φ
  have H := NNN36.triangle_price NNN30.proof_R108_3 φ 0 (c:ℂ) q o ha hb hc hq
    (by simpa only [sub_zero] using hbq)
    (by rw [zero_sub,norm_neg,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hc])
  have total := NNN30.sum_le_omega φ
  rw [hω] at total
  apply H.trans
  nlinarith only [mul_le_mul_of_nonneg_right h₀ (theta_nonneg φ 0),
    mul_le_mul_of_nonneg_right h₁ (theta_nonneg φ 1),mul_le_mul_of_nonneg_right h₂ (theta_nonneg φ 2),
    mul_le_mul_of_nonneg_left total hr]

end OM.Formats

