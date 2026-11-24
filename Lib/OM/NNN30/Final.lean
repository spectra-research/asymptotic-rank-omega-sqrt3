import Lib.OM.NNN22.Asm
import Lib.OM.Omega
import PLATFORM.Statements.«R111.1»
import PLATFORM.Statements.«R111.2»
import PLATFORM.Statements.«R111.3»
import PLATFORM.Statements.«NNN.30»
import PLATFORM.Statements.«NNN.31»

/-! # R111.3, NNN.30 and NNN.31 from the geometry (R111.1) and the price metric (R111.2)

* `cube_of : S_R111_1 → S_R111_2 → S_R111_3`: at a spectral point `φ`, R111.2 gives a
  midpoint space with terminals `p i` and a point `o` whose distance sum is `g = F(1,1,1)` and minimal (5); R111.1
  gives `d(p i, p j)² ≥ h_i² + h_i h_j + h_j² ≥ (3/4)(h_i + h_j)²`; summing the square roots over the three pairs,
  `√3 g = √3 Σ h ≤ Σ d(p i, p j) ≤ θ 0 + θ 1 + θ 2`.
* `nnn30_of`: R88.17 at `B = 3√3/4`, since `F(1,1,1) ≤ Σθ/√3 ≤ (9/4)/√3 = 3√3/4`
  (`OM.Omega.theta_sum_le_nine_quarters`).
* `nnn31_of`: R88.18 at `B = 2/√3`, since its hypothesis carries `Σθ ≤ 2`. -/

noncomputable section

namespace OM.NNN30.Fin

open Foundations.PairUnitExponents

/-- `x ≥ (√3/2)(a + b)` from `x² ≥ a² + ab + b²` for nonnegative `a, b, x`. -/
lemma half_sqrt3_le {a b x : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hx : 0 ≤ x)
    (h : a ^ 2 + a * b + b ^ 2 ≤ x ^ 2) : Real.sqrt 3 / 2 * (a + b) ≤ x := by
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
  have hl : 0 ≤ Real.sqrt 3 / 2 * (a + b) := by positivity
  have hsq : (Real.sqrt 3 / 2 * (a + b)) ^ 2 ≤ x ^ 2 := by
    have : (Real.sqrt 3 / 2 * (a + b)) ^ 2 = 3 / 4 * (a + b) ^ 2 := by
      rw [mul_pow, div_pow, h3]; ring
    rw [this]
    nlinarith [sq_nonneg (a - b)]
  exact (pow_le_pow_iff_left₀ hl hx (by norm_num)).1 hsq

/-- **R111.1 ∧ R111.2 ⇒ R111.3**. -/
theorem cube_of (h1 : S_R111_1) (h2 : S_R111_2) : S_R111_3 := by
  intro φ
  obtain ⟨X, d, m, p, o, hd0, hsymm, htri, hax1, hax2, hdiag, hquad, hferm, ho, h12, h02, h01⟩ := h2 φ
  set g := P2M.R88.Fv φ (fun _ => 1) with hg
  have hnn : ∀ x y, 0 ≤ d x y := by
    intro x y
    have := htri x y x
    rw [hd0 x, hsymm y x] at this
    linarith
  -- `o` minimises the distance sum
  have hmin : ∀ q, d o (p 0) + d o (p 1) + d o (p 2) ≤ d q (p 0) + d q (p 1) + d q (p 2) :=
    fun q => ho.trans (hferm q)
  have hsum : d o (p 0) + d o (p 1) + d o (p 2) = g := le_antisymm ho (hferm o)
  have hang := h1 X d m p o hd0 hsymm htri hax1 hax2 hdiag hquad hmin
  have e01 := half_sqrt3_le (hnn o (p 0)) (hnn o (p 1)) (hnn (p 0) (p 1))
    (hang 0 1 (by decide))
  have e02 := half_sqrt3_le (hnn o (p 0)) (hnn o (p 2)) (hnn (p 0) (p 2))
    (hang 0 2 (by decide))
  have e12 := half_sqrt3_le (hnn o (p 1)) (hnn o (p 2)) (hnn (p 1) (p 2))
    (hang 1 2 (by decide))
  have key : Real.sqrt 3 * g ≤ d (p 0) (p 1) + d (p 0) (p 2) + d (p 1) (p 2) := by
    rw [← hsum]
    linarith
  linarith

/-- **R111.3 ⇒ NNN.30** (R88.17 at `B = 3√3/4`). -/
theorem nnn30_of (h3 : S_R111_3) : S_NNN_30 := by
  have hs3 : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have h33 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  refine OM.NNN22.proof_R88_17 (3 * Real.sqrt 3 / 4) (by positivity) ?_
  intro φ _ _ _ _
  have hc := h3 φ
  have hs := OM.Omega.theta_sum_le_nine_quarters φ
  -- `√3 F ≤ 9/4`, multiply by `√3`
  have h1 : Real.sqrt 3 * P2M.R88.Fv φ (fun _ => 1) ≤ 9 / 4 := hc.trans hs
  have h2 : Real.sqrt 3 * (Real.sqrt 3 * P2M.R88.Fv φ (fun _ => 1)) ≤ Real.sqrt 3 * (9 / 4) :=
    mul_le_mul_of_nonneg_left h1 hs3.le
  rw [← mul_assoc, h33] at h2
  linarith

/-- **R111.3 ⇒ NNN.31** (R88.18 at `B = 2/√3`). -/
theorem nnn31_of (h3 : S_R111_3) : S_NNN_31 := by
  have hs3 : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  refine OM.NNN22.proof_R88_18 (2 / Real.sqrt 3) (by positivity) ?_
  intro φ _ _ hs _
  have hc := h3 φ
  rw [le_div_iff₀ hs3, mul_comm]
  linarith

end OM.NNN30.Fin

