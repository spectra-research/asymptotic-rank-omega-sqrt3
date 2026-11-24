import Lib.OM.NNN34.SectorApproximation
import Lib.OM.NNN32.FourTower
import Lib.OM.NNN32.MatchingWires
import Lib.OM.NNN32.Comparison
import PLATFORM.Statements.«R114.18»
import PLATFORM.Statements.«R114.19»

/-! # Transferring the two bills from finite price spaces to planar tests -/

namespace OM.NNN34

open NNN32 NNN32.FourNetwork NNN30.Net NNN30.Geom AsymptoticSpectrumDuality
open Semicontinuity Filter Topology

private abbrev Sites := Fin 4 ⊕ (Fin 4 ⊕ Fin 3)
private abbrev corner (i : Fin 4) : Sites := .inl i
private abbrev port (i : Fin 4) : Sites := .inr (.inl i)
private abbrev hub (j : Fin 3) : Sites := .inr (.inr j)

private def separated (d : Sites → Sites → ℝ) :=
  ∀ i j, i ≠ j → 0 < d (corner i) (corner j)

private def bills (d : Sites → Sites → ℝ) (l n : ℝ) :=
  let per (i j : Fin 4) := d (port i) (port j) + d (port j) (hub 0) + d (hub 0) (port i)
  d (corner 0) (corner 3) + d (corner 1) (corner 2) ≤
    max ((∑ i, d (corner i) (port i)) + l*per 0 1 + n*per 3 2)
      (d (corner 0) (hub 1) + d (corner 2) (hub 1) + d (corner 1) (hub 2) +
        d (corner 3) (hub 2) + Real.sqrt 3*d (hub 1) (hub 2))

private lemma bill_equiv {X : Type*} (d : X → X → ℝ) (l n : ℝ) :
    P2M.R114.triangleBillBound d l n ↔
      ∀ x : Sites → X, separated (fun i j => d (x i) (x j)) → bills (fun i j => d (x i) (x j)) l n := by
  constructor
  · intro h x hx
    exact h (fun i => x (corner i)) hx (fun i => x (port i)) (x (hub 0)) (x (hub 1)) (x (hub 2))
  · intro h t ht p o u v
    exact h (Sum.elim t (Sum.elim p ![o,u,v])) ht

private lemma scale_bills {d : Sites → Sites → ℝ} {l n s : ℝ} (hs : 0 ≤ s) (h : bills d l n) :
    bills (fun i j => s*d i j) l n := by
  have hh := mul_le_mul_of_nonneg_left h hs
  unfold bills at hh ⊢
  dsimp only at hh ⊢
  rw [mul_max_of_nonneg _ _ hs] at hh
  simp only [Fin.sum_univ_four] at hh ⊢
  convert hh using 1 <;> first | ring | congr 1 <;> ring

private lemma closed_bills (l n : ℝ) : IsClosed {d | bills d l n} := by
  unfold bills
  dsimp only
  apply isClosed_le <;> fun_prop

private lemma plane_of_sector {X : Type*} (S : MidSpace X) {o a b : X} (ha : 0 < S.d o a)
    (hd : 0 < 4*(S.d o a)^2*(S.d o b)^2-((S.d o a)^2+(S.d o b)^2-(delta S o a b)^2)^2)
    {l n : ℝ} (hb : P2M.R114.triangleBillBound S.d l n) :
    P2M.R114.triangleBillBound planeLength l n := by
  apply (bill_equiv _ _ _).mpr
  intro v sep
  let ε (k : ℕ) := 1/((k : ℝ)+1)
  choose scale hs x hx using fun k => approximate_plane S o a b ha hd v (show 0 < ε k by dsimp [ε]; positivity)
  let d (k : ℕ) (i j : Sites) := scale k * S.d (x k i) (x k j)
  let L (i j : Sites) := planeLength (v i) (v j)
  have herr : Tendsto ε atTop (𝓝 0) := by
    simpa only [ε, one_div, Function.comp_def, Nat.cast_add, Nat.cast_one] using!
      (tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop (R := ℝ))).comp (tendsto_add_atTop_nat 1)
  have lim (i j : Sites) : Tendsto (fun k => d k i j) atTop (𝓝 (L i j)) := by
    apply Metric.tendsto_nhds.mpr
    intro δ hδ
    filter_upwards [herr.eventually (Iio_mem_nhds hδ)] with k h
    exact (hx k i j).trans h
  have all : ∀ᶠ k in atTop, separated (d k) := by
    apply Filter.eventually_all.mpr
    intro i
    apply Filter.eventually_all.mpr
    intro j
    by_cases he : i = j
    · exact Eventually.of_forall fun _ hn => (hn he).elim
    exact ((lim (corner i) (corner j)).eventually (Ioi_mem_nhds (sep i j he))).mono fun _ h _ => h
  apply (closed_bills l n).mem_of_tendsto (tendsto_pi_nhds.mpr fun i => tendsto_pi_nhds.mpr (lim i))
  filter_upwards [all] with k hsep
  apply scale_bills (hs k).le
  apply (bill_equiv _ _ _).mp hb (x k)
  exact fun i j hij => pos_of_mul_pos_right (hsep i j hij) (hs k).le

theorem plane_of_finite_prices (finite : S_R114_18) : S_R114_19 := by
  intro hg l n hl hn cofinal
  have tower (φ : AsymptoticSpectrum fourPreorder) :
      P2M.R114.triangleBillBound (space φ).d l n := by
    apply (bill_equiv _ _ _).mpr
    intro x hx
    obtain ⟨k,y,hy⟩ := common_price_level (prices φ) x
    have eqd : (fun i j => (level φ k).val (y i) (y j)) = fun i j => (space φ).d (x i) (x j) :=
      funext fun i => funext fun j => hy i j
    rw [← eqd] at hx ⊢
    exact (bill_equiv _ _ _).mp (finite l n hl hn cofinal _ φ (site k) _ (level φ k).property) y hx
  by_contra violation
  have degen (φ : AsymptoticSpectrum fourPreorder) : degenerateSectors (space φ) := by
    intro o a b ha
    exact le_of_not_gt fun hd => violation (plane_of_sector (space φ) ha hd (tower φ))
  have spectral : P2M.R113.spectralFourPoint := by
    intro D φ
    let S := space φ
    let t : Fin 4 → Tm := Tm.leaf
    let p := fourPreorder
    have mv {i j k l : Fin 4} (hij : i ≠ j) (hkl : k ≠ l)
        (hdis : ∀ a : Fin 4, (a=i ∨ a=j) ↔ ¬(a=k ∨ a=l)) :
        AsymptoticSpectrum.eval p (TensorClass.mk ⟨_,matching D i j k l⟩) φ =
          ((D:ℕ):ℝ)^(S.d (t i) (t j) + S.d (t k) (t l)) := by
      rw [matching_eq_wires D hij hkl hdis, AsymptoticSpectrum.eval_mul, Real.rpow_add (by positivity)]
      exact congrArg₂ (· * ·) (terminal_value φ D i j hij) (terminal_value φ D k l hkl)
    let val (i j k l : Fin 4) := AsymptoticSpectrum.eval p (TensorClass.mk ⟨_,matching D i j k l⟩) φ
    change val 0 3 1 2 ≤ max (val 0 1 2 3) (val 0 2 1 3)
    unfold val
    rw [mv (i := 0) (j := 3) (k := 1) (l := 2) (by decide +kernel) (by decide +kernel) (by decide +kernel),
      mv (i := 0) (j := 1) (k := 2) (l := 3) (by decide +kernel) (by decide +kernel) (by decide +kernel),
      mv (i := 0) (j := 2) (k := 1) (l := 3) (by decide +kernel) (by decide +kernel) (by decide +kernel)]
    have side := fourPoint_of_degenerate S (degen φ) (t 0) (t 1) (t 3) (t 2)
    rw [S.d_comm (t 3) (t 2)] at side
    have hD : (1 : ℝ) ≤ (D : ℕ) := by exact_mod_cast D.pos
    rcases le_max_iff.mp side with h | h
    · exact (Real.rpow_le_rpow_of_exponent_le hD h).trans (le_max_left _ _)
    · exact (Real.rpow_le_rpow_of_exponent_le hD h).trans (le_max_right _ _)
  have hOne := NNN32.proof_R113_21 spectral
  rw [hg] at hOne
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

end OM.NNN34
