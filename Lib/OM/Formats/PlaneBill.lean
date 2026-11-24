import Lib.OM.Formats.CrossingBill
import Lib.OM.NNN34.PlanePrices

/-! # Real wire weights and planar configurations of minimal prices -/

noncomputable section
open scoped Classical
namespace OM.Formats

open NNN32 NNN32.FourNetwork NNN34 NNN30.Net NNN30.Geom AsymptoticSpectrumDuality Semicontinuity
open Filter Topology

theorem real_bill {V : Type} [Fintype V] {φ : AsymptoticSpectrum fourPreorder} {τ : Fin 4 → V}
    {d : V → V → ℝ} (hd : Minimal φ τ d) (t : Fin 4 → V)
    (sep : ∀ i j, i ≠ j → 0 < d (t i) (t j)) (l r o h k : V)
    {a b c u v κ : ℝ} (hu : 0 < u) (hv : 0 < v) (hua : u ≤ a) (hvb : v ≤ b) (hc : 0 ≤ c)
    (hβ : 0 ≤ formatBeta a b c) (hκ : 0 ≤ κ) (hdisk : 2*(u^2+v^2) < c^2+κ^2) :
    bill d t u v (formatBeta a b c) κ l r o h k := by
  let A (x : ℝ) (j : ℕ) := ⌊x*(j:ℝ)⌋₊
  let rate (x : ℝ) (j : ℕ) := (A x j:ℝ)/j
  have lim (x : ℝ) (hx : 0 ≤ x) : Tendsto (rate x) atTop (𝓝 x) :=
    (tendsto_nat_floor_mul_div_atTop hx).comp tendsto_natCast_atTop_atTop
  have closed : IsClosed {z : ℝ × ℝ | bill d t z.1 z.2 (formatBeta a b c) κ l r o h k} := by
    unfold bill diagonalCost rowCost colCost externalCost
    apply isClosed_le <;> fun_prop
  change (u,v) ∈ {z : ℝ × ℝ | bill d t z.1 z.2 (formatBeta a b c) κ l r o h k}
  apply closed.mem_of_tendsto ((lim u hu.le).prodMk_nhds (lim v hv.le))
  filter_upwards [eventually_ge_atTop 1,(tendsto_nat_floor_mul_atTop u hu).eventually_ge_atTop 1,
    (tendsto_nat_floor_mul_atTop v hv).eventually_ge_atTop 1] with j hj hA hB
  have hjR : 0 < (j:ℝ) := by exact_mod_cast hj
  have under (x : ℝ) (hx : 0 ≤ x) : rate x j ≤ x :=
    (div_le_iff₀ hjR).mpr (Nat.floor_le (mul_nonneg hx hjR.le))
  apply rational_bill hd t sep l r o h k (hu.le.trans hua) (hv.le.trans hvb) hc hβ hA hB hj
    ((under _ hu.le).trans hua) ((under _ hv.le).trans hvb) hκ
  exact lt_of_le_of_lt (by
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    exact add_le_add (pow_le_pow_left₀ (by positivity) (under u hu.le) 2)
      (pow_le_pow_left₀ (by positivity) (under v hv.le) 2)) hdisk

theorem exists_nondegenerate (hg : P2M.R113.gamma = Real.sqrt 2) :
    ∃ φ : AsymptoticSpectrum fourPreorder, ¬ degenerateSectors (space φ) := by
  by_contra! degen
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


/-- Finite complex-plane distances are simultaneous limits of rescaled finite
minimal prices in the high branch. -/
theorem approximate_prices (hg : P2M.R113.gamma = Real.sqrt 2) {ι : Type} [Fintype ι]
    (v : ι → ℂ) (ε : ℝ) (hε : 0 < ε) :
    ∃ (φ : AsymptoticSpectrum fourPreorder) (k : ℕ) (s : ℝ), 0 < s ∧ ∃ x : ι → Lv k,
      ∀ i j, |s*(level φ k).val (x i) (x j) - dist (v i) (v j)| < ε := by
  obtain ⟨φ,hφ⟩ := exists_nondegenerate hg
  unfold degenerateSectors at hφ
  push Not at hφ
  obtain ⟨o,p,q,hp,hd⟩ := hφ
  obtain ⟨s,hs,x,hx⟩ := approximate_plane (space φ) o p q hp hd (fun i => ((v i).re,(v i).im)) hε
  obtain ⟨k,y,hy⟩ := common_price_level (prices φ) x
  refine ⟨φ,k,s,hs,y,fun i j => ?_⟩
  change |s*(prices φ).d k (y i) (y j) - _| < ε
  rw [hy]
  have e (z w : ℂ) : planeLength (z.re,z.im) (w.re,w.im) = dist z w := by
    unfold planeLength
    rw [dist_comm,dist_eq_norm,← Real.sqrt_sq (norm_nonneg (w-z)),Complex.sq_norm,Complex.normSq_apply]
    simp [sq]
  exact (e (v i) (v j)) ▸ hx i j

private abbrev Sites := Fin 4 ⊕ Fin 5
private abbrev corner (i : Fin 4) : Sites := .inl i
private abbrev aux (i : Fin 5) : Sites := .inr i

theorem plane_bill (hg : P2M.R113.gamma = Real.sqrt 2) (t : Fin 4 → ℂ)
    (sep : Function.Injective t) (l r o h k : ℂ) {a b c u v κ : ℝ}
    (hu : 0 < u) (hv : 0 < v) (hua : u ≤ a) (hvb : v ≤ b) (hc : 0 ≤ c)
    (hβ : 0 ≤ formatBeta a b c) (hκ : 0 ≤ κ) (hdisk : 2*(u^2+v^2) < c^2+κ^2) :
    bill dist t u v (formatBeta a b c) κ l r o h k := by
  let vtx := Sum.elim t (![l,r,o,h,k] : Fin 5 → ℂ)
  let test (d : Sites → Sites → ℝ) := bill d corner u v (formatBeta a b c) κ (aux 0) (aux 1) (aux 2) (aux 3) (aux 4)
  let ε (n : ℕ) := 1/((n:ℝ)+1)
  choose φ lev s hs x hx using fun n => approximate_prices hg vtx (ε n) (by dsimp [ε]; positivity)
  let d (n : ℕ) (i j : Sites) := s n*(level (φ n) (lev n)).val (x n i) (x n j)
  let D (i j : Sites) := dist (vtx i) (vtx j)
  have herr : Tendsto ε atTop (𝓝 0) := by
    simpa only [ε,one_div,Function.comp_def,Nat.cast_add,Nat.cast_one] using!
      (tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop (R:=ℝ))).comp (tendsto_add_atTop_nat 1)
  have lim (i j : Sites) : Tendsto (fun n => d n i j) atTop (𝓝 (D i j)) := by
    apply Metric.tendsto_nhds.mpr
    intro δ hδ
    filter_upwards [herr.eventually (Iio_mem_nhds hδ)] with n hh
    exact (hx n i j).trans hh
  have ev : ∀ᶠ n in atTop, ∀ i j : Fin 4, i ≠ j → 0 < d n (corner i) (corner j) := by
    apply eventually_all.mpr; intro i
    apply eventually_all.mpr; intro j
    by_cases e : i = j
    · exact Eventually.of_forall fun _ hn => (hn e).elim
    have pos : 0 < D (corner i) (corner j) := dist_pos.mpr (sep.ne e)
    exact ((lim _ _).eventually (Ioi_mem_nhds pos)).mono fun _ h _ => h
  have closed : IsClosed {d | test d} := by
    unfold test bill diagonalCost rowCost colCost externalCost perimeter3
    apply isClosed_le <;> fun_prop
  change test D
  apply closed.mem_of_tendsto (tendsto_pi_nhds.mpr fun i => tendsto_pi_nhds.mpr (lim i))
  filter_upwards [ev] with n hn
  have H := real_bill (level (φ n) (lev n)).property (fun i => x n (corner i))
    (fun i j hij => pos_of_mul_pos_right (hn i j hij) (hs n).le)
    (x n (aux 0)) (x n (aux 1)) (x n (aux 2)) (x n (aux 3)) (x n (aux 4)) hu hv hua hvb hc hβ hκ hdisk
  have scaled := mul_le_mul_of_nonneg_left H (hs n).le
  change test (d n)
  unfold test bill diagonalCost rowCost colCost externalCost perimeter3 at *
  rw [mul_max_of_nonneg _ _ (hs n).le] at scaled
  dsimp [d,corner,aux] at scaled ⊢
  convert scaled using 1 <;> ring_nf

end OM.Formats
