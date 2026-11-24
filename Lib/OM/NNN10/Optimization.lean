import Lib.OM.NNN10.Scalar

/-! Jensen's inequality chooses the retained bond at each asymmetric point. -/
noncomputable section
open scoped BigOperators
namespace OM.NNN10
set_option maxHeartbeats 1000000

lemma jensen_three {f : ℝ → ℝ} (hf : ConvexOn ℝ (Set.Icc (1 / 4 : ℝ) 1) f)
    (t : Fin 3 → ℝ) (ht : ∀ i, t i ∈ Set.Icc (1 / 4 : ℝ) 1)
    (hs : ∑ i, t i = 9 / 4) : 3 * f (3 / 4) ≤ ∑ i, f (t i) := by
  have h := hf.map_sum_le (t := Finset.univ) (w := fun _ : Fin 3 => (1 / 3 : ℝ))
    (p := t) (by intro i _; norm_num) (by norm_num) (fun i _ => ht i)
  simp only [smul_eq_mul, ← Finset.mul_sum, hs] at h
  norm_num at h
  linarith

def chosenRate (h i : Fin 3) (t : ℝ) : ℝ := rate (if i = h then 2 else 3) t

theorem exists_retained_gain (t : Fin 3 → ℝ)
    (ht : ∀ i, t i ∈ Set.Icc (1 / 4 : ℝ) 1) (hs : ∑ i, t i = 9 / 4) :
    ∃ h : Fin 3, 9 / 2 - 3 * beta ≤ ∑ i, t i * chosenRate h i (t i) := by
  have hF := jensen_three (weightedRate_convex (k := 3) (by norm_num)) t ht hs
  have hG := jensen_three (weightedRate_convex (k := 2) (by norm_num)) t ht hs
  simp only [weightedRate, rate_balance_three, rate_balance_two, Fin.sum_univ_three] at hF hG
  by_contra! hn
  have h0 := hn 0
  have h1 := hn 1
  have h2 := hn 2
  simp only [Fin.sum_univ_three, chosenRate,
    show (0 : Fin 3) = 0 from rfl, show (1 : Fin 3) = 1 from rfl,
    show (2 : Fin 3) = 2 from rfl,
    show ¬(0 : Fin 3) = 1 by decide +kernel,
    show ¬(0 : Fin 3) = 2 by decide +kernel,
    show ¬(1 : Fin 3) = 0 by decide +kernel,
    show ¬(1 : Fin 3) = 2 by decide +kernel,
    show ¬(2 : Fin 3) = 0 by decide +kernel,
    show ¬(2 : Fin 3) = 1 by decide +kernel, if_true, if_false] at h0 h1 h2
  rw [beta_eq] at h0 h1 h2
  linarith

theorem exists_enlargement (t : Fin 3 → ℝ) (ht : ∀ i, t i ∈ Set.Icc (0 : ℝ) 1)
    (hs : ∑ i, t i ≤ 9 / 4) :
    ∃ u : Fin 3 → ℝ, (∀ i, t i ≤ u i) ∧
      (∀ i, u i ∈ Set.Icc (1 / 4 : ℝ) 1) ∧ ∑ i, u i = 9 / 4 := by
  let s := ∑ i, t i
  let q := (9 / 4 - s) / (3 - s)
  have hs' : s ≤ 9 / 4 := hs
  have hd : 0 < 3 - s := by linarith
  have hq0 : 0 ≤ q := div_nonneg (by linarith) hd.le
  have hq1 : q ≤ 1 := (div_le_one hd).2 (by linarith)
  let u := fun i => t i + q * (1 - t i)
  have htu (i) : t i ≤ u i := by
    dsimp [u]
    nlinarith [mul_nonneg hq0 (sub_nonneg.mpr (ht i).2)]
  have hu1 (i) : u i ≤ 1 := by
    dsimp [u]
    nlinarith [mul_nonneg (sub_nonneg.mpr hq1) (sub_nonneg.mpr (ht i).2)]
  have hsum : ∑ i, u i = 9 / 4 := by
    have hqe : q * (3 - s) = 9 / 4 - s := div_mul_cancel₀ _ hd.ne'
    simp only [u, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib] 
    norm_num
    change s + q * (3 - s) = 9 / 4
    linarith
  refine ⟨u, htu, ?_, hsum⟩
  intro i
  refine ⟨?_, hu1 i⟩
  have h0 := hu1 0
  have h1 := hu1 1
  have h2 := hu1 2
  simp only [Fin.sum_univ_three] at hsum
  fin_cases i
  · change 1 / 4 ≤ u 0
    linarith
  · change 1 / 4 ≤ u 1
    linarith
  · change 1 / 4 ≤ u 2
    linarith

lemma positive_rate_eq {k t : ℝ} (h : 0 < rate k t) : rate k t = rawRate k t := by
  apply max_eq_right
  by_contra! hn
  have he : rate k t = 0 := max_eq_left hn.le
  linarith

end OM.NNN10
