import Lib.OM.NNN32.Sectors
import Lib.OM.NNN30.Net.Tower

/-! # Finite configurations in a nondegenerate two-ray sector -/

namespace OM.NNN34

open Filter Topology OM.NNN30.Geom ConePt OM.NNN32

private theorem place_in_square {ι : Type*} [Fintype ι] (v : ι → ℝ × ℝ) :
    ∃ c : ℝ, 0 < c ∧ ∃ w : ι → ℝ × ℝ, (∀ i, InSquare (w i)) ∧
      ∀ i j, planeLength (w i) (w j) = c * planeLength (v i) (v j) := by
  classical
  let M := 1 + ∑ i, (|(v i).1| + |(v i).2|)
  have hM : 0 < M := by dsimp [M]; positivity
  let c := (2 * M)⁻¹
  have hc : 0 < c := by dsimp [c]; positivity
  have hscale : c * (2 * M) = 1 := inv_mul_cancel₀ (by positivity)
  let w (i : ι) := (c * ((v i).1 + M), c * ((v i).2 + M))
  refine ⟨c, hc, w, ?_, ?_⟩
  · intro i
    have hsum := Finset.single_le_sum (f := fun j => |(v j).1| + |(v j).2|)
      (fun j _ => add_nonneg (abs_nonneg _) (abs_nonneg _)) (Finset.mem_univ i)
    have bound {x : ℝ} (hx : |x| ≤ M) : 0 ≤ c * (x + M) ∧ c * (x + M) ≤ 1 := by
      obtain ⟨hlo, hhi⟩ := abs_le.mp hx
      exact ⟨mul_nonneg hc.le (by linarith), (mul_le_mul_of_nonneg_left
        (show x + M ≤ 2 * M by linarith) hc.le).trans_eq hscale⟩
    have h₁ := bound (x := (v i).1) (by dsimp [M]; linarith only [hsum, abs_nonneg (v i).2])
    have h₂ := bound (x := (v i).2) (by dsimp [M]; linarith only [hsum, abs_nonneg (v i).1])
    exact ⟨⟨h₁.1, h₂.1⟩, h₁.2, h₂.2⟩
  · intro i j
    unfold planeLength
    dsimp only [w]
    rw [show (c * ((v j).1 + M) - c * ((v i).1 + M)) ^ 2 +
        (c * ((v j).2 + M) - c * ((v i).2 + M)) ^ 2 =
        c ^ 2 * (((v j).1 - (v i).1) ^ 2 + ((v j).2 - (v i).2) ^ 2) by ring,
      Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc.le]

/-- A positive two-ray Gram determinant lets the original midpoint space
approximate all pair distances of any finite planar configuration after
one common rescaling. -/
theorem approximate_plane {X : Type*} (S : MidSpace X) (o p q : X) (hp : 0 < S.d o p)
    (hdet : 0 < 4 * (S.d o p) ^ 2 * (S.d o q) ^ 2 -
      ((S.d o p) ^ 2 + (S.d o q) ^ 2 - (delta S o p q) ^ 2) ^ 2)
    {ι : Type*} [Fintype ι] (v : ι → ℝ × ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ scale : ℝ, 0 < scale ∧ ∃ x : ι → X, ∀ i j,
      |scale * S.d (x i) (x j) - planeLength (v i) (v j)| < ε := by
  obtain ⟨c, hc, w, hw, hlen⟩ := place_in_square v
  obtain ⟨r, f, hr, _, _, hdist⟩ := euclidean_square (qhyp S o p q) hp
    (Nf_e1 S o p q) (Nf_e2 S o p q) (by rw [Nf_e21]) hdet
  let x (i : ι) := J S o p q (f (w i))
  have hdist' (i j : ι) : ρ (x i) (x j) = (r * c) * planeLength (v i) (v j) := by
    change Nf S o p q (f (w i)) (f (w j)) = _
    rw [hdist _ _ (hw i) (hw j), hlen, mul_assoc]
  have hrc := mul_pos hr hc
  have hlim (i j : ι) : Tendsto (fun n => sd (x i) (x j) n / (r * c))
      (U : Filter ℕ) (𝓝 (planeLength (v i) (v j))) := by
    have h := (tendsto_ρ (x i) (x j)).div_const (r * c)
    rwa [hdist', mul_div_cancel_left₀ _ hrc.ne'] at h
  have hall : ∀ᶠ n in (U : Filter ℕ), ∀ i j,
      |sd (x i) (x j) n / (r * c) - planeLength (v i) (v j)| < ε := by
    apply Filter.eventually_all.mpr
    intro i
    apply Filter.eventually_all.mpr
    intro j
    simpa only [Real.dist_eq] using Metric.tendsto_nhds.mp (hlim i j) ε hε
  obtain ⟨n, hn⟩ := hall.exists
  refine ⟨(2 : ℝ) ^ n / (r * c), div_pos (by positivity) hrc, fun i => (x i).seq n, ?_⟩
  intro i j
  simpa only [sd, div_mul_eq_mul_div] using hn i j

open OM.NNN30.Net

/-- A finite family of tower labels has all its union distances realized
exactly at one finite level. -/
theorem common_price_level (P : PriceTower) {ι : Type*} [Fintype ι] (x : ι → Tm) :
    ∃ k : ℕ, ∃ y : ι → Lv k, ∀ i j, P.d k (y i) (y j) = P.dX (x i) (x j) := by
  classical
  let k := Finset.univ.sup fun i => (x i).depth
  have hk (i : ι) : (x i).depth ≤ k := Finset.le_sup (f := fun j => (x j).depth) (Finset.mem_univ i)
  exact ⟨k, fun i => ev k (x i), fun i j => P.dX_eq _ _ k (max_le (hk i) (hk j))⟩

end OM.NNN34

