import Lib.OM.NNN20.Hyp

/-! # Linear gates on vertex cones, and open query domains

* `IsLin`: a linear functional on formats. A strict linear gate that holds at every (strictly
  positive) hull vertex holds at every nonzero point of the vertex cone (`IsLin.pos_of_cone`);
  a linear format map sending every vertex into a cone sends the whole vertex cone there
  (`inCone_of_lin`).
* `isOpen_segIn`: the formats whose whole query segment lies in an open set form an open set
  (compactness of the segment). This is how strict gates and open parent domains give each
  catalytic node an open validity cone. -/

noncomputable section
open scoped BigOperators Topology
open Finset Filter

namespace OM.NNN20

/-- a linear functional on formats -/
def IsLin (L : (Fin 3 → ℝ) → ℝ) : Prop :=
  ∃ a : Fin 3 → ℝ, ∀ x, L x = a 0 * x 0 + a 1 * x 1 + a 2 * x 2

namespace IsLin

lemma coord (u : Fin 3) : IsLin (fun x => x u) :=
  ⟨fun j => if j = u then 1 else 0, fun x => by fin_cases u <;> simp⟩

lemma const_mul {L : (Fin 3 → ℝ) → ℝ} (h : IsLin L) (r : ℝ) : IsLin (fun x => r * L x) := by
  obtain ⟨a, ha⟩ := h
  exact ⟨fun j => r * a j, fun x => by beta_reduce; rw [ha]; ring⟩

lemma mul_const {L : (Fin 3 → ℝ) → ℝ} (h : IsLin L) (r : ℝ) : IsLin (fun x => L x * r) := by
  obtain ⟨a, ha⟩ := h
  exact ⟨fun j => a j * r, fun x => by beta_reduce; rw [ha]; ring⟩

lemma add {L M : (Fin 3 → ℝ) → ℝ} (hL : IsLin L) (hM : IsLin M) : IsLin (fun x => L x + M x) := by
  obtain ⟨a, ha⟩ := hL
  obtain ⟨b, hb⟩ := hM
  exact ⟨fun j => a j + b j, fun x => by beta_reduce; rw [ha, hb]; ring⟩

lemma sub {L M : (Fin 3 → ℝ) → ℝ} (hL : IsLin L) (hM : IsLin M) : IsLin (fun x => L x - M x) := by
  obtain ⟨a, ha⟩ := hL
  obtain ⟨b, hb⟩ := hM
  exact ⟨fun j => a j - b j, fun x => by beta_reduce; rw [ha, hb]; ring⟩

lemma neg {L : (Fin 3 → ℝ) → ℝ} (hL : IsLin L) : IsLin (fun x => -L x) := by
  obtain ⟨a, ha⟩ := hL
  exact ⟨fun j => -a j, fun x => by beta_reduce; rw [ha]; ring⟩

lemma continuous {L : (Fin 3 → ℝ) → ℝ} (h : IsLin L) : Continuous L := by
  obtain ⟨a, ha⟩ := h
  have : L = fun x => a 0 * x 0 + a 1 * x 1 + a 2 * x 2 := funext ha
  rw [this]
  fun_prop

lemma map_smul {L : (Fin 3 → ℝ) → ℝ} (h : IsLin L) (r : ℝ) (x : Fin 3 → ℝ) :
    L (fun u => r * x u) = r * L x := by
  obtain ⟨a, ha⟩ := h
  rw [ha, ha]; ring

/-- linearity along a nonnegative combination of vertices -/
lemma map_sum {L : (Fin 3 → ℝ) → ℝ} (h : IsLin L) (N : ℕ) (μ : ℕ → ℝ) (Z : ℕ → Fin 3 → ℝ)
    (x : Fin 3 → ℝ) (hx : ∀ u, x u = ∑ i ∈ range N, μ i * Z i u) :
    L x = ∑ i ∈ range N, μ i * L (Z i) := by
  obtain ⟨a, ha⟩ := h
  rw [ha, hx 0, hx 1, hx 2]
  simp only [ha, mul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun i _ => by ring

end IsLin

lemma isLin_rdot (a : Fin 3 → ℚ) : IsLin (rdot a) :=
  ⟨fun j => (a j : ℝ), fun x => rfl⟩

lemma isLin_plane (c : Fin 3 → ℝ) : IsLin (NNN13.plane c) :=
  ⟨c, fun x => rfl⟩

/-- the real point of a hull vertex -/
def vR (pt : ℤ × ℤ) : Fin 3 → ℝ := fun u => ((vecV pt u : ℚ) : ℝ)

lemma getD_mem {V : List (ℤ × ℤ)} {i : ℕ} (hi : i < V.length) : V.getD i (0, 0) ∈ V := by
  rw [List.getD_eq_getElem _ _ hi]
  exact List.getElem_mem hi

/-- **A strict linear gate at every vertex holds on the punctured vertex cone.** -/
lemma IsLin.pos_of_cone {L : (Fin 3 → ℝ) → ℝ} (hL : IsLin L) {V : List (ℤ × ℤ)}
    (hV : ∀ pt ∈ V, 0 < L (vR pt)) {z : Fin 3 → ℝ} (hz : InCone V z) (hz0 : z ≠ 0) : 0 < L z := by
  obtain ⟨μ, hμ, hzμ⟩ := hz
  have hsum := hL.map_sum V.length μ (fun i => vR (V.getD i (0, 0))) z hzμ
  have hterm : ∀ i ∈ range V.length, 0 ≤ μ i * L (vR (V.getD i (0, 0))) := by
    intro i hi
    exact mul_nonneg (hμ i) (hV _ (getD_mem (mem_range.1 hi))).le
  rcases (sum_nonneg hterm).lt_or_eq with hpos | hzero
  · rw [hsum]; exact hpos
  · exfalso
    apply hz0
    have hall := (sum_eq_zero_iff_of_nonneg hterm).1 hzero.symm
    have hμ0 : ∀ i ∈ range V.length, μ i = 0 := by
      intro i hi
      have h1 := hall i hi
      have h2 := hV _ (getD_mem (mem_range.1 hi))
      rcases mul_eq_zero.1 h1 with h | h
      · exact h
      · exact absurd h h2.ne'
    funext u
    rw [hzμ u]
    simp only [Pi.zero_apply]
    exact sum_eq_zero fun i hi => by rw [hμ0 i hi, zero_mul]

/-- nonnegative combinations stay in a cone -/
lemma inCone_sum {W : List (ℤ × ℤ)} (N : ℕ) (μ : ℕ → ℝ) (hμ : ∀ i, 0 ≤ μ i) (Z : ℕ → Fin 3 → ℝ)
    (hZ : ∀ i < N, InCone W (Z i)) : InCone W (fun u => ∑ i ∈ range N, μ i * Z i u) := by
  induction N with
  | zero =>
    refine ⟨fun _ => 0, fun _ => le_rfl, fun u => ?_⟩
    simp
  | succ N ih =>
    have h1 := ih (fun i hi => hZ i (by omega))
    have h2 := (hZ N (by omega)).smul (hμ N)
    refine (h1.add h2).congr fun u => ?_
    rw [sum_range_succ]

/-- **A linear format map sending every vertex into a cone sends the vertex cone there.** -/
lemma inCone_of_lin {E : (Fin 3 → ℝ) → (Fin 3 → ℝ)} (hE : ∀ u, IsLin (fun x => E x u))
    {V W : List (ℤ × ℤ)} (hV : ∀ pt ∈ V, InCone W (E (vR pt))) {z : Fin 3 → ℝ} (hz : InCone V z) :
    InCone W (E z) := by
  obtain ⟨μ, hμ, hzμ⟩ := hz
  have h := inCone_sum (W := W) V.length μ hμ (fun i => E (vR (V.getD i (0, 0))))
    (fun i hi => hV _ (getD_mem hi))
  refine h.congr fun u => ?_
  rw [(hE u).map_sum V.length μ (fun i => vR (V.getD i (0, 0))) z hzμ]

lemma vecV_pos {pt : ℤ × ℤ} (h1 : 0 < pt.1) (h2 : 0 < pt.2) (h3 : 0 < GRID - pt.1 - pt.2)
    (u : Fin 3) : 0 < vecV pt u := by
  have hG : (0 : ℚ) < (GRID : ℚ) := by norm_num [GRID]
  have e1 : (0 : ℚ) < ((GRID - pt.1 - pt.2 : ℤ) : ℚ) := by exact_mod_cast h3
  have e2 : (0 : ℚ) < (pt.1 : ℚ) := by exact_mod_cast h1
  have e3 : (0 : ℚ) < (pt.2 : ℚ) := by exact_mod_cast h2
  fin_cases u
  · exact div_pos e1 hG
  · exact div_pos e2 hG
  · exact div_pos e3 hG

/-- the vertex cone of strictly positive vertices consists of positive formats (except `0`) -/
lemma pos_of_cone {V : List (ℤ × ℤ)} (hV : ∀ pt ∈ V, 0 < pt.1 ∧ 0 < pt.2 ∧ 0 < GRID - pt.1 - pt.2)
    {z : Fin 3 → ℝ} (hz : InCone V z) (hz0 : z ≠ 0) (u : Fin 3) : 0 < z u := by
  have hpos : ∀ pt ∈ V, 0 < vR pt u := by
    intro pt hpt
    obtain ⟨h1, h2, h3⟩ := hV pt hpt
    exact Rat.cast_pos.2 (vecV_pos h1 h2 h3 u)
  exact (IsLin.coord u).pos_of_cone hpos hz hz0

/-! ## Open query domains -/

/-- **The formats whose whole query segment lies in an open set form an open set.** -/
lemma isOpen_segIn {K : Set (Fin 3 → ℝ)} (hK : IsOpen K) {Y : (Fin 3 → ℝ) → (Fin 3 → ℝ)}
    {d : Fin 3 → ℝ} {lo hi : (Fin 3 → ℝ) → ℝ} (hY : Continuous Y) (hlo : Continuous lo)
    (hhi : Continuous hi) : IsOpen {x | SegIn K (Y x) d (lo x) (hi x)} := by
  rw [isOpen_iff_mem_nhds]
  intro x0 hx0
  set W : Set ((Fin 3 → ℝ) × ℝ) := {p | (fun u => Y p.1 u - p.2 * d u) ∈ K} with hWdef
  have hW : IsOpen W := hK.preimage (by fun_prop)
  rcases lt_or_ge (hi x0) (lo x0) with hlt | hle
  · -- empty segment near `x0`
    have hev : ∀ᶠ x in 𝓝 x0, hi x < lo x :=
      (hhi.continuousAt.eventually_lt hlo.continuousAt hlt)
    filter_upwards [hev] with x hx ξ h1 h2
    exact absurd (h1.trans h2) (not_le.2 hx)
  · -- the open slice at `x0` contains a closed enlargement of the segment
    set O : Set ℝ := {ξ | (x0, ξ) ∈ W} with hOdef
    have hO : IsOpen O := hW.preimage (by fun_prop)
    have hlo0 : lo x0 ∈ O := hx0 (lo x0) le_rfl hle
    have hhi0 : hi x0 ∈ O := hx0 (hi x0) hle le_rfl
    obtain ⟨δ1, hδ1, hb1⟩ := Metric.isOpen_iff.1 hO _ hlo0
    obtain ⟨δ2, hδ2, hb2⟩ := Metric.isOpen_iff.1 hO _ hhi0
    set δ := min δ1 δ2 / 2 with hδdef
    have hδ : 0 < δ := by positivity
    have hsub : Set.Icc (lo x0 - δ) (hi x0 + δ) ⊆ O := by
      intro ξ hξ
      obtain ⟨h1, h2⟩ := hξ
      rcases lt_or_ge ξ (lo x0) with ha | ha
      · apply hb1
        rw [Metric.mem_ball, Real.dist_eq, abs_lt]
        constructor <;> nlinarith [min_le_left δ1 δ2]
      · rcases lt_or_ge (hi x0) ξ with hb | hb
        · apply hb2
          rw [Metric.mem_ball, Real.dist_eq, abs_lt]
          constructor <;> nlinarith [min_le_right δ1 δ2]
        · exact hx0 ξ ha hb
    have hcpt : IsCompact (Set.Icc (lo x0 - δ) (hi x0 + δ)) := isCompact_Icc
    have hev : ∀ᶠ x in 𝓝 x0, ∀ ξ ∈ Set.Icc (lo x0 - δ) (hi x0 + δ), (x, ξ) ∈ W := by
      apply hcpt.eventually_forall_of_forall_eventually
      intro ξ hξ
      exact hW.mem_nhds (hsub hξ)
    have hev1 : ∀ᶠ x in 𝓝 x0, lo x0 - δ < lo x :=
      hlo.continuousAt.eventually (lt_mem_nhds (by linarith))
    have hev2 : ∀ᶠ x in 𝓝 x0, hi x < hi x0 + δ :=
      hhi.continuousAt.eventually (gt_mem_nhds (by linarith))
    filter_upwards [hev, hev1, hev2] with x hx h1 h2 ξ hξ1 hξ2
    exact hx ξ ⟨by linarith, by linarith⟩

end OM.NNN20

namespace OM.NNN20

open scoped Topology
open Filter

/-- **A uniform neighbourhood of a query segment inside an open set**: if the whole segment
`{Y - ξ d : lo ≤ ξ ≤ hi}` lies in the open set `K`, then for some `ε > 0` every point within `ε`
(coordinatewise) of `Y - ξ d`, `lo - ε ≤ ξ ≤ hi + ε`, lies in `K`. The catalytic step uses it for
the rounding and label overheads of the packed formats. -/
lemma exists_tube {K : Set (Fin 3 → ℝ)} (hK : IsOpen K) {Y d : Fin 3 → ℝ} {lo hi : ℝ}
    (hlh : lo ≤ hi) (hseg : SegIn K Y d lo hi) :
    ∃ ε > 0, ∀ ξ : ℝ, lo - ε ≤ ξ → ξ ≤ hi + ε → ∀ y : Fin 3 → ℝ,
      (∀ u, |y u - (Y u - ξ * d u)| < ε) → y ∈ K := by
  -- the segment as the image of a compact interval
  set g : ℝ → (Fin 3 → ℝ) := fun ξ => fun u => Y u - ξ * d u with hg
  have hgc : Continuous g := by fun_prop
  have hcpt : IsCompact (g '' Set.Icc lo hi) := isCompact_Icc.image hgc
  have hsub : g '' Set.Icc lo hi ⊆ K := by
    rintro _ ⟨ξ, ⟨h1, h2⟩, rfl⟩
    exact hseg ξ h1 h2
  obtain ⟨δ, hδ, hthick⟩ := hcpt.exists_thickening_subset_open hK hsub
  -- choose `ε` so that `ε` in ξ and `ε` in y move the point by less than `δ`
  set Dn : ℝ := |d 0| + |d 1| + |d 2| + 1 with hDn
  have hDn1 : 1 ≤ Dn := by
    have := abs_nonneg (d 0); have := abs_nonneg (d 1); have := abs_nonneg (d 2); linarith
  refine ⟨δ / (2 * Dn), by positivity, fun ξ h1 h2 y hy => hthick ?_⟩
  -- the nearest parameter in `[lo, hi]`
  set ξ' := max lo (min ξ hi) with hξ'
  have hξ'm : ξ' ∈ Set.Icc lo hi := ⟨le_max_left _ _, max_le hlh (min_le_right _ _)⟩
  have hε0 : 0 ≤ δ / (2 * Dn) := by positivity
  have hdist : |ξ - ξ'| ≤ δ / (2 * Dn) := by
    rw [abs_le]
    rcases le_or_gt ξ hi with hh | hh
    · rw [hξ', min_eq_left hh]
      rcases le_or_gt lo ξ with hl | hl
      · rw [max_eq_right hl]; constructor <;> linarith
      · rw [max_eq_left hl.le]; constructor <;> linarith
    · rw [hξ', min_eq_right hh.le, max_eq_right hlh]
      constructor <;> linarith
  rw [Metric.mem_thickening_iff]
  refine ⟨g ξ', ⟨ξ', hξ'm, rfl⟩, ?_⟩
  -- sup distance on `Fin 3 → ℝ`
  have hcoord : ∀ u, |y u - g ξ' u| < δ := by
    intro u
    have h1 := hy u
    have h2 : |(Y u - ξ * d u) - g ξ' u| ≤ δ / (2 * Dn) * |d u| := by
      simp only [hg]
      rw [show Y u - ξ * d u - (Y u - ξ' * d u) = -((ξ - ξ') * d u) by ring, abs_neg, abs_mul]
      exact mul_le_mul_of_nonneg_right hdist (abs_nonneg _)
    have hdu : |d u| ≤ Dn := by
      have hs : |d u| ≤ ∑ i, |d i| :=
        Finset.single_le_sum (fun i _ => abs_nonneg (d i)) (Finset.mem_univ u)
      rw [Fin.sum_univ_three] at hs
      linarith
    have h3 : δ / (2 * Dn) * |d u| ≤ δ / 2 := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [abs_nonneg (d u)]
    have h4 : δ / (2 * Dn) ≤ δ / 2 := by
      apply div_le_div_of_nonneg_left hδ.le (by norm_num) (by linarith)
    calc |y u - g ξ' u| = |(y u - (Y u - ξ * d u)) + ((Y u - ξ * d u) - g ξ' u)| := by ring_nf
      _ ≤ |y u - (Y u - ξ * d u)| + |(Y u - ξ * d u) - g ξ' u| := abs_add_le _ _
      _ < δ := by linarith
  rw [dist_pi_lt_iff hδ]
  intro u
  rw [Real.dist_eq]
  exact hcoord u

end OM.NNN20
