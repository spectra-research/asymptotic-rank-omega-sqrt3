import Lib.OM.NNN30.Geom.Basic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Order.Filter.Ultrafilter.Basic

/-! # The cone at a point

For countably many sequences of points, successive extraction gives a diagonal subsequence
along which every rescaled distance converges. Here we use one non-principal
ultrafilter `U = hyperfilter ℕ`: every bounded real sequence has a limit along `U` (compactness of a
closed interval), and these limits are additive, monotone and commute with continuous maps.

For a midpoint space `S` and a point `o`, `ConePt S o` is the type of sequences `q` with
`2^n d(q n, o)` bounded; `ρ q q' = lim_U 2^n d(q n, q' n)` and `M q q' = (m (q n) (q' n))_n` make
it a midpoint space (`coneSpace`), since all axioms are pointwise inequalities.  The cone has
real-fraction geodesic points `cgeo A B t` (dyadic points of `S` with fractions converging to `t`)
with exact distances and Busemann convexity (11). -/

noncomputable section

open Filter Topology

namespace OM.NNN30.Geom

/-- The non-principal ultrafilter used for every limit. -/
abbrev U : Ultrafilter ℕ := hyperfilter ℕ

lemma U_le_atTop : ((U : Ultrafilter ℕ) : Filter ℕ) ≤ atTop := by
  rw [← Nat.cofinite_eq_atTop]; exact hyperfilter_le_cofinite

lemma eventually_U {p : ℕ → Prop} (N : ℕ) (h : ∀ n, N ≤ n → p n) : ∀ᶠ n in (U : Filter ℕ), p n :=
  U_le_atTop (eventually_atTop.2 ⟨N, h⟩)

/-- Ultralimit of a real sequence (a junk value if the sequence is unbounded). -/
def ulim (f : ℕ → ℝ) : ℝ := limUnder (U : Filter ℕ) f

lemma tendsto_ulim {f : ℕ → ℝ} {C : ℝ} (hf : ∀ n, |f n| ≤ C) :
    Tendsto f (U : Filter ℕ) (𝓝 (ulim f)) := by
  apply tendsto_nhds_limUnder
  obtain ⟨x, -, hx⟩ := (isCompact_Icc (a := -C) (b := C)).ultrafilter_le_nhds
    (Ultrafilter.map f U) (by
      rw [Ultrafilter.coe_map, le_principal_iff, Filter.mem_map]
      exact Filter.univ_mem' (fun n => abs_le.1 (hf n)))
  exact ⟨x, hx⟩

variable {X : Type*}

/-- Points of the cone at `o`: sequences `q` with `2^n d(q n, o)` bounded. -/
structure ConePt (S : MidSpace X) (o : X) where
  seq : ℕ → X
  bdd : ∃ C, ∀ n, (2 : ℝ) ^ n * S.d (seq n) o ≤ C

namespace ConePt

variable {S : MidSpace X} {o : X}

/-- The rescaled distance sequence. -/
def sd (P Q : ConePt S o) (n : ℕ) : ℝ := (2 : ℝ) ^ n * S.d (P.seq n) (Q.seq n)

lemma sd_nonneg (P Q : ConePt S o) (n : ℕ) : 0 ≤ sd P Q n :=
  mul_nonneg (by positivity) (S.d_nonneg _ _)

lemma sd_le (P Q : ConePt S o) (n : ℕ) :
    sd P Q n ≤ (2 : ℝ) ^ n * S.d (P.seq n) o + (2 : ℝ) ^ n * S.d (Q.seq n) o := by
  have t := S.d_tri (P.seq n) o (Q.seq n)
  rw [S.d_comm o] at t
  rw [sd, ← mul_add]
  exact mul_le_mul_of_nonneg_left t (by positivity)

lemma sd_bdd (P Q : ConePt S o) : ∃ C, ∀ n, |sd P Q n| ≤ C := by
  obtain ⟨C1, h1⟩ := P.bdd
  obtain ⟨C2, h2⟩ := Q.bdd
  refine ⟨C1 + C2, fun n => ?_⟩
  rw [abs_of_nonneg (sd_nonneg P Q n)]
  linarith [sd_le P Q n, h1 n, h2 n]

/-- The cone distance. -/
def ρ (P Q : ConePt S o) : ℝ := ulim (sd P Q)

lemma tendsto_ρ (P Q : ConePt S o) : Tendsto (sd P Q) (U : Filter ℕ) (𝓝 (ρ P Q)) :=
  let ⟨_, hC⟩ := sd_bdd P Q
  tendsto_ulim hC

lemma ρ_eq {P Q : ConePt S o} {x : ℝ} (h : Tendsto (sd P Q) (U : Filter ℕ) (𝓝 x)) : ρ P Q = x :=
  tendsto_nhds_unique (tendsto_ρ P Q) h

/-- The cone midpoint. -/
def M (P Q : ConePt S o) : ConePt S o where
  seq n := S.m (P.seq n) (Q.seq n)
  bdd := by
    obtain ⟨C1, h1⟩ := P.bdd
    obtain ⟨C2, h2⟩ := Q.bdd
    refine ⟨(C1 + C2) / 2, fun n => ?_⟩
    have t := S.d_tri (S.m (P.seq n) (Q.seq n)) (S.m o o) o
    rw [S.ax3 o, add_zero] at t
    have b := S.bus (P.seq n) (Q.seq n) o o
    have h2n : (0 : ℝ) ≤ 2 ^ n := by positivity
    have := mul_le_mul_of_nonneg_left (t.trans b) h2n
    have := h1 n
    have := h2 n
    nlinarith

end ConePt

open ConePt

/-- The cone at `o` is a midpoint space. -/
def coneSpace (S : MidSpace X) (o : X) : MidSpace (ConePt S o) where
  d := ρ
  m := M
  d_self P := ρ_eq (by
    refine tendsto_const_nhds.congr (fun n => ?_)
    simp [sd, S.d_self])
  d_comm P Q := by
    have : sd P Q = sd Q P := funext fun n => by simp [sd, S.d_comm]
    simp only [ρ, this]
  d_tri P Q R := le_of_tendsto_of_tendsto' (tendsto_ρ P R) ((tendsto_ρ P Q).add (tendsto_ρ Q R))
    (fun n => by
      simp only [sd]; rw [← mul_add]
      exact mul_le_mul_of_nonneg_left (S.d_tri _ _ _) (by positivity))
  ax1 A B C := le_of_tendsto_of_tendsto' (tendsto_ρ _ _) ((tendsto_ρ A C).div_const 2)
    (fun n => by
      simp only [sd, M]
      have := mul_le_mul_of_nonneg_left (S.ax1 (A.seq n) (B.seq n) (C.seq n))
        (by positivity : (0 : ℝ) ≤ 2 ^ n)
      linarith)
  ax2 A B E := le_of_tendsto_of_tendsto' (tendsto_ρ _ _) ((tendsto_ρ B E).div_const 2)
    (fun n => by
      simp only [sd, M]
      have := mul_le_mul_of_nonneg_left (S.ax2 (A.seq n) (B.seq n) (E.seq n))
        (by positivity : (0 : ℝ) ≤ 2 ^ n)
      linarith)
  ax3 A := ρ_eq (by
    refine tendsto_const_nhds.congr (fun n => ?_)
    simp [sd, M, S.ax3])
  quad A B C E := le_of_tendsto_of_tendsto'
    (((tendsto_ρ _ _).pow 2).add ((tendsto_ρ _ _).pow 2))
    ((((tendsto_ρ A C).pow 2).add ((tendsto_ρ B E).pow 2)).div_const 2)
    (fun n => by
      simp only [sd, M]
      have h := S.quad (A.seq n) (B.seq n) (C.seq n) (E.seq n)
      have h4 : (0 : ℝ) ≤ ((2 : ℝ) ^ n) ^ 2 := by positivity
      have := mul_le_mul_of_nonneg_left h h4
      nlinarith)

namespace ConePt

variable {S : MidSpace X} {o : X}

lemma coneSpace_d : (coneSpace S o).d = ρ := rfl
lemma coneSpace_m : (coneSpace S o).m = M := rfl

/-- The dyadic numerator approximating the fraction `t` at level `n`. -/
def frac (t : ℝ) (n : ℕ) : ℕ := min ⌊t * 2 ^ n⌋₊ (2 ^ n)

lemma frac_le (t : ℝ) (n : ℕ) : frac t n ≤ 2 ^ n := min_le_right _ _

lemma frac_eq {t : ℝ} (h1 : t ≤ 1) (n : ℕ) : frac t n = ⌊t * 2 ^ n⌋₊ := by
  apply min_eq_left
  apply Nat.floor_le_of_le
  push_cast
  have : (0 : ℝ) < 2 ^ n := by positivity
  nlinarith

lemma tendsto_floor_div {t : ℝ} (h0 : 0 ≤ t) :
    Tendsto (fun n : ℕ => (⌊t * 2 ^ n⌋₊ : ℝ) / 2 ^ n) atTop (𝓝 t) :=
  (tendsto_nat_floor_mul_div_atTop h0).comp (tendsto_pow_atTop_atTop_of_one_lt one_lt_two)

lemma tendsto_frac {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    Tendsto (fun n : ℕ => (frac t n : ℝ) / 2 ^ n) (U : Filter ℕ) (𝓝 t) := by
  refine ((tendsto_floor_div h0).mono_left U_le_atTop).congr (fun n => ?_)
  rw [frac_eq h1]

/-- Real-fraction geodesic points of the cone. -/
def cgeo (A B : ConePt S o) (t : ℝ) : ConePt S o where
  seq n := S.geo (A.seq n) (B.seq n) n (frac t n)
  bdd := by
    obtain ⟨C1, h1⟩ := A.bdd
    obtain ⟨C, hC⟩ := sd_bdd A B
    refine ⟨C + C1, fun n => ?_⟩
    have e := S.geo_left n (A.seq n) (B.seq n) (frac_le t n)
    have t1 := S.d_tri (S.geo (A.seq n) (B.seq n) n (frac t n)) (A.seq n) o
    rw [S.d_comm _ (A.seq n), e] at t1
    have hf0 : (0 : ℝ) ≤ (frac t n : ℝ) / 2 ^ n := by positivity
    have hf1 : (frac t n : ℝ) / 2 ^ n ≤ 1 := by
      rw [div_le_one (by positivity)]; exact_mod_cast frac_le t n
    have hD := S.d_nonneg (A.seq n) (B.seq n)
    have t2 : (frac t n : ℝ) / 2 ^ n * S.d (A.seq n) (B.seq n) ≤ S.d (A.seq n) (B.seq n) := by
      nlinarith
    have h2n : (0 : ℝ) ≤ 2 ^ n := by positivity
    have t3 : S.d (S.geo (A.seq n) (B.seq n) n (frac t n)) o ≤
        S.d (A.seq n) (B.seq n) + S.d (A.seq n) o := by linarith
    have := mul_le_mul_of_nonneg_left t3 h2n
    have hs := hC n
    rw [abs_of_nonneg (sd_nonneg A B n)] at hs
    simp only [sd] at hs
    have := h1 n
    nlinarith

lemma ρ_cgeo_left (A B : ConePt S o) {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    ρ A (cgeo A B t) = t * ρ A B := by
  apply ρ_eq
  refine ((tendsto_frac h0 h1).mul (tendsto_ρ A B)).congr (fun n => ?_)
  simp only [sd, cgeo]
  rw [S.geo_left n _ _ (frac_le t n)]
  ring

lemma ρ_cgeo_right (A B : ConePt S o) {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    ρ (cgeo A B t) B = (1 - t) * ρ A B := by
  apply ρ_eq
  refine (((tendsto_frac h0 h1).const_sub 1).mul (tendsto_ρ A B)).congr (fun n => ?_)
  simp only [sd, cgeo]
  rw [S.geo_right n _ _ (frac_le t n)]
  ring

/-- Busemann convexity (11) in the cone, at real fractions. -/
lemma ρ_cgeo_bus (A B C E : ConePt S o) {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    ρ (cgeo A B t) (cgeo C E t) ≤ (1 - t) * ρ A C + t * ρ B E := by
  refine le_of_tendsto_of_tendsto' (tendsto_ρ _ _)
    ((((tendsto_frac h0 h1).const_sub 1).mul (tendsto_ρ A C)).add
      ((tendsto_frac h0 h1).mul (tendsto_ρ B E))) (fun n => ?_)
  simp only [sd, cgeo]
  have := S.geo_bus n (A.seq n) (B.seq n) (C.seq n) (E.seq n) (frac t n) (frac_le t n)
  have h2n : (0 : ℝ) ≤ 2 ^ n := by positivity
  have := mul_le_mul_of_nonneg_left this h2n
  calc (2 : ℝ) ^ n * S.d (S.geo (A.seq n) (B.seq n) n (frac t n)) (S.geo (C.seq n) (E.seq n) n (frac t n))
      ≤ 2 ^ n * ((1 - (frac t n : ℝ) / 2 ^ n) * S.d (A.seq n) (C.seq n) +
          (frac t n : ℝ) / 2 ^ n * S.d (B.seq n) (E.seq n)) := this
    _ = _ := by ring

lemma cgeo_onSeg (A B : ConePt S o) {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    (coneSpace S o).OnSeg A B (cgeo A B t) t :=
  ⟨ρ_cgeo_left A B h0 h1, ρ_cgeo_right A B h0 h1⟩

/-- Busemann convexity for arbitrary points on geodesics (uniqueness of geodesic points). -/
lemma onSeg_bus {A B Z A' B' Z' : ConePt S o} {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1)
    (hZ : (coneSpace S o).OnSeg A B Z t) (hZ' : (coneSpace S o).OnSeg A' B' Z' t) :
    ρ Z Z' ≤ (1 - t) * ρ A A' + t * ρ B B' := by
  have u1 := (coneSpace S o).onSeg_unique h0 h1 hZ (cgeo_onSeg A B h0 h1)
  have u2 := (coneSpace S o).onSeg_unique h0 h1 hZ' (cgeo_onSeg A' B' h0 h1)
  have := (coneSpace S o).d_congr u1 u2
  rw [coneSpace_d] at this
  rw [this]
  exact ρ_cgeo_bus A B A' B' h0 h1

end ConePt

end OM.NNN30.Geom
