import Lib.OM.NNN20.Catalytic

/-! # Soundness of the catalytic checker, part 1: cones, witnesses, queries

* `InCone V Y`: `Y` is a nonnegative combination of the normalized hull vertices `vecV (V i)`.
  It is closed under nonnegative combinations (`InCone.add`, `InCone.smul`).
* `inTri_spec`: a passing fan-triangle witness puts `Y` in the cone (Cramer's rule).
* `queryOK_spec`: every queried endpoint is positive and in the parent's cone. -/

namespace OM.NNN20

open Finset

/-- `Y` is a nonnegative combination of the vertices `vecV (V i)` -/
def InCone (V : List (ℤ × ℤ)) (Y : Fin 3 → ℝ) : Prop :=
  ∃ μ : ℕ → ℝ, (∀ i, 0 ≤ μ i) ∧
    ∀ u, Y u = ∑ i ∈ range V.length, μ i * ((vecV (V.getD i (0, 0)) u : ℚ) : ℝ)

lemma InCone.add {V : List (ℤ × ℤ)} {Y Z : Fin 3 → ℝ} (hY : InCone V Y) (hZ : InCone V Z) :
    InCone V (fun u => Y u + Z u) := by
  obtain ⟨μ, hμ, hY⟩ := hY
  obtain ⟨ν, hν, hZ⟩ := hZ
  refine ⟨fun i => μ i + ν i, fun i => add_nonneg (hμ i) (hν i), fun u => ?_⟩
  beta_reduce
  rw [hY u, hZ u, ← sum_add_distrib]
  refine sum_congr rfl fun i _ => by ring

lemma InCone.smul {V : List (ℤ × ℤ)} {Y : Fin 3 → ℝ} (hY : InCone V Y) {a : ℝ} (ha : 0 ≤ a) :
    InCone V (fun u => a * Y u) := by
  obtain ⟨μ, hμ, hY⟩ := hY
  refine ⟨fun i => a * μ i, fun i => mul_nonneg ha (hμ i), fun u => ?_⟩
  beta_reduce
  rw [hY u, mul_sum]
  refine sum_congr rfl fun i _ => by ring

lemma InCone.congr {V : List (ℤ × ℤ)} {Y Z : Fin 3 → ℝ} (hY : InCone V Y) (h : ∀ u, Y u = Z u) :
    InCone V Z := by
  have : Y = Z := funext h
  rwa [← this]

/-- Cramer's rule in dimension three -/
lemma cramer (A B C Y : Fin 3 → ℚ) (u : Fin 3) :
    det3 A B C * Y u = det3 Y B C * A u + det3 A Y C * B u + det3 A B Y * C u := by
  fin_cases u <;> simp [det3] <;> ring

theorem inTri_spec {V : List (ℤ × ℤ)} {i : ℕ} {Y : Fin 3 → ℚ} (h : inTri V i Y = true) :
    InCone V (fun u => (Y u : ℝ)) := by
  unfold inTri at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hD, h0⟩, h1⟩, h2⟩, hlen⟩ := h
  set A := vecV (V.getD 0 (0, 0))
  set Bv := vecV (V.getD i (0, 0))
  set Cv := vecV (V.getD (i + 1) (0, 0))
  set D := det3 A Bv Cv
  -- the three coefficients, nonnegative
  have hc : ∀ e : ℚ, 0 ≤ e * D → 0 ≤ e / D := by
    intro e he
    rcases lt_or_gt_of_ne hD with hneg | hpos
    · have : e ≤ 0 := by
        by_contra hc; have hc' := not_le.mp hc; nlinarith
      exact div_nonneg_of_nonpos this hneg.le
    · have : 0 ≤ e := by
        by_contra hc; have hc' := not_le.mp hc; nlinarith
      exact div_nonneg this hpos.le
  set m0 := det3 Y Bv Cv / D
  set m1 := det3 A Y Cv / D
  set m2 := det3 A Bv Y / D
  refine ⟨fun l => (if l = 0 then (m0 : ℝ) else 0) + (if l = i then (m1 : ℝ) else 0) +
    (if l = i + 1 then (m2 : ℝ) else 0), fun l => ?_, fun u => ?_⟩
  · have := hc _ h0; have := hc _ h1; have := hc _ h2
    have e0 : (0 : ℝ) ≤ m0 := by exact_mod_cast hc _ h0
    have e1 : (0 : ℝ) ≤ m1 := by exact_mod_cast hc _ h1
    have e2 : (0 : ℝ) ≤ m2 := by exact_mod_cast hc _ h2
    positivity
  · have hY : Y u = m0 * A u + m1 * Bv u + m2 * Cv u := by
      have := cramer A Bv Cv Y u
      simp only [m0, m1, m2]
      field_simp
      linarith
    beta_reduce
    rw [show (Y u : ℝ) = ((m0 * A u + m1 * Bv u + m2 * Cv u : ℚ) : ℝ) by rw [hY]]
    simp only [add_mul, sum_add_distrib, ite_mul, zero_mul]
    rw [sum_ite_eq' (range V.length) 0, sum_ite_eq' (range V.length) i,
      sum_ite_eq' (range V.length) (i + 1)]
    have hi0 : 0 ∈ range V.length := mem_range.mpr (by omega)
    have hi1 : i ∈ range V.length := mem_range.mpr (by omega)
    have hi2 : i + 1 ∈ range V.length := mem_range.mpr hlen
    rw [if_pos hi0, if_pos hi1, if_pos hi2]
    push_cast
    ring

/-! ## Queries -/

lemma endpointOK_spec {a s : Fin 3 → ℚ} {V : List (ℤ × ℤ)} {x : ℚ} {w w' : List ℕ}
    (h : endpointOK a s V x w = some w') :
    (∀ u, 0 < a u - x * s u) ∧ InCone V (fun u => ((a u - x * s u : ℚ) : ℝ)) := by
  match w with
  | [] => simp [endpointOK] at h
  | i :: w =>
    simp only [endpointOK] at h
    split_ifs at h with h1
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h1
    exact ⟨fun u => by fin_cases u <;> simp [h1.1.1.1, h1.1.1.2, h1.1.2], inTri_spec h1.2⟩

lemma queryOK_spec {a s : Fin 3 → ℚ} : ∀ {xis : List TM} {V : List (ℤ × ℤ)} {w w' : List ℕ},
    queryOK a s xis V w = some w' → ∀ xi ∈ xis, ∀ x ∈ [((xi.rng.1 : ℚ) / ONE), ((xi.rng.2 : ℚ) / ONE)],
      (∀ u, 0 < a u - x * s u) ∧ InCone V (fun u => ((a u - x * s u : ℚ) : ℝ))
  | [], V, w, w', _ => by simp
  | xi :: xis, V, w, w', h => by
    simp only [queryOK] at h
    split at h
    · cases h
    rename_i w1 h1
    split at h
    · cases h
    rename_i w2 h2
    intro xi' hxi' x hx
    simp only [List.mem_cons] at hxi'
    rcases hxi' with rfl | hxi'
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact endpointOK_spec h1
      · exact endpointOK_spec h2
    · exact queryOK_spec h xi' hxi' x hx

end OM.NNN20

namespace OM.NNN20

open Finset

/-- an affine segment between two cone points stays in the cone -/
lemma segment_inCone {V : List (ℤ × ℤ)} {a s : Fin 3 → ℝ} {lo hi : ℝ}
    (hlo : InCone V (fun u => a u - lo * s u)) (hhi : InCone V (fun u => a u - hi * s u))
    {ξ : ℝ} (h1 : lo ≤ ξ) (h2 : ξ ≤ hi) : InCone V (fun u => a u - ξ * s u) := by
  rcases eq_or_lt_of_le (h1.trans h2) with heq | hlt
  · have : ξ = lo := by linarith
    subst this; exact hlo
  · set t := (ξ - lo) / (hi - lo)
    have ht0 : 0 ≤ t := div_nonneg (by linarith) (by linarith)
    have ht1 : 0 ≤ 1 - t := by
      rw [sub_nonneg, div_le_one (by linarith)]; linarith
    refine ((hlo.smul ht1).add (hhi.smul ht0)).congr fun u => ?_
    simp only [t]
    field_simp
    ring

end OM.NNN20

namespace OM.NNN20

open Finset

/-! ## The capacity constants -/

/-- `κ_q(t) = log2 q + t log2 t + (1-t) log2 (1-t) - t log2 (q-1)` -/
noncomputable def kappaR (q : ℕ) (t : ℝ) : ℝ :=
  Real.logb 2 q + t * Real.logb 2 t + (1 - t) * Real.logb 2 (1 - t) - t * Real.logb 2 ((q : ℝ) - 1)

/-- rational bounds of `log2 c` from a log enclosure -/
lemma logb2_bounds {c : ℚ} {l : ℚ × ℚ} (h : logI c = some l) :
    ((if 0 ≤ l.1 then l.1 / LN2HI else l.1 / LN2LO : ℚ) : ℝ) ≤ Real.logb 2 c ∧
    Real.logb 2 c ≤ ((if 0 ≤ l.2 then l.2 / LN2LO else l.2 / LN2HI : ℚ) : ℝ) := by
  obtain ⟨h1, h2⟩ := logI_spec h
  obtain ⟨g1, g2⟩ := ln2_bounds
  have hl0 := LN2LO_pos
  have hlog2 : 0 < Real.log 2 := by linarith
  rw [Real.logb]
  constructor
  · split_ifs with hs
    · push_cast
      have : (l.1 : ℝ) / LN2HI ≤ l.1 / Real.log 2 :=
        div_le_div_of_nonneg_left (by exact_mod_cast hs) hlog2 g2
      exact this.trans (div_le_div_of_nonneg_right h1 hlog2.le)
    · push_cast
      have hs' : (l.1 : ℝ) < 0 := by exact_mod_cast not_le.mp hs
      rw [div_le_div_iff₀ hl0 hlog2]
      nlinarith
  · split_ifs with hs
    · push_cast
      have : (l.2 : ℝ) / Real.log 2 ≤ l.2 / LN2LO :=
        div_le_div_of_nonneg_left (by exact_mod_cast hs) hl0 g1
      exact (div_le_div_of_nonneg_right h2 hlog2.le).trans this
    · push_cast
      have hs' : (l.2 : ℝ) < 0 := by exact_mod_cast not_le.mp hs
      rw [div_le_div_iff₀ hlog2 (by linarith)]
      nlinarith

def lg2lo (c : ℚ) : ℚ := match logI c with
  | some l => if 0 ≤ l.1 then l.1 / LN2HI else l.1 / LN2LO
  | none => 0
def lg2hi (c : ℚ) : ℚ := match logI c with
  | some l => if 0 ≤ l.2 then l.2 / LN2LO else l.2 / LN2HI
  | none => 0

lemma lg2_spec {c : ℚ} (h : (logI c).isSome = true) :
    (lg2lo c : ℝ) ≤ Real.logb 2 c ∧ Real.logb 2 c ≤ lg2hi c := by
  obtain ⟨l, hl⟩ := Option.isSome_iff_exists.mp h
  have := logb2_bounds hl
  simp only [lg2lo, lg2hi, hl]
  exact this

lemma logI_some_7 : (logI 7).isSome = true := by decide +kernel
lemma logI_some_11 : (logI 11).isSome = true := by decide +kernel
lemma logI_some_6 : (logI 6).isSome = true := by decide +kernel
lemma logI_some_10 : (logI 10).isSome = true := by decide +kernel
lemma logI_some_t0 : (logI (9 / 20)).isSome = true := by decide +kernel
lemma logI_some_1t0 : (logI (11 / 20)).isSome = true := by decide +kernel

lemma LOG2_7_rat : LOG2_7.1 ≤ lg2lo 7 ∧ lg2hi 7 ≤ LOG2_7.2 := by decide +kernel
lemma LOG2_11_rat : LOG2_11.1 ≤ lg2lo 11 ∧ lg2hi 11 ≤ LOG2_11.2 := by decide +kernel

lemma KAP_7_rat : KAP_7.1 ≤ lg2lo 7 + 9 / 20 * lg2lo (9 / 20) + 11 / 20 * lg2lo (11 / 20) - 9 / 20 * lg2hi 6 ∧
    lg2hi 7 + 9 / 20 * lg2hi (9 / 20) + 11 / 20 * lg2hi (11 / 20) - 9 / 20 * lg2lo 6 ≤ KAP_7.2 := by
  decide +kernel
lemma KAP_11_rat : KAP_11.1 ≤ lg2lo 11 + 9 / 20 * lg2lo (9 / 20) + 11 / 20 * lg2lo (11 / 20) -
      9 / 20 * lg2hi 10 ∧
    lg2hi 11 + 9 / 20 * lg2hi (9 / 20) + 11 / 20 * lg2hi (11 / 20) - 9 / 20 * lg2lo 10 ≤ KAP_11.2 := by
  decide +kernel

theorem log2q_spec {q : ℕ} (hq : q = 7 ∨ q = 11) :
    ((log2q q).1 : ℝ) ≤ Real.logb 2 q ∧ Real.logb 2 q ≤ (log2q q).2 := by
  rcases hq with rfl | rfl
  · have h := lg2_spec logI_some_7
    have r := LOG2_7_rat
    have r1 : (LOG2_7.1 : ℝ) ≤ lg2lo 7 := by exact_mod_cast r.1
    have r2 : (lg2hi 7 : ℝ) ≤ LOG2_7.2 := by exact_mod_cast r.2
    simp only [log2q, if_pos rfl]
    push_cast at h ⊢
    exact ⟨r1.trans h.1, h.2.trans r2⟩
  · have h := lg2_spec logI_some_11
    have r := LOG2_11_rat
    have r1 : (LOG2_11.1 : ℝ) ≤ lg2lo 11 := by exact_mod_cast r.1
    have r2 : (lg2hi 11 : ℝ) ≤ LOG2_11.2 := by exact_mod_cast r.2
    simp only [log2q, show (11 : ℕ) ≠ 7 by norm_num, if_false]
    push_cast at h ⊢
    exact ⟨r1.trans h.1, h.2.trans r2⟩

theorem kapq_spec {q : ℕ} (hq : q = 7 ∨ q = 11) :
    ((kapq q).1 : ℝ) ≤ kappaR q (T0 : ℝ) ∧ kappaR q (T0 : ℝ) ≤ (kapq q).2 := by
  have ht := lg2_spec logI_some_t0
  have h1t := lg2_spec logI_some_1t0
  have eT0 : (T0 : ℝ) = ((9 / 20 : ℚ) : ℝ) := by norm_num [T0]
  have e1 : (1 : ℝ) - (T0 : ℝ) = ((11 / 20 : ℚ) : ℝ) := by norm_num [T0]
  rcases hq with rfl | rfl
  · have h7 := lg2_spec logI_some_7
    have h6 := lg2_spec logI_some_6
    have r := KAP_7_rat
    have e6 : ((7 : ℕ) : ℝ) - 1 = ((6 : ℚ) : ℝ) := by norm_num
    simp only [kapq, if_pos rfl, kappaR]
    rw [e6, e1, eT0]
    have r1 : (KAP_7.1 : ℝ) ≤ ((lg2lo 7 + 9 / 20 * lg2lo (9 / 20) + 11 / 20 * lg2lo (11 / 20) -
        9 / 20 * lg2hi 6 : ℚ) : ℝ) := by exact_mod_cast r.1
    have r2 : ((lg2hi 7 + 9 / 20 * lg2hi (9 / 20) + 11 / 20 * lg2hi (11 / 20) - 9 / 20 * lg2lo 6 : ℚ) : ℝ)
        ≤ KAP_7.2 := by exact_mod_cast r.2
    push_cast at r1 r2 h7 h6 ht h1t ⊢
    constructor <;> nlinarith
  · have h11 := lg2_spec logI_some_11
    have h10 := lg2_spec logI_some_10
    have r := KAP_11_rat
    have e10 : ((11 : ℕ) : ℝ) - 1 = ((10 : ℚ) : ℝ) := by norm_num
    simp only [kapq, show (11 : ℕ) ≠ 7 by norm_num, if_false, kappaR]
    rw [e10, e1, eT0]
    have r1 : (KAP_11.1 : ℝ) ≤ ((lg2lo 11 + 9 / 20 * lg2lo (9 / 20) + 11 / 20 * lg2lo (11 / 20) -
        9 / 20 * lg2hi 10 : ℚ) : ℝ) := by exact_mod_cast r.1
    have r2 : ((lg2hi 11 + 9 / 20 * lg2hi (9 / 20) + 11 / 20 * lg2hi (11 / 20) - 9 / 20 * lg2lo 10 : ℚ) : ℝ)
        ≤ KAP_11.2 := by exact_mod_cast r.2
    push_cast at r1 r2 h11 h10 ht h1t ⊢
    constructor <;> nlinarith

end OM.NNN20
