import Lib.OM.NNN30.Net.Core
import Mathlib.Topology.Sion
import Mathlib.Analysis.Convex.Quasiconvex

/-! # The linear sandwich, without the concave `F_V`

A local network on the grid with positive value has data `(log₂ value, ndCost, U, V)`; the
achievable data are closed under sums (Kronecker products) and contain `0` (the unit network), and
each satisfies the core inequality.  Hence every finite family of achievable data has a common
disc parameter `λ` with `log₂ value ≤ cost at Dlam d λ` (Sion's minimax theorem on the simplex of
weights times the compact convex set of disc parameters; rational weights by powers, real weights
by continuity), and by compactness one `λ` works for all networks: `Dlam d λ` is admissible
(`exists_adm_Dlam`). -/

noncomputable section
open scoped BigOperators Classical
open Filter Topology

namespace OM.NNN30.Net

open CoordinateTensor OM.NNN.Raw

variable {V : Type} [Fintype V] [LinearOrder V]

/-- the disc parameters -/
def Lam (V : Type) [LinearOrder V] : Set (Rect V → ℝ × ℝ) :=
  {lam | ∀ R, 0 ≤ (lam R).1 ∧ 0 ≤ (lam R).2 ∧ (lam R).1 ^ 2 + (lam R).2 ^ 2 ≤ 1}

/-- data of a network: `(log₂ value, ndCost, U, V)` -/
abbrev Dat (V : Type) [LinearOrder V] := ℝ × ℝ × (Rect V → ℝ) × (Rect V → ℝ)

/-- the bound `Hd` on data -/
def HdD (d : V → V → ℝ) (p : Dat V) : ℝ := Hd d p.2.1 p.2.2.1 p.2.2.2

/-- the linear bound at disc parameters `lam` -/
def linD (d : V → V → ℝ) (lam : Rect V → ℝ × ℝ) (p : Dat V) : ℝ :=
  p.2.1 + ∑ R, crad d R * ((lam R).1 * p.2.2.1 R + (lam R).2 * p.2.2.2 R)

/-- achievable data -/
def Ach (φ : OM.PolMul.Spectral ℂ) (τ : Fin 3 → V) (d : V → V → ℝ) : Set (Dat V) :=
  {p | ∃ (O0 O1 O2 : Type) (_ : Fintype O0) (_ : Fintype O1) (_ : Fintype O2)
    (M : TN (V × V) O0 O1 O2), M.Local (fun i => (τ i, τ i)) ∧ 0 < value φ M.Z ∧
      p = (Real.logb 2 (value φ M.Z), M.ndCost d, M.Uw, M.Vw)}

variable {φ : OM.PolMul.Spectral ℂ} {τ : Fin 3 → V} {d : V → V → ℝ}

lemma zero_mem_Ach : (0 : Dat V) ∈ Ach φ τ d := by
  refine ⟨Unit, Unit, Unit, inferInstance, inferInstance, inferInstance, TN.one (V × V),
    TN.Local_one _, ?_, ?_⟩
  · have h : (TN.one (V × V)).Z = fun (_ : Unit) (_ : Unit) (_ : Unit) => (1 : ℂ) := TN.Z_one
    rw [h, OM.NNN22.value_one111]; norm_num
  · have h : (TN.one (V × V)).Z = fun (_ : Unit) (_ : Unit) (_ : Unit) => (1 : ℂ) := TN.Z_one
    rw [h, OM.NNN22.value_one111, Real.logb_one, TN.ndCost_one]
    ext R <;> simp [TN.Uw_one, TN.Vw_one]

lemma add_mem_Ach {p p' : Dat V} (hp : p ∈ Ach φ τ d) (hp' : p' ∈ Ach φ τ d) :
    p + p' ∈ Ach φ τ d := by
  obtain ⟨O0, O1, O2, i0, i1, i2, M, hM, hv, rfl⟩ := hp
  obtain ⟨P0, P1, P2, j0, j1, j2, M', hM', hv', rfl⟩ := hp'
  have hval := value_kron_of_pos φ M M' hv hv'
  refine ⟨O0 × P0, O1 × P1, O2 × P2, inferInstance, inferInstance, inferInstance, M.kron M',
    hM.kron hM', by rw [hval]; positivity, ?_⟩
  rw [hval, Real.logb_mul hv.ne' hv'.ne', TN.ndCost_kron]
  ext R
  · rfl
  · rfl
  · simp [TN.Uw_kron]
  · simp [TN.Vw_kron]

lemma nsmul_mem_Ach {p : Dat V} (hp : p ∈ Ach φ τ d) (k : ℕ) : k • p ∈ Ach φ τ d := by
  induction k with
  | zero => simpa using (zero_mem_Ach : (0 : Dat V) ∈ Ach φ τ d)
  | succ k ih => rw [succ_nsmul]; exact add_mem_Ach ih hp

lemma sum_mem_Ach {n : ℕ} {p : Fin n → Dat V} (hp : ∀ i, p i ∈ Ach φ τ d) (q : Fin n → ℕ) :
    (∑ i, q i • p i) ∈ Ach φ τ d := by
  have : ∀ s : Finset (Fin n), (∑ i ∈ s, q i • p i) ∈ Ach φ τ d := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using (zero_mem_Ach : (0 : Dat V) ∈ Ach φ τ d)
    | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact add_mem_Ach (nsmul_mem_Ach (hp a) _) ih
  exact this Finset.univ

lemma core_Ach (h3 : S_R108_3) (hd : Adm φ τ d) {p : Dat V} (hp : p ∈ Ach φ τ d) :
    p.1 ≤ HdD d p := by
  obtain ⟨O0, O1, O2, i0, i1, i2, M, hM, hv, rfl⟩ := hp
  exact core h3 hd M hM hv

lemma HdD_smul (d : V → V → ℝ) {c : ℝ} (hc : 0 ≤ c) (p : Dat V) : HdD d (c • p) = c * HdD d p := by
  unfold HdD Hd
  simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, Pi.smul_apply]
  rw [mul_add, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun R _ => ?_
  have : (c * p.2.2.1 R) ^ 2 + (c * p.2.2.2 R) ^ 2 = c ^ 2 * (p.2.2.1 R ^ 2 + p.2.2.2 R ^ 2) := by
    ring
  rw [this, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc]
  ring

lemma continuous_HdD (d : V → V → ℝ) : Continuous (HdD d) := by
  unfold HdD Hd
  fun_prop

/-- A continuous, positively homogeneous support bound extends from integer powers of
achievable data to all nonnegative real combinations. -/
lemma conv_tests_of {A : Set (Dat V)} {H : Dat V → ℝ} (hcont : Continuous H)
    (hscale : ∀ {c : ℝ}, 0 ≤ c → ∀ p, H (c • p) = c * H p)
    (hcore : ∀ {p}, p ∈ A → p.1 ≤ H p)
    {n : ℕ} {p : Fin n → Dat V} (hp : ∀ i, p i ∈ A)
    (hadd : ∀ q : Fin n → ℕ, ∑ i, q i • p i ∈ A)
    (μ : Fin n → ℝ) (hμ : ∀ i, 0 ≤ μ i) :
    ∑ i, μ i * (p i).1 ≤ H (∑ i, μ i • p i) := by
  have hQ : ∀ Q : ℕ, 0 < Q → ∑ i, ((⌊μ i * Q⌋₊ : ℝ) / Q) * (p i).1 ≤
      H (∑ i, ((⌊μ i * Q⌋₊ : ℝ) / Q) • p i) := by
    intro Q hQ
    have hQR : (0 : ℝ) < Q := by exact_mod_cast hQ
    have hc := hcore (hadd (fun i => ⌊μ i * Q⌋₊))
    have e1 : (∑ i, ⌊μ i * Q⌋₊ • p i).1 = ∑ i, (⌊μ i * Q⌋₊ : ℝ) * (p i).1 := by
      rw [Prod.fst_sum]
      simp [nsmul_eq_mul]
    have e2 : (∑ i, ((⌊μ i * Q⌋₊ : ℝ) / Q) • p i) = (1 / (Q : ℝ)) • ∑ i, ⌊μ i * Q⌋₊ • p i := by
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
      congr 1
      ring
    rw [e2, hscale (by positivity)]
    rw [e1] at hc
    have e3 : ∑ i, ((⌊μ i * Q⌋₊ : ℝ) / Q) * (p i).1 =
        (1 / (Q : ℝ)) * ∑ i, (⌊μ i * Q⌋₊ : ℝ) * (p i).1 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    rw [e3]
    exact mul_le_mul_of_nonneg_left hc (by positivity)
  have hlim : ∀ i, Tendsto (fun Q : ℕ => (⌊μ i * Q⌋₊ : ℝ) / Q) atTop (𝓝 (μ i)) :=
    fun i => (tendsto_nat_floor_mul_div_atTop (hμ i)).comp tendsto_natCast_atTop_atTop
  have hL : Tendsto (fun Q : ℕ => ∑ i, ((⌊μ i * Q⌋₊ : ℝ) / Q) * (p i).1) atTop
      (𝓝 (∑ i, μ i * (p i).1)) :=
    tendsto_finset_sum _ fun i _ => (hlim i).mul_const _
  have hR : Tendsto (fun Q : ℕ => H (∑ i, ((⌊μ i * Q⌋₊ : ℝ) / Q) • p i)) atTop
      (𝓝 (H (∑ i, μ i • p i))) :=
    (hcont.tendsto _).comp (tendsto_finset_sum _ fun i _ => (hlim i).smul_const _)
  exact le_of_tendsto_of_tendsto hL hR (eventually_atTop.2 ⟨1, fun Q hQ1 => hQ Q hQ1⟩)

lemma conv_Ach_of {H : Dat V → ℝ} (hcont : Continuous H)
    (hscale : ∀ {c : ℝ}, 0 ≤ c → ∀ p, H (c • p) = c * H p)
    (hcore : ∀ {p}, p ∈ Ach φ τ d → p.1 ≤ H p)
    {n : ℕ} {p : Fin n → Dat V} (hp : ∀ i, p i ∈ Ach φ τ d)
    (μ : Fin n → ℝ) (hμ : ∀ i, 0 ≤ μ i) :
    ∑ i, μ i * (p i).1 ≤ H (∑ i, μ i • p i) :=
  conv_tests_of hcont hscale hcore hp (sum_mem_Ach hp) μ hμ

/-- weighted sums of achievable data satisfy the core bound -/
lemma conv_Ach (h3 : S_R108_3) (hd : Adm φ τ d) {n : ℕ} {p : Fin n → Dat V}
    (hp : ∀ i, p i ∈ Ach φ τ d) (μ : Fin n → ℝ) (hμ : ∀ i, 0 ≤ μ i) :
    ∑ i, μ i * (p i).1 ≤ HdD d (∑ i, μ i • p i) :=
  conv_Ach_of (continuous_HdD d) (HdD_smul d) (core_Ach h3 hd) hp μ hμ

lemma linD_add (d : V → V → ℝ) (lam : Rect V → ℝ × ℝ) (p p' : Dat V) :
    linD d lam (p + p') = linD d lam p + linD d lam p' := by
  unfold linD
  simp only [Prod.snd_add, Prod.fst_add, Pi.add_apply]
  rw [add_add_add_comm, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun R _ => ?_
  ring

lemma linD_smul (d : V → V → ℝ) (lam : Rect V → ℝ × ℝ) (c : ℝ) (p : Dat V) :
    linD d lam (c • p) = c * linD d lam p := by
  unfold linD
  simp only [Prod.smul_snd, Prod.smul_fst, smul_eq_mul, Pi.smul_apply]
  rw [mul_add, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun R _ => ?_
  ring

lemma linD_zero (d : V → V → ℝ) (lam : Rect V → ℝ × ℝ) : linD d lam 0 = 0 := by
  have := linD_smul d lam 0 0
  simpa using this

lemma linD_sum (d : V → V → ℝ) (lam : Rect V → ℝ × ℝ) {n : ℕ} (μ : Fin n → ℝ)
    (p : Fin n → Dat V) : linD d lam (∑ i, μ i • p i) = ∑ i, μ i * linD d lam (p i) := by
  have : ∀ s : Finset (Fin n), linD d lam (∑ i ∈ s, μ i • p i) = ∑ i ∈ s, μ i * linD d lam (p i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [linD_zero]
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, linD_add, linD_smul, ih]
  exact this Finset.univ

lemma U_nonneg_Ach {p : Dat V} (hp : p ∈ Ach φ τ d) (R : Rect V) : 0 ≤ p.2.2.1 R := by
  obtain ⟨O0, O1, O2, i0, i1, i2, M, hM, hv, rfl⟩ := hp
  exact M.Uw_nonneg hv R

lemma W_nonneg_Ach {p : Dat V} (hp : p ∈ Ach φ τ d) (R : Rect V) : 0 ≤ p.2.2.2 R := by
  obtain ⟨O0, O1, O2, i0, i1, i2, M, hM, hv, rfl⟩ := hp
  exact M.Vw_nonneg hv R

/-- the disc parameter attaining `√(u² + w²)` -/
def nrm (u w : ℝ) : ℝ × ℝ :=
  if u ^ 2 + w ^ 2 = 0 then (0, 0) else (u / Real.sqrt (u ^ 2 + w ^ 2), w / Real.sqrt (u ^ 2 + w ^ 2))

lemma nrm_spec (u w : ℝ) : (nrm u w).1 * u + (nrm u w).2 * w = Real.sqrt (u ^ 2 + w ^ 2) := by
  unfold nrm
  split_ifs with h
  · simp [h]
  · have hpos : 0 < u ^ 2 + w ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm h)
    have hs := Real.sq_sqrt hpos.le
    have hsp := Real.sqrt_pos.2 hpos
    field_simp
    nlinarith

lemma nrm_mem {u w : ℝ} (hu : 0 ≤ u) (hw : 0 ≤ w) :
    0 ≤ (nrm u w).1 ∧ 0 ≤ (nrm u w).2 ∧ (nrm u w).1 ^ 2 + (nrm u w).2 ^ 2 ≤ 1 := by
  unfold nrm
  split_ifs with h
  · simp
  · have hpos : 0 < u ^ 2 + w ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm h)
    have hs := Real.sq_sqrt hpos.le
    have hsp := Real.sqrt_pos.2 hpos
    refine ⟨div_nonneg hu hsp.le, div_nonneg hw hsp.le, ?_⟩
    rw [div_pow, div_pow, hs, ← add_div, div_self hpos.ne']

lemma convex_Lam : Convex ℝ (Lam V) := by
  intro x hx y hy a b ha hb hab
  intro R
  obtain ⟨hx1, hx2, hx3⟩ := hx R
  obtain ⟨hy1, hy2, hy3⟩ := hy R
  simp only [Pi.add_apply, Pi.smul_apply, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
    Prod.smul_snd, smul_eq_mul]
  refine ⟨by positivity, by positivity, ?_⟩
  have hb' : b = 1 - a := by linarith
  subst hb'
  nlinarith [sq_nonneg ((x R).1 - (y R).1), sq_nonneg ((x R).2 - (y R).2), mul_nonneg ha hb]

lemma isCompact_Lam : IsCompact (Lam V) := by
  have hK : IsCompact (Set.univ.pi fun _ : Rect V => (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1)) :=
    isCompact_univ_pi fun _ => isCompact_Icc.prod isCompact_Icc
  apply hK.of_isClosed_subset
  · unfold Lam
    simp only [Set.ofPred_forall]
    refine isClosed_iInter fun R => ?_
    have h1 : IsClosed {lam : Rect V → ℝ × ℝ | 0 ≤ (lam R).1} :=
      isClosed_le continuous_const (by fun_prop)
    have h2 : IsClosed {lam : Rect V → ℝ × ℝ | 0 ≤ (lam R).2} :=
      isClosed_le continuous_const (by fun_prop)
    have h3 : IsClosed {lam : Rect V → ℝ × ℝ | (lam R).1 ^ 2 + (lam R).2 ^ 2 ≤ 1} :=
      isClosed_le (by fun_prop) continuous_const
    have := h1.inter (h2.inter h3)
    simpa only [Set.setOf_and] using this
  · intro lam hlam
    simp only [Set.mem_pi, Set.mem_univ, Set.mem_prod, Set.mem_Icc, forall_const]
    intro R
    obtain ⟨h1, h2, h3⟩ := hlam R
    refine ⟨⟨h1, ?_⟩, ⟨h2, ?_⟩⟩ <;> nlinarith [sq_nonneg (lam R).1, sq_nonneg (lam R).2]

lemma linD_comb (d : V → V → ℝ) (lam lam' : Rect V → ℝ × ℝ) (a b : ℝ) (hab : a + b = 1)
    (p : Dat V) : linD d (a • lam + b • lam') p = a * linD d lam p + b * linD d lam' p := by
  unfold linD
  simp only [Pi.add_apply, Pi.smul_apply, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
    Prod.smul_snd, smul_eq_mul]
  rw [mul_add, mul_add, Finset.mul_sum, Finset.mul_sum]
  have h : a * p.2.1 + (∑ R, a * (crad d R * ((lam R).1 * p.2.2.1 R + (lam R).2 * p.2.2.2 R))) +
      (b * p.2.1 + ∑ R, b * (crad d R * ((lam' R).1 * p.2.2.1 R + (lam' R).2 * p.2.2.2 R))) =
      (a + b) * p.2.1 + ∑ R, (a * (crad d R * ((lam R).1 * p.2.2.1 R + (lam R).2 * p.2.2.2 R)) +
        b * (crad d R * ((lam' R).1 * p.2.2.1 R + (lam' R).2 * p.2.2.2 R))) := by
    rw [Finset.sum_add_distrib]; ring
  rw [h, hab, one_mul]
  congr 1
  refine Finset.sum_congr rfl fun R _ => ?_
  ring

/-! ## Sion's theorem for finitely many networks -/

/-- the simplex of weights -/
def Simp (n : ℕ) : Set (Fin n → ℝ) := {μ | (∀ i, 0 ≤ μ i) ∧ ∑ i, μ i = 1}

lemma isCompact_Simp (n : ℕ) : IsCompact (Simp n) := by
  have hK : IsCompact (Set.univ.pi fun _ : Fin n => Set.Icc (0 : ℝ) 1) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  apply hK.of_isClosed_subset
  · have h1 : IsClosed {μ : Fin n → ℝ | ∀ i, 0 ≤ μ i} := by
      simp only [Set.ofPred_forall]
      exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)
    have h2 : IsClosed {μ : Fin n → ℝ | ∑ i, μ i = 1} :=
      isClosed_eq (continuous_finset_sum _ fun i _ => continuous_apply i) continuous_const
    exact h1.inter h2
  · intro μ hμ
    simp only [Set.mem_pi, Set.mem_univ, Set.mem_Icc, forall_const]
    intro i
    refine ⟨hμ.1 i, ?_⟩
    have := Finset.single_le_sum (fun j _ => hμ.1 j) (Finset.mem_univ i)
    rw [hμ.2] at this
    exact this

lemma convex_Simp (n : ℕ) : Convex ℝ (Simp n) := by
  intro x hx y hy a b ha hb hab
  refine ⟨fun i => ?_, ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact add_nonneg (mul_nonneg ha (hx.1 i)) (mul_nonneg hb (hy.1 i))
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib, ← Finset.mul_sum,
      hx.2, hy.2, mul_one, hab]

/-- Minimax for a compact convex family of prices. It suffices that each weighted
network test can be met by a price in the family. -/
lemma finite_family_of {K : Set (Rect V → ℝ × ℝ)} (hKne : K.Nonempty)
    (hKconv : Convex ℝ K) (hKcompact : IsCompact K) {n : ℕ} {p : Fin n → Dat V}
    (htest : ∀ a ∈ Simp n, ∃ lam ∈ K,
      ∑ i, a i * (p i).1 ≤ linD d lam (∑ i, a i • p i)) :
    ∃ lam ∈ K, ∀ i, (p i).1 ≤ linD d lam (p i) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨hKne.choose, hKne.choose_spec, fun i => i.elim0⟩
  let f : (Fin n → ℝ) → (Rect V → ℝ × ℝ) → ℝ :=
    fun μ lam => ∑ i, μ i * (linD d lam (p i) - (p i).1)
  have hfy : ∀ lam ∈ K, LowerSemicontinuousOn (fun μ => f μ lam) (Simp n) := fun lam _ =>
    (continuous_finset_sum _ fun i _ => (continuous_apply i).mul continuous_const).continuousOn
      |>.lowerSemicontinuousOn
  have hfy' : ∀ lam ∈ K, QuasiconvexOn ℝ (Simp n) (fun μ => f μ lam) := by
    intro lam _
    refine ConvexOn.quasiconvexOn ⟨convex_Simp n, ?_⟩
    intro x _ y _ a b _ _ _
    simp only [f, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, Finset.sum_add_distrib,
      Finset.mul_sum, mul_assoc]
    exact le_rfl
  have hlin : ∀ μ : Fin n → ℝ, Continuous fun lam => f μ lam := by
    intro μ
    unfold f linD
    fun_prop
  have hfx : ∀ μ ∈ Simp n, UpperSemicontinuousOn (fun lam => f μ lam) (K) := fun μ _ =>
    (hlin μ).continuousOn.upperSemicontinuousOn
  have hfx' : ∀ μ ∈ Simp n, QuasiconcaveOn ℝ (K) (fun lam => f μ lam) := by
    intro μ _
    refine ConcaveOn.quasiconcaveOn ⟨hKconv, ?_⟩
    intro x _ y _ a b _ _ hab
    apply le_of_eq
    show a * f μ x + b * f μ y = f μ (a • x + b • y)
    simp only [f, linD_comb d x y a b hab, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hb : b = 1 - a := by linarith
    subst hb
    ring
  have ne_X : (Simp n).Nonempty := ⟨fun _ => 1 / n, fun _ => by positivity, by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp⟩
  obtain ⟨a, ha, b, hb, hsad⟩ := Sion.exists_isSaddlePointOn ne_X (convex_Simp n)
    (isCompact_Simp n) hfy hfy' hKconv hKne hKcompact hfx hfx'
  obtain ⟨lam0, hlam0, hprice⟩ := htest a ha
  have hval : 0 ≤ f a lam0 := by
    simpa only [f, mul_sub, Finset.sum_sub_distrib, sub_nonneg, linD_sum] using
      (show 0 ≤ linD d lam0 (∑ i, a i • p i) - ∑ i, a i * (p i).1 from sub_nonneg.2 hprice)
  refine ⟨b, hb, fun i => ?_⟩
  let e : Fin n → ℝ := fun j => if j = i then 1 else 0
  have he : e ∈ Simp n := ⟨fun j => by simp only [e]; split_ifs <;> norm_num, by simp [e]⟩
  have hs := hsad e he lam0 hlam0
  have hfe : f e b = linD d b (p i) - (p i).1 := by
    simp only [f, e, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  linarith

/-- every finite family of achievable data has a common disc parameter -/
lemma finite_family (h3 : S_R108_3) (hd : Adm φ τ d) {n : ℕ} {p : Fin n → Dat V}
    (hp : ∀ i, p i ∈ Ach φ τ d) : ∃ lam ∈ Lam V, ∀ i, (p i).1 ≤ linD d lam (p i) := by
  apply finite_family_of ⟨0, fun R => by simp⟩ convex_Lam isCompact_Lam
  intro a ha
  -- the disc parameter attaining the bound for the weighted data
  let P : Dat V := ∑ i, a i • p i
  have hPU : ∀ R, 0 ≤ P.2.2.1 R := fun R => by
    have e : P.2.2.1 R = ∑ i, a i * (p i).2.2.1 R := by
      simp [P, Prod.fst_sum, Prod.snd_sum, Finset.sum_apply]
    rw [e]
    exact Finset.sum_nonneg fun i _ => mul_nonneg (ha.1 i) (U_nonneg_Ach (hp i) R)
  have hPW : ∀ R, 0 ≤ P.2.2.2 R := fun R => by
    have e : P.2.2.2 R = ∑ i, a i * (p i).2.2.2 R := by
      simp [P, Prod.fst_sum, Prod.snd_sum, Finset.sum_apply]
    rw [e]
    exact Finset.sum_nonneg fun i _ => mul_nonneg (ha.1 i) (W_nonneg_Ach (hp i) R)
  let lam0 : Rect V → ℝ × ℝ := fun R => nrm (P.2.2.1 R) (P.2.2.2 R)
  have hlam0 : lam0 ∈ Lam V := fun R => nrm_mem (hPU R) (hPW R)
  refine ⟨lam0, hlam0, (conv_Ach h3 hd hp a ha.1).trans_eq ?_⟩
  unfold linD HdD Hd
  congr 1
  exact Finset.sum_congr rfl fun R _ => by rw [nrm_spec]

/-- Compactness turns the finite price tests into admissibility on every network. -/
theorem common_parameters {A : Set (Dat V)} {K : Set (Rect V → ℝ × ℝ)} (hKcompact : IsCompact K)
    (hfinite : ∀ {n : ℕ} {p : Fin n → Dat V}, (∀ i, p i ∈ A) →
      ∃ lam ∈ K, ∀ i, (p i).1 ≤ linD d lam (p i)) :
    ∃ lam ∈ K, ∀ p ∈ A, p.1 ≤ linD d lam p := by
  let ι := {p : Dat V // p ∈ A}
  let t : ι → Set (Rect V → ℝ × ℝ) := fun p => {lam | p.1.1 ≤ linD d lam p.1}
  have htc : ∀ p, IsClosed (t p) := by
    intro p
    refine isClosed_le continuous_const ?_
    unfold linD
    fun_prop
  have hfin : ∀ u : Finset ι, (K ∩ ⋂ p ∈ u, t p).Nonempty := by
    intro u
    let pp : Fin u.card → Dat V := fun i => (u.equivFin.symm i).1.1
    obtain ⟨lam, hlam, hall⟩ := hfinite (p := pp) fun i => (u.equivFin.symm i).1.2
    refine ⟨lam, hlam, Set.mem_iInter₂.2 fun p hp => ?_⟩
    have := hall (u.equivFin ⟨p, hp⟩)
    simp only [pp, Equiv.symm_apply_apply] at this
    exact this
  obtain ⟨lam, hlam, hall⟩ := hKcompact.inter_iInter_nonempty t htc hfin
  exact ⟨lam,hlam,fun p hp => Set.mem_iInter.1 hall ⟨p,hp⟩⟩

theorem exists_adm_Dlam_of {K : Set (Rect V → ℝ × ℝ)} (hKcompact : IsCompact K)
    (hfinite : ∀ {n : ℕ} {p : Fin n → Dat V}, (∀ i, p i ∈ Ach φ τ d) →
      ∃ lam ∈ K, ∀ i, (p i).1 ≤ linD d lam (p i)) :
    ∃ lam ∈ K, Adm φ (fun i => (τ i, τ i)) (Dlam d lam) := by
  obtain ⟨lam,hlam,hall⟩ := common_parameters hKcompact hfinite
  refine ⟨lam, hlam, ?_⟩
  intro O0 O1 O2 _ _ _ M hM hv
  have hmem : (Real.logb 2 (value φ M.Z), M.ndCost d, M.Uw, M.Vw) ∈ Ach φ τ d :=
    ⟨O0, O1, O2, inferInstance, inferInstance, inferInstance, M, hM, hv, rfl⟩
  have := hall _ hmem
  simp only [linD] at this
  rw [cost_Dlam]
  exact this

/-- **The linear sandwich**: one disc parameter for all networks -/
theorem exists_adm_Dlam (h3 : S_R108_3) (hd : Adm φ τ d) :
    ∃ lam ∈ Lam V, Adm φ (fun i => (τ i, τ i)) (Dlam d lam) :=
  exists_adm_Dlam_of isCompact_Lam (finite_family h3 hd)

end OM.NNN30.Net
