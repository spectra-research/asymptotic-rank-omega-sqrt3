import PLATFORM.Statements.«R108.1»
import PLATFORM.Statements.«R108.2»
import PLATFORM.Statements.«R108.3»
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # R108.3 from R108.1 and R108.2: the rectangular crossing estimate

At widths `a = α/q`, `b = β/q` and scale `L = q j`, let `H, E` be the least integers `≥ 1` with
`p(H) ≥ 2^(αj)` and `p(E) ≥ 2^(βj)` (they exist since `p` is unbounded by R108.2).  The pieces of
R108.1 at `(H, E)`, restricted to `2^(αj)` and `2^(βj)` indices through injections into the
partitions, sum to the two equalities (`Bf_sum`), and restriction does not raise either flattening
rank (`Bf_rank_row`, `Bf_rank_col`: ranks `≤ Q(k)`, `≤ Q(D - k)`, `D = 2(H + E)`).  There are
`D + 1 = O(L²)` pieces (`Kf_bound`, from the lower growth of `p`).  With
`(log₂ Q(h))² ≤ (C + η)² h + M` (upper growth of `Q`) and
`H ≤ (αj/(C - η))² + O(1)` (minimality of `H` and the lower growth of `p`), every piece has
`(log₂ r)² + (log₂ c)² ≤ ((C+η)/(C-η))² · 2(α² + β²) j² + O(1)`; dividing by `L²` and letting
`η → 0` gives `r² + c² ≤ 2(a² + b²) + ε` for large `j` (`circle`).  The positivity of `α, β` is
not needed. -/

namespace OM.NNN30.Rect

open Filter Topology

/-- `Q(h) = ∑_{j ≤ h} p(j)` as a natural number. -/
abbrev Qn (h : ℕ) : ℕ := ∑ j ∈ Finset.range (h + 1), Fintype.card j.Partition

lemma one_le_Qn (h : ℕ) : 1 ≤ Qn h := by
  have : Fintype.card (Nat.Partition 0) ≤ Qn h :=
    Finset.single_le_sum (f := fun j => Fintype.card j.Partition) (fun _ _ => Nat.zero_le _)
      (Finset.mem_range.mpr (Nat.succ_pos h))
  have h0 : Fintype.card (Nat.Partition 0) = 1 := Fintype.card_unique
  omega

lemma Qn_mono {h h' : ℕ} (hh : h ≤ h') : Qn h ≤ Qn h' :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr (by omega))
    (fun _ _ _ => Nat.zero_le _)

lemma logb_nat_nonneg (n : ℕ) : 0 ≤ Real.logb 2 n := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp
  · exact Real.logb_nonneg one_lt_two (by exact_mod_cast h)

lemma logb_sq_le {n m : ℕ} (hnm : n ≤ m) :
    Real.logb 2 n ^ 2 ≤ Real.logb 2 m ^ 2 := by
  apply pow_le_pow_left₀ (logb_nat_nonneg n)
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simpa using logb_nat_nonneg m
  · exact Real.logb_le_logb_of_le one_lt_two (by exact_mod_cast h) (by exact_mod_cast hnm)

/-- From R108.2: partition numbers are unbounded. -/
lemma exists_H (h2 : S_R108_2) (A : ℕ) : ∃ H : ℕ, 1 ≤ H ∧ A ≤ Fintype.card H.Partition := by
  obtain ⟨C, hC, hp, -⟩ := h2
  obtain ⟨h1, hh1⟩ := eventually_atTop.mp (hp.eventually (Ioi_mem_nhds (half_lt_self hC)))
  obtain ⟨n, hn⟩ := exists_nat_ge ((2 * Real.logb 2 A / C) ^ 2)
  set h := max (max h1 1) n with hh
  refine ⟨h, le_trans (le_max_right _ _) (le_max_left _ _), ?_⟩
  have hgt := hh1 h (le_trans (le_max_left _ _) (le_max_left _ _))
  have hpos : (0 : ℝ) < Real.sqrt h := Real.sqrt_pos.mpr (by
    have : 1 ≤ h := le_trans (le_max_right _ _) (le_max_left _ _)
    exact_mod_cast this)
  rw [lt_div_iff₀ hpos] at hgt
  rcases Nat.eq_zero_or_pos A with hA | hA
  · subst hA; exact Nat.zero_le _
  have hlogA : 0 ≤ Real.logb 2 A := logb_nat_nonneg A
  have hsq : 2 * Real.logb 2 A / C ≤ Real.sqrt h := by
    have h3 : (2 * Real.logb 2 A / C) ^ 2 ≤ (h : ℝ) := hn.trans (by exact_mod_cast le_max_right _ _)
    calc 2 * Real.logb 2 A / C = Real.sqrt ((2 * Real.logb 2 A / C) ^ 2) :=
          (Real.sqrt_sq (by positivity)).symm
      _ ≤ Real.sqrt h := Real.sqrt_le_sqrt h3
  have hlog : Real.logb 2 A < Real.logb 2 (Fintype.card h.Partition) := by
    have : Real.logb 2 A ≤ C / 2 * Real.sqrt h := by
      rw [div_le_iff₀ hC] at hsq; nlinarith
    linarith
  have hpos' : (0 : ℝ) < A := by exact_mod_cast hA
  have hp0 : (0 : ℝ) < Fintype.card h.Partition := by exact_mod_cast Fintype.card_pos
  have := (Real.logb_lt_logb_iff one_lt_two hpos' hp0).mp hlog
  exact_mod_cast this.le

/-- The least `H ≥ 1` with `p(H) ≥ A`. -/
noncomputable def Hof (h2 : S_R108_2) (A : ℕ) : ℕ := Nat.find (exists_H h2 A)

lemma Hof_spec (h2 : S_R108_2) (A : ℕ) :
    1 ≤ Hof h2 A ∧ A ≤ Fintype.card (Hof h2 A).Partition := Nat.find_spec (exists_H h2 A)

lemma Hof_min (h2 : S_R108_2) (A : ℕ) {H : ℕ} (hH : H < Hof h2 A) :
    ¬ (1 ≤ H ∧ A ≤ Fintype.card H.Partition) := Nat.find_min (exists_H h2 A) hH

/-- An injection of `Fin A` into the partitions of `Hof A`. -/
noncomputable def emb (h2 : S_R108_2) (A : ℕ) : Fin A → (Hof h2 A).Partition :=
  fun i => (Fintype.equivFin _).symm (Fin.castLE (Hof_spec h2 A).2 i)

lemma emb_injective (h2 : S_R108_2) (A : ℕ) : Function.Injective (emb h2 A) := by
  intro i i' h
  have := (Fintype.equivFin _).symm.injective h
  exact Fin.castLE_injective _ this

/-- Any `H ≥ 1` with `p(H) ≥ A` bounds `Hof A`. -/
lemma Hof_le (h2 : S_R108_2) (A : ℕ) {H : ℕ} (h1 : 1 ≤ H) (hA : A ≤ Fintype.card H.Partition) :
    Hof h2 A ≤ H := Nat.find_min' (exists_H h2 A) ⟨h1, hA⟩

/-! ## Growth bounds extracted from R108.2 -/

lemma Q_sq_bound {C η : ℝ} (hη : 0 < η)
    (hq : Tendsto (fun h : ℕ => Real.logb 2 (∑ j ∈ Finset.range (h + 1),
      (Fintype.card j.Partition : ℝ)) / Real.sqrt h) atTop (𝓝 C)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ h : ℕ, Real.logb 2 (Qn h) ^ 2 ≤ (C + η) ^ 2 * h + M := by
  obtain ⟨h0, hh0⟩ := eventually_atTop.mp (hq.eventually (Iio_mem_nhds (lt_add_of_pos_right C hη)))
  refine ⟨Real.logb 2 (Qn (max h0 1)) ^ 2, sq_nonneg _, fun h => ?_⟩
  by_cases hh : max h0 1 ≤ h
  · have h1 := hh0 h (le_trans (le_max_left _ _) hh)
    have h1' : (1 : ℝ) ≤ h := by exact_mod_cast le_trans (le_max_right _ _) hh
    have hpos : 0 < Real.sqrt h := Real.sqrt_pos.mpr (by linarith)
    rw [div_lt_iff₀ hpos] at h1
    have e : ((Qn h : ℕ) : ℝ) = ∑ j ∈ Finset.range (h + 1), (Fintype.card j.Partition : ℝ) := by
      push_cast; rfl
    rw [← e] at h1
    have hl0 := logb_nat_nonneg (Qn h)
    have h2 : Real.logb 2 (Qn h) ^ 2 ≤ ((C + η) * Real.sqrt h) ^ 2 := pow_le_pow_left₀ hl0 h1.le 2
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg h)] at h2
    have hM : 0 ≤ Real.logb 2 (Qn (max h0 1)) ^ 2 := sq_nonneg _
    linarith
  · push Not at hh
    have h1 := logb_sq_le (Qn_mono hh.le)
    have : 0 ≤ (C + η) ^ 2 * h := by positivity
    linarith

lemma p_lower {C η : ℝ} (hη : 0 < η)
    (hp : Tendsto (fun h : ℕ => Real.logb 2 (Fintype.card h.Partition) / Real.sqrt h) atTop (𝓝 C)) :
    ∃ h2 : ℕ, ∀ h, h2 ≤ h → (C - η) * Real.sqrt h ≤ Real.logb 2 (Fintype.card h.Partition) := by
  obtain ⟨h0, hh0⟩ := eventually_atTop.mp (hp.eventually (Ioi_mem_nhds (show C - η < C by linarith)))
  refine ⟨max h0 1, fun h hh => ?_⟩
  have h1 := hh0 h (le_trans (le_max_left _ _) hh)
  have h1' : (1 : ℝ) ≤ h := by exact_mod_cast le_trans (le_max_right _ _) hh
  have hpos : 0 < Real.sqrt h := Real.sqrt_pos.mpr (by linarith)
  rw [lt_div_iff₀ hpos] at h1
  exact h1.le

lemma logb_two_pow (m : ℕ) : Real.logb 2 ((2 ^ m : ℕ) : ℝ) = m := by
  rw [Nat.cast_pow, Nat.cast_ofNat, Real.logb_pow, Real.logb_self_eq_one one_lt_two, mul_one]

/-- `Hof (2^m) ≤ (m/(C-η))² + h₂ + 2`, from the lower growth bound. -/
lemma Hof_bound (h2s : S_R108_2) {C η : ℝ} (hηC : η < C) {h2 : ℕ}
    (hlow : ∀ h, h2 ≤ h → (C - η) * Real.sqrt h ≤ Real.logb 2 (Fintype.card h.Partition))
    (m : ℕ) : (Hof h2s (2 ^ m) : ℝ) ≤ ((m : ℝ) / (C - η)) ^ 2 + h2 + 2 := by
  have hc : 0 < C - η := by linarith
  set H := Hof h2s (2 ^ m) with hH
  by_cases hsmall : H ≤ h2 + 1
  · have : (H : ℝ) ≤ h2 + 1 := by exact_mod_cast hsmall
    nlinarith [sq_nonneg ((m : ℝ) / (C - η))]
  · push Not at hsmall
    have hlt : H - 1 < H := by omega
    have hnot := Hof_min h2s (2 ^ m) hlt
    have h1 : 1 ≤ H - 1 := by omega
    have hp : Fintype.card (H - 1).Partition < 2 ^ m := by
      by_contra hcon
      exact hnot ⟨h1, by omega⟩
    have hl := hlow (H - 1) (by omega)
    have hp0 : (0 : ℝ) < Fintype.card (H - 1).Partition := by exact_mod_cast Fintype.card_pos
    have hlt2 : Real.logb 2 (Fintype.card (H - 1).Partition) < m := by
      rw [← logb_two_pow m]
      exact Real.logb_lt_logb one_lt_two hp0 (by exact_mod_cast hp)
    have hsq : Real.sqrt ((H - 1 : ℕ) : ℝ) < (m : ℝ) / (C - η) := by
      rw [lt_div_iff₀ hc]; linarith
    have hsq2 : ((H - 1 : ℕ) : ℝ) < ((m : ℝ) / (C - η)) ^ 2 := by
      have h0 : 0 ≤ Real.sqrt ((H - 1 : ℕ) : ℝ) := Real.sqrt_nonneg _
      have := pow_lt_pow_left₀ hsq h0 (by norm_num : (2 : ℕ) ≠ 0)
      rwa [Real.sq_sqrt (Nat.cast_nonneg _)] at this
    have hcast : ((H - 1 : ℕ) : ℝ) = (H : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]; simp
    rw [hcast] at hsq2
    have : (0 : ℝ) ≤ h2 := Nat.cast_nonneg _
    linarith

/-! ## The expansion at scale `j` -/

/-- Number of pieces at scale `j`. -/
noncomputable def Kf (h2 : S_R108_2) (α β j : ℕ) : ℕ :=
  2 * (Hof h2 (2 ^ (α * j)) + Hof h2 (2 ^ (β * j))) + 1

lemma R108_1_at (h1 : S_R108_1) (h2 : S_R108_2) (α β j : ℕ) :
    ∃ B : Fin (Kf h2 α β j) → (Hof h2 (2 ^ (α * j))).Partition → (Hof h2 (2 ^ (β * j))).Partition →
        (Hof h2 (2 ^ (β * j))).Partition → (Hof h2 (2 ^ (α * j))).Partition → ℂ,
      (∀ z x y w, ∑ k, B k z x y w = if z = w ∧ x = y then 1 else 0) ∧
      ∀ k : Fin (Kf h2 α β j),
        (Matrix.of fun (zx : (Hof h2 (2 ^ (α * j))).Partition × (Hof h2 (2 ^ (β * j))).Partition)
            (yw : (Hof h2 (2 ^ (β * j))).Partition × (Hof h2 (2 ^ (α * j))).Partition) =>
            B k zx.1 zx.2 yw.1 yw.2).rank ≤ Qn k ∧
        (Matrix.of fun (zy : (Hof h2 (2 ^ (α * j))).Partition × (Hof h2 (2 ^ (β * j))).Partition)
            (xw : (Hof h2 (2 ^ (β * j))).Partition × (Hof h2 (2 ^ (α * j))).Partition) =>
            B k zy.1 xw.1 zy.2 xw.2).rank ≤
          Qn (2 * (Hof h2 (2 ^ (α * j)) + Hof h2 (2 ^ (β * j))) - k) :=
  h1 _ _ (Hof_spec h2 _).1 (Hof_spec h2 _).1

/-- The pieces of R108.1 at the least sizes `H, E` with `p(H) ≥ 2^(αj)`, `p(E) ≥ 2^(βj)`. -/
noncomputable def Bpc (h1 : S_R108_1) (h2 : S_R108_2) (α β j : ℕ) :=
  Classical.choose (R108_1_at h1 h2 α β j)

/-- The pieces restricted to `2^(αj)` and `2^(βj)` indices. -/
noncomputable def Bf (h1 : S_R108_1) (h2 : S_R108_2) (α β j : ℕ) :
    Fin (Kf h2 α β j) → Fin (2 ^ (α * j)) → Fin (2 ^ (β * j)) → Fin (2 ^ (β * j)) →
      Fin (2 ^ (α * j)) → ℂ :=
  fun k z x y w => Bpc h1 h2 α β j k (emb h2 _ z) (emb h2 _ x) (emb h2 _ y) (emb h2 _ w)

lemma Bf_sum (h1 : S_R108_1) (h2 : S_R108_2) (α β j : ℕ) (z : Fin (2 ^ (α * j)))
    (x y : Fin (2 ^ (β * j))) (w : Fin (2 ^ (α * j))) :
    ∑ k, Bf h1 h2 α β j k z x y w = if z = w ∧ x = y then 1 else 0 := by
  have hs := (Classical.choose_spec (R108_1_at h1 h2 α β j)).1
    (emb h2 _ z) (emb h2 _ x) (emb h2 _ y) (emb h2 _ w)
  simp only [Bf, Bpc]
  rw [hs]
  simp only [(emb_injective h2 _).eq_iff]

lemma Bf_rank_row (h1 : S_R108_1) (h2 : S_R108_2) (α β j : ℕ) (k : Fin (Kf h2 α β j)) :
    (Matrix.of fun (zx : Fin (2 ^ (α * j)) × Fin (2 ^ (β * j)))
        (yw : Fin (2 ^ (β * j)) × Fin (2 ^ (α * j))) =>
        Bf h1 h2 α β j k zx.1 zx.2 yw.1 yw.2).rank ≤ Qn k := by
  have hr := ((Classical.choose_spec (R108_1_at h1 h2 α β j)).2 k).1
  refine le_trans ?_ hr
  have e : (Matrix.of fun (zx : Fin (2 ^ (α * j)) × Fin (2 ^ (β * j)))
        (yw : Fin (2 ^ (β * j)) × Fin (2 ^ (α * j))) =>
        Bf h1 h2 α β j k zx.1 zx.2 yw.1 yw.2) =
      (Matrix.of fun (zx : (Hof h2 (2 ^ (α * j))).Partition × (Hof h2 (2 ^ (β * j))).Partition)
            (yw : (Hof h2 (2 ^ (β * j))).Partition × (Hof h2 (2 ^ (α * j))).Partition) =>
            Bpc h1 h2 α β j k zx.1 zx.2 yw.1 yw.2).submatrix
        (fun zx => (emb h2 _ zx.1, emb h2 _ zx.2)) (fun yw => (emb h2 _ yw.1, emb h2 _ yw.2)) := by
    ext zx yw; rfl
  rw [e]
  exact Matrix.rank_submatrix_le _ _ _

lemma Bf_rank_col (h1 : S_R108_1) (h2 : S_R108_2) (α β j : ℕ) (k : Fin (Kf h2 α β j)) :
    (Matrix.of fun (zy : Fin (2 ^ (α * j)) × Fin (2 ^ (β * j)))
        (xw : Fin (2 ^ (β * j)) × Fin (2 ^ (α * j))) =>
        Bf h1 h2 α β j k zy.1 xw.1 zy.2 xw.2).rank ≤
      Qn (2 * (Hof h2 (2 ^ (α * j)) + Hof h2 (2 ^ (β * j))) - k) := by
  have hr := ((Classical.choose_spec (R108_1_at h1 h2 α β j)).2 k).2
  refine le_trans ?_ hr
  have e : (Matrix.of fun (zy : Fin (2 ^ (α * j)) × Fin (2 ^ (β * j)))
        (xw : Fin (2 ^ (β * j)) × Fin (2 ^ (α * j))) =>
        Bf h1 h2 α β j k zy.1 xw.1 zy.2 xw.2) =
      (Matrix.of fun (zy : (Hof h2 (2 ^ (α * j))).Partition × (Hof h2 (2 ^ (β * j))).Partition)
            (xw : (Hof h2 (2 ^ (β * j))).Partition × (Hof h2 (2 ^ (α * j))).Partition) =>
            Bpc h1 h2 α β j k zy.1 xw.1 zy.2 xw.2).submatrix
        (fun zy => (emb h2 _ zy.1, emb h2 _ zy.2)) (fun xw => (emb h2 _ xw.1, emb h2 _ xw.2)) := by
    ext zy xw; rfl
  rw [e]
  exact Matrix.rank_submatrix_le _ _ _

/-! ## The two estimates of R108.3 -/

lemma Kf_bound (h2 : S_R108_2) (α β q : ℕ) (hq : 0 < q) :
    ∃ C' : ℝ, ∀ j : ℕ, (Kf h2 α β j : ℝ) ≤ C' * ((q * j : ℕ) + 1 : ℝ) ^ 2 := by
  obtain ⟨C, hC, hp, -⟩ := id h2
  have hη : 0 < C / 2 := half_pos hC
  obtain ⟨h2', hlow⟩ := p_lower hη hp
  have hηC : C / 2 < C := half_lt_self hC
  set A' : ℝ := 2 * ((2 / C) ^ 2 * ((α : ℝ) ^ 2 + (β : ℝ) ^ 2)) with hA'
  set B' : ℝ := 4 * (h2' : ℝ) + 9 with hB'
  have hA'0 : 0 ≤ A' := by positivity
  have hB'0 : 0 ≤ B' := by positivity
  refine ⟨A' + B', fun j => ?_⟩
  have hH := Hof_bound h2 hηC hlow (α * j)
  have hE := Hof_bound h2 hηC hlow (β * j)
  have e1 : C - C / 2 = C / 2 := by ring
  rw [e1] at hH hE
  have e2 : ∀ m : ℕ, ((m : ℝ) / (C / 2)) ^ 2 = (2 / C) ^ 2 * (m : ℝ) ^ 2 := by
    intro m; field_simp
  rw [e2] at hH hE
  have hK : (Kf h2 α β j : ℝ) ≤ A' * (j : ℝ) ^ 2 + B' := by
    unfold Kf
    push_cast at hH hE ⊢
    rw [hA', hB']
    nlinarith
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hj : (j : ℝ) ^ 2 ≤ ((q * j : ℕ) + 1 : ℝ) ^ 2 := by
    push_cast
    have h0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have : (j : ℝ) ≤ (q : ℝ) * j + 1 := by nlinarith
    exact pow_le_pow_left₀ h0 this 2
  have h1 : (1 : ℝ) ≤ ((q * j : ℕ) + 1 : ℝ) ^ 2 := by
    have h0 : (1 : ℝ) ≤ ((q * j : ℕ) + 1 : ℝ) := by
      have : (0 : ℝ) ≤ ((q * j : ℕ) : ℝ) := Nat.cast_nonneg _
      linarith
    nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hj hA'0, mul_le_mul_of_nonneg_left h1 hB'0]

lemma ratio_bound {C x : ℝ} (hC : 0 < C) (hx0 : 0 < x) (hx12 : x ≤ 1 / 2) :
    ((C + C * x) / (C - C * x)) ^ 2 ≤ 1 + 16 * x := by
  have hd : 0 < C - C * x := by nlinarith
  have h1 : (C + C * x) / (C - C * x) ≤ 1 + 4 * x := by
    rw [div_le_iff₀ hd]
    have : C * x * x ≤ C * x * (1 / 2) := mul_le_mul_of_nonneg_left hx12 (by positivity)
    nlinarith
  have h0 : 0 ≤ (C + C * x) / (C - C * x) := div_nonneg (by nlinarith) hd.le
  calc ((C + C * x) / (C - C * x)) ^ 2 ≤ (1 + 4 * x) ^ 2 := pow_le_pow_left₀ h0 h1 2
    _ ≤ 1 + 16 * x := by nlinarith

lemma sum_real {a2 b2 c k M H E X h2 θ cd : ℝ} (hcd : 0 < cd)
    (hθ : θ = (c / cd) ^ 2)
    (s1 : a2 ≤ c ^ 2 * k + M) (s2 : b2 ≤ c ^ 2 * (2 * (H + E) - k) + M)
    (hHE : H + E ≤ X / cd ^ 2 + 2 * h2 + 4) :
    a2 + b2 ≤ 2 * θ * X + (4 * c ^ 2 * (h2 + 2) + 2 * M) := by
  have hc2 : 0 ≤ c ^ 2 := sq_nonneg c
  have h3 : c ^ 2 * (H + E) ≤ θ * X + c ^ 2 * (2 * h2 + 4) := by
    calc c ^ 2 * (H + E) ≤ c ^ 2 * (X / cd ^ 2 + 2 * h2 + 4) := mul_le_mul_of_nonneg_left hHE hc2
      _ = θ * X + c ^ 2 * (2 * h2 + 4) := by rw [hθ, div_pow]; field_simp; ring
  nlinarith

lemma final_real {A2 S ε θ x K0 q j α2 : ℝ} (hq : 0 < q) (hj : 1 ≤ j) (hε : 0 < ε)
    (hSq : S * q ^ 2 = 2 * α2) (hα2 : 0 ≤ α2) (hS0 : 0 ≤ S)
    (hθ : θ ≤ 1 + 16 * x) (hxε : x ≤ ε / (32 * (S + 1)))
    (hsum : A2 ≤ 2 * θ * α2 * j ^ 2 + K0) (hK0 : 0 ≤ K0)
    (hj0 : 2 * K0 / (ε * q ^ 2) ≤ j) :
    A2 ≤ (S + ε) * (q * j) ^ 2 := by
  have hθ1 : θ - 1 ≤ ε / (2 * (S + 1)) := by
    have e : 16 * (ε / (32 * (S + 1))) = ε / (2 * (S + 1)) := by field_simp; ring
    nlinarith [mul_le_mul_of_nonneg_left hxε (by norm_num : (0 : ℝ) ≤ 16)]
  have hfrac : α2 * (ε / (2 * (S + 1))) ≤ ε / 4 * q ^ 2 := by
    rw [mul_div_assoc', div_le_iff₀ (by positivity)]
    nlinarith [mul_pos hε (pow_pos hq 2)]
  have hj2 : 1 ≤ j ^ 2 := by nlinarith
  have hjj : j ≤ j ^ 2 := by nlinarith
  have hK : K0 ≤ ε / 2 * q ^ 2 * j ^ 2 := by
    rw [div_le_iff₀ (by positivity)] at hj0
    nlinarith
  have hθX : 2 * θ * α2 * j ^ 2 ≤ 2 * α2 * j ^ 2 + ε / 2 * q ^ 2 * j ^ 2 := by
    have h1 : 2 * α2 * j ^ 2 * (θ - 1) ≤ 2 * α2 * j ^ 2 * (ε / (2 * (S + 1))) :=
      mul_le_mul_of_nonneg_left hθ1 (by positivity)
    have h2 : 2 * j ^ 2 * (α2 * (ε / (2 * (S + 1)))) ≤ 2 * j ^ 2 * (ε / 4 * q ^ 2) :=
      mul_le_mul_of_nonneg_left hfrac (by positivity)
    nlinarith
  have e : (S + ε) * (q * j) ^ 2 = S * q ^ 2 * j ^ 2 + ε * q ^ 2 * j ^ 2 := by ring
  rw [e, hSq]
  linarith

lemma circle (h1 : S_R108_1) (h2 : S_R108_2) (α β q : ℕ) (hq : 0 < q) {ε : ℝ} (hε : 0 < ε) :
    ∃ j₀ : ℕ, ∀ j : ℕ, j₀ ≤ j → ∀ k : Fin (Kf h2 α β j),
      (Real.logb 2 (Matrix.of fun (zx : Fin (2 ^ (α * j)) × Fin (2 ^ (β * j)))
            (yw : Fin (2 ^ (β * j)) × Fin (2 ^ (α * j))) =>
            Bf h1 h2 α β j k zx.1 zx.2 yw.1 yw.2).rank / (q * j : ℕ)) ^ 2 +
      (Real.logb 2 (Matrix.of fun (zy : Fin (2 ^ (α * j)) × Fin (2 ^ (β * j)))
            (xw : Fin (2 ^ (β * j)) × Fin (2 ^ (α * j))) =>
            Bf h1 h2 α β j k zy.1 xw.1 zy.2 xw.2).rank / (q * j : ℕ)) ^ 2
        ≤ 2 * (((α : ℝ) / q) ^ 2 + ((β : ℝ) / q) ^ 2) + ε := by
  obtain ⟨C, hC, hp, hqT⟩ := id h2
  set S : ℝ := 2 * (((α : ℝ) / q) ^ 2 + ((β : ℝ) / q) ^ 2) with hS
  have hS0 : 0 ≤ S := by positivity
  set x : ℝ := min (1 / 2) (ε / (32 * (S + 1))) with hx
  have hx0 : 0 < x := lt_min (by norm_num) (by positivity)
  have hx12 : x ≤ 1 / 2 := min_le_left _ _
  have hxε : x ≤ ε / (32 * (S + 1)) := min_le_right _ _
  set η : ℝ := C * x with hη
  have hη0 : 0 < η := by positivity
  have hηC : η < C := by nlinarith
  obtain ⟨M, hM0, hM⟩ := Q_sq_bound hη0 hqT
  obtain ⟨h2', hlow⟩ := p_lower hη0 hp
  set K0 : ℝ := 4 * (C + η) ^ 2 * ((h2' : ℝ) + 2) + 2 * M with hK0
  have hK00 : 0 ≤ K0 := by positivity
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  obtain ⟨j0, hj0⟩ := exists_nat_ge (2 * K0 / (ε * (q : ℝ) ^ 2))
  refine ⟨j0 + 1, fun j hj k => ?_⟩
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast (show 1 ≤ j by omega)
  have hjj0 : (j0 : ℝ) + 1 ≤ j := by exact_mod_cast hj
  set H := Hof h2 (2 ^ (α * j)) with hHdef
  set E := Hof h2 (2 ^ (β * j)) with hEdef
  have hk : (k : ℕ) ≤ 2 * (H + E) := Nat.lt_succ_iff.mp k.2
  set a := Real.logb 2 ((Matrix.of fun (zx : Fin (2 ^ (α * j)) × Fin (2 ^ (β * j)))
            (yw : Fin (2 ^ (β * j)) × Fin (2 ^ (α * j))) =>
            Bf h1 h2 α β j k zx.1 zx.2 yw.1 yw.2).rank : ℝ) with ha
  set b := Real.logb 2 ((Matrix.of fun (zy : Fin (2 ^ (α * j)) × Fin (2 ^ (β * j)))
            (xw : Fin (2 ^ (β * j)) × Fin (2 ^ (α * j))) =>
            Bf h1 h2 α β j k zy.1 xw.1 zy.2 xw.2).rank : ℝ) with hb
  have s1 : a ^ 2 ≤ (C + η) ^ 2 * (k : ℕ) + M :=
    (logb_sq_le (Bf_rank_row h1 h2 α β j k)).trans (hM k)
  have s2 : b ^ 2 ≤ (C + η) ^ 2 * ((2 * (H + E) - (k : ℕ) : ℕ) : ℝ) + M :=
    (logb_sq_le (Bf_rank_col h1 h2 α β j k)).trans (hM _)
  have hDk : ((2 * (H + E) - (k : ℕ) : ℕ) : ℝ) = 2 * ((H : ℝ) + E) - (k : ℕ) := by
    rw [Nat.cast_sub hk]; push_cast; ring
  rw [hDk] at s2
  have hHb := Hof_bound h2 hηC hlow (α * j)
  have hEb := Hof_bound h2 hηC hlow (β * j)
  rw [← hHdef] at hHb
  rw [← hEdef] at hEb
  have hcη : 0 < C - η := by linarith
  set θ := ((C + η) / (C - η)) ^ 2 with hθ
  have hθb : θ ≤ 1 + 16 * x := ratio_bound hC hx0 hx12
  -- total bound
  have hHE : (H : ℝ) + E ≤ ((α : ℝ) ^ 2 + (β : ℝ) ^ 2) * (j : ℝ) ^ 2 / (C - η) ^ 2 +
      2 * (h2' : ℝ) + 4 := by
    have e : ∀ m : ℕ, ((m : ℝ) / (C - η)) ^ 2 = (m : ℝ) ^ 2 / (C - η) ^ 2 := fun m => by
      rw [div_pow]
    rw [e] at hHb hEb
    have hcast : ((α : ℝ) ^ 2 + (β : ℝ) ^ 2) * (j : ℝ) ^ 2 / (C - η) ^ 2 =
        ((α * j : ℕ) : ℝ) ^ 2 / (C - η) ^ 2 + ((β * j : ℕ) : ℝ) ^ 2 / (C - η) ^ 2 := by
      push_cast; ring
    rw [hcast]; linarith
  have hsum := sum_real (a2 := a ^ 2) (b2 := b ^ 2) hcη hθ s1 s2 hHE
  have hd : (0 : ℝ) < ((q * j : ℕ) : ℝ) := by
    have : (1 : ℝ) ≤ ((q * j : ℕ) : ℝ) := by
      push_cast; nlinarith [(by exact_mod_cast hq : (1 : ℝ) ≤ q)]
    linarith
  have hdq : ((q * j : ℕ) : ℝ) = (q : ℝ) * j := by push_cast; ring
  rw [div_pow, div_pow, ← add_div, div_le_iff₀ (pow_pos hd 2), hdq]
  have hSq : S * (q : ℝ) ^ 2 = 2 * ((α : ℝ) ^ 2 + (β : ℝ) ^ 2) := by rw [hS]; field_simp
  exact final_real hq' hj1 hε hSq (by positivity) hS0 hθb hxε (by rw [← hK0] at hsum; linarith)
    hK00 (by linarith)

/-- **R108.1 ∧ R108.2 ⟹ R108.3** (the rectangular crossing estimate). -/
theorem rect_of (h1 : S_R108_1) (h2 : S_R108_2) : S_R108_3 := by
  intro α β q _ _ hq
  refine ⟨Kf h2 α β, Bf h1 h2 α β, Kf_bound h2 α β q hq,
    fun j z x y w => Bf_sum h1 h2 α β j z x y w, ?_⟩
  intro ε hε
  obtain ⟨j₀, hj₀⟩ := circle h1 h2 α β q hq hε
  exact ⟨j₀, fun j hj k _ => hj₀ j hj k⟩

end OM.NNN30.Rect

