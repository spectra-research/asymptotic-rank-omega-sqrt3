import Lib.OM.NNN30.Crossing.Kernel

/-! # The `0`–`1` pairing of partition states is invertible

`G⁺(λ, μ)` (the Wick sum of `λ` at `0` against `μ` at `1` with the kernel
`kc b c = Σ_j C(b, j) j C(c, j)`) is the Gram matrix of the polynomials
`A_λ = Π_{b ∈ λ} Σ_{1 ≤ j ≤ b} C(b, j) X_j` for the weighted pairing
`⟨X^ν, X^ν'⟩ = [ν = ν'] Π_j j^{ν_j} ν_j!`. -/

namespace OM.NNN30.Crossing.Gram

open MvPolynomial

abbrev Poly := MvPolynomial ℕ ℝ

/-- The factor of the variable `j` with exponent `k`. -/
noncomputable def wtf (j k : ℕ) : ℝ := (j : ℝ) ^ k * (k.factorial : ℝ)

/-- The weight `Π_j j^{ν_j} ν_j!` of a monomial. -/
noncomputable def wt (ν : ℕ →₀ ℕ) : ℝ := ν.prod wtf

theorem wt_nonneg (ν : ℕ →₀ ℕ) : 0 ≤ wt ν := by
  unfold wt Finsupp.prod
  apply Finset.prod_nonneg
  intro j _
  unfold wtf
  positivity

theorem wt_pos (ν : ℕ →₀ ℕ) (h : 0 ∉ ν.support) : 0 < wt ν := by
  unfold wt Finsupp.prod
  apply Finset.prod_pos
  intro j hj
  have hj0 : j ≠ 0 := fun h' => h (h' ▸ hj)
  unfold wtf
  have : (0 : ℝ) < j := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hj0)
  positivity

theorem wt_add_single (ν : ℕ →₀ ℕ) (j : ℕ) :
    wt (ν + Finsupp.single j 1) = wt ν * j * (ν j + 1) := by
  classical
  set s := ν.support ∪ {j}
  have h1 : (ν + Finsupp.single j 1).support ⊆ s := by
    intro i hi
    rw [Finsupp.mem_support_iff, Finsupp.add_apply] at hi
    by_cases hij : i = j
    · simp [s, hij]
    · simp only [Finsupp.single_apply, if_neg (Ne.symm hij), add_zero] at hi
      simp [s, Finsupp.mem_support_iff, hi]
  have h2 : ν.support ⊆ s := Finset.subset_union_left
  have hg : ∀ i ∈ s, wtf i 0 = 1 := by simp [wtf]
  unfold wt
  rw [Finsupp.prod_of_support_subset _ h1 _ hg, Finsupp.prod_of_support_subset _ h2 _ hg]
  have hjs : j ∈ s := by simp [s]
  rw [← Finset.mul_prod_erase s _ hjs, ← Finset.mul_prod_erase s _ hjs]
  have hrest : ∏ x ∈ s.erase j, wtf x ((ν + Finsupp.single j 1 : ℕ →₀ ℕ) x) =
      ∏ x ∈ s.erase j, wtf x (ν x) := by
    apply Finset.prod_congr rfl
    intro x hx
    have hxj : x ≠ j := Finset.ne_of_mem_erase hx
    rw [Finsupp.add_apply, Finsupp.single_apply, if_neg (Ne.symm hxj), add_zero]
  rw [hrest]
  simp only [wtf, Finsupp.add_apply, Finsupp.single_eq_same, Nat.factorial_succ, pow_succ,
    Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  ring

/-- The weighted pairing. -/
noncomputable def ip (F G : Poly) : ℝ := ∑ ν ∈ F.support ∪ G.support, F.coeff ν * G.coeff ν * wt ν

theorem ip_eq (F G : Poly) (s : Finset (ℕ →₀ ℕ)) (hs : F.support ⊆ s) :
    ip F G = ∑ ν ∈ s, F.coeff ν * G.coeff ν * wt ν := by
  classical
  have key : ∀ t : Finset (ℕ →₀ ℕ), F.support ⊆ t →
      ∑ ν ∈ t, F.coeff ν * G.coeff ν * wt ν = ∑ ν ∈ t ∪ s ∪ (F.support ∪ G.support),
        F.coeff ν * G.coeff ν * wt ν := by
    intro t ht
    apply Finset.sum_subset (fun x hx => by simp [hx])
    intro x _ hx
    have : x ∉ F.support := fun h => hx (ht h)
    rw [MvPolynomial.notMem_support_iff.mp this]; ring
  unfold ip
  rw [key _ Finset.subset_union_left, key _ hs]
  congr 1
  ext x; simp; tauto

theorem ip_comm (F G : Poly) : ip F G = ip G F := by
  unfold ip; rw [Finset.union_comm]; apply Finset.sum_congr rfl; intro ν _; ring

theorem ip_add_left (F F' G : Poly) : ip (F + F') G = ip F G + ip F' G := by
  classical
  set s := F.support ∪ F'.support
  rw [ip_eq (F + F') G s MvPolynomial.support_add, ip_eq F G s Finset.subset_union_left,
    ip_eq F' G s Finset.subset_union_right, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro ν _; rw [MvPolynomial.coeff_add]; ring

theorem ip_smul_left (c : ℝ) (F G : Poly) : ip (c • F) G = c * ip F G := by
  rw [ip_eq (c • F) G F.support MvPolynomial.support_smul, ip_eq F G F.support le_rfl,
    Finset.mul_sum]
  apply Finset.sum_congr rfl; intro ν _; rw [coeff_smul, smul_eq_mul]; ring

theorem ip_add_right (F G G' : Poly) : ip F (G + G') = ip F G + ip F G' := by
  rw [ip_comm, ip_add_left, ip_comm G, ip_comm G']

theorem ip_smul_right (c : ℝ) (F G : Poly) : ip F (c • G) = c * ip F G := by
  rw [ip_comm, ip_smul_left, ip_comm]

theorem ip_zero_left (G : Poly) : ip 0 G = 0 := by
  have := ip_smul_left 0 0 G; simpa using this

theorem ip_zero_right (F : Poly) : ip F 0 = 0 := by rw [ip_comm, ip_zero_left]

theorem ip_sum_left {ι : Type*} (t : Finset ι) (F : ι → Poly) (G : Poly) :
    ip (∑ i ∈ t, F i) G = ∑ i ∈ t, ip (F i) G := by
  classical
  induction t using Finset.induction_on with
  | empty => simp [ip_zero_left]
  | insert i t hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, ip_add_left, ih]

theorem ip_msum_right (F : Poly) (s : Multiset Poly) :
    ip F s.sum = (s.map (ip F)).sum := by
  induction s using Multiset.induction_on with
  | empty => simp [ip_zero_right]
  | cons G s ih => rw [Multiset.sum_cons, ip_add_right, ih, Multiset.map_cons, Multiset.sum_cons]

theorem ip_monomial (a b : ℕ →₀ ℕ) (x y : ℝ) :
    ip (monomial a x) (monomial b y) = if a = b then x * y * wt a else 0 := by
  classical
  rw [ip_eq _ _ {a} MvPolynomial.support_monomial_subset, Finset.sum_singleton, coeff_monomial,
    coeff_monomial]
  by_cases h : a = b
  · subst h; simp
  · simp [h, Ne.symm h]

/-- Multiplication by `X_j` is adjoint to `j ∂_j`. -/
theorem ip_X_mul (j : ℕ) (F G : Poly) : ip (X j * F) G = (j : ℝ) * ip F (pderiv j G) := by
  classical
  induction F using MvPolynomial.induction_on' with
  | monomial a x =>
    induction G using MvPolynomial.induction_on' with
    | monomial b y =>
      rw [show (X j : Poly) = monomial (Finsupp.single j 1) 1 from rfl, monomial_mul_monomial,
        one_mul, pderiv_monomial, ip_monomial, ip_monomial]
      by_cases hb : Finsupp.single j 1 + a = b
      · subst hb
        have h1 : Finsupp.single j 1 + a - Finsupp.single j 1 = a := by
          ext i; simp [Finsupp.single_apply]
        rw [if_pos rfl, h1, if_pos rfl, add_comm (Finsupp.single j 1) a, wt_add_single]
        simp [Finsupp.single_apply]
        ring
      · rw [if_neg hb]
        by_cases ha : a = b - Finsupp.single j 1
        · rw [if_pos ha]
          have hbj : b j = 0 := by
            by_contra hbj
            apply hb
            ext i
            have := congrArg (fun f => f i) ha
            simp only [Finsupp.coe_tsub, Pi.sub_apply] at this
            by_cases hij : i = j
            · subst hij; simp [Finsupp.single_apply] at this ⊢; omega
            · simp [Finsupp.single_apply, Ne.symm hij] at this ⊢; omega
          simp [hbj]
        · rw [if_neg ha, mul_zero]
    | add G G' hG hG' =>
      rw [map_add, ip_add_right, ip_add_right, hG, hG', mul_add]
  | add F F' hF hF' =>
    rw [mul_add, ip_add_left, ip_add_left, hF, hF', mul_add]

theorem ip_one_left (G : Poly) : ip 1 G = G.coeff 0 := by
  classical
  rw [show (1 : Poly) = monomial 0 1 from rfl, ip_eq _ _ {0} MvPolynomial.support_monomial_subset,
    Finset.sum_singleton, coeff_monomial, if_pos rfl]
  simp [wt]

/-- `L_c = Σ_{1 ≤ j ≤ c} C(c, j) X_j`. -/
noncomputable def Lc (c : ℕ) : Poly := ∑ j ∈ Finset.Icc 1 c, C (c.choose j : ℝ) * X j

/-- `A_μ = Π_{c ∈ μ} L_c`. -/
noncomputable def Am (μ : Multiset ℕ) : Poly := (μ.map Lc).prod

/-- The coefficient of `X_j` in `L_c`. -/
noncomputable def cj (c j : ℕ) : ℝ := if 1 ≤ j ∧ j ≤ c then (c.choose j : ℝ) else 0

theorem pderiv_Lc (c j : ℕ) : pderiv j (Lc c) = C (cj c j) := by
  classical
  unfold Lc cj
  rw [map_sum]
  have : ∀ i ∈ Finset.Icc 1 c, pderiv j (C (c.choose i : ℝ) * (X i : Poly)) =
      if j = i then C (c.choose i : ℝ) else 0 := by
    intro i _
    rw [pderiv_C_mul, pderiv_X]
    by_cases h : i = j
    · subst h; simp
    · simp [Pi.single_apply, h, Ne.symm h]
  rw [Finset.sum_congr rfl this, Finset.sum_ite_eq]
  by_cases h : j ∈ Finset.Icc 1 c
  · rw [if_pos h, if_pos (Finset.mem_Icc.mp h)]
  · rw [if_neg h, if_neg (fun h' => h (Finset.mem_Icc.mpr h')), map_zero]

theorem constantCoeff_Lc (c : ℕ) : constantCoeff (Lc c) = 0 := by
  unfold Lc
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro i _
  rw [map_mul, constantCoeff_X, mul_zero]

theorem Am_cons (c : ℕ) (μ : Multiset ℕ) : Am (c ::ₘ μ) = Lc c * Am μ := by
  simp [Am]

theorem pderiv_Am (j : ℕ) (μ : Multiset ℕ) :
    pderiv j (Am μ) = (μ.map fun c => C (cj c j) * Am (μ.erase c)).sum := by
  classical
  induction μ using Multiset.induction_on with
  | empty => simp [Am]
  | cons c μ ih =>
    rw [Am_cons, Derivation.leibniz, ih, pderiv_Lc, Multiset.map_cons, Multiset.sum_cons,
      Multiset.erase_cons_head, smul_eq_mul, smul_eq_mul, ← Multiset.sum_map_mul_left]
    rw [add_comm]
    congr 1
    · ring
    · apply congrArg Multiset.sum
      apply Multiset.map_congr rfl
      intro c' hc'
      rw [Multiset.erase_cons_tail_of_mem hc', Am_cons]
      ring

/-- The real kernel `Σ_j C(b, j) j C(c, j)`. -/
noncomputable def kcR (b c : ℕ) : ℝ := ∑ j ∈ Finset.range (b + c + 1), cj b j * j * cj c j

theorem kcR_symm (b c : ℕ) : kcR b c = kcR c b := by
  unfold kcR; rw [add_comm b c]; apply Finset.sum_congr rfl; intro j _; ring

theorem kcR_eq (b c : ℕ) : kcR b c = ∑ j ∈ Finset.Icc 1 b, (b.choose j : ℝ) * j * cj c j := by
  unfold kcR
  rw [← Finset.sum_subset (s₁ := Finset.Icc 1 b) (s₂ := Finset.range (b + c + 1))
    (fun x hx => by simp at hx ⊢; omega)]
  · apply Finset.sum_congr rfl
    intro j hj
    rw [cj, if_pos (Finset.mem_Icc.mp hj)]
  · intro j _ hj
    rw [cj, if_neg (fun h => hj (Finset.mem_Icc.mpr h))]; ring

/-- The `0`–`1` real kernel on labels (`p` = the point `0`, `q` = the point `1`). -/
noncomputable def gramK : Pt × ℕ → Pt × ℕ → ℝ
  | (.p, b), (.q, c) | (.q, c), (.p, b) => kcR b c
  | _, _ => 0

theorem gramK_symm (u v : Pt × ℕ) : gramK u v = gramK v u := by
  rcases u with ⟨_ | _ | _ | _ | _, a⟩ <;> rcases v with ⟨_ | _ | _ | _ | _, b⟩ <;> rfl

theorem finset_multiset_sum_comm {ι κ : Type*} (t : Finset ι) (s : Multiset κ) (f : ι → κ → ℝ) :
    ∑ i ∈ t, (s.map (f i)).sum = (s.map fun k => ∑ i ∈ t, f i k).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons k s ih => simp [Finset.sum_add_distrib, ih]

/-- The Gram identity: the `0`–`1` Wick pairing is the weighted pairing of `A_λ` and `A_μ`. -/
theorem gram_wick (lam : Multiset ℕ) : ∀ μ : Multiset ℕ,
    wickM gramK (lam.map (fun b => (Pt.p, b)) + μ.map (fun c => (Pt.q, c))) =
      ip (Am lam) (Am μ) := by
  classical
  induction lam using Multiset.induction_on with
  | empty =>
    intro μ
    rw [Multiset.map_zero, zero_add]
    rw [show Am 0 = 1 by simp [Am], ip_one_left, ← constantCoeff_eq]
    induction μ using Multiset.induction_on with
    | empty => simp [wickM_zero, Am]
    | cons c μ _ =>
      rw [Multiset.map_cons, wickM_cons_eq_zero gramK_symm]
      · rw [Am_cons, map_mul, constantCoeff_Lc, zero_mul]
      · intro x hx
        obtain ⟨d, _, rfl⟩ := Multiset.mem_map.mp hx
        rfl
  | cons b lam ih =>
    intro μ
    rw [Multiset.map_cons, Multiset.cons_add, wickM_cons gramK_symm, Multiset.map_add,
      Multiset.sum_add]
    have h0 : ((lam.map fun b => (Pt.p, b)).map fun x => gramK (Pt.p, b) x *
        wickM gramK (((lam.map fun b => (Pt.p, b)) + μ.map (fun c => (Pt.q, c))).erase x)).sum = 0 := by
      apply Multiset.sum_eq_zero
      intro y hy
      obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.mp hy
      obtain ⟨d, _, rfl⟩ := Multiset.mem_map.mp hx
      simp [gramK]
    rw [h0, zero_add, Multiset.map_map]
    -- the right-hand side
    rw [Am_cons, Lc, Finset.sum_mul, ip_sum_left]
    have hR : ∀ j ∈ Finset.Icc 1 b, ip (C (b.choose j : ℝ) * X j * Am lam) (Am μ) =
        (μ.map fun c => (b.choose j : ℝ) * j * cj c j * ip (Am lam) (Am (μ.erase c))).sum := by
      intro j _
      rw [mul_assoc, C_mul', ip_smul_left, ip_X_mul, pderiv_Am, ip_msum_right, Multiset.map_map,
        ← Multiset.sum_map_mul_left, ← Multiset.sum_map_mul_left]
      apply congrArg Multiset.sum
      apply Multiset.map_congr rfl
      intro c _
      simp only [Function.comp]
      rw [C_mul', ip_smul_right]
      ring
    rw [Finset.sum_congr rfl hR, finset_multiset_sum_comm]
    apply congrArg Multiset.sum
    apply Multiset.map_congr rfl
    intro c hc
    simp only [Function.comp]
    have he : ((lam.map fun b => (Pt.p, b)) + μ.map (fun c => (Pt.q, c))).erase (Pt.q, c) =
        lam.map (fun b => (Pt.p, b)) + (μ.erase c).map (fun c => (Pt.q, c)) := by
      rw [Multiset.erase_add_right_pos _ (Multiset.mem_map_of_mem _ hc),
        Multiset.map_erase _ (fun x y h => by simpa using h)]
    rw [he, ih, ← Finset.sum_mul, ← kcR_eq]
    rfl

/-- The weighted degree `Σ_j j ν_j`. -/
noncomputable def wdeg : (ℕ →₀ ℕ) →+ ℕ := Finsupp.weight (fun i : ℕ => i)

theorem wdeg_single (j : ℕ) : wdeg (Finsupp.single j 1) = j := by
  simp [wdeg, Finsupp.weight_single]

theorem toFinsupp_cons (c : ℕ) (s : Multiset ℕ) :
    Multiset.toFinsupp (c ::ₘ s) = Finsupp.single c 1 + Multiset.toFinsupp s := by
  rw [← Multiset.singleton_add, Multiset.toFinsupp_add, Multiset.toFinsupp_singleton]

theorem wdeg_toFinsupp (s : Multiset ℕ) : wdeg (Multiset.toFinsupp s) = s.sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons c s ih => rw [toFinsupp_cons, map_add, wdeg_single, ih, Multiset.sum_cons]

theorem Lc_mul (c : ℕ) (F : Poly) :
    Lc c * F = ∑ j ∈ Finset.Icc 1 c, C (c.choose j : ℝ) * (X j * F) := by
  rw [Lc, Finset.sum_mul]; apply Finset.sum_congr rfl; intro j _; ring

theorem coeff_Lc_mul (c : ℕ) (F : Poly) (ν : ℕ →₀ ℕ) :
    (Lc c * F).coeff ν = ∑ j ∈ Finset.Icc 1 c,
      (c.choose j : ℝ) * (if j ∈ ν.support then F.coeff (ν - Finsupp.single j 1) else 0) := by
  classical
  rw [Lc_mul, coeff_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [coeff_C_mul, coeff_X_mul']

theorem single_le_of_mem_support {ν : ℕ →₀ ℕ} {j : ℕ} (h : j ∈ ν.support) :
    Finsupp.single j 1 ≤ ν := by
  intro i
  rw [Finsupp.single_apply]
  split_ifs with hij
  · subst hij; exact Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp h)
  · exact Nat.zero_le _

/-- Monomials of `A_s` have weighted degree at most `Σ s`, with equality only for `X^s`. -/
theorem coeff_Am_ne_zero (s : Multiset ℕ) (hs : ∀ a ∈ s, 0 < a) :
    ∀ ν : ℕ →₀ ℕ, (Am s).coeff ν ≠ 0 →
      wdeg ν ≤ s.sum ∧ (wdeg ν = s.sum → ν = Multiset.toFinsupp s) := by
  classical
  induction s using Multiset.induction_on with
  | empty =>
    intro ν hν
    rw [show Am 0 = 1 by simp [Am], MvPolynomial.coeff_one] at hν
    split_ifs at hν with h
    · subst h; simp
    · exact absurd rfl hν
  | cons c s ih =>
    intro ν hν
    have hs' : ∀ a ∈ s, 0 < a := fun a ha => hs a (Multiset.mem_cons_of_mem ha)
    rw [Am_cons, coeff_Lc_mul] at hν
    obtain ⟨j, hj, hjne⟩ : ∃ j ∈ Finset.Icc 1 c, (c.choose j : ℝ) *
        (if j ∈ ν.support then (Am s).coeff (ν - Finsupp.single j 1) else 0) ≠ 0 := by
      by_contra h
      apply hν
      apply Finset.sum_eq_zero
      intro j hj
      by_contra h'
      exact h ⟨j, hj, h'⟩
    have hjs : j ∈ ν.support := by
      by_contra h; rw [if_neg h, mul_zero] at hjne; exact hjne rfl
    rw [if_pos hjs] at hjne
    have hcoef := right_ne_zero_of_mul hjne
    obtain ⟨h1, h2⟩ := ih hs' _ hcoef
    have hsplit : ν = (ν - Finsupp.single j 1) + Finsupp.single j 1 :=
      (tsub_add_cancel_of_le (single_le_of_mem_support hjs)).symm
    have hw : wdeg ν = wdeg (ν - Finsupp.single j 1) + j := by
      conv_lhs => rw [hsplit]
      rw [map_add, wdeg_single]
    have hjc := (Finset.mem_Icc.mp hj).2
    refine ⟨by rw [Multiset.sum_cons]; omega, fun heq => ?_⟩
    rw [Multiset.sum_cons] at heq
    have e1 : j = c := by omega
    have e2 := h2 (by omega)
    rw [hsplit, e2, e1, toFinsupp_cons, add_comm]

theorem coeff_Am_top (s : Multiset ℕ) (hs : ∀ a ∈ s, 0 < a) :
    (Am s).coeff (Multiset.toFinsupp s) = 1 := by
  classical
  induction s using Multiset.induction_on with
  | empty => simp [Am]
  | cons c s ih =>
    have hs' : ∀ a ∈ s, 0 < a := fun a ha => hs a (Multiset.mem_cons_of_mem ha)
    have hc : 0 < c := hs c (Multiset.mem_cons_self c s)
    rw [Am_cons, coeff_Lc_mul, Finset.sum_eq_single c]
    · have hmem : c ∈ (Multiset.toFinsupp (c ::ₘ s)).support := by
        rw [Finsupp.mem_support_iff, Multiset.toFinsupp_apply]; simp
      rw [if_pos hmem, toFinsupp_cons, add_tsub_cancel_left, ih hs']
      simp
    · intro j hj hjc
      split_ifs with hjs
      · have hjlt : j < c := lt_of_le_of_ne (Finset.mem_Icc.mp hj).2 hjc
        have : (Am s).coeff (Multiset.toFinsupp (c ::ₘ s) - Finsupp.single j 1) = 0 := by
          by_contra hne
          have h1 := (coeff_Am_ne_zero s hs' _ hne).1
          have hsplit : Multiset.toFinsupp (c ::ₘ s) =
              (Multiset.toFinsupp (c ::ₘ s) - Finsupp.single j 1) + Finsupp.single j 1 :=
            (tsub_add_cancel_of_le (single_le_of_mem_support hjs)).symm
          have hw : wdeg (Multiset.toFinsupp (c ::ₘ s)) =
              wdeg (Multiset.toFinsupp (c ::ₘ s) - Finsupp.single j 1) + j := by
            conv_lhs => rw [hsplit]
            rw [map_add, wdeg_single]
          rw [wdeg_toFinsupp, Multiset.sum_cons] at hw
          omega
        rw [this, mul_zero]
      · rw [mul_zero]
    · intro h; exact absurd (Finset.mem_Icc.mpr ⟨hc, le_rfl⟩) h

theorem coeff_Am_partition {E : ℕ} (lam mu : E.Partition) :
    (Am lam.parts).coeff (Multiset.toFinsupp mu.parts) = if lam = mu then 1 else 0 := by
  by_cases h : lam = mu
  · subst h; rw [if_pos rfl]; exact coeff_Am_top _ (fun a ha => lam.parts_pos ha)
  · rw [if_neg h]
    by_contra hne
    have h2 := (coeff_Am_ne_zero lam.parts (fun a ha => lam.parts_pos ha) _ hne).2
    rw [wdeg_toFinsupp, mu.parts_sum, lam.parts_sum] at h2
    have h3 := h2 rfl
    apply h
    apply Nat.Partition.ext
    exact (Multiset.toFinsupp.injective h3).symm

theorem ip_sum_right {ι : Type*} (t : Finset ι) (F : Poly) (G : ι → Poly) :
    ip F (∑ i ∈ t, G i) = ∑ i ∈ t, ip F (G i) := by
  rw [ip_comm, ip_sum_left]; apply Finset.sum_congr rfl; intro i _; rw [ip_comm]

/-- The Gram matrix of the `A_λ`, `λ ⊢ E`, is positive definite. -/
theorem gram_posDef (E : ℕ) :
    (Matrix.of fun lam mu : E.Partition => ip (Am lam.parts) (Am mu.parts)).PosDef := by
  classical
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  refine ⟨?_, fun x hx => ?_⟩
  · ext i j
    simp [Matrix.conjTranspose_apply, ip_comm]
  · set F : Poly := ∑ lam : E.Partition, x lam • Am lam.parts with hF
    have hq : star x ⬝ᵥ Matrix.mulVec
        (Matrix.of fun lam mu : E.Partition => ip (Am lam.parts) (Am mu.parts)) x = ip F F := by
      rw [hF, ip_sum_left]
      simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, star_trivial, Pi.star_apply]
      apply Finset.sum_congr rfl
      intro lam _
      rw [ip_smul_left, ip_sum_right, Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro mu _
      rw [ip_smul_right]
      ring
    rw [hq]
    obtain ⟨lam0, hlam0⟩ : ∃ lam0, x lam0 ≠ 0 := by
      by_contra h
      apply hx
      funext lam
      by_contra h'
      exact h ⟨lam, h'⟩
    have hcoef : F.coeff (Multiset.toFinsupp lam0.parts) = x lam0 := by
      rw [hF, coeff_sum]
      simp only [coeff_smul, smul_eq_mul, coeff_Am_partition]
      rw [Finset.sum_eq_single lam0]
      · simp
      · intro b _ hb; simp [hb]
      · intro h; exact absurd (Finset.mem_univ lam0) h
    set ν0 := Multiset.toFinsupp lam0.parts with hν0
    have hmem : ν0 ∈ F.support := by
      rw [MvPolynomial.mem_support_iff, hcoef]; exact hlam0
    have hwt : 0 < wt ν0 := by
      apply wt_pos
      rw [Finsupp.mem_support_iff, Multiset.toFinsupp_apply, Multiset.count_eq_zero.mpr]
      · simp
      · intro h0; exact absurd (lam0.parts_pos h0) (lt_irrefl 0)
    rw [ip_eq F F F.support le_rfl]
    calc (0 : ℝ) < F.coeff ν0 * F.coeff ν0 * wt ν0 := by
          rw [hcoef]; exact mul_pos (mul_self_pos.mpr hlam0) hwt
      _ ≤ ∑ ν ∈ F.support, F.coeff ν * F.coeff ν * wt ν :=
          Finset.single_le_sum (fun ν _ => mul_nonneg (mul_self_nonneg _) (wt_nonneg ν)) hmem

end OM.NNN30.Crossing.Gram

namespace OM.NNN30.Crossing

theorem vandermonde_shift (b c : ℕ) :
    ∑ k ∈ Finset.range (b + 1), b.choose k * (c + 1).choose (k + 1) = (b + c + 1).choose c := by
  have h1 : (b + c + 1).choose c = ∑ k ∈ Finset.range (c + 1), b.choose k * (c + 1).choose (k + 1) := by
    rw [show b + c + 1 = b + (c + 1) by ring, Nat.add_choose_eq,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i l => b.choose i * (c + 1).choose l)]
    apply Finset.sum_congr rfl
    intro k hk
    have hk' : k ≤ c := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    rw [Nat.choose_symm_of_eq_add (show c + 1 = (c - k) + (k + 1) by omega)]
  rw [h1]
  have key : ∀ n m : ℕ, b ≤ n → c ≤ m → ∑ k ∈ Finset.range (n + 1), b.choose k * (c + 1).choose (k + 1) =
      ∑ k ∈ Finset.range (b + c + 2), b.choose k * (c + 1).choose (k + 1) := by
    intro n m hn _
    by_cases h : n + 1 ≤ b + c + 2
    · apply Finset.sum_subset (Finset.range_subset_range.mpr h)
      intro k hk hk'
      simp at hk hk'
      rw [Nat.choose_eq_zero_of_lt (show b < k by omega), zero_mul]
    · symm
      apply Finset.sum_subset (Finset.range_subset_range.mpr (by omega))
      intro k hk hk'
      simp at hk hk'
      by_cases hkb : b < k
      · rw [Nat.choose_eq_zero_of_lt hkb, zero_mul]
      · rw [Nat.choose_eq_zero_of_lt (show c + 1 < k + 1 by omega), mul_zero]
  rw [key b c le_rfl le_rfl]
  have key2 : ∑ k ∈ Finset.range (c + 1), b.choose k * (c + 1).choose (k + 1) =
      ∑ k ∈ Finset.range (b + c + 2), b.choose k * (c + 1).choose (k + 1) := by
    apply Finset.sum_subset (Finset.range_subset_range.mpr (by omega))
    intro k hk hk'
    simp at hk hk'
    rw [Nat.choose_eq_zero_of_lt (show c + 1 < k + 1 by omega), mul_zero]
  rw [key2]

theorem sum_choose_mul_choose (b c : ℕ) :
    ∑ j ∈ Finset.Icc 1 (b + 1), (b + 1).choose j * j * (c + 1).choose j =
      (b + 1) * (b + c + 1).choose c := by
  rw [← vandermonde_shift, Finset.mul_sum]
  rw [show Finset.Icc 1 (b + 1) = Finset.Ico (0 + 1) (b + 1 + 1) by
    ext x; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega, ← Finset.sum_Ico_add',
    ← Finset.range_eq_Ico]
  apply Finset.sum_congr rfl
  intro k _
  rw [← Nat.add_one_mul_choose_eq]
  ring

theorem kc_succ_eq (b c : ℕ) :
    kc (b + 1) (c + 1) = ((b + 1) * (b + c + 1).choose c : ℕ) := by
  rw [kc_succ, Nat.cast_mul, Nat.cast_choose ℂ (show c ≤ b + c + 1 by omega),
    show b + c + 1 - c = b + 1 by omega]
  have h1 : (b.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have h2 : (c.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  rw [Nat.factorial_succ b]
  push_cast
  field_simp

theorem kc_eq_kcR (b c : ℕ) (hb : 0 < b) (hc : 0 < c) : kc b c = ((Gram.kcR b c : ℝ) : ℂ) := by
  obtain ⟨b, rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
  obtain ⟨c, rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
  rw [kc_succ_eq, Gram.kcR_eq]
  have : ∀ j ∈ Finset.Icc 1 (b + 1), ((b + 1).choose j : ℝ) * j * Gram.cj (c + 1) j =
      (((b + 1).choose j * j * (c + 1).choose j : ℕ) : ℝ) := by
    intro j hj
    have hj1 := (Finset.mem_Icc.mp hj).1
    rw [Gram.cj]
    split_ifs with h
    · push_cast; ring
    · rw [Nat.choose_eq_zero_of_lt (show c + 1 < j by omega)]; simp
  rw [Finset.sum_congr rfl this, ← Nat.cast_sum, sum_choose_mul_choose]
  push_cast
  ring

/-- The `0`–`1` top pairing of partition states (`p` = the point `0`, `q` = the point `1`). -/
noncomputable def Gmat (E : ℕ) : Matrix E.Partition E.Partition ℂ :=
  Matrix.of fun lam mu => wickM topK (lam.parts.map (fun b => (Pt.p, b)) +
    mu.parts.map (fun c => (Pt.q, c)))

theorem Gmat_eq (E : ℕ) (lam mu : E.Partition) :
    Gmat E lam mu = ((Gram.ip (Gram.Am lam.parts) (Gram.Am mu.parts) : ℝ) : ℂ) *
      (mu.parts.map sg).prod := by
  classical
  set s := lam.parts.map (fun b => (Pt.p, b)) + mu.parts.map (fun c => (Pt.q, c)) with hs
  let σ : Pt × ℕ → ℂ := fun u => if u.1 = Pt.q then sg u.2 else 1
  let β' : Pt × ℕ → Pt × ℕ → ℂ := fun u v => σ u * σ v * ((Gram.gramK u v : ℝ) : ℂ)
  have hβ' : ∀ u v, β' u v = β' v u := by
    intro u v; simp only [β']; rw [Gram.gramK_symm]; ring
  have hgs : ∀ u v, ((Gram.gramK u v : ℝ) : ℂ) = ((Gram.gramK v u : ℝ) : ℂ) := by
    intro u v; rw [Gram.gramK_symm]
  have hmem : ∀ u ∈ s, (u.1 = Pt.p ∨ u.1 = Pt.q) ∧ 0 < u.2 := by
    intro u hu
    rcases Multiset.mem_add.mp hu with hu | hu <;> obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.mp hu
    · exact ⟨Or.inl rfl, lam.parts_pos ha⟩
    · exact ⟨Or.inr rfl, mu.parts_pos ha⟩
  have key : ∀ u ∈ s, ∀ v ∈ s, topK u v = β' u v := by
    intro u hu v hv
    obtain ⟨hpu, hu0⟩ := hmem u hu
    obtain ⟨hpv, hv0⟩ := hmem v hv
    rcases u with ⟨pu, a⟩
    rcases v with ⟨pv, b⟩
    simp only at hpu hpv hu0 hv0
    rcases hpu with rfl | rfl <;> rcases hpv with rfl | rfl
    · simp [topK, β', σ, Gram.gramK]
    · simp only [topK, β', σ, Gram.gramK, kc_eq_kcR a b hu0 hv0]
      simp [mul_comm]
    · simp only [topK, β', σ, Gram.gramK, kc_eq_kcR b a hv0 hu0]
      simp [mul_comm]
    · simp [topK, β', σ, Gram.gramK]
  unfold Gmat
  have hR : wickM (fun u v => ((Gram.gramK u v : ℝ) : ℂ)) s = ((wickM Gram.gramK s : ℝ) : ℂ) :=
    wickM_ringHom Complex.ofRealHom Gram.gramK s
  rw [Matrix.of_apply, ← hs, wickM_congr topK_symm hβ' s key,
    wickM_scale hgs hβ' σ (fun u v => rfl), hR, hs, Gram.gram_wick]
  rw [mul_comm]
  congr 1
  rw [Multiset.map_add, Multiset.prod_add, Multiset.map_map, Multiset.map_map]
  have h1 : (lam.parts.map (σ ∘ fun b => (Pt.p, b))).prod = 1 :=
    Multiset.prod_eq_one (fun x hx => by
      obtain ⟨b, _, rfl⟩ := Multiset.mem_map.mp hx
      simp [σ])
  have h2 : mu.parts.map (σ ∘ fun c => (Pt.q, c)) = mu.parts.map sg :=
    Multiset.map_congr rfl (fun c _ => by simp [σ])
  rw [h1, h2, one_mul]

theorem Gmat_det_ne_zero (E : ℕ) : (Gmat E).det ≠ 0 := by
  classical
  set Gr : Matrix E.Partition E.Partition ℝ :=
    Matrix.of fun lam mu : E.Partition => Gram.ip (Gram.Am lam.parts) (Gram.Am mu.parts)
  have hG : Gmat E = (Complex.ofRealHom.mapMatrix Gr) *
      Matrix.diagonal (fun mu : E.Partition => (mu.parts.map sg).prod) := by
    ext lam mu
    rw [Matrix.mul_diagonal, Gmat_eq]
    rfl
  rw [hG, Matrix.det_mul, Matrix.det_diagonal, ← RingHom.map_det]
  apply mul_ne_zero
  · have hpos := (Gram.gram_posDef E).det_pos
    have e : Complex.ofRealHom Gr.det = (Gr.det : ℂ) := rfl
    rw [e]
    exact_mod_cast hpos.ne'
  · rw [Finset.prod_ne_zero_iff]
    intro mu _
    apply Multiset.prod_ne_zero
    intro h
    obtain ⟨c, _, hc⟩ := Multiset.mem_map.mp h
    rw [sg] at hc
    exact pow_ne_zero _ (by norm_num) hc

end OM.NNN30.Crossing
