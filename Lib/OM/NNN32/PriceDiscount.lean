import Lib.OM.NNN32.FourSupport

/-! # A minimal price precludes a uniform discount on common wire width

Reducing one coordinate of a minimal price yields a violating network. For two
positive coordinates we power the two witnesses until each marked width lies
between z and 2z. Their product then violates a putative discount proportional
to the smaller width. Integer powers suffice even when the logarithms are irrational.
-/

noncomputable section
open scoped Classical

namespace OM.NNN32.FourNetwork

open OM.NNN30.Net Semicontinuity AsymptoticSpectrumDuality

variable {V : Type} {φ : AsymptoticSpectrum fourPreorder} {τ : Fin 4 → V} {d : V → V → ℝ}

def gap {f : Fin 4 → ℕ+} (N : FourNetwork V f) (φ : AsymptoticSpectrum fourPreorder) (d : V → V → ℝ) :=
  N.graph.cost d - Real.logb 2 (value φ N)

lemma gap_nonneg {f : Fin 4 → ℕ+} {N : FourNetwork V f} (hv : Valid φ τ d)
    (hl : N.Local τ) (hp : 0 < value φ N) : 0 ≤ gap N φ d := sub_nonneg.2 (hv N hl hp)

private lemma cheap_coordinate (hd : Minimal φ τ d) (a c : V) {δ : ℝ} (hδ : 0 < δ) (hpos : δ ≤ d a c) :
    ∃ f, ∃ N : FourNetwork V f, N.Local τ ∧ 0 < value φ N ∧ gap N φ d < δ * N.graph.wid a c := by
  let d' (i j : V) := if i=a ∧ j=c then d a c-δ else d i j
  have hn : ¬ Valid φ τ d' := by
    intro h
    have := coordinate_le hd a c _ (sub_nonneg.2 hpos) h
    linarith
  unfold Valid at hn
  push Not at hn
  obtain ⟨f,N,hl,hp,hb⟩ := hn
  refine ⟨f,N,hl,hp,?_⟩
  have hc : N.graph.cost d' = N.graph.cost d - δ * N.graph.wid a c := by
    unfold TN.cost TN.wid
    rw [Finset.mul_sum,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k _
    by_cases h : N.graph.e1 k = a ∧ N.graph.e2 k = c
    · simp [d',h,sub_mul]
    · simp [d',h]
  rw [hc] at hb
  dsimp [gap]
  linarith

private lemma width_nonneg {f : Fin 4 → ℕ+} (N : FourNetwork V f) (i j : V) : 0 ≤ N.graph.wid i j := by
  apply Finset.sum_nonneg
  intro k _
  split_ifs
  · rcases Nat.eq_zero_or_pos (N.graph.r k) with h | h
    · simp [h]
    · exact Real.logb_nonneg (by norm_num) (by exact_mod_cast h)
  · exact le_rfl

private def data (φ : AsymptoticSpectrum fourPreorder) (τ : Fin 4 → V) (d : V → V → ℝ)
    (a c b e : V) : AddSubmonoid (ℝ × ℝ × ℝ) where
  carrier := {z | ∃ f, ∃ N : FourNetwork V f, N.Local τ ∧ 0 < value φ N ∧
    z = (gap N φ d,N.graph.wid a c,N.graph.wid b e)}
  zero_mem' := by
    refine ⟨_,unit _,unit_local _,by rw [unit_value]; norm_num,?_⟩
    unfold gap
    rw [unit_value]
    simp [unit,TN.cost,TN.wid,TN.one]
    rfl
  add_mem' := by
    rintro _ _ ⟨_,M,hl,hp,rfl⟩ ⟨_,N,hl',hp',rfl⟩
    refine ⟨_,M.kron N,hl.kron hl',by rw [value_kron]; positivity,?_⟩
    have hc : (M.kron N).graph.cost d = M.graph.cost d + N.graph.cost d :=
      TN.cost_kron d M.packed N.packed
    have hw i j : (M.kron N).graph.wid i j = M.graph.wid i j + N.graph.wid i j :=
      TN.wid_kron M.packed N.packed i j
    ext <;> simp [gap,hc,hw,value_kron,Real.logb_mul hp.ne' hp'.ne']
    ring

/-- Simultaneous tensor powers multiply the price gap and both marked widths. -/
theorem powered_data {f : Fin 4 → ℕ+} (M : FourNetwork V f) (hl : M.Local τ)
    (hp : 0 < value φ M) (a c b e : V) (d : V → V → ℝ) (p : ℕ) :
    ∃ f', ∃ N : FourNetwork V f', N.Local τ ∧ 0 < value φ N ∧
      gap N φ d = p * gap M φ d ∧ N.graph.wid a c = p * M.graph.wid a c ∧
      N.graph.wid b e = p * M.graph.wid b e := by
  let A := data φ τ d a c b e
  have h : p • (gap M φ d,M.graph.wid a c,M.graph.wid b e) ∈ A :=
    A.nsmul_mem ⟨_,M,hl,hp,rfl⟩ p
  obtain ⟨_,N,hl',hp',hz⟩ := h
  refine ⟨_,N,hl',hp',?_,?_,?_⟩
  · simpa [nsmul_eq_mul] using (congrArg Prod.fst hz).symm
  · simpa [nsmul_eq_mul] using (congrArg (fun x : ℝ × ℝ × ℝ => x.2.1) hz).symm
  · simpa [nsmul_eq_mul] using (congrArg (fun x : ℝ × ℝ × ℝ => x.2.2) hz).symm

/-- Every pair of positively priced ordered bonds has networks that come
arbitrarily close to saturating the bill per unit of common width. -/
theorem small_gap (hd : Minimal φ τ d) {a c b e : V} (ha : 0 < d a c) (hb : 0 < d b e)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ f, ∃ N : FourNetwork V f, N.Local τ ∧ 0 < value φ N ∧
      gap N φ d < δ * min (N.graph.wid a c) (N.graph.wid b e) := by
  let ε := min (min (d a c) (d b e)) (δ/4)
  have he : 0 < ε := lt_min (lt_min ha hb) (by positivity)
  obtain ⟨_,M,hM,hp,hm⟩ := cheap_coordinate hd a c he ((min_le_left _ _).trans (min_le_left _ _))
  obtain ⟨_,N,hN,hq,hn⟩ := cheap_coordinate hd b e he ((min_le_left _ _).trans (min_le_right _ _))
  let v := M.graph.wid a c
  let w := N.graph.wid b e
  have hv : 0 < v := pos_of_mul_pos_right ((gap_nonneg hd.1 hM hp).trans_lt hm) he.le
  have hw : 0 < w := pos_of_mul_pos_right ((gap_nonneg hd.1 hN hq).trans_lt hn) he.le
  let z := max v w
  have hz : 0 < z := hv.trans_le (le_max_left _ _)
  have round (x : ℝ) (hx : 0 < x) (hxz : x ≤ z) :
      z ≤ (⌈z/x⌉₊:ℝ)*x ∧ (⌈z/x⌉₊:ℝ)*x ≤ 2*z := by
    constructor
    · exact (div_le_iff₀ hx).1 (Nat.le_ceil _)
    · have h := Nat.ceil_lt_add_one (div_nonneg hz.le hx.le)
      have h' := mul_lt_mul_of_pos_right h hx
      rw [add_mul,div_mul_cancel₀ _ hx.ne',one_mul] at h'
      linarith
  let i := ⌈z/v⌉₊
  let j := ⌈z/w⌉₊
  obtain ⟨hi,hi'⟩ := round v hv (le_max_left _ _)
  obtain ⟨hj,hj'⟩ := round w hw (le_max_right _ _)
  have hip : (0:ℝ) < (i:ℝ) := pos_of_mul_pos_left (hz.trans_le hi) hv.le
  have hjp : (0:ℝ) < (j:ℝ) := pos_of_mul_pos_left (hz.trans_le hj) hw.le
  let A := data φ τ d a c b e
  let p := (gap M φ d,M.graph.wid a c,M.graph.wid b e)
  let q := (gap N φ d,N.graph.wid a c,N.graph.wid b e)
  have hA : i • p + j • q ∈ A := A.add_mem (A.nsmul_mem ⟨_,M,hM,hp,rfl⟩ i) (A.nsmul_mem ⟨_,N,hN,hq,rfl⟩ j)
  obtain ⟨_,T,hT,hpT,ht⟩ := hA
  refine ⟨_,T,hT,hpT,?_⟩
  have g := congrArg Prod.fst ht
  have g1 := congrArg (fun p : ℝ × ℝ × ℝ => p.2.1) ht
  have g2 := congrArg (fun p : ℝ × ℝ × ℝ => p.2.2) ht
  simp [p,q,nsmul_eq_mul] at g g1 g2
  have hzle : z ≤ min (T.graph.wid a c) (T.graph.wid b e) := by
    apply le_min
    · rw [← g1]
      exact hi.trans (le_add_of_nonneg_right (mul_nonneg hjp.le (width_nonneg N a c)))
    · rw [← g2]
      exact hj.trans (le_add_of_nonneg_left (mul_nonneg hip.le (width_nonneg M b e)))
  have hm' : (i:ℝ)*gap M φ d < ε*((i:ℝ)*v) := (mul_lt_mul_of_pos_left hm hip).trans_eq (by ring)
  have hn' : (j:ℝ)*gap N φ d < ε*((j:ℝ)*w) := (mul_lt_mul_of_pos_left hn hjp).trans_eq (by ring)
  apply lt_of_lt_of_le _ (mul_le_mul_of_nonneg_left hzle hδ.le)
  rw [← g]
  linarith [mul_le_mul_of_nonneg_left hi' he.le,mul_le_mul_of_nonneg_left hj' he.le,
    mul_le_mul_of_nonneg_right (show ε ≤ δ/4 from min_le_right _ _) hz.le]

end OM.NNN32.FourNetwork
