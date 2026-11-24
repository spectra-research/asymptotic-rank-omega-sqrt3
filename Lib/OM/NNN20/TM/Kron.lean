import Lib.OM.NNN20.TM.Sem

/-! # Kronecker multiplication of Taylor models

`kmul p q` packs both coefficient lists into integers `Σ c_i 2^(W κ_i)` (`κ = a + 17 b`),
multiplies them, adds the offset `Σ_{k<289} 2^(W-1) 2^(W k)` and reads the base-`2^W` digits at
the positions `κ_t` of the monomials of total degree `≤ 8`. With `W = log2(ℓ¹(p) ℓ¹(q)) + 2`
every slot sum is smaller than `2^(W-1)` in absolute value, so the digits are exactly the
coefficients of the product (`kmul_coeff`). The second component bounds the discarded products
of total degree `≥ 9` (`kmul_high`). Together they give `TM.mul_encl`. -/

namespace OM.NNN20

open Finset

/-! ## Finite facts about the monomial tables -/

def kap (i : ℕ) : ℕ := KAPPA.getD i 0
def deg (i : ℕ) : ℕ := (mx i).1 + (mx i).2
def idx (m : ℕ × ℕ) : ℕ := MONO.idxOf m
/-- start of the block of total degree `s` -/
def T (s : ℕ) : ℕ := s * (s + 1) / 2

lemma deg_le : ∀ i < NM, deg i ≤ DEG := by decide +kernel
lemma kap_eq : ∀ i < NM, kap i = (mx i).1 + RK * (mx i).2 := by decide +kernel
lemma kap_lt : ∀ i < NM, kap i ≤ 136 := by decide +kernel
lemma mx_fst_le : ∀ i < NM, (mx i).1 ≤ 8 := by decide +kernel
lemma idx_spec : ∀ a < 9, ∀ b < 9, a + b ≤ 8 → idx (a, b) < NM ∧ mx (idx (a, b)) = (a, b) := by
  decide +kernel
lemma idx_mx : ∀ i < NM, idx (mx i) = i := by decide +kernel
lemma deg_block : ∀ s < 9, (range NM).filter (fun i => deg i = s) = Ico (T s) (T s + (s + 1)) := by
  decide +kernel

lemma mx_add_deg {i j : ℕ} (h : deg i + deg j ≤ DEG) :
    idx (mx i + mx j) < NM ∧ mx (idx (mx i + mx j)) = mx i + mx j := by
  have := idx_spec ((mx i).1 + (mx j).1) (by simp [deg, DEG] at h; omega)
    ((mx i).2 + (mx j).2) (by simp [deg, DEG] at h; omega) (by simp [deg, DEG] at h; omega)
  have e : mx i + mx j = ((mx i).1 + (mx j).1, (mx i).2 + (mx j).2) := rfl
  rw [e]; exact this

/-- slot equality is monomial equality -/
lemma kap_add_iff {i j t : ℕ} (hi : i < NM) (hj : j < NM) (ht : t < NM) :
    kap i + kap j = kap t ↔ mx i + mx j = mx t := by
  rw [kap_eq i hi, kap_eq j hj, kap_eq t ht]
  have a1 := mx_fst_le i hi
  have a2 := mx_fst_le j hj
  have a3 := mx_fst_le t ht
  simp only [RK, Prod.ext_iff, Prod.fst_add, Prod.snd_add]
  constructor
  · intro h; omega
  · rintro ⟨h1, h2⟩; omega

/-! ## Packing -/

lemma pack_eq (W : ℕ) : ∀ (c : List ℤ) (ks : List ℕ),
    pack W c ks = ∑ i ∈ range ks.length, cf c i * (2 : ℤ) ^ (W * ks.getD i 0)
  | [], ks => by simp [pack]
  | a :: as, [] => by simp [pack]
  | a :: as, k :: ks => by
    rw [pack, pack_eq W as ks, List.length_cons, sum_range_succ']
    simp [add_comm]

lemma pack_KAPPA (W : ℕ) (c : List ℤ) :
    pack W c KAPPA = ∑ i ∈ range NM, cf c i * (2 : ℤ) ^ (W * kap i) := by
  rw [pack_eq]; rfl

/-- the slot sums of the product -/
def conv (p q : List ℤ) (k : ℕ) : ℤ :=
  ∑ x ∈ range NM ×ˢ range NM with kap x.1 + kap x.2 = k, cf p x.1 * cf q x.2

lemma pack_mul (W : ℕ) (p q : List ℤ) :
    pack W p KAPPA * pack W q KAPPA = ∑ k ∈ range NSLOT, conv p q k * (2 : ℤ) ^ (W * k) := by
  rw [pack_KAPPA, pack_KAPPA, sum_mul_sum, ← sum_product']
  have hmap : ∀ x ∈ range NM ×ˢ range NM, kap x.1 + kap x.2 ∈ range NSLOT := by
    intro x hx
    simp only [mem_product, mem_range] at hx
    have := kap_lt x.1 hx.1
    have := kap_lt x.2 hx.2
    simp only [mem_range, NSLOT]; omega
  rw [← sum_fiberwise_of_maps_to hmap]
  refine sum_congr rfl fun k _ => ?_
  rw [conv, sum_mul]
  refine sum_congr rfl fun x hx => ?_
  simp only [mem_filter] at hx
  rw [← hx.2, mul_add, pow_add]; ring

/-! ## Base-`B` digits -/

lemma digit_sum (B : ℕ) (hB : 0 < B) : ∀ (m K : ℕ) (e : ℕ → ℕ), (∀ k < K, e k < B) → m < K →
    (∑ k ∈ range K, e k * B ^ k) / B ^ m % B = e m := by
  intro m
  induction m with
  | zero =>
    intro K e he hm
    obtain ⟨K', rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
    have : ∑ k ∈ range K', e (k + 1) * B ^ (k + 1) = B * ∑ k ∈ range K', e (k + 1) * B ^ k := by
      rw [mul_sum]; refine sum_congr rfl fun k _ => ?_; ring
    rw [sum_range_succ', this]
    simp only [pow_zero, mul_one, Nat.div_one]
    rw [add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (he 0 (by omega))]
  | succ m ih =>
    intro K e he hm
    obtain ⟨K', rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
    rw [sum_range_succ', pow_zero, mul_one]
    have : ∑ k ∈ range K', e (k + 1) * B ^ (k + 1) = B * ∑ k ∈ range K', e (k + 1) * B ^ k := by
      rw [mul_sum]; refine sum_congr rfl fun k _ => ?_; ring
    rw [this, pow_succ', ← Nat.div_div_eq_div_mul, add_comm, Nat.add_mul_div_left _ _ hB,
      Nat.div_eq_of_lt (he 0 (by omega)), zero_add]
    exact ih K' (fun k => e (k + 1)) (fun k hk => he (k + 1) (by omega)) (by omega)

lemma cf_digits (W N h : ℕ) : ∀ (ks : List ℕ) (t : ℕ), t < ks.length →
    cf (digits W N h ks) t = (((N >>> (W * ks.getD t 0)) % 2 ^ W : ℕ) : ℤ) - h
  | [], t, ht => by simp at ht
  | k :: ks, 0, _ => by simp [digits]
  | k :: ks, t + 1, ht => by
    simp only [digits, cf_cons_succ, List.getD_cons_succ]
    exact cf_digits W N h ks t (by simpa using ht)

/-! ## The coefficients of the product -/

lemma sum_abs_le_l1_int : ∀ (c : List ℤ) (n : ℕ), ∑ i ∈ range n, |cf c i| ≤ (l1 c : ℤ)
  | [], n => by simp [l1]
  | a :: as, 0 => by simp
  | a :: as, n + 1 => by
    rw [sum_range_succ']
    simp only [cf_cons_succ, cf_cons_zero, l1_cons, Nat.cast_add, Int.natCast_natAbs]
    have := sum_abs_le_l1_int as n
    linarith

lemma conv_abs_le (p q : List ℤ) (k : ℕ) : |conv p q k| ≤ (l1 p * l1 q : ℕ) := by
  unfold conv
  refine (abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ x ∈ range NM ×ˢ range NM with kap x.1 + kap x.2 = k, |cf p x.1 * cf q x.2|
      ≤ ∑ x ∈ range NM ×ˢ range NM, |cf p x.1 * cf q x.2| :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => abs_nonneg _)
    _ = (∑ i ∈ range NM, |cf p i|) * ∑ j ∈ range NM, |cf q j| := by
        rw [sum_product, sum_mul_sum]; simp only [abs_mul]
    _ ≤ (l1 p : ℤ) * l1 q :=
        mul_le_mul (sum_abs_le_l1_int p NM) (sum_abs_le_l1_int q NM)
          (sum_nonneg fun _ _ => abs_nonneg _) (by positivity)
    _ = _ := by norm_cast

theorem kmul_coeff (p q : List ℤ) {t : ℕ} (ht : t < NM) :
    cf (kmul p q).1 t = ∑ x ∈ range NM ×ˢ range NM with mx x.1 + mx x.2 = mx t,
      cf p x.1 * cf q x.2 := by
  set W := Nat.log2 (l1 p * l1 q) + 2 with hW
  set h : ℕ := 2 ^ (W - 1) with hh
  have hW1 : 2 ^ W = 2 * h := by
    rw [hh, ← pow_succ']; congr 1
  have hlt : l1 p * l1 q < h := by
    rw [hh, show W - 1 = Nat.log2 (l1 p * l1 q) + 1 by omega]; exact Nat.lt_log2_self
  -- every slot digit lies in [0, 2^W)
  have hslot : ∀ k, 0 ≤ conv p q k + h ∧ conv p q k + h < 2 ^ W := by
    intro k
    have := abs_lt.mp ((conv_abs_le p q k).trans_lt (by exact_mod_cast hlt :
      ((l1 p * l1 q : ℕ) : ℤ) < (h : ℤ)))
    constructor
    · linarith
    · have : ((2 ^ W : ℕ) : ℤ) = 2 * h := by exact_mod_cast hW1
      push_cast at this; rw [this]; linarith
  set e : ℕ → ℕ := fun k => (conv p q k + h).toNat
  have he : ∀ k, (e k : ℤ) = conv p q k + h := fun k => Int.toNat_of_nonneg (hslot k).1
  have heB : ∀ k, e k < 2 ^ W := fun k => by
    have := (hslot k).2; rw [← he k] at this; exact_mod_cast this
  -- the offset
  have hoff : ((h * ((2 ^ (W * NSLOT) - 1) / (2 ^ W - 1)) : ℕ) : ℤ) =
      ∑ k ∈ range NSLOT, (h : ℤ) * (2 : ℤ) ^ (W * k) := by
    have h2 : 2 ≤ 2 ^ W := by
      calc 2 = 2 ^ 1 := rfl
        _ ≤ 2 ^ W := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [pow_mul, ← Nat.geomSum_eq h2 NSLOT, mul_sum]
    push_cast
    refine sum_congr rfl fun k _ => ?_
    rw [← pow_mul]
  -- the packed number
  set N := (pack W p KAPPA * pack W q KAPPA + (h * ((2 ^ (W * NSLOT) - 1) / (2 ^ W - 1)) : ℕ)).toNat
  have hNsum : N = ∑ k ∈ range NSLOT, e k * (2 ^ W) ^ k := by
    have hz : pack W p KAPPA * pack W q KAPPA + (h * ((2 ^ (W * NSLOT) - 1) / (2 ^ W - 1)) : ℕ) =
        ((∑ k ∈ range NSLOT, e k * (2 ^ W) ^ k : ℕ) : ℤ) := by
      rw [pack_mul, hoff, ← sum_add_distrib]
      push_cast
      refine sum_congr rfl fun k _ => ?_
      rw [← pow_mul, ← add_mul, he k]
    simp only [N, hz, Int.toNat_natCast]
  -- the digit at the slot of t
  have hk : kap t < NSLOT := by have := kap_lt t ht; simp [NSLOT]; omega
  have hdig : (N >>> (W * kap t)) % 2 ^ W = e (kap t) := by
    rw [Nat.shiftRight_eq_div_pow, pow_mul, hNsum]
    exact digit_sum (2 ^ W) (by positivity) (kap t) NSLOT e (fun k _ => heB k) hk
  have hc : cf (kmul p q).1 t = conv p q (kap t) := by
    show cf (digits W N h KAPPA) t = _
    rw [cf_digits W N h KAPPA t (by rw [show KAPPA.length = NM from rfl]; exact ht)]
    change (((N >>> (W * kap t)) % 2 ^ W : ℕ) : ℤ) - h = _
    rw [hdig, he]; ring
  rw [hc, conv]
  refine sum_congr ?_ fun _ _ => rfl
  ext x
  simp only [mem_filter, mem_product, mem_range]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨h1, h2⟩, (kap_add_iff h1 h2 ht).mp h3⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨h1, h2⟩, (kap_add_iff h1 h2 ht).mpr h3⟩


/-! ## The discarded products -/

lemma getD_drop' {α : Type*} (d : α) : ∀ (l : List α) (n i : ℕ), (l.drop n).getD i d = l.getD (n + i) d
  | [], n, i => by simp
  | a :: l, 0, i => by simp
  | a :: l, n + 1, i => by
    rw [List.drop_succ_cons, getD_drop' d l n i, show n + 1 + i = (n + i) + 1 by omega,
      List.getD_cons_succ]

lemma l1_slice : ∀ (c : List ℤ) (a b : ℕ),
    (l1 ((c.drop a).take b) : ℤ) = ∑ i ∈ range b, |cf c (a + i)|
  | [], a, b => by simp [l1]
  | x :: xs, 0, 0 => by simp [l1]
  | x :: xs, 0, b + 1 => by
    rw [List.drop_zero, List.take_succ_cons, l1_cons, sum_range_succ']
    have := l1_slice xs 0 b
    simp only [List.drop_zero, zero_add] at this ⊢
    simp only [cf_cons_zero, cf_cons_succ, Nat.cast_add, Int.natCast_natAbs, this]
    ring
  | x :: xs, a + 1, b => by
    rw [List.drop_succ_cons, l1_slice xs a b]
    refine sum_congr rfl fun i _ => ?_
    rw [show a + 1 + i = (a + i) + 1 by omega, cf_cons_succ]

lemma degNorms_getD : ∀ (bs : List ℕ) (c : List ℤ) (s : ℕ), s < bs.length →
    (degNorms bs c).getD s 0 = l1 ((c.drop ((bs.take s).sum)).take (bs.getD s 0))
  | [], c, s, h => by simp at h
  | b :: bs, c, 0, _ => by simp [degNorms]
  | b :: bs, c, s + 1, h => by
    simp only [degNorms, List.getD_cons_succ, List.take_succ_cons, List.sum_cons, List.getD_cons_succ]
    rw [degNorms_getD bs (c.drop b) s (by simpa using h), List.drop_drop]

lemma BLOCKS_take_sum : ∀ s < 9, (BLOCKS.take s).sum = T s := by decide +kernel
lemma BLOCKS_getD : ∀ s < 9, BLOCKS.getD s 0 = s + 1 := by decide +kernel

/-- the per-degree norms -/
lemma degNorms_BLOCKS (c : List ℤ) {s : ℕ} (hs : s < 9) :
    ((degNorms BLOCKS c).getD s 0 : ℤ) = ∑ i ∈ Ico (T s) (T s + (s + 1)), |cf c i| := by
  rw [degNorms_getD BLOCKS c s (by simpa [BLOCKS] using hs), BLOCKS_take_sum s hs,
    BLOCKS_getD s hs, l1_slice, sum_Ico_eq_sum_range]
  simp

lemma sumN_eq : ∀ (l : List ℕ), (sumN l : ℤ) = ∑ i ∈ range l.length, (l.getD i 0 : ℤ)
  | [] => by simp [sumN]
  | a :: as => by
    rw [sumN, List.length_cons, sum_range_succ']
    simp [sumN_eq as, add_comm]

lemma highAux_eq (m : List ℕ) : ∀ (l : List ℕ) (s0 : ℕ),
    (highAux m s0 l : ℤ) = ∑ i ∈ range l.length,
      (l.getD i 0 : ℤ) * sumN (m.drop (DEG + 1 - (s0 + i)))
  | [], s0 => by simp [highAux]
  | a :: as, s0 => by
    rw [highAux, List.length_cons, sum_range_succ']
    push_cast
    rw [highAux_eq m as (s0 + 1)]
    simp only [List.getD_cons_succ, List.getD_cons_zero, add_zero]
    rw [add_comm]
    congr 1
    refine sum_congr rfl fun i _ => ?_
    rw [show s0 + (i + 1) = s0 + 1 + i by omega]

/-- `deg` is constant on the blocks, and the blocks partition `range NM` -/
lemma sum_by_deg (F : ℕ → ℤ) :
    ∑ i ∈ range NM, F i = ∑ s ∈ range 9, ∑ a ∈ range (s + 1), F (T s + a) := by
  have hmap : ∀ i ∈ range NM, deg i ∈ range 9 := by
    intro i hi
    have := deg_le i (mem_range.mp hi)
    simp [DEG] at this; simp; omega
  rw [← sum_fiberwise_of_maps_to hmap]
  refine sum_congr rfl fun s hs => ?_
  rw [deg_block s (mem_range.mp hs), sum_Ico_eq_sum_range]
  simp

lemma deg_T {s a : ℕ} (hs : s < 9) (ha : a < s + 1) : deg (T s + a) = s ∧ T s + a < NM := by
  have h := deg_block s hs
  have hm : T s + a ∈ Ico (T s) (T s + (s + 1)) := by simp; omega
  rw [← h] at hm
  simp only [mem_filter, mem_range] at hm
  exact ⟨hm.2, hm.1⟩

theorem kmul_high (p q : List ℤ) :
    ∑ z ∈ (range NM ×ˢ range NM).filter (fun z => DEG < deg z.1 + deg z.2),
      |cf p z.1| * |cf q z.2| ≤ ((kmul p q).2 : ℤ) := by
  have hn : ∀ s < 9, ((degNorms BLOCKS p).getD s 0 : ℤ) = ∑ a ∈ range (s + 1), |cf p (T s + a)| := by
    intro s hs; rw [degNorms_BLOCKS p hs, sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]
  have hm : ∀ s < 9, ((degNorms BLOCKS q).getD s 0 : ℤ) = ∑ a ∈ range (s + 1), |cf q (T s + a)| := by
    intro s hs; rw [degNorms_BLOCKS q hs, sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]
  have hlen : ∀ c : List ℤ, (degNorms BLOCKS c).length = 9 := fun c => by simp [degNorms, BLOCKS]
  show _ ≤ ((highBound (degNorms BLOCKS p) (degNorms BLOCKS q) : ℕ) : ℤ)
  rw [highBound, highAux_eq, hlen]
  -- the left side, grouped by degrees
  rw [sum_filter, sum_product]
  rw [sum_by_deg (fun i => ∑ j ∈ range NM, if DEG < deg i + deg j then |cf p i| * |cf q j| else 0)]
  refine sum_le_sum fun s hs => ?_
  have hs9 := mem_range.mp hs
  rw [hn s hs9, sum_mul]
  refine sum_le_sum fun a ha => ?_
  have ha' := mem_range.mp ha
  obtain ⟨hda, _⟩ := deg_T hs9 ha'
  rw [sum_by_deg, sumN_eq, List.length_drop, hlen, mul_sum]
  simp only [hda, zero_add]
  -- the inner sum over the degree s' of the second factor
  have : ∀ s' ∈ range 9, (∑ b ∈ range (s' + 1),
      if DEG < s + deg (T s' + b) then |cf p (T s + a)| * |cf q (T s' + b)| else 0) =
      if DEG < s + s' then |cf p (T s + a)| * ((degNorms BLOCKS q).getD s' 0 : ℤ) else 0 := by
    intro s' hs'
    have hs'9 := mem_range.mp hs'
    rw [hm s' hs'9]
    split_ifs with hc
    · rw [mul_sum]; refine sum_congr rfl fun b hb => ?_
      rw [(deg_T hs'9 (mem_range.mp hb)).1, if_pos hc]
    · refine sum_eq_zero fun b hb => ?_
      rw [(deg_T hs'9 (mem_range.mp hb)).1, if_neg hc]
  rw [sum_congr rfl this]
  -- compare with the right side: s' ranges over [9 - s, 9)
  have hsplit : ∑ s' ∈ range 9, (if DEG < s + s' then |cf p (T s + a)| *
      ((degNorms BLOCKS q).getD s' 0 : ℤ) else 0) =
      ∑ i ∈ range (9 - (DEG + 1 - s)), |cf p (T s + a)| *
        (((degNorms BLOCKS q).drop (DEG + 1 - s)).getD i 0 : ℤ) := by
    rw [← sum_range_add_sum_Ico _ (show DEG + 1 - s ≤ 9 by simp only [DEG]; omega),
      sum_eq_zero (fun i hi => by
        have := mem_range.mp hi; rw [if_neg (by simp [DEG] at this ⊢; omega)]),
      zero_add, sum_Ico_eq_sum_range]
    refine sum_congr rfl fun i hi => ?_
    have := mem_range.mp hi
    rw [if_pos (by simp [DEG] at this ⊢; omega), getD_drop']
  rw [hsplit]

/-! ## The product -/

lemma low_regroup (p q : List ℤ) (x y : ℝ) :
    ∑ z ∈ (range NM ×ˢ range NM).filter (fun z => deg z.1 + deg z.2 ≤ DEG),
      ((cf p z.1 : ℝ) * cf q z.2) * (mono z.1 x y * mono z.2 x y) =
    ∑ t ∈ range NM, (cf (kmul p q).1 t : ℝ) * mono t x y := by
  have hmap : ∀ z ∈ (range NM ×ˢ range NM).filter (fun z => deg z.1 + deg z.2 ≤ DEG),
      idx (mx z.1 + mx z.2) ∈ range NM := by
    intro z hz
    simp only [mem_filter] at hz
    exact mem_range.mpr (mx_add_deg hz.2).1
  rw [← sum_fiberwise_of_maps_to hmap]
  refine sum_congr rfl fun t ht => ?_
  have ht' := mem_range.mp ht
  rw [kmul_coeff p q ht']
  push_cast
  rw [sum_mul]
  have hfilt : ((range NM ×ˢ range NM).filter (fun z => deg z.1 + deg z.2 ≤ DEG)).filter
      (fun z => idx (mx z.1 + mx z.2) = t) =
      (range NM ×ˢ range NM).filter (fun z => mx z.1 + mx z.2 = mx t) := by
    ext z
    simp only [mem_filter, mem_product, mem_range]
    constructor
    · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
      refine ⟨⟨h1, h2⟩, ?_⟩
      rw [← h4]; exact ((mx_add_deg h3).2).symm
    · rintro ⟨⟨h1, h2⟩, h3⟩
      have hd : deg z.1 + deg z.2 ≤ DEG := by
        have := deg_le t ht'
        simp only [deg] at this ⊢
        have e1 := congrArg Prod.fst h3
        have e2 := congrArg Prod.snd h3
        simp only [Prod.fst_add, Prod.snd_add] at e1 e2
        omega
      exact ⟨⟨⟨h1, h2⟩, hd⟩, by rw [h3, idx_mx t ht']⟩
  rw [hfilt]
  refine sum_congr rfl fun z hz => ?_
  simp only [mem_filter] at hz
  have e1 := congrArg Prod.fst hz.2
  have e2 := congrArg Prod.snd hz.2
  simp only [Prod.fst_add, Prod.snd_add] at e1 e2
  simp only [mono, ← e1, ← e2, pow_add]
  ring

lemma peval_mul (p q : List ℤ) (x y : ℝ) :
    peval p x y * peval q x y =
    ∑ z ∈ (range NM ×ˢ range NM).filter (fun z => deg z.1 + deg z.2 ≤ DEG),
      ((cf p z.1 : ℝ) * cf q z.2) * (mono z.1 x y * mono z.2 x y) +
    ∑ z ∈ (range NM ×ˢ range NM).filter (fun z => ¬ deg z.1 + deg z.2 ≤ DEG),
      ((cf p z.1 : ℝ) * cf q z.2) * (mono z.1 x y * mono z.2 x y) := by
  rw [sum_filter_add_sum_filter_not, peval, peval, sum_mul_sum, sum_product]
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
  ring

namespace TM

theorem mul_encl {t u : TM} {f g : ℝ → ℝ → ℝ} (ht : t.Encl f) (hu : u.Encl g) :
    (t.mul u).Encl (fun x y => f x y * g x y) := by
  intro x y hx hy
  obtain ⟨a1, a2⟩ := ht x y hx hy
  obtain ⟨b1, b2⟩ := hu x y hx hy
  set e1 := (ONE : ℝ) * f x y - peval t.c x y
  set e2 := (ONE : ℝ) * g x y - peval u.c x y
  have hO := ONE_pos
  have emax_ge : ∀ v : TM, |(v.lo : ℝ)| ≤ v.emax ∧ |(v.hi : ℝ)| ≤ v.emax := by
    intro v
    unfold emax
    rw [Nat.cast_max, Nat.cast_natAbs, Nat.cast_natAbs, Int.cast_abs, Int.cast_abs]
    exact ⟨le_max_left _ _, le_max_right _ _⟩
  have hE1 : |e1| ≤ t.emax := by
    obtain ⟨l1', l2'⟩ := emax_ge t
    rw [abs_le]; constructor
    · have := neg_abs_le (t.lo : ℝ); linarith
    · have := le_abs_self (t.hi : ℝ); linarith
  have hE2 : |e2| ≤ u.emax := by
    obtain ⟨l1', l2'⟩ := emax_ge u
    rw [abs_le]; constructor
    · have := neg_abs_le (u.lo : ℝ); linarith
    · have := le_abs_self (u.hi : ℝ); linarith
  have hP := peval_abs_le t.c hx hy
  have hQ := peval_abs_le u.c hx hy
  -- the product and its parts
  set K := (kmul t.c u.c).1 with hK
  set hb := (kmul t.c u.c).2 with hhb
  set LOW := ∑ s ∈ range NM, (cf K s : ℝ) * mono s x y
  set HIGH := ∑ z ∈ (range NM ×ˢ range NM).filter (fun z => ¬ deg z.1 + deg z.2 ≤ DEG),
      ((cf t.c z.1 : ℝ) * cf u.c z.2) * (mono z.1 x y * mono z.2 x y)
  have hpq : peval t.c x y * peval u.c x y = LOW + HIGH := by
    rw [peval_mul, low_regroup]
  have hHIGH : |HIGH| ≤ hb := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    have hkh := kmul_high t.c u.c
    have hkh' : ∑ z ∈ (range NM ×ˢ range NM).filter (fun z => DEG < deg z.1 + deg z.2),
        |(cf t.c z.1 : ℝ)| * |(cf u.c z.2 : ℝ)| ≤ (hb : ℝ) := by
      have : ((∑ z ∈ (range NM ×ˢ range NM).filter (fun z => DEG < deg z.1 + deg z.2),
          |cf t.c z.1| * |cf u.c z.2| : ℤ) : ℝ) ≤ ((hb : ℤ) : ℝ) := by exact_mod_cast hkh
      push_cast at this; exact this
    have hfil : (range NM ×ˢ range NM).filter (fun z => ¬ deg z.1 + deg z.2 ≤ DEG) =
        (range NM ×ˢ range NM).filter (fun z => DEG < deg z.1 + deg z.2) := by
      ext z; simp
    rw [hfil]
    refine le_trans (sum_le_sum fun z _ => ?_) hkh'
    calc |((cf t.c z.1 : ℝ) * cf u.c z.2) * (mono z.1 x y * mono z.2 x y)|
        = |(cf t.c z.1 : ℝ)| * |(cf u.c z.2 : ℝ)| * (|mono z.1 x y| * |mono z.2 x y|) := by
          rw [abs_mul, abs_mul, abs_mul]
      _ ≤ |(cf t.c z.1 : ℝ)| * |(cf u.c z.2 : ℝ)| * (1 * 1) := by
          gcongr
          · exact mono_abs_le hx hy _
          · exact mono_abs_le hx hy _
      _ = _ := by ring
  -- rescaling the kept coefficients
  have hD1 : |LOW - ONE * peval (K.map (fun a => a / ONE)) x y| ≤ NM * ONE := by
    rw [peval, mul_sum, ← sum_sub_distrib]
    refine (abs_sum_le_sum_abs _ _).trans ?_
    have : ∀ s ∈ range NM, |(cf K s : ℝ) * mono s x y -
        ONE * ((cf (K.map (fun a => a / ONE)) s : ℝ) * mono s x y)| ≤ ONE := by
      intro s _
      rw [cf_map (by simp)]
      obtain ⟨r1, r2⟩ := ediv_bounds (cf K s) ONE (by norm_num [ONE])
      have e : (cf K s : ℝ) * mono s x y - ONE * (((cf K s / ONE : ℤ) : ℝ) * mono s x y) =
          ((cf K s : ℝ) - ONE * ((cf K s / ONE : ℤ) : ℝ)) * mono s x y := by ring
      rw [e, abs_mul]
      have h0 : 0 ≤ (cf K s : ℝ) - ONE * ((cf K s / ONE : ℤ) : ℝ) := by linarith
      have h1 : (cf K s : ℝ) - ONE * ((cf K s / ONE : ℤ) : ℝ) ≤ ONE := by linarith
      calc |(cf K s : ℝ) - ONE * ((cf K s / ONE : ℤ) : ℝ)| * |mono s x y| ≤ ONE * 1 :=
            mul_le_mul (by rw [abs_of_nonneg h0]; exact h1) (mono_abs_le hx hy s) (abs_nonneg _)
              hO.le
        _ = ONE := mul_one _
    refine (sum_le_sum this).trans ?_
    simp [NM]
  -- the cross terms
  set X : ℕ := l1 t.c * u.emax + l1 u.c * t.emax + t.emax * u.emax
  have hX : |peval t.c x y * e2 + peval u.c x y * e1 + e1 * e2| ≤ X := by
    have h1 : |peval t.c x y * e2| ≤ (l1 t.c : ℝ) * (u.emax : ℝ) := by
      rw [abs_mul]; exact mul_le_mul hP hE2 (abs_nonneg _) (Nat.cast_nonneg _)
    have h2 : |peval u.c x y * e1| ≤ (l1 u.c : ℝ) * (t.emax : ℝ) := by
      rw [abs_mul]; exact mul_le_mul hQ hE1 (abs_nonneg _) (Nat.cast_nonneg _)
    have h3 : |e1 * e2| ≤ (t.emax : ℝ) * (u.emax : ℝ) := by
      rw [abs_mul]; exact mul_le_mul hE1 hE2 (abs_nonneg _) (Nat.cast_nonneg _)
    have hXe : (X : ℝ) = (l1 t.c : ℝ) * (u.emax : ℝ) + (l1 u.c : ℝ) * (t.emax : ℝ) +
        (t.emax : ℝ) * (u.emax : ℝ) := by simp only [X]; push_cast; ring
    rw [hXe]
    calc _ ≤ |peval t.c x y * e2| + |peval u.c x y * e1| + |e1 * e2| := abs_add_three _ _ _
      _ ≤ _ := by linarith
  -- assemble
  have hfg : (ONE : ℝ) * (f x y * g x y) =
      (LOW + HIGH + (peval t.c x y * e2 + peval u.c x y * e1 + e1 * e2)) / ONE := by
    rw [← hpq]
    field_simp
    simp only [e1, e2]; ring
  have hc1 := cdiv_bounds hb ONE (by norm_num [ONE])
  have hc2 := cdiv_bounds X ONE (by norm_num [ONE])
  push_cast at hc1 hc2
  have key : |(ONE : ℝ) * (f x y * g x y) - peval (K.map (fun a => a / ONE)) x y| ≤
      NM + cdiv hb ONE + cdiv X ONE := by
    rw [hfg]
    have : (LOW + HIGH + (peval t.c x y * e2 + peval u.c x y * e1 + e1 * e2)) / ONE -
        peval (K.map (fun a => a / ONE)) x y =
        ((LOW - ONE * peval (K.map (fun a => a / ONE)) x y) + HIGH +
          (peval t.c x y * e2 + peval u.c x y * e1 + e1 * e2)) / ONE := by
      field_simp
      ring
    rw [this, abs_div, abs_of_pos hO, div_le_iff₀ hO]
    calc _ ≤ |LOW - ONE * peval (K.map (fun a => a / ONE)) x y| + |HIGH| +
          |peval t.c x y * e2 + peval u.c x y * e1 + e1 * e2| := abs_add_three _ _ _
      _ ≤ NM * ONE + hb + X := by linarith
      _ ≤ ((NM : ℝ) + (cdiv hb ONE : ℝ) + (cdiv X ONE : ℝ)) * ONE := by linarith
  have hk := abs_le.mp key
  have hlo : ((t.mul u).lo : ℝ) = -((NM : ℝ) + (cdiv hb ONE : ℝ) + (cdiv X ONE : ℝ)) := by
    simp only [TM.mul]; push_cast; rfl
  have hhi : ((t.mul u).hi : ℝ) = (NM : ℝ) + (cdiv hb ONE : ℝ) + (cdiv X ONE : ℝ) := by
    simp only [TM.mul]; push_cast; rfl
  have hc : (t.mul u).c = K.map (fun a => a / ONE) := rfl
  rw [hlo, hhi, hc]
  exact ⟨by linarith [hk.1], hk.2⟩

end TM

end OM.NNN20
