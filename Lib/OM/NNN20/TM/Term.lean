import Lib.OM.NNN20.TM.Series

/-! # Upper bounds of exact polynomials on the box, by subdivision

`termCheck c B lvl` cuts `[-1,1]^2` into `2^lvl × 2^lvl` squares; on each it evaluates the
polynomial `c` (coefficients in units of `2^-P`) at the affine Taylor models `cx + h s`,
`cy + h t` and compares the upper range bound with `B`. Soundness (`termCheck_spec`) only uses
the proved Taylor-model operations and the fact that the squares cover the box. -/

namespace OM.NNN20

open Finset

namespace TM

/-- `[1, X, X^2, …, X^n]` -/
def powers (X : TM) : ℕ → List TM
  | 0 => [const ONE]
  | n + 1 => let l := powers X n; l ++ [(l.getLast?.getD (const ONE)).mul X]

/-- `Σ_i c_i 2^-P X^{a_i} Y^{b_i}` -/
def evalAux (XP YP : List TM) : List ℤ → List (ℕ × ℕ) → TM
  | a :: as, m :: ms =>
    (mulq ((a : ℚ) / ONE) (((XP.getD m.1 (const ONE)).mul (YP.getD m.2 (const ONE))))).add
      (evalAux XP YP as ms)
  | _, _ => const 0

def evalAt (c : List ℤ) (X Y : TM) : TM := evalAux (powers X DEG) (powers Y DEG) c MONO

end TM

/-- check `peval c / ONE ≤ B` on the box by a `2^lvl` grid -/
def termCheck (c : List ℤ) (B : ℚ) (lvl : ℕ) : Bool :=
  let n : ℕ := 2 ^ lvl
  let h : ℚ := 1 / n
  (List.range n).all fun i => (List.range n).all fun j =>
    decide ((TM.evalAt c (TM.affine (-1 + h * (2 * i + 1)) h 0)
      (TM.affine (-1 + h * (2 * j + 1)) h 1)).rng.2 ≤ qfloor (B * ONE))

namespace TM

lemma powers_length (X : TM) : ∀ n, (powers X n).length = n + 1
  | 0 => rfl
  | n + 1 => by simp [powers, powers_length X n]

lemma powers_encl {X : TM} {xf : ℝ → ℝ → ℝ} (hX : X.Encl xf) :
    ∀ n k, k ≤ n → ((powers X n).getD k (const ONE)).Encl (fun s t => xf s t ^ k)
  | 0, k, hk => by
    obtain rfl : k = 0 := by omega
    simpa [powers] using const_one_encl
  | n + 1, k, hk => by
    have hlen := powers_length X n
    rcases Nat.lt_or_ge k (n + 1) with h | h
    · simp only [powers]
      rw [List.getD_append _ _ _ _ (by rw [hlen]; exact h)]
      exact powers_encl hX n k (by omega)
    · obtain rfl : k = n + 1 := by omega
      simp only [powers]
      rw [List.getD_append_right _ _ _ _ (by rw [hlen])]
      simp only [hlen, Nat.sub_self, List.getD_cons_zero]
      have hlast : (powers X n).getLast?.getD (const ONE) = (powers X n).getD n (const ONE) := by
        rw [List.getLast?_eq_getElem?, hlen, Nat.add_sub_cancel, List.getD_eq_getElem?_getD]
      rw [hlast]
      exact (mul_encl (powers_encl hX n n le_rfl) hX).congr fun _ _ _ _ => by ring

lemma evalAux_encl {XP YP : List TM} {xf yf : ℝ → ℝ → ℝ}
    (hXP : ∀ k ≤ DEG, (XP.getD k (const ONE)).Encl (fun s t => xf s t ^ k))
    (hYP : ∀ k ≤ DEG, (YP.getD k (const ONE)).Encl (fun s t => yf s t ^ k)) :
    ∀ (c : List ℤ) (ms : List (ℕ × ℕ)), (∀ m ∈ ms, m.1 ≤ DEG ∧ m.2 ≤ DEG) →
      (evalAux XP YP c ms).Encl (fun s t => ∑ i ∈ range (min c.length ms.length),
        ((c.getD i 0 : ℝ) / ONE) * xf s t ^ (ms.getD i (0, 0)).1 * yf s t ^ (ms.getD i (0, 0)).2)
  | a :: as, m :: ms, hm => by
    have h1 := hm m (by simp)
    have hrest := evalAux_encl hXP hYP as ms (fun m' hm' => hm m' (by simp [hm']))
    have hprod := mul_encl (hXP m.1 h1.1) (hYP m.2 h1.2)
    have hterm := mulq_encl ((a : ℚ) / ONE) hprod
    refine (add_encl hterm hrest).congr fun s t _ _ => ?_
    have hmin : min (as.length + 1) (ms.length + 1) = min as.length ms.length + 1 := by omega
    simp only [List.length_cons, hmin]
    rw [sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    push_cast; ring
  | [], ms, _ => by simpa [evalAux] using (const_encl 0).congr fun _ _ _ _ => by simp
  | a :: as, [], _ => by simpa [evalAux] using (const_encl 0).congr fun _ _ _ _ => by simp

lemma MONO_le : ∀ m ∈ MONO, m.1 ≤ DEG ∧ m.2 ≤ DEG := by decide +kernel

theorem evalAt_encl (c : List ℤ) {X Y : TM} {xf yf : ℝ → ℝ → ℝ} (hX : X.Encl xf) (hY : Y.Encl yf) :
    (evalAt c X Y).Encl (fun s t => peval c (xf s t) (yf s t) / ONE) := by
  have h := evalAux_encl (fun k hk => powers_encl hX DEG k hk) (fun k hk => powers_encl hY DEG k hk)
    c MONO MONO_le
  refine h.congr fun s t _ _ => ?_
  rw [peval, sum_div]
  have hM : MONO.length = NM := rfl
  rcases le_total c.length NM with hc | hc
  · rw [Nat.min_eq_left (hM ▸ hc)]
    rw [← sum_range_add_sum_Ico _ hc]
    rw [sum_eq_zero (s := Ico c.length NM) (fun i hi => by
      have := (mem_Ico.mp hi).1
      rw [show cf c i = 0 from List.getD_eq_default _ _ this]; simp), add_zero]
    refine sum_congr rfl fun i _ => ?_
    simp only [cf, mono, mx]; ring
  · rw [Nat.min_eq_right (hM ▸ hc)]
    refine sum_congr rfl fun i _ => ?_
    simp only [cf, mono, mx]; ring

end TM

/-- the grid squares cover `[-1, 1]` -/
lemma grid_cover {n : ℕ} (hn : 0 < n) {x : ℝ} (hx : |x| ≤ 1) :
    ∃ i < n, |(x - (-1 + (1 / (n : ℝ)) * (2 * i + 1))) / (1 / (n : ℝ))| ≤ 1 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hx' := abs_le.mp hx
  set i := min (n - 1) ⌊(x + 1) * n / 2⌋₊
  refine ⟨i, by omega, ?_⟩
  rw [abs_le, le_div_iff₀ (by positivity), div_le_iff₀ (by positivity)]
  have hfl := Nat.floor_le (show (0 : ℝ) ≤ (x + 1) * n / 2 by nlinarith)
  have hfl' := Nat.lt_floor_add_one ((x + 1) * n / 2)
  have hi1 : (i : ℝ) ≤ (x + 1) * n / 2 := by
    have : (i : ℝ) ≤ ⌊(x + 1) * n / 2⌋₊ := by exact_mod_cast min_le_right _ _
    linarith
  have hi2 : (x + 1) * n / 2 ≤ i + 1 := by
    rcases le_total (n - 1) ⌊(x + 1) * n / 2⌋₊ with h | h
    · have : i = n - 1 := min_eq_left h
      have hc : ((n - 1 : ℕ) : ℝ) = n - 1 := by rw [Nat.cast_sub (by omega)]; simp
      rw [this, hc]; nlinarith
    · have : i = ⌊(x + 1) * n / 2⌋₊ := min_eq_right h
      rw [this]; linarith
  constructor
  · have : -1 * (1 / (n : ℝ)) = -(1 / n) := by ring
    rw [this]
    have e : x - (-1 + 1 / ↑n * (2 * ↑i + 1)) = (x + 1) - (2 * i + 1) / n := by field_simp; ring
    rw [e]
    have : (2 * (i : ℝ) + 1) / n ≤ (x + 1) + 1 / n := by
      rw [div_le_iff₀ hnR, add_mul, div_mul_cancel₀ _ hnR.ne']; nlinarith
    linarith
  · have e : x - (-1 + 1 / ↑n * (2 * ↑i + 1)) = (x + 1) - (2 * i + 1) / n := by field_simp; ring
    rw [e, one_mul]
    have : (x + 1) - 1 / n ≤ (2 * (i : ℝ) + 1) / n := by
      rw [le_div_iff₀ hnR, sub_mul, div_mul_cancel₀ _ hnR.ne']; nlinarith
    linarith

theorem termCheck_spec {c : List ℤ} {B : ℚ} {lvl : ℕ} (h : termCheck c B lvl = true)
    {x y : ℝ} (hx : |x| ≤ 1) (hy : |y| ≤ 1) : peval c x y / ONE ≤ B := by
  unfold termCheck at h
  simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  have hn : 0 < 2 ^ lvl := by positivity
  obtain ⟨i, hi, hsi⟩ := grid_cover hn hx
  obtain ⟨j, hj, htj⟩ := grid_cover hn hy
  have hij := h i hi j hj
  set n := 2 ^ lvl
  set hq : ℚ := 1 / n
  have hX := TM.affine_encl (-1 + hq * (2 * i + 1)) hq 0
  have hY := TM.affine_encl (-1 + hq * (2 * j + 1)) hq 1
  have he := TM.evalAt_encl c hX hY
  set s := (x - (-1 + (1 / (n : ℝ)) * (2 * i + 1))) / (1 / (n : ℝ))
  set t := (y - (-1 + (1 / (n : ℝ)) * (2 * j + 1))) / (1 / (n : ℝ))
  have hr := (rng_spec he hsi htj).2
  have hn' : (0 : ℝ) < n := by positivity
  have hxs : ((-1 + hq * (2 * i + 1) : ℚ) : ℝ) + (hq : ℝ) * (if (0 : ℕ) = 0 then s else t) = x := by
    simp only [if_pos rfl, s, hq]; push_cast; field_simp; ring
  have hyt : ((-1 + hq * (2 * j + 1) : ℚ) : ℝ) + (hq : ℝ) * (if (1 : ℕ) = 0 then s else t) = y := by
    simp only [if_neg one_ne_zero, t, hq]; push_cast; field_simp; ring
  rw [hxs, hyt] at hr
  have hB := TM.qfloor_le_real (B * ONE)
  push_cast at hB
  set TT := TM.evalAt c (TM.affine (-1 + hq * (2 * i + 1)) hq 0) (TM.affine (-1 + hq * (2 * j + 1)) hq 1)
  have hcmp : (TT.rng.2 : ℝ) ≤ (qfloor (B * ONE) : ℝ) := by exact_mod_cast hij
  have hO := ONE_pos
  have e : (ONE : ℝ) * (peval c x y / ONE) = peval c x y := by field_simp
  rw [e] at hr
  rw [div_le_iff₀ hO]
  linarith

end OM.NNN20
