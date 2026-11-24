import Mathlib

/-!
# Monomial lower bounds on the box `[-2R,R] × [-3R,3R]` -/

noncomputable section
namespace OM.NNN18

structure Mono where
  c : ℚ
  i : ℕ
  j : ℕ

namespace Mono

def eval (m : Mono) (d y : ℝ) : ℝ := (m.c : ℝ) * d ^ m.i * y ^ m.j

/-- Range of `d^i` for `d ∈ [-2R, R]`. -/
def dLo (R : ℚ) (i : ℕ) : ℚ := if i = 0 then 1 else if i % 2 = 1 then (-2 * R) ^ i else 0
def dHi (R : ℚ) (i : ℕ) : ℚ := if i = 0 then 1 else if i % 2 = 1 then R ^ i else (2 * R) ^ i
/-- Range of `y^j` for `y ∈ [-3R, 3R]`. -/
def yLo (R : ℚ) (j : ℕ) : ℚ := if j = 0 then 1 else if j % 2 = 1 then -(3 * R) ^ j else 0
def yHi (R : ℚ) (j : ℕ) : ℚ := if j = 0 then 1 else (3 * R) ^ j

/-- The minimum of `c d^i y^j` over the four corners of the two ranges. -/
def lower (R : ℚ) (m : Mono) : ℚ :=
  min (min (m.c * (dLo R m.i * yLo R m.j)) (m.c * (dLo R m.i * yHi R m.j)))
      (min (m.c * (dHi R m.i * yLo R m.j)) (m.c * (dHi R m.i * yHi R m.j)))

lemma lin_ge_min {a a₁ a₂ b : ℝ} (h₁ : a₁ ≤ a) (h₂ : a ≤ a₂) :
    min (a₁ * b) (a₂ * b) ≤ a * b := by
  rcases le_total 0 b with hb | hb
  · exact (min_le_left _ _).trans (mul_le_mul_of_nonneg_right h₁ hb)
  · exact (min_le_right _ _).trans (mul_le_mul_of_nonpos_right h₂ hb)

lemma pow_range_d {R : ℚ} {d : ℝ} (hR : 0 ≤ R) (hd₁ : -2 * (R : ℝ) ≤ d) (hd₂ : d ≤ R)
    (i : ℕ) : ((dLo R i : ℚ) : ℝ) ≤ d ^ i ∧ d ^ i ≤ ((dHi R i : ℚ) : ℝ) := by
  have hR' : (0 : ℝ) ≤ R := by exact_mod_cast hR
  have habs : |d| ≤ 2 * R := abs_le.2 ⟨by linarith, by linarith⟩
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simp [dLo, dHi]
  rcases Nat.mod_two_eq_zero_or_one i with he | ho
  · have hev : Even i := Nat.even_iff.2 he
    have hi0 : i ≠ 0 := by omega
    have hne : i % 2 ≠ 1 := by omega
    simp only [dLo, dHi, hi0, if_false, hne]
    push_cast
    refine ⟨hev.pow_nonneg d, ?_⟩
    calc d ^ i = |d| ^ i := (hev.pow_abs d).symm
      _ ≤ (2 * R) ^ i := pow_le_pow_left₀ (abs_nonneg d) habs i
  · have hod : Odd i := Nat.odd_iff.2 ho
    have hi0 : i ≠ 0 := by omega
    simp only [dLo, dHi, hi0, if_false, ho, if_true]
    push_cast
    exact ⟨hod.strictMono_pow.monotone hd₁, hod.strictMono_pow.monotone hd₂⟩

lemma pow_range_y {R : ℚ} {y : ℝ} (hR : 0 ≤ R) (hy₁ : -(3 * (R : ℝ)) ≤ y)
    (hy₂ : y ≤ 3 * R) (j : ℕ) :
    ((yLo R j : ℚ) : ℝ) ≤ y ^ j ∧ y ^ j ≤ ((yHi R j : ℚ) : ℝ) := by
  have hR' : (0 : ℝ) ≤ R := by exact_mod_cast hR
  have habs : |y| ≤ 3 * R := abs_le.2 ⟨by linarith, by linarith⟩
  have hup : |y ^ j| ≤ (3 * (R : ℝ)) ^ j := by
    rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg y) habs j
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp [yLo, yHi]
  have hj0 : j ≠ 0 := by omega
  rcases Nat.mod_two_eq_zero_or_one j with he | ho
  · have hev : Even j := Nat.even_iff.2 he
    have hne : j % 2 ≠ 1 := by omega
    simp only [yLo, yHi, hj0, if_false, hne]
    push_cast
    exact ⟨hev.pow_nonneg y, (le_abs_self _).trans hup⟩
  · simp only [yLo, yHi, hj0, if_false, ho, if_true]
    push_cast
    exact ⟨by linarith [neg_abs_le (y ^ j)], (le_abs_self _).trans hup⟩

theorem lower_le_eval (m : Mono) {R : ℚ} {d y : ℝ} (hR : 0 ≤ R)
    (hd₁ : -2 * (R : ℝ) ≤ d) (hd₂ : d ≤ R) (hy₁ : -(3 * (R : ℝ)) ≤ y) (hy₂ : y ≤ 3 * R) :
    ((m.lower R : ℚ) : ℝ) ≤ m.eval d y := by
  obtain ⟨hdl, hdh⟩ := pow_range_d hR hd₁ hd₂ m.i
  obtain ⟨hyl, hyh⟩ := pow_range_y hR hy₁ hy₂ m.j
  set A := d ^ m.i
  set Y := y ^ m.j
  set c : ℝ := (m.c : ℝ)
  set dl : ℝ := ((dLo R m.i : ℚ) : ℝ)
  set dh : ℝ := ((dHi R m.i : ℚ) : ℝ)
  set yl : ℝ := ((yLo R m.j : ℚ) : ℝ)
  set yh : ℝ := ((yHi R m.j : ℚ) : ℝ)
  have e : m.eval d y = Y * (c * A) := by simp only [eval, A, Y, c]; ring
  rw [e]
  -- linear in Y, then linear in A
  have h1 : min (yl * (c * A)) (yh * (c * A)) ≤ Y * (c * A) := lin_ge_min hyl hyh
  have h2 : min (dl * (c * yl)) (dh * (c * yl)) ≤ A * (c * yl) := lin_ge_min hdl hdh
  have h3 : min (dl * (c * yh)) (dh * (c * yh)) ≤ A * (c * yh) := lin_ge_min hdl hdh
  have hlow : ((m.lower R : ℚ) : ℝ) =
      min (min (c * (dl * yl)) (c * (dl * yh))) (min (c * (dh * yl)) (c * (dh * yh))) := by
    simp only [lower, c, dl, dh, yl, yh]; push_cast; rfl
  rw [hlow]
  have ka : min (min (c * (dl * yl)) (c * (dl * yh))) (min (c * (dh * yl)) (c * (dh * yh)))
      ≤ min (dl * (c * yl)) (dh * (c * yl)) := by
    apply le_min
    · exact ((min_le_left _ _).trans (min_le_left _ _)).trans_eq (by ring)
    · exact ((min_le_right _ _).trans (min_le_left _ _)).trans_eq (by ring)
  have kb : min (min (c * (dl * yl)) (c * (dl * yh))) (min (c * (dh * yl)) (c * (dh * yh)))
      ≤ min (dl * (c * yh)) (dh * (c * yh)) := by
    apply le_min
    · exact ((min_le_left _ _).trans (min_le_right _ _)).trans_eq (by ring)
    · exact ((min_le_right _ _).trans (min_le_right _ _)).trans_eq (by ring)
  have t1 : A * (c * yl) = yl * (c * A) := by ring
  have t2 : A * (c * yh) = yh * (c * A) := by ring
  refine le_trans ?_ h1
  apply le_min
  · exact (ka.trans h2).trans_eq t1
  · exact (kb.trans h3).trans_eq t2

end Mono

abbrev Poly := List Mono

def Poly.eval (p : Poly) (d y : ℝ) : ℝ := (p.map fun m => m.eval d y).sum
def Poly.lower (R : ℚ) (p : Poly) : ℚ := (p.map (Mono.lower R)).sum

theorem Poly.lower_le_eval (p : Poly) {R : ℚ} {d y : ℝ} (hR : 0 ≤ R)
    (hd₁ : -2 * (R : ℝ) ≤ d) (hd₂ : d ≤ R) (hy₁ : -(3 * (R : ℝ)) ≤ y) (hy₂ : y ≤ 3 * R) :
    ((p.lower R : ℚ) : ℝ) ≤ p.eval d y := by
  induction p with
  | nil => simp [Poly.lower, Poly.eval]
  | cons m p ih =>
    simp only [Poly.lower, Poly.eval, List.map_cons, List.sum_cons, Rat.cast_add] at ih ⊢
    exact add_le_add (m.lower_le_eval hR hd₁ hd₂ hy₁ hy₂) ih

/-- A positive kernel-checked lower bound proves positivity on the box. -/
theorem Poly.pos_of_lower (p : Poly) {R : ℚ} (hR : 0 ≤ R) (hpos : 0 < p.lower R)
    {d y : ℝ} (hd₁ : -2 * (R : ℝ) ≤ d) (hd₂ : d ≤ R) (hy₁ : -(3 * (R : ℝ)) ≤ y)
    (hy₂ : y ≤ 3 * R) : 0 < p.eval d y :=
  lt_of_lt_of_le (by exact_mod_cast hpos) (p.lower_le_eval hR hd₁ hd₂ hy₁ hy₂)

end OM.NNN18
