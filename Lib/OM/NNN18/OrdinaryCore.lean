import Lib.OM.NNN18.Setup

/-!
* `quad3_nonneg_of_dd`: the five low-endpoint polynomials (row sums above 1/2, at most one
  positive off-diagonal entry per row, bounded by 1/5) make the form nonnegative.
* `quad3_nonneg_of_pos`: entrywise positivity on nonnegative vectors.
* `ordHat_chord`: for fixed `d, y, x`, the ordinary majorant form is a concave quadratic
  in `e` (only the side moment majorants depend on `e` nonlinearly), so it lies above
  its chord.
-/

noncomputable section
namespace OM.NNN18

theorem quad3_nonneg_of_dd {m00 m01 m02 m11 m12 m22 : ℝ}
    (r0 : 1 / 2 ≤ m00 + m01 + m02) (r1 : 1 / 2 ≤ m01 + m11 + m12)
    (r2 : 1 / 2 ≤ m02 + m12 + m22) (o01 : m01 ≤ 1 / 5) (o02 : m02 ≤ 1 / 5)
    (o12 : m12 ≤ 0) (s0 : m01 + m02 ≤ 0) (x : Fin 3 → ℝ) :
    0 ≤ quad3 m00 m01 m02 m11 m12 m22 x := by
  unfold quad3
  have q12 := mul_nonneg (neg_nonneg.2 o12) (sq_nonneg (x 1 - x 2))
  rcases le_total 0 m01 with h01 | h01
  · -- m01 ≥ 0, so m02 ≤ 0
    have h02 : m02 ≤ 0 := by linarith
    have a := mul_nonneg h01 (sq_nonneg (x 0 + x 1))
    have b := mul_nonneg (neg_nonneg.2 h02) (sq_nonneg (x 0 - x 2))
    have c0 := mul_nonneg (show 0 ≤ m00 - m01 + m02 by linarith) (sq_nonneg (x 0))
    have c1 := mul_nonneg (show 0 ≤ m11 - m01 + m12 by linarith) (sq_nonneg (x 1))
    have c2 := mul_nonneg (show 0 ≤ m22 + m02 + m12 by linarith) (sq_nonneg (x 2))
    nlinarith only [a, b, q12, c0, c1, c2]
  · rcases le_total 0 m02 with h02 | h02
    · have a := mul_nonneg (neg_nonneg.2 h01) (sq_nonneg (x 0 - x 1))
      have b := mul_nonneg h02 (sq_nonneg (x 0 + x 2))
      have c0 := mul_nonneg (show 0 ≤ m00 + m01 - m02 by linarith) (sq_nonneg (x 0))
      have c1 := mul_nonneg (show 0 ≤ m11 + m01 + m12 by linarith) (sq_nonneg (x 1))
      have c2 := mul_nonneg (show 0 ≤ m22 - m02 + m12 by linarith) (sq_nonneg (x 2))
      nlinarith only [a, b, q12, c0, c1, c2]
    · have a := mul_nonneg (neg_nonneg.2 h01) (sq_nonneg (x 0 - x 1))
      have b := mul_nonneg (neg_nonneg.2 h02) (sq_nonneg (x 0 - x 2))
      have c0 := mul_nonneg (show 0 ≤ m00 + m01 + m02 by linarith) (sq_nonneg (x 0))
      have c1 := mul_nonneg (show 0 ≤ m11 + m01 + m12 by linarith) (sq_nonneg (x 1))
      have c2 := mul_nonneg (show 0 ≤ m22 + m02 + m12 by linarith) (sq_nonneg (x 2))
      nlinarith only [a, b, q12, c0, c1, c2]

theorem quad3_nonneg_of_pos {m00 m01 m02 m11 m12 m22 : ℝ}
    (h00 : 0 ≤ m00) (h01 : 0 ≤ m01) (h02 : 0 ≤ m02) (h11 : 0 ≤ m11) (h12 : 0 ≤ m12)
    (h22 : 0 ≤ m22) {x : Fin 3 → ℝ} (hx : ∀ i, 0 ≤ x i) :
    0 ≤ quad3 m00 m01 m02 m11 m12 m22 x := by
  unfold quad3
  have := hx 0; have := hx 1; have := hx 2
  positivity

variable (P : Track)

/-- The curvature of `e ↦ ordHat P e d y x`: four times the side curvature, times the
nonnegative side moment weights. -/
def ordCurv (d y : ℝ) (x : Fin 3 → ℝ) : ℝ :=
  4 * (Track.K 1 : ℝ) * (theta P (delta d y) 1 * (x 0 * x 2) + theta P (delta d y) 2 * (x 0 * x 1))

/-- `e ↦ ordHat` is the quadratic `α + βe - ordCurv e²`; hence the chord identity. -/
theorem ordHat_chord (e₁ e₂ e d y : ℝ) (x : Fin 3 → ℝ) :
    (e₂ - e₁) * ordHat P e d y x =
      (e₂ - e) * ordHat P e₁ d y x + (e - e₁) * ordHat P e₂ d y x
        + (e₂ - e₁) * ordCurv P d y x * ((e - e₁) * (e₂ - e)) := by
  simp only [ordHat, ordCurv, form0, parents0, target0, betaOrd, args, theta, delta, cross, dot,
    star, tariff, other, Track.Lmaj, Track.z0, Track.K,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, Fin.isValue, ite_true, ite_false, ↓reduceIte]
  norm_num
  ring

theorem ordHat_nonneg_between {e₁ e₂ e d y : ℝ} {x : Fin 3 → ℝ} (h12 : e₁ < e₂)
    (he₁ : e₁ ≤ e) (he₂ : e ≤ e₂) (hcurv : 0 ≤ ordCurv P d y x)
    (h₁ : 0 ≤ ordHat P e₁ d y x) (h₂ : 0 ≤ ordHat P e₂ d y x) : 0 ≤ ordHat P e d y x := by
  have hc := ordHat_chord P e₁ e₂ e d y x
  have hpos : 0 < e₂ - e₁ := by linarith
  have t1 := mul_nonneg (sub_nonneg.2 he₂) h₁
  have t2 := mul_nonneg (sub_nonneg.2 he₁) h₂
  have t3 := mul_nonneg (mul_nonneg hpos.le hcurv)
    (mul_nonneg (sub_nonneg.2 he₁) (sub_nonneg.2 he₂))
  have : 0 ≤ (e₂ - e₁) * ordHat P e d y x := by rw [hc]; linarith
  exact (mul_nonneg_iff_of_pos_left hpos).1 this

end OM.NNN18
