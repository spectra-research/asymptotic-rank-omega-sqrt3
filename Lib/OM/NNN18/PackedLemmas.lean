import Lib.OM.NNN18.PackedHinge

/-!
# Generic algebra for the packed base -/

noncomputable section
open Set
namespace OM.NNN18

def symE (u v : Fin 3 → ℝ) (j k : Fin 3) : ℝ := (u j * v k + u k * v j) / 2

/-- The pair terms of the source form at focus 0. -/
def pairE (θ L : Fin 3 → ℝ) : Fin 3 → Fin 3 → ℝ :=
  ![![0, -(11 / 2) * θ 2 - θ 2 * L 2 / 2, -(11 / 2) * θ 1 - θ 1 * L 1 / 2],
    ![-(11 / 2) * θ 2 - θ 2 * L 2 / 2, 0, -5 * θ 0 - 5 / 11 * θ 0 * L 0],
    ![-(11 / 2) * θ 1 - θ 1 * L 1 / 2, -5 * θ 0 - 5 / 11 * θ 0 * L 0, 0]]

/-- The source matrix at focus 0. -/
def gE (θ β : Fin 3 → ℝ) (P : Fin 3 → Fin 3 → ℝ) (L G : Fin 3 → ℝ) (j k : Fin 3) : ℝ :=
  symE ![6, 5, 5] G j k + θ 0 / β 0 * symE ![0, 5, 5] (fun i => G i - P 0 i) j k
    + θ 1 / β 1 * symE ![6, 5, 5] (fun i => G i - P 1 i) j k
    + θ 2 / β 2 * symE ![6, 5, 5] (fun i => G i - P 2 i) j k + pairE θ L j k

set_option maxHeartbeats 1000000 in
theorem form0_eq_quad3 (θ β : Fin 3 → ℝ) (P : Fin 3 → Fin 3 → ℝ) (L G x : Fin 3 → ℝ) :
    form0 θ β P L (dot G x) x =
      quad3 (gE θ β P L G 0 0) (gE θ β P L G 0 1) (gE θ β P L G 0 2) (gE θ β P L G 1 1)
        (gE θ β P L G 1 2) (gE θ β P L G 2 2) x := by
  simp only [form0, gE, symE, pairE, quad3, dot, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.isValue]
  ring

/-- `ρ/(h+ky) + ρ/(h-ky) ≥ 2ρ/h` for `ρ ≥ 0` and positive denominators. -/
theorem ratPair_ge_center {A ρ h k y : ℝ} (hρ : 0 ≤ ρ) (hh : 0 < h) (h1 : 0 < h + k * y)
    (h2 : 0 < h - k * y) :
    ratPart A 0 ρ 0 h k 0 + ratPart 0 0 ρ 0 h (-k) 0 ≤
      ratPart A 0 ρ 0 h k y + ratPart 0 0 ρ 0 h (-k) y := by
  have e2 : h + -k * y = h - k * y := by ring
  simp only [ratPart, mul_zero, add_zero, zero_div, e2]
  have key : ρ / (h + k * y) + ρ / (h - k * y) - (ρ / h + ρ / h)
      = 2 * ρ * k ^ 2 * y ^ 2 / (h * (h + k * y) * (h - k * y)) := by
    field_simp; ring
  have : 0 ≤ 2 * ρ * k ^ 2 * y ^ 2 / (h * (h + k * y) * (h - k * y)) := by positivity
  linarith

lemma hingeCurv_eq {μ κ U V h y : ℝ} (hκ : κ ≠ 0) :
    hingeCurv (-(5 * μ / κ ^ 2) * U) (5 * μ / κ ^ 2 * V) h (κ / 2) y =
      5 * μ / 2 * (V / (h - κ / 2 * y) ^ 3 - U / (h + κ / 2 * y) ^ 3) := by
  unfold hingeCurv
  field_simp
  ring

theorem hinge_curv_bounds {μ κ bs R H K U₀ U₁ V₀ V₁ d y : ℝ}
    (hμ : 0 < μ) (hκ : 0 < κ) (hR : 0 < R) (hH : 0 ≤ H)
    (hU₁ : U₁ ≤ 0) (hV₁ : 0 ≤ V₁) (hUR : 0 < U₀ + U₁ * R) (hV : 0 ≤ V₀ + V₁ * (-2 * R))
    -- positivity of the denominators that occur
    (hbH : 0 < bs - κ / 2 * R - κ / 2 * H) (hb3 : 0 < bs - 2 * κ * R)
    (hgH : V₀ + V₁ * R ≤ (U₀ + U₁ * R) *
      ((bs - κ / 2 * R - κ / 2 * H) / (bs - κ / 2 * R + κ / 2 * H)) ^ 3)
    (hg3 : 5 * μ / 2 * ((V₀ + V₁ * R) / (bs - 2 * κ * R) ^ 3
        - (U₀ + U₁ * R) / (bs + κ * R) ^ 3) ≤ 2 * K)
    (hd₁ : -2 * R ≤ d) (hd₂ : d ≤ R) (hy₁ : -(d + 2 * R) ≤ y) (hy₂ : y ≤ d + 2 * R) :
    (y ≤ H → 5 * μ / 2 * ((V₀ + V₁ * d) / (bs - κ * d / 2 - κ / 2 * y) ^ 3
        - (U₀ + U₁ * d) / (bs - κ * d / 2 + κ / 2 * y) ^ 3) ≤ 0) ∧
    (H ≤ y → 5 * μ / 2 * ((V₀ + V₁ * d) / (bs - κ * d / 2 - κ / 2 * y) ^ 3
        - (U₀ + U₁ * d) / (bs - κ * d / 2 + κ / 2 * y) ^ 3) ≤ 2 * K) := by
  set Ud := U₀ + U₁ * d
  set Vd := V₀ + V₁ * d
  have hUd : U₀ + U₁ * R ≤ Ud := by
    simp only [Ud]; nlinarith [mul_le_mul_of_nonpos_left hd₂ hU₁]
  have hVd : Vd ≤ V₀ + V₁ * R := by
    simp only [Vd]; nlinarith [mul_le_mul_of_nonneg_left hd₂ hV₁]
  have hVd0 : 0 ≤ Vd := by
    simp only [Vd]; nlinarith [mul_le_mul_of_nonneg_left hd₁ hV₁]
  have hUd0 : 0 < Ud := lt_of_lt_of_le hUR hUd
  have kd₂ := mul_le_mul_of_nonneg_left hd₂ hκ.le
  have kd₁ := mul_le_mul_of_nonneg_left hd₁ hκ.le
  have ky₂ := mul_le_mul_of_nonneg_left hy₂ hκ.le
  have ky₁ := mul_le_mul_of_nonneg_left hy₁ hκ.le
  have kH := mul_nonneg hκ.le hH
  have kR := mul_pos hκ hR
  set b1 := bs - κ * d / 2 + κ / 2 * y
  set b2 := bs - κ * d / 2 - κ / 2 * y
  have hb2 : 0 < b2 := by simp only [b2]; linarith
  have hb1 : 0 < b1 := by simp only [b1]; linarith
  constructor
  · intro hyH
    -- compare with y = H and then d = R
    have kyH := mul_le_mul_of_nonneg_left hyH hκ.le
    set c1 := bs - κ * d / 2 + κ / 2 * H
    set c2 := bs - κ * d / 2 - κ / 2 * H
    have hc2 : 0 < c2 := by simp only [c2]; linarith
    have hc1 : 0 < c1 := by simp only [c1]; linarith
    have hb1c : b1 ≤ c1 := by simp only [b1, c1]; linarith
    have hc2b : c2 ≤ b2 := by simp only [b2, c2]; linarith
    -- ratio monotone in d: c2/c1 ≥ (bs-κR/2-κH/2)/(bs-κR/2+κH/2)
    have hden : 0 < bs - κ / 2 * R + κ / 2 * H := by linarith
    have hrat : (bs - κ / 2 * R - κ / 2 * H) / (bs - κ / 2 * R + κ / 2 * H) ≤ c2 / c1 := by
      rw [div_le_div_iff₀ hden hc1]
      have key : c2 * (bs - κ / 2 * R + κ / 2 * H) - (bs - κ / 2 * R - κ / 2 * H) * c1
          = κ * H * (κ * R - κ * d) / 2 := by simp only [c1, c2]; ring
      have : 0 ≤ κ * H * (κ * R - κ * d) / 2 := by
        apply div_nonneg _ (by norm_num); exact mul_nonneg kH (by linarith)
      linarith
    have hrat0 : 0 ≤ (bs - κ / 2 * R - κ / 2 * H) / (bs - κ / 2 * R + κ / 2 * H) :=
      div_nonneg hbH.le hden.le
    have hV' : Vd ≤ Ud * (c2 / c1) ^ 3 := by
      calc Vd ≤ V₀ + V₁ * R := hVd
        _ ≤ (U₀ + U₁ * R) * ((bs - κ / 2 * R - κ / 2 * H) / (bs - κ / 2 * R + κ / 2 * H)) ^ 3 := hgH
        _ ≤ Ud * (c2 / c1) ^ 3 := mul_le_mul hUd (pow_le_pow_left₀ hrat0 hrat 3)
            (by positivity) hUd0.le
    -- V/b2³ ≤ V/c2³ ≤ U/c1³ ≤ U/b1³
    have s1 : Vd / b2 ^ 3 ≤ Vd / c2 ^ 3 :=
      div_le_div_of_nonneg_left hVd0 (by positivity) (pow_le_pow_left₀ hc2.le hc2b 3)
    have s2 : Vd / c2 ^ 3 ≤ Ud / c1 ^ 3 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have := mul_le_mul_of_nonneg_right hV' (by positivity : (0 : ℝ) ≤ c1 ^ 3 * c2 ^ 3)
      rw [div_pow] at this
      field_simp at this
      nlinarith [this]
    have s3 : Ud / c1 ^ 3 ≤ Ud / b1 ^ 3 :=
      div_le_div_of_nonneg_left hUd0.le (by positivity) (pow_le_pow_left₀ hb1.le hb1c 3)
    have : Vd / b2 ^ 3 - Ud / b1 ^ 3 ≤ 0 := by linarith
    nlinarith
  · intro _
    -- compare with y = d + 2R and then d = R
    set r0 := bs - κ * (d + R)
    have hr0 : 0 < r0 := by simp only [r0]; linarith
    have hb2r : r0 ≤ b2 := by simp only [b2, r0]; linarith
    have hb1s : bs + κ * R ≥ b1 := by simp only [b1]; linarith
    have hrR : bs - 2 * κ * R ≤ r0 := by simp only [r0]; linarith
    have s1 : Vd / b2 ^ 3 ≤ (V₀ + V₁ * R) / (bs - 2 * κ * R) ^ 3 := by
      calc Vd / b2 ^ 3 ≤ Vd / r0 ^ 3 :=
            div_le_div_of_nonneg_left hVd0 (by positivity) (pow_le_pow_left₀ hr0.le hb2r 3)
        _ ≤ Vd / (bs - 2 * κ * R) ^ 3 :=
            div_le_div_of_nonneg_left hVd0 (by positivity) (pow_le_pow_left₀ hb3.le hrR 3)
        _ ≤ (V₀ + V₁ * R) / (bs - 2 * κ * R) ^ 3 :=
            div_le_div_of_nonneg_right hVd (by positivity)
    have s2 : (U₀ + U₁ * R) / (bs + κ * R) ^ 3 ≤ Ud / b1 ^ 3 := by
      have hbs : 0 ≤ (bs + κ * R) ^ 3 := by
        have : 0 < bs + κ * R := by linarith
        positivity
      calc (U₀ + U₁ * R) / (bs + κ * R) ^ 3 ≤ Ud / (bs + κ * R) ^ 3 :=
            div_le_div_of_nonneg_right hUd hbs
        _ ≤ Ud / b1 ^ 3 :=
            div_le_div_of_nonneg_left hUd0.le (by positivity) (pow_le_pow_left₀ hb1.le hb1s 3)
    have : 5 * μ / 2 * (Vd / b2 ^ 3 - Ud / b1 ^ 3) ≤
        5 * μ / 2 * ((V₀ + V₁ * R) / (bs - 2 * κ * R) ^ 3 - (U₀ + U₁ * R) / (bs + κ * R) ^ 3) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      linarith
    linarith

end OM.NNN18
