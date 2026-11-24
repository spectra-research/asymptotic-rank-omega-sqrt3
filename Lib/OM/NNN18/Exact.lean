import Lib.OM.NNN18.Derivative
import Lib.OM.NNN18.MomentCore

/-!
# The exact-moment source forms at focus 0

`ordExact`, `packExact`: the source form with the complete moment `ell` on every bond
(ordinary, resp. packed charging), at focus 0 in the coordinates `d = δ₀`, `y = δ₁ - δ₂`.
-/

noncomputable section
open Set
namespace OM.NNN18

variable (P : Track)

def exactL (θ β : Fin 3 → ℝ) (Pp : Fin 3 → Fin 3 → ℝ) : Fin 3 → ℝ := fun i => ell (args θ β Pp i)

def ordExact (e d y : ℝ) (x : Fin 3 → ℝ) : ℝ :=
  form0 (theta P (delta d y)) betaOrd (parents0 P e (delta d y))
    (exactL (theta P (delta d y)) betaOrd (parents0 P e (delta d y)))
    (dot (target0 P (19 / 20) e (delta d y)) x) x

def packExact (e d y : ℝ) (x : Fin 3 → ℝ) : ℝ :=
  form0 (theta P (delta d y)) (betaPack P e (delta d y)) (parents0 P e (delta d y))
    (exactL (theta P (delta d y)) (betaPack P e (delta d y)) (parents0 P e (delta d y)))
    (dot (target0 P (19 / 20) e (delta d y)) x) x

lemma form0_moment_mono {θ β : Fin 3 → ℝ} {Pp : Fin 3 → Fin 3 → ℝ} {L L' : Fin 3 → ℝ} {F : ℝ}
    {x : Fin 3 → ℝ} (hθ : ∀ i, 0 ≤ θ i) (hx : ∀ i, 0 ≤ x i) (hL : ∀ i, L i ≤ L' i) :
    form0 θ β Pp L' F x ≤ form0 θ β Pp L F x := by
  unfold form0
  have p0 := mul_nonneg (mul_nonneg (hθ 0) (mul_nonneg (hx 1) (hx 2))) (sub_nonneg.2 (hL 0))
  have p1 := mul_nonneg (mul_nonneg (hθ 1) (mul_nonneg (hx 0) (hx 2))) (sub_nonneg.2 (hL 1))
  have p2 := mul_nonneg (mul_nonneg (hθ 2) (mul_nonneg (hx 0) (hx 1))) (sub_nonneg.2 (hL 2))
  nlinarith

lemma quad3_mono {m00 m01 m02 m11 m12 m22 n00 n01 n02 n11 n12 n22 : ℝ} {x : Fin 3 → ℝ}
    (hx : ∀ i, 0 ≤ x i) (h00 : m00 ≤ n00) (h01 : m01 ≤ n01) (h02 : m02 ≤ n02) (h11 : m11 ≤ n11)
    (h12 : m12 ≤ n12) (h22 : m22 ≤ n22) :
    quad3 m00 m01 m02 m11 m12 m22 x ≤ quad3 n00 n01 n02 n11 n12 n22 x := by
  unfold quad3
  have a := mul_le_mul_of_nonneg_right h00 (sq_nonneg (x 0))
  have b := mul_le_mul_of_nonneg_right h11 (sq_nonneg (x 1))
  have c := mul_le_mul_of_nonneg_right h22 (sq_nonneg (x 2))
  have d := mul_le_mul_of_nonneg_right h01 (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) (mul_nonneg (hx 0) (hx 1)))
  have e := mul_le_mul_of_nonneg_right h02 (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) (mul_nonneg (hx 0) (hx 2)))
  have f := mul_le_mul_of_nonneg_right h12 (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) (mul_nonneg (hx 1) (hx 2)))
  nlinarith

lemma betaPack_e (e : ℝ) (δ : Fin 3 → ℝ) :
    betaPack P e δ = ![1, betaPack P 0 δ 1 + e, betaPack P 0 δ 2 + e] := by
  funext i
  fin_cases i <;> simp [betaPack, parents0, cross] <;> ring

lemma parents0_eq (e : ℝ) (δ : Fin 3 → ℝ) :
    parents0 P e δ = ![star (theta P δ) 0, fun i => tariff P δ 1 i + e, fun i => tariff P δ 2 i + e] :=
  rfl

/-- Scalar form of the monotonicity of the packed moment argument `z = -2 + 2θ/(β₀+e)`. -/
lemma arg_anti_scalar {θ η e : ℝ} (hθ : 0 ≤ θ) (hβ : 0 < (θ + η) / 2) (he : 0 ≤ e) :
    (θ - (η + 2 * e)) / ((θ + η) / 2 + e) ≤ (θ - η) / ((θ + η) / 2) := by
  have hβe : 0 < (θ + η) / 2 + e := by linarith
  rw [div_le_div_iff₀ hβe hβ]
  nlinarith

lemma args_pack_eq1 (e : ℝ) (δ : Fin 3 → ℝ) :
    args (theta P δ) (betaPack P e δ) (parents0 P e δ) 1 =
      (theta P δ 1 - ((tariff P δ 1 0 + tariff P δ 1 2) + 2 * e)) /
        ((theta P δ 1 + (tariff P δ 1 0 + tariff P δ 1 2)) / 2 + e) := by
  simp only [args, betaPack, parents0, cross, Matrix.cons_val_one, Matrix.cons_val_zero,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  ring

lemma args_pack_eq2 (e : ℝ) (δ : Fin 3 → ℝ) :
    args (theta P δ) (betaPack P e δ) (parents0 P e δ) 2 =
      (theta P δ 2 - ((tariff P δ 2 0 + tariff P δ 2 1) + 2 * e)) /
        ((theta P δ 2 + (tariff P δ 2 0 + tariff P δ 2 1)) / 2 + e) := by
  simp only [args, betaPack, parents0, cross, Matrix.cons_val_one, Matrix.cons_val_zero,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  ring

lemma betaPack0_eq1 (δ : Fin 3 → ℝ) :
    betaPack P 0 δ 1 = (theta P δ 1 + (tariff P δ 1 0 + tariff P δ 1 2)) / 2 := by
  simp only [betaPack, parents0, cross, Matrix.cons_val_one, Matrix.cons_val_zero,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  ring

lemma betaPack0_eq2 (δ : Fin 3 → ℝ) :
    betaPack P 0 δ 2 = (theta P δ 2 + (tariff P δ 2 0 + tariff P δ 2 1)) / 2 := by
  simp only [betaPack, parents0, cross, Matrix.cons_val_one, Matrix.cons_val_zero,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  ring

lemma args_pack_eq0 (e : ℝ) (δ : Fin 3 → ℝ) :
    args (theta P δ) (betaPack P e δ) (parents0 P e δ) 0 =
      args (theta P δ) (betaPack P 0 δ) (parents0 P 0 δ) 0 := by
  simp only [args, betaPack, parents0, cross, Matrix.cons_val_one, Matrix.cons_val_zero,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]

/-- The packed exact moments do not increase with the error. -/
lemma exactL_pack_anti {e : ℝ} (he : 0 ≤ e) (δ : Fin 3 → ℝ)
    (hθ1 : 0 ≤ theta P δ 1) (hθ2 : 0 ≤ theta P δ 2)
    (hβ1 : 0 < betaPack P 0 δ 1) (hβ2 : 0 < betaPack P 0 δ 2) (i : Fin 3) :
    exactL (theta P δ) (betaPack P e δ) (parents0 P e δ) i ≤
      exactL (theta P δ) (betaPack P 0 δ) (parents0 P 0 δ) i := by
  unfold exactL
  apply ell_mono
  fin_cases i
  · exact (args_pack_eq0 P e δ).le
  · show args (theta P δ) (betaPack P e δ) (parents0 P e δ) 1 ≤
      args (theta P δ) (betaPack P 0 δ) (parents0 P 0 δ) 1
    have h0 := args_pack_eq1 P 0 δ
    simp only [mul_zero, add_zero] at h0
    rw [args_pack_eq1, h0]
    rw [betaPack0_eq1] at hβ1
    have := arg_anti_scalar hθ1 hβ1 he
    simpa using this
  · show args (theta P δ) (betaPack P e δ) (parents0 P e δ) 2 ≤
      args (theta P δ) (betaPack P 0 δ) (parents0 P 0 δ) 2
    have h0 := args_pack_eq2 P 0 δ
    simp only [mul_zero, add_zero] at h0
    rw [args_pack_eq2, h0]
    rw [betaPack0_eq2] at hβ2
    have := arg_anti_scalar hθ2 hβ2 he
    simpa using this

theorem packExact_mono {e d y : ℝ} (he : 0 ≤ e) {x : Fin 3 → ℝ} (hx : ∀ i, 0 ≤ x i)
    (hθ : ∀ i, 0 ≤ theta P (delta d y) i) (hθ0 : 1 / 5 ≤ theta P (delta d y) 0)
    (hθ1 : theta P (delta d y) 1 ≤ 86 / 100) (hθ2 : theta P (delta d y) 2 ≤ 86 / 100)
    (hβ1 : 64 / 100 ≤ betaPack P 0 (delta d y) 1) (hβ2 : 64 / 100 ≤ betaPack P 0 (delta d y) 2)
    (hA₁ : ∀ i, tariff P (delta d y) 0 i - tariff P (delta d y) 1 i
      + (1 - 19 / 20) * betaPack P 0 (delta d y) 1 ≤ 16 / 100)
    (hA₂ : ∀ i, tariff P (delta d y) 0 i - tariff P (delta d y) 2 i
      + (1 - 19 / 20) * betaPack P 0 (delta d y) 2 ≤ 16 / 100) :
    packExact P 0 d y x ≤ packExact P e d y x := by
  have hL := exactL_pack_anti P he (delta d y) (hθ 1) (hθ 2) (by linarith) (by linarith)
  have hm := fun j k => gE_mono_packed (theta P (delta d y))
    (exactL (theta P (delta d y)) (betaPack P 0 (delta d y)) (parents0 P 0 (delta d y)))
    (exactL (theta P (delta d y)) (betaPack P e (delta d y)) (parents0 P e (delta d y)))
    (tariff P (delta d y) 0) (tariff P (delta d y) 1) (tariff P (delta d y) 2)
    (star (theta P (delta d y)) 0) (betaPack P 0 (delta d y) 1) (betaPack P 0 (delta d y) 2) e he
    hθ hθ0 hθ1 hθ2 hβ1 hβ2 hA₁ hA₂ hL j k
  unfold packExact
  rw [form0_eq_quad3, form0_eq_quad3]
  set L0 := exactL (theta P (delta d y)) (betaPack P 0 (delta d y)) (parents0 P 0 (delta d y))
  set Le := exactL (theta P (delta d y)) (betaPack P e (delta d y)) (parents0 P e (delta d y))
  have e0 : betaPack P 0 (delta d y) =
      ![1, betaPack P 0 (delta d y) 1, betaPack P 0 (delta d y) 2] := by
    have := betaPack_e P 0 (delta d y); simpa using this
  rw [betaPack_e P e (delta d y)]
  rw [e0]
  exact quad3_mono hx (hm 0 0) (hm 0 1) (hm 0 2) (hm 1 1) (hm 1 2) (hm 2 2)

end OM.NNN18
