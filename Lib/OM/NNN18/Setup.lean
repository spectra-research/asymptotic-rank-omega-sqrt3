import Lib.OM.NNN18.Basic


noncomputable section
namespace OM.NNN18

variable (P : Track)

@[simp] lemma other_01 : other 0 1 = 2 := rfl
@[simp] lemma other_02 : other 0 2 = 1 := rfl
@[simp] lemma other_10 : other 1 0 = 2 := rfl
@[simp] lemma other_12 : other 1 2 = 0 := rfl
@[simp] lemma other_20 : other 2 0 = 1 := rfl
@[simp] lemma other_21 : other 2 1 = 0 := rfl

section entries
variable (δ : Fin 3 → ℝ) (θ : Fin 3 → ℝ)
@[simp] lemma tariff_00 : tariff P δ 0 0 = P.u - P.a * δ 0 := by simp [tariff]
@[simp] lemma tariff_01 : tariff P δ 0 1 = P.v + P.b * δ 0 - P.c * (δ 1 - δ 2) := by
  simp [tariff]
@[simp] lemma tariff_02 : tariff P δ 0 2 = P.v + P.b * δ 0 - P.c * (δ 2 - δ 1) := by
  simp [tariff]
@[simp] lemma tariff_10 : tariff P δ 1 0 = P.v + P.b * δ 1 - P.c * (δ 0 - δ 2) := by
  simp [tariff]
@[simp] lemma tariff_11 : tariff P δ 1 1 = P.u - P.a * δ 1 := by simp [tariff]
@[simp] lemma tariff_12 : tariff P δ 1 2 = P.v + P.b * δ 1 - P.c * (δ 2 - δ 0) := by
  simp [tariff]
@[simp] lemma tariff_20 : tariff P δ 2 0 = P.v + P.b * δ 2 - P.c * (δ 0 - δ 1) := by
  simp [tariff]
@[simp] lemma tariff_21 : tariff P δ 2 1 = P.v + P.b * δ 2 - P.c * (δ 1 - δ 0) := by
  simp [tariff]
@[simp] lemma tariff_22 : tariff P δ 2 2 = P.u - P.a * δ 2 := by simp [tariff]
@[simp] lemma star_00 : star θ 0 0 = 0 := by simp [star]
@[simp] lemma star_01 : star θ 0 1 = θ 2 := by simp [star]
@[simp] lemma star_02 : star θ 0 2 = θ 1 := by simp [star]
end entries

/-- Parents at focus 0 and error `e`. -/
def parents0 (e : ℝ) (δ : Fin 3 → ℝ) : Fin 3 → Fin 3 → ℝ :=
  ![star (theta P δ) 0, fun j => tariff P δ 1 j + e, fun j => tariff P δ 2 j + e]

/-- The target `G_0 = C_0 + q e`. -/
def target0 (q e : ℝ) (δ : Fin 3 → ℝ) : Fin 3 → ℝ := fun j => tariff P δ 0 j + q * e

/-- Label exponents: ordinary `1`; packed `(θ_i + P_ij + P_ik)/2` off the focus. -/
def betaOrd : Fin 3 → ℝ := fun _ => 1
def betaPack (e : ℝ) (δ : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![1, (theta P δ 1 + cross (parents0 P e δ 1) 1) / 2,
    (theta P δ 2 + cross (parents0 P e δ 2) 2) / 2]

/-- The moment arguments `(θ_i - P_ij - P_ik)/β_i`. -/
def args (θ β : Fin 3 → ℝ) (Pp : Fin 3 → Fin 3 → ℝ) : Fin 3 → ℝ :=
  fun i => (θ i - cross (Pp i) i) / β i

/-- The ordinary majorant form at focus 0 (all `β = 1`; moment kinds retained/side/side). -/
def ordHat (e d y : ℝ) (x : Fin 3 → ℝ) : ℝ :=
  form0 (theta P (delta d y)) (betaOrd) (parents0 P e (delta d y))
    ![P.Lmaj 0 (args (theta P (delta d y)) betaOrd (parents0 P e (delta d y)) 0),
      P.Lmaj 1 (args (theta P (delta d y)) betaOrd (parents0 P e (delta d y)) 1),
      P.Lmaj 1 (args (theta P (delta d y)) betaOrd (parents0 P e (delta d y)) 2)]
    (dot (target0 P (19 / 20) e (delta d y)) x) x

/-- The packed majorant form at focus 0 (moment kinds retained/packed/packed). -/
def packHat (e d y : ℝ) (x : Fin 3 → ℝ) : ℝ :=
  form0 (theta P (delta d y)) (betaPack P e (delta d y)) (parents0 P e (delta d y))
    ![P.Lmaj 0 (args (theta P (delta d y)) (betaPack P e (delta d y)) (parents0 P e (delta d y)) 0),
      P.Lmaj 2 (args (theta P (delta d y)) (betaPack P e (delta d y)) (parents0 P e (delta d y)) 1),
      P.Lmaj 2 (args (theta P (delta d y)) (betaPack P e (delta d y)) (parents0 P e (delta d y)) 2)]
    (dot (target0 P (19 / 20) e (delta d y)) x) x

/-- A symmetric 3×3 quadratic form from six entries. -/
def quad3 (m00 m01 m02 m11 m12 m22 : ℝ) (x : Fin 3 → ℝ) : ℝ :=
  m00 * x 0 ^ 2 + m11 * x 1 ^ 2 + m22 * x 2 ^ 2
    + 2 * m01 * (x 0 * x 1) + 2 * m02 * (x 0 * x 2) + 2 * m12 * (x 1 * x 2)

end OM.NNN18
