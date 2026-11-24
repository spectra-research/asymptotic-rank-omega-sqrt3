import Lib.OM.NNN22.F
import PLATFORM.Statements.«R88.1»

/-! # The value function on the closed orthant: zero, Lipschitz, continuous, concave

Facts about `F = P2M.R88.Fv φ` (definitionally `OM.NNN22.Fv φ`) used in the minimax argument:
`F(0) = 0`; `F(y) ≤ F(z) + Σ_l |y_l - z_l|` for `y, z ≥ 0` (monotonicity and the slicing bound
`Fv_lipschitz` once per coordinate), hence `F` is 3-Lipschitz for the sup distance and continuous on
the orthant; and `F` is concave on the orthant (`Fv_concave`). -/

noncomputable section
open scoped BigOperators

namespace OM.NNN24.Mm

open OM.NNN22

variable (φ : OM.PolMul.Spectral ℂ)

/-- the `F` (R88.1) is the library's `Fv` -/
lemma Fv_eq : @P2M.R88.Fv = @OM.NNN22.Fv := rfl

/-- the nonnegative orthant of `ℝ³` -/
def orth : Set (Fin 3 → ℝ) := {y | ∀ l, 0 ≤ y l}

/-- `F(0) = 0` -/
lemma Fv_zero : P2M.R88.Fv φ (fun _ => 0) = 0 := by
  rw [Fv_eq]
  have h := Fv_zero_smul φ (fun _ => (0 : ℝ))
  simpa using h

/-- one unit of slack per coordinate: `F(y) ≤ F(z) + Σ_l |y_l - z_l|` on the orthant -/
lemma Fv_le_add_abs {y z : Fin 3 → ℝ} (_hy : ∀ l, 0 ≤ y l) (hz : ∀ l, 0 ≤ z l) :
    P2M.R88.Fv φ y ≤ P2M.R88.Fv φ z + (|y 0 - z 0| + |y 1 - z 1| + |y 2 - z 2|) := by
  rw [Fv_eq]
  let e : Fin 3 → ℝ := fun l => |y l - z l|
  have he0 : ∀ l, 0 ≤ e l := fun l => abs_nonneg _
  have hmono : Fv φ y ≤ Fv φ (fun l => z l + e l) :=
    Fv_mono φ (fun l => by
      have := le_abs_self (y l - z l)
      dsimp [e]
      linarith)
  let z0 : Fin 3 → ℝ := fun l => z l + (if l = 0 then e 0 else 0)
  let z1 : Fin 3 → ℝ := fun l => z0 l + (if l = 1 then e 1 else 0)
  have hz0 : ∀ l, 0 ≤ z0 l := fun l => by
    have := hz l; have := he0 0; dsimp [z0]; split_ifs <;> linarith
  have hz1 : ∀ l, 0 ≤ z1 l := fun l => by
    have := hz0 l; have := he0 1; dsimp [z1]; split_ifs <;> linarith
  have h0 := Fv_lipschitz φ hz (he0 0) 0
  have h1 := Fv_lipschitz φ hz0 (he0 1) 1
  have h2 := Fv_lipschitz φ hz1 (he0 2) 2
  have hfin : (fun l => z1 l + if l = 2 then e 2 else 0) = fun l => z l + e l := by
    funext l
    fin_cases l <;> simp [z1, z0]
  rw [hfin] at h2
  change Fv φ z0 ≤ _ at h0
  change Fv φ z1 ≤ _ at h1
  change Fv φ y ≤ _
  dsimp [e] at h0 h1 h2 ⊢
  linarith

/-- `F` is 3-Lipschitz on the orthant for the sup distance -/
lemma Fv_lipschitzOn : LipschitzOnWith 3 (P2M.R88.Fv φ) orth := by
  apply LipschitzOnWith.of_dist_le_mul
  intro y hy z hz
  have hd : ∀ l, |y l - z l| ≤ dist y z := fun l => by
    rw [← Real.dist_eq]; exact dist_le_pi_dist y z l
  have hd' : ∀ l, |z l - y l| ≤ dist y z := fun l => by
    rw [abs_sub_comm]; exact hd l
  have h1 := Fv_le_add_abs φ hy hz
  have h2 := Fv_le_add_abs φ hz hy
  rw [Real.dist_eq, abs_le]
  push_cast
  constructor
  · linarith [hd' 0, hd' 1, hd' 2]
  · linarith [hd 0, hd 1, hd 2]

lemma Fv_continuousOn : ContinuousOn (P2M.R88.Fv φ) orth :=
  (Fv_lipschitzOn φ).continuousOn

lemma convex_orth : Convex ℝ orth := by
  intro y hy z hz a b ha hb _ l
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  exact add_nonneg (mul_nonneg ha (hy l)) (mul_nonneg hb (hz l))

/-- `F` is concave on the orthant -/
lemma Fv_concaveOn : ConcaveOn ℝ orth (P2M.R88.Fv φ) := by
  refine ⟨convex_orth, ?_⟩
  intro y hy z hz a b ha hb hab
  have hb' : b = 1 - a := by linarith
  subst hb'
  have h := Fv_concave φ hy hz ha (by linarith)
  simp only [smul_eq_mul]
  rw [Fv_eq]
  convert h using 2

end OM.NNN24.Mm

