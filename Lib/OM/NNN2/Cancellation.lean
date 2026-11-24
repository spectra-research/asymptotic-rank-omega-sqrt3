import Lib.OM.NNN.Extraction

/-! Two explicit cancellation sources for arbitrary ordinary and residual maps.
The polynomial parameter is supplied by `Raw.extract`: first and second residual
rows have weight 1, ordinary third rows weight 2, and residual third rows weight 0.
Thus the target is the coefficient of degree 2 and every lower coefficient vanishes.
This is the projected arbitrary-head degeneration. -/

noncomputable section
open scoped BigOperators Classical
set_option maxHeartbeats 1000000
namespace OM.NNN2
open CoordinateTensor OM.NNN.Raw

variable {I J K A B C D E H : Type}

/-- The source with basis sum `αₓ βₓₕ γₕ`. -/
def auxLeft (A H : Type) : Tensor ℂ A (A × H) H :=
  fun a b h => if a = b.1 ∧ b.2 = h then 1 else 0

/-- The source with basis sum `δᵧₕ ηᵧ ζₕ`. -/
def auxRight (B H : Type) : Tensor ℂ (B × H) B H :=
  fun a b h => if a.1 = b ∧ a.2 = h then 1 else 0

theorem map_auxLeft [Fintype A] [Fintype H]
    (U : D → A → ℂ) (V : E → A × H → ℂ) (W : C → H → ℂ) (d e c) :
    mapTensor U V W (auxLeft A H) d e c =
      ∑ a, ∑ h, U d a * V e (a, h) * W c h := by
  simp [mapTensor, auxLeft, Fintype.sum_prod_type, mul_ite, ite_and,
    Finset.sum_ite_irrel]

theorem map_auxRight [Fintype B] [Fintype H]
    (U : D → B × H → ℂ) (V : E → B → ℂ) (W : C → H → ℂ) (d e c) :
    mapTensor U V W (auxRight B H) d e c =
      ∑ b, ∑ h, U d (b, h) * V e b * W c h := by
  simp [mapTensor, auxRight, Fintype.sum_prod_type, mul_ite, ite_and,
    Finset.sum_ite_irrel]

/-- The cancellation arrays are the three mixed contractions of the fixed source.
No condition on the tensor entries or on any slice is imposed. -/
theorem arbitrary_head [Fintype I] [Fintype J] [Fintype K]
    [Fintype A] [Fintype B] [Fintype C] [Fintype D] [Fintype E] [Fintype H]
    (S : Tensor ℂ I J K)
    (U : A → I → ℂ) (V : B → J → ℂ) (W : C → K → ℂ)
    (U' : D → I → ℂ) (V' : E → J → ℂ) (W' : H → K → ℂ) :
    Degenerates (directSum S (directSum (auxLeft A H) (auxRight B H)))
      (directSum (mapTensor U V W S) (mapTensor U' V' W' S)) := by
  let Q := mapTensor U V W' S
  let M := mapTensor U V' W' S
  let L := mapTensor U' V W' S
  let u : A → I ⊕ (A ⊕ B × H) → ℂ := fun a =>
    Sum.elim (U a) (Sum.elim (fun x => if a = x then 1 else 0) (fun _ => 0))
  let v : B → J ⊕ ((A × H) ⊕ B) → ℂ := fun b =>
    Sum.elim (V b) (Sum.elim (fun x => -Q x.1 b x.2) (fun y => if b = y then 1 else 0))
  let w : C → K ⊕ (H ⊕ H) → ℂ := fun c =>
    Sum.elim (W c) (fun _ => 0)
  let u' : D → I ⊕ (A ⊕ B × H) → ℂ := fun d =>
    Sum.elim (U' d) (Sum.elim (fun _ => 0) (fun y => -L d y.1 y.2))
  let v' : E → J ⊕ ((A × H) ⊕ B) → ℂ := fun e =>
    Sum.elim (V' e) (Sum.elim (fun x => -M x.1 e x.2) (fun _ => 0))
  let w' : H → K ⊕ (H ⊕ H) → ℂ := fun h =>
    Sum.elim (W' h) (Sum.elim (fun x => if x = h then 1 else 0)
      (fun x => if x = h then 1 else 0))
  have h00 : mapTensor u v w' (directSum S (directSum (auxLeft A H) (auxRight B H))) = 0 := by
    funext a b h
    simp [mapTensor_directSum, u, v, w', map_auxLeft, map_auxRight, mul_ite,
      ite_mul, Finset.sum_ite_irrel, Q]
  have h10 : mapTensor u' v w' (directSum S (directSum (auxLeft A H) (auxRight B H))) = 0 := by
    funext d b h
    simp [mapTensor_directSum, u', v, w', map_auxLeft, map_auxRight, mul_ite,
      ite_mul, Finset.sum_ite_irrel, L]
  have h01 : mapTensor u v' w' (directSum S (directSum (auxLeft A H) (auxRight B H))) = 0 := by
    funext a e h
    simp [mapTensor_directSum, u, v', w', map_auxLeft, map_auxRight, mul_ite,
      ite_mul, Finset.sum_ite_irrel, M]
  have hp : mapTensor u v w (directSum S (directSum (auxLeft A H) (auxRight B H))) =
      mapTensor U V W S := by
    funext a b c
    simp [mapTensor_directSum, u, v, w, map_auxLeft, map_auxRight]
  have hr : mapTensor u' v' w' (directSum S (directSum (auxLeft A H) (auxRight B H))) =
      mapTensor U' V' W' S := by
    funext d e h
    simp [mapTensor_directSum, u', v', w', map_auxLeft, map_auxRight]
  simpa only [hp, hr] using! extract _ u v w u' v' w' h00 h10 h01

/-- Monotonicity uses the existing interpolation bridge for polynomial degenerations. -/
theorem arbitrary_head_value [Fintype I] [Fintype J] [Fintype K]
    [Fintype A] [Fintype B] [Fintype C] [Fintype D] [Fintype E] [Fintype H]
    (φ : PolMul.Spectral ℂ) (S : Tensor ℂ I J K)
    (U : A → I → ℂ) (V : B → J → ℂ) (W : C → K → ℂ)
    (U' : D → I → ℂ) (V' : E → J → ℂ) (W' : H → K → ℂ) :
    value φ (mapTensor U V W S) + value φ (mapTensor U' V' W' S) ≤
      value φ S + (value φ (auxLeft A H) + value φ (auxRight B H)) := by
  have h := value_mono φ (arbitrary_head S U V W U' V' W')
  simpa only [value_add] using! h

end OM.NNN2
