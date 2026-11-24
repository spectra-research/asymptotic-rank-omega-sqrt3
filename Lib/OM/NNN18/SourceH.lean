import Lib.OM.NNN18.Relabel
import Lib.OM.NNN18.FocusU
import Lib.OM.NNN18.FocusC

/-!
# The source inequality at every focus, both tracks -/

noncomputable section
open scoped BigOperators
namespace OM.NNN18

/-- The focus-`h` exact source form. -/
def formH (P : Track) (packed : Bool) (h : Fin 3) (e : ℝ) (δ x : Fin 3 → ℝ) : ℝ :=
  let β : Fin 3 → ℝ := if packed then betaPackH P h e δ else fun _ => 1
  form h (theta P δ) β (parentsH P h e δ)
    (fun i => ell (args (theta P δ) β (parentsH P h e δ) i))
    (dot (targetH P h (19 / 20) e δ) x) x

theorem formH_nonneg_of_focus0 (P : Track) (R : ℝ)
    (hord : ∀ {d y e : ℝ}, 1 / 25 ≤ e → e ≤ 1 / 2 → -2 * R ≤ d → d ≤ R → -(d + 2 * R) ≤ y →
      y ≤ d + 2 * R → ∀ {x : Fin 3 → ℝ}, (∀ i, 0 ≤ x i) → 0 ≤ ordExact P e d y x)
    (hpack : ∀ {d y e : ℝ}, 0 ≤ e → -2 * R ≤ d → d ≤ R → -(d + 2 * R) ≤ y →
      y ≤ d + 2 * R → ∀ {x : Fin 3 → ℝ}, (∀ i, 0 ≤ x i) → 0 ≤ packExact P e d y x)
    (h : Fin 3) {δ : Fin 3 → ℝ} (hs : δ 0 + δ 1 + δ 2 = 0) (hδ : ∀ i, δ i ≤ R)
    {x : Fin 3 → ℝ} (hx : ∀ i, 0 ≤ x i) :
    (∀ e, 1 / 25 ≤ e → e ≤ 1 / 2 → 0 ≤ formH P false h e δ x) ∧
    (∀ e, 0 ≤ e → 0 ≤ formH P true h e δ x) := by
  set d := δ (rho h 0)
  set y := δ (rho h 1) - δ (rho h 2)
  have hdel := delta_relabel h δ hs
  have hxr : ∀ i, 0 ≤ (fun i => x (rho h i)) i := fun i => hx _
  -- the relabelled profile lies in the focus-0 triangle
  have hsum : δ (rho h 0) + δ (rho h 1) + δ (rho h 2) = 0 := by
    fin_cases h <;> simp [rho] <;> linarith
  have h1 := hδ (rho h 1)
  have h2 := hδ (rho h 2)
  have h0 := hδ (rho h 0)
  have hd₁ : -2 * R ≤ d := by simp only [d]; linarith
  have hd₂ : d ≤ R := h0
  have hy₁ : -(d + 2 * R) ≤ y := by simp only [d, y]; linarith
  have hy₂ : y ≤ d + 2 * R := by simp only [d, y]; linarith
  constructor
  · intro e he₁ he₂
    have key := hord he₁ he₂ hd₁ hd₂ hy₁ hy₂ hxr
    simp only [formH, Bool.false_eq_true, ↓reduceIte]
    rw [form_relabel h, theta_relabel, parentsH_relabel, targetH_relabel, form_zero]
    have hL : (fun i => ell (args (theta P δ) (fun _ => (1 : ℝ)) (parentsH P h e δ) (rho h i))) =
        exactL (theta P (fun k => δ (rho h k))) betaOrd (parents0 P e (fun k => δ (rho h k))) := by
      funext i
      rw [args_relabel, theta_relabel, parentsH_relabel]
      rfl
    rw [hL, hdel]
    exact key
  · intro e he
    have key := hpack he hd₁ hd₂ hy₁ hy₂ hxr
    simp only [formH, ↓reduceIte]
    rw [form_relabel h, theta_relabel, parentsH_relabel, targetH_relabel, betaPackH_relabel,
      form_zero]
    have hL : (fun i => ell (args (theta P δ) (betaPackH P h e δ) (parentsH P h e δ) (rho h i))) =
        exactL (theta P (fun k => δ (rho h k))) (betaPack P e (fun k => δ (rho h k)))
          (parents0 P e (fun k => δ (rho h k))) := by
      funext i
      rw [args_relabel, theta_relabel, parentsH_relabel, betaPackH_relabel]
      rfl
    rw [hL, hdel]
    exact key

theorem formH_U (h : Fin 3) {δ : Fin 3 → ℝ} (hs : δ 0 + δ 1 + δ 2 = 0)
    (hδ : ∀ i, δ i ≤ FocusU.R) {x : Fin 3 → ℝ} (hx : ∀ i, 0 ≤ x i) :
    (∀ e, 1 / 25 ≤ e → e ≤ 1 / 2 → 0 ≤ formH U false h e δ x) ∧
    (∀ e, 0 ≤ e → 0 ≤ formH U true h e δ x) :=
  formH_nonneg_of_focus0 U FocusU.R FocusU.ordExact_nonneg FocusU.packExact_nonneg h hs hδ hx

theorem formH_C (h : Fin 3) {δ : Fin 3 → ℝ} (hs : δ 0 + δ 1 + δ 2 = 0)
    (hδ : ∀ i, δ i ≤ FocusC.R) {x : Fin 3 → ℝ} (hx : ∀ i, 0 ≤ x i) :
    (∀ e, 1 / 25 ≤ e → e ≤ 1 / 2 → 0 ≤ formH C false h e δ x) ∧
    (∀ e, 0 ≤ e → 0 ≤ formH C true h e δ x) :=
  formH_nonneg_of_focus0 C FocusC.R FocusC.ordExact_nonneg FocusC.packExact_nonneg h hs hδ hx

end OM.NNN18
