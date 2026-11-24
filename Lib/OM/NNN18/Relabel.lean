import Lib.OM.NNN18.Exact
import Lib.OM.NNN18.Triangle

/-!
`rho h` is the cyclic relabelling with `rho h 0 = h`.  The source form, the tariff family and the
coefficient stars are covariant, so the focus-`h` data at the profile `δ` are the focus-0 data at
`δ ∘ rho h`.  This is algebra in the price variables; the spectral point is not permuted.
-/

noncomputable section
open scoped BigOperators
namespace OM.NNN18

def rho : Fin 3 → Fin 3 → Fin 3 := ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]]

variable (P : Track)

/-- Parents at focus `h`: the star on bond `h`, `C_i + e` elsewhere. -/
def parentsH (h : Fin 3) (e : ℝ) (δ : Fin 3 → ℝ) : Fin 3 → Fin 3 → ℝ :=
  fun i => if i = h then star (theta P δ) h else fun j => tariff P δ i j + e

def targetH (h : Fin 3) (q e : ℝ) (δ : Fin 3 → ℝ) : Fin 3 → ℝ := fun j => tariff P δ h j + q * e

def betaPackH (h : Fin 3) (e : ℝ) (δ : Fin 3 → ℝ) : Fin 3 → ℝ :=
  fun i => if i = h then 1 else (theta P δ i + cross (parentsH P h e δ i) i) / 2

lemma form_relabel (h : Fin 3) (θ β L x : Fin 3 → ℝ) (Pp : Fin 3 → Fin 3 → ℝ) (F : ℝ) :
    form h θ β Pp L F x = form 0 (fun i => θ (rho h i)) (fun i => β (rho h i))
      (fun i j => Pp (rho h i) (rho h j)) (fun i => L (rho h i)) F (fun i => x (rho h i)) := by
  fin_cases h <;> simp [form, Fin.sum_univ_three, own, nu, pp, dot, rho] <;> ring

lemma tariff_relabel (h i j : Fin 3) (δ : Fin 3 → ℝ) :
    tariff P δ (rho h i) (rho h j) = tariff P (fun k => δ (rho h k)) i j := by
  fin_cases h <;> fin_cases i <;> fin_cases j <;> simp [tariff, other, rho]

lemma star_relabel (h j : Fin 3) (θ : Fin 3 → ℝ) :
    star θ h (rho h j) = star (fun k => θ (rho h k)) 0 j := by
  fin_cases h <;> fin_cases j <;> simp [star, other, rho]

lemma theta_relabel (h : Fin 3) (δ : Fin 3 → ℝ) :
    (fun i => theta P δ (rho h i)) = theta P (fun k => δ (rho h k)) := rfl

lemma parentsH_relabel (h : Fin 3) (e : ℝ) (δ : Fin 3 → ℝ) :
    (fun i j => parentsH P h e δ (rho h i) (rho h j)) = parents0 P e (fun k => δ (rho h k)) := by
  funext i j
  fin_cases h <;> fin_cases i <;> fin_cases j <;>
    simp [parentsH, parents0, star, tariff, other, rho, theta]

lemma targetH_relabel (h : Fin 3) (e : ℝ) (δ : Fin 3 → ℝ) (x : Fin 3 → ℝ) :
    dot (targetH P h (19 / 20) e δ) x =
      dot (target0 P (19 / 20) e (fun k => δ (rho h k))) (fun i => x (rho h i)) := by
  fin_cases h <;> simp [targetH, target0, dot, tariff, other, rho] <;> ring

lemma betaPackH_relabel (h : Fin 3) (e : ℝ) (δ : Fin 3 → ℝ) :
    (fun i => betaPackH P h e δ (rho h i)) = betaPack P e (fun k => δ (rho h k)) := by
  funext i
  fin_cases h <;> fin_cases i <;>
    simp [betaPackH, betaPack, parentsH, parents0, cross, star, tariff, other, rho, theta] <;> ring

lemma args_relabel (h : Fin 3) (θ β : Fin 3 → ℝ) (Pp : Fin 3 → Fin 3 → ℝ) (i : Fin 3) :
    args θ β Pp (rho h i) = args (fun k => θ (rho h k)) (fun k => β (rho h k))
      (fun k j => Pp (rho h k) (rho h j)) i := by
  fin_cases h <;> fin_cases i <;> simp [args, cross, rho] <;> ring

/-- The triangle is invariant under relabelling, and `δ ∘ rho h` has focus-0 coordinates. -/
lemma delta_relabel (h : Fin 3) (δ : Fin 3 → ℝ) (hs : δ 0 + δ 1 + δ 2 = 0) :
    (fun k => δ (rho h k)) = delta (δ (rho h 0)) (δ (rho h 1) - δ (rho h 2)) := by
  funext k
  fin_cases h <;> fin_cases k <;> simp [delta, rho] <;> linarith

end OM.NNN18
