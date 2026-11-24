import Lib.OM.NNN20.Recipe

/-! # Whole recipes and terminal comparisons

`AllChecked S C R`: every node of the recipe passes `gcheckAt` (one kernel check per node in the
generated certificates). `recipeOK_of_checked` gives the real statement `RecipeOK`: at every point
of the cell every node's gates hold and its tangent tariff is below its stored upper polynomial.
`sumL` adds coefficient lists; `termCheck_sum` bounds a sum of stored polynomials on the cell. -/

namespace OM.NNN20

open Finset

def sumL : List (List ℤ) → List ℤ
  | [] => []
  | c :: cs => addL c (sumL cs)

lemma peval_sumL : ∀ (cs : List (List ℤ)) (x y : ℝ),
    peval (sumL cs) x y = (cs.map (fun c => peval c x y)).sum
  | [], x, y => by simp [sumL, peval]
  | c :: cs, x, y => by simp [sumL, peval_addL, peval_sumL cs]

def AllChecked (S : SeedPrm) (C : Cell) (R : List GEntry) : Prop :=
  ∀ k < R.length, gcheckAt S C R k = true

/-- the real conclusion of a checked recipe on its cell -/
def RecipeOK (S : SeedPrm) (C : Cell) (R : List GEntry) : Prop :=
  ∀ x y : ℝ, |x| ≤ 1 → |y| ≤ 1 → ∀ k < R.length,
    GGates (R.getD k default).node (fun i => thetaReal S.t C i x y)
      (fun i j => parR S C R ((R.getD k default).par i) i j x y) ∧
    ∀ u, gC (R.getD k default).node (fun i => thetaReal S.t C i x y)
      (fun i j => parR S C R ((R.getD k default).par i) i j x y) u ≤
      peval ((R.getD k default).Pk u) x y / ONE

theorem recipeOK_of_checked {S : SeedPrm} {C : Cell} {R : List GEntry} (h : AllChecked S C R) :
    RecipeOK S C R := fun _ _ hx hy k hk => gcheckAt_spec (h k hk) hx hy

/-- a terminal comparison of a sum of stored polynomials -/
theorem termCheck_sum {cs : List (List ℤ)} {B : ℚ} {lvl : ℕ} (h : termCheck (sumL cs) B lvl = true)
    {x y : ℝ} (hx : |x| ≤ 1) (hy : |y| ≤ 1) :
    (cs.map (fun c => peval c x y / ONE)).sum ≤ B := by
  have := termCheck_spec h hx hy
  rw [peval_sumL] at this
  have e : ∀ l : List (List ℤ), (l.map (fun c => peval c x y / ONE)).sum =
      (l.map (fun c => peval c x y)).sum / ONE := by
    intro l
    induction l with
    | nil => simp
    | cons a l ih => simp [ih, add_div]
  rw [e]; exact this

end OM.NNN20
