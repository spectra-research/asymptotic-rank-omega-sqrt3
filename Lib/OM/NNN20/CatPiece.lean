import Lib.OM.NNN20.CatalyticSpec2

/-! # Catalytic recipes on a cell

`ccheckAt_spec`: a passing check of catalytic node `k` gives its gates `CNodeGates` at every point
of the cell, for the real parent tariffs `cparR` (global tariffs of the cell's global recipe, or the
stored upper tariffs `λ̂` of earlier catalytic nodes) and the parents' hull vertex lists.
`cterm_spec`: the terminal node's upper tariff prices the cube at most `B` on the cell, and the
cube direction `(1,1,1)` lies in the terminal node's cone. -/

namespace OM.NNN20

open Finset

/-- the real parent tariff of a catalytic node -/
noncomputable def cparR (S : SeedPrm) (C : Cell) (R : List GEntry) (CR : List CEntry) (r : CRef)
    (i u : Fin 3) (x y : ℝ) : ℝ :=
  match r with
  | .glob g => parR S C R g i u x y
  | .cat m => peval ((CR.getD m default).Lhat u) x y / ONE

theorem cparRow_encl (S : SeedPrm) (C : Cell) (R : List GEntry) (CR : List CEntry) (r : CRef)
    (i u : Fin 3) : (cparRow S (thetaTM S.t C) R CR r i u).Encl (cparR S C R CR r i u) := by
  cases r with
  | glob g => exact (parRow_encl S C R g i u).congr fun x y _ _ => rfl
  | cat m => fin_cases u <;> exact (pk_encl _).congr fun x y _ _ => rfl

/-- **Soundness of one catalytic recipe check.** -/
theorem ccheckAt_spec {S : SeedPrm} {C : Cell} {R : List GEntry} {B : ℚ} {CR : List CEntry} {k : ℕ}
    (h : ccheckAt S C R B CR k = true) {x y : ℝ} (hx : |x| ≤ 1) (hy : |y| ≤ 1) :
    CNodeGates (CR.getD k default).node (fun i => thetaReal S.t C i x y) B
      (fun i u => cparR S C R CR ((CR.getD k default).node.par i) i u x y)
      (fun u => peval ((CR.getD k default).Lhat u) x y / ONE) (CR.getD k default).V
      (fun i => cparV CR ((CR.getD k default).node.par i)) := by
  unfold ccheckAt at h
  dsimp only at h
  have hP : ∀ i u, ((![cparRow S (thetaTM S.t C) R CR ((CR.getD k default).node.par 0) 0,
      cparRow S (thetaTM S.t C) R CR ((CR.getD k default).node.par 1) 1,
      cparRow S (thetaTM S.t C) R CR ((CR.getD k default).node.par 2) 2] : Fin 3 → Fin 3 → TM) i u).Encl
      (cparR S C R CR ((CR.getD k default).node.par i) i u) := by
    intro i u
    fin_cases i <;> exact cparRow_encl S C R CR _ _ u
  exact ccheckNode_spec (thetaTM_encl S.t C) hP h hx hy

/-- **The terminal of a catalytic recipe.** -/
theorem cterm_spec {CR : List CEntry} {B : ℚ} {lvl k w : ℕ} (h : cterm CR B lvl k w = true) :
    (∀ x y : ℝ, |x| ≤ 1 → |y| ≤ 1 →
      peval ((CR.getD k default).Lhat 0) x y / ONE + peval ((CR.getD k default).Lhat 1) x y / ONE +
        peval ((CR.getD k default).Lhat 2) x y / ONE ≤ B) ∧
    InCone (CR.getD k default).V (fun _ => 1) := by
  unfold cterm at h
  simp only [Bool.and_eq_true] at h
  refine ⟨fun x y hx hy => ?_, (inTri_spec h.2).congr fun u => by simp⟩
  have := termCheck_sum h.1 hx hy
  simpa [add_assoc] using this

end OM.NNN20
