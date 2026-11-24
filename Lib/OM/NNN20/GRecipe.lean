import Lib.OM.NNN20.Hyp

/-! # Global recipes are valid (finite causal induction)

`recipe_valid`: at a point of a checked cell whose profile is an upper profile of `φ`, given the
three seeds as global tariffs and the global source rule, every stored polynomial upper tariff of
the recipe is a global tariff. The induction runs along the recipe (`recipeShapeAux` checks that
every parent `node m` of node `k` has `m < k` and that every node satisfies `GShape`).
Each node: its parents are global tariffs (stars: `NNN18.star_affine`; seeds; earlier nodes by
induction), its gates hold (`gcheckAt_spec`), so its tangent tariff is a global tariff
(`GlobalRule`), and so is the larger stored polynomial (`affineBound_mono`). -/

noncomputable section
open scoped BigOperators
open CoordinateTensor OM.NNN.Raw
open OM.NNN12 (Shape DyadicTensor)

namespace OM.NNN20

/-- a coordinatewise larger tariff is a tariff (formats are nonnegative) -/
lemma affineBound_mono {φ : PolMul.Spectral ℂ} {c c' : Fin 3 → ℝ} (h : NNN13.AffineBound φ c)
    (hle : ∀ u, c u ≤ c' u) : NNN13.AffineBound φ c' := by
  intro v U
  refine (h v U).trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_)
  simp only [NNN13.plane]
  have h0 := mul_le_mul_of_nonneg_right (hle 0) (Nat.cast_nonneg (α := ℝ) (v 0))
  have h1 := mul_le_mul_of_nonneg_right (hle 1) (Nat.cast_nonneg (α := ℝ) (v 1))
  have h2 := mul_le_mul_of_nonneg_right (hle 2) (Nat.cast_nonneg (α := ℝ) (v 2))
  linarith

lemma tariffOn_mono {φ : PolMul.Spectral ℂ} {c c' : Fin 3 → ℝ} {K : Set (Fin 3 → ℝ)}
    (h : TariffOn φ c K) (hle : ∀ u, c u ≤ c' u) : TariffOn φ c' K := by
  intro v hv U
  refine (h v hv U).trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_)
  simp only [NNN13.plane]
  have h0 := mul_le_mul_of_nonneg_right (hle 0) (Nat.cast_nonneg (α := ℝ) (v 0))
  have h1 := mul_le_mul_of_nonneg_right (hle 1) (Nat.cast_nonneg (α := ℝ) (v 1))
  have h2 := mul_le_mul_of_nonneg_right (hle 2) (Nat.cast_nonneg (α := ℝ) (v 2))
  linarith

lemma tariffOn_univ {φ : PolMul.Spectral ℂ} {c : Fin 3 → ℝ} (h : NNN13.AffineBound φ c) :
    TariffOn φ c Set.univ := fun v _ U => h v U

/-! ## The structural side conditions of a recipe -/

/-- Boolean test for `GShape` -/
def gshapeB (n : GNode) : Bool :=
  (List.finRange 3).all (fun i => decide (n.act i = F7) || decide (n.act i = F11)) &&
  (List.finRange 3).all (fun u => decide (0 < n.b u)) && decide (0 < n.a 0 + n.a 1 + n.a 2) &&
  !(n.tri n.h) &&
  ((List.finRange 3).all (fun i => decide (i = n.h) || n.tri i) ||
    (List.finRange 3).all (fun i => !(n.tri i)))

lemma gshapeB_spec {n : GNode} (h : gshapeB n = true) : GShape n := by
  simp only [gshapeB, Bool.and_eq_true, Bool.or_eq_true, List.all_eq_true, List.mem_finRange,
    true_implies, decide_eq_true_eq, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨hact, hb⟩, ha⟩, hh⟩, htri⟩ := h
  refine ⟨hact, hb, ha, hh, ?_⟩
  rcases htri with h1 | h2
  · left
    intro i hi
    rcases h1 i with h | h
    · exact absurd h hi
    · exact h
  · right
    intro i
    simpa using h2 i

/-- a parent reference of node `k` is causal (and a seed only if seeds are admitted, `sd`) -/
def refOK (sd : Bool) (k : ℕ) : Ref → Bool
  | .star => true
  | .seed _ => sd
  | .node m => decide (m < k)

/-- every node from index `k` on satisfies `GShape` and has causal parents -/
def recipeShapeAux (sd : Bool) : ℕ → List GEntry → Bool
  | _, [] => true
  | k, e :: R => (gshapeB e.node && (List.finRange 3).all (fun i => refOK sd k (e.par i))) &&
      recipeShapeAux sd (k + 1) R

lemma recipeShapeAux_spec (sd : Bool) : ∀ (R : List GEntry) (k0 : ℕ), recipeShapeAux sd k0 R = true →
    ∀ j < R.length, gshapeB (R.getD j default).node = true ∧
      ∀ i, refOK sd (k0 + j) ((R.getD j default).par i) = true
  | [], _, _, j, hj => by simp at hj
  | e :: R, k0, h, j, hj => by
    simp only [recipeShapeAux, Bool.and_eq_true, List.all_eq_true, List.mem_finRange,
      true_implies] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    cases j with
    | zero => exact ⟨by simpa using h1, fun i => by simpa using h2 i⟩
    | succ j =>
      have hj' : j < R.length := by simpa using hj
      have := recipeShapeAux_spec sd R (k0 + 1) h3 j hj'
      refine ⟨by simpa using this.1, fun i => ?_⟩
      have e1 : k0 + (j + 1) = k0 + 1 + j := by omega
      rw [e1]
      simpa using this.2 i

/-! ## Stars and seeds -/

lemma starR_eq_star (θ : Fin 3 → ℝ) (h : Fin 3) : (fun j => starR θ h j) = OM.NNN18.star θ h := by
  funext j
  fin_cases h <;> fin_cases j <;> rfl

lemma star_valid {φ : PolMul.Spectral ℂ} {θ : Fin 3 → ℝ}
    (hθ : ∀ i, Foundations.PairUnitExponents.theta φ i ≤ θ i) (h : Fin 3) :
    NNN13.AffineBound φ (fun j => starR θ h j) := by
  rw [starR_eq_star]
  exact OM.NNN18.star_affine φ θ hθ h

/-! ## The induction -/

/-- **Every stored upper tariff of a checked global recipe is a global tariff.** -/
theorem recipe_valid (G : GlobalRule) {S : SeedPrm} {C : Cell} {R : List GEntry} {sd : Bool}
    (hchk : AllChecked S C R) (hsh : recipeShapeAux sd 0 R = true)
    {φ : PolMul.Spectral ℂ} {x y : ℝ} (hx : |x| ≤ 1) (hy : |y| ≤ 1)
    (hθ : UpperProfile φ (fun i => thetaReal S.t C i x y))
    (hseed : sd = true →
      ∀ h, NNN13.AffineBound φ (fun j => seedR S (fun l => thetaReal S.t C l x y) h j)) :
    ∀ k < R.length, NNN13.AffineBound φ (fun u => peval ((R.getD k default).Pk u) x y / ONE) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k IH =>
    intro hk
    obtain ⟨hshape, hcaus⟩ := recipeShapeAux_spec sd R 0 hsh k hk
    have hpar : ∀ i, NNN13.AffineBound φ
        (fun j => parR S C R ((R.getD k default).par i) i j x y) := by
      intro i
      have hc := hcaus i
      generalize hr : (R.getD k default).par i = r at hc ⊢
      cases r with
      | star => exact star_valid hθ.1 i
      | seed h => exact hseed (by simpa [refOK] using hc) h
      | node m =>
        simp only [refOK, zero_add, decide_eq_true_eq] at hc
        exact IH m hc (by omega)
    obtain ⟨hg, hdom⟩ := gcheckAt_spec (hchk k hk) hx hy
    exact affineBound_mono (G _ φ _ _ (gshapeB_spec hshape) hθ hpar hg) hdom

end OM.NNN20
