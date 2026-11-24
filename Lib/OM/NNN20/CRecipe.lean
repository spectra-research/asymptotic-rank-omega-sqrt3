import Lib.OM.NNN20.GRecipe
import Lib.OM.NNN20.ConeLin

/-! # Catalytic recipes are valid under the contradiction hypothesis (node CDAG)

`crecipe_valid`: fix a point of a checked record cell whose profile is an upper profile of `φ`,
and a cube `S` with `φ(S) > 2^{B l}`. Then every catalytic node `k` has an open cone `K_k` of
formats, containing its punctured vertex cone, on which its stored polynomial upper tariff `λ̂_k`
is a tariff. Finite causal induction along the recipe:

* parents: global references are global tariffs (`recipe_valid`, stars, seeds), `K = univ`;
  catalytic references `cat m` have `m < k` and the induction hypothesis;
* the node's gates hold (`ccheckAt_spec`); `CatalyticRule` gives `λ` on `CDom`, an open cone
  (`isOpen_cDom`, `isConeSet_cDom`) that contains the punctured vertex cone, because every gate is
  linear in the format and strict at every hull vertex, and the query endpoints are linear in the
  format and lie in the parent's vertex cone at every vertex (`famRule_of_verts`);
* `λ ≤ λ̂` coordinatewise (`tariffOn_mono`).

`record_cube`: the terminal node's cone contains the cube direction and `Σ λ̂ ≤ B` on the cell, a
contradiction; so `B` bounds every cube at `φ`. -/

noncomputable section
open scoped BigOperators
open CoordinateTensor OM.NNN.Raw
open OM.NNN12 (Shape DyadicTensor)

namespace OM.NNN20

/-! ## Rational vertices and real formats -/

lemma rdot_cast (a y : Fin 3 → ℚ) : rdot a (fun u => (y u : ℝ)) = ((qdot a y : ℚ) : ℝ) := by
  simp only [rdot, qdot]; push_cast; ring

lemma rdot_vR (a : Fin 3 → ℚ) (pt : ℤ × ℤ) : rdot a (vR pt) = ((qdot a (vecV pt) : ℚ) : ℝ) :=
  rdot_cast a (vecV pt)

lemma vR_apply (pt : ℤ × ℤ) (u : Fin 3) : vR pt u = ((vecV pt u : ℚ) : ℝ) := rfl

section Lin
variable (n : CNode) (θ : Fin 3 → ℝ) (B : ℚ) (c : Fin 3 → Fin 3 → ℝ)

lemma cNx_cast (f : Fin 3) (y : Fin 3 → ℚ) :
    cNx n f (fun u => (y u : ℝ)) = ((cNy n f y : ℚ) : ℝ) := by
  unfold cNx cNy
  split_ifs <;> exact rdot_cast _ _

lemma cRhoX_cast (f : Fin 3) (y : Fin 3 → ℚ) :
    cRhoX n θ B c f (fun u => (y u : ℝ)) = cRho n θ B c f y := by
  unfold cRhoX cRho
  rw [cNx_cast, rdot_cast]
  unfold cNy
  simp only [NNN13.plane]
  push_cast
  ring

lemma isLin_cNx (f : Fin 3) : IsLin (cNx n f) := by
  by_cases h : f = cj n
  · exact ⟨fun j => (cNj n j : ℝ), fun x => by simp only [cNx, if_pos h, rdot]⟩
  · exact ⟨fun j => (cNk n j : ℝ), fun x => by simp only [cNx, if_neg h, rdot]⟩

lemma isLin_cRhoX (f : Fin 3) : IsLin (cRhoX n θ B c f) :=
  ((((isLin_plane (cLam n θ B c)).add ((isLin_rdot (cts n)).mul_const (B : ℝ))).sub
    ((isLin_plane (c f)).add ((isLin_rdot (cts n)).mul_const (csum c f)))).mul_const
      (1 / cBeta n θ c f)).sub ((isLin_cNx n f).mul_const (cL n θ c f))

/-- the queried format before extraction: `x + t_S(x) 1` -/
def famY (x : Fin 3 → ℝ) : Fin 3 → ℝ := fun u => x u + rdot (cts n) x

lemma isLin_famY (u : Fin 3) : IsLin (fun x => famY n x u) :=
  (IsLin.coord u).add (isLin_rdot _)

/-- the lower end of the shortened query segment -/
def loS (f : Fin 3) (x : Fin 3 → ℝ) : ℝ :=
  -(cRhoX n θ B c f x) / 2 + (n.act f).d * (T0 : ℝ) * cNx n f x

/-- the upper end of the query segment -/
def hiS (f : Fin 3) (x : Fin 3 → ℝ) : ℝ := (n.act f).d * cNx n f x

lemma isLin_loS (f : Fin 3) : IsLin (loS n θ B c f) :=
  (((isLin_cRhoX n θ B c f).neg).mul_const (1 / 2)).add
    ((isLin_cNx n f).const_mul ((n.act f).d * (T0 : ℝ))) |> fun h => by
      obtain ⟨a, ha⟩ := h
      exact ⟨a, fun x => by rw [← ha]; simp only [loS]; ring⟩

lemma isLin_hiS (f : Fin 3) : IsLin (hiS n f) := (isLin_cNx n f).const_mul _

lemma isLin_plainLo (f : Fin 3) : IsLin (fun x => -(cRhoX n θ B c f x) / 2) := by
  obtain ⟨a, ha⟩ := (isLin_cRhoX n θ B c f).neg.mul_const (1 / 2)
  exact ⟨a, fun x => by rw [← ha]; ring⟩

end Lin

lemma balR_of_balanceOK {yu tu : ℚ} {ac : Act} (h : balanceOK yu tu ac = true) :
    BalR (yu : ℝ) (tu : ℝ) ac := by
  simp only [balanceOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h1, h2⟩ := h
  constructor
  · have := (Rat.cast_pos (K := ℝ)).2 h1
    push_cast at this
    exact this
  · have := (Rat.cast_pos (K := ℝ)).2 h2
    push_cast at this
    exact this

/-! ## Open cones -/

lemma isOpen_famRule {n : CNode} {θ : Fin 3 → ℝ} {B : ℚ} {c : Fin 3 → Fin 3 → ℝ}
    {K : Set (Fin 3 → ℝ)} (hK : IsOpen K) (f o : Fin 3) :
    IsOpen {x | FamRule n θ B c K f o x} := by
  have cρ := (isLin_cRhoX n θ B c f).continuous
  have cN := (isLin_cNx n f).continuous
  have cT := (isLin_rdot (cth n)).continuous
  have cY : Continuous (fun x => fun u => x u + rdot (cts n) x) :=
    continuous_pi fun u => (isLin_famY n u).continuous
  have hbal : IsOpen {x : Fin 3 → ℝ | BalR (x o) (rdot (cth n) x) (n.act f)} := by
    have e1 : IsOpen {x : Fin 3 → ℝ | (0 : ℝ) < x o - rdot (cth n) x *
        (((n.act f).k : ℝ) / (((n.act f).q : ℝ) - (n.act f).k))} :=
      isOpen_lt continuous_const ((continuous_apply o).sub (cT.mul continuous_const))
    have e2 : IsOpen {x : Fin 3 → ℝ | (0 : ℝ) < rdot (cth n) x *
        ((((n.act f).q : ℝ) - (n.act f).k) / (n.act f).k) - x o} :=
      isOpen_lt continuous_const ((cT.mul continuous_const).sub (continuous_apply o))
    exact e1.inter e2
  have h1 : IsOpen {x : Fin 3 → ℝ | 0 < cRhoX n θ B c f x} := isOpen_lt continuous_const cρ
  have h2 : IsOpen {x : Fin 3 → ℝ | cRhoX n θ B c f x < Real.logb 2 (n.act f).q * cNx n f x} :=
    isOpen_lt cρ (by fun_prop)
  have hs1 : IsOpen {x : Fin 3 → ℝ | SegIn K (fun u => x u + rdot (cts n) x) (qdirR n o)
      (-(cRhoX n θ B c f x) / 2) ((n.act f).d * cNx n f x)} :=
    isOpen_segIn hK cY (by fun_prop) (by fun_prop)
  have hk : IsOpen {x : Fin 3 → ℝ | cRhoX n θ B c f x < kappaR (n.act f).q T0 * cNx n f x} :=
    isOpen_lt cρ (by fun_prop)
  have hs2 : IsOpen {x : Fin 3 → ℝ | SegIn K (fun u => x u + rdot (cts n) x) (qdirR n o)
      (-(cRhoX n θ B c f x) / 2 + (n.act f).d * (T0 : ℝ) * cNx n f x)
      ((n.act f).d * cNx n f x)} :=
    isOpen_segIn hK cY (by fun_prop) (by fun_prop)
  exact hbal.inter (h1.inter (h2.inter (hs1.union (hk.inter hs2))))

lemma isOpen_cDom {n : CNode} {θ : Fin 3 → ℝ} {B : ℚ} {c : Fin 3 → Fin 3 → ℝ}
    {K : Fin 3 → Set (Fin 3 → ℝ)} (hK : ∀ i, IsOpen (K i)) : IsOpen (CDom n θ B c K) := by
  have hp : IsOpen {x : Fin 3 → ℝ | ∀ u, 0 < x u} := by
    have : {x : Fin 3 → ℝ | ∀ u, 0 < x u} = ⋂ u, {x | 0 < x u} := by ext x; simp
    rw [this]
    exact isOpen_iInter_of_finite fun u => isOpen_lt continuous_const (continuous_apply u)
  exact hp.inter ((isOpen_famRule (hK _) _ _).inter (isOpen_famRule (hK _) _ _))

lemma segIn_scale {K : Set (Fin 3 → ℝ)} (hK : IsConeSet K) {Y d : Fin 3 → ℝ} {lo hi a : ℝ}
    (ha : 0 < a) (h : SegIn K Y d lo hi) :
    SegIn K (fun u => a * Y u) d (a * lo) (a * hi) := by
  intro ξ h1 h2
  have h1' : lo ≤ ξ / a := by rw [le_div_iff₀ ha]; linarith
  have h2' : ξ / a ≤ hi := by rw [div_le_iff₀ ha]; linarith
  have := hK _ (h (ξ / a) h1' h2') a ha
  refine (congrArg (· ∈ K) (funext fun u => ?_)).mp this
  field_simp

lemma isConeSet_famRule {n : CNode} {θ : Fin 3 → ℝ} {B : ℚ} {c : Fin 3 → Fin 3 → ℝ}
    {K : Set (Fin 3 → ℝ)} (hK : IsConeSet K) (f o : Fin 3) {x : Fin 3 → ℝ}
    (hx : FamRule n θ B c K f o x) {a : ℝ} (ha : 0 < a) :
    FamRule n θ B c K f o (fun u => a * x u) := by
  have eρ := (isLin_cRhoX n θ B c f).map_smul a x
  have eN := (isLin_cNx n f).map_smul a x
  have eT := (isLin_rdot (cth n)).map_smul a x
  have eS := (isLin_rdot (cts n)).map_smul a x
  obtain ⟨⟨hb1, hb2⟩, hρ1, hρ2, hseg⟩ := hx
  have eY : (fun u => a * x u + rdot (cts n) (fun u => a * x u)) =
      (fun u => a * (x u + rdot (cts n) x)) := by funext u; rw [eS]; ring
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [eT]
    have := mul_pos ha hb1
    linarith [this]
  · rw [eT]
    have := mul_pos ha hb2
    nlinarith [this]
  · rw [eρ]; exact mul_pos ha hρ1
  · rw [eρ, eN]
    have := mul_lt_mul_of_pos_left hρ2 ha
    linarith
  · rw [eρ, eN, eY]
    rcases hseg with hs | ⟨hk, hs⟩
    · left
      have := segIn_scale hK ha hs
      refine fun ξ h1 h2 => this ξ (by linarith) (by linarith)
    · right
      refine ⟨by have := mul_lt_mul_of_pos_left hk ha; linarith, ?_⟩
      have := segIn_scale hK ha hs
      refine fun ξ h1 h2 => this ξ (by linarith) (by linarith)

lemma isConeSet_cDom {n : CNode} {θ : Fin 3 → ℝ} {B : ℚ} {c : Fin 3 → Fin 3 → ℝ}
    {K : Fin 3 → Set (Fin 3 → ℝ)} (hK : ∀ i, IsConeSet (K i)) : IsConeSet (CDom n θ B c K) := by
  intro x hx a ha
  obtain ⟨hpos, hj, hk⟩ := hx
  exact ⟨fun u => mul_pos ha (hpos u), isConeSet_famRule (hK _) _ _ hj ha,
    isConeSet_famRule (hK _) _ _ hk ha⟩

/-! ## Gates at the vertices give the gates on the vertex cone -/

lemma qdirR_cast (n : CNode) (o u : Fin 3) : qdirR n o u = ((qdir n o u : ℚ) : ℝ) := by
  simp only [qdirR, qdir]; split_ifs <;> simp

lemma famRule_of_verts {n : CNode} {θ : Fin 3 → ℝ} {B : ℚ} {c : Fin 3 → Fin 3 → ℝ}
    {K : Set (Fin 3 → ℝ)} {Vp : Option (List (ℤ × ℤ))} {f o : Fin 3}
    (hfp : f ≠ n.p) (hfo : f ≠ o) (htau : 0 < n.tau)
    (hK : ∀ Vf, Vp = some Vf → ∀ z, InCone Vf z → z ≠ 0 → z ∈ K)
    (hKu : Vp = none → K = Set.univ)
    {V : List (ℤ × ℤ)} (hpos : ∀ pt ∈ V, 0 < pt.1 ∧ 0 < pt.2 ∧ 0 < GRID - pt.1 - pt.2)
    (hbal : ∀ pt ∈ V, balanceOK ((vecV pt) o) (qdot (cth n) (vecV pt)) (n.act f) = true)
    (hfam : ∀ pt ∈ V, FamGates n θ B c Vp f o (vecV pt))
    {z : Fin 3 → ℝ} (hz : InCone V z) (hz0 : z ≠ 0) : FamRule n θ B c K f o z := by
  have hzpos := pos_of_cone hpos hz hz0
  have hvnn : ∀ pt ∈ V, ∀ u, (0 : ℚ) ≤ vecV pt u := fun pt hpt u => by
    obtain ⟨h1, h2, h3⟩ := hpos pt hpt
    exact (vecV_pos h1 h2 h3 u).le
  have hρv : ∀ pt ∈ V, cRhoX n θ B c f (vR pt) = cRho n θ B c f (vecV pt) :=
    fun pt _ => cRhoX_cast n θ B c f (vecV pt)
  have hNv : ∀ pt ∈ V, cNx n f (vR pt) = ((cNy n f (vecV pt) : ℚ) : ℝ) :=
    fun pt _ => cNx_cast n f (vecV pt)
  have hρpos : ∀ pt ∈ V, 0 < cRhoX n θ B c f (vR pt) := fun pt hpt => by
    rw [hρv pt hpt]; exact (hfam pt hpt).1
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · refine ((IsLin.coord o).sub ((isLin_rdot (cth n)).mul_const _)).pos_of_cone
      (fun pt hpt => ?_) hz hz0
    have := (balR_of_balanceOK (hbal pt hpt)).1
    beta_reduce
    rw [rdot_vR, vR_apply]
    exact this
  · refine (((isLin_rdot (cth n)).mul_const _).sub (IsLin.coord o)).pos_of_cone
      (fun pt hpt => ?_) hz hz0
    have := (balR_of_balanceOK (hbal pt hpt)).2
    beta_reduce
    rw [rdot_vR, vR_apply]
    exact this
  · exact (isLin_cRhoX n θ B c f).pos_of_cone hρpos hz hz0
  · have := (((isLin_cNx n f).const_mul (Real.logb 2 (n.act f).q)).sub
      (isLin_cRhoX n θ B c f)).pos_of_cone (fun pt hpt => ?_) hz hz0
    · beta_reduce at this; linarith
    · beta_reduce
      rw [hρv pt hpt, hNv pt hpt]
      have := (hfam pt hpt).2.1
      linarith
  · -- the parent queries
    rcases hVp : Vp with _ | Vf
    · left
      rw [hKu hVp]
      intro _ _ _
      trivial
    · right
      have hg : ∀ pt ∈ V, cRho n θ B c f (vecV pt) < kappaR (n.act f).q T0 * (cNy n f (vecV pt) : ℝ) ∧
          ∀ ξ : ℝ, cXiLow n θ B c f (vecV pt) ≤ ξ → ξ ≤ (((n.act f).d * cNy n f (vecV pt) : ℚ) : ℝ) →
            InCone Vf (fun u => ((vecV pt u + qdot (cts n) (vecV pt) : ℚ) : ℝ) -
              ξ * (qdir n o u : ℝ)) :=
        fun pt hpt => (hfam pt hpt).2.2 Vf hVp
      refine ⟨?_, ?_⟩
      · have := (((isLin_cNx n f).const_mul (kappaR (n.act f).q T0)).sub
          (isLin_cRhoX n θ B c f)).pos_of_cone (fun pt hpt => ?_) hz hz0
        · beta_reduce at this; linarith
        · beta_reduce
          rw [hρv pt hpt, hNv pt hpt]
          have := (hg pt hpt).1
          linarith
      · -- endpoints at the vertices
        have hNnn : ∀ pt ∈ V, (0 : ℝ) ≤ (cNy n f (vecV pt) : ℝ) := fun pt hpt => by
          exact_mod_cast cNy_nonneg htau (hvnn pt hpt) f
        have hlohi : ∀ pt ∈ V, cXiLow n θ B c f (vecV pt) ≤
            (((n.act f).d * cNy n f (vecV pt) : ℚ) : ℝ) := by
          intro pt hpt
          have hρ := (hfam pt hpt).1
          have hN := hNnn pt hpt
          have hd : (0 : ℝ) ≤ (n.act f).d := Nat.cast_nonneg _
          simp only [cXiLow, T0]
          push_cast
          nlinarith
        have hcast : ∀ pt ∈ V, ∀ (ξ : ℝ) (u : Fin 3), famY n (vR pt) u - ξ * qdirR n o u =
            ((vecV pt u + qdot (cts n) (vecV pt) : ℚ) : ℝ) - ξ * (qdir n o u : ℝ) := by
          intro pt _ ξ u
          simp only [famY]
          rw [rdot_vR, vR_apply, qdirR_cast]
          push_cast
          ring
        have hEl : InCone Vf (fun u => famY n z u - loS n θ B c f z * qdirR n o u) := by
          refine inCone_of_lin (E := fun x u => famY n x u - loS n θ B c f x * qdirR n o u)
            (fun u => (isLin_famY n u).sub ((isLin_loS n θ B c f).mul_const _)) (fun pt hpt => ?_) hz
          have hlo : loS n θ B c f (vR pt) = cXiLow n θ B c f (vecV pt) := by
            simp only [loS, cXiLow, hρv pt hpt, hNv pt hpt]
            push_cast; ring
          refine ((hg pt hpt).2 _ le_rfl (hlohi pt hpt)).congr fun u => ?_
          rw [← hcast pt hpt, hlo]
        have hEh : InCone Vf (fun u => famY n z u - hiS n f z * qdirR n o u) := by
          refine inCone_of_lin (E := fun x u => famY n x u - hiS n f x * qdirR n o u)
            (fun u => (isLin_famY n u).sub ((isLin_hiS n f).mul_const _)) (fun pt hpt => ?_) hz
          have hhi : hiS n f (vR pt) = (((n.act f).d * cNy n f (vecV pt) : ℚ) : ℝ) := by
            simp only [hiS, hNv pt hpt]
            push_cast; ring
          refine ((hg pt hpt).2 _ (hlohi pt hpt) le_rfl).congr fun u => ?_
          rw [← hcast pt hpt, hhi]
        intro ξ h1 h2
        refine hK Vf hVp _ (segment_inCone (lo := loS n θ B c f z) (hi := hiS n f z) hEl hEh
          (by simp only [loS] at h1 ⊢; linarith) (by simp only [hiS] at h2 ⊢; linarith)) ?_
        intro h0
        have h0f := congrFun h0 f
        have hq : qdirR n o f = 0 := by simp [qdirR, hfp, hfo]
        have hts : 0 ≤ rdot (cts n) z := by
          simp only [rdot, cts]
          have h0' := hzpos 0; have h1' := hzpos 1; have h2' := hzpos 2
          split_ifs <;> push_cast <;> positivity
        simp only [famY, hq, mul_zero, sub_zero, Pi.zero_apply] at h0f
        linarith [hzpos f]

/-! ## The causal induction -/

/-- a parent reference of catalytic node `k` (global recipe of length `nR`) is causal -/
def crefOK (sd : Bool) (nR k : ℕ) : CRef → Bool
  | .glob (.node m) => decide (m < nR)
  | .glob (.seed _) => sd
  | .glob .star => true
  | .cat m => decide (m < k)

/-- every catalytic node from index `k` on has a positive mass and causal parents -/
def crecipeShapeAux (sd : Bool) (nR : ℕ) : ℕ → List CEntry → Bool
  | _, [] => true
  | k, e :: CR => (decide (0 < e.node.tau) &&
      (List.finRange 3).all (fun i => crefOK sd nR k (e.node.par i))) &&
        crecipeShapeAux sd nR (k + 1) CR

lemma crecipeShapeAux_spec (sd : Bool) (nR : ℕ) : ∀ (CR : List CEntry) (k0 : ℕ),
    crecipeShapeAux sd nR k0 CR = true →
    ∀ j < CR.length, 0 < (CR.getD j default).node.tau ∧
      ∀ i, crefOK sd nR (k0 + j) ((CR.getD j default).node.par i) = true
  | [], _, _, j, hj => by simp at hj
  | e :: CR, k0, h, j, hj => by
    simp only [crecipeShapeAux, Bool.and_eq_true, List.all_eq_true, List.mem_finRange,
      true_implies, decide_eq_true_eq] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    cases j with
    | zero => exact ⟨by simpa using h1, fun i => by simpa using h2 i⟩
    | succ j =>
      have hj' : j < CR.length := by simpa using hj
      have := crecipeShapeAux_spec sd nR CR (k0 + 1) h3 j hj'
      refine ⟨by simpa using this.1, fun i => ?_⟩
      have e1 : k0 + (j + 1) = k0 + 1 + j := by omega
      rw [e1]
      simpa using this.2 i

/-- the validity of catalytic node `k` at the point `(x, y)` of the cell -/
def CValid (φ : PolMul.Spectral ℂ) (CR : List CEntry) (x y : ℝ) (k : ℕ) : Prop :=
  ∃ K : Set (Fin 3 → ℝ), IsOpen K ∧ IsConeSet K ∧
    (∀ z, InCone (CR.getD k default).V z → z ≠ 0 → z ∈ K) ∧
    TariffOn φ (fun u => peval ((CR.getD k default).Lhat u) x y / ONE) K

/-- **Every catalytic node of a checked record recipe is a conditional tariff on an open cone
containing its punctured vertex cone.** -/
theorem crecipe_valid (G : GlobalRule) (CRule : CatalyticRule) {S : SeedPrm} {C : Cell}
    {R : List GEntry} {B : ℚ} {CR : List CEntry} {sd : Bool}
    (hchk : AllChecked S C R) (hsh : recipeShapeAux sd 0 R = true)
    (hcchk : ∀ k < CR.length, ccheckAt S C R B CR k = true)
    (hcsh : crecipeShapeAux sd R.length 0 CR = true)
    {φ : PolMul.Spectral ℂ} {x y : ℝ} (hx : |x| ≤ 1) (hy : |y| ≤ 1)
    (hθ : UpperProfile φ (fun i => thetaReal S.t C i x y))
    (hseed : sd = true →
      ∀ h, NNN13.AffineBound φ (fun j => seedR S (fun l => thetaReal S.t C l x y) h j))
    {l : ℕ} {Sq : DyadicTensor (fun _ => l)} (hS : (2 : ℝ) ^ ((B : ℝ) * l) < value φ Sq) :
    ∀ k < CR.length, CValid φ CR x y k := by
  have hglob := recipe_valid G hchk hsh hx hy hθ hseed
  intro k
  induction k using Nat.strong_induction_on with
  | _ k IH =>
    intro hk
    obtain ⟨htau, hcaus⟩ := crecipeShapeAux_spec sd R.length CR 0 hcsh k hk
    simp only [zero_add] at hcaus
    -- the parents and their domains
    have hparK : ∀ i, ∃ K : Set (Fin 3 → ℝ), IsOpen K ∧ IsConeSet K ∧
        (∀ Vf, cparV CR ((CR.getD k default).node.par i) = some Vf →
          ∀ z, InCone Vf z → z ≠ 0 → z ∈ K) ∧
        (cparV CR ((CR.getD k default).node.par i) = none → K = Set.univ) ∧
        TariffOn φ (fun u => cparR S C R CR ((CR.getD k default).node.par i) i u x y) K := by
      intro i
      have hc := hcaus i
      generalize hr : (CR.getD k default).node.par i = r at hc ⊢
      cases r with
      | glob g =>
        refine ⟨Set.univ, isOpen_univ, fun _ _ _ _ => trivial,
          fun Vf hV => by simp [cparV] at hV, fun _ => rfl, tariffOn_univ ?_⟩
        show NNN13.AffineBound φ (fun u => parR S C R g i u x y)
        cases g with
        | star => exact star_valid hθ.1 i
        | seed h => exact hseed (by simpa [crefOK] using hc) h
        | node m =>
          simp only [crefOK, decide_eq_true_eq] at hc
          exact hglob m hc
      | cat m =>
        simp only [crefOK, decide_eq_true_eq] at hc
        obtain ⟨K, hKo, hKc, hKV, hKT⟩ := IH m hc (by omega)
        refine ⟨K, hKo, hKc, fun Vf hV => ?_, fun hV => by simp [cparV] at hV, hKT⟩
        simp only [cparV, Option.some.injEq] at hV
        subst hV
        exact hKV
    choose Kp hKpo hKpc hKpV hKpu hKpT using hparK
    -- the gates of the node
    obtain ⟨hact, hbeta, hrp0, hrp1, hlam, hret, hvpos, hverts⟩ :=
      ccheckAt_spec (hcchk k hk) hx hy
    -- the retained family
    have hRet : RetRule (CR.getD k default).node (fun i => thetaReal S.t C i x y) B
        (fun i u => cparR S C R CR ((CR.getD k default).node.par i) i u x y)
        (Kp (CR.getD k default).node.p) := by
      refine ⟨hrp0, hrp1, ?_⟩
      rcases hVp : cparV CR ((CR.getD k default).node.par (CR.getD k default).node.p) with _ | Vpp
      · left
        rw [hKpu _ hVp]
        intro _ _ _
        trivial
      · right
        obtain ⟨hk1, hseg⟩ := hret Vpp hVp
        refine ⟨hk1, fun ξ h1 h2 => hKpV _ Vpp hVp _ ?_ ?_⟩
        · have := hseg ξ (by push_cast at h1 ⊢; linarith) (by push_cast at h2 ⊢; linarith)
          refine this.congr fun u => ?_
          simp only [rdirR]
          split_ifs <;> push_cast <;> ring
        · intro h0
          have hne1 := (cj_ne_p (CR.getD k default).node).symm
          have hne2 := (ck_ne_p (CR.getD k default).node).symm
          have hr : rdirR (CR.getD k default).node (CR.getD k default).node.p = 0 := by
            simp only [rdirR]
            rw [if_neg (by rintro (h | h) <;> [exact hne1 h; exact hne2 h])]
          have hp : (1 : ℝ) - ξ * rdirR (CR.getD k default).node (CR.getD k default).node.p = 0 :=
            congrFun h0 (CR.getD k default).node.p
          rw [hr, mul_zero, sub_zero] at hp
          exact one_ne_zero hp
    have hT := CRule φ _ B l Sq hS hθ (CR.getD k default).node _ Kp hact htau hbeta hKpo hKpc hKpT
      hRet
    refine ⟨_, isOpen_cDom hKpo, isConeSet_cDom hKpc, fun z hz hz0 => ?_, tariffOn_mono hT hlam⟩
    refine ⟨pos_of_cone hvpos hz hz0, ?_, ?_⟩
    · exact famRule_of_verts (cj_ne_p _) (cj_ne_ck _) htau (hKpV _) (hKpu _) hvpos
        (fun pt hpt => (hverts pt hpt).1) (fun pt hpt => (hverts pt hpt).2.2.1) hz hz0
    · exact famRule_of_verts (ck_ne_p _) (cj_ne_ck _).symm htau (hKpV _) (hKpu _) hvpos
        (fun pt hpt => (hverts pt hpt).2.1) (fun pt hpt => (hverts pt hpt).2.2.2) hz hz0

/-! ## Pieces -/

/-- `B` bounds every cube at `φ` -/
def CubeBound (B : ℝ) (φ : PolMul.Spectral ℂ) : Prop :=
  ∀ (l : ℕ) (S : DyadicTensor (fun _ => l)), value φ S ≤ (2 : ℝ) ^ (B * l)

lemma cube_of_affine {φ : PolMul.Spectral ℂ} {c : Fin 3 → ℝ} {B : ℝ} (h : NNN13.AffineBound φ c)
    (hs : c 0 + c 1 + c 2 ≤ B) : CubeBound B φ := by
  intro l S
  refine (h _ S).trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_)
  simp only [NNN13.plane]
  have hl : (0 : ℝ) ≤ l := Nat.cast_nonneg l
  have := mul_le_mul_of_nonneg_right hs hl
  linarith

/-- **A global piece** (exterior or direct global cell): its terminal tariff is a global tariff
with coefficient sum at most `B` on the cell. -/
theorem global_cube (G : GlobalRule) {S : SeedPrm} {C : Cell} {R : List GEntry} {sd : Bool}
    (hchk : AllChecked S C R) (hsh : recipeShapeAux sd 0 R = true) {k : ℕ} (hk : k < R.length)
    {B : ℚ} {lvl : ℕ}
    (hterm : termCheck (sumL [(R.getD k default).Pk 0, (R.getD k default).Pk 1,
      (R.getD k default).Pk 2]) B lvl = true)
    {φ : PolMul.Spectral ℂ} {x y : ℝ} (hx : |x| ≤ 1) (hy : |y| ≤ 1)
    (hθ : UpperProfile φ (fun i => thetaReal S.t C i x y))
    (hseed : sd = true →
      ∀ h, NNN13.AffineBound φ (fun j => seedR S (fun l => thetaReal S.t C l x y) h j)) :
    CubeBound (B : ℝ) φ := by
  have hv := recipe_valid G hchk hsh hx hy hθ hseed k hk
  have hs := termCheck_sum hterm hx hy
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at hs
  exact cube_of_affine hv (by linarith)

/-- **A record piece**: under `φ(S) > 2^{B l}` the terminal catalytic node prices the cube at
most `B l`, a contradiction. -/
theorem record_cube (G : GlobalRule) (CRule : CatalyticRule) {S : SeedPrm} {C : Cell}
    {R : List GEntry} {B : ℚ} {CR : List CEntry} {sd : Bool}
    (hchk : AllChecked S C R) (hsh : recipeShapeAux sd 0 R = true)
    (hcchk : ∀ k < CR.length, ccheckAt S C R B CR k = true)
    (hcsh : crecipeShapeAux sd R.length 0 CR = true)
    {lvl kT w : ℕ} (hkT : kT < CR.length) (hterm : cterm CR B lvl kT w = true)
    {φ : PolMul.Spectral ℂ} {x y : ℝ} (hx : |x| ≤ 1) (hy : |y| ≤ 1)
    (hθ : UpperProfile φ (fun i => thetaReal S.t C i x y))
    (hseed : sd = true →
      ∀ h, NNN13.AffineBound φ (fun j => seedR S (fun l => thetaReal S.t C l x y) h j)) :
    CubeBound (B : ℝ) φ := by
  intro l Sq
  by_contra hcon
  have hS : (2 : ℝ) ^ ((B : ℝ) * l) < value φ Sq := lt_of_not_ge hcon
  obtain ⟨K, _, hKc, hKV, hKT⟩ :=
    crecipe_valid G CRule hchk hsh hcchk hcsh hx hy hθ hseed hS kT hkT
  obtain ⟨hsum, hcone⟩ := cterm_spec hterm
  have h1 : (fun _ => (1 : ℝ)) ∈ K :=
    hKV _ hcone (fun h => by have := congrFun h 0; simp at this)
  rcases Nat.eq_zero_or_pos l with hl | hl
  · subst hl
    have h0 := star_valid hθ.1 0 _ Sq
    simp only [NNN13.plane, Nat.cast_zero, mul_zero, add_zero, Real.rpow_zero] at h0 hS
    linarith
  · have hlK : (fun i => (((fun _ => l) i : ℕ) : ℝ)) ∈ K := by
      have := hKc _ h1 (l : ℝ) (by exact_mod_cast hl)
      simpa using this
    have hv := hKT _ hlK Sq
    have hle : NNN13.plane (fun u => peval ((CR.getD kT default).Lhat u) x y / ONE)
        (fun i => (((fun _ => l) i : ℕ) : ℝ)) ≤ (B : ℝ) * l := by
      simp only [NNN13.plane]
      have := hsum x y hx hy
      have hl0 : (0 : ℝ) ≤ l := Nat.cast_nonneg l
      have := mul_le_mul_of_nonneg_right this hl0
      linarith
    have := hv.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) hle)
    linarith

end OM.NNN20
