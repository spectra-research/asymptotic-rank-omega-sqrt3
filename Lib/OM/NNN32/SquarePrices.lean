import Lib.OM.NNN32.SquareCore
import Lib.OM.NNN30.Net.Step

/-! # Admissible grid prices for the linear rectangle inequality -/

noncomputable section

namespace OM.NNN32

open OM.NNN30.Net OM.NNN.Raw CoordinateTensor
open scoped Classical

variable {V : Type} [Fintype V] [LinearOrder V]

private def cap (d : V → V → ℝ) (c : ℝ) (R : Rect V) := c * maxPrice d R / crad d R

private lemma crad_cap (d : V → V → ℝ) (c : ℝ) (R : Rect V) :
    crad d R * cap d c R = c * maxPrice d R := by
  unfold cap
  by_cases h : crad d R = 0
  · have eqn := Real.sq_sqrt (show 0 ≤ (d R.a R.c ^ 2 + d R.b R.e ^ 2)/2 by positivity)
    change crad d R ^ 2 = _ at eqn
    rw [h] at eqn
    have ha : d R.a R.c = 0 := by nlinarith [sq_nonneg (d R.b R.e)]
    have hb : d R.b R.e = 0 := by nlinarith [sq_nonneg (d R.a R.c)]
    simp [h,maxPrice,ha,hb]
  · field_simp

private def priceSet (k : Rect V → ℝ) : Set (Rect V → ℝ × ℝ) :=
  {t | ∀ R, 0 ≤ (t R).1 ∧ 0 ≤ (t R).2 ∧ (t R).1 + (t R).2 ≤ k R}

private lemma priceSet_compact (k : Rect V → ℝ) : IsCompact (priceSet k) := by
  have hK : IsCompact (Set.univ.pi fun R => Set.Icc (0 : ℝ) (k R) ×ˢ Set.Icc 0 (k R)) :=
    isCompact_univ_pi fun _ => isCompact_Icc.prod isCompact_Icc
  apply hK.of_isClosed_subset
  · unfold priceSet
    simp only [Set.ofPred_forall]
    apply isClosed_iInter
    intro R
    have a : IsClosed {t : Rect V → ℝ × ℝ | 0 ≤ (t R).1} := isClosed_le continuous_const (by fun_prop)
    have b : IsClosed {t : Rect V → ℝ × ℝ | 0 ≤ (t R).2} := isClosed_le continuous_const (by fun_prop)
    have z : IsClosed {t : Rect V → ℝ × ℝ | (t R).1+(t R).2 ≤ k R} :=
      isClosed_le (by fun_prop) continuous_const
    exact a.inter (b.inter z)
  · intro t ht R _
    obtain ⟨a,b,h⟩ := ht R
    exact ⟨⟨a,by linarith⟩, ⟨b,by linarith⟩⟩

private lemma priceSet_convex (k : Rect V → ℝ) : Convex ℝ (priceSet k) := by
  intro x hx y hy a b ha hb hab R
  obtain ⟨x1,x2,xs⟩ := hx R
  obtain ⟨y1,y2,ys⟩ := hy R
  simp only [Pi.add_apply,Pi.smul_apply,Prod.fst_add,Prod.snd_add,Prod.smul_fst,Prod.smul_snd,
    smul_eq_mul]
  refine ⟨by positivity,by positivity,?_⟩
  linarith [mul_le_mul_of_nonneg_left xs ha, mul_le_mul_of_nonneg_left ys hb,
    congrArg (fun z : ℝ => z*k R) hab]

theorem exists_square_prices {φ : OM.PolMul.Spectral ℂ} {τ : Fin 3 → V}
    {d : V → V → ℝ} {c : ℝ} (hc : 0 ≤ c) (he : SquareExpansion c)
    (hd : MinAdm φ τ d) :
    ∃ lam ∈ priceSet (cap d c), Adm φ (fun i => (τ i,τ i)) (Dlam d lam) := by
  have hk (R : Rect V) : 0 ≤ cap d c R :=
    div_nonneg (mul_nonneg hc ((hd.2.1 _ _).trans (le_max_left _ _))) (crad_nonneg _ _)
  apply exists_adm_Dlam_of (priceSet_compact _)
  intro n p hp
  apply finite_family_of ⟨0, fun R => by simpa using hk R⟩ (priceSet_convex _) (priceSet_compact _)
  intro a ha
  let P := ∑ i, a i • p i
  have hscale {t : ℝ} (ht : 0 ≤ t) (q : Dat V) :
      squareSupport d c (t • q) = t * squareSupport d c q := by
    simp only [squareSupport,Prod.smul_fst,Prod.smul_snd,Pi.smul_apply,smul_eq_mul,
      ← mul_max_of_nonneg _ _ ht,mul_add,Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun R _ => by ring
  have hcont : Continuous (squareSupport d c) := by unfold squareSupport; fun_prop
  have h := conv_Ach_of hcont hscale (square_core hc he hd.1 hd.2.1) hp a ha.1
  let lam (R : Rect V) : ℝ × ℝ := if P.2.2.2 R ≤ P.2.2.1 R then (cap d c R,0) else (0,cap d c R)
  refine ⟨lam,fun R => ?_,h.trans_eq ?_⟩
  · dsimp [lam]
    split_ifs <;> simp [hk]
  · change squareSupport d c P = linD d lam P
    unfold squareSupport linD
    congr 1
    refine Finset.sum_congr rfl fun R _ => ?_
    by_cases hh : P.2.2.2 R ≤ P.2.2.1 R
    · simp only [lam,if_pos hh,max_eq_left hh, zero_mul,add_zero,← mul_assoc,crad_cap]
    · simp only [lam,if_neg hh,max_eq_right (le_of_not_ge hh), zero_mul,zero_add,← mul_assoc,crad_cap]

/-- An equal-width extension fixes the diagonal by minimality. The two axis bounds
alone suffice to compare the diagonal with the original price. -/
theorem square_extension {φ : OM.PolMul.Spectral ℂ} {τ : Fin 3 → V} {d : V → V → ℝ}
    {c : ℝ} (hc : 1 ≤ c) (he : SquareExpansion c) (hd : MinAdm φ τ d) :
    ∃ D : V × V → V × V → ℝ, MinAdm φ (fun i => (τ i,τ i)) D ∧
      (∀ a b z, D (a,b) (z,b) ≤ d a z / 2) ∧
      (∀ a b e, D (a,b) (a,e) ≤ d b e / 2) ∧
      (∀ a b z e, D (a,b) (z,e) + D (a,e) (z,b) ≤ c * max (d a z) (d b e)) ∧
      (∀ a z, D (a,a) (z,z) = d a z) := by
  obtain ⟨lam,hl,hadm⟩ := exists_square_prices (zero_le_one.trans hc) he hd
  have hnon (s t : V × V) : 0 ≤ Dlam d lam s t := by
    unfold Dlam
    rcases classify s t with _ | ⟨R,_|_⟩
    · exact div_nonneg (add_nonneg (hd.2.1 _ _) (hd.2.1 _ _)) (by norm_num)
    · exact mul_nonneg (crad_nonneg _ _) (hl R).2.1
    · exact mul_nonneg (crad_nonneg _ _) (hl R).1
  obtain ⟨D,hD,hle⟩ := exists_minAdm hadm hnon (Dlam_diag_zero hd.2.2.1 lam)
  have hrow a b z := (hle (a,b) (z,b)).trans (Dlam_row d hd.2.2.1 lam _ _ _).le
  have hcol a b e := (hle (a,b) (a,e)).trans (Dlam_col d hd.2.2.1 lam _ _ _).le
  refine ⟨D,hD,hrow,hcol,?_,?_⟩
  · intro a b z e
    have hcmax : max (d a z) (d b e) ≤ c * max (d a z) (d b e) :=
      le_mul_of_one_le_left ((hd.2.1 _ _).trans (le_max_left _ _)) hc
    by_cases haz : a = z
    · subst z
      have h1 := hcol a b e
      have h2 := hcol a e b
      rw [hd.symm e b] at h2
      exact (show _ ≤ d b e by linarith).trans ((le_max_right _ _).trans hcmax)
    by_cases hbe : b = e
    · subst e
      exact (show _ ≤ d a z by linarith [hrow a b z]).trans ((le_max_left _ _).trans hcmax)
    obtain ⟨R,side,h1,h2,hr,hc'⟩ := classify_diagonals d hd.symm haz hbe
    refine (add_le_add (hle _ _) (hle _ _)).trans ?_
    have hprice := mul_le_mul_of_nonneg_left (hl R).2.2 (crad_nonneg d R)
    rw [mul_add,crad_cap,maxPrice,hr,hc'] at hprice
    unfold Dlam
    rw [h1,h2]
    cases side <;> simpa [add_comm] using hprice
  · have had : Adm φ τ (fun a z => D (a,a) (z,z)) := by
      intro O0 O1 O2 _ _ _ N hN hv
      have h := hD.1 O0 O1 O2 (N.relocate fun s => (s,s)) (hN.relocate _ fun i => rfl)
        (by rw [TN.Z_relocate]; exact hv)
      rw [TN.Z_relocate,TN.cost_relocate] at h
      exact h
    have hh a z : D (a,a) (z,z) ≤ d a z := by
      have ht := hD.triangle (a,a) (a,z) (z,z)
      linarith [hcol a a z,hrow a z z]
    have hdiag := hd.2.2.2 _ had (fun _ _ => hD.2.1 _ _) (fun _ => hD.2.2.1 _) hh
    exact fun a z => congrFun (congrFun hdiag a) z

end OM.NNN32
