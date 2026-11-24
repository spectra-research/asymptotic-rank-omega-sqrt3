import Lib.OM.NNN20.CRecipe
import Lib.OM.NNN18.FactsU
import Lib.OM.NNN18.FactsC
import Lib.OM.NNN18.PackStep
import Lib.OM.NNN12.RecursiveTransport

/-!
# From pieces to every spectral point -/

noncomputable section
open scoped BigOperators
open CoordinateTensor OM.NNN.Raw
open OM.NNN12 (Shape DyadicTensor)
open Foundations.OrientationTransport Lib.E.RectangularSpectrum

namespace OM.NNN20

local notation "θφ" => Foundations.PairUnitExponents.theta

/-! ## Relabelling -/

/-- cube bounds at `ψ` give cube bounds at `φ` -/
def Reach (φ ψ : PolMul.Spectral ℂ) : Prop := ∀ B : ℝ, CubeBound B ψ → CubeBound B φ

lemma Reach.trans {φ ψ χ : PolMul.Spectral ℂ} (h1 : Reach φ ψ) (h2 : Reach ψ χ) : Reach φ χ :=
  fun B h => h1 B (h2 B h)

lemma Reach.refl (φ : PolMul.Spectral ℂ) : Reach φ φ := fun _ h => h

lemma gen02 (φ : PolMul.Spectral ℂ) :
    ∃ ψ, Reach φ ψ ∧ ∀ j, θφ ψ j = θφ φ (![2, 1, 0] j) := by
  refine ⟨pullPoint φ (rot 0), fun B h l S => ?_, fun j => ?_⟩
  · have e := NNN11.value_swap02 φ S
    rw [← e]
    exact h l (swap02 S)
  · rw [theta_legReindex]
    congr 1
    fin_cases j <;> decide +kernel

lemma gen12 (φ : PolMul.Spectral ℂ) :
    ∃ ψ, Reach φ ψ ∧ ∀ j, θφ ψ j = θφ φ (![0, 2, 1] j) := by
  refine ⟨pullPoint φ (rot 1), fun B h l S => ?_, fun j => ?_⟩
  · have e := NNN11.value_swap12 φ S
    rw [← e]
    exact h l (swap12 S)
  · rw [theta_legReindex]
    congr 1
    fin_cases j <;> decide +kernel

lemma gen01 (φ : PolMul.Spectral ℂ) :
    ∃ ψ, Reach φ ψ ∧ ∀ j, θφ ψ j = θφ φ (![1, 0, 2] j) := by
  obtain ⟨ψ1, h1, e1⟩ := gen02 φ
  obtain ⟨ψ2, h2, e2⟩ := gen12 ψ1
  obtain ⟨ψ3, h3, e3⟩ := gen02 ψ2
  refine ⟨ψ3, h1.trans (h2.trans h3), fun j => ?_⟩
  rw [e3, e2, e1]
  fin_cases j <;> rfl

/-- every upper profile can be ordered by relabelling -/
lemma exists_sorted (φ : PolMul.Spectral ℂ) (t : Fin 3 → ℝ) (ht : ∀ i, θφ φ i ≤ t i) :
    ∃ (ψ : PolMul.Spectral ℂ) (s : Fin 3 → ℝ), Reach φ ψ ∧ (∀ i, θφ ψ i ≤ s i) ∧ s 1 ≤ s 0 ∧
      s 2 ≤ s 1 ∧
      s 0 + s 1 + s 2 = t 0 + t 1 + t 2 ∧ ∀ i, ∃ j, s i = t j := by
  rcases le_total (t 1) (t 0) with h01 | h10 <;> rcases le_total (t 2) (t 1) with h12 | h21 <;>
    rcases le_total (t 2) (t 0) with h02 | h20
  · -- t0 ≥ t1 ≥ t2
    exact ⟨φ, t, Reach.refl φ, ht, h01, h12, rfl, fun i => ⟨i, rfl⟩⟩
  · -- t0 ≥ t1 ≥ t2 ≥ t0
    exact ⟨φ, t, Reach.refl φ, ht, h01, h12, rfl, fun i => ⟨i, rfl⟩⟩
  · -- t0 ≥ t2 ≥ t1
    obtain ⟨ψ, h, e⟩ := gen12 φ
    refine ⟨ψ, ![t 0, t 2, t 1], h, fun j => ?_, h02, h21, by simp; ring, fun i => ?_⟩
    · rw [e]; fin_cases j <;> exact ht _
    · fin_cases i <;> simp
  · -- t2 ≥ t0 ≥ t1
    obtain ⟨ψ1, h1, e1⟩ := gen02 φ
    obtain ⟨ψ2, h2, e2⟩ := gen12 ψ1
    refine ⟨ψ2, ![t 2, t 0, t 1], h1.trans h2, fun j => ?_, h20, h01, by simp; ring, fun i => ?_⟩
    · rw [e2, e1]; fin_cases j <;> exact ht _
    · fin_cases i <;> simp
  · -- t1 ≥ t0 ≥ t2
    obtain ⟨ψ, h, e⟩ := gen01 φ
    refine ⟨ψ, ![t 1, t 0, t 2], h, fun j => ?_, h10, h02, by simp; ring, fun i => ?_⟩
    · rw [e]; fin_cases j <;> exact ht _
    · fin_cases i <;> simp
  · -- t1 ≥ t2 ≥ t0
    obtain ⟨ψ1, h1, e1⟩ := gen01 φ
    obtain ⟨ψ2, h2, e2⟩ := gen12 ψ1
    refine ⟨ψ2, ![t 1, t 2, t 0], h1.trans h2, fun j => ?_, h12, h20, by simp; ring, fun i => ?_⟩
    · rw [e2, e1]; fin_cases j <;> exact ht _
    · fin_cases i <;> simp
  · -- t0 ≤ t1 ≤ t2 ≤ t0: all equal
    exact ⟨φ, t, Reach.refl φ, ht, by linarith, by linarith, rfl, fun i => ⟨i, rfl⟩⟩
  · -- t2 ≥ t1 ≥ t0
    obtain ⟨ψ, h, e⟩ := gen02 φ
    refine ⟨ψ, ![t 2, t 1, t 0], h, fun j => ?_, h21, h10, by simp; ring, fun i => ?_⟩
    · rw [e]; fin_cases j <;> exact ht _
    · fin_cases i <;> simp

/-! ## The ordered sector -/

/-- the ordered profile `(t + r, t - r/2 + 3q/2, t - r/2 - 3q/2)` (as in `thetaReal`) -/
def base (t : ℚ) (r q : ℝ) : Fin 3 → ℝ :=
  ![(t : ℝ) + r, (t : ℝ) + ((((-1 / 2 : ℚ) : ℝ)) * r + (((3 / 2 : ℚ) : ℝ)) * q),
    (t : ℝ) - ((((1 / 2 : ℚ) : ℝ)) * r + (((3 / 2 : ℚ) : ℝ)) * q)]

lemma base_sum (t : ℚ) (r q : ℝ) : base t r q 0 + base t r q 1 + base t r q 2 = 3 * t := by
  simp only [base]; norm_num; ring

lemma base_of_sorted {t : ℚ} {s : Fin 3 → ℝ} (hs : s 0 + s 1 + s 2 = 3 * t) :
    ∀ i, s i = base t (s 0 - t) ((s 1 - s 2) / 3) i := by
  intro i
  fin_cases i <;> simp [base] <;> norm_num <;> linarith

lemma thetaReal_eq (t : ℚ) (C : Cell) (i : Fin 3) (x y : ℝ) :
    thetaReal t C i x y = base t (rOf C x) (qOf C x y) (C.perm i) := rfl

/-- an affine coordinate on `[lo, hi]` -/
lemma exists_coord {lo hi v : ℝ} (h1 : lo ≤ v) (h2 : v ≤ hi) :
    ∃ x : ℝ, |x| ≤ 1 ∧ (lo + hi) / 2 + (hi - lo) / 2 * x = v := by
  rcases eq_or_lt_of_le (h1.trans h2) with heq | hlt
  · exact ⟨0, by simp, by subst heq; linarith⟩
  · refine ⟨(v - (lo + hi) / 2) / ((hi - lo) / 2), ?_, ?_⟩
    · rw [abs_div, abs_of_pos (by linarith : (0 : ℝ) < (hi - lo) / 2), div_le_one (by linarith),
        abs_le]
      constructor <;> linarith
    · field_simp
      ring

lemma exists_rOf (C : Cell) {r : ℝ} (ha : (C.a : ℝ) ≤ r) (hb : r ≤ C.b) :
    ∃ x : ℝ, |x| ≤ 1 ∧ rOf C x = r := by
  obtain ⟨x, hx, e⟩ := exists_coord ha hb
  exact ⟨x, hx, by simp only [rOf]; push_cast; linarith⟩

lemma exists_qOf (C : Cell) {x r q : ℝ} (hr : rOf C x = r) (hq0 : 0 ≤ q) (hqr : q ≤ r)
    (ha : (C.a : ℝ) ≤ r) (hb : r ≤ C.b) (hc : (C.c : ℝ) ≤ q) (hd : q ≤ C.d) :
    ∃ y : ℝ, |y| ≤ 1 ∧ qOf C x y = q := by
  by_cases hrs : C.rs
  · have hlo : ((max 0 (C.a - C.d) : ℚ) : ℝ) ≤ r - q := by
      push_cast
      exact max_le (by linarith) (by linarith)
    have hhi : r - q ≤ ((C.b - C.c : ℚ) : ℝ) := by push_cast; linarith
    obtain ⟨y, hy, e⟩ := exists_coord hlo hhi
    refine ⟨y, hy, ?_⟩
    simp only [qOf, hrs, if_true, hr]
    push_cast at e ⊢
    linarith
  · obtain ⟨y, hy, e⟩ := exists_coord hc hd
    refine ⟨y, hy, ?_⟩
    simp only [qOf, hrs, if_false, Bool.false_eq_true]
    push_cast at e ⊢
    linarith

/-- **A piece certified on a cell bounds the cube at every spectral point whose ordered profile
lies in the cell's claimed rectangle.** -/
theorem piece_apply {t : ℚ} {C : Cell} {B : ℝ} {SH : PolMul.Spectral ℂ → (Fin 3 → ℝ) → Prop}
    (PT : ∀ (φ : PolMul.Spectral ℂ) (x y : ℝ), |x| ≤ 1 → |y| ≤ 1 →
      UpperProfile φ (fun i => thetaReal t C i x y) → SH φ (fun i => thetaReal t C i x y) →
        CubeBound B φ)
    (hperm : C.perm = ![0, 1, 2] ∨ C.perm = ![1, 0, 2])
    {r q : ℝ} (hq0 : 0 ≤ q) (hqr : q ≤ r) (ha : (C.a : ℝ) ≤ r) (hb : r ≤ C.b)
    (hc : (C.c : ℝ) ≤ q) (hd : q ≤ C.d)
    {ψ : PolMul.Spectral ℂ} (hψ : ∀ i, θφ ψ i ≤ base t r q i)
    (hmem : ∀ i, base t r q i ∈ Set.Icc (0 : ℝ) 1) (hsum : 3 * (t : ℝ) ≤ 9 / 4)
    (hSH : ∀ φ : PolMul.Spectral ℂ, UpperProfile φ (fun i => base t r q (C.perm i)) →
      SH φ (fun i => base t r q (C.perm i))) :
    CubeBound B ψ := by
  obtain ⟨x, hx, hr⟩ := exists_rOf C ha hb
  obtain ⟨y, hy, hq⟩ := exists_qOf C hr hq0 hqr ha hb hc hd
  have hth : (fun i => thetaReal t C i x y) = fun i => base t r q (C.perm i) := by
    funext i; rw [thetaReal_eq, hr, hq]
  have hsum' : ∀ π : Fin 3 → Fin 3, (π = ![0, 1, 2] ∨ π = ![1, 0, 2]) →
      base t r q (π 0) + base t r q (π 1) + base t r q (π 2) ≤ 9 / 4 := by
    intro π hπ
    have := base_sum t r q
    rcases hπ with h | h <;> subst h <;> simp <;> linarith
  rcases hperm with hp | hp
  · have hU : UpperProfile ψ (fun i => base t r q (C.perm i)) := by
      refine ⟨fun i => ?_, fun i => ?_, ?_⟩
      · rw [hp]; fin_cases i <;> exact hψ _
      · rw [hp]; fin_cases i <;> exact hmem _
      · rw [hp]; exact hsum' _ (Or.inl rfl)
    exact PT ψ x y hx hy (hth ▸ hU) (hth ▸ hSH ψ hU)
  · obtain ⟨ψ', hreach, e⟩ := gen01 ψ
    have hU : UpperProfile ψ' (fun i => base t r q (C.perm i)) := by
      refine ⟨fun i => ?_, fun i => ?_, ?_⟩
      · rw [hp, e]; fin_cases i <;> exact hψ _
      · rw [hp]; fin_cases i <;> exact hmem _
      · rw [hp]; exact hsum' _ (Or.inr rfl)
    exact hreach B (PT ψ' x y hx hy (hth ▸ hU) (hth ▸ hSH ψ' hU))

/-- **The star tail**: for `r ≥ 2t - B` the coefficient star at the largest exponent prices the
cube at `θ₁ + θ₂ = 2t - r ≤ B`. -/
theorem tail_cube {t : ℚ} {r q B : ℝ} {ψ : PolMul.Spectral ℂ} (hψ : ∀ i, θφ ψ i ≤ base t r q i)
    (hr : 2 * (t : ℝ) - r ≤ B) : CubeBound B ψ := by
  have hs := star_valid hψ 0
  refine cube_of_affine hs ?_
  simp only [starR, base, third]
  norm_num
  linarith


def seedU20 : SeedPrm :=
  ⟨3 / 4, 40271 / 100000, 6233 / 12500, 35329 / 50000, 753 / 2500, 38569 / 100000⟩

lemma seedU20_eq (θ : Fin 3 → ℝ) (h : Fin 3) :
    (fun j => seedR seedU20 θ h j) = OM.NNN18.tariff OM.NNN18.U (fun i => θ i - 3 / 4) h := by
  funext j
  fin_cases h <;> fin_cases j <;>
    simp [seedR, seedU20, OM.NNN18.tariff, OM.NNN18.U, OM.NNN18.other, third] <;> norm_num <;> ring

theorem seedsU {φ : PolMul.Spectral ℂ} {θ : Fin 3 → ℝ} (hθ : UpperProfile φ θ)
    (hs : θ 0 + θ 1 + θ 2 = 9 / 4) (hR : ∀ i, θ i - 3 / 4 ≤ 10001 / 100000) (h : Fin 3) :
    NNN13.AffineBound φ (fun j => seedR seedU20 θ h j) := by
  have hδ : OM.NNN18.InTri OM.NNN18.FactsU.facts.R (fun i => θ i - 3 / 4) := by
    refine ⟨by linarith, fun i => ?_⟩
    simp only [OM.NNN18.FactsU.facts, OM.NNN18.FocusU.R]
    exact hR i
  have htheta : OM.NNN18.theta OM.NNN18.U (fun i => θ i - 3 / 4) = θ := by
    funext i; simp [OM.NNN18.theta, OM.NNN18.U]
  have hθ' : ∀ i, θφ φ i ≤ OM.NNN18.theta OM.NNN18.U (fun i => θ i - 3 / 4) i := by
    rw [htheta]; exact hθ.1
  have hsum : ∑ i, OM.NNN18.theta OM.NNN18.U (fun i => θ i - 3 / 4) i ≤ 9 / 4 := by
    rw [htheta, Fin.sum_univ_three]; linarith
  rw [seedU20_eq]
  intro v U
  exact OM.NNN18.tariffs_valid OM.NNN18.U OM.NNN18.FactsU.facts OM.NNN18.triangleStep φ hδ hθ'
    hsum h v U


def seedC20 : SeedPrm := ⟨2 / 3, 3637 / 10000, 4431 / 10000, 13 / 20, 11 / 40, 3 / 8⟩

lemma seedC20_eq (θ : Fin 3 → ℝ) (h : Fin 3) :
    (fun j => seedR seedC20 θ h j) = OM.NNN18.tariff OM.NNN18.C (fun i => θ i - 2 / 3) h := by
  funext j
  fin_cases h <;> fin_cases j <;>
    simp [seedR, seedC20, OM.NNN18.tariff, OM.NNN18.C, OM.NNN18.other, third] <;> norm_num <;> ring

theorem seedsC {φ : PolMul.Spectral ℂ} {θ : Fin 3 → ℝ} (hθ : UpperProfile φ θ)
    (hs : θ 0 + θ 1 + θ 2 = 2) (hR : ∀ i, θ i - 2 / 3 ≤ 2503 / 30000) (h : Fin 3) :
    NNN13.AffineBound φ (fun j => seedR seedC20 θ h j) := by
  have hδ : OM.NNN18.InTri OM.NNN18.FactsC.facts.R (fun i => θ i - 2 / 3) := by
    refine ⟨by linarith, fun i => ?_⟩
    simp only [OM.NNN18.FactsC.facts, OM.NNN18.FocusC.R]
    exact hR i
  have htheta : OM.NNN18.theta OM.NNN18.C (fun i => θ i - 2 / 3) = θ := by
    funext i; simp [OM.NNN18.theta, OM.NNN18.C]
  have hθ' : ∀ i, θφ φ i ≤ OM.NNN18.theta OM.NNN18.C (fun i => θ i - 2 / 3) i := by
    rw [htheta]; exact hθ.1
  have hsum : ∑ i, OM.NNN18.theta OM.NNN18.C (fun i => θ i - 2 / 3) i ≤ 9 / 4 := by
    rw [htheta, Fin.sum_univ_three]; linarith
  rw [seedC20_eq]
  intro v U
  exact OM.NNN18.tariffs_valid OM.NNN18.C OM.NNN18.FactsC.facts OM.NNN18.triangleStep φ hδ hθ'
    hsum h v U

end OM.NNN20
