import Lib.OM.NNN12.Potential
import Lib.OM.NNN11.Extraction
import Lib.OM.NNN11.InnerSpectral

noncomputable section
open scoped BigOperators Classical
namespace OM.NNN12
open CoordinateTensor OM.NNN.Raw OM.NNN2 Foundations.PairUnitExponents
open NNN8 (BinaryWord binary_word_card)

abbrev Shape := Fin 3 → ℕ
abbrev DyadicTensor (x : Shape) :=
  Tensor ℂ (BinaryWord (x 0)) (BinaryWord (x 1)) (BinaryWord (x 2))

def volume (x : Shape) : ℝ := (x 0 : ℝ) + x 1 + x 2
def target (x : Shape) : ℝ := fallbackPotential (x 0) (x 1) (x 2)

lemma volume_nonneg (x : Shape) : 0 ≤ volume x := by unfold volume; positivity
lemma target_nonneg (x : Shape) : 0 ≤ target x :=
  fallbackPotential_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-- An elementary bound, proved before any recursive assumption. -/
theorem value_le_volume (φ : PolMul.Spectral ℂ) (x : Shape) (T : DyadicTensor x) :
    value φ T ≤ (2 : ℝ) ^ volume x := by
  have hr : Restricts (mm (BinaryWord (x 0)) (BinaryWord (x 1)) Unit) T := by
    simpa using! NNN11.starAB id (fun _ => ()) id (fun _ => ()) T
  have h := (value_mono φ (restricts_degenerates _ _ hr)).trans (NNN10.value_mm_card_le φ)
  simp only [binary_word_card, Fintype.card_unique, Nat.cast_one, Real.one_rpow,
    mul_one, Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast,
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
    ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)] at h
  apply h.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_)
  have h0 := mul_le_mul_of_nonneg_left (theta_mem_Icc φ 1).2 (Nat.cast_nonneg (x 0) : (0 : ℝ) ≤ x 0)
  have h1 := mul_le_mul_of_nonneg_left (theta_mem_Icc φ 0).2 (Nat.cast_nonneg (x 1) : (0 : ℝ) ≤ x 1)
  dsimp [volume]
  nlinarith [show (0 : ℝ) ≤ x 2 from Nat.cast_nonneg _]

/-- Zero is adjoined explicitly. Scalar formats and zero spectral values are
handled directly, so no logarithm of zero enters the set being bounded. -/
def excessSet (φ : PolMul.Spectral ℂ) (F : Shape → ℝ) : Set ℝ :=
  insert 0 {r | ∃ (x : Shape) (T : DyadicTensor x),
    0 < value φ T ∧ 0 < volume x ∧ r = (Real.logb 2 (value φ T) - F x) / volume x}

def excess (φ : PolMul.Spectral ℂ) (F : Shape → ℝ) : ℝ := sSup (excessSet φ F)

lemma excessSet_nonempty (φ : PolMul.Spectral ℂ) (F : Shape → ℝ) :
    (excessSet φ F).Nonempty := ⟨0, Set.mem_insert _ _⟩

lemma excessSet_bddAbove (φ : PolMul.Spectral ℂ) {F : Shape → ℝ} (hF : ∀ x, 0 ≤ F x) :
    BddAbove (excessSet φ F) := by
  refine ⟨1, ?_⟩
  intro r hr
  rcases hr with rfl | ⟨x, T, hv, hx, rfl⟩
  · norm_num
  · apply (div_le_iff₀ hx).2
    have hh := (Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ) < 2) hv).2
      (value_le_volume φ x T)
    linarith [hF x]

lemma excess_nonneg (φ : PolMul.Spectral ℂ) {F : Shape → ℝ} (hF : ∀ x, 0 ≤ F x) :
    0 ≤ excess φ F := le_csSup (excessSet_bddAbove φ hF) (Set.mem_insert _ _)

lemma excess_le_one (φ : PolMul.Spectral ℂ) {F : Shape → ℝ} (hF : ∀ x, 0 ≤ F x) :
    excess φ F ≤ 1 := by
  apply csSup_le (excessSet_nonempty φ F)
  intro r hr
  rcases hr with rfl | ⟨x, T, hv, hx, rfl⟩
  · norm_num
  · apply (div_le_iff₀ hx).2
    have hh := (Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ) < 2) hv).2
      (value_le_volume φ x T)
    linarith [hF x]

/-- The supremum controls every format, whether or not it is attained. -/
theorem value_le_excess (φ : PolMul.Spectral ℂ) {F : Shape → ℝ} (hF : ∀ x, 0 ≤ F x)
    (x : Shape) (T : DyadicTensor x) :
    value φ T ≤ (2 : ℝ) ^ (F x + excess φ F * volume x) := by
  by_cases hx : 0 < volume x
  · by_cases hv : 0 < value φ T
    · have hh : (Real.logb 2 (value φ T) - F x) / volume x ≤ excess φ F :=
        le_csSup (excessSet_bddAbove φ hF) (Or.inr ⟨x, T, hv, hx, rfl⟩)
      apply (Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ) < 2) hv).1
      have := (div_le_iff₀ hx).1 hh
      linarith
    · exact (le_of_not_gt hv).trans (by positivity)
  · have hx0 : volume x = 0 := le_antisymm (le_of_not_gt hx) (volume_nonneg x)
    apply (value_le_volume φ x T).trans
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    simpa [hx0] using! hF x

theorem excess_le_of_bound (φ : PolMul.Spectral ℂ) (F : Shape → ℝ) {ε : ℝ} (hε : 0 ≤ ε)
    (hb : ∀ (x : Shape) (T : DyadicTensor x), value φ T ≤ (2 : ℝ) ^ (F x + ε * volume x)) :
    excess φ F ≤ ε := by
  apply csSup_le (excessSet_nonempty φ F)
  intro r hr
  rcases hr with rfl | ⟨x, T, hv, hx, rfl⟩
  · exact hε
  · apply (div_le_iff₀ hx).2
    have hh := (Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ) < 2) hv).2 (hb x T)
    linarith

/-- This is the precise premise to be discharged by the network and its
analytic supersolution certificate, after removing finite constants. -/
def Improves (φ : PolMul.Spectral ℂ) (F : Shape → ℝ) (γ : ℝ) : Prop :=
  ∀ ε : ℝ, 0 ≤ ε →
    (∀ (x : Shape) (T : DyadicTensor x), value φ T ≤ (2 : ℝ) ^ (F x + ε * volume x)) →
    ∀ (x : Shape) (T : DyadicTensor x), value φ T ≤ (2 : ℝ) ^ (F x + γ * ε * volume x)

theorem excess_le_mul (φ : PolMul.Spectral ℂ) {F : Shape → ℝ} (hF : ∀ x, 0 ≤ F x)
    {γ : ℝ} (hγ : 0 ≤ γ) (step : Improves φ F γ) :
    excess φ F ≤ γ * excess φ F :=
  excess_le_of_bound φ F (mul_nonneg hγ (excess_nonneg φ hF))
    (step (excess φ F) (excess_nonneg φ hF) (value_le_excess φ hF))

theorem excess_eq_zero (φ : PolMul.Spectral ℂ) {F : Shape → ℝ} (hF : ∀ x, 0 ≤ F x)
    {γ : ℝ} (hγ : 0 ≤ γ) (hγ1 : γ < 1) (step : Improves φ F γ) : excess φ F = 0 := by
  have he := excess_nonneg φ hF
  have hc := excess_le_mul φ hF hγ step
  nlinarith

theorem invariant_of_improves (φ : PolMul.Spectral ℂ) {F : Shape → ℝ} (hF : ∀ x, 0 ≤ F x)
    {γ : ℝ} (hγ : 0 ≤ γ) (hγ1 : γ < 1) (step : Improves φ F γ)
    (x : Shape) (T : DyadicTensor x) : value φ T ≤ (2 : ℝ) ^ F x := by
  simpa [excess_eq_zero φ hF hγ hγ1 step] using! value_le_excess φ hF x T

theorem target_invariant_of_improves (φ : PolMul.Spectral ℂ) (step : Improves φ target gamma)
    (x : Shape) (T : DyadicTensor x) : value φ T ≤ (2 : ℝ) ^ target x :=
  invariant_of_improves φ target_nonneg (by norm_num [gamma]) (by norm_num [gamma]) step x T

end OM.NNN12
