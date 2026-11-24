import Lib.OM.NNN12.Excess

/-! Remove uniform finite constants on every rectangular format before
taking the excess supremum. Only powers of the same tensor are used. -/
noncomputable section
namespace OM.NNN12
open CoordinateTensor OM.NNN.Raw NNN11.Network

def powerShape (q : ℕ) (x : Shape) : Shape := fun i => q * x i

lemma volume_power (q : ℕ) (x : Shape) : volume (powerShape q x) = q * volume x := by
  simp only [volume, powerShape, Nat.cast_mul]
  ring

lemma target_power (q : ℕ) (x : Shape) : target (powerShape q x) = q * target x := by
  simp only [target, powerShape, Nat.cast_mul]
  exact fallbackPotential_homogeneous (Nat.cast_nonneg q) _ _ _

/-- The dyadic encoding of a tensor power preserves physical party order. -/
def dyadicPower {x : Shape} (T : DyadicTensor x) (q : ℕ) : DyadicTensor (powerShape q x) :=
  fun a b c => ordered (D := Fin q) T
    (NNN11.wordPowerEquiv q (x 0) a) (NNN11.wordPowerEquiv q (x 1) b)
    (NNN11.wordPowerEquiv q (x 2) c)

lemma value_dyadicPower (φ : PolMul.Spectral ℂ) {x : Shape} (T : DyadicTensor x) (q : ℕ) :
    value φ (dyadicPower T q) = value φ T ^ q := by
  exact (value_reindex φ (ordered (D := Fin q) T)
    (NNN11.wordPowerEquiv q (x 0)) (NNN11.wordPowerEquiv q (x 1))
    (NNN11.wordPowerEquiv q (x 2))).trans (value_ordered_fin φ T q)

theorem remove_uniform_constant (φ : PolMul.Spectral ℂ) {F : Shape → ℝ}
    (hF : ∀ q x, F (powerShape q x) = q * F x) (C : ℝ)
    (hb : ∀ (x : Shape) (T : DyadicTensor x), value φ T ≤ C * (2 : ℝ) ^ F x)
    (x : Shape) (T : DyadicTensor x) : value φ T ≤ (2 : ℝ) ^ F x := by
  have hp (q : ℕ) : value φ T ^ q ≤ C * ((2 : ℝ) ^ F x) ^ q := by
    have hh := hb (powerShape q x) (dyadicPower T q)
    rw [value_dyadicPower, hF] at hh
    convert! hh using 1
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 2
    ring
  by_contra! hn
  have hv : 0 < (2 : ℝ) ^ F x := by positivity
  have hratio : 1 < value φ T / (2 : ℝ) ^ F x := (one_lt_div hv).2 hn
  obtain ⟨q, hq⟩ := pow_unbounded_of_one_lt C hratio
  have hle : (value φ T / (2 : ℝ) ^ F x) ^ q ≤ C := by
    rw [div_pow]
    exact (div_le_iff₀ (pow_pos hv q)).2 (hp q)
  exact (not_lt_of_ge hle) hq

/-- A network may supply a constant depending on the fixed point and error,
but not on the shape or tensor. This suffices for the supremum contraction. -/
theorem improves_of_finite (φ : PolMul.Spectral ℂ) {γ : ℝ}
    (step : ∀ ε : ℝ, 0 ≤ ε →
      (∀ (x : Shape) (T : DyadicTensor x), value φ T ≤ (2 : ℝ) ^ (target x + ε * volume x)) →
      ∃ C : ℝ, ∀ (x : Shape) (T : DyadicTensor x),
        value φ T ≤ C * (2 : ℝ) ^ (target x + γ * ε * volume x)) :
    Improves φ target γ := by
  intro ε hε hb
  obtain ⟨C, hC⟩ := step ε hε hb
  apply remove_uniform_constant φ (C := C) (hb := hC)
  intro q x
  rw [target_power, volume_power]
  ring

theorem target_invariant_of_finite (φ : PolMul.Spectral ℂ)
    (step : ∀ ε : ℝ, 0 ≤ ε →
      (∀ (x : Shape) (T : DyadicTensor x), value φ T ≤ (2 : ℝ) ^ (target x + ε * volume x)) →
      ∃ C : ℝ, ∀ (x : Shape) (T : DyadicTensor x),
        value φ T ≤ C * (2 : ℝ) ^ (target x + gamma * ε * volume x))
    (x : Shape) (T : DyadicTensor x) : value φ T ≤ (2 : ℝ) ^ target x :=
  target_invariant_of_improves φ (improves_of_finite φ step) x T

end OM.NNN12
