import Lib.OM.NNN8.BinaryAction

/-! Exact rectangular correction prices and the code-projector inequality. -/
noncomputable section
open scoped BigOperators Classical
namespace OM.NNN8
open CoordinateTensor OM.NNN.Raw OM.NNN2 Foundations.PairUnitExponents
set_option maxHeartbeats 1000000

/-- Empty compressed sources cost zero; this upper bound also covers exponent zero. -/
lemma value_squareSource_card_le {Y R : Type} [Fintype Y] [Fintype R] [Nonempty Y]
    (φ : PolMul.Spectral ℂ) :
    value φ (squareSource Y R) ≤
      (Fintype.card Y : ℝ) ^ (theta φ 0 + theta φ 1) *
        (Fintype.card R : ℝ) ^ theta φ 2 := by
  rcases isEmpty_or_nonempty R with hR | hR
  · letI := hR
    have hz : squareSource Y R = 0 := by
      funext a b c
      exact isEmptyElim a.2
    rw [hz, value_zero]
    positivity
  · letI := hR
    rw [OM.NNN7.value_squareSource_card, Real.rpow_add (by positivity)]
    exact le_of_eq (by ring)

abbrev BinaryWord (l : ℕ) := Fin l → ZMod 2

lemma binary_word_card (l : ℕ) : Fintype.card (BinaryWord l) = 2 ^ l := by
  simp [BinaryWord]

lemma selected_card (l : ℕ) (s : Finset (Fin l)) :
    Fintype.card (Selected (fun _ : Fin l => ZMod 2) s) = 2 ^ s.card := by
  simp [Selected]

lemma remaining_card (l : ℕ) (s : Finset (Fin l)) :
    Fintype.card (Remaining (fun _ : Fin l => ZMod 2) s) = 2 ^ (l - s.card) := by
  simp [Remaining, Fintype.card_subtype_compl]

lemma residual_card (l : ℕ) (s : Finset (Fin l)) :
    (Fintype.card (BinaryWord l × Remaining (fun _ : Fin l => ZMod 2) s) : ℝ) =
      ((2 : ℝ) ^ l) ^ (2 : ℕ) / (2 : ℝ) ^ s.card := by
  have hs : s.card ≤ l := (Finset.card_le_univ s).trans_eq (Fintype.card_fin l)
  simp only [Fintype.card_prod, binary_word_card, remaining_card, Nat.cast_mul, Nat.cast_pow,
    Nat.cast_ofNat]
  apply (eq_div_iff (by positivity : (2 : ℝ) ^ s.card ≠ 0)).2
  rw [mul_assoc, ← pow_add, Nat.sub_add_cancel hs, pow_two]

/-- Equation (9), before consolidating the two equal long edges. -/
theorem correction_price (φ : PolMul.Spectral ℂ) (l : ℕ) (s : Finset (Fin l)) :
    value φ (squareSource (BinaryWord l × Remaining (fun _ : Fin l => ZMod 2) s)
      (Selected (fun _ : Fin l => ZMod 2) s)) =
      (((2 : ℝ) ^ l) ^ (2 : ℕ) / (2 : ℝ) ^ s.card) ^ (theta φ 0 + theta φ 1) *
        ((2 : ℝ) ^ s.card) ^ theta φ 2 := by
  rw [OM.NNN7.value_squareSource_card, residual_card, selected_card]
  push_cast
  rw [Real.rpow_add (by positivity)]
  ring

/-- Equation (10) for a finite additive family of binary masks. The code may
have a kernel: every nonzero message is charged, including zero-image messages. -/
theorem code_price {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (φ : PolMul.Spectral ℂ) (l : ℕ) (T : Cube ℂ (BinaryWord l))
    (code : G →+ BinaryWord l) :
    value φ T ^ 2 ≤
      ((2 : ℝ) ^ l) ^ (theta φ 0 + theta φ 1) *
        (((2 : ℝ) ^ l) ^ (2 : ℕ) / Fintype.card G) ^ theta φ 2 +
      ∑ c ∈ Finset.univ.erase (0 : G),
        (((2 : ℝ) ^ l) ^ (2 : ℕ) / (2 : ℝ) ^ (binaryMask (code c)).card) ^
            (theta φ 0 + theta φ 1) *
          ((2 : ℝ) ^ (binaryMask (code c)).card) ^ theta φ 2 := by
  obtain ⟨χ, r, U, V, hr, hUV⟩ := exists_swap_factorization (X := fun _ : Fin l => ZMod 2) code
  have h := compressed_value φ T (Finset.univ.erase (0 : G))
    (fun c => binaryMask (code c)) χ U V hUV
  let n : ℕ+ := ⟨2 ^ l, by positivity⟩
  rw [value_cubeSquare φ (n := n) (Fintype.equivOfCardEq (by simp [n, binary_word_card]))] at h
  have hmain := value_squareSource_card_le (Y := BinaryWord l) (R := Fin r) φ
  simp only [binary_word_card, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat] at hmain
  have hrR : (r : ℝ) ≤ ((2 : ℝ) ^ l) ^ (2 : ℕ) / Fintype.card G := by
    apply (le_div_iff₀ (Nat.cast_pos.mpr Fintype.card_pos)).2
    exact_mod_cast (by simpa [binary_word_card] using! hr)
  have hmain' := hmain.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (Nat.cast_nonneg r) hrR (theta_mem_Icc φ 2).1) (by positivity))
  simp only [correction_price] at h
  exact h.trans (add_le_add hmain' le_rfl)

end OM.NNN8
