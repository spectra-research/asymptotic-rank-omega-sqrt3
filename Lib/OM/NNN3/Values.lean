import Lib.OM.NNN3.Restriction

noncomputable section
open scoped BigOperators Classical
namespace OM.NNN3
open CoordinateTensor OM.NNN.Raw OM.NNN2 Semicontinuity Foundations.HyperbolicLift Foundations.PairUnitExponents
set_option maxHeartbeats 1000000
variable {I J K I' J' K' X : Type}

lemma value_product' [Fintype I] [Fintype J] [Fintype K]
    [Fintype I'] [Fintype J'] [Fintype K']
    [Nonempty I] [Nonempty J] [Nonempty K] [Nonempty I'] [Nonempty J'] [Nonempty K']
    (φ : PolMul.Spectral ℂ) (S : Tensor ℂ I J K) (T : Tensor ℂ I' J' K') :
    value φ (tensorProduct S T) = value φ S * value φ T := by
  let d : Fin 3 → ℕ+ := ![⟨Fintype.card I, Fintype.card_pos⟩,
    ⟨Fintype.card J, Fintype.card_pos⟩, ⟨Fintype.card K, Fintype.card_pos⟩]
  let d' : Fin 3 → ℕ+ := ![⟨Fintype.card I', Fintype.card_pos⟩,
    ⟨Fintype.card J', Fintype.card_pos⟩, ⟨Fintype.card K', Fintype.card_pos⟩]
  exact value_product (d := d) (d' := d') (Fintype.equivFin I).symm
    (Fintype.equivFin J).symm (Fintype.equivFin K).symm (Fintype.equivFin I').symm
    (Fintype.equivFin J').symm (Fintype.equivFin K').symm φ S T

lemma value_cube [Fintype X] [Nonempty X] (φ : PolMul.Spectral ℂ) (T : Cube ℂ X) :
    value φ (cube T) = value φ T ^ 3 := by
  have he : cube T = tensorProduct T (tensorProduct T T) := by
    funext x y z
    simp [cube, tensorProduct, mul_assoc]
  rw [he, value_product', value_product']
  ring

lemma value_diag_le [Fintype X] [DecidableEq X] (φ : PolMul.Spectral ℂ) :
    value φ (diagonal ℂ X) ≤ Fintype.card X := by
  have h : CoordinateTensor.Restricts (diagonal ℂ X) (pad (diagonal ℂ X)) := by
    refine ⟨(fun a i => if a = Sum.inl i then 1 else 0),
      (fun b j => if b = Sum.inr (Sum.inl j) then 1 else 0),
      (fun c k => if c = Sum.inr (Sum.inr k) then 1 else 0), ?_⟩
    funext a b c
    rcases a with a | (a | a) <;> rcases b with b | (b | b) <;>
      rcases c with c | (c | c) <;>
      simp [mapTensor, pad, diagonal, ite_mul, mul_ite, ite_and, Finset.sum_ite_irrel]
    split_ifs <;> simp_all
  have h' := eval_cubeClass_mono φ (restricts_degenerates _ _ h)
  simpa only [value, cubeClass_diagonal, AsymptoticSpectrumDuality.AsymptoticSpectrum.eval_natCast] using! h'

lemma value_mm_price [Fintype X] [Nonempty X] (φ : PolMul.Spectral ℂ) :
    value φ (mm X X X) ≤ (Fintype.card X : ℝ) ^ ((9 : ℝ) / 4) := by
  let n : ℕ+ := ⟨Fintype.card X, Fintype.card_pos⟩
  have hn : (0 : ℝ) < (n : ℝ) := by positivity
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast n.pos
  rw [value_mm φ (n := n) (p := n) (m := n) (Fintype.equivFin X).symm
    (Fintype.equivFin X).symm (Fintype.equivFin X).symm,
    ← Real.rpow_add hn, ← Real.rpow_add hn]
  apply Real.rpow_le_rpow_of_exponent_le hn1
  have h := Omega.theta_sum_le_nine_quarters φ
  linarith

lemma cube_restricts [Fintype X] (T : Cube ℂ X) :
    CoordinateTensor.Restricts (mm (X × X) (X × X) (X × X)) (cube T) := by
  refine ⟨(fun x a => if x.2.1 = a.2.2 ∧ x.2.2 = a.1.1 then T x.1 a.2.1 a.1.2 else 0),
    (fun y b => if y.1 = b.2.1 ∧ y.2.2 = b.1.2 then T b.2.2 y.2.1 b.1.1 else 0),
    (fun z c => if z.1 = c.1.2 ∧ z.2.1 = c.2.1 then T c.1.1 c.2.2 z.2.2 else 0), ?_⟩
  funext x y z
  simp [map_mm, Fintype.sum_prod_type, cube, ite_mul, mul_ite, ite_and, Finset.sum_ite_irrel]

/-- Pricing the complete ordinary restriction at any spectral point. -/
theorem cubic_inequality [Fintype X] [Nonempty X] (φ : PolMul.Spectral ℂ) (T : Cube ℂ X) :
    value φ T ^ 3 ≤ (Fintype.card (Sym2 X) : ℝ) ^ ((9 : ℝ) / 4) +
      3 * (Fintype.card X : ℝ) ^ ((9 : ℝ) / 4) * value φ T +
      4 * (Fintype.card X : ℝ) ^ ((17 : ℝ) / 4) := by
  have h := value_mono φ (restricts_degenerates _ _ (symmetric_restriction T))
  rw [value_cube, value_add] at h
  simp only [correctionSource, value_add, value_product'] at h
  letI : Nonempty (Sym2 X) := ⟨s(Classical.choice ‹Nonempty X›, Classical.choice ‹Nonempty X›)⟩
  have hM := value_mm_price (X := X) φ
  have hR := value_mm_price (X := Sym2 X) φ
  have hD := value_diag_le (X := X × X) φ
  have hn : (0 : ℝ) < Fintype.card X := by exact_mod_cast Fintype.card_pos
  have hT : 0 ≤ value φ T := φ.nonneg _
  have hM0 : 0 ≤ value φ (mm X X X) := φ.nonneg _
  have hD0 : 0 ≤ value φ (diagonal ℂ (X × X)) := φ.nonneg _
  have hMT := mul_le_mul_of_nonneg_right hM hT
  have hMD := mul_le_mul hM hD hD0 (Real.rpow_nonneg hn.le _)
  simp only [Fintype.card_prod, Nat.cast_mul] at hMD
  have he : (Fintype.card X : ℝ) ^ ((9 : ℝ) / 4) *
      ((Fintype.card X : ℝ) * Fintype.card X) = (Fintype.card X : ℝ) ^ ((17 : ℝ) / 4) := by
    rw [← pow_two, ← Real.rpow_natCast, ← Real.rpow_add hn]
    norm_num
  rw [he] at hMD
  linarith

end OM.NNN3
