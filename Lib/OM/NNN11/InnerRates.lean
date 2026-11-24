import Lib.OM.NNN11.FiniteBound
import Lib.OM.NNN11.Rectangle

/-! Homogeneous rectangular rates, including zero logarithmic dimensions. -/
noncomputable section
open scoped BigOperators
namespace OM.NNN11
set_option maxHeartbeats 2000000

lemma central_rate_cap_scaled {t m H : ℝ}
    (ht : t ∈ Set.Icc (1 / 4 : ℝ) 1) (hm : 0 ≤ m) (hH : 0 ≤ H) (hcone : 5 * H ≤ m) :
    max 0 (rectRawRate 70 7 t (m * innerF t - H * innerG t)
      (centralSource t m H) (m - H)) ≤ 7 * (m - H) * Real.logb 2 7 := by
  by_cases hz : m = 0
  · have hH0 : H = 0 := by linarith
    simp [hz, hH0, rectRawRate, centralSource]
  have hm0 : 0 < m := lt_of_le_of_ne hm (Ne.symm hz)
  have hzmem : H / m ∈ Set.Icc (0 : ℝ) (1 / 5) :=
    ⟨div_nonneg hH hm, (div_le_iff₀ hm0).2 (by linarith)⟩
  have h := mul_le_mul_of_nonneg_left (central_rate_cap ht hzmem) hm
  rw [mul_max_of_nonneg _ _ hm, mul_zero] at h
  have he : m * (70 * (innerF t - H / m * innerG t - (9 / 4 - t) * (1 - H / m)) +
      7 * (1 - H / m) * codeK t) =
      rectRawRate 70 7 t (m * innerF t - H * innerG t) (centralSource t m H) (m - H) := by
    dsimp [rectRawRate, centralSource]
    field_simp <;> ring
  rw [he] at h
  convert! h using 1
  field_simp <;> ring

lemma short_rate_cap_scaled {t u m H q b : ℝ}
    (ht : t ∈ Set.Icc (1 / 4 : ℝ) 1) (hu : u ≤ 1)
    (hm : 0 ≤ m) (hH : 0 ≤ H) (hcone : 5 * H ≤ m)
    (hqb : (q = 70 ∧ b = 7) ∨ (q = 42 ∧ b = 6)) :
    max 0 (rectRawRate q b u (m * innerF t - H * innerG t)
      (shortSource t u m H) (m - H)) ≤ b * (m - H) * Real.logb 2 7 := by
  by_cases hz : m = 0
  · have hH0 : H = 0 := by linarith
    simp [hz, hH0, rectRawRate, shortSource]
  have hm0 : 0 < m := lt_of_le_of_ne hm (Ne.symm hz)
  have hzmem : H / m ∈ Set.Icc (0 : ℝ) (1 / 5) :=
    ⟨div_nonneg hH hm, (div_le_iff₀ hm0).2 (by linarith)⟩
  have h := mul_le_mul_of_nonneg_left (short_rate_cap ht hu hzmem hqb) hm
  rw [mul_max_of_nonneg _ _ hm, mul_zero] at h
  have he : m * (q * (innerF t - H / m * innerG t - 9 / 4 + u + t * (H / m)) +
      b * (1 - H / m) * codeK u) =
      rectRawRate q b u (m * innerF t - H * innerG t) (shortSource t u m H) (m - H) := by
    dsimp [rectRawRate, shortSource]
    field_simp <;> ring
  rw [he] at h
  convert! h using 1
  field_simp <;> ring

lemma rect_sources (m H : ℕ) (hHm : H ≤ m) (t : Fin 3 → ℝ)
    (hs : t 0 + t 1 + t 2 = (9 : ℝ) / 4) :
    sourceLog m (m - H) (m - H) t =
      ![centralSource (t 0) m H, shortSource (t 0) (t 1) m H, shortSource (t 0) (t 2) m H] := by
  have ht2 : t 2 = 9 / 4 - t 0 - t 1 := by linarith
  funext i
  fin_cases i <;>
    simp only [sourceLog, Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, centralSource, shortSource, Nat.cast_sub hHm, ht2] <;> ring

lemma rect_lengths (m H : ℕ) : lengths m (m - H) (m - H) =
    ![7 * (m - H), 7 * (m - H), 6 * (m - H)] := by
  simp [lengths, min_eq_left (Nat.sub_le m H), min_eq_right (Nat.sub_le m H)]

lemma rect_rates (m H : ℕ) (hHm : H ≤ m) (t : Fin 3 → ℝ) (a : ℝ)
    (hs : t 0 + t 1 + t 2 = (9 : ℝ) / 4) :
    rawRates m (m - H) (m - H) t a =
      ![max 0 (rectRawRate 70 7 (t 0) a (centralSource (t 0) m H) ((m : ℝ) - H)),
        max 0 (rectRawRate 70 7 (t 1) a (shortSource (t 0) (t 1) m H) ((m : ℝ) - H)),
        max 0 (rectRawRate 42 6 (t 2) a (shortSource (t 0) (t 2) m H) ((m : ℝ) - H))] := by
  funext i
  dsimp only [rawRates]
  rw [rect_lengths, rect_sources m H hHm t hs]
  fin_cases i <;>
    norm_num only [degrees, Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, rawAllowed, rectRawRate, Nat.cast_mul,
      Nat.cast_ofNat, Nat.cast_sub hHm] <;> rfl

lemma rect_rates_cap (m H : ℕ) (hcone : 5 * H ≤ m) (t : Fin 3 → ℝ)
    (ht : ∀ i, t i ∈ Set.Icc (1 / 4 : ℝ) 1) (hs : t 0 + t 1 + t 2 = (9 : ℝ) / 4) :
    ∀ i, rawRates m (m - H) (m - H) t (m * innerF (t 0) - H * innerG (t 0)) i ≤
      lengths m (m - H) (m - H) i * Real.logb 2 7 := by
  have hHm : H ≤ m := by omega
  have hconeR : 5 * (H : ℝ) ≤ m := by exact_mod_cast hcone
  rw [rect_rates m H hHm t _ hs, rect_lengths]
  intro i
  fin_cases i <;>
    norm_num only [Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sub hHm]
  · exact central_rate_cap_scaled (ht 0) (Nat.cast_nonneg _) (Nat.cast_nonneg _) hconeR
  · exact short_rate_cap_scaled (ht 0) (ht 1).2 (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      hconeR (Or.inl ⟨rfl, rfl⟩)
  · exact short_rate_cap_scaled (ht 0) (ht 2).2 (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      hconeR (Or.inr ⟨rfl, rfl⟩)

lemma rect_head_eq (m H : ℕ) (hHm : H ≤ m) (t : Fin 3 → ℝ) (a : ℝ)
    (hs : t 0 + t 1 + t 2 = (9 : ℝ) / 4) :
    (∑ i, t i * ((bondLog 21 21 28 m (m - H) (m - H) i : ℝ) - rawRates m (m - H) (m - H) t a i)) =
      rectHead (fun x => max 0 x) false (t 0) (t 1) (t 2) m H a := by
  rw [rect_rates m H hHm t a hs]
  simp only [Fin.sum_univ_three, bondLog, Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Nat.cast_add, Nat.cast_mul,
    Nat.cast_ofNat, Nat.cast_sub hHm, rectHead, Bool.false_eq_true, if_false]
  have he : (t 0 + t 1 + t 2) * ((m : ℝ) * 49 - (H : ℝ) * 21) =
      (9 / 4) * ((m : ℝ) * 49 - (H : ℝ) * 21) := congrArg (fun s : ℝ => s * ((m : ℝ) * 49 - (H : ℝ) * 21)) hs
  dsimp [shortSource]
  nlinarith only [he]

end OM.NNN11
