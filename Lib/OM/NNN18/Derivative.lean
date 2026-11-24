import Lib.OM.NNN18.PackedLemmas

/-!
For the packed source matrix at focus 0 with parents `S, C₁+e, C₂+e`, label exponents
`1, β₁+e, β₂+e`, target `C₀+qe` and moment values `L(e)`, every entry satisfies

  gE(e) - gE(0) = e [q sym(D*,1) - Σ_{i=1,2} θ_i sym(b, A_i)/(β_i(β_i+e))] + (moment terms),
-/

noncomputable section
open Set
namespace OM.NNN18

/-- The entrywise identity (6.1). -/
lemma gE_diff (θ L L' C0 C1 C2 S : Fin 3 → ℝ) (β₁ β₂ q e : ℝ) (j k : Fin 3)
    (h1 : β₁ ≠ 0) (h2 : β₂ ≠ 0) (h1e : β₁ + e ≠ 0) (h2e : β₂ + e ≠ 0) :
    gE θ ![1, β₁ + e, β₂ + e] ![S, fun i => C1 i + e, fun i => C2 i + e] L'
        (fun i => C0 i + q * e) j k
      - gE θ ![1, β₁, β₂] ![S, fun i => C1 i + 0, fun i => C2 i + 0] L (fun i => C0 i + q * 0) j k
      = e * (q * symE (fun i => ![6, 5, 5] i + θ 0 * ![0, 5, 5] i) (fun _ => 1) j k
          - θ 1 * symE ![6, 5, 5] (fun i => C0 i - C1 i + (1 - q) * β₁) j k / (β₁ * (β₁ + e))
          - θ 2 * symE ![6, 5, 5] (fun i => C0 i - C2 i + (1 - q) * β₂) j k / (β₂ * (β₂ + e)))
        + (pairE θ L' j k - pairE θ L j k) := by
  fin_cases j <;> fin_cases k <;>
  · simp [gE, symE]
    field_simp
    ring

/-- Moment terms do not decrease the matrix when the moments do not increase. -/
lemma pairE_mono {θ L L' : Fin 3 → ℝ} (hθ : ∀ i, 0 ≤ θ i) (hL : ∀ i, L' i ≤ L i) (j k : Fin 3) :
    0 ≤ pairE θ L' j k - pairE θ L j k := by
  have h0 := mul_le_mul_of_nonneg_left (hL 0) (hθ 0)
  have h1 := mul_le_mul_of_nonneg_left (hL 1) (hθ 1)
  have h2 := mul_le_mul_of_nonneg_left (hL 2) (hθ 2)
  fin_cases j <;> fin_cases k <;> simp [pairE] <;> nlinarith

/-- `sym(b, A) ≤ 6·.16` entrywise when every component of `A` is below `.16`. -/
lemma symE_le {A : Fin 3 → ℝ} (hA : ∀ i, A i ≤ 16 / 100) (j k : Fin 3) :
    symE ![6, 5, 5] A j k ≤ 6 * (16 / 100) := by
  have hb : ∀ i, (0 : ℝ) ≤ (![6, 5, 5] : Fin 3 → ℝ) i ∧ (![6, 5, 5] : Fin 3 → ℝ) i ≤ 6 := by
    intro i; fin_cases i <;> norm_num
  unfold symE
  have t1 : (![6, 5, 5] : Fin 3 → ℝ) j * A k ≤ 6 * (16 / 100) := by
    rcases le_total (A k) 0 with h | h
    · have := mul_nonpos_of_nonneg_of_nonpos (hb j).1 h; linarith
    · have := mul_le_mul_of_nonneg_right (hb j).2 h; linarith [hA k]
  have t2 : (![6, 5, 5] : Fin 3 → ℝ) k * A j ≤ 6 * (16 / 100) := by
    rcases le_total (A j) 0 with h | h
    · have := mul_nonpos_of_nonneg_of_nonpos (hb k).1 h; linarith
    · have := mul_le_mul_of_nonneg_right (hb k).2 h; linarith [hA j]
  linarith

/-- `sym(D*, 1) ≥ 6` entrywise when `θ₀ ≥ 1/5`. -/
lemma symE_Dstar_ge {θ0 : ℝ} (hθ0 : 1 / 5 ≤ θ0) (j k : Fin 3) :
    6 ≤ symE (fun i => ![6, 5, 5] i + θ0 * ![0, 5, 5] i) (fun _ => 1) j k := by
  fin_cases j <;> fin_cases k <;> simp [symE] <;> linarith

theorem gE_mono_packed (θ L L' C0 C1 C2 S : Fin 3 → ℝ) (β₁ β₂ e : ℝ) (he : 0 ≤ e)
    (hθ : ∀ i, 0 ≤ θ i) (hθ0 : 1 / 5 ≤ θ 0) (hθ1 : θ 1 ≤ 86 / 100) (hθ2 : θ 2 ≤ 86 / 100)
    (hβ₁ : 64 / 100 ≤ β₁) (hβ₂ : 64 / 100 ≤ β₂)
    (hA₁ : ∀ i, C0 i - C1 i + (1 - 19 / 20) * β₁ ≤ 16 / 100)
    (hA₂ : ∀ i, C0 i - C2 i + (1 - 19 / 20) * β₂ ≤ 16 / 100)
    (hL : ∀ i, L' i ≤ L i) (j k : Fin 3) :
    gE θ ![1, β₁, β₂] ![S, fun i => C1 i + 0, fun i => C2 i + 0] L (fun i => C0 i + 19 / 20 * 0) j k ≤
      gE θ ![1, β₁ + e, β₂ + e] ![S, fun i => C1 i + e, fun i => C2 i + e] L'
        (fun i => C0 i + 19 / 20 * e) j k := by
  have hb1 : (0 : ℝ) < β₁ := by linarith
  have hb2 : (0 : ℝ) < β₂ := by linarith
  have hdiff := gE_diff θ L L' C0 C1 C2 S β₁ β₂ (19 / 20) e j k hb1.ne' hb2.ne'
    (by linarith : β₁ + e ≠ 0).symm.symm (by linarith : β₂ + e ≠ 0).symm.symm
  have hm := pairE_mono hθ hL j k
  have hD := symE_Dstar_ge hθ0 j k
  have hs1 := symE_le hA₁ j k
  have hs2 := symE_le hA₂ j k
  -- each correction term is at most .86·(6·.16)/.64²
  have hden1 : (64 / 100 : ℝ) ^ 2 ≤ β₁ * (β₁ + e) := by nlinarith
  have hden2 : (64 / 100 : ℝ) ^ 2 ≤ β₂ * (β₂ + e) := by nlinarith
  have bound : ∀ (θi s β : ℝ), 0 ≤ θi → θi ≤ 86 / 100 → s ≤ 6 * (16 / 100) →
      (64 / 100 : ℝ) ^ 2 ≤ β → θi * s / β ≤ 86 / 100 * (6 * (16 / 100)) / (64 / 100) ^ 2 := by
    intro θi s β h0 h1 hs hβ
    have hβpos : 0 < β := lt_of_lt_of_le (by norm_num) hβ
    rcases le_total s 0 with hs0 | hs0
    · have : θi * s / β ≤ 0 := div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos h0 hs0) hβpos.le
      have : (0 : ℝ) ≤ 86 / 100 * (6 * (16 / 100)) / (64 / 100) ^ 2 := by norm_num
      linarith
    · rw [div_le_div_iff₀ hβpos (by norm_num)]
      have := mul_le_mul h1 hs hs0 (by norm_num : (0 : ℝ) ≤ 86 / 100)
      have := mul_le_mul this hβ (by norm_num) (by positivity)
      nlinarith
  have c1 := bound (θ 1) _ _ (hθ 1) hθ1 hs1 hden1
  have c2 := bound (θ 2) _ _ (hθ 2) hθ2 hs2 hden2
  have key : 0 ≤ 19 / 20 * symE (fun i => ![6, 5, 5] i + θ 0 * ![0, 5, 5] i) (fun _ => 1) j k
      - θ 1 * symE ![6, 5, 5] (fun i => C0 i - C1 i + (1 - 19 / 20) * β₁) j k / (β₁ * (β₁ + e))
      - θ 2 * symE ![6, 5, 5] (fun i => C0 i - C2 i + (1 - 19 / 20) * β₂) j k / (β₂ * (β₂ + e)) := by
    -- 19/20·6 - 2·(.86·.96/.64²) = 267/160 > 0
    have : (0 : ℝ) < 19 / 20 * 6 - 2 * (86 / 100 * (6 * (16 / 100)) / (64 / 100) ^ 2) := by norm_num
    nlinarith
  have := mul_nonneg he key
  linarith

end OM.NNN18
