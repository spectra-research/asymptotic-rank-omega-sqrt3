import PLATFORM.Statements.«NNN.36»
import Lib.OM.NNN30.Main
import Lib.OM.NNN32.Implication
import Lib.OM.NNN32.Conclusion
import Lib.OM.NNN34.Conclusion
import Lib.OM.NNN36.Wide
import Lib.OM.NNN36.TriangleBound
import Lib.OM.NNN36.Plateau
import Lib.OM.NNN36.Isosceles
import Lib.OM.NNN36.SplitBound
import Lib.OM.Formats.Example

/-! # Asymptotic rank via matrix multiplication and sums of squares -/

namespace AsymptoticRank

/-- Theorem 1.2. Every complex tensor of cube side `n` has asymptotic rank at most
`n ^ (ω / √3)`. -/
theorem asympRank_le_pow_omega_div_sqrt3 : S_NNN_36 :=
  OM.NNN30.asympRank_le_omega_div_sqrt_three

/-- Theorem 1.3(i). When the largest dimension is at least the product of the other
two, that product is the maximal asymptotic rank. -/
theorem formatRank_eq_product_of_wide : S_R115_3 := OM.NNN36.proof_R115_3

/-- Theorem 1.3(ii), attained form. The minimum rectangular exponent over the closed triangle of
logarithmic side lengths bounds the logarithm of the maximal asymptotic rank. -/
theorem log_formatRank_le_triangle_min : S_R115_4 := OM.NNN36.proof_R115_4

/-- Theorem 1.3(ii), as stated in the paper: the logarithm of the maximal asymptotic rank is at most
the rectangular exponent at the distances from every point `z` of the plane to the three vertices,
hence at most their infimum over the plane. -/
theorem log_formatRank_le_omegaRect_everywhere :
    ∀ (n₁ n₂ n₃ : ℕ+), n₁ ≤ n₂ → n₂ ≤ n₃ →
      let a := Real.logb 2 (n₁ : ℕ)
      let b := Real.logb 2 (n₂ : ℕ)
      let c := Real.logb 2 (n₃ : ℕ)
      let q₃ := (c : ℂ) * P2M.R115.normalizedApex a b c
      c < a + b → ∀ z : ℂ,
        Real.logb 2 (P2M.R115.formatRankSup n₁ n₂ n₃) ≤
          OmegaBound.omegaRect3 ℂ (dist z 0) (dist z (c : ℂ)) (dist z q₃) := by
  intro n₁ n₂ n₃ h₁₂ h₂₃ _ _ _ _ ht z
  exact OM.NNN36.rank_at_point n₁ n₂ n₃ h₁₂ h₂₃ ht z

/-- Theorem 1.3(iii) in coordinates. The normalized apex determines a unique cubic root in (0,1).
Under the stated distance inequality the maximal asymptotic rank is the largest dimension. -/
theorem formatRank_eq_largest_of_apex_bound : S_R115_5 := OM.NNN36.proof_R115_5

/-- Theorem 1.3(iii), as stated in the paper. If the largest logarithm `c` splits as `p + q` with
`c (p a² + q b²) ≤ p q (p q + c²)`, then the maximal asymptotic rank is the largest dimension. -/
theorem formatRank_eq_largest_of_split_bound :
  ∀ (n₁ n₂ n₃ : ℕ+), n₁ ≤ n₂ → n₂ ≤ n₃ →
    let a := Real.logb 2 (n₁ : ℕ)
    let b := Real.logb 2 (n₂ : ℕ)
    let c := Real.logb 2 (n₃ : ℕ)
    c < a + b → (∃ p q : ℝ, 0 ≤ p ∧ 0 ≤ q ∧ p + q = c ∧
      c * (p * a ^ 2 + q * b ^ 2) ≤ p * q * (p * q + c ^ 2)) →
    P2M.R115.formatRankSup n₁ n₂ n₃ = ((n₃ : ℕ) : ℝ) := by
  have h5 : S_R115_5 := formatRank_eq_largest_of_apex_bound
  intro n₁ n₂ n₃ h₁₂ h₂₃ a b c hc hpq
  obtain ⟨p, q, hp, hq, hsum, h⟩ := hpq
  obtain ⟨hunique, hrank⟩ := h5 n₁ n₂ n₃ h₁₂ h₂₃ hc
  obtain ⟨x, hx, _⟩ := hunique
  have h0 : 0 ≤ a := Real.logb_nonneg (by norm_num) (by exact_mod_cast n₁.pos)
  have hab : a ≤ b := Real.logb_le_logb_of_le (by norm_num)
    (by exact_mod_cast n₁.pos) (by exact_mod_cast (show (n₁ : ℕ) ≤ (n₂ : ℕ) from h₁₂))
  have hbc : b ≤ c := Real.logb_le_logb_of_le (by norm_num)
    (by exact_mod_cast n₂.pos) (by exact_mod_cast (show (n₂ : ℕ) ≤ (n₃ : ℕ) from h₂₃))
  exact hrank x hx (P2M.R115.apex_bound_of_pq a b c h0 hab hbc hc p q hp hq hsum h x hx.1 hx.2)

/-- Theorem 1.3(iv). The maximal asymptotic rank of format `(n,n,m)` equals `m`
for `n ^ (4 / √5) ≤ m ≤ n ^ 2`. -/
theorem formatRank_eq_largest_of_isosceles : S_R115_6 := OM.NNN36.proof_R115_6

/-- Theorem 1.4. The sums-of-squares exponent is one or √2. The statement
also identifies it as the common limit for the crossing cost and restricted partition rank. -/
theorem sumsOfSquares_exponent_dichotomy : S_R113_22 := OM.NNN32.proof_R113_22

/-- The exponent `β` of the paper, the limsup of `log_n` of the maximal asymptotic rank in format
`(n,n,n)`, equals the supremum over integer sides that Theorem 1.5 is stated for. -/
theorem formatBeta_cube_eq_beta : P2M.R116.formatBeta 1 1 1 = P2M.R114.beta :=
  OM.Formats.cube_exponent

/-- Theorem 1.5. The cube exponent equals ω/2 exactly when the sums-of-squares
exponent is one. In the other case the cube exponent lies in [2/√3, ω/√3]. -/
theorem cube_exponent_dichotomy : S_NNN_34 := OM.NNN34.proof_NNN_34

/-- Theorem 1.6(i). If γ = 1, the format exponent of a strict triangle with
semiperimeter s equals the rectangular exponent at (s − a, s − b, s − c). -/
theorem formatExponent_eq_rectangular_of_gamma_eq_one : S_NNN_47 := OM.Formats.proof_NNN_47

/-- Theorem 1.6(i). If γ = 1, every tensor with dimensions
(b₁₂b₁₃, b₁₂b₂₃, b₁₃b₂₃) is an asymptotic restriction of ⟨b₁₃,b₁₂,b₂₃⟩. -/
theorem asympRestricts_matMul_of_gamma_eq_one : S_R116_3 := OM.Formats.proof_R116_3

/-- Theorem 1.6(ii). If γ = √2, twice the radius of the smallest disc containing
the triangle of logarithmic side lengths is a lower bound for the format exponent. -/
theorem two_mul_discRadius_le_formatExponent : S_NNN_48 := OM.Formats.proof_NNN_48

/-- Theorem 1.6(ii), equality at ω = 2. If γ = √2 and ω = 2, the format exponent
equals twice the radius of the smallest disc containing the triangle. -/
theorem formatExponent_eq_two_mul_discRadius_of_omega_eq_two : S_NNN_49 := OM.Formats.proof_NNN_49

/-- Corollary 1.7(i)–(ii). The sums-of-squares exponent is one exactly when
the format exponent β(3,3,4) is four. -/
theorem gamma_eq_one_iff_formatExponent_334_eq_four : S_NNN_50 := OM.Formats.proof_NNN_50

/-- Corollary 1.7(ii)–(iii). The format exponent β(3,3,4) is four exactly when
the maximal asymptotic rank in format (t³,t³,t⁴) equals t⁴ for every positive integer t. -/
theorem formatExponent_334_eq_four_iff_formatRank_eq_fourth_power :
    P2M.R116.formatBeta 3 3 4 = 4 ↔
      ∀ t : ℕ+, P2M.R115.formatRankSup (t^3) (t^3) (t^4) = (t : ℝ)^4 :=
  OM.Formats.exponent_334_iff_formatRank

/-- Corollary 1.7. If γ = √2, then β(3,3,4) is at least 9/√5. -/
theorem nine_div_sqrt_five_le_formatExponent_334 : S_NNN_51 := OM.Formats.proof_NNN_51

/-- Theorem 1.2 with the nine-quarters bound for ω. -/
theorem asympRank_le_pow_three_sqrt3_div_four : S_NNN_30 := OM.NNN30.proof_NNN_30

/-- Theorem 1.2 at ω = 2. -/
theorem asympRank_le_pow_two_div_sqrt3_of_omega_eq_two : S_NNN_31 := OM.NNN30.proof_NNN_31

/-- Theorem 1.5(i) under a finite witness for γ = 1, using ω ≤ 9/4. -/
theorem asympRank_le_pow_nine_eighths_of_witness : S_NNN_32 := OM.NNN32.proof_NNN_32

/-- Theorem 1.5(i) under a finite witness for γ = 1, at ω = 2. -/
theorem asympRank_le_side_of_witness_of_omega_eq_two : S_NNN_33 := OM.NNN32.proof_NNN_33

/-- Theorem 1.5 at ω = 2. The asymptotic rank conjecture over ℂ holds exactly when
the sums-of-squares exponent is one. -/
theorem asympRank_conjecture_iff_gamma_eq_one_of_omega_eq_two : S_NNN_35 := OM.NNN34.proof_NNN_35

end AsymptoticRank
