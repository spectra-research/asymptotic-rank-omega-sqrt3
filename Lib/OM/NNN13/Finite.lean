import Lib.OM.NNN13.Averaged
import Lib.OM.NNN12.BranchMoments
import Lib.OM.NNN12.Scalar

/-! Integral code dimensions and a uniform finite tensor bound. Analytic
moment, capacity and head certificates are explicit premises. These apply
to arbitrary all-position layouts and all three recursive residual groups. -/
noncomputable section
open scoped BigOperators Classical
namespace OM.NNN13
open CoordinateTensor OM.NNN.Raw NNN11.Network
open NNN11 (bondLog)
open NNN11.ExtractionAB (X)
open Foundations.PairUnitExponents
set_option maxHeartbeats 2000000

def groupDegrees (a b c : ℕ) : Fin 3 → ℕ := ![b + c, a + b + c, a + b + c]
def groupIntercepts (a b c : ℕ) (C : Fin 3 → Fin 3 → ℝ) (x : Fin 3 → ℝ) (i : Fin 3) : ℝ :=
  groupDegrees a b c i * plane (C i) x
def groupSlopes (d : Fin 3 → ℕ) (t : Fin 3 → ℝ) (C : Fin 3 → Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![d 0 * (t 0 - C 0 1 - C 0 2), d 1 * (t 1 - C 1 0 - C 1 2),
    d 2 * (t 2 - C 2 0 - C 2 1)]
def groupRates (a b c : ℕ) (M : Fin 3 → ℝ) (P : ℝ) (i : Fin 3) : ℝ :=
  max 0 (groupDegrees a b c i * P - M i)

lemma alphabet_floor_constant (q : Fin 3 → ℕ) (hq : ∀ i, q i ≤ 19) {a : ℕ} (ha : 13 ≤ a) :
    (∏ i, (q i : ℝ)) + 2 ≤ (2 : ℝ) ^ a := by
  have hp : (∏ i, (q i : ℝ)) ≤ ∏ _i : Fin 3, (19 : ℝ) := by
    apply Finset.prod_le_prod₀
    · intro i _; exact Nat.cast_nonneg _
    · intro i _; exact_mod_cast hq i
  have ha' := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) ha
  norm_num at hp ha'
  linarith

variable {A B C : Type} [Fintype A] [Fintype B] [Fintype C]
  [DecidableEq A] [DecidableEq B] [DecidableEq C]
  {x y z : ℕ} {N q d : Fin 3 → ℕ} [∀ i, Fact (q i).Prime]

theorem combined_network_rounded_with_loss (φ : PolMul.Spectral ℂ)
    (c : Fin 3 → Fin 3 → ℝ) (hb : ∀ i, AffineBound φ (c i))
    (t : Fin 3 → ℝ) (ht : ∀ i, t i ∈ Set.Icc (0 : ℝ) 1) (hθ : ∀ i, theta φ i ≤ t i)
    (Lab : NNN12.BondLayout (q 2) (d 2) A B x y (N 2))
    (Lbc : NNN12.BondLayout (q 0) (d 0) B C y z (N 0))
    (Lca : NNN12.BondLayout (q 1) (d 1) C A z x (N 1))
    (M : Fin 3 → ℝ) (P H : ℝ)
    (hM : ∀ i, NNN12.momentExponent (q i) (N i)
      (groupIntercepts (Fintype.card A) (Fintype.card B) (Fintype.card C) c ![x, y, z] i)
      (groupSlopes d t c i) ≤ M i)
    (hcap : ∀ i, groupRates (Fintype.card A) (Fintype.card B) (Fintype.card C) M P i ≤
      N i * Real.logb 2 (q i))
    (hhead : (∑ i, t i * ((bondLog (Fintype.card A) (Fintype.card B) (Fintype.card C) x y z i : ℝ) -
      groupRates (Fintype.card A) (Fintype.card B) (Fintype.card C) M P i)) ≤
      (Fintype.card A + Fintype.card B + Fintype.card C : ℕ) * P + H)
    (ha : 0 < Fintype.card A) (hm : 0 < Fintype.card B + Fintype.card C)
    (hconstant : (∏ i, (q i : ℝ)) * (2 : ℝ) ^ H + 2 ≤ (2 : ℝ) ^ Fintype.card A)
    (T : Tensor ℂ (X x) (X y) (X z)) : value φ T ≤ 2 * (2 : ℝ) ^ P := by
  let a := Fintype.card A
  let b := Fintype.card B
  let cc := Fintype.card C
  let p := a + b + cc
  let rates := groupRates a b cc M P
  let r : Fin 3 → ℕ := fun i => NNN12.codeDimension (q i) (rates i)
  have hr (i : Fin 3) : r i ≤ N i := NNN12.codeDimension_le (N i) (hcap i)
  have hn := combined_network_average φ c hb t hθ Lab Lbc Lca hr T
  have hh := NNN12.rounded_head_mixed q
    (fun i => (bondLog a b cc x y z i : ℝ)) t rates ht (p * P + H) hhead
  rw [Real.rpow_add (by norm_num)] at hh
  have hi (i : Fin 3) := NNN12.moment_rounded_of_le (q := q i) (N i)
    (groupIntercepts a b cc c ![x, y, z] i) (groupSlopes d t c i) (M i)
    (groupDegrees a b cc i * P) (hM i)
  have h0 := mul_le_mul_of_nonneg_right (hi 0)
    (show 0 ≤ value φ T ^ a from pow_nonneg (φ.nonneg _) _)
  have h1 := hi 1
  have h2 := hi 2
  have hs : value φ T ^ p ≤ ((∏ i, (q i : ℝ)) * (2 : ℝ) ^ H + 2) * (2 : ℝ) ^ (p * P) +
      value φ T ^ a * (2 : ℝ) ^ ((b + cc : ℕ) * P) := by
    dsimp [r, rates, groupRates, groupIntercepts, groupDegrees, groupSlopes, a, b, cc, p] at hn hh h0 h1 h2 ⊢
    nlinarith only [hn, hh, h0, h1, h2]
  apply NNN12.retained_scalar_scaled (h := a) (m := b + cc) (by positivity) ha hm hconstant
  have he (n : ℕ) : ((2 : ℝ) ^ P) ^ n = (2 : ℝ) ^ ((n : ℝ) * P) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_comm]
  simpa only [he, p, Nat.add_assoc] using! hs

end OM.NNN13
