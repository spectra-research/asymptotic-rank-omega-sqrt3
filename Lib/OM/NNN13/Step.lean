import Lib.OM.NNN13.Rounding

/-! The finite all-residual improvement step. Every analytic supersolution
and affine-majorant assumption is explicit. No near-profile certificate is
asserted here. Moments may include the uniform cycle-rounding loss. -/
noncomputable section
open scoped BigOperators Classical
namespace OM.NNN13
open CoordinateTensor OM.NNN.Raw NNN11.Network
open NNN11 (bondLog)
open NNN11.ExtractionAB (X)
open Foundations.PairUnitExponents
set_option maxHeartbeats 2000000

variable {A B C : Type} [Fintype A] [Fintype B] [Fintype C]
  [DecidableEq A] [DecidableEq B] [DecidableEq C]
  {x y z : ℕ} {N q d : Fin 3 → ℕ} [∀ i, Fact (q i).Prime]

theorem combined_recursive_step (φ : PolMul.Spectral ℂ)
    (c : Fin 3 → Fin 3 → ℝ) (F ε H : ℝ) (hε : 0 ≤ ε)
    (hb : ∀ i, AffineBound φ (fun j => c i j + ε))
    (t : Fin 3 → ℝ) (ht : ∀ i, t i ∈ Set.Icc (0 : ℝ) 1)
    (htsum : ∑ i, t i ≤ 9 / 4) (hθ : ∀ i, theta φ i ≤ t i)
    (Lab : NNN12.BondLayout (q 2) (d 2) A B x y (N 2))
    (Lbc : NNN12.BondLayout (q 0) (d 0) B C y z (N 0))
    (Lca : NNN12.BondLayout (q 1) (d 1) C A z x (N 1))
    (M : Fin 3 → ℝ)
    (hM : ∀ i, NNN12.momentExponent (q i) (N i)
      (groupIntercepts (Fintype.card A) (Fintype.card B) (Fintype.card C) c ![x, y, z] i)
      (groupSlopes d t c i) ≤ M i)
    (hbase : ∀ i, F ≤ plane (c i) ![x, y, z])
    (hsuper : (∑ i, t i * (bondLog (Fintype.card A) (Fintype.card B) (Fintype.card C) x y z i : ℝ)) +
      (∑ i, t i * M i) ≤
      ((Fintype.card A + Fintype.card B + Fintype.card C : ℕ) +
        ∑ i, t i * groupDegrees (Fintype.card A) (Fintype.card B) (Fintype.card C) i) * F + H)
    (ha : 0 < Fintype.card A) (hm : 0 < Fintype.card B + Fintype.card C)
    (hconstant : (∏ i, (q i : ℝ)) * (2 : ℝ) ^ H + 2 ≤ (2 : ℝ) ^ Fintype.card A)
    (T : Tensor ℂ (X x) (X y) (X z)) :
    value φ T ≤ 2 * (2 : ℝ) ^ (F + gamma * ε * (x + y + z : ℝ)) := by
  let a := Fintype.card A
  let b := Fintype.card B
  let cc := Fintype.card C
  let p := a + b + cc
  let m : Fin 3 → ℝ := fun i => (groupDegrees a b cc i : ℝ)
  let V : ℝ := x + y + z
  let P := F + gamma * ε * V
  let M' : Fin 3 → ℝ := fun i => M i + m i * ε * V
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hmass : (∑ i, t i * m i) ≤ p * (9 / 4) := by
    apply recursive_mass_le t m (fun i => (ht i).1) _ htsum (Nat.cast_nonneg p)
    intro i
    dsimp [m, p]
    exact_mod_cast groupDegrees_le a b cc i
  have hM' (i : Fin 3) : NNN12.momentExponent (q i) (N i)
      (groupIntercepts a b cc (fun i j => c i j + ε) ![x, y, z] i)
      (groupSlopes d t (fun i j => c i j + ε) i) ≤ M' i :=
    recursive_moment_bound q N d a b cc t c ![x, y, z] M hε hM i
  have hcap (i : Fin 3) : groupRates a b cc M' P i ≤ N i * Real.logb 2 (q i) := by
    apply recursive_rate_cap (Nat.cast_nonneg (groupDegrees a b cc i))
      (mul_nonneg (Nat.cast_nonneg (N i)) (NNN12.alphabet_log_pos (q := q i)).le) _ hε hV
    have hz := moment_capacity (q := q i) (N i)
      (groupIntercepts a b cc c ![x, y, z] i) (groupSlopes d t c i)
    have hf := mul_le_mul_of_nonneg_left (hbase i) (Nat.cast_nonneg (groupDegrees a b cc i) :
      (0 : ℝ) ≤ groupDegrees a b cc i)
    dsimp [groupIntercepts] at hz
    exact hf.trans (hz.trans (add_le_add (hM i) le_rfl))
  have hh := recursive_head_affordable t m M (p := p)
    (H := (∑ i, t i * (bondLog a b cc x y z i : ℝ)) - H)
    (P := F) (ε := ε) (V := V) (fun i => (ht i).1) hε hV hmass
    (by dsimp [m, p, a, b, cc]; linarith [hsuper])
  have hhead : (∑ i, t i * ((bondLog a b cc x y z i : ℝ) -
      groupRates a b cc M' P i)) ≤ p * P + H := by
    simp only [mul_sub, Finset.sum_sub_distrib]
    change (∑ i, t i * (bondLog a b cc x y z i : ℝ)) -
      (∑ i, t i * max 0 (m i * (F + gamma * ε * V) - (M i + m i * ε * V))) ≤ _
    dsimp [P]
    linarith only [hh]
  exact combined_network_rounded_with_loss φ (fun i j => c i j + ε) hb t ht hθ
    Lab Lbc Lca M' P H hM' hcap hhead ha hm hconstant T

/-- A continuous supersolution pays all integral losses uniformly. `E` is
the real cycle capacity and `N` is the packed integer cycle count. -/
theorem combined_continuous_step (φ : PolMul.Spectral ℂ)
    (c : Fin 3 → Fin 3 → ℝ) (F ε : ℝ) (hε : 0 ≤ ε)
    (hb : ∀ i, AffineBound φ (fun j => c i j + ε))
    (t : Fin 3 → ℝ) (ht : ∀ i, t i ∈ Set.Icc (0 : ℝ) 1)
    (htsum : ∑ i, t i ≤ 9 / 4) (hθ : ∀ i, theta φ i ≤ t i)
    (Lab : NNN12.BondLayout (q 2) (d 2) A B x y (N 2))
    (Lbc : NNN12.BondLayout (q 0) (d 0) B C y z (N 0))
    (Lca : NNN12.BondLayout (q 1) (d 1) C A z x (N 1))
    (M E D : Fin 3 → ℝ) (hq : ∀ i, q i ≤ 19)
    (hN : ∀ i, (N i : ℝ) ≤ E i) (hE : ∀ i, E i ≤ N i + 2)
    (hD : ∀ i, D i ≤ 0) (hslope : ∀ i, groupSlopes d t c i = d i * D i)
    (hM : ∀ i, M i =
      groupIntercepts (Fintype.card A) (Fintype.card B) (Fintype.card C) c ![x, y, z] i +
        E i * logMoment (q i) (d i) (D i))
    (hbase : ∀ i, F ≤ plane (c i) ![x, y, z])
    (hsuper : (∑ i, t i * (bondLog (Fintype.card A) (Fintype.card B) (Fintype.card C) x y z i : ℝ)) +
      (∑ i, t i * M i) ≤
      ((Fintype.card A + Fintype.card B + Fintype.card C : ℕ) +
        ∑ i, t i * groupDegrees (Fintype.card A) (Fintype.card B) (Fintype.card C) i) * F)
    (ha : 43 ≤ Fintype.card A) (hm : 0 < Fintype.card B + Fintype.card C)
    (T : Tensor ℂ (X x) (X y) (X z)) :
    value φ T ≤ 2 * (2 : ℝ) ^ (F + gamma * ε * (x + y + z : ℝ)) := by
  apply combined_recursive_step φ c F ε 30 hε hb t ht htsum hθ Lab Lbc Lca
    (fun i => M i + 10) _ hbase _ (by omega) hm (alphabet_rounding_constant q hq ha) T
  · intro i
    (try dsimp only)
    rw [hslope, hM]
    exact moment_rounded_cycles (hq i) (N i) _ (E i) (d i) (D i)
      (hN i) (hE i) (Nat.cast_nonneg _) (hD i)
  · have hloss : (∑ i, t i * (10 : ℝ)) ≤ 30 := by
      have hsum : (∑ i, t i * (10 : ℝ)) ≤ ∑ _i : Fin 3, (10 : ℝ) :=
        Finset.sum_le_sum (fun i _ => by nlinarith [(ht i).2])
      convert! hsum using 1 <;> norm_num
    simp only [mul_add, Finset.sum_add_distrib]
    linarith only [hsuper, hloss]

end OM.NNN13
