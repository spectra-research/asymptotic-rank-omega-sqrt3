import Lib.OM.NNN18.PackAverage
import Lib.OM.NNN13.Step

/-!
# Rates, rounding and the retained bootstrap for the packed network (PACKSTEP T7c)

  `value(T)^p ≤ Λ 2^{pP} + value(T)^a 2^{(b+c)P}`,

where `Λ = ∏ q_i 2^{30} + (Ov_1 + Ov_2)(N_max + 1)` collects the alphabet floors, the cycle
rounding, the packing overhead and the `(N+1)^{1-β}` of the fractional moment.  The source gap
(the head budget) is the hypothesis `hgap`.
-/

noncomputable section
open scoped BigOperators Classical
namespace OM.NNN18.PackNet
open CoordinateTensor OM.NNN.Raw OM.NNN2 OM.NNN11.Network
open OM.NNN11 (bondLog)
open OM.NNN11.ExtractionAB (X)
open Foundations.PairUnitExponents OM.NNN12.Codes
set_option maxHeartbeats 4000000

variable {A B C : Type} [Fintype A] [Fintype B] [Fintype C]
  [DecidableEq A] [DecidableEq B] [DecidableEq C]
  {x y z : ℕ} {N q d : Fin 3 → ℕ} [∀ i, Fact (q i).Prime]

lemma rpow_one_sub_le {n : ℕ} {β : ℝ} (hβ0 : 0 < β) {M : ℕ} (hn : n ≤ M) :
    ((n + 1 : ℕ) : ℝ) ^ (1 - β) ≤ (M + 1 : ℝ) := by
  have h1 : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos n
  calc ((n + 1 : ℕ) : ℝ) ^ (1 - β) ≤ ((n + 1 : ℕ) : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le h1 (by linarith)
    _ = (n + 1 : ℝ) := by rw [Real.rpow_one]; push_cast; ring
    _ ≤ (M + 1 : ℝ) := by have : (n : ℝ) ≤ M := by exact_mod_cast hn
                          linarith

/-- **The rounded packed network inequality.** -/
theorem packed_network_rounded (φ : PolMul.Spectral ℂ)
    (c : Fin 3 → Fin 3 → ℝ) (hb : ∀ i, NNN13.AffineBound φ (c i))
    (t β : Fin 3 → ℝ) (ht : ∀ i, t i ∈ Set.Icc (0 : ℝ) 1)
    (hθ : ∀ i, Foundations.PairUnitExponents.theta φ i ≤ t i)
    (hβ1 : (t 1 + c 1 0 + c 1 2) / 2 ≤ β 1) (hβ2 : (t 2 + c 2 0 + c 2 1) / 2 ≤ β 2)
    (hβpos : ∀ i, 0 < β i) (hβle : ∀ i, β i ≤ 1)
    (Lab : NNN12.BondLayout (q 2) (d 2) A B x y (N 2))
    (Lbc : NNN12.BondLayout (q 0) (d 0) B C y z (N 0))
    (Lca : NNN12.BondLayout (q 1) (d 1) C A z x (N 1))
    (E : Fin 3 → ℝ) (hq : ∀ i, q i ≤ 19)
    (hN : ∀ i, (N i : ℝ) ≤ E i) (hE : ∀ i, E i ≤ N i + 2)
    (hD : ∀ i, NNN13.rawSlope t c i ≤ 0)
    (P : ℝ) (hbase : ∀ i, P ≤ NNN13.plane (c i) ![(x : ℝ), y, z])
    (hgap : (∑ i, t i * (bondLog (Fintype.card A) (Fintype.card B) (Fintype.card C) x y z i : ℝ))
      ≤ ((Fintype.card A + Fintype.card B + Fintype.card C : ℕ) : ℝ) * P
        + t 0 * (((Fintype.card B + Fintype.card C : ℕ) : ℝ) *
            (P - NNN13.plane (c 0) ![(x : ℝ), y, z]) -
            E 0 * NNN13.logMoment (q 0) (d 0) (NNN13.rawSlope t c 0))
        + t 1 * (((Fintype.card A + Fintype.card B + Fintype.card C : ℕ) : ℝ) / β 1 *
            (P - NNN13.plane (c 1) ![(x : ℝ), y, z]) -
            E 1 * NNN13.logMoment (q 1) (d 1) (NNN13.rawSlope t c 1 / β 1))
        + t 2 * (((Fintype.card A + Fintype.card B + Fintype.card C : ℕ) : ℝ) / β 2 *
            (P - NNN13.plane (c 2) ![(x : ℝ), y, z]) -
            E 2 * NNN13.logMoment (q 2) (d 2) (NNN13.rawSlope t c 2 / β 2)))
    (Nmax : ℕ) (hNmax : ∀ i, N i ≤ Nmax)
    (T : Tensor ℂ (X x) (X y) (X z)) :
    value φ T ^ (Fintype.card A + Fintype.card B + Fintype.card C) ≤
      ((∏ i, (q i : ℝ)) * (2 : ℝ) ^ (30 : ℝ) +
        (OM.NNN18.packOverhead (c 1 2) (q 1 ^ Nmax) + OM.NNN18.packOverhead (c 2 1) (q 2 ^ Nmax)) *
          (Nmax + 1 : ℝ)) *
        (2 : ℝ) ^ (((Fintype.card A + Fintype.card B + Fintype.card C : ℕ) : ℝ) * P) +
      value φ T ^ Fintype.card A *
        (2 : ℝ) ^ (((Fintype.card B + Fintype.card C : ℕ) : ℝ) * P) := by
  set p := Fintype.card A + Fintype.card B + Fintype.card C with hp
  set m := Fintype.card B + Fintype.card C with hm
  set v : Fin 3 → ℝ := ![(x : ℝ), y, z] with hv
  -- moment arguments
  set M0 := (m : ℝ) * NNN13.plane (c 0) v
  set D0 := (d 0 : ℝ) * (t 0 - c 0 1 - c 0 2)
  set M1 := (p : ℝ) * NNN13.plane (c 1) v / β 1
  set D1 := (d 1 : ℝ) * (t 1 - c 1 0 - c 1 2) / β 1
  set M2 := (p : ℝ) * NNN13.plane (c 2) v / β 2
  set D2 := (d 2 : ℝ) * (t 2 - c 2 0 - c 2 1) / β 2
  -- rates
  set ρ0 := max 0 ((m : ℝ) * P - NNN12.momentExponent (q 0) (N 0) M0 D0)
  set ρ1 := max 0 ((p : ℝ) * P / β 1 - NNN12.momentExponent (q 1) (N 1) M1 D1)
  set ρ2 := max 0 ((p : ℝ) * P / β 2 - NNN12.momentExponent (q 2) (N 2) M2 D2)
  let ρ : Fin 3 → ℝ := ![ρ0, ρ1, ρ2]
  let r : Fin 3 → ℕ := fun i => NNN12.codeDimension (q i) (ρ i)
  have hsl0 : t 0 - c 0 1 - c 0 2 = NNN13.rawSlope t c 0 := by
    simp [NNN13.rawSlope, NNN13.cross]; ring
  have hsl1 : t 1 - c 1 0 - c 1 2 = NNN13.rawSlope t c 1 := by
    simp [NNN13.rawSlope, NNN13.cross]; ring
  have hsl2 : t 2 - c 2 0 - c 2 1 = NNN13.rawSlope t c 2 := by
    simp [NNN13.rawSlope, NNN13.cross]; ring
  have hpl (i : Fin 3) : P - NNN13.plane (c i) v ≤ 0 := by have := hbase i; linarith
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  -- capacities: every rate fits its alphabet
  have hcap0 : ρ0 ≤ N 0 * Real.logb 2 (q 0) := by
    have hz := NNN13.moment_capacity (q := q 0) (N 0) M0 D0
    have hl := mul_nonneg (Nat.cast_nonneg (N 0)) (NNN12.alphabet_log_pos (q := q 0)).le
    have : (m : ℝ) * P ≤ M0 := by
      simp only [M0]; exact mul_le_mul_of_nonneg_left (hbase 0) hm0
    exact max_le hl (by linarith)
  have hcapi (i : Fin 3) (hi : (p : ℝ) * P / β i ≤ (p : ℝ) * NNN13.plane (c i) v / β i)
      (Mi Di : ℝ) (hMi : Mi = (p : ℝ) * NNN13.plane (c i) v / β i) :
      max 0 ((p : ℝ) * P / β i - NNN12.momentExponent (q i) (N i) Mi Di) ≤
        N i * Real.logb 2 (q i) := by
    have hz := NNN13.moment_capacity (q := q i) (N i) Mi Di
    have hl := mul_nonneg (Nat.cast_nonneg (N i)) (NNN12.alphabet_log_pos (q := q i)).le
    have hle : (p : ℝ) * P / β i ≤ Mi := by rw [hMi]; exact hi
    exact max_le hl (by linarith)
  have hdiv (i : Fin 3) : (p : ℝ) * P / β i ≤ (p : ℝ) * NNN13.plane (c i) v / β i :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (hbase i) hp0) (hβpos i).le
  have hcap1 : ρ1 ≤ N 1 * Real.logb 2 (q 1) := hcapi 1 (hdiv 1) M1 D1 rfl
  have hcap2 : ρ2 ≤ N 2 * Real.logb 2 (q 2) := hcapi 2 (hdiv 2) M2 D2 rfl
  have hr : ∀ i, r i ≤ N i := by
    intro i
    fin_cases i
    · exact NNN12.codeDimension_le (N 0) hcap0
    · exact NNN12.codeDimension_le (N 1) hcap1
    · exact NNN12.codeDimension_le (N 2) hcap2
  -- the averaged network at these code dimensions
  have hn := packed_network_average (r := r) φ c hb t β hθ hβ1 hβ2 hβpos hβle Lab Lbc Lca hr T
  -- moments at the chosen rates
  have hmo0 : NNN12.moment (q 0) (N 0) (r 0) M0 D0 ≤ (2 : ℝ) ^ ((m : ℝ) * P) :=
    NNN12.moment_rounded (N 0) M0 D0 _
  have hmo1 : NNN12.moment (q 1) (N 1) (r 1) M1 D1 ≤ (2 : ℝ) ^ ((p : ℝ) * P / β 1) :=
    NNN12.moment_rounded (N 1) M1 D1 _
  have hmo2 : NNN12.moment (q 2) (N 2) (r 2) M2 D2 ≤ (2 : ℝ) ^ ((p : ℝ) * P / β 2) :=
    NNN12.moment_rounded (N 2) M2 D2 _
  have hpowβ (i : Fin 3) {Mo : ℝ} (h0 : 0 ≤ Mo) (h : Mo ≤ (2 : ℝ) ^ ((p : ℝ) * P / β i)) :
      Mo ^ β i ≤ (2 : ℝ) ^ ((p : ℝ) * P) := by
    calc Mo ^ β i ≤ ((2 : ℝ) ^ ((p : ℝ) * P / β i)) ^ β i :=
          Real.rpow_le_rpow h0 h (hβpos i).le
      _ = (2 : ℝ) ^ ((p : ℝ) * P) := by
          rw [← Real.rpow_mul (by norm_num), div_mul_cancel₀ _ (hβpos i).ne']
  have hmb1 := hpowβ 1 (NNN12.moment_nonneg _ _ _ _) hmo1
  have hmb2 := hpowβ 2 (NNN12.moment_nonneg _ _ _ _) hmo2
  -- head
  have hρ0 : (m : ℝ) * (P - NNN13.plane (c 0) v) -
      E 0 * NNN13.logMoment (q 0) (d 0) (NNN13.rawSlope t c 0) - 10 ≤ ρ0 := by
    have hc := NNN13.moment_rounded_cycles (hq 0) (N 0) M0 (E 0) (d 0) (NNN13.rawSlope t c 0)
      (hN 0) (hE 0) (Nat.cast_nonneg _) (hD 0)
    rw [← hsl0] at hc
    have : (m : ℝ) * P - NNN12.momentExponent (q 0) (N 0) M0 D0 ≤ ρ0 := le_max_right _ _
    simp only [M0, D0] at hc this ⊢
    rw [← hsl0]
    nlinarith
  have hρi (i : Fin 3) (Mi Di : ℝ) (hMi : Mi = (p : ℝ) * NNN13.plane (c i) v / β i)
      (hDi : Di = (d i : ℝ) * (NNN13.rawSlope t c i / β i)) :
      (p : ℝ) / β i * (P - NNN13.plane (c i) v) -
        E i * NNN13.logMoment (q i) (d i) (NNN13.rawSlope t c i / β i) - 10 ≤
      max 0 ((p : ℝ) * P / β i - NNN12.momentExponent (q i) (N i) Mi Di) := by
    have hc := NNN13.moment_rounded_cycles (hq i) (N i) Mi (E i) (d i)
      (NNN13.rawSlope t c i / β i) (hN i) (hE i) (Nat.cast_nonneg _)
      (div_nonpos_of_nonpos_of_nonneg (hD i) (hβpos i).le)
    rw [← hDi] at hc
    have h1 : (p : ℝ) * P / β i - NNN12.momentExponent (q i) (N i) Mi Di ≤
        max 0 ((p : ℝ) * P / β i - NNN12.momentExponent (q i) (N i) Mi Di) := le_max_right _ _
    have h2 : (p : ℝ) / β i * (P - NNN13.plane (c i) v) = (p : ℝ) * P / β i - Mi := by
      rw [hMi]; ring
    linarith
  have hρ1 := hρi 1 M1 D1 rfl (by simp only [D1, ← hsl1]; ring)
  have hρ2 := hρi 2 M2 D2 rfl (by simp only [D2, ← hsl2]; ring)
  have hhead_budget : (∑ i, t i * ((bondLog (Fintype.card A) (Fintype.card B) (Fintype.card C)
      x y z i : ℝ) - ρ i)) ≤ (p : ℝ) * P + 30 := by
    have ht0 := (ht 0).1; have ht1 := (ht 1).1; have ht2 := (ht 2).1
    have ht0' := (ht 0).2; have ht1' := (ht 1).2; have ht2' := (ht 2).2
    have e0 := mul_le_mul_of_nonneg_left hρ0 ht0
    have e1 := mul_le_mul_of_nonneg_left hρ1 ht1
    have e2 := mul_le_mul_of_nonneg_left hρ2 ht2
    simp only [Fin.sum_univ_three, ρ, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons] at hgap ⊢
    nlinarith
  have hh := NNN12.rounded_head_mixed q
    (fun i => (bondLog (Fintype.card A) (Fintype.card B) (Fintype.card C) x y z i : ℝ)) t ρ ht
    ((p : ℝ) * P + 30) hhead_budget
  -- overheads
  have hOv (i : Fin 3) (cc : ℝ) : OM.NNN18.packOverhead cc (q i ^ r i) ≤
      OM.NNN18.packOverhead cc (q i ^ Nmax) :=
    OM.NNN18.packOverhead_mono cc (pow_pos (Fact.out : Nat.Prime (q i)).pos _)
      (Nat.pow_le_pow_right (Fact.out : Nat.Prime (q i)).pos ((hr i).trans (hNmax i)))
  have hN1 := rpow_one_sub_le (hβpos 1) (hNmax 1)
  have hN2 := rpow_one_sub_le (hβpos 2) (hNmax 2)
  have hO1 := OM.NNN18.packOverhead_nonneg (c 1 2) (q 1 ^ r 1)
  have hO2 := OM.NNN18.packOverhead_nonneg (c 2 1) (q 2 ^ r 2)
  have hO1' := OM.NNN18.packOverhead_nonneg (c 1 2) (q 1 ^ Nmax)
  have hO2' := OM.NNN18.packOverhead_nonneg (c 2 1) (q 2 ^ Nmax)
  have hr1 : (0 : ℝ) ≤ ((N 1 + 1 : ℕ) : ℝ) ^ (1 - β 1) := by positivity
  have hr2 : (0 : ℝ) ≤ ((N 2 + 1 : ℕ) : ℝ) ^ (1 - β 2) := by positivity
  have hm1 : 0 ≤ NNN12.moment (q 1) (N 1) (r 1) M1 D1 ^ β 1 := by
    have := NNN12.moment_nonneg (q := q 1) (N 1) (r 1) M1 D1; positivity
  have hm2 : 0 ≤ NNN12.moment (q 2) (N 2) (r 2) M2 D2 ^ β 2 := by
    have := NNN12.moment_nonneg (q := q 2) (N 2) (r 2) M2 D2; positivity
  have hc1 : OM.NNN18.packOverhead (c 1 2) (q 1 ^ r 1) * ((N 1 + 1 : ℕ) : ℝ) ^ (1 - β 1) *
      NNN12.moment (q 1) (N 1) (r 1) M1 D1 ^ β 1 ≤
      OM.NNN18.packOverhead (c 1 2) (q 1 ^ Nmax) * (Nmax + 1 : ℝ) * (2 : ℝ) ^ ((p : ℝ) * P) := by
    apply mul_le_mul (mul_le_mul (hOv 1 _) hN1 hr1 hO1') hmb1 hm1 (by positivity)
  have hc2 : OM.NNN18.packOverhead (c 2 1) (q 2 ^ r 2) * ((N 2 + 1 : ℕ) : ℝ) ^ (1 - β 2) *
      NNN12.moment (q 2) (N 2) (r 2) M2 D2 ^ β 2 ≤
      OM.NNN18.packOverhead (c 2 1) (q 2 ^ Nmax) * (Nmax + 1 : ℝ) * (2 : ℝ) ^ ((p : ℝ) * P) := by
    apply mul_le_mul (mul_le_mul (hOv 2 _) hN2 hr2 hO2') hmb2 hm2 (by positivity)
  have hc0 : NNN12.moment (q 0) (N 0) (r 0) M0 D0 * value φ T ^ Fintype.card A ≤
      (2 : ℝ) ^ ((m : ℝ) * P) * value φ T ^ Fintype.card A :=
    mul_le_mul_of_nonneg_right hmo0 (pow_nonneg (φ.nonneg _) _)
  rw [Real.rpow_add (by norm_num)] at hh
  have hsplit : ((∏ i, (q i : ℝ)) * (2 : ℝ) ^ (30 : ℝ) +
        (OM.NNN18.packOverhead (c 1 2) (q 1 ^ Nmax) + OM.NNN18.packOverhead (c 2 1) (q 2 ^ Nmax)) *
          (Nmax + 1 : ℝ)) * (2 : ℝ) ^ ((p : ℝ) * P) =
      (∏ i, (q i : ℝ)) * ((2 : ℝ) ^ ((p : ℝ) * P) * (2 : ℝ) ^ (30 : ℝ)) +
      OM.NNN18.packOverhead (c 1 2) (q 1 ^ Nmax) * (Nmax + 1 : ℝ) * (2 : ℝ) ^ ((p : ℝ) * P) +
      OM.NNN18.packOverhead (c 2 1) (q 2 ^ Nmax) * (Nmax + 1 : ℝ) * (2 : ℝ) ^ ((p : ℝ) * P) := by
    ring
  rw [hsplit]
  have hr' : (∑ i, t i * ((bondLog (Fintype.card A) (Fintype.card B) (Fintype.card C) x y z i : ℝ)
      - (NNN12.codeDimension (q i) (ρ i) : ℝ) * Real.logb 2 (q i))) =
      (∑ i, t i * ((bondLog (Fintype.card A) (Fintype.card B) (Fintype.card C) x y z i : ℝ)
      - (r i : ℝ) * Real.logb 2 (q i))) := rfl
  rw [hr'] at hh
  linarith only [hn, hh, hc0, hc1, hc2]

end OM.NNN18.PackNet
