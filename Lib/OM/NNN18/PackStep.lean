import Lib.OM.NNN18.PackRounded

/-!
`OM.NNN18.triangleStep : TriangleStep`.  For retained bond `0` (`triangle_step_zero`): build the
coefficient network at copy counts `K o` (eleven-slot layouts on all three bonds, NNN13), apply
`PackNet.packed_network_rounded` (packed AB and CA classes, ordinary retained BC), and choose
`K = s²` so large that the retained copies `2^{K o_0}` pay the overhead
`α + B e^{G √K}` (`exists_large`, `lambda_bound`); the retained bootstrap
(`NNN12.retained_scalar_scaled`) gives `value ≤ 2 · 2^F`.  The other two retained bonds follow by
rotating parties and the spectral point (`triangleStepAt_rotate`, as `NNN13.packedStepAt_rotate`).
-/

noncomputable section
open scoped BigOperators Classical
namespace OM.NNN18.PackNet

/-- A subexponential overhead is beaten by `2^{s²}` for `s` large. -/
lemma exists_large (α B G : ℝ) (hα : 0 < α) (hB : 0 ≤ B) (hG : 0 ≤ G) :
    ∃ s : ℕ, 1 ≤ s ∧ α + B * Real.exp (G * s) ≤ (2 : ℝ) ^ (s * s) := by
  set L0 := |Real.log (α + B)| + G + 1 with hL0
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  refine ⟨⌈L0 / Real.log 2⌉₊ + 1, by omega, ?_⟩
  set s := ⌈L0 / Real.log 2⌉₊ + 1
  have hs1 : (1 : ℝ) ≤ s := by simp [s]
  have hsL : L0 ≤ s * Real.log 2 := by
    have h1 := Nat.le_ceil (L0 / Real.log 2)
    have h' : L0 / Real.log 2 ≤ s := by simp only [s]; push_cast; linarith
    rwa [div_le_iff₀ hl2] at h'
  have hαB : 0 < α + B := by linarith
  have hexp1 : 1 ≤ Real.exp (G * s) := Real.one_le_exp (by positivity)
  calc α + B * Real.exp (G * s) ≤ (α + B) * Real.exp (G * s) := by nlinarith
    _ = Real.exp (Real.log (α + B) + G * s) := by rw [Real.exp_add, Real.exp_log hαB]
    _ ≤ Real.exp (((s * s : ℕ) : ℝ) * Real.log 2) := by
        apply Real.exp_le_exp.2
        have h1 : Real.log (α + B) ≤ |Real.log (α + B)| := le_abs_self _
        have h2 : |Real.log (α + B)| ≤ |Real.log (α + B)| * s :=
          le_mul_of_one_le_right (abs_nonneg _) hs1
        have h3 : (s : ℝ) * L0 ≤ (s : ℝ) * (s * Real.log 2) :=
          mul_le_mul_of_nonneg_left hsL (by positivity)
        push_cast
        nlinarith
    _ = (2 : ℝ) ^ (s * s) := by rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]

/-- The overhead constant of the network at copy counts `K o`, bounded by `α + B e^{G √K}`. -/
lemma lambda_bound (c1 c2 : ℝ) (K L : ℕ) :
    (OM.NNN18.packOverhead c1 (11 ^ (K * L)) + OM.NNN18.packOverhead c2 (11 ^ (K * L))) *
        (((K * L : ℕ) : ℝ) + 1) ≤
      ((2 : ℝ) ^ (2 * |c1| + 3) + (2 : ℝ) ^ (2 * |c2| + 3)) * Real.exp 140 * (L + 1) *
        Real.exp ((10 * √(10 * L) + 2) * √K) := by
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg L
  have hsK := Real.sqrt_nonneg (K : ℝ)
  -- the logarithm of the word count
  have hlog : Real.log (((11 ^ (K * L) : ℕ) : ℝ)) ≤ 10 * L * K := by
    rw [Nat.cast_pow, Real.log_pow]
    have h11 : Real.log 11 ≤ 10 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 11 by norm_num); linarith
    push_cast
    have : (0 : ℝ) ≤ (K : ℝ) * L := by positivity
    nlinarith
  have hsq : √(Real.log (((11 ^ (K * L) : ℕ) : ℝ))) ≤ √(10 * L) * √K := by
    rw [← Real.sqrt_mul (by positivity)]
    exact Real.sqrt_le_sqrt (by linarith)
  have hover (c : ℝ) : OM.NNN18.packOverhead c (11 ^ (K * L)) ≤
      (2 : ℝ) ^ (2 * |c| + 3) * Real.exp 140 * Real.exp (10 * √(10 * L) * √K) := by
    unfold OM.NNN18.packOverhead
    rw [mul_assoc, ← Real.exp_add]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.exp_le_exp.2
    nlinarith
  -- `K L + 1 ≤ (L + 1) e^{2 √K}`
  have hKL : ((K * L : ℕ) : ℝ) + 1 ≤ (L + 1) * Real.exp (2 * √K) := by
    have hq := Real.quadratic_le_exp_of_nonneg (show 0 ≤ 2 * √(K : ℝ) by positivity)
    have hsq2 : (2 * √(K : ℝ)) ^ 2 = 4 * K := by
      rw [mul_pow, Real.sq_sqrt hK0]; norm_num
    rw [hsq2] at hq
    have hK1 : (K : ℝ) + 1 ≤ Real.exp (2 * √K) := by nlinarith
    push_cast
    calc (K : ℝ) * L + 1 ≤ (L + 1) * (K + 1) := by nlinarith
      _ ≤ (L + 1) * Real.exp (2 * √K) := mul_le_mul_of_nonneg_left hK1 (by positivity)
  have h1 := hover c1
  have h2 := hover c2
  have hO1 := OM.NNN18.packOverhead_nonneg c1 (11 ^ (K * L))
  have hO2 := OM.NNN18.packOverhead_nonneg c2 (11 ^ (K * L))
  calc (OM.NNN18.packOverhead c1 (11 ^ (K * L)) + OM.NNN18.packOverhead c2 (11 ^ (K * L))) *
        (((K * L : ℕ) : ℝ) + 1)
      ≤ (((2 : ℝ) ^ (2 * |c1| + 3) + (2 : ℝ) ^ (2 * |c2| + 3)) * Real.exp 140 *
          Real.exp (10 * √(10 * L) * √K)) * ((L + 1) * Real.exp (2 * √K)) := by
        apply mul_le_mul _ hKL (by positivity) (by positivity)
        nlinarith
    _ = ((2 : ℝ) ^ (2 * |c1| + 3) + (2 : ℝ) ^ (2 * |c2| + 3)) * Real.exp 140 * (L + 1) *
          Real.exp ((10 * √(10 * L) + 2) * √K) := by
        rw [show (10 * √(10 * (L : ℝ)) + 2) * √(K : ℝ) = 10 * √(10 * L) * √K + 2 * √K by ring,
          Real.exp_add]
        ring

end OM.NNN18.PackNet

namespace OM.NNN18.PackNet
open CoordinateTensor OM.NNN.Raw
open OM.NNN12 (Shape DyadicTensor)
open OM.NNN11.ExtractionAB (X)

lemma capacity_le_sum {k A B : ℝ} (hk : 0 ≤ k) (hAB : 0 ≤ A + B) :
    NNN13.capacity k A B ≤ A + B := by
  unfold NNN13.capacity
  refine (min_le_left _ _).trans ?_
  rw [div_le_iff₀ (by linarith)]
  nlinarith

lemma packedGap_scale (K : ℕ) (o : Fin 3 → ℕ) (last : Fin 3) (t β : Fin 3 → ℝ)
    (C : Fin 3 → Fin 3 → ℝ) (F : ℝ) (x : Fin 3 → ℝ) :
    OM.NNN18.packedGap (fun i => K * o i) last t β C F x =
      K * OM.NNN18.packedGap o last t β C F x := by
  have hcyc (i : Fin 3) : NNN13.rawCycles (fun i => K * o i) (fun _ => NNN13.Alphabet.eleven) x i =
      NNN13.rawCycles o (fun _ => NNN13.Alphabet.eleven) x i * K := by
    simp only [NNN13.rawCycles, NNN13.Alphabet.k, Nat.cast_ofNat]
    rw [← OM.NNN18.capacity_scale _ _ _ (Nat.cast_nonneg K)]
    fin_cases i <;> simp [NNN13.rawSupplyA, NNN13.rawSupplyB] <;> ring_nf
  simp only [OM.NNN18.packedGap, hcyc, NNN13.rawTotal, NNN13.rawDegree, NNN13.rawSupplyA,
    NNN13.rawSupplyB, Fin.sum_univ_three]
  fin_cases last <;> simp <;> ring

lemma logMoment_eleven' (D : ℝ) :
    NNN13.logMoment NNN13.Alphabet.eleven.q (NNN13.Alphabet.eleven.d : ℝ) D = OM.NNN18.ell D := by
  simp only [NNN13.Alphabet.q, NNN13.Alphabet.d]
  rw [show ((3 : ℕ) : ℝ) = 3 by norm_num]
  exact OM.NNN18.logMoment_eleven D

end OM.NNN18.PackNet

namespace OM.NNN18.PackNet
open CoordinateTensor OM.NNN.Raw
open OM.NNN12 (Shape DyadicTensor)
open OM.NNN11.ExtractionAB (X)
open OM.NNN11 (bondLog)

/-- `TriangleStep` at one retained bond. -/
def TriangleStepAt (last : Fin 3) : Prop :=
  ∀ (φ : PolMul.Spectral ℂ) (o : Fin 3 → ℕ) (C : Fin 3 → Fin 3 → ℝ) (t β : Fin 3 → ℝ) (F : ℝ),
    (∀ i, NNN13.AffineBound φ (C i)) → (∀ i, t i ∈ Set.Icc (0 : ℝ) 1) →
    (∀ i, Foundations.PairUnitExponents.theta φ i ≤ t i) → β last = 1 → (∀ i, 0 < β i) →
    (∀ i, i ≠ last → (t i + NNN13.cross (C i) i) / 2 ≤ β i ∧ β i ≤ 1) →
    (∀ i, NNN13.rawSlope t C i ≤ 0) → (∀ i, 1 ≤ o i) →
    ∀ (v : Shape), (∀ i, F ≤ NNN13.plane (C i) (fun j => (v j : ℝ))) →
    0 ≤ OM.NNN18.packedGap o last t β C F (fun j => (v j : ℝ)) →
    ∀ U : DyadicTensor v, value φ U ≤ 2 * (2 : ℝ) ^ F

/-- The source gap in the form used by `packed_network_rounded` (retained bond `0`). -/
lemma gap_network_form (n : Fin 3 → ℕ) (t β : Fin 3 → ℝ) (hβ0 : β 0 = 1)
    (C : Fin 3 → Fin 3 → ℝ) (F : ℝ) (x y z : ℕ)
    (hgap : 0 ≤ OM.NNN18.packedGap n 0 t β C F ![(x : ℝ), y, z]) :
    (∑ i, t i * (bondLog (n 0) (n 1) (n 2) x y z i : ℝ))
      ≤ ((n 0 + n 1 + n 2 : ℕ) : ℝ) * F
        + t 0 * (((n 1 + n 2 : ℕ) : ℝ) * (F - NNN13.plane (C 0) ![(x : ℝ), y, z]) -
            NNN13.rawCycles n (fun _ => NNN13.Alphabet.eleven) ![(x : ℝ), y, z] 0 *
              NNN13.logMoment NNN13.Alphabet.eleven.q (NNN13.Alphabet.eleven.d : ℝ)
                (NNN13.rawSlope t C 0))
        + t 1 * (((n 0 + n 1 + n 2 : ℕ) : ℝ) / β 1 * (F - NNN13.plane (C 1) ![(x : ℝ), y, z]) -
            NNN13.rawCycles n (fun _ => NNN13.Alphabet.eleven) ![(x : ℝ), y, z] 1 *
              NNN13.logMoment NNN13.Alphabet.eleven.q (NNN13.Alphabet.eleven.d : ℝ)
                (NNN13.rawSlope t C 1 / β 1))
        + t 2 * (((n 0 + n 1 + n 2 : ℕ) : ℝ) / β 2 * (F - NNN13.plane (C 2) ![(x : ℝ), y, z]) -
            NNN13.rawCycles n (fun _ => NNN13.Alphabet.eleven) ![(x : ℝ), y, z] 2 *
              NNN13.logMoment NNN13.Alphabet.eleven.q (NNN13.Alphabet.eleven.d : ℝ)
                (NNN13.rawSlope t C 2 / β 2)) := by
  simp only [logMoment_eleven']
  have hh (i : Fin 3) := NNN13.rawHead_eq n x y z i
  simp only [OM.NNN18.packedGap, Fin.sum_univ_three, NNN13.rawTotal, NNN13.rawDegree, hβ0,
    div_one] at hgap
  simp only [Fin.sum_univ_three, ← hh 0, ← hh 1, ← hh 2, NNN13.rawSlope]
  simp only [Fin.isValue, ↓reduceIte, Nat.cast_add] at hgap ⊢
  have h10 : ((1 : Fin 3) = 0) = False := by simp
  have h20 : ((2 : Fin 3) = 0) = False := by simp
  simp only [h10, h20, if_false, sub_zero] at hgap
  linear_combination hgap

end OM.NNN18.PackNet

namespace OM.NNN18.PackNet
open CoordinateTensor OM.NNN.Raw
open OM.NNN12 (Shape DyadicTensor)
open OM.NNN11.ExtractionAB (X)
open OM.NNN11 (bondLog)

theorem triangle_step_zero : TriangleStepAt 0 := by
  intro φ o C t β F hb ht hθ hβ0 hβpos hβ hD ho v hbase hgap U
  have hv : (fun j => (v j : ℝ)) = ![(v 0 : ℝ), v 1, v 2] := by
    funext j; fin_cases j <;> rfl
  rw [hv] at hbase hgap
  -- constants independent of the scaling
  set L : ℕ := (o 0 + o 1 + o 2) * (v 0 + v 1 + v 2) with hL
  have h11 : NNN13.Alphabet.eleven.q = 11 := rfl
  have hαpos : (0 : ℝ) < (∏ _i : Fin 3, ((11 : ℕ) : ℝ)) * (2 : ℝ) ^ (30 : ℝ) := by
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]; positivity
  obtain ⟨s, hs1, hs⟩ := exists_large ((∏ _i : Fin 3, ((11 : ℕ) : ℝ)) * (2 : ℝ) ^ (30 : ℝ))
    (((2 : ℝ) ^ (2 * |C 1 2| + 3) + (2 : ℝ) ^ (2 * |C 2 1| + 3)) * Real.exp 140 * ((L : ℝ) + 1))
    (10 * √(10 * (L : ℝ)) + 2) hαpos (by positivity) (by positivity)
  set K := s * s with hK
  have hK1 : 1 ≤ K := Nat.mul_le_mul hs1 hs1
  set n : Fin 3 → ℕ := fun i => K * o i with hn
  have hn0 : 0 < n 0 := Nat.mul_pos (by omega) (by have := ho 0; omega)
  have hn12 : 0 < n 1 + n 2 := by
    have : 0 < n 1 := Nat.mul_pos (by omega) (by have := ho 1; omega)
    omega
  have hgapn : 0 ≤ OM.NNN18.packedGap n 0 t β C F ![(v 0 : ℝ), v 1, v 2] := by
    rw [packedGap_scale]; exact mul_nonneg (Nat.cast_nonneg K) hgap
  -- layouts on the three bonds (eleven-slot alphabet)
  obtain ⟨N0, ⟨L0⟩, hN0, hE0⟩ := NNN13.AllPositions.exists_packed_layout
    (A := Fin (n 1)) (B := Fin (n 2)) (x := v 1) (y := v 2)
    NNN13.Alphabet.eleven.differenceSet NNN13.Alphabet.eleven.parameters.1
    NNN13.Alphabet.eleven.parameters.2.1 NNN13.Alphabet.eleven.counts.1
    NNN13.Alphabet.eleven.counts.2
  obtain ⟨N1, ⟨L1⟩, hN1, hE1⟩ := NNN13.AllPositions.exists_packed_layout
    (A := Fin (n 2)) (B := Fin (n 0)) (x := v 2) (y := v 0)
    NNN13.Alphabet.eleven.differenceSet NNN13.Alphabet.eleven.parameters.1
    NNN13.Alphabet.eleven.parameters.2.1 NNN13.Alphabet.eleven.counts.1
    NNN13.Alphabet.eleven.counts.2
  obtain ⟨N2, ⟨L2⟩, hN2, hE2⟩ := NNN13.AllPositions.exists_packed_layout
    (A := Fin (n 0)) (B := Fin (n 1)) (x := v 0) (y := v 1)
    NNN13.Alphabet.eleven.differenceSet NNN13.Alphabet.eleven.parameters.1
    NNN13.Alphabet.eleven.parameters.2.1 NNN13.Alphabet.eleven.counts.1
    NNN13.Alphabet.eleven.counts.2
  let Nv : Fin 3 → ℕ := ![N0, N1, N2]
  let E : Fin 3 → ℝ := fun i =>
    NNN13.rawCycles n (fun _ => NNN13.Alphabet.eleven) ![(v 0 : ℝ), v 1, v 2] i
  have hN : ∀ i, (Nv i : ℝ) ≤ E i := by
    intro i
    fin_cases i
    · simpa [Nv, E, NNN13.rawCycles, NNN13.rawSupplyA, NNN13.rawSupplyB] using! hN0
    · simpa [Nv, E, NNN13.rawCycles, NNN13.rawSupplyA, NNN13.rawSupplyB] using! hN1
    · simpa [Nv, E, NNN13.rawCycles, NNN13.rawSupplyA, NNN13.rawSupplyB,
        Matrix.cons_val_two] using! hN2
  have hE : ∀ i, E i ≤ Nv i + 2 := by
    intro i
    fin_cases i
    · simpa [Nv, E, NNN13.rawCycles, NNN13.rawSupplyA, NNN13.rawSupplyB] using! hE0.le
    · simpa [Nv, E, NNN13.rawCycles, NNN13.rawSupplyA, NNN13.rawSupplyB] using! hE1.le
    · simpa [Nv, E, NNN13.rawCycles, NNN13.rawSupplyA, NNN13.rawSupplyB,
        Matrix.cons_val_two] using! hE2.le
  -- every cycle count is at most `K L`
  have hsupply : ∀ i, NNN13.rawSupplyA n ![(v 0 : ℝ), v 1, v 2] i +
      NNN13.rawSupplyB n ![(v 0 : ℝ), v 1, v 2] i ≤ ((K * L : ℕ) : ℝ) := by
    intro i
    have hKo : ∀ a b : ℕ, ((K * a : ℕ) : ℝ) * (b : ℝ) = (K : ℝ) * ((a * b : ℕ) : ℝ) := by
      intro a b; push_cast; ring
    have hle : ∀ a b c d : ℕ, a * b + c * d ≤ L → ((K * a : ℕ) : ℝ) * (b : ℝ) +
        ((K * c : ℕ) : ℝ) * (d : ℝ) ≤ ((K * L : ℕ) : ℝ) := by
      intro a b c d h
      rw [hKo, hKo, ← mul_add]
      push_cast
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast h) (Nat.cast_nonneg K)
    fin_cases i
    · exact hle (o 1) (v 2) (o 2) (v 1) (by simp only [hL]; nlinarith)
    · exact hle (o 2) (v 0) (o 0) (v 2) (by simp only [hL]; nlinarith)
    · exact hle (o 0) (v 1) (o 1) (v 0) (by simp only [hL]; nlinarith)
  have hNmax : ∀ i, Nv i ≤ K * L := by
    intro i
    have h1 : E i ≤ ((K * L : ℕ) : ℝ) := by
      refine (capacity_le_sum (by norm_num) ?_).trans (hsupply i)
      fin_cases i <;> simp [NNN13.rawSupplyA, NNN13.rawSupplyB] <;> positivity
    exact_mod_cast (hN i).trans h1
  -- the label exponents
  have hβle : ∀ i, β i ≤ 1 := by
    intro i
    by_cases hi : i = 0
    · rw [hi, hβ0]
    · exact (hβ i hi).2
  have hβ1 : (t 1 + C 1 0 + C 1 2) / 2 ≤ β 1 := by
    have := (hβ 1 (by decide +kernel)).1
    simpa [NNN13.cross, add_assoc] using this
  have hβ2 : (t 2 + C 2 0 + C 2 1) / 2 ≤ β 2 := by
    have := (hβ 2 (by decide +kernel)).1
    simpa [NNN13.cross, add_assoc] using this
  have hq : ∀ i : Fin 3, (fun _ : Fin 3 => NNN13.Alphabet.eleven.q) i ≤ 19 :=
    fun _ => NNN13.Alphabet.eleven.parameters.2.2.2
  have hround := packed_network_rounded (A := Fin (n 0)) (B := Fin (n 1)) (C := Fin (n 2))
    (x := v 0) (y := v 1) (z := v 2) (N := Nv)
    (q := fun _ => NNN13.Alphabet.eleven.q) (d := fun _ => NNN13.Alphabet.eleven.d)
    φ C hb t β ht hθ hβ1 hβ2 hβpos hβle L2 L0 L1 E hq hN hE hD F hbase
    (by simp only [Fintype.card_fin]; exact gap_network_form n t β hβ0 C F (v 0) (v 1) (v 2) hgapn)
    (K * L) hNmax U
  simp only [Fintype.card_fin] at hround
  -- the overhead constant is beaten by the retained copies
  have hΛ : (∏ _i : Fin 3, ((NNN13.Alphabet.eleven.q : ℕ) : ℝ)) * (2 : ℝ) ^ (30 : ℝ) +
      (OM.NNN18.packOverhead (C 1 2) (NNN13.Alphabet.eleven.q ^ (K * L)) +
        OM.NNN18.packOverhead (C 2 1) (NNN13.Alphabet.eleven.q ^ (K * L))) *
          (((K * L : ℕ) : ℝ) + 1) ≤ (2 : ℝ) ^ (n 0) := by
    have h1 := lambda_bound (C 1 2) (C 2 1) K L
    have hsqrt : √(K : ℝ) = s := by
      rw [hK]; push_cast; exact Real.sqrt_mul_self (Nat.cast_nonneg s)
    rw [hsqrt] at h1
    have h2 : (2 : ℝ) ^ (s * s) ≤ (2 : ℝ) ^ (n 0) := by
      apply pow_le_pow_right₀ (by norm_num)
      show K ≤ K * o 0
      have := ho 0
      nlinarith
    rw [h11]
    linarith
  -- the retained bootstrap
  have hpos : 0 < (2 : ℝ) ^ F := by positivity
  apply NNN12.retained_scalar_scaled (h := n 0) (m := n 1 + n 2) hpos hn0 hn12 hΛ
  have he (k : ℕ) : ((2 : ℝ) ^ F) ^ k = (2 : ℝ) ^ ((k : ℝ) * F) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_comm]
  simpa only [he, Nat.add_assoc, Nat.cast_add] using hround

end OM.NNN18.PackNet

namespace OM.NNN18.PackNet
open CoordinateTensor OM.NNN.Raw
open OM.NNN12 (Shape DyadicTensor)
open Foundations.PairUnitExponents Foundations.OrientationTransport Lib.E.RectangularSpectrum

lemma packedGap_rotate (n : Fin 3 → ℕ) (t β : Fin 3 → ℝ) (C : Fin 3 → Fin 3 → ℝ) (F : ℝ)
    (x : Fin 3 → ℝ) (i : Fin 3) :
    OM.NNN18.packedGap (NNN13.rotate n) i (NNN13.rotate t) (NNN13.rotate β) (NNN13.rotateRows C) F
      (NNN13.rotate x) = OM.NNN18.packedGap n (NNN13.rotate (fun j => j) i) t β C F x := by
  have h01 : (0 : Fin 3) ≠ 1 := by decide +kernel
  have h02 : (0 : Fin 3) ≠ 2 := by decide +kernel
  have h10 : (1 : Fin 3) ≠ 0 := by decide +kernel
  have h12 : (1 : Fin 3) ≠ 2 := by decide +kernel
  have h20 : (2 : Fin 3) ≠ 0 := by decide +kernel
  have h21 : (2 : Fin 3) ≠ 1 := by decide +kernel
  fin_cases i <;>
    simp [OM.NNN18.packedGap, NNN13.rawTotal, NNN13.rawDegree, NNN13.rawSupplyA,
      NNN13.rawSupplyB, NNN13.rawCycles, NNN13.cross, NNN13.rotateRows, NNN13.rotate,
      Fin.sum_univ_three, NNN13.plane, h01, h02, h10, h12, h20, h21] <;>
    ring_nf

end OM.NNN18.PackNet

namespace OM.NNN18.PackNet
open CoordinateTensor OM.NNN.Raw
open OM.NNN12 (Shape DyadicTensor)
open Foundations.PairUnitExponents Foundations.OrientationTransport Lib.E.RectangularSpectrum

lemma rotate_apply {α : Type*} (w : Fin 3 → α) (j : Fin 3) :
    NNN13.rotate w j = w (NNN13.rotate (fun k => k) j) := by
  fin_cases j <;> rfl

lemma cross_rotateRows (C : Fin 3 → Fin 3 → ℝ) (j : Fin 3) :
    NNN13.cross (NNN13.rotateRows C j) j =
      NNN13.cross (C (NNN13.rotate (fun k => k) j)) (NNN13.rotate (fun k => k) j) := by
  fin_cases j <;> simp [NNN13.cross, NNN13.rotateRows, NNN13.rotate] <;> ring

lemma rotate_injective : Function.Injective (NNN13.rotate (fun k : Fin 3 => k)) := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp_all [NNN13.rotate]

theorem triangleStepAt_rotate (i : Fin 3) (h : TriangleStepAt i) :
    TriangleStepAt (NNN13.rotate (fun j => j) i) := by
  intro φ o C t β F hb ht hθ hβ0 hβpos hβ hD ho v hbase hgap U
  let ψ := pullPoint (pullPoint φ (rot 1)) (rot 0)
  have hb' (j : Fin 3) : NNN13.AffineBound ψ (NNN13.rotateRows C j) := by
    fin_cases j
    · exact NNN13.affineBound_rotate φ _ (hb 1)
    · exact NNN13.affineBound_rotate φ _ (hb 2)
    · exact NNN13.affineBound_rotate φ _ (hb 0)
  have ht' (j) : NNN13.rotate t j ∈ Set.Icc (0 : ℝ) 1 := by
    rw [rotate_apply]; exact ht _
  have hσ : ∀ j : Fin 3, (rot 1).symm ((rot 0).symm j) = NNN13.rotate (fun k => k) j := by
    decide +kernel
  have hθ' (j) : Foundations.PairUnitExponents.theta ψ j ≤ NNN13.rotate t j := by
    have e1 := theta_legReindex (pullPoint φ (rot 1)) (rot 0) j
    have e2 := theta_legReindex (F := ℂ) φ (rot 1) ((rot 0).symm j)
    have e : Foundations.PairUnitExponents.theta ψ j =
        Foundations.PairUnitExponents.theta φ (NNN13.rotate (fun k => k) j) := by
      rw [← hσ j]; exact e1.trans e2
    rw [e, rotate_apply t]
    exact hθ _
  have hβ0' : NNN13.rotate β i = 1 := by rw [rotate_apply]; exact hβ0
  have hβpos' (j) : 0 < NNN13.rotate β j := by rw [rotate_apply]; exact hβpos _
  have hβ' (j) (hj : j ≠ i) : (NNN13.rotate t j + NNN13.cross (NNN13.rotateRows C j) j) / 2 ≤
      NNN13.rotate β j ∧ NNN13.rotate β j ≤ 1 := by
    rw [rotate_apply t, rotate_apply β, cross_rotateRows]
    exact hβ _ (fun he => hj (rotate_injective he))
  have hD' (j) : NNN13.rawSlope (NNN13.rotate t) (NNN13.rotateRows C) j ≤ 0 := by
    rw [NNN13.rawSlope_rotate, rotate_apply]; exact hD _
  have ho' (j) : 1 ≤ NNN13.rotate o j := by rw [rotate_apply]; exact ho _
  have hbase' (j) : F ≤ NNN13.plane (NNN13.rotateRows C j)
      (fun k => ((NNN13.rotate v k : ℕ) : ℝ)) := by
    change F ≤ NNN13.plane (NNN13.rotateRows C j) (NNN13.rotate (fun k => (v k : ℝ)))
    fin_cases j
    · simpa only [← NNN13.plane_rotate (C 1) (fun k => (v k : ℝ))] using! hbase 1
    · simpa only [← NNN13.plane_rotate (C 2) (fun k => (v k : ℝ))] using! hbase 2
    · simpa only [← NNN13.plane_rotate (C 0) (fun k => (v k : ℝ))] using! hbase 0
  have hgap' : 0 ≤ OM.NNN18.packedGap (NNN13.rotate o) i (NNN13.rotate t) (NNN13.rotate β)
      (NNN13.rotateRows C) F (fun k => ((NNN13.rotate v k : ℕ) : ℝ)) := by
    change 0 ≤ OM.NNN18.packedGap (NNN13.rotate o) i (NNN13.rotate t) (NNN13.rotate β)
      (NNN13.rotateRows C) F (NNN13.rotate (fun k => (v k : ℝ)))
    rw [packedGap_rotate]
    exact hgap
  have hh := h ψ (NNN13.rotate o) (NNN13.rotateRows C) (NNN13.rotate t) (NNN13.rotate β) F hb'
    ht' hθ' hβ0' hβpos' hβ' hD' ho' (NNN13.rotate v) hbase' hgap' (swap02 (swap12 U))
  have e1 := NNN11.value_swap12 φ U
  have e2 := NNN11.value_swap02 (pullPoint φ (rot 1)) (swap12 U)
  calc value φ U = value (pullPoint (pullPoint φ (rot 1)) (rot 0)) (swap02 (swap12 U)) :=
        (e2.trans e1).symm
    _ ≤ 2 * (2 : ℝ) ^ F := hh

theorem triangleStepAt (i : Fin 3) : TriangleStepAt i := by
  fin_cases i
  · exact triangle_step_zero
  · exact triangleStepAt_rotate 0 triangle_step_zero
  · exact triangleStepAt_rotate 1 (triangleStepAt_rotate 0 triangle_step_zero)

end OM.NNN18.PackNet

namespace OM.NNN18

/-- **Node PACKSTEP: the packed (triangle-label) source rule holds for the actual network.** -/
theorem triangleStep : TriangleStep := by
  intro last φ o C t β F hb ht _hsum hθ hβ0 hβpos hβ hD ho v hbase hgap U
  exact PackNet.triangleStepAt last φ o C t β F hb ht hθ hβ0 hβpos hβ hD ho v hbase hgap U

end OM.NNN18
