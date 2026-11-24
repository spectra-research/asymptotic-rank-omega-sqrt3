import Lib.OM.NNN18.Step
import Mathlib.Combinatorics.Additive.AP.Three.Behrend

/-! # Padding and progression-free densities for the packed source (PACKSTEP T4, T5)

* `value_le_of_card_le`: an all-format affine tariff bounds every tensor whose leg sizes are at
  most `2^{x_i}` (zero padding to a dyadic shape).
* `exists_selection`: for every `K ≥ 1` there are `N` and a 3AP-free `D ⊆ [N]` with
  `K ≤ N·#D` and `log N ≤ ½ log K + 5 √(log K) + 70` (Behrend, via Mathlib's
  `Behrend.roth_lower_bound`; LABEL_PACKING (8)-(12)). -/

noncomputable section
open scoped BigOperators Classical
open CoordinateTensor OM.NNN.Raw
open OM.NNN12 (Shape DyadicTensor)
namespace OM.NNN18

theorem value_le_of_card_le (φ : PolMul.Spectral ℂ) {c : Fin 3 → ℝ}
    (hc : NNN13.AffineBound φ c) {I J K : Type} [Fintype I] [Fintype J] [Fintype K]
    (x : Shape) (hi : Fintype.card I ≤ 2 ^ x 0) (hj : Fintype.card J ≤ 2 ^ x 1)
    (hk : Fintype.card K ≤ 2 ^ x 2) (T : Tensor ℂ I J K) :
    value φ T ≤ (2 : ℝ) ^ NNN13.plane c (fun i => (x i : ℝ)) := by
  have hci : Fintype.card I ≤ Fintype.card (OM.NNN8.BinaryWord (x 0)) := by
    rwa [OM.NNN8.binary_word_card]
  have hcj : Fintype.card J ≤ Fintype.card (OM.NNN8.BinaryWord (x 1)) := by
    rwa [OM.NNN8.binary_word_card]
  have hck : Fintype.card K ≤ Fintype.card (OM.NNN8.BinaryWord (x 2)) := by
    rwa [OM.NNN8.binary_word_card]
  obtain ⟨e0⟩ := Function.Embedding.nonempty_of_card_le hci
  obtain ⟨e1⟩ := Function.Embedding.nonempty_of_card_le hcj
  obtain ⟨e2⟩ := Function.Embedding.nonempty_of_card_le hck
  let T' : DyadicTensor x := fun i j k =>
    Function.extend e0 (fun a => Function.extend e1 (fun b => Function.extend e2
      (fun c => T a b c) 0 k) 0 j) 0 i
  have hT : T = fun a b c => T' (e0 a) (e1 b) (e2 c) := by
    funext a b c
    simp only [T', e0.injective.extend_apply, e1.injective.extend_apply, e2.injective.extend_apply]
  rw [hT, ← mapTensor_indicator]
  exact (value_map_le φ T' _ _ _).trans (hc x T')

/-- A 3AP-free selection with the Behrend density. -/
theorem exists_selection (K : ℕ) (hK : 1 ≤ K) :
    ∃ (N : ℕ) (D : Finset ℕ), 0 < N ∧ (∀ d ∈ D, d < N) ∧ ThreeAPFree (D : Set ℕ) ∧
      K ≤ N * D.card ∧
      Real.log N ≤ Real.log K / 2 + 5 * √(Real.log K) + 70 := by
  set L := Real.log K
  have hL0 : 0 ≤ L := Real.log_nonneg (by exact_mod_cast hK)
  by_cases hsmall : L ≤ 100
  · -- trivial selection: N = K, D = {0}
    refine ⟨K, {0}, by omega, by simp; omega, by simp [ThreeAPFree], by simp, ?_⟩
    have : 0 ≤ 5 * √L := by positivity
    linarith
  · push Not at hsmall
    have hK1 : (1 : ℝ) < K := by
      by_contra h; push Not at h
      have : L ≤ 0 := Real.log_nonpos (by positivity) h
      linarith
    set s := √L with hs
    have hs0 : 0 ≤ s := Real.sqrt_nonneg L
    have hss : s * s = L := Real.mul_self_sqrt hL0
    have hs10 : 10 < s := by nlinarith
    set a := √(K : ℝ) * Real.exp (4 * s)
    have ha1 : 1 ≤ a := by
      have : 1 ≤ √(K : ℝ) := Real.one_le_sqrt.2 hK1.le
      have : 1 ≤ Real.exp (4 * s) := Real.one_le_exp (by positivity)
      nlinarith
    set N := ⌈a⌉₊
    have hNa : a ≤ N := Nat.le_ceil a
    have hNa' : (N : ℝ) < a + 1 := Nat.ceil_lt_add_one (by linarith)
    have hN0 : 0 < N := by
      have : (0 : ℝ) < N := by linarith
      exact_mod_cast this
    have hlogN : Real.log N ≤ L / 2 + 4 * s + 1 := by
      have h1 : Real.log N ≤ Real.log (a + 1) := Real.log_le_log (by positivity) hNa'.le
      have h2 : Real.log (a + 1) ≤ Real.log a + 1 := by
        have : a + 1 ≤ a * Real.exp 1 := by
          have := Real.add_one_le_exp 1
          nlinarith
        calc Real.log (a + 1) ≤ Real.log (a * Real.exp 1) := Real.log_le_log (by positivity) this
          _ = Real.log a + 1 := by rw [Real.log_mul (by positivity) (by positivity), Real.log_exp]
      have h3 : Real.log a = L / 2 + 4 * s := by
        simp only [a]
        rw [Real.log_mul (by positivity) (by positivity), Real.log_exp, Real.log_sqrt (by positivity)]
      linarith
    have hlogNL : Real.log N ≤ L := by nlinarith
    -- Behrend: roth N ≥ N exp(-4 √(log N)) ≥ N exp(-4 s) ≥ √K
    have hroth := Behrend.roth_lower_bound (N := N)
    have hsq : √(Real.log N) ≤ s := Real.sqrt_le_sqrt hlogNL
    have hexp : Real.exp (-4 * s) ≤ Real.exp (-4 * √(Real.log N)) := Real.exp_le_exp.2 (by linarith)
    have hrothK : √(K : ℝ) ≤ (rothNumberNat N : ℝ) := by
      have h1 : (N : ℝ) * Real.exp (-4 * s) ≤ (N : ℝ) * Real.exp (-4 * √(Real.log N)) :=
        mul_le_mul_of_nonneg_left hexp (by positivity)
      have h2 : √(K : ℝ) ≤ (N : ℝ) * Real.exp (-4 * s) := by
        have he : Real.exp (4 * s) * Real.exp (-4 * s) = 1 := by
          rw [← Real.exp_add]; simp
        have : √(K : ℝ) = a * Real.exp (-4 * s) := by
          simp only [a]; rw [mul_assoc, he, mul_one]
        rw [this]
        exact mul_le_mul_of_nonneg_right hNa (by positivity)
      linarith
    obtain ⟨D, hDsub, hDcard, hD⟩ := rothNumberNat_spec N
    refine ⟨N, D, hN0, fun d hd => Finset.mem_range.1 (hDsub hd), hD, ?_, ?_⟩
    · have hKs : (K : ℝ) = √(K : ℝ) * √(K : ℝ) := (Real.mul_self_sqrt (by positivity)).symm
      have hsN : √(K : ℝ) ≤ N := by
        have : √(K : ℝ) ≤ a := by
          have : (1 : ℝ) ≤ Real.exp (4 * s) := Real.one_le_exp (by positivity)
          simp only [a]; nlinarith [Real.sqrt_nonneg (K : ℝ)]
        linarith
      have : (K : ℝ) ≤ (N : ℝ) * D.card := by
        rw [hDcard, hKs]
        exact mul_le_mul hsN hrothK (Real.sqrt_nonneg _) (by positivity)
      exact_mod_cast this
    · linarith

end OM.NNN18
