import Lib.OM.NNN13.Step
import Lib.OM.NNN13.Policies
import Lib.OM.NNN13.Layout
import Lib.OM.NNN12.RecursiveTransport

/-! Realizing a scalar policy with actual integer layouts. These interfaces
retain the original spectral point, including when tensor legs are rotated. -/
noncomputable section
open scoped BigOperators Classical
namespace OM.NNN13
open CoordinateTensor OM.NNN.Raw NNN11.Network
open NNN11.ExtractionAB (X)
open Foundations.PairUnitExponents Foundations.OrientationTransport Lib.E.RectangularSpectrum
set_option maxHeartbeats 5000000
set_option maxRecDepth 10000

def rawTotal (n : Fin 3 → ℕ) : ℝ := n 0 + n 1 + n 2
def rawDegree (n : Fin 3 → ℕ) (last i : Fin 3) : ℝ :=
  rawTotal n - if i = last then (n i : ℝ) else 0
def rawSupplyA (n : Fin 3 → ℕ) (x : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![(n 1 : ℝ) * x 2, (n 2 : ℝ) * x 0, (n 0 : ℝ) * x 1]
def rawSupplyB (n : Fin 3 → ℕ) (x : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![(n 2 : ℝ) * x 1, (n 0 : ℝ) * x 2, (n 1 : ℝ) * x 0]
def rawCycles (n : Fin 3 → ℕ) (q : Fin 3 → Alphabet) (x : Fin 3 → ℝ) (i : Fin 3) : ℝ :=
  capacity (q i).k (rawSupplyA n x i) (rawSupplyB n x i)
def rawSlope (t : Fin 3 → ℝ) (C : Fin 3 → Fin 3 → ℝ) (i : Fin 3) : ℝ := t i - cross (C i) i
def rawGap (n : Fin 3 → ℕ) (last : Fin 3) (q : Fin 3 → Alphabet)
    (t : Fin 3 → ℝ) (C : Fin 3 → Fin 3 → ℝ) (F : ℝ) (x : Fin 3 → ℝ) : ℝ :=
  rawTotal n * F - ∑ i, t i * (rawSupplyA n x i + rawSupplyB n x i) +
    ∑ i, t i * (rawDegree n last i * (F - plane (C i) x) -
      rawCycles n q x i * logMoment (q i).q (q i).d (rawSlope t C i))

lemma rawDegree_zero (n : Fin 3 → ℕ) (i : Fin 3) :
    rawDegree n 0 i = groupDegrees (n 0) (n 1) (n 2) i := by
  fin_cases i <;> norm_num [rawDegree, rawTotal, groupDegrees, Matrix.cons_val_two] <;> ring

lemma rawHead_eq (n : Fin 3 → ℕ) (x y z : ℕ) (i : Fin 3) :
    rawSupplyA n ![x,y,z] i + rawSupplyB n ![x,y,z] i =
      (NNN11.bondLog (n 0) (n 1) (n 2) x y z i : ℝ) := by
  fin_cases i <;> simp [rawSupplyA, rawSupplyB, NNN11.bondLog, Matrix.cons_val_two] <;> ring

theorem packed_step_zero (φ : PolMul.Spectral ℂ) (n : Fin 3 → ℕ) (q : Fin 3 → Alphabet)
    (C : Fin 3 → Fin 3 → ℝ) (t : Fin 3 → ℝ) (F ε : ℝ) (hε : 0 ≤ ε)
    (hb : ∀ i, AffineBound φ (fun j => C i j + ε))
    (ht : ∀ i, t i ∈ Set.Icc (0 : ℝ) 1) (htsum : ∑ i, t i ≤ 9 / 4)
    (hθ : ∀ i, theta φ i ≤ t i) (hD : ∀ i, rawSlope t C i ≤ 0)
    (ha : 43 ≤ n 0) (hm : 0 < n 1 + n 2)
    {x y z : ℕ} (hbase : ∀ i, F ≤ plane (C i) ![x,y,z])
    (hgap : 0 ≤ rawGap n 0 q t C F ![x,y,z])
    (T : Tensor ℂ (X x) (X y) (X z)) :
    value φ T ≤ 2 * (2 : ℝ) ^ (F + gamma * ε * (x + y + z : ℝ)) := by
  obtain ⟨N0, ⟨L0⟩, hN0, hE0⟩ := AllPositions.exists_packed_layout
    (A := Fin (n 1)) (B := Fin (n 2)) (x := y) (y := z)
    (q 0).differenceSet (q 0).parameters.1 (q 0).parameters.2.1
    (q 0).counts.1 (q 0).counts.2
  obtain ⟨N1, ⟨L1⟩, hN1, hE1⟩ := AllPositions.exists_packed_layout
    (A := Fin (n 2)) (B := Fin (n 0)) (x := z) (y := x)
    (q 1).differenceSet (q 1).parameters.1 (q 1).parameters.2.1
    (q 1).counts.1 (q 1).counts.2
  obtain ⟨N2, ⟨L2⟩, hN2, hE2⟩ := AllPositions.exists_packed_layout
    (A := Fin (n 0)) (B := Fin (n 1)) (x := x) (y := y)
    (q 2).differenceSet (q 2).parameters.1 (q 2).parameters.2.1
    (q 2).counts.1 (q 2).counts.2
  let N : Fin 3 → ℕ := ![N0,N1,N2]
  let E := rawCycles n q ![(x : ℝ),y,z]
  let M := fun i => groupIntercepts (n 0) (n 1) (n 2) C ![(x : ℝ),y,z] i +
    E i * logMoment (q i).q (q i).d (rawSlope t C i)
  have hN (i : Fin 3) : (N i : ℝ) ≤ E i := by
    fin_cases i
    · simpa [N, E, rawCycles, rawSupplyA, rawSupplyB] using! hN0
    · simpa [N, E, rawCycles, rawSupplyA, rawSupplyB] using! hN1
    · simpa [N, E, rawCycles, rawSupplyA, rawSupplyB, Matrix.cons_val_two] using! hN2
  have hE (i : Fin 3) : E i ≤ N i + 2 := by
    fin_cases i
    · simpa [N, E, rawCycles, rawSupplyA, rawSupplyB] using! hE0.le
    · simpa [N, E, rawCycles, rawSupplyA, rawSupplyB] using! hE1.le
    · simpa [N, E, rawCycles, rawSupplyA, rawSupplyB, Matrix.cons_val_two] using! hE2.le
  apply combined_continuous_step (q := fun i => (q i).q) (d := fun i => (q i).d) (N := N)
    φ C F ε hε hb t ht htsum hθ L2 L0 L1 M E (rawSlope t C)
    (fun i => (q i).parameters.2.2.2) hN hE hD _ _ hbase _
    (by simpa using! ha) (by simpa using! hm) T
  · intro i
    fin_cases i <;> dsimp [groupSlopes, rawSlope, cross] <;> ring
  · intro i
    simp only [Fintype.card_fin]
    rfl
  · simp only [Fintype.card_fin]
    simp only [rawGap, rawDegree_zero, rawHead_eq] at hgap
    dsimp [M, groupIntercepts, E]
    simp only [rawTotal, Fin.sum_univ_three, Nat.cast_add] at hgap ⊢
    nlinarith only [hgap]

def rotate {α : Type*} (v : Fin 3 → α) : Fin 3 → α := ![v 1, v 2, v 0]
def rotateRows (C : Fin 3 → Fin 3 → ℝ) : Fin 3 → Fin 3 → ℝ :=
  ![rotate (C 1), rotate (C 2), rotate (C 0)]

lemma plane_rotate (c x : Fin 3 → ℝ) : plane (rotate c) (rotate x) = plane c x := by
  dsimp [plane, rotate]
  ring

lemma rawGap_rotate (n : Fin 3 → ℕ) (q : Fin 3 → Alphabet)
    (t : Fin 3 → ℝ) (C : Fin 3 → Fin 3 → ℝ) (F : ℝ) (x : Fin 3 → ℝ) (i : Fin 3) :
    rawGap (rotate n) i (rotate q) (rotate t) (rotateRows C) F (rotate x) =
      rawGap n (rotate (fun j => j) i) q t C F x := by
  have h01 : (0 : Fin 3) ≠ 1 := by decide +kernel
  have h02 : (0 : Fin 3) ≠ 2 := by decide +kernel
  have h10 : (1 : Fin 3) ≠ 0 := by decide +kernel
  have h12 : (1 : Fin 3) ≠ 2 := by decide +kernel
  have h20 : (2 : Fin 3) ≠ 0 := by decide +kernel
  have h21 : (2 : Fin 3) ≠ 1 := by decide +kernel
  have h22 : (2 : Fin 3) = ⟨2, by decide +kernel⟩ := rfl
  fin_cases i <;>
    norm_num [rawGap, rawTotal, rawDegree, rawSupplyA, rawSupplyB, rawCycles, rawSlope,
      cross, rotateRows, rotate, Fin.sum_univ_three, plane,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, Nat.cast_add, reduceIte, sub_zero,
      h01, h02, h10, h12, h20, h21]
  all_goals
    simp only [if_pos h22, add_comm (C 1 2) (C 1 0), add_comm (C 2 1) (C 2 0)]
    ring

theorem affineBound_rotate (φ : PolMul.Spectral ℂ) (c : Fin 3 → ℝ) (hb : AffineBound φ c) :
    AffineBound (pullPoint (pullPoint φ (rot 1)) (rot 0)) (rotate c) := by
  intro v U
  have hh := hb ![v 2, v 0, v 1] (swap12 (swap02 U))
  have he1 := NNN11.value_swap12 φ (swap12 (swap02 U))
  have he2 := NNN11.value_swap02 (pullPoint φ (rot 1)) (swap02 U)
  change value (pullPoint φ (rot 1)) (swap02 U) = value φ (swap12 (swap02 U)) at he1
  change value (pullPoint (pullPoint φ (rot 1)) (rot 0)) U =
    value (pullPoint φ (rot 1)) (swap02 U) at he2
  rw [← he1, ← he2] at hh
  convert! hh using 1
  congr 1
  dsimp [plane, rotate]
  ring

lemma rotate_add_constant (c : Fin 3 → ℝ) (s : ℝ) :
    rotate (fun i => c i + s) = fun i => rotate c i + s := by
  funext i
  fin_cases i <;> rfl

lemma rawSlope_rotate (t : Fin 3 → ℝ) (C : Fin 3 → Fin 3 → ℝ) (i : Fin 3) :
    rawSlope (rotate t) (rotateRows C) i = rotate (rawSlope t C) i := by
  fin_cases i <;> dsimp [rawSlope, cross, rotateRows, rotate] <;> ring

/-- All three last-bond choices share the same finite inequality. -/
def PackedStepAt (last : Fin 3) : Prop :=
  ∀ (φ : PolMul.Spectral ℂ) (n : Fin 3 → ℕ) (q : Fin 3 → Alphabet)
    (C : Fin 3 → Fin 3 → ℝ) (t : Fin 3 → ℝ) (F ε : ℝ), 0 ≤ ε →
    (∀ i, AffineBound φ (fun j => C i j + ε)) →
    (∀ i, t i ∈ Set.Icc (0 : ℝ) 1) → (∑ i, t i ≤ 9 / 4) →
    (∀ i, theta φ i ≤ t i) → (∀ i, rawSlope t C i ≤ 0) →
    (∀ i, 43 ≤ n i) → ∀ (v : NNN12.Shape),
    (∀ i, F ≤ plane (C i) (fun j => (v j : ℝ))) →
    0 ≤ rawGap n last q t C F (fun j => (v j : ℝ)) →
    ∀ (U : NNN12.DyadicTensor v),
      value φ U ≤ 2 * (2 : ℝ) ^ (F + gamma * ε * NNN12.volume v)

theorem packedStepAt_zero : PackedStepAt 0 := by
  intro φ n q C t F ε hε hb ht htsum hθ hD hn v hbase hgap U
  have hv : (fun j => (v j : ℝ)) = ![(v 0 : ℝ),v 1,v 2] := by
    funext j
    fin_cases j <;> rfl
  rw [hv] at hbase hgap
  exact packed_step_zero φ n q C t F ε hε hb ht htsum hθ hD (hn 0)
    (by have := hn 1; omega) hbase hgap U

theorem packedStepAt_rotate (i : Fin 3) (h : PackedStepAt i) :
    PackedStepAt (rotate (fun j => j) i) := by
  intro φ n q C t F ε hε hb ht htsum hθ hD hn v hbase hgap U
  let ψ := pullPoint (pullPoint φ (rot 1)) (rot 0)
  have hb' (j : Fin 3) : AffineBound ψ (fun k => rotateRows C j k + ε) := by
    fin_cases j
    · simpa only [rotate_add_constant] using! affineBound_rotate φ _ (hb 1)
    · simpa only [rotate_add_constant] using! affineBound_rotate φ _ (hb 2)
    · simpa only [rotate_add_constant] using! affineBound_rotate φ _ (hb 0)
  have ht' (j) : rotate t j ∈ Set.Icc (0 : ℝ) 1 := by
    fin_cases j <;> first | exact ht 1 | exact ht 2 | exact ht 0
  have hsum' : ∑ j, rotate t j ≤ 9 / 4 := by
    rw [Fin.sum_univ_three] at htsum ⊢
    change t 1 + t 2 + t 0 ≤ 9 / 4
    linarith
  have hθ' (j) : theta ψ j ≤ rotate t j := by
    simp only [ψ, theta_legReindex]
    fin_cases j <;> first | exact hθ 1 | exact hθ 2 | exact hθ 0
  have hD' (j) : rawSlope (rotate t) (rotateRows C) j ≤ 0 := by
    rw [rawSlope_rotate]
    fin_cases j <;> first | exact hD 1 | exact hD 2 | exact hD 0
  have hn' (j) : 43 ≤ rotate n j := by
    fin_cases j <;> first | exact hn 1 | exact hn 2 | exact hn 0
  have hbase' (j) : F ≤ plane (rotateRows C j) (fun k => ((rotate v k : ℕ) : ℝ)) := by
    change F ≤ plane (rotateRows C j) (rotate (fun k => (v k : ℝ)))
    fin_cases j
    · simpa only [← plane_rotate (C 1) (fun k => (v k : ℝ))] using! hbase 1
    · simpa only [← plane_rotate (C 2) (fun k => (v k : ℝ))] using! hbase 2
    · simpa only [← plane_rotate (C 0) (fun k => (v k : ℝ))] using! hbase 0
  have hgap' : 0 ≤ rawGap (rotate n) i (rotate q) (rotate t) (rotateRows C) F
      (fun k => ((rotate v k : ℕ) : ℝ)) := by
    change 0 ≤ rawGap (rotate n) i (rotate q) (rotate t) (rotateRows C) F
      (rotate (fun k => (v k : ℝ)))
    rw [rawGap_rotate]
    exact hgap
  have hh := h ψ (rotate n) (rotate q) (rotateRows C) (rotate t) F ε hε hb' ht'
    hsum' hθ' hD' hn' (rotate v) hbase' hgap' (swap02 (swap12 U))
  rw [NNN11.value_swap02, NNN11.value_swap12] at hh
  have hv : NNN12.volume (rotate v) = NNN12.volume v := by
    dsimp [NNN12.volume, rotate]
    ring
  rwa [hv] at hh

theorem packedStepAt (i : Fin 3) : PackedStepAt i := by
  fin_cases i
  · exact packedStepAt_zero
  · exact packedStepAt_rotate 0 packedStepAt_zero
  · exact packedStepAt_rotate 1 (packedStepAt_rotate 0 packedStepAt_zero)

end OM.NNN13
