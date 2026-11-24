import Lib.OM.NNN18.SourceH
import Lib.OM.NNN13.PackedStep

/-!
# The network steps (nodes SRC, ORDSTEP; the statement of PACKSTEP) -/

noncomputable section
open scoped BigOperators
open CoordinateTensor OM.NNN.Raw
open OM.NNN12 (Shape DyadicTensor volume)
namespace OM.NNN18

def copies (K : ℕ) (h : Fin 3) (v : Fin 3 → ℕ) : Fin 3 → ℕ :=
  fun u => K * (if u = h then 6 else 5) * v u

lemma logMoment_eleven (D : ℝ) : NNN13.logMoment 11 3 D = ell D := by
  simp only [NNN13.logMoment, ell]
  norm_num

lemma capacity_scale (a b p : ℝ) (hp : 0 ≤ p) :
    NNN13.capacity 5 (a * p) (b * p) = NNN13.capacity 5 a b * p := by
  simp only [NNN13.capacity]
  rw [min_mul_of_nonneg _ _ hp, min_mul_of_nonneg _ _ hp]
  congr 1
  · ring
  · congr 1 <;> ring

lemma cap55 (K va vb : ℝ) (hp : 0 ≤ K * va * vb) :
    NNN13.capacity 5 (K * 5 * va * vb) (K * 5 * vb * va) = K * (10 / 11) * (va * vb) := by
  rw [show K * 5 * va * vb = 5 * (K * va * vb) by ring, show K * 5 * vb * va = 5 * (K * va * vb) by ring,
    capacity_scale _ _ _ hp]
  norm_num [NNN13.capacity]; ring

lemma cap56 (K va vb : ℝ) (hp : 0 ≤ K * va * vb) :
    NNN13.capacity 5 (K * 5 * va * vb) (K * 6 * vb * va) = K * (va * vb) := by
  rw [show K * 5 * va * vb = 5 * (K * va * vb) by ring, show K * 6 * vb * va = 6 * (K * va * vb) by ring,
    capacity_scale _ _ _ hp]
  norm_num [NNN13.capacity]; ring

lemma cap65 (K va vb : ℝ) (hp : 0 ≤ K * va * vb) :
    NNN13.capacity 5 (K * 6 * va * vb) (K * 5 * vb * va) = K * (va * vb) := by
  rw [show K * 6 * va * vb = 6 * (K * va * vb) by ring, show K * 5 * vb * va = 5 * (K * va * vb) by ring,
    capacity_scale _ _ _ hp]
  norm_num [NNN13.capacity]; ring

lemma rawCycles_copies (K : ℕ) (h i : Fin 3) (v : Fin 3 → ℕ) :
    NNN13.rawCycles (copies K h v) (fun _ => NNN13.Alphabet.eleven) (fun j => (v j : ℝ)) i =
      K * nu h i * pp (fun j => (v j : ℝ)) i := by
  have hp : ∀ a b : ℕ, (0 : ℝ) ≤ (K : ℝ) * a * b := fun a b => by positivity
  fin_cases h <;> fin_cases i <;>
    simp [NNN13.rawCycles, NNN13.rawSupplyA, NNN13.rawSupplyB, copies, nu, pp, NNN13.Alphabet.k] <;>
    first
    | (rw [cap55 _ _ _ (hp _ _)]; try ring)
    | (rw [cap56 _ _ _ (hp _ _)]; try ring)
    | (rw [cap65 _ _ _ (hp _ _)]; try ring)

theorem rawGap_copies (K : ℕ) (h : Fin 3) (v : Fin 3 → ℕ) (t : Fin 3 → ℝ)
    (C : Fin 3 → Fin 3 → ℝ) (F : ℝ) :
    NNN13.rawGap (copies K h v) h (fun _ => NNN13.Alphabet.eleven) t C F (fun j => (v j : ℝ)) =
      K * form h t (fun _ => 1) C (fun i => ell (NNN13.rawSlope t C i)) F (fun j => (v j : ℝ)) := by
  simp only [NNN13.rawGap, rawCycles_copies, NNN13.Alphabet.q, NNN13.Alphabet.d]
  simp only [show ((11 : ℕ) : ℝ) = 11 by norm_num, show ((3 : ℕ) : ℝ) = 3 by norm_num,
    logMoment_eleven]
  fin_cases h <;>
  · simp [form, Fin.sum_univ_three, own, nu, pp, dot, NNN13.plane, NNN13.rawTotal, NNN13.rawDegree,
      NNN13.rawSupplyA, NNN13.rawSupplyB, copies]
    ring

theorem ord_step (φ : PolMul.Spectral ℂ) (h : Fin 3) (C : Fin 3 → Fin 3 → ℝ) (t : Fin 3 → ℝ)
    (F : ℝ) (hb : ∀ i, NNN13.AffineBound φ (C i)) (ht : ∀ i, t i ∈ Set.Icc (0 : ℝ) 1)
    (hts : ∑ i, t i ≤ 9 / 4) (hθ : ∀ i, Foundations.PairUnitExponents.theta φ i ≤ t i)
    (hD : ∀ i, NNN13.rawSlope t C i ≤ 0) (v : Shape) (hv : ∀ i, 1 ≤ v i)
    (hbase : ∀ i, F ≤ NNN13.plane (C i) (fun j => (v j : ℝ)))
    (hgap : 0 ≤ form h t (fun _ => 1) C (fun i => ell (NNN13.rawSlope t C i)) F
      (fun j => (v j : ℝ)))
    (U : DyadicTensor v) : value φ U ≤ 2 * (2 : ℝ) ^ F := by
  have hn : ∀ i, 43 ≤ copies 43 h v i := by
    intro i
    simp only [copies]
    have := hv i
    split_ifs <;> nlinarith
  have hstep := NNN13.packedStepAt h φ (copies 43 h v) (fun _ => NNN13.Alphabet.eleven) C t F 0
    le_rfl (by simpa using hb) ht hts hθ hD hn v hbase
    (by rw [rawGap_copies]; exact mul_nonneg (by norm_num) hgap) U
  simpa using hstep

def packedGap (n : Fin 3 → ℕ) (last : Fin 3) (t β : Fin 3 → ℝ) (C : Fin 3 → Fin 3 → ℝ)
    (F : ℝ) (x : Fin 3 → ℝ) : ℝ :=
  NNN13.rawTotal n * F - ∑ i, t i * (NNN13.rawSupplyA n x i + NNN13.rawSupplyB n x i)
    + ∑ i, t i / β i * NNN13.rawDegree n last i * (F - NNN13.plane (C i) x)
    - ∑ i, t i * NNN13.rawCycles n (fun _ => NNN13.Alphabet.eleven) x i
        * ell ((t i - NNN13.cross (C i) i) / β i)

theorem packedGap_copies (K : ℕ) (h : Fin 3) (v : Fin 3 → ℕ) (t β : Fin 3 → ℝ)
    (C : Fin 3 → Fin 3 → ℝ) (F : ℝ) :
    packedGap (copies K h v) h t β C F (fun j => (v j : ℝ)) =
      K * form h t β C (fun i => ell ((t i - NNN13.cross (C i) i) / β i)) F (fun j => (v j : ℝ)) := by
  simp only [packedGap, rawCycles_copies]
  fin_cases h <;>
  · simp [form, Fin.sum_univ_three, own, nu, pp, dot, NNN13.plane, NNN13.rawTotal, NNN13.rawDegree,
      NNN13.rawSupplyA, NNN13.rawSupplyB, copies]
    ring

def TriangleStep : Prop :=
  ∀ (last : Fin 3) (φ : PolMul.Spectral ℂ) (o : Fin 3 → ℕ) (C : Fin 3 → Fin 3 → ℝ)
    (t β : Fin 3 → ℝ) (F : ℝ),
    (∀ i, NNN13.AffineBound φ (C i)) → (∀ i, t i ∈ Set.Icc (0 : ℝ) 1) → (∑ i, t i ≤ 9 / 4) →
    (∀ i, Foundations.PairUnitExponents.theta φ i ≤ t i) → β last = 1 → (∀ i, 0 < β i) →
    (∀ i, i ≠ last → (t i + NNN13.cross (C i) i) / 2 ≤ β i ∧ β i ≤ 1) →
    (∀ i, NNN13.rawSlope t C i ≤ 0) → (∀ i, 1 ≤ o i) →
    ∀ (v : Shape), (∀ i, F ≤ NNN13.plane (C i) (fun j => (v j : ℝ))) →
    0 ≤ packedGap o last t β C F (fun j => (v j : ℝ)) →
    ∀ U : DyadicTensor v, value φ U ≤ 2 * (2 : ℝ) ^ F

lemma mapTensor_indicator {I J K A B C : Type} [Fintype I] [Fintype J] [Fintype K]
    [DecidableEq I] [DecidableEq J] [DecidableEq K]
    (e0 : A → I) (e1 : B → J) (e2 : C → K) (S : Tensor ℂ I J K) :
    mapTensor (fun a i => if e0 a = i then (1 : ℂ) else 0) (fun b j => if e1 b = j then (1 : ℂ) else 0)
      (fun c k => if e2 c = k then (1 : ℂ) else 0) S = fun a b c => S (e0 a) (e1 b) (e2 c) := by
  funext a b c
  simp only [mapTensor]
  rw [Finset.sum_eq_single (e0 a)]
  · rw [Finset.sum_eq_single (e1 b)]
    · rw [Finset.sum_eq_single (e2 c)]
      · simp
      · intro k _ hk; simp [Ne.symm hk]
      · simp
    · intro j _ hj; simp [Ne.symm hj]
    · simp
  · intro i _ hi; simp [Ne.symm hi]
  · simp

/-- Zero padding: a dyadic tensor is a restriction of one of any larger shape. -/
theorem exists_pad (φ : PolMul.Spectral ℂ) {v w : Shape} (hvw : ∀ i, v i ≤ w i)
    (U : DyadicTensor v) : ∃ U' : DyadicTensor w, value φ U ≤ value φ U' := by
  have hc : ∀ i, Fintype.card (NNN8.BinaryWord (v i)) ≤ Fintype.card (NNN8.BinaryWord (w i)) := by
    intro i; simp only [NNN8.binary_word_card]; exact Nat.pow_le_pow_right (by norm_num) (hvw i)
  obtain ⟨e0⟩ := Function.Embedding.nonempty_of_card_le (hc 0)
  obtain ⟨e1⟩ := Function.Embedding.nonempty_of_card_le (hc 1)
  obtain ⟨e2⟩ := Function.Embedding.nonempty_of_card_le (hc 2)
  let U' : DyadicTensor w := fun i j k =>
    Function.extend e0 (fun a => Function.extend e1 (fun b => Function.extend e2
      (fun c => U a b c) 0 k) 0 j) 0 i
  refine ⟨U', ?_⟩
  have hU : U = fun a b c => U' (e0 a) (e1 b) (e2 c) := by
    funext a b c
    simp only [U', e0.injective.extend_apply, e1.injective.extend_apply, e2.injective.extend_apply]
  rw [hU, ← mapTensor_indicator]
  exact value_map_le φ U' _ _ _

end OM.NNN18
