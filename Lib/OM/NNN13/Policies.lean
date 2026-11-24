import Lib.OM.NNN13.Geometry
import Lib.OM.NNN13.Majorants
import Lib.OM.NNN13.Moments
import Lib.OM.NNN12.QuadraticNumerics
import Lib.OM.NNN12.Cyclic

/-! A finite ownership and alphabet menu, and its exact scalar source gap.
The tensor-level justification of a policy is separate from its scalar
certificate. Every residual price is one of the six lifted global planes. -/
noncomputable section
open scoped BigOperators Classical
namespace OM.NNN13
set_option maxHeartbeats 4000000

inductive Alphabet where
  | three | seven | eleven | nineteen
  deriving DecidableEq, Fintype

def Alphabet.q : Alphabet → ℕ
  | .three => 3 | .seven => 7 | .eleven => 11 | .nineteen => 19
def Alphabet.k : Alphabet → ℕ
  | .three => 1 | .seven => 3 | .eleven => 5 | .nineteen => 9
def Alphabet.d : Alphabet → ℕ
  | .three => 1 | .seven => 2 | .eleven => 3 | .nineteen => 5

instance (q : Alphabet) : Fact q.q.Prime := by
  cases q <;> exact ⟨by decide +kernel⟩

lemma Alphabet.parameters (q : Alphabet) :
    q.q = 2 * q.k + 1 ∧ 0 < q.k ∧ 0 ≤ q.d ∧ q.q ≤ 19 := by
  cases q <;> decide +kernel

def Alphabet.differenceSet (q : Alphabet) : Finset (ZMod q.q) :=
  match q with
  | .three => NNN12.Cyclic.d3
  | .seven => NNN11.fano
  | .eleven => NNN12.Cyclic.d11
  | .nineteen => NNN12.Cyclic.d19

lemma Alphabet.counts (q : Alphabet) : q.differenceSet.card = q.k ∧
    NNN12.Cyclic.ShiftCounts q.differenceSet q.d := by
  cases q
  · exact NNN12.Cyclic.d3_counts
  · exact NNN12.Cyclic.d7_counts
  · exact NNN12.Cyclic.d11_counts
  · exact NNN12.Cyclic.d19_counts

def momentUpper (q : Alphabet) (D : ℝ) : ℝ :=
  match q with
  | .three => NNN12.momentUpper3 D
  | .seven => -NNN12.capacityLower7 (D / 2 + 9 / 8)
  | .eleven => -NNN12.capacityLower11 (D / 2 + 9 / 8)
  | .nineteen => NNN12.momentUpper19 D

theorem logMoment_le_upper (q : Alphabet) (D : ℝ) :
    logMoment q.q q.d D ≤ momentUpper q D := by
  cases q
  · have h := NNN12.logMoment3_le_quadratic D
    norm_num [Alphabet.q, Alphabet.d, logMoment, NNN12.logMoment3, momentUpper] at h ⊢
    exact h
  · have h := NNN12.capacityLower7_le (D / 2 + 9 / 8)
    have he : logMoment 7 2 D = -NNN11.codeK (D / 2 + 9 / 8) := by
      norm_num [logMoment, NNN11.codeK]
      ring_nf
    change logMoment 7 2 D ≤ -NNN12.capacityLower7 (D / 2 + 9 / 8)
    rw [he]
    linarith
  · have h := NNN12.capacityLower11_le (D / 2 + 9 / 8)
    have he : logMoment 11 3 D = -NNN12.rawCapacity 11 3 (D / 2 + 9 / 8) := by
      norm_num [logMoment, NNN12.rawCapacity]
      ring_nf
    change logMoment 11 3 D ≤ -NNN12.capacityLower11 (D / 2 + 9 / 8)
    rw [he]
    linarith
  · have h := NNN12.logMoment19_le_quadratic D
    norm_num [Alphabet.q, Alphabet.d, logMoment, NNN12.logMoment19, momentUpper] at h ⊢
    exact h

abbrev Price := Bool × Fin 3

def price (r z : ℝ) (p : Price) (j : Fin 3) : ℝ :=
  (if p.1 then candidateCoefficients r z p.2 j else starCoefficients (profile r z) p.2 j) + lift

lemma potential_le_price (r z : ℝ) (x : Fin 3 → ℝ) (p : Price) :
    potential r z x ≤ plane (price r z p) x := by
  rcases p with ⟨b, i⟩
  cases b
  · exact potential_le_star r z x i
  · exact potential_le_candidate r z x i

theorem price_affineBound_with_error (φ : PolMul.Spectral ℂ) (r z ε : ℝ)
    (hb : ∀ (v : NNN12.Shape) (U : NNN12.DyadicTensor v),
      OM.NNN.Raw.value φ U ≤ (2 : ℝ) ^ (target r z v + ε * NNN12.volume v)) (p : Price) :
    AffineBound φ (fun j => price r z p j + ε) := by
  rcases p with ⟨b, i⟩
  cases b
  · exact star_affineBound_with_error φ r z ε hb i
  · exact candidate_affineBound_with_error φ r z ε hb i

def owners : Fin 10 → Fin 3 → ℕ :=
  ![![504,504,672], ![504,672,504], ![525,525,630], ![525,630,525],
    ![540,540,600], ![540,600,540], ![560,560,560], ![600,540,540],
    ![630,525,525], ![672,504,504]]

lemma owners_sum (o : Fin 10) : owners o 0 + owners o 1 + owners o 2 = 1680 := by
  revert o
  decide +kernel
lemma owners_large (o : Fin 10) (i : Fin 3) : 504 ≤ owners o i := by
  revert o i
  decide +kernel

def ownership (o : Fin 10) (i : Fin 3) : ℚ := owners o i / 1680

structure Policy where
  owner : Fin 10
  last : Fin 3
  alphabet : Fin 3 → Alphabet
  residual : Fin 3 → Price
  deriving DecidableEq

def Policy.mass (p : Policy) (i : Fin 3) : ℚ :=
  if i = p.last then 1 - ownership p.owner i else 1

def cross (c : Fin 3 → ℝ) : Fin 3 → ℝ := ![c 1 + c 2, c 0 + c 2, c 0 + c 1]
def Policy.slope (p : Policy) (r z : ℝ) (i : Fin 3) : ℝ :=
  profile r z i - cross (price r z (p.residual i)) i

lemma price_slope_nonpos {r z : ℝ} (hr : r ∈ Set.Icc 0 radius) (hz : z ∈ Set.Icc 0 r)
    (p : Price) (i : Fin 3) : profile r z i - cross (price r z p) i ≤ 0 := by
  rcases p with ⟨b, j⟩
  cases b <;> fin_cases i <;> fin_cases j <;>
    norm_num [price, cross, profile, deviation, candidateCoefficients, starCoefficients,
      a, b, tiltA, tiltB, tiltG, tiltE, lift, radius, Matrix.cons_val_two] at hr ⊢ <;>
    linarith [hr.1, hr.2, hz.1, hz.2]

def Policy.supplyA (p : Policy) (x : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![(ownership p.owner 2 : ℝ) * x 1, (ownership p.owner 0 : ℝ) * x 2,
    (ownership p.owner 1 : ℝ) * x 0]
def Policy.supplyB (p : Policy) (x : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![(ownership p.owner 1 : ℝ) * x 2, (ownership p.owner 2 : ℝ) * x 0,
    (ownership p.owner 0 : ℝ) * x 1]
def Policy.cycles (p : Policy) (x : Fin 3 → ℝ) (i : Fin 3) : ℝ :=
  capacity (p.alphabet i).k (p.supplyA x i) (p.supplyB x i)

def Policy.gap (p : Policy) (r z : ℝ) (c x : Fin 3 → ℝ) : ℝ :=
  plane c x - ∑ i, (ownership p.owner i : ℝ) * plane (starCoefficients (profile r z) i) x +
    ∑ i, profile r z i * ((p.mass i : ℝ) * (plane c x - plane (price r z (p.residual i)) x) -
      p.cycles x i * logMoment (p.alphabet i).q (p.alphabet i).d (p.slope r z i))

def Policy.upperGap (p : Policy) (r z : ℝ) (c x : Fin 3 → ℝ) : ℝ :=
  plane c x - ∑ i, (ownership p.owner i : ℝ) * plane (starCoefficients (profile r z) i) x +
    ∑ i, profile r z i * ((p.mass i : ℝ) * (plane c x - plane (price r z (p.residual i)) x) -
      p.cycles x i * momentUpper (p.alphabet i) (p.slope r z i))

lemma ownership_nonneg (o : Fin 10) (i : Fin 3) : (0 : ℝ) ≤ ownership o i := by
  dsimp [ownership]
  positivity

lemma Policy.cycles_nonneg (p : Policy) {x : Fin 3 → ℝ} (hx : ∀ i, 0 ≤ x i) (i : Fin 3) :
    0 ≤ p.cycles x i := by
  apply capacity_nonneg (by exact_mod_cast (p.alphabet i).parameters.2.1)
  · fin_cases i <;> exact mul_nonneg (ownership_nonneg _ _) (hx _)
  · fin_cases i <;> exact mul_nonneg (ownership_nonneg _ _) (hx _)

lemma Policy.upperGap_le (p : Policy) {r z : ℝ} (hr : r ∈ Set.Icc 0 radius)
    (hz : z ∈ Set.Icc 0 r) (c : Fin 3 → ℝ) {x : Fin 3 → ℝ} (hx : ∀ i, 0 ≤ x i) :
    p.upperGap r z c x ≤ p.gap r z c x := by
  unfold upperGap gap
  gcongr with i
  · exact (profile_box hr hz i).1.trans' (by norm_num)
  · exact p.cycles_nonneg hx i
  · exact logMoment_le_upper _ _

end OM.NNN13
