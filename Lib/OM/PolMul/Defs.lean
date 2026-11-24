/- Adapted from PolMul/Defs.lean of an earlier formalisation
   (commit 51c6e6b6e8b8d7226c6a828dba618ae1de5b5f8a).
   Amanov, van den Berg and Zuiddam (2026),
   “Multiplying matrices via polynomials: exposition and barriers”.
   Uses Foundations tensor definitions; declarations are renamed under OM. -/
import Foundations.Tensors.Semicontinuity.SpectralPointExtension
import Foundations.Tensors.Semicontinuity.TensorRank
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.RingTheory.Polynomial.Basic

/-!
# Definitions for polynomial multiplication tensors

This module contains only the definitions used throughout the formalisation of
“Multiplying matrices via polynomials: exposition and barriers”.
-/

namespace OM.PolMul

open AsymptoticSpectrumDuality
open Semicontinuity
open scoped BigOperators

universe u

variable {F : Type u} [Field F]

/-- Three-tensors over `F` in positive format `d`. -/
abbrev T3 (F : Type u) [Field F] (d : Fin 3 → ℕ+) := KTensor F d


/-- The three-leg format `(n₁,n₂,n₃)`. -/
def fmt (n₁ n₂ n₃ : ℕ+) : Fin 3 → ℕ+
  | 0 => n₁
  | 1 => n₂
  | 2 => n₃


/-- The unit tensor `⟨n⟩`, with value `1` exactly on the diagonal. -/
def unit (n : ℕ+) : T3 F (fmt n n n) :=
  fun idx => if ∀ i j : Fin 3, (idx i).val = (idx j).val then 1 else 0

-- NOTE: `Semicontinuity.unitTensor` has the same entries, but its constant
-- format `fun _ => n` is not definitionally `fmt n n n`; this definition keeps
-- the requested format without introducing a format-cast theorem.


example :
    unit (F := ℚ) 3
      (fun
        | 0 => (1 : Fin 3)
        | 1 => (1 : Fin 3)
        | 2 => (1 : Fin 3)) = 1 := by
  decide +kernel

/-- The matrix multiplication tensor `⟨n₁,n₂,n₃⟩`.  A coordinate decodes as
`(i,j),(j',k),(k',i')` using `finProdFinEquiv` and has value `1` exactly when
`i=i'`, `j=j'`, and `k=k'`. -/
def matMul (n₁ n₂ n₃ : ℕ+) :
    T3 F (fmt (n₁ * n₂) (n₂ * n₃) (n₃ * n₁)) := by
  intro idx
  let ij : Fin (n₁ : ℕ) × Fin (n₂ : ℕ) :=
    finProdFinEquiv.symm (by simpa [PNat.mul_coe] using! idx 0)
  let jk : Fin (n₂ : ℕ) × Fin (n₃ : ℕ) :=
    finProdFinEquiv.symm (by simpa [PNat.mul_coe] using! idx 1)
  let ki : Fin (n₃ : ℕ) × Fin (n₁ : ℕ) :=
    finProdFinEquiv.symm (by simpa [PNat.mul_coe] using! idx 2)
  exact if ij.2 = jk.1 ∧ jk.2 = ki.1 ∧ ki.2 = ij.1 then 1 else 0


example :
    matMul (F := ℚ) 2 3 4
      (fun
        | 0 => finProdFinEquiv ((1 : Fin 2), (2 : Fin 3))
        | 1 => finProdFinEquiv ((2 : Fin 3), (3 : Fin 4))
        | 2 => finProdFinEquiv ((3 : Fin 4), (1 : Fin 2))) = 1 := by
  decide +kernel

/-- The polynomial multiplication tensor `𝖯_{a,b}`: its `(i,j,l)` entry is
`1` iff the zero-based indices satisfy `l = i+j`. -/
def polmul (a b : ℕ+) : T3 F (fmt a b (a + b - 1)) :=
  fun idx => if (idx 2).val = (idx 0).val + (idx 1).val then 1 else 0


example :
    polmul (F := ℚ) 2 3
      (fun
        | 0 => (1 : Fin 2)
        | 1 => (1 : Fin 3)
        | 2 => (2 : Fin 4)) = 1 := by
  decide +kernel

/-- Direct sum of tensors, block-diagonal in all three legs.  This is `Semicontinuity.directSumTensor`. -/
noncomputable def dsum {dT dS : Fin 3 → ℕ+} (T : T3 F dT) (S : T3 F dS) :
    T3 F (fun i => dT i + dS i) :=
  directSumTensor T S


/-- Tensor (Kronecker) product with corresponding legs grouped.  This is `Semicontinuity.kroneckerTensor`. -/
noncomputable def kron {dT dS : Fin 3 → ℕ+} (T : T3 F dT) (S : T3 F dS) :
    T3 F (fun i => dT i * dS i) :=
  kroneckerTensor T S


/-- The `n`-fold Kronecker power `T^{⊗n}`.  The zeroth power is the unique
scalar-one tensor in format `d^0`; the successor case iterates `kron` and
transports its format along `pow_succ`. -/
noncomputable def kronPow {d : Fin 3 → ℕ+} (T : T3 F d) :
    (n : ℕ) → T3 F (fun i => (d i) ^ n) :=
  fun n => Nat.rec (motive := fun n => T3 F (fun i => (d i) ^ n))
    (fun _ => 1)
    (fun n prev idx =>
      kron prev T (fun i => Fin.cast (by simp [pow_succ]) (idx i)))
    n


scoped infixr:65 " ⊕ₜ " => OM.PolMul.dsum
scoped infixr:70 " ⊗ₜ " => OM.PolMul.kron

/-- Partial direct sum with the first leg shared, as witnessed by `h`.  The
second and third legs use matching left or right blocks, and mixed blocks are
zero. -/
noncomputable def pdsum {dT dS : Fin 3 → ℕ+}
    (T : T3 F dT) (S : T3 F dS) (h : dT 0 = dS 0) :
    T3 F (fmt (dT 0) (dT 1 + dS 1) (dT 2 + dS 2)) := by
  classical
  intro idx
  by_cases hv : (idx 1).val < (dT 1 : ℕ)
  · by_cases hw : (idx 2).val < (dT 2 : ℕ)
    · exact T (fun
        | 0 => Fin.cast (by simp [fmt]) (idx 0)
        | 1 => ⟨(idx 1).val, hv⟩
        | 2 => ⟨(idx 2).val, hw⟩)
    · exact 0
  · by_cases hw : (dT 2 : ℕ) ≤ (idx 2).val
    · exact S (fun
        | 0 => Fin.cast (congrArg (fun x : ℕ+ => (x : ℕ)) h) (idx 0)
        | 1 => ⟨(idx 1).val - (dT 1 : ℕ), by
            have hi := (idx 1).isLt
            simp only [fmt] at hi ⊢
            have hcoe := PNat.add_coe (dT 1) (dS 1)
            omega⟩
        | 2 => ⟨(idx 2).val - (dT 2 : ℕ), by
            have hi := (idx 2).isLt
            simp only [fmt] at hi ⊢
            have hcoe := PNat.add_coe (dT 2) (dS 2)
            omega⟩)
    · exact 0


scoped infixr:65 " ⊕ₓ " => OM.PolMul.pdsum

/-- The partial direct sum of a nonempty `Fin m`-indexed family, with the first
leg shared as witnessed by `h`.  `finSigmaFinEquiv` gives the consecutive-block
encodings of the second and third legs. -/
noncomputable def pdsumFamily {m : ℕ} (d : Fin m → Fin 3 → ℕ+) (n : ℕ+)
    (h : ∀ i, d i 0 = n) [NeZero m] (T : ∀ i, T3 F (d i)) :
    T3 F (fmt n
      ⟨∑ i : Fin m, (d i 1 : ℕ), by
        exact Finset.sum_pos (fun i _ => (d i 1).pos) Finset.univ_nonempty⟩
      ⟨∑ i : Fin m, (d i 2 : ℕ), by
        exact Finset.sum_pos (fun i _ => (d i 2).pos) Finset.univ_nonempty⟩) := by
  classical
  intro idx
  let iv : (i : Fin m) × Fin (d i 1 : ℕ) := finSigmaFinEquiv.symm (idx 1)
  let iw : (i : Fin m) × Fin (d i 2 : ℕ) := finSigmaFinEquiv.symm (idx 2)
  if hi : iv.1 = iw.1 then
    exact T iv.1 (fun
      | 0 => Fin.cast (congrArg (fun x : ℕ+ => (x : ℕ)) (h iv.1).symm) (idx 0)
      | 1 => iv.2
      | 2 => Fin.cast (by rw [hi]) iw.2)
  else
    exact 0


/-- The direct sum of a nonempty `Fin m`-indexed family, block-diagonal in all
three legs.  `finSigmaFinEquiv` gives the consecutive-block encodings. -/
noncomputable def dsumFamily {m : ℕ} (d : Fin m → Fin 3 → ℕ+) [NeZero m]
    (T : ∀ i, T3 F (d i)) :
    T3 F (fun j => ⟨∑ i : Fin m, (d i j : ℕ), by
      exact Finset.sum_pos (fun i _ => (d i j).pos) Finset.univ_nonempty⟩) := by
  classical
  intro idx
  let block : ∀ j : Fin 3, (i : Fin m) × Fin (d i j : ℕ) :=
    fun j => finSigmaFinEquiv.symm (idx j)
  if h : ∀ j, (block j).1 = (block 0).1 then
    exact T (block 0).1 (fun j => Fin.cast (by rw [h j]) (block j).2)
  else
    exact 0


example :
    dsumFamily (F := ℚ) (m := 2) (fun _ => fmt 1 1 1)
      (fun i _ => if i = 0 then 7 else 9)
        (fun | 0 => (1 : Fin 2) | 1 => (1 : Fin 2) | 2 => (1 : Fin 2)) = 9 := by
  decide +kernel

/-- A tensor with four prescribed blocks in the second and third legs, with
`Tᵢⱼ` in block row `i` and block column `j`. -/
noncomputable def block2 {n v₁ v₂ w₁ w₂ : ℕ+}
    (T₁₁ : T3 F (fmt n v₁ w₁)) (T₁₂ : T3 F (fmt n v₁ w₂))
    (T₂₁ : T3 F (fmt n v₂ w₁)) (T₂₂ : T3 F (fmt n v₂ w₂)) :
    T3 F (fmt n (v₁ + v₂) (w₁ + w₂)) := by
  classical
  intro idx
  by_cases hv : (idx 1).val < (v₁ : ℕ)
  · by_cases hw : (idx 2).val < (w₁ : ℕ)
    · exact T₁₁ (fun
        | 0 => idx 0
        | 1 => ⟨(idx 1).val, hv⟩
        | 2 => ⟨(idx 2).val, hw⟩)
    · exact T₁₂ (fun
        | 0 => idx 0
        | 1 => ⟨(idx 1).val, hv⟩
        | 2 => ⟨(idx 2).val - (w₁ : ℕ), by
            have hi := (idx 2).isLt
            simp only [fmt] at hi ⊢
            have hcoe := PNat.add_coe w₁ w₂
            omega⟩)
  · by_cases hw : (idx 2).val < (w₁ : ℕ)
    · exact T₂₁ (fun
        | 0 => idx 0
        | 1 => ⟨(idx 1).val - (v₁ : ℕ), by
            have hi := (idx 1).isLt
            simp only [fmt] at hi ⊢
            have hcoe := PNat.add_coe v₁ v₂
            omega⟩
        | 2 => ⟨(idx 2).val, hw⟩)
    · exact T₂₂ (fun
        | 0 => idx 0
        | 1 => ⟨(idx 1).val - (v₁ : ℕ), by
            have hi := (idx 1).isLt
            simp only [fmt] at hi ⊢
            have hcoe := PNat.add_coe v₁ v₂
            omega⟩
        | 2 => ⟨(idx 2).val - (w₁ : ℕ), by
            have hi := (idx 2).isLt
            simp only [fmt] at hi ⊢
            have hcoe := PNat.add_coe w₁ w₂
            omega⟩)


example :
    block2 (F := ℚ) (n := 1) (v₁ := 2) (v₂ := 1) (w₁ := 1) (w₂ := 2)
      (fun _ => 11) (fun _ => 12) (fun _ => 21) (fun _ => 22)
        (fun | 0 => (0 : Fin 1) | 1 => (1 : Fin 3) | 2 => (2 : Fin 3)) = 12 := by
  decide +kernel

/-- A tensor with nine prescribed blocks in the second and third legs, with
`Tᵢⱼ` in block row `i` and block column `j`. -/
noncomputable def block3 {n v₁ v₂ v₃ w₁ w₂ w₃ : ℕ+}
    (T₁₁ : T3 F (fmt n v₁ w₁)) (T₁₂ : T3 F (fmt n v₁ w₂))
    (T₁₃ : T3 F (fmt n v₁ w₃)) (T₂₁ : T3 F (fmt n v₂ w₁))
    (T₂₂ : T3 F (fmt n v₂ w₂)) (T₂₃ : T3 F (fmt n v₂ w₃))
    (T₃₁ : T3 F (fmt n v₃ w₁)) (T₃₂ : T3 F (fmt n v₃ w₂))
    (T₃₃ : T3 F (fmt n v₃ w₃)) :
    T3 F (fmt n (v₁ + v₂ + v₃) (w₁ + w₂ + w₃)) := by
  classical
  intro idx
  let split3 : {a b c : ℕ+} → Fin (a + b + c) →
      Sum (Fin a) (Sum (Fin b) (Fin c)) :=
    fun {a b c} x =>
      if h₁ : x.val < (a : ℕ) then
        Sum.inl ⟨x.val, h₁⟩
      else if h₂ : x.val < (a : ℕ) + (b : ℕ) then
        Sum.inr (Sum.inl ⟨x.val - (a : ℕ), by omega⟩)
      else
        Sum.inr (Sum.inr ⟨x.val - ((a : ℕ) + (b : ℕ)), by
          have hx := x.isLt
          have hab := PNat.add_coe a b
          have habc := PNat.add_coe (a + b) c
          omega⟩)
  let row := split3 (a := v₁) (b := v₂) (c := v₃) (idx 1)
  let col := split3 (a := w₁) (b := w₂) (c := w₃) (idx 2)
  exact match row, col with
  | Sum.inl i, Sum.inl j => T₁₁ (fun | 0 => idx 0 | 1 => i | 2 => j)
  | Sum.inl i, Sum.inr (Sum.inl j) => T₁₂ (fun | 0 => idx 0 | 1 => i | 2 => j)
  | Sum.inl i, Sum.inr (Sum.inr j) => T₁₃ (fun | 0 => idx 0 | 1 => i | 2 => j)
  | Sum.inr (Sum.inl i), Sum.inl j => T₂₁ (fun | 0 => idx 0 | 1 => i | 2 => j)
  | Sum.inr (Sum.inl i), Sum.inr (Sum.inl j) =>
      T₂₂ (fun | 0 => idx 0 | 1 => i | 2 => j)
  | Sum.inr (Sum.inl i), Sum.inr (Sum.inr j) =>
      T₂₃ (fun | 0 => idx 0 | 1 => i | 2 => j)
  | Sum.inr (Sum.inr i), Sum.inl j => T₃₁ (fun | 0 => idx 0 | 1 => i | 2 => j)
  | Sum.inr (Sum.inr i), Sum.inr (Sum.inl j) =>
      T₃₂ (fun | 0 => idx 0 | 1 => i | 2 => j)
  | Sum.inr (Sum.inr i), Sum.inr (Sum.inr j) =>
      T₃₃ (fun | 0 => idx 0 | 1 => i | 2 => j)


/-- Permute tensor legs so that leg `i` of `T` becomes leg `π i` of the result.
Thus the output format is `d ∘ π.symm`.  This reuses
`Semicontinuity.KTensor.legReindex` with `π.symm`. -/
def perm (π : Equiv.Perm (Fin 3)) {d : Fin 3 → ℕ+} (T : T3 F d) :
    T3 F (d ∘ π.symm) :=
  KTensor.legReindex π.symm T


/-- Swap the second and third legs. -/
def swap23 {d : Fin 3 → ℕ+} (T : T3 F d) :
    T3 F (d ∘ (Equiv.swap (1 : Fin 3) 2).symm) :=
  perm (Equiv.swap (1 : Fin 3) 2) T


/-- Swap the second and third legs while retaining an explicit `fmt` output
format. -/
def swap23' {n v w : ℕ+} (T : T3 F (fmt n v w)) : T3 F (fmt n w v) :=
  fun idx => T (fun
    | 0 => idx 0
    | 1 => idx 2
    | 2 => idx 1)


/-- Isomorphism of tensors, the paper's `≅`: `T` is the image of `S` under
leg matrices `A i` that are invertible, with inverses `B i`, in the restriction convention of
`Semicontinuity.Restricts` (`T idx = ∑ sidx, (∏ i, A i (idx i) (sidx i)) * S sidx`). -/
def Iso {dT dS : Fin 3 → ℕ+} (T : T3 F dT) (S : T3 F dS) : Prop :=
  ∃ (A : ∀ i : Fin 3, Matrix (Fin (dT i)) (Fin (dS i)) F)
    (B : ∀ i : Fin 3, Matrix (Fin (dS i)) (Fin (dT i)) F),
    (∀ i, A i * B i = 1) ∧ (∀ i, B i * A i = 1) ∧
    ∀ idx : ∀ i : Fin 3, Fin (dT i),
      T idx = ∑ sidx : (∀ i : Fin 3, Fin (dS i)), (∏ i : Fin 3, A i (idx i) (sidx i)) * S sidx


/-- Isomorphism fixing the shared first leg: as `Iso`, with the first-leg matrix equal to the
identity transported along `h : dT 0 = dS 0` (used for the partial direct sums of
Sections 3 and 4). -/
def Iso23 {dT dS : Fin 3 → ℕ+} (T : T3 F dT) (S : T3 F dS) (h : dT 0 = dS 0) : Prop :=
  ∃ (A : ∀ i : Fin 3, Matrix (Fin (dT i)) (Fin (dS i)) F)
    (B : ∀ i : Fin 3, Matrix (Fin (dS i)) (Fin (dT i)) F),
    (∀ i, A i * B i = 1) ∧ (∀ i, B i * A i = 1) ∧
    (∀ x y : Fin (dT 0),
      A 0 x (Fin.cast (congrArg (fun z : ℕ+ => (z : ℕ)) h) y) = if x = y then 1 else 0) ∧
    ∀ idx : ∀ i : Fin 3, Fin (dT i),
      T idx = ∑ sidx : (∀ i : Fin 3, Fin (dS i)), (∏ i : Fin 3, A i (idx i) (sidx i)) * S sidx


scoped infix:50 " ≅ₜ " => OM.PolMul.Iso

/-- Polynomial degeneration: `T ⊴ S` when polynomial leg maps send `S` to
`X^q T + X^(q+1) T₁ + ... + X^(q+d) T_d`. -/
def Degen {dT dS : Fin 3 → ℕ+} (T : T3 F dT) (S : T3 F dS) : Prop :=
  ∃ q e : ℕ,
    ∃ A : ∀ i : Fin 3, Matrix (Fin (dT i)) (Fin (dS i)) (Polynomial F),
    ∃ R : Fin e → T3 F dT,
      ∀ idx : ∀ i : Fin 3, Fin (dT i),
        (∑ sidx : (∀ i : Fin 3, Fin (dS i)),
            (∏ i : Fin 3, A i (idx i) (sidx i)) * Polynomial.C (S sidx)) =
          Polynomial.X ^ q * Polynomial.C (T idx) +
            ∑ j : Fin e,
              Polynomial.X ^ (q + j.val + 1) * Polynomial.C (R j idx)


scoped infix:50 " ⊴ " => OM.PolMul.Degen

/-- Degeneration on the second and third legs: the first-leg polynomial matrix
is the identity transported along the shared-leg equality `h`. -/
def Degen23 {dT dS : Fin 3 → ℕ+}
    (T : T3 F dT) (S : T3 F dS) (h : dT 0 = dS 0) : Prop :=
  ∃ q e : ℕ,
    ∃ A : ∀ i : Fin 3,
      Matrix (Fin (dT i)) (Fin (dS i)) (Polynomial F),
    ∃ R : Fin e → T3 F dT,
      (∀ x y : Fin (dT 0),
        A 0 x (Fin.cast (congrArg (fun z : ℕ+ => (z : ℕ)) h) y) = if x = y then 1 else 0) ∧
      ∀ idx : ∀ i : Fin 3, Fin (dT i),
        (∑ sidx : (∀ i : Fin 3, Fin (dS i)),
            (∏ i : Fin 3, A i (idx i) (sidx i)) * Polynomial.C (S sidx)) =
          Polynomial.X ^ q * Polynomial.C (T idx) +
            ∑ j : Fin e,
              Polynomial.X ^ (q + j.val + 1) * Polynomial.C (R j idx)


scoped infix:50 " ⊴₂₃ " => OM.PolMul.Degen23

noncomputable def AsympRestricts {dT dS : Fin 3 → ℕ+}
    (T : T3 F dT) (S : T3 F dS) : Prop :=
  AsympRel (tensorStrassenPreorder (F := F) (k := 3) (by norm_num))
    (TensorClass.mk ⟨dT, T⟩) (TensorClass.mk ⟨dS, S⟩)


scoped infix:50 " ≲ " => OM.PolMul.AsympRestricts

/-- Tensor rank, reusing `Semicontinuity.tensorRank`. -/
noncomputable def tensorRank {d : Fin 3 → ℕ+} (T : T3 F d) : ℕ :=
  Semicontinuity.tensorRank T


/-- The exponent of square matrix multiplication. -/
noncomputable def omegaF (F : Type u) [Field F] : ℝ :=
  sInf {τ : ℝ | ∃ C : ℝ, ∀ (n : ℕ), ∀ hn : 1 ≤ n,
    (tensorRank (matMul (F := F) (⟨n, Nat.zero_lt_one.trans_le hn⟩ : ℕ+)
      (⟨n, Nat.zero_lt_one.trans_le hn⟩ : ℕ+)
      (⟨n, Nat.zero_lt_one.trans_le hn⟩ : ℕ+)) : ℝ) ≤ C * (n : ℝ) ^ τ}


/-- The rectangular matrix multiplication exponent, with side lengths
`⌈n^a⌉,⌈n^b⌉,⌈n^c⌉`. -/
noncomputable def omegaRect (F : Type u) [Field F] (a b c : ℝ) : ℝ :=
  sInf {γ : ℝ | ∃ C : ℝ, ∀ (n : ℕ), ∀ hn : 1 ≤ n,
    (tensorRank (matMul (F := F)
      (⟨⌈(n : ℝ) ^ a⌉₊, Nat.ceil_pos.mpr (Real.rpow_pos_of_pos (by
          exact_mod_cast Nat.zero_lt_one.trans_le hn) a)⟩ : ℕ+)
      (⟨⌈(n : ℝ) ^ b⌉₊, Nat.ceil_pos.mpr (Real.rpow_pos_of_pos (by
          exact_mod_cast Nat.zero_lt_one.trans_le hn) b)⟩ : ℕ+)
      (⟨⌈(n : ℝ) ^ c⌉₊, Nat.ceil_pos.mpr (Real.rpow_pos_of_pos (by
          exact_mod_cast Nat.zero_lt_one.trans_le hn) c)⟩ : ℕ+)) : ℝ)
      ≤ C * (n : ℝ) ^ γ}


/-- The dual exponent `α_F`, the largest nonnegative `k` with
`ω_F(1,k,1)=2`. -/
noncomputable def alphaF (F : Type u) [Field F] : ℝ :=
  sSup {k : ℝ | 0 ≤ k ∧ omegaRect F 1 k 1 = 2}


/-- Strassen's asymptotic spectrum of three-tensor restriction classes. -/
noncomputable def Spectral (F : Type u) [Field F] : Type u :=
  AsymptoticSpectrum (tensorStrassenPreorder (F := F) (k := 3) (by norm_num))


namespace Spectral

/-- Evaluate a spectral point on a tensor through `TensorClass.mk`. -/
noncomputable def eval (φ : Spectral F) {d : Fin 3 → ℕ+} (T : T3 F d) : ℝ :=
  AsymptoticSpectrum.eval
    (tensorStrassenPreorder (F := F) (k := 3) (by norm_num))
    (TensorClass.mk ⟨d, T⟩) φ


/-- The permuted spectral point `φ_π`, satisfying
`φ_π(T) = φ(π • T)` with the leg convention of `OM.PolMul.perm`. -/
noncomputable def perm (π : Equiv.Perm (Fin 3)) (φ : Spectral F) : Spectral F :=
  toAbstractSpectralPoint (F := F) (k := 3) (by norm_num)
    ((ofAbstractSpectralPoint (K := F) (k := 3) (by norm_num) φ).reindex π.symm)


end Spectral

/-- Symmetrisation: the tensor product of all six leg permutations of `T`.
Each output-leg coordinate is decoded into its six factors in the canonical
`Fintype.equivFin` order (used in Section 4). -/
-- NOTE: the dependency has only binary `kroneckerTensor`; this heterogeneous
-- six-fold product is defined entrywise so its format is the pointwise product.
noncomputable def symm {d : Fin 3 → ℕ+} (T : T3 F d) :
    T3 F (fun i => ∏ π : Equiv.Perm (Fin 3), d (π.symm i)) := by
  classical
  intro idx
  let split : ∀ i : Fin 3, ∀ π : Equiv.Perm (Fin 3), Fin (d (π.symm i)) :=
    fun i =>
      (Fintype.equivFin (∀ π : Equiv.Perm (Fin 3), Fin (d (π.symm i)))).symm
        (Fin.cast (by
          rw [Fintype.card_pi]
          simpa only [Fintype.card_fin] using!
            (map_prod PNat.coeMonoidHom (fun π : Equiv.Perm (Fin 3) => d (π.symm i))
              Finset.univ).symm) (idx i))
  exact ∏ π : Equiv.Perm (Fin 3), perm π T (fun i => split i π)


end OM.PolMul
