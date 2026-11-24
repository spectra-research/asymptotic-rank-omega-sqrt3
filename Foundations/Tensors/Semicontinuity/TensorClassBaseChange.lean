/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Foundations.Tensors.Semicontinuity.TensorSemiring
import Foundations.Tensors.Semicontinuity.FieldExtension

/-!
# The scalar-extension ring homomorphism on tensor-classes

For a field extension `K / F`, base change `KTensor.baseChange` (Strassen 1988,
Theorem 3.10, scalar extension) sends a `k`-tensor over `F` to a `k`-tensor over
`K` by applying `algebraMap F K` entrywise. Because base change respects the
restriction-equivalence `∼ₜ` (from `KTensor.baseChange_restricts`, applied both
ways) and commutes with the direct sum `⊕ₜ` and Kronecker product `⊠`, it
descends to a **semiring homomorphism** between the `TensorClass`-class
semirings:

`tensorClassBaseChange : TensorClass F k →+* TensorClass K k`.

This is the scalar-extension functor on tensor-classes (Strassen 1988, scalar
extension). It is the ring-hom `i` fed to
`AsymptoticSpectrumDuality.restriction_surjective` (build component 3 of the
Strassen-duality bridge).
-/

namespace Semicontinuity

universe u

variable {F : Type u} [Field F] {K : Type u} [Field K] [Algebra F K]
  {k : ℕ} [NeZero k]

/-- Base change of a packaged tensor `⟨d, T⟩ : TT F k`, keeping the format `d`
    and base-changing the underlying `KTensor`. -/
def TT.baseChange (x : TT F k) : TT K k := ⟨x.1, x.2.baseChange (K := K)⟩

omit [NeZero k] in
/-- Base change respects restriction-equivalence `∼ₜ` (both directions of
    `KTensor.baseChange_restricts`). -/
lemma TT.baseChange_respects {x y : TT F k} (h : x ≈ y) :
    (TT.baseChange (K := K) x) ≈ (TT.baseChange (K := K) y) :=
  ⟨KTensor.baseChange_restricts (K := K) _ _ h.1,
    KTensor.baseChange_restricts (K := K) _ _ h.2⟩

/-- **Scalar-extension ring homomorphism** on tensor-classes (Strassen 1988,
    scalar extension). Lifts `KTensor.baseChange` to the `∼ₜ`-quotient:

    * `map_zero` — base change of the zero tensor is `∼ₜ` to the zero tensor
      (`KTensor.baseChange` sends `0 ↦ algebraMap 0 = 0`);
    * `map_one` — `KTensor.baseChange_unitTensor`;
    * `map_add` — `KTensor.baseChange_directSum`;
    * `map_mul` — `KTensor.baseChange_kron`.

    This is the ring-hom `i` fed to
    `AsymptoticSpectrumDuality.restriction_surjective`. -/
noncomputable def tensorClassBaseChange :
    TensorClass F k →+* TensorClass K k where
  toFun := Quotient.map (TT.baseChange (K := K)) (fun _ _ h => TT.baseChange_respects h)
  map_one' := by
    rw [TensorClass.one_def, TensorClass.one_def]
    change TensorClass.mk (TT.baseChange (K := K) ⟨_, unitTensor F (k := k) 1⟩) = _
    exact congrArg TensorClass.mk
      (by simp only [TT.baseChange, KTensor.baseChange_unitTensor])
  map_mul' := by
    rintro ⟨a⟩ ⟨b⟩
    change TensorClass.mk (TT.baseChange (K := K) ⟨_, a.2 ⊠ b.2⟩) = _
    exact congrArg TensorClass.mk
      (by simp only [TT.baseChange, KTensor.baseChange_kron])
  map_zero' := by
    have h0 : (zeroT (F := F) (k := k)).baseChange (K := K) = zeroT (F := K) (k := k) := by
      funext idx
      simp only [KTensor.baseChange, zeroT, map_zero]
    rw [TensorClass.zero_def, TensorClass.zero_def]
    change TensorClass.mk (TT.baseChange (K := K) ⟨_, zeroT (F := F) (k := k)⟩) = _
    exact congrArg TensorClass.mk (by simp only [TT.baseChange, h0])
  map_add' := by
    rintro ⟨a⟩ ⟨b⟩
    change TensorClass.mk (TT.baseChange (K := K) ⟨_, a.2 ⊕ₜ b.2⟩) = _
    exact congrArg TensorClass.mk
      (by simp only [TT.baseChange, KTensor.baseChange_directSum])

end Semicontinuity
