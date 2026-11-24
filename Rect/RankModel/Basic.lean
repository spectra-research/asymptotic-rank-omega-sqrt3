/-
The tensor-rank model of `github.com/jzuiddam/matrix-mult-exponent` (Apache-2.0), commit
`f8478f7b8706db8f176e3cc1954003af9c4113f0`, copied **verbatim** (declarations, binders, bodies and
docstrings) from these files, so that the rank-model statements of the rectangular bound use its notions:

* `OmegaBound/Tensor/Basic.lean`: `Tensor3`, `Tensor3.act`, `Tensor3.Restricts` (notation `≤ₜ`), `Tensor3.matMul`;
* `OmegaBound/Tensor/Identity.lean`: `Tensor3.identity`;
* `OmegaBound/Rank.lean`: `OmegaBound.RankLE`;
* `OmegaBound/Omega.lean`: `OmegaBound.IsMMExponent`, `OmegaBound.omegaMM`.

That repository builds with Lean v4.27.0, this one with v4.34.1, so it cannot be imported; only the
imports differ: focused finite-sum and real-power modules replace the upstream imports.
All copied declarations below remain verbatim. Nothing else from it is used.
-/
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! ## From `OmegaBound/Tensor/Basic.lean` -/

section BasicLean

variable (R : Type*) [CommSemiring R]

/-- A 3-tensor over R with index sets α, β, γ -/
abbrev Tensor3 (α β γ : Type*) := α → β → γ → R

namespace Tensor3

variable {R}
variable {α β γ α' β' γ' : Type*}

section Action

variable [Fintype α] [Fintype β] [Fintype γ]

/-- The action (A₁ ⊗ A₂ ⊗ A₃) · T of three matrices on a tensor.
    The result at index (i, j, k) is ∑_{i',j',k'} A₁(i,i') A₂(j,j') A₃(k,k') T(i',j',k'). -/
def act (A₁ : α' → α → R) (A₂ : β' → β → R) (A₃ : γ' → γ → R)
    (T : Tensor3 R α β γ) : Tensor3 R α' β' γ' :=
  fun i j k => ∑ i' : α, ∑ j' : β, ∑ k' : γ, A₁ i i' * A₂ j j' * A₃ k k' * T i' j' k'

end Action

section Restriction

variable [Fintype α] [Fintype β] [Fintype γ]

/-- `S ≤ₜ T`: `S` is a restriction of `T`, that is, there exist matrices A₁, A₂, A₃
    such that S = (A₁ ⊗ A₂ ⊗ A₃) · T -/
def Restricts (S : Tensor3 R α' β' γ') (T : Tensor3 R α β γ) : Prop :=
  ∃ (A₁ : α' → α → R) (A₂ : β' → β → R) (A₃ : γ' → γ → R),
    S = act A₁ A₂ A₃ T

scoped infix:50 " ≤ₜ " => Restricts

end Restriction

section MatMul

/-- The matrix multiplication tensor ⟨a,b,c⟩ of format (a·b) × (b·c) × (c·a).
    Defined as ∑_{i ∈ [a]} ∑_{j ∈ [b]} ∑_{k ∈ [c]} e_{i,j} ⊗ e_{j,k} ⊗ e_{k,i}.
    This tensor encodes the bilinear map (A, B) ↦ A·B for matrix multiplication. -/
def matMul (a b c : ℕ) : Tensor3 R (Fin a × Fin b) (Fin b × Fin c) (Fin c × Fin a) :=
  fun ⟨i, j⟩ ⟨j', k⟩ ⟨k', i'⟩ => if j = j' ∧ k = k' ∧ i = i' then 1 else 0

end MatMul

end Tensor3

end BasicLean

/-! ## From `OmegaBound/Tensor/Identity.lean` -/

section IdentityLean

namespace Tensor3

variable (R : Type*) [CommSemiring R]

/-- The identity tensor I_r of size r × r × r.
    I_r(i,j,k) = 1 if i = j = k, else 0 -/
def identity (r : ℕ) : Tensor3 R (Fin r) (Fin r) (Fin r) :=
  fun i j k => if i = j ∧ j = k then 1 else 0

end Tensor3

end IdentityLean

/-! ## From `OmegaBound/Rank.lean` -/

section RankLean

open Tensor3

namespace OmegaBound

variable {R : Type*} [CommSemiring R]
variable {α β γ α' β' γ' : Type*}

/-- `RankLE T r` says the tensor `T` has rank at most `r`: it is a restriction of the
`r`-dimensional identity tensor, equivalently a sum of `r` rank-one tensors. -/
def RankLE (T : Tensor3 R α β γ) (r : ℕ) : Prop := T ≤ₜ identity R r

end OmegaBound

end RankLean

/-! ## From `OmegaBound/Omega.lean` -/

section OmegaLean

open Tensor3

namespace OmegaBound

variable (R : Type*) [CommSemiring R]

/-- `τ` is an exponent for matrix multiplication over `R` if the rank of `⟨n,n,n⟩`
is `O(nᵗ)`. -/
def IsMMExponent (τ : ℝ) : Prop :=
  ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n →
    ∃ r : ℕ, RankLE (Tensor3.matMul (R := R) n n n) r ∧ (r : ℝ) ≤ C * (n : ℝ) ^ τ

/-- **The exponent of matrix multiplication** over `R`. -/
noncomputable def omegaMM : ℝ := sInf {τ | IsMMExponent R τ}

end OmegaBound

end OmegaLean
