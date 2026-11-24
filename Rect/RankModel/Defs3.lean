/-
The rectangular exponent `ω_R(a,b,c)` for three real parameters in the tensor-rank model, defined like
`OmegaBound.omegaMM` in `Rect/RankModel/Basic.lean`, for the shape `⟨⌈n^a⌉, ⌈n^b⌉, ⌈n^c⌉⟩`.
-/
import Rect.RankModel.Basic

open Tensor3

namespace OmegaBound

/-- `τ` is an exponent for `⌈n^a⌉ × ⌈n^b⌉` by `⌈n^b⌉ × ⌈n^c⌉` matrix multiplication over `R` if the rank of
`⟨⌈n^a⌉, ⌈n^b⌉, ⌈n^c⌉⟩` is `O(nᵗ)`. -/
def IsRectMMExponent3 (R : Type*) [CommSemiring R] (a b c τ : ℝ) : Prop :=
  ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n →
    ∃ r : ℕ, RankLE (Tensor3.matMul (R := R) ⌈(n : ℝ) ^ a⌉₊ ⌈(n : ℝ) ^ b⌉₊ ⌈(n : ℝ) ^ c⌉₊) r ∧
      (r : ℝ) ≤ C * (n : ℝ) ^ τ

/-- **The rectangular exponent** `ω_R(a,b,c)` over `R`, in the tensor-rank model. -/
noncomputable def omegaRect3 (R : Type*) [CommSemiring R] (a b c : ℝ) : ℝ :=
  sInf {τ | IsRectMMExponent3 R a b c τ}

end OmegaBound
