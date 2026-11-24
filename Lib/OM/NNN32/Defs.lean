import Foundations.Tensors.Semicontinuity.MaxRankBound
import Mathlib.Basic.Complex.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Module.Pi
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.Data.PNat.Basic
import Mathlib.Order.Lattice.Nat
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Foundations.Tensors.Semicontinuity.TensorStrassenPreorder
import Foundations.AsymptoticSpectrumDuality.AsymptoticSpectrum

/-! # The finite crossing costs and the two four-party comparison conditions -/

namespace OM.NNN32

open Semicontinuity AsymptoticSpectrumDuality

/-- Two equality wires of size `D` in a common four-party format. The crossing pairs `0,3` and `1,2`. -/
def matching (D : ℕ+) (i j k l : Fin 4) : Semicontinuity.KTensor ℂ (fun _ : Fin 4 => D) :=
  fun a => if a i = a j ∧ a k = a l then 1 else 0

/-- Attainable geometric-mean costs of ordinary finite expansions, in leg order `(x,y,u,v)`. -/
def expansionCosts {d : Fin 4 → ℕ+} (T : KTensor ℂ d) : Set ℝ :=
  {c | ∃ (m : ℕ) (B : Fin m → KTensor ℂ d), (∑ j, B j) = T ∧
    c = ∑ j, Real.sqrt ((flatRank (B j) {0, 1} : ℝ) * (flatRank (B j) {0, 2} : ℝ))}

/-- The strict finite crossing test (18). -/
def finiteWitness : Prop :=
  ∃ D : ℕ+, 2 ≤ D ∧ ∃ c ∈ expansionCosts (matching D 0 3 1 2),
    c < ((D : ℕ) : ℝ) ^ Real.sqrt 2

/-- The optimal geometric-mean cost of the crossing. -/
noncomputable def W (D : ℕ+) : ℝ :=
  sInf (expansionCosts (matching D 0 3 1 2))

/-- The partial-transpose rank of the crossing. -/
noncomputable def P (D : ℕ+) : ℕ :=
  sInf {k : ℕ | ∃ R S : KTensor ℂ (fun _ : Fin 4 => D),
    R + S = matching D 0 3 1 2 ∧ k = flatRank R {0, 1} + flatRank S {0, 2}}

/-- Least number of complex bilinear squares in a composition formula of type `[D,D,s]`. -/
noncomputable def sigma (D : ℕ+) : ℕ :=
  let V := Fin (D : ℕ) → ℂ
  sInf {s : ℕ | ∃ f : Fin s → (V →ₗ[ℂ] V →ₗ[ℂ] ℂ),
    ∀ a b : V, (∑ i, a i ^ 2) * (∑ i, b i ^ 2) = ∑ j, (f j a b) ^ 2}

/-- The crossing exponent, specified by its finite-base infimum. -/
noncomputable def gamma : ℝ :=
  sInf {g : ℝ | ∃ b : ℕ+, 2 ≤ b ∧ g = Real.logb ((b : ℕ) : ℝ) (W b)}

/-- The multiplicative four-point inequality in the ordinary spectrum of four-tensor restriction. -/
def spectralFourPoint : Prop :=
  let p := tensorStrassenPreorder (F := ℂ) (k := 4) (by decide +kernel)
  ∀ (D : ℕ+) (φ : AsymptoticSpectrum p),
    let value := fun (i j k l : Fin 4) =>
      AsymptoticSpectrum.eval p (TensorClass.mk ⟨_, matching D i j k l⟩) φ
    value 0 3 1 2 ≤ max (value 0 1 2 3) (value 0 2 1 3)

/-- The two factorizations use cuts `xy|uv` and `xu|yv`, with arbitrary factor sites. -/
def twoTermBound {X : Type*} (d : X → X → ℝ) (κ : ℝ) : Prop :=
  let charge := fun a b c e u v => d a u + d b u + d c v + d e v + κ * d u v
  ∀ t : Fin 4 → X, (∀ i j, i ≠ j → 0 < d (t i) (t j)) →
    ∀ u v u' v' : X,
      d (t 0) (t 3) + d (t 1) (t 2) ≤
        max (charge (t 0) (t 1) (t 2) (t 3) u v)
            (charge (t 0) (t 2) (t 1) (t 3) u' v')

end OM.NNN32
