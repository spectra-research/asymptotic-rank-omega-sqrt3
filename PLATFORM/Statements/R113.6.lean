import Mathlib.Basic.Complex.Basic
import Mathlib.Algebra.Module.Pi
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.Data.PNat.Basic
import Mathlib.Order.Lattice.Nat

namespace P2M.R113

/-- Least number of complex bilinear squares in a composition formula of type `[D,D,s]`. -/
noncomputable def sigma (D : ℕ+) : ℕ :=
  let V := Fin (D : ℕ) → ℂ
  sInf {s : ℕ | ∃ f : Fin s → (V →ₗ[ℂ] V →ₗ[ℂ] ℂ),
    ∀ a b : V, (∑ i, a i ^ 2) * (∑ i, b i ^ 2) = ∑ j, (f j a b) ^ 2}

end P2M.R113
