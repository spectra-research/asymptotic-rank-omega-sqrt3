import PLATFORM.Statements.«R114.3»
import Lib.OM.NNN32.FourPrices

open P2M.R114 Semicontinuity AsymptoticSpectrumDuality OM.NNN32
open scoped Classical

def S_R114_16 : Prop :=
  ∀ (V : Type) [Fintype V] (φ : AsymptoticSpectrum fourPreorder) (τ : Fin 4 → V) (d : V → V → ℝ),
    FourNetwork.Valid φ τ d → 0 ≤ d → (∀ v, d v v = 0) → (∀ u v, d u v = d v u) →
    ∀ (f : Fin 4 → ℕ+) (N : FourNetwork V f), N.Local τ →
    ∀ (m : ℕ) (D : Fin m → ℕ+) (U : (j : Fin m) → KTensor ℂ (fun _ : Fin 3 => D j))
      (p : Fin m → Fin 3 → V)
      (read : (j : Fin m) → Fin 3 → ((v : N.graph.V) → N.graph.T v) → Fin (D j : ℕ)),
      (∀ j, 2 ≤ D j) → (∀ j i, N.graph.DepAt (p j i) (read j i)) →
      let Z : KTensor ℂ f := fun a => ∑ x : (v : N.graph.V) → N.graph.T v,
        (∏ i, N.out i x (a i)) * (∏ k, N.graph.F k x) * ∏ j, U j (fun i => read j i x)
      let value := AsymptoticSpectrum.eval fourPreorder (TensorClass.mk ⟨f, Z⟩) φ
      0 < value → Real.logb 2 value ≤ N.graph.cost d +
        ∑ j, relativeCost (U j) * Real.logb 2 ((D j : ℕ) : ℝ) *
          (d (p j 0) (p j 1) + d (p j 1) (p j 2) + d (p j 2) (p j 0))
