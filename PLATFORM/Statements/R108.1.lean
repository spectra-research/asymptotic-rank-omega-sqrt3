import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Basic.Complex.Basic

/-- The finite crossing lemma.  The legs are, in order, `z : H.Partition`,
`0 : E.Partition`, `1 : E.Partition`, `∞ : H.Partition`; `B k z x y w` is the `k`-th piece.
The pieces sum to the equality on `z, ∞` times the equality on `0, 1`; the flattening
`z0 | 1∞` of `B k` has rank at most `Q(k) = ∑_{j ≤ k} p(j)`, and the flattening `z1 | 0∞` has
rank at most `Q(D - k)`, `D = 2(H + E)`. -/
def S_R108_1 : Prop :=
  ∀ H E : ℕ, 0 < H → 0 < E →
    ∃ B : Fin (2 * (H + E) + 1) → H.Partition → E.Partition → E.Partition → H.Partition → ℂ,
      (∀ z x y w, ∑ k, B k z x y w = if z = w ∧ x = y then 1 else 0) ∧
      ∀ k : Fin (2 * (H + E) + 1),
        (Matrix.of fun (zx : H.Partition × E.Partition) (yw : E.Partition × H.Partition) =>
            B k zx.1 zx.2 yw.1 yw.2).rank ≤
          ∑ j ∈ Finset.range ((k : ℕ) + 1), Fintype.card j.Partition ∧
        (Matrix.of fun (zy : H.Partition × E.Partition) (xw : E.Partition × H.Partition) =>
            B k zy.1 xw.1 zy.2 xw.2).rank ≤
          ∑ j ∈ Finset.range (2 * (H + E) - (k : ℕ) + 1), Fintype.card j.Partition
