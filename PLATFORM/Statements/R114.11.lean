import PLATFORM.Statements.«R114.7»
import PLATFORM.Statements.«R113.1»

open P2M.R114 Semicontinuity

def S_R114_11 : Prop :=
  ∀ H : ℕ, 2 ≤ H →
    let D := partitionSide H
    let k := cutoff H
    let S : KTensor ℂ (fun _ : Fin 4 => D) := fun a =>
      ∑ j ∈ Finset.Ioc k (4 * H), OM.NNN30.Crossing.Bfin H H j
        (partitionAt H (a 0)) (partitionAt H (a 1)) (partitionAt H (a 2)) (partitionAt H (a 3))
    rowPiece H + S = P2M.R113.matching D 0 3 1 2 ∧
    flatRank (rowPiece H) {0, 1} ≤ OM.NNN30.Rect.Qn k ∧
    OM.NNN30.Rect.Qn k ≤ (D : ℕ) ∧
    flatRank S {0, 2} ≤ OM.NNN30.Rect.Qn (4 * H - k - 1)
