/- Adapted from PLATFORM/Statements/DEF.16.lean of an earlier formalisation
   (commit 51c6e6b6e8b8d7226c6a828dba618ae1de5b5f8a).
   Amanov, van den Berg and Zuiddam (2026),
   “Multiplying matrices via polynomials: exposition and barriers”.
   Uses Foundations tensor definitions; declarations are renamed under OM. -/
import Lib.OM.PolMulStatements.DEF_2
import Lib.OM.PolMulStatements.DEF_4
import Lib.OM.PolMulStatements.DEF_15

namespace OM.PolMulDef

open AsymptoticSpectrumDuality
open Semicontinuity
open scoped BigOperators

universe u

variable {F : Type u} [Field F]

/-- The exponent of square matrix multiplication. -/
noncomputable def omegaF (F : Type u) [Field F] : ℝ :=
  sInf {τ : ℝ | ∃ C : ℝ, ∀ (n : ℕ), ∀ hn : 1 ≤ n,
    (tensorRank (matMul (F := F) (⟨n, Nat.zero_lt_one.trans_le hn⟩ : ℕ+)
      (⟨n, Nat.zero_lt_one.trans_le hn⟩ : ℕ+)
      (⟨n, Nat.zero_lt_one.trans_le hn⟩ : ℕ+)) : ℝ) ≤ C * (n : ℝ) ^ τ}

end OM.PolMulDef
