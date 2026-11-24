import Lib.OM.NNN32.Multiplicity

/-! # Multiplicity-grouped expansions of ordinary tensor powers

The library's `kronPowNat T n` is the `(n + 1)`-fold Kronecker power. Expanding
a sum in this power and grouping by letter counts gives at most `(n + 2)^m`
groups for an alphabet of size `m`.
-/

namespace OM.NNN32

open Semicontinuity OM.PolMul.Superadditivity

variable {F : Type*} [Field F] {k m : ℕ} {d : Fin k → ℕ+}

/-- The Kronecker product of the letters of a nonempty word, in the library power format. -/
noncomputable def kronWord (B : Fin m → KTensor F d) :
    (n : ℕ) → (Fin (n + 1) → Fin m) → KTensor F (kronPowFormat d n)
  | 0, w => B (w 0)
  | n + 1, w => kroneckerTensor (kronWord B n (fun i => w i.succ)) (B (w 0))

theorem flatRank_kronWord_le (B : Fin m → KTensor F d) (I : Finset (Fin k))
    (n : ℕ) (w : Fin (n + 1) → Fin m) :
    flatRank (kronWord B n w) I ≤ ∏ i, flatRank (B (w i)) I := by
  induction n with
  | zero => simp [kronWord]
  | succ n ih =>
    rw [kronWord, Fin.prod_univ_succ]
    exact (flatRank_kron_mul_ge _ _ I).trans
      ((Nat.mul_le_mul_right _ (ih fun i => w i.succ)).trans_eq (Nat.mul_comm _ _))

/-- Coefficientwise distributivity expands a power as the sum over all words. -/
theorem sum_kronWord (B : Fin m → KTensor F d) (n : ℕ) :
    (∑ w : Fin (n + 1) → Fin m, kronWord B n w) = kronPowNat (∑ j, B j) n := by
  classical
  induction n with
  | zero => exact (Equiv.funUnique (Fin 1) (Fin m)).sum_comp B
  | succ n ih =>
    calc
      _ = ∑ j : Fin m, ∑ w : Fin (n + 1) → Fin m, kroneckerTensor (kronWord B n w) (B j) := by
        rw [← (Fin.consEquiv (fun _ : Fin (n + 2) => Fin m)).sum_comp (kronWord B (n + 1)),
          Fintype.sum_prod_type]
        simp only [Fin.consEquiv_apply, kronWord, Fin.cons_succ, Fin.cons_zero]
      _ = kroneckerTensor (kronPowNat (∑ j, B j) n) (∑ j, B j) := by
        rw [← ih]
        funext idx
        simp only [Finset.sum_apply, kroneckerTensor]
        rw [Finset.mul_sum]
        simp only [Finset.sum_mul]

/-- Every ordinary tensor power of a sum has a polynomial-size grouped expansion.
The cost bound holds for every group and any chosen pair of cuts. -/
theorem exists_grouped_kronPow (B : Fin m → KTensor F d) (I J : Finset (Fin k)) (n : ℕ) :
    ∃ G : (Fin m → Fin (n + 2)) → KTensor F (kronPowFormat d n),
      (∑ μ, G μ) = kronPowNat (∑ j, B j) n ∧
      ∀ μ, Real.sqrt ((flatRank (G μ) I : ℝ) * (flatRank (G μ) J : ℝ)) ≤
        (∑ j, Real.sqrt ((flatRank (B j) I : ℝ) * (flatRank (B j) J : ℝ))) ^ (n + 1) := by
  classical
  refine ⟨fun μ => ∑ w : {w : Fin (n + 1) → Fin m // wordType w = μ}, kronWord B n w.val, ?_, ?_⟩
  · exact (Fintype.sum_fiberwise wordType (kronWord B n)).trans (sum_kronWord B n)
  · exact sqrt_flatRank_wordType_sum_le (kronWord B n) I J _ _
      (flatRank_kronWord_le B I n) (flatRank_kronWord_le B J n)

end OM.NNN32

