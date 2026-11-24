/- Adapted from PolMul/Main.lean of an earlier formalisation
   (commit 51c6e6b6e8b8d7226c6a828dba618ae1de5b5f8a).
   Uses Foundations tensor definitions; declarations are renamed under OM. -/
import Mathlib
import Lib.OM.PolMul.Analysis
import Lib.OM.PolMul.OmegaBridge
import Lib.OM.PolMul.SpectralFacts
import Lib.OM.PolMulStatements.MAIN_1
import Lib.OM.PolMulStatements.MAIN_2

namespace OM.PolMul.Main

open AsymptoticSpectrumDuality Semicontinuity
open scoped BigOperators
open OM.PolMulDef

universe u

lemma spectral_value_le {F : Type u} [Field F] (φ : OM.PolMul.Spectral F) :
    Real.logb 2 (OM.PolMul.Spectral.eval φ (OM.PolMul.matMul (F := F) 2 2 2)) ≤
      (9 : ℝ) / 4 := by
  let τ := Real.logb 2 (OM.PolMul.Spectral.eval φ (OM.PolMul.matMul (F := F) 2 2 2))
  have hall (n : ℕ+) :
      (((n : ℕ) : ℝ) ^ (8 * τ / 3)) ≤
        (2 * ((n : ℕ) : ℝ)) ^ (6 : ℕ) := by
    have hlo := OM.PolMul.Analysis.proof_AN_3 F φ n
    change (((n : ℕ) : ℝ) ^ (8 * τ / 3)) ≤
      ∏ π : Equiv.Perm (Fin 3),
        OM.PolMul.Spectral.eval φ (OM.PolMul.perm π (OM.PolMul.polmul n n)) at hlo
    let U : ℝ := (((n + n - 1 : ℕ+) : ℕ) : ℝ)
    have hfactor (π : Equiv.Perm (Fin 3)) :
        OM.PolMul.Spectral.eval φ (OM.PolMul.perm π (OM.PolMul.polmul n n)) ≤ U := by
      rw [← OM.PolMul.Superadditivity.eval_perm]
      exact (OM.PolMul.Profiles.proof_PR_1 F (OM.PolMul.Spectral.perm π φ) n n).2.1
    have hnonneg (π : Equiv.Perm (Fin 3)) : 0 ≤
        OM.PolMul.Spectral.eval φ (OM.PolMul.perm π (OM.PolMul.polmul n n)) := by
      rw [← OM.PolMul.Superadditivity.eval_perm]
      have H := (OM.PolMul.Profiles.proof_PR_1 F (OM.PolMul.Spectral.perm π φ) n n).1
      exact (by positivity : (0 : ℝ) ≤ (((min n n : ℕ+) : ℕ) : ℝ)).trans H
    have hprod : (∏ π : Equiv.Perm (Fin 3),
        OM.PolMul.Spectral.eval φ (OM.PolMul.perm π (OM.PolMul.polmul n n))) ≤
        U ^ (6 : ℕ) := by
      calc
        _ ≤ ∏ _π : Equiv.Perm (Fin 3), U := by
          apply Finset.prod_le_prod₀
          · intro π _
            exact hnonneg π
          · intro π _
            exact hfactor π
        _ = U ^ (6 : ℕ) := by
          rw [Finset.prod_const]
          norm_num [Fintype.card_perm]
    have hU0 : 0 ≤ U := by
      dsimp [U]
      positivity
    have hU : U ≤ 2 * ((n : ℕ) : ℝ) := by
      dsimp [U]
      have hnNat : 1 ≤ (n : ℕ) := n.pos
      have hlt : (1 : ℕ+) < n + n := by
        apply (PNat.coe_lt_coe _ _).mp
        simp only [PNat.add_coe, PNat.val_ofNat]
        omega
      have hval : ((n + n - 1 : ℕ+) : ℕ) = (n : ℕ) + (n : ℕ) - 1 := by
        rw [PNat.sub_coe, if_pos hlt, PNat.add_coe]
        norm_num
      rw [hval, Nat.cast_sub (by omega : 1 ≤ (n : ℕ) + (n : ℕ))]
      push_cast
      linarith
    exact hlo.trans (hprod.trans (pow_le_pow_left₀ hU0 hU 6))
  change τ ≤ (9 : ℝ) / 4
  by_contra hτ
  have hτ' : (9 : ℝ) / 4 < τ := lt_of_not_ge hτ
  let d : ℝ := 8 * τ / 3 - 6
  have hd : 0 < d := by dsimp [d]; linarith
  let x : ℝ := (64 : ℝ) ^ d⁻¹
  have hx : 0 < x := Real.rpow_pos_of_pos (by norm_num) _
  obtain ⟨n, hn⟩ := exists_nat_gt x
  have hnpos : 0 < n := by
    have : (0 : ℝ) < n := hx.trans hn
    exact_mod_cast this
  let N : ℕ+ := ⟨n, hnpos⟩
  have H := hall N
  change ((n : ℝ) ^ (8 * τ / 3)) ≤ (2 * (n : ℝ)) ^ (6 : ℕ) at H
  have H' : (n : ℝ) ^ d ≤ 64 := by
    have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
    rw [show d = 8 * τ / 3 - 6 by rfl, Real.rpow_sub hnR]
    rw [div_le_iff₀ (Real.rpow_pos_of_pos hnR (6 : ℝ))]
    calc
      (n : ℝ) ^ (8 * τ / 3) ≤ (2 * (n : ℝ)) ^ (6 : ℕ) := H
      _ = 64 * (n : ℝ) ^ (6 : ℝ) := by
        ring_nf
        exact congrArg (fun z : ℝ => z * 64)
          (Real.rpow_natCast (n : ℝ) 6).symm
  have hlarge : (64 : ℝ) < (n : ℝ) ^ d := by
    have hbase : x < (n : ℝ) := hn
    have hp := Real.rpow_lt_rpow (Real.rpow_nonneg (by norm_num) _)
      hbase hd
    have hxpow : x ^ d = (64 : ℝ) := by
      dsimp [x]
      rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 64)]
      rw [inv_mul_cancel₀ hd.ne', Real.rpow_one]
    rwa [hxpow] at hp
  linarith

-- The contradiction above is the paper's `n → ∞` argument in an
-- Archimedean form: a positive excess exponent would eventually exceed 64.
set_option maxHeartbeats 500000 in
theorem proof_MAIN_1 : OM_S_MAIN_1 := by
  intro F _
  obtain ⟨φ, hφ⟩ := (OM.PolMul.SpectralFacts.proof_SP_1 F).1
  change OM.PolMul.omegaF F = Real.logb 2
    (OM.PolMul.Spectral.eval φ (OM.PolMul.matMul (F := F) 2 2 2)) at hφ
  change OM.PolMul.omegaF F ≤ (9 : ℝ) / 4
  rw [hφ]
  exact spectral_value_le φ

-- Since `omegaF` is the infimum of the admissible exponents, every strictly
-- larger exponent admits a uniform rank constant.  Monotonicity of real powers
-- then raises that witness exponent to `9/4 + ε`.
set_option maxHeartbeats 300000 in
theorem proof_MAIN_2 : OM_S_MAIN_2 := by
  intro F _ ε hε
  let A : Set ℝ := {t : ℝ | ∃ C : ℝ, ∀ (n : ℕ), ∀ hn : 1 ≤ n,
    (OM.PolMulDef.tensorRank (OM.PolMulDef.matMul (F := F)
      ⟨n, Nat.zero_lt_one.trans_le hn⟩ ⟨n, Nat.zero_lt_one.trans_le hn⟩
      ⟨n, Nat.zero_lt_one.trans_le hn⟩) : ℝ) ≤ C * (n : ℝ) ^ t}
  have hmain := proof_MAIN_1 F
  change OM.PolMul.omegaF F ≤ (9 : ℝ) / 4 at hmain
  have hinf : sInf A < (9 : ℝ) / 4 + ε := by
    change OM.PolMul.omegaF F < (9 : ℝ) / 4 + ε
    linarith
  have hne : A.Nonempty := by
    exact OM.PolMul.OmegaBridge.omegaSet_nonempty F
  obtain ⟨t, htA, ht⟩ := exists_lt_of_csInf_lt hne hinf
  obtain ⟨C, hC⟩ := htA
  have hC0 : 0 ≤ C := by
    have H := hC 1 (by omega)
    norm_num [Real.one_rpow] at H
    exact (Nat.cast_nonneg _).trans H
  refine ⟨C, ?_⟩
  intro n
  have hnR : (1 : ℝ) ≤ ((n : ℕ) : ℝ) := by exact_mod_cast n.pos
  have hpow : (((n : ℕ) : ℝ) ^ t) ≤
      ((n : ℕ) : ℝ) ^ ((9 : ℝ) / 4 + ε) :=
    Real.rpow_le_rpow_of_exponent_le hnR ht.le
  let n' : ℕ+ := ⟨(n : ℕ), n.pos⟩
  have hn' : n' = n := PNat.eq rfl
  have H := hC (n : ℕ) n.pos
  change (OM.PolMulDef.tensorRank (OM.PolMulDef.matMul (F := F) n' n' n') : ℝ) ≤
    C * (((n : ℕ) : ℝ) ^ t) at H
  rw [hn'] at H
  exact H.trans (mul_le_mul_of_nonneg_left hpow hC0)

end OM.PolMul.Main
