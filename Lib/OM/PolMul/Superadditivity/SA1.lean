/- Adapted from PolMul/Superadditivity/SA1.lean of an earlier formalisation
   (commit 51c6e6b6e8b8d7226c6a828dba618ae1de5b5f8a).
   Amanov, van den Berg and Zuiddam (2026),
   “Multiplying matrices via polynomials: exposition and barriers”.
   Uses Foundations tensor definitions; declarations are renamed under OM. -/
import Lib.OM.PolMul.Superadditivity.Families
import Lib.OM.PolMul.PolmulBasics
import Lib.OM.PolMulStatements.SA_1

/-!
# Isomorphic-summand superadditivity

This follows the short finite-parameter argument in the proof of the isomorphic-summands lemma:
separate the summands with `PM.4`, normalize the polynomial-multiplication
factors with `PM.1`, `SP.3`, and `SP.5`, and use the direct-sum copy bound.
-/

namespace OM.PolMul.Superadditivity

open AsymptoticSpectrumDuality
open Semicontinuity
open scoped BigOperators

universe u

variable {F : Type u} [Field F]

private lemma polmul_one_fmt (q : ℕ+) : ∀ i : Fin 3,
    ((fmt 1 q (1 + q - 1) i : ℕ)) =
      (fmt (1 * 1) (1 * q) (q * 1) i : ℕ) := by
  have hadd : (((1 : ℕ+) + q - 1 : ℕ+) : ℕ) = (q : ℕ) := by
    rw [PNat.sub_coe, PNat.add_coe]
    rw [if_pos]
    · omega
    · apply (PNat.coe_lt_coe _ _).mp
      rw [PNat.add_coe]
      have hq := q.pos
      norm_num
  intro i
  fin_cases i <;> simp [fmt, hadd]

-- Keep coordinate normalization from monopolizing a malformed build.
set_option maxHeartbeats 300000 in
private lemma polmul_one_restrictsEquiv_matMul (q : ℕ+) :
    polmul (F := F) 1 q ∼ₜ matMul (F := F) 1 1 q := by
  let hfmt := polmul_one_fmt q
  have hval : ∀ idx, polmul (F := F) 1 q idx =
      matMul (F := F) 1 1 q (fun i ↦ Fin.cast (hfmt i) (idx i)) := by
    intro idx
    simp only [polmul, matMul, finProdFinEquiv_symm_apply]
    have h0 : (idx 0).val = 0 := by
      simpa using! congrArg Fin.val (Fin.eq_zero (idx 0))
    have hlt1 : (idx 1).val < (q : ℕ) := by simpa [fmt] using! (idx 1).isLt
    congr 1
    apply propext
    simp [Fin.ext_iff, Nat.mod_eq_of_lt hlt1, h0, eq_comm]
  constructor
  · exact Restricts.of_eq_cast hfmt hval
  · refine Restricts.of_eq_cast (fun i ↦ (hfmt i).symm) (fun idx ↦ ?_)
    have hv := hval (fun i ↦ Fin.cast (hfmt i).symm (idx i))
    have hcast :
        (fun i ↦ Fin.cast (hfmt i) (Fin.cast (hfmt i).symm (idx i))) = idx := by
      funext i
      exact Fin.rightInverse_cast (hfmt i) (idx i)
    rw [hcast] at hv
    exact hv.symm

-- The logarithmic normal form uses `ring` under two `logb` expansions.
set_option maxHeartbeats 100000 in
private lemma eval_polmul_one (φ : Spectral F) (q : ℕ+) :
    Spectral.eval φ (polmul (F := F) 1 q) =
      ((q : ℕ) : ℝ) ^
        Real.logb 2 (Spectral.eval φ (matMul (F := F) 1 1 2)) := by
  rw [eval_restrictsEquiv φ (polmul_one_restrictsEquiv_matMul q)]
  have h := (OM.PolMul.SpectralFacts.proof_SP_5 F φ).2.2.2 1 1 q
  change Spectral.eval φ (matMul (F := F) 1 1 q) = _ at h
  rw [h]
  have hone : ((((1 : ℕ+) : ℕ) : ℝ)) = 1 := by norm_num
  rw [hone, Real.logb_one]
  simp only [Real.rpow_zero, one_mul]
  let c : ℝ := Spectral.eval φ (matMul (F := F) 1 1 2)
  have hc : 0 < c := by
    have hc1 := (OM.PolMul.SpectralFacts.proof_SP_5 F φ).1.1
    change 1 ≤ c at hc1
    exact zero_lt_one.trans_le hc1
  have hq : 0 < (((q : ℕ) : ℝ)) := by exact_mod_cast q.pos
  apply Real.log_injOn_pos (Real.rpow_pos_of_pos hc _)
    (Real.rpow_pos_of_pos hq _)
  rw [Real.log_rpow hc, Real.log_rpow hq]
  simp only [Real.logb]
  ring

-- Bound the separation-chain normalization independently of project defaults.
set_option maxHeartbeats 200000 in
/-- The lemma on isomorphic summands. -/
theorem proof_SA_1 : OM_S_SA_1 := by
  intro F _ φ hp r d n h S hiso
  change 0 < Real.logb 2 (Spectral.eval φ (matMul (F := F) 1 1 2)) at hp
  change (1 / 2 : ℝ) *
      (((r : ℕ) : ℝ) ^
        Real.logb 2 (Spectral.eval φ (matMul (F := F) 1 1 2))) *
      Spectral.eval φ (S 0) ≤ Spectral.eval φ (pdsumFamily d n h S)
  let p : ℝ := Real.logb 2 (Spectral.eval φ (matMul (F := F) 1 1 2))
  let x : ℝ := Spectral.eval φ (S 0)
  let z : ℝ := Spectral.eval φ (pdsumFamily d n h S)
  let D : ℝ := Spectral.eval φ (dsumFamily d S)
  let R : ℝ := ((r : ℕ) : ℝ)
  let A : ℝ := R ^ p
  let Q : ℝ := Spectral.eval φ (polmul (F := F) r r)
  have hsep := OM.PolMul.SpectralFacts.proof_SP_2 F φ _ _
    (OM.PolMul.PolmulBasics.proof_PM_4 F r r d n h S)
  change Spectral.eval φ (kron (dsumFamily d S) (polmul 1 r)) ≤
    Spectral.eval φ (kron (pdsumFamily d n h S) (polmul r r)) at hsep
  rw [eval_kron, eval_kron, eval_polmul_one] at hsep
  change D * A ≤ z * Q at hsep
  have hcopies : R * x ≤ D := by
    exact card_mul_eval_le_eval_dsumFamily φ r d S hiso
  have hQ : Q ≤ (((r + r - 1 : ℕ+) : ℕ) : ℝ) := by
    have hmono := OM.PolMul.SpectralFacts.proof_SP_2 F φ _ _
      (OM.PolMul.PolmulBasics.proof_PM_1 F r r)
    change Spectral.eval φ (polmul (F := F) r r) ≤
      Spectral.eval φ (unit (r + r - 1)) at hmono
    have hu := (OM.PolMul.SpectralFacts.proof_SP_3 F φ).2 (r + r - 1)
    change Spectral.eval φ (unit (F := F) (r + r - 1)) = _ at hu
    rw [hu] at hmono
    exact hmono
  have hR : 0 < R := by
    dsimp [R]
    positivity
  have hA : 0 ≤ A := Real.rpow_nonneg hR.le _
  have hz : 0 ≤ z := eval_nonneg φ _
  have htwo : (((r + r - 1 : ℕ+) : ℕ) : ℝ) ≤ 2 * R := by
    have hn : ((r + r - 1 : ℕ+) : ℕ) ≤ 2 * (r : ℕ) := by
      have hcoe : ((r + r - 1 : ℕ+) : ℕ) = (r : ℕ) + r - 1 := by
        rw [PNat.sub_coe, PNat.add_coe]
        rw [if_pos]
        · rfl
        · apply (PNat.coe_lt_coe _ _).mp
          rw [PNat.add_coe]
          have hr := r.pos
          norm_num
          omega
      rw [hcoe]
      omega
    dsimp [R]
    exact_mod_cast hn
  change (1 / 2 : ℝ) * A * x ≤ z
  have hmain : R * x * A ≤ z * Q :=
    (mul_le_mul_of_nonneg_right hcopies hA).trans hsep
  have hmain' : R * x * A ≤ z * (2 * R) :=
    hmain.trans ((mul_le_mul_of_nonneg_left hQ hz).trans
      (mul_le_mul_of_nonneg_left htwo hz))
  have hcanc : x * A ≤ 2 * z := by
    apply le_of_mul_le_mul_left _ hR
    simpa only [mul_assoc, mul_comm, mul_left_comm] using! hmain'
  calc
    (1 / 2 : ℝ) * A * x = (A * x) / 2 := by ring
    _ ≤ z := (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).2 (by
      simpa only [mul_comm] using! hcanc)

end OM.PolMul.Superadditivity
