/- Adapted from PolMul/SpectralFacts/Power.lean of an earlier formalisation
   (commit 51c6e6b6e8b8d7226c6a828dba618ae1de5b5f8a).
   Uses Foundations tensor definitions; declarations are renamed under OM. -/
import Lib.OM.PolMulStatements.SP_5

namespace OM.PolMul.SpectralFacts

open AsymptoticSpectrumDuality
open Semicontinuity
open OM.PolMulDef

universe u

variable {F : Type u} [Field F]

private lemma unitPair_value_pow {arity : ℕ} (Fspec : Semicontinuity.SpectralPoint arity F)
    (i j : Fin arity) (hij : i ≠ j) (r : ℕ+) (k : ℕ) :
    Fspec.toFun (unitPairTensor (F := F)
      (⟨(r : ℕ) ^ k, pow_pos r.pos k⟩ : ℕ+) i j hij) =
      (Fspec.toFun (unitPairTensor (F := F) r i j hij)) ^ k := by
  induction k with
  | zero =>
      simpa using! Fspec.unitPair_one i j hij
  | succ k ih =>
      let rk : ℕ+ := ⟨(r : ℕ) ^ k, pow_pos r.pos k⟩
      have hmul := Fspec.unitPair_mul i j hij rk r
      have hr : (⟨(r : ℕ) ^ (k + 1), pow_pos r.pos (k + 1)⟩ : ℕ+) = rk * r := by
        apply PNat.coe_injective
        simp [rk, pow_succ]
      rw [hr, hmul, ih, pow_succ]

/-- A positive, monotone multiplicative value on pair-unit tensors is determined by
its value at two.  This is Strassen's Proposition 4.3 in the form used by SP.5. -/
lemma unitPair_value_eq_rpow {arity : ℕ} (Fspec : Semicontinuity.SpectralPoint arity F)
    (i j : Fin arity) (hij : i ≠ j) (n : ℕ+) :
    Fspec.toFun (unitPairTensor (F := F) n i j hij) =
      Fspec.toFun (unitPairTensor (F := F) 2 i j hij) ^
        Real.logb 2 (((n : ℕ) : ℝ)) := by
  classical
  let x : ℝ := Fspec.toFun (unitPairTensor (F := F) 2 i j hij)
  let y : ℝ := Fspec.toFun (unitPairTensor (F := F) n i j hij)
  have hx_one : 1 ≤ x := by
    have hmono := Fspec.mono
      (unitPairTensor (F := F) 1 i j hij)
      (unitPairTensor (F := F) 2 i j hij)
      (unitPairTensor_restricts_of_le (F := F) i j hij (by norm_num))
    simpa [x, Fspec.unitPair_one i j hij] using! hmono
  have hy_one : 1 ≤ y := by
    have hmono := Fspec.mono
      (unitPairTensor (F := F) 1 i j hij)
      (unitPairTensor (F := F) n i j hij)
      (unitPairTensor_restricts_of_le (F := F) i j hij n.pos)
    simpa [y, Fspec.unitPair_one i j hij] using! hmono
  rcases hx_one.eq_or_lt with hx | hx
  · have hall := free_units (F := F) Fspec i j hij hx.symm n
    simp [x, hall, hx.symm]
  · have hxpos : 0 < x := zero_lt_one.trans hx
    have hypos : 0 < y := zero_lt_one.trans_le hy_one
    have hlog : Real.logb x y = Real.logb 2 (((n : ℕ) : ℝ)) := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · let D : ℝ := Real.logb 2 (((n : ℕ) : ℝ)) - Real.logb x y
        have hD : 0 < D := sub_pos.mpr hlt
        obtain ⟨k, hk⟩ := exists_nat_gt (1 / D)
        have hkpos : 0 < k := by
          by_contra hk0
          have : k = 0 := Nat.eq_zero_of_not_pos hk0
          subst k
          simp only [Nat.cast_zero] at hk
          exact (not_lt_of_ge (div_nonneg zero_le_one hD.le)) hk
        let a : ℕ := Nat.log 2 ((n : ℕ) ^ k)
        let twoPow : ℕ+ := ⟨2 ^ a, pow_pos (by norm_num) a⟩
        let nPow : ℕ+ := ⟨(n : ℕ) ^ k, pow_pos n.pos k⟩
        have hnat_lo : (twoPow : ℕ) ≤ (nPow : ℕ) := by
          simpa [twoPow, nPow, a] using!
            (Nat.pow_log_le_self 2 (pow_ne_zero k (PNat.ne_zero n)))
        have hnat_hi : (nPow : ℕ) < (twoPow : ℕ) * 2 := by
          simpa [twoPow, nPow, a, pow_succ] using!
            (Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) ((n : ℕ) ^ k))
        have hval_lo : x ^ a ≤ y ^ k := by
          rw [← unitPair_value_pow Fspec i j hij (2 : ℕ+) a,
            ← unitPair_value_pow Fspec i j hij n k]
          exact Fspec.mono _ _
            (unitPairTensor_restricts_of_le (F := F) i j hij hnat_lo)
        have hval_hi : y ^ k ≤ x ^ (a + 1) := by
          rw [← unitPair_value_pow Fspec i j hij n k,
            ← unitPair_value_pow Fspec i j hij (2 : ℕ+) (a + 1)]
          exact Fspec.mono _ _
            (unitPairTensor_restricts_of_le (F := F) i j hij (by
              simpa [twoPow, pow_succ] using! hnat_hi.le))
        have hlog_lo := (Real.logb_le_logb (b := x) hx (pow_pos hxpos a)
          (pow_pos hypos k)).2 hval_lo
        have hlog_hi := (Real.logb_le_logb (b := x) hx (pow_pos hypos k)
          (pow_pos hxpos (a + 1))).2 hval_hi
        rw [Real.logb_pow, Real.logb_pow, Real.logb_self_eq_one hx] at hlog_lo hlog_hi
        norm_num at hlog_lo hlog_hi
        have hbase_hi : (k : ℝ) * Real.logb 2 (((n : ℕ) : ℝ)) < a + 1 := by
          have hcast : (((n : ℕ) ^ k : ℕ) : ℝ) < ((2 ^ (a + 1) : ℕ) : ℝ) := by
            exact_mod_cast (by simpa [twoPow, nPow, pow_succ] using! hnat_hi)
          have ht := Real.logb_lt_logb (b := (2 : ℝ)) (by norm_num)
            (by positivity) hcast
          rw [Nat.cast_pow, Nat.cast_pow, Real.logb_pow, Real.logb_pow,
            show (((2 : ℕ) : ℝ)) = 2 by norm_num,
            Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)] at ht
          norm_num at ht
          simpa [mul_comm] using! ht
        have hgap : 1 < (k : ℝ) * D := by
          have hk' : 1 / D < (k : ℝ) := by exact_mod_cast hk
          calc
            1 = (1 / D) * D := by field_simp [hD.ne']
            _ < (k : ℝ) * D := mul_lt_mul_of_pos_right hk' hD
        have : (k : ℝ) * D < 1 := by
          dsimp [D]
          nlinarith
        linarith
      · let D : ℝ := Real.logb x y - Real.logb 2 (((n : ℕ) : ℝ))
        have hD : 0 < D := sub_pos.mpr hgt
        obtain ⟨k, hk⟩ := exists_nat_gt (1 / D)
        have hkpos : 0 < k := by
          by_contra hk0
          have : k = 0 := Nat.eq_zero_of_not_pos hk0
          subst k
          simp only [Nat.cast_zero] at hk
          exact (not_lt_of_ge (div_nonneg zero_le_one hD.le)) hk
        let a : ℕ := Nat.log 2 ((n : ℕ) ^ k)
        let twoPow : ℕ+ := ⟨2 ^ a, pow_pos (by norm_num) a⟩
        let nPow : ℕ+ := ⟨(n : ℕ) ^ k, pow_pos n.pos k⟩
        have hnat_lo : (twoPow : ℕ) ≤ (nPow : ℕ) := by
          simpa [twoPow, nPow, a] using!
            (Nat.pow_log_le_self 2 (pow_ne_zero k (PNat.ne_zero n)))
        have hnat_hi : (nPow : ℕ) < (twoPow : ℕ) * 2 := by
          simpa [twoPow, nPow, a, pow_succ] using!
            (Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) ((n : ℕ) ^ k))
        have hval_lo : x ^ a ≤ y ^ k := by
          rw [← unitPair_value_pow Fspec i j hij (2 : ℕ+) a,
            ← unitPair_value_pow Fspec i j hij n k]
          exact Fspec.mono _ _
            (unitPairTensor_restricts_of_le (F := F) i j hij hnat_lo)
        have hval_hi : y ^ k ≤ x ^ (a + 1) := by
          rw [← unitPair_value_pow Fspec i j hij n k,
            ← unitPair_value_pow Fspec i j hij (2 : ℕ+) (a + 1)]
          exact Fspec.mono _ _
            (unitPairTensor_restricts_of_le (F := F) i j hij (by
              simpa [twoPow, pow_succ] using! hnat_hi.le))
        have hlog_lo := (Real.logb_le_logb (b := x) hx (pow_pos hxpos a)
          (pow_pos hypos k)).2 hval_lo
        have hlog_hi := (Real.logb_le_logb (b := x) hx (pow_pos hypos k)
          (pow_pos hxpos (a + 1))).2 hval_hi
        rw [Real.logb_pow, Real.logb_pow, Real.logb_self_eq_one hx] at hlog_lo hlog_hi
        norm_num at hlog_lo hlog_hi
        have hbase_lo : (a : ℝ) ≤ (k : ℝ) * Real.logb 2 (((n : ℕ) : ℝ)) := by
          have := Real.natLog_le_logb ((n : ℕ) ^ k) 2
          rw [Nat.cast_pow, Real.logb_pow] at this
          simpa [a, mul_comm] using! this
        have hgap : 1 < (k : ℝ) * D := by
          have hk' : 1 / D < (k : ℝ) := by exact_mod_cast hk
          calc
            1 = (1 / D) * D := by field_simp [hD.ne']
            _ < (k : ℝ) * D := mul_lt_mul_of_pos_right hk' hD
        have : (k : ℝ) * D ≤ 1 := by
          dsimp [D]
          nlinarith
        linarith
    calc
      y = x ^ Real.logb x y :=
        (Real.rpow_logb hxpos (ne_of_gt hx) hypos).symm
      _ = x ^ Real.logb 2 (((n : ℕ) : ℝ)) := by rw [hlog]

end OM.PolMul.SpectralFacts
