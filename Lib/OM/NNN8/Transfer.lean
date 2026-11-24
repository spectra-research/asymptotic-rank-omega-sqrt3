import Lib.OM.NNN8.Dyadic
import Lib.OM.PolMul.DegenAsymp.Powers
import Lib.OM.PolMul.Superadditivity.Core

/-! Powers of one tensor and dyadic zero padding remove the multiplicative
constant. No submultiplicativity of a maximum over formats is used. -/
noncomputable section
namespace OM.NNN8
open Semicontinuity
set_option maxHeartbeats 2000000

lemma eval_kronPow (φ : PolMul.Spectral ℂ) {d : Fin 3 → ℕ+}
    (T : KTensor ℂ d) (k : ℕ) :
    PolMul.Spectral.eval φ (PolMul.kronPow T k) = (PolMul.Spectral.eval φ T) ^ k := by
  unfold PolMul.Spectral.eval
  rw [PolMul.DegenAsymp.mk_kronPow]
  exact AsymptoticSpectrumDuality.AsymptoticSpectrum.eval_pow _ _ _ _

theorem spectral_power_padding_transfer {a C : ℝ} (ha : 0 ≤ a) (hC : 0 ≤ C)
    (hbound : ∀ (φ : PolMul.Spectral ℂ) (l : ℕ) (N : ℕ+), (N : ℕ) = 2 ^ l →
      ∀ T : KTensor ℂ (fun _ : Fin 3 => N), PolMul.Spectral.eval φ T ≤ C * (N : ℝ) ^ a)
    (φ : PolMul.Spectral ℂ) (n : ℕ+) (T : KTensor ℂ (fun _ : Fin 3 => n)) :
    PolMul.Spectral.eval φ T ≤ (n : ℝ) ^ a := by
  have hn0 : (0 : ℝ) < n := by positivity
  have hnp : 0 < (n : ℝ) ^ a := Real.rpow_pos_of_pos hn0 a
  have hpow (k : ℕ) : (PolMul.Spectral.eval φ T) ^ k ≤
      (C * (2 : ℝ) ^ a) * ((n : ℝ) ^ a) ^ k := by
    let l := Nat.log 2 ((n : ℕ) ^ k) + 1
    let N : ℕ+ := ⟨2 ^ l, by positivity⟩
    have hsize : (n : ℕ) ^ k ≤ (N : ℕ) :=
      (Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) ((n : ℕ) ^ k)).le
    have hupper : (N : ℕ) ≤ 2 * (n : ℕ) ^ k := by
      dsimp [N, l]
      rw [pow_succ, mul_comm]
      exact Nat.mul_le_mul_left 2 (Nat.pow_log_le_self 2 (pow_ne_zero k n.ne_zero))
    have hpad : ∀ i : Fin 3, ((fun _ : Fin 3 => n ^ k) i : ℕ) ≤
        ((fun _ : Fin 3 => N) i : ℕ) := by
      intro i
      simpa using! hsize
    let S := PolMul.kronPow T k
    have hmono := PolMul.Superadditivity.eval_restricts φ (reembed_restricts_to hpad S)
    have hb := hbound φ l N rfl (reembed hpad S)
    have hupperR : (N : ℝ) ≤ 2 * (n : ℝ) ^ k := by exact_mod_cast hupper
    have hc := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ N) hupperR ha) hC
    have he : C * (2 * (n : ℝ) ^ k) ^ a = (C * (2 : ℝ) ^ a) * ((n : ℝ) ^ a) ^ k := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (by positivity)]
      rw [← Real.rpow_natCast, ← Real.rpow_mul hn0.le,
        ← Real.rpow_natCast, ← Real.rpow_mul hn0.le]
      rw [mul_comm (k : ℝ) a]
      ring
    rw [he] at hc
    have heval : PolMul.Spectral.eval φ S = (PolMul.Spectral.eval φ T) ^ k := eval_kronPow φ T k
    rw [heval] at hmono
    exact hmono.trans (hb.trans hc)
  by_contra hnot
  have hratio : 1 < PolMul.Spectral.eval φ T / (n : ℝ) ^ a :=
    (one_lt_div hnp).2 (lt_of_not_ge hnot)
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (C * (2 : ℝ) ^ a) hratio
  have hle : (PolMul.Spectral.eval φ T / (n : ℝ) ^ a) ^ k ≤ C * (2 : ℝ) ^ a := by
    rw [div_pow]
    exact (div_le_iff₀ (pow_pos hnp k)).2 (hpow k)
  exact (not_lt_of_ge hle) hk

lemma alpha0_nonneg : 0 ≤ alpha0 := by
  have hg := codeG_pos (3 / 4)
  have he : codeG (3 / 4) = Real.logb 2 (1 + (2 : ℝ) ^ (3 / 4 : ℝ)) := by
    norm_num [codeG]
  rw [he] at hg
  dsimp [alpha0]
  linarith

/-- The exact Route 1 exponent holds in every positive integer format. -/
theorem all_dimensions (n : ℕ+) (T : KTensor ℂ (fun _ : Fin 3 => n)) :
    asympRank T ≤ (n : ℝ) ^ alpha0 := by
  apply OM.NNN.asympRank_le_of_spectral_bound T _ (by positivity)
  intro φ
  exact spectral_power_padding_transfer alpha0_nonneg (by norm_num : (0 : ℝ) ≤ 2)
    dyadic_spectral φ n T

end OM.NNN8
