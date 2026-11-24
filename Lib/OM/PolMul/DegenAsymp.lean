/- Adapted from PolMul/DegenAsymp.lean of an earlier formalisation
   (commit 51c6e6b6e8b8d7226c6a828dba618ae1de5b5f8a).
   Uses Foundations tensor definitions; declarations are renamed under OM. -/
import Lib.OM.PolMul.DegenAsymp.Powers
import Lib.OM.PolMul.DegenAsymp.Rate
import Lib.OM.PolMulStatements.SP_2

/-!
# Degeneration implies asymptotic restriction

Strassen (1988), Theorem 3.1: polynomial coefficient extraction produces
`(q*n+1)²` copies of the source's `n`-th power. This overhead has root limit
(and positive-index root infimum) one. No interpolation or field extension
is used.
-/

namespace OM.PolMul

open Semicontinuity AsymptoticSpectrumDuality

universe u
variable {F : Type u} [Field F]

namespace DegenAsymp

lemma unit_class (m : ℕ+) :
    (TensorClass.mk ⟨_, unitTensor F (k := 3) m⟩ : TensorClass F 3) = (m : ℕ) := by
  rw [natCast_eq_unitClass, unitClass, dif_pos m.pos]
  cases m
  rfl

private lemma class_pow_succ {d : Fin 3 → ℕ+} (T : T3 F d) (n : ℕ) :
    (TensorClass.mk ⟨d, T⟩ : TensorClass F 3) ^ (n + 1) = TensorClass.mk ⟨_, kronPowNat T n⟩ := by
  induction n with
  | zero => exact pow_one _
  | succ n ih => rw [pow_succ, ih, TensorClass.mk_mul]; rfl

/-- Exact restriction of class powers with quadratic overhead. -/
lemma Leading.class_power_restricts {dT dS : Fin 3 → ℕ+}
    {T : T3 F dT} {S : T3 F dS} {q : ℕ} (h : Leading T S q)
    (n : ℕ) (hn : 1 ≤ n) :
    (tensorStrassenPreorder (F := F) (k := 3) (by norm_num)).rel
      (TensorClass.mk ⟨dT, T⟩ ^ n)
      (TensorClass.mk ⟨dS, S⟩ ^ n * (((q*n+1)^2 : ℕ) : TensorClass F 3)) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  rw [class_pow_succ, class_pow_succ, mul_comm, natCast_eq_unitClass, unitClass,
    dif_pos (by positivity : 0 < (q*(m+1)+1)^2), TensorClass.mk_mul]
  exact (h.kronPowNat m).restricts

/-- The same bound for the project's concrete, cast-based tensor powers. -/
lemma Leading.kronPow_restricts {dT dS : Fin 3 → ℕ+}
    {T : T3 F dT} {S : T3 F dS} {q : ℕ} (h : Leading T S q)
    (n : ℕ) (hn : 1 ≤ n) :
    Restricts (kronPow T n)
      (OM.PolMul.kron (kronPow S n)
        (unitTensor F (k := 3) ⟨(q*n+1)^2, pow_pos (Nat.succ_pos _) 2⟩)) := by
  let m : ℕ+ := ⟨(q*n+1)^2, pow_pos (Nat.succ_pos _) 2⟩
  have hu : (TensorClass.mk ⟨_, unitTensor F (k := 3) m⟩ : TensorClass F 3) =
      (((q*n+1)^2 : ℕ) : TensorClass F 3) := unit_class m
  have hc := h.class_power_restricts n hn
  rw [← mk_kronPow T n, ← mk_kronPow S n, ← hu, TensorClass.mk_mul] at hc
  exact hc

/-- Turn the vanishing of the lower coefficients into a common power of `X`. -/
lemma leading_of_coeff {dT dS : Fin 3 → ℕ+} {T : T3 F dT} {S : T3 F dS} (q : ℕ)
    (A : ∀ i, Matrix (Fin (dT i)) (Fin (dS i)) (Polynomial F))
    (low : ∀ idx, ∀ j < q, (contraction S A idx).coeff j = 0)
    (lead : ∀ idx, (contraction S A idx).coeff q = T idx) : Leading T S q := by
  choose P hP using fun idx => Polynomial.X_pow_dvd_iff.mpr (low idx)
  refine ⟨A, P, hP, fun idx => ?_⟩
  simpa [hP idx, Polynomial.coeff_X_pow_mul'] using lead idx

/-- Spectral points preserve the inequality given by a leading coefficient. -/
lemma Leading.eval_le {dT dS : Fin 3 → ℕ+} {T : T3 F dT} {S : T3 F dS} {q : ℕ}
    (h : Leading T S q) (φ : Spectral F) : Spectral.eval φ T ≤ Spectral.eval φ S := by
  apply (StrassenPreorder.asympRel_iff_forall_spectrum _ _ _).mp _ φ
  exact ⟨_, h.class_power_restricts, quadratic_root_inf q⟩

end DegenAsymp

/-- Polynomial degeneration implies asymptotic restriction over every field. -/
theorem degen_asympRestricts {dT dS : Fin 3 → ℕ+}
    (T : T3 F dT) (S : T3 F dS) (h : Degen T S) : AsympRestricts T S := by
  obtain ⟨q, hq⟩ := DegenAsymp.leading_of_degen h
  exact ⟨(fun n => (q*n+1)^2), hq.class_power_restricts, DegenAsymp.quadratic_root_inf q⟩

namespace SpectralFacts

/-- Spectral points are monotone under polynomial degeneration (SP.2). -/
theorem proof_SP_2 : OM_S_SP_2 := by
  intro F _ φ dT dS T S h
  exact (StrassenPreorder.asympRel_iff_forall_spectrum
    (tensorStrassenPreorder (F := F) (k := 3) (by norm_num))
    (TensorClass.mk ⟨dT, T⟩) (TensorClass.mk ⟨dS, S⟩)).mp
      (degen_asympRestricts T S h) φ

end SpectralFacts
end OM.PolMul

