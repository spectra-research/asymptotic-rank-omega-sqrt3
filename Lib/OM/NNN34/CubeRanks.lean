import Lib.OM.NNN30.Main
import PLATFORM.Statements.«R114.23»
import PLATFORM.Statements.«R114.24»

/-! # The uniform exponent and the concrete asymptotic rank of a three-tensor -/

namespace OM.NNN34

open Semicontinuity AsymptoticSpectrumDuality P2M.R114

/-- Regrouping identifies every term in the two infima defining asymptotic rank. -/
theorem class_asympRank_eq {d : Fin 3 → ℕ+} (T : KTensor ℂ d) :
    (PolMul.OmegaBridge.pF ℂ).asympRank (TensorClass.mk ⟨d, T⟩) = asympRank T := by
  refine le_antisymm ?_ (Foundations.AsympRankBridge.asympRank_le_strassen (by norm_num) T)
  let p := PolMul.OmegaBridge.pF ℂ
  let a : TensorClass ℂ 3 := TensorClass.mk ⟨d, T⟩
  change p.asympRank a ≤ ⨅ n : ℕ+,
    (tensorRank (regroupingMap d n (tensorPow (F := ℂ) n T)) : ℝ) ^ (1 / ((n : ℕ) : ℝ))
  apply le_ciInf
  intro n
  have hr := PolMul.OmegaBridge.strassenRank_mk_eq_tensorRank
    (regroupingMap d n (tensorPow (F := ℂ) n T))
  rw [Foundations.AsympRankBridge.mk_regrouping_pow] at hr
  rw [← hr]
  exact csInf_le (p.asympRankSet_bddBelow a) ⟨(n : ℕ), n.pos, rfl⟩

theorem spectral_le_concrete {d : Fin 3 → ℕ+} (φ : PolMul.Spectral ℂ) (T : KTensor ℂ d) :
    φ.eval T ≤ asympRank T := by
  rw [← class_asympRank_eq]
  exact (PolMul.OmegaBridge.pF ℂ).spectralPoint_le_asympRank φ _

private theorem cube_le (n : ℕ+) (T : KTensor ℂ (fun _ : Fin 3 => n)) :
    asympRank T ≤ ((n : ℕ) : ℝ) ^ (3 : ℕ) := by
  let p := PolMul.OmegaBridge.pF ℂ
  let a : TensorClass ℂ 3 := TensorClass.mk ⟨_, T⟩
  have hu : (p.rank a : ℝ) ∈ p.asympRankSet a := ⟨1, by simp, by simp⟩
  have hr : p.rank a = tensorRank T := PolMul.OmegaBridge.strassenRank_mk_eq_tensorRank T
  have h := tensorRank_le_prod_dims (by decide +kernel : 1 ≤ 3) T
  rw [← class_asympRank_eq]
  refine (csInf_le (p.asympRankSet_bddBelow a) hu).trans ?_
  rw [hr]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h
  exact_mod_cast h

private theorem rank_bdd (n : ℕ+) : BddAbove
    (Set.range fun T : KTensor ℂ (fun _ : Fin 3 => n) => asympRank T) :=
  ⟨_, by rintro _ ⟨T, rfl⟩; exact cube_le n T⟩

private theorem cubeRankSup_pos (n : ℕ+) : 0 < cubeRankSup n := by
  let T : KTensor ℂ (fun _ : Fin 3 => n) := fun _ => 1
  have hT : T ≠ 0 := fun h => one_ne_zero (congrFun h (fun _ => ⟨0, n.pos⟩))
  obtain ⟨φ, _⟩ := (PolMul.SpectralFacts.proof_SP_1 ℂ).1
  exact zero_lt_one.trans_le (((PolMul.SpectralFacts.proof_SP_4 ℂ φ T hT).trans
    (spectral_le_concrete φ T)).trans (le_csSup (rank_bdd n) ⟨T, rfl⟩))

private theorem side_gt {n : ℕ+} (hn : 2 ≤ n) : (1 : ℝ) < ((n : ℕ) : ℝ) := by
  have h : 2 ≤ (n : ℕ) := hn
  exact_mod_cast (show 1 < (n : ℕ) by omega)

private theorem cube_logs_bdd : BddAbove
    {b : ℝ | ∃ n : ℕ+, 2 ≤ n ∧ b = Real.logb ((n : ℕ) : ℝ) (cubeRankSup n)} := by
  refine ⟨3, ?_⟩
  rintro _ ⟨n, hn, rfl⟩
  apply (Real.logb_le_iff_le_rpow (side_gt hn) (cubeRankSup_pos n)).2
  rw [show (3 : ℝ) = (3 : ℕ) by norm_num, Real.rpow_natCast]
  exact csSup_le (Set.range_nonempty _) (by rintro _ ⟨T, rfl⟩; exact cube_le n T)

theorem proof_R114_23 : S_R114_23 := by
  intro b
  constructor
  · intro hb n T
    by_cases hn : 2 ≤ n
    · have hl : Real.logb ((n : ℕ) : ℝ) (cubeRankSup n) ≤ beta :=
        le_csSup cube_logs_bdd ⟨n, hn, rfl⟩
      exact (le_csSup (rank_bdd n) ⟨T, rfl⟩).trans
        ((Real.logb_le_iff_le_rpow (side_gt hn) (cubeRankSup_pos n)).1 (hl.trans hb))
    · have h : (n : ℕ) = 1 := by have := n.pos; change ¬ 2 ≤ (n : ℕ) at hn; omega
      simpa [h] using cube_le n T
  · intro hb
    unfold beta
    refine csSup_le ?_ ?_
    · exact ⟨_, (2 : ℕ+), le_rfl, rfl⟩
    rintro _ ⟨n, hn, rfl⟩
    exact (Real.logb_le_iff_le_rpow (side_gt hn) (cubeRankSup_pos n)).2
      (csSup_le (Set.range_nonempty _) (by rintro _ ⟨T, rfl⟩; exact hb n T))

theorem proof_R114_24 : S_R114_24 := by
  refine ⟨?_, (proof_R114_23 _).2 NNN30.asympRank_le_omega_div_sqrt_three⟩
  let M := PolMul.matMul (F := ℂ) 2 2 2
  have hf : PolMul.fmt (2*2) (2*2) (2*2) = (fun _ : Fin 3 => (4 : ℕ+)) := by
    funext i
    fin_cases i <;> rfl
  have bound {d : Fin 3 → ℕ+} (h : d = (fun _ => (4 : ℕ+))) (T : KTensor ℂ d) :
      asympRank T ≤ (4 : ℝ) ^ beta := by
    subst d
    exact (proof_R114_23 beta).1 le_rfl 4 T
  have hm := bound hf M
  rw [← class_asympRank_eq] at hm
  change (PolMul.OmegaBridge.pF ℂ).asympRank (PolMul.OmegaBridge.mmClass ℂ) ≤ _ at hm
  rw [← PolMul.two_rpow_omegaF] at hm
  have h4 : (4 : ℝ) = (2 : ℝ) ^ (2 : ℝ) := by norm_num
  rw [h4, ← Real.rpow_mul (by norm_num), Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)] at hm
  change PolMul.omegaF ℂ ≤ 2 * beta at hm
  linarith

end OM.NNN34

