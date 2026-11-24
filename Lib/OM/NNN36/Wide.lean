import Lib.OM.NNN36.Flattening
import PLATFORM.Statements.«R115.3»

namespace OM.NNN36

open Semicontinuity P2M.R115

theorem asympRank_le_first_two {d : Fin 3 → ℕ+} (T : KTensor ℂ d) :
    asympRank T ≤ (((d 0 : ℕ) * (d 1 : ℕ) : ℕ) : ℝ) := by
  have h := regularize_le_F1 (tensorRankAdmissible ℂ (by decide : 1 ≤ 3) d) T
  change asympRank T ≤ (tensorRank (regroupingMap d 1 (tensorPow (F := ℂ) 1 T)) : ℝ) at h
  apply h.trans (Nat.cast_le.mpr ?_)
  simpa [formatPow] using tensorRank_le_first_two (regroupingMap d 1 (tensorPow (F := ℂ) 1 T))

theorem format_bounds (n₁ n₂ n₃ : ℕ+) :
    ((min (n₃ : ℕ) ((n₁ : ℕ)*(n₂ : ℕ)) : ℕ) : ℝ) ≤ formatRankSup n₁ n₂ n₃ ∧
      formatRankSup n₁ n₂ n₃ ≤ (((n₁ : ℕ)*(n₂ : ℕ) : ℕ) : ℝ) := by
  let d := PolMul.fmt n₁ n₂ n₃
  let m := min (n₃ : ℕ) ((n₁ : ℕ)*(n₂ : ℕ))
  let ranks := Set.range fun T : KTensor ℂ d => asympRank T
  have upper : ∀ t ∈ ranks, t ≤ (((n₁ : ℕ)*(n₂ : ℕ) : ℕ) : ℝ) := by
    rintro _ ⟨T,rfl⟩
    exact asympRank_le_first_two T
  obtain ⟨T,hT⟩ := exists_third_flatRank_ge (F := ℂ) (d := d) m (min_le_right ..) (min_le_left ..)
  have lower : (m : ℝ) ≤ asympRank T :=
    (Nat.cast_le.mpr hT).trans (flatRank_le_asympRank T 2)
  exact ⟨lower.trans (le_csSup ⟨_,upper⟩ ⟨T,rfl⟩), csSup_le (Set.range_nonempty _) upper⟩

theorem formatRankSup_pos (n₁ n₂ n₃ : ℕ+) : 0 < formatRankSup n₁ n₂ n₃ :=
  (Nat.cast_pos.mpr (lt_min n₃.pos (Nat.mul_pos n₁.pos n₂.pos))).trans_le (format_bounds ..).1

theorem proof_R115_3 : S_R115_3 := by
  intro n₁ n₂ n₃ _ _ hlog
  have hp : 0 < (n₁ : ℝ) * (n₂ : ℝ) := by positivity
  rw [← Real.logb_mul (by positivity : (n₁ : ℝ) ≠ 0) (by positivity : (n₂ : ℝ) ≠ 0)] at hlog
  have hprod : (n₁ : ℕ) * (n₂ : ℕ) ≤ (n₃ : ℕ) := by
    exact_mod_cast (Real.logb_le_logb one_lt_two hp (by positivity)).mp hlog
  obtain ⟨hlo, hhi⟩ := format_bounds n₁ n₂ n₃
  rw [min_eq_right hprod] at hlo
  simpa only [Nat.cast_mul] using le_antisymm hhi hlo

end OM.NNN36

