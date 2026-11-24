import Lib.OM.NNN32.ClassCost
import PLATFORM.Statements.«R113.21»
import Foundations.AsymptoticSpectrumDuality.SpectrumDuality

/-! # Strassen comparison for the three matching tensors -/

noncomputable section

namespace OM.NNN32

open Semicontinuity AsymptoticSpectrumDuality Filter Topology

abbrev matchingClass (D : ℕ+) (i j k l : Fin 4) : TensorClass ℂ 4 :=
  TensorClass.mk ⟨_,matching D i j k l⟩

private lemma index_eq {D E : ℕ+} (x y : Fin ((D*E : ℕ+) : ℕ)) :
    x.val / E = y.val / E ∧ x.val % E = y.val % E ↔ x = y := by
  constructor
  · rintro ⟨ha,hb⟩
    apply Fin.ext
    calc
      x.val = x.val % E + (E : ℕ) * (x.val / E) := (Nat.mod_add_div _ _).symm
      _ = y.val % E + (E : ℕ) * (y.val / E) := by rw [ha,hb]
      _ = y.val := Nat.mod_add_div _ _
  · rintro rfl
    exact ⟨rfl,rfl⟩

lemma matchingClass_mul (D E : ℕ+) (i j k l : Fin 4) :
    matchingClass (D*E) i j k l = matchingClass D i j k l * matchingClass E i j k l := by
  change TensorClass.mk ⟨_,matching (D*E) i j k l⟩ =
    TensorClass.mk ⟨_,kroneckerTensor (matching D i j k l) (matching E i j k l)⟩
  congr 2
  funext x
  unfold kroneckerTensor matching
  simp only [Fin.ext_iff]
  change (if _ ∧ _ then (1:ℂ) else 0) =
    (if (x i).val / E = (x j).val / E ∧ (x k).val / E = (x l).val / E then 1 else 0) *
    (if (x i).val % E = (x j).val % E ∧ (x k).val % E = (x l).val % E then 1 else 0)
  have h₁ := (index_eq (D := D) (E := E) (x i) (x j)).trans Fin.ext_iff
  have h₂ := (index_eq (D := D) (E := E) (x k) (x l)).trans Fin.ext_iff
  split_ifs <;> simp_all

lemma matchingClass_pow (D : ℕ+) (i j k l : Fin 4) (n : ℕ) :
    matchingClass (D^n) i j k l = (matchingClass D i j k l)^n := by
  induction n with
  | zero =>
    rw [pow_zero,pow_zero,TensorClass.one_def]
    change TensorClass.mk ⟨_,matching 1 i j k l⟩ = _
    congr 2
    funext x
    have hall (s t : Fin 4) : x s = x t := by
      change (x s : Fin 1) = (x t : Fin 1)
      exact Subsingleton.elim (α := Fin 1) (x s) (x t)
    rw [matching,unitTensor,if_pos ⟨hall i j,hall k l⟩,if_pos hall]
  | succ n ih => rw [pow_succ,matchingClass_mul,ih,pow_succ]

private lemma straight_cost (D : ℕ+) : classCost (matchingClass D 0 1 2 3) ≤ (D : ℕ) ∧
    classCost (matchingClass D 0 2 1 3) ≤ (D : ℕ) := by
  classical
  let v : Index D × Index D → ℂ := fun p => if p.1=p.2 then 1 else 0
  have hr : rowMatrix (matching D 0 1 2 3) = Matrix.vecMulVec v v := by
    funext a b
    simp [rowMatrix,coeff,matching,Matrix.vecMulVec,v]
    split_ifs <;> simp_all
  have hc : colMatrix (matching D 0 2 1 3) = Matrix.vecMulVec v v := by
    funext a b
    simp [colMatrix,coeff,matching,Matrix.vecMulVec,v]
    split_ifs <;> simp_all
  have big (M : Matrix (Index D × Index D) (Index D × Index D) ℂ) : M.rank ≤ (D : ℕ)^2 := by
    simpa [sq] using M.rank_le_card_width
  have tr := Matrix.rank_vecMulVec_le v v
  have h1 : flatRank (matching D 0 1 2 3) {0,1} * flatRank (matching D 0 1 2 3) {0,2} ≤ (D : ℕ)^2 := by
    rw [← rowMatrix_rank,← colMatrix_rank,hr]
    simpa using Nat.mul_le_mul tr (big _)
  have h2 : flatRank (matching D 0 2 1 3) {0,1} * flatRank (matching D 0 2 1 3) {0,2} ≤ (D : ℕ)^2 := by
    rw [← rowMatrix_rank,← colMatrix_rank,hc]
    simpa using Nat.mul_le_mul (big _) tr
  constructor <;> apply ((expansion_isLeast _).2 (weight_mem_costs _)).trans <;>
    apply (Real.sqrt_le_iff).2 <;> constructor <;> first | positivity | exact_mod_cast h1 | exact_mod_cast h2

private lemma spectral_cost {D : ℕ+} (hD : 2 ≤ D) (h : spectralFourPoint) :
    ((D : ℕ) : ℝ)^gamma ≤ 2*(D : ℕ) := by
  let p := tensorStrassenPreorder (F := ℂ) (k := 4) (by decide +kernel)
  let X := matchingClass D 0 3 1 2
  let H := matchingClass D 0 1 2 3
  let V := matchingClass D 0 2 1 3
  have hcmp : AsympRel p X (H+V) := by
    apply (StrassenPreorder.asympRel_iff_forall_spectrum p _ _).2
    intro φ
    rw [show AsymptoticSpectrum.eval p (H+V) φ = _ + _ from φ.map_add H V]
    exact (h D φ).trans (max_le (le_add_of_nonneg_right (φ.nonneg V)) (le_add_of_nonneg_left (φ.nonneg H)))
  obtain ⟨f,hr,hf⟩ := (AsympRel_iff_tendsto p X (H+V)).1 hcmp
  let d : ℝ := D
  have hd2 : 2 ≤ d := by dsimp [d]; exact_mod_cast hD
  have hd0 : 0 < d := by linarith
  have hx : classCost (H+V) ≤ 2*d := (classCost_add H V).trans (by linarith [(straight_cost D).1,(straight_cost D).2] : _)
  have hn (n : ℕ) (hn : 1 ≤ n) : (d^gamma)^n ≤ (2*d)^n * (f n : ℝ) := by
    have hd : 1 < d^n := one_lt_pow₀ (by linarith) (by omega)
    have hp : (((D^n : ℕ+) : ℕ) : ℝ) = d^n := by simp [d]
    have hpow : (2 : ℕ+) ≤ D^n := by
      have hh : (1:ℝ) < (((D^n : ℕ+) : ℕ) : ℝ) := hp ▸ hd
      exact_mod_cast (show (1:ℕ) < ((D^n : ℕ+) : ℕ) by exact_mod_cast hh)
    have hw := gamma_le_base (D^n) hpow
    have hpw : 0 < W (D^n) := (by rw [hp]; positivity : 0 < (((D^n : ℕ+) : ℕ) : ℝ)).trans_le (size_le_W _)
    rw [hp] at hw
    have hlow := (Real.le_logb_iff_rpow_le hd hpw).1 hw
    rw [← Real.rpow_natCast_mul hd0.le, mul_comm,Real.rpow_mul_natCast hd0.le] at hlow
    have hxc : W (D^n) = classCost (X^n) := by
      rw [← matchingClass_pow]; rfl
    rw [hxc] at hlow
    exact hlow.trans ((classCost_mono _ _ (hr n hn)).trans ((classCost_mul _ _).trans
      (mul_le_mul ((classCost_pow _ _).trans (pow_le_pow_left₀ (classCost_nonneg _) hx _))
        (classCost_nat _) (classCost_nonneg _) (by positivity))))
  have hle : ∀ᶠ n : ℕ in atTop, d^gamma ≤ 2*d*(f n : ℝ)^(1/(n:ℝ)) := by
    filter_upwards [eventually_ge_atTop 1] with n hpos
    have h' := Real.rpow_le_rpow (by positivity) (hn n hpos) (by positivity : 0 ≤ (1/(n:ℝ)))
    rw [one_div]
    rwa [Real.mul_rpow (by positivity) (by positivity),one_div,Real.pow_rpow_inv_natCast (by positivity) (by omega),
      Real.pow_rpow_inv_natCast (by positivity) (by omega)] at h'
  simpa [d] using ge_of_tendsto ((tendsto_const_nhds (x := 2*d)).mul hf) hle

theorem proof_R113_21 : S_R113_21 := by
  intro h
  apply le_antisymm _ gamma_ge_one
  have hlim : Tendsto (fun D : ℕ+ => Real.log 2 / Real.log (D : ℕ) + 1) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds.div_atTop log_side_atTop).add (tendsto_const_nhds (x := (1:ℝ)))
  apply ge_of_tendsto hlim
  filter_upwards [eventually_ge_atTop (2 : ℕ+)] with D hD
  have hd2 : (2:ℝ) ≤ (D : ℕ) := by exact_mod_cast hD
  have hd : (1:ℝ) < (D : ℕ) := by linarith
  have h' := (Real.le_logb_iff_rpow_le hd (by positivity)).2 (spectral_cost hD h)
  rwa [Real.logb_mul (by norm_num) (by positivity),Real.logb_self_eq_one hd] at h'

end OM.NNN32
