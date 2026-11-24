import Lib.OM.NNN32.Splits
import Lib.OM.NNN32.Dyadic
import Lib.OM.NNN30.RectMain
import PLATFORM.Statements.«R113.15»

/-! # The finite-base infimum formula and the upper bound from the rectangular crossing estimate -/

noncomputable section

namespace OM.NNN32

open Semicontinuity Filter Topology

def tensorCost {d : Fin 4 → ℕ+} (T : KTensor ℂ d) := sInf (expansionCosts T)

lemma cost_le_sum {d : Fin 4 → ℕ+} {ι : Type*} [Fintype ι] (A : ι → KTensor ℂ d) :
    tensorCost (∑ i, A i) ≤ ∑ i, weight (A i) := by
  classical
  let e := (Fintype.equivFin ι).symm
  exact (expansion_isLeast _).2 ⟨_,fun j => A (e j),e.sum_comp _,(e.sum_comp (fun i => weight (A i))).symm⟩

lemma weight_kron {d e : Fin 4 → ℕ+} (T : KTensor ℂ d) (S : KTensor ℂ e) :
    weight (kroneckerTensor T S) ≤ weight T * weight S := by
  unfold weight
  rw [← Real.sqrt_mul (by positivity)]
  apply Real.sqrt_le_sqrt
  calc
    _ ≤ ((flatRank T {0,1} : ℝ) * flatRank S {0,1}) * ((flatRank T {0,2} : ℝ)*flatRank S {0,2}) := by
      exact_mod_cast Nat.mul_le_mul (flatRank_kron_mul_ge T S {0,1}) (flatRank_kron_mul_ge T S {0,2})
    _ = _ := by ring

lemma W_le_power {D E : ℕ+} (n : ℕ) (h : (E : ℕ) ≤ (D : ℕ)^(n+1)) : W E ≤ W D ^ (n+1) := by
  classical
  obtain ⟨m,B,hB,hc⟩ := (expansion_isLeast (crossing D)).1
  change W D = ∑ j, weight (B j) at hc
  let A (w : Fin (n+1) → Fin m) := pull (powerIndex n h) (kronWord B n w)
  have hs : ∑ w, A w = crossing E := by
    rw [← pull_crossing_power n h, ← hB, ← sum_kronWord]
    funext x
    simp [A,pull]
  have hword (p : ℕ) (w : Fin (p+1) → Fin m) : weight (kronWord B p w) ≤ ∏ i, weight (B (w i)) := by
    induction p with
    | zero => simp [kronWord]
    | succ p ih =>
      rw [kronWord,Fin.prod_univ_succ,mul_comm (weight (B _))]
      exact (weight_kron _ _).trans (mul_le_mul_of_nonneg_right (ih _) (Real.sqrt_nonneg _))
  change tensorCost (crossing E) ≤ _
  rw [← hs,hc,Fintype.sum_pow]
  exact (cost_le_sum A).trans (Finset.sum_le_sum fun w _ => (weight_pull_le _ _).trans (hword n w))

def baseExponents := {g : ℝ | ∃ D : ℕ+, 2 ≤ D ∧ g = Real.logb ((D : ℕ) : ℝ) (W D)}

lemma base_nonempty : baseExponents.Nonempty := ⟨_,2,le_rfl,rfl⟩

lemma base_lower : (1 : ℝ) ∈ lowerBounds baseExponents := by
  rintro _ ⟨D,hD,rfl⟩
  have h2 : (2 : ℝ) ≤ (D : ℕ) := by exact_mod_cast hD
  have h1 : (1 : ℝ) < (D : ℕ) := by linarith
  calc
    1 = Real.logb ((D : ℕ) : ℝ) (D : ℕ) := (Real.logb_self_eq_one h1).symm
    _ ≤ _ := Real.logb_le_logb_of_le h1 (by linarith) (size_le_W _)

lemma gamma_le_base (D : ℕ+) (hD : 2 ≤ D) : gamma ≤ Real.logb ((D : ℕ) : ℝ) (W D) :=
  csInf_le (s := baseExponents) ⟨_,base_lower⟩ ⟨D,hD,rfl⟩

lemma gamma_ge_one : 1 ≤ gamma := le_csInf base_nonempty base_lower

lemma log_side_atTop : Tendsto (fun D : ℕ+ => Real.log ((D : ℕ) : ℝ)) atTop atTop :=
  Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp tendsto_PNat_val_atTop_atTop)

lemma tendsto_W : Tendsto (fun D : ℕ+ => Real.logb ((D : ℕ) : ℝ) (W D)) atTop (𝓝 gamma) := by
  apply tendsto_order.2
  constructor
  · intro r hr
    filter_upwards [eventually_ge_atTop (2 : ℕ+)] with D hD using hr.trans_le (gamma_le_base D hD)
  · intro r hr
    obtain ⟨_,⟨b,hb,rfl⟩,hlt⟩ := exists_lt_of_csInf_lt base_nonempty hr
    let g := Real.logb ((b : ℕ) : ℝ) (W b)
    have hbr : (2 : ℝ) ≤ (b : ℕ) := by exact_mod_cast hb
    have hb1 : (1 : ℝ) < (b : ℕ) := by linarith
    have hb0 : (0 : ℝ) < (b : ℕ) := by linarith
    have hwb : (1 : ℝ) ≤ W b := le_trans (by linarith) (size_le_W b)
    have hlogw := Real.log_nonneg hwb
    have hlim : Tendsto (fun D : ℕ+ => g + Real.log (W b) / Real.log (D : ℕ)) atTop (𝓝 g) := by
      simpa using (tendsto_const_nhds (x := g)).add (tendsto_const_nhds.div_atTop log_side_atTop)
    filter_upwards [eventually_ge_atTop (2 : ℕ+), (tendsto_order.1 hlim).2 r hlt] with D hD hupper
    have hdr : (2 : ℝ) ≤ (D : ℕ) := by exact_mod_cast hD
    have hd1 : (1 : ℝ) < (D : ℕ) := by linarith
    have hd0 : (0 : ℝ) < (D : ℕ) := by linarith
    let v := Real.logb ((b : ℕ) : ℝ) (D : ℕ)
    let n := ⌊v⌋₊
    have hside : (D : ℕ) ≤ (b : ℕ)^(n+1) := by
      have h : (D : ℕ) ≤ ((b : ℕ) : ℝ)^((n : ℝ)+1) :=
        (Real.logb_le_iff_le_rpow hb1 hd0).1 (Nat.lt_floor_add_one v).le
      rw [← Nat.cast_one (R := ℝ), ← Nat.cast_add,Real.rpow_natCast] at h
      exact_mod_cast h
    have hw := W_le_power n hside
    have hw0 : 0 < W D := hd0.trans_le (size_le_W _)
    have hh := Real.log_le_log hw0 hw
    rw [Real.log_pow,Nat.cast_add,Nat.cast_one] at hh
    have hv : (n : ℝ) ≤ v := Nat.floor_le (Real.logb_nonneg hb1 hd1.le)
    apply lt_of_le_of_lt _ hupper
    change Real.log (W D) / Real.log (D : ℕ) ≤ _
    rw [div_le_iff₀ (Real.log_pos hd1), add_mul, div_mul_cancel₀ _ (Real.log_pos hd1).ne']
    have he : g * Real.log (D : ℕ) = v * Real.log (W b) := by unfold g v Real.logb; ring
    rw [he]
    linarith [mul_le_mul_of_nonneg_right hv hlogw]

lemma gamma_lt_of_saving {D : ℕ+} (hD : 2 ≤ D) {c t : ℝ} (h : c ∈ expansionCosts (crossing D))
    (hs : c < ((D : ℕ) : ℝ)^t) : gamma < t := by
  have h2 : (2 : ℝ) ≤ (D : ℕ) := by exact_mod_cast hD
  have h1 : (1 : ℝ) < (D : ℕ) := by linarith
  apply (gamma_le_base D hD).trans_lt
  exact (Real.logb_lt_iff_lt_rpow h1 ((by linarith : (0:ℝ) < (D : ℕ)).trans_le (size_le_W _))).2
    (((expansion_isLeast _).2 h).trans_lt hs)

end OM.NNN32
