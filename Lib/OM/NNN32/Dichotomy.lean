import Lib.OM.NNN32.Comparison
import Lib.OM.NNN32.Composition
import Lib.OM.NNN32.Exponent
import PLATFORM.Statements.«R113.20»
import PLATFORM.Statements.«R113.22»
import PLATFORM.Statements.«R113.23»

/-! # From the spectral implication to the common limit and the strict finite test -/

noncomputable section

namespace OM.NNN32

open Filter Topology

private lemma one_lt_sqrt_two : 1 < Real.sqrt 2 := by
  nlinarith [Real.sq_sqrt (show 0 ≤ (2:ℝ) by norm_num),Real.sqrt_nonneg 2]

theorem dichotomy_of_comparison (hspectral : S_R113_20) : S_R113_22 := by
  classical
  let Cheap := ∃ κ : ℝ, 0 ≤ κ ∧ κ < Real.sqrt 2 ∧
    ∀ M : ℕ+, ∃ D : ℕ+, M ≤ D ∧ (P D : ℝ) ≤ ((D : ℕ) : ℝ)^κ
  let p (D : ℕ+) := Real.logb ((D : ℕ) : ℝ) (P D)
  let w (D : ℕ+) := Real.logb ((D : ℕ) : ℝ) (W D)
  let s (D : ℕ+) := Real.logb ((D : ℕ) : ℝ) (sigma D)
  let b (D : ℕ+) := Real.log 2 / Real.log (D : ℕ)
  have hb : Tendsto b atTop (𝓝 0) := tendsto_const_nhds.div_atTop log_side_atTop
  have h2 (D : ℕ+) (hD : 2 ≤ D) : (1 : ℝ) < (D : ℕ) := by
    have : (2:ℝ) ≤ (D:ℕ) := by exact_mod_cast hD
    linarith
  have hp (D : ℕ+) : 0 < (P D : ℝ) := by exact_mod_cast D.2.trans_le (size_le_P D)
  have hlow : ∀ᶠ D : ℕ+ in atTop, 1 ≤ p D := by
    filter_upwards [eventually_ge_atTop (2:ℕ+)] with D hD
    have := Real.logb_le_logb_of_le (h2 D hD) (by positivity)
      (show ((D:ℕ):ℝ) ≤ P D by exact_mod_cast size_le_P D)
    simpa [p,Real.logb_self_eq_one (h2 D hD)] using this
  have hup : ∀ᶠ D : ℕ+ in atTop, p D ≤ w D := by
    filter_upwards [eventually_ge_atTop (2:ℕ+)] with D hD
    exact Real.logb_le_logb_of_le (h2 D hD) (hp D) (P_le_cost (expansion_isLeast _).1)
  have hW : Tendsto w atTop (𝓝 gamma) := tendsto_W
  have middle : (gamma = 1 ∨ gamma = Real.sqrt 2) ∧ Tendsto p atTop (𝓝 gamma) := by
    by_cases cheap : Cheap
    · have hg : gamma = 1 := proof_R113_21 (hspectral cheap)
      exact ⟨Or.inl hg,tendsto_of_tendsto_of_tendsto_of_le_of_le' (by rw [hg]; exact tendsto_const_nhds) hW hlow hup⟩
    · have lower (r : ℝ) (hr : r < Real.sqrt 2) : ∀ᶠ D : ℕ+ in atTop, r < p D := by
        let κ := max r 0
        have hκ : κ < Real.sqrt 2 := max_lt hr (Real.sqrt_pos.2 (by norm_num))
        have hh : ¬ ∀ M : ℕ+, ∃ D : ℕ+, M ≤ D ∧ (P D : ℝ) ≤ ((D : ℕ) : ℝ)^κ :=
          fun hall => cheap ⟨κ,le_max_right _ _,hκ,hall⟩
        push Not at hh
        obtain ⟨M,hM⟩ := hh
        filter_upwards [eventually_ge_atTop M,eventually_ge_atTop (2:ℕ+)] with D hd hD
        exact (le_max_left r 0).trans_lt ((Real.lt_logb_iff_rpow_lt (h2 D hD) (hp D)).2 (hM D hd))
      have hg : gamma = Real.sqrt 2 := by
        apply le_antisymm gamma_le_sqrt_two
        apply le_of_forall_lt_imp_le_of_dense
        intro r hr
        exact ge_of_tendsto hW (by filter_upwards [lower r hr,hup] with D h₁ h₂ using h₁.le.trans h₂)
      refine ⟨Or.inr hg,tendsto_order.2 ⟨fun r hr => lower r (hg ▸ hr),?_⟩⟩
      intro r hr
      filter_upwards [(tendsto_order.1 hW).2 r hr,hup] with D hw h using h.trans_lt hw
  refine ⟨middle.1,hW,middle.2,?_⟩
  have bounds : ∀ᶠ D : ℕ+ in atTop, p D - b D ≤ s D ∧ s D ≤ p D + b D := by
    filter_upwards [eventually_ge_atTop (2:ℕ+)] with D hD
    obtain ⟨_,_,hsize,hps,hsp⟩ := proof_R113_14 D
    have hs : 0 < (sigma D : ℝ) := by exact_mod_cast D.2.trans_le hsize
    have hlog (x y : ℕ) (hx : 0 < (x:ℝ)) (hy : 0 < (y:ℝ)) (hxy : x ≤ 2*y) :
        Real.logb ((D:ℕ):ℝ) x ≤ b D + Real.logb ((D:ℕ):ℝ) y := by
      have h' := Real.logb_le_logb_of_le (h2 D hD) hx (show (x:ℝ) ≤ 2*y by exact_mod_cast hxy)
      rwa [Real.logb_mul (by norm_num) hy.ne'] at h'
    have a : p D ≤ b D + s D := hlog _ _ (hp D) hs hps
    have c : s D ≤ b D + p D := hlog _ _ hs (hp D) hsp
    constructor <;> linarith
  change Tendsto s atTop (𝓝 gamma)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' _ _ (bounds.mono fun _ h => h.1) (bounds.mono fun _ h => h.2)
  · simpa using middle.2.sub hb
  · simpa using middle.2.add hb

theorem finiteWitness_iff_gamma_lt : finiteWitness ↔ gamma < Real.sqrt 2 := by
  constructor
  · rintro ⟨D,hD,c,hc,hlt⟩
    exact gamma_lt_of_saving hD hc hlt
  · intro hg
    obtain ⟨_,⟨D,hD,rfl⟩,hs⟩ := exists_lt_of_csInf_lt base_nonempty hg
    have h2 : (2:ℝ) ≤ (D:ℕ) := by exact_mod_cast hD
    have hd : (1:ℝ) < (D:ℕ) := by linarith
    exact ⟨D,hD,W D,(expansion_isLeast _).1,
      (Real.logb_lt_iff_lt_rpow hd ((by linarith : (0:ℝ) < (D:ℕ)).trans_le (size_le_W _))).1 hs⟩

theorem finite_test_of_dichotomy (h : S_R113_22) : S_R113_23 := by
  change gamma = 1 ↔ finiteWitness
  rw [finiteWitness_iff_gamma_lt]
  exact ⟨fun h => h ▸ one_lt_sqrt_two,fun hlt => h.1.resolve_right hlt.ne⟩

end OM.NNN32
