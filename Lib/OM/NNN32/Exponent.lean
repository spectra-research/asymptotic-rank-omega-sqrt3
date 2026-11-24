import Lib.OM.NNN32.Growth

namespace OM.NNN32

open Semicontinuity OM.NNN30 OM.NNN30.Net Filter Topology

private lemma circle_linear {x y ε : ℝ} (he : 0 < ε) (h : x^2+y^2 ≤ 4+ε^2/2) :
    x+y ≤ 2*Real.sqrt 2 + ε := by
  nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num),Real.sqrt_nonneg 2,
    sq_nonneg (x-y), mul_pos (Real.sqrt_pos.2 (by norm_num : (0:ℝ)<2)) he]

theorem gamma_le_sqrt_two : gamma ≤ Real.sqrt 2 := by
  by_contra! hg
  have h108 := proof_R108_3 1 1 1 (by decide +kernel) (by decide +kernel)
    (by decide +kernel)
  obtain ⟨K,A,⟨C,hC⟩,hA,hr⟩ := h108
  simp only [one_mul] at hC
  let f (L : ℕ) : Index ((2 : ℕ+)^L) ≃ Fin (2^(1*L)) := finCongr (by simp [Index])
  let B (L : ℕ) (j : Fin (K L)) : Four ((2 : ℕ+)^L) :=
    fun x => A L j (f L (x 0)) (f L (x 1)) (f L (x 2)) (f L (x 3))
  have hs L : ∑ j, B L j = crossing ((2 : ℕ+)^L) := by
    funext x
    rw [Finset.sum_apply]
    simpa [B,crossing,matching] using hA L (f L (x 0)) (f L (x 1)) (f L (x 2)) (f L (x 3))
  have hK L : 0 < K L := by
    by_contra! h
    have : IsEmpty (Fin (K L)) := by rw [Nat.eq_zero_of_le_zero h]; infer_instance
    exact crossing_ne_zero _ ((hs L).symm.trans (Finset.sum_of_isEmpty _))
  have hCp : 0 < C := by
    have := hC 0
    norm_num at this
    exact (Nat.cast_pos.2 (hK 0)).trans_le this
  have ht : Tendsto (fun L : ℕ => Real.logb 2 (K L)/L) atTop (𝓝 0) := by
    apply squeeze_zero (fun L => div_nonneg (Real.logb_nonneg (by norm_num)
      (by exact_mod_cast hK L)) (Nat.cast_nonneg L))
      (fun L => div_le_div_of_nonneg_right (Real.logb_le_logb_of_le (by norm_num)
        (Nat.cast_pos.2 (hK L)) (hC L)) (Nat.cast_nonneg L))
    simpa using (tendsto_count (q := 1) (by decide +kernel) (fun _ : Unit => C) (fun _ => hCp))
  obtain ⟨D,hD,s,hcost,hcheap⟩ := saving_of_dyadic (t := gamma) (κ := 2*Real.sqrt 2)
    (by linarith) K B hs ht (fun ε he => by
      obtain ⟨L₀,hL₀⟩ := hr (ε^2/2) (by positivity)
      filter_upwards [eventually_ge_atTop (max 1 L₀)] with L hL
      intro j hj
      have hA' : A L j ≠ 0 := fun h => hj (by funext x; simp [B,h])
      have hh := hL₀ L ((le_max_right _ _).trans hL) j hA'
      norm_num at hh
      have hc := circle_linear he hh
      rw [← rowMatrix_rank,← colMatrix_rank]
      apply (div_le_iff₀ (by exact_mod_cast (le_max_left 1 L₀).trans hL : (0:ℝ)<L)).1
      rw [add_div]
      let r := Matrix.of fun (i j : Fin (2^(1*L)) × Fin (2^(1*L))) => A L ‹Fin (K L)› i.1 i.2 j.1 j.2
      let s := Matrix.of fun (i j : Fin (2^(1*L)) × Fin (2^(1*L))) => A L ‹Fin (K L)› i.1 j.1 i.2 j.2
      let e := (f L).prodCongr (f L)
      change Real.logb 2 (r.submatrix e e).rank / L + Real.logb 2 (s.submatrix e e).rank / L ≤ _
      rw [Matrix.rank_submatrix,Matrix.rank_submatrix]
      exact hc)
  exact (lt_irrefl gamma) (gamma_lt_of_saving hD hcost hcheap)

theorem proof_R113_15 : S_R113_15 := ⟨tendsto_W,gamma_ge_one,gamma_le_sqrt_two⟩

end OM.NNN32
