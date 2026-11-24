import Lib.OM.NNN34.NetworkPricing
import Lib.OM.NNN32.FourSums

/-! # Inserting a three-tensor of arbitrary format in a four-output network -/

noncomputable section
open scoped Classical
namespace OM.Formats

open NNN32 NNN32.FourNetwork NNN34 AsymptoticSpectrumDuality Semicontinuity

/-- Padding only changes the index set on which the network reads a local tensor.
The resulting charge is half the log asymptotic rank times the perimeter. -/
theorem insert_price {V : Type} [Fintype V] {φ : AsymptoticSpectrum fourPreorder}
    {τ : Fin 4 → V} {d : V → V → ℝ} (hd : Minimal φ τ d) {f : Fin 4 → ℕ+}
    (N : FourNetwork V f) (hN : N.Local τ) {g : Fin 3 → ℕ+} (T : KTensor ℂ g)
    (p : Fin 3 → V) (read : (i : Fin 3) → Env N → Fin (g i))
    (hr : ∀ i, N.graph.DepAt (p i) (read i)) :
    let Z : KTensor ℂ f := fun a => ∑ x : Env N,
      (∏ i, N.out i x (a i)) * (∏ k, N.graph.F k x) * T (fun i => read i x)
    0 < fourValue φ Z → Real.logb 2 (fourValue φ Z) ≤ N.graph.cost d +
      Real.logb 2 (asympRank T) / 2 * (d (p 0) (p 1) + d (p 1) (p 2) + d (p 2) (p 0)) := by
  intro Z hv
  let D : ℕ+ := max 2 (max (g 0) (max (g 1) (g 2)))
  have hD : 2 ≤ D := le_max_left ..
  have fit (i : Fin 3) : (g i : ℕ) ≤ (D : ℕ) := by
    change g i ≤ D
    apply le_trans _ (le_max_right ..)
    fin_cases i
    · exact le_max_left ..
    · exact (le_max_left ..).trans (le_max_right ..)
    · exact (le_max_right ..).trans (le_max_right ..)
  let U := reembed (d'' := fun _ => D) fit T
  let r (i : Fin 3) (x : Env N) : Fin (D : ℕ) := (read i x).castLE (fit i)
  have eval (x : Env N) : U (fun i => r i x) = T (fun i => read i x) := by
    dsimp only [U, reembed]
    rw [dite_eq_left (show ∀ i, (r i x).val < (g i : ℕ) from fun i => (read i x).isLt)]
    rfl
  have hu : U ≠ 0 := by
    intro he
    have hZ : Z = 0 := by
      funext a
      change (∑ x : Env N, _ * _ * T (fun i => read i x)) = 0
      simp only [← eval,he,Pi.zero_apply,mul_zero,Finset.sum_const_zero]
    rw [hZ,fourValue_zero] at hv
    exact (lt_irrefl _ hv)
  have pU : asympRank U = asympRank T :=
    Restricts.asympRank_eq_of_equiv (restricts_reembed fit T) (reembed_restricts_to fit T)
  have hpr := (NNN34.proof_R114_14 D U hD).2.2 hu
  rw [pU] at hpr
  have hdR : (1:ℝ) < (D:ℕ) := by exact_mod_cast (show 1 < (D:ℕ) from hD)
  have hcost : P2M.R114.relativeCost U * Real.logb 2 (D:ℕ) ≤ Real.logb 2 (asympRank T)/2 := by
    have hh := mul_le_mul_of_nonneg_left hpr (Real.logb_pos one_lt_two hdR).le
    rw [Real.mul_logb (by positivity) hdR.ne' (by linarith)] at hh
    linarith
  let Z' : KTensor ℂ f := insertCubes N (m := 1) (d := fun _ _ => D) (fun _ => U) (fun _ => r)
  have he : Z' = Z := by
    funext a
    change (∑ x : Env N, _ * _ * ∏ j : Fin 1, U (fun i => r i x)) = _
    simp only [Fin.prod_univ_one, eval, Z]
  have hp := NNN34.proof_R114_16 V φ τ d hd.1 hd.2.1 hd.2.2.1 hd.symm f N hN 1
    (fun _ => D) (fun _ => U) (fun _ => p) (fun _ => r) (fun _ => hD)
    (fun _ i x y h => congrArg (Fin.castLE (fit i)) (hr i x y h)) (show 0 < fourValue φ Z' by rwa [he])
  change Real.logb 2 (fourValue φ Z') ≤ _ at hp
  rw [he,Fin.sum_univ_one] at hp
  exact hp.trans (add_le_add_right (mul_le_mul_of_nonneg_right hcost
    (add_nonneg (add_nonneg (hd.2.1 _ _) (hd.2.1 _ _)) (hd.2.1 _ _))) _)

end OM.Formats
