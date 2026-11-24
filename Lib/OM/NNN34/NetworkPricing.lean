import Lib.OM.NNN34.InsertTriangles
import Lib.OM.NNN32.BondFactors
import PLATFORM.Statements.«R114.16»

/-! # Pricing simultaneous local three-tensor resources at four free outputs -/

noncomputable section
open scoped Classical

namespace OM.NNN34

open Filter Topology Semicontinuity AsymptoticSpectrumDuality NNN32 FourNetwork PolMul P2M.R114

private lemma multiplicity_rate {x : ℕ → ℕ}
    (hx : Tendsto (fun n : ℕ => (x n : ℝ)^(1/(n : ℝ))) atTop (𝓝 1)) :
    (∀ᶠ n in atTop, 0 < x n) ∧ Tendsto (fun n : ℕ => Real.logb 2 (x n) / n) atTop (𝓝 0) := by
  have hp : ∀ᶠ n in atTop, 0 < x n := by
    filter_upwards [hx.eventually (Ioi_mem_nhds zero_lt_one), eventually_ge_atTop 1] with n h hn
    by_contra! h0
    have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
    change 0 < (x n : ℝ)^(1/(n : ℝ)) at h
    rw [Nat.eq_zero_of_le_zero h0,Nat.cast_zero,Real.zero_rpow (one_div_ne_zero hn'.ne')] at h
    exact lt_irrefl _ h
  refine ⟨hp, ?_⟩
  have hl := (Real.continuousAt_logb (b := 2) (x := (1 : ℝ)) one_ne_zero).tendsto.comp hx
  rw [Real.logb_one] at hl
  apply hl.congr'
  filter_upwards [hp] with n hn
  change Real.logb 2 ((x n : ℝ)^(1/(n : ℝ))) = _
  rw [Real.logb_rpow_eq_mul_logb_of_pos (by exact_mod_cast hn)]
  ring

private theorem price_comparisons {V : Type} [Fintype V] {f : Fin 4 → ℕ+} {m : ℕ}
    {φ : AsymptoticSpectrum fourPreorder} {τ : Fin 4 → V} {δ : V → V → ℝ} (hd : Valid φ τ δ)
    (N : FourNetwork V f) (hN : N.Local τ) {D : Fin m → ℕ+}
    (U : (j : Fin m) → KTensor ℂ (fun _ : Fin 3 => D j)) (p : Fin m → Fin 3 → V)
    (r : Reads N (fun j _ => D j)) (hr : ∀ j i, N.graph.DepAt (p j i) (r j i))
    (k : ℕ+) (l : Fin m → ℕ+) (rel : ∀ j, AsympRestricts (kronPow (U j) k)
      (kronPow (matMul (F := ℂ) 2 2 2) (l j)))
    (hv : 0 < fourValue φ (insertCubes N U r)) :
    (k : ℝ)*Real.logb 2 (fourValue φ (insertCubes N U r)) ≤ (k : ℝ)*N.graph.cost δ +
      ∑ j, (l j : ℝ)*perimeter δ (p j) := by
  let v := fourValue φ (insertCubes N U r)
  choose x hrel hroot using fun j => (AsympRel_iff_tendsto (OmegaBridge.pF ℂ) _ _).mp (rel j)
  have hp := fun j => (multiplicity_rate (hroot j)).1
  have hrates := fun j => (multiplicity_rate (hroot j)).2
  let rate (n : ℕ) (j : Fin m) := Real.logb 2 (x j n) / n + (l j : ℝ)
  have hrate (j) : Tendsto (fun n => rate n j) atTop (𝓝 (l j : ℝ)) := by
    simpa only [zero_add] using! (hrates j).add_const (l j : ℝ)
  have hlim : Tendsto (fun n : ℕ => (k : ℝ)*N.graph.cost δ +
      ∑ j, rate n j * perimeter δ (p j)) atTop (𝓝 ((k : ℝ)*N.graph.cost δ +
      ∑ j, (l j : ℝ)*perimeter δ (p j))) :=
    tendsto_const_nhds.add (tendsto_finsetSum _ fun j _ => (hrate j).mul_const _)
  apply ge_of_tendsto hlim
  filter_upwards [eventually_ge_atTop 1, Filter.eventually_all.mpr hp] with n hn hx
  let n' : ℕ+ := ⟨n,hn⟩
  let total := k*n'
  let c (j : Fin m) : ℕ+ := ⟨x j n,hx j⟩
  let b (j : Fin m) := OmegaBridge.powTwoPNat ((l j : ℕ)*n)
  let W (j : Fin m) := c j * b j
  obtain ⟨A,hA⟩ : ∃ A : (j : Fin m) → TriangleModel (W j) (formatPow (fun _ => D j) total),
      ∀ j a, blockPower (U j) total a = (A j).coeff a := by
    choose A hA using fun j => powered_triangle_model (U j) (k := k) (l := l j) (n := n') (m := c j) (hrel j n hn)
    exact ⟨A,hA⟩
  let N' := repeatNet N total
  let r' := blockRead N r total
  let M := realizeTriangles N' A p r'
  have hlocal : M.Local τ := realizeTriangles_local N' A p r' (repeat_local N hN total)
    (blockRead_local N r p hr total)
  have hvalue : value φ M = v^(total : ℕ) := by
    change AsymptoticSpectrum.eval fourPreorder (TensorClass.mk ⟨_,M.tensor⟩) φ = _
    rw [show M.tensor = blockPower (insertCubes N U r) total from
      (realizeTriangles_tensor N' A p r' _ hA).trans (repeat_insert N U r total)]
    rw [class_blockPower,AsymptoticSpectrum.eval_pow]
  have bits (j : Fin m) : Real.logb 2 (W j : ℕ) = Real.logb 2 (x j n) + (l j : ℝ)*n := by
    change Real.logb 2 (((x j n * 2^((l j : ℕ)*n) : ℕ) : ℝ)) = _
    have xpos : 0 < (x j n : ℝ) := by exact_mod_cast hx j
    rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, Real.logb_mul xpos.ne' (by positivity),
      Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one, Nat.cast_mul]
  have h := hd M hlocal (hvalue.symm ▸ pow_pos hv (total : ℕ))
  rw [hvalue,Real.logb_pow,realizeTriangles_cost,repeat_cost] at h
  simp_rw [bits] at h
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  apply le_of_mul_le_mul_right (a := (n : ℝ)) _ hnR
  dsimp only [rate]
  rw [add_mul,Finset.sum_mul]
  have terms (j : Fin m) : ((Real.logb 2 (x j n)/n+(l j : ℝ))*perimeter δ (p j))*n =
      (Real.logb 2 (x j n)+(l j : ℝ)*n)*perimeter δ (p j) := by field_simp <;> ring
  simp_rw [terms]
  have size : ((total : ℕ) : ℝ) = (k : ℝ)*n := Nat.cast_mul _ _
  rw [size] at h
  change ((k : ℝ)*Real.logb 2 v)*n ≤ _
  linarith only [h]

theorem proof_R114_16 : S_R114_16 := by
  intro V _ φ τ δ hδ hn _ _ f N hN m D U p r hD hr
  dsimp only
  intro hv
  let v := fourValue φ (insertCubes N U r)
  let α (j : Fin m) := relativeCost (U j) * Real.logb 2 (D j : ℝ)
  let π (j : Fin m) := perimeter δ (p j)
  let B := N.graph.cost δ + ∑ j, α j * π j
  change Real.logb 2 v ≤ B
  have hπ (j) : 0 ≤ π j := add_nonneg (add_nonneg (hn _ _) (hn _ _)) (hn _ _)
  have hα (j) : 0 ≤ α j := mul_nonneg (proof_R114_14 _ _ (hD j)).1
    (Real.logb_nonneg one_lt_two (by exact_mod_cast (D j).pos))
  by_contra! hgap
  let gap := Real.logb 2 v - B
  have hg : 0 < gap := sub_pos.mpr hgap
  obtain ⟨K,hK⟩ := exists_nat_gt ((∑ j, π j)/gap+1)
  have hK0 : (1 : ℝ) < K := (le_add_of_nonneg_left (div_nonneg (Finset.sum_nonneg fun j _ => hπ j) hg.le)).trans_lt hK
  let k : ℕ+ := ⟨K, by exact_mod_cast (zero_lt_one.trans hK0)⟩
  let l (j : Fin m) : ℕ+ := ⟨⌊α j*K⌋₊+1,Nat.succ_pos _⟩
  have ht (j) : α j*K < (l j : ℝ) := by simpa [l] using Nat.lt_floor_add_one (α j*K)
  have hu (j) : (l j : ℝ) ≤ α j*K+1 := by
    simpa [l] using add_le_add_right (Nat.floor_le (mul_nonneg (hα j) (Nat.cast_nonneg K))) 1
  have hlt (j) := proof_R114_15 (D j) (U j) (hD j) (k : ℕ) (l j : ℕ) k.pos (l j).pos
    ((lt_div_iff₀ (zero_lt_one.trans hK0)).mpr (ht j))
  have h := price_comparisons hδ N hN U p r hr k l hlt hv
  have sum := Finset.sum_le_sum (s := Finset.univ) (fun j _ => mul_le_mul_of_nonneg_right (hu j) (hπ j))
  have algebra : ∑ j, (α j*K+1)*π j = (∑ j, α j*π j)*K + ∑ j, π j := by
    rw [Finset.sum_mul,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro j _; ring
  rw [algebra] at sum
  change (K : ℝ)*Real.logb 2 v ≤ (K : ℝ)*N.graph.cost δ + ∑ j, (l j : ℝ)*π j at h
  have hbound : (∑ j, π j) < (K : ℝ)*gap :=
    (div_lt_iff₀ hg).mp (by linarith only [hK])
  dsimp [gap,B] at hbound
  nlinarith only [hbound, h, sum]

end OM.NNN34

