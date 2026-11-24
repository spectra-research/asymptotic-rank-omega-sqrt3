/- Adapted from PolMul/SpectralFacts/Tensors.lean of an earlier formalisation
   (commit 51c6e6b6e8b8d7226c6a828dba618ae1de5b5f8a).
   Uses Foundations tensor definitions; declarations are renamed under OM. -/
import Lib.OM.PolMul.SpectralFacts.Power

namespace OM.PolMul.SpectralFacts

open AsymptoticSpectrumDuality
open Semicontinuity
open OM.PolMulDef

universe u

variable {F : Type u} [Field F]

lemma restricts_of_index_equiv {dS dT : Fin 3 → ℕ+}
    {S : KTensor F dS} {T : KTensor F dT}
    (e : ∀ i : Fin 3, Fin (dS i) ≃ Fin (dT i))
    (hval : ∀ idx, S idx = T (fun i => e i (idx i))) : Restricts S T := by
  classical
  refine ⟨fun i a b => if e i a = b then 1 else 0, ?_⟩
  intro idx
  let idx0 : ∀ i : Fin 3, Fin (dT i) := fun i => e i (idx i)
  rw [Finset.sum_eq_single idx0]
  · rw [hval]
    have hp : (∏ i : Fin 3, (if e i (idx i) = idx0 i then (1 : F) else 0)) = 1 := by
      apply Finset.prod_eq_one
      intro i _
      simp [idx0]
    rw [hp, one_mul]
  · intro col _ hcol
    have hex : ∃ i : Fin 3, col i ≠ idx0 i := by
      by_contra h
      push_neg at h
      exact hcol (funext h)
    obtain ⟨i, hi⟩ := hex
    have hz : (if e i (idx i) = col i then (1 : F) else 0) = 0 := by
      rw [if_neg]
      exact fun h => hi h.symm
    rw [Finset.prod_eq_zero (Finset.mem_univ i) hz, zero_mul]
  · intro h
    exact (h (Finset.mem_univ _)).elim

lemma restrictsEquiv_of_index_equiv {dS dT : Fin 3 → ℕ+}
    {S : KTensor F dS} {T : KTensor F dT}
    (e : ∀ i : Fin 3, Fin (dS i) ≃ Fin (dT i))
    (hval : ∀ idx, S idx = T (fun i => e i (idx i))) : S ∼ₜ T := by
  constructor
  · exact restricts_of_index_equiv e hval
  · refine restricts_of_index_equiv (fun i => (e i).symm) (fun idx => ?_)
    have h := hval (fun i => (e i).symm (idx i))
    simpa only [Equiv.apply_symm_apply] using! h.symm

-- Coordinate normalization through two nested `Fin` product encodings is expensive.
set_option maxHeartbeats 300000 in
private lemma matMul_n11_pair (n : ℕ+) :
    (matMul (F := F) n 1 1) ∼ₜ
      unitPairTensor (F := F) n (0 : Fin 3) (2 : Fin 3) (by decide +kernel) := by
  let hfmt : ∀ i : Fin 3,
      ((fmt (n * 1) (1 * 1) (1 * n) i : ℕ)) =
        (naturalPairFormat n (0 : Fin 3) (2 : Fin 3) i : ℕ) := by
    intro i
    fin_cases i <;> simp [fmt, naturalPairFormat]
  have hval : ∀ idx, matMul (F := F) n 1 1 idx =
      unitPairTensor (F := F) n (0 : Fin 3) (2 : Fin 3) (by decide +kernel)
        (fun i => Fin.cast (hfmt i) (idx i)) := by
    intro idx
    have hlt : (idx 2).val < (n : ℕ) := by simpa [fmt] using! (idx 2).isLt
    simp only [matMul, unitPairTensor]
    simp [finProdFinEquiv_symm_apply, Fin.ext_iff, Nat.mod_eq_of_lt hlt, eq_comm]
  constructor
  · exact Restricts.of_eq_cast hfmt hval
  · refine Restricts.of_eq_cast (fun i => (hfmt i).symm) (fun idx => ?_)
    have h := hval (fun i => Fin.cast (hfmt i).symm (idx i))
    have hcast : (fun i => Fin.cast (hfmt i) (Fin.cast (hfmt i).symm (idx i))) = idx := by
      funext i
      exact Fin.rightInverse_cast (hfmt i) (idx i)
    rw [hcast] at h
    exact h.symm

-- Coordinate normalization through two nested `Fin` product encodings is expensive.
set_option maxHeartbeats 300000 in
private lemma matMul_1n1_pair (n : ℕ+) :
    (matMul (F := F) 1 n 1) ∼ₜ
      unitPairTensor (F := F) n (0 : Fin 3) (1 : Fin 3) (by decide +kernel) := by
  let hfmt : ∀ i : Fin 3,
      ((fmt (1 * n) (n * 1) (1 * 1) i : ℕ)) =
        (naturalPairFormat n (0 : Fin 3) (1 : Fin 3) i : ℕ) := by
    intro i
    fin_cases i <;> simp [fmt, naturalPairFormat]
  have hval : ∀ idx, matMul (F := F) 1 n 1 idx =
      unitPairTensor (F := F) n (0 : Fin 3) (1 : Fin 3) (by decide +kernel)
        (fun i => Fin.cast (hfmt i) (idx i)) := by
    intro idx
    have hlt : (idx 0).val < (n : ℕ) := by simpa [fmt] using! (idx 0).isLt
    simp only [matMul, unitPairTensor]
    simp [finProdFinEquiv_symm_apply, Fin.ext_iff, Nat.mod_eq_of_lt hlt, eq_comm]
  constructor
  · exact Restricts.of_eq_cast hfmt hval
  · refine Restricts.of_eq_cast (fun i => (hfmt i).symm) (fun idx => ?_)
    have h := hval (fun i => Fin.cast (hfmt i).symm (idx i))
    have hcast : (fun i => Fin.cast (hfmt i) (Fin.cast (hfmt i).symm (idx i))) = idx := by
      funext i
      exact Fin.rightInverse_cast (hfmt i) (idx i)
    rw [hcast] at h
    exact h.symm

-- Coordinate normalization through two nested `Fin` product encodings is expensive.
set_option maxHeartbeats 300000 in
private lemma matMul_11n_pair (n : ℕ+) :
    (matMul (F := F) 1 1 n) ∼ₜ
      unitPairTensor (F := F) n (1 : Fin 3) (2 : Fin 3) (by decide +kernel) := by
  let hfmt : ∀ i : Fin 3,
      ((fmt (1 * 1) (1 * n) (n * 1) i : ℕ)) =
        (naturalPairFormat n (1 : Fin 3) (2 : Fin 3) i : ℕ) := by
    intro i
    fin_cases i <;> simp [fmt, naturalPairFormat]
  have hval : ∀ idx, matMul (F := F) 1 1 n idx =
      unitPairTensor (F := F) n (1 : Fin 3) (2 : Fin 3) (by decide +kernel)
        (fun i => Fin.cast (hfmt i) (idx i)) := by
    intro idx
    have hlt : (idx 1).val < (n : ℕ) := by simpa [fmt] using! (idx 1).isLt
    simp only [matMul, unitPairTensor]
    simp [finProdFinEquiv_symm_apply, Fin.ext_iff, Nat.mod_eq_of_lt hlt, eq_comm]
  constructor
  · exact Restricts.of_eq_cast hfmt hval
  · refine Restricts.of_eq_cast (fun i => (hfmt i).symm) (fun idx => ?_)
    have h := hval (fun i => Fin.cast (hfmt i).symm (idx i))
    have hcast : (fun i => Fin.cast (hfmt i) (Fin.cast (hfmt i).symm (idx i))) = idx := by
      funext i
      exact Fin.rightInverse_cast (hfmt i) (idx i)
    rw [hcast] at h
    exact h.symm

lemma eval_matMul_n11_eq_pair (Fspec : Semicontinuity.SpectralPoint 3 F) (n : ℕ+) :
    Fspec.toFun (matMul (F := F) n 1 1) =
      Fspec.toFun (unitPairTensor (F := F) n (0 : Fin 3) (2 : Fin 3) (by decide +kernel)) :=
  le_antisymm (Fspec.mono _ _ (matMul_n11_pair n).1)
    (Fspec.mono _ _ (matMul_n11_pair n).2)

lemma eval_matMul_1n1_eq_pair (Fspec : Semicontinuity.SpectralPoint 3 F) (n : ℕ+) :
    Fspec.toFun (matMul (F := F) 1 n 1) =
      Fspec.toFun (unitPairTensor (F := F) n (0 : Fin 3) (1 : Fin 3) (by decide +kernel)) :=
  le_antisymm (Fspec.mono _ _ (matMul_1n1_pair n).1)
    (Fspec.mono _ _ (matMul_1n1_pair n).2)

lemma eval_matMul_11n_eq_pair (Fspec : Semicontinuity.SpectralPoint 3 F) (n : ℕ+) :
    Fspec.toFun (matMul (F := F) 1 1 n) =
      Fspec.toFun (unitPairTensor (F := F) n (1 : Fin 3) (2 : Fin 3) (by decide +kernel)) :=
  le_antisymm (Fspec.mono _ _ (matMul_11n_pair n).1)
    (Fspec.mono _ _ (matMul_11n_pair n).2)

lemma unitPair_restricts_unitTensor (r : ℕ+) (i j : Fin 3) (hij : i ≠ j) :
    Restricts (unitPairTensor (F := F) r i j hij)
      (unitTensor F (k := 3) r) := by
  classical
  let A : ∀ ℓ : Fin 3,
      Matrix (Fin (naturalPairFormat r i j ℓ)) (Fin r) F :=
    fun ℓ a b => if ℓ = i ∨ ℓ = j then if a.val = b.val then 1 else 0 else 1
  refine ⟨A, ?_⟩
  intro jdx
  simp only [unitPairTensor]
  by_cases hp : (jdx i).val = (jdx j).val
  · rw [if_pos hp]
    have hi_lt : (jdx i).val < (r : ℕ) := by
      simpa [naturalPairFormat] using! (jdx i).isLt
    let idx0 : ∀ _ : Fin 3, Fin r := fun _ => ⟨(jdx i).val, hi_lt⟩
    rw [Finset.sum_eq_single idx0]
    · have hprod : (∏ ℓ : Fin 3, A ℓ (jdx ℓ) (idx0 ℓ)) = 1 := by
        apply Finset.prod_eq_one
        intro ℓ _
        by_cases hℓ : ℓ = i ∨ ℓ = j
        · rcases hℓ with rfl | rfl
          · simp [A, idx0]
          · simp [A, idx0, hp]
        · simp [A, hℓ]
      rw [hprod, one_mul]
      simp [unitTensor, idx0]
    · intro idx _ hidx
      by_cases hall : ∀ a b : Fin 3, idx a = idx b
      · have hidxi : idx i ≠ idx0 i := by
          intro hi
          apply hidx
          funext ℓ
          apply Fin.ext
          calc
            (idx ℓ).val = (idx i).val := congrArg Fin.val (hall ℓ i)
            _ = (idx0 i).val := congrArg Fin.val hi
            _ = (idx0 ℓ).val := rfl
        have hz : A i (jdx i) (idx i) = 0 := by
          have hv : (jdx i).val ≠ (idx i).val := by
            intro h
            apply hidxi
            apply Fin.ext
            simpa [idx0] using! h.symm
          simp [A, hv]
        rw [Finset.prod_eq_zero (Finset.mem_univ i) hz, zero_mul]
      · simp [unitTensor, hall]
    · intro h
      exact (h (Finset.mem_univ _)).elim
  · rw [if_neg hp]
    symm
    apply Finset.sum_eq_zero
    intro idx _
    by_cases hall : ∀ a b : Fin 3, idx a = idx b
    · by_cases hi : (jdx i).val = (idx i).val
      · have hj : (jdx j).val ≠ (idx j).val := by
          intro hj'
          apply hp
          calc
            (jdx i).val = (idx i).val := hi
            _ = (idx j).val := congrArg Fin.val (hall i j)
            _ = (jdx j).val := hj'.symm
        have hz : A j (jdx j) (idx j) = 0 := by simp [A, hj]
        rw [Finset.prod_eq_zero (Finset.mem_univ j) hz, zero_mul]
      · have hz : A i (jdx i) (idx i) = 0 := by simp [A, hi]
        rw [Finset.prod_eq_zero (Finset.mem_univ i) hz, zero_mul]
    · simp [unitTensor, hall]

-- The cyclic third-leg coordinate swap makes this normalization moderately expensive.
set_option maxHeartbeats 600000 in
set_option maxRecDepth 10000 in
lemma matMul_factor_equiv (n₁ n₂ n₃ : ℕ+) :
    matMul (F := F) n₁ n₂ n₃ ∼ₜ
      ((unitPairTensor (F := F) n₁ (0 : Fin 3) (2 : Fin 3) (by decide +kernel) ⊠
        unitPairTensor (F := F) n₂ (0 : Fin 3) (1 : Fin 3) (by decide +kernel)) ⊠
        unitPairTensor (F := F) n₃ (1 : Fin 3) (2 : Fin 3) (by decide +kernel)) := by
  let dM := fmt (n₁ * n₂) (n₂ * n₃) (n₃ * n₁)
  let dP : Fin 3 → ℕ+ := fun i =>
    (naturalPairFormat n₁ (0 : Fin 3) (2 : Fin 3) i *
      naturalPairFormat n₂ (0 : Fin 3) (1 : Fin 3) i) *
      naturalPairFormat n₃ (1 : Fin 3) (2 : Fin 3) i
  have h0 : (dM 0 : ℕ) = (dP 0 : ℕ) := by
    simp [dM, dP, fmt, naturalPairFormat]
  have h1 : (dM 1 : ℕ) = (dP 1 : ℕ) := by
    simp [dM, dP, fmt, naturalPairFormat]
  have h2 : (((n₁ * n₃ : ℕ+) : ℕ)) = (dP 2 : ℕ) := by
    simp [dP, naturalPairFormat]
  let eswap : Fin ((n₃ * n₁ : ℕ+) : ℕ) ≃ Fin ((n₁ * n₃ : ℕ+) : ℕ) :=
    (kronDecodeEquiv (d₁ := n₃) (d₂ := n₁)).trans
      ((Equiv.prodComm _ _).trans (kronDecodeEquiv (d₁ := n₁) (d₂ := n₃)).symm)
  let e : ∀ i : Fin 3, Fin (dM i) ≃ Fin (dP i)
    | 0 => finCongr h0
    | 1 => finCongr h1
    | 2 => eswap.trans (finCongr h2)
  apply restrictsEquiv_of_index_equiv e
  intro idx
  simp only [dM, dP] at e ⊢
  simp only [matMul, unitPairTensor, kroneckerTensor]
  have he0 : (e 0 (idx 0)).val = (idx 0).val := by
    change (Fin.cast h0 (idx 0)).val = (idx 0).val
    rfl
  have he1 : (e 1 (idx 1)).val = (idx 1).val := by
    change (Fin.cast h1 (idx 1)).val = (idx 1).val
    rfl
  have hswap :
      kronDecodeEquiv (d₁ := n₁) (d₂ := n₃) (eswap (idx 2)) =
        ((kronDecodeEquiv (d₁ := n₃) (d₂ := n₁) (idx 2)).2,
          (kronDecodeEquiv (d₁ := n₃) (d₂ := n₁) (idx 2)).1) := by
    simp [eswap]
    generalize kronDecodeEquiv (d₁ := n₃) (d₂ := n₁) (idx 2) = p
    rcases p with ⟨a, b⟩
    rfl
  have hswapL : (eswap (idx 2)).val / (n₃ : ℕ) = (idx 2).val % (n₁ : ℕ) := by
    have h := congrArg (fun p => p.1.val) hswap
    simpa only [kronDecodeEquiv_apply, kronDecodeL_val, kronDecodeR_val] using! h
  have hswapR : (eswap (idx 2)).val % (n₃ : ℕ) = (idx 2).val / (n₁ : ℕ) := by
    have h := congrArg (fun p => p.2.val) hswap
    simpa only [kronDecodeEquiv_apply, kronDecodeL_val, kronDecodeR_val] using! h
  have he2L : (e 2 (idx 2)).val / (n₃ : ℕ) = (idx 2).val % (n₁ : ℕ) := by
    simpa only [e, Fin.val_cast] using! hswapL
  have he2R : (e 2 (idx 2)).val % (n₃ : ℕ) = (idx 2).val / (n₁ : ℕ) := by
    simpa only [e, Fin.val_cast] using! hswapR
  have hdiv1 : (idx 1).val / (n₃ : ℕ) < (n₂ : ℕ) := by
    apply (Nat.div_lt_iff_lt_mul n₃.pos).2
    simpa [dM, fmt, PNat.mul_coe] using! (idx 1).isLt
  have he0div : (e 0 (idx 0)).val / (n₂ : ℕ) = (idx 0).val / (n₂ : ℕ) :=
    congrArg (fun a => a / (n₂ : ℕ)) he0
  have he0mod : (e 0 (idx 0)).val % (n₂ : ℕ) = (idx 0).val % (n₂ : ℕ) :=
    congrArg (fun a => a % (n₂ : ℕ)) he0
  have he1divmod : (e 1 (idx 1)).val / (n₃ : ℕ) % (n₂ : ℕ) =
      (idx 1).val / (n₃ : ℕ) := by
    rw [congrArg (fun a => a / (n₃ : ℕ) % (n₂ : ℕ)) he1,
      Nat.mod_eq_of_lt hdiv1]
  have he1mod : (e 1 (idx 1)).val % (n₃ : ℕ) = (idx 1).val % (n₃ : ℕ) :=
    congrArg (fun a => a % (n₃ : ℕ)) he1
  have hA :
      ((kronLeftIndex (kronLeftIndex (fun i => e i (idx i))) 0).val =
        (kronLeftIndex (kronLeftIndex (fun i => e i (idx i))) 2).val) ↔
        (finProdFinEquiv.symm (idx 2)).2 = (finProdFinEquiv.symm (idx 0)).1 := by
    simp only [kronLeftIndex, finProdFinEquiv_symm_apply, Fin.coe_divNat]
    simp [naturalPairFormat]
    constructor
    · intro h
      apply Fin.ext
      exact he2L.symm.trans (h.symm.trans he0div)
    · intro h
      have hv := congrArg Fin.val h
      exact he0div.trans (hv.symm.trans he2L.symm)
  have hB :
      ((kronRightIndex (kronLeftIndex (fun i => e i (idx i))) 0).val =
        (kronRightIndex (kronLeftIndex (fun i => e i (idx i))) 1).val) ↔
        (finProdFinEquiv.symm (idx 0)).2 = (finProdFinEquiv.symm (idx 1)).1 := by
    simp only [kronRightIndex, kronLeftIndex, finProdFinEquiv_symm_apply,
      Fin.coe_divNat, Fin.coe_modNat]
    simp [naturalPairFormat]
    constructor
    · intro h
      apply Fin.ext
      exact he0mod.symm.trans (h.trans he1divmod)
    · intro h
      have hv := congrArg Fin.val h
      exact he0mod.trans (hv.trans he1divmod.symm)
  have hC :
      ((kronRightIndex (fun i => e i (idx i)) 1).val =
        (kronRightIndex (fun i => e i (idx i)) 2).val) ↔
        (finProdFinEquiv.symm (idx 1)).2 = (finProdFinEquiv.symm (idx 2)).1 := by
    simp only [kronRightIndex, finProdFinEquiv_symm_apply, Fin.coe_modNat]
    simp [naturalPairFormat]
    constructor
    · intro h
      apply Fin.ext
      exact he1mod.symm.trans (h.trans he2R)
    · intro h
      have hv := congrArg Fin.val h
      exact he1mod.trans (hv.trans he2R.symm)
  rw [if_congr hA rfl rfl, if_congr hB rfl rfl, if_congr hC rfl rfl]
  by_cases hB' : (finProdFinEquiv.symm (idx 0)).2 =
      (finProdFinEquiv.symm (idx 1)).1 <;>
    by_cases hC' : (finProdFinEquiv.symm (idx 1)).2 =
      (finProdFinEquiv.symm (idx 2)).1 <;>
    by_cases hA' : (finProdFinEquiv.symm (idx 2)).2 =
      (finProdFinEquiv.symm (idx 0)).1 <;>
    simp only [finProdFinEquiv_symm_apply] at hA' hB' hC' ⊢ <;>
    simp only [hA', hB', hC', and_self, if_pos, one_mul] <;>
    simp

lemma eval_matMul_factor (Fspec : Semicontinuity.SpectralPoint 3 F) (n₁ n₂ n₃ : ℕ+) :
    Fspec.toFun (matMul (F := F) n₁ n₂ n₃) =
      Fspec.toFun (matMul (F := F) n₁ 1 1) *
      Fspec.toFun (matMul (F := F) 1 n₂ 1) *
      Fspec.toFun (matMul (F := F) 1 1 n₃) := by
  have heq := matMul_factor_equiv (F := F) n₁ n₂ n₃
  have hval : Fspec.toFun (matMul (F := F) n₁ n₂ n₃) =
      Fspec.toFun
        ((unitPairTensor (F := F) n₁ (0 : Fin 3) (2 : Fin 3) (by decide +kernel) ⊠
          unitPairTensor (F := F) n₂ (0 : Fin 3) (1 : Fin 3) (by decide +kernel)) ⊠
          unitPairTensor (F := F) n₃ (1 : Fin 3) (2 : Fin 3) (by decide +kernel)) :=
    le_antisymm (Fspec.mono _ _ heq.1) (Fspec.mono _ _ heq.2)
  rw [hval, Fspec.mult, Fspec.mult, eval_matMul_n11_eq_pair,
    eval_matMul_1n1_eq_pair, eval_matMul_11n_eq_pair]

end OM.PolMul.SpectralFacts
