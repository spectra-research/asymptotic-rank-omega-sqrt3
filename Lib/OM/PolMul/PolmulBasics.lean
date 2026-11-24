/- Adapted from PolMul/PolmulBasics.lean of an earlier formalisation
   (commit 51c6e6b6e8b8d7226c6a828dba618ae1de5b5f8a).
   Amanov, van den Berg and Zuiddam (2026),
   “Multiplying matrices via polynomials: exposition and barriers”.
   Uses Foundations tensor definitions; declarations are renamed under OM. -/
import Lib.OM.PolMul.Defs
import Lib.OM.PolMulStatements.PM_1
import Lib.OM.PolMulStatements.PM_2
import Lib.OM.PolMulStatements.PM_3
import Lib.OM.PolMulStatements.PM_4
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Vandermonde

/-!
# Basic degenerations for polynomial multiplication

This file proves the four results in Sections 3.1--3.2 of the paper.  Small
coordinate lemmas used by more than one proof are kept private here.
-/

namespace OM.PolMul.PolmulBasics

open AsymptoticSpectrumDuality
open Semicontinuity
open scoped BigOperators

universe u

variable {F : Type u} [Field F]

/-- A restriction is a constant polynomial degeneration. -/
private lemma degen_of_restricts {dT dS : Fin 3 → ℕ+}
    {T : OM.PolMul.T3 F dT} {S : OM.PolMul.T3 F dS}
    (h : Restricts T S) : OM.PolMul.Degen T S := by
  classical
  obtain ⟨A, hA⟩ := h
  refine ⟨0, 0, (fun i x y => Polynomial.C (A i x y)), Fin.elim0, ?_⟩
  intro idx
  rw [show (∑ sidx, (∏ i, Polynomial.C (A i (idx i) (sidx i))) *
        Polynomial.C (S sidx)) = Polynomial.C (T idx) by
    rw [hA idx, map_sum]
    apply Finset.sum_congr rfl
    intro sidx _
    rw [map_mul, map_prod]]
  simp

/-- Evaluate a tensor contraction whose leg matrices have one selected source
coordinate in each row. -/
private lemma sparse_contraction {R : Type*} [CommSemiring R]
    {dT dS : Fin 3 → ℕ+} (S : (∀ i, Fin (dS i)) → R)
    (f : ∀ i, Fin (dT i) → Fin (dS i))
    (c : ∀ i, Fin (dT i) → R) (idx : ∀ i, Fin (dT i)) :
    (∑ sidx, (∏ i, (if f i (idx i) = sidx i then c i (idx i) else 0)) * S sidx) =
      (∏ i, c i (idx i)) * S (fun i => f i (idx i)) := by
  classical
  rw [Finset.sum_eq_single (fun i => f i (idx i))]
  · simp
  · intro sidx _ hne
    have hex : ∃ i, f i (idx i) ≠ sidx i := by
      by_contra hall
      push_neg at hall
      exact hne (funext fun i => (hall i).symm)
    obtain ⟨i, hi⟩ := hex
    rw [show (∏ j, if f j (idx j) = sidx j then c j (idx j) else 0) = 0 from
      Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi), zero_mul]
  · simp

/-- Contraction against the three-leg unit tensor is the sum over its
diagonal.  This version uses `OM.PolMul.unit`'s explicit `fmt` indices. -/
private lemma unit_diagonal_sum (r : ℕ+)
    (f : (∀ i : Fin 3, Fin (OM.PolMul.fmt r r r i)) → Polynomial F) :
    (∑ idx : ∀ i : Fin 3, Fin (OM.PolMul.fmt r r r i),
        f idx * Polynomial.C (OM.PolMul.unit r idx)) =
      ∑ s : Fin r, f (fun | 0 => s | 1 => s | 2 => s) := by
  classical
  simp only [OM.PolMul.unit, apply_ite, Polynomial.C_1, Polynomial.C_0,
    mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  refine Finset.sum_bij
    (t := (Finset.univ : Finset (Fin r)))
    (f := f)
    (g := fun s : Fin r => f (fun | 0 => s | 1 => s | 2 => s))
    (fun idx (_ : idx ∈ (Finset.univ.filter
      (fun idx : ∀ i : Fin 3, Fin (OM.PolMul.fmt r r r i) =>
        ∀ i j : Fin 3, (idx i).val = (idx j).val))) => idx 0)
    ?_ ?_ ?_ ?_
  · intro idx _
    simp
  · intro x hx y hy hxy
    rw [Finset.mem_filter] at hx hy
    obtain ⟨_, hdx⟩ := hx
    obtain ⟨_, hdy⟩ := hy
    funext i
    apply Fin.ext
    calc
      (x i).val = (x 0).val := hdx i 0
      _ = (y 0).val := congrArg Fin.val hxy
      _ = (y i).val := (hdy i 0).symm
  · intro s _
    refine ⟨(fun | 0 => s | 1 => s | 2 => s), ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      intro i j
      fin_cases i <;> fin_cases j <;> rfl
    · rfl
  · intro idx hidx
    rw [Finset.mem_filter] at hidx
    obtain ⟨_, hd⟩ := hidx
    congr 1
    funext i
    apply Fin.ext
    fin_cases i
    · exact hd 0 0
    · exact hd 1 0
    · exact hd 2 0
/-- Permuting bases on every leg gives an isomorphism in the explicit
matrix-based sense used by the contracts. -/
private lemma iso_of_equiv {dT dS : Fin 3 → ℕ+}
    (T : OM.PolMul.T3 F dT) (S : OM.PolMul.T3 F dS)
    (e : ∀ i, Fin (dT i) ≃ Fin (dS i))
    (hTS : ∀ idx, T idx = S (fun i => e i (idx i))) : OM.PolMul.Iso T S := by
  classical
  let A : ∀ i : Fin 3, Matrix (Fin (dT i)) (Fin (dS i)) F :=
    fun i x y => if e i x = y then 1 else 0
  let B : ∀ i : Fin 3, Matrix (Fin (dS i)) (Fin (dT i)) F :=
    fun i y x => if e i x = y then 1 else 0
  refine ⟨A, B, ?_, ?_, ?_⟩
  · intro i
    ext x x'
    simp only [Matrix.mul_apply, A, B, Matrix.one_apply]
    by_cases hxx : x = x'
    · subst x'
      rw [if_pos rfl, Finset.sum_eq_single (e i x)]
      · simp
      · intro y _ hy
        simp only [ite_mul, one_mul, zero_mul]
        by_cases hxy : e i x = y
        · exact (hy hxy.symm).elim
        · simp [hxy]
      · simp
    · rw [if_neg hxx]
      apply Finset.sum_eq_zero
      intro y _
      by_cases hxy : e i x = y
      · have hx'y : e i x' ≠ y := by
          intro hx'y
          apply hxx
          exact (e i).injective (hxy.trans hx'y.symm)
        simp [hxy, hx'y]
      · simp [hxy]
  · intro i
    ext y y'
    simp only [Matrix.mul_apply, A, B, Matrix.one_apply]
    by_cases hyy : y = y'
    · subst y'
      rw [if_pos rfl, Finset.sum_eq_single ((e i).symm y)]
      · simp
      · intro x _ hx
        simp only [ite_mul, one_mul, zero_mul]
        by_cases hxy : e i x = y
        · have : x = (e i).symm y := by simpa using! congrArg (e i).symm hxy
          exact (hx this).elim
        · simp [hxy]
      · simp
    · rw [if_neg hyy]
      apply Finset.sum_eq_zero
      intro x _
      by_cases hxy : e i x = y
      · have hxy' : e i x ≠ y' := hxy.symm ▸ hyy
        simp [hxy, hxy', hyy]
      · simp [hxy]
  · intro idx
    rw [hTS idx, Finset.sum_eq_single (fun i => e i (idx i))]
    · simp [A]
    · intro sidx _ hne
      have hex : ∃ i, e i (idx i) ≠ sidx i := by
        by_contra hall
        push_neg at hall
        exact hne (funext fun i => (hall i).symm)
      obtain ⟨i, hi⟩ := hex
      have hz : A i (idx i) (sidx i) = 0 := by simp [A, hi]
      rw [show (∏ j, A j (idx j) (sidx j)) = 0 from
        Finset.prod_eq_zero (Finset.mem_univ i) hz, zero_mul]
    · simp

private def finOneMulEquiv (k : ℕ) : Fin k ≃ Fin (1 * k) :=
  (Equiv.uniqueProd (Fin k) (Fin 1)).symm.trans finProdFinEquiv

private def finMulOneEquiv (k : ℕ) : Fin k ≃ Fin (k * 1) :=
  (Equiv.prodUnique (Fin k) (Fin 1)).symm.trans finProdFinEquiv

private def repeatOneMulEquiv (k d : ℕ) :
    Fin (∑ _ : Fin k, d) ≃ Fin (d * (1 * k)) :=
  finSigmaFinEquiv.symm |>.trans (Equiv.sigmaEquivProd (Fin k) (Fin d)) |>.trans
    (Equiv.prodComm (Fin k) (Fin d)) |>.trans
    ((Equiv.refl (Fin d)).prodCongr (finOneMulEquiv k)) |>.trans finProdFinEquiv

private def repeatMulOneEquiv (k d : ℕ) :
    Fin (∑ _ : Fin k, d) ≃ Fin (d * (k * 1)) :=
  finSigmaFinEquiv.symm |>.trans (Equiv.sigmaEquivProd (Fin k) (Fin d)) |>.trans
    (Equiv.prodComm (Fin k) (Fin d)) |>.trans
    ((Equiv.refl (Fin d)).prodCongr (finMulOneEquiv k)) |>.trans finProdFinEquiv

private def finOneOneEquiv (d : ℕ) : Fin d ≃ Fin (d * (1 * 1)) :=
  (Equiv.prodUnique (Fin d) (Fin 1)).symm |>.trans
    ((Equiv.refl (Fin d)).prodCongr (finOneMulEquiv 1)) |>.trans finProdFinEquiv

private lemma finProdFinEquiv_symm_finOneMulEquiv (k : ℕ) (x : Fin k) :
    finProdFinEquiv.symm (finOneMulEquiv k x) = ((0 : Fin 1), x) := by
  change finProdFinEquiv.symm (finProdFinEquiv (default, x)) = _
  rw [Equiv.symm_apply_apply]
  congr

private lemma finProdFinEquiv_symm_finMulOneEquiv (k : ℕ) (x : Fin k) :
    finProdFinEquiv.symm (finMulOneEquiv k x) = (x, (0 : Fin 1)) := by
  change finProdFinEquiv.symm (finProdFinEquiv (x, default)) = _
  rw [Equiv.symm_apply_apply]
  congr

private lemma finProdFinEquiv_symm_repeatOneMulEquiv (k d : ℕ)
    (x : Fin (∑ _ : Fin k, d)) :
    finProdFinEquiv.symm (repeatOneMulEquiv k d x) =
      ((finSigmaFinEquiv.symm x).2,
        finOneMulEquiv k (finSigmaFinEquiv.symm x).1) := by
  change finProdFinEquiv.symm
    (finProdFinEquiv ((finSigmaFinEquiv.symm x).2,
      finOneMulEquiv k (finSigmaFinEquiv.symm x).1)) = _
  exact Equiv.symm_apply_apply _ _

private lemma finProdFinEquiv_symm_repeatMulOneEquiv (k d : ℕ)
    (x : Fin (∑ _ : Fin k, d)) :
    finProdFinEquiv.symm (repeatMulOneEquiv k d x) =
      ((finSigmaFinEquiv.symm x).2,
        finMulOneEquiv k (finSigmaFinEquiv.symm x).1) := by
  change finProdFinEquiv.symm
    (finProdFinEquiv ((finSigmaFinEquiv.symm x).2,
      finMulOneEquiv k (finSigmaFinEquiv.symm x).1)) = _
  exact Equiv.symm_apply_apply _ _

private lemma finProdFinEquiv_symm_finOneOneEquiv (d : ℕ) (x : Fin d) :
    finProdFinEquiv.symm (finOneOneEquiv d x) =
      (x, finOneMulEquiv 1 (0 : Fin 1)) := by
  change finProdFinEquiv.symm
    (finProdFinEquiv (x, finOneMulEquiv 1 default)) = _
  rw [Equiv.symm_apply_apply]
  congr

private lemma matMul_one_one_apply (k : ℕ+) (r s : Fin k) :
    OM.PolMul.matMul (F := F) 1 1 k
      (fun | 0 => finOneMulEquiv 1 (0 : Fin 1)
           | 1 => finOneMulEquiv (k : ℕ) r
           | 2 => finMulOneEquiv (k : ℕ) s) = if r = s then 1 else 0 := by
  simp only [OM.PolMul.matMul]
  change (if
      (finProdFinEquiv.symm (finOneMulEquiv 1 (0 : Fin 1))).2 =
          (finProdFinEquiv.symm (finOneMulEquiv (k : ℕ) r)).1 ∧
        (finProdFinEquiv.symm (finOneMulEquiv (k : ℕ) r)).2 =
          (finProdFinEquiv.symm (finMulOneEquiv (k : ℕ) s)).1 ∧
        (finProdFinEquiv.symm (finMulOneEquiv (k : ℕ) s)).2 =
          (finProdFinEquiv.symm (finOneMulEquiv 1 (0 : Fin 1))).1
    then 1 else 0) = _
  rw [finProdFinEquiv_symm_finOneMulEquiv,
    finProdFinEquiv_symm_finOneMulEquiv,
    finProdFinEquiv_symm_finMulOneEquiv]
  simp

private lemma pnat_add_sub_one_coe (a b : ℕ+) :
    ((a + b - 1 : ℕ+) : ℕ) = (a : ℕ) + (b : ℕ) - 1 := by
  rw [PNat.sub_coe, PNat.add_coe]
  rw [if_pos]
  · rfl
  · apply (PNat.coe_lt_coe _ _).mp
    rw [PNat.add_coe]
    norm_num
    have ha := a.pos
    have hb := b.pos
    omega

private lemma nat_gap_identity {S C U Q : ℕ} (hCS : C ≤ S)
    (hCU : C + U ≤ Q) :
    S + U + (Q - (C + U)) = Q + (S - C) := by
  omega

/-- Normalize a nonzero polynomial at its first nonzero coefficient and write
the remaining coefficients in the consecutive form required by `Degen`. -/
private lemma normalize_at_trailingCoeff (p : Polynomial F) (hp : p ≠ 0) :
    Polynomial.C p.trailingCoeff⁻¹ * p =
      Polynomial.X ^ p.natTrailingDegree +
        ∑ j : Fin (p.natDegree - p.natTrailingDegree),
          Polynomial.X ^ (p.natTrailingDegree + j.val + 1) *
            Polynomial.C (p.trailingCoeff⁻¹ *
              p.coeff (p.natTrailingDegree + j.val + 1)) := by
  ext n
  simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_pow, Polynomial.finset_sum_coeff,
    Polynomial.coeff_mul_C, one_mul, zero_mul]
  by_cases hnq : n < p.natTrailingDegree
  · have hcoeff := Polynomial.coeff_eq_zero_of_lt_natTrailingDegree hnq
    rw [hcoeff, mul_zero]
    have hne : n ≠ p.natTrailingDegree := by omega
    rw [if_neg hne]
    simp only [zero_add]
    symm
    apply Finset.sum_eq_zero
    intro j _
    have hcond : n ≠ p.natTrailingDegree + j.val + 1 := by omega
    rw [if_neg hcond, zero_mul]
  · have hqn : p.natTrailingDegree ≤ n := Nat.le_of_not_gt hnq
    by_cases heq : n = p.natTrailingDegree
    · subst n
      rw [if_pos rfl]
      have htc : p.trailingCoeff ≠ 0 :=
        Polynomial.trailingCoeff_nonzero_iff_nonzero.mpr hp
      change p.trailingCoeff⁻¹ * p.trailingCoeff = _
      rw [inv_mul_cancel₀ htc]
      rw [show (∑ j : Fin (p.natDegree - p.natTrailingDegree),
          (if p.natTrailingDegree = p.natTrailingDegree + j.val + 1 then 1 else 0) *
            (p.trailingCoeff⁻¹ * p.coeff (p.natTrailingDegree + j.val + 1))) = 0 by
        apply Finset.sum_eq_zero
        intro j _
        have hcond : p.natTrailingDegree ≠
            p.natTrailingDegree + j.val + 1 := by omega
        rw [if_neg hcond, zero_mul]]
      simp
    · rw [if_neg heq]
      by_cases hdeg : n ≤ p.natDegree
      · let j₀ : Fin (p.natDegree - p.natTrailingDegree) :=
          ⟨n - p.natTrailingDegree - 1, by omega⟩
        rw [Finset.sum_eq_single j₀]
        · have hj : p.natTrailingDegree + j₀.val + 1 = n := by
            dsimp [j₀]
            omega
          rw [if_pos hj.symm, hj]
          simp
        · intro j _ hjne
          have hcond : n ≠ p.natTrailingDegree + j.val + 1 := by
            intro hj
            apply hjne
            apply Fin.ext
            dsimp [j₀]
            omega
          rw [if_neg hcond, zero_mul]
        · simp
      · have hcoeff : p.coeff n = 0 :=
          Polynomial.coeff_eq_zero_of_natDegree_lt (Nat.lt_of_not_ge hdeg)
        rw [hcoeff, mul_zero]
        simp only [zero_add]
        symm
        apply Finset.sum_eq_zero
        intro j _
        have hcond : n ≠ p.natTrailingDegree + j.val + 1 := by
          intro hj
          have hjlt := j.isLt
          omega
        rw [if_neg hcond, zero_mul]

/-- The proposition on the rank of polynomial multiplication.  This follows the paper's
Vandermonde evaluation argument, clearing the inverse by the adjugate and
normalizing the first nonzero coefficient of its determinant. -/
theorem proof_PM_1 : OM_S_PM_1 := by
  intro F _ a b
  classical
  let r : ℕ+ := a + b - 1
  change OM.PolMul.Degen (OM.PolMul.polmul (F := F) a b) (OM.PolMul.unit r)
  have har : (a : ℕ) ≤ (r : ℕ) := by
    dsimp [r]
    rw [pnat_add_sub_one_coe]
    have hb := b.pos
    omega
  have hbr : (b : ℕ) ≤ (r : ℕ) := by
    dsimp [r]
    rw [pnat_add_sub_one_coe]
    have ha := a.pos
    omega
  let ia : Fin a → Fin r := Fin.castLE har
  let ib : Fin b → Fin r := Fin.castLE hbr
  let v : Fin r → Polynomial F := fun s => Polynomial.X ^ s.val
  let V : Matrix (Fin r) (Fin r) (Polynomial F) := Matrix.vandermonde v
  let p : Polynomial F := V.det
  have hv : Function.Injective v := by
    intro x y hxy
    apply Fin.ext
    have hd := congrArg Polynomial.natDegree hxy
    simpa [v] using! hd
  have hp : p ≠ 0 := by
    exact Matrix.det_vandermonde_ne_zero_iff.mpr hv
  let A : ∀ t : Fin 3,
      Matrix (Fin (OM.PolMul.fmt a b r t)) (Fin (OM.PolMul.fmt r r r t))
        (Polynomial F) := fun t =>
    match t with
    | 0 => fun i s => Polynomial.C p.trailingCoeff⁻¹ * V s (ia i)
    | 1 => fun j s => V s (ib j)
    | 2 => fun k s => V.adjugate k s
  let e : ℕ := p.natDegree - p.natTrailingDegree
  let R : Fin e → OM.PolMul.T3 F (OM.PolMul.fmt a b r) := fun j idx =>
    (p.trailingCoeff⁻¹ * p.coeff (p.natTrailingDegree + j.val + 1)) *
      OM.PolMul.polmul a b idx
  refine ⟨p.natTrailingDegree, e, A, R, ?_⟩
  intro idx
  let i : Fin a := idx 0
  let j : Fin b := idx 1
  let k : Fin r := idx 2
  let ij : Fin r := ⟨i.val + j.val, by
    have hi := i.isLt
    have hj := j.isLt
    dsimp [r]
    rw [pnat_add_sub_one_coe]
    omega⟩
  rw [unit_diagonal_sum (r := r)
    (f := fun sidx => ∏ t, A t (idx t) (sidx t))]
  simp only [Fin.prod_univ_three]
  change (∑ s : Fin r,
      (Polynomial.C p.trailingCoeff⁻¹ * V s (ia i)) * V s (ib j) *
        V.adjugate k s) = _
  have hVmul : ∀ s : Fin r, V s (ia i) * V s (ib j) = V s ij := by
    intro s
    simp only [V, Matrix.vandermonde_apply, v]
    rw [← pow_add]
    congr 2
  have hadj := congrArg
    (fun M : Matrix (Fin r) (Fin r) (Polynomial F) => M k ij)
    (Matrix.adjugate_mul V)
  have hcore : (∑ s : Fin r,
      (Polynomial.C p.trailingCoeff⁻¹ * V s (ia i)) * V s (ib j) *
        V.adjugate k s) =
      (Polynomial.C p.trailingCoeff⁻¹ * p) *
        Polynomial.C (OM.PolMul.polmul a b idx) := by
    calc
      (∑ s : Fin r,
          (Polynomial.C p.trailingCoeff⁻¹ * V s (ia i)) * V s (ib j) *
            V.adjugate k s) =
          Polynomial.C p.trailingCoeff⁻¹ *
            ∑ s : Fin r, V.adjugate k s * V s ij := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro s _
              rw [← hVmul s]
              ring
      _ = Polynomial.C p.trailingCoeff⁻¹ *
          (p * (1 : Matrix (Fin r) (Fin r) (Polynomial F)) k ij) := by
            simpa only [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul]
              using! congrArg (fun z : Polynomial F =>
                Polynomial.C p.trailingCoeff⁻¹ * z) hadj
      _ = (Polynomial.C p.trailingCoeff⁻¹ * p) *
          Polynomial.C (OM.PolMul.polmul a b idx) := by
            by_cases h : k.val = i.val + j.val
            · have hk : k = ij := by
                apply Fin.ext
                simpa [ij] using! h
              have ht : OM.PolMul.polmul (F := F) a b idx = 1 := by
                unfold OM.PolMul.polmul
                rw [if_pos]
                simpa [i, j, k] using! h
              have hone : (1 : Matrix (Fin r) (Fin r) (Polynomial F)) k ij = 1 := by
                rw [Matrix.one_apply, if_pos hk]
              rw [hone, ht, Polynomial.C_1]
              ring
            · have hk : k ≠ ij := by
                intro hk
                apply h
                simpa [ij] using! congrArg Fin.val hk
              have ht : OM.PolMul.polmul (F := F) a b idx = 0 := by
                unfold OM.PolMul.polmul
                rw [if_neg]
                simpa [i, j, k] using! h
              have hone : (1 : Matrix (Fin r) (Fin r) (Polynomial F)) k ij = 0 := by
                rw [Matrix.one_apply, if_neg hk]
              rw [hone, ht, Polynomial.C_0]
              ring
  rw [hcore, normalize_at_trailingCoeff p hp]
  simp only [add_mul, Finset.sum_mul, Polynomial.C_mul, R, e]
  -- (v4.34 upgrade: `congr 1` timed out at `whnf`; the two sides differ only inside the sum.)
  refine congrArg (_ + ·) (Finset.sum_congr rfl fun t _ => ?_)
  ring

/-- The lemma on unit tensors and polynomial multiplication.  This follows the paper's
quadratic-weight monomial degeneration, written directly in coordinates. -/
theorem proof_PM_2 : OM_S_PM_2 := by
  intro F _ n
  change OM.PolMul.Degen (OM.PolMul.unit (F := F) n) (OM.PolMul.polmul n n)
  classical
  let N : ℕ := (n : ℕ) - 1
  let q₀ : ℕ := (2 * N) ^ 2
  let f : ∀ i : Fin 3, Fin (OM.PolMul.fmt n n n i) →
      Fin (OM.PolMul.fmt n n (n + n - 1) i) := fun i =>
    match i with
    | 0 => fun x => x
    | 1 => fun x => x
    | 2 => fun x => ⟨2 * x.val, by
        change 2 * x.val < ((n + n - 1 : ℕ+) : ℕ)
        have hx : x.val < (n : ℕ) := by simpa [OM.PolMul.fmt] using! x.isLt
        have hn : 1 ≤ (n : ℕ) := n.pos
        have hdim : ((n + n - 1 : ℕ+) : ℕ) = 2 * (n : ℕ) - 1 := by
          have hadd : (1 : ℕ+) < n + n := by
            apply (PNat.coe_lt_coe _ _).mp
            rw [PNat.add_coe]
            norm_num
            omega
          rw [PNat.sub_coe, PNat.add_coe]
          rw [if_pos hadd]
          norm_num [two_mul]
        rw [hdim]
        omega
        ⟩
  let w : ∀ i : Fin 3, Fin (OM.PolMul.fmt n n n i) → ℕ := fun i =>
    match i with
    | 0 => fun x => 2 * x.val ^ 2
    | 1 => fun x => 2 * x.val ^ 2
    | 2 => fun x => q₀ - (2 * x.val) ^ 2
  let A : ∀ i : Fin 3,
      Matrix (Fin (OM.PolMul.fmt n n n i))
        (Fin (OM.PolMul.fmt n n (n + n - 1) i)) (Polynomial F) :=
    fun i x y => if f i x = y then Polynomial.X ^ w i x else 0
  let R : Fin q₀ → OM.PolMul.T3 F (OM.PolMul.fmt n n n) := fun j idx =>
    if (∑ i : Fin 3, w i (idx i)) = q₀ + j.val + 1 then
      OM.PolMul.polmul n n (fun i => f i (idx i))
    else 0
  refine ⟨q₀, q₀, A, R, ?_⟩
  intro idx
  rw [show (∑ sidx, (∏ i, A i (idx i) (sidx i)) *
        Polynomial.C (OM.PolMul.polmul n n sidx)) =
      (∏ i, Polynomial.X ^ w i (idx i)) *
        Polynomial.C (OM.PolMul.polmul n n (fun i => f i (idx i))) by
    simpa only [A] using! sparse_contraction
      (R := Polynomial F) (fun sidx => Polynomial.C (OM.PolMul.polmul n n sidx)) f
      (fun i x => Polynomial.X ^ w i x)
      idx]
  rw [Finset.prod_pow_eq_pow_sum]
  simp only [OM.PolMul.polmul, f, OM.PolMul.fmt]
  by_cases hsupp : 2 * (idx 2).val = (idx 0).val + (idx 1).val
  · rw [if_pos hsupp]
    have hzN : (idx 2).val ≤ N := by
      dsimp [N]
      have hz : (idx 2).val < (n : ℕ) := by simpa [OM.PolMul.fmt] using! (idx 2).isLt
      omega
    have hxN : (idx 0).val ≤ N := by
      dsimp [N]
      have hx : (idx 0).val < (n : ℕ) := by simpa [OM.PolMul.fmt] using! (idx 0).isLt
      omega
    have hyN : (idx 1).val ≤ N := by
      dsimp [N]
      have hy : (idx 1).val < (n : ℕ) := by simpa [OM.PolMul.fmt] using! (idx 1).isLt
      omega
    have hw2 : w 2 (idx 2) = q₀ - (2 * (idx 2).val) ^ 2 := rfl
    have hsq : (2 * (idx 2).val) ^ 2 ≤ q₀ := by
      dsimp [q₀]
      nlinarith
    let g : ℕ := 2 * (idx 0).val ^ 2 + 2 * (idx 1).val ^ 2 -
      (2 * (idx 2).val) ^ 2
    have hle : (2 * (idx 2).val) ^ 2 ≤
        2 * (idx 0).val ^ 2 + 2 * (idx 1).val ^ 2 := by
      have hsuppZ : 2 * ((idx 2).val : ℤ) =
          (idx 0).val + (idx 1).val := by exact_mod_cast hsupp
      have hleZ : (2 * ((idx 2).val : ℤ)) ^ 2 ≤
          2 * ((idx 0).val : ℤ) ^ 2 + 2 * ((idx 1).val : ℤ) ^ 2 := by
        nlinarith [sq_nonneg (((idx 0).val : ℤ) - (idx 1).val)]
      exact_mod_cast hleZ
    have hsum : (∑ i : Fin 3, w i (idx i)) = q₀ + g := by
      rw [Fin.sum_univ_three]
      dsimp [w]
      dsimp [g]
      omega
    by_cases hxy : (idx 0).val = (idx 1).val
    · have hxz : (idx 0).val = (idx 2).val := by nlinarith
      have hyz : (idx 1).val = (idx 2).val := hxy.symm.trans hxz
      have hg : g = 0 := by
        apply Nat.sub_eq_zero_of_le
        (try dsimp [g])
        nlinarith
      have hdiag : ∀ i j : Fin 3, (idx i).val = (idx j).val := by
        have hi : ∀ i : Fin 3, (idx i).val = (idx 0).val := by
          intro i
          fin_cases i
          · rfl
          · exact hxy.symm
          · exact hxz.symm
        intro i j
        exact (hi i).trans (hi j).symm
      have hunit_one : OM.PolMul.unit (F := F) n idx = 1 := by
        simp only [OM.PolMul.unit]
        rw [if_pos hdiag]
      have hRzero : ∀ j, R j idx = 0 := by
        intro j
        simp only [R, hsum, hg, add_zero]
        rw [if_neg]
        omega
      rw [hunit_one, Polynomial.C_1, mul_one]
      rw [hsum, hg, add_zero]
      simp [hRzero]
    · have hgpos : 0 < g := by
        have hne : g ≠ 0 := by
          intro hg
          have heq : 2 * (idx 0).val ^ 2 + 2 * (idx 1).val ^ 2 =
              (2 * (idx 2).val) ^ 2 := by
            dsimp [g] at hg
            omega
          have hsuppZ : 2 * ((idx 2).val : ℤ) =
              (idx 0).val + (idx 1).val := by exact_mod_cast hsupp
          have heqZ : 2 * ((idx 0).val : ℤ) ^ 2 + 2 * ((idx 1).val : ℤ) ^ 2 =
              (2 * ((idx 2).val : ℤ)) ^ 2 := by exact_mod_cast heq
          have hxyZ : ((idx 0).val : ℤ) = (idx 1).val := by
            nlinarith [sq_nonneg (((idx 0).val : ℤ) - (idx 1).val)]
          exact hxy (by exact_mod_cast hxyZ)
        omega
      have hgle : g ≤ q₀ := by
        have hgraw : g ≤ 2 * (idx 0).val ^ 2 + 2 * (idx 1).val ^ 2 := by
          dsimp [g]
          exact Nat.sub_le _ _
        dsimp [q₀]
        nlinarith
      have hunit : OM.PolMul.unit (F := F) n idx = 0 := by
        simp only [OM.PolMul.unit]
        rw [if_neg]
        intro hall
        exact hxy (hall 0 1)
      let j₀ : Fin q₀ := ⟨g - 1, by omega⟩
      have hpol : OM.PolMul.polmul (F := F) n n (fun i => f i (idx i)) = 1 := by
        simp [OM.PolMul.polmul, f, hsupp]
      rw [hunit, Polynomial.C_0, mul_zero, zero_add,
        Finset.sum_eq_single j₀]
      · have hj : q₀ + j₀.val + 1 = q₀ + g := by
          dsimp [j₀]
          omega
        simp only [R, hsum, if_pos hj.symm, hpol, Polynomial.C_1, mul_one]
        rw [hj]
      · intro j _ hjne
        have hR : R j idx = 0 := by
          simp only [R, hsum]
          rw [if_neg]
          intro heq
          apply hjne
          apply Fin.ext
          dsimp [j₀]
          omega
        rw [hR, Polynomial.C_0, mul_zero]
      · simp
  · rw [if_neg hsupp]
    have hunit : OM.PolMul.unit (F := F) n idx = 0 := by
      simp only [OM.PolMul.unit]
      rw [if_neg]
      intro hall
      have h02 := hall 0 2
      have h12 := hall 1 2
      (try simp only at h02 h12)
      omega
    rw [hunit]
    have hpol : OM.PolMul.polmul (F := F) n n (fun i => f i (idx i)) = 0 := by
      simp [OM.PolMul.polmul, f, hsupp]
    have hRzero : ∀ j, R j idx = 0 := by
      intro j
      simp [R, hpol]
    simp [hRzero]

/-- The lemma on two copies.  As in the paper, this is only a
basis reindexing: the copy label becomes the matrix-multiplication index. -/
theorem proof_PM_3 : OM_S_PM_3 := by
  intro F _ d T k
  change OM.PolMul.Iso
    (OM.PolMul.pdsumFamily (fun _ : Fin k => d) (d 0) (fun _ => rfl) (fun _ => T))
    (OM.PolMul.kron T (OM.PolMul.matMul 1 1 k))
  classical
  let e0 : Fin (d 0) ≃ Fin ((d 0 : ℕ) * (1 * 1)) := finOneOneEquiv (d 0)
  let e : ∀ i,
      Fin ((OM.PolMul.fmt (d 0)
        ⟨∑ _ : Fin k, (d 1 : ℕ), Finset.sum_pos (fun _ _ => (d 1).pos)
          Finset.univ_nonempty⟩
        ⟨∑ _ : Fin k, (d 2 : ℕ), Finset.sum_pos (fun _ _ => (d 2).pos)
          Finset.univ_nonempty⟩) i) ≃
      Fin (d i * (OM.PolMul.fmt (1 * 1) (1 * k) (k * 1)) i) := fun i =>
    match i with
    | 0 => e0
    | 1 => repeatOneMulEquiv (k : ℕ) (d 1 : ℕ)
    | 2 => repeatMulOneEquiv (k : ℕ) (d 2 : ℕ)
  apply iso_of_equiv _ _ e
  intro idx
  let iv : (r : Fin k) × Fin (d 1) := finSigmaFinEquiv.symm (idx 1)
  let iw : (r : Fin k) × Fin (d 2) := finSigmaFinEquiv.symm (idx 2)
  simp only [OM.PolMul.pdsumFamily, OM.PolMul.kron, kroneckerTensor, kronLeftIndex,
    kronRightIndex]
  change (if h : iv.1 = iw.1 then
      T (fun | 0 => idx 0 | 1 => iv.2 | 2 => iw.2)
    else 0) = _
  have hleft : kronLeftIndex (fun i => e i (idx i)) =
      (fun | 0 => idx 0 | 1 => iv.2 | 2 => iw.2) := by
    funext i
    fin_cases i
    · change (finProdFinEquiv.symm (e 0 (idx 0))).1 = idx 0
      simpa only [e, e0] using! congrArg Prod.fst
        (finProdFinEquiv_symm_finOneOneEquiv (d 0) (idx 0))
    · change (finProdFinEquiv.symm (e 1 (idx 1))).1 = iv.2
      simpa only [e, iv] using! congrArg Prod.fst
        (finProdFinEquiv_symm_repeatOneMulEquiv (k : ℕ) (d 1) (idx 1))
    · change (finProdFinEquiv.symm (e 2 (idx 2))).1 = iw.2
      simpa only [e, iw] using! congrArg Prod.fst
        (finProdFinEquiv_symm_repeatMulOneEquiv (k : ℕ) (d 2) (idx 2))
  have hright : kronRightIndex (fun i => e i (idx i)) =
      (fun | 0 => finOneMulEquiv 1 (0 : Fin 1)
           | 1 => finOneMulEquiv (k : ℕ) iv.1
           | 2 => finMulOneEquiv (k : ℕ) iw.1) := by
    funext i
    fin_cases i
    · change (finProdFinEquiv.symm (e 0 (idx 0))).2 = _
      simpa only [e, e0] using! congrArg Prod.snd
        (finProdFinEquiv_symm_finOneOneEquiv (d 0) (idx 0))
    · change (finProdFinEquiv.symm (e 1 (idx 1))).2 = _
      simpa only [e, iv] using! congrArg Prod.snd
        (finProdFinEquiv_symm_repeatOneMulEquiv (k : ℕ) (d 1) (idx 1))
    · change (finProdFinEquiv.symm (e 2 (idx 2))).2 = _
      simpa only [e, iw] using! congrArg Prod.snd
        (finProdFinEquiv_symm_repeatMulOneEquiv (k : ℕ) (d 2) (idx 2))
  have hTk := congrArg T hleft
  have hMk := congrArg (OM.PolMul.matMul (F := F) 1 1 k) hright
  refine Eq.trans ?_ (congrArg₂ (fun x y : F => x * y) hTk hMk).symm
  rw [matMul_one_one_apply]
  by_cases h : iv.1 = iw.1
  · rw [dif_pos h]
    simp [h]
  · rw [dif_neg h]
    simp [h]

/-- The proposition on separating partial direct sums.  This follows the paper's monomial
degeneration; the three weights have leading gap `(i-ℓ)^2`. -/
theorem proof_PM_4 : OM_S_PM_4 := by
  intro F _ m q d n h T
  change OM.PolMul.Degen
    (OM.PolMul.kron (OM.PolMul.dsumFamily d T) (OM.PolMul.polmul 1 q))
    (OM.PolMul.kron (OM.PolMul.pdsumFamily d n h T) (OM.PolMul.polmul m q))
  classical
  let D : Fin 3 → ℕ+ := fun j =>
    ⟨∑ i : Fin m, (d i j : ℕ),
      Finset.sum_pos (fun i _ => (d i j).pos) Finset.univ_nonempty⟩
  let dTar : Fin 3 → ℕ+ := fun j =>
    D j * OM.PolMul.fmt 1 q (1 + q - 1) j
  let dSrc : Fin 3 → ℕ+ := fun j =>
    OM.PolMul.fmt n (D 1) (D 2) j * OM.PolMul.fmt m q (m + q - 1) j
  let f : ∀ j, Fin (dTar j) → Fin (dSrc j) := fun j =>
    match j with
    | 0 => fun x =>
      let xp : Fin (D 0) × Fin 1 := finProdFinEquiv.symm x
      let xb : (i : Fin m) × Fin (d i 0) := finSigmaFinEquiv.symm xp.1
      finProdFinEquiv
        (Fin.cast (congrArg (fun z : ℕ+ => (z : ℕ)) (h xb.1)) xb.2, xb.1)
    | 1 => fun x => x
    | 2 => fun x =>
      let xp : Fin (D 2) × Fin ((1 + q - 1 : ℕ+) : ℕ) := finProdFinEquiv.symm x
      let xb : (i : Fin m) × Fin (d i 2) := finSigmaFinEquiv.symm xp.1
      finProdFinEquiv (xp.1, ⟨xb.1.val + xp.2.val, by
        have hi := xb.1.isLt
        have hj : xp.2.val < (q : ℕ) := by
          simpa [pnat_add_sub_one_coe] using! xp.2.isLt
        change xb.1.val + xp.2.val < ((m + q - 1 : ℕ+) : ℕ)
        conv_rhs => rw [pnat_add_sub_one_coe]
        omega⟩)
  let M : ℕ := (m : ℕ)
  let Q : ℕ := (q : ℕ)
  let q₀ : ℕ := 2 * M * (M + Q)
  let e₀ : ℕ := 2 * M ^ 2
  let w : ∀ j, Fin (dTar j) → ℕ := fun j =>
    match j with
    | 0 => fun x =>
      let xp : Fin (D 0) × Fin 1 := finProdFinEquiv.symm x
      let xb : (i : Fin m) × Fin (d i 0) := finSigmaFinEquiv.symm xp.1
      (xb.1.val + 1) ^ 2
    | 1 => fun x =>
      let xp : Fin (D 1) × Fin q := finProdFinEquiv.symm x
      let xb : (i : Fin m) × Fin (d i 1) := finSigmaFinEquiv.symm xp.1
      (xb.1.val + 1) ^ 2 + 2 * (xb.1.val + 1) * xp.2.val
    | 2 => fun x =>
      let xp : Fin (D 2) × Fin ((1 + q - 1 : ℕ+) : ℕ) := finProdFinEquiv.symm x
      let xb : (i : Fin m) × Fin (d i 2) := finSigmaFinEquiv.symm xp.1
      q₀ - 2 * (xb.1.val + 1) * (xb.1.val + xp.2.val + 1)
  let A : ∀ j, Matrix (Fin (dTar j)) (Fin (dSrc j)) (Polynomial F) :=
    fun j x y => if f j x = y then Polynomial.X ^ w j x else 0
  let R : Fin e₀ → OM.PolMul.T3 F dTar := fun r idx =>
    if (∑ j : Fin 3, w j (idx j)) = q₀ + r.val + 1 then
      OM.PolMul.kron (OM.PolMul.pdsumFamily d n h T) (OM.PolMul.polmul m q)
        (fun j => f j (idx j))
    else 0
  refine ⟨q₀, e₀, A, R, ?_⟩
  intro idx
  rw [show (∑ sidx, (∏ j, A j (idx j) (sidx j)) *
        Polynomial.C
          (OM.PolMul.kron (OM.PolMul.pdsumFamily d n h T) (OM.PolMul.polmul m q) sidx)) =
      (∏ j, Polynomial.X ^ w j (idx j)) *
        Polynomial.C
          (OM.PolMul.kron (OM.PolMul.pdsumFamily d n h T) (OM.PolMul.polmul m q)
            (fun j => f j (idx j))) by
    simpa only [A] using! sparse_contraction
      (R := Polynomial F)
      (fun sidx => Polynomial.C
        (OM.PolMul.kron (OM.PolMul.pdsumFamily d n h T) (OM.PolMul.polmul m q) sidx))
      f (fun j x => Polynomial.X ^ w j x) idx]
  rw [Finset.prod_pow_eq_pow_sum]
  let x0 : Fin (D 0) × Fin 1 := finProdFinEquiv.symm (idx 0)
  let x1 : Fin (D 1) × Fin q := finProdFinEquiv.symm (idx 1)
  let x2 : Fin (D 2) × Fin ((1 + q - 1 : ℕ+) : ℕ) :=
    finProdFinEquiv.symm (idx 2)
  let b0 : (i : Fin m) × Fin (d i 0) := finSigmaFinEquiv.symm x0.1
  let b1 : (i : Fin m) × Fin (d i 1) := finSigmaFinEquiv.symm x1.1
  let b2 : (i : Fin m) × Fin (d i 2) := finSigmaFinEquiv.symm x2.1
  have hf0 : finProdFinEquiv.symm (f 0 (idx 0)) =
      (Fin.cast (congrArg (fun z : ℕ+ => (z : ℕ)) (h b0.1)) b0.2, b0.1) := by
    change finProdFinEquiv.symm (finProdFinEquiv
      (Fin.cast (congrArg (fun z : ℕ+ => (z : ℕ)) (h b0.1)) b0.2, b0.1)) = _
    exact Equiv.symm_apply_apply _ _
  have hf1 : finProdFinEquiv.symm (f 1 (idx 1)) = x1 := by
    change finProdFinEquiv.symm (idx 1) = x1
    rfl
  have hf2 : finProdFinEquiv.symm (f 2 (idx 2)) =
      (x2.1, ⟨b2.1.val + x2.2.val, by
        have hi := b2.1.isLt
        have hj : x2.2.val < (q : ℕ) := by
          simpa [pnat_add_sub_one_coe] using! x2.2.isLt
        change b2.1.val + x2.2.val < ((m + q - 1 : ℕ+) : ℕ)
        conv_rhs => rw [pnat_add_sub_one_coe]
        omega⟩) := by
    change finProdFinEquiv.symm (finProdFinEquiv (x2.1, _)) = _
    exact Equiv.symm_apply_apply _ _
  have hTL : kronLeftIndex idx =
      (fun | 0 => x0.1 | 1 => x1.1 | 2 => x2.1) := by
    funext j
    fin_cases j <;> rfl
  have hTR : kronRightIndex idx =
      (fun | 0 => x0.2 | 1 => x1.2 | 2 => x2.2) := by
    funext j
    fin_cases j <;> rfl
  have hSL : kronLeftIndex (fun j => f j (idx j)) =
      (fun | 0 => Fin.cast (congrArg (fun z : ℕ+ => (z : ℕ)) (h b0.1)) b0.2
           | 1 => x1.1 | 2 => x2.1) := by
    funext j
    fin_cases j
    · exact congrArg Prod.fst hf0
    · exact congrArg Prod.fst hf1
    · exact congrArg Prod.fst hf2
  have hSR : kronRightIndex (fun j => f j (idx j)) =
      (fun | 0 => b0.1 | 1 => x1.2
           | 2 => ⟨b2.1.val + x2.2.val, by
             have hi := b2.1.isLt
             have hj : x2.2.val < (q : ℕ) := by
               simpa [pnat_add_sub_one_coe] using! x2.2.isLt
             change b2.1.val + x2.2.val < ((m + q - 1 : ℕ+) : ℕ)
             conv_rhs => rw [pnat_add_sub_one_coe]
             omega⟩) := by
    funext j
    fin_cases j
    · exact congrArg Prod.snd hf0
    · exact congrArg Prod.snd hf1
    · exact congrArg Prod.snd hf2
  have hsval :
      OM.PolMul.kron (OM.PolMul.pdsumFamily d n h T) (OM.PolMul.polmul m q)
          (fun j => f j (idx j)) =
        OM.PolMul.pdsumFamily d n h T
            (fun | 0 => Fin.cast (congrArg (fun z : ℕ+ => (z : ℕ)) (h b0.1)) b0.2
                 | 1 => x1.1 | 2 => x2.1) *
          OM.PolMul.polmul m q
            (fun | 0 => b0.1 | 1 => x1.2
                 | 2 => ⟨b2.1.val + x2.2.val, by
                   have hi := b2.1.isLt
                   have hj : x2.2.val < (q : ℕ) := by
                     simpa [pnat_add_sub_one_coe] using! x2.2.isLt
                   change b2.1.val + x2.2.val < ((m + q - 1 : ℕ+) : ℕ)
                   conv_rhs => rw [pnat_add_sub_one_coe]
                   omega⟩) := by
    unfold OM.PolMul.kron kroneckerTensor
    exact congrArg₂ (fun x y : F => x * y)
      (congrArg (OM.PolMul.pdsumFamily d n h T) hSL)
      (congrArg (OM.PolMul.polmul (F := F) m q) hSR)
  have htval :
      OM.PolMul.kron (OM.PolMul.dsumFamily d T) (OM.PolMul.polmul 1 q) idx =
        OM.PolMul.dsumFamily d T (fun | 0 => x0.1 | 1 => x1.1 | 2 => x2.1) *
          OM.PolMul.polmul 1 q (fun | 0 => x0.2 | 1 => x1.2 | 2 => x2.2) := by
    unfold OM.PolMul.kron kroneckerTensor
    exact congrArg₂ (fun x y : F => x * y)
      (congrArg (OM.PolMul.dsumFamily d T) hTL)
      (congrArg (OM.PolMul.polmul (F := F) 1 q) hTR)
  by_cases hb12 : b1.1 = b2.1
  · have hbval : b2.1.val = b1.1.val := congrArg Fin.val hb12.symm
    have hx0zero : x0.2.val = 0 := by omega
    by_cases hsupp : b2.1.val + x2.2.val = b0.1.val + x1.2.val
    · have hspol : OM.PolMul.polmul (F := F) m q
          (fun | 0 => b0.1 | 1 => x1.2
               | 2 => ⟨b2.1.val + x2.2.val, by
                 have hi := b2.1.isLt
                 have hj : x2.2.val < (q : ℕ) := by
                   simpa [pnat_add_sub_one_coe] using! x2.2.isLt
                 change b2.1.val + x2.2.val < ((m + q - 1 : ℕ+) : ℕ)
                 conv_rhs => rw [pnat_add_sub_one_coe]
                 omega⟩) = 1 := by
        simp [OM.PolMul.polmul, hsupp]
      have hb2M : b2.1.val + 1 ≤ M := by
        dsimp [M]
        omega
      have htail : b2.1.val + x2.2.val + 1 ≤ M + Q := by
        dsimp [M, Q]
        have hq : x2.2.val < (q : ℕ) := by
          simpa [pnat_add_sub_one_coe] using! x2.2.isLt
        omega
      have hsub : 2 * (b2.1.val + 1) * (b2.1.val + x2.2.val + 1) ≤ q₀ := by
        dsimp [q₀]
        exact Nat.mul_le_mul (Nat.mul_le_mul_left 2 hb2M) htail
      let I : ℕ := b0.1.val + 1
      let L : ℕ := b1.1.val + 1
      let g : ℕ := I ^ 2 + L ^ 2 - 2 * I * L
      have hgaple : 2 * I * L ≤ I ^ 2 + L ^ 2 := by
        have hz : 2 * (I : ℤ) * L ≤ (I : ℤ) ^ 2 + (L : ℤ) ^ 2 := by
          nlinarith only [sq_nonneg ((I : ℤ) - L)]
        exact_mod_cast hz
      have hsub' : 2 * (b1.1.val + 1) * (b0.1.val + x1.2.val + 1) ≤ q₀ := by
        rw [← hsupp, ← hbval]
        exact hsub
      have hgaple' : 2 * (b0.1.val + 1) * (b1.1.val + 1) ≤
          (b0.1.val + 1) ^ 2 + (b1.1.val + 1) ^ 2 := by
        simpa [I, L] using! hgaple
      have hsplit : 2 * (b1.1.val + 1) * (b0.1.val + x1.2.val + 1) =
          2 * (b0.1.val + 1) * (b1.1.val + 1) +
            2 * (b1.1.val + 1) * x1.2.val := by ring
      have hsub'' : 2 * (b0.1.val + 1) * (b1.1.val + 1) +
          2 * (b1.1.val + 1) * x1.2.val ≤ q₀ := by
        rw [← hsplit]
        exact hsub'
      have hsum : (∑ j : Fin 3, w j (idx j)) = q₀ + g := by
        rw [Fin.sum_univ_three]
        change (b0.1.val + 1) ^ 2 +
            ((b1.1.val + 1) ^ 2 + 2 * (b1.1.val + 1) * x1.2.val) +
            (q₀ - 2 * (b2.1.val + 1) * (b2.1.val + x2.2.val + 1)) =
          q₀ + ((b0.1.val + 1) ^ 2 + (b1.1.val + 1) ^ 2 -
            2 * (b0.1.val + 1) * (b1.1.val + 1))
        rw [hsupp, hbval]
        rw [hsplit]
        simpa only [add_assoc] using! nat_gap_identity hgaple' hsub''
      have hIM : I ≤ M := by
        dsimp [I, M]
        omega
      have hLM : L ≤ M := by
        dsimp [L, M]
        omega
      have hgle : g ≤ e₀ := by
        calc
          g ≤ I ^ 2 + L ^ 2 := Nat.sub_le _ _
          _ ≤ 2 * M ^ 2 := by
            have hI2 : I ^ 2 ≤ M ^ 2 := by
              simpa [pow_two] using! Nat.mul_self_le_mul_self hIM
            have hL2 : L ^ 2 ≤ M ^ 2 := by
              simpa [pow_two] using! Nat.mul_self_le_mul_self hLM
            omega
      by_cases hIL : I = L
      · have hb01 : b0.1 = b1.1 := by
          apply Fin.ext
          dsimp [I, L] at hIL
          omega
        have hp : x2.2.val = x1.2.val := by
          dsimp [I, L] at hIL
          omega
        have htpol : OM.PolMul.polmul (F := F) 1 q
            (fun | 0 => x0.2 | 1 => x1.2 | 2 => x2.2) = 1 := by
          simp only [OM.PolMul.polmul]
          rw [if_pos]
          omega
        have hsource_target :
            OM.PolMul.kron (OM.PolMul.pdsumFamily d n h T) (OM.PolMul.polmul m q)
                (fun j => f j (idx j)) =
              OM.PolMul.kron (OM.PolMul.dsumFamily d T) (OM.PolMul.polmul 1 q) idx := by
          rw [hsval, htval, hspol, htpol, mul_one, mul_one]
          have hpblock : (finSigmaFinEquiv.symm x1.1).1 =
              (finSigmaFinEquiv.symm x2.1).1 := by
            simpa [b1, b2] using! hb12
          let xt : ∀ j, Fin (D j) := fun j =>
            match j with | 0 => x0.1 | 1 => x1.1 | 2 => x2.1
          change _ = OM.PolMul.dsumFamily d T xt
          have hdblock : ∀ j : Fin 3,
              (finSigmaFinEquiv.symm (xt j)).1 =
                (finSigmaFinEquiv.symm x0.1).1 := by
            intro j
            fin_cases j
            · rfl
            · simpa [xt, b0, b1] using! hb01.symm
            · simpa [xt, b0, b2] using! hb12.symm.trans hb01.symm
          unfold OM.PolMul.pdsumFamily OM.PolMul.dsumFamily
          rw [dif_pos hpblock, dif_pos hdblock]
          have hlab : (finSigmaFinEquiv.symm x1.1).1 =
              (finSigmaFinEquiv.symm x0.1).1 := by
            simpa [b0, b1] using! hb01.symm
          congr 1
          refine Function.hfunext rfl ?_
          intro j j' hj
          have hj' : j = j' := eq_of_heq hj
          subst j'
          refine (Fin.heq_ext_iff
            (congrArg (fun z : Fin m => (d z j : ℕ)) hlab)).2 ?_
          fin_cases j
          <;> rfl
        have hg : g = 0 := by
          apply Nat.sub_eq_zero_of_le
          (try dsimp [g])
          rw [hIL]
          exact le_of_eq (by ring)
        have hRzero : ∀ r, R r idx = 0 := by
          intro r
          simp only [R, hsum, hg, add_zero]
          rw [if_neg]
          omega
        rw [hsource_target, hsum, hg, add_zero]
        simp [hRzero]
      · have hgpos : 0 < g := by
          have hne : g ≠ 0 := by
            intro hg
            have heq : I ^ 2 + L ^ 2 = 2 * I * L := by
              dsimp [g] at hg
              omega
            have heqZ : (I : ℤ) ^ 2 + (L : ℤ) ^ 2 = 2 * I * L := by
              exact_mod_cast heq
            have : (I : ℤ) = L := by
              nlinarith only [sq_nonneg ((I : ℤ) - L), heqZ]
            exact hIL (by exact_mod_cast this)
          omega
        have hdzero : OM.PolMul.dsumFamily d T
            (fun | 0 => x0.1 | 1 => x1.1 | 2 => x2.1) = 0 := by
          unfold OM.PolMul.dsumFamily
          rw [dif_neg]
          intro hall
          apply hIL
          have h0 := hall 0
          have h1 := hall 1
          have hb01val : b0.1.val = b1.1.val := by
            have hb01' : b0.1 = b1.1 := by
              simpa [b0, b1] using! h1.symm
            exact congrArg Fin.val hb01'
          dsimp [I, L]
          omega
        have htval0 : OM.PolMul.kron (OM.PolMul.dsumFamily d T) (OM.PolMul.polmul 1 q) idx = 0 := by
          rw [htval, hdzero, zero_mul]
        let r₀ : Fin e₀ := ⟨g - 1, by omega⟩
        rw [htval0, Polynomial.C_0, mul_zero, zero_add,
          Finset.sum_eq_single r₀]
        · have hr : q₀ + r₀.val + 1 = q₀ + g := by
            dsimp [r₀]
            omega
          simp only [R, hsum, if_pos hr.symm]
          rw [hr]
        · intro r _ hrne
          have hR : R r idx = 0 := by
            simp only [R, hsum]
            rw [if_neg]
            intro heq
            apply hrne
            apply Fin.ext
            dsimp [r₀]
            omega
          rw [hR, Polynomial.C_0, mul_zero]
        · simp
    · have hspol : OM.PolMul.polmul (F := F) m q
          (fun | 0 => b0.1 | 1 => x1.2
               | 2 => ⟨b2.1.val + x2.2.val, by
                 have hi := b2.1.isLt
                 have hj : x2.2.val < (q : ℕ) := by
                   simpa [pnat_add_sub_one_coe] using! x2.2.isLt
                 change b2.1.val + x2.2.val < ((m + q - 1 : ℕ+) : ℕ)
                 conv_rhs => rw [pnat_add_sub_one_coe]
                 omega⟩) = 0 := by
        simp [OM.PolMul.polmul, hsupp]
      have hsval0 : OM.PolMul.kron (OM.PolMul.pdsumFamily d n h T) (OM.PolMul.polmul m q)
          (fun j => f j (idx j)) = 0 := by rw [hsval, hspol, mul_zero]
      have htval0 : OM.PolMul.kron (OM.PolMul.dsumFamily d T) (OM.PolMul.polmul 1 q) idx = 0 := by
        rw [htval]
        by_cases hp : x2.2.val = x1.2.val
        · have hdzero : OM.PolMul.dsumFamily d T
              (fun | 0 => x0.1 | 1 => x1.1 | 2 => x2.1) = 0 := by
            unfold OM.PolMul.dsumFamily
            rw [dif_neg]
            intro hall
            apply hsupp
            have h0 := hall 0
            have h1 := hall 1
            have hb01' : b0.1 = b1.1 := by
              simpa [b0, b1] using! h1.symm
            have hb01val := congrArg Fin.val hb01'
            omega
          rw [hdzero, zero_mul]
        · have htpol : OM.PolMul.polmul (F := F) 1 q
              (fun | 0 => x0.2 | 1 => x1.2 | 2 => x2.2) = 0 := by
            simp only [OM.PolMul.polmul]
            rw [if_neg]
            omega
          rw [htpol, mul_zero]
      have hRzero : ∀ r, R r idx = 0 := by
        intro r
        simp [R, hsval0]
      rw [hsval0, htval0]
      simp [hRzero]
  · have hpzero : OM.PolMul.pdsumFamily d n h T
        (fun | 0 => Fin.cast (congrArg (fun z : ℕ+ => (z : ℕ)) (h b0.1)) b0.2
             | 1 => x1.1 | 2 => x2.1) = 0 := by
      simp only [OM.PolMul.pdsumFamily]
      rw [dif_neg]
      intro hh
      apply hb12
      simpa [b1, b2] using! hh
    have hdzero : OM.PolMul.dsumFamily d T
        (fun | 0 => x0.1 | 1 => x1.1 | 2 => x2.1) = 0 := by
      unfold OM.PolMul.dsumFamily
      rw [dif_neg]
      intro hall
      apply hb12
      have h1 := hall 1
      have h2 := hall 2
      simpa [b1, b2] using! h1.trans h2.symm
    have hsval0 : OM.PolMul.kron (OM.PolMul.pdsumFamily d n h T) (OM.PolMul.polmul m q)
        (fun j => f j (idx j)) = 0 := by rw [hsval, hpzero, zero_mul]
    have htval0 : OM.PolMul.kron (OM.PolMul.dsumFamily d T) (OM.PolMul.polmul 1 q) idx = 0 := by
      rw [htval, hdzero, zero_mul]
    have hRzero : ∀ r, R r idx = 0 := by
      intro r
      simp [R, hsval0]
    rw [hsval0, htval0]
    simp [hRzero]

end OM.PolMul.PolmulBasics
