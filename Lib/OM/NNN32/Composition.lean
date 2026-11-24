import Lib.OM.NNN32.Splits
import Mathlib.Tactic.LinearCombination
import PLATFORM.Statements.«R113.14»

/-! # Partial-transpose rank and bilinear composition formulas over the complex numbers -/

noncomputable section

namespace OM.NNN32

open Semicontinuity OM.NNN30.Net

abbrev Vec (D : ℕ+) := Index D → ℂ
abbrev Form (D : ℕ+) := Vec D →ₗ[ℂ] Vec D →ₗ[ℂ] ℂ
def Q {D} (a : Vec D) := ∑ i, a i ^ 2
def pairing {D} (a b : Vec D) := ∑ i, a i * b i

def compLengths (D : ℕ+) := {k : ℕ | ∃ F : Fin k → Form D,
    ∀ a b, Q a * Q b = ∑ j, (F j a b)^2}

private def evalRow {D} (T : Four D) (a b : Vec D) : ℂ :=
  ∑ i : Index D × Index D, ∑ j : Index D × Index D,
    (a i.1*b i.2)*(a j.2*b j.1)*rowMatrix T i j

private lemma evalCol {D} (T : Four D) (a b : Vec D) :
    evalRow T a b = ∑ i : Index D × Index D, ∑ j : Index D × Index D,
      (a i.1*b i.2)*(a j.2*b j.1)*colMatrix T i j := by
  simp only [evalRow,Fintype.sum_prod_type,rowMatrix,colMatrix]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_comm]
  congr 1
  funext y
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro v _
  ring

private lemma eval_crossing (D : ℕ+) (a b : Vec D) : evalRow (crossing D) a b = Q a * Q b := by
  classical
  have he (x y u v : Index D) : rowMatrix (crossing D) (x,y) (u,v) =
      if x=v ∧ y=u then 1 else 0 := by rfl
  simp only [evalRow,Fintype.sum_prod_type,he,mul_ite,mul_one,mul_zero,ite_and]
  simp only [Finset.sum_ite_eq,Finset.mem_univ,ite_true,Q]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  ring

private lemma eval_factors {D : ℕ+} {m : ℕ}
    {M : Matrix (Index D × Index D) (Index D × Index D) ℂ}
    {U : Index D × Index D → Fin m → ℂ} {W : Fin m → Index D × Index D → ℂ}
    (hf : ∀ i j, M i j = ∑ k, U i k * W k j) :
    ∃ F G : Fin m → Form D, ∀ a b : Vec D,
      (∑ i : Index D × Index D, ∑ j : Index D × Index D,
        (a i.1*b i.2)*(a j.2*b j.1)*M i j) = ∑ k, F k a b * G k a b := by
  let F k := Matrix.toBilin' (Matrix.of fun i j : Index D => U (i,j) k)
  let G k := Matrix.toBilin' (Matrix.of fun i j : Index D => W k (j,i))
  have hF k (a b : Vec D) : F k a b = ∑ i : Index D × Index D, (a i.1*b i.2)*U i k := by
    simp [F,Matrix.toBilin'_apply,Fintype.sum_prod_type,mul_right_comm]
  have hG k (a b : Vec D) : G k a b = ∑ j : Index D × Index D, (a j.2*b j.1)*W k j := by
    simp only [G,Matrix.toBilin'_apply,Matrix.of_apply,Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    simp only [mul_right_comm]
  refine ⟨F,G,fun a b => ?_⟩
  simp only [hf,hF,hG,Finset.sum_mul,Finset.mul_sum]
  conv_lhs =>
    enter [2,i]
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- A product of two bilinear forms is a sum of two complex squares. -/
private lemma two_squares {D} (F G : Form D) :
    ∃ A B : Form D, ∀ x y, F x y * G x y = (A x y)^2 + (B x y)^2 := by
  refine ⟨(2:ℂ)⁻¹ • (F+G), (Complex.I/2) • (F-G), fun x y => ?_⟩
  simp only [LinearMap.smul_apply,LinearMap.add_apply,LinearMap.sub_apply,smul_eq_mul]
  linear_combination (-(F x y-G x y)^2/4) * Complex.I_sq

private lemma comp_from_split (D : ℕ+) :
    2 * P D ∈ compLengths D := by
  classical
  obtain ⟨R,S,hadd,hcost⟩ := (split_min D).1
  rw [← rowMatrix_rank,← colMatrix_rank] at hcost
  obtain ⟨_,_,hR⟩ := exists_rank_factor (rowMatrix R)
  obtain ⟨_,_,hS⟩ := exists_rank_factor (colMatrix S)
  obtain ⟨F,G,hFG⟩ := eval_factors hR
  obtain ⟨H,K,hHK⟩ := eval_factors hS
  let f := Fin.append F H
  let g := Fin.append G K
  have heval (a b : Vec D) : Q a * Q b = ∑ j, f j a b * g j a b := by
    rw [← eval_crossing,← hadd]
    have hsum : evalRow (R+S) a b = evalRow R a b + evalRow S a b := by
      unfold evalRow
      simp only [rowMatrix,coeff,Pi.add_apply,mul_add,Finset.sum_add_distrib]
    rw [hsum,evalCol S,evalRow,hFG a b,hHK a b]
    conv_rhs => rw [Fin.sum_univ_add]
    simp [f,g,Fin.append]
  choose A B hAB using fun j => two_squares (f j) (g j)
  rw [hcost,two_mul]
  use Fin.append A B
  intro a b
  rw [heval]
  conv_rhs => rw [Fin.sum_univ_add]
  simp only [hAB,Finset.sum_add_distrib,Fin.append_left,Fin.append_right]

lemma sigma_min (D : ℕ+) : IsLeast (compLengths D) (sigma D) :=
  isLeast_csInf ⟨_,comp_from_split D⟩

private lemma Q_add {D} (a b : Vec D) : Q (a+b) = Q a + 2*pairing a b + Q b := by
  simp only [Q,pairing,Pi.add_apply,add_sq,Finset.sum_add_distrib,Finset.mul_sum,mul_assoc]

private lemma polarize {D k} (F : Fin k → Form D)
    (hF : ∀ a b, Q a * Q b = ∑ j, (F j a b)^2) (a a' b b' : Vec D) :
    2 * pairing a a' * pairing b b' =
      ∑ j, (F j a b * F j a' b' + F j a b' * F j a' b) := by
  have first (y : Vec D) : pairing a a' * Q y = ∑ j, F j a y * F j a' y := by
    have h := hF (a+a') y
    simp only [Q_add,map_add,LinearMap.add_apply,add_sq,Finset.sum_add_distrib,mul_assoc,
      ← Finset.mul_sum] at h
    linear_combination (h - hF a y - hF a' y)/2
  have h := first (b+b')
  simp only [Q_add,map_add,add_mul,mul_add,Finset.sum_add_distrib] at h
  rw [Finset.sum_add_distrib]
  linear_combination h - first b - first b'

private def basisVector {D : ℕ+} (i : Index D) : Vec D := Pi.single i 1

private lemma pairing_basis {D : ℕ+} (i j : Index D) :
    pairing (basisVector i) (basisVector j) = if i=j then 1 else 0 := by
  classical
  simp [pairing,basisVector,Pi.single_apply,eq_comm]

private lemma rank_from_factor {A B : Type} [Fintype A] [Fintype B] {m : ℕ}
    (M : Matrix A B ℂ) (U : Matrix A (Fin m) ℂ) (V : Matrix (Fin m) B ℂ)
    (h : ∀ i j, M i j = ∑ l, U i l * V l j) : M.rank ≤ m := by
  have he : M = U*V := funext fun i => funext (h i)
  rw [he]
  simpa using (Matrix.rank_mul_le_left U V).trans U.rank_le_card_width

private lemma polarized_bounds (D : ℕ+) : (D : ℕ) ≤ sigma D ∧ P D ≤ 2*sigma D := by
  classical
  obtain ⟨F,hF⟩ := (sigma_min D).1
  let A j (x y : Index D) := F j (basisVector x) (basisVector y)
  have pol (x v y u : Index D) : 2 * (if x=v ∧ y=u then (1:ℂ) else 0) =
      ∑ j, (A j x y * A j v u + A j x u * A j v y) := by
    have h := polarize F hF (basisVector x) (basisVector v) (basisVector y) (basisVector u)
    by_cases hx : x=v <;> by_cases hy : y=u <;> simpa [A,pairing_basis,hx,hy] using h
  constructor
  · let x : Index D := ⟨0,D.2⟩
    have hid (i j : Index D) : (1 : Matrix (Index D) (Index D) ℂ) i j =
        ∑ l, A l x i * A l x j := by
      have h := pol x x i j
      simp only [true_and,eq_self,mul_comm (A _ x j) (A _ x i),← two_mul,← Finset.mul_sum] at h
      simpa [Matrix.one_apply] using (mul_left_cancel₀ (by norm_num : (2:ℂ) ≠ 0) h)
    simpa using rank_from_factor 1 (fun i l => A l x i) (fun l j => A l x j) hid
  · let R : Four D := fun x => ∑ j, (A j (x 0) (x 1)/2)*A j (x 3) (x 2)
    let S : Four D := fun x => ∑ j, (A j (x 0) (x 2)/2)*A j (x 3) (x 1)
    have hadd : R+S = crossing D := by
      funext x
      have h := pol (x 0) (x 3) (x 1) (x 2)
      simp only [Finset.sum_add_distrib] at h
      simp only [Pi.add_apply,R,S,crossing,matching,div_mul_eq_mul_div,← Finset.sum_div]
      linear_combination -h / 2
    have hr := rank_from_factor (rowMatrix R) (fun i j => A j i.1 i.2/2)
      (fun j i => A j i.2 i.1) (fun _ _ => rfl)
    have hs := rank_from_factor (colMatrix S) (fun i j => A j i.1 i.2/2)
      (fun j i => A j i.2 i.1) (fun _ _ => rfl)
    rw [rowMatrix_rank] at hr
    rw [colMatrix_rank] at hs
    exact (split_min D).2 ⟨R,S,hadd,rfl⟩ |>.trans ((Nat.add_le_add hr hs).trans_eq (two_mul _).symm)

theorem proof_R113_14 : S_R113_14 := fun D =>
  ⟨size_le_P D,P_le_cost (expansion_isLeast _).1,(polarized_bounds D).1,(polarized_bounds D).2,
    (sigma_min D).2 (comp_from_split D)⟩

end OM.NNN32
