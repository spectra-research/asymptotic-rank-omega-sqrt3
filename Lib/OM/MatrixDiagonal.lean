import Lib.OM.PolMul.DegenAsymp

/-! # A diagonal in rectangular matrix multiplication

The three legs of ⟨n,n,2n⟩ record (i,j), (j,k), and (k,i). On its support
the sum of three nonnegative integer weights is (2n)² + (i+j-k)². Its
lowest coefficient therefore consists of the n² disjoint triples with k=i+j.
-/

namespace OM.PolMul

open Semicontinuity DegenAsymp

private lemma weight_min (x y N : ℕ) (hx : x ≤ N) (hy : y ≤ N) :
    let w := (N-x)^2 + 2*x*(N-y) + y^2
    N^2 ≤ w ∧ (w = N^2 ↔ x = y) := by
  dsimp only
  zify [hx, hy]
  constructor
  · nlinarith [sq_nonneg ((x : ℤ) - y)]
  · constructor
    · intro h
      apply sub_eq_zero.mp
      apply (sq_eq_zero_iff).mp
      nlinarith
    · intro h
      rw [h]
      ring

/-- The n² diagonal terms are the leading coefficient of a monomial
restriction of the rectangular matrix multiplication tensor. -/
private lemma matrix_diagonal_leading {F : Type*} [Field F] (n : ℕ+) :
    Leading (unitTensor F (k := 3) (n*n)) (matMul n n (n+n)) ((n+n : ℕ)^2) := by
  classical
  let p : Fin (n*n : ℕ+) ≃ Fin n × Fin n := finProdFinEquiv.symm
  let total (r : Fin (n*n : ℕ+)) : Fin (n+n : ℕ+) :=
    ⟨(p r).1.val + (p r).2.val, Nat.add_lt_add (p r).1.isLt (p r).2.isLt⟩
  let src := fmt (n*n) (n*(n+n)) ((n+n)*n)
  let pick : (i : Fin 3) → Fin (n*n : ℕ+) → Fin (src i)
    | 0, r => r
    | 1, r => finProdFinEquiv ((p r).2, total r)
    | 2, r => finProdFinEquiv (total r, (p r).1)
  let N := (n : ℕ) + n
  let w : Fin 3 → Fin (n*n : ℕ+) → ℕ
    | 0, r => (N - (total r).val)^2
    | 1, r => 2*(p r).2.val*(N - (total r).val)
    | 2, r => 2*(p r).1.val*(N - (total r).val) + (total r).val^2
  let A (i : Fin 3) (r : Fin (n*n : ℕ+)) (s : Fin (src i)) : Polynomial F :=
    if s = pick i r then Polynomial.X ^ w i r else 0
  have entry (g : Fin 3 → Fin (n*n : ℕ+)) :
      (matMul (F := F) n n (n+n)) (fun i => pick i (g i)) =
        if (p (g 0)).2 = (p (g 1)).2 ∧ total (g 1) = total (g 2) ∧
          (p (g 2)).1 = (p (g 0)).1 then 1 else 0 := by
    change (if (p (g 0)).2 = (finProdFinEquiv.symm (finProdFinEquiv ((p (g 1)).2, total (g 1)))).1 ∧
      (finProdFinEquiv.symm (finProdFinEquiv ((p (g 1)).2, total (g 1)))).2 =
        (finProdFinEquiv.symm (finProdFinEquiv (total (g 2), (p (g 2)).1))).1 ∧
      (finProdFinEquiv.symm (finProdFinEquiv (total (g 2), (p (g 2)).1))).2 = (p (g 0)).1
      then (1 : F) else 0) = _
    simp only [Equiv.symm_apply_apply]
  have contract (g : Fin 3 → Fin (n*n : ℕ+)) :
      contraction (matMul (F := F) n n (n+n)) A g =
        Polynomial.X ^ (∑ i, w i (g i)) *
          Polynomial.C (matMul n n (n+n) (fun i => pick i (g i))) := by
    unfold contraction
    rw [Finset.sum_eq_single (fun i => pick i (g i))]
    · simp [A, Fin.prod_univ_three, Fin.sum_univ_three, pow_add, mul_assoc]
    · intro s _ hs
      obtain ⟨i, hi⟩ := Function.ne_iff.mp hs
      rw [Finset.prod_eq_zero (Finset.mem_univ i) (by simp [A, hi]), zero_mul]
    · simp
  have onSupport (g : Fin 3 → Fin (n*n : ℕ+))
      (hb : (p (g 0)).2 = (p (g 1)).2) (hk : total (g 1) = total (g 2))
      (ha : (p (g 2)).1 = (p (g 0)).1) :
      N^2 ≤ ∑ i, w i (g i) ∧ ((∑ i, w i (g i)) = N^2 ↔ ∀ i j, g i = g j) := by
    have hw := weight_min (total (g 0)).val (total (g 2)).val N
      (total (g 0)).isLt.le (total (g 2)).isLt.le
    have hsum : (∑ i, w i (g i)) = (N-(total (g 0)).val)^2 +
        2*(total (g 0)).val*(N-(total (g 2)).val) + (total (g 2)).val^2 := by
      simp only [Fin.sum_univ_three, w, ← hb, hk, ha]
      dsimp [total]
      ring
    rw [hsum]
    refine ⟨hw.1, hw.2.trans ⟨?_, fun h => congrArg (fun r => (total r).val) (h 0 2)⟩⟩
    intro he
    have he' := congrArg Fin.val hk
    change (p (g 0)).1.val + (p (g 0)).2.val = (p (g 2)).1.val + (p (g 2)).2.val at he
    change (p (g 1)).1.val + (p (g 1)).2.val = (p (g 2)).1.val + (p (g 2)).2.val at he'
    rw [← hb, ha] at he'
    rw [ha] at he
    have h01 : g 0 = g 1 := p.injective (Prod.ext (Fin.ext (by omega)) hb)
    have h02 : g 0 = g 2 := p.injective (Prod.ext ha.symm (Fin.ext (by omega)))
    intro i j
    fin_cases i <;> fin_cases j <;> simp_all
  apply leading_of_coeff (N^2) A
  · intro g t ht
    rw [contract, entry]
    split_ifs with h
    · have hlt := ht.trans_le (onSupport g h.1 h.2.1 h.2.2).1
      simp [Polynomial.coeff_X_pow, hlt.ne]
    · simp
  · intro g
    rw [contract, entry, unitTensor]
    split_ifs with h hd hd
    · have he := (onSupport g h.1 h.2.1 h.2.2).2.mpr hd
      simp [he, Polynomial.coeff_X_pow]
    · have he := mt (onSupport g h.1 h.2.1 h.2.2).2.mp hd
      simp [Polynomial.coeff_X_pow, Ne.symm he]
    · exact (h ⟨congrArg (fun r => (p r).2) (hd 0 1), congrArg total (hd 1 2),
        congrArg (fun r => (p r).1) (hd 2 0)⟩).elim
    · simp

/-- Every spectral point evaluates ⟨n,n,2n⟩ at least n². -/
theorem square_le_eval_matMul {F : Type*} [Field F] (φ : Spectral F) (n : ℕ+) :
    ((n : ℕ) : ℝ)^2 ≤ Spectral.eval φ (matMul n n (n+n)) := by
  have h := (matrix_diagonal_leading (F := F) n).eval_le φ
  change AsymptoticSpectrumDuality.AsymptoticSpectrum.eval _
    (TensorClass.mk ⟨_, unitTensor F (k := 3) (n*n)⟩) φ ≤ _ at h
  rw [unit_class, AsymptoticSpectrumDuality.AsymptoticSpectrum.eval_natCast] at h
  simpa only [PNat.mul_coe, Nat.cast_mul, sq] using h

end OM.PolMul
