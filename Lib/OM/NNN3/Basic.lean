import Lib.OM.NNN2.Square

/-! Coordinate tools for the ordinary symmetric-square restriction. -/
noncomputable section
open scoped BigOperators Classical
namespace OM.NNN3
open CoordinateTensor OM.NNN.Raw OM.NNN2

variable {I J K I' J' K' A B C X : Type}

lemma restricts_add [Fintype I] [Fintype J] [Fintype K]
    [Fintype I'] [Fintype J'] [Fintype K']
    {S : Tensor ℂ I J K} {S' : Tensor ℂ I' J' K'}
    {T T' : Tensor ℂ A B C} (h : Restricts S T) (h' : Restricts S' T') :
    Restricts (directSum S S') (T + T') := by
  obtain ⟨u, v, w, rfl⟩ := h
  obtain ⟨u', v', w', rfl⟩ := h'
  refine ⟨(fun a => Sum.elim (u a) (u' a)), (fun b => Sum.elim (v b) (v' b)),
    (fun c => Sum.elim (w c) (w' c)), ?_⟩
  funext a b c
  exact mapTensor_directSum _ _ _ _ _ _ _ _

lemma restricts_neg [Fintype I] [Fintype J] [Fintype K]
    {S : Tensor ℂ I J K} {T : Tensor ℂ A B C} (h : Restricts S T) :
    Restricts S (-T) := by
  obtain ⟨u, v, w, rfl⟩ := h
  refine ⟨-u, v, w, ?_⟩
  funext a b c
  simp [mapTensor, Finset.sum_neg_distrib]

lemma map_mm [Fintype X]
    (U : A → X × X → ℂ) (V : B → X × X → ℂ) (W : C → X × X → ℂ)
    (a : A) (b : B) (c : C) :
    mapTensor U V W (mm X X X) a b c =
      ∑ q, ∑ r, ∑ p, U a (q, p) * V b (r, p) * W c (q, r) :=
  map_squareSource U V W a b c

lemma map_mm_product [Fintype X] [Fintype I] [Fintype J] [Fintype K]
    (T : Tensor ℂ I J K)
    (U : A → (X × X) × I → ℂ) (V : B → (X × X) × J → ℂ)
    (W : C → (X × X) × K → ℂ) (a : A) (b : B) (c : C) :
    mapTensor U V W (tensorProduct (mm X X X) T) a b c =
      ∑ q, ∑ r, ∑ p, ∑ i, ∑ j, ∑ k,
        U a ((q, p), i) * V b ((r, p), j) * W c ((q, r), k) * T i j k := by
  simp only [mapTensor, tensorProduct, mm, Fintype.sum_prod_type,
    mul_ite, ite_mul, mul_one, one_mul, mul_zero, zero_mul, ite_and]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq',
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  apply Finset.sum_congr rfl
  intro q _
  calc
    _ = ∑ p, ∑ r, ∑ i, ∑ j, ∑ k,
      U a ((q, p), i) * V b ((r, p), j) * W c ((q, r), k) * T i j k := by
        apply Finset.sum_congr rfl
        intro p _
        rw [Finset.sum_comm]
    _ = _ := Finset.sum_comm

/-- Unordered pairs supply the symmetric-square bond, with the required
factor two on diagonal pairs in the second embedding. -/
def symU (p : Sym2 X) (a b : X) : ℂ := if p = s(a, b) then 1 else 0

def symV (p : Sym2 X) (a b : X) : ℂ :=
  if p = s(a, b) then (if a = b then 2 else 1) else 0

lemma sym_pairing [Fintype X] (a b c d : X) :
    (∑ p : Sym2 X, symU p a b * symV p c d) =
      (if a = c ∧ b = d then 1 else 0) + (if a = d ∧ b = c then 1 else 0) := by
  simp only [symU, symV, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true, Sym2.eq_iff]
  by_cases hac : a = c <;> by_cases hbd : b = d <;>
    by_cases had : a = d <;> by_cases hbc : b = c <;>
    simp_all <;> norm_num

lemma card_sym (n : ℕ+) : Fintype.card (Sym2 (Fin n)) = (n : ℕ) * ((n : ℕ) + 1) / 2 := by
  rw [Sym2.card, Fintype.card_fin, Nat.choose_two_right]
  simp [Nat.mul_comm]

end OM.NNN3
