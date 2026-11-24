import Lib.Tensor.CubeClass
import Lib.OM.Omega

/-! Rectangular coordinate tensors, including empty index sets. -/

noncomputable section
open scoped BigOperators Classical
set_option maxHeartbeats 1000000

namespace OM.NNN.Raw

open CoordinateTensor AsymptoticSpectrumDuality

variable {I J K I' J' K' A B C : Type}

/-- Put the three coordinate spaces in disjoint parts of a common space. -/
def pad {R : Type*} [Zero R] (T : Tensor R I J K) : Cube R (I ⊕ J ⊕ K)
  | .inl i, .inr (.inl j), .inr (.inr k) => T i j k
  | _, _, _ => 0

def row0 {R : Type*} [Zero R] (U : A → I → R) :
    (A ⊕ B ⊕ C) → (I ⊕ J ⊕ K) → R
  | .inl a, .inl i => U a i
  | _, _ => 0

def row1 {R : Type*} [Zero R] (V : B → J → R) :
    (A ⊕ B ⊕ C) → (I ⊕ J ⊕ K) → R
  | .inr (.inl b), .inr (.inl j) => V b j
  | _, _ => 0

def row2 {R : Type*} [Zero R] (W : C → K → R) :
    (A ⊕ B ⊕ C) → (I ⊕ J ⊕ K) → R
  | .inr (.inr c), .inr (.inr k) => W c k
  | _, _ => 0

theorem map_pad {R : Type*} [CommSemiring R]
    [Fintype I] [Fintype J] [Fintype K]
    (T : Tensor R I J K) (U : A → I → R) (V : B → J → R) (W : C → K → R) :
    mapTensor (row0 U) (row1 V) (row2 W) (pad T) = pad (mapTensor U V W T) := by
  funext a b c
  rcases a with a | (a | a) <;> rcases b with b | (b | b) <;>
    rcases c with c | (c | c) <;>
    simp [mapTensor, pad, row0, row1, row2, Fintype.sum_sum_type]

theorem polyLift_pad (T : Tensor ℂ I J K) : polyLift (pad T) = pad (polyLift T) := by
  funext a b c
  rcases a with a | (a | a) <;> rcases b with b | (b | b) <;>
    rcases c with c | (c | c) <;> simp only [pad, polyLift, map_zero]

theorem degenerates_pad [Fintype I] [Fintype J] [Fintype K]
    {S : Tensor ℂ I J K} {T : Tensor ℂ A B C} (h : Degenerates S T) :
    Degenerates (pad S) (pad T) := by
  obtain ⟨q, U, V, W, h⟩ := h
  refine ⟨q, row0 U, row1 V, row2 W, ?_⟩
  intro a b c
  rw [polyLift_pad, map_pad]
  rcases a with a | (a | a) <;> rcases b with b | (b | b) <;>
    rcases c with c | (c | c) <;> simp only [pad]
  all_goals first | exact h _ _ _ | simp

def value (φ : PolMul.Spectral ℂ) [Fintype I] [Fintype J] [Fintype K]
    (T : Tensor ℂ I J K) : ℝ := AsymptoticSpectrum.eval _ (cubeClass (pad T)) φ

theorem value_mono (φ : PolMul.Spectral ℂ)
    [Fintype I] [Fintype J] [Fintype K] [Fintype A] [Fintype B] [Fintype C]
    {S : Tensor ℂ I J K} {T : Tensor ℂ A B C} (h : Degenerates S T) :
    value φ T ≤ value φ S := eval_cubeClass_mono φ (degenerates_pad h)

theorem value_map_le (φ : PolMul.Spectral ℂ)
    [Fintype I] [Fintype J] [Fintype K] [Fintype A] [Fintype B] [Fintype C]
    (S : Tensor ℂ I J K) (U : A → I → ℂ) (V : B → J → ℂ) (W : C → K → ℂ) :
    value φ (mapTensor U V W S) ≤ value φ S :=
  value_mono φ (restricts_degenerates S _ ⟨U, V, W, rfl⟩)

theorem value_reindex (φ : PolMul.Spectral ℂ)
    [Fintype I] [Fintype J] [Fintype K] [Fintype A] [Fintype B] [Fintype C]
    (S : Tensor ℂ I J K) (e : A ≃ I) (f : B ≃ J) (g : C ≃ K) :
    value φ (fun a b c => S (e a) (f b) (g c)) = value φ S := by
  have h : pad (fun a b c => S (e a) (f b) (g c)) =
      restrict (pad S) (Equiv.sumCongr e (Equiv.sumCongr f g))
        (Equiv.sumCongr e (Equiv.sumCongr f g))
        (Equiv.sumCongr e (Equiv.sumCongr f g)) := by
    funext a b c
    rcases a with a | (a | a) <;> rcases b with b | (b | b) <;>
      rcases c with c | (c | c) <;> rfl
  rw [value, h, cubeClass_reindex]
  rfl

def sumShuffle : ((I ⊕ I') ⊕ (J ⊕ J') ⊕ (K ⊕ K')) ≃
    ((I ⊕ J ⊕ K) ⊕ (I' ⊕ J' ⊕ K')) where
  toFun
    | .inl (.inl i) => .inl (.inl i)
    | .inl (.inr i) => .inr (.inl i)
    | .inr (.inl (.inl j)) => .inl (.inr (.inl j))
    | .inr (.inl (.inr j)) => .inr (.inr (.inl j))
    | .inr (.inr (.inl k)) => .inl (.inr (.inr k))
    | .inr (.inr (.inr k)) => .inr (.inr (.inr k))
  invFun
    | .inl (.inl i) => .inl (.inl i)
    | .inr (.inl i) => .inl (.inr i)
    | .inl (.inr (.inl j)) => .inr (.inl (.inl j))
    | .inr (.inr (.inl j)) => .inr (.inl (.inr j))
    | .inl (.inr (.inr k)) => .inr (.inr (.inl k))
    | .inr (.inr (.inr k)) => .inr (.inr (.inr k))
  left_inv x := by rcases x with (x | x) | ((x | x) | (x | x)) <;> rfl
  right_inv x := by rcases x with (x | (x | x)) | (x | (x | x)) <;> rfl

theorem value_add (φ : PolMul.Spectral ℂ)
    [Fintype I] [Fintype J] [Fintype K] [Fintype I'] [Fintype J'] [Fintype K']
    (S : Tensor ℂ I J K) (T : Tensor ℂ I' J' K') :
    value φ (directSum S T) = value φ S + value φ T := by
  have h : pad (directSum S T) =
      restrict (directSum (pad S) (pad T)) sumShuffle sumShuffle sumShuffle := by
    funext a b c
    rcases a with (a | a) | ((a | a) | (a | a)) <;>
      rcases b with (b | b) | ((b | b) | (b | b)) <;>
      rcases c with (c | c) | ((c | c) | (c | c)) <;> rfl
  rw [value, h, cubeClass_reindex, cubeClass_add]
  exact φ.map_add _ _

open Semicontinuity Foundations.HyperbolicLift

/-- The rectangular encoding has exactly the original tensor class. -/
theorem cubeClass_pad (d : Fin 3 → ℕ+) (T : KTensor ℂ d) :
    cubeClass (pad (fun a b c => T (idx3 a b c))) =
      TensorClass.mk ⟨d, T⟩ := by
  let Q := Fin (d 0) ⊕ Fin (d 1) ⊕ Fin (d 2)
  let m : ℕ+ := ⟨Fintype.card Q, Fintype.card_pos⟩
  let e : Fin m ≃ Q := (Fintype.equivFin Q).symm
  rw [cubeClass_eq e]
  apply TensorClass.mk_eq_of_equiv
  constructor
  · refine ⟨legTriple
      (fun a b => if e a = Sum.inl b then 1 else 0)
      (fun a b => if e a = Sum.inr (Sum.inl b) then 1 else 0)
      (fun a b => if e a = Sum.inr (Sum.inr b) then 1 else 0), ?_⟩
    intro g
    rw [sum_pi_fin3]
    simp only [Fin.prod_univ_three, legTriple_zero, legTriple_one, legTriple_two,
      idx3_zero, idx3_one, idx3_two, cubeToK]
    generalize e (g 0) = a, e (g 1) = b, e (g 2) = c
    dsimp only [Q] at *
    rcases a with a | (a | a) <;> rcases b with b | (b | b) <;>
      rcases c with c | (c | c) <;>
      simp only [pad, Sum.inl.injEq, Sum.inr.injEq, Sum.inl_ne_inr, Sum.inr_ne_inl,
        ite_true, ite_false, ite_mul, mul_ite, zero_mul, mul_zero, one_mul, mul_one,
        Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, Finset.sum_const_zero]
  · let f : ∀ i, Fin (d i) → Fin m := fun i =>
      match i with
      | 0 => fun a => e.symm (Sum.inl a)
      | 1 => fun b => e.symm (Sum.inr (Sum.inl b))
      | 2 => fun c => e.symm (Sum.inr (Sum.inr c))
    apply Lib.E.restricts_of_indices f
    intro g
    simp only [cubeToK, f, Equiv.apply_symm_apply, pad]
    rw [idx3_eta]

theorem value_encode (φ : PolMul.Spectral ℂ) {d : Fin 3 → ℕ+} (T : KTensor ℂ d) :
    value φ (fun a b c => T (idx3 a b c)) = PolMul.Spectral.eval φ T := by
  change AsymptoticSpectrumDuality.AsymptoticSpectrum.eval _
    (cubeClass _) φ = _
  rw [cubeClass_pad]
  rfl

theorem value_zero (φ : PolMul.Spectral ℂ) [Fintype I] [Fintype J] [Fintype K] :
    value φ (0 : Tensor ℂ I J K) = 0 := by
  have h : pad (0 : Tensor ℂ I J K) = 0 := by
    funext a b c
    rcases a with a | (a | a) <;> rcases b with b | (b | b) <;>
      rcases c with c | (c | c) <;> rfl
  simp only [value, h, cubeClass_zero,
    AsymptoticSpectrumDuality.AsymptoticSpectrum.eval_zero]

end OM.NNN.Raw
