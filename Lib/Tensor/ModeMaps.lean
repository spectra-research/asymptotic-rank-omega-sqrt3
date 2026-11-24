import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Data.Fintype.BigOperators

/-! Coordinate tensors on three finite index sets. The rows of each mode map
index target coordinates and its columns index source coordinates. -/

namespace CoordinateTensor

noncomputable section
open scoped BigOperators Classical
open Polynomial

abbrev Tensor (K I J L : Type*) := I → J → L → K
abbrev Cube (K I : Type*) := Tensor K I I I

def restrict {K I J L A B C : Type*} (T : Tensor K I J L)
    (a : A → I) (b : B → J) (c : C → L) : Tensor K A B C :=
  fun i j k => T (a i) (b j) (c k)

def directSum {K I J L I' J' L' : Type*} [Zero K]
    (S : Tensor K I J L) (T : Tensor K I' J' L') :
    Tensor K (I ⊕ I') (J ⊕ J') (L ⊕ L')
  | .inl i, .inl j, .inl k => S i j k
  | .inr i, .inr j, .inr k => T i j k
  | _, _, _ => 0

def tensorProduct {K I J L I' J' L' : Type*} [Mul K]
    (S : Tensor K I J L) (T : Tensor K I' J' L') :
    Tensor K (I × I') (J × J') (L × L') :=
  fun i j k => S i.1 j.1 k.1 * T i.2 j.2 k.2

def mapTensor {K I J L A B C : Type*} [CommSemiring K]
    [Fintype I] [Fintype J] [Fintype L]
    (U : A → I → K) (V : B → J → K) (W : C → L → K)
    (T : Tensor K I J L) : Tensor K A B C :=
  fun i j k => ∑ a, ∑ b, ∑ c, U i a * V j b * W k c * T a b c

def polyLift {K I J L : Type*} [Semiring K] (T : Tensor K I J L) :
    Tensor K[X] I J L := fun i j k => Polynomial.C (T i j k)

/-- A single polynomial degeneration certificate of specified order. The lower
coefficients vanish and the coefficient of order `q` is exactly the target.
This is equivalent to `mapTensor ... S = X^q * (T + X * error)` coefficientwise. -/
def DegeneratesAt {K I J L A B C : Type*} [CommSemiring K]
    [Fintype I] [Fintype J] [Fintype L]
    (q : ℕ) (S : Tensor K I J L) (T : Tensor K A B C)
    (U : A → I → K[X]) (V : B → J → K[X]) (W : C → L → K[X]) : Prop :=
  ∀ i j k, (mapTensor U V W (polyLift S) i j k).coeff q = T i j k ∧
    ∀ d < q, (mapTensor U V W (polyLift S) i j k).coeff d = 0

def Degenerates {K I J L A B C : Type*} [CommSemiring K]
    [Fintype I] [Fintype J] [Fintype L]
    (S : Tensor K I J L) (T : Tensor K A B C) : Prop :=
  ∃ q U V W, DegeneratesAt q S T U V W

/-- Restriction by linear maps in the three modes. -/
def Restricts {K I J L A B C : Type*} [CommSemiring K]
    [Fintype I] [Fintype J] [Fintype L]
    (S : Tensor K I J L) (T : Tensor K A B C) : Prop :=
  ∃ U V W, mapTensor U V W S = T

def diagonal (K I : Type*) [Zero K] [One K] [DecidableEq I] : Cube K I :=
  fun i j k => if i = j ∧ j = k then 1 else 0

section
variable {K I J L A B C I' J' L' : Type*} [CommSemiring K]
variable [Fintype I] [Fintype J] [Fintype L] [Fintype I'] [Fintype J'] [Fintype L']

theorem mapTensor_directSum (S : Tensor K I J L) (T : Tensor K I' J' L')
    (U : A → I ⊕ I' → K) (V : B → J ⊕ J' → K) (W : C → L ⊕ L' → K)
    (i : A) (j : B) (k : C) :
    mapTensor U V W (directSum S T) i j k =
      mapTensor (fun i a => U i (.inl a)) (fun j b => V j (.inl b))
        (fun k c => W k (.inl c)) S i j k +
      mapTensor (fun i a => U i (.inr a)) (fun j b => V j (.inr b))
        (fun k c => W k (.inr c)) T i j k := by
  simp [mapTensor, Fintype.sum_sum_type, directSum, Finset.sum_add_distrib]

theorem polyLift_map (U : A → I → K) (V : B → J → K) (W : C → L → K)
    (T : Tensor K I J L) :
    polyLift (mapTensor U V W T) =
      mapTensor (fun a i => Polynomial.C (U a i)) (fun b j => Polynomial.C (V b j))
        (fun c k => Polynomial.C (W c k)) (polyLift T) := by
  funext a b c
  simp [polyLift, mapTensor]

theorem restricts_degenerates (S : Tensor K I J L) (T : Tensor K A B C)
    (h : Restricts S T) : Degenerates S T := by
  obtain ⟨U, V, W, h⟩ := h
  refine ⟨0, (fun a i => Polynomial.C (U a i)), (fun b j => Polynomial.C (V b j)),
    (fun c k => Polynomial.C (W c k)), ?_⟩
  intro a b c
  rw [← polyLift_map, h]
  simp [polyLift]

end

end
end CoordinateTensor
