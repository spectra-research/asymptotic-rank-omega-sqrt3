import Lib.E.RectangularSpectrum
import Foundations.Tensors.OrientationTransport

namespace Lib.E.RectangularSpectrum
noncomputable section
open scoped BigOperators Classical
open Semicontinuity CoordinateTensor Foundations.OrientationTransport

def wordPower {I J H : Type} (S : Tensor ℂ I J H) (n : ℕ) :
    Tensor ℂ (Fin n → I) (Fin n → J) (Fin n → H) :=
  fun a b c => ∏ i, S (a i) (b i) (c i)

def splitWord (I : Type) (n : ℕ) : (Fin (n + 1) → I) ≃ I × (Fin n → I) where
  toFun f := (f 0, fun i => f i.succ)
  invFun p := Fin.cases p.1 p.2
  left_inv f := funext fun i => by refine Fin.cases rfl (fun _ => rfl) i
  right_inv p := rfl

theorem cls_wordPower {I J H : Type} [Fintype I] [Fintype J] [Fintype H]
    [Nonempty I] [Nonempty J] [Nonempty H] (S : Tensor ℂ I J H) (n : ℕ) :
    cls (wordPower S n) = cls S ^ n := by
  induction n with
  | zero =>
    rw [pow_zero]
    change cls _ = TensorClass.mk ⟨_, unitTensor ℂ 1⟩
    refine cls_eq _ _ (by exact Equiv.ofUnique (Fin 1) (Fin 0 → I))
      (by exact Equiv.ofUnique (Fin 1) (Fin 0 → J)) (by exact Equiv.ofUnique (Fin 1) (Fin 0 → H)) ?_
    intro idx
    simp only [unitTensor, wordPower, Finset.univ_eq_empty, Finset.prod_empty]
    rw [if_pos (fun i j => (Subsingleton.elim (α := Fin 1) (idx i) (idx j)))]
  | succ n ih =>
    have he : wordPower S (n + 1) =
        restrict (tensorProduct S (wordPower S n))
          (splitWord I n) (splitWord J n) (splitWord H n) := by
      funext a b c
      exact Fin.prod_univ_succ _
    rw [he, cls_reindex, cls_mul, ih, pow_succ']

def swap02 {I J H : Type} (S : Tensor ℂ I J H) : Tensor ℂ H J I :=
  fun c b a => S a b c
def swap12 {I J H : Type} (S : Tensor ℂ I J H) : Tensor ℂ I H J :=
  fun a c b => S a b c

theorem cls_swap02 {I J H : Type} [Fintype I] [Fintype J] [Fintype H]
    [Nonempty I] [Nonempty J] [Nonempty H] (S : Tensor ℂ I J H) :
    cls (swap02 S) = legPermEquiv (rot 0) (cls S) := by
  symm
  apply legPermEquiv_mk_eq
  · intro i; fin_cases i <;> rfl
  · intro jdx ρ h
    have h0 := Fin.ext (h 0)
    have h1 := Fin.ext (h 1)
    have h2 := Fin.ext (h 2)
    change S ((enumeration I) (ρ 0)) ((enumeration J) (ρ 1)) ((enumeration H) (ρ 2)) =
      S ((enumeration I) (jdx 2)) ((enumeration J) (jdx 1)) ((enumeration H) (jdx 0))
    rw [h0, h1, h2]
    rfl

theorem cls_swap12 {I J H : Type} [Fintype I] [Fintype J] [Fintype H]
    [Nonempty I] [Nonempty J] [Nonempty H] (S : Tensor ℂ I J H) :
    cls (swap12 S) = legPermEquiv (rot 1) (cls S) := by
  symm
  apply legPermEquiv_mk_eq
  · intro i; fin_cases i <;> rfl
  · intro jdx ρ h
    have h0 := Fin.ext (h 0)
    have h1 := Fin.ext (h 1)
    have h2 := Fin.ext (h 2)
    change S ((enumeration I) (ρ 0)) ((enumeration J) (ρ 1)) ((enumeration H) (ρ 2)) =
      S ((enumeration I) (jdx 0)) ((enumeration J) (jdx 2)) ((enumeration H) (jdx 1))
    rw [h0, h1, h2]
    rfl

end
end Lib.E.RectangularSpectrum
