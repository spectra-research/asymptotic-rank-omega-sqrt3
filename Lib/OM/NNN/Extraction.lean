import Lib.OM.NNN.RawTensor

noncomputable section
open scoped BigOperators Classical
set_option maxHeartbeats 1000000

namespace OM.NNN.Raw

open CoordinateTensor Polynomial

variable {I J K A B C A' B' C' : Type}
variable [Fintype I] [Fintype J] [Fintype K]

theorem map_scale_rows {R : Type*} [CommSemiring R]
    (S : Tensor R I J K) (U : A → I → R) (V : B → J → R) (W : C → K → R)
    (r : A → R) (s : B → R) (t : C → R) (a : A) (b : B) (c : C) :
    mapTensor (fun a i => r a * U a i) (fun b j => s b * V b j)
      (fun c k => t c * W c k) S a b c =
        r a * s b * t c * mapTensor U V W S a b c := by
  simp only [mapTensor, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem map_monomial [Fintype A] [Fintype B] [Fintype C] (S : Tensor ℂ I J K)
    (U : A → I → ℂ) (V : B → J → ℂ) (W : C → K → ℂ)
    (r : A → ℕ) (s : B → ℕ) (t : C → ℕ) (a : A) (b : B) (c : C) :
    mapTensor (fun a i => X ^ r a * Polynomial.C (U a i))
      (fun b j => X ^ s b * Polynomial.C (V b j))
      (fun c k => X ^ t c * Polynomial.C (W c k)) (polyLift S) a b c =
      Polynomial.monomial (r a + s b + t c) (mapTensor U V W S a b c) := by
  rw [map_scale_rows, ← CoordinateTensor.polyLift_map]
  simp only [polyLift]
  rw [← pow_add, ← pow_add, mul_comm, Polynomial.C_mul_X_pow_eq_monomial]

/-- Simultaneous extraction: the three vanishing blocks remove all terms
below degree two, while the retained tensor and edge family have degree two. -/
theorem extract [Fintype A] [Fintype B] [Fintype C]
    [Fintype A'] [Fintype B'] [Fintype C'] (S : Tensor ℂ I J K)
    (U : A → I → ℂ) (V : B → J → ℂ) (W : C → K → ℂ)
    (U' : A' → I → ℂ) (V' : B' → J → ℂ) (W' : C' → K → ℂ)
    (h00 : mapTensor U V W' S = 0)
    (h10 : mapTensor U' V W' S = 0)
    (h01 : mapTensor U V' W' S = 0) :
    Degenerates S (directSum (mapTensor U V W S) (mapTensor U' V' W' S)) := by
  let u := Sum.elim U U'
  let v := Sum.elim V V'
  let w := Sum.elim W W'
  let r : A ⊕ A' → ℕ := Sum.elim (fun _ => 0) (fun _ => 1)
  let s : B ⊕ B' → ℕ := Sum.elim (fun _ => 0) (fun _ => 1)
  let t : C ⊕ C' → ℕ := Sum.elim (fun _ => 2) (fun _ => 0)
  refine ⟨2, (fun a i => X ^ r a * Polynomial.C (u a i)),
    (fun b j => X ^ s b * Polynomial.C (v b j)),
    (fun c k => X ^ t c * Polynomial.C (w c k)), ?_⟩
  intro a b c
  rw [map_monomial]
  have hh00 (a b c) := congrFun (congrFun (congrFun h00 a) b) c
  have hh10 (a b c) := congrFun (congrFun (congrFun h10 a) b) c
  have hh01 (a b c) := congrFun (congrFun (congrFun h01 a) b) c
  simp only [mapTensor, Pi.zero_apply] at hh00 hh10 hh01
  cases a <;> cases b <;> cases c <;>
    simp only [r, s, t, u, v, w, Sum.elim_inl, Sum.elim_inr, directSum,
      mapTensor, Nat.reduceAdd, hh00, hh10, hh01]
  all_goals
    simp only [Polynomial.coeff_monomial, Pi.zero_apply]
    constructor
    · norm_num
    · intro d hd
      have h2 : 2 ≠ d := by omega
      have h3 : 3 ≠ d := by omega
      have h4 : 4 ≠ d := by omega
      simp [h2, h3, h4]

end OM.NNN.Raw
