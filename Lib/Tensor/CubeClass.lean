import Lib.E.RectangularSpectrum

/-! The tensor class of a coordinate cube, including the empty cube. -/

namespace CoordinateTensor
noncomputable section
open scoped Classical
open Semicontinuity AsymptoticSpectrumDuality Lib.E.RectangularSpectrum

variable {I J : Type}

/-- Use a common enumeration for the three legs of a cube. -/
def cubeToK {n : ℕ+} (e : Fin n ≃ I) (T : Cube ℂ I) : KTensor ℂ (fun _ : Fin 3 => n) :=
  fun g => T (e (g 0)) (e (g 1)) (e (g 2))

/-- A nonempty cube has its usual rectangular class. An empty cube represents zero. -/
def cubeClass [Fintype I] (T : Cube ℂ I) : TensorClass ℂ 3 :=
  if _ : Nonempty I then cls T else 0

@[simp] theorem cubeClass_empty [Fintype I] [IsEmpty I] (T : Cube ℂ I) :
    cubeClass T = 0 := by simp [cubeClass]

theorem cubeClass_of_nonempty [Fintype I] [Nonempty I] (T : Cube ℂ I) :
    cubeClass T = cls T := by simp [cubeClass, ‹Nonempty I›]

theorem cubeClass_eq [Fintype I] {n : ℕ+} (e : Fin n ≃ I) (T : Cube ℂ I) :
    cubeClass T = TensorClass.mk ⟨_, cubeToK e T⟩ := by
  have : Nonempty I := ⟨e ⟨0, n.pos⟩⟩
  rw [cubeClass_of_nonempty]
  exact cls_eq T _ e e e (fun _ => rfl)

@[simp] theorem cubeClass_zero [Fintype I] : cubeClass (0 : Cube ℂ I) = 0 := by
  cases isEmpty_or_nonempty I with
  | inl h => simp
  | inr h =>
    rw [cubeClass_of_nonempty]
    apply TensorClass.mk_eq_of_equiv
    exact zero_equiv

theorem cubeClass_reindex [Fintype I] [Fintype J] (e : I ≃ J) (T : Cube ℂ J) :
    cubeClass (restrict T e e e) = cubeClass T := by
  cases isEmpty_or_nonempty I with
  | inl h =>
    have : IsEmpty J := ⟨fun j => isEmptyElim (e.symm j)⟩
    simp
  | inr h =>
    have : Nonempty J := ⟨e (Classical.choice h)⟩
    simpa only [cubeClass_of_nonempty] using cls_reindex e e e T

theorem cubeClass_add [Fintype I] [Fintype J] (S : Cube ℂ I) (T : Cube ℂ J) :
    cubeClass (directSum S T) = cubeClass S + cubeClass T := by
  cases isEmpty_or_nonempty I with
  | inl h =>
    let e := Equiv.emptySum I J
    have he : directSum S T = restrict T e e e := by
      funext a b c
      rcases a with a | a; exact isEmptyElim a
      rcases b with b | b; exact isEmptyElim b
      rcases c with c | c; exact isEmptyElim c
      rfl
    rw [he, cubeClass_reindex, cubeClass_empty S, zero_add]
  | inr h =>
    cases isEmpty_or_nonempty J with
    | inl h =>
      let e := Equiv.sumEmpty I J
      have he : directSum S T = restrict S e e e := by
        funext a b c
        rcases a with a | a; swap; exact isEmptyElim a
        rcases b with b | b; swap; exact isEmptyElim b
        rcases c with c | c; swap; exact isEmptyElim c
        rfl
      rw [he, cubeClass_reindex, cubeClass_empty T, add_zero]
    | inr h =>
      simpa only [cubeClass_of_nonempty] using cls_add S T

theorem cubeClass_diagonal (I : Type) [Fintype I] [DecidableEq I] :
    cubeClass (diagonal ℂ I) = (Fintype.card I : TensorClass ℂ 3) := by
  cases isEmpty_or_nonempty I with
  | inl h => simp
  | inr h =>
    let n := size I
    let e : Fin n ≃ I := enumeration I
    have hd : cubeToK e (diagonal ℂ I) = unitTensor ℂ (k := 3) n := by
      funext g
      simp only [cubeToK, diagonal, unitTensor, e.injective.eq_iff]
      congr 1
      apply propext
      constructor
      · rintro ⟨hab, hbc⟩ i j
        fin_cases i <;> fin_cases j <;> simp_all
      · intro h
        exact ⟨h 0 1, h 1 2⟩
    rw [cubeClass_eq e, hd]
    exact OM.PolMul.DegenAsymp.unit_class n

theorem eval_cubeClass_mono (φ : OM.PolMul.Spectral ℂ) [Fintype I] [Fintype J]
    {S : Cube ℂ I} {T : Cube ℂ J} (h : Degenerates S T) :
    AsymptoticSpectrum.eval _ (cubeClass T) φ ≤ AsymptoticSpectrum.eval _ (cubeClass S) φ := by
  cases isEmpty_or_nonempty J with
  | inl hJ =>
    rw [cubeClass_empty, AsymptoticSpectrum.eval_zero]
    exact φ.nonneg _
  | inr hJ =>
    cases isEmpty_or_nonempty I with
    | inl hI =>
      obtain ⟨q, U, V, W, hc⟩ := h
      have hz : T = 0 := by
        funext a b c
        simpa [mapTensor] using! (hc a b c).1.symm
      rw [hz, cubeClass_zero, cubeClass_empty]
    | inr hI =>
      simpa only [cubeClass_of_nonempty] using Lib.E.RectangularSpectrum.eval_mono φ h

end
end CoordinateTensor
