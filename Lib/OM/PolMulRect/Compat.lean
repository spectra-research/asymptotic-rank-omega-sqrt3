import Lib.OM.PolMulRect.Defs
import Rect.RankModel.Defs3

/-! # Comparing the two rank definitions used for rectangular matrix multiplication -/

namespace OM.PolMulRect

open Semicontinuity

universe u

/-- At rank `r` the identity contraction is a sum indexed by `Fin r`, also at `r = 0`. -/
private lemma act_identity_apply {F X Y Z : Type*} [Field F] {r : ℕ}
    (a : X → Fin r → F) (b : Y → Fin r → F) (c : Z → Fin r → F) (x : X) (y : Y) (z : Z) :
    Tensor3.act a b c (Tensor3.identity F r) x y z = ∑ i, a x i * b y i * c z i := by
  simp [Tensor3.act, Tensor3.identity, mul_ite, ite_and]

/-- A minimal decomposition gives one with exactly `r` terms by appending zero vectors. -/
private lemma rank_le_iff_factors {F : Type u} [Field F] {d : Fin 3 → ℕ+}
    (T : KTensor F d) (r : ℕ) :
    tensorRank T ≤ r ↔ ∃ v : Fin r → (i : Fin 3) → Fin (d i) → F, ∀ idx,
      T idx = ∑ q, v q 0 (idx 0) * v q 1 (idx 1) * v q 2 (idx 2) := by
  classical
  constructor
  · intro hr
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hr
    have hmem : tensorRank T ∈ {s : ℕ | ∃ f : Fin s → KTensor F d,
        (∀ q, IsSimpleTensor (f q)) ∧ T = ∑ q, f q} :=
      Nat.sInf_mem (exists_tensorRank_decomp (by norm_num) T)
    obtain ⟨f, hf, hT⟩ := hmem
    choose v hv using hf
    refine ⟨Fin.append v (fun _ : Fin m => fun _ _ => 0), fun idx => ?_⟩
    simpa [Fin.sum_univ_add, hv, simpleTensor, Fin.prod_univ_three] using congrFun hT idx
  · rintro ⟨v, hv⟩
    apply Nat.sInf_le
    refine ⟨fun q => simpleTensor (v q), fun q => ⟨v q, rfl⟩, ?_⟩
    funext idx
    simpa [simpleTensor, Fin.prod_univ_three] using hv idx

private lemma matMul_decode {F : Type u} [Field F] (A B C : ℕ+)
    (idx : ∀ i : Fin 3, Fin (PolMul.fmt (A * B) (B * C) (C * A) i)) :
    PolMul.matMul (F := F) A B C idx = Tensor3.matMul (R := F) A B C
      (kronDecodeEquiv (d₁ := A) (d₂ := B) (idx 0))
      (kronDecodeEquiv (d₁ := B) (d₂ := C) (idx 1))
      (kronDecodeEquiv (d₁ := C) (d₂ := A) (idx 2)) := by
  let x := kronDecodeEquiv (d₁ := A) (d₂ := B) (idx 0)
  let y := kronDecodeEquiv (d₁ := B) (d₂ := C) (idx 1)
  let z := kronDecodeEquiv (d₁ := C) (d₂ := A) (idx 2)
  change (if x.2 = y.1 ∧ y.2 = z.1 ∧ z.2 = x.1 then (1 : F) else 0) =
    (if x.2 = y.1 ∧ y.2 = z.1 ∧ x.1 = z.2 then 1 else 0)
  simp only [show z.2 = x.1 ↔ x.1 = z.2 from eq_comm]

/-- Restriction from the diagonal and decomposition into simple tensors give the
same finite matrix multiplication rank certificates. -/
theorem rankLE_matMul_iff_tensorRank_le (F : Type u) [Field F] (A B C : ℕ+) (r : ℕ) :
    OmegaBound.RankLE (Tensor3.matMul (R := F) A B C) r ↔
      tensorRank (PolMul.matMul (F := F) A B C) ≤ r := by
  let e₀ := kronDecodeEquiv (d₁ := A) (d₂ := B)
  let e₁ := kronDecodeEquiv (d₁ := B) (d₂ := C)
  let e₂ := kronDecodeEquiv (d₁ := C) (d₂ := A)
  rw [rank_le_iff_factors]
  constructor
  · rintro ⟨a, b, c, H⟩
    let v (q : Fin r) : (i : Fin 3) → Fin (PolMul.fmt (A * B) (B * C) (C * A) i) → F
      | 0, x => a (e₀ x) q
      | 1, y => b (e₁ y) q
      | 2, z => c (e₂ z) q
    refine ⟨v, fun idx => ?_⟩
    rw [matMul_decode, H, act_identity_apply]
  · rintro ⟨v, H⟩
    refine ⟨fun x q => v q 0 (e₀.symm x), fun y q => v q 1 (e₁.symm y),
      fun z q => v q 2 (e₂.symm z), ?_⟩
    funext x y z
    let idx : (i : Fin 3) → Fin (PolMul.fmt (A * B) (B * C) (C * A) i)
      | 0 => e₀.symm x
      | 1 => e₁.symm y
      | 2 => e₂.symm z
    have h := H idx
    rw [matMul_decode] at h
    rw [act_identity_apply]
    simpa only [idx, e₀, e₁, e₂, Equiv.apply_symm_apply] using h

/-- Quantifying the finite comparison over input sizes identifies the admissible exponents. -/
theorem rectAdmissible_iff (F : Type u) [Field F] (a b c τ : ℝ) :
    OmegaBound.IsRectMMExponent3 F a b c τ ↔ RectAdmissible F a b c τ := by
  constructor
  · rintro ⟨K, hK⟩
    refine ⟨K, fun n hn => ?_⟩
    obtain ⟨r, hr, hbound⟩ := hK n hn
    have h := (rankLE_matMul_iff_tensorRank_le F
      (ceilSide n hn a) (ceilSide n hn b) (ceilSide n hn c) r).mp hr
    exact (Nat.cast_le.mpr h).trans hbound
  · rintro ⟨K, hK⟩
    refine ⟨K, fun n hn => ⟨_, ?_, hK n hn⟩⟩
    exact (rankLE_matMul_iff_tensorRank_le F
      (ceilSide n hn a) (ceilSide n hn b) (ceilSide n hn c) _).mpr le_rfl

/-- The two rectangular exponents agree over a field at every real shape. -/
theorem omegaRect3_eq_omegaRect (F : Type u) [Field F] (a b c : ℝ) :
    OmegaBound.omegaRect3 F a b c = PolMul.omegaRect F a b c := by
  change sInf {τ | OmegaBound.IsRectMMExponent3 F a b c τ} = sInf {τ | RectAdmissible F a b c τ}
  congr 1
  ext τ
  exact rectAdmissible_iff F a b c τ

end OM.PolMulRect
