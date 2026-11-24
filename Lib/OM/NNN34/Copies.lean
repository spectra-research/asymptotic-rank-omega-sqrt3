import Lib.OM.PolMul.DegenAsymp.Blocks

/-! # Expanding a restriction from direct-sum copies of a tensor -/

namespace OM.NNN34

open Semicontinuity

/-- The ordinary sum behind a restriction from `m` copies. Each summand
has one local matrix per party and uses a single common copy label. -/
theorem images_of_restricts_copies {F : Type*} [Field F] {k : ℕ} [NeZero k]
    {d e : Fin k → ℕ+} {T : KTensor F d} {S : KTensor F e} {m : ℕ+}
    (h : Restricts T (kroneckerTensor (unitTensor F (k := k) m) S)) :
    ∃ B : Fin m → (i : Fin k) → Matrix (Fin (d i)) (Fin (e i)) F, ∀ a,
      T a = ∑ c : Fin m, ∑ z : (i : Fin k) → Fin (e i),
        (∏ i, B c i (a i) (z i)) * S z := by
  classical
  obtain ⟨A, hA⟩ := h
  let B (c : Fin m) (i : Fin k) : Matrix (Fin (d i)) (Fin (e i)) F :=
    fun x y => A i x (kronDecodeEquiv.symm (c, y))
  refine ⟨B, fun a => ?_⟩
  let E := kronIndexEquiv (d₁ := fun _ : Fin k => m) (d₂ := e)
  rw [hA, ← E.symm.sum_comp (fun g =>
    (∏ i, A i (a i) (g i)) * kroneckerTensor (unitTensor F (k := k) m) S g)]
  rw [Fintype.sum_prod_type]
  have entry (c : Fin k → Fin m) (z : (i : Fin k) → Fin (e i)) :
      (∏ i, A i (a i) (E.symm (c, z) i)) * kroneckerTensor (unitTensor F m) S (E.symm (c, z)) =
        ((∏ i, B (c i) i (a i) (z i)) * S z) * unitTensor F m c := by
    obtain ⟨hleft, hright⟩ := Prod.mk.inj (E.apply_symm_apply (c, z))
    change kronLeftIndex (E.symm (c, z)) = c at hleft
    change kronRightIndex (E.symm (c, z)) = z at hright
    have hindex (i : Fin k) : E.symm (c, z) i = kronDecodeEquiv.symm (c i, z i) := rfl
    simp only [kroneckerTensor, hleft, hright, hindex, B]
    ring
  simp_rw [entry, ← Finset.sum_mul]
  exact OM.PolMul.DegenAsymp.unitTensor_diagonal_sum _

end OM.NNN34

