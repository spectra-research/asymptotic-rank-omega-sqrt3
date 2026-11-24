import Lib.OM.NNN8.Projectors

/-! A finite-dimensional range basis provides a literal matrix factorisation. -/
noncomputable section
open scoped BigOperators Classical
namespace OM.NNN8
open Module LinearMap

/-- Every linear map on a finite coordinate space factors through its range
dimension, including dimension zero. -/
theorem exists_range_factorization {I : Type} [Fintype I]
    (f : (I → ℂ) →ₗ[ℂ] (I → ℂ)) :
    ∃ U V : Fin (finrank ℂ (LinearMap.range f)) → I → ℂ,
      ∀ i j, (∑ p, U p i * V p j) = f (Pi.single j 1) i := by
  let b := Module.finBasis ℂ (LinearMap.range f)
  refine ⟨(fun p i => (b p : I → ℂ) i),
    (fun p j => b.repr (f.rangeRestrict (Pi.single j 1)) p), ?_⟩
  intro i j
  have h := congrArg (fun x : LinearMap.range f => (x : I → ℂ) i)
    (b.sum_repr (f.rangeRestrict (Pi.single j 1)))
  simpa only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, mul_comm] using! h

/-- A cheapest projector supplies an explicit factorisation of the unnormalised
character sum with at most dim(V)/|G| columns. -/
theorem exists_character_factorization {G I : Type} [AddCommGroup G] [Fintype G]
    [Fintype I] (P : G → Module.End ℂ (I → ℂ)) (hzero : P 0 = 1)
    (hadd : ∀ a b, P (a + b) = P a * P b) :
    ∃ (χ : AddChar G ℂ) (r : ℕ) (U V : Fin r → I → ℂ),
      r * Fintype.card G ≤ Fintype.card I ∧
      ∀ i j, (∑ p, U p i * V p j) =
        ∑ g, χ g * P g (Pi.single j 1) i := by
  obtain ⟨χ, hχ⟩ := exists_characterProjector_rank_le P hzero hadd
  obtain ⟨U, V, hUV⟩ := exists_range_factorization (characterProjector P χ)
  refine ⟨χ, _, U, (fun p j => (Fintype.card G : ℂ) * V p j), ?_, ?_⟩
  · simpa using! hχ
  · intro i j
    have hn : (Fintype.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    calc
      _ = (Fintype.card G : ℂ) * ∑ p, U p i * V p j := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p _
        ring
      _ = (Fintype.card G : ℂ) * characterProjector P χ (Pi.single j 1) i := by
        rw [hUV]
      _ = _ := by
        simp [characterProjector, characterSum, LinearMap.sum_apply, hn]

end OM.NNN8
