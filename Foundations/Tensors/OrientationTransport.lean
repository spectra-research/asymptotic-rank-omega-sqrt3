/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Foundations.Tensors.PairUnitExponents

/-! # Permutations of tensor legs and spectral points -/

open scoped Matrix

namespace Foundations.OrientationTransport

open AsymptoticSpectrumDuality AsymptoticSpectrumDuality.AsymptoticSpectrum
open Semicontinuity Foundations.PairUnitExponents

universe u

variable {F : Type u} [Field F]

private noncomputable abbrev tsp (F : Type u) [Field F] :=
  tensorStrassenPreorder (F := F) (k := 3) (by omega)

/-- Reindexing the legs induces a semiring automorphism of tensor classes. -/
noncomputable def legPermEquiv (σ : Equiv.Perm (Fin 3)) :
    TensorClass F 3 ≃+* TensorClass F 3 where
  toFun := Quotient.map
    (fun a : TT F 3 => ⟨fun i => a.1 (σ i), KTensor.legReindex σ a.2⟩)
    (by
      intro a b hab
      exact ⟨KTensor.legReindex_Restricts σ hab.1, KTensor.legReindex_Restricts σ hab.2⟩)
  invFun := Quotient.map
    (fun a : TT F 3 => ⟨fun i => a.1 (σ.symm i), KTensor.legReindex σ.symm a.2⟩)
    (by
      intro a b hab
      exact ⟨KTensor.legReindex_Restricts σ.symm hab.1,
        KTensor.legReindex_Restricts σ.symm hab.2⟩)
  left_inv := by
    intro x
    refine Quotient.inductionOn x ?_
    rintro ⟨d, T⟩
    apply TensorClass.mk_eq_of_equiv
    exact ⟨KTensor.legReindex_legReindex_restricts σ T,
      KTensor.restricts_legReindex_legReindex σ T⟩
  right_inv := by
    intro x
    refine Quotient.inductionOn x ?_
    rintro ⟨d, T⟩
    apply TensorClass.mk_eq_of_equiv
    simpa only [Equiv.symm_symm] using!
      (show KTensor.legReindex σ (KTensor.legReindex σ.symm T) ∼ₜ T from
        ⟨KTensor.legReindex_legReindex_restricts σ.symm T,
          KTensor.restricts_legReindex_legReindex σ.symm T⟩)
  map_add' := by
    rintro ⟨a⟩ ⟨b⟩
    change TensorClass.mk ⟨_, KTensor.legReindex σ (a.2 ⊕ₜ b.2)⟩
      = TensorClass.mk ⟨_, KTensor.legReindex σ a.2 ⊕ₜ KTensor.legReindex σ b.2⟩
    rw [KTensor.legReindex_directSum]
  map_mul' := by
    rintro ⟨a⟩ ⟨b⟩
    change TensorClass.mk ⟨_, KTensor.legReindex σ (a.2 ⊠ b.2)⟩
      = TensorClass.mk ⟨_, KTensor.legReindex σ a.2 ⊠ KTensor.legReindex σ b.2⟩
    rw [KTensor.legReindex_kron]

@[simp] theorem legPermEquiv_mk (σ : Equiv.Perm (Fin 3)) (a : TT F 3) :
    legPermEquiv (F := F) σ (TensorClass.mk a)
      = TensorClass.mk ⟨fun i => a.1 (σ i), KTensor.legReindex σ a.2⟩ := rfl

/-- Leg reindexing preserves and reflects the tensor Strassen preorder. -/
theorem legPermEquiv_rel_iff (σ : Equiv.Perm (Fin 3)) (x y : TensorClass F 3) :
    (tensorStrassenPreorder (F := F) (k := 3) (by omega)).rel
        (legPermEquiv σ x) (legPermEquiv σ y) ↔
      (tensorStrassenPreorder (F := F) (k := 3) (by omega)).rel x y := by
  refine Quotient.inductionOn₂ x y ?_
  intro a b
  change Restricts (KTensor.legReindex σ a.2) (KTensor.legReindex σ b.2) ↔ Restricts a.2 b.2
  exact ⟨KTensor.legReindex_Restricts_iff σ, KTensor.legReindex_Restricts σ⟩

/-- Pull a spectral point back along a leg permutation. -/
noncomputable def pullPoint
    (φ : AsymptoticSpectrum (tensorStrassenPreorder (F := F) (k := 3) (by omega)))
    (σ : Equiv.Perm (Fin 3)) :
    AsymptoticSpectrum (tensorStrassenPreorder (F := F) (k := 3) (by omega)) where
  toFun x := φ.toFun (legPermEquiv σ x)
  map_zero := by rw [(legPermEquiv (F := F) σ).map_zero, φ.map_zero]
  map_one := by rw [(legPermEquiv (F := F) σ).map_one, φ.map_one]
  map_add x y := by rw [(legPermEquiv (F := F) σ).map_add, φ.map_add]
  map_mul x y := by rw [(legPermEquiv (F := F) σ).map_mul, φ.map_mul]
  monotone x y hxy := φ.monotone _ _ ((legPermEquiv_rel_iff σ x y).2 hxy)
  nonneg x := φ.nonneg _

theorem spectralPoint_ext
    {φ ψ : AsymptoticSpectrum (tensorStrassenPreorder (F := F) (k := 3) (by omega))}
    (h : φ.toFun = ψ.toFun) : φ = ψ := by
  cases φ; cases ψ; cases h; rfl

/-! ## 1. The leg action on oriented pair units -/

/-- The pair unit is symmetric in its two pair modes. -/
lemma mk_unitPair_swap (r : ℕ+) (a b : Fin 3) (hab : a ≠ b) :
    TensorClass.mk (F := F) ⟨_, unitPairTensor (F := F) r a b hab⟩
      = TensorClass.mk (F := F) ⟨_, unitPairTensor (F := F) r b a hab.symm⟩ := by
  have hfmt : ∀ l : Fin 3,
      ((naturalPairFormat (k := 3) r a b l : ℕ+) : ℕ)
        = ((naturalPairFormat (k := 3) r b a l : ℕ+) : ℕ) := by
    intro l
    simp only [naturalPairFormat]
    by_cases h : l = a ∨ l = b
    · rw [if_pos h, if_pos (Or.symm h)]
    · rw [if_neg h, if_neg (fun hh => h (Or.symm hh))]
  have hfmt' : ∀ l : Fin 3,
      ((naturalPairFormat (k := 3) r b a l : ℕ+) : ℕ)
        = ((naturalPairFormat (k := 3) r a b l : ℕ+) : ℕ) := fun l => (hfmt l).symm
  refine TensorClass.mk_eq_of_equiv ⟨?_, ?_⟩
  · refine Restricts.of_eq_cast hfmt ?_
    intro jdx
    show (if ((jdx a : Fin _) : ℕ) = ((jdx b : Fin _) : ℕ) then (1 : F) else 0)
      = (if ((Fin.cast (hfmt b) (jdx b) : Fin _) : ℕ)
          = ((Fin.cast (hfmt a) (jdx a) : Fin _) : ℕ) then (1 : F) else 0)
    exact if_congr eq_comm rfl rfl
  · refine Restricts.of_eq_cast hfmt' ?_
    intro jdx
    show (if ((jdx b : Fin _) : ℕ) = ((jdx a : Fin _) : ℕ) then (1 : F) else 0)
      = (if ((Fin.cast (hfmt' a) (jdx a) : Fin _) : ℕ)
          = ((Fin.cast (hfmt' b) (jdx b) : Fin _) : ℕ) then (1 : F) else 0)
    exact if_congr eq_comm rfl rfl

/-- The leg action on a pair unit moves the two pair modes by `σ⁻¹`. -/
lemma mk_unitPair_reindex (r : ℕ+) (a b : Fin 3) (hab : a ≠ b) (σ : Equiv.Perm (Fin 3)) :
    legPermEquiv (F := F) σ
        (TensorClass.mk ⟨_, unitPairTensor (F := F) r a b hab⟩)
      = TensorClass.mk (F := F) ⟨_, unitPairTensor (F := F) r (σ.symm a) (σ.symm b)
          (fun h => hab (by simpa using! congrArg σ h))⟩ := by
  rw [legPermEquiv_mk]
  have hfmt : ∀ l : Fin 3,
      ((naturalPairFormat (k := 3) r a b (σ l) : ℕ+) : ℕ)
        = ((naturalPairFormat (k := 3) r (σ.symm a) (σ.symm b) l : ℕ+) : ℕ) := by
    intro l
    simp only [naturalPairFormat]
    by_cases h : σ l = a ∨ σ l = b
    · rw [if_pos h, if_pos (h.imp (fun hh => (Equiv.eq_symm_apply σ).2 hh)
        (fun hh => (Equiv.eq_symm_apply σ).2 hh))]
    · rw [if_neg h, if_neg (fun hh => h (hh.imp (fun x => (Equiv.eq_symm_apply σ).1 x)
        (fun x => (Equiv.eq_symm_apply σ).1 x)))]
  have hfmt' : ∀ l : Fin 3,
      ((naturalPairFormat (k := 3) r (σ.symm a) (σ.symm b) l : ℕ+) : ℕ)
        = ((naturalPairFormat (k := 3) r a b (σ l) : ℕ+) : ℕ) := fun l => (hfmt l).symm
  refine TensorClass.mk_eq_of_equiv ⟨?_, ?_⟩
  · refine Restricts.of_eq_cast hfmt ?_
    intro jdx
    show (if ((Equiv.piCongrLeft (fun i => Fin ((naturalPairFormat (k := 3) r a b i : ℕ+) : ℕ))
              σ jdx) a : Fin _).val
            = ((Equiv.piCongrLeft
              (fun i => Fin ((naturalPairFormat (k := 3) r a b i : ℕ+) : ℕ)) σ jdx) b : Fin _).val
          then (1 : F) else 0)
      = (if ((Fin.cast (hfmt (σ.symm a)) (jdx (σ.symm a)) : Fin _) : ℕ)
            = ((Fin.cast (hfmt (σ.symm b)) (jdx (σ.symm b)) : Fin _) : ℕ) then (1 : F) else 0)
    refine if_congr ?_ rfl rfl
    rw [piCongrLeft_val, piCongrLeft_val]
    rfl
  · refine Restricts.of_eq_cast hfmt' ?_
    intro jdx
    show (if ((jdx (σ.symm a) : Fin _) : ℕ) = ((jdx (σ.symm b) : Fin _) : ℕ) then (1 : F) else 0)
      = (if ((Equiv.piCongrLeft (fun i => Fin ((naturalPairFormat (k := 3) r a b i : ℕ+) : ℕ))
              σ (fun l => Fin.cast (hfmt' l) (jdx l))) a : Fin _).val
            = ((Equiv.piCongrLeft
              (fun i => Fin ((naturalPairFormat (k := 3) r a b i : ℕ+) : ℕ)) σ
                (fun l => Fin.cast (hfmt' l) (jdx l))) b : Fin _).val then (1 : F) else 0)
    refine if_congr ?_ rfl rfl
    rw [piCongrLeft_val, piCongrLeft_val]
    rfl

/-! ## 2. The leg action on oriented pair units, continued -/

/-- The two modes of `complementaryPair j` are exactly the modes `≠ j`. -/
lemma complementaryPair_ne (j : Fin 3) :
    (complementaryPair j).1 ≠ j ∧ (complementaryPair j).2 ≠ j := by
  fin_cases j <;> decide

lemma mem_complementaryPair {j x : Fin 3} (h : x ≠ j) :
    x = (complementaryPair j).1 ∨ x = (complementaryPair j).2 := by
  revert h; fin_cases j <;> fin_cases x <;> decide

lemma pair_eq_or_swap {u v x y : Fin 3} (hu : x = u ∨ x = v) (hv : y = u ∨ y = v)
    (hxy : x ≠ y) : (x = u ∧ y = v) ∨ (x = v ∧ y = u) := by
  rcases hu with h1 | h1 <;> rcases hv with h2 | h2
  · exact absurd (h1.trans h2.symm) hxy
  · exact Or.inl ⟨h1, h2⟩
  · exact Or.inr ⟨h1, h2⟩
  · exact absurd (h1.trans h2.symm) hxy

lemma mk_unitPair_congr (r : ℕ+) {a b a' b' : Fin 3} (hab : a ≠ b) (hab' : a' ≠ b')
    (h1 : a = a') (h2 : b = b') :
    TensorClass.mk (F := F) ⟨_, unitPairTensor (F := F) r a b hab⟩
      = TensorClass.mk (F := F) ⟨_, unitPairTensor (F := F) r a' b' hab'⟩ := by
  subst h1; subst h2; rfl

/-- **The leg action moves the orientation of a pair unit by `σ⁻¹`.** -/
lemma legReindexEquiv_orientedPairUnit (σ : Equiv.Perm (Fin 3)) (j : Fin 3) {m : ℕ} (hm : 0 < m) :
    legPermEquiv (F := F) σ (orientedPairUnit F j m)
      = orientedPairUnit F (σ.symm j) m := by
  rw [orientedPairUnit, pairUnitTT_complementary_eq j m hm,
    orientedPairUnit, pairUnitTT_complementary_eq (σ.symm j) m hm]
  show legPermEquiv (F := F) σ
      (TensorClass.mk ⟨_, unitPairTensor (F := F) ⟨m, hm⟩ (complementaryPair j).1
        (complementaryPair j).2 (complementaryPair_fst_ne_snd j)⟩)
    = TensorClass.mk ⟨_, unitPairTensor (F := F) ⟨m, hm⟩ (complementaryPair (σ.symm j)).1
        (complementaryPair (σ.symm j)).2 (complementaryPair_fst_ne_snd (σ.symm j))⟩
  rw [mk_unitPair_reindex]
  obtain ⟨ha, hb⟩ := complementaryPair_ne j
  have hxa : σ.symm (complementaryPair j).1 ≠ σ.symm j := fun h => ha (σ.symm.injective h)
  have hxb : σ.symm (complementaryPair j).2 ≠ σ.symm j := fun h => hb (σ.symm.injective h)
  have hne : σ.symm (complementaryPair j).1 ≠ σ.symm (complementaryPair j).2 :=
    fun h => (complementaryPair_fst_ne_snd j) (σ.symm.injective h)
  rcases pair_eq_or_swap (mem_complementaryPair hxa) (mem_complementaryPair hxb) hne with
    ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact mk_unitPair_congr _ _ _ h1 h2
  · refine (mk_unitPair_congr (a' := (complementaryPair (σ.symm j)).2)
      (b' := (complementaryPair (σ.symm j)).1) _ _
      (complementaryPair_fst_ne_snd (σ.symm j)).symm h1 h2).trans ?_
    exact (mk_unitPair_swap _ _ _ (complementaryPair_fst_ne_snd (σ.symm j))).symm

/-! ## 3. Transport of the orientation exponents -/

lemma eval_legReindex (φ : AsymptoticSpectrum (tsp F)) (σ : Equiv.Perm (Fin 3))
    (x : TensorClass F 3) :
    eval (tsp F) x (pullPoint φ σ)
      = eval (tsp F) (legPermEquiv σ x) φ := rfl

/-- **`θ` transports by `σ⁻¹`.** -/
lemma theta_legReindex (φ : AsymptoticSpectrum (tsp F)) (σ : Equiv.Perm (Fin 3)) (j : Fin 3) :
    theta (pullPoint φ σ) j = theta φ (σ.symm j) := by
  unfold theta
  congr 1
  rw [show eval (tsp F) (orientedPairUnit F j 2) (pullPoint φ σ)
      = eval (tsp F) (legPermEquiv σ (orientedPairUnit F j 2)) φ from rfl,
    legReindexEquiv_orientedPairUnit σ j (by norm_num)]

/-- The identity leg permutation acts trivially. -/
lemma legReindexEquiv_one (x : TensorClass F 3) :
    legPermEquiv (F := F) (1 : Equiv.Perm (Fin 3)) x = x := by
  refine Quotient.inductionOn x ?_
  rintro ⟨d, T⟩
  have hpi : ∀ jdx : (∀ i : Fin 3, Fin ((d i : ℕ+) : ℕ)),
      Equiv.piCongrLeft (fun i => Fin ((d i : ℕ+) : ℕ)) (1 : Equiv.Perm (Fin 3)) jdx = jdx := by
    intro jdx
    funext i
    exact Fin.ext (by rw [piCongrLeft_val]; rfl)
  refine TensorClass.mk_eq_of_equiv ⟨?_, ?_⟩
  · refine Restricts.of_eq_cast (fun _ => rfl) (fun jdx => ?_)
    show T (Equiv.piCongrLeft (fun i => Fin ((d i : ℕ+) : ℕ)) (1 : Equiv.Perm (Fin 3)) jdx) = T _
    rw [hpi jdx]
    exact congrArg T (funext fun i => Fin.ext rfl)
  · refine Restricts.of_eq_cast (fun _ => rfl) (fun jdx => ?_)
    show T jdx = T (Equiv.piCongrLeft (fun i => Fin ((d i : ℕ+) : ℕ)) (1 : Equiv.Perm (Fin 3)) _)
    rw [hpi]
    exact congrArg T (funext fun i => Fin.ext rfl)

/-- A leg permutation taking mode `i` to mode `2`; its inverse takes `2` to `i`. -/
def rot : Fin 3 → Equiv.Perm (Fin 3) := ![Equiv.swap 0 2, Equiv.swap 1 2, 1]

lemma rot_symm_two (i : Fin 3) : (rot i).symm 2 = i := by fin_cases i <;> decide

/-! ## 6. Identifying a leg-permuted class with an explicit tensor

All the orientation bookkeeping reduces to one lemma: to identify
`legPermEquiv σ ⟦S⟧` with an explicitly given `⟦S'⟧`, it suffices to give the
pointwise format equality and the value equality *stated on `.val`s only*, so
that no dependent-type juggling escapes into the caller. -/

theorem legPermEquiv_mk_eq {d d' : Fin 3 → ℕ+} (σ : Equiv.Perm (Fin 3))
    (S : KTensor F d) (S' : KTensor F d')
    (hfmt : ∀ i, ((d (σ i) : ℕ+) : ℕ) = ((d' i : ℕ+) : ℕ))
    (hval : ∀ (jdx : ∀ i, Fin ((d' i : ℕ+) : ℕ)) (ρ : ∀ i, Fin ((d i : ℕ+) : ℕ)),
      (∀ i, ((ρ i : Fin _) : ℕ) = ((jdx (σ.symm i) : Fin _) : ℕ)) → S ρ = S' jdx) :
    legPermEquiv σ (TensorClass.mk ⟨d, S⟩) = TensorClass.mk ⟨d', S'⟩ := by
  rw [legPermEquiv_mk]
  refine TensorClass.mk_eq_of_equiv ⟨?_, ?_⟩
  · refine Restricts.of_eq_cast hfmt (fun jdx => ?_)
    show S (Equiv.piCongrLeft (fun i => Fin ((d i : ℕ+) : ℕ)) σ jdx) = _
    refine hval _ _ (fun i => ?_)
    rw [piCongrLeft_val]
    rfl
  · refine Restricts.of_eq_cast (fun i => (hfmt i).symm) (fun jdx => ?_)
    show S' jdx = S (Equiv.piCongrLeft (fun i => Fin ((d i : ℕ+) : ℕ)) σ _)
    refine (hval jdx _ (fun i => ?_)).symm
    rw [piCongrLeft_val]
    rfl

/-- The leg action is a right action: `σ · (τ · x) = (τ * σ) · x`. -/
theorem legPermEquiv_comp (σ τ : Equiv.Perm (Fin 3)) (x : TensorClass F 3) :
    legPermEquiv σ (legPermEquiv τ x) = legPermEquiv (τ * σ) x := by
  refine Quotient.inductionOn x ?_
  rintro ⟨d, S⟩
  refine TensorClass.mk_eq_of_equiv ⟨?_, ?_⟩
  · refine Restricts.of_eq_cast (fun _ => rfl) (fun jdx => ?_)
    show S (Equiv.piCongrLeft (fun i => Fin ((d i : ℕ+) : ℕ)) τ
        (Equiv.piCongrLeft (fun i => Fin ((d (τ i) : ℕ+) : ℕ)) σ jdx)) = _
    show _ = S (Equiv.piCongrLeft (fun i => Fin ((d i : ℕ+) : ℕ)) (τ * σ) _)
    congr 1
    funext i
    refine Fin.ext ?_
    rw [piCongrLeft_val, piCongrLeft_val, piCongrLeft_val]
    rfl
  · refine Restricts.of_eq_cast (fun _ => rfl) (fun jdx => ?_)
    show S (Equiv.piCongrLeft (fun i => Fin ((d i : ℕ+) : ℕ)) (τ * σ) jdx) = _
    show _ = S (Equiv.piCongrLeft (fun i => Fin ((d i : ℕ+) : ℕ)) τ
        (Equiv.piCongrLeft (fun i => Fin ((d (τ i) : ℕ+) : ℕ)) σ _))
    congr 1
    funext i
    refine Fin.ext ?_
    rw [piCongrLeft_val, piCongrLeft_val, piCongrLeft_val]
    rfl

lemma rot_sq (k : Fin 3) : rot k * rot k = 1 := by
  fin_cases k <;> exact Equiv.ext (fun i => by fin_cases i <;> decide)

/-- Undoing a leg permutation. -/
theorem legPermEquiv_rot_rot (k : Fin 3) (x : TensorClass F 3) :
    legPermEquiv (rot k) (legPermEquiv (rot k) x) = x := by
  rw [legPermEquiv_comp, rot_sq, legReindexEquiv_one]

end Foundations.OrientationTransport
