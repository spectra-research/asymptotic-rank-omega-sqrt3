import Lib.OM.NNN12.TelescopeA
import Lib.OM.NNN18.PackGroup
import Lib.OM.NNN18.PackCode

/-! # The coefficient network with packed correction classes (PACKSTEP T7b)

`NNN12.network_code_price_lastBC` charges every nonzero code word of every bond separately.
Here the corrections of the two non-retained bonds (AB and CA) are grouped by the weight of
their code word; each group is one tensor, priced as a whole (by `PackBonds.packedAB_class`
and `packedCA_class`).  The retained bond BC keeps the ordinary word-by-word charge.  The
telescope (`telescoped_value_lastBC`) is unchanged: only the index sets of the AB and CA sums
are the weight classes instead of the words. -/

noncomputable section
open scoped BigOperators Classical
namespace OM.NNN18.PackNet
open CoordinateTensor OM.NNN.Raw OM.NNN2 OM.NNN11.Network
open OM.NNN11 (bondLog)
open OM.NNN11.ExtractionAB (X)
open Foundations.PairUnitExponents OM.NNN12.Codes
set_option maxHeartbeats 2000000

/-- The nonzero messages whose code word has weight `w`. -/
def wclass {q N r : ℕ} [Fact q.Prime] (code : Word q r →ₗ[ZMod q] Word q N) (w : ℕ) :
    Finset (Word q r) :=
  (Finset.univ.erase (0 : Word q r)).filter (fun c => weight (code c) = w)

lemma sum_wclass {q N r : ℕ} [Fact q.Prime] {M : Type} [AddCommMonoid M]
    (code : Word q r →ₗ[ZMod q] Word q N) (f : Word q r → M) :
    ∑ w ∈ Finset.range (N + 1), ∑ c ∈ wclass code w, f c =
      ∑ c ∈ Finset.univ.erase (0 : Word q r), f c :=
  Finset.sum_fiberwise_of_maps_to
    (fun c _ => Finset.mem_range.2 (Nat.lt_succ_of_le (weight_le (code c)))) f

lemma card_wclass {q N r : ℕ} [Fact q.Prime] (code : Word q r →ₗ[ZMod q] Word q N) (w : ℕ) :
    (wclass code w).card = OM.NNN18.classCount code w := rfl

variable {A B C : Type} [Fintype A] [Fintype B] [Fintype C]
  [DecidableEq A] [DecidableEq B] [DecidableEq C]
  {x y z : ℕ} {N r q k : Fin 3 → ℕ} [∀ i, Fact (q i).Prime]

/-- **The packed network inequality** (retained party `A`, last bond BC). -/
theorem network_packed_price_lastBC (φ : PolMul.Spectral ℂ) (T : Tensor ℂ (X x) (X y) (X z))
    (Lab : NNN12.BondLayout (q 2) (k 2) A B x y (N 2))
    (Lbc : NNN12.BondLayout (q 0) (k 0) B C y z (N 0))
    (Lca : NNN12.BondLayout (q 1) (k 1) C A z x (N 1))
    (code : (i : Fin 3) → Word (q i) (r i) →ₗ[ZMod (q i)] Word (q i) (N i))
    (p0 : Word (q 0) (N 0) → ℝ) (pAB pCA : ℕ → ℝ)
    (hab : ∀ (α : Word (q 2) (r 2) → ℂ) (w : ℕ) Q R,
      value φ (∑ c ∈ wclass (code 2) w,
        α c • contract (A := A) (B := B) (C := C) T (Lab.kernel (code 2 c)) Q R) ≤ pAB w)
    (hbc : ∀ c, value φ (contract (A := A) (B := B) (C := C) T (identity _) (Lbc.kernel c)
      (identity _)) ≤ p0 c)
    (hca : ∀ (α : Word (q 1) (r 1) → ℂ) (w : ℕ) P Q,
      value φ (∑ c ∈ wclass (code 1) w,
        α c • contract (A := A) (B := B) (C := C) T P Q (Lca.kernel (code 1 c))) ≤ pCA w) :
    value φ T ^ (Fintype.card A + Fintype.card B + Fintype.card C) ≤
      NNN12.headPrice q (Fintype.card A) (Fintype.card B) (Fintype.card C) x y z r
        (Foundations.PairUnitExponents.theta φ) +
        (∑ c ∈ Finset.univ.erase (0 : Word (q 0) (r 0)), p0 (code 0 c)) +
        (∑ w ∈ Finset.range (N 1 + 1), pCA w) +
        ∑ w ∈ Finset.range (N 2 + 1), pAB w := by
  obtain ⟨χab, dab, Uab, Vab, hdab, habUV⟩ := Lab.factorization (code 2)
  obtain ⟨χbc, dbc, Ubc, Vbc, hdbc, hbcUV⟩ := Lbc.factorization (code 0)
  obtain ⟨χca, dca, Uca, Vca, hdca, hcaUV⟩ := Lca.factorization (code 1)
  let words (i : Fin 3) := Finset.univ.erase (0 : Word (q i) (r i))
  let termsAB (c : Word (q 2) (r 2)) := χab c • Lab.kernel (code 2 c)
  let termsBC (c : Word (q 0) (r 0)) := χbc c • Lbc.kernel (code 0 c)
  let termsCA (c : Word (q 1) (r 1)) := χca c • Lca.kernel (code 1 c)
  let groupAB (w : ℕ) := ∑ c ∈ wclass (code 2) w, termsAB c
  let groupCA (w : ℕ) := ∑ c ∈ wclass (code 1) w, termsCA c
  let P := identity _ + ∑ c ∈ words 2, termsAB c
  let Q := identity _ + ∑ c ∈ words 0, termsBC c
  let R := identity _ + ∑ c ∈ words 1, termsCA c
  have hPg : P = identity _ + ∑ w ∈ Finset.range (N 2 + 1), groupAB w := by
    simp only [P, groupAB, words]; rw [sum_wclass]
  have hRg : R = identity _ + ∑ w ∈ Finset.range (N 1 + 1), groupCA w := by
    simp only [R, groupCA, words]; rw [sum_wclass]
  have hP : factor Uab Vab = P := by
    funext u v
    simpa only [factor, P, words, termsAB, Pi.add_apply, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul] using! habUV u v
  have hQ : factor Ubc Vbc = Q := by
    funext u v
    simpa only [factor, Q, words, termsBC, Pi.add_apply, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul] using! hbcUV u v
  have hR : factor Uca Vca = R := by
    funext u v
    simpa only [factor, R, words, termsCA, Pi.add_apply, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul] using! hcaUV u v
  have hqpos (i : Fin 3) : (0 : ℝ) < q i := Nat.cast_pos.mpr (Fact.out : Nat.Prime (q i)).pos
  have dimBound (i : Fin 3) {d M r : ℕ} (h : d * q i ^ r ≤ 2 ^ M) :
      (d : ℝ) ≤ (2 : ℝ) ^ M / (q i : ℝ) ^ r := by
    apply (le_div_iff₀ (pow_pos (hqpos i) r)).2
    exact_mod_cast h
  have pab := Real.rpow_le_rpow (Nat.cast_nonneg dab) (dimBound 2 hdab) (theta_mem_Icc φ 2).1
  have pbc := Real.rpow_le_rpow (Nat.cast_nonneg dbc) (dimBound 0 hdbc) (theta_mem_Icc φ 0).1
  have pca := Real.rpow_le_rpow (Nat.cast_nonneg dca) (dimBound 1 hdca) (theta_mem_Icc φ 1).1
  have hhead : value φ (contract (A := A) (B := B) (C := C) T P Q R) ≤
      NNN12.headPrice q (Fintype.card A) (Fintype.card B) (Fintype.card C) x y z r
        (Foundations.PairUnitExponents.theta φ) := by
    rw [← hP, ← hQ, ← hR]
    have h := head_value φ T Uab Vab Ubc Vbc Uca Vca
    simp only [Fintype.card_fin] at h
    apply h.trans
    have hm := mul_le_mul (mul_le_mul pca pab (by positivity) (by positivity))
      pbc (by positivity) (by positivity)
    simpa only [NNN12.headPrice, bondLog, Fin.prod_univ_three, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, mul_comm, mul_left_comm, mul_assoc] using! hm
  have ha (w : ℕ) (_ : w ∈ Finset.range (N 2 + 1)) :
      value φ (contract (A := A) (B := B) (C := C) T (groupAB w) Q (identity _)) ≤ pAB w := by
    have he : contract (A := A) (B := B) (C := C) T (groupAB w) Q (identity _) =
        ∑ c ∈ wclass (code 2) w,
          χab c • contract (A := A) (B := B) (C := C) T (Lab.kernel (code 2 c)) Q (identity _) := by
      have h1 := map_sum (linearAB (A := A) (B := B) (C := C) T Q (identity _)) termsAB
        (wclass (code 2) w)
      change contract (A := A) (B := B) (C := C) T (∑ c ∈ wclass (code 2) w, termsAB c) Q
        (identity _) = ∑ c ∈ wclass (code 2) w,
          contract (A := A) (B := B) (C := C) T (termsAB c) Q (identity _) at h1
      rw [h1]
      apply Finset.sum_congr rfl
      intro c _
      exact (linearAB (A := A) (B := B) (C := C) T Q (identity _)).map_smul _ _
    rw [he]
    exact hab χab w Q (identity _)
  have hb (c : Word (q 0) (r 0)) (_ : c ∈ words 0) :
      value φ (contract (A := A) (B := B) (C := C) T (identity _) (termsBC c) (identity _)) ≤
        p0 (code 0 c) := by
    have he : contract (A := A) (B := B) (C := C) T (identity _) (termsBC c) (identity _) =
        χbc c • contract (A := A) (B := B) (C := C) T (identity _) (Lbc.kernel (code 0 c))
          (identity _) :=
      (linearBC T (identity _) (identity _)).map_smul _ _
    rw [he]
    exact (NNN10.value_smul_le φ _ _).trans (hbc _)
  have hc (w : ℕ) (_ : w ∈ Finset.range (N 1 + 1)) :
      value φ (contract (A := A) (B := B) (C := C) T
        (identity _ + ∑ w' ∈ Finset.range (N 2 + 1), groupAB w') Q (groupCA w)) ≤ pCA w := by
    have he : contract (A := A) (B := B) (C := C) T
        (identity _ + ∑ w' ∈ Finset.range (N 2 + 1), groupAB w') Q (groupCA w) =
        ∑ c ∈ wclass (code 1) w, χca c • contract (A := A) (B := B) (C := C) T
          (identity _ + ∑ w' ∈ Finset.range (N 2 + 1), groupAB w') Q (Lca.kernel (code 1 c)) := by
      have h1 := map_sum (linearCA (A := A) (B := B) (C := C) T
        (identity _ + ∑ w' ∈ Finset.range (N 2 + 1), groupAB w') Q) termsCA (wclass (code 1) w)
      change contract (A := A) (B := B) (C := C) T
        (identity _ + ∑ w' ∈ Finset.range (N 2 + 1), groupAB w') Q
        (∑ c ∈ wclass (code 1) w, termsCA c) = ∑ c ∈ wclass (code 1) w,
          contract (A := A) (B := B) (C := C) T
            (identity _ + ∑ w' ∈ Finset.range (N 2 + 1), groupAB w') Q (termsCA c) at h1
      rw [h1]
      apply Finset.sum_congr rfl
      intro c _
      exact (linearCA (A := A) (B := B) (C := C) T
        (identity _ + ∑ w' ∈ Finset.range (N 2 + 1), groupAB w') Q).map_smul _ _
    rw [he]
    exact hca χca w _ Q
  have h := telescoped_value_lastBC φ T (Finset.range (N 2 + 1)) (words 0)
    (Finset.range (N 1 + 1)) groupAB termsBC groupCA _ _ _ ha hb hc
  rw [← hPg, ← hRg] at h
  change value φ (contract (A := A) (B := B) (C := C) T
    (identity _) (identity _) (identity _)) ≤
      value φ (contract (A := A) (B := B) (C := C) T P Q R) + _ + _ + _ at h
  rw [value_contract_identity] at h
  linarith only [h, hhead]

end OM.NNN18.PackNet
