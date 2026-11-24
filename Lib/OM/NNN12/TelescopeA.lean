import Lib.OM.NNN12.CodePrice
import Lib.OM.NNN11.TelescopeOrders

/-! Mixed-alphabet telescope retaining party A, in the original physical
party order. All full residual bounds are uniform in the other operators. -/
noncomputable section
open scoped BigOperators Classical
namespace OM.NNN12
open CoordinateTensor OM.NNN.Raw OM.NNN2 NNN11.Network
open NNN11 (bondLog)
open NNN11.ExtractionAB (X)
open Foundations.PairUnitExponents Codes
set_option maxHeartbeats 2000000

variable {A B C : Type} [Fintype A] [Fintype B] [Fintype C]
  [DecidableEq A] [DecidableEq B] [DecidableEq C]
  {x y z : ℕ} {N r q k : Fin 3 → ℕ} [∀ i, Fact (q i).Prime]

theorem network_code_price_lastBC (φ : PolMul.Spectral ℂ) (T : Tensor ℂ (X x) (X y) (X z))
    (Lab : BondLayout (q 2) (k 2) A B x y (N 2)) (Lbc : BondLayout (q 0) (k 0) B C y z (N 0))
    (Lca : BondLayout (q 1) (k 1) C A z x (N 1))
    (code : (i : Fin 3) → Word (q i) (r i) →ₗ[ZMod (q i)] Word (q i) (N i))
    (p : (i : Fin 3) → Word (q i) (N i) → ℝ)
    (hab : ∀ c Q R, value φ (contract (A := A) (B := B) (C := C) T (Lab.kernel c) Q R) ≤ p 2 c)
    (hbc : ∀ c, value φ (contract (A := A) (B := B) (C := C) T (NNN11.Network.identity _) (Lbc.kernel c) (NNN11.Network.identity _)) ≤ p 0 c)
    (hca : ∀ c P Q, value φ (contract (A := A) (B := B) (C := C) T P Q (Lca.kernel c)) ≤ p 1 c) :
    value φ T ^ (Fintype.card A + Fintype.card B + Fintype.card C) ≤
      headPrice q (Fintype.card A) (Fintype.card B) (Fintype.card C) x y z r (theta φ) +
        (∑ c ∈ Finset.univ.erase (0 : Word (q 0) (r 0)), p 0 (code 0 c)) +
        (∑ c ∈ Finset.univ.erase (0 : Word (q 1) (r 1)), p 1 (code 1 c)) +
        ∑ c ∈ Finset.univ.erase (0 : Word (q 2) (r 2)), p 2 (code 2 c) := by
  obtain ⟨χab, dab, Uab, Vab, hdab, habUV⟩ := Lab.factorization (code 2)
  obtain ⟨χbc, dbc, Ubc, Vbc, hdbc, hbcUV⟩ := Lbc.factorization (code 0)
  obtain ⟨χca, dca, Uca, Vca, hdca, hcaUV⟩ := Lca.factorization (code 1)
  let words (i : Fin 3) := Finset.univ.erase (0 : Word (q i) (r i))
  let termsAB (c : Word (q 2) (r 2)) := χab c • Lab.kernel (code 2 c)
  let termsBC (c : Word (q 0) (r 0)) := χbc c • Lbc.kernel (code 0 c)
  let termsCA (c : Word (q 1) (r 1)) := χca c • Lca.kernel (code 1 c)
  let P := NNN11.Network.identity _ + ∑ c ∈ words 2, termsAB c
  let Q := NNN11.Network.identity _ + ∑ c ∈ words 0, termsBC c
  let R := NNN11.Network.identity _ + ∑ c ∈ words 1, termsCA c
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
      headPrice q (Fintype.card A) (Fintype.card B) (Fintype.card C) x y z r (theta φ) := by
    rw [← hP, ← hQ, ← hR]
    have h := head_value φ T Uab Vab Ubc Vbc Uca Vca
    simp only [Fintype.card_fin] at h
    apply h.trans
    have hm := mul_le_mul (mul_le_mul pca pab (by positivity) (by positivity))
      pbc (by positivity) (by positivity)
    simpa only [headPrice, bondLog, Fin.prod_univ_three, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, mul_comm, mul_left_comm, mul_assoc] using! hm
  have ha (c : Word (q 2) (r 2)) (_ : c ∈ words 2) :
      value φ (contract (C := C) T (termsAB c) Q (NNN11.Network.identity _)) ≤ p 2 (code 2 c) := by
    have he : contract (C := C) T (termsAB c) Q (NNN11.Network.identity _) =
        χab c • contract (C := C) T (Lab.kernel (code 2 c)) Q (NNN11.Network.identity _) :=
      (linearAB (C := C) T Q (NNN11.Network.identity _)).map_smul _ _
    rw [he]
    exact (NNN10.value_smul_le φ _ _).trans (hab _ _ _)
  have hb (c : Word (q 0) (r 0)) (_ : c ∈ words 0) :
      value φ (contract (A := A) (B := B) (C := C) T (NNN11.Network.identity _) (termsBC c) (NNN11.Network.identity _)) ≤ p 0 (code 0 c) := by
    have he : contract (A := A) (B := B) (C := C) T (NNN11.Network.identity _) (termsBC c) (NNN11.Network.identity _) =
        χbc c • contract (A := A) (B := B) (C := C) T (NNN11.Network.identity _) (Lbc.kernel (code 0 c)) (NNN11.Network.identity _) :=
      (linearBC T (NNN11.Network.identity _) (NNN11.Network.identity _)).map_smul _ _
    rw [he]
    exact (NNN10.value_smul_le φ _ _).trans (hbc _)
  have hc (c : Word (q 1) (r 1)) (_ : c ∈ words 1) :
      value φ (contract (A := A) (B := B) (C := C) T P Q (termsCA c)) ≤ p 1 (code 1 c) := by
    have he : contract (A := A) (B := B) (C := C) T P Q (termsCA c) =
        χca c • contract (A := A) (B := B) (C := C) T P Q (Lca.kernel (code 1 c)) :=
      (linearCA T P Q).map_smul _ _
    rw [he]
    exact (NNN10.value_smul_le φ _ _).trans (hca _ _ _)
  have h := telescoped_value_lastBC φ T (words 2) (words 0) (words 1)
    termsAB termsBC termsCA _ _ _ ha hb hc
  change value φ (contract (A := A) (B := B) (C := C) T
    (NNN11.Network.identity _) (NNN11.Network.identity _) (NNN11.Network.identity _)) ≤
      value φ (contract (A := A) (B := B) (C := C) T P Q R) + _ + _ + _ at h
  rw [value_contract_identity] at h
  linarith only [h, hhead]

end OM.NNN12
