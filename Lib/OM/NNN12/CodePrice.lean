import Lib.OM.NNN12.NetworkPrices
import Lib.OM.NNN11.CodePrice

/-! The mixed-alphabet telescope, with three separately factored character
sums and arbitrary uniform residual prices at the same spectral point.
This extends NNN11.network_code_price without modifying its source. -/
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

def headPrice (q : Fin 3 → ℕ) (a b c x y z : ℕ) (r : Fin 3 → ℕ) (t : Fin 3 → ℝ) : ℝ :=
  ∏ i, ((2 : ℝ) ^ (bondLog a b c x y z i) / (q i : ℝ) ^ r i) ^ t i

theorem network_code_price (φ : PolMul.Spectral ℂ) (T : Tensor ℂ (X x) (X y) (X z))
    (Lab : BondLayout (q 2) (k 2) A B x y (N 2)) (Lbc : BondLayout (q 0) (k 0) B C y z (N 0))
    (Lca : BondLayout (q 1) (k 1) C A z x (N 1))
    (code : (i : Fin 3) → Word (q i) (r i) →ₗ[ZMod (q i)] Word (q i) (N i))
    (p : (i : Fin 3) → Word (q i) (N i) → ℝ)
    (hab : ∀ c, value φ (contract (C := C) T (Lab.kernel c) (NNN11.Network.identity _) (NNN11.Network.identity _)) ≤ p 2 c)
    (hbc : ∀ c P R, value φ (contract (A := A) (B := B) (C := C) T P (Lbc.kernel c) R) ≤ p 0 c)
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
      value φ (contract (C := C) T (termsAB c) (NNN11.Network.identity _) (NNN11.Network.identity _)) ≤ p 2 (code 2 c) := by
    have he : contract (C := C) T (termsAB c) (NNN11.Network.identity _) (NNN11.Network.identity _) =
        χab c • contract (C := C) T (Lab.kernel (code 2 c)) (NNN11.Network.identity _) (NNN11.Network.identity _) :=
      (linearAB (C := C) T (NNN11.Network.identity _) (NNN11.Network.identity _)).map_smul _ _
    rw [he]
    exact (NNN10.value_smul_le φ _ _).trans (hab _)
  have hb (c : Word (q 0) (r 0)) (_ : c ∈ words 0) :
      value φ (contract (A := A) (B := B) (C := C) T P (termsBC c) R) ≤ p 0 (code 0 c) := by
    have he : contract (A := A) (B := B) (C := C) T P (termsBC c) R = χbc c • contract (A := A) (B := B) (C := C) T P (Lbc.kernel (code 0 c)) R :=
      (linearBC T P R).map_smul _ _
    rw [he]
    exact (NNN10.value_smul_le φ _ _).trans (hbc _ _ _)
  have hc (c : Word (q 1) (r 1)) (_ : c ∈ words 1) :
      value φ (contract (A := A) (B := B) (C := C) T P (NNN11.Network.identity _) (termsCA c)) ≤ p 1 (code 1 c) := by
    have he : contract (A := A) (B := B) (C := C) T P (NNN11.Network.identity _) (termsCA c) =
        χca c • contract (A := A) (B := B) (C := C) T P (NNN11.Network.identity _) (Lca.kernel (code 1 c)) :=
      (linearCA T P (NNN11.Network.identity _)).map_smul _ _
    rw [he]
    exact (NNN10.value_smul_le φ _ _).trans (hca _ _ _)
  have h := telescoped_value φ T (words 2) (words 0) (words 1)
    termsAB termsBC termsCA _ _ _ ha hb hc
  change value φ (contract (A := A) (B := B) (C := C) T
    (NNN11.Network.identity _) (NNN11.Network.identity _) (NNN11.Network.identity _)) ≤
      value φ (contract (A := A) (B := B) (C := C) T P Q R) + _ + _ + _ at h
  rw [value_contract_identity] at h
  linarith only [h, hhead]

lemma headPrice_eq (a b c x y z : ℕ) (r : Fin 3 → ℕ) (t : Fin 3 → ℝ) :
    headPrice q a b c x y z r t =
      (2 : ℝ) ^ (∑ i, t i * ((bondLog a b c x y z i : ℝ) - r i * Real.logb 2 (q i))) := by
  rw [headPrice, Real.rpow_sum_of_pos (by norm_num)]
  apply Finset.prod_congr rfl
  intro i _
  have hq : (0 : ℝ) < q i := Nat.cast_pos.mpr (Fact.out : Nat.Prime (q i)).pos
  have hqpow : (q i : ℝ) ^ r i = (2 : ℝ) ^ ((r i : ℝ) * Real.logb 2 (q i)) := by
    rw [mul_comm, Real.rpow_mul (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) hq,
      Real.rpow_natCast]
  rw [hqpow, ← Real.rpow_natCast, ← Real.rpow_sub (by norm_num),
    ← Real.rpow_mul (by norm_num)]
  congr 1
  ring

theorem headPrice_enlarge
    (Lab : BondLayout (q 2) (k 2) A B x y (N 2)) (Lbc : BondLayout (q 0) (k 0) B C y z (N 0))
    (Lca : BondLayout (q 1) (k 1) C A z x (N 1)) (hr : ∀ i, r i ≤ N i)
    (φ : PolMul.Spectral ℂ) (t : Fin 3 → ℝ) (ht : ∀ i, theta φ i ≤ t i) :
    headPrice q (Fintype.card A) (Fintype.card B) (Fintype.card C) x y z r (theta φ) ≤
      (2 : ℝ) ^ (∑ i, t i * ((bondLog (Fintype.card A) (Fintype.card B) (Fintype.card C) x y z i : ℝ) -
        r i * Real.logb 2 (q i))) := by
  rw [← headPrice_eq]
  apply Finset.prod_le_prod₀
  · intro i _
    positivity
  · intro i _
    apply Real.rpow_le_rpow_of_exponent_le _ (ht i)
    fin_cases i
    · exact Lbc.head_base_ge_one (hr 0)
    · exact Lca.head_base_ge_one (hr 1)
    · exact Lab.head_base_ge_one (hr 2)

end OM.NNN12
