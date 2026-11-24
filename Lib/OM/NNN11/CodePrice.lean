import Lib.OM.NNN11.Layout
import Lib.OM.NNN11.TelescopeOrders

/-! Three separately factored character sums and one exact telescope.
The correction bounds may price an arbitrary residual at this same point. -/
noncomputable section
open scoped BigOperators Classical
namespace OM.NNN11
open CoordinateTensor OM.NNN.Raw OM.NNN2 Network
open ExtractionAB (X)
open Foundations.PairUnitExponents
set_option maxHeartbeats 2000000

variable {A B C : Type} [Fintype A] [Fintype B] [Fintype C]
  [DecidableEq A] [DecidableEq B] [DecidableEq C]
  {x y z : ℕ} {N r : Fin 3 → ℕ}

def bondLog (a b c x y z : ℕ) : Fin 3 → ℕ := ![b * z + c * y, c * x + a * z, a * y + b * x]

def headPrice (a b c x y z : ℕ) (r : Fin 3 → ℕ) (t : Fin 3 → ℝ) : ℝ :=
  ∏ i, ((2 : ℝ) ^ (bondLog a b c x y z i) / (7 : ℝ) ^ r i) ^ t i

theorem network_code_price (φ : PolMul.Spectral ℂ) (T : Tensor ℂ (X x) (X y) (X z))
    (Lab : BondLayout A B x y (N 2)) (Lbc : BondLayout B C y z (N 0))
    (Lca : BondLayout C A z x (N 1))
    (code : (i : Fin 3) → Word (r i) →ₗ[ZMod 7] Word (N i))
    (p : (i : Fin 3) → Word (N i) → ℝ)
    (hab : ∀ c, value φ (contract (C := C) T (Lab.kernel c) (Network.identity _) (Network.identity _)) ≤ p 2 c)
    (hbc : ∀ c P R, value φ (contract (A := A) (B := B) (C := C) T P (Lbc.kernel c) R) ≤ p 0 c)
    (hca : ∀ c P Q, value φ (contract (A := A) (B := B) (C := C) T P Q (Lca.kernel c)) ≤ p 1 c) :
    value φ T ^ (Fintype.card A + Fintype.card B + Fintype.card C) ≤
      headPrice (Fintype.card A) (Fintype.card B) (Fintype.card C) x y z r (theta φ) +
        (∑ c ∈ Finset.univ.erase (0 : Word (r 0)), p 0 (code 0 c)) +
        (∑ c ∈ Finset.univ.erase (0 : Word (r 1)), p 1 (code 1 c)) +
        ∑ c ∈ Finset.univ.erase (0 : Word (r 2)), p 2 (code 2 c) := by
  obtain ⟨χab, dab, Uab, Vab, hdab, habUV⟩ := Lab.factorization (code 2)
  obtain ⟨χbc, dbc, Ubc, Vbc, hdbc, hbcUV⟩ := Lbc.factorization (code 0)
  obtain ⟨χca, dca, Uca, Vca, hdca, hcaUV⟩ := Lca.factorization (code 1)
  let words (i : Fin 3) := Finset.univ.erase (0 : Word (r i))
  let termsAB (c : Word (r 2)) := χab c • Lab.kernel (code 2 c)
  let termsBC (c : Word (r 0)) := χbc c • Lbc.kernel (code 0 c)
  let termsCA (c : Word (r 1)) := χca c • Lca.kernel (code 1 c)
  let P := Network.identity _ + ∑ c ∈ words 2, termsAB c
  let Q := Network.identity _ + ∑ c ∈ words 0, termsBC c
  let R := Network.identity _ + ∑ c ∈ words 1, termsCA c
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
  have dimBound {d M k : ℕ} (h : d * 7 ^ k ≤ 2 ^ M) :
      (d : ℝ) ≤ (2 : ℝ) ^ M / (7 : ℝ) ^ k := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < (7 : ℝ) ^ k)).2
    exact_mod_cast h
  have pab := Real.rpow_le_rpow (Nat.cast_nonneg dab) (dimBound hdab) (theta_mem_Icc φ 2).1
  have pbc := Real.rpow_le_rpow (Nat.cast_nonneg dbc) (dimBound hdbc) (theta_mem_Icc φ 0).1
  have pca := Real.rpow_le_rpow (Nat.cast_nonneg dca) (dimBound hdca) (theta_mem_Icc φ 1).1
  have hhead : value φ (contract (A := A) (B := B) (C := C) T P Q R) ≤
      headPrice (Fintype.card A) (Fintype.card B) (Fintype.card C) x y z r (theta φ) := by
    rw [← hP, ← hQ, ← hR]
    have h := head_value φ T Uab Vab Ubc Vbc Uca Vca
    simp only [Fintype.card_fin] at h
    apply h.trans
    have hm := mul_le_mul (mul_le_mul pca pab (by positivity) (by positivity))
      pbc (by positivity) (by positivity)
    simpa only [headPrice, bondLog, Fin.prod_univ_three, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, mul_comm, mul_left_comm, mul_assoc] using! hm
  have ha (c : Word (r 2)) (_ : c ∈ words 2) :
      value φ (contract (C := C) T (termsAB c) (Network.identity _) (Network.identity _)) ≤ p 2 (code 2 c) := by
    have he : contract (C := C) T (termsAB c) (Network.identity _) (Network.identity _) =
        χab c • contract (C := C) T (Lab.kernel (code 2 c)) (Network.identity _) (Network.identity _) :=
      (linearAB (C := C) T (Network.identity _) (Network.identity _)).map_smul _ _
    rw [he]
    exact (NNN10.value_smul_le φ _ _).trans (hab _)
  have hb (c : Word (r 0)) (_ : c ∈ words 0) :
      value φ (contract (A := A) (B := B) (C := C) T P (termsBC c) R) ≤ p 0 (code 0 c) := by
    have he : contract (A := A) (B := B) (C := C) T P (termsBC c) R = χbc c • contract (A := A) (B := B) (C := C) T P (Lbc.kernel (code 0 c)) R :=
      (linearBC T P R).map_smul _ _
    rw [he]
    exact (NNN10.value_smul_le φ _ _).trans (hbc _ _ _)
  have hc (c : Word (r 1)) (_ : c ∈ words 1) :
      value φ (contract (A := A) (B := B) (C := C) T P (Network.identity _) (termsCA c)) ≤ p 1 (code 1 c) := by
    have he : contract (A := A) (B := B) (C := C) T P (Network.identity _) (termsCA c) =
        χca c • contract (A := A) (B := B) (C := C) T P (Network.identity _) (Lca.kernel (code 1 c)) :=
      (linearCA T P (Network.identity _)).map_smul _ _
    rw [he]
    exact (NNN10.value_smul_le φ _ _).trans (hca _ _ _)
  have h := telescoped_value φ T (words 2) (words 0) (words 1)
    termsAB termsBC termsCA _ _ _ ha hb hc
  change value φ (contract (A := A) (B := B) (C := C) T
    (Network.identity _) (Network.identity _) (Network.identity _)) ≤
      value φ (contract (A := A) (B := B) (C := C) T P Q R) + _ + _ + _ at h
  rw [value_contract_identity] at h
  linarith only [h, hhead]

end OM.NNN11
