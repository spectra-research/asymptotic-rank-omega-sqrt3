/- Adapted from PolMul/Profiles.lean of an earlier formalisation
   (commit 51c6e6b6e8b8d7226c6a828dba618ae1de5b5f8a).
   Amanov, van den Berg and Zuiddam (2026),
   “Multiplying matrices via polynomials: exposition and barriers”.
   Uses Foundations tensor definitions; declarations are renamed under OM. -/
import Lib.OM.PolMul.ConcavityDegeneration
import Lib.OM.PolMul.DegenerationFacts
import Lib.OM.PolMul.PolmulBasics
import Lib.OM.PolMul.SpectralFacts
import Lib.OM.PolMul.Superadditivity
import Lib.OM.PolMul.TriplingDegeneration
import Lib.OM.PolMulStatements.PR_1
import Lib.OM.PolMulStatements.PR_2
import Lib.OM.PolMulStatements.PR_3

/-!
# Polynomial-multiplication profiles

The proof of `PR.1` follows the paper: coordinate
inclusions give monotonicity, while `PM.1`, `PM.2`, `SP.2`, and `SP.3` give
the two bounds. The proof of `PR.2` uses binary superadditivity, and the proof
of `PR.3` uses the general superadditivity theorem `SA.2`.
-/

namespace OM.PolMul.Profiles

open AsymptoticSpectrumDuality
open Semicontinuity
open scoped BigOperators

universe u

variable {F : Type u} [Field F]

private lemma pnat_add_sub_one_coe (a b : ℕ+) :
    ((a + b - 1 : ℕ+) : ℕ) = (a : ℕ) + (b : ℕ) - 1 := by
  rw [PNat.sub_coe, PNat.add_coe]
  rw [if_pos]
  · rfl
  · apply (PNat.coe_lt_coe _ _).mp
    rw [PNat.add_coe]
    norm_num
    have ha := a.pos
    have hb := b.pos
    omega

/-- Coordinate inclusion realizes the elementary restriction
`P_{a,b} ≤ₜ P_{a',b'}` used in part (i) of the lemma on profiles. -/
private lemma polmul_restricts_of_le (a b a' b' : ℕ+)
    (ha : a ≤ a') (hb : b ≤ b') :
    Restricts (polmul (F := F) a b) (polmul a' b') := by
  classical
  have ha' : (a : ℕ) ≤ (a' : ℕ) := by exact_mod_cast ha
  have hb' : (b : ℕ) ≤ (b' : ℕ) := by exact_mod_cast hb
  have hr' : ((a + b - 1 : ℕ+) : ℕ) ≤ ((a' + b' - 1 : ℕ+) : ℕ) := by
    rw [pnat_add_sub_one_coe, pnat_add_sub_one_coe]
    omega
  let f : ∀ i : Fin 3, Fin (fmt a b (a + b - 1) i) →
      Fin (fmt a' b' (a' + b' - 1) i) := fun i =>
    match i with
    | 0 => Fin.castLE ha'
    | 1 => Fin.castLE hb'
    | 2 => Fin.castLE hr'
  refine ⟨fun i x y => if f i x = y then 1 else 0, ?_⟩
  intro idx
  rw [Finset.sum_eq_single (fun i => f i (idx i))]
  · have hprod :
        (∏ i : Fin 3, if f i (idx i) = f i (idx i) then (1 : F) else 0) = 1 := by
      apply Finset.prod_eq_one
      intro i _
      simp
    rw [hprod, one_mul]
    simp only [polmul]
    congr 1
  · intro jdx _ hjdx
    have hex : ∃ i : Fin 3, f i (idx i) ≠ jdx i := by
      by_contra hall
      push_neg at hall
      exact hjdx (funext fun i => (hall i).symm)
    obtain ⟨i, hi⟩ := hex
    rw [show (∏ k : Fin 3, if f k (idx k) = jdx k then (1 : F) else 0) = 0 by
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp [hi], zero_mul]
  · simp

/-- Forgetting that the first leg map is fixed turns a `Degen23` witness into
an ordinary degeneration witness. -/
private lemma degen_of_degen23 {dT dS : Fin 3 → ℕ+}
    {T : T3 F dT} {S : T3 F dS} {h : dT 0 = dS 0}
    (hdeg : Degen23 T S h) : Degen T S := by
  rcases hdeg with ⟨q, e, A, R, _, hA⟩
  exact ⟨q, e, A, R, hA⟩

/-- `swap23` and its explicit-`fmt` wrapper represent the same permuted
tensor up to the canonical coordinate casts. -/
private lemma swap23_restrictsEquiv_swap23' {n v w : ℕ+}
    (T : T3 F (fmt n v w)) : swap23 T ∼ₜ swap23' T := by
  let hfmt : ∀ i : Fin 3,
      (((fmt n v w) ∘ (Equiv.swap (1 : Fin 3) 2).symm) i : ℕ) =
        (fmt n w v i : ℕ) := by
    intro i
    fin_cases i <;> rfl
  let e : ∀ i : Fin 3,
      Fin (((fmt n v w) ∘ (Equiv.swap (1 : Fin 3) 2).symm) i) ≃
        Fin (fmt n w v i) := fun i => finCongr (hfmt i)
  apply OM.PolMul.SpectralFacts.restrictsEquiv_of_index_equiv e
  intro idx
  simp only [swap23, perm, KTensor.legReindex_apply, swap23']
  apply congrArg T
  funext i
  fin_cases i <;> rfl

/-- The lemma on profiles (i). -/
theorem proof_PR_1 : OM_S_PR_1 := by
  intro F _ φ a b
  let n : ℕ+ := min a b
  have hna : n ≤ a := min_le_left _ _
  have hnb : n ≤ b := min_le_right _ _
  have hunit := (OM.PolMul.SpectralFacts.proof_SP_3 F φ).2 n
  have hlower₁ := OM.PolMul.SpectralFacts.proof_SP_2 F φ _ _
    (OM.PolMul.PolmulBasics.proof_PM_2 F n)
  have hlower₂ := OM.PolMul.Superadditivity.eval_restricts φ
    (polmul_restricts_of_le (F := F) n n a b hna hnb)
  have hlower : (((n : ℕ) : ℝ)) ≤ Spectral.eval φ (polmul (F := F) a b) := by
    change Spectral.eval φ (unit (F := F) n) = (((n : ℕ) : ℝ)) at hunit
    rw [← hunit]
    exact hlower₁.trans hlower₂
  have hupper := OM.PolMul.SpectralFacts.proof_SP_2 F φ _ _
    (OM.PolMul.PolmulBasics.proof_PM_1 F a b)
  have hunit' := (OM.PolMul.SpectralFacts.proof_SP_3 F φ).2 (a + b - 1)
  have hupper' : Spectral.eval φ (polmul (F := F) a b) ≤
      ((((a + b - 1 : ℕ+) : ℕ)) : ℝ) := by
    change Spectral.eval φ (unit (F := F) (a + b - 1)) = _ at hunit'
    change Spectral.eval φ (polmul (F := F) a b) ≤
      Spectral.eval φ (unit (F := F) (a + b - 1)) at hupper
    rwa [hunit'] at hupper
  refine ⟨?_, hupper', ?_, ?_⟩
  · simpa [n] using! hlower
  · intro a' ha'
    exact OM.PolMul.Superadditivity.eval_restricts φ
      (polmul_restricts_of_le (F := F) a b a' b ha' le_rfl)
  · intro b' hb'
    exact OM.PolMul.Superadditivity.eval_restricts φ
      (polmul_restricts_of_le (F := F) a b a b' le_rfl hb')

/-- For two identical summands, the binary and family shared-leg sums differ
only by their canonical block coordinates. -/
private lemma pdsum_same_restrictsEquiv_family_two {d₀ : Fin 3 → ℕ+}
    (X : T3 F d₀) :
    pdsum X X rfl ∼ₜ
      pdsumFamily (m := 2) (fun _ => d₀) (d₀ 0) (fun _ => rfl) (fun _ => X) := by
  classical
  let hfmt : ∀ i : Fin 3,
      ((fmt (d₀ 0) (d₀ 1 + d₀ 1) (d₀ 2 + d₀ 2) i : ℕ)) =
        (fmt (d₀ 0)
          ⟨∑ _ : Fin 2, (d₀ 1 : ℕ), by positivity⟩
          ⟨∑ _ : Fin 2, (d₀ 2 : ℕ), by positivity⟩ i : ℕ) := by
    intro i
    fin_cases i <;> simp [fmt, PNat.add_coe] <;> omega
  let e : ∀ i : Fin 3,
      Fin (fmt (d₀ 0) (d₀ 1 + d₀ 1) (d₀ 2 + d₀ 2) i) ≃
        Fin (fmt (d₀ 0)
          ⟨∑ _ : Fin 2, (d₀ 1 : ℕ), by positivity⟩
          ⟨∑ _ : Fin 2, (d₀ 2 : ℕ), by positivity⟩ i) :=
    fun i => finCongr (hfmt i)
  apply OM.PolMul.SpectralFacts.restrictsEquiv_of_index_equiv e
  intro idx
  let iv : (_ : Fin 2) × Fin (d₀ 1) := finSigmaFinEquiv.symm (e 1 (idx 1))
  let iw : (_ : Fin 2) × Fin (d₀ 2) := finSigmaFinEquiv.symm (e 2 (idx 2))
  have hiv := congrArg Fin.val (finSigmaFinEquiv.apply_symm_apply (e 1 (idx 1)))
  have hiw := congrArg Fin.val (finSigmaFinEquiv.apply_symm_apply (e 2 (idx 2)))
  change (finSigmaFinEquiv iv).val = (e 1 (idx 1)).val at hiv
  change (finSigmaFinEquiv iw).val = (e 2 (idx 2)).val at hiw
  have heval (i : Fin 3) : (e i (idx i)).val = (idx i).val := by
    change (finCongr (hfmt i) (idx i)).val = (idx i).val
    rfl
  rw [heval 1] at hiv
  rw [heval 2] at hiw
  have hivfst : (finSigmaFinEquiv.symm (e 1 (idx 1))).fst = iv.1 := rfl
  have hiwfst : (finSigmaFinEquiv.symm (e 2 (idx 2))).fst = iw.1 := rfl
  have hivsnd : (finSigmaFinEquiv.symm (e 1 (idx 1))).snd.val = iv.2.val := rfl
  have hiwsnd : (finSigmaFinEquiv.symm (e 2 (idx 2))).snd.val = iw.2.val := rfl
  rcases iv with ⟨iv, xv⟩
  rcases iw with ⟨iw, xw⟩
  change (finSigmaFinEquiv.symm (e 1 (idx 1))).fst = iv at hivfst
  change (finSigmaFinEquiv.symm (e 2 (idx 2))).fst = iw at hiwfst
  change (finSigmaFinEquiv.symm (e 1 (idx 1))).snd.val = xv.val at hivsnd
  change (finSigmaFinEquiv.symm (e 2 (idx 2))).snd.val = xw.val at hiwsnd
  fin_cases iv <;> fin_cases iw
  <;> simp [pdsum, pdsumFamily, Fin.sum_univ_two,
    finSigmaFinEquiv_apply, Fin.ext_iff, heval, hivfst, hiwfst,
    hivsnd, hiwsnd] at hiv hiw ⊢
  <;> try omega
  all_goals split_ifs <;> try omega
  all_goals try rfl
  all_goals
    refine congrArg X ?_
    funext i
    fin_cases i
    · apply Fin.ext
      exact (heval 0).symm
    · apply Fin.ext
      simp only [Fin.isValue]
      rw [hivsnd]
      omega
    · apply Fin.ext
      simp only [Fin.isValue]
      rw [hiwsnd]
      omega

def BinarySA2 : Prop :=
  ∀ (F : Type u) [Field F] (φ : Spectral F),
    0 < Real.logb 2 (Spectral.eval φ (matMul 1 1 2)) →
    ∀ (a m : ℕ+), 2 ≤ m →
      Spectral.eval φ (polmul a (m + 1)) ^
          ((1 : ℝ) / Real.logb 2 (Spectral.eval φ (matMul 1 1 2))) +
        Spectral.eval φ (polmul a (m - 1)) ^
          ((1 : ℝ) / Real.logb 2 (Spectral.eval φ (matMul 1 1 2))) ≤
        Spectral.eval φ
            (pdsum (polmul a (m + 1)) (polmul a (m - 1)) rfl) ^
          ((1 : ℝ) / Real.logb 2 (Spectral.eval φ (matMul 1 1 2)))

/-- `PM.3` evaluates the binary partial sum of two identical tensors. -/
private lemma eval_pdsum_same (F : Type u) [Field F] (φ : Spectral F)
    {d₀ : Fin 3 → ℕ+} (X : T3 F d₀) :
    Spectral.eval φ (pdsum X X rfl) =
      Spectral.eval φ X * Spectral.eval φ (matMul 1 1 2) := by
  calc
    Spectral.eval φ (pdsum X X rfl) =
        Spectral.eval φ
          (pdsumFamily (m := 2) (fun _ => d₀) (d₀ 0)
            (fun _ => rfl) (fun _ => X)) :=
      OM.PolMul.Superadditivity.eval_restrictsEquiv φ
        (pdsum_same_restrictsEquiv_family_two X)
    _ = Spectral.eval φ (kron X (matMul 1 1 2)) :=
      OM.PolMul.Superadditivity.eval_iso φ
        (OM.PolMul.PolmulBasics.proof_PM_3 F X 2)
    _ = _ := OM.PolMul.Superadditivity.eval_kron φ X (matMul 1 1 2)

/-- Part (ii) of the profile lemma follows from the binary instance of `SA.2`. -/
theorem proof_PR_2_of_binary_SA_2
    (hSA : BinarySA2.{u}) : OM_S_PR_2.{u} := by
  intro F _ φ hp a m hm
  let p : ℝ := Real.logb 2 (Spectral.eval φ (matMul (F := F) 1 1 2))
  let A := pdsum (polmul (F := F) a (m + 1)) (polmul a (m - 1)) rfl
  let E := pdsum (polmul (F := F) a m) (polmul a m) rfl
  have hsum := hSA F φ hp a m hm
  have hdeg23 : Degen23 A E rfl := by
    simpa [A, E] using!
      (OM.PolMul.ConcavityDegeneration.proof_CG_1 F a m hm)
  have hmono : Spectral.eval φ A ≤ Spectral.eval φ E :=
    OM.PolMul.SpectralFacts.proof_SP_2 F φ A E (degen_of_degen23 hdeg23)
  have hrmono : Spectral.eval φ A ^ ((1 : ℝ) / p) ≤
      Spectral.eval φ E ^ ((1 : ℝ) / p) := by
    exact Real.rpow_le_rpow (OM.PolMul.Superadditivity.eval_nonneg φ A) hmono
      (le_of_lt (one_div_pos.mpr hp))
  have hcpos : 0 < Spectral.eval φ (matMul (F := F) 1 1 2) :=
    zero_lt_one.trans_le (OM.PolMul.SpectralFacts.proof_SP_5 F φ).1.1
  have hc : (2 : ℝ) ^ p = Spectral.eval φ (matMul (F := F) 1 1 2) := by
    exact Real.rpow_logb (by norm_num) (by norm_num) hcpos
  have hnormalize : Spectral.eval φ E ^ ((1 : ℝ) / p) =
      2 * Spectral.eval φ (polmul a m) ^ ((1 : ℝ) / p) := by
    rw [show Spectral.eval φ E =
        Spectral.eval φ (polmul a m) *
          Spectral.eval φ (matMul (F := F) 1 1 2) by
      simpa [E] using! eval_pdsum_same F φ (polmul a m)]
    rw [← hc]
    simp only [one_div]
    rw [Real.mul_rpow (OM.PolMul.Superadditivity.eval_nonneg φ (polmul a m))
      (Real.rpow_nonneg (by norm_num) p)]
    have hp0 : p ≠ 0 := by
      exact (ne_of_gt (by simpa [p] using! hp))
    rw [Real.rpow_rpow_inv (by norm_num) hp0]
    ring
  change
    Spectral.eval φ (polmul a (m + 1)) ^ ((1 : ℝ) / p) +
      Spectral.eval φ (polmul a (m - 1)) ^ ((1 : ℝ) / p) ≤
      2 * Spectral.eval φ (polmul a m) ^ ((1 : ℝ) / p)
  calc
    _ ≤ Spectral.eval φ A ^ ((1 : ℝ) / p) := by
      simpa [p, A] using! hsum
    _ ≤ Spectral.eval φ E ^ ((1 : ℝ) / p) := hrmono
    _ = _ := hnormalize

/-- Part (iii) of the profile lemma follows from the general superadditivity theorem `SA.2`. -/
theorem proof_PR_3_of_SA_2 (hSA : OM_S_SA_2.{u}) : OM_S_PR_3.{u} := by
  intro F _ φ hp a b
  let p : ℝ := Real.logb 2 (Spectral.eval φ (matMul (F := F) 1 1 2))
  let d : Fin 3 → Fin 3 → ℕ+ := fun
    | 0 => fmt a b (a + b - 1)
    | 1 => fmt a (a + b - 1) b
    | 2 => fmt a b (a + b - 1)
  let hd : ∀ i, d i 0 = a := fun
    | 0 => rfl
    | 1 => rfl
    | 2 => rfl
  let T : ∀ i, T3 F (d i) := fun
    | 0 => polmul a b
    | 1 => swap23' (polmul a b)
    | 2 => polmul a b
  let P := pdsumFamily d a hd T
  have hsum := hSA F φ hp 3 d a hd T
  have hdeg23 : Degen23 P (polmul a (3 * b + a - 1)) rfl := by
    simpa [P, d, hd, T] using!
      (OM.PolMul.TriplingDegeneration.proof_TP_1 F a b)
  have hmono : Spectral.eval φ P ≤
      Spectral.eval φ (polmul a (3 * b + a - 1)) :=
    OM.PolMul.SpectralFacts.proof_SP_2 F φ P _ (degen_of_degen23 hdeg23)
  have hrmono : Spectral.eval φ P ^ ((1 : ℝ) / p) ≤
      Spectral.eval φ (polmul a (3 * b + a - 1)) ^ ((1 : ℝ) / p) := by
    exact Real.rpow_le_rpow (OM.PolMul.Superadditivity.eval_nonneg φ P) hmono
      (le_of_lt (one_div_pos.mpr hp))
  have hswap : Spectral.eval φ (swap23' (polmul (F := F) a b)) =
      Spectral.eval φ (swap23 (polmul a b)) := by
    exact (OM.PolMul.Superadditivity.eval_restrictsEquiv φ
      (swap23_restrictsEquiv_swap23' (F := F) (polmul a b))).symm
  change
    2 * Spectral.eval φ (polmul a b) ^ ((1 : ℝ) / p) +
      Spectral.eval φ (swap23 (polmul a b)) ^ ((1 : ℝ) / p) ≤
      Spectral.eval φ (polmul a (3 * b + a - 1)) ^ ((1 : ℝ) / p)
  calc
    _ = ∑ i : Fin 3, Spectral.eval φ (T i) ^ ((1 : ℝ) / p) := by
      rw [Fin.sum_univ_three]
      simp [T, hswap]
      ring
    _ ≤ Spectral.eval φ P ^ ((1 : ℝ) / p) := by
      simpa [p, P] using! hsum
    _ ≤ _ := hrmono

end OM.PolMul.Profiles

namespace OM.PolMul.Profiles

-- The binary superadditivity theorem supplies the sole conditional hypothesis.
set_option maxHeartbeats 200000 in
/-- Unconditional discrete concavity, from SA.2 and the concavity degeneration. -/
theorem proof_PR_2 : OM_S_PR_2 := by
  apply proof_PR_2_of_binary_SA_2
  intro F _ φ hp a m _hm
  simpa only [one_div] using!
    OM.PolMul.Superadditivity.superadd_binary φ hp
      (polmul a (m + 1)) (polmul a (m - 1)) rfl

-- Instantiating the previously checked tripling argument needs no new estimates.
set_option maxHeartbeats 200000 in
/-- Unconditional coupled tripling, from SA.2 and the tripling degeneration. -/
theorem proof_PR_3 : OM_S_PR_3 :=
  proof_PR_3_of_SA_2 OM.PolMul.Superadditivity.proof_SA_2

end OM.PolMul.Profiles

