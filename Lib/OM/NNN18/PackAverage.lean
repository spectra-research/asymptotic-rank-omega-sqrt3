import Lib.OM.NNN18.PackNetwork
import Lib.OM.NNN13.Averaged

/-! # The averaged packed network inequality (PACKSTEP T7c, first half)

Analogue of `NNN13.combined_network_average` with packed charging on the two non-retained
bonds: bond `0` (BC, retained party `A`) keeps the ordinary moment, bonds `1` (CA) and `2` (AB)
pay `Ov · (N+1)^{1-β} · moment(…, M/β, D/β)^β` (T6 + T7a). -/

noncomputable section
open scoped BigOperators Classical
namespace OM.NNN18.PackNet
open CoordinateTensor OM.NNN.Raw OM.NNN2 OM.NNN11.Network
open OM.NNN11 (bondLog)
open OM.NNN11.ExtractionAB (X)
open Foundations.PairUnitExponents OM.NNN12.Codes
set_option maxHeartbeats 2000000

variable {A B C : Type} [Fintype A] [Fintype B] [Fintype C]
  [DecidableEq A] [DecidableEq B] [DecidableEq C]
  {x y z : ℕ} {N r q d : Fin 3 → ℕ} [∀ i, Fact (q i).Prime]

lemma classCount_le {q' N' r' : ℕ} [Fact q'.Prime] (code : Word q' r' →ₗ[ZMod q'] Word q' N')
    (w : ℕ) : OM.NNN18.classCount code w ≤ q' ^ r' := by
  unfold OM.NNN18.classCount
  calc _ ≤ (Finset.univ.erase (0 : Word q' r')).card := Finset.card_filter_le _ _
    _ ≤ (Finset.univ : Finset (Word q' r')).card := Finset.card_erase_le
    _ = q' ^ r' := by rw [Finset.card_univ, word_card]

/-- The packed correction total of one bond, from the per-class price and the fractional code
moment: `Σ_w Ov K_w^β 2^{M + D w} ≤ Ov (N+1)^{1-β} moment(q,N,r,M/β,D/β)^β`. -/
lemma packed_total {q' N' r' : ℕ} [Fact q'.Prime] (code : Word q' r' →ₗ[ZMod q'] Word q' N')
    (Ov M D β : ℝ) (hOv : 0 ≤ Ov) (hβ0 : 0 < β)
    (hcode : ∑ w ∈ Finset.range (N' + 1), (OM.NNN18.classCount code w : ℝ) ^ β *
        (2 : ℝ) ^ (D * w) ≤ ((N' + 1 : ℕ) : ℝ) ^ (1 - β) *
          (((q' : ℝ) ^ r' - 1) / (q' : ℝ) ^ N' * (1 + (q' - 1 : ℝ) * (2 : ℝ) ^ (D / β)) ^ N') ^ β) :
    ∑ w ∈ Finset.range (N' + 1),
        Ov * (OM.NNN18.classCount code w : ℝ) ^ β * (2 : ℝ) ^ (M + D * w) ≤
      Ov * ((N' + 1 : ℕ) : ℝ) ^ (1 - β) * NNN12.moment q' N' r' (M / β) (D / β) ^ β := by
  have hX : 0 ≤ ((q' : ℝ) ^ r' - 1) / (q' : ℝ) ^ N' *
      (1 + (q' - 1 : ℝ) * (2 : ℝ) ^ (D / β)) ^ N' := by
    have h1 : (1 : ℝ) ≤ (q' : ℝ) ^ r' := one_le_pow₀ NNN12.alphabet_one_le
    have h2 : 0 ≤ (q' - 1 : ℝ) := sub_nonneg.mpr NNN12.alphabet_one_le
    have := NNN12.alphabet_pos (q := q')
    apply mul_nonneg (div_nonneg (by linarith) (by positivity))
    positivity
  have hsplit : ∀ w ∈ Finset.range (N' + 1),
      Ov * (OM.NNN18.classCount code w : ℝ) ^ β * (2 : ℝ) ^ (M + D * w) =
        Ov * (2 : ℝ) ^ M * ((OM.NNN18.classCount code w : ℝ) ^ β * (2 : ℝ) ^ (D * w)) := by
    intro w _
    rw [Real.rpow_add (by norm_num)]; ring
  rw [Finset.sum_congr rfl hsplit, ← Finset.mul_sum]
  have hmom : NNN12.moment q' N' r' (M / β) (D / β) ^ β = (2 : ℝ) ^ M *
      (((q' : ℝ) ^ r' - 1) / (q' : ℝ) ^ N' * (1 + (q' - 1 : ℝ) * (2 : ℝ) ^ (D / β)) ^ N') ^ β := by
    unfold NNN12.moment
    rw [Real.mul_rpow (by positivity) hX, ← Real.rpow_mul (by norm_num), div_mul_cancel₀ _ hβ0.ne']
  rw [hmom]
  have h2M : 0 ≤ Ov * (2 : ℝ) ^ M := by positivity
  calc Ov * (2 : ℝ) ^ M * ∑ w ∈ Finset.range (N' + 1),
        (OM.NNN18.classCount code w : ℝ) ^ β * (2 : ℝ) ^ (D * w)
      ≤ Ov * (2 : ℝ) ^ M * (((N' + 1 : ℕ) : ℝ) ^ (1 - β) *
          (((q' : ℝ) ^ r' - 1) / (q' : ℝ) ^ N' *
            (1 + (q' - 1 : ℝ) * (2 : ℝ) ^ (D / β)) ^ N') ^ β) :=
        mul_le_mul_of_nonneg_left hcode h2M
    _ = _ := by ring

/-- **The averaged packed network inequality.** -/
theorem packed_network_average (φ : PolMul.Spectral ℂ)
    (c : Fin 3 → Fin 3 → ℝ) (hb : ∀ i, NNN13.AffineBound φ (c i))
    (t β : Fin 3 → ℝ) (hθ : ∀ i, Foundations.PairUnitExponents.theta φ i ≤ t i)
    (hβ1 : (t 1 + c 1 0 + c 1 2) / 2 ≤ β 1) (hβ2 : (t 2 + c 2 0 + c 2 1) / 2 ≤ β 2)
    (hβpos : ∀ i, 0 < β i) (hβle : ∀ i, β i ≤ 1)
    (Lab : NNN12.BondLayout (q 2) (d 2) A B x y (N 2))
    (Lbc : NNN12.BondLayout (q 0) (d 0) B C y z (N 0))
    (Lca : NNN12.BondLayout (q 1) (d 1) C A z x (N 1))
    (hr : ∀ i, r i ≤ N i) (T : Tensor ℂ (X x) (X y) (X z)) :
    value φ T ^ (Fintype.card A + Fintype.card B + Fintype.card C) ≤
      (2 : ℝ) ^ (∑ i, t i * ((bondLog (Fintype.card A) (Fintype.card B)
        (Fintype.card C) x y z i : ℝ) - r i * Real.logb 2 (q i))) +
      NNN12.moment (q 0) (N 0) (r 0)
        ((Fintype.card B + Fintype.card C : ℕ) * NNN13.plane (c 0) ![(x : ℝ), y, z])
        (d 0 * (t 0 - c 0 1 - c 0 2)) * value φ T ^ Fintype.card A +
      OM.NNN18.packOverhead (c 1 2) (q 1 ^ r 1) * ((N 1 + 1 : ℕ) : ℝ) ^ (1 - β 1) *
        NNN12.moment (q 1) (N 1) (r 1)
          ((Fintype.card A + Fintype.card B + Fintype.card C : ℕ) *
            NNN13.plane (c 1) ![(x : ℝ), y, z] / β 1)
          (d 1 * (t 1 - c 1 0 - c 1 2) / β 1) ^ β 1 +
      OM.NNN18.packOverhead (c 2 1) (q 2 ^ r 2) * ((N 2 + 1 : ℕ) : ℝ) ^ (1 - β 2) *
        NNN12.moment (q 2) (N 2) (r 2)
          ((Fintype.card A + Fintype.card B + Fintype.card C : ℕ) *
            NNN13.plane (c 2) ![(x : ℝ), y, z] / β 2)
          (d 2 * (t 2 - c 2 0 - c 2 1) / β 2) ^ β 2 := by
  obtain ⟨code0, hc0⟩ := NNN12.exists_generator_price (q := q 0) (N 0) (r 0)
    ((Fintype.card B + Fintype.card C : ℕ) * NNN13.plane (c 0) ![(x : ℝ), y, z])
    (d 0 * (t 0 - c 0 1 - c 0 2))
  obtain ⟨code1, hc1⟩ := OM.NNN18.exists_generator_packed (q := q 1) (N 1) (r 1)
    (d 1 * (t 1 - c 1 0 - c 1 2)) (β 1) (hβpos 1) (hβle 1)
  obtain ⟨code2, hc2⟩ := OM.NNN18.exists_generator_packed (q := q 2) (N 2) (r 2)
    (d 2 * (t 2 - c 2 0 - c 2 1)) (β 2) (hβpos 2) (hβle 2)
  let code : (i : Fin 3) → Word (q i) (r i) →ₗ[ZMod (q i)] Word (q i) (N i) :=
    Fin.cases code0 (Fin.cases code1 (Fin.cases code2 (fun i => Fin.elim0 i)))
  let p0 : Word (q 0) (N 0) → ℝ := fun w =>
    (2 : ℝ) ^ ((Fintype.card B + Fintype.card C : ℕ) * NNN13.plane (c 0) ![(x : ℝ), y, z] +
      (d 0 * (t 0 - c 0 1 - c 0 2)) * weight w) * value φ T ^ Fintype.card A
  let pAB : ℕ → ℝ := fun w =>
    OM.NNN18.packOverhead (c 2 1) (q 2 ^ r 2) * (OM.NNN18.classCount code2 w : ℝ) ^ β 2 *
      (2 : ℝ) ^ ((Fintype.card A + Fintype.card B + Fintype.card C : ℕ) *
        NNN13.plane (c 2) ![(x : ℝ), y, z] + (d 2 * (t 2 - c 2 0 - c 2 1)) * w)
  let pCA : ℕ → ℝ := fun w =>
    OM.NNN18.packOverhead (c 1 2) (q 1 ^ r 1) * (OM.NNN18.classCount code1 w : ℝ) ^ β 1 *
      (2 : ℝ) ^ ((Fintype.card A + Fintype.card B + Fintype.card C : ℕ) *
        NNN13.plane (c 1) ![(x : ℝ), y, z] + (d 1 * (t 1 - c 1 0 - c 1 2)) * w)
  have hbc (w : Word (q 0) (N 0)) : value φ (contract (A := A) (B := B) (C := C) T (identity _)
      (Lbc.kernel w) (identity _)) ≤ p0 w :=
    NNN13.retained_BC_affine Lbc w φ (hb 0) (t 0) (hθ 0) T
  have hab : ∀ (α : Word (q 2) (r 2) → ℂ) (w : ℕ) Q R,
      value φ (∑ c' ∈ wclass (code 2) w,
        α c' • contract (A := A) (B := B) (C := C) T (Lab.kernel (code 2 c')) Q R) ≤ pAB w := by
    intro α w Q R
    have hpAB : 0 ≤ pAB w := by
      have := OM.NNN18.packOverhead_nonneg (c 2 1) (q 2 ^ r 2)
      simp only [pAB]
      positivity
    by_cases hK : (wclass (code 2) w).card = 0
    · rw [Finset.card_eq_zero.1 hK, Finset.sum_empty, value_zero]; exact hpAB
    · have hcard : Fintype.card (wclass (code 2) w) = OM.NNN18.classCount code2 w := by
        rw [Fintype.card_coe]; rfl
      have hG : 0 < Fintype.card (wclass (code 2) w) := by
        rw [Fintype.card_coe]; omega
      rw [← Finset.sum_coe_sort (wclass (code 2) w)]
      have hcl := OM.NNN18.PackBonds.packedAB_class Lab φ (hb 2) (hθ 2) hβ2 (hβpos 2).le
        (hβle 2) T Q R (G := wclass (code 2) w) (fun g => code 2 g.1) w
        (fun g => (Finset.mem_filter.1 g.2).2) (fun g => α g.1) hG
      rw [hcard] at hcl hG
      refine hcl.trans ?_
      have hmono := OM.NNN18.packOverhead_mono (c 2 1) hG (classCount_le code2 w)
      simp only [pAB]
      gcongr
  have hca : ∀ (α : Word (q 1) (r 1) → ℂ) (w : ℕ) P Q,
      value φ (∑ c' ∈ wclass (code 1) w,
        α c' • contract (A := A) (B := B) (C := C) T P Q (Lca.kernel (code 1 c'))) ≤ pCA w := by
    intro α w P Q
    have hpCA : 0 ≤ pCA w := by
      have := OM.NNN18.packOverhead_nonneg (c 1 2) (q 1 ^ r 1)
      simp only [pCA]
      positivity
    by_cases hK : (wclass (code 1) w).card = 0
    · rw [Finset.card_eq_zero.1 hK, Finset.sum_empty, value_zero]; exact hpCA
    · have hcard : Fintype.card (wclass (code 1) w) = OM.NNN18.classCount code1 w := by
        rw [Fintype.card_coe]; rfl
      have hG : 0 < Fintype.card (wclass (code 1) w) := by
        rw [Fintype.card_coe]; omega
      rw [← Finset.sum_coe_sort (wclass (code 1) w)]
      have hcl := OM.NNN18.PackBonds.packedCA_class Lca φ (hb 1) (hθ 1) hβ1 (hβpos 1).le
        (hβle 1) T P Q (G := wclass (code 1) w) (fun g => code 1 g.1) w
        (fun g => (Finset.mem_filter.1 g.2).2) (fun g => α g.1) hG
      rw [hcard] at hcl hG
      refine hcl.trans ?_
      have hmono := OM.NNN18.packOverhead_mono (c 1 2) hG (classCount_le code1 w)
      simp only [pCA]
      gcongr
  have hnet := network_packed_price_lastBC φ T Lab Lbc Lca code p0 pAB pCA hab hbc hca
  have hhead := NNN12.headPrice_enlarge Lab Lbc Lca hr φ t hθ
  have hsum0 : (∑ c' ∈ Finset.univ.erase (0 : Word (q 0) (r 0)), p0 (code 0 c')) ≤
      NNN12.moment (q 0) (N 0) (r 0)
        ((Fintype.card B + Fintype.card C : ℕ) * NNN13.plane (c 0) ![(x : ℝ), y, z])
        (d 0 * (t 0 - c 0 1 - c 0 2)) * value φ T ^ Fintype.card A := by
    simp only [p0]
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right hc0 (pow_nonneg (φ.nonneg _) _)
  have hsum1 : (∑ w ∈ Finset.range (N 1 + 1), pCA w) ≤
      OM.NNN18.packOverhead (c 1 2) (q 1 ^ r 1) * ((N 1 + 1 : ℕ) : ℝ) ^ (1 - β 1) *
        NNN12.moment (q 1) (N 1) (r 1)
          ((Fintype.card A + Fintype.card B + Fintype.card C : ℕ) *
            NNN13.plane (c 1) ![(x : ℝ), y, z] / β 1)
          (d 1 * (t 1 - c 1 0 - c 1 2) / β 1) ^ β 1 :=
    packed_total code1 _ _ _ (β 1) (OM.NNN18.packOverhead_nonneg _ _) (hβpos 1) hc1
  have hsum2 : (∑ w ∈ Finset.range (N 2 + 1), pAB w) ≤
      OM.NNN18.packOverhead (c 2 1) (q 2 ^ r 2) * ((N 2 + 1 : ℕ) : ℝ) ^ (1 - β 2) *
        NNN12.moment (q 2) (N 2) (r 2)
          ((Fintype.card A + Fintype.card B + Fintype.card C : ℕ) *
            NNN13.plane (c 2) ![(x : ℝ), y, z] / β 2)
          (d 2 * (t 2 - c 2 0 - c 2 1) / β 2) ^ β 2 :=
    packed_total code2 _ _ _ (β 2) (OM.NNN18.packOverhead_nonneg _ _) (hβpos 2) hc2
  linarith only [hnet, hhead, hsum0, hsum1, hsum2]

end OM.NNN18.PackNet
