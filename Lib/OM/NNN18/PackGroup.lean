import Lib.OM.NNN18.PackTriangle
import Lib.OM.NNN18.PackDensity
import Lib.OM.NNN13.AffineExtraction

/-! # The price of one packed correction class (PACKSTEP T7a; LABEL_PACKING (13)-(18))

`packed_family_bound`: a family `Σ_g edgeFactor(W_g)(fx_g ·, fy_g ·, ·)` of `K ≥ 1` residuals of a
common dyadic format `2^m`, with an extracted equality of size `2^e`, costs at most

  `packOverhead(c₁, K) · K^β · 2^{c·m + t e}`,     `(t + c₀ + c₁)/2 ≤ β ≤ 1`,

under an all-format affine tariff `c`.  The overhead `2^{2|c₁|+3} e^{10√(ln K) + 140}` is
`2^{o(log K)}`; it is paid later by retained copies (T7c).  Proof: Behrend's 3AP-free selection
(`exists_selection`), the literal triangle source (`packed_value`), padding to a dyadic format
(`value_le_of_card_le`). -/

noncomputable section
open scoped BigOperators Classical
open CoordinateTensor OM.NNN.Raw
open OM.NNN12 (Shape DyadicTensor)
open OM.NNN11.ExtractionAB (X)
namespace OM.NNN18

/-- The subexponential overhead of the packed source for `K` words. -/
def packOverhead (c1 : ℝ) (K : ℕ) : ℝ :=
  (2 : ℝ) ^ (2 * |c1| + 3) * Real.exp (10 * √(Real.log K) + 140)

lemma packOverhead_nonneg (c1 : ℝ) (K : ℕ) : 0 ≤ packOverhead c1 K := by
  unfold packOverhead; positivity

lemma packOverhead_mono (c1 : ℝ) {K K' : ℕ} (hK : 0 < K) (h : K ≤ K') :
    packOverhead c1 K ≤ packOverhead c1 K' := by
  unfold packOverhead
  have hl : Real.log K ≤ Real.log K' :=
    Real.log_le_log (by exact_mod_cast hK) (by exact_mod_cast h)
  have hs := Real.sqrt_le_sqrt hl
  gcongr

/-- `2^{2βn} ≤ 4 K^β e^{10√(ln K)+140}` when `2^n` is the dyadic size above a Behrend size. -/
lemma two_pow_le_overhead {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) {K N' n : ℕ} (hK : 1 ≤ K)
    (hn : (n : ℝ) ≤ Real.logb 2 N' + 1)
    (hlog : Real.log N' ≤ Real.log K / 2 + 5 * √(Real.log K) + 70) :
    (2 : ℝ) ^ (2 * β * n) ≤ 4 * (K : ℝ) ^ β * Real.exp (10 * √(Real.log K) + 140) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hn' : (n : ℝ) * Real.log 2 ≤ Real.log N' + Real.log 2 := by
    have := mul_le_mul_of_nonneg_right hn hl2.le
    rwa [add_mul, one_mul, Real.logb, div_mul_cancel₀ _ hl2.ne'] at this
  have hsq : 0 ≤ √(Real.log K) := Real.sqrt_nonneg _
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK
  have hlogK : 0 ≤ Real.log K := Real.log_nonneg (by exact_mod_cast hK)
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), Real.rpow_def_of_pos hK0]
  have h4 : (4 : ℝ) = Real.exp (2 * Real.log 2) := by
    rw [show (2 : ℝ) * Real.log 2 = Real.log 4 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num, Real.exp_log (by norm_num)]
  rw [h4, ← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.2
  have h1 : 2 * β * ((n : ℝ) * Real.log 2) ≤ 2 * β * (Real.log N' + Real.log 2) :=
    mul_le_mul_of_nonneg_left hn' (by positivity)
  have h2 : 2 * β * (Real.log N' + Real.log 2) ≤
      2 * β * (Real.log K / 2 + 5 * √(Real.log K) + 70 + Real.log 2) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have h3 : β * (10 * √(Real.log K) + 140 + 2 * Real.log 2) ≤
      10 * √(Real.log K) + 140 + 2 * Real.log 2 := by
    have : 0 ≤ 10 * √(Real.log K) + 140 + 2 * Real.log 2 := by positivity
    nlinarith
  nlinarith

/-- The exponent bookkeeping of the packed price. -/
lemma pack_exponent {θ t β c0 c1 : ℝ} (n e : ℕ) (_hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hθt : θ ≤ t)
    (hβ : (t + c0 + c1) / 2 ≤ β) :
    c0 * n + c1 * (n + 2) + θ * (e + 1 + n) ≤ t * e + 2 * β * n + (2 * |c1| + 1) := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have he : (0 : ℝ) ≤ e := Nat.cast_nonneg e
  have h1 : (c0 + c1 + θ) * n ≤ 2 * β * n := mul_le_mul_of_nonneg_right (by linarith) hn
  have h2 : θ * e ≤ t * e := mul_le_mul_of_nonneg_right hθt he
  have h3 : c1 ≤ |c1| := le_abs_self c1
  nlinarith

variable {G OA OB Z : Type} [Fintype G] [Fintype OA] [Fintype OB] [Fintype Z]

/-- **The packed class price** (LABEL_PACKING (13)-(15) with the explicit overhead). -/
theorem packed_family_bound (φ : PolMul.Spectral ℂ) {c : Fin 3 → ℝ} (hc : NNN13.AffineBound φ c)
    {t β : ℝ} (hθ : Foundations.PairUnitExponents.theta φ 2 ≤ t) (hβ : (t + c 0 + c 1) / 2 ≤ β)
    (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (m : Shape) (e : ℕ) (hZ : Fintype.card Z = 2 ^ m 2)
    (fx : G → OA → X (m 0) × X e) (fy : G → OB → X (m 1) × X e)
    (W : G → Tensor ℂ (X (m 0)) (X (m 1)) Z) (hG : 0 < Fintype.card G) :
    value φ (packedFamily fx fy W) ≤ packOverhead (c 1) (Fintype.card G) *
      (Fintype.card G : ℝ) ^ β * (2 : ℝ) ^ (NNN13.plane c (fun i => (m i : ℝ)) + t * e) := by
  set K := Fintype.card G
  obtain ⟨N', D, hN'0, hDlt, hD3, hKN, hlog⟩ := exists_selection K hG
  -- dyadic size above `N'`
  set n := Nat.log 2 N' + 1
  have hN'' : N' < 2 ^ n := Nat.lt_pow_succ_log_self (by norm_num) N'
  have hn : (n : ℝ) ≤ Real.logb 2 N' + 1 := by
    have h1 : 2 ^ Nat.log 2 N' ≤ N' := Nat.pow_log_le_self 2 hN'0.ne'
    have h2 : (Nat.log 2 N' : ℝ) ≤ Real.logb 2 N' := by
      rw [Real.le_logb_iff_rpow_le (by norm_num) (by exact_mod_cast hN'0)]
      rw [Real.rpow_natCast]; exact_mod_cast h1
    simp only [n, Nat.cast_add, Nat.cast_one]; linarith
  -- the injection of the class into `[N'] × D`
  have hcard : Fintype.card G ≤ Fintype.card (Finset.range N' ×ˢ D : Finset (ℕ × ℕ)) := by
    rw [Fintype.card_coe, Finset.card_product, Finset.card_range]; exact hKN
  obtain ⟨emb⟩ := Function.Embedding.nonempty_of_card_le hcard
  let pos : G → ℕ × ℕ := fun g => (emb g : ℕ × ℕ)
  have hmem (g : G) := Finset.mem_product.1 (emb g).2
  have hinj : Function.Injective pos := fun a b h => emb.injective (Subtype.ext h)
  have hd : ∀ g, (pos g).2 ∈ (D : Set ℕ) := fun g => (hmem g).2
  have hx : ∀ g, (pos g).1 < 2 ^ n := fun g => (Finset.mem_range.1 (hmem g).1).trans hN''
  have hdN : ∀ g, (pos g).2 < 2 ^ n := fun g => (hDlt _ (hmem g).2).trans hN''
  have hpos : 0 < 2 ^ n := by positivity
  have : Nonempty Z := Fintype.card_pos_iff.1 (by rw [hZ]; positivity)
  have hv := packed_value φ (2 ^ n) hpos pos hinj hD3 hd hx hdN fx fy W
  -- price of the packed residual
  let x' : Shape := ![m 0 + n, m 1 + n + 2, m 2]
  have hres := value_le_of_card_le φ hc x'
    (I := X (m 0) × Fin (2 ^ n)) (J := X (m 1) × Fin (3 * 2 ^ n)) (K := Z)
    (by simp [x', X, pow_add])
    (by
      show Fintype.card (X (m 1) × Fin (3 * 2 ^ n)) ≤ 2 ^ (m 1 + n + 2)
      rw [Fintype.card_prod, Fintype.card_fin]
      simp only [X, Fintype.card_fun, ZMod.card, Fintype.card_fin]
      calc 2 ^ m 1 * (3 * 2 ^ n) ≤ 2 ^ m 1 * (4 * 2 ^ n) :=
            Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (by norm_num))
        _ = 2 ^ (m 1 + n + 2) := by ring)
    (by simp [x', hZ]) (packedResidual (2 ^ n) pos W)
  have hE : Fintype.card (X e) = 2 ^ e := by simp [X]
  rw [hE] at hv
  have hθ0 := (Foundations.PairUnitExponents.theta_mem_Icc φ 2).1
  have hθ1 := (Foundations.PairUnitExponents.theta_mem_Icc φ 2).2
  -- combine
  have hedge : (((2 ^ e * (2 * 2 ^ n) : ℕ) : ℝ)) ^ Foundations.PairUnitExponents.theta φ 2 =
      (2 : ℝ) ^ (Foundations.PairUnitExponents.theta φ 2 * (e + 1 + n)) := by
    rw [show (2 ^ e * (2 * 2 ^ n) : ℕ) = 2 ^ (e + 1 + n) by ring, Nat.cast_pow, Nat.cast_ofNat,
      ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    push_cast; ring_nf
  rw [hedge] at hv
  have hplane : NNN13.plane c (fun i => (x' i : ℝ)) =
      NNN13.plane c (fun i => (m i : ℝ)) + (c 0 * n + c 1 * (n + 2)) := by
    simp only [NNN13.plane, x', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, Nat.cast_add, Nat.cast_ofNat]
    ring
  rw [hplane] at hres
  have hexp := pack_exponent (θ := Foundations.PairUnitExponents.theta φ 2) (c0 := c 0) (c1 := c 1)
    n e hθ0 hθ1 hθ hβ
  have hover := two_pow_le_overhead hβ0 hβ1 hG hn hlog
  calc value φ (packedFamily fx fy W)
      ≤ (2 : ℝ) ^ (NNN13.plane c (fun i => (m i : ℝ)) + (c 0 * n + c 1 * (n + 2))) *
          (2 : ℝ) ^ (Foundations.PairUnitExponents.theta φ 2 * (e + 1 + n)) :=
        hv.trans (mul_le_mul_of_nonneg_right hres (by positivity))
    _ = (2 : ℝ) ^ (NNN13.plane c (fun i => (m i : ℝ)) +
          (c 0 * n + c 1 * (n + 2) + Foundations.PairUnitExponents.theta φ 2 * (e + 1 + n))) := by
        rw [← Real.rpow_add (by norm_num)]; ring_nf
    _ ≤ (2 : ℝ) ^ (NNN13.plane c (fun i => (m i : ℝ)) + t * e + 2 * β * n + (2 * |c 1| + 1)) := by
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num); linarith
    _ = (2 : ℝ) ^ (2 * β * n) * (2 : ℝ) ^ (2 * |c 1| + 1) *
          (2 : ℝ) ^ (NNN13.plane c (fun i => (m i : ℝ)) + t * e) := by
        rw [← Real.rpow_add (by norm_num), ← Real.rpow_add (by norm_num)]; ring_nf
    _ ≤ 4 * (K : ℝ) ^ β * Real.exp (10 * √(Real.log K) + 140) * (2 : ℝ) ^ (2 * |c 1| + 1) *
          (2 : ℝ) ^ (NNN13.plane c (fun i => (m i : ℝ)) + t * e) := by
        gcongr
    _ = packOverhead (c 1) K * (K : ℝ) ^ β *
          (2 : ℝ) ^ (NNN13.plane c (fun i => (m i : ℝ)) + t * e) := by
        have h4 : (2 : ℝ) ^ (2 * |c 1| + 3) = 4 * (2 : ℝ) ^ (2 * |c 1| + 1) := by
          rw [show (2 * |c 1| + 3 : ℝ) = (2 * |c 1| + 1) + 2 by ring,
            Real.rpow_add (by norm_num)]
          norm_num
          ring
        unfold packOverhead
        rw [h4]
        ring

namespace PackBonds
open OM.NNN11.Network OM.NNN11.SlotExtraction OM.NNN12.Codes
open OM.NNN11 (card_eq_change_fintypes outputs_binary_card)
open Foundations.PairUnitExponents Foundations.OrientationTransport

variable {A B C : Type} [Fintype A] [Fintype B] [Fintype C]
  [DecidableEq A] [DecidableEq B] [DecidableEq C]
  {q d x y z N : ℕ} [Fact q.Prime]

/-- **The AB correction class** (bond `2`, word-dependent maps at `A`, `B`): `K` code words of a
common weight `w`, arbitrary coefficients and arbitrary operators on the other two bonds. -/
theorem packedAB_class (L : NNN12.BondLayout q d A B x y N) (φ : PolMul.Spectral ℂ)
    {c : Fin 3 → ℝ} (hc : NNN13.AffineBound φ c) {t β : ℝ}
    (hθ : Foundations.PairUnitExponents.theta φ 2 ≤ t)
    (hβ : (t + c 0 + c 1) / 2 ≤ β) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (T : Tensor ℂ (X x) (X y) (X z))
    (Q : Operator (BondBC B C (X y) (X z))) (R : Operator (BondCA C A (X z) (X x)))
    {G : Type} [Fintype G] (u : G → Word q N) (w : ℕ) (hw : ∀ g, weight (u g) = w)
    (α : G → ℂ) (hG : 0 < Fintype.card G) :
    value φ (∑ g, α g • contract T (L.kernel (u g)) Q R) ≤
      packOverhead (c 1) (Fintype.card G) * (Fintype.card G : ℝ) ^ β *
        (2 : ℝ) ^ ((Fintype.card A + Fintype.card B + Fintype.card C : ℕ) *
          NNN13.plane c ![(x : ℝ), y, z] + (d * (t - c 0 - c 1)) * w) := by
  set p := Fintype.card A + Fintype.card B + Fintype.card C
  let σ := fun g => NNN12.Cyclic.permutation L.coordinates (u g)
  let act := fun g => NNN12.Cyclic.active L.coordinates (u g)
  have hcross (g : G) : Fintype.card (EqualSlots (σ g) (act g)) = d * w := by
    rw [← hw g]; exact L.crossings (u g)
  have hcX (g : G) : Fintype.card (NNN11.ExtractionAB.ResidualX (C := C) (σ g) (act g)) =
      Fintype.card (X (p * x - d * w)) := by
    have hd := NNN11.ExtractionAB.residualX_card (C := C) (σ g) (act g)
    rw [hcross g] at hd
    rw [card_eq_change_fintypes hd]; simp [X, p]
  have hcY (g : G) : Fintype.card (NNN11.ExtractionAB.ResidualY (C := C) (σ g) (act g)) =
      Fintype.card (X (p * y - d * w)) := by
    have hd := NNN11.ExtractionAB.residualY_card (C := C) (σ g) (act g)
    rw [hcross g] at hd
    rw [card_eq_change_fintypes hd]; simp [X, p]
  have hcE (g : G) : Fintype.card (EqualSlots (σ g) (act g) → ZMod 2) =
      Fintype.card (X (d * w)) := by
    simp [X, hcross g]
  let eX := fun g => Fintype.equivOfCardEq (hcX g)
  let eY := fun g => Fintype.equivOfCardEq (hcY g)
  let eE := fun g => Fintype.equivOfCardEq (hcE g)
  let res := fun g => NNN11.ExtractionAB.residual (σ g) (act g) T
    (NNN11.ExtractionAB.productComplement (act g) Q R)
  let fx : G → Outputs A B C (X x) → X (p * x - d * w) × X (d * w) := fun g xx =>
    (eX g (NNN11.ExtractionAB.reduceX (σ g) (act g) xx),
      eE g (NNN11.ExtractionAB.outEqualX (σ g) (act g) xx))
  let fy : G → Outputs A B C (X y) → X (p * y - d * w) × X (d * w) := fun g yy =>
    (eY g (NNN11.ExtractionAB.reduceY (σ g) (act g) yy),
      eE g (NNN11.ExtractionAB.outEqualY (σ g) (act g) yy))
  let W : G → Tensor ℂ (X (p * x - d * w)) (X (p * y - d * w)) (Outputs A B C (X z)) :=
    fun g r s zz => α g * res g ((eX g).symm r) ((eY g).symm s) zz
  have hfam : (∑ g, α g • contract T (L.kernel (u g)) Q R) = packedFamily fx fy W := by
    funext xx yy zz
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, packedFamily]
    apply Finset.sum_congr rfl
    intro g _
    have hk : L.kernel (u g) = NNN11.ExtractionAB.permutationBond (σ g) := rfl
    rw [hk, NNN11.ExtractionAB.contract_eq_joint (σ g) (act g)
      (NNN12.Cyclic.fixed L.coordinates (u g)) T Q R,
      NNN11.ExtractionAB.residual_factorization (σ g) (act g)
      (NNN12.Cyclic.stable L.coordinates (u g)) T]
    simp only [NNN11.edgeFactor, fx, fy, W, res, (eE g).injective.eq_iff,
      Equiv.symm_apply_apply]
    split_ifs <;> ring
  rw [hfam]
  obtain ⟨g0⟩ := Fintype.card_pos_iff.1 hG
  obtain ⟨hEx, hEy⟩ := NNN13.extracted_le L (u g0)
  rw [hw g0] at hEx hEy
  have hx : d * w ≤ p * x := hEx.trans (Nat.mul_le_mul_right x (by omega))
  have hy : d * w ≤ p * y := hEy.trans (Nat.mul_le_mul_right y (by omega))
  have hb := packed_family_bound φ hc hθ hβ hβ0 hβ1 ![p * x - d * w, p * y - d * w, p * z]
    (d * w) (outputs_binary_card z) fx fy W hG
  have he := NNN13.affine_residual_AB (z := z) c t hx hy
  refine hb.trans (le_of_eq ?_)
  congr 2
  rw [he]
  push_cast
  ring

/-- An affine tariff transported along the party swap `1 ↔ 2`. -/
theorem affineBound_swap12 (φ : PolMul.Spectral ℂ) {c : Fin 3 → ℝ}
    (hc : NNN13.AffineBound φ c) :
    NNN13.AffineBound (pullPoint φ (rot 1)) ![c 0, c 2, c 1] := by
  intro v U
  have h := hc ![v 0, v 2, v 1] (Lib.E.RectangularSpectrum.swap12 U)
  have he := NNN11.value_swap12 φ (Lib.E.RectangularSpectrum.swap12 U)
  change value (pullPoint φ (rot 1)) U = _ at he
  rw [he]
  refine h.trans (le_of_eq ?_)
  congr 1
  simp [NNN13.plane]
  ring

/-- **The CA correction class** (bond `1`, word-dependent maps at `C`, `A`), by the party swap
`1 ↔ 2`, which turns it into an AB-oriented family for the pulled-back spectral point. -/
theorem packedCA_class (L : NNN12.BondLayout q d C A z x N) (φ : PolMul.Spectral ℂ)
    {c : Fin 3 → ℝ} (hc : NNN13.AffineBound φ c) {t β : ℝ}
    (hθ : Foundations.PairUnitExponents.theta φ 1 ≤ t)
    (hβ : (t + c 0 + c 2) / 2 ≤ β) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (T : Tensor ℂ (X x) (X y) (X z))
    (P : Operator (BondAB A B (X x) (X y))) (Q : Operator (BondBC B C (X y) (X z)))
    {G : Type} [Fintype G] (u : G → Word q N) (w : ℕ) (hw : ∀ g, weight (u g) = w)
    (α : G → ℂ) (hG : 0 < Fintype.card G) :
    value φ (∑ g, α g • contract T P Q (L.kernel (u g))) ≤
      packOverhead (c 2) (Fintype.card G) * (Fintype.card G : ℝ) ^ β *
        (2 : ℝ) ^ ((Fintype.card A + Fintype.card B + Fintype.card C : ℕ) *
          NNN13.plane c ![(x : ℝ), y, z] + (d * (t - c 0 - c 2)) * w) := by
  set p := Fintype.card A + Fintype.card B + Fintype.card C
  let σ := fun g => NNN12.Cyclic.permutation L.coordinates (u g)
  let act := fun g => NNN12.Cyclic.active L.coordinates (u g)
  have hcross (g : G) : Fintype.card (EqualSlots (σ g) (act g)) = d * w := by
    rw [← hw g]; exact L.crossings (u g)
  have hcX (g : G) : Fintype.card (NNN11.ExtractionCA.ResidualX (B := B) (σ g) (act g)) =
      Fintype.card (X (p * x - d * w)) := by
    have hd := NNN11.ExtractionCA.residualX_card (B := B) (σ g) (act g)
    rw [hcross g] at hd
    rw [card_eq_change_fintypes hd]; simp [X, p]
  have hcZ (g : G) : Fintype.card (NNN11.ExtractionCA.ResidualZ (B := B) (σ g) (act g)) =
      Fintype.card (X (p * z - d * w)) := by
    have hd := NNN11.ExtractionCA.residualZ_card (B := B) (σ g) (act g)
    rw [hcross g] at hd
    rw [card_eq_change_fintypes hd]; simp [X, p]
  have hcE (g : G) : Fintype.card (EqualSlots (σ g) (act g) → ZMod 2) =
      Fintype.card (X (d * w)) := by
    simp [X, hcross g]
  let eX := fun g => Fintype.equivOfCardEq (hcX g)
  let eZ := fun g => Fintype.equivOfCardEq (hcZ g)
  let eE := fun g => Fintype.equivOfCardEq (hcE g)
  let res := fun g => NNN11.ExtractionCA.residual (σ g) (act g) T
    (NNN11.ExtractionCA.productComplement (act g) P Q)
  let fx : G → Outputs A B C (X x) → X (p * x - d * w) × X (d * w) := fun g xx =>
    (eX g (NNN11.ExtractionCA.reduceX (σ g) (act g) xx),
      eE g (NNN11.ExtractionCA.outEqualX (σ g) (act g) xx))
  let fz : G → Outputs A B C (X z) → X (p * z - d * w) × X (d * w) := fun g zz =>
    (eZ g (NNN11.ExtractionCA.reduceZ (σ g) (act g) zz),
      eE g (NNN11.ExtractionCA.outEqualZ (σ g) (act g) zz))
  let W : G → Tensor ℂ (X (p * x - d * w)) (X (p * z - d * w)) (Outputs A B C (X y)) :=
    fun g r s yy => α g * res g ((eX g).symm r) yy ((eZ g).symm s)
  have hfam : Lib.E.RectangularSpectrum.swap12
      (∑ g, α g • contract T P Q (L.kernel (u g))) = packedFamily fx fz W := by
    funext xx zz yy
    simp only [Lib.E.RectangularSpectrum.swap12, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      packedFamily]
    apply Finset.sum_congr rfl
    intro g _
    have hk : L.kernel (u g) = NNN11.ExtractionAB.permutationBond (σ g) := rfl
    rw [hk, NNN11.ExtractionCA.contract_eq_joint (σ g) (act g)
      (NNN12.Cyclic.fixed L.coordinates (u g)) T P Q,
      NNN11.ExtractionCA.residual_factorization (σ g) (act g)
      (NNN12.Cyclic.stable L.coordinates (u g)) T]
    simp only [NNN11.edgeFactor, fx, fz, W, res, (eE g).injective.eq_iff,
      Equiv.symm_apply_apply]
    by_cases h : NNN11.ExtractionCA.outEqualZ (σ g) (act g) zz =
        NNN11.ExtractionCA.outEqualX (σ g) (act g) xx
    · simp [h]
    · simp [h, Ne.symm h]
  have hval := NNN11.value_swap12 φ (∑ g, α g • contract T P Q (L.kernel (u g)))
  rw [← hval, hfam]
  obtain ⟨g0⟩ := Fintype.card_pos_iff.1 hG
  obtain ⟨hEz, hEx⟩ := NNN13.extracted_le L (u g0)
  rw [hw g0] at hEx hEz
  have hx : d * w ≤ p * x := hEx.trans (Nat.mul_le_mul_right x (by omega))
  have hz : d * w ≤ p * z := hEz.trans (Nat.mul_le_mul_right z (by omega))
  have hθ' : Foundations.PairUnitExponents.theta (pullPoint φ (rot 1)) 2 ≤ t := by
    rw [theta_legReindex, rot_symm_two]; exact hθ
  have hβ' : (t + (![c 0, c 2, c 1] : Fin 3 → ℝ) 0 + (![c 0, c 2, c 1] : Fin 3 → ℝ) 1) / 2 ≤ β := by
    simpa using hβ
  have hb := packed_family_bound (pullPoint φ (rot 1)) (affineBound_swap12 φ hc) hθ' hβ'
    hβ0 hβ1 ![p * x - d * w, p * z - d * w, p * y]
    (d * w) (outputs_binary_card y) fx fz W hG
  have he := NNN13.affine_residual_CA (y := y) c t hx hz
  refine hb.trans (le_of_eq ?_)
  have hpl : NNN13.plane ![c 0, c 2, c 1]
      (fun i => ((![p * x - d * w, p * z - d * w, p * y] : Shape) i : ℝ)) =
      NNN13.plane c (fun i => ((![p * x - d * w, p * y, p * z - d * w] : Shape) i : ℝ)) := by
    simp [NNN13.plane]; ring
  congr 2
  rw [hpl, he]
  push_cast
  ring

end PackBonds
end OM.NNN18
