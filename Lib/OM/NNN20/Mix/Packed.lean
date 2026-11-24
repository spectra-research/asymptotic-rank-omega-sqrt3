import Lib.OM.NNN20.Mix.ExtractCA
import Lib.OM.NNN18.PackGroup

/-! # Packed correction classes priced by a tariff at the packed formats only

NNN.18's `packed_family_bound` prices a packed class with a *global* tariff. A catalytic parent
is a tariff only on an open cone of formats; the label source applies it at the packed formats
`m + (n, n + 2, 0)`, with `n ≤ log₂ K / 2 + O(√log K)` (`K` the class size). Here the parent is
asked for exactly those formats (`packed_family_bound_at`). -/

noncomputable section
open scoped BigOperators Classical
namespace OM.NNN20.Mix
open CoordinateTensor OM.NNN.Raw OM.NNN2
open OM.NNN12 (Shape DyadicTensor)
open OM.NNN11.ExtractionAB (X)
open OM.NNN18 (packOverhead packedFamily packedResidual)

/-- a bound at one dyadic format prices every smaller tensor (zero padding) -/
theorem value_le_of_card_le_at (φ : PolMul.Spectral ℂ) {G : ℝ} (x : Shape)
    (hb : ∀ U : DyadicTensor x, value φ U ≤ (2 : ℝ) ^ G)
    {I J K : Type} [Fintype I] [Fintype J] [Fintype K]
    (hi : Fintype.card I ≤ 2 ^ x 0) (hj : Fintype.card J ≤ 2 ^ x 1)
    (hk : Fintype.card K ≤ 2 ^ x 2) (T : Tensor ℂ I J K) : value φ T ≤ (2 : ℝ) ^ G := by
  have hci : Fintype.card I ≤ Fintype.card (OM.NNN8.BinaryWord (x 0)) := by
    rwa [OM.NNN8.binary_word_card]
  have hcj : Fintype.card J ≤ Fintype.card (OM.NNN8.BinaryWord (x 1)) := by
    rwa [OM.NNN8.binary_word_card]
  have hck : Fintype.card K ≤ Fintype.card (OM.NNN8.BinaryWord (x 2)) := by
    rwa [OM.NNN8.binary_word_card]
  obtain ⟨e0⟩ := Function.Embedding.nonempty_of_card_le hci
  obtain ⟨e1⟩ := Function.Embedding.nonempty_of_card_le hcj
  obtain ⟨e2⟩ := Function.Embedding.nonempty_of_card_le hck
  let T' : DyadicTensor x := fun i j k =>
    Function.extend e0 (fun a => Function.extend e1 (fun b => Function.extend e2
      (fun c => T a b c) 0 k) 0 j) 0 i
  have hT : T = fun a b c => T' (e0 a) (e1 b) (e2 c) := by
    funext a b c
    simp only [T', e0.injective.extend_apply, e1.injective.extend_apply, e2.injective.extend_apply]
  rw [hT, ← OM.NNN18.mapTensor_indicator]
  exact (value_map_le φ T' _ _ _).trans (hb T')

/-- the largest label enlargement of a packed class of size `K` -/
def packBound (K : ℕ) : ℝ := (Real.log K / 2 + 5 * √(Real.log K) + 70) / Real.log 2 + 1

variable {G OA OB Z : Type} [Fintype G] [Fintype OA] [Fintype OB] [Fintype Z]

/-- **The packed class price with the parent tariff required only at the packed formats.** -/
theorem packed_family_bound_at (φ : PolMul.Spectral ℂ) {c : Fin 3 → ℝ} (m : Shape)
    (hc : ∀ n : ℕ, (n : ℝ) ≤ packBound (Fintype.card G) →
      ∀ U : DyadicTensor ![m 0 + n, m 1 + n + 2, m 2],
        value φ U ≤ (2 : ℝ) ^ NNN13.plane c (fun i => ((![m 0 + n, m 1 + n + 2, m 2] i : ℕ) : ℝ)))
    {t β : ℝ} (hθ : Foundations.PairUnitExponents.theta φ 2 ≤ t) (hβ : (t + c 0 + c 1) / 2 ≤ β)
    (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (e : ℕ) (hZ : Fintype.card Z = 2 ^ m 2)
    (fx : G → OA → X (m 0) × X e) (fy : G → OB → X (m 1) × X e)
    (W : G → Tensor ℂ (X (m 0)) (X (m 1)) Z) (hG : 0 < Fintype.card G) :
    value φ (packedFamily fx fy W) ≤ packOverhead (c 1) (Fintype.card G) *
      (Fintype.card G : ℝ) ^ β * (2 : ℝ) ^ (NNN13.plane c (fun i => (m i : ℝ)) + t * e) := by
  set K := Fintype.card G
  obtain ⟨N', D, hN'0, hDlt, hD3, hKN, hlog⟩ := OM.NNN18.exists_selection K hG
  set n := Nat.log 2 N' + 1
  have hN'' : N' < 2 ^ n := Nat.lt_pow_succ_log_self (by norm_num) N'
  have hn : (n : ℝ) ≤ Real.logb 2 N' + 1 := by
    have h1 : 2 ^ Nat.log 2 N' ≤ N' := Nat.pow_log_le_self 2 hN'0.ne'
    have h2 : (Nat.log 2 N' : ℝ) ≤ Real.logb 2 N' := by
      rw [Real.le_logb_iff_rpow_le (by norm_num) (by exact_mod_cast hN'0)]
      rw [Real.rpow_natCast]; exact_mod_cast h1
    simp only [n, Nat.cast_add, Nat.cast_one]; linarith
  have hnB : (n : ℝ) ≤ packBound K := by
    have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
    have : Real.logb 2 N' ≤ (Real.log K / 2 + 5 * √(Real.log K) + 70) / Real.log 2 := by
      rw [Real.logb, div_le_div_iff_of_pos_right hl2]; exact hlog
    simp only [packBound]; linarith
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
  have hv := OM.NNN18.packed_value φ (2 ^ n) hpos pos hinj hD3 hd hx hdN fx fy W
  let x' : Shape := ![m 0 + n, m 1 + n + 2, m 2]
  have hres := value_le_of_card_le_at φ x' (hc n hnB)
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
  have hedge : (((2 ^ e * (2 * 2 ^ n) : ℕ) : ℝ)) ^ Foundations.PairUnitExponents.theta φ 2 =
      (2 : ℝ) ^ (Foundations.PairUnitExponents.theta φ 2 * (e + 1 + n)) := by
    rw [show (2 ^ e * (2 * 2 ^ n) : ℕ) = 2 ^ (e + 1 + n) by ring, Nat.cast_pow, Nat.cast_ofNat,
      ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    push_cast; ring_nf
  rw [hedge] at hv
  have hplane : NNN13.plane c (fun i => ((x' i : ℕ) : ℝ)) =
      NNN13.plane c (fun i => (m i : ℝ)) + (c 0 * n + c 1 * (n + 2)) := by
    simp only [NNN13.plane, x', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, Nat.cast_add, Nat.cast_ofNat]
    ring
  rw [hplane] at hres
  have hexp := OM.NNN18.pack_exponent (θ := Foundations.PairUnitExponents.theta φ 2) (c0 := c 0)
    (c1 := c 1) n e hθ0 hθ1 hθ hβ
  have hover := OM.NNN18.two_pow_le_overhead hβ0 hβ1 hG hn hlog
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

end OM.NNN20.Mix

namespace OM.NNN20.Mix
open CoordinateTensor OM.NNN.Raw OM.NNN2 OM.NNN11.Network OM.NNN11.SlotExtraction
open OM.NNN12 (Shape DyadicTensor)
open OM.NNN11.ExtractionAB (X)
open OM.NNN11 (card_eq_change_fintypes)
open OM.NNN12.Codes
open OM.NNN18 (packOverhead packedFamily)

set_option maxHeartbeats 2000000

variable {A B C : Type} [Fintype A] [Fintype B] [Fintype C]
  [DecidableEq A] [DecidableEq B] [DecidableEq C]
  {q d N : ℕ} [Fact q.Prime]

/-- the residual format of an AB class of crossing weight `e` -/
def resAB (a b c xa ya za xb yb zb xc yc zc e : ℕ) : Shape :=
  ![a * xa + b * xb + c * xc - e, a * ya + b * yb + c * yc - e, a * za + b * zb + c * zc]

/-- **An AB correction class of a mixed network** (bond `2`): `K` code words of a common weight
`w`, arbitrary coefficients and arbitrary operators on the other two bonds; the parent tariff `c`
is needed only at the packed formats of the residual format. -/
theorem packedAB3_class {xb ya : ℕ} (L : OM.NNN12.BondLayout q d A B xb ya N) (φ : PolMul.Spectral ℂ)
    {xa za yb zb xc yc zc : ℕ} {c : Fin 3 → ℝ} {t β : ℝ}
    (hθ : Foundations.PairUnitExponents.theta φ 2 ≤ t)
    (hβ : (t + c 0 + c 1) / 2 ≤ β) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (TA : Tensor ℂ (X xa) (X ya) (X za)) (TB : Tensor ℂ (X xb) (X yb) (X zb))
    (TC : Tensor ℂ (X xc) (X yc) (X zc))
    (Q : Operator (BondBC B C (X yc) (X zb))) (R : Operator (BondCA C A (X za) (X xc)))
    {G : Type} [Fintype G] (u : G → Word q N) (w : ℕ) (hw : ∀ g, weight (u g) = w)
    (α : G → ℂ) (hG : 0 < Fintype.card G)
    (hc : ∀ n : ℕ, (n : ℝ) ≤ packBound (Fintype.card G) →
      ∀ U : DyadicTensor
        ![resAB (Fintype.card A) (Fintype.card B) (Fintype.card C) xa ya za xb yb zb xc yc zc
            (d * w) 0 + n,
          resAB (Fintype.card A) (Fintype.card B) (Fintype.card C) xa ya za xb yb zb xc yc zc
            (d * w) 1 + n + 2,
          resAB (Fintype.card A) (Fintype.card B) (Fintype.card C) xa ya za xb yb zb xc yc zc
            (d * w) 2],
        value φ U ≤ (2 : ℝ) ^ NNN13.plane c (fun i => ((![
          resAB (Fintype.card A) (Fintype.card B) (Fintype.card C) xa ya za xb yb zb xc yc zc
            (d * w) 0 + n,
          resAB (Fintype.card A) (Fintype.card B) (Fintype.card C) xa ya za xb yb zb xc yc zc
            (d * w) 1 + n + 2,
          resAB (Fintype.card A) (Fintype.card B) (Fintype.card C) xa ya za xb yb zb xc yc zc
            (d * w) 2] i : ℕ) : ℝ))) :
    value φ (∑ g, α g • contract3 TA TB TC (L.kernel (u g)) Q R) ≤
      packOverhead (c 1) (Fintype.card G) * (Fintype.card G : ℝ) ^ β *
        (2 : ℝ) ^ (NNN13.plane c (fun i => ((resAB (Fintype.card A) (Fintype.card B)
          (Fintype.card C) xa ya za xb yb zb xc yc zc (d * w) i : ℕ) : ℝ)) + t * (d * w : ℕ)) := by
  set m := resAB (Fintype.card A) (Fintype.card B) (Fintype.card C) xa ya za xb yb zb xc yc zc
    (d * w) with hm
  let σ := fun g => OM.NNN12.Cyclic.permutation L.coordinates (u g)
  let act := fun g => OM.NNN12.Cyclic.active L.coordinates (u g)
  have hcross (g : G) : Fintype.card (EqualSlots (σ g) (act g)) = d * w := by
    rw [← hw g]; exact L.crossings (u g)
  have hcX (g : G) : Fintype.card (AB.ResidualX3 (XA := X xa) (XC := X xc) (C := C) (σ g) (act g)) =
      Fintype.card (X (m 0)) := by
    have hd := AB.residualX3_card (C := C) (xa := xa) (xc := xc) (σ g) (act g)
    rw [hcross g] at hd
    rw [OM.NNN11.card_eq_change_fintypes hd]; simp [X, hm, resAB]
  have hcY (g : G) : Fintype.card (AB.ResidualY3 (YB := X yb) (YC := X yc) (C := C) (σ g) (act g)) =
      Fintype.card (X (m 1)) := by
    have hd := AB.residualY3_card (C := C) (yb := yb) (yc := yc) (σ g) (act g)
    rw [hcross g] at hd
    rw [OM.NNN11.card_eq_change_fintypes hd]; simp [X, hm, resAB]
  have hcE (g : G) : Fintype.card (EqualSlots (σ g) (act g) → ZMod 2) =
      Fintype.card (X (d * w)) := by
    simp [X, hcross g]
  let eX := fun g => Fintype.equivOfCardEq (hcX g)
  let eY := fun g => Fintype.equivOfCardEq (hcY g)
  let eE := fun g => Fintype.equivOfCardEq (hcE g)
  let res := fun g => AB.residual3 (σ g) (act g) TA TB TC (AB.productComplement3 (act g) Q R)
  let fx : G → ((A → X xa) × (B → X xb) × (C → X xc)) → X (m 0) × X (d * w) := fun g xx =>
    (eX g (AB.reduceX3 (σ g) (act g) xx), eE g (AB.outEqualX3 (σ g) (act g) xx))
  let fy : G → ((A → X ya) × (B → X yb) × (C → X yc)) → X (m 1) × X (d * w) := fun g yy =>
    (eY g (AB.reduceY3 (σ g) (act g) yy), eE g (AB.outEqualY3 (σ g) (act g) yy))
  let W : G → Tensor ℂ (X (m 0)) (X (m 1)) ((A → X za) × (B → X zb) × (C → X zc)) :=
    fun g r s zz => α g * res g ((eX g).symm r) ((eY g).symm s) zz
  have hfam : (∑ g, α g • contract3 TA TB TC (L.kernel (u g)) Q R) = packedFamily fx fy W := by
    funext xx yy zz
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, packedFamily]
    apply Finset.sum_congr rfl
    intro g _
    have hk : L.kernel (u g) = OM.NNN11.ExtractionAB.permutationBond (σ g) := rfl
    rw [hk, AB.contract3_eq_joint (σ g) (act g)
      (OM.NNN12.Cyclic.fixed L.coordinates (u g)) TA TB TC Q R,
      AB.residual3_factorization (σ g) (act g)
      (OM.NNN12.Cyclic.stable L.coordinates (u g)) TA TB TC]
    simp only [OM.NNN11.edgeFactor, fx, fy, W, res, (eE g).injective.eq_iff,
      Equiv.symm_apply_apply]
    split_ifs <;> ring
  rw [hfam]
  have hZ : Fintype.card ((A → X za) × (B → X zb) × (C → X zc)) = 2 ^ m 2 := by
    simp only [Fintype.card_prod, Fintype.card_fun, X, ZMod.card, Fintype.card_fin, ← pow_mul,
      ← pow_add, hm, resAB, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
    ring_nf
  have hb := packed_family_bound_at φ m hc hθ hβ hβ0 hβ1 (d * w) hZ fx fy W hG
  simpa using hb

end OM.NNN20.Mix

namespace OM.NNN20.Mix
open CoordinateTensor OM.NNN.Raw OM.NNN2 OM.NNN11.Network OM.NNN11.SlotExtraction
open OM.NNN12 (Shape DyadicTensor)
open OM.NNN11.ExtractionAB (X)
open OM.NNN12.Codes
open OM.NNN18 (packOverhead packedFamily)
open Foundations.OrientationTransport

set_option maxHeartbeats 2000000

variable {A B C : Type} [Fintype A] [Fintype B] [Fintype C]
  [DecidableEq A] [DecidableEq B] [DecidableEq C]
  {q d N : ℕ} [Fact q.Prime]

/-- the residual format of a CA class of crossing weight `e` -/
def resCA (a b c xa ya za xb yb zb xc yc zc e : ℕ) : Shape :=
  ![a * xa + b * xb + c * xc - e, a * ya + b * yb + c * yc, a * za + b * zb + c * zc - e]

/-- **A CA correction class of a mixed network** (bond `1`), by the party swap `1 ↔ 2`; the parent
is needed only at the packed formats `m + (n, 0, n + 2)`. -/
theorem packedCA3_class {za xc : ℕ} (L : OM.NNN12.BondLayout q d C A za xc N) (φ : PolMul.Spectral ℂ)
    {xa ya xb yb zb yc zc : ℕ} {c : Fin 3 → ℝ} {t β : ℝ}
    (hθ : Foundations.PairUnitExponents.theta φ 1 ≤ t)
    (hβ : (t + c 0 + c 2) / 2 ≤ β) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (TA : Tensor ℂ (X xa) (X ya) (X za)) (TB : Tensor ℂ (X xb) (X yb) (X zb))
    (TC : Tensor ℂ (X xc) (X yc) (X zc))
    (P : Operator (BondAB A B (X xb) (X ya))) (Q : Operator (BondBC B C (X yc) (X zb)))
    {G : Type} [Fintype G] (u : G → Word q N) (w : ℕ) (hw : ∀ g, weight (u g) = w)
    (α : G → ℂ) (hG : 0 < Fintype.card G)
    (hc : ∀ n : ℕ, (n : ℝ) ≤ packBound (Fintype.card G) →
      ∀ U : DyadicTensor
        ![resCA (Fintype.card A) (Fintype.card B) (Fintype.card C) xa ya za xb yb zb xc yc zc
            (d * w) 0 + n,
          resCA (Fintype.card A) (Fintype.card B) (Fintype.card C) xa ya za xb yb zb xc yc zc
            (d * w) 1,
          resCA (Fintype.card A) (Fintype.card B) (Fintype.card C) xa ya za xb yb zb xc yc zc
            (d * w) 2 + n + 2],
        value φ U ≤ (2 : ℝ) ^ NNN13.plane c (fun i => ((![
          resCA (Fintype.card A) (Fintype.card B) (Fintype.card C) xa ya za xb yb zb xc yc zc
            (d * w) 0 + n,
          resCA (Fintype.card A) (Fintype.card B) (Fintype.card C) xa ya za xb yb zb xc yc zc
            (d * w) 1,
          resCA (Fintype.card A) (Fintype.card B) (Fintype.card C) xa ya za xb yb zb xc yc zc
            (d * w) 2 + n + 2] i : ℕ) : ℝ))) :
    value φ (∑ g, α g • contract3 TA TB TC P Q (L.kernel (u g))) ≤
      packOverhead (c 2) (Fintype.card G) * (Fintype.card G : ℝ) ^ β *
        (2 : ℝ) ^ (NNN13.plane c (fun i => ((resCA (Fintype.card A) (Fintype.card B)
          (Fintype.card C) xa ya za xb yb zb xc yc zc (d * w) i : ℕ) : ℝ)) + t * (d * w : ℕ)) := by
  set m := resCA (Fintype.card A) (Fintype.card B) (Fintype.card C) xa ya za xb yb zb xc yc zc
    (d * w) with hm
  let σ := fun g => OM.NNN12.Cyclic.permutation L.coordinates (u g)
  let act := fun g => OM.NNN12.Cyclic.active L.coordinates (u g)
  have hcross (g : G) : Fintype.card (EqualSlots (σ g) (act g)) = d * w := by
    rw [← hw g]; exact L.crossings (u g)
  have hcX (g : G) : Fintype.card (CA.ResidualX3 (B := B) (XA := X xa) (XB := X xb) (σ g) (act g)) =
      Fintype.card (X (m 0)) := by
    have hd := CA.residualX3_card (B := B) (xa := xa) (xb := xb) (σ g) (act g)
    rw [hcross g] at hd
    rw [OM.NNN11.card_eq_change_fintypes hd]; simp [X, hm, resCA]
  have hcZ (g : G) : Fintype.card (CA.ResidualZ3 (B := B) (ZB := X zb) (ZC := X zc) (σ g) (act g)) =
      Fintype.card (X (m 2)) := by
    have hd := CA.residualZ3_card (B := B) (zb := zb) (zc := zc) (σ g) (act g)
    rw [hcross g] at hd
    rw [OM.NNN11.card_eq_change_fintypes hd]; simp [X, hm, resCA]
  have hcE (g : G) : Fintype.card (EqualSlots (σ g) (act g) → ZMod 2) =
      Fintype.card (X (d * w)) := by
    simp [X, hcross g]
  let eX := fun g => Fintype.equivOfCardEq (hcX g)
  let eZ := fun g => Fintype.equivOfCardEq (hcZ g)
  let eE := fun g => Fintype.equivOfCardEq (hcE g)
  let res := fun g => CA.residual3 (σ g) (act g) TA TB TC (CA.productComplement3 (act g) P Q)
  let fx : G → ((A → X xa) × (B → X xb) × (C → X xc)) → X (m 0) × X (d * w) := fun g xx =>
    (eX g (CA.reduceX3 (σ g) (act g) xx), eE g (CA.outEqualX3 (σ g) (act g) xx))
  let fz : G → ((A → X za) × (B → X zb) × (C → X zc)) → X (m 2) × X (d * w) := fun g zz =>
    (eZ g (CA.reduceZ3 (σ g) (act g) zz), eE g (CA.outEqualZ3 (σ g) (act g) zz))
  let W : G → Tensor ℂ (X (m 0)) (X (m 2)) ((A → X ya) × (B → X yb) × (C → X yc)) :=
    fun g r s yy => α g * res g ((eX g).symm r) yy ((eZ g).symm s)
  have hfam : Lib.E.RectangularSpectrum.swap12
      (∑ g, α g • contract3 TA TB TC P Q (L.kernel (u g))) = packedFamily fx fz W := by
    funext xx zz yy
    simp only [Lib.E.RectangularSpectrum.swap12, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      packedFamily]
    apply Finset.sum_congr rfl
    intro g _
    have hk : L.kernel (u g) = OM.NNN11.ExtractionAB.permutationBond (σ g) := rfl
    rw [hk, CA.contract3_eq_joint (σ g) (act g)
      (OM.NNN12.Cyclic.fixed L.coordinates (u g)) TA TB TC P Q,
      CA.residual3_factorization (σ g) (act g)
      (OM.NNN12.Cyclic.stable L.coordinates (u g)) TA TB TC]
    simp only [OM.NNN11.edgeFactor, fx, fz, W, res, (eE g).injective.eq_iff,
      Equiv.symm_apply_apply]
    by_cases h : CA.outEqualZ3 (σ g) (act g) zz = CA.outEqualX3 (σ g) (act g) xx
    · simp [h]
    · simp [h, Ne.symm h]
  have hval := OM.NNN11.value_swap12 φ (∑ g, α g • contract3 TA TB TC P Q (L.kernel (u g)))
  rw [← hval, hfam]
  -- the swapped spectral point and the swapped parent
  set ψ := pullPoint φ (rot 1) with hψ
  have hθ' : Foundations.PairUnitExponents.theta ψ 2 ≤ t := by
    rw [hψ, theta_legReindex, rot_symm_two]; exact hθ
  have hβ' : (t + (![c 0, c 2, c 1] : Fin 3 → ℝ) 0 + (![c 0, c 2, c 1] : Fin 3 → ℝ) 1) / 2 ≤ β := by
    simpa using hβ
  have hc' : ∀ n : ℕ, (n : ℝ) ≤ packBound (Fintype.card G) →
      ∀ U : DyadicTensor ![(![m 0, m 2, m 1] : Shape) 0 + n, (![m 0, m 2, m 1] : Shape) 1 + n + 2,
        (![m 0, m 2, m 1] : Shape) 2],
        value ψ U ≤ (2 : ℝ) ^ NNN13.plane ![c 0, c 2, c 1] (fun i => ((![
          (![m 0, m 2, m 1] : Shape) 0 + n, (![m 0, m 2, m 1] : Shape) 1 + n + 2,
          (![m 0, m 2, m 1] : Shape) 2] i : ℕ) : ℝ)) := by
    intro n hn U
    have h := hc n hn (Lib.E.RectangularSpectrum.swap12 U)
    have he := OM.NNN11.value_swap12 φ (Lib.E.RectangularSpectrum.swap12 U)
    change value ψ U = _ at he
    rw [he]
    refine h.trans (le_of_eq ?_)
    congr 1
    simp [NNN13.plane]
    ring
  have hY : Fintype.card ((A → X ya) × (B → X yb) × (C → X yc)) = 2 ^ (![m 0, m 2, m 1] : Shape) 2 := by
    simp only [Fintype.card_prod, Fintype.card_fun, X, ZMod.card, Fintype.card_fin, ← pow_mul,
      ← pow_add, hm, resCA, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons,
      Matrix.cons_val_one, Matrix.cons_val_zero]
    ring_nf
  have hb := packed_family_bound_at ψ ![m 0, m 2, m 1] hc' hθ' hβ' hβ0 hβ1 (d * w) hY fx fz W hG
  refine hb.trans (le_of_eq ?_)
  have hpl : NNN13.plane ![c 0, c 2, c 1] (fun i => (((![m 0, m 2, m 1] : Shape) i : ℕ) : ℝ)) =
      NNN13.plane c (fun i => ((m i : ℕ) : ℝ)) := by
    simp [NNN13.plane]; ring
  simp only [Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons] at hpl ⊢
  rw [hpl]
  push_cast
  ring

end OM.NNN20.Mix
