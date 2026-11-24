import Lib.OM.NNN20.Mix.Packed
import Lib.OM.NNN22.F

/-! # The three labels of a packed correction class

A correction class of `K` code words of one weight is NNN.18's `packedFamily fx fy W`: residuals
`W g` of a common format with an extracted equality on `E` between parties 0 and 1. It is priced
under one of three labels, each with an arbitrary bound `2^G` of the residual tensors at the
packed format (in the network: the true `F` there):

* **ind** (`packed_ind`): `K` times one residual, `≤ K |E|^{θ₂} 2^G`;
* **tri** (`packed_tri`): NNN.18's triangle packing, the residual at `m + (n, n + 2, 0)` with
  `n ≤ packBound K = log₂ K / 2 + O(√log K)`, `≤ 2^{θ₂ (e + 1 + packBound K) + G}`;
* **dbl** (`packed_dbl`): the word itself as a label at both ends of the bond
  (`dblResidual`, a restriction, `dbl_restricts`), the residual at `m + (c, c, 0)` with
  `K ≤ 2^c`, `≤ 2^{θ₂ e + G}`.

The three labels have costs `κ, θκ/2, 0` and offsets `0, κ/2, κ`, respectively,
where `κ = log₂ K` per unit. -/

noncomputable section
open scoped BigOperators Classical
namespace OM.NNN22.NE
open CoordinateTensor OM.NNN.Raw OM.NNN2
open OM.NNN12 (Shape DyadicTensor)
open OM.NNN11.ExtractionAB (X)
open OM.NNN18 (packedFamily packedResidual)
open OM.NNN20.Mix (packBound value_le_of_card_le_at)

variable {G OA OB Z R Q E : Type} [Fintype G] [Fintype OA] [Fintype OB] [Fintype Z]
  [Fintype R] [Fintype Q] [Fintype E]

/-- one term of a packed family is a restriction of the edge factor of its residual -/
lemma value_term_le [Nonempty R] [Nonempty Q] [Nonempty Z] [Nonempty E] (φ : PolMul.Spectral ℂ)
    (fx : OA → R × E) (fy : OB → Q × E) (W : Tensor ℂ R Q Z) :
    value φ (fun xx yy zz => NNN11.edgeFactor (E := E) W (fx xx) (fy yy) zz : Tensor ℂ OA OB Z) ≤
      value φ W * (Fintype.card E : ℝ) ^ Foundations.PairUnitExponents.theta φ 2 := by
  rw [← NNN11.value_edgeFactor (E := E) φ W]
  have h := OM.NNN18.mapTensor_indicator fx fy (fun z : Z => z) (NNN11.edgeFactor (E := E) W)
  rw [← h]
  exact value_map_le φ _ _ _ _

/-- **The ind label**: `K` residuals priced one by one. -/
theorem packed_ind [Nonempty R] [Nonempty Q] [Nonempty Z] [Nonempty E] (φ : PolMul.Spectral ℂ)
    (fx : G → OA → R × E) (fy : G → OB → Q × E) (W : G → Tensor ℂ R Q Z) {V : ℝ}
    (hW : ∀ g, value φ (W g) ≤ V) :
    value φ (packedFamily fx fy W) ≤
      Fintype.card G * ((Fintype.card E : ℝ) ^ Foundations.PairUnitExponents.theta φ 2 * V) := by
  have hsum : packedFamily fx fy W =
      ∑ g, (fun xx yy zz => NNN11.edgeFactor (E := E) (W g) (fx g xx) (fy g yy) zz :
        Tensor ℂ OA OB Z) := by
    funext xx yy zz
    simp [packedFamily, Finset.sum_apply]
  rw [hsum]
  refine (OM.NNN22.value_sum_le φ Finset.univ _).trans ?_
  have hE : 0 ≤ (Fintype.card E : ℝ) ^ Foundations.PairUnitExponents.theta φ 2 := by positivity
  calc ∑ g, value φ (fun xx yy zz => NNN11.edgeFactor (E := E) (W g) (fx g xx) (fy g yy) zz :
        Tensor ℂ OA OB Z)
      ≤ ∑ _g : G, (Fintype.card E : ℝ) ^ Foundations.PairUnitExponents.theta φ 2 * V := by
        apply Finset.sum_le_sum
        intro g _
        refine (value_term_le φ (fx g) (fy g) (W g)).trans ?_
        rw [mul_comm]
        exact mul_le_mul_of_nonneg_left (hW g) hE
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- **The tri label**: NNN.18's triangle packing, with an arbitrary bound at the packed formats. -/
theorem packed_tri (φ : PolMul.Spectral ℂ) (m : Shape) {Gt : ℝ}
    (hc : ∀ n : ℕ, (n : ℝ) ≤ packBound (Fintype.card G) →
      ∀ U : DyadicTensor ![m 0 + n, m 1 + n + 2, m 2], value φ U ≤ (2 : ℝ) ^ Gt)
    (e : ℕ) (hZ : Fintype.card Z = 2 ^ m 2)
    (fx : G → OA → X (m 0) × X e) (fy : G → OB → X (m 1) × X e)
    (W : G → Tensor ℂ (X (m 0)) (X (m 1)) Z) (hG : 0 < Fintype.card G) :
    value φ (packedFamily fx fy W) ≤
      (2 : ℝ) ^ (Foundations.PairUnitExponents.theta φ 2 * (e + 1 + packBound (Fintype.card G)) + Gt) := by
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
  have hedge : (((2 ^ e * (2 * 2 ^ n) : ℕ) : ℝ)) ^ Foundations.PairUnitExponents.theta φ 2 =
      (2 : ℝ) ^ (Foundations.PairUnitExponents.theta φ 2 * (e + 1 + n)) := by
    rw [show (2 ^ e * (2 * 2 ^ n) : ℕ) = 2 ^ (e + 1 + n) by ring, Nat.cast_pow, Nat.cast_ofNat,
      ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    push_cast; ring_nf
  rw [hedge] at hv
  calc value φ (packedFamily fx fy W)
      ≤ (2 : ℝ) ^ Gt * (2 : ℝ) ^ (Foundations.PairUnitExponents.theta φ 2 * (e + 1 + n)) :=
        hv.trans (mul_le_mul_of_nonneg_right hres (by positivity))
    _ = (2 : ℝ) ^ (Foundations.PairUnitExponents.theta φ 2 * (e + 1 + n) + Gt) := by
        rw [← Real.rpow_add (by norm_num)]; ring_nf
    _ ≤ _ := by
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        have := mul_le_mul_of_nonneg_left hnB hθ0
        linarith

/-- the doubled-label residual: `W g` stored at the label `(g, g)` of the two bond parties -/
def dblResidual (W : G → Tensor ℂ R Q Z) : Tensor ℂ (R × G) (Q × G) Z :=
  fun a b z => if a.2 = b.2 then W a.2 a.1 b.1 z else 0

omit [Fintype OA] [Fintype OB] in
/-- **The dbl source**: a packed family is a restriction of the edge factor of `dblResidual`. -/
theorem dbl_restricts (fx : G → OA → R × E) (fy : G → OB → Q × E) (W : G → Tensor ℂ R Q Z) :
    Restricts (NNN11.edgeFactor (E := E) (dblResidual W)) (packedFamily fx fy W) := by
  let A : G → OA → (R × G) × E := fun g xx => (((fx g xx).1, g), (fx g xx).2)
  let Bm : G → OB → (Q × G) × E := fun g yy => (((fy g yy).1, g), (fy g yy).2)
  refine ⟨fun xx a => ∑ g, if a = A g xx then (1 : ℂ) else 0,
    fun yy b => ∑ g, if b = Bm g yy then (1 : ℂ) else 0,
    fun zz c => if zz = c then (1 : ℂ) else 0, ?_⟩
  funext xx yy zz
  simp only [mapTensor]
  set S := NNN11.edgeFactor (E := E) (dblResidual W)
  have hz : ∀ (a : (R × G) × E) (b : (Q × G) × E),
      ∑ c, (∑ g, if a = A g xx then (1 : ℂ) else 0) * (∑ g, if b = Bm g yy then (1 : ℂ) else 0) *
        (if zz = c then (1 : ℂ) else 0) * S a b c =
      (∑ g, if a = A g xx then (1 : ℂ) else 0) *
        ((∑ g, if b = Bm g yy then (1 : ℂ) else 0) * S a b zz) := by
    intro a b
    simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
      if_true]
    ring
  simp only [hz]
  calc (∑ a, ∑ b, (∑ g, if a = A g xx then (1 : ℂ) else 0) *
        ((∑ g, if b = Bm g yy then (1 : ℂ) else 0) * S a b zz))
      = ∑ a, (∑ g, if a = A g xx then (1 : ℂ) else 0) *
          ∑ b, ((∑ g, if b = Bm g yy then (1 : ℂ) else 0) * S a b zz) := by
        simp only [Finset.mul_sum]
    _ = ∑ g, ∑ b, ((∑ g, if b = Bm g yy then (1 : ℂ) else 0) * S (A g xx) b zz) :=
        OM.NNN18.sum_indicator_sum (fun g => A g xx)
          (fun a => ∑ b, ((∑ g, if b = Bm g yy then (1 : ℂ) else 0) * S a b zz))
    _ = ∑ g, ∑ g', S (A g xx) (Bm g' yy) zz := by
        apply Finset.sum_congr rfl
        intro g _
        exact OM.NNN18.sum_indicator_sum (fun g => Bm g yy) (fun b => S (A g xx) b zz)
    _ = packedFamily fx fy W xx yy zz := by
        unfold packedFamily
        apply Finset.sum_congr rfl
        intro g _
        rw [Finset.sum_eq_single g]
        · simp only [S, A, Bm, NNN11.edgeFactor, dblResidual, if_true]
        · intro g' _ hne
          simp only [S, A, Bm, NNN11.edgeFactor, dblResidual]
          rw [if_neg (Ne.symm hne)]
          simp
        · simp

/-- **The dbl label**: the residual at `m + (c, c, 0)` with `K ≤ 2^c`, no label cost. -/
theorem packed_dbl (φ : PolMul.Spectral ℂ) (m : Shape) {Gd : ℝ} (c : ℕ)
    (hK : Fintype.card G ≤ 2 ^ c)
    (hb : ∀ U : DyadicTensor ![m 0 + c, m 1 + c, m 2], value φ U ≤ (2 : ℝ) ^ Gd)
    (e : ℕ) (hZ : Fintype.card Z = 2 ^ m 2)
    (fx : G → OA → X (m 0) × X e) (fy : G → OB → X (m 1) × X e)
    (W : G → Tensor ℂ (X (m 0)) (X (m 1)) Z) (hG : 0 < Fintype.card G) :
    value φ (packedFamily fx fy W) ≤
      (2 : ℝ) ^ (Foundations.PairUnitExponents.theta φ 2 * e + Gd) := by
  have : Nonempty Z := Fintype.card_pos_iff.1 (by rw [hZ]; positivity)
  have : Nonempty G := Fintype.card_pos_iff.1 hG
  have h := value_mono φ (restricts_degenerates _ _ (dbl_restricts (E := X e) fx fy W))
  rw [NNN11.value_edgeFactor] at h
  have hres := value_le_of_card_le_at φ ![m 0 + c, m 1 + c, m 2] hb
    (I := X (m 0) × G) (J := X (m 1) × G) (K := Z)
    (by
      show Fintype.card (X (m 0) × G) ≤ 2 ^ (m 0 + c)
      rw [Fintype.card_prod]
      simp only [X, Fintype.card_fun, ZMod.card, Fintype.card_fin]
      rw [pow_add]; exact Nat.mul_le_mul_left _ hK)
    (by
      show Fintype.card (X (m 1) × G) ≤ 2 ^ (m 1 + c)
      rw [Fintype.card_prod]
      simp only [X, Fintype.card_fun, ZMod.card, Fintype.card_fin]
      rw [pow_add]; exact Nat.mul_le_mul_left _ hK)
    (by simp [hZ]) (dblResidual W)
  have hE : (Fintype.card (X e) : ℝ) ^ Foundations.PairUnitExponents.theta φ 2 =
      (2 : ℝ) ^ (Foundations.PairUnitExponents.theta φ 2 * e) := by
    rw [show Fintype.card (X e) = 2 ^ e by simp [X], Nat.cast_pow, Nat.cast_ofNat,
      ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_comm]
  rw [hE] at h
  calc value φ (packedFamily fx fy W)
      ≤ (2 : ℝ) ^ Gd * (2 : ℝ) ^ (Foundations.PairUnitExponents.theta φ 2 * e) :=
        h.trans (mul_le_mul_of_nonneg_right hres (by positivity))
    _ = _ := by rw [← Real.rpow_add (by norm_num)]; ring_nf

/-- the direction `(1, 1, 0)` of the packed offsets of a family on the edge `0 - 1` -/
def e01R : Fin 3 → ℝ := ![1, 1, 0]

lemma clog_le (K : ℕ) (hK : 0 < K) : (Nat.clog 2 K : ℝ) ≤ Real.logb 2 K + 1 := by
  rcases Nat.lt_or_ge 1 K with h1 | h1
  · have h := Nat.pow_pred_clog_lt_self (b := 2) one_lt_two h1
    have hpos : 0 < Nat.clog 2 K := Nat.clog_pos one_lt_two h1
    have hr : ((2 : ℝ) ^ ((Nat.clog 2 K - 1 : ℕ) : ℝ)) < K := by
      rw [Real.rpow_natCast]; exact_mod_cast h
    have hl : ((Nat.clog 2 K - 1 : ℕ) : ℝ) < Real.logb 2 K := by
      rw [Real.lt_logb_iff_rpow_lt one_lt_two (by exact_mod_cast hK)]; exact hr
    have : ((Nat.clog 2 K - 1 : ℕ) : ℝ) = (Nat.clog 2 K : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]; simp
    linarith
  · have hK1 : K = 1 := by omega
    subst hK1
    simp

/-- **All three labels** for a packed family at a spectral point `ψ`, priced by a monotone
function `P` of the real format that bounds every dyadic tensor (in the network: `F` at the format,
possibly with the parties permuted). -/
theorem family_bounds (ψ : PolMul.Spectral ℂ) (P : (Fin 3 → ℝ) → ℝ)
    (hPm : ∀ y y' : Fin 3 → ℝ, (∀ i, y i ≤ y' i) → P y ≤ P y')
    (hP : ∀ (x : Shape) (U : DyadicTensor x), value ψ U ≤ (2 : ℝ) ^ P (fun i => (x i : ℝ)))
    (m : Shape) (e : ℕ) (hZ : Fintype.card Z = 2 ^ m 2)
    (fx : G → OA → X (m 0) × X e) (fy : G → OB → X (m 1) × X e)
    (W : G → Tensor ℂ (X (m 0)) (X (m 1)) Z) (hG : 0 < Fintype.card G) :
    value ψ (packedFamily fx fy W) ≤ Fintype.card G *
        ((2 : ℝ) ^ (Foundations.PairUnitExponents.theta ψ 2 * e) * (2 : ℝ) ^ P (fun i => (m i : ℝ))) ∧
    value ψ (packedFamily fx fy W) ≤
      (2 : ℝ) ^ (Foundations.PairUnitExponents.theta ψ 2 * (e + 1 + packBound (Fintype.card G)) +
        P (fun i => (m i : ℝ) + (packBound (Fintype.card G) + 2) * e01R i)) ∧
    value ψ (packedFamily fx fy W) ≤
      (2 : ℝ) ^ (Foundations.PairUnitExponents.theta ψ 2 * e +
        P (fun i => (m i : ℝ) + (Real.logb 2 (Fintype.card G) + 1) * e01R i)) := by
  have : Nonempty Z := Fintype.card_pos_iff.1 (by rw [hZ]; positivity)
  have hcm : ∀ (x : Shape) {I J K : Type} [Fintype I] [Fintype J] [Fintype K],
      Fintype.card I ≤ 2 ^ x 0 → Fintype.card J ≤ 2 ^ x 1 → Fintype.card K ≤ 2 ^ x 2 →
      ∀ T : Tensor ℂ I J K, value ψ T ≤ (2 : ℝ) ^ P (fun i => (x i : ℝ)) := by
    intro x I J K _ _ _ hi hj hk T
    exact value_le_of_card_le_at ψ x (hP x) hi hj hk T
  have hE : (Fintype.card (X e) : ℝ) ^ Foundations.PairUnitExponents.theta ψ 2 =
      (2 : ℝ) ^ (Foundations.PairUnitExponents.theta ψ 2 * e) := by
    rw [show Fintype.card (X e) = 2 ^ e by simp [X], Nat.cast_pow, Nat.cast_ofNat,
      ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_comm]
  have hθ0 := (Foundations.PairUnitExponents.theta_mem_Icc ψ 2).1
  refine ⟨?_, ?_, ?_⟩
  · -- ind
    have h := packed_ind ψ fx fy W (V := (2 : ℝ) ^ P (fun i => (m i : ℝ)))
      (fun g => hcm m (by simp [X]) (by simp [X]) (by rw [hZ]) (W g))
    rwa [hE] at h
  · -- tri
    refine packed_tri ψ m (fun n hn U => ?_) e hZ fx fy W hG
    refine (hP _ U).trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) (hPm _ _ ?_))
    intro i
    fin_cases i <;> simp [e01R] <;> linarith
  · -- dbl
    refine packed_dbl ψ m (Nat.clog 2 (Fintype.card G)) (Nat.le_pow_clog one_lt_two _)
      (fun U => ?_) e hZ fx fy W hG
    have hc := clog_le (Fintype.card G) hG
    refine (hP _ U).trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) (hPm _ _ ?_))
    intro i
    fin_cases i <;> simp [e01R] <;> linarith

end OM.NNN22.NE
