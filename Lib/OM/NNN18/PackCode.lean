import Lib.OM.NNN12.Moments
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.Convex.Jensen

/-!
For a linear code `F_q^r → F_q^N`, group the nonzero messages by the weight of their code word:
`K_w = #{c ≠ 0 : wt(code c) = w}`.  A packed correction family of weight `w` costs `K_w^β` times
the price of one word (T1-T5), so the total is `Σ_w K_w^β 2^{D w}`.  Averaging over **all**
generator maps and Jensen's inequality for the concave `x ↦ x^β` (`0 < β ≤ 1`) give a code with

  `Σ_w K_w^β 2^{D w} ≤ (N+1)^{1-β} ((q^r - 1)/q^N · (1 + (q-1) 2^{D/β})^N)^β`.

No probabilistic statement is used: the average is an exact finite sum (`NNN8.sum_generator_image`).
-/

noncomputable section
open scoped BigOperators Classical
namespace OM.NNN18
open OM.NNN12 OM.NNN12.Codes

/-- Power mean: `Σ_{i∈s} a_i^β ≤ #s^{1-β} (Σ_{i∈s} a_i)^β` for `a ≥ 0`, `0 ≤ β ≤ 1`. -/
theorem sum_rpow_le_card {ι : Type} (s : Finset ι) (a : ι → ℝ) (ha : ∀ i ∈ s, 0 ≤ a i)
    {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) :
    ∑ i ∈ s, a i ^ β ≤ (s.card : ℝ) ^ (1 - β) * (∑ i ∈ s, a i) ^ β := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp only [Finset.sum_empty, Finset.card_empty, Nat.cast_zero]
    exact mul_nonneg (Real.rpow_nonneg le_rfl _) (Real.rpow_nonneg le_rfl _)
  have hn : (0 : ℝ) < s.card := by exact_mod_cast hs.card_pos
  have hw : ∑ _i ∈ s, (1 / (s.card : ℝ)) = 1 := by
    rw [Finset.sum_const, nsmul_eq_mul]; field_simp
  have hJ := (Real.concaveOn_rpow hβ0 hβ1).le_map_sum (t := s)
    (w := fun _ => 1 / (s.card : ℝ)) (p := a) (fun i _ => by positivity) hw
    (fun i hi => Set.mem_Ici.2 (ha i hi))
  simp only [smul_eq_mul] at hJ
  rw [← Finset.mul_sum, ← Finset.mul_sum,
    Real.mul_rpow (by positivity) (Finset.sum_nonneg ha)] at hJ
  have hS : 0 ≤ (∑ i ∈ s, a i) ^ β := Real.rpow_nonneg (Finset.sum_nonneg ha) _
  have he : (s.card : ℝ) ^ (1 - β) = s.card * (1 / (s.card : ℝ)) ^ β := by
    rw [Real.rpow_sub hn, Real.rpow_one, Real.div_rpow (by norm_num) hn.le, Real.one_rpow]
    ring
  rw [he]
  have := mul_le_mul_of_nonneg_left hJ hn.le
  calc ∑ i ∈ s, a i ^ β = s.card * (1 / (s.card : ℝ) * ∑ i ∈ s, a i ^ β) := by
        field_simp
    _ ≤ _ := by linarith

variable {q : ℕ} [Fact q.Prime]

/-- The number of nonzero messages whose code word has weight `w`. -/
def classCount {N r : ℕ} (code : Word q r →ₗ[ZMod q] Word q N) (w : ℕ) : ℕ :=
  ((Finset.univ.erase (0 : Word q r)).filter (fun c => weight (code c) = w)).card

lemma sum_classCount {N r : ℕ} (code : Word q r →ₗ[ZMod q] Word q N) (f : ℕ → ℝ) :
    ∑ w ∈ Finset.range (N + 1), (classCount code w : ℝ) * f w =
      ∑ c ∈ Finset.univ.erase (0 : Word q r), f (weight (code c)) := by
  have h := Finset.sum_fiberwise_of_maps_to (s := Finset.univ.erase (0 : Word q r))
    (t := Finset.range (N + 1)) (g := fun c => weight (code c))
    (fun c _ => Finset.mem_range.2 (Nat.lt_succ_of_le (weight_le _)))
    (fun c => f (weight (code c)))
  rw [← h]
  apply Finset.sum_congr rfl
  intro w _
  rw [Finset.sum_congr rfl (fun c hc => by rw [(Finset.mem_filter.1 hc).2])]
  simp [classCount]

section Average
variable {V W : Type} [AddCommGroup V] [Module (ZMod q) V] [AddCommGroup W] [Module (ZMod q) W]
  [Fintype V] [Fintype W]

local instance instFintypeLinPack : Fintype (V →ₗ[ZMod q] W) :=
  Fintype.ofInjective DFunLike.coe DFunLike.coe_injective

/-- Exact average over all generator maps of a nonzero-message sum. -/
lemma sum_generators [DecidableEq V] (w : W → ℝ) :
    (∑ f : V →ₗ[ZMod q] W, ∑ v ∈ Finset.univ.erase (0 : V), w (f v)) =
      (Fintype.card (V →ₗ[ZMod q] W) : ℝ) *
        (((Fintype.card V : ℝ) - 1) / Fintype.card W * ∑ y, w y) := by
  have hnW : (0 : ℝ) < Fintype.card W := Nat.cast_pos.mpr Fintype.card_pos
  rw [Finset.sum_comm]
  have he (v : V) (hv : v ∈ Finset.univ.erase (0 : V)) :
      (∑ f : V →ₗ[ZMod q] W, w (f v)) =
        (Fintype.card (V →ₗ[ZMod q] W) : ℝ) * (∑ y, w y) / Fintype.card W := by
    rw [eq_div_iff hnW.ne']
    exact NNN8.sum_generator_image (K := ZMod q) (Finset.mem_erase.mp hv).1 w
  rw [Finset.sum_congr rfl he]
  simp only [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ (0 : V)),
    Finset.card_univ, nsmul_eq_mul, Nat.cast_sub (Fintype.card_pos : 0 < Fintype.card V),
    Nat.cast_one]
  field_simp

end Average

/-- **Fractional code moment** (LABEL_PACKING (19)): one generator map controls the packed
correction total of all weight classes. -/
theorem exists_generator_packed (N r : ℕ) (D β : ℝ) (hβ0 : 0 < β) (hβ1 : β ≤ 1) :
    ∃ code : Word q r →ₗ[ZMod q] Word q N,
      ∑ w ∈ Finset.range (N + 1), (classCount code w : ℝ) ^ β * (2 : ℝ) ^ (D * w) ≤
        ((N + 1 : ℕ) : ℝ) ^ (1 - β) *
          (((q : ℝ) ^ r - 1) / (q : ℝ) ^ N * (1 + (q - 1 : ℝ) * (2 : ℝ) ^ (D / β)) ^ N) ^ β := by
  letI : Fintype (Word q r →ₗ[ZMod q] Word q N) := instFintypeLinPack
  set G := Fintype.card (Word q r →ₗ[ZMod q] Word q N)
  have hG : (0 : ℝ) < G := Nat.cast_pos.mpr Fintype.card_pos
  set M := ((q : ℝ) ^ r - 1) / (q : ℝ) ^ N * (1 + (q - 1 : ℝ) * (2 : ℝ) ^ (D / β)) ^ N
  -- the cost of one code, rewritten as a sum of `β`-th powers
  let a : (Word q r →ₗ[ZMod q] Word q N) × ℕ → ℝ :=
    fun fw => (classCount fw.1 fw.2 : ℝ) * (2 : ℝ) ^ (D / β * fw.2)
  have ha : ∀ fw, 0 ≤ a fw := fun fw => by positivity
  have hpow (f : Word q r →ₗ[ZMod q] Word q N) (w : ℕ) :
      (classCount f w : ℝ) ^ β * (2 : ℝ) ^ (D * w) = a (f, w) ^ β := by
    simp only [a]
    rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul (by norm_num)]
    congr 2
    field_simp
  let s := (Finset.univ : Finset (Word q r →ₗ[ZMod q] Word q N)) ×ˢ Finset.range (N + 1)
  have hmean := sum_rpow_le_card s a (fun fw _ => ha fw) hβ0.le hβ1
  rw [Finset.sum_product] at hmean
  simp only [← hpow] at hmean
  -- the linear sum is the exact generator average
  have hlin : (∑ fw ∈ s, a fw) = G * M := by
    rw [Finset.sum_product]
    have h1 (f : Word q r →ₗ[ZMod q] Word q N) :
        (∑ w ∈ Finset.range (N + 1), a (f, w)) =
          ∑ c ∈ Finset.univ.erase (0 : Word q r), ((2 : ℝ) ^ (D / β)) ^ weight (f c) := by
      simp only [a]
      rw [sum_classCount f (fun w => (2 : ℝ) ^ (D / β * w))]
      apply Finset.sum_congr rfl
      intro c _
      rw [Real.rpow_mul (by norm_num), Real.rpow_natCast]
    simp only [h1]
    have hs := sum_generators (q := q) (V := Word q r) (W := Word q N)
      (fun y : Word q N => ((2 : ℝ) ^ (D / β)) ^ weight y)
    rw [sum_weights, word_card, word_card] at hs
    refine hs.trans ?_
    simp only [M, G, Nat.cast_pow]
  have hcard : (s.card : ℝ) = G * (N + 1 : ℕ) := by
    simp [s, Finset.card_product, G]
  rw [hlin, hcard] at hmean
  have hM : 0 ≤ M := by
    have h1 : (1 : ℝ) ≤ (q : ℝ) ^ r := one_le_pow₀ alphabet_one_le
    have h2 : 0 ≤ (q - 1 : ℝ) := sub_nonneg.mpr alphabet_one_le
    have := alphabet_pos (q := q)
    simp only [M]
    apply mul_nonneg (div_nonneg (by linarith) (by positivity))
    positivity
  have hbound : (∑ f : Word q r →ₗ[ZMod q] Word q N,
      ∑ w ∈ Finset.range (N + 1), (classCount f w : ℝ) ^ β * (2 : ℝ) ^ (D * w)) ≤
      ∑ _f : Word q r →ₗ[ZMod q] Word q N, ((N + 1 : ℕ) : ℝ) ^ (1 - β) * M ^ β := by
    refine hmean.trans (le_of_eq ?_)
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      Real.mul_rpow hG.le (by positivity), Real.mul_rpow hG.le hM]
    have hGG : (G : ℝ) ^ (1 - β) * (G : ℝ) ^ β = G := by
      rw [← Real.rpow_add hG]; simp
    calc (G : ℝ) ^ (1 - β) * ((N + 1 : ℕ) : ℝ) ^ (1 - β) * ((G : ℝ) ^ β * M ^ β)
        = ((G : ℝ) ^ (1 - β) * (G : ℝ) ^ β) * (((N + 1 : ℕ) : ℝ) ^ (1 - β) * M ^ β) := by ring
      _ = _ := by rw [hGG]
  obtain ⟨f, _, hf⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty hbound
  exact ⟨f, hf⟩

end OM.NNN18
