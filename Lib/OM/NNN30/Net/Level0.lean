import Lib.OM.NNN30.Net.FourSites
import Lib.OM.NNN30.Net.FormatPrice
import Lib.OM.NNN30.Net.Support

/-! # Initial admissible prices at the terminals and the centre -/

noncomputable section
open scoped BigOperators Classical

namespace OM.NNN30.Net

open CoordinateTensor OM.NNN.Raw OM.NNN22 Foundations.PairUnitExponents

/-- Pair-unit prices between terminals and supporting prices on the three spokes. -/
def initialPrice (φ : OM.PolMul.Spectral ℂ) (h : Fin 3 → ℝ) : Fin 4 → Fin 4 → ℝ :=
  ![![0, theta φ 2, theta φ 1, h 0], ![theta φ 2, 0, theta φ 0, h 1],
    ![theta φ 1, theta φ 0, 0, h 2], ![h 0, h 1, h 2, 0]]

namespace TN

variable {O₀ O₁ O₂ : Type} [Fintype O₀] [Fintype O₁] [Fintype O₂]
variable {φ : OM.PolMul.Spectral ℂ} (N : TN (Fin 4) O₀ O₁ O₂)

lemma label_nonempty (hv : 0 < value φ N.Z) (s t : Fin 4) : Nonempty (N.Label s t) :=
  ⟨fun k => ⟨0, N.r_pos_of_value hv k.val⟩⟩

lemma bits_label (hv : 0 < value φ N.Z) (s t : Fin 4) : bits (N.Label s t) = N.wid s t := by
  rw [bits, Fintype.card_pi]
  simp only [Fintype.card_fin, Nat.cast_prod]
  rw [Real.logb_prod _ _ (fun k _ => by exact_mod_cast (N.r_pos_of_value hv k.val).ne')]
  unfold TN.wid
  simp_rw [← Prod.mk.injEq]
  rw [← Finset.sum_filter]
  exact (Finset.sum_subtype _ (fun k => by simp) (fun k => Real.logb 2 (N.r k))).symm

lemma bits_bond (hv : 0 < value φ N.Z) (s t : Fin 4) :
    bits (N.BondIndex s t) = N.wid s t + N.wid t s := by
  have := N.label_nonempty hv s t
  have := N.label_nonempty hv t s
  rw [← N.bits_label hv, ← N.bits_label hv]
  unfold bits
  rw [Fintype.card_prod, Nat.cast_mul, Real.logb_mul] <;> positivity

lemma initial_cost (hv : 0 < value φ N.Z) (h : Fin 3 → ℝ) :
    N.cost (initialPrice φ h) = (∑ i : Fin 3, h i * bits (N.BondIndex i.castSucc 3)) +
      theta φ 2 * bits (N.BondIndex 0 1) + theta φ 1 * bits (N.BondIndex 0 2) +
      theta φ 0 * bits (N.BondIndex 1 2) := by
  rw [TN.cost_eq_wid]
  simp [Fin.sum_univ_four, Fin.sum_univ_three, initialPrice, N.bits_bond hv]
  ring

lemma initial_bound (h : Fin 3 → ℝ) (hn : ∀ i, 0 ≤ h i)
    (hs : ∀ y : Fin 3 → ℝ, (∀ i, 0 ≤ y i) → Fv φ y ≤ ∑ i, h i * y i)
    (hN : N.Local Fin.castSucc) (hv : 0 < value φ N.Z) :
    Real.logb 2 (value φ N.Z) ≤ N.cost (initialPrice φ h) + ∑ i, h i := by
  cases isEmpty_or_nonempty N.Assignment with
  | inl he =>
    have hz : N.Z = 0 := by funext a b c; exact Finset.sum_of_isEmpty _
    rw [hz, value_zero] at hv
    exact (lt_irrefl _ hv).elim
  | inr he =>
    let u := Classical.choice he
    let cfgNE (s : Fin 4) : Nonempty (N.Config s) := ⟨N.atSite u s⟩
    let labelNE (s t : Fin 4) : Nonempty (N.Label s t) := N.label_nonempty hv s t
    let I := fun (i : Fin 3) => N.BondIndex i.castSucc 3
    have hhub := cost_hub φ h hn hs I (N.hub u)
    have hstar : value φ (N.starTensor u) ≤ (2 : ℝ) ^ ((∑ i, h i * bits (I i)) + ∑ i, h i) := by
      rw [N.starTensor_eq_map]
      exact (value_map_le φ _ _ _ _).trans hhub
    have e01 := cost_pair01 (C := N.Config 2) φ (N.leftEnd u 0 1) (N.rightEnd u 0 1)
    have e02 := cost_pair02 (B := N.Config 1) φ (N.leftEnd u 0 2) (N.rightEnd u 0 2)
    have e12 := cost_pair12 (A := N.Config 0) φ (N.leftEnd u 1 2) (N.rightEnd u 1 2)
    simp_rw [← N.edge_eq] at e01 e02 e12
    have hterm := cost_pointwise φ (cost_pointwise φ (cost_pointwise φ hstar e01) e02) e12
    apply (Real.logb_le_iff_le_rpow (by norm_num) hv).2
    rw [N.Z_four_sites u hN]
    apply (value_map_le φ _ _ _ _).trans
    apply hterm.trans_eq
    rw [N.initial_cost hv]
    congr 1
    dsimp only [I]
    ring

end TN

/-- Tensor powers remove the constant cost of rounding the three central index sizes. -/
theorem initial_admissible (φ : OM.PolMul.Spectral ℂ) (h : Fin 3 → ℝ) (hn : ∀ i, 0 ≤ h i)
    (hs : ∀ y : Fin 3 → ℝ, (∀ i, 0 ≤ y i) → Fv φ y ≤ ∑ i, h i * y i) :
    Adm φ Fin.castSucc (initialPrice φ h) := by
  intro O₀ O₁ O₂ _ _ _ N hN hv
  by_contra! hlt
  have hgap := sub_pos.mpr hlt
  obtain ⟨n, hn'⟩ := exists_nat_gt ((∑ i, h i) / (Real.logb 2 (value φ N.Z) - N.cost (initialPrice φ h)))
  have hh := (div_lt_iff₀ hgap).mp hn'
  have hp : 0 < value φ (N.pow n).Z := by rw [value_pow φ N hv]; exact pow_pos hv _
  have hc := (N.pow n).initial_bound h hn hs (hN.pow n) hp
  rw [value_pow φ N hv, Real.logb_pow, TN.cost_pow] at hc
  linarith only [hc, hh]

theorem initial_minimal (φ : OM.PolMul.Spectral ℂ) :
    ∃ d : Fin 4 → Fin 4 → ℝ, MinAdm φ Fin.castSucc d ∧
      d 3 0 + d 3 1 + d 3 2 ≤ P2M.R88.Fv φ (fun _ => 1) ∧
      d 1 2 ≤ theta φ 0 ∧ d 0 2 ≤ theta φ 1 ∧ d 0 1 ≤ theta φ 2 := by
  obtain ⟨h, hn, hsum, hs⟩ := supporting_prices φ
  obtain ⟨d, hd, hle⟩ := exists_minAdm (initial_admissible φ h hn hs)
    (fun s t => by fin_cases s <;> fin_cases t <;> first | exact le_rfl | exact hn _ | exact theta_nonneg φ _)
    (fun s => by fin_cases s <;> rfl)
  refine ⟨d, hd, ?_, hle 1 2, hle 0 2, hle 0 1⟩
  rw [← hsum, Fin.sum_univ_three]
  exact add_le_add (add_le_add (hle 3 0) (hle 3 1)) (hle 3 2)

end OM.NNN30.Net
