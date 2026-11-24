import Lib.OM.NNN32.FourNetwork

/-! # Finite minimal prices for networks with four boundary observations -/

noncomputable section
open scoped Classical

namespace OM.NNN32.FourNetwork

open OM.NNN30.Net Semicontinuity AsymptoticSpectrumDuality

variable {V : Type} {τ : Fin 4 → V} {φ : AsymptoticSpectrum fourPreorder}

def value {d : Fin 4 → ℕ+} (φ : AsymptoticSpectrum fourPreorder) (N : FourNetwork V d) : ℝ :=
  AsymptoticSpectrum.eval fourPreorder (TensorClass.mk ⟨_,N.tensor⟩) φ

def Valid (φ : AsymptoticSpectrum fourPreorder) (τ : Fin 4 → V) (d : V → V → ℝ) : Prop :=
  ∀ {f} (N : FourNetwork V f), N.Local τ → 0 < value φ N →
    Real.logb 2 (value φ N) ≤ N.graph.cost d

def Minimal (φ : AsymptoticSpectrum fourPreorder) (τ : Fin 4 → V) (d : V → V → ℝ) : Prop :=
  Valid φ τ d ∧ 0 ≤ d ∧ (∀ s, d s s = 0) ∧
    ∀ d', Valid φ τ d' → 0 ≤ d' → (∀ s, d' s s = 0) → d' ≤ d → d' = d

lemma closed_valid [Fintype V] : IsClosed {d | Valid φ τ d} := by
  change IsClosed {d | ∀ f (N : FourNetwork V f), N.Local τ → 0 < value φ N →
    Real.logb 2 (value φ N) ≤ N.graph.cost d}
  simp only [Set.ofPred_forall]
  exact isClosed_iInter fun _ => isClosed_iInter fun N => isClosed_iInter fun _ =>
    isClosed_iInter fun _ => isClosed_le continuous_const (continuous_cost N.graph)

lemma exists_minimal [Fintype V] {d : V → V → ℝ} (hv : Valid φ τ d) (h0 : 0 ≤ d)
    (hs : ∀ s, d s s = 0) : ∃ e, Minimal φ τ e ∧ e ≤ d := by
  let K := Set.Icc 0 d ∩ {e | Valid φ τ e} ∩ {e | ∀ s, e s s = 0}
  have hc : IsCompact K := by
    apply (isCompact_Icc.inter_right (closed_valid (φ := φ) (τ := τ))).inter_right
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun i => isClosed_eq (by fun_prop) continuous_const
  obtain ⟨e,he,hmin⟩ := hc.exists_isMinOn ⟨d,⟨⟨h0,le_rfl⟩,hv⟩,hs⟩
    (f := fun e : V → V → ℝ => ∑ i, ∑ j, e i j)
    ((continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ =>
      (by fun_prop : Continuous fun e : V → V → ℝ => e i j)).continuousOn)
  refine ⟨e,⟨he.1.2,he.1.1.1,he.2,?_⟩,he.1.1.2⟩
  intro g hg h0g hsg hge
  have h : ∑ i, ∑ j, e i j ≤ ∑ i, ∑ j, g i j := hmin ⟨⟨⟨h0g,hge.trans he.1.1.2⟩,hg⟩,hsg⟩
  have hr i : ∑ j, g i j ≤ ∑ j, e i j := Finset.sum_le_sum fun j _ => hge i j
  have heq := (Finset.sum_eq_sum_iff_of_le fun i _ => hr i).1
    (le_antisymm (Finset.sum_le_sum fun i _ => hr i) h)
  funext i j
  exact (Finset.sum_eq_sum_iff_of_le fun j _ => hge i j).1
    (heq i (Finset.mem_univ _)) j (Finset.mem_univ _)

/-- Replacing one ordered price by the cost of a valid routing cannot decrease
it at a minimal vector. -/
lemma coordinate_le {d : V → V → ℝ} (hd : Minimal φ τ d) (s t : V) (b : ℝ) (hb : 0 ≤ b)
    (hv : Valid φ τ (fun x y => if x=s ∧ y=t then b else d x y)) : d s t ≤ b := by
  by_contra! h
  let e (x y : V) := if x=s ∧ y=t then b else d x y
  have hne : s ≠ t := by rintro rfl; rw [hd.2.2.1] at h; linarith
  have heq := hd.2.2.2 e hv
    (fun x y => by dsimp [e]; split_ifs <;> first | exact hb | exact hd.2.1 x y)
    (fun x => by dsimp [e]; rw [if_neg (fun H => hne (H.1.symm.trans H.2)),hd.2.2.1])
    (fun x y => by
      dsimp [e]
      split_ifs with H
      · simpa [H.1,H.2] using h.le
      · exact le_rfl)
  have := congrFun (congrFun heq s) t
  simp [e] at this
  linarith

lemma Minimal.symm {d : V → V → ℝ} (hd : Minimal φ τ d) (s t : V) : d s t = d t s := by
  have le (s t : V) : d s t ≤ d t s := by
    apply coordinate_le hd _ _ _ (hd.2.1 _ _)
    intro f N hl hv
    let P (k : N.graph.K) := N.graph.e1 k=s ∧ N.graph.e2 k=t
    have he : value φ (N.rev P) = value φ N := by simp [value,tensor_rev]
    have h := hd.1 (N.rev P) (hl.rev P) (he ▸ hv)
    rw [he] at h
    apply h.trans_eq
    rw [show (N.rev P).graph = N.graph.rev P by rfl,TN.cost_rev]
    apply Finset.sum_congr rfl
    intro k _
    by_cases H : P k
    · simp [packed,H,P,H.1,H.2]
    · change ¬(_ ∧ _) at H
      simp [packed,P,H]
  exact le_antisymm (le s t) (le t s)

lemma Minimal.triangle {d : V → V → ℝ} (hd : Minimal φ τ d) (s t u : V) :
    d s u ≤ d s t + d t u := by
  apply coordinate_le hd _ _ _ (add_nonneg (hd.2.1 _ _) (hd.2.1 _ _))
  intro f N hl hv
  let P (k : N.graph.K) := N.graph.e1 k=s ∧ N.graph.e2 k=u
  have he : value φ (N.reroute P t) = value φ N := by simp [value,tensor_reroute]
  have h := hd.1 (N.reroute P t) (hl.reroute P t) (he ▸ hv)
  rw [he] at h
  apply h.trans_eq
  change (N.packed.reroute P t).cost d = _
  rw [TN.cost_reroute]
  apply Finset.sum_congr rfl
  intro k _
  by_cases H : P k
  · simp [packed,H,P,H.1,H.2]
  · change ¬(_ ∧ _) at H
    simp [packed,P,H]

end OM.NNN32.FourNetwork
