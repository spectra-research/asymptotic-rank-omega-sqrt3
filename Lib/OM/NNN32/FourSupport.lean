import Lib.OM.NNN32.FourRectangles
import Lib.OM.NNN30.Net.Sandwich

/-! # The rectangle support bound for four-party network tests -/

noncomputable section
open scoped Classical

namespace OM.NNN32.FourNetwork

open OM.NNN30.Net Semicontinuity AsymptoticSpectrumDuality Filter Topology

variable {V : Type} [Fintype V] [LinearOrder V] {φ : AsymptoticSpectrum fourPreorder}
    {τ : Fin 4 → V} {d : V → V → ℝ}

def unit (V : Type) : FourNetwork V (fun _ => 1) :=
  ⟨TN.one V,fun _ _ _ => 1⟩

lemma unit_value (φ : AsymptoticSpectrum fourPreorder) (V : Type) : value φ (unit V) = 1 := by
  have hs : (unit V).tensor = unitTensor ℂ 1 := by
    rw [unitTensor_one_eq]
    funext x
    simpa [tensor,packed,unit,TN.Z,TN.one]
  exact (congrArg (fourValue φ) hs).trans φ.map_one

omit [Fintype V] [LinearOrder V] in
lemma unit_local (τ : Fin 4 → V) : (unit V).Local τ :=
  ⟨fun k => k.elim,fun k => k.elim,fun _ _ _ _ _ => rfl⟩

lemma value_kron {W : Type} {f g : Fin 4 → ℕ+} (φ : AsymptoticSpectrum fourPreorder)
    (N : FourNetwork W f) (M : FourNetwork W g) : value φ (N.kron M) = value φ N * value φ M := by
  unfold value
  rw [tensor_kron]
  exact φ.map_mul (TensorClass.mk ⟨_,N.tensor⟩) (TensorClass.mk ⟨_,M.tensor⟩)

private def observations (N : FourNetwork (V × V) f) (φ : AsymptoticSpectrum fourPreorder)
    (d : V → V → ℝ) : Dat V :=
  (Real.logb 2 (value φ N),N.packed.ndCost d,N.packed.Uw,N.packed.Vw)

private def tests (φ : AsymptoticSpectrum fourPreorder) (τ : Fin 4 → V) (d : V → V → ℝ) : AddSubmonoid (Dat V) where
  carrier := {p | ∃ f, ∃ N : FourNetwork (V × V) f, N.Local (fun i => (τ i,τ i)) ∧
    0 < value φ N ∧ p = observations N φ d}
  zero_mem' := by
    refine ⟨_,unit _,unit_local _,by rw [unit_value]; norm_num,?_⟩
    unfold observations
    rw [unit_value]
    ext R <;> simp [packed,unit,TN.ndCost,TN.Uw,TN.Vw,TN.one]
  add_mem' := by
    rintro _ _ ⟨f,M,h,hp,rfl⟩ ⟨g,N,k,hq,rfl⟩
    refine ⟨_,M.kron N,h.kron k,by rw [value_kron]; positivity,?_⟩
    have hn : (M.kron N).packed.ndCost d = M.packed.ndCost d + N.packed.ndCost d :=
      TN.ndCost_kron d M.packed N.packed
    have hu R : (M.kron N).packed.Uw R = M.packed.Uw R + N.packed.Uw R :=
      TN.Uw_kron M.packed N.packed R
    have hv R : (M.kron N).packed.Vw R = M.packed.Vw R + N.packed.Vw R :=
      TN.Vw_kron M.packed N.packed R
    ext R <;> simp [observations,value_kron,Real.logb_mul hp.ne' hq.ne',hn,hu,hv]

private lemma rpos {f : Fin 4 → ℕ+} {N : FourNetwork (V × V) f} (hp : 0 < value φ N) (k : N.graph.K) :
    0 < N.graph.r k := by
  apply N.r_pos _ k
  intro hz
  change 0 < fourValue φ N.tensor at hp
  rw [hz,fourValue_zero] at hp
  exact lt_irrefl _ hp

private lemma widths_nonneg {p : Dat V} (h : p ∈ tests φ τ d) :
    (∀ R, 0 ≤ p.2.2.1 R) ∧ ∀ R, 0 ≤ p.2.2.2 R := by
  obtain ⟨_,N,_,hp,rfl⟩ := h
  have hr k : 0 ≤ Real.logb 2 (N.packed.r k) := Real.logb_nonneg (by norm_num)
    (by exact_mod_cast rpos hp k)
  constructor <;> intro R <;> apply Finset.sum_nonneg <;> intro k _ <;>
    split_ifs <;> first | exact hr k | exact le_rfl

private theorem support (h3 : S_R108_3) (hd : Valid φ τ d) {p : Dat V} (h : p ∈ tests φ τ d) :
    p.1 ≤ HdD d p := by
  obtain ⟨f,M,hM,hp,rfl⟩ := h
  let x := observations M φ d
  have hx : x ∈ tests φ τ d := ⟨_,M,hM,hp,rfl⟩
  have hw := widths_nonneg hx
  have hall : ScaleBounds d x.1 x.2.1 x.2.2.1 x.2.2.2 := by
    intro q j hL α β hα hβ K B hB
    obtain ⟨_,N,hl,hv,he⟩ := (tests φ τ d).nsmul_mem hx (q*j)
    have hc : (q*j:ℕ) • x = observations N φ d := he
    have hu R : N.packed.Uw R = ((q*j:ℕ):ℝ) * x.2.2.1 R :=
      (congrArg (fun z : Dat V => z.2.2.1 R) hc).symm.trans (by simp [nsmul_eq_mul])
    have hw R : N.packed.Vw R = ((q*j:ℕ):ℝ) * x.2.2.2 R :=
      (congrArg (fun z : Dat V => z.2.2.2 R) hc).symm.trans (by simp [nsmul_eq_mul])
    let u (R : Rect V) : N.packed.I1 R ↪ Fin (2^(α R*j)) := dyadicEmbedding
      ⟨fun k => ⟨0,rpos hv k.1⟩⟩ _ (by
        rw [N.packed.logb_card_I1_of_pos (rpos hv),hu]
        push_cast
        nlinarith [mul_le_mul_of_nonneg_right (hα R) (Nat.cast_nonneg j)])
    let v (R : Rect V) : N.packed.I2 R ↪ Fin (2^(β R*j)) := dyadicEmbedding
      ⟨fun k => ⟨0,rpos hv k.1⟩⟩ _ (by
        rw [N.packed.logb_card_I2_of_pos (rpos hv),hw]
        push_cast
        nlinarith [mul_le_mul_of_nonneg_right (hβ R) (Nat.cast_nonneg j)])
    obtain ⟨m,hm,hb⟩ := rectangle_price N B u v hd hl hv hB
    have hval : Real.logb 2 (value φ N) = ((q*j:ℕ):ℝ) * x.1 :=
      (congrArg Prod.fst hc).symm.trans (by simp [nsmul_eq_mul])
    have hcost : N.packed.ndCost d = ((q*j:ℕ):ℝ) * x.2.1 :=
      (congrArg (fun z : Dat V => z.2.1) hc).symm.trans (by simp [nsmul_eq_mul])
    exact ⟨m,hm,by simpa only [hval,hcost] using hb⟩
  have lim : Continuous fun t : ℝ => x.2.1 +
      ∑ R, crad d R * Real.sqrt ((x.2.2.1 R+t)^2+(x.2.2.2 R+t)^2+t) := by fun_prop
  have hlim := (lim.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
  have h := ge_of_tendsto hlim (eventually_nhdsWithin_of_forall
    (fun t ht => core_t_of_scales h3 hw.1 hw.2 hall ht))
  simpa [HdD,Hd,x] using h

theorem disc_prices (h3 : S_R108_3) (hd : Valid φ τ d) :
    ∃ lam ∈ Lam V, Valid φ (fun i => (τ i,τ i)) (Dlam d lam) := by
  have hf {n : ℕ} {p : Fin n → Dat V} (hp : ∀ i, p i ∈ tests φ τ d) :
      ∃ lam ∈ Lam V, ∀ i, (p i).1 ≤ linD d lam (p i) := by
    apply finite_family_of ⟨0,fun R => by simp⟩ convex_Lam isCompact_Lam
    intro a ha
    let P := ∑ i, a i • p i
    have hU (R : Rect V) : 0 ≤ P.2.2.1 R := by
      simp only [P,Prod.fst_sum,Prod.snd_sum,Finset.sum_apply,Prod.smul_fst,Prod.smul_snd,Pi.smul_apply,smul_eq_mul]
      exact Finset.sum_nonneg fun i _ => mul_nonneg (ha.1 i) ((widths_nonneg (hp i)).1 R)
    have hW (R : Rect V) : 0 ≤ P.2.2.2 R := by
      simp only [P,Prod.fst_sum,Prod.snd_sum,Finset.sum_apply,Prod.smul_fst,Prod.smul_snd,Pi.smul_apply,smul_eq_mul]
      exact Finset.sum_nonneg fun i _ => mul_nonneg (ha.1 i) ((widths_nonneg (hp i)).2 R)
    refine ⟨fun R => nrm (P.2.2.1 R) (P.2.2.2 R),fun R => nrm_mem (hU R) (hW R),?_⟩
    apply (conv_tests_of (continuous_HdD d) (HdD_smul d) (support h3 hd) hp
      (fun q => (tests φ τ d).sum_mem (fun i _ => (tests φ τ d).nsmul_mem (hp i) (q i))) a ha.1).trans_eq
    change HdD d P = linD d _ P
    unfold linD HdD Hd
    congr 1
    exact Finset.sum_congr rfl fun R _ => by rw [nrm_spec]
  obtain ⟨lam,hl,hall⟩ := common_parameters isCompact_Lam hf
  refine ⟨lam,hl,?_⟩
  intro f N hN hv
  have hmem : observations N φ d ∈ tests φ τ d := ⟨_,N,hN,hv,rfl⟩
  have h := hall _ hmem
  rw [cost_Dlam]
  exact h

end OM.NNN32.FourNetwork
