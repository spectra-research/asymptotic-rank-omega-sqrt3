import Lib.OM.NNN32.FourPrices
import Lib.OM.NNN32.BondFactors
import Lib.OM.NNN30.Net.FourSites

/-! # The wire exponents give a minimal valid price at the four boundary sites -/

noncomputable section
open scoped Classical

namespace OM.NNN32

open Semicontinuity AsymptoticSpectrumDuality OM.NNN30.Net

namespace FourNetwork

private lemma not_zero {V : Type} {d : Fin 4 → ℕ+} {N : FourNetwork V d}
    {φ : AsymptoticSpectrum fourPreorder} (h : 0 < value φ N) : N.tensor ≠ 0 := by
  intro ht
  have he : TensorClass.mk ⟨_,N.tensor⟩ = (0 : TensorClass ℂ 4) := by
    rw [ht,TensorClass.zero_def]
    exact TensorClass.mk_eq_of_equiv zeroT_equiv_zero.symm
  exact (ne_of_gt h) (by simp [value,he,AsymptoticSpectrum.eval_zero])

private lemma value_prod {d : Fin 4 → ℕ+} {ι : Type} (φ : AsymptoticSpectrum fourPreorder)
    (s : Finset ι) (T : ι → KTensor ℂ d) : fourValue φ (∏ k ∈ s,T k) ≤ ∏ k ∈ s,fourValue φ (T k) := by
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty]
    have h := fourValue_mono φ (local_restricts (d := d) 0 (fun _ => 1))
    exact h.trans_eq φ.map_one
  | insert i s hi ih =>
    rw [Finset.prod_insert hi,Finset.prod_insert hi]
    exact (value_pointwise_mul _ _ _).trans (mul_le_mul_of_nonneg_left ih (φ.nonneg _))

theorem initial_valid (φ : AsymptoticSpectrum fourPreorder) :
    Valid φ id (wirePrice φ) := by
  intro d N hN hv
  let G := N.graph
  obtain ⟨u⟩ : Nonempty G.Assignment := by
    by_contra! he
    haveI : IsEmpty G.Assignment := he
    exact not_zero hv (by
      funext x
      change (∑ z : G.Assignment, _) = 0
      exact Finset.sum_of_isEmpty _)
  let fmt (s : Fin 4) : ℕ+ := ⟨Fintype.card (G.Config s),Fintype.card_pos_iff.2 ⟨G.atSite u s⟩⟩
  let idx (s : Fin 4) : G.Config s ≃ Fin (fmt s) := Fintype.equivFin _
  let e : G.Assignment ≃ ((s : Fin 4) → Fin (fmt s)) :=
    (Equiv.piCongrFiberwise (f := G.loc) (fun _ => Equiv.refl _)).trans (Equiv.piCongrRight idx)
  have e_apply (x : G.Assignment) (s) : e x s = idx s (G.atSite x s) := rfl
  let fill (s : Fin 4) (a : Fin (fmt s)) := G.fill u s ((idx s).symm a)
  have dep {s : Fin 4} {f : G.Assignment → ℂ} (hf : G.DepAt s f) (x : G.Assignment) :
      f x = f (fill s (e x s)) := by
    simpa [fill,e_apply] using hf.fill G u x
  let T (k : G.K) : KTensor ℂ fmt := fun y => G.F k (e.symm y)
  have hres : Restricts N.tensor (∏ k,T k) := by
    refine ⟨fun i b a => N.out i (fill i a) b,?_⟩
    intro a
    rw [← e.sum_comp]
    unfold tensor TN.Z
    apply Finset.sum_congr rfl
    intro x _
    simp only [packed,one_mul,mul_one,Finset.prod_apply,T,Equiv.symm_apply_apply]
    congr 1
    exact Finset.prod_congr rfl fun i _ => dep (hN.2.2 i (a i)) x
  have hpos (k : G.K) : 0 < G.r k := r_pos (not_zero hv) k
  have hterm (k : G.K) :
      fourValue φ (T k) ≤ (G.r k : ℝ) ^ wirePrice φ (G.e1 k) (G.e2 k) := by
    let i := G.e1 k
    let j := G.e2 k
    let g (a : Fin (fmt i)) (z : Fin (G.r k)) := G.g k z (fill i a)
    let h (a : Fin (fmt j)) (z : Fin (G.r k)) := G.h k z (fill j a)
    have he : T k = fun y => ∑ z, g (y i) z * h (y j) z := by
      funext y
      apply Finset.sum_congr rfl
      intro z _
      have hg := dep (hN.1 k z) (e.symm y)
      have hh := dep (hN.2.1 k z) (e.symm y)
      simpa only [Equiv.apply_symm_apply] using congrArg₂ (· * ·) hg hh
    change _ ≤ (G.r k : ℝ)^wirePrice φ i j
    rw [he]
    by_cases hij : i=j
    · rw [show wirePrice φ i j = 0 from hij ▸ wirePrice_self φ j,Real.rpow_zero]
      have hh (x : (s : Fin 4) → Fin (fmt s)) : x i = Fin.cast (congrArg (fun s => (fmt s : ℕ)) hij.symm) (x j) := by
        exact Fin.ext (congrArg (fun s => (x s).val) hij)
      let atJ (a : Fin (fmt j)) := ∑ z, g (Fin.cast (congrArg (fun s => (fmt s : ℕ)) hij.symm) a) z * h a z
      have eqn : (fun x : (s : Fin 4) → Fin (fmt s) => ∑ z, g (x i) z * h (x j) z) =
          fun x => atJ (x j) := by funext x; rw [hh x]
      rw [eqn]
      exact (fourValue_mono φ (local_restricts j atJ)).trans_eq φ.map_one
    · let r : ℕ+ := ⟨G.r k,hpos k⟩
      exact (fourValue_mono φ (bond_restricts r hij g h)).trans_eq
        (eval_wire φ r i j hij)
  have hu : value φ N ≤ ∏ k, (G.r k : ℝ)^wirePrice φ (G.e1 k) (G.e2 k) :=
    (fourValue_mono φ hres).trans ((value_prod φ _ _).trans
      (Finset.prod_le_prod₀ (fun _ _ => φ.nonneg _) (fun k _ => hterm k)))
  have hlog := Real.logb_le_logb_of_le (by norm_num : (1:ℝ) < 2) hv hu
  rw [Real.logb_prod _ _ (fun k _ => (Real.rpow_pos_of_pos (Nat.cast_pos.2 (hpos k)) _).ne')] at hlog
  simpa only [TN.cost,Real.logb_rpow_eq_mul_logb_of_pos (Nat.cast_pos.2 (hpos _))] using hlog

/-- A single binary bond, read at all four boundary sites. -/
private def testWire (i j : Fin 4) : FourNetwork (Fin 4) (naturalPairFormat 2 i j) where
  graph := {
    V := Fin 4
    T := fun a => Fin (naturalPairFormat 2 i j a)
    loc := id
    K := Unit
    e1 := fun _ => i
    e2 := fun _ => j
    r := fun _ => 2
    g := fun _ z x => if (x i).val = z.val then 1 else 0
    h := fun _ z x => if (x j).val = z.val then 1 else 0
    out0 := fun _ _ => 1
    out1 := fun _ _ => 1
    out2 := fun _ _ => 1 }
  out a x y := if y = x a then 1 else 0

private lemma testWire_local (i j : Fin 4) : (testWire i j).Local id := by
  constructor
  · intro k z x y h
    change (if (x i).val = z.val then (1:ℂ) else 0) = _
    rw [h i rfl]; rfl
  constructor
  · intro k z x y h
    change (if (x j).val = z.val then (1:ℂ) else 0) = _
    rw [h j rfl]; rfl
  · intro a b x y h
    change (if b=x a then (1:ℂ) else 0) = _
    rw [h a rfl]; rfl

private lemma testWire_tensor {i j : Fin 4} (hij : i ≠ j) :
    (testWire i j).tensor = unitPairTensor (F := ℂ) 2 i j hij := by
  funext a
  simp only [tensor,packed,testWire,TN.Z,TN.F,mul_one,Fintype.prod_unique]
  rw [Finset.sum_eq_single a]
  · simp only [ite_true,Finset.prod_const_one,one_mul]
    let z : Fin 2 := ⟨(a i).val,by simpa [naturalPairFormat] using (a i).isLt⟩
    rw [Finset.sum_eq_single z]
    · simp [z,unitPairTensor,eq_comm]
    · intro w _ hw
      have hn : (a i).val ≠ w.val := fun e => hw (Fin.ext e.symm)
      simp [hn]
    · simp
  · intro x _ hx
    have hn : ∃ b, a b ≠ x b := by
      by_contra! he
      exact hx (funext he).symm
    obtain ⟨b,hb⟩ := hn
    rw [Finset.prod_eq_zero (Finset.mem_univ b) (if_neg hb)]
    simp
  · simp

theorem initial_minimal (φ : AsymptoticSpectrum fourPreorder) : Minimal φ id (wirePrice φ) := by
  refine ⟨initial_valid φ,wirePrice_nonneg φ,wirePrice_self φ,?_⟩
  intro d hv _ hs hle
  funext i j
  apply le_antisymm (hle i j)
  by_cases hij : i=j
  · subst j
    rw [wirePrice_self,hs]
  let N := testWire i j
  have hw : value φ N = (2:ℝ)^wirePrice φ i j := by
    simpa [value,N,testWire_tensor hij,wire] using eval_wire φ 2 i j hij
  have h := hv N (testWire_local i j) (hw ▸ Real.rpow_pos_of_pos (by norm_num) _)
  rw [hw,Real.logb_rpow (by norm_num) (by norm_num)] at h
  simpa [N,testWire,TN.cost,Real.logb_self_eq_one (by norm_num : (1:ℝ)<2)] using h

end FourNetwork

end OM.NNN32
