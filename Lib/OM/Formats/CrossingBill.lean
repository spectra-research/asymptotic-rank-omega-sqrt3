import Lib.OM.Formats.PiecePrices
import Lib.OM.NNN30.Final

/-! # The weighted crossing inequality for minimal finite prices -/

noncomputable section
open scoped Classical
namespace OM.Formats

open NNN32 NNN32.FourNetwork NNN34 NNN30.Net AsymptoticSpectrumDuality Semicontinuity Filter Topology

theorem crossing_gap {V : Type} [Fintype V] {f : Fin 4 → ℕ+}
    {φ : AsymptoticSpectrum fourPreorder} {τ : Fin 4 → V} {d : V → V → ℝ} (hd : Minimal φ τ d)
    (N : FourNetwork V f) (hl : N.Local τ) (hp : 0 < value φ N)
    (t : Fin 4 → V) (ht : t 0 ≠ t 1) {D E : ℕ+} {n : ℕ} (hn : 0 < n)
    {a b c u v κ : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hβ : 0 ≤ formatBeta a b c)
    (hu : 0 < u) (hv : 0 < v) (hua : u ≤ a) (hvb : v ≤ b)
    (hD : Real.logb 2 (D:ℕ) = n*u) (hE : Real.logb 2 (E:ℕ) = n*v)
    (hw₀ : n*u ≤ N.graph.wid (t 0) (t 3)) (hw₁ : n*v ≤ N.graph.wid (t 1) (t 2))
    {K : ℕ} (P : Fin K → Piece D E) (sum : ∀ i j k l, ∑ m, P m i j k l = if i=l ∧ j=k then 1 else 0)
    (cuts : ∀ m, P m ≠ 0 → Real.logb 2 (cutMatrix false (P m)).rank ≤ n*c ∨
      Real.logb 2 (cutMatrix true (P m)).rank ≤ n*κ)
    (l r o h k : V) :
    n*(diagonalCost d t u v - max (rowCost d t u v (formatBeta a b c) l r o) (colCost d t u v κ h k)) -
      (Real.logb 2 K + d (t 0) (t 3) + d (t 1) (t 2)) ≤ gap N φ d := by
  have hr := ranks_positive hp
  obtain ⟨wa,wb⟩ := N.bundle_widths t ht hr
  obtain ⟨r',⟨p⟩,hpr⟩ := residual_embedding (N.bundle t 0) D (hD.symm ▸ (by positivity : 0 < (n:ℝ)*u))
    (hD.trans_le (hw₀.trans_eq wa.symm))
  obtain ⟨s,⟨q⟩,hqs⟩ := residual_embedding (N.bundle t 1) E (hE.symm ▸ (by positivity : 0 < (n:ℝ)*v))
    (hE.trans_le (hw₁.trans_eq wb.symm))
  rw [wa,hD] at hpr
  rw [wb,hE] at hqs
  let C := N.context t
  let F m := TwoBonds.insert C p q (P m)
  have eqn : N.tensor = ∑ m, F m := (N.context_closed t).symm.trans (TwoBonds.sum_insert C p q P sum)
  change 0 < fourValue φ N.tensor at hp
  have nonempty : (Finset.univ : Finset (Fin K)).Nonempty := by
    by_contra! he; rw [eqn,he,Finset.sum_empty,fourValue_zero] at hp; exact lt_irrefl _ hp
  obtain ⟨m,_,hm⟩ := Finset.exists_max_image Finset.univ (fun m => fourValue φ (F m)) nonempty
  have hk : (0:ℝ) < K := by exact_mod_cast (Nat.zero_le m.val).trans_lt m.isLt
  have hsum : fourValue φ N.tensor ≤ K * fourValue φ (F m) := by
    rw [eqn]; apply (fourValue_sum _ _ _).trans
    simpa using Finset.sum_le_sum fun j hj => hm j hj
  have pos : 0 < fourValue φ (F m) := pos_of_mul_pos_right (hp.trans_le hsum) hk.le
  have ne : P m ≠ 0 := by
    intro he
    have hzero : F m = 0 := by funext z; simp [F,TwoBonds.insert,he]
    rw [hzero,fourValue_zero] at pos; exact lt_irrefl _ pos
  have H := piece_bound hd C (N.context_local t hl ht) p q (P m) ne pos hn ha hb hc hβ hua hvb hD hE
    (cuts m ne) l r o h k
  have bound := Real.logb_le_logb_of_le one_lt_two hp hsum
  rw [Real.logb_mul hk.ne' pos.ne'] at bound
  change Real.logb 2 (fourValue φ (F m)) ≤ (N.unmarked t).graph.cost d +
    _ * max (rowCost d t u v _ l r o) (colCost d t u v κ h k) +
    (d (t 0) (t 3)*_ + d (t 1) (t 2)*_) at H
  unfold gap value diagonalCost
  rw [N.unmarked_cost t d ht hr]
  nlinarith only [H,bound,mul_le_mul_of_nonneg_left hpr (hd.2.1 (t 0) (t 3)),
    mul_le_mul_of_nonneg_left hqs (hd.2.1 (t 1) (t 2))]

def bill {V : Type} (d : V → V → ℝ) (t : Fin 4 → V) (u v B κ : ℝ) (l r o h k : V) : Prop :=
  diagonalCost d t u v ≤ max (rowCost d t u v B l r o) (colCost d t u v κ h k)

theorem rational_bill {V : Type} [Fintype V] {φ : AsymptoticSpectrum fourPreorder} {τ : Fin 4 → V}
    {d : V → V → ℝ} (hd : Minimal φ τ d) (t : Fin 4 → V)
    (sep : ∀ i j, i ≠ j → 0 < d (t i) (t j)) (l r o h k : V)
    {a b c κ : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hβ : 0 ≤ formatBeta a b c)
    {A B q : ℕ} (hA : 0 < A) (hB : 0 < B) (hq : 0 < q)
    (hua : (A:ℝ)/q ≤ a) (hvb : (B:ℝ)/q ≤ b) (hκ : 0 ≤ κ)
    (hdisk : 2*(((A:ℝ)/q)^2 + ((B:ℝ)/q)^2) < c^2 + κ^2) :
    bill d t ((A:ℝ)/q) ((B:ℝ)/q) (formatBeta a b c) κ l r o h k := by
  let u := (A:ℝ)/q
  let v := (B:ℝ)/q
  let cost := diagonalCost d t u v - max (rowCost d t u v (formatBeta a b c) l r o) (colCost d t u v κ h k)
  by_contra violation
  have hcost : 0 < cost := sub_pos.mpr (lt_of_not_ge violation)
  let δ := cost/4
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hu : 0 < u := by dsimp [u]; positivity
  have hv : 0 < v := by dsimp [v]; positivity
  let z := max u v
  have hz : 0 < z := hu.trans_le (le_max_left ..)
  have ht : t 0 ≠ t 1 := by
    intro eqn; have H := sep 0 1 (by decide +kernel); rw [eqn,hd.2.2.1] at H; exact lt_irrefl _ H
  obtain ⟨_,M,hl,hp,hgap⟩ := small_gap hd (sep 0 3 (by decide +kernel)) (sep 1 2 (by decide +kernel))
    (div_pos hδ hz)
  let w := min (M.graph.wid (t 0) (t 3)) (M.graph.wid (t 1) (t 2)) / z
  have small : gap M φ d < δ*w := hgap.trans_eq (by dsimp [w]; ring)
  have hw := pos_of_mul_pos_right ((gap_nonneg hd.1 hl hp).trans_lt small) hδ.le
  have widths : w*u ≤ M.graph.wid (t 0) (t 3) ∧ w*v ≤ M.graph.wid (t 1) (t 2) := by
    have e : w*z = min (M.graph.wid (t 0) (t 3)) (M.graph.wid (t 1) (t 2)) := div_mul_cancel₀ _ hz.ne'
    exact ⟨((mul_le_mul_of_nonneg_left (le_max_left u v) hw.le).trans_eq e).trans (min_le_left ..),
      ((mul_le_mul_of_nonneg_left (le_max_right u v) hw.le).trans_eq e).trans (min_le_right ..)⟩
  obtain ⟨K,P,⟨C,hC⟩,hsum,hcuts⟩ := NNN30.proof_R108_3 A B q hA hB hq
  let ε := c^2+κ^2-2*(u^2+v^2)
  obtain ⟨j₀,hj₀⟩ := hcuts ε (sub_pos.mpr hdisk)
  have large : Tendsto (fun j : ℕ => ((q*j:ℕ):ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_id.const_mul_atTop' hq)
  let margins := d (t 0) (t 3) + d (t 1) (t 2)
  have hcount := tendsto_count hq (fun _ : Unit => |C|+1) (fun _ => by positivity)
  simp only [Fintype.sum_unique] at hcount
  obtain ⟨j, hj, h₀, hlarge, hcnt⟩ := ((eventually_ge_atTop 1).and ((eventually_ge_atTop j₀).and
    ((large.eventually_gt_atTop (w + margins/δ)).and (hcount.eventually (Iio_mem_nhds hδ))))).exists
  let n := q*j
  have hn : 0 < n := Nat.mul_pos hq hj
  have hnR : 0 < (n:ℝ) := by exact_mod_cast hn
  change w+margins/δ < (n:ℝ) at hlarge
  change Real.logb 2 ((|C|+1)*((n:ℝ)+1)^2)/(n:ℝ) < δ at hcnt
  have hcnt' : Real.logb 2 (K j) ≤ δ*n := by
    by_cases hzK : K j = 0
    · rw [hzK,Nat.cast_zero,Real.logb_zero]; positivity
    apply (Real.logb_le_logb_of_le one_lt_two (by exact_mod_cast Nat.pos_of_ne_zero hzK) _).trans
      ((div_lt_iff₀ hnR).mp hcnt).le
    exact (hC j).trans (mul_le_mul_of_nonneg_right (by linarith [le_abs_self C]) (sq_nonneg _))
  let p := ⌈(n:ℝ)/w⌉₊
  have low : (n:ℝ) ≤ (p:ℝ)*w := (div_le_iff₀ hw).mp (Nat.le_ceil _)
  have high : (p:ℝ)*w < n+w := by
    have H := mul_lt_mul_of_pos_right (Nat.ceil_lt_add_one (div_nonneg hnR.le hw.le)) hw
    rwa [add_mul,one_mul,div_mul_cancel₀ _ hw.ne'] at H
  have hpp := pos_of_mul_pos_left (hnR.trans_le low) hw.le
  obtain ⟨_,N,hN,hpN,hgN,hw₀,hw₁⟩ := M.powered_data hl hp (t 0) (t 3) (t 1) (t 2) d p
  let bond (X : ℕ) : ℕ+ := ⟨2^(X*j),by positivity⟩
  have bits (X : ℕ) : Real.logb 2 (bond X : ℕ) = n*((X:ℝ)/q) := by
    change Real.logb 2 ((2^(X*j):ℕ):ℝ) = ((q*j:ℕ):ℝ)*_
    rw [Nat.cast_pow,Nat.cast_ofNat,Real.logb_pow,Real.logb_self_eq_one one_lt_two]
    push_cast; field_simp
  have width {x y : ℝ} (hx : 0 ≤ x) (hxy : w*x ≤ y) : (n:ℝ)*x ≤ (p:ℝ)*y :=
    (mul_le_mul_of_nonneg_right low hx).trans ((mul_assoc ..).le.trans (mul_le_mul_of_nonneg_left hxy hpp.le))
  have cuts (m) (hm : P j m ≠ 0) :
      Real.logb 2 (cutMatrix (D := bond A) (E := bond B) false (P j m)).rank ≤ n*c ∨
      Real.logb 2 (cutMatrix (D := bond A) (E := bond B) true (P j m)).rank ≤ n*κ := by
    have H := hj₀ j h₀ m hm
    let x := Real.logb 2 (cutMatrix (D := bond A) (E := bond B) false (P j m)).rank
    let y := Real.logb 2 (cutMatrix (D := bond A) (E := bond B) true (P j m)).rank
    change (x/n)^2+(y/n)^2 ≤ 2*(u^2+v^2)+ε at H
    change x ≤ n*c ∨ y ≤ n*κ
    by_contra! bad
    have hx : c < x/n := (lt_div_iff₀ hnR).mpr (by linarith only [bad.1])
    have hy : κ < y/n := (lt_div_iff₀ hnR).mpr (by linarith only [bad.2])
    dsimp only [ε] at H
    linarith only [H,pow_lt_pow_left₀ hx hc (by decide +kernel : 2 ≠ 0),pow_lt_pow_left₀ hy hκ (by decide +kernel : 2 ≠ 0)]
  have H := crossing_gap hd N hN hpN t ht hn ha hb hc hβ hu hv hua hvb (bits A) (bits B)
    (hw₀.symm ▸ width hu.le widths.1) (hw₁.symm ▸ width hv.le widths.2) (P j) (hsum j) cuts l r o h k
  change (n:ℝ)*cost - (Real.logb 2 (K j) + _ + _) ≤ _ at H
  rw [hgN] at H
  have loss := mul_lt_mul_of_pos_left small hpp
  have room : margins < ((n:ℝ)-w)*δ := (div_lt_iff₀ hδ).mp (by linarith only [hlarge])
  dsimp only [margins] at room
  linarith only [H,hcnt',room,mul_nonneg hnR.le hδ.le,show (p:ℝ)*gap M φ d < δ*((n:ℝ)+w) by
    nlinarith only [loss,mul_lt_mul_of_pos_left high hδ],show (n:ℝ)*cost = 4*((n:ℝ)*δ) by dsimp [δ]; ring]

end OM.Formats
