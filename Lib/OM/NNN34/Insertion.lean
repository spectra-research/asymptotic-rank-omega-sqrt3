import Lib.OM.NNN34.RowNetwork
import Lib.OM.NNN34.Pivots
import PLATFORM.Statements.«R114.16»

/-! # The savings from inserting the two actual partition terms in marked bonds -/

noncomputable section
open scoped Classical

namespace OM.NNN34

open NNN32 FourNetwork AsymptoticSpectrumDuality Semicontinuity P2M.R114 OM.NNN30.Net

def perimeter3 {V : Type} (d : V → V → ℝ) (a b c : V) := d a b+d b c+d c a

def rowCharge {V : Type} (d : V → V → ℝ) (t ports : Fin 4 → V) (o : V) (bL bN : ℝ) :=
  (∑ i, d (t i) (ports i)) + bL*perimeter3 d (ports 0) (ports 1) o +
    bN*perimeter3 d (ports 3) (ports 2) o

private theorem row_price (insertPrice : S_R114_16) {V A B : Type} [Fintype V] [Fintype A] [Fintype B]
    {f : Fin 4 → ℕ+} {D : ℕ+} (hD : 2 ≤ D) {r s : ℕ}
    {φ : AsymptoticSpectrum fourPreorder} {τ : Fin 4 → V} {d : V → V → ℝ} (hd : Minimal φ τ d)
    (C : CutContext V f A B) (hl : C.Local τ) (p : A ↪ Index D × Fin r) (q : B ↪ Index D × Fin s)
    (ports : Fin 4 → V) (o : V) (L N : KTensor ℂ (fun _ : Fin 3 => D)) (R : Four D)
    (contract : ∀ h, R h = ∑ j, L ![h 0,h 1,j] * N ![h 3,h 2,j])
    {bL bN : ℝ} (hL : relativeCost L ≤ bL) (hN : relativeCost N ≤ bN)
    (hv : 0 < fourValue φ (C.insert p q R)) :
    Real.logb 2 (fourValue φ (C.insert p q R)) ≤ C.net.graph.cost d +
      rowCharge d C.sites ports o bL bN * Real.logb 2 (D:ℕ) +
      d (C.sites 0) (C.sites 3)*Real.logb 2 r + d (C.sites 1) (C.sites 2)*Real.logb 2 s := by
  let M := RowNetwork.network C p q ports o
  let T : Fin 2 → KTensor ℂ (fun _ : Fin 3 => D) := ![L,N]
  let sites := RowNetwork.locations ports o
  let read := RowNetwork.readIndex C p q ports o
  have eq := RowNetwork.insert_eq C p q ports o L N R contract
  have pos : 0 < fourValue φ (insertCubes M T read) := eq.symm ▸ hv
  have h := insertPrice V φ τ d hd.1 hd.2.1 hd.2.2.1 hd.symm f M
    (RowNetwork.network_local C p q ports o hl) 2 (fun _ => D) T sites read (fun _ => hD)
    (RowNetwork.read_local C p q ports o) pos
  change Real.logb 2 (fourValue φ (insertCubes M T read)) ≤ M.graph.cost d + _ at h
  rw [eq, RowNetwork.network_cost, Fin.sum_univ_two] at h
  let b := Real.logb 2 (D:ℕ)
  have hb : 0 ≤ b := Real.logb_nonneg one_lt_two (by exact_mod_cast D.pos)
  have per (a e : V) : 0 ≤ perimeter3 d a e o := add_nonneg (add_nonneg (hd.2.1 _ _) (hd.2.1 _ _)) (hd.2.1 _ _)
  change _ ≤ _ + (relativeCost L*b*perimeter3 d (ports 0) (ports 1) o +
    relativeCost N*b*perimeter3 d (ports 3) (ports 2) o) at h
  unfold rowCharge
  exact h.trans (by dsimp only [b] at *; nlinarith only [
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hL hb) (per (ports 0) (ports 1)),
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hN hb) (per (ports 3) (ports 2))])

theorem insertion_gap (insertPrice : S_R114_16) {V : Type} [Fintype V] {f : Fin 4 → ℕ+}
    {φ : AsymptoticSpectrum fourPreorder} {τ : Fin 4 → V} {d : V → V → ℝ} (hd : Minimal φ τ d)
    (M : FourNetwork V f) (hl : M.Local τ) (hp : 0 < value φ M)
    (t ports : Fin 4 → V) (o u v : V) (ht : t 0 ≠ t 1)
    {H : ℕ} (hH : 2 ≤ H) (hD : 2 ≤ partitionSide H)
    (hw₀ : Real.logb 2 (partitionSide H : ℕ) ≤ M.graph.wid (t 0) (t 3))
    (hw₁ : Real.logb 2 (partitionSide H : ℕ) ≤ M.graph.wid (t 1) (t 2))
    {bL bN K η : ℝ} (hL : relativeCost (leftFactor H) ≤ bL) (hN : relativeCost (rightFactor H) ≤ bN)
    (hK : Real.logb ((partitionSide H : ℕ) : ℝ) (NNN30.Rect.Qn (4*H-cutoff H-1)) ≤ K)
    (hrow : rowCharge d t ports o bL bN ≤ d (t 0) (t 3)+d (t 1) (t 2)-η)
    (hcol : d (t 0) u+d (t 2) u+d (t 1) v+d (t 3) v+K*d u v ≤ d (t 0) (t 3)+d (t 1) (t 2)-η) :
    η*Real.logb 2 (partitionSide H : ℕ) - (1+d (t 0) (t 3)+d (t 1) (t 2)) ≤ gap M φ d := by
  let D := partitionSide H
  let B := Real.logb 2 (D:ℕ)
  have hgt : (1 : ℝ) < (D : ℕ) := by exact_mod_cast (show 1 < (D : ℕ) from hD)
  have hB : 0 < B := Real.logb_pos one_lt_two hgt
  obtain ⟨S,split,hS⟩ : ∃ S : Four D, rowPiece H+S = crossing D ∧
      flatRank S {0,2} ≤ NNN30.Rect.Qn (4*H-cutoff H-1) := by
    have hs := proof_R114_11 H hH
    exact ⟨_,hs.1,hs.2.2.2⟩
  obtain ⟨A,E,hAE⟩ := NNN30.Net.exists_rank_factor (colMatrix S)
  let G : FactorSites V D := ⟨Equiv.swap 1 2,u,v,(colMatrix S).rank,A,E⟩
  have gker : G.kernel = S := by
    funext a
    have h := hAE (a 0,a 2) (a 1,a 3)
    change S ![a 0,a 1,a 2,a 3] = _ at h
    rw [show (![a 0,a 1,a 2,a 3] : Fin 4 → Index D) = a by funext i; fin_cases i <;> rfl] at h
    simpa [G,FactorSites.kernel,Equiv.swap_apply_def] using h.symm
  have rankBits : Real.logb 2 (G.rank : ℝ) ≤ K*B := by
    let Q := NNN30.Rect.Qn (4*H-cutoff H-1)
    have hQ : 0 < (Q : ℝ) := by exact_mod_cast NNN30.Rect.one_le_Qn _
    have hg : G.rank ≤ Q := (colMatrix_rank S).le.trans hS
    have hlog : Real.logb 2 (G.rank : ℝ) ≤ Real.logb 2 (Q : ℝ) := by
      rcases Nat.eq_zero_or_pos G.rank with h | h
      · rw [h]; simp only [Nat.cast_zero,Real.logb_zero]
        exact Real.logb_nonneg one_lt_two (by exact_mod_cast (show 1 ≤ Q from NNN30.Rect.one_le_Qn _))
      · exact Real.logb_le_logb_of_le one_lt_two (by exact_mod_cast h) (by exact_mod_cast hg)
    have base := Real.mul_logb (a := 2) (c := (Q:ℝ)) (b := ((D:ℕ):ℝ)) (by positivity) hgt.ne' (by linarith)
    exact hlog.trans (base.symm.trans_le ((mul_le_mul_of_nonneg_left hK hB.le).trans_eq (mul_comm _ _)))
  have hr := ranks_positive hp
  obtain ⟨wa,wb⟩ := M.bundle_widths t ht hr
  obtain ⟨r,⟨p⟩,hpr⟩ := NNN32.residual_embedding (M.bundle t 0) D hB (hw₀.trans_eq wa.symm)
  obtain ⟨s,⟨q⟩,hqs⟩ := NNN32.residual_embedding (M.bundle t 1) D hB (hw₁.trans_eq wb.symm)
  rw [wa] at hpr
  rw [wb] at hqs
  let C := M.context t
  have data : M.tensor = C.insert p q (rowPiece H) + (C.realize p q G).tensor := by
    rw [CutContext.realize_tensor,gker,← CutContext.insert_add,split,CutContext.insert_crossing,M.context_closed]
  have hval : value φ M ≤ fourValue φ (C.insert p q (rowPiece H)) + value φ (C.realize p q G) := by
    change fourValue φ M.tensor ≤ _
    rw [data]; exact fourValue_add _ _ _
  let leaves := d (t 0) u+d (t 2) u+d (t 1) v+d (t 3) v
  have leavesG : G.leaves d t = leaves := by
    simp [G, FactorSites.leaves, FactorSites.hub, Fin.sum_univ_four, Equiv.swap_apply_def, leaves]; ring
  let residual := d (t 0) (t 3)*Real.logb 2 r + d (t 1) (t 2)*Real.logb 2 s
  let cap := (M.unmarked t).graph.cost d + (d (t 0) (t 3)+d (t 1) (t 2)-η)*B + residual
  have costR (hv : 0 < fourValue φ (C.insert p q (rowPiece H))) :
      Real.logb 2 (fourValue φ (C.insert p q (rowPiece H))) ≤ cap := by
    have h := row_price insertPrice hD hd C (M.context_local t hl ht) p q ports o _ _ _
      (proof_R114_12 H hH).2.2 hL hN hv
    change _ ≤ (M.unmarked t).graph.cost d + rowCharge d t ports o bL bN*B + _ + _ at h
    rw [show C.sites = t from rfl] at h
    dsimp only [cap,residual]
    linarith only [h,mul_le_mul_of_nonneg_right hrow hB.le]
  have costS (hv : 0 < value φ (C.realize p q G)) : Real.logb 2 (value φ (C.realize p q G)) ≤ cap := by
    have h := hd.1 _ (C.realize_local p q G (M.context_local t hl ht)) hv
    rw [CutContext.realize_cost] at h
    change _ ≤ (M.unmarked t).graph.cost d + G.leaves d t*B + _ + _ + d u v*_ at h
    rw [leavesG, show C.sites = t from rfl] at h
    dsimp only [cap,residual,leaves] at *
    nlinarith only [h,mul_le_mul_of_nonneg_left rankBits (hd.2.1 u v),mul_le_mul_of_nonneg_right hcol hB.le]
  have bound {z : ℝ} (hz : value φ M ≤ 2*z) (price : 0 < z → Real.logb 2 z ≤ cap) :
      Real.logb 2 (value φ M) ≤ 1+cap := by
    have hz' : 0 < z := by linarith
    have h := Real.logb_le_logb_of_le one_lt_two hp hz
    rw [Real.logb_mul (by norm_num) hz'.ne', Real.logb_self_eq_one (by norm_num)] at h
    exact h.trans (by linarith [price hz'])
  have discount : Real.logb 2 (value φ M) ≤ 1+cap := by
    rcases le_total (fourValue φ (C.insert p q (rowPiece H))) (value φ (C.realize p q G)) with h|h
    · exact bound (by linarith only [h,hval]) costS
    · exact bound (by linarith only [h,hval]) costR
  have total := M.unmarked_cost t d ht hr
  unfold gap
  dsimp only [cap,residual,B,D] at discount
  linarith only [discount,total,mul_le_mul_of_nonneg_left hpr (hd.2.1 (t 0) (t 3)),
    mul_le_mul_of_nonneg_left hqs (hd.2.1 (t 1) (t 2))]

end OM.NNN34
