import Lib.OM.Formats.BondNetwork
import Lib.OM.Formats.Rates
import Lib.OM.NNN30.Net.Core
import Lib.OM.NNN32.InsertionBill
import Lib.OM.NNN34.Insertion

/-! # Cost of either flattening of a rectangular crossing piece -/

noncomputable section
open scoped Classical
namespace OM.Formats

open NNN32 NNN32.FourNetwork NNN34 NNN30.Net AsymptoticSpectrumDuality Semicontinuity Foundations.HyperbolicLift

abbrev cutMatrix {D E : ℕ+} (flip : Bool) (P : Piece D E) :=
  Matrix.of fun (i : Index D × Index E) (j : Index E × Index D) =>
    if flip then P i.1 j.1 i.2 j.2 else P i.1 i.2 j.1 j.2

lemma rank_positive {D E : ℕ+} {P : Piece D E} (hP : P ≠ 0) (flip : Bool) :
    0 < (cutMatrix flip P).rank := by
  apply rank_pos_of_ne_zero
  cases flip
  · exact rowMat_ne_zero hP
  · exact colMat_ne_zero hP

abbrev cutSize {D E : ℕ+} (flip : Bool) (P : Piece D E) (hP : P ≠ 0) : ℕ+ :=
  ⟨(cutMatrix flip P).rank, rank_positive hP flip⟩

theorem factor_piece {D E : ℕ+} (flip : Bool) (P : Piece D E) (hn : P ≠ 0) :
    let J := cutSize flip P hn
    ∃ (L : KTensor ℂ (PolMul.fmt D E J)) (R : Index J → Index E → Index D → ℂ),
      ∀ (h : Channels D E), P (h 0) (h 1) (h 2) (h 3) =
        ∑ j, L (idx3 (h 0) (if flip then h 2 else h 1) j) * R j (if flip then h 1 else h 2) (h 3) := by
  intro J
  obtain ⟨U,W,he⟩ := exists_rank_factor (cutMatrix flip P)
  refine ⟨fun i => U (i 0,i 1) (i 2),fun j i k => W j (i,k),?_⟩
  intro h
  cases flip
  · exact he (h 0,h 1) (h 2,h 3)
  · exact he (h 0,h 2) (h 1,h 3)

lemma log_rank_bits {D E J : ℕ+} (L : KTensor ℂ (PolMul.fmt D E J)) {n : ℕ} (hn : 0 < n)
    {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hβ : 0 ≤ formatBeta a b c)
    (hD : Real.logb 2 (D : ℕ) ≤ n*a) (hE : Real.logb 2 (E : ℕ) ≤ n*b)
    (hJ : Real.logb 2 (J : ℕ) ≤ n*c) :
    Real.logb 2 (asympRank L) ≤ n*formatBeta a b c := by
  rcases (asympRank_nonneg L).eq_or_lt with hzero | hpos
  · rw [← hzero,Real.logb_zero]; positivity
  let m : ℕ+ := 2^n
  have hm : 2 ≤ m := by
    change 2 ≤ (2:ℕ)^n
    exact Nat.le_self_pow hn.ne' 2
  have base : Real.logb 2 (m:ℕ) = n := by
    change Real.logb 2 ((2^n:ℕ):ℝ) = n
    rw [Nat.cast_pow,Nat.cast_ofNat,Real.logb_pow,Real.logb_self_eq_one one_lt_two,mul_one]
  have fit (X : ℕ+) (y : ℝ) (h : Real.logb 2 (X:ℕ) ≤ n*y) : ((X:ℕ):ℝ) ≤ ((m:ℕ):ℝ)^y := by
    apply (Real.logb_le_logb one_lt_two (by positivity) (Real.rpow_pos_of_pos (by positivity) _)).mp
    rw [Real.logb_rpow_eq_mul_logb_of_pos (by positivity),base,mul_comm]; exact h
  have h := log_rank_le_beta (y := ![a,b,c]) (fun i => by fin_cases i <;> assumption) L hm
    (fun i => by fin_cases i <;> first | exact fit D a hD | exact fit E b hE | exact fit J c hJ) hpos
  have e := Real.mul_logb (a := 2) (b := ((m:ℕ):ℝ)) (c := asympRank L)
    (by positivity) (cast_one_lt m hm).ne' (by linarith [cast_one_lt m hm])
  rw [base] at e
  rw [← e]
  exact mul_le_mul_of_nonneg_left h (Nat.cast_nonneg _)

def externalCost {V : Type} (d : V → V → ℝ) (t p : Fin 4 → V) (u v : ℝ) :=
  u*d (t 0) (p 0) + v*d (t 1) (p 1) + v*d (t 2) (p 2) + u*d (t 3) (p 3)

def diagonalCost {V : Type} (d : V → V → ℝ) (t : Fin 4 → V) (u v : ℝ) :=
  u*d (t 0) (t 3) + v*d (t 1) (t 2)

def rowCost {V : Type} (d : V → V → ℝ) (t : Fin 4 → V) (u v β : ℝ) (l r o : V) :=
  externalCost d t ![l,r,o,o] u v + β/2 * perimeter3 d l r o

def colCost {V : Type} (d : V → V → ℝ) (t : Fin 4 → V) (u v κ : ℝ) (l r : V) :=
  externalCost d t ![l,r,l,r] u v + κ*d l r

theorem piece_bound {V A B : Type} [Fintype V] [Fintype A] [Fintype B] {f : Fin 4 → ℕ+}
    {φ : AsymptoticSpectrum fourPreorder} {τ : Fin 4 → V} {d : V → V → ℝ} (hd : Minimal φ τ d)
    {D E : ℕ+} {r s : ℕ} (C : CutContext V f A B) (hl : C.Local τ)
    (p : A ↪ Index D × Fin r) (q : B ↪ Index E × Fin s)
    (P : Piece D E) (hn : P ≠ 0) (hv : 0 < fourValue φ (TwoBonds.insert C p q P))
    {n : ℕ} (hnat : 0 < n) {a b c u v κ : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hβ : 0 ≤ formatBeta a b c) (hu : u ≤ a) (hw : v ≤ b)
    (hD : Real.logb 2 (D:ℕ) = n*u) (hE : Real.logb 2 (E:ℕ) = n*v)
    (cut : Real.logb 2 (cutMatrix false P).rank ≤ n*c ∨ Real.logb 2 (cutMatrix true P).rank ≤ n*κ)
    (l r' o h k : V) :
    Real.logb 2 (fourValue φ (TwoBonds.insert C p q P)) ≤ C.net.graph.cost d +
      n * max (rowCost d C.sites u v (formatBeta a b c) l r' o) (colCost d C.sites u v κ h k) +
      (d (C.sites 0) (C.sites 3)*Real.logb 2 r + d (C.sites 1) (C.sites 2)*Real.logb 2 s) := by
  have charge (flip : Bool) (ports : Fin 4 → V) (w z : V) (h3 : ports 3 = z)
      (h2 : (if flip then ports 1 else ports 2) = z) :
      ∃ L : KTensor ℂ (PolMul.fmt D E (cutSize flip P hn)),
        Real.logb 2 (fourValue φ (TwoBonds.insert C p q P)) ≤
          C.net.graph.cost d + n*externalCost d C.sites ports u v +
          (d (C.sites 0) (C.sites 3)*Real.logb 2 r + d (C.sites 1) (C.sites 2)*Real.logb 2 s +
           d w z*Real.logb 2 (cutMatrix flip P).rank) +
          Real.logb 2 (asympRank L)/2 * perimeter3 d (ports 0) (if flip then ports 2 else ports 1) w := by
    obtain ⟨L,R,he⟩ := factor_piece flip P hn
    have eqn := BondNetwork.evaluate C p q flip R ports w z L P he
    have H := insert_price hd _ (BondNetwork.local_net C p q flip R ports w z hl h3 h2) L _
      (BondNetwork.read C p q flip R ports w z) (BondNetwork.read_local C p q flip R ports w z)
    dsimp only at H eqn
    rw [eqn,BondNetwork.cost,Fin.sum_univ_four] at H
    refine ⟨L,(H hv).trans_eq ?_⟩
    change _ + (_ * Real.logb 2 (D:ℕ) + _ * Real.logb 2 (E:ℕ) + _ * Real.logb 2 (E:ℕ) +
      _ * Real.logb 2 (D:ℕ)) + _ + _ = _
    rw [hD,hE]
    unfold externalCost perimeter3
    simp [BondNetwork.leftSite,cutSize]
    ring
  rcases cut with row | col
  · obtain ⟨L,H⟩ := charge false ![l,r',o,o] o o rfl rfl
    have rank := log_rank_bits L hnat ha hb hc hβ
      (hD.le.trans (mul_le_mul_of_nonneg_left hu (by positivity)))
      (hE.le.trans (mul_le_mul_of_nonneg_left hw (by positivity))) row
    change _ ≤ _ + _ + (_ + d o o * _) + _ * perimeter3 d l r' o at H
    rw [hd.2.2.1 o,zero_mul,add_zero] at H
    have per : 0 ≤ perimeter3 d l r' o := add_nonneg (add_nonneg (hd.2.1 _ _) (hd.2.1 _ _)) (hd.2.1 _ _)
    apply H.trans
    have hm := mul_le_mul_of_nonneg_left (le_max_left (rowCost d C.sites u v (formatBeta a b c) l r' o)
      (colCost d C.sites u v κ h k)) (show 0 ≤ (n:ℝ) by positivity)
    unfold rowCost at hm ⊢
    nlinarith only [hm,mul_le_mul_of_nonneg_right rank per]
  · obtain ⟨L,H⟩ := charge true ![h,k,h,k] h k rfl rfl
    change _ ≤ _ + _ + (_ + d h k * _) + _ * perimeter3 d h h h at H
    simp only [perimeter3,hd.2.2.1,add_zero,mul_zero] at H
    apply H.trans
    have hm := mul_le_mul_of_nonneg_left (le_max_right (rowCost d C.sites u v (formatBeta a b c) l r' o)
      (colCost d C.sites u v κ h k)) (show 0 ≤ (n:ℝ) by positivity)
    unfold colCost at hm ⊢
    nlinarith only [hm,mul_le_mul_of_nonneg_left col (hd.2.1 h k)]

end OM.Formats
