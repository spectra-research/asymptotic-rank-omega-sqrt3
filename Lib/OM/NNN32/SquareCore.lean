import Lib.OM.NNN32.Dyadic
import Lib.OM.NNN32.Cuts
import Lib.OM.NNN30.Net.Sandwich

/-! # The support bound from equal-width crossings on the grid -/

noncomputable section

namespace OM.NNN32

open OM.NNN30.Net OM.NNN.Raw CoordinateTensor Semicontinuity Filter Topology
open scoped Classical

/-- Equal-width dyadic expansions, with arbitrarily small overhead for counting terms. -/
def SquareExpansion (c : ℝ) : Prop :=
  ∀ η : ℝ, 0 < η → ∃ L₀ : ℕ, ∀ L ≥ L₀,
    ∃ (m : ℕ) (B : Fin m → Four ((2 : ℕ+)^L)),
      0 < m ∧ Real.logb 2 m ≤ η*L ∧ (∑ j, B j) = crossing _ ∧
      ∀ j, B j ≠ 0 → Real.logb 2 (rowMatrix (B j)).rank + Real.logb 2 (colMatrix (B j)).rank
        ≤ 2*c*L

lemma square_expansion_of_witness (h : finiteWitness) :
    ∃ c, 1 ≤ c ∧ c < Real.sqrt 2 ∧ SquareExpansion c := by
  obtain ⟨κ,hκ,m,B,hs,hm,hr⟩ := proof_R113_8.mp h
  let ε := (2*Real.sqrt 2-κ)/2
  let c := max 1 ((κ+ε)/2)
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hroot : 1 < Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
  have hc : c < Real.sqrt 2 := max_lt hroot (by dsimp [ε]; linarith)
  refine ⟨c,le_max_left _ _,hc,fun η hη => ?_⟩
  obtain ⟨L₀,hL₀⟩ := eventually_atTop.1 (((tendsto_order.1 hm).2 η hη).and (hr ε hε))
  refine ⟨max 1 L₀,fun L hL => ?_⟩
  have hp : 0 < L := (le_max_left 1 L₀).trans hL
  obtain ⟨hcount,hcut⟩ := hL₀ L ((le_max_right 1 L₀).trans hL)
  have hsum : ∑ j, B L j = crossing _ := hs L
  refine ⟨m L,B L,?_,((div_lt_iff₀ (by exact_mod_cast hp : (0:ℝ)<L)).1 hcount).le,hsum,?_⟩
  · by_contra! hm0
    have : IsEmpty (Fin (m L)) := by rw [Nat.eq_zero_of_le_zero hm0]; infer_instance
    exact crossing_ne_zero _ (hsum.symm.trans (Finset.sum_of_isEmpty _))
  · intro j hj
    rw [rowMatrix_rank,colMatrix_rank]
    refine (hcut j hj).trans (mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg L))
    linarith [le_max_right (1:ℝ) ((κ+ε)/2)]

variable {V : Type} [Fintype V] [LinearOrder V]

def maxPrice (d : V → V → ℝ) (R : Rect V) := max (d R.a R.c) (d R.b R.e)

def squareSupport (d : V → V → ℝ) (c : ℝ) (p : Dat V) : ℝ :=
  p.2.1 + ∑ R, c * maxPrice d R * max (p.2.2.1 R) (p.2.2.2 R)

private lemma embed_dyadic {ι : Type} [Fintype ι] (hp : 0 < Fintype.card ι) {L : ℕ}
    (hL : Real.logb 2 (Fintype.card ι) ≤ L) : Nonempty (ι ↪ Index ((2 : ℕ+)^L)) := by
  apply Function.Embedding.nonempty_of_card_le
  rw [Fintype.card_fin]
  have hh := (Real.logb_le_iff_le_rpow (by norm_num) (by exact_mod_cast hp : (0:ℝ)<Fintype.card ι)).1 hL
  rw [Real.rpow_natCast] at hh
  exact_mod_cast hh

private lemma weighted_cuts {a b x y t : ℝ} (ha : 0 ≤ a) (hx : 0 ≤ x)
    (hy : 0 ≤ y) (hh : x+y ≤ t) : (a*x+b*y)/2 ≤ max a b*t/2 := by
  have := mul_le_mul_of_nonneg_right (le_max_left a b) hx
  have := mul_le_mul_of_nonneg_right (le_max_right a b) hy
  have := mul_le_mul_of_nonneg_left hh (ha.trans (le_max_left a b))
  linarith

theorem square_core {φ : OM.PolMul.Spectral ℂ} {τ : Fin 3 → V} {d : V → V → ℝ}
    {c : ℝ} (hc : 0 ≤ c) (he : SquareExpansion c) (hd : Adm φ τ d) (hd0 : ∀ a b, 0 ≤ d a b)
    {p : Dat V} (hp : p ∈ Ach φ τ d) : p.1 ≤ squareSupport d c p := by
  obtain ⟨O0,O1,O2,_,_,_,M,hl,hv,rfl⟩ := hp
  let w (R : Rect V) := max (M.Uw R) (M.Vw R)
  have hw (R : Rect V) : 0 ≤ w R := (M.Uw_nonneg hv R).trans (le_max_left _ _)
  let s (R : Rect V) := c * maxPrice d R
  have hs0 (R : Rect V) : 0 ≤ s R := mul_nonneg hc ((hd0 _ _).trans (le_max_left _ _))
  change Real.logb 2 (value φ M.Z) ≤ M.ndCost d + ∑ R, s R * w R
  suffices ht : ∀ η : ℝ, 0 < η → Real.logb 2 (value φ M.Z) ≤
      M.ndCost d + ∑ R, (η+s R)*w R by
    have hcont : Continuous (fun η : ℝ => M.ndCost d + ∑ R, (η+s R)*w R) := by fun_prop
    simpa using ge_of_tendsto ((hcont.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0)))
      (eventually_nhdsWithin_of_forall fun η hη => ht η hη)
  intro η hη
  obtain ⟨L₀,hL₀⟩ := he η hη
  let C : ℝ := L₀+1
  let err := ∑ R, (η+s R)*C
  have key (n : ℕ) :
      (n : ℝ) * Real.logb 2 (value φ M.Z) ≤
        (n : ℝ) * (M.ndCost d + ∑ R, (η+s R)*w R) + err := by
    let N := M.pow n
    have hval : value φ N.Z = value φ M.Z ^ n := value_pow φ M hv n
    have hv' : 0 < value φ N.Z := hval ▸ pow_pos hv n
    let L (R : Rect V) := ⌈(n : ℝ)*w R⌉₊ + L₀
    have hlow R : (n : ℝ)*w R ≤ L R :=
      (Nat.le_ceil _).trans (by dsimp [L]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) L₀])
    have hupp R : (L R : ℝ) ≤ (n : ℝ)*w R + C := by
      dsimp [L,C]; push_cast
      linarith [Nat.ceil_lt_add_one (mul_nonneg (Nat.cast_nonneg n) (hw R))]
    choose m B hm hcount hsum hb using fun R => hL₀ (L R) (Nat.le_add_left _ _)
    let F R (j : Fin (m R)) := coeff (B R j)
    have hF R z y u v : (∑ j, F R j z y u v) = if z=v ∧ y=u then 1 else 0 := by
      have hh := congrFun (hsum R) ![z,y,u,v]
      simpa [F,coeff,crossing,matching] using hh
    have hpos1 R : 0 < Fintype.card (N.I1 R) :=
      Fintype.card_pos_iff.2 ⟨fun k => ⟨0,N.r_pos_of_value hv' k.1⟩⟩
    have hpos2 R : 0 < Fintype.card (N.I2 R) :=
      Fintype.card_pos_iff.2 ⟨fun k => ⟨0,N.r_pos_of_value hv' k.1⟩⟩
    have emb1 (R) : Nonempty (N.I1 R ↪ Index ((2 : ℕ+)^L R)) := by
      apply embed_dyadic (hpos1 R)
      rw [N.logb_card_I1 hv', TN.Uw_pow]
      exact (mul_le_mul_of_nonneg_left (le_max_left _ _) (Nat.cast_nonneg n)).trans (hlow R)
    have emb2 (R) : Nonempty (N.I2 R ↪ Index ((2 : ℕ+)^L R)) := by
      apply embed_dyadic (hpos2 R)
      rw [N.logb_card_I2 hv', TN.Vw_pow]
      exact (mul_le_mul_of_nonneg_left (le_max_right _ _) (Nat.cast_nonneg n)).trans (hlow R)
    obtain ⟨μ,hnz,hbill⟩ := single_scale hd N (hl.pow n) hv' F hF
      (fun R => (emb1 R).some) (fun R => (emb2 R).some)
    rw [hval,Real.logb_pow, TN.ndCost_pow, Fintype.card_pi] at hbill
    simp only [Fintype.card_fin, Nat.cast_prod] at hbill
    rw [Real.logb_prod _ _ fun R _ => (Nat.cast_pos.2 (hm R) : (0 : ℝ) < m R).ne'] at hbill
    have rect R : (d R.a R.c * Real.logb 2 (TN.rowMat F R (μ R)).rank +
          d R.b R.e * Real.logb 2 (TN.colMat F R (μ R)).rank)/2 ≤ s R*L R := by
      have hB : B R (μ R) ≠ 0 := fun h => hnz R (by simp [F,h]; rfl)
      have h1 := rank_pos_of_ne_zero (rowMat_ne_zero (hnz R))
      have h2 := rank_pos_of_ne_zero (colMat_ne_zero (hnz R))
      have hh := weighted_cuts (a := d R.a R.c) (b := d R.b R.e) (hd0 _ _)
        (Real.logb_nonneg (by norm_num) (by exact_mod_cast h1))
        (Real.logb_nonneg (by norm_num) (by exact_mod_cast h2)) (hb R _ hB)
      exact hh.trans_eq (by dsimp [s,maxPrice]; ring)
    have hsumcost := Finset.sum_le_sum (s := Finset.univ) fun R _ =>
      (add_le_add (hcount R) (rect R)).trans
        (show η*(L R)+s R*(L R) ≤ (η+s R)*((n : ℝ)*w R+C) by
          rw [← add_mul]; exact mul_le_mul_of_nonneg_left (hupp R) (add_nonneg hη.le (hs0 R)))
    simp only [Finset.sum_add_distrib] at hsumcost
    have hsplit : (∑ R, (η+s R)*((n : ℝ)*w R+C)) = (n : ℝ)*(∑ R, (η+s R)*w R)+err := by
      simp [err,mul_add,Finset.sum_add_distrib,Finset.mul_sum,mul_left_comm]
    rw [hsplit] at hsumcost
    linarith
  by_contra! hn
  obtain ⟨n,h⟩ := exists_nat_gt (err/(Real.logb 2 (value φ M.Z) -
    (M.ndCost d + ∑ R, (η+s R)*w R)))
  have := (div_lt_iff₀ (sub_pos.2 hn)).1 h
  linarith [key n]

end OM.NNN32
