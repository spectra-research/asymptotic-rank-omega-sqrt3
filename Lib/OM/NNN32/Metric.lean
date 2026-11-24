import Lib.OM.NNN32.SquarePrices
import Lib.OM.NNN30.Net.Main
import Lib.OM.NNN30.RectMain
import PLATFORM.Statements.«R113.9»

/-! # The square estimate on the tower of midpoint price extensions

A minimal price admits a squared-rectangle extension. In that extension every
old midpoint agrees at distance zero with the new midpoint. Thus midpoints in any
finite minimal price are unique up to distance zero. A separate equal-width
extension can price these same midpoints and its linear bound transfers back.
-/

noncomputable section

namespace OM.NNN32

open OM.NNN30 OM.NNN30.Net OM.NNN30.Geom Foundations.PairUnitExponents

variable {V : Type} [Fintype V] [LinearOrder V] {φ : OM.PolMul.Spectral ℂ}
  {τ : Fin 3 → V} {d : V → V → ℝ}

private lemma unique_midprice (hd : MinAdm φ τ d) {a b x y : V}
    (hax : d a x ≤ d a b/2) (hxb : d x b ≤ d a b/2)
    (hay : d a y ≤ d a b/2) (hyb : d y b ≤ d a b/2) : d x y = 0 := by
  obtain ⟨D,hD,hrow,hcol,hquad,hdiag⟩ := midpoint_extension proof_R108_3 hd
  have same (z : V) (ha : d a z ≤ d a b/2) (hb : d z b ≤ d a b/2) :
      D (a,b) (z,z) = 0 := by
    have h := hquad a z z b
    have h1 := hD.triangle (a,a) (a,z) (b,b)
    have h2 := hD.triangle (a,z) (z,b) (b,b)
    rw [hdiag] at h1
    have hlow : d a b/2 ≤ D (a,z) (z,b) := by linarith [hcol a a z, hrow z b b]
    have hsq := pow_le_pow_left₀ (div_nonneg (hd.2.1 _ _) (by norm_num)) hlow 2
    have hsa := pow_le_pow_left₀ (hd.2.1 _ _) ha 2
    have hsb := pow_le_pow_left₀ (hd.2.1 _ _) hb 2
    nlinarith [hD.2.1 (a,b) (z,z)]
  have ht := hD.triangle (x,x) (a,b) (y,y)
  rw [hdiag,hD.symm (x,x) (a,b),same x hax hxb,same y hay hyb,zero_add] at ht
  exact le_antisymm ht (hd.2.1 _ _)

private lemma finite_linear {c : ℝ} (hc : 1 ≤ c) (he : SquareExpansion c) (hd : MinAdm φ τ d)
    (a b z e u v w x : V)
    (hu : d a u ≤ d a b/2 ∧ d u b ≤ d a b/2)
    (hv : d z v ≤ d z e/2 ∧ d v e ≤ d z e/2)
    (hw : d a w ≤ d a e/2 ∧ d w e ≤ d a e/2)
    (hx : d z x ≤ d z b/2 ∧ d x b ≤ d z b/2) :
    d u v + d w x ≤ c * max (d a z) (d b e) := by
  obtain ⟨D,hD,hr,hs,hl,hi⟩ := square_extension hc he hd
  letI : LinearOrder (V × V) := LinearOrder.lift' (Fintype.equivFin _) (Fintype.equivFin _).injective
  have zero (i j m : V) (hm : d i m ≤ d i j/2 ∧ d m j ≤ d i j/2) : D (m,m) (i,j) = 0 := by
    apply unique_midprice hD (a := (i,i)) (b := (j,j))
    · simpa only [hi] using! hm.1
    · simpa only [hi] using! hm.2
    · simpa only [hi] using! hs i i j
    · simpa only [hi] using! hr i j j
  have cmp (i j k l g f : V) (h1 : D (g,g) (i,j) = 0) (h2 : D (f,f) (k,l) = 0) :
      d g f ≤ D (i,j) (k,l) := by
    have t1 := hD.triangle (g,g) (i,j) (f,f)
    have t2 := hD.triangle (i,j) (k,l) (f,f)
    rw [hi,h1] at t1
    rw [hD.symm (k,l) (f,f),h2] at t2
    linarith
  exact (add_le_add (cmp a b z e u v (zero _ _ _ hu) (zero _ _ _ hv))
    (cmp a e z b w x (zero _ _ _ hw) (zero _ _ _ hx))).trans (hl a b z e)

private lemma tower_linear {c : ℝ} (hc : 1 ≤ c) (he : SquareExpansion c)
    (base : {d : Lv 0 → Lv 0 → ℝ // MinAdm φ (τL 0) d})
    (a b z e : Tm) :
    dX proof_R108_3 base (.node a b) (.node z e) + dX proof_R108_3 base (.node a e) (.node z b)
      ≤ c * max (dX proof_R108_3 base a z) (dX proof_R108_3 base b e) := by
  let K := max (max a.depth b.depth) (max z.depth e.depth)
  have r := rel proof_R108_3 base K
  let D := dL proof_R108_3 base (K+1)
  have halves (i j : Lv K) :
      D (i,i) (i,j) ≤ D (i,i) (j,j)/2 ∧ D (i,j) (j,j) ≤ D (i,i) (j,j)/2 := by
    dsimp only [D]
    rw [r.diag]
    exact ⟨r.col i i j, r.row i j j⟩
  rw [← dX_eq proof_R108_3 base (.node a b) (.node z e) (K+1) (by simp only [Tm.depth]; omega),
    ← dX_eq proof_R108_3 base (.node a e) (.node z b) (K+1) (by simp only [Tm.depth]; omega),
    ← dX_eq proof_R108_3 base a z K (by omega), ← dX_eq proof_R108_3 base b e K (by omega)]
  have h := finite_linear hc he (tower proof_R108_3 base (K+1)).2 _ _ _ _ _ _ _ _
    (halves (ev K a) (ev K b)) (halves (ev K z) (ev K e))
    (halves (ev K a) (ev K e)) (halves (ev K z) (ev K b))
  simpa only [show (tower proof_R108_3 base (K+1)).1 = dL proof_R108_3 base (K+1) from rfl,
    r.diag] using! h

theorem proof_R113_9 : S_R113_9 := by
  intro hw
  obtain ⟨c,hc,hstrict,hexp⟩ := square_expansion_of_witness hw
  refine ⟨c,hc,hstrict,fun φ => ?_⟩
  obtain ⟨d,hd,ho,h12,h02,h01⟩ := initial_minimal φ
  let base : {d : Lv 0 → Lv 0 → ℝ // MinAdm φ (τL 0) d} := ⟨d,hd⟩
  let S : MidSpace Tm := ⟨dX proof_R108_3 base,Tm.node,dX_self _ _,dX_symm _ _,dX_tri _ _,
    dX_node_row _ _,dX_node_col _ _,dX_node_self _ _,dX_quad _ _⟩
  refine ⟨Tm,S,fun i => Tm.leaf i.castSucc,Tm.leaf 3,tower_linear hc hexp base,?_,?_,h12,h02,h01⟩
  · intro q
    simpa [Fin.sum_univ_succ,S,add_assoc] using dX_fermat proof_R108_3 base q
  · apply le_antisymm
    · simpa [Fin.sum_univ_succ,S,base,add_assoc,dX_level0] using ho
    · simpa [Fin.sum_univ_succ,S,add_assoc] using dX_fermat proof_R108_3 base (Tm.leaf 3)

end OM.NNN32
