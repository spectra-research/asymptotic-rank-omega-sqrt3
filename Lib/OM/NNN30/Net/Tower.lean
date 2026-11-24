import Lib.OM.NNN30.Net.Step

/-! # The tower of midpoint extensions and its union

Levels `Lv 0 = Fin 4` (terminals `0, 1, 2`, initial site `3`), `Lv (k+1) = Lv k × Lv k`, minimal
admissible prices `dL k` chosen by recursion with `midpoint_extension`.  The union is the type `Tm`
of binary trees with leaves in `Fin 4`; a tree of depth `≤ K` is evaluated at level `K` by
`ev K` (a leaf is copied along the diagonal, a node `m(a,b)` is the pair `(ev a, ev b)`), and the
distance of two trees is that of their evaluations at the larger depth.  Evaluation one level
higher changes nothing up to distance zero (`ev_succ_zero`, from the uniqueness of midpoints, i.e.
(7) one level up), so all axioms of R111.2 hold at a common level. -/

noncomputable section
open scoped BigOperators Classical

namespace OM.NNN30.Net

open CoordinateTensor OM.NNN.Raw

/-- the levels of the tower -/
def Lv : ℕ → Type
  | 0 => Fin 4
  | k + 1 => Lv k × Lv k

instance instFintypeLv : (k : ℕ) → Fintype (Lv k)
  | 0 => (inferInstance : Fintype (Fin 4))
  | k + 1 => @instFintypeProd _ _ (instFintypeLv k) (instFintypeLv k)

instance instLinearOrderLv (k : ℕ) : LinearOrder (Lv k) :=
  LinearOrder.lift' (Fintype.equivFin (Lv k)) (Fintype.equivFin (Lv k)).injective

/-- the terminals at each level -/
def τL : (k : ℕ) → Fin 3 → Lv k
  | 0 => fun i => (Fin.castSucc i : Fin 4)
  | k + 1 => fun i => (τL k i, τL k i)

/-- the properties of one level over the previous one -/
structure LevelRel {k : ℕ} (d : Lv k → Lv k → ℝ) (D : Lv (k + 1) → Lv (k + 1) → ℝ) : Prop where
  row : ∀ a b c : Lv k, D (a, b) (c, b) ≤ d a c / 2
  col : ∀ a b e : Lv k, D (a, b) (a, e) ≤ d b e / 2
  quad : ∀ a b c e : Lv k, D (a, b) (c, e) ^ 2 + D (a, e) (c, b) ^ 2 ≤ (d a c ^ 2 + d b e ^ 2) / 2
  diag : ∀ a c : Lv k, D (a, a) (c, c) = d a c

variable {φ : OM.PolMul.Spectral ℂ}

/-- the tower of minimal admissible prices -/
def tower (h3 : S_R108_3) (d0 : {d : Lv 0 → Lv 0 → ℝ // MinAdm φ (τL 0) d}) :
    (k : ℕ) → {d : Lv k → Lv k → ℝ // MinAdm φ (τL k) d}
  | 0 => d0
  | k + 1 => ⟨Classical.choose (midpoint_extension (V := Lv k) h3 (tower h3 d0 k).2),
      (Classical.choose_spec (midpoint_extension (V := Lv k) h3 (tower h3 d0 k).2)).1⟩

lemma tower_rel (h3 : S_R108_3) (d0 : {d : Lv 0 → Lv 0 → ℝ // MinAdm φ (τL 0) d}) (k : ℕ) :
    LevelRel (tower h3 d0 k).1 (tower h3 d0 (k + 1)).1 := by
  obtain ⟨_, hrow, hcol, hquad, hdiag⟩ :=
    Classical.choose_spec (midpoint_extension (V := Lv k) h3 (tower h3 d0 k).2)
  exact ⟨hrow, hcol, hquad, hdiag⟩

/-! ## Trees -/

/-- binary trees with leaves in `Fin 4`: the points of the union -/
inductive Tm : Type
  | leaf : Fin 4 → Tm
  | node : Tm → Tm → Tm

/-- the depth of a tree -/
def Tm.depth : Tm → ℕ
  | leaf _ => 0
  | node a b => max a.depth b.depth + 1

/-- evaluation at a level -/
def ev : (K : ℕ) → Tm → Lv K
  | 0, Tm.leaf i => i
  | 0, Tm.node _ _ => (0 : Fin 4)
  | K + 1, Tm.leaf i => (ev K (Tm.leaf i), ev K (Tm.leaf i))
  | K + 1, Tm.node a b => (ev K a, ev K b)

lemma ev_leaf (j : Fin 3) : ∀ K, ev K (Tm.leaf (Fin.castSucc j)) = τL K j
  | 0 => rfl
  | K + 1 => by
    show (ev K (Tm.leaf (Fin.castSucc j)), ev K (Tm.leaf (Fin.castSucc j))) = (τL K j, τL K j)
    rw [ev_leaf j K]

/-! ## Distances in the union -/

section Union

variable (h3 : S_R108_3) (d0 : {d : Lv 0 → Lv 0 → ℝ // MinAdm φ (τL 0) d})

/-- the prices at level `k` -/
def dL (k : ℕ) : Lv k → Lv k → ℝ := (tower h3 d0 k).1

lemma dL_nonneg (k : ℕ) (s t : Lv k) : 0 ≤ dL h3 d0 k s t := (tower h3 d0 k).2.2.1 s t
lemma dL_self (k : ℕ) (s : Lv k) : dL h3 d0 k s s = 0 := (tower h3 d0 k).2.2.2.1 s
lemma dL_symm (k : ℕ) (s t : Lv k) : dL h3 d0 k s t = dL h3 d0 k t s := (tower h3 d0 k).2.symm s t
lemma dL_tri (k : ℕ) (s t u : Lv k) : dL h3 d0 k s u ≤ dL h3 d0 k s t + dL h3 d0 k t u :=
  (tower h3 d0 k).2.triangle s t u

lemma rel (k : ℕ) : LevelRel (dL h3 d0 k) (dL h3 d0 (k + 1)) := tower_rel h3 d0 k

/-- The geometry of the union uses only the finite pseudometrics and the
rectangle, axis and diagonal relations between successive levels. -/
structure PriceTower where
  d : (k : ℕ) → Lv k → Lv k → ℝ
  nonneg : ∀ k s t, 0 ≤ d k s t
  self : ∀ k s, d k s s = 0
  symm : ∀ k s t, d k s t = d k t s
  triangle : ∀ k s t u, d k s u ≤ d k s t + d k t u
  step : ∀ k, LevelRel (d k) (d (k+1))

private def priceTower : PriceTower :=
  ⟨dL h3 d0,dL_nonneg h3 d0,dL_self h3 d0,dL_symm h3 d0,dL_tri h3 d0,rel h3 d0⟩

namespace PriceTower

variable (P : PriceTower)

/-- **uniqueness of midpoints**: the diagonal copy of `(u, w)` is the midpoint of `ι u, ι w` -/
lemma consistency (k : ℕ) (u w : Lv k) :
    P.d (k + 2) (((u, u) : Lv (k + 1)), ((w, w) : Lv (k + 1)))
      (((u, w) : Lv (k + 1)), ((u, w) : Lv (k + 1))) = 0 := by
  have R1 := P.step k
  have R2 := P.step (k + 1)
  set δ := P.d k u w
  have hδ : 0 ≤ δ := P.nonneg k u w
  let A : Lv (k + 1) := (u, u)
  let C : Lv (k + 1) := (w, w)
  let Bz : Lv (k + 1) := (u, w)
  have hq := R2.quad A Bz Bz C
  have hAB : P.d (k + 1) A Bz ≤ δ / 2 := R1.col u u w
  have hBC : P.d (k + 1) Bz C ≤ δ / 2 := R1.row u w w
  have hAC : P.d (k + 1) A C = δ := R1.diag u w
  have hAAC : P.d (k + 2) (A, A) (C, C) = δ := by rw [R2.diag A C, hAC]
  have h1 : P.d (k + 2) (A, A) (A, Bz) ≤ δ / 4 := by
    have := R2.col A A Bz; linarith
  have h2 : P.d (k + 2) (Bz, C) (C, C) ≤ δ / 4 := by
    have := R2.row Bz C C; linarith
  have htri : P.d (k + 2) (A, A) (C, C) ≤ P.d (k + 2) (A, A) (A, Bz) +
      P.d (k + 2) (A, Bz) (Bz, C) + P.d (k + 2) (Bz, C) (C, C) := by
    have t1 := P.triangle (k + 2) (A, A) (A, Bz) (C, C)
    have t2 := P.triangle (k + 2) (A, Bz) (Bz, C) (C, C)
    linarith
  have hlow : δ / 2 ≤ P.d (k + 2) (A, Bz) (Bz, C) := by linarith
  have hlow2 : (δ / 2) ^ 2 ≤ P.d (k + 2) (A, Bz) (Bz, C) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hlow 2
  have hAB2 : P.d (k + 1) A Bz ^ 2 ≤ (δ / 2) ^ 2 :=
    pow_le_pow_left₀ (P.nonneg _ _ _) hAB 2
  have hBC2 : P.d (k + 1) Bz C ^ 2 ≤ (δ / 2) ^ 2 :=
    pow_le_pow_left₀ (P.nonneg _ _ _) hBC 2
  have hz : P.d (k + 2) (A, C) (Bz, Bz) ^ 2 ≤ 0 := by nlinarith
  have h0 := P.nonneg (k + 2) (A, C) (Bz, Bz)
  nlinarith

/-- evaluation one level higher agrees with the diagonal copy, up to distance zero -/
lemma ev_succ_zero : ∀ (s : Tm) (K : ℕ), s.depth ≤ K →
    P.d (K + 1) (ev (K + 1) s) ((ev K s, ev K s) : Lv (K + 1)) = 0
  | Tm.leaf i, K, _ => P.self (K + 1) _
  | Tm.node a b, K, hK => by
    obtain ⟨K', rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by
      have : 1 ≤ (Tm.node a b).depth := by simp [Tm.depth]
      omega⟩
    have ha : a.depth ≤ K' := by simp only [Tm.depth] at hK; omega
    have hb : b.depth ≤ K' := by simp only [Tm.depth] at hK; omega
    have iha := ev_succ_zero a K' ha
    have ihb := ev_succ_zero b K' hb
    have R := P.step (K' + 1)
    set x := ev (K' + 1) a
    set y := ev (K' + 1) b
    set x' : Lv (K' + 1) := (ev K' a, ev K' a)
    set y' : Lv (K' + 1) := (ev K' b, ev K' b)
    have e1 : P.d (K' + 2) (x, y) (x', y) ≤ 0 := by
      have := R.row x y x'; rw [iha] at this; linarith
    have e2 : P.d (K' + 2) (x', y) (x', y') ≤ 0 := by
      have := R.col x' y y'; rw [ihb] at this; linarith
    have e3 := P.consistency K' (ev K' a) (ev K' b)
    show P.d (K' + 2) (x, y) ((ev K' a, ev K' b), (ev K' a, ev K' b)) = 0
    have t1 := P.triangle (K' + 2) (x, y) (x', y) (x', y')
    have t2 := P.triangle (K' + 2) (x, y) (x', y') ((ev K' a, ev K' b), (ev K' a, ev K' b))
    have h0 := P.nonneg (K' + 2) (x, y) ((ev K' a, ev K' b), (ev K' a, ev K' b))
    have h0' := P.nonneg (K' + 2) (x, y) (x', y)
    have h0'' := P.nonneg (K' + 2) (x', y) (x', y')
    linarith

/-- distances do not change one level up -/
lemma dL_ev_succ (s t : Tm) (K : ℕ) (hs : s.depth ≤ K) (ht : t.depth ≤ K) :
    P.d (K + 1) (ev (K + 1) s) (ev (K + 1) t) = P.d K (ev K s) (ev K t) := by
  have hd := (P.step K).diag (ev K s) (ev K t)
  have zs := P.ev_succ_zero s K hs
  have zt := P.ev_succ_zero t K ht
  have t1 := P.triangle (K + 1) (ev (K + 1) s) ((ev K s, ev K s) : Lv (K + 1)) (ev (K + 1) t)
  have t2 := P.triangle (K + 1) ((ev K s, ev K s) : Lv (K + 1)) ((ev K t, ev K t) : Lv (K + 1))
    (ev (K + 1) t)
  have t3 := P.triangle (K + 1) ((ev K s, ev K s) : Lv (K + 1)) (ev (K + 1) s)
    ((ev K t, ev K t) : Lv (K + 1))
  have t4 := P.triangle (K + 1) (ev (K + 1) s) (ev (K + 1) t) ((ev K t, ev K t) : Lv (K + 1))
  have sy1 := P.symm (K + 1) (ev (K + 1) t) ((ev K t, ev K t) : Lv (K + 1))
  have sy2 := P.symm (K + 1) (ev (K + 1) s) ((ev K s, ev K s) : Lv (K + 1))
  linarith

/-- the distance in the union -/
def dX (s t : Tm) : ℝ := P.d (max s.depth t.depth) (ev _ s) (ev _ t)

lemma dX_eq (s t : Tm) (K : ℕ) (hK : max s.depth t.depth ≤ K) :
    P.d K (ev K s) (ev K t) = P.dX s t := by
  induction K, hK using Nat.le_induction with
  | base => rfl
  | succ K hK ih =>
    rw [P.dL_ev_succ s t K (le_trans (le_max_left _ _) hK) (le_trans (le_max_right _ _) hK), ih]

lemma dX_self (x : Tm) : P.dX x x = 0 := P.self _ _

lemma dX_symm (x y : Tm) : P.dX x y = P.dX y x := by
  rw [← P.dX_eq y x (max x.depth y.depth) (by rw [max_comm])]
  exact P.symm _ _ _

lemma dX_tri (x y z : Tm) : P.dX x z ≤ P.dX x y + P.dX y z := by
  set K := max (max x.depth y.depth) z.depth
  rw [← P.dX_eq x z K (by omega), ← P.dX_eq x y K (by omega),
    ← P.dX_eq y z K (by omega)]
  exact P.triangle _ _ _ _

lemma dX_node_row (a b c : Tm) :
    P.dX (Tm.node a b) (Tm.node c b) ≤ P.dX a c / 2 := by
  set K := max (max a.depth b.depth) c.depth
  rw [← P.dX_eq (Tm.node a b) (Tm.node c b) (K + 1) (by simp only [Tm.depth]; omega),
    ← P.dX_eq a c K (by omega)]
  exact (P.step K).row (ev K a) (ev K b) (ev K c)

lemma dX_node_col (a b e : Tm) :
    P.dX (Tm.node a b) (Tm.node a e) ≤ P.dX b e / 2 := by
  set K := max (max a.depth b.depth) e.depth
  rw [← P.dX_eq (Tm.node a b) (Tm.node a e) (K + 1) (by simp only [Tm.depth]; omega),
    ← P.dX_eq b e K (by omega)]
  exact (P.step K).col (ev K a) (ev K b) (ev K e)

lemma dX_node_self (a : Tm) : P.dX (Tm.node a a) a = 0 := by
  rw [← P.dX_eq (Tm.node a a) a (a.depth + 1) (by simp only [Tm.depth]; omega)]
  exact (P.symm (a.depth + 1) ((ev a.depth a, ev a.depth a) : Lv (a.depth + 1))
    (ev (a.depth + 1) a)).trans (P.ev_succ_zero a a.depth le_rfl)

lemma dX_quad (a b c e : Tm) :
    P.dX (Tm.node a b) (Tm.node c e) ^ 2 + P.dX (Tm.node a e) (Tm.node c b) ^ 2 ≤
      (P.dX a c ^ 2 + P.dX b e ^ 2) / 2 := by
  set K := max (max a.depth b.depth) (max c.depth e.depth)
  rw [← P.dX_eq (Tm.node a b) (Tm.node c e) (K + 1) (by simp only [Tm.depth]; omega),
    ← P.dX_eq (Tm.node a e) (Tm.node c b) (K + 1) (by simp only [Tm.depth]; omega),
    ← P.dX_eq a c K (by omega), ← P.dX_eq b e K (by omega)]
  exact (P.step K).quad (ev K a) (ev K b) (ev K c) (ev K e)

end PriceTower

lemma consistency (k : ℕ) (u w : Lv k) :
    dL h3 d0 (k + 2) (((u, u) : Lv (k + 1)), ((w, w) : Lv (k + 1)))
      (((u, w) : Lv (k + 1)), ((u, w) : Lv (k + 1))) = 0 :=
  (priceTower h3 d0).consistency k u w

lemma ev_succ_zero : ∀ (s : Tm) (K : ℕ), s.depth ≤ K →
    dL h3 d0 (K + 1) (ev (K + 1) s) ((ev K s, ev K s) : Lv (K + 1)) = 0 :=
  (priceTower h3 d0).ev_succ_zero

lemma dL_ev_succ (s t : Tm) (K : ℕ) (hs : s.depth ≤ K) (ht : t.depth ≤ K) :
    dL h3 d0 (K + 1) (ev (K + 1) s) (ev (K + 1) t) = dL h3 d0 K (ev K s) (ev K t) :=
  (priceTower h3 d0).dL_ev_succ s t K hs ht

def dX (s t : Tm) : ℝ :=
  (priceTower h3 d0).dX s t

lemma dX_eq (s t : Tm) (K : ℕ) (hK : max s.depth t.depth ≤ K) :
    dL h3 d0 K (ev K s) (ev K t) = dX h3 d0 s t :=
  (priceTower h3 d0).dX_eq s t K hK

lemma dX_self (x : Tm) : dX h3 d0 x x = 0 :=
  (priceTower h3 d0).dX_self x

lemma dX_symm (x y : Tm) : dX h3 d0 x y = dX h3 d0 y x :=
  (priceTower h3 d0).dX_symm x y

lemma dX_tri (x y z : Tm) : dX h3 d0 x z ≤ dX h3 d0 x y + dX h3 d0 y z :=
  (priceTower h3 d0).dX_tri x y z

lemma dX_node_row (a b c : Tm) :
    dX h3 d0 (Tm.node a b) (Tm.node c b) ≤ dX h3 d0 a c / 2 :=
  (priceTower h3 d0).dX_node_row a b c

lemma dX_node_col (a b e : Tm) :
    dX h3 d0 (Tm.node a b) (Tm.node a e) ≤ dX h3 d0 b e / 2 :=
  (priceTower h3 d0).dX_node_col a b e

lemma dX_node_self (a : Tm) : dX h3 d0 (Tm.node a a) a = 0 :=
  (priceTower h3 d0).dX_node_self a

lemma dX_quad (a b c e : Tm) :
    dX h3 d0 (Tm.node a b) (Tm.node c e) ^ 2 + dX h3 d0 (Tm.node a e) (Tm.node c b) ^ 2 ≤
      (dX h3 d0 a c ^ 2 + dX h3 d0 b e ^ 2) / 2 :=
  (priceTower h3 d0).dX_quad a b c e

lemma dX_leaf (q : Tm) (j : Fin 3) :
    dX h3 d0 q (Tm.leaf (Fin.castSucc j)) = dL h3 d0 q.depth (ev q.depth q) (τL q.depth j) := by
  rw [← dX_eq h3 d0 q (Tm.leaf (Fin.castSucc j)) q.depth (by simp [Tm.depth]), ev_leaf]

lemma dX_fermat (q : Tm) :
    P2M.R88.Fv φ (fun _ => 1) ≤ dX h3 d0 q (Tm.leaf 0) + dX h3 d0 q (Tm.leaf 1) +
      dX h3 d0 q (Tm.leaf 2) := by
  have h := Fv_le_sum (tower h3 d0 q.depth).2.1 (tower h3 d0 q.depth).2.2.1
    (tower h3 d0 q.depth).2.2.2.1 (ev q.depth q)
  have e0 := dX_leaf h3 d0 q 0
  have e1 := dX_leaf h3 d0 q 1
  have e2 := dX_leaf h3 d0 q 2
  simp only [Fin.castSucc_zero, Fin.castSucc_one] at e0 e1
  have e2' : (Fin.castSucc (2 : Fin 3) : Fin 4) = 2 := rfl
  rw [e2'] at e2
  rw [e0, e1, e2]
  exact h

lemma dX_level0 (i j : Fin 4) : dX h3 d0 (Tm.leaf i) (Tm.leaf j) = d0.1 i j := rfl

end Union

end OM.NNN30.Net
