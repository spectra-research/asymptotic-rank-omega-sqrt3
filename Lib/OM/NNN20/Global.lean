import Lib.OM.NNN20.TM.Term

/-!
# Global source nodes: real semantics and the whole-cell checker

* `η_i = P_ij + P_ik`, `w_i = θ_i / β_i`, `z_i = (θ_i - η_i)/β_i`,
  `L_i = log2((1 + (q_i - 1) 2^(d_i z_i)) / q_i)`, `ν_i = min((b_j+b_k)/q_i, b_j/k_i, b_k/k_i)`;
* the symmetric matrix `Q` of `Σ_i θ_i (b_j+b_k+ν_i L_i) x_j x_k + Σ_i w_i (b·x - [i=h] b_h x_h)(P_i·x)`
  and `D_u = b_u (1 + Σ w) - [u=h] b_h w_h`;
* the tangent tariff `c = (2 Q a - v D)/(D·a)`, `v = aᵀQa/(D·a)`, and the entries `p, q, r` of `Q`
  on `D^⊥` in the basis `(-D_1, D_0, 0)`, `(-D_2, 0, D_0)`.

Its gates: `θ_i ≤ η_i` (needed by the Lean network step), `0 < β_i ≤ 1` for triangle bonds,
`D_u > 0`, `p ≤ 0`, `r ≤ 0`, `pr - q² ≥ 0`, `c ≥ 0`. The checker `gcheck` evaluates all of this
with Taylor models on the whole cell, and also
checks that the stored polynomial upper tariff dominates `c`.
-/

namespace OM.NNN20

open Finset

/-- an action on a bond: field size `q`, role size `k`, crossings `d` -/
structure Act where
  q : ℕ
  k : ℕ
  d : ℕ
  deriving DecidableEq

def F7 : Act := ⟨7, 3, 2⟩
def F11 : Act := ⟨11, 5, 3⟩

structure GNode where
  h : Fin 3
  b : Fin 3 → ℚ
  act : Fin 3 → Act
  tri : Fin 3 → Bool
  a : Fin 3 → ℕ

/-- the two other parties, in increasing order -/
def oth1 : Fin 3 → Fin 3 := ![1, 0, 0]
def oth2 : Fin 3 → Fin 3 := ![2, 2, 1]

/-! ## Real semantics -/

section Real
variable (n : GNode) (θ : Fin 3 → ℝ) (P : Fin 3 → Fin 3 → ℝ)

def gEta (i : Fin 3) : ℝ := P i (oth1 i) + P i (oth2 i)

noncomputable def gBeta (i : Fin 3) : ℝ := if n.tri i then ((1 / 2 : ℚ) : ℝ) * (θ i + gEta P i) else 1

noncomputable def gW (i : Fin 3) : ℝ := θ i * (1 / gBeta n θ P i)

noncomputable def gZ (i : Fin 3) : ℝ := (θ i - gEta P i) * (1 / gBeta n θ P i)

noncomputable def gL (i : Fin 3) : ℝ :=
  Real.logb 2 (((1 / ((n.act i).q : ℚ) : ℚ) : ℝ) *
    (1 + (((n.act i).q - 1 : ℕ) : ℤ) * (2 : ℝ) ^ ((((n.act i).d : ℕ) : ℤ) * gZ n θ P i)))

def gNu (i : Fin 3) : ℚ :=
  min ((n.b (oth1 i) + n.b (oth2 i)) / (n.act i).q)
    (min (n.b (oth1 i) / (n.act i).k) (n.b (oth2 i) / (n.act i).k))

/-- `b` with `b_h` replaced by `0` on the retained bond `i = h` -/
def gBi (i u : Fin 3) : ℚ := if i = n.h ∧ u = n.h then 0 else n.b u

/-- the source term of bond `i` on the entry `(oth1 i, oth2 i)` -/
noncomputable def gQ1 (i : Fin 3) : ℝ :=
  ((1 / 2 : ℚ) : ℝ) * (θ i * (((n.b (oth1 i) + n.b (oth2 i) : ℚ) : ℝ) + (gNu n i : ℝ) * gL n θ P i))

/-- the parent term of bond `i` on the entry `(u, v)` -/
noncomputable def gQ2 (i u v : Fin 3) : ℝ :=
  ((1 / 2 : ℚ) : ℝ) * (gW n θ P i * ((gBi n i u : ℝ) * P i v + (gBi n i v : ℝ) * P i u))

/-- the third party (for `u ≠ v`) -/
def third (u v : Fin 3) : Fin 3 := ⟨(3 - u.val - v.val) % 3, Nat.mod_lt _ (by norm_num)⟩

noncomputable def gQ (u v : Fin 3) : ℝ :=
  (if u = v then 0 else gQ1 n θ P (third u v)) + (gQ2 n θ P 0 u v + gQ2 n θ P 1 u v + gQ2 n θ P 2 u v)

noncomputable def gD (u : Fin 3) : ℝ :=
  (n.b u : ℝ) * (1 + (gW n θ P 0 + gW n θ P 1 + gW n θ P 2)) -
    (if u = n.h then (n.b n.h : ℝ) * gW n θ P n.h else 0)

noncomputable def gQa (u : Fin 3) : ℝ :=
  (n.a 0 : ℝ) * gQ n θ P u 0 + (n.a 1 : ℝ) * gQ n θ P u 1 + (n.a 2 : ℝ) * gQ n θ P u 2

noncomputable def gDen : ℝ :=
  (n.a 0 : ℝ) * gD n θ P 0 + (n.a 1 : ℝ) * gD n θ P 1 + (n.a 2 : ℝ) * gD n θ P 2

noncomputable def gNum : ℝ :=
  (n.a 0 : ℝ) * gQa n θ P 0 + (n.a 1 : ℝ) * gQa n θ P 1 + (n.a 2 : ℝ) * gQa n θ P 2

noncomputable def gVal : ℝ := gNum n θ P * (1 / gDen n θ P)

/-- the tangent tariff `(2 Q a - v D) / (D·a)` -/
noncomputable def gC (u : Fin 3) : ℝ :=
  (2 * gQa n θ P u - gVal n θ P * gD n θ P u) * (1 / gDen n θ P)

noncomputable def gPp : ℝ :=
  gD n θ P 1 * gD n θ P 1 * gQ n θ P 0 0 - 2 * (gD n θ P 0 * gD n θ P 1 * gQ n θ P 0 1) +
    gD n θ P 0 * gD n θ P 0 * gQ n θ P 1 1

noncomputable def gPq : ℝ :=
  gD n θ P 1 * gD n θ P 2 * gQ n θ P 0 0 - gD n θ P 0 * gD n θ P 1 * gQ n θ P 0 2 -
    gD n θ P 0 * gD n θ P 2 * gQ n θ P 0 1 + gD n θ P 0 * gD n θ P 0 * gQ n θ P 1 2

noncomputable def gPr : ℝ :=
  gD n θ P 2 * gD n θ P 2 * gQ n θ P 0 0 - 2 * (gD n θ P 0 * gD n θ P 2 * gQ n θ P 0 2) +
    gD n θ P 0 * gD n θ P 0 * gQ n θ P 2 2

/-- all gates of the node at one point -/
def GGates : Prop :=
  (∀ i, θ i ≤ gEta P i) ∧ (∀ i, n.tri i = true → 0 < gBeta n θ P i ∧ gBeta n θ P i ≤ 1) ∧
  (∀ u, 0 < gD n θ P u) ∧ gPp n θ P ≤ 0 ∧ gPr n θ P ≤ 0 ∧
  0 ≤ gPp n θ P * gPr n θ P - gPq n θ P * gPq n θ P ∧ (∀ u, 0 ≤ gC n θ P u)

end Real

/-! ## The Taylor-model checker -/

structure BondTM where
  slope : TM
  beta : Option TM
  w : TM
  L : TM

def bondTM (n : GNode) (θ : Fin 3 → TM) (P : Fin 3 → Fin 3 → TM) (i : Fin 3) : Option BondTM :=
  let eta := (P i (oth1 i)).add (P i (oth2 i))
  let ac := n.act i
  let rest (z w : TM) (beta : Option TM) : Option BondTM :=
    match (TM.smul (ac.d : ℤ) z).exp2 with
    | none => none
    | some E =>
      match (TM.mulq (1 / (ac.q : ℚ)) ((TM.const ONE).add (TM.smul ((ac.q - 1 : ℕ) : ℤ) E))).log2 with
      | none => none
      | some L => some ⟨eta.sub (θ i), beta, w, L⟩
  if n.tri i then
    let beta := TM.mulq (1 / 2) ((θ i).add eta)
    match beta.recip with
    | none => none
    | some rb => rest (((θ i).sub eta).mul rb) ((θ i).mul rb) (some beta)
  else rest ((θ i).sub eta) (θ i) none

/-- a gate: `0 ≤ f` (or `0 < f` if strict) on the whole box -/
def gateOK (t : TM) (strict : Bool) : Bool :=
  if strict then decide (0 < t.rng.1) else decide (0 ≤ t.rng.1)

structure GOut where
  slope : Fin 3 → TM
  beta : Fin 3 → Option TM
  D : Fin 3 → TM
  p : TM
  r : TM
  det : TM
  c : Fin 3 → TM

def qTerm1 (n : GNode) (θ : Fin 3 → TM) (B : Fin 3 → BondTM) (i : Fin 3) : TM :=
  TM.mulq (1 / 2) ((θ i).mul ((TM.ofq (n.b (oth1 i) + n.b (oth2 i))).add (TM.mulq (gNu n i) (B i).L)))

def qTerm2 (n : GNode) (P : Fin 3 → Fin 3 → TM) (B : Fin 3 → BondTM) (i u v : Fin 3) : TM :=
  TM.mulq (1 / 2) ((B i).w.mul ((TM.mulq (gBi n i u) (P i v)).add (TM.mulq (gBi n i v) (P i u))))

def qEntry (n : GNode) (θ : Fin 3 → TM) (P : Fin 3 → Fin 3 → TM) (B : Fin 3 → BondTM)
    (u v : Fin 3) : TM :=
  (if u = v then TM.const 0 else qTerm1 n θ B (third u v)).add
    (((qTerm2 n P B 0 u v).add (qTerm2 n P B 1 u v)).add (qTerm2 n P B 2 u v))

def qMat (n : GNode) (θ : Fin 3 → TM) (P : Fin 3 → Fin 3 → TM) (B : Fin 3 → BondTM) :
    Fin 3 → Fin 3 → TM :=
  let Q00 := qEntry n θ P B 0 0
  let Q01 := qEntry n θ P B 0 1
  let Q02 := qEntry n θ P B 0 2
  let Q11 := qEntry n θ P B 1 1
  let Q12 := qEntry n θ P B 1 2
  let Q22 := qEntry n θ P B 2 2
  ![![Q00, Q01, Q02], ![Q01, Q11, Q12], ![Q02, Q12, Q22]]

def dEntry (n : GNode) (B : Fin 3 → BondTM) (W : TM) (u : Fin 3) : TM :=
  let du := TM.mulq (n.b u) ((TM.const ONE).add W)
  if u = n.h then du.sub (TM.mulq (n.b n.h) (B n.h).w) else du

def dVec (n : GNode) (B : Fin 3 → BondTM) : Fin 3 → TM :=
  let W := ((B 0).w.add (B 1).w).add (B 2).w
  let D0 := dEntry n B W 0
  let D1 := dEntry n B W 1
  let D2 := dEntry n B W 2
  ![D0, D1, D2]

/-- `a_0 v_0 + a_1 v_1 + a_2 v_2` -/
def dotA (a : Fin 3 → ℕ) (v : Fin 3 → TM) : TM :=
  ((TM.smul (a 0) (v 0)).add (TM.smul (a 1) (v 1))).add (TM.smul (a 2) (v 2))

def projP (D : Fin 3 → TM) (Q : Fin 3 → Fin 3 → TM) : TM :=
  (((D 1).mul (D 1)).mul (Q 0 0) |>.sub (TM.smul 2 (((D 0).mul (D 1)).mul (Q 0 1)))).add
    (((D 0).mul (D 0)).mul (Q 1 1))

def projQ (D : Fin 3 → TM) (Q : Fin 3 → Fin 3 → TM) : TM :=
  (((((D 1).mul (D 2)).mul (Q 0 0)).sub (((D 0).mul (D 1)).mul (Q 0 2))).sub
    (((D 0).mul (D 2)).mul (Q 0 1))).add (((D 0).mul (D 0)).mul (Q 1 2))

def projR (D : Fin 3 → TM) (Q : Fin 3 → Fin 3 → TM) : TM :=
  (((D 2).mul (D 2)).mul (Q 0 0) |>.sub (TM.smul 2 (((D 0).mul (D 2)).mul (Q 0 2)))).add
    (((D 0).mul (D 0)).mul (Q 2 2))

def gnodeTM (n : GNode) (θ : Fin 3 → TM) (P : Fin 3 → Fin 3 → TM) : Option GOut :=
  match bondTM n θ P 0, bondTM n θ P 1, bondTM n θ P 2 with
  | some B0, some B1, some B2 =>
    let B : Fin 3 → BondTM := ![B0, B1, B2]
    let Q := qMat n θ P B
    let D := dVec n B
    let qa0 := dotA n.a (Q 0)
    let qa1 := dotA n.a (Q 1)
    let qa2 := dotA n.a (Q 2)
    let QA : Fin 3 → TM := ![qa0, qa1, qa2]
    let den := dotA n.a D
    let num := dotA n.a QA
    match den.recip with
    | none => none
    | some rden =>
      let val := num.mul rden
      let cnew (u : Fin 3) : TM := ((TM.smul 2 (QA u)).sub (val.mul (D u))).mul rden
      let p := projP D Q
      let q := projQ D Q
      let r := projR D Q
      some ⟨fun i => (B i).slope, fun i => (B i).beta, D, p, r, (p.mul r).sub (q.mul q),
        ![cnew 0, cnew 1, cnew 2]⟩
  | _, _, _ => none

/-- the checker: all gates on the whole cell and `c ≤ Pk` -/
def gcheck (n : GNode) (θ : Fin 3 → TM) (P : Fin 3 → Fin 3 → TM) (Pk : Fin 3 → List ℤ) : Bool :=
  match gnodeTM n θ P with
  | none => false
  | some o =>
    (List.finRange 3).all (fun i => gateOK (o.slope i) false) &&
    (List.finRange 3).all (fun i => match o.beta i with
      | none => !(n.tri i)
      | some bt => n.tri i && gateOK bt true && gateOK ((TM.const ONE).sub bt) false) &&
    (List.finRange 3).all (fun u => gateOK (o.D u) true) &&
    gateOK o.p.neg false && gateOK o.r.neg false && gateOK o.det false &&
    (List.finRange 3).all (fun u => gateOK (o.c u) false) &&
    (List.finRange 3).all (fun u => gateOK ((TM.mk (Pk u) 0 0).sub (o.c u)) false)


/-! ## The profile and the coefficient stars on a cell -/

/-- the cell chart: `r ∈ [a, b]`; `rq`: `q ∈ [c, d]`; `rs`: `s = r - q ∈ [max 0 (a-d), b-c]` -/
structure Cell where
  a : ℚ
  b : ℚ
  c : ℚ
  d : ℚ
  rs : Bool
  perm : Fin 3 → Fin 3

/-- `θ = (t + r, t - r/2 + 3q/2, t - r/2 - 3q/2)`, permuted -/
def thetaTM (t : ℚ) (C : Cell) : Fin 3 → TM :=
  let r := TM.affine ((C.a + C.b) / 2) ((C.b - C.a) / 2) 0
  let q := if C.rs then
      let lo := max 0 (C.a - C.d)
      let hi := C.b - C.c
      r.sub (TM.affine ((lo + hi) / 2) ((hi - lo) / 2) 1)
    else TM.affine ((C.c + C.d) / 2) ((C.d - C.c) / 2) 1
  let tt := TM.ofq t
  let base : Fin 3 → TM := ![tt.add r, tt.add ((TM.mulq (-1 / 2) r).add (TM.mulq (3 / 2) q)),
    tt.sub ((TM.mulq (1 / 2) r).add (TM.mulq (3 / 2) q))]
  fun i => base (C.perm i)

/-- the coefficient star at focus `h`: `S_hh = 0`, `S_hj = θ_k` -/
def starTM (θ : Fin 3 → TM) (h j : Fin 3) : TM := if j = h then TM.const 0 else θ (third h j)

end OM.NNN20
