import Lib.OM.NNN20.Piece

/-! # Catalytic nodes: real semantics and checker

A catalytic node has an
owner `p` (`{p, j, k} = {0, 1, 2}`, `j < k`), equal T-masses `τ_j = τ_k = τ`, an action and triangle
charging on each bond, a retained code on bond `p`, and parent tariffs `c_i` on the three bonds
(global tariffs or earlier catalytic tariffs). At the profile `θ` and the target `B`:

* `η_i`, `β_i = (θ_i + η_i)/2`, `z_i`, `L_i` as for global nodes;
* `r_p = (B - Σ c_p) / β_p - L_p / q_p` (retained rate per unit of T-mass);
* `w_i = θ_i / β_i` (`i = j, k`), `den = 1 + w_j + w_k`;
* `t_j = t_k = τ/2` off `p`, `t_S = τ` off `p`, `N_j(u) = ([u = k] + t_k(u))/q_j`,
  `N_k(u) = ([u = j] + t_j(u))/q_k`;
* `λ_u = (θ_p t_S(u) + θ_j([u=k] + t_k(u)) + θ_k([u=j] + t_j(u)) - t_S(u) θ_p r_p - t_S(u) B den
         + w_j (c_j(u) + t_S(u) Σ c_j) + w_k (c_k(u) + t_S(u) Σ c_k) + N_j(u) θ_j L_j + N_k(u) θ_k L_k) / den`.

At a format `y` the full family `f ∈ {j, k}` has rate
`ρ_f(y) = (λ·y + B t_S·y - c_f·y - Σ c_f · t_S·y) / β_f - L_f N_f·y` and, with the absent-class
cutoff `t0 = 9/20`, extraction parameters between `ξ_low = -ρ_f/2 + d_f t0 N_f·y` and
`ξ_high = d_f N_f·y`; the parent of a catalytic family is queried at `y + t_S·y (1,1,1) - ξ (e_p + e_o)`
(`o` the other full party). The retained family queries its catalytic parent at
`(1,1,1) - ξ (e_j + e_k)`, `ξ ∈ [-r_p/2 + d_p t0 / q_p, d_p / q_p]`. -/

namespace OM.NNN20

open Finset

/-- the absent-class cutoff `t0 = 9/20` -/
def T0 : ℚ := 9 / 20

/-- a parent of a catalytic node: a global tariff (`Ref.seed h` or `Ref.node m` of the global
recipe) or an earlier catalytic node -/
inductive CRef where
  | glob (r : Ref)
  | cat (m : ℕ)
  deriving DecidableEq

structure CNode where
  p : Fin 3
  tau : ℚ
  act : Fin 3 → Act
  par : Fin 3 → CRef

def cj (n : CNode) : Fin 3 := oth1 n.p
def ck (n : CNode) : Fin 3 := oth2 n.p

/-! ## Real semantics at one profile point -/

section Real
variable (n : CNode) (θ : Fin 3 → ℝ) (B : ℚ) (c : Fin 3 → Fin 3 → ℝ)

/-- the bond data of a catalytic node coincide with those of a triangle-charged global node -/
def asG : GNode := ⟨n.p, fun _ => 0, n.act, fun _ => true, fun _ => 0⟩

noncomputable def cBeta (i : Fin 3) : ℝ := gBeta (asG n) θ c i
noncomputable def cL (i : Fin 3) : ℝ := gL (asG n) θ c i
noncomputable def cW (i : Fin 3) : ℝ := gW (asG n) θ c i

/-- `Σ_u c_i(u)` -/
def csum (i : Fin 3) : ℝ := c i 0 + c i 1 + c i 2

noncomputable def cRp : ℝ :=
  ((B : ℝ) - csum c n.p) * (1 / cBeta n θ c n.p) - ((1 / ((n.act n.p).q : ℚ) : ℚ) : ℝ) * cL n θ c n.p

noncomputable def cDen : ℝ := 1 + cW n θ c (cj n) + cW n θ c (ck n)

/-- `t_j(u) = t_k(u)` and `t_S(u)` -/
def cth (u : Fin 3) : ℚ := if u = n.p then 0 else n.tau / 2
def cts (u : Fin 3) : ℚ := if u = n.p then 0 else n.tau
def cNj (u : Fin 3) : ℚ := ((if u = ck n then 1 else 0) + cth n u) / (n.act (cj n)).q
def cNk (u : Fin 3) : ℚ := ((if u = cj n then 1 else 0) + cth n u) / (n.act (ck n)).q

/-- the source tariff `λ_u` -/
noncomputable def cLam (u : Fin 3) : ℝ :=
  ((cts n u : ℝ) * θ n.p + (((if u = ck n then 1 else 0) + cth n u : ℚ) : ℝ) * θ (cj n) +
    (((if u = cj n then 1 else 0) + cth n u : ℚ) : ℝ) * θ (ck n) -
    (cts n u : ℝ) * (θ n.p * cRp n θ B c) - ((cts n u * B : ℚ) : ℝ) * cDen n θ c +
    cW n θ c (cj n) * (c (cj n) u + (cts n u : ℝ) * csum c (cj n)) +
    cW n θ c (ck n) * (c (ck n) u + (cts n u : ℝ) * csum c (ck n)) +
    (cNj n u : ℝ) * (θ (cj n) * cL n θ c (cj n)) + (cNk n u : ℝ) * (θ (ck n) * cL n θ c (ck n))) *
  (1 / cDen n θ c)

/-- `Σ_u a_u y_u` for rational `y` -/
def qdot (a : Fin 3 → ℚ) (y : Fin 3 → ℚ) : ℚ := a 0 * y 0 + a 1 * y 1 + a 2 * y 2

/-- the rate of the full family `f` at the format `y` -/
noncomputable def cRho (f : Fin 3) (y : Fin 3 → ℚ) : ℝ :=
  ((y 0 : ℝ) * cLam n θ B c 0 + (y 1 : ℝ) * cLam n θ B c 1 + (y 2 : ℝ) * cLam n θ B c 2 +
      ((qdot (cts n) y * B : ℚ) : ℝ) -
      ((y 0 : ℝ) * c f 0 + (y 1 : ℝ) * c f 1 + (y 2 : ℝ) * c f 2 +
        (qdot (cts n) y : ℝ) * csum c f)) * (1 / cBeta n θ c f) -
  ((if f = cj n then qdot (cNj n) y else qdot (cNk n) y : ℚ) : ℝ) * cL n θ c f

end Real

/-! ## Constants: `log2 q` and `κ_q(9/20)` for `q = 7, 11` (rounded outward to `2^-80`) -/

def LOG2_7 : ℚ × ℚ := (3393883850097652449610045 / 1208925819614629174706176,
  3393883850097652449627213 / 1208925819614629174706176)
def LOG2_11 : ℚ × ℚ := (4182196204961857850096909 / 1208925819614629174706176,
  1045549051240464462532207 / 302231454903657293676544)
def KAP_7 : ℚ × ℚ := (393715310091071505385447 / 604462909807314587353088,
  393715310091071505400691 / 604462909807314587353088)
def KAP_11 : ℚ × ℚ := (293705361079131269050751 / 302231454903657293676544,
  146852680539565634531153 / 151115727451828646838272)

def log2q (q : ℕ) : ℚ × ℚ := if q = 7 then LOG2_7 else LOG2_11
def kapq (q : ℕ) : ℚ × ℚ := if q = 7 then KAP_7 else KAP_11

/-! ## Hull vertices and cones -/

def GRID : ℤ := 1267650600228229401496703205376

/-- the normalized format of a grid point `(x, y)`: `((G - x - y)/G, x/G, y/G)` -/
def vecV (pt : ℤ × ℤ) : Fin 3 → ℚ :=
  ![((GRID - pt.1 - pt.2 : ℤ) : ℚ) / GRID, (pt.1 : ℚ) / GRID, (pt.2 : ℚ) / GRID]

def det3 (a b c : Fin 3 → ℚ) : ℚ :=
  a 0 * (b 1 * c 2 - b 2 * c 1) - a 1 * (b 0 * c 2 - b 2 * c 0) + a 2 * (b 0 * c 1 - b 1 * c 0)

/-- `Y` lies in the cone of the fan triangle `(V_0, V_i, V_{i+1})` -/
def inTri (V : List (ℤ × ℤ)) (i : ℕ) (Y : Fin 3 → ℚ) : Bool :=
  let A := vecV (V.getD 0 (0, 0))
  let Bv := vecV (V.getD i (0, 0))
  let Cv := vecV (V.getD (i + 1) (0, 0))
  let D := det3 A Bv Cv
  decide (D ≠ 0) && decide (0 ≤ det3 Y Bv Cv * D) && decide (0 ≤ det3 A Y Cv * D) &&
    decide (0 ≤ det3 A Bv Y * D) && decide (i + 1 < V.length)

/-- all vertices are strictly positive formats -/
def vertsPos (V : List (ℤ × ℤ)) : Bool :=
  V.all fun pt => decide (0 < pt.1) && decide (0 < pt.2) && decide (0 < GRID - pt.1 - pt.2)

/-! ## The Taylor-model checker -/

structure CBond where
  beta : TM
  rb : TM
  L : TM

def cbondTM (n : CNode) (θ : Fin 3 → TM) (P : Fin 3 → Fin 3 → TM) (i : Fin 3) : Option CBond :=
  let eta := (P i (oth1 i)).add (P i (oth2 i))
  let ac := n.act i
  let beta := TM.mulq (1 / 2) ((θ i).add eta)
  match beta.recip with
  | none => none
  | some rb =>
    match (TM.smul (ac.d : ℤ) (((θ i).sub eta).mul rb)).exp2 with
    | none => none
    | some E =>
      match (TM.mulq (1 / (ac.q : ℚ)) ((TM.const ONE).add (TM.smul ((ac.q - 1 : ℕ) : ℤ) E))).log2 with
      | none => none
      | some L => some ⟨beta, rb, L⟩

structure COut where
  bond : Fin 3 → CBond
  rp : TM
  wj : TM
  wk : TM
  den : TM
  rden : TM
  lam : Fin 3 → TM

def tsum3 (c : Fin 3 → TM) : TM := ((c 0).add (c 1)).add (c 2)

/-- `Σ_u y_u t_u` -/
def tmLin (t : Fin 3 → TM) (y : Fin 3 → ℚ) : TM :=
  ((TM.mulq (y 0) (t 0)).add (TM.mulq (y 1) (t 1))).add (TM.mulq (y 2) (t 2))

def lamEntry (n : CNode) (θ : Fin 3 → TM) (B : ℚ) (P : Fin 3 → Fin 3 → TM) (b : Fin 3 → CBond)
    (rp wj wk den rden : TM) (u : Fin 3) : TM :=
  let j := cj n
  let k := ck n
  ((((((((TM.mulq (cts n u) (θ n.p)).add (TM.mulq ((if u = k then 1 else 0) + cth n u) (θ j))).add
    (TM.mulq ((if u = j then 1 else 0) + cth n u) (θ k))).sub (TM.mulq (cts n u) ((θ n.p).mul rp))).sub
    (TM.mulq (cts n u * B) den)).add (wj.mul ((P j u).add (TM.mulq (cts n u) (tsum3 (P j)))))).add
    (wk.mul ((P k u).add (TM.mulq (cts n u) (tsum3 (P k)))))).add
    (TM.mulq (cNj n u) ((θ j).mul (b j).L))).add (TM.mulq (cNk n u) ((θ k).mul (b k).L)) |>.mul rden

def cnodeTM (n : CNode) (θ : Fin 3 → TM) (B : ℚ) (P : Fin 3 → Fin 3 → TM) : Option COut :=
  match cbondTM n θ P n.p, cbondTM n θ P (cj n), cbondTM n θ P (ck n) with
  | some bp, some bj, some bk =>
    let b : Fin 3 → CBond := fun i => if i = n.p then bp else if i = cj n then bj else bk
    let rp := (((TM.ofq B).sub (tsum3 (P n.p))).mul bp.rb).sub (TM.mulq (1 / ((n.act n.p).q : ℚ)) bp.L)
    let wj := (θ (cj n)).mul bj.rb
    let wk := (θ (ck n)).mul bk.rb
    let den := ((TM.const ONE).add wj).add wk
    match den.recip with
    | none => none
    | some rden =>
      let l0 := lamEntry n θ B P b rp wj wk den rden 0
      let l1 := lamEntry n θ B P b rp wj wk den rden 1
      let l2 := lamEntry n θ B P b rp wj wk den rden 2
      some ⟨b, rp, wj, wk, den, rden, ![l0, l1, l2]⟩
  | _, _, _ => none

/-- one query endpoint `a - x s`: positive and in the cone of the fan triangle given by the head of
the witness list -/
def endpointOK (a s : Fin 3 → ℚ) (V : List (ℤ × ℤ)) (x : ℚ) : List ℕ → Option (List ℕ)
  | [] => none
  | i :: w =>
    if decide (0 < a 0 - x * s 0) && decide (0 < a 1 - x * s 1) && decide (0 < a 2 - x * s 2) &&
      inTri V i (fun u => a u - x * s u) then some w else none

/-- the query endpoints for the two range ends of every `ξ` in `xis` -/
def queryOK (a s : Fin 3 → ℚ) : List TM → List (ℤ × ℤ) → List ℕ → Option (List ℕ)
  | [], _, w => some w
  | xi :: xis, V, w =>
    match endpointOK a s V ((xi.rng.1 : ℚ) / ONE) w with
    | none => none
    | some w1 =>
      match endpointOK a s V ((xi.rng.2 : ℚ) / ONE) w1 with
      | none => none
      | some w2 => queryOK a s xis V w2

/-- the full family `f` (other full party `oth`, densities `N`) at the format `y` -/
def famOK (n : CNode) (B : ℚ) (P : Fin 3 → Fin 3 → TM) (o : COut) (Vp : Option (List (ℤ × ℤ)))
    (y : Fin 3 → ℚ) (f oth : Fin 3) (N : Fin 3 → ℚ) (w : List ℕ) : Option (List ℕ) :=
  let ts := qdot (cts n) y
  let Ny := qdot N y
  let ac := n.act f
  let base := (((tmLin o.lam y).add (TM.ofq (ts * B))).sub
    ((tmLin (P f) y).add (TM.mulq ts (tsum3 (P f))))).mul (o.bond f).rb
  let rho := base.sub (TM.mulq Ny (o.bond f).L)
  let lq := log2q ac.q
  if !(gateOK rho true && gateOK ((TM.constI (Ny * lq.1) (Ny * lq.2)).sub rho) true) then none else
  match Vp with
  | none => some w
  | some V =>
    let kq := kapq ac.q
    if !(gateOK ((TM.constI (Ny * kq.1) (Ny * kq.2)).sub rho) true) then none else
    queryOK (fun u => y u + ts) (fun u => if u = n.p ∨ u = oth then 1 else 0)
      [(TM.mulq (-1 / 2) rho).add (TM.ofq (ac.d * T0 * Ny)), TM.ofq (Ny * ac.d)] V w

/-- host balance of a full family: `role/(q-role) < y_u / t < (q-role)/role` -/
def balanceOK (yu tu : ℚ) (ac : Act) : Bool :=
  decide (0 < yu - tu * ((ac.k : ℚ) / ((ac.q : ℚ) - ac.k))) &&
    decide (0 < tu * (((ac.q : ℚ) - ac.k) / ac.k) - yu)

def vertexOK (n : CNode) (B : ℚ) (P : Fin 3 → Fin 3 → TM) (o : COut)
    (Vp : Fin 3 → Option (List (ℤ × ℤ))) (pt : ℤ × ℤ) (w : List ℕ) : Option (List ℕ) :=
  let y := vecV pt
  let tu := qdot (cth n) y
  if !(balanceOK (y (ck n)) tu (n.act (cj n)) && balanceOK (y (cj n)) tu (n.act (ck n))) then none else
  match famOK n B P o (Vp (cj n)) y (cj n) (ck n) (cNj n) w with
  | none => none
  | some w' => famOK n B P o (Vp (ck n)) y (ck n) (cj n) (cNk n) w'

def vertsOK (n : CNode) (B : ℚ) (P : Fin 3 → Fin 3 → TM) (o : COut)
    (Vp : Fin 3 → Option (List (ℤ × ℤ))) : List (ℤ × ℤ) → List ℕ → Option (List ℕ)
  | [], w => some w
  | pt :: V, w =>
    match vertexOK n B P o Vp pt w with
    | none => none
    | some w' => vertsOK n B P o Vp V w'

/-- all checks of one catalytic node -/
def ccheckNode (n : CNode) (θ : Fin 3 → TM) (B : ℚ) (P : Fin 3 → Fin 3 → TM)
    (Vp : Fin 3 → Option (List (ℤ × ℤ))) (Lhat : Fin 3 → List ℤ) (V : List (ℤ × ℤ)) (wit : List ℕ) :
    Bool :=
  match cnodeTM n θ B P with
  | none => false
  | some o =>
    let acp := n.act n.p
    let lq := log2q acp.q
    let gates :=
      decide (0 < n.tau) &&
      (List.finRange 3).all (fun i => decide (n.act i = F7) || decide (n.act i = F11)) &&
      (List.finRange 3).all (fun i => gateOK (o.bond i).beta true &&
        gateOK ((TM.const ONE).sub (o.bond i).beta) true) &&
      gateOK o.rp true &&
      gateOK ((TM.constI (lq.1 / acp.q) (lq.2 / acp.q)).sub o.rp) true &&
      (List.finRange 3).all (fun u => gateOK ((TM.mk (Lhat u) 0 0).sub (o.lam u)) false) &&
      vertsPos V
    if !gates then false else
    let w1 : Option (List ℕ) := match Vp n.p with
      | none => some wit
      | some Vpp =>
        let kq := kapq acp.q
        if !(gateOK ((TM.constI (kq.1 / acp.q) (kq.2 / acp.q)).sub o.rp) true) then none else
        queryOK (fun _ => 1) (fun u => if u = cj n ∨ u = ck n then 1 else 0)
          [(TM.mulq (-1 / 2) o.rp).add (TM.ofq (acp.d * T0 / acp.q)), TM.ofq ((acp.d : ℚ) / acp.q)] Vpp wit
    match w1 with
    | none => false
    | some w =>
      match vertsOK n B P o Vp V w with
      | some [] => true
      | _ => false

structure CEntry where
  node : CNode
  Lhat : Fin 3 → List ℤ
  V : List (ℤ × ℤ)
  wit : List ℕ

instance : Inhabited CEntry := ⟨⟨⟨0, 0, fun _ => F11, fun _ => .cat 0⟩, fun _ => [], [], []⟩⟩

def cparRow (S : SeedPrm) (θ : Fin 3 → TM) (R : List GEntry) (CR : List CEntry) (r : CRef)
    (i : Fin 3) : Fin 3 → TM :=
  match r with
  | .glob g => parRow S θ R g i
  | .cat m => let e := CR.getD m default; ![⟨e.Lhat 0, 0, 0⟩, ⟨e.Lhat 1, 0, 0⟩, ⟨e.Lhat 2, 0, 0⟩]

def cparV (CR : List CEntry) (r : CRef) : Option (List (ℤ × ℤ)) :=
  match r with
  | .glob _ => none
  | .cat m => some (CR.getD m default).V

/-- the check of catalytic node `k` -/
def ccheckAt (S : SeedPrm) (C : Cell) (R : List GEntry) (B : ℚ) (CR : List CEntry) (k : ℕ) : Bool :=
  let θ := thetaTM S.t C
  let e := CR.getD k default
  let P0 := cparRow S θ R CR (e.node.par 0) 0
  let P1 := cparRow S θ R CR (e.node.par 1) 1
  let P2 := cparRow S θ R CR (e.node.par 2) 2
  ccheckNode e.node θ B ![P0, P1, P2] (fun i => cparV CR (e.node.par i)) e.Lhat e.V e.wit

/-- the terminal of a catalytic recipe: `Σ λ̂ ≤ B` on the cell and `(1,1,1)` in its cone -/
def cterm (CR : List CEntry) (B : ℚ) (lvl k w : ℕ) : Bool :=
  let e := CR.getD k default
  termCheck (sumL [e.Lhat 0, e.Lhat 1, e.Lhat 2]) B lvl && inTri e.V w (fun _ => 1)

end OM.NNN20
