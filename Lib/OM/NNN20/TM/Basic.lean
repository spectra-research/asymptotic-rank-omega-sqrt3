import Mathlib

/-! # Fixed-point bivariate Taylor models: the computational core

Every number is an integer `m` standing for `m * 2^-P` (`P = 64`, `ONE = 2^64`). A polynomial
is the list of its integer coefficients on the graded monomial list `MONO` (`x^a y^b`,
`a + b ≤ 8`, ordered by total degree and then by `a`). A Taylor model `⟨c, lo, hi⟩` encloses a
function `f` on the box `[-1,1]^2` when `poly c + lo ≤ ONE * f ≤ poly c + hi` there (`TM.Encl`,
in `Lib.OM.NNN20.TM.Sem`).

This file contains only the algorithms that the kernel evaluates in the certificates
(`decide +kernel`). The sibling modules prove soundness of the rational Taylor enclosures.

Products use Kronecker substitution: both factors are packed into one integer
`Σ c_i 2^(W κ_i)` (`κ = a + 17 b`), multiplied by GMP, and the coefficients of total degree
`≤ 8` are read off as base-`2^W` digits after adding the offset `Σ_k 2^(W-1) 2^(W k)`. The
discarded part (total degree `≥ 9`) is bounded through the per-degree `ℓ¹` norms. -/

namespace OM.NNN20

/-- fractional bits -/
def P : ℕ := 64
/-- `2^P` -/
def ONE : ℤ := 18446744073709551616
/-- total degree of the Taylor polynomials -/
def DEG : ℕ := 8
/-- number of monomials of total degree `≤ DEG` -/
def NM : ℕ := 45
/-- the Kronecker radix `2 DEG + 1` -/
def RK : ℕ := 17
/-- number of Kronecker slots of a product (`RK * RK`) -/
def NSLOT : ℕ := 289
/-- series terms of the reciprocal, logarithm and exponential -/
def NS : ℕ := 8

/-- The graded monomials `(a, b)` standing for `x^a y^b`. -/
def MONO : List (ℕ × ℕ) :=
  [(0,0),(0,1),(1,0),(0,2),(1,1),(2,0),(0,3),(1,2),(2,1),(3,0),(0,4),(1,3),(2,2),(3,1),(4,0),
   (0,5),(1,4),(2,3),(3,2),(4,1),(5,0),(0,6),(1,5),(2,4),(3,3),(4,2),(5,1),(6,0),
   (0,7),(1,6),(2,5),(3,4),(4,3),(5,2),(6,1),(7,0),
   (0,8),(1,7),(2,6),(3,5),(4,4),(5,3),(6,2),(7,1),(8,0)]

/-- Kronecker exponents `a + RK b` of `MONO`. -/
def KAPPA : List ℕ :=
  [0, 17, 1, 34, 18, 2, 51, 35, 19, 3, 68, 52, 36, 20, 4, 85, 69, 53, 37, 21, 5, 102, 86, 70,
   54, 38, 22, 6, 119, 103, 87, 71, 55, 39, 23, 7, 136, 120, 104, 88, 72, 56, 40, 24, 8]

/-- `x^a y^b ≥ 0` on the box when `a` and `b` are even. -/
def EVEN : List Bool :=
  [true, false, false, true, false, true, false, false, false, false, true, false, true, false,
   true, false, false, false, false, false, false, true, false, true, false, true, false, true,
   false, false, false, false, false, false, false, false, true, false, true, false, true, false,
   true, false, true]

/-- sizes of the blocks of equal total degree in `MONO` -/
def BLOCKS : List ℕ := [1, 2, 3, 4, 5, 6, 7, 8, 9]

/-! ## Rational helpers -/

/-- `⌊x⌋` for a rational `x` -/
def qfloor (x : ℚ) : ℤ := x.num / (x.den : ℤ)
/-- `⌈x⌉` for a rational `x` -/
def qceil (x : ℚ) : ℤ := -qfloor (-x)
/-- `⌈a / b⌉` for `b > 0` -/
def cdiv (a b : ℤ) : ℤ := -((-a) / b)

/-! ## Coefficient lists -/

/-- coefficientwise sum, padding the shorter list with zeros -/
def addL : List ℤ → List ℤ → List ℤ
  | a :: as, b :: bs => (a + b) :: addL as bs
  | [], bs => bs
  | as, [] => as

def negL (c : List ℤ) : List ℤ := c.map (fun a => -a)

def smulL (k : ℤ) (c : List ℤ) : List ℤ := c.map (fun a => k * a)

/-- `Σ |c_i|` -/
def l1 : List ℤ → ℕ
  | [] => 0
  | a :: as => a.natAbs + l1 as

/-- the per-degree `ℓ¹` norms `[N_0, …, N_8]` (blocks of `MONO`) -/
def degNorms : List ℕ → List ℤ → List ℕ
  | [], _ => []
  | b :: bs, c => l1 (c.take b) :: degNorms bs (c.drop b)

/-- `Σ_{t} m_t` -/
def sumN : List ℕ → ℕ
  | [] => 0
  | a :: as => a + sumN as

/-- `Σ_{s + s' > DEG} n_s m_s'` for `n = [n_0, …]`, `m = [m_0, …, m_DEG]` -/
def highAux (m : List ℕ) : ℕ → List ℕ → ℕ
  | _, [] => 0
  | s, a :: as => a * sumN (m.drop (DEG + 1 - s)) + highAux m (s + 1) as

def highBound (n m : List ℕ) : ℕ := highAux m 0 n

/-- `Σ c_i 2^(W κ_i)` -/
def pack (W : ℕ) : List ℤ → List ℕ → ℤ
  | a :: as, k :: ks => a * (2 : ℤ) ^ (W * k) + pack W as ks
  | _, _ => 0

/-- the base-`2^W` digits of `N` at the positions `ks`, minus `h` -/
def digits (W N h : ℕ) : List ℕ → List ℤ
  | [] => []
  | k :: ks => (((N >>> (W * k)) % 2 ^ W : ℕ) - (h : ℤ)) :: digits W N h ks

/-- Kronecker product: the coefficients of total degree `≤ DEG` (unscaled) and a bound for the
sum of the absolute values of the discarded products. -/
def kmul (p q : List ℤ) : List ℤ × ℕ :=
  let W := Nat.log2 (l1 p * l1 q) + 2
  let h : ℕ := 2 ^ (W - 1)
  let off : ℕ := h * ((2 ^ (W * NSLOT) - 1) / (2 ^ W - 1))
  let N := (pack W p KAPPA * pack W q KAPPA + off).toNat
  (digits W N h KAPPA, highBound (degNorms BLOCKS p) (degNorms BLOCKS q))

/-! ## Taylor models -/

/-- A Taylor model: coefficients on `MONO` and a remainder interval `[lo, hi]`, all in units
of `2^-P`. -/
structure TM where
  c : List ℤ
  lo : ℤ
  hi : ℤ

namespace TM

/-- `max |lo| |hi|` -/
def emax (t : TM) : ℕ := max t.lo.natAbs t.hi.natAbs

def add (t u : TM) : TM := ⟨addL t.c u.c, t.lo + u.lo, t.hi + u.hi⟩

def neg (t : TM) : TM := ⟨negL t.c, -t.hi, -t.lo⟩

def sub (t u : TM) : TM := t.add u.neg

/-- multiplication by an integer -/
def smul (k : ℤ) (t : TM) : TM :=
  if 0 ≤ k then ⟨smulL k t.c, k * t.lo, k * t.hi⟩ else ⟨smulL k t.c, k * t.hi, k * t.lo⟩

/-- the constant `m * 2^-P` -/
def const (m : ℤ) : TM := ⟨[m], 0, 0⟩

/-- an unknown constant in the rational interval `[a, b]` -/
def constI (a b : ℚ) : TM :=
  let m := qfloor (a * ONE)
  ⟨[m], 0, qceil (b * ONE) - m⟩

/-- the rational constant `x` -/
def ofq (x : ℚ) : TM := constI x x

/-- `mid + rad * x` (`var = 0`) or `mid + rad * y` (`var = 1`) -/
def affine (mid rad : ℚ) (var : ℕ) : TM :=
  let m0 := qfloor (mid * ONE)
  let m1 := qfloor (rad * ONE)
  let e0 : ℤ := if (m0 : ℚ) = mid * ONE then 0 else 1
  let e1 : ℤ := if (m1 : ℚ) = rad * ONE then 0 else 1
  ⟨if var = 0 then [m0, 0, m1] else [m0, m1], -e1, e0 + e1⟩

/-- multiplication by a rational; coefficients rounded down, `[-NM, NM]` added -/
def mulq (x : ℚ) (t : TM) : TM :=
  let n := x.num
  let d : ℤ := x.den
  let c := t.c.map (fun a => n * a / d)
  if 0 ≤ n then ⟨c, n * t.lo / d - NM, cdiv (n * t.hi) d + NM⟩
  else ⟨c, n * t.hi / d - NM, cdiv (n * t.lo) d + NM⟩

/-- product of two Taylor models -/
def mul (t u : TM) : TM :=
  let r := kmul t.c u.c
  let cross : ℕ := l1 t.c * u.emax + l1 u.c * t.emax + t.emax * u.emax
  let e : ℤ := NM + cdiv r.2 ONE + cdiv cross ONE
  ⟨r.1.map (fun a => a / ONE), -e, e⟩

def rngAux : List ℤ → List Bool → ℤ × ℤ
  | a :: as, ev :: evs =>
    let r := rngAux as evs
    if ev then (r.1 + min 0 a, r.2 + max 0 a) else (r.1 - a.natAbs, r.2 + a.natAbs)
  | _, _ => (0, 0)

/-- lower and upper bounds of `ONE * f` on the box -/
def rng (t : TM) : ℤ × ℤ :=
  match t.c with
  | a :: as => let r := rngAux as EVEN.tail; (a + r.1 + t.lo, a + r.2 + t.hi)
  | [] => (t.lo, t.hi)

def absmax (t : TM) : ℕ := max t.rng.1.natAbs t.rng.2.natAbs

def widen (t : TM) (e : ℤ) : TM := ⟨t.c, t.lo - e, t.hi + e⟩

/-- multiplication by an unknown constant in `[a, b]` -/
def mulI (t : TM) (a b : ℚ) : TM :=
  (mulq ((a + b) / 2) t).widen (qceil ((b - a) / 2 * t.absmax))

/-- the constant coefficient and the rest -/
def center (t : TM) : ℤ × TM :=
  match t.c with
  | a :: as => (a, ⟨0 :: as, t.lo, t.hi⟩)
  | [] => (0, t)

end TM

/-! ## Scalar enclosures -/

/-- `(Σ_{i<n} x^(i+1)/(i+1), |x|^(n+1)/(1-|x|))`: `|S + log (1 - x)| ≤ err` for `|x| < 1` -/
def log1mSeries (x : ℚ) (n : ℕ) : ℚ × ℚ :=
  let rec go : ℕ → ℕ → ℚ → ℚ → ℚ
    | 0, _, _, s => s
    | k + 1, i, p, s => go k (i + 1) (p * x) (s + p * x / (i + 1 : ℕ))
  (go n 0 1 0, |x| ^ (n + 1) / (1 - |x|))

/-- rational bounds of `log 2` (generated by the series at `x = 1/2` with 70 terms) -/
def LN2LO : ℚ := 837963523372001241318869 / 1208925819614629174706176
def LN2HI : ℚ := 418981761686000620660459 / 604462909807314587353088

/-- `c = 2^k m` with `m ∈ [2/3, 4/3]` (for `c > 0`) -/
def logScale (c : ℚ) : ℤ × ℚ :=
  let k0 : ℤ := (Nat.log2 c.num.toNat : ℤ) - (Nat.log2 c.den : ℤ)
  let m0 : ℚ := c / (2 : ℚ) ^ k0
  if m0 < 2 / 3 then (k0 - 1, m0 * 2) else if 4 / 3 < m0 then (k0 + 1, m0 / 2) else (k0, m0)

/-- bounds of `k log 2 + log m` -/
def logBounds (k : ℤ) (m : ℚ) : ℚ × ℚ :=
  let s := log1mSeries (1 - m) 40
  if 0 ≤ k then (k * LN2LO - s.1 - s.2, k * LN2HI - s.1 + s.2)
  else (k * LN2HI - s.1 - s.2, k * LN2LO - s.1 + s.2)

/-- a rational interval containing `log c`, for a rational `c > 0` -/
def logI (c : ℚ) : Option (ℚ × ℚ) :=
  if c ≤ 0 then none else
  if 1 / 2 < |1 - (logScale c).2| then none else some (logBounds (logScale c).1 (logScale c).2)

/-- `Σ_{i<n} y^i / i!` -/
def expSum (y : ℚ) (n : ℕ) : ℚ :=
  let rec go : ℕ → ℕ → ℚ → ℚ → ℚ
    | 0, _, _, s => s
    | k + 1, i, p, s => let p' := p * y / (i + 1 : ℕ); go k (i + 1) p' (s + p')
  go (n - 1) 0 1 1

/-- a rational interval containing `2^c` -/
def exp2I (c : ℚ) : ℚ × ℚ :=
  let k := qfloor c
  let f := c - k
  let g : ℚ := 1208925819614629174706176
  let ylo : ℚ := qfloor (f * LN2LO * g) / g
  let yhi : ℚ := qceil (f * LN2HI * g) / g
  let lo := expSum ylo 25
  let hi := expSum yhi 25 + yhi ^ 25 * 26 / (15511210043330985984000000 * 25)
  ((2 : ℚ) ^ k * lo, (2 : ℚ) ^ k * hi)

/-! ## Reciprocal, logarithm and exponential of Taylor models -/

namespace TM

/-- `Σ_{k ≤ n} q^k` from `term = q^0 = 1` -/
def recipSeries (q : TM) : ℕ → TM → TM → TM
  | 0, _, out => out
  | k + 1, term, out => let term' := term.mul q; recipSeries q k term' (out.add term')

def recip (t : TM) : Option TM :=
  let cd := t.center
  if cd.1 = 0 then none else
  let q := mulq ((-ONE : ℚ) / cd.1) cd.2
  let M := q.absmax
  if (ONE : ℤ) ≤ M then none else
  let out := mulq ((ONE : ℚ) / cd.1) (recipSeries q NS (const ONE) (const ONE))
  let Mq : ℚ := (M : ℚ) / ONE
  some (out.widen (qceil (Mq ^ (NS + 1) / (1 - Mq) / |((cd.1 : ℚ) / ONE)| * ONE)))

/-- `Σ_{i=1}^{n} (-1)^(i+1) q^i / i` from `term = q` -/
def logSeries (q : TM) : ℕ → ℕ → TM → TM → TM
  | 0, _, _, out => out
  | k + 1, i, term, out =>
    let term' := term.mul q
    logSeries q k (i + 1) term' (out.add (mulq ((-1) ^ (i + 1) / (i : ℚ)) term'))

def log2 (t : TM) : Option TM :=
  let cd := t.center
  if cd.1 ≤ 0 then none else
  let q := mulq ((ONE : ℚ) / cd.1) cd.2
  let M := q.absmax
  if (ONE : ℤ) ≤ M then none else
  match logI ((cd.1 : ℚ) / ONE) with
  | none => none
  | some l =>
    let out := logSeries q (NS - 1) 2 q q
    let Mq : ℚ := (M : ℚ) / ONE
    let err := qceil (Mq ^ (NS + 1) / (1 - Mq) / (NS + 1 : ℕ) * ONE)
    some (((out.widen err).add (constI l.1 l.2)).mulI (1 / LN2HI) (1 / LN2LO))

/-- `Σ_{i=0}^{n} q^i / i!` from `term = 1` -/
def expSeries (q : TM) : ℕ → ℕ → TM → TM → TM
  | 0, _, _, out => out
  | k + 1, i, term, out =>
    let term' := mulq (1 / (i : ℚ)) (term.mul q)
    expSeries q k (i + 1) term' (out.add term')

def exp2 (t : TM) : Option TM :=
  let cd := t.center
  let q := cd.2.mulI LN2LO LN2HI
  let M := q.absmax
  if (ONE : ℤ) < M then none else
  let out := expSeries q NS 1 (const ONE) (const ONE)
  let Mq : ℚ := (M : ℚ) / ONE
  let err := qceil (Mq ^ (NS + 1) * (NS + 2 : ℕ) / ((Nat.factorial (NS + 1) : ℚ) * (NS + 1 : ℕ)) * ONE)
  let e := exp2I ((cd.1 : ℚ) / ONE)
  some ((out.widen err).mulI e.1 e.2)

end TM

end OM.NNN20
