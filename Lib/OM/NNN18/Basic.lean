import Mathlib

/-!
  (b·x) F + Σ_i (θ_i/β_i) (b·x - [i=h] 6 x_h) (F - P_i·x)
          - Σ_i θ_i (b_j+b_k) x_j x_k - Σ_i θ_i ν_i x_j x_k L_i,
-/

noncomputable section
open scoped BigOperators
namespace OM.NNN18

/-- Ownership weights, 6 at the focus and 5 elsewhere. -/
def own (h u : Fin 3) : ℝ := if u = h then 6 else 5

def dot (p x : Fin 3 → ℝ) : ℝ := p 0 * x 0 + p 1 * x 1 + p 2 * x 2

/-- `pp x i = x_j x_k` for `{i,j,k} = {0,1,2}`. -/
def pp (x : Fin 3 → ℝ) : Fin 3 → ℝ := ![x 1 * x 2, x 0 * x 2, x 0 * x 1]

/-- The sum of the two off-diagonal entries of a row: `P_ij + P_ik`. -/
def cross (p : Fin 3 → ℝ) : Fin 3 → ℝ := ![p 1 + p 2, p 0 + p 2, p 0 + p 1]

def nu (h i : Fin 3) : ℝ := if i = h then 10 / 11 else 1

/-- The global source form at focus `h`. -/
def form (h : Fin 3) (θ β : Fin 3 → ℝ) (P : Fin 3 → Fin 3 → ℝ) (L : Fin 3 → ℝ)
    (F : ℝ) (x : Fin 3 → ℝ) : ℝ :=
  dot (own h) x * F
    + ∑ i, θ i / β i * (dot (own h) x - if i = h then 6 * x h else 0) * (F - dot (P i) x)
    - ∑ i, θ i * (16 - own h i) * pp x i
    - ∑ i, θ i * nu h i * pp x i * L i

/-- The form at focus 0, written out. -/
def form0 (θ β : Fin 3 → ℝ) (P : Fin 3 → Fin 3 → ℝ) (L : Fin 3 → ℝ)
    (F : ℝ) (x : Fin 3 → ℝ) : ℝ :=
  (6 * x 0 + 5 * x 1 + 5 * x 2) * F
    + θ 0 / β 0 * (5 * x 1 + 5 * x 2) * (F - dot (P 0) x)
    + θ 1 / β 1 * (6 * x 0 + 5 * x 1 + 5 * x 2) * (F - dot (P 1) x)
    + θ 2 / β 2 * (6 * x 0 + 5 * x 1 + 5 * x 2) * (F - dot (P 2) x)
    - (10 * θ 0 * (x 1 * x 2) + 11 * θ 1 * (x 0 * x 2) + 11 * θ 2 * (x 0 * x 1))
    - (10 / 11 * θ 0 * (x 1 * x 2) * L 0 + θ 1 * (x 0 * x 2) * L 1
        + θ 2 * (x 0 * x 1) * L 2)

lemma form_zero (θ β : Fin 3 → ℝ) (P : Fin 3 → Fin 3 → ℝ) (L : Fin 3 → ℝ)
    (F : ℝ) (x : Fin 3 → ℝ) : form 0 θ β P L F x = form0 θ β P L F x := by
  simp only [form, form0, Fin.sum_univ_three, own, nu, pp, dot, Fin.isValue,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, ↓reduceIte, ite_true, ite_false,
    show (1 : Fin 3) = 0 ↔ False by decide, show (2 : Fin 3) = 0 ↔ False by decide +kernel]
  ring


structure Track where
  t : ℚ
  R : ℚ
  u : ℚ
  v : ℚ
  a : ℚ
  b : ℚ
  c : ℚ
  v0 : ℚ
  /-- moment constants: 0 retained, 1 ordinary side, 2 packed side -/
  A0 : Fin 3 → ℚ
  A1 : Fin 3 → ℚ

/-- Unconditional track (Ω = 9/4). -/
def U : Track where
  t := 3 / 4
  R := 10001 / 100000
  u := 40271 / 100000
  v := 49864 / 100000
  a := 70658 / 100000
  b := 3012 / 10000
  c := 38569 / 100000
  v0 := 49895 / 100000
  A0 := ![-1826118 / 1000000, -657845 / 1000000, -749225 / 1000000]
  A1 := ![2032957 / 1000000, 2569711 / 1000000, 2541575 / 1000000]

/-- The track under ω = 2 (Ω = 2). -/
def C : Track where
  t := 2 / 3
  R := 2503 / 30000
  u := 3637 / 10000
  v := 4431 / 10000
  a := 65 / 100
  b := 275 / 1000
  c := 375 / 1000
  v0 := 442 / 1000
  A0 := ![-1652074 / 1000000, -578944 / 1000000, -740719 / 1000000]
  A1 := ![15 / 7, 2592611 / 1000000, 2544270 / 1000000]

namespace Track

def z0 (P : Track) : Fin 3 → ℚ := ![-P.t, P.t - 2 * P.v0, 2 * (P.t - 2 * P.v0) / (P.t + 2 * P.v0)]

/-- Moment curvature coefficients: 39/50, 39/50, 11/20. -/
def K : Fin 3 → ℚ := ![39 / 50, 39 / 50, 11 / 20]

def Lmaj (P : Track) (k : Fin 3) (z : ℝ) : ℝ :=
  (P.A0 k : ℝ) + P.A1 k * (z - P.z0 k) + K k * (z - P.z0 k) ^ 2

/-- The cube target `u + 2v`. -/
def B (P : Track) : ℚ := P.u + 2 * P.v

end Track

/-- The third index: `other h j` for `h ≠ j`. -/
def other : Fin 3 → Fin 3 → Fin 3 := ![![0, 2, 1], ![2, 1, 0], ![1, 0, 2]]

def tariff (P : Track) (δ : Fin 3 → ℝ) (h j : Fin 3) : ℝ :=
  if j = h then (P.u : ℝ) - P.a * δ h
  else (P.v : ℝ) + P.b * δ h - P.c * (δ j - δ (other h j))

def star (θ : Fin 3 → ℝ) (h j : Fin 3) : ℝ := if j = h then 0 else θ (other h j)

/-- Focus-0 coordinates `d = δ_0`, `y = δ_1 - δ_2` on the plane `Σ δ = 0`. -/
def delta (d y : ℝ) : Fin 3 → ℝ := ![d, (y - d) / 2, (-d - y) / 2]

/-- The upper profile `θ = t + δ`. -/
def theta (P : Track) (δ : Fin 3 → ℝ) : Fin 3 → ℝ := fun i => (P.t : ℝ) + δ i

end OM.NNN18
