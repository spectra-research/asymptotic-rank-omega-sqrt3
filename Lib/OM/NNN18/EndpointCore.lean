import Mathlib

/-! # Univariate positivity lemmas for the endpoint polynomials (PACKED_TABLES (P4)-(P11))

Polynomials are coefficient lists in increasing degree, `peval [c₀,c₁,…] x = c₀ + x(c₁ + …)`.

* `peval_ge_head_sub`: on `|x| ≤ 1`, `p ≥ c₀ - Σ_{i≥1} |c_i|` ((P4), (P5)).
* `quad_pos`: `A > 0`, `a₁² < 4 A a₀` give `a₀ + a₁ d + A d² > 0` (the discriminant gates).
* `neg_half_bound` (P7), `pos_small_bound` (P8), `sym_bound` (P11): quadratic minorants of a
  polynomial whose coefficients from degree 6 (resp. 5) on lie in `[-1, 1]`.
* `pos_of_concave_gate` (P9)-(P10): a negative bound on the second derivative over `[α, R]`
  gives concavity, hence positivity from the two endpoint values. -/

noncomputable section
open Set
namespace OM.NNN18

def peval : List ℚ → ℝ → ℝ
  | [], _ => 0
  | c :: cs, x => (c : ℝ) + x * peval cs x

def absSum (cs : List ℚ) : ℚ := (cs.map fun c => |c|).sum

lemma abs_peval_le (cs : List ℚ) {x : ℝ} (hx : |x| ≤ 1) :
    |peval cs x| ≤ ((absSum cs : ℚ) : ℝ) := by
  induction cs with
  | nil => simp [peval, absSum]
  | cons c cs ih =>
    have e : ((absSum (c :: cs) : ℚ) : ℝ) = |(c : ℝ)| + ((absSum cs : ℚ) : ℝ) := by
      simp [absSum]
    rw [e]
    simp only [peval]
    calc |(c : ℝ) + x * peval cs x| ≤ |(c : ℝ)| + |x| * |peval cs x| := by
          rw [← abs_mul]; exact abs_add_le _ _
      _ ≤ |(c : ℝ)| + 1 * ((absSum cs : ℚ) : ℝ) := by
          gcongr
      _ = _ := by ring

/-- (P4)/(P5): `c₀ - Σ_{i≥1}|c_i|` is a lower bound on `|x| ≤ 1`. -/
theorem peval_ge_head_sub (c : ℚ) (cs : List ℚ) {x : ℝ} (hx : |x| ≤ 1) :
    ((c - absSum cs : ℚ) : ℝ) ≤ peval (c :: cs) x := by
  have h := abs_peval_le cs hx
  have hm : |x * peval cs x| ≤ ((absSum cs : ℚ) : ℝ) := by
    rw [abs_mul]
    calc |x| * |peval cs x| ≤ 1 * |peval cs x| := by gcongr
      _ ≤ _ := by rw [one_mul]; exact h
  simp only [peval]
  push_cast
  linarith [neg_abs_le (x * peval cs x)]

/-- The discriminant gate. -/
theorem quad_pos {a₀ a₁ A : ℝ} (hA : 0 < A) (hdisc : a₁ ^ 2 < 4 * A * a₀) (d : ℝ) :
    0 < a₀ + a₁ * d + A * d ^ 2 := by
  have e : 4 * A * (a₀ + a₁ * d + A * d ^ 2) = (2 * A * d + a₁) ^ 2 + (4 * A * a₀ - a₁ ^ 2) := by
    ring
  have h : 0 < 4 * A * (a₀ + a₁ * d + A * d ^ 2) := by
    rw [e]; nlinarith [sq_nonneg (2 * A * d + a₁)]
  by_contra hc
  push_neg at hc
  nlinarith

/-- A tail with coefficients in `[-1,1]`: `|peval cs x| ≤ 1/(1-|x|)`. -/
lemma abs_peval_le_geom (cs : List ℚ) (hc : ∀ c ∈ cs, |c| ≤ 1) {x : ℝ} (hx : |x| < 1) :
    |peval cs x| ≤ 1 / (1 - |x|) := by
  have hpos : 0 < 1 - |x| := by linarith
  induction cs with
  | nil => simp only [peval, abs_zero]; positivity
  | cons c cs ih =>
    have hc0 : |(c : ℝ)| ≤ 1 := by
      have := hc c List.mem_cons_self; exact_mod_cast this
    have ih' := ih (fun c' hc' => hc c' (List.mem_cons_of_mem _ hc'))
    simp only [peval]
    calc |(c : ℝ) + x * peval cs x| ≤ |(c : ℝ)| + |x| * |peval cs x| := by
          rw [← abs_mul]; exact abs_add_le _ _
      _ ≤ 1 + |x| * (1 / (1 - |x|)) := by gcongr
      _ = 1 / (1 - |x|) := by field_simp; ring

/-- `x^m · tail ≥ -(r^(m-2)/(1-r)) x²` for `|x| ≤ r < 1`, `m ≥ 2`. -/
lemma tail_lower (m : ℕ) (hm : 2 ≤ m) {t : List ℚ} (ht : ∀ c ∈ t, |c| ≤ 1) {x r : ℝ}
    (hr1 : r < 1) (hx : |x| ≤ r) : -(r ^ (m - 2) / (1 - r)) * x ^ 2 ≤ x ^ m * peval t x := by
  have hr0 : 0 ≤ r := (abs_nonneg x).trans hx
  have hx1 : |x| < 1 := lt_of_le_of_lt hx hr1
  have hg := abs_peval_le_geom t ht hx1
  have hpos : 0 < 1 - |x| := by linarith
  have hpos' : 0 < 1 - r := by linarith
  -- |x^m peval| ≤ |x|^m/(1-|x|) ≤ r^(m-2) x²/(1-r)
  have h1 : |x ^ m * peval t x| ≤ |x| ^ m * (1 / (1 - |x|)) := by
    rw [abs_mul, abs_pow]; gcongr
  have hsplit : |x| ^ m = |x| ^ (m - 2) * x ^ 2 := by
    rw [← sq_abs, ← pow_add]; congr 1; omega
  have h2 : |x| ^ m * (1 / (1 - |x|)) ≤ r ^ (m - 2) / (1 - r) * x ^ 2 := by
    rw [hsplit]
    have hp : |x| ^ (m - 2) ≤ r ^ (m - 2) := pow_le_pow_left₀ (abs_nonneg x) hx _
    have hi : 1 / (1 - |x|) ≤ 1 / (1 - r) := one_div_le_one_div_of_le hpos' (by linarith)
    calc |x| ^ (m - 2) * x ^ 2 * (1 / (1 - |x|)) ≤ r ^ (m - 2) * x ^ 2 * (1 / (1 - r)) := by
          gcongr
      _ = r ^ (m - 2) / (1 - r) * x ^ 2 := by ring
  have := neg_abs_le (x ^ m * peval t x)
  linarith

lemma peval_six (a₀ a₁ a₂ a₃ a₄ a₅ : ℚ) (t : List ℚ) (x : ℝ) :
    peval (a₀ :: a₁ :: a₂ :: a₃ :: a₄ :: a₅ :: t) x =
      a₀ + a₁ * x + a₂ * x ^ 2 + a₃ * x ^ 3 + a₄ * x ^ 4 + a₅ * x ^ 5 + x ^ 6 * peval t x := by
  simp only [peval]; ring

lemma peval_five (a₀ a₁ a₂ a₃ a₄ : ℚ) (t : List ℚ) (x : ℝ) :
    peval (a₀ :: a₁ :: a₂ :: a₃ :: a₄ :: t) x =
      a₀ + a₁ * x + a₂ * x ^ 2 + a₃ * x ^ 3 + a₄ * x ^ 4 + x ^ 5 * peval t x := by
  simp only [peval]; ring

/-- (P7): on `d = -x`, `0 ≤ x ≤ r < 1`, with `a₃ ≤ 0 ≤ a₄`, `a₅ ≤ 0`. -/
theorem neg_half_bound {a₀ a₁ a₂ a₃ a₄ a₅ : ℚ} {t : List ℚ} (ht : ∀ c ∈ t, |c| ≤ 1)
    (h3 : a₃ ≤ 0) (h4 : 0 ≤ a₄) (h5 : a₅ ≤ 0) {r d : ℝ} (hr1 : r < 1) (hd₁ : -r ≤ d)
    (hd₂ : d ≤ 0) :
    (a₀ : ℝ) + a₁ * d + (a₂ - r ^ 4 / (1 - r)) * d ^ 2 ≤
      peval (a₀ :: a₁ :: a₂ :: a₃ :: a₄ :: a₅ :: t) d := by
  rw [peval_six]
  have hx : |d| ≤ r := by rw [abs_of_nonpos hd₂]; linarith
  have ht6 := tail_lower 6 (by norm_num) ht hr1 hx
  have e3 : (0 : ℝ) ≤ a₃ * d ^ 3 := by
    have : d ^ 3 ≤ 0 := Odd.pow_nonpos (by decide +kernel) hd₂
    exact mul_nonneg_of_nonpos_of_nonpos (by exact_mod_cast h3) this
  have e4 : (0 : ℝ) ≤ a₄ * d ^ 4 := mul_nonneg (by exact_mod_cast h4) (by positivity)
  have e5 : (0 : ℝ) ≤ a₅ * d ^ 5 := by
    have : d ^ 5 ≤ 0 := Odd.pow_nonpos (by decide +kernel) hd₂
    exact mul_nonneg_of_nonpos_of_nonpos (by exact_mod_cast h5) this
  norm_num at ht6
  nlinarith [ht6]

/-- (P8): on `0 ≤ d ≤ r < 1`, with `a₄ ≥ 0`. -/
theorem pos_small_bound {a₀ a₁ a₂ a₃ a₄ a₅ : ℚ} {t : List ℚ} (ht : ∀ c ∈ t, |c| ≤ 1)
    (h4 : 0 ≤ a₄) {r d : ℝ} (hr1 : r < 1) (hd₁ : 0 ≤ d) (hd₂ : d ≤ r) :
    (a₀ : ℝ) + a₁ * d + (a₂ - |(a₃ : ℝ)| * r - |(a₅ : ℝ)| * r ^ 3 - r ^ 4 / (1 - r)) * d ^ 2 ≤
      peval (a₀ :: a₁ :: a₂ :: a₃ :: a₄ :: a₅ :: t) d := by
  rw [peval_six]
  have hx : |d| ≤ r := by rw [abs_of_nonneg hd₁]; exact hd₂
  have ht6 := tail_lower 6 (by norm_num) ht hr1 hx
  have hd2 : 0 ≤ d ^ 2 := sq_nonneg d
  have e3 : -(|(a₃ : ℝ)| * r) * d ^ 2 ≤ a₃ * d ^ 3 := by
    have h1 : -(|(a₃ : ℝ)|) * d ^ 3 ≤ a₃ * d ^ 3 :=
      mul_le_mul_of_nonneg_right (neg_abs_le _) (by positivity)
    have h2 : |(a₃ : ℝ)| * d ^ 3 ≤ |(a₃ : ℝ)| * r * d ^ 2 := by
      have : d ^ 3 = d * d ^ 2 := by ring
      rw [this]
      have := mul_le_mul_of_nonneg_right hd₂ hd2
      nlinarith [abs_nonneg (a₃ : ℝ)]
    linarith
  have e4 : (0 : ℝ) ≤ a₄ * d ^ 4 := mul_nonneg (by exact_mod_cast h4) (by positivity)
  have e5 : -(|(a₅ : ℝ)| * r ^ 3) * d ^ 2 ≤ a₅ * d ^ 5 := by
    have h1 : -(|(a₅ : ℝ)|) * d ^ 5 ≤ a₅ * d ^ 5 :=
      mul_le_mul_of_nonneg_right (neg_abs_le _) (by positivity)
    have h2 : |(a₅ : ℝ)| * d ^ 5 ≤ |(a₅ : ℝ)| * r ^ 3 * d ^ 2 := by
      have : d ^ 5 = d ^ 3 * d ^ 2 := by ring
      rw [this]
      have h3 : d ^ 3 ≤ r ^ 3 := pow_le_pow_left₀ hd₁ hd₂ 3
      have := mul_le_mul_of_nonneg_right h3 hd2
      nlinarith [abs_nonneg (a₅ : ℝ)]
    linarith
  norm_num at ht6
  nlinarith [ht6]

/-- (P11): on `|d| ≤ R < 1`, coefficients from degree five on in `[-1, 1]`. -/
theorem sym_bound {a₀ a₁ a₂ a₃ a₄ : ℚ} {t : List ℚ} (ht : ∀ c ∈ t, |c| ≤ 1)
    {R d : ℝ} (hR1 : R < 1) (hd : |d| ≤ R) :
    (a₀ : ℝ) + a₁ * d + (a₂ - |(a₃ : ℝ)| * R - |(a₄ : ℝ)| * R ^ 2 - R ^ 3 / (1 - R)) * d ^ 2 ≤
      peval (a₀ :: a₁ :: a₂ :: a₃ :: a₄ :: t) d := by
  rw [peval_five]
  have ht5 := tail_lower 5 (by norm_num) ht hR1 hd
  have hd2 : 0 ≤ d ^ 2 := sq_nonneg d
  have hda : |d| ^ 2 = d ^ 2 := sq_abs d
  have e3 : -(|(a₃ : ℝ)| * R) * d ^ 2 ≤ a₃ * d ^ 3 := by
    have h1 : |(a₃ : ℝ) * d ^ 3| ≤ |(a₃ : ℝ)| * R * d ^ 2 := by
      rw [abs_mul, abs_pow, show |d| ^ 3 = |d| * |d| ^ 2 by ring, hda]
      have := mul_le_mul_of_nonneg_right hd hd2
      nlinarith [abs_nonneg (a₃ : ℝ)]
    linarith [neg_abs_le ((a₃ : ℝ) * d ^ 3)]
  have e4 : -(|(a₄ : ℝ)| * R ^ 2) * d ^ 2 ≤ a₄ * d ^ 4 := by
    have h1 : |(a₄ : ℝ) * d ^ 4| ≤ |(a₄ : ℝ)| * R ^ 2 * d ^ 2 := by
      rw [abs_mul, abs_pow, show |d| ^ 4 = |d| ^ 2 * |d| ^ 2 by ring, hda]
      have h2 : |d| ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (abs_nonneg d) hd 2
      rw [hda] at h2
      have := mul_le_mul_of_nonneg_right h2 hd2
      nlinarith [abs_nonneg (a₄ : ℝ)]
    linarith [neg_abs_le ((a₄ : ℝ) * d ^ 4)]
  norm_num at ht5
  nlinarith [ht5]

/-! ## Derivatives of list polynomials and the concavity gate -/

def ladd : List ℚ → List ℚ → List ℚ
  | [], b => b
  | a, [] => a
  | a :: as, b :: bs => (a + b) :: ladd as bs

lemma peval_ladd (a b : List ℚ) (x : ℝ) : peval (ladd a b) x = peval a x + peval b x := by
  induction a generalizing b with
  | nil => simp [ladd, peval]
  | cons a as ih =>
    cases b with
    | nil => simp [ladd, peval]
    | cons b bs => simp only [ladd, peval, Rat.cast_add, ih]; ring

/-- Formal derivative: `(c + x q)' = q + x q'`. -/
def pderiv : List ℚ → List ℚ
  | [] => []
  | _ :: cs => ladd cs (0 :: pderiv cs)

lemma hasDerivAt_peval (cs : List ℚ) (x : ℝ) :
    HasDerivAt (peval cs) (peval (pderiv cs) x) x := by
  induction cs with
  | nil => simpa [peval, pderiv] using hasDerivAt_const x (0 : ℝ)
  | cons c cs ih =>
    have h := ((hasDerivAt_id x).mul ih).const_add (c : ℝ)
    have e : peval (pderiv (c :: cs)) x = peval cs x + x * peval (pderiv cs) x := by
      simp [pderiv, peval_ladd, peval]
    rw [e]
    convert! h using 1
    simp

/-- Upper bound on `[0, R]` by the positive parts at `R`. -/
def posPart (cs : List ℚ) : List ℚ := cs.map fun c => max c 0

lemma peval_le_posPart (cs : List ℚ) {x R : ℝ} (hx₀ : 0 ≤ x) (hxR : x ≤ R) :
    peval cs x ≤ peval (posPart cs) R := by
  induction cs with
  | nil => simp [peval, posPart]
  | cons c cs ih =>
    have hR0 : 0 ≤ R := hx₀.trans hxR
    have hpos : 0 ≤ peval (posPart cs) R := by
      clear ih
      induction cs with
      | nil => simp [peval, posPart]
      | cons c' cs' ih' =>
        simp only [posPart, List.map_cons, peval] at ih' ⊢
        have : (0 : ℝ) ≤ ((max c' 0 : ℚ) : ℝ) := by exact_mod_cast le_max_right c' 0
        have := ih'
        positivity
    simp only [posPart, List.map_cons, peval] at ih hpos ⊢
    have hc : (c : ℝ) ≤ ((max c 0 : ℚ) : ℝ) := by exact_mod_cast le_max_left c 0
    have h1 : x * peval cs x ≤ x * peval (List.map (fun c => max c 0) cs) R :=
      mul_le_mul_of_nonneg_left ih hx₀
    have h2 : x * peval (List.map (fun c => max c 0) cs) R ≤
        R * peval (List.map (fun c => max c 0) cs) R := mul_le_mul_of_nonneg_right hxR hpos
    linarith

lemma peval_three (b₀ b₁ b₂ : ℚ) (t : List ℚ) (x : ℝ) :
    peval (b₀ :: b₁ :: b₂ :: t) x = b₀ + b₁ * x + b₂ * x ^ 2 + x ^ 3 * peval t x := by
  simp only [peval]; ring

/-- Rational evaluation, for kernel checks. -/
def pevalQ : List ℚ → ℚ → ℚ
  | [], _ => 0
  | c :: cs, x => c + x * pevalQ cs x

lemma pevalQ_cast (cs : List ℚ) (q : ℚ) : ((pevalQ cs q : ℚ) : ℝ) = peval cs q := by
  induction cs with
  | nil => simp [pevalQ, peval]
  | cons c cs ih => simp [pevalQ, peval, ih]

lemma peval_posPart_nonneg (t : List ℚ) {R : ℝ} (hR : 0 ≤ R) : 0 ≤ peval (posPart t) R := by
  induction t with
  | nil => simp [peval, posPart]
  | cons c t ih =>
    simp only [posPart, List.map_cons, peval] at ih ⊢
    have : (0 : ℝ) ≤ ((max c 0 : ℚ) : ℝ) := by exact_mod_cast le_max_right c 0
    have := ih
    positivity

/-- A convex quadratic is below its larger endpoint value on `[α, R]`. -/
lemma quad_le_max {b₀ b₁ b₂ α R x : ℝ} (hb₂ : 0 ≤ b₂) (hx₁ : α ≤ x) (hx₂ : x ≤ R) :
    b₀ + b₁ * x + b₂ * x ^ 2 ≤ max (b₀ + b₁ * α + b₂ * α ^ 2) (b₀ + b₁ * R + b₂ * R ^ 2) := by
  rcases eq_or_lt_of_le (hx₁.trans hx₂) with heq | hlt
  · have h1 : x = α := by linarith
    rw [h1]; exact le_max_left _ _
  · have key : (R - α) * (b₀ + b₁ * x + b₂ * x ^ 2) =
        (R - x) * (b₀ + b₁ * α + b₂ * α ^ 2) + (x - α) * (b₀ + b₁ * R + b₂ * R ^ 2)
          - (R - α) * b₂ * ((x - α) * (R - x)) := by ring
    have hb : 0 ≤ (R - α) * b₂ * ((x - α) * (R - x)) := by
      have := mul_nonneg (sub_nonneg.2 hx₁) (sub_nonneg.2 hx₂)
      have : 0 ≤ R - α := by linarith
      positivity
    set M := max (b₀ + b₁ * α + b₂ * α ^ 2) (b₀ + b₁ * R + b₂ * R ^ 2)
    have t1 := mul_le_mul_of_nonneg_left (le_max_left (b₀ + b₁ * α + b₂ * α ^ 2)
      (b₀ + b₁ * R + b₂ * R ^ 2)) (sub_nonneg.2 hx₂)
    have t2 := mul_le_mul_of_nonneg_left (le_max_right (b₀ + b₁ * α + b₂ * α ^ 2)
      (b₀ + b₁ * R + b₂ * R ^ 2)) (sub_nonneg.2 hx₁)
    have hRα : 0 < R - α := by linarith
    have : (R - α) * (b₀ + b₁ * x + b₂ * x ^ 2) ≤ (R - α) * M := by
      rw [key]; nlinarith
    exact le_of_mul_le_mul_left this hRα

/-- (P9)-(P10): if the second derivative `b₀ + b₁ x + b₂ x² + x³·rest` satisfies
`max(q(α), q(R)) + R³·rest⁺(R) < 0` with `b₂ ≥ 0`, then `p` is concave on `[α, R]`, hence
positive there when it is positive at both ends. -/
theorem pos_of_concave_gate (cs : List ℚ) {b₀ b₁ b₂ : ℚ} {t : List ℚ}
    (hdd : pderiv (pderiv cs) = b₀ :: b₁ :: b₂ :: t) (hb₂ : 0 ≤ b₂)
    {α R : ℚ} (hα : 0 ≤ α)
    (hgate : max (b₀ + b₁ * α + b₂ * α ^ 2) (b₀ + b₁ * R + b₂ * R ^ 2)
      + R ^ 3 * pevalQ (posPart t) R < 0)
    (hpα : 0 < pevalQ cs α) (hpR : 0 < pevalQ cs R) {d : ℝ} (hd₁ : (α : ℝ) ≤ d)
    (hd₂ : d ≤ R) : 0 < peval cs d := by
  have hgR : ((max (b₀ + b₁ * α + b₂ * α ^ 2) (b₀ + b₁ * R + b₂ * R ^ 2)
      + R ^ 3 * pevalQ (posPart t) R : ℚ) : ℝ) < 0 := by exact_mod_cast hgate
  push_cast [pevalQ_cast] at hgR
  have hconc : ConcaveOn ℝ (Icc (α : ℝ) R) (peval cs) := by
    apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc _ _)
      (f' := peval (pderiv cs)) (f'' := peval (pderiv (pderiv cs)))
    · exact fun x _ => (hasDerivAt_peval cs x).continuousAt.continuousWithinAt
    · exact fun x _ => (hasDerivAt_peval cs x).hasDerivWithinAt
    · exact fun x _ => (hasDerivAt_peval (pderiv cs) x).hasDerivWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      have hα' : (0 : ℝ) ≤ α := by exact_mod_cast hα
      have hx0 : (0 : ℝ) ≤ x := le_trans hα' hx.1.le
      rw [hdd, peval_three]
      have hq := quad_le_max (b₀ := (b₀ : ℝ)) (b₁ := b₁) (b₂ := (b₂ : ℝ)) (by exact_mod_cast hb₂) hx.1.le hx.2.le
      have h1 := peval_le_posPart t hx0 hx.2.le
      have hp := peval_posPart_nonneg t (show (0 : ℝ) ≤ R by linarith [hx.2])
      have hx3 : x ^ 3 ≤ (R : ℝ) ^ 3 := pow_le_pow_left₀ hx0 hx.2.le 3
      have hrest : x ^ 3 * peval t x ≤ (R : ℝ) ^ 3 * peval (posPart t) R :=
        calc x ^ 3 * peval t x ≤ x ^ 3 * peval (posPart t) R :=
              mul_le_mul_of_nonneg_left h1 (by positivity)
          _ ≤ (R : ℝ) ^ 3 * peval (posPart t) R := mul_le_mul_of_nonneg_right hx3 hp
      linarith
  have hpα' : 0 < peval cs α := by rw [← pevalQ_cast]; exact_mod_cast hpα
  have hpR' : 0 < peval cs R := by rw [← pevalQ_cast]; exact_mod_cast hpR
  have hαR : (α : ℝ) ≤ R := hd₁.trans hd₂
  have hmin := hconc.min_le_of_mem_Icc (left_mem_Icc.2 hαR) (right_mem_Icc.2 hαR) ⟨hd₁, hd₂⟩
  exact lt_of_lt_of_le (lt_min hpα' hpR') hmin

end OM.NNN18
