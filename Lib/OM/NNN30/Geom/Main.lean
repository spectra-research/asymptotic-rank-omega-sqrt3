import Lib.OM.NNN30.Geom.Plane
import PLATFORM.Statements.«R111.1»

/-! # R111.1: the angle condition (14)

`proof_R111_1 : S_R111_1`.  For two terminals with positive radii `a = d(o,pa)`, `b = d(o,pb)`,
the quadrant lemma applied to the plane of `GPlane` gives `N z z' ^ 2 = Φ(z' - z)` with
`Φ(w) = w₁² a² + w₁ w₂ (a² + b² - δ²) + w₂² b²`.  At `z = (1/a, 1/b)` the Fermat inequality in the
cone, `R (a + b) ≤ N z (R,0) + N z (0,R) + N z 0` for `R = 2^K`, forces
`u = (a² + b² - δ²)/(ab) ≤ -1` (`endgame`; equivalently, `t ≥ t²` with `t² = 2 + u`), i.e.
`δ² ≥ a² + ab + b²`; and `δ ≤ d(pa, pb)`.  A zero radius is handled by the triangle inequality. -/

noncomputable section

namespace OM.NNN30.Geom

/-- The first-variation estimate at `R = 2^K → ∞`: with `p3² = 2 + u`, the
inequalities force `u ≤ -1`. -/
lemma endgame {a b u p3 : ℝ} (ha : 0 < a) (hb : 0 < b) (hp3 : 0 ≤ p3) (hp3sq : p3 ^ 2 = 2 + u)
    (hF : ∀ K : ℕ, ∃ p1 p2 : ℝ, 0 ≤ p1 ∧ 0 ≤ p2 ∧
      p1 ^ 2 = (2 ^ K * a - 1) ^ 2 - u * (2 ^ K * a - 1) + 1 ∧
      p2 ^ 2 = (2 ^ K * b - 1) ^ 2 - u * (2 ^ K * b - 1) + 1 ∧
      2 ^ K * (a + b) ≤ p1 + p2 + p3) : u ≤ -1 := by
  by_contra hu
  replace hu := not_le.1 hu
  have hp3g : 1 < p3 := by nlinarith
  have hη : 0 < p3 ^ 2 - p3 := by nlinarith
  obtain ⟨K, hK⟩ := pow_unbounded_of_one_lt ((1 + |u| + 1 / (p3 ^ 2 - p3)) * (1 / a + 1 / b))
    (by norm_num : (1 : ℝ) < 2)
  obtain ⟨p1, p2, h1, h2, e1, e2, hsum⟩ := hF K
  have hu1 := le_abs_self u
  have hu2 := neg_abs_le u
  have hinv : 0 < 1 / (p3 ^ 2 - p3) := by positivity
  have grow : ∀ c x y : ℝ, 0 < c → 0 < x → 0 < y → c ≤ c * (1 / x + 1 / y) * x := by
    intro c x y hc hx hy
    have e : c * (1 / x + 1 / y) * x = c + c * (x / y) := by field_simp
    rw [e]
    have : 0 ≤ c * (x / y) := by positivity
    linarith
  have hc0 : 0 < 1 + |u| + 1 / (p3 ^ 2 - p3) := by positivity
  have hT : 1 + |u| + 1 / (p3 ^ 2 - p3) < 2 ^ K * a ∧ 1 + |u| + 1 / (p3 ^ 2 - p3) < 2 ^ K * b := by
    have g1 := grow _ a b hc0 ha hb
    have g2 := grow _ b a hc0 hb ha
    rw [add_comm (1 / b) (1 / a)] at g2
    constructor
    · nlinarith [mul_lt_mul_of_pos_right hK ha]
    · nlinarith [mul_lt_mul_of_pos_right hK hb]
  -- `p ≤ c + 1/(2c)` from `p² = c² + 1 - u²/4` with `c = A - u/2`
  have bound : ∀ A p : ℝ, 0 ≤ p → p ^ 2 = A ^ 2 - u * A + 1 → 1 / (p3 ^ 2 - p3) < A - u / 2 →
      p ≤ A - u / 2 + 1 / (2 * (A - u / 2)) := by
    intro A p hp hpsq hA
    have hc : 0 < A - u / 2 := lt_trans hinv hA
    obtain ⟨c, hcdef⟩ : ∃ c, c = A - u / 2 := ⟨_, rfl⟩
    rw [← hcdef] at hc ⊢
    have he : 2 * c * (1 / (2 * c)) = 1 := by field_simp
    have hr : 0 ≤ c + 1 / (2 * c) := by positivity
    have hsq : p ^ 2 ≤ (c + 1 / (2 * c)) ^ 2 := by
      have e : (c + 1 / (2 * c)) ^ 2 = c ^ 2 + 1 + (1 / (2 * c)) ^ 2 := by
        calc (c + 1 / (2 * c)) ^ 2 = c ^ 2 + 2 * c * (1 / (2 * c)) + (1 / (2 * c)) ^ 2 := by ring
          _ = _ := by rw [he]
      have hA' : A = c + u / 2 := by linarith
      rw [e, hpsq, hA']
      nlinarith [sq_nonneg u, sq_nonneg (1 / (2 * c))]
    exact (pow_le_pow_iff_left₀ hp hr (by norm_num)).1 hsq
  have small : ∀ A : ℝ, 1 / (p3 ^ 2 - p3) < A - u / 2 →
      1 / (2 * (A - u / 2)) < (p3 ^ 2 - p3) / 2 := by
    intro A hA
    have hc : 0 < A - u / 2 := lt_trans hinv hA
    rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
    rw [div_lt_iff₀ hη] at hA
    nlinarith
  have hA : 1 / (p3 ^ 2 - p3) < (2 ^ K * a - 1) - u / 2 := by linarith [hT.1]
  have hB : 1 / (p3 ^ 2 - p3) < (2 ^ K * b - 1) - u / 2 := by linarith [hT.2]
  have b1 := bound _ p1 h1 e1 hA
  have b2 := bound _ p2 h2 e2 hB
  have s1 := small _ hA
  have s2 := small _ hB
  nlinarith

/-- The angle condition from the plane: the quadrant lemma, the three boundary values and the
Fermat inequality give `a² + ab + b² ≤ δ²`. -/
lemma angle_from_plane {N : ℝ × ℝ → ℝ × ℝ → ℝ} {L a b δ : ℝ} (hq : QHyp N L)
    (ha : 0 < a) (hb : 0 < b) (h1 : N 0 (1, 0) = a) (h2 : N 0 (0, 1) = b)
    (h3 : N (0, 1) (1, 0) = δ)
    (hF : ∀ z : ℝ × ℝ, ∀ K : ℕ, 2 ^ K * (a + b) ≤ N z (2 ^ K, 0) + N z (0, 2 ^ K) + N z 0) :
    a ^ 2 + a * b + b ^ 2 ≤ δ ^ 2 := by
  have hz : InQ ((1 / a, 1 / b) : ℝ × ℝ) := ⟨by positivity, by positivity⟩
  have h0 : InQ (0 : ℝ × ℝ) := ⟨le_rfl, le_rfl⟩
  have hp3 := hq.formula hz h0
  rw [h1, h2, h3] at hp3
  have hp3' : N (1 / a, 1 / b) 0 ^ 2 = 2 + (a ^ 2 + b ^ 2 - δ ^ 2) / (a * b) := by
    rw [hp3]; simp only [Prod.fst_zero, Prod.snd_zero]; field_simp; ring
  have hu := endgame (u := (a ^ 2 + b ^ 2 - δ ^ 2) / (a * b)) ha hb (hq.nonneg hz h0) hp3'
    (fun K => by
      have hK1 : InQ (((2 : ℝ) ^ K, (0 : ℝ)) : ℝ × ℝ) := ⟨by positivity, le_rfl⟩
      have hK2 : InQ (((0 : ℝ), (2 : ℝ) ^ K) : ℝ × ℝ) := ⟨le_rfl, by positivity⟩
      have f1 := hq.formula hz hK1
      have f2 := hq.formula hz hK2
      rw [h1, h2, h3] at f1 f2
      refine ⟨N (1 / a, 1 / b) (2 ^ K, 0), N (1 / a, 1 / b) (0, 2 ^ K),
        hq.nonneg hz hK1, hq.nonneg hz hK2, ?_, ?_, hF _ K⟩
      · rw [f1]; field_simp; ring
      · rw [f2]; field_simp; ring)
  rw [div_le_iff₀ (by positivity)] at hu
  linarith

variable {X : Type*}

/-- **The angle condition (14)** for one pair of terminals, the third terminal being `pc`. -/
theorem angle_core (S : MidSpace X) (o pa pb pc : X)
    (hmin : ∀ q, S.d o pa + S.d o pb + S.d o pc ≤ S.d q pa + S.d q pb + S.d q pc) :
    S.d o pa ^ 2 + S.d o pa * S.d o pb + S.d o pb ^ 2 ≤ S.d pa pb ^ 2 := by
  have ha0 := S.d_nonneg o pa
  have hb0 := S.d_nonneg o pb
  have hab := S.d_nonneg pa pb
  rcases ha0.lt_or_eq with ha | ha
  · rcases hb0.lt_or_eq with hb | hb
    · have key := angle_from_plane (qhyp S o pa pb) ha hb (Nf_e1 S o pa pb) (Nf_e2 S o pa pb)
        (Nf_e21 S o pa pb) (fun z K => Nf_fermat S o pa pb pc hmin z K)
      have hδ0 := delta_nonneg S o pa pb
      have hδ := delta_le S o pa pb
      nlinarith
    · -- `d(o, pb) = 0`
      have t := S.d_tri o pb pa
      rw [S.d_comm pb pa, ← hb] at t
      rw [← hb]
      nlinarith
  · -- `d(o, pa) = 0`
    have t := S.d_tri o pa pb
    rw [← ha] at t
    rw [← ha]
    nlinarith

/-- (14) for every two distinct terminals of three. -/
theorem angle_fin (S : MidSpace X) (o : X) (p : Fin 3 → X)
    (hmin : ∀ q, S.d o (p 0) + S.d o (p 1) + S.d o (p 2) ≤ S.d q (p 0) + S.d q (p 1) + S.d q (p 2))
    (i j : Fin 3) (hij : i ≠ j) :
    S.d o (p i) ^ 2 + S.d o (p i) * S.d o (p j) + S.d o (p j) ^ 2 ≤ S.d (p i) (p j) ^ 2 := by
  have h01 := angle_core S o (p 0) (p 1) (p 2) hmin
  have h10 := angle_core S o (p 1) (p 0) (p 2) (fun q => by linarith [hmin q])
  have h02 := angle_core S o (p 0) (p 2) (p 1) (fun q => by linarith [hmin q])
  have h20 := angle_core S o (p 2) (p 0) (p 1) (fun q => by linarith [hmin q])
  have h12 := angle_core S o (p 1) (p 2) (p 0) (fun q => by linarith [hmin q])
  have h21 := angle_core S o (p 2) (p 1) (p 0) (fun q => by linarith [hmin q])
  fin_cases i <;> fin_cases j
  all_goals first
    | exact absurd rfl hij
    | exact h01 | exact h10 | exact h02 | exact h20 | exact h12 | exact h21

/-- The angle condition at a minimiser of the sum of the three terminal distances. -/
theorem proof_R111_1 : S_R111_1 := by
  intro X d m p o hd0 hsymm htri hax1 hax2 hdiag hquad hmin i j hij
  exact angle_fin ⟨d, m, hd0, hsymm, htri, hax1, hax2, hdiag, hquad⟩ o p hmin i j hij

end OM.NNN30.Geom
