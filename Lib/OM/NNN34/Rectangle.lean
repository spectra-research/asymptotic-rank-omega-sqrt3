import Lib.OM.NNN34.RectangleLengths
import PLATFORM.Statements.«R114.20»

/-! # The planar rectangle with two equilateral row triangles -/

namespace OM.NNN34

open OM.NNN32 P2M.R114

private lemma length_of_sq {p q : ℝ × ℝ} {s : ℝ} (hs : 0 ≤ s)
    (he : (q.1 - p.1)^2 + (q.2 - p.2)^2 = s^2) : planeLength p q = s :=
  (Real.sqrt_eq_iff_eq_sq (by positivity) hs).2 he

theorem proof_R114_20 : S_R114_20 := by
  intro bL bN hbL hbN bill
  by_contra! hm
  let L := Real.sqrt 3
  have hL : 0 < L := by dsimp [L]; positivity
  have hL2 : L^2 = 3 := Real.sq_sqrt (by norm_num)
  let b := (bL+bN)/2
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hb' : b*L < 1 := (lt_div_iff₀ hL).mp hm
  let a := (1+b*L)/2
  have ha : 0 < a := by dsimp [a]; positivity
  have ha' : a < 1 := by dsimp [a]; linarith
  have hmean : b*L ≤ a := by dsimp [a]; linarith
  let t := (1-a)/4
  have ht : 0 < t := by dsimp [t]; linarith
  let s := Real.sqrt (3+a^2)
  let R := Real.sqrt (3*(1-t)^2+(a-3*t)^2)
  let C := Real.sqrt (3*(1-t)^2+a^2)
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have hR : 0 ≤ R := Real.sqrt_nonneg _
  have hC : 0 ≤ C := Real.sqrt_nonneg _
  have hs2 : s^2 = 3+a^2 := Real.sq_sqrt (by positivity)
  have hR2 : R^2 = 3*(1-t)^2+(a-3*t)^2 := Real.sq_sqrt (by positivity)
  have hC2 : C^2 = 3*(1-t)^2+a^2 := Real.sq_sqrt (by positivity)
  let corner : Fin 4 → ℝ × ℝ := ![(-L,a),(L,a),(-L,-a),(L,-a)]
  let port : Fin 4 → ℝ × ℝ := ![(-L*t,3*t),(L*t,3*t),(-L*t,-3*t),(L*t,-3*t)]
  let o : ℝ × ℝ := (0,0)
  let u : ℝ × ℝ := (-L*t,0)
  let v : ℝ × ℝ := (L*t,0)
  have sep : ∀ i j, i ≠ j → 0 < planeLength (corner i) (corner j) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> first | exact (hij rfl).elim | skip
    all_goals apply Real.sqrt_pos.mpr
    all_goals dsimp [corner]
    all_goals nlinarith only [sq_pos_of_pos hL, sq_pos_of_pos ha]
  have diag : planeLength (corner 0) (corner 3) = 2*s ∧
      planeLength (corner 1) (corner 2) = 2*s := by
    constructor <;> apply length_of_sq (by positivity) <;> dsimp [corner]
    all_goals ring_nf <;> rw [hL2, hs2] <;> ring
  have leaves (i : Fin 4) : planeLength (corner i) (port i) = R := by
    apply length_of_sq hR
    fin_cases i <;> dsimp [corner, port] <;> rw [hR2] <;> ring_nf <;> rw [hL2] <;> ring
  let E := 2*L*t
  have he : 0 ≤ E := by dsimp [E]; positivity
  have per : ∀ (i j : Fin 4), (i = 0 ∧ j = 1 ∨ i = 3 ∧ j = 2) →
      planeLength (port i) (port j) = E ∧ planeLength (port j) o = E ∧ planeLength o (port i) = E := by
    rintro i j (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩) <;> refine ⟨length_of_sq he ?_, length_of_sq he ?_, length_of_sq he ?_⟩
    all_goals dsimp [port, o, E]
    all_goals ring_nf <;> rw [hL2] <;> ring
  have col : planeLength (corner 0) u = C ∧ planeLength (corner 2) u = C ∧
      planeLength (corner 1) v = C ∧ planeLength (corner 3) v = C := by
    refine ⟨length_of_sq hC ?_, length_of_sq hC ?_, length_of_sq hC ?_, length_of_sq hC ?_⟩
    all_goals dsimp [corner,u,v]; rw [hC2]; ring_nf <;> rw [hL2] <;> ring
  have middle : planeLength u v = E := by apply length_of_sq he; dsimp [u,v,E]; ring
  obtain ⟨p0,p1,p2⟩ := per 0 1 (Or.inl ⟨rfl,rfl⟩)
  obtain ⟨p3,p4,p5⟩ := per 3 2 (Or.inr ⟨rfl,rfl⟩)
  have test := bill corner sep port o u v
  simp only [diag.1, diag.2, leaves, p0, p1, p2, p3, p4, p5, col.1, col.2.1, col.2.2.1,
    col.2.2.2, middle, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat] at test
  obtain ⟨rowLess, colLess⟩ := rectangle_costs_lt ha ha'
  change R+3*a*t < s at rowLess
  change C+3*t/2 < s at colLess
  change _ ≤ max _ (_ + L*E) at test
  dsimp only [E] at test
  have hrow : 4*R + bL*(2*L*t+2*L*t+2*L*t) + bN*(2*L*t+2*L*t+2*L*t) < 2*s+2*s := by
    have m := mul_le_mul_of_nonneg_right hmean ht.le
    dsimp only [b] at m
    nlinarith only [m, rowLess]
  apply (not_lt_of_ge test)
  apply max_lt hrow
  nlinarith only [colLess, congrArg (fun x : ℝ => x*t) hL2]

end OM.NNN34

