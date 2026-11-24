import Lib.OM.NNN18.OrdinaryCore
import Lib.OM.NNN18.Monomials


noncomputable section
namespace OM.NNN18.OrdC

set_option maxHeartbeats 4000000

def lo00 (d y : ℝ) : ℝ :=
  (1759 / 1000 : ℝ) + (-7529 / 2500 : ℝ) * d + (-3 / 10 : ℝ) * d ^ 2 + (3 / 10 : ℝ) * y ^ 2

def lo01 (d y : ℝ) : ℝ :=
  (-1223663711 / 3000000000 : ℝ) + (20593382233 / 12000000000 : ℝ) * d + (6128927411 / 4000000000 : ℝ) * y + (-256285411 / 160000000 : ℝ) * d ^ 2 + (-285411 / 80000000 : ℝ) * d * y + (-4285411 / 160000000 : ℝ) * y ^ 2 + (3159 / 320000 : ℝ) * d ^ 3 + (9477 / 320000 : ℝ) * d ^ 2 * y + (9477 / 320000 : ℝ) * d * y ^ 2 + (3159 / 320000 : ℝ) * y ^ 3

def lo02 (d y : ℝ) : ℝ :=
  (-1223663711 / 3000000000 : ℝ) + (20593382233 / 12000000000 : ℝ) * d + (-6128927411 / 4000000000 : ℝ) * y + (-256285411 / 160000000 : ℝ) * d ^ 2 + (285411 / 80000000 : ℝ) * d * y + (-4285411 / 160000000 : ℝ) * y ^ 2 + (3159 / 320000 : ℝ) * d ^ 3 + (-9477 / 320000 : ℝ) * d ^ 2 * y + (9477 / 320000 : ℝ) * d * y ^ 2 + (-3159 / 320000 : ℝ) * y ^ 3

def lo11 (d y : ℝ) : ℝ :=
  (36689 / 18000 : ℝ) + (3263 / 1500 : ℝ) * d + (-9559 / 6000 : ℝ) * y + (35 / 8 : ℝ) * d ^ 2 + (9 / 8 : ℝ) * d * y

def lo12 (d y : ℝ) : ℝ :=
  (-1966207 / 2475000 : ℝ) + (-7082093 / 2100000 : ℝ) * d + (4563 / 3080 : ℝ) * d ^ 2 + (-78 / 55 : ℝ) * d ^ 3

def lo22 (d y : ℝ) : ℝ :=
  (36689 / 18000 : ℝ) + (3263 / 1500 : ℝ) * d + (9559 / 6000 : ℝ) * y + (35 / 8 : ℝ) * d ^ 2 + (-9 / 8 : ℝ) * d * y

theorem ordHat_lo (d y : ℝ) (x : Fin 3 → ℝ) :
    ordHat C (1 / 25) d y x =
      quad3 (lo00 d y) (lo01 d y) (lo02 d y) (lo11 d y) (lo12 d y) (lo22 d y) x := by
  simp only [ordHat, form0, parents0, target0, betaOrd, args, theta, delta, cross, dot,
    star, tariff, other, Track.Lmaj, Track.z0, Track.K, quad3, C,
    lo00, lo01, lo02, lo11, lo12, lo22,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, Fin.isValue, ↓reduceIte]
  norm_num
  ring

lemma lo02_refl (d y : ℝ) : lo02 d y = lo01 d (-y) := by
  simp only [lo01, lo02] <;> ring
lemma lo22_refl (d y : ℝ) : lo22 d y = lo11 d (-y) := by
  simp only [lo11, lo22] <;> ring
lemma lo12_refl (d y : ℝ) : lo12 d y = lo12 d (-y) := by
  simp only [lo12] <;> ring

def hi00 (d y : ℝ) : ℝ :=
  (4197 / 1000 : ℝ) + (-1796 / 625 : ℝ) * d + (-3 / 10 : ℝ) * d ^ 2 + (3 / 10 : ℝ) * y ^ 2

def hi01 (d y : ℝ) : ℝ :=
  (9272872969 / 3000000000 : ℝ) + (29108592193 / 12000000000 : ℝ) * d + (4091330731 / 4000000000 : ℝ) * y + (-243368611 / 160000000 : ℝ) * d ^ 2 + (12631389 / 80000000 : ℝ) * d * y + (8631389 / 160000000 : ℝ) * y ^ 2 + (3159 / 320000 : ℝ) * d ^ 3 + (9477 / 320000 : ℝ) * d ^ 2 * y + (9477 / 320000 : ℝ) * d * y ^ 2 + (3159 / 320000 : ℝ) * y ^ 3

def hi02 (d y : ℝ) : ℝ :=
  (9272872969 / 3000000000 : ℝ) + (29108592193 / 12000000000 : ℝ) * d + (-4091330731 / 4000000000 : ℝ) * y + (-243368611 / 160000000 : ℝ) * d ^ 2 + (-12631389 / 80000000 : ℝ) * d * y + (8631389 / 160000000 : ℝ) * y ^ 2 + (3159 / 320000 : ℝ) * d ^ 3 + (-9477 / 320000 : ℝ) * d ^ 2 * y + (9477 / 320000 : ℝ) * d * y ^ 2 + (-3159 / 320000 : ℝ) * y ^ 3

def hi11 (d y : ℝ) : ℝ :=
  (99479 / 18000 : ℝ) + (6713 / 1500 : ℝ) * d + (-9559 / 6000 : ℝ) * y + (35 / 8 : ℝ) * d ^ 2 + (9 / 8 : ℝ) * d * y

def hi12 (d y : ℝ) : ℝ :=
  (3333709 / 1237500 : ℝ) + (-2252093 / 2100000 : ℝ) * d + (4563 / 3080 : ℝ) * d ^ 2 + (-78 / 55 : ℝ) * d ^ 3

def hi22 (d y : ℝ) : ℝ :=
  (99479 / 18000 : ℝ) + (6713 / 1500 : ℝ) * d + (9559 / 6000 : ℝ) * y + (35 / 8 : ℝ) * d ^ 2 + (-9 / 8 : ℝ) * d * y

theorem ordHat_hi (d y : ℝ) (x : Fin 3 → ℝ) :
    ordHat C (1 / 2) d y x =
      quad3 (hi00 d y) (hi01 d y) (hi02 d y) (hi11 d y) (hi12 d y) (hi22 d y) x := by
  simp only [ordHat, form0, parents0, target0, betaOrd, args, theta, delta, cross, dot,
    star, tariff, other, Track.Lmaj, Track.z0, Track.K, quad3, C,
    hi00, hi01, hi02, hi11, hi12, hi22,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, Fin.isValue, ↓reduceIte]
  norm_num
  ring

lemma hi02_refl (d y : ℝ) : hi02 d y = hi01 d (-y) := by
  simp only [hi01, hi02] <;> ring
lemma hi22_refl (d y : ℝ) : hi22 d y = hi11 d (-y) := by
  simp only [hi11, hi22] <;> ring
lemma hi12_refl (d y : ℝ) : hi12 d y = hi12 d (-y) := by
  simp only [hi12] <;> ring

def p_low_row0 : Poly :=
  [⟨(664836289 / 1500000000 : ℚ), 0, 0⟩,
    ⟨(2523782233 / 6000000000 : ℚ), 1, 0⟩,
    ⟨(-280285411 / 80000000 : ℚ), 2, 0⟩,
    ⟨(19714589 / 80000000 : ℚ), 0, 2⟩,
    ⟨(3159 / 160000 : ℚ), 3, 0⟩,
    ⟨(9477 / 160000 : ℚ), 1, 2⟩]

lemma p_low_row0_eval (d y : ℝ) : p_low_row0.eval d y = lo00 d y + lo01 d y + lo02 d y - 1 / 2 := by
  simp only [p_low_row0, Poly.eval, Mono.eval, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, lo00, lo01, lo02]
  push_cast; ring

lemma p_low_row0_lower : 0 < p_low_row0.lower C.R := by
  decide +kernel

def p_low_row1 : Poly :=
  [⟨(33260317537 / 99000000000 : ℚ), 0, 0⟩,
    ⟨(14532651877 / 28000000000 : ℚ), 1, 0⟩,
    ⟨(-731217767 / 12000000000 : ℚ), 0, 1⟩,
    ⟨(52418023353 / 12320000000 : ℚ), 2, 0⟩,
    ⟨(89714589 / 80000000 : ℚ), 1, 1⟩,
    ⟨(-4285411 / 160000000 : ℚ), 0, 2⟩,
    ⟨(-4957251 / 3520000 : ℚ), 3, 0⟩,
    ⟨(9477 / 320000 : ℚ), 2, 1⟩,
    ⟨(9477 / 320000 : ℚ), 1, 2⟩,
    ⟨(3159 / 320000 : ℚ), 0, 3⟩]

lemma p_low_row1_eval (d y : ℝ) : p_low_row1.eval d y = lo01 d y + lo11 d y + lo12 d y - 1 / 2 := by
  simp only [p_low_row1, Poly.eval, Mono.eval, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, lo01, lo11, lo12]
  push_cast; ring

lemma p_low_row1_lower : 0 < p_low_row1.lower C.R := by
  decide +kernel

def p_low_off01 : Poly :=
  [⟨(1823663711 / 3000000000 : ℚ), 0, 0⟩,
    ⟨(-20593382233 / 12000000000 : ℚ), 1, 0⟩,
    ⟨(-6128927411 / 4000000000 : ℚ), 0, 1⟩,
    ⟨(256285411 / 160000000 : ℚ), 2, 0⟩,
    ⟨(285411 / 80000000 : ℚ), 1, 1⟩,
    ⟨(4285411 / 160000000 : ℚ), 0, 2⟩,
    ⟨(-3159 / 320000 : ℚ), 3, 0⟩,
    ⟨(-9477 / 320000 : ℚ), 2, 1⟩,
    ⟨(-9477 / 320000 : ℚ), 1, 2⟩,
    ⟨(-3159 / 320000 : ℚ), 0, 3⟩]

lemma p_low_off01_eval (d y : ℝ) : p_low_off01.eval d y = 1 / 5 - lo01 d y := by
  simp only [p_low_off01, Poly.eval, Mono.eval, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, lo01]
  push_cast; ring

lemma p_low_off01_lower : 0 < p_low_off01.lower C.R := by
  decide +kernel

def p_low_off12 : Poly :=
  [⟨(1966207 / 2475000 : ℚ), 0, 0⟩,
    ⟨(7082093 / 2100000 : ℚ), 1, 0⟩,
    ⟨(-4563 / 3080 : ℚ), 2, 0⟩,
    ⟨(78 / 55 : ℚ), 3, 0⟩]

lemma p_low_off12_eval (d y : ℝ) : p_low_off12.eval d y = -lo12 d y := by
  simp only [p_low_off12, Poly.eval, Mono.eval, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, lo12]
  push_cast; ring

lemma p_low_off12_lower : 0 < p_low_off12.lower C.R := by
  decide +kernel

def p_low_offsum0 : Poly :=
  [⟨(1223663711 / 1500000000 : ℚ), 0, 0⟩,
    ⟨(-20593382233 / 6000000000 : ℚ), 1, 0⟩,
    ⟨(256285411 / 80000000 : ℚ), 2, 0⟩,
    ⟨(4285411 / 80000000 : ℚ), 0, 2⟩,
    ⟨(-3159 / 160000 : ℚ), 3, 0⟩,
    ⟨(-9477 / 160000 : ℚ), 1, 2⟩]

lemma p_low_offsum0_eval (d y : ℝ) : p_low_offsum0.eval d y = -lo01 d y - lo02 d y := by
  simp only [p_low_offsum0, Poly.eval, Mono.eval, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, lo01, lo02]
  push_cast; ring

lemma p_low_offsum0_lower : 0 < p_low_offsum0.lower C.R := by
  decide +kernel

def p_high_00 : Poly :=
  [⟨(4197 / 1000 : ℚ), 0, 0⟩,
    ⟨(-1796 / 625 : ℚ), 1, 0⟩,
    ⟨(-3 / 10 : ℚ), 2, 0⟩,
    ⟨(3 / 10 : ℚ), 0, 2⟩]

lemma p_high_00_eval (d y : ℝ) : p_high_00.eval d y = hi00 d y := by
  simp only [p_high_00, Poly.eval, Mono.eval, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, hi00]
  push_cast; ring

lemma p_high_00_lower : 0 < p_high_00.lower C.R := by
  decide +kernel

def p_high_01 : Poly :=
  [⟨(9272872969 / 3000000000 : ℚ), 0, 0⟩,
    ⟨(29108592193 / 12000000000 : ℚ), 1, 0⟩,
    ⟨(4091330731 / 4000000000 : ℚ), 0, 1⟩,
    ⟨(-243368611 / 160000000 : ℚ), 2, 0⟩,
    ⟨(12631389 / 80000000 : ℚ), 1, 1⟩,
    ⟨(8631389 / 160000000 : ℚ), 0, 2⟩,
    ⟨(3159 / 320000 : ℚ), 3, 0⟩,
    ⟨(9477 / 320000 : ℚ), 2, 1⟩,
    ⟨(9477 / 320000 : ℚ), 1, 2⟩,
    ⟨(3159 / 320000 : ℚ), 0, 3⟩]

lemma p_high_01_eval (d y : ℝ) : p_high_01.eval d y = hi01 d y := by
  simp only [p_high_01, Poly.eval, Mono.eval, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, hi01]
  push_cast; ring

lemma p_high_01_lower : 0 < p_high_01.lower C.R := by
  decide +kernel

def p_high_11 : Poly :=
  [⟨(99479 / 18000 : ℚ), 0, 0⟩,
    ⟨(6713 / 1500 : ℚ), 1, 0⟩,
    ⟨(-9559 / 6000 : ℚ), 0, 1⟩,
    ⟨(35 / 8 : ℚ), 2, 0⟩,
    ⟨(9 / 8 : ℚ), 1, 1⟩]

lemma p_high_11_eval (d y : ℝ) : p_high_11.eval d y = hi11 d y := by
  simp only [p_high_11, Poly.eval, Mono.eval, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, hi11]
  push_cast; ring

lemma p_high_11_lower : 0 < p_high_11.lower C.R := by
  decide +kernel

def p_high_12 : Poly :=
  [⟨(3333709 / 1237500 : ℚ), 0, 0⟩,
    ⟨(-2252093 / 2100000 : ℚ), 1, 0⟩,
    ⟨(4563 / 3080 : ℚ), 2, 0⟩,
    ⟨(-78 / 55 : ℚ), 3, 0⟩]

lemma p_high_12_eval (d y : ℝ) : p_high_12.eval d y = hi12 d y := by
  simp only [p_high_12, Poly.eval, Mono.eval, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, hi12]
  push_cast; ring

lemma p_high_12_lower : 0 < p_high_12.lower C.R := by
  decide +kernel


theorem ordHat_nonneg {e d y : ℝ} (he₁ : 1 / 25 ≤ e) (he₂ : e ≤ 1 / 2)
    (hd₁ : -2 * (C.R : ℝ) ≤ d) (hd₂ : d ≤ C.R) (hy₁ : -(3 * (C.R : ℝ)) ≤ y)
    (hy₂ : y ≤ 3 * C.R) {x : Fin 3 → ℝ} (hx : ∀ i, 0 ≤ x i) :
    0 ≤ ordHat C e d y x := by
  have hR : (0 : ℚ) ≤ C.R := by norm_num [C]
  have hy₁' : -(3 * (C.R : ℝ)) ≤ -y := by linarith
  have hy₂' : -y ≤ 3 * C.R := by linarith
  have pos := fun (p : Poly) (h : 0 < p.lower C.R) => p.pos_of_lower hR h hd₁ hd₂ hy₁ hy₂
  have pos' := fun (p : Poly) (h : 0 < p.lower C.R) => p.pos_of_lower hR h hd₁ hd₂ hy₁' hy₂'
  -- low endpoint e = 1/25: diagonal dominance
  have hlow : 0 ≤ ordHat C (1 / 25) d y x := by
    rw [ordHat_lo]
    have r0 := pos _ p_low_row0_lower; rw [p_low_row0_eval] at r0
    have r1 := pos _ p_low_row1_lower; rw [p_low_row1_eval] at r1
    have r2 := pos' _ p_low_row1_lower; rw [p_low_row1_eval] at r2
    have o1 := pos _ p_low_off01_lower; rw [p_low_off01_eval] at o1
    have o2 := pos' _ p_low_off01_lower; rw [p_low_off01_eval] at o2
    have o3 := pos _ p_low_off12_lower; rw [p_low_off12_eval] at o3
    have o4 := pos _ p_low_offsum0_lower; rw [p_low_offsum0_eval] at o4
    rw [← lo02_refl, ← lo22_refl, ← lo12_refl] at r2
    rw [← lo02_refl] at o2
    exact quad3_nonneg_of_dd (by linarith) (by linarith) (by linarith) (by linarith)
      (by linarith) (by linarith) (by linarith) x
  -- high endpoint e = 1/2: entrywise positivity
  have hhigh : 0 ≤ ordHat C (1 / 2) d y x := by
    rw [ordHat_hi]
    have a00 := pos _ p_high_00_lower; rw [p_high_00_eval] at a00
    have a01 := pos _ p_high_01_lower; rw [p_high_01_eval] at a01
    have a02 := pos' _ p_high_01_lower; rw [p_high_01_eval, ← hi02_refl] at a02
    have a11 := pos _ p_high_11_lower; rw [p_high_11_eval] at a11
    have a12 := pos _ p_high_12_lower; rw [p_high_12_eval] at a12
    have a22 := pos' _ p_high_11_lower; rw [p_high_11_eval, ← hi22_refl] at a22
    exact quad3_nonneg_of_pos a00.le a01.le a02.le a11.le a12.le a22.le hx
  -- concavity in e
  have hcurv : 0 ≤ ordCurv C d y x := by
    have hR' : (0 : ℝ) ≤ C.R := by exact_mod_cast hR
    have ht : (2 : ℝ) * C.R ≤ C.t := by norm_num [C]
    have e1 : theta C (delta d y) 1 = C.t + (y - d) / 2 := by simp [theta, delta]
    have e2 : theta C (delta d y) 2 = C.t + (-d - y) / 2 := by simp [theta, delta]
    have h1 : 0 ≤ theta C (delta d y) 1 := by rw [e1]; linarith
    have h2 : 0 ≤ theta C (delta d y) 2 := by rw [e2]; linarith
    have hK : (0 : ℝ) ≤ ((Track.K 1 : ℚ) : ℝ) := by norm_num [Track.K]
    unfold ordCurv
    exact mul_nonneg (mul_nonneg (by norm_num) hK)
      (add_nonneg (mul_nonneg h1 (mul_nonneg (hx 0) (hx 2)))
        (mul_nonneg h2 (mul_nonneg (hx 0) (hx 1))))
  rcases eq_or_lt_of_le he₁ with h | h
  · rw [← h]; exact hlow
  · exact ordHat_nonneg_between C (by norm_num) he₁ he₂ hcurv hlow hhigh

end OM.NNN18.OrdC
