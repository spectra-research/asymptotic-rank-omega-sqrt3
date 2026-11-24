import Lib.OM.NNN18.OrdinaryCore
import Lib.OM.NNN18.Monomials


noncomputable section
namespace OM.NNN18.OrdU

set_option maxHeartbeats 4000000

def lo00 (d y : ℝ) : ℝ :=
  (176289 / 100000 : ℝ) + (-689781 / 200000 : ℝ) * d + (-13533 / 100000 : ℝ) * d ^ 2 + (25347 / 100000 : ℝ) * y ^ 2

def lo01 (d y : ℝ) : ℝ :=
  (-852052198489 / 2000000000000 : ℝ) + (1421354285973 / 1000000000000 : ℝ) * d + (1536985535973 / 1000000000000 : ℝ) * y + (-84386008387 / 50000000000 : ℝ) * d ^ 2 + (-1057633387 / 25000000000 : ℝ) * d * y + (-637008387 / 50000000000 : ℝ) * y ^ 2 + (9633351 / 1250000000 : ℝ) * d ^ 3 + (28900053 / 1250000000 : ℝ) * d ^ 2 * y + (28900053 / 1250000000 : ℝ) * d * y ^ 2 + (9633351 / 1250000000 : ℝ) * y ^ 3

def lo02 (d y : ℝ) : ℝ :=
  (-852052198489 / 2000000000000 : ℝ) + (1421354285973 / 1000000000000 : ℝ) * d + (-1536985535973 / 1000000000000 : ℝ) * y + (-84386008387 / 50000000000 : ℝ) * d ^ 2 + (1057633387 / 25000000000 : ℝ) * d * y + (-637008387 / 50000000000 : ℝ) * y ^ 2 + (9633351 / 1250000000 : ℝ) * d ^ 3 + (-28900053 / 1250000000 : ℝ) * d ^ 2 * y + (28900053 / 1250000000 : ℝ) * d * y ^ 2 + (-9633351 / 1250000000 : ℝ) * y ^ 3

def lo11 (d y : ℝ) : ℝ :=
  (178227 / 80000 : ℝ) + (16277 / 6400 : ℝ) * d + (-246381 / 160000 : ℝ) * y + (71249 / 16000 : ℝ) * d ^ 2 + (37791 / 40000 : ℝ) * d * y + (1969 / 80000 : ℝ) * y ^ 2

def lo12 (d y : ℝ) : ℝ :=
  (-1979169 / 2200000 : ℝ) + (-5302479 / 1760000 : ℝ) * d + (6781647 / 4400000 : ℝ) * d ^ 2 + (1969 / 80000 : ℝ) * y ^ 2 + (-78 / 55 : ℝ) * d ^ 3

def lo22 (d y : ℝ) : ℝ :=
  (178227 / 80000 : ℝ) + (16277 / 6400 : ℝ) * d + (246381 / 160000 : ℝ) * y + (71249 / 16000 : ℝ) * d ^ 2 + (-37791 / 40000 : ℝ) * d * y + (1969 / 80000 : ℝ) * y ^ 2

theorem ordHat_lo (d y : ℝ) (x : Fin 3 → ℝ) :
    ordHat U (1 / 25) d y x =
      quad3 (lo00 d y) (lo01 d y) (lo02 d y) (lo11 d y) (lo12 d y) (lo22 d y) x := by
  simp only [ordHat, form0, parents0, target0, betaOrd, args, theta, delta, cross, dot,
    star, tariff, other, Track.Lmaj, Track.z0, Track.K, quad3, U,
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
  (417789 / 100000 : ℝ) + (-662181 / 200000 : ℝ) * d + (-13533 / 100000 : ℝ) * d ^ 2 + (25347 / 100000 : ℝ) * y ^ 2

def hi01 (d y : ℝ) : ℝ :=
  (6406709759511 / 2000000000000 : ℝ) + (2135856139973 / 1000000000000 : ℝ) * d + (1032487389973 / 1000000000000 : ℝ) * y + (-80819536387 / 50000000000 : ℝ) * d ^ 2 + (2508838613 / 25000000000 : ℝ) * d * y + (2929463613 / 50000000000 : ℝ) * y ^ 2 + (9633351 / 1250000000 : ℝ) * d ^ 3 + (28900053 / 1250000000 : ℝ) * d ^ 2 * y + (28900053 / 1250000000 : ℝ) * d * y ^ 2 + (9633351 / 1250000000 : ℝ) * y ^ 3

def hi02 (d y : ℝ) : ℝ :=
  (6406709759511 / 2000000000000 : ℝ) + (2135856139973 / 1000000000000 : ℝ) * d + (-1032487389973 / 1000000000000 : ℝ) * y + (-80819536387 / 50000000000 : ℝ) * d ^ 2 + (-2508838613 / 25000000000 : ℝ) * d * y + (2929463613 / 50000000000 : ℝ) * y ^ 2 + (9633351 / 1250000000 : ℝ) * d ^ 3 + (-28900053 / 1250000000 : ℝ) * d ^ 2 * y + (28900053 / 1250000000 : ℝ) * d * y ^ 2 + (-9633351 / 1250000000 : ℝ) * y ^ 3

def hi11 (d y : ℝ) : ℝ :=
  (470327 / 80000 : ℝ) + (30997 / 6400 : ℝ) * d + (-246381 / 160000 : ℝ) * y + (71249 / 16000 : ℝ) * d ^ 2 + (37791 / 40000 : ℝ) * d * y + (1969 / 80000 : ℝ) * y ^ 2

def hi12 (d y : ℝ) : ℝ :=
  (6053581 / 2200000 : ℝ) + (-1254479 / 1760000 : ℝ) * d + (6781647 / 4400000 : ℝ) * d ^ 2 + (1969 / 80000 : ℝ) * y ^ 2 + (-78 / 55 : ℝ) * d ^ 3

def hi22 (d y : ℝ) : ℝ :=
  (470327 / 80000 : ℝ) + (30997 / 6400 : ℝ) * d + (246381 / 160000 : ℝ) * y + (71249 / 16000 : ℝ) * d ^ 2 + (-37791 / 40000 : ℝ) * d * y + (1969 / 80000 : ℝ) * y ^ 2

theorem ordHat_hi (d y : ℝ) (x : Fin 3 → ℝ) :
    ordHat U (1 / 2) d y x =
      quad3 (hi00 d y) (hi01 d y) (hi02 d y) (hi11 d y) (hi12 d y) (hi22 d y) x := by
  simp only [ordHat, form0, parents0, target0, betaOrd, args, theta, delta, cross, dot,
    star, tariff, other, Track.Lmaj, Track.z0, Track.K, quad3, U,
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
  [⟨(410837801511 / 1000000000000 : ℚ), 0, 0⟩,
    ⟨(-303098214027 / 500000000000 : ℚ), 1, 0⟩,
    ⟨(-87769258387 / 25000000000 : ℚ), 2, 0⟩,
    ⟨(5699741613 / 25000000000 : ℚ), 0, 2⟩,
    ⟨(9633351 / 625000000 : ℚ), 3, 0⟩,
    ⟨(28900053 / 625000000 : ℚ), 1, 2⟩]

lemma p_low_row0_eval (d y : ℝ) : p_low_row0.eval d y = lo00 d y + lo01 d y + lo02 d y - 1 / 2 := by
  simp only [p_low_row0, Poly.eval, Mono.eval, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, lo00, lo01, lo02]
  push_cast; ring

lemma p_low_row0_lower : 0 < p_low_row0.lower U.R := by
  decide +kernel

def p_low_row1 : Poly :=
  [⟨(8848160816621 / 22000000000000 : ℚ), 0, 0⟩,
    ⟨(10470497145703 / 11000000000000 : ℚ), 1, 0⟩,
    ⟨(-2895714027 / 1000000000000 : ℚ), 0, 1⟩,
    ⟨(2368644157743 / 550000000000 : ℚ), 2, 0⟩,
    ⟨(22561741613 / 25000000000 : ℚ), 1, 1⟩,
    ⟨(1824241613 / 50000000000 : ℚ), 0, 2⟩,
    ⟨(-19394033139 / 13750000000 : ℚ), 3, 0⟩,
    ⟨(28900053 / 1250000000 : ℚ), 2, 1⟩,
    ⟨(28900053 / 1250000000 : ℚ), 1, 2⟩,
    ⟨(9633351 / 1250000000 : ℚ), 0, 3⟩]

lemma p_low_row1_eval (d y : ℝ) : p_low_row1.eval d y = lo01 d y + lo11 d y + lo12 d y - 1 / 2 := by
  simp only [p_low_row1, Poly.eval, Mono.eval, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, lo01, lo11, lo12]
  push_cast; ring

lemma p_low_row1_lower : 0 < p_low_row1.lower U.R := by
  decide +kernel

def p_low_off01 : Poly :=
  [⟨(1252052198489 / 2000000000000 : ℚ), 0, 0⟩,
    ⟨(-1421354285973 / 1000000000000 : ℚ), 1, 0⟩,
    ⟨(-1536985535973 / 1000000000000 : ℚ), 0, 1⟩,
    ⟨(84386008387 / 50000000000 : ℚ), 2, 0⟩,
    ⟨(1057633387 / 25000000000 : ℚ), 1, 1⟩,
    ⟨(637008387 / 50000000000 : ℚ), 0, 2⟩,
    ⟨(-9633351 / 1250000000 : ℚ), 3, 0⟩,
    ⟨(-28900053 / 1250000000 : ℚ), 2, 1⟩,
    ⟨(-28900053 / 1250000000 : ℚ), 1, 2⟩,
    ⟨(-9633351 / 1250000000 : ℚ), 0, 3⟩]

lemma p_low_off01_eval (d y : ℝ) : p_low_off01.eval d y = 1 / 5 - lo01 d y := by
  simp only [p_low_off01, Poly.eval, Mono.eval, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, lo01]
  push_cast; ring

lemma p_low_off01_lower : 0 < p_low_off01.lower U.R := by
  decide +kernel

def p_low_off12 : Poly :=
  [⟨(1979169 / 2200000 : ℚ), 0, 0⟩,
    ⟨(5302479 / 1760000 : ℚ), 1, 0⟩,
    ⟨(-6781647 / 4400000 : ℚ), 2, 0⟩,
    ⟨(-1969 / 80000 : ℚ), 0, 2⟩,
    ⟨(78 / 55 : ℚ), 3, 0⟩]

lemma p_low_off12_eval (d y : ℝ) : p_low_off12.eval d y = -lo12 d y := by
  simp only [p_low_off12, Poly.eval, Mono.eval, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, lo12]
  push_cast; ring

lemma p_low_off12_lower : 0 < p_low_off12.lower U.R := by
  decide +kernel

def p_low_offsum0 : Poly :=
  [⟨(852052198489 / 1000000000000 : ℚ), 0, 0⟩,
    ⟨(-1421354285973 / 500000000000 : ℚ), 1, 0⟩,
    ⟨(84386008387 / 25000000000 : ℚ), 2, 0⟩,
    ⟨(637008387 / 25000000000 : ℚ), 0, 2⟩,
    ⟨(-9633351 / 625000000 : ℚ), 3, 0⟩,
    ⟨(-28900053 / 625000000 : ℚ), 1, 2⟩]

lemma p_low_offsum0_eval (d y : ℝ) : p_low_offsum0.eval d y = -lo01 d y - lo02 d y := by
  simp only [p_low_offsum0, Poly.eval, Mono.eval, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, lo01, lo02]
  push_cast; ring

lemma p_low_offsum0_lower : 0 < p_low_offsum0.lower U.R := by
  decide +kernel

def p_high_00 : Poly :=
  [⟨(417789 / 100000 : ℚ), 0, 0⟩,
    ⟨(-662181 / 200000 : ℚ), 1, 0⟩,
    ⟨(-13533 / 100000 : ℚ), 2, 0⟩,
    ⟨(25347 / 100000 : ℚ), 0, 2⟩]

lemma p_high_00_eval (d y : ℝ) : p_high_00.eval d y = hi00 d y := by
  simp only [p_high_00, Poly.eval, Mono.eval, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, hi00]
  push_cast; ring

lemma p_high_00_lower : 0 < p_high_00.lower U.R := by
  decide +kernel

def p_high_01 : Poly :=
  [⟨(6406709759511 / 2000000000000 : ℚ), 0, 0⟩,
    ⟨(2135856139973 / 1000000000000 : ℚ), 1, 0⟩,
    ⟨(1032487389973 / 1000000000000 : ℚ), 0, 1⟩,
    ⟨(-80819536387 / 50000000000 : ℚ), 2, 0⟩,
    ⟨(2508838613 / 25000000000 : ℚ), 1, 1⟩,
    ⟨(2929463613 / 50000000000 : ℚ), 0, 2⟩,
    ⟨(9633351 / 1250000000 : ℚ), 3, 0⟩,
    ⟨(28900053 / 1250000000 : ℚ), 2, 1⟩,
    ⟨(28900053 / 1250000000 : ℚ), 1, 2⟩,
    ⟨(9633351 / 1250000000 : ℚ), 0, 3⟩]

lemma p_high_01_eval (d y : ℝ) : p_high_01.eval d y = hi01 d y := by
  simp only [p_high_01, Poly.eval, Mono.eval, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, hi01]
  push_cast; ring

lemma p_high_01_lower : 0 < p_high_01.lower U.R := by
  decide +kernel

def p_high_11 : Poly :=
  [⟨(470327 / 80000 : ℚ), 0, 0⟩,
    ⟨(30997 / 6400 : ℚ), 1, 0⟩,
    ⟨(-246381 / 160000 : ℚ), 0, 1⟩,
    ⟨(71249 / 16000 : ℚ), 2, 0⟩,
    ⟨(37791 / 40000 : ℚ), 1, 1⟩,
    ⟨(1969 / 80000 : ℚ), 0, 2⟩]

lemma p_high_11_eval (d y : ℝ) : p_high_11.eval d y = hi11 d y := by
  simp only [p_high_11, Poly.eval, Mono.eval, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, hi11]
  push_cast; ring

lemma p_high_11_lower : 0 < p_high_11.lower U.R := by
  decide +kernel

def p_high_12 : Poly :=
  [⟨(6053581 / 2200000 : ℚ), 0, 0⟩,
    ⟨(-1254479 / 1760000 : ℚ), 1, 0⟩,
    ⟨(6781647 / 4400000 : ℚ), 2, 0⟩,
    ⟨(1969 / 80000 : ℚ), 0, 2⟩,
    ⟨(-78 / 55 : ℚ), 3, 0⟩]

lemma p_high_12_eval (d y : ℝ) : p_high_12.eval d y = hi12 d y := by
  simp only [p_high_12, Poly.eval, Mono.eval, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, hi12]
  push_cast; ring

lemma p_high_12_lower : 0 < p_high_12.lower U.R := by
  decide +kernel


theorem ordHat_nonneg {e d y : ℝ} (he₁ : 1 / 25 ≤ e) (he₂ : e ≤ 1 / 2)
    (hd₁ : -2 * (U.R : ℝ) ≤ d) (hd₂ : d ≤ U.R) (hy₁ : -(3 * (U.R : ℝ)) ≤ y)
    (hy₂ : y ≤ 3 * U.R) {x : Fin 3 → ℝ} (hx : ∀ i, 0 ≤ x i) :
    0 ≤ ordHat U e d y x := by
  have hR : (0 : ℚ) ≤ U.R := by norm_num [U]
  have hy₁' : -(3 * (U.R : ℝ)) ≤ -y := by linarith
  have hy₂' : -y ≤ 3 * U.R := by linarith
  have pos := fun (p : Poly) (h : 0 < p.lower U.R) => p.pos_of_lower hR h hd₁ hd₂ hy₁ hy₂
  have pos' := fun (p : Poly) (h : 0 < p.lower U.R) => p.pos_of_lower hR h hd₁ hd₂ hy₁' hy₂'
  -- low endpoint e = 1/25: diagonal dominance
  have hlow : 0 ≤ ordHat U (1 / 25) d y x := by
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
  have hhigh : 0 ≤ ordHat U (1 / 2) d y x := by
    rw [ordHat_hi]
    have a00 := pos _ p_high_00_lower; rw [p_high_00_eval] at a00
    have a01 := pos _ p_high_01_lower; rw [p_high_01_eval] at a01
    have a02 := pos' _ p_high_01_lower; rw [p_high_01_eval, ← hi02_refl] at a02
    have a11 := pos _ p_high_11_lower; rw [p_high_11_eval] at a11
    have a12 := pos _ p_high_12_lower; rw [p_high_12_eval] at a12
    have a22 := pos' _ p_high_11_lower; rw [p_high_11_eval, ← hi22_refl] at a22
    exact quad3_nonneg_of_pos a00.le a01.le a02.le a11.le a12.le a22.le hx
  -- concavity in e
  have hcurv : 0 ≤ ordCurv U d y x := by
    have hR' : (0 : ℝ) ≤ U.R := by exact_mod_cast hR
    have ht : (2 : ℝ) * U.R ≤ U.t := by norm_num [U]
    have e1 : theta U (delta d y) 1 = U.t + (y - d) / 2 := by simp [theta, delta]
    have e2 : theta U (delta d y) 2 = U.t + (-d - y) / 2 := by simp [theta, delta]
    have h1 : 0 ≤ theta U (delta d y) 1 := by rw [e1]; linarith
    have h2 : 0 ≤ theta U (delta d y) 2 := by rw [e2]; linarith
    have hK : (0 : ℝ) ≤ ((Track.K 1 : ℚ) : ℝ) := by norm_num [Track.K]
    unfold ordCurv
    exact mul_nonneg (mul_nonneg (by norm_num) hK)
      (add_nonneg (mul_nonneg h1 (mul_nonneg (hx 0) (hx 2)))
        (mul_nonneg h2 (mul_nonneg (hx 0) (hx 1))))
  rcases eq_or_lt_of_le he₁ with h | h
  · rw [← h]; exact hlow
  · exact ordHat_nonneg_between U (by norm_num) he₁ he₂ hcurv hlow hhigh

end OM.NNN18.OrdU
