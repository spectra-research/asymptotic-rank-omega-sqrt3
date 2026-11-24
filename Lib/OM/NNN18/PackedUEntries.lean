import Lib.OM.NNN18.PackedLemmas

/-!
At focus 0 and error 0, for fixed `d`, each entry is a sum of two `ratPart`s in `y`
with denominators `β₁ = h + κy/2`, `β₂ = h - κy/2`, `h = β* - κd/2`.  The identity
with `packHat` is checked by `field_simp; ring`.
-/

noncomputable section
namespace OM.NNN18.PackU

set_option maxHeartbeats 8000000

/-- `κ/2` -/
def k : ℝ := (2003 / 5000 : ℝ)
/-- `h(d) = β* - κd/2` -/
def h (d : ℝ) : ℝ := (21841 / 25000 : ℝ) - (2003 / 5000 : ℝ) * d

def A00 (d : ℝ) : ℝ := (110066898567 / 200600450000 : ℝ) + (-195375711 / 50075000 : ℝ) * d
def R00 (d : ℝ) : ℝ := (15410453625489 / 40120090000000 : ℝ) + (-3313791 / 25037500 : ℝ) * d

def A01 (d : ℝ) : ℝ := (-14762511002148570897941 / 32464642511850987200000 : ℝ) + (464241268842993713 / 324160184841248000 : ℝ) * d + (-35329 / 20000 : ℝ) * d ^ 2
def B01 (d : ℝ) : ℝ := (13819841170573169211 / 8104004621031200000 : ℝ)
def R101 (d : ℝ) : ℝ := (-64722742981 / 6419214400000 : ℝ) + (124737639 / 4006000000 : ℝ) * d
def R201 (d : ℝ) : ℝ := (-305345068776125015703 / 1021543187912240000000 : ℝ) + (124737639 / 4006000000 : ℝ) * d
def S201 (d : ℝ) : ℝ := (27896467124383 / 642884322160000 : ℝ)

def A11 (d : ℝ) : ℝ := (169100963983 / 80240180000 : ℝ) + (21409243 / 10015000 : ℝ) * d + (2003 / 500 : ℝ) * d ^ 2
def B11 (d : ℝ) : ℝ := (-314970949 / 160240000 : ℝ) + (11431 / 20000 : ℝ) * d
def R111 (d : ℝ) : ℝ := (-455035965839 / 1604803600000 : ℝ) + (115219013 / 801200000 : ℝ) * d
def R211 (d : ℝ) : ℝ := (2516498462933 / 16048036000000 : ℝ) + (115219013 / 801200000 : ℝ) * d

def A12 (d : ℝ) : ℝ := (-18006333647147 / 17652839600000 : ℝ) + (-6025295213 / 1762640000 : ℝ) * d + (1203643 / 1100000 : ℝ) * d ^ 2 + (-78 / 55 : ℝ) * d ^ 3
def R12 (d : ℝ) : ℝ := (-2033861195457 / 32096072000000 : ℝ) + (115219013 / 801200000 : ℝ) * d

def m00 (d y : ℝ) : ℝ := ratPart (A00 d) 0 (R00 d) 0 (h d) k y + ratPart 0 0 (R00 d) 0 (h d) (-k) y
def m01 (d y : ℝ) : ℝ := ratPart (A01 d) (B01 d) (R101 d) 0 (h d) k y + ratPart 0 0 (R201 d) (S201 d) (h d) (-k) y
def m02 (d y : ℝ) : ℝ := ratPart (A01 d) (-B01 d) (R101 d) 0 (h d) (-k) y + ratPart 0 0 (R201 d) (S201 d) (h d) k y
def m11 (d y : ℝ) : ℝ := ratPart (A11 d) (B11 d) (R111 d) 0 (h d) k y + ratPart 0 0 (R211 d) 0 (h d) (-k) y
def m22 (d y : ℝ) : ℝ := ratPart (A11 d) (-B11 d) (R111 d) 0 (h d) (-k) y + ratPart 0 0 (R211 d) 0 (h d) k y
def m12 (d y : ℝ) : ℝ := ratPart (A12 d) 0 (R12 d) 0 (h d) k y + ratPart 0 0 (R12 d) 0 (h d) (-k) y

lemma betaPack_eq (d y : ℝ) : betaPack U 0 (delta d y) = ![1, h d + k * y, h d + -k * y] := by
  funext i
  fin_cases i <;> simp [betaPack, parents0, theta, delta, cross, tariff, other, h, k, U] <;> ring

lemma m02_eq (d y : ℝ) : m02 d y = m01 d (-y) := by
  simp only [m01, m02, ratPart]; ring_nf
lemma m22_eq (d y : ℝ) : m22 d y = m11 d (-y) := by
  simp only [m11, m22, ratPart]; ring_nf

lemma gE00 (d y : ℝ) (h1 : h d + k * y ≠ 0) (h2 : h d + -k * y ≠ 0) :
    gE (theta U (delta d y)) ![1, h d + k * y, h d + -k * y] (parents0 U 0 (delta d y))
      ![U.Lmaj 0 (args (theta U (delta d y)) ![1, h d + k * y, h d + -k * y] (parents0 U 0 (delta d y)) 0),
        U.Lmaj 2 (args (theta U (delta d y)) ![1, h d + k * y, h d + -k * y] (parents0 U 0 (delta d y)) 1),
        U.Lmaj 2 (args (theta U (delta d y)) ![1, h d + k * y, h d + -k * y] (parents0 U 0 (delta d y)) 2)]
      (target0 U (19 / 20) 0 (delta d y)) 0 0 = m00 d y := by
  simp only [gE, symE, pairE, args, parents0, target0, theta, delta, cross, star_00, star_01,
    star_02, tariff_00, tariff_01, tariff_02, tariff_10, tariff_11, tariff_12, tariff_20, tariff_21,
    tariff_22, Track.Lmaj, Track.z0, Track.K, U, m00, ratPart, A00, R00, A01, B01, R101, R201,
    S201, A11, B11, R111, R211, A12, R12, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.isValue, ↓reduceIte]
  generalize hb1 : h d + k * y = b1 at h1 ⊢
  generalize hb2 : h d + -k * y = b2 at h2 ⊢
  field_simp
  subst hb1 hb2
  simp only [h, k]
  ring

lemma gE01 (d y : ℝ) (h1 : h d + k * y ≠ 0) (h2 : h d + -k * y ≠ 0) :
    gE (theta U (delta d y)) ![1, h d + k * y, h d + -k * y] (parents0 U 0 (delta d y))
      ![U.Lmaj 0 (args (theta U (delta d y)) ![1, h d + k * y, h d + -k * y] (parents0 U 0 (delta d y)) 0),
        U.Lmaj 2 (args (theta U (delta d y)) ![1, h d + k * y, h d + -k * y] (parents0 U 0 (delta d y)) 1),
        U.Lmaj 2 (args (theta U (delta d y)) ![1, h d + k * y, h d + -k * y] (parents0 U 0 (delta d y)) 2)]
      (target0 U (19 / 20) 0 (delta d y)) 0 1 = m01 d y := by
  simp only [gE, symE, pairE, args, parents0, target0, theta, delta, cross, star_00, star_01,
    star_02, tariff_00, tariff_01, tariff_02, tariff_10, tariff_11, tariff_12, tariff_20, tariff_21,
    tariff_22, Track.Lmaj, Track.z0, Track.K, U, m01, ratPart, A00, R00, A01, B01, R101, R201,
    S201, A11, B11, R111, R211, A12, R12, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.isValue, ↓reduceIte]
  generalize hb1 : h d + k * y = b1 at h1 ⊢
  generalize hb2 : h d + -k * y = b2 at h2 ⊢
  field_simp
  subst hb1 hb2
  simp only [h, k]
  ring

lemma gE02 (d y : ℝ) (h1 : h d + k * y ≠ 0) (h2 : h d + -k * y ≠ 0) :
    gE (theta U (delta d y)) ![1, h d + k * y, h d + -k * y] (parents0 U 0 (delta d y))
      ![U.Lmaj 0 (args (theta U (delta d y)) ![1, h d + k * y, h d + -k * y] (parents0 U 0 (delta d y)) 0),
        U.Lmaj 2 (args (theta U (delta d y)) ![1, h d + k * y, h d + -k * y] (parents0 U 0 (delta d y)) 1),
        U.Lmaj 2 (args (theta U (delta d y)) ![1, h d + k * y, h d + -k * y] (parents0 U 0 (delta d y)) 2)]
      (target0 U (19 / 20) 0 (delta d y)) 0 2 = m02 d y := by
  simp only [gE, symE, pairE, args, parents0, target0, theta, delta, cross, star_00, star_01,
    star_02, tariff_00, tariff_01, tariff_02, tariff_10, tariff_11, tariff_12, tariff_20, tariff_21,
    tariff_22, Track.Lmaj, Track.z0, Track.K, U, m02, ratPart, A00, R00, A01, B01, R101, R201,
    S201, A11, B11, R111, R211, A12, R12, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.isValue, ↓reduceIte]
  generalize hb1 : h d + k * y = b1 at h1 ⊢
  generalize hb2 : h d + -k * y = b2 at h2 ⊢
  field_simp
  subst hb1 hb2
  simp only [h, k]
  ring

lemma gE11 (d y : ℝ) (h1 : h d + k * y ≠ 0) (h2 : h d + -k * y ≠ 0) :
    gE (theta U (delta d y)) ![1, h d + k * y, h d + -k * y] (parents0 U 0 (delta d y))
      ![U.Lmaj 0 (args (theta U (delta d y)) ![1, h d + k * y, h d + -k * y] (parents0 U 0 (delta d y)) 0),
        U.Lmaj 2 (args (theta U (delta d y)) ![1, h d + k * y, h d + -k * y] (parents0 U 0 (delta d y)) 1),
        U.Lmaj 2 (args (theta U (delta d y)) ![1, h d + k * y, h d + -k * y] (parents0 U 0 (delta d y)) 2)]
      (target0 U (19 / 20) 0 (delta d y)) 1 1 = m11 d y := by
  simp only [gE, symE, pairE, args, parents0, target0, theta, delta, cross, star_00, star_01,
    star_02, tariff_00, tariff_01, tariff_02, tariff_10, tariff_11, tariff_12, tariff_20, tariff_21,
    tariff_22, Track.Lmaj, Track.z0, Track.K, U, m11, ratPart, A00, R00, A01, B01, R101, R201,
    S201, A11, B11, R111, R211, A12, R12, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.isValue, ↓reduceIte]
  generalize hb1 : h d + k * y = b1 at h1 ⊢
  generalize hb2 : h d + -k * y = b2 at h2 ⊢
  field_simp
  subst hb1 hb2
  simp only [h, k]
  ring

lemma gE12 (d y : ℝ) (h1 : h d + k * y ≠ 0) (h2 : h d + -k * y ≠ 0) :
    gE (theta U (delta d y)) ![1, h d + k * y, h d + -k * y] (parents0 U 0 (delta d y))
      ![U.Lmaj 0 (args (theta U (delta d y)) ![1, h d + k * y, h d + -k * y] (parents0 U 0 (delta d y)) 0),
        U.Lmaj 2 (args (theta U (delta d y)) ![1, h d + k * y, h d + -k * y] (parents0 U 0 (delta d y)) 1),
        U.Lmaj 2 (args (theta U (delta d y)) ![1, h d + k * y, h d + -k * y] (parents0 U 0 (delta d y)) 2)]
      (target0 U (19 / 20) 0 (delta d y)) 1 2 = m12 d y := by
  simp only [gE, symE, pairE, args, parents0, target0, theta, delta, cross, star_00, star_01,
    star_02, tariff_00, tariff_01, tariff_02, tariff_10, tariff_11, tariff_12, tariff_20, tariff_21,
    tariff_22, Track.Lmaj, Track.z0, Track.K, U, m12, ratPart, A00, R00, A01, B01, R101, R201,
    S201, A11, B11, R111, R211, A12, R12, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.isValue, ↓reduceIte]
  generalize hb1 : h d + k * y = b1 at h1 ⊢
  generalize hb2 : h d + -k * y = b2 at h2 ⊢
  field_simp
  subst hb1 hb2
  simp only [h, k]
  ring

lemma gE22 (d y : ℝ) (h1 : h d + k * y ≠ 0) (h2 : h d + -k * y ≠ 0) :
    gE (theta U (delta d y)) ![1, h d + k * y, h d + -k * y] (parents0 U 0 (delta d y))
      ![U.Lmaj 0 (args (theta U (delta d y)) ![1, h d + k * y, h d + -k * y] (parents0 U 0 (delta d y)) 0),
        U.Lmaj 2 (args (theta U (delta d y)) ![1, h d + k * y, h d + -k * y] (parents0 U 0 (delta d y)) 1),
        U.Lmaj 2 (args (theta U (delta d y)) ![1, h d + k * y, h d + -k * y] (parents0 U 0 (delta d y)) 2)]
      (target0 U (19 / 20) 0 (delta d y)) 2 2 = m22 d y := by
  simp only [gE, symE, pairE, args, parents0, target0, theta, delta, cross, star_00, star_01,
    star_02, tariff_00, tariff_01, tariff_02, tariff_10, tariff_11, tariff_12, tariff_20, tariff_21,
    tariff_22, Track.Lmaj, Track.z0, Track.K, U, m22, ratPart, A00, R00, A01, B01, R101, R201,
    S201, A11, B11, R111, R211, A12, R12, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.isValue, ↓reduceIte]
  generalize hb1 : h d + k * y = b1 at h1 ⊢
  generalize hb2 : h d + -k * y = b2 at h2 ⊢
  field_simp
  subst hb1 hb2
  simp only [h, k]
  ring

/-- The packed majorant form at error 0 is the quadratic form of the decomposed matrix. -/
theorem packHat_eq (d y : ℝ) (x : Fin 3 → ℝ) (h1 : h d + k * y ≠ 0) (h2 : h d + -k * y ≠ 0) :
    packHat U 0 d y x = quad3 (m00 d y) (m01 d y) (m02 d y) (m11 d y) (m12 d y) (m22 d y) x := by
  rw [packHat, betaPack_eq, form0_eq_quad3, gE00 d y h1 h2, gE01 d y h1 h2, gE02 d y h1 h2,
    gE11 d y h1 h2, gE12 d y h1 h2, gE22 d y h1 h2]

end OM.NNN18.PackU
