import Lib.OM.NNN18.PackedLemmas

/-!
At focus 0 and error 0, for fixed `d`, each entry is a sum of two `ratPart`s in `y`
with denominators `β₁ = h + κy/2`, `β₂ = h - κy/2`, `h = β* - κd/2`.  The identity
with `packHat` is checked by `field_simp; ring`.
-/

noncomputable section
namespace OM.NNN18.PackC

set_option maxHeartbeats 8000000

/-- `κ/2` -/
def k : ℝ := (31 / 80 : ℝ)
/-- `h(d) = β* - κd/2` -/
def h (d : ℝ) : ℝ := (23293 / 30000 : ℝ) - (31 / 80 : ℝ) * d

def A00 (d : ℝ) : ℝ := (2084351 / 4805000 : ℝ) + (-969 / 310 : ℝ) * d
def R00 (d : ℝ) : ℝ := (650770051 / 1801875000 : ℝ) + (-7793 / 38750 : ℝ) * d

def A01 (d : ℝ) : ℝ := (-70974667583506771 / 201471915395000000 : ℝ) + (27899366556235187 / 15597825708000000 : ℝ) * d + (-13 / 8 : ℝ) * d ^ 2
def B01 (d : ℝ) : ℝ := (8850568676378729 / 5199275236000000 : ℝ)
def R101 (d : ℝ) : ℝ := (-650770051 / 21622500000 : ℝ) + (7793 / 465000 : ℝ) * d
def R201 (d : ℝ) : ℝ := (-585596266720612219 / 1948889981250000000 : ℝ) + (7793 / 465000 : ℝ) * d
def S201 (d : ℝ) : ℝ := (5206030568827 / 125680781250000 : ℝ)

def A11 (d : ℝ) : ℝ := (221251 / 111600 : ℝ) + (96111 / 62000 : ℝ) * d + (31 / 8 : ℝ) * d ^ 2
def B11 (d : ℝ) : ℝ := (-1565 / 744 : ℝ) + (5 / 8 : ℝ) * d
def R111 (d : ℝ) : ℝ := (-650770051 / 2162250000 : ℝ) + (7793 / 46500 : ℝ) * d
def R211 (d : ℝ) : ℝ := (181522349 / 1081125000 : ℝ) + (7793 / 46500 : ℝ) * d

def A12 (d : ℝ) : ℝ := (-65229217 / 76725000 : ℝ) + (-86747511 / 21700000 : ℝ) * d + (3023 / 3080 : ℝ) * d ^ 2 + (-78 / 55 : ℝ) * d ^ 3
def R12 (d : ℝ) : ℝ := (-3093821 / 46500000 : ℝ) + (7793 / 46500 : ℝ) * d

def m00 (d y : ℝ) : ℝ := ratPart (A00 d) 0 (R00 d) 0 (h d) k y + ratPart 0 0 (R00 d) 0 (h d) (-k) y
def m01 (d y : ℝ) : ℝ := ratPart (A01 d) (B01 d) (R101 d) 0 (h d) k y + ratPart 0 0 (R201 d) (S201 d) (h d) (-k) y
def m02 (d y : ℝ) : ℝ := ratPart (A01 d) (-B01 d) (R101 d) 0 (h d) (-k) y + ratPart 0 0 (R201 d) (S201 d) (h d) k y
def m11 (d y : ℝ) : ℝ := ratPart (A11 d) (B11 d) (R111 d) 0 (h d) k y + ratPart 0 0 (R211 d) 0 (h d) (-k) y
def m22 (d y : ℝ) : ℝ := ratPart (A11 d) (-B11 d) (R111 d) 0 (h d) (-k) y + ratPart 0 0 (R211 d) 0 (h d) k y
def m12 (d y : ℝ) : ℝ := ratPart (A12 d) 0 (R12 d) 0 (h d) k y + ratPart 0 0 (R12 d) 0 (h d) (-k) y

lemma betaPack_eq (d y : ℝ) : betaPack C 0 (delta d y) = ![1, h d + k * y, h d + -k * y] := by
  funext i
  fin_cases i <;> simp [betaPack, parents0, theta, delta, cross, tariff, other, h, k, C] <;> ring

lemma m02_eq (d y : ℝ) : m02 d y = m01 d (-y) := by
  simp only [m01, m02, ratPart]; ring_nf
lemma m22_eq (d y : ℝ) : m22 d y = m11 d (-y) := by
  simp only [m11, m22, ratPart]; ring_nf

lemma gE00 (d y : ℝ) (h1 : h d + k * y ≠ 0) (h2 : h d + -k * y ≠ 0) :
    gE (theta C (delta d y)) ![1, h d + k * y, h d + -k * y] (parents0 C 0 (delta d y))
      ![C.Lmaj 0 (args (theta C (delta d y)) ![1, h d + k * y, h d + -k * y] (parents0 C 0 (delta d y)) 0),
        C.Lmaj 2 (args (theta C (delta d y)) ![1, h d + k * y, h d + -k * y] (parents0 C 0 (delta d y)) 1),
        C.Lmaj 2 (args (theta C (delta d y)) ![1, h d + k * y, h d + -k * y] (parents0 C 0 (delta d y)) 2)]
      (target0 C (19 / 20) 0 (delta d y)) 0 0 = m00 d y := by
  simp only [gE, symE, pairE, args, parents0, target0, theta, delta, cross, star_00, star_01,
    star_02, tariff_00, tariff_01, tariff_02, tariff_10, tariff_11, tariff_12, tariff_20, tariff_21,
    tariff_22, Track.Lmaj, Track.z0, Track.K, C, m00, ratPart, A00, R00, A01, B01, R101, R201,
    S201, A11, B11, R111, R211, A12, R12, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.isValue, ↓reduceIte]
  generalize hb1 : h d + k * y = b1 at h1 ⊢
  generalize hb2 : h d + -k * y = b2 at h2 ⊢
  field_simp
  subst hb1 hb2
  simp only [h, k]
  ring

lemma gE01 (d y : ℝ) (h1 : h d + k * y ≠ 0) (h2 : h d + -k * y ≠ 0) :
    gE (theta C (delta d y)) ![1, h d + k * y, h d + -k * y] (parents0 C 0 (delta d y))
      ![C.Lmaj 0 (args (theta C (delta d y)) ![1, h d + k * y, h d + -k * y] (parents0 C 0 (delta d y)) 0),
        C.Lmaj 2 (args (theta C (delta d y)) ![1, h d + k * y, h d + -k * y] (parents0 C 0 (delta d y)) 1),
        C.Lmaj 2 (args (theta C (delta d y)) ![1, h d + k * y, h d + -k * y] (parents0 C 0 (delta d y)) 2)]
      (target0 C (19 / 20) 0 (delta d y)) 0 1 = m01 d y := by
  simp only [gE, symE, pairE, args, parents0, target0, theta, delta, cross, star_00, star_01,
    star_02, tariff_00, tariff_01, tariff_02, tariff_10, tariff_11, tariff_12, tariff_20, tariff_21,
    tariff_22, Track.Lmaj, Track.z0, Track.K, C, m01, ratPart, A00, R00, A01, B01, R101, R201,
    S201, A11, B11, R111, R211, A12, R12, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.isValue, ↓reduceIte]
  generalize hb1 : h d + k * y = b1 at h1 ⊢
  generalize hb2 : h d + -k * y = b2 at h2 ⊢
  field_simp
  subst hb1 hb2
  simp only [h, k]
  ring

lemma gE02 (d y : ℝ) (h1 : h d + k * y ≠ 0) (h2 : h d + -k * y ≠ 0) :
    gE (theta C (delta d y)) ![1, h d + k * y, h d + -k * y] (parents0 C 0 (delta d y))
      ![C.Lmaj 0 (args (theta C (delta d y)) ![1, h d + k * y, h d + -k * y] (parents0 C 0 (delta d y)) 0),
        C.Lmaj 2 (args (theta C (delta d y)) ![1, h d + k * y, h d + -k * y] (parents0 C 0 (delta d y)) 1),
        C.Lmaj 2 (args (theta C (delta d y)) ![1, h d + k * y, h d + -k * y] (parents0 C 0 (delta d y)) 2)]
      (target0 C (19 / 20) 0 (delta d y)) 0 2 = m02 d y := by
  simp only [gE, symE, pairE, args, parents0, target0, theta, delta, cross, star_00, star_01,
    star_02, tariff_00, tariff_01, tariff_02, tariff_10, tariff_11, tariff_12, tariff_20, tariff_21,
    tariff_22, Track.Lmaj, Track.z0, Track.K, C, m02, ratPart, A00, R00, A01, B01, R101, R201,
    S201, A11, B11, R111, R211, A12, R12, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.isValue, ↓reduceIte]
  generalize hb1 : h d + k * y = b1 at h1 ⊢
  generalize hb2 : h d + -k * y = b2 at h2 ⊢
  field_simp
  subst hb1 hb2
  simp only [h, k]
  ring

lemma gE11 (d y : ℝ) (h1 : h d + k * y ≠ 0) (h2 : h d + -k * y ≠ 0) :
    gE (theta C (delta d y)) ![1, h d + k * y, h d + -k * y] (parents0 C 0 (delta d y))
      ![C.Lmaj 0 (args (theta C (delta d y)) ![1, h d + k * y, h d + -k * y] (parents0 C 0 (delta d y)) 0),
        C.Lmaj 2 (args (theta C (delta d y)) ![1, h d + k * y, h d + -k * y] (parents0 C 0 (delta d y)) 1),
        C.Lmaj 2 (args (theta C (delta d y)) ![1, h d + k * y, h d + -k * y] (parents0 C 0 (delta d y)) 2)]
      (target0 C (19 / 20) 0 (delta d y)) 1 1 = m11 d y := by
  simp only [gE, symE, pairE, args, parents0, target0, theta, delta, cross, star_00, star_01,
    star_02, tariff_00, tariff_01, tariff_02, tariff_10, tariff_11, tariff_12, tariff_20, tariff_21,
    tariff_22, Track.Lmaj, Track.z0, Track.K, C, m11, ratPart, A00, R00, A01, B01, R101, R201,
    S201, A11, B11, R111, R211, A12, R12, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.isValue, ↓reduceIte]
  generalize hb1 : h d + k * y = b1 at h1 ⊢
  generalize hb2 : h d + -k * y = b2 at h2 ⊢
  field_simp
  subst hb1 hb2
  simp only [h, k]
  ring

lemma gE12 (d y : ℝ) (h1 : h d + k * y ≠ 0) (h2 : h d + -k * y ≠ 0) :
    gE (theta C (delta d y)) ![1, h d + k * y, h d + -k * y] (parents0 C 0 (delta d y))
      ![C.Lmaj 0 (args (theta C (delta d y)) ![1, h d + k * y, h d + -k * y] (parents0 C 0 (delta d y)) 0),
        C.Lmaj 2 (args (theta C (delta d y)) ![1, h d + k * y, h d + -k * y] (parents0 C 0 (delta d y)) 1),
        C.Lmaj 2 (args (theta C (delta d y)) ![1, h d + k * y, h d + -k * y] (parents0 C 0 (delta d y)) 2)]
      (target0 C (19 / 20) 0 (delta d y)) 1 2 = m12 d y := by
  simp only [gE, symE, pairE, args, parents0, target0, theta, delta, cross, star_00, star_01,
    star_02, tariff_00, tariff_01, tariff_02, tariff_10, tariff_11, tariff_12, tariff_20, tariff_21,
    tariff_22, Track.Lmaj, Track.z0, Track.K, C, m12, ratPart, A00, R00, A01, B01, R101, R201,
    S201, A11, B11, R111, R211, A12, R12, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.isValue, ↓reduceIte]
  generalize hb1 : h d + k * y = b1 at h1 ⊢
  generalize hb2 : h d + -k * y = b2 at h2 ⊢
  field_simp
  subst hb1 hb2
  simp only [h, k]
  ring

lemma gE22 (d y : ℝ) (h1 : h d + k * y ≠ 0) (h2 : h d + -k * y ≠ 0) :
    gE (theta C (delta d y)) ![1, h d + k * y, h d + -k * y] (parents0 C 0 (delta d y))
      ![C.Lmaj 0 (args (theta C (delta d y)) ![1, h d + k * y, h d + -k * y] (parents0 C 0 (delta d y)) 0),
        C.Lmaj 2 (args (theta C (delta d y)) ![1, h d + k * y, h d + -k * y] (parents0 C 0 (delta d y)) 1),
        C.Lmaj 2 (args (theta C (delta d y)) ![1, h d + k * y, h d + -k * y] (parents0 C 0 (delta d y)) 2)]
      (target0 C (19 / 20) 0 (delta d y)) 2 2 = m22 d y := by
  simp only [gE, symE, pairE, args, parents0, target0, theta, delta, cross, star_00, star_01,
    star_02, tariff_00, tariff_01, tariff_02, tariff_10, tariff_11, tariff_12, tariff_20, tariff_21,
    tariff_22, Track.Lmaj, Track.z0, Track.K, C, m22, ratPart, A00, R00, A01, B01, R101, R201,
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
    packHat C 0 d y x = quad3 (m00 d y) (m01 d y) (m02 d y) (m11 d y) (m12 d y) (m22 d y) x := by
  rw [packHat, betaPack_eq, form0_eq_quad3, gE00 d y h1 h2, gE01 d y h1 h2, gE02 d y h1 h2,
    gE11 d y h1 h2, gE12 d y h1 h2, gE22 d y h1 h2]

end OM.NNN18.PackC
