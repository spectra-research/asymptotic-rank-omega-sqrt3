import Lib.OM.NNN18.PackedLemmas

/-!
`m` is the packed source matrix in partial-fraction form (one `d` fixed, variable `y`),
`n` the entrywise concave lower matrix (7.1): `n00 = m00(d,0)`, `n11 = m11 - K (y-H)_+²`,
`n22 = m22 - K (-y-H)_+²`, other entries equal.  From the curvature signs and the
positivity of the endpoint matrix `n(d, d+2R)` we get `xᵀ m(d,y) x ≥ 0` for every `x ≥ 0`
on the triangle `-2R ≤ d ≤ R`, `|y| ≤ d + 2R`.
-/

noncomputable section
open Set
namespace OM.NNN18

section
variable (k K H : ℝ) (h : ℝ → ℝ)
  (A00 R00 A01 B01 R101 R201 S201 A11 B11 R111 R211 A12 R12 : ℝ → ℝ)

def dm00 (d y : ℝ) : ℝ := ratPart (A00 d) 0 (R00 d) 0 (h d) k y + ratPart 0 0 (R00 d) 0 (h d) (-k) y
def dm01 (d y : ℝ) : ℝ :=
  ratPart (A01 d) (B01 d) (R101 d) 0 (h d) k y + ratPart 0 0 (R201 d) (S201 d) (h d) (-k) y
def dm02 (d y : ℝ) : ℝ :=
  ratPart (A01 d) (-B01 d) (R101 d) 0 (h d) (-k) y + ratPart 0 0 (R201 d) (S201 d) (h d) k y
def dm11 (d y : ℝ) : ℝ :=
  ratPart (A11 d) (B11 d) (R111 d) 0 (h d) k y + ratPart 0 0 (R211 d) 0 (h d) (-k) y
def dm22 (d y : ℝ) : ℝ :=
  ratPart (A11 d) (-B11 d) (R111 d) 0 (h d) (-k) y + ratPart 0 0 (R211 d) 0 (h d) k y
def dm12 (d y : ℝ) : ℝ := ratPart (A12 d) 0 (R12 d) 0 (h d) k y + ratPart 0 0 (R12 d) 0 (h d) (-k) y

/-- The endpoint lower matrix form `xᵀ n(d, Y) x`. -/
def endForm (d Y : ℝ) (x : Fin 3 → ℝ) : ℝ :=
  quad3 (dm00 k h A00 R00 d 0) (dm01 k h A01 B01 R101 R201 S201 d Y)
    (dm02 k h A01 B01 R101 R201 S201 d Y) (dm11 k h A11 B11 R111 R211 d Y - K * hinge H Y)
    (dm12 k h A12 R12 d Y) (dm22 k h A11 B11 R111 R211 d Y - K * hinge H (-Y)) x
end

lemma concaveOn_reflect {f : ℝ → ℝ} {Y : ℝ} (hf : ConcaveOn ℝ (Icc (-Y) Y) f) :
    ConcaveOn ℝ (Icc (-Y) Y) (fun y => f (-y)) := by
  refine ⟨convex_Icc _ _, ?_⟩
  intro x hx y hy a b ha hb hab
  have hx' : -x ∈ Icc (-Y) Y := ⟨by linarith [hx.2], by linarith [hx.1]⟩
  have hy' : -y ∈ Icc (-Y) Y := ⟨by linarith [hy.2], by linarith [hy.1]⟩
  have := hf.2 hx' hy' ha hb hab
  simp only [smul_eq_mul] at this ⊢
  have e : a * -x + b * -y = -(a * x + b * y) := by ring
  rwa [e] at this

lemma hinge_eq_zero {H y : ℝ} (hy : y ≤ H) : hinge H y = 0 := by
  simp [hinge, max_eq_right (by linarith : y - H ≤ 0)]

lemma hinge_nonneg (H y : ℝ) : 0 ≤ hinge H y := by unfold hinge; positivity

set_option maxHeartbeats 2000000 in
theorem packed_base (k K H R bs : ℝ) (h : ℝ → ℝ)
    (A00 R00 A01 B01 R101 R201 S201 A11 B11 R111 R211 A12 R12 : ℝ → ℝ)
    (hk : 0 < k) (hK : 0 ≤ K) (hH : 0 ≤ H) (hR : 0 < R)
    (hh : ∀ d, h d = bs - k * d) (hpos : 0 < bs - 4 * k * R)
    (h00 : ∀ d, -2 * R ≤ d → d ≤ R → 0 ≤ R00 d)
    (h01a : ∀ d, -2 * R ≤ d → d ≤ R → R101 d ≤ 0)
    (h01b : ∀ d β, -2 * R ≤ d → d ≤ R → bs - 4 * k * R ≤ β → β ≤ bs + 2 * k * R →
      R201 d * β + 3 * S201 d ≤ 0)
    (h12 : ∀ d, -2 * R ≤ d → d ≤ R → R12 d ≤ 0)
    (h11n : ∀ d y, -2 * R ≤ d → d ≤ R → -(d + 2 * R) ≤ y → y ≤ d + 2 * R → y ≤ H →
      hingeCurv (R111 d) (R211 d) (h d) k y ≤ 0)
    (h11p : ∀ d y, -2 * R ≤ d → d ≤ R → -(d + 2 * R) ≤ y → y ≤ d + 2 * R → H ≤ y →
      hingeCurv (R111 d) (R211 d) (h d) k y ≤ 2 * K)
    (hend : ∀ d, -2 * R ≤ d → d ≤ R → ∀ x : Fin 3 → ℝ,
      0 ≤ endForm k K H h A00 R00 A01 B01 R101 R201 S201 A11 B11 R111 R211 A12 R12 d (d + 2 * R) x)
    {d y : ℝ} (hd₁ : -2 * R ≤ d) (hd₂ : d ≤ R) (hy₁ : -(d + 2 * R) ≤ y) (hy₂ : y ≤ d + 2 * R)
    {x : Fin 3 → ℝ} (hx : ∀ i, 0 ≤ x i) :
    0 ≤ quad3 (dm00 k h A00 R00 d y) (dm01 k h A01 B01 R101 R201 S201 d y)
      (dm02 k h A01 B01 R101 R201 S201 d y) (dm11 k h A11 B11 R111 R211 d y)
      (dm12 k h A12 R12 d y) (dm22 k h A11 B11 R111 R211 d y) x := by
  set Y := d + 2 * R with hYdef
  have hY0 : 0 ≤ Y := by linarith
  have kd₁ := mul_le_mul_of_nonneg_left hd₁ hk.le
  have kd₂ := mul_le_mul_of_nonneg_left hd₂ hk.le
  -- denominators on the whole segment
  have hb : ∀ w ∈ Icc (-Y) Y, 0 < h d + k * w ∧ 0 < h d + -k * w ∧
      bs - 4 * k * R ≤ h d + k * w ∧ h d + k * w ≤ bs + 2 * k * R ∧
      bs - 4 * k * R ≤ h d + -k * w ∧ h d + -k * w ≤ bs + 2 * k * R := by
    intro w hw
    have kw₁ := mul_le_mul_of_nonneg_left hw.1 hk.le
    have kw₂ := mul_le_mul_of_nonneg_left hw.2 hk.le
    have kY : k * Y = k * d + 2 * (k * R) := by rw [hYdef]; ring
    have kR : 0 ≤ k * R := (mul_pos hk hR).le
    rw [hh d]
    refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩
  have hb2 : ∀ w ∈ Icc (-Y) Y, 0 < h d + k * w ∧ 0 < h d - k * w := fun w hw =>
    ⟨(hb w hw).1, by have := (hb w hw).2.1; linarith⟩
  have hx01 := mul_nonneg (hx 0) (hx 1)
  have hx02 := mul_nonneg (hx 0) (hx 2)
  have hx12 := mul_nonneg (hx 1) (hx 2)
  -- the lower matrix entries
  let n00 : ℝ := dm00 k h A00 R00 d 0
  let n01 : ℝ → ℝ := dm01 k h A01 B01 R101 R201 S201 d
  let n02 : ℝ → ℝ := dm02 k h A01 B01 R101 R201 S201 d
  let n11 : ℝ → ℝ := fun w => dm11 k h A11 B11 R111 R211 d w - K * hinge H w
  let n12 : ℝ → ℝ := dm12 k h A12 R12 d
  let n22 : ℝ → ℝ := fun w => dm22 k h A11 B11 R111 R211 d w - K * hinge H (-w)
  -- (1) entrywise comparison m ≥ n at y
  have hmn : quad3 n00 (n01 y) (n02 y) (n11 y) (n12 y) (n22 y) x ≤
      quad3 (dm00 k h A00 R00 d y) (dm01 k h A01 B01 R101 R201 S201 d y)
        (dm02 k h A01 B01 R101 R201 S201 d y) (dm11 k h A11 B11 R111 R211 d y)
        (dm12 k h A12 R12 d y) (dm22 k h A11 B11 R111 R211 d y) x := by
    have hy : y ∈ Icc (-Y) Y := ⟨hy₁, hy₂⟩
    have c00 : n00 ≤ dm00 k h A00 R00 d y := by
      have := ratPair_ge_center (A := A00 d) (ρ := R00 d) (k := k) (y := y) (h00 d hd₁ hd₂)
        (by rw [hh d]; have := (mul_pos hk hR).le; linarith) (hb y hy).1 (hb2 y hy).2
      simpa [n00, dm00] using this
    have c11 : n11 y ≤ dm11 k h A11 B11 R111 R211 d y := by
      have := hinge_nonneg H y; simp only [n11]; nlinarith
    have c22 : n22 y ≤ dm22 k h A11 B11 R111 R211 d y := by
      have := hinge_nonneg H (-y); simp only [n22]; nlinarith
    simp only [quad3]
    have := mul_le_mul_of_nonneg_right c00 (sq_nonneg (x 0))
    have := mul_le_mul_of_nonneg_right c11 (sq_nonneg (x 1))
    have := mul_le_mul_of_nonneg_right c22 (sq_nonneg (x 2))
    linarith
  -- (2) endpoint forms
  have hE : 0 ≤ quad3 n00 (n01 Y) (n02 Y) (n11 Y) (n12 Y) (n22 Y) x := hend d hd₁ hd₂ x
  have hE' : 0 ≤ quad3 n00 (n01 (-Y)) (n02 (-Y)) (n11 (-Y)) (n12 (-Y)) (n22 (-Y)) x := by
    have h1 : n01 (-Y) = n02 Y := by simp only [n01, n02, dm01, dm02, ratPart]; ring_nf
    have h2 : n02 (-Y) = n01 Y := by simp only [n01, n02, dm01, dm02, ratPart]; ring_nf
    have h3 : n11 (-Y) = n22 Y := by
      simp only [n11, n22, dm11, dm22, ratPart]; ring_nf
    have h4 : n22 (-Y) = n11 Y := by
      simp only [n11, n22, dm11, dm22, ratPart]; ring_nf
    have h5 : n12 (-Y) = n12 Y := by simp only [n12, dm12, ratPart]; ring_nf
    have := hend d hd₁ hd₂ ![x 0, x 2, x 1]
    rw [h1, h2, h3, h4, h5]
    convert this using 1
    simp only [quad3, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, endForm, n00, n01, n02, n11, n12, n22]
    ring
  rcases eq_or_lt_of_le hY0 with hYz | hYp
  · -- degenerate edge Y = 0, so y = 0 = Y
    have hy0 : y = Y := by linarith
    rw [hy0] at hmn ⊢
    exact hE.trans hmn
  -- (3) concavity of each lower entry in y on [-Y, Y]
  have cv01 : ConcaveOn ℝ (Icc (-Y) Y) n01 := by
    apply ConcaveOn.add
    · apply concaveOn_ratPart (fun w hw => (hb w hw).1)
      intro w hw; have := (hb w hw).1; have := h01a d hd₁ hd₂; nlinarith
    · apply concaveOn_ratPart (fun w hw => (hb w hw).2.1)
      intro w hw
      exact h01b d _ hd₁ hd₂ (hb w hw).2.2.2.2.1 (hb w hw).2.2.2.2.2
  have cv02 : ConcaveOn ℝ (Icc (-Y) Y) n02 := by
    apply ConcaveOn.add
    · apply concaveOn_ratPart (fun w hw => (hb w hw).2.1)
      intro w hw; have := (hb w hw).2.1; have := h01a d hd₁ hd₂; nlinarith
    · apply concaveOn_ratPart (fun w hw => (hb w hw).1)
      intro w hw
      exact h01b d _ hd₁ hd₂ (hb w hw).2.2.1 (hb w hw).2.2.2.1
  have cv12 : ConcaveOn ℝ (Icc (-Y) Y) n12 := by
    apply ConcaveOn.add
    · apply concaveOn_ratPart (fun w hw => (hb w hw).1)
      intro w hw; have := (hb w hw).1; have := h12 d hd₁ hd₂; nlinarith
    · apply concaveOn_ratPart (fun w hw => (hb w hw).2.1)
      intro w hw; have := (hb w hw).2.1; have := h12 d hd₁ hd₂; nlinarith
  have cv11 : ConcaveOn ℝ (Icc (-Y) Y) n11 :=
    concaveOn_hingeEntry hb2
      (fun w hw hwH => h11n d w hd₁ hd₂ hw.1 hw.2 hwH)
      (fun w hw hHw => h11p d w hd₁ hd₂ hw.1 hw.2 hHw)
  have cv22 : ConcaveOn ℝ (Icc (-Y) Y) n22 := by
    have := concaveOn_reflect cv11
    convert this using 1
    funext w
    simp only [n11, n22, dm11, dm22, ratPart]; ring_nf
  -- (4) chord inequalities and the final combination
  have ch01 := chord_of_concave hYp cv01 hy₁ hy₂
  have ch02 := chord_of_concave hYp cv02 hy₁ hy₂
  have ch11 := chord_of_concave hYp cv11 hy₁ hy₂
  have ch12 := chord_of_concave hYp cv12 hy₁ hy₂
  have ch22 := chord_of_concave hYp cv22 hy₁ hy₂
  set l₁ := (Y - y) / (2 * Y)
  set l₂ := (Y + y) / (2 * Y)
  have hl1 : 0 ≤ l₁ := div_nonneg (by linarith) (by linarith)
  have hl2 : 0 ≤ l₂ := div_nonneg (by linarith) (by linarith)
  have hsum : l₁ + l₂ = 1 := by simp only [l₁, l₂]; field_simp; ring
  have hcomb : l₁ * quad3 n00 (n01 (-Y)) (n02 (-Y)) (n11 (-Y)) (n12 (-Y)) (n22 (-Y)) x
      + l₂ * quad3 n00 (n01 Y) (n02 Y) (n11 Y) (n12 Y) (n22 Y) x ≤
      quad3 n00 (n01 y) (n02 y) (n11 y) (n12 y) (n22 y) x := by
    simp only [quad3]
    have t1 := mul_le_mul_of_nonneg_right ch01 (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hx01)
    have t2 := mul_le_mul_of_nonneg_right ch02 (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hx02)
    have t3 := mul_le_mul_of_nonneg_right ch11 (sq_nonneg (x 1))
    have t4 := mul_le_mul_of_nonneg_right ch12 (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hx12)
    have t5 := mul_le_mul_of_nonneg_right ch22 (sq_nonneg (x 2))
    have e00 : l₁ * (n00 * x 0 ^ 2) + l₂ * (n00 * x 0 ^ 2) = n00 * x 0 ^ 2 := by
      rw [← add_mul, hsum, one_mul]
    linarith [t1, t2, t3, t4, t5, e00]
  have := add_nonneg (mul_nonneg hl1 hE') (mul_nonneg hl2 hE)
  linarith

end OM.NNN18
