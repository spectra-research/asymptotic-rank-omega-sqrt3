import Lib.OM.NNN11.InnerCaps

/-! The asymmetric inner envelope and the affordable-head choice between the
two short parties. This module is numerical; the tensor restriction is separate. -/
noncomputable section
namespace OM.NNN11
set_option maxHeartbeats 3000000

def asymmetricCapacity (t u w : ℝ) : ℝ :=
  7 * weightedK t + 13 / 2 * (weightedK u + weightedK w)
def asymmetricF (t u w : ℝ) : ℝ :=
  91 / 2 * (9 / 4) + 7 / 2 * t + 56 * (9 / 4) ^ 2 + 14 * (9 / 4) * t -
    70 * t ^ 2 - 56 * (u ^ 2 + w ^ 2) - asymmetricCapacity t u w
def asymmetricG (t u w : ℝ) : ℝ :=
  21 * (9 / 4) + 28 * t + 126 * t * (9 / 4 - t) - asymmetricCapacity t u w

theorem asymmetric_envelope {t u w : ℝ}
    (hu : u ∈ Set.Icc (1 / 4 : ℝ) 1) (hw : w ∈ Set.Icc (1 / 4 : ℝ) 1)
    (hs : t + u + w = 9 / 4) :
    asymmetricF t u w ≤ numeratorF t ∧ numeratorG t ≤ asymmetricG t u w := by
  have hm : (1 / 2 : ℝ) * u + (1 / 2 : ℝ) * w = shortParam t := by
    dsimp [shortParam]
    linarith
  have hk := weightedK_concave.2 hu hw (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  have hq := inner_quadratic_concave.2 hu hw (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  simp only [smul_eq_mul, hm] at hk hq
  rw [numeratorF_paper, numeratorG_paper]
  dsimp [asymmetricF, asymmetricG, asymmetricCapacity, capacity]
  constructor <;> linarith

def centralSource (t m H : ℝ) : ℝ := (9 / 4 - t) * (m - H)
def shortSource (t u m H : ℝ) : ℝ := (9 / 4 - u) * m - t * H
def rectRawRate (q b t a S L : ℝ) : ℝ := q * (a - S) + b * L * codeK t

/-- `h = true` assigns the 28 heavy copies to the first short party. -/
def rectHead (clip : ℝ → ℝ) (h : Bool) (t u w m H a : ℝ) : ℝ :=
  21 * ((9 / 2) * m - (9 / 4 + t) * H) +
    7 * (if h then shortSource t u m H else shortSource t w m H) -
    t * clip (rectRawRate 70 7 t a (centralSource t m H) (m - H)) -
    u * clip (rectRawRate (if h then 42 else 70) (if h then 6 else 7)
      u a (shortSource t u m H) (m - H)) -
    w * clip (rectRawRate (if h then 70 else 42) (if h then 7 else 6)
      w a (shortSource t w m H) (m - H))

lemma rectHead_average (t u w m H a : ℝ) (hs : t + u + w = 9 / 4) :
    (rectHead id true t u w m H a + rectHead id false t u w m H a) / 2 - 70 * a =
      m * asymmetricF t u w - H * asymmetricG t u w - denominator t * a := by
  have hw : w = 9 / 4 - t - u := by linarith
  subst w
  dsimp [rectHead, rectRawRate, centralSource, shortSource, asymmetricF,
    asymmetricG, asymmetricCapacity, denominator, weightedK]
  ring

lemma rectHead_clipped_le (h : Bool) {t u w : ℝ} (ht : 0 ≤ t) (hu : 0 ≤ u) (hw : 0 ≤ w)
    (m H a : ℝ) : rectHead (fun x => max 0 x) h t u w m H a ≤ rectHead id h t u w m H a := by
  have h0 := mul_le_mul_of_nonneg_left (le_max_right (0 : ℝ)
    (rectRawRate 70 7 t a (centralSource t m H) (m - H))) ht
  have h1 := mul_le_mul_of_nonneg_left (le_max_right (0 : ℝ)
    (rectRawRate (if h then 42 else 70) (if h then 6 else 7) u a (shortSource t u m H) (m - H))) hu
  have h2 := mul_le_mul_of_nonneg_left (le_max_right (0 : ℝ)
    (rectRawRate (if h then 70 else 42) (if h then 7 else 6) w a (shortSource t w m H) (m - H))) hw
  dsimp [rectHead]
  linarith

theorem exists_rect_head {t u w m H : ℝ}
    (ht : t ∈ Set.Icc (1 / 4 : ℝ) 1) (hu : u ∈ Set.Icc (1 / 4 : ℝ) 1)
    (hw : w ∈ Set.Icc (1 / 4 : ℝ) 1) (hs : t + u + w = 9 / 4)
    (hm : 0 ≤ m) (hH : 0 ≤ H) :
    ∃ h : Bool, rectHead (fun x => max 0 x) h t u w m H (m * innerF t - H * innerG t) ≤
      70 * (m * innerF t - H * innerG t) := by
  let a := m * innerF t - H * innerG t
  have ht0 : 0 ≤ t := by linarith [ht.1]
  have henv := asymmetric_envelope hu hw hs
  have hf := mul_le_mul_of_nonneg_left henv.1 hm
  have hg := mul_le_mul_of_nonneg_left henv.2 hH
  have he : denominator t * a = m * numeratorF t - H * numeratorG t := by
    dsimp [a, innerF, innerG]
    have hd := (denominator_pos ht0).ne'
    field_simp
  have hav := rectHead_average t u w m H a hs
  have hbound : (rectHead id true t u w m H a + rectHead id false t u w m H a) / 2 ≤ 70 * a := by
    linarith
  have hclip (h : Bool) := rectHead_clipped_le (t := t) (u := u) (w := w)
    h ht0 (by linarith [hu.1]) (by linarith [hw.1]) m H a
  by_cases hh : rectHead id true t u w m H a ≤ 70 * a
  · exact ⟨true, (hclip true).trans hh⟩
  · refine ⟨false, (hclip false).trans ?_⟩
    linarith

end OM.NNN11
