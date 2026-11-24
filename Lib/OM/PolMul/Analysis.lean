/- Adapted from PolMul/Analysis.lean of an earlier formalisation
   (commit 51c6e6b6e8b8d7226c6a828dba618ae1de5b5f8a).
   Amanov, van den Berg and Zuiddam (2026),
   “Multiplying matrices via polynomials: exposition and barriers”.
   Uses Foundations tensor definitions; declarations are renamed under OM. -/
import Mathlib
import Lib.OM.PolMul.Profiles
import Lib.OM.PolMul.SpectralFacts
import Lib.OM.PolMulStatements.AN_1
import Lib.OM.PolMulStatements.AN_2
import Lib.OM.PolMulStatements.AN_3

namespace OM.PolMul.Analysis

open AsymptoticSpectrumDuality Semicontinuity
open scoped BigOperators
open OM.PolMulDef

/-! The elementary lemmas below isolate the discrete-concavity argument used in
the paired-step and paired-growth lemmas. -/

private lemma diff_antitone
    (f : ℕ → ℝ)
    (hconc : ∀ m : ℕ, 2 ≤ m → f (m + 1) + f (m - 1) ≤ 2 * f m)
    {i j : ℕ} (hi : 1 ≤ i) (hij : i ≤ j) :
    f (j + 1) - f j ≤ f (i + 1) - f i := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hij
  induction d with
  | zero => simp
  | succ d ih =>
      have hc := hconc (i + d + 1) (by omega)
      have hstep :
          f (i + (d + 1) + 1) - f (i + (d + 1)) ≤
            f (i + d + 1) - f (i + d) := by
        convert! (show f ((i + d + 1) + 1) - f (i + d + 1) ≤
            f (i + d + 1) - f ((i + d + 1) - 1) by linarith) using 1
      exact hstep.trans (ih (Nat.le_add_right i d))

private lemma secant_le_mul_diff
    (f : ℕ → ℝ)
    (hconc : ∀ m : ℕ, 2 ≤ m → f (m + 1) + f (m - 1) ≤ 2 * f m)
    {k m t : ℕ} (hk : 1 ≤ k) (hkm : k ≤ m) :
    f (m + t) - f m ≤ (t : ℝ) * (f (k + 1) - f k) := by
  induction t with
  | zero => simp
  | succ t ih =>
      have hd := diff_antitone f hconc hk (hkm.trans (Nat.le_add_right m t))
      calc
        f (m + (t + 1)) - f m =
            (f (m + t) - f m) + (f (m + t + 1) - f (m + t)) := by
              rw [show m + (t + 1) = m + t + 1 by omega]
              ring
        _ ≤ (t : ℝ) * (f (k + 1) - f k) + (f (k + 1) - f k) :=
          add_le_add ih hd
        _ = ((t + 1 : ℕ) : ℝ) * (f (k + 1) - f k) := by
          push_cast
          ring

private lemma tripling_diff_lower
    (a : ℕ) (ha : 1 ≤ a) (f q : ℕ → ℝ)
    (hconc : ∀ m : ℕ, 2 ≤ m → f (m + 1) + f (m - 1) ≤ 2 * f m)
    (htrip : ∀ m : ℕ, 1 ≤ m → 2 * f m + q m ≤ f (3 * m + a - 1))
    {k m : ℕ} (hk : 1 ≤ k) (hkm : k ≤ m) :
    (f m + q m) / (((2 * m + a - 1 : ℕ) : ℝ)) ≤ f (k + 1) - f k := by
  have hm : 1 ≤ m := hk.trans hkm
  let L : ℕ := 2 * m + a - 1
  have hLpos : 0 < L := by dsimp [L]; omega
  have hindex : m + L = 3 * m + a - 1 := by dsimp [L]; omega
  have hsec := secant_le_mul_diff f hconc hk hkm (t := L)
  rw [hindex] at hsec
  have ht := htrip m hm
  have hnum : f m + q m ≤ f (3 * m + a - 1) - f m := by linarith
  rw [div_le_iff₀ (by exact_mod_cast hLpos)]
  dsimp [L] at hsec ⊢
  simpa [mul_comm] using! hnum.trans hsec

private lemma mul_le_growth
    (f : ℕ → ℝ) (c : ℝ) {m : ℕ}
    (hlow : ∀ k : ℕ, 1 ≤ k → k < m → c ≤ f (k + 1) - f k)
    {u t : ℕ} (hu : 1 ≤ u) (hut : u + t ≤ m) :
    (t : ℝ) * c ≤ f (u + t) - f u := by
  induction t with
  | zero => simp
  | succ t ih =>
      have hut' : u + t ≤ m := by omega
      have hlt : u + t < m := by omega
      have hs := hlow (u + t) (by omega) hlt
      calc
        (((t + 1 : ℕ) : ℝ) * c) = (t : ℝ) * c + c := by
          push_cast
          ring
        _ ≤ (f (u + t) - f u) + (f (u + t + 1) - f (u + t)) :=
          add_le_add (ih hut') hs
        _ = f (u + (t + 1)) - f u := by
          rw [show u + (t + 1) = u + t + 1 by omega]
          ring

private noncomputable def growthRhs (a u v r s : ℕ) : ℝ :=
  let D : ℝ := ((u + v + r + s + a - 1 : ℕ) : ℝ)
  let R : ℝ := ((r + s : ℕ) : ℝ)
  (D / (D - 4 * (r : ℝ) * (s : ℝ) / R)) ^ R

private theorem paired_growth
    (a : ℕ) (ha : 1 ≤ a) (g h : ℕ → ℝ)
    (hgpos : ∀ m : ℕ, 1 ≤ m → 0 < g m)
    (hhpos : ∀ m : ℕ, 1 ≤ m → 0 < h m)
    (hgconc : ∀ m : ℕ, 2 ≤ m → g (m + 1) + g (m - 1) ≤ 2 * g m)
    (hhconc : ∀ m : ℕ, 2 ≤ m → h (m + 1) + h (m - 1) ≤ 2 * h m)
    (hgtrip : ∀ m : ℕ, 1 ≤ m → 2 * g m + h m ≤ g (3 * m + a - 1))
    (hhtrip : ∀ m : ℕ, 1 ≤ m → 2 * h m + g m ≤ h (3 * m + a - 1))
    (u v r s : ℕ) (hu : 1 ≤ u) (hv : 1 ≤ v) (hr : 1 ≤ r) (hs : 1 ≤ s) :
    (g (u + r) / g u) ^ ((s : ℕ) : ℝ) *
          (h (v + s) / h v) ^ ((r : ℕ) : ℝ) ≥
        growthRhs a u v r s := by
  let m : ℕ := max (u + r) (v + s)
  let L : ℕ := 2 * m + a - 1
  let D : ℕ := u + v + r + s + a - 1
  let R : ℕ := r + s
  let lam : ℝ := (g m + h m) / (L : ℝ)
  let A : ℝ := g (u + r)
  let B : ℝ := h (v + s)
  have hur : 1 ≤ u + r := by omega
  have hvs : 1 ≤ v + s := by omega
  have hurm : u + r ≤ m := by exact le_max_left _ _
  have hvsm : v + s ≤ m := by exact le_max_right _ _
  have hm : 1 ≤ m := hur.trans hurm
  have hLpos : 0 < L := by dsimp [L]; omega
  have hDpos : (0 : ℝ) < (D : ℝ) := by
    exact_mod_cast (show 0 < D by dsimp [D]; omega)
  have hRpos : (0 : ℝ) < (R : ℝ) := by
    exact_mod_cast (show 0 < R by dsimp [R]; omega)
  have hlampos : 0 < lam := by
    dsimp [lam]
    exact div_pos (add_pos (hgpos m hm) (hhpos m hm)) (by exact_mod_cast hLpos)
  have hlowg : ∀ k : ℕ, 1 ≤ k → k < m → lam ≤ g (k + 1) - g k := by
    intro k hk hkm
    dsimp [lam, L]
    exact tripling_diff_lower a ha g h hgconc hgtrip hk hkm.le
  have hlowh : ∀ k : ℕ, 1 ≤ k → k < m → lam ≤ h (k + 1) - h k := by
    intro k hk hkm
    dsimp [lam, L]
    simpa [add_comm] using! tripling_diff_lower a ha h g hhconc hhtrip hk hkm.le
  have hAg : (r : ℝ) * lam ≤ A - g u := by
    simpa [A] using! mul_le_growth g lam hlowg hu hurm
  have hBh : (s : ℝ) * lam ≤ B - h v := by
    simpa [B] using! mul_le_growth h lam hlowh hv hvsm
  let rgap : ℕ := m - (u + r)
  let sgap : ℕ := m - (v + s)
  have hrgap : u + r + rgap = m := by dsimp [rgap]; omega
  have hsgap : v + s + sgap = m := by dsimp [sgap]; omega
  have hgmA : (rgap : ℝ) * lam ≤ g m - A := by
    have ht := mul_le_growth g lam hlowg hur (m := m) (t := rgap) (by omega)
    rw [hrgap] at ht
    simpa [A] using! ht
  have hhmB : (sgap : ℝ) * lam ≤ h m - B := by
    have ht := mul_le_growth h lam hlowh hvs (m := m) (t := sgap) (by omega)
    rw [hsgap] at ht
    simpa [B] using! ht
  have hnat : L = rgap + sgap + D := by
    dsimp [L, rgap, sgap, D, m]
    omega
  have hcast : (L : ℝ) = (rgap : ℝ) + (sgap : ℝ) + (D : ℝ) := by
    exact_mod_cast hnat
  have hlamL : lam * (L : ℝ) = g m + h m := by
    dsimp [lam]
    field_simp
  have hAB : A + B ≤ lam * (D : ℝ) := by
    have hexpand : lam * (L : ℝ) =
        (rgap : ℝ) * lam + (sgap : ℝ) * lam + lam * (D : ℝ) := by
      rw [hcast]
      ring
    linarith
  have hApos : 0 < A := by exact hgpos (u + r) hur
  have hBpos : 0 < B := by exact hhpos (v + s) hvs
  have hABpos : 0 < A + B := add_pos hApos hBpos
  have hRltD : (R : ℝ) < (D : ℝ) := by
    exact_mod_cast (show R < D by dsimp [R, D]; omega)
  have hrs_sq : 4 * (r : ℝ) * (s : ℝ) ≤ (R : ℝ) ^ 2 := by
    have hsquare := sq_nonneg ((r : ℝ) - (s : ℝ))
    dsimp [R]
    push_cast
    nlinarith
  have hcorr_le_R :
      4 * (r : ℝ) * (s : ℝ) / (R : ℝ) ≤ (R : ℝ) := by
    rw [div_le_iff₀ hRpos]
    nlinarith
  have hdenpos :
      0 < (D : ℝ) - 4 * (r : ℝ) * (s : ℝ) / (R : ℝ) := by
    linarith
  have hrecip : 4 / (A + B) ≤ 1 / A + 1 / B := by
    calc
      4 / (A + B) ≤ (A + B) / (A * B) := by
        rw [div_le_div_iff₀ hABpos (mul_pos hApos hBpos)]
        nlinarith [sq_nonneg (A - B)]
      _ = 1 / A + 1 / B := by field_simp; ring
  have hbase : 1 / (D : ℝ) ≤ lam / (A + B) := by
    rw [div_le_div_iff₀ hDpos hABpos]
    simpa [mul_comm] using! hAB
  have hlamrecip : 4 / (D : ℝ) ≤ lam * (1 / A + 1 / B) := by
    calc
      4 / (D : ℝ) = 4 * (1 / (D : ℝ)) := by ring
      _ ≤ 4 * (lam / (A + B)) := mul_le_mul_of_nonneg_left hbase (by norm_num)
      _ = lam * (4 / (A + B)) := by ring
      _ ≤ lam * (1 / A + 1 / B) := mul_le_mul_of_nonneg_left hrecip hlampos.le
  let x : ℝ := g u / A
  let y : ℝ := h v / B
  have hxpos : 0 < x := div_pos (hgpos u hu) hApos
  have hypos : 0 < y := div_pos (hhpos v hv) hBpos
  have hx : x ≤ 1 - (r : ℝ) * lam / A := by
    dsimp [x]
    rw [div_le_iff₀ hApos]
    calc
      g u ≤ A - (r : ℝ) * lam := by linarith
      _ = (1 - (r : ℝ) * lam / A) * A := by field_simp
  have hy : y ≤ 1 - (s : ℝ) * lam / B := by
    dsimp [y]
    rw [div_le_iff₀ hBpos]
    calc
      h v ≤ B - (s : ℝ) * lam := by linarith
      _ = (1 - (s : ℝ) * lam / B) * B := by field_simp
  have havg :
      ((s : ℝ) * x + (r : ℝ) * y) / (R : ℝ) ≤
        1 - 4 * (r : ℝ) * (s : ℝ) / ((R : ℝ) * (D : ℝ)) := by
    rw [div_le_iff₀ hRpos]
    have hrs0 : 0 ≤ (r : ℝ) * (s : ℝ) := by positivity
    have hscaled := mul_le_mul_of_nonneg_left hlamrecip hrs0
    have hr0 : 0 ≤ (r : ℝ) := by positivity
    have hs0 : 0 ≤ (s : ℝ) := by positivity
    have hx' := mul_le_mul_of_nonneg_left hx hs0
    have hy' := mul_le_mul_of_nonneg_left hy hr0
    have hxy :
        (s : ℝ) * x + (r : ℝ) * y ≤
          (s : ℝ) + (r : ℝ) -
            (r : ℝ) * (s : ℝ) * lam * (1 / A + 1 / B) := by
      calc
        (s : ℝ) * x + (r : ℝ) * y ≤
            (s : ℝ) * (1 - (r : ℝ) * lam / A) +
              (r : ℝ) * (1 - (s : ℝ) * lam / B) := add_le_add hx' hy'
        _ = (s : ℝ) + (r : ℝ) -
            (r : ℝ) * (s : ℝ) * lam * (1 / A + 1 / B) := by ring
    have hscaled' :
        4 * (r : ℝ) * (s : ℝ) / (D : ℝ) ≤
          (r : ℝ) * (s : ℝ) * lam * (1 / A + 1 / B) := by
      calc
        4 * (r : ℝ) * (s : ℝ) / (D : ℝ) =
            (r : ℝ) * (s : ℝ) * (4 / (D : ℝ)) := by ring
        _ ≤ (r : ℝ) * (s : ℝ) * (lam * (1 / A + 1 / B)) := hscaled
        _ = (r : ℝ) * (s : ℝ) * lam * (1 / A + 1 / B) := by ring
    have hnum :
        (s : ℝ) * x + (r : ℝ) * y ≤
          (R : ℝ) - 4 * (r : ℝ) * (s : ℝ) / (D : ℝ) := by
      calc
        (s : ℝ) * x + (r : ℝ) * y ≤
            (s : ℝ) + (r : ℝ) -
              (r : ℝ) * (s : ℝ) * lam * (1 / A + 1 / B) := hxy
        _ ≤ (s : ℝ) + (r : ℝ) -
            4 * (r : ℝ) * (s : ℝ) / (D : ℝ) :=
              sub_le_sub_left hscaled' _
        _ = (R : ℝ) - 4 * (r : ℝ) * (s : ℝ) / (D : ℝ) := by
          dsimp [R]
          push_cast
          ring
    calc
      (s : ℝ) * x + (r : ℝ) * y ≤
          (R : ℝ) - 4 * (r : ℝ) * (s : ℝ) / (D : ℝ) := hnum
      _ = (1 - 4 * (r : ℝ) * (s : ℝ) / ((R : ℝ) * (D : ℝ))) *
          (R : ℝ) := by field_simp
  let C : ℝ := 1 - 4 * (r : ℝ) * (s : ℝ) / ((R : ℝ) * (D : ℝ))
  have hCpos : 0 < C := by
    dsimp [C]
    rw [show 4 * (r : ℝ) * (s : ℝ) / ((R : ℝ) * (D : ℝ)) =
        (4 * (r : ℝ) * (s : ℝ) / (R : ℝ)) / (D : ℝ) by ring]
    rw [sub_pos, div_lt_one hDpos]
    exact sub_pos.mp hdenpos
  have hweights : (s : ℝ) / (R : ℝ) + (r : ℝ) / (R : ℝ) = 1 := by
    field_simp
    dsimp [R]
    push_cast
    ring
  have hamgm := Real.geom_mean_le_arith_mean2_weighted
    (w₁ := (s : ℝ) / (R : ℝ)) (w₂ := (r : ℝ) / (R : ℝ))
    (p₁ := x) (p₂ := y)
    (div_nonneg (by positivity) hRpos.le) (div_nonneg (by positivity) hRpos.le)
    hxpos.le hypos.le hweights
  have hroot :
      x ^ ((s : ℝ) / (R : ℝ)) * y ^ ((r : ℝ) / (R : ℝ)) ≤ C := by
    calc
      x ^ ((s : ℝ) / (R : ℝ)) * y ^ ((r : ℝ) / (R : ℝ)) ≤
          (s : ℝ) / (R : ℝ) * x + (r : ℝ) / (R : ℝ) * y := hamgm
      _ = ((s : ℝ) * x + (r : ℝ) * y) / (R : ℝ) := by ring
      _ ≤ C := by simpa [C] using! havg
  have hxpow : (x ^ ((s : ℝ) / (R : ℝ))) ^ R = x ^ s := by
    calc
      (x ^ ((s : ℝ) / (R : ℝ))) ^ R =
          (x ^ ((s : ℝ) / (R : ℝ))) ^ (R : ℝ) :=
            (Real.rpow_natCast _ R).symm
      _ = x ^ (((s : ℝ) / (R : ℝ)) * (R : ℝ)) :=
        (Real.rpow_mul hxpos.le _ _).symm
      _ = x ^ (s : ℝ) := by field_simp
      _ = x ^ s := Real.rpow_natCast x s
  have hypow : (y ^ ((r : ℝ) / (R : ℝ))) ^ R = y ^ r := by
    calc
      (y ^ ((r : ℝ) / (R : ℝ))) ^ R =
          (y ^ ((r : ℝ) / (R : ℝ))) ^ (R : ℝ) :=
            (Real.rpow_natCast _ R).symm
      _ = y ^ (((r : ℝ) / (R : ℝ)) * (R : ℝ)) :=
        (Real.rpow_mul hypos.le _ _).symm
      _ = y ^ (r : ℝ) := by field_simp
      _ = y ^ r := Real.rpow_natCast y r
  have hpow : x ^ s * y ^ r ≤ C ^ R := by
    have ht := pow_le_pow_left₀
      (mul_nonneg (Real.rpow_nonneg hxpos.le _) (Real.rpow_nonneg hypos.le _)) hroot R
    rw [mul_pow, hxpow, hypow] at ht
    exact ht
  have hinv : 1 / (C ^ R) ≤ 1 / (x ^ s * y ^ r) := by
    rw [div_le_div_iff₀ (pow_pos hCpos R)
      (mul_pos (pow_pos hxpos s) (pow_pos hypos r))]
    simpa using! hpow
  have hleft :
      (g (u + r) / g u) ^ s * (h (v + s) / h v) ^ r =
        1 / (x ^ s * y ^ r) := by
    have hxinv : g (u + r) / g u = 1 / x := by
      dsimp [x, A]
      field_simp
    have hyinv : h (v + s) / h v = 1 / y := by
      dsimp [y, B]
      field_simp
    rw [hxinv, hyinv, one_div_pow, one_div_pow]
    field_simp
  have hright : growthRhs a u v r s = 1 / (C ^ R) := by
    have hbaseeq :
        (D : ℝ) / ((D : ℝ) - 4 * (r : ℝ) * (s : ℝ) / (R : ℝ)) =
          1 / C := by
      dsimp [C]
      field_simp
    change ((D : ℝ) / ((D : ℝ) -
      4 * (r : ℝ) * (s : ℝ) / (R : ℝ))) ^ (R : ℝ) = 1 / (C ^ R)
    rw [Real.rpow_natCast, hbaseeq, one_div_pow]
  rw [Real.rpow_natCast, Real.rpow_natCast, hleft, hright]
  exact hinv

/-- The lemma on the paired step.  We use the paper's general
paired-growth argument specialized to equal starting indices and unit steps;
this is shorter in Lean and reduces definitionally to the displayed square. -/
theorem proof_AN_1 : OM_S_AN_1 := by
  intro a ha g h hgpos hhpos hgconc hhconc hgtrip hhtrip b hb
  have H := paired_growth a ha g h hgpos hhpos hgconc hhconc hgtrip hhtrip
    b b 1 1 hb hb (by omega) (by omega)
  norm_num [growthRhs] at H
  have hnumCast : (((2 * b + a + 1 : ℕ) : ℝ)) =
      2 * (b : ℝ) + (a : ℝ) + 1 := by
    push_cast
    ring
  have hdenCast : (((2 * b + a - 1 : ℕ) : ℝ)) =
      2 * (b : ℝ) + (a : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  rw [hnumCast, hdenCast]
  have hbase :
      (2 * (b : ℝ) + (a : ℝ) + 1) / (2 * (b : ℝ) + (a : ℝ) - 1) =
        ((b : ℝ) + (b : ℝ) + 1 + (a : ℝ)) /
          ((b : ℝ) + (b : ℝ) + 1 + (a : ℝ) - 2) := by
    congr 1 <;> ring
  rw [hbase]
  rw [Real.rpow_two]
  change (((b : ℝ) + (b : ℝ) + 1 + (a : ℝ)) /
      ((b : ℝ) + (b : ℝ) + 1 + (a : ℝ) - 2)) ^ (2 : ℕ) ≤
        g (b + 1) / g b * (h (b + 1) / h b)
  exact H

/-- The lemma on paired growth.  This follows the paper's
common-slope and weighted AM--GM proof, with the finite-difference summations
written as inductions. -/
theorem proof_AN_2 : OM_S_AN_2 := by
  intro a ha g h hgpos hhpos hgconc hhconc hgtrip hhtrip u v r s hu hv hr hs
  simpa [growthRhs] using!
    paired_growth a ha g h hgpos hhpos hgconc hhconc hgtrip hhtrip
      u v r s hu hv hr hs

universe u

/-- The six-permutation growth bound (Amanov–van den Berg–Zuiddam, Proposition 4.12),
conditional on the profile growth estimate supplied by `PR.1`–`PR.3` and `AN.1`.
The proof uses `SP.5` to identify the sum of the three profile exponents with
`log₂ φ(⟨2,2,2⟩)`. -/
theorem proof_AN_3_of_profile_growth
    (profile_growth : ∀ (F : Type u) [Field F] (phi : OM.PolMulDef.Spectral F) (n : ℕ+),
      (((n : ℕ) : ℝ) ^
          (8 * (Real.logb 2 (OM.PolMulDef.Spectral.eval phi (OM.PolMulDef.matMul 1 1 2)) +
              Real.logb 2 (OM.PolMulDef.Spectral.eval phi (OM.PolMulDef.matMul 2 1 1)) +
              Real.logb 2 (OM.PolMulDef.Spectral.eval phi (OM.PolMulDef.matMul 1 2 1))) / 3)) ≤
        ∏ pi : Equiv.Perm (Fin 3),
          OM.PolMulDef.Spectral.eval phi (OM.PolMulDef.perm pi (OM.PolMulDef.polmul n n))) :
    OM_S_AN_3.{u} := by
  intro F _instF phi n
  obtain ⟨h112, h211, h121, hformula⟩ := OM.PolMul.SpectralFacts.proof_SP_5 F phi
  have h112pos : 0 < OM.PolMulDef.Spectral.eval phi (OM.PolMulDef.matMul (F := F) 1 1 2) :=
    zero_lt_one.trans_le h112.1
  have h211pos : 0 < OM.PolMulDef.Spectral.eval phi (OM.PolMulDef.matMul (F := F) 2 1 1) :=
    zero_lt_one.trans_le h211.1
  have h121pos : 0 < OM.PolMulDef.Spectral.eval phi (OM.PolMulDef.matMul (F := F) 1 2 1) :=
    zero_lt_one.trans_le h121.1
  have heval := hformula (2 : ℕ+) (2 : ℕ+) (2 : ℕ+)
  norm_num [Real.logb_self_eq_one] at heval
  have htau :
      Real.logb 2 (OM.PolMulDef.Spectral.eval phi (OM.PolMulDef.matMul (F := F) 2 2 2)) =
        Real.logb 2 (OM.PolMulDef.Spectral.eval phi (OM.PolMulDef.matMul 1 1 2)) +
          Real.logb 2 (OM.PolMulDef.Spectral.eval phi (OM.PolMulDef.matMul 2 1 1)) +
          Real.logb 2 (OM.PolMulDef.Spectral.eval phi (OM.PolMulDef.matMul 1 2 1)) := by
    rw [heval, Real.logb_mul (mul_ne_zero h211pos.ne' h121pos.ne') h112pos.ne',
      Real.logb_mul h211pos.ne' h121pos.ne']
    ring
  rw [htau]
  exact profile_growth F phi n

/-! The remaining lemmas prove the six-permutation growth bound of
Amanov–van den Berg–Zuiddam, Proposition 4.12. The three coset representatives
contribute one basic spectral exponent each. -/

private def swap12Perm : Equiv.Perm (Fin 3) := Equiv.swap 0 1

private def swap23Perm : Equiv.Perm (Fin 3) := Equiv.swap 1 2

private def cyclicRep : Fin 3 → Equiv.Perm (Fin 3)
  | 0 => 1
  | 1 => finRotate 3
  | 2 => (finRotate 3)⁻¹

private def pairedPerm : Fin 3 × Fin 2 → Equiv.Perm (Fin 3)
  | (i, 0) => cyclicRep i
  | (i, 1) => cyclicRep i * swap23Perm

private lemma pairedPerm_bijective : Function.Bijective pairedPerm := by
  decide +kernel

private noncomputable def pairedPermEquiv :
    (Fin 3 × Fin 2) ≃ Equiv.Perm (Fin 3) :=
  Equiv.ofBijective pairedPerm pairedPerm_bijective

-- The coordinate casts in the third leg account only for `a + b = b + a`.
set_option maxHeartbeats 200000 in
private lemma polmul_swap12_restrictsEquiv {F : Type u} [Field F] (a b : ℕ+) :
    perm swap12Perm (polmul (F := F) a b) ∼ₜ polmul b a := by
  let hfmt : ∀ i : Fin 3,
      (((fmt a b (a + b - 1) ∘ swap12Perm.symm) i : ℕ)) =
        (fmt b a (b + a - 1) i : ℕ) := by
    intro i
    fin_cases i <;> simp [fmt, swap12Perm, Equiv.swap_apply_def, add_comm]
  let e : ∀ i : Fin 3,
      Fin ((fmt a b (a + b - 1) ∘ swap12Perm.symm) i) ≃
        Fin (fmt b a (b + a - 1) i) := fun i => finCongr (hfmt i)
  apply OM.PolMul.SpectralFacts.restrictsEquiv_of_index_equiv e
  intro idx
  simp only [perm, KTensor.legReindex_apply, polmul]
  congr 1
  apply propext
  simp only [e, Fin.val_cast]
  change (idx 2).val = (idx 1).val + (idx 0).val ↔
    (idx 2).val = (idx 0).val + (idx 1).val
  omega

-- This is the symmetry `φ_π(a,b) = φ_{π(12)}(b,a)`, multiplied over all π.
set_option maxHeartbeats 200000 in
private lemma profile_product_swap {F : Type u} [Field F]
    (φ : Spectral F) (a b : ℕ+) :
    (∏ π : Equiv.Perm (Fin 3),
        Spectral.eval (Spectral.perm π φ) (polmul a b)) =
      ∏ π : Equiv.Perm (Fin 3),
        Spectral.eval (Spectral.perm π φ) (polmul b a) := by
  let s := swap12Perm
  calc
    (∏ π : Equiv.Perm (Fin 3),
        Spectral.eval (Spectral.perm π φ) (polmul a b)) =
        ∏ π : Equiv.Perm (Fin 3),
          Spectral.eval (Spectral.perm π φ) (perm s (polmul b a)) := by
            apply Finset.prod_congr rfl
            intro π _
            exact OM.PolMul.Superadditivity.eval_restrictsEquiv
              (Spectral.perm π φ) (polmul_swap12_restrictsEquiv b a) |>.symm
    _ = ∏ π : Equiv.Perm (Fin 3),
        Spectral.eval (Spectral.perm s (Spectral.perm π φ)) (polmul b a) := by
          apply Finset.prod_congr rfl
          intro π _
          exact (OM.PolMul.Superadditivity.eval_perm (Spectral.perm π φ) s
            (polmul b a)).symm
    _ = ∏ π : Equiv.Perm (Fin 3),
        Spectral.eval (Spectral.perm (π * s) φ) (polmul b a) := by
          apply Finset.prod_congr rfl
          intro π _
          exact OM.PolMul.Superadditivity.eval_perm_perm φ π s (polmul b a)
    _ = ∏ π : Equiv.Perm (Fin 3),
        Spectral.eval (Spectral.perm π φ) (polmul b a) := by
          exact Equiv.prod_comp (Equiv.mulRight s)
            (fun π => Spectral.eval (Spectral.perm π φ) (polmul b a))

private lemma profile_eval_pos {F : Type u} [Field F]
    (φ : Spectral F) (a b : ℕ+) :
    0 < Spectral.eval φ (polmul a b) := by
  have h := (OM.PolMul.Profiles.proof_PR_1 F φ a b).1
  have hmin : (0 : ℝ) < (((min a b : ℕ+) : ℕ) : ℝ) := by positivity
  exact hmin.trans_le h

-- PR.1--PR.3 supply all six hypotheses of AN.1 for a swapped pair of spectra.
set_option maxHeartbeats 500000 in
private lemma paired_profile_step {F : Type u} [Field F]
    (φ : Spectral F) (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    let p := Real.logb 2 (Spectral.eval φ (matMul (F := F) 1 1 2))
    ((((2 * b + a + 1 : ℕ) : ℝ) / ((2 * b + a - 1 : ℕ) : ℝ)) ^ (2 * p)) ≤
      (Spectral.eval φ (polmul (Nat.toPNat' a) (Nat.toPNat' (b + 1))) /
        Spectral.eval φ (polmul (Nat.toPNat' a) (Nat.toPNat' b))) *
      (Spectral.eval (Spectral.perm swap23Perm φ)
          (polmul (Nat.toPNat' a) (Nat.toPNat' (b + 1))) /
        Spectral.eval (Spectral.perm swap23Perm φ)
          (polmul (Nat.toPNat' a) (Nat.toPNat' b))) := by
  let s := swap23Perm
  let ψ := Spectral.perm s φ
  let p := Real.logb 2 (Spectral.eval φ (matMul (F := F) 1 1 2))
  let q : ℕ → ℕ+ := Nat.toPNat'
  let g : ℕ → ℝ := fun m =>
    Spectral.eval φ (polmul (q a) (q m)) ^ ((1 : ℝ) / p)
  let h : ℕ → ℝ := fun m =>
    Spectral.eval ψ (polmul (q a) (q m)) ^ ((1 : ℝ) / p)
  have hq (m : ℕ) (hm : 1 ≤ m) : ((q m : ℕ+) : ℕ) = m := by
    exact PNat.toPNat'_coe (Nat.zero_lt_one.trans_le hm)
  have hq_succ (m : ℕ) (hm : 1 ≤ m) : q (m + 1) = q m + 1 := by
    apply PNat.eq
    rw [PNat.add_coe, hq m hm, hq (m + 1) (by omega)]
    norm_num
  have hq_pred (m : ℕ) (hm : 2 ≤ m) : q (m - 1) = q m - 1 := by
    have hlt : (1 : ℕ+) < q m := by
      apply (PNat.coe_lt_coe _ _).mp
      rw [hq m (by omega)]
      norm_num
      omega
    apply PNat.eq
    rw [PNat.sub_coe, if_pos hlt, hq m (by omega), hq (m - 1) (by omega)]
    norm_num
  have hq_trip (m : ℕ) (hm : 1 ≤ m) :
      q (3 * m + a - 1) = 3 * q m + q a - 1 := by
    have hlt : (1 : ℕ+) < 3 * q m + q a := by
      apply (PNat.coe_lt_coe _ _).mp
      simp only [PNat.add_coe, PNat.mul_coe, PNat.val_ofNat]
      have hqm := (q m).pos
      have hqa := (q a).pos
      omega
    apply PNat.eq
    rw [PNat.sub_coe, if_pos hlt, PNat.add_coe, PNat.mul_coe,
      hq m hm, hq a ha, hq (3 * m + a - 1) (by omega)]
    norm_num
  have hpψ : Real.logb 2 (Spectral.eval ψ (matMul (F := F) 1 1 2)) = p := by
    simpa [ψ, s, p, swap23Perm] using!
      congrArg (Real.logb 2)
        (OM.PolMul.Superadditivity.eval_swap_matMul_11 φ (2 : ℕ+))
  have hp0 : 0 ≤ p := by
    exact OM.PolMul.Superadditivity.spectral_exponent_nonneg φ
  change ((((2 * b + a + 1 : ℕ) : ℝ) / ((2 * b + a - 1 : ℕ) : ℝ)) ^
      (2 * p)) ≤
    (Spectral.eval φ (polmul (q a) (q (b + 1))) /
      Spectral.eval φ (polmul (q a) (q b))) *
    (Spectral.eval ψ (polmul (q a) (q (b + 1))) /
      Spectral.eval ψ (polmul (q a) (q b)))
  by_cases hp : 0 < p
  · have hgpos : ∀ m : ℕ, 1 ≤ m → 0 < g m := by
      intro m hm
      exact Real.rpow_pos_of_pos (profile_eval_pos φ (q a) (q m)) _
    have hhpos : ∀ m : ℕ, 1 ≤ m → 0 < h m := by
      intro m hm
      exact Real.rpow_pos_of_pos (profile_eval_pos ψ (q a) (q m)) _
    have hgconc : ∀ m : ℕ, 2 ≤ m → g (m + 1) + g (m - 1) ≤ 2 * g m := by
      intro m hm
      have hmP : (2 : ℕ+) ≤ q m := by
        apply (PNat.coe_le_coe _ _).mp
        rw [hq m (by omega)]
        norm_num
        exact hm
      have H := OM.PolMul.Profiles.proof_PR_2 F φ (by simpa [p] using! hp)
        (q a) (q m) hmP
      change Spectral.eval φ (polmul (q a) (q (m + 1))) ^ ((1 : ℝ) / p) +
          Spectral.eval φ (polmul (q a) (q (m - 1))) ^ ((1 : ℝ) / p) ≤
        2 * Spectral.eval φ (polmul (q a) (q m)) ^ ((1 : ℝ) / p)
      rw [hq_succ m (by omega), hq_pred m hm]
      exact H
    have hhconc : ∀ m : ℕ, 2 ≤ m → h (m + 1) + h (m - 1) ≤ 2 * h m := by
      intro m hm
      have hpψpos : 0 < Real.logb 2 (Spectral.eval ψ (matMul (F := F) 1 1 2)) := by
        change 0 < Real.logb 2 (Spectral.eval ψ (matMul (F := F) 1 1 2))
        rw [hpψ]
        exact hp
      have hmP : (2 : ℕ+) ≤ q m := by
        apply (PNat.coe_le_coe _ _).mp
        rw [hq m (by omega)]
        norm_num
        exact hm
      have H := OM.PolMul.Profiles.proof_PR_2 F ψ hpψpos (q a) (q m) hmP
      change Spectral.eval ψ (polmul (q a) (q m + 1)) ^
            ((1 : ℝ) / Real.logb 2 (Spectral.eval ψ (matMul 1 1 2))) +
          Spectral.eval ψ (polmul (q a) (q m - 1)) ^
            ((1 : ℝ) / Real.logb 2 (Spectral.eval ψ (matMul 1 1 2))) ≤
        2 * Spectral.eval ψ (polmul (q a) (q m)) ^
            ((1 : ℝ) / Real.logb 2 (Spectral.eval ψ (matMul 1 1 2))) at H
      rw [hpψ] at H
      change Spectral.eval ψ (polmul (q a) (q (m + 1))) ^ ((1 : ℝ) / p) +
          Spectral.eval ψ (polmul (q a) (q (m - 1))) ^ ((1 : ℝ) / p) ≤
        2 * Spectral.eval ψ (polmul (q a) (q m)) ^ ((1 : ℝ) / p)
      rw [hq_succ m (by omega), hq_pred m hm]
      exact H
    have hgtrip : ∀ m : ℕ, 1 ≤ m →
        2 * g m + h m ≤ g (3 * m + a - 1) := by
      intro m hm
      have H := OM.PolMul.Profiles.proof_PR_3 F φ (by simpa [p] using! hp) (q a) (q m)
      have hswap : Spectral.eval φ (swap23 (polmul (q a) (q m))) =
          Spectral.eval ψ (polmul (q a) (q m)) := by
        exact (OM.PolMul.Superadditivity.eval_perm φ s (polmul (q a) (q m))).symm
      change 2 * Spectral.eval φ (polmul (q a) (q m)) ^ ((1 : ℝ) / p) +
          Spectral.eval ψ (polmul (q a) (q m)) ^ ((1 : ℝ) / p) ≤
        Spectral.eval φ (polmul (q a) (q (3 * m + a - 1))) ^ ((1 : ℝ) / p)
      rw [hq_trip m hm]
      simpa only [hswap] using! H
    have hhtrip : ∀ m : ℕ, 1 ≤ m →
        2 * h m + g m ≤ h (3 * m + a - 1) := by
      intro m hm
      have hpψpos : 0 < Real.logb 2 (Spectral.eval ψ (matMul (F := F) 1 1 2)) := by
        change 0 < Real.logb 2 (Spectral.eval ψ (matMul (F := F) 1 1 2))
        rw [hpψ]
        exact hp
      have H := OM.PolMul.Profiles.proof_PR_3 F ψ hpψpos (q a) (q m)
      change 2 * Spectral.eval ψ (polmul (q a) (q m)) ^
            ((1 : ℝ) / Real.logb 2 (Spectral.eval ψ (matMul 1 1 2))) +
          Spectral.eval ψ (swap23 (polmul (q a) (q m))) ^
            ((1 : ℝ) / Real.logb 2 (Spectral.eval ψ (matMul 1 1 2))) ≤
        Spectral.eval ψ (polmul (q a) (3 * q m + q a - 1)) ^
            ((1 : ℝ) / Real.logb 2 (Spectral.eval ψ (matMul 1 1 2))) at H
      rw [hpψ] at H
      have hswap : Spectral.eval ψ (swap23 (polmul (q a) (q m))) =
          Spectral.eval φ (polmul (q a) (q m)) := by
        simpa [ψ, s, swap23Perm] using!
          OM.PolMul.Superadditivity.eval_swap_swap φ (polmul (q a) (q m))
      change 2 * Spectral.eval ψ (polmul (q a) (q m)) ^ ((1 : ℝ) / p) +
          Spectral.eval φ (polmul (q a) (q m)) ^ ((1 : ℝ) / p) ≤
        Spectral.eval ψ (polmul (q a) (q (3 * m + a - 1))) ^ ((1 : ℝ) / p)
      rw [hq_trip m hm]
      rw [← hswap]
      exact H
    have H := proof_AN_1 a ha g h hgpos hhpos hgconc hhconc hgtrip hhtrip b hb
    have Hpow := Real.rpow_le_rpow (Real.rpow_nonneg (by positivity) (2 : ℝ)) H hp.le
    dsimp only [g, h, q] at Hpow
    have hroot_div (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
        (x ^ ((1 : ℝ) / p) / y ^ ((1 : ℝ) / p)) ^ p = x / y := by
      rw [Real.div_rpow (Real.rpow_nonneg hx _) (Real.rpow_nonneg hy _)]
      simp only [one_div]
      rw [Real.rpow_inv_rpow hx hp.ne', Real.rpow_inv_rpow hy hp.ne']
    have hright :
        ((Spectral.eval φ (polmul (q a) (q (b + 1))) ^ ((1 : ℝ) / p) /
            Spectral.eval φ (polmul (q a) (q b)) ^ ((1 : ℝ) / p)) *
          (Spectral.eval ψ (polmul (q a) (q (b + 1))) ^ ((1 : ℝ) / p) /
            Spectral.eval ψ (polmul (q a) (q b)) ^ ((1 : ℝ) / p))) ^ p =
          (Spectral.eval φ (polmul (q a) (q (b + 1))) /
            Spectral.eval φ (polmul (q a) (q b))) *
          (Spectral.eval ψ (polmul (q a) (q (b + 1))) /
            Spectral.eval ψ (polmul (q a) (q b))) := by
      rw [Real.mul_rpow (div_nonneg (Real.rpow_nonneg (profile_eval_pos φ _ _).le _)
          (Real.rpow_nonneg (profile_eval_pos φ _ _).le _))
        (div_nonneg (Real.rpow_nonneg (profile_eval_pos ψ _ _).le _)
          (Real.rpow_nonneg (profile_eval_pos ψ _ _).le _)),
        hroot_div _ _ (profile_eval_pos φ _ _).le (profile_eval_pos φ _ _).le,
        hroot_div _ _ (profile_eval_pos ψ _ _).le (profile_eval_pos ψ _ _).le]
    have hbase : 0 ≤
        (((2 * b + a + 1 : ℕ) : ℝ) / ((2 * b + a - 1 : ℕ) : ℝ)) := by
      positivity
    have hleft :
        ((((2 * b + a + 1 : ℕ) : ℝ) / ((2 * b + a - 1 : ℕ) : ℝ)) ^ (2 : ℝ)) ^ p =
          (((2 * b + a + 1 : ℕ) : ℝ) / ((2 * b + a - 1 : ℕ) : ℝ)) ^ (2 * p) := by
      rw [← Real.rpow_mul hbase]
    rw [hleft, hright] at Hpow
    exact Hpow
  · have hpz : p = 0 := le_antisymm (le_of_not_gt hp) hp0
    have hqb : q b ≤ q (b + 1) := by
      apply (PNat.coe_le_coe _ _).mp
      rw [hq b hb, hq (b + 1) (by omega)]
      omega
    have hφ := (OM.PolMul.Profiles.proof_PR_1 F φ (q a) (q b)).2.2.2
      (q (b + 1)) hqb
    have hψ := (OM.PolMul.Profiles.proof_PR_1 F ψ (q a) (q b)).2.2.2
      (q (b + 1)) hqb
    have hφden := profile_eval_pos φ (q a) (q b)
    have hψden := profile_eval_pos ψ (q a) (q b)
    rw [hpz, mul_zero, Real.rpow_zero]
    simpa only [OM.PolMulDef.Spectral.eval, OM.PolMulDef.polmul, one_mul] using!
      (mul_le_mul ((one_le_div hφden).2 hφ) ((one_le_div hψden).2 hψ)
        (by norm_num) (div_pos (profile_eval_pos φ _ _) hφden).le)

-- Multiplying the paired estimate over the three coset representatives gives
-- one factor for every permutation of the tensor legs.
set_option maxHeartbeats 300000 in
private lemma all_profile_step {F : Type u} [Field F]
    (φ : Spectral F) (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    let τ := Real.logb 2 (Spectral.eval φ (matMul (F := F) 1 1 2)) +
      Real.logb 2 (Spectral.eval φ (matMul (F := F) 2 1 1)) +
      Real.logb 2 (Spectral.eval φ (matMul (F := F) 1 2 1))
    ((((2 * b + a + 1 : ℕ) : ℝ) / ((2 * b + a - 1 : ℕ) : ℝ)) ^ (2 * τ)) ≤
      ∏ π : Equiv.Perm (Fin 3),
        Spectral.eval (Spectral.perm π φ)
            (polmul (Nat.toPNat' a) (Nat.toPNat' (b + 1))) /
          Spectral.eval (Spectral.perm π φ)
            (polmul (Nat.toPNat' a) (Nat.toPNat' b)) := by
  let B : ℝ := ((2 * b + a + 1 : ℕ) : ℝ) / ((2 * b + a - 1 : ℕ) : ℝ)
  let R : Equiv.Perm (Fin 3) → ℝ := fun π =>
    Spectral.eval (Spectral.perm π φ)
          (polmul (Nat.toPNat' a) (Nat.toPNat' (b + 1))) /
      Spectral.eval (Spectral.perm π φ)
          (polmul (Nat.toPNat' a) (Nat.toPNat' b))
  let p : Fin 3 → ℝ := fun i =>
    Real.logb 2 (Spectral.eval (Spectral.perm (cyclicRep i) φ)
      (matMul (F := F) 1 1 2))
  have hp :
      p 0 = Real.logb 2 (Spectral.eval φ (matMul (F := F) 1 1 2)) ∧
      p 1 = Real.logb 2 (Spectral.eval φ (matMul (F := F) 2 1 1)) ∧
      p 2 = Real.logb 2 (Spectral.eval φ (matMul (F := F) 1 2 1)) := by
    constructor
    · simp only [p, cyclicRep]
      rw [OM.PolMul.Superadditivity.eval_perm]
      rfl
    constructor
    · simp only [p, cyclicRep]
      rw [OM.PolMul.Superadditivity.eval_perm,
        OM.PolMul.Superadditivity.eval_rotate_matMul]
    · simp only [p, cyclicRep]
      rw [OM.PolMul.Superadditivity.eval_perm,
        OM.PolMul.Superadditivity.eval_rotate_inv_matMul]
  have hpair (i : Fin 3) : B ^ (2 * p i) ≤
      R (cyclicRep i) * R (cyclicRep i * swap23Perm) := by
    have H := paired_profile_step (Spectral.perm (cyclicRep i) φ) a b ha hb
    change B ^ (2 * p i) ≤
      (Spectral.eval (Spectral.perm (cyclicRep i) φ)
          (polmul (Nat.toPNat' a) (Nat.toPNat' (b + 1))) /
        Spectral.eval (Spectral.perm (cyclicRep i) φ)
          (polmul (Nat.toPNat' a) (Nat.toPNat' b))) *
      (Spectral.eval (Spectral.perm swap23Perm
          (Spectral.perm (cyclicRep i) φ))
          (polmul (Nat.toPNat' a) (Nat.toPNat' (b + 1))) /
        Spectral.eval (Spectral.perm swap23Perm
          (Spectral.perm (cyclicRep i) φ))
          (polmul (Nat.toPNat' a) (Nat.toPNat' b))) at H
    change B ^ (2 * p i) ≤ R (cyclicRep i) * R (cyclicRep i * swap23Perm)
    simpa only [R, OM.PolMul.Superadditivity.eval_perm_perm] using! H
  have hB : 0 < B := by
    dsimp [B]
    have hden : 0 < 2 * b + a - 1 := by omega
    exact div_pos (by positivity) (by exact_mod_cast hden)
  have hprod : (∏ i : Fin 3, B ^ (2 * p i)) ≤
      ∏ i : Fin 3, R (cyclicRep i) * R (cyclicRep i * swap23Perm) := by
    apply Finset.prod_le_prod₀
    · intro i _
      exact Real.rpow_nonneg hB.le _
    · intro i _
      exact hpair i
  have hleft : (∏ i : Fin 3, B ^ (2 * p i)) =
      B ^ (2 * (p 0 + p 1 + p 2)) := by
    rw [Fin.prod_univ_three, ← Real.rpow_add hB, ← Real.rpow_add hB]
    congr 1
    ring
  have hright : (∏ i : Fin 3, R (cyclicRep i) * R (cyclicRep i * swap23Perm)) =
      ∏ π : Equiv.Perm (Fin 3), R π := by
    calc
      _ = ∏ x : Fin 3 × Fin 2, R (pairedPerm x) := by
        rw [Fintype.prod_prod_type]
        apply Finset.prod_congr rfl
        intro i _
        rw [Fin.prod_univ_two]
        rfl
      _ = _ := pairedPermEquiv.prod_comp R
  change B ^ (2 *
      (Real.logb 2 (Spectral.eval φ (matMul (F := F) 1 1 2)) +
       Real.logb 2 (Spectral.eval φ (matMul (F := F) 2 1 1)) +
       Real.logb 2 (Spectral.eval φ (matMul (F := F) 1 2 1)))) ≤
    ∏ π : Equiv.Perm (Fin 3), R π
  rw [← hp.1, ← hp.2.1, ← hp.2.2, ← hleft, ← hright]
  exact hprod

private noncomputable def profileProduct {F : Type u} [Field F]
    (φ : Spectral F) (a b : ℕ+) : ℝ :=
  ∏ π : Equiv.Perm (Fin 3), Spectral.eval (Spectral.perm π φ) (polmul a b)

private lemma profileProduct_pos {F : Type u} [Field F]
    (φ : Spectral F) (a b : ℕ+) : 0 < profileProduct φ a b := by
  apply Finset.prod_pos
  intro π _
  exact profile_eval_pos (Spectral.perm π φ) a b

set_option maxHeartbeats 200000 in
private lemma profile_product_step {F : Type u} [Field F]
    (φ : Spectral F) (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    let τ := Real.logb 2 (Spectral.eval φ (matMul (F := F) 1 1 2)) +
      Real.logb 2 (Spectral.eval φ (matMul (F := F) 2 1 1)) +
      Real.logb 2 (Spectral.eval φ (matMul (F := F) 1 2 1))
    ((((2 * b + a + 1 : ℕ) : ℝ) / ((2 * b + a - 1 : ℕ) : ℝ)) ^ (2 * τ)) ≤
      profileProduct φ (Nat.toPNat' a) (Nat.toPNat' (b + 1)) /
        profileProduct φ (Nat.toPNat' a) (Nat.toPNat' b) := by
  have H := all_profile_step φ a b ha hb
  simpa only [profileProduct, Finset.prod_div_distrib] using! H

-- The two rectangular increments making up one square increment.  The
-- elementary rational estimate is the last inequality in the paper.
set_option maxHeartbeats 500000 in
private lemma profile_square_step {F : Type u} [Field F]
    (φ : Spectral F) (n : ℕ) (hn : 1 ≤ n) :
    let τ := Real.logb 2 (Spectral.eval φ (matMul (F := F) 1 1 2)) +
      Real.logb 2 (Spectral.eval φ (matMul (F := F) 2 1 1)) +
      Real.logb 2 (Spectral.eval φ (matMul (F := F) 1 2 1))
    ((((n + 1 : ℕ) : ℝ) / (n : ℝ)) ^ (8 * τ / 3)) ≤
      profileProduct φ (Nat.toPNat' (n + 1)) (Nat.toPNat' (n + 1)) /
        profileProduct φ (Nat.toPNat' n) (Nat.toPNat' n) := by
  let τ := Real.logb 2 (Spectral.eval φ (matMul (F := F) 1 1 2)) +
    Real.logb 2 (Spectral.eval φ (matMul (F := F) 2 1 1)) +
    Real.logb 2 (Spectral.eval φ (matMul (F := F) 1 2 1))
  let q : ℕ → ℕ+ := Nat.toPNat'
  let G : ℕ → ℕ → ℝ := fun a b => profileProduct φ (q a) (q b)
  let A : ℝ := ((3 * n + 1 : ℕ) : ℝ) / ((3 * n - 1 : ℕ) : ℝ)
  let B : ℝ := ((3 * n + 2 : ℕ) : ℝ) / ((3 * n : ℕ) : ℝ)
  let r : ℝ := ((n + 1 : ℕ) : ℝ) / (n : ℝ)
  have hτ0 : 0 ≤ τ := by
    dsimp [τ]
    have H := OM.PolMul.SpectralFacts.proof_SP_5 F φ
    have h1 : 0 ≤ Real.logb 2 (Spectral.eval φ (matMul (F := F) 1 1 2)) :=
      Real.logb_nonneg (by norm_num) H.1.1
    have h2 : 0 ≤ Real.logb 2 (Spectral.eval φ (matMul (F := F) 2 1 1)) :=
      Real.logb_nonneg (by norm_num) H.2.1.1
    have h3 : 0 ≤ Real.logb 2 (Spectral.eval φ (matMul (F := F) 1 2 1)) :=
      Real.logb_nonneg (by norm_num) H.2.2.1.1
    positivity
  have hA : 0 < A := by
    dsimp [A]
    have hd : 0 < 3 * n - 1 := by omega
    exact div_pos (by positivity) (by exact_mod_cast hd)
  have hB : 0 < B := by
    dsimp [B]
    exact div_pos (by positivity) (by exact_mod_cast (mul_pos (by norm_num : 0 < 3) (by omega : 0 < n)))
  have hr : 0 < r := by
    dsimp [r]
    exact div_pos (by positivity) (by exact_mod_cast (by omega : 0 < n))
  have hfirst := profile_product_step φ n n hn hn
  have hsecond := profile_product_step φ (n + 1) n (by omega) hn
  dsimp only at hfirst hsecond
  change (((2 * n + n + 1 : ℕ) : ℝ) / ((2 * n + n - 1 : ℕ) : ℝ)) ^
      (2 * τ) ≤ G n (n + 1) / G n n at hfirst
  rw [show 2 * n + n + 1 = 3 * n + 1 by omega,
    show 2 * n + n - 1 = 3 * n - 1 by omega] at hfirst
  change A ^ (2 * τ) ≤ G n (n + 1) / G n n at hfirst
  change (((2 * n + (n + 1) + 1 : ℕ) : ℝ) / ((2 * n + (n + 1) - 1 : ℕ) : ℝ)) ^
      (2 * τ) ≤ G (n + 1) (n + 1) / G (n + 1) n at hsecond
  rw [show 2 * n + (n + 1) + 1 = 3 * n + 2 by omega,
    show 2 * n + (n + 1) - 1 = 3 * n by omega] at hsecond
  change B ^ (2 * τ) ≤ G (n + 1) (n + 1) / G (n + 1) n at hsecond
  have hmul : A ^ (2 * τ) * B ^ (2 * τ) ≤
      (G n (n + 1) / G n n) * (G (n + 1) (n + 1) / G (n + 1) n) := by
    exact mul_le_mul hfirst hsecond (Real.rpow_nonneg hB.le _)
      (div_pos (profileProduct_pos φ _ _) (profileProduct_pos φ _ _)).le
  have hswap : G n (n + 1) = G (n + 1) n := by
    dsimp [G, q]
    exact profile_product_swap φ (Nat.toPNat' n) (Nat.toPNat' (n + 1))
  have hmul' : (A * B) ^ (2 * τ) ≤ G (n + 1) (n + 1) / G n n := by
    rw [Real.mul_rpow hA.le hB.le]
    refine hmul.trans_eq ?_
    rw [hswap]
    have hmid := profileProduct_pos φ (q (n + 1)) (q n)
    have h00 := profileProduct_pos φ (q n) (q n)
    change 0 < G (n + 1) n at hmid
    change 0 < G n n at h00
    field_simp [hmid.ne', h00.ne']
  have hratio : r ^ ((4 : ℝ) / 3) ≤ A * B := by
    let C : ℝ := ((3 * n + 2 : ℕ) : ℝ) / ((3 * n - 1 : ℕ) : ℝ)
    let D : ℝ := ((3 * n + 1 : ℕ) : ℝ) / ((3 * n : ℕ) : ℝ)
    have hC : r ≤ C := by
      dsimp [r, C]
      have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
      have hdR : (0 : ℝ) < ((3 * n - 1 : ℕ) : ℝ) := by
        exact_mod_cast (by omega : 0 < 3 * n - 1)
      rw [div_le_div_iff₀ hnR hdR]
      push_cast [Nat.cast_sub (by omega : 1 ≤ 3 * n)]
      ring_nf
      linarith
    have hD : r ^ ((1 : ℝ) / 3) ≤ D := by
      apply le_of_pow_le_pow_left₀ (by norm_num : (3 : ℕ) ≠ 0) (by dsimp [D]; positivity)
      have hl : (r ^ ((1 : ℝ) / 3)) ^ (3 : ℕ) = r := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hr.le]
        norm_num
      rw [hl]
      dsimp [r, D]
      have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
      have h3nR : (0 : ℝ) < ((3 * n : ℕ) : ℝ) := by positivity
      rw [div_pow, div_le_div_iff₀ hnR (pow_pos h3nR 3)]
      push_cast
      ring_nf
      nlinarith [sq_nonneg (n : ℝ)]
    have hCD : r * r ^ ((1 : ℝ) / 3) ≤ C * D :=
      mul_le_mul hC hD (Real.rpow_nonneg hr.le _)
        (hr.le.trans hC)
    have hleft : r ^ ((4 : ℝ) / 3) = r * r ^ ((1 : ℝ) / 3) := by
      rw [show (4 : ℝ) / 3 = 1 + 1 / 3 by ring, Real.rpow_add hr,
        Real.rpow_one]
    have hright : C * D = A * B := by
      dsimp [A, B, C, D]
      field_simp
    rw [hleft, ← hright]
    exact hCD
  have hrpow : (r ^ ((4 : ℝ) / 3)) ^ (2 * τ) ≤ (A * B) ^ (2 * τ) :=
    Real.rpow_le_rpow (Real.rpow_nonneg hr.le _) hratio
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hτ0)
  have hnormalize : (r ^ ((4 : ℝ) / 3)) ^ (2 * τ) = r ^ (8 * τ / 3) := by
    rw [← Real.rpow_mul hr.le]
    congr 1
    ring
  dsimp only
  change r ^ (8 * τ / 3) ≤ G (n + 1) (n + 1) / G n n
  rw [← hnormalize]
  exact hrpow.trans hmul'

set_option maxHeartbeats 400000 in
private lemma profile_growth_from_profiles {F : Type u} [Field F]
    (φ : Spectral F) (N : ℕ+) :
    let τ := Real.logb 2 (Spectral.eval φ (matMul (F := F) 1 1 2)) +
      Real.logb 2 (Spectral.eval φ (matMul (F := F) 2 1 1)) +
      Real.logb 2 (Spectral.eval φ (matMul (F := F) 1 2 1))
    (((N : ℕ) : ℝ) ^ (8 * τ / 3)) ≤
      ∏ π : Equiv.Perm (Fin 3), Spectral.eval φ (perm π (polmul N N)) := by
  let τ := Real.logb 2 (Spectral.eval φ (matMul (F := F) 1 1 2)) +
    Real.logb 2 (Spectral.eval φ (matMul (F := F) 2 1 1)) +
    Real.logb 2 (Spectral.eval φ (matMul (F := F) 1 2 1))
  let E : ℝ := 8 * τ / 3
  let q : ℕ → ℕ+ := Nat.toPNat'
  let G : ℕ → ℝ := fun n => profileProduct φ (q n) (q n)
  have hτ0 : 0 ≤ τ := by
    dsimp [τ]
    have H := OM.PolMul.SpectralFacts.proof_SP_5 F φ
    have h1 : 0 ≤ Real.logb 2 (Spectral.eval φ (matMul (F := F) 1 1 2)) :=
      Real.logb_nonneg (by norm_num) H.1.1
    have h2 : 0 ≤ Real.logb 2 (Spectral.eval φ (matMul (F := F) 2 1 1)) :=
      Real.logb_nonneg (by norm_num) H.2.1.1
    have h3 : 0 ≤ Real.logb 2 (Spectral.eval φ (matMul (F := F) 1 2 1)) :=
      Real.logb_nonneg (by norm_num) H.2.2.1.1
    positivity
  have hE0 : 0 ≤ E := by dsimp [E]; positivity
  have hbase : G 1 = 1 := by
    dsimp [G, q, profileProduct]
    apply Finset.prod_eq_one
    intro π _
    have H := OM.PolMul.Profiles.proof_PR_1 F (Spectral.perm π φ) (1 : ℕ+) (1 : ℕ+)
    have hlo : (1 : ℝ) ≤ Spectral.eval (Spectral.perm π φ)
        (polmul (F := F) 1 1) := by simpa using! H.1
    have hhi : Spectral.eval (Spectral.perm π φ)
        (polmul (F := F) 1 1) ≤ (1 : ℝ) := by simpa using! H.2.1
    exact le_antisymm hhi hlo
  have growth : ∀ n : ℕ, 1 ≤ n → ((n : ℝ) ^ E) ≤ G n := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base =>
        rw [hbase]
        simpa only [Nat.cast_one] using! le_of_eq (Real.one_rpow E)
    | succ n hn ih =>
        have hs := profile_square_step φ n hn
        change ((((n + 1 : ℕ) : ℝ) / (n : ℝ)) ^ E) ≤ G (n + 1) / G n at hs
        have hmul : (n : ℝ) ^ E *
            (((n + 1 : ℕ) : ℝ) / (n : ℝ)) ^ E ≤
            G n * (G (n + 1) / G n) := by
          exact mul_le_mul ih hs (Real.rpow_nonneg (by positivity) E)
            (profileProduct_pos φ (q n) (q n)).le
        have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
        have hratioR : 0 ≤ ((n + 1 : ℕ) : ℝ) / (n : ℝ) := by positivity
        have hleft : (n : ℝ) ^ E *
            (((n + 1 : ℕ) : ℝ) / (n : ℝ)) ^ E =
            ((n + 1 : ℕ) : ℝ) ^ E := by
          rw [← Real.mul_rpow hnR.le hratioR]
          congr 1
          field_simp
        have hGn := profileProduct_pos φ (q n) (q n)
        change 0 < G n at hGn
        rw [hleft] at hmul
        convert! hmul using 1
        field_simp [hGn.ne']
  have hNq : q (N : ℕ) = N := by
    apply PNat.eq
    exact PNat.toPNat'_coe N.pos
  have H := growth (N : ℕ) N.pos
  rw [show G (N : ℕ) = profileProduct φ N N by simp only [G, hNq]] at H
  have hout : profileProduct φ N N =
      ∏ π : Equiv.Perm (Fin 3), Spectral.eval φ (perm π (polmul N N)) := by
    apply Finset.prod_congr rfl
    intro π _
    exact OM.PolMul.Superadditivity.eval_perm φ π (polmul N N)
  dsimp only
  change (((N : ℕ) : ℝ) ^ E) ≤
    ∏ π : Equiv.Perm (Fin 3), Spectral.eval φ (perm π (polmul N N))
  rw [← hout]
  exact H

-- The profile lemmas discharge the hypothesis of the already-verified AN.3
-- conversion, whose final use of SP.5 replaces the three exponents by τ.
set_option maxHeartbeats 500000 in
theorem proof_AN_3 : OM_S_AN_3 := by
  apply proof_AN_3_of_profile_growth
  intro F _ φ n
  change (((n : ℕ) : ℝ) ^
      (8 * (Real.logb 2 (Spectral.eval φ (matMul (F := F) 1 1 2)) +
        Real.logb 2 (Spectral.eval φ (matMul (F := F) 2 1 1)) +
        Real.logb 2 (Spectral.eval φ (matMul (F := F) 1 2 1))) / 3)) ≤
    ∏ π : Equiv.Perm (Fin 3), Spectral.eval φ (perm π (polmul n n))
  exact profile_growth_from_profiles φ n

end OM.PolMul.Analysis
