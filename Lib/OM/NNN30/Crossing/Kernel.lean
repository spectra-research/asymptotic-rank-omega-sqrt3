import Lib.OM.NNN30.Crossing.OPE

namespace OM.NNN30.Crossing

/-- `kc a b = (a + b - 1)! / ((a - 1)! (b - 1)!)`, the constant of the kernel
`∂^{a-1}_x ∂^{b-1}_y (x - y)^{-2} / ((a-1)! (b-1)!)`. -/
noncomputable def kc (a b : ℕ) : ℂ :=
  ((a + b - 1).factorial : ℂ) / ((a - 1).factorial * (b - 1).factorial)

theorem kc_symm (a b : ℕ) : kc a b = kc b a := by
  unfold kc; rw [add_comm a b, mul_comm]

/-- The sign `(-1)^(a+1)` (`= (-1)^(a-1)` for `a ≥ 1`). -/
noncomputable def sg (a : ℕ) : ℂ := (-1) ^ (a + 1)

theorem kc_succ (a c : ℕ) :
    kc (a + 1) (c + 1) = ((a + c + 1).factorial : ℂ) / (a.factorial * c.factorial) := by
  unfold kc
  rw [show a + 1 + (c + 1) - 1 = a + c + 1 by omega, Nat.add_sub_cancel, Nat.add_sub_cancel]

/-- The Taylor rule for the kernel constants: `kc a c * C(n+c-1, n-a) = C(n-1, n-a) * kc n c`,
with `a = a' + 1`, `c = c' + 1`, `n = a + t`. -/
theorem kc_taylor (a c t : ℕ) :
    kc (a + 1) (c + 1) * ((a + t + c + 1).choose t : ℂ) =
      ((a + t).choose t : ℂ) * kc (a + 1 + t) (c + 1) := by
  rw [kc_succ, show a + 1 + t = (a + t) + 1 by ring, kc_succ]
  rw [Nat.cast_choose ℂ (show t ≤ a + t + c + 1 by omega),
    Nat.cast_choose ℂ (show t ≤ a + t by omega)]
  rw [show a + t + c + 1 - t = a + c + 1 by omega, show a + t - t = a by omega]
  have h1 : (a.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have h2 : (c.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have h3 : (t.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have h4 : ((a + c + 1).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have h5 : ((a + t).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  field_simp


/-- The polynomial kernel of `P(z) = z^M (z-1)^M F(z)`: the four-point kernels with the dressing
`z^a (z-1)^a` on `z`-modes, `z^b` on `0`-modes (`p`) and `(z-1)^c` on `1`-modes (`q`). -/
noncomputable def fullK : Pt × ℕ → Pt × ℕ → Polynomial ℂ
  | (.z, a), (.p, b) | (.p, b), (.z, a) =>
      Polynomial.C (sg a * kc a b) * (Polynomial.X - 1) ^ a
  | (.z, a), (.q, c) | (.q, c), (.z, a) =>
      Polynomial.C (sg a * kc a c) * Polynomial.X ^ a
  | (.z, a), (.inf, d) | (.inf, d), (.z, a) =>
      Polynomial.C ((d - 1).choose (a - 1) : ℂ) * Polynomial.X ^ d * (Polynomial.X - 1) ^ a
  | (.p, b), (.q, c) | (.q, c), (.p, b) =>
      Polynomial.C (sg c * kc b c) * Polynomial.X ^ b * (Polynomial.X - 1) ^ c
  | (.p, b), (.inf, d) | (.inf, d), (.p, b) => if b = d then Polynomial.X ^ b else 0
  | (.q, c), (.inf, d) | (.inf, d), (.q, c) =>
      Polynomial.C ((d - 1).choose (c - 1) : ℂ) * (Polynomial.X - 1) ^ c
  | _, _ => 0

theorem fullK_symm (u v : Pt × ℕ) : fullK u v = fullK v u := by
  rcases u with ⟨_ | _ | _ | _ | _, a⟩ <;> rcases v with ⟨_ | _ | _ | _ | _, b⟩ <;> rfl

section DegHelpers
open Polynomial

theorem natDeg_C_mul_X_sub_one_pow (x : ℂ) (a : ℕ) : (C x * (X - 1) ^ a).natDegree ≤ a :=
  (natDegree_C_mul_le _ _).trans ((natDegree_pow_le).trans (by
    rw [show (X - 1 : ℂ[X]) = X - C 1 by simp, natDegree_X_sub_C]; simp))

theorem natDeg_C_mul_X_pow (x : ℂ) (a : ℕ) : (C x * X ^ a).natDegree ≤ a :=
  (natDegree_C_mul_le _ _).trans (by rw [natDegree_X_pow])

theorem natDeg_C_mul_X_pow_mul (x : ℂ) (b c : ℕ) :
    (C x * X ^ b * (X - 1) ^ c).natDegree ≤ b + c :=
  (natDegree_mul_le).trans (add_le_add (natDeg_C_mul_X_pow x b)
    ((natDegree_pow_le).trans (by
      rw [show (X - 1 : ℂ[X]) = X - C 1 by simp, natDegree_X_sub_C]; simp)))

end DegHelpers

theorem fullK_natDegree (u v : Pt × ℕ) : (fullK u v).natDegree ≤ u.2 + v.2 := by
  rcases u with ⟨_ | _ | _ | _ | _, a⟩ <;> rcases v with ⟨_ | _ | _ | _ | _, b⟩ <;>
    simp only [fullK, Polynomial.natDegree_zero, zero_le]
  · exact (natDeg_C_mul_X_sub_one_pow _ a).trans (by omega)
  · exact (natDeg_C_mul_X_pow _ a).trans (by omega)
  · exact (natDeg_C_mul_X_pow_mul _ b a).trans (by omega)
  · exact (natDeg_C_mul_X_sub_one_pow _ b).trans (by omega)
  · exact (natDeg_C_mul_X_pow_mul _ a b).trans (by omega)
  · split_ifs
    · rw [Polynomial.natDegree_X_pow]; omega
    · simp
  · exact (natDeg_C_mul_X_pow _ b).trans (by omega)
  · exact (natDeg_C_mul_X_pow_mul _ b a).trans (by omega)
  · exact (natDeg_C_mul_X_sub_one_pow _ a).trans (by omega)
  · exact (natDeg_C_mul_X_pow_mul _ a b).trans (by omega)
  · split_ifs
    · rw [Polynomial.natDegree_X_pow]; omega
    · simp
  · exact (natDeg_C_mul_X_sub_one_pow _ b).trans (by omega)

/-- The top-degree kernel: only `z`–`∞` and `0`–`1` pairs reach the full degree. -/
noncomputable def topK : Pt × ℕ → Pt × ℕ → ℂ
  | (.z, a), (.inf, d) | (.inf, d), (.z, a) => ((d - 1).choose (a - 1) : ℂ)
  | (.p, b), (.q, c) | (.q, c), (.p, b) => sg c * kc b c
  | _, _ => 0

theorem topK_symm (u v : Pt × ℕ) : topK u v = topK v u := by
  rcases u with ⟨_ | _ | _ | _ | _, a⟩ <;> rcases v with ⟨_ | _ | _ | _ | _, b⟩ <;> rfl

section TopHelpers
open Polynomial

theorem coeff_X_sub_one_pow_self (a : ℕ) : ((X - 1 : ℂ[X]) ^ a).coeff a = 1 := by
  have hm : ((X - C 1 : ℂ[X]) ^ a).Monic := (monic_X_sub_C 1).pow a
  have hd : ((X - C 1 : ℂ[X]) ^ a).natDegree = a := by
    rw [natDegree_pow, natDegree_X_sub_C, mul_one]
  have := hm.coeff_natDegree
  rw [hd] at this
  simpa using this

theorem coeff_C_mul_X_pow_mul_top (x : ℂ) (b c : ℕ) :
    (C x * X ^ b * (X - 1) ^ c).coeff (b + c) = x := by
  rw [mul_assoc, coeff_C_mul, add_comm, coeff_X_pow_mul, coeff_X_sub_one_pow_self, mul_one]

end TopHelpers

theorem fullK_top (u v : Pt × ℕ) (hu : 0 < u.2) (hv : 0 < v.2) :
    (fullK u v).coeff (u.2 + v.2) = topK u v := by
  rcases u with ⟨_ | _ | _ | _ | _, a⟩ <;> rcases v with ⟨_ | _ | _ | _ | _, b⟩ <;>
    simp only at hu hv <;> simp only [fullK, topK, Polynomial.coeff_zero]
  · exact Polynomial.coeff_eq_zero_of_natDegree_lt ((natDeg_C_mul_X_sub_one_pow _ a).trans_lt (by omega))
  · exact Polynomial.coeff_eq_zero_of_natDegree_lt ((natDeg_C_mul_X_pow _ a).trans_lt (by omega))
  · rw [show a + b = b + a by ring, coeff_C_mul_X_pow_mul_top]
  · exact Polynomial.coeff_eq_zero_of_natDegree_lt ((natDeg_C_mul_X_sub_one_pow _ b).trans_lt (by omega))
  · rw [coeff_C_mul_X_pow_mul_top]
  · split_ifs
    · rw [Polynomial.coeff_X_pow]; simp; omega
    · simp
  · exact Polynomial.coeff_eq_zero_of_natDegree_lt ((natDeg_C_mul_X_pow _ b).trans_lt (by omega))
  · rw [show a + b = b + a by ring, coeff_C_mul_X_pow_mul_top]
  · exact Polynomial.coeff_eq_zero_of_natDegree_lt ((natDeg_C_mul_X_sub_one_pow _ a).trans_lt (by omega))
  · rw [coeff_C_mul_X_pow_mul_top]
  · split_ifs
    · rw [Polynomial.coeff_X_pow]; simp; omega
    · simp
  · exact Polynomial.coeff_eq_zero_of_natDegree_lt ((natDeg_C_mul_X_sub_one_pow _ b).trans_lt (by omega))

section PS
open PowerSeries

/-- `(1 - X)^{-(d+1)} = Σ_t C(d + t, d) X^t`. -/
noncomputable def negBin (d : ℕ) : ℂ⟦X⟧ := mk fun t => ((d + t).choose d : ℂ)

theorem negBin_mul (d : ℕ) : negBin d * (1 - X) ^ (d + 1) = 1 :=
  mk_add_choose_mul_one_sub_pow_eq_one ℂ d

/-- `(1 + X)^{-(d+1)} = Σ_t (-1)^t C(d + t, d) X^t`. -/
noncomputable def negBinAlt (d : ℕ) : ℂ⟦X⟧ := mk fun t => (-1) ^ t * ((d + t).choose d : ℂ)

theorem negBinAlt_mul (d : ℕ) : negBinAlt d * (1 + X) ^ (d + 1) = 1 := by
  have h := congrArg (rescale (-1 : ℂ)) (negBin_mul d)
  rw [map_mul, map_pow, map_sub, map_one, rescale_X] at h
  have e1 : rescale (-1 : ℂ) (negBin d) = negBinAlt d := by
    ext t; rw [coeff_rescale]; simp [negBin, negBinAlt, coeff_mk]
  have e2 : (1 - C (-1 : ℂ) * X : ℂ⟦X⟧) = 1 + X := by
    rw [map_neg, map_one]; ring
  rw [e1, e2] at h
  exact h

/-- The kernel for the expansion at `0` (`z = w`, dressing `w^a` on `z`-modes and `w^b` on
`0`-modes; `p` = the point `0`, `q` = the point `1`). -/
noncomputable def ker0 : Pt × ℕ → Pt × ℕ → ℂ⟦X⟧
  | (.z, a), (.p, b) | (.p, b), (.z, a) => C (sg a * kc a b)
  | (.z, a), (.q, c) | (.q, c), (.z, a) =>
      C (sg a * kc a c * (-1) ^ (a + c)) * X ^ a * negBin (a + c - 1)
  | (.z, a), (.inf, d) | (.inf, d), (.z, a) => C ((d - 1).choose (a - 1) : ℂ) * X ^ d
  | (.p, b), (.q, c) | (.q, c), (.p, b) => C (sg c * kc b c) * X ^ b
  | (.p, b), (.inf, d) | (.inf, d), (.p, b) => if b = d then X ^ b else 0
  | (.q, c), (.inf, d) | (.inf, d), (.q, c) => C ((d - 1).choose (c - 1) : ℂ)
  | (.sig, n), (.q, c) | (.q, c), (.sig, n) => C (sg c * kc n c)
  | (.sig, n), (.inf, d) | (.inf, d), (.sig, n) => if n = d then 1 else 0
  | _, _ => 0

/-- The kernel for the expansion at `1` (`z = 1 + w`, dressing `w^a` on `z`-modes and `w^c` on
`1`-modes; `p` = the point `1`, `q` = the point `0`). -/
noncomputable def ker1 : Pt × ℕ → Pt × ℕ → ℂ⟦X⟧
  | (.z, a), (.p, c) | (.p, c), (.z, a) => C (sg a * kc a c)
  | (.z, a), (.q, b) | (.q, b), (.z, a) => C (sg a * kc a b) * X ^ a * negBinAlt (a + b - 1)
  | (.z, a), (.inf, d) | (.inf, d), (.z, a) =>
      C ((d - 1).choose (a - 1) : ℂ) * X ^ a * (1 + X) ^ (d - a)
  | (.p, c), (.q, b) | (.q, b), (.p, c) => C (sg c * kc c b) * X ^ c
  | (.p, c), (.inf, d) | (.inf, d), (.p, c) => C ((d - 1).choose (c - 1) : ℂ) * X ^ c
  | (.q, b), (.inf, d) | (.inf, d), (.q, b) => if b = d then 1 else 0
  | (.sig, n), (.q, b) | (.q, b), (.sig, n) => C (sg n * kc n b)
  | (.sig, n), (.inf, d) | (.inf, d), (.sig, n) => C ((d - 1).choose (n - 1) : ℂ)
  | _, _ => 0

theorem ker0_symm (u v : Pt × ℕ) : ker0 u v = ker0 v u := by
  rcases u with ⟨_ | _ | _ | _ | _, a⟩ <;> rcases v with ⟨_ | _ | _ | _ | _, b⟩ <;> rfl

theorem ker1_symm (u v : Pt × ℕ) : ker1 u v = ker1 v u := by
  rcases u with ⟨_ | _ | _ | _ | _, a⟩ <;> rcases v with ⟨_ | _ | _ | _ | _, b⟩ <;> rfl

theorem coeff_one_add_X_pow_ps (m k : ℕ) : coeff k ((1 + X : ℂ⟦X⟧) ^ m) = (m.choose k : ℂ) := by
  have : ((1 + X : ℂ⟦X⟧) ^ m) = (((1 + Polynomial.X : Polynomial ℂ) ^ m : Polynomial ℂ) : ℂ⟦X⟧) := by
    simp
  rw [this, Polynomial.coeff_coe, Polynomial.coeff_one_add_X_pow]

theorem sg_succ_mul (a c : ℕ) : sg (a + 1) * (-1 : ℂ) ^ (a + 1 + (c + 1)) = sg (c + 1) := by
  unfold sg
  rw [← pow_add, show a + 1 + 1 + (a + 1 + (c + 1)) = (c + 1 + 1) + 2 * (a + 1) by ring, pow_add,
    pow_mul]
  norm_num

theorem sg_shift (a t : ℕ) : sg (a + 1) * (-1 : ℂ) ^ t = sg (a + 1 + t) := by
  unfold sg
  rw [← pow_add]
  ring_nf

/-- Binomial identity behind the Taylor rule at infinity, expansion at `1`. -/
theorem choose_taylor_inf (a t d : ℕ) :
    (d.choose a : ℂ) * ((d - a).choose t : ℂ) = ((a + t).choose t : ℂ) * (d.choose (a + t) : ℂ) := by
  have := Nat.choose_mul (n := d) (k := a + t) (s := a) (by omega)
  rw [show a + t - a = t by omega] at this
  rw [show (a + t).choose t = (a + t).choose a from (Nat.choose_symm_add).symm]
  exact_mod_cast (by rw [mul_comm ((a + t).choose a)]; exact this.symm)

theorem opeHyp_ker0 : OPEHyp ker0 where
  symm := ker0_symm
  zz := fun _ _ => rfl
  pp := fun _ _ => rfl
  zs := fun _ _ => rfl
  ps := fun _ _ => rfl
  ss := fun _ _ => rfl
  zp := fun _ _ => ⟨_, rfl⟩
  zfar := by
    rintro a ha ⟨py, m⟩ ⟨hpy, hm⟩ n
    simp only at hpy hm
    obtain ⟨a, rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
    rcases hpy with rfl | rfl
    · -- the point `1`
      obtain ⟨c, rfl⟩ : ∃ c', m = c' + 1 := ⟨m - 1, by omega⟩
      simp only [ker0, mul_assoc, coeff_C_mul, coeff_X_pow_mul', constantCoeff_C]
      split_ifs with han
      · obtain ⟨t, rfl⟩ : ∃ t, n = a + 1 + t := ⟨n - (a + 1), by omega⟩
        rw [negBin, coeff_mk, show a + 1 + (c + 1) - 1 = a + c + 1 by omega,
          show a + 1 + t - (a + 1) = t by omega, show a + 1 + t - 1 = a + t by omega,
          Nat.choose_symm_add, show a + c + 1 + t = a + t + c + 1 by ring]
        have hk := kc_taylor a c t
        have hs := sg_succ_mul a c
        calc sg (a + 1) * (kc (a + 1) (c + 1) * ((-1) ^ (a + 1 + (c + 1)) *
              ((a + t + c + 1).choose t : ℂ)))
            = (sg (a + 1) * (-1) ^ (a + 1 + (c + 1))) * (kc (a + 1) (c + 1) *
              ((a + t + c + 1).choose t : ℂ)) := by ring
          _ = sg (c + 1) * (((a + t).choose t : ℂ) * kc (a + 1 + t) (c + 1)) := by rw [hs, hk]
          _ = ((a + t).choose t : ℂ) * (sg (c + 1) * kc (a + 1 + t) (c + 1)) := by ring
      · simp
    · -- the point at infinity
      simp only [ker0, coeff_C_mul, coeff_X_pow, apply_ite constantCoeff, constantCoeff_one,
        map_zero]
      by_cases hnd : n = m
      · subst hnd
        by_cases han : a + 1 ≤ n
        · simp only [if_true, if_pos han, mul_one]
          rw [show n - (a + 1) = n - 1 - a by omega, ← Nat.choose_symm (by omega)]
          simp
        · rw [if_neg han, Nat.choose_eq_zero_of_lt (by omega)]; simp
      · simp [hnd]
  pfar := by
    rintro b ⟨py, m⟩ ⟨hpy, _⟩
    simp only at hpy
    rcases hpy with rfl | rfl
    · simp only [ker0]; ring
    · simp only [ker0]; split_ifs <;> simp
  farconst := by
    rintro ⟨pu, a⟩ ⟨pv, b⟩ hu hv
    rcases hu with ⟨hu, _⟩ | hu <;> rcases hv with ⟨hv, _⟩ | hv <;>
      simp only at hu hv <;>
      (try rcases hu with rfl | rfl) <;> (try rcases hv with rfl | rfl) <;>
      simp only [ker0, constantCoeff_C, map_zero] <;>
      split_ifs <;> simp

theorem opeHyp_ker1 : OPEHyp ker1 where
  symm := ker1_symm
  zz := fun _ _ => rfl
  pp := fun _ _ => rfl
  zs := fun _ _ => rfl
  ps := fun _ _ => rfl
  ss := fun _ _ => rfl
  zp := fun _ _ => ⟨_, rfl⟩
  zfar := by
    rintro a ha ⟨py, m⟩ ⟨hpy, hm⟩ n
    simp only at hpy hm
    obtain ⟨a, rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
    rcases hpy with rfl | rfl
    · -- the point `0`
      obtain ⟨b, rfl⟩ : ∃ b', m = b' + 1 := ⟨m - 1, by omega⟩
      simp only [ker1, mul_assoc, coeff_C_mul, coeff_X_pow_mul', constantCoeff_C]
      split_ifs with han
      · obtain ⟨t, rfl⟩ : ∃ t, n = a + 1 + t := ⟨n - (a + 1), by omega⟩
        rw [negBinAlt, coeff_mk, show a + 1 + (b + 1) - 1 = a + b + 1 by omega,
          show a + 1 + t - (a + 1) = t by omega, show a + 1 + t - 1 = a + t by omega,
          Nat.choose_symm_add, show a + b + 1 + t = a + t + b + 1 by ring]
        have hk := kc_taylor a b t
        have hs := sg_shift a t
        calc sg (a + 1) * (kc (a + 1) (b + 1) * ((-1) ^ t * ((a + t + b + 1).choose t : ℂ)))
            = (sg (a + 1) * (-1) ^ t) * (kc (a + 1) (b + 1) * ((a + t + b + 1).choose t : ℂ)) := by
              ring
          _ = sg (a + 1 + t) * (((a + t).choose t : ℂ) * kc (a + 1 + t) (b + 1)) := by rw [hs, hk]
          _ = ((a + t).choose t : ℂ) * (sg (a + 1 + t) * kc (a + 1 + t) (b + 1)) := by ring
      · simp
    · -- the point at infinity
      obtain ⟨d, rfl⟩ : ∃ d', m = d' + 1 := ⟨m - 1, by omega⟩
      simp only [ker1, mul_assoc, coeff_C_mul, coeff_X_pow_mul', constantCoeff_C]
      split_ifs with han
      · obtain ⟨t, rfl⟩ : ∃ t, n = a + 1 + t := ⟨n - (a + 1), by omega⟩
        rw [coeff_one_add_X_pow_ps, show a + 1 + t - (a + 1) = t by omega,
          show a + 1 + t - 1 = a + t by omega, show d + 1 - 1 = d by omega,
          show a + 1 - 1 = a by omega, show d + 1 - (a + 1) = d - a by omega]
        exact choose_taylor_inf a t d
      · simp
  pfar := by
    rintro b ⟨py, m⟩ ⟨hpy, _⟩
    simp only at hpy
    rcases hpy with rfl | rfl <;> simp only [ker1] <;> ring
  farconst := by
    rintro ⟨pu, a⟩ ⟨pv, b⟩ hu hv
    rcases hu with ⟨hu, _⟩ | hu <;> rcases hv with ⟨hv, _⟩ | hv <;>
      simp only at hu hv <;>
      (try rcases hu with rfl | rfl) <;> (try rcases hv with rfl | rfl) <;>
      simp only [ker1, constantCoeff_C, map_zero] <;>
      split_ifs <;> simp

/-- The four points of the four-point function (no fused modes). -/
def IsFour (u : Pt × ℕ) : Prop := u.1 ≠ Pt.sig ∧ 0 < u.2

/-- Dressing removed by the expansion at `0`. -/
noncomputable def s0 : Pt × ℕ → ℂ⟦X⟧
  | (.z, a) => (X - 1) ^ a
  | (.q, c) => (X - 1) ^ c
  | _ => 1

/-- Dressing removed by the expansion at `1`. -/
noncomputable def s1 : Pt × ℕ → ℂ⟦X⟧
  | (.z, a) => (1 + X) ^ a
  | (.p, b) => (1 + X) ^ b
  | _ => 1

/-- Exchange of the points `0` and `1`. -/
def swPt : Pt → Pt
  | .p => .q
  | .q => .p
  | x => x

def sw (u : Pt × ℕ) : Pt × ℕ := (swPt u.1, u.2)

theorem coe_fullK_zq (a c : ℕ) (ha : 0 < a) (hc : 0 < c) :
    ((Polynomial.C (sg a * kc a c) * Polynomial.X ^ a : Polynomial ℂ) : ℂ⟦X⟧) =
      (X - 1) ^ a * (X - 1) ^ c * (C (sg a * kc a c * (-1) ^ (a + c)) * X ^ a * negBin (a + c - 1)) := by
  have hn := negBin_mul (a + c - 1)
  rw [show a + c - 1 + 1 = a + c by omega] at hn
  have e : (X - 1 : ℂ⟦X⟧) ^ a * (X - 1) ^ c * C ((-1 : ℂ) ^ (a + c)) = (1 - X) ^ (a + c) := by
    rw [← pow_add, map_pow, map_neg, map_one, ← mul_pow]; ring
  rw [Polynomial.coe_mul, Polynomial.coe_C, Polynomial.coe_pow, Polynomial.coe_X]
  rw [show C (sg a * kc a c * (-1) ^ (a + c)) = C (sg a * kc a c) * C ((-1 : ℂ) ^ (a + c)) from
    map_mul _ _ _]
  set N := negBin (a + c - 1)
  set Y := (X - 1 : ℂ⟦X⟧)
  calc C (sg a * kc a c) * X ^ a
      = C (sg a * kc a c) * X ^ a * (N * (1 - X) ^ (a + c)) := by rw [hn, mul_one]
    _ = C (sg a * kc a c) * X ^ a * (N * (Y ^ a * Y ^ c * C ((-1 : ℂ) ^ (a + c)))) := by rw [e]
    _ = Y ^ a * Y ^ c * (C (sg a * kc a c) * C ((-1 : ℂ) ^ (a + c)) * X ^ a * N) := by ring

theorem coe_C_mul_Xsub (x : ℂ) (a : ℕ) :
    ((Polynomial.C x * (Polynomial.X - 1) ^ a : Polynomial ℂ) : ℂ⟦X⟧) = C x * (X - 1) ^ a := by
  simp only [Polynomial.coe_mul, Polynomial.coe_C, Polynomial.coe_pow, Polynomial.coe_sub,
    Polynomial.coe_X, Polynomial.coe_one]

theorem coe_C_mul_X_mul_Xsub (x : ℂ) (b c : ℕ) :
    ((Polynomial.C x * Polynomial.X ^ b * (Polynomial.X - 1) ^ c : Polynomial ℂ) : ℂ⟦X⟧) =
      C x * X ^ b * (X - 1) ^ c := by
  simp only [Polynomial.coe_mul, Polynomial.coe_C, Polynomial.coe_pow, Polynomial.coe_sub,
    Polynomial.coe_X, Polynomial.coe_one]

theorem fullK_rel0 (u v : Pt × ℕ) (hu : IsFour u) (hv : IsFour v) :
    ((fullK u v : Polynomial ℂ) : ℂ⟦X⟧) = s0 u * s0 v * ker0 u v := by
  rcases u with ⟨pu, a⟩
  rcases v with ⟨pv, b⟩
  obtain ⟨hpu, ha⟩ := hu
  obtain ⟨hpv, hb⟩ := hv
  simp only at hpu hpv ha hb
  cases pu <;> cases pv
  case z.z => simp [fullK, ker0]
  case z.p => simp only [fullK, ker0, s0]; rw [coe_C_mul_Xsub]; ring
  case z.q => exact coe_fullK_zq _ _ ha hb
  case z.inf => simp only [fullK, ker0, s0]; rw [coe_C_mul_X_mul_Xsub]; ring
  case p.z => simp only [fullK, ker0, s0]; rw [coe_C_mul_Xsub]; ring
  case p.p => simp [fullK, ker0]
  case p.q => simp only [fullK, ker0, s0]; rw [coe_C_mul_X_mul_Xsub]; ring
  case p.inf => simp only [fullK, ker0, s0]; split_ifs <;> simp
  case q.z => simp only [fullK, ker0, s0]; rw [coe_fullK_zq _ _ hb ha]; ring
  case q.p => simp only [fullK, ker0, s0]; rw [coe_C_mul_X_mul_Xsub]; ring
  case q.q => simp [fullK, ker0]
  case q.inf => simp only [fullK, ker0, s0]; rw [coe_C_mul_Xsub]; ring
  case inf.z => simp only [fullK, ker0, s0]; rw [coe_C_mul_X_mul_Xsub]; ring
  case inf.p => simp only [fullK, ker0, s0]; split_ifs <;> simp
  case inf.q => simp only [fullK, ker0, s0]; rw [coe_C_mul_Xsub]; ring
  case inf.inf => simp [fullK, ker0]
  all_goals simp at hpu hpv

/-- The substitution `z = 1 + w`, then the power series in `w`. -/
noncomputable def shift1 (P : Polynomial ℂ) : ℂ⟦X⟧ := ((P.comp (Polynomial.X + 1) : Polynomial ℂ) : ℂ⟦X⟧)

theorem shift1_C_mul_Xsub (x : ℂ) (a : ℕ) :
    shift1 (Polynomial.C x * (Polynomial.X - 1) ^ a) = C x * X ^ a := by
  simp [shift1, Polynomial.mul_comp, Polynomial.pow_comp]

theorem shift1_C_mul_X (x : ℂ) (a : ℕ) :
    shift1 (Polynomial.C x * Polynomial.X ^ a) = C x * (1 + X) ^ a := by
  simp [shift1, Polynomial.mul_comp, Polynomial.pow_comp, add_comm]

theorem shift1_C_mul_X_mul_Xsub (x : ℂ) (b c : ℕ) :
    shift1 (Polynomial.C x * Polynomial.X ^ b * (Polynomial.X - 1) ^ c) =
      C x * (1 + X) ^ b * X ^ c := by
  simp [shift1, Polynomial.mul_comp, Polynomial.pow_comp, add_comm]

theorem shift1_ite (b d : ℕ) :
    shift1 (if b = d then Polynomial.X ^ b else 0) = if b = d then (1 + X) ^ b else 0 := by
  split_ifs <;> simp [shift1, Polynomial.pow_comp, add_comm]

theorem shift1_zero : shift1 0 = 0 := by simp [shift1]

theorem shift1_zq (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    shift1 (Polynomial.C (sg a * kc a b) * (Polynomial.X - 1) ^ a) =
      (1 + X) ^ a * (1 + X) ^ b * (C (sg a * kc a b) * X ^ a * negBinAlt (a + b - 1)) := by
  rw [shift1_C_mul_Xsub]
  have hn := negBinAlt_mul (a + b - 1)
  rw [show a + b - 1 + 1 = a + b by omega] at hn
  set N := negBinAlt (a + b - 1)
  calc C (sg a * kc a b) * X ^ a = C (sg a * kc a b) * X ^ a * (N * (1 + X) ^ (a + b)) := by
        rw [hn, mul_one]
    _ = (1 + X) ^ a * (1 + X) ^ b * (C (sg a * kc a b) * X ^ a * N) := by ring

theorem shift1_zinf (a d : ℕ) (ha : 0 < a) (hd : 0 < d) :
    shift1 (Polynomial.C ((d - 1).choose (a - 1) : ℂ) * Polynomial.X ^ d * (Polynomial.X - 1) ^ a) =
      (1 + X) ^ a * (C ((d - 1).choose (a - 1) : ℂ) * X ^ a * (1 + X) ^ (d - a)) := by
  rw [shift1_C_mul_X_mul_Xsub]
  by_cases had : a ≤ d
  · have : (1 + X : ℂ⟦X⟧) ^ d = (1 + X) ^ a * (1 + X) ^ (d - a) := by
      rw [← pow_add, Nat.add_sub_cancel' had]
    rw [this]; ring
  · rw [Nat.choose_eq_zero_of_lt (by omega)]; simp

theorem fullK_rel1 (u v : Pt × ℕ) (hu : IsFour u) (hv : IsFour v) :
    shift1 (fullK u v) = s1 u * s1 v * ker1 (sw u) (sw v) := by
  rcases u with ⟨pu, a⟩
  rcases v with ⟨pv, b⟩
  obtain ⟨hpu, ha⟩ := hu
  obtain ⟨hpv, hb⟩ := hv
  simp only at hpu hpv ha hb
  cases pu <;> cases pv
  case z.z => simp [fullK, ker1, sw, swPt, shift1_zero]
  case z.p => simp only [fullK, ker1, s1, sw, swPt]; exact shift1_zq a b ha hb
  case z.q => simp only [fullK, ker1, s1, sw, swPt]; rw [shift1_C_mul_X]; ring
  case z.inf => simp only [fullK, ker1, s1, sw, swPt]; rw [shift1_zinf a b ha hb]; ring
  case p.z => simp only [fullK, ker1, s1, sw, swPt]; rw [shift1_zq b a hb ha]; ring
  case p.p => simp [fullK, ker1, sw, swPt, shift1_zero]
  case p.q =>
    simp only [fullK, ker1, s1, sw, swPt]; rw [shift1_C_mul_X_mul_Xsub, kc_symm a b]; ring
  case p.inf => simp only [fullK, ker1, s1, sw, swPt]; rw [shift1_ite]; split_ifs <;> simp
  case q.z => simp only [fullK, ker1, s1, sw, swPt]; rw [shift1_C_mul_X]; ring
  case q.p =>
    simp only [fullK, ker1, s1, sw, swPt]; rw [shift1_C_mul_X_mul_Xsub, kc_symm b a]; ring
  case q.q => simp [fullK, ker1, sw, swPt, shift1_zero]
  case q.inf => simp only [fullK, ker1, s1, sw, swPt]; rw [shift1_C_mul_Xsub]; ring
  case inf.z => simp only [fullK, ker1, s1, sw, swPt]; rw [shift1_zinf b a hb ha]; ring
  case inf.p => simp only [fullK, ker1, s1, sw, swPt]; rw [shift1_ite]; split_ifs <;> simp
  case inf.q => simp only [fullK, ker1, s1, sw, swPt]; rw [shift1_C_mul_Xsub]; ring
  case inf.inf => simp [fullK, ker1, sw, swPt, shift1_zero]
  all_goals simp at hpu hpv

end PS

end OM.NNN30.Crossing
