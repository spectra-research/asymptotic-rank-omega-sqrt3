import PLATFORM.Statements.«R116.2»
import Lib.OM.NNN36.TrianglePrice
import Mathlib.Tactic

/-! # The disc of a triangle with prescribed side lengths -/

noncomputable section
namespace OM.Formats

/-- Coordinates of the triangle and a centre witnessing the piecewise radius.
The base has length `c`. Its perpendicular bisector contains both candidate centres. -/
theorem enclosing_disc_data {a b c : ℝ} (ha : 0 < a) (hab : a ≤ b) (hbc : b ≤ c) (ht : c < a+b) :
    ∃ q o : ℂ, ‖(c : ℂ)-q‖ = a ∧ ‖q‖ = b ∧
      dist o 0 ≤ P2M.R116.discRadius a b c ∧ dist o (c : ℂ) ≤ P2M.R116.discRadius a b c ∧
      dist o q ≤ P2M.R116.discRadius a b c ∧ 0 < q.im ∧
      (c^2 < a^2+b^2 → ∃ u v w : ℝ, 0 ≤ u ∧ 0 ≤ v ∧ 0 ≤ w ∧ u+v+w=1 ∧
        v • (c:ℂ) + w • q = o ∧ ‖o‖ = P2M.R116.discRadius a b c ∧
        ‖(c:ℂ)-o‖ = P2M.R116.discRadius a b c ∧ ‖q-o‖ = P2M.R116.discRadius a b c) := by
  let s := (a+b+c)/2
  let H := Real.sqrt (s*(s-a)*(s-b)*(s-c))
  have hb := ha.trans_le hab
  have hc := hb.trans_le hbc
  have hs : 0 < s := by dsimp [s]; linarith
  have hs₁ : 0 < s-a := by dsimp [s]; linarith
  have hs₂ : 0 < s-b := by dsimp [s]; linarith
  have hs₃ : 0 < s-c := by dsimp [s]; linarith
  have hH : 0 < H := Real.sqrt_pos.mpr (by positivity)
  have hHsq : H^2 = s*(s-a)*(s-b)*(s-c) := Real.sq_sqrt (by positivity)
  let x := (b^2+c^2-a^2)/(2*c)
  let y := 2*H/c
  have hy : 0 < y := by dsimp [y]; positivity
  have hx : 2*c*x = b^2+c^2-a^2 := by dsimp [x]; field_simp
  have hq : x^2+y^2 = b^2 := by
    dsimp only [x,y]
    field_simp
    dsimp only [s] at hHsq
    linear_combination 16*hHsq
  let q : ℂ := ⟨x,y⟩
  have norm_sq (u v w z : ℝ) :
      ‖(⟨u,v⟩ : ℂ) - ⟨w,z⟩‖^2 = (u-w)^2+(v-z)^2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im]; ring
  have h₁ : ‖(c:ℂ)-q‖ = a := by
    apply (sq_eq_sq₀ (norm_nonneg _) ha.le).mp
    change ‖(⟨c,0⟩ : ℂ) - ⟨x,y⟩‖^2 = a^2
    rw [norm_sq c 0 x y]; linarith only [show (c-x)^2+(0-y)^2 = c^2-2*c*x+(x^2+y^2) by ring,hq,hx]
  have h₂ : ‖q‖ = b := by
    apply (sq_eq_sq₀ (norm_nonneg _) hb.le).mp
    rw [Complex.sq_norm, Complex.normSq_apply]
    exact (by change x*x+y*y = b^2; nlinarith only [hq])
  by_cases acute : c^2 < a^2+b^2
  · let z := (a^2+b^2-c^2)/(4*y)
    let R := a*b*c/(4*H)
    have hR : 0 ≤ R := by dsimp [R]; positivity
    have hz : 4*y*z = a^2+b^2-c^2 := by dsimp [z]; field_simp
    have ho : (c/2)^2+z^2 = R^2 := by
      dsimp only [z,y,R]
      field_simp
      dsimp only [s] at hHsq
      linear_combination 16*hHsq
    have dr : P2M.R116.discRadius a b c = R := ite_eq_left acute
    let O : ℂ := ⟨c/2,z⟩
    have reach : dist O 0 = R ∧ dist O (c:ℂ) = R ∧ dist O q = R := by
      refine ⟨?_,?_,?_⟩ <;> rw [dist_eq_norm] <;> apply (sq_eq_sq₀ (norm_nonneg _) hR).mp
      · change ‖(⟨c/2,z⟩ : ℂ) - ⟨0,0⟩‖^2 = R^2
        rw [norm_sq (c/2) z 0 0]; simpa using ho
      · change ‖(⟨c/2,z⟩ : ℂ) - ⟨c,0⟩‖^2 = R^2
        rw [norm_sq (c/2) z c 0]; linarith only [ho,show (c/2-c)^2+(z-0)^2 = (c/2)^2+z^2 by ring]
      · rw [norm_sq (c/2) z x y]; nlinarith only [hq,hx,hz,ho]
    rw [dr]
    refine ⟨q,O,h₁,h₂,reach.1.le,reach.2.1.le,reach.2.2.le,hy,fun _ => ?_⟩
    let w := z/y
    let v := (c/2-w*x)/c
    let u := 1-v-w
    have wy : w*y = z := div_mul_cancel₀ _ hy.ne'
    have vc : v*c = c/2-w*x := div_mul_cancel₀ _ hc.ne'
    have zy : 2*y*z = b^2-c*x := by linarith only [hz,hx]
    have xp : 0 ≤ x := nonneg_of_mul_nonneg_right (a := 2*c) (by
      linarith only [hx,sq_nonneg c,pow_le_pow_left₀ ha.le hab 2]) (by positivity)
    have cx : 0 ≤ c-x := nonneg_of_mul_nonneg_right (a := 2*c) (by
      nlinarith only [hx,sq_nonneg a,pow_le_pow_left₀ hb.le hbc 2]) (by positivity)
    have vId : v*(2*c*y^2) = b^2*(c-x) := by
      linear_combination 2*y^2*vc - 2*x*y*wy + c*hq - x*zy
    have uId : u*(2*c*y^2) = a^2*x := by
      dsimp [u]
      linear_combination -2*y^2*vc - 2*(c-x)*y*wy + c*hq - (c-x)*zy - x*hx
    have denom : 0 < 2*c*y^2 := by positivity
    refine ⟨u,v,w,nonneg_of_mul_nonneg_left (uId.symm ▸ mul_nonneg (sq_nonneg a) xp) denom,
      nonneg_of_mul_nonneg_left (vId.symm ▸ mul_nonneg (sq_nonneg b) cx) denom,
      div_nonneg (by dsimp [z]; positivity) hy.le,by dsimp [u]; ring,?_,?_,?_,?_⟩
    · apply Complex.ext
      · simp only [Complex.add_re,Complex.smul_re,Complex.ofReal_re,smul_eq_mul,O,q]
        linarith only [vc]
      · simpa only [Complex.add_im,Complex.smul_im,Complex.ofReal_im,smul_eq_mul,O,q,mul_zero,zero_add] using wy
    · simpa only [dist_zero_right] using reach.1
    · simpa only [dist_eq_norm,norm_sub_rev (c:ℂ) O] using reach.2.1
    · simpa only [dist_eq_norm,norm_sub_rev q O] using reach.2.2
  · have dr : P2M.R116.discRadius a b c = c/2 := ite_eq_right acute
    refine ⟨q, ⟨c/2,0⟩,h₁,h₂,?_,?_,?_,hy,fun h => (acute h).elim⟩ <;> rw [dr,dist_eq_norm] <;>
      apply (sq_le_sq₀ (norm_nonneg _) (half_pos hc).le).mp
    · change ‖(⟨c/2,0⟩ : ℂ) - ⟨0,0⟩‖^2 ≤ (c/2)^2
      rw [norm_sq (c/2) 0 0 0]; simp
    · change ‖(⟨c/2,0⟩ : ℂ) - ⟨c,0⟩‖^2 ≤ (c/2)^2
      rw [norm_sq (c/2) 0 c 0]; linarith only [show (c/2-c)^2+(0-0)^2 = (c/2)^2 by ring]
    · rw [norm_sq (c/2) 0 x y]; nlinarith only [hq,hx,not_lt.mp acute]

theorem enclosing_disc {a b c : ℝ} (ha : 0 < a) (hab : a ≤ b) (hbc : b ≤ c) (ht : c < a+b) :
    ∃ q o : ℂ, ‖(c : ℂ)-q‖ = a ∧ ‖q‖ = b ∧
      dist o 0 ≤ P2M.R116.discRadius a b c ∧ dist o (c : ℂ) ≤ P2M.R116.discRadius a b c ∧
      dist o q ≤ P2M.R116.discRadius a b c := by
  obtain ⟨q,o,hq,hb,h₁,h₂,h₃,_⟩ := enclosing_disc_data ha hab hbc ht
  exact ⟨q,o,hq,hb,h₁,h₂,h₃⟩

open scoped InnerProductSpace

/-- The piecewise expression is attained and is the least feasible radius
for a triangle with the prescribed three side lengths. -/
theorem least_disc_radius {a b c : ℝ} (ha : 0 < a) (hab : a ≤ b) (hbc : b ≤ c) (ht : c < a+b) :
    ∃ q : ℂ, ‖(c:ℂ)-q‖ = a ∧ ‖q‖ = b ∧
      IsLeast {r : ℝ | ∃ z : ℂ, dist z 0 ≤ r ∧ dist z (c:ℂ) ≤ r ∧ dist z q ≤ r}
        (P2M.R116.discRadius a b c) := by
  obtain ⟨q,o,hq,hb,h₀,h₁,h₂,_,cert⟩ := enclosing_disc_data ha hab hbc ht
  refine ⟨q,hq,hb,⟨o,h₀,h₁,h₂⟩,?_⟩
  rintro r ⟨z,hz₀,hz₁,hz₂⟩
  let R := P2M.R116.discRadius a b c
  have hR : 0 ≤ R := (dist_nonneg.trans h₀)
  have hr : 0 ≤ r := (dist_nonneg.trans hz₀)
  have hc := (ha.trans_le hab).trans_le hbc
  by_cases ac : c^2 < a^2+b^2
  · obtain ⟨u,v,w,hu,hv,hw,sum,centre,reach₀,reach₁,reach₂⟩ := cert ac
    let D := ‖z-o‖^2+R^2-r^2
    have point (x : ℂ) (reach : ‖x-o‖ = R) (bound : dist z x ≤ r) :
        D ≤ 2*⟪z-o,x-o⟫_ℝ := by
      have H := norm_sub_sq_real (z-o) (x-o)
      rw [show (z-o)-(x-o)=z-x by abel,reach] at H
      rw [dist_eq_norm] at bound
      dsimp only [D]
      linarith only [H,pow_le_pow_left₀ (norm_nonneg _) bound 2]
    have bal : u • ((0:ℂ)-o) + v • ((c:ℂ)-o) + w • (q-o) = 0 := calc
      _ = v • (c:ℂ) + w • q - (u+v+w) • o := by simp only [smul_sub,smul_zero,add_smul]; abel
      _ = 0 := by rw [centre,sum,one_smul,sub_self]
    have H := congrArg (fun x : ℂ => ⟪z-o,x⟫_ℝ) bal
    simp only [inner_add_right,real_inner_smul_right,inner_zero_right] at H
    have h : D ≤ 0 := by
      have total : u*D+v*D+w*D = D := by rw [← add_mul,← add_mul,sum,one_mul]
      nlinarith only [H,total,mul_le_mul_of_nonneg_left (point 0 (by simpa using reach₀) hz₀) hu,
        mul_le_mul_of_nonneg_left (point c reach₁ hz₁) hv,mul_le_mul_of_nonneg_left (point q reach₂ hz₂) hw]
    exact (sq_le_sq₀ hR hr).mp (by dsimp [D] at h; linarith only [h,sq_nonneg ‖z-o‖])
  · rw [show P2M.R116.discRadius a b c = c/2 from ite_eq_right ac]
    have H := dist_triangle (0:ℂ) z (c:ℂ)
    rw [dist_zero_left,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hc,dist_comm 0 z] at H
    linarith only [H,hz₀,hz₁]

end OM.Formats
