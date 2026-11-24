import Lib.OM.Formats.Disc
import Lib.OM.NNN34.Insertion

/-! # A planar work certificate for the circumradius of an acute triangle -/

noncomputable section
open scoped InnerProductSpace
namespace OM.Formats

open NNN34

theorem acute_witness {a b c : ℝ} (ha : 0 < a) (hab : a ≤ b) (hbc : b ≤ c) (ht : c < a+b)
    (acute : c^2 < a^2+b^2) :
    ∃ p q l r : ℂ, ‖p‖ = a ∧ ‖q‖ = b ∧ ‖p+q‖ = c ∧ 0 < ‖p-q‖ ∧
      0 < perimeter3 dist l r 0 ∧
      ⟪p,l⟫_ℝ + ⟪q,r⟫_ℝ = P2M.R116.discRadius a b c * perimeter3 dist l r 0 := by
  let R := P2M.R116.discRadius a b c
  have hc := (ha.trans_le hab).trans_le hbc
  obtain ⟨z,O,hz,hb,_,_,_,him,cert⟩ := enclosing_disc_data ha hab hbc ht
  obtain ⟨u,v,w,hu,hv,hw,sum,centre,h₀,h₁,h₂⟩ := cert acute
  let e₀ := -O
  let e₁ := (c:ℂ)-O
  let e₂ := z-O
  let l := -(v • e₁)
  let r := u • e₀
  have reach₀ : ‖e₀‖ = R := (norm_neg O).trans h₀
  have reach₁ : ‖e₁‖ = R := h₁
  have reach₂ : ‖e₂‖ = R := h₂
  have normc : ‖(c:ℂ)‖ = c := by rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hc]
  have hR : 0 < R := by
    have H := norm_sub_le ((c:ℂ)-O) (-O)
    rw [show (c:ℂ)-O - (-O) = (c:ℂ) by abel,normc,norm_neg,h₀,h₁] at H
    dsimp only [R]; linarith only [H,hc]
  have balance : u • e₀ + v • e₁ + w • e₂ = 0 := calc
    _ = v • (c:ℂ) + w • z - (u+v+w) • O := by simp only [e₀,e₁,e₂,smul_neg,smul_sub,add_smul]; abel
    _ = 0 := by rw [centre,sum,one_smul,sub_self]
  have edge : l-r = w • e₂ := by dsimp only [l,r]; linear_combination -balance
  have per : perimeter3 dist l r 0 = R := by
    unfold perimeter3
    rw [dist_zero_left,dist_zero_right,dist_eq_norm,edge]
    simp only [l,r,norm_neg,norm_smul,Real.norm_eq_abs,
      abs_of_nonneg hu,abs_of_nonneg hv,abs_of_nonneg hw,reach₀,reach₁,reach₂]
    linear_combination R*sum
  refine ⟨z-c,-z,l,r,(norm_sub_rev z (c:ℂ)).trans hz,(norm_neg z).trans hb,?_,?_,per.symm ▸ hR,?_⟩
  · rw [show z-(c:ℂ) + -z = -(c:ℂ) by abel,norm_neg,normc]
  · apply norm_pos_iff.mpr
    intro he
    have hi := congrArg Complex.im he
    simp only [Complex.sub_im,Complex.neg_im,Complex.ofReal_im,Complex.zero_im] at hi
    linarith only [hi,him]
  · calc
      _ = ⟪e₀,r⟫_ℝ + ⟪e₁,-l⟫_ℝ + ⟪e₂,l-r⟫_ℝ := by
        simp only [e₀,e₁,e₂,inner_sub_left,inner_sub_right,inner_neg_left,inner_neg_right]; ring
      _ = (u+v+w)*R^2 := by
        rw [edge]
        simp only [r,l,neg_neg,real_inner_smul_right,real_inner_self_eq_norm_sq,reach₀,reach₁,reach₂]
        ring
      _ = _ := by rw [sum,per]; ring

end OM.Formats
