import Lib.OM.NNN11.Network

/-! Transport raw spectral values between extensionally identical finite
enumerations without reducing enormous function-space enumerations. -/
noncomputable section
namespace OM.NNN11
open CoordinateTensor OM.NNN.Raw

theorem value_change_fintypes {I J K : Type} (φ : PolMul.Spectral ℂ) (T : Tensor ℂ I J K)
    (i i' : Fintype I) (j j' : Fintype J) (k k' : Fintype K) :
    @value I J K φ i j k T = @value I J K φ i' j' k' T := by
  cases Subsingleton.elim i i'
  cases Subsingleton.elim j j'
  cases Subsingleton.elim k k'
  rfl

theorem value_le_change_fintypes {I J K : Type} (φ : PolMul.Spectral ℂ) (T : Tensor ℂ I J K)
    {i i' : Fintype I} {j j' : Fintype J} {k k' : Fintype K} {B : ℝ}
    (h : @value I J K φ i j k T ≤ B) : @value I J K φ i' j' k' T ≤ B := by
  rw [← value_change_fintypes φ T i i' j j' k k']
  exact h

end OM.NNN11
