import Foundations.Tensors.Semicontinuity.MaxRankBound
import Mathlib.Basic.Complex.Basic

namespace P2M.R113

/-- Two equality wires of size `D` in a common four-party format. The crossing pairs `0,3` and `1,2`. -/
def matching (D : ℕ+) (i j k l : Fin 4) : Semicontinuity.KTensor ℂ (fun _ : Fin 4 => D) :=
  fun a => if a i = a j ∧ a k = a l then 1 else 0

end P2M.R113
