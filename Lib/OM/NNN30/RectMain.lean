import Lib.OM.NNN30.Crossing.Main
import Lib.OM.NNN30.Partition.Main
import Lib.OM.NNN30.Rect

namespace OM.NNN30

/-- The rectangular asymptotic estimate from the finite crossing and partition growth. -/
theorem proof_R108_3 : S_R108_3 :=
  Rect.rect_of Crossing.proof_R108_1 Partition.proof_R108_2

end OM.NNN30

