import Lib.OM.NNN30.Net.Level0
import Lib.OM.NNN30.Net.Tower
import PLATFORM.Statements.«R111.2»

namespace OM.NNN30.Net

/-- Start the tower at the minimal prices below the four-site bound. -/
theorem metric_of (crossing : S_R108_3) : S_R111_2 := by
  intro φ
  obtain ⟨d, hd, ho, h12, h02, h01⟩ := initial_minimal φ
  let base : {d : Lv 0 → Lv 0 → ℝ // MinAdm φ (τL 0) d} := ⟨d, hd⟩
  exact ⟨Tm, dX crossing base, Tm.node, fun i => Tm.leaf i.castSucc, Tm.leaf 3,
    dX_self crossing base, dX_symm crossing base, dX_tri crossing base,
    dX_node_row crossing base, dX_node_col crossing base, dX_node_self crossing base,
    dX_quad crossing base, dX_fermat crossing base, ho, h12, h02, h01⟩

end OM.NNN30.Net

