import Lib.OM.NNN34.FinitePrices
import Lib.OM.NNN34.PlanePrices
import Lib.OM.NNN34.Saturation

/-! # The exponent dichotomy and its specialization at omega two -/

namespace OM.NNN34

theorem proof_R114_19 : S_R114_19 := plane_of_finite_prices proof_R114_18

theorem proof_R114_21 : S_R114_21 := saturation_of_plane proof_R114_19

theorem proof_R114_22 : S_R114_22 := rank_witness_of_saturation proof_R114_21

theorem proof_R114_25 : S_R114_25 := upper_case_of_witness proof_R114_22

theorem proof_NNN_34 : S_NNN_34 := dichotomy_of_upper_case proof_R114_25

theorem proof_NNN_35 : S_NNN_35 := conjecture_of_dichotomy proof_NNN_34

end OM.NNN34

