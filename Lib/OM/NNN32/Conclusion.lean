import Lib.OM.NNN32.CheapPrices
import Lib.OM.NNN32.MatchingWires
import Lib.OM.NNN32.Dichotomy

/-! # Spectral comparison, the common-limit dichotomy, and its finite test -/

namespace OM.NNN32

theorem proof_R113_20 : S_R113_20 := spectral_of_price_spaces proof_R113_18

theorem proof_R113_22 : S_R113_22 := dichotomy_of_comparison proof_R113_20

theorem proof_R113_23 : S_R113_23 := finite_test_of_dichotomy proof_R113_22

end OM.NNN32
