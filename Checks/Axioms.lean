import Main
import Lib.OM.NNN36.Defs

-- The format supremum of Theorem 1.3 agrees with its definition in the statement files.
example : P2M.R115.formatRankSup = OM.NNN36.formatRankSup := rfl

-- The normalized apex of Theorem 1.3 agrees with its definition in the statement files.
example : P2M.R115.normalizedApex = OM.NNN36.normalizedApex := rfl

-- The exponent and enclosing-disc radius in Theorem 1.6 agree with their definitions in the statement files.
example : P2M.R116.formatBeta = OM.Formats.formatBeta := rfl
example : P2M.R116.discRadius = OM.Formats.discRadius := rfl

#print axioms AsymptoticRank.asympRank_le_pow_omega_div_sqrt3
#print axioms AsymptoticRank.formatRank_eq_product_of_wide
#print axioms AsymptoticRank.log_formatRank_le_triangle_min
#print axioms AsymptoticRank.log_formatRank_le_omegaRect_everywhere
#print axioms AsymptoticRank.formatRank_eq_largest_of_apex_bound
#print axioms AsymptoticRank.formatRank_eq_largest_of_split_bound
#print axioms AsymptoticRank.formatRank_eq_largest_of_isosceles
#print axioms AsymptoticRank.sumsOfSquares_exponent_dichotomy
#print axioms AsymptoticRank.formatBeta_cube_eq_beta
#print axioms AsymptoticRank.cube_exponent_dichotomy
#print axioms AsymptoticRank.formatExponent_eq_rectangular_of_gamma_eq_one
#print axioms AsymptoticRank.asympRestricts_matMul_of_gamma_eq_one
#print axioms AsymptoticRank.two_mul_discRadius_le_formatExponent
#print axioms AsymptoticRank.formatExponent_eq_two_mul_discRadius_of_omega_eq_two
#print axioms AsymptoticRank.gamma_eq_one_iff_formatExponent_334_eq_four
#print axioms AsymptoticRank.formatExponent_334_eq_four_iff_formatRank_eq_fourth_power
#print axioms AsymptoticRank.nine_div_sqrt_five_le_formatExponent_334
#print axioms AsymptoticRank.asympRank_le_pow_three_sqrt3_div_four
#print axioms AsymptoticRank.asympRank_le_pow_two_div_sqrt3_of_omega_eq_two
#print axioms AsymptoticRank.asympRank_le_pow_nine_eighths_of_witness
#print axioms AsymptoticRank.asympRank_le_side_of_witness_of_omega_eq_two
#print axioms AsymptoticRank.asympRank_conjecture_iff_gamma_eq_one_of_omega_eq_two
