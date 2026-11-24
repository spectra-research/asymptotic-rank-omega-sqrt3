# Asymptotic rank via matrix multiplication and sums of squares

Lean 4 formalisation of the main results of the paper by Jeroen Zuiddam. All tensors are over ℂ.
The theorems are in `Main.lean`, namespace `AsymptoticRank`.
The paper is [`paper/results.pdf`](paper/results.pdf), with its source in `paper/results.tex`.

| Paper | Lean name |
| --- | --- |
| Theorem 1.2: every T ∈ ℂⁿ⊗ℂⁿ⊗ℂⁿ has asymptotic rank at most n^{ω/√3} | `asympRank_le_pow_omega_div_sqrt3` |
| Theorem 1.3(i)–(iv): other formats | `formatRank_eq_product_of_wide`, `log_formatRank_le_omegaRect_everywhere`, `formatRank_eq_largest_of_split_bound`, `formatRank_eq_largest_of_isosceles` |
| Theorem 1.4: γ ∈ {1, √2} | `sumsOfSquares_exponent_dichotomy` |
| Theorem 1.5: β = ω/2 if γ = 1, and 2/√3 ≤ β ≤ ω/√3 if γ = √2 | `cube_exponent_dichotomy`, `formatBeta_cube_eq_beta` |
| Theorem 1.6(i)–(ii). Format dichotomy, tensor restriction and equality at ω = 2 | `formatExponent_eq_rectangular_of_gamma_eq_one`, `asympRestricts_matMul_of_gamma_eq_one`, `two_mul_discRadius_le_formatExponent`, `formatExponent_eq_two_mul_discRadius_of_omega_eq_two` |
| Corollary 1.7. The (3,3,4) criterion, its integer-power formulation and the 9/√5 lower bound | `gamma_eq_one_iff_formatExponent_334_eq_four`, `formatExponent_334_eq_four_iff_formatRank_eq_fourth_power`, `nine_div_sqrt_five_le_formatExponent_334` |

The proofs use only the axioms `propext`, `Classical.choice` and `Quot.sound` (see `Checks/Axioms.lean`).

Build: `lake exe cache get && lake build` (Lean `v4.34.1`).

This release is based on a private development repository: Theorems 1.2–1.5 at commit
`72dfd08e9883cc24a7343b0db49daabdd9e178ef` (2026-11-21), and Theorem 1.6 and Corollary 1.7 at commit
`66ae5ab2ea341a19fb009e5c3f42cebc9f4b1ea8` (2026-11-24). `Rect/RankModel/Basic.lean` copies declarations from `github.com/jzuiddam/matrix-mult-exponent`
(see `NOTICE`).

The proofs were developed with the help of large language models.

Copyright 2026 Jeroen Zuiddam.

License: Apache-2.0 (see LICENSE)
