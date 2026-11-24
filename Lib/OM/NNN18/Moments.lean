import Lib.OM.NNN18.MomentCore
import Lib.OM.NNN18.Basic

/-!
For each track and kind (0 retained, 1 ordinary side, 2 packed side) the complete moment
`ell` lies below the quadratic majorant `Track.Lmaj` on `|z - z0| ≤ 2` (and `z ≥ -1/2`
for the packed kind).  The centre certificates are rational and kernel-checked.
-/

noncomputable section
namespace OM.NNN18

theorem U_bracket0 {z : ℝ} (hz : |z - (U.z0 0 : ℝ)| ≤ 2) :
    ell z ≤ U.Lmaj 0 z := by
  have h := bracket_of_cert (min z (U.z0 0 : ℝ)) (A0 := U.A0 0)
    (A1 := U.A1 0) (K := Track.K 0) 2 1 (1 / 4 : ℚ) (41306041 / 50000000 : ℚ)
    (fun w _ => by simpa [Track.K] using ell_second_le w)
    (by norm_num [Track.z0, U]) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel) (by decide +kernel) (min_le_right _ _) (min_le_left _ _) hz
  simpa [Track.Lmaj] using h

theorem U_bracket1 {z : ℝ} (hz : |z - (U.z0 1 : ℝ)| ≤ 2) :
    ell z ≤ U.Lmaj 1 z := by
  have h := bracket_of_cert (min z (U.z0 1 : ℝ)) (A0 := U.A0 1)
    (A1 := U.A1 1) (K := Track.K 1) 0 0 (7437 / 10000 : ℚ) (6578471 / 10000000 : ℚ)
    (fun w _ => by simpa [Track.K] using ell_second_le w)
    (by norm_num [Track.z0, U]) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel) (by decide +kernel) (min_le_right _ _) (min_le_left _ _) hz
  simpa [Track.Lmaj] using h

theorem U_bracket2 {z : ℝ} (hz : |z - (U.z0 2 : ℝ)| ≤ 2) (hz2 : -1 / 2 ≤ z) :
    ell z ≤ U.Lmaj 2 z := by
  have h := bracket_of_cert (-1 / 2) (A0 := U.A0 2)
    (A1 := U.A1 2) (K := Track.K 2) 0 0 (14874 / 17479 : ℚ) (37461383 / 50000000 : ℚ)
    (fun w hw => by simpa [Track.K] using ell_second_le_packed hw)
    (by norm_num [Track.z0, U]) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel) (by decide +kernel) (by norm_num [Track.z0, U]) hz2 hz
  simpa [Track.Lmaj] using h

theorem C_bracket0 {z : ℝ} (hz : |z - (C.z0 0 : ℝ)| ≤ 2) :
    ell z ≤ C.Lmaj 0 z := by
  have h := bracket_of_cert (min z (C.z0 0 : ℝ)) (A0 := C.A0 0)
    (A1 := C.A1 0) (K := Track.K 0) 2 1 (0 : ℚ) (16301917 / 25000000 : ℚ)
    (fun w _ => by simpa [Track.K] using ell_second_le w)
    (by norm_num [Track.z0, C]) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel) (by decide +kernel) (min_le_right _ _) (min_le_left _ _) hz
  simpa [Track.Lmaj] using h

theorem C_bracket1 {z : ℝ} (hz : |z - (C.z0 1 : ℝ)| ≤ 2) :
    ell z ≤ C.Lmaj 1 z := by
  have h := bracket_of_cert (min z (C.z0 1 : ℝ)) (A0 := C.A0 1)
    (A1 := C.A1 1) (K := Track.K 1) 0 0 (163 / 250 : ℚ) (28947347 / 50000000 : ℚ)
    (fun w _ => by simpa [Track.K] using ell_second_le w)
    (by norm_num [Track.z0, C]) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel) (by decide +kernel) (min_le_right _ _) (min_le_left _ _) hz
  simpa [Track.Lmaj] using h

theorem C_bracket2 {z : ℝ} (hz : |z - (C.z0 2 : ℝ)| ≤ 2) (hz2 : -1 / 2 ≤ z) :
    ell z ≤ C.Lmaj 2 z := by
  have h := bracket_of_cert (-1 / 2) (A0 := C.A0 2)
    (A1 := C.A1 2) (K := Track.K 2) 0 0 (978 / 1163 : ℚ) (37036063 / 50000000 : ℚ)
    (fun w hw => by simpa [Track.K] using ell_second_le_packed hw)
    (by norm_num [Track.z0, C]) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel) (by decide +kernel) (by norm_num [Track.z0, C]) hz2 hz
  simpa [Track.Lmaj] using h

end OM.NNN18
