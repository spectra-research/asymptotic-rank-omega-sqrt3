import Lib.OM.NNN11.InnerFinite

/-! Powers of the same rectangular tensor remove the finite constant.
The resulting bound applies to every residual tensor with the specified dimensions. -/
noncomputable section
open scoped BigOperators Classical
namespace OM.NNN11
open CoordinateTensor OM.NNN.Raw Network
open ExtractionAB (X)
open Foundations.PairUnitExponents Foundations.OrientationTransport Lib.E.RectangularSpectrum
set_option maxHeartbeats 2000000

def wordPowerEquiv (q m : ℕ) : X (q * m) ≃ (Fin q → X m) :=
  Fintype.equivOfCardEq (by simp [X, ← pow_mul, Nat.mul_comm])

theorem rect_spectral (m H : ℕ) (hcone : 5 * H ≤ m) (φ : PolMul.Spectral ℂ)
    (t : Fin 3 → ℝ) (ht : ∀ i, t i ∈ Set.Icc (1 / 4 : ℝ) 1)
    (hθ : ∀ i, theta φ i ≤ t i) (hs : t 0 + t 1 + t 2 = (9 : ℝ) / 4)
    (T : Tensor ℂ (X m) (X (m - H)) (X (m - H))) :
    value φ T ≤ (2 : ℝ) ^ (m * innerF (t 0) - H * innerG (t 0)) := by
  let a : ℝ := m * innerF (t 0) - H * innerG (t 0)
  have hp (q : ℕ) : value φ T ^ q ≤ 2 * ((2 : ℝ) ^ a) ^ q := by
    have hq : 5 * (q * H) ≤ q * m := by nlinarith [Nat.mul_le_mul_left q hcone]
    let em := wordPowerEquiv q m
    let es : X (q * m - q * H) ≃ (Fin q → X (m - H)) :=
      (Equiv.cast (congrArg X (Nat.mul_sub_left_distrib q m H).symm)).trans (wordPowerEquiv q (m - H))
    have hb := rect_finite (q * m) (q * H) hq φ t ht hθ hs
      (fun xx yy zz => ordered (D := Fin q) T (em xx) (es yy) (es zz))
    have hv := value_reindex φ (ordered (D := Fin q) T) em es es
    rw [value_ordered_fin] at hv
    rw [hv] at hb
    apply hb.trans_eq
    congr 1
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    dsimp [a]
    push_cast
    ring
  by_contra hn
  have hv : 0 < (2 : ℝ) ^ a := by positivity
  have hratio : 1 < value φ T / (2 : ℝ) ^ a := (one_lt_div hv).2 (lt_of_not_ge hn)
  obtain ⟨q, hq⟩ := pow_unbounded_of_one_lt (2 : ℝ) hratio
  have hle : (value φ T / (2 : ℝ) ^ a) ^ q ≤ 2 := by
    rw [div_pow]
    exact (div_le_iff₀ (pow_pos hv q)).2 (hp q)
  exact (not_lt_of_ge hle) hq

theorem rect_spectral_A {I J K : Type} [Fintype I] [Fintype J] [Fintype K]
    (m H : ℕ) (hcone : 5 * H ≤ m)
    (hi : Fintype.card I = 2 ^ m) (hj : Fintype.card J = 2 ^ (m - H))
    (hk : Fintype.card K = 2 ^ (m - H))
    (φ : PolMul.Spectral ℂ) (t : Fin 3 → ℝ) (ht : ∀ i, t i ∈ Set.Icc (1 / 4 : ℝ) 1)
    (hθ : ∀ i, theta φ i ≤ t i) (hs : t 0 + t 1 + t 2 = (9 : ℝ) / 4)
    (T : Tensor ℂ I J K) : value φ T ≤ (2 : ℝ) ^ (m * innerF (t 0) - H * innerG (t 0)) := by
  let ei : X m ≃ I := Fintype.equivOfCardEq (by simp [X, hi])
  let ej : X (m - H) ≃ J := Fintype.equivOfCardEq (by simp [X, hj])
  let ek : X (m - H) ≃ K := Fintype.equivOfCardEq (by simp [X, hk])
  have hb := rect_spectral m H hcone φ t ht hθ hs (fun x y z => T (ei x) (ej y) (ek z))
  rwa [value_reindex] at hb

theorem rect_spectral_B {I J K : Type} [Fintype I] [Fintype J] [Fintype K]
    [Nonempty I] [Nonempty J] [Nonempty K]
    (m H : ℕ) (hcone : 5 * H ≤ m)
    (hi : Fintype.card I = 2 ^ (m - H)) (hj : Fintype.card J = 2 ^ m)
    (hk : Fintype.card K = 2 ^ (m - H))
    (φ : PolMul.Spectral ℂ) (t : Fin 3 → ℝ) (ht : ∀ i, t i ∈ Set.Icc (1 / 4 : ℝ) 1)
    (hθ : ∀ i, theta φ i ≤ t i) (hs : t 0 + t 1 + t 2 = (9 : ℝ) / 4)
    (T : Tensor ℂ I J K) : value φ T ≤ (2 : ℝ) ^ (m * innerF (t 1) - H * innerG (t 1)) := by
  let ψ := pullPoint (pullPoint φ (rot 1)) (rot 0)
  let v : Fin 3 → ℝ := ![t 1, t 2, t 0]
  have hv (i) : v i ∈ Set.Icc (1 / 4 : ℝ) 1 := by
    fin_cases i <;> first | exact ht 1 | exact ht 2 | exact ht 0
  have hvθ (i) : theta ψ i ≤ v i := by
    simp only [ψ, theta_legReindex]
    fin_cases i <;> first | exact hθ 1 | exact hθ 2 | exact hθ 0
  have hvs : v 0 + v 1 + v 2 = (9 : ℝ) / 4 := by change t 1 + t 2 + t 0 = _; linarith
  have hb := rect_spectral_A m H hcone hj hk hi ψ v hv hvθ hvs (swap02 (swap12 T))
  rw [value_swap02, value_swap12] at hb
  exact hb

theorem rect_spectral_C {I J K : Type} [Fintype I] [Fintype J] [Fintype K]
    [Nonempty I] [Nonempty J] [Nonempty K]
    (m H : ℕ) (hcone : 5 * H ≤ m)
    (hi : Fintype.card I = 2 ^ (m - H)) (hj : Fintype.card J = 2 ^ (m - H))
    (hk : Fintype.card K = 2 ^ m)
    (φ : PolMul.Spectral ℂ) (t : Fin 3 → ℝ) (ht : ∀ i, t i ∈ Set.Icc (1 / 4 : ℝ) 1)
    (hθ : ∀ i, theta φ i ≤ t i) (hs : t 0 + t 1 + t 2 = (9 : ℝ) / 4)
    (T : Tensor ℂ I J K) : value φ T ≤ (2 : ℝ) ^ (m * innerF (t 2) - H * innerG (t 2)) := by
  let ψ := pullPoint φ (rot 0)
  let v : Fin 3 → ℝ := ![t 2, t 1, t 0]
  have hv (i) : v i ∈ Set.Icc (1 / 4 : ℝ) 1 := by
    fin_cases i <;> first | exact ht 2 | exact ht 1 | exact ht 0
  have hvθ (i) : theta ψ i ≤ v i := by
    simp only [ψ, theta_legReindex]
    fin_cases i <;> first | exact hθ 2 | exact hθ 1 | exact hθ 0
  have hvs : v 0 + v 1 + v 2 = (9 : ℝ) / 4 := by change t 2 + t 1 + t 0 = _; linarith
  have hb := rect_spectral_A m H hcone hk hj hi ψ v hv hvθ hvs (swap02 T)
  rw [value_swap02] at hb
  exact hb

end OM.NNN11
