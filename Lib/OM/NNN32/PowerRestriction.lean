import Lib.OM.NNN32.Defs
import Lib.OM.NNN32.WordPower
import Lib.OM.NNN30.Net.Core

/-! # Restricting powers of a finite crossing expansion -/

noncomputable section

namespace OM.NNN32

open Semicontinuity

abbrev crossing (D : ℕ+) := matching D 0 3 1 2

def weight {d : Fin 4 → ℕ+} (T : KTensor ℂ d) : ℝ :=
  Real.sqrt ((flatRank T {0,1} : ℝ) * (flatRank T {0,2} : ℝ))

lemma flatRank_pos {k : ℕ} {d : Fin k → ℕ+} {T : KTensor ℂ d} (hT : T ≠ 0)
    (I : Finset (Fin k)) : 0 < flatRank T I := by
  apply OM.NNN30.Net.rank_pos_of_ne_zero
  intro h
  apply hT
  funext x
  have he := congrFun (congrFun h (fun i => x i.1)) (fun j => x j.1)
  simpa [flattenMatrix] using he

lemma one_le_weight {d : Fin 4 → ℕ+} {T : KTensor ℂ d} (hT : T ≠ 0) : 1 ≤ weight T := by
  have a : (1 : ℝ) ≤ flatRank T {0,1} := by exact_mod_cast flatRank_pos hT {0,1}
  have b : (1 : ℝ) ≤ flatRank T {0,2} := by exact_mod_cast flatRank_pos hT {0,2}
  simpa [weight] using Real.sqrt_le_sqrt (one_le_mul_of_one_le_of_one_le a b)

@[simp] lemma weight_zero (d : Fin 4 → ℕ+) : weight (0 : KTensor ℂ d) = 0 := by
  change Real.sqrt (((0 : Matrix _ _ ℂ).rank : ℝ) * ((0 : Matrix _ _ ℂ).rank : ℝ)) = 0
  simp

lemma crossing_ne_zero (D : ℕ+) : crossing D ≠ 0 := by
  intro h
  have := congrFun h (fun _ => ⟨0, D.2⟩)
  simp [crossing, matching] at this

lemma one_le_cost {D : ℕ+} {c : ℝ} (hc : c ∈ expansionCosts (crossing D)) : 1 ≤ c := by
  classical
  obtain ⟨m, B, hB, rfl⟩ := hc
  obtain ⟨i, hi⟩ : ∃ i, B i ≠ 0 := by
    by_contra! h
    exact crossing_ne_zero D (by simpa [h] using hB.symm)
  exact (one_le_weight hi).trans
    (Finset.single_le_sum (f := fun j => weight (B j)) (fun j _ => Real.sqrt_nonneg _)
      (Finset.mem_univ i))

/-- Pull back the coefficient array along one index map at each leg. -/
def pull {k : ℕ} {d e : Fin k → ℕ+} (f : ∀ i, Fin (e i) → Fin (d i))
    (T : KTensor ℂ d) : KTensor ℂ e := fun x => T (fun i => f i (x i))

lemma flatRank_pull_le {k : ℕ} {d e : Fin k → ℕ+} (f : ∀ i, Fin (e i) → Fin (d i))
    (T : KTensor ℂ d) (I : Finset (Fin k)) : flatRank (pull f T) I ≤ flatRank T I := by
  let row := fun (x : ∀ i : {i // i ∈ I}, Fin (e i.1)) (i : {i // i ∈ I}) => f i.1 (x i)
  let col := fun (x : ∀ i : {i // i ∉ I}, Fin (e i.1)) (i : {i // i ∉ I}) => f i.1 (x i)
  have he : flattenMatrix (pull f T) I = (flattenMatrix T I).submatrix row col := by
    funext x y
    apply congrArg T
    funext i
    by_cases hi : i ∈ I <;> simp [row, col, hi]
  unfold flatRank
  rw [he]
  exact (flattenMatrix T I).rank_submatrix_le row col

lemma weight_pull_le {d e : Fin 4 → ℕ+} (f : ∀ i, Fin (e i) → Fin (d i))
    (T : KTensor ℂ d) : weight (pull f T) ≤ weight T := by
  apply Real.sqrt_le_sqrt
  exact_mod_cast Nat.mul_le_mul (flatRank_pull_le f T {0,1}) (flatRank_pull_le f T {0,2})

lemma power_side (D : ℕ+) (n : ℕ) (i : Fin 4) :
    (kronPowFormat (fun _ : Fin 4 => D) n i : ℕ) = (D : ℕ) ^ (n+1) := by
  induction n with
  | zero => simp [kronPowFormat]
  | succ n ih => simp [kronPowFormat, PNat.mul_coe, ih, pow_succ]

private lemma div_mod_eq {d x y : ℕ} : x / d = y / d ∧ x % d = y % d ↔ x = y := by
  constructor
  · rintro ⟨h,k⟩
    calc
      x = x % d + d * (x / d) := (Nat.mod_add_div x d).symm
      _ = y % d + d * (y / d) := by rw [h,k]
      _ = y := Nat.mod_add_div y d
  · rintro rfl
    exact ⟨rfl,rfl⟩

lemma crossing_power_apply (D : ℕ+) (n : ℕ)
    (x : ∀ i, Fin (kronPowFormat (fun _ : Fin 4 => D) n i)) :
    kronPowNat (crossing D) n x =
      if (x 0).val = (x 3).val ∧ (x 1).val = (x 2).val then 1 else 0 := by
  induction n with
  | zero => simp [kronPowNat, crossing, matching, Fin.ext_iff]
  | succ n ih =>
    rw [kronPowNat, kroneckerTensor, ih]
    change (if (x 0).val / D = (x 3).val / D ∧ (x 1).val / D = (x 2).val / D
      then (1 : ℂ) else 0) *
        (if _ ∧ _ then 1 else 0) = _
    simp only [Fin.ext_iff]
    change _ * (if (x 0).val % D = (x 3).val % D ∧ (x 1).val % D = (x 2).val % D
      then (1 : ℂ) else 0) = _
    by_cases h : (x 0).val = (x 3).val ∧ (x 1).val = (x 2).val
    · simp [h.1, h.2]
    · split_ifs <;> simp_all [← div_mod_eq (d := (D : ℕ)) (x := (x 0).val) (y := (x 3).val),
        ← div_mod_eq (d := (D : ℕ)) (x := (x 1).val) (y := (x 2).val)]

def powerIndex {D E : ℕ+} (n : ℕ) (hE : (E : ℕ) ≤ (D : ℕ) ^ (n+1))
    (i : Fin 4) (x : Fin (E : ℕ)) : Fin (kronPowFormat (fun _ : Fin 4 => D) n i) :=
  ⟨x.val, (power_side D n i).symm ▸ x.isLt.trans_le hE⟩

lemma pull_crossing_power {D E : ℕ+} (n : ℕ) (hE : (E : ℕ) ≤ (D : ℕ) ^ (n+1)) :
    pull (powerIndex n hE) (kronPowNat (crossing D) n) = crossing E := by
  funext x
  simp [pull, crossing_power_apply, powerIndex, crossing, matching, Fin.ext_iff]

/-- A side at most `D^(n+1)` inherits the grouped expansion. -/
theorem grouped_crossing {D E : ℕ+} {m : ℕ} (B : Fin m → KTensor ℂ (fun _ : Fin 4 => D))
    (hB : ∑ j, B j = crossing D) (n : ℕ) (hE : (E : ℕ) ≤ (D : ℕ) ^ (n+1)) :
    ∃ G : Fin ((n+2)^m) → KTensor ℂ (fun _ : Fin 4 => E),
      (∑ j, G j) = crossing E ∧ ∀ j, weight (G j) ≤ (∑ i, weight (B i)) ^ (n+1) := by
  classical
  let f := powerIndex n hE
  obtain ⟨A, hs, hw⟩ := exists_grouped_kronPow B {0,1} {0,2} n
  let eqv := Fintype.equivFinOfCardEq (α := Fin m → Fin (n+2)) (show _ = (n+2)^m by simp)
  refine ⟨fun j => pull f (A (eqv.symm j)), ?_, fun j => (weight_pull_le f _).trans (hw _)⟩
  rw [eqv.symm.sum_comp (fun a => pull f (A a))]
  funext x
  have h := congrFun hs (fun i => f i (x i))
  rw [hB, crossing_power_apply] at h
  simpa [pull, crossing, matching, f, powerIndex, Fin.ext_iff] using h

end OM.NNN32
