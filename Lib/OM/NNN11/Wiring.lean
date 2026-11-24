import Lib.OM.NNN11.Tiles

/-! Literal equality extraction from a partial permutation, with an arbitrary
joint operator on its complement. No tensor coefficient is factored by digits. -/
noncomputable section
open scoped BigOperators Classical
namespace OM.NNN11.Wiring
set_option maxHeartbeats 1000000

variable {S E : Type} (σ : S ≃ S) (active role : S → Prop)

def Selected (s : S) : Prop := active s ∧ ¬ role s ∧ role (σ s)

def Relation (r c : S → E) : Prop := ∀ s, active s → r s = c (σ s)

def Equalities (r c : S → E) : Prop := ∀ s, Selected σ active role s → r s = c (σ s)

def eraseRow (e : E) (r : S → E) : S → E :=
  fun s => if Selected σ active role s then e else r s

def eraseCol (e : E) (c : S → E) : S → E :=
  fun s => if Selected σ active role (σ.symm s) then e else c s

lemma relation_erase_iff (e : E) (r c : S → E) :
    Relation σ active r c ↔ Equalities σ active role r c ∧
      Relation σ active (eraseRow σ active role e r) (eraseCol σ active role e c) := by
  constructor
  · intro h
    refine ⟨fun s hs => h s hs.1, ?_⟩
    intro s hs
    by_cases hsel : Selected σ active role s
    · simp [eraseRow, eraseCol, hsel]
    · simpa [eraseRow, eraseCol, hsel] using! h s hs
  · rintro ⟨he, h⟩ s hs
    by_cases hsel : Selected σ active role s
    · exact he s hsel
    · simpa [eraseRow, eraseCol, hsel] using! h s hs

def delta (r c : S → E) : ℂ := if Relation σ active r c then 1 else 0

theorem delta_extract (e : E) (r c : S → E) :
    delta σ active r c = if Equalities σ active role r c then
      delta σ active (eraseRow σ active role e r) (eraseCol σ active role e c) else 0 := by
  unfold delta
  rw [relation_erase_iff σ active role e]
  split_ifs <;> simp_all

lemma eraseRow_coeff (e : E) (r : S → E) {s : S} (h : role s) :
    eraseRow σ active role e r s = r s := by
  simp [eraseRow, Selected, h]

lemma eraseCol_coeff (e : E) (c : S → E) {s : S} (h : ¬ role s) :
    eraseCol σ active role e c s = c s := by
  simp [eraseCol, Selected, h]

def complement (r : S → E) : {s // ¬ active s} → E := fun s => r s.1

lemma complement_eraseRow (e : E) (r : S → E) :
    complement active (eraseRow σ active role e r) = complement active r := by
  funext s
  simp [complement, eraseRow, Selected, s.property]

lemma complement_eraseCol (stable : ∀ s, active (σ s) ↔ active s)
    (e : E) (c : S → E) :
    complement active (eraseCol σ active role e c) = complement active c := by
  funext s
  have hn : ¬ active (σ.symm s.1) := by
    intro h
    exact s.property (by simpa using! (stable (σ.symm s.1)).2 h)
  simp [complement, eraseCol, Selected, hn]

/-- K is an arbitrary function of both complementary endpoint words; in
particular it need not be a product over physical bonds or digit positions. -/
def joint (K : ({s // ¬ active s} → E) → ({s // ¬ active s} → E) → ℂ)
    (r c : S → E) : ℂ :=
  delta σ active r c * K (complement active r) (complement active c)

theorem joint_extract (stable : ∀ s, active (σ s) ↔ active s)
    (e : E) (K : ({s // ¬ active s} → E) → ({s // ¬ active s} → E) → ℂ)
    (r c : S → E) :
    joint σ active K r c = if Equalities σ active role r c then
      joint σ active K (eraseRow σ active role e r) (eraseCol σ active role e c) else 0 := by
  unfold joint
  rw [complement_eraseRow, complement_eraseCol σ active role stable,
    delta_extract σ active role e]
  split_ifs <;> simp

/-- Finite linear combinations preserve the same extracted equality. This
includes internal summations and any other coefficients in the network. -/
theorem sum_joint_extract {D : Type} [Fintype D]
    (stable : ∀ s, active (σ s) ↔ active s) (e : E)
    (K : D → ({s // ¬ active s} → E) → ({s // ¬ active s} → E) → ℂ)
    (r c : D → S → E) (a : D → ℂ) (P : Prop)
    (hP : ∀ d, Equalities σ active role (r d) (c d) ↔ P) :
    (∑ d, joint σ active (K d) (r d) (c d) * a d) = if P then
      ∑ d, joint σ active (K d) (eraseRow σ active role e (r d))
        (eraseCol σ active role e (c d)) * a d else 0 := by
  by_cases hp : P
  · rw [if_pos hp]
    apply Finset.sum_congr rfl
    intro d _
    rw [joint_extract σ active role stable e, if_pos ((hP d).2 hp)]
  · rw [if_neg hp]
    apply Finset.sum_eq_zero
    intro d _
    rw [joint_extract σ active role stable e, if_neg (fun h => hp ((hP d).1 h)), zero_mul]

end OM.NNN11.Wiring
