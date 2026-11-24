import Mathlib

/-! # Wick sums (hafnians) of lists and multisets

`wick β l` pairs the head of `l` with each element of the tail and recurses on the rest: for a
symmetric pairing `β` it is the sum over all perfect matchings of the positions of `l` of the
product of `β` over the pairs.  It is invariant under permutations (`wick_perm`), so it descends
to multisets (`wickM`), with the recursion `wickM_cons`. -/

namespace OM.NNN30.Crossing

open BigOperators

section Wick

variable {α : Type*} {R : Type*} [CommRing R]

/-- Wick sum (hafnian) of a list for the pairing `β`. -/
def wick (β : α → α → R) : List α → R
  | [] => 1
  | a :: l => ∑ i : Fin l.length, β a (l.get i) * wick β (l.eraseIdx i)
termination_by l => l.length
decreasing_by
  simp only [List.length_cons]
  exact Nat.lt_succ_of_le (List.length_eraseIdx_le _ _)

theorem wick_nil (β : α → α → R) : wick β [] = 1 := by rw [wick]

theorem wick_cons (β : α → α → R) (a : α) (l : List α) :
    wick β (a :: l) = ∑ i : Fin l.length, β a (l.get i) * wick β (l.eraseIdx i) := by
  rw [wick]

theorem perm_getElem_cons_eraseIdx (l : List α) (i : ℕ) (h : i < l.length) :
    l.Perm (l[i] :: l.eraseIdx i) := by
  rw [List.eraseIdx_eq_take_drop_succ]
  conv_lhs => rw [← List.take_append_drop i l]
  rw [List.drop_eq_getElem_cons h]
  exact List.perm_middle

theorem sum_fin_get {M : Type*} [AddCommMonoid M] (l : List α) (f : α → M) :
    ∑ i : Fin l.length, f (l.get i) = (l.map f).sum := by
  rw [← List.sum_ofFn]
  congr 1
  have : (List.ofFn fun i : Fin l.length => f (l.get i)) = List.ofFn (f ∘ l.get) := rfl
  rw [this, ← List.map_ofFn, List.ofFn_get]

variable [DecidableEq α]

theorem eraseIdx_perm_erase (l : List α) (i : Fin l.length) :
    (l.eraseIdx i).Perm (l.erase (l.get i)) := by
  have h1 := perm_getElem_cons_eraseIdx l i i.2
  have h2 : l.Perm (l.get i :: l.erase (l.get i)) := List.perm_cons_erase (List.get_mem l i)
  have h3 : (l.get i :: l.eraseIdx i).Perm (l.get i :: l.erase (l.get i)) := by
    simp only [List.get_eq_getElem] at h2 ⊢
    exact h1.symm.trans h2
  exact h3.cons_inv

/-- Sums over ordered pairs of distinct elements of a multiset are symmetric. -/
theorem pair_sum_symm {M : Type*} [AddCommMonoid M] (s : Multiset α) (F : α → α → M) :
    (s.map fun u => ((s.erase u).map fun v => F u v).sum).sum =
      (s.map fun u => ((s.erase u).map fun v => F v u).sum).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a t ih =>
    have h1 : ∀ (G : α → α → M), (t.map fun u => (((a ::ₘ t).erase u).map fun v => G u v).sum) =
        t.map fun u => G u a + ((t.erase u).map fun v => G u v).sum := by
      intro G
      apply Multiset.map_congr rfl
      intro u hu
      rw [Multiset.erase_cons_tail_of_mem hu, Multiset.map_cons, Multiset.sum_cons]
    simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.erase_cons_head]
    rw [h1 (fun u v => F u v), h1 (fun u v => F v u)]
    simp only [Multiset.sum_map_add]
    rw [ih]
    abel

theorem pair_sum_symm_list {M : Type*} [AddCommMonoid M] (l : List α) (F : α → α → M) :
    (l.map fun u => ((l.erase u).map fun v => F u v).sum).sum =
      (l.map fun u => ((l.erase u).map fun v => F v u).sum).sum := by
  have h := pair_sum_symm (l : Multiset α) F
  simp only [Multiset.coe_erase, Multiset.map_coe, Multiset.sum_coe] at h
  exact h

theorem cons_erase_perm (c u : α) (l : List α) (hu : u ∈ l) :
    ((c :: l).erase u).Perm (c :: l.erase u) := by
  by_cases h : c = u
  · subst h
    rw [List.erase_cons_head]
    exact List.perm_cons_erase hu
  · rw [List.erase_cons_tail (by simpa using h)]

end Wick

section Perm

variable {α : Type*} {R : Type*} [CommRing R]
variable (β : α → α → R) (hβ : ∀ u v, β u v = β v u)
include hβ

theorem wick_perm_aux (n : ℕ) :
    ∀ l₁ l₂ : List α, l₁.length ≤ n → l₁.Perm l₂ → wick β l₁ = wick β l₂ := by
  classical
  induction n with
  | zero =>
    intro l₁ l₂ h hp
    have h0 : l₁ = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp h)
    subst h0
    rw [List.Perm.nil_eq hp]
  | succ n ih =>
    have key : ∀ (a : α) (l : List α), l.length ≤ n →
        wick β (a :: l) = (l.map fun x => β a x * wick β (l.erase x)).sum := by
      intro a l hl
      rw [wick_cons]
      rw [← sum_fin_get l (fun x => β a x * wick β (l.erase x))]
      apply Finset.sum_congr rfl
      intro i _
      congr 1
      exact ih _ _ ((List.length_eraseIdx_le _ _).trans hl) (eraseIdx_perm_erase l i)
    intro l₁ l₂ hl hp
    revert hl
    induction hp with
    | nil => intro _; rfl
    | @cons x l₁ l₂ h _ =>
      intro hl
      have hl1 : l₁.length ≤ n := by simpa using hl
      have hl2 : l₂.length ≤ n := h.length_eq ▸ hl1
      rw [key x l₁ hl1, key x l₂ hl2]
      have hw : ∀ y, wick β (l₁.erase y) = wick β (l₂.erase y) := fun y =>
        ih _ _ (List.length_erase_le.trans hl1) (h.erase y)
      simp_rw [hw]
      exact (h.map _).sum_eq
    | swap x y l =>
      intro hl
      have hl0 : l.length + 1 ≤ n := by simp at hl; omega
      have expand : ∀ c u : α, u ∈ l → wick β ((c :: l).erase u) =
          ((l.erase u).map fun v => β c v * wick β ((l.erase u).erase v)).sum := by
        intro c u hu
        have hlen : ((c :: l).erase u).length ≤ n := by
          rw [List.length_erase_of_mem (List.mem_cons_of_mem c hu)]; simp; omega
        rw [ih _ _ hlen (cons_erase_perm c u l hu)]
        apply key
        have := (List.length_erase_le : (l.erase u).length ≤ l.length)
        omega
      rw [key y (x :: l) (by simp; omega), key x (y :: l) (by simp; omega)]
      simp only [List.map_cons, List.sum_cons, List.erase_cons_head]
      rw [hβ y x]
      congr 1
      have e1 : (l.map fun u => β y u * wick β ((x :: l).erase u)) =
          l.map fun u => β y u * ((l.erase u).map fun v => β x v * wick β ((l.erase u).erase v)).sum :=
        List.map_congr_left (fun u hu => by rw [expand x u hu])
      have e2 : (l.map fun u => β x u * wick β ((y :: l).erase u)) =
          l.map fun u => β x u * ((l.erase u).map fun v => β y v * wick β ((l.erase u).erase v)).sum :=
        List.map_congr_left (fun u hu => by rw [expand y u hu])
      rw [e1, e2]
      have lhs : (l.map fun u => β y u *
            ((l.erase u).map fun v => β x v * wick β ((l.erase u).erase v)).sum) =
          l.map fun u => ((l.erase u).map fun v => β y u * (β x v * wick β ((l.erase u).erase v))).sum :=
        List.map_congr_left (fun u _ => (List.sum_map_mul_left _ _ _).symm)
      rw [lhs, pair_sum_symm_list l (fun u v => β y u * (β x v * wick β ((l.erase u).erase v)))]
      congr 1
      apply List.map_congr_left
      intro u _
      rw [← List.sum_map_mul_left]
      congr 1
      apply List.map_congr_left
      intro v _
      rw [List.erase_comm]
      ring
    | trans h₁ h₂ ih₁ ih₂ =>
      intro hl
      rw [ih₁ hl, ih₂ (h₁.length_eq ▸ hl)]

theorem wick_perm {l₁ l₂ : List α} (hp : l₁.Perm l₂) : wick β l₁ = wick β l₂ :=
  wick_perm_aux β hβ l₁.length l₁ l₂ le_rfl hp

theorem wick_cons_erase [DecidableEq α] (a : α) (l : List α) :
    wick β (a :: l) = (l.map fun x => β a x * wick β (l.erase x)).sum := by
  rw [wick_cons]
  rw [← sum_fin_get l (fun x => β a x * wick β (l.erase x))]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  exact wick_perm β hβ (eraseIdx_perm_erase l i)

end Perm


section RingHom

variable {α : Type*} {R R' : Type*} [CommRing R] [CommRing R']

theorem wick_ringHom (φ : R →+* R') (β : α → α → R) :
    ∀ l : List α, wick (fun u v => φ (β u v)) l = φ (wick β l)
  | [] => by simp [wick_nil]
  | a :: l => by
    rw [wick_cons, wick_cons, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_mul, wick_ringHom φ β (l.eraseIdx i)]
termination_by l => l.length
decreasing_by
  simp only [List.length_cons]
  exact Nat.lt_succ_of_le (List.length_eraseIdx_le _ _)

/-- Wick sum of a multiset (independent of the order for symmetric pairings). -/
noncomputable def wickM (β : α → α → R) (s : Multiset α) : R := wick β s.toList

theorem wickM_ringHom (φ : R →+* R') (β : α → α → R) (s : Multiset α) :
    wickM (fun u v => φ (β u v)) s = φ (wickM β s) :=
  wick_ringHom φ β s.toList

theorem wickM_zero (β : α → α → R) : wickM β 0 = 1 := by
  simp [wickM, wick_nil]

end RingHom

section Multiset

variable {α : Type*} {R : Type*} [CommRing R]
variable {β : α → α → R} (hβ : ∀ u v, β u v = β v u)
include hβ

theorem wickM_coe (l : List α) : wickM β (l : Multiset α) = wick β l :=
  wick_perm β hβ (Multiset.coe_eq_coe.mp (Multiset.coe_toList _))

theorem wickM_cons [DecidableEq α] (a : α) (s : Multiset α) :
    wickM β (a ::ₘ s) = (s.map fun x => β a x * wickM β (s.erase x)).sum := by
  induction s using Quotient.inductionOn with
  | h l =>
    have e : a ::ₘ (Quotient.mk _ l : Multiset α) = ((a :: l : List α) : Multiset α) := rfl
    rw [e, wickM_coe hβ, wick_cons_erase β hβ]
    have e2 : (Quotient.mk _ l : Multiset α) = (l : Multiset α) := rfl
    rw [e2, Multiset.map_coe, Multiset.sum_coe]
    congr 1
    apply List.map_congr_left
    intro x _
    rw [Multiset.coe_erase, wickM_coe hβ]

/-- If the first element pairs trivially with every other element, the Wick sum vanishes. -/
theorem wickM_cons_eq_zero [DecidableEq α] (a : α) (s : Multiset α) (h : ∀ x ∈ s, β a x = 0) :
    wickM β (a ::ₘ s) = 0 := by
  rw [wickM_cons hβ]
  apply Multiset.sum_eq_zero
  intro y hy
  obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.mp hy
  rw [h x hx, zero_mul]

/-- Congruence: only the values of the pairing on the elements of the multiset matter. -/
theorem wickM_congr [DecidableEq α] {β' : α → α → R} (hβ' : ∀ u v, β' u v = β' v u) :
    ∀ s : Multiset α, (∀ u ∈ s, ∀ v ∈ s, β u v = β' u v) → wickM β s = wickM β' s := by
  intro s
  induction s using Multiset.strongInductionOn with
  | ih s ih =>
    intro h
    induction s using Multiset.induction_on with
    | empty => rw [wickM_zero, wickM_zero]
    | cons a t _ =>
      rw [wickM_cons hβ, wickM_cons hβ']
      apply congrArg Multiset.sum
      apply Multiset.map_congr rfl
      intro x hx
      rw [h a (Multiset.mem_cons_self a t) x (Multiset.mem_cons_of_mem hx)]
      congr 1
      apply ih
      · exact lt_of_le_of_lt (Multiset.erase_le x t) (Multiset.lt_cons_self t a)
      · intro u hu v hv
        exact h u (Multiset.mem_cons_of_mem (Multiset.mem_of_mem_erase hu)) v
          (Multiset.mem_cons_of_mem (Multiset.mem_of_mem_erase hv))

/-- Block factorisation: orthogonal multisets contribute independently. -/
theorem wickM_add_of_orth [DecidableEq α] (t : Multiset α) :
    ∀ s : Multiset α, (∀ u ∈ s, ∀ v ∈ t, β u v = 0) → wickM β (s + t) = wickM β s * wickM β t := by
  intro s
  induction s using Multiset.strongInductionOn with
  | ih s ih =>
    intro h
    induction s using Multiset.induction_on with
    | empty => rw [zero_add, wickM_zero, one_mul]
    | cons a s' _ =>
      rw [Multiset.cons_add, wickM_cons hβ, wickM_cons hβ, Multiset.map_add, Multiset.sum_add]
      have h0 : (t.map fun x => β a x * wickM β ((s' + t).erase x)).sum = 0 := by
        apply Multiset.sum_eq_zero
        intro y hy
        obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.mp hy
        rw [h a (Multiset.mem_cons_self a s') x hx, zero_mul]
      rw [h0, add_zero, ← Multiset.sum_map_mul_right]
      apply congrArg Multiset.sum
      apply Multiset.map_congr rfl
      intro x hx
      rw [Multiset.erase_add_left_pos t hx, mul_assoc]
      congr 1
      apply ih
      · exact lt_of_le_of_lt (Multiset.erase_le x s') (Multiset.lt_cons_self s' a)
      · intro u hu v hv
        exact h u (Multiset.mem_cons_of_mem (Multiset.mem_of_mem_erase hu)) v hv

/-- Scaling every element scales the Wick sum by the product of the scalars. -/
theorem wickM_scale [DecidableEq α] {β' : α → α → R} (hβ' : ∀ u v, β' u v = β' v u) (σ : α → R)
    (hs : ∀ u v, β' u v = σ u * σ v * β u v) :
    ∀ s : Multiset α, wickM β' s = (s.map σ).prod * wickM β s := by
  intro s
  induction s using Multiset.strongInductionOn with
  | ih s ih =>
    induction s using Multiset.induction_on with
    | empty => rw [wickM_zero, wickM_zero, Multiset.map_zero, Multiset.prod_zero, one_mul]
    | cons a t _ =>
      rw [wickM_cons hβ', wickM_cons hβ, Multiset.map_cons, Multiset.prod_cons,
        ← Multiset.sum_map_mul_left]
      apply congrArg Multiset.sum
      apply Multiset.map_congr rfl
      intro x hx
      rw [hs, ih _ (lt_of_le_of_lt (Multiset.erase_le x t) (Multiset.lt_cons_self t a)),
        ← Multiset.prod_map_erase hx]
      ring

end Multiset

section Relabel

variable {α α' : Type*} {R : Type*} [CommRing R]

/-- Relabelling the elements of a multiset. -/
theorem wickM_map [DecidableEq α] [DecidableEq α'] {β : α → α → R} (hβ : ∀ u v, β u v = β v u)
    (f : α' → α) : ∀ s : Multiset α', wickM β (s.map f) = wickM (fun u v => β (f u) (f v)) s := by
  have hβf : ∀ u v, β (f u) (f v) = β (f v) (f u) := fun u v => hβ _ _
  intro s
  induction s using Multiset.strongInductionOn with
  | ih s ih =>
    induction s using Multiset.induction_on with
    | empty => rw [Multiset.map_zero, wickM_zero, wickM_zero]
    | cons a t _ =>
      rw [Multiset.map_cons, wickM_cons hβ, wickM_cons hβf, Multiset.map_map]
      apply congrArg Multiset.sum
      apply Multiset.map_congr rfl
      intro x hx
      simp only [Function.comp]
      rw [← Multiset.map_erase_of_mem f t hx,
        ih _ (lt_of_le_of_lt (Multiset.erase_le x t) (Multiset.lt_cons_self t a))]

end Relabel


section Degree

open Polynomial

variable {α : Type*} [DecidableEq α]

theorem natDegree_multiset_sum_le' {s : Multiset ℂ[X]} {n : ℕ} (h : ∀ p ∈ s, p.natDegree ≤ n) :
    s.sum.natDegree ≤ n := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a t ih =>
    rw [Multiset.sum_cons]
    exact (natDegree_add_le _ _).trans (max_le (h a (Multiset.mem_cons_self a t))
      (ih fun p hp => h p (Multiset.mem_cons_of_mem hp)))

variable {β : α → α → ℂ[X]} (hβ : ∀ u v, β u v = β v u) (δ : α → ℕ)
  (hdeg : ∀ u v, (β u v).natDegree ≤ δ u + δ v)
include hβ hdeg

/-- Degree budget: each element contributes at most its budget to the degree. -/
theorem wickM_natDegree_le : ∀ s : Multiset α, (wickM β s).natDegree ≤ (s.map δ).sum := by
  intro s
  induction s using Multiset.strongInductionOn with
  | ih s ih =>
    induction s using Multiset.induction_on with
    | empty => simp [wickM_zero]
    | cons a t _ =>
      rw [wickM_cons hβ]
      apply natDegree_multiset_sum_le'
      intro p hp
      obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.mp hp
      refine (natDegree_mul_le).trans ?_
      have h1 := hdeg a x
      have h2 := ih _ (lt_of_le_of_lt (Multiset.erase_le x t) (Multiset.lt_cons_self t a))
      have h3 := Multiset.sum_map_erase (f := δ) hx
      rw [Multiset.map_cons, Multiset.sum_cons]
      omega

/-- The coefficient at the full budget is the Wick sum of the top coefficients. -/
theorem wickM_coeff_top : ∀ s : Multiset α,
    (wickM β s).coeff (s.map δ).sum = wickM (fun u v => (β u v).coeff (δ u + δ v)) s := by
  have hβt : ∀ u v, (β u v).coeff (δ u + δ v) = (β v u).coeff (δ v + δ u) := by
    intro u v; rw [hβ u v, add_comm]
  intro s
  induction s using Multiset.strongInductionOn with
  | ih s ih =>
    induction s using Multiset.induction_on with
    | empty => simp [wickM_zero]
    | cons a t _ =>
      rw [wickM_cons hβ, wickM_cons hβt, ← Polynomial.lcoeff_apply, map_multiset_sum,
        Multiset.map_map]
      apply congrArg Multiset.sum
      apply Multiset.map_congr rfl
      intro x hx
      simp only [Function.comp, Polynomial.lcoeff_apply]
      have h3 := Multiset.sum_map_erase (f := δ) hx
      have e : ((a ::ₘ t).map δ).sum = (δ a + δ x) + ((t.erase x).map δ).sum := by
        rw [Multiset.map_cons, Multiset.sum_cons, ← h3]; ring
      rw [e, coeff_mul_add_eq_of_natDegree_le (hdeg a x)
        (wickM_natDegree_le hβ δ hdeg _),
        ih _ (lt_of_le_of_lt (Multiset.erase_le x t) (Multiset.lt_cons_self t a))]

end Degree

end OM.NNN30.Crossing
