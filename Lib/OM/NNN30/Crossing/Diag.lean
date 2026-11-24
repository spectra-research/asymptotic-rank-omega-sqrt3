import Lib.OM.NNN30.Crossing.Kernel

namespace OM.NNN30.Crossing

/-- The `z`–`∞` top kernel with integer values. -/
def zinfK : Pt × ℕ → Pt × ℕ → ℤ
  | (.z, a), (.inf, d) | (.inf, d), (.z, a) => ((d - 1).choose (a - 1) : ℤ)
  | _, _ => 0

theorem zinfK_symm (u v : Pt × ℕ) : zinfK u v = zinfK v u := by
  rcases u with ⟨_ | _ | _ | _ | _, a⟩ <;> rcases v with ⟨_ | _ | _ | _ | _, b⟩ <;> rfl

theorem zinfK_nonneg (u v : Pt × ℕ) : 0 ≤ zinfK u v := by
  rcases u with ⟨_ | _ | _ | _ | _, a⟩ <;> rcases v with ⟨_ | _ | _ | _ | _, b⟩ <;>
    simp [zinfK]

/-- A Wick sum of a nonnegative integer pairing is nonnegative. -/
theorem wickM_nonneg {α : Type*} [DecidableEq α] {β : α → α → ℤ} (hβ : ∀ u v, β u v = β v u)
    (hpos : ∀ u v, 0 ≤ β u v) : ∀ s : Multiset α, 0 ≤ wickM β s := by
  intro s
  induction s using Multiset.strongInductionOn with
  | ih s ih =>
    induction s using Multiset.induction_on with
    | empty => rw [wickM_zero]; norm_num
    | cons a t _ =>
      rw [wickM_cons hβ]
      apply Multiset.sum_nonneg
      intro y hy
      obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.mp hy
      exact mul_nonneg (hpos a x)
        (ih _ (lt_of_le_of_lt (Multiset.erase_le x t) (Multiset.lt_cons_self t a)))

def zM (s : Multiset ℕ) : Multiset (Pt × ℕ) := s.map (fun a => (Pt.z, a))
def iM (s : Multiset ℕ) : Multiset (Pt × ℕ) := s.map (fun d => (Pt.inf, d))

theorem delta_self (s : Multiset ℕ) : 1 ≤ wickM zinfK (zM s + iM s) := by
  induction s using Multiset.induction_on with
  | empty => simp [zM, iM, wickM_zero]
  | cons a t ih =>
    have e : zM (a ::ₘ t) + iM (a ::ₘ t) = (Pt.z, a) ::ₘ (zM t + iM (a ::ₘ t)) := by
      simp only [zM, iM, Multiset.map_cons, Multiset.cons_add]
    rw [e, wickM_cons zinfK_symm]
    have hmem : (Pt.inf, a) ∈ zM t + iM (a ::ₘ t) := by simp [iM]
    have hterm : zinfK (Pt.z, a) (Pt.inf, a) * wickM zinfK ((zM t + iM (a ::ₘ t)).erase (Pt.inf, a)) ∈
        (zM t + iM (a ::ₘ t)).map (fun x => zinfK (Pt.z, a) x *
          wickM zinfK ((zM t + iM (a ::ₘ t)).erase x)) := Multiset.mem_map_of_mem _ hmem
    refine le_trans ?_ (Multiset.single_le_sum (fun y hy => ?_) _ hterm)
    · have he : (zM t + iM (a ::ₘ t)).erase (Pt.inf, a) = zM t + iM t := by
        rw [Multiset.erase_add_right_pos _ (by simp [iM])]
        simp [iM]
      rw [he]
      simp only [zinfK, Nat.choose_self, Nat.cast_one, one_mul]
      exact ih
    · obtain ⟨x, _, rfl⟩ := Multiset.mem_map.mp hy
      exact mul_nonneg (zinfK_nonneg _ _) (wickM_nonneg zinfK_symm zinfK_nonneg _)

theorem delta_support (s : Multiset ℕ) (hs : ∀ a ∈ s, 0 < a) :
    ∀ t : Multiset ℕ, (∀ d ∈ t, 0 < d) → wickM zinfK (zM s + iM t) ≠ 0 →
      s.sum ≤ t.sum ∧ (s.sum = t.sum → s = t) := by
  induction s using Multiset.induction_on with
  | empty =>
    intro t ht _
    refine ⟨Nat.zero_le _, fun h => ?_⟩
    symm
    rw [Multiset.sum_zero] at h
    exact Multiset.eq_zero_of_forall_notMem (fun d hd => by
      have := Multiset.le_sum_of_mem hd; have := ht d hd; omega)
  | cons a s ih =>
    intro t ht hne
    have ha : 0 < a := hs a (Multiset.mem_cons_self a s)
    have hs' : ∀ b ∈ s, 0 < b := fun b hb => hs b (Multiset.mem_cons_of_mem hb)
    have e : zM (a ::ₘ s) + iM t = (Pt.z, a) ::ₘ (zM s + iM t) := by
      simp [zM, Multiset.cons_add]
    rw [e, wickM_cons zinfK_symm] at hne
    obtain ⟨y, hy, hyne⟩ : ∃ y ∈ (zM s + iM t).map (fun x => zinfK (Pt.z, a) x *
        wickM zinfK ((zM s + iM t).erase x)), y ≠ 0 := by
      by_contra h
      apply hne
      apply Multiset.sum_eq_zero
      intro y hy
      by_contra hy0
      exact h ⟨y, hy, hy0⟩
    obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.mp hy
    rcases Multiset.mem_add.mp hx with hx | hx
    · obtain ⟨b, _, rfl⟩ := Multiset.mem_map.mp hx
      simp [zinfK] at hyne
    · obtain ⟨d, hd, rfl⟩ := Multiset.mem_map.mp hx
      have hk : zinfK (Pt.z, a) (Pt.inf, d) ≠ 0 := left_ne_zero_of_mul hyne
      have hw := right_ne_zero_of_mul hyne
      have had : a ≤ d := by
        simp only [zinfK, ne_eq, Nat.cast_eq_zero] at hk
        have := ht d hd
        by_contra h
        exact hk (Nat.choose_eq_zero_of_lt (by omega))
      have he : (zM s + iM t).erase (Pt.inf, d) = zM s + iM (t.erase d) := by
        simp only [iM]
        rw [Multiset.erase_add_right_pos _ (Multiset.mem_map_of_mem _ hd),
          Multiset.map_erase _ (fun x y h => by simpa using h)]
      rw [he] at hw
      obtain ⟨h1, h2⟩ := ih hs' (t.erase d)
        (fun e he => ht e (Multiset.mem_of_mem_erase he)) hw
      have hsum := Multiset.sum_erase hd
      refine ⟨by rw [Multiset.sum_cons]; omega, fun heq => ?_⟩
      rw [Multiset.sum_cons] at heq
      have h3 : s.sum = (t.erase d).sum := by omega
      have h4 : a = d := by omega
      rw [h2 h3, h4, Multiset.cons_erase hd]

end OM.NNN30.Crossing
