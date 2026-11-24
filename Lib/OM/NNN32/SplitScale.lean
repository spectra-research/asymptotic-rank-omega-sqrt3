import Lib.OM.NNN32.Splits
import Lib.OM.NNN30.Net.Cross

/-! # Using an unbounded sequence of cheap splits at powered network scales

For a fixed register of size b, restrict a favorable split at D to b^p, where
p is the integer base-b logarithm of D. The loss of at most one power of b
in the favorable dimension costs at most ε in the normalized exponent.
-/

noncomputable section

namespace OM.NNN32

open Semicontinuity

lemma P_mono : Monotone P := by
  intro b D h
  let f (_ : Fin 4) := Fin.castLE (show (b:ℕ) ≤ (D:ℕ) from h)
  obtain ⟨R,S,hs,hP⟩ := (split_min D).1
  have he : pull f R + pull f S = crossing b := by
    funext x
    have h' := congrFun hs (fun i => f i (x i))
    simpa [pull,crossing,matching,f] using h'
  exact ((split_min b).2 ⟨pull f R,pull f S,he,rfl⟩).trans ((Nat.add_le_add
    (flatRank_pull_le f R {0,1}) (flatRank_pull_le f S {0,2})).trans_eq hP.symm)

theorem cheap_split_at_powers {κ : ℝ} (hκ : 0 ≤ κ)
    (hcheap : ∀ M : ℕ+, ∃ D : ℕ+, M ≤ D ∧ (P D : ℝ) ≤ ((D:ℕ):ℝ)^κ)
    (b : ℕ+) (hb : 2 ≤ b) {ε : ℝ} (hε : 0 < ε) (m : ℕ) :
    ∃ p : ℕ, m ≤ p ∧ (P (b^p) : ℝ) ≤ ((b:ℕ):ℝ) ^ ((p : ℝ)*(κ+ε)) := by
  let q := max m ⌈κ/ε⌉₊
  obtain ⟨D,hD,hd⟩ := hcheap (b^q)
  let p := Nat.log (b:ℕ) (D:ℕ)
  have hb' : 1 < (b:ℕ) := hb
  have hq : q ≤ p := Nat.le_log_of_pow_le hb' hD
  have hlow : (b^p : ℕ+) ≤ D := Nat.pow_log_le_self _ D.ne_zero
  have hhigh : (D:ℕ) < (b:ℕ)^(p+1) := Nat.lt_pow_succ_log_self hb' _
  have hbase : (1:ℝ) ≤ (b:ℕ) := by exact_mod_cast b.2
  have hlarge : κ / ε ≤ (p:ℝ) := (Nat.le_ceil _).trans
    (by exact_mod_cast (le_max_right m ⌈κ/ε⌉₊).trans hq)
  have he := (div_le_iff₀ hε).1 hlarge
  refine ⟨p,(le_max_left _ _).trans hq,?_⟩
  calc
    _ ≤ (P D : ℝ) := by exact_mod_cast P_mono hlow
    _ ≤ _ := hd
    _ ≤ (((b:ℕ):ℝ)^(p+1))^κ :=
      Real.rpow_le_rpow (by positivity) (by exact_mod_cast hhigh.le) hκ
    _ = ((b:ℕ):ℝ)^(((p:ℝ)+1)*κ) := by rw [← Real.rpow_natCast_mul (by positivity)]; push_cast; rfl
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hbase (by linarith)

/-- A cheap powered register has two factorizations whose middle bond sizes,
added together, obey the same exponent. Each factor retains both of its corner indices. -/
theorem cheap_split_factors {κ : ℝ} (hκ : 0 ≤ κ)
    (hcheap : ∀ M : ℕ+, ∃ D : ℕ+, M ≤ D ∧ (P D : ℝ) ≤ ((D:ℕ):ℝ)^κ)
    (b : ℕ+) (hb : 2 ≤ b) {ε : ℝ} (hε : 0 < ε) (m : ℕ) :
    ∃ p : ℕ, m ≤ p ∧ ∃ r s : ℕ, (((r+s : ℕ) : ℝ) ≤ ((b:ℕ):ℝ)^((p:ℝ)*(κ+ε))) ∧
      ∃ (A : Index (b^p) × Index (b^p) → Fin r → ℂ) (B : Fin r → Index (b^p) × Index (b^p) → ℂ)
        (C : Index (b^p) × Index (b^p) → Fin s → ℂ) (E : Fin s → Index (b^p) × Index (b^p) → ℂ),
      ∀ x y u v, (if x=v ∧ y=u then (1:ℂ) else 0) =
        (∑ z, A (x,y) z * B z (u,v)) + ∑ z, C (x,u) z * E z (y,v) := by
  obtain ⟨p,hp,hcost⟩ := cheap_split_at_powers hκ hcheap b hb hε m
  obtain ⟨R,S,hs,hP⟩ := (split_min (b^p)).1
  obtain ⟨A,B,hAB⟩ := OM.NNN30.Net.exists_rank_factor (rowMatrix R)
  obtain ⟨C,E,hCE⟩ := OM.NNN30.Net.exists_rank_factor (colMatrix S)
  refine ⟨p,hp,_,_,?_,A,B,C,E,?_⟩
  · rwa [rowMatrix_rank,colMatrix_rank,← hP]
  · intro x y u v
    rw [← hAB,← hCE]
    simpa [rowMatrix,colMatrix,coeff,crossing,matching] using (congrFun hs ![x,y,u,v]).symm

end OM.NNN32
