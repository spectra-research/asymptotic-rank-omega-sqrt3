/- Adapted from PolMul/DegenAsymp/Coefficients.lean of an earlier formalisation
   (commit 51c6e6b6e8b8d7226c6a828dba618ae1de5b5f8a).
   Uses Foundations tensor definitions; declarations are renamed under OM. -/
import Lib.OM.PolMul.Defs
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Polynomial coefficient extraction without interpolation

The coefficient convolution and its finite encoding below adapt the private
helpers in the dependency's `AsymptoticSubrank/BorderSubrank.lean` (Apache-2.0).
They concern arbitrary polynomials; no unit-tensor target is assumed.
-/

namespace OM.PolMul.DegenAsymp

open Semicontinuity
open scoped BigOperators

universe u
variable {F : Type u} [Field F]

private lemma coeff_prod_finsuppAntidiag {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → Polynomial F) (N : ℕ) :
    (∏ i, p i).coeff N
      = ∑ l ∈ Finset.finsuppAntidiag (Finset.univ : Finset ι) N,
          ∏ i, (p i).coeff (l i) := by
  classical
  -- Pull `coeff N` along the polynomial → power series coercion (a ring hom).
  have hcoe : ((∏ i, p i : Polynomial F) : PowerSeries F)
      = ∏ i, ((p i : Polynomial F) : PowerSeries F) :=
    map_prod (Polynomial.coeToPowerSeries.ringHom (R := F)) p Finset.univ
  rw [← Polynomial.coeff_coe, hcoe, PowerSeries.coeff_prod]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  refine Finset.prod_congr rfl (fun i _ => ?_)
  rw [Polynomial.coeff_coe]

private def exactifyPart (n N : ℕ) (c : Fin n → Fin (N + 1)) : Fin (n + 1) → ℕ :=
  Fin.lastCases (N - ∑ j : Fin n, (c j : ℕ)) (fun j : Fin n => (c j : ℕ))

def exactifyCoef (n N : ℕ) (i : Fin (n + 1)) (c : Fin n → Fin (N + 1))
    (p : Polynomial F) : F :=
  Fin.lastCases
    (if (∑ j : Fin n, (c j : ℕ)) ≤ N then p.coeff (N - ∑ j : Fin n, (c j : ℕ)) else 0)
    (fun j : Fin n => p.coeff (c j : ℕ)) i

private lemma exactifyPart_castSucc (n N : ℕ) (c : Fin n → Fin (N + 1)) (j : Fin n) :
    exactifyPart n N c j.castSucc = (c j : ℕ) := by
  simp [exactifyPart]

private lemma exactifyPart_last (n N : ℕ) (c : Fin n → Fin (N + 1)) :
    exactifyPart n N c (Fin.last n) = N - ∑ j : Fin n, (c j : ℕ) := by
  simp [exactifyPart]

private lemma exactifyCoef_castSucc (n N : ℕ) (c : Fin n → Fin (N + 1))
    (p : Polynomial F) (j : Fin n) :
    exactifyCoef n N j.castSucc c p = p.coeff (c j : ℕ) := by
  simp [exactifyCoef]

private lemma exactifyCoef_last (n N : ℕ) (c : Fin n → Fin (N + 1)) (p : Polynomial F) :
    exactifyCoef n N (Fin.last n) c p =
      if (∑ j : Fin n, (c j : ℕ)) ≤ N then p.coeff (N - ∑ j : Fin n, (c j : ℕ)) else 0 := by
  simp [exactifyCoef]

set_option linter.flexible false in
lemma exactifyCoef_sum_eq_coeff (n N : ℕ) (p : Fin (n + 1) → Polynomial F) :
    (∑ q : Fin ((N + 1) ^ n),
        ∏ i : Fin (n + 1),
          exactifyCoef n N i (finFunctionFinEquiv.symm q) (p i))
      = (∏ i : Fin (n + 1), p i).coeff N := by
  classical
  let e := finFunctionFinEquiv (m := N + 1) (n := n)
  let H : (Fin n → Fin (N + 1)) → F :=
    fun c => ∏ i : Fin (n + 1), exactifyCoef n N i c (p i)
  have hq : (∑ q : Fin ((N + 1) ^ n), H (e.symm q)) = ∑ c : Fin n → Fin (N + 1), H c := by
    simpa [e] using! (e.symm.sum_comp H)
  rw [show (∑ q : Fin ((N + 1) ^ n),
        ∏ i : Fin (n + 1), exactifyCoef n N i (finFunctionFinEquiv.symm q) (p i))
        = ∑ q : Fin ((N + 1) ^ n), H (e.symm q) from rfl, hq]
  let valid : (Fin n → Fin (N + 1)) → Prop := fun c => (∑ j : Fin n, (c j : ℕ)) ≤ N
  have hinvalid_zero : ∀ c : Fin n → Fin (N + 1), ¬ valid c → H c = 0 := by
    intro c hc
    have hlast : exactifyCoef n N (Fin.last n) c (p (Fin.last n)) = 0 := by
      rw [exactifyCoef_last, if_neg hc]
    exact Finset.prod_eq_zero (Finset.mem_univ (Fin.last n)) hlast
  rw [show (∑ c : Fin n → Fin (N + 1), H c)
      = ∑ c ∈ (Finset.univ.filter valid : Finset (Fin n → Fin (N + 1))), H c by
        symm
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl ?_
        intro c _
        by_cases hc : valid c
        · rw [if_pos hc]
        · rw [if_neg hc, hinvalid_zero c hc]]
  rw [coeff_prod_finsuppAntidiag (F := F) p N]
  -- Use `sum_bij` with the membership-dependent map, so the bound proof for `Fin (N+1)`
  -- can use the antidiagonal equation.
  refine (Finset.sum_bij
    (s := Finset.finsuppAntidiag (Finset.univ : Finset (Fin (n + 1))) N)
    (t := (Finset.univ.filter valid : Finset (Fin n → Fin (N + 1))))
    (f := fun l => ∏ i : Fin (n + 1), (p i).coeff (l i))
    (g := H)
    (fun l hl j => ⟨l j.castSucc, by
      have hsum := (Finset.mem_finsuppAntidiag.mp hl).1
      have hle : l j.castSucc ≤ N := by
        rw [← hsum]
        exact Finset.single_le_sum (fun _ _ => by positivity) (Finset.mem_univ j.castSucc)
      omega⟩)
    ?_ ?_ ?_ ?_).symm
  · intro l hl
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have hsum := (Finset.mem_finsuppAntidiag.mp hl).1
    have hsplit : (∑ x : Fin (n + 1), l x)
        = (∑ j : Fin n, l j.castSucc) + l (Fin.last n) := by
      exact Fin.sum_univ_castSucc (fun x : Fin (n + 1) => l x)
    rw [hsplit] at hsum
    have : (∑ j : Fin n, l j.castSucc) ≤ N := by omega
    simpa using! this
  · intro l₁ hl₁ l₂ hl₂ h
    apply Finsupp.ext
    intro i
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · exact congrArg Fin.val (congrFun h j)
    · have hsum₁ := (Finset.mem_finsuppAntidiag.mp hl₁).1
      have hsum₂ := (Finset.mem_finsuppAntidiag.mp hl₂).1
      have hsplit₁ : (∑ x : Fin (n + 1), l₁ x)
          = (∑ j : Fin n, l₁ j.castSucc) + l₁ (Fin.last n) :=
        Fin.sum_univ_castSucc (fun x : Fin (n + 1) => l₁ x)
      have hsplit₂ : (∑ x : Fin (n + 1), l₂ x)
          = (∑ j : Fin n, l₂ j.castSucc) + l₂ (Fin.last n) :=
        Fin.sum_univ_castSucc (fun x : Fin (n + 1) => l₂ x)
      rw [hsplit₁] at hsum₁
      rw [hsplit₂] at hsum₂
      have hpref : (∑ j : Fin n, l₁ j.castSucc) = ∑ j : Fin n, l₂ j.castSucc := by
        refine Finset.sum_congr rfl ?_
        intro j _
        exact congrArg Fin.val (congrFun h j)
      omega
  · intro c hc
    rw [Finset.mem_filter] at hc
    obtain ⟨_, hcvalid⟩ := hc
    let l : Fin (n + 1) →₀ ℕ :=
      Finsupp.onFinset Finset.univ
        (exactifyPart n N c)
        (by intro i _; simp)
    refine ⟨l, ?_, ?_⟩
    · rw [Finset.mem_finsuppAntidiag]
      constructor
      · dsimp [l]
        change (∑ x : Fin (n + 1), exactifyPart n N c x) = N
        rw [Fin.sum_univ_castSucc]
        simp [exactifyPart_castSucc, exactifyPart_last]
        rw [Nat.add_comm]
        exact Nat.sub_add_cancel hcvalid
      · exact fun x _ => Finset.mem_univ x
    · funext j
      dsimp [l]
      simp [exactifyPart_castSucc]
  · intro l hl
    dsimp [H]
    refine Finset.prod_congr rfl ?_
    intro i _
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · simp [exactifyCoef_castSucc]
    · have hsum := (Finset.mem_finsuppAntidiag.mp hl).1
      have hsplit : (∑ x : Fin (n + 1), l x)
          = (∑ j : Fin n, l j.castSucc) + l (Fin.last n) :=
        Fin.sum_univ_castSucc (fun x : Fin (n + 1) => l x)
      rw [hsplit] at hsum
      have hle : (∑ j : Fin n, l j.castSucc) ≤ N := by omega
      have hlast : l (Fin.last n) = N - ∑ j : Fin n, l j.castSucc := by omega
      simp [exactifyCoef_last, hle, hlast]


end OM.PolMul.DegenAsymp
