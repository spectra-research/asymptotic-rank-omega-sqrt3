import Lib.OM.NNN32.FourPoint
import PLATFORM.Statements.«R113.18»
import PLATFORM.Statements.«R113.20»

/-! # The three matchings as products of individual equality wires -/

noncomputable section

namespace OM.NNN32

open Semicontinuity AsymptoticSpectrumDuality

private lemma mk_congr {d e : Fin 4 → ℕ+} (h : d=e) (S : KTensor ℂ d) (T : KTensor ℂ e)
    (he : ∀ x, S (fun i => Fin.cast (congrArg (fun f : Fin 4 → ℕ+ => ((f i : ℕ+) : ℕ)) h.symm) (x i)) = T x) :
    TensorClass.mk ⟨_,S⟩ = TensorClass.mk ⟨_,T⟩ := by
  subst e
  have hs : S=T := funext he
  rw [hs]

abbrev wire (D : ℕ+) (i j : Fin 4) (hij : i ≠ j) : TensorClass ℂ 4 :=
  TensorClass.mk ⟨_,unitPairTensor (F := ℂ) D i j hij⟩

lemma matching_eq_wires (D : ℕ+) {i j k l : Fin 4} (hij : i ≠ j) (hkl : k ≠ l)
    (hdis : ∀ a : Fin 4, (a = i ∨ a = j) ↔ ¬(a = k ∨ a = l)) :
    TensorClass.mk ⟨_,matching D i j k l⟩ = wire D i j hij * wire D k l hkl := by
  let L := naturalPairFormat D i j
  let R := naturalPairFormat D k l
  have fmt : (fun _ : Fin 4 => D) = (fun a => L a * R a) := by
    funext a
    by_cases h : a=i ∨ a=j
    · simp [L,R,naturalPairFormat,h,(hdis a).1 h]
    · have h' : a=k ∨ a=l := by_contra fun hn => h ((hdis a).2 hn)
      simp [L,R,naturalPairFormat,h,h']
  apply mk_congr fmt
  intro x
  have wi : R i = 1 := if_neg ((hdis i).1 (Or.inl rfl))
  have wj : R j = 1 := if_neg ((hdis j).1 (Or.inr rfl))
  have wk : L k = 1 := if_neg (fun h => (hdis k).1 h (Or.inl rfl))
  have wl : L l = 1 := if_neg (fun h => (hdis l).1 h (Or.inr rfl))
  have hmod (a : Fin 4) (ha : L a = 1) : (x a).val % R a = (x a).val :=
    Nat.mod_eq_of_lt (by have hh := (x a).isLt; simpa [PNat.mul_coe,ha] using hh)
  simp only [matching,kroneckerTensor,unitPairTensor,Fin.ext_iff,Fin.val_cast]
  change (if (x i).val = (x j).val ∧ (x k).val = (x l).val then (1:ℂ) else 0) =
    (if (x i).val / R i = (x j).val / R j then 1 else 0) *
    (if (x k).val % R k = (x l).val % R l then 1 else 0)
  have hdiv (a n : ℕ) (h : n=1) : a / n = a := by simp [h]
  rw [hdiv _ _ (congrArg PNat.val wi),hdiv _ _ (congrArg PNat.val wj),hmod k wk,hmod l wl]
  split_ifs <;> simp_all

theorem spectral_of_price_spaces (hprice : S_R113_18) : S_R113_20 := by
  rintro ⟨κ,hk,hc,hd⟩ D φ
  let p := tensorStrassenPreorder (F := ℂ) (k := 4) (by decide +kernel)
  obtain ⟨X,S,t,hB,ht⟩ := hprice κ hk hc hd φ
  have matching_value {i j k l : Fin 4} (hij : i ≠ j) (hkl : k ≠ l)
      (hdis : ∀ a : Fin 4, (a=i ∨ a=j) ↔ ¬(a=k ∨ a=l)) :
      AsymptoticSpectrum.eval p (TensorClass.mk ⟨_,matching D i j k l⟩) φ =
        ((D:ℕ):ℝ) ^ (S.d (t i) (t j) + S.d (t k) (t l)) := by
    rw [matching_eq_wires D hij hkl hdis,AsymptoticSpectrum.eval_mul,Real.rpow_add (by positivity)]
    exact congrArg₂ (· * ·) (ht D i j hij) (ht D k l hkl)
  have side := proof_R113_19 X S κ hk hc hB (t 0) (t 1) (t 3) (t 2)
  rw [S.d_comm (t 3) (t 2)] at side
  let value (i j k l : Fin 4) := AsymptoticSpectrum.eval p (TensorClass.mk ⟨_,matching D i j k l⟩) φ
  change value 0 3 1 2 ≤ max (value 0 1 2 3) (value 0 2 1 3)
  unfold value
  rw [matching_value (i := 0) (j := 3) (k := 1) (l := 2) (by decide +kernel) (by decide +kernel) (by decide +kernel),
    matching_value (i := 0) (j := 1) (k := 2) (l := 3) (by decide +kernel) (by decide +kernel) (by decide +kernel),
    matching_value (i := 0) (j := 2) (k := 1) (l := 3) (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  have hD : (1:ℝ) ≤ (D:ℕ) := by exact_mod_cast D.2
  rcases le_max_iff.1 side with h | h
  · exact (Real.rpow_le_rpow_of_exponent_le hD h).trans (le_max_left _ _)
  · exact (Real.rpow_le_rpow_of_exponent_le hD h).trans (le_max_right _ _)

end OM.NNN32
