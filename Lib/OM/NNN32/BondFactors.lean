import Lib.OM.NNN32.WirePrices
import Lib.OM.NNN32.PowerRestriction

/-! # Restrictions for local observations and a single factored bond -/

noncomputable section
open scoped Classical

namespace OM.NNN32

open Semicontinuity AsymptoticSpectrumDuality

lemma pull_restricts {d e : Fin 4 → ℕ+} (f : ∀ i, Fin (e i) → Fin (d i)) (T : KTensor ℂ d) :
    Restricts (pull f T) T := by
  refine ⟨fun i a b => if f i a=b then 1 else 0,?_⟩
  intro x
  rw [Finset.sum_eq_single (fun i => f i (x i))]
  · simp [pull]
  · intro y _ hxy
    obtain ⟨i,hi⟩ : ∃ i, f i (x i) ≠ y i := by
      by_contra! h
      exact hxy (funext h).symm
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi),zero_mul]
  · simp

abbrev fourValue {d : Fin 4 → ℕ+} (φ : AsymptoticSpectrum fourPreorder) (T : KTensor ℂ d) :=
  AsymptoticSpectrum.eval fourPreorder (TensorClass.mk ⟨_,T⟩) φ

lemma fourValue_mono {d e : Fin 4 → ℕ+} (φ : AsymptoticSpectrum fourPreorder)
    {S : KTensor ℂ d} {T : KTensor ℂ e} (h : Restricts S T) : fourValue φ S ≤ fourValue φ T :=
  φ.monotone (TensorClass.mk ⟨_,S⟩) (TensorClass.mk ⟨_,T⟩) h

lemma value_pointwise_mul {d : Fin 4 → ℕ+} (φ : AsymptoticSpectrum fourPreorder) (S T : KTensor ℂ d) :
    fourValue φ (S*T) ≤ fourValue φ S * fourValue φ T := by
  let f (i : Fin 4) (x : Fin (d i)) : Fin ((d i * d i : ℕ+) : ℕ) := kronDecodeEquiv.symm (x,x)
  have he : pull f (kroneckerTensor S T) = S*T := by
    funext x
    have hloc i : kronDecodeEquiv (f i (x i)) = (x i,x i) := Equiv.apply_symm_apply _ _
    have hl i := congrArg Prod.fst (hloc i)
    have hr i := congrArg Prod.snd (hloc i)
    change S _ * T _ = S x * T x
    exact congrArg₂ (· * ·) (congrArg S (funext hl)) (congrArg T (funext hr))
  rw [← he,← AsymptoticSpectrum.eval_mul fourPreorder φ]
  exact φ.monotone _ _ (pull_restricts f (kroneckerTensor S T))

private def pairIndex (r : ℕ+) (i j : Fin 4) (z : Fin (r:ℕ)) (a : Fin 4) : Fin (naturalPairFormat r i j a) :=
  if h : a=i ∨ a=j then ⟨z.val,by simpa [naturalPairFormat,h] using z.isLt⟩
  else ⟨0,(naturalPairFormat r i j a).pos⟩

private lemma pairIndex_val {r : ℕ+} {i j a : Fin 4} (h : a=i ∨ a=j) (z : Fin (r:ℕ)) :
    (pairIndex r i j z a).val = z.val := by simp [pairIndex,h]

private lemma sum_pair (r : ℕ+) (i j : Fin 4) (hij : i ≠ j)
    (f : ((a : Fin 4) → Fin (naturalPairFormat r i j a)) → ℂ) :
    ∑ y, f y * unitPairTensor (F := ℂ) r i j hij y = ∑ z, f (pairIndex r i j z) := by
  let z (y : (a : Fin 4) → Fin (naturalPairFormat r i j a)) : Fin (r:ℕ) :=
    ⟨(y i).val,by simpa [naturalPairFormat] using (y i).isLt⟩
  have hinj : Function.Injective (pairIndex r i j) := by
    intro a b h
    exact Fin.ext (by simpa [pairIndex] using congrArg Fin.val (congrFun h i))
  have hs (y : (a : Fin 4) → Fin (naturalPairFormat r i j a)) :
      (y i).val = (y j).val ↔ pairIndex r i j (z y) = y := by
    constructor
    · intro he
      funext a
      apply Fin.ext
      by_cases ha : a=i ∨ a=j
      · rw [pairIndex_val ha]
        rcases ha with rfl | rfl
        · rfl
        · exact he
      · have hh : (y a).val < 1 := by simpa [naturalPairFormat,ha] using (y a).isLt
        simp [pairIndex,ha,show (y a).val = 0 by omega]
    · intro he
      have h := congrArg Fin.val (congrFun he j)
      simpa [pairIndex,z] using h
  have hv (y : (a : Fin 4) → Fin (naturalPairFormat r i j a)) :
      f y * unitPairTensor (F := ℂ) r i j hij y = ∑ w, if pairIndex r i j w = y then f y else 0 := by
    by_cases h : (y i).val = (y j).val
    · rw [Finset.sum_eq_single (z y)]
      · simp [unitPairTensor,h,(hs y).1 h]
      · intro w _ hw
        exact if_neg (fun he => hw (hinj (he.trans ((hs y).1 h).symm)))
      · simp
    · have hh (w) : pairIndex r i j w ≠ y := by
        rintro rfl
        apply h
        simp [pairIndex]
      simp [unitPairTensor,h,hh]
  simp_rw [hv]
  rw [Finset.sum_comm]
  simp

/-- Each end of a bond of size r reads one local configuration. -/
lemma bond_restricts {d : Fin 4 → ℕ+} (r : ℕ+) {i j : Fin 4} (hij : i ≠ j)
    (g : Fin (d i) → Fin (r:ℕ) → ℂ) (h : Fin (d j) → Fin (r:ℕ) → ℂ) :
    Restricts (fun x => ∑ z, g (x i) z * h (x j) z : KTensor ℂ d)
      (unitPairTensor (F := ℂ) r i j hij) := by
  let left (a : Fin 4) (x : Fin (d a)) (y : Fin (naturalPairFormat r i j a)) :=
    if e : a=i then g (e ▸ x) ⟨y.val,by subst a; simpa [naturalPairFormat] using y.isLt⟩ else 1
  let right (a : Fin 4) (x : Fin (d a)) (y : Fin (naturalPairFormat r i j a)) :=
    if e : a=j then h (e ▸ x) ⟨y.val,by subst a; simpa [naturalPairFormat] using y.isLt⟩ else 1
  refine ⟨fun a x y => left a x y * right a x y,?_⟩
  intro x
  rw [sum_pair]
  apply Finset.sum_congr rfl
  intro z _
  rw [Finset.prod_mul_distrib]
  have hl : ∏ a, left a (x a) (pairIndex r i j z a) = g (x i) z := by
    rw [Finset.prod_eq_single i]
    · simp [left,pairIndex]
    · intro a _ ha; simp [left,ha]
    · simp
  have hr : ∏ a, right a (x a) (pairIndex r i j z a) = h (x j) z := by
    rw [Finset.prod_eq_single j]
    · simp [right,pairIndex]
    · intro a _ ha; simp [right,ha]
    · simp
  rw [hl,hr]

lemma local_restricts {d : Fin 4 → ℕ+} (i : Fin 4) (g : Fin (d i) → ℂ) :
    Restricts (fun x => g (x i) : KTensor ℂ d) (unitTensor ℂ 1) := by
  refine ⟨fun a x _ => if e : a=i then g (e ▸ x) else 1,?_⟩
  intro x
  let z : (a : Fin 4) → Fin ((1:ℕ+):ℕ) := fun _ => 0
  rw [Finset.sum_eq_single z]
  · rw [unitTensor_one_eq,mul_one,Finset.prod_eq_single i]
    · simp
    · intro a _ ha; simp [ha]
    · simp
  · intro y _ hn
    exact (hn (funext (fun a => Subsingleton.elim (α := Fin 1) (y a) (z a)))).elim
  · exact fun h => (h (Finset.mem_univ _)).elim

end OM.NNN32
