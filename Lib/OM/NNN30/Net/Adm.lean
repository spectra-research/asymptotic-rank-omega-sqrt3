import Lib.OM.NNN30.Net.Basic

/-! # Admissible prices and minimal admissible prices

`Adm φ τ d`: every local network with positive value has `log₂ value ≤ cost`.  The admissible
set is closed (`isClosed_adm`); below any admissible vector there is a coordinatewise minimal one
(`exists_minAdm`); a minimal vector is symmetric (`MinAdm.symm`, by reversing factors) and
satisfies the triangle inequality (`MinAdm.triangle`, by re-routing factors through a third site
with one new variable per factor). -/

noncomputable section
open scoped BigOperators Classical

namespace OM.NNN30.Net

open CoordinateTensor OM.NNN.Raw

variable {S O0 O1 O2 P0 P1 P2 : Type}

/-- admissible prices -/
def Adm (φ : OM.PolMul.Spectral ℂ) (τ : Fin 3 → S) (d : S → S → ℝ) : Prop :=
  ∀ (O0 O1 O2 : Type) [Fintype O0] [Fintype O1] [Fintype O2] (N : TN S O0 O1 O2),
    N.Local τ → 0 < value φ N.Z → Real.logb 2 (value φ N.Z) ≤ N.cost d

/-- minimal admissible prices: admissible, nonnegative, zero on the diagonal, and no other such
vector lies below -/
def MinAdm (φ : OM.PolMul.Spectral ℂ) (τ : Fin 3 → S) (d : S → S → ℝ) : Prop :=
  Adm φ τ d ∧ (∀ s t, 0 ≤ d s t) ∧ (∀ s, d s s = 0) ∧
  ∀ d' : S → S → ℝ, Adm φ τ d' → (∀ s t, 0 ≤ d' s t) → (∀ s, d' s s = 0) →
    (∀ s t, d' s t ≤ d s t) → d' = d

namespace TN

lemma Z_eq_zero_of_r (N : TN S O0 O1 O2) {k : N.K} (hk : N.r k = 0) : N.Z = 0 := by
  funext a b c
  simp only [Z, Pi.zero_apply]
  refine Finset.sum_eq_zero fun x _ => ?_
  have : N.F k x = 0 := by
    unfold F
    have : IsEmpty (Fin (N.r k)) := by rw [hk]; infer_instance
    exact Finset.sum_of_isEmpty _
  rw [Finset.prod_eq_zero (Finset.mem_univ k) this, mul_zero]

lemma r_pos_of_value [Fintype O0] [Fintype O1] [Fintype O2] {φ : OM.PolMul.Spectral ℂ}
    (N : TN S O0 O1 O2) (hv : 0 < value φ N.Z) (k : N.K) : 0 < N.r k := by
  rcases Nat.eq_zero_or_pos (N.r k) with h | h
  · rw [N.Z_eq_zero_of_r h, value_zero] at hv; exact absurd hv (lt_irrefl _)
  · exact h

lemma logb_r_nonneg [Fintype O0] [Fintype O1] [Fintype O2] {φ : OM.PolMul.Spectral ℂ}
    (N : TN S O0 O1 O2) (hv : 0 < value φ N.Z) (k : N.K) : 0 ≤ Real.logb 2 (N.r k) :=
  Real.logb_nonneg (by norm_num) (by exact_mod_cast N.r_pos_of_value hv k)

lemma cost_mono [Fintype O0] [Fintype O1] [Fintype O2] {φ : OM.PolMul.Spectral ℂ}
    (N : TN S O0 O1 O2) (hv : 0 < value φ N.Z) {d d' : S → S → ℝ}
    (h : ∀ s t, d s t ≤ d' s t) : N.cost d ≤ N.cost d' :=
  Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_right (h _ _) (N.logb_r_nonneg hv k)

/-! ## Reversing factors -/

/-- reverse the factors satisfying `P` (swap ends and halves) -/
def rev (N : TN S O0 O1 O2) (P : N.K → Prop) : TN S O0 O1 O2 where
  V := N.V
  T := N.T
  loc := N.loc
  K := N.K
  e1 := fun k => if P k then N.e2 k else N.e1 k
  e2 := fun k => if P k then N.e1 k else N.e2 k
  r := N.r
  g := fun k i x => if P k then N.h k i x else N.g k i x
  h := fun k i x => if P k then N.g k i x else N.h k i x
  out0 := N.out0
  out1 := N.out1
  out2 := N.out2

lemma Z_rev (N : TN S O0 O1 O2) (P : N.K → Prop) : (N.rev P).Z = N.Z := by
  funext a b c
  refine Finset.sum_congr rfl fun x _ => ?_
  congr 1
  refine Finset.prod_congr rfl fun k _ => ?_
  show (∑ i, (if P k then N.h k i x else N.g k i x) * (if P k then N.g k i x else N.h k i x)) =
    ∑ i, N.g k i x * N.h k i x
  by_cases hk : P k
  · simp only [hk, if_true, mul_comm]
  · simp only [hk, if_false]

lemma Local.rev {τ : Fin 3 → S} {N : TN S O0 O1 O2} (hN : N.Local τ) (P : N.K → Prop) :
    (N.rev P).Local τ := by
  obtain ⟨hg, hh, h0, h1, h2⟩ := hN
  refine ⟨fun k i => ?_, fun k i => ?_, h0, h1, h2⟩
  · by_cases hk : P k
    · intro x y hxy
      show (if P k then N.h k i x else N.g k i x) = (if P k then N.h k i y else N.g k i y)
      rw [if_pos hk, if_pos hk]
      exact hh k i x y fun v hv => hxy v (show N.loc v = (if P k then N.e2 k else N.e1 k) by
        rw [if_pos hk, hv])
    · intro x y hxy
      show (if P k then N.h k i x else N.g k i x) = (if P k then N.h k i y else N.g k i y)
      rw [if_neg hk, if_neg hk]
      exact hg k i x y fun v hv => hxy v (show N.loc v = (if P k then N.e2 k else N.e1 k) by
        rw [if_neg hk, hv])
  · by_cases hk : P k
    · intro x y hxy
      show (if P k then N.g k i x else N.h k i x) = (if P k then N.g k i y else N.h k i y)
      rw [if_pos hk, if_pos hk]
      exact hg k i x y fun v hv => hxy v (show N.loc v = (if P k then N.e1 k else N.e2 k) by
        rw [if_pos hk, hv])
    · intro x y hxy
      show (if P k then N.g k i x else N.h k i x) = (if P k then N.g k i y else N.h k i y)
      rw [if_neg hk, if_neg hk]
      exact hh k i x y fun v hv => hxy v (show N.loc v = (if P k then N.e1 k else N.e2 k) by
        rw [if_neg hk, hv])

lemma cost_rev (d : S → S → ℝ) (N : TN S O0 O1 O2) (P : N.K → Prop) :
    (N.rev P).cost d = ∑ k, (if P k then d (N.e2 k) (N.e1 k) else d (N.e1 k) (N.e2 k)) *
      Real.logb 2 (N.r k) := by
  refine Finset.sum_congr rfl fun k _ => ?_
  show d (if P k then N.e2 k else N.e1 k) (if P k then N.e1 k else N.e2 k) *
    Real.logb 2 (N.r k) = _
  split_ifs <;> rfl

/-! ## Re-routing factors through a third site -/

/-- re-route the factors satisfying `P` through the site `t`: factor `k` becomes a factor from
`e1 k` to `t` and a factor from `t` to `e2 k`, joined by a new variable at `t` of size `r k` -/
def reroute (N : TN S O0 O1 O2) (P : N.K → Prop) (t : S) : TN S O0 O1 O2 where
  V := N.V ⊕ {k // P k}
  T := Sum.elim N.T (fun k => Fin (N.r k.1))
  fT := fun v => match v with
    | .inl v => N.fT v
    | .inr k => (inferInstance : Fintype (Fin (N.r k.1)))
  loc := Sum.elim N.loc (fun _ => t)
  K := N.K ⊕ {k // P k}
  e1 := Sum.elim (fun k => N.e1 k) (fun _ => t)
  e2 := Sum.elim (fun k => if P k then t else N.e2 k) (fun k => N.e2 k.1)
  r := Sum.elim N.r (fun k => N.r k.1)
  g := fun k => match k with
    | .inl k => fun i x => N.g k i (fun v => x (.inl v))
    | .inr k => fun i x => if x (.inr k) = i then 1 else 0
  h := fun k => match k with
    | .inl k => fun i x =>
        if hk : P k then (if x (.inr ⟨k, hk⟩) = i then 1 else 0) else N.h k i (fun v => x (.inl v))
    | .inr k => fun i x => N.h k.1 i (fun v => x (.inl v))
  out0 := fun x a => N.out0 (fun v => x (.inl v)) a
  out1 := fun x b => N.out1 (fun v => x (.inl v)) b
  out2 := fun x c => N.out2 (fun v => x (.inl v)) c

lemma sum_mul_ite_one {n : ℕ} (c : Fin n) (ψ : Fin n → ℂ) (inst : ∀ i, Decidable (c = i)) :
    (∑ i : Fin n, ψ i * @ite ℂ (c = i) (inst i) 1 0) = ψ c := by
  rw [Finset.sum_eq_single c (fun b _ hb => by rw [if_neg (Ne.symm hb), mul_zero])
    (fun h => absurd (Finset.mem_univ c) h)]
  rw [if_pos rfl, mul_one]

lemma sum_ite_one_mul {n : ℕ} (c : Fin n) (ψ : Fin n → ℂ) (inst : ∀ i, Decidable (c = i)) :
    (∑ i : Fin n, @ite ℂ (c = i) (inst i) 1 0 * ψ i) = ψ c := by
  rw [Finset.sum_eq_single c (fun b _ hb => by rw [if_neg (Ne.symm hb), zero_mul])
    (fun h => absurd (Finset.mem_univ c) h)]
  rw [if_pos rfl, one_mul]

/-- sums over assignments of a sum of two variable sets (any instance on the left) -/
lemma sum_sumPi {V P : Type} [Fintype V] [Fintype P] {T : V → Type} {U : P → Type}
    [∀ v, Fintype (T v)] [∀ k, Fintype (U k)] [instPi : Fintype ((w : V ⊕ P) → Sum.elim T U w)]
    (f : ((v : V) → T v) → ((k : P) → U k) → ℂ) :
    ∑ z : (w : V ⊕ P) → Sum.elim T U w, f (fun v => z (.inl v)) (fun k => z (.inr k)) =
      ∑ x, ∑ y, f x y := by
  rw [← Fintype.sum_prod_type']
  exact @Fintype.sum_equiv _ (((v : V) → T v) × ((k : P) → U k)) _ instPi _ _
    (Equiv.sumPiEquivProdPi (Sum.elim T U)) _ _ (fun z => rfl)

lemma reroute_F_inl (N : TN S O0 O1 O2) (P : N.K → Prop) (t : S) (k : N.K)
    (z : (v : (N.reroute P t).V) → (N.reroute P t).T v) :
    (N.reroute P t).F (.inl k) z = if hk : P k then N.g k (z (.inr ⟨k, hk⟩)) (fun v => z (.inl v))
      else N.F k (fun v => z (.inl v)) := by
  by_cases hk : P k
  · rw [dif_pos hk]
    have e : ∀ i : Fin (N.r k), (N.reroute P t).h (.inl k) i z =
        if (z (.inr ⟨k, hk⟩) : Fin (N.r k)) = i then 1 else 0 := by
      intro i
      show (if hk : P k then (if z (.inr ⟨k, hk⟩) = i then (1 : ℂ) else 0)
        else N.h k i (fun v => z (.inl v))) = _
      rw [dif_pos hk]
    show (∑ i : Fin (N.r k), N.g k i (fun v => z (.inl v)) * (N.reroute P t).h (.inl k) i z) = _
    simp only [e]
    exact sum_mul_ite_one _ _ _
  · rw [dif_neg hk]
    have e : ∀ i : Fin (N.r k), (N.reroute P t).h (.inl k) i z = N.h k i (fun v => z (.inl v)) := by
      intro i
      show (if hk : P k then (if z (.inr ⟨k, hk⟩) = i then (1 : ℂ) else 0)
        else N.h k i (fun v => z (.inl v))) = _
      rw [dif_neg hk]
    show (∑ i : Fin (N.r k), N.g k i (fun v => z (.inl v)) * (N.reroute P t).h (.inl k) i z) = _
    simp only [e]
    rfl

lemma reroute_F_inr (N : TN S O0 O1 O2) (P : N.K → Prop) (t : S) (k : {k // P k})
    (z : (v : (N.reroute P t).V) → (N.reroute P t).T v) :
    (N.reroute P t).F (.inr k) z = N.h k.1 (z (.inr k)) (fun v => z (.inl v)) := by
  show (∑ i : Fin (N.r k.1), (if (z (.inr k) : Fin (N.r k.1)) = i then (1 : ℂ) else 0) *
    N.h k.1 i (fun v => z (.inl v))) = _
  exact sum_ite_one_mul _ _ _

/-- assignments of the re-routed network: old variables and new variables -/
def rerouteEquiv (N : TN S O0 O1 O2) (P : N.K → Prop) (t : S) :
    ((v : (N.reroute P t).V) → (N.reroute P t).T v) ≃
      ((v : N.V) → N.T v) × ((k : {k // P k}) → Fin (N.r k.1)) :=
  Equiv.sumPiEquivProdPi _

lemma Z_reroute (N : TN S O0 O1 O2) (P : N.K → Prop) (t : S) : (N.reroute P t).Z = N.Z := by
  funext a b c
  let f : ((v : N.V) → N.T v) → ((k : {k // P k}) → Fin (N.r k.1)) → ℂ := fun x y =>
    N.out0 x a * N.out1 x b * N.out2 x c *
      ((∏ k : N.K, if hk : P k then N.g k (y ⟨k, hk⟩) x else N.F k x) *
        ∏ k : {k // P k}, N.h k.1 (y k) x)
  have hsum0 : (N.reroute P t).Z a b c = ∑ z : (v : (N.reroute P t).V) → (N.reroute P t).T v,
      f (fun v => z (.inl v)) (fun k => z (.inr k)) := by
    refine Finset.sum_congr rfl fun z _ => ?_
    have hp : (∏ k, (N.reroute P t).F k z) =
        (∏ k : N.K, (N.reroute P t).F (.inl k) z) * ∏ k : {k // P k}, (N.reroute P t).F (.inr k) z :=
      Fintype.prod_sum_type _
    show (N.reroute P t).out0 z a * (N.reroute P t).out1 z b * (N.reroute P t).out2 z c *
      ∏ k, (N.reroute P t).F k z = _
    rw [hp]
    simp only [reroute_F_inl, reroute_F_inr]
    rfl
  have hsum : (N.reroute P t).Z a b c = ∑ x, ∑ y, f x y := by
    rw [hsum0, ← Fintype.sum_prod_type']
    exact Fintype.sum_equiv (N.rerouteEquiv P t) _ _ (fun z => rfl)
  rw [hsum]
  show _ = ∑ x : (v : N.V) → N.T v, N.out0 x a * N.out1 x b * N.out2 x c * ∏ k, N.F k x
  refine Finset.sum_congr rfl fun x _ => ?_
  have hrhs : (∏ k, N.F k x) =
      (∏ k : {k // ¬ P k}, N.F k.1 x) * ∏ k : {k // P k}, N.F k.1 x := by
    have := Fintype.prod_subtype_mul_prod_subtype P (fun k => N.F k x)
    rw [← this, mul_comm]
  have hF : (∏ k : {k // P k}, N.F k.1 x) = ∑ y : (k : {k // P k}) → Fin (N.r k.1),
      ∏ k : {k // P k}, (N.g k.1 (y k) x * N.h k.1 (y k) x) :=
    Fintype.prod_sum (fun (k : {k // P k}) (i : Fin (N.r k.1)) => N.g k.1 i x * N.h k.1 i x)
  rw [hrhs, hF, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  simp only [f]
  rw [Fintype.prod_dite, Finset.prod_mul_distrib]
  ring

lemma Local.reroute {τ : Fin 3 → S} {N : TN S O0 O1 O2} (hN : N.Local τ) (P : N.K → Prop)
    (t : S) : (N.reroute P t).Local τ := by
  obtain ⟨hg, hh, h0, h1, h2⟩ := hN
  refine ⟨fun k i => ?_, fun k i => ?_, fun a x y hxy => ?_, fun b x y hxy => ?_,
    fun c x y hxy => ?_⟩
  · rcases k with k | k
    · intro x y hxy
      exact hg k i _ _ fun v hv => hxy (.inl v) hv
    · intro x y hxy
      show (if x (.inr k) = i then (1 : ℂ) else 0) = (if y (.inr k) = i then (1 : ℂ) else 0)
      rw [hxy (.inr k) rfl]
  · rcases k with k | k
    · intro x y hxy
      by_cases hk : P k
      · show (if hk : P k then (if x (.inr ⟨k, hk⟩) = i then (1 : ℂ) else 0)
            else N.h k i (fun v => x (.inl v))) =
          (if hk : P k then (if y (.inr ⟨k, hk⟩) = i then (1 : ℂ) else 0)
            else N.h k i (fun v => y (.inl v)))
        rw [dif_pos hk, dif_pos hk]
        rw [hxy (.inr ⟨k, hk⟩) (show t = (if P k then t else N.e2 k) by rw [if_pos hk])]
      · show (if hk : P k then (if x (.inr ⟨k, hk⟩) = i then (1 : ℂ) else 0)
            else N.h k i (fun v => x (.inl v))) =
          (if hk : P k then (if y (.inr ⟨k, hk⟩) = i then (1 : ℂ) else 0)
            else N.h k i (fun v => y (.inl v)))
        rw [dif_neg hk, dif_neg hk]
        exact hh k i _ _ fun v hv => hxy (.inl v)
          (show N.loc v = (if P k then t else N.e2 k) by rw [if_neg hk, hv])
    · intro x y hxy
      exact hh k.1 i _ _ fun v hv => hxy (.inl v) hv
  · exact h0 a _ _ fun v hv => hxy (.inl v) hv
  · exact h1 b _ _ fun v hv => hxy (.inl v) hv
  · exact h2 c _ _ fun v hv => hxy (.inl v) hv

lemma cost_reroute (d : S → S → ℝ) (N : TN S O0 O1 O2) (P : N.K → Prop) (t : S) :
    (N.reroute P t).cost d = ∑ k, (if P k then d (N.e1 k) t + d t (N.e2 k)
      else d (N.e1 k) (N.e2 k)) * Real.logb 2 (N.r k) := by
  have h1 : (N.reroute P t).cost d = (∑ k : N.K, d (N.e1 k) (if P k then t else N.e2 k) *
      Real.logb 2 (N.r k)) + ∑ k : {k // P k}, d t (N.e2 k.1) * Real.logb 2 (N.r k.1) :=
    Fintype.sum_sum_type _
  rw [h1]
  have h2 : (∑ k : {k // P k}, d t (N.e2 k.1) * Real.logb 2 (N.r k.1)) =
      ∑ k : N.K, if P k then d t (N.e2 k) * Real.logb 2 (N.r k) else 0 := by
    rw [← Finset.sum_filter]
    exact (Finset.sum_subtype (p := P) (Finset.univ.filter P) (fun k => by simp)
      (fun k => d t (N.e2 k) * Real.logb 2 (N.r k))).symm
  rw [h2, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases hk : P k <;> simp [hk] <;> ring

end TN

open TN

/-! ## The admissible set is closed; minimal admissible prices -/

lemma continuous_cost [Fintype S] (N : TN S O0 O1 O2) : Continuous fun d : S → S → ℝ => N.cost d :=
  continuous_finset_sum _ fun k _ => by fun_prop

lemma isClosed_adm [Fintype S] (φ : OM.PolMul.Spectral ℂ) (τ : Fin 3 → S) :
    IsClosed {d : S → S → ℝ | Adm φ τ d} := by
  have h : {d : S → S → ℝ | Adm φ τ d} = ⋂ (O0 : Type) (O1 : Type) (O2 : Type) (i0 : Fintype O0)
      (i1 : Fintype O1) (i2 : Fintype O2) (N : TN S O0 O1 O2) (_ : N.Local τ)
      (_ : 0 < value φ N.Z), {d | Real.logb 2 (value φ N.Z) ≤ N.cost d} := by
    ext d
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    rfl
  rw [h]
  exact isClosed_iInter fun O0 => isClosed_iInter fun O1 => isClosed_iInter fun O2 =>
    isClosed_iInter fun i0 => isClosed_iInter fun i1 => isClosed_iInter fun i2 =>
    isClosed_iInter fun N => isClosed_iInter fun _ => isClosed_iInter fun _ =>
    isClosed_le continuous_const (continuous_cost N)

lemma Adm.mono {φ : OM.PolMul.Spectral ℂ} {τ : Fin 3 → S} {d d' : S → S → ℝ} (hd : Adm φ τ d)
    (h : ∀ s t, d s t ≤ d' s t) : Adm φ τ d' := by
  intro O0 O1 O2 _ _ _ N hN hv
  exact (hd O0 O1 O2 N hN hv).trans (N.cost_mono hv h)

/-- below every admissible, nonnegative vector with zero diagonal there is a minimal one -/
theorem exists_minAdm [Fintype S] {φ : OM.PolMul.Spectral ℂ} {τ : Fin 3 → S} {d0 : S → S → ℝ}
    (had : Adm φ τ d0) (h0 : ∀ s t, 0 ≤ d0 s t) (hdiag : ∀ s, d0 s s = 0) :
    ∃ d, MinAdm φ τ d ∧ ∀ s t, d s t ≤ d0 s t := by
  let C : Set (S → S → ℝ) := {d | Adm φ τ d} ∩ {d | ∀ s t, 0 ≤ d s t ∧ d s t ≤ d0 s t} ∩
    {d | ∀ s, d s s = 0}
  have hbox : IsCompact (Set.univ.pi fun s : S => Set.univ.pi fun t : S => Set.Icc (0 : ℝ) (d0 s t)) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_Icc
  have hC : IsCompact C := by
    apply hbox.of_isClosed_subset
    · refine ((isClosed_adm φ τ).inter ?_).inter ?_
      · simp only [Set.ofPred_forall]
        exact isClosed_iInter fun s => isClosed_iInter fun t =>
          (isClosed_le continuous_const (by fun_prop : Continuous fun d : S → S → ℝ => d s t)).inter
            (isClosed_le (by fun_prop : Continuous fun d : S → S → ℝ => d s t) continuous_const)
      · simp only [Set.ofPred_forall]
        exact isClosed_iInter fun s =>
          isClosed_eq (by fun_prop : Continuous fun d : S → S → ℝ => d s s) continuous_const
    · intro d hd
      simp only [Set.mem_pi, Set.mem_univ, Set.mem_Icc, forall_const]
      exact fun s t => hd.1.2 s t
  have hne : C.Nonempty := ⟨d0, ⟨had, fun s t => ⟨h0 s t, le_rfl⟩⟩, hdiag⟩
  have hcont : ContinuousOn (fun d : S → S → ℝ => ∑ s, ∑ t, d s t) C :=
    (continuous_finset_sum _ fun s _ => continuous_finset_sum _ fun t _ =>
      (by fun_prop : Continuous fun d : S → S → ℝ => d s t)).continuousOn
  obtain ⟨d, hd, hmin⟩ := hC.exists_isMinOn hne hcont
  refine ⟨d, ⟨hd.1.1, fun s t => (hd.1.2 s t).1, hd.2, ?_⟩, fun s t => (hd.1.2 s t).2⟩
  intro d' had' h0' hdiag' hle
  have hd'C : d' ∈ C := ⟨⟨had', fun s t => ⟨h0' s t, (hle s t).trans (hd.1.2 s t).2⟩⟩, hdiag'⟩
  have h1 : ∑ s, ∑ t, d s t ≤ ∑ s, ∑ t, d' s t := hmin hd'C
  have h2 : ∀ s, ∑ t, d' s t ≤ ∑ t, d s t := fun s => Finset.sum_le_sum fun t _ => hle s t
  have heq : ∀ s, ∑ t, d' s t = ∑ t, d s t := by
    have := (Finset.sum_eq_sum_iff_of_le fun s _ => h2 s).1
      (le_antisymm (Finset.sum_le_sum fun s _ => h2 s) h1)
    exact fun s => this s (Finset.mem_univ s)
  funext s t
  exact (Finset.sum_eq_sum_iff_of_le fun t _ => hle s t).1 (heq s) t (Finset.mem_univ t)

/-- a minimal admissible vector is symmetric -/
theorem MinAdm.symm {φ : OM.PolMul.Spectral ℂ} {τ : Fin 3 → S} {d : S → S → ℝ}
    (hd : MinAdm φ τ d) (s u : S) : d s u = d u s := by
  have key : ∀ s u, d s u ≤ d u s := by
    intro s u
    by_contra hlt'
    have hlt := not_le.mp hlt'
    let d' : S → S → ℝ := fun a b => if a = s ∧ b = u then d u s else d a b
    have hadm : Adm φ τ d' := by
      intro O0 O1 O2 _ _ _ N hN hv
      let P : N.K → Prop := fun k => N.e1 k = s ∧ N.e2 k = u
      have h := hd.1 O0 O1 O2 (N.rev P) (hN.rev P) (by rw [Z_rev]; exact hv)
      rw [Z_rev, cost_rev] at h
      refine h.trans (le_of_eq (Finset.sum_congr rfl fun k _ => ?_))
      congr 1
      by_cases hk : P k
      · rw [if_pos hk]
        show d (N.e2 k) (N.e1 k) =
          (if N.e1 k = s ∧ N.e2 k = u then d u s else d (N.e1 k) (N.e2 k))
        rw [if_pos hk, hk.1, hk.2]
      · rw [if_neg hk]
        show d (N.e1 k) (N.e2 k) =
          (if N.e1 k = s ∧ N.e2 k = u then d u s else d (N.e1 k) (N.e2 k))
        rw [if_neg hk]
    have h0' : ∀ a b, 0 ≤ d' a b := fun a b => by
      simp only [d']; split_ifs
      · exact hd.2.1 u s
      · exact hd.2.1 a b
    have hdiag' : ∀ a, d' a a = 0 := fun a => by
      simp only [d']; split_ifs with h
      · obtain ⟨rfl, rfl⟩ := h; exact hd.2.2.1 a
      · exact hd.2.2.1 a
    have hle : ∀ a b, d' a b ≤ d a b := fun a b => by
      simp only [d']; split_ifs with h
      · obtain ⟨rfl, rfl⟩ := h; exact hlt.le
      · exact le_rfl
    have := hd.2.2.2 d' hadm h0' hdiag' hle
    have hsu : d' s u = d s u := by rw [this]
    simp only [d', and_self, if_true] at hsu
    linarith
  exact le_antisymm (key s u) (key u s)

/-- a minimal admissible vector satisfies the triangle inequality -/
theorem MinAdm.triangle {φ : OM.PolMul.Spectral ℂ} {τ : Fin 3 → S} {d : S → S → ℝ}
    (hd : MinAdm φ τ d) (s t u : S) : d s u ≤ d s t + d t u := by
  by_contra hlt'
  have hlt := not_le.mp hlt'
  have hsu : s ≠ u := by
    rintro rfl
    rw [hd.2.2.1 s] at hlt
    linarith [hd.2.1 s t, hd.2.1 t s]
  let d' : S → S → ℝ := fun a b => if a = s ∧ b = u then d s t + d t u else d a b
  have hadm : Adm φ τ d' := by
    intro O0 O1 O2 _ _ _ N hN hv
    let P : N.K → Prop := fun k => N.e1 k = s ∧ N.e2 k = u
    have h := hd.1 O0 O1 O2 (N.reroute P t) (hN.reroute P t) (by rw [Z_reroute]; exact hv)
    rw [Z_reroute, cost_reroute] at h
    refine h.trans (le_of_eq (Finset.sum_congr rfl fun k _ => ?_))
    congr 1
    by_cases hk : P k
    · rw [if_pos hk]
      show d (N.e1 k) t + d t (N.e2 k) =
        (if N.e1 k = s ∧ N.e2 k = u then d s t + d t u else d (N.e1 k) (N.e2 k))
      rw [if_pos hk, hk.1, hk.2]
    · rw [if_neg hk]
      show d (N.e1 k) (N.e2 k) =
        (if N.e1 k = s ∧ N.e2 k = u then d s t + d t u else d (N.e1 k) (N.e2 k))
      rw [if_neg hk]
  have h0' : ∀ a b, 0 ≤ d' a b := fun a b => by
    simp only [d']; split_ifs
    · exact add_nonneg (hd.2.1 s t) (hd.2.1 t u)
    · exact hd.2.1 a b
  have hdiag' : ∀ a, d' a a = 0 := fun a => by
    simp only [d']; split_ifs with h
    · exact absurd (h.1.symm.trans h.2) hsu
    · exact hd.2.2.1 a
  have hle : ∀ a b, d' a b ≤ d a b := fun a b => by
    simp only [d']; split_ifs with h
    · obtain ⟨rfl, rfl⟩ := h; exact hlt.le
    · exact le_rfl
  have := hd.2.2.2 d' hadm h0' hdiag' hle
  have hsu' : d' s u = d s u := by rw [this]
  simp only [d', and_self, if_true] at hsu'
  linarith

end OM.NNN30.Net
