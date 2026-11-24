import Lib.OM.NNN30.Net.Adm
import PLATFORM.Statements.«R88.1»

/-! # Values of products and powers; the cube witness at a site

`value_kron_of_pos`, `value_pow`: Kronecker products and powers of networks with positive value
have multiplicative values.  `starNet q W`: a dyadic tensor `W` stored at the site `q`, its three
legs sent to the terminals by equality wires; its output is `W`.  Hence an admissible,
nonnegative price vector has `F(1,1,1) ≤ Σ_j d(q, τ j)` at every site `q` (`Fv_le_sum`). -/

noncomputable section
open scoped BigOperators Classical

namespace OM.NNN30.Net

open CoordinateTensor OM.NNN.Raw OM.NNN8 OM.NNN12

variable {S O0 O1 O2 P0 P1 P2 : Type}

lemma nonempty_of_value_pos {I J K : Type} [Fintype I] [Fintype J] [Fintype K]
    {φ : OM.PolMul.Spectral ℂ} {T : Tensor ℂ I J K} (h : 0 < value φ T) :
    Nonempty I ∧ Nonempty J ∧ Nonempty K := by
  by_contra hne
  have hT : T = 0 := by
    funext a b c
    exact absurd ⟨⟨a⟩, ⟨b⟩, ⟨c⟩⟩ hne
  rw [hT, value_zero] at h
  exact lt_irrefl _ h

/-- finite sums do not depend on the `Fintype` instance -/
lemma sum_congr_fintype {α : Type*} (i1 i2 : Fintype α) (f : α → ℂ) :
    @Finset.sum α ℂ _ (@Finset.univ α i1) f = @Finset.sum α ℂ _ (@Finset.univ α i2) f := by
  cases Subsingleton.elim i1 i2; rfl

lemma value_kron_of_pos [Fintype O0] [Fintype O1] [Fintype O2] [Fintype P0] [Fintype P1]
    [Fintype P2] (φ : OM.PolMul.Spectral ℂ) (N : TN S O0 O1 O2) (N' : TN S P0 P1 P2)
    (hv : 0 < value φ N.Z) (hv' : 0 < value φ N'.Z) :
    value φ (N.kron N').Z = value φ N.Z * value φ N'.Z := by
  obtain ⟨h0, h1, h2⟩ := nonempty_of_value_pos hv
  obtain ⟨h0', h1', h2'⟩ := nonempty_of_value_pos hv'
  rw [TN.Z_kron]
  exact OM.NNN3.value_product' φ N.Z N'.Z

lemma value_pow [Fintype O0] [Fintype O1] [Fintype O2] (φ : OM.PolMul.Spectral ℂ)
    (N : TN S O0 O1 O2) (hv : 0 < value φ N.Z) (p : ℕ) :
    value φ (N.pow p).Z = value φ N.Z ^ p := by
  induction p with
  | zero =>
    have h : (N.pow 0).Z = fun (_ : Unit) (_ : Unit) (_ : Unit) => (1 : ℂ) := TN.Z_one
    rw [pow_zero]
    exact (congrArg (value φ) h).trans (OM.NNN22.value_one111 φ)
  | succ p ih =>
    have hp : 0 < value φ (N.pow p).Z := by rw [ih]; exact pow_pos hv p
    have h := value_kron_of_pos φ (N.pow p) N hp hv
    exact h.trans (by rw [ih, pow_succ])

/-! ## The cube witness -/

/-- the indicator `[a = b]` (one fixed decidability instance) -/
def ind {X : Type} (a b : X) : ℂ := if a = b then 1 else 0

lemma ind_self {X : Type} (a : X) : ind a a = 1 := if_pos rfl

lemma ind_of_ne {X : Type} {a b : X} (h : a ≠ b) : ind a b = 0 := if_neg h

lemma ind_eq {X : Type} {a b : X} (h : a = b) : ind a b = 1 := if_pos h

lemma ind_comm {X : Type} (a b : X) : ind a b = ind b a := by
  by_cases h : a = b
  · rw [ind_eq h, ind_eq h.symm]
  · rw [ind_of_ne h, ind_of_ne (Ne.symm h)]

lemma sum_ind_mul_ind {X : Type} {n : ℕ} (e : Fin n ≃ X) (p q : X) :
    (∑ i : Fin n, ind p (e i) * ind q (e i)) = ind p q := by
  rw [Finset.sum_eq_single (e.symm p)]
  · rw [Equiv.apply_symm_apply, ind_self, one_mul, ind_comm]
  · intro i _ hi
    have : p ≠ e i := fun h => hi (by rw [h, Equiv.symm_apply_apply])
    rw [ind_of_ne this, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- `Fin (2^l) ≃ BinaryWord l` -/
def bwEquiv (l : ℕ) : Fin (2 ^ l) ≃ BinaryWord l :=
  (Fintype.equivFinOfCardEq (binary_word_card l)).symm

/-- the three words, by party -/
def trip {w : Shape} (a : BinaryWord (w 0)) (b : BinaryWord (w 1)) (c : BinaryWord (w 2)) :
    (j : Fin 3) → BinaryWord (w j)
  | 0 => a
  | 1 => b
  | 2 => c

/-- the dyadic tensor `W` stored at the site `q`, its legs wired to the terminals -/
def starNet (τ : Fin 3 → S) (q : S) {w : Shape} (W : DyadicTensor w) :
    TN S (BinaryWord (w 0)) (BinaryWord (w 1)) (BinaryWord (w 2)) where
  V := Bool × Fin 3
  T := fun v => BinaryWord (w v.2)
  loc := fun v => if v.1 then τ v.2 else q
  K := Option (Fin 3)
  e1 := fun _ => q
  e2 := fun k => match k with
    | none => q
    | some j => τ j
  r := fun k => match k with
    | none => 1
    | some j => 2 ^ w j
  g := fun k => match k with
    | none => fun _ x => W (x (false, 0)) (x (false, 1)) (x (false, 2))
    | some j => fun i x => ind (x (false, j)) (bwEquiv (w j) i)
  h := fun k => match k with
    | none => fun _ _ => 1
    | some j => fun i x => ind (x (true, j)) (bwEquiv (w j) i)
  out0 := fun x a => ind (x (true, 0)) a
  out1 := fun x b => ind (x (true, 1)) b
  out2 := fun x c => ind (x (true, 2)) c

lemma starNet_F_none (τ : Fin 3 → S) (q : S) {w : Shape} (W : DyadicTensor w)
    (x : (v : (starNet τ q W).V) → (starNet τ q W).T v) :
    (starNet τ q W).F none x = W (x (false, 0)) (x (false, 1)) (x (false, 2)) := by
  show (∑ i : Fin 1, W (x (false, 0)) (x (false, 1)) (x (false, 2)) * 1) = _
  simp

lemma starNet_F_some (τ : Fin 3 → S) (q : S) {w : Shape} (W : DyadicTensor w)
    (x : (v : (starNet τ q W).V) → (starNet τ q W).T v) (j : Fin 3) :
    (starNet τ q W).F (some j) x = @ind (BinaryWord (w j)) (x (false, j)) (x (true, j)) := by
  show (∑ i : Fin (2 ^ w j), @ind (BinaryWord (w j)) (x (false, j)) (bwEquiv (w j) i) *
    @ind (BinaryWord (w j)) (x (true, j)) (bwEquiv (w j) i)) = _
  exact sum_ind_mul_ind _ _ _

lemma Z_starNet (τ : Fin 3 → S) (q : S) {w : Shape} (W : DyadicTensor w) :
    (starNet τ q W).Z = W := by
  funext a b c
  have hprod : ∀ x : (v : (starNet τ q W).V) → (starNet τ q W).T v, (∏ k, (starNet τ q W).F k x) =
      W (x (false, 0)) (x (false, 1)) (x (false, 2)) *
        ∏ j : Fin 3, @ind (BinaryWord (w j)) (x (false, j)) (x (true, j)) := by
    intro x
    have ho : (∏ k, (starNet τ q W).F k x) = (starNet τ q W).F none x *
        ∏ j : Fin 3, (starNet τ q W).F (some j) x := Fintype.prod_option _
    rw [ho, starNet_F_none]
    simp only [starNet_F_some]
  -- the canonical form of the sum
  let G : ((v : Bool × Fin 3) → BinaryWord (w v.2)) → ℂ := fun x =>
    @ind (BinaryWord (w 0)) (x (true, 0)) a * @ind (BinaryWord (w 1)) (x (true, 1)) b *
      @ind (BinaryWord (w 2)) (x (true, 2)) c *
        (W (x (false, 0)) (x (false, 1)) (x (false, 2)) *
          ∏ j : Fin 3, @ind (BinaryWord (w j)) (x (false, j)) (x (true, j)))
  have hcan : (starNet τ q W).Z a b c = ∑ x : (v : Bool × Fin 3) → BinaryWord (w v.2), G x := by
    have e1 : (starNet τ q W).Z a b c =
        ∑ x : (v : (starNet τ q W).V) → (starNet τ q W).T v, G x := by
      refine Finset.sum_congr rfl fun x _ => ?_
      show (starNet τ q W).out0 x a * (starNet τ q W).out1 x b * (starNet τ q W).out2 x c *
        ∏ k, (starNet τ q W).F k x = G x
      rw [hprod x]
      rfl
    rw [e1]
    exact sum_congr_fintype _ _ G
  rw [hcan]
  let x0 : (v : Bool × Fin 3) → BinaryWord (w v.2) := fun v => trip a b c v.2
  rw [Finset.sum_eq_single x0]
  · have hp : ∀ j : Fin 3, @ind (BinaryWord (w j)) (x0 (false, j)) (x0 (true, j)) = 1 :=
      fun j => ind_self _
    show @ind (BinaryWord (w 0)) a a * @ind (BinaryWord (w 1)) b b * @ind (BinaryWord (w 2)) c c *
        (W a b c * ∏ j : Fin 3, @ind (BinaryWord (w j)) (x0 (false, j)) (x0 (true, j))) = W a b c
    rw [ind_self, ind_self, ind_self, Finset.prod_eq_one fun j _ => hp j]
    ring
  · intro x _ hx
    obtain ⟨⟨bb, j⟩, hv⟩ : ∃ v, x v ≠ x0 v := by
      by_contra hcon
      push Not at hcon
      exact hx (funext hcon)
    show @ind (BinaryWord (w 0)) (x (true, 0)) a * @ind (BinaryWord (w 1)) (x (true, 1)) b *
      @ind (BinaryWord (w 2)) (x (true, 2)) c *
        (W (x (false, 0)) (x (false, 1)) (x (false, 2)) *
          ∏ j : Fin 3, @ind (BinaryWord (w j)) (x (false, j)) (x (true, j))) = 0
    by_cases hout : x (true, 0) = a ∧ x (true, 1) = b ∧ x (true, 2) = c
    · have ht : ∀ j : Fin 3, x (true, j) = x0 (true, j) := by
        intro j; fin_cases j
        · exact hout.1
        · exact hout.2.1
        · exact hout.2.2
      cases bb
      · have hne : x (false, j) ≠ x (true, j) := by
          rw [ht j]; exact hv
        have hz : (∏ j : Fin 3, @ind (BinaryWord (w j)) (x (false, j)) (x (true, j))) = 0 :=
          Finset.prod_eq_zero (Finset.mem_univ j) (ind_of_ne hne)
        rw [hz]; ring
      · exact absurd (ht j) hv
    · by_cases h0 : x (true, 0) = a
      · by_cases h1 : x (true, 1) = b
        · have h2 : ¬ x (true, 2) = c := fun h2 => hout ⟨h0, h1, h2⟩
          rw [ind_of_ne h2]; ring
        · rw [ind_of_ne h1]; ring
      · rw [ind_of_ne h0]; ring
  · intro h; exact absurd (Finset.mem_univ _) h

lemma Local_starNet (τ : Fin 3 → S) (q : S) {w : Shape} (W : DyadicTensor w) :
    (starNet τ q W).Local τ := by
  refine ⟨fun k i => ?_, fun k i => ?_, fun a x y hxy => ?_, fun b x y hxy => ?_,
    fun c x y hxy => ?_⟩
  · rcases k with _ | j
    · intro x y hxy
      show W (x (false, 0)) (x (false, 1)) (x (false, 2)) =
        W (y (false, 0)) (y (false, 1)) (y (false, 2))
      rw [hxy (false, 0) rfl, hxy (false, 1) rfl, hxy (false, 2) rfl]
    · intro x y hxy
      show @ind (BinaryWord (w j)) (x (false, j)) (bwEquiv (w j) i) =
        @ind (BinaryWord (w j)) (y (false, j)) (bwEquiv (w j) i)
      rw [hxy (false, j) rfl]
  · rcases k with _ | j
    · intro x y _; rfl
    · intro x y hxy
      show @ind (BinaryWord (w j)) (x (true, j)) (bwEquiv (w j) i) =
        @ind (BinaryWord (w j)) (y (true, j)) (bwEquiv (w j) i)
      rw [hxy (true, j) rfl]
  · show @ind (BinaryWord (w 0)) (x (true, 0)) a = @ind (BinaryWord (w 0)) (y (true, 0)) a
    rw [hxy (true, 0) rfl]
  · show @ind (BinaryWord (w 1)) (x (true, 1)) b = @ind (BinaryWord (w 1)) (y (true, 1)) b
    rw [hxy (true, 1) rfl]
  · show @ind (BinaryWord (w 2)) (x (true, 2)) c = @ind (BinaryWord (w 2)) (y (true, 2)) c
    rw [hxy (true, 2) rfl]

lemma logb_two_pow_nat (l : ℕ) : Real.logb 2 ((2 ^ l : ℕ) : ℝ) = l := by
  rw [Nat.cast_pow, Nat.cast_ofNat, Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one]

lemma cost_starNet (d : S → S → ℝ) (hd : ∀ s, d s s = 0) (τ : Fin 3 → S) (q : S) {w : Shape}
    (W : DyadicTensor w) :
    (starNet τ q W).cost d = d q (τ 0) * w 0 + d q (τ 1) * w 1 + d q (τ 2) * w 2 := by
  show (∑ k : Option (Fin 3), d q ((starNet τ q W).e2 k) * Real.logb 2 ((starNet τ q W).r k)) = _
  rw [Fintype.sum_option, Fin.sum_univ_three]
  show d q q * Real.logb 2 ((1 : ℕ) : ℝ) + (d q (τ 0) * Real.logb 2 ((2 ^ w 0 : ℕ) : ℝ) +
    d q (τ 1) * Real.logb 2 ((2 ^ w 1 : ℕ) : ℝ) + d q (τ 2) * Real.logb 2 ((2 ^ w 2 : ℕ) : ℝ)) = _
  rw [hd, logb_two_pow_nat, logb_two_pow_nat, logb_two_pow_nat]
  ring

/-- **(5)**: at admissible nonnegative prices, every site has distance sum at least `F(1,1,1)` -/
theorem Fv_le_sum {φ : OM.PolMul.Spectral ℂ} {τ : Fin 3 → S} {d : S → S → ℝ}
    (had : Adm φ τ d) (h0 : ∀ s t, 0 ≤ d s t) (hdiag : ∀ s, d s s = 0) (q : S) :
    P2M.R88.Fv φ (fun _ => 1) ≤ d q (τ 0) + d q (τ 1) + d q (τ 2) := by
  have hsum0 : 0 ≤ d q (τ 0) + d q (τ 1) + d q (τ 2) :=
    add_nonneg (add_nonneg (h0 _ _) (h0 _ _)) (h0 _ _)
  show OM.NNN22.Fv φ (fun _ => 1) ≤ _
  refine OM.NNN22.Fv_le_of φ hsum0 fun D w W hD hw => ?_
  by_cases hv : 0 < value φ W
  · have h := had _ _ _ (starNet τ q W) (Local_starNet τ q W) (by rw [Z_starNet]; exact hv)
    rw [Z_starNet, cost_starNet d hdiag] at h
    have hw' : ∀ i, (w i : ℝ) ≤ D := fun i => by simpa using hw i
    have hle : d q (τ 0) * w 0 + d q (τ 1) * w 1 + d q (τ 2) * w 2 ≤
        D * (d q (τ 0) + d q (τ 1) + d q (τ 2)) := by
      have e0 := mul_le_mul_of_nonneg_left (hw' 0) (h0 q (τ 0))
      have e1 := mul_le_mul_of_nonneg_left (hw' 1) (h0 q (τ 1))
      have e2 := mul_le_mul_of_nonneg_left (hw' 2) (h0 q (τ 2))
      linarith
    rw [← Real.rpow_logb (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1) hv]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (h.trans hle)
  · exact (not_lt.mp hv).trans (by positivity)

end OM.NNN30.Net
