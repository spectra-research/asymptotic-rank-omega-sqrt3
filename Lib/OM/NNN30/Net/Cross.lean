import Lib.OM.NNN30.Net.Rect

/-! # The crossing expansion of a network on the grid

For a network `N` on `V × V` and a rectangle `R`, the factors on the diagonal `{z, ∞}` (`D1 R`) and
on the diagonal `{0, 1}` (`D2 R`) multiply to `Σ_{I,I',J,J'} [I = I'][J = J'] GZ(I) G∞(I') G0(J)
G1(J')`, a product of two equalities on the index sets `I1 R`, `I2 R`.  Given crossing pieces
`B m` summing to the product of two equalities on larger index sets (`Bp`, with embeddings `ε1`,
`ε2`), the product of the diagonal factors is `Σ_m Φ R m` (`prod_diag_eq_sum`). -/

noncomputable section
open scoped BigOperators Classical

namespace OM.NNN30.Net

open CoordinateTensor OM.NNN.Raw

variable {V : Type} [Fintype V] [LinearOrder V] {O0 O1 O2 : Type}

lemma sum_comm_out4 {α β γ δ ε : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    [Fintype ε] (f : α → β → γ → δ → ε → ℂ) :
    (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, f a b c d e) = ∑ b, ∑ c, ∑ d, ∑ e, ∑ a, f a b c d e := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Finset.sum_comm]

namespace TN

variable (N : TN (V × V) O0 O1 O2)

/-- the half of factor `k` at the site `u` -/
def half (k : N.K) (u : V × V) (i : Fin (N.r k)) (x : (v : N.V) → N.T v) : ℂ :=
  if N.e1 k = u then N.g k i x else N.h k i x

lemma F_eq_half {k : N.K} {u u' : V × V}
    (h : (N.e1 k = u ∧ N.e2 k = u') ∨ (N.e1 k = u' ∧ N.e2 k = u)) (hne : u ≠ u')
    (x : (v : N.V) → N.T v) : N.F k x = ∑ i, N.half k u i x * N.half k u' i x := by
  unfold F half
  rcases h with ⟨h1, _⟩ | ⟨h1, _⟩
  · simp only [h1, if_true, if_neg hne]
  · simp only [h1, if_neg (Ne.symm hne), if_true, mul_comm]

lemma half_dep {τ : Fin 3 → V × V} (hN : N.Local τ) {k : N.K} {u : V × V}
    (h : N.e1 k = u ∨ N.e2 k = u) (i : Fin (N.r k)) : N.DepAt u (N.half k u i) := by
  intro x y hxy
  unfold half
  by_cases h1 : N.e1 k = u
  · simp only [h1, if_true]
    exact hN.1 k i x y fun v hv => hxy v (hv.trans h1)
  · simp only [h1, if_false]
    have h2 : N.e2 k = u := h.resolve_left h1
    exact hN.2.1 k i x y fun v hv => hxy v (hv.trans h2)

/-- factors on the diagonal `{z, ∞}` of `R` -/
abbrev D1 (R : Rect V) := {k : N.K // N.cls k = some (R, true)}
/-- factors on the diagonal `{0, 1}` of `R` -/
abbrev D2 (R : Rect V) := {k : N.K // N.cls k = some (R, false)}
/-- axis factors -/
abbrev Dn := {k : N.K // N.cls k = none}

/-- index sets of the two diagonals -/
abbrev I1 (R : Rect V) := (k : N.D1 R) → Fin (N.r k.1)
abbrev I2 (R : Rect V) := (k : N.D2 R) → Fin (N.r k.1)

def GZ (R : Rect V) (I : N.I1 R) (x : (v : N.V) → N.T v) : ℂ :=
  ∏ k : N.D1 R, N.half k.1 R.z (I k) x
def GW (R : Rect V) (I : N.I1 R) (x : (v : N.V) → N.T v) : ℂ :=
  ∏ k : N.D1 R, N.half k.1 R.w (I k) x
def G0 (R : Rect V) (J : N.I2 R) (x : (v : N.V) → N.T v) : ℂ :=
  ∏ k : N.D2 R, N.half k.1 R.p0 (J k) x
def G1 (R : Rect V) (J : N.I2 R) (x : (v : N.V) → N.T v) : ℂ :=
  ∏ k : N.D2 R, N.half k.1 R.p1 (J k) x

lemma z_ne_w (R : Rect V) : R.z ≠ R.w := fun h => R.a_lt_c.ne (congrArg Prod.fst h)
lemma p0_ne_p1 (R : Rect V) : R.p0 ≠ R.p1 := fun h => R.a_lt_c.ne (congrArg Prod.fst h)

lemma prod_D1 (R : Rect V) (x : (v : N.V) → N.T v) :
    (∏ k : N.D1 R, N.F k.1 x) = ∑ I : N.I1 R, N.GZ R I x * N.GW R I x := by
  have hF : ∀ k : N.D1 R, N.F k.1 x = ∑ i, N.half k.1 R.z i x * N.half k.1 R.w i x :=
    fun k => N.F_eq_half (classify_eq_true k.2) (z_ne_w R) x
  simp only [hF]
  rw [Fintype.prod_sum]
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [GZ, GW, ← Finset.prod_mul_distrib]

lemma prod_D2 (R : Rect V) (x : (v : N.V) → N.T v) :
    (∏ k : N.D2 R, N.F k.1 x) = ∑ J : N.I2 R, N.G0 R J x * N.G1 R J x := by
  have hF : ∀ k : N.D2 R, N.F k.1 x = ∑ i, N.half k.1 R.p0 i x * N.half k.1 R.p1 i x :=
    fun k => N.F_eq_half (classify_eq_false k.2) (p0_ne_p1 R) x
  simp only [hF]
  rw [Fintype.prod_sum]
  refine Finset.sum_congr rfl fun J _ => ?_
  rw [G0, G1, ← Finset.prod_mul_distrib]

/-- the product of all factors, by classes -/
lemma prod_F_classes (x : (v : N.V) → N.T v) :
    (∏ k, N.F k x) = (∏ k : N.Dn, N.F k.1 x) *
      ∏ R : Rect V, ((∏ k : N.D1 R, N.F k.1 x) * ∏ k : N.D2 R, N.F k.1 x) := by
  rw [← Fintype.prod_fiberwise N.cls (fun k => N.F k x), Fintype.prod_option,
    Fintype.prod_prod_type]
  congr 1
  refine Finset.prod_congr rfl fun R _ => ?_
  rw [Fintype.prod_bool]

/-! ## The expansion with crossing pieces -/

variable {K A B : Rect V → ℕ}
  (Bp : (R : Rect V) → Fin (K R) → Fin (A R) → Fin (B R) → Fin (B R) → Fin (A R) → ℂ)
  (ε1 : (R : Rect V) → N.I1 R ↪ Fin (A R)) (ε2 : (R : Rect V) → N.I2 R ↪ Fin (B R))

/-- the piece `m` of rectangle `R`, as a function of the variables -/
def Phi (R : Rect V) (m : Fin (K R)) (x : (v : N.V) → N.T v) : ℂ :=
  ∑ I : N.I1 R, ∑ J : N.I2 R, ∑ J' : N.I2 R, ∑ I' : N.I1 R,
    Bp R m (ε1 R I) (ε2 R J) (ε2 R J') (ε1 R I') *
      (N.GZ R I x * N.G0 R J x * N.G1 R J' x * N.GW R I' x)

lemma prod_diag_eq_sum
    (hB : ∀ R z y y' z', ∑ m, Bp R m z y y' z' = if z = z' ∧ y = y' then 1 else 0)
    (R : Rect V) (x : (v : N.V) → N.T v) :
    (∏ k : N.D1 R, N.F k.1 x) * (∏ k : N.D2 R, N.F k.1 x) = ∑ m, N.Phi Bp ε1 ε2 R m x := by
  rw [N.prod_D1, N.prod_D2]
  unfold Phi
  rw [sum_comm_out4 (fun m I J J' I' => Bp R m (ε1 R I) (ε2 R J) (ε2 R J') (ε1 R I') *
    (N.GZ R I x * N.G0 R J x * N.G1 R J' x * N.GW R I' x))]
  simp_rw [← Finset.sum_mul, hB]
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun J _ => ?_
  rw [Finset.sum_eq_single J, Finset.sum_eq_single I]
  · simp only [(ε1 R).injective.eq_iff, (ε2 R).injective.eq_iff, and_self, if_true, one_mul]
    ring
  · intro I' _ hI'
    simp [(ε1 R).injective.eq_iff, Ne.symm hI']
  · simp
  · intro J' _ hJ'
    refine Finset.sum_eq_zero fun I' _ => ?_
    simp [(ε2 R).injective.eq_iff, hJ', Ne.symm hJ']
  · simp

/-! ## Rank factorisations of the pieces -/

end TN

lemma exists_rank_factor {m n : Type} [Fintype m] [Fintype n] (M : Matrix m n ℂ) :
    ∃ (U : m → Fin M.rank → ℂ) (W : Fin M.rank → n → ℂ), ∀ i j, M i j = ∑ l, U i l * W l j := by
  let Sp : Submodule ℂ (m → ℂ) := Submodule.span ℂ (Set.range M.transpose)
  have hdim : Module.finrank ℂ Sp = M.rank := (Matrix.rank_eq_finrank_span_cols M).symm
  let bs : Module.Basis (Fin M.rank) ℂ Sp := Module.finBasisOfFinrankEq ℂ Sp hdim
  have hmem : ∀ j, M.transpose j ∈ Sp := fun j => Submodule.subset_span ⟨j, rfl⟩
  refine ⟨fun i l => (bs l : m → ℂ) i, fun l j => bs.repr ⟨M.transpose j, hmem j⟩ l, fun i j => ?_⟩
  have h := bs.sum_repr ⟨M.transpose j, hmem j⟩
  have h' := congrArg (fun v : Sp => (v : m → ℂ) i) h
  simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul] at h'
  have h'' : ∑ l, bs.repr ⟨M.transpose j, hmem j⟩ l * (bs l : m → ℂ) i = M i j := h'
  rw [← h'']
  exact Finset.sum_congr rfl fun l _ => mul_comm _ _

namespace TN

variable (N : TN (V × V) O0 O1 O2)
variable {K A B : Rect V → ℕ}
  (Bp : (R : Rect V) → Fin (K R) → Fin (A R) → Fin (B R) → Fin (B R) → Fin (A R) → ℂ)
  (ε1 : (R : Rect V) → N.I1 R ↪ Fin (A R)) (ε2 : (R : Rect V) → N.I2 R ↪ Fin (B R))

/-- the row flattening `z0 | 1∞` of a piece -/
def rowMat (R : Rect V) (m : Fin (K R)) : Matrix (Fin (A R) × Fin (B R)) (Fin (B R) × Fin (A R)) ℂ :=
  Matrix.of fun zx yw => Bp R m zx.1 zx.2 yw.1 yw.2

/-- the column flattening `z1 | 0∞` of a piece -/
def colMat (R : Rect V) (m : Fin (K R)) : Matrix (Fin (A R) × Fin (B R)) (Fin (B R) × Fin (A R)) ℂ :=
  Matrix.of fun zy xw => Bp R m zy.1 xw.1 zy.2 xw.2

def URow (R : Rect V) (m : Fin (K R)) := (exists_rank_factor (rowMat Bp R m)).choose
def WRow (R : Rect V) (m : Fin (K R)) := (exists_rank_factor (rowMat Bp R m)).choose_spec.choose
lemma row_factor (R : Rect V) (m : Fin (K R)) (z : Fin (A R)) (y y' : Fin (B R)) (z' : Fin (A R)) :
    Bp R m z y y' z' = ∑ l, URow Bp R m (z, y) l * WRow Bp R m l (y', z') :=
  (exists_rank_factor (rowMat Bp R m)).choose_spec.choose_spec (z, y) (y', z')

def UCol (R : Rect V) (m : Fin (K R)) := (exists_rank_factor (colMat Bp R m)).choose
def WCol (R : Rect V) (m : Fin (K R)) := (exists_rank_factor (colMat Bp R m)).choose_spec.choose
lemma col_factor (R : Rect V) (m : Fin (K R)) (z : Fin (A R)) (y y' : Fin (B R)) (z' : Fin (A R)) :
    Bp R m z y y' z' = ∑ l, UCol Bp R m (z, y') l * WCol Bp R m l (y, z') :=
  (exists_rank_factor (colMat Bp R m)).choose_spec.choose_spec (z, y') (y, z')

/-- the row realisation of a piece: halves at rows `a` and `c` -/
def rowLeft (R : Rect V) (m : Fin (K R)) (l : Fin (rowMat Bp R m).rank)
    (x : (v : N.V) → N.T v) : ℂ :=
  ∑ I : N.I1 R, ∑ J : N.I2 R, URow Bp R m (ε1 R I, ε2 R J) l * (N.GZ R I x * N.G0 R J x)
def rowRight (R : Rect V) (m : Fin (K R)) (l : Fin (rowMat Bp R m).rank)
    (x : (v : N.V) → N.T v) : ℂ :=
  ∑ J' : N.I2 R, ∑ I' : N.I1 R, WRow Bp R m l (ε2 R J', ε1 R I') * (N.G1 R J' x * N.GW R I' x)

/-- the column realisation of a piece: halves at columns `b` and `e` -/
def colLeft (R : Rect V) (m : Fin (K R)) (l : Fin (colMat Bp R m).rank)
    (x : (v : N.V) → N.T v) : ℂ :=
  ∑ I : N.I1 R, ∑ J' : N.I2 R, UCol Bp R m (ε1 R I, ε2 R J') l * (N.GZ R I x * N.G1 R J' x)
def colRight (R : Rect V) (m : Fin (K R)) (l : Fin (colMat Bp R m).rank)
    (x : (v : N.V) → N.T v) : ℂ :=
  ∑ J : N.I2 R, ∑ I' : N.I1 R, WCol Bp R m l (ε2 R J, ε1 R I') * (N.G0 R J x * N.GW R I' x)

lemma sum_row (R : Rect V) (m : Fin (K R)) (x : (v : N.V) → N.T v) :
    (∑ l, N.rowLeft Bp ε1 ε2 R m l x * N.rowRight Bp ε1 ε2 R m l x) = N.Phi Bp ε1 ε2 R m x := by
  have hl : ∀ l, N.rowLeft Bp ε1 ε2 R m l x * N.rowRight Bp ε1 ε2 R m l x =
      ∑ I : N.I1 R, ∑ J : N.I2 R, ∑ J' : N.I2 R, ∑ I' : N.I1 R,
        URow Bp R m (ε1 R I, ε2 R J) l * (N.GZ R I x * N.G0 R J x) *
          (WRow Bp R m l (ε2 R J', ε1 R I') * (N.G1 R J' x * N.GW R I' x)) := by
    intro l
    unfold rowLeft rowRight
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun I _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun J _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun J' _ => ?_
    rw [Finset.mul_sum]
  simp only [hl]
  unfold Phi
  rw [sum_comm_out4 (fun l I J J' I' => URow Bp R m (ε1 R I, ε2 R J) l * (N.GZ R I x * N.G0 R J x) *
    (WRow Bp R m l (ε2 R J', ε1 R I') * (N.G1 R J' x * N.GW R I' x)))]
  refine Finset.sum_congr rfl fun I _ => Finset.sum_congr rfl fun J _ =>
    Finset.sum_congr rfl fun J' _ => Finset.sum_congr rfl fun I' _ => ?_
  rw [row_factor Bp R m, Finset.sum_mul]
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

lemma sum_col (R : Rect V) (m : Fin (K R)) (x : (v : N.V) → N.T v) :
    (∑ l, N.colLeft Bp ε1 ε2 R m l x * N.colRight Bp ε1 ε2 R m l x) = N.Phi Bp ε1 ε2 R m x := by
  have hl : ∀ l, N.colLeft Bp ε1 ε2 R m l x * N.colRight Bp ε1 ε2 R m l x =
      ∑ I : N.I1 R, ∑ J' : N.I2 R, ∑ J : N.I2 R, ∑ I' : N.I1 R,
        UCol Bp R m (ε1 R I, ε2 R J') l * (N.GZ R I x * N.G1 R J' x) *
          (WCol Bp R m l (ε2 R J, ε1 R I') * (N.G0 R J x * N.GW R I' x)) := by
    intro l
    unfold colLeft colRight
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun I _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun J' _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun J _ => ?_
    rw [Finset.mul_sum]
  simp only [hl]
  unfold Phi
  rw [sum_comm_out4 (fun l I J' J I' => UCol Bp R m (ε1 R I, ε2 R J') l *
    (N.GZ R I x * N.G1 R J' x) * (WCol Bp R m l (ε2 R J, ε1 R I') * (N.G0 R J x * N.GW R I' x)))]
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun J _ => Finset.sum_congr rfl fun J' _ =>
    Finset.sum_congr rfl fun I' _ => ?_
  rw [col_factor Bp R m, Finset.sum_mul]
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

/-! ## Dependence on sets of variables -/

/-- `f` reads only the variables satisfying `P` -/
def DepOn (P : N.V → Prop) (f : ((v : N.V) → N.T v) → ℂ) : Prop :=
  ∀ x y : (v : N.V) → N.T v, (∀ v, P v → x v = y v) → f x = f y

omit [Fintype V] [LinearOrder V] in
lemma DepOn.mul {P : N.V → Prop} {f g : ((v : N.V) → N.T v) → ℂ} (hf : N.DepOn P f)
    (hg : N.DepOn P g) : N.DepOn P (fun x => f x * g x) := fun x y h => by
  show f x * g x = f y * g y
  rw [hf x y h, hg x y h]

omit [Fintype V] [LinearOrder V] in
lemma DepOn.sum {ι : Type} [Fintype ι] {P : N.V → Prop} {f : ι → ((v : N.V) → N.T v) → ℂ}
    (hf : ∀ i, N.DepOn P (f i)) : N.DepOn P (fun x => ∑ i, f i x) := fun x y h =>
  Finset.sum_congr rfl fun i _ => hf i x y h

omit [Fintype V] [LinearOrder V] in
lemma DepOn.prod {ι : Type} [Fintype ι] {P : N.V → Prop} {f : ι → ((v : N.V) → N.T v) → ℂ}
    (hf : ∀ i, N.DepOn P (f i)) : N.DepOn P (fun x => ∏ i, f i x) := fun x y h =>
  Finset.prod_congr rfl fun i _ => hf i x y h

omit [Fintype V] [LinearOrder V] in
lemma DepOn.const_mul {P : N.V → Prop} (c : ℂ) {f : ((v : N.V) → N.T v) → ℂ}
    (hf : N.DepOn P f) : N.DepOn P (fun x => c * f x) := fun x y h => by
  show c * f x = c * f y
  rw [hf x y h]

omit [Fintype V] [LinearOrder V] in
lemma DepOn.mono {P Q : N.V → Prop} {f : ((v : N.V) → N.T v) → ℂ} (hf : N.DepOn P f)
    (h : ∀ v, P v → Q v) : N.DepOn Q f := fun x y hxy => hf x y fun v hv => hxy v (h v hv)

omit [Fintype V] [LinearOrder V] in
lemma depOn_of_depAt {u : V × V} {f : ((v : N.V) → N.T v) → ℂ} (hf : N.DepAt u f) :
    N.DepOn (fun v => N.loc v = u) f := hf

lemma GZ_dep {τ : Fin 3 → V × V} (hN : N.Local τ) (R : Rect V) (I : N.I1 R) :
    N.DepOn (fun v => N.loc v = R.z) (N.GZ R I) :=
  DepOn.prod N fun k => depOn_of_depAt N (N.half_dep hN
    ((classify_eq_true k.2).elim (fun h => Or.inl h.1) (fun h => Or.inr h.2)) _)

lemma GW_dep {τ : Fin 3 → V × V} (hN : N.Local τ) (R : Rect V) (I : N.I1 R) :
    N.DepOn (fun v => N.loc v = R.w) (N.GW R I) :=
  DepOn.prod N fun k => depOn_of_depAt N (N.half_dep hN
    ((classify_eq_true k.2).elim (fun h => Or.inr h.2) (fun h => Or.inl h.1)) _)

lemma G0_dep {τ : Fin 3 → V × V} (hN : N.Local τ) (R : Rect V) (J : N.I2 R) :
    N.DepOn (fun v => N.loc v = R.p0) (N.G0 R J) :=
  DepOn.prod N fun k => depOn_of_depAt N (N.half_dep hN
    ((classify_eq_false k.2).elim (fun h => Or.inl h.1) (fun h => Or.inr h.2)) _)

lemma G1_dep {τ : Fin 3 → V × V} (hN : N.Local τ) (R : Rect V) (J : N.I2 R) :
    N.DepOn (fun v => N.loc v = R.p1) (N.G1 R J) :=
  DepOn.prod N fun k => depOn_of_depAt N (N.half_dep hN
    ((classify_eq_false k.2).elim (fun h => Or.inr h.2) (fun h => Or.inl h.1)) _)

/-! ## The expansion and the two realisations -/

/-- the summand `μ` of the expansion: piece `μ R` in every rectangle `R` -/
def Zmu (μ : (R : Rect V) → Fin (K R)) : Tensor ℂ O0 O1 O2 := fun a b c =>
  ∑ x : (v : N.V) → N.T v, N.out0 x a * N.out1 x b * N.out2 x c *
    ((∏ k : N.Dn, N.F k.1 x) * ∏ R, N.Phi Bp ε1 ε2 R (μ R) x)

lemma Z_eq_sum_Zmu
    (hB : ∀ R z y y' z', ∑ m, Bp R m z y y' z' = if z = z' ∧ y = y' then 1 else 0) :
    N.Z = ∑ μ : (R : Rect V) → Fin (K R), N.Zmu Bp ε1 ε2 μ := by
  funext a b c
  simp only [Finset.sum_apply]
  unfold Z Zmu
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [N.prod_F_classes x]
  simp only [N.prod_diag_eq_sum Bp ε1 ε2 hB]
  rw [Fintype.prod_sum, Finset.mul_sum, Finset.mul_sum]

/-- the row realisation: merge the sites of each row -/
def rowNet (μ : (R : Rect V) → Fin (K R)) : TN V O0 O1 O2 where
  V := N.V
  T := N.T
  loc := fun v => (N.loc v).1
  K := N.Dn ⊕ Rect V
  e1 := Sum.elim (fun k => (N.e1 k.1).1) (fun R => R.a)
  e2 := Sum.elim (fun k => (N.e2 k.1).1) (fun R => R.c)
  r := Sum.elim (fun k => N.r k.1) (fun R => (rowMat Bp R (μ R)).rank)
  g := fun k => match k with
    | .inl k => N.g k.1
    | .inr R => N.rowLeft Bp ε1 ε2 R (μ R)
  h := fun k => match k with
    | .inl k => N.h k.1
    | .inr R => N.rowRight Bp ε1 ε2 R (μ R)
  out0 := N.out0
  out1 := N.out1
  out2 := N.out2

/-- the column realisation: merge the sites of each column -/
def colNet (μ : (R : Rect V) → Fin (K R)) : TN V O0 O1 O2 where
  V := N.V
  T := N.T
  loc := fun v => (N.loc v).2
  K := N.Dn ⊕ Rect V
  e1 := Sum.elim (fun k => (N.e1 k.1).2) (fun R => R.b)
  e2 := Sum.elim (fun k => (N.e2 k.1).2) (fun R => R.e)
  r := Sum.elim (fun k => N.r k.1) (fun R => (colMat Bp R (μ R)).rank)
  g := fun k => match k with
    | .inl k => N.g k.1
    | .inr R => N.colLeft Bp ε1 ε2 R (μ R)
  h := fun k => match k with
    | .inl k => N.h k.1
    | .inr R => N.colRight Bp ε1 ε2 R (μ R)
  out0 := N.out0
  out1 := N.out1
  out2 := N.out2

lemma Z_rowNet (μ : (R : Rect V) → Fin (K R)) : (N.rowNet Bp ε1 ε2 μ).Z = N.Zmu Bp ε1 ε2 μ := by
  funext a b c
  refine Finset.sum_congr rfl fun x _ => ?_
  have hp : (∏ k, (N.rowNet Bp ε1 ε2 μ).F k x) =
      (∏ k : N.Dn, (N.rowNet Bp ε1 ε2 μ).F (.inl k) x) *
        ∏ R : Rect V, (N.rowNet Bp ε1 ε2 μ).F (.inr R) x := Fintype.prod_sum_type _
  have h1 : ∀ k : N.Dn, (N.rowNet Bp ε1 ε2 μ).F (.inl k) x = N.F k.1 x := fun k => rfl
  have h2 : ∀ R : Rect V, (N.rowNet Bp ε1 ε2 μ).F (.inr R) x = N.Phi Bp ε1 ε2 R (μ R) x :=
    fun R => N.sum_row Bp ε1 ε2 R (μ R) x
  show (N.rowNet Bp ε1 ε2 μ).out0 x a * (N.rowNet Bp ε1 ε2 μ).out1 x b *
    (N.rowNet Bp ε1 ε2 μ).out2 x c * ∏ k, (N.rowNet Bp ε1 ε2 μ).F k x = _
  rw [hp]
  simp only [h1, h2]
  rfl

lemma Z_colNet (μ : (R : Rect V) → Fin (K R)) : (N.colNet Bp ε1 ε2 μ).Z = N.Zmu Bp ε1 ε2 μ := by
  funext a b c
  refine Finset.sum_congr rfl fun x _ => ?_
  have hp : (∏ k, (N.colNet Bp ε1 ε2 μ).F k x) =
      (∏ k : N.Dn, (N.colNet Bp ε1 ε2 μ).F (.inl k) x) *
        ∏ R : Rect V, (N.colNet Bp ε1 ε2 μ).F (.inr R) x := Fintype.prod_sum_type _
  have h1 : ∀ k : N.Dn, (N.colNet Bp ε1 ε2 μ).F (.inl k) x = N.F k.1 x := fun k => rfl
  have h2 : ∀ R : Rect V, (N.colNet Bp ε1 ε2 μ).F (.inr R) x = N.Phi Bp ε1 ε2 R (μ R) x :=
    fun R => N.sum_col Bp ε1 ε2 R (μ R) x
  show (N.colNet Bp ε1 ε2 μ).out0 x a * (N.colNet Bp ε1 ε2 μ).out1 x b *
    (N.colNet Bp ε1 ε2 μ).out2 x c * ∏ k, (N.colNet Bp ε1 ε2 μ).F k x = _
  rw [hp]
  simp only [h1, h2]
  rfl

lemma Local_rowNet {τ : Fin 3 → V} (hN : N.Local (fun i => (τ i, τ i)))
    (μ : (R : Rect V) → Fin (K R)) : (N.rowNet Bp ε1 ε2 μ).Local τ := by
  have hN' := hN
  obtain ⟨hg, hh, h0, h1, h2⟩ := hN'
  refine ⟨fun k i => ?_, fun k i => ?_, fun a x y hxy => ?_, fun b x y hxy => ?_,
    fun c x y hxy => ?_⟩
  · rcases k with k | R
    · intro x y hxy
      exact hg k.1 i x y fun v hv => hxy v (show (N.loc v).1 = (N.e1 k.1).1 by rw [hv])
    · have hdep : N.DepOn (fun v => (N.loc v).1 = R.a) (N.rowLeft Bp ε1 ε2 R (μ R) i) :=
        DepOn.sum N fun I => DepOn.sum N fun J => DepOn.const_mul N _
          (DepOn.mul N ((N.GZ_dep hN R I).mono N fun v hv => by rw [hv]; rfl)
            ((N.G0_dep hN R J).mono N fun v hv => by rw [hv]; rfl))
      exact hdep
  · rcases k with k | R
    · intro x y hxy
      exact hh k.1 i x y fun v hv => hxy v (show (N.loc v).1 = (N.e2 k.1).1 by rw [hv])
    · have hdep : N.DepOn (fun v => (N.loc v).1 = R.c) (N.rowRight Bp ε1 ε2 R (μ R) i) :=
        DepOn.sum N fun J => DepOn.sum N fun I => DepOn.const_mul N _
          (DepOn.mul N ((N.G1_dep hN R J).mono N fun v hv => by rw [hv]; rfl)
            ((N.GW_dep hN R I).mono N fun v hv => by rw [hv]; rfl))
      exact hdep
  · exact h0 a x y fun v hv => hxy v (show (N.loc v).1 = τ 0 by rw [hv])
  · exact h1 b x y fun v hv => hxy v (show (N.loc v).1 = τ 1 by rw [hv])
  · exact h2 c x y fun v hv => hxy v (show (N.loc v).1 = τ 2 by rw [hv])

lemma Local_colNet {τ : Fin 3 → V} (hN : N.Local (fun i => (τ i, τ i)))
    (μ : (R : Rect V) → Fin (K R)) : (N.colNet Bp ε1 ε2 μ).Local τ := by
  have hN' := hN
  obtain ⟨hg, hh, h0, h1, h2⟩ := hN'
  refine ⟨fun k i => ?_, fun k i => ?_, fun a x y hxy => ?_, fun b x y hxy => ?_,
    fun c x y hxy => ?_⟩
  · rcases k with k | R
    · intro x y hxy
      exact hg k.1 i x y fun v hv => hxy v (show (N.loc v).2 = (N.e1 k.1).2 by rw [hv])
    · have hdep : N.DepOn (fun v => (N.loc v).2 = R.b) (N.colLeft Bp ε1 ε2 R (μ R) i) :=
        DepOn.sum N fun I => DepOn.sum N fun J => DepOn.const_mul N _
          (DepOn.mul N ((N.GZ_dep hN R I).mono N fun v hv => by rw [hv]; rfl)
            ((N.G1_dep hN R J).mono N fun v hv => by rw [hv]; rfl))
      exact hdep
  · rcases k with k | R
    · intro x y hxy
      exact hh k.1 i x y fun v hv => hxy v (show (N.loc v).2 = (N.e2 k.1).2 by rw [hv])
    · have hdep : N.DepOn (fun v => (N.loc v).2 = R.e) (N.colRight Bp ε1 ε2 R (μ R) i) :=
        DepOn.sum N fun J => DepOn.sum N fun I => DepOn.const_mul N _
          (DepOn.mul N ((N.G0_dep hN R J).mono N fun v hv => by rw [hv]; rfl)
            ((N.GW_dep hN R I).mono N fun v hv => by rw [hv]; rfl))
      exact hdep
  · exact h0 a x y fun v hv => hxy v (show (N.loc v).2 = τ 0 by rw [hv])
  · exact h1 b x y fun v hv => hxy v (show (N.loc v).2 = τ 1 by rw [hv])
  · exact h2 c x y fun v hv => hxy v (show (N.loc v).2 = τ 2 by rw [hv])

lemma cost_rowNet (d : V → V → ℝ) (μ : (R : Rect V) → Fin (K R)) :
    (N.rowNet Bp ε1 ε2 μ).cost d =
      (∑ k : N.Dn, d (N.e1 k.1).1 (N.e2 k.1).1 * Real.logb 2 (N.r k.1)) +
        ∑ R, d R.a R.c * Real.logb 2 ((rowMat Bp R (μ R)).rank) :=
  Fintype.sum_sum_type _

lemma cost_colNet (d : V → V → ℝ) (μ : (R : Rect V) → Fin (K R)) :
    (N.colNet Bp ε1 ε2 μ).cost d =
      (∑ k : N.Dn, d (N.e1 k.1).2 (N.e2 k.1).2 * Real.logb 2 (N.r k.1)) +
        ∑ R, d R.b R.e * Real.logb 2 ((colMat Bp R (μ R)).rank) :=
  Fintype.sum_sum_type _

lemma ndCost_eq (d : V → V → ℝ) :
    N.ndCost d = ∑ k : N.Dn, ap d (N.e1 k.1) (N.e2 k.1) * Real.logb 2 (N.r k.1) := by
  unfold ndCost
  rw [← Finset.sum_filter]
  exact (Finset.sum_subtype (p := fun k => N.cls k = none)
    (Finset.univ.filter (fun k => N.cls k = none))
    (fun k => by simp) (fun k => ap d (N.e1 k) (N.e2 k) * Real.logb 2 (N.r k)))

lemma avg_cost (d : V → V → ℝ) (μ : (R : Rect V) → Fin (K R)) :
    ((N.rowNet Bp ε1 ε2 μ).cost d + (N.colNet Bp ε1 ε2 μ).cost d) / 2 =
      N.ndCost d + ∑ R, (d R.a R.c * Real.logb 2 ((rowMat Bp R (μ R)).rank) +
        d R.b R.e * Real.logb 2 ((colMat Bp R (μ R)).rank)) / 2 := by
  rw [cost_rowNet, cost_colNet, ndCost_eq]
  unfold ap
  have e1 : (∑ k : N.Dn, (d (N.e1 k.1).1 (N.e2 k.1).1 + d (N.e1 k.1).2 (N.e2 k.1).2) / 2 *
      Real.logb 2 (N.r k.1)) = ((∑ k : N.Dn, d (N.e1 k.1).1 (N.e2 k.1).1 * Real.logb 2 (N.r k.1)) +
        ∑ k : N.Dn, d (N.e1 k.1).2 (N.e2 k.1).2 * Real.logb 2 (N.r k.1)) / 2 := by
    rw [← Finset.sum_add_distrib, Finset.sum_div]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  have e2 : (∑ R : Rect V, (d R.a R.c * Real.logb 2 ((rowMat Bp R (μ R)).rank) +
      d R.b R.e * Real.logb 2 ((colMat Bp R (μ R)).rank)) / 2) =
      ((∑ R : Rect V, d R.a R.c * Real.logb 2 ((rowMat Bp R (μ R)).rank)) +
        ∑ R : Rect V, d R.b R.e * Real.logb 2 ((colMat Bp R (μ R)).rank)) / 2 := by
    rw [← Finset.sum_add_distrib, Finset.sum_div]
  rw [e1, e2]
  ring

end TN

/-- **The crossing step at one scale**: a local network on the grid, the crossing
pieces of every rectangle, and admissible prices `d` on `V`.  Some choice `μ` of one (nonzero)
piece per rectangle carries at least a `1 / #choices` share of the value, and that summand is the
output both of the row realisation and of the column realisation on `V`; averaging the two
admissibility bounds gives the axis costs plus, per rectangle,
`(d(a,c) log₂ rank_row + d(b,e) log₂ rank_col)/2`. -/
theorem single_scale {φ : OM.PolMul.Spectral ℂ} {τ : Fin 3 → V} {d : V → V → ℝ}
    (hd : Adm φ τ d) [Fintype O0] [Fintype O1] [Fintype O2] (N : TN (V × V) O0 O1 O2)
    (hN : N.Local (fun i => (τ i, τ i))) (hv : 0 < value φ N.Z)
    {K A B : Rect V → ℕ}
    (Bp : (R : Rect V) → Fin (K R) → Fin (A R) → Fin (B R) → Fin (B R) → Fin (A R) → ℂ)
    (hB : ∀ R z y y' z', ∑ m, Bp R m z y y' z' = if z = z' ∧ y = y' then 1 else 0)
    (ε1 : (R : Rect V) → N.I1 R ↪ Fin (A R)) (ε2 : (R : Rect V) → N.I2 R ↪ Fin (B R)) :
    ∃ μ : (R : Rect V) → Fin (K R), (∀ R, Bp R (μ R) ≠ 0) ∧
      Real.logb 2 (value φ N.Z) ≤ Real.logb 2 (Fintype.card ((R : Rect V) → Fin (K R))) +
        (N.ndCost d + ∑ R, (d R.a R.c * Real.logb 2 ((TN.rowMat Bp R (μ R)).rank) +
          d R.b R.e * Real.logb 2 ((TN.colMat Bp R (μ R)).rank)) / 2) := by
  have hZ := N.Z_eq_sum_Zmu Bp ε1 ε2 hB
  have hne : (Finset.univ : Finset ((R : Rect V) → Fin (K R))).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    rw [hZ, h, Finset.sum_empty, value_zero] at hv
    exact lt_irrefl _ hv
  obtain ⟨μ, -, hμ⟩ :=
    Finset.exists_max_image Finset.univ (fun μ => value φ (N.Zmu Bp ε1 ε2 μ)) hne
  have hsum : value φ N.Z ≤
      Fintype.card ((R : Rect V) → Fin (K R)) * value φ (N.Zmu Bp ε1 ε2 μ) := by
    rw [hZ]
    refine (OM.NNN22.value_sum_le φ Finset.univ _).trans ?_
    calc (∑ μ', value φ (N.Zmu Bp ε1 ε2 μ'))
        ≤ ∑ _μ' : (R : Rect V) → Fin (K R), value φ (N.Zmu Bp ε1 ε2 μ) :=
          Finset.sum_le_sum fun μ' _ => hμ μ' (Finset.mem_univ _)
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hcard : (0 : ℝ) < Fintype.card ((R : Rect V) → Fin (K R)) := by
    exact_mod_cast Fintype.card_pos_iff.2 ⟨μ⟩
  have hvμ : 0 < value φ (N.Zmu Bp ε1 ε2 μ) := by
    by_contra h
    have h' : value φ (N.Zmu Bp ε1 ε2 μ) ≤ 0 := not_lt.mp h
    have := mul_nonpos_of_nonneg_of_nonpos hcard.le h'
    linarith
  refine ⟨μ, fun R hR => ?_, ?_⟩
  · have hz : N.Zmu Bp ε1 ε2 μ = 0 := by
      funext a b c
      refine Finset.sum_eq_zero fun x _ => ?_
      have hphi : N.Phi Bp ε1 ε2 R (μ R) x = 0 := by
        unfold TN.Phi; simp [hR]
      rw [Finset.prod_eq_zero (Finset.mem_univ R) hphi]; simp
    rw [hz, value_zero] at hvμ
    exact lt_irrefl _ hvμ
  · have hrow := hd _ _ _ (N.rowNet Bp ε1 ε2 μ) (N.Local_rowNet Bp ε1 ε2 hN μ)
      (by rw [TN.Z_rowNet]; exact hvμ)
    have hcol := hd _ _ _ (N.colNet Bp ε1 ε2 μ) (N.Local_colNet Bp ε1 ε2 hN μ)
      (by rw [TN.Z_colNet]; exact hvμ)
    rw [TN.Z_rowNet] at hrow
    rw [TN.Z_colNet] at hcol
    have havg := N.avg_cost Bp ε1 ε2 d μ
    have hlog : Real.logb 2 (value φ N.Z) ≤ Real.logb 2 (Fintype.card ((R : Rect V) → Fin (K R))) +
        Real.logb 2 (value φ (N.Zmu Bp ε1 ε2 μ)) := by
      rw [← Real.logb_mul hcard.ne' hvμ.ne']
      exact Real.logb_le_logb_of_le (by norm_num) hv hsum
    linarith

end OM.NNN30.Net
