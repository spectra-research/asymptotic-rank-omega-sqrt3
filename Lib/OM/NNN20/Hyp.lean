import Lib.OM.NNN20.CatPiece
import Lib.OM.NNN18.Contraction

/-!
# The structural rules behind the finite certificates (statements)

A tariff on a set of log-formats (`TariffOn`) prices every dyadic tensor
whose log-format lies in the set. `TariffOn φ c univ` is `NNN13.AffineBound φ c`.
-/

noncomputable section
open scoped BigOperators
open CoordinateTensor OM.NNN.Raw
open OM.NNN12 (Shape DyadicTensor)

namespace OM.NNN20

/-- `θ` is an upper profile of `φ` (the hypotheses of the network steps) -/
def UpperProfile (φ : PolMul.Spectral ℂ) (θ : Fin 3 → ℝ) : Prop :=
  (∀ i, Foundations.PairUnitExponents.theta φ i ≤ θ i) ∧ (∀ i, θ i ∈ Set.Icc (0 : ℝ) 1) ∧
    θ 0 + θ 1 + θ 2 ≤ 9 / 4

/-- `c` prices every dyadic tensor whose log-format lies in `K` -/
def TariffOn (φ : PolMul.Spectral ℂ) (c : Fin 3 → ℝ) (K : Set (Fin 3 → ℝ)) : Prop :=
  ∀ (v : Shape), (fun i => (v i : ℝ)) ∈ K → ∀ U : DyadicTensor v,
    value φ U ≤ (2 : ℝ) ^ NNN13.plane c (fun i => (v i : ℝ))

/-- `K` is closed under positive scaling -/
def IsConeSet (K : Set (Fin 3 → ℝ)) : Prop :=
  ∀ x ∈ K, ∀ a : ℝ, 0 < a → (fun i => a * x i) ∈ K

/-- the query segment `{Y - ξ d : lo ≤ ξ ≤ hi}` lies in `K` -/
def SegIn (K : Set (Fin 3 → ℝ)) (Y d : Fin 3 → ℝ) (lo hi : ℝ) : Prop :=
  ∀ ξ : ℝ, lo ≤ ξ → ξ ≤ hi → (fun u => Y u - ξ * d u) ∈ K

/-! ## The global source rule -/

/-- the node shapes of global recipes: actions `F_7`/`F_11`, positive ownership weights, a
nonzero anchor, ordinary charging on the retained bond, and the two full bonds either both
triangle-charged or both ordinary -/
def GShape (n : GNode) : Prop :=
  (∀ i, n.act i = F7 ∨ n.act i = F11) ∧ (∀ u, 0 < n.b u) ∧ 0 < n.a 0 + n.a 1 + n.a 2 ∧
    n.tri n.h = false ∧ ((∀ i, i ≠ n.h → n.tri i = true) ∨ ∀ i, n.tri i = false)

def GlobalRule : Prop :=
  ∀ (n : GNode) (φ : PolMul.Spectral ℂ) (θ : Fin 3 → ℝ) (P : Fin 3 → Fin 3 → ℝ),
    GShape n → UpperProfile φ θ → (∀ i, NNN13.AffineBound φ (P i)) → GGates n θ P →
    NNN13.AffineBound φ (fun u => gC n θ P u)

/-! ## The catalysed source rule -/

section RealFormat
variable (n : CNode) (θ : Fin 3 → ℝ) (B : ℚ) (c : Fin 3 → Fin 3 → ℝ)

/-- `Σ_u a_u x_u` for a rational row `a` and a real format `x` -/
def rdot (a : Fin 3 → ℚ) (x : Fin 3 → ℝ) : ℝ :=
  (a 0 : ℝ) * x 0 + (a 1 : ℝ) * x 1 + (a 2 : ℝ) * x 2

/-- the host density `N_f` of the full family `f` at the format `x` -/
def cNx (f : Fin 3) (x : Fin 3 → ℝ) : ℝ := if f = cj n then rdot (cNj n) x else rdot (cNk n) x

/-- the rate `ρ_f` of the full family `f` at the format `x` -/
def cRhoX (f : Fin 3) (x : Fin 3 → ℝ) : ℝ :=
  (NNN13.plane (cLam n θ B c) x + rdot (cts n) x * B -
      (NNN13.plane (c f) x + rdot (cts n) x * csum c f)) * (1 / cBeta n θ c f) -
    cNx n f x * cL n θ c f

/-- the query direction `e_p + e_o` of the full family whose other full party is `o` -/
def qdirR (o : Fin 3) : Fin 3 → ℝ := fun u => if u = n.p ∨ u = o then 1 else 0

/-- the query direction `e_j + e_k` of the retained family -/
def rdirR : Fin 3 → ℝ := fun u => if u = cj n ∨ u = ck n then 1 else 0

/-- the host balance of a full family -/
def BalR (yu tu : ℝ) (ac : Act) : Prop :=
  0 < yu - tu * ((ac.k : ℝ) / ((ac.q : ℝ) - ac.k)) ∧ 0 < tu * (((ac.q : ℝ) - ac.k) / ac.k) - yu

/-- the gates of the full family `f` (other full party `o`, parent domain `K`) at the format `x`:
host balance, `0 < ρ_f < N_f log₂ q_f`, and the parent queries
`x + t_S(x) 1 - ξ (e_p + e_o)` in `K`, either for the whole segment `-ρ_f/2 ≤ ξ ≤ d_f N_f` or,
after the absent-class gate `ρ_f < κ_q(t₀) N_f`, for the shortened segment
`-ρ_f/2 + d_f t₀ N_f ≤ ξ ≤ d_f N_f` -/
def FamRule (K : Set (Fin 3 → ℝ)) (f o : Fin 3) (x : Fin 3 → ℝ) : Prop :=
  BalR (x o) (rdot (cth n) x) (n.act f) ∧
  0 < cRhoX n θ B c f x ∧ cRhoX n θ B c f x < Real.logb 2 (n.act f).q * cNx n f x ∧
  (SegIn K (fun u => x u + rdot (cts n) x) (qdirR n o) (-(cRhoX n θ B c f x) / 2)
      ((n.act f).d * cNx n f x) ∨
    (cRhoX n θ B c f x < kappaR (n.act f).q T0 * cNx n f x ∧
      SegIn K (fun u => x u + rdot (cts n) x) (qdirR n o)
        (-(cRhoX n θ B c f x) / 2 + (n.act f).d * (T0 : ℝ) * cNx n f x) ((n.act f).d * cNx n f x)))

/-- the gates of the retained family, constant in the format and including the absent-class extension -/
def RetRule (K : Set (Fin 3 → ℝ)) : Prop :=
  0 < cRp n θ B c ∧ cRp n θ B c < Real.logb 2 (n.act n.p).q / (n.act n.p).q ∧
  (SegIn K (fun _ => 1) (rdirR n) (-(cRp n θ B c) / 2) ((n.act n.p).d / (n.act n.p).q) ∨
    (cRp n θ B c < kappaR (n.act n.p).q T0 / (n.act n.p).q ∧
      SegIn K (fun _ => 1) (rdirR n)
        (-(cRp n θ B c) / 2 + (n.act n.p).d * (T0 : ℝ) / (n.act n.p).q)
        ((n.act n.p).d / (n.act n.p).q)))

/-- the formats at which the catalytic rule gives the source tariff `λ` -/
def CDom (K : Fin 3 → Set (Fin 3 → ℝ)) : Set (Fin 3 → ℝ) :=
  {x | (∀ u, 0 < x u) ∧ FamRule n θ B c (K (cj n)) (cj n) (ck n) x ∧
    FamRule n θ B c (K (ck n)) (ck n) (cj n) x}

end RealFormat

/-- **The catalysed source rule**. Fix a spectral point `φ`, an upper profile `θ`, a target `B`, and a cube `S` of
format `(l,l,l)` with `φ(S) > 2^{B l}`. A catalytic node with actions `F_7`/`F_11`, positive
T-mass, label exponents in `(0,1)`, parent tariffs `c i` valid on open cones `K i`, and the
retained-family gates, has the source tariff `λ = cLam` at every format of `CDom`. -/
def CatalyticRule : Prop :=
  ∀ (φ : PolMul.Spectral ℂ) (θ : Fin 3 → ℝ) (B : ℚ) (l : ℕ) (S : DyadicTensor (fun _ => l)),
    (2 : ℝ) ^ ((B : ℝ) * l) < value φ S → UpperProfile φ θ →
    ∀ (n : CNode) (c : Fin 3 → Fin 3 → ℝ) (K : Fin 3 → Set (Fin 3 → ℝ)),
      (∀ i, n.act i = F7 ∨ n.act i = F11) → 0 < n.tau →
      (∀ i, 0 < cBeta n θ c i ∧ cBeta n θ c i < 1) →
      (∀ i, IsOpen (K i)) → (∀ i, IsConeSet (K i)) → (∀ i, TariffOn φ (c i) (K i)) →
      RetRule n θ B c (K n.p) →
      TariffOn φ (cLam n θ B c) (CDom n θ B c K)

end OM.NNN20
