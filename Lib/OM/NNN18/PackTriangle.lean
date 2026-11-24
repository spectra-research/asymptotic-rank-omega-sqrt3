import Lib.OM.NNN11.EdgeFactor
import Mathlib.Combinatorics.Additive.AP.Three.Defs

/-!
A family `F = Σ_g edgeFactor(W_g)(fx_g ·, fy_g ·, ·)` — word-dependent coordinate maps at the two
parties of a bond, the identity at the third — is a restriction of one tensor
`edgeFactor_{E × Fin 2N}(W_pack)`, where `W_pack` stores `W_g` at the labels `(x_g, x_g + 2 d_g)`
of a triangle `(x_g, x_g + d_g, x_g + 2 d_g)` with `d_g` in a 3AP-free set.  The middle vertex is
communicated by one additional (paid) equality index of size `2N`.
-/

noncomputable section
open scoped BigOperators Classical
open CoordinateTensor OM.NNN.Raw
namespace OM.NNN18

/-- **LABEL_PACKING (5)**: three edges of selected triangles that close up come from one
triangle.  `pos g = (x_g, d_g)`. -/
theorem triangle_unique {G : Type} {pos : G → ℕ × ℕ} (hinj : Function.Injective pos)
    {D : Set ℕ} (hD : ThreeAPFree D) (hd : ∀ g, (pos g).2 ∈ D) {g g' g'' : G}
    (h1 : (pos g).1 = (pos g').1)
    (h2 : (pos g).1 + (pos g).2 = (pos g'').1 + (pos g'').2)
    (h3 : (pos g'').1 + 2 * (pos g'').2 = (pos g').1 + 2 * (pos g').2) :
    g = g' ∧ g'' = g' := by
  -- increments d₁ = d_g, d₂ = d_{g''}, d₃ = d_{g'} satisfy d₁ + d₂ = 2 d₃
  have hsum : (pos g).2 + (pos g'').2 = (pos g').2 + (pos g').2 := by omega
  have e1 : (pos g).2 = (pos g').2 := hD (hd g) (hd g') (hd g'') hsum
  have e2 : (pos g'').2 = (pos g').2 := by omega
  have ex : (pos g'').1 = (pos g').1 := by omega
  exact ⟨hinj (Prod.ext h1 e1), hinj (Prod.ext ex e2)⟩

variable {G OA OB Z R Q E : Type} [Fintype G] [Fintype OA] [Fintype OB] [Fintype Z]
  [Fintype R] [Fintype Q] [Fintype E]

/-- The packed residual (LABEL_PACKING (6)). -/
def packedResidual (N : ℕ) (pos : G → ℕ × ℕ) (W : G → Tensor ℂ R Q Z) :
    Tensor ℂ (R × Fin N) (Q × Fin (3 * N)) Z :=
  fun ri ql z => ∑ g, if (ri.2 : ℕ) = (pos g).1 ∧ (ql.2 : ℕ) = (pos g).1 + 2 * (pos g).2
    then W g ri.1 ql.1 z else 0

/-- The family produced by the packed source (LABEL_PACKING (1)). -/
def packedFamily (fx : G → OA → R × E) (fy : G → OB → Q × E) (W : G → Tensor ℂ R Q Z) :
    Tensor ℂ OA OB Z :=
  fun xx yy zz => ∑ g, NNN11.edgeFactor (E := E) (W g) (fx g xx) (fy g yy) zz

/-- Coordinates of the first and second edges of triangle `g` in the source legs. -/
def edgeA (N : ℕ) (pos : G → ℕ × ℕ) (hx : ∀ g, (pos g).1 < N) (hdN : ∀ g, (pos g).2 < N)
    (fx : G → OA → R × E) (g : G) (xx : OA) : (R × Fin N) × (E × Fin (2 * N)) :=
  (((fx g xx).1, ⟨(pos g).1, hx g⟩), ((fx g xx).2, ⟨(pos g).1 + (pos g).2, by
    have := hx g; have := hdN g; omega⟩))

def edgeB (N : ℕ) (pos : G → ℕ × ℕ) (hx : ∀ g, (pos g).1 < N) (hdN : ∀ g, (pos g).2 < N)
    (fy : G → OB → Q × E) (g : G) (yy : OB) : (Q × Fin (3 * N)) × (E × Fin (2 * N)) :=
  (((fy g yy).1, ⟨(pos g).1 + 2 * (pos g).2, by have := hx g; have := hdN g; omega⟩),
    ((fy g yy).2, ⟨(pos g).1 + (pos g).2, by have := hx g; have := hdN g; omega⟩))

lemma sum_indicator_sum {I : Type} [Fintype I] [DecidableEq I] (A : G → I) (f : I → ℂ) :
    ∑ a, (∑ g, if a = A g then (1 : ℂ) else 0) * f a = ∑ g, f (A g) := by
  simp only [Finset.sum_mul, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro g _
  rw [Finset.sum_ite_eq']
  simp

/-- **LABEL_PACKING (7)**: the packed family is a restriction of `E_{#E·2N} ⊗ W_pack`. -/
theorem packed_restricts (N : ℕ) (pos : G → ℕ × ℕ) (hinj : Function.Injective pos)
    {D : Set ℕ} (hD : ThreeAPFree D) (hd : ∀ g, (pos g).2 ∈ D)
    (hx : ∀ g, (pos g).1 < N) (hdN : ∀ g, (pos g).2 < N)
    (fx : G → OA → R × E) (fy : G → OB → Q × E) (W : G → Tensor ℂ R Q Z) :
    Restricts (NNN11.edgeFactor (E := E × Fin (2 * N)) (packedResidual N pos W))
      (packedFamily fx fy W) := by
  refine ⟨fun xx a => ∑ g, if a = edgeA N pos hx hdN fx g xx then (1 : ℂ) else 0,
    fun yy b => ∑ g, if b = edgeB N pos hx hdN fy g yy then (1 : ℂ) else 0,
    fun zz c => if zz = c then (1 : ℂ) else 0, ?_⟩
  funext xx yy zz
  simp only [mapTensor]
  -- collapse the identity on the third leg
  have hz : ∀ (a : (R × Fin N) × (E × Fin (2 * N))) (b : (Q × Fin (3 * N)) × (E × Fin (2 * N))),
      ∑ c, (∑ g, if a = edgeA N pos hx hdN fx g xx then (1 : ℂ) else 0) *
        (∑ g, if b = edgeB N pos hx hdN fy g yy then (1 : ℂ) else 0) *
        (if zz = c then (1 : ℂ) else 0) *
        NNN11.edgeFactor (packedResidual N pos W) a b c =
      (∑ g, if a = edgeA N pos hx hdN fx g xx then (1 : ℂ) else 0) *
        ((∑ g, if b = edgeB N pos hx hdN fy g yy then (1 : ℂ) else 0) *
          NNN11.edgeFactor (packedResidual N pos W) a b zz) := by
    intro a b
    simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
      if_true]
    ring
  simp only [hz]
  set S := NNN11.edgeFactor (E := E × Fin (2 * N)) (packedResidual N pos W)
  calc (∑ a, ∑ b, (∑ g, if a = edgeA N pos hx hdN fx g xx then (1 : ℂ) else 0) *
        ((∑ g, if b = edgeB N pos hx hdN fy g yy then (1 : ℂ) else 0) * S a b zz))
      = ∑ a, (∑ g, if a = edgeA N pos hx hdN fx g xx then (1 : ℂ) else 0) *
        ∑ b, ((∑ g, if b = edgeB N pos hx hdN fy g yy then (1 : ℂ) else 0) * S a b zz) := by
        simp only [Finset.mul_sum]
    _ = ∑ g, ∑ b, ((∑ g, if b = edgeB N pos hx hdN fy g yy then (1 : ℂ) else 0) *
          S (edgeA N pos hx hdN fx g xx) b zz) :=
        sum_indicator_sum (fun g => edgeA N pos hx hdN fx g xx)
          (fun a => ∑ b, ((∑ g, if b = edgeB N pos hx hdN fy g yy then (1 : ℂ) else 0) * S a b zz))
    _ = ∑ g, ∑ g'', S (edgeA N pos hx hdN fx g xx) (edgeB N pos hx hdN fy g'' yy) zz := by
        apply Finset.sum_congr rfl
        intro g _
        exact sum_indicator_sum (fun g => edgeB N pos hx hdN fy g yy)
          (fun b => S (edgeA N pos hx hdN fx g xx) b zz)
    _ = packedFamily fx fy W xx yy zz := ?_
  -- now Σ_g Σ_g'' edgeFactor W_pack (edgeA g) (edgeB g'') zz
  simp only [S]
  unfold packedFamily
  apply Finset.sum_congr rfl
  intro g _
  rw [Finset.sum_eq_single g]
  · -- diagonal term
    simp only [NNN11.edgeFactor, edgeA, edgeB, packedResidual, Prod.mk.injEq, Fin.mk.injEq,
      and_true]
    by_cases hE : (fx g xx).2 = (fy g yy).2
    · simp only [hE, if_true]
      rw [Finset.sum_eq_single g]
      · simp
      · intro g' _ hne
        rw [if_neg]
        rintro ⟨h1, h3⟩
        exact hne ((triangle_unique hinj hD hd (g := g) (g' := g') (g'' := g) h1 rfl
          (by omega)).1.symm)
      · simp
    · simp [hE]
  · -- off-diagonal terms vanish
    intro g'' _ hne
    simp only [NNN11.edgeFactor, edgeA, edgeB, packedResidual, Prod.mk.injEq, Fin.mk.injEq]
    split_ifs with hh
    · apply Finset.sum_eq_zero
      intro g' _
      rw [if_neg]
      rintro ⟨h1, h3⟩
      have := triangle_unique hinj hD hd (g := g) (g' := g') (g'' := g'') h1 hh.2 h3
      exact hne (this.2.trans this.1.symm)
    · rfl
  · simp

/-- **LABEL_PACKING (13)**: the price of the packed family. -/
theorem packed_value [Nonempty R] [Nonempty Q] [Nonempty Z] [Nonempty E]
    (φ : PolMul.Spectral ℂ) (N : ℕ) (hN : 0 < N) (pos : G → ℕ × ℕ)
    (hinj : Function.Injective pos) {D : Set ℕ} (hD : ThreeAPFree D) (hd : ∀ g, (pos g).2 ∈ D)
    (hx : ∀ g, (pos g).1 < N) (hdN : ∀ g, (pos g).2 < N)
    (fx : G → OA → R × E) (fy : G → OB → Q × E) (W : G → Tensor ℂ R Q Z) :
    value φ (packedFamily fx fy W) ≤ value φ (packedResidual N pos W) *
      ((Fintype.card E * (2 * N) : ℕ) : ℝ) ^ Foundations.PairUnitExponents.theta φ 2 := by
  haveI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  haveI : Nonempty (Fin (3 * N)) := ⟨⟨0, by omega⟩⟩
  haveI : Nonempty (Fin (2 * N)) := ⟨⟨0, by omega⟩⟩
  have h := value_mono φ (restricts_degenerates _ _ (packed_restricts N pos hinj hD hd hx hdN fx fy W))
  rw [NNN11.value_edgeFactor] at h
  simpa [Fintype.card_prod, Fintype.card_fin] using h

end OM.NNN18
