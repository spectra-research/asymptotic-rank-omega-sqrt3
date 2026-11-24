import Lib.OM.NNN30.Crossing.Jets
import Lib.OM.NNN30.Crossing.Diag
import Lib.OM.NNN30.Crossing.Gram
import PLATFORM.Statements.«R108.1»

/-! # R108.1: the finite crossing lemma

`P(z) = z^M (z-1)^M F(z)` (the four-point function of partition states, `M = H + E`) has degree at
most `D = 2(H + E)` and leading coefficient `Δ ⊗ G` (`Δ` diagonal, `G` the `0`–`1` pairing,
both invertible).  Writing `P = Σ_k B'_k z^k (z-1)^{D-k}`, `B'_k` is a combination of the first
`k + 1` Taylor coefficients of `P` at `0` and of the first `D - k + 1` at `1`; by the operator
product expansions these factor through the partitions of weight at most `k` (across `z0 | 1∞`)
and at most `D - k` (across `z1 | 0∞`).  Normalising the legs `1` and `∞` by `G⁻¹` and `Δ⁻¹`
gives pieces summing to `δ(z,∞) δ(0,1)`. -/

namespace OM.NNN30.Crossing

open PowerSeries

/-- A matrix that factors through `σ` has rank at most `|σ|`. -/
theorem rank_le_of_factor {m n σ : Type*} [Fintype m] [Fintype n] [Fintype σ] [DecidableEq σ]
    (M : Matrix m n ℂ) (A : m → σ → ℂ) (R : σ → n → ℂ)
    (h : ∀ i j, M i j = ∑ s, A i s * R s j) : M.rank ≤ Fintype.card σ := by
  have : M = Matrix.of A * Matrix.of R := by
    ext i j; rw [h, Matrix.mul_apply]; rfl
  rw [this]
  exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_le_card_width _)

theorem card_sigma_partition (k : ℕ) :
    Fintype.card (Σ i : Fin (k + 1), (i : ℕ).Partition) =
      ∑ j ∈ Finset.range (k + 1), Fintype.card j.Partition := by
  rw [Fintype.card_sigma, Fin.sum_univ_eq_sum_range (fun j => Fintype.card j.Partition)]

section Assembly

variable (H E : ℕ)

/-- The four-point polynomial of partition states. -/
noncomputable def Ppart (z : H.Partition) (x y : E.Partition) (w : H.Partition) : Polynomial ℂ :=
  P4 z.parts x.parts y.parts w.parts

/-- The coefficients in the basis `z^k (z-1)^{D-k}`. -/
noncomputable def Bp (k : ℕ) (z : H.Partition) (x y : E.Partition) (w : H.Partition) : ℂ :=
  (trL 1 (-1) (2 * (H + E)) (Ppart H E z x y w)).coeff k

theorem pos_parts {n : ℕ} (p : n.Partition) : Pos p.parts := fun _ h => p.parts_pos h

theorem Ppart_natDegree (z : H.Partition) (x y : E.Partition) (w : H.Partition) :
    (Ppart H E z x y w).natDegree ≤ 2 * (H + E) := by
  have := P4_natDegree z.parts x.parts y.parts w.parts
  rw [z.parts_sum, x.parts_sum, y.parts_sum, w.parts_sum] at this
  unfold Ppart; omega

/-- The `z`–`∞` top pairing. -/
noncomputable def Dmat : Matrix H.Partition H.Partition ℂ :=
  Matrix.of fun z w => wickM topK (z.parts.map (fun a => (Pt.z, a)) + w.parts.map (fun d => (Pt.inf, d)))

theorem Bp_sum (z : H.Partition) (x y : E.Partition) (w : H.Partition) :
    ∑ k ∈ Finset.range (2 * (H + E) + 1), Bp H E k z x y w = Dmat H z w * Gmat E x y := by
  unfold Bp
  rw [basis_sum _ _ (Ppart_natDegree H E z x y w)]
  have := P4_top (pos_parts z) (pos_parts x) (pos_parts y) (pos_parts w)
  rw [z.parts_sum, x.parts_sum, y.parts_sum, w.parts_sum] at this
  rw [show 2 * (H + E) = H + E + E + H by ring]
  exact this

theorem topK_zinf (Z I : Multiset ℕ) :
    wickM topK (Z.map (fun a => (Pt.z, a)) + I.map (fun d => (Pt.inf, d))) =
      ((wickM zinfK (zM Z + iM I) : ℤ) : ℂ) := by
  classical
  have hs : ∀ u v : Pt × ℕ, ((zinfK u v : ℤ) : ℂ) = ((zinfK v u : ℤ) : ℂ) := by
    intro u v; rw [zinfK_symm]
  have key : ∀ u ∈ Z.map (fun a => (Pt.z, a)) + I.map (fun d => (Pt.inf, d)),
      ∀ v ∈ Z.map (fun a => (Pt.z, a)) + I.map (fun d => (Pt.inf, d)),
      topK u v = ((zinfK u v : ℤ) : ℂ) := by
    intro u hu v hv
    rcases Multiset.mem_add.mp hu with hu | hu <;> obtain ⟨a, _, rfl⟩ := Multiset.mem_map.mp hu <;>
      rcases Multiset.mem_add.mp hv with hv | hv <;> obtain ⟨b, _, rfl⟩ := Multiset.mem_map.mp hv <;>
      simp [topK, zinfK]
  rw [wickM_congr topK_symm hs _ key]
  exact wickM_ringHom (Int.castRingHom ℂ) zinfK _

theorem Dmat_offdiag (z w : H.Partition) (h : z ≠ w) : Dmat H z w = 0 := by
  unfold Dmat
  rw [Matrix.of_apply, topK_zinf]
  by_contra hne
  have hne' : wickM zinfK (zM z.parts + iM w.parts) ≠ 0 := fun h0 => hne (by rw [h0]; simp)
  obtain ⟨_, h2⟩ := delta_support z.parts (pos_parts z) w.parts (pos_parts w) hne'
  apply h
  apply Nat.Partition.ext
  exact h2 (by rw [z.parts_sum, w.parts_sum])

theorem Dmat_diag_ne_zero (z : H.Partition) : Dmat H z z ≠ 0 := by
  unfold Dmat
  rw [Matrix.of_apply, topK_zinf]
  have := delta_self z.parts
  exact_mod_cast (show wickM zinfK (zM z.parts + iM z.parts) ≠ 0 by omega)

/-- The inverse of the diagonal matrix `Δ`. -/
noncomputable def Dinv : Matrix H.Partition H.Partition ℂ :=
  Matrix.diagonal fun z => (Dmat H z z)⁻¹

theorem Dmat_mul_Dinv : Dmat H * Dinv H = 1 := by
  classical
  ext z w
  rw [Dinv, Matrix.mul_diagonal, Matrix.one_apply]
  by_cases h : z = w
  · subst h; rw [if_pos rfl, mul_inv_cancel₀ (Dmat_diag_ne_zero H z)]
  · rw [if_neg h, Dmat_offdiag H z w h, zero_mul]

theorem Gmat_mul_inv : Gmat E * (Gmat E)⁻¹ = 1 :=
  Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (Gmat_det_ne_zero E))

/-- The normalised pieces. -/
noncomputable def Bfin (k : ℕ) (z : H.Partition) (x y : E.Partition) (w : H.Partition) : ℂ :=
  ∑ y' : E.Partition, ∑ w' : H.Partition, Bp H E k z x y' w' * (Gmat E)⁻¹ y' y * Dinv H w' w

theorem Bfin_sum (z : H.Partition) (x y : E.Partition) (w : H.Partition) :
    ∑ k ∈ Finset.range (2 * (H + E) + 1), Bfin H E k z x y w = if z = w ∧ x = y then 1 else 0 := by
  classical
  unfold Bfin
  rw [Finset.sum_comm]
  have h1 : ∀ y' : E.Partition, ∑ k ∈ Finset.range (2 * (H + E) + 1), ∑ w' : H.Partition,
      Bp H E k z x y' w' * (Gmat E)⁻¹ y' y * Dinv H w' w =
      ∑ w' : H.Partition, Dmat H z w' * Gmat E x y' * (Gmat E)⁻¹ y' y * Dinv H w' w := by
    intro y'
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro w' _
    rw [← Finset.sum_mul, ← Finset.sum_mul, Bp_sum]
  rw [Finset.sum_congr rfl (fun y' _ => h1 y')]
  have h2 : ∑ y' : E.Partition, ∑ w' : H.Partition,
      Dmat H z w' * Gmat E x y' * (Gmat E)⁻¹ y' y * Dinv H w' w =
      (∑ w' : H.Partition, Dmat H z w' * Dinv H w' w) *
        (∑ y' : E.Partition, Gmat E x y' * (Gmat E)⁻¹ y' y) := by
    rw [Finset.sum_mul_sum, Finset.sum_comm]
    apply Finset.sum_congr rfl; intro w' _
    apply Finset.sum_congr rfl; intro y' _
    ring
  rw [h2, ← Matrix.mul_apply, ← Matrix.mul_apply, Dmat_mul_Dinv, Gmat_mul_inv,
    Matrix.one_apply, Matrix.one_apply]
  by_cases hzw : z = w <;> by_cases hxy : x = y <;> simp [hzw, hxy]

private noncomputable def far (β : Pt × ℕ → Pt × ℕ → ℂ⟦X⟧) (m : ℕ) (t : m.Partition)
    (q : E.Partition × H.Partition) : ℂ :=
  farVal β t.parts (q.1.parts.map (fun a => (Pt.q, a)) + q.2.parts.map (fun b => (Pt.inf, b)))

private theorem row_factor (k : ℕ) (hk : k ≤ 2 * (H + E)) :
    ∃ L : H.Partition × E.Partition → States k → ℂ, ∀ z x y w,
      Bp H E k z x y w = ∑ s, L (z, x) s * far H E ker0 s.1.val s.2 (y, w) := by
  let P := fun (i : H.Partition × E.Partition) (j : E.Partition × H.Partition) =>
    Ppart H E i.1 i.2 j.1 j.2
  let U := fun (i : H.Partition × E.Partition) (j : E.Partition × H.Partition) =>
    wickM ker0 (labels4 i.1.parts i.2.parts j.1.parts j.2.parts)
  obtain ⟨L, hL⟩ := jet_factor 1 (-1) 1 _ k hk ((X - 1) ^ (H + E)) P U (far H E ker0)
    (fun i j => by
      simpa only [P, U, Ppart, shift1, Nat.Partition.parts_sum] using
        P4_coe (pos_parts i.1) (pos_parts i.2) (pos_parts j.1) (pos_parts j.2))
    (fun i m => by
      obtain ⟨l, hl⟩ := row_fact (pos_parts i.1) (pos_parts i.2) m
      exact ⟨l, fun j => hl _ _ (pos_parts j.1) (pos_parts j.2)⟩)
  exact ⟨L, fun z x y w => by simpa only [Bp, P, one_mul] using hL (z, x) (y, w)⟩

private theorem col_factor (k : ℕ) (hk : k ≤ 2 * (H + E)) :
    ∃ L : H.Partition × E.Partition → States (2 * (H + E) - k) → ℂ, ∀ z x y w,
      Bp H E k z x y w = ∑ s, L (z, y) s * far H E ker1 s.1.val s.2 (x, w) := by
  let P := fun (i : H.Partition × E.Partition) (j : E.Partition × H.Partition) =>
    (Ppart H E i.1 j.1 i.2 j.2).comp (Polynomial.X + 1)
  let U := fun (i : H.Partition × E.Partition) (j : E.Partition × H.Partition) =>
    wickM ker1 (labels4 i.1.parts i.2.parts j.1.parts j.2.parts)
  obtain ⟨L, hL⟩ := jet_factor (-1) (-1) ((-1) ^ k) (2 * (H + E)) _ (Nat.sub_le _ k)
    ((1 + X) ^ (H + E)) P U (far H E ker1)
    (fun i j => by
      simpa only [P, U, Ppart, shift1, Nat.Partition.parts_sum] using
        P4_shift1 (pos_parts i.1) (pos_parts j.1) (pos_parts i.2) (pos_parts j.2))
    (fun i m => by
      obtain ⟨l, hl⟩ := col_fact (pos_parts i.1) (pos_parts i.2) m
      exact ⟨l, fun j => hl _ _ (pos_parts j.1) (pos_parts j.2)⟩)
  refine ⟨L, fun z x y w => ?_⟩
  exact (basis_coeff_at_one _ _ (Ppart_natDegree H E z x y w) k hk).trans (hL (z, y) (x, w))

private theorem sum_rotate {I J S : Type} [Fintype I] [Fintype J] [Fintype S] (f : I → J → S → ℂ) :
    ∑ i, ∑ j, ∑ s, f i j s = ∑ s, ∑ i, ∑ j, f i j s := by
  simp_rw [Finset.sum_comm (f := fun j s => f _ j s)]
  exact Finset.sum_comm

theorem proof_R108_1 : S_R108_1 := by
  classical
  intro H E _ _
  refine ⟨fun k => Bfin H E k.val, fun z x y w => ?_, fun k => ?_⟩
  · rw [Fin.sum_univ_eq_sum_range (fun k => Bfin H E k z x y w)]
    exact Bfin_sum H E z x y w
  have hk := Nat.lt_succ_iff.mp k.isLt
  constructor
  · obtain ⟨L, hL⟩ := row_factor H E k hk
    rw [← card_sigma_partition]
    apply rank_le_of_factor _ L (fun s j => ∑ y', ∑ w',
      far H E ker0 s.1.val s.2 (y', w') * (Gmat E)⁻¹ y' j.1 * Dinv H w' j.2)
    intro i j
    simp only [Matrix.of_apply, Bfin, hL, Finset.sum_mul, Finset.mul_sum]
    rw [sum_rotate (fun y' w' s => L (i.1, i.2) s * far H E ker0 s.1.val s.2 (y', w') *
      (Gmat E)⁻¹ y' j.1 * Dinv H w' j.2)]
    simp [mul_assoc]
  · obtain ⟨L, hL⟩ := col_factor H E k hk
    rw [← card_sigma_partition]
    apply rank_le_of_factor _
      (fun i s => ∑ y', L (i.1, y') s * (Gmat E)⁻¹ y' i.2)
      (fun s j => ∑ w', far H E ker1 s.1.val s.2 (j.1, w') * Dinv H w' j.2)
    intro i j
    simp only [Matrix.of_apply, Bfin, hL, Finset.sum_mul]
    rw [sum_rotate (fun y' w' s => L (i.1, y') s * far H E ker1 s.1.val s.2 (j.1, w') *
      (Gmat E)⁻¹ y' i.2 * Dinv H w' j.2)]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s _
    apply Finset.sum_congr rfl
    intro y' _
    apply Finset.sum_congr rfl
    intro w' _
    ring

end Assembly

end OM.NNN30.Crossing

