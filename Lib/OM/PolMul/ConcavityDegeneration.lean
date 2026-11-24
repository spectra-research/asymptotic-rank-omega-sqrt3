/- Adapted from PolMul/ConcavityDegeneration.lean of an earlier formalisation
   (commit 51c6e6b6e8b8d7226c6a828dba618ae1de5b5f8a).
   Uses Foundations tensor definitions; declarations are renamed under OM. -/
import Lib.OM.PolMul.Defs
import Lib.OM.PolMulStatements.CG_1

/-!
# The concavity degeneration

This is the coordinate form of the exact-sequence proof in Section 3.3 of the
paper.  The matrices below use the splitting

`(q,p) ↦ (q_{<d} - t p, p + q_d t^(d-1))`

of `F[t]_{≤ d} ⊕ F[t]_{≤ d-2} ≃ F[t]_{≤ d-1} ⊕ F[t]_{≤ d-1}`.
-/

namespace OM.PolMul.ConcavityDegeneration

open scoped BigOperators

universe u

variable {F : Type u} [Field F]

/-- The transpose of the chosen splitting on the second (dual) leg. -/
private def secondBase (b : ℕ+)
    (x : Fin (((b + 1) + (b - 1) : ℕ+) : ℕ))
    (y : Fin ((b + b : ℕ+) : ℕ)) : F :=
  if x.val < (b : ℕ) + 1 then
    if x.val < (b : ℕ) then
      if y.val = x.val then 1 else 0
    else
      if y.val = 2 * (b : ℕ) - 1 then 1 else 0
  else
    (if y.val = (b : ℕ) + (x.val - ((b : ℕ) + 1)) then 1 else 0) -
      if y.val = (x.val - ((b : ℕ) + 1)) + 1 then 1 else 0

/-- The quotient/kernel coordinate map on the third (primal) leg. -/
private def thirdBase (a b : ℕ+)
    (x : Fin (((a + (b + 1) - 1) + (a + (b - 1) - 1) : ℕ+) : ℕ))
    (y : Fin (((a + b - 1) + (a + b - 1) : ℕ+) : ℕ)) : F :=
  let c := (a : ℕ) + (b : ℕ) - 1
  if x.val < c + 1 then
    if x.val = 0 then
      if y.val = 0 then 1 else 0
    else if x.val < c then
      (if y.val = x.val then 1 else 0) +
        if y.val = c + x.val - 1 then 1 else 0
    else
      if y.val = 2 * c - 1 then 1 else 0
  else
    if y.val = c + (x.val - (c + 1)) then 1 else 0

/-- The three constant matrices implementing the exact-sequence base change. -/
private def baseMatrix (a b : ℕ+) : ∀ i : Fin 3,
    Matrix
      (Fin ((fmt a ((b + 1) + (b - 1))
        ((a + (b + 1) - 1) + (a + (b - 1) - 1))) i))
      (Fin ((fmt a (b + b) ((a + b - 1) + (a + b - 1))) i)) F
  | 0 => fun x y => if x = y then 1 else 0
  | 1 => secondBase b
  | 2 => thirdBase a b

/-- Re-index a three-leg coordinate array as an ordinary triple. -/
private def indexEquiv (n v w : ℕ+) :
    (∀ i : Fin 3, Fin (fmt n v w i)) ≃ Fin n × (Fin v × Fin w) where
  toFun x := (x 0, x 1, x 2)
  invFun x := fun
    | 0 => x.1
    | 1 => x.2.1
    | 2 => x.2.2
  left_inv x := by
    funext i
    fin_cases i <;> rfl
  right_inv x := rfl

/-- The unique third-leg source coordinate selected by a first- and
second-leg source coordinate of the two-copy multiplication tensor. -/
private def sourceColumn (a b : ℕ+) (i : Fin a)
    (j : Fin ((b + b : ℕ+) : ℕ)) :
    Fin (((a + b - 1) + (a + b - 1) : ℕ+) : ℕ) := by
  let c := (a : ℕ) + (b : ℕ) - 1
  by_cases hj : j.val < (b : ℕ)
  · exact ⟨i.val + j.val, by
      have hi := i.isLt
      have ha := a.pos
      have hb := b.pos
      have hab : (1 : ℕ+) < a + b := by
        have : (1 : ℕ) < (a : ℕ) + (b : ℕ) := by omega
        exact_mod_cast this
      have hout : (((a + b - 1) + (a + b - 1) : ℕ+) : ℕ) = 2 * c := by
        simp only [PNat.add_coe, PNat.sub_coe, if_pos hab]
        simp only [two_mul]
        change c + c = c + c
        rfl
      rw [hout]
      have hc : c + 1 = (a : ℕ) + (b : ℕ) := by
        dsimp only [c]
        omega
      omega⟩

  · exact ⟨c + i.val + (j.val - (b : ℕ)), by
      have hi := i.isLt
      have hjlt := j.isLt
      have ha := a.pos
      have hb := b.pos
      have hab : (1 : ℕ+) < a + b := by
        have : (1 : ℕ) < (a : ℕ) + (b : ℕ) := by omega
        exact_mod_cast this
      have hout : (((a + b - 1) + (a + b - 1) : ℕ+) : ℕ) = 2 * c := by
        simp only [PNat.add_coe, PNat.sub_coe, if_pos hab]
        simp only [two_mul]
        change c + c = c + c
        rfl
      simp only [PNat.add_coe] at hjlt
      rw [hout]
      have hc : c + 1 = (a : ℕ) + (b : ℕ) := by
        dsimp only [c]
        omega
      omega⟩

-- This coordinate check is the support description of the two-copy shared-leg
-- direct sum.  The larger budget is for normalization of positive-natural
-- subtraction in the lower block.
set_option maxHeartbeats 400000 in
private theorem sourceTensor_eq (a b : ℕ+) (i : Fin a)
    (j : Fin ((b + b : ℕ+) : ℕ))
    (k : Fin (((a + b - 1) + (a + b - 1) : ℕ+) : ℕ)) :
    pdsum (polmul (F := F) a b) (polmul a b) rfl
        (fun | 0 => i | 1 => j | 2 => k) =
      if k = sourceColumn a b i j then 1 else 0 := by
  classical
  have ha := a.pos
  have hb := b.pos
  have hab : (1 : ℕ+) < a + b := by
    have : (1 : ℕ) < (a : ℕ) + (b : ℕ) := by omega
    exact_mod_cast this
  by_cases hj : j.val < (b : ℕ)
  · by_cases hk : k.val < (a : ℕ) + (b : ℕ) - 1
    · simp [pdsum, polmul, fmt, sourceColumn, hj, hk, Fin.ext_iff,
        PNat.add_coe, PNat.sub_coe, hab]
    · simp [pdsum, polmul, fmt, sourceColumn, hj, hk, Fin.ext_iff,
        PNat.add_coe, PNat.sub_coe, hab]
      omega
  · by_cases hk : (a : ℕ) + (b : ℕ) - 1 ≤ k.val
    · simp [pdsum, polmul, fmt, sourceColumn, hj, hk, Fin.ext_iff,
        PNat.add_coe, PNat.sub_coe, hab, Nat.sub_eq_iff_eq_add' hk,
        add_assoc]
    · simp [pdsum, polmul, fmt, sourceColumn, hj, hk, Fin.ext_iff,
        PNat.add_coe, PNat.sub_coe, hab]
      omega

-- Eta-expanded form used when simplifying the tensor-action sum.
set_option maxHeartbeats 100000 in
private theorem sourceTensor_eq_idx (a b : ℕ+)
    (sidx : ∀ i : Fin 3, Fin (fmt a (b + b)
      ((a + b - 1) + (a + b - 1)) i)) :
    pdsum (polmul (F := F) a b) (polmul a b) rfl sidx =
      if sidx 2 = sourceColumn a b (sidx 0) (sidx 1) then 1 else 0 := by
  simpa using! sourceTensor_eq (F := F) a b (sidx 0) (sidx 1) (sidx 2)

/-- The tensor after the constant exact-sequence coordinate change. -/
private noncomputable def constantAction (a b : ℕ+)
    (idx : ∀ i : Fin 3, Fin (fmt a ((b + 1) + (b - 1))
      ((a + (b + 1) - 1) + (a + (b - 1) - 1)) i)) : F :=
  ∑ sidx : (∀ i : Fin 3, Fin (fmt a (b + b)
      ((a + b - 1) + (a + b - 1)) i)),
    (∏ i : Fin 3, baseMatrix (F := F) a b i (idx i) (sidx i)) *
      pdsum (polmul (F := F) a b) (polmul a b) rfl sidx

-- The expanded three finite sums are small enough for the kernel simplifier;
-- this budget mainly covers unfolding the dependent coordinate tuples.
set_option maxHeartbeats 800000 in
private theorem constantAction_eq_sum (a b : ℕ+)
    (idx : ∀ i : Fin 3, Fin (fmt a ((b + 1) + (b - 1))
      ((a + (b + 1) - 1) + (a + (b - 1) - 1)) i)) :
    constantAction (F := F) a b idx =
      ∑ j : Fin ((b + b : ℕ+) : ℕ), secondBase (F := F) b (idx 1) j *
        thirdBase (F := F) a b (idx 2) (sourceColumn a b (idx 0) j) := by
  classical
  unfold constantAction
  rw [← (indexEquiv a (b + b) ((a + b - 1) + (a + b - 1))).symm.sum_comp]
  simp only [Fintype.sum_prod_type]
  simp [indexEquiv, baseMatrix, Fin.prod_univ_succ, sourceTensor_eq_idx]

-- Normalized cardinalities of all four blocks.  Keeping them in one lemma
-- prevents repeated unfolding of truncated subtraction in later coordinates.
set_option maxHeartbeats 200000 in
private theorem sizeFacts (a b : ℕ+) (hb : 2 ≤ b) :
    (((b + 1) + (b - 1) : ℕ+) : ℕ) = 2 * (b : ℕ) ∧
    ((b + b : ℕ+) : ℕ) = 2 * (b : ℕ) ∧
    ((a + b - 1 : ℕ+) : ℕ) = (a : ℕ) + (b : ℕ) - 1 ∧
    ((a + (b + 1) - 1 : ℕ+) : ℕ) = (a : ℕ) + (b : ℕ) ∧
    ((a + (b - 1) - 1 : ℕ+) : ℕ) = (a : ℕ) + (b : ℕ) - 2 ∧
    (((a + (b + 1) - 1) + (a + (b - 1) - 1) : ℕ+) : ℕ) =
      2 * ((a : ℕ) + (b : ℕ) - 1) := by
  have ha := a.pos
  have hbNat : 2 ≤ (b : ℕ) := by exact_mod_cast hb
  have hb1 : (1 : ℕ+) < b := by exact_mod_cast (show (1 : ℕ) < (b : ℕ) by omega)
  have hab : (1 : ℕ+) < a + b := by
    exact_mod_cast (show (1 : ℕ) < (a : ℕ) + (b : ℕ) by omega)
  have habp : (1 : ℕ+) < a + (b + 1) := by
    exact_mod_cast (show (1 : ℕ) < (a : ℕ) + ((b : ℕ) + 1) by omega)
  have habm : (1 : ℕ+) < a + (b - 1) := by
    have hbm : ((b - 1 : ℕ+) : ℕ) = (b : ℕ) - 1 := by
      simp [PNat.sub_coe, hb1]
    apply (PNat.coe_lt_coe 1 (a + (b - 1))).mp
    simp only [PNat.add_coe, hbm]
    norm_num
    omega
  simp only [PNat.add_coe, PNat.sub_coe, if_pos hb1, if_pos hab,
    if_pos habp, if_pos habm]
  norm_num at *
  omega

/-- A source second-leg index presented by its normalized natural value. -/
private def sourceSecondIndex (b : ℕ+) (k : ℕ)
    (hk : k < 2 * (b : ℕ)) : Fin ((b + b : ℕ+) : ℕ) :=
  Fin.cast (by simp only [PNat.add_coe, two_mul]) ⟨k, hk⟩

@[simp] private theorem sourceSecondIndex_val (b : ℕ+) (k : ℕ)
    (hk : k < 2 * (b : ℕ)) : (sourceSecondIndex b k hk).val = k := rfl

-- Sparse-row summation for the coordinate matrices.
set_option maxHeartbeats 100000 in
private theorem sum_delta (n k : ℕ) (hk : k < n) (f : Fin n → F) :
    (∑ j : Fin n, (if j.val = k then 1 else 0) * f j) = f ⟨k, hk⟩ := by
  classical
  simp only [show ∀ j : Fin n, (j.val = k) = (j = ⟨k, hk⟩) by
    intro j
    apply propext
    exact ⟨fun h ↦ Fin.ext h, fun h ↦ congrArg Fin.val h⟩]
  simp

-- The three possible sparse rows of the second-leg base-change matrix.
set_option maxHeartbeats 200000 in
private theorem constantAction_top_low (a b : ℕ+)
    (idx : ∀ i : Fin 3, Fin (fmt a ((b + 1) + (b - 1))
      ((a + (b + 1) - 1) + (a + (b - 1) - 1)) i))
    (hx : (idx 1).val < (b : ℕ)) :
    constantAction (F := F) a b idx =
      thirdBase (F := F) a b (idx 2)
        (sourceColumn a b (idx 0)
          ⟨(idx 1).val, by
            have hbpos := b.pos
            simp only [PNat.add_coe]
            omega⟩) := by
  rw [constantAction_eq_sum]
  have htop : (idx 1).val < (b : ℕ) + 1 := by omega
  simp only [secondBase, if_pos htop, if_pos hx]
  apply sum_delta

set_option maxHeartbeats 200000 in
private theorem constantAction_top_edge (a b : ℕ+)
    (idx : ∀ i : Fin 3, Fin (fmt a ((b + 1) + (b - 1))
      ((a + (b + 1) - 1) + (a + (b - 1) - 1)) i))
    (hx : (idx 1).val = (b : ℕ)) :
    constantAction (F := F) a b idx =
      thirdBase (F := F) a b (idx 2)
        (sourceColumn a b (idx 0)
          ⟨2 * (b : ℕ) - 1, by
            have hbpos := b.pos
            simp only [PNat.add_coe]
            omega⟩) := by
  rw [constantAction_eq_sum]
  have htop : (idx 1).val < (b : ℕ) + 1 := by omega
  have hnlow : ¬ (idx 1).val < (b : ℕ) := by omega
  simp only [secondBase, if_pos htop, if_neg hnlow]
  apply sum_delta

set_option maxHeartbeats 300000 in
private theorem constantAction_bottom (a b : ℕ+) (hb : 2 ≤ b)
    (idx : ∀ i : Fin 3, Fin (fmt a ((b + 1) + (b - 1))
      ((a + (b + 1) - 1) + (a + (b - 1) - 1)) i))
    (hx : (b : ℕ) + 1 ≤ (idx 1).val) :
    let r := (idx 1).val - ((b : ℕ) + 1)
    constantAction (F := F) a b idx =
      thirdBase (F := F) a b (idx 2)
          (sourceColumn a b (idx 0)
            ⟨(b : ℕ) + r, by
              have hlt : (idx 1).val < 2 * (b : ℕ) := by
                calc
                  (idx 1).val < (((b + 1) + (b - 1) : ℕ+) : ℕ) := (idx 1).isLt
                  _ = 2 * (b : ℕ) := (sizeFacts a b hb).1
              calc
                (b : ℕ) + r < 2 * (b : ℕ) := by omega
                _ = ((b + b : ℕ+) : ℕ) := (sizeFacts a b hb).2.1.symm⟩) -
        thirdBase (F := F) a b (idx 2)
          (sourceColumn a b (idx 0)
            ⟨r + 1, by
              have hlt : (idx 1).val < 2 * (b : ℕ) := by
                calc
                  (idx 1).val < (((b + 1) + (b - 1) : ℕ+) : ℕ) := (idx 1).isLt
                  _ = 2 * (b : ℕ) := (sizeFacts a b hb).1
              calc
                r + 1 < 2 * (b : ℕ) := by omega
                _ = ((b + b : ℕ+) : ℕ) := (sizeFacts a b hb).2.1.symm⟩) := by
  dsimp only
  rw [constantAction_eq_sum]
  have hnTop : ¬ (idx 1).val < (b : ℕ) + 1 := by omega
  simp only [secondBase, if_neg hnTop, sub_mul, Finset.sum_sub_distrib]
  rw [sum_delta, sum_delta]

/-- The desired diagonal tensor, in the exact target format. -/
private noncomputable def diagonalTensor (a b : ℕ+) :
    T3 F (fmt a ((b + 1) + (b - 1))
      ((a + (b + 1) - 1) + (a + (b - 1) - 1))) :=
  pdsum (polmul (F := F) a (b + 1)) (polmul a (b - 1)) rfl

-- In the lower diagonal block, `pdsum` is just the smaller multiplication
-- tensor with both block offsets removed.
set_option maxHeartbeats 200000 in
private theorem diagonalTensor_bottom_value (a b : ℕ+) (hb : 2 ≤ b)
    (idx : ∀ i : Fin 3, Fin (fmt a ((b + 1) + (b - 1))
      ((a + (b + 1) - 1) + (a + (b - 1) - 1)) i))
    (hr : ¬ (idx 1).val < (b : ℕ) + 1)
    (hz : ¬ (idx 2).val < (a : ℕ) + (b : ℕ)) :
    diagonalTensor (F := F) a b idx =
      if (idx 2).val - ((a : ℕ) + (b : ℕ)) =
          (idx 0).val + ((idx 1).val - ((b : ℕ) + 1)) then 1 else 0 := by
  rcases sizeFacts a b hb with ⟨hrow, hsrow, hc, hctop, hcbot, hout⟩
  simp [diagonalTensor, pdsum, polmul, fmt, hr, hz, hctop]

-- The upper diagonal block has no offsets.
set_option maxHeartbeats 200000 in
private theorem diagonalTensor_top_value (a b : ℕ+) (hb : 2 ≤ b)
    (idx : ∀ i : Fin 3, Fin (fmt a ((b + 1) + (b - 1))
      ((a + (b + 1) - 1) + (a + (b - 1) - 1)) i))
    (hr : (idx 1).val < (b : ℕ) + 1)
    (hz : (idx 2).val < (a : ℕ) + (b : ℕ)) :
    diagonalTensor (F := F) a b idx =
      if (idx 2).val = (idx 0).val + (idx 1).val then 1 else 0 := by
  rcases sizeFacts a b hb with ⟨hrow, hsrow, hc, hctop, hcbot, hout⟩
  simp [diagonalTensor, pdsum, polmul, fmt, hr, hz, hctop]

-- On a non-endpoint upper row the third-leg matrix preserves the usual
-- multiplication coordinate.
set_option maxHeartbeats 300000 in
private theorem thirdBase_top_low_value (a b : ℕ+) (hb : 2 ≤ b)
    (i : Fin a) (j : Fin ((b + b : ℕ+) : ℕ))
    (z : Fin (((a + (b + 1) - 1) + (a + (b - 1) - 1) : ℕ+) : ℕ))
    (hj : j.val < (b : ℕ)) (hz : z.val < (a : ℕ) + (b : ℕ)) :
    thirdBase (F := F) a b z (sourceColumn a b i j) =
      if z.val = i.val + j.val then 1 else 0 := by
  rcases sizeFacts a b hb with ⟨hrow, hsrow, hc, hctop, hcbot, hout⟩
  have haNat : 1 ≤ (a : ℕ) := a.pos
  have hbNat : 2 ≤ (b : ℕ) := by exact_mod_cast hb
  have hi := i.isLt
  simp [thirdBase, sourceColumn, hj]
  split_ifs
  all_goals try simp only [Fin.ext_iff, Fin.val_zero] at *
  all_goals first | fin_omega | ring

-- The endpoint upper row is supplied by the last coefficient of the second
-- source copy and selects the coordinate `i+b`.
set_option maxHeartbeats 300000 in
private theorem thirdBase_top_edge_value (a b : ℕ+) (hb : 2 ≤ b)
    (i : Fin a)
    (z : Fin (((a + (b + 1) - 1) + (a + (b - 1) - 1) : ℕ+) : ℕ))
    (hz : z.val < (a : ℕ) + (b : ℕ)) :
    thirdBase (F := F) a b z
        (sourceColumn a b i
          ⟨2 * (b : ℕ) - 1, by
            rw [(sizeFacts a b hb).2.1]
            have hbPos := b.pos
            omega⟩) =
      if z.val = i.val + (b : ℕ) then 1 else 0 := by
  rcases sizeFacts a b hb with ⟨hrow, hsrow, hc, hctop, hcbot, hout⟩
  have haNat : 1 ≤ (a : ℕ) := a.pos
  have hbNat : 2 ≤ (b : ℕ) := by exact_mod_cast hb
  have hi := i.isLt
  have hnSource : ¬ 2 * (b : ℕ) - 1 < (b : ℕ) := by omega
  simp [thirdBase, sourceColumn, hnSource]
  split_ifs
  all_goals try simp only [Fin.ext_iff, Fin.val_zero] at *
  all_goals first | fin_omega | ring

-- The top-left block is the larger multiplication tensor.  The budget is for
-- normalization of the dependent `Fin` equalities at the two endpoint rows.
set_option maxHeartbeats 200000 in
private theorem constantAction_top_left (a b : ℕ+) (hb : 2 ≤ b)
    (idx : ∀ i : Fin 3, Fin (fmt a ((b + 1) + (b - 1))
      ((a + (b + 1) - 1) + (a + (b - 1) - 1)) i))
    (hr : (idx 1).val < (b : ℕ) + 1)
    (hz : (idx 2).val < (a : ℕ) + (b : ℕ)) :
    constantAction (F := F) a b idx = diagonalTensor (F := F) a b idx := by
  by_cases hlow : (idx 1).val < (b : ℕ)
  · rw [constantAction_top_low a b idx hlow]
    rw [thirdBase_top_low_value a b hb _ _ _ hlow hz]
    rw [diagonalTensor_top_value a b hb idx hr hz]
  · have hedge : (idx 1).val = (b : ℕ) := by omega
    rw [constantAction_top_edge a b idx hedge]
    rw [thirdBase_top_edge_value a b hb _ _ hz]
    rw [diagonalTensor_top_value a b hb idx hr hz]
    simp only [hedge]

-- The lower-left block vanishes.  Again, most of the budget is spent reducing
-- truncated natural subtraction introduced by the block coordinates.
set_option maxHeartbeats 900000 in
private theorem constantAction_bottom_left (a b : ℕ+) (hb : 2 ≤ b)
    (idx : ∀ i : Fin 3, Fin (fmt a ((b + 1) + (b - 1))
      ((a + (b + 1) - 1) + (a + (b - 1) - 1)) i))
    (hr : ¬ (idx 1).val < (b : ℕ) + 1)
    (hz : (idx 2).val < (a : ℕ) + (b : ℕ)) :
    constantAction (F := F) a b idx = 0 := by
  classical
  rcases sizeFacts a b hb with ⟨hrow, hsrow, hc, hctop, hcbot, hout⟩
  have haNat : 1 ≤ (a : ℕ) := a.pos
  have hbNat : 2 ≤ (b : ℕ) := by exact_mod_cast hb
  have hi0 := (idx 0).isLt
  have hi1 := (idx 1).isLt
  have hi2 := (idx 2).isLt
  change (idx 0).val < (a : ℕ) at hi0
  change (idx 1).val < (((b + 1) + (b - 1) : ℕ+) : ℕ) at hi1
  change (idx 2).val <
    (((a + (b + 1) - 1) + (a + (b - 1) - 1) : ℕ+) : ℕ) at hi2
  rw [hrow] at hi1
  rw [hout] at hi2
  have hr' : (b : ℕ) + 1 ≤ (idx 1).val := by omega
  rw [constantAction_bottom a b hb idx hr']
  simp [thirdBase, sourceColumn, diagonalTensor, pdsum, polmul, fmt,
    hr, hz, hrow, hsrow, hc, hctop, hcbot, hout]
  split_ifs
  all_goals try simp only [Fin.ext_iff, Fin.val_zero] at *
  all_goals first | omega | ring

-- The bottom-right block is the smaller multiplication tensor.
set_option maxHeartbeats 500000 in
private theorem constantAction_bottom_right (a b : ℕ+) (hb : 2 ≤ b)
    (idx : ∀ i : Fin 3, Fin (fmt a ((b + 1) + (b - 1))
      ((a + (b + 1) - 1) + (a + (b - 1) - 1)) i))
    (hr : ¬ (idx 1).val < (b : ℕ) + 1)
    (hz : ¬ (idx 2).val < (a : ℕ) + (b : ℕ)) :
    constantAction (F := F) a b idx = diagonalTensor (F := F) a b idx := by
  classical
  rcases sizeFacts a b hb with ⟨hrow, hsrow, hc, hctop, hcbot, hout⟩
  have haNat : 1 ≤ (a : ℕ) := a.pos
  have hbNat : 2 ≤ (b : ℕ) := by exact_mod_cast hb
  have hi0 := (idx 0).isLt
  have hi1 := (idx 1).isLt
  have hi2 := (idx 2).isLt
  change (idx 0).val < (a : ℕ) at hi0
  change (idx 1).val < (((b + 1) + (b - 1) : ℕ+) : ℕ) at hi1
  change (idx 2).val <
    (((a + (b + 1) - 1) + (a + (b - 1) - 1) : ℕ+) : ℕ) at hi2
  rw [hrow] at hi1
  rw [hout] at hi2
  have hr' : (b : ℕ) + 1 ≤ (idx 1).val := by omega
  rw [constantAction_bottom a b hb idx hr']
  let c := (a : ℕ) + (b : ℕ) - 1
  let r := (idx 1).val - ((b : ℕ) + 1)
  have hc1 : c + 1 = (a : ℕ) + (b : ℕ) := by dsimp only [c]; omega
  have hz' : c + 1 ≤ (idx 2).val := by omega
  have hrange : r + 1 < (b : ℕ) := by dsimp only [r]; omega
  have hjBottom : ¬ (b : ℕ) + r < (b : ℕ) := by omega
  have hsBottom :
      (sourceColumn a b (idx 0)
        ⟨(b : ℕ) + r, by
          calc
            (b : ℕ) + r < 2 * (b : ℕ) := by omega
            _ = ((b + b : ℕ+) : ℕ) := hsrow.symm⟩).val =
        c + (idx 0).val + r := by
    simp [sourceColumn, hjBottom, c]
  have hsTop :
      (sourceColumn a b (idx 0)
        ⟨r + 1, by
          calc
            r + 1 < 2 * (b : ℕ) := by omega
            _ = ((b + b : ℕ+) : ℕ) := hsrow.symm⟩).val =
        (idx 0).val + r + 1 := by
    simp [sourceColumn, hrange]
    omega
  have hthird (y : Fin (((a + b - 1) + (a + b - 1) : ℕ+) : ℕ)) :
      thirdBase (F := F) a b (idx 2) y =
        if y.val = c + ((idx 2).val - (c + 1)) then 1 else 0 := by
    simp [thirdBase, c, show ¬ (idx 2).val < c + 1 by omega]
  dsimp only [r] at hrange hjBottom hsBottom hsTop ⊢
  rw [hthird, hthird, diagonalTensor_bottom_value a b hb idx hr hz]
  rw [hsBottom, hsTop]
  simp [hc1]
  clear hsBottom hsTop hthird
  dsimp only [c] at *
  have hsecond : ¬ (idx 0).val + ((idx 1).val - ((b : ℕ) + 1)) + 1 =
      (a : ℕ) + (b : ℕ) - 1 +
        ((idx 2).val - ((a : ℕ) + (b : ℕ))) := by omega
  simp only [if_neg hsecond, sub_zero]
  split_ifs
  all_goals first | omega | ring

-- Coordinate form of the block-upper-triangular statement obtained from the
-- exact sequence.  The top-right block is deliberately left as itself.
set_option maxHeartbeats 100000 in
private theorem constantAction_shape (a b : ℕ+) (hb : 2 ≤ b)
    (idx : ∀ i : Fin 3, Fin (fmt a ((b + 1) + (b - 1))
      ((a + (b + 1) - 1) + (a + (b - 1) - 1)) i)) :
    constantAction (F := F) a b idx =
      if (idx 1).val < (b : ℕ) + 1 then
        if (idx 2).val < (a : ℕ) + (b : ℕ) then
          diagonalTensor (F := F) a b idx
        else constantAction (F := F) a b idx
      else if (idx 2).val < (a : ℕ) + (b : ℕ) then
        0
      else diagonalTensor (F := F) a b idx := by
  by_cases hr : (idx 1).val < (b : ℕ) + 1
  · simp only [if_pos hr]
    by_cases hz : (idx 2).val < (a : ℕ) + (b : ℕ)
    · simpa only [if_pos hz] using! constantAction_top_left (F := F) a b hb idx hr hz
    · simp only [if_neg hz]
  · simp only [if_neg hr]
    by_cases hz : (idx 2).val < (a : ℕ) + (b : ℕ)
    · simpa only [if_pos hz] using! constantAction_bottom_left (F := F) a b hb idx hr hz
    · simpa only [if_neg hz] using! constantAction_bottom_right (F := F) a b hb idx hr hz

/-- Weight one on the upper second-leg block and weight zero on the lower. -/
private noncomputable def secondScale (b : ℕ+)
    (x : Fin (((b + 1) + (b - 1) : ℕ+) : ℕ)) : Polynomial F :=
  if x.val < (b : ℕ) + 1 then Polynomial.X else 1

/-- Weight zero on the upper third-leg block and weight one on the lower. -/
private noncomputable def thirdScale (a b : ℕ+)
    (x : Fin (((a + (b + 1) - 1) + (a + (b - 1) - 1) : ℕ+) : ℕ)) :
    Polynomial F :=
  if x.val < (a : ℕ) + (b : ℕ) then 1 else Polynomial.X

/-- The polynomial matrices: the constant exact-sequence base change followed
by the two complementary block scalings. -/
private noncomputable def degenerationMatrix (a b : ℕ+) : ∀ i : Fin 3,
    Matrix
      (Fin ((fmt a ((b + 1) + (b - 1))
        ((a + (b + 1) - 1) + (a + (b - 1) - 1))) i))
      (Fin ((fmt a (b + b) ((a + b - 1) + (a + b - 1))) i))
      (Polynomial F)
  | 0 => fun x y => Polynomial.C (baseMatrix (F := F) a b 0 x y)
  | 1 => fun x y => secondScale (F := F) b x *
      Polynomial.C (baseMatrix (F := F) a b 1 x y)
  | 2 => fun x y => thirdScale (F := F) a b x *
      Polynomial.C (baseMatrix (F := F) a b 2 x y)

-- Polynomial transport is the constant transport times the two row weights.
set_option maxHeartbeats 300000 in
private theorem degenerationAction_eq (a b : ℕ+)
    (idx : ∀ i : Fin 3, Fin (fmt a ((b + 1) + (b - 1))
      ((a + (b + 1) - 1) + (a + (b - 1) - 1)) i)) :
    (∑ sidx : (∀ i : Fin 3, Fin (fmt a (b + b)
        ((a + b - 1) + (a + b - 1)) i)),
      (∏ i : Fin 3, degenerationMatrix (F := F) a b i (idx i) (sidx i)) *
        Polynomial.C (pdsum (polmul (F := F) a b) (polmul a b) rfl sidx)) =
      secondScale (F := F) b (idx 1) * thirdScale (F := F) a b (idx 2) *
        Polynomial.C (constantAction (F := F) a b idx) := by
  classical
  unfold constantAction
  calc
    (∑ sidx : (∀ i : Fin 3, Fin (fmt a (b + b)
        ((a + b - 1) + (a + b - 1)) i)),
      (∏ i : Fin 3, degenerationMatrix (F := F) a b i (idx i) (sidx i)) *
        Polynomial.C (pdsum (polmul (F := F) a b) (polmul a b) rfl sidx)) =
      ∑ sidx, secondScale (F := F) b (idx 1) * thirdScale (F := F) a b (idx 2) *
        Polynomial.C
          ((∏ i : Fin 3, baseMatrix (F := F) a b i (idx i) (sidx i)) *
            pdsum (polmul (F := F) a b) (polmul a b) rfl sidx) := by
          apply Finset.sum_congr rfl
          intro sidx _
          simp [degenerationMatrix, Fin.prod_univ_succ, map_mul]
          ring
    _ = secondScale (F := F) b (idx 1) * thirdScale (F := F) a b (idx 2) *
        ∑ sidx, Polynomial.C
          ((∏ i : Fin 3, baseMatrix (F := F) a b i (idx i) (sidx i)) *
            pdsum (polmul (F := F) a b) (polmul a b) rfl sidx) := by
          rw [Finset.mul_sum]
    _ = secondScale (F := F) b (idx 1) * thirdScale (F := F) a b (idx 2) *
        Polynomial.C
          (∑ sidx, (∏ i : Fin 3, baseMatrix (F := F) a b i (idx i) (sidx i)) *
            pdsum (polmul (F := F) a b) (polmul a b) rfl sidx) := by
          rw [map_sum]

/-- The only error is the top-right block, appearing in degree two. -/
private noncomputable def errorTensor (a b : ℕ+) :
    T3 F (fmt a ((b + 1) + (b - 1))
      ((a + (b + 1) - 1) + (a + (b - 1) - 1))) := fun idx =>
  if (idx 1).val < (b : ℕ) + 1 then
    if (idx 2).val < (a : ℕ) + (b : ℕ) then 0
    else constantAction (F := F) a b idx
  else 0

set_option maxHeartbeats 200000 in
private theorem diagonalTensor_top_right_zero (a b : ℕ+) (hb : 2 ≤ b)
    (idx : ∀ i : Fin 3, Fin (fmt a ((b + 1) + (b - 1))
      ((a + (b + 1) - 1) + (a + (b - 1) - 1)) i))
    (hr : (idx 1).val < (b : ℕ) + 1)
    (hz : ¬ (idx 2).val < (a : ℕ) + (b : ℕ)) :
    diagonalTensor (F := F) a b idx = 0 := by
  rcases sizeFacts a b hb with ⟨hrow, hsrow, hc, hctop, hcbot, hout⟩
  simp [diagonalTensor, pdsum, fmt, hr, hz, hctop]

set_option maxHeartbeats 200000 in
private theorem diagonalTensor_bottom_left_zero (a b : ℕ+) (hb : 2 ≤ b)
    (idx : ∀ i : Fin 3, Fin (fmt a ((b + 1) + (b - 1))
      ((a + (b + 1) - 1) + (a + (b - 1) - 1)) i))
    (hr : ¬ (idx 1).val < (b : ℕ) + 1)
    (hz : (idx 2).val < (a : ℕ) + (b : ℕ)) :
    diagonalTensor (F := F) a b idx = 0 := by
  rcases sizeFacts a b hb with ⟨hrow, hsrow, hc, hctop, hcbot, hout⟩
  simp [diagonalTensor, pdsum, fmt, hr, hz, hctop]

-- The weighted block-triangular tensor has degree-one diagonal and degree-two
-- top-right error.
set_option maxHeartbeats 300000 in
private theorem scaledAction_eq (a b : ℕ+) (hb : 2 ≤ b)
    (idx : ∀ i : Fin 3, Fin (fmt a ((b + 1) + (b - 1))
      ((a + (b + 1) - 1) + (a + (b - 1) - 1)) i)) :
    secondScale (F := F) b (idx 1) * thirdScale (F := F) a b (idx 2) *
        Polynomial.C (constantAction (F := F) a b idx) =
      Polynomial.X ^ 1 * Polynomial.C (diagonalTensor (F := F) a b idx) +
        Polynomial.X ^ 2 * Polynomial.C (errorTensor (F := F) a b idx) := by
  rw [constantAction_shape a b hb idx]
  by_cases hr : (idx 1).val < (b : ℕ) + 1
  · by_cases hz : (idx 2).val < (a : ℕ) + (b : ℕ)
    · simp [secondScale, thirdScale, errorTensor, hr, hz]
    · rw [diagonalTensor_top_right_zero a b hb idx hr hz]
      simp [secondScale, thirdScale, errorTensor, hr, hz]
      ring
  · by_cases hz : (idx 2).val < (a : ℕ) + (b : ℕ)
    · rw [diagonalTensor_bottom_left_zero a b hb idx hr hz]
      simp [secondScale, thirdScale, errorTensor, hr, hz]
    · simp [secondScale, thirdScale, errorTensor, hr, hz]

-- The larger budget covers normalization of the statement contract's
-- definitionally equal formats.
set_option maxHeartbeats 400000 in
/-- `CG.1`: concavity of the polynomial-multiplication tensors, as an
explicit degeneration on the last two legs. -/
theorem proof_CG_1 : OM_S_CG_1 := by
  intro F _ a b hb
  change Degen23
    (pdsum (polmul (F := F) a (b + 1)) (polmul a (b - 1)) rfl)
    (pdsum (polmul a b) (polmul a b) rfl) rfl
  refine ⟨1, 1, degenerationMatrix (F := F) a b,
    fun _ => errorTensor (F := F) a b, ?_, ?_⟩
  · intro x y
    simp [degenerationMatrix, baseMatrix]
  · intro idx
    change
      (∑ sidx : (∀ i : Fin 3, Fin (fmt a (b + b)
          ((a + b - 1) + (a + b - 1)) i)),
        (∏ i : Fin 3, degenerationMatrix (F := F) a b i (idx i) (sidx i)) *
          Polynomial.C (pdsum (polmul (F := F) a b) (polmul a b) rfl sidx)) =
        Polynomial.X ^ 1 * Polynomial.C (diagonalTensor (F := F) a b idx) +
          ∑ j : Fin 1, Polynomial.X ^ (1 + j.val + 1) *
            Polynomial.C (errorTensor (F := F) a b idx)
    rw [degenerationAction_eq a b idx, scaledAction_eq a b hb idx]
    simp

end OM.PolMul.ConcavityDegeneration

