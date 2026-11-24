import Lib.OM.NNN11.Network
import Lib.OM.NNN11.Cyclic

/-! Explicit 7/7/6 tilings and rectangular low/high-bit bond equivalences. -/
noncomputable section
open scoped BigOperators Classical
namespace OM.NNN11.Tiles
open Network
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

def tilePosition : Fin 3 ⊕ Fin 4 → ZMod 7 :=
  Sum.elim ![0, 1, 3] ![2, 4, 5, 6]

def tileEquiv : (Fin 3 ⊕ Fin 4) ≃ ZMod 7 :=
  Equiv.ofBijective tilePosition (by decide +kernel)

def heavyTiles : (Fin 21 ⊕ Fin 28) ≃ Fin 7 × ZMod 7 :=
  (Equiv.sumCongr finProdFinEquiv.symm finProdFinEquiv.symm).trans
    ((Equiv.prodSumDistrib (Fin 7) (Fin 3) (Fin 4)).symm.trans
      (Equiv.prodCongr (Equiv.refl _) tileEquiv))

lemma heavy_left_role : ∀ i : Fin 21, (heavyTiles (Sum.inl i)).2 ∈ fano := by
  decide +kernel

lemma heavy_right_role : ∀ i : Fin 28, (heavyTiles (Sum.inr i)).2 ∉ fano := by
  decide +kernel

/-- Three 3/4 tiles followed by three 4/3 tiles. -/
def lightPosition : Fin 21 ⊕ Fin 21 → Fin 6 × ZMod 7
  | .inl i =>
    if h : i.val < 9 then
      (⟨i.val / 3, by omega⟩, ![0, 1, 3] ⟨i.val % 3, Nat.mod_lt _ (by omega)⟩)
    else
      (⟨3 + (i.val - 9) / 4, by omega⟩,
        ![2, 4, 5, 6] ⟨(i.val - 9) % 4, Nat.mod_lt _ (by omega)⟩)
  | .inr i =>
    if h : i.val < 12 then
      (⟨i.val / 4, by omega⟩, ![2, 4, 5, 6] ⟨i.val % 4, Nat.mod_lt _ (by omega)⟩)
    else
      (⟨3 + (i.val - 12) / 3, by omega⟩,
        ![0, 1, 3] ⟨(i.val - 12) % 3, Nat.mod_lt _ (by omega)⟩)

def lightTiles : (Fin 21 ⊕ Fin 21) ≃ Fin 6 × ZMod 7 :=
  Equiv.ofBijective lightPosition (by decide +kernel)

def lightRole (s : Fin 6 × ZMod 7) : Prop :=
  if s.1.val < 3 then s.2 ∈ fano else s.2 ∉ fano

lemma light_left_role : ∀ i : Fin 21, lightRole (lightTiles (Sum.inl i)) := by
  unfold lightRole
  decide +kernel

lemma light_right_role : ∀ i : Fin 21, ¬ lightRole (lightTiles (Sum.inr i)) := by
  unfold lightRole
  decide +kernel

/-- Splitting by positions preserves every unmatched high digit. -/
def splitDigits (m L : ℕ) (h : L ≤ m) (E : Type) :
    (Fin m → E) ≃ (Fin L → E) × (Fin (m - L) → E) where
  toFun x := (fun i => x ⟨i.val, lt_of_lt_of_le i.isLt h⟩,
    fun i => x ⟨L + i.val, by omega⟩)
  invFun x := fun i => if hi : i.val < L then x.1 ⟨i.val, hi⟩ else
    x.2 ⟨i.val - L, by omega⟩
  left_inv x := by
    funext i
    dsimp
    split_ifs with hi
    · rfl
    · congr 1
      apply Fin.ext
      dsimp
      omega
  right_inv x := by
    apply Prod.ext
    · funext i
      simp only [dif_pos i.isLt]
    · funext i
      dsimp
      rw [dif_neg (by omega : ¬ L + i.val < L)]
      exact congrArg x.2 (Fin.ext (Nat.add_sub_cancel_left L i.val))

/-- Keep low and high coordinates as separate words on each ownership block. -/
def splitBond (A B E : Type) (x y L : ℕ) (hx : L ≤ x) (hy : L ≤ y) :
    BondAB A B (Fin x → E) (Fin y → E) ≃
      ((A → Fin L → E) × (B → Fin L → E)) ×
        ((A → Fin (y - L) → E) × (B → Fin (x - L) → E)) where
  toFun w := ((fun a => (splitDigits y L hy E (w.1 a)).1,
    fun b => (splitDigits x L hx E (w.2 b)).1),
    (fun a => (splitDigits y L hy E (w.1 a)).2,
    fun b => (splitDigits x L hx E (w.2 b)).2))
  invFun w := (fun a => (splitDigits y L hy E).symm (w.1.1 a, w.2.1 a),
    fun b => (splitDigits x L hx E).symm (w.1.2 b, w.2.2 b))
  left_inv w := by
    apply Prod.ext <;> funext i <;> exact Equiv.symm_apply_apply _ _
  right_inv w := by
    rcases w with ⟨⟨a, b⟩, ⟨c, d⟩⟩
    simp only [Equiv.apply_symm_apply]

def exchangeDigits (b L : ℕ) (E : Type) :
    (Fin b × ZMod 7 → Fin L → E) ≃ (Fin b × Fin L → ZMod 7 → E) where
  toFun w := fun td j => w (td.1, j) td.2
  invFun w := fun tj d => w (tj.1, d) tj.2
  left_inv _ := rfl
  right_inv _ := rfl

/-- Enumerate tile-digit pairs in `Fin (b*L)` to use the existing F7 action. -/
def matchedBasis {A B : Type} {b : ℕ} (e : (A ⊕ B) ≃ Fin b × ZMod 7)
    (L : ℕ) (E : Type) :
    ((A → Fin L → E) × (B → Fin L → E)) ≃ Slots (b * L) E :=
  (Equiv.sumArrowEquivProdArrow A B (Fin L → E)).symm.trans
    ((e.arrowCongr (Equiv.refl _)).trans
      ((exchangeDigits b L E).trans (finProdFinEquiv.arrowCongr (Equiv.refl _))))

/-- Actual rectangular physical bond = matched tiles × all untouched high bits. -/
def bondBasis {A B : Type} {b : ℕ} (e : (A ⊕ B) ≃ Fin b × ZMod 7)
    (x y L : ℕ) (hx : L ≤ x) (hy : L ≤ y) (E : Type) :
    BondAB A B (Fin x → E) (Fin y → E) ≃
      Slots (b * L) E × ((A → Fin (y - L) → E) × (B → Fin (x - L) → E)) :=
  (splitBond A B E x y L hx hy).trans
    (Equiv.prodCongr (matchedBasis e L E) (Equiv.refl _))

def heavyBasis (x y : ℕ) :
    BondAB (Fin 21) (Fin 28) (Fin x → ZMod 2) (Fin y → ZMod 2) ≃
      Slots (7 * min x y) (ZMod 2) ×
        ((Fin 21 → Fin (y - min x y) → ZMod 2) ×
          (Fin 28 → Fin (x - min x y) → ZMod 2)) :=
  bondBasis heavyTiles x y (min x y) (min_le_left _ _) (min_le_right _ _) _

def lightBasis (x y : ℕ) :
    BondAB (Fin 21) (Fin 21) (Fin x → ZMod 2) (Fin y → ZMod 2) ≃
      Slots (6 * min x y) (ZMod 2) ×
        ((Fin 21 → Fin (y - min x y) → ZMod 2) ×
          (Fin 21 → Fin (x - min x y) → ZMod 2)) :=
  bondBasis lightTiles x y (min x y) (min_le_left _ _) (min_le_right _ _) _

section Action
variable {E F X : Type} {N : ℕ} (e : E ≃ Slots N X × F)

def shiftBond (c : Word N) (w : E) : E := e.symm (shift c (e w).1, (e w).2)

lemma shiftBond_zero (w : E) : shiftBond e 0 w = w := by
  simp [shiftBond, shift_zero]

lemma shiftBond_add (c d : Word N) (w : E) :
    shiftBond e (c + d) w = shiftBond e d (shiftBond e c w) := by
  simp [shiftBond, shift_add]

lemma shiftBond_high (c : Word N) (w : E) : (e (shiftBond e c w)).2 = (e w).2 := by
  simp [shiftBond]

def bondAction (c : Word N) : Module.End ℂ (E → ℂ) where
  toFun f w := f (shiftBond e c w)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma bondAction_zero : bondAction e 0 = 1 := by
  ext f w
  simp [bondAction, shiftBond_zero]

lemma bondAction_add (c d : Word N) :
    bondAction e (c + d) = bondAction e c * bondAction e d := by
  ext f w
  exact congrArg f (shiftBond_add e c d w)

def bondKernel (c : Word N) : Operator E := fun w v => if shiftBond e c w = v then 1 else 0

lemma bondKernel_zero : bondKernel e 0 = Network.identity E := by
  funext w v
  simp [bondKernel, shiftBond_zero, Network.identity]

/-- Cheap characters on the entire physical bond, with all high bits fixed.
Dependent generators and rank-zero factorizations are both allowed. -/
theorem exists_bond_factorization [Fintype E] {r : ℕ}
    (code : Word r →ₗ[ZMod 7] Word N) :
    ∃ (χ : AddChar (Word r) ℂ) (R : ℕ) (U V : Fin R → E → ℂ),
      R * 7 ^ r ≤ Fintype.card E ∧
      ∀ w v, (∑ p, U p w * V p v) =
        Network.identity E w v +
          ∑ c ∈ Finset.univ.erase (0 : Word r), χ c * bondKernel e (code c) w v := by
  obtain ⟨χ, R, U, V, hR, hUV⟩ := NNN8.exists_character_factorization
    (fun c => bondAction e (code c))
    (by simp [bondAction_zero]) (by intro a b; simp [bondAction_add])
  refine ⟨χ, R, U, V, ?_, ?_⟩
  · simpa only [word_card] using! hR
  · intro w v
    rw [hUV, ← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : Word r))]
    simp [bondAction, bondKernel, Pi.single_apply, Network.identity, shiftBond_zero, eq_comm]
end Action

end OM.NNN11.Tiles
