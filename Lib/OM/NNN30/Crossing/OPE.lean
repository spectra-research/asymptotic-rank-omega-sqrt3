import Lib.OM.NNN30.Crossing.Wick


namespace OM.NNN30.Crossing

/-- The five kinds of labels: the moving point `z`, its fusion partner `p`, the other finite point
`q`, the point at infinity `inf`, and the fused modes `sig` (at `p`). -/
inductive Pt
  | z | p | q | inf | sig
  deriving DecidableEq

/-- A far label: at `q` or at infinity, with a positive mode. -/
def IsFar (u : Pt × ℕ) : Prop := (u.1 = Pt.q ∨ u.1 = Pt.inf) ∧ 0 < u.2

section OPE

open PowerSeries

variable (β : Pt × ℕ → Pt × ℕ → ℂ⟦X⟧)

/-- The value of the "three-point function": σ-modes `T` against the far labels `Y`. -/
noncomputable def farVal (T : Multiset ℕ) (Y : Multiset (Pt × ℕ)) : ℂ :=
  constantCoeff (wickM β (T.map (fun n => (Pt.sig, n)) + Y))

/-- `f` factors through the partitions of `m`, with the σ-modes `S` already present. -/
def Fact (m : ℕ) (S : Multiset ℕ) (f : Multiset (Pt × ℕ) → ℂ) : Prop :=
  ∃ c : m.Partition → ℂ, ∀ Y : Multiset (Pt × ℕ), (∀ y ∈ Y, IsFar y) →
    f Y = ∑ τ, c τ * farVal β (S + τ.parts) Y

variable {β}

theorem Fact.add {m : ℕ} {S : Multiset ℕ} {f g : Multiset (Pt × ℕ) → ℂ}
    (hf : Fact β m S f) (hg : Fact β m S g) : Fact β m S (fun Y => f Y + g Y) := by
  obtain ⟨c, hc⟩ := hf
  obtain ⟨d, hd⟩ := hg
  refine ⟨fun τ => c τ + d τ, fun Y hY => ?_⟩
  show f Y + g Y = _
  rw [hc Y hY, hd Y hY, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro τ _
  ring

theorem Fact.smul {m : ℕ} {S : Multiset ℕ} {f : Multiset (Pt × ℕ) → ℂ} (a : ℂ)
    (hf : Fact β m S f) : Fact β m S (fun Y => a * f Y) := by
  obtain ⟨c, hc⟩ := hf
  refine ⟨fun τ => a * c τ, fun Y hY => ?_⟩
  show a * f Y = _
  rw [hc Y hY, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro τ _
  ring

theorem Fact.zero {m : ℕ} {S : Multiset ℕ} : Fact β m S (fun _ => 0) :=
  ⟨fun _ => 0, fun Y _ => by simp⟩

theorem Fact.sum {ι : Type*} (t : Finset ι) {m : ℕ} {S : Multiset ℕ}
    {f : ι → Multiset (Pt × ℕ) → ℂ} (hf : ∀ i ∈ t, Fact β m S (f i)) :
    Fact β m S (fun Y => ∑ i ∈ t, f i Y) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using (Fact.zero (β := β) (m := m) (S := S))
  | insert i t hi ih =>
    have h1 := hf i (Finset.mem_insert_self i t)
    have h2 := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
    have := Fact.add h1 h2
    simpa [Finset.sum_insert hi] using this

theorem Fact.multiset_sum {ι : Type*} (s : Multiset ι) {m : ℕ} {S : Multiset ℕ}
    {f : ι → Multiset (Pt × ℕ) → ℂ} (hf : ∀ i ∈ s, Fact β m S (f i)) :
    Fact β m S (fun Y => (s.map fun i => f i Y).sum) := by
  induction s using Multiset.induction_on with
  | empty => simpa using (Fact.zero (β := β) (m := m) (S := S))
  | cons i t ih =>
    have h1 := hf i (Multiset.mem_cons_self i t)
    have h2 := ih (fun j hj => hf j (Multiset.mem_cons_of_mem hj))
    have := Fact.add h1 h2
    simpa [Multiset.map_cons, Multiset.sum_cons] using this

/-- The partition `n :: τ` of `m` built from a partition `τ` of `m - n`. -/
def consPart {m n : ℕ} (hn : 0 < n) (hnm : n ≤ m) (τ : (m - n).Partition) : m.Partition where
  parts := n ::ₘ τ.parts
  parts_pos := by
    intro i hi
    rcases Multiset.mem_cons.mp hi with h | h
    · omega
    · exact τ.parts_pos h
  parts_sum := by
    rw [Multiset.sum_cons, τ.parts_sum]
    omega

theorem Fact.shift {m n : ℕ} (hn : 0 < n) (hnm : n ≤ m) {S : Multiset ℕ}
    {f : Multiset (Pt × ℕ) → ℂ} (hf : Fact β (m - n) (n ::ₘ S) f) : Fact β m S f := by
  classical
  obtain ⟨c, hc⟩ := hf
  refine ⟨fun τ => ∑ τ' ∈ Finset.univ.filter (fun τ' => consPart hn hnm τ' = τ), c τ', ?_⟩
  intro Y hY
  rw [hc Y hY]
  simp only [Finset.sum_mul]
  have e : ∀ τ : m.Partition,
      ∑ τ' ∈ Finset.univ.filter (fun τ' => consPart hn hnm τ' = τ), c τ' * farVal β (S + τ.parts) Y =
        ∑ τ' ∈ Finset.univ.filter (fun τ' => consPart hn hnm τ' = τ),
          c τ' * farVal β (S + (consPart hn hnm τ').parts) Y := by
    intro τ
    apply Finset.sum_congr rfl
    intro τ' hτ'
    rw [(Finset.mem_filter.mp hτ').2]
  rw [Finset.sum_congr rfl (fun τ _ => e τ),
    Finset.sum_fiberwise_of_maps_to (fun _ _ => Finset.mem_univ _)
      (fun τ' => c τ' * farVal β (S + (consPart hn hnm τ').parts) Y)]
  apply Finset.sum_congr rfl
  intro τ' _
  simp only [consPart, Multiset.cons_add, Multiset.add_cons]

theorem Fact.congr {m : ℕ} {S : Multiset ℕ} {f g : Multiset (Pt × ℕ) → ℂ}
    (hfg : ∀ Y : Multiset (Pt × ℕ), (∀ y ∈ Y, IsFar y) → f Y = g Y) (hg : Fact β m S g) :
    Fact β m S f := by
  obtain ⟨c, hc⟩ := hg
  exact ⟨c, fun Y hY => by rw [hfg Y hY, hc Y hY]⟩

/-- Hypotheses on the pairing for the operator product expansion at `p`. -/
structure OPEHyp (β : Pt × ℕ → Pt × ℕ → ℂ⟦X⟧) : Prop where
  symm : ∀ u v, β u v = β v u
  zz : ∀ a b, β (Pt.z, a) (Pt.z, b) = 0
  pp : ∀ a b, β (Pt.p, a) (Pt.p, b) = 0
  zs : ∀ a b, β (Pt.z, a) (Pt.sig, b) = 0
  ps : ∀ a b, β (Pt.p, a) (Pt.sig, b) = 0
  ss : ∀ a b, β (Pt.sig, a) (Pt.sig, b) = 0
  zp : ∀ a b, ∃ γ : ℂ, β (Pt.z, a) (Pt.p, b) = C γ
  zfar : ∀ a, 0 < a → ∀ y, IsFar y → ∀ n, coeff n (β (Pt.z, a) y) =
    if a ≤ n then ((n - 1).choose (n - a) : ℂ) * constantCoeff (β (Pt.sig, n) y) else 0
  pfar : ∀ b y, IsFar y → β (Pt.p, b) y = X ^ b * β (Pt.sig, b) y
  farconst : ∀ u v, (IsFar u ∨ u.1 = Pt.sig) → (IsFar v ∨ v.1 = Pt.sig) →
    β u v = C (constantCoeff (β u v))

theorem prod_map_X_pow (A : Multiset ℕ) :
    (A.map fun b => (X : ℂ⟦X⟧) ^ b).prod = X ^ A.sum := by
  induction A using Multiset.induction_on with
  | empty => simp
  | cons b A ih => rw [Multiset.map_cons, Multiset.prod_cons, ih, Multiset.sum_cons, pow_add]

/-- The base case: without `z`-modes the `p`-modes become fused modes, up to the power of `X`. -/
theorem ope_base (h : OPEHyp β) (S A : Multiset ℕ) (Y : Multiset (Pt × ℕ))
    (hY : ∀ y ∈ Y, IsFar y) :
    wickM β (S.map (fun n => (Pt.sig, n)) + A.map (fun b => (Pt.p, b)) + Y) =
      X ^ A.sum * C (farVal β (S + A) Y) := by
  classical
  let g : Pt × ℕ → Pt × ℕ := fun u => if u.1 = Pt.p then (Pt.sig, u.2) else u
  let σ : Pt × ℕ → ℂ⟦X⟧ := fun u => if u.1 = Pt.p then X ^ u.2 else 1
  let β' : Pt × ℕ → Pt × ℕ → ℂ⟦X⟧ := fun u v => σ u * σ v * β (g u) (g v)
  have hgs : ∀ u v, β (g u) (g v) = β (g v) (g u) := fun u v => h.symm _ _
  have hβ' : ∀ u v, β' u v = β' v u := by
    intro u v; simp only [β']; rw [h.symm (g u) (g v)]; ring
  set s := S.map (fun n => (Pt.sig, n)) + A.map (fun b => (Pt.p, b)) + Y with hs
  have hmem : ∀ u ∈ s, u.1 = Pt.sig ∨ u.1 = Pt.p ∨ IsFar u := by
    intro u hu
    rcases Multiset.mem_add.mp hu with hu | hu
    · rcases Multiset.mem_add.mp hu with hu | hu
      · obtain ⟨n, _, rfl⟩ := Multiset.mem_map.mp hu; exact Or.inl rfl
      · obtain ⟨b, _, rfl⟩ := Multiset.mem_map.mp hu; exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (hY u hu))
  have key : ∀ u v, (u.1 = Pt.sig ∨ u.1 = Pt.p ∨ IsFar u) →
      (v.1 = Pt.sig ∨ v.1 = Pt.p ∨ IsFar v) → β u v = β' u v := by
    rintro ⟨pu, a⟩ ⟨pv, b⟩ hu hv
    simp only at hu hv
    simp only [β', σ, g]
    rcases hu with hu | hu | hu <;> rcases hv with hv | hv | hv
    · subst hu; subst hv; simp
    · subst hu; subst hv; simp [h.symm (Pt.sig, a) (Pt.p, b), h.ps, h.ss]
    · subst hu
      have : pv ≠ Pt.p := by rcases hv.1 with hv | hv <;> simp at hv <;> simp [hv]
      simp [this]
    · subst hu; subst hv; simp [h.ps, h.ss]
    · subst hu; subst hv; simp [h.pp, h.ss]
    · subst hu
      have : pv ≠ Pt.p := by rcases hv.1 with hv | hv <;> simp at hv <;> simp [hv]
      simp [this, h.pfar a (pv, b) hv]
    · have : pu ≠ Pt.p := by rcases hu.1 with hu | hu <;> simp at hu <;> simp [hu]
      subst hv; simp [this]
    · have : pu ≠ Pt.p := by rcases hu.1 with hu | hu <;> simp at hu <;> simp [hu]
      subst hv
      simp [this, h.symm (pu, a) (Pt.p, b), h.pfar b (pu, a) hu, h.symm (Pt.sig, b) (pu, a)]
    · have h1 : pu ≠ Pt.p := by rcases hu.1 with hu | hu <;> simp at hu <;> simp [hu]
      have h2 : pv ≠ Pt.p := by rcases hv.1 with hv | hv <;> simp at hv <;> simp [hv]
      simp [h1, h2]
  rw [wickM_congr h.symm hβ' s (fun u hu v hv => key u v (hmem u hu) (hmem v hv)),
    wickM_scale hgs hβ' σ (fun u v => rfl) s, ← wickM_map h.symm g s]
  have hsg : s.map g = (S + A).map (fun n => (Pt.sig, n)) + Y := by
    simp only [hs, Multiset.map_add, Multiset.map_map, Function.comp]
    have hYg : Y.map g = Y := by
      conv_rhs => rw [← Multiset.map_id Y]
      apply Multiset.map_congr rfl
      intro y hy
      have : y.1 ≠ Pt.p := by
        rcases (hY y hy).1 with h' | h' <;> rw [h'] <;> simp
      simp [g, this]
    rw [hYg]
    congr 1
  have hσ : (s.map σ).prod = X ^ A.sum := by
    simp only [hs, Multiset.map_add, Multiset.prod_add, Multiset.map_map, Function.comp]
    have h1 : (S.map fun n => σ (Pt.sig, n)).prod = 1 := by simp [σ]
    have h2 : (Y.map σ).prod = 1 := by
      apply Multiset.prod_eq_one
      intro x hx
      obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.mp hx
      have : y.1 ≠ Pt.p := by
        rcases (hY y hy).1 with h' | h' <;> rw [h'] <;> simp
      simp [σ, this]
    have h3 : (A.map fun b => σ (Pt.p, b)) = A.map fun b => (X : ℂ⟦X⟧) ^ b := by simp [σ]
    rw [h1, h2, h3, prod_map_X_pow]
    ring
  rw [hσ, hsg]
  congr 1
  -- the far Wick sum is a constant
  have hfar : ∀ u ∈ (S + A).map (fun n => (Pt.sig, n)) + Y, IsFar u ∨ u.1 = Pt.sig := by
    intro u hu
    rcases Multiset.mem_add.mp hu with hu | hu
    · obtain ⟨n, _, rfl⟩ := Multiset.mem_map.mp hu; exact Or.inr rfl
    · exact Or.inl (hY u hu)
  have hc : ∀ u v, β u v = β v u := h.symm
  have hcC : ∀ u v, C (constantCoeff (β u v)) = C (constantCoeff (β v u)) := by
    intro u v; rw [h.symm]
  rw [wickM_congr h.symm hcC _ (fun u hu v hv => h.farconst u v (hfar u hu) (hfar v hv)),
    wickM_ringHom C (fun u v => constantCoeff (β u v))]
  unfold farVal
  rw [wickM_congr h.symm hcC _ (fun u hu v hv => h.farconst u v (hfar u hu) (hfar v hv)),
    wickM_ringHom C (fun u v => constantCoeff (β u v))]
  simp

theorem multiset_sum_finset_sum {ι κ M : Type*} [AddCommMonoid M] (Y : Multiset ι)
    (t : Finset κ) (f : ι → κ → M) :
    (Y.map fun y => ∑ p ∈ t, f y p).sum = ∑ p ∈ t, (Y.map fun y => f y p).sum := by
  induction Y using Multiset.induction_on with
  | empty => simp
  | cons y Y ih => simp [Multiset.sum_cons, ih, Finset.sum_add_distrib]

/-- **Operator product expansion at `p`.**  The coefficient of `X^m` in the Wick sum of the `z`-modes
`Z`, the fused modes `S`, the `p`-modes `A` and far labels `Y` factors through the partitions of `m`:
it is a combination, with coefficients independent of `Y`, of the values `farVal β (S + τ) Y`. -/
theorem ope_fact (h : OPEHyp β) :
    ∀ (Z : Multiset ℕ), (∀ a ∈ Z, 0 < a) → ∀ (S A : Multiset ℕ), (∀ b ∈ A, 0 < b) → ∀ m : ℕ,
      Fact β m S (fun Y => coeff m (wickM β (Z.map (fun a => (Pt.z, a)) +
        ((S.map (fun n => (Pt.sig, n)) + A.map (fun b => (Pt.p, b))) + Y)))) := by
  classical
  intro Z
  induction Z using Multiset.induction_on with
  | empty =>
    intro _ S A hA m
    have hb : ∀ Y : Multiset (Pt × ℕ), (∀ y ∈ Y, IsFar y) →
        coeff m (wickM β ((0 : Multiset ℕ).map (fun a => (Pt.z, a)) +
          ((S.map (fun n => (Pt.sig, n)) + A.map (fun b => (Pt.p, b))) + Y))) =
          if m = A.sum then farVal β (S + A) Y else 0 := by
      intro Y hY
      rw [Multiset.map_zero, zero_add, ope_base h S A Y hY, coeff_X_pow_mul', coeff_C]
      by_cases hm : m = A.sum
      · simp [hm]
      · rw [if_neg hm]
        by_cases hle : A.sum ≤ m
        · rw [if_pos hle, if_neg]; omega
        · rw [if_neg hle]
    by_cases hm : m = A.sum
    · let τA : m.Partition := ⟨A, fun hi => hA _ hi, hm.symm⟩
      refine ⟨fun τ => if τ = τA then 1 else 0, fun Y hY => ?_⟩
      dsimp only
      rw [hb Y hY, if_pos hm, Finset.sum_eq_single τA]
      · simp [τA]
      · intro τ _ hτ; simp [hτ]
      · intro hn; exact absurd (Finset.mem_univ τA) hn
    · exact Fact.congr (fun Y hY => by rw [hb Y hY, if_neg hm]) Fact.zero
  | cons a Z ih =>
    intro hZ S A hA m
    have ha : 0 < a := hZ a (Multiset.mem_cons_self a Z)
    have hZ' : ∀ b ∈ Z, 0 < b := fun b hb => hZ b (Multiset.mem_cons_of_mem hb)
    -- abbreviations
    set zz : Multiset (Pt × ℕ) := Z.map (fun b => (Pt.z, b)) with hzz
    set ss : Multiset (Pt × ℕ) := S.map (fun n => (Pt.sig, n)) with hss
    set aa : Multiset (Pt × ℕ) := A.map (fun b => (Pt.p, b)) with haa
    -- the expansion of the head `z`-mode
    have expand : ∀ Y : Multiset (Pt × ℕ), (∀ y ∈ Y, IsFar y) →
        coeff m (wickM β ((a ::ₘ Z).map (fun b => (Pt.z, b)) + ((ss + aa) + Y))) =
          (A.map fun b => constantCoeff (β (Pt.z, a) (Pt.p, b)) *
            coeff m (wickM β (zz + ((ss + (A.erase b).map (fun c => (Pt.p, c))) + Y)))).sum +
          ∑ p ∈ Finset.HasAntidiagonal.antidiagonal m, (if a ≤ p.1 then ((p.1 - 1).choose (p.1 - a) : ℂ) else 0) *
            coeff p.2 (wickM β (zz + ((((p.1 ::ₘ S).map (fun n => (Pt.sig, n))) + aa) + Y))) := by
      intro Y hY
      rw [Multiset.map_cons, Multiset.cons_add, wickM_cons h.symm, Multiset.map_add,
        Multiset.map_add, Multiset.map_add, Multiset.sum_add, Multiset.sum_add, Multiset.sum_add]
      have h0z : (zz.map fun x => β (Pt.z, a) x *
          wickM β ((zz + (ss + aa + Y)).erase x)).sum = 0 := by
        apply Multiset.sum_eq_zero
        intro w hw
        obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.mp hw
        obtain ⟨b, _, rfl⟩ := Multiset.mem_map.mp hx
        rw [h.zz, zero_mul]
      have h0s : (ss.map fun x => β (Pt.z, a) x *
          wickM β ((zz + (ss + aa + Y)).erase x)).sum = 0 := by
        apply Multiset.sum_eq_zero
        intro w hw
        obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.mp hw
        obtain ⟨b, _, rfl⟩ := Multiset.mem_map.mp hx
        rw [h.zs, zero_mul]
      rw [h0z, h0s, zero_add, zero_add, map_add]
      congr 1
      · -- the `p`-partners
        rw [map_multiset_sum, Multiset.map_map, haa, Multiset.map_map]
        apply congrArg Multiset.sum
        apply Multiset.map_congr rfl
        intro b hb
        simp only [Function.comp]
        obtain ⟨γ, hγ⟩ := h.zp a b
        have he : (zz + (ss + A.map (fun b => (Pt.p, b)) + Y)).erase (Pt.p, b) =
            zz + ((ss + (A.erase b).map (fun c => (Pt.p, c))) + Y) := by
          have hmem : (Pt.p, b) ∈ A.map (fun b => (Pt.p, b)) := Multiset.mem_map_of_mem _ hb
          rw [Multiset.erase_add_right_pos _ (Multiset.mem_add.mpr (Or.inl
              (Multiset.mem_add.mpr (Or.inr hmem)))),
            Multiset.erase_add_left_pos _ (Multiset.mem_add.mpr (Or.inr hmem)),
            Multiset.erase_add_right_pos _ hmem,
            Multiset.map_erase _ (fun x y hxy => by simpa using hxy)]
        rw [he, hγ, coeff_C_mul, constantCoeff_C]
      · -- the far partners
        rw [map_multiset_sum, Multiset.map_map]
        have e1 : ∀ y ∈ Y, (coeff m ∘ fun x => β (Pt.z, a) x *
            wickM β ((zz + (ss + aa + Y)).erase x)) y =
            ∑ p ∈ Finset.HasAntidiagonal.antidiagonal m, (if a ≤ p.1 then ((p.1 - 1).choose (p.1 - a) : ℂ) else 0) *
              (constantCoeff (β (Pt.sig, p.1) y) *
                coeff p.2 (wickM β (zz + ((ss + aa) + Y.erase y)))) := by
          intro y hy
          simp only [Function.comp]
          rw [coeff_mul, Multiset.erase_add_right_pos _ (Multiset.mem_add.mpr (Or.inr hy)),
            Multiset.erase_add_right_pos _ hy]
          apply Finset.sum_congr rfl
          intro p _
          rw [h.zfar a ha y (hY y hy) p.1]
          split_ifs <;> ring
        rw [Multiset.map_congr rfl e1, multiset_sum_finset_sum]
        apply Finset.sum_congr rfl
        intro p _
        simp only [Multiset.sum_map_mul_left]
        congr 1
        -- the fused mode `(sig, p.1)` pairs only with the far labels
        have hT : ((p.1 ::ₘ S).map (fun n => (Pt.sig, n))) = (Pt.sig, p.1) ::ₘ ss := by
          rw [Multiset.map_cons]
        rw [hT, Multiset.cons_add, Multiset.cons_add, Multiset.add_cons, wickM_cons h.symm,
          Multiset.map_add, Multiset.map_add, Multiset.map_add, Multiset.sum_add,
          Multiset.sum_add, Multiset.sum_add]
        have z1 : (zz.map fun x => β (Pt.sig, p.1) x *
            wickM β ((zz + (ss + aa + Y)).erase x)).sum = 0 := by
          apply Multiset.sum_eq_zero
          intro w hw
          obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.mp hw
          obtain ⟨b, _, rfl⟩ := Multiset.mem_map.mp hx
          rw [h.symm, h.zs, zero_mul]
        have z2 : (ss.map fun x => β (Pt.sig, p.1) x *
            wickM β ((zz + (ss + aa + Y)).erase x)).sum = 0 := by
          apply Multiset.sum_eq_zero
          intro w hw
          obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.mp hw
          obtain ⟨b, _, rfl⟩ := Multiset.mem_map.mp hx
          rw [h.ss, zero_mul]
        have z3 : (aa.map fun x => β (Pt.sig, p.1) x *
            wickM β ((zz + (ss + aa + Y)).erase x)).sum = 0 := by
          apply Multiset.sum_eq_zero
          intro w hw
          obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.mp hw
          obtain ⟨b, _, rfl⟩ := Multiset.mem_map.mp hx
          rw [h.symm, h.ps, zero_mul]
        rw [z1, z2, z3, zero_add, zero_add, zero_add, map_multiset_sum, Multiset.map_map]
        apply congrArg Multiset.sum
        apply Multiset.map_congr rfl
        intro y hy
        simp only [Function.comp]
        rw [Multiset.erase_add_right_pos _ (Multiset.mem_add.mpr (Or.inr hy)),
          Multiset.erase_add_right_pos _ hy,
          h.farconst (Pt.sig, p.1) y (Or.inr rfl) (Or.inl (hY y hy)), coeff_C_mul,
          constantCoeff_C]
    refine Fact.congr expand (Fact.add ?_ ?_)
    · apply Fact.multiset_sum
      intro b hb
      apply Fact.smul
      have hA' : ∀ c ∈ A.erase b, 0 < c := fun c hc => hA c (Multiset.mem_of_mem_erase hc)
      exact ih hZ' S (A.erase b) hA' m
    · apply Fact.sum
      intro p hp
      have hpm : p.1 + p.2 = m := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
      by_cases hap : a ≤ p.1
      · simp only [if_pos hap]
        apply Fact.smul
        have hp2 : p.2 = m - p.1 := by omega
        have := ih hZ' (p.1 ::ₘ S) A hA p.2
        rw [hp2] at this
        rw [hp2]
        exact Fact.shift (by omega) (by omega) this
      · simp only [if_neg hap, zero_mul]
        exact Fact.zero

end OPE

end OM.NNN30.Crossing
