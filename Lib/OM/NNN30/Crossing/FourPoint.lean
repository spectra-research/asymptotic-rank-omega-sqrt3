import Lib.OM.NNN30.Crossing.Kernel

namespace OM.NNN30.Crossing

open PowerSeries

/-- The labels of the four states `Z` (at `z`), `A` (at `0`), `Q` (at `1`), `I` (at `∞`). -/
def labels4 (Z A Q I : Multiset ℕ) : Multiset (Pt × ℕ) :=
  Z.map (fun a => (Pt.z, a)) + A.map (fun b => (Pt.p, b)) + Q.map (fun c => (Pt.q, c)) +
    I.map (fun d => (Pt.inf, d))

/-- The polynomial `P(z) = z^M (z-1)^M F(z)` of the four states. -/
noncomputable def P4 (Z A Q I : Multiset ℕ) : Polynomial ℂ := wickM fullK (labels4 Z A Q I)

theorem prod_map_pow_eq {M : Type*} [CommMonoid M] (y : M) (s : Multiset ℕ) :
    (s.map (fun a => y ^ a)).prod = y ^ s.sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons b s ih => rw [Multiset.map_cons, Multiset.prod_cons, ih, Multiset.sum_cons, pow_add]

/-- Positive modes. -/
def Pos (s : Multiset ℕ) : Prop := ∀ a ∈ s, 0 < a

theorem labels4_isFour {Z A Q I : Multiset ℕ} (hZ : Pos Z) (hA : Pos A) (hQ : Pos Q) (hI : Pos I) :
    ∀ u ∈ labels4 Z A Q I, IsFour u := by
  intro u hu
  simp only [labels4, Multiset.mem_add, Multiset.mem_map] at hu
  rcases hu with ((⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩) | ⟨a, ha, rfl⟩) | ⟨a, ha, rfl⟩
  · exact ⟨by simp, hZ a ha⟩
  · exact ⟨by simp, hA a ha⟩
  · exact ⟨by simp, hQ a ha⟩
  · exact ⟨by simp, hI a ha⟩

theorem labels4_sum_snd (Z A Q I : Multiset ℕ) :
    ((labels4 Z A Q I).map Prod.snd).sum = Z.sum + A.sum + Q.sum + I.sum := by
  simp [labels4, Multiset.map_add, Multiset.sum_add, Multiset.map_map, Function.comp]

theorem P4_natDegree (Z A Q I : Multiset ℕ) :
    (P4 Z A Q I).natDegree ≤ Z.sum + A.sum + Q.sum + I.sum := by
  rw [← labels4_sum_snd]
  exact wickM_natDegree_le fullK_symm Prod.snd fullK_natDegree _

/-- The leading coefficient: the `z`–`∞` pairing times the `0`–`1` pairing. -/
theorem P4_top {Z A Q I : Multiset ℕ} (hZ : Pos Z) (hA : Pos A) (hQ : Pos Q) (hI : Pos I) :
    (P4 Z A Q I).coeff (Z.sum + A.sum + Q.sum + I.sum) =
      wickM topK (Z.map (fun a => (Pt.z, a)) + I.map (fun d => (Pt.inf, d))) *
        wickM topK (A.map (fun b => (Pt.p, b)) + Q.map (fun c => (Pt.q, c))) := by
  classical
  have h4 := labels4_isFour hZ hA hQ hI
  rw [← labels4_sum_snd, P4, wickM_coeff_top fullK_symm Prod.snd fullK_natDegree]
  have hsym : ∀ u v : Pt × ℕ, (fullK u v).coeff (u.2 + v.2) = (fullK v u).coeff (v.2 + u.2) := by
    intro u v; rw [fullK_symm, add_comm]
  rw [wickM_congr hsym topK_symm _ (fun u hu v hv => fullK_top u v (h4 u hu).2 (h4 v hv).2)]
  have e : labels4 Z A Q I = (Z.map (fun a => (Pt.z, a)) + I.map (fun d => (Pt.inf, d))) +
      (A.map (fun b => (Pt.p, b)) + Q.map (fun c => (Pt.q, c))) := by
    simp only [labels4]; abel
  rw [e, wickM_add_of_orth topK_symm]
  intro u hu v hv
  simp only [Multiset.mem_add, Multiset.mem_map] at hu hv
  rcases hu with ⟨a, _, rfl⟩ | ⟨a, _, rfl⟩ <;> rcases hv with ⟨b, _, rfl⟩ | ⟨b, _, rfl⟩ <;> rfl

/-- The expansion at `0`: `P = (z - 1)^{H+E} · (z^M F)` as power series in `z`. -/
theorem P4_coe {Z A Q I : Multiset ℕ} (hZ : Pos Z) (hA : Pos A) (hQ : Pos Q) (hI : Pos I) :
    ((P4 Z A Q I : Polynomial ℂ) : ℂ⟦X⟧) =
      (X - 1) ^ (Z.sum + Q.sum) * wickM ker0 (labels4 Z A Q I) := by
  classical
  have h4 := labels4_isFour hZ hA hQ hI
  have hs : ∀ u v : Pt × ℕ, ((fullK u v : Polynomial ℂ) : ℂ⟦X⟧) = ((fullK v u : Polynomial ℂ) : ℂ⟦X⟧) := by
    intro u v; rw [fullK_symm]
  have hs' : ∀ u v : Pt × ℕ, s0 u * s0 v * ker0 u v = s0 v * s0 u * ker0 v u := by
    intro u v; rw [ker0_symm]; ring
  have e1 : ((P4 Z A Q I : Polynomial ℂ) : ℂ⟦X⟧) =
      wickM (fun u v => ((fullK u v : Polynomial ℂ) : ℂ⟦X⟧)) (labels4 Z A Q I) :=
    (wickM_ringHom Polynomial.coeToPowerSeries.ringHom fullK _).symm
  rw [e1, wickM_congr hs hs' _ (fun u hu v hv => fullK_rel0 u v (h4 u hu) (h4 v hv)),
    wickM_scale ker0_symm hs' s0 (fun u v => rfl)]
  congr 1
  simp only [labels4, Multiset.map_add, Multiset.prod_add, Multiset.map_map]
  have hz : Z.map (s0 ∘ fun a => (Pt.z, a)) = Z.map (fun a => (X - 1 : ℂ⟦X⟧) ^ a) :=
    Multiset.map_congr rfl (fun _ _ => rfl)
  have hq : Q.map (s0 ∘ fun c => (Pt.q, c)) = Q.map (fun c => (X - 1 : ℂ⟦X⟧) ^ c) :=
    Multiset.map_congr rfl (fun _ _ => rfl)
  have hp : (A.map (s0 ∘ fun b => (Pt.p, b))).prod = 1 :=
    Multiset.prod_eq_one (fun x hx => by obtain ⟨b, _, rfl⟩ := Multiset.mem_map.mp hx; rfl)
  have hi : (I.map (s0 ∘ fun d => (Pt.inf, d))).prod = 1 :=
    Multiset.prod_eq_one (fun x hx => by obtain ⟨b, _, rfl⟩ := Multiset.mem_map.mp hx; rfl)
  rw [hz, hq, hp, hi, prod_map_pow_eq, prod_map_pow_eq, pow_add]
  ring

/-- The expansion at `1`: `P(1 + w) = (1 + w)^{H+E} · (w^M F(1 + w))`, the points `0` and `1`
exchanging their roles. -/
theorem P4_shift1 {Z A Q I : Multiset ℕ} (hZ : Pos Z) (hA : Pos A) (hQ : Pos Q) (hI : Pos I) :
    shift1 (P4 Z A Q I) = (1 + X) ^ (Z.sum + A.sum) * wickM ker1 (labels4 Z Q A I) := by
  classical
  have h4 := labels4_isFour hZ hA hQ hI
  let φ : Polynomial ℂ →+* ℂ⟦X⟧ :=
    Polynomial.coeToPowerSeries.ringHom.comp (Polynomial.compRingHom (Polynomial.X + 1))
  have hφ : ∀ P : Polynomial ℂ, shift1 P = φ P := fun P => rfl
  have hs : ∀ u v : Pt × ℕ, φ (fullK u v) = φ (fullK v u) := by intro u v; rw [fullK_symm]
  have hs' : ∀ u v : Pt × ℕ, s1 u * s1 v * ker1 (sw u) (sw v) = s1 v * s1 u * ker1 (sw v) (sw u) := by
    intro u v; rw [ker1_symm]; ring
  have hsw : ∀ u v : Pt × ℕ, ker1 (sw u) (sw v) = ker1 (sw v) (sw u) := fun u v => ker1_symm _ _
  rw [hφ, P4, ← wickM_ringHom φ fullK]
  rw [wickM_congr hs hs' _ (fun u hu v hv => by
      rw [← hφ]; exact fullK_rel1 u v (h4 u hu) (h4 v hv)),
    wickM_scale hsw hs' s1 (fun u v => rfl), ← wickM_map ker1_symm sw]
  congr 1
  · simp only [labels4, Multiset.map_add, Multiset.prod_add, Multiset.map_map]
    have hz : Z.map (s1 ∘ fun a => (Pt.z, a)) = Z.map (fun a => (1 + X : ℂ⟦X⟧) ^ a) :=
      Multiset.map_congr rfl (fun _ _ => rfl)
    have hp : A.map (s1 ∘ fun b => (Pt.p, b)) = A.map (fun b => (1 + X : ℂ⟦X⟧) ^ b) :=
      Multiset.map_congr rfl (fun _ _ => rfl)
    have hq : (Q.map (s1 ∘ fun c => (Pt.q, c))).prod = 1 :=
      Multiset.prod_eq_one (fun x hx => by obtain ⟨b, _, rfl⟩ := Multiset.mem_map.mp hx; rfl)
    have hi : (I.map (s1 ∘ fun d => (Pt.inf, d))).prod = 1 :=
      Multiset.prod_eq_one (fun x hx => by obtain ⟨b, _, rfl⟩ := Multiset.mem_map.mp hx; rfl)
    rw [hz, hp, hq, hi, prod_map_pow_eq, prod_map_pow_eq, pow_add]
    ring
  · simp only [labels4, Multiset.map_add, Multiset.map_map]
    have hz : Z.map (sw ∘ fun a => (Pt.z, a)) = Z.map (fun a => (Pt.z, a)) :=
      Multiset.map_congr rfl (fun _ _ => rfl)
    have hp : A.map (sw ∘ fun b => (Pt.p, b)) = A.map (fun b => (Pt.q, b)) :=
      Multiset.map_congr rfl (fun _ _ => rfl)
    have hq : Q.map (sw ∘ fun c => (Pt.q, c)) = Q.map (fun c => (Pt.p, c)) :=
      Multiset.map_congr rfl (fun _ _ => rfl)
    have hi : I.map (sw ∘ fun d => (Pt.inf, d)) = I.map (fun d => (Pt.inf, d)) :=
      Multiset.map_congr rfl (fun _ _ => rfl)
    rw [hz, hp, hq, hi]
    abel

/-- Operator product expansion at `0`: the coefficient of `w^m` factors through the partitions of
`m`, across the cut `(z, 0) | (1, ∞)`. -/
theorem row_fact {Z A : Multiset ℕ} (hZ : Pos Z) (hA : Pos A) (m : ℕ) :
    ∃ c : m.Partition → ℂ, ∀ Q I : Multiset ℕ, Pos Q → Pos I →
      coeff m (wickM ker0 (labels4 Z A Q I)) =
        ∑ τ, c τ * farVal ker0 τ.parts (Q.map (fun c => (Pt.q, c)) + I.map (fun d => (Pt.inf, d))) := by
  obtain ⟨c, hc⟩ := ope_fact opeHyp_ker0 Z hZ 0 A hA m
  refine ⟨c, fun Q I hQ hI => ?_⟩
  have hY : ∀ y ∈ Q.map (fun c => (Pt.q, c)) + I.map (fun d => (Pt.inf, d)), IsFar y := by
    intro y hy
    rcases Multiset.mem_add.mp hy with hy | hy <;> obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.mp hy
    · exact ⟨Or.inl rfl, hQ a ha⟩
    · exact ⟨Or.inr rfl, hI a ha⟩
  have := hc _ hY
  simp only [Multiset.map_zero, zero_add] at this
  rw [← this]
  congr 2
  simp only [labels4]
  abel

/-- Operator product expansion at `1`, across the cut `(z, 1) | (0, ∞)`. -/
theorem col_fact {Z Q : Multiset ℕ} (hZ : Pos Z) (hQ : Pos Q) (m : ℕ) :
    ∃ c : m.Partition → ℂ, ∀ A I : Multiset ℕ, Pos A → Pos I →
      coeff m (wickM ker1 (labels4 Z Q A I)) =
        ∑ τ, c τ * farVal ker1 τ.parts (A.map (fun b => (Pt.q, b)) + I.map (fun d => (Pt.inf, d))) := by
  obtain ⟨c, hc⟩ := ope_fact opeHyp_ker1 Z hZ 0 Q hQ m
  refine ⟨c, fun A I hA hI => ?_⟩
  have hY : ∀ y ∈ A.map (fun b => (Pt.q, b)) + I.map (fun d => (Pt.inf, d)), IsFar y := by
    intro y hy
    rcases Multiset.mem_add.mp hy with hy | hy <;> obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.mp hy
    · exact ⟨Or.inl rfl, hA a ha⟩
    · exact ⟨Or.inr rfl, hI a ha⟩
  have := hc _ hY
  simp only [Multiset.map_zero, zero_add] at this
  rw [← this]
  congr 2
  simp only [labels4]
  abel

end OM.NNN30.Crossing
