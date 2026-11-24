import Lib.OM.NNN20.CatalyticSpec

/-! # Soundness of the catalytic checker, part 2: node and vertex gates

`ccheckNode_spec`: a passing `ccheckNode` gives, at every point of the cell, the gates
`CNodeGates` with the absent-class rule for the node's real
semantics: triangle exponents in `(0, 1)`, a positive retained rate below the capacity, the
domination `λ ≤ λ̂`, the retained queries in the retained parent's cone, and at every hull vertex
the host balances, positive full rates below capacity and below the absent-class bound, and the
full-family queries in the parents' cones. -/

namespace OM.NNN20

open Finset

/-- the three parties -/
lemma party_cases (n : CNode) (i : Fin 3) : i = n.p ∨ i = cj n ∨ i = ck n := by
  rcases n with ⟨p, _, _, _⟩
  simp only [cj, ck]
  fin_cases p <;> fin_cases i <;> simp [oth1, oth2]

lemma cj_ne_p (n : CNode) : cj n ≠ n.p := by
  rcases n with ⟨p, _, _, _⟩; simp only [cj]; fin_cases p <;> decide
lemma ck_ne_p (n : CNode) : ck n ≠ n.p := by
  rcases n with ⟨p, _, _, _⟩; simp only [ck]; fin_cases p <;> decide
lemma cj_ne_ck (n : CNode) : cj n ≠ ck n := by
  rcases n with ⟨p, _, _, _⟩; simp only [cj, ck]; fin_cases p <;> decide

section
variable {n : CNode} {θ : Fin 3 → TM} {B : ℚ} {P : Fin 3 → Fin 3 → TM}
  {θf : Fin 3 → ℝ → ℝ → ℝ} {Pf : Fin 3 → Fin 3 → ℝ → ℝ → ℝ}

structure CBondSpec (n : CNode) (θf : Fin 3 → ℝ → ℝ → ℝ) (Pf : Fin 3 → Fin 3 → ℝ → ℝ → ℝ)
    (i : Fin 3) (b : CBond) : Prop where
  beta : b.beta.Encl (fun x y => cBeta n (atθ θf x y) (atP Pf x y) i)
  rb : b.rb.Encl (fun x y => 1 / cBeta n (atθ θf x y) (atP Pf x y) i)
  L : b.L.Encl (fun x y => cL n (atθ θf x y) (atP Pf x y) i)

theorem cbondTM_spec (hθ : ∀ i, (θ i).Encl (θf i)) (hP : ∀ i j, (P i j).Encl (Pf i j))
    {i : Fin 3} {b : CBond} (h : cbondTM n θ P i = some b) : CBondSpec n θf Pf i b := by
  have heta : ((P i (oth1 i)).add (P i (oth2 i))).Encl (fun x y => gEta (atP Pf x y) i) :=
    TM.add_encl (hP _ _) (hP _ _)
  unfold cbondTM at h
  dsimp only at h
  split at h
  · cases h
  rename_i rb hrb
  split at h
  · cases h
  rename_i E hE
  split at h
  · cases h
  rename_i L hL
  cases h
  have hbeta := TM.mulq_encl (1 / 2) (TM.add_encl (hθ i) heta)
  have hrb' := TM.recip_encl hbeta hrb
  have hz := TM.mul_encl (TM.sub_encl (hθ i) heta) hrb'
  have hE' := TM.exp2_encl (TM.smul_encl ((n.act i).d : ℤ) hz) hE
  have hA := TM.mulq_encl (1 / ((n.act i).q : ℚ)) (TM.add_encl TM.const_one_encl
    (TM.smul_encl (((n.act i).q - 1 : ℕ) : ℤ) hE'))
  have hL' := (TM.log2_encl hA hL).2
  refine ⟨hbeta.congr fun x y _ _ => ?_, hrb'.congr fun x y _ _ => ?_, hL'.congr fun x y _ _ => ?_⟩
  · simp [cBeta, gBeta, asG, atθ]
  · simp [cBeta, gBeta, asG, atθ]
  · simp [cL, gL, gZ, gBeta, asG, atθ]

lemma tsum3_encl {c : Fin 3 → TM} {cf : Fin 3 → ℝ → ℝ → ℝ} (hc : ∀ u, (c u).Encl (cf u)) :
    (tsum3 c).Encl (fun x y => cf 0 x y + cf 1 x y + cf 2 x y) :=
  TM.add_encl (TM.add_encl (hc 0) (hc 1)) (hc 2)

lemma tmLin_encl {t : Fin 3 → TM} {tf : Fin 3 → ℝ → ℝ → ℝ} (ht : ∀ u, (t u).Encl (tf u))
    (yv : Fin 3 → ℚ) :
    (tmLin t yv).Encl (fun x y => (yv 0 : ℝ) * tf 0 x y + (yv 1 : ℝ) * tf 1 x y + (yv 2 : ℝ) * tf 2 x y) :=
  TM.add_encl (TM.add_encl (TM.mulq_encl _ (ht 0)) (TM.mulq_encl _ (ht 1))) (TM.mulq_encl _ (ht 2))

structure COutSpec (n : CNode) (θf : Fin 3 → ℝ → ℝ → ℝ) (B : ℚ) (Pf : Fin 3 → Fin 3 → ℝ → ℝ → ℝ)
    (o : COut) : Prop where
  bond : ∀ i, CBondSpec n θf Pf i (o.bond i)
  rp : o.rp.Encl (fun x y => cRp n (atθ θf x y) B (atP Pf x y))
  lam : ∀ u, (o.lam u).Encl (fun x y => cLam n (atθ θf x y) B (atP Pf x y) u)

theorem cnodeTM_spec (hθ : ∀ i, (θ i).Encl (θf i)) (hP : ∀ i j, (P i j).Encl (Pf i j))
    {o : COut} (h : cnodeTM n θ B P = some o) : COutSpec n θf B Pf o := by
  unfold cnodeTM at h
  split at h
  · rename_i bp bj bk hp hj hk
    have sp := cbondTM_spec hθ hP hp
    have sj := cbondTM_spec hθ hP hj
    have sk := cbondTM_spec hθ hP hk
    have hb : ∀ i, CBondSpec n θf Pf i
        (if i = n.p then bp else if i = cj n then bj else bk) := by
      intro i
      rcases party_cases n i with rfl | rfl | rfl
      · simpa using sp
      · simpa [cj_ne_p] using sj
      · simpa [ck_ne_p, Ne.symm (cj_ne_ck n)] using sk
    dsimp only at h
    split at h
    · cases h
    rename_i rden hrden
    cases h
    have hwj := TM.mul_encl (hθ (cj n)) sj.rb
    have hwk := TM.mul_encl (hθ (ck n)) sk.rb
    have hden := TM.add_encl (TM.add_encl TM.const_one_encl hwj) hwk
    have hrd := TM.recip_encl hden hrden
    have hrp := TM.sub_encl (TM.mul_encl (TM.sub_encl (TM.ofq_encl B) (tsum3_encl (hP n.p))) sp.rb)
      (TM.mulq_encl (1 / ((n.act n.p).q : ℚ)) sp.L)
    refine ⟨hb, hrp.congr fun x y _ _ => ?_, fun u => ?_⟩
    · simp [cRp, csum, atP]
    · have hl : ∀ u, (lamEntry n θ B P (fun i => if i = n.p then bp else if i = cj n then bj else bk)
          (((TM.ofq B).sub (tsum3 (P n.p))).mul bp.rb |>.sub (TM.mulq (1 / ((n.act n.p).q : ℚ)) bp.L))
          ((θ (cj n)).mul bj.rb) ((θ (ck n)).mul bk.rb)
          (((TM.const ONE).add ((θ (cj n)).mul bj.rb)).add ((θ (ck n)).mul bk.rb)) rden u).Encl
          (fun x y => cLam n (atθ θf x y) B (atP Pf x y) u) := by
        intro u
        unfold lamEntry
        dsimp only
        have bj' := hb (cj n)
        have bk' := hb (ck n)
        refine (TM.mul_encl (TM.add_encl (TM.add_encl (TM.add_encl (TM.add_encl (TM.sub_encl
          (TM.sub_encl (TM.add_encl (TM.add_encl (TM.mulq_encl _ (hθ n.p)) (TM.mulq_encl _ (hθ (cj n))))
            (TM.mulq_encl _ (hθ (ck n)))) (TM.mulq_encl _ (TM.mul_encl (hθ n.p) hrp)))
          (TM.mulq_encl _ hden))
          (TM.mul_encl hwj (TM.add_encl (hP _ _) (TM.mulq_encl _ (tsum3_encl (hP (cj n)))))))
          (TM.mul_encl hwk (TM.add_encl (hP _ _) (TM.mulq_encl _ (tsum3_encl (hP (ck n)))))))
          (TM.mulq_encl _ (TM.mul_encl (hθ (cj n)) bj'.L)))
          (TM.mulq_encl _ (TM.mul_encl (hθ (ck n)) bk'.L))) hrd).congr fun x y _ _ => ?_
        simp only [cLam, cRp, cDen, cW, csum, gW, cBeta, cL, atθ, atP]
      fin_cases u
      · exact hl 0
      · exact hl 1
      · exact hl 2
  · cases h

end

end OM.NNN20

namespace OM.NNN20

open Finset

/-! ## Real statements at one point -/

section Real
variable (n : CNode) (θ : Fin 3 → ℝ) (B : ℚ) (c : Fin 3 → Fin 3 → ℝ)

/-- the density of the full family `f` at the format `yv` -/
def cNy (f : Fin 3) (yv : Fin 3 → ℚ) : ℚ := if f = cj n then qdot (cNj n) yv else qdot (cNk n) yv

/-- the lower end of the extraction parameter of the full family `f` (absent-class rule) -/
noncomputable def cXiLow (f : Fin 3) (yv : Fin 3 → ℚ) : ℝ :=
  ((-1 / 2 : ℚ) : ℝ) * cRho n θ B c f yv + (((n.act f).d * T0 * cNy n f yv : ℚ) : ℝ)

/-- the query direction of the full family `f` (`oth` the other full party) -/
def qdir (n : CNode) (oth : Fin 3) : Fin 3 → ℚ := fun u => if u = n.p ∨ u = oth then 1 else 0

/-- the gates of one full family at one format -/
def FamGates (Vp : Option (List (ℤ × ℤ))) (f oth : Fin 3) (yv : Fin 3 → ℚ) : Prop :=
  0 < cRho n θ B c f yv ∧ cRho n θ B c f yv < Real.logb 2 (n.act f).q * (cNy n f yv : ℝ) ∧
  ∀ Vf, Vp = some Vf → cRho n θ B c f yv < kappaR (n.act f).q T0 * (cNy n f yv : ℝ) ∧
    ∀ ξ : ℝ, cXiLow n θ B c f yv ≤ ξ → ξ ≤ (((n.act f).d * cNy n f yv : ℚ) : ℝ) →
      InCone Vf (fun u => ((yv u + qdot (cts n) yv : ℚ) : ℝ) - ξ * (qdir n oth u : ℝ))

/-- the gates at one hull vertex -/
def VertGates (Vp : Fin 3 → Option (List (ℤ × ℤ))) (pt : ℤ × ℤ) : Prop :=
  balanceOK ((vecV pt) (ck n)) (qdot (cth n) (vecV pt)) (n.act (cj n)) = true ∧
  balanceOK ((vecV pt) (cj n)) (qdot (cth n) (vecV pt)) (n.act (ck n)) = true ∧
  FamGates n θ B c (Vp (cj n)) (cj n) (ck n) (vecV pt) ∧
  FamGates n θ B c (Vp (ck n)) (ck n) (cj n) (vecV pt)

/-- all gates of a catalytic node at one point of the cell -/
def CNodeGates (lhat : Fin 3 → ℝ) (V : List (ℤ × ℤ)) (Vp : Fin 3 → Option (List (ℤ × ℤ))) : Prop :=
  (∀ i, n.act i = F7 ∨ n.act i = F11) ∧
  (∀ i, 0 < cBeta n θ c i ∧ cBeta n θ c i < 1) ∧
  0 < cRp n θ B c ∧ cRp n θ B c < Real.logb 2 (n.act n.p).q / (n.act n.p).q ∧
  (∀ u, cLam n θ B c u ≤ lhat u) ∧
  (∀ Vpp, Vp n.p = some Vpp → cRp n θ B c < kappaR (n.act n.p).q T0 / (n.act n.p).q ∧
    ∀ ξ : ℝ, ((-1 / 2 : ℚ) : ℝ) * cRp n θ B c + (((n.act n.p).d * T0 / (n.act n.p).q : ℚ) : ℝ) ≤ ξ →
      ξ ≤ (((n.act n.p).d / (n.act n.p).q : ℚ) : ℝ) →
      InCone Vpp (fun u => 1 - ξ * ((if u = cj n ∨ u = ck n then 1 else 0 : ℚ) : ℝ))) ∧
  (∀ pt ∈ V, 0 < pt.1 ∧ 0 < pt.2 ∧ 0 < GRID - pt.1 - pt.2) ∧
  (∀ pt ∈ V, VertGates n θ B c Vp pt)

end Real

end OM.NNN20

namespace OM.NNN20

open Finset

section
variable {n : CNode} {θ : Fin 3 → TM} {B : ℚ} {P : Fin 3 → Fin 3 → TM}
  {θf : Fin 3 → ℝ → ℝ → ℝ} {Pf : Fin 3 → Fin 3 → ℝ → ℝ → ℝ}

lemma qdot_nonneg {a y : Fin 3 → ℚ} (ha : ∀ u, 0 ≤ a u) (hy : ∀ u, 0 ≤ y u) : 0 ≤ qdot a y := by
  unfold qdot
  have := mul_nonneg (ha 0) (hy 0); have := mul_nonneg (ha 1) (hy 1); have := mul_nonneg (ha 2) (hy 2)
  linarith

lemma cNy_nonneg (hτ : 0 < n.tau) {yv : Fin 3 → ℚ} (hy : ∀ u, 0 ≤ yv u) (f : Fin 3) :
    0 ≤ cNy n f yv := by
  have hth : ∀ u, 0 ≤ cth n u := fun u => by unfold cth; split_ifs <;> linarith
  unfold cNy
  split_ifs
  · refine qdot_nonneg (fun u => ?_) hy
    unfold cNj; apply div_nonneg _ (Nat.cast_nonneg _)
    have := hth u; split_ifs <;> linarith
  · refine qdot_nonneg (fun u => ?_) hy
    unfold cNk; apply div_nonneg _ (Nat.cast_nonneg _)
    have := hth u; split_ifs <;> linarith

theorem famOK_spec (hθ : ∀ i, (θ i).Encl (θf i)) (hP : ∀ i j, (P i j).Encl (Pf i j))
    {o : COut} (ho : COutSpec n θf B Pf o) (hτ : 0 < n.tau) (hacts : ∀ i, n.act i = F7 ∨ n.act i = F11)
    {Vp : Option (List (ℤ × ℤ))} {yv : Fin 3 → ℚ} (hy : ∀ u, 0 ≤ yv u) {f oth : Fin 3}
    {N : Fin 3 → ℚ} (hN : qdot N yv = cNy n f yv) {w w' : List ℕ}
    (h : famOK n B P o Vp yv f oth N w = some w') {x y : ℝ} (hx : |x| ≤ 1) (hyy : |y| ≤ 1) :
    FamGates n (atθ θf x y) B (atP Pf x y) Vp f oth yv := by
  have hq : (n.act f).q = 7 ∨ (n.act f).q = 11 := by
    rcases hacts f with h | h <;> simp [h, F7, F11]
  have hNy := cNy_nonneg hτ hy f
  have hNyR : (0 : ℝ) ≤ (cNy n f yv : ℝ) := by exact_mod_cast hNy
  -- the rate
  have hrho : ((((tmLin o.lam yv).add (TM.ofq (qdot (cts n) yv * B))).sub
      ((tmLin (P f) yv).add (TM.mulq (qdot (cts n) yv) (tsum3 (P f))))).mul (o.bond f).rb |>.sub
      (TM.mulq (qdot N yv) (o.bond f).L)).Encl (fun x y => cRho n (atθ θf x y) B (atP Pf x y) f yv) := by
    refine (TM.sub_encl (TM.mul_encl (TM.sub_encl (TM.add_encl (tmLin_encl ho.lam yv) (TM.ofq_encl _))
      (TM.add_encl (tmLin_encl (hP f) yv) (TM.mulq_encl _ (tsum3_encl (hP f))))) (ho.bond f).rb)
      (TM.mulq_encl _ (ho.bond f).L)).congr fun x y _ _ => ?_
    simp only [cRho, hN, cNy, csum, atP]
  have key : ∀ (b : Bool) {α : Type} (r : Option α) (w' : α),
      (if (!b) = true then none else r) = some w' → b = true ∧ r = some w' := by
    intro b α r w' hr; cases b <;> simp at hr ⊢; exact hr
  have constI_mul : ∀ (lo hi : ℚ) (v : ℝ), (lo : ℝ) ≤ v → v ≤ hi →
      (TM.constI (qdot N yv * lo) (qdot N yv * hi)).Encl (fun _ _ => (cNy n f yv : ℝ) * v) := by
    intro lo hi v h1 h2
    refine TM.constI_encl _ _ fun _ _ _ _ => ⟨?_, ?_⟩
    · push_cast; rw [hN]; exact mul_le_mul_of_nonneg_left h1 hNyR
    · push_cast; rw [hN]; exact mul_le_mul_of_nonneg_left h2 hNyR
  unfold famOK at h
  dsimp only at h
  obtain ⟨g1, h2⟩ := key _ _ _ h
  simp only [Bool.and_eq_true] at g1
  obtain ⟨g1a, g1b⟩ := g1
  have hl2 := log2q_spec hq
  have r1 := (gateOK_spec g1a hrho hx hyy).2 rfl
  have r2 := (gateOK_spec g1b (TM.sub_encl (constI_mul _ _ _ hl2.1 hl2.2) hrho) hx hyy).2 rfl
  refine ⟨r1, by linarith [mul_comm (cNy n f yv : ℝ) (Real.logb 2 ((n.act f).q : ℝ))], ?_⟩
  intro Vf hVf
  subst hVf
  obtain ⟨g2, h3⟩ := key _ _ _ h2
  have hk := kapq_spec hq
  have r3 := (gateOK_spec g2 (TM.sub_encl (constI_mul _ _ _ hk.1 hk.2) hrho) hx hyy).2 rfl
  refine ⟨by linarith [mul_comm (cNy n f yv : ℝ) (kappaR (n.act f).q (T0 : ℝ))], ?_⟩
  intro ξ hξ1 hξ2
  have hq3 := queryOK_spec h3
  -- the two parameter Taylor models and their ranges
  set rhoT := ((((tmLin o.lam yv).add (TM.ofq (qdot (cts n) yv * B))).sub
      ((tmLin (P f) yv).add (TM.mulq (qdot (cts n) yv) (tsum3 (P f))))).mul (o.bond f).rb).sub
      (TM.mulq (qdot N yv) (o.bond f).L)
  have hlow : ((TM.mulq (-1 / 2) rhoT).add (TM.ofq ((n.act f).d * T0 * qdot N yv))).Encl
      (fun x y => cXiLow n (atθ θf x y) B (atP Pf x y) f yv) :=
    (TM.add_encl (TM.mulq_encl _ hrho) (TM.ofq_encl _)).congr fun x y _ _ => by
      simp only [cXiLow, hN]
  have hhigh := TM.ofq_encl (qdot N yv * (n.act f).d)
  have rl := (rng_spec hlow hx hyy).1
  have rh := (rng_spec hhigh hx hyy).2
  have hO := ONE_pos
  set lowT := (TM.mulq (-1 / 2) rhoT).add (TM.ofq ((n.act f).d * T0 * qdot N yv))
  set highT := TM.ofq (qdot N yv * (n.act f).d)
  obtain ⟨_, cl⟩ := hq3 lowT (by simp) ((lowT.rng.1 : ℚ) / ONE) (by simp)
  obtain ⟨_, ch⟩ := hq3 highT (by simp) ((highT.rng.2 : ℚ) / ONE) (by simp)
  refine segment_inCone (a := fun u => ((yv u + qdot (cts n) yv : ℚ) : ℝ))
    (s := fun u => (qdir n oth u : ℝ)) (lo := (((lowT.rng.1 : ℚ) / ONE : ℚ) : ℝ))
    (hi := (((highT.rng.2 : ℚ) / ONE : ℚ) : ℝ))
    (cl.congr fun u => by simp only [qdir]; push_cast; ring)
    (ch.congr fun u => by simp only [qdir]; push_cast; ring) ?_ ?_
  · push_cast
    rw [div_le_iff₀ hO]
    have : (ONE : ℝ) * cXiLow n (atθ θf x y) B (atP Pf x y) f yv ≤ ONE * ξ :=
      mul_le_mul_of_nonneg_left hξ1 hO.le
    linarith
  · push_cast
    rw [le_div_iff₀ hO]
    have e : ((qdot N yv * (n.act f).d : ℚ) : ℝ) = (((n.act f).d * cNy n f yv : ℚ) : ℝ) := by
      rw [hN, mul_comm]
    rw [e] at rh
    have : (ONE : ℝ) * ξ ≤ ONE * (((n.act f).d * cNy n f yv : ℚ) : ℝ) :=
      mul_le_mul_of_nonneg_left hξ2 hO.le
    linarith

lemma vecV_nonneg {pt : ℤ × ℤ} (hpt : 0 < pt.1 ∧ 0 < pt.2 ∧ 0 < GRID - pt.1 - pt.2) (u : Fin 3) :
    0 ≤ vecV pt u := by
  have hG : (0 : ℚ) < GRID := by norm_num [GRID]
  obtain ⟨h1, h2, h3⟩ := hpt
  fin_cases u <;> simp only [vecV] <;> simp <;> apply div_nonneg _ hG.le
  · exact_mod_cast h3.le
  · exact_mod_cast h1.le
  · exact_mod_cast h2.le

theorem vertexOK_spec (hθ : ∀ i, (θ i).Encl (θf i)) (hP : ∀ i j, (P i j).Encl (Pf i j))
    {o : COut} (ho : COutSpec n θf B Pf o) (hτ : 0 < n.tau) (hacts : ∀ i, n.act i = F7 ∨ n.act i = F11)
    {Vp : Fin 3 → Option (List (ℤ × ℤ))} {pt : ℤ × ℤ}
    (hpt : 0 < pt.1 ∧ 0 < pt.2 ∧ 0 < GRID - pt.1 - pt.2) {w w' : List ℕ}
    (h : vertexOK n B P o Vp pt w = some w') {x y : ℝ} (hx : |x| ≤ 1) (hyy : |y| ≤ 1) :
    VertGates n (atθ θf x y) B (atP Pf x y) Vp pt := by
  have key : ∀ (b : Bool) {α : Type} (r : Option α) (w' : α),
      (if (!b) = true then none else r) = some w' → b = true ∧ r = some w' := by
    intro b α r w' hr; cases b <;> simp at hr ⊢; exact hr
  have hy := vecV_nonneg hpt
  unfold vertexOK at h
  dsimp only at h
  obtain ⟨g, h2⟩ := key _ _ _ h
  simp only [Bool.and_eq_true] at g
  split at h2
  · cases h2
  rename_i w1 h1
  refine ⟨g.1, g.2, famOK_spec hθ hP ho hτ hacts hy (by simp [cNy]) h1 hx hyy,
    famOK_spec hθ hP ho hτ hacts hy (by simp [cNy, Ne.symm (cj_ne_ck n)]) h2 hx hyy⟩

theorem vertsOK_spec {o : COut} {Vp : Fin 3 → Option (List (ℤ × ℤ))} :
    ∀ {V : List (ℤ × ℤ)} {w w' : List ℕ}, vertsOK n B P o Vp V w = some w' →
      ∀ pt ∈ V, ∃ w1 w2, vertexOK n B P o Vp pt w1 = some w2
  | [], w, w', _ => by simp
  | pt :: V, w, w', h => by
    simp only [vertsOK] at h
    split at h
    · cases h
    rename_i w1 h1
    intro pt' hpt'
    simp only [List.mem_cons] at hpt'
    rcases hpt' with rfl | hpt'
    · exact ⟨w, w1, h1⟩
    · exact vertsOK_spec h pt' hpt'

/-- **Soundness of the catalytic-node checker.** -/
theorem ccheckNode_spec (hθ : ∀ i, (θ i).Encl (θf i)) (hP : ∀ i j, (P i j).Encl (Pf i j))
    {Vp : Fin 3 → Option (List (ℤ × ℤ))} {Lhat : Fin 3 → List ℤ} {V : List (ℤ × ℤ)} {wit : List ℕ}
    (h : ccheckNode n θ B P Vp Lhat V wit = true) {x y : ℝ} (hx : |x| ≤ 1) (hyy : |y| ≤ 1) :
    CNodeGates n (atθ θf x y) B (atP Pf x y) (fun u => peval (Lhat u) x y / ONE) V Vp := by
  have key : ∀ (b : Bool) {α : Type} (r : Option α) (w' : α),
      (if (!b) = true then none else r) = some w' → b = true ∧ r = some w' := by
    intro b α r w' hr; cases b <;> simp at hr ⊢; exact hr
  unfold ccheckNode at h
  split at h
  · cases h
  rename_i o hcn
  have ho := cnodeTM_spec hθ hP hcn
  dsimp only at h
  have keyB : ∀ (b r : Bool), (if (!b) = true then false else r) = true → b = true ∧ r = true := by
    intro b r hr; cases b <;> simp at hr ⊢; exact hr
  obtain ⟨hg, h⟩ := keyB _ _ h
  simp only [Bool.and_eq_true] at hg
  obtain ⟨⟨⟨⟨⟨⟨hτ, hact⟩, hbeta⟩, hrp⟩, hcap⟩, hdom⟩, hpos⟩ := hg
  have hτ' : 0 < n.tau := by simpa using hτ
  have hacts : ∀ i, n.act i = F7 ∨ n.act i = F11 := by
    intro i
    have := all_finRange hact i
    simp only [Bool.or_eq_true, decide_eq_true_eq] at this
    exact this
  have hq : (n.act n.p).q = 7 ∨ (n.act n.p).q = 11 := by
    rcases hacts n.p with h | h <;> simp [h, F7, F11]
  have hqpos : (0 : ℝ) < (n.act n.p).q := by rcases hq with h | h <;> rw [h] <;> norm_num
  have hverts : ∀ pt ∈ V, 0 < pt.1 ∧ 0 < pt.2 ∧ 0 < GRID - pt.1 - pt.2 := by
    intro pt hpt
    unfold vertsPos at hpos
    simp only [List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hpos
    exact ⟨(hpos pt hpt).1.1, (hpos pt hpt).1.2, (hpos pt hpt).2⟩
  -- the retained capacity constant
  have hl2 := log2q_spec hq
  have capE : (TM.constI ((log2q (n.act n.p).q).1 / (n.act n.p).q) ((log2q (n.act n.p).q).2 / (n.act n.p).q)).Encl
      (fun _ _ => Real.logb 2 (n.act n.p).q / (n.act n.p).q) :=
    TM.constI_encl _ _ fun _ _ _ _ => ⟨by push_cast; exact div_le_div_of_nonneg_right hl2.1 hqpos.le,
      by push_cast; exact div_le_div_of_nonneg_right hl2.2 hqpos.le⟩
  have r1 := (gateOK_spec hrp ho.rp hx hyy).2 rfl
  have r2 := (gateOK_spec hcap (TM.sub_encl capE ho.rp) hx hyy).2 rfl
  -- the vertex part
  have hvert : ∀ w : List ℕ, (match vertsOK n B P o Vp V w with
      | some [] => true
      | _ => false) = true → ∀ pt ∈ V, VertGates n (atθ θf x y) B (atP Pf x y) Vp pt := by
    intro w hw pt hpt
    split at hw
    · rename_i hvs
      obtain ⟨w1, w2, hv⟩ := vertsOK_spec hvs pt hpt
      exact vertexOK_spec hθ hP ho hτ' hacts (hverts pt hpt) hv hx hyy
    · cases hw
  have hbeta' : ∀ i, 0 < cBeta n (atθ θf x y) (atP Pf x y) i ∧ cBeta n (atθ θf x y) (atP Pf x y) i < 1 := by
    intro i
    have hb := all_finRange hbeta i
    simp only [Bool.and_eq_true] at hb
    have b1 := (gateOK_spec hb.1 (ho.bond i).beta hx hyy).2 rfl
    have b2 := (gateOK_spec hb.2 (TM.sub_encl TM.const_one_encl (ho.bond i).beta) hx hyy).2 rfl
    exact ⟨b1, by linarith⟩
  have hdom' : ∀ u, cLam n (atθ θf x y) B (atP Pf x y) u ≤ peval (Lhat u) x y / ONE := by
    intro u
    have hd := all_finRange hdom u
    have := (gateOK_spec hd (TM.sub_encl (pk_encl (Lhat u)) (ho.lam u)) hx hyy).1
    linarith
  cases hVp : Vp n.p with
  | none =>
    simp only [hVp] at h
    refine ⟨hacts, hbeta', r1, by linarith, hdom', fun Vpp hVpp => (by rw [hVp] at hVpp; cases hVpp),
      hverts, hvert _ h⟩
  | some Vpp =>
    simp only [hVp] at h
    split at h
    · cases h
    rename_i w hw1
    obtain ⟨g2, hq3⟩ := key _ _ _ hw1
    refine ⟨hacts, hbeta', r1, by linarith, hdom', fun Vpp' hVpp' => ?_, hverts, hvert _ h⟩
    have hv : Vpp' = Vpp := by rw [hVp] at hVpp'; exact (Option.some_injective _ hVpp').symm
    subst hv
    have hk := kapq_spec hq
    have kapE : (TM.constI ((kapq (n.act n.p).q).1 / (n.act n.p).q) ((kapq (n.act n.p).q).2 / (n.act n.p).q)).Encl
        (fun _ _ => kappaR (n.act n.p).q T0 / (n.act n.p).q) :=
      TM.constI_encl _ _ fun _ _ _ _ => ⟨by push_cast; exact div_le_div_of_nonneg_right hk.1 hqpos.le,
        by push_cast; exact div_le_div_of_nonneg_right hk.2 hqpos.le⟩
    have r3 := (gateOK_spec g2 (TM.sub_encl kapE ho.rp) hx hyy).2 rfl
    refine ⟨by linarith, fun ξ hξ1 hξ2 => ?_⟩
    have hq3' := queryOK_spec hq3
    set lowT := (TM.mulq (-1 / 2) o.rp).add (TM.ofq ((n.act n.p).d * T0 / (n.act n.p).q))
    set highT := TM.ofq (((n.act n.p).d : ℚ) / (n.act n.p).q)
    have hlow : lowT.Encl (fun x y => ((-1 / 2 : ℚ) : ℝ) * cRp n (atθ θf x y) B (atP Pf x y) +
        (((n.act n.p).d * T0 / (n.act n.p).q : ℚ) : ℝ)) :=
      TM.add_encl (TM.mulq_encl _ ho.rp) (TM.ofq_encl _)
    have rl := (rng_spec hlow hx hyy).1
    have rh := (rng_spec (TM.ofq_encl (((n.act n.p).d : ℚ) / (n.act n.p).q)) hx hyy).2
    obtain ⟨_, cl⟩ := hq3' lowT (by simp) ((lowT.rng.1 : ℚ) / ONE) (by simp)
    obtain ⟨_, ch⟩ := hq3' highT (by simp) ((highT.rng.2 : ℚ) / ONE) (by simp)
    have hO := ONE_pos
    refine segment_inCone (a := fun _ => (1 : ℝ))
      (s := fun u => ((if u = cj n ∨ u = ck n then 1 else 0 : ℚ) : ℝ))
      (lo := (((lowT.rng.1 : ℚ) / ONE : ℚ) : ℝ)) (hi := (((highT.rng.2 : ℚ) / ONE : ℚ) : ℝ))
      (cl.congr fun u => by push_cast; ring) (ch.congr fun u => by push_cast; ring) ?_ ?_
    · push_cast
      rw [div_le_iff₀ hO]
      have : (ONE : ℝ) * (((-1 / 2 : ℚ) : ℝ) * cRp n (atθ θf x y) B (atP Pf x y) +
          (((n.act n.p).d * T0 / (n.act n.p).q : ℚ) : ℝ)) ≤ ONE * ξ :=
        mul_le_mul_of_nonneg_left hξ1 hO.le
      linarith
    · push_cast
      rw [le_div_iff₀ hO]
      have : (ONE : ℝ) * ξ ≤ ONE * ((((n.act n.p).d : ℚ) / (n.act n.p).q : ℚ) : ℝ) :=
        mul_le_mul_of_nonneg_left hξ2 hO.le
      push_cast at this rh
      linarith

end

end OM.NNN20
