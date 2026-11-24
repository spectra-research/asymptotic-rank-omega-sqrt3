import Lib.OM.NNN20.Global

/-! # Soundness of the global-node checker

`gcheck_spec`: if `gcheck n θ P Pk = true` and the Taylor models `θ i`, `P i j` enclose real
functions `θf i`, `Pf i j` on the box, then at every point of the box all gates `GGates` of the
node hold for the profile `θf · x y` and the parents `Pf · · x y`, and the tangent tariff is at most
the stored polynomial `Pk u / ONE`. -/

namespace OM.NNN20

open Finset

/-- a passing gate gives the sign on the whole box -/
lemma gateOK_spec {t : TM} {s : Bool} (h : gateOK t s = true) {f : ℝ → ℝ → ℝ} (ht : t.Encl f)
    {x y : ℝ} (hx : |x| ≤ 1) (hy : |y| ≤ 1) : 0 ≤ f x y ∧ (s = true → 0 < f x y) := by
  have hr := (rng_spec ht hx hy).1
  have hO := ONE_pos
  unfold gateOK at h
  split_ifs at h with hs
  · have h' : (0 : ℝ) < t.rng.1 := by exact_mod_cast (of_decide_eq_true h)
    have : 0 < f x y := by nlinarith
    exact ⟨this.le, fun _ => this⟩
  · have h' : (0 : ℝ) ≤ t.rng.1 := by exact_mod_cast (of_decide_eq_true h)
    refine ⟨by nlinarith, fun h2 => absurd h2 hs⟩

section
variable {n : GNode} {θ : Fin 3 → TM} {P : Fin 3 → Fin 3 → TM}
  {θf : Fin 3 → ℝ → ℝ → ℝ} {Pf : Fin 3 → Fin 3 → ℝ → ℝ → ℝ}

/-- the profile and the parents at a point -/
def atθ (θf : Fin 3 → ℝ → ℝ → ℝ) (x y : ℝ) : Fin 3 → ℝ := fun i => θf i x y
def atP (Pf : Fin 3 → Fin 3 → ℝ → ℝ → ℝ) (x y : ℝ) : Fin 3 → Fin 3 → ℝ := fun i j => Pf i j x y

structure BondSpec (n : GNode) (θf : Fin 3 → ℝ → ℝ → ℝ) (Pf : Fin 3 → Fin 3 → ℝ → ℝ → ℝ)
    (i : Fin 3) (B : BondTM) : Prop where
  slope : B.slope.Encl (fun x y => gEta (atP Pf x y) i - θf i x y)
  w : B.w.Encl (fun x y => gW n (atθ θf x y) (atP Pf x y) i)
  L : B.L.Encl (fun x y => gL n (atθ θf x y) (atP Pf x y) i)
  beta_some : ∀ bt, B.beta = some bt → n.tri i = true ∧ bt.Encl (fun x y => gBeta n (atθ θf x y) (atP Pf x y) i)
  beta_none : B.beta = none → n.tri i = false

theorem bondTM_spec (hθ : ∀ i, (θ i).Encl (θf i)) (hP : ∀ i j, (P i j).Encl (Pf i j))
    {i : Fin 3} {B : BondTM} (hB : bondTM n θ P i = some B) : BondSpec n θf Pf i B := by
  have heta : ((P i (oth1 i)).add (P i (oth2 i))).Encl (fun x y => gEta (atP Pf x y) i) :=
    TM.add_encl (hP _ _) (hP _ _)
  -- the common tail: exp, moment, log
  have tail : ∀ (z w : TM) (beta : Option TM) (zf wf : ℝ → ℝ → ℝ),
      z.Encl zf → w.Encl wf →
      (∀ x y, |x| ≤ 1 → |y| ≤ 1 → zf x y = gZ n (atθ θf x y) (atP Pf x y) i) →
      (∀ x y, |x| ≤ 1 → |y| ≤ 1 → wf x y = gW n (atθ θf x y) (atP Pf x y) i) →
      ∀ B', (match (TM.smul ((n.act i).d : ℤ) z).exp2 with
        | none => none
        | some E =>
          match (TM.mulq (1 / ((n.act i).q : ℚ)) ((TM.const ONE).add
              (TM.smul (((n.act i).q - 1 : ℕ) : ℤ) E))).log2 with
          | none => none
          | some L => some (⟨((P i (oth1 i)).add (P i (oth2 i))).sub (θ i), beta, w, L⟩ : BondTM)) =
          some B' →
      B'.slope.Encl (fun x y => gEta (atP Pf x y) i - θf i x y) ∧
      B'.w.Encl (fun x y => gW n (atθ θf x y) (atP Pf x y) i) ∧
      B'.L.Encl (fun x y => gL n (atθ θf x y) (atP Pf x y) i) ∧ B'.beta = beta := by
    intro z w beta zf wf hz hw hzf hwf B' hB'
    split at hB'
    · cases hB'
    rename_i E hE
    split at hB'
    · cases hB'
    rename_i L hL
    cases hB'
    have hE' := TM.exp2_encl (TM.smul_encl ((n.act i).d : ℤ) hz) hE
    have hA := TM.mulq_encl (1 / ((n.act i).q : ℚ)) (TM.add_encl TM.const_one_encl
      (TM.smul_encl (((n.act i).q - 1 : ℕ) : ℤ) hE'))
    have hL' := (TM.log2_encl hA hL).2
    refine ⟨TM.sub_encl heta (hθ i), hw.congr hwf, hL'.congr fun x y hx hy => ?_, rfl⟩
    simp only [gL, hzf x y hx hy]
  unfold bondTM at hB
  dsimp only at hB
  split_ifs at hB with htri
  · split at hB
    · cases hB
    rename_i rb hrb
    have hbeta := TM.mulq_encl (1 / 2) (TM.add_encl (hθ i) heta)
    have hrb' := TM.recip_encl hbeta hrb
    have hz := TM.mul_encl (TM.sub_encl (hθ i) heta) hrb'
    have hw := TM.mul_encl (hθ i) hrb'
    obtain ⟨h1, h2, h3, h4⟩ := tail _ _ _ _ _ hz hw
      (fun x y _ _ => by simp [gZ, gBeta, htri, gEta, atθ, atP])
      (fun x y _ _ => by simp [gW, gBeta, htri, gEta, atθ, atP]) B hB
    refine ⟨h1, h2, h3, fun bt hbt => ?_, fun hn => by rw [h4] at hn; cases hn⟩
    rw [h4] at hbt
    cases hbt
    exact ⟨htri, hbeta.congr fun x y _ _ => by simp [gBeta, htri, gEta, atθ, atP]⟩
  · obtain ⟨h1, h2, h3, h4⟩ := tail _ _ _ _ _ (TM.sub_encl (hθ i) heta) (hθ i)
      (fun x y _ _ => by simp [gZ, gBeta, htri, gEta, atθ, atP])
      (fun x y _ _ => by simp [gW, gBeta, htri, atθ]) B hB
    refine ⟨h1, h2, h3, fun bt hbt => (by rw [h4] at hbt; cases hbt), fun _ => (by simpa using htri)⟩

end

lemma third_comm (u v : Fin 3) : third u v = third v u := by
  fin_cases u <;> fin_cases v <;> rfl

lemma gQ_symm (n : GNode) (θ : Fin 3 → ℝ) (P : Fin 3 → Fin 3 → ℝ) (u v : Fin 3) :
    gQ n θ P u v = gQ n θ P v u := by
  unfold gQ gQ2
  rw [third_comm]
  by_cases h : u = v
  · subst h; rfl
  · rw [if_neg h, if_neg (Ne.symm h)]; ring

lemma pk_encl (c : List ℤ) : (TM.mk c 0 0).Encl (fun x y => peval c x y / ONE) := by
  intro x y _ _
  have : (ONE : ℝ) * (peval c x y / ONE) = peval c x y := by field_simp [ONE_pos.ne']
  simp [this]

lemma all_finRange {f : Fin 3 → Bool} (h : (List.finRange 3).all f = true) : ∀ i, f i = true := by
  intro i
  simp only [List.all_eq_true] at h
  exact h i (List.mem_finRange i)

section
variable {n : GNode} {θ : Fin 3 → TM} {P : Fin 3 → Fin 3 → TM}
  {θf : Fin 3 → ℝ → ℝ → ℝ} {Pf : Fin 3 → Fin 3 → ℝ → ℝ → ℝ}

theorem qTerm1_encl (hθ : ∀ i, (θ i).Encl (θf i)) {B : Fin 3 → BondTM}
    (hB : ∀ i, BondSpec n θf Pf i (B i)) (i : Fin 3) :
    (qTerm1 n θ B i).Encl (fun x y => gQ1 n (atθ θf x y) (atP Pf x y) i) :=
  TM.mulq_encl _ (TM.mul_encl (hθ i) (TM.add_encl (TM.ofq_encl _) (TM.mulq_encl _ (hB i).L)))

theorem qTerm2_encl (hP : ∀ i j, (P i j).Encl (Pf i j)) {B : Fin 3 → BondTM}
    (hB : ∀ i, BondSpec n θf Pf i (B i)) (i u v : Fin 3) :
    (qTerm2 n P B i u v).Encl (fun x y => gQ2 n (atθ θf x y) (atP Pf x y) i u v) :=
  TM.mulq_encl _ (TM.mul_encl (hB i).w (TM.add_encl (TM.mulq_encl _ (hP i v)) (TM.mulq_encl _ (hP i u))))

theorem qEntry_encl (hθ : ∀ i, (θ i).Encl (θf i)) (hP : ∀ i j, (P i j).Encl (Pf i j))
    {B : Fin 3 → BondTM} (hB : ∀ i, BondSpec n θf Pf i (B i)) (u v : Fin 3) :
    (qEntry n θ P B u v).Encl (fun x y => gQ n (atθ θf x y) (atP Pf x y) u v) := by
  unfold qEntry
  have h2 := TM.add_encl (TM.add_encl (qTerm2_encl (θf := θf) hP hB 0 u v) (qTerm2_encl (θf := θf) hP hB 1 u v))
    (qTerm2_encl (θf := θf) hP hB 2 u v)
  by_cases huv : u = v
  · rw [if_pos huv]
    refine (TM.add_encl (TM.const_encl 0) h2).congr fun x y _ _ => ?_
    simp [gQ, huv]
  · rw [if_neg huv]
    refine (TM.add_encl (qTerm1_encl hθ hB (third u v)) h2).congr fun x y _ _ => ?_
    simp [gQ, huv]

end

section
variable {n : GNode} {θ : Fin 3 → TM} {P : Fin 3 → Fin 3 → TM}
  {θf : Fin 3 → ℝ → ℝ → ℝ} {Pf : Fin 3 → Fin 3 → ℝ → ℝ → ℝ}

theorem qMat_encl (hθ : ∀ i, (θ i).Encl (θf i)) (hP : ∀ i j, (P i j).Encl (Pf i j))
    {B : Fin 3 → BondTM} (hB : ∀ i, BondSpec n θf Pf i (B i)) (u v : Fin 3) :
    (qMat n θ P B u v).Encl (fun x y => gQ n (atθ θf x y) (atP Pf x y) u v) := by
  have e := qEntry_encl hθ hP hB
  have sym : ∀ u v, (qEntry n θ P B u v).Encl (fun x y => gQ n (atθ θf x y) (atP Pf x y) v u) :=
    fun u v => (e u v).congr fun x y _ _ => gQ_symm _ _ _ _ _
  fin_cases u <;> fin_cases v
  · exact e 0 0
  · exact e 0 1
  · exact e 0 2
  · exact sym 0 1
  · exact e 1 1
  · exact e 1 2
  · exact sym 0 2
  · exact sym 1 2
  · exact e 2 2

theorem dVec_encl {B : Fin 3 → BondTM} (hB : ∀ i, BondSpec n θf Pf i (B i)) (u : Fin 3) :
    (dVec n B u).Encl (fun x y => gD n (atθ θf x y) (atP Pf x y) u) := by
  have hW := TM.add_encl (TM.add_encl (hB 0).w (hB 1).w) (hB 2).w
  have hd : ∀ u, (dEntry n B (((B 0).w.add (B 1).w).add (B 2).w) u).Encl
      (fun x y => gD n (atθ θf x y) (atP Pf x y) u) := by
    intro u
    unfold dEntry
    have hdu := TM.mulq_encl (n.b u) (TM.add_encl TM.const_one_encl hW)
    split_ifs with hu
    · refine (TM.sub_encl hdu (TM.mulq_encl (n.b n.h) (hB n.h).w)).congr fun x y _ _ => ?_
      simp [gD, hu]
    · refine hdu.congr fun x y _ _ => ?_
      simp [gD, hu]
  fin_cases u
  · exact hd 0
  · exact hd 1
  · exact hd 2

theorem dotA_encl (a : Fin 3 → ℕ) {v : Fin 3 → TM} {vf : Fin 3 → ℝ → ℝ → ℝ}
    (hv : ∀ i, (v i).Encl (vf i)) :
    (dotA a v).Encl (fun x y => (a 0 : ℝ) * vf 0 x y + (a 1 : ℝ) * vf 1 x y + (a 2 : ℝ) * vf 2 x y) :=
  (TM.add_encl (TM.add_encl (TM.smul_encl _ (hv 0)) (TM.smul_encl _ (hv 1))) (TM.smul_encl _ (hv 2))).congr
    fun x y _ _ => by push_cast; ring

theorem projP_encl {D : Fin 3 → TM} {Q : Fin 3 → Fin 3 → TM} {Df : Fin 3 → ℝ → ℝ → ℝ}
    {Qf : Fin 3 → Fin 3 → ℝ → ℝ → ℝ} (hD : ∀ u, (D u).Encl (Df u)) (hQ : ∀ u v, (Q u v).Encl (Qf u v)) :
    (projP D Q).Encl (fun x y => Df 1 x y * Df 1 x y * Qf 0 0 x y -
      2 * (Df 0 x y * Df 1 x y * Qf 0 1 x y) + Df 0 x y * Df 0 x y * Qf 1 1 x y) :=
  (TM.add_encl (TM.sub_encl (TM.mul_encl (TM.mul_encl (hD 1) (hD 1)) (hQ 0 0))
    (TM.smul_encl 2 (TM.mul_encl (TM.mul_encl (hD 0) (hD 1)) (hQ 0 1))))
    (TM.mul_encl (TM.mul_encl (hD 0) (hD 0)) (hQ 1 1))).congr fun x y _ _ => by push_cast; ring

theorem projQ_encl {D : Fin 3 → TM} {Q : Fin 3 → Fin 3 → TM} {Df : Fin 3 → ℝ → ℝ → ℝ}
    {Qf : Fin 3 → Fin 3 → ℝ → ℝ → ℝ} (hD : ∀ u, (D u).Encl (Df u)) (hQ : ∀ u v, (Q u v).Encl (Qf u v)) :
    (projQ D Q).Encl (fun x y => Df 1 x y * Df 2 x y * Qf 0 0 x y - Df 0 x y * Df 1 x y * Qf 0 2 x y -
      Df 0 x y * Df 2 x y * Qf 0 1 x y + Df 0 x y * Df 0 x y * Qf 1 2 x y) :=
  TM.add_encl (TM.sub_encl (TM.sub_encl (TM.mul_encl (TM.mul_encl (hD 1) (hD 2)) (hQ 0 0))
    (TM.mul_encl (TM.mul_encl (hD 0) (hD 1)) (hQ 0 2)))
    (TM.mul_encl (TM.mul_encl (hD 0) (hD 2)) (hQ 0 1)))
    (TM.mul_encl (TM.mul_encl (hD 0) (hD 0)) (hQ 1 2))

theorem projR_encl {D : Fin 3 → TM} {Q : Fin 3 → Fin 3 → TM} {Df : Fin 3 → ℝ → ℝ → ℝ}
    {Qf : Fin 3 → Fin 3 → ℝ → ℝ → ℝ} (hD : ∀ u, (D u).Encl (Df u)) (hQ : ∀ u v, (Q u v).Encl (Qf u v)) :
    (projR D Q).Encl (fun x y => Df 2 x y * Df 2 x y * Qf 0 0 x y -
      2 * (Df 0 x y * Df 2 x y * Qf 0 2 x y) + Df 0 x y * Df 0 x y * Qf 2 2 x y) :=
  (TM.add_encl (TM.sub_encl (TM.mul_encl (TM.mul_encl (hD 2) (hD 2)) (hQ 0 0))
    (TM.smul_encl 2 (TM.mul_encl (TM.mul_encl (hD 0) (hD 2)) (hQ 0 2))))
    (TM.mul_encl (TM.mul_encl (hD 0) (hD 0)) (hQ 2 2))).congr fun x y _ _ => by push_cast; ring

structure GOutSpec (n : GNode) (θf : Fin 3 → ℝ → ℝ → ℝ) (Pf : Fin 3 → Fin 3 → ℝ → ℝ → ℝ)
    (o : GOut) : Prop where
  slope : ∀ i, (o.slope i).Encl (fun x y => gEta (atP Pf x y) i - θf i x y)
  beta_some : ∀ i bt, o.beta i = some bt →
    n.tri i = true ∧ bt.Encl (fun x y => gBeta n (atθ θf x y) (atP Pf x y) i)
  beta_none : ∀ i, o.beta i = none → n.tri i = false
  D : ∀ u, (o.D u).Encl (fun x y => gD n (atθ θf x y) (atP Pf x y) u)
  p : o.p.Encl (fun x y => gPp n (atθ θf x y) (atP Pf x y))
  r : o.r.Encl (fun x y => gPr n (atθ θf x y) (atP Pf x y))
  det : o.det.Encl (fun x y => gPp n (atθ θf x y) (atP Pf x y) * gPr n (atθ θf x y) (atP Pf x y) -
    gPq n (atθ θf x y) (atP Pf x y) * gPq n (atθ θf x y) (atP Pf x y))
  c : ∀ u, (o.c u).Encl (fun x y => gC n (atθ θf x y) (atP Pf x y) u)

theorem gnodeTM_spec (hθ : ∀ i, (θ i).Encl (θf i)) (hP : ∀ i j, (P i j).Encl (Pf i j))
    {o : GOut} (h : gnodeTM n θ P = some o) : GOutSpec n θf Pf o := by
  unfold gnodeTM at h
  split at h
  · rename_i B0 B1 B2 h0 h1 h2
    have hB : ∀ i, BondSpec n θf Pf i ((![B0, B1, B2] : Fin 3 → BondTM) i) := by
      intro i
      fin_cases i
      · exact bondTM_spec hθ hP h0
      · exact bondTM_spec hθ hP h1
      · exact bondTM_spec hθ hP h2
    dsimp only at h
    split at h
    · cases h
    rename_i rden hrden
    cases h
    set B : Fin 3 → BondTM := ![B0, B1, B2]
    have hQ := qMat_encl hθ hP hB
    have hD := dVec_encl hB
    have hQA : ∀ u, ((![dotA n.a (qMat n θ P B 0), dotA n.a (qMat n θ P B 1),
        dotA n.a (qMat n θ P B 2)] : Fin 3 → TM) u).Encl
        (fun x y => gQa n (atθ θf x y) (atP Pf x y) u) := by
      intro u
      fin_cases u <;> exact (dotA_encl n.a (hQ _)).congr fun x y _ _ => by simp [gQa]
    have hden : (dotA n.a (dVec n B)).Encl (fun x y => gDen n (atθ θf x y) (atP Pf x y)) :=
      (dotA_encl n.a hD).congr fun x y _ _ => by simp [gDen]
    have hnum : (dotA n.a (![dotA n.a (qMat n θ P B 0), dotA n.a (qMat n θ P B 1),
        dotA n.a (qMat n θ P B 2)] : Fin 3 → TM)).Encl (fun x y => gNum n (atθ θf x y) (atP Pf x y)) :=
      (dotA_encl n.a hQA).congr fun x y _ _ => by simp [gNum]
    have hrd := TM.recip_encl hden hrden
    have hval := TM.mul_encl hnum hrd
    refine ⟨fun i => (hB i).slope, fun i bt hbt => (hB i).beta_some bt hbt,
      fun i hi => (hB i).beta_none hi, hD, ?_, ?_, ?_, ?_⟩
    · exact (projP_encl hD hQ).congr fun x y _ _ => by simp [gPp]
    · exact (projR_encl hD hQ).congr fun x y _ _ => by simp [gPr]
    · exact (TM.sub_encl (TM.mul_encl (projP_encl hD hQ) (projR_encl hD hQ))
        (TM.mul_encl (projQ_encl hD hQ) (projQ_encl hD hQ))).congr fun x y _ _ => by simp [gPp, gPr, gPq]
    · intro u
      have hc : ∀ u, (((TM.smul 2 ((![dotA n.a (qMat n θ P B 0), dotA n.a (qMat n θ P B 1),
          dotA n.a (qMat n θ P B 2)] : Fin 3 → TM) u)).sub
          (((dotA n.a (![dotA n.a (qMat n θ P B 0), dotA n.a (qMat n θ P B 1),
          dotA n.a (qMat n θ P B 2)] : Fin 3 → TM)).mul rden).mul (dVec n B u))).mul rden).Encl
          (fun x y => gC n (atθ θf x y) (atP Pf x y) u) := fun u =>
        (TM.mul_encl (TM.sub_encl (TM.smul_encl 2 (hQA u)) (TM.mul_encl hval (hD u))) hrd).congr
          fun x y _ _ => by simp [gC, gVal]
      fin_cases u
      · exact hc 0
      · exact hc 1
      · exact hc 2
  · cases h

/-- **Soundness of the global-node checker.** -/
theorem gcheck_spec {Pk : Fin 3 → List ℤ} (h : gcheck n θ P Pk = true)
    (hθ : ∀ i, (θ i).Encl (θf i)) (hP : ∀ i j, (P i j).Encl (Pf i j))
    {x y : ℝ} (hx : |x| ≤ 1) (hy : |y| ≤ 1) :
    GGates n (atθ θf x y) (atP Pf x y) ∧
    ∀ u, gC n (atθ θf x y) (atP Pf x y) u ≤ peval (Pk u) x y / ONE := by
  unfold gcheck at h
  split at h
  · cases h
  rename_i o ho
  have S := gnodeTM_spec hθ hP ho
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hsl, hbe⟩, hD⟩, hp⟩, hr⟩, hdet⟩, hc⟩, hdom⟩ := h
  have hsl' := all_finRange hsl
  have hbe' := all_finRange hbe
  have hD' := all_finRange hD
  have hc' := all_finRange hc
  have hdom' := all_finRange hdom
  refine ⟨⟨fun i => ?_, fun i hi => ?_, fun u => ?_, ?_, ?_, ?_, fun u => ?_⟩, fun u => ?_⟩
  · have := (gateOK_spec (hsl' i) (S.slope i) hx hy).1
    simp only [atθ] at this ⊢; linarith
  · have hb := hbe' i
    cases hbt : o.beta i with
    | none => rw [hbt] at hb; simp [hi] at hb
    | some bt =>
      rw [hbt] at hb
      simp only [Bool.and_eq_true] at hb
      obtain ⟨⟨_, hb1⟩, hb2⟩ := hb
      obtain ⟨_, hbe⟩ := S.beta_some i bt hbt
      have g1 := (gateOK_spec hb1 hbe hx hy).2 rfl
      have g2 := (gateOK_spec hb2 (TM.sub_encl TM.const_one_encl hbe) hx hy).1
      exact ⟨g1, by linarith⟩
  · exact (gateOK_spec (hD' u) (S.D u) hx hy).2 rfl
  · have := (gateOK_spec hp (TM.neg_encl S.p) hx hy).1; linarith
  · have := (gateOK_spec hr (TM.neg_encl S.r) hx hy).1; linarith
  · exact (gateOK_spec hdet S.det hx hy).1
  · exact (gateOK_spec (hc' u) (S.c u) hx hy).1
  · have := (gateOK_spec (hdom' u) (TM.sub_encl (pk_encl (Pk u)) (S.c u)) hx hy).1
    linarith

end

end OM.NNN20
