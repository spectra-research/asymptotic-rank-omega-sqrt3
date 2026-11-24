import Lib.OM.NNN20.GlobalSpec

/-! # Global recipes on a cell

A recipe is a list of global nodes with parent references: the coefficient star of the bond
(`star`), one of the three affine seed tariffs (`seed h`), or the stored polynomial upper tariff of
an earlier node (`node m`). `gcheckAt S C R k` checks node `k` on the cell `C` with Taylor models;
`gcheckAt_spec` turns a passing check into the real gates and the domination by `R[k].Pk` at every
point of the cell. -/

namespace OM.NNN20

open Finset

inductive Ref where
  | star
  | seed (h : Fin 3)
  | node (k : ℕ)
  deriving DecidableEq

/-- the profile track `t` and the affine seed `C_hh = u - A δ_h`, `C_hj = v + B δ_h - C (δ_j - δ_k)` -/
structure SeedPrm where
  t : ℚ
  u : ℚ
  v : ℚ
  A : ℚ
  B : ℚ
  C : ℚ

structure GEntry where
  node : GNode
  par : Fin 3 → Ref
  Pk : Fin 3 → List ℤ

instance : Inhabited GEntry := ⟨⟨⟨0, fun _ => 0, fun _ => F11, fun _ => false, fun _ => 0⟩,
  fun _ => .star, fun _ => []⟩⟩

/-! ## Taylor models of the parents -/

def seedTM (S : SeedPrm) (θ : Fin 3 → TM) (h j : Fin 3) : TM :=
  let tt := TM.ofq S.t
  if j = h then (TM.ofq S.u).sub (TM.mulq S.A ((θ h).sub tt))
  else ((TM.ofq S.v).add (TM.mulq S.B ((θ h).sub tt))).sub
    (TM.mulq S.C (((θ j).sub tt).sub ((θ (third h j)).sub tt)))

def parRow (S : SeedPrm) (θ : Fin 3 → TM) (R : List GEntry) (r : Ref) (i : Fin 3) : Fin 3 → TM :=
  match r with
  | .star => ![starTM θ i 0, starTM θ i 1, starTM θ i 2]
  | .seed h => ![seedTM S θ h 0, seedTM S θ h 1, seedTM S θ h 2]
  | .node m => let e := R.getD m default; ![⟨e.Pk 0, 0, 0⟩, ⟨e.Pk 1, 0, 0⟩, ⟨e.Pk 2, 0, 0⟩]

/-- the check of node `k` of the recipe `R` on the cell `C` -/
def gcheckAt (S : SeedPrm) (C : Cell) (R : List GEntry) (k : ℕ) : Bool :=
  let θ := thetaTM S.t C
  let e := R.getD k default
  let P0 := parRow S θ R (e.par 0) 0
  let P1 := parRow S θ R (e.par 1) 1
  let P2 := parRow S θ R (e.par 2) 2
  gcheck e.node θ ![P0, P1, P2] e.Pk

/-! ## Real semantics -/

/-- the real cell coordinates: `r = mid + rad x`, `q = mid + rad y` or `q = r - s` -/
noncomputable def rOf (C : Cell) (x : ℝ) : ℝ := (((C.a + C.b) / 2 : ℚ) : ℝ) + (((C.b - C.a) / 2 : ℚ) : ℝ) * x

noncomputable def qOf (C : Cell) (x y : ℝ) : ℝ :=
  if C.rs then rOf C x - ((((max 0 (C.a - C.d)) + (C.b - C.c)) / 2 : ℚ) +
      (((C.b - C.c) - max 0 (C.a - C.d)) / 2 : ℚ) * y)
  else (((C.c + C.d) / 2 : ℚ) : ℝ) + (((C.d - C.c) / 2 : ℚ) : ℝ) * y

/-- the ordered profile `(t + r, t - r/2 + 3q/2, t - r/2 - 3q/2)`, permuted -/
noncomputable def thetaReal (t : ℚ) (C : Cell) (i : Fin 3) (x y : ℝ) : ℝ :=
  (![(t : ℝ) + rOf C x, (t : ℝ) + ((((-1 / 2 : ℚ) : ℝ)) * rOf C x + (((3 / 2 : ℚ) : ℝ)) * qOf C x y),
    (t : ℝ) - ((((1 / 2 : ℚ) : ℝ)) * rOf C x + (((3 / 2 : ℚ) : ℝ)) * qOf C x y)] : Fin 3 → ℝ) (C.perm i)

def starR (θ : Fin 3 → ℝ) (h j : Fin 3) : ℝ := if j = h then 0 else θ (third h j)

def seedR (S : SeedPrm) (θ : Fin 3 → ℝ) (h j : Fin 3) : ℝ :=
  if j = h then (S.u : ℝ) - S.A * (θ h - S.t)
  else (S.v : ℝ) + S.B * (θ h - S.t) - S.C * ((θ j - S.t) - (θ (third h j) - S.t))

noncomputable def parR (S : SeedPrm) (C : Cell) (R : List GEntry) (r : Ref) (i j : Fin 3)
    (x y : ℝ) : ℝ :=
  match r with
  | .star => starR (fun l => thetaReal S.t C l x y) i j
  | .seed h => seedR S (fun l => thetaReal S.t C l x y) h j
  | .node m => peval ((R.getD m default).Pk j) x y / ONE

/-! ## Enclosures -/

theorem thetaTM_encl (t : ℚ) (C : Cell) (i : Fin 3) :
    (thetaTM t C i).Encl (thetaReal t C i) := by
  have hr : (TM.affine ((C.a + C.b) / 2) ((C.b - C.a) / 2) 0).Encl (fun x _ => rOf C x) :=
    (TM.affine_encl _ _ 0).congr fun x y _ _ => by simp [rOf]
  have hq : (if C.rs then
      (TM.affine ((C.a + C.b) / 2) ((C.b - C.a) / 2) 0).sub
        (TM.affine ((max 0 (C.a - C.d) + (C.b - C.c)) / 2) ((C.b - C.c - max 0 (C.a - C.d)) / 2) 1)
      else TM.affine ((C.c + C.d) / 2) ((C.d - C.c) / 2) 1).Encl (qOf C) := by
    split_ifs with hrs
    · refine (TM.sub_encl hr (TM.affine_encl _ _ 1)).congr fun x y _ _ => ?_
      simp [qOf, hrs]
    · refine (TM.affine_encl _ _ 1).congr fun x y _ _ => ?_
      simp [qOf, hrs]
  have ht := TM.ofq_encl t
  have b0 := TM.add_encl ht hr
  have b1 := TM.add_encl ht (TM.add_encl (TM.mulq_encl (-1 / 2) hr) (TM.mulq_encl (3 / 2) hq))
  have b2 := TM.sub_encl ht (TM.add_encl (TM.mulq_encl (1 / 2) hr) (TM.mulq_encl (3 / 2) hq))
  unfold thetaTM
  dsimp only
  have key : ∀ k : Fin 3, ((![(TM.ofq t).add (TM.affine ((C.a + C.b) / 2) ((C.b - C.a) / 2) 0),
      (TM.ofq t).add ((TM.mulq (-1 / 2) (TM.affine ((C.a + C.b) / 2) ((C.b - C.a) / 2) 0)).add
        (TM.mulq (3 / 2) (if C.rs then
          (TM.affine ((C.a + C.b) / 2) ((C.b - C.a) / 2) 0).sub
            (TM.affine ((max 0 (C.a - C.d) + (C.b - C.c)) / 2) ((C.b - C.c - max 0 (C.a - C.d)) / 2) 1)
          else TM.affine ((C.c + C.d) / 2) ((C.d - C.c) / 2) 1))),
      (TM.ofq t).sub ((TM.mulq (1 / 2) (TM.affine ((C.a + C.b) / 2) ((C.b - C.a) / 2) 0)).add
        (TM.mulq (3 / 2) (if C.rs then
          (TM.affine ((C.a + C.b) / 2) ((C.b - C.a) / 2) 0).sub
            (TM.affine ((max 0 (C.a - C.d) + (C.b - C.c)) / 2) ((C.b - C.c - max 0 (C.a - C.d)) / 2) 1)
          else TM.affine ((C.c + C.d) / 2) ((C.d - C.c) / 2) 1)))] : Fin 3 → TM) k).Encl
      (fun x y => (![(t : ℝ) + rOf C x, (t : ℝ) + ((((-1 / 2 : ℚ) : ℝ)) * rOf C x +
        (((3 / 2 : ℚ) : ℝ)) * qOf C x y), (t : ℝ) - ((((1 / 2 : ℚ) : ℝ)) * rOf C x +
        (((3 / 2 : ℚ) : ℝ)) * qOf C x y)] : Fin 3 → ℝ) k) := by
    intro k
    fin_cases k
    · exact b0
    · exact b1
    · exact b2
  exact key (C.perm i)

theorem starTM_encl {θ : Fin 3 → TM} {θf : Fin 3 → ℝ → ℝ → ℝ} (hθ : ∀ i, (θ i).Encl (θf i))
    (h j : Fin 3) : (starTM θ h j).Encl (fun x y => starR (fun l => θf l x y) h j) := by
  unfold starTM
  split_ifs with hj
  · exact (TM.const_encl 0).congr fun x y _ _ => by simp [starR, hj]
  · exact (hθ _).congr fun x y _ _ => by simp [starR, hj]

theorem seedTM_encl (S : SeedPrm) {θ : Fin 3 → TM} {θf : Fin 3 → ℝ → ℝ → ℝ}
    (hθ : ∀ i, (θ i).Encl (θf i)) (h j : Fin 3) :
    (seedTM S θ h j).Encl (fun x y => seedR S (fun l => θf l x y) h j) := by
  unfold seedTM
  dsimp only
  have hd : ∀ i, ((θ i).sub (TM.ofq S.t)).Encl (fun x y => θf i x y - S.t) :=
    fun i => TM.sub_encl (hθ i) (TM.ofq_encl S.t)
  split_ifs with hj
  · exact (TM.sub_encl (TM.ofq_encl _) (TM.mulq_encl _ (hd h))).congr fun x y _ _ => by
      simp [seedR, hj]
  · exact (TM.sub_encl (TM.add_encl (TM.ofq_encl _) (TM.mulq_encl _ (hd h)))
      (TM.mulq_encl _ (TM.sub_encl (hd j) (hd _)))).congr fun x y _ _ => by simp [seedR, hj]

theorem parRow_encl (S : SeedPrm) (C : Cell) (R : List GEntry) (r : Ref) (i j : Fin 3) :
    (parRow S (thetaTM S.t C) R r i j).Encl (parR S C R r i j) := by
  have hθ := thetaTM_encl S.t C
  cases r with
  | star => fin_cases j <;> exact (starTM_encl hθ i _).congr fun x y _ _ => rfl
  | seed h => fin_cases j <;> exact (seedTM_encl S hθ h _).congr fun x y _ _ => rfl
  | node m => fin_cases j <;> exact (pk_encl _).congr fun x y _ _ => rfl

/-- **Soundness of one recipe check.** -/
theorem gcheckAt_spec {S : SeedPrm} {C : Cell} {R : List GEntry} {k : ℕ}
    (h : gcheckAt S C R k = true) {x y : ℝ} (hx : |x| ≤ 1) (hy : |y| ≤ 1) :
    GGates (R.getD k default).node (fun i => thetaReal S.t C i x y)
      (fun i j => parR S C R ((R.getD k default).par i) i j x y) ∧
    ∀ u, gC (R.getD k default).node (fun i => thetaReal S.t C i x y)
      (fun i j => parR S C R ((R.getD k default).par i) i j x y) u ≤
      peval ((R.getD k default).Pk u) x y / ONE := by
  unfold gcheckAt at h
  dsimp only at h
  have hP : ∀ i j, ((![parRow S (thetaTM S.t C) R ((R.getD k default).par 0) 0,
      parRow S (thetaTM S.t C) R ((R.getD k default).par 1) 1,
      parRow S (thetaTM S.t C) R ((R.getD k default).par 2) 2] : Fin 3 → Fin 3 → TM) i j).Encl
      (parR S C R ((R.getD k default).par i) i j) := by
    intro i j
    fin_cases i <;> exact parRow_encl S C R _ _ j
  exact gcheck_spec h (thetaTM_encl S.t C) hP hx hy

end OM.NNN20
