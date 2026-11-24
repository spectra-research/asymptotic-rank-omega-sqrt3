import Lib.OM.NNN32.Sectors
import Lib.OM.NNN32.Defs

/-! # The two factorizations exclude a Euclidean square -/

noncomputable section

namespace OM.NNN32

open OM.NNN30.Geom ConePt Filter Topology

def charge {X : Type*} (d : X → X → ℝ) (κ : ℝ) (a b c e u v : X) :=
  d a u + d b u + d c v + d e v + κ*d u v

lemma cone_twoTerm {X : Type*} {S : MidSpace X} {κ : ℝ} (h : twoTermBound S.d κ) (o : X) :
    twoTermBound (coneSpace S o).d κ := by
  intro t hsep u v u' v'
  let q := charge (ρ (S := S) (o := o)) κ
  have hlim (a b c e u v : ConePt S o) :
      Tendsto (fun n => charge (fun x y : ConePt S o => sd x y n) κ a b c e u v)
        (U : Filter ℕ) (𝓝 (q a b c e u v)) :=
    ((((tendsto_ρ a u).add (tendsto_ρ b u)).add (tendsto_ρ c v)).add (tendsto_ρ e v)).add
      ((tendsto_ρ u v).const_mul κ)
  apply le_of_tendsto_of_tendsto ((tendsto_ρ _ _).add (tendsto_ρ _ _))
    ((hlim (t 0) (t 1) (t 2) (t 3) u v).max (hlim (t 0) (t 2) (t 1) (t 3) u' v'))
  have hev : ∀ᶠ n in (U : Filter ℕ), ∀ i j : Fin 4, i ≠ j → 0 < S.d ((t i).seq n) ((t j).seq n) := by
    apply Filter.eventually_all.2
    intro i
    apply Filter.eventually_all.2
    intro j
    by_cases hij : i=j
    · exact Eventually.of_forall fun _ hne => (hne hij).elim
    filter_upwards [(tendsto_order.1 (tendsto_ρ (t i) (t j))).1 0 (hsep i j hij)] with n hn
    exact fun _ => (mul_pos_iff_of_pos_left (by positivity : (0:ℝ)<2^n)).1 hn
  filter_upwards [hev] with n hn
  have h' := h (fun i => (t i).seq n) hn (u.seq n) (v.seq n) (u'.seq n) (v'.seq n)
  have hscale := mul_le_mul_of_nonneg_left h' (by positivity : (0:ℝ) ≤ 2^n)
  simpa only [charge,sd,mul_max_of_nonneg _ _ (by positivity : (0:ℝ) ≤ 2^n),mul_add,
    mul_left_comm κ] using hscale

private lemma square_discount {κ : ℝ} (hκ : 0 ≤ κ) (hstrict : κ < Real.sqrt 2) :
    ∃ t : ℝ, 0 < t ∧ t ≤ 1/2 ∧
      4*Real.sqrt ((1/2:ℝ)^2+(1/2-t)^2) + 2*κ*t < 2*Real.sqrt 2 := by
  let t := (2-Real.sqrt 2*κ)/4
  have hr := Real.sqrt_pos.2 (by norm_num : (0:ℝ) < 2)
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  have ht : 0 < t := by dsimp [t]; nlinarith [mul_lt_mul_of_pos_left hstrict hr]
  have ht' : t ≤ 1/2 := by dsimp [t]; nlinarith [mul_nonneg hr.le hκ]
  refine ⟨t,ht,ht',?_⟩
  have hsq := Real.sq_sqrt (show 0 ≤ (1/2:ℝ)^2+(1/2-t)^2 by positivity)
  have hpos : 0 < 2*Real.sqrt 2-2*κ*t := by nlinarith [mul_le_mul_of_nonneg_left ht' hκ]
  have he : 4*t = 2-Real.sqrt 2*κ := by dsimp [t]; ring
  have hdiff : (2*Real.sqrt 2-2*κ*t)^2 - 16*((1/2:ℝ)^2+(1/2-t)^2) =
      (16+4*κ^2)*t^2 := by linear_combination 4*hs - 8*t*he
  have hgt : 0 < (16+4*κ^2)*t^2 := by positivity
  nlinarith [Real.sqrt_nonneg ((1/2:ℝ)^2+(1/2-t)^2)]

/-- On a Euclidean square the two symmetric pairs of factor sites can both
underspend the diagonals. All eight sites are in the closed unit square. -/
private lemma no_square {X : Type*} {d : X → X → ℝ} {κ r : ℝ} (hr : 0 < r)
    (hκ : 0 ≤ κ) (hstrict : κ < Real.sqrt 2) (h : twoTermBound d κ)
    (f : ℝ × ℝ → X) (hf : ∀ v w, InSquare v → InSquare w → d (f v) (f w) = r*planeLength v w) :
    False := by
  obtain ⟨t,ht,ht',hsave⟩ := square_discount hκ hstrict
  let A : Fin 4 → ℝ × ℝ := ![(0,0),(1,0),(0,1),(1,1)]
  let u : ℝ × ℝ := (1/2,1/2-t)
  let v : ℝ × ℝ := (1/2,1/2+t)
  let w : ℝ × ℝ := (1/2-t,1/2)
  let x : ℝ × ℝ := (1/2+t,1/2)
  have hA (i : Fin 4) : InSquare (A i) := by fin_cases i <;> norm_num [A,InSquare,InQ]
  have hu : InSquare u := by dsimp [InSquare,InQ,u]; exact ⟨⟨by norm_num,by linarith⟩,by norm_num,by linarith⟩
  have hv : InSquare v := by dsimp [InSquare,InQ,v]; exact ⟨⟨by norm_num,by linarith⟩,by norm_num,by linarith⟩
  have hw : InSquare w := by dsimp [InSquare,InQ,w]; exact ⟨⟨by linarith,by norm_num⟩,by linarith,by norm_num⟩
  have hx : InSquare x := by dsimp [InSquare,InQ,x]; exact ⟨⟨by linarith,by norm_num⟩,by linarith,by norm_num⟩
  have hsep (i j : Fin 4) (hn : i ≠ j) : 0 < d (f (A i)) (f (A j)) := by
    rw [hf _ _ (hA i) (hA j)]
    apply mul_pos hr
    fin_cases i <;> fin_cases j <;> first
      | exact (hn rfl).elim
      | norm_num [A,planeLength]
  have hh := h (fun i => f (A i)) hsep (f u) (f v) (f w) (f x)
  simp only [hf _ _ (hA _) (hA _),hf _ _ (hA _) hu,hf _ _ (hA _) hv,
    hf _ _ (hA _) hw,hf _ _ (hA _) hx,hf _ _ hu hv,hf _ _ hw hx] at hh
  let b := Real.sqrt ((1/2:ℝ)^2+(1/2-t)^2)
  have leaf : ∀ (i : Fin 4), planeLength (A i) (if i=0 ∨ i=1 then u else v) = b ∧
      planeLength (A i) (if i=0 ∨ i=2 then w else x) = b := by
    intro i
    fin_cases i <;> constructor <;> norm_num [A,u,v,w,x,planeLength,b] <;>
      apply congrArg Real.sqrt <;> ring
  have link1 : planeLength u v = 2*t := by
    unfold planeLength
    rw [show (v.1-u.1)^2+(v.2-u.2)^2 = (2*t)^2 by dsimp [v,u]; ring, Real.sqrt_sq (by positivity)]
  have link2 : planeLength w x = 2*t := by
    unfold planeLength
    rw [show (x.1-w.1)^2+(x.2-w.2)^2 = (2*t)^2 by dsimp [x,w]; ring, Real.sqrt_sq (by positivity)]
  have l0 := leaf 0
  have l1 := leaf 1
  have l2 := leaf 2
  have l3 := leaf 3
  norm_num at l0 l1 l2 l3
  rw [l0.1,l1.1,l2.1,l3.1,l0.2,l2.2,l1.2,l3.2,link1,link2,max_self] at hh
  have diag : planeLength (A 0) (A 3) = Real.sqrt 2 ∧ planeLength (A 1) (A 2) = Real.sqrt 2 := by
    norm_num [planeLength,A]
  rw [diag.1,diag.2] at hh
  change 4*b+2*κ*t < _ at hsave
  nlinarith [mul_lt_mul_of_pos_left hsave hr]

theorem det_nonpos_of_twoTerm {X : Type*} {S : MidSpace X} {κ : ℝ} (hk : 0 ≤ κ)
    (hc : κ < Real.sqrt 2) (h : twoTermBound S.d κ) (o pa pb : X) (ha : 0 < S.d o pa) :
    let a := S.d o pa
    let b := S.d o pb
    4*a^2*b^2-(a^2+b^2-delta S o pa pb^2)^2 ≤ 0 := by
  dsimp only
  by_contra! hd
  obtain ⟨r,f,hr,_,_,hdist⟩ := euclidean_square (qhyp S o pa pb) ha
    (Nf_e1 S o pa pb) (Nf_e2 S o pa pb) (by rw [Nf_e21]) hd
  exact no_square hr hk hc (cone_twoTerm h o) (fun z => J S o pa pb (f z)) hdist

end OM.NNN32
