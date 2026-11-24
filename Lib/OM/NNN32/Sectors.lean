import Lib.OM.NNN30.Geom.Main
import Mathlib.Tactic.LinearCombination
import Mathlib.Algebra.BigOperators.Fin
import PLATFORM.Statements.«R113.10»

/-! # Euclidean squares in a nondegenerate two-ray sector -/

noncomputable section

namespace OM.NNN32

open OM.NNN30.Geom ConePt

abbrev squareBound {X : Type*} (S : MidSpace X) (c : ℝ) :=
  ∀ a b z e, S.d (S.m a b) (S.m z e) + S.d (S.m a e) (S.m z b) ≤
    c * max (S.d a z) (S.d b e)

lemma cone_squareBound {X : Type*} {S : MidSpace X} {c : ℝ} (h : squareBound S c) (o : X) :
    squareBound (coneSpace S o) c := by
  intro a b z e
  apply le_of_tendsto_of_tendsto' ((tendsto_ρ _ _).add (tendsto_ρ _ _))
    (((tendsto_ρ a z).max (tendsto_ρ b e)).const_mul c)
  intro n
  simp only [sd, M]
  rw [← mul_add, ← mul_max_of_nonneg _ _ (by positivity : (0 : ℝ) ≤ 2^n), mul_left_comm]
  exact mul_le_mul_of_nonneg_left (h _ _ _ _) (by positivity)

def InSquare (z : ℝ × ℝ) : Prop := InQ z ∧ z.1 ≤ 1 ∧ z.2 ≤ 1

def planeLength (v w : ℝ × ℝ) := Real.sqrt ((w.1-v.1)^2 + (w.2-v.2)^2)

/-- Completing the square in the two-ray Gram form places a Euclidean unit square,
up to one common scale, in the parameter quadrant. The placement preserves affine midpoints. -/
theorem euclidean_square {N : ℝ × ℝ → ℝ × ℝ → ℝ} {L a b k : ℝ} (hq : QHyp N L)
    (ha : 0 < a) (h1 : N 0 (1,0) = a) (h2 : N 0 (0,1) = b)
    (hk : a^2+b^2-N (0,1) (1,0)^2 = k) (hdet : 0 < 4*a^2*b^2-k^2) :
    ∃ (r : ℝ) (f : ℝ × ℝ → ℝ × ℝ), 0 < r ∧
      (∀ z, InSquare z → InQ (f z)) ∧
      (∀ v w, mid (f v) (f w) = f (mid v w)) ∧
      ∀ v w, InSquare v → InSquare w → N (f v) (f w) = r * planeLength v w := by
  let q := Real.sqrt (4*a^2*b^2-k^2)
  have hq0 : 0 < q := Real.sqrt_pos.2 hdet
  have hq2 : q^2 = 4*a^2*b^2-k^2 := Real.sq_sqrt hdet.le
  let f (z : ℝ × ℝ) : ℝ × ℝ := (|k|+q*z.1-k*z.2, 2*a^2*z.2)
  have hf (z : ℝ × ℝ) (hz : InSquare z) : InQ (f z) := by
    obtain ⟨⟨hx,hy⟩,_,hy'⟩ := hz
    have hyk := (mul_le_mul_of_nonneg_right (le_abs_self k) hy).trans
      (mul_le_of_le_one_right (abs_nonneg k) hy')
    exact ⟨by dsimp [f]; linarith [mul_nonneg hq0.le hx], by dsimp [f]; positivity⟩
  refine ⟨a*q,f,mul_pos ha hq0,hf,fun v w => ?_,fun v w hv hw => ?_⟩
  · ext <;> dsimp [f,mid] <;> ring
  · have hh := hq.formula (hf v hv) (hf w hw)
    rw [h1,h2,hk] at hh
    apply (pow_left_inj₀ (hq.nonneg (hf v hv) (hf w hw))
      (mul_nonneg (mul_pos ha hq0).le (Real.sqrt_nonneg _)) (by decide +kernel : 2 ≠ 0)).mp
    rw [hh, mul_pow, mul_pow, Real.sq_sqrt (show 0 ≤ (w.1-v.1)^2+(w.2-v.2)^2 by positivity)]
    dsimp [f]
    linear_combination (a^2 * (w.2-v.2)^2) * -hq2

lemma det_nonpos_of_squareBound {X : Type*} {S : MidSpace X} {c : ℝ}
    (hlin : squareBound S c) (hc : c < Real.sqrt 2) (o pa pb : X) (ha : 0 < S.d o pa) :
    let a := S.d o pa
    let b := S.d o pb
    let k := a^2+b^2-delta S o pa pb^2
    4*a^2*b^2-k^2 ≤ 0 := by
  dsimp only
  by_contra! hd
  let N := Nf S o pa pb
  obtain ⟨r,f,hr,hf,haff,hdist⟩ := euclidean_square (qhyp S o pa pb) ha
    (Nf_e1 S o pa pb) (Nf_e2 S o pa pb) (by rw [Nf_e21]) hd
  let A : ℝ × ℝ := (0,0)
  let Z : ℝ × ℝ := (1,0)
  let E : ℝ × ℝ := (0,1)
  have hA : InSquare A := by norm_num [InSquare,InQ,A]
  have hZ : InSquare Z := by norm_num [InSquare,InQ,Z]
  have hE : InSquare E := by norm_num [InSquare,InQ,E]
  have hh := cone_squareBound hlin o (J S o pa pb (f A)) (J S o pa pb (f A))
    (J S o pa pb (f Z)) (J S o pa pb (f E))
  change ρ (M _ _) (M _ _) + ρ (M _ _) (M _ _) ≤ c * max (N (f A) (f Z)) (N (f A) (f E)) at hh
  rw [← Nf_mid S o pa pb (hf _ hA) (hf _ hA) (hf _ hZ) (hf _ hE),
    ← Nf_mid S o pa pb (hf _ hA) (hf _ hE) (hf _ hZ) (hf _ hA)] at hh
  dsimp only [N] at hh
  simp only [haff] at hh
  rw [hdist _ _ hA hZ, hdist _ _ hA hE, hdist, hdist] at hh
  all_goals try norm_num [InSquare,InQ,mid,A,E,Z]
  norm_num [planeLength,mid,A,E,Z] at hh
  have hs : (Real.sqrt 2)⁻¹ = Real.sqrt 2 / 2 := by
    rw [inv_eq_one_div, div_eq_div_iff (by positivity) (by norm_num)]
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  rw [hs] at hh
  nlinarith [mul_lt_mul_of_pos_right hc hr]

private lemma between (S : MidSpace X) (c : ℝ) (hc : c < Real.sqrt 2) (hlin : squareBound S c)
    (o pa pb pc : X)
    (hmin : ∀ q, S.d o pa + S.d o pb + S.d o pc ≤ S.d q pa + S.d q pb + S.d q pc) :
    S.d pa pb = S.d o pa + S.d o pb := by
  apply le_antisymm (by simpa [S.d_comm pa o] using S.d_tri pa o pb)
  rcases (S.d_nonneg o pa).eq_or_lt with h | ha
  · rw [← h,zero_add]
    simpa [← h] using S.d_tri o pa pb
  rcases (S.d_nonneg o pb).eq_or_lt with h | hb
  · rw [← h,add_zero]
    simpa [← h,S.d_comm pb pa] using S.d_tri o pb pa
  have hd := det_nonpos_of_squareBound hlin hc o pa pb ha
  have hang := angle_from_plane (qhyp S o pa pb) ha hb (Nf_e1 S o pa pb) (Nf_e2 S o pa pb)
    (Nf_e21 S o pa pb) (fun z K => Nf_fermat S o pa pb pc hmin z K)
  let a := S.d o pa
  let b := S.d o pb
  let δ := delta S o pa pb
  change 0 < a at ha
  change 0 < b at hb
  change a^2+a*b+b^2 ≤ δ^2 at hang
  change 4*a^2*b^2-(a^2+b^2-δ^2)^2 ≤ 0 at hd
  have hs : 2*a*b ≤ δ^2-a^2-b^2 := by
    apply (pow_le_pow_iff_left₀ (by positivity) (by nlinarith [mul_pos ha hb]) (by norm_num : 2 ≠ 0)).mp
    nlinarith only [hd]
  have hδ0 : 0 ≤ δ := delta_nonneg S o pa pb
  have hδ : a+b ≤ δ := by nlinarith
  exact hδ.trans (delta_le S o pa pb)

theorem proof_R113_10 : S_R113_10 := by
  intro X S c _ hc hlin p o hmin i j hij
  have ht (q : X) := hmin q
  simp [Fin.sum_univ_succ] at ht
  have h01 := between S c hc hlin o (p 0) (p 1) (p 2) (fun q => by linarith [ht q])
  have h02 := between S c hc hlin o (p 0) (p 2) (p 1) (fun q => by linarith [ht q])
  have h10 := between S c hc hlin o (p 1) (p 0) (p 2) (fun q => by linarith [ht q])
  have h12 := between S c hc hlin o (p 1) (p 2) (p 0) (fun q => by linarith [ht q])
  have h20 := between S c hc hlin o (p 2) (p 0) (p 1) (fun q => by linarith [ht q])
  have h21 := between S c hc hlin o (p 2) (p 1) (p 0) (fun q => by linarith [ht q])
  fin_cases i <;> fin_cases j <;> first
    | exact (hij rfl).elim
    | exact h01 | exact h02 | exact h10 | exact h12 | exact h20 | exact h21

end OM.NNN32
