import Lib.OM.NNN32.FourSupport
import Lib.OM.NNN32.InitialPrices
import Lib.OM.NNN30.Net.Tower
import Lib.OM.NNN30.RectMain

/-! # A midpoint space with four exact terminal prices -/

noncomputable section
open scoped Classical

namespace OM.NNN32.FourNetwork

open OM.NNN30 OM.NNN30.Net OM.NNN30.Geom Semicontinuity AsymptoticSpectrumDuality

private lemma extend_prices {V : Type} [Fintype V] [LinearOrder V]
    {φ : AsymptoticSpectrum fourPreorder} {τ : Fin 4 → V} {d : V → V → ℝ}
    (hd : Minimal φ τ d) : ∃ D, Minimal φ (fun i => (τ i,τ i)) D ∧
      (∀ a b c, D (a,b) (c,b) ≤ d a c/2) ∧ (∀ a b e, D (a,b) (a,e) ≤ d b e/2) ∧
      (∀ a b c e, D (a,b) (c,e)^2 + D (a,e) (c,b)^2 ≤ (d a c^2 + d b e^2)/2) ∧
      (∀ a c, D (a,a) (c,c) = d a c) := by
  obtain ⟨lam,hl,hv⟩ := disc_prices proof_R108_3 hd.1
  obtain ⟨D,hD,hle⟩ := exists_minimal hv (Dlam_nonneg hd.2.1 hl) (Dlam_diag_zero hd.2.2.1 _)
  obtain ⟨hr,hc,hq,hi⟩ := rectangle_geometry hd.symm hd.2.1 hd.2.2.1 hl hD.2.1 hle
  refine ⟨D,hD,hr,hc,hq,?_⟩
  have ha : Valid φ τ (fun s t => D (s,s) (t,t)) := by
    intro f N hN hp
    exact hD.1 (N.relocate fun s => (s,s)) (hN.relocate _) hp
  have he := hd.2.2.2 _ ha (fun a c => hD.2.1 _ _) (fun a => hD.2.2.1 _) hi
  exact fun a c => congrFun (congrFun he a) c

def site : ∀ k : ℕ, Fin 4 → Lv k
  | 0 => id
  | k+1 => fun i => (site k i,site k i)

def level (φ : AsymptoticSpectrum fourPreorder) :
    (k : ℕ) → {d : Lv k → Lv k → ℝ // Minimal φ (site k) d}
  | 0 => ⟨wirePrice φ,initial_minimal φ⟩
  | k+1 => ⟨(extend_prices (level φ k).2).choose,(extend_prices (level φ k).2).choose_spec.1⟩

def prices (φ : AsymptoticSpectrum fourPreorder) : PriceTower where
  d k := (level φ k).1
  nonneg k := (level φ k).2.2.1
  self k := (level φ k).2.2.2.1
  symm k := (level φ k).2.symm
  triangle k := (level φ k).2.triangle
  step k := by
    obtain ⟨_,hr,hc,hq,hi⟩ := (extend_prices (level φ k).2).choose_spec
    exact ⟨hr,hc,hq,hi⟩

def space (φ : AsymptoticSpectrum fourPreorder) : MidSpace Tm :=
  let P := prices φ
  ⟨P.dX,Tm.node,P.dX_self,P.dX_symm,P.dX_tri,P.dX_node_row,P.dX_node_col,P.dX_node_self,P.dX_quad⟩

theorem terminal_value (φ : AsymptoticSpectrum fourPreorder) (D : ℕ+) (i j : Fin 4) (hij : i ≠ j) :
    fourValue φ (unitPairTensor (F := ℂ) D i j hij) =
      ((D:ℕ):ℝ)^(space φ).d (.leaf i) (.leaf j) := eval_wire φ D i j hij

/-- All eight sites occurring in the factorization test evaluate in a common finite level. -/
theorem twoTerm_of_levels {φ : AsymptoticSpectrum fourPreorder} {κ : ℝ}
    (h : ∀ k, twoTermBound (level φ k).1 κ) : twoTermBound (space φ).d κ := by
  intro t ht u v w x
  let K := max ((Finset.univ : Finset (Fin 4)).sup fun i => (t i).depth)
    (max (max u.depth v.depth) (max w.depth x.depth))
  have hterm (i : Fin 4) : (t i).depth ≤ K :=
    (Finset.le_sup (f := fun i => (t i).depth) (Finset.mem_univ i)).trans (le_max_left _ _)
  have hu : u.depth ≤ K := by dsimp [K]; omega
  have hv : v.depth ≤ K := by dsimp [K]; omega
  have hw : w.depth ≤ K := by dsimp [K]; omega
  have hx : x.depth ≤ K := by dsimp [K]; omega
  have eqn (a b : Tm) (ha : a.depth ≤ K) (hb : b.depth ≤ K) :
      (level φ K).1 (ev K a) (ev K b) = (space φ).d a b := (prices φ).dX_eq a b K (max_le ha hb)
  have q := h K (fun i => ev K (t i)) (fun i j hij => by rw [eqn _ _ (hterm i) (hterm j)]; exact ht i j hij)
    (ev K u) (ev K v) (ev K w) (ev K x)
  simpa only [eqn _ _ (hterm _) (hterm _),eqn _ _ (hterm _) hu,eqn _ _ (hterm _) hv,
    eqn _ _ (hterm _) hw,eqn _ _ (hterm _) hx,eqn _ _ hu hv,eqn _ _ hw hx] using q

end OM.NNN32.FourNetwork
