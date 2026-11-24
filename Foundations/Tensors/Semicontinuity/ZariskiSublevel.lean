/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Foundations.Tensors.Semicontinuity.Defs
import Foundations.Tensors.Semicontinuity.MaxRankBound
import Foundations.Tensors.Semicontinuity.TensorRank
import Mathlib.Data.Fin.Tuple.Sort

/-!
# §2.2 Zariski-closed sublevel sets + §2.3 well-ordering for asymptotic rank

Source: Christandl, Hoeberechts, Nieuwboer, Vrana and Zuiddam,
“Asymptotic tensor rank is characterized by polynomials” (arXiv:2411.15789v2).

* `regularize_zariski_closure_eq` — **Theorem 2.2**.
* `power_subset_span_closure` — **Lemma 2.3**.
* `sublevel_zariski_closed` — **Corollary 2.4**.
* `wellOrdered_values_per_format` — **Corollary 2.5**.
* `wellOrdered_asympRank_alltensors` — **Corollary 2.6**.
-/

namespace Semicontinuity

open scoped TensorProduct
open PiTensorProduct

universe u v

variable {F : Type u} [Field F]
variable {V : Type v} [AddCommGroup V] [Module F V] [Module.Finite F V]

/-! ## Polynomial-pullback lemma

The key technical input for Lemma 2.3: pulling back any linear form on `V^⊗n`
through `tensorPow n` produces a polynomial function on `V`. Explicitly, with
basis `b` of `V`, writing `T = ∑ c_i b_i` and expanding,
`ℓ(T^⊗n) = ∑_I (∏_k c_{I k}) · ℓ(b_{I 0} ⊗ ⋯ ⊗ b_{I n-1})`,
a polynomial of total degree `n` in the coordinates `c_i`.
-/

/-- For any linear form `ℓ : V^⊗n →ₗ[F] F`, the function `T ↦ ℓ (T^⊗n)` is
    a polynomial function on `V`. -/
lemma isPolynomialFunction_linMap_tensorPow
    (n : ℕ+) (ℓ : TensorPower F (n : ℕ) V →ₗ[F] F) :
    IsPolynomialFunction (F := F) (V := V) (fun T : V => ℓ (tensorPow n T)) := by
  classical
  set d := Module.finrank F V
  set b := Module.finBasis F V
  -- Witness polynomial: monomial coefficient at `X_{I 0} ⋯ X_{I (n-1)}` is
  -- `ℓ(b_{I 0} ⊗ ⋯ ⊗ b_{I (n-1)})`.
  refine ⟨∑ I : Fin (n : ℕ) → Fin d,
            MvPolynomial.C
              (ℓ (PiTensorProduct.tprod F (fun k : Fin (n : ℕ) => b (I k)))) *
              ∏ k : Fin (n : ℕ), MvPolynomial.X (I k), ?_⟩
  intro T
  have hT : T = ∑ i, (b.repr T i) • b i := (b.sum_repr T).symm
  have hTPow :
      tensorPow (F := F) (V := V) n T =
        ∑ I : Fin (n : ℕ) → Fin d,
          (∏ k, b.repr T (I k)) •
            PiTensorProduct.tprod F (fun k : Fin (n : ℕ) => b (I k)) := by
    unfold tensorPow
    conv_lhs =>
      rw [show (fun _ : Fin (n : ℕ) => T) =
        (fun _ : Fin (n : ℕ) => ∑ i, (b.repr T i) • b i) from by funext; exact hT]
    rw [MultilinearMap.map_sum (PiTensorProduct.tprod F (s := fun _ : Fin (n : ℕ) => V))]
    refine Finset.sum_congr rfl (fun I _ => ?_)
    exact MultilinearMap.map_smul_univ
        (PiTensorProduct.tprod F (s := fun _ : Fin (n : ℕ) => V))
        (fun k : Fin (n : ℕ) => b.repr T (I k)) (fun k : Fin (n : ℕ) => b (I k))
  change ℓ (tensorPow n T) = _
  rw [hTPow, map_sum, map_sum]
  refine Finset.sum_congr rfl (fun I _ => ?_)
  rw [LinearMap.map_smul, smul_eq_mul, map_mul, MvPolynomial.eval_C, map_prod]
  simp_rw [MvPolynomial.eval_X]
  ring

/-! ## A ⊆ Z̄(A), boundedness of `F̃`, and monotonicity of `asympOnSet`. -/

/-- Every set is contained in its Zariski closure (a polynomial vanishing on `A`
    in particular vanishes at each `T ∈ A`). -/
lemma subset_zariskiClosure (A : Set V) :
    A ⊆ zariskiClosure (F := F) A := by
  intro T hTA f _ hfA
  exact hfA T hTA

/-- `F̃(T) ≤ F_1(T^⊗1)`: the infimum is at most its `n = 1` member. -/
lemma regularize_le_F1 (Func : AdmissibleFunctional F V) (T : V) :
    Func.regularize T ≤ ((Func.toFun 1 (tensorPow 1 T)) : ℝ) := by
  unfold AdmissibleFunctional.regularize
  have h_at_one : ((Func.toFun 1 (tensorPow (F := F) (V := V) 1 T)) : ℝ) ^
                    ((1 : ℝ) / ((1 : ℕ+) : ℕ)) =
                  ((Func.toFun 1 (tensorPow (F := F) (V := V) 1 T)) : ℝ) := by
    simp
  have h_bdd : BddBelow (Set.range fun n : ℕ+ =>
      ((Func.toFun n (tensorPow (F := F) (V := V) n T)) : ℝ) ^ ((1 : ℝ) / (n : ℕ))) := by
    refine ⟨0, ?_⟩
    rintro x ⟨n, rfl⟩
    exact Real.rpow_nonneg (NNReal.coe_nonneg _) _
  calc (⨅ n : ℕ+, ((Func.toFun n (tensorPow (F := F) (V := V) n T)) : ℝ) ^
          ((1 : ℝ) / (n : ℕ)))
      ≤ ((Func.toFun (1 : ℕ+) (tensorPow 1 T)) : ℝ) ^ ((1 : ℝ) / ((1 : ℕ+) : ℕ)) :=
        ciInf_le h_bdd (1 : ℕ+)
    _ = ((Func.toFun 1 (tensorPow 1 T)) : ℝ) := h_at_one

/-- `F̃` is bounded above by the `F₁`-bound `c` of the admissible functional. -/
lemma regularize_bounded (Func : AdmissibleFunctional F V) :
    ∃ c : ℝ, ∀ T : V, Func.regularize T ≤ c := by
  obtain ⟨c, hc⟩ := Func.bdd_one
  refine ⟨c, fun T => ?_⟩
  calc Func.regularize T
      ≤ ((Func.toFun 1 (tensorPow 1 T)) : ℝ) := regularize_le_F1 Func T
    _ ≤ (c : ℝ) := NNReal.coe_le_coe.mpr (hc _)

/-! ## A.3.5 — iterated submultiplicativity gives `F(S^⊗ℓ) ≤ B^ℓ`. -/

/-- Helper: `(tensorPowerAdd F V ℓ.val 1).symm (tensorPow ℓ T ⊗ₜ tensorPow 1 T) = tensorPow (ℓ+1) T`.

    Uses `TensorPower.tprod_mul_tprod` and the fact that `Fin.append` of two constant
    functions is the corresponding constant function on `Fin (ℓ + 1)`. -/
lemma tensorPowerAdd_symm_tensorPow (T : V) (ℓ : ℕ+) :
    (tensorPowerAdd F V (ℓ : ℕ) ((1 : ℕ+) : ℕ)).symm
        (tensorPow (F := F) (V := V) ℓ T ⊗ₜ tensorPow (1 : ℕ+) T) =
      tensorPow (F := F) (V := V) (ℓ + 1) T := by
  unfold tensorPowerAdd tensorPow
  show TensorPower.mulEquiv ((PiTensorProduct.tprod F fun _ : Fin (ℓ : ℕ) => T) ⊗ₜ[F]
    PiTensorProduct.tprod F fun _ : Fin (((1 : ℕ+) : ℕ)) => T) = _
  rw [show TensorPower.mulEquiv
    ((PiTensorProduct.tprod F fun _ : Fin (ℓ : ℕ) => T) ⊗ₜ[F]
      PiTensorProduct.tprod F fun _ : Fin ((1 : ℕ+) : ℕ) => T) =
    PiTensorProduct.tprod F
      (Fin.append (fun _ : Fin (ℓ : ℕ) => T) (fun _ : Fin ((1 : ℕ+) : ℕ) => T)) from
      TensorPower.tprod_mul_tprod F _ _]
  have heq : Fin.append (fun _ : Fin (ℓ : ℕ) => T) (fun _ : Fin ((1 : ℕ+) : ℕ) => T) =
      fun _ : Fin ((ℓ : ℕ) + ((1 : ℕ+) : ℕ)) => T := by
    funext i
    refine Fin.addCases (fun _ => ?_) (fun _ => ?_) i
    · simp [Fin.append, Fin.addCases]
    · simp [Fin.append, Fin.addCases]
  rw [heq]
  congr 1

/-- General `(k + l)` version of `tensorPowerAdd_symm_tensorPow`:
    `(tensorPowerAdd F V k l).symm (tensorPow k T ⊗ₜ tensorPow l T) = tensorPow (k+l) T`.

    Same proof as `tensorPowerAdd_symm_tensorPow` but with an arbitrary second
    exponent `l : ℕ+` instead of `1`. Used to express submultiplicativity of
    `F` along powers of a single tensor (Fekete subadditivity input, Definition 2.1). -/
lemma tensorPowerAdd_symm_tensorPow_add (T : V) (k l : ℕ+) :
    (tensorPowerAdd F V (k : ℕ) (l : ℕ)).symm
        (tensorPow (F := F) (V := V) k T ⊗ₜ tensorPow l T) =
      tensorPow (F := F) (V := V) (k + l) T := by
  unfold tensorPowerAdd tensorPow
  show TensorPower.mulEquiv ((PiTensorProduct.tprod F fun _ : Fin (k : ℕ) => T) ⊗ₜ[F]
    PiTensorProduct.tprod F fun _ : Fin (l : ℕ) => T) = _
  rw [show TensorPower.mulEquiv
    ((PiTensorProduct.tprod F fun _ : Fin (k : ℕ) => T) ⊗ₜ[F]
      PiTensorProduct.tprod F fun _ : Fin (l : ℕ) => T) =
    PiTensorProduct.tprod F
      (Fin.append (fun _ : Fin (k : ℕ) => T) (fun _ : Fin (l : ℕ) => T)) from
      TensorPower.tprod_mul_tprod F _ _]
  have heq : Fin.append (fun _ : Fin (k : ℕ) => T) (fun _ : Fin (l : ℕ) => T) =
      fun _ : Fin ((k : ℕ) + (l : ℕ)) => T := by
    funext i
    refine Fin.addCases (fun _ => ?_) (fun _ => ?_) i
    · simp [Fin.append, Fin.addCases]
    · simp [Fin.append, Fin.addCases]
  rw [heq]
  congr 1

/-- Submultiplicativity of `F` along powers of a single tensor:
    `F_{k+l}(S^⊗(k+l)) ≤ F_k(S^⊗k) · F_l(S^⊗l)`.

    Direct consequence of `Func.submul` + `tensorPowerAdd_symm_tensorPow_add`.
    This is the subadditivity input feeding Fekete's lemma (Definition 2.1). -/
lemma toFun_tensorPow_add_le (Func : AdmissibleFunctional F V) (S : V) (k l : ℕ+) :
    Func.toFun (k + l) (tensorPow (k + l) S) ≤
      Func.toFun k (tensorPow k S) * Func.toFun l (tensorPow l S) := by
  have hstep := Func.submul k l (tensorPow k S) (tensorPow l S)
  rw [tensorPowerAdd_symm_tensorPow_add S k l] at hstep
  -- Reconcile the `⟨k+l, _⟩` index of `submul` with `(k + l : ℕ+)`.
  convert! hstep using 2 <;> exact (PNat.add_coe k l).symm

/-- **A.3.5** Iterated submultiplicativity: for `T : V` and `ℓ : ℕ+`,
    `F_ℓ(T^⊗ℓ) ≤ F_1(T^⊗1)^ℓ`. -/
lemma toFun_tensorPow_le_F1_pow (Func : AdmissibleFunctional F V) (T : V) (ℓ : ℕ+) :
    Func.toFun ℓ (tensorPow ℓ T) ≤ (Func.toFun 1 (tensorPow 1 T)) ^ (ℓ : ℕ) := by
  induction ℓ using PNat.recOn with
  | one => simp
  | succ ℓ ih =>
    -- Goal: F_{ℓ+1}(tensorPow (ℓ+1) T) ≤ F_1(tensorPow 1 T)^((ℓ+1) : ℕ)
    -- Use submul + tensorPowerAdd_symm_tensorPow + ih.
    have hstep := Func.submul ℓ 1 (tensorPow ℓ T) (tensorPow 1 T)
    rw [tensorPowerAdd_symm_tensorPow T ℓ] at hstep
    -- hstep : F_{ℓ+1}(tensorPow (ℓ+1) T) ≤ F_ℓ(tensorPow ℓ T) * F_1(tensorPow 1 T)
    calc Func.toFun (ℓ + 1) (tensorPow (ℓ + 1) T)
        ≤ Func.toFun ℓ (tensorPow ℓ T) * Func.toFun 1 (tensorPow 1 T) := by
          convert! hstep using 2 <;> exact (PNat.add_coe ℓ 1).symm
      _ ≤ (Func.toFun 1 (tensorPow 1 T)) ^ (ℓ : ℕ) * Func.toFun 1 (tensorPow 1 T) :=
          mul_le_mul_left ih _
      _ = (Func.toFun 1 (tensorPow 1 T)) ^ ((ℓ + 1 : ℕ+) : ℕ) := by
          rw [PNat.add_coe]
          rw [show ((ℓ : ℕ) + ((1 : ℕ+) : ℕ)) = (ℓ : ℕ) + 1 from rfl, pow_succ]

/-- **A.3.5 (corollary)** Combined with `bdd_one`, gives `F(S^⊗ℓ) ≤ B^ℓ`. -/
lemma toFun_tensorPow_le_bdd_pow (Func : AdmissibleFunctional F V) (T : V) (ℓ : ℕ+)
    (B : NNReal) (hB : ∀ U : TensorPower F 1 V, Func.toFun 1 U ≤ B) :
    Func.toFun ℓ (tensorPow ℓ T) ≤ B ^ (ℓ : ℕ) :=
  (toFun_tensorPow_le_F1_pow Func T ℓ).trans (pow_le_pow_left' (hB _) _)

/-! ## A.3.6 — `p(n)^(1/n) → 1` for polynomial growth.

The paper (Theorem 2.2) uses the bound
`p(n) ≤ dim Sym^n V = binom(dim V + n - 1, n)`,
which grows polynomially in `n` of degree `dim V - 1`. The standard
"polynomial^(1/n) → 1" argument then gives `p(n)^(1/n) → 1`. -/

omit [Module.Finite F V] in
/-- Helper: for `d ≥ 1` and `n ≥ 1`,
    `Nat.choose (d + n - 1) n ≤ (d + n - 1)^(d - 1)`.

    Proof: by the symmetry `choose (a + b) a = choose (a + b) b` with
    `a = d - 1` and `b = n`, we have
    `choose (d + n - 1) n = choose (d + n - 1) (d - 1) ≤ (d + n - 1)^(d - 1)`
    using `Nat.choose_le_pow`. -/
lemma choose_add_sub_one_le_pow {d : ℕ} (hd : 0 < d) (n : ℕ) :
    Nat.choose (d + n - 1) n ≤ (d + n - 1) ^ (d - 1) := by
  -- d + n - 1 = (d - 1) + n since 0 < d.
  have hsum : d + n - 1 = (d - 1) + n := by omega
  -- choose (d + n - 1) n = choose (d + n - 1) (d - 1).
  have hsymm : Nat.choose (d + n - 1) n = Nat.choose (d + n - 1) (d - 1) := by
    apply Nat.choose_symm_of_eq_add
    omega
  rw [hsymm]
  exact Nat.choose_le_pow _ _

omit [Module.Finite F V] in
/-- Helper: `Real.log m / n → 0` as `n → ∞`, when `m n = d + n - 1` in `ℕ` and `0 < d`.

    Argument: as `n → ∞`, `m_n := d + n - 1 → ∞`, so `log m_n / m_n → 0`
    by `Real.isLittleO_log_id_atTop`. Also `m_n / n → 1`. Hence
    `log m_n / n = (log m_n / m_n) · (m_n / n) → 0 · 1 = 0`. -/
lemma tendsto_log_natCast_add_sub_one_div_atTop_nhds_zero {d : ℕ} (hd : 0 < d) :
    Filter.Tendsto (fun n : ℕ => Real.log ((d + n - 1 : ℕ) : ℝ) / n) Filter.atTop (nhds 0) := by
  -- Set d' = d - 1; then for n ≥ 1, (d + n - 1 : ℕ) = d' + n.
  set d' : ℕ := d - 1 with hd'def
  -- Step 1: log((d' + n : ℕ) : ℝ) / ((d' + n : ℕ) : ℝ) → 0.
  have hLog : Filter.Tendsto (fun n : ℕ => Real.log ((d' + n : ℕ) : ℝ) / ((d' + n : ℕ) : ℝ))
      Filter.atTop (nhds 0) := by
    have h1 := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
    have h2 : Filter.Tendsto (fun n : ℕ => ((d' + n : ℕ) : ℝ)) Filter.atTop Filter.atTop := by
      have : Filter.Tendsto (fun n : ℕ => (d' + n : ℕ)) Filter.atTop Filter.atTop :=
        Filter.tendsto_atTop_atTop.mpr fun b => ⟨b, fun n hn => by omega⟩
      exact tendsto_natCast_atTop_atTop.comp this
    exact h1.comp h2
  -- Step 2: ((d' + n : ℕ) : ℝ) / (n : ℝ) → 1 (eventually).
  have hRatio : Filter.Tendsto (fun n : ℕ => ((d' + n : ℕ) : ℝ) / (n : ℝ))
      Filter.atTop (nhds 1) := by
    -- Eventually equals d'/n + 1; d'/n → 0.
    have hInv : Filter.Tendsto (fun n : ℕ => (d' : ℝ) / (n : ℝ)) Filter.atTop (nhds 0) := by
      have hN : Filter.Tendsto (fun n : ℕ => (n : ℝ)) Filter.atTop Filter.atTop :=
        tendsto_natCast_atTop_atTop
      have hInvN : Filter.Tendsto (fun n : ℕ => ((n : ℝ))⁻¹) Filter.atTop (nhds 0) :=
        hN.inv_tendsto_atTop
      have := (tendsto_const_nhds (x := (d' : ℝ))).mul hInvN
      simp only [mul_zero] at this
      refine this.congr' ?_
      filter_upwards [Filter.eventually_gt_atTop 0] with n hn
      have hnne : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
      field_simp
    have hSum : Filter.Tendsto (fun n : ℕ => (d' : ℝ) / (n : ℝ) + 1) Filter.atTop (nhds (0 + 1)) :=
      hInv.add_const 1
    simp only [zero_add] at hSum
    refine hSum.congr' ?_
    filter_upwards [Filter.eventually_gt_atTop 0] with n hn
    have hnne : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    push_cast
    field_simp
  -- Step 3: product → 0 · 1 = 0.
  have hprod := hLog.mul hRatio
  simp only [zero_mul] at hprod
  -- Step 4: simplify product to log((d' + n : ℕ) : ℝ) / n.
  have hprod' : Filter.Tendsto (fun n : ℕ => Real.log ((d' + n : ℕ) : ℝ) / (n : ℝ))
      Filter.atTop (nhds 0) := by
    refine hprod.congr' ?_
    filter_upwards [Filter.eventually_gt_atTop 0] with n hn
    have hnne : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    -- For 0 < d and n ≥ 1, ((d' + n : ℕ) : ℝ) ≥ 1 > 0.
    have hdn_pos : 0 < d' + n := by
      have : 0 < n := hn
      omega
    have hdn_ne : ((d' + n : ℕ) : ℝ) ≠ 0 := by
      have : (0 : ℝ) < ((d' + n : ℕ) : ℝ) := by exact_mod_cast hdn_pos
      linarith
    field_simp
  -- Step 5: rewrite (d + n - 1 : ℕ) = d' + n eventually.
  refine hprod'.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  have heq : d + n - 1 = d' + n := by omega
  rw [heq]

omit [Module.Finite F V] in
/-- **A.3.6 (positive case)** For `d ≥ 1`,
    `(binom(d + n - 1, n))^(1/n) → 1` as `n → ∞`.

    Squeeze: `1 ≤ binom(d+n-1, n) ≤ (d+n-1)^(d-1)`, both raised to `1/n`. -/
lemma binomial_pow_root_tendsto_one_pos {d : ℕ} (hd : 0 < d) :
    Filter.Tendsto (fun n : ℕ => (Nat.choose (d + n - 1) n : ℝ) ^ ((1 : ℝ) / n))
      Filter.atTop (nhds 1) := by
  -- The lower envelope is 1, upper envelope is (d+n-1 : ℝ)^((d-1)/n).
  -- Both tend to 1, so squeeze.
  -- Upper envelope: U n := ((d + n - 1 : ℝ))^((d - 1 : ℝ)/n).
  -- Lower envelope: constant 1.
  have hConstOne : Filter.Tendsto (fun _ : ℕ => (1 : ℝ)) Filter.atTop (nhds 1) :=
    tendsto_const_nhds
  -- Step 1: lower bound 1 ≤ choose^(1/n) for n ≥ 1.
  have hLower : ∀ᶠ n : ℕ in Filter.atTop,
      (1 : ℝ) ≤ (Nat.choose (d + n - 1) n : ℝ) ^ ((1 : ℝ) / n) := by
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    -- choose (d+n-1) n ≥ 1 since n ≤ d + n - 1 (as 0 < d).
    have hchoose_pos : 0 < Nat.choose (d + n - 1) n := by
      apply Nat.choose_pos
      omega
    have hchoose_ge_one : (1 : ℝ) ≤ (Nat.choose (d + n - 1) n : ℝ) := by
      exact_mod_cast hchoose_pos
    have hone_div_nonneg : (0 : ℝ) ≤ (1 : ℝ) / n := by
      have : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
      positivity
    calc (1 : ℝ) = (1 : ℝ) ^ ((1 : ℝ) / n) := by rw [Real.one_rpow]
      _ ≤ (Nat.choose (d + n - 1) n : ℝ) ^ ((1 : ℝ) / n) :=
            Real.rpow_le_rpow (by norm_num) hchoose_ge_one hone_div_nonneg
  -- Step 2: upper bound choose^(1/n) ≤ ((d+n-1 : ℕ) : ℝ)^((d-1)/n) for n ≥ 1.
  have hUpper : ∀ᶠ n : ℕ in Filter.atTop,
      (Nat.choose (d + n - 1) n : ℝ) ^ ((1 : ℝ) / n) ≤
        ((d + n - 1 : ℕ) : ℝ) ^ (((d : ℝ) - 1) / n) := by
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    -- choose (d+n-1) n ≤ (d+n-1)^(d-1).
    have h1 : Nat.choose (d + n - 1) n ≤ (d + n - 1) ^ (d - 1) :=
      choose_add_sub_one_le_pow hd n
    have h1R : (Nat.choose (d + n - 1) n : ℝ) ≤ ((d + n - 1 : ℕ) : ℝ) ^ (d - 1 : ℕ) := by
      have := (Nat.cast_le (α := ℝ)).mpr h1
      simpa [Nat.cast_pow] using! this
    have hone_div_nonneg : (0 : ℝ) ≤ (1 : ℝ) / n := by
      have : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
      positivity
    have hchoose_nn : (0 : ℝ) ≤ (Nat.choose (d + n - 1) n : ℝ) := by
      exact_mod_cast Nat.zero_le _
    have hbase_nn : (0 : ℝ) ≤ ((d + n - 1 : ℕ) : ℝ) := by exact_mod_cast Nat.zero_le _
    -- Convert to rpow then change exponent.
    have hstep1 : (Nat.choose (d + n - 1) n : ℝ) ^ ((1 : ℝ) / n) ≤
        (((d + n - 1 : ℕ) : ℝ) ^ (d - 1 : ℕ)) ^ ((1 : ℝ) / n) :=
      Real.rpow_le_rpow hchoose_nn h1R hone_div_nonneg
    have hstep2 : (((d + n - 1 : ℕ) : ℝ) ^ (d - 1 : ℕ)) ^ ((1 : ℝ) / n) =
        ((d + n - 1 : ℕ) : ℝ) ^ (((d - 1 : ℕ) : ℝ) * ((1 : ℝ) / n)) := by
      rw [← Real.rpow_natCast (((d + n - 1 : ℕ) : ℝ)) (d - 1),
          ← Real.rpow_mul hbase_nn]
    have hstep3 : ((d - 1 : ℕ) : ℝ) * ((1 : ℝ) / n) = ((d : ℝ) - 1) / n := by
      have hd_cast : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by
        have hd' : (d - 1 : ℕ) + 1 = d := by omega
        have : (((d - 1 : ℕ) + 1 : ℕ) : ℝ) = (d : ℝ) := by exact_mod_cast hd'
        push_cast at this
        linarith
      rw [hd_cast]
      ring
    calc (Nat.choose (d + n - 1) n : ℝ) ^ ((1 : ℝ) / n)
        ≤ (((d + n - 1 : ℕ) : ℝ) ^ (d - 1 : ℕ)) ^ ((1 : ℝ) / n) := hstep1
      _ = ((d + n - 1 : ℕ) : ℝ) ^ (((d - 1 : ℕ) : ℝ) * ((1 : ℝ) / n)) := hstep2
      _ = ((d + n - 1 : ℕ) : ℝ) ^ (((d : ℝ) - 1) / n) := by rw [hstep3]
  -- Step 3: ((d+n-1 : ℕ) : ℝ)^((d-1)/n) → 1.
  have hUtendsto : Filter.Tendsto
      (fun n : ℕ => ((d + n - 1 : ℕ) : ℝ) ^ (((d : ℝ) - 1) / n))
      Filter.atTop (nhds 1) := by
    -- Rewrite eventually as exp(((d-1)/n) · log((d+n-1 : ℕ) : ℝ)), exponent → 0.
    have hExpZero : Real.exp 0 = 1 := Real.exp_zero
    have hexp_form : ∀ᶠ n : ℕ in Filter.atTop,
        ((d + n - 1 : ℕ) : ℝ) ^ (((d : ℝ) - 1) / n) =
          Real.exp ((((d : ℝ) - 1) / n) * Real.log ((d + n - 1 : ℕ) : ℝ)) := by
      filter_upwards [Filter.eventually_ge_atTop 1] with n hn
      have hpos : (0 : ℝ) < ((d + n - 1 : ℕ) : ℝ) := by
        have hpos' : 0 < d + n - 1 := by omega
        exact_mod_cast hpos'
      rw [Real.rpow_def_of_pos hpos]
      ring_nf
    -- Exponent → 0.
    have hexpzero : Filter.Tendsto
        (fun n : ℕ => (((d : ℝ) - 1) / n) * Real.log ((d + n - 1 : ℕ) : ℝ))
        Filter.atTop (nhds 0) := by
      have hLogDiv : Filter.Tendsto (fun n : ℕ => Real.log ((d + n - 1 : ℕ) : ℝ) / n)
          Filter.atTop (nhds 0) :=
        tendsto_log_natCast_add_sub_one_div_atTop_nhds_zero hd
      have hMul : Filter.Tendsto
          (fun n : ℕ => ((d : ℝ) - 1) * (Real.log ((d + n - 1 : ℕ) : ℝ) / n))
          Filter.atTop (nhds (((d : ℝ) - 1) * 0)) :=
        hLogDiv.const_mul _
      simp only [mul_zero] at hMul
      refine hMul.congr' ?_
      filter_upwards [Filter.eventually_gt_atTop 0] with n hn
      have hnp : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
      field_simp
    have hExpTendsto : Filter.Tendsto
        (fun n : ℕ => Real.exp ((((d : ℝ) - 1) / n) * Real.log ((d + n - 1 : ℕ) : ℝ)))
        Filter.atTop (nhds 1) := by
      have := hexpzero.rexp
      simpa [hExpZero] using! this
    refine hExpTendsto.congr' ?_
    filter_upwards [hexp_form] with n hn
    exact hn.symm
  -- Apply squeeze.
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hConstOne hUtendsto hLower hUpper

/-! NOTE: A `d`-unconstrained version `binomial_pow_root_tendsto_one (d : ℕ)`
    would be FALSE for `d = 0` (the values `Nat.choose (n - 1) n` are zero for
    `n ≥ 1`, so the sequence is constantly zero, not tending to 1). The
    load-bearing version with the required `0 < d` hypothesis is
    `binomial_pow_root_tendsto_one_pos` above, used in
    `regularize_le_asymp_plus_eps`. We do not export a `d = 0` variant. -/

/-! ## A.3.4 — `regularize_approximation`: F̃(S) is approximated by `F(S^⊗ℓ)^(1/ℓ)`. -/

/-- **A.3.4** For every `ε > 0`, there exists `M : ℕ+` such that for all `ℓ ≥ M`,
    `F(S^⊗ℓ)^(1/ℓ) ≤ F̃(S) + ε`.

    Direct from `Func.regularize S = ⨅ n, F(S^⊗n)^(1/n)` and the fact that an
    infimum is approximated by some witness from below. -/
lemma regularize_approximation
    (Func : AdmissibleFunctional F V) (S : V) (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℕ+, ((Func.toFun M (tensorPow M S)) : ℝ) ^ ((1 : ℝ) / (M : ℕ)) ≤
      Func.regularize S + ε := by
  -- regularize S = ⨅ n, value(n). Pick n witnessing closeness to inf.
  -- `ciInf_lt_iff` gives: inf < a ⟺ ∃ n, value(n) < a.
  -- We use `regularize S < regularize S + ε`, so ∃ n with value(n) < regularize S + ε.
  have h_bdd : BddBelow (Set.range fun n : ℕ+ =>
      ((Func.toFun n (tensorPow (F := F) (V := V) n S)) : ℝ) ^ ((1 : ℝ) / (n : ℕ))) := by
    refine ⟨0, ?_⟩
    rintro x ⟨n, rfl⟩
    exact Real.rpow_nonneg (NNReal.coe_nonneg _) _
  have h_lt : Func.regularize S < Func.regularize S + ε := by linarith
  rw [show Func.regularize S = ⨅ n : ℕ+, ((Func.toFun n (tensorPow n S)) : ℝ) ^
       ((1 : ℝ) / (n : ℕ)) from rfl] at h_lt
  obtain ⟨M, hM⟩ := exists_lt_of_ciInf_lt h_lt
  refine ⟨M, hM.le⟩

/-- `F̃` is nonnegative (inf of nonneg rpow values is nonneg). -/
lemma regularize_nonneg (Func : AdmissibleFunctional F V) (T : V) :
    0 ≤ Func.regularize T := by
  unfold AdmissibleFunctional.regularize
  refine Real.iInf_nonneg fun n => ?_
  exact Real.rpow_nonneg (NNReal.coe_nonneg _) _

/-- **A.3.4 (uniform strengthening)** Fekete strengthening of
    `regularize_approximation` (Theorem 2.2, used implicitly there):

    "For every `ε > 0`, there is an `M(ε)` such that for every `ℓ ≥ M(ε)`,
    `F(S^⊗ℓ)^(1/ℓ) ≤ F̃(S) + ε`."

    Since `regularize S = ⨅ n, F(S^⊗n)^(1/n)` and `log F(S^⊗·)` is subadditive
    by `toFun_tensorPow_add_le`, Fekete's lemma
    (`Subadditive.eventually_div_lt_of_div_lt`) upgrades the single-witness
    `regularize_approximation` to a uniform "for all large `ℓ`" bound. -/
lemma regularize_approximation_uniform
    (Func : AdmissibleFunctional F V) (S : V) (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℕ+, ∀ ℓ : ℕ+, M ≤ ℓ →
      ((Func.toFun ℓ (tensorPow ℓ S)) : ℝ) ^ ((1 : ℝ) / (ℓ : ℕ)) ≤
        Func.regularize S + ε := by
  classical
  -- Abbreviation for the rooted value at index `k : ℕ+`.
  set val : ℕ+ → ℝ := fun k =>
    ((Func.toFun k (tensorPow (F := F) (V := V) k S)) : ℝ) ^ ((1 : ℝ) / (k : ℕ))
    with hval_def
  have hval_nn : ∀ k : ℕ+, 0 ≤ val k := fun k =>
    Real.rpow_nonneg (NNReal.coe_nonneg _) _
  -- The infimum form of `regularize`.
  have hreg_eq : Func.regularize S = ⨅ k : ℕ+, val k := rfl
  -- Case split: either some power has `F = 0`, or all powers are strictly positive.
  by_cases hzero : ∃ k₀ : ℕ+, Func.toFun k₀ (tensorPow k₀ S) = 0
  · -- Zero case: once `F(S^⊗k₀) = 0`, all larger powers vanish (submultiplicativity),
    -- so `val ℓ = 0 ≤ F̃(S) + ε` for `ℓ ≥ k₀`.
    obtain ⟨k₀, hk₀⟩ := hzero
    refine ⟨k₀, fun ℓ hℓ => ?_⟩
    -- F̃(S) + ε ≥ ε > 0; suffices to show `val ℓ = 0`.
    have hreg_nn : 0 ≤ Func.regularize S := regularize_nonneg Func S
    have hval_zero : val ℓ = 0 := by
      -- Write ℓ = k₀ + j or ℓ = k₀; in all cases F(S^⊗ℓ) = 0.
      have hF_zero : Func.toFun ℓ (tensorPow ℓ S) = 0 := by
        rcases eq_or_lt_of_le hℓ with heq | hlt
        · -- ℓ = k₀
          have hℓk : ℓ = k₀ := heq.symm
          subst hℓk; exact hk₀
        · -- ℓ = k₀ + j for j := ℓ - k₀ ≥ 1
          have hlt_nat : (k₀ : ℕ) < (ℓ : ℕ) := hlt
          have hj_pos : 0 < (ℓ : ℕ) - (k₀ : ℕ) := Nat.sub_pos_of_lt hlt_nat
          set j : ℕ+ := ⟨(ℓ : ℕ) - (k₀ : ℕ), hj_pos⟩ with hj_def
          have hk₀j : k₀ + j = ℓ := by
            apply PNat.coe_injective
            simp only [PNat.add_coe, hj_def, PNat.mk_coe]
            omega
          have hsub := toFun_tensorPow_add_le Func S k₀ j
          rw [hk₀, zero_mul] at hsub
          rw [hk₀j] at hsub
          exact le_antisymm hsub (by positivity)
      simp only [hval_def, hF_zero, NNReal.coe_zero]
      rw [Real.zero_rpow]
      positivity
    calc val ℓ = 0 := hval_zero
      _ ≤ Func.regularize S + ε := by linarith
  · -- Positive case: all `F(S^⊗k) > 0`. Use Fekete on `u k = log (F(S^⊗k))`.
    push_neg at hzero
    have hpos : ∀ k : ℕ+, (0 : ℝ) < (Func.toFun k (tensorPow k S) : ℝ) := by
      intro k
      have : Func.toFun k (tensorPow k S) ≠ 0 := hzero k
      positivity
    -- `u : ℕ → ℝ`, subadditive: `u (a+b) ≤ u a + u b`.
    -- For `k ≥ 1`, `u k = log (F(S^⊗k))`; set `u 0 = 0`.
    set u : ℕ → ℝ := fun k =>
      if hk : 0 < k then Real.log (Func.toFun ⟨k, hk⟩ (tensorPow ⟨k, hk⟩ S) : ℝ) else 0
      with hu_def
    have hu_pnat : ∀ k : ℕ+, u (k : ℕ) =
        Real.log (Func.toFun k (tensorPow k S) : ℝ) := by
      intro k
      simp only [hu_def, dif_pos k.pos]
      congr 1
    have hu_zero : u 0 = 0 := by simp only [hu_def, lt_irrefl, dif_neg, not_false_eq_true]
    have hsubadd : Subadditive u := by
      intro a b
      rcases Nat.eq_zero_or_pos a with ha | ha
      · subst ha; rw [Nat.zero_add, hu_zero, zero_add]
      rcases Nat.eq_zero_or_pos b with hb | hb
      · subst hb; rw [Nat.add_zero, hu_zero, add_zero]
      -- both positive
      have hab : 0 < a + b := by omega
      set aP : ℕ+ := ⟨a, ha⟩ with haP_def
      set bP : ℕ+ := ⟨b, hb⟩ with hbP_def
      set abP : ℕ+ := ⟨a + b, hab⟩ with habP_def
      have hfa := hpos aP
      have hfb := hpos bP
      have hmul := toFun_tensorPow_add_le Func S aP bP
      -- u(a+b) = log F(S^⊗(a+b)) ≤ log (F(S^⊗a)·F(S^⊗b)) = u a + u b
      have hcast : aP + bP = abP := by
        apply PNat.coe_injective
        simp only [PNat.add_coe, haP_def, hbP_def, habP_def, PNat.mk_coe]
      rw [hcast] at hmul
      have hmulR : (Func.toFun abP (tensorPow abP S) : ℝ) ≤
          (Func.toFun aP (tensorPow aP S) : ℝ) *
            (Func.toFun bP (tensorPow bP S) : ℝ) := by
        exact_mod_cast hmul
      have hlog := Real.log_le_log (hpos abP) hmulR
      rw [Real.log_mul (hfa.ne') (hfb.ne')] at hlog
      -- Match indices: u (a+b) with the ⟨a+b, hab⟩ form.
      have hua : u a = Real.log (Func.toFun aP (tensorPow aP S) : ℝ) := by
        simp only [hu_def, dif_pos ha]; rw [← haP_def]
      have hub : u b = Real.log (Func.toFun bP (tensorPow bP S) : ℝ) := by
        simp only [hu_def, dif_pos hb]; rw [← hbP_def]
      have huab : u (a + b) =
          Real.log (Func.toFun abP (tensorPow abP S) : ℝ) := by
        simp only [hu_def, dif_pos hab]; rw [← habP_def]
      rw [hua, hub, huab]
      exact hlog
    -- Pick a witness `n` with `val n < F̃(S) + ε`, i.e. `u n / n < log (F̃(S)+ε)`.
    have hreg_lt : Func.regularize S < Func.regularize S + ε := by linarith
    rw [hreg_eq] at hreg_lt
    have h_bdd : BddBelow (Set.range val) := ⟨0, by rintro x ⟨k, rfl⟩; exact hval_nn k⟩
    obtain ⟨N, hN⟩ := exists_lt_of_ciInf_lt hreg_lt
    -- hN : val N < F̃(S) + ε
    have hreg_eps_pos : 0 < Func.regularize S + ε :=
      lt_of_le_of_lt (regularize_nonneg Func S) (by linarith)
    -- Translate to `u N / N < log (F̃(S)+ε)`.
    set L : ℝ := Real.log (Func.regularize S + ε) with hL_def
    have hdiv_lt : u (N : ℕ) / (N : ℕ) < L := by
      -- u N / N = log (val N), and val N < F̃(S)+ε with both positive.
      have hvalN_pos : 0 < val N := by
        simp only [hval_def]
        exact Real.rpow_pos_of_pos (hpos N) _
      have hlog_valN : Real.log (val N) = u (N : ℕ) / (N : ℕ) := by
        simp only [hval_def, hu_pnat N]
        rw [Real.log_rpow (hpos N)]
        ring
      rw [← hlog_valN, hL_def]
      exact Real.log_lt_log hvalN_pos hN
    -- Fekete: eventually `u p / p < L`.
    have hev := hsubadd.eventually_div_lt_of_div_lt (n := (N : ℕ)) N.pos.ne' hdiv_lt
    -- Convert `∀ᶠ p in atTop, u p / p < L` to `∃ M, ∀ ℓ ≥ M, val ℓ ≤ F̃(S)+ε`.
    rw [Filter.eventually_atTop] at hev
    obtain ⟨M₀, hM₀⟩ := hev
    refine ⟨⟨M₀ + 1, Nat.succ_pos _⟩, fun ℓ hℓ => ?_⟩
    have hℓ_ge : M₀ ≤ (ℓ : ℕ) := by
      have : (⟨M₀ + 1, Nat.succ_pos _⟩ : ℕ+) ≤ ℓ := hℓ
      have hcoe : (M₀ + 1 : ℕ) ≤ (ℓ : ℕ) := this
      omega
    have hdivℓ : u (ℓ : ℕ) / (ℓ : ℕ) < L := hM₀ (ℓ : ℕ) hℓ_ge
    -- u ℓ / ℓ = log (val ℓ) < L = log(F̃(S)+ε), so val ℓ < F̃(S)+ε.
    have hvalℓ_pos : 0 < val ℓ := by
      simp only [hval_def]; exact Real.rpow_pos_of_pos (hpos ℓ) _
    have hlog_valℓ : Real.log (val ℓ) = u (ℓ : ℕ) / (ℓ : ℕ) := by
      simp only [hval_def, hu_pnat ℓ]
      rw [Real.log_rpow (hpos ℓ)]; ring
    have hval_lt : val ℓ < Func.regularize S + ε := by
      have hlog_lt : Real.log (val ℓ) < L := by rw [hlog_valℓ]; exact hdivℓ
      rw [hL_def] at hlog_lt
      exact (Real.log_lt_log_iff hvalℓ_pos hreg_eps_pos).mp hlog_lt
    exact hval_lt.le

/-- `⨆ _ : (T ∈ B), F̃ T` evaluates to `F̃ T` when `T ∈ B` and to `0` when `T ∉ B`,
    matching mathlib's convention `sSup (∅ : Set ℝ) = 0`. -/
lemma iSup_mem_eq (Func : AdmissibleFunctional F V) (T : V) (B : Set V)
    [Decidable (T ∈ B)] :
    (⨆ _ : T ∈ B, Func.regularize T) =
      if T ∈ B then Func.regularize T else 0 := by
  by_cases hT : T ∈ B
  · haveI : Nonempty (T ∈ B) := ⟨hT⟩
    rw [ciSup_const, if_pos hT]
  · haveI : IsEmpty (T ∈ B) := ⟨hT⟩
    change sSup _ = _
    rw [Set.range_eq_empty (fun _ : (T ∈ B) => Func.regularize T), Real.sSup_empty,
      if_neg hT]

/-- `asympOnSet B` is bounded above (by the global `F̃`-bound from `regularize_bounded`). -/
lemma asympOnSet_bddAbove (Func : AdmissibleFunctional F V) (B : Set V) :
    BddAbove (Set.range fun T : V => ⨆ _ : T ∈ B, Func.regularize T) := by
  classical
  obtain ⟨c, hc⟩ := regularize_bounded Func
  refine ⟨max c 0, ?_⟩
  rintro x ⟨T, rfl⟩
  change (⨆ _ : T ∈ B, Func.regularize T) ≤ max c 0
  rw [iSup_mem_eq]
  split_ifs with hT
  · exact (hc T).trans (le_max_left _ _)
  · exact le_max_right _ _

/-- `Func.asympOnSet` is monotone in the underlying set. -/
lemma asympOnSet_mono (Func : AdmissibleFunctional F V) {A B : Set V} (h : A ⊆ B) :
    Func.asympOnSet A ≤ Func.asympOnSet B := by
  classical
  unfold AdmissibleFunctional.asympOnSet
  refine ciSup_mono (asympOnSet_bddAbove Func B) (fun T => ?_)
  rw [iSup_mem_eq, iSup_mem_eq]
  split_ifs with hTA hTB hTB
  · exact le_rfl
  · exact absurd (h hTA) hTB
  · exact regularize_nonneg Func T
  · exact le_rfl

/-! ## Lemma 2.3: `Z̄(A)^{(n)} ⊆ span A^{(n)}`. -/

/-- **Lemma 2.3**.

For every subset `A ⊆ V` and every `n ∈ ℕ+`,
`Z̄(A)^{(n)} ⊆ span A^{(n)}`.

Proof (Lemma 2.3): every linear form `ℓ : V^⊗n →ₗ[F] F` vanishing on
`A^{(n)}` corresponds, via composition with `T ↦ T^{⊗n}`, to a polynomial
function on `V` vanishing on `A`; this polynomial then vanishes on `Z̄(A)`
by definition, hence `ℓ` vanishes on `Z̄(A)^{(n)}`. The span is the
intersection of kernels of all such `ℓ`, giving the inclusion. -/
theorem power_subset_span_closure (A : Set V) (n : ℕ+) :
    powerSet (F := F) (zariskiClosure (F := F) A) n ⊆
      ((Submodule.span F (powerSet (F := F) A n)) : Set _) := by
  rintro x ⟨T, hT_closure, rfl⟩
  rw [SetLike.mem_coe, ← Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff]
  intro ℓ hℓ
  rw [Submodule.mem_dualAnnihilator] at hℓ
  apply hT_closure (fun S : V => ℓ (tensorPow n S))
  · exact isPolynomialFunction_linMap_tensorPow n ℓ
  · intro S hSA
    exact hℓ _ (Submodule.subset_span ⟨S, hSA, rfl⟩)

/-! ## A.3.1 — decomposition extraction from `T ∈ Z̄(A)` -/

/-- **A.3.1** From `T ∈ Z̄(A)` and `n : ℕ+`, extract a finite indexed decomposition
    `tensorPow n T = ∑ i, α i • tensorPow n (S i)` with all `S i ∈ A`.

    Uses `power_subset_span_closure` (Lemma 2.3) + `Submodule.mem_span_iff_exists_finset_subset`.
    Each base element of `powerSet A n` is by definition `tensorPow n S` for some
    `S ∈ A`; we pick representatives via classical choice. -/
lemma exists_tensorPow_decomp (A : Set V) (T : V) (n : ℕ+)
    (hT : T ∈ zariskiClosure (F := F) A) :
    ∃ (p : ℕ) (S : Fin p → V) (α : Fin p → F),
      (∀ i, S i ∈ A) ∧
      tensorPow (F := F) (V := V) n T = ∑ i, α i • tensorPow n (S i) := by
  -- tensorPow n T ∈ Submodule.span F (powerSet A n) by Lemma 2.3.
  have hmem : tensorPow (F := F) (V := V) n T ∈
      Submodule.span F (powerSet (F := F) A n) := by
    exact power_subset_span_closure A n ⟨T, hT, rfl⟩
  -- Extract a finset decomposition over powerSet A n.
  obtain ⟨f, t, ht_sub, _, hsum⟩ :=
    Submodule.mem_span_iff_exists_finset_subset.mp hmem
  classical
  -- For each y ∈ t, the predicate `y ∈ powerSet A n` gives `∃ S ∈ A, y = tensorPow n S`.
  -- Enumerate `t` via `t.equivFin.symm : Fin t.card ≃ ↥t` and pick a base `S ∈ A`.
  refine ⟨t.card,
    fun i => Classical.choose (ht_sub (t.equivFin.symm i).2),
    fun i => f (t.equivFin.symm i).val, ?_, ?_⟩
  · intro i
    exact (Classical.choose_spec (ht_sub (t.equivFin.symm i).2)).1
  · -- Sum-equivalence: bridge ∑ over Fin t.card to ∑ over t via Finset.sum_attach + sum_equiv.
    calc tensorPow (F := F) (V := V) n T
        = ∑ a ∈ t, f a • a := hsum.symm
      _ = ∑ a ∈ t.attach, f a.val • a.val :=
          (Finset.sum_attach t (fun y => f y • y)).symm
      _ = ∑ i : Fin t.card, f (t.equivFin.symm i).val • (t.equivFin.symm i).val := by
          refine Finset.sum_equiv t.equivFin (fun a => by simp) (fun a _ => ?_)
          simp
      _ = ∑ i : Fin t.card, f (t.equivFin.symm i).val •
            tensorPow n (Classical.choose (ht_sub (t.equivFin.symm i).2)) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          congr 1
          exact (Classical.choose_spec (ht_sub (t.equivFin.symm i).2)).2

/-- The `n`-th tensor power `V^{⊗n}` of a finite-dimensional `V` is finite-dimensional.
    Built from the `PiTensorProduct` basis (`Basis.piTensorProduct`) indexed by the
    finite type `Fin n → Fin (dim V)`. Used to bound the length of decompositions in
    `exists_tensorPow_decomp_bounded`. -/
instance tensorPow_module_finite (n : ℕ) :
    Module.Finite F (TensorPower F n V) := by
  classical
  exact Module.Finite.of_basis
    (Basis.piTensorProduct (fun _ : Fin n => Module.finBasis F V))

/-- **A.3.1 (length-bounded form)** Strengthening of `exists_tensorPow_decomp`:
    the decomposition `T^⊗n = ∑_{i<p} αᵢ Sᵢ^⊗n` can be taken with the number of
    parts bounded by the dimension of the span of `A^{(n)}`:
    `p ≤ dim (span A^{(n)})`.

    Theorem 2.2 takes the `Sᵢ^⊗n` *linearly independent*; the count of a
    linearly independent family in `span A^{(n)}` is `≤ dim (span A^{(n)})`.
    Here we extract a linearly-independent spanning subset `b ⊆ A^{(n)}` (via
    `exists_linearIndependent`), express `T^⊗n` over `b`, and use
    `finrank_span_eq_card` to identify `p = |b| = dim (span A^{(n)})`. This is
    the input to the polynomial-growth bound `p(n) ≤ dim Sym^n V` (Theorem 2.2). -/
lemma exists_tensorPow_decomp_bounded (A : Set V) (T : V) (n : ℕ+)
    (hT : T ∈ zariskiClosure (F := F) A) :
    ∃ (p : ℕ) (S : Fin p → V) (α : Fin p → F),
      (∀ i, S i ∈ A) ∧
      tensorPow (F := F) (V := V) n T = ∑ i, α i • tensorPow n (S i) ∧
      p ≤ Module.finrank F (Submodule.span F (powerSet (F := F) A n)) := by
  classical
  -- tensorPow n T ∈ Submodule.span F (powerSet A n) by Lemma 2.3.
  have hmem : tensorPow (F := F) (V := V) n T ∈
      Submodule.span F (powerSet (F := F) A n) :=
    power_subset_span_closure A n ⟨T, hT, rfl⟩
  -- Extract a linearly independent spanning subset `b ⊆ powerSet A n`.
  obtain ⟨b, hb_sub, hb_span, hb_li⟩ :=
    exists_linearIndependent F (powerSet (F := F) A n)
  -- `b` is finite (it sits in the finite-dimensional space `V^⊗n`).
  have hb_fin : b.Finite := hb_li.finite
  haveI : Fintype b := hb_fin.fintype
  -- `T^⊗n ∈ span b`.
  have hmem_b : tensorPow (F := F) (V := V) n T ∈ Submodule.span F b := by
    rw [hb_span]; exact hmem
  -- Decompose `T^⊗n` as a finite combination over `b`'s finset.
  obtain ⟨f, t, ht_sub, _, hsum⟩ :=
    Submodule.mem_span_iff_exists_finset_subset.mp hmem_b
  -- `t ⊆ b ⊆ powerSet A n`.
  have ht_sub_pow : ∀ y ∈ t, y ∈ powerSet (F := F) A n := fun y hy => hb_sub (ht_sub hy)
  -- The dimension of `span (powerSet A n)` equals `|b|` (linearly independent spanning set).
  have hcard_eq : Module.finrank F (Submodule.span F (powerSet (F := F) A n)) =
      b.toFinset.card := by
    rw [← hb_span]
    exact finrank_span_set_eq_card hb_li
  -- Build the `Fin t.card`-indexed decomposition over `t`.
  refine ⟨t.card,
    fun i => Classical.choose (ht_sub_pow _ (t.equivFin.symm i).2),
    fun i => f (t.equivFin.symm i).val, ?_, ?_, ?_⟩
  · intro i
    exact (Classical.choose_spec (ht_sub_pow _ (t.equivFin.symm i).2)).1
  · calc tensorPow (F := F) (V := V) n T
        = ∑ a ∈ t, f a • a := hsum.symm
      _ = ∑ a ∈ t.attach, f a.val • a.val :=
          (Finset.sum_attach t (fun y => f y • y)).symm
      _ = ∑ i : Fin t.card, f (t.equivFin.symm i).val • (t.equivFin.symm i).val := by
          refine Finset.sum_equiv t.equivFin (fun a => by simp) (fun a _ => ?_)
          simp
      _ = ∑ i : Fin t.card, f (t.equivFin.symm i).val •
            tensorPow n (Classical.choose (ht_sub_pow _ (t.equivFin.symm i).2)) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          congr 1
          exact (Classical.choose_spec (ht_sub_pow _ (t.equivFin.symm i).2)).2
  · -- `p = t.card ≤ |b| = dim (span (powerSet A n))`.
    rw [hcard_eq]
    -- `t ⊆ b`, so `t.card ≤ b.toFinset.card`.
    have ht_sub_b : t ⊆ b.toFinset := by
      intro y hy
      rw [Set.mem_toFinset]
      exact ht_sub hy
    exact Finset.card_le_card ht_sub_b

/-- **Symmetric-monomial spanning bound** (Theorem 2.2, the
    `dim span V^{(n)} ≤ dim Sym^n V` step).

    The pure powers `{T^⊗n : T ∈ V}` span the symmetric subspace of `V^{⊗n}`.
    Expanding `T = ∑ᵢ cᵢ bᵢ` in a basis `b` of `V`,
    `T^⊗n = ∑_{multisets J of size n} (coeff_J) · msymₘ(J)`, where
    `msym(J) = ∑_{orderings of J} b_{·}⊗⋯⊗b_{·}` is the symmetrized monomial for
    `J`. Hence `span V^{(n)} ⊆ span {msym(J) : J ∈ Sym (Fin d) n}`, a family of
    `|Sym (Fin d) n| = multichoose d n = binom(d + n - 1, n)` vectors
    This is the focused missing structural fact: it does not include the
    stars-and-bars cardinal computation, only the inclusion in the span of
    symmetrized monomials indexed by `Sym (Fin d) n`.

    Theorem 2.2:
    > "Note that p(n) grows at most polynomially in n, since
    >  p(n) ≤ dim span A^{(n)} ≤ dim Sym^n(V) = binom(dim V + n - 1, n)." -/
lemma finrank_span_powerSet_univ_le_card_sym (n : ℕ+) :
    Module.finrank F (Submodule.span F (powerSet (F := F) (Set.univ : Set V) n)) ≤
      Fintype.card (Sym (Fin (Module.finrank F V)) (n : ℕ)) := by
  classical
  let d := Module.finrank F V
  let b := Module.finBasis F V
  let msym : Sym (Fin d) (n : ℕ) → TensorPower F (n : ℕ) V := fun J =>
    ∑ e : {e : Fin (n : ℕ) → Fin d //
        (Finset.univ : Finset (Fin (n : ℕ))).val.map e = (J : Multiset (Fin d))},
      PiTensorProduct.tprod F (fun k : Fin (n : ℕ) => b (e.1 k))
  -- Focused structural fact from Theorem 2.2.  Expanding each pure
  -- power in the basis `b` and collecting words with the same multiset gives
  -- a linear combination of the symmetrized monomials `msym J`; hence all
  -- pure powers lie in `span (Set.range msym)`.
  have hspan : Submodule.span F (powerSet (F := F) (Set.univ : Set V) n) ≤
      Submodule.span F (Set.range msym) := by
    have h_pure_power_mem_sym_span :
        ∀ T : V, tensorPow (F := F) (V := V) n T ∈ Submodule.span F (Set.range msym) := by
      -- Focused remaining mathematical subfact: expand `T` in the basis `b`,
      -- use multilinearity of `PiTensorProduct.tprod`, and regroup the finite
      -- sum over words `Fin n → Fin d` by the multiset in `Sym (Fin d) n`.
      intro T
      have h_msym_linear_combination :
          ∃ c : Sym (Fin d) (n : ℕ) → F,
            tensorPow (F := F) (V := V) n T = ∑ J : Sym (Fin d) (n : ℕ), c J • msym J := by
        -- Expand `T` in the basis `b`, use multilinearity of `tprod`, and
        -- regroup the resulting word-sum by the multiset of indices.  On each
        -- fiber the scalar coefficient `∏ k, b.repr T (e k)` is constant.
        let wordSym : (Fin (n : ℕ) → Fin d) → Sym (Fin d) (n : ℕ) := fun e =>
          ⟨(Finset.univ : Finset (Fin (n : ℕ))).val.map e, by
            rw [Fin.univ_val_map]
            simp⟩
        let c : Sym (Fin d) (n : ℕ) → F := fun J =>
          ((J : Multiset (Fin d)).map fun i => b.repr T i).prod
        refine ⟨c, ?_⟩
        have hT : T = ∑ i, (b.repr T i) • b i := (b.sum_repr T).symm
        have hTPow :
            tensorPow (F := F) (V := V) n T =
              ∑ e : Fin (n : ℕ) → Fin d,
                (∏ k, b.repr T (e k)) •
                  PiTensorProduct.tprod F (fun k : Fin (n : ℕ) => b (e k)) := by
          unfold tensorPow
          conv_lhs =>
            rw [show (fun _ : Fin (n : ℕ) => T) =
              (fun _ : Fin (n : ℕ) => ∑ i, (b.repr T i) • b i) from by
                funext
                exact hT]
          rw [MultilinearMap.map_sum
            (PiTensorProduct.tprod F (s := fun _ : Fin (n : ℕ) => V))]
          refine Finset.sum_congr rfl (fun e _ => ?_)
          exact MultilinearMap.map_smul_univ
            (PiTensorProduct.tprod F (s := fun _ : Fin (n : ℕ) => V))
            (fun k : Fin (n : ℕ) => b.repr T (e k))
            (fun k : Fin (n : ℕ) => b (e k))
        have hcoeff (e : Fin (n : ℕ) → Fin d) :
            c (wordSym e) = ∏ k, b.repr T (e k) := by
          simp [c, wordSym, Fin.univ_val_map, Finset.prod_eq_multiset_prod]
          rfl
        have hmsym_filter (J : Sym (Fin d) (n : ℕ)) :
            msym J =
              ∑ e : Fin (n : ℕ) → Fin d with wordSym e = J,
                PiTensorProduct.tprod F (fun k : Fin (n : ℕ) => b (e k)) := by
          let p : (Fin (n : ℕ) → Fin d) → Prop := fun e =>
            (Finset.univ : Finset (Fin (n : ℕ))).val.map e = (J : Multiset (Fin d))
          have hp (e : Fin (n : ℕ) → Fin d) : wordSym e = J ↔ p e := by
            constructor
            · intro h
              simpa [p, wordSym] using! congrArg (fun J : Sym (Fin d) (n : ℕ) =>
                (J : Multiset (Fin d))) h
            · intro h
              exact Sym.ext (by simpa [p, wordSym] using! h)
          calc
            msym J =
                ∑ e : {e : Fin (n : ℕ) → Fin d // p e},
                  PiTensorProduct.tprod F (fun k : Fin (n : ℕ) => b (e.1 k)) := by
              simp [msym, p]
            _ = ∑ e : Fin (n : ℕ) → Fin d with p e,
                  PiTensorProduct.tprod F (fun k : Fin (n : ℕ) => b (e k)) := by
              simpa using! (Finset.sum_subtype_eq_sum_filter
                (s := (Finset.univ : Finset (Fin (n : ℕ) → Fin d)))
                (p := p)
                (f := fun e : Fin (n : ℕ) → Fin d =>
                  PiTensorProduct.tprod F (fun k : Fin (n : ℕ) => b (e k))))
            _ = ∑ e : Fin (n : ℕ) → Fin d with wordSym e = J,
                  PiTensorProduct.tprod F (fun k : Fin (n : ℕ) => b (e k)) := by
              refine Finset.sum_congr ?_ (fun e _ => rfl)
              exact Finset.filter_congr (fun e _ => (hp e).symm)
        calc
          tensorPow (F := F) (V := V) n T
              = ∑ e : Fin (n : ℕ) → Fin d,
                  (∏ k, b.repr T (e k)) •
                    PiTensorProduct.tprod F (fun k : Fin (n : ℕ) => b (e k)) := hTPow
          _ = ∑ J : Sym (Fin d) (n : ℕ),
                ∑ e : Fin (n : ℕ) → Fin d with wordSym e = J,
                  (∏ k, b.repr T (e k)) •
                    PiTensorProduct.tprod F (fun k : Fin (n : ℕ) => b (e k)) := by
            rw [Finset.sum_fiberwise]
          _ = ∑ J : Sym (Fin d) (n : ℕ), c J • msym J := by
            refine Finset.sum_congr rfl (fun J _ => ?_)
            rw [hmsym_filter J, Finset.smul_sum]
            refine Finset.sum_congr rfl (fun e he => ?_)
            rw [← hcoeff e]
            have heq : wordSym e = J := (Finset.mem_filter.mp he).2
            rw [heq]
      rcases h_msym_linear_combination with ⟨c, hc⟩
      rw [hc]
      refine Submodule.sum_mem _ (fun J _ => ?_)
      exact Submodule.smul_mem _ (c J) (Submodule.subset_span ⟨J, rfl⟩)
    rw [Submodule.span_le]
    intro S hS
    rcases hS with ⟨T, _hT_univ, rfl⟩
    exact h_pure_power_mem_sym_span T
  calc
    Module.finrank F (Submodule.span F (powerSet (F := F) (Set.univ : Set V) n))
        ≤ Module.finrank F (Submodule.span F (Set.range msym)) :=
          Submodule.finrank_mono hspan
    _ ≤ Fintype.card (Sym (Fin d) (n : ℕ)) := by
          simpa [Set.finrank] using! finrank_range_le_card (R := F) (b := msym)
    _ = Fintype.card (Sym (Fin (Module.finrank F V)) (n : ℕ)) := rfl

/-- **Symmetric-subspace dimension bound** (Theorem 2.2, the
    `dim span V^{(n)} ≤ dim Sym^n V = binom(dim V + n - 1, n)` step). -/
lemma finrank_span_powerSet_univ_le_choose (n : ℕ+) :
    Module.finrank F (Submodule.span F (powerSet (F := F) (Set.univ : Set V) n)) ≤
      Nat.choose (Module.finrank F V + (n : ℕ) - 1) (n : ℕ) := by
  classical
  calc
    Module.finrank F (Submodule.span F (powerSet (F := F) (Set.univ : Set V) n))
        ≤ Fintype.card (Sym (Fin (Module.finrank F V)) (n : ℕ)) :=
          finrank_span_powerSet_univ_le_card_sym n
    _ = Nat.choose (Module.finrank F V + (n : ℕ) - 1) (n : ℕ) := by
          rw [Sym.card_sym_eq_choose, Fintype.card_fin]

/--
**Polynomial growth bound** (Theorem 2.2): the dimension of the span of
    `A^{(n)}` is at most `dim Sym^n V = binom(dim V + n - 1, n)`.

    Theorem 2.2:
    > "Note that p(n) grows at most polynomially in n, since
    >  p(n) ≤ dim span A^{(n)} ≤ dim Sym^n(V) = binom(dim V + n - 1, n)."

    Proof: `span A^{(n)} ⊆ span V^{(n)}` (monotonicity, `A ⊆ V`), and `span V^{(n)}`
    is the *symmetric subspace* of `V^{⊗n}` (spanned by the pure powers
    `{T^⊗n : T ∈ V}`), whose dimension is `binom(dim V + n - 1, n)`. The latter
    equality is the standard dimension of the `n`-th symmetric power of a
    `dim V`-dimensional space (`Sym.card_sym_eq_multichoose` +
    `Nat.multichoose_eq`: the symmetric monomials of degree `n` in `dim V`
    variables number `multichoose (dim V) n = binom(dim V + n - 1, n)`).
-/
lemma finrank_span_powerSet_le_choose (A : Set V) (n : ℕ+) :
    Module.finrank F (Submodule.span F (powerSet (F := F) A n)) ≤
      Nat.choose (Module.finrank F V + (n : ℕ) - 1) (n : ℕ) := by
  -- Step 1: monotonicity `span A^(n) ⊆ span V^(n)` since `A ⊆ univ`.
  have hsub : Submodule.span F (powerSet (F := F) A n) ≤
      Submodule.span F (powerSet (F := F) (Set.univ : Set V) n) := by
    apply Submodule.span_mono
    rintro x ⟨T, _, rfl⟩
    exact ⟨T, Set.mem_univ T, rfl⟩
  have hmono := Submodule.finrank_mono hsub
  refine hmono.trans ?_
  -- Step 2: `dim (span V^(n)) = dim Sym^n V = binom(dim V + n - 1, n)`.
  -- The pure powers `{T^⊗n : T ∈ V}` span the symmetric subspace of `V^⊗n`,
  -- whose dimension is `binom(dim V + n - 1, n)` (= number of degree-`n`
  -- symmetric monomials in `dim V` variables). See docstring; isolated as a
  exact finrank_span_powerSet_univ_le_choose n

/-!
## Theorem 2.2 — building blocks for the hard direction.

* `regularize_le_poly_times_eps`: for every `n : ℕ+` and `ε > 0`,
  `F̃(T) ≤ p_n^(1/n) · (F̃[A] + ε)` where `p_n = binom(d + n - 1, n)`.
  This is the result of the *inner* combinatorial bound in the proof of Theorem 2.2 after
  taking `m → ∞`.

* `regularize_le_asymp_plus_eps`: for every `ε > 0`, `F̃(T) ≤ F̃[A] + ε`,
  obtained by sending `n → ∞` and using
  `binomial_pow_root_tendsto_one_pos`.

* `regularize_le_asymp_on_set`: `F̃(T) ≤ F̃[A]` by sending `ε → 0`.
-/

/-- Helper: `Func.asympOnSet A ≥ 0` always. Either `A` is nonempty and we use
    `regularize_nonneg` on a witness, or `A` is empty and the supremum is 0. -/
lemma asympOnSet_nonneg (Func : AdmissibleFunctional F V) (A : Set V) :
    0 ≤ Func.asympOnSet A := by
  classical
  unfold AdmissibleFunctional.asympOnSet
  by_cases hAne : A.Nonempty
  · obtain ⟨T', hT'⟩ := hAne
    have h_T'_le : Func.regularize T' ≤
        (⨆ T : V, ⨆ _ : T ∈ A, Func.regularize T) := by
      have h_inner_eq : (⨆ _ : T' ∈ A, Func.regularize T') = Func.regularize T' := by
        rw [iSup_mem_eq, if_pos hT']
      rw [← h_inner_eq]
      exact le_ciSup (asympOnSet_bddAbove Func A) T'
    exact (regularize_nonneg Func T').trans h_T'_le
  · rw [Set.not_nonempty_iff_eq_empty] at hAne
    subst hAne
    have hzero_inner : ∀ T : V, (⨆ _ : T ∈ (∅ : Set V), Func.regularize T) = 0 := fun T => by
      rw [iSup_mem_eq, if_neg (Set.notMem_empty T)]
    simp_rw [hzero_inner]
    rcases (inferInstance : Nonempty V) with ⟨v⟩
    haveI : Nonempty V := ⟨v⟩
    rw [ciSup_const]

/-!
### Sub-helpers for `tensorPow_nm_inner_bound`

The proof of `tensorPow_nm_inner_bound` (Theorem 2.2) factorizes into a
single combinatorial sub-helper that captures all the multi-index
structural work, plus a closed limit-bookkeeping assembly that uses
`regularize_approximation`, `toFun_tensorPow_le_bdd_pow`, and the
binomial growth of the decomposition length.

  ∀ m, F_{nm}(T^⊗(nm)) ≤ p_n^m · (F̃[A] + ε)^(nm) · B^(p_n · M(ε,n))

where:
* `p_n` is the decomposition length (≤ binom(d+n-1, n));
* `B` is any constant ≥ 1 bounding `F_1`;
* `M(ε, n)` is the uniform `regularize_approximation` threshold for
  each `S_i` in the decomposition `T^⊗n = ∑ᵢ αᵢ Sᵢ^⊗n`.
-/

/-!
#### Sub-helpers for `nm_F_combinatorial_bound`

2. **`F_S_pow_le_target_factor`** (Theorem 2.2, fully closed via
   `regularize_approximation` + `toFun_tensorPow_le_bdd_pow` + monotonicity
   `regularize ≤ asympOnSet`): for each `i` and `k : ℕ`, the bound
   `F(Sᵢ^⊗(k·n)) ≤ (F̃[A]+ε)^(k·n) · B^M` (with the convention that the
   empty `k = 0` case is `F(Sᵢ^⊗0) ≤ 1` which we encode as `Sᵢ^⊗(0·n) ≤ 1`
   by special-casing — we treat `k·n` as ℕ+ only when `k ≥ 1` and otherwise
   the factor is 1).

3. **Final assembly**: multiply factors over `i : Fin p`, sum exponents
   `∑ᵢ mᵢ(I) = m`, get `∏ᵢ (F̃[A]+ε)^(mᵢ·n) · B^M = (F̃[A]+ε)^(nm) · B^(p·M)`.
   The number of multi-indices `I : Fin m → Fin p` is `p^m`; combining with
   the bound on each I gives `F(T^⊗(nm)) ≤ p^m · (F̃[A]+ε)^(nm) · B^(p·M)`.
-/

/-!
* `F_tensorPow_nm_le_pm_max_block_apply` (Theorem 2.2): the
  multi-index expansion combined with subadditivity and scalar
  invariance gives `F(T^⊗(nm)) ≤ p^m · max_I F(block_I)` where
  `block_I = (tensorPowerAdd-iterated) ⊗_j tensorPow n (S (I j))`.
  Pure expansion + subadd + scalar_inv (Theorem 2.2).
* `F_block_le_grouped_product` (Theorem 2.2): a single block
  tensor `⊗_j tensorPow n (S (I j))` (a particular admissible-functional
  input via `tensorPowerBlock`) satisfies
  `F(block_I) ≤ ∏ᵢ F(Sᵢ^⊗(mᵢ(I)·n))`. Pure perm_inv + iterated submul
  (Theorem 2.2).

The combined `F_tensorPow_nm_le_max_grouped_product` follows by bounding `max_I F(block_I) ≤ max_I (∏ᵢ per-i factor)` factor-by-
factor via the second helper, then chain.
-/

/-- **Block tensor for a multi-index** (Theorem 2.2, notation).

    For a multi-index `I : Fin m → Fin p` and `S : Fin p → V`, this is
    the block tensor `⊗_{j=1}^m S(I j)^⊗n`, an element of
    `TensorPower F ((n*m).val) V` via the `tensorPowerBlock` assembly
    with constant block-size `n`, cast across `∑_{j : Fin m} n = n*m`. -/
noncomputable def blockTensorOfMultiIndex
    (n : ℕ+) {p : ℕ} (S : Fin p → V) {m : ℕ+} (I : Fin m → Fin p) :
    TensorPower F ((n * m : ℕ+) : ℕ) V :=
  -- ∑ j : Fin m, n = m * n = n * m, by `Finset.sum_const + Fin.card` + `mul_comm`.
  let nVec : Fin m → ℕ := fun _ => (n : ℕ)
  let Ts : ∀ j : Fin m, TensorPower F (nVec j) V := fun j => tensorPow n (S (I j))
  have hsum_eq : ∑ j : Fin m, nVec j = ((n * m : ℕ+) : ℕ) := by
    rw [PNat.mul_coe, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    ring
  (TensorPower.cast F V hsum_eq) (tensorPowerBlock F V nVec Ts)

/-- **Helper: `∑ _ : Fin m, n = n*m`** (proof of Theorem 2.2).

    Used to cast the `tensorPowerBlock` (which lives in
    `TensorPower F (∑ j, n) V`) into the target type `TensorPower F (n*m) V`. -/
private lemma tensorPower_sum_const_eq_mul (n : ℕ+) (m : ℕ+) :
    ∑ _ : Fin m, (n : ℕ) = ((n * m : ℕ+) : ℕ) := by
  rw [PNat.mul_coe, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  ring

/-- **Multilinearity at slot 0 (additive).** Recursive base step for
    `tensorPowerBlock` linearity in the first input. -/
private lemma tensorPowerBlock_succ_zero_add {ℓ : ℕ} (nVec : Fin (ℓ + 1) → ℕ)
    (Ts : ∀ i : Fin (ℓ + 1), TensorPower F (nVec i) V)
    (x y : TensorPower F (nVec 0) V) :
    tensorPowerBlock F V nVec (Function.update Ts 0 (x + y)) =
      tensorPowerBlock F V nVec (Function.update Ts 0 x) +
        tensorPowerBlock F V nVec (Function.update Ts 0 y) := by
  unfold tensorPowerBlock
  simp only [Function.update_self]
  -- Tail unchanged: update at 0 doesn't affect i.succ.
  have htail :
      (fun i : Fin ℓ => (Function.update Ts 0 (x + y)) i.succ) =
        (fun i : Fin ℓ => Ts i.succ) := by
    funext i; rw [Function.update_of_ne (Fin.succ_ne_zero i)]
  have htail_x :
      (fun i : Fin ℓ => (Function.update Ts 0 x) i.succ) =
        (fun i : Fin ℓ => Ts i.succ) := by
    funext i; rw [Function.update_of_ne (Fin.succ_ne_zero i)]
  have htail_y :
      (fun i : Fin ℓ => (Function.update Ts 0 y) i.succ) =
        (fun i : Fin ℓ => Ts i.succ) := by
    funext i; rw [Function.update_of_ne (Fin.succ_ne_zero i)]
  rw [htail, htail_x, htail_y]
  rw [TensorProduct.add_tmul, map_add, map_add]

/-- **Multilinearity at slot 0 (scalar).** Recursive base step for
    `tensorPowerBlock` linearity in the first input. -/
private lemma tensorPowerBlock_succ_zero_smul {ℓ : ℕ} (nVec : Fin (ℓ + 1) → ℕ)
    (Ts : ∀ i : Fin (ℓ + 1), TensorPower F (nVec i) V)
    (c : F) (x : TensorPower F (nVec 0) V) :
    tensorPowerBlock F V nVec (Function.update Ts 0 (c • x)) =
      c • tensorPowerBlock F V nVec (Function.update Ts 0 x) := by
  unfold tensorPowerBlock
  simp only [Function.update_self]
  have htail :
      (fun i : Fin ℓ => (Function.update Ts 0 (c • x)) i.succ) =
        (fun i : Fin ℓ => Ts i.succ) := by
    funext i; rw [Function.update_of_ne (Fin.succ_ne_zero i)]
  have htail_x :
      (fun i : Fin ℓ => (Function.update Ts 0 x) i.succ) =
        (fun i : Fin ℓ => Ts i.succ) := by
    funext i; rw [Function.update_of_ne (Fin.succ_ne_zero i)]
  rw [htail, htail_x]
  rw [← TensorProduct.smul_tmul', map_smul, map_smul]

/-- **Multilinearity at slot j.succ (additive).** Recursive step for
    `tensorPowerBlock` linearity in a later input. -/
private lemma tensorPowerBlock_succ_succ_add {ℓ : ℕ}
    (htail_add : ∀ (nVec' : Fin ℓ → ℕ) (Ts' : ∀ i : Fin ℓ, TensorPower F (nVec' i) V)
        (j' : Fin ℓ) (x' y' : TensorPower F (nVec' j') V),
        tensorPowerBlock F V nVec' (Function.update Ts' j' (x' + y')) =
          tensorPowerBlock F V nVec' (Function.update Ts' j' x') +
            tensorPowerBlock F V nVec' (Function.update Ts' j' y'))
    (nVec : Fin (ℓ + 1) → ℕ)
    (Ts : ∀ i : Fin (ℓ + 1), TensorPower F (nVec i) V) (j : Fin ℓ)
    (x y : TensorPower F (nVec j.succ) V) :
    tensorPowerBlock F V nVec (Function.update Ts j.succ (x + y)) =
      tensorPowerBlock F V nVec (Function.update Ts j.succ x) +
        tensorPowerBlock F V nVec (Function.update Ts j.succ y) := by
  unfold tensorPowerBlock
  have h0_ne : (0 : Fin (ℓ + 1)) ≠ j.succ := (Fin.succ_ne_zero j).symm
  rw [Function.update_of_ne h0_ne, Function.update_of_ne h0_ne,
      Function.update_of_ne h0_ne]
  have htail :
      ∀ (v : TensorPower F (nVec j.succ) V),
        (fun i : Fin ℓ => (Function.update Ts j.succ v) i.succ) =
          Function.update (fun i : Fin ℓ => Ts i.succ) j v := by
    intro v
    funext i
    by_cases hi : i = j
    · subst hi; simp
    · rw [Function.update_of_ne (fun h => hi (Fin.succ_injective _ h)),
          Function.update_of_ne hi]
  rw [htail (x + y), htail x, htail y]
  rw [htail_add (fun i => nVec i.succ) (fun i => Ts i.succ) j x y]
  rw [TensorProduct.tmul_add, map_add, map_add]

/-- **Multilinearity at slot j.succ (scalar).** Recursive step. -/
private lemma tensorPowerBlock_succ_succ_smul {ℓ : ℕ}
    (htail_smul : ∀ (nVec' : Fin ℓ → ℕ) (Ts' : ∀ i : Fin ℓ, TensorPower F (nVec' i) V)
        (j' : Fin ℓ) (c' : F) (x' : TensorPower F (nVec' j') V),
        tensorPowerBlock F V nVec' (Function.update Ts' j' (c' • x')) =
          c' • tensorPowerBlock F V nVec' (Function.update Ts' j' x'))
    (nVec : Fin (ℓ + 1) → ℕ)
    (Ts : ∀ i : Fin (ℓ + 1), TensorPower F (nVec i) V) (j : Fin ℓ)
    (c : F) (x : TensorPower F (nVec j.succ) V) :
    tensorPowerBlock F V nVec (Function.update Ts j.succ (c • x)) =
      c • tensorPowerBlock F V nVec (Function.update Ts j.succ x) := by
  unfold tensorPowerBlock
  have h0_ne : (0 : Fin (ℓ + 1)) ≠ j.succ := (Fin.succ_ne_zero j).symm
  rw [Function.update_of_ne h0_ne, Function.update_of_ne h0_ne]
  have htail :
      ∀ (v : TensorPower F (nVec j.succ) V),
        (fun i : Fin ℓ => (Function.update Ts j.succ v) i.succ) =
          Function.update (fun i : Fin ℓ => Ts i.succ) j v := by
    intro v
    funext i
    by_cases hi : i = j
    · subst hi; simp
    · rw [Function.update_of_ne (fun h => hi (Fin.succ_injective _ h)),
          Function.update_of_ne hi]
  rw [htail (c • x), htail x]
  rw [htail_smul (fun i => nVec i.succ) (fun i => Ts i.succ) j c x]
  rw [TensorProduct.tmul_smul, map_smul, map_smul]

/-- **Multilinearity of `tensorPowerBlock` in the `Ts` slot at coordinate `j`,
    additive part** (proof of Theorem 2.2).

    Proof: structural recursion on `ℓ`, dispatching slot 0 vs slot `j.succ`. -/
private lemma tensorPowerBlock_update_add :
    ∀ {ℓ : ℕ} (nVec : Fin ℓ → ℕ)
      (Ts : ∀ i : Fin ℓ, TensorPower F (nVec i) V) (j : Fin ℓ)
      (x y : TensorPower F (nVec j) V),
      tensorPowerBlock F V nVec (Function.update Ts j (x + y)) =
        tensorPowerBlock F V nVec (Function.update Ts j x) +
          tensorPowerBlock F V nVec (Function.update Ts j y)
  | 0, _, _, j, _, _ => Fin.elim0 j
  | ℓ + 1, nVec, Ts, j, x, y =>
      j.cases
        (tensorPowerBlock_succ_zero_add (F := F) (V := V) nVec Ts)
        (fun j' =>
          tensorPowerBlock_succ_succ_add (F := F) (V := V)
            (fun nVec' Ts' j'' x' y' =>
              tensorPowerBlock_update_add nVec' Ts' j'' x' y')
            nVec Ts j')
        x y

/-- **Multilinearity of `tensorPowerBlock` in the `Ts` slot at coordinate `j`,
    scalar part** (proof of Theorem 2.2). -/
private lemma tensorPowerBlock_update_smul :
    ∀ {ℓ : ℕ} (nVec : Fin ℓ → ℕ)
      (Ts : ∀ i : Fin ℓ, TensorPower F (nVec i) V) (j : Fin ℓ)
      (c : F) (x : TensorPower F (nVec j) V),
      tensorPowerBlock F V nVec (Function.update Ts j (c • x)) =
        c • tensorPowerBlock F V nVec (Function.update Ts j x)
  | 0, _, _, j, _, _ => Fin.elim0 j
  | ℓ + 1, nVec, Ts, j, c, x =>
      j.cases
        (tensorPowerBlock_succ_zero_smul (F := F) (V := V) nVec Ts c)
        (fun j' =>
          tensorPowerBlock_succ_succ_smul (F := F) (V := V)
            (fun nVec' Ts' j'' c' x' =>
              tensorPowerBlock_update_smul nVec' Ts' j'' c' x')
            nVec Ts j' c)
        x

/-- **Constant-block multilinear assembly** (proof of Theorem 2.2).

    The `m`-fold block tensor with constant block-size `n` packaged as a
    `MultilinearMap` from `(Fin m → TensorPower F n V)` to
    `TensorPower F (n*m) V` (via `tensorPowerBlock` + `TensorPower.cast`).

    For a multi-index `I`, applying this to `fun j => tensorPow n (S (I j))`
    yields `blockTensorOfMultiIndex n S I` (definitionally). -/
noncomputable def tensorPowerBlockConstMulti (n : ℕ+) (m : ℕ+) :
    MultilinearMap F (fun _ : Fin m => TensorPower F (n : ℕ) V)
      (TensorPower F ((n * m : ℕ+) : ℕ) V) :=
  (TensorPower.cast F V (tensorPower_sum_const_eq_mul n m)).toLinearMap.compMultilinearMap
    { toFun := fun Ts => tensorPowerBlock F V (fun _ : Fin m => (n : ℕ)) Ts
      map_update_add' := by
        intro instDec Ts j x y
        -- `instDec = instDecidableEqFin (↑m)` by `Subsingleton.elim`
        -- (DecidableEq is a subsingleton), so the two `Function.update`
        -- forms are equal.
        have hinst : instDec = instDecidableEqFin (↑m) := Subsingleton.elim _ _
        subst hinst
        exact tensorPowerBlock_update_add (F := F) (V := V)
          (fun _ : Fin m => (n : ℕ)) Ts j x y
      map_update_smul' := by
        intro instDec Ts j c x
        have hinst : instDec = instDecidableEqFin (↑m) := Subsingleton.elim _ _
        subst hinst
        exact tensorPowerBlock_update_smul (F := F) (V := V)
          (fun _ : Fin m => (n : ℕ)) Ts j c x }

/-- **Apply lemma for `tensorPowerBlockConstMulti`** in terms of `tensorPowerBlock`. -/
private lemma tensorPowerBlockConstMulti_apply (n : ℕ+) (m : ℕ+)
    (Ts : ∀ _ : Fin m, TensorPower F (n : ℕ) V) :
    tensorPowerBlockConstMulti (F := F) (V := V) n m Ts =
      (TensorPower.cast F V (tensorPower_sum_const_eq_mul n m))
        (tensorPowerBlock F V (fun _ : Fin m => (n : ℕ)) Ts) := by
  rfl

/-- **`tensorPowerBlock` as a multilinear map** in its family argument, for a
    general block-size vector `nVec` (Definition 2.1). The
    `map_update_add'`/`map_update_smul'` fields are exactly the general-`nVec`
    update lemmas `tensorPowerBlock_update_add`/`tensorPowerBlock_update_smul`. -/
noncomputable def tensorPowerBlockMulti {ℓ : ℕ} (nVec : Fin ℓ → ℕ) :
    MultilinearMap F (fun i : Fin ℓ => TensorPower F (nVec i) V)
      (TensorPower F (∑ i, nVec i) V) where
  toFun Ts := tensorPowerBlock F V nVec Ts
  map_update_add' := by
    intro instDec Ts j x y
    have hinst : instDec = instDecidableEqFin ℓ := Subsingleton.elim _ _
    subst hinst
    exact tensorPowerBlock_update_add (F := F) (V := V) nVec Ts j x y
  map_update_smul' := by
    intro instDec Ts j c x
    have hinst : instDec = instDecidableEqFin ℓ := Subsingleton.elim _ _
    subst hinst
    exact tensorPowerBlock_update_smul (F := F) (V := V) nVec Ts j c x

@[simp] private lemma tensorPowerBlockMulti_apply {ℓ : ℕ} (nVec : Fin ℓ → ℕ)
    (Ts : ∀ i : Fin ℓ, TensorPower F (nVec i) V) :
    tensorPowerBlockMulti (F := F) (V := V) nVec Ts = tensorPowerBlock F V nVec Ts := rfl

/-- **Bridge: `blockTensorOfMultiIndex` is the multilinear assembly applied to
    the family `j ↦ tensorPow n (S (I j))`.** -/
private lemma blockTensorOfMultiIndex_eq_constMulti
    (n : ℕ+) {p : ℕ} (S : Fin p → V) {m : ℕ+} (I : Fin m → Fin p) :
    blockTensorOfMultiIndex (F := F) (V := V) n S I =
      tensorPowerBlockConstMulti (F := F) (V := V) n m
        (fun j => tensorPow n (S (I j))) := by
  rw [tensorPowerBlockConstMulti_apply]
  rfl

/-- **Structural lemma**: a `tensorPowerBlock` of constant-`tprod` family
    equals the `tprod` of the constant `T`-family over the appended `Fin`
    space (modulo `TensorPower.cast` for the type equality).

    Proof by induction on `ℓ` (the block count). The base case is the empty
    block, where both sides reduce to the unit. The inductive step uses
    `TensorPower.tprod_mul_tprod` (which says `mulEquiv (tprod u ⊗ tprod v)
    = tprod (Fin.append u v)`) + IH on the tail. -/
private lemma tensorPowerBlock_const_tprod :
    ∀ {ℓ : ℕ} (T : V) (nVec : Fin ℓ → ℕ),
      tensorPowerBlock F V nVec
          (fun i : Fin ℓ => PiTensorProduct.tprod F (fun _ : Fin (nVec i) => T)) =
        PiTensorProduct.tprod F (fun _ : Fin (∑ i : Fin ℓ, nVec i) => T)
  | 0, T, nVec => by
    -- Base case: empty product. `tensorPowerBlock` returns the algebra unit cast.
    -- We need: `cast (algebraMap₀ 1) = tprod F (fun _ : Fin 0 => T)`.
    unfold tensorPowerBlock
    -- `algebraMap₀ 1 = ₜ1 = tprod F Fin.elim0`.
    rw [TensorPower.algebraMap₀_one, TensorPower.gOne_def]
    -- After `cast_tprod`, both sides become `tprod` of `Fin.elim0`-style.
    rw [TensorPower.cast_tprod]
    -- Goal: tprod (Fin.elim0 ∘ Fin.cast h.symm) = tprod (fun _ : Fin (∑ Fin 0, nVec) => T)
    -- But `∑ i : Fin 0, nVec i = 0`, so both indices are over `Fin 0`.
    -- Any two functions `Fin 0 → V` are equal by funext (vacuous).
    congr 1
    funext i
    exact i.elim0
  | ℓ + 1, T, nVec => by
    -- Inductive step: split off the first index.
    unfold tensorPowerBlock
    -- LHS = cast (mulEquiv (tprod (const T) ⊗ tensorPowerBlock tail (const tprods)))
    --     = cast (mulEquiv (tprod (const T over Fin (nVec 0)) ⊗
    --              tprod (const T over Fin (∑ tail))))    [by IH]
    --     = cast (tprod (Fin.append (const T) (const T)))  [by tprod_mul_tprod]
    --     = tprod (const T over Fin (nVec 0 + ∑ tail))    [Fin.append of constants]
    --     = tprod (const T over Fin (∑ Fin (ℓ+1), nVec)) [by Fin.sum_univ_succ]
    rw [tensorPowerBlock_const_tprod T (fun i : Fin ℓ => nVec i.succ)]
    rw [show TensorPower.mulEquiv (R := F) (M := V)
              ((PiTensorProduct.tprod F fun _ : Fin (nVec 0) => T) ⊗ₜ[F]
                PiTensorProduct.tprod F (fun _ : Fin (∑ i : Fin ℓ, nVec i.succ) => T)) =
            PiTensorProduct.tprod F
              (Fin.append (fun _ : Fin (nVec 0) => T)
                (fun _ : Fin (∑ i : Fin ℓ, nVec i.succ) => T)) from
        TensorPower.tprod_mul_tprod F _ _]
    -- Now Fin.append of two constant `T`-functions is the constant function on the sum.
    have happend :
        Fin.append (fun _ : Fin (nVec 0) => T)
            (fun _ : Fin (∑ i : Fin ℓ, nVec i.succ) => T) =
          fun _ : Fin (nVec 0 + ∑ i : Fin ℓ, nVec i.succ) => T := by
      funext i
      refine Fin.addCases (fun _ => ?_) (fun _ => ?_) i
      · simp [Fin.append, Fin.addCases]
      · simp [Fin.append, Fin.addCases]
    rw [happend]
    --                   = tprod (const T over Fin (∑ (ℓ+1), nVec))
    -- via TensorPower.cast_tprod + the equality `nVec 0 + ∑ tail = ∑ (ℓ+1)`.
    rw [TensorPower.cast_tprod]
    -- After cast_tprod, goal: tprod (constT ∘ Fin.cast h.symm) = tprod (constT).
    -- The function is constant, so the composition equals the constant.
    rfl

omit [Module.Finite F V] in
/-- **General block-of-`tprod` flattening (Theorem 2.2, reusable core)**:
    a `tensorPowerBlock` whose `i`-th factor is `tprod (w i)` (for some
    `w i : Fin (nVec i) → V`) equals the `tprod` of the flattened family
    `flat : Fin (∑ nVec) → V`, provided `flat ∘ finSigmaFinEquiv = fun s => w s.1 s.2`
    (i.e. `flat` concatenates the per-block families in index order), up to the
    canonical `TensorPower.cast`.

    Generalizes `tensorPowerBlock_const_tprod` (the case where every `w i` is the
    constant `T`-family). Proof by induction on `ℓ`, peeling block `0` and gluing
    via `TensorPower.tprod_mul_tprod` (`mulEquiv (tprod u ⊗ tprod v) = tprod (Fin.append u v)`). -/
private lemma tensorPowerBlock_tprod_family :
    ∀ {ℓ : ℕ} (nVec : Fin ℓ → ℕ) (w : ∀ i : Fin ℓ, Fin (nVec i) → V)
      (flat : Fin (∑ i : Fin ℓ, nVec i) → V)
      (hflat : ∀ s : (i : Fin ℓ) × Fin (nVec i), flat (finSigmaFinEquiv s) = w s.1 s.2),
      tensorPowerBlock F V nVec
          (fun i : Fin ℓ => PiTensorProduct.tprod F (w i)) =
        PiTensorProduct.tprod F flat
  | 0, nVec, w, flat, hflat => by
    unfold tensorPowerBlock
    rw [TensorPower.algebraMap₀_one, TensorPower.gOne_def, TensorPower.cast_tprod]
    congr 1
    funext i
    exact i.elim0
  | ℓ + 1, nVec, w, flat, hflat => by
    -- Peel block 0; glue head `tprod (w 0)` with the tail flatten via IH.
    unfold tensorPowerBlock
    -- Define the tail flatten: `flat` restricted to the tail positions.
    set flatTail : Fin (∑ i : Fin ℓ, nVec i.succ) → V :=
      fun k => w (Fin.succ (finSigmaFinEquiv.symm k).1)
        ((finSigmaFinEquiv.symm k).2) with hflatTail
    rw [tensorPowerBlock_tprod_family (fun i : Fin ℓ => nVec i.succ)
        (fun i : Fin ℓ => w i.succ) flatTail
        (fun s => by
          rw [hflatTail]
          change w (finSigmaFinEquiv.symm (finSigmaFinEquiv s)).fst.succ
              (finSigmaFinEquiv.symm (finSigmaFinEquiv s)).snd = _
          rw [Equiv.symm_apply_apply])]
    rw [show TensorPower.mulEquiv (R := F) (M := V)
              ((PiTensorProduct.tprod F (w 0)) ⊗ₜ[F]
                PiTensorProduct.tprod F flatTail) =
            PiTensorProduct.tprod F (Fin.append (w 0) flatTail) from
        TensorPower.tprod_mul_tprod F _ _]
    rw [TensorPower.cast_tprod]
    -- Goal: tprod (Fin.append (w 0) flatTail ∘ Fin.cast _) = tprod flat.
    congr 1
    funext k
    -- Reindex via `finSigmaFinEquiv`: write `k` as the image of a sigma element.
    obtain ⟨⟨i, j⟩, rfl⟩ := finSigmaFinEquiv.surjective k
    rw [hflat ⟨i, j⟩]
    simp only [Function.comp_apply]
    -- Case split on the block index `i`.
    induction i using Fin.cases with
    | zero =>
      -- Value of `finSigmaFinEquiv ⟨0, j⟩` is `j < nVec 0`: lands in the left part.
      have hpos : Fin.cast (Fin.sum_univ_succ (fun i => nVec i))
          (finSigmaFinEquiv (⟨0, j⟩ : (i : Fin (ℓ+1)) × Fin (nVec i)))
            = Fin.castAdd (∑ i : Fin ℓ, nVec i.succ) j := by
        apply Fin.ext
        simp only [Fin.val_cast, Fin.val_castAdd]
        rw [finSigmaFinEquiv_apply]
        simp
      rw [hpos, Fin.append_left]
    | succ i' =>
      -- Value is `nVec 0 + (value over the tail)`: lands in the right part.
      have hpos : Fin.cast (Fin.sum_univ_succ (fun i => nVec i))
          (finSigmaFinEquiv (⟨i'.succ, j⟩ : (i : Fin (ℓ+1)) × Fin (nVec i)))
            = Fin.natAdd (nVec 0)
                (finSigmaFinEquiv (⟨i', j⟩ : (i : Fin ℓ) × Fin (nVec i.succ))) := by
        apply Fin.ext
        simp only [Fin.val_cast, Fin.val_natAdd]
        rw [finSigmaFinEquiv_apply, finSigmaFinEquiv_apply]
        -- prefix-sum: `∑_{x < i'+1} nVec(castLE x) = nVec 0 + ∑_{x<i'} nVec((castLE x).succ)`
        -- Convert both Fin-sums to range-sums over explicit nat bounds.
        rw [Finset.sum_fin_eq_sum_range, Finset.sum_fin_eq_sum_range]
        simp only [Fin.val_succ]
        -- Key prefix-sum identity (in range form):
        have hkey : (∑ k ∈ Finset.range (i'.val + 1),
              if h : k < i'.val + 1 then nVec (Fin.castLE (by omega) ⟨k, h⟩) else 0)
            = nVec 0 + ∑ k ∈ Finset.range i'.val,
              if h : k < i'.val then nVec (Fin.castLE (by omega) ⟨k, h⟩).succ else 0 := by
          rw [Finset.sum_range_succ' _ i'.val]
          rw [add_comm]
          have hlead : (if h : 0 < i'.val + 1 then nVec (Fin.castLE (by omega) ⟨0, h⟩) else 0)
              = nVec 0 := by
            rw [dif_pos (Nat.succ_pos _)]
            congr 1
          rw [hlead]
          congr 1
          apply Finset.sum_congr rfl
          intro x hx
          simp only [Finset.mem_range] at hx
          rw [dif_pos (by omega), dif_pos hx]
          congr 1
        rw [hkey, add_assoc]
      rw [hpos, Fin.append_right, hflatTail]
      beta_reduce
      rw [Equiv.symm_apply_apply]

/-- **Helper A (proof of Theorem 2.2)**: `T^⊗(nm)` equals the constant
    `m`-fold block tensor of `T^⊗n`.

    This is the "type-level" identification: viewing
    `tensorPow (n*m) T = tprod F (fun _ : Fin (n*m) => T)` as the iterated
    glue (via `TensorPower.mulEquiv` aka `tensorPowerAdd.symm`) of
    `m` copies of `tensorPow n T`.

    Proof: at the `tprod`-level, both sides reduce to
    `tprod F (fun _ : Fin (n*m) => T)` (after `TensorPower.cast`).
    The constant-`T` `tensorPowerBlock` produces `tprod F (Fin.repeat-of-T)`
    which `TensorPower.cast_tprod` then identifies with the constant `tprod`. -/
private lemma tensorPow_eq_tensorPowerBlockConstMulti
    (T : V) (n : ℕ+) (m : ℕ+) :
    tensorPow (F := F) (V := V) (n * m) T =
      tensorPowerBlockConstMulti (F := F) (V := V) n m
        (fun _ : Fin m => tensorPow n T) := by
  -- Apply the apply lemma to unfold `tensorPowerBlockConstMulti`.
  rw [tensorPowerBlockConstMulti_apply]
  -- Apply the structural lemma `tensorPowerBlock_const_tprod` with `nVec = const n`
  -- and `T : V` (already a constant index).
  unfold tensorPow
  rw [tensorPowerBlock_const_tprod (F := F) (V := V) T (fun _ : Fin m => (n : ℕ))]
  -- Now goal: `tprod F (const T over Fin (n*m).val) =
  --           cast (∑ Fin m, n = (n*m).val) (tprod F (const T over Fin (∑ Fin m, n)))`.
  -- After cast_tprod, both are tprod of constant functions, which are equal.
  rw [TensorPower.cast_tprod]
  -- Goal: tprod (const T) = tprod ((const T) ∘ Fin.cast _).
  -- The composition of a constant function is still constant.
  rfl

/-- **Helper (nonzero tensor power)**: over a field, `T ≠ 0` implies
    `tensorPow n T ≠ 0`.

    This is the standard fact that the `n`-th tensor power of a nonzero vector
    is nonzero (here `tensorPow n T = ⨂[F] (fun _ : Fin n => T)`). It is used to
    discharge the `t = ∅` corner of `F_tensorPow_nm_le_pm_max_block_apply`
    (Theorem 2.2): the corner fires exactly when the decomposition forces
    `tensorPow n T = 0`, which contradicts `T ≠ 0`.

    **Proof**: `T ≠ 0` over a field gives a coordinate functional
    `φ : V →ₗ[F] F` with `φ T ≠ 0` (via `Module.finBasis`). The multilinear map
    `v ↦ ∏ i, φ (v i)` lifts (`PiTensorProduct.lift`) to a linear map sending
    `tprod (fun _ => T) ↦ (φ T)^n ≠ 0`, so `tprod (fun _ => T) ≠ 0`. -/
lemma tensorPow_ne_zero (T : V) (n : ℕ+) (hT : T ≠ 0) :
    tensorPow (F := F) (V := V) n T ≠ 0 := by
  classical
  -- Step 1: a coordinate functional `φ : V →ₗ[F] F` with `φ T ≠ 0`.
  obtain ⟨φ, hφ⟩ : ∃ φ : V →ₗ[F] F, φ T ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    -- If every linear functional kills T, then T = 0 (using a basis: each
    -- `Basis.coord i` is a linear functional, and `forall_coord_eq_zero_iff`).
    apply hT
    set b := Module.finBasis F V with hb_def
    exact (b.forall_coord_eq_zero_iff).mp (fun i => hcon (b.coord i))
  -- Step 2: the multilinear map `v ↦ ∏ i, φ (v i)`.
  set M : MultilinearMap F (fun _ : Fin (n : ℕ) => V) F :=
    (MultilinearMap.mkPiAlgebra F (Fin (n : ℕ)) F).compLinearMap (fun _ => φ) with hM_def
  -- Step 3: `lift M (tensorPow n T) = (φ T)^n ≠ 0`.
  have hval : (PiTensorProduct.lift M) (tensorPow (F := F) (V := V) n T) = (φ T) ^ (n : ℕ) := by
    unfold tensorPow
    rw [PiTensorProduct.lift.tprod]
    simp [hM_def, MultilinearMap.mkPiAlgebra_apply, Finset.prod_const]
  have hne : (PiTensorProduct.lift M) (tensorPow (F := F) (V := V) n T) ≠ 0 := by
    rw [hval]
    exact pow_ne_zero _ hφ
  intro hzero
  apply hne
  rw [hzero, map_zero]

/-- **Multi-index expansion identity** (proof of Theorem 2.2).

    Quotes Theorem 2.2 verbatim:
      `T^⊗(nm) = ∑_{i_1, …, i_m ∈ [p(n)]} ⊗_{j=1}^m α_{i_j} S_{i_j}^⊗n`.

    The RHS uses `blockTensorOfMultiIndex n S I` for the `m`-fold block tensor
    `⊗_{j=1}^m S(I j)^⊗n`, and factors out the scalar `∏_j α(I j)` (from
    multilinearity of the tensor product).

    **Proof structure**: Reduce to multilinearity of `tensorPowerBlockConstMulti`
    via the bridge `tensorPow_eq_tensorPowerBlockConstMulti` (Helper A).
    Substitute the decomposition `tensorPow n T = ∑_i α_i • tensorPow n (S i)`
    and apply `MultilinearMap.map_sum` + `MultilinearMap.map_smul_univ` to
    obtain the multi-index sum. The bridge to `blockTensorOfMultiIndex` is
    definitional via `blockTensorOfMultiIndex_eq_constMulti`. -/
lemma tensorPow_nm_eq_multiIndex_sum
    (T : V) (n : ℕ+) {p : ℕ} (S : Fin p → V) (α : Fin p → F)
    (hdecomp : tensorPow (F := F) (V := V) n T = ∑ i, α i • tensorPow n (S i))
    (m : ℕ+) :
    tensorPow (F := F) (V := V) (n * m) T =
      ∑ I : Fin m → Fin p,
        (∏ j : Fin m, α (I j)) •
          blockTensorOfMultiIndex (F := F) (V := V) n S I := by
  classical
  -- Theorem 2.2: structural multi-index expansion identity.
  -- Step 1 (Helper A): bridge `tensorPow (n*m) T` to the constant
  -- `m`-fold block tensor of `tensorPow n T`.
  rw [tensorPow_eq_tensorPowerBlockConstMulti (F := F) (V := V) T n m]
  -- Step 2: substitute the decomposition `tensorPow n T = ∑_i α_i • tensorPow n (S i)`.
  have hconst :
      (fun _ : Fin m => tensorPow (F := F) (V := V) n T) =
        fun _ : Fin m => ∑ i : Fin p, α i • tensorPow n (S i) := by
    funext _; exact hdecomp
  rw [hconst]
  -- Step 3: apply `MultilinearMap.map_sum` to expand the `∑_i` inside each slot
  -- across all `m` slots, getting a sum over multi-indices `I : Fin m → Fin p`.
  rw [(tensorPowerBlockConstMulti (F := F) (V := V) n m).map_sum
        (g := fun (_ : Fin m) (i : Fin p) => α i • tensorPow n (S i))]
  -- Goal: ∑ I, M (fun j => α (I j) • tensorPow n (S (I j))) =
  --       ∑ I, (∏ j, α (I j)) • blockTensorOfMultiIndex n S I.
  refine Finset.sum_congr rfl ?_
  intro I _
  -- Step 4: pull out the scalar `∏_j α(I j)` via `map_smul_univ`.
  rw [(tensorPowerBlockConstMulti (F := F) (V := V) n m).map_smul_univ
        (c := fun j => α (I j)) (m := fun j => tensorPow n (S (I j)))]
  -- Step 5: bridge `tensorPowerBlockConstMulti (fun j => tensorPow n (S (I j)))`
  -- to `blockTensorOfMultiIndex n S I` (definitional).
  rw [← blockTensorOfMultiIndex_eq_constMulti (F := F) (V := V) n S I]

/-- **Sub-helper 1 (Theorem 2.2)**: multi-index expansion + subadditivity
    + scalar invariance.

    Quotes Theorem 2.2:
      `T^⊗(nm) = ∑_{(i_1,…,i_m) ∈ [p(n)]^m} ⊗_{j=1}^m α_{i_j} S_{i_j}^⊗n`.
    Quotes Theorem 2.2:
      `F(T^⊗(nm)) ≤ p(n)^m max_I F(⊗_{j=1}^m S_{I j}^⊗n)`.

    Statement: `F_{nm}(T^⊗(nm)) ≤ p^m · iSup_I F_{nm}(block_I)` where
    `block_I = ⊗_j tensorPow n (S (I j))` via `blockTensorOfMultiIndex`.

    **Proof**: We use `tensorPow_nm_eq_multiIndex_sum` (the load-bearing
    multi-index expansion identity), then apply:
    1. `Func.subadd` iteratively over the `p^m` terms of the sum.
    2. `Func.scalar_inv` to drop the scalar `∏_j α(I j)` (in the nonzero
       case; the zero case bounds the term by `Func 0 ≤ max` separately).
    3. `Finset.sum_le_card_nsmul_max`-style bound to get `≤ p^m · max`. -/
lemma F_tensorPow_nm_le_pm_max_block_apply
    (Func : AdmissibleFunctional F V) (T : V) (hT : T ≠ 0)
    (n : ℕ+)
    {p : ℕ} (S : Fin p → V) (α : Fin p → F)
    (hdecomp : tensorPow (F := F) (V := V) n T = ∑ i, α i • tensorPow n (S i))
    (m : ℕ+) :
    ((Func.toFun (n * m) (tensorPow (F := F) (V := V) (n * m) T) : ℝ)) ≤
      ((p : ℝ) ^ (m : ℕ)) *
        ⨆ (I : Fin m → Fin p),
          ((Func.toFun (n * m)
            (blockTensorOfMultiIndex (F := F) (V := V) n S I)) : ℝ) := by
  -- Theorem 2.2. Multi-index expansion + subadd + scalar_inv.
  classical
  -- Step 1: Use the multi-index expansion identity (Theorem 2.2).
  -- `tensorPow (n*m) T = ∑_I (∏_j α(I j)) • blockTensorOfMultiIndex n S I`.
  have hexp := tensorPow_nm_eq_multiIndex_sum (F := F) (V := V) T n S α hdecomp m
  -- Notation for brevity.
  set block : (Fin m → Fin p) →
      TensorPower F ((n * m : ℕ+) : ℕ) V :=
    fun I => blockTensorOfMultiIndex (F := F) (V := V) n S I with hblock_def
  set scal : (Fin m → Fin p) → F :=
    fun I => ∏ j : Fin m, α (I j) with hscal_def
  -- Per-multi-index real value `F(block I)`.
  set Fblock : (Fin m → Fin p) → ℝ :=
    fun I => ((Func.toFun (n * m) (block I)) : ℝ) with hFblock_def
  -- Rewrite the goal LHS using `hexp`.
  rw [hexp]
  -- Filter the sum to nonzero scalars: zero-scalar terms contribute 0 to the
  -- sum and so dropping them preserves the value. This lets us bypass the
  -- (avoidable) `F(0) = 0` artifact in the subadd induction empty case.
  set t : Finset (Fin m → Fin p) :=
    (Finset.univ : Finset (Fin m → Fin p)).filter (fun I => scal I ≠ 0) with ht_def
  have hsum_t :
      (∑ I : (Fin m → Fin p), scal I • block I) =
        ∑ I ∈ t, scal I • block I := by
    rw [ht_def]
    refine (Finset.sum_filter_of_ne ?_).symm
    intro I _ hne
    -- If `scal I • block I ≠ 0`, then `scal I ≠ 0`.
    intro hα
    apply hne
    rw [hα, zero_smul]
  rw [hsum_t]
  -- Now LHS goal: `F_{nm}(∑_{I ∈ t} scal I • block I) ≤ p^m · iSup_I Fblock I`.
  -- Step 2 (subadd): bound `F(∑_{I ∈ t} ...) ≤ ∑_{I ∈ t} F(scal I • block I)`.
  -- We induct over Finset s ⊆ t, using subadd at each `insert` step. The
  -- empty case is handled by using a one-step `insert` form: we induct only
  -- on NONEMPTY s, and split off the `t = ∅` case separately.
  by_cases ht_empty : t = ∅
  · -- t = ∅ corner case (Theorem 2.2): this is IMPOSSIBLE when `T ≠ 0`.
    --
    -- `t = ∅` means every multi-index `I` has `scal I = ∏_j α(I j) = 0`. Taking
    -- the constant multi-index `I = fun _ => i` gives `α(i)^m = 0`, hence
    -- `α(i) = 0` for every `i`. So `α ≡ 0` and the decomposition `hdecomp`
    -- gives `tensorPow n T = ∑ 0 • _ = 0`. But `tensorPow_ne_zero` (over a
    -- field, `T ≠ 0`) says `tensorPow n T ≠ 0`. Contradiction.
    --
    -- This matches the paper's use of a linearly-independent (minimal)
    -- decomposition with all `α_i ≠ 0`; `F_n(0) = 0` is never invoked.
    exfalso
    -- Every multi-index `I` has `scal I = 0`.
    have hscal_zero : ∀ I : Fin m → Fin p, scal I = 0 := by
      intro I
      by_contra hne
      have hI_mem : I ∈ t := by
        rw [ht_def, Finset.mem_filter]
        exact ⟨Finset.mem_univ I, hne⟩
      rw [ht_empty] at hI_mem
      exact absurd hI_mem (Finset.notMem_empty I)
    -- For each `i`, the constant multi-index gives `α i ^ m = 0`, so `α i = 0`.
    have hα_zero : ∀ i : Fin p, α i = 0 := by
      intro i
      have hconst := hscal_zero (fun _ => i)
      rw [hscal_def] at hconst
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hconst
      exact pow_eq_zero_iff m.pos.ne' |>.mp hconst
    -- Then `tensorPow n T = ∑ α i • tensorPow n (S i) = 0`.
    have htp_zero : tensorPow (F := F) (V := V) n T = 0 := by
      rw [hdecomp]
      refine Finset.sum_eq_zero ?_
      intro i _
      rw [hα_zero i, zero_smul]
    exact tensorPow_ne_zero T n hT htp_zero
  · -- t ≠ ∅: standard case.
    have ht_empty : t.Nonempty := Finset.nonempty_iff_ne_empty.mpr ht_empty
    -- Subadd induction over Finset.Nonempty (so we never hit the F(0) case).
    have hsubadd : ∀ (s : Finset (Fin m → Fin p)), s.Nonempty →
        ((Func.toFun (n * m) (∑ I ∈ s, scal I • block I) : ℝ)) ≤
          ∑ I ∈ s, ((Func.toFun (n * m) (scal I • block I) : ℝ)) := by
      intro s hs
      induction hs using Finset.Nonempty.cons_induction with
      | singleton I =>
        rw [Finset.sum_singleton, Finset.sum_singleton]
      | cons I s hIs hsne ih =>
        rw [Finset.sum_cons, Finset.sum_cons]
        have hadd := Func.subadd (n * m) (scal I • block I)
          (∑ J ∈ s, scal J • block J)
        have hadd_R : ((Func.toFun (n * m)
            (scal I • block I + ∑ J ∈ s, scal J • block J)) : ℝ) ≤
              ((Func.toFun (n * m) (scal I • block I)) : ℝ) +
                ((Func.toFun (n * m) (∑ J ∈ s, scal J • block J)) : ℝ) := by
          have := NNReal.coe_le_coe.mpr hadd
          simpa [NNReal.coe_add] using! this
        linarith [hadd_R, ih]
    have hsubadd_t := hsubadd t ht_empty
    -- Step 3 (scalar_inv): for I ∈ t, scal I ≠ 0, so F(scal I • block I) = F(block I).
    have hscalar : ∀ I ∈ t,
        ((Func.toFun (n * m) (scal I • block I) : ℝ)) =
          ((Func.toFun (n * m) (block I) : ℝ)) := by
      intro I hI
      have hα : scal I ≠ 0 := (Finset.mem_filter.mp hI).2
      congr 1
      rw [Func.scalar_inv (n * m) (scal I) hα (block I)]
    -- Step 4: replace each `F(scal I • block I)` by `F(block I)`, then bound.
    have hsum_eq_F : ∑ I ∈ t, ((Func.toFun (n * m) (scal I • block I) : ℝ)) =
        ∑ I ∈ t, Fblock I := by
      refine Finset.sum_congr rfl ?_
      intro I hI
      exact hscalar I hI
    -- Combine subadd + scalar identity.
    have hstep1 : ((Func.toFun (n * m)
        (∑ I ∈ t, scal I • block I)) : ℝ) ≤
          ∑ I ∈ t, Fblock I := by
      rw [← hsum_eq_F]; exact hsubadd_t
    -- Step 5: bound `∑_{I ∈ t} Fblock I ≤ p^m · iSup_I Fblock I`.
    -- Cardinality: |t| ≤ |Finset.univ| = p^m.
    have hcard_univ : (Finset.univ : Finset (Fin m → Fin p)).card = p ^ (m : ℕ) := by
      rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
    have ht_card_le : t.card ≤ p ^ (m : ℕ) := by
      rw [← hcard_univ]; exact Finset.card_le_univ t
    -- Need p > 0 for the iSup to be over nonempty.
    -- Since t is nonempty, there exists I ∈ t, so Fin m → Fin p is nonempty,
    -- so p > 0 (else Fin m → Fin 0 is empty).
    obtain ⟨I₀, hI₀⟩ := ht_empty
    have hI₀_univ : I₀ ∈ (Finset.univ : Finset (Fin m → Fin p)) := Finset.mem_univ _
    have hp_pos : 0 < p := by
      by_contra hp_neg
      push_neg at hp_neg
      interval_cases p
      exact (I₀ ⟨0, m.pos⟩).elim0
    haveI : Nonempty (Fin p) := ⟨⟨0, hp_pos⟩⟩
    haveI : Nonempty (Fin m → Fin p) := ⟨fun _ => ⟨0, hp_pos⟩⟩
    have hbdd : BddAbove (Set.range Fblock) := Set.Finite.bddAbove (Set.toFinite _)
    have hFblock_le_iSup : ∀ I, Fblock I ≤ ⨆ J, Fblock J :=
      fun I => le_ciSup hbdd I
    have hsum_bnd : ∑ I ∈ t, Fblock I ≤ t.card • (⨆ J, Fblock J) := by
      refine (Finset.sum_le_sum (s := t) (fun I _ => hFblock_le_iSup I)).trans ?_
      rw [Finset.sum_const]
    -- iSup is nonneg, so (t.card • iSup) ≤ (p^m • iSup).
    have hiSup_nn : 0 ≤ (⨆ J, Fblock J) := by
      refine le_ciSup_of_le hbdd I₀ ?_
      exact NNReal.coe_nonneg _
    have hcard_nsmul_le : t.card • (⨆ J, Fblock J) ≤
        (p ^ (m : ℕ)) • (⨆ J, Fblock J) :=
      nsmul_le_nsmul_left hiSup_nn ht_card_le
    -- Bring it together.
    calc ((Func.toFun (n * m)
            (∑ I ∈ t, scal I • block I)) : ℝ)
        ≤ ∑ I ∈ t, Fblock I := hstep1
      _ ≤ t.card • (⨆ J, Fblock J) := hsum_bnd
      _ ≤ (p ^ (m : ℕ)) • (⨆ J, Fblock J) := hcard_nsmul_le
      _ = ((p : ℝ) ^ (m : ℕ)) * (⨆ J, Fblock J) := by
          rw [nsmul_eq_mul]
          push_cast
          ring

/-- **Sub-helper 2 (Theorem 2.2)**: perm_inv rearrangement + iterated
    submul. For a fixed multi-index `I : Fin m → Fin p`,
    `F(⊗_j S(I j)^⊗n)` is bounded by `∏ᵢ F(Sᵢ^⊗(mᵢ(I)·n))` (with the
    convention that factors at `i` with `mᵢ(I) = 0` contribute `1`).

    Quotes Theorem 2.2 (perm_inv): rearrange the factors so that all
    `S(I j) = Sᵢ` factors are grouped together at position `i`. The
    resulting block has block-sizes `(mᵢ · n)_{i=1}^p` summing to `m · n`.
    Quotes Theorem 2.2 (iterated submul):
      `F(⊗_i Sᵢ^⊗(mᵢ n)) ≤ ∏_i F(Sᵢ^⊗(mᵢ n))`.

    **Grouping equal factors.**
    1. Use `Func.perm_inv` with the constant block-size vector
       `fun _ : Fin m => n` and a permutation sorting indices by `I j`.
    2. After permutation, regroup consecutive same-index blocks via
       iterated `Func.submul` (or via a sort-based `tensorPowerBlock`
       cast).
    3. The result is `∏_i F(Sᵢ^⊗(mᵢ·n))`, with `mᵢ = 0` factors
       absorbing to `1` (the empty product / `tensorPow 0` neutral). -/
private lemma F_block_grouped_sorting_perm_exists
    (n : ℕ+) {p : ℕ} (S : Fin p → V) {m : ℕ+} (I : Fin m → Fin p) :
    ∃ σ : Equiv.Perm (Fin m),
      ∀ i : Fin p,
        (Finset.univ.filter (fun j : Fin m => I (σ j) = i)).card =
          (Finset.univ.filter (fun j : Fin m => I j = i)).card := by
  /- Theorem 2.2. Construct `σ` by sorting the finite list
     `j : Fin m` by the key `I j : Fin p`, preserving the cardinality of
     every fiber. This is the permutation used with `Func.perm_inv` for the
     constant block-size vector `fun _ => n`. -/
  classical
  refine ⟨Tuple.sort I, fun i => ?_⟩
  rw [← Fintype.card_subtype, ← Fintype.card_subtype]
  exact Fintype.card_congr
    { toFun := fun j => ⟨Tuple.sort I j.1, j.2⟩
      invFun := fun j => ⟨(Tuple.sort I).symm j.1, by simpa using! j.2⟩
      left_inv := by
        intro j
        ext
        simp
      right_inv := by
        intro j
        ext
        simp }

private lemma AdmissibleFunctional.toFun_tensorPower_cast
    (Func : AdmissibleFunctional F V) {a b : ℕ} (h : a = b) (ha : 0 < a)
    (T : TensorPower F a V) :
    Func.toFun ⟨b, by simpa [← h] using! ha⟩ ((TensorPower.cast F V h) T) =
      Func.toFun ⟨a, ha⟩ T := by
  subst h
  simp

omit [Module.Finite F V] in
/-- **Single-factor block reduction**: a `tensorPowerBlock` over `Fin 1` with
    block-size function `nV` and single entry `Ts` equals `Ts 0` modulo the
    canonical `TensorPower.cast` for `∑ _ : Fin 1, nV = nV 0`.

    Reusable engineering helper for the `ℓ = 1` base of iterated `Func.submul`
    over a block (Theorem 2.2). -/
private lemma tensorPowerBlock_fin_one
    (nV : Fin 1 → ℕ) (Ts : ∀ j : Fin 1, TensorPower F (nV j) V) :
    tensorPowerBlock F V nV Ts =
      (TensorPower.cast F V (by simp : nV 0 = ∑ j : Fin 1, nV j)) (Ts 0) := by
  show tensorPowerBlock F V nV Ts = _
  -- Unfold the (0+1) step: `cast (mulEquiv (Ts 0 ⊗ empty-block))`; the empty
  -- tail block is `algebraMap₀ 1 = GOne.one`. After collapsing the casts over
  -- equal levels (`∑ Fin 0 = 0`, `nV 0 + 0 = nV 0`), this is graded `mul_one`.
  apply (TensorPower.cast F V (by simp : ∑ j : Fin 1, nV j = nV 0)).injective
  simp only [tensorPowerBlock, TensorPower.algebraMap₀_one, ← TensorPower.gMul_def,
    TensorPower.cast_refl, LinearEquiv.refl_apply, Fin.sum_univ_zero]
  -- Goal (modulo the identity refls): `GMul.mul (Ts 0) GOne.one = Ts 0`.
  have hmo := TensorPower.mul_one (R := F) (M := V) (Ts 0)
  rw [TensorPower.cast_refl] at hmo
  exact hmo

/-- **Helper: `∑ _ : Fin (a+b), n = ∑ _ : Fin a, n + ∑ _ : Fin b, n`.** -/
private lemma sum_const_fin_add (n : ℕ) (a b : ℕ) :
    ∑ _ : Fin (a + b), n = (∑ _ : Fin a, n) + (∑ _ : Fin b, n) := by
  simp [Finset.sum_const, Finset.card_univ, add_mul]

/-- **Cast pushes through the right factor of graded multiplication.** -/
private lemma gMul_cast_right {na nb nb' : ℕ} (h : nb = nb')
    (x : TensorPower F na V) (y : TensorPower F nb V) :
    TensorPower.mulEquiv (x ⊗ₜ[F]
        (TensorPower.cast F V h : _ ≃ₗ[F] TensorPower F nb' V) y) =
      (TensorPower.cast F V (by rw [h] : na + nb = na + nb'))
        (TensorPower.mulEquiv (x ⊗ₜ[F] y)) := by
  subst h
  simp only [TensorPower.cast_refl, LinearEquiv.refl_apply]

/-- **Cast pushes through the left factor of graded multiplication.** -/
private lemma gMul_cast_left {na na' nb : ℕ} (h : na = na')
    (x : TensorPower F na V) (y : TensorPower F nb V) :
    TensorPower.mulEquiv (((TensorPower.cast F V h : _ ≃ₗ[F] TensorPower F na' V) x) ⊗ₜ[F] y) =
      (TensorPower.cast F V (by rw [h] : na + nb = na' + nb))
        (TensorPower.mulEquiv (x ⊗ₜ[F] y)) := by
  subst h
  simp only [TensorPower.cast_refl, LinearEquiv.refl_apply]

/-- **Reindex a constant-`n` block along an index equality `h : a = a'`.**
    `tensorPowerBlock` of `g ∘ Fin.cast h.symm` (a `Fin a' → _` family) equals
    the cast of `tensorPowerBlock` of `g` (a `Fin a → _` family). Both block
    sizes are the constant `n`, so there is no per-index cast. -/
private lemma tensorPowerBlock_const_cast_arg (n : ℕ) {a a' : ℕ} (h : a = a')
    (g : Fin a → TensorPower F n V) :
    tensorPowerBlock F V (fun _ : Fin a' => n)
        (fun i : Fin a' => g (Fin.cast h.symm i)) =
      (TensorPower.cast F V (by subst h; rfl :
        ∑ _ : Fin a, n = ∑ _ : Fin a', n))
        (tensorPowerBlock F V (fun _ : Fin a => n) g) := by
  subst h
  simp only [Fin.cast_eq_self, TensorPower.cast_refl, LinearEquiv.refl_apply]

/-- **`tensorPowerBlock` append/associativity at constant block size
    (reusable core, Theorem 2.2)**: for a uniform block size `n`, the
    block of `a+b` factors splits as `TensorPower.mulEquiv` of the first-`a`
    block and the last-`b` block (cast across `(a+b)·n = a·n + b·n`).

    Proof by induction on the length `a` of the first segment. The base case
    `a = 0` collapses the empty left block to the unit (`one_mul`). The
    inductive step peels index `0` (which lands in the first segment) and
    recurses on the tail, reassociating the `mulEquiv` glue. -/
private lemma tensorPowerBlock_const_append (n : ℕ) :
    ∀ {a b : ℕ} (g : Fin (a + b) → TensorPower F n V),
      tensorPowerBlock F V (fun _ : Fin (a + b) => n) g =
        (TensorPower.cast F V (sum_const_fin_add n a b).symm)
          (TensorPower.mulEquiv
            ((tensorPowerBlock F V (fun _ : Fin a => n)
                (fun i : Fin a => g (Fin.castAdd b i))) ⊗ₜ[F]
              (tensorPowerBlock F V (fun _ : Fin b => n)
                (fun i : Fin b => g (Fin.natAdd a i)))))
  | 0, b, g => by
      -- Left block is empty (= unit). `mulEquiv (unit ⊗ blockB) = unit ₜ* blockB`,
      -- which collapses to `blockB` by `one_mul`. The reindexing `g ∘ natAdd 0 = g`
      -- (modulo `Fin.cast (zero_add b)`) is handled by `tensorPowerBlock_const_cast_arg`.
      -- Rewrite the LHS `block over Fin (0+b) g` as the cast of `block over Fin b (g∘natAdd 0)`.
      have hLHS :
          tensorPowerBlock F V (fun _ : Fin (0 + b) => n) g =
            (TensorPower.cast F V (by simp :
              ∑ _ : Fin b, n = ∑ _ : Fin (0 + b), n))
              (tensorPowerBlock F V (fun _ : Fin b => n)
                (fun i : Fin b => g (Fin.natAdd 0 i))) := by
        have := tensorPowerBlock_const_cast_arg (F := F) (V := V) n
          (a := b) (a' := 0 + b) (by simp) (fun i : Fin b => g (Fin.natAdd 0 i))
        rw [← this]
        congr 1
        funext i
        simp [Fin.natAdd_zero]
      rw [hLHS]
      -- Right side: collapse the empty left block to the unit and use `one_mul`.
      have hblockA :
          tensorPowerBlock F V (fun _ : Fin 0 => n) (fun i : Fin 0 => g (Fin.castAdd b i)) =
            (TensorPower.cast F V (by simp : (0 : ℕ) = ∑ _i : Fin 0, n))
              (TensorPower.algebraMap₀ (1 : F)) := rfl
      rw [hblockA]
      set B := tensorPowerBlock F V (fun _ : Fin b => n)
        (fun i : Fin b => g (Fin.natAdd 0 i)) with hB
      -- Now both sides are casts of `B`; reduce via `one_mul`.
      apply (TensorPower.cast F V (sum_const_fin_add n 0 b)).injective
      rw [TensorPower.cast_cast, TensorPower.cast_cast]
      simp only [TensorPower.algebraMap₀_one, TensorPower.cast_refl, LinearEquiv.refl_apply,
        ← TensorPower.gMul_def]
      -- Goal: `cast h B = GMul.mul (refl ₜ1) B = ₜ1 ₜ* B`. Use `one_mul`.
      have hom := TensorPower.one_mul (R := F) (M := V) B
      rw [TensorPower.gMul_def, TensorPower.gOne_def] at hom
      change (TensorPower.cast F V _) B =
        TensorPower.mulEquiv ((PiTensorProduct.tprod F) Fin.elim0 ⊗ₜ[F] B)
      have hom2 : TensorPower.mulEquiv ((PiTensorProduct.tprod F) Fin.elim0 ⊗ₜ[F] B) =
          (TensorPower.cast F V (zero_add _)).symm B := by
        apply (TensorPower.cast F V (zero_add _)).injective
        rw [LinearEquiv.apply_symm_apply]; exact hom
      rw [hom2, TensorPower.cast_symm]
  | a + 1, b, g => by
      -- Transport the block over `Fin (a+1+b)` to `Fin ((a+b)+1)` (head `succ`),
      -- where `tensorPowerBlock` unfolds by peeling index 0.
      have hlen : (a + b) + 1 = a + 1 + b := by omega
      -- `g' : Fin ((a+b)+1) → _` is `g` reindexed.
      set g' : Fin ((a + b) + 1) → TensorPower F n V :=
        fun i => g (Fin.cast hlen i) with hg'
      have hLHS :
          tensorPowerBlock F V (fun _ : Fin (a + 1 + b) => n) g =
            (TensorPower.cast F V (by simp [hlen] :
              ∑ _ : Fin ((a + b) + 1), n = ∑ _ : Fin (a + 1 + b), n))
              (tensorPowerBlock F V (fun _ : Fin ((a + b) + 1) => n) g') := by
        have hcast := tensorPowerBlock_const_cast_arg (F := F) (V := V) n
          (a := (a + b) + 1) (a' := a + 1 + b) hlen g'
        rw [← hcast]
        rfl
      rw [hLHS]
      -- Unfold the head-`succ` block on the LHS.
      conv_lhs => rw [show tensorPowerBlock F V (fun _ : Fin ((a+b)+1) => n) g' =
        (TensorPower.cast F V (Fin.sum_univ_succ (fun _ : Fin ((a+b)+1) => n)).symm)
          (TensorPower.mulEquiv (g' 0 ⊗ₜ[F]
            tensorPowerBlock F V (fun _ : Fin (a+b) => n)
              (fun i : Fin (a+b) => g' i.succ))) from rfl]
      -- Apply the inductive hypothesis to the tail `g' ∘ succ`.
      rw [tensorPowerBlock_const_append n (a := a) (b := b)
        (fun i : Fin (a+b) => g' i.succ)]
      -- Unfold the head-`succ` block `blockA` on the RHS.
      conv_rhs => rw [show tensorPowerBlock F V (fun _ : Fin (a+1) => n)
          (fun i : Fin (a+1) => g (Fin.castAdd b i)) =
        (TensorPower.cast F V (Fin.sum_univ_succ (fun _ : Fin (a+1) => n)).symm)
          (TensorPower.mulEquiv ((g (Fin.castAdd b 0)) ⊗ₜ[F]
            tensorPowerBlock F V (fun _ : Fin a => n)
              (fun i : Fin a => g (Fin.castAdd b i.succ)))) from rfl]
      -- Reindex the inner block families so both sides agree term-by-term.
      have q0 : Fin.cast hlen (0 : Fin ((a+b)+1)) = Fin.castAdd b (0 : Fin (a+1)) := by
        ext; simp
      have q1 : ∀ i : Fin a,
          Fin.cast hlen ((Fin.castAdd b i).succ) = Fin.castAdd b i.succ := fun i => by
        ext; simp
      have q2 : ∀ i : Fin b,
          Fin.cast hlen ((Fin.natAdd a i).succ) = Fin.natAdd (a+1) i := fun i => by
        ext; simp [Fin.natAdd]; omega
      have hgg0 : g' 0 = g (Fin.castAdd b 0) := by rw [hg']; simp only []; rw [q0]
      have hggA : (fun i : Fin a => g' (Fin.castAdd b i).succ) =
          (fun i : Fin a => g (Fin.castAdd b i.succ)) := by
        funext i; rw [hg']; simp only []; rw [q1]
      have hggB : (fun i : Fin b => g' (Fin.natAdd a i).succ) =
          (fun i : Fin b => g (Fin.natAdd (a+1) i)) := by
        funext i; rw [hg']; simp only []; rw [q2]
      rw [hgg0, hggA, hggB]
      -- Abbreviate the three building blocks.
      set X := g (Fin.castAdd b (0 : Fin (a+1))) with hX
      set A := tensorPowerBlock F V (fun _ : Fin a => n)
        (fun i : Fin a => g (Fin.castAdd b i.succ)) with hA
      set B := tensorPowerBlock F V (fun _ : Fin b => n)
        (fun i : Fin b => g (Fin.natAdd (a+1) i)) with hB
      -- Push the inner casts out of the `mulEquiv` factors on both sides.
      rw [gMul_cast_right (F := F) (V := V) (sum_const_fin_add n a b).symm X
        (TensorPower.mulEquiv (A ⊗ₜ[F] B))]
      rw [gMul_cast_left (F := F) (V := V) (Fin.sum_univ_succ (fun _ : Fin (a+1) => n)).symm
        (TensorPower.mulEquiv (X ⊗ₜ[F] A)) B]
      -- Convert `mulEquiv (· ⊗ ·)` to graded multiplication `ₜ*` and use `mul_assoc`.
      simp only [← TensorPower.gMul_def, TensorPower.cast_cast]
      rw [← TensorPower.mul_assoc X A B]
      rw [TensorPower.cast_cast, TensorPower.cast_eq_cast]

/-- **General block submultiplicativity (Theorem 2.2, iterated `Func.submul`)**:
    for a block tensor `T_1 ⊗ ⋯ ⊗ T_ℓ` assembled by `tensorPowerBlock` from
    pieces `Ts j : TensorPower F (nVec j) V` (with positive `ℕ+` block sizes),
    the admissible functional is submultiplicative:
    `F(T_1 ⊗ ⋯ ⊗ T_ℓ) ≤ ∏_j F(T_j)`.

    This is the reusable iterated-`submul` engine: it follows by induction on
    the block count `ℓ`, applying `Func.submul` to peel off the first factor at
    each step. Used for the sorted-run regrouping bound (Theorem 2.2). -/
private lemma Func_tensorPowerBlock_le_prod
    (Func : AdmissibleFunctional F V) :
    ∀ {ℓ : ℕ} (nVec : Fin ℓ → ℕ+)
      (Ts : ∀ j : Fin ℓ, TensorPower F ((nVec j : ℕ)) V)
      (hpos : 0 < ∑ j, ((nVec j : ℕ))),
      ((Func.toFun ⟨∑ j, ((nVec j : ℕ)), hpos⟩
        (tensorPowerBlock F V (fun j => (nVec j : ℕ)) Ts)) : ℝ)
        ≤ ∏ j, ((Func.toFun (nVec j) (Ts j)) : ℝ)
  | 0, nVec, Ts, hpos => by
      exact absurd hpos (by simp)
  | 1, nVec, Ts, hpos => by
      -- Single block: the block tensor equals `Ts 0` (modulo cast), product is `F(Ts 0)`.
      have hsum : ∑ j : Fin 1, ((nVec j : ℕ)) = (nVec 0 : ℕ) := by simp
      rw [Fin.prod_univ_one]
      -- `tensorPowerBlock` of one factor is `cast (Ts 0)`; reduce via the helper.
      have hblock1 :
          ((Func.toFun ⟨∑ j : Fin 1, ((nVec j : ℕ)), hpos⟩
            (tensorPowerBlock F V (fun j => (nVec j : ℕ)) Ts)) : ℝ) =
            ((Func.toFun (nVec 0) (Ts 0)) : ℝ) := by
        rw [tensorPowerBlock_fin_one (F := F) (V := V) (fun j => (nVec j : ℕ)) Ts]
        have hc := AdmissibleFunctional.toFun_tensorPower_cast (F := F) (V := V) Func
          (by simp : (nVec 0 : ℕ) = ∑ j : Fin 1, ((nVec j : ℕ))) (nVec 0).pos (Ts 0)
        rw [hc]
        congr 1
      rw [hblock1]
  | ℓ + 2, nVec, Ts, hpos => by
      -- Peel off the first block factor and apply `Func.submul`, then IH on the tail.
      set tail : Fin (ℓ + 1) → ℕ+ := fun i => nVec i.succ with htail
      set Tstail : ∀ j : Fin (ℓ + 1), TensorPower F ((tail j : ℕ)) V :=
        fun j => Ts j.succ with hTstail
      have hsum_succ : ∑ j, ((nVec j : ℕ)) = (nVec 0 : ℕ) + ∑ i, ((tail i : ℕ)) :=
        Fin.sum_univ_succ (fun j => (nVec j : ℕ))
      have htailpos : 0 < ∑ i, ((tail i : ℕ)) := by
        have : (tail 0 : ℕ) ≤ ∑ i, ((tail i : ℕ)) :=
          Finset.single_le_sum (f := fun i => ((tail i : ℕ)))
            (by intro i _; positivity) (Finset.mem_univ 0)
        exact lt_of_lt_of_le (tail 0).pos this
      -- Step 1: unfold the (ℓ+1) block as cast (mulEquiv (Ts 0 ⊗ tail-block)).
      have hblock :
          tensorPowerBlock F V (fun j => (nVec j : ℕ)) Ts =
            (TensorPower.cast F V (Fin.sum_univ_succ (fun j => (nVec j : ℕ))).symm)
              (TensorPower.mulEquiv
                ((Ts 0) ⊗ₜ[F]
                  tensorPowerBlock F V (fun i => (tail i : ℕ)) Tstail)) := by
        rfl
      -- Step 2: push Func through the cast.
      have hcast :
          ((Func.toFun ⟨∑ j, ((nVec j : ℕ)), hpos⟩
            (tensorPowerBlock F V (fun j => (nVec j : ℕ)) Ts)) : ℝ) =
            ((Func.toFun ⟨(nVec 0 : ℕ) + ∑ i, ((tail i : ℕ)),
                by rw [← hsum_succ]; exact hpos⟩
              (TensorPower.mulEquiv
                ((Ts 0) ⊗ₜ[F]
                  tensorPowerBlock F V (fun i => (tail i : ℕ)) Tstail))) : ℝ) := by
        rw [hblock]
        congr 1
        exact AdmissibleFunctional.toFun_tensorPower_cast (F := F) (V := V) Func
          (Fin.sum_univ_succ (fun j => (nVec j : ℕ))).symm
          (by rw [← hsum_succ]; exact hpos) _
      rw [hcast]
      -- Step 3: `mulEquiv = (tensorPowerAdd ...).symm`, apply submul.
      have hmulEquiv :
          TensorPower.mulEquiv
              ((Ts 0) ⊗ₜ[F]
                tensorPowerBlock F V (fun i => (tail i : ℕ)) Tstail) =
            (tensorPowerAdd F V (nVec 0 : ℕ) (∑ i, ((tail i : ℕ)))).symm
              ((Ts 0) ⊗ₜ[F]
                tensorPowerBlock F V (fun i => (tail i : ℕ)) Tstail) := by
        rfl
      have hsubmul :=
        Func.submul (nVec 0) ⟨∑ i, ((tail i : ℕ)), htailpos⟩
          (Ts 0) (tensorPowerBlock F V (fun i => (tail i : ℕ)) Tstail)
      -- Reconcile the submul index `⟨(nVec 0) + ∑ tail, _⟩` with our level.
      have hstep :
          ((Func.toFun ⟨(nVec 0 : ℕ) + ∑ i, ((tail i : ℕ)),
              by rw [← hsum_succ]; exact hpos⟩
            (TensorPower.mulEquiv
              ((Ts 0) ⊗ₜ[F]
                tensorPowerBlock F V (fun i => (tail i : ℕ)) Tstail))) : ℝ) ≤
            ((Func.toFun (nVec 0) (Ts 0)) : ℝ) *
              ((Func.toFun ⟨∑ i, ((tail i : ℕ)), htailpos⟩
                (tensorPowerBlock F V (fun i => (tail i : ℕ)) Tstail)) : ℝ) := by
        rw [hmulEquiv]
        exact_mod_cast hsubmul
      refine hstep.trans ?_
      -- Step 4: IH on the tail and `Finset.prod_univ_succ`.
      have hIH :
          ((Func.toFun ⟨∑ i, ((tail i : ℕ)), htailpos⟩
            (tensorPowerBlock F V (fun i => (tail i : ℕ)) Tstail)) : ℝ) ≤
            ∏ i, ((Func.toFun (tail i) (Tstail i)) : ℝ) :=
        Func_tensorPowerBlock_le_prod Func tail Tstail htailpos
      calc
        ((Func.toFun (nVec 0) (Ts 0)) : ℝ) *
            ((Func.toFun ⟨∑ i, ((tail i : ℕ)), htailpos⟩
              (tensorPowerBlock F V (fun i => (tail i : ℕ)) Tstail)) : ℝ)
            ≤ ((Func.toFun (nVec 0) (Ts 0)) : ℝ) *
              ∏ i, ((Func.toFun (tail i) (Tstail i)) : ℝ) := by
              apply mul_le_mul_of_nonneg_left hIH
              positivity
        _ = ∏ j, ((Func.toFun (nVec j) (Ts j)) : ℝ) := by
              rw [Fin.prod_univ_succ (fun j => ((Func.toFun (nVec j) (Ts j)) : ℝ))]

/-- **Run entry for the regrouped sorted block (Theorem 2.2)**: the
    `i`-th run is `S_i^{⊗ k_i n}`, realized as an element of
    `TensorPower F (k i * n) V`. For an empty fiber (`k i = 0`) it is the unit
    (`algebraMap₀ 1` cast across `0 = k i * n`); for a nonempty fiber it is the
    cast of `tensorPow ⟨k i * n, _⟩ (Ssub i)`. This packaging keeps a single
    `tensorPowerBlock` over `Fin p` with run-sizes `k i * n` (zero allowed),
    matching the paper's "implicitly omit factors for which `m_i = 0`". -/
noncomputable def runEntry (n : ℕ+) {p : ℕ} (Ssub : Fin p → V) (k : Fin p → ℕ)
    (i : Fin p) : TensorPower F (k i * (n : ℕ)) V :=
  if h : 0 < k i then
    tensorPow ⟨k i * (n : ℕ), Nat.mul_pos h n.pos⟩ (Ssub i)
  else
    (TensorPower.cast F V (by simp_all : (0 : ℕ) = k i * (n : ℕ)))
      (TensorPower.algebraMap₀ (1 : F))

/-- **Unit-left collapse for `Func` on a block (Theorem 2.2, empty leading
    fiber)**: gluing the level-`0` unit on the left of a block `B` and applying
    `Func` gives `Func` of `B` (the unit factor drops out). Used for empty fibers
    `m_i = 0` in the sorted-run regrouping. -/
private lemma Func_mulEquiv_unit_left
    (Func : AdmissibleFunctional F V) {b : ℕ} (hb : 0 < b)
    (B : TensorPower F b V) :
    Func.toFun ⟨0 + b, by simpa using! hb⟩
        (TensorPower.mulEquiv ((TensorPower.algebraMap₀ (1 : F)) ⊗ₜ[F] B)) =
      Func.toFun ⟨b, hb⟩ B := by
  have hcollapse :
      TensorPower.mulEquiv ((TensorPower.algebraMap₀ (1 : F)) ⊗ₜ[F] B) =
        (TensorPower.cast F V (zero_add b)).symm B := by
    have hom := TensorPower.one_mul (R := F) (M := V) B
    rw [TensorPower.gMul_def, TensorPower.gOne_def] at hom
    apply (TensorPower.cast F V (zero_add b)).injective
    rw [LinearEquiv.apply_symm_apply, TensorPower.algebraMap₀_one, TensorPower.gOne_def]
    exact hom
  rw [hcollapse, TensorPower.cast_symm]
  exact AdmissibleFunctional.toFun_tensorPower_cast (F := F) (V := V) Func
    (zero_add b).symm hb B

/-- **Unit-right collapse for `Func` on a block (Theorem 2.2, empty trailing
    fibers)**: gluing the level-`0` unit on the right of a block `A` and applying
    `Func` gives `Func` of `A`. Used when all remaining fibers are empty. -/
private lemma Func_mulEquiv_unit_right
    (Func : AdmissibleFunctional F V) {a : ℕ} (ha : 0 < a)
    (A : TensorPower F a V) :
    Func.toFun ⟨a + 0, by simpa using! ha⟩
        (TensorPower.mulEquiv (A ⊗ₜ[F] (TensorPower.algebraMap₀ (1 : F)))) =
      Func.toFun ⟨a, ha⟩ A := by
  have hcollapse :
      TensorPower.mulEquiv (A ⊗ₜ[F] (TensorPower.algebraMap₀ (1 : F))) =
        (TensorPower.cast F V (add_zero a)).symm A := by
    have hom := TensorPower.mul_one (R := F) (M := V) A
    rw [TensorPower.gMul_def, TensorPower.gOne_def] at hom
    apply (TensorPower.cast F V (add_zero a)).injective
    rw [LinearEquiv.apply_symm_apply, TensorPower.algebraMap₀_one, TensorPower.gOne_def]
    exact hom
  rw [hcollapse, TensorPower.cast_symm]
  exact AdmissibleFunctional.toFun_tensorPower_cast (F := F) (V := V) Func
    (add_zero a).symm ha A

/-- **All-empty run-block collapses to the unit (Theorem 2.2)**: if every
    run is empty (`k i = 0`), the regrouped run-block is the level-`0` unit
    (`algebraMap₀ 1` cast across `∑ k_i n = 0`). Proof by induction on `p`,
    collapsing the leading unit factor at each step (`gMul_cast_left` + graded
    `one_mul`). -/
private lemma runBlock_eq_unit_of_all_zero (n : ℕ+) :
    ∀ {p : ℕ} (Ssub : Fin p → V) (k : Fin p → ℕ) (hk : ∀ i, k i = 0),
      tensorPowerBlock F V (fun i => k i * (n : ℕ))
          (runEntry (F := F) (V := V) n Ssub k) =
        (TensorPower.cast F V (by simp [hk] : (0 : ℕ) = ∑ i, k i * (n : ℕ)))
          (TensorPower.algebraMap₀ (1 : F))
  | 0, Ssub, k, hk => by
      change (TensorPower.cast F V _) (TensorPower.algebraMap₀ (1 : F)) = _
      congr 1
  | p + 1, Ssub, k, hk => by
      classical
      set tailk : Fin p → ℕ := fun i => k i.succ with htailk
      set tailS : Fin p → V := fun i => Ssub i.succ with htailS
      have hentry_tail :
          (fun i : Fin p => runEntry (F := F) (V := V) n Ssub k i.succ) =
            runEntry (F := F) (V := V) n tailS tailk := rfl
      have htailk0 : ∀ i, tailk i = 0 := fun i => hk i.succ
      have hk0 : k 0 = 0 := hk 0
      -- Block unfolds: head (unit) glued with the tail (unit by IH).
      have hblock :
          tensorPowerBlock F V (fun i => k i * (n : ℕ))
              (runEntry (F := F) (V := V) n Ssub k) =
            (TensorPower.cast F V
              (Fin.sum_univ_succ (fun i => k i * (n : ℕ))).symm)
              (TensorPower.mulEquiv
                ((runEntry (F := F) (V := V) n Ssub k 0) ⊗ₜ[F]
                  tensorPowerBlock F V (fun i => tailk i * (n : ℕ))
                    (runEntry (F := F) (V := V) n tailS tailk))) := by
        conv_lhs => rw [show tensorPowerBlock F V (fun i => k i * (n : ℕ))
            (runEntry (F := F) (V := V) n Ssub k) =
          (TensorPower.cast F V (Fin.sum_univ_succ (fun i => k i * (n : ℕ))).symm)
            (TensorPower.mulEquiv
              ((runEntry (F := F) (V := V) n Ssub k 0) ⊗ₜ[F]
                tensorPowerBlock F V (fun i : Fin p => k i.succ * (n : ℕ))
                  (fun i : Fin p => runEntry (F := F) (V := V) n Ssub k i.succ))) from rfl]
        rw [hentry_tail]
      rw [hblock]
      -- Head run 0 is the unit; tail block is the unit by IH.
      have hr0 : runEntry (F := F) (V := V) n Ssub k 0 =
          (TensorPower.cast F V (by rw [hk0]; simp : (0 : ℕ) = k 0 * (n : ℕ)))
            (TensorPower.algebraMap₀ (1 : F)) := by
        simp only [runEntry, dif_neg (by rw [hk0]; simp : ¬ 0 < k 0)]
      rw [hr0, runBlock_eq_unit_of_all_zero n tailS tailk htailk0]
      -- Pull both casts out of `mulEquiv`, reduce to graded `mul_one`/`one_mul`.
      rw [gMul_cast_left (F := F) (V := V)
        (by rw [hk0]; simp : (0 : ℕ) = k 0 * (n : ℕ))
        (TensorPower.algebraMap₀ (1 : F)) _]
      rw [gMul_cast_right (F := F) (V := V)
        (by simp [htailk0] : (0 : ℕ) = ∑ i, tailk i * (n : ℕ))
        (TensorPower.algebraMap₀ (1 : F)) (TensorPower.algebraMap₀ (1 : F))]
      rw [TensorPower.cast_cast, TensorPower.cast_cast]
      -- `mulEquiv (ₜ1 ⊗ ₜ1) = cast (ₜ1)`.
      have hone :
          TensorPower.mulEquiv
              ((TensorPower.algebraMap₀ (1 : F)) ⊗ₜ[F] (TensorPower.algebraMap₀ (1 : F))) =
            (TensorPower.cast F V (zero_add 0)).symm (TensorPower.algebraMap₀ (1 : F)) := by
        have hom := TensorPower.one_mul (R := F) (M := V) (TensorPower.algebraMap₀ (1 : F))
        rw [TensorPower.gMul_def, TensorPower.gOne_def, TensorPower.algebraMap₀_one,
          TensorPower.gOne_def] at hom
        apply (TensorPower.cast F V (zero_add 0)).injective
        rw [LinearEquiv.apply_symm_apply, TensorPower.algebraMap₀_one, TensorPower.gOne_def]
        exact hom
      rw [hone, TensorPower.cast_symm, TensorPower.cast_cast, TensorPower.cast_eq_cast]

/-- **Run-block submultiplicative bound (Theorem 2.2, iterated `Func.submul`
    over the `p` runs)**: for run-sizes `k : Fin p → ℕ` (zero allowed for empty
    fibers) and the run entries `runEntry n Ssub k`, the admissible functional of
    the regrouped block is bounded by the product of the per-run functionals,
    where empty fibers contribute the unit factor `1`:
    `F(⊗_i S_i^{⊗ k_i n}) ≤ ∏_{i, k_i>0} F(S_i^{⊗ k_i n})`.

    Proof by induction on `p`, peeling run `0`. If `k 0 > 0`, apply `Func.submul`
    to split off the first run, then the IH on the tail. If `k 0 = 0`, run `0` is
    the unit, so the block collapses to the tail block (graded `one_mul`) and the
    first product factor is `1`; recurse on the tail (whose run-size sum is still
    positive). This is the run-level analogue of `Func_tensorPowerBlock_le_prod`,
    used for the sorted-run regrouping bound. -/
private lemma Func_runBlock_le_prod
    (Func : AdmissibleFunctional F V) (n : ℕ+) :
    ∀ {p : ℕ} (Ssub : Fin p → V) (k : Fin p → ℕ)
      (hpos : 0 < ∑ i, k i * (n : ℕ)),
      ((Func.toFun ⟨∑ i, k i * (n : ℕ), hpos⟩
        (tensorPowerBlock F V (fun i => k i * (n : ℕ))
          (runEntry (F := F) (V := V) n Ssub k))) : ℝ) ≤
        ∏ i : Fin p,
          (if hki : 0 < k i then
            (Func.toFun ⟨k i * (n : ℕ), Nat.mul_pos hki n.pos⟩
              (tensorPow ⟨k i * (n : ℕ), Nat.mul_pos hki n.pos⟩ (Ssub i)) : ℝ)
          else 1)
  | 0, Ssub, k, hpos => by
      exact absurd hpos (by simp)
  | p + 1, Ssub, k, hpos => by
      classical
      set tailk : Fin p → ℕ := fun i => k i.succ with htailk
      set tailS : Fin p → V := fun i => Ssub i.succ with htailS
      -- The tail entries coincide with the run entries for the shifted data.
      have hentry_tail :
          (fun i : Fin p => runEntry (F := F) (V := V) n Ssub k i.succ) =
            runEntry (F := F) (V := V) n tailS tailk := rfl
      have hsum_succ : ∑ i, k i * (n : ℕ) =
          k 0 * (n : ℕ) + ∑ i, tailk i * (n : ℕ) := by
        rw [Fin.sum_univ_succ (fun i => k i * (n : ℕ))]
      -- Common block-unfold: peel run 0.
      have hblock :
          tensorPowerBlock F V (fun i => k i * (n : ℕ))
              (runEntry (F := F) (V := V) n Ssub k) =
            (TensorPower.cast F V
              (Fin.sum_univ_succ (fun i => k i * (n : ℕ))).symm)
              (TensorPower.mulEquiv
                ((runEntry (F := F) (V := V) n Ssub k 0) ⊗ₜ[F]
                  tensorPowerBlock F V (fun i => tailk i * (n : ℕ))
                    (runEntry (F := F) (V := V) n tailS tailk))) := by
        conv_lhs => rw [show tensorPowerBlock F V (fun i => k i * (n : ℕ))
            (runEntry (F := F) (V := V) n Ssub k) =
          (TensorPower.cast F V (Fin.sum_univ_succ (fun i => k i * (n : ℕ))).symm)
            (TensorPower.mulEquiv
              ((runEntry (F := F) (V := V) n Ssub k 0) ⊗ₜ[F]
                tensorPowerBlock F V (fun i : Fin p => k i.succ * (n : ℕ))
                  (fun i : Fin p => runEntry (F := F) (V := V) n Ssub k i.succ))) from rfl]
        rw [hentry_tail]
      -- Product over `Fin (p+1)` splits off factor 0.
      have hprod_succ :
          (∏ i : Fin (p + 1),
            (if hki : 0 < k i then
              (Func.toFun ⟨k i * (n : ℕ), Nat.mul_pos hki n.pos⟩
                (tensorPow ⟨k i * (n : ℕ), Nat.mul_pos hki n.pos⟩ (Ssub i)) : ℝ)
            else 1)) =
            (if hk0 : 0 < k 0 then
              (Func.toFun ⟨k 0 * (n : ℕ), Nat.mul_pos hk0 n.pos⟩
                (tensorPow ⟨k 0 * (n : ℕ), Nat.mul_pos hk0 n.pos⟩ (Ssub 0)) : ℝ)
            else 1) *
            (∏ i : Fin p,
              (if hki : 0 < tailk i then
                (Func.toFun ⟨tailk i * (n : ℕ), Nat.mul_pos hki n.pos⟩
                  (tensorPow ⟨tailk i * (n : ℕ), Nat.mul_pos hki n.pos⟩ (tailS i)) : ℝ)
              else 1)) := by
        rw [Fin.prod_univ_succ]
      -- IH on the tail (used in both branches below when tail is nonempty).
      have hIH : ∀ (htp : 0 < ∑ i, tailk i * (n : ℕ)),
          ((Func.toFun ⟨∑ i, tailk i * (n : ℕ), htp⟩
            (tensorPowerBlock F V (fun i => tailk i * (n : ℕ))
              (runEntry (F := F) (V := V) n tailS tailk))) : ℝ) ≤
            ∏ i : Fin p,
              (if hki : 0 < tailk i then
                (Func.toFun ⟨tailk i * (n : ℕ), Nat.mul_pos hki n.pos⟩
                  (tensorPow ⟨tailk i * (n : ℕ), Nat.mul_pos hki n.pos⟩ (tailS i)) : ℝ)
              else 1) := fun htp =>
        Func_runBlock_le_prod Func n tailS tailk htp
      -- Push `Func` through the head-`succ` cast in `hblock`.
      have hpushcast :
          ((Func.toFun ⟨∑ i, k i * (n : ℕ), hpos⟩
            (tensorPowerBlock F V (fun i => k i * (n : ℕ))
              (runEntry (F := F) (V := V) n Ssub k))) : ℝ) =
            ((Func.toFun ⟨k 0 * (n : ℕ) + ∑ i, tailk i * (n : ℕ),
                by rw [← hsum_succ]; exact hpos⟩
              (TensorPower.mulEquiv
                ((runEntry (F := F) (V := V) n Ssub k 0) ⊗ₜ[F]
                  tensorPowerBlock F V (fun i => tailk i * (n : ℕ))
                    (runEntry (F := F) (V := V) n tailS tailk)))) : ℝ) := by
        rw [hblock]
        congr 1
        exact AdmissibleFunctional.toFun_tensorPower_cast (F := F) (V := V) Func
          (Fin.sum_univ_succ (fun i => k i * (n : ℕ))).symm
          (by rw [← hsum_succ]; exact hpos) _
      by_cases h0 : 0 < k 0
      · -- Run 0 nonempty.
        have hr0 : runEntry (F := F) (V := V) n Ssub k 0 =
            tensorPow ⟨k 0 * (n : ℕ), Nat.mul_pos h0 n.pos⟩ (Ssub 0) := by
          simp only [runEntry, dif_pos h0]
        by_cases htp : 0 < ∑ i, tailk i * (n : ℕ)
        · -- Both run 0 and the tail are nonempty: split via `Func.submul`.
          rw [hprod_succ]
          rw [hpushcast, hr0]
          have hsubmul :=
            Func.submul ⟨k 0 * (n : ℕ), Nat.mul_pos h0 n.pos⟩
              ⟨∑ i, tailk i * (n : ℕ), htp⟩
              (tensorPow ⟨k 0 * (n : ℕ), Nat.mul_pos h0 n.pos⟩ (Ssub 0))
              (tensorPowerBlock F V (fun i => tailk i * (n : ℕ))
                (runEntry (F := F) (V := V) n tailS tailk))
          have hstep :
              ((Func.toFun ⟨k 0 * (n : ℕ) + ∑ i, tailk i * (n : ℕ),
                  by rw [← hsum_succ]; exact hpos⟩
                (TensorPower.mulEquiv
                  ((tensorPow ⟨k 0 * (n : ℕ), Nat.mul_pos h0 n.pos⟩ (Ssub 0)) ⊗ₜ[F]
                    tensorPowerBlock F V (fun i => tailk i * (n : ℕ))
                      (runEntry (F := F) (V := V) n tailS tailk)))) : ℝ) ≤
                (Func.toFun ⟨k 0 * (n : ℕ), Nat.mul_pos h0 n.pos⟩
                  (tensorPow ⟨k 0 * (n : ℕ), Nat.mul_pos h0 n.pos⟩ (Ssub 0)) : ℝ) *
                ((Func.toFun ⟨∑ i, tailk i * (n : ℕ), htp⟩
                  (tensorPowerBlock F V (fun i => tailk i * (n : ℕ))
                    (runEntry (F := F) (V := V) n tailS tailk))) : ℝ) := by
            exact_mod_cast hsubmul
          refine hstep.trans ?_
          rw [dif_pos h0]
          apply mul_le_mul_of_nonneg_left (hIH htp)
          positivity
        · -- Run 0 nonempty but tail sum is 0: tail block is the unit.
          have htailz : ∀ i, tailk i = 0 := by
            intro i
            by_contra hne
            exact htp (lt_of_lt_of_le
              (Nat.mul_pos (Nat.pos_of_ne_zero hne) n.pos)
              (Finset.single_le_sum (f := fun i => tailk i * (n : ℕ))
                (by intro j _; positivity) (Finset.mem_univ i)))
          have htailsum0 : ∑ i, tailk i * (n : ℕ) = 0 := by simp [htailz]
          -- The product reduces to the single factor for run 0.
          have hprodtail1 :
              (∏ i : Fin p,
                (if hki : 0 < tailk i then
                  (Func.toFun ⟨tailk i * (n : ℕ), Nat.mul_pos hki n.pos⟩
                    (tensorPow ⟨tailk i * (n : ℕ), Nat.mul_pos hki n.pos⟩ (tailS i)) : ℝ)
                else 1)) = 1 := by
            apply Finset.prod_eq_one
            intro i _
            rw [dif_neg (by rw [htailz i]; simp)]
          rw [hprod_succ, dif_pos h0, hprodtail1, mul_one]
          rw [hpushcast, hr0]
          -- Tail block is the unit.
          rw [runBlock_eq_unit_of_all_zero n tailS tailk htailz]
          -- Collapse the level-`0` unit factor on the right (`Func_mulEquiv_unit_right`),
          -- transporting across `∑ tailk*n = 0`.
          have hgoal :
              ((Func.toFun ⟨k 0 * (n : ℕ) + ∑ i, tailk i * (n : ℕ),
                  by rw [← hsum_succ]; exact hpos⟩
                (TensorPower.mulEquiv
                  ((tensorPow ⟨k 0 * (n : ℕ), Nat.mul_pos h0 n.pos⟩ (Ssub 0)) ⊗ₜ[F]
                    (TensorPower.cast F V (by simp [htailz] :
                      (0 : ℕ) = ∑ i, tailk i * (n : ℕ)))
                      (TensorPower.algebraMap₀ (1 : F))))) : ℝ) =
                (Func.toFun ⟨k 0 * (n : ℕ), Nat.mul_pos h0 n.pos⟩
                  (tensorPow ⟨k 0 * (n : ℕ), Nat.mul_pos h0 n.pos⟩ (Ssub 0)) : ℝ) := by
            rw [gMul_cast_right (F := F) (V := V)
              (na := k 0 * (n : ℕ)) (nb := 0) (nb' := ∑ i, tailk i * (n : ℕ))
              (by simp [htailz])
              (tensorPow ⟨k 0 * (n : ℕ), Nat.mul_pos h0 n.pos⟩ (Ssub 0))
              (TensorPower.algebraMap₀ (1 : F) : TensorPower F 0 V)]
            rw [AdmissibleFunctional.toFun_tensorPower_cast (F := F) (V := V) Func
              (by simp [htailz] : k 0 * (n : ℕ) + 0 =
                k 0 * (n : ℕ) + ∑ i, tailk i * (n : ℕ))
              (by positivity) _]
            exact_mod_cast Func_mulEquiv_unit_right (F := F) (V := V) Func
              (Nat.mul_pos h0 n.pos)
              (tensorPow ⟨k 0 * (n : ℕ), Nat.mul_pos h0 n.pos⟩ (Ssub 0))
          exact le_of_eq hgoal
      · -- Run 0 empty: it is the unit; block collapses to the tail.
        have hk0 : k 0 = 0 := by omega
        have htp : 0 < ∑ i, tailk i * (n : ℕ) := by
          rw [hsum_succ, hk0] at hpos; simpa using! hpos
        -- The product's leading factor is `1`.
        rw [hprod_succ, dif_neg h0, one_mul]
        -- Push to the unfolded head-`succ` form.
        rw [hpushcast]
        -- Run 0 is the unit `algebraMap₀ 1` at level `k 0 * n = 0`.
        have hr0 : runEntry (F := F) (V := V) n Ssub k 0 =
            (TensorPower.cast F V (by rw [hk0]; simp : (0 : ℕ) = k 0 * (n : ℕ)))
              (TensorPower.algebraMap₀ (1 : F)) := by
          simp only [runEntry, dif_neg h0]
        rw [hr0]
        refine le_trans (le_of_eq ?_) (hIH htp)
        set B := tensorPowerBlock F V (fun i => tailk i * (n : ℕ))
          (runEntry (F := F) (V := V) n tailS tailk) with hB
        clear_value B
        -- Pull the head cast out of `mulEquiv` (`gMul_cast_left`).
        rw [gMul_cast_left (F := F) (V := V)
          (by rw [hk0]; simp : (0 : ℕ) = k 0 * (n : ℕ))
          (TensorPower.algebraMap₀ (1 : F)) B]
        -- Push `Func` through the resulting cast, then collapse the unit.
        rw [AdmissibleFunctional.toFun_tensorPower_cast (F := F) (V := V) Func
          (by rw [hk0]; simp : (0 : ℕ) + ∑ i, tailk i * (n : ℕ) =
            k 0 * (n : ℕ) + ∑ i, tailk i * (n : ℕ))
          (by simpa using! htp) _]
        exact_mod_cast Func_mulEquiv_unit_left (F := F) (V := V) Func htp B

/--
**Bridge for Theorem 2.2**: applying admissible-functional permutation
    invariance to the constant-block tensor used by `blockTensorOfMultiIndex`.
-/
private lemma F_block_grouped_blockTensor_perm_inv_bridge
    (Func : AdmissibleFunctional F V) (n : ℕ+)
    {p : ℕ} (S : Fin p → V) {m : ℕ+} (I : Fin m → Fin p)
    (σ : Equiv.Perm (Fin m)) :
    ((Func.toFun (n * m)
      (blockTensorOfMultiIndex (F := F) (V := V) n S I)) : ℝ) =
      ((Func.toFun (n * m)
        (blockTensorOfMultiIndex (F := F) (V := V) n S (fun j => I (σ j)))) : ℝ) := by
  classical
  let nVec : Fin m → ℕ+ := fun _ => n
  let Ts : ∀ j : Fin m, TensorPower F (nVec j : ℕ) V :=
    fun j => tensorPow n (S (I j))
  have hpos₁ : 0 < ∑ j : Fin m, (nVec j : ℕ) := by
    change 0 < ∑ _j : Fin m, (n : ℕ)
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    exact Nat.mul_pos m.pos n.pos
  have hpos₂ : 0 < ∑ j : Fin m, (nVec (σ j) : ℕ) := by
    change 0 < ∑ _j : Fin m, (n : ℕ)
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    exact Nat.mul_pos m.pos n.pos
  have hperm :
      Func.toFun ⟨_, hpos₁⟩
          (tensorPowerBlock F V (fun j => (nVec j : ℕ)) Ts) =
        Func.toFun ⟨_, hpos₂⟩
          (tensorPowerBlock F V (fun j => (nVec (σ j) : ℕ)) (fun j => Ts (σ j))) :=
    Func.perm_inv nVec σ Ts hpos₁ hpos₂
  have hmain :
      Func.toFun (n * m)
          (blockTensorOfMultiIndex (F := F) (V := V) n S I) =
        Func.toFun (n * m)
          (blockTensorOfMultiIndex (F := F) (V := V) n S (fun j => I (σ j))) := by
    calc
      Func.toFun (n * m)
          (blockTensorOfMultiIndex (F := F) (V := V) n S I)
          =
        Func.toFun ⟨∑ j : Fin m, (nVec j : ℕ), hpos₁⟩
          (tensorPowerBlock F V (fun j => (nVec j : ℕ)) Ts) := by
          unfold blockTensorOfMultiIndex
          dsimp [nVec, Ts]
          exact AdmissibleFunctional.toFun_tensorPower_cast
            (F := F) (V := V) Func _ hpos₁ _
      _ =
        Func.toFun ⟨∑ j : Fin m, (nVec (σ j) : ℕ), hpos₂⟩
          (tensorPowerBlock F V (fun j => (nVec (σ j) : ℕ)) (fun j => Ts (σ j))) :=
          hperm
      _ =
        Func.toFun (n * m)
          (blockTensorOfMultiIndex (F := F) (V := V) n S (fun j => I (σ j))) := by
          unfold blockTensorOfMultiIndex
          dsimp [nVec, Ts]
          exact (AdmissibleFunctional.toFun_tensorPower_cast
            (F := F) (V := V) Func _ hpos₂ _).symm
  exact_mod_cast hmain

private lemma F_block_grouped_regrouping_identity
    (Func : AdmissibleFunctional F V) (n : ℕ+)
    {p : ℕ} (S : Fin p → V) {m : ℕ+} (I : Fin m → Fin p) :
    ∃ σ : Equiv.Perm (Fin m),
      ((Func.toFun (n * m)
        (blockTensorOfMultiIndex (F := F) (V := V) n S I)) : ℝ) =
        ((Func.toFun (n * m)
          (blockTensorOfMultiIndex (F := F) (V := V) n S (fun j => I (σ j)))) : ℝ) := by
  /- Theorem 2.2. Use `F_block_grouped_sorting_perm_exists` to choose
     a fiber-sorting permutation `σ`, then apply `Func.perm_inv` with
     `nVec = fun _ : Fin m => n` and
     `Ts j = tensorPow n (S (I j))`.  The two casts to level `n*m` are
     reconciled by `blockTensorOfMultiIndex_eq_constMulti`.  Consecutive
     equal fibers are then identified with powers via
     `tensorPow_eq_tensorPowerBlockConstMulti`. -/
  classical
  refine ⟨Tuple.sort I, ?_⟩
  exact F_block_grouped_blockTensor_perm_inv_bridge (F := F) (V := V) Func n S I (Tuple.sort I)

omit [Module.Finite F V] in
/-- **Monotone initial-segment characterization (Theorem 2.2, run structure)**:
    for a monotone `J : Fin m → Fin p` and a `Nat` threshold `N`, the value `(J j) < N`
    holds iff `j` lies in the initial segment of length `#{j' | (J j') < N}`. This is
    the core fact that monotone tuples lay out their fibers as consecutive runs. -/
private lemma monotone_val_lt_card {p : ℕ} {m : ℕ} (J : Fin m → Fin p)
    (hJ : Monotone J) (N : ℕ) (j : Fin m) :
    ((J j : ℕ) < N ↔ (j : ℕ) < (Finset.univ.filter (fun j' : Fin m => (J j' : ℕ) < N)).card) := by
  constructor
  · intro hji
    have hsub : (Finset.univ.filter (fun j'' : Fin m => j'' ≤ j)) ⊆
        Finset.univ.filter (fun j' : Fin m => (J j' : ℕ) < N) := fun j'' hj'' => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj'' ⊢
      exact lt_of_le_of_lt (by exact_mod_cast hJ hj'') hji
    have hcard : (Finset.univ.filter (fun j'' : Fin m => j'' ≤ j)).card = (j : ℕ) + 1 := by
      rw [show (Finset.univ.filter (fun j'' : Fin m => j'' ≤ j)) = Finset.Iic j from by
        ext x; simp [Finset.mem_Iic]]
      simp [Fin.card_Iic]
    have := Finset.card_le_card hsub; omega
  · intro hjc
    by_contra hcon
    push_neg at hcon
    have hsub : (Finset.univ.filter (fun j' : Fin m => (J j' : ℕ) < N)) ⊆
        Finset.univ.filter (fun j'' : Fin m => j'' < j) := fun j' hj' => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj' ⊢
      by_contra hle; push_neg at hle
      have : (J j : ℕ) ≤ (J j' : ℕ) := by exact_mod_cast hJ hle
      omega
    have hcard : (Finset.univ.filter (fun j'' : Fin m => j'' < j)).card = (j : ℕ) := by
      rw [show (Finset.univ.filter (fun j'' : Fin m => j'' < j)) = Finset.Iio j from by
        ext x; simp [Finset.mem_Iio]]
      simp [Fin.card_Iio]
    have := Finset.card_le_card hsub; omega

omit [Module.Finite F V] in
/-- **Run value (Theorem 2.2)**: for monotone `J`, the `(start i + k)`-th
    index (`start i = #{j' | (J j') < i}`) lands in fiber `i`, provided `k < #{J = i}`.
    Consequence of `monotone_val_lt_card` applied at thresholds `i` and `i+1`. -/
private lemma monotone_run_value {p : ℕ} {m : ℕ} (J : Fin m → Fin p)
    (hJ : Monotone J) (i : Fin p) (k : ℕ)
    (hk : k < (Finset.univ.filter (fun j' : Fin m => J j' = i)).card)
    (j0 : Fin m)
    (hj0 : (j0 : ℕ) = (Finset.univ.filter (fun j' : Fin m => (J j' : ℕ) < (i:ℕ))).card + k) :
    J j0 = i := by
  set s := (Finset.univ.filter (fun j' : Fin m => (J j' : ℕ) < (i:ℕ))).card with hs
  have hge : ¬ ((J j0 : ℕ) < (i:ℕ)) := by
    rw [monotone_val_lt_card J hJ (i:ℕ) j0, ← hs]; omega
  have hcard_le : (Finset.univ.filter (fun j' : Fin m => (J j' : ℕ) < (i:ℕ) + 1)).card
      = s + (Finset.univ.filter (fun j' : Fin m => J j' = i)).card := by
    rw [hs, ← Finset.card_union_of_disjoint]
    · congr 1
      ext x
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro hx
        rcases Nat.lt_succ_iff_lt_or_eq.mp hx with h | h
        · exact Or.inl h
        · exact Or.inr (Fin.ext h)
      · rintro (h | h)
        · omega
        · rw [h]; omega
    · rw [Finset.disjoint_left]
      intro x hx hx'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx hx'
      rw [hx'] at hx; omega
  have hle : (J j0 : ℕ) < (i:ℕ) + 1 := by
    rw [monotone_val_lt_card J hJ ((i:ℕ)+1) j0, hcard_le]; omega
  exact Fin.ext (by omega)

omit [Module.Finite F V] in
/-- **Fiber-prefix partition (Theorem 2.2)**: the count of indices with value
    below `i` is the sum of fiber cardinalities for all values below `i`. -/
private lemma card_lt_eq_sum_fibers {p : ℕ} {m : ℕ} (J : Fin m → Fin p) (i : Fin p) :
    (Finset.univ.filter (fun j : Fin m => (J j : ℕ) < (i:ℕ))).card
      = ∑ i' ∈ Finset.univ.filter (fun i' : Fin p => (i' : ℕ) < (i:ℕ)),
          (Finset.univ.filter (fun j : Fin m => J j = i')).card := by
  rw [← Finset.card_biUnion]
  · congr 1
    ext j
    simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨fun h => ⟨J j, h, rfl⟩, fun h => h.elim (fun i' hh => ?_)⟩
    have hv : (J j : ℕ) = (i' : ℕ) := congrArg Fin.val hh.2
    have := hh.1; omega
  · intro x hx y hy hxy
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro j hj hj'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj hj'
    exact hxy (hj ▸ hj')

omit [Module.Finite F V] in
/-- **Reindex a `Fin i.val` prefix sum as a filtered `Fin p` sum (engineering).** -/
private lemma sum_castLE_eq_sum_filter {p : ℕ} (f : Fin p → ℕ) (i : Fin p) :
    (∑ i' : Fin (i:ℕ), f (Fin.castLE (le_of_lt i.2) i'))
      = ∑ i' ∈ Finset.univ.filter (fun i' : Fin p => (i' : ℕ) < (i:ℕ)), f i' := by
  symm
  apply Finset.sum_bij
    (fun (i' : Fin p) (hi' : i' ∈ Finset.univ.filter (fun i' : Fin p => (i' : ℕ) < (i:ℕ))) =>
      (⟨(i':ℕ), by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi'; exact hi'⟩ : Fin (i:ℕ)))
  · intro a ha; exact Finset.mem_univ _
  · intro a ha b hb hab
    simp only [Fin.mk.injEq] at hab
    exact Fin.ext hab
  · intro b _
    refine ⟨Fin.castLE (le_of_lt i.2) b, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.castLE]; exact b.2
    · apply Fin.ext; simp [Fin.castLE]
  · intro a ha; apply congrArg f; apply Fin.ext; simp [Fin.castLE]

omit [Module.Finite F V] in
/-- **Fiber-card permutation invariance**: sorting by `I` preserves fiber sizes. -/
private lemma card_fiber_sort_eq {p : ℕ} {m : ℕ} (I : Fin m → Fin p) (i : Fin p) :
    (Finset.univ.filter (fun j : Fin m => I (Tuple.sort I j) = i)).card
      = (Finset.univ.filter (fun j : Fin m => I j = i)).card := by
  rw [← Finset.card_image_of_injective _ (Tuple.sort I).injective]
  congr 1
  ext x
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨a, ha, rfl⟩; exact ha
  · intro hx; exact ⟨(Tuple.sort I).symm x, by simp [hx]⟩

omit [Module.Finite F V] in
/-- **`runEntry` as a `tprod`**: each run is the constant `tprod` of `S i` (the
    empty-fiber unit is also a `tprod` over `Fin 0`). -/
private lemma runEntry_eq_tprod (n : ℕ+) {p : ℕ} (S : Fin p → V) (k : Fin p → ℕ) (i : Fin p) :
    runEntry (F := F) (V := V) n S k i
      = PiTensorProduct.tprod F (fun _ : Fin (k i * (n : ℕ)) => S i) := by
  unfold runEntry
  by_cases h : 0 < k i
  · rw [dif_pos h]; rfl
  · rw [dif_neg h]
    push_neg at h
    have hk0 : k i = 0 := Nat.le_zero.mp h
    rw [TensorPower.algebraMap₀_one, TensorPower.gOne_def, TensorPower.cast_tprod]
    congr 1
    funext x
    exact absurd x.2 (by simp [hk0])

/--
**Sorted-block run regrouping identity (Theorem 2.2, "rearranging tensor
    factors")**: the sorted constant block `⊗_{j} S_{(I∘sort)(j)}^{⊗n}` is, up to
    the canonical level cast `∑_i m_i n = n m`, the `p`-fold run-block whose `i`-th
    factor is `S_i^{⊗ m_i n}` (`runEntry`), where `m_i = card{j : I j = i}`.
-/
private lemma blockTensorOfMultiIndex_sort_eq_runBlock
    (n : ℕ+) {p : ℕ} (S : Fin p → V) {m : ℕ+} (I : Fin m → Fin p) :
    blockTensorOfMultiIndex (F := F) (V := V) n S (fun j => I (Tuple.sort I j)) =
      (TensorPower.cast F V
        (by
          -- `∑_i m_i n = n m`: each `j : Fin m` lands in exactly one fiber.
          rw [← Finset.sum_mul]
          have hsum : (∑ i : Fin p, ((Finset.univ.filter (fun j : Fin m => I j = i)).card : ℕ))
              = (m : ℕ) := by
            have hdisj :
                ((Finset.univ : Finset (Fin p)) : Set (Fin p)).PairwiseDisjoint
                  (fun i => Finset.univ.filter (fun j : Fin m => I j = i)) := by
              intro i _ i' _ hii'
              simp only [Function.onFun, Finset.disjoint_left, Finset.mem_filter,
                Finset.mem_univ, true_and]
              rintro j hj hj'
              exact hii' (hj ▸ hj')
            rw [← Finset.card_biUnion hdisj]
            have hbu : (Finset.univ.biUnion
                (fun i : Fin p => Finset.univ.filter (fun j : Fin m => I j = i)))
                = (Finset.univ : Finset (Fin m)) := by
              ext j; simp
            rw [hbu, Finset.card_univ, Fintype.card_fin]
          rw [hsum, PNat.mul_coe]; ring :
          (∑ i : Fin p, (Finset.univ.filter (fun j : Fin m => I j = i)).card * (n : ℕ))
            = ((n * m : ℕ+) : ℕ)))
        (tensorPowerBlock F V
          (fun i : Fin p =>
            (Finset.univ.filter (fun j : Fin m => I j = i)).card * (n : ℕ))
          (runEntry (F := F) (V := V) n S
            (fun i : Fin p => (Finset.univ.filter (fun j : Fin m => I j = i)).card))) := by
  /- Theorem 2.2. The monotone sorted tuple `J := I∘sort` lays the fibers out
     consecutively. Both the sorted block and the run-block flatten (via
     `tensorPowerBlock_tprod_family`) to the `tprod` of a single function
     `flat_common t = S (J ⌊t/n⌋)`; the LHS match is pure division arithmetic and
     the RHS match is the monotone run-structure (`monotone_run_value`). -/
  classical
  set J : Fin m → Fin p := fun j => I (Tuple.sort I j) with hJdef
  have hJmono : Monotone J := Tuple.monotone_sort I
  set mi : Fin p → ℕ := fun i => (Finset.univ.filter (fun j : Fin m => I j = i)).card with hmidef
  -- J's fibers have the same cardinalities as I's.
  have hmiJ : ∀ i, mi i = (Finset.univ.filter (fun j : Fin m => J j = i)).card := by
    intro i; rw [hmidef]; exact (card_fiber_sort_eq I i).symm
  -- Level casts.
  have hm : (∑ _j : Fin m, (n : ℕ)) = ((n * m : ℕ+) : ℕ) := tensorPower_sum_const_eq_mul n m
  have hp : (∑ i : Fin p, mi i * (n : ℕ)) = ((n * m : ℕ+) : ℕ) := by
    rw [← Finset.sum_mul]
    have hsum : (∑ i : Fin p, mi i) = (m : ℕ) := by
      rw [hmidef]
      have hdisj :
          ((Finset.univ : Finset (Fin p)) : Set (Fin p)).PairwiseDisjoint
            (fun i => Finset.univ.filter (fun j : Fin m => I j = i)) := by
        intro i _ i' _ hii'
        simp only [Function.onFun, Finset.disjoint_left, Finset.mem_filter,
          Finset.mem_univ, true_and]
        rintro j hj hj'
        exact hii' (hj ▸ hj')
      rw [← Finset.card_biUnion hdisj]
      have hbu : (Finset.univ.biUnion
          (fun i : Fin p => Finset.univ.filter (fun j : Fin m => I j = i)))
          = (Finset.univ : Finset (Fin m)) := by
        ext j; simp
      rw [hbu, Finset.card_univ, Fintype.card_fin]
    rw [hsum, PNat.mul_coe]; ring
  -- The common flattened function: `flat_common t = S (J ⌊t/n⌋)`.
  set flat_common : Fin ((n * m : ℕ+) : ℕ) → V :=
    fun t => S (J ⟨(t : ℕ) / (n : ℕ), by
      have ht : (t : ℕ) < (n : ℕ) * (m : ℕ) :=
        lt_of_lt_of_eq t.2 (PNat.mul_coe n m)
      exact Nat.div_lt_of_lt_mul ht⟩) with hflatdef
  -- Both sides equal `tprod flat_common`.
  rw [show (TensorPower.cast F V hp)
        (tensorPowerBlock F V (fun i : Fin p => mi i * (n : ℕ))
          (runEntry (F := F) (V := V) n S mi))
      = PiTensorProduct.tprod F flat_common from ?_,
      show blockTensorOfMultiIndex (F := F) (V := V) n S J
        = PiTensorProduct.tprod F flat_common from ?_]
  · -- LHS = tprod flat_common.
    rw [blockTensorOfMultiIndex_eq_constMulti, tensorPowerBlockConstMulti_apply]
    have hfactor : (fun j : Fin m => tensorPow (F := F) (V := V) n (S (J j)))
        = fun j : Fin m => PiTensorProduct.tprod F (fun _ : Fin (n : ℕ) => S (J j)) := by
      funext j; rfl
    rw [hfactor]
    rw [tensorPowerBlock_tprod_family (fun _ : Fin m => (n : ℕ))
        (fun j : Fin m => fun _ : Fin (n : ℕ) => S (J j))
        (flat_common ∘ Fin.cast hm)
        (fun s => by
          simp only [Function.comp_apply]
          -- value of `finSigmaFinEquiv ⟨j, c⟩` is `j*n + c`; division by `n` gives `j`.
          rw [hflatdef]
          beta_reduce
          congr 1
          apply congrArg J
          apply Fin.ext
          simp only [Fin.val_cast]
          rw [finSigmaFinEquiv_apply]
          have hc : (s.2 : ℕ) < (n : ℕ) := s.2.2
          rw [show (∑ i : Fin (s.1 : ℕ), (fun _ : Fin m => (n : ℕ)) (Fin.castLE (by omega) i))
                = (s.1 : ℕ) * (n : ℕ) from by
            simp [Finset.sum_const]]
          rw [show ((s.1 : ℕ) * (n : ℕ) + (s.2 : ℕ)) = ((s.2 : ℕ) + (s.1 : ℕ) * (n : ℕ))
                from by ring,
            Nat.add_mul_div_right _ _ n.pos, Nat.div_eq_of_lt hc, zero_add])]
    rw [TensorPower.cast_tprod]
    congr 1
  · -- RHS = tprod flat_common (the monotone run-structure crux).
    have hfactor : (runEntry (F := F) (V := V) n S mi)
        = fun i : Fin p => PiTensorProduct.tprod F (fun _ : Fin (mi i * (n : ℕ)) => S i) := by
      funext i; exact runEntry_eq_tprod (F := F) (V := V) n S mi i
    rw [hfactor]
    rw [tensorPowerBlock_tprod_family (fun i : Fin p => mi i * (n : ℕ))
        (fun i : Fin p => fun _ : Fin (mi i * (n : ℕ)) => S i)
        (flat_common ∘ Fin.cast hp)
        (fun s => by
          simp only [Function.comp_apply]
          rw [hflatdef]
          beta_reduce
          -- need `J ⌊value/n⌋ = s.1`.
          set i := s.1 with hidef
          set d := s.2 with hddef
          set A := (Finset.univ.filter (fun j : Fin m => (J j : ℕ) < (i:ℕ))).card with hAdef
          have hval : ((finSigmaFinEquiv (⟨i, d⟩ : (i : Fin p) × Fin (mi i * (n:ℕ)))) : ℕ)
              = A * (n : ℕ) + (d : ℕ) := by
            rw [finSigmaFinEquiv_apply]
            congr 1
            rw [← Finset.sum_mul]
            congr 1
            rw [hAdef, card_lt_eq_sum_fibers J i,
              ← sum_castLE_eq_sum_filter
                (fun i' => (Finset.univ.filter (fun j : Fin m => J j = i')).card) i]
            apply Finset.sum_congr rfl
            intro x _
            rw [hmiJ]
          have hk : (d : ℕ) / (n : ℕ) < mi i := by
            apply Nat.div_lt_of_lt_mul
            exact lt_of_lt_of_eq d.2 (Nat.mul_comm _ _)
          have hdiv : (A * (n : ℕ) + (d : ℕ)) / (n : ℕ) = A + (d : ℕ) / (n : ℕ) := by
            rw [add_comm (A * (n:ℕ)) ((d:ℕ)), Nat.add_mul_div_right _ _ n.pos, add_comm]
          -- `S (J ⌊val/n⌋) = S i`: reduce to `J ⌊val/n⌋ = i` via the run-structure.
          congr 1
          apply monotone_run_value J hJmono i ((d : ℕ) / (n : ℕ))
          · rw [← hmiJ]; exact hk
          · simp only [Fin.val_cast]
            rw [hval, hdiv, ← hAdef])]
    rw [TensorPower.cast_tprod]
    congr 1

/--
**Narrow sorted-run regrouping helper for Theorem 2.2**: after
    replacing `I` by `I ∘ Tuple.sort I`, the constant block tensor is grouped
    into consecutive nonempty fibers, each fiber is identified with
    `tensorPow (m_i*n) (S i)` via `tensorPow_eq_tensorPowerBlockConstMulti`,
    and iterated `Func.submul` over those grouped blocks gives the filtered
    product bound.
-/
private lemma F_block_le_grouped_product_tuple_sort_regrouped_runs_submul
    (Func : AdmissibleFunctional F V) (n : ℕ+)
    {p : ℕ} (S : Fin p → V) {m : ℕ+} (I : Fin m → Fin p) :
    ((Func.toFun (n * m)
      (blockTensorOfMultiIndex (F := F) (V := V) n S
        (fun j => I (Tuple.sort I j)))) : ℝ) ≤
      (∏ i : Fin p,
        (let mi : ℕ := (Finset.univ.filter (fun j : Fin m => I j = i)).card
         if hmi : 0 < mi then
           (Func.toFun ⟨mi * (n : ℕ), Nat.mul_pos hmi n.pos⟩
             (tensorPow ⟨mi * (n : ℕ), Nat.mul_pos hmi n.pos⟩ (S i)) : ℝ)
         else 1)) := by
  classical
  set mi : Fin p → ℕ :=
    fun i => (Finset.univ.filter (fun j : Fin m => I j = i)).card with hmi
  -- Total run-size sum equals `n m`.
  have hsum : (∑ i : Fin p, mi i) = (m : ℕ) := by
    rw [hmi]
    have hdisj :
        ((Finset.univ : Finset (Fin p)) : Set (Fin p)).PairwiseDisjoint
          (fun i => Finset.univ.filter (fun j : Fin m => I j = i)) := by
      intro i _ i' _ hii'
      simp only [Function.onFun, Finset.disjoint_left, Finset.mem_filter,
        Finset.mem_univ, true_and]
      rintro j hj hj'
      exact hii' (hj ▸ hj')
    rw [← Finset.card_biUnion hdisj]
    have hbu : (Finset.univ.biUnion
        (fun i : Fin p => Finset.univ.filter (fun j : Fin m => I j = i)))
        = (Finset.univ : Finset (Fin m)) := by
      ext j; simp
    rw [hbu, Finset.card_univ, Fintype.card_fin]
  have hsum : (∑ i : Fin p, mi i * (n : ℕ)) = ((n * m : ℕ+) : ℕ) := by
    rw [← Finset.sum_mul, hsum, PNat.mul_coe]; ring
  have hpos : 0 < ∑ i : Fin p, mi i * (n : ℕ) := by
    rw [hsum]; exact (n * m).pos
  -- Step 1: regroup the sorted block into the run-block (combinatorial residual).
  rw [blockTensorOfMultiIndex_sort_eq_runBlock (F := F) (V := V) n S I]
  -- Step 2: push `Func` through the level cast.
  rw [show Func.toFun (n * m)
        ((TensorPower.cast F V (by rw [hsum] :
            (∑ i : Fin p, mi i * (n : ℕ)) = ((n * m : ℕ+) : ℕ)))
          (tensorPowerBlock F V (fun i : Fin p => mi i * (n : ℕ))
            (runEntry (F := F) (V := V) n S mi)))
      = Func.toFun ⟨∑ i : Fin p, mi i * (n : ℕ), hpos⟩
          (tensorPowerBlock F V (fun i : Fin p => mi i * (n : ℕ))
            (runEntry (F := F) (V := V) n S mi)) from
    AdmissibleFunctional.toFun_tensorPower_cast (F := F) (V := V) Func
      (by rw [hsum] : (∑ i : Fin p, mi i * (n : ℕ)) = ((n * m : ℕ+) : ℕ)) hpos _]
  refine le_trans (Func_runBlock_le_prod (F := F) (V := V) Func n S mi hpos) ?_
  -- The run-block bound's RHS is exactly the headline product.
  apply le_of_eq
  apply Finset.prod_congr rfl
  intro i _
  rfl

/-- **Sorted-run residual core for Theorem 2.2**: once the block has
    already been permuted by `Tuple.sort I`, the resulting sorted runs regroup
    into the product of nonempty fibers, and iterated `Func.submul` gives the
    displayed bound.

    This is narrower than
    `F_block_le_grouped_product_iterated_submul_sorted_runs_core`: it no longer
    contains the initial `perm_inv` step for the original block, only the
    sorted-run regrouping plus iterated submultiplicativity. -/
private lemma F_block_le_grouped_product_tuple_sort_iterated_submul_core
    (Func : AdmissibleFunctional F V) (n : ℕ+)
    {p : ℕ} (S : Fin p → V) {m : ℕ+} (I : Fin m → Fin p) :
    ((Func.toFun (n * m)
      (blockTensorOfMultiIndex (F := F) (V := V) n S
        (fun j => I (Tuple.sort I j)))) : ℝ) ≤
      (∏ i : Fin p,
        (let mi : ℕ := (Finset.univ.filter (fun j : Fin m => I j = i)).card
         if hmi : 0 < mi then
           (Func.toFun ⟨mi * (n : ℕ), Nat.mul_pos hmi n.pos⟩
             (tensorPow ⟨mi * (n : ℕ), Nat.mul_pos hmi n.pos⟩ (S i)) : ℝ)
         else 1)) := by
  /- Theorem 2.2. The sorted block has consecutive runs indexed by each
     nonempty fiber of `I`. Regroup each run as `S i ^⊗ (m_i*n)`, omit empty
     fibers as unit factors, then induct through those nonempty runs using
     `Func.submul`. -/
  exact F_block_le_grouped_product_tuple_sort_regrouped_runs_submul
    (F := F) (V := V) Func n S I

/--
**Narrow residual core for Theorem 2.2**: after the permutation and
    run-regrouping from Theorem 2.2 have put the block tensor in grouped-run
    form, iterated applications of `Func.submul` give the product over the
    nonempty fibers.
-/
private lemma F_block_le_grouped_product_iterated_submul_sorted_runs_core
    (Func : AdmissibleFunctional F V) (n : ℕ+)
    {p : ℕ} (S : Fin p → V) {m : ℕ+} (I : Fin m → Fin p) :
    ((Func.toFun (n * m)
      (blockTensorOfMultiIndex (F := F) (V := V) n S I)) : ℝ) ≤
      (∏ i : Fin p,
        (let mi : ℕ := (Finset.univ.filter (fun j : Fin m => I j = i)).card
         if hmi : 0 < mi then
           (Func.toFun ⟨mi * (n : ℕ), Nat.mul_pos hmi n.pos⟩
             (tensorPow ⟨mi * (n : ℕ), Nat.mul_pos hmi n.pos⟩ (S i)) : ℝ)
         else 1)) := by
  /- Theorem 2.2. After `F_block_grouped_regrouping_identity`, the
     sorted block is the p-fold product of nonempty grouped powers
     `S i ^⊗ (m_i*n)`, omitting the zero fibers.  Induct over `Fin p`, applying
     `Func.submul` at each nonzero fiber and multiplying by `1` for
     `m_i = 0`, exactly matching the displayed product. -/
  calc
    ((Func.toFun (n * m)
      (blockTensorOfMultiIndex (F := F) (V := V) n S I)) : ℝ)
        =
      ((Func.toFun (n * m)
        (blockTensorOfMultiIndex (F := F) (V := V) n S
          (fun j => I (Tuple.sort I j)))) : ℝ) := by
        exact F_block_grouped_blockTensor_perm_inv_bridge
          (F := F) (V := V) Func n S I (Tuple.sort I)
    _ ≤
      (∏ i : Fin p,
        (let mi : ℕ := (Finset.univ.filter (fun j : Fin m => I j = i)).card
         if hmi : 0 < mi then
           (Func.toFun ⟨mi * (n : ℕ), Nat.mul_pos hmi n.pos⟩
             (tensorPow ⟨mi * (n : ℕ), Nat.mul_pos hmi n.pos⟩ (S i)) : ℝ)
         else 1)) :=
        F_block_le_grouped_product_tuple_sort_iterated_submul_core
          (F := F) (V := V) Func n S I

private lemma F_block_grouped_iterated_submul
    (Func : AdmissibleFunctional F V) (n : ℕ+)
    {p : ℕ} (S : Fin p → V) {m : ℕ+} (I : Fin m → Fin p) :
    ((Func.toFun (n * m)
      (blockTensorOfMultiIndex (F := F) (V := V) n S I)) : ℝ) ≤
      (∏ i : Fin p,
        (let mi : ℕ := (Finset.univ.filter (fun j : Fin m => I j = i)).card
         if hmi : 0 < mi then
           (Func.toFun ⟨mi * (n : ℕ), Nat.mul_pos hmi n.pos⟩
             (tensorPow ⟨mi * (n : ℕ), Nat.mul_pos hmi n.pos⟩ (S i)) : ℝ)
         else 1)) := by
  exact F_block_le_grouped_product_iterated_submul_sorted_runs_core
    (F := F) (V := V) Func n S I

private lemma F_block_le_grouped_product_iterated_submul
    (Func : AdmissibleFunctional F V) (n : ℕ+)
    {p : ℕ} (S : Fin p → V) {m : ℕ+} (I : Fin m → Fin p) :
    ((Func.toFun (n * m)
      (blockTensorOfMultiIndex (F := F) (V := V) n S I)) : ℝ) ≤
      (∏ i : Fin p,
        (let mi : ℕ := (Finset.univ.filter (fun j : Fin m => I j = i)).card
         if hmi : 0 < mi then
           (Func.toFun ⟨mi * (n : ℕ), Nat.mul_pos hmi n.pos⟩
             (tensorPow ⟨mi * (n : ℕ), Nat.mul_pos hmi n.pos⟩ (S i)) : ℝ)
         else 1)) := by
  exact F_block_grouped_iterated_submul (F := F) (V := V) Func n S I

lemma F_block_le_grouped_product
    (Func : AdmissibleFunctional F V) (n : ℕ+)
    {p : ℕ} (S : Fin p → V) {m : ℕ+} (I : Fin m → Fin p) :
    ((Func.toFun (n * m)
      (blockTensorOfMultiIndex (F := F) (V := V) n S I)) : ℝ) ≤
      (∏ i : Fin p,
        (let mi : ℕ := (Finset.univ.filter (fun j : Fin m => I j = i)).card
         if hmi : 0 < mi then
           (Func.toFun ⟨mi * (n : ℕ), Nat.mul_pos hmi n.pos⟩
             (tensorPow ⟨mi * (n : ℕ), Nat.mul_pos hmi n.pos⟩ (S i)) : ℝ)
         else 1)) := by
  -- Theorem 2.2. perm_inv + iterated submul.
  exact F_block_le_grouped_product_iterated_submul (F := F) (V := V) Func n S I

/--
**Combined structural sub-helper (Theorem 2.2)**: combines
    `F_tensorPow_nm_le_pm_max_block_apply` (Theorem 2.2) and
    `F_block_le_grouped_product` (Theorem 2.2).

    Apply the first inequality, then the second for each index in the supremum.
-/
lemma F_tensorPow_nm_le_max_grouped_product
    (Func : AdmissibleFunctional F V) (T : V) (hT : T ≠ 0)
    (n : ℕ+)
    {p : ℕ} (S : Fin p → V) (α : Fin p → F)
    (hdecomp : tensorPow (F := F) (V := V) n T = ∑ i, α i • tensorPow n (S i))
    (m : ℕ+) :
    ((Func.toFun (n * m) (tensorPow (F := F) (V := V) (n * m) T) : ℝ)) ≤
      ((p : ℝ) ^ (m : ℕ)) *
        ⨆ (I : Fin m → Fin p),
          (∏ i : Fin p,
            -- Per-i factor: F(Sᵢ^⊗(mᵢ(I) · n)) if mᵢ(I) ≥ 1, else 1.
            (let mi : ℕ := (Finset.univ.filter (fun j : Fin m => I j = i)).card
             if hmi : 0 < mi then
               (Func.toFun ⟨mi * (n : ℕ), Nat.mul_pos hmi n.pos⟩
                 (tensorPow ⟨mi * (n : ℕ), Nat.mul_pos hmi n.pos⟩ (S i)) : ℝ)
             else 1)) := by
  classical
  -- Step 1 (Theorem 2.2): apply the expansion + subadd + scalar_inv
  -- sub-helper to bound `F(T^⊗(nm)) ≤ p^m · iSup_I F(block_I)`.
  have hstep1 := F_tensorPow_nm_le_pm_max_block_apply
    (F := F) (V := V) Func T hT n S α hdecomp m
  -- Step 2 (Theorem 2.2): for each `I`, bound `F(block_I) ≤ ∏ᵢ per-i factor`.
  have hstep2 : ∀ I : Fin m → Fin p,
      ((Func.toFun (n * m)
        (blockTensorOfMultiIndex (F := F) (V := V) n S I)) : ℝ) ≤
        (∏ i : Fin p,
          (let mi : ℕ := (Finset.univ.filter (fun j : Fin m => I j = i)).card
           if hmi : 0 < mi then
             (Func.toFun ⟨mi * (n : ℕ), Nat.mul_pos hmi n.pos⟩
               (tensorPow ⟨mi * (n : ℕ), Nat.mul_pos hmi n.pos⟩ (S i)) : ℝ)
           else 1)) := fun I =>
    F_block_le_grouped_product (F := F) (V := V) Func n S I
  -- Step 3: chain by monotonicity of iSup and `(p^m) * _ ≥ 0`.
  have hp_R_nn : (0 : ℝ) ≤ ((p : ℝ) ^ (m : ℕ)) := pow_nonneg (Nat.cast_nonneg _) _
  refine hstep1.trans ?_
  -- iSup-bound: each block-application is ≤ the product, so iSup ≤ iSup of products.
  -- For the iSup inequality, we use `ciSup_le` (after handling the empty case `p = 0`).
  by_cases hp_pos : 0 < p
  · haveI : Nonempty (Fin p) := ⟨⟨0, hp_pos⟩⟩
    haveI : Nonempty (Fin m → Fin p) := ⟨fun _ => ⟨0, hp_pos⟩⟩
    -- Both sides are iSups; we relate them factor-wise via hstep2.
    have hbdd_rhs : BddAbove (Set.range fun I : Fin m → Fin p =>
        (∏ i : Fin p,
          (let mi : ℕ := (Finset.univ.filter (fun j : Fin m => I j = i)).card
           if hmi : 0 < mi then
             (Func.toFun ⟨mi * (n : ℕ), Nat.mul_pos hmi n.pos⟩
               (tensorPow ⟨mi * (n : ℕ), Nat.mul_pos hmi n.pos⟩ (S i)) : ℝ)
           else 1))) := by
      -- The set is finite (image of finite type), so it's bdd above.
      exact Set.Finite.bddAbove (Set.toFinite _)
    have hiSup_le :
        (⨆ I : Fin m → Fin p,
          ((Func.toFun (n * m)
            (blockTensorOfMultiIndex (F := F) (V := V) n S I)) : ℝ)) ≤
        ⨆ I : Fin m → Fin p,
          (∏ i : Fin p,
            (let mi : ℕ := (Finset.univ.filter (fun j : Fin m => I j = i)).card
             if hmi : 0 < mi then
               (Func.toFun ⟨mi * (n : ℕ), Nat.mul_pos hmi n.pos⟩
                 (tensorPow ⟨mi * (n : ℕ), Nat.mul_pos hmi n.pos⟩ (S i)) : ℝ)
             else 1)) := by
      refine ciSup_le ?_
      intro I
      exact (hstep2 I).trans (le_ciSup hbdd_rhs I)
    exact mul_le_mul_of_nonneg_left hiSup_le hp_R_nn
  · -- p = 0 case: iSup over `Fin m → Fin 0` is empty.
    push_neg at hp_pos
    interval_cases p
    haveI : IsEmpty (Fin m → Fin 0) := ⟨fun f => (f ⟨0, m.pos⟩).elim0⟩
    rw [Real.iSup_of_isEmpty, Real.iSup_of_isEmpty]

/-- **Sub-helper (Theorem 2.2 per-i factor bound)**.

    Quotes Theorem 2.2:
      For every `i ∈ [p(n)]`, if `mᵢ n ≥ M(ε,n)` then
        `F(Sᵢ^⊗(mᵢ n)) ≤ (F̃(Sᵢ) + ε)^(mᵢ n) ≤ (F̃[A] + ε)^(mᵢ n)`.
      If `mᵢ n < M(ε,n)` then `F(Sᵢ^⊗(mᵢ n)) ≤ B^(mᵢ n) ≤ B^M`.

    Combined: `F(Sᵢ^⊗(mᵢ n)) ≤ (F̃[A]+ε)^(mᵢ n) · B^M` when both quantities
    are nonneg (using `B ≥ 1`, `F̃[A]+ε ≥ 0`).

    Wait — this is FALSE as stated when `(F̃[A]+ε)^(mᵢ n) = 0` and we're in
    the small-`mᵢ n` regime. The paper handles this by splitting the product
    into "large mᵢ n" indices (which contribute `(F̃[A]+ε)^(mᵢ n)`) and
    "small mᵢ n" indices (which contribute `B^(mᵢ n) ≤ B^M`). The product
    over small indices is bounded by `B^(p · M)`.

    The cleanest closed statement for the per-i factor is the **CASE-SPLIT**
    version: encode the conditional bound directly.

    Closed via `regularize_approximation` (hypothesis `hM`) + monotonicity
    of `regularize ≤ asympOnSet` + `toFun_tensorPow_le_bdd_pow`. -/
lemma F_S_pow_split_bound
    (Func : AdmissibleFunctional F V) (A : Set V)
    {p : ℕ} (S : Fin p → V) (hSA : ∀ i, S i ∈ A) (ε : ℝ) (hε : 0 < ε)
    (B : NNReal) (hB_one : 1 ≤ B)
    (hB_F1 : ∀ U : TensorPower F 1 V, Func.toFun 1 U ≤ B)
    (M : ℕ+)
    (hM : ∀ (i : Fin p) (ℓ : ℕ+), M ≤ ℓ →
      ((Func.toFun ℓ (tensorPow ℓ (S i)) : ℝ)) ^ ((1 : ℝ) / (ℓ : ℕ)) ≤
        Func.regularize (S i) + ε)
    (i : Fin p) (k : ℕ+) :
    -- Either k ≥ M, in which case (F̃[A]+ε)^k bounds F(S i ^⊗ k);
    -- or k < M, in which case B^k ≤ B^M bounds F(S i ^⊗ k).
    -- Combined disjunctive form (matches Theorem 2.2).
    ((Func.toFun k (tensorPow k (S i)) : ℝ)) ≤
      (Func.asympOnSet A + ε) ^ (k : ℕ) ∨
    ((Func.toFun k (tensorPow k (S i)) : ℝ)) ≤ ((B : ℝ)) ^ (M : ℕ) := by
  classical
  -- Case split on M ≤ k.
  by_cases hk : M ≤ k
  · -- Large case (Theorem 2.2): F(S_i^⊗k)^(1/k) ≤ F̃(S_i)+ε ≤ F̃[A]+ε.
    left
    have hroot : ((Func.toFun k (tensorPow k (S i)) : ℝ)) ^ ((1 : ℝ) / (k : ℕ)) ≤
        Func.regularize (S i) + ε := hM i k hk
    -- F̃(S_i) ≤ F̃[A] since S_i ∈ A.
    have hSi_le_asymp : Func.regularize (S i) ≤ Func.asympOnSet A := by
      unfold AdmissibleFunctional.asympOnSet
      have hbdd : BddAbove (Set.range fun T : V => ⨆ _ : T ∈ A, Func.regularize T) :=
        asympOnSet_bddAbove Func A
      calc Func.regularize (S i)
          = (⨆ _ : (S i) ∈ A, Func.regularize (S i)) := by
            rw [iSup_mem_eq, if_pos (hSA i)]
        _ ≤ (⨆ T : V, ⨆ _ : T ∈ A, Func.regularize T) := le_ciSup hbdd (S i)
    have hroot' : ((Func.toFun k (tensorPow k (S i)) : ℝ)) ^ ((1 : ℝ) / (k : ℕ)) ≤
        Func.asympOnSet A + ε := by linarith
    -- Now raise both sides to the k-th power.
    have hLHS_nn : (0 : ℝ) ≤ ((Func.toFun k (tensorPow k (S i)) : ℝ)) := NNReal.coe_nonneg _
    have hk_R_pos : (0 : ℝ) < (k : ℕ) := by exact_mod_cast k.pos
    have h_inv_k_nn : (0 : ℝ) ≤ (1 : ℝ) / (k : ℕ) := by positivity
    have h_k_R_nn : (0 : ℝ) ≤ ((k : ℕ) : ℝ) := hk_R_pos.le
    have hasymp_nn : 0 ≤ Func.asympOnSet A + ε :=
      add_nonneg (asympOnSet_nonneg Func A) hε.le
    -- F(...)^(1/k))^k = F(...).
    -- Strategy: cast (k : ℕ) → ℝ via PNat.val.
    set v : ℝ := ((Func.toFun k (tensorPow k (S i)) : ℝ)) ^ ((1 : ℝ) / (k : ℕ)) with hv_def
    have hv_nn : 0 ≤ v := Real.rpow_nonneg hLHS_nn _
    -- Apply Real.rpow_le_rpow with exponent (k : ℕ) on both sides.
    have hraise : v ^ ((k : ℕ) : ℝ) ≤
          (Func.asympOnSet A + ε) ^ ((k : ℕ) : ℝ) :=
      Real.rpow_le_rpow hv_nn hroot' h_k_R_nn
    -- Simplify LHS: v^((k : ℕ) : ℝ) = v^(k : ℕ) by Real.rpow_natCast.
    rw [show (((k : ℕ) : ℝ)) = ((k : ℕ) : ℕ) from rfl] at hraise
    rw [Real.rpow_natCast v ((k : ℕ) : ℕ),
        Real.rpow_natCast (Func.asympOnSet A + ε) ((k : ℕ) : ℕ)] at hraise
    -- v^(k : ℕ) = F(S_i^⊗k).
    have hv_pow_eq : v ^ ((k : ℕ) : ℕ) = (Func.toFun k (tensorPow k (S i)) : ℝ) := by
      rw [hv_def]
      rw [← Real.rpow_natCast (((Func.toFun k (tensorPow k (S i)) : ℝ))
            ^ ((1 : ℝ) / (k : ℕ))) ((k : ℕ) : ℕ),
          ← Real.rpow_mul hLHS_nn]
      have hk_ne : ((k : ℕ) : ℝ) ≠ 0 := hk_R_pos.ne'
      have h1 : ((1 : ℝ) / (k : ℕ)) * (((k : ℕ) : ℕ) : ℝ) = 1 := by
        push_cast
        field_simp
      rw [h1, Real.rpow_one]
    rw [hv_pow_eq] at hraise
    exact hraise
  · -- Small case (Theorem 2.2): F(S_i^⊗k) ≤ B^k ≤ B^M.
    right
    have h_FSk : Func.toFun k (tensorPow k (S i)) ≤ B ^ (k : ℕ) :=
      toFun_tensorPow_le_bdd_pow Func (S i) k B hB_F1
    have h_R : ((Func.toFun k (tensorPow k (S i)) : ℝ)) ≤ ((B : ℝ)) ^ (k : ℕ) := by
      have := NNReal.coe_le_coe.mpr h_FSk
      simpa [NNReal.coe_pow] using! this
    refine h_R.trans ?_
    have hk_lt_M : (k : ℕ) < (M : ℕ) := by
      -- hk : ¬ M ≤ k as PNat, so (M : ℕ) > (k : ℕ).
      have hk' : ¬ ((M : ℕ) ≤ (k : ℕ)) := by
        intro hle
        apply hk
        exact hle
      omega
    have hB_R_one : (1 : ℝ) ≤ ((B : ℝ)) := by exact_mod_cast hB_one
    exact pow_le_pow_right₀ hB_R_one hk_lt_M.le

/--
**Multi-index combinatorial inner bound** (Theorem 2.2).
    The proof combines subadditivity, permutation invariance, submultiplicativity,
    scalar invariance and the bound on `F_1` from Definition 2.1.

    Given:
    * `T^⊗n = ∑_{i=1}^p αᵢ Sᵢ^⊗n` with `Sᵢ ∈ A` (from `exists_tensorPow_decomp`);
    * a constant `B ≥ 1` with `F_1 ≤ B`;
    * a uniform threshold `M ∈ ℕ+` such that
      `F(Sᵢ^⊗ℓ)^(1/ℓ) ≤ F̃(Sᵢ) + ε` for every `i` and every `ℓ ≥ M`,
    then for every `m : ℕ+`,
    `F_{nm}(T^⊗(nm)) ≤ p^m · (F̃[A] + ε)^(nm) · B^(p · M)`.

    Mathematically this is the paper's Theorem 2.2 chain BEFORE taking the
    `(1/(nm))`-th root.
-/
lemma nm_F_combinatorial_bound
    (Func : AdmissibleFunctional F V) (A : Set V) (T : V) (hT : T ≠ 0)
    (n : ℕ+) (ε : ℝ) (hε : 0 < ε)
    {p : ℕ} (S : Fin p → V) (α : Fin p → F)
    (hSA : ∀ i, S i ∈ A)
    (hdecomp : tensorPow (F := F) (V := V) n T = ∑ i, α i • tensorPow n (S i))
    (B : NNReal) (hB_one : 1 ≤ B) (hB_F1 : ∀ U : TensorPower F 1 V, Func.toFun 1 U ≤ B)
    (M : ℕ+)
    (hM : ∀ (i : Fin p) (ℓ : ℕ+), M ≤ ℓ →
      ((Func.toFun ℓ (tensorPow ℓ (S i)) : ℝ)) ^ ((1 : ℝ) / (ℓ : ℕ)) ≤
        Func.regularize (S i) + ε)
    (m : ℕ+) :
    ((Func.toFun (n * m) (tensorPow (F := F) (V := V) (n * m) T) : ℝ)) ≤
      ((p : ℝ) ^ (m : ℕ)) *
        ((Func.asympOnSet A + ε) ^ ((n : ℕ) * (m : ℕ))) *
        ((max (B : ℝ) ((B : ℝ) / (Func.asympOnSet A + ε))) ^ ((p : ℕ) * (M : ℕ))) := by
  classical
  -- Step 1: invoke the structural sub-lemma (Theorem 2.2).
  have hstep1 := F_tensorPow_nm_le_max_grouped_product (F := F) (V := V) Func T hT n S α
    hdecomp m
  -- Setup nonnegativity facts.
  have hasymp_nn : (0 : ℝ) ≤ Func.asympOnSet A + ε :=
    add_nonneg (asympOnSet_nonneg Func A) hε.le
  have hasymp_pos : (0 : ℝ) < Func.asympOnSet A + ε := by
    have := asympOnSet_nonneg Func A; linarith
  have hB_R_one : (1 : ℝ) ≤ ((B : ℝ)) := by exact_mod_cast hB_one
  have hB_R_pos : (0 : ℝ) < ((B : ℝ)) := lt_of_lt_of_le zero_lt_one hB_R_one
  have hB_R_nn : (0 : ℝ) ≤ ((B : ℝ)) := hB_R_pos.le
  -- The correction constant: `Bc = max B (B / (F̃[A]+ε))`. In the `≥1` case the
  -- `B/(asymp+ε) ≤ B` so `Bc = B`; in the `<1` case the small-base discrepancy
  -- `(F̃[A]+ε)^(∑_L) ≤ (F̃[A]+ε)^(nm) · (1/(F̃[A]+ε))^(pM)` is absorbed by `Bc`.
  set Bc : ℝ := max (B : ℝ) ((B : ℝ) / (Func.asympOnSet A + ε)) with hBc_def
  have hBc_ge_B : (B : ℝ) ≤ Bc := le_max_left _ _
  have hBc_ge_Bdiv : (B : ℝ) / (Func.asympOnSet A + ε) ≤ Bc := le_max_right _ _
  have hBc_one : (1 : ℝ) ≤ Bc := le_trans hB_R_one hBc_ge_B
  have hBc_nn : (0 : ℝ) ≤ Bc := le_trans zero_le_one hBc_one
  -- Step 2 + 3: for each `I`, the per-I product ≤ (F̃[A]+ε)^(nm) · Bc^(p·M).
  -- We bound the iSup by establishing the bound for each `I`.
  have hper_I : ∀ I : Fin m → Fin p,
      (∏ i : Fin p,
        (let mi : ℕ := (Finset.univ.filter (fun j : Fin m => I j = i)).card
         if hmi : 0 < mi then
           (Func.toFun ⟨mi * (n : ℕ), Nat.mul_pos hmi n.pos⟩
             (tensorPow ⟨mi * (n : ℕ), Nat.mul_pos hmi n.pos⟩ (S i)) : ℝ)
         else 1)) ≤
        ((Func.asympOnSet A + ε) ^ ((n : ℕ) * (m : ℕ))) *
          (Bc ^ ((p : ℕ) * (M : ℕ))) := by
    intro I
    -- Theorem 2.2: per-multi-index assembly.
    -- We define mi : Fin p → ℕ as the occurrence-count of i in I.
    -- The sum ∑ᵢ mᵢ = m. For each i, the per-i factor is bounded by
    -- (F̃[A]+ε)^(mᵢ·n) (large case) or B^M (small case). After partitioning
    -- Fin p into "large", "small", "zero" subsets and bounding factor-by-factor:
    -- product ≤ (F̃[A]+ε)^(∑_L mᵢ·n) · B^(|S|·M) ≤ (F̃[A]+ε)^(nm) · B^(p·M).
    set mi : Fin p → ℕ := fun i => (Finset.univ.filter (fun j : Fin m => I j = i)).card
      with hmi_def
    -- Per-i factor (with `let`-elimination).
    set fac : Fin p → ℝ := fun i =>
      if hmi_pos : 0 < mi i then
        (Func.toFun ⟨mi i * (n : ℕ), Nat.mul_pos hmi_pos n.pos⟩
          (tensorPow ⟨mi i * (n : ℕ), Nat.mul_pos hmi_pos n.pos⟩ (S i)) : ℝ)
      else 1 with hfac_def
    -- Step A: per-i bound. For each i, either factor ≤ (F̃[A]+ε)^(mi·n) (large)
    -- or factor ≤ B^M (small), with the small case taking factor = 1 included.
    -- Specifically: fac i ≤ (F̃[A]+ε)^(mi i * n) * B^M' where M' = M if small,
    -- and the M' = 0 (and (F̃[A]+ε)^... is the actual bound) if large.
    -- We bound by case split via M ≤ ⟨mi·n, _⟩.
    -- Goal: ∏ fac i ≤ (F̃[A]+ε)^(n*m) * B^(p*M).
    have hfac_nn : ∀ i, 0 ≤ fac i := by
      intro i
      simp only [hfac_def]
      split_ifs
      · exact NNReal.coe_nonneg _
      · exact zero_le_one
    -- Sum of mi equals m. (Finset partition by `I j`.)
    have hsum_mi : ∑ i : Fin p, mi i = (m : ℕ) := by
      simp only [hmi_def]
      -- ∑ i, |{j | I j = i}| = |Fin m| = m, by partition.
      have hmaps : ∀ j ∈ (Finset.univ : Finset (Fin m)),
          I j ∈ (Finset.univ : Finset (Fin p)) :=
        fun _ _ => Finset.mem_univ _
      have hcard : (Finset.univ : Finset (Fin m)).card =
          ∑ b ∈ (Finset.univ : Finset (Fin p)),
            ((Finset.univ : Finset (Fin m)).filter (fun a => I a = b)).card :=
        Finset.card_eq_sum_card_fiberwise hmaps
      simp at hcard
      simpa using! hcard.symm
    -- For each i, define the "split bound": if M ≤ ⟨mi·n, _⟩, then large case;
    -- else small case.
    -- Partition predicate.
    let isLarge : Fin p → Prop := fun i =>
      ∃ hmi_pos : 0 < mi i, (M : ℕ) ≤ mi i * (n : ℕ)
    have hisLarge_dec : ∀ i, Decidable (isLarge i) := fun i => by
      simp only [isLarge]
      by_cases hp : 0 < mi i
      · by_cases hM : (M : ℕ) ≤ mi i * (n : ℕ)
        · exact isTrue ⟨hp, hM⟩
        · exact isFalse fun ⟨_, h⟩ => hM h
      · exact isFalse fun ⟨h, _⟩ => hp h
    -- Per-i bound: fac i ≤ (F̃[A]+ε)^(mi i * n) if isLarge i, else fac i ≤ B^M.
    have hper_i_large : ∀ i, isLarge i →
        fac i ≤ (Func.asympOnSet A + ε) ^ (mi i * (n : ℕ)) := by
      intro i ⟨hmi_pos, hMle⟩
      -- Use F_S_pow_split_bound with k := ⟨mi i * n, _⟩.
      have hk_pos : 0 < mi i * (n : ℕ) := Nat.mul_pos hmi_pos n.pos
      let k : ℕ+ := ⟨mi i * (n : ℕ), hk_pos⟩
      have hk_eq : (k : ℕ) = mi i * (n : ℕ) := rfl
      -- Apply F_S_pow_split_bound on the LARGE case directly via hM.
      -- F(S_i^⊗k)^(1/k) ≤ F̃(S_i) + ε  (from hM since M ≤ k).
      have hMk : M ≤ k := by
        change (M : ℕ) ≤ (k : ℕ)
        simpa [hk_eq] using! hMle
      have hroot := hM i k hMk
      -- F̃(S_i) ≤ F̃[A] (since S_i ∈ A).
      have hSi_le_asymp : Func.regularize (S i) ≤ Func.asympOnSet A := by
        unfold AdmissibleFunctional.asympOnSet
        have hbdd : BddAbove (Set.range fun T : V => ⨆ _ : T ∈ A, Func.regularize T) :=
          asympOnSet_bddAbove Func A
        calc Func.regularize (S i)
            = (⨆ _ : (S i) ∈ A, Func.regularize (S i)) := by
              rw [iSup_mem_eq, if_pos (hSA i)]
          _ ≤ (⨆ T : V, ⨆ _ : T ∈ A, Func.regularize T) := le_ciSup hbdd (S i)
      have hroot' : ((Func.toFun k (tensorPow k (S i)) : ℝ)) ^ ((1 : ℝ) / (k : ℕ)) ≤
          Func.asympOnSet A + ε := by linarith
      -- Now raise both sides to k-th power.
      have hLHS_nn : (0 : ℝ) ≤ ((Func.toFun k (tensorPow k (S i)) : ℝ)) :=
        NNReal.coe_nonneg _
      have hk_R_pos : (0 : ℝ) < (k : ℕ) := by exact_mod_cast hk_pos
      have hk_R_nn : (0 : ℝ) ≤ ((k : ℕ) : ℝ) := hk_R_pos.le
      set v : ℝ := ((Func.toFun k (tensorPow k (S i)) : ℝ)) ^ ((1 : ℝ) / (k : ℕ)) with hv_def
      have hv_nn : 0 ≤ v := Real.rpow_nonneg hLHS_nn _
      have hasymp_nn' : 0 ≤ Func.asympOnSet A + ε :=
        add_nonneg (asympOnSet_nonneg Func A) hε.le
      have hraise : v ^ ((k : ℕ) : ℝ) ≤
            (Func.asympOnSet A + ε) ^ ((k : ℕ) : ℝ) :=
        Real.rpow_le_rpow hv_nn hroot' hk_R_nn
      rw [Real.rpow_natCast v ((k : ℕ)),
          Real.rpow_natCast (Func.asympOnSet A + ε) ((k : ℕ))] at hraise
      have hv_pow_eq : v ^ ((k : ℕ)) = (Func.toFun k (tensorPow k (S i)) : ℝ) := by
        rw [hv_def]
        rw [← Real.rpow_natCast (((Func.toFun k (tensorPow k (S i)) : ℝ))
              ^ ((1 : ℝ) / (k : ℕ))) ((k : ℕ)),
            ← Real.rpow_mul hLHS_nn]
        have hk_ne : ((k : ℕ) : ℝ) ≠ 0 := hk_R_pos.ne'
        have h1 : ((1 : ℝ) / (k : ℕ)) * (((k : ℕ)) : ℝ) = 1 := by
          field_simp
        rw [h1, Real.rpow_one]
      rw [hv_pow_eq] at hraise
      -- Goal: fac i ≤ (F̃[A]+ε)^(mi i * n). With `k = ⟨mi i * n, hk_pos⟩`,
      -- fac i = Func.toFun k (tensorPow k (S i)) by `dif_pos`. And from hraise,
      -- Func.toFun k (...) ≤ (F̃[A]+ε)^k = (F̃[A]+ε)^(mi i * n).
      have : fac i = (Func.toFun k (tensorPow k (S i)) : ℝ) := by
        change (if hmi_pos : 0 < mi i then
              ((Func.toFun ⟨mi i * (n : ℕ), Nat.mul_pos hmi_pos n.pos⟩
                (tensorPow ⟨mi i * (n : ℕ), Nat.mul_pos hmi_pos n.pos⟩ (S i))) : ℝ)
              else 1) = _
        rw [dif_pos hmi_pos]
      rw [this]
      -- Goal: Func.toFun k (...) ≤ (F̃[A]+ε)^(mi i * n).
      have hexp_eq : (k : ℕ) = mi i * (n : ℕ) := hk_eq
      rw [← hexp_eq]
      exact hraise
    have hper_i_small : ∀ i, ¬ isLarge i → fac i ≤ ((B : ℝ)) ^ (M : ℕ) := by
      intro i hnot
      -- Case split on mi i = 0 or mi i > 0 ∧ mi·n < M.
      by_cases hmi_pos : 0 < mi i
      · -- mi i > 0; from ¬ isLarge, get ¬ ((M : ℕ) ≤ mi i * n).
        have hM_gt : mi i * (n : ℕ) < (M : ℕ) := by
          have := hnot
          simp only [isLarge] at this
          push_neg at this
          exact this hmi_pos
        have hk_pos : 0 < mi i * (n : ℕ) := Nat.mul_pos hmi_pos n.pos
        let k : ℕ+ := ⟨mi i * (n : ℕ), hk_pos⟩
        have hk_eq : (k : ℕ) = mi i * (n : ℕ) := rfl
        -- F(S_i^⊗k) ≤ B^k ≤ B^M (since k < M and B ≥ 1).
        have h_FSk : Func.toFun k (tensorPow k (S i)) ≤ B ^ (k : ℕ) :=
          toFun_tensorPow_le_bdd_pow Func (S i) k B hB_F1
        have h_R : ((Func.toFun k (tensorPow k (S i)) : ℝ)) ≤ ((B : ℝ)) ^ (k : ℕ) := by
          have := NNReal.coe_le_coe.mpr h_FSk
          simpa [NNReal.coe_pow] using! this
        have hk_lt_M : (k : ℕ) < (M : ℕ) := by simpa [hk_eq] using! hM_gt
        have hB_pow_le : ((B : ℝ)) ^ (k : ℕ) ≤ ((B : ℝ)) ^ (M : ℕ) :=
          pow_le_pow_right₀ hB_R_one hk_lt_M.le
        have hfac_eq : fac i = (Func.toFun k (tensorPow k (S i)) : ℝ) := by
          change (if hmi_pos : 0 < mi i then
                ((Func.toFun ⟨mi i * (n : ℕ), Nat.mul_pos hmi_pos n.pos⟩
                  (tensorPow ⟨mi i * (n : ℕ), Nat.mul_pos hmi_pos n.pos⟩ (S i))) : ℝ)
                else 1) = _
          rw [dif_pos hmi_pos]
        rw [hfac_eq]
        exact h_R.trans hB_pow_le
      · -- mi i = 0; fac i = 1 ≤ B^M.
        have hfac_eq : fac i = 1 := by
          change (if hmi_pos : 0 < mi i then
                ((Func.toFun ⟨mi i * (n : ℕ), Nat.mul_pos hmi_pos n.pos⟩
                  (tensorPow ⟨mi i * (n : ℕ), Nat.mul_pos hmi_pos n.pos⟩ (S i))) : ℝ)
                else 1) = _
          rw [dif_neg hmi_pos]
        rw [hfac_eq]
        exact one_le_pow₀ hB_R_one
    -- Partition Fin p into L (large) and notL (rest = small or zero).
    -- For zero i's, fac i = 1 ≤ B^M, so they're "small" too. Combine.
    -- We use the partition: large = filter isLarge; notLarge = filter ¬ isLarge.
    have hp_le : 0 ≤ ((Func.asympOnSet A + ε) ^ ((n : ℕ) * (m : ℕ))) *
        ((B : ℝ) ^ ((p : ℕ) * (M : ℕ))) := by
      apply mul_nonneg
      · exact pow_nonneg hasymp_nn _
      · exact pow_nonneg hB_R_nn _
    -- Now bound each subproduct.
    -- (a) ∏_L fac ≤ ∏_L (F̃[A]+ε)^(mi · n) = (F̃[A]+ε)^(∑_L mi · n) ≤ (F̃[A]+ε)^(n·m).
    haveI : DecidablePred isLarge := hisLarge_dec
    -- Decidable instance for ¬·∘isLarge.
    have hsumtot : ∑ i : Fin p, mi i * (n : ℕ) = (n : ℕ) * (m : ℕ) := by
      rw [← Finset.sum_mul, hsum_mi]; ring
    have h_sum_L_le : ∑ i ∈ Finset.univ.filter isLarge, mi i * (n : ℕ) ≤ (n : ℕ) * (m : ℕ) := by
      have h_filter_sum_le :
          ∑ i ∈ Finset.univ.filter isLarge, mi i * (n : ℕ) ≤
            ∑ i : Fin p, mi i * (n : ℕ) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
        · exact Finset.filter_subset _ _
        · intros _ _ _; exact Nat.zero_le _
      linarith
    -- Lower bound on `∑_L`: the complement (¬large blocks) carries
    -- `∑_{¬L} mᵢn < p · M` (each ¬large block has `mᵢn < M`, ≤ p blocks).
    -- Hence `∑_L = nm - ∑_{¬L} ≥ nm - pM`.
    have h_sum_notL_lt : ∑ i ∈ Finset.univ.filter (fun i : Fin p => ¬ isLarge i),
        mi i * (n : ℕ) ≤ (p : ℕ) * (M : ℕ) := by
      calc ∑ i ∈ Finset.univ.filter (fun i : Fin p => ¬ isLarge i), mi i * (n : ℕ)
          ≤ ∑ _i ∈ Finset.univ.filter (fun i : Fin p => ¬ isLarge i), (M : ℕ) := by
            refine Finset.sum_le_sum (fun i hi => ?_)
            have hnL : ¬ isLarge i := (Finset.mem_filter.mp hi).2
            by_cases hmi_pos : 0 < mi i
            · have hlt : mi i * (n : ℕ) < (M : ℕ) := by
                have := hnL; simp only [isLarge] at this; push_neg at this
                exact this hmi_pos
              exact hlt.le
            · push_neg at hmi_pos
              interval_cases (mi i)
              simp
        _ = (Finset.univ.filter (fun i : Fin p => ¬ isLarge i)).card * (M : ℕ) := by
            rw [Finset.sum_const, smul_eq_mul]
        _ ≤ (p : ℕ) * (M : ℕ) := by
            apply Nat.mul_le_mul_right
            have := Finset.card_filter_le Finset.univ (fun i : Fin p => ¬ isLarge i)
            simpa using! this
    have h_sum_L_ge : (n : ℕ) * (m : ℕ) - (p : ℕ) * (M : ℕ) ≤
        ∑ i ∈ Finset.univ.filter isLarge, mi i * (n : ℕ) := by
      have hsplit : (∑ i ∈ Finset.univ.filter isLarge, mi i * (n : ℕ)) +
          (∑ i ∈ Finset.univ.filter (fun i : Fin p => ¬ isLarge i), mi i * (n : ℕ)) =
          (n : ℕ) * (m : ℕ) := by
        rw [Finset.sum_filter_add_sum_filter_not Finset.univ isLarge]; exact hsumtot
      omega
    have h_prod_L_le :
        (∏ i ∈ Finset.univ.filter isLarge, fac i) ≤
          (Func.asympOnSet A + ε) ^
            (∑ i ∈ Finset.univ.filter isLarge, mi i * (n : ℕ)) := by
      calc (∏ i ∈ Finset.univ.filter isLarge, fac i)
          ≤ ∏ i ∈ Finset.univ.filter isLarge,
              (Func.asympOnSet A + ε) ^ (mi i * (n : ℕ)) := by
            apply Finset.prod_le_prod₀
            · intros i _; exact hfac_nn i
            · intros i hi
              have hL : isLarge i := (Finset.mem_filter.mp hi).2
              exact hper_i_large i hL
        _ = (Func.asympOnSet A + ε) ^
              (∑ i ∈ Finset.univ.filter isLarge, mi i * (n : ℕ)) := by
            rw [← Finset.prod_pow_eq_pow_sum]
    -- (b) ∏_¬L fac ≤ ∏_¬L B^M ≤ B^(|¬L| · M) ≤ B^(p · M).
    have h_card_notL_le_p :
        (Finset.univ.filter (fun i : Fin p => ¬ isLarge i)).card ≤ p := by
      have := (Finset.card_filter_le Finset.univ (fun i : Fin p => ¬ isLarge i))
      simpa using! this
    have h_prod_notL_le :
        (∏ i ∈ Finset.univ.filter (fun i : Fin p => ¬ isLarge i), fac i) ≤
          ((B : ℝ)) ^ ((p : ℕ) * (M : ℕ)) := by
      calc (∏ i ∈ Finset.univ.filter (fun i : Fin p => ¬ isLarge i), fac i)
          ≤ ∏ _i ∈ Finset.univ.filter (fun i : Fin p => ¬ isLarge i),
              ((B : ℝ)) ^ (M : ℕ) := by
            apply Finset.prod_le_prod₀
            · intros i _; exact hfac_nn i
            · intros i hi
              have hnL : ¬ isLarge i := (Finset.mem_filter.mp hi).2
              exact hper_i_small i hnL
        _ = ((B : ℝ)) ^ ((Finset.univ.filter (fun i : Fin p => ¬ isLarge i)).card *
              (M : ℕ)) := by
            rw [Finset.prod_const, ← pow_mul, mul_comm]
        _ ≤ ((B : ℝ)) ^ ((p : ℕ) * (M : ℕ)) := by
            apply pow_le_pow_right₀ hB_R_one
            exact Nat.mul_le_mul_right _ h_card_notL_le_p
    -- (c) Combine. Key sub-bound (valid for ALL `F̃[A]+ε ≥ 0`, base `≥1` OR `<1`):
    --   `(F̃[A]+ε)^(∑_L) · B^(pM) ≤ (F̃[A]+ε)^(nm) · Bc^(pM)`, where
    --   `Bc = max B (B/(F̃[A]+ε))`.  In the `≥1` case `∑_L ≤ nm` gives
    --   `(F̃[A]+ε)^(∑_L) ≤ (F̃[A]+ε)^(nm)`; in the `<1` case `∑_L ≥ nm - pM` gives
    --   `(F̃[A]+ε)^(∑_L) ≤ (F̃[A]+ε)^(nm - pM) = (F̃[A]+ε)^(nm)·(1/(F̃[A]+ε))^(pM)`,
    --   and `(1/(F̃[A]+ε))^(pM)·B^(pM) = (B/(F̃[A]+ε))^(pM) ≤ Bc^(pM)`.
    set sL : ℕ := ∑ i ∈ Finset.univ.filter isLarge, mi i * (n : ℕ) with hsL_def
    have h_combine_bound :
        (Func.asympOnSet A + ε) ^ sL * (B : ℝ) ^ ((p : ℕ) * (M : ℕ)) ≤
          (Func.asympOnSet A + ε) ^ ((n : ℕ) * (m : ℕ)) * Bc ^ ((p : ℕ) * (M : ℕ)) := by
      by_cases hge : 1 ≤ Func.asympOnSet A + ε
      · -- `≥1` case: `(asymp+ε)^(sL) ≤ (asymp+ε)^(nm)` and `B^(pM) ≤ Bc^(pM)`.
        apply mul_le_mul
        · exact pow_le_pow_right₀ hge h_sum_L_le
        · exact pow_le_pow_left₀ hB_R_nn hBc_ge_B _
        · exact pow_nonneg hB_R_nn _
        · exact pow_nonneg hasymp_nn _
      · -- `<1` case.
        push_neg at hge
        -- `(asymp+ε)^(sL) ≤ (asymp+ε)^(nm - pM)` (base < 1, sL ≥ nm - pM).
        have hbase_le_one : Func.asympOnSet A + ε ≤ 1 := hge.le
        have hstep1 : (Func.asympOnSet A + ε) ^ sL ≤
            (Func.asympOnSet A + ε) ^ ((n : ℕ) * (m : ℕ) - (p : ℕ) * (M : ℕ)) :=
          pow_le_pow_of_le_one hasymp_nn hbase_le_one (hsL_def ▸ h_sum_L_ge)
        -- `(asymp+ε)^(nm - pM) · (asymp+ε)^(pM) = (asymp+ε)^(nm)` if `pM ≤ nm`;
        -- more simply: `(asymp+ε)^(nm-pM) = (asymp+ε)^(nm) / (asymp+ε)^(pM)`.
        -- We bound `(asymp+ε)^(nm-pM) · B^(pM) ≤ (asymp+ε)^(nm) · Bc^(pM)`.
        -- Note `(asymp+ε)^(nm-pM) ≤ (asymp+ε)^(nm) · (1/(asymp+ε))^(pM)`
        -- because `(asymp+ε)^(nm) = (asymp+ε)^(nm-pM)·(asymp+ε)^(min(pM,nm))≤...`.
        -- Cleanest: multiply both sides by `(asymp+ε)^(pM) > 0` is awkward with ℕ-sub.
        -- Instead bound directly via the division form.
        have hpos := hasymp_pos
        have hkey : (Func.asympOnSet A + ε) ^ ((n : ℕ) * (m : ℕ) - (p : ℕ) * (M : ℕ)) *
            (B : ℝ) ^ ((p : ℕ) * (M : ℕ)) ≤
            (Func.asympOnSet A + ε) ^ ((n : ℕ) * (m : ℕ)) * Bc ^ ((p : ℕ) * (M : ℕ)) := by
          -- Reduce to: `(asymp+ε)^(nm-pM) · B^(pM) ≤ (asymp+ε)^(nm) · (B/(asymp+ε))^(pM)`
          -- then `(B/(asymp+ε))^(pM) ≤ Bc^(pM)`.
          have hBdiv_nn : (0 : ℝ) ≤ (B : ℝ) / (Func.asympOnSet A + ε) := by positivity
          set c : ℝ := Func.asympOnSet A + ε with hc_def
          have hc_pos : 0 < c := hasymp_pos
          have hcpow_pos : (0 : ℝ) < c ^ ((p : ℕ) * (M : ℕ)) := pow_pos hc_pos _
          -- `c^(nm-pM) · B^(pM) ≤ c^(nm) · (B/c)^(pM)`.
          -- Key: `c^(nm-pM) · c^(pM) = c^((nm-pM)+pM) ≤ c^(nm)` (base ≤ 1, exponent ≥ nm).
          have hc_exp : c ^ ((n : ℕ) * (m : ℕ) - (p : ℕ) * (M : ℕ)) * c ^ ((p : ℕ) * (M : ℕ)) ≤
              c ^ ((n : ℕ) * (m : ℕ)) := by
            rw [← pow_add]
            apply pow_le_pow_of_le_one hasymp_nn hbase_le_one
            omega
          have hmid : c ^ ((n : ℕ) * (m : ℕ) - (p : ℕ) * (M : ℕ)) *
              (B : ℝ) ^ ((p : ℕ) * (M : ℕ)) ≤
              c ^ ((n : ℕ) * (m : ℕ)) *
                ((B : ℝ) / c) ^ ((p : ℕ) * (M : ℕ)) := by
            rw [div_pow, mul_div_assoc', le_div_iff₀ hcpow_pos]
            -- Goal: c^(nm-pM)·B^(pM)·c^(pM) ≤ c^(nm)·B^(pM).
            calc c ^ ((n : ℕ) * (m : ℕ) - (p : ℕ) * (M : ℕ)) * (B : ℝ) ^ ((p : ℕ) * (M : ℕ)) *
                  c ^ ((p : ℕ) * (M : ℕ))
                = (c ^ ((n : ℕ) * (m : ℕ) - (p : ℕ) * (M : ℕ)) * c ^ ((p : ℕ) * (M : ℕ))) *
                    (B : ℝ) ^ ((p : ℕ) * (M : ℕ)) := by ring
              _ ≤ c ^ ((n : ℕ) * (m : ℕ)) * (B : ℝ) ^ ((p : ℕ) * (M : ℕ)) :=
                  mul_le_mul_of_nonneg_right hc_exp (pow_nonneg hB_R_nn _)
          refine hmid.trans ?_
          apply mul_le_mul_of_nonneg_left _ (pow_nonneg hasymp_nn _)
          exact pow_le_pow_left₀ hBdiv_nn hBc_ge_Bdiv _
        calc (Func.asympOnSet A + ε) ^ sL * (B : ℝ) ^ ((p : ℕ) * (M : ℕ))
            ≤ (Func.asympOnSet A + ε) ^ ((n : ℕ) * (m : ℕ) - (p : ℕ) * (M : ℕ)) *
                (B : ℝ) ^ ((p : ℕ) * (M : ℕ)) :=
              mul_le_mul_of_nonneg_right hstep1 (pow_nonneg hB_R_nn _)
          _ ≤ _ := hkey
    calc ∏ i : Fin p, fac i
        = (∏ i ∈ Finset.univ.filter isLarge, fac i) *
            (∏ i ∈ Finset.univ.filter (fun i : Fin p => ¬ isLarge i), fac i) := by
          rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ isLarge fac]
      _ ≤ (Func.asympOnSet A + ε) ^ sL * (B : ℝ) ^ ((p : ℕ) * (M : ℕ)) := by
          apply mul_le_mul h_prod_L_le h_prod_notL_le
          · apply Finset.prod_nonneg; intros i _; exact hfac_nn i
          · exact pow_nonneg hasymp_nn _
      _ ≤ ((Func.asympOnSet A + ε) ^ ((n : ℕ) * (m : ℕ))) *
            (Bc ^ ((p : ℕ) * (M : ℕ))) := h_combine_bound
  -- Step 4: bound the iSup by the per-I bound.
  -- Case-split on `p = 0` vs `0 < p` to handle the empty-supremum case.
  have hSup : ⨆ (I : Fin m → Fin p),
      (∏ i : Fin p,
        (let mi : ℕ := (Finset.univ.filter (fun j : Fin m => I j = i)).card
         if hmi : 0 < mi then
           (Func.toFun ⟨mi * (n : ℕ), Nat.mul_pos hmi n.pos⟩
             (tensorPow ⟨mi * (n : ℕ), Nat.mul_pos hmi n.pos⟩ (S i)) : ℝ)
         else 1)) ≤
        ((Func.asympOnSet A + ε) ^ ((n : ℕ) * (m : ℕ))) *
          (Bc ^ ((p : ℕ) * (M : ℕ))) := by
    by_cases hp_pos : 0 < p
    · -- Nonempty case: `Fin m → Fin p` is nonempty since both are nonempty.
      haveI : Nonempty (Fin p) := ⟨⟨0, hp_pos⟩⟩
      haveI : Nonempty (Fin m → Fin p) := ⟨fun _ => ⟨0, hp_pos⟩⟩
      refine ciSup_le ?_
      intro I
      exact hper_I I
    · -- Empty case: `p = 0`, so `Fin m → Fin 0` is empty (since m ≥ 1).
      push_neg at hp_pos
      interval_cases p
      haveI : IsEmpty (Fin m → Fin 0) := ⟨fun f => (f ⟨0, m.pos⟩).elim0⟩
      rw [Real.iSup_of_isEmpty]
      have hrhs_nn : 0 ≤ ((Func.asympOnSet A + ε) ^ ((n : ℕ) * (m : ℕ))) *
          (Bc ^ ((0 : ℕ) * (M : ℕ))) := by
        apply mul_nonneg
        · exact pow_nonneg hasymp_nn _
        · exact pow_nonneg hBc_nn _
      exact hrhs_nn
  -- Step 5: combine Step 1 and Step 4.
  have hp_R_nn : (0 : ℝ) ≤ ((p : ℝ)) := Nat.cast_nonneg _
  have hpm_nn : (0 : ℝ) ≤ ((p : ℝ)) ^ (m : ℕ) := pow_nonneg hp_R_nn _
  calc ((Func.toFun (n * m) (tensorPow (n * m) T) : ℝ))
      ≤ ((p : ℝ) ^ (m : ℕ)) *
          ⨆ (I : Fin m → Fin p),
            (∏ i : Fin p,
              (let mi : ℕ := (Finset.univ.filter (fun j : Fin m => I j = i)).card
               if hmi : 0 < mi then
                 (Func.toFun ⟨mi * (n : ℕ), Nat.mul_pos hmi n.pos⟩
                   (tensorPow ⟨mi * (n : ℕ), Nat.mul_pos hmi n.pos⟩ (S i)) : ℝ)
               else 1)) := hstep1
    _ ≤ ((p : ℝ) ^ (m : ℕ)) *
          (((Func.asympOnSet A + ε) ^ ((n : ℕ) * (m : ℕ))) *
            (Bc ^ ((p : ℕ) * (M : ℕ)))) :=
          mul_le_mul_of_nonneg_left hSup hpm_nn
    _ = ((p : ℝ) ^ (m : ℕ)) *
          ((Func.asympOnSet A + ε) ^ ((n : ℕ) * (m : ℕ))) *
          (Bc ^ ((p : ℕ) * (M : ℕ))) := by ring

/--
`∀ m, F(T^⊗(nm))^(1/(nm)) ≤ p(n)^(1/n) · (F̃[A] + ε) · B^(p(n) · M / (nm))`

where `B` is the `F_1`-bound (from `Func.bdd_one`) and `M` is the `regularize_approximation`
threshold for the `S_i` decomposition (so `M` depends on `(ε, n)` but not on `m`).

This is the load-bearing combinatorial step from the paper:
* (i) subadditivity, (iv) scalar invariance: Theorem 2.2 (bound by `p^m · max`)
* (iii) permutation invariance: Theorem 2.2 (rearrange to `⊗_i S_i^⊗(m_i n)`)
* (ii) submultiplicativity: Theorem 2.2 (bound by `∏_i F(S_i^⊗(m_i n))`)
* `regularize_approximation` + `toFun_tensorPow_le_bdd_pow`: Theorem 2.2
* combine and take `(1/(nm))`-th root: Theorem 2.2.
-/
lemma tensorPow_nm_inner_bound
    (Func : AdmissibleFunctional F V) (A : Set V) (T : V)
    (hT : T ∈ zariskiClosure (F := F) A) (hT0 : T ≠ 0)
    (hd_pos : 0 < Module.finrank F V)
    (n : ℕ+) (ε : ℝ) (hε : 0 < ε) :
    ∃ (B : ℝ) (Meps : ℕ),
      1 ≤ B ∧
      ∀ m : ℕ+,
        let pn : ℝ :=
          (Nat.choose (Module.finrank F V + (n : ℕ) - 1) (n : ℕ) : ℝ)
        let nm : ℕ+ := n * m
        ((Func.toFun nm (tensorPow nm T) : ℝ)) ^ ((1 : ℝ) / (nm : ℕ)) ≤
          pn ^ ((1 : ℝ) / (n : ℕ)) *
            (Func.asympOnSet A + ε) *
            B ^ ((pn * (Meps : ℝ)) / ((n : ℕ) * (m : ℕ) : ℝ)) := by
  classical
  -- Step 1: Extract the n-th decomposition T^⊗n = ∑ᵢ αᵢ Sᵢ^⊗n with Sᵢ ∈ A.
  obtain ⟨p, S, α, hSA, hdecomp, hp_bound⟩ := exists_tensorPow_decomp_bounded A T n hT
  -- Step 2: F_1 bound (axiom (v), Definition 2.1), forced to be ≥ 1.
  obtain ⟨B₀, hB₀⟩ := Func.bdd_one
  set B : NNReal := max 1 B₀ with hB_def
  have hB_one : (1 : NNReal) ≤ B := le_max_left _ _
  have hB_F1 : ∀ U : TensorPower F 1 V, Func.toFun 1 U ≤ B := fun U =>
    (hB₀ U).trans (le_max_right _ _)
  have hB_R_ge_one : (1 : ℝ) ≤ (B : ℝ) := by exact_mod_cast hB_one
  have hB_R_pos : (0 : ℝ) < (B : ℝ) := lt_of_lt_of_le zero_lt_one hB_R_ge_one
  -- The witness constant `Bw = max B (B/(F̃[A]+ε))`. It coincides with `B` in the
  -- `F̃[A]+ε ≥ 1` regime and absorbs the small-base correction `(1/(F̃[A]+ε))^(pM)`
  -- in the `F̃[A]+ε < 1` regime (Theorem 2.2). Since `Bw ≥ 1` is a constant
  -- (independent of `m`), the downstream `Bw^(pn·Meps/(nm)) → 1` limit is unchanged.
  set Bw : ℝ := max (B : ℝ) ((B : ℝ) / (Func.asympOnSet A + ε)) with hBw_def
  have hBw_ge_B : (B : ℝ) ≤ Bw := le_max_left _ _
  have hBw_ge_one : (1 : ℝ) ≤ Bw := le_trans hB_R_ge_one hBw_ge_B
  have hBw_pos : (0 : ℝ) < Bw := lt_of_lt_of_le zero_lt_one hBw_ge_one
  -- Step 3: per-i thresholds Mᵢ (the "∀ ℓ ≥ Mᵢ" strengthening of `regularize_approximation`).
  have hM_each : ∀ i : Fin p, ∃ Mᵢ : ℕ+,
      ∀ ℓ : ℕ+, Mᵢ ≤ ℓ →
        ((Func.toFun ℓ (tensorPow ℓ (S i)) : ℝ)) ^ ((1 : ℝ) / (ℓ : ℕ)) ≤
          Func.regularize (S i) + ε := fun i =>
    -- The "for all ℓ ≥ Mᵢ" Fekete strengthening of `regularize_approximation`
    -- (Theorem 2.2). Discharged by `regularize_approximation_uniform`,
    -- which upgrades the single-witness infimum bound to a uniform bound via
    -- `Subadditive.eventually_div_lt_of_div_lt` (Fekete's lemma).
    regularize_approximation_uniform Func (S i) ε hε
  choose Mi hMi using hM_each
  -- Uniform threshold over `Fin p`. Handle the `p = 0` case (empty decomposition,
  -- so `T^⊗n = 0`) inline by defaulting to MepsP = 1; the bound then needs no
  -- per-i Mᵢ at all.
  set MepsP : ℕ+ := if h : 0 < p then
    haveI : Nonempty (Fin p) := ⟨⟨0, h⟩⟩
    (Finset.univ.sup' Finset.univ_nonempty fun i : Fin p => Mi i) ⊔ 1
  else 1 with hMepsP_def
  have hMepsP_ge_Mi : ∀ i : Fin p, Mi i ≤ MepsP := fun i => by
    have hp_pos : 0 < p := i.pos
    simp only [hMepsP_def, dif_pos hp_pos]
    refine le_trans ?_ le_sup_left
    exact Finset.le_sup' (fun j : Fin p => Mi j) (Finset.mem_univ i)
  set Meps : ℕ := (MepsP : ℕ) with hMeps_def
  have hMepsP_unif : ∀ (i : Fin p) (ℓ : ℕ+), MepsP ≤ ℓ →
      ((Func.toFun ℓ (tensorPow ℓ (S i)) : ℝ)) ^ ((1 : ℝ) / (ℓ : ℕ)) ≤
        Func.regularize (S i) + ε := fun i ℓ hℓ =>
    hMi i ℓ ((hMepsP_ge_Mi i).trans hℓ)
  refine ⟨Bw, Meps, hBw_ge_one, ?_⟩
  intro m
  dsimp only
  set pn : ℝ := (Nat.choose (Module.finrank F V + (n : ℕ) - 1) (n : ℕ) : ℝ) with hpn_def
  set nm : ℕ+ := n * m with hnm_def
  -- Apply the load-bearing combinatorial sub-helper (`nm_F_combinatorial_bound`),
  -- now valid for ALL `F̃[A]+ε ≥ 0` (both `≥1` and `<1` regimes) with the
  -- correction constant `Bw = max B (B/(F̃[A]+ε))` (Theorem 2.2).
  have hcomb : ((Func.toFun (n * m) (tensorPow (n * m) T) : ℝ)) ≤
      ((p : ℝ) ^ (m : ℕ)) *
        ((Func.asympOnSet A + ε) ^ ((n : ℕ) * (m : ℕ))) *
        (Bw ^ ((p : ℕ) * (MepsP : ℕ))) :=
    nm_F_combinatorial_bound (F := F) (V := V) Func A T hT0 n ε hε
      S α hSA hdecomp B hB_one hB_F1 MepsP hMepsP_unif m
  -- Setup: nonnegativity lemmas.
  have hLHS_nn : (0 : ℝ) ≤ (Func.toFun nm (tensorPow nm T) : ℝ) := NNReal.coe_nonneg _
  have hP_R_nn : (0 : ℝ) ≤ ((p : ℝ)) := Nat.cast_nonneg _
  -- `pn ≥ 1`: `n ≤ d + n - 1` since `d ≥ 1` (`hd_pos`).
  have h_n_le : (n : ℕ) ≤ Module.finrank F V + (n : ℕ) - 1 := by
    have hn_pos : 0 < (n : ℕ) := n.pos
    omega
  have hpn_ge_one : (1 : ℝ) ≤ pn := by
    have hge : 1 ≤ Nat.choose (Module.finrank F V + (n : ℕ) - 1) (n : ℕ) :=
      Nat.choose_pos h_n_le
    have : (1 : ℝ) ≤ (Nat.choose (Module.finrank F V + (n : ℕ) - 1) (n : ℕ) : ℝ) := by
      exact_mod_cast hge
    exact this
  have hpn_pos : (0 : ℝ) < pn := lt_of_lt_of_le zero_lt_one hpn_ge_one
  have hpn_nn : (0 : ℝ) ≤ pn := hpn_pos.le
  -- The "p ≤ p_n" bound (Lemma 2.3 + finrank Sym^n V = binom).
  have hp_le_pn : ((p : ℝ)) ≤ pn := by
    -- `exists_tensorPow_decomp_bounded` (Theorem 2.2, linear independence)
    -- gives `p ≤ dim (span A^(n))`; `finrank_span_powerSet_le_choose`
    -- (Theorem 2.2, `dim span A^(n) ≤ dim Sym^n V = binom(d+n-1,n)`)
    -- gives the rest.
    have hchain : p ≤ Nat.choose (Module.finrank F V + (n : ℕ) - 1) (n : ℕ) :=
      hp_bound.trans (finrank_span_powerSet_le_choose A n)
    calc ((p : ℝ)) ≤ (Nat.choose (Module.finrank F V + (n : ℕ) - 1) (n : ℕ) : ℝ) := by
          exact_mod_cast hchain
      _ = pn := by rw [hpn_def]
  -- Nonnegativity of the post-combinatorial RHS factor.
  have h_asymp_nn : 0 ≤ Func.asympOnSet A + ε :=
    add_nonneg (asympOnSet_nonneg Func A) hε.le
  have hpow_le : 0 ≤ (((p : ℝ)) ^ (m : ℕ)) *
        ((Func.asympOnSet A + ε) ^ ((n : ℕ) * (m : ℕ))) *
        (Bw ^ ((p : ℕ) * (MepsP : ℕ))) := by
    positivity
  have hnm_pos : (0 : ℕ) < (nm : ℕ) := nm.pos
  have hnm_R_pos : (0 : ℝ) < (nm : ℕ) := by exact_mod_cast hnm_pos
  have h_inv_nm_nn : (0 : ℝ) ≤ (1 : ℝ) / (nm : ℕ) := by positivity
  -- Take (1/(nm))-th root.
  have h_root :
      ((Func.toFun nm (tensorPow nm T) : ℝ)) ^ ((1 : ℝ) / (nm : ℕ)) ≤
        ((((p : ℝ)) ^ (m : ℕ)) *
          ((Func.asympOnSet A + ε) ^ ((n : ℕ) * (m : ℕ))) *
          (Bw ^ ((p : ℕ) * (MepsP : ℕ)))) ^ ((1 : ℝ) / (nm : ℕ)) :=
    Real.rpow_le_rpow hLHS_nn hcomb h_inv_nm_nn
  refine h_root.trans ?_
  -- Now compute the RHS root.
  -- RHS = (p^m)^(1/(nm)) · ((F̃[A]+ε)^(nm))^(1/(nm)) · (B^(p · M))^(1/(nm))
  --     = p^(m/(nm)) · (F̃[A]+ε)^(nm/(nm)) · B^(p·M/(nm))
  --     = p^(1/n) · (F̃[A]+ε) · B^(p·M/(nm))
  -- We need this ≤ pn^(1/n) · (F̃[A]+ε) · B^(pn·Meps/(nm)).
  -- Steps:
  --  1. p^(1/n) ≤ pn^(1/n) since p ≤ pn and 1/n ≥ 0.
  --  2. B^(p·M/(nm)) ≤ B^(pn·Meps/(nm)) since B ≥ 1 and p·M ≤ pn·Meps.
  -- Both ≤'s combine multiplicatively (RHS factors all ≥ 0).
  -- Cast to real-rpow form first.
  -- We're going to rewrite using Real.rpow lemmas.
  set asymp : ℝ := Func.asympOnSet A + ε with hasymp_def
  have hasymp_nn : 0 ≤ asymp := add_nonneg (asympOnSet_nonneg Func A) hε.le
  -- Compute the RHS product root.
  -- Let f := p^m, g := asymp^(nm), h := B^(p·M).
  -- (f·g·h)^(1/(nm)) = f^(1/(nm)) · g^(1/(nm)) · h^(1/(nm)).
  have hf_nn : (0 : ℝ) ≤ ((p : ℝ)) ^ (m : ℕ) := pow_nonneg hP_R_nn _
  have hg_nn : (0 : ℝ) ≤ (asymp ^ ((n : ℕ) * (m : ℕ))) := pow_nonneg hasymp_nn _
  have hh_nn : (0 : ℝ) ≤ (Bw ^ ((p : ℕ) * (MepsP : ℕ))) := pow_nonneg hBw_pos.le _
  have h_rpow_mul1 :
      (((p : ℝ)) ^ (m : ℕ) * asymp ^ ((n : ℕ) * (m : ℕ)) *
          Bw ^ ((p : ℕ) * (MepsP : ℕ))) ^ ((1 : ℝ) / (nm : ℕ)) =
      (((p : ℝ)) ^ (m : ℕ)) ^ ((1 : ℝ) / (nm : ℕ)) *
        (asymp ^ ((n : ℕ) * (m : ℕ))) ^ ((1 : ℝ) / (nm : ℕ)) *
        (Bw ^ ((p : ℕ) * (MepsP : ℕ))) ^ ((1 : ℝ) / (nm : ℕ)) := by
    rw [Real.mul_rpow (by positivity) hh_nn, Real.mul_rpow hf_nn hg_nn]
  rw [h_rpow_mul1]
  -- nm = n * m as ℕ (via PNat.mul_coe).
  have h_nm_eq_nat : (nm : ℕ) = (n : ℕ) * (m : ℕ) := by
    simp [hnm_def]
  have h_nm_eq_R : ((nm : ℕ) : ℝ) = ((n : ℕ) : ℝ) * ((m : ℕ) : ℝ) := by
    rw [h_nm_eq_nat]; push_cast; ring
  have hn_R_pos : (0 : ℝ) < (n : ℕ) := by exact_mod_cast n.pos
  have hm_R_pos : (0 : ℝ) < (m : ℕ) := by exact_mod_cast m.pos
  have hnne : ((n : ℕ) : ℝ) ≠ 0 := hn_R_pos.ne'
  have hmne : ((m : ℕ) : ℝ) ≠ 0 := hm_R_pos.ne'
  -- Simplify each factor.
  -- (p^m)^(1/(nm)) = p^(m/(nm)) = p^(1/n).
  have hf_simp :
      (((p : ℝ)) ^ (m : ℕ)) ^ ((1 : ℝ) / (nm : ℕ)) = ((p : ℝ)) ^ ((1 : ℝ) / (n : ℕ)) := by
    rw [← Real.rpow_natCast ((p : ℝ)) (m : ℕ), ← Real.rpow_mul hP_R_nn]
    congr 1
    -- m / (n*m) = 1/n
    rw [h_nm_eq_R]
    field_simp
  rw [hf_simp]
  -- (asymp^(n·m))^(1/(nm)) = asymp.
  have hg_simp : (asymp ^ ((n : ℕ) * (m : ℕ))) ^ ((1 : ℝ) / (nm : ℕ)) = asymp := by
    rw [← Real.rpow_natCast asymp ((n : ℕ) * (m : ℕ)), ← Real.rpow_mul hasymp_nn]
    have heq : ((((n : ℕ) * (m : ℕ) : ℕ) : ℝ)) * ((1 : ℝ) / (nm : ℕ)) = 1 := by
      rw [h_nm_eq_R]
      push_cast
      field_simp
    rw [heq, Real.rpow_one]
  rw [hg_simp]
  -- (Bw^(p·M))^(1/(nm)) = Bw^(p·M/(nm)).
  have hh_simp : (Bw ^ ((p : ℕ) * (MepsP : ℕ))) ^ ((1 : ℝ) / (nm : ℕ)) =
      Bw ^ (((p : ℕ) * (MepsP : ℕ) : ℝ) / (nm : ℕ)) := by
    rw [← Real.rpow_natCast Bw ((p : ℕ) * (MepsP : ℕ)), ← Real.rpow_mul hBw_pos.le]
    congr 1
    push_cast
    ring
  rw [hh_simp]
  -- Now goal: p^(1/n) · asymp · B^((p·M)/(nm)) ≤ pn^(1/n) · asymp · B^((pn·Meps)/(nm)).
  -- Both sides have the asymp factor (≥ 0). Split into two ≤'s.
  have h_inv_n_nn : (0 : ℝ) ≤ (1 : ℝ) / (n : ℕ) := by
    have : (0 : ℝ) ≤ (n : ℕ) := by exact_mod_cast Nat.zero_le _
    positivity
  -- (a) p^(1/n) ≤ pn^(1/n).
  have hp_root : ((p : ℝ)) ^ ((1 : ℝ) / (n : ℕ)) ≤ pn ^ ((1 : ℝ) / (n : ℕ)) :=
    Real.rpow_le_rpow hP_R_nn hp_le_pn h_inv_n_nn
  -- (b) (p · M) / (nm) ≤ (pn · Meps) / (nm). Since B ≥ 1 and denominator > 0,
  -- this gives B^((p·M)/(nm)) ≤ B^((pn·Meps)/(nm)).
  have hexp_le : ((((p : ℕ) * (MepsP : ℕ)) : ℝ)) / ((nm : ℕ)) ≤
      (pn * (Meps : ℝ)) / (((n : ℕ) * (m : ℕ)) : ℝ) := by
    -- p · M ≤ pn · Meps (with Meps := (MepsP : ℕ)), and nm = n * m as reals.
    have h_PM_le : (((p : ℕ) * (MepsP : ℕ)) : ℝ) ≤ pn * (Meps : ℝ) := by
      have h1 : (((p : ℕ) : ℝ) * ((MepsP : ℕ) : ℝ)) ≤ pn * ((Meps : ℕ) : ℝ) := by
        apply mul_le_mul hp_le_pn (le_refl _) (Nat.cast_nonneg _) hpn_nn
      simpa [hMeps_def] using! h1
    have hnm_R_pos' : (0 : ℝ) < ((nm : ℕ) : ℝ) := by exact_mod_cast nm.pos
    have h_nm_eq_R' : ((nm : ℕ) : ℝ) = ((n : ℕ) : ℝ) * ((m : ℕ) : ℝ) := h_nm_eq_R
    rw [← h_nm_eq_R']
    have hnm_R_nn : (0 : ℝ) ≤ ((nm : ℕ) : ℝ) := hnm_R_pos'.le
    exact div_le_div_of_nonneg_right h_PM_le hnm_R_nn
  have hB_pow_le : Bw ^ ((((p : ℕ) * (MepsP : ℕ)) : ℝ) / ((nm : ℕ))) ≤
      Bw ^ ((pn * (Meps : ℝ)) / (((n : ℕ) * (m : ℕ)) : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hBw_ge_one hexp_le
  -- Combine.
  calc ((p : ℝ)) ^ ((1 : ℝ) / (n : ℕ)) * asymp *
        Bw ^ ((((p : ℕ) * (MepsP : ℕ)) : ℝ) / ((nm : ℕ)))
      ≤ pn ^ ((1 : ℝ) / (n : ℕ)) * asymp *
        Bw ^ ((((p : ℕ) * (MepsP : ℕ)) : ℝ) / ((nm : ℕ))) := by
        apply mul_le_mul_of_nonneg_right
        · exact mul_le_mul_of_nonneg_right hp_root hasymp_nn
        · positivity
    _ ≤ pn ^ ((1 : ℝ) / (n : ℕ)) * asymp *
        Bw ^ ((pn * (Meps : ℝ)) / (((n : ℕ) * (m : ℕ)) : ℝ)) := by
        apply mul_le_mul_of_nonneg_left hB_pow_le
        have hpn_root_nn : 0 ≤ pn ^ ((1 : ℝ) / (n : ℕ)) :=
          Real.rpow_nonneg hpn_nn _
        positivity

/-- **Inner bound** (Theorem 2.2). After sending `m → ∞`
in `tensorPow_nm_inner_bound`, the `B^(p·M/(nm))` factor tends to `B^0 = 1`,
giving `F̃(T) ≤ p_n^(1/n) · (F̃[A] + ε)`. -/
lemma regularize_le_poly_times_eps
    (Func : AdmissibleFunctional F V) (A : Set V) (T : V)
    (hT : T ∈ zariskiClosure (F := F) A) (hT0 : T ≠ 0) (hA_nonempty : A.Nonempty)
    (hd_pos : 0 < Module.finrank F V)
    (n : ℕ+) (ε : ℝ) (hε : 0 < ε) :
    Func.regularize T ≤
      (Nat.choose (Module.finrank F V + (n : ℕ) - 1) (n : ℕ) : ℝ) ^ ((1 : ℝ) / (n : ℕ)) *
        (Func.asympOnSet A + ε) := by
  -- The `m → ∞` limit-passing step on `tensorPow_nm_inner_bound`.
  -- For every `m : ℕ+`, we have F̃(T) ≤ F(T^⊗(nm))^(1/(nm)) ≤ L · B^(pn·M/(nm)),
  -- where L = pn^(1/n) · (F̃[A]+ε). As m → ∞, B^(pn·M/(nm)) → B^0 = 1, so F̃(T) ≤ L.
  set pn : ℝ := (Nat.choose (Module.finrank F V + (n : ℕ) - 1) (n : ℕ) : ℝ) with hpn_def
  set L : ℝ := pn ^ ((1 : ℝ) / (n : ℕ)) * (Func.asympOnSet A + ε) with hL_def
  -- Extract the (B, M) pair from `tensorPow_nm_inner_bound`.
  obtain ⟨B, Meps, hB_one, hBound⟩ := tensorPow_nm_inner_bound Func A T hT hT0 hd_pos n ε hε
  -- F̃(T) ≤ F(T^⊗(nm))^(1/(nm)) for every m (by ciInf_le on the regularize def).
  have h_reg_le : ∀ m : ℕ+, Func.regularize T ≤
      ((Func.toFun (n * m) (tensorPow (n * m) T) : ℝ)) ^ ((1 : ℝ) / ((n * m : ℕ+) : ℕ)) := by
    intro m
    unfold AdmissibleFunctional.regularize
    have h_bdd : BddBelow (Set.range fun k : ℕ+ =>
        ((Func.toFun k (tensorPow (F := F) (V := V) k T)) : ℝ) ^ ((1 : ℝ) / (k : ℕ))) := by
      refine ⟨0, ?_⟩
      rintro x ⟨k, rfl⟩
      exact Real.rpow_nonneg (NNReal.coe_nonneg _) _
    exact ciInf_le h_bdd (n * m)
  -- Chain: F̃(T) ≤ F(T^⊗(nm))^(1/(nm)) ≤ L · B^(pn·M/(nm)).
  have h_chain : ∀ m : ℕ+, Func.regularize T ≤
      L * B ^ ((pn * (Meps : ℝ)) / ((n : ℕ) * (m : ℕ) : ℝ)) := by
    intro m
    calc Func.regularize T
        ≤ ((Func.toFun (n * m) (tensorPow (n * m) T) : ℝ)) ^
            ((1 : ℝ) / ((n * m : ℕ+) : ℕ)) := h_reg_le m
      _ ≤ L * B ^ ((pn * (Meps : ℝ)) / ((n : ℕ) * (m : ℕ) : ℝ)) := by
          have := hBound m
          simp only [PNat.mul_coe] at this ⊢
          convert! this using 2
  -- Now take m → ∞. The sequence v(m) := L · B^(pn·M / (n*m)) tends to L · B^0 = L.
  -- Exponent (pn·M) / (n·m) → 0 as m → ∞.
  have hExpZero : Filter.Tendsto (fun m : ℕ => (pn * (Meps : ℝ)) / ((n : ℕ) * (m : ℕ) : ℝ))
      Filter.atTop (nhds 0) := by
    -- = (pn · M / n) · (1/m), which tends to 0.
    have hNumer : (n : ℝ) > 0 := by exact_mod_cast n.pos
    have hRecip : Filter.Tendsto (fun m : ℕ => ((m : ℝ))⁻¹) Filter.atTop (nhds 0) :=
      tendsto_inv_atTop_nhds_zero_nat
    have : Filter.Tendsto (fun m : ℕ => ((pn * Meps) / (n : ℝ)) * ((m : ℝ))⁻¹)
        Filter.atTop (nhds 0) := by
      have := (tendsto_const_nhds (x := (pn * (Meps : ℝ)) / (n : ℝ))).mul hRecip
      simp at this
      exact this
    refine this.congr' ?_
    filter_upwards [Filter.eventually_gt_atTop 0] with m hm
    have hmne : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
    have hnne : (n : ℝ) ≠ 0 := by exact_mod_cast (n.pos).ne'
    field_simp
  -- B^((pn·M)/(n·m)) → B^0 = 1.
  have hBpos : 0 < B := lt_of_lt_of_le zero_lt_one hB_one
  have hBseqLim : Filter.Tendsto
      (fun m : ℕ => B ^ ((pn * (Meps : ℝ)) / ((n : ℕ) * (m : ℕ) : ℝ)))
      Filter.atTop (nhds 1) := by
    have hBne : B ≠ 0 := hBpos.ne'
    have := (Real.continuousAt_const_rpow hBne (b := 0)).tendsto.comp hExpZero
    simpa [Real.rpow_zero] using! this
  -- v(m) := L · B^(...) → L.
  have hvLim : Filter.Tendsto
      (fun m : ℕ => L * B ^ ((pn * (Meps : ℝ)) / ((n : ℕ) * (m : ℕ) : ℝ)))
      Filter.atTop (nhds (L * 1)) := hBseqLim.const_mul L
  rw [mul_one] at hvLim
  -- F̃(T) ≤ v(m) for every m ≥ 1.
  have hForBdd : ∀ᶠ m : ℕ in Filter.atTop,
      Func.regularize T ≤ L * B ^ ((pn * (Meps : ℝ)) / ((n : ℕ) * (m : ℕ) : ℝ)) := by
    filter_upwards [Filter.eventually_ge_atTop 1] with m hm
    have hmpos : 0 < m := hm
    exact h_chain ⟨m, hmpos⟩
  exact ge_of_tendsto hvLim hForBdd

/-- After sending `n → ∞` in `regularize_le_poly_times_eps`, the polynomial
factor `p(n)^(1/n) → 1` and we get `F̃(T) ≤ F̃[A] + ε`. -/
lemma regularize_le_asymp_plus_eps
    (Func : AdmissibleFunctional F V) (A : Set V) (T : V)
    (hT : T ∈ zariskiClosure (F := F) A) (hT0 : T ≠ 0) (hA_nonempty : A.Nonempty)
    (ε : ℝ) (hε : 0 < ε) :
    Func.regularize T ≤ Func.asympOnSet A + ε := by
  -- Set d := dim V. We have F̃(T) ≤ p_n^(1/n) · (F̃[A] + ε) for every n : ℕ+,
  -- where p_n = C(d + n - 1, n). By `binomial_pow_root_tendsto_one_pos`,
  -- p_n^(1/n) → 1, so the rhs tends to F̃[A] + ε.
  -- We use the form: for sequences a_n → 1, if F̃(T) ≤ a_n · (F̃[A] + ε) for all n,
  -- then F̃(T) ≤ F̃[A] + ε.
  set d := Module.finrank F V with hd_def
  -- d ≥ 1 because V is nonempty (it has at least the zero vector); but actually
  -- we need d ≥ 1 to use `binomial_pow_root_tendsto_one_pos`. For d = 0,
  -- V is trivial (only the zero vector), and the regularization is trivially 0.
  by_cases hd_pos : 0 < d
  · -- The sequence (p_n^(1/n) : ℕ → ℝ) tends to 1.
    have hSeq : Filter.Tendsto
        (fun n : ℕ => (Nat.choose (d + n - 1) n : ℝ) ^ ((1 : ℝ) / n))
        Filter.atTop (nhds 1) := binomial_pow_root_tendsto_one_pos hd_pos
    -- Multiplied by (F̃[A] + ε):
    have hRhsLim : Filter.Tendsto
        (fun n : ℕ => (Nat.choose (d + n - 1) n : ℝ) ^ ((1 : ℝ) / n) *
          (Func.asympOnSet A + ε)) Filter.atTop (nhds (1 * (Func.asympOnSet A + ε))) :=
      hSeq.mul_const _
    rw [one_mul] at hRhsLim
    -- F̃(T) is bounded above by every term in this sequence (for n ≥ 1).
    have hBound : ∀ᶠ n : ℕ in Filter.atTop,
        Func.regularize T ≤
          (Nat.choose (d + n - 1) n : ℝ) ^ ((1 : ℝ) / n) *
            (Func.asympOnSet A + ε) := by
      filter_upwards [Filter.eventually_ge_atTop 1] with n hn
      -- Build n : ℕ+ from n ≥ 1.
      set n' : ℕ+ := ⟨n, hn⟩ with hn'_def
      have hcast : (n' : ℕ) = n := rfl
      have := regularize_le_poly_times_eps Func A T hT hT0 hA_nonempty hd_pos n' ε hε
      simpa [hd_def, hcast] using! this
    -- Conclude by `ge_of_tendsto`: if `f n → L` and `b ≤ f n` eventually, then `b ≤ L`.
    exact ge_of_tendsto hRhsLim hBound
  · -- d = 0 case: V is a subsingleton, so T = S for any S ∈ A.
    push_neg at hd_pos
    have hd_zero : Module.finrank F V = 0 := Nat.le_zero.mp hd_pos
    have hV_subsingleton : Subsingleton V :=
      Module.finrank_zero_iff.mp hd_zero
    obtain ⟨S, hSA⟩ := hA_nonempty
    have hTS : T = S := Subsingleton.elim T S
    rw [hTS]
    have hS_le : Func.regularize S ≤ Func.asympOnSet A := by
      classical
      rw [show Func.regularize S = (⨆ _ : S ∈ A, Func.regularize S) from by
        rw [iSup_mem_eq, if_pos hSA]]
      unfold AdmissibleFunctional.asympOnSet
      exact le_ciSup (asympOnSet_bddAbove Func A) S
    linarith

/-- **Helper (`F̃(0) ≤ F̃(T)`)**: the regularization at `0` is at most the
    regularization at any `T`.

    Subadditivity (Def 2.1 (i), Definition 2.1) pins down `F_n(0)` relative to other
    values, even though `F_n(0) = 0` is NOT among the paper's axioms (Def 2.1
    lists only 5 properties; scalar invariance (iv), Definition 2.1, excludes `α = 0`):
    for every `n`,
      `F_n(0) = F_n(T^⊗n + (-1)•T^⊗n) ≤ F_n(T^⊗n) + F_n((-1)•T^⊗n) = 2·F_n(T^⊗n)`
    using subadditivity then scalar invariance with `α = -1 ≠ 0`. Taking
    `(1/n)`-th roots, `(F_n(0))^(1/n) ≤ 2^(1/n)·(F_n(T^⊗n))^(1/n)`, and since
    `2^(1/n) → 1` while `(F_n(T^⊗n))^(1/n) → F̃(T)`, we get `F̃(0) ≤ F̃(T)`.

    This is how the paper handles `T = 0` in Theorem 2.2: the
    `T = 0` case of `F̃[Z̄(A)] ≤ F̃[A]` follows from `F̃(0) ≤ F̃(S)` for any
    witness `S ∈ A`; `F_n(0) = 0` is never invoked. -/
lemma regularize_zero_le (Func : AdmissibleFunctional F V) (T : V) :
    Func.regularize (0 : V) ≤ Func.regularize T := by
  classical
  -- Abbreviation for the rooted value at index `n : ℕ+`.
  set vT : ℕ+ → ℝ := fun n =>
    ((Func.toFun n (tensorPow (F := F) (V := V) n T)) : ℝ) ^ ((1 : ℝ) / (n : ℕ))
    with hvT_def
  -- Step 1: `tensorPow n 0 = 0` (a multilinear map with a zero coordinate).
  have htp_zero : ∀ n : ℕ+, tensorPow (F := F) (V := V) n (0 : V) = 0 := by
    intro n
    unfold tensorPow
    exact MultilinearMap.map_coord_zero (PiTensorProduct.tprod F) ⟨0, n.pos⟩ rfl
  -- Step 2: `F_n(0) ≤ 2 · F_n(T^⊗n)` via subadd + scalar_inv (α = -1).
  have hF0_le : ∀ n : ℕ+,
      ((Func.toFun n (tensorPow (F := F) (V := V) n (0 : V))) : ℝ) ≤
        2 * ((Func.toFun n (tensorPow (F := F) (V := V) n T)) : ℝ) := by
    intro n
    -- `0 = T^⊗n + (-1)•T^⊗n`.
    have hzero_eq : (0 : TensorPower F (n : ℕ) V) =
        tensorPow (F := F) (V := V) n T + (-1 : F) • tensorPow (F := F) (V := V) n T := by
      rw [neg_one_smul, add_neg_cancel]
    have hsub := Func.subadd n (tensorPow (F := F) (V := V) n T)
      ((-1 : F) • tensorPow (F := F) (V := V) n T)
    rw [Func.scalar_inv n (-1 : F) (by norm_num) (tensorPow (F := F) (V := V) n T)] at hsub
    -- `F_n(0) = F_n(T^⊗n + (-1)•T^⊗n) ≤ F_n(T^⊗n) + F_n(T^⊗n) = 2 F_n(T^⊗n)`.
    rw [htp_zero n, hzero_eq]
    have hsubR := NNReal.coe_le_coe.mpr hsub
    rw [NNReal.coe_add] at hsubR
    linarith
  -- Step 3: `regularize 0 ≤ 2^(1/n) · vT n` for every `n`.
  -- First: `regularize 0 ≤ (F_n(0))^(1/n)` (iInf lower bound).
  have hreg0_le : ∀ n : ℕ+,
      Func.regularize (0 : V) ≤
        ((Func.toFun n (tensorPow (F := F) (V := V) n (0 : V))) : ℝ) ^ ((1 : ℝ) / (n : ℕ)) := by
    intro n
    unfold AdmissibleFunctional.regularize
    have h_bdd : BddBelow (Set.range fun k : ℕ+ =>
        ((Func.toFun k (tensorPow (F := F) (V := V) k (0 : V))) : ℝ) ^ ((1 : ℝ) / (k : ℕ))) := by
      refine ⟨0, ?_⟩
      rintro x ⟨k, rfl⟩
      exact Real.rpow_nonneg (NNReal.coe_nonneg _) _
    exact ciInf_le h_bdd n
  -- `(F_n(0))^(1/n) ≤ 2^(1/n) · vT n`.
  have hroot_le : ∀ n : ℕ+,
      Func.regularize (0 : V) ≤ (2 : ℝ) ^ ((1 : ℝ) / (n : ℕ)) * vT n := by
    intro n
    refine (hreg0_le n).trans ?_
    have hF0_nn : (0 : ℝ) ≤ ((Func.toFun n (tensorPow (F := F) (V := V) n (0 : V))) : ℝ) :=
      NNReal.coe_nonneg _
    have hinv_nn : (0 : ℝ) ≤ (1 : ℝ) / (n : ℕ) := by positivity
    have hstep : ((Func.toFun n (tensorPow (F := F) (V := V) n (0 : V))) : ℝ) ^ ((1 : ℝ) / (n : ℕ)) ≤
        (2 * ((Func.toFun n (tensorPow (F := F) (V := V) n T)) : ℝ)) ^ ((1 : ℝ) / (n : ℕ)) :=
      Real.rpow_le_rpow hF0_nn (hF0_le n) hinv_nn
    refine hstep.trans ?_
    rw [Real.mul_rpow (by norm_num) (NNReal.coe_nonneg _)]
  -- Step 4: `vT n → regularize T` (approximation + iInf lower bound), along `ℕ+`,
  -- but we pass to `ℕ` for the limit machinery.
  -- Lower bound: regularize T ≤ vT n for all n.
  have hreg_le_vT : ∀ n : ℕ+, Func.regularize T ≤ vT n := by
    intro n
    rw [hvT_def]
    unfold AdmissibleFunctional.regularize
    have h_bdd : BddBelow (Set.range fun k : ℕ+ =>
        ((Func.toFun k (tensorPow (F := F) (V := V) k T)) : ℝ) ^ ((1 : ℝ) / (k : ℕ))) := by
      refine ⟨0, ?_⟩
      rintro x ⟨k, rfl⟩
      exact Real.rpow_nonneg (NNReal.coe_nonneg _) _
    exact ciInf_le h_bdd n
  -- Define the ℕ-indexed sequence `w n := 2^(1/n) · vT n` (for n ≥ 1).
  -- We show `regularize 0 ≤ regularize T` by `ge_of_tendsto`: `w → regularize T`.
  -- 2^(1/n) → 1 as n → ∞.
  have h2lim : Filter.Tendsto (fun n : ℕ => (2 : ℝ) ^ ((1 : ℝ) / (n : ℕ)))
      Filter.atTop (nhds 1) := by
    have hExpZero : Filter.Tendsto (fun n : ℕ => (1 : ℝ) / (n : ℕ))
        Filter.atTop (nhds 0) := by
      have hinv : Filter.Tendsto (fun n : ℕ => ((n : ℝ))⁻¹) Filter.atTop (nhds 0) :=
        tendsto_inv_atTop_nhds_zero_nat
      refine hinv.congr ?_
      intro n; rw [one_div]
    have := (Real.continuousAt_const_rpow (by norm_num : (2 : ℝ) ≠ 0) (b := 0)).tendsto.comp hExpZero
    simpa [Real.rpow_zero] using! this
  -- vT (ℕ+ version) → regularize T as ℕ-sequence.
  have hvTlim : Filter.Tendsto
      (fun n : ℕ => if hn : 0 < n then vT ⟨n, hn⟩ else Func.regularize T)
      Filter.atTop (nhds (Func.regularize T)) := by
    rw [Metric.tendsto_atTop]
    intro δ hδ
    -- Use the `δ/2` approximation to get a STRICT bound `vT n' < regularize T + δ`.
    obtain ⟨M, hM⟩ := regularize_approximation_uniform Func T (δ / 2) (by linarith)
    refine ⟨(M : ℕ), fun n hn => ?_⟩
    have hnpos : 0 < n := lt_of_lt_of_le M.pos hn
    rw [dif_pos hnpos]
    set n' : ℕ+ := ⟨n, hnpos⟩ with hn'_def
    have hMn' : M ≤ n' := by
      rw [hn'_def]; exact hn
    have hupper : vT n' ≤ Func.regularize T + δ / 2 := hM n' hMn'
    have hlower : Func.regularize T ≤ vT n' := hreg_le_vT n'
    rw [Real.dist_eq, abs_sub_lt_iff]
    constructor <;> linarith
  -- w n := 2^(1/n) · (vT-as-ℕ) → 1 · regularize T = regularize T.
  have hwlim : Filter.Tendsto
      (fun n : ℕ => (2 : ℝ) ^ ((1 : ℝ) / (n : ℕ)) *
        (if hn : 0 < n then vT ⟨n, hn⟩ else Func.regularize T))
      Filter.atTop (nhds ((1 : ℝ) * Func.regularize T)) := h2lim.mul hvTlim
  rw [one_mul] at hwlim
  -- regularize 0 ≤ w n eventually (for n ≥ 1).
  have hbound : ∀ᶠ n : ℕ in Filter.atTop,
      Func.regularize (0 : V) ≤ (2 : ℝ) ^ ((1 : ℝ) / (n : ℕ)) *
        (if hn : 0 < n then vT ⟨n, hn⟩ else Func.regularize T) := by
    filter_upwards [Filter.eventually_gt_atTop 0] with n hn
    rw [dif_pos hn]
    exact hroot_le ⟨n, hn⟩
  exact ge_of_tendsto hwlim hbound

/-! ## Theorem 2.2. -/

/--
**Theorem 2.2**.

For any admissible functional `Func` on `V` and any subset `A ⊆ V`,
`F̃[Z̄(A)] = F̃[A]`.

Proof outline (Theorem 2.2):
* (`A ⊆ Z̄(A)`-direction) Trivial via `asympOnSet_mono`.
* (`F̃[Z̄(A)] ≤ F̃[A]`-direction) Fix `T ∈ Z̄(A)`. For each `n ∈ ℕ+`, Lemma 2.3
  gives `T^⊗n = Σᵢ₌₁^{p(n)} αᵢ Sᵢ^⊗n` with `Sᵢ ∈ A` and `p(n) ≤ dim Sym^n V`
  growing polynomially in `n`. For any `m`, expand
  `T^⊗(nm) = Σ_{(i₁,…,iₘ)} ⊗ⱼ αᵢⱼ Sᵢⱼ^⊗n`. Using (i) subadditivity, (iv) scalar
  invariance, (iii) permutation invariance to rearrange `⊗ⱼ Sᵢⱼ^⊗n` as
  `⊗ᵢ Sᵢ^⊗(mᵢ n)` where `mᵢ` counts how often `i` appears in `(i₁,…,iₘ)`, then
  (ii) iterated submultiplicativity gives
  `F(⊗ᵢ Sᵢ^⊗(mᵢn)) ≤ ∏ᵢ F(Sᵢ^⊗(mᵢn))`. Bound each factor by
  `(F̃(Sᵢ) + ε)^(mᵢn)` (when `mᵢn ≥ M(ε,n)`) or by `B^(mᵢn)` (small `mᵢn`, via
  `F₁ ≤ B`). Taking `n`-th roots and letting `m → ∞`, `ε → 0`, `n → ∞`, we
  recover `F̃(T) ≤ F̃[A]`.
-/
theorem regularize_zariski_closure_eq
    (Func : AdmissibleFunctional F V) (A : Set V) :
    Func.asympOnSet (zariskiClosure (F := F) A) = Func.asympOnSet A := by
  refine le_antisymm ?_ (asympOnSet_mono Func (subset_zariskiClosure A))
  classical
  unfold AdmissibleFunctional.asympOnSet
  refine ciSup_le fun T => ?_
  rw [iSup_mem_eq]
  split_ifs with hT
  case neg =>
    -- T ∉ Z̄(A). Inner ⨆ = 0. Need 0 ≤ Func.asympOnSet A.
    -- Either A is empty (then both sides are 0) or A has a witness with F̃ ≥ 0.
    by_cases hA_ne : A.Nonempty
    · obtain ⟨S, hSA⟩ := hA_ne
      have h_S_le : Func.regularize S ≤ Func.asympOnSet A := by
        rw [show Func.regularize S = (⨆ _ : S ∈ A, Func.regularize S) from by
          rw [iSup_mem_eq, if_pos hSA]]
        unfold AdmissibleFunctional.asympOnSet
        exact le_ciSup (asympOnSet_bddAbove Func A) S
      exact (regularize_nonneg Func S).trans h_S_le
    · rw [Set.not_nonempty_iff_eq_empty] at hA_ne
      subst hA_ne
      -- Show 0 ≤ ⨆ T, ⨆ _ : T ∈ ∅, F̃ T. The inner sup is uniformly 0, then outer sup is 0.
      have hzero_inner : ∀ T : V, (⨆ _ : T ∈ (∅ : Set V), Func.regularize T) = 0 := fun T => by
        rw [iSup_mem_eq, if_neg (Set.notMem_empty T)]
      simp_rw [hzero_inner]
      rcases (inferInstance : Nonempty V) with ⟨v⟩
      haveI : Nonempty V := ⟨v⟩
      rw [ciSup_const]
  case pos =>
    -- T ∈ Z̄(A). Need F̃(T) ≤ Func.asympOnSet A.
    -- Case split on whether A is empty: if it is, then Z̄(∅) = ∅ (constant 1
    -- polynomial separates), contradicting hT.
    by_cases hA_ne : A.Nonempty
    · -- The main case. Split on `T = 0` (paper handles `T = 0` via the sup
      -- structure; `F_n(0) = 0` is never invoked).
      by_cases hT0 : T = 0
      · -- `T = 0`: `F̃(0) ≤ F̃(S) ≤ F̃[A]` for any witness `S ∈ A`.
        obtain ⟨S, hSA⟩ := hA_ne
        subst hT0
        have h_S_le : Func.regularize S ≤ Func.asympOnSet A := by
          rw [show Func.regularize S = (⨆ _ : S ∈ A, Func.regularize S) from by
            rw [iSup_mem_eq, if_pos hSA]]
          unfold AdmissibleFunctional.asympOnSet
          exact le_ciSup (asympOnSet_bddAbove Func A) S
        exact (regularize_zero_le Func S).trans h_S_le
      · -- `T ≠ 0`: by `regularize_le_asymp_plus_eps`, F̃(T) ≤ F̃[A] + ε for all
        -- ε > 0. Conclude F̃(T) ≤ F̃[A] by ε → 0.
        refine le_of_forall_pos_le_add fun ε hε => ?_
        exact regularize_le_asymp_plus_eps Func A T hT hT0 hA_ne ε hε
    · rw [Set.not_nonempty_iff_eq_empty] at hA_ne
      subst hA_ne
      -- T ∈ Z̄(∅). Constant 1 polynomial is in F[V] and vanishes vacuously on ∅,
      -- so it must vanish at T, giving 1 = 0 in F. Contradiction.
      have h_one : (1 : F) = 0 :=
        hT (fun _ => (1 : F)) ⟨MvPolynomial.C 1, fun _ => by simp⟩
          (fun _ h => (h : _ ∈ (∅ : Set V)).elim)
      exact absurd h_one one_ne_zero

/-! ## Corollary 2.4. -/

/-- **Corollary 2.4**.

For any admissible functional `Func` and any `r ∈ ℝ`,
`{T ∈ V : F̃(T) ≤ r}` is Zariski-closed.

Proof (Corollary 2.4): set `A = {T | F̃(T) ≤ r}`. Then `F̃[A] ≤ r` by the
supremum bound. Apply Theorem 2.2 to get `F̃[Z̄(A)] = F̃[A] ≤ r`. So every
`T ∈ Z̄(A)` has `F̃(T) ≤ r`, giving `Z̄(A) ⊆ A`. The reverse inclusion is
the general `A ⊆ Z̄(A)`. -/
theorem sublevel_zariski_closed
    (Func : AdmissibleFunctional F V) (r : ℝ) :
    zariskiClosure (F := F) { T : V | Func.regularize T ≤ r } =
      { T : V | Func.regularize T ≤ r } := by
  classical
  set A : Set V := { T : V | Func.regularize T ≤ r } with hA_def
  refine Set.eq_of_subset_of_subset ?_ (subset_zariskiClosure A)
  -- Z̄(A) ⊆ A: every T ∈ Z̄(A) has F̃(T) ≤ r.
  intro T hT
  show Func.regularize T ≤ r
  have h_in_closure : T ∈ zariskiClosure (F := F) A := hT
  -- A ≠ ∅ since `Z̄(A) ⊇ A` and we have `T ∈ Z̄(A)` (so `Z̄(A) ≠ ∅`), and
  -- `Z̄(∅) = ∅` (since the constant function `1` is polynomial). So `A ≠ ∅`,
  -- which gives us some witness `T_A ∈ A` with `F̃(T_A) ≤ r`, so `r ≥ 0`.
  -- This justifies the `0 ≤ r` case in `h_sup_A_le` below.
  have hA_nonempty : A.Nonempty := by
    by_contra hempty
    rw [Set.not_nonempty_iff_eq_empty] at hempty
    -- T ∈ Z̄(∅): every polynomial function vanishes at T. But constant `1` is
    -- polynomial, so 1 = 0 in F, contradiction.
    have h_one : (1 : F) = 0 :=
      (hempty ▸ h_in_closure)
        (fun _ => (1 : F))
        ⟨MvPolynomial.C 1, fun _ => by simp⟩
        (fun _ h => (h : _ ∈ (∅ : Set V)).elim)
    exact one_ne_zero h_one
  obtain ⟨T_A, hT_A⟩ := hA_nonempty
  have hr_nonneg : 0 ≤ r := (regularize_nonneg Func T_A).trans hT_A
  have h_sup_A_le : Func.asympOnSet A ≤ r := by
    refine ciSup_le fun T' => ?_
    rw [iSup_mem_eq]
    split_ifs with hT'
    · exact hT'
    · exact hr_nonneg
  have h_sup_closure_le : Func.asympOnSet (zariskiClosure (F := F) A) ≤ r := by
    rw [regularize_zariski_closure_eq]; exact h_sup_A_le
  -- F̃(T) = `⨆ _ : T ∈ Z̄(A), F̃ T` ≤ `⨆ T', ⨆ _ : T' ∈ Z̄(A), F̃ T'` = asympOnSet
  have h_le_sup : Func.regularize T ≤ Func.asympOnSet (zariskiClosure (F := F) A) := by
    have : Func.regularize T = (⨆ _ : T ∈ zariskiClosure (F := F) A, Func.regularize T) := by
      rw [iSup_mem_eq, if_pos h_in_closure]
    rw [this]
    unfold AdmissibleFunctional.asympOnSet
    exact le_ciSup (asympOnSet_bddAbove Func (zariskiClosure (F := F) A)) T
  exact h_le_sup.trans h_sup_closure_le

/-! ## Vanishing ideal — bridge between Zariski-closed subsets of `V` and ideals
of `MvPolynomial (Fin (finrank F V)) F`.

For descending chains of Zariski-closed sets to stabilize we use Noetherianity of
`F[X_1, …, X_d]` via the order-reversing map `A ↦ I(A)` and its right-inverse on
Zariski-closed sets. -/

/-- The **vanishing ideal** of `A ⊆ V`: polynomials in
`MvPolynomial (Fin (Module.finrank F V)) F` whose evaluation at the coordinates
`(b.repr T)` for `b := Module.finBasis F V` vanishes at every `T ∈ A`. -/
def vanishingIdeal (A : Set V) :
    Ideal (MvPolynomial (Fin (Module.finrank F V)) F) where
  carrier := { p | ∀ T ∈ A, MvPolynomial.eval
    (fun i => (Module.finBasis F V).repr T i) p = 0 }
  add_mem' {p q} hp hq := fun T hT => by
    simp [map_add, hp T hT, hq T hT]
  zero_mem' := fun T _ => by simp
  smul_mem' c {p} hp := fun T hT => by
    simp [hp T hT]

/-- Membership in `vanishingIdeal A`. -/
lemma mem_vanishingIdeal {A : Set V}
    {p : MvPolynomial (Fin (Module.finrank F V)) F} :
    p ∈ vanishingIdeal (F := F) (V := V) A ↔
      ∀ T ∈ A, MvPolynomial.eval
        (fun i => (Module.finBasis F V).repr T i) p = 0 := Iff.rfl

/-- `vanishingIdeal` is antitone: bigger sets have smaller vanishing ideals. -/
lemma vanishingIdeal_antitone {A B : Set V} (h : A ⊆ B) :
    vanishingIdeal (F := F) (V := V) B ≤
      vanishingIdeal (F := F) (V := V) A := by
  intro p hp T hT
  exact hp T (h hT)

/-- A polynomial function `f T = eval (b.repr T) p` vanishes on `A` iff `p ∈ vanishingIdeal A`. -/
lemma polynomial_function_vanishes_iff_mem_vanishingIdeal (A : Set V)
    (p : MvPolynomial (Fin (Module.finrank F V)) F) :
    (∀ T ∈ A, MvPolynomial.eval
        (fun i => (Module.finBasis F V).repr T i) p = 0) ↔
      p ∈ vanishingIdeal (F := F) (V := V) A := Iff.rfl

/-- A point of the Zariski closure of `A` is killed by every polynomial in the
vanishing ideal of `A`. -/
lemma eval_vanishingIdeal_of_mem_zariskiClosure {A : Set V} {T : V}
    (hT : T ∈ zariskiClosure (F := F) A)
    {p : MvPolynomial (Fin (Module.finrank F V)) F}
    (hp : p ∈ vanishingIdeal (F := F) (V := V) A) :
    MvPolynomial.eval (fun i => (Module.finBasis F V).repr T i) p = 0 := by
  -- Apply `T ∈ zariskiClosure A` to the polynomial function `f S = eval (b.repr S) p`.
  refine hT (fun S => MvPolynomial.eval
    (fun i => (Module.finBasis F V).repr S i) p) ⟨p, fun _ => rfl⟩ ?_
  intro S hSA
  exact hp S hSA

/-- A point `T ∈ V` lies in the Zariski closure of `A` iff every polynomial in
`vanishingIdeal A` evaluates to zero at `T`. -/
lemma mem_zariskiClosure_iff_eval_vanishingIdeal (A : Set V) (T : V) :
    T ∈ zariskiClosure (F := F) A ↔
      ∀ p ∈ vanishingIdeal (F := F) (V := V) A,
        MvPolynomial.eval (fun i => (Module.finBasis F V).repr T i) p = 0 := by
  constructor
  · intro hT p hp
    exact eval_vanishingIdeal_of_mem_zariskiClosure hT hp
  · intro hT f hf hfA
    obtain ⟨p, hp⟩ := hf
    rw [hp T]
    exact hT p (fun S hS => by rw [← hp S]; exact hfA S hS)

/-- **Key bridge**: For Zariski-closed sets `A`, `B`, with `A ⊆ B` and
`vanishingIdeal A = vanishingIdeal B`, we have `A = B`. -/
lemma eq_of_vanishingIdeal_eq {A B : Set V}
    (hA_closed : zariskiClosure (F := F) A = A)
    (hB_closed : zariskiClosure (F := F) B = B)
    (hAB : A ⊆ B)
    (hI : vanishingIdeal (F := F) (V := V) A =
          vanishingIdeal (F := F) (V := V) B) :
    A = B := by
  apply Set.eq_of_subset_of_subset hAB
  intro T hTB
  -- Goal: T ∈ A. We use that A is Zariski-closed and T satisfies every
  -- polynomial in vanishingIdeal A.
  rw [← hA_closed]
  rw [mem_zariskiClosure_iff_eval_vanishingIdeal]
  intro p hpA
  rw [hI] at hpA
  -- T ∈ B ⊆ zariskiClosure B, and p ∈ vanishingIdeal B.
  exact eval_vanishingIdeal_of_mem_zariskiClosure
    (hB_closed ▸ subset_zariskiClosure (F := F) B hTB) hpA

/-! ## Corollary 2.5. -/

/-- **Corollary 2.5**.

The set of values `{F̃(T) : T ∈ V}` is well-ordered.

Proof (Corollary 2.5): a non-increasing sequence `r₁ ≥ r₂ ≥ ⋯` in this set has
sublevel sets `A_{r_i} = {T : F̃(T) ≤ r_i}` forming a descending chain of
Zariski-closed sets (Corollary 2.4). Noetherianity of the Zariski topology on `V`
(`Hartshorne §1.4`) forces this chain to stabilize, hence so does `r_i`.

We reduce Noetherianity of the Zariski topology to Noetherianity of
`MvPolynomial (Fin (finrank F V)) F` (`MvPolynomial.isNoetherianRing_fin`) via
the order-reversing assignment `A ↦ vanishingIdeal A`. -/
theorem wellOrdered_values_per_format
    (Func : AdmissibleFunctional F V) :
    WellFoundedLT (Set.range Func.regularize) := by
  classical
  -- Reduce to: `<` on `Set.range Func.regularize` admits no infinite descending
  -- chain. We use `RelEmbedding.wellFounded_iff_isEmpty`.
  unfold WellFoundedLT  -- (v4.34: WellFoundedLT is now `WellFounded (· < ·)`, no IsWellFounded wrapper)
  rw [RelEmbedding.wellFounded_iff_isEmpty]
  refine ⟨fun e => ?_⟩
  -- `e : ((· > ·) : ℕ → ℕ → Prop) ↪r ((· < ·) : ↥(Set.range Func.regularize) → _ → _)`.
  -- That is: e : ℕ → Set.range Func.regularize with k < m → e m < e k (strictly
  -- decreasing on values).
  -- Extract the sequence of reals.
  set r : ℕ → ℝ := fun k => (e k : ℝ) with hr_def
  -- Strictly decreasing: r is StrictAnti.
  have hr_anti : StrictAnti r := by
    intro k m hkm
    -- e.toRelEmbedding sends `m > k` to `e m < e k` in subtype.
    have h := e.map_rel_iff.mpr (show m > k from hkm)
    -- h : (e k : Set.range Func.regularize) > e m, i.e., e m < e k.
    -- This is `<` on subtype, which is the restriction of `<` on ℝ.
    exact h
  -- Extract witnesses: for each k, there is T_k ∈ V with Func.regularize T_k = r k.
  have hr_mem : ∀ k, r k ∈ Set.range Func.regularize := fun k => (e k).2
  choose T hT using hr_mem
  -- Define the sublevel-set chain A_k = {S : Func.regularize S ≤ r k}.
  let A : ℕ → Set V := fun k => { S : V | Func.regularize S ≤ r k }
  -- Each A_k is Zariski-closed (Cor 2.4).
  have hA_closed : ∀ k, zariskiClosure (F := F) (A k) = A k := fun k =>
    sublevel_zariski_closed Func (r k)
  -- Descending chain: k ≤ m → A m ⊆ A k.
  have hA_anti : Antitone A := by
    intro k m hkm S hS
    -- hS : Func.regularize S ≤ r m. Since k ≤ m, r m ≤ r k.
    exact hS.trans (hr_anti.antitone hkm)
  -- Ascending chain of vanishing ideals.
  let I : ℕ → Ideal (MvPolynomial (Fin (Module.finrank F V)) F) :=
    fun k => vanishingIdeal (F := F) (V := V) (A k)
  have hI_mono : Monotone I := by
    intro k m hkm
    exact vanishingIdeal_antitone (hA_anti hkm)
  -- Stabilization via Noetherianity of MvPolynomial (Fin d) F.
  -- MvPolynomial.isNoetherianRing_fin gives IsNoetherianRing, hence
  -- WellFoundedGT (Ideal _) = WellFoundedGT (Submodule _ _).
  haveI : IsNoetherianRing (MvPolynomial (Fin (Module.finrank F V)) F) :=
    MvPolynomial.isNoetherianRing_fin
  -- IsNoetherianRing R = IsNoetherian R R, which gives WellFoundedGT (Submodule R R)
  -- = WellFoundedGT (Ideal R).
  obtain ⟨N, hN⟩ :=
    (monotone_stabilizes_iff_noetherian
      (R := MvPolynomial (Fin (Module.finrank F V)) F)
      (M := MvPolynomial (Fin (Module.finrank F V)) F)).mpr
      inferInstance ⟨I, hI_mono⟩
  -- hN : ∀ m, N ≤ m → I N = I m. Use m = N+1.
  have hI_eq : I N = I (N + 1) := hN (N + 1) (Nat.le_succ N)
  -- Translate to A N = A (N + 1) via eq_of_vanishingIdeal_eq.
  -- A (N+1) ⊆ A N (descending) and same vanishing ideal => A (N+1) = A N.
  have hA_eq_succ : A (N + 1) = A N :=
    eq_of_vanishingIdeal_eq
      (hA_closed (N + 1))
      (hA_closed N)
      (hA_anti (Nat.le_succ N))
      (by simp only [I] at hI_eq; exact hI_eq.symm)
  have hA_eq : A N = A (N + 1) := hA_eq_succ.symm
  -- Now derive the contradiction. T N ∈ V with Func.regularize (T N) = r N.
  -- T N ∈ A N (since r N ≤ r N).
  have hT_N_in_A_N : T N ∈ A N := by
    change Func.regularize (T N) ≤ r N
    rw [hT N]
  -- By hA_eq, T N ∈ A (N + 1), i.e., Func.regularize (T N) ≤ r (N + 1).
  have hT_N_le : Func.regularize (T N) ≤ r (N + 1) := by
    have : T N ∈ A (N + 1) := hA_eq ▸ hT_N_in_A_N
    exact this
  -- Combined: r N = Func.regularize (T N) ≤ r (N + 1), contradicting r (N + 1) < r N.
  have hN_lt : r (N + 1) < r N := hr_anti (Nat.lt_succ_self N)
  rw [hT N] at hT_N_le
  exact absurd hT_N_le (not_le.mpr hN_lt)

/-!
## Corollary 2.6. -/

/-!
### Structural helpers for `tensorRankAdmissible`

The two compatibilities below (`tensorRank_regroupingMap_add_le` and
`tensorRank_regroupingMap_block_perm`) are the structural content of paper
Section 2.1: `regroupingMap` (which sends `v_1 ⊗ ⋯ ⊗ v_n ↦ v_1 ⊠ ⋯ ⊠ v_n`) is
compatible with `⊗`-concatenation and with permutations of the factors.
-/

/-- **Format identification** `formatPow d (n+n') = fun i => formatPow d n i * formatPow d n' i`.
    Pointwise instance of the PNat law `pow_add : a^(n+n') = a^n * a^n'`.

    Used to transport the tensor-rank inequality across the format mismatch
    between `regroupingMap d (n+n')` and the iterated Kronecker product
    `regroupingMap d n T ⊠ regroupingMap d n' S`. Section 2.1 (regrouping
    is over `(d_i)^{n+n'}` legs, equivalent to splitting as `(d_i)^n × (d_i)^{n'}`). -/
lemma formatPow_add_eq_mul {k : ℕ} (d : Fin k → ℕ+) (n n' : ℕ+) :
    formatPow d ⟨(n : ℕ) + (n' : ℕ), Nat.add_pos_left n.pos _⟩
      = fun i => formatPow d n i * formatPow d n' i := by
  funext i
  simp only [formatPow]
  show d i ^ ((n : ℕ) + (n' : ℕ)) = d i ^ (n : ℕ) * d i ^ (n' : ℕ)
  exact pow_add _ _ _

/-- **Helper (Section 2.1)**: explicit pointwise formula for `regroupingMap d n`
    applied to an arbitrary `PiTensorProduct.tprod F u` (where `u : Fin n →
    KTensor F d`). Generalizes `regroupingMap_tensorPow_apply` (which is the
    constant-`u` special case).

    Section 2.1 says `regroupingMap` is the linear extension of
    `v_1 ⊗ ⋯ ⊗ v_n ↦ v_1 ⊠ ⋯ ⊠ v_n`, so on `tprod F u` it computes as
    `u(0) ⊠ ⋯ ⊠ u(n-1)`, whose `jdx`-entry is `∏ j, u(j)(sliceFun d n jdx j)`. -/
lemma regroupingMap_tprod_apply {k : ℕ} (d : Fin k → ℕ+) (n : ℕ+)
    (u : Fin (n : ℕ) → KTensor F d) (jdx : ∀ i : Fin k, Fin (formatPow d n i)) :
    regroupingMap d n (PiTensorProduct.tprod F u) jdx =
      ∏ j : Fin (n : ℕ), u j (sliceFun d n jdx j) := by
  unfold regroupingMap
  rw [PiTensorProduct.lift.tprod]
  rw [MultilinearMap.pi_apply]
  rw [MultilinearMap.compLinearMap_apply]
  rw [MultilinearMap.mkPiRing_apply]
  simp [kTensorEval]

/-- **Helper**: transport of a `KTensor` along a format equality reduces to
    transport of the index argument. `subst h; rfl`. -/
private lemma KTensor_cast_apply {k : ℕ} {d d' : Fin k → ℕ+} (h : d = d')
    (T : KTensor F d) (idx : ∀ i, Fin (d' i)) :
    (h ▸ T) idx = T (h.symm ▸ idx) := by
  subst h; rfl

/-- **Helper**: transport along format equality commutes with addition. -/
private lemma KTensor_cast_add {k : ℕ} {d d' : Fin k → ℕ+} (h : d = d')
    (T S : KTensor F d) :
    (h ▸ (T + S) : KTensor F d') = (h ▸ T : KTensor F d') + (h ▸ S : KTensor F d') := by
  subst h; rfl

/-- **Helper**: transport along format equality commutes with scalar action. -/
private lemma KTensor_cast_smul {k : ℕ} {d d' : Fin k → ℕ+} (h : d = d')
    (r : F) (T : KTensor F d) :
    (h ▸ (r • T) : KTensor F d') = r • (h ▸ T : KTensor F d') := by
  subst h; rfl

/-- **Helper**: Transport along a function equality `f = g` preserves the underlying
    `Nat` value of pointwise `Fin` elements. Used in `sliceFun_split_left/right`
    to bridge `((formatPow_add_eq_mul d n n').symm ▸ idx) i` with `idx i`.

    Generic version: for any `f g : Fin k → ℕ+` with `h : f = g`, and any
    `x : ∀ i, Fin ↑(f i)`, the cast `h ▸ x` has the same pointwise `.val`. -/
private lemma val_eq_rec_pi_fin
    {k : ℕ} {f g : Fin k → ℕ+} (h : f = g)
    (x : ∀ i : Fin k, Fin ↑(f i)) (i : Fin k) :
    ((h ▸ x : ∀ i, Fin ↑(g i)) i).val = (x i).val := by
  subst h
  rfl

/-- **Structural identity, multi-index decomposition** (Christandl et al., Section 2.1). The `j`-th slice of the (n+n')-decomposition
    of `(formatPow_add_eq_mul d n n').symm ▸ idx` (a multi-index living in the
    `(d^(n+n'))`-leg format) on `Fin.castAdd n' j` (for `j : Fin n`) equals the
    `j`-th slice of the `n`-decomposition of `kronLeftIndex idx` (a multi-index
    living in the `d^n`-leg format).

    Section 2.1: `regroupingMap` is the linear extension of `v_1 ⊗ ⋯ ⊗ v_n ↦
    v_1 ⊠ ⋯ ⊠ v_n`; the paper's `⊠`-associativity then says the `n+n'`-fold
    Kronecker product factors as `(n-fold) ⊠ (n'-fold)`. This is precisely the
    statement of compatibility of digit-decomposition for `(d i)^(n+n') =
    (d i)^n * (d i)^n'`.

    Now that `powIndexEquiv` (`TensorRank.lean`) is defined via Mathlib's
    computable `finFunctionFinEquiv` (`Mathlib.Algebra.BigOperators.Fin` line 580)
    composed with `Fin.rev`, with the big-endian convention (low positions = high
    digits), both halves reduce to elementary `Nat` arithmetic on
    `a / d^(n+n'-1-j) = (a / d^n') / d^(n-1-j)` (`Nat.div_div_eq_div_mul` and
    `pow_add`). See `regroupingMap_tensorPowerAdd_symm_eq_kron_cast` for the
    downstream consumer. -/
lemma sliceFun_split_left {k : ℕ} (d : Fin k → ℕ+) (n n' : ℕ+)
    (idx : ∀ i : Fin k, Fin (formatPow d n i * formatPow d n' i))
    (j : Fin (n : ℕ)) :
    sliceFun d ⟨(n : ℕ) + (n' : ℕ), Nat.add_pos_left n.pos _⟩
        ((formatPow_add_eq_mul d n n').symm ▸ idx) (Fin.castAdd (n' : ℕ) j)
      = sliceFun d n (kronLeftIndex idx) j := by
  -- Stage 1: Replace the `▸`-cast by an explicit `Eq.rec` (this is what Lean's
  -- elaborator computes) so we can hypothesize about its `.val` value.
  set jdx_full :
      (i : Fin k) → Fin ↑(formatPow d ⟨(n : ℕ) + (n' : ℕ),
        Nat.add_pos_left n.pos _⟩ i) :=
    Eq.rec (motive := fun x _ ↦ (i : Fin k) → Fin ↑(x i)) idx
      (formatPow_add_eq_mul d n n').symm with hjdx_full_def
  -- Stage 2: Key fact — `.val` is invariant under the `Eq.rec` cast on functions.
  have hval_jdx : ∀ i, (jdx_full i).val = (idx i).val := by
    intro i
    rw [hjdx_full_def]
    exact val_eq_rec_pi_fin (formatPow_add_eq_mul d n n').symm idx i
  -- Stage 3: Per-leg arithmetic.
  funext i
  unfold sliceFun
  apply Fin.ext
  -- Unfold `powIndexEquiv` to expose `finFunctionFinEquiv.symm`, then use the
  -- `@[simps!]`-generated `finFunctionFinEquiv_symm_apply_val`:
  --   `(finFunctionFinEquiv.symm a b).val = a.val / m^b.val % m`.
  simp only [powIndexEquiv, Equiv.coe_fn_mk, finFunctionFinEquiv_symm_apply_val]
  -- Compute Fin.rev positions.
  have hrev_castAdd :
      (Fin.rev (Fin.castAdd (n' : ℕ) j) : Fin ((n : ℕ) + (n' : ℕ))).val
        = (n : ℕ) + (n' : ℕ) - 1 - (j : ℕ) := by
    simp [Fin.val_rev]; omega
  have hrev_j : (Fin.rev j : Fin (n : ℕ)).val = (n : ℕ) - 1 - (j : ℕ) := by
    simp [Fin.val_rev]; omega
  rw [hrev_castAdd, hrev_j]
  -- Goal: ↑(jdx_full i) / d^(n+n'-1-j) % d = ↑(kronLeftIndex idx i) / d^(n-1-j) % d.
  -- Rewrite via `hval_jdx` and the explicit `kronLeftIndex` div-formula.
  rw [hval_jdx i]
  have hkL : (kronLeftIndex idx i).val
      = (idx i).val / ((d i : ℕ) ^ (n' : ℕ)) := by
    simp only [kronLeftIndex, finProdFinEquiv_symm_apply, Fin.divNat]
    rfl
  rw [hkL]
  -- Now: (idx i).val / (d i)^(n+n'-1-j) % (d i)
  --   = ((idx i).val / (d i)^n') / (d i)^(n-1-j) % (d i)
  -- via (a/p)/q = a/(p*q) and pow_add for n+n'-1-j = n' + (n-1-j).
  have hjle : (j : ℕ) + 1 ≤ (n : ℕ) := j.is_lt
  have hsum : (n : ℕ) + (n' : ℕ) - 1 - (j : ℕ) = (n' : ℕ) + ((n : ℕ) - 1 - (j : ℕ)) := by
    omega
  rw [hsum, pow_add, ← Nat.div_div_eq_div_mul]

/-- **Structural identity, multi-index decomposition (right half)** (Christandl et al., Section 2.1). The `(n+j)`-th slice (for
    `j : Fin n'`) of the (n+n')-decomposition equals the `j`-th slice of the
    `n'`-decomposition of `kronRightIndex idx`. See `sliceFun_split_left` for
    the full discussion. -/
lemma sliceFun_split_right {k : ℕ} (d : Fin k → ℕ+) (n n' : ℕ+)
    (idx : ∀ i : Fin k, Fin (formatPow d n i * formatPow d n' i))
    (j : Fin (n' : ℕ)) :
    sliceFun d ⟨(n : ℕ) + (n' : ℕ), Nat.add_pos_left n.pos _⟩
        ((formatPow_add_eq_mul d n n').symm ▸ idx) (Fin.natAdd (n : ℕ) j)
      = sliceFun d n' (kronRightIndex idx) j := by
  -- Stage 1: Explicit `Eq.rec` for the `▸`-cast.
  set jdx_full :
      (i : Fin k) → Fin ↑(formatPow d ⟨(n : ℕ) + (n' : ℕ),
        Nat.add_pos_left n.pos _⟩ i) :=
    Eq.rec (motive := fun x _ ↦ (i : Fin k) → Fin ↑(x i)) idx
      (formatPow_add_eq_mul d n n').symm with hjdx_full_def
  have hval_jdx : ∀ i, (jdx_full i).val = (idx i).val := by
    intro i
    rw [hjdx_full_def]
    exact val_eq_rec_pi_fin (formatPow_add_eq_mul d n n').symm idx i
  funext i
  unfold sliceFun
  apply Fin.ext
  simp only [powIndexEquiv, Equiv.coe_fn_mk, finFunctionFinEquiv_symm_apply_val]
  -- Fin.rev positions: rev (natAdd n j) has val n'-1-j in Fin (n+n');
  -- rev j has val n'-1-j in Fin n'.
  have hrev_natAdd : (Fin.rev (Fin.natAdd (n : ℕ) j) : Fin ((n : ℕ) + (n' : ℕ))).val
      = (n' : ℕ) - 1 - (j : ℕ) := by
    simp [Fin.val_rev]; omega
  have hrev_j : (Fin.rev j : Fin (n' : ℕ)).val = (n' : ℕ) - 1 - (j : ℕ) := by
    simp [Fin.val_rev]; omega
  rw [hrev_natAdd, hrev_j]
  -- Bridge via hval_jdx and explicit kronRightIndex modulo-formula.
  rw [hval_jdx i]
  have hkR : (kronRightIndex idx i).val
      = (idx i).val % ((d i : ℕ) ^ (n' : ℕ)) := by
    simp only [kronRightIndex, finProdFinEquiv_symm_apply, Fin.modNat]
    rfl
  rw [hkR]
  -- Goal: (idx i).val / (d i)^(n'-1-j) % (d i)
  --     = ((idx i).val % (d i)^n') / (d i)^(n'-1-j) % (d i)
  -- Decomposition: (idx i).val = r * d^n' + q with q < d^n', r = (idx i).val/d^n'.
  -- Then (idx i).val / d^p = r * d^(n'-p) + q/d^p (since q < d^n' and p ≤ n').
  -- Since n'-p ≥ 1, the first summand is a multiple of d, so mod d gives q/d^p % d.
  have hjlt : (j : ℕ) < (n' : ℕ) := j.is_lt
  set p : ℕ := (n' : ℕ) - 1 - (j : ℕ) with hp_def
  set q : ℕ := (idx i).val % ((d i : ℕ) ^ (n' : ℕ)) with hq_def
  set r : ℕ := (idx i).val / ((d i : ℕ) ^ (n' : ℕ)) with hr_def
  have ha_decomp : (idx i).val = r * ((d i : ℕ) ^ (n' : ℕ)) + q := by
    show (idx i).val
        = ((idx i).val / ((d i : ℕ) ^ (n' : ℕ))) * ((d i : ℕ) ^ (n' : ℕ))
          + (idx i).val % ((d i : ℕ) ^ (n' : ℕ))
    -- `Nat.div_add_mod : k * (m / k) + m % k = m`. Reframe with `Nat.div_mul_add_mod`.
    have := Nat.div_add_mod (idx i).val ((d i : ℕ) ^ (n' : ℕ))
    linarith [this, Nat.mul_comm ((d i : ℕ) ^ (n' : ℕ)) ((idx i).val / (d i : ℕ) ^ (n' : ℕ))]
  rw [ha_decomp]
  have hd_pos : 0 < (d i : ℕ) := (d i).pos
  have hd_pow_pos : 0 < ((d i : ℕ) ^ p) := pow_pos hd_pos _
  have hp_le' : p ≤ (n' : ℕ) := by simp [hp_def]; omega
  have hpow_split :
      ((d i : ℕ) ^ (n' : ℕ)) = ((d i : ℕ) ^ p) * ((d i : ℕ) ^ ((n' : ℕ) - p)) := by
    rw [← pow_add]
    congr 1; omega
  rw [hpow_split]
  rw [show r * (((d i : ℕ) ^ p) * ((d i : ℕ) ^ ((n' : ℕ) - p))) + q
        = q + r * ((d i : ℕ) ^ ((n' : ℕ) - p)) * ((d i : ℕ) ^ p) from by ring]
  rw [Nat.add_mul_div_right _ _ hd_pow_pos]
  have hnp_pos : 1 ≤ (n' : ℕ) - p := by simp [hp_def]; omega
  rw [show ((d i : ℕ) ^ ((n' : ℕ) - p))
        = (d i : ℕ) * ((d i : ℕ) ^ ((n' : ℕ) - p - 1)) from by
    rw [← pow_succ']; congr 1; omega]
  rw [show q / ((d i : ℕ) ^ p) + r * ((d i : ℕ) * ((d i : ℕ) ^ ((n' : ℕ) - p - 1)))
        = q / ((d i : ℕ) ^ p)
          + (r * ((d i : ℕ) ^ ((n' : ℕ) - p - 1))) * (d i : ℕ) from by ring]
  rw [Nat.add_mul_mod_self_right]

/-- **Helper (base case of the regrouping in Section 2.1)**: structural identity on `tprod ⊗ tprod`.
    Combines `TensorPower.tprod_mul_tprod` (which says `mulEquiv (tprod u ⊗ tprod v)
    = tprod (Fin.append u v)`) with the entry-wise computation of `regroupingMap`
    on a `tprod`, plus the `sliceFun_split_left`/`right` digit-decomposition
    identities. -/
private lemma regroupingMap_tensorPowerAdd_symm_eq_kron_cast_tprod_tprod
    {k : ℕ} (d : Fin k → ℕ+) (n n' : ℕ+)
    (u : Fin (n : ℕ) → KTensor F d) (v : Fin (n' : ℕ) → KTensor F d) :
    (formatPow_add_eq_mul d n n') ▸
        regroupingMap d ⟨(n : ℕ) + (n' : ℕ), Nat.add_pos_left n.pos _⟩
          ((tensorPowerAdd F (KTensor F d) (n : ℕ) (n' : ℕ)).symm
            (PiTensorProduct.tprod F u ⊗ₜ[F] PiTensorProduct.tprod F v))
      = (regroupingMap d n (PiTensorProduct.tprod F u)) ⊠
          (regroupingMap d n' (PiTensorProduct.tprod F v)) := by
  -- First, expand `(tensorPowerAdd ..).symm (tprod u ⊗ tprod v) = tprod (Fin.append u v)`.
  have htmul :
      (tensorPowerAdd F (KTensor F d) (n : ℕ) (n' : ℕ)).symm
          (PiTensorProduct.tprod F u ⊗ₜ[F] PiTensorProduct.tprod F v)
        = PiTensorProduct.tprod F (Fin.append u v) := by
    unfold tensorPowerAdd
    change TensorPower.mulEquiv _ = _
    exact TensorPower.tprod_mul_tprod F u v
  rw [htmul]
  -- Both sides have type KTensor F (fun i => formatPow d n i * formatPow d n' i).
  -- Reduce to entry-wise via funext.
  funext idx
  -- Replace LHS cast via KTensor_cast_apply (simp only handles the implicit-proof
  -- mismatch that bare rw can't resolve).
  simp only [KTensor_cast_apply]
  -- Name the recast index to make the next rewrite work.
  set jdx_full : (i : Fin k) → Fin ↑(formatPow d
        ⟨(n : ℕ) + (n' : ℕ), Nat.add_pos_left n.pos _⟩ i) :=
      Eq.rec (motive := fun x _ ↦ (i : Fin k) → Fin ↑(x i)) idx
        (formatPow_add_eq_mul d n n').symm with hjdx_full_def
  -- Apply regroupingMap_tprod_apply to LHS via `have`-trans (rw has unification issues here).
  have happ := regroupingMap_tprod_apply (F := F) d
        ⟨(n : ℕ) + (n' : ℕ), Nat.add_pos_left n.pos _⟩ (Fin.append u v) jdx_full
  refine happ.trans ?_
  -- Goal: ∏ j, Fin.append u v j (sliceFun d ⟨n+n', _⟩ jdx_full j)
  --     = (regroupingMap d n (tprod u) ⊠ regroupingMap d n' (tprod v)) idx
  -- RHS: kroneckerTensor at idx.
  change _ = regroupingMap d n (PiTensorProduct.tprod F u) (kronLeftIndex idx)
              * regroupingMap d n' (PiTensorProduct.tprod F v) (kronRightIndex idx)
  rw [regroupingMap_tprod_apply d n u (kronLeftIndex idx)]
  rw [regroupingMap_tprod_apply d n' v (kronRightIndex idx)]
  -- Split LHS product via Fin.prod_univ_add into Fin n part + Fin n' part.
  have hsplit := Fin.prod_univ_add (a := (n : ℕ)) (b := (n' : ℕ))
    (fun j : Fin ((n : ℕ) + (n' : ℕ)) => (Fin.append u v) j
      (sliceFun d ⟨(n : ℕ) + (n' : ℕ), Nat.add_pos_left n.pos _⟩ jdx_full j))
  refine hsplit.trans ?_
  congr 1
  · refine Finset.prod_congr rfl ?_
    intro j _
    rw [Fin.append_left u v j]
    congr 1
    rw [hjdx_full_def]
    exact sliceFun_split_left d n n' idx j
  · refine Finset.prod_congr rfl ?_
    intro j _
    rw [Fin.append_right u v j]
    congr 1
    rw [hjdx_full_def]
    exact sliceFun_split_right d n n' idx j

/-- **Structural identity (Section 2.1)**: regrouping the `(n+n')`-fold `tprod` of a
    block-decomposable tensor equals the iterated Kronecker product
    `(regroupingMap d n T) ⊠ (regroupingMap d n' S)`, modulo the format cast
    `formatPow_add_eq_mul`.

    The paper writes (Section 2.1): `regroupingMap` is the linear extension of
    `v_1 ⊗ ⋯ ⊗ v_n ↦ v_1 ⊠ ⋯ ⊠ v_n`. Hence on the block-decomposable tensor
    `(tensorPowerAdd ..).symm (T ⊗ S)` (which on simple tensors becomes
    `Fin.append U V` per `TensorPower.tprod_mul_tprod`), the regrouping computes
    as the iterated Kronecker product.

    Proof: bilinear extension. Both LHS and RHS are linear in `T` (for fixed `S`)
    and in `S` (for fixed `T`), so by `PiTensorProduct.induction_on` on `T` then
    on `S`, equality reduces to the base case
    `regroupingMap_tensorPowerAdd_symm_eq_kron_cast_tprod_tprod`. -/
lemma regroupingMap_tensorPowerAdd_symm_eq_kron_cast
    {k : ℕ} (d : Fin k → ℕ+)
    (n n' : ℕ+) (T : TensorPower F (n : ℕ) (KTensor F d))
    (S : TensorPower F (n' : ℕ) (KTensor F d)) :
    (formatPow_add_eq_mul d n n') ▸
        regroupingMap d ⟨(n : ℕ) + (n' : ℕ), Nat.add_pos_left n.pos _⟩
          ((tensorPowerAdd F (KTensor F d) (n : ℕ) (n' : ℕ)).symm (T ⊗ₜ[F] S))
      = (regroupingMap d n T) ⊠ (regroupingMap d n' S) := by
  -- Bilinear extension. Induct on T, then on S, reducing to the tprod⊗tprod base case
  -- handled by `regroupingMap_tensorPowerAdd_symm_eq_kron_cast_tprod_tprod`.
  induction T using PiTensorProduct.induction_on with
  | smul_tprod r u =>
    induction S using PiTensorProduct.induction_on with
    | smul_tprod r' v =>
      -- Base case modulo scalars: pull `r` and `r'` out on both sides.
      -- LHS linearity: `regroupingMap` and `(tensorPowerAdd ..).symm` are linear, ▸
      -- distributes over •.
      -- RHS linearity: `regroupingMap` is linear, `⊠` is bilinear; linear in T and S.
      have hbase := regroupingMap_tensorPowerAdd_symm_eq_kron_cast_tprod_tprod
        (F := F) d n n' u v
      -- LHS = (r * r') • LHS(tprod, tprod); RHS = (r * r') • RHS(tprod, tprod).
      -- Goal becomes: (r * r') • LHS(tprod, tprod) = (r * r') • RHS(tprod, tprod),
      -- which follows from hbase by smul_congr.
      -- Reduce LHS via linearity of ⊗ₜ and the maps involved.
      rw [show ((r • PiTensorProduct.tprod F u) ⊗ₜ[F] (r' • PiTensorProduct.tprod F v) :
              TensorPower F (n : ℕ) (KTensor F d) ⊗[F] TensorPower F (n' : ℕ) (KTensor F d))
            = (r * r') •
              ((PiTensorProduct.tprod F u) ⊗ₜ[F] (PiTensorProduct.tprod F v)) from by
        rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul, ← mul_smul,
            ← TensorProduct.smul_tmul]]
      rw [LinearEquiv.map_smul, LinearMap.map_smul]
      -- LHS: (formatCast) ▸ (r * r') • _ = (r * r') • ((formatCast) ▸ _)
      rw [KTensor_cast_smul (formatPow_add_eq_mul d n n') (r * r')]
      -- RHS: regroupingMap d n (r • tprod u) = r • regroupingMap d n (tprod u), similarly for v.
      -- Then ⊠ is bilinear: (r • X) ⊠ (r' • Y) = (r * r') • (X ⊠ Y).
      rw [LinearMap.map_smul, LinearMap.map_smul]
      -- Goal: (r * r') • LHS_base = (r • X) ⊠ (r' • Y)
      rw [show
        ((r • (regroupingMap d n (PiTensorProduct.tprod F u))) ⊠
          (r' • (regroupingMap d n' (PiTensorProduct.tprod F v)))) =
        (r * r') • ((regroupingMap d n (PiTensorProduct.tprod F u)) ⊠
          (regroupingMap d n' (PiTensorProduct.tprod F v))) from by
          funext idx; simp only [Pi.smul_apply, smul_eq_mul, kroneckerTensor]; ring]
      rw [hbase]
    | add x y hx hy =>
      -- S = x + y, S-linearity: ⊗ₜ distributes over + in the right slot;
      -- regroupingMap is linear, ▸ commutes with +, ⊠ distributes over + in slot 2.
      rw [TensorProduct.tmul_add, LinearEquiv.map_add, LinearMap.map_add]
      rw [KTensor_cast_add]
      rw [hx, hy]
      rw [LinearMap.map_add]
      funext idx
      simp only [Pi.add_apply, kroneckerTensor, mul_add]
  | add x y hx hy =>
    rw [TensorProduct.add_tmul, LinearEquiv.map_add, LinearMap.map_add]
    rw [KTensor_cast_add]
    rw [hx, hy]
    rw [LinearMap.map_add]
    funext idx
    simp only [Pi.add_apply, kroneckerTensor, add_mul]

/-- **Helper (`regroupingMap` submultiplicativity at the `ℕ` rank level)**:
    `R(regroupingMap d (n+n') ((tensorPowerAdd ..).symm (T ⊗ S)))
       ≤ R(regroupingMap d n T) · R(regroupingMap d n' S)`.

    The identity in Section 2.1 `regroupingMap (v_1 ⊗ ⋯ ⊗ v_n ⊗ w_1 ⊗ ⋯ ⊗ w_{n'})
    = (v_1 ⊠ ⋯ ⊠ v_n) ⊠ (w_1 ⊠ ⋯ ⊠ w_{n'})` together with `tensorRank_kron_le`
    gives the bound; the format identification `(d i)^(n+n') = (d i)^n · (d i)^n'`
    is `PNat.pow_add` (transports tensor rank).

    Proof structure:
    1. Format-cast the LHS via `formatPow_add_eq_mul d n n'` and
       `tensorRank_format_cast` (rank is preserved).
    2. After the cast, apply the structural identity
       `regroupingMap_tensorPowerAdd_symm_eq_kron_cast` to rewrite the LHS as
       `(regroupingMap d n T) ⊠ (regroupingMap d n' S)`.
    3. Conclude via `tensorRank_kron_le hk`. -/
lemma tensorRank_regroupingMap_add_le {k : ℕ} (hk : 1 ≤ k) (d : Fin k → ℕ+)
    (n n' : ℕ+) (T : TensorPower F (n : ℕ) (KTensor F d))
    (S : TensorPower F (n' : ℕ) (KTensor F d)) :
    tensorRank
      (regroupingMap d ⟨(n : ℕ) + (n' : ℕ), Nat.add_pos_left n.pos _⟩
        ((tensorPowerAdd F (KTensor F d) (n : ℕ) (n' : ℕ)).symm (T ⊗ₜ[F] S)))
      ≤
    tensorRank (regroupingMap d n T) * tensorRank (regroupingMap d n' S) := by
  -- Step 1: format-cast preserves rank.
  set hfmt : formatPow d ⟨(n : ℕ) + (n' : ℕ), Nat.add_pos_left n.pos _⟩
      = fun i => formatPow d n i * formatPow d n' i := formatPow_add_eq_mul d n n'
  set LHS := regroupingMap d ⟨(n : ℕ) + (n' : ℕ), Nat.add_pos_left n.pos _⟩
        ((tensorPowerAdd F (KTensor F d) (n : ℕ) (n' : ℕ)).symm (T ⊗ₜ[F] S))
  rw [show tensorRank LHS = tensorRank (hfmt ▸ LHS) from
    (tensorRank_format_cast (F := F) hfmt LHS).symm]
  -- Step 2: structural identity.
  rw [regroupingMap_tensorPowerAdd_symm_eq_kron_cast (F := F) d n n' T S]
  -- Step 3: tensor-rank submultiplicativity under `⊠`.
  exact tensorRank_kron_le (F := F) hk _ _

/-! ### Block-perm structural helpers (Definition 2.1)

Permutation invariance of `F_{n_1+⋯+n_ℓ}(T_1 ⊗ ⋯ ⊗ T_ℓ)` under `σ : [ℓ] → [ℓ]`
is Definition 2.1(iii):

> F_{n_1+⋯+n_ℓ}(T_1 ⊗ ⋯ ⊗ T_ℓ) = F_{n_1+⋯+n_ℓ}(T_{σ(1)} ⊗ ⋯ ⊗ T_{σ(ℓ)})

For the canonical `F_n = tensorRank ∘ regroupingMap`, this reduces to two
ingredients:

* **Format coincidence** (Lean equality): the output formats
  `formatPow d ⟨∑ nVec, hpos₁⟩` and `formatPow d ⟨∑ nVec ∘ σ, hpos₂⟩` agree
  because `∑ nVec = ∑ nVec ∘ σ` (reindex permutation under `Finset.sum`).

* **Rank invariance after the cast** (structural, Definition 2.1): once the
  formats are identified, the two regrouped tensors have equal tensor rank.
  This is the rank-level statement of Definition 2.1 itself; we isolate it as a
  named axiom-style helper below. -/

/-- **Sum invariance under permutation** of `nVec : Fin ℓ → ℕ+`:
    `∑ i, (nVec i : ℕ) = ∑ i, ((nVec (σ i)) : ℕ)` for any `σ : Equiv.Perm (Fin ℓ)`.

    Used to identify the output formats of `regroupingMap d ⟨_, hpos₁⟩` and
    `regroupingMap d ⟨_, hpos₂⟩` in `tensorRank_regroupingMap_block_perm`
    (Definition 2.1). -/
lemma sum_nVec_perm_eq {ℓ : ℕ} (nVec : Fin ℓ → ℕ+) (σ : Equiv.Perm (Fin ℓ)) :
    ∑ i, (nVec i : ℕ) = ∑ i, ((nVec (σ i)) : ℕ) := by
  exact (Equiv.sum_comp σ (fun i => (nVec i : ℕ))).symm

/-- **Format coincidence under block permutation** (Definition 2.1):
    `formatPow d ⟨_, hpos₁⟩ = formatPow d ⟨_, hpos₂⟩` since both PNats have
    the same underlying value `∑ i, (nVec i : ℕ) = ∑ i, ((nVec (σ i)) : ℕ)`. -/
lemma formatPow_block_perm_eq {k : ℕ} (d : Fin k → ℕ+)
    {ℓ : ℕ} (nVec : Fin ℓ → ℕ+) (σ : Equiv.Perm (Fin ℓ))
    (hpos₁ : 0 < ∑ i, (nVec i : ℕ))
    (hpos₂ : 0 < ∑ i, ((nVec (σ i)) : ℕ)) :
    formatPow d ⟨_, hpos₁⟩
      = formatPow d ⟨(∑ i, ((nVec (σ i)) : ℕ)), hpos₂⟩ := by
  funext i
  simp only [formatPow]
  -- `d i ^ N = d i ^ N'` where `N = ∑ nVec` and `N' = ∑ nVec ∘ σ` agree.
  have hsum : ∑ i, (nVec i : ℕ) = ∑ i, ((nVec (σ i)) : ℕ) :=
    sum_nVec_perm_eq nVec σ
  -- Both sides are `(d i : ℕ+)^(sum)` with PNat.val equal; reduce via cast on PNat.
  apply PNat.coe_inj.mp
  simp [PNat.pow_coe, hsum]

/-! ### Leg-wise reindexing API for `KTensor` (Definition 2.1(iii))

The rank-level statement of Definition 2.1 (perm-invariance) requires that
`tensorRank` is preserved under uniform leg-wise reindexing of a `KTensor`:
given per-leg `Equiv`s `φ i : Fin (d i) ≃ Fin (d i)` (each leg may have its
own permutation), the tensor `T ∘ φ` (pulled back leg-wise) has the same
tensor rank as `T`.

Realized via bidirectional `Restricts`: the leg-wise permutation matrices
`P_i` and their inverses witness the restriction in both directions, so
`tensorRank_mono_under_Restricts` (TensorRank.lean) yields the equality.
-/

/-- **Leg-wise pull-back** of a `KTensor` by per-leg `Equiv`s.
    Given `φ i : Fin (d i) ≃ Fin (d i)`, transports `T : KTensor F d`
    to `fun jdx => T (fun i => φ i (jdx i))`. -/
def KTensor.legPerm {k : ℕ} {d : Fin k → ℕ+}
    (T : KTensor F d) (φ : ∀ i : Fin k, Equiv.Perm (Fin (d i))) :
    KTensor F d :=
  fun jdx => T (fun i => φ i (jdx i))

/-- **Permutation matrix** for a single `Equiv.Perm (Fin n)`:
    `(P_φ) j i = 1 if i = φ j, else 0`. Witnesses `(P_φ · v) j = v (φ j)`. -/
private def permMatrix {n : ℕ} (φ : Equiv.Perm (Fin n)) :
    Matrix (Fin n) (Fin n) F :=
  fun j i => if i = φ j then 1 else 0

/-- **Restriction-witness**: `T.legPerm φ ≤ T` via leg-wise permutation matrices.
    Each `permMatrix (φ i)` realizes the leg-wise reindexing on `Fin (d i)`. -/
lemma KTensor.legPerm_Restricts {k : ℕ} {d : Fin k → ℕ+}
    (T : KTensor F d) (φ : ∀ i : Fin k, Equiv.Perm (Fin (d i))) :
    Restricts (T.legPerm φ) T := by
  classical
  refine ⟨fun i => permMatrix (F := F) (φ i), ?_⟩
  intro jdx
  -- Goal: T.legPerm φ jdx = ∑ idx, (∏ i, permMatrix (φ i) (jdx i) (idx i)) * T idx.
  -- The product ∏ i, [idx i = φ i (jdx i)] is 1 iff idx i = φ i (jdx i) for all i,
  -- else 0. So the sum collapses to T (fun i => φ i (jdx i)) = T.legPerm φ jdx.
  show T (fun i => φ i (jdx i))
      = ∑ idx : (∀ i : Fin k, Fin (d i)),
        (∏ i, (permMatrix (F := F) (φ i)) (jdx i) (idx i)) * T idx
  rw [Finset.sum_eq_single (fun i : Fin k => φ i (jdx i))]
  · -- At idx = fun i => φ i (jdx i): product is 1.
    have hprod :
        (∏ i, (permMatrix (F := F) (φ i)) (jdx i) ((fun i' => φ i' (jdx i')) i)) = 1 := by
      apply Finset.prod_eq_one
      intro i _
      simp [permMatrix]
    rw [hprod, one_mul]
  · -- For idx ≠ (fun i => φ i (jdx i)): some leg i₀ has idx i₀ ≠ φ i₀ (jdx i₀).
    intro idx _ hne
    have hex : ∃ i₀ : Fin k, idx i₀ ≠ φ i₀ (jdx i₀) := by
      by_contra hall
      push_neg at hall
      exact hne (funext hall)
    obtain ⟨i₀, hi₀⟩ := hex
    have hzero : (permMatrix (F := F) (φ i₀)) (jdx i₀) (idx i₀) = 0 := by
      simp [permMatrix, hi₀]
    have hprod_zero :
        (∏ i, (permMatrix (F := F) (φ i)) (jdx i) (idx i)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i₀) hzero
    rw [hprod_zero, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- **Restriction-witness (reverse)**: `T ≤ T.legPerm φ` via the inverse permutations.
    Composing `legPerm φ` with `legPerm φ⁻¹` recovers `T`, so `legPerm φ⁻¹ (T.legPerm φ)
    = T`; thus `T ≤ T.legPerm φ` by `legPerm_Restricts` applied to `T.legPerm φ`
    with `φ⁻¹`. -/
lemma KTensor.Restricts_legPerm {k : ℕ} {d : Fin k → ℕ+}
    (T : KTensor F d) (φ : ∀ i : Fin k, Equiv.Perm (Fin (d i))) :
    Restricts T (T.legPerm φ) := by
  classical
  -- Apply `legPerm_Restricts` with `T' := T.legPerm φ` and `φ' := fun i => (φ i).symm`.
  have h := KTensor.legPerm_Restricts (F := F) (T.legPerm φ) (fun i => (φ i).symm)
  -- Then `(T.legPerm φ).legPerm (fun i => (φ i).symm) = T` (cancellation).
  have heq : (T.legPerm φ).legPerm (fun i => (φ i).symm) = T := by
    funext jdx
    -- (legPerm.legPerm) jdx = T (fun i => φ i ((φ i).symm (jdx i))) = T jdx.
    unfold KTensor.legPerm
    congr 1
    funext i
    exact Equiv.apply_symm_apply (φ i) (jdx i)
  rw [heq] at h
  exact h

/-- **Rank-invariance under leg-wise permutation** (the bedrock fact behind
    Definition 2.1 at the rank level). Bidirectional `Restricts` via
    `legPerm_Restricts` and `Restricts_legPerm` gives the equality
    via `tensorRank_mono_under_Restricts`. -/
lemma tensorRank_legPerm_eq {k : ℕ} (hk : 1 ≤ k) {d : Fin k → ℕ+}
    (T : KTensor F d) (φ : ∀ i : Fin k, Equiv.Perm (Fin (d i))) :
    tensorRank (T.legPerm φ) = tensorRank T := by
  apply le_antisymm
  · exact tensorRank_mono_under_Restricts hk (T.legPerm_Restricts φ)
  · exact tensorRank_mono_under_Restricts hk (T.Restricts_legPerm φ)

/-- **`powIndexEquiv` value depends only on the `Nat` values** of `n`, the
    decomposed index `a`, and the position `j` (Definition 2.1(iii)). Two
    `powIndexEquiv` digits with equal underlying `Nat`-data agree, even across
    different (equal-valued) exponents `n n'`. Proved via the explicit base-`d`
    digit formula `(finFunctionFinEquiv.symm a r).val = a.val / d^r.val % d` and
    `(Fin.rev j).val = n - 1 - j.val`. -/
private lemma powIndexEquiv_val_congr (d : ℕ+) {n n' : ℕ+}
    {a : Fin ((d : ℕ) ^ (n : ℕ))} {a' : Fin ((d : ℕ) ^ (n' : ℕ))}
    {j : Fin (n : ℕ)} {j' : Fin (n' : ℕ)}
    (hn : (n : ℕ) = (n' : ℕ)) (ha : a.val = a'.val) (hj : j.val = j'.val) :
    (powIndexEquiv d n a j).val = (powIndexEquiv d n' a' j').val := by
  simp only [powIndexEquiv, Equiv.coe_fn_mk, finFunctionFinEquiv_symm_apply_val]
  rw [ha]
  congr 2
  · -- d ^ (Fin.rev j).val = d ^ (Fin.rev j').val
    rw [Fin.val_rev, Fin.val_rev]
    congr 1
    omega

/-- The block-permutation τ on Fin (∑ nVec (σ i)) induced by σ, used as the
    digit-permutation in all `_for_tau` helpers. This is the SPECIFIC τ that
    makes the perm_inv identity hold (arbitrary τ would imply invariance under
    every digit permutation, which is false for non-symmetric tensors). -/
private noncomputable def tauOfSigma
    {ℓ : ℕ} (nVec : Fin ℓ → ℕ+) (σ : Equiv.Perm (Fin ℓ)) :
    Equiv.Perm (Fin (∑ i, ((nVec (σ i)) : ℕ))) :=
  let nσ : Fin ℓ → ℕ := fun i => (nVec (σ i) : ℕ)
  let eSig : Sigma (fun i : Fin ℓ => Fin (nσ i)) ≃
      Sigma (fun i : Fin ℓ => Fin ((nVec i : ℕ))) :=
    (Equiv.sigmaCongrLeft' (β := fun i : Fin ℓ => Fin ((nVec i : ℕ))) σ.symm).symm
  ((finSigmaFinEquiv (n := nσ)).symm.trans
    (eSig.trans
      ((finSigmaFinEquiv (n := fun i : Fin ℓ => (nVec i : ℕ))).trans
        (finCongr (sum_nVec_perm_eq nVec σ)))))

/-- **Block-permutation action of `tauOfSigma` at the sigma level** (Definition 2.1).
    The digit permutation `τ = tauOfSigma nVec σ` sends the position
    `finSigmaFinEquiv ⟨a, b⟩` (digit `b` inside block `a`, where block `a` has size
    `nVec (σ a)`) to `finCongr _ (finSigmaFinEquiv ⟨σ a, b⟩)` (the same digit `b`,
    now inside block `σ a` of the `nVec`-ordering). This is the concrete
    `finSigmaFinEquiv`/`sigmaCongrLeft'` content of `tauOfSigma`. -/
private lemma tauOfSigma_finSigmaFinEquiv
    {ℓ : ℕ} (nVec : Fin ℓ → ℕ+) (σ : Equiv.Perm (Fin ℓ))
    (a : Fin ℓ) (b : Fin ((nVec (σ a)) : ℕ)) :
    tauOfSigma nVec σ
        (finSigmaFinEquiv (n := fun i => (nVec (σ i) : ℕ)) ⟨a, b⟩)
      = finCongr (sum_nVec_perm_eq nVec σ)
          (finSigmaFinEquiv (n := fun i => (nVec i : ℕ)) ⟨σ a, b⟩) := by
  unfold tauOfSigma
  simp only [Equiv.trans_apply, Equiv.symm_apply_apply]
  -- The middle equiv `eSig = (sigmaCongrLeft' σ.symm).symm` sends ⟨a, b⟩ to ⟨σ a, b⟩.
  congr 1

/-- **Value-action of the leg permutation `φ_σ`** (Definition 2.1). For the digit
    permutation `τ` and the format-`N₂` leg `i`, the permutation
    `φ_σ i = powIndexEquiv ≫ arrowCongr τ.symm refl ≫ powIndexEquiv.symm` acts on
    the digit decomposition by `powIndexEquiv (φ_σ i x) j = powIndexEquiv x (τ j)`
    (because `Equiv.arrowCongr τ.symm refl f = f ∘ τ.symm.symm = f ∘ τ`). -/
private lemma powIndexEquiv_φ_σ
    {k : ℕ} (d : Fin k → ℕ+)
    {ℓ : ℕ} (nVec : Fin (ℓ + 1) → ℕ+) (σ : Equiv.Perm (Fin (ℓ + 1)))
    (hpos₂ : 0 < ∑ i, ((nVec (σ i)) : ℕ))
    (i : Fin k)
    (x : Fin (formatPow d ⟨(∑ i, ((nVec (σ i)) : ℕ)), hpos₂⟩ i))
    (j : Fin (∑ i, ((nVec (σ i)) : ℕ))) :
    let τ : Equiv.Perm (Fin (∑ i, ((nVec (σ i)) : ℕ))) := tauOfSigma nVec σ
    let N₂ : ℕ+ := ⟨(∑ i, ((nVec (σ i)) : ℕ)), hpos₂⟩
    let φ_σ : Equiv.Perm (Fin (formatPow d N₂ i)) :=
      (by
        simpa [formatPow] using!
          (powIndexEquiv (d i) N₂).trans
            ((Equiv.arrowCongr τ.symm (Equiv.refl (Fin (d i : ℕ)))).trans
              (powIndexEquiv (d i) N₂).symm))
    powIndexEquiv (d i) N₂ (by simpa [formatPow] using! φ_σ x) j
      = powIndexEquiv (d i) N₂ (by simpa [formatPow] using! x) (τ j) := by
  intro τ N₂ φ_σ
  change powIndexEquiv (d i) N₂
      (id ((powIndexEquiv (d i) N₂).trans
        ((Equiv.arrowCongr τ.symm (Equiv.refl (Fin (d i : ℕ)))).trans
          (powIndexEquiv (d i) N₂).symm)) x) j
      = powIndexEquiv (d i) N₂ x (τ j)
  rw [id_eq, Equiv.trans_apply, Equiv.trans_apply]
  refine Eq.trans (congrFun (Equiv.apply_symm_apply (powIndexEquiv (d i) N₂)
        ((Equiv.arrowCongr τ.symm (Equiv.refl (Fin (d i : ℕ)))) ((powIndexEquiv (d i) N₂) x))) j) ?_
  -- `arrowCongr τ.symm refl g = g ∘ τ.symm.symm = g ∘ τ`, evaluated at `j`.
  show (powIndexEquiv (d i) N₂ x) (τ.symm.symm j) = (powIndexEquiv (d i) N₂ x) (τ j)
  rw [Equiv.symm_symm]

/-- **tprod-family core for Definition 2.1** (after the φ_σ direction fix). When every
    `Ts i = tprod (w i)`, both `tensorPowerBlock` calls flatten to single
    `tprod`s (`tensorPowerBlock_tprod_family`), `regroupingMap_tprod_apply`
    evaluates each as a product of leaf factors, and the two products are matched
    leaf-by-leaf by the block bijection `τ = tauOfSigma nVec σ` via
    `tauOfSigma_finSigmaFinEquiv` (block action `⟨a,b⟩ ↦ ⟨σ a, b⟩`) and the
    digit action `powIndexEquiv_φ_σ` (`φ_σ` reindexes digits by `τ`). -/
private lemma regroupingMap_tensorPowerBlock_perm_eq_legPerm_tauOfSigma_tprod
    {k : ℕ} (d : Fin k → ℕ+)
    {ℓ : ℕ} (nVec : Fin (ℓ + 1) → ℕ+) (σ : Equiv.Perm (Fin (ℓ + 1)))
    (w : ∀ i : Fin (ℓ + 1), Fin (nVec i : ℕ) → KTensor F d)
    (hpos₁ : 0 < ∑ i, (nVec i : ℕ))
    (hpos₂ : 0 < ∑ i, ((nVec (σ i)) : ℕ)) :
    let τ : Equiv.Perm (Fin (∑ i, ((nVec (σ i)) : ℕ))) := tauOfSigma nVec σ
    let N₂ : ℕ+ := ⟨(∑ i, ((nVec (σ i)) : ℕ)), hpos₂⟩
    let φ_σ : ∀ i : Fin k, Equiv.Perm (Fin (formatPow d N₂ i)) :=
      fun i =>
        (by
          simpa [formatPow] using!
            (powIndexEquiv (d i) N₂).trans
              ((Equiv.arrowCongr τ.symm (Equiv.refl (Fin (d i : ℕ)))).trans
                (powIndexEquiv (d i) N₂).symm))
    ∀ jdx : ∀ i : Fin k, Fin (formatPow d N₂ i),
      (((formatPow_block_perm_eq d nVec σ hpos₁ hpos₂) ▸
        regroupingMap d ⟨_, hpos₁⟩
          (tensorPowerBlock F (KTensor F d) (fun i => (nVec i : ℕ))
            (fun i => PiTensorProduct.tprod F (w i)))) jdx)
      =
      (KTensor.legPerm
        (regroupingMap d N₂
          (tensorPowerBlock F (KTensor F d) (fun i => ((nVec (σ i)) : ℕ))
            (fun i => PiTensorProduct.tprod F ((w (σ i)) : Fin (nVec (σ i) : ℕ) → KTensor F d))))
        φ_σ) jdx := by
  intro τ N₂ φ_σ jdx
  classical
  -- LHS flat: `flatL (finSigmaFinEquiv ⟨a,b⟩) = w a b`.
  set flatL : Fin (∑ i, (nVec i : ℕ)) → KTensor F d :=
    fun p => w (finSigmaFinEquiv.symm p).1 (finSigmaFinEquiv.symm p).2 with hflatL
  have hLblock : tensorPowerBlock F (KTensor F d) (fun i => (nVec i : ℕ))
        (fun i => PiTensorProduct.tprod F (w i)) = PiTensorProduct.tprod F flatL := by
    refine tensorPowerBlock_tprod_family (F := F) (fun i => (nVec i : ℕ)) w flatL ?_
    intro s
    rw [hflatL]
    change w (finSigmaFinEquiv.symm (finSigmaFinEquiv s)).fst
        (finSigmaFinEquiv.symm (finSigmaFinEquiv s)).snd = _
    rw [Equiv.symm_apply_apply]
  -- RHS flat: `flatR (finSigmaFinEquiv ⟨a,b⟩) = w (σ a) b`.
  set flatR : Fin (∑ i, (nVec (σ i) : ℕ)) → KTensor F d :=
    fun p => w (σ (finSigmaFinEquiv.symm p).1) (finSigmaFinEquiv.symm p).2 with hflatR
  have hRblock : tensorPowerBlock F (KTensor F d) (fun i => (nVec (σ i) : ℕ))
        (fun i => PiTensorProduct.tprod F (w (σ i))) = PiTensorProduct.tprod F flatR := by
    refine tensorPowerBlock_tprod_family (F := F) (fun i => (nVec (σ i) : ℕ))
      (fun i => w (σ i)) flatR ?_
    intro s
    rw [hflatR]
    change w (σ (finSigmaFinEquiv.symm (finSigmaFinEquiv s)).fst)
        (finSigmaFinEquiv.symm (finSigmaFinEquiv s)).snd = _
    rw [Equiv.symm_apply_apply]
  -- Rewrite both blocks as single tprods.
  rw [hLblock, hRblock]
  -- LHS: push the format cast through the index argument, then expand regroupingMap on a tprod.
  set hfmt := formatPow_block_perm_eq d nVec σ hpos₁ hpos₂ with hfmt_def
  rw [KTensor_cast_apply hfmt]
  -- Name the cast-back index `jL := hfmt.symm ▸ jdx` (opaque, to unblock `rw`).
  generalize hjL : (Eq.rec (motive := fun x h => (i : Fin k) → Fin ↑(x i)) jdx hfmt.symm
      : ∀ i : Fin k, Fin ↑(formatPow d ⟨_, hpos₁⟩ i)) = jL
  -- Expand both regroupingMaps on tprods into products of leaf factors.
  have hL := regroupingMap_tprod_apply d ⟨∑ i, (nVec i : ℕ), hpos₁⟩ flatL jL
  have hR := regroupingMap_tprod_apply d N₂ flatR (fun i => φ_σ i (jdx i))
  refine hL.trans ?_
  refine Eq.trans ?_ hR.symm
  -- Now: `∏ j₁, flatL j₁ (sliceFun .. jL j₁) = ∏ j₂, flatR j₂ (sliceFun .. (φ_σ • jdx) j₂)`.
  -- Reindex the RHS product over `Fin N₂` to `Fin N₁` via `e' j₂ = finCongr h.symm (τ j₂)`.
  -- For `j₂ = finSigmaFinEquiv ⟨a, b⟩` (b in block `σ a`), `τ j₂ = finCongr h (finSigmaFinEquiv ⟨σ a, b⟩)`,
  -- so `e' j₂ = finSigmaFinEquiv ⟨σ a, b⟩` and `flatL (e' j₂) = w (σ a) b = flatR j₂` — no casts.
  refine (Fintype.prod_equiv
    (τ.trans (finCongr (sum_nVec_perm_eq nVec σ)).symm)
    (fun j₂ => flatR j₂ (sliceFun d N₂ (fun i => φ_σ i (jdx i)) j₂))
    (fun j₁ => flatL j₁ (sliceFun d ⟨∑ i, (nVec i : ℕ), hpos₁⟩ jL j₁)) ?_).symm
  intro j₂
  -- Decompose `j₂ = finSigmaFinEquiv ⟨a, b⟩` (b in block `σ a` of the `nVec∘σ` ordering).
  obtain ⟨⟨a, b⟩, rfl⟩ : ∃ s : (i : Fin (ℓ + 1)) × Fin ((nVec (σ i) : ℕ)),
      finSigmaFinEquiv s = j₂ := ⟨finSigmaFinEquiv.symm j₂, by simp⟩
  -- `e' j₂ = finCongr h.symm (τ (finSigmaFinEquiv ⟨a,b⟩)) = finSigmaFinEquiv ⟨σ a, b⟩`.
  have hej : (finCongr (sum_nVec_perm_eq nVec σ)).symm
        (τ (finSigmaFinEquiv (n := fun i => (nVec (σ i) : ℕ)) ⟨a, b⟩))
      = finSigmaFinEquiv (n := fun i => (nVec i : ℕ)) ⟨σ a, b⟩ := by
    rw [tauOfSigma_finSigmaFinEquiv nVec σ a b]
    simp
  simp only [Equiv.trans_apply, Equiv.symm_symm, finCongr_symm, finCongr_apply,
    Equiv.symm_apply_apply] at hej ⊢
  rw [hej]
  -- Both flat tensors are `w (σ a) b` (no casts). Reduce to the slice argument equality.
  simp only [hflatL, hflatR, Equiv.symm_apply_apply]
  -- Goal: `w (σ a) b (sliceFun N₂ (φ_σ•jdx) (finSigmaFinEquiv ⟨a,b⟩))
  --       = w (σ a) b (sliceFun N₁ jL (finSigmaFinEquiv ⟨σ a, b⟩))`.
  -- Reduce to the slice-argument equality (the two `w (σ a) b` tensors are identical).
  have hslice : sliceFun d N₂ (fun i => φ_σ i (jdx i))
        (finSigmaFinEquiv (n := fun i => (nVec (σ i) : ℕ)) ⟨a, b⟩)
      = sliceFun d ⟨∑ i, (nVec i : ℕ), hpos₁⟩ jL
        (finSigmaFinEquiv (n := fun i => (nVec i : ℕ)) ⟨σ a, b⟩) := by
    funext i
    apply Fin.ext
    -- RHS digit action: `φ_σ` shifts the position by `τ`.
    rw [show sliceFun d N₂ (fun i => φ_σ i (jdx i))
          (finSigmaFinEquiv (n := fun i => (nVec (σ i) : ℕ)) ⟨a, b⟩) i
        = powIndexEquiv (d i) N₂ (φ_σ i (jdx i))
            (finSigmaFinEquiv (n := fun i => (nVec (σ i) : ℕ)) ⟨a, b⟩) from rfl]
    rw [powIndexEquiv_φ_σ d nVec σ hpos₂ i (jdx i)
        (finSigmaFinEquiv (n := fun i => (nVec (σ i) : ℕ)) ⟨a, b⟩)]
    -- Now: `powIndexEquiv (d i) N₂ (jdx i) (τ (finSigmaFinEquiv ⟨a,b⟩)) = sliceFun N₁ jL (finSigmaFinEquiv ⟨σ a, b⟩) i`.
    -- LHS position `τ (finSigmaFinEquiv ⟨a,b⟩) = finCongr h (finSigmaFinEquiv ⟨σ a, b⟩)`.
    rw [tauOfSigma_finSigmaFinEquiv nVec σ a b]
    show (powIndexEquiv (d i) N₂ (jdx i)
        (finCongr (sum_nVec_perm_eq nVec σ)
          (finSigmaFinEquiv (n := fun i => (nVec i : ℕ)) ⟨σ a, b⟩))).val = _
    rw [show sliceFun d ⟨∑ i, (nVec i : ℕ), hpos₁⟩ jL
          (finSigmaFinEquiv (n := fun i => (nVec i : ℕ)) ⟨σ a, b⟩) i
        = powIndexEquiv (d i) ⟨∑ i, (nVec i : ℕ), hpos₁⟩
            (by simpa [formatPow] using! jL i)
            (finSigmaFinEquiv (n := fun i => (nVec i : ℕ)) ⟨σ a, b⟩) from rfl]
    -- Both digits agree by `powIndexEquiv_val_congr`: equal exponent vals, equal index vals,
    -- equal positions (the `finCongr`/cast only change types, not `Nat`-values).
    refine powIndexEquiv_val_congr (d i)
      (sum_nVec_perm_eq nVec σ).symm ?_ ?_
    · -- `(jdx i).val = (jL i).val` (cast over equal-valued formats).
      have := val_eq_rec_pi_fin hfmt.symm jdx i
      simp only [hjL] at this ⊢
      -- `jL = hfmt.symm ▸ jdx`, so `(jL i).val = (jdx i).val`.
      rw [← hjL]
      exact (val_eq_rec_pi_fin hfmt.symm jdx i).symm
    · -- position vals agree (finCongr preserves `.val`).
      simp [finCongr_apply, Fin.val_cast]
  rw [hslice]
  -- The two `w (σ a) b` tensors are identical (`finSigmaFinEquiv.symm ∘ finSigmaFinEquiv = id`).
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]

/-- **Two multilinear maps on tensor-power slots agreeing on all tprod-families
    are equal** (Definition 2.1). The slots `TensorPower F (m i) W` are
    spanned by `tprod`s, so a multilinear map is determined by its values on
    families `fun i => tprod (w i)`. Proved by induction on the number of slots,
    peeling slot 0 via `PiTensorProduct.induction_on`. -/
private lemma multilinearMap_eq_of_tprod {W : Type*} [AddCommGroup W] [Module F W]
    {Z : Type*} [AddCommGroup Z] [Module F Z] :
    ∀ {ℓ : ℕ} (m : Fin ℓ → ℕ)
      (M₁ M₂ : MultilinearMap F (fun i : Fin ℓ => TensorPower F (m i) W) Z),
      (∀ w : ∀ i : Fin ℓ, Fin (m i) → W,
        M₁ (fun i => PiTensorProduct.tprod F (w i))
          = M₂ (fun i => PiTensorProduct.tprod F (w i))) →
      ∀ Ts : ∀ i : Fin ℓ, TensorPower F (m i) W, M₁ Ts = M₂ Ts
  | 0, m, M₁, M₂, htprod => fun Ts => by
      have h := htprod (fun i => i.elim0)
      have hTs : Ts = (fun i => PiTensorProduct.tprod F ((fun i => i.elim0) i)) := by
        funext i; exact i.elim0
      rw [hTs]; exact h
  | ℓ + 1, m, M₁, M₂, htprod => fun Ts => by
      classical
      -- Rewrite `Ts = Fin.cons (Ts 0) (Fin.tail Ts)` and curry slot 0.
      rw [← Fin.cons_self_tail Ts]
      rw [← MultilinearMap.curryLeft_apply, ← MultilinearMap.curryLeft_apply]
      -- Induct on the head `Ts 0`.
      induction (Ts 0) using PiTensorProduct.induction_on with
      | smul_tprod r u =>
          rw [map_smul, map_smul, MultilinearMap.smul_apply, MultilinearMap.smul_apply]
          -- On `tprod u`, the two tail multilinear maps agree by the IH.
          congr 1
          refine multilinearMap_eq_of_tprod (fun i => m i.succ)
            (M₁.curryLeft (PiTensorProduct.tprod F u))
            (M₂.curryLeft (PiTensorProduct.tprod F u)) ?_ (Fin.tail Ts)
          intro w'
          simp only [MultilinearMap.curryLeft_apply]
          -- `Fin.cons (tprod u) (fun i => tprod (w' i)) = fun i => tprod ((Fin.cons u w' : ∀ i : Fin (ℓ + 1), Fin (m i) → W) i)`.
          have hcons : (Fin.cons (PiTensorProduct.tprod F u)
                (fun i => PiTensorProduct.tprod F (w' i))
              : ∀ i : Fin (ℓ + 1), TensorPower F (m i) W)
              = fun i => PiTensorProduct.tprod F ((Fin.cons u w' : ∀ i : Fin (ℓ + 1), Fin (m i) → W) i) := by
            funext i
            refine Fin.cases ?_ ?_ i
            · simp [Fin.cons_zero]
            · intro i'; simp [Fin.cons_succ]
          rw [hcons]
          exact htprod ((Fin.cons u w' : ∀ i : Fin (ℓ + 1), Fin (m i) → W))
      | add x y hx hy =>
          rw [map_add, map_add, MultilinearMap.add_apply, MultilinearMap.add_apply, hx, hy]

/-- **Slot-reindexing of a multilinear map along a permutation** (Definition 2.1(iii)). Given `M : MultilinearMap F (fun i => P i) Z` and a permutation
    `e` of the (finite) index, produces a multilinear map on the reindexed slot
    family `fun i => P (e i)`, by precomposing with the dependent reindexing
    equiv `(Equiv.piCongrLeft' P e.symm).symm`. The `map_update_*` fields are the
    dependent `Function.piCongrLeft'_symm_update` lemmas. -/
noncomputable def multilinearReindex {n : ℕ}
    {P : Fin n → Type*} [∀ i, AddCommGroup (P i)] [∀ i, Module F (P i)]
    {Z : Type*} [AddCommGroup Z] [Module F Z]
    (e : Equiv.Perm (Fin n))
    (M : MultilinearMap F (fun i => P i) Z) :
    MultilinearMap F (fun i => P (e i)) Z where
  toFun Us := M ((Equiv.piCongrLeft' P e.symm).symm Us)
  map_update_add' := by
    intro inst Us j x y
    have hinst : inst = instDecidableEqFin n := Subsingleton.elim _ _
    subst hinst
    rw [Function.piCongrLeft'_symm_update (P := P) e.symm Us j (x + y),
        Function.piCongrLeft'_symm_update (P := P) e.symm Us j x,
        Function.piCongrLeft'_symm_update (P := P) e.symm Us j y,
        M.map_update_add]
  map_update_smul' := by
    intro inst Us j c x
    have hinst : inst = instDecidableEqFin n := Subsingleton.elim _ _
    subst hinst
    rw [Function.piCongrLeft'_symm_update (P := P) e.symm Us j (c • x),
        Function.piCongrLeft'_symm_update (P := P) e.symm Us j x,
        M.map_update_smul]

@[simp] lemma multilinearReindex_apply {n : ℕ}
    {P : Fin n → Type*} [∀ i, AddCommGroup (P i)] [∀ i, Module F (P i)]
    {Z : Type*} [AddCommGroup Z] [Module F Z]
    (e : Equiv.Perm (Fin n))
    (M : MultilinearMap F (fun i => P i) Z) (Us : ∀ i, P (e i)) :
    multilinearReindex (F := F) e M Us = M ((Equiv.piCongrLeft' P e.symm).symm Us) := rfl

/-- The reindexing equiv sends a `σ`-shifted family back to the original
    (Definition 2.1): `(piCongrLeft' P σ.symm).symm (fun i => Ts (σ i)) = Ts`. -/
lemma piCongrLeft'_symm_comp_perm {n : ℕ} {P : Fin n → Type*}
    (σ : Equiv.Perm (Fin n)) (Ts : ∀ i, P i) :
    (Equiv.piCongrLeft' P σ.symm).symm (fun i => Ts (σ i)) = Ts := by
  rw [Equiv.symm_apply_eq]
  funext b
  rw [Equiv.piCongrLeft'_apply]
  simp

/-- **Reindexing a tprod-family of `TensorPower`s** (Definition 2.1): the
    dependent reindex `(piCongrLeft' P σ.symm).symm` of a tprod-family
    `fun i => tprod (w i)` (with `P i = ⨂[F]^(nVec i) W`) is again a tprod-family,
    of the `Fin.cast`-reindexed leaf vectors. -/
lemma piCongrLeft'_symm_tprod_reindex {n : ℕ}
    {W : Type*} [AddCommGroup W] [Module F W]
    (nVec : Fin n → ℕ) (σ : Equiv.Perm (Fin n)) (w : ∀ i, Fin (nVec (σ i)) → W)
    (hcast : ∀ i, nVec (σ (σ.symm i)) = nVec i) :
    (Equiv.piCongrLeft' (fun i => (⨂[F]^(nVec i) W)) σ.symm).symm
        (fun i => PiTensorProduct.tprod F (w i))
      = fun i => PiTensorProduct.tprod F
          (fun a => w (σ.symm i) (Fin.cast (hcast i).symm a)) := by
  have gen : ∀ (p q : Fin n) (hpq : p = q) (b : Fin (nVec (σ q)))
      (hc : nVec (σ q) = nVec (σ p)), w q b ≍ w p (Fin.cast hc b) := by
    intro p q hpq b hc; subst hpq; rw [Fin.cast_eq_self]
  rw [Equiv.symm_apply_eq]
  funext i
  rw [Equiv.piCongrLeft'_apply]
  simp only [Equiv.symm_symm]
  obtain ⟨j, rfl⟩ : ∃ j, σ.symm j = i := ⟨σ i, σ.symm_apply_apply i⟩
  refine congrArg (PiTensorProduct.tprod F) ?_
  apply eq_of_heq
  apply Function.hfunext rfl
  intro a a' ha
  rw [eq_of_heq ha]
  exact gen (σ.symm (σ (σ.symm j))) (σ.symm j) (by rw [Equiv.apply_symm_apply]) a' _

/-- **Fixed-τ scalar core for Definition 2.1**.

    This is the narrowly isolated combinatorial step left after the caller has
    specialized the digit permutation to `tauOfSigma nVec σ`. It expands the
    recursive `tensorPowerBlock` at successor length and matches the resulting
    `regroupingMap` Kronecker factors by the block reindexing encoded in
    `tauOfSigma`. -/
lemma regroupingMap_tensorPowerBlock_perm_eq_legPerm_tauOfSigma_pointwise
    {k : ℕ} (d : Fin k → ℕ+)
    {ℓ : ℕ} (nVec : Fin (ℓ + 1) → ℕ+) (σ : Equiv.Perm (Fin (ℓ + 1)))
    (Ts : ∀ i : Fin (ℓ + 1), TensorPower F (nVec i : ℕ) (KTensor F d))
    (hpos₁ : 0 < ∑ i, (nVec i : ℕ))
    (hpos₂ : 0 < ∑ i, ((nVec (σ i)) : ℕ)) :
    let τ : Equiv.Perm (Fin (∑ i, ((nVec (σ i)) : ℕ))) := tauOfSigma nVec σ
    let N₂ : ℕ+ := ⟨(∑ i, ((nVec (σ i)) : ℕ)), hpos₂⟩
    let φ_σ : ∀ i : Fin k, Equiv.Perm (Fin (formatPow d N₂ i)) :=
      fun i =>
        (by
          simpa [formatPow] using!
            (powIndexEquiv (d i) N₂).trans
              ((Equiv.arrowCongr τ.symm (Equiv.refl (Fin (d i : ℕ)))).trans
                (powIndexEquiv (d i) N₂).symm))
    ∀ jdx : ∀ i : Fin k, Fin (formatPow d N₂ i),
      (((formatPow_block_perm_eq d nVec σ hpos₁ hpos₂) ▸
        regroupingMap d ⟨_, hpos₁⟩
          (tensorPowerBlock F (KTensor F d) (fun i => (nVec i : ℕ)) Ts)) jdx)
      =
      (KTensor.legPerm
        (regroupingMap d N₂
          (tensorPowerBlock F (KTensor F d) (fun i => ((nVec (σ i)) : ℕ))
            (fun i => Ts (σ i))))
        φ_σ) jdx := by
  intro τ N₂ φ_σ jdx
  classical
  set hfmt := formatPow_block_perm_eq d nVec σ hpos₁ hpos₂ with hfmt_def
  -- Slot family for the common domain: `fun i => TensorPower (nVec (σ i)) (KTensor F d)`.
  -- `M₂` (RHS) is built directly from `tensorPowerBlockMulti (nVec∘σ)`;
  -- `M₁` (LHS) reindexes `tensorPowerBlockMulti nVec` along `σ`.
  -- Both are the SAME `MultilinearMap F (fun i => TensorPower (nVec (σ i)) _) F`.
  -- RHS linear functional: evaluate the regrouped tensor at `legPerm`-shifted index.
  let L₂ : KTensor F (formatPow d N₂) →ₗ[F] F :=
    LinearMap.proj (fun i => φ_σ i (jdx i))
  -- LHS linear functional: cast format then evaluate at `jdx`.
  let L₁ : KTensor F (formatPow d ⟨_, hpos₁⟩) →ₗ[F] F :=
    LinearMap.proj (hfmt.symm ▸ jdx)
  -- The two multilinear maps over the common slot family.
  let M₂ : MultilinearMap F
      (fun i : Fin (ℓ + 1) => TensorPower F (nVec (σ i) : ℕ) (KTensor F d)) F :=
    (L₂.comp (regroupingMap d N₂)).compMultilinearMap
      (tensorPowerBlockMulti (F := F) (V := KTensor F d) (fun i => (nVec (σ i) : ℕ)))
  let M₁ : MultilinearMap F
      (fun i : Fin (ℓ + 1) => TensorPower F (nVec (σ i) : ℕ) (KTensor F d)) F :=
    (L₁.comp (regroupingMap d ⟨_, hpos₁⟩)).compMultilinearMap
      (multilinearReindex (F := F) σ
        (tensorPowerBlockMulti (F := F) (V := KTensor F d) (fun i => (nVec i : ℕ))))
  -- Rewrite the bare `Ts` in the LHS block as the σ-reindex of `fun i => Ts (σ i)`,
  -- so the LHS literally has `multilinearReindex` shape (only the LHS occurrence).
  conv_lhs => rw [← piCongrLeft'_symm_comp_perm σ Ts]
  -- Turn `(hfmt ▸ T) jdx` into `T (hfmt.symm ▸ jdx)` so the LHS matches `L₁`.
  rw [KTensor_cast_apply hfmt]
  -- The goal now equals `M₁ (fun i => Ts (σ i)) = M₂ (fun i => Ts (σ i))`.
  show M₁ (fun i => Ts (σ i)) = M₂ (fun i => Ts (σ i))
  -- Reduce to agreement on every tprod-family via `multilinearMap_eq_of_tprod`.
  refine multilinearMap_eq_of_tprod (F := F) (W := KTensor F d)
    (fun i => (nVec (σ i) : ℕ)) M₁ M₂ ?_ (fun i => Ts (σ i))
  intro w
  -- Unfold both multilinear maps on the tprod family `fun i => tprod (w i)`.
  show L₁ (regroupingMap d ⟨_, hpos₁⟩
        (tensorPowerBlock F (KTensor F d) (fun i => (nVec i : ℕ))
          ((Equiv.piCongrLeft' (fun i => TensorPower F (nVec i : ℕ) (KTensor F d)) σ.symm).symm
            (fun i => PiTensorProduct.tprod F (w i)))))
      = L₂ (regroupingMap d N₂
        (tensorPowerBlock F (KTensor F d) (fun i => (nVec (σ i) : ℕ))
          (fun i => PiTensorProduct.tprod F (w i))))
  -- The reindexed tprod-family is again a tprod-family of cast leaf-vectors.
  -- Define `w'' i := w (σ.symm i) ∘ Fin.cast (over nVec (σ (σ.symm i)) = nVec i)`.
  have hcast : ∀ i, (nVec (σ (σ.symm i)) : ℕ) = (nVec i : ℕ) := by
    intro i; rw [σ.apply_symm_apply]
  set w'' : ∀ i : Fin (ℓ + 1), Fin (nVec i : ℕ) → KTensor F d :=
    fun i => fun a => w (σ.symm i) (Fin.cast (hcast i).symm a) with hw''_def
  have hreindex :
      (Equiv.piCongrLeft' (fun i => TensorPower F (nVec i : ℕ) (KTensor F d)) σ.symm).symm
        (fun i => PiTensorProduct.tprod F (w i))
      = fun i => PiTensorProduct.tprod F (w'' i) :=
    piCongrLeft'_symm_tprod_reindex (F := F) (W := KTensor F d)
      (fun i => (nVec i : ℕ)) σ w hcast
  rw [hreindex]
  -- Now LHS uses `tensorPowerBlock nVec (fun i => tprod (w'' i))`, matching the tprod core.
  -- And `w'' (σ i) = w i` (Fin.cast over rfl), so RHS matches too.
  have hw''σ : ∀ i, w'' (σ i) = w i := by
    intro i
    funext a
    simp only [hw''_def]
    -- `w (σ.symm (σ i)) (Fin.cast _ a) = w i a`; the index `σ.symm (σ i) = i`.
    have gen : ∀ (p : Fin (ℓ + 1)) (hpi : p = i) (b : Fin (nVec (σ i) : ℕ))
        (hc : (nVec (σ i) : ℕ) = (nVec (σ p) : ℕ)), w p (Fin.cast hc b) = w i b := by
      intro p hpi b hc; subst hpi; rw [Fin.cast_eq_self]
    exact gen (σ.symm (σ i)) (σ.symm_apply_apply i) a _
  -- Invoke the tprod core (against the CORRECTED φ_σ statement).
  have hcore := regroupingMap_tensorPowerBlock_perm_eq_legPerm_tauOfSigma_tprod
    (F := F) d nVec σ w'' hpos₁ hpos₂
  simp only at hcore
  have hcore_jdx := hcore jdx
  -- Rewrite RHS tprod family `w i` as `w'' (σ i)`.
  conv_rhs => rw [show (fun i => PiTensorProduct.tprod F (w i))
      = (fun i => PiTensorProduct.tprod F (w'' (σ i))) from by funext i; rw [hw''σ]]
  -- `L₁`, `L₂` are exactly the format-cast-eval / legPerm-eval of the core's two sides.
  -- Rewrite the core's `(hfmt ▸ T) jdx` into `T (hfmt.symm ▸ jdx) = L₁ T`, leaving the RHS
  -- `legPerm T φ_σ jdx = T (fun i => φ_σ i (jdx i)) = L₂ T` (defeq).
  rw [KTensor_cast_apply hfmt] at hcore_jdx
  exact hcore_jdx

/-- Pointwise scalar core for the successor step in Definition 2.1.

    This is the remaining combinatorial computation after expanding
    `tensorPowerBlock` at `ℓ + 1`: `TensorPower.mulEquiv` splits the first block
    from the recursive tail, `regroupingMap_tensorPowerAdd_symm_eq_kron_cast`
    rewrites the regrouping as a Kronecker product, and the block/digit
    permutation `τ := tauOfSigma nVec σ` reindexes the scalar factors uniformly in every leg. -/
lemma regroupingMap_tensorPowerBlock_perm_eq_legPerm_for_tau_induction_step_pointwise
    {k : ℕ} (d : Fin k → ℕ+)
    {ℓ : ℕ} (nVec : Fin (ℓ + 1) → ℕ+) (σ : Equiv.Perm (Fin (ℓ + 1)))
    (Ts : ∀ i : Fin (ℓ + 1), TensorPower F (nVec i : ℕ) (KTensor F d))
    (hpos₁ : 0 < ∑ i, (nVec i : ℕ))
    (hpos₂ : 0 < ∑ i, ((nVec (σ i)) : ℕ))
    (τ : Equiv.Perm (Fin (∑ i, ((nVec (σ i)) : ℕ))))
    (hτ : τ = tauOfSigma nVec σ) :
    let N₂ : ℕ+ := ⟨(∑ i, ((nVec (σ i)) : ℕ)), hpos₂⟩
    let φ_σ : ∀ i : Fin k, Equiv.Perm (Fin (formatPow d N₂ i)) :=
      fun i =>
        (by
          simpa [formatPow] using!
            (powIndexEquiv (d i) N₂).trans
              ((Equiv.arrowCongr τ.symm (Equiv.refl (Fin (d i : ℕ)))).trans
                (powIndexEquiv (d i) N₂).symm))
    ∀ jdx : ∀ i : Fin k, Fin (formatPow d N₂ i),
      (((formatPow_block_perm_eq d nVec σ hpos₁ hpos₂) ▸
        regroupingMap d ⟨_, hpos₁⟩
          (tensorPowerBlock F (KTensor F d) (fun i => (nVec i : ℕ)) Ts)) jdx)
      =
      (KTensor.legPerm
        (regroupingMap d N₂
          (tensorPowerBlock F (KTensor F d) (fun i => ((nVec (σ i)) : ℕ))
            (fun i => Ts (σ i))))
        φ_σ) jdx := by
  subst τ
  dsimp
  intro jdx
  exact
    regroupingMap_tensorPowerBlock_perm_eq_legPerm_tauOfSigma_pointwise
      (F := F) d nVec σ Ts hpos₁ hpos₂ jdx

lemma regroupingMap_tensorPowerBlock_perm_eq_legPerm_for_tau_induction_step
    {k : ℕ} (d : Fin k → ℕ+)
    {ℓ : ℕ} (nVec : Fin (ℓ + 1) → ℕ+) (σ : Equiv.Perm (Fin (ℓ + 1)))
    (Ts : ∀ i : Fin (ℓ + 1), TensorPower F (nVec i : ℕ) (KTensor F d))
    (hpos₁ : 0 < ∑ i, (nVec i : ℕ))
    (hpos₂ : 0 < ∑ i, ((nVec (σ i)) : ℕ))
    (τ : Equiv.Perm (Fin (∑ i, ((nVec (σ i)) : ℕ))))
    (hτ : τ = tauOfSigma nVec σ) :
    let N₂ : ℕ+ := ⟨(∑ i, ((nVec (σ i)) : ℕ)), hpos₂⟩
    let φ_σ : ∀ i : Fin k, Equiv.Perm (Fin (formatPow d N₂ i)) :=
      fun i =>
        (by
          simpa [formatPow] using!
            (powIndexEquiv (d i) N₂).trans
              ((Equiv.arrowCongr τ.symm (Equiv.refl (Fin (d i : ℕ)))).trans
                (powIndexEquiv (d i) N₂).symm))
    ((formatPow_block_perm_eq d nVec σ hpos₁ hpos₂) ▸
      regroupingMap d ⟨_, hpos₁⟩
        (tensorPowerBlock F (KTensor F d) (fun i => (nVec i : ℕ)) Ts))
    =
    KTensor.legPerm
      (regroupingMap d N₂
        (tensorPowerBlock F (KTensor F d) (fun i => ((nVec (σ i)) : ℕ))
          (fun i => Ts (σ i))))
      φ_σ := by
  /- This is the successor case of the structural induction described in the
     surrounding theorem.  The current public helper quantifies over arbitrary
     `τ`; the intended downstream call supplies the block permutation induced by
     `σ`, where this successor case follows by expanding `tensorPowerBlock` and
     using `regroupingMap_tensorPowerAdd_symm_eq_kron_cast`. -/
  funext jdx
  exact
    regroupingMap_tensorPowerBlock_perm_eq_legPerm_for_tau_induction_step_pointwise
      (F := F) d nVec σ Ts hpos₁ hpos₂ τ hτ jdx

/-- **Bedrock combinatorial fact (Definition 2.1)**: the format-cast LHS
    `regroupingMap d ⟨∑ nVec, hpos₁⟩ (tensorPowerBlock F (KTensor F d) nVec Ts)`
    coincides with `RHS.legPerm φ_σ` for some uniform leg-wise digit-permutation
    `φ_σ : ∀ i : Fin k, Equiv.Perm (Fin ((d i)^N))`, where RHS is the
    block-permuted regrouped tensor.

    Definition 2.1 (iii), verbatim:
    `F_{n_1+⋯+n_ℓ}(T_1 ⊗ ⋯ ⊗ T_ℓ) =
    F_{n_1+⋯+n_ℓ}(T_{σ(1)} ⊗ ⋯ ⊗ T_{σ(ℓ)})`.

    The permutation `φ_σ i` realizes the digit-permutation `τ_σ : Fin N ≃ Fin N`
    on `Fin ((d i)^N) ≃ (Fin N → Fin (d i))` (via `powIndexEquiv`) and is the
    *same* across all legs `i` (since `σ` permutes blocks of `Fin N` uniformly).

    **Concretely**: at every multi-index `jdx : ∀ i, Fin (formatPow d ⟨N₂, hpos₂⟩ i)`,
    the LHS visits the factors `u_i(j_i)(sliceFun jdx (posLHS(i,j_i)))` in block
    order `i = 0, 1, ..., ℓ-1` (using `Ts`), while RHS visits
    `u_{σ i}(j_i)(sliceFun jdx (posRHS(i,j_i)))` in block order `i = 0, ..., ℓ-1`
    (using `Ts ∘ σ`). Since both products visit each leaf `(i, j_i)` once, and
    both are `∏` of scalars over a commutative field, the values agree up to a
    permutation of `sliceFun jdx`-positions, which corresponds to leg-wise
    digit-permutation `φ_σ`.

    Stated as a sub-helper: this is the load-bearing combinatorial identity
    that Definition 2.1 leaves implicit. Discharge would require building the
    explicit `τ_σ : Fin N ≃ Fin N` via `finSigmaFinEquiv` + `Equiv.sigmaCongrLeft' σ`
    and a careful induction on `ℓ` matching the recursive `tensorPowerBlock`
    structure. -/
lemma regroupingMap_tensorPowerBlock_perm_eq_legPerm_for_tau
    {k : ℕ} (d : Fin k → ℕ+)
    {ℓ : ℕ} (nVec : Fin ℓ → ℕ+) (σ : Equiv.Perm (Fin ℓ))
    (Ts : ∀ i : Fin ℓ, TensorPower F (nVec i : ℕ) (KTensor F d))
    (hpos₁ : 0 < ∑ i, (nVec i : ℕ))
    (hpos₂ : 0 < ∑ i, ((nVec (σ i)) : ℕ))
    (τ : Equiv.Perm (Fin (∑ i, ((nVec (σ i)) : ℕ))))
    (hτ : τ = tauOfSigma nVec σ) :
    let N₂ : ℕ+ := ⟨(∑ i, ((nVec (σ i)) : ℕ)), hpos₂⟩
    let φ_σ : ∀ i : Fin k, Equiv.Perm (Fin (formatPow d N₂ i)) :=
      fun i =>
        (by
          simpa [formatPow] using!
            (powIndexEquiv (d i) N₂).trans
              ((Equiv.arrowCongr τ.symm (Equiv.refl (Fin (d i : ℕ)))).trans
                (powIndexEquiv (d i) N₂).symm))
    ((formatPow_block_perm_eq d nVec σ hpos₁ hpos₂) ▸
      regroupingMap d ⟨_, hpos₁⟩
        (tensorPowerBlock F (KTensor F d) (fun i => (nVec i : ℕ)) Ts))
    =
    KTensor.legPerm
      (regroupingMap d N₂
        (tensorPowerBlock F (KTensor F d) (fun i => ((nVec (σ i)) : ℕ))
          (fun i => Ts (σ i))))
      φ_σ := by
  /- Definition 2.1 (iii), verbatim:
     "F_{n_1+⋯+n_ℓ}(T_1 ⊗ ⋯ ⊗ T_ℓ) =
      F_{n_1+⋯+n_ℓ}(T_{σ(1)} ⊗ ⋯ ⊗ T_{σ(ℓ)})".

     This focused sub-fact is the remaining pointwise combinatorial computation
     once the permutation of the total tensor-power index has been fixed as
     `τ`.  It says that the `powIndexEquiv` pullback of this `τ`, uniformly in
     every tensor leg, is exactly the leg-wise reindexing relating the two
     regrouped block tensors.  Induction on `ℓ` uses
     the recursive definition of `tensorPowerBlock`, `TensorPower.mulEquiv`,
     `TensorPower.tprod_mul_tprod`, and `regroupingMap_tprod_apply`. -/
  cases ℓ with
  | zero =>
      exfalso
      simpa using! hpos₁
  | succ ℓ =>
      exact regroupingMap_tensorPowerBlock_perm_eq_legPerm_for_tau_induction_step
        (F := F) d nVec σ Ts hpos₁ hpos₂ τ hτ

lemma regroupingMap_tensorPowerBlock_perm_eq_legPerm
    {k : ℕ} (d : Fin k → ℕ+)
    {ℓ : ℕ} (nVec : Fin ℓ → ℕ+) (σ : Equiv.Perm (Fin ℓ))
    (Ts : ∀ i : Fin ℓ, TensorPower F (nVec i : ℕ) (KTensor F d))
    (hpos₁ : 0 < ∑ i, (nVec i : ℕ))
    (hpos₂ : 0 < ∑ i, ((nVec (σ i)) : ℕ)) :
    ∃ φ_σ : ∀ i : Fin k, Equiv.Perm (Fin (formatPow d
        ⟨(∑ i, ((nVec (σ i)) : ℕ)), hpos₂⟩ i)),
      ((formatPow_block_perm_eq d nVec σ hpos₁ hpos₂) ▸
        regroupingMap d ⟨_, hpos₁⟩
          (tensorPowerBlock F (KTensor F d) (fun i => (nVec i : ℕ)) Ts))
      =
      KTensor.legPerm
        (regroupingMap d ⟨_, hpos₂⟩
          (tensorPowerBlock F (KTensor F d) (fun i => ((nVec (σ i)) : ℕ))
            (fun i => Ts (σ i))))
        φ_σ := by
  let τ : Equiv.Perm (Fin (∑ i, ((nVec (σ i)) : ℕ))) := tauOfSigma nVec σ
  let N₂ : ℕ+ := ⟨(∑ i, ((nVec (σ i)) : ℕ)), hpos₂⟩
  let φ_σ : ∀ i : Fin k, Equiv.Perm (Fin (formatPow d N₂ i)) :=
    fun i =>
      (by
        simpa [formatPow, N₂] using!
          (powIndexEquiv (d i) N₂).trans
            ((Equiv.arrowCongr τ.symm (Equiv.refl (Fin (d i : ℕ)))).trans
              (powIndexEquiv (d i) N₂).symm))
  refine ⟨φ_σ, ?_⟩
  simpa [N₂, φ_σ, τ] using!
    regroupingMap_tensorPowerBlock_perm_eq_legPerm_for_tau
      (F := F) d nVec σ Ts hpos₁ hpos₂ τ rfl

/-- **Structural rank-equality (Definition 2.1 (iii))**:
    after format-casting the LHS to the RHS's output format, the regrouped
    `tensorPowerBlock F (KTensor F d) (fun i => nVec i) Ts` has the same
    tensor rank as the regrouped block-permuted version
    `tensorPowerBlock F (KTensor F d) (fun i => nVec (σ i)) (Ts ∘ σ)`.

    Definition 2.1(iii):
    `F_{n_1+⋯+n_ℓ}(T_1 ⊗ ⋯ ⊗ T_ℓ) = F_{n_1+⋯+n_ℓ}(T_{σ(1)} ⊗ ⋯ ⊗ T_{σ(ℓ)})`.

    At the `ℕ` rank level, this expresses that the iterated Kronecker product
    `(regroupingMap d (nVec 1) (Ts 1)) ⊠ ⋯ ⊠ (regroupingMap d (nVec ℓ) (Ts ℓ))`
    has the same tensor rank as its block-permuted analogue, modulo the
    multi-index reindexing induced on `Fin ((d i)^(∑ nVec))` legs by the block
    permutation. Since `∏_j u_j(idx j)` is symmetric in `j`, this reindexing
    preserves the simple-tensor decomposition data hence preserves tensor rank.

    **Proof structure**: The two regrouped tensors live in the same `KTensor`
    type (after the format cast `formatPow_block_perm_eq`). They are related by
    a uniform leg-wise permutation `φ : ∀ i, Equiv.Perm (Fin (formatPow d ⟨N₂,
    hpos₂⟩ i))` — the digit-permutation on each leg's `Fin ((d i)^N₂)` induced
    by the block permutation `σ`. By `tensorRank_legPerm_eq` (above), this
    leg-wise reindexing preserves tensor rank.

    The bedrock combinatorial fact — that LHS = RHS.legPerm φ_σ for an
    explicit uniform `φ_σ` — is isolated as the sub-helper
    `regroupingMap_tensorPowerBlock_perm_eq_legPerm` below.

    Requires `1 ≤ k` (downstream consumer `tensorRank_regroupingMap_block_perm`
    has `_hk : 1 ≤ k`). -/
lemma tensorRank_regroupingMap_block_perm_aux {k : ℕ} (hk : 1 ≤ k) (d : Fin k → ℕ+)
    {ℓ : ℕ} (nVec : Fin ℓ → ℕ+) (σ : Equiv.Perm (Fin ℓ))
    (Ts : ∀ i : Fin ℓ, TensorPower F (nVec i : ℕ) (KTensor F d))
    (hpos₁ : 0 < ∑ i, (nVec i : ℕ))
    (hpos₂ : 0 < ∑ i, ((nVec (σ i)) : ℕ)) :
    tensorRank
      ((formatPow_block_perm_eq d nVec σ hpos₁ hpos₂) ▸
        regroupingMap d ⟨_, hpos₁⟩
          (tensorPowerBlock F (KTensor F d) (fun i => (nVec i : ℕ)) Ts))
      =
    tensorRank
      (regroupingMap d ⟨_, hpos₂⟩
        (tensorPowerBlock F (KTensor F d) (fun i => ((nVec (σ i)) : ℕ))
          (fun i => Ts (σ i)))) := by
  -- Set the format-cast LHS and the RHS as the two `KTensor F (formatPow d ⟨N₂, hpos₂⟩)`
  -- elements to compare. By the bedrock fact, LHS = RHS.legPerm φ_σ for some uniform φ_σ.
  -- Then `tensorRank_legPerm_eq` gives `tensorRank LHS = tensorRank RHS`.
  set RHS : KTensor F (formatPow d ⟨(∑ i, ((nVec (σ i)) : ℕ)), hpos₂⟩) :=
    regroupingMap d ⟨_, hpos₂⟩
      (tensorPowerBlock F (KTensor F d) (fun i => ((nVec (σ i)) : ℕ))
        (fun i => Ts (σ i))) with hRHS_def
  -- The bedrock fact (Definition 2.1): LHS = RHS.legPerm φ_σ for a uniform leg-wise
  -- digit-permutation `φ_σ` derived from `σ : Equiv.Perm (Fin ℓ)`.
  obtain ⟨φ_σ, hLHS_eq⟩ := regroupingMap_tensorPowerBlock_perm_eq_legPerm
    (F := F) d nVec σ Ts hpos₁ hpos₂
  rw [hLHS_eq]
  exact tensorRank_legPerm_eq (F := F) hk RHS φ_σ

/--
**Helper (`regroupingMap` permutation invariance at the `ℕ` rank level)**:
    permuting the block factors before regrouping preserves tensor rank.

    Definition 2.1(iii):
    `F_{n_1+⋯+n_ℓ}(T_1 ⊗ ⋯ ⊗ T_ℓ) = F_{n_1+⋯+n_ℓ}(T_{σ(1)} ⊗ ⋯ ⊗ T_{σ(ℓ)})`.

    Proof structure:
    1. Format-cast preserves rank (`tensorRank_format_cast` applied to
       `formatPow_block_perm_eq`).
    2. After the cast, both regrouped tensors live in the same `KTensor` type
       and have equal tensor rank by the named structural identity
       `tensorRank_regroupingMap_block_perm_aux` (the rank-level content of
       Definition 2.1).
-/
lemma tensorRank_regroupingMap_block_perm {k : ℕ} (hk : 1 ≤ k) (d : Fin k → ℕ+)
    {ℓ : ℕ} (nVec : Fin ℓ → ℕ+) (σ : Equiv.Perm (Fin ℓ))
    (Ts : ∀ i : Fin ℓ, TensorPower F (nVec i : ℕ) (KTensor F d))
    (hpos₁ : 0 < ∑ i, (nVec i : ℕ))
    (hpos₂ : 0 < ∑ i, ((nVec (σ i)) : ℕ)) :
    tensorRank
      (regroupingMap d ⟨_, hpos₁⟩
        (tensorPowerBlock F (KTensor F d) (fun i => (nVec i : ℕ)) Ts))
      =
    tensorRank
      (regroupingMap d ⟨_, hpos₂⟩
        (tensorPowerBlock F (KTensor F d) (fun i => ((nVec (σ i)) : ℕ))
          (fun i => Ts (σ i)))) := by
  -- Step 1: format-cast preserves rank.
  set hfmt := formatPow_block_perm_eq d nVec σ hpos₁ hpos₂
  set LHS := regroupingMap d ⟨_, hpos₁⟩
        (tensorPowerBlock F (KTensor F d) (fun i => (nVec i : ℕ)) Ts)
  rw [show tensorRank LHS = tensorRank (hfmt ▸ LHS) from
    (tensorRank_format_cast (F := F) hfmt LHS).symm]
  -- Step 2: rank-level Definition 2.1 — block-perm preserves rank after cast.
  exact tensorRank_regroupingMap_block_perm_aux (F := F) hk d nVec σ Ts hpos₁ hpos₂

/-- The canonical asymptotic-tensor-rank admissible functional on `KTensor F d`.
    Concrete construction is in `Tensors/Semicontinuity/TensorRank.lean` (5 axioms
    to verify): `simpleTensor` + `tensorRank` + iterated Kronecker `regroupingMap`,
    then subadd/submul/perm_inv/scalar_inv/F_1-bound. -/
lemma tensorRankAdmissible_submul {k : ℕ} (hk : 1 ≤ k) (d : Fin k → ℕ+)
    (n n' : ℕ+) (T : TensorPower F (n : ℕ) (KTensor F d))
    (S : TensorPower F (n' : ℕ) (KTensor F d)) :
    ((tensorRank
      (regroupingMap d ⟨(n : ℕ) + (n' : ℕ), Nat.add_pos_left n.pos _⟩
        ((tensorPowerAdd F (KTensor F d) (n : ℕ) (n' : ℕ)).symm (T ⊗ₜ[F] S))) : ℕ) :
        NNReal)
      ≤
    ((tensorRank (regroupingMap d n T) : ℕ) : NNReal) *
      ((tensorRank (regroupingMap d n' S) : ℕ) : NNReal) := by
  exact_mod_cast tensorRank_regroupingMap_add_le (F := F) hk d n n' T S

lemma tensorRankAdmissible_perm_inv {k : ℕ} (hk : 1 ≤ k) (d : Fin k → ℕ+)
    {ℓ : ℕ} (nVec : Fin ℓ → ℕ+) (σ : Equiv.Perm (Fin ℓ))
    (Ts : ∀ i : Fin ℓ, TensorPower F (nVec i : ℕ) (KTensor F d))
    (hpos₁ : 0 < ∑ i, (nVec i : ℕ))
    (hpos₂ : 0 < ∑ i, ((nVec (σ i)) : ℕ)) :
    ((tensorRank
      (regroupingMap d ⟨_, hpos₁⟩
        (tensorPowerBlock F (KTensor F d) (fun i => (nVec i : ℕ)) Ts)) : ℕ) :
        NNReal)
      =
    ((tensorRank
      (regroupingMap d ⟨_, hpos₂⟩
        (tensorPowerBlock F (KTensor F d) (fun i => ((nVec (σ i)) : ℕ))
          (fun i => Ts (σ i)))) : ℕ) : NNReal) := by
  exact_mod_cast tensorRank_regroupingMap_block_perm (F := F) hk d nVec σ Ts hpos₁ hpos₂

noncomputable def tensorRankAdmissible (F : Type u) [Field F]
    {k : ℕ} (hk : 1 ≤ k) (d : Fin k → ℕ+) :
    AdmissibleFunctional F (KTensor F d) where
  toFun n T := ((tensorRank (regroupingMap d n T) : ℕ) : NNReal)
  subadd n T S := by
    change
      ((tensorRank (regroupingMap d n (T + S)) : ℕ) : NNReal) ≤
        ((tensorRank (regroupingMap d n T) : ℕ) : NNReal) +
          ((tensorRank (regroupingMap d n S) : ℕ) : NNReal)
    rw [map_add]
    exact_mod_cast tensorRank_add_le (F := F) hk (regroupingMap d n T) (regroupingMap d n S)
  submul n n' T S :=
    tensorRankAdmissible_submul (F := F) hk d n n' T S
  perm_inv nVec σ Ts hpos₁ hpos₂ :=
    tensorRankAdmissible_perm_inv (F := F) hk d nVec σ Ts hpos₁ hpos₂
  scalar_inv n α hα T := by
    rw [map_smul]
    exact_mod_cast tensorRank_smul_of_ne_zero (F := F) hk α hα (regroupingMap d n T)
  bdd_one := by
    refine ⟨((∏ i, ((formatPow d (1 : ℕ+) i : ℕ))) : NNReal), ?_⟩
    intro T
    exact_mod_cast tensorRank_le_prod_dims (F := F) hk (regroupingMap d (1 : ℕ+) T)

/-- **Asymptotic tensor rank** `R̃(T)` for `T ∈ KTensor F d`. -/
noncomputable def asympRank {k : ℕ} {d : Fin k → ℕ+} (T : KTensor F d) : ℝ :=
  if hk : 1 ≤ k then (tensorRankAdmissible F hk d).regularize T else 0

/-!
### Helper lemmas for Corollary 2.6 -/

/-- `R̃` is non-negative.

Since `R̃(T) = ⨅ n, R(T^{⊠n})^{1/n}` and `R(·) ≥ 0`, the regularization is
non-negative. (Used to bound `⌊r_1⌋ ≥ 0` so the re-embedding format is
well-defined.) -/
lemma asympRank_nonneg {k : ℕ} {d : Fin k → ℕ+} (T : KTensor F d) :
    0 ≤ asympRank T := by
  by_cases hk : 1 ≤ k
  · unfold asympRank
    simp only [dif_pos hk]
    unfold AdmissibleFunctional.regularize
    refine le_ciInf fun n => ?_
    exact Real.rpow_nonneg (NNReal.coe_nonneg _) _
  · simp [asympRank, hk]

/-- **`R̃(0) = 0`** (Corollary 2.6, Cor 2.6 helper; Section 1.4 for `R(0) = 0`).

    The asymptotic rank of the zero tensor is `0`. This is the well-ordering
    floor used in Corollary 2.6: the paper's proof picks concise
    witnesses for the *positive* values `r_i`, and the value `0` is realized in
    any format by the zero tensor — it does not need a concise equivalent.

    Proof: `R̃(0) = ⨅ n, R((0)^{⊠n})^{1/n}`. The `n`-fold Kronecker power
    `tensorPow n 0 = tprod (fun _ => 0)` vanishes (`MultilinearMap.map_coord_zero`,
    using `n ≥ 1`), `regroupingMap` is linear so maps `0 ↦ 0`, and
    `tensorRank 0 = 0` (Section 1.4). Hence each summand is `0^{1/n} = 0`, so the
    infimum is `0` (`ciInf_const`). -/
lemma asympRank_zero {k : ℕ} (d : Fin k → ℕ+) :
    asympRank (0 : KTensor F d) = 0 := by
  by_cases hk : 1 ≤ k
  · unfold asympRank
    simp only [dif_pos hk]
    unfold AdmissibleFunctional.regularize
    -- The level-`n` value `R(regroupingMap d n (tensorPow n 0))` is `0`.
    have hzero : ∀ n : ℕ+,
        ((((tensorRankAdmissible F hk d).toFun n
            (tensorPow (F := F) (V := KTensor F d) n (0 : KTensor F d)) : NNReal) : ℝ))
          ^ ((1 : ℝ) / (n : ℕ)) = 0 := by
      intro n
      -- `tensorPow n 0 = 0` since `tprod` of a family with a zero coordinate is `0`.
      have htp : tensorPow (F := F) (V := KTensor F d) n (0 : KTensor F d) = 0 := by
        unfold tensorPow
        exact MultilinearMap.map_coord_zero
          (PiTensorProduct.tprod F) (i := ⟨0, n.pos⟩) rfl
      -- `toFun n` of the zero power is `R(regroupingMap d n 0) = R(0) = 0`.
      have hval : ((tensorRankAdmissible F hk d).toFun n
          (tensorPow (F := F) (V := KTensor F d) n (0 : KTensor F d)) : NNReal) = 0 := by
        show (((tensorRank (regroupingMap d n
            (tensorPow (F := F) (V := KTensor F d) n (0 : KTensor F d)))) : ℕ) : NNReal) = 0
        rw [htp, map_zero, tensorRank_zero]
        simp
      rw [hval]
      simp only [NNReal.coe_zero]
      exact Real.zero_rpow (by positivity)
    -- The infimum of a constantly-`0` family is `0`.
    rw [show (fun n : ℕ+ =>
        ((((tensorRankAdmissible F hk d).toFun n
            (tensorPow (F := F) (V := KTensor F d) n (0 : KTensor F d)) : NNReal) : ℝ))
          ^ ((1 : ℝ) / (n : ℕ))) = fun _ : ℕ+ => (0 : ℝ) from funext hzero]
    exact ciInf_const
  · simp [asympRank, hk]

/-!
#### Auxiliary lemmas for Corollary 2.6. -/

/-- **Flattening-rank lower bound on tensor rank**.

    In Section 1.3, just before Theorem 1.6, Christandl–Hoeberechts–Nieuwboer–Vrana–Zuiddam write:
    "For any proper subset `I ⊆ [k]`, let
    `tensorrank_I(T)` be the matrix rank of the matrix obtained by grouping the
    legs in `I` together and grouping the remaining legs together. If `i ∈ I`
    and `j ∉ I`, then `tensorrank_I(T) ≥ subrank_{i,j}(T)`."

    The first half of that sentence is the *definition* of `flatRank` (now
    realized in `MaxRankBound.lean` via `flattenMatrix` + `Matrix.rank`).
    Combined with the standard fact `tensorRank T ≥ flatRank T I` (a sum of
    `tensorRank T` simple tensors flattens to a sum of `tensorRank T` rank-≤-1
    matrices), we obtain this inequality.

    Reduction to matrix algebra:
    1. Pick a decomposition `T = ∑_{ℓ=1}^{tensorRank T} simpleTensor u_ℓ`
       (`exists_tensorRank_decomp` from `TensorRank.lean`).
    2. The flattening of a *simple* tensor is the outer product of two
       leg-wise product vectors, hence has matrix rank ≤ 1
       (`Matrix.rank_vecMulVec_le` from
       `Mathlib/LinearAlgebra/Matrix/Rank.lean:185`).
    3. `Matrix.rank` is subadditive (`LinearMap.rank_add_le` from
       `Mathlib/LinearAlgebra/Dimension/LinearMap.lean:87`, transported
       to `Matrix.rank` via `rank_eq_finrank_range_toLin`).

    This is a focused, paper-cited sub-lemma; its matrix-algebra discharge is
    isolated for clarity. Requires `1 ≤ k` to ensure `tensorRank T` is realized
    by a simple-tensor decomposition (`exists_tensorRank_decomp`). -/
lemma flatRank_le_tensorRank {k : ℕ} (hk : 1 ≤ k) {d : Fin k → ℕ+}
    (T : KTensor F d) (I : Finset (Fin k)) :
    flatRank T I ≤ tensorRank T := by
  classical
  -- 1. Pick a simple-tensor decomposition `T = ∑_ℓ s ℓ`, `ℓ : Fin (tensorRank T)`,
  --    with `s ℓ = simpleTensor (u ℓ)`.
  -- 2. Show the column span of `flattenMatrix T I` is contained in the linear span
  --    of the vectors `w ℓ : RowIdx → F`, `w ℓ row := ∏_{i ∈ I} u ℓ i (row ⟨i, _⟩)`.
  -- 3. Apply `finrank_range_le_card` over `Fin (tensorRank T)`.
  -- Pull a decomposition of size `tensorRank T`.
  have hT_mem : tensorRank T ∈
      { r : ℕ | ∃ s : Fin r → KTensor F d,
          (∀ i, IsSimpleTensor (s i)) ∧ T = ∑ i, s i } := by
    apply Nat.sInf_mem
    obtain ⟨rT, sT, hsT, hT⟩ := exists_tensorRank_decomp hk T
    exact ⟨rT, sT, hsT, hT⟩
  obtain ⟨s, hs_simple, hT_decomp⟩ := hT_mem
  choose u hu using hs_simple
  -- Local abbreviations for the row/column index types.
  let RowIdx : Type _ := ∀ i : {i : Fin k // i ∈ I}, Fin (d i.val)
  let ColIdx : Type _ := ∀ j : {j : Fin k // j ∉ I}, Fin (d j.val)
  -- The leg-products restricted to `I`, one per simple summand.
  let w : Fin (tensorRank T) → (RowIdx → F) :=
    fun ℓ row => ∏ i : {i : Fin k // i ∈ I}, u ℓ i.val (row i)
  -- The leg-products restricted to the complement of `I`.
  let v : Fin (tensorRank T) → (ColIdx → F) :=
    fun ℓ col => ∏ j : {j : Fin k // j ∉ I}, u ℓ j.val (col j)
  -- Recombine `(row, col)` to a full multi-index over `Fin k`.
  let combine : RowIdx → ColIdx → ∀ i : Fin k, Fin (d i) :=
    fun row col i => if h : i ∈ I then row ⟨i, h⟩ else col ⟨i, h⟩
  -- Step A: identity at the entry level.
  -- `flattenMatrix T I row col = ∑_ℓ (v ℓ col) * (w ℓ row)`.
  have hentry : ∀ row col,
      flattenMatrix T I row col = ∑ ℓ, v ℓ col * w ℓ row := by
    intro row col
    change T (combine row col) = ∑ ℓ, v ℓ col * w ℓ row
    have hT_app : T (combine row col) =
        ∑ ℓ : Fin (tensorRank T),
          ∏ i : Fin k, u ℓ i (combine row col i) := by
      calc T (combine row col)
          = (∑ ℓ, s ℓ) (combine row col) := by rw [← hT_decomp]
        _ = ∑ ℓ, (s ℓ) (combine row col) := by rw [Finset.sum_apply]
        _ = ∑ ℓ, ∏ i, u ℓ i (combine row col i) := by
            refine Finset.sum_congr rfl ?_
            intro ℓ _
            rw [hu ℓ]; rfl
    rw [hT_app]
    refine Finset.sum_congr rfl ?_
    intro ℓ _
    -- Split the product over `Fin k` into the `I` part and the `Iᶜ` part.
    -- Note: `Fintype` instances on the subtypes could differ between
    -- `Subtype.fintype` and `Finset.Subtype.fintype`; the products are equal
    -- as `Subsingleton`s pick the same value.
    have hsplit :
        ∏ i, u ℓ i (combine row col i) =
          (∏ i : {i : Fin k // i ∈ I}, u ℓ i.val (combine row col i.val)) *
            (∏ j : {j : Fin k // j ∉ I}, u ℓ j.val (combine row col j.val)) := by
      have key := (Fintype.prod_subtype_mul_prod_subtype (p := (· ∈ I))
            (f := fun i => u ℓ i (combine row col i))).symm
      convert! key using 4
      all_goals exact Subsingleton.elim _ _
    -- Simplify each factor.
    have hI_part :
        (∏ i : {i : Fin k // i ∈ I}, u ℓ i.val (combine row col i.val)) = w ℓ row := by
      refine Finset.prod_congr rfl ?_
      intro i _
      change u ℓ i.val (combine row col i.val) = u ℓ i.val (row i)
      have : combine row col i.val = row i := by
        change (if h : i.val ∈ I then row ⟨i.val, h⟩ else col ⟨i.val, h⟩) = row i
        rw [dif_pos i.prop]
      rw [this]
    have hIc_part :
        (∏ j : {j : Fin k // j ∉ I}, u ℓ j.val (combine row col j.val)) = v ℓ col := by
      refine Finset.prod_congr rfl ?_
      intro j _
      change u ℓ j.val (combine row col j.val) = u ℓ j.val (col j)
      have : combine row col j.val = col j := by
        change (if h : j.val ∈ I then row ⟨j.val, h⟩ else col ⟨j.val, h⟩) = col j
        rw [dif_neg j.prop]
      rw [this]
    rw [hsplit, hI_part, hIc_part, mul_comm]
  -- Step B: rewrite `flatRank` via the column-span finrank.
  have hrank_eq :
      flatRank T I = Module.finrank F
        (Submodule.span F (Set.range (flattenMatrix T I).col)) := by
    unfold flatRank
    exact (flattenMatrix T I).rank_eq_finrank_span_cols
  rw [hrank_eq]
  -- Step C: every column is in `Submodule.span F (Set.range w)`.
  have hcol_in_span :
      ∀ col : ColIdx,
        (flattenMatrix T I).col col ∈
          Submodule.span F (Set.range w) := by
    intro col
    -- Express col-vector as a linear combo of `w ℓ`.
    have hcol_apply :
        (flattenMatrix T I).col col =
          ∑ ℓ : Fin (tensorRank T), v ℓ col • w ℓ := by
      funext row
      simp only [Matrix.col_apply]
      rw [hentry row col]
      rw [Finset.sum_apply]
      refine Finset.sum_congr rfl ?_
      intro ℓ _
      change v ℓ col * w ℓ row = (v ℓ col • w ℓ) row
      rfl
    rw [hcol_apply]
    refine Submodule.sum_mem _ ?_
    intro ℓ _
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨ℓ, rfl⟩)
  -- Step D: combine column-span containment + `finrank_range_le_card`.
  have hspan_subset :
      Submodule.span F (Set.range (flattenMatrix T I).col) ≤
        Submodule.span F (Set.range w) := by
    rw [Submodule.span_le]
    rintro c ⟨col, rfl⟩
    exact hcol_in_span col
  calc Module.finrank F (Submodule.span F (Set.range (flattenMatrix T I).col))
      ≤ Module.finrank F (Submodule.span F (Set.range w)) :=
        Submodule.finrank_mono hspan_subset
    _ ≤ Fintype.card (Fin (tensorRank T)) := finrank_range_le_card w
    _ = tensorRank T := Fintype.card_fin _

/-! ### Iterated Kronecker multiplicativity of flattening rank (Section 1.4)

`flatRank T {j}^n ≤ flatRank (regroupingMap d n (tensorPow n T)) {j}`,
proved by induction on `n` via `flatRank_kron_mul_le` (Section 1.4, axiom-free,
proven in `MaxRankBound.lean`) and structural identities at `n=1` (base case)
and `n→n+1` (step case). The two structural identities are extracted as
private helpers `regroupingMap_tensorPow_one_flatRank_eq` and
`flatRank_regroupingMap_tensorPow_succ_eq_kron`. -/

/-- **flatRank format-cast invariance** (see Section 1.4):
    transporting along a leg-wise format equality preserves `flatRank` at any
    `I`-flattening. Used by `flatRank_pow_le_flatRank_regroupingMap_tensorPow`
    base + step. -/
private lemma flatRank_format_cast {k : ℕ} {d d' : Fin k → ℕ+} (h : d = d')
    (T : KTensor F d) (I : Finset (Fin k)) :
    flatRank (h ▸ T) I = flatRank T I := by
  subst h; rfl

/-- **n=1 base-case identity** (Christandl-Hoeberechts-Nieuwboer-Vrana-Zuiddam,
    “Asymptotic tensor rank is characterized by polynomials”,
    Section 2.1). The flattening rank of `regroupingMap d 1 (tensorPow 1 T)` equals
    the flattening rank of `T`.

    Section 2.1: the regrouping is the linear extension of `v_1 ⊗ ⋯ ⊗ v_n ↦
    v_1 ⊠ ⋯ ⊠ v_n`. For `n = 1` the single Kronecker factor is the tensor itself,
    so `regroupingMap d 1 (tensorPow 1 T) = hfmt.symm ▸ T` (a pure format recast
    along `hfmt : formatPow d 1 = d`), and `flatRank_format_cast` concludes.

    PRIVATE structural sub-helper for `flatRank_pow_le_flatRank_regroupingMap_tensorPow`
    base case `n = 1`. The equality `regroupingMap d 1 (tensorPow 1 T) = hfmt.symm ▸ T`
    is proven entry-wise: `regroupingMap_tprod_apply` + `Fin.prod_univ_one` reduce
    the LHS to `T (sliceFun d 1 jdx 0)`, `KTensor_cast_apply` moves the RHS cast onto
    the index argument, and the two multi-indices agree leg-wise at the `.val` level
    via `val_eq_rec_pi_fin` and `powIndexEquiv_one` (the `n = 1` base-`d` digit
    decomposition is the identity on values). AXIOM-FREE. -/
private lemma regroupingMap_tensorPow_one_flatRank_eq
    {k : ℕ} (d : Fin k → ℕ+) (T : KTensor F d) (j : Fin k) :
    flatRank (regroupingMap d (1 : ℕ+)
      (tensorPow (F := F) (V := KTensor F d) (1 : ℕ+) T)) {j} = flatRank T {j} := by
  classical
  -- Step 1: `formatPow d 1 = d` entrywise.
  have hfmt : formatPow d 1 = d := by funext i; simp [formatPow]
  -- Step 2: it suffices to show `regroupingMap d 1 (tensorPow 1 T) = hfmt.symm ▸ T`.
  -- Then `flatRank_format_cast` concludes.
  suffices h : regroupingMap d (1 : ℕ+)
      (tensorPow (F := F) (V := KTensor F d) (1 : ℕ+) T) = hfmt.symm ▸ T by
    rw [h, flatRank_format_cast]
  -- Pointwise: at every `jdx : ∀ i, Fin (formatPow d 1 i)`, both sides equal
  -- `T (cast jdx : ∀ i, Fin (d i))`.
  -- We use the `subst hfmt` strategy: substitute `formatPow d 1` with `d`
  -- throughout, reducing the ▸-cast to identity.
  -- The trick: bind everything in the goal under a "for all `dʹ` such that
  -- `d^1 = dʹ`" pattern, then `subst`.
  -- Concretely: revert all hypotheses involving `formatPow d 1` and use
  -- `hfmt : formatPow d 1 = d` as the substituted equation.
  -- Since `T : KTensor F d` and `regroupingMap d (1 : ℕ+) ...` produces
  -- a `KTensor F (formatPow d 1)`, we use the equation between formats
  -- to bridge.
  -- Direct approach: prove pointwise via funext and compute.
  -- Approach: revert everything that depends on `formatPow d 1` and then
  -- substitute via `hfmt`. The cleanest is to use `subst hfmt.symm` after
  -- ensuring `d` is a local variable bound (which it is, as the lemma binder).
  -- But hfmt is `formatPow d 1 = d`, so subst eliminates `d` if d is a variable.
  -- That's fine — d is a parameter of the lemma.
  -- BUT: after `subst hfmt.symm`, `d` would be replaced by `formatPow d 1`,
  -- which mentions `d` recursively (because formatPow is defined as `d i ^ n`).
  -- So `subst` doesn't work directly.
  -- The alternative: use `Eq.mpr` / `congr` to bridge.
  -- We use `congrArg`: regroupingMap d 1 (tensorPow 1 T) = h ▸ T
  -- iff both sides agree pointwise via .val. We've narrowed to a pure
  -- `Fin (d_i^1) = Fin (d_i)` identification per leg.
  -- The remaining obstruction is that `Eq.mp` of a `Fin = Fin` equation
  -- does not reduce to `Fin.cast` definitionally in our context.
  --
  -- Discharge attempt: use `Subsingleton.elim` to identify the two `KTensor`
  -- values. Since both LHS and RHS are `T` applied at multi-indices that are
  -- pointwise `.val`-equal in `Fin (d i)`, they are equal `Fin` elements
  -- (and hence the `T`-values agree).
  funext jdx
  show regroupingMap d (1 : ℕ+)
      (PiTensorProduct.tprod F (fun _ : Fin ((1 : ℕ+) : ℕ) => T)) jdx
    = (hfmt.symm ▸ T) jdx
  rw [regroupingMap_tprod_apply]
  show (∏ jj : Fin 1, T (sliceFun d 1 jdx jj)) = _
  rw [Fin.prod_univ_one]
  -- LHS: `T (sliceFun d 1 jdx 0)`.
  -- RHS: `(hfmt.symm ▸ T) jdx`. By `KTensor_cast_apply` (transport along a format
  -- equality moves the cast onto the index argument), this is
  -- `T (hfmt.symm.symm ▸ jdx)`.
  rw [KTensor_cast_apply]
  -- Goal: `T (sliceFun d 1 jdx 0) = T ((hfmt.symm.symm) ▸ jdx)`.
  -- It suffices to identify the two multi-indices in `∀ i, Fin (d i)`.
  congr 1
  funext i
  -- Two `Fin (d i)` elements; check `.val`-equality (Fin.ext).
  apply Fin.ext
  -- RHS: `((hfmt.symm.symm ▸ jdx) i).val = (jdx i).val` by `val_eq_rec_pi_fin`.
  rw [val_eq_rec_pi_fin]
  -- LHS: `(sliceFun d 1 jdx 0 i).val = (powIndexEquiv (d i) 1 (cast (jdx i)) 0).val`.
  -- By `powIndexEquiv_one` (n=1 decomposition is the identity on values), this is
  -- `(cast (jdx i)).val = (jdx i).val` (the `Fin (formatPow d 1 i) = Fin (d i ^ 1)`
  -- cast preserves `.val`).
  rw [sliceFun, powIndexEquiv_one]

/--
**Step-case structural identity** (Sections 1.4 and 2.1). The
    `(n+1)`-fold regrouped tensor power factors via Kronecker product as
    `regroupingMap d (n+1) (tensorPow (n+1) T) = (fmt_cast) ▸
       (regroupingMap d n (tensorPow n T) ⊠ regroupingMap d 1 (tensorPow 1 T))`,
    so `flatRank` at any `{j}` is invariant.

    PRIVATE structural sub-helper for `flatRank_pow_le_flatRank_regroupingMap_tensorPow`
    step case. Combines:
    * `tensorPowerAdd_symm_tensorPow` (already proven, axiom-free):
      `(tensorPowerAdd ..).symm (tensorPow n T ⊗ tensorPow 1 T) = tensorPow (n+1) T`.
    * `regroupingMap_tensorPowerAdd_symm_eq_kron_cast` (already proven, axiom-free):
      `(fmt_cast) ▸ regroupingMap d ⟨n+1,_⟩ (...) = regroupingMap d n .. ⊠ regroupingMap d 1 ..`.
    * `flatRank_format_cast` (proven above): format-cast invariance.
    * `PNat-cast invariance: ⟨n+1, _⟩ = n + 1` so the regroupingMaps agree.
-/
private lemma flatRank_regroupingMap_tensorPow_succ_eq_kron
    {k : ℕ} (d : Fin k → ℕ+) (T : KTensor F d) (j : Fin k) (n : ℕ+) :
    flatRank ((regroupingMap d n (tensorPow (F := F) (V := KTensor F d) n T)) ⊠
      (regroupingMap d (1 : ℕ+) (tensorPow (F := F) (V := KTensor F d) (1 : ℕ+) T))) {j} =
    flatRank (regroupingMap d (n + 1)
      (tensorPow (F := F) (V := KTensor F d) (n + 1) T)) {j} := by
  -- Use the structural identity from `regroupingMap_tensorPowerAdd_symm_eq_kron_cast`
  -- + `tensorPowerAdd_symm_tensorPow`.
  have htP := tensorPowerAdd_symm_tensorPow (F := F) (V := KTensor F d) T n
  have hreg_kron := regroupingMap_tensorPowerAdd_symm_eq_kron_cast (F := F) d n 1
      (tensorPow (F := F) (V := KTensor F d) n T)
      (tensorPow (F := F) (V := KTensor F d) 1 T)
  rw [htP] at hreg_kron
  -- hreg_kron : (formatPow_add_eq_mul d n 1) ▸ regroupingMap d ⟨n+1,_⟩ (tensorPow (n+1) T)
  --            = (regroupingMap d n ..) ⊠ (regroupingMap d 1 ..).
  -- Hence LHS of the goal = flatRank ((fmt_cast) ▸ regroupingMap d ⟨n+1,_⟩ (tensorPow (n+1) T)) {j}
  --                       = flatRank (regroupingMap d ⟨n+1,_⟩ (tensorPow (n+1) T)) {j}
  --                                                              (by flatRank_format_cast)
  --                       = flatRank (regroupingMap d (n+1) (tensorPow (n+1) T)) {j}
  --                                                              (by PNat-cast: ⟨n+1,_⟩ = n+1)
  rw [← hreg_kron]
  rw [flatRank_format_cast]
  -- Goal: flatRank ((regroupingMap d ⟨↑n + ↑1, _⟩) (tensorPow (n+1) T)) {j}
  --     = flatRank ((regroupingMap d (n+1)) (tensorPow (n+1) T)) {j}.
  -- Only the regroupingMap's PNat index differs: `⟨↑n + ↑1, _⟩` vs `n + 1`.
  have hn1 : (⟨(n : ℕ) + ((1 : ℕ+) : ℕ),
      Nat.add_pos_left n.pos _⟩ : ℕ+) = (n + 1 : ℕ+) := by
    apply PNat.coe_injective
    show (n : ℕ) + ((1 : ℕ+) : ℕ) = ((n + 1 : ℕ+) : ℕ)
    rw [PNat.add_coe]
  -- Both sides depend on the PNat index in a dependent way. Use `congr 1` for
  -- the format and `subst`-style cast bridge.
  -- Both sides are `flatRank (regroupingMap d <PNat> (tensorPow <PNat> T)) {j}`,
  -- where the only difference is the PNat. The `tensorPow (n+1) T` on the inside
  -- of both sides happens to use `n+1` — but on the LHS, regroupingMap is at
  -- `⟨↑n+↑1, _⟩`, which is a different PNat with the same value as `n+1`.
  -- This is a HEq across PNat equality.
  -- Since `regroupingMap` takes `d : Fin k → ℕ+` and `n : ℕ+`, and the output
  -- type `KTensor F (formatPow d n)` depends on n, this requires HEq.
  -- Use congrArg with subst:
  cases hn1
  rfl

/-- **Iterated Kronecker multiplicativity of flatRank** (Sections 1.4 and 2.1).

    Section 1.4: "For two `k`-tensors `S` and `T` their Kronecker
    product `S ⊠ T` is the `k`-tensor obtained by taking the tensor product
    and grouping corresponding legs."

    Iterated `n` times via `regroupingMap d n (tensorPow n T)`:

      `(flatRank T {j})^n ≤ flatRank (regroupingMap d n (tensorPow n T)) {j}`.

    Proof by `PNat.recOn` induction:
    * **Base `n = 1`**: `regroupingMap_tensorPow_one_flatRank_eq`.
    * **Step `n → n+1`**: chain `IH * flatRank T {j}` via
      `flatRank_kron_mul_le` (Section 1.4, axiom-free) and
      `flatRank_regroupingMap_tensorPow_succ_eq_kron`. -/
lemma flatRank_pow_le_flatRank_regroupingMap_tensorPow
    {k : ℕ} {d : Fin k → ℕ+}
    (T : KTensor F d) (j : Fin k) (n : ℕ+) :
    (flatRank T {j}) ^ (n : ℕ) ≤
      flatRank (regroupingMap d n (tensorPow (F := F) (V := KTensor F d) n T))
        {⟨j.val, by
          -- `j : Fin k`; `regroupingMap d n …` has format `formatPow d n` over `Fin k`,
          -- so we can reuse `j` at the same index.
          exact j.isLt⟩} := by
  -- `⟨j.val, j.isLt⟩ = j` by Fin.eta, so reduce to the cleaner form.
  show (flatRank T {j}) ^ (n : ℕ) ≤
    flatRank (regroupingMap d n (tensorPow (F := F) (V := KTensor F d) n T)) {j}
  induction n using PNat.recOn with
  | one =>
    -- Base case: regroupingMap_tensorPow_one_flatRank_eq gives the equality.
    simp only [PNat.one_coe, pow_one]
    -- Goal: flatRank T {j} ≤ flatRank (regroupingMap d 1 (tensorPow 1 T)) {j}.
    have heq := regroupingMap_tensorPow_one_flatRank_eq (F := F) d T j
    omega
  | succ n ih =>
    -- Step case: use IH + flatRank_kron_mul_le + flatRank_regroupingMap_tensorPow_succ_eq_kron.
    have hpow_succ : (flatRank T {j}) ^ ((n + 1 : ℕ+) : ℕ) =
        (flatRank T {j}) ^ (n : ℕ) * (flatRank T {j}) := by
      rw [PNat.add_coe, PNat.one_coe, pow_succ]
    rw [hpow_succ]
    have hkron := flatRank_kron_mul_le (F := F)
      (regroupingMap d n (tensorPow (F := F) (V := KTensor F d) n T))
      (regroupingMap d (1 : ℕ+) (tensorPow (F := F) (V := KTensor F d) (1 : ℕ+) T))
      j
    have hreg_one_flat := regroupingMap_tensorPow_one_flatRank_eq (F := F) d T j
    have hstep_eq := flatRank_regroupingMap_tensorPow_succ_eq_kron (F := F) d T j n
    calc (flatRank T {j}) ^ (n : ℕ) * (flatRank T {j})
        ≤ flatRank (regroupingMap d n
            (tensorPow (F := F) (V := KTensor F d) n T)) {j} * (flatRank T {j}) :=
          Nat.mul_le_mul_right _ ih
      _ = flatRank (regroupingMap d n
            (tensorPow (F := F) (V := KTensor F d) n T)) {j} *
          flatRank (regroupingMap d (1 : ℕ+)
            (tensorPow (F := F) (V := KTensor F d) (1 : ℕ+) T)) {j} := by
            rw [hreg_one_flat]
      _ ≤ flatRank ((regroupingMap d n
            (tensorPow (F := F) (V := KTensor F d) n T)) ⊠
          (regroupingMap d (1 : ℕ+)
            (tensorPow (F := F) (V := KTensor F d) (1 : ℕ+) T))) {j} := hkron
      _ = flatRank (regroupingMap d (n + 1)
            (tensorPow (F := F) (V := KTensor F d) (n + 1) T)) {j} := hstep_eq

/-- Per-`n` flattening bound (Section 1.4).

For every `n : ℕ+`, the `n`-th power of the flattening rank is bounded by the
tensor rank of the regrouped `n`-th Kronecker power:
`flatRank T {j}^n ≤ tensorRank (regroupingMap d n (T^⊗n))`.

Proof in the paper combines two facts from Section 1.4:
* Section 1.4 — `tensorRank T ≥ flatRank_I T` (matrix flattening rank is a lower
  bound for tensor rank). Encoded as `flatRank_le_tensorRank`.
* Section 1.4 — `flatRank (S ⊠ T) I = flatRank S I · flatRank T I` (matrix
  flattening rank is multiplicative under Kronecker product). Iterated `n`
  times via `regroupingMap_tensorPowerAdd_symm_eq_kron_cast` (Section 2.1),
  yielding `(flatRank T {j})^n ≤ flatRank (regroupingMap d n (T^⊗n)) {j}`.
  Encoded as `flatRank_pow_le_flatRank_regroupingMap_tensorPow`.

Combine: `(flatRank T {j})^n ≤ flatRank (regroupingMap d n (T^⊗n)) {j} ≤
tensorRank (regroupingMap d n (T^⊗n))`. -/
lemma flatRank_pow_le_tensorRank_regroupingMap {k : ℕ} {d : Fin k → ℕ+}
    (T : KTensor F d) (j : Fin k) (n : ℕ+) :
    (flatRank T {j} : ℝ) ^ (n : ℕ) ≤
      ((tensorRank (regroupingMap d n
        (tensorPow (F := F) (V := KTensor F d) n T)) : ℕ) : ℝ) := by
  -- Step 1: `(flatRank T {j})^n ≤ flatRank (regroupingMap d n (T^⊗n)) {j}`
  -- by iterated Kronecker multiplicativity of flatRank (Section 1.4).
  have h_pow_le :
      (flatRank T {j}) ^ (n : ℕ) ≤
        flatRank (regroupingMap d n
          (tensorPow (F := F) (V := KTensor F d) n T))
          {⟨j.val, j.isLt⟩} :=
    flatRank_pow_le_flatRank_regroupingMap_tensorPow (F := F) T j n
  -- Step 2: `flatRank S I ≤ tensorRank S` for any `S, I` (Section 1.4).
  have hk : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr (fun h => by
    rw [h] at j; exact j.elim0)
  have h_le :
      flatRank (regroupingMap d n
        (tensorPow (F := F) (V := KTensor F d) n T))
        {⟨j.val, j.isLt⟩} ≤
      tensorRank (regroupingMap d n
        (tensorPow (F := F) (V := KTensor F d) n T)) :=
    flatRank_le_tensorRank (F := F) hk _ _
  -- Cast to ℝ and combine.
  have h_combined :
      (flatRank T {j}) ^ (n : ℕ) ≤
        tensorRank (regroupingMap d n
          (tensorPow (F := F) (V := KTensor F d) n T)) :=
    le_trans h_pow_le h_le
  exact_mod_cast h_combined

/-! ### Conciseness API (Section 1.4).

The conciseness reduction `exists_concise_restriction` is the standard fact
(Section 1.4: "Any tensor is equivalent to a concise tensor.")
combined with the admissibility-of-`R̃` axioms (Definition 2.1) — equivalence
(`Restricts T S ∧ Restricts S T`) is preserved by every admissible
functional, in particular by `asympRank`.

We isolate three named helpers carrying paper citations:

* `Restricts.asympRank_le` — restriction is `asympRank`-monotone (Definition 2.1,
  via tensor-rank monotonicity under leg-wise linear maps).
* `Restricts.asympRank_eq_of_equiv` — equivalent tensors have equal
  `asympRank` (immediate from `asympRank_le` applied both ways).
* `exists_concise_restriction` — the existence of a concise equivalent
  with matching flattening-rank format, requiring `T ≠ 0` (Section 1.4, the
  load-bearing standard fact).

The `T ≠ 0` hypothesis on `exists_concise_restriction` is exactly the
paper's positive-format convention `d ∈ ℤ_{≥1}^k` (Section 1.4): conciseness
forces `flatRank T' {j} = d' j ≥ 1`, so `T' ≠ 0`. Corollary 2.6
(Corollary 2.6) only applies conciseness to the *positive* values `r_i`,
where the raw witness is nonzero; the well-ordering floor `r_i = 0` is
realized in any format by the zero tensor (`asympRank_zero`) and needs no
concise equivalent. So the `T = 0` case never arises and the paper's proof
is transcribed faithfully without a false `T = 0` conciseness instance. -/

/-! ### Restriction lifts to regrouped tensor powers (Sections 1.4 and 2.1)

The headline lemma `Restricts.regroupingMap_tensorPow` is the paper's leg-wise
functoriality of the `n`-fold Kronecker self-power:

* **Setup** — Section 1.4: `S ≤ T` ↔ `S = (A_1 ⊗ ⋯ ⊗ A_k) T` for leg-wise
  linear maps `A_i : F^{d_T i} → F^{d_S i}`.
* **Regrouping** — Section 2.1: `regroupingMap d n` is the linear extension
  of `v_1 ⊗ ⋯ ⊗ v_n ↦ v_1 ⊠ ⋯ ⊠ v_n`; hence
  `regroupingMap d n (tensorPow n T) = T^{⊠ n}` (the `n`-fold Kronecker
  self-product, living in `KTensor F (formatPow d n)`).
* **Claim**: if `S ≤ T` via `(A_1, …, A_k)`, then `S^{⊠ n} ≤ T^{⊠ n}` via the
  leg-wise Kronecker `n`-th powers `(A_1^{⊠ n}, …, A_k^{⊠ n})`, where
  `A_i^{⊠ n} : F^{(d_T i)^n} → F^{(d_S i)^n}` is the Kronecker product of `n`
  copies of `A_i`.

Two helpers are needed for the proof:

* `regroupingMap_tensorPow_apply` — explicit evaluation formula:
  `(regroupingMap d n (tensorPow n S)) jdx = ∏ j, S (sliceFun d n jdx j)`.
* `regroupingMultiIndexEquiv` — the multi-index equivalence
  `(∀ i, Fin (formatPow d n i)) ≃ (Fin n → ∀ i, Fin (d i))` by per-leg slicing,
  used to change variables in the `Restricts` sum.

The main proof then expands both sides explicitly, applies `Finset.prod_univ_sum`
to swap `∏ j ∑ inner_j` with `∑ tuple ∏ j`, reindexes via
`regroupingMultiIndexEquiv`, and identifies the leg-wise Kronecker `n`-th power
of `A_i` with the inner product over `j` of the `A_i`-entries at the sliced
indices. -/

/-- **Helper** (Christandl et al., Section 2.1).

    Explicit evaluation formula for `regroupingMap d n` applied to a `tensorPow n S`:
    on a multi-index `jdx : ∀ i, Fin (formatPow d n i)`, the value is the product
    over `j : Fin n` of `S` evaluated at the `j`-th slice `sliceFun d n jdx j`.

    This is the pointwise content of Section 2.1: `regroupingMap` is the linear
    extension of `v_1 ⊗ ⋯ ⊗ v_n ↦ v_1 ⊠ ⋯ ⊠ v_n`; on a constant `tprod` this
    becomes `S ⊠ ⋯ ⊠ S` (`n` copies), whose `jdx`-entry is the product of `S`
    entries at the sliced indices.

    Proved by unfolding `regroupingMap = PiTensorProduct.lift (...)` and using
    `PiTensorProduct.lift.tprod`, `MultilinearMap.pi_apply`,
    `MultilinearMap.compLinearMap_apply`, `MultilinearMap.mkPiRing_apply`. -/
lemma regroupingMap_tensorPow_apply {k : ℕ} (d : Fin k → ℕ+) (n : ℕ+)
    (S : KTensor F d) (jdx : ∀ i : Fin k, Fin (formatPow d n i)) :
    regroupingMap d n (tensorPow (F := F) (V := KTensor F d) n S) jdx =
      ∏ j : Fin (n : ℕ), S (sliceFun d n jdx j) := by
  unfold regroupingMap tensorPow
  rw [PiTensorProduct.lift.tprod]
  rw [MultilinearMap.pi_apply]
  rw [MultilinearMap.compLinearMap_apply]
  rw [MultilinearMap.mkPiRing_apply]
  -- Now: `(∏ j, kTensorEval (sliceFun d n jdx j) S) • 1 = ∏ j, S (sliceFun d n jdx j)`.
  -- `kTensorEval idx S = S idx` and `(· • 1)` is identity at value `1`.
  simp [kTensorEval]

/-- **Helper** (Christandl et al., Section 2.1).

    For each `i : Fin k`, the multi-index leg `Fin ((dT i)^n)` is equivalent to
    `Fin n → Fin (dT i)` via `powIndexEquiv`. Equivalently, the full multi-index
    `(∀ i, Fin (formatPow dT n i))` is equivalent to `(Fin n → ∀ i, Fin (dT i))`
    by per-leg slicing. We package this equivalence so we can change variables in
    the sum index in `Restricts.regroupingMap_tensorPow`. -/
noncomputable def regroupingMultiIndexEquiv {k : ℕ} (d : Fin k → ℕ+) (n : ℕ+) :
    (∀ i : Fin k, Fin (formatPow d n i)) ≃ (Fin (n : ℕ) → ∀ i : Fin k, Fin (d i)) where
  toFun idx := fun j i => sliceFun d n idx j i
  invFun tuple := fun i =>
    (by simpa [formatPow] using! ((powIndexEquiv (d i) n).symm (fun j => tuple j i)) :
      Fin (formatPow d n i))
  left_inv := by
    intro idx
    funext i
    change (by simpa [formatPow] using!
        ((powIndexEquiv (d i) n).symm (fun j =>
          powIndexEquiv (d i) n (by simpa [formatPow] using! idx i) j)) :
        Fin (formatPow d n i)) = idx i
    -- The inner `fun j => powIndexEquiv (...) j` is just `powIndexEquiv (d i) n (cast idx i)`.
    have hfun :
        (fun j : Fin (n : ℕ) =>
          powIndexEquiv (d i) n (by simpa [formatPow] using! idx i) j)
          = powIndexEquiv (d i) n (by simpa [formatPow] using! idx i) := by
      funext j; rfl
    rw [hfun]
    rw [Equiv.symm_apply_apply]
    -- Now: `(by simpa : Fin (formatPow ...)) = idx i`, where the LHS is the
    -- `simpa`-cast of `(by simpa : Fin ((d i)^n))` of `idx i`. Both casts are
    -- between propositionally-equal types (`formatPow d n i = (d i)^n`) and the
    -- composition is the identity.
    rfl
  right_inv := by
    intro tuple
    funext j i
    change sliceFun d n
        (fun i' => (by simpa [formatPow] using!
          ((powIndexEquiv (d i') n).symm (fun j' => tuple j' i'))) : (∀ i' : Fin k,
            Fin (formatPow d n i'))) j i = tuple j i
    -- sliceFun d n idx j i = powIndexEquiv (d i) n (cast (idx i)) j.
    change powIndexEquiv (d i) n
        (by simpa [formatPow] using!
          (by simpa [formatPow] using!
            ((powIndexEquiv (d i) n).symm (fun j' => tuple j' i)) :
              Fin (formatPow d n i)) :
              Fin ((d i : ℕ) ^ (n : ℕ))) j = tuple j i
    -- The double `simpa` cast composes to identity, leaving:
    --   `powIndexEquiv (d i) n ((powIndexEquiv (d i) n).symm (fun j' => tuple j' i)) j`
    --   = (fun j' => tuple j' i) j = tuple j i.
    have hcast :
        (by simpa [formatPow] using!
          (by simpa [formatPow] using!
            ((powIndexEquiv (d i) n).symm (fun j' => tuple j' i)) :
              Fin (formatPow d n i)) :
              Fin ((d i : ℕ) ^ (n : ℕ)))
        = (powIndexEquiv (d i) n).symm (fun j' => tuple j' i) := rfl
    rw [hcast]
    rw [Equiv.apply_symm_apply]

@[simp] lemma regroupingMultiIndexEquiv_apply {k : ℕ} (d : Fin k → ℕ+) (n : ℕ+)
    (idx : ∀ i : Fin k, Fin (formatPow d n i)) (j : Fin (n : ℕ)) :
    regroupingMultiIndexEquiv d n idx j = sliceFun d n idx j := rfl

lemma regroupingMultiIndexEquiv_symm_slice {k : ℕ} (d : Fin k → ℕ+) (n : ℕ+)
    (tuple : Fin (n : ℕ) → ∀ i : Fin k, Fin (d i)) (j : Fin (n : ℕ)) (i : Fin k) :
    sliceFun d n ((regroupingMultiIndexEquiv d n).symm tuple) j i = tuple j i := by
  have := (regroupingMultiIndexEquiv d n).apply_symm_apply tuple
  have hh := congr_fun (congr_fun this j) i
  exact hh

/-- **Restriction lifts to regrouped tensor powers** (Christandl et al., Sections 1.4 and 2.1).

    If `S ≤ T` via `(A_1, …, A_k)`, then `regroupingMap dS n (tensorPow n S) ≤
    regroupingMap dT n (tensorPow n T)` via the leg-wise Kronecker `n`-th
    powers of the `A_i`. See module note above for the proof outline. -/
lemma Restricts.regroupingMap_tensorPow {k : ℕ} {dS dT : Fin k → ℕ+}
    {S : KTensor F dS} {T : KTensor F dT} (h : Restricts S T) (n : ℕ+) :
    Restricts
      (regroupingMap dS n (tensorPow (F := F) (V := KTensor F dS) n S))
      (regroupingMap dT n (tensorPow (F := F) (V := KTensor F dT) n T)) := by
  classical
  obtain ⟨A, hSeq⟩ := h
  -- Witness: A' i jdx_i idx_i = ∏ j, A i (powIndexEquiv (dS i) n (cast jdx_i) j)
  --                                    (powIndexEquiv (dT i) n (cast idx_i) j).
  -- More compactly, using `sliceFun`:
  --   A' i jdx_i idx_i = ∏ j, A i (sliceFun-leg-i jdx_i j) (sliceFun-leg-i idx_i j).
  refine ⟨fun i => fun jdx_i idx_i =>
      ∏ j : Fin (n : ℕ),
        A i (powIndexEquiv (dS i) n
              (by simpa [formatPow] using! jdx_i : Fin ((dS i : ℕ) ^ (n : ℕ))) j)
            (powIndexEquiv (dT i) n
              (by simpa [formatPow] using! idx_i : Fin ((dT i : ℕ) ^ (n : ℕ))) j), ?_⟩
  intro jdx
  -- LHS: regroupingMap dS n (tensorPow n S) jdx = ∏ j, S (sliceFun dS n jdx j).
  rw [regroupingMap_tensorPow_apply (F := F) dS n S jdx]
  -- Substitute S (sliceFun dS n jdx j) using hSeq.
  have hS_slice : ∀ j : Fin (n : ℕ),
      S (sliceFun dS n jdx j) =
        ∑ inner_j : (∀ i : Fin k, Fin (dT i)),
          (∏ i, A i (sliceFun dS n jdx j i) (inner_j i)) * T inner_j :=
    fun j => hSeq (sliceFun dS n jdx j)
  -- Rewrite each factor in the LHS product.
  rw [show
      (∏ j : Fin (n : ℕ), S (sliceFun dS n jdx j))
        = ∏ j : Fin (n : ℕ),
          ∑ inner_j : (∀ i : Fin k, Fin (dT i)),
            (∏ i, A i (sliceFun dS n jdx j i) (inner_j i)) * T inner_j from
      Finset.prod_congr rfl (fun j _ => hS_slice j)]
  -- Apply `Finset.prod_univ_sum` to swap ∏ j ∑ inner_j → ∑ tuple ∏ j.
  rw [Finset.prod_univ_sum
        (t := fun _ : Fin (n : ℕ) => (Finset.univ : Finset (∀ i : Fin k, Fin (dT i))))
        (f := fun (j : Fin (n : ℕ)) (inner_j : ∀ i : Fin k, Fin (dT i)) =>
          (∏ i, A i (sliceFun dS n jdx j i) (inner_j i)) * T inner_j)]
  -- Rewrite `Fintype.piFinset (fun _ => univ) = univ`.
  rw [show
      Fintype.piFinset
          (fun _ : Fin (n : ℕ) => (Finset.univ : Finset (∀ i : Fin k, Fin (dT i))))
        = (Finset.univ : Finset (Fin (n : ℕ) → ∀ i : Fin k, Fin (dT i))) from by
    ext _; simp]
  -- LHS = ∑ tuple, ∏ j, (∏ i, A i (sliceFun dS n jdx j i) (tuple j i)) * T (tuple j).
  -- Change variable from `tuple : Fin n → ∀ i, Fin (dT i)` to
  -- `idx : ∀ i, Fin (formatPow dT n i)` via `regroupingMultiIndexEquiv dT n`.
  rw [show
      (∑ tuple : (Fin (n : ℕ) → ∀ i : Fin k, Fin (dT i)),
        ∏ j : Fin (n : ℕ),
          (∏ i, A i (sliceFun dS n jdx j i) (tuple j i)) * T (tuple j))
        = ∑ idx : (∀ i : Fin k, Fin (formatPow dT n i)),
          ∏ j : Fin (n : ℕ),
            (∏ i, A i (sliceFun dS n jdx j i)
              (sliceFun dT n idx j i)) * T (sliceFun dT n idx j) from ?_]
  swap
  · -- Sum reindexing along `regroupingMultiIndexEquiv dT n`.
    refine (Equiv.sum_comp (regroupingMultiIndexEquiv dT n)
      (fun tuple : (Fin (n : ℕ) → ∀ i : Fin k, Fin (dT i)) =>
        ∏ j : Fin (n : ℕ),
          (∏ i, A i (sliceFun dS n jdx j i) (tuple j i)) * T (tuple j))).symm
  -- Goal: ∑ idx, (∏ j ∏ i, A i (sliceFun dS jdx j i) (sliceFun dT idx j i))
  --                * (∏ j, T (sliceFun dT idx j))
  --     = ∑ idx, (∏ i, A' i (jdx i) (idx i)) * (regroupingMap dT n (tensorPow n T) idx).
  -- Apply distributivity (∏ j of (a * b) = (∏ j a) * (∏ j b)) and swap (∏ i ∏ j ↔ ∏ j ∏ i)
  -- on each summand.
  refine Finset.sum_congr rfl ?_
  intro idx _
  -- Pull the product over `j` of the products.
  rw [Finset.prod_mul_distrib]
  -- Now: (∏ j, ∏ i, A i (sliceFun dS jdx j i) (sliceFun dT idx j i))
  --      * (∏ j, T (sliceFun dT idx j))
  -- Goal RHS: (∏ i, A' i (jdx i) (idx i)) * regroupingMap dT n (tensorPow n T) idx.
  -- For the second factor: use `regroupingMap_tensorPow_apply`.
  rw [regroupingMap_tensorPow_apply (F := F) dT n T idx]
  -- For the first factor: swap product order and identify with A'.
  rw [Finset.prod_comm]
  -- Goal first factor: ∏ i, ∏ j, A i (sliceFun dS n jdx j i) (sliceFun dT n idx j i)
  --              = ∏ i, A' i (jdx i) (idx i).
  -- The witness `A' i jdx_i idx_i` is defined as
  --   ∏ j, A i (powIndexEquiv (dS i) n (cast jdx_i) j) (powIndexEquiv (dT i) n (cast idx_i) j).
  -- And `sliceFun d n idx j i = powIndexEquiv (d i) n (cast (idx i)) j`.
  -- So the two products agree.
  -- Identify `sliceFun d n idx j i` with the corresponding `powIndexEquiv` value.
  congr 1

/-- **Restriction is `asympRank`-monotone** (Christandl et al., Definition 2.1 and Section 1.4).

    Paper: `R̃` is the admissible functional given by tensor rank on the
    regrouped `n`-th Kronecker self-power (Section 2.1). Restriction
    `S ≤ T` (Section 1.4) factors `S = (A_1 ⊗ ⋯ ⊗ A_k) T` for leg-wise linear
    maps `A_i`. Tensor rank does not increase under leg-wise linear maps
    (Section 1.4, standard fact:
    `tensorRank_mono_under_Restricts` in `TensorRank.lean`). Multiplicativity
    under `⊠` (Section 2.1) lifts the inequality to powers via
    `Restricts.regroupingMap_tensorPow`, giving the per-`n` inequality
    `R(regroupingMap dS n (tensorPow n S)) ≤ R(regroupingMap dT n (tensorPow n T))`.
    Monotonicity of `⨅ n, (·)^(1/n)` then yields `R̃(S) ≤ R̃(T)`. -/
lemma Restricts.asympRank_le {k : ℕ} {dS dT : Fin k → ℕ+}
    {S : KTensor F dS} {T : KTensor F dT} (h : Restricts S T) :
    asympRank S ≤ asympRank T := by
  classical
  by_cases hk : 1 ≤ k
  · -- The non-degenerate case `1 ≤ k`.
    -- `asympRank T = ⨅ n, (toFun n (tensorPow n T) : ℝ)^(1/n)` where
    -- `toFun n U = (tensorRank (regroupingMap dT n U) : NNReal)`.
    unfold asympRank
    simp only [dif_pos hk]
    unfold AdmissibleFunctional.regularize
    -- Both sides are infima over `n : ℕ+`. Use per-`n` monotonicity + ciInf_mono.
    -- For each n: the regrouped tensorPows are related by Restricts (by
    -- `Restricts.regroupingMap_tensorPow`), so their tensor ranks are ordered
    -- by `tensorRank_mono_under_Restricts`. After `(·)^(1/n)`, this preserves
    -- order (rpow is monotone for nonneg base, positive exponent).
    set fS : ℕ+ → ℝ := fun n =>
      ((tensorRankAdmissible F hk dS).toFun n
          (tensorPow (F := F) (V := KTensor F dS) n S) : ℝ) ^ ((1 : ℝ) / (n : ℕ)) with hfS_def
    set fT : ℕ+ → ℝ := fun n =>
      ((tensorRankAdmissible F hk dT).toFun n
          (tensorPow (F := F) (V := KTensor F dT) n T) : ℝ) ^ ((1 : ℝ) / (n : ℕ)) with hfT_def
    -- Per-n inequality: fS n ≤ fT n.
    have h_per_n : ∀ n : ℕ+, fS n ≤ fT n := by
      intro n
      -- Unfold tensorRankAdmissible.toFun.
      have hSn : (tensorRankAdmissible F hk dS).toFun n
          (tensorPow (F := F) (V := KTensor F dS) n S) =
            ((tensorRank
              (regroupingMap dS n
                (tensorPow (F := F) (V := KTensor F dS) n S)) : ℕ) : NNReal) := rfl
      have hTn : (tensorRankAdmissible F hk dT).toFun n
          (tensorPow (F := F) (V := KTensor F dT) n T) =
            ((tensorRank
              (regroupingMap dT n
                (tensorPow (F := F) (V := KTensor F dT) n T)) : ℕ) : NNReal) := rfl
      -- Tensor-rank inequality at the regrouped n-th power level.
      have h_rank : tensorRank
          (regroupingMap dS n (tensorPow (F := F) (V := KTensor F dS) n S))
        ≤ tensorRank
          (regroupingMap dT n (tensorPow (F := F) (V := KTensor F dT) n T)) :=
        tensorRank_mono_under_Restricts hk (h.regroupingMap_tensorPow n)
      -- Cast to NNReal then to ℝ then take 1/n-th power.
      have h_real : ((tensorRank
            (regroupingMap dS n
              (tensorPow (F := F) (V := KTensor F dS) n S)) : ℕ) : ℝ)
          ≤ ((tensorRank
            (regroupingMap dT n
              (tensorPow (F := F) (V := KTensor F dT) n T)) : ℕ) : ℝ) :=
        by exact_mod_cast h_rank
      have h_inv_pos : (0 : ℝ) ≤ (1 : ℝ) / (n : ℕ) :=
        div_nonneg zero_le_one (by exact_mod_cast Nat.zero_le _)
      have h_nn : (0 : ℝ) ≤ ((tensorRank
          (regroupingMap dS n
            (tensorPow (F := F) (V := KTensor F dS) n S)) : ℕ) : ℝ) := by
        exact_mod_cast Nat.zero_le _
      -- Apply Real.rpow_le_rpow on nonneg base.
      have h_rpow := Real.rpow_le_rpow h_nn h_real h_inv_pos
      -- Repackage to match fS, fT after the toFun rewrites.
      simp only [hfS_def, hfT_def, hSn, hTn]
      -- The coercion of NNReal-cast of Nat into ℝ matches Nat→ℝ.
      simp only [NNReal.coe_natCast]
      exact h_rpow
    -- BddBelow witness (both infima are bounded below by 0).
    have h_bdd_S : BddBelow (Set.range fS) := by
      refine ⟨0, ?_⟩
      rintro x ⟨n, rfl⟩
      exact Real.rpow_nonneg (NNReal.coe_nonneg _) _
    have h_bdd_T : BddBelow (Set.range fT) := by
      refine ⟨0, ?_⟩
      rintro x ⟨n, rfl⟩
      exact Real.rpow_nonneg (NNReal.coe_nonneg _) _
    -- ⨅ n, fS n ≤ ⨅ n, fT n by ciInf_mono.
    exact ciInf_mono h_bdd_S h_per_n
  · -- `k = 0`: asympRank S = 0 = asympRank T by definition.
    simp [asympRank, hk]

/-- **Equivalent tensors have equal `asympRank`** (Definition 2.1, Section 1.4).

    Immediate from `Restricts.asympRank_le` applied in both directions.

    Equivalence (Section 1.4): "Two tensors `S` and `T` are equivalent
    if `S ≤ T` and `T ≤ S`." -/
lemma Restricts.asympRank_eq_of_equiv {k : ℕ} {dS dT : Fin k → ℕ+}
    {S : KTensor F dS} {T : KTensor F dT}
    (hST : Restricts S T) (hTS : Restricts T S) :
    asympRank S = asympRank T :=
  le_antisymm hST.asympRank_le hTS.asympRank_le

/-- **Leg-wise matrix application** to a `k`-tensor (Section 1.4).

    Given leg-wise matrices `A i : Matrix (Fin (e i)) (Fin (d i)) F` (each encoding
    a linear map `F^{d i} → F^{e i}`), the applied tensor `applyLegTensor A T` of
    format `e` is `((A_1 ⊗ ⋯ ⊗ A_k) T) jdx = ∑ idx, (∏ i, A i (jdx i) (idx i)) * T idx`.

    This is the data realizing a `Restricts` (Section 1.4): `applyLegTensor A T ≤ T`
    via the witness `A`, by construction. -/
noncomputable def applyLegTensor {k : ℕ} {d e : Fin k → ℕ+}
    (A : ∀ i : Fin k, Matrix (Fin (e i)) (Fin (d i)) F) (T : KTensor F d) :
    KTensor F e :=
  fun jdx => ∑ idx : (∀ i : Fin k, Fin (d i)),
    (∏ i, A i (jdx i) (idx i)) * T idx

/-- `applyLegTensor A T ≤ T` by construction (Section 1.4). -/
lemma applyLegTensor_restricts {k : ℕ} {d e : Fin k → ℕ+}
    (A : ∀ i : Fin k, Matrix (Fin (e i)) (Fin (d i)) F) (T : KTensor F d) :
    Restricts (applyLegTensor A T) T :=
  ⟨A, fun _ => rfl⟩

/-- **Composition of leg-wise applications** (Section 1.4).

    `applyLegTensor B (applyLegTensor A T) = applyLegTensor (fun i => B i * A i) T`.
    This is the leg-wise matrix-product composition
    `(B_1 ⊗ ⋯) (A_1 ⊗ ⋯) = (B_1 A_1) ⊗ ⋯`; same computation as `Restricts.trans`. -/
lemma applyLegTensor_comp {k : ℕ} {d e g : Fin k → ℕ+}
    (B : ∀ i : Fin k, Matrix (Fin (g i)) (Fin (e i)) F)
    (A : ∀ i : Fin k, Matrix (Fin (e i)) (Fin (d i)) F) (T : KTensor F d) :
    applyLegTensor B (applyLegTensor A T) = applyLegTensor (fun i => B i * A i) T := by
  classical
  funext jdx
  -- Unfold both sides.
  show (∑ idx : (∀ i : Fin k, Fin (e i)),
        (∏ i, B i (jdx i) (idx i)) * applyLegTensor A T idx)
      = ∑ kdx : (∀ i : Fin k, Fin (d i)),
        (∏ i, (B i * A i) (jdx i) (kdx i)) * T kdx
  simp only [applyLegTensor]
  -- LHS: ∑ idx, (∏ i, B..) * (∑ kdx, (∏ i, A..) * T kdx).
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro kdx _
  have hfactor :
      ∀ idx : (∀ i : Fin k, Fin (e i)),
        (∏ i, B i (jdx i) (idx i)) * ((∏ i, A i (idx i) (kdx i)) * T kdx)
          = (∏ i, B i (jdx i) (idx i) * A i (idx i) (kdx i)) * T kdx := by
    intro idx
    rw [Finset.prod_mul_distrib]; ring
  simp_rw [hfactor]
  rw [← Finset.sum_mul]
  congr 1
  have hmulapply :
      (∏ i, (B i * A i) (jdx i) (kdx i))
        = ∏ i, ∑ m : Fin (e i), B i (jdx i) m * A i m (kdx i) := by
    refine Finset.prod_congr rfl ?_
    intro i _
    rw [Matrix.mul_apply]
  rw [hmulapply]
  rw [Finset.prod_univ_sum
        (t := fun _ : Fin k => (Finset.univ : Finset (Fin (e _))))
        (f := fun (i : Fin k) (m : Fin (e i)) => B i (jdx i) m * A i m (kdx i))]
  rw [show
      Fintype.piFinset (fun i : Fin k => (Finset.univ : Finset (Fin (e i))))
        = (Finset.univ : Finset (∀ i : Fin k, Fin (e i))) from by
    ext _; simp]

/-- **Zero flattening rank implies zero tensor** (Section 1.4).

    If `flatRank T {j} = 0` for some leg `j`, then `T = 0`: the `j`-flattening
    matrix has rank `0`, hence is the zero matrix (every column lies in the
    column span, which is `0`-dimensional), and each entry of that matrix is an
    entry of `T`, so `T = 0`. -/
lemma flatRank_zero_imp_zero {k : ℕ} {d : Fin k → ℕ+}
    (T : KTensor F d) (j : Fin k) (h : flatRank T {j} = 0) :
    T = (0 : KTensor F d) := by
  classical
  -- `flattenMatrix T {j}` has rank 0, hence is the zero matrix.
  have hrank : (flattenMatrix T {j}).rank = 0 := h
  have hspan :
      Submodule.span F (Set.range (flattenMatrix T {j}).col) = ⊥ := by
    have hfin := (flattenMatrix T {j}).rank_eq_finrank_span_cols
    rw [hrank] at hfin
    -- `finrank (span cols) = 0` ⟹ span = ⊥ (finite-dimensional).
    have : Module.finrank F
        (Submodule.span F (Set.range (flattenMatrix T {j}).col)) = 0 := hfin.symm
    exact Submodule.finrank_eq_zero.mp this
  -- Every column of the flattening matrix is `0`.
  have hcol_zero : ∀ c, (flattenMatrix T {j}).col c = 0 := by
    intro c
    have hmem : (flattenMatrix T {j}).col c ∈
        Submodule.span F (Set.range (flattenMatrix T {j}).col) :=
      Submodule.subset_span ⟨c, rfl⟩
    rw [hspan] at hmem
    simpa using! hmem
  -- Hence the matrix is `0`, and each `T idx` is an entry of it.
  funext idx
  -- `T idx = flattenMatrix T {j} row col` for the row/col split of `idx` at `{j}`.
  set row : (∀ i : {i : Fin k // i ∈ ({j} : Finset (Fin k))}, Fin (d i.val)) :=
    fun i => idx i.val with hrow
  set col : (∀ i : {i : Fin k // i ∉ ({j} : Finset (Fin k))}, Fin (d i.val)) :=
    fun i => idx i.val with hcol
  have hentry : flattenMatrix T {j} row col = T idx := by
    simp only [flattenMatrix, hrow, hcol]
    congr 1
    funext i
    by_cases hi : i ∈ ({j} : Finset (Fin k)) <;> simp [hi]
  have : flattenMatrix T {j} row col = 0 := by
    have := hcol_zero col
    have hz := congrArg (fun f => f row) this
    simpa [Matrix.col] using! hz
  rw [← hentry, this]
  rfl

/-- **Flattening rank is monotone under restriction** (Section 1.4).

    If `S ≤ T`, then for every leg `j`, `flatRank S {j} ≤ flatRank T {j}`.

    Reason (Section 1.4: tensor rank lower-bounds matrix-rank flattenings; the same
    leg-wise linear-map structure that realizes a restriction `S = (A_1 ⊗ ⋯ ⊗ A_k) T`
    factors the `j`-flattening matrix of `S` as a product of matrices through the
    `j`-flattening of `T`, and matrix rank only decreases under multiplication
    (`Matrix.rank_mul_le`). -/
lemma Restricts.flatRank_mono {k : ℕ} {dS dT : Fin k → ℕ+}
    {S : KTensor F dS} {T : KTensor F dT} (h : Restricts S T) (j : Fin k) :
    flatRank S {j} ≤ flatRank T {j} := by
  classical
  obtain ⟨A, hA⟩ := h
  -- Row/column index types of the `{j}`-flattenings.
  set RowS : Type _ := ∀ i : {i : Fin k // i ∈ ({j} : Finset (Fin k))}, Fin (dS i.val)
  set RowT : Type _ := ∀ i : {i : Fin k // i ∈ ({j} : Finset (Fin k))}, Fin (dT i.val)
  set ColS : Type _ := ∀ i : {i : Fin k // i ∉ ({j} : Finset (Fin k))}, Fin (dS i.val)
  set ColT : Type _ := ∀ i : {i : Fin k // i ∉ ({j} : Finset (Fin k))}, Fin (dT i.val)
  -- The leg-`j` row matrix `P r_S r_T = ∏_{i ∈ {j}} A i (r_S i) (r_T i)`.
  let Pmat : Matrix RowS RowT F :=
    fun rS rT => ∏ i : {i : Fin k // i ∈ ({j} : Finset (Fin k))}, A i.val (rS i) (rT i)
  -- The "other legs" column transform `C c_T c_S = ∏_{i ∉ {j}} A i (c_S i) (c_T i)`.
  let Cmat : Matrix ColT ColS F :=
    fun cT cS => ∏ i : {i : Fin k // i ∉ ({j} : Finset (Fin k))}, A i.val (cS i) (cT i)
  -- The split equiv: `(∀ i, Fin (dT i)) ≃ RowT × ColT`.
  let eT := Equiv.piEquivPiSubtypeProd (fun i => i ∈ ({j} : Finset (Fin k)))
    (fun i => Fin (dT i))
  -- Key matrix identity: `flattenMatrix S {j} = Pmat * (flattenMatrix T {j} * Cmat)`.
  have hfact : flattenMatrix S {j} = Pmat * (flattenMatrix T {j} * Cmat) := by
    funext rS cS
    -- LHS: `S (combine rS cS) = ∑ idx, (∏ i, A i ((combine rS cS) i) (idx i)) * T idx`.
    show flattenMatrix S {j} rS cS = (Pmat * (flattenMatrix T {j} * Cmat)) rS cS
    rw [flattenMatrix, hA]
    -- RHS: expand the double matrix product into `∑ rT ∑ cT, P * (MT * C)`.
    rw [Matrix.mul_apply]
    simp_rw [Matrix.mul_apply]
    -- RHS = ∑ rT, Pmat rS rT * (∑ cT, flattenMatrix T {j} rT cT * Cmat cT cS).
    -- Reindex LHS sum over `idx` via `eT : idx ≃ (rT, cT)`.
    rw [← Equiv.sum_comp eT.symm
      (fun idx : (∀ i, Fin (dT i)) =>
        (∏ i, A i (if h : i ∈ ({j} : Finset (Fin k))
          then rS ⟨i, h⟩ else cS ⟨i, h⟩) (idx i)) * T idx)]
    -- Now sum over `p : RowT × ColT`.
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl ?_
    intro rT _
    -- Pull `Pmat rS rT` out of the inner `cT`-sum on the RHS.
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro cT _
    -- Match the single term.
    -- LHS term at `(rT, cT)`: `(∏ i, A i (combine rS cS i) (eT.symm (rT,cT) i)) * T (eT.symm (rT,cT))`.
    -- Split the product over legs into the `{j}` part and the rest.
    have hsplit_prod :
        (∏ i, A i (if h : i ∈ ({j} : Finset (Fin k))
            then rS ⟨i, h⟩ else cS ⟨i, h⟩) (eT.symm (rT, cT) i))
          = Pmat rS rT * Cmat cT cS := by
      -- Product over all legs = product over `{i ∈ {j}}` times product over `{i ∉ {j}}`.
      rw [← Fintype.prod_subtype_mul_prod_subtype
        (fun i => i ∈ ({j} : Finset (Fin k)))
        (fun i => A i (if h : i ∈ ({j} : Finset (Fin k))
          then rS ⟨i, h⟩ else cS ⟨i, h⟩) (eT.symm (rT, cT) i))]
      refine congr_arg₂ (· * ·) ?_ ?_
      · -- `{i ∈ {j}}` part = `Pmat rS rT`.
        simp only [Pmat]
        refine Finset.prod_congr (by ext; simp) (fun x _ => ?_)
        obtain ⟨i, hi⟩ := x
        simp only [dif_pos hi]
        have hval : eT.symm (rT, cT) i = rT ⟨i, hi⟩ := by
          simp only [eT, Equiv.piEquivPiSubtypeProd_symm_apply, dif_pos hi]
        rw [hval]
      · -- `{i ∉ {j}}` part = `Cmat cT cS`.
        simp only [Cmat]
        refine Finset.prod_congr (by ext; simp) (fun x _ => ?_)
        obtain ⟨i, hi⟩ := x
        simp only [dif_neg hi]
        have hval : eT.symm (rT, cT) i = cT ⟨i, hi⟩ := by
          simp only [eT, Equiv.piEquivPiSubtypeProd_symm_apply, dif_neg hi]
        rw [hval]
    rw [hsplit_prod]
    -- And `T (eT.symm (rT, cT)) = flattenMatrix T {j} rT cT`.
    have harg : (eT.symm (rT, cT))
        = (fun i => if h : i ∈ ({j} : Finset (Fin k))
            then rT ⟨i, h⟩ else cT ⟨i, h⟩) := by
      funext i
      simp only [eT, Equiv.piEquivPiSubtypeProd_symm_apply]
    have hT_entry : T (eT.symm (rT, cT)) = flattenMatrix T {j} rT cT := by
      rw [flattenMatrix, harg]
    rw [hT_entry]
    ring
  -- Conclude via `Matrix.rank_mul_le`.
  unfold flatRank
  rw [hfact]
  calc (Pmat * (flattenMatrix T {j} * Cmat)).rank
      ≤ (flattenMatrix T {j} * Cmat).rank := Matrix.rank_mul_le_right _ _
    _ ≤ (flattenMatrix T {j}).rank := Matrix.rank_mul_le_left _ _

/-- **Flattening rank is bounded by the leg dimension** (Section 1.4).

    For any leg `j`, `flatRank T {j} ≤ (d j : ℕ)`: the `j`-flattening matrix has
    rows indexed by the singleton-leg index type `∀ i ∈ {j}, Fin (d i)`, whose
    cardinality is `d j`, and `Matrix.rank` is at most the number of rows. -/
lemma flatRank_le_format {k : ℕ} {d : Fin k → ℕ+}
    (T : KTensor F d) (j : Fin k) :
    flatRank T {j} ≤ (d j : ℕ) := by
  classical
  unfold flatRank
  refine le_trans (Matrix.rank_le_card_height _) ?_
  -- The row type `∀ i : {i // i ∈ {j}}, Fin (d i.val)` has cardinality `d j`.
  -- The subtype `{i // i ∈ ({j} : Finset (Fin k))}` is a singleton.
  haveI huniq : Unique {i : Fin k // i ∈ ({j} : Finset (Fin k))} := by
    refine ⟨⟨⟨j, Finset.mem_singleton_self j⟩⟩, ?_⟩
    rintro ⟨i, hi⟩
    have : i = j := Finset.mem_singleton.mp hi
    subst this
    rfl
  rw [Fintype.card_pi, Fintype.prod_unique]
  have hdef : ((default : {i : Fin k // i ∈ ({j} : Finset (Fin k))}) : Fin k) = j :=
    Finset.mem_singleton.mp (default : {i : Fin k // i ∈ ({j} : Finset (Fin k))}).2
  simp [hdef]

open Matrix Module in
/-- **Matrix rank factorization fixing the matrix** (linear-algebra core of
    conciseness, Christandl et al., Section 1.4).

    For any matrix `M : Matrix ρ β F` of rank `r`, there are matrices
    `B : Matrix ρ (Fin r) F` (columns = a basis of the column space of `M`)
    and `A : Matrix (Fin r) ρ F` (a left inverse, `A * B = 1`) such that
    `(B * A) * M = M`, i.e. the rank-`r` projector `B * A` fixes the column
    space of `M`. This is the standard rank factorization `M = (col basis) ·
    (coordinates)` underlying the conciseness reduction in Section 1.4 ("Any tensor
    is equivalent to a concise tensor"). -/
private lemma exists_rank_factorization_fixing
    {ρ : Type*} [Fintype ρ] {β : Type*} [Fintype β]
    (M : Matrix ρ β F) {r : ℕ} (hr : M.rank = r) :
    ∃ (B : Matrix ρ (Fin r) F) (A : Matrix (Fin r) ρ F), (B * A) * M = M := by
  classical
  set V : Submodule F (ρ → F) := LinearMap.range M.mulVecLin with hV
  have hrankV : Module.finrank F V = r := by rw [← hr]; rfl
  let bV : Module.Basis (Fin r) F V := (Module.finBasisOfFinrankEq F V hrankV)
  let B : Matrix ρ (Fin r) F := fun i m => (bV m : ρ → F) i
  have hLI : LinearIndependent F (fun m => (bV m : ρ → F)) := by
    have := bV.linearIndependent
    exact (this.map' (V.subtype) (by simp [Submodule.ker_subtype]))
  have hmulVec : ∀ x : Fin r → F, B.mulVec x = ∑ m, x m • (bV m : ρ → F) := by
    intro x; funext i
    simp only [Matrix.mulVec, dotProduct, B, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl (fun m _ => by ring)
  have hinj : Function.Injective B.mulVecLin := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have hsum : ∑ m, x m • (bV m : ρ → F) = 0 := by
      rw [Matrix.mulVecLin_apply, hmulVec] at hx; exact hx
    funext m
    exact (Fintype.linearIndependent_iff.mp hLI) x hsum m
  have hrange : LinearMap.range B.mulVecLin = V := by
    apply le_antisymm
    · rw [LinearMap.range_le_iff_comap, eq_top_iff]
      intro x _
      rw [Submodule.mem_comap, Matrix.mulVecLin_apply, hmulVec]
      exact Submodule.sum_mem _ (fun m _ => Submodule.smul_mem _ _ (bV m).2)
    · intro v hv
      refine ⟨bV.repr ⟨v, hv⟩, ?_⟩
      rw [Matrix.mulVecLin_apply, hmulVec]
      -- `∑ m, (repr m) • (bV m : ρ → F) = ↑(∑ m, (repr m) • bV m) = ↑⟨v, hv⟩ = v`.
      have hsum : (∑ m, (bV.repr ⟨v, hv⟩ m) • bV m) = (⟨v, hv⟩ : V) := bV.sum_repr ⟨v, hv⟩
      have hcoe : ((∑ m, (bV.repr ⟨v, hv⟩ m) • bV m : V) : ρ → F)
          = ∑ m, (bV.repr ⟨v, hv⟩ m) • (bV m : ρ → F) := by
        rw [Submodule.coe_sum]
        exact Finset.sum_congr rfl (fun m _ => by rw [Submodule.coe_smul])
      rw [← hcoe, hsum]
  obtain ⟨g, hg⟩ := B.mulVecLin.exists_leftInverse_of_injective
    (by rw [LinearMap.ker_eq_bot]; exact hinj)
  let A : Matrix (Fin r) ρ F := LinearMap.toMatrix' g
  have hA_mulVecLin : A.mulVecLin = g := by
    rw [show A.mulVecLin = Matrix.toLin' A from (Matrix.toLin'_apply' A).symm]
    exact Matrix.toLin'_toMatrix' g
  have hAB : A * B = 1 := by
    apply Matrix.toLin'.injective
    rw [Matrix.toLin'_mul, Matrix.toLin'_one]
    have e1 : Matrix.toLin' A = A.mulVecLin := rfl
    have e2 : Matrix.toLin' B = B.mulVecLin := rfl
    rw [e1, e2, hA_mulVecLin, hg]
  refine ⟨B, A, ?_⟩
  apply Matrix.ext_iff_mulVec.mpr
  intro v
  -- `((B*A)*M) *ᵥ v = (B*A) *ᵥ (M *ᵥ v)`; `M *ᵥ v ∈ V = range B.mulVecLin`, so `= B *ᵥ y`.
  rw [← Matrix.mulVec_mulVec]
  have hmem : M.mulVec v ∈ V := by rw [hV]; exact ⟨v, rfl⟩
  rw [← hrange] at hmem
  obtain ⟨y, hy⟩ := hmem
  rw [Matrix.mulVecLin_apply] at hy
  -- `(B*A) *ᵥ (B *ᵥ y) = B *ᵥ ((A*B) *ᵥ y) = B *ᵥ y = M *ᵥ v`.
  rw [← hy, Matrix.mulVec_mulVec, Matrix.mul_assoc, ← Matrix.mulVec_mulVec,
    hAB, Matrix.one_mulVec]

/-- **Per-leg fiber-fixing matrices** (Christandl et al., Section 1.4).

    For a single leg `j`, the `j`-flattening matrix has rank `flatRank T {j}`,
    so by `exists_rank_factorization_fixing` there are leg-`j` matrices
    `Bj : Matrix (Fin (d j)) (Fin (flatRank T {j})) F` and `Aj` (transposed
    format) such that the rank-`flatRank T {j}` projector `Bj * Aj` fixes every
    leg-`j` fiber of `T`: `∑ c', (Bj Aj) c c' · T(update w j c') = T(update w j c)`.
    The fibers `c' ↦ T(update w j c')` are exactly the columns of the
    `j`-flattening, so this is the column-space-fixing property of the rank
    factorization. This is the matrix content of conciseness in Section 1.4. -/
private lemma exists_leg_fiber_fixing {k : ℕ} {d : Fin k → ℕ+}
    (T : KTensor F d) (j : Fin k) :
    ∃ (Bj : Matrix (Fin (d j)) (Fin (flatRank T {j})) F)
      (Aj : Matrix (Fin (flatRank T {j})) (Fin (d j)) F),
      ∀ (w : ∀ i, Fin (d i)) (c : Fin (d j)),
        ∑ c' : Fin (d j), (Bj * Aj) c c' * T (Function.update w j c')
          = T (Function.update w j c) := by
  classical
  haveI huniq : Unique {i : Fin k // i ∈ ({j} : Finset (Fin k))} :=
    ⟨⟨⟨j, Finset.mem_singleton_self j⟩⟩, by rintro ⟨i, hi⟩; simp [Finset.mem_singleton.mp hi]⟩
  have hdef : ((default : {i : Fin k // i ∈ ({j} : Finset (Fin k))}) : Fin k) = j :=
    Finset.mem_singleton.mp (default : {i : Fin k // i ∈ ({j} : Finset (Fin k))}).2
  let e1 := Equiv.piUnique (fun i : {i // i ∈ ({j} : Finset (Fin k))} => Fin (d i.val))
  have hd : (d (default : {i // i ∈ ({j} : Finset (Fin k))}).val : ℕ) = (d j : ℕ) := by rw [hdef]
  let eRow := e1.trans (finCongr hd)
  -- Value of `eRow.symm cc` at the unique row index has `.val = cc.val`.
  have hvalj : ∀ (cc : Fin (d j)) (h : j ∈ ({j} : Finset (Fin k))),
      ((eRow.symm cc) ⟨j, h⟩).val = cc.val := by
    intro cc h
    have hround : eRow (eRow.symm cc) = cc := eRow.apply_symm_apply cc
    have hap : eRow (eRow.symm cc) = finCongr hd ((eRow.symm cc) default) := rfl
    rw [hap] at hround
    have hval_default : ((eRow.symm cc) default).val = cc.val := by
      have := congrArg Fin.val hround
      simpa [finCongr] using! this
    have hpe : (⟨j, h⟩ : {i // i ∈ ({j} : Finset (Fin k))}) = default := Subsingleton.elim _ _
    rw [show ((eRow.symm cc) ⟨j, h⟩).val = ((eRow.symm cc) default).val from by rw [hpe]]
    exact hval_default
  set Mflat := flattenMatrix T {j} with hMflat
  let Mj : Matrix (Fin (d j)) (∀ i : {i // i ∉ ({j} : Finset (Fin k))}, Fin (d i.val)) F :=
    Mflat.submatrix eRow.symm (Equiv.refl _)
  have hrankMj : Mj.rank = flatRank T {j} := by
    change (Mflat.submatrix eRow.symm (Equiv.refl _)).rank = (flattenMatrix T {j}).rank
    rw [hMflat, Matrix.rank_submatrix Mflat eRow.symm (Equiv.refl _)]
  obtain ⟨B, A, hBA⟩ := exists_rank_factorization_fixing Mj hrankMj
  refine ⟨B, A, ?_⟩
  intro w c
  set colW : (∀ i : {i // i ∉ ({j} : Finset (Fin k))}, Fin (d i.val)) := fun i => w i.val with hcolW
  have hentry : ∀ (cc : Fin (d j)), Mj cc colW = T (Function.update w j cc) := by
    intro cc
    change Mflat (eRow.symm cc) (Equiv.refl _ colW) = T (Function.update w j cc)
    rw [hMflat]
    change flattenMatrix T {j} (eRow.symm cc) colW = T (Function.update w j cc)
    unfold flattenMatrix
    congr 1
    funext m
    by_cases h : m ∈ ({j} : Finset (Fin k))
    · rw [dif_pos h]
      have hmj : m = j := Finset.mem_singleton.mp h
      subst hmj
      rw [Function.update_self]
      apply Fin.ext; exact hvalj cc h
    · rw [dif_neg h]
      have hmj : m ≠ j := fun he => h (he ▸ Finset.mem_singleton_self j)
      rw [Function.update_of_ne hmj, hcolW]
  calc ∑ c' : Fin (d j), (B * A) c c' * T (Function.update w j c')
      = ∑ c' : Fin (d j), (B * A) c c' * Mj c' colW := by
          refine Finset.sum_congr rfl (fun c' _ => ?_); rw [hentry c']
    _ = ((B * A) * Mj) c colW := by rw [Matrix.mul_apply]
    _ = Mj c colW := by rw [hBA]
    _ = T (Function.update w j c) := hentry c

/-- **Single-leg application fixes `T`** (Section 1.4). Applying the projector
    `C j` on leg `j` (and identity elsewhere) fixes `T`, provided `C j` fixes
    every leg-`j` fiber of `T` (`hfix`). -/
private lemma applyLegTensor_single_leg_fix {k : ℕ} {d : Fin k → ℕ+} (j : Fin k)
    (C : ∀ i, Matrix (Fin (d i)) (Fin (d i)) F) (T : KTensor F d)
    (hfix : ∀ (w : ∀ i, Fin (d i)) (c : Fin (d j)),
      ∑ c' : Fin (d j), C j c c' * T (Function.update w j c') = T (Function.update w j c)) :
    applyLegTensor (fun i => if i = j then C i else (1 : Matrix (Fin (d i)) (Fin (d i)) F)) T = T := by
  classical
  funext jdx
  unfold applyLegTensor
  have hprod : ∀ idx : (∀ i, Fin (d i)),
      (∏ i, (if i = j then C i else (1 : Matrix (Fin (d i)) (Fin (d i)) F)) (jdx i) (idx i)) * T idx
        = (if (∀ i ∈ Finset.univ.erase j, jdx i = idx i) then (1 : F) else 0)
            * (C j (jdx j) (idx j) * T idx) := by
    intro idx
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ j), mul_comm (∏ _ ∈ _, _), if_pos rfl]
    have hrest : (∏ i ∈ Finset.univ.erase j,
        (if i = j then C i else (1 : Matrix (Fin (d i)) (Fin (d i)) F)) (jdx i) (idx i))
        = ∏ i ∈ Finset.univ.erase j, (if jdx i = idx i then (1 : F) else 0) := by
      refine Finset.prod_congr rfl (fun i hi => ?_)
      simp only [if_neg (Finset.ne_of_mem_erase hi), Matrix.one_apply]
    rw [hrest, Finset.prod_boole]; ring
  simp_rw [hprod]
  -- Reindex: only `idx` agreeing with `jdx` off leg `j` survive; reindex by `c = idx j`.
  rw [show (∑ idx : (∀ i, Fin (d i)),
        (if (∀ i ∈ Finset.univ.erase j, jdx i = idx i) then (1 : F) else 0)
          * (C j (jdx j) (idx j) * T idx))
      = ∑ c : Fin (d j), C j (jdx j) c * T (Function.update jdx j c) from ?_]
  · rw [hfix jdx (jdx j), Function.update_eq_self]
  · -- the reindexing identity
    have step1 : (∑ idx : (∀ i, Fin (d i)),
          (if (∀ i ∈ Finset.univ.erase j, jdx i = idx i) then (1 : F) else 0)
            * (C j (jdx j) (idx j) * T idx))
        = ∑ idx ∈ Finset.univ.filter (fun idx => ∀ i ∈ Finset.univ.erase j, jdx i = idx i),
            (C j (jdx j) (idx j) * T idx) := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl (fun idx _ => ?_)
      by_cases h : ∀ i ∈ Finset.univ.erase j, jdx i = idx i <;> simp [h]
    rw [step1]
    refine Finset.sum_bij'
      (i := fun (idx : ∀ i, Fin (d i)) _ => idx j)
      (j := fun (c : Fin (d j)) _ => Function.update jdx j c)
      (fun idx _ => Finset.mem_univ _)
      ?_ ?_ ?_ ?_
    · intro c _
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      intro i hi
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
    · intro idx hidx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hidx
      funext i
      by_cases h : i = j
      · subst h; simp
      · simp only [Function.update_of_ne h]
        exact hidx i (Finset.mem_erase.mpr ⟨h, Finset.mem_univ _⟩)
    · intro c _; simp
    · intro idx hidx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hidx
      have hupd : Function.update jdx j (idx j) = idx := by
        funext i
        by_cases h : i = j
        · subst h; simp
        · simp only [Function.update_of_ne h]
          exact hidx i (Finset.mem_erase.mpr ⟨h, Finset.mem_univ _⟩)
      rw [hupd]

/-- **All-identity leg application is the identity** (Section 1.4). -/
private lemma applyLegTensor_one {k : ℕ} {d : Fin k → ℕ+} (T : KTensor F d) :
    applyLegTensor (fun i => (1 : Matrix (Fin (d i)) (Fin (d i)) F)) T = T := by
  classical
  funext jdx
  unfold applyLegTensor
  rw [Finset.sum_eq_single jdx]
  · rw [show (∏ i, (1 : Matrix (Fin (d i)) (Fin (d i)) F) (jdx i) (jdx i)) = 1 by
      simp [Matrix.one_apply], one_mul]
  · intro idx _ hne
    have hex : ∃ i, jdx i ≠ idx i := by
      by_contra h; push_neg at h; exact hne (funext fun i => (h i).symm)
    obtain ⟨i, hi⟩ := hex
    have hzero : (1 : Matrix (Fin (d i)) (Fin (d i)) F) (jdx i) (idx i) = 0 := by
      simp [Matrix.one_apply, hi]
    rw [Finset.prod_eq_zero (Finset.mem_univ i) hzero, zero_mul]
  · intro h; exact absurd (Finset.mem_univ jdx) h

/-- **Simultaneous leg-projector application fixes `T`** (Section 1.4). If each
    leg-`j` projector `C j` fixes the leg-`j` fibers of `T`, then applying all
    `C j` simultaneously fixes `T`. Proven by `Finset` induction over legs:
    `applyLegTensor (fun i => if i ∈ S then C i else 1) T = T`, peeling one leg
    at a time via `applyLegTensor_comp` and `applyLegTensor_single_leg_fix`. -/
private lemma applyLegTensor_fix_of_forall_fiber {k : ℕ} {d : Fin k → ℕ+}
    (C : ∀ i, Matrix (Fin (d i)) (Fin (d i)) F) (T : KTensor F d)
    (hfix : ∀ (j : Fin k) (w : ∀ i, Fin (d i)) (c : Fin (d j)),
      ∑ c' : Fin (d j), C j c c' * T (Function.update w j c') = T (Function.update w j c)) :
    applyLegTensor C T = T := by
  classical
  have key : ∀ S : Finset (Fin k),
      applyLegTensor (fun i => if i ∈ S then C i else (1 : Matrix (Fin (d i)) (Fin (d i)) F)) T
        = T := by
    intro S
    induction S using Finset.induction with
    | empty => simpa using! applyLegTensor_one T
    | @insert j S' hj ih =>
      have hfactor :
          (fun i => if i ∈ insert j S' then C i else (1 : Matrix (Fin (d i)) (Fin (d i)) F))
            = fun i => (if i = j then C i else 1) * (if i ∈ S' then C i else 1) := by
        funext i
        by_cases hij : i = j
        · subst hij
          simp only [Finset.mem_insert, true_or, if_true, if_pos rfl]
          rw [if_neg hj, mul_one]
        · simp only [Finset.mem_insert, hij, false_or, if_neg hij]
          by_cases hiS : i ∈ S' <;> simp [hiS]
      rw [hfactor,
        ← applyLegTensor_comp (fun i => if i = j then C i else 1)
          (fun i => if i ∈ S' then C i else 1) T,
        ih, applyLegTensor_single_leg_fix j C T (hfix j)]
  simpa using! key Finset.univ

/-- **Per-leg projection/section factorization** (Christandl et al., Section 1.4).

    Paper verbatim (Section 1.4): "A tensor `T ∈ 𝔽^{d_1} ⊗ ⋯ ⊗ 𝔽^{d_k}` is called
    concise if ... Any tensor is equivalent to a concise tensor."

    The matrix rank-factorization content of conciseness: for each leg `j`, the
    `j`-flattening matrix `M_j := flattenMatrix T {j}` has column rank
    `r_j := flatRank T {j}`. We provide leg-wise projection matrices
    `A j : Matrix (Fin (r_j')) (Fin (d j)) F` and section matrices
    `B j : Matrix (Fin (d j)) (Fin (r_j')) F` onto a `ℕ+` format `r' = d'`
    with `(d' j : ℕ) = r_j`, such that the leg-wise composition `B_j A_j`
    leaves `T` invariant: `applyLegTensor (fun i => B i * A i) T = T`.

    Concretely `B_j` has columns forming a basis of the column space of `M_j`
    (full column rank `r_j`) and `A_j` is a left inverse of `B_j` (`A_j B_j = 1`);
    then `B_j A_j` is the identity on the column space of `M_j`, which contains
    every leg-`j` fiber of `T`, so the leg-wise composition fixes `T`. -/
lemma exists_flattening_projection_section {k : ℕ} {d : Fin k → ℕ+}
    (T : KTensor F d) (hT : ∀ j, 1 ≤ flatRank T {j}) :
    ∃ (d' : Fin k → ℕ+)
      (A : ∀ i : Fin k, Matrix (Fin (d' i)) (Fin (d i)) F)
      (B : ∀ i : Fin k, Matrix (Fin (d i)) (Fin (d' i)) F),
      (∀ j, (d' j : ℕ) = flatRank T {j}) ∧
        applyLegTensor (fun i => B i * A i) T = T := by
  classical
  -- Format `d' j := flatRank T {j}` (positive by hypothesis `hT`).
  refine ⟨fun j => ⟨flatRank T {j}, hT j⟩, ?_⟩
  -- Per-leg fiber-fixing matrices `Bj, Aj` from the rank factorization.
  choose B A hfix using fun j => exists_leg_fiber_fixing T j
  refine ⟨A, B, fun j => rfl, ?_⟩
  -- Simultaneous leg application fixes `T` because each `Bj Aj` fixes leg-`j` fibers.
  exact applyLegTensor_fix_of_forall_fiber (fun i => B i * A i) T hfix

/-- **Existence of a concise restriction** (Christandl et al., Section 1.4).

    Paper verbatim (Section 1.4): "A tensor `T ∈ 𝔽^{d_1} ⊗ ⋯ ⊗ 𝔽^{d_k}` is called
    concise if for every `i ∈ [k]`, the flattening rank
    `tensorrank_i(T) = tensorrank_{{i}}(T)` equals `d_i`. Any tensor is
    equivalent to a concise tensor."

    Construction: for each leg `j`, the column space of the `j`-flattening
    has dimension `r_j = flatRank T {j}`. Choose a rank-`r_j` factorization
    `M_j = B_j ∘ A_j` where `A_j : F^{d j} → F^{r_j}` is the projection to
    a basis of the column space and `B_j : F^{r_j} → F^{d j}` is the
    inclusion (`exists_flattening_projection_section`). Then
    `T' := applyLegTensor A T : KTensor F (fun j => r_j)` satisfies:
    * `T' ≤ T` via `A` (`applyLegTensor_restricts`);
    * `T ≤ T'` via `B`, since `applyLegTensor B T' = applyLegTensor (B·A) T = T`;
    * `flatRank T' {j} = r_j = d' j` (conciseness), from
      `r_j = flatRank T {j} ≤ flatRank T' {j}` (`Restricts.flatRank_mono` on
      `T ≤ T'`) and `flatRank T' {j} ≤ (d' j : ℕ) = r_j` (`flatRank_le_format`).

    Restriction to the non-degenerate case `r_j ≥ 1` for all `j` (i.e.,
    `T ≠ 0`): the construction above requires `d' j = r_j ∈ ℕ+`, hence
    `r_j ≥ 1`. Equivalently (since `flatRank T {j} = 0` for some `j` iff
    `T = 0`), the hypothesis is `T ≠ 0`. -/
lemma exists_concise_restriction {k : ℕ} {d : Fin k → ℕ+}
    (T : KTensor F d) (hT : T ≠ 0) :
    ∃ (d' : Fin k → ℕ+) (T' : KTensor F d'),
      Restricts T' T ∧ Restricts T T' ∧ ∀ j, (d' j : ℕ) = flatRank T' {j} := by
  classical
  -- Every leg has `flatRank T {j} ≥ 1` since `T ≠ 0`.
  have hpos : ∀ j, 1 ≤ flatRank T {j} := by
    intro j
    by_contra h
    push_neg at h
    -- `flatRank T {j} = 0` ⟹ `flattenMatrix T {j} = 0` ⟹ `T = 0`.
    have hzero : flatRank T {j} = 0 := by omega
    exact absurd (flatRank_zero_imp_zero T j hzero) hT
  -- Obtain the per-leg projection/section matrices.
  obtain ⟨d', A, B, hdim, hrecover⟩ :=
    exists_flattening_projection_section T hpos
  -- The concise witness.
  refine ⟨d', applyLegTensor A T, ?_, ?_, ?_⟩
  · -- `T' ≤ T` via `A`.
    exact applyLegTensor_restricts A T
  · -- `T ≤ T'`: `applyLegTensor B (applyLegTensor A T) = applyLegTensor (B·A) T = T`.
    -- So `T ≤ applyLegTensor A T` via the witness `B`.
    refine ⟨B, ?_⟩
    intro jdx
    -- `T jdx = applyLegTensor B (applyLegTensor A T) jdx`.
    have hcomp : applyLegTensor B (applyLegTensor A T)
        = applyLegTensor (fun i => B i * A i) T :=
      applyLegTensor_comp B A T
    have : applyLegTensor B (applyLegTensor A T) = T := by
      rw [hcomp, hrecover]
    calc T jdx = applyLegTensor B (applyLegTensor A T) jdx := by rw [this]
      _ = ∑ idx, (∏ i, B i (jdx i) (idx i)) * applyLegTensor A T idx := rfl
  · -- Conciseness: `(d' j : ℕ) = flatRank (applyLegTensor A T) {j}`.
    intro j
    have hTle : Restricts T (applyLegTensor A T) := by
      refine ⟨B, ?_⟩
      intro jdx
      have hcomp : applyLegTensor B (applyLegTensor A T)
          = applyLegTensor (fun i => B i * A i) T :=
        applyLegTensor_comp B A T
      have heq : applyLegTensor B (applyLegTensor A T) = T := by rw [hcomp, hrecover]
      calc T jdx = applyLegTensor B (applyLegTensor A T) jdx := by rw [heq]
        _ = ∑ idx, (∏ i, B i (jdx i) (idx i)) * applyLegTensor A T idx := rfl
    -- `r_j ≤ flatRank T' {j}` from monotonicity on `T ≤ T'`.
    have hge : flatRank T {j} ≤ flatRank (applyLegTensor A T) {j} :=
      hTle.flatRank_mono j
    -- `flatRank T' {j} ≤ (d' j : ℕ) = r_j`.
    have hle : flatRank (applyLegTensor A T) {j} ≤ (d' j : ℕ) :=
      flatRank_le_format (applyLegTensor A T) j
    rw [hdim j] at hle ⊢
    omega

/-- **Zero-padded re-embedding** (Corollary 2.6, Cor 2.6 helper).

For formats `d ≤ d''` componentwise, the canonical zero-padded re-embedding
extends `T : KTensor F d` to `KTensor F d''` by setting
`reembed h T idx = T (idx restricted)` whenever `(idx j : ℕ) < (d j : ℕ)` for
all `j`, and `0` otherwise.

Corollary 2.6 (verbatim): "By re-embedding the `T_i`, we see that the `r_i`
are all contained in `{R̃(T) : T ∈ F^d ⊗ ⋯ ⊗ F^d}` where `d = ⌊r_1⌋`." -/
noncomputable def reembed {k : ℕ} {d d'' : Fin k → ℕ+}
    (h : ∀ j, (d j : ℕ) ≤ (d'' j : ℕ)) (T : KTensor F d) : KTensor F d'' :=
  fun idx =>
    if h_in : ∀ j, (idx j : ℕ) < (d j : ℕ)
      then T (fun j => ⟨(idx j : ℕ), h_in j⟩)
      else 0

/-- **Re-embedding restricts to `T`** (Corollary 2.6, Section 1.4).

The zero-padded re-embedding `reembed h T` admits `T` as a restriction along
the leg-wise projection matrices `A_j : Matrix (Fin (d j)) (Fin (d'' j)) F`
defined by `A_j jdx idx = 1` if `(idx : ℕ) = (jdx : ℕ)` and `0` otherwise.
This is the "truncate to the first `d j` coordinates" map; applied to
`reembed h T`, it returns `T jdx`. -/
lemma reembed_restricts_to {k : ℕ} {d d'' : Fin k → ℕ+}
    (h : ∀ j, (d j : ℕ) ≤ (d'' j : ℕ)) (T : KTensor F d) :
    Restricts T (reembed h T) := by
  classical
  -- A_j (jdx) (idx) = 1 if (idx : ℕ) = (jdx : ℕ), else 0.
  refine ⟨fun j =>
    Matrix.of (fun (jdx : Fin (d j)) (idx : Fin (d'' j)) =>
      if (idx : ℕ) = (jdx : ℕ) then (1 : F) else 0), ?_⟩
  intro jdx
  -- The only nonzero term in the sum is at
  -- `idx⋆ j := ⟨jdx j, lt_of_lt_of_le (jdx j).2 (h j)⟩`.
  set idxStar : (∀ i : Fin k, Fin (d'' i)) :=
    fun j => ⟨(jdx j : ℕ), lt_of_lt_of_le (jdx j).2 (h j)⟩ with hidxStar_def
  rw [Finset.sum_eq_single idxStar]
  · -- At idx = idxStar: product = 1, and `reembed h T idxStar = T jdx`.
    have hprod :
        (∏ i, (Matrix.of (fun (jdx' : Fin (d i)) (idx' : Fin (d'' i)) =>
          if (idx' : ℕ) = (jdx' : ℕ) then (1 : F) else 0))
            (jdx i) (idxStar i)) = 1 := by
      apply Finset.prod_eq_one
      intro i _
      simp [Matrix.of_apply, hidxStar_def]
    -- reembed unfolds at idxStar: all coords (idxStar j : ℕ) = (jdx j : ℕ) < d j.
    have hin : ∀ j, ((idxStar j : Fin (d'' j)) : ℕ) < (d j : ℕ) := by
      intro j
      simp [hidxStar_def]
    have hreembed :
        reembed h T idxStar = T jdx := by
      simp only [reembed, dif_pos hin]
      -- The argument `fun j => ⟨(idxStar j : ℕ), hin j⟩` is defeq to `jdx`.
      rfl
    rw [hprod, hreembed, one_mul]
  · -- For idx ≠ idxStar: ∃ i₀ with (idx i₀ : ℕ) ≠ (jdx i₀ : ℕ), so factor = 0.
    intro idx _ hne
    have hex : ∃ i₀, ((idx i₀ : Fin (d'' i₀)) : ℕ) ≠ ((jdx i₀ : Fin (d i₀)) : ℕ) := by
      by_contra hall
      push_neg at hall
      -- If all (idx i : ℕ) = (jdx i : ℕ), then idx = idxStar.
      apply hne
      funext i
      apply Fin.ext
      simp [hidxStar_def]
      exact hall i
    obtain ⟨i₀, hi₀⟩ := hex
    have hzero :
        (Matrix.of (fun (jdx' : Fin (d i₀)) (idx' : Fin (d'' i₀)) =>
          if (idx' : ℕ) = (jdx' : ℕ) then (1 : F) else 0))
            (jdx i₀) (idx i₀) = 0 := by
      simp [Matrix.of_apply, hi₀]
    have hprod_zero :
        (∏ i, (Matrix.of (fun (jdx' : Fin (d i)) (idx' : Fin (d'' i)) =>
          if (idx' : ℕ) = (jdx' : ℕ) then (1 : F) else 0))
            (jdx i) (idx i)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i₀) hzero
    rw [hprod_zero, zero_mul]
  · intro hne; exact absurd (Finset.mem_univ _) hne

/-- **`T` restricts to its re-embedding** (Corollary 2.6, Section 1.4).

The zero-padded re-embedding is a restriction of `T` along the leg-wise
inclusion matrices `B_j : Matrix (Fin (d'' j)) (Fin (d j)) F` defined by
`B_j jdx idx = 1` if `(jdx : ℕ) = (idx : ℕ)` and `0` otherwise. This is
the canonical inclusion `F^{d j} ↪ F^{d'' j}`; applied to `T`, it produces
exactly `reembed h T`. -/
lemma restricts_reembed {k : ℕ} {d d'' : Fin k → ℕ+}
    (h : ∀ j, (d j : ℕ) ≤ (d'' j : ℕ)) (T : KTensor F d) :
    Restricts (reembed h T) T := by
  classical
  -- B_j (jdx) (idx) = 1 if (jdx : ℕ) = (idx : ℕ), else 0.
  refine ⟨fun j =>
    Matrix.of (fun (jdx : Fin (d'' j)) (idx : Fin (d j)) =>
      if (jdx : ℕ) = (idx : ℕ) then (1 : F) else 0), ?_⟩
  intro jdx
  -- Case split on whether all (jdx j : ℕ) < (d j : ℕ).
  by_cases hin : ∀ j, ((jdx j : Fin (d'' j)) : ℕ) < (d j : ℕ)
  · -- All coords in the "small box": only term at idxStar j := ⟨jdx j, hin j⟩.
    set idxStar : (∀ i : Fin k, Fin (d i)) :=
      fun j => ⟨((jdx j : Fin (d'' j)) : ℕ), hin j⟩ with hidxStar_def
    rw [Finset.sum_eq_single idxStar]
    · have hprod :
          (∏ i, (Matrix.of (fun (jdx' : Fin (d'' i)) (idx' : Fin (d i)) =>
            if (jdx' : ℕ) = (idx' : ℕ) then (1 : F) else 0))
              (jdx i) (idxStar i)) = 1 := by
        apply Finset.prod_eq_one
        intro i _
        simp [Matrix.of_apply, hidxStar_def]
      have hreembed : reembed h T jdx = T idxStar := by
        simp only [reembed, dif_pos hin]
        rfl
      rw [hprod, hreembed, one_mul]
    · -- For idx ≠ idxStar: ∃ i₀ with (jdx i₀ : ℕ) ≠ (idx i₀ : ℕ), factor 0.
      intro idx _ hne
      have hex : ∃ i₀, ((jdx i₀ : Fin (d'' i₀)) : ℕ) ≠ ((idx i₀ : Fin (d i₀)) : ℕ) := by
        by_contra hall
        push_neg at hall
        apply hne
        funext i
        apply Fin.ext
        simp [hidxStar_def]
        exact (hall i).symm
      obtain ⟨i₀, hi₀⟩ := hex
      have hzero :
          (Matrix.of (fun (jdx' : Fin (d'' i₀)) (idx' : Fin (d i₀)) =>
            if (jdx' : ℕ) = (idx' : ℕ) then (1 : F) else 0))
              (jdx i₀) (idx i₀) = 0 := by
        simp [Matrix.of_apply, hi₀]
      have hprod_zero :
          (∏ i, (Matrix.of (fun (jdx' : Fin (d'' i)) (idx' : Fin (d i)) =>
            if (jdx' : ℕ) = (idx' : ℕ) then (1 : F) else 0))
              (jdx i) (idx i)) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ i₀) hzero
      rw [hprod_zero, zero_mul]
    · intro hne; exact absurd (Finset.mem_univ _) hne
  · -- ∃ j₀ with (jdx j₀ : ℕ) ≥ (d j₀ : ℕ). Then `reembed h T jdx = 0` and
    -- every term in the sum has the `j₀`-factor = 0 (since (idx j₀ : ℕ) < d j₀
    -- ≤ (jdx j₀ : ℕ)).
    push_neg at hin
    obtain ⟨j₀, hj₀⟩ := hin
    have hnotin : ¬ (∀ j, ((jdx j : Fin (d'' j)) : ℕ) < (d j : ℕ)) := by
      push_neg; exact ⟨j₀, hj₀⟩
    have hreembed_zero : reembed h T jdx = 0 := by
      simp only [reembed, dif_neg hnotin]
    rw [hreembed_zero]
    -- Now show ∑ idx, (...) * T idx = 0.
    symm
    apply Finset.sum_eq_zero
    intro idx _
    have hne : ((jdx j₀ : Fin (d'' j₀)) : ℕ) ≠ ((idx j₀ : Fin (d j₀)) : ℕ) := by
      intro heq
      have : ((idx j₀ : Fin (d j₀)) : ℕ) < (d j₀ : ℕ) := (idx j₀).2
      omega
    have hzero :
        (Matrix.of (fun (jdx' : Fin (d'' j₀)) (idx' : Fin (d j₀)) =>
          if (jdx' : ℕ) = (idx' : ℕ) then (1 : F) else 0))
            (jdx j₀) (idx j₀) = 0 := by
      simp [Matrix.of_apply, hne]
    have hprod_zero :
        (∏ i, (Matrix.of (fun (jdx' : Fin (d'' i)) (idx' : Fin (d i)) =>
          if (jdx' : ℕ) = (idx' : ℕ) then (1 : F) else 0))
            (jdx i) (idx i)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ j₀) hzero
    rw [hprod_zero, zero_mul]

/-- **Re-embedding preserves `asympRank`** (Section 1.4 and Corollary 2.6; Cor 2.6 helper).

For `d ≤ d''` componentwise, the canonical zero-padded re-embedding sends a
`k`-tensor of format `d` to a `k`-tensor of format `d''` with the same
asymptotic rank. The proof of Corollary 2.6 uses this implicitly when it writes
"by re-embedding the `T_i`". The re-embedding is equivalence-preserving (each
direction is a restriction along the canonical inclusion / projection maps),
hence preserves every admissible functional. -/
lemma exists_reembed_of_le {k : ℕ} {d d'' : Fin k → ℕ+}
    (h : ∀ j, (d j : ℕ) ≤ (d'' j : ℕ)) (T : KTensor F d) :
    ∃ T'' : KTensor F d'', asympRank T'' = asympRank T := by
  refine ⟨reembed h T, ?_⟩
  -- `T ≤ reembed h T` and `reembed h T ≤ T`, so `asympRank` is equal.
  exact Restricts.asympRank_eq_of_equiv (restricts_reembed h T) (reembed_restricts_to h T)

/-- **Flattening-rank lower bound** (Section 1.4 and Corollary 2.6; helper for Cor 2.6).

The matrix-rank flattening `R_j(T)` is a lower bound on the asymptotic rank
`R̃(T)`. Formally, for any leg `j ∈ Fin k`, `flatRank T {j} ≤ R̃(T)`.

Standard fact: tensor rank lower-bounds matrix-rank flattenings (Section 1.4),
and the matrix-rank flattening is multiplicative under Kronecker product
(Section 1.4), so `flatRank (T^{⊠n}) {j} = flatRank T {j}^n` and hence
`tensorRank (T^{⊠n})^{1/n} ≥ flatRank T {j}^{n · (1/n)} = flatRank T {j}`.
The per-`n` inequality is packaged in `flatRank_pow_le_tensorRank_regroupingMap`;
this lemma takes the `n`-th root and infs over `n`. -/
lemma flatRank_le_asympRank {k : ℕ} {d : Fin k → ℕ+}
    (T : KTensor F d) (j : Fin k) :
    (flatRank T {j} : ℝ) ≤ asympRank T := by
  -- Edge case: `k = 0` is degenerate (no legs); `j : Fin 0` is uninhabited.
  by_cases hk : 1 ≤ k
  · -- `asympRank T = ⨅ n, (tensorRank (regroupingMap d n (T^⊗n)) : ℝ)^(1/n)`.
    unfold asympRank
    simp only [dif_pos hk]
    unfold AdmissibleFunctional.regularize
    -- Goal: `flatRank T {j} ≤ ⨅ n, …^(1/n)`. Use `le_ciInf`.
    refine le_ciInf fun n => ?_
    -- Unfold `tensorRankAdmissible.toFun`.
    change (flatRank T {j} : ℝ) ≤
      ((((tensorRank
        (regroupingMap d n
          (tensorPow (F := F) (V := KTensor F d) n T))) : ℕ) : NNReal) : ℝ) ^
      ((1 : ℝ) / (n : ℕ))
    -- Set `r := flatRank T {j}` and `Rn := tensorRank (regroupingMap d n (T^⊗n))`.
    set r : ℝ := (flatRank T {j} : ℝ) with hr_def
    set Rn : ℝ := ((tensorRank
        (regroupingMap d n (tensorPow (F := F) (V := KTensor F d) n T)) : ℕ) : ℝ)
      with hRn_def
    have hr_nn : 0 ≤ r := by
      rw [hr_def]; exact_mod_cast Nat.zero_le _
    have hRn_nn : 0 ≤ Rn := by
      rw [hRn_def]; exact_mod_cast Nat.zero_le _
    -- Key per-`n` inequality: `r^n ≤ Rn`.
    have hkey : r ^ (n : ℕ) ≤ Rn := by
      have := flatRank_pow_le_tensorRank_regroupingMap (F := F) T j n
      simpa [hr_def, hRn_def] using! this
    -- The NNReal-cast on the RHS simplifies to a plain `ℕ → ℝ` cast.
    have hcoe :
        ((((tensorRank
          (regroupingMap d n
            (tensorPow (F := F) (V := KTensor F d) n T))) : ℕ) : NNReal) : ℝ) = Rn := by
      simp [hRn_def]
    rw [hcoe]
    -- Now goal: `r ≤ Rn^(1/n)`. Equivalent to `r^n ≤ Rn` for `r ≥ 0`, `n ≥ 1`.
    have h1 : r ^ ((n : ℕ) : ℝ) ≤ Rn := by
      have hrpow_eq : r ^ ((n : ℕ) : ℝ) = r ^ (n : ℕ) :=
        Real.rpow_natCast r (n : ℕ)
      rw [hrpow_eq]; exact hkey
    have hinv : (0 : ℝ) ≤ (1 : ℝ) / (n : ℕ) := by positivity
    have h2 :
        (r ^ ((n : ℕ) : ℝ)) ^ ((1 : ℝ) / (n : ℕ)) ≤
          Rn ^ ((1 : ℝ) / (n : ℕ)) :=
      Real.rpow_le_rpow (Real.rpow_nonneg hr_nn _) h1 hinv
    have hpow_simp : (r ^ ((n : ℕ) : ℝ)) ^ ((1 : ℝ) / (n : ℕ)) = r := by
      rw [← Real.rpow_mul hr_nn]
      have hmul : ((n : ℕ) : ℝ) * ((1 : ℝ) / (n : ℕ)) = 1 := by
        field_simp
      rw [hmul, Real.rpow_one]
    rw [hpow_simp] at h2
    exact h2
  · -- `k = 0`: `j : Fin 0` is uninhabited.
    have hk0 : k = 0 := by omega
    subst hk0
    exact j.elim0

/-- **Re-embedding** (Corollary 2.6; helper for Cor 2.6).

A `k`-tensor of format `d` embeds (as a `k`-tensor with zero-padding on each
leg) into any larger format `d''` with `d j ≤ d'' j` for all `j`, preserving
asymptotic rank. -/
lemma exists_reembed {k : ℕ} {d d'' : Fin k → ℕ+}
    (h : ∀ j, (d j : ℕ) ≤ (d'' j : ℕ)) (T : KTensor F d) :
    ∃ T'' : KTensor F d'', asympRank T'' = asympRank T :=
  exists_reembed_of_le h T

/-- **Corollary 2.6**.

The set `{R̃(T) : T ∈ F^{d_1} ⊗ ⋯ ⊗ F^{d_k}, d ∈ ℤ_{≥1}^k}` is well-ordered.

Proof (Corollary 2.6): a non-increasing sequence `r₁ ≥ r₂ ≥ ⋯` with witnesses
`T_i : KTensor F d_i` and `R̃(T_i) = r_i`. For each *positive* value `r_i`,
replace `T_i` by a concise equivalent `T_i' : KTensor F d_i'` (Section 1.4, via
`exists_concise_restriction`); then `d_i' j = R_j(T_i') ≤ R̃(T_i') = r_i ≤ r_1`.
The well-ordering floor `r_i = 0` needs no concise equivalent: it is realized
in any format by the zero tensor (`asympRank_zero`). So every value `r_i` has a
bounded-format witness, hence re-embeds into the single fixed format
`d_★ = (fun _ => max 1 ⌈r_1⌉₊)`. Corollary 2.5 (well-ordered values per format)
applied to `tensorRankAdmissible F hk d_★` then contradicts strict descent of
`r_1, r_2, …`.

(This avoids the `T = 0` conciseness edge case: the paper's Corollary 2.6 only
picks concise witnesses for the actual positive values; `0` is handled by the
well-ordering floor.) -/
theorem wellOrdered_asympRank_alltensors {k : ℕ} (hk : 1 ≤ k) :
    WellFoundedLT
      (⋃ d : Fin k → ℕ+, Set.range (fun T : KTensor F d => asympRank T)) := by
  classical
  -- Set-theoretic shorthand for the union.
  set S : Set ℝ := ⋃ d : Fin k → ℕ+, Set.range (fun T : KTensor F d => asympRank T)
    with hS_def
  unfold WellFoundedLT  -- (v4.34: WellFoundedLT is now `WellFounded (· < ·)`, no IsWellFounded wrapper)
  rw [RelEmbedding.wellFounded_iff_isEmpty]
  refine ⟨fun e => ?_⟩
  -- Extract the strictly decreasing sequence `r : ℕ → ℝ`.
  set r : ℕ → ℝ := fun k => (e k : ℝ) with hr_def
  have hr_anti : StrictAnti r := fun k m hkm => e.map_rel_iff.mpr hkm
  -- Each `r i` is realized in some format.
  have hr_mem : ∀ i, r i ∈ S := fun i => (e i).2
  have hr_raw : ∀ i, ∃ (d : Fin k → ℕ+) (T : KTensor F d), asympRank T = r i := by
    intro i
    have := hr_mem i
    simp only [hS_def, Set.mem_iUnion, Set.mem_range] at this
    obtain ⟨d, T, hT⟩ := this
    exact ⟨d, T, hT⟩
  choose dRaw TRaw hTRaw using hr_raw
  -- Bounds on `r`.
  have hr_bdd : ∀ i, r i ≤ r 0 := by
    intro i
    rcases Nat.eq_zero_or_pos i with h0 | hpos
    · simp [h0]
    · exact (hr_anti hpos).le
  -- `r 0 ≥ 0` since `r 0 = R̃(TRaw 0) ≥ 0`.
  have hr0_nonneg : 0 ≤ r 0 := by
    rw [← hTRaw 0]; exact asympRank_nonneg _
  -- The uniform format dimension: `N = max 1 ⌈r 0⌉₊ ≥ 1`.
  set N : ℕ := max 1 ⌈r 0⌉₊ with hN_def
  have hN_pos : 0 < N := lt_of_lt_of_le Nat.one_pos (le_max_left _ _)
  -- Cast `N : ℕ` to a `ℕ+` for use as a format component.
  set Npos : ℕ+ := ⟨N, hN_pos⟩ with hNpos_def
  set dStar : Fin k → ℕ+ := fun _ => Npos with hdStar_def
  -- **Bounded-format witness for each value `r i`** (Corollary 2.6).
  --
  -- The paper picks a *concise* witness for each `r_i`, then bounds its
  -- format `d_i' j = R_j(T_i') ≤ R̃(T_i') = r_i ≤ r_0 ≤ N`. The value `0`
  -- is the well-ordering floor and needs no concise equivalent: it is
  -- realized in *any* format by the zero tensor (`asympRank_zero`). We
  -- therefore case-split on `r i = 0`:
  --   * `r i = 0`: take the format `fun _ => 1` and the zero tensor.
  --   * `r i > 0`: the raw witness `TRaw i ≠ 0` (else `R̃(TRaw i) = 0 ≠ r i`),
  --     so `exists_concise_restriction` yields a concise equivalent and the
  --     ceiling bound applies as in the paper.
  have hbdd : ∀ i, ∃ (d' : Fin k → ℕ+) (T' : KTensor F d'),
      asympRank T' = r i ∧ ∀ j, (d' j : ℕ) ≤ N := by
    intro i
    by_cases hzero : r i = 0
    · -- Floor value `0`: zero tensor in the trivial format `fun _ => 1`.
      refine ⟨fun _ => (1 : ℕ+), (0 : KTensor F (fun _ => (1 : ℕ+))), ?_, ?_⟩
      · rw [asympRank_zero, hzero]
      · intro j; simpa using! hN_pos
    · -- Positive value: `TRaw i ≠ 0`, so a concise equivalent exists.
      have hTne : TRaw i ≠ 0 := by
        intro h0
        apply hzero
        have : asympRank (TRaw i) = 0 := by rw [h0]; exact asympRank_zero _
        rw [hTRaw i] at this; exact this
      obtain ⟨d', T', hST, hTS, hflat⟩ := exists_concise_restriction (TRaw i) hTne
      have hRk : asympRank T' = r i := by
        rw [Restricts.asympRank_eq_of_equiv hST hTS, hTRaw i]
      refine ⟨d', T', hRk, ?_⟩
      intro j
      -- `(d' j : ℕ) = R_j(T') ≤ R̃(T') = r i ≤ r 0 ≤ N` via the ceiling bound.
      have h1 : ((d' j : ℕ) : ℝ) = (flatRank T' {j} : ℝ) := by
        exact_mod_cast (hflat j)
      have h2 : (flatRank T' {j} : ℝ) ≤ asympRank T' :=
        flatRank_le_asympRank T' j
      have h3 : asympRank T' ≤ r 0 := by rw [hRk]; exact hr_bdd i
      have hreal : ((d' j : ℕ) : ℝ) ≤ r 0 := h1 ▸ (h2.trans h3)
      have hceil : ⌈((d' j : ℕ) : ℝ)⌉₊ ≤ ⌈r 0⌉₊ := Nat.ceil_le_ceil hreal
      have hself : ⌈((d' j : ℕ) : ℝ)⌉₊ = (d' j : ℕ) := Nat.ceil_natCast _
      have hbnd : (d' j : ℕ) ≤ ⌈r 0⌉₊ := hself ▸ hceil
      exact hbnd.trans (le_max_right _ _)
  -- Re-embed each bounded-format witness into the uniform format `dStar`.
  have hreembed : ∀ i, ∃ T'' : KTensor F dStar, asympRank T'' = r i := by
    intro i
    obtain ⟨d', T', hRk, hle'⟩ := hbdd i
    have hle : ∀ j, (d' j : ℕ) ≤ (dStar j : ℕ) := fun j => hle' j
    obtain ⟨T'', hT''⟩ := exists_reembed hle T'
    exact ⟨T'', hT''.trans hRk⟩
  choose T'' hT'' using hreembed
  -- Now all `r i` are in `Set.range (tensorRankAdmissible F hk dStar).regularize`,
  -- which is well-ordered by `wellOrdered_values_per_format` (Cor 2.5).
  -- (`asympRank T = (tensorRankAdmissible F hk dStar).regularize T` by definition.)
  have hmem' : ∀ i, r i ∈ Set.range (tensorRankAdmissible F hk dStar).regularize := by
    intro i
    refine ⟨T'' i, ?_⟩
    -- `(tensorRankAdmissible F hk dStar).regularize (T'' i) = asympRank (T'' i) = r i`.
    rw [← hT'' i]
    simp [asympRank, hk]
  -- Cor 2.5 gives well-foundedness of `<` on this set.
  have hWO : WellFoundedLT
      (Set.range (tensorRankAdmissible F hk dStar).regularize) :=
    wellOrdered_values_per_format _
  -- Build a contradicting relation embedding `(· > ·) ↪r (· < ·)`.
  have hWF : WellFounded
      (α := Set.range (tensorRankAdmissible F hk dStar).regularize) (· < ·) :=
    hWO
  rw [RelEmbedding.wellFounded_iff_isEmpty] at hWF
  -- The embedding: `i ↦ ⟨r i, hmem' i⟩`. Inject + relation preservation.
  have hinj : Function.Injective
      (fun i : ℕ => (⟨r i, hmem' i⟩ :
        Set.range (tensorRankAdmissible F hk dStar).regularize)) := by
    intro a b hab
    have hsub : r a = r b := by
      have hext : (⟨r a, hmem' a⟩ :
          Set.range (tensorRankAdmissible F hk dStar).regularize) =
            ⟨r b, hmem' b⟩ := hab
      exact Subtype.mk.inj hext
    exact hr_anti.injective hsub
  refine hWF.false ⟨⟨fun i => ⟨r i, hmem' i⟩, hinj⟩, ?_⟩
  -- Relation preservation: `subtype-elt a < subtype-elt b ↔ a > b` (Subtype.lt).
  intro a b
  change r a < r b ↔ a > b
  constructor
  · intro hlt
    by_contra hge
    push_neg at hge
    rcases lt_or_eq_of_le hge with halt | hab
    · exact absurd (hr_anti halt) (not_lt.mpr hlt.le)
    · rw [hab] at hlt; exact absurd hlt (lt_irrefl _)
  · intro hgt; exact hr_anti hgt

end Semicontinuity


