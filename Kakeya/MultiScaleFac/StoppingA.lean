/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.MultiScaleFac.RefineStep

/-!
# The half-(A) stopping time, run in blocks

The cardinality budget of one refinement round, the block-wise run of the stopping time, and the
quadratic-budget variant the self-banding pass is charged at.

This module is the merge of the former `MultiScaleRefineStepBlocksAux`,
`MultiScaleRefineStepBlocks`, `MultiScaleRefineStepBlocksQuad`.  Each keeps its own section, so its
file-level `open`s and `variable`s stay confined to it.

## Helpers of the hoisted stopping time

This section builds
`Kakeya.MultiScaleFac.exists_maximal_cuts_state_instance_hoisted_blocks_quad`, the block-wise run of
the stopping time carrying an extra abstract state invariant, out of the block-level step of
`Kakeya/MultiScaleFac/RefineStep.lean`.

The primed declarations below are the elementary helpers that run needs.  They are the single copy
of each statement: the earlier duplicate family they were named after no longer exists.  The
stopping-margin ceiling arithmetic likewise lives once and publicly in
`Kakeya/MultiScaleFac/RefineStep.lean` under the `Kakeya.MultiScaleFac.KT` namespace, and is used
from there by both halves.

## The stopping time of GWZ Lemma 7.7(A) with an abstract state invariant

`Kakeya.MultiScaleFac.exists_maximal_cuts_state_instance_hoisted_blocks_quad` runs the stopping
time on states
consisting of a subfamily that is grid-uniform, has comparable fibre counts, and carries the block
bound `Good_l(0, Mgrid)`.  Some consumers need a *further* property of the terminal family — the
paired homogenization band is the motivating one — which the refinement steps of the stopping
time destroy and which therefore has to be
re-established inside every step, before the stopping test is read.

This section is the twin of that engine, carrying one extra, wholly abstract, invariant
`Inv : ℕ → Finset ι → Prop` in the state and taking as a hypothesis a **pass** that restores the
invariant on a subfamily.  No concrete invariant appears here: the caller supplies the pass, and
the engine only has to know what it costs.

## Why the pass hypothesis is per anchor

On the Katz–Tao side the block invariant `Kakeya.MultiScaleFac.BlockKatzTaoOn` is inherited by
subfamilies for free.  On the Frostman side it is not: moving `Kakeya.MultiScaleFac.BlockFrostman`
to a subfamily is `Kakeya.MultiScaleFac.BlockFrostmanAt.of_subfamily`, whose hypothesis compares the
cardinalities of the fibres of the two families **at each anchor separately**, namely
`fibreIndex t T δ (gridScale δ Mgrid a) i₀` against
`fibreIndex t' T δ (gridScale δ Mgrid a) i₀`.  A single global proportion `|t| ≤ A |t'|` is not
enough.  So the abstract pass hypothesis here supplies the per-anchor ratio directly, at every
coarse grid index `a ≤ Mgrid`; this is exactly what a caller has to produce.

## Why the accumulated loss is harmless

The pass runs once before the first stopping-time step and once inside each of the at most `N`
steps, so its cardinality loss and its per-anchor constant are each raised to a power at most
`Mgrid + 1`.  With `N` fixed, `Kakeya.MultiScaleFac.gridLoss_pow` absorbs such a power back into a
single `Kakeya.MultiScaleFac.gridLoss`, and the constants of the two locked dichotomies
`Kakeya.MultiScaleFac.dividingScalesFrostman` and
`Kakeya.MultiScaleFac.dividingScalesKatzTao` are existentially quantified, so nothing displayed
changes.

## Contents

* `Kakeya.MultiScaleFac.BlockFrostman.of_subfamily_pointwise`, the whole-family form of
  `Kakeya.MultiScaleFac.BlockFrostmanAt.of_subfamily`;
* `exists_hoisted_cuts_run_blocks`, the run of the stopping time with the invariant in the state;
* `Kakeya.MultiScaleFac.exists_maximal_cuts_state_instance_hoisted_blocks_quad`, the assembled
  statement with the extra terminal clause `Inv m tL`.

The elementary helpers this run needs are the primed declarations of the first section of this file.

## The stopping time with an abstract state invariant, at a quadratic pass budget

`Kakeya.MultiScaleFac.exists_maximal_cuts_state_instance_hoisted_blocks_quad` runs the half-(A)
stopping time with an abstract state invariant `Inv`, and asks its caller for a **pass** presented
at two budgets: a cardinality loss `A_pass^{M+1}(1-\log δ)^{K_pass (M+1)}` and a per-anchor
fibre-retention ratio `C_pass^{M+1}(1-\log δ)^{K_pass' (M+1)}`.  Both polylogarithmic exponents are
*linear* in the grid length, and the constant `C_pass` is quantified *before* the state constant
`Cv`.

Neither shape can be met by the banded pass `Kakeya.StickyKakeya.exists_banded_pass_gridUniform`:

* the paired homogenization treats one band per **pair** of grid levels, so its cost carries the
  exponent `2(M+2)(M+1)`, quadratic in the grid length, and no constant fixed before the grid length
  turns a quadratic exponent into a linear one;
* its per-anchor ratio is a power of the grid-uniform constant of the state, so it is only available
  once `Cv` is known.

This section re-runs the same engine at the two widened shapes.  Nothing about the run of the
stopping time changes: the pass is still applied once before the run and once inside each of at most
`N`
steps, and both budgets are still raised to a power at most `Mgrid + 1`.  What changes is only which
displayed exponent absorbs the accumulated loss, and where the per-anchor constant is quantified.

The widened loss is still affordable: a quadratic polylogarithmic exponent is one
`Kakeya.MultiScaleFac.gridLoss`, and a `δ`-independent power of a `gridLoss` is again one by
`Kakeya.MultiScaleFac.gridLoss_pow`.  The banded stopping time downstream charges it that way.
-/

@[expose] public section

open MeasureTheory Real Metric

universe u
open Tube

namespace Kakeya

open StickyKakeya

namespace MultiScaleFac

open _root_.StickyKakeya

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

/-- **The two tube-volume comparison constants are ordered.** -/
private theorem one_le_volume_ratio_const :
    (1 : NNReal) ≤
      Tube.volume_le.C (Module.finrank ℝ E) / Tube.le_volume.c (Module.finrank ℝ E) := by
  obtain ⟨u, hu⟩ := exists_ne (0 : E)
  have hdist : dist (0 : E) (‖u‖⁻¹ • u) = 1 := by
    rw [dist_zero_left]; exact norm_smul_inv_norm hu
  set T : Tube (1 : NNReal) E := Tube.mk' (1 : NNReal) hdist
  have hle : (Tube.le_volume.c (Module.finrank ℝ E) : ENNReal) ≤ volume T.carrier := by
    simpa [one_pow] using Tube.le_volume T
  rw [le_div_iff₀ (Tube.le_volume.c_pos _), one_mul]
  exact ENNReal.coe_le_coe.mp
    (hle.trans (by simpa [one_pow] using Tube.volume_le (le_refl (1 : NNReal)) T))

omit [Nontrivial E] in
/-- **The block bound on the whole grid gives the Frostman bound at the unit scale.** -/
private theorem frostmanConstant_unit_le_of_blockFrostman_zero
    {δ : NNReal} {M : ℕ} (hM : 0 < M)
    {ι : Type u} {tL : Finset ι} {T : ι → Tube δ E} {Ct : NNReal} {ζ : ℝ}
    (h : BlockFrostman tL T M Ct ζ 0 M) (i₀ : ι) (hi₀ : i₀ ∈ tL) :
    ConvexSpaceBody.frostmanConstant (fibreIndex tL T δ 1 i₀) (fibreBodies T δ)
        ((T i₀).rescale 1).toConvexSpaceBody
      ≤ (Ct : ENNReal) * ENNReal.ofReal ((δ : ℝ) ^ (-ζ)) := by
  have hAt : ConvexSpaceBody.frostmanConstant
      (fibreIndex tL T δ (gridScale δ M 0) i₀)
      (fibreBodies T (gridScale δ M M))
      ((T i₀).rescale (2 * gridScale δ M 0)).toConvexSpaceBody
    ≤ ((Ct : NNReal) : ENNReal) *
        ENNReal.ofReal (((gridScale δ M 0 : ℝ) / (gridScale δ M M : ℝ)) ^ ζ) := h i₀ hi₀
  rw [gridScale_zero, gridScale_self δ hM,
    show (((1 : NNReal) : ℝ) / (δ : ℝ)) ^ ζ = (δ : ℝ) ^ (-ζ) by
      rw [NNReal.coe_one, one_div]; exact (Real.rpow_neg_eq_inv_rpow (δ : ℝ) ζ).symm] at hAt
  have hrs := Tube.rescale_le_rescale_of_radius_le (T i₀) (by norm_num : (1 : NNReal) ≤ 2 * 1)
  have hmem1 : ∀ i ∈ fibreIndex tL T δ (1 : NNReal) i₀,
      fibreBodies T δ i ≤ ((T i₀).rescale (1 : NNReal)).toConvexSpaceBody := fun i hi => by
    simpa [fibreIndex, Kakeya.familyIn, fibreBodies] using (Finset.mem_filter.mp hi).2
  have hdeflate := frostmanConstant_mono_anchor (fun i hi => (hmem1 i hi).trans hrs) hmem1
    (by rw [one_mul]; exact measure_mono fun y hy => hrs hy) (by simp : (1 : ENNReal) ≠ ⊤)
  rw [one_mul] at hdeflate
  exact hdeflate.trans hAt

/-- **A cut parameter below `1/64` is below one.** -/
private theorem eps_le_one_of_le_one_div_64 {ε : ℝ} (h : ε ≤ 1 / 64) : ε ≤ 1 := by
  linarith

/-- **The exponent chain is below `ε` at every index it is read at.** -/
private theorem eta_le_eps_of_mono {N : ℕ} {ε : ℝ} {η : ℕ → ℝ}
    (hmono : ∀ ⦃j j' : ℕ⦄, j ≤ j' → j' ≤ N → η j ≤ η j') (hηN : η N ≤ ε) :
    ∀ k ≤ N, η k ≤ ε := fun _ hk => (hmono hk le_rfl).trans hηN

/-- **The exponent chain increases up to `N`.** -/
private lemma eta_mono_of_gap' (N : ℕ) (hN : 0 < N) {ε : ℝ} (hε : ε = 1 / Real.sqrt (N : ℝ))
    (η : ℕ → ℝ) (hη0 : 0 ≤ η 0) (hηgap : ∀ k < N, η k ≤ ε * η (k + 1)) :
    ∀ ⦃j j' : ℕ⦄, j ≤ j' → j' ≤ N → η j ≤ η j' := by
  have hnonneg : ∀ k ≤ N, 0 ≤ η k := eta_nonneg_of_gap N hN hε η hη0 hηgap
  have hε1 : ε ≤ 1 := by
    rw [hε, div_le_one (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hN)), Real.one_le_sqrt]
    exact_mod_cast hN
  have hstep : ∀ k < N, η k ≤ η (k + 1) := fun k hk =>
    (hηgap k hk).trans (mul_le_of_le_one_left (hnonneg (k + 1) (by omega)) hε1)
  intro j j' hjj'
  induction hjj' with
  | refl => exact fun _ => le_rfl
  | step h ih => exact fun hn => (ih (by omega)).trans (hstep _ (by omega))

/-- **A real cardinality bound is a bound with the coefficient read in `ℝ≥0`.** -/
private theorem card_le_toNNReal_mul {x : ℝ} (hx : 0 ≤ x) {p q : ℕ}
    (h : (p : ℝ) ≤ x * (q : ℝ)) :
    (p : ℝ) ≤ ((Real.toNNReal x : NNReal) : ℝ) * (q : ℝ) := by
  rw [Real.coe_toNNReal x hx]; exact h

/-- **A geometric constant chain starting above one stays above one.** -/
private theorem one_le_geomConst {step baseC : NNReal} (hs : 1 ≤ step) (hb : 1 ≤ baseC) (m : ℕ) :
    1 ≤ step ^ m * baseC := by
  exact one_le_mul (one_le_pow_of_one_le' hs m) hb

/-- **The hoisted per-cut step, with the cut placed at distance at least the stopping margin from
both ends of its block.** -/
private theorem exists_refined_cut_hoisted_margin (Cu : NNReal) (hCu : 1 ≤ Cu) :
    ∃ (A : ℝ) (K K'' : ℕ) (Cv C'' : NNReal), 1 ≤ A ∧ Cu ≤ Cv ∧ 1 ≤ C'' ∧
      ∀ (N : ℕ), 16 ≤ N → ∀ {ε : ℝ}, 0 < ε → ε ≤ 1 / 64 →
      ∀ {ι : Type u} {δ : NNReal}, 0 < δ → (δ : ℝ) ≤ 1 → δ ≤ (16 : NNReal) ^ (-(N : ℝ)) →
      ∀ (s t : Finset ι) (T : ι → Tube δ E), t ⊆ s →
      (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall (0 : E) 1) →
      (↑s : Set ι).Pairwise (fun i j => IsEssentiallyDistinct (T i).carrier (T j).carrier) →
      Nonempty (GridUniform t T N Cv) →
      ComparableFibreCounts t T (gridScales δ N) Cv →
      ∀ (C : NNReal) (ζ ζ' : ℝ), 0 ≤ ζ → ζ ≤ ε * ζ' → ζ' ≤ ε →
      ∀ a b : ℕ, b ≤ N → IsLongBlock N ε a b →
      BlockFrostman t T N C ζ a b →
      t.card ≤ 2 * (passingNodes t T N C ε ζ' a b).card →
      ∃ c : ℕ, a + ⌈ε * ((⌈ε * (N : ℝ)⌉₊ : ℕ) : ℝ)⌉₊ ≤ c ∧
          c + ⌈ε * ((⌈ε * (N : ℝ)⌉₊ : ℕ) : ℝ)⌉₊ ≤ b ∧ ∃ t' ⊆ t,
        (t.card : ℝ) ≤ (2 : ℝ) * (N + 1 : ℝ) * A ^ (N + 1) *
            (1 - Real.log (δ : ℝ)) ^ (K * (N + 1)) * (t'.card : ℝ) ∧
          Nonempty (GridUniform t' T N Cv) ∧
          ComparableFibreCounts t' T (gridScales δ N) Cv ∧
          ComparableFibreCountsInflated t' T (gridScales δ N) Cv ∧
          BlockFrostman t' T N
            (C'' ^ (N + 1) *
              Real.toNNReal ((1 - Real.log (δ : ℝ)) ^ (K'' * (N + 1))) * C) ζ' a c ∧
          BlockFrostman t' T N
            (C'' ^ (N + 1) *
              Real.toNNReal ((1 - Real.log (δ : ℝ)) ^ (K'' * (N + 1))) * C) ζ' c b ∧
          ∀ (C₂ : NNReal) (ζ₂ : ℝ) (a₂ b₂ : ℕ), 0 ≤ ζ₂ → a₂ ≤ b₂ → b₂ ≤ N →
            BlockFrostman t T N C₂ ζ₂ a₂ b₂ →
            BlockFrostman t' T N
              (C'' ^ (N + 1) *
                Real.toNNReal ((1 - Real.log (δ : ℝ)) ^ (K'' * (N + 1))) * C₂) ζ₂ a₂ b₂ := by
  obtain ⟨A, K, K'', Cv, C'', hA, hCuCv, hC'', hmain⟩ :=
    exists_refined_cut_hoisted.{u, _} (E := E) Cu hCu
  refine ⟨A, K, K'', Cv, C'', hA, hCuCv, hC'', ?_⟩
  intro N hN ε hεpos hε64 ι δ hδ hδ1 hδ0 s t T hts hball hED hG hC C ζ ζ' hζ hgap hζ' a b hbN
    hlong hbf htest
  obtain ⟨c, hac, hcb, hrest⟩ :=
    hmain N hN hεpos hε64 hδ hδ1 hδ0 s t T hts hball hED hG hC C ζ ζ' hζ hgap hζ' a b hbN hlong
      hbf htest
  have hmar := KT.stoppingMargin_le_ceil_of_isLongBlock hεpos hlong
  exact ⟨c, by omega, by omega, hrest⟩

/-- **The initial block bound of the hoisted stopping time.** -/
private theorem exists_initial_blockFrostman_hoisted (Cv : NNReal) (hCv : 1 ≤ Cv) :
    ∃ C₀ : NNReal, 1 ≤ C₀ ∧
      ∀ (Mgrid : ℕ), 16 ≤ Mgrid →
      ∀ {ι : Type u} {δ : NNReal}, 0 < δ → (δ : ℝ) ≤ 1 → δ ≤ (16 : NNReal) ^ (-(Mgrid : ℝ)) →
      ∀ (s s₀ : Finset ι) (T : ι → Tube δ E), s₀ ⊆ s →
      (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall (0 : E) 1) →
      Nonempty (GridUniform s₀ T Mgrid Cv) →
      ComparableFibreCounts s₀ T (gridScales δ Mgrid) Cv →
      ∀ Acc : NNReal, (s.card : ℝ) ≤ ((Acc : NNReal) : ℝ) * (s₀.card : ℝ) →
      ∀ ζ : ℝ, 0 ≤ ζ →
      ConvexSpaceBody.frostmanConstant s (fibreBodies T δ) ConvexSpaceBody.closedUnitBall
          ≤ ENNReal.ofReal ((δ : ℝ) ^ (-ζ)) →
      ∀ Cbase : NNReal,
        C₀ * (Acc * (Tube.volume_le.C (Module.finrank ℝ E)
            / Tube.le_volume.c (Module.finrank ℝ E))) ≤ Cbase →
        BlockFrostman s₀ T Mgrid Cbase ζ 0 Mgrid := by
  classical
  obtain ⟨C_frost0, hC_frost0, hfrost⟩ :=
    blockFrostman_zero_right.{u, _} (E := E) (uniformTubeSetCuOf (E := E) Cv)
      (le_trans hCv (le_max_left _ _))
  refine ⟨C_frost0, hC_frost0, ?_⟩
  intro Mgrid hMgrid ι δ hδ hδ1 hδ0 s s₀ T hs₀sub hball hG₀ hC₀ Acc hAcc ζ hζ hfrosthy Cbase hCbase
  let volfac : NNReal := Tube.volume_le.C (Module.finrank ℝ E)
      / Tube.le_volume.c (Module.finrank ℝ E)
  have hMg : (16 : ℝ) ≤ (Mgrid : ℝ) := by exact_mod_cast (show 16 ≤ Mgrid by omega)
  have hδ16 : 16 * δ ≤ 1 := by
    calc
      16 * δ ≤ 16 * (16 : NNReal) ^ (-(Mgrid : ℝ)) :=
        mul_le_mul_of_nonneg_left hδ0 (by norm_num : (0 : NNReal) ≤ 16)
      _ = (16 : NNReal) ^ (1 - (Mgrid : ℝ)) := by
        rw [sub_eq_add_neg, NNReal.rpow_add (by norm_num : (16 : NNReal) ≠ 0), NNReal.rpow_one]
      _ ≤ 1 := NNReal.rpow_le_one_of_one_le_of_nonpos (by norm_num : (1 : NNReal) ≤ 16)
          (by linarith)
  have hδ1nn : δ ≤ 1 := by exact_mod_cast hδ1
  by_cases hs₀ne : s₀.Nonempty
  · have hFrost₀ :
        ConvexSpaceBody.frostmanConstant s₀ (fibreBodies T δ) ConvexSpaceBody.closedUnitBall
          ≤ ((Acc * volfac : NNReal) : ENNReal) * ENNReal.ofReal ((δ : ℝ) ^ (-ζ)) :=
      (frostmanConstant_unitBall_le_of_subfamily (E := E) (T := T) hδ hδ1nn hs₀sub hs₀ne
        hball (by exact_mod_cast hAcc)).trans (mul_le_mul' le_rfl hfrosthy)
    exact (hfrost Mgrid (by omega : 0 < Mgrid) hδ hδ1 hδ16 s₀ T
        (fun i hi => hball i (hs₀sub hi)) (Classical.choice hG₀).toUniformTubeSet
        (hC₀.mono (le_max_left _ _)) ζ hζ (Acc * volfac) hFrost₀).mono hδ hδ1
      (by simpa [volfac] using hCbase) hζ le_rfl (Nat.zero_le Mgrid)
  · intro i₀ hi₀
    exact absurd ⟨i₀, hi₀⟩ hs₀ne

/-! ### Bookkeeping with a free polylogarithmic exponent

The helpers above all display the polylogarithmic factor in the shape `W ^ (K * (M + 1))`, an
exponent *linear* in the grid length.  A homogenizing pass that treats one band per pair of grid
levels costs `W ^ (K * ((M + 2) * (M + 1)))` instead, and no choice of `K` made before the grid
length turns the quadratic shape into the linear one.  The variants below therefore leave the
exponent of `W` free, which lets a linear factor and a quadratic factor be combined in one
inequality.  Nothing else about them differs from their linear namesakes. -/

/-- **The linear grid length is below the quadratic one.** -/
theorem grid_succ_le_quad (M : ℕ) : M + 1 ≤ (M + 2) * (M + 1) := by
  exact Nat.le_mul_of_pos_left (M + 1) (by omega : 0 < M + 2)

/-- **A linear exponent is below a quadratic one with a larger multiplier.** -/
theorem quad_exp_le {a c : ℕ} (hac : a ≤ c) (M : ℕ) :
    a * (M + 1) ≤ c * ((M + 2) * (M + 1)) := Nat.mul_le_mul hac (grid_succ_le_quad M)

/-- **A linear exponent plus a quadratic one is below a quadratic one with the summed
multiplier.** -/
theorem quad_exp_add_le {a b c : ℕ} (hab : a + b ≤ c) (M : ℕ) :
    a * (M + 1) + b * ((M + 2) * (M + 1)) ≤ c * ((M + 2) * (M + 1)) := by
  refine (Nat.add_le_add_right (Nat.mul_le_mul_left a (grid_succ_le_quad M)) _).trans ?_
  rw [← Nat.add_mul]; exact Nat.mul_le_mul_right _ hab

/-- **The per-cut cardinality loss is below the per-round budget, at a free exponent.** -/
theorem refinedCut_loss_le_budget_gen {A₀ A W : ℝ} (hA₀ : 1 ≤ A₀) (hA : A₀ ≤ A)
    (hW : 1 ≤ W) {e₀ e : ℕ} (he : e₀ ≤ e) (M : ℕ) :
    2 * ((M : ℝ) + 1) * A₀ ^ (M + 1) * W ^ e₀
      ≤ 2 * ((M : ℝ) + 1) * A ^ (M + 1) * W ^ e := by
  have hA0 : (0 : ℝ) ≤ A₀ := by linarith
  have hC0 : (0 : ℝ) ≤ 2 * ((M : ℝ) + 1) := by positivity
  exact mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hA0 hA _) hC0)
    (pow_le_pow_right₀ hW he) (pow_nonneg (by linarith) _)
    (mul_nonneg hC0 (pow_nonneg (hA0.trans hA) _))

/-- **The initial-uniformization loss is below the per-round budget, at a free exponent.** -/
theorem gridUniform_loss_le_budget_gen {A₁ A W : ℝ} (hA₁ : 1 ≤ A₁) (hA : A₁ ≤ A)
    (hW : 1 ≤ W) {e₁ e : ℕ} (he : e₁ ≤ e) (M : ℕ) :
    A₁ ^ (M + 1) * W ^ e₁ ≤ 2 * ((M : ℝ) + 1) * A ^ (M + 1) * W ^ e := by
  have hA₁nn : (0 : ℝ) ≤ A₁ := by linarith
  have hprod : A₁ ^ (M + 1) * W ^ e₁ ≤ A ^ (M + 1) * W ^ e :=
    mul_le_mul (pow_le_pow_left₀ hA₁nn hA _) (pow_le_pow_right₀ hW he)
      (pow_nonneg (by linarith) _) (pow_nonneg (hA₁nn.trans hA) _)
  have hinner : (0 : ℝ) ≤ A ^ (M + 1) * W ^ e :=
    mul_nonneg (pow_nonneg (hA₁nn.trans hA) _) (pow_nonneg (by linarith) _)
  have hM : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
  refine hprod.trans ?_
  have hstep : A ^ (M + 1) * W ^ e ≤ 2 * ((M : ℝ) + 1) * (A ^ (M + 1) * W ^ e) :=
    le_mul_of_one_le_left hinner (by linarith)
  linarith

/-- **The initial-uniformization loss is nonnegative, at a free exponent.** -/
theorem gridUniform_loss_nonneg_gen {A W : ℝ} (hA : 1 ≤ A) (hW : 1 ≤ W) (e M : ℕ) :
    0 ≤ A ^ (M + 1) * W ^ e :=
  mul_nonneg (pow_nonneg (zero_le_one.trans hA) _) (pow_nonneg (zero_le_one.trans hW) _)

/-- **The per-cut cardinality loss is nonnegative, at a free exponent.** -/
theorem refinedCut_loss_nonneg_gen {A W : ℝ} (hA : 1 ≤ A) (hW : 1 ≤ W) (e M : ℕ) :
    0 ≤ 2 * ((M : ℝ) + 1) * A ^ (M + 1) * W ^ e :=
  mul_nonneg (mul_nonneg (by positivity) (pow_nonneg (zero_le_one.trans hA) _))
    (pow_nonneg (zero_le_one.trans hW) _)

/-- **A product of a per-cut loss and a pass loss, at two free exponents.** -/
theorem refinedCut_loss_mul_pass_loss_gen (A₀ A₁ W : ℝ) (e₀ e₁ M : ℕ) :
    (2 * ((M : ℝ) + 1) * A₀ ^ (M + 1) * W ^ e₀) * (A₁ ^ (M + 1) * W ^ e₁)
      = 2 * ((M : ℝ) + 1) * (A₀ * A₁) ^ (M + 1) * W ^ (e₀ + e₁) := by
  rw [pow_add, mul_pow]; ring

/-- **The per-cut block factor is at least one, at a free exponent.** -/
theorem one_le_cutStep_gen {C : NNReal} (hC : 1 ≤ C) {W : ℝ} (hW : 1 ≤ W) (e M : ℕ) :
    (1 : NNReal) ≤ C ^ (M + 1) * Real.toNNReal (W ^ e) :=
  one_le_mul (one_le_pow_of_one_le' hC _) (Real.one_le_toNNReal.mpr (one_le_pow₀ hW))

/-- **The per-cut block factor is below one round of the terminal budget, at free exponents.** -/
theorem cutStep_le_terminalBudget_gen {C₀ C₁ : NNReal} (hC : C₀ ≤ C₁)
    {W : ℝ} (hW : 1 ≤ W) {e₀ e₁ : ℕ} (he : e₀ ≤ e₁) (M : ℕ) :
    C₀ ^ (M + 1) * Real.toNNReal (W ^ e₀)
      ≤ C₁ ^ (M + 1) * Real.toNNReal (W ^ e₁) :=
  mul_le_mul' (pow_le_pow_left' hC (M + 1))
    (Real.toNNReal_le_toNNReal (pow_le_pow_right₀ hW he))

/-- **The pass factor is below one round of the terminal budget, at free exponents.** -/
theorem passStep_le_terminalBudget_gen {C₁ volfac C : NNReal} (hv : 1 ≤ volfac)
    (hC : C₁ * volfac ≤ C) {W : ℝ} (hW : 1 ≤ W) {e₁ e : ℕ} (he : e₁ ≤ e) (M : ℕ) :
    (C₁ ^ (M + 1) * Real.toNNReal (W ^ e₁)) * volfac
      ≤ C ^ (M + 1) * Real.toNNReal (W ^ e) := by
  have hbase : C₁ ^ (M + 1) * volfac ≤ C ^ (M + 1) :=
    ((mul_le_mul' le_rfl (le_self_pow hv (Nat.succ_ne_zero M))).trans_eq
      (mul_pow C₁ volfac (M + 1)).symm).trans (pow_le_pow_left' hC (M + 1))
  rw [mul_right_comm]
  exact mul_le_mul' hbase (Real.toNNReal_le_toNNReal (pow_le_pow_right₀ hW he))

/-- **A cut factor times a pass factor is a step factor, at free exponents.** -/
theorem cutStep_mul_pass_le_gen {C₀ C₁ volfac C : NNReal} (hv : 1 ≤ volfac)
    (hC : C₀ * C₁ * volfac ≤ C) {W : ℝ} (hW : 1 ≤ W) {e₀ e₁ e : ℕ} (he : e₀ + e₁ ≤ e) (M : ℕ) :
    (C₁ ^ (M + 1) * Real.toNNReal (W ^ e₁)) * volfac
        * (C₀ ^ (M + 1) * Real.toNNReal (W ^ e₀))
      ≤ C ^ (M + 1) * Real.toNNReal (W ^ e) := by
  have hW0 : (0 : ℝ) ≤ W := by linarith
  have hV : (1 : NNReal) ≤ Real.toNNReal W := by simpa using Real.toNNReal_le_toNNReal hW
  simp only [Real.toNNReal_pow hW0]
  calc
    (C₁ ^ (M + 1) * Real.toNNReal W ^ e₁) * volfac
        * (C₀ ^ (M + 1) * Real.toNNReal W ^ e₀)
        = (C₀ * C₁) ^ (M + 1) * volfac * Real.toNNReal W ^ (e₀ + e₁) := by
            rw [mul_pow, pow_add]; ring
    _ ≤ (C₀ * C₁) ^ (M + 1) * volfac ^ (M + 1) * Real.toNNReal W ^ e :=
        mul_le_mul' (mul_le_mul' le_rfl (le_self_pow hv (Nat.succ_ne_zero M)))
          (pow_le_pow_right₀ hV he)
    _ = (C₀ * C₁ * volfac) ^ (M + 1) * Real.toNNReal W ^ e := by ring
    _ ≤ C ^ (M + 1) * Real.toNNReal W ^ e := mul_le_mul' (pow_le_pow_left' hC _) le_rfl

/-- **The initial block constant is below one round of the terminal budget, at free exponents.** -/
theorem baseConst_le_terminalBudget_gen {C_frost volfac C₁ : NNReal} (hC : 1 ≤ C_frost)
    (hv : 1 ≤ volfac) {A : ℝ} (hA : 1 ≤ A) {W : ℝ} (hW : 1 ≤ W) {e₀ e₁ : ℕ} (he : e₀ ≤ e₁)
    (hC₁ : C_frost * volfac * Real.toNNReal A ≤ C₁) (h1 : 1 ≤ C₁) (M : ℕ) :
    max 1 (C_frost * (Real.toNNReal (A ^ (M + 1) * W ^ e₀) * volfac))
      ≤ C₁ ^ (M + 1) * Real.toNNReal (W ^ e₁) := by
  have hA0 : (0 : ℝ) ≤ A := by linarith
  have hstep : C_frost * volfac * Real.toNNReal A ^ (M + 1)
      ≤ (C_frost * volfac * Real.toNNReal A) ^ (M + 1) := by
    rw [mul_pow]
    exact mul_le_mul_left (le_self_pow (one_le_mul hC hv) (Nat.succ_ne_zero M)) _
  refine max_le (one_le_mul (one_le_pow₀ h1)
    (by simpa using Real.toNNReal_le_toNNReal (one_le_pow₀ hW))) ?_
  rw [Real.toNNReal_mul (pow_nonneg hA0 (M + 1)), Real.toNNReal_pow hA0]
  calc
    C_frost * (Real.toNNReal A ^ (M + 1) * Real.toNNReal (W ^ e₀) * volfac)
        = C_frost * volfac * Real.toNNReal A ^ (M + 1) * Real.toNNReal (W ^ e₀) := by ring
    _ ≤ (C_frost * volfac * Real.toNNReal A) ^ (M + 1) * Real.toNNReal (W ^ e₁) :=
        mul_le_mul' hstep (Real.toNNReal_le_toNNReal (pow_le_pow_right₀ hW he))
    _ ≤ C₁ ^ (M + 1) * Real.toNNReal (W ^ e₁) := mul_le_mul_left (pow_le_pow_left' hC₁ _) _

/-- **A per-anchor pass constant read as a power of the grid length.**

The banded pass displays its per-anchor fibre-retention ratio as a constant times the real
cardinality loss `A^{M+1} W`; the abstract engine asks for a constant raised to the power `M + 1`
times `W`.  Absorbing the base `A` into the constant converts one into the other. -/
theorem passRatio_const_le {Cp : NNReal} (hCp : 1 ≤ Cp) {A : ℝ} (hA : 1 ≤ A) {W : ℝ}
    (M : ℕ) :
    Cp * Real.toNNReal (A ^ (M + 1) * W)
      ≤ (Cp * Real.toNNReal A) ^ (M + 1) * Real.toNNReal W := by
  have hA0 : (0 : ℝ) ≤ A := by linarith
  rw [Real.toNNReal_mul (pow_nonneg hA0 (M + 1)), Real.toNNReal_pow hA0, mul_pow, ← mul_assoc]
  exact mul_le_mul_left (mul_le_mul_left (le_self_pow hCp (Nat.succ_ne_zero M)) _) _

/-! ### Moving a block bound along a pass -/

/-- **A block bound descends to a subfamily with a per-anchor retention ratio.**  The whole-family
form of `Kakeya.MultiScaleFac.BlockFrostmanAt.of_subfamily`: if at every anchor of the retained
family `t'` the fibre at the coarse grid index `a` loses at most a factor `A`, then the block bound
on `(a,b)` descends at the cost of `A` and one tube-volume ratio.  A global proportion is not
enough: the descent compares the fibres anchor by anchor. -/
theorem BlockFrostman.of_subfamily_pointwise {ι : Type*} {δ : NNReal} {t t' : Finset ι}
    {T : ι → Tube δ E} {M : ℕ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) {C A : NNReal} {ζ : ℝ} {a b : ℕ}
    (hab : a ≤ b) (hbM : b ≤ M) (htt' : t' ⊆ t)
    (hcard : ∀ i₀ ∈ t', ((fibreIndex t T δ (gridScale δ M a) i₀).card : ENNReal)
      ≤ (A : ENNReal) * ((fibreIndex t' T δ (gridScale δ M a) i₀).card : ENNReal))
    (h : BlockFrostman t T M C ζ a b) :
    BlockFrostman t' T M
      (A * (Tube.volume_le.C (Module.finrank ℝ E)
        / Tube.le_volume.c (Module.finrank ℝ E)) * C) ζ a b := fun i₀ hi₀ =>
  BlockFrostmanAt.of_subfamily hδ hδ1 hab hbM htt' hi₀ (hcard i₀ hi₀) (h i₀ (htt' hi₀))

/-! ### The arithmetic of composing a cut with a pass -/

/-- **One round of the budget absorbs a two-round base and one factor per cut.**

The base is charged two rounds rather than one.  The extra round is the invariant-restoring pass
run once before the stopping time starts, on top of the descent of the initial Frostman bound. -/
private theorem pow_mul_le_pow_add_two {step base G : NNReal} (hstep : step ≤ G)
    (hbase : base ≤ G * G) (m : ℕ) : step ^ m * base ≤ G ^ (m + 2) :=
  (mul_le_mul' (pow_le_pow_left' hstep m) hbase).trans_eq (by ring)

/-- **Two initial passes and the `m` cuts fit in `m + 2` rounds of the common budget.**

The two-step form of `Kakeya.MultiScaleFac.KT.hoisted_card_accum`: here the stopping time is
preceded by *two* cardinality losses, the manufacture of the grid-uniform family and the first
invariant-restoring pass, so the number of rounds is `m + 2` rather than `m + 1`. -/
private theorem card_accum_two {x y z u P₁ P₂ G : ℝ} (hG0 : 0 ≤ G)
    (hP₁G : P₁ ≤ G) (hP₂G : P₂ ≤ G) (hy : 0 ≤ y) (hz : 0 ≤ z) (m : ℕ)
    (h1 : x ≤ P₁ * y) (h2 : y ≤ P₂ * z) (h3 : z ≤ G ^ m * u) : x ≤ G ^ (m + 2) * u := by
  have h4 : y ≤ G * (G ^ m * u) :=
    h2.trans ((mul_le_mul_of_nonneg_right hP₂G hz).trans (mul_le_mul_of_nonneg_left h3 hG0))
  exact (h1.trans ((mul_le_mul_of_nonneg_right hP₁G hy).trans
    (mul_le_mul_of_nonneg_left h4 hG0))).trans_eq (by ring)

/-! ### One refinement step followed by one invariant-restoring pass -/

/-- **A cut composed with an invariant-restoring pass.**  A refinement step produces a cut index `c`
and a subfamily `t'` carrying the block bounds on both halves; the pass is then run on `t'`, giving
`t''` which satisfies the invariant, the block bounds being moved across by
`Kakeya.MultiScaleFac.BlockFrostman.of_subfamily_pointwise`.  The result has the shape of the cut
hypothesis itself, with the two per-round costs composed. -/
private theorem exists_cut_with_pass (Mgrid w : ℕ) {ε : ℝ}
    {ι : Type u} {δ : NNReal} (hδ : 0 < δ) (hδ1 : (δ : ℝ) ≤ 1)
    (s₀ : Finset ι) (T : ι → Tube δ E) (Cv : NNReal)
    (P₀ P₁ : ℝ) (hP₀ : 0 ≤ P₀) (stepCut step Ainv : NNReal)
    (hstep : Ainv * (Tube.volume_le.C (Module.finrank ℝ E)
        / Tube.le_volume.c (Module.finrank ℝ E)) * stepCut ≤ step)
    (Inv : ℕ → Finset ι → Prop)
    (hcut : ∀ t : Finset ι, t ⊆ s₀ → Nonempty (GridUniform t T Mgrid Cv) →
      ComparableFibreCounts t T (gridScales δ Mgrid) Cv →
      ∀ (C : NNReal) (ζ ζ' : ℝ), 0 ≤ ζ → ζ ≤ ε * ζ' → ζ' ≤ ε →
      ∀ a b : ℕ, b ≤ Mgrid → IsLongBlock Mgrid ε a b →
      BlockFrostman t T Mgrid C ζ a b →
      t.card ≤ 2 * (passingNodes t T Mgrid C ε ζ' a b).card →
      ∃ c : ℕ, a + w ≤ c ∧ c + w ≤ b ∧ ∃ t' ⊆ t,
        (t.card : ℝ) ≤ P₀ * (t'.card : ℝ) ∧
          Nonempty (GridUniform t' T Mgrid Cv) ∧
          ComparableFibreCounts t' T (gridScales δ Mgrid) Cv ∧
          ComparableFibreCountsInflated t' T (gridScales δ Mgrid) Cv ∧
          BlockFrostman t' T Mgrid (stepCut * C) ζ' a c ∧
          BlockFrostman t' T Mgrid (stepCut * C) ζ' c b ∧
          ∀ (C₂ : NNReal) (ζ₂ : ℝ) (a₂ b₂ : ℕ), 0 ≤ ζ₂ → a₂ ≤ b₂ → b₂ ≤ Mgrid →
            BlockFrostman t T Mgrid C₂ ζ₂ a₂ b₂ →
            BlockFrostman t' T Mgrid (stepCut * C₂) ζ₂ a₂ b₂)
    (hpass : ∀ (l : ℕ) (t : Finset ι), t ⊆ s₀ → Nonempty (GridUniform t T Mgrid Cv) →
      ComparableFibreCounts t T (gridScales δ Mgrid) Cv →
      ComparableFibreCountsInflated t T (gridScales δ Mgrid) Cv →
      ∃ t' ⊆ t,
        (t.card : ℝ) ≤ P₁ * (t'.card : ℝ) ∧
          Nonempty (GridUniform t' T Mgrid Cv) ∧
          ComparableFibreCounts t' T (gridScales δ Mgrid) Cv ∧
          ComparableFibreCountsInflated t' T (gridScales δ Mgrid) Cv ∧
          Inv l t' ∧
          ∀ i₀ ∈ t', ∀ a ≤ Mgrid,
            ((fibreIndex t T δ (gridScale δ Mgrid a) i₀).card : ENNReal)
              ≤ (Ainv : ENNReal)
                * ((fibreIndex t' T δ (gridScale δ Mgrid a) i₀).card : ENNReal))
    (l : ℕ) (t : Finset ι) (hts : t ⊆ s₀)
    (hGt : Nonempty (GridUniform t T Mgrid Cv))
    (hCt : ComparableFibreCounts t T (gridScales δ Mgrid) Cv)
    (C : NNReal) (ζ ζ' : ℝ) (hζ : 0 ≤ ζ) (hζ'0 : 0 ≤ ζ') (hgap : ζ ≤ ε * ζ') (hζ' : ζ' ≤ ε)
    (a b : ℕ) (hbM : b ≤ Mgrid) (hlong : IsLongBlock Mgrid ε a b)
    (hbf : BlockFrostman t T Mgrid C ζ a b)
    (htest : t.card ≤ 2 * (passingNodes t T Mgrid C ε ζ' a b).card) :
    ∃ c : ℕ, a + w ≤ c ∧ c + w ≤ b ∧ ∃ t' ⊆ t,
      (t.card : ℝ) ≤ P₀ * P₁ * (t'.card : ℝ) ∧
        Nonempty (GridUniform t' T Mgrid Cv) ∧
        ComparableFibreCounts t' T (gridScales δ Mgrid) Cv ∧
        ComparableFibreCountsInflated t' T (gridScales δ Mgrid) Cv ∧
        Inv l t' ∧
        BlockFrostman t' T Mgrid (step * C) ζ' a c ∧
        BlockFrostman t' T Mgrid (step * C) ζ' c b ∧
        ∀ (C₂ : NNReal) (ζ₂ : ℝ) (a₂ b₂ : ℕ), 0 ≤ ζ₂ → a₂ ≤ b₂ → b₂ ≤ Mgrid →
          BlockFrostman t T Mgrid C₂ ζ₂ a₂ b₂ →
          BlockFrostman t' T Mgrid (step * C₂) ζ₂ a₂ b₂ := by
  classical
  have hd1nn : δ ≤ 1 := by exact_mod_cast hδ1
  obtain ⟨cut, hca, hcb, t', hsub1, hcard1, hG1, hC1, hCI1, hfineAC, hfineCB, hdesc⟩ :=
    hcut t hts hGt hCt C ζ ζ' hζ hgap hζ' a b hbM hlong hbf htest
  obtain ⟨t2, hsub2, hcard2, hG2, hC2, hCI2, hInv2, hBK⟩ :=
    hpass l t' (hsub1.trans hts) hG1 hC1 hCI1
  have hstepC : ∀ B : NNReal,
      Ainv * (Tube.volume_le.C (Module.finrank ℝ E)
          / Tube.le_volume.c (Module.finrank ℝ E)) * (stepCut * B)
        ≤ step * B := fun B => by
    rw [← mul_assoc]; exact mul_le_mul_left hstep B
  have hmove : ∀ (B : NNReal) (z : ℝ) (u v : ℕ), 0 ≤ z → u ≤ v → v ≤ Mgrid →
      BlockFrostman t' T Mgrid (stepCut * B) z u v →
      BlockFrostman t2 T Mgrid (step * B) z u v := fun B z u v hz huv hvm hB3 =>
    (BlockFrostman.of_subfamily_pointwise hδ hd1nn huv hvm hsub2
      (fun y hy => hBK y hy u (huv.trans hvm)) hB3).mono hδ hd1nn (hstepC B) hz le_rfl huv
  refine ⟨cut, hca, hcb, t2, hsub2.trans hsub1, ?_, hG2, hC2, hCI2, hInv2,
    hmove C ζ' a cut hζ'0 (by omega) (by omega) hfineAC,
    hmove C ζ' cut b hζ'0 (by omega) (by omega) hfineCB,
    fun B z u v hz huv hvM hB4 => hmove B z u v hz huv hvM (hdesc B z u v hz huv hvM hB4)⟩
  calc
    (t.card : ℝ) ≤ P₀ * (t'.card : ℝ) := hcard1
    _ ≤ P₀ * (P₁ * (t2.card : ℝ)) := mul_le_mul_of_nonneg_left hcard2 hP₀
    _ = P₀ * P₁ * (t2.card : ℝ) := by ring

/-! ### The run of the stopping time with an abstract state invariant -/

/-- **The run of the hoisted stopping time with an abstract state invariant.**
`exists_maximal_cuts_abstract_state_margin` instantiated at the states `(t, l)` consisting of a
grid-uniform subfamily `t ⊆ s₀` with comparable fibre counts, satisfying `Inv l t` and carrying the
block bound `Good_l(0, Mgrid)` at the constant `step^l · baseC`.  The invariant is restored after
every refinement, so the per-round losses are those of the cut composed with those of the pass. -/
theorem exists_hoisted_cuts_run_blocks
    (N Mgrid w : ℕ) (hw : 0 < w) (hwM : w ≤ Mgrid) (hwN : Mgrid ≤ w * N)
    {ε : ℝ} (η : ℕ → ℝ) (hηnonneg : ∀ k ≤ N, 0 ≤ η k)
    (hηmono : ∀ ⦃j j' : ℕ⦄, j ≤ j' → j' ≤ N → η j ≤ η j')
    (hηgap : ∀ k < N, η k ≤ ε * η (k + 1)) (hηε : ∀ k ≤ N, η k ≤ ε)
    {ι : Type u} {δ : NNReal} (hδ : 0 < δ) (hδ1 : (δ : ℝ) ≤ 1)
    (s₀ : Finset ι) (T : ι → Tube δ E) (Cv : NNReal)
    (P₀ P₁ P : ℝ) (hP₀ : 0 ≤ P₀) (hP₁ : 0 ≤ P₁) (hP₀P : P₀ * P₁ ≤ P)
    (stepCut step baseC Ainv : NNReal)
    (hstep : Ainv * (Tube.volume_le.C (Module.finrank ℝ E)
        / Tube.le_volume.c (Module.finrank ℝ E)) * stepCut ≤ step)
    (Inv : ℕ → Finset ι → Prop) (hInv₀ : Inv 0 s₀)
    (hG₀ : Nonempty (GridUniform s₀ T Mgrid Cv))
    (hC₀ : ComparableFibreCounts s₀ T (gridScales δ Mgrid) Cv)
    (hCI₀ : ComparableFibreCountsInflated s₀ T (gridScales δ Mgrid) Cv)
    (hgood₀ : BlockFrostman s₀ T Mgrid baseC (η 0) 0 Mgrid)
    (hcut : ∀ t : Finset ι, t ⊆ s₀ → Nonempty (GridUniform t T Mgrid Cv) →
      ComparableFibreCounts t T (gridScales δ Mgrid) Cv →
      ∀ (C : NNReal) (ζ ζ' : ℝ), 0 ≤ ζ → ζ ≤ ε * ζ' → ζ' ≤ ε →
      ∀ a b : ℕ, b ≤ Mgrid → IsLongBlock Mgrid ε a b →
      BlockFrostman t T Mgrid C ζ a b →
      t.card ≤ 2 * (passingNodes t T Mgrid C ε ζ' a b).card →
      ∃ c : ℕ, a + w ≤ c ∧ c + w ≤ b ∧ ∃ t' ⊆ t,
        (t.card : ℝ) ≤ P₀ * (t'.card : ℝ) ∧
          Nonempty (GridUniform t' T Mgrid Cv) ∧
          ComparableFibreCounts t' T (gridScales δ Mgrid) Cv ∧
          ComparableFibreCountsInflated t' T (gridScales δ Mgrid) Cv ∧
          BlockFrostman t' T Mgrid (stepCut * C) ζ' a c ∧
          BlockFrostman t' T Mgrid (stepCut * C) ζ' c b ∧
          ∀ (C₂ : NNReal) (ζ₂ : ℝ) (a₂ b₂ : ℕ), 0 ≤ ζ₂ → a₂ ≤ b₂ → b₂ ≤ Mgrid →
            BlockFrostman t T Mgrid C₂ ζ₂ a₂ b₂ →
            BlockFrostman t' T Mgrid (stepCut * C₂) ζ₂ a₂ b₂)
    (hpass : ∀ (l : ℕ) (t : Finset ι), t ⊆ s₀ → Nonempty (GridUniform t T Mgrid Cv) →
      ComparableFibreCounts t T (gridScales δ Mgrid) Cv →
      ComparableFibreCountsInflated t T (gridScales δ Mgrid) Cv →
      ∃ t' ⊆ t,
        (t.card : ℝ) ≤ P₁ * (t'.card : ℝ) ∧
          Nonempty (GridUniform t' T Mgrid Cv) ∧
          ComparableFibreCounts t' T (gridScales δ Mgrid) Cv ∧
          ComparableFibreCountsInflated t' T (gridScales δ Mgrid) Cv ∧
          Inv l t' ∧
          ∀ i₀ ∈ t', ∀ a ≤ Mgrid,
            ((fibreIndex t T δ (gridScale δ Mgrid a) i₀).card : ENNReal)
              ≤ (Ainv : ENNReal)
                * ((fibreIndex t' T δ (gridScale δ Mgrid a) i₀).card : ENNReal)) :
    ∃ (S : Finset ℕ) (m : ℕ) (tL : Finset ι), m < N ∧ tL ⊆ s₀ ∧
      (s₀.card : ℝ) ≤ P ^ m * (tL.card : ℝ) ∧
      Nonempty (GridUniform tL T Mgrid Cv) ∧
      ComparableFibreCounts tL T (gridScales δ Mgrid) Cv ∧
      ComparableFibreCountsInflated tL T (gridScales δ Mgrid) Cv ∧
      Inv m tL ∧
      BlockFrostman tL T Mgrid (step ^ m * baseC) (η m) 0 Mgrid ∧
      0 ∈ S ∧ Mgrid ∈ S ∧ S ⊆ Finset.range (Mgrid + 1) ∧ S.card = m + 2 ∧
      ∀ a ∈ S, ∀ b ∈ S, a < b → (∀ y ∈ S, ¬(a < y ∧ y < b)) →
        BlockFrostman tL T Mgrid (step ^ m * baseC) (η m) a b ∧
          (¬ IsLongBlock Mgrid ε a b ∨
            ¬ (tL.card
                ≤ 2 * (passingNodes tL T Mgrid (step ^ m * baseC) ε (η (m + 1)) a b).card)) := by
  let ct : ℕ → NNReal := fun l => step ^ l * baseC
  let etaN : ℕ → ℝ := fun p => η (min p N)
  have hetaN_mono : ∀ {p q : ℕ}, p ≤ q → etaN p ≤ etaN q := fun {p q} hpq =>
    hηmono (min_le_min_right N hpq) (min_le_right q N)
  have hetaN_of : ∀ {p : ℕ}, p ≤ N → etaN p = η p := fun {p} hp => by
    simp only [etaN, min_eq_left hp]
  have hetaN_nonneg : ∀ p : ℕ, 0 ≤ etaN p := fun p => hηnonneg _ (min_le_right p N)
  have hP : 0 ≤ P := le_trans (mul_nonneg hP₀ hP₁) hP₀P
  let σ : Type u := { p : Finset ι × ℕ //
      p.1 ⊆ s₀ ∧ Nonempty (GridUniform p.1 T Mgrid Cv) ∧
      ComparableFibreCounts p.1 T (gridScales δ Mgrid) Cv ∧
      ComparableFibreCountsInflated p.1 T (gridScales δ Mgrid) Cv ∧
      Inv p.2 p.1 ∧
      BlockFrostman p.1 T Mgrid (ct p.2) (etaN p.2) 0 Mgrid }
  let Good : ℕ → ℕ → ℕ → σ → Prop :=
    fun j a b x => BlockFrostman x.1.1 T Mgrid (ct x.1.2) (etaN j) a b
  let Test : ℕ → ℕ → ℕ → σ → Prop :=
    fun j a b x => x.1.1.card ≤ 2 * (passingNodes x.1.1 T Mgrid (ct x.1.2) ε (etaN j) a b).card
  let Long : ℕ → ℕ → Prop :=
    fun a b => IsLongBlock Mgrid ε a b
  have hct_add : ∀ p k : ℕ, ct (p + k) = step ^ k * ct p := fun p k => by
    simp only [ct, pow_add]; ring
  let Rel : ℕ → σ → σ → Prop := fun k x y =>
    y.1.1 ⊆ x.1.1 ∧
      (x.1.1.card : ℝ) ≤ P ^ k * (y.1.1.card : ℝ) ∧
      ct y.1.2 ≤ step ^ k * ct x.1.2 ∧ y.1.2 = x.1.2 + k ∧
      ∀ (C₂ : NNReal) (ζ₂ : ℝ) (a₂ b₂ : ℕ), 0 ≤ ζ₂ → a₂ ≤ b₂ → b₂ ≤ Mgrid →
        BlockFrostman x.1.1 T Mgrid C₂ ζ₂ a₂ b₂ →
        BlockFrostman y.1.1 T Mgrid (step ^ k * C₂) ζ₂ a₂ b₂
  let x₀ : σ :=
    ⟨(s₀, 0), Finset.Subset.refl s₀, hG₀, hC₀, hCI₀, hInv₀, by simpa [ct, etaN] using hgood₀⟩
  have hGood : Good 0 0 Mgrid x₀ := x₀.2.2.2.2.2.2
  have hrefl : ∀ x : σ, Rel 0 x x := fun x =>
    ⟨Finset.Subset.refl _, by simp, by simp, by simp,
      fun _ _ _ _ _ _ _ hBF => by simpa using hBF⟩
  have hcomp : ∀ (k l : ℕ) (x y z : σ), Rel k x y → Rel l y z → Rel (k + l) x z := by
    intro k l x y z ⟨hyx, hyyc, hcty, hly, hdxy⟩ ⟨hzy, hzz, hctz, hlz, hdyz⟩
    refine ⟨hzy.trans hyx, ?_, ?_, by omega, ?_⟩
    · calc
        (x.1.1.card : ℝ) ≤ P ^ k * (y.1.1.card : ℝ) := hyyc
        _ ≤ P ^ k * (P ^ l * (z.1.1.card : ℝ)) := mul_le_mul_of_nonneg_left hzz (pow_nonneg hP k)
        _ = P ^ (k + l) * (z.1.1.card : ℝ) := by rw [← mul_assoc, ← pow_add]
    · calc
        ct z.1.2 ≤ step ^ l * ct y.1.2 := hctz
        _ ≤ step ^ l * (step ^ k * ct x.1.2) := mul_le_mul' le_rfl hcty
        _ = step ^ (k + l) * ct x.1.2 := by rw [← mul_assoc, ← pow_add, add_comm l k]
    · intro C₂ ζ₂ a₂ b₂ hζ₂ hab₂ hb₂M hBF
      have h2 := hdyz (step ^ k * C₂) ζ₂ a₂ b₂ hζ₂ hab₂ hb₂M
        (hdxy C₂ ζ₂ a₂ b₂ hζ₂ hab₂ hb₂M hBF)
      rwa [← mul_assoc, ← pow_add, add_comm l k] at h2
  have hmono : ∀ j j' : ℕ, j ≤ j' → j' ≤ N → ∀ a b : ℕ, a < b → ∀ x : σ,
      Good j a b x → Good j' a b x := fun j _ hjj' _ _ _ hab _ hg =>
    hg.mono hδ hδ1 le_rfl (hetaN_nonneg j) (hetaN_mono hjj') hab.le
  have hdescend : ∀ j a b : ℕ, a < b → b ≤ Mgrid → ∀ x y : σ, Rel 1 x y →
      Good j a b x → Good j a b y := by
    intro j a b hab hbM x y ⟨_, _, _, hlvl, hdesc⟩ hg
    change BlockFrostman y.1.1 T Mgrid (ct y.1.2) (etaN j) a b
    rw [hlvl, hct_add]
    exact hdesc (ct x.1.2) (etaN j) a b (hetaN_nonneg j) hab.le hbM hg
  have hsplit : ∀ j a b : ℕ, j + 1 ≤ N → a < b → b ≤ Mgrid → Long a b →
      ∀ x : σ, Good j a b x → Test (j + 1) a b x →
        ∃ (y : σ) (c : ℕ), Rel 1 x y ∧ a + w ≤ c ∧ c + w ≤ b ∧
          Good (j + 1) a c y ∧ Good (j + 1) c b y := by
    intro j a b hjn hab hbM hlong x hg ht
    have hgapj : etaN j ≤ ε * etaN (j + 1) := by
      rw [hetaN_of (by omega : j ≤ N), hetaN_of hjn]; exact hηgap j (by omega)
    have hεj : etaN (j + 1) ≤ ε := by rw [hetaN_of hjn]; exact hηε (j + 1) hjn
    obtain ⟨c, hac, hcb, t', ht't, htcard, hG', hC', hCI', hInv', hfineAC, hfineCB, hdesc⟩ :=
      exists_cut_with_pass Mgrid w hδ hδ1 s₀ T Cv P₀ P₁ hP₀ stepCut step Ainv hstep Inv hcut hpass
        (x.1.2 + 1) x.1.1 x.2.1 x.2.2.1 x.2.2.2.1
        (ct x.1.2) (etaN j) (etaN (j + 1)) (hetaN_nonneg j) (hetaN_nonneg (j + 1)) hgapj hεj
        a b hbM hlong hg ht
    have hconst : step * ct x.1.2 = ct (x.1.2 + 1) := by rw [hct_add]; simp
    have hzeroN : BlockFrostman t' T Mgrid (ct (x.1.2 + 1)) (etaN (x.1.2 + 1)) 0 Mgrid := by
      rw [← hconst]
      exact (hdesc (ct x.1.2) (etaN x.1.2) 0 Mgrid (hetaN_nonneg x.1.2) (Nat.zero_le Mgrid)
        le_rfl x.2.2.2.2.2.2).mono hδ hδ1 le_rfl (hetaN_nonneg x.1.2)
          (hetaN_mono (Nat.le_succ _)) (Nat.zero_le Mgrid)
    refine ⟨⟨(t', x.1.2 + 1), ht't.trans x.2.1, hG', hC', hCI', hInv', hzeroN⟩, c,
      ⟨ht't, ?_, by rw [← hconst]; simp, rfl,
        fun C₂ ζ₂ a₂ b₂ hζ₂ hab₂ hb₂M hBF => by
          simpa using hdesc C₂ ζ₂ a₂ b₂ hζ₂ hab₂ hb₂M hBF⟩, hac, hcb, ?_, ?_⟩
    · exact htcard.trans (mul_le_mul_of_nonneg_right (by simpa [pow_one] using hP₀P)
        (by exact_mod_cast Nat.zero_le t'.card))
    · change BlockFrostman t' T Mgrid (ct (x.1.2 + 1)) (etaN (j + 1)) a c
      rw [← hconst]; exact hfineAC
    · change BlockFrostman t' T Mgrid (ct (x.1.2 + 1)) (etaN (j + 1)) c b
      rw [← hconst]; exact hfineCB
  obtain ⟨S, m, x, hm, hRel, h0S, hMS, hSsub, hScard, hAll⟩ :=
    exists_maximal_cuts_abstract_state_margin (σ := σ) Mgrid N w hw hwM hwN
      Good Test Long Rel x₀ hrefl hcomp hGood hmono hdescend hsplit
  have hxlvl : x.1.2 = m := by simpa [x₀] using hRel.2.2.2.1
  have hctm : ct m = step ^ m * baseC := rfl
  have hminm : min m N = m := by omega
  have hminm1 : min (m + 1) N = m + 1 := by omega
  refine ⟨S, m, x.1.1, hm, x.2.1, by simpa [x₀] using hRel.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
    by rw [← hxlvl]; exact x.2.2.2.2.2.1, ?_, h0S, hMS, hSsub, hScard, ?_⟩
  · have h := x.2.2.2.2.2.2
    rwa [hxlvl, hctm, hetaN_of (le_of_lt hm)] at h
  · simpa only [Good, Test, Long, ct, etaN, hxlvl, hminm, hminm1] using hAll

/-- **The stopping time with the grid length and the step budget separated, carrying an abstract
state invariant, at a quadratic pass budget** (blueprint
`lem:dividingScales_stoppingTime_instance_blocks_quad`).  As the narrow engine, except that both
polylogarithmic exponents of the pass read `K ((Mgrid+2)(Mgrid+1))`, and the per-anchor constant
`Cpass` and the terminal block constant `C₁` are quantified **after** the state constant `Cv`. -/
theorem exists_maximal_cuts_state_instance_hoisted_blocks_quad (Cu : NNReal) (hCu : 1 ≤ Cu)
    (Apass : ℝ) (hApass : 1 ≤ Apass) (Kpass Kpass' : ℕ) :
    ∃ (A : ℝ) (K K₁ : ℕ) (Cv : NNReal), 1 ≤ A ∧ Cu ≤ Cv ∧
      ∀ Cpass : NNReal, 1 ≤ Cpass →
      ∃ C₁ : NNReal, 1 ≤ C₁ ∧
      ∀ (N : ℕ), 4096 ≤ N → ∀ {ε : ℝ}, ε = 1 / Real.sqrt (N : ℝ) →
      ∀ (Mgrid : ℕ), 16 ≤ Mgrid →
      ∀ {ι : Type u} {δ : NNReal}, 0 < δ → (δ : ℝ) ≤ 1 → δ ≤ (16 : NNReal) ^ (-(Mgrid : ℝ)) →
      ∀ (s : Finset ι) (T : ι → Tube δ E),
      (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall (0 : E) 1) →
      (↑s : Set ι).Pairwise (fun i j => IsEssentiallyDistinct (T i).carrier (T j).carrier) →
      ∀ Inv : ℕ → Finset ι → Prop,
      (∀ (l : ℕ) (t : Finset ι), t ⊆ s → Nonempty (GridUniform t T Mgrid Cv) →
        ComparableFibreCounts t T (gridScales δ Mgrid) Cv →
        ComparableFibreCountsInflated t T (gridScales δ Mgrid) Cv →
        ∃ t' ⊆ t,
          (t.card : ℝ) ≤ Apass ^ (Mgrid + 1)
              * (1 - Real.log (δ : ℝ)) ^ (Kpass * ((Mgrid + 2) * (Mgrid + 1)))
              * (t'.card : ℝ) ∧
            Nonempty (GridUniform t' T Mgrid Cv) ∧
            ComparableFibreCounts t' T (gridScales δ Mgrid) Cv ∧
            ComparableFibreCountsInflated t' T (gridScales δ Mgrid) Cv ∧
            Inv l t' ∧
            ∀ i₀ ∈ t', ∀ a ≤ Mgrid,
              ((fibreIndex t T δ (gridScale δ Mgrid a) i₀).card : ENNReal)
                ≤ ((Cpass ^ (Mgrid + 1)
                      * Real.toNNReal ((1 - Real.log (δ : ℝ))
                          ^ (Kpass' * ((Mgrid + 2) * (Mgrid + 1)))) :
                    NNReal) : ENNReal)
                  * ((fibreIndex t' T δ (gridScale δ Mgrid a) i₀).card : ENNReal)) →
      ∀ η : ℕ → ℝ, 0 ≤ η 0 → (∀ k < N, η k ≤ ε * η (k + 1)) → η N ≤ ε →
      ConvexSpaceBody.frostmanConstant s (fibreBodies T δ) ConvexSpaceBody.closedUnitBall
          ≤ ENNReal.ofReal ((δ : ℝ) ^ (-η 0)) →
      ∃ (S : Finset ℕ) (m L : ℕ) (Ct : NNReal) (tL : Finset ι),
        m < N ∧ L ≤ N + 1 ∧ L ≤ Mgrid + 1 ∧ 1 ≤ Ct ∧
        Ct ≤ (C₁ ^ (Mgrid + 1)
                * Real.toNNReal ((1 - Real.log (δ : ℝ))
                    ^ (K₁ * ((Mgrid + 2) * (Mgrid + 1))))) ^ L ∧
        tL ⊆ s ∧
        (s.card : ℝ)
            ≤ (2 * ((Mgrid : ℝ) + 1) * A ^ (Mgrid + 1)
                * (1 - Real.log (δ : ℝ)) ^ (K * ((Mgrid + 2) * (Mgrid + 1)))) ^ L
              * (tL.card : ℝ) ∧
        Nonempty (GridUniform tL T Mgrid Cv) ∧
        ComparableFibreCounts tL T (gridScales δ Mgrid) Cv ∧
        ComparableFibreCountsInflated tL T (gridScales δ Mgrid) Cv ∧
        Inv m tL ∧
        0 ∈ S ∧ Mgrid ∈ S ∧ S ⊆ Finset.range (Mgrid + 1) ∧ S.card = m + 2 ∧
        (∀ i₀ ∈ tL,
          ConvexSpaceBody.frostmanConstant (fibreIndex tL T δ 1 i₀) (fibreBodies T δ)
              ((T i₀).rescale 1).toConvexSpaceBody
            ≤ (Ct : ENNReal) * ENNReal.ofReal ((δ : ℝ) ^ (-(η m)))) ∧
        ∀ a ∈ S, ∀ b ∈ S, a < b → (∀ x ∈ S, ¬(a < x ∧ x < b)) →
          BlockFrostman tL T Mgrid Ct (η m) a b ∧
            (¬ IsLongBlock Mgrid ε a b ∨
              ¬ (tL.card ≤ 2 * (passingNodes tL T Mgrid Ct ε (η (m + 1)) a b).card)) := by
  classical
  obtain ⟨A₁, K₁₀, Cu₁, hA₁, hCu₁, hgrid⟩ :=
    exists_gridUniform_subfamily_hoisted.{u, _} (E := E)
  have htemp0 := exists_refined_cut_hoisted_margin.{u, _} (E := E) (max Cu Cu₁)
    (le_trans hCu (le_max_left _ _))
  rcases htemp0 with ⟨A₀, K₀, K''₀, Cv₀, C''₀, hA₀, hCu₀, hC''₀, hmain⟩
  have hCv₀one : (1 : NNReal) ≤ Cv₀ := le_trans hCu (le_trans (le_max_left Cu Cu₁) hCu₀)
  obtain ⟨C_frost, hC_frost, hinit⟩ :=
    exists_initial_blockFrostman_hoisted.{u, _} (E := E) Cv₀ hCv₀one
  have hCu₁le : Cu₁ ≤ Cv₀ := le_trans (le_max_right Cu Cu₁) hCu₀
  have hvolfac1 : (1 : NNReal) ≤
      Tube.volume_le.C (Module.finrank ℝ E) / Tube.le_volume.c (Module.finrank ℝ E) :=
    one_le_volume_ratio_const
  have hApass0 : (0 : ℝ) ≤ Apass := le_trans zero_le_one hApass
  have hA₁A : A₁ ≤ A₁ * Apass := le_mul_of_one_le_right (by linarith) hApass
  have hApassA : Apass ≤ A₁ * Apass := le_mul_of_one_le_left hApass0 hA₁
  refine ⟨max (A₀ * Apass) (A₁ * Apass), max (K₀ + Kpass) (K₁₀ + Kpass),
    max (K''₀ + Kpass') (max Kpass' K₁₀), Cv₀,
    le_trans (le_trans hA₁ hA₁A) (le_max_right _ _),
    le_trans (le_max_left Cu Cu₁) hCu₀, ?_⟩
  intro Cpass hCpass
  refine ⟨max 1 (max (C''₀ * Cpass * (Tube.volume_le.C (Module.finrank ℝ E)
        / Tube.le_volume.c (Module.finrank ℝ E)))
    (max (Cpass * (Tube.volume_le.C (Module.finrank ℝ E)
          / Tube.le_volume.c (Module.finrank ℝ E)))
      (C_frost * (Tube.volume_le.C (Module.finrank ℝ E)
          / Tube.le_volume.c (Module.finrank ℝ E)) * Real.toNNReal A₁))),
    le_max_left _ _, ?_⟩
  intro N hN ε hε Mgrid hMgrid ι δ hδ hδ1 hδ0 s T hball hED Inv hpass η hη0 hηgap hηN hfrosthy
  have hNpos : 0 < N := by omega
  have hεpos : 0 < ε := eps_pos_of_eq_one_div_sqrt (by omega : 16 ≤ N) hε
  have hε64 : ε ≤ 1 / 64 := eps_le_one_div_64_of_eq_one_div_sqrt hN hε
  have hε1 : ε ≤ 1 := eps_le_one_of_le_one_div_64 hε64
  have hεsq : ε ^ 2 * (N : ℝ) = 1 := eps_sq_mul_eq_one_of_eq_one_div_sqrt hNpos hε
  have hW1 : (1 : ℝ) ≤ 1 - Real.log (δ : ℝ) := KT.one_le_one_sub_log hδ hδ1
  have hδ1nn : δ ≤ 1 := by exact_mod_cast hδ1
  have hηnonneg : ∀ k ≤ N, 0 ≤ η k := eta_nonneg_of_gap N hNpos hε η hη0 hηgap
  have hηmono : ∀ ⦃j j' : ℕ⦄, j ≤ j' → j' ≤ N → η j ≤ η j' :=
    eta_mono_of_gap' N hNpos hε η hη0 hηgap
  have hηε : ∀ k ≤ N, η k ≤ ε := eta_le_eps_of_mono hηmono hηN
  have hw : 0 < ⌈ε * ((⌈ε * (Mgrid : ℝ)⌉₊ : ℕ) : ℝ)⌉₊ :=
    KT.stoppingMargin_pos hεpos (by omega : 0 < Mgrid)
  have hwM : ⌈ε * ((⌈ε * (Mgrid : ℝ)⌉₊ : ℕ) : ℝ)⌉₊ ≤ Mgrid :=
    KT.stoppingMargin_le hεpos hε1 Mgrid
  have hwN : Mgrid ≤ ⌈ε * ((⌈ε * (Mgrid : ℝ)⌉₊ : ℕ) : ℝ)⌉₊ * N :=
    KT.le_mul_stoppingMargin hεpos hεsq Mgrid
  obtain ⟨s₀, hs₀sub, hs₀card, g₀, hcmp₀, hcmp₀i⟩ :=
    hgrid Mgrid (by omega : 0 < Mgrid) hδ hδ0 s s T (Finset.Subset.refl s) hball hED
  have hG₀ : Nonempty (GridUniform s₀ T Mgrid Cv₀) := ⟨(Classical.choice g₀).mono hCu₁le⟩
  have hC₀ : ComparableFibreCounts s₀ T (gridScales δ Mgrid) Cv₀ := hcmp₀.mono hCu₁le
  have hCI₀ : ComparableFibreCountsInflated s₀ T (gridScales δ Mgrid) Cv₀ := hcmp₀i.mono hCu₁le
  have hinit₀ :
      BlockFrostman s₀ T Mgrid
        (max 1 (C_frost
          * (Real.toNNReal (A₁ ^ (Mgrid + 1)
                * (1 - Real.log (δ : ℝ)) ^ (K₁₀ * (Mgrid + 1)))
            * (Tube.volume_le.C (Module.finrank ℝ E)
                / Tube.le_volume.c (Module.finrank ℝ E))))) (η 0) 0 Mgrid :=
    hinit Mgrid hMgrid hδ hδ1 hδ0 s s₀ T hs₀sub hball hG₀ hC₀ _
      (card_le_toNNReal_mul (gridUniform_loss_nonneg_gen hA₁ hW1 (K₁₀ * (Mgrid + 1)) Mgrid)
        hs₀card) (η 0)
      (hηnonneg 0 (Nat.zero_le N)) hfrosthy _ (le_max_right _ _)
  set vf := Tube.volume_le.C (Module.finrank ℝ E) / Tube.le_volume.c (Module.finrank ℝ E) with hvf
  set P0 : ℝ :=
    2 * ((Mgrid : ℝ) + 1) * A₀ ^ (Mgrid + 1) * (1 - Real.log (δ : ℝ)) ^ (K₀ * (Mgrid + 1)) with hP0
  set P1 : ℝ :=
    Apass ^ (Mgrid + 1) * (1 - Real.log (δ : ℝ)) ^ (Kpass * ((Mgrid + 2) * (Mgrid + 1))) with hP1
  set gl : ℝ := A₁ ^ (Mgrid + 1) * (1 - Real.log (δ : ℝ)) ^ (K₁₀ * (Mgrid + 1)) with hgl
  set Pbig : ℝ :=
    2 * ((Mgrid : ℝ) + 1) * (max (A₀ * Apass) (A₁ * Apass)) ^ (Mgrid + 1) *
      (1 - Real.log (δ : ℝ)) ^
        ((max (K₀ + Kpass) (K₁₀ + Kpass)) * ((Mgrid + 2) * (Mgrid + 1))) with hPbig
  set stepCut : NNReal := C''₀ ^ (Mgrid + 1) *
    Real.toNNReal ((1 - Real.log (δ : ℝ)) ^ (K''₀ * (Mgrid + 1))) with hstepCut
  set Ainv : NNReal := Cpass ^ (Mgrid + 1) *
    Real.toNNReal ((1 - Real.log (δ : ℝ)) ^ (Kpass' * ((Mgrid + 2) * (Mgrid + 1)))) with hAinv
  set stp : NNReal := (C''₀ * Cpass * vf) ^ (Mgrid + 1) *
    Real.toNNReal
      ((1 - Real.log (δ : ℝ)) ^ ((K''₀ + Kpass') * ((Mgrid + 2) * (Mgrid + 1)))) with hstp
  set bse : NNReal := max 1 (C_frost * (Real.toNNReal
    (A₁ ^ (Mgrid + 1) * (1 - Real.log (δ : ℝ)) ^ (K₁₀ * (Mgrid + 1))) * vf)) with hbse
  set G : NNReal :=
    max 1 (max (C''₀ * Cpass * vf) (max (Cpass * vf) (C_frost * vf * Real.toNNReal A₁)))
  have hCle : C''₀ * Cpass * vf ≤ G := le_trans (le_max_left _ _) (le_max_right (1 : NNReal) _)
  have hCpass_vf_le : Cpass * vf ≤ G :=
    le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right (1 : NNReal) _))
  have hC_frost_vf_A₁_le : C_frost * vf * Real.toNNReal A₁ ≤ G :=
    le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right (1 : NNReal) _))
  have hGone : (1 : NNReal) ≤ G := le_max_left _ _
  obtain ⟨s₁, hs₁s₀, hs₁card, hG₁, hC₁', hCI₁, hInv₁, hfib₁⟩ :=
    hpass 0 s₀ hs₀sub hG₀ hC₀ hCI₀
  have hs₁sub : s₁ ⊆ s := Finset.Subset.trans hs₁s₀ hs₀sub
  have hgood₁ : BlockFrostman s₁ T Mgrid (Ainv * vf * bse) (η 0) 0 Mgrid :=
    BlockFrostman.of_subfamily_pointwise hδ hδ1nn (Nat.zero_le Mgrid : 0 ≤ Mgrid) (le_refl Mgrid)
      hs₁s₀ (fun i hi => hfib₁ i hi 0 (Nat.zero_le Mgrid)) hinit₀
  set w : ℕ := ⌈ε * ((⌈ε * (Mgrid : ℝ)⌉₊ : ℕ) : ℝ)⌉₊
  have hsteple : Ainv * vf * stepCut ≤ stp := by
    simp only [Ainv, vf, stepCut, stp]
    exact cutStep_mul_pass_le_gen hvolfac1 le_rfl hW1
      (quad_exp_add_le (le_refl (K''₀ + Kpass')) Mgrid) Mgrid
  have hP0P : P0 * P1 ≤ Pbig := by
    simp only [P0, P1, Pbig]
    rw [refinedCut_loss_mul_pass_loss_gen A₀ Apass (1 - Real.log (δ : ℝ))
        (K₀ * (Mgrid + 1)) (Kpass * ((Mgrid + 2) * (Mgrid + 1))) Mgrid]
    have hA₀Ap : 1 ≤ A₀ * Apass := hApass.trans (le_mul_of_one_le_left hApass0 hA₀)
    exact refinedCut_loss_le_budget_gen hA₀Ap (le_max_left _ _) hW1
      (quad_exp_add_le (le_max_left _ _) Mgrid) Mgrid
  have hP0nn : 0 ≤ P0 := refinedCut_loss_nonneg_gen hA₀ hW1 (K₀ * (Mgrid + 1)) Mgrid
  have hP1nn : 0 ≤ P1 := gridUniform_loss_nonneg_gen hApass hW1
    (Kpass * ((Mgrid + 2) * (Mgrid + 1))) Mgrid
  have hPbig0 : 0 ≤ Pbig := le_trans (mul_nonneg hP0nn hP1nn) hP0P
  have hgl0 : 0 ≤ gl := gridUniform_loss_nonneg_gen hA₁ hW1 (K₁₀ * (Mgrid + 1)) Mgrid
  have hglP : gl ≤ Pbig := by
    simp only [gl, Pbig]
    exact gridUniform_loss_le_budget_gen hA₁ (le_trans hA₁A (le_max_right _ _)) hW1
      (quad_exp_le (le_trans (Nat.le_add_right K₁₀ Kpass) (le_max_right _ _)) Mgrid) Mgrid
  have hP1P : P1 ≤ Pbig := by
    simp only [P1, Pbig]
    exact gridUniform_loss_le_budget_gen hApass (le_trans hApassA (le_max_right _ _)) hW1
      (Nat.mul_le_mul_right _ (le_trans (Nat.le_add_left Kpass K₀) (le_max_left _ _))) Mgrid
  have hbase1 : 1 ≤ Ainv * vf * bse := by
    have hAinv1 : (1 : NNReal) ≤ Ainv :=
      one_le_cutStep_gen hCpass hW1 (Kpass' * ((Mgrid + 2) * (Mgrid + 1))) Mgrid
    exact one_le_mul (one_le_mul hAinv1 hvolfac1) (le_max_left (1 : NNReal) _)
  obtain ⟨S, m, tL, hm, htLs₁, hcardm, hGL, hCL, hCIL, hInvL, hzero, h0S, hMS, hSsub,
      hScard, hAll⟩ :=
    exists_hoisted_cuts_run_blocks N Mgrid w hw hwM hwN
      η hηnonneg hηmono hηgap hηε hδ hδ1 s₁ T Cv₀ P0 P1 Pbig
      hP0nn hP1nn hP0P stepCut stp (Ainv * vf * bse) Ainv hsteple Inv hInv₁ hG₁ hC₁' hCI₁ hgood₁
      (fun t hts hGt hCt C ζ ζ' hζ hgap hζ' a b hbM hlong hbf htest =>
        hmain Mgrid hMgrid hεpos hε64 hδ hδ1 hδ0 s t T
          (Finset.Subset.trans hts (Finset.Subset.trans hs₁s₀ hs₀sub)) hball hED hGt hCt
          C ζ ζ' hζ hgap hζ' a b hbM hlong hbf htest)
      (fun l t hts hGt hCt hCIt =>
        hpass l t (Finset.Subset.trans hts (Finset.Subset.trans hs₁s₀ hs₀sub)) hGt hCt hCIt)
  refine ⟨S, m, m + 2, stp ^ m * (Ainv * vf * bse), tL, hm, by omega, ?_, ?_, ?_,
    Finset.Subset.trans htLs₁ (Finset.Subset.trans hs₁s₀ hs₀sub), ?_,
    hGL, hCL, hCIL, hInvL, h0S, hMS, hSsub, hScard,
    (fun i₀ hi₀ =>
      frostmanConstant_unit_le_of_blockFrostman_zero (by omega : 0 < Mgrid) hzero i₀ hi₀),
    hAll⟩
  · have h := Finset.card_le_card hSsub
    rw [Finset.card_range] at h
    omega
  · have hCbase : (1 : NNReal) ≤ C''₀ * Cpass * vf := one_le_mul (one_le_mul hC''₀ hCpass) hvolfac1
    have hstp1 : 1 ≤ stp := one_le_cutStep_gen hCbase hW1
      ((K''₀ + Kpass') * ((Mgrid + 2) * (Mgrid + 1))) Mgrid
    exact one_le_geomConst hstp1 hbase1 m
  · have hKbase : K''₀ + Kpass' ≤ max (K''₀ + Kpass') (max Kpass' K₁₀) := le_max_left _ _
    have hKp : Kpass' ≤ max (K''₀ + Kpass') (max Kpass' K₁₀) :=
      le_trans (le_max_left _ _) (le_max_right _ _)
    have hK₁₀ : K₁₀ ≤ max (K''₀ + Kpass') (max Kpass' K₁₀) :=
      le_trans (le_max_right _ _) (le_max_right _ _)
    have hstepG : stp ≤ G ^ (Mgrid + 1) * Real.toNNReal
        ((1 - Real.log (δ : ℝ)) ^
          (max (K''₀ + Kpass') (max Kpass' K₁₀) * ((Mgrid + 2) * (Mgrid + 1)))) :=
      cutStep_le_terminalBudget_gen hCle hW1 (Nat.mul_le_mul_right _ hKbase) Mgrid
    exact pow_mul_le_pow_add_two hstepG
      (mul_le_mul' (passStep_le_terminalBudget_gen hvolfac1 hCpass_vf_le hW1
          (Nat.mul_le_mul_right _ hKp) Mgrid)
        (baseConst_le_terminalBudget_gen hC_frost hvolfac1 hA₁ hW1 (quad_exp_le hK₁₀ Mgrid)
          hC_frost_vf_A₁_le hGone Mgrid)) m
  · exact card_accum_two (x := (s.card : ℝ)) (y := (s₀.card : ℝ)) (z := (s₁.card : ℝ))
      (u := (tL.card : ℝ)) (P₁ := gl) (P₂ := P1) (G := Pbig) hPbig0 hglP hP1P
      (Nat.cast_nonneg _) (Nat.cast_nonneg _) m hs₀card hs₁card hcardm

end MultiScaleFac
end Kakeya

end
