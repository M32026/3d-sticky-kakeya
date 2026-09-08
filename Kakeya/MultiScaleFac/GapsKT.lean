/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Density
public import Kakeya.MultiScaleFac.FibrePacking
public import Kakeya.Frostman
public import Kakeya.GridScale
public import Kakeya.MultiScaleFac.BulletThreeKT
public import Kakeya.MultiScaleFac.Loss
public import Kakeya.MultiScaleFac.NodeAncestorSplit
public import Kakeya.MultiScaleFac.Ports
public import Kakeya.MultiScaleFac.RefineStep
public import Kakeya.MultiScaleFac.Stopping
public import Kakeya.Sticky
public import Kakeya.Tube.Basic
public import Kakeya.Tube.CardEssentiallyDistinct
public import Kakeya.Uniform
public import Kakeya.MultiScaleFac.UniformBridgeKT

/-!
# The gaps between the stopping time and the amended dichotomy, half (B)

The half-(B) counterpart of `Kakeya.MultiScaleFac.GapsA`: the four gap lemmas of the Katz-Tao side,
and the pointwise readings they are assembled from.

Sliced out of the former `DividingScalesKT`.
-/

@[expose] public section

open MeasureTheory Real Metric
open scoped Topology

universe u
open Tube

namespace Kakeya

open StickyKakeya

namespace MultiScaleFac

open _root_.StickyKakeya

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

/-! ### The four gaps between the stopping time and the amended statement

The statements of this section are the skeleton of the proof of
`Kakeya.MultiScaleFac.dividingScalesKatzTao`. Each one is a single step between what the
Katz-Tao stopping time and its bridge already deliver and what the amended dichotomy displays, and
together with the transports proved earlier in this file they compose to the main theorem. -/

section SsfGapsKT

/-! **The block invariant, the terminal alternative and the homogenization band** now live in
`Kakeya/MultiScaleFac/StoppingKT.lean`, as
`Kakeya.MultiScaleFac.exists_maximal_cutsKT_hoisted_blocks`.  The two obstructions this file
recorded against the statement have been met there: the dimension hypothesis and the threshold have
joined it, and the homogenizing pass now returns a `Kakeya.MultiScaleFac.GridUniform` rather than a
bundle, by way of `Kakeya.MultiScaleFac.exists_gridUniform_restrict_band`.  Moving the declaration
also moved its proof out of this file, which is already too long for the tooling to work in
comfortably. -/

/-- **Alternative (i) on the `ssfGridLen δ` grid, over `GridUniformCore`** (route (a)).  A one-line corollary of `isKatzTaoAtEveryScale_of_cutsKT_grid_core`, exactly as the
`GridUniform` original below is of `isKatzTaoAtEveryScale_of_cutsKT_grid`.

**Constant.**  `B = Q ^ 2` with `Q` the constant of the grid form at `Cw`; `K = c = 0`.  No new
`Cw` dependence beyond the one documented at the grid form. -/
theorem alternativeOneKT_of_cutsKT_core (hn : Module.finrank ℝ E = 3)
    (Cv Cw Cb : NNReal) (hCv : 1 ≤ Cv) (hCw : 1 ≤ Cw) (hCb : 1 ≤ Cb) :
    ∃ (B : NNReal) (K c : ℕ), 1 ≤ B ∧ Cb ≤ B ∧
      ∀ (N : ℕ), 4096 ≤ N → ∀ {ε : ℝ}, ε = 1 / Real.sqrt (N : ℝ) →
      ∀ (Mgrid : ℕ), 16 ≤ Mgrid → N ≤ Mgrid →
      ∀ {ι : Type u} {δ : NNReal}, 0 < δ → δ ≤ 1 → δ ≤ (16 : NNReal) ^ (-(Mgrid : ℝ)) →
      Mgrid ≤ ssfGridLen δ →
      ∀ (t : Finset ι) (T : ι → Tube δ E), t.Nonempty →
      (∀ i ∈ t, (T i).carrier ⊆ Metric.closedBall (0 : E) 1) →
      ∀ (𝒞 : GridUniformCore t T Mgrid Cv) (𝒱 : Tube.UniformTubeSet t T Mgrid Cw),
        𝒱.cover = 𝒞.cover →
      ∀ (ζ : ℝ), 0 ≤ ζ → ζ ≤ ε →
      ∀ S : Finset ℕ, 0 ∈ S → Mgrid ∈ S →
      (∀ a ∈ S, ∀ b ∈ S, a < b → (∀ x ∈ S, ¬(a < x ∧ x < b)) →
        BlockKatzTaoOn t 𝒞.uniformAt Cb ζ a b ∧ ¬ IsLongBlock Mgrid ε a b) →
      𝒱.IsKatzTaoAtEveryScale
        ((B : ENNReal) * totalLoss B K c δ
          * ENNReal.ofReal ((δ : ℝ) ^ (-(5 * ε)))) := by
  obtain ⟨Q, hQ1, hCbQ, hmain⟩ :=
    isKatzTaoAtEveryScale_of_cutsKT_grid_core.{u, _} (E := E) hn Cv Cw hCv hCw Cb hCb
  refine ⟨Q ^ 2, 0, 0, one_le_pow₀ hQ1, le_trans hCbQ (le_self_pow hQ1 two_ne_zero), ?_⟩
  intro N hN eps heps Mgrid hM16 hNM iota delta hd0 hd1 hdM hMss t T hs hball CC VV hcov zeta
    hz0 hzeps S hS0 hSM hblocks
  have hepsnn : (0 : ℝ) ≤ eps := by
    rw [heps]
    positivity
  exact (hmain N hN heps Mgrid hNM hd0 hd1 hdM t T hs hball CC VV hcov zeta hz0 hzeps S hS0 hSM
      hblocks).mono
    (katzTao_bound_le_totalLoss_bound hQ1 hd0 hd1 hMss 0 0 hepsnn)

/-- **Alternative (i), on the `ssfGridLen δ` grid and at the displayed loss.**  The port of
`Kakeya.StickyKakeya.isKatzTaoAtEveryScale_of_cutsKT` in which the grid length is a parameter
independent of the step bound, and in which the conclusion is weakened from the fixed power
`δ^{-4ε}` to `C · totalLoss · δ^{-5ε}`.  The grid length is tied by `Mgrid ≤ ssfGridLen δ`.

**The statement is unchanged**; the proof is one line through
`alternativeOneKT_of_cutsKT_core` at `Cw := uniformTubeSetCuOf Cv`. -/
theorem alternativeOneKT_of_cutsKT (hn : Module.finrank ℝ E = 3) (Cv Cb : NNReal)
    (hCv : 1 ≤ Cv) (hCb : 1 ≤ Cb) :
    ∃ (B : NNReal) (K c : ℕ), 1 ≤ B ∧ Cb ≤ B ∧
      ∀ (N : ℕ), 4096 ≤ N → ∀ {ε : ℝ}, ε = 1 / Real.sqrt (N : ℝ) →
      ∀ (Mgrid : ℕ), 16 ≤ Mgrid → N ≤ Mgrid →
      ∀ {ι : Type u} {δ : NNReal}, 0 < δ → δ ≤ 1 → δ ≤ (16 : NNReal) ^ (-(Mgrid : ℝ)) →
      Mgrid ≤ ssfGridLen δ →
      ∀ (t : Finset ι) (T : ι → Tube δ E), t.Nonempty →
      (∀ i ∈ t, (T i).carrier ⊆ Metric.closedBall (0 : E) 1) →
      ∀ (𝒢 : GridUniform t T Mgrid Cv) (ζ : ℝ), 0 ≤ ζ → ζ ≤ ε →
      ∀ S : Finset ℕ, 0 ∈ S → Mgrid ∈ S →
      (∀ a ∈ S, ∀ b ∈ S, a < b → (∀ x ∈ S, ¬(a < x ∧ x < b)) →
        BlockKatzTaoOn t 𝒢.uniformAt Cb ζ a b ∧ ¬ IsLongBlock Mgrid ε a b) →
      (𝒢.toUniformTubeSet).IsKatzTaoAtEveryScale
        ((B : ENNReal) * totalLoss B K c δ
          * ENNReal.ofReal ((δ : ℝ) ^ (-(5 * ε)))) := by
  obtain ⟨B, K, c, hB1, hCbB, h⟩ := alternativeOneKT_of_cutsKT_core.{u, _} (E := E) hn Cv
    (uniformTubeSetCuOf (E := E) Cv) Cb hCv (le_trans hCv (le_max_left _ _)) hCb
  refine ⟨B, K, c, hB1, hCbB, ?_⟩
  intro N hN eps heps Mgrid hM16 hNM iota delta hd0 hd1 hdM hMss t T hs hball GG zeta hz0 hzeps S
    hS0 hSM hblocks
  exact h N hN heps Mgrid hM16 hNM hd0 hd1 hdM hMss t T hs hball GG.toGridUniformCore
    GG.toUniformTubeSet rfl zeta hz0 hzeps S hS0 hSM hblocks

/-- **Alternative (ii) on the `ssfGridLen δ` grid, over `GridUniformCore`** (route (a)).  A one-line corollary of
`alternative_two_of_terminal_blockKT_grid_core`, exactly as the `GridUniform` original below is of
`alternative_two_of_terminal_blockKT_grid`; the `totalLoss` repackaging is untouched by the swap
because it is applied to the constant, not to the family.

**Constant.**  `C = Q ^ 2` with `Q` the constant of the grid form at `Cw`, so the only `Cw`
dependence is the one already documented there.  The `K = cL = 0` slots are unchanged. -/
theorem alternativeTwoKT_of_terminal_block_core (hn : Module.finrank ℝ E = 3)
    (Cv Cw Cb : NNReal) (hCv : 1 ≤ Cv) (hCw : 1 ≤ Cw) (hCb : 1 ≤ Cb) :
    ∃ (C : NNReal) (K cL : ℕ), 1 ≤ C ∧ Cb ≤ C ∧
      ∀ (N : ℕ), 4096 ≤ N → ∀ {ε : ℝ}, ε = 1 / Real.sqrt (N : ℝ) →
      ∀ (Mgrid : ℕ), 16 ≤ Mgrid → N ≤ Mgrid →
      ∀ {ι : Type u} {δ : NNReal}, 0 < δ → δ ≤ 1 → δ ≤ (16 : NNReal) ^ (-(Mgrid : ℝ)) →
      Mgrid ≤ ssfGridLen δ →
      ∀ (t : Finset ι) (T : ι → Tube δ E), t.Nonempty →
      (∀ i ∈ t, (T i).carrier ⊆ Metric.closedBall (0 : E) 1) →
      ∀ (𝒞 : GridUniformCore t T Mgrid Cv) (𝒱 : Tube.UniformTubeSet t T Mgrid Cw),
        𝒱.cover = 𝒞.cover →
      ∀ (ζ ζ' : ℝ), 0 ≤ ζ → 0 ≤ ζ' →
      ∀ S : Finset ℕ, 0 ∈ S → Mgrid ∈ S →
      (∀ a ∈ S, ∀ b ∈ S, a < b → (∀ x ∈ S, ¬(a < x ∧ x < b)) →
        BlockKatzTaoOn t 𝒞.uniformAt Cb ζ a b) →
      ∀ a b : ℕ, a ∈ S → b ∈ S → a < b → (∀ x ∈ S, ¬(a < x ∧ x < b)) →
      IsLongBlock Mgrid ε a b → b ≤ Mgrid →
      ¬ (t.card ≤ 2 * (passingNodesKT t 𝒞.uniformAt Cb ε ζ' a b).card) →
      ∃ F ⊆ 𝒞.cover.indexSet a,
        (((𝒞.cover.indexSet a).card : ENNReal)
            ≤ (C : ENNReal) * totalLoss C K cL δ * (F.card : ENNReal)) ∧
        Kakeya.maxDensity (𝒞.cover.indexSet a)
            (fun j => (𝒞.cover.tube a j).toConvexSpaceBody)
          ≤ (C : ENNReal) * totalLoss C K cL δ
              * ENNReal.ofReal ((gridScale δ Mgrid a : ℝ) ^ (-ζ)) ∧
        (∀ j ∈ 𝒞.cover.indexSet a,
          Kakeya.maxDensity (𝒱.nodesUnder b a j)
              (fun j' => (𝒞.cover.tube b j').toConvexSpaceBody)
            ≤ (C : ENNReal) * totalLoss C K cL δ
                * ENNReal.ofReal
                (((gridScale δ Mgrid a : ℝ) / (gridScale δ Mgrid b : ℝ)) ^ ζ)) ∧
        (∀ c : ℕ, a + ⌈ε * ((b : ℝ) - (a : ℝ))⌉₊ ≤ c →
          c + ⌈ε * ((b : ℝ) - (a : ℝ))⌉₊ ≤ b →
          ∀ j ∈ F,
            ENNReal.ofReal (((gridScale δ Mgrid a : ℝ) / (gridScale δ Mgrid c : ℝ)) ^ ζ')
              ≤ (C : ENNReal) * totalLoss C K cL δ *
                  Kakeya.maxDensity
                    (𝒱.nodesIn c
                      (((𝒞.cover.tube a j).rescale
                          (8 * gridScale δ Mgrid a)).toConvexSpaceBody))
                    (fun j' => (𝒞.cover.tube c j').toConvexSpaceBody)) := by
  obtain ⟨Q, hQ1, hCbQ, hmain⟩ :=
    alternative_two_of_terminal_blockKT_grid_core.{u, _} (E := E) hn Cv Cw hCv hCw Cb hCb
  refine ⟨Q ^ 2, 0, 0, one_le_pow₀ hQ1, le_trans hCbQ (le_self_pow hQ1 two_ne_zero), ?_⟩
  intro N hN eps heps Mgrid hM16 hNM iota delta hd0 hd1 hdM hMss t T hs hball CC VV hcov
    zeta zeta' hz0 hz'0 S hS0 hSM hblocks a b haS hbS hab hadj hlong hbM hnotpass
  obtain ⟨F, hFsub, hc1, hc2, hc3, hc4⟩ :=
    hmain Mgrid (by omega) hd0 hd1 hdM t T hs hball CC VV hcov eps zeta zeta' hz0 hz'0 S hS0
      hblocks a b haS hbS hab hadj hbM hnotpass
  have hpow := pow_le_mul_ofReal_totalLoss hQ1 hd0 hd1 hMss 0 0
  exact ⟨F, hFsub, natCast_le_mul_totalLoss_mul_natCast hQ1 hd0 hd1 hMss 0 0 hc1,
    hc2.trans (mul_le_mul_left hpow _),
    fun j hj => (hc3 j hj).trans (mul_le_mul_left hpow _),
    fun c hl hr j hjF => (hc4 c hl hr j hjF).trans
      (pow_mul_le_mul_ofReal_totalLoss_mul hQ1 hd0 hd1 hMss 0 0 _)⟩

/-- **Alternative (ii), on the `ssfGridLen δ` grid.**  The port of
`Kakeya.MultiScaleFac.alternative_two_of_terminal_blockKT_grid` with the grid length separated from
the step bound.  Its three conclusions are unchanged in content — the maximal density of the coarse
level, that of the fine nodes under a coarse node, and the lower bound at the pair `(σ_a, σ_c)` on
the majority set `F` — but every constant is displayed as `C · totalLoss C K c δ`.

**The statement is unchanged**; the proof is one line through
`alternativeTwoKT_of_terminal_block_core` at `Cw := uniformTubeSetCuOf Cv`. -/
theorem alternativeTwoKT_of_terminal_block (hn : Module.finrank ℝ E = 3) (Cv Cb : NNReal)
    (hCv : 1 ≤ Cv) (hCb : 1 ≤ Cb) :
    ∃ (C : NNReal) (K cL : ℕ), 1 ≤ C ∧ Cb ≤ C ∧
      ∀ (N : ℕ), 4096 ≤ N → ∀ {ε : ℝ}, ε = 1 / Real.sqrt (N : ℝ) →
      ∀ (Mgrid : ℕ), 16 ≤ Mgrid → N ≤ Mgrid →
      ∀ {ι : Type u} {δ : NNReal}, 0 < δ → δ ≤ 1 → δ ≤ (16 : NNReal) ^ (-(Mgrid : ℝ)) →
      Mgrid ≤ ssfGridLen δ →
      ∀ (t : Finset ι) (T : ι → Tube δ E), t.Nonempty →
      (∀ i ∈ t, (T i).carrier ⊆ Metric.closedBall (0 : E) 1) →
      ∀ (𝒢 : GridUniform t T Mgrid Cv) (ζ ζ' : ℝ), 0 ≤ ζ → 0 ≤ ζ' →
      ∀ S : Finset ℕ, 0 ∈ S → Mgrid ∈ S →
      (∀ a ∈ S, ∀ b ∈ S, a < b → (∀ x ∈ S, ¬(a < x ∧ x < b)) →
        BlockKatzTaoOn t 𝒢.uniformAt Cb ζ a b) →
      ∀ a b : ℕ, a ∈ S → b ∈ S → a < b → (∀ x ∈ S, ¬(a < x ∧ x < b)) →
      IsLongBlock Mgrid ε a b → b ≤ Mgrid →
      ¬ (t.card ≤ 2 * (passingNodesKT t 𝒢.uniformAt Cb ε ζ' a b).card) →
      ∃ F ⊆ 𝒢.cover.indexSet a,
        (((𝒢.cover.indexSet a).card : ENNReal)
            ≤ (C : ENNReal) * totalLoss C K cL δ * (F.card : ENNReal)) ∧
        Kakeya.maxDensity (𝒢.cover.indexSet a)
            (fun j => (𝒢.cover.tube a j).toConvexSpaceBody)
          ≤ (C : ENNReal) * totalLoss C K cL δ
              * ENNReal.ofReal ((gridScale δ Mgrid a : ℝ) ^ (-ζ)) ∧
        (∀ j ∈ 𝒢.cover.indexSet a,
          Kakeya.maxDensity (𝒢.toUniformTubeSet.nodesUnder b a j)
              (fun j' => (𝒢.cover.tube b j').toConvexSpaceBody)
            ≤ (C : ENNReal) * totalLoss C K cL δ
                * ENNReal.ofReal
                (((gridScale δ Mgrid a : ℝ) / (gridScale δ Mgrid b : ℝ)) ^ ζ)) ∧
        (∀ c : ℕ, a + ⌈ε * ((b : ℝ) - (a : ℝ))⌉₊ ≤ c →
          c + ⌈ε * ((b : ℝ) - (a : ℝ))⌉₊ ≤ b →
          ∀ j ∈ F,
            ENNReal.ofReal (((gridScale δ Mgrid a : ℝ) / (gridScale δ Mgrid c : ℝ)) ^ ζ')
              ≤ (C : ENNReal) * totalLoss C K cL δ *
                  Kakeya.maxDensity
                    (𝒢.toUniformTubeSet.nodesIn c
                      (((𝒢.cover.tube a j).rescale
                          (8 * gridScale δ Mgrid a)).toConvexSpaceBody))
                    (fun j' => (𝒢.cover.tube c j').toConvexSpaceBody)) := by
  obtain ⟨C, K, cL, hC1, hCbC, h⟩ := alternativeTwoKT_of_terminal_block_core.{u, _} (E := E) hn
    Cv (uniformTubeSetCuOf (E := E) Cv) Cb hCv (le_trans hCv (le_max_left _ _)) hCb
  refine ⟨C, K, cL, hC1, hCbC, ?_⟩
  intro N hN eps heps Mgrid hM16 hNM iota delta hd0 hd1 hdM hMss t T hs hball GG zeta zeta' hz0
    hz'0 S hS0 hSM hblocks a b haS hbS hab hadj hlong hbM hnotpass
  exact h N hN heps Mgrid hM16 hNM hd0 hd1 hdM hMss t T hs hball GG.toGridUniformCore
    GG.toUniformTubeSet rfl zeta zeta' hz0 hz'0 S hS0 hSM hblocks a b haS hbS hab hadj hlong
    hbM hnotpass

section Pointwise

variable {ι : Type*}

open scoped Classical in
/-- **A dilated node is covered by boundedly many class images of its own level.**  The level-`c`
nodes inside the `8σ_a`-dilate of a level-`a` node are covered by the level-`c` images of boundedly
many level-`a` classes, the number being dimensional and independent of the family.  The two side
conditions are those of `Kakeya.MultiScaleFac.card_image_nodeAncestor_le`, which supplies it. -/
theorem exists_coarseNeighbours (Cu : NNReal) (hCu : 1 ≤ Cu) :
    ∃ Kn : ℕ, 1 ≤ Kn ∧
      ∀ {ι : Type u} {δ : NNReal}, 0 < δ → δ ≤ 1 →
      ∀ {M : ℕ} {s : Finset ι} {T : ι → Tube δ E} (𝒰 : UniformTubeSet s T M Cu),
      s.Nonempty →
      ∀ {a c : ℕ}, a ≤ c → c ≤ M → 2 * δ ≤ gridScale δ M a →
      ∀ j ∈ 𝒰.cover.indexSet a,
        ∃ P ⊆ 𝒰.cover.indexSet a, P.card ≤ Kn ∧
          𝒰.nodesIn c ((𝒰.cover.tube a j).rescale
              (8 * gridScale δ M a)).toConvexSpaceBody
            ⊆ P.biUnion (fun p =>
                (coverClass s (𝒰.cover.assign a) p).image (𝒰.cover.assign c)) := by
  let c0 : ℝ := 2 * (25 : ℝ) ^ (2 * Module.finrank ℝ E) * (32 : ℝ) ^ (2 * Module.finrank ℝ E) *
      (Cu : ℝ)
  let Kn : ℕ := ⌈c0⌉₊
  have hKn : 1 ≤ Kn := by
    have hCu0 : (0 : ℝ) < (Cu : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le zero_lt_one hCu)
    have hpos : (0 : ℝ) < c0 := by
      dsimp [c0]
      positivity
    exact (Nat.one_le_ceil_iff.mpr hpos)
  refine ⟨Kn, hKn, ?_⟩
  intro ι δ hδ hδ1 M s T 𝒰 hs a c hac hcM h2d j hj
  classical
  let dil : ConvexSpaceBody E :=
    ((𝒰.cover.tube a j).rescale (8 * gridScale δ M a)).toConvexSpaceBody
  have hcard :
      (((𝒰.nodesIn c dil).image (𝒰.nodeAncestor c a)).card : ℝ) ≤ c0 := by
    exact card_image_nodeAncestor_le hδ 𝒰 (a := a) (b := c) (hac.trans hcM) hcM hs h2d
      (r := 8 * gridScale δ M a) le_rfl
      ((𝒰.cover.tube a j).rescale (8 * gridScale δ M a))
  refine ⟨(𝒰.nodesIn c dil).image (𝒰.nodeAncestor c a), ?_, ?_, ?_⟩
  · intro j' hj'
    rw [Finset.mem_image] at hj'
    obtain ⟨w, hwP, hxeq⟩ := hj'
    rw [← hxeq]
    exact 𝒰.nodeAncestor_mem (b := c) (a := a) (hac.trans hcM) hcM hs
      ((𝒰.mem_nodesIn_iff c dil w).mp hwP).1
  · have hlc : (((𝒰.nodesIn c dil).image (𝒰.nodeAncestor c a)).card : ℝ) ≤ (Kn : ℝ) :=
      hcard.trans (Nat.le_ceil c0)
    exact Nat.cast_le.mp hlc
  · intro w hw
    rw [Finset.mem_biUnion]
    refine ⟨𝒰.nodeAncestor c a w, Finset.mem_image_of_mem _ hw, ?_⟩
    rw [Finset.mem_image]
    have hidx : w ∈ 𝒰.cover.indexSet c :=
      ((𝒰.mem_nodesIn_iff c dil w).mp hw).1
    obtain ⟨i, hi, hwi, hwa⟩ :=
      𝒰.exists_nodeAncestor_witness (b := c) (a := a) hcM hs hidx
    refine ⟨i, ?_, hwi⟩
    rw [coverClass, Finset.mem_filter]
    exact ⟨hi, hwa.symm⟩

omit [Nontrivial E] in
open scoped Classical in
/-- **From the anchored lower bound to a lower bound at one class image.**
Covering the `8σ_a`-dilate of a level-`a` node by boundedly many level-`a` class images and using
subadditivity of `Kakeya.maxDensity` moves the lower bound of
`Kakeya.MultiScaleFac.alternativeTwoKT_of_terminal_block` onto one of them, at the cost of their
number.  Only *one* witness `p` is produced, and only for the grid index `c` at hand. -/
theorem exists_undilated_of_dilated {δ : NNReal} (_hδ : 0 < δ) (_hδ1 : δ ≤ 1)
    {s : Finset ι} {T : ι → Tube δ E} {Cu C : NNReal} {Kn : ℕ} (_hKn : 1 ≤ Kn)
    (𝒰 : UniformTubeSet s T (ssfGridLen δ) Cu) {a c : ℕ} (_hac : a ≤ c)
    (_hcM : c ≤ ssfGridLen δ) {ζ' : ℝ} {j : ι} (hj : j ∈ 𝒰.cover.indexSet a)
    (hP : ∃ P ⊆ 𝒰.cover.indexSet a, P.card ≤ Kn ∧
      𝒰.nodesIn c ((𝒰.cover.tube a j).rescale
          (8 * gridScale δ (ssfGridLen δ) a)).toConvexSpaceBody
        ⊆ P.biUnion (fun p =>
            (coverClass s (𝒰.cover.assign a) p).image (𝒰.cover.assign c)))
    (hdil : ENNReal.ofReal (((gridScale δ (ssfGridLen δ) a : ℝ)
        / (gridScale δ (ssfGridLen δ) c : ℝ)) ^ ζ')
      ≤ (C : ENNReal) *
          Kakeya.maxDensity
            (𝒰.nodesIn c ((𝒰.cover.tube a j).rescale
                (8 * gridScale δ (ssfGridLen δ) a)).toConvexSpaceBody)
            (fun j' => (𝒰.cover.tube c j').toConvexSpaceBody)) :
    ∃ p ∈ 𝒰.cover.indexSet a,
      ENNReal.ofReal (((gridScale δ (ssfGridLen δ) a : ℝ)
          / (gridScale δ (ssfGridLen δ) c : ℝ)) ^ ζ')
        ≤ (Kn : ENNReal) * (C : ENNReal) *
            Kakeya.maxDensity
              ((coverClass s (𝒰.cover.assign a) p).image (𝒰.cover.assign c))
              (fun j' => (𝒰.cover.tube c j').toConvexSpaceBody) := by
  classical
  let X : ENNReal := ENNReal.ofReal (((gridScale δ (ssfGridLen δ) a : ℝ)
      / (gridScale δ (ssfGridLen δ) c : ℝ)) ^ ζ')
  let Dil : Finset ι := 𝒰.nodesIn c ((𝒰.cover.tube a j).rescale
      (8 * gridScale δ (ssfGridLen δ) a)).toConvexSpaceBody
  let W : ι → ConvexSpaceBody E := fun j' => (𝒰.cover.tube c j').toConvexSpaceBody
  let G : ι → Finset ι := fun p =>
      (coverClass s (𝒰.cover.assign a) p).image (𝒰.cover.assign c)
  obtain ⟨P, hPsub, hPcard, hcov⟩ := hP
  have hdil' : X ≤ (C : ENNReal) * Kakeya.maxDensity Dil W := by
    simpa [X, Dil, W] using hdil
  by_cases hPe : P = ∅
  · have hDil : Dil = ∅ := Finset.subset_empty.mp (by simpa [hPe] using hcov)
    exact ⟨j, hj, le_trans (hdil'.trans (by simp [hDil])) bot_le⟩
  · obtain ⟨p, hpP, hpmax⟩ := Finset.exists_max_image (s := P)
      (f := fun q => Kakeya.maxDensity (G q) W) (Finset.nonempty_iff_ne_empty.mpr hPe)
    have hcard_le : (P.card : ENNReal) ≤ (Kn : ENNReal) := by exact_mod_cast hPcard
    have hsum : Kakeya.maxDensity Dil W ≤ (Kn : ENNReal) * Kakeya.maxDensity (G p) W := by
      refine le_trans (by simpa [G] using (maxDensity_le_sum_of_subset_biUnion (W := W) hcov)) ?_
      refine le_trans (by simpa [nsmul_eq_mul] using (Finset.sum_le_card_nsmul P
        (fun q => Kakeya.maxDensity (G q) W) (Kakeya.maxDensity (G p) W) hpmax)) ?_
      gcongr
    refine ⟨p, hPsub hpP, le_trans hdil' ?_⟩
    calc (C : ENNReal) * Kakeya.maxDensity Dil W
        ≤ (C : ENNReal) * ((Kn : ENNReal) * Kakeya.maxDensity (G p) W) := by gcongr
      _ = (Kn : ENNReal) * (C : ENNReal) * Kakeya.maxDensity (G p) W := by ring

omit [Nontrivial E] in
open scoped Classical in
/-- **One witness plus the band gives every node.**  The step that removes the majority set: the
paired homogenization band brackets the level-`c` image of a level-`a` class between `Φ` and `C' Φ`
uniformly in the node, so a lower bound at a single node gives one at every node of the level, read
on `Tube.UniformTubeSet.nodesUnder`, which contains the class image. -/
theorem le_maxDensity_nodesUnder_of_band {δ : NNReal} {s : Finset ι} {T : ι → Tube δ E}
    {Cu : NNReal} (𝒰 : UniformTubeSet s T (ssfGridLen δ) Cu) {a c : ℕ} (hac : a ≤ c)
    (hcM : c ≤ ssfGridLen δ) {X D Φ : ENNReal} {C' : NNReal}
    (hband : ∀ j ∈ 𝒰.cover.indexSet a,
      Φ ≤ Kakeya.maxDensity ((coverClass s (𝒰.cover.assign a) j).image (𝒰.cover.assign c))
            (fun j' => (𝒰.cover.tube c j').toConvexSpaceBody) ∧
        Kakeya.maxDensity ((coverClass s (𝒰.cover.assign a) j).image (𝒰.cover.assign c))
            (fun j' => (𝒰.cover.tube c j').toConvexSpaceBody) ≤ (C' : ENNReal) * Φ)
    (hwit : ∃ p ∈ 𝒰.cover.indexSet a,
      X ≤ D * Kakeya.maxDensity
            ((coverClass s (𝒰.cover.assign a) p).image (𝒰.cover.assign c))
            (fun j' => (𝒰.cover.tube c j').toConvexSpaceBody)) :
    ∀ j ∈ 𝒰.cover.indexSet a,
      X ≤ D * (C' : ENNReal) * Kakeya.maxDensity (𝒰.nodesUnder c a j)
            (fun j' => (𝒰.cover.tube c j').toConvexSpaceBody) := by
  obtain ⟨p, hp, hX⟩ := hwit
  have h1 : X ≤ D * (C' : ENNReal) * Φ := by
    exact hX.trans (by
      rw [mul_assoc]
      exact mul_le_mul_right (hband p hp).2 D)
  intro j hj
  have hsub : (coverClass s (𝒰.cover.assign a) j).image (𝒰.cover.assign c) ⊆
      𝒰.nodesUnder c a j := by
    exact (Finset.image_subset_iff).mpr (fun i hi => assign_mem_nodesUnder 𝒰 hac hcM hi)
  have hmono : Kakeya.maxDensity ((coverClass s (𝒰.cover.assign a) j).image
        (𝒰.cover.assign c)) (fun j' => (𝒰.cover.tube c j').toConvexSpaceBody)
      ≤ Kakeya.maxDensity (𝒰.nodesUnder c a j)
          (fun j' => (𝒰.cover.tube c j').toConvexSpaceBody) := by
    exact Kakeya.maxDensity_mono (fun j' => (𝒰.cover.tube c j').toConvexSpaceBody) hsub
  exact h1.trans (mul_le_mul_right ((hband j hj).1.trans hmono) (D * (C' : ENNReal)))

end Pointwise

/-- **One constant for all the gaps.**  The Katz-Tao twin of the private helper of half (A). -/
theorem KT.exists_common_const (B₀ B₁ B₂ B₃ Cq : NNReal) (hCq : 1 ≤ Cq) :
    ∃ C : NNReal, 1 ≤ C ∧ B₀ ≤ C ∧ B₁ ≤ C ∧ B₂ ≤ C ∧ B₃ ≤ C ∧ Cq ≤ C :=
  ⟨max B₀ (max B₁ (max B₂ (max B₃ Cq))), by simp [hCq]⟩

/-- **One polylogarithmic degree for all the gaps.** -/
theorem KT.exists_common_deg (K₀ K₁ K₂ K₃ K₄ : ℕ) :
    ∃ K : ℕ, K₀ ≤ K ∧ K₁ ≤ K ∧ K₂ ≤ K ∧ K₃ ≤ K ∧ K₄ ≤ K :=
  ⟨K₀ + K₁ + K₂ + K₃ + K₄, by omega⟩

/-- **One threshold for all the gaps.** -/
theorem KT.exists_common_threshold {δ₁ δ₂ δ₃ : NNReal} (h₁ : 0 < δ₁) (h₁' : δ₁ ≤ 1)
    (h₂ : 0 < δ₂) (h₃ : 0 < δ₃) :
    ∃ δ₀ : NNReal, 0 < δ₀ ∧ δ₀ ≤ 1 ∧ δ₀ ≤ δ₁ ∧ δ₀ ≤ δ₂ ∧ δ₀ ≤ δ₃ :=
  ⟨min δ₁ (min δ₂ δ₃), lt_min h₁ (lt_min h₂ h₃), by simp [h₁']⟩


/-! ### The arithmetic of the displayed losses -/

/-- **The exponent chain is bounded by `ε` one step past the stopping index.**  The Katz-Tao twin of
the private helper of half (A): the gap hypothesis and nonnegativity make `η` monotone up to `N`, so
`η (m+1) ≤ η N ≤ ε` for every `m < N`. -/
theorem KT.eta_succ_le_eps {N : ℕ} (hN : 0 < N) {ε : ℝ} (hε : ε = 1 / Real.sqrt (N : ℝ))
    (η : ℕ → ℝ) (hη0 : 0 ≤ η 0) (hgap : ∀ k < N, η k ≤ ε * η (k + 1)) (hηN : η N ≤ ε)
    {m : ℕ} (hm : m < N) :
    η (m + 1) ≤ ε := by
  have hnonneg : ∀ k ≤ N, 0 ≤ η k := eta_nonneg_of_gap N hN hε η hη0 hgap
  have hε1 : ε ≤ 1 := by
    rw [hε, div_le_one (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hN))]
    exact Real.one_le_sqrt.mpr (by exact_mod_cast hN)
  have hstep : ∀ k < N, η k ≤ η (k + 1) := fun k hk =>
    (hgap k hk).trans (mul_le_of_le_one_left (hnonneg (k + 1) hk) hε1)
  have hadd : ∀ d : ℕ, (m + 1) + d ≤ N → η (m + 1) ≤ η ((m + 1) + d) := by
    intro d
    induction d with
    | zero => exact fun _ => le_rfl
    | succ d ih => exact fun hdN => (ih (by omega)).trans (hstep _ (by omega))
  have hto := hadd (N - (m + 1)) (by omega)
  rw [show (m + 1) + (N - (m + 1)) = N by omega] at hto
  exact hto.trans hηN

/-- **A bare constant and two displayed losses make one displayed loss.**  The product of two losses
is the loss at the product of the bases and the sum of the exponents
(`Kakeya.MultiScaleFac.gridLoss_mul`, `Kakeya.MultiScaleFac.A.scaleGapLoss_add`), raised to a common
one by `Kakeya.MultiScaleFac.loss_raise`. -/
theorem KT.prod_le {δ : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1) {A B₁ B₂ C : NNReal}
    (hA : 1 ≤ A) (hB₁ : 1 ≤ B₁) (hB₂ : 1 ≤ B₂) {K₁ K₂ K c₁ c₂ c : ℕ}
    (hC : A * B₁ * B₂ ≤ C) (hK : K₁ + K₂ ≤ K) (hc : c₁ + c₂ ≤ c) {X Y : ENNReal}
    (h : X ≤ (A : ENNReal) * ((B₁ : ENNReal) * totalLoss B₁ K₁ c₁ δ) *
        ((B₂ : ENNReal) * totalLoss B₂ K₂ c₂ δ) * Y) :
    X ≤ (C : ENNReal) * totalLoss C K c δ * Y := by
  set P : NNReal := A * B₁ * B₂ with hPdef
  have hP1 : 1 ≤ P := one_le_mul (one_le_mul hA hB₁) hB₂
  have hPC : P ≤ C := by simpa [P] using hC
  have hBB1 : 1 ≤ B₁ * B₂ := one_le_mul hB₁ hB₂
  have hBBP : B₁ * B₂ ≤ P := by
    calc
      B₁ * B₂ ≤ B₁ * B₂ * A := by simpa using mul_le_mul_of_nonneg_left hA zero_le
      _ = P := by rw [hPdef]; ring
  have hPcoe : (P : ENNReal) = (A : ENNReal) * (B₁ : ENNReal) * (B₂ : ENNReal) := by
    rw [hPdef, ENNReal.coe_mul, ENNReal.coe_mul]
  refine le_trans h (mul_le_mul_left ?_ Y)
  calc
    (A : ENNReal) * ((B₁ : ENNReal) * totalLoss B₁ K₁ c₁ δ) *
          ((B₂ : ENNReal) * totalLoss B₂ K₂ c₂ δ)
        = (P : ENNReal) * (totalLoss B₁ K₁ c₁ δ * totalLoss B₂ K₂ c₂ δ) := by
          rw [hPcoe]; ring
    _ = (P : ENNReal) * totalLoss (B₁ * B₂) (K₁ + K₂) (c₁ + c₂) δ := by
        rw [totalLoss_mul hB₁ hB₂ K₁ K₂ c₁ c₂ hδ hδ1]
    _ ≤ (P : ENNReal) * totalLoss P (K₁ + K₂) (c₁ + c₂) δ :=
        mul_le_mul_right (totalLoss_mono hBB1 hBBP le_rfl le_rfl hδ hδ1) (P : ENNReal)
    _ ≤ (C : ENNReal) * totalLoss C K c δ := loss_raise hP1 hPC hK hc hδ hδ1

/-- **The cardinality clause, with the loss raised.**  The stopping time counts in `ℝ≥0∞` against
its own displayed loss; the amended statement displays the common one, and the loss may be raised on
the way. -/
theorem KT.card_le {ι : Type*} {δ : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1) {B C : NNReal}
    (hB : 1 ≤ B) (hBC : B ≤ C) {K K' c c' : ℕ} (hK : K ≤ K') (hc : c ≤ c')
    {s s' : Finset ι} (h : (s.card : ENNReal) ≤ totalLoss B K c δ * (s'.card : ENNReal)) :
    (s.card : ENNReal) ≤ totalLoss C K' c' δ * (s'.card : ENNReal) :=
  h.trans (mul_le_mul_left (totalLoss_mono hB hBC hK hc hδ hδ1) _)

/-- **A displayed loss is the coercion of a single constant.**  Used to feed a bound whose
coefficient is a displayed loss to a lemma whose coefficient slot is an `NNReal`; the `δ`-dependence
of that `NNReal` is harmless because it is never placed in the base of a
`Kakeya.MultiScaleFac.gridLoss`.  The finiteness side condition is
`Kakeya.MultiScaleFac.totalLoss_ne_top` at every use. -/
theorem KT.coe_mul_ofReal (C : NNReal) {x : ENNReal} (hx : x ≠ ⊤) :
    (C : ENNReal) * x = ((C * x.toNNReal : NNReal) : ENNReal) := by
  rw [ENNReal.coe_mul, ENNReal.coe_toNNReal hx]

/-! ### From one dilated witness to every node of the level -/

section Pointwise

variable {ι : Type*}

omit [Nontrivial E] in
open scoped Classical in
/-- **The two steps that remove the majority set, in one.**
`Kakeya.MultiScaleFac.exists_undilated_of_dilated` moves the lower bound of the terminal alternative
onto a single level-`a` class image, and `Kakeya.MultiScaleFac.le_maxDensity_nodesUnder_of_band`
spreads that witness over the whole level by the two-sided homogenization band; the composite is a
lower bound at *every* node of the coarse level, with no majority set left. -/
theorem KT.gridLower_of_band {δ : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {s : Finset ι} {T : ι → Tube δ E} {Cu : NNReal} (𝒰 : UniformTubeSet s T (ssfGridLen δ) Cu)
    {Kn : ℕ} (hKn : 1 ≤ Kn) {C' Dn : NNReal} {Φ₀ : ENNReal} {ζ' : ℝ} {a c : ℕ}
    (hac : a ≤ c) (hcM : c ≤ ssfGridLen δ)
    (hnb : ∀ j ∈ 𝒰.cover.indexSet a,
      ∃ P ⊆ 𝒰.cover.indexSet a, P.card ≤ Kn ∧
        𝒰.nodesIn c ((𝒰.cover.tube a j).rescale
            (8 * gridScale δ (ssfGridLen δ) a)).toConvexSpaceBody
          ⊆ P.biUnion (fun p =>
              (coverClass s (𝒰.cover.assign a) p).image (𝒰.cover.assign c)))
    (hband : ∀ j ∈ 𝒰.cover.indexSet a,
      Φ₀ ≤ Kakeya.maxDensity ((coverClass s (𝒰.cover.assign a) j).image (𝒰.cover.assign c))
            (fun j' => (𝒰.cover.tube c j').toConvexSpaceBody) ∧
        Kakeya.maxDensity ((coverClass s (𝒰.cover.assign a) j).image (𝒰.cover.assign c))
            (fun j' => (𝒰.cover.tube c j').toConvexSpaceBody) ≤ (C' : ENNReal) * Φ₀)
    {j₀ : ι} (hj₀ : j₀ ∈ 𝒰.cover.indexSet a)
    (hlow : ENNReal.ofReal (((gridScale δ (ssfGridLen δ) a : ℝ)
          / (gridScale δ (ssfGridLen δ) c : ℝ)) ^ ζ')
        ≤ (Dn : ENNReal) * Kakeya.maxDensity
            (𝒰.nodesIn c ((𝒰.cover.tube a j₀).rescale
                (8 * gridScale δ (ssfGridLen δ) a)).toConvexSpaceBody)
            (fun j' => (𝒰.cover.tube c j').toConvexSpaceBody)) :
    ∀ j ∈ 𝒰.cover.indexSet a,
      ENNReal.ofReal (((gridScale δ (ssfGridLen δ) a : ℝ)
          / (gridScale δ (ssfGridLen δ) c : ℝ)) ^ ζ')
        ≤ (Kn : ENNReal) * (Dn : ENNReal) * (C' : ENNReal) *
            Kakeya.maxDensity (𝒰.nodesUnder c a j)
              (fun j' => (𝒰.cover.tube c j').toConvexSpaceBody) := by
  have hwit := exists_undilated_of_dilated hδ hδ1 hKn 𝒰 hac hcM hj₀ (hnb j₀ hj₀) hlow
  exact le_maxDensity_nodesUnder_of_band 𝒰 hac hcM hband hwit

/-- **The third bullet with the hypothesis coefficient left free.**  The constant of the hypothesis
is an arbitrary `ENNReal` factor `D`, which rides through the two roundings untouched and reappears
in the conclusion; the roundings themselves — a margin index comparable to `ρ`, and the transport
from the level-`c` nodes to the level-`b` nodes — are charged to `C · totalLoss C K cL δ`. -/
theorem KT.bulletThreeGen {δ : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {s : Finset ι} {T : ι → Tube δ E} {Cu C : NNReal} (hC : 1 ≤ C)
    (hCcmp : KT.gapDensityConstCmp (E := E) ≤ C) (K cL : ℕ)
    (hcL : 2 + 4 * Module.finrank ℝ E ≤ cL)
    (𝒰 : UniformTubeSet s T (ssfGridLen δ) Cu) (hs : s.Nonempty)
    {ε ζ' : ℝ} {a b m' : ℕ} (_hab : a < b) (hbM : b ≤ ssfGridLen δ)
    (hζ'0 : 0 ≤ ζ') (hζ'1 : ζ' ≤ 1)
    (hmlo : ε * ((b : ℝ) - (a : ℝ)) ≤ (m' : ℝ))
    (hmhi : (m' : ℝ) ≤ ε * ((b : ℝ) - (a : ℝ)) + 1) (hroom : a + 2 * m' ≤ b)
    (D : ENNReal)
    (hgrid : ∀ c : ℕ, a + m' ≤ c → c + m' ≤ b → ∀ p ∈ 𝒰.cover.indexSet a,
      ENNReal.ofReal (((gridScale δ (ssfGridLen δ) a : ℝ)
          / (gridScale δ (ssfGridLen δ) c : ℝ)) ^ ζ')
        ≤ D * Kakeya.maxDensity (𝒰.nodesUnder c a p)
            (fun j' => (𝒰.cover.tube c j').toConvexSpaceBody)) :
    ∀ ρ : NNReal,
      (gridScale δ (ssfGridLen δ) b : ℝ)
          * ((gridScale δ (ssfGridLen δ) a : ℝ)
              / (gridScale δ (ssfGridLen δ) b : ℝ)) ^ ε ≤ (ρ : ℝ) →
      (ρ : ℝ) ≤ (gridScale δ (ssfGridLen δ) a : ℝ)
          * ((gridScale δ (ssfGridLen δ) b : ℝ)
              / (gridScale δ (ssfGridLen δ) a : ℝ)) ^ ε →
      ∀ j ∈ 𝒰.cover.indexSet a,
        ENNReal.ofReal (((gridScale δ (ssfGridLen δ) a : ℝ) / (ρ : ℝ)) ^ ζ')
          ≤ D * ((C : ENNReal) * totalLoss C K cL δ) *
              Kakeya.maxDensity (𝒰.nodesUnder b a j)
                (fun j' => ((𝒰.cover.tube b j').rescale ρ).toConvexSpaceBody) := by
  intro ρ hρlo hρhi j hj
  obtain ⟨c, hc1, hc2, hclo, hchi⟩ :=
    exists_marginIndex_of_window hδ hδ1 hmlo hmhi hroom hρlo hρhi
  have hσa : (0 : ℝ) < (gridScale δ (ssfGridLen δ) a : ℝ) := by
    rw [gridScale, NNReal.coe_rpow]
    exact Real.rpow_pos_of_pos (by exact_mod_cast hδ) _
  have hσc : (0 : ℝ) < (gridScale δ (ssfGridLen δ) c : ℝ) := by
    rw [gridScale, NNReal.coe_rpow]
    exact Real.rpow_pos_of_pos (by exact_mod_cast hδ) _
  have hσb : (0 : ℝ) < (gridScale δ (ssfGridLen δ) b : ℝ) := by
    rw [gridScale, NNReal.coe_rpow]
    exact Real.rpow_pos_of_pos (by exact_mod_cast hδ) _
  have hρpos : (0 : ℝ) < (ρ : ℝ) := by
    exact lt_of_lt_of_le
      (mul_pos hσb (Real.rpow_pos_of_pos (div_pos hσa hσb) ε)) hρlo
  have hρ0 : 0 < ρ := by
    exact_mod_cast hρpos
  have hG : (1 : ℝ) ≤ scaleGapLoss 2 δ := one_le_scaleGapLoss 2 hδ hδ1
  have hcb : c ≤ b := by
    omega
  have hexp :
      ENNReal.ofReal (((gridScale δ (ssfGridLen δ) a : ℝ) / (ρ : ℝ)) ^ ζ') ≤
        ENNReal.ofReal (scaleGapLoss 2 δ) *
          ENNReal.ofReal (((gridScale δ (ssfGridLen δ) a : ℝ) /
            (gridScale δ (ssfGridLen δ) c : ℝ)) ^ ζ') :=
    ofReal_rpow_div_le_mul_ofReal_rpow_div hδ hδ1 (le_of_lt hσa) hρpos hσc
      hζ'0 hζ'1 hclo
  have htrans :
      Kakeya.maxDensity (𝒰.nodesUnder c a j)
          (fun j' => (𝒰.cover.tube c j').toConvexSpaceBody) ≤
        (KT.gapDensityConstCmp (E := E) : ENNReal) *
          ENNReal.ofReal ((scaleGapLoss 2 δ) ^ (2 * Module.finrank ℝ E)) *
          Kakeya.maxDensity (𝒰.nodesUnder b a j)
            (fun j' => ((𝒰.cover.tube b j').rescale ρ).toConvexSpaceBody) := by
    simpa [UniformTubeSet.nodesUnder_eq_nodesIn] using
      (maxDensity_nodesIn_le_mul_maxDensity_nodesIn_rescale_comparable hδ1 𝒰 hs hcb
        hbM hρ0 hG hclo hchi ((𝒰.cover.tube a j).toConvexSpaceBody))
  have hAbs :
      ENNReal.ofReal (scaleGapLoss 2 δ) * (KT.gapDensityConstCmp (E := E) : ENNReal) *
        ENNReal.ofReal ((scaleGapLoss 2 δ) ^ (2 * Module.finrank ℝ E)) ≤
        (C : ENNReal) * totalLoss C K cL δ := by
    have hsgnn : ∀ c : ℕ, (0 : ℝ) ≤ scaleGapLoss c δ := fun c =>
      le_trans zero_le_one (one_le_scaleGapLoss c hδ hδ1)
    have hgnn : (0 : ℝ) ≤ gridLoss C K δ :=
      le_trans zero_le_one (one_le_gridLoss C hC K hδ1)
    have hCmpE : (KT.gapDensityConstCmp (E := E) : ENNReal) ≤ (C : ENNReal) := by
      exact_mod_cast hCcmp
    have hgridge1 : (1 : ENNReal) ≤ ENNReal.ofReal (gridLoss C K δ) := by
      simpa using ENNReal.ofReal_le_ofReal (one_le_gridLoss C hC K hδ1)
    have hpow : ENNReal.ofReal ((scaleGapLoss 2 δ) ^ (2 * Module.finrank ℝ E)) =
        ENNReal.ofReal (scaleGapLoss (2 * (2 * Module.finrank ℝ E)) δ) := by
      rw [Kakeya.MultiScaleFac.A.scaleGapLoss_pow hδ 2 (2 * Module.finrank ℝ E)]
    have hL : ENNReal.ofReal (scaleGapLoss 2 δ) * (C : ENNReal) ≤
        ENNReal.ofReal (scaleGapLoss 2 δ) * (C : ENNReal) *
          ENNReal.ofReal (gridLoss C K δ) := by
      exact
        (le_mul_of_one_le_right
          (by positivity : (0 : ENNReal) ≤ ENNReal.ofReal (scaleGapLoss 2 δ) * (C : ENNReal))
          hgridge1 :
          ENNReal.ofReal (scaleGapLoss 2 δ) * (C : ENNReal) ≤
            ENNReal.ofReal (scaleGapLoss 2 δ) * (C : ENNReal) *
              ENNReal.ofReal (gridLoss C K δ))
    calc
      ENNReal.ofReal (scaleGapLoss 2 δ) * (KT.gapDensityConstCmp (E := E) : ENNReal) *
          ENNReal.ofReal ((scaleGapLoss 2 δ) ^ (2 * Module.finrank ℝ E))
        ≤ ENNReal.ofReal (scaleGapLoss 2 δ) * (C : ENNReal) *
            ENNReal.ofReal ((scaleGapLoss 2 δ) ^ (2 * Module.finrank ℝ E)) := by
          gcongr
      _ ≤ ENNReal.ofReal (scaleGapLoss 2 δ) * (C : ENNReal) *
            ENNReal.ofReal (gridLoss C K δ) *
            ENNReal.ofReal ((scaleGapLoss 2 δ) ^ (2 * Module.finrank ℝ E)) := by
          exact mul_le_mul hL le_rfl (by positivity) (by positivity)
      _ = (C : ENNReal) * (ENNReal.ofReal (scaleGapLoss 2 δ) *
          ENNReal.ofReal (gridLoss C K δ) *
          ENNReal.ofReal ((scaleGapLoss 2 δ) ^ (2 * Module.finrank ℝ E))) := by
          simp [mul_assoc, mul_comm, mul_left_comm]
      _ = (C : ENNReal) * ENNReal.ofReal ((scaleGapLoss 2 δ * gridLoss C K δ) *
          scaleGapLoss (2 * (2 * Module.finrank ℝ E)) δ) := by
          rw [hpow]
          rw [← ENNReal.ofReal_mul' hgnn]
          rw [← ENNReal.ofReal_mul' (hsgnn (2 * (2 * Module.finrank ℝ E)))]
      _ = (C : ENNReal) * ENNReal.ofReal (gridLoss C K δ *
          (scaleGapLoss 2 δ * scaleGapLoss (2 * (2 * Module.finrank ℝ E)) δ)) := by
          congr 1
          congr 1
          ring
      _ = (C : ENNReal) * ENNReal.ofReal (gridLoss C K δ *
          scaleGapLoss (2 + 2 * (2 * Module.finrank ℝ E)) δ) := by
          congr 1
          congr 1
          rw [Kakeya.MultiScaleFac.A.scaleGapLoss_add hδ 2 (2 * (2 * Module.finrank ℝ E))]
      _ ≤ (C : ENNReal) * ENNReal.ofReal (gridLoss C K δ * scaleGapLoss cL δ) := by
          gcongr
          exact Kakeya.MultiScaleFac.A.scaleGapLoss_mono hδ hδ1 (by omega)
      _ = (C : ENNReal) * totalLoss C K cL δ := by
          rw [totalLoss_eq_ofReal]
  calc
    ENNReal.ofReal (((gridScale δ (ssfGridLen δ) a : ℝ) / (ρ : ℝ)) ^ ζ') ≤
        ENNReal.ofReal (scaleGapLoss 2 δ) *
          ENNReal.ofReal (((gridScale δ (ssfGridLen δ) a : ℝ) /
            (gridScale δ (ssfGridLen δ) c : ℝ)) ^ ζ') := hexp
    _ ≤ ENNReal.ofReal (scaleGapLoss 2 δ) *
          (D * Kakeya.maxDensity (𝒰.nodesUnder c a j)
            (fun j' => (𝒰.cover.tube c j').toConvexSpaceBody)) := by
          gcongr
          exact hgrid c hc1 hc2 j hj
    _ ≤ ENNReal.ofReal (scaleGapLoss 2 δ) * (D *
          ((KT.gapDensityConstCmp (E := E) : ENNReal) *
            ENNReal.ofReal ((scaleGapLoss 2 δ) ^ (2 * Module.finrank ℝ E)) *
            Kakeya.maxDensity (𝒰.nodesUnder b a j)
              (fun j' => ((𝒰.cover.tube b j').rescale ρ).toConvexSpaceBody))) := by
          gcongr
    _ = (D * (ENNReal.ofReal (scaleGapLoss 2 δ) *
          (KT.gapDensityConstCmp (E := E) : ENNReal) *
          ENNReal.ofReal ((scaleGapLoss 2 δ) ^ (2 * Module.finrank ℝ E)))) *
        Kakeya.maxDensity (𝒰.nodesUnder b a j)
          (fun j' => ((𝒰.cover.tube b j').rescale ρ).toConvexSpaceBody) := by
          simp [mul_assoc, mul_comm, mul_left_comm]
    _ ≤ D * ((C : ENNReal) * totalLoss C K cL δ) *
        Kakeya.maxDensity (𝒰.nodesUnder b a j)
          (fun j' => ((𝒰.cover.tube b j').rescale ρ).toConvexSpaceBody) := by
          gcongr

end Pointwise

omit [Nontrivial E] in
open scoped Classical in
/-- **The hypothesis of the window rounding, from the terminal alternative.**  The passage from what
`Kakeya.MultiScaleFac.alternativeTwoKT_of_terminal_block` returns — a lower bound on the majority
set `F` and on the `8σ_a`-dilate of a node — to what `Kakeya.MultiScaleFac.KT.bulletThreeGen`
consumes: the same bound at every node of the coarse level and on its undilated fine nodes. -/
theorem KT.hgrid_of_alternativeTwo {ι : Type*} {δ : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {s : Finset ι} {T : ι → Tube δ E} {Cu : NNReal} (𝒰 : UniformTubeSet s T (ssfGridLen δ) Cu)
    {Kn : ℕ} (hKn : 1 ≤ Kn) {a b m' : ℕ} (_hab : a < b) (hbM : b ≤ ssfGridLen δ)
    (hnb : ∀ c : ℕ, a ≤ c → c ≤ ssfGridLen δ → ∀ j ∈ 𝒰.cover.indexSet a,
      ∃ P ⊆ 𝒰.cover.indexSet a, P.card ≤ Kn ∧
        𝒰.nodesIn c ((𝒰.cover.tube a j).rescale
            (8 * gridScale δ (ssfGridLen δ) a)).toConvexSpaceBody
          ⊆ P.biUnion (fun p =>
              (coverClass s (𝒰.cover.assign a) p).image (𝒰.cover.assign c)))
    {C₁ B₂ : NNReal} (_hB₂ : 1 ≤ B₂) {K₂ c₂ : ℕ} {Φ : ℕ → ℕ → ENNReal}
    (hband : ∀ c : ℕ, c ≤ ssfGridLen δ → ∀ j ∈ 𝒰.cover.indexSet a,
      Φ a c ≤ Kakeya.maxDensity ((coverClass s (𝒰.cover.assign a) j).image (𝒰.cover.assign c))
            (fun j' => (𝒰.cover.tube c j').toConvexSpaceBody) ∧
        Kakeya.maxDensity ((coverClass s (𝒰.cover.assign a) j).image (𝒰.cover.assign c))
            (fun j' => (𝒰.cover.tube c j').toConvexSpaceBody) ≤ (C₁ : ENNReal) * Φ a c)
    {F : Finset ι} (hFsub : F ⊆ 𝒰.cover.indexSet a) (hFne : F.Nonempty) {ζ' : ℝ}
    (hlow : ∀ c : ℕ, a + m' ≤ c → c + m' ≤ b → ∀ j ∈ F,
      ENNReal.ofReal (((gridScale δ (ssfGridLen δ) a : ℝ)
          / (gridScale δ (ssfGridLen δ) c : ℝ)) ^ ζ')
        ≤ (B₂ : ENNReal) * totalLoss B₂ K₂ c₂ δ *
            Kakeya.maxDensity
              (𝒰.nodesIn c ((𝒰.cover.tube a j).rescale
                  (8 * gridScale δ (ssfGridLen δ) a)).toConvexSpaceBody)
              (fun j' => (𝒰.cover.tube c j').toConvexSpaceBody)) :
    ∀ c : ℕ, a + m' ≤ c → c + m' ≤ b → ∀ p ∈ 𝒰.cover.indexSet a,
      ENNReal.ofReal (((gridScale δ (ssfGridLen δ) a : ℝ)
          / (gridScale δ (ssfGridLen δ) c : ℝ)) ^ ζ')
        ≤ (Kn : ENNReal) * ((B₂ : ENNReal) * totalLoss B₂ K₂ c₂ δ)
            * (C₁ : ENNReal) *
            Kakeya.maxDensity (𝒰.nodesUnder c a p)
              (fun j' => (𝒰.cover.tube c j').toConvexSpaceBody) := by
  intro c hc1 hc2 p hp
  obtain ⟨j0, hj0F⟩ := hFne
  have hj0 : j0 ∈ 𝒰.cover.indexSet a := hFsub hj0F
  have hac : a ≤ c := by omega
  have hcM : c ≤ ssfGridLen δ := by omega
  have hcoe : (B₂ : ENNReal) * totalLoss B₂ K₂ c₂ δ
      = ((B₂ * (totalLoss B₂ K₂ c₂ δ).toNNReal : NNReal) : ENNReal) :=
    KT.coe_mul_ofReal B₂ (totalLoss_ne_top B₂ K₂ c₂ δ)
  have hlow0 := hlow c hc1 hc2 j0 hj0F
  rw [hcoe] at hlow0
  have hmain : ENNReal.ofReal (((gridScale δ (ssfGridLen δ) a : ℝ)
        / (gridScale δ (ssfGridLen δ) c : ℝ)) ^ ζ')
      ≤ (Kn : ENNReal) * ((B₂ : ENNReal) * totalLoss B₂ K₂ c₂ δ)
          * (C₁ : ENNReal) *
          Kakeya.maxDensity (𝒰.nodesUnder c a p)
            (fun j' => (𝒰.cover.tube c j').toConvexSpaceBody) := by
    apply KT.gridLower_of_band hδ hδ1 𝒰 hKn
      (Dn := B₂ * (totalLoss B₂ K₂ c₂ δ).toNNReal) (C' := C₁) (Φ₀ := Φ a c)
      hac hcM (fun j hj => hnb c hac hcM j hj) (hband c hcM) hj0 hlow0 p hp
  simpa [hcoe] using hmain

end SsfGapsKT

end MultiScaleFac

end Kakeya

end
