/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.AScaleBalls
public import Kakeya.DimensionThree.MainLemma2.NonSlabFibre

/-!
# The elementary sublayer of the scale-`a` estimates of Main Lemma 2

The two scale-`a` estimates packaged by `Kakeya.VeryNotSticky.AScaleData` — blueprint
`lowerBoundTTScaleAAndABall` and `volumeOfTTa` — are assembled in the blueprint
(`blueprint/src/GWZAdapted/section9_setup.tex`) out of small pieces, so that no single step
hides more than one idea. This file formalizes those pieces, apart from the ball geometry —
blueprint `lem:ml2packingBound`, `lem:ballCoverHalfRadius`, `lem:ml2ballPigeonhole`,
`lem:ml2ballRecentre` and `lem:ml2coarseShaded` — which is in
`Kakeya/DimensionThree/MainLemma2/AScaleBalls.lean`:

* the tube volume comparison across the two scales, blueprint `lem:ml2tubeVolumeRatio`;
* the two counting statements at the scale `a`, blueprint `lem:ml2uniformScaleA` and
  `lem:ml2parentCountInBody`, and the multiplicity transport they feed, blueprint
  `def:ml2DeltamaxScaleAConstant`, `lem:ml2DeltamaxScaleA` and `lem:ml2DeltamaxPower`;
* the coarse mass and volume estimates, blueprint `lem:ml2coarseMassBound`,
  `def:ml2aScaleVolumeConstant` and `lem:ml2coarseVolumeLower`, with the exponent budget
  `lem:ml2aScaleExponentBudget` and the rearrangement `lem:ml2aScaleVolume`, which is
  estimate (ii) of `Kakeya.VeryNotSticky.AScaleData`;
* the ball-scale estimate itself, blueprint `def:ml2aScaleBallConstant` and
  `lem:ml2aScaleBall`, which is estimate (i) of `Kakeya.VeryNotSticky.AScaleData`.

The comparison constants themselves — blueprint `def:ml2tubeVolumeRatioConstant`,
`def:ml2DeltamaxScaleAConstant`, `def:ml2aScaleVolumeConstant` and
`def:ml2aScaleBallConstant` — are in `Kakeya.DimensionThree.MainLemma2.AScaleConstants`,
upstream of `Kakeya.DimensionThree.MainLemma2.VeryNotSticky`, because the configuration
carries the clause absorbing the constant they combine into.

Assembling `Kakeya.VeryNotSticky.exists_aScaleData` out of these is deliberately *not* done
here; see the docstring of that declaration.

Three deliberate divergences from the blueprint text are recorded at the declarations
concerned: `Tube.UniformTubeSet` carries a single constant for both the
branching bracket and the bounded overlap, and its assignment is a function, so the overlap
constant `D₀` of the blueprint is carried as a free parameter bounded below by `1` rather
than read off the bundle; `Kakeya.ShadedBody.shadingMultiplicityEstimateForRhoTubes` carries a
*fixed* constant rather than an existential one, so blueprint `def:ml2aScaleBallConstant` is a
formula and not a choice; and `Kakeya.KatzTaoEstimate.multiplicity_bound` asks for pairwise
essential distinctness of the family it is applied to, which the parent family `𝕋_a` of a
`UniformTubeSet` does not have, so blueprint `lem:ml2coarseMassBound` carries the Katz–Tao
conclusion as a hypothesis instead of deriving it.
-/

@[expose] public section

namespace Kakeya

open MeasureTheory Metric Set

/-! ### The volume of a tube and of its scale-`a` parent -/

/-- **Volume ratio of a tube and its scale-`a` parent** (blueprint `lem:ml2tubeVolumeRatio`).

For `δ ≤ 1` and `a ≤ 1` in `ℝ³`, any `δ`-tube `T` and any `a`-tube `Ta` satisfy
`c (a/δ)² |T| ≤ |Ta| ≤ c⁻¹ (a/δ)² |T|` with `c = Kakeya.tubeVolumeRatioConstant 3 = π/36`.
Both halves are written without division: the first conjunct is `c a² |T| ≤ δ² |Ta|` and the
second is `c δ² |Ta| ≤ a² |T|`.

Each half uses one of the two bounds of blueprint `def:ml2tubeVolumeRatioConstant` on each
tube; the development contains no Steiner-type volume formula for the neighbourhood of a
segment, and an absolute constant costs nothing here, since blueprint `lem:ml2aScaleVolume`
carries a comparison constant in any case.

The first conjunct is used in `Kakeya.VeryNotSticky.coarseVolumeLower` and the second in
`Kakeya.VeryNotSticky.maxDensity_activeTubeNodes_le`. -/
theorem volume_tube_ratio {δ a : NNReal} (hδ1 : δ ≤ 1) (ha1 : a ≤ 1)
    (T : Tube δ (EuclideanSpace ℝ (Fin 3))) (Ta : Tube a (EuclideanSpace ℝ (Fin 3))) :
    (tubeVolumeRatioConstant 3 : ENNReal) * ((a : ENNReal) ^ 2 * volume T.carrier) ≤
        (δ : ENNReal) ^ 2 * volume Ta.carrier ∧
      (tubeVolumeRatioConstant 3 : ENNReal) * ((δ : ENNReal) ^ 2 * volume Ta.carrier) ≤
        (a : ENNReal) ^ 2 * volume T.carrier := by
  have hfin : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := finrank_euclideanSpace_fin
  have hvolT_le : volume T.carrier ≤ (Tube.volume_le.C 3 : ENNReal) * (δ : ENNReal) ^ 2 := by
    simpa [hfin] using (Tube.volume_le hδ1 T)
  have hvolTa_le : volume Ta.carrier ≤ (Tube.volume_le.C 3 : ENNReal) * (a : ENNReal) ^ 2 := by
    simpa [hfin] using (Tube.volume_le ha1 Ta)
  have hvolT_ge : (Tube.le_volume.c 3 : ENNReal) * (δ : ENNReal) ^ 2 ≤ volume T.carrier := by
    simpa [hfin] using (Tube.le_volume T)
  have hvolTa_ge : (Tube.le_volume.c 3 : ENNReal) * (a : ENNReal) ^ 2 ≤ volume Ta.carrier := by
    simpa [hfin] using (Tube.le_volume Ta)
  have hC₃₀ : Tube.volume_le.C 3 ≠ 0 := ne_of_gt (Tube.volume_le.C_pos 3)
  have hc_mul : (tubeVolumeRatioConstant 3 : ENNReal) * (Tube.volume_le.C 3 : ENNReal) =
      (Tube.le_volume.c 3 : ENNReal) := by
    rw [tubeVolumeRatioConstant, ENNReal.coe_div hC₃₀]
    exact ENNReal.div_mul_cancel (by exact_mod_cast hC₃₀) (by simp)
  constructor
  · calc
      (tubeVolumeRatioConstant 3 : ENNReal) * ((a : ENNReal) ^ 2 * volume T.carrier)
          ≤ (tubeVolumeRatioConstant 3 : ENNReal) *
              ((a : ENNReal) ^ 2 * ((Tube.volume_le.C 3 : ENNReal) * (δ : ENNReal) ^ 2)) := by
            gcongr
      _ = (tubeVolumeRatioConstant 3 : ENNReal) * (Tube.volume_le.C 3 : ENNReal) *
            (a : ENNReal) ^ 2 * (δ : ENNReal) ^ 2 := by
            ring
      _ = (Tube.le_volume.c 3 : ENNReal) * (a : ENNReal) ^ 2 * (δ : ENNReal) ^ 2 := by
            rw [hc_mul]
      _ = (δ : ENNReal) ^ 2 * ((Tube.le_volume.c 3 : ENNReal) * (a : ENNReal) ^ 2) := by
            ring
      _ ≤ (δ : ENNReal) ^ 2 * volume Ta.carrier := by
            gcongr
  · calc
      (tubeVolumeRatioConstant 3 : ENNReal) * ((δ : ENNReal) ^ 2 * volume Ta.carrier)
          ≤ (tubeVolumeRatioConstant 3 : ENNReal) *
              ((δ : ENNReal) ^ 2 * ((Tube.volume_le.C 3 : ENNReal) * (a : ENNReal) ^ 2)) := by
            gcongr
      _ = (tubeVolumeRatioConstant 3 : ENNReal) * (Tube.volume_le.C 3 : ENNReal) *
            (δ : ENNReal) ^ 2 * (a : ENNReal) ^ 2 := by
            ring
      _ = (Tube.le_volume.c 3 : ENNReal) * (δ : ENNReal) ^ 2 * (a : ENNReal) ^ 2 := by
            rw [hc_mul]
      _ = (a : ENNReal) ^ 2 * ((Tube.le_volume.c 3 : ENNReal) * (δ : ENNReal) ^ 2) := by
            ring
      _ ≤ (a : ENNReal) ^ 2 * volume T.carrier := by
            gcongr

/-! ### Counting at the scale `a` -/

namespace VeryNotSticky

variable {N : ℕ} {C₀ : NNReal}

open scoped Classical in
/-- The assignment classes at a grid level partition `𝕋`.

This is `Kakeya.VeryNotSticky.nonslabFibrePartition` with its unused angular-scale hypothesis
removed: `GridCoverSystem.assign` is a *function*, so its classes partition `cfg.s` at every
level of the grid, and no scale hypothesis enters. It is the counting input of
`Kakeya.VeryNotSticky.card_le_card_activeTubeNodes_mul` and
`Kakeya.VeryNotSticky.card_parentsIn_mul_card_tubeFibre_le`. -/
theorem sum_card_tubeFibre (cfg : VeryNotSticky)
    (𝒰 : Tube.UniformTubeSet cfg.s (fun i ↦ (cfg.T i).toTube) N C₀) {k : ℕ} (hk : k ≤ N) :
    ∑ j ∈ cfg.activeTubeNodes 𝒰 k, (cfg.tubeFibre 𝒰 k j).card = cfg.s.card := by
  classical
  let J := cfg.activeTubeNodes 𝒰 k
  change ∑ j ∈ J, (cfg.tubeFibre 𝒰 k j).card = cfg.s.card
  have hdisj : (J : Set cfg.ι).PairwiseDisjoint (cfg.tubeFibre 𝒰 k) := by
    change ∀ ⦃j⦄, j ∈ J → ∀ ⦃j'⦄, j' ∈ J → j ≠ j' →
      Disjoint (cfg.tubeFibre 𝒰 k j) (cfg.tubeFibre 𝒰 k j')
    intro j hj j' hj' hjj'
    rw [Finset.disjoint_left]
    intro i hij hij'
    have hj_eq : 𝒰.cover.assign k i = j := by
      simp only [tubeFibre, Tube.coverClass, Finset.mem_filter] at hij
      exact hij.2
    have hj'_eq : 𝒰.cover.assign k i = j' := by
      simp only [tubeFibre, Tube.coverClass, Finset.mem_filter] at hij'
      exact hij'.2
    exact hjj' (hj_eq.symm.trans hj'_eq)
  have hbiUnion : J.biUnion (cfg.tubeFibre 𝒰 k) = cfg.s := by
    apply Finset.Subset.antisymm
    · intro i hi
      rcases Finset.mem_biUnion.mp hi with ⟨j, hj, hji⟩
      exact Kakeya.VeryNotSticky.tubeFibre_subset cfg 𝒰 k j hji
    · intro i hi
      have hj : 𝒰.cover.assign k i ∈ 𝒰.cover.indexSet k := 𝒰.cover.assign_mem k hk i hi
      have hinf : i ∈ cfg.tubeFibre 𝒰 k (𝒰.cover.assign k i) := by
        simp [tubeFibre, Tube.coverClass, hi]
      have hactive : 𝒰.cover.assign k i ∈ J := by
        simp only [J, activeTubeNodes, Finset.mem_filter]
        exact ⟨hj, ⟨i, hinf⟩⟩
      exact Finset.mem_biUnion.mpr ⟨𝒰.cover.assign k i, hactive, hinf⟩
  rw [← Finset.card_biUnion hdisj, hbiUnion]

/-- Two assignment classes at the same grid level have comparable size.

Blueprint `uniformSetOfTubes`(iii) compares each `|𝕋[T_a]|` with the branching number `N` in
both directions with the constant `C₀`, so comparing two *parents* with one another spends
`C₀` twice. -/
theorem card_tubeFibre_le_card_tubeFibre (cfg : VeryNotSticky)
    (𝒰 : Tube.UniformTubeSet cfg.s (fun i ↦ (cfg.T i).toTube) N C₀) {k : ℕ} (hk : k ≤ N)
    {j j' : cfg.ι} (hj : j ∈ 𝒰.cover.indexSet k) (hj' : j' ∈ 𝒰.cover.indexSet k) :
    ((cfg.tubeFibre 𝒰 k j).card : NNReal) ≤ C₀ ^ 2 * ((cfg.tubeFibre 𝒰 k j').card : NNReal) := by
  calc
    ((cfg.tubeFibre 𝒰 k j).card : NNReal) ≤ C₀ * 𝒰.branchingN k := by
      simpa [tubeFibre] using 𝒰.card_class_le k hk j hj
    _ ≤ C₀ * (C₀ * ((cfg.tubeFibre 𝒰 k j').card : NNReal)) := by
      exact mul_le_mul_of_nonneg_left
        (by simpa [tubeFibre] using 𝒰.le_card_class k hk j' hj') (by positivity)
    _ = C₀ ^ 2 * ((cfg.tubeFibre 𝒰 k j').card : NNReal) := by
      rw [pow_two]
      ring

/-- **Branching count at the scale `a`** (blueprint `lem:ml2uniformScaleA`).

`|𝕋| ≤ C₀² |𝕋_a| |𝕋[T_a]|` and `|𝕋_a| |𝕋[T_a]| ≤ C₀² D₀ |𝕋|`, for `T_a` any parent tube in
`𝕋_a`. The loss is `C₀²`, not `C₀`, because comparing two parents with one another spends the
branching constant twice (`Kakeya.VeryNotSticky.card_tubeFibre_le_card_tubeFibre`).

Only the first inequality is used downstream; the second is recorded because it is the
direction that the blueprint attributes to the bounded overlap `D₀`. In the Lean bundle
`Tube.UniformTubeSet` the assignment is a function, so its classes *partition*
`𝕋` and the overlap is `1`; `D₀` therefore enters only as a free parameter with `1 ≤ D₀`,
kept so that the constants of blueprint `def:ml2DeltamaxScaleAConstant` and
`def:ml2aScaleVolumeConstant` read as the blueprint writes them. -/
theorem card_le_card_activeTubeNodes_mul (cfg : VeryNotSticky)
    (𝒰 : Tube.UniformTubeSet cfg.s (fun i ↦ (cfg.T i).toTube) N C₀) {k : ℕ} (hk : k ≤ N)
    {D₀ : NNReal} (hD₀ : 1 ≤ D₀) {j : cfg.ι} (hj : j ∈ 𝒰.cover.indexSet k) :
    (cfg.s.card : NNReal) ≤
        C₀ ^ 2 * (((cfg.activeTubeNodes 𝒰 k).card : NNReal) *
          ((cfg.tubeFibre 𝒰 k j).card : NNReal)) ∧
      ((cfg.activeTubeNodes 𝒰 k).card : NNReal) * ((cfg.tubeFibre 𝒰 k j).card : NNReal) ≤
        C₀ ^ 2 * D₀ * (cfg.s.card : NNReal) := by
  classical
  let active := cfg.activeTubeNodes 𝒰 k
  let f : cfg.ι → NNReal := fun j' ↦ ((cfg.tubeFibre 𝒰 k j').card : NNReal)
  have hsum : (∑ j' ∈ active, f j') = (cfg.s.card : NNReal) := by
    rw [← Nat.cast_sum]
    exact congrArg (fun n : ℕ ↦ (n : NNReal)) (sum_card_tubeFibre cfg 𝒰 hk)
  have hle : ∀ j' ∈ active, f j' ≤ C₀ ^ 2 * f j := by
    intro j' hj'
    have hj'k : j' ∈ 𝒰.cover.indexSet k := (Finset.mem_filter.mp hj').1
    exact card_tubeFibre_le_card_tubeFibre cfg 𝒰 hk hj'k hj
  have hle' : ∀ j' ∈ active, f j ≤ C₀ ^ 2 * f j' := by
    intro j' hj'
    have hj'k : j' ∈ 𝒰.cover.indexSet k := (Finset.mem_filter.mp hj').1
    exact card_tubeFibre_le_card_tubeFibre cfg 𝒰 hk hj hj'k
  constructor
  · calc
      (cfg.s.card : NNReal) = ∑ j' ∈ active, f j' := hsum.symm
      _ ≤ ∑ j' ∈ active, (C₀ ^ 2 * f j) := by
        exact Finset.sum_le_sum hle
      _ = C₀ ^ 2 * (((cfg.activeTubeNodes 𝒰 k).card : NNReal) *
          ((cfg.tubeFibre 𝒰 k j).card : NNReal)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
        ring
  · calc
      ((cfg.activeTubeNodes 𝒰 k).card : NNReal) * ((cfg.tubeFibre 𝒰 k j).card : NNReal)
          = ∑ j' ∈ active, f j := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ j' ∈ active, (C₀ ^ 2 * f j') := by
        exact Finset.sum_le_sum hle'
      _ = C₀ ^ 2 * (∑ j' ∈ active, f j') := by
        rw [Finset.mul_sum]
      _ = C₀ ^ 2 * (cfg.s.card : NNReal) := by
        rw [hsum]
      _ ≤ C₀ ^ 2 * D₀ * (cfg.s.card : NNReal) := by
        have hleD : (cfg.s.card : NNReal) ≤ D₀ * (cfg.s.card : NNReal) := by
          simpa [one_mul] using mul_le_mul_of_nonneg_right hD₀ (by positivity)
        calc
          C₀ ^ 2 * (cfg.s.card : NNReal) ≤ C₀ ^ 2 * (D₀ * (cfg.s.card : NNReal)) := by
            exact mul_le_mul_of_nonneg_left hleD (by positivity)
          _ = C₀ ^ 2 * D₀ * (cfg.s.card : NNReal) := by ring

open scoped Classical in
/-- The parent nodes at grid level `k` whose node tube is contained in the body `K`.

This is the blueprint's `𝕋_a[K]` of `def:WW`, read on the parent family
`Kakeya.VeryNotSticky.activeTubeNodes`. -/
noncomputable def parentsIn (cfg : VeryNotSticky)
    (𝒰 : Tube.UniformTubeSet cfg.s (fun i ↦ (cfg.T i).toTube) N C₀) (k : ℕ)
    (K : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))) : Finset cfg.ι :=
  (cfg.activeTubeNodes 𝒰 k).filter fun j ↦ (𝒰.cover.tube k j).toConvexSpaceBody ≤ K

/-- **Parent count inside a convex body** (blueprint `lem:ml2parentCountInBody`).

`|𝕋_a[K]| |𝕋[T_a]| ≤ C₀² D₀ |𝕋[K]|` for any convex body `K` and any parent tube `T_a ∈ 𝕋_a`.
This is the two-scale count that the multiplicity estimate at the scale `a` needs, and the
analogue for a single body of the second inequality of
`Kakeya.VeryNotSticky.card_le_card_activeTubeNodes_mul`, which it recovers at `K = B₁`.

Counting the pairs `(T_a', T)` with `T_a' ∈ 𝕋_a[K]` and `T ∈ 𝕋[T_a']` in two ways: a tube of
a class whose node lies in `K` lies in `K`, the classes are disjoint, and each class is at
least `C₀^{-2} |𝕋[T_a]|`. -/
theorem card_parentsIn_mul_card_tubeFibre_le (cfg : VeryNotSticky)
    (𝒰 : Tube.UniformTubeSet cfg.s (fun i ↦ (cfg.T i).toTube) N C₀) {k : ℕ} (hk : k ≤ N)
    {D₀ : NNReal} (hD₀ : 1 ≤ D₀) {j : cfg.ι} (hj : j ∈ 𝒰.cover.indexSet k)
    (K : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))) :
    ((cfg.parentsIn 𝒰 k K).card : NNReal) * ((cfg.tubeFibre 𝒰 k j).card : NNReal) ≤
      C₀ ^ 2 * D₀ *
        ((familyIn cfg.s (fun i ↦ (cfg.T i).toConvexSpaceBody) K).card : NNReal) := by
  classical
  let P : Finset cfg.ι := cfg.parentsIn 𝒰 k K
  let F : Finset cfg.ι := familyIn cfg.s (fun i ↦ (cfg.T i).toConvexSpaceBody) K
  -- A tube whose node lies in `K` lies in `K`: the fibres of the active parents are
  -- contained in the fine family `𝕋[K]`.
  have hsub : ∀ j' ∈ P, cfg.tubeFibre 𝒰 k j' ⊆ F := by
    intro j' hj'
    have hj'P := Finset.mem_filter.mp hj'
    have hj'K : (𝒰.cover.tube k j').toConvexSpaceBody ≤ K := hj'P.2
    intro i hi
    have hmem_s : i ∈ cfg.s := (Finset.mem_filter.mp hi).1
    have hassign : 𝒰.cover.assign k i = j' := (Finset.mem_filter.mp hi).2
    have hle : (cfg.T i).toConvexSpaceBody ≤ (𝒰.cover.tube k j').toConvexSpaceBody := by
      simpa [hassign] using (𝒰.cover.le_tube_assign k hk i hmem_s)
    exact Finset.mem_filter.mpr ⟨hmem_s, hle.trans hj'K⟩
  -- The parent classes over `P` are pairwise disjoint, being fibres of the assignment.
  have hdisj : (P : Set cfg.ι).PairwiseDisjoint (cfg.tubeFibre 𝒰 k) := by
    change ∀ ⦃j' : cfg.ι⦄, j' ∈ P → ∀ ⦃j'' : cfg.ι⦄, j'' ∈ P → j' ≠ j'' →
      Disjoint (cfg.tubeFibre 𝒰 k j') (cfg.tubeFibre 𝒰 k j'')
    intro j' hj' j'' hj'' hjj'
    rw [Finset.disjoint_left]
    intro i hij' hij''
    have heq1 : 𝒰.cover.assign k i = j' := by
      simp only [tubeFibre, Tube.coverClass, Finset.mem_filter] at hij'
      exact hij'.2
    have heq2 : 𝒰.cover.assign k i = j'' := by
      simp only [tubeFibre, Tube.coverClass, Finset.mem_filter] at hij''
      exact hij''.2
    exact hjj' (heq1.symm.trans heq2)
  -- Summing the fibre sizes over the parents bounds `|𝕋[K]|`.
  have hcard_le : (∑ j' ∈ P, (cfg.tubeFibre 𝒰 k j').card) ≤ F.card := by
    calc
      (∑ j' ∈ P, (cfg.tubeFibre 𝒰 k j').card) = (P.biUnion (cfg.tubeFibre 𝒰 k)).card := by
        rw [Finset.card_biUnion hdisj]
      _ ≤ F.card := Finset.card_le_card (by
        intro i hi
        rcases Finset.mem_biUnion.mp hi with ⟨j', hj', hi'⟩
        exact hsub j' hj' hi')
  -- Branching: `|𝕋[T_a]| ≤ C₀² |𝕋[T_a']|` termwise over the parents.
  have hfibre_le : ∀ j' ∈ P,
      ((cfg.tubeFibre 𝒰 k j).card : NNReal) ≤
        C₀ ^ 2 * ((cfg.tubeFibre 𝒰 k j').card : NNReal) := by
    intro j' hj'
    have hj'Idx : j' ∈ 𝒰.cover.indexSet k :=
      (Finset.mem_filter.mp (Finset.mem_filter.mp hj').1).1
    exact card_tubeFibre_le_card_tubeFibre cfg 𝒰 hk hj hj'Idx
  have hsum_le : (∑ j' ∈ P, ((cfg.tubeFibre 𝒰 k j).card : NNReal)) ≤
      ∑ j' ∈ P, (C₀ ^ 2 * ((cfg.tubeFibre 𝒰 k j').card : NNReal)) := by
    exact Finset.sum_le_sum (fun j' hj' => hfibre_le j' hj')
  have hP_mul : (P.card : NNReal) * ((cfg.tubeFibre 𝒰 k j).card : NNReal) ≤
      C₀ ^ 2 * ((∑ j' ∈ P, (cfg.tubeFibre 𝒰 k j').card : NNReal)) := by
    calc
      (P.card : NNReal) * ((cfg.tubeFibre 𝒰 k j).card : NNReal)
          = (∑ j' ∈ P, ((cfg.tubeFibre 𝒰 k j).card : NNReal)) := by
            rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ j' ∈ P, (C₀ ^ 2 * ((cfg.tubeFibre 𝒰 k j').card : NNReal)) := hsum_le
      _ = C₀ ^ 2 * (∑ j' ∈ P, ((cfg.tubeFibre 𝒰 k j').card : NNReal)) := by
            rw [Finset.mul_sum]
  have hcard_le_N : (∑ j' ∈ P, ((cfg.tubeFibre 𝒰 k j').card : NNReal)) ≤ (F.card : NNReal) := by
    exact_mod_cast hcard_le
  have hmain : (P.card : NNReal) * ((cfg.tubeFibre 𝒰 k j).card : NNReal) ≤
      C₀ ^ 2 * (F.card : NNReal) := by
    exact hP_mul.trans (by gcongr)
  -- finally weaken with `1 ≤ D₀`.
  have hD : (F.card : NNReal) ≤ D₀ * (F.card : NNReal) := by
    calc
      (F.card : NNReal) = 1 * (F.card : NNReal) := by rw [one_mul]
      _ ≤ D₀ * (F.card : NNReal) := by gcongr
  simpa [P, F] using (calc
    (P.card : NNReal) * ((cfg.tubeFibre 𝒰 k j).card : NNReal) ≤
        C₀ ^ 2 * (F.card : NNReal) := hmain
    _ ≤ C₀ ^ 2 * (D₀ * (F.card : NNReal)) := by gcongr
    _ = C₀ ^ 2 * D₀ * (F.card : NNReal) := by ac_rfl)

/-- The single-body form of blueprint `lem:ml2DeltamaxScaleA`: the density of the parent
family in a fixed convex body `K` already obeys the bound, with no `K` left in it.

Stated at an arbitrary scale `ρ ≤ 1` of the multiscale grid, not only at `cfg.a`: the proof
reads the radius of the parent tubes off `hgrid` and nothing else, so nothing ties it to the
factoring dimension. That generality is what
`Kakeya.VeryNotSticky.rScaleParentData_of_gridScale` needs, since the radius it is invoked at is
an arbitrary `r ≥ cfg.a` rounded up to the grid (`Kakeya.StickyKakeya.exists_gridScale_ge`).

`Δ(𝕋_a, K) ≤ |𝕋_a[K]| C₃ a² / |K|` by the upper tube-volume bound of blueprint
`def:ml2tubeVolumeRatioConstant`, and `Δ(𝕋, K) ≥ |𝕋[K]| c₃ δ² / |K|` by its lower bound;
feeding in the two-scale count
`Kakeya.VeryNotSticky.card_parentsIn_mul_card_tubeFibre_le` and
`Δ(𝕋, K) ≤ Δ_max(𝕋) ≤ δ^{-η}`, which is `cfg.maxDensity_le`, removes `K`. -/
theorem densityIn_activeTubeNodes_le (cfg : VeryNotSticky) (hC₀ : 1 ≤ C₀)
    (𝒰 : Tube.UniformTubeSet cfg.s (fun i ↦ (cfg.T i).toTube) N C₀) {k : ℕ} (hk : k ≤ N)
    {D₀ : NNReal} (hD₀ : 1 ≤ D₀) {j : cfg.ι} (hj : j ∈ 𝒰.cover.indexSet k)
    {ρ : NNReal} (hgrid : Tube.gridScale cfg.δ N k = ρ) (hρ1 : ρ ≤ 1)
    (K : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))) :
    densityIn (cfg.activeTubeNodes 𝒰 k) (fun j' ↦ (𝒰.cover.tube k j').toConvexSpaceBody) K *
        (((cfg.tubeFibre 𝒰 k j).card : ENNReal) * (cfg.δ : ENNReal) ^ cfg.η *
          (cfg.δ : ENNReal) ^ 2) ≤
      (deltamaxScaleAConstant C₀ D₀ : ENNReal) * (ρ : ENNReal) ^ 2 := by
  classical
  let P : Finset cfg.ι := cfg.activeTubeNodes 𝒰 k
  let Wa : cfg.ι → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)) :=
    fun j' ↦ (𝒰.cover.tube k j').toConvexSpaceBody
  let parents : Finset cfg.ι := cfg.parentsIn 𝒰 k K
  let fK : Finset cfg.ι := familyIn cfg.s (fun i ↦ (cfg.T i).toConvexSpaceBody) K
  let S : ENNReal := ∑ j' ∈ parents, volume (Wa j').carrier
  let d : ENNReal := (cfg.δ : ENNReal)
  let A : ENNReal := (ρ : ENNReal)
  let Nf : ENNReal := ((cfg.tubeFibre 𝒰 k j).card : ENNReal)
  let b : ENNReal := Nf * d ^ cfg.η * d ^ 2
  let c₃ : ENNReal := (Tube.le_volume.c 3 : ENNReal)
  let C₃ : ENNReal := (Tube.volume_le.C 3 : ENNReal)
  let CD : ENNReal := (C₀ ^ 2 * D₀ : ENNReal)
  let vK : ENNReal := volume K.carrier
  let C : ENNReal := (deltamaxScaleAConstant C₀ D₀ : ENNReal) * A ^ 2
  have hfin : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := finrank_euclideanSpace_fin
  have hd0 : d ≠ 0 := by
    exact ENNReal.coe_ne_zero.mpr (ne_of_gt cfg.hδ)
  have hdtop : d ≠ ⊤ := by
    exact ENNReal.coe_ne_top
  have hd : d ^ cfg.η * d ^ (-cfg.η) = 1 := by
    rw [← ENNReal.rpow_add cfg.η (-cfg.η) hd0 hdtop]
    have hzero : cfg.η + -cfg.η = 0 := by ring
    rw [hzero, ENNReal.rpow_zero]
  have hc₃ : c₃ ≠ 0 := by
    exact ENNReal.coe_ne_zero.mpr (Tube.le_volume.c_pos 3).ne'
  have hc₃top : c₃ ≠ ⊤ := by
    exact ENNReal.coe_ne_top
  -- the dimension-3 tube-volume comparison constant identity
  have hconstNN : deltamaxScaleAConstant C₀ D₀ * Tube.le_volume.c 3 =
      C₀ ^ 2 * D₀ * Tube.volume_le.C 3 := by
    rw [deltamaxScaleAConstant, tubeVolumeRatioConstant]
    field_simp [Tube.le_volume.c_pos 3, Tube.volume_le.C_pos 3]
    exact div_self (Tube.le_volume.c_pos 3).ne'
  have hconstE : (deltamaxScaleAConstant C₀ D₀ : ENNReal) * c₃ = CD * C₃ := by
    simpa [c₃, C₃, CD] using congrArg (fun x : NNReal => (x : ENNReal)) hconstNN
  -- (2) termwise tube-volume upper bound over the parents
  have hterm : ∀ j' ∈ parents, volume (Wa j').carrier ≤ C₃ * A ^ 2 := by
    intro j' hj'
    have hδ1 : Tube.gridScale cfg.δ N k ≤ 1 := by simpa [hgrid] using hρ1
    simpa [Wa, A, C₃, hgrid, hfin] using (Tube.volume_le hδ1 (𝒰.cover.tube k j'))
  have hsum2 : S ≤ (parents.card : ENNReal) * (C₃ * A ^ 2) := by
    calc
      S = ∑ j' ∈ parents, volume (Wa j').carrier := rfl
      _ ≤ ∑ j' ∈ parents, (C₃ * A ^ 2) := Finset.sum_le_sum (fun j' hj' => hterm j' hj')
      _ = (parents.card : ENNReal) * (C₃ * A ^ 2) := by
        rw [Finset.sum_const, nsmul_eq_mul]
  -- (3) the two-scale count, cast to ENNReal
  have h3 : (parents.card : ENNReal) * Nf ≤ CD * (fK.card : ENNReal) := by
    have h : ((cfg.parentsIn 𝒰 k K).card : NNReal) * ((cfg.tubeFibre 𝒰 k j).card : NNReal) ≤
        C₀ ^ 2 * D₀ * ((familyIn cfg.s (fun i => (cfg.T i).toConvexSpaceBody) K).card : NNReal) :=
      card_parentsIn_mul_card_tubeFibre_le cfg 𝒰 hk hD₀ hj K
    have h' : ((cfg.parentsIn 𝒰 k K).card : ENNReal) * ((cfg.tubeFibre 𝒰 k j).card : ENNReal) ≤
        (C₀ ^ 2 * D₀ : ENNReal) *
          ((familyIn cfg.s (fun i => (cfg.T i).toConvexSpaceBody) K).card : ENNReal) := by
      exact_mod_cast h
    simpa [parents, fK, Nf, CD] using h'
  -- (4) the fine-scale lower bound
  have hterms : ∀ i ∈ cfg.s, c₃ * d ^ 2 ≤ volume ((cfg.T i).toConvexSpaceBody).carrier := by
    intro i hi
    simpa [d, c₃, hfin] using (Tube.le_volume (cfg.T i).toTube)
  have hsum4 : (fK.card : ENNReal) * (c₃ * d ^ 2) ≤
      ∑ i ∈ fK, volume ((cfg.T i).toConvexSpaceBody).carrier := by
    calc
      (fK.card : ENNReal) * (c₃ * d ^ 2) = ∑ _i ∈ fK, (c₃ * d ^ 2) := by
        rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ i ∈ fK, volume ((cfg.T i).toConvexSpaceBody).carrier := by
        exact Finset.sum_le_sum (fun i hi => hterms i (Finset.mem_filter.mp hi).1)
  have hvolsum : ∑ i ∈ fK, volume ((cfg.T i).toConvexSpaceBody).carrier = densityIn cfg.s
      (fun i => (cfg.T i).toConvexSpaceBody) K * vK := by
    simpa [fK, familyIn, vK] using (Kakeya.sum_volume_eq_densityIn_mul_volume cfg.s
      (fun i => (cfg.T i).toConvexSpaceBody) K)
  have hmden : densityIn cfg.s (fun i => (cfg.T i).toConvexSpaceBody) K ≤ d ^ (-cfg.η) := by
    exact (Kakeya.le_maxDensity cfg.s (fun i => (cfg.T i).toConvexSpaceBody) K).trans
      (by simpa [d] using cfg.maxDensity_le)
  have h4 : (fK.card : ENNReal) * (c₃ * d ^ 2) ≤ d ^ (-cfg.η) * vK := by
    calc
      (fK.card : ENNReal) * (c₃ * d ^ 2) ≤
          ∑ i ∈ fK, volume ((cfg.T i).toConvexSpaceBody).carrier := hsum4
      _ = densityIn cfg.s (fun i => (cfg.T i).toConvexSpaceBody) K * vK := hvolsum
      _ ≤ d ^ (-cfg.η) * vK := by
        exact mul_le_mul' hmden le_rfl
  -- (5) chain: c₃ * (S * b) ≤ C₀² D₀ C₃ A² vK = c₃ * (C * vK)
  have hchain : c₃ * (S * b) ≤ c₃ * (C * vK) := by
    calc
      c₃ * (S * b)
          ≤ c₃ * ((parents.card : ENNReal) * Nf * (C₃ * A ^ 2 * d ^ cfg.η * d ^ 2)) := by
            have hA :
                S * b ≤
                  (parents.card : ENNReal) * Nf * (C₃ * A ^ 2 * d ^ cfg.η * d ^ 2) := by
              calc
                S * b = S * (Nf * (d ^ cfg.η * d ^ 2)) := by ring
                _ ≤
                    ((parents.card : ENNReal) * (C₃ * A ^ 2)) *
                      (Nf * (d ^ cfg.η * d ^ 2)) := by
                  exact mul_le_mul' hsum2 le_rfl
                _ = (parents.card : ENNReal) * Nf * (C₃ * A ^ 2 * d ^ cfg.η * d ^ 2) := by ring
            exact mul_le_mul' le_rfl hA
      _ ≤ c₃ * (CD * (fK.card : ENNReal) * (C₃ * A ^ 2 * d ^ cfg.η * d ^ 2)) := by
            exact mul_le_mul' le_rfl (mul_le_mul' h3 le_rfl)
      _ = CD * C₃ * A ^ 2 * d ^ cfg.η * ((fK.card : ENNReal) * (c₃ * d ^ 2)) := by ring
      _ ≤ CD * C₃ * A ^ 2 * d ^ cfg.η * (d ^ (-cfg.η) * vK) := by
            exact mul_le_mul' le_rfl h4
      _ = CD * C₃ * A ^ 2 * vK := by
            calc
              CD * C₃ * A ^ 2 * d ^ cfg.η * (d ^ (-cfg.η) * vK)
                  = CD * C₃ * A ^ 2 * (d ^ cfg.η * d ^ (-cfg.η) * vK) := by ring
              _ = CD * C₃ * A ^ 2 * vK := by
                rw [hd, one_mul]
      _ = c₃ * (C * vK) := by
            calc
              CD * C₃ * A ^ 2 * vK =
                  (deltamaxScaleAConstant C₀ D₀ : ENNReal) * c₃ * A ^ 2 * vK := by
                rw [← hconstE]
              _ = c₃ * (C * vK) := by
                dsimp [C]
                ring
  have hSb : S * b ≤ C * vK := by
    exact (ENNReal.mul_le_mul_iff_right hc₃ hc₃top).mp hchain
  -- reduce the sum-form inequality to the density inequality
  by_cases hK : vK = 0
  · have hden0 : densityIn P Wa K = 0 :=
      Kakeya.densityIn_eq_zero_of_volume_eq_zero (K := K) hK
    rw [hden0]
    simp
  · have hK0 : vK ≠ 0 := hK
    have hKtop : vK ≠ ⊤ := K.isCompact.measure_ne_top
    have hdens : densityIn P Wa K * b = (S * b) / vK := by
      change (S / vK) * b = (S * b) / vK
      rw [← ENNReal.mul_div_right_comm]
    rw [hdens]
    exact (ENNReal.div_le_iff_le_mul (Or.inl hK0) (Or.inl hKtop)).2 hSb

/-- **Multiplicity of the parent tubes at a grid scale** (blueprint `lem:ml2DeltamaxScaleA`).

`Δ_max(𝕋_ρ) |𝕋[T_ρ]| δ^η δ² ≤ C_{lem:ml2DeltamaxScaleA} ρ²` at every scale `ρ ≤ 1` of the
multiscale grid — the hypothesis `hgrid` names which grid index `ρ` is, and nothing else in
the proof mentions `cfg.a`. At `ρ = cfg.a` this is the blueprint's statement verbatim; at a
general grid scale it is what `Kakeya.VeryNotSticky.rScaleParentData_of_gridScale` applies, after
rounding its radius `r` up to the grid with `Kakeya.StickyKakeya.exists_gridScale_ge`.

In the displayed form at `ρ = a`:

`Δ_max(𝕋_a) |𝕋[T_a]| δ^η δ² ≤ C_{lem:ml2DeltamaxScaleA} a²`, equivalently
`Δ_max(𝕋_a) ≤ C δ^{-η} (a/δ)² / |𝕋[T_a]|`, with
`C = Kakeya.deltamaxScaleAConstant C₀ D₀`.

For a convex body `K`, `Δ(𝕋_a, K) ≤ |𝕋_a[K]| C₃ a² / |K|` by the upper tube-volume bound of
blueprint `def:ml2tubeVolumeRatioConstant`, and
`Δ(𝕋, K) ≥ |𝕋[K]| c₃ δ² / |K|` by its lower bound; feeding in the two-scale count
`Kakeya.VeryNotSticky.card_parentsIn_mul_card_tubeFibre_le` and
`Δ(𝕋, K) ≤ Δ_max(𝕋) ≤ δ^{-η}` (which is `cfg.maxDensity_le`) gives a bound free of `K`, and
`Kakeya.maxDensity_le_iff` turns it into a bound on the supremum.

The bound carries a comparison constant, and it has to: the two-scale count spends the
branching constant twice and the overlap constant once, and comparing `|T_a|` with `|T|`
spends `c`. The constant-free form is an over-claim. -/
theorem maxDensity_activeTubeNodes_le (cfg : VeryNotSticky) (hC₀ : 1 ≤ C₀)
    (𝒰 : Tube.UniformTubeSet cfg.s (fun i ↦ (cfg.T i).toTube) N C₀) {k : ℕ} (hk : k ≤ N)
    {D₀ : NNReal} (hD₀ : 1 ≤ D₀) {j : cfg.ι} (hj : j ∈ 𝒰.cover.indexSet k)
    {ρ : NNReal} (hgrid : Tube.gridScale cfg.δ N k = ρ) (hρ1 : ρ ≤ 1) :
    maxDensity (cfg.activeTubeNodes 𝒰 k) (fun j' ↦ (𝒰.cover.tube k j').toConvexSpaceBody) *
          ((cfg.tubeFibre 𝒰 k j).card : ENNReal) * (cfg.δ : ENNReal) ^ cfg.η *
          (cfg.δ : ENNReal) ^ 2 ≤
      (deltamaxScaleAConstant C₀ D₀ : ENNReal) * (ρ : ENNReal) ^ 2 := by
  classical
  let P : Finset cfg.ι := cfg.activeTubeNodes 𝒰 k
  let Wa : cfg.ι → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)) :=
    fun j' ↦ (𝒰.cover.tube k j').toConvexSpaceBody
  let Nf : ENNReal := ((cfg.tubeFibre 𝒰 k j).card : ENNReal)
  let d : ENNReal := (cfg.δ : ENNReal)
  let A : ENNReal := (ρ : ENNReal)
  let CD : ENNReal := (deltamaxScaleAConstant C₀ D₀ : ENNReal)
  let X : ENNReal := Nf * d ^ cfg.η * d ^ 2
  rcases eq_or_ne Nf 0 with hNf0 | hNf0
  · simp [Nf, hNf0]
  · have hd0 : d ≠ 0 := ENNReal.coe_ne_zero.mpr (ne_of_gt cfg.hδ)
    have hdtop : d ≠ ⊤ := ENNReal.coe_ne_top
    have hNftop : Nf ≠ ⊤ := by
      change ((cfg.tubeFibre 𝒰 k j).card : ENNReal) ≠ ⊤
      exact ENNReal.natCast_ne_top _
    have hdη0 : d ^ cfg.η ≠ 0 := by
      simp [hd0, hdtop]
    have hdηtop : d ^ cfg.η ≠ ⊤ := ENNReal.rpow_ne_top_of_ne_zero hd0 hdtop
    have hd20 : d ^ 2 ≠ 0 := pow_ne_zero 2 hd0
    have hd2top : d ^ 2 ≠ ⊤ := ENNReal.pow_ne_top hdtop
    have hX0 : X ≠ 0 := by
      have hNdη0 : Nf * d ^ cfg.η ≠ 0 := mul_ne_zero hNf0 hdη0
      simpa [X] using mul_ne_zero hNdη0 hd20
    have hXtop : X ≠ ⊤ := by
      have hNdηtop : Nf * d ^ cfg.η ≠ ⊤ := ENNReal.mul_ne_top hNftop hdηtop
      simpa [X] using ENNReal.mul_ne_top hNdηtop hd2top
    have hdiv : maxDensity P Wa ≤ (CD * A ^ 2) / X := by
      rw [maxDensity_le_iff]
      intro K
      have hK := densityIn_activeTubeNodes_le cfg hC₀ 𝒰 hk hD₀ hj hgrid hρ1 K
      have hK' : densityIn P Wa K * X ≤ CD * A ^ 2 := by
        simpa [P, Wa, Nf, d, A, CD, X] using hK
      exact (ENNReal.le_div_iff_mul_le (Or.inl hX0) (Or.inl hXtop)).mpr hK'
    calc
      maxDensity P Wa * Nf * d ^ cfg.η * d ^ 2 = maxDensity P Wa * X := by
        dsimp [X]
        ac_rfl
      _ ≤ ((CD * A ^ 2) / X) * X := by
        exact mul_le_mul_left hdiv X
      _ = CD * A ^ 2 := by
        rw [ENNReal.div_mul_cancel hX0 hXtop]
      _ = (deltamaxScaleAConstant C₀ D₀ : ENNReal) * (ρ : ENNReal) ^ 2 := by
        simp [CD, A]

end VeryNotSticky

/-! ### The coarse mass and volume estimates -/

/-- **The `Δ_max` factor at the scale `a`** (blueprint `lem:ml2DeltamaxPower`).

Raising `Δ ≤ C δ^{-η} P` to the power `1 - β ∈ [0, 1]` costs nothing beyond what is already
there: `C^{1-β} ≤ C` because `C ≥ 1` and `δ^{-η(1-β)} ≤ δ^{-η}` because `0 < δ ≤ 1` and
`η ≥ 0`.

Stated as a pure `ℝ≥0∞` inequality, with `d` for `δ` and `P` for `(a/δ)²/|𝕋[T_a]|`, following
the convention of `Kakeya.VeryNotSticky.mul_self_mul_le_of_aScaleChain`.

**This is an interface statement and is deliberately kept without a call site.** It is the Lean
rendering of blueprint `lem:ml2DeltamaxPower`, retained so that the blueprint lemma has a named
counterpart; the current route to `Kakeya.VeryNotSticky.AScaleData` reaches the same bound
through `Kakeya.VeryNotSticky.coarseKatzTaoBound` and does not pass through it. `hd0` and
`hdtop` are hypotheses of the blueprint statement that this proof happens not to need; they are
kept so that the signature matches the blueprint, and underscored so that the `unusedArguments`
linter does not flag them. -/
theorem rpow_one_sub_le_of_le_mul {Δ P d : ENNReal} {C : NNReal} {β η : ℝ}
    (hC : 1 ≤ C) (_hd0 : d ≠ 0) (_hdtop : d ≠ ⊤) (hd1 : d ≤ 1) (hη : 0 ≤ η)
    (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (h : Δ ≤ (C : ENNReal) * d ^ (-η) * P) :
    Δ ^ (1 - β) ≤ (C : ENNReal) * d ^ (-η) * P ^ (1 - β) := by
  have h1b : 0 ≤ 1 - β := by linarith
  have h1b1 : 1 - β ≤ 1 := by linarith
  have hpow : Δ ^ (1 - β) ≤ ((C : ENNReal) * d ^ (-η) * P) ^ (1 - β) :=
    ENNReal.rpow_le_rpow h h1b
  have hsplit : ((C : ENNReal) * d ^ (-η) * P) ^ (1 - β) =
      (C : ENNReal) ^ (1 - β) * (d ^ (-η)) ^ (1 - β) * P ^ (1 - β) := by
    rw [mul_assoc (C : ENNReal) (d ^ (-η)) P]
    rw [ENNReal.mul_rpow_of_nonneg (C : ENNReal) (d ^ (-η) * P) h1b]
    rw [ENNReal.mul_rpow_of_nonneg (d ^ (-η)) P h1b]
    rw [mul_assoc]
  have hC' : 1 ≤ (C : ENNReal) := ENNReal.one_le_coe_iff.mpr hC
  have hCpow : (C : ENNReal) ^ (1 - β) ≤ (C : ENNReal) := by
    simpa using ENNReal.rpow_le_rpow_of_exponent_le hC' h1b1
  have hηb : η * (1 - β) ≤ η := by
    simpa using mul_le_mul_of_nonneg_left h1b1 hη
  have hneg : -η ≤ -η * (1 - β) := by linarith
  have hdpow : (d ^ (-η)) ^ (1 - β) ≤ d ^ (-η) := by
    rw [← ENNReal.rpow_mul d (-η) (1 - β)]
    exact ENNReal.rpow_le_rpow_of_exponent_ge hd1 hneg
  calc
    Δ ^ (1 - β) ≤ ((C : ENNReal) * d ^ (-η) * P) ^ (1 - β) := hpow
    _ = (C : ENNReal) ^ (1 - β) * (d ^ (-η)) ^ (1 - β) * P ^ (1 - β) := hsplit
    _ ≤ (C : ENNReal) * d ^ (-η) * P ^ (1 - β) := by
      gcongr

/-- **Exponent budget at the scale `a`** (blueprint `lem:ml2aScaleExponentBudget`).

For `η > 0` and `ν ≥ 90 η` the two exponents of the scale-`a` chain are ordered by
`2η + ν/90 ≤ ν/30 ≤ ν/9`: the first step is `η ≤ ν/90`, the second is `ν > 0`. Consequently
`δ^{ν/9} ≤ δ^{2η+ν/90}` for `0 < δ ≤ 1`, since `s ↦ δ^s` is antitone there.

This is the single arithmetic step separating `Kakeya.VeryNotSticky.coarseVolumeLower`, whose
gain is the smaller `δ^{2η+ν/90}`, from `Kakeya.VeryNotSticky.aScaleVolume`, which is stated at
the gain `δ^{ν/9}` that `Kakeya.VeryNotSticky.AScaleData` asks for. Stated over `ℝ≥0∞` with
`d` for `δ`, so that it applies to the coerced scale without a cast. -/
theorem aScaleExponentBudget {d : ENNReal} (hd1 : d ≤ 1) {η ν : ℝ} (hη : 0 < η)
    (hνη : 90 * η ≤ ν) :
    2 * η + ν / 90 ≤ ν / 30 ∧ ν / 30 ≤ ν / 9 ∧ d ^ (ν / 9) ≤ d ^ (2 * η + ν / 90) := by
  have hν : 0 < ν := by linarith
  have h1 : 2 * η + ν / 90 ≤ ν / 30 := by linarith
  have h2 : ν / 30 ≤ ν / 9 := by linarith
  exact ⟨h1, h2, ENNReal.rpow_le_rpow_of_exponent_ge hd1 (le_trans h1 h2)⟩

namespace VeryNotSticky

set_option linter.unusedVariables false in
/-- **Coarse-scale mass bound from the Katz–Tao estimate** (blueprint
`lem:ml2coarseMassBound`).

`δ^{2η} |𝕋_a| |T_a| ≤ δ^{-ν/90} Δ_max(𝕋_a)^{1-β} |𝕋_a|^β |U(𝕋_a, Y_{𝕋_a})|`.

The density exponent is `2η`, not `η`, because that is what the field
`Kakeya.VeryNotSticky.lam_ge` supplies: see its docstring for why `δ^η` there is refuted by
the aggregate fullness binder of `Kakeya.VeryNotSticky.exists_setup_caseSideData`. The extra
`η` is free downstream — `Kakeya.VeryNotSticky.coarseVolumeLower_right` was discarding exactly
one spare `δ^η` — so `Kakeya.VeryNotSticky.coarseVolumeLower` and
`Kakeya.VeryNotSticky.aScaleVolume` keep their statements verbatim.

Two steps. The Katz–Tao estimate at the coarse family gives
`μ(𝕋_a, Y_{𝕋_a}) ≤ a^{-ν/90} Δ_max(𝕋_a)^{1-β} |𝕋_a|^β ≤ δ^{-ν/90} …`, the second step by
`δ ≤ a ≤ 1` and `ν > 0`; and
`μ(𝕋_a, Y_{𝕋_a}) |U(𝕋_a, Y_{𝕋_a})| = ∑_{T_a} |Y_{𝕋_a}(T_a)| ≥ δ^{2η} |𝕋_a| |T_a|` by
`Kakeya.ShadedBody.multiplicity_mul_union` and
`Kakeya.ShadedBody.coe_fullness_mul_le_sum_volume_shade`.

**Why the Katz–Tao conclusion is a hypothesis.** Blueprint `genKKT` is
`Kakeya.KatzTaoEstimate.multiplicity_bound`, which asks for the family it is applied to to be
pairwise essentially distinct. The parent family `𝕋_a` of a
`Tube.UniformTubeSet` is not: the docstring of that bundle records that its
`boundedOverlap` field deliberately *replaces* pairwise essential distinctness, which it says
is unsatisfiable while preserving cardinality. Discharging the hypothesis is therefore not
available at this layer, and it is carried as `hKT`, so that what this lemma owns — the
transport from a multiplicity bound to a mass bound — is proved outright. The threshold and
fullness hypotheses of blueprint `genKKT` (`a < δ₀(ν/90, β)` and
`λ(𝕋_a, Y_{𝕋_a}) ≥ a^{η_genKKT(ν/90, β)}`, the latter needing the unlisted budget
`η ≤ exscal · η_genKKT`) travel with `hKT`. -/
theorem coarseMassBound (cfg : VeryNotSticky) {κ : Type*} {t : Finset κ}
    {V : κ → ShadedBody (EuclideanSpace ℝ (Fin 3))} {Δ volTa : ENNReal} {ν : ℝ}
    (hν : 0 < ν) (ha1 : cfg.a ≤ 1) (hδa : cfg.δ ≤ cfg.a)
    (hfull : (cfg.δ : NNReal) ^ (2 * cfg.η) ≤ ShadedBody.fullness t V)
    (hvolTa : ∀ i ∈ t, volTa ≤ volume (V i).carrier)
    (hKT : ShadedBody.multiplicity t V ≤
      (cfg.a : ENNReal) ^ (-(ν / 90)) * Δ ^ (1 - cfg.β) * (t.card : ENNReal) ^ cfg.β) :
    (cfg.δ : ENNReal) ^ (2 * cfg.η) * ((t.card : ENNReal) * volTa) ≤
      (cfg.δ : ENNReal) ^ (-(ν / 90)) * Δ ^ (1 - cfg.β) * (t.card : ENNReal) ^ cfg.β *
        volume (⋃ i ∈ t, (V i).shade) := by
  have hsum : (cfg.δ : ENNReal) ^ (2 * cfg.η) * ((t.card : ENNReal) * volTa) ≤
      ∑ i ∈ t, volume (V i).shade := by
    simpa [ENNReal.coe_rpow_of_ne_zero cfg.hδ.ne'] using
      (ShadedBody.coe_fullness_mul_le_sum_volume_shade t V (a := cfg.δ ^ (2 * cfg.η))
        (c := volTa) hfull hvolTa)
  have ha_le : (cfg.a : ENNReal) ^ (-(ν / 90)) ≤ (cfg.δ : ENNReal) ^ (-(ν / 90)) := by
    rw [ENNReal.rpow_neg, ENNReal.rpow_neg]
    exact ENNReal.inv_le_inv' (ENNReal.rpow_le_rpow (by exact_mod_cast hδa) (by positivity))
  calc
    (cfg.δ : ENNReal) ^ (2 * cfg.η) * ((t.card : ENNReal) * volTa)
        ≤ ∑ i ∈ t, volume (V i).shade := hsum
    _ = ShadedBody.multiplicity t V * volume (⋃ i ∈ t, (V i).shade) := by
        rw [ShadedBody.sum_shade_eq_multiplicity_mul_union]
    _ ≤ (cfg.a : ENNReal) ^ (-(ν / 90)) * Δ ^ (1 - cfg.β) * (t.card : ENNReal) ^ cfg.β *
          volume (⋃ i ∈ t, (V i).shade) := by
        gcongr
    _ ≤ (cfg.δ : ENNReal) ^ (-(ν / 90)) * Δ ^ (1 - cfg.β) * (t.card : ENNReal) ^ cfg.β *
          volume (⋃ i ∈ t, (V i).shade) := by
        gcongr

/-- The left-hand half of the arithmetic of `Kakeya.VeryNotSticky.coarseVolumeLower`:
everything that touches the tube volume `volT` and the tube count `Ns`.

Multiplying the goal's left side by the nonzero finite factor `c · Na^β · (A²)^{1-β}` lets
`(A²)^{1-β} · A^{2β} = A²` pair with the tube-volume comparison `hTa`, and
`Na^β · Na^{1-β} = Na` pair with the count `hcount`, so that no division and no cancellation
is needed here. -/
theorem coarseVolumeLower_left {d A volT volTa Na Nf Ns c : ENNReal} {C₀ : NNReal}
    {β η ν : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1) (hC₀ : 1 ≤ C₀)
    (hA0 : A ≠ 0) (hAtop : A ≠ ⊤) (hNa0 : Na ≠ 0) (hNatop : Na ≠ ⊤)
    (hTa : c * (A ^ 2 * volT) ≤ d ^ 2 * volTa)
    (hcount : Ns ≤ (C₀ : ENNReal) ^ 2 * (Na * Nf)) :
    c * (Na ^ β * (A ^ 2) ^ (1 - β)) *
        (d ^ (2 * η + ν / 90) * A ^ (2 * β) * volT * Ns ^ (1 - β)) ≤
      (C₀ : ENNReal) ^ 2 *
        (d ^ (2 * η + ν / 90 + 2 * β) * (Na * volTa) * (Nf * d ^ 2) ^ (1 - β)) := by
  let e : ℝ := 1 - β
  have he0 : 0 ≤ e := by
    dsimp [e]
    linarith
  have he1 : e ≤ 1 := by
    dsimp [e]
    linarith
  have h2e0 : 0 ≤ 2 * e := by nlinarith
  have h2b0 : 0 ≤ 2 * β := by nlinarith
  have h2bpos : 0 < 2 * β := by nlinarith
  have hC₀e : (1 : ENNReal) ≤ (C₀ : ENNReal) := ENNReal.one_le_coe_iff.mpr hC₀
  have hC0sq1 : (1 : ENNReal) ≤ (C₀ : ENNReal) ^ 2 := by
    simpa using (pow_le_pow_left₀ (zero_le_one : (0 : ENNReal) ≤ 1) hC₀e 2)
  have hNs : Ns ^ e ≤ (C₀ : ENNReal) ^ 2 * Na ^ e * Nf ^ e := by
    calc
      Ns ^ e ≤ ((C₀ : ENNReal) ^ 2 * (Na * Nf)) ^ e := by
        exact ENNReal.rpow_le_rpow hcount he0
      _ = ((C₀ : ENNReal) ^ 2) ^ e * (Na * Nf) ^ e := by
        rw [ENNReal.mul_rpow_of_nonneg ((C₀ : ENNReal) ^ 2) (Na * Nf) he0]
      _ = ((C₀ : ENNReal) ^ 2) ^ e * (Na ^ e * Nf ^ e) := by
        rw [ENNReal.mul_rpow_of_nonneg Na Nf he0]
      _ = ((C₀ : ENNReal) ^ 2) ^ e * Na ^ e * Nf ^ e := by ring
      _ ≤ (C₀ : ENNReal) ^ 2 * Na ^ e * Nf ^ e := by
        have hpow : ((C₀ : ENNReal) ^ 2) ^ e ≤ (C₀ : ENNReal) ^ 2 :=
          (ENNReal.rpow_le_rpow_of_exponent_le hC0sq1 he1).trans
            (le_of_eq (ENNReal.rpow_one ((C₀ : ENNReal) ^ 2)))
        exact mul_le_mul' (mul_le_mul' hpow le_rfl) le_rfl
  have hA2r : (A : ENNReal) ^ 2 = A ^ (2 : ℝ) := (ENNReal.rpow_natCast A 2).symm
  have hA2e : (A ^ 2) ^ e * A ^ (2 * β) = A ^ 2 := by
    calc
      (A ^ 2) ^ e * A ^ (2 * β) = (A ^ (2 : ℝ)) ^ e * A ^ (2 * β) := by rw [hA2r]
      _ = A ^ ((2 : ℝ) * e) * A ^ (2 * β) := by
            rw [← ENNReal.rpow_mul A (2 : ℝ) e]
      _ = A ^ (((2 : ℝ) * e) + (2 * β)) := by
            rw [← ENNReal.rpow_add ((2 : ℝ) * e) (2 * β) hA0 hAtop]
      _ = A ^ (2 : ℝ) := by
            congr 1
            dsimp [e]
            ring
      _ = A ^ 2 := by exact ENNReal.rpow_natCast A 2
  have hNaβe : Na ^ β * Na ^ e = Na := by
    calc
      Na ^ β * Na ^ e = Na ^ (β + e) := by
            rw [← ENNReal.rpow_add β e hNa0 hNatop]
      _ = Na ^ (1 : ℝ) := by
            congr 1
            dsimp [e]
            ring
      _ = Na := by rw [ENNReal.rpow_one]
  have hd2r : (d : ENNReal) ^ 2 = d ^ (2 : ℝ) := (ENNReal.rpow_natCast d 2).symm
  have hNfpow : Nf ^ e * d ^ 2 = (Nf * d ^ 2) ^ e * d ^ (2 * β) := by
    calc
      Nf ^ e * d ^ 2 = Nf ^ e * d ^ (2 : ℝ) := by rw [hd2r]
      _ = Nf ^ e * d ^ (2 * e + 2 * β) := by
            congr 1
            dsimp [e]
            ring_nf
      _ = Nf ^ e * (d ^ (2 * e) * d ^ (2 * β)) := by
            rw [ENNReal.rpow_add_of_nonneg (2 * e) (2 * β) h2e0 h2b0]
      _ = (Nf ^ e * d ^ (2 * e)) * d ^ (2 * β) := by ring
      _ = (Nf ^ e * (d ^ 2) ^ e) * d ^ (2 * β) := by
            rw [show d ^ (2 * e) = (d ^ 2) ^ e by
              calc
                d ^ (2 * e) = (d ^ (2 : ℝ)) ^ e := by rw [ENNReal.rpow_mul d (2 : ℝ) e]
                _ = (d ^ 2) ^ e := by rw [← hd2r]]
      _ = (Nf * d ^ 2) ^ e * d ^ (2 * β) := by
            rw [@ENNReal.mul_rpow_of_nonneg Nf (d ^ 2) e he0]
  have hmerge : d ^ (2 * η + ν / 90) * d ^ (2 * β) ≤ d ^ (2 * η + ν / 90 + 2 * β) := by
    rcases eq_or_ne d 0 with hd0 | hd0
    · rw [hd0]
      simp [ENNReal.zero_rpow_of_pos h2bpos]
    · rcases eq_or_ne d ⊤ with hdtop | hdtop
      · rw [hdtop]
        by_cases ha : 2 * η + ν / 90 < 0
        · simp [ENNReal.top_rpow_of_neg ha, ENNReal.top_rpow_of_pos h2bpos]
        · have hab : 0 < 2 * η + ν / 90 + 2 * β := by
            nlinarith [le_of_not_gt ha, h2bpos]
          simp [ENNReal.top_rpow_of_pos hab, ENNReal.top_rpow_of_pos h2bpos]
      · rw [← ENNReal.rpow_add (2 * η + ν / 90) (2 * β) hd0 hdtop]
  calc
    c * (Na ^ β * (A ^ 2) ^ e) *
        (d ^ (2 * η + ν / 90) * A ^ (2 * β) * volT * Ns ^ e)
        ≤ c * (Na ^ β * (A ^ 2) ^ e) *
            (d ^ (2 * η + ν / 90) * A ^ (2 * β) * volT *
              ((C₀ : ENNReal) ^ 2 * Na ^ e * Nf ^ e)) := by
          gcongr
    _ = (C₀ : ENNReal) ^ 2 * c * d ^ (2 * η + ν / 90) * volT * Nf ^ e *
          ((A ^ 2) ^ e * A ^ (2 * β)) * (Na ^ β * Na ^ e) := by
          ring
    _ = (C₀ : ENNReal) ^ 2 * c * d ^ (2 * η + ν / 90) * volT * Nf ^ e * A ^ 2 * Na := by
          rw [hA2e, hNaβe]
    _ = (C₀ : ENNReal) ^ 2 * (d ^ (2 * η + ν / 90) * Na * Nf ^ e * (c * (A ^ 2 * volT))) := by
          ring
    _ ≤ (C₀ : ENNReal) ^ 2 * (d ^ (2 * η + ν / 90) * Na * Nf ^ e * (d ^ 2 * volTa)) := by
          gcongr
    _ = (C₀ : ENNReal) ^ 2 * (d ^ (2 * η + ν / 90) * Na * (Nf ^ e * d ^ 2) * volTa) := by
          ring
    _ = (C₀ : ENNReal) ^ 2 * (d ^ (2 * η + ν / 90) * Na *
          ((Nf * d ^ 2) ^ e * d ^ (2 * β)) * volTa) := by
          rw [hNfpow]
    _ = (C₀ : ENNReal) ^ 2 *
          ((d ^ (2 * η + ν / 90) * d ^ (2 * β)) * (Na * volTa) * (Nf * d ^ 2) ^ e) := by
          ring
    _ ≤ (C₀ : ENNReal) ^ 2 *
          (d ^ (2 * η + ν / 90 + 2 * β) * (Na * volTa) * (Nf * d ^ 2) ^ e) := by
          gcongr

set_option linter.unusedVariables false in
/-- The right-hand half of the arithmetic of `Kakeya.VeryNotSticky.coarseVolumeLower`:
everything that touches the mass bound `hmass` and the multiplicity bound `hΔ`.

The factor `(Nf d²)^{1-β}` is exactly what pairs with `Δ^{1-β}` to let `hΔ` be spent.

**`hmass` is read at `d^{2η}`, and the conclusion is unchanged.** The earlier version assumed
`hmass` at `d^η` and then threw away a spare `d^η` at the very last step
(`d^{η+2β} ≤ d^{2β}`), so this is the same lemma with that slack spent instead of discarded:
strictly stronger, since `d^{2η} ≤ d^η` for `d ≤ 1`. It is exactly the room that pays for the
repair of `Kakeya.VeryNotSticky.lam_ge` (see that field's docstring), which lowers the
per-tube density the configuration can promise from `δ^η` to `δ^{2η}`. `hη` is now unused and
is kept only so that call sites need not change. -/
theorem coarseVolumeLower_right {d A volTa volU Δ Na Nf : ENNReal} {CΔ : NNReal} {β η ν : ℝ}
    (hβ0 : 0 < β) (hβ1 : β ≤ 1) (hCΔ : 1 ≤ CΔ) (hd0 : d ≠ 0) (hdtop : d ≠ ⊤) (hd1 : d ≤ 1)
    (hη : 0 ≤ η)
    (hmass : d ^ (2 * η) * (Na * volTa) ≤ d ^ (-(ν / 90)) * Δ ^ (1 - β) * Na ^ β * volU)
    (hΔ : Δ * (Nf * d ^ 2) ≤ (CΔ : ENNReal) * A ^ 2) :
    d ^ (2 * η + ν / 90 + 2 * β) * (Na * volTa) * (Nf * d ^ 2) ^ (1 - β) ≤
      (CΔ : ENNReal) * (d ^ (2 * β) * Na ^ β * volU * (A ^ 2) ^ (1 - β)) := by
  set e : ℝ := 1 - β with he
  have he0 : 0 ≤ e := by rw [he]; linarith
  have he1 : e ≤ 1 := by rw [he]; linarith
  have hS1 : Δ ^ e * (Nf * d ^ 2) ^ e ≤ (CΔ : ENNReal) * (A ^ 2) ^ e := by
    have hΔpow : (Δ * (Nf * d ^ 2)) ^ e ≤ ((CΔ : ENNReal) * A ^ 2) ^ e :=
      ENNReal.rpow_le_rpow hΔ he0
    calc
      Δ ^ e * (Nf * d ^ 2) ^ e = (Δ * (Nf * d ^ 2)) ^ e := by
        rw [← ENNReal.mul_rpow_of_nonneg Δ (Nf * d ^ 2) he0]
      _ ≤ ((CΔ : ENNReal) * A ^ 2) ^ e := hΔpow
      _ = (CΔ : ENNReal) ^ e * (A ^ 2) ^ e := by
        rw [ENNReal.mul_rpow_of_nonneg (CΔ : ENNReal) (A ^ 2) he0]
      _ ≤ (CΔ : ENNReal) * (A ^ 2) ^ e := by
        have hCe : (CΔ : ENNReal) ^ e ≤ (CΔ : ENNReal) := by
          simpa using ENNReal.rpow_le_rpow_of_exponent_le (ENNReal.one_le_coe_iff.mpr hCΔ) he1
        exact mul_le_mul_left hCe ((A ^ 2) ^ e)
  have hpow_split : d ^ (2 * η + ν / 90 + 2 * β) = d ^ (2 * β + ν / 90) * d ^ (2 * η) := by
    rw [show 2 * η + ν / 90 + 2 * β = (2 * β + ν / 90) + 2 * η by ring]
    exact ENNReal.rpow_add (2 * β + ν / 90) (2 * η) hd0 hdtop
  have hcomb : d ^ (2 * β + ν / 90) * d ^ (-(ν / 90)) = d ^ (2 * β) := by
    rw [← ENNReal.rpow_add (2 * β + ν / 90) (-(ν / 90)) hd0 hdtop,
      show (2 * β + ν / 90) + (-(ν / 90)) = 2 * β by ring]
  calc
    d ^ (2 * η + ν / 90 + 2 * β) * (Na * volTa) * (Nf * d ^ 2) ^ e
        = d ^ (2 * β + ν / 90) * (d ^ (2 * η) * (Na * volTa)) * (Nf * d ^ 2) ^ e := by
          rw [hpow_split]
          ring
    _ ≤ d ^ (2 * β + ν / 90) * (d ^ (-(ν / 90)) * Δ ^ e * Na ^ β * volU) *
          (Nf * d ^ 2) ^ e := by
          exact mul_le_mul_left (mul_le_mul' le_rfl hmass) ((Nf * d ^ 2) ^ e)
    _ = (Δ ^ e * (Nf * d ^ 2) ^ e) * (d ^ (2 * β) * Na ^ β * volU) := by
          calc
            d ^ (2 * β + ν / 90) * (d ^ (-(ν / 90)) * Δ ^ e * Na ^ β * volU) *
                  (Nf * d ^ 2) ^ e
                = (d ^ (2 * β + ν / 90) * d ^ (-(ν / 90))) *
                    (Δ ^ e * Na ^ β * volU * (Nf * d ^ 2) ^ e) := by
                  ring
            _ = (Δ ^ e * (Nf * d ^ 2) ^ e) * (d ^ (2 * β) * Na ^ β * volU) := by
                  rw [hcomb]
                  ring
    _ ≤ ((CΔ : ENNReal) * (A ^ 2) ^ e) * (d ^ (2 * β) * Na ^ β * volU) := by
          exact mul_le_mul_left hS1 (d ^ (2 * β) * Na ^ β * volU)
    _ = (CΔ : ENNReal) * (d ^ (2 * β) * Na ^ β * volU * (A ^ 2) ^ e) := by
          ring

set_option linter.unusedVariables false in
/-- **Lower bound for the volume of the coarse union** (blueprint
`lem:ml2coarseVolumeLower`).

`δ^{2η+ν/90} a^{2β} |T| |𝕋|^{1-β} ≤ C_{lem:ml2aScaleVolume} |U(𝕋_a, Y_{𝕋_a})| δ^{2β}`, the
division-free form of `δ^{2η+ν/90} (a/δ)^{2β} |T| |𝕋|^{1-β} ≤ C |U(𝕋_a, Y_{𝕋_a})|`.

Stated over `ℝ≥0∞` with its four inputs as hypotheses, so that the arithmetic is isolated
from the geometry: `hmass` is `Kakeya.VeryNotSticky.coarseMassBound`, `hΔ` is
`Kakeya.VeryNotSticky.maxDensity_activeTubeNodes_le` in the form `Δ Nf d^η d² ≤ CΔ A²`,
`hTa` is the first half of `Kakeya.volume_tube_ratio`, and `hcount` is the first half of
`Kakeya.VeryNotSticky.card_le_card_activeTubeNodes_mul`. Read `d = δ`, `A = a`,
`Na = |𝕋_a|`, `Nf = |𝕋[T_a]|`, `Ns = |𝕋|`, `volT = |T|`, `volTa = |T_a|` and
`volU = |U(𝕋_a, Y_{𝕋_a})|`.

Multiplying `hmass` by `(Nf d²)^{1-β}` and feeding in `hΔ` raised to the power `1-β`
cancels the `Δ^{1-β}`; `hTa` then replaces `d² volTa` by `c A² volT`, cancelling `(A²)^{1-β}`
against `A²` leaves `A^{2β}`, cancelling `Na^β` against `Na Nf^{1-β}` leaves `(Na Nf)^{1-β}`,
and `hcount` replaces that by `C₀^{-2} Ns^{1-β}`. What comes out carries `δ^{2η}` on the left
and a spare `δ^{ν/90}` on the right, which is why the gain recorded in the blueprint is the
smaller `δ^{2η+ν/90}`.

`hmass` is read at `δ^{2η}` rather than `δ^η` — the exponent
`Kakeya.VeryNotSticky.coarseMassBound` now delivers after the repair of
`Kakeya.VeryNotSticky.lam_ge` — and **the conclusion is unchanged**: the earlier proof spent
`δ^η` of the left-hand exponent on `hmass` and discarded the other `δ^η` inside
`Kakeya.VeryNotSticky.coarseVolumeLower_right`. So nothing downstream of here moves: neither
`Kakeya.VeryNotSticky.aScaleVolume`, nor `Kakeya.aScaleExponentBudget`, nor
`Kakeya.VeryNotSticky.exists_aScaleData`.

The three cardinality side conditions `Na ≠ 0`, `Na ≠ ⊤`, `Nf ≠ ⊤` are not decoration: at
`Na = ⊤` the hypothesis `hcount` bounds `Ns` by `⊤` and says nothing, while `hmass` becomes
`⊤ ≤ ⊤`, so the conclusion — whose left side still carries `Ns^{1-β}` — is refutable (take
`β = 1/2`, `d = A = 1/2`, `Ns = 10^{10}`, `volU = volTa = Nf = 1`, `volT = 1/100`,
`Δ = 1/10`). At `Na = 0` and `β = 1` the same happens with `volU = 0` and `volT > 0`. In the
intended application `Na = |𝕋_a|` and `Nf = |𝕋[T_a]|` are `Nat.cast`s and `𝕋_a` is nonempty,
so all three are free. -/
theorem coarseVolumeLower {d A volT volTa volU Δ Na Nf Ns : ENNReal} {C₀ D₀ : NNReal}
    {ν ηc : ℝ}
    (cfg : VeryNotSticky) (hβ1 : cfg.β ≤ 1) (hν : 0 ≤ ν) (hC₀ : 1 ≤ C₀) (hD₀ : 1 ≤ D₀)
    (hd0 : d ≠ 0) (hdtop : d ≠ ⊤) (hd1 : d ≤ 1) (hA0 : A ≠ 0) (hAtop : A ≠ ⊤)
    (hNa0 : Na ≠ 0) (hNatop : Na ≠ ⊤) (hNftop : Nf ≠ ⊤)
    (hηc : 0 ≤ ηc)
    (hmass : d ^ (2 * ηc) * (Na * volTa) ≤
      d ^ (-(ν / 90)) * Δ ^ (1 - cfg.β) * Na ^ cfg.β * volU)
    (hΔ : Δ * (Nf * d ^ 2) ≤ (deltamaxScaleAConstant C₀ D₀ : ENNReal) * A ^ 2)
    (hTa : (tubeVolumeRatioConstant 3 : ENNReal) * (A ^ 2 * volT) ≤ d ^ 2 * volTa)
    (hcount : Ns ≤ (C₀ : ENNReal) ^ 2 * (Na * Nf)) :
    d ^ (2 * ηc + ν / 90) * A ^ (2 * cfg.β) * volT * Ns ^ (1 - cfg.β) ≤
      (aScaleVolumeConstant C₀ D₀ : ENNReal) * volU * d ^ (2 * cfg.β) := by
  set β : ℝ := cfg.β
  set η : ℝ := ηc
  set e : ℝ := 1 - β
  let c : ENNReal := (tubeVolumeRatioConstant 3 : ENNReal)
  let CΔ : ENNReal := (deltamaxScaleAConstant C₀ D₀ : ENNReal)
  let Cv : ENNReal := (aScaleVolumeConstant C₀ D₀ : ENNReal)
  let K : ENNReal := c * (Na ^ β * (A ^ 2) ^ e)
  have hc0 : c ≠ 0 := by
    dsimp [c]
    exact ENNReal.coe_ne_zero.mpr (tubeVolumeRatioConstant_pos 3).ne'
  have hctop : c ≠ ⊤ := by
    dsimp [c]
    exact ENNReal.coe_ne_top
  have hNaβ0 : Na ^ β ≠ 0 := by simp [hNa0, hNatop]
  have hNaβtop : Na ^ β ≠ ⊤ := ENNReal.rpow_ne_top_of_ne_zero hNa0 hNatop
  have hA2_0 : A ^ 2 ≠ 0 := pow_ne_zero 2 hA0
  have hA2_top : A ^ 2 ≠ ⊤ := ENNReal.pow_ne_top hAtop
  have hA2e0 : (A ^ 2) ^ e ≠ 0 := by simp [hA2_0, hA2_top]
  have hA2etop : (A ^ 2) ^ e ≠ ⊤ := ENNReal.rpow_ne_top_of_ne_zero hA2_0 hA2_top
  have hNaA0 : Na ^ β * (A ^ 2) ^ e ≠ 0 := mul_ne_zero hNaβ0 hA2e0
  have hNaAtop : Na ^ β * (A ^ 2) ^ e ≠ ⊤ := ENNReal.mul_ne_top hNaβtop hA2etop
  have hK0 : K ≠ 0 := by
    dsimp [K]
    exact mul_ne_zero hc0 hNaA0
  have hKtop : K ≠ ⊤ := by
    dsimp [K]
    exact ENNReal.mul_ne_top hctop hNaAtop
  have hnn : aScaleVolumeConstant C₀ D₀ * tubeVolumeRatioConstant 3 =
      C₀ ^ 2 * deltamaxScaleAConstant C₀ D₀ := by
    exact aScaleVolumeConstant_mul_tubeVolumeRatioConstant C₀ D₀
  have hCv : (C₀ : ENNReal) ^ 2 * CΔ = Cv * c := by
    dsimp [CΔ, Cv, c]
    exact_mod_cast hnn.symm
  have hB : d ^ (2 * η + ν / 90 + 2 * β) * (Na * volTa) * (Nf * d ^ 2) ^ e ≤
      (deltamaxScaleAConstant C₀ D₀ : ENNReal) *
        (d ^ (2 * β) * Na ^ β * volU * (A ^ 2) ^ e) := by
    exact coarseVolumeLower_right cfg.hβ hβ1 (one_le_deltamaxScaleAConstant hC₀ hD₀)
      hd0 hdtop hd1 (hηc) hmass hΔ
  have hmain : K * (d ^ (2 * η + ν / 90) * A ^ (2 * β) * volT * Ns ^ e) ≤
      K * (Cv * volU * d ^ (2 * β)) := by
    calc
      K * (d ^ (2 * η + ν / 90) * A ^ (2 * β) * volT * Ns ^ e)
          ≤ (C₀ : ENNReal) ^ 2 *
              (d ^ (2 * η + ν / 90 + 2 * β) * (Na * volTa) * (Nf * d ^ 2) ^ e) := by
            exact coarseVolumeLower_left cfg.hβ hβ1 hC₀ hA0 hAtop hNa0 hNatop hTa hcount
      _ ≤ (C₀ : ENNReal) ^ 2 *
            (CΔ * (d ^ (2 * β) * Na ^ β * volU * (A ^ 2) ^ e)) := by
            exact mul_le_mul_right hB ((C₀ : ENNReal) ^ 2)
      _ = K * (Cv * volU * d ^ (2 * β)) := by
            rw [← mul_assoc, hCv]
            dsimp [K]
            ring
  exact (ENNReal.mul_le_mul_iff_left hK0 hKtop).mp (by simpa only [mul_comm] using hmain)

/-- **Scale-`a` estimate: volume of the coarse union** (blueprint `lem:ml2aScaleVolume`).

`δ^{ν/9} a^{2β} ∑_{T ∈ 𝕋} |T| ≤ C_{lem:ml2aScaleVolume} |U(𝕋_a, Y_{𝕋_a})| δ^{2β} |𝕋|^β`,
which is estimate (ii) of `Kakeya.VeryNotSticky.AScaleData` at the radius `a`.

It is the rearrangement of `Kakeya.VeryNotSticky.coarseVolumeLower` announced in the blueprint,
and it performs exactly two steps. The gain is weakened from `δ^{2η+ν/90}` to `δ^{ν/9}` by
`Kakeya.aScaleExponentBudget`, which is where the budget `ν ≥ 90 η` is spent and the only place
it is used. And both sides are multiplied by `|𝕋|^β`, which turns the factor `|𝕋|^{1-β}` of the
coarse bound into `|𝕋|`, hence — the tubes having the common volume `|T|`, the hypothesis
`hS` — into the sum `∑_T |T|`, while the right-hand side acquires the `|𝕋|^β` that estimate
(ii) carries.

The hypotheses are those of `Kakeya.VeryNotSticky.coarseVolumeLower` together with `hνη`, the
tube count `hS`, and the two side conditions `Ns ≠ 0`, `Ns ≠ ⊤` that the identity
`|𝕋|^{1-β} |𝕋|^β = |𝕋|` needs; `0 < ν` is not assumed, being a consequence of `hνη` and
`cfg.hη`. Read `d = δ`, `A = a`, `Na = |𝕋_a|`, `Nf = |𝕋[T_a]|`, `Ns = |𝕋|`, `volT = |T|`,
`volTa = |T_a|`, `volU = |U(𝕋_a, Y_{𝕋_a})|` and `S = ∑_T |T|`. -/
theorem aScaleVolume {d A volT volTa volU Δ Na Nf Ns S : ENNReal} {C₀ D₀ : NNReal} {ν ηc : ℝ}
    (cfg : VeryNotSticky) (hβ1 : cfg.β ≤ 1) (hνη : 90 * cfg.η ≤ ν) (hC₀ : 1 ≤ C₀) (hD₀ : 1 ≤ D₀)
    (hd0 : d ≠ 0) (hdtop : d ≠ ⊤) (hd1 : d ≤ 1) (hA0 : A ≠ 0) (hAtop : A ≠ ⊤)
    (hNa0 : Na ≠ 0) (hNatop : Na ≠ ⊤) (hNftop : Nf ≠ ⊤)
    (hNs0 : Ns ≠ 0) (hNstop : Ns ≠ ⊤) (hS : S = volT * Ns)
    (hbud : d ^ (ν / 9) ≤ d ^ (2 * ηc + ν / 90))
    (hηc : 0 ≤ ηc)
    (hmass : d ^ (2 * ηc) * (Na * volTa) ≤
      d ^ (-(ν / 90)) * Δ ^ (1 - cfg.β) * Na ^ cfg.β * volU)
    (hΔ : Δ * (Nf * d ^ 2) ≤ (deltamaxScaleAConstant C₀ D₀ : ENNReal) * A ^ 2)
    (hTa : (tubeVolumeRatioConstant 3 : ENNReal) * (A ^ 2 * volT) ≤ d ^ 2 * volTa)
    (hcount : Ns ≤ (C₀ : ENNReal) ^ 2 * (Na * Nf)) :
    d ^ (ν / 9) * A ^ (2 * cfg.β) * S ≤
      (aScaleVolumeConstant C₀ D₀ : ENNReal) * volU * d ^ (2 * cfg.β) * Ns ^ cfg.β := by
  have hν : 0 ≤ ν := by
    nlinarith [hνη, cfg.hη]
  have hbudget : d ^ (ν / 9) ≤ d ^ (2 * ηc + ν / 90) := hbud
  have hcvl := coarseVolumeLower (cfg := cfg) (hβ1 := hβ1) (hν := hν) (hC₀ := hC₀)
    (hD₀ := hD₀) (hd0 := hd0) (hdtop := hdtop) (hd1 := hd1) (hA0 := hA0) (hAtop := hAtop)
    (hNa0 := hNa0) (hNatop := hNatop) (hNftop := hNftop) (hηc := hηc) (hmass := hmass)
    (hΔ := hΔ) (hTa := hTa) (hcount := hcount)
  have hNs1 : Ns ^ (1 - cfg.β) * Ns ^ cfg.β = Ns := by
    calc
      Ns ^ (1 - cfg.β) * Ns ^ cfg.β = Ns ^ ((1 - cfg.β) + cfg.β) := by
        rw [← ENNReal.rpow_add (1 - cfg.β) cfg.β hNs0 hNstop]
      _ = Ns ^ (1 : ℝ) := by
        congr 1
        ring
      _ = Ns := by rw [ENNReal.rpow_one]
  have hleft : d ^ (2 * ηc + ν / 90) * A ^ (2 * cfg.β) * volT * Ns ^ (1 - cfg.β) *
        Ns ^ cfg.β = d ^ (2 * ηc + ν / 90) * A ^ (2 * cfg.β) * S := by
    calc
      d ^ (2 * ηc + ν / 90) * A ^ (2 * cfg.β) * volT * Ns ^ (1 - cfg.β) * Ns ^ cfg.β
          = d ^ (2 * ηc + ν / 90) * A ^ (2 * cfg.β) * volT *
              (Ns ^ (1 - cfg.β) * Ns ^ cfg.β) := by
            ring
      _ = d ^ (2 * ηc + ν / 90) * A ^ (2 * cfg.β) * volT * Ns := by
            rw [hNs1]
      _ = d ^ (2 * ηc + ν / 90) * A ^ (2 * cfg.β) * S := by
            rw [hS]
            ring
  calc
    d ^ (ν / 9) * A ^ (2 * cfg.β) * S
        ≤ d ^ (2 * ηc + ν / 90) * A ^ (2 * cfg.β) * S := by
          exact mul_le_mul' (mul_le_mul' hbudget le_rfl) le_rfl
    _ = d ^ (2 * ηc + ν / 90) * A ^ (2 * cfg.β) * volT * Ns ^ (1 - cfg.β) *
          Ns ^ cfg.β := hleft.symm
    _ ≤ (aScaleVolumeConstant C₀ D₀ : ENNReal) * volU * d ^ (2 * cfg.β) * Ns ^ cfg.β := by
          exact mul_le_mul' hcvl le_rfl

end VeryNotSticky

/-! ### The ball-scale estimate -/

/-- **Scale-`a` estimate: transfer to an `a`-ball** (blueprint `lem:ml2aScaleBall`).

For every ball `B_r` meeting the fine shaded union `U(𝕋, Y')`,
`δ^{ν/9} |U(𝕋_a, Y_{𝕋_a})| |U(𝕋, Y') ∩ B_r| ≤ C_{lem:ml2aScaleBall}(Cb) |U(𝕋, Y')| |B_r|`
with `C_{lem:ml2aScaleBall}(Cb) = Kakeya.aScaleBallConstant Cb = 5^3 Cb`.

`Kakeya.exists_mem_volume_inter_ball_recentre` produces `x ∈ U(𝕋, Y')` with
`|U(𝕋, Y') ∩ B_r| ≤ 5^3 |U(𝕋, Y') ∩ B(x, r)|` and `|B(x, r)| = |B_r|`;
`Kakeya.ShadedBody.mem_iUnion_outerShade_of_mem_iUnion_innerShade` puts `x` in
`U(𝕋_a, Y_{𝕋_a})`, so the hypothesis `hvol` — blueprint `boundVolumeAcrossTwoScales`, the
ninth conclusion of `Kakeya.ShadedBody.shadingMultiplicityEstimateForRhoTubes` — applies at
`x`.

The constant is independent of the ball precisely because `Cb` is: `hvol` is asserted for all
admissible centres with one constant. That uniformity is what lets the constant be fixed
before the ball supplied by the density hypothesis is chosen, and so avoids a circularity in
blueprint `lem:ml2goalfromdens`.

**The factor `δ^{ν/9}` sits inside the hypothesis, not outside the conclusion.** It used to be
carried only because `Kakeya.VeryNotSticky.AScaleData` asks for it, and was spent immediately
against `δ ≤ 1`; that discarded a surplus the producer of `hvol` needs. The producer is
`Kakeya.VeryNotSticky.coarseBallEstimate_of_gridScale`, which obtains the estimate from the
section-5 interface at a *grid* radius `ρ ≥ r` and must pay the ratio of ball volumes
`(ρ/r)³` to move it to the radius `r`; that ratio is one grid step cubed, hence at most
`δ^{-3/⌈log log 1/δ⌉} ≤ δ^{-3η} ≤ δ^{-ν/9}` under `Kakeya.VeryNotSticky.gridFine` and
`ν ≥ 90 η`. Leaving the gain in the hypothesis is what makes that payment possible; the
present lemma simply carries it through, and is otherwise unchanged. The hypothesis with the
factor is weaker than the hypothesis without it, so nothing that could supply the old form
fails to supply this one.

`0 < Cb` is not cosmetic: at `Cb = 0` the hypothesis reads `⊤ · … ≤ |U(𝕋, Y')|` and the
conclusion `… ≤ 0`, and the two do not combine. The intended value,
`Kakeya.ShadedBody.shadingMultiplicityEstimateForRhoTubes.C = 1`, satisfies it, as does every
`C ≥ 1` the blueprint contemplates. -/
theorem aScaleBall {ι κ : Type*}
    (G : ShadedBody.ShadedFactorFamily (EuclideanSpace ℝ (Fin 3)) ι κ) {Cb : NNReal}
    (hCb : 0 < Cb) {r : ℝ} (hr : 0 < r) {δ : NNReal} {ν : ℝ}
    (hvol : ∀ x ∈ ⋃ j ∈ G.outerSet, (G.outerBody j).shade,
      (δ : ENNReal) ^ (ν / 9) *
          ((Cb : ENNReal)⁻¹ * volume (⋃ j ∈ G.outerSet, (G.outerBody j).shade) *
            (volume ((⋃ i ∈ G.innerSet, (G.innerBody i).shade) ∩ ball x r) /
              volume (ball x r))) ≤
        volume (⋃ i ∈ G.innerSet, (G.innerBody i).shade))
    (x₀ : EuclideanSpace ℝ (Fin 3))
    (hne : ((⋃ i ∈ G.innerSet, (G.innerBody i).shade) ∩ ball x₀ r).Nonempty) :
    (δ : ENNReal) ^ (ν / 9) * volume (⋃ j ∈ G.outerSet, (G.outerBody j).shade) *
        volume ((⋃ i ∈ G.innerSet, (G.innerBody i).shade) ∩ ball x₀ r) ≤
      (aScaleBallConstant Cb : ENNReal) *
        volume (⋃ i ∈ G.innerSet, (G.innerBody i).shade) * volume (ball x₀ r) := by
  classical
  let U : Set (EuclideanSpace ℝ (Fin 3)) := ⋃ i ∈ G.innerSet, (G.innerBody i).shade
  let W : ENNReal := volume (⋃ j ∈ G.outerSet, (G.outerBody j).shade)
  let M : ENNReal := volume (⋃ i ∈ G.innerSet, (G.innerBody i).shade)
  let A : ENNReal := (δ : ENNReal) ^ (ν / 9)
  have hfin : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := finrank_euclideanSpace_fin
  have hxne : (U ∩ ball x₀ r).Nonempty := by simpa [U] using hne
  rcases exists_mem_volume_inter_ball_recentre (S := U) hr hxne with ⟨x, hxU, hrec, hball⟩
  have hrecU : volume (U ∩ ball x₀ r) ≤
      (separatedNetCoverConstant 3 : ENNReal) * volume (U ∩ ball x r) := by
    simpa [hfin] using hrec
  have hxO : x ∈ ⋃ j ∈ G.outerSet, (G.outerBody j).shade :=
    ShadedBody.mem_iUnion_outerShade_of_mem_iUnion_innerShade G hxU
  have hvolx : A * ((Cb : ENNReal)⁻¹ * W * (volume (U ∩ ball x r) / volume (ball x r))) ≤
      M := by
    simpa [A, U, W, M] using hvol x hxO
  have hCbpos : (0 : ENNReal) < (Cb : ENNReal) := by exact_mod_cast hCb
  have hCb0 : (Cb : ENNReal) ≠ 0 := hCbpos.ne'
  have hCbTop : (Cb : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hBpos : (0 : ENNReal) < volume (ball x r) := Metric.measure_ball_pos volume x hr
  have hB0 : volume (ball x r) ≠ 0 := hBpos.ne'
  have hBtop : volume (ball x r) ≠ ⊤ := ne_of_lt (MeasureTheory.measure_ball_lt_top)
  have hq : A * ((Cb : ENNReal)⁻¹ * W * volume (U ∩ ball x r)) ≤
      M * volume (ball x r) := by
    have hdiv : volume (U ∩ ball x r) =
        (volume (U ∩ ball x r) / volume (ball x r)) * volume (ball x r) := by
      exact (ENNReal.div_mul_cancel hB0 hBtop).symm
    calc
      A * ((Cb : ENNReal)⁻¹ * W * volume (U ∩ ball x r))
          = (A * ((Cb : ENNReal)⁻¹ * W * (volume (U ∩ ball x r) / volume (ball x r)))) *
              volume (ball x r) := by
            conv_lhs => rw [hdiv]
            ring
      _ ≤ M * volume (ball x r) := by
            exact mul_le_mul' hvolx le_rfl
  have hkey : A * W * volume (U ∩ ball x r) ≤ (Cb : ENNReal) * M * volume (ball x r) := by
    have hcinv : (Cb : ENNReal) * (Cb : ENNReal)⁻¹ = (1 : ENNReal) := by
      simpa [mul_comm] using (ENNReal.mul_inv_cancel hCb0 hCbTop)
    calc
      A * W * volume (U ∩ ball x r)
          = (Cb : ENNReal) * (A * (((Cb : ENNReal)⁻¹ * W) * volume (U ∩ ball x r))) := by
            calc
              A * W * volume (U ∩ ball x r)
                  = (1 : ENNReal) * (A * W * volume (U ∩ ball x r)) := by
                    rw [one_mul]
              _ = ((Cb : ENNReal) * (Cb : ENNReal)⁻¹) * (A * W * volume (U ∩ ball x r)) := by
                    rw [← hcinv]
              _ = (Cb : ENNReal) * (A * (((Cb : ENNReal)⁻¹ * W) * volume (U ∩ ball x r))) := by
                    ring
      _ ≤ (Cb : ENNReal) * M * volume (ball x r) := by
            calc
              (Cb : ENNReal) * (A * (((Cb : ENNReal)⁻¹ * W) * volume (U ∩ ball x r)))
                  ≤ (Cb : ENNReal) * (M * volume (ball x r)) := by
                    exact mul_le_mul_right hq (Cb : ENNReal)
              _ = (Cb : ENNReal) * M * volume (ball x r) := by
                    ring
  have hsepc : (separatedNetCoverConstant 3 : ENNReal) =
      ((separatedNetCoverConstant 3 : NNReal) : ENNReal) := by
    norm_num [separatedNetCoverConstant]
  calc
    A * W * volume (U ∩ ball x₀ r)
        ≤ A * W * ((separatedNetCoverConstant 3 : ENNReal) * volume (U ∩ ball x r)) := by
          gcongr
    _ = (separatedNetCoverConstant 3 : ENNReal) * (A * W * volume (U ∩ ball x r)) := by
          ring
    _ ≤ (separatedNetCoverConstant 3 : ENNReal) * ((Cb : ENNReal) * M * volume (ball x r)) := by
          gcongr
    _ = (separatedNetCoverConstant 3 : ENNReal) * ((Cb : ENNReal) * M * volume (ball x₀ r)) := by
          rw [hball]
    _ = (aScaleBallConstant Cb : ENNReal) * M * volume (ball x₀ r) := by
          rw [aScaleBallConstant]
          simp only [EuclideanSpace.volume_ball_fin_three]
          rw [ENNReal.coe_mul]
          rw [hsepc]
          ring

end Kakeya
