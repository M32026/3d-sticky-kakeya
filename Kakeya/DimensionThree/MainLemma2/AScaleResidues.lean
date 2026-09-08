/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.AScaleRounding
public import Kakeya.DimensionThree.MainLemma2.NonSlabFibre
public import Kakeya.Factoring.RhoTubesUndilated
public import Kakeya.Factoring.RhoTubesSection9
public import Kakeya.MultiScaleFac.UniformBridgeKT
public import Kakeya.PartialEstimatesWindowed
public import Kakeya.DimensionThree.MainLemma2.KTWindowThresholds

/-!
# What Sections 3 and 5 owe the scale-`r` layer of Main Lemma 2

Two statements, each as a proposition, each owned by another section of the
development, and each stated in a form that section can actually deliver. Together with the
proved material of `Kakeya.DimensionThree.MainLemma2.AScaleRounding` they are exactly what
`Kakeya.DimensionThree.MainLemma2.AScaleInterface` consumes.

* `Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid` — Section 5, blueprint
  `shadingMultiplicityEstimateForRhoTubes` at `ρ` a scale of the multiscale grid. The Lean
  statement of that lemma cannot be applied here, and the obstruction is *not* the scale: it is
  the hypothesis `hed`, pairwise essential distinctness of the outer family, which the
  docstring of `Tube.UniformTubeSet.boundedOverlap` records as unsatisfiable for
  the nodes of a hierarchy while preserving cardinality. The version below replaces `hed` by
  taking the outer family to *be* the node family of the hierarchy, which carries bounded
  overlap instead.
* `Kakeya.VeryNotSticky.coarseKatzTaoBound` — Section 3, blueprint `genKKT`
  (`Kakeya.KatzTaoEstimate.multiplicity_bound`) applied to the coarse family, with the same
  substitution of bounded overlap for essential distinctness, and with the two thresholds of
  `genKKT` absorbed.

**Both are stated at the configuration's own hierarchy, not at an arbitrary one.** Each takes
the uniform bundle at the grid length `⌈log log 1/δ⌉` and the branching/overlap constant
`cfg.C₀` that Configuration `hyp:ml2setup` carries, and the first takes the *shaded* bundle
`Kakeya.ShadedTube.ShadedUniformTubeSet`, which is what the field
`Kakeya.VeryNotSticky.uniform` supplies and what blueprint
`shadingMultiplicityEstimateForRhoTubes` asks for. (There is **no** Lean declaration of that
name: only the placeholder constant
`Kakeya.ShadedBody.shadingMultiplicityEstimateForRhoTubes.C` exists, and the proved Lean forms
of GWZ Lemma 5.11 are `Kakeya.ShadedBody.shadingMultiplicityEstimateForRhoTubesDilate` and its
undilated specialisations.) Earlier versions
quantified both the grid length `N` and the overlap constant `C₀` universally and handed
Section 5 only the tube-level bundle. That was wrong twice over: the tube-level bundle is not
enough to invoke Section 5 at all, and a `C₀` quantified before the statement makes each
estimate an assertion, with a `C₀`-free constant, about hierarchies of arbitrarily bad
overlap — while the substitution of bounded overlap for essential distinctness costs exactly a
factor `C₀`. At the configuration's own `C₀` that loss is sub-polynomial,
`Kakeya.VeryNotSticky.coe_C₀_le_rpow_neg_eta`, and each docstring below says where it is paid
for: out of the gain in `Kakeya.VeryNotSticky.coarseKatzTaoBound`, and out of the factor
`δ^{cfg.η}` now carried on the small side of the ball conjunct of
`Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid`. Neither statement absorbs a loss it has
no room for.

Section 5 also asks its inner family for two-sided per-tube shading densities, and those are
not a consequence of the aggregate `cfg.fullness_ge`, a ratio of sums. They are carried as the
configuration fields `Kakeya.VeryNotSticky.lam`, `Kakeya.VeryNotSticky.Cd`,
`Kakeya.VeryNotSticky.shading_lb`, `Kakeya.VeryNotSticky.shading_ub` and
`Kakeya.VeryNotSticky.lam_ge`, so that the residue below assumes nothing it does not say.
-/

@[expose] public section

namespace Kakeya.VeryNotSticky

open MeasureTheory Metric Set ShadedBody

universe u

/-! ## What Section 5 already delivers at this configuration

The three declarations below are the *proved* part of the Section-5 residue: the node factor
family of the configuration at a grid index, and GWZ Lemma 5.11
(`Kakeya.ShadedBody.shadingMultiplicityEstimateForRhoTubesUndilated_lam`) applied to it. They
are what `Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid` below has to be closed *from*,
and the difference between the two is exactly the residue.
-/

/-- **The node factor family of the configuration at grid index `k`.**

Inner layer: the pair `(𝕋, Y)` of Configuration `hyp:ml2setup`. Outer layer: the active node
family `𝕋_ρ` of the hierarchy at `k`, with the node tubes as convex bodies. The parent map is
the hierarchy's own assignment, so `parent_mem` is
`Tube.GridCoverSystem.assign_mem` together with the fact that a node carrying an
assigned member is active, and `inner_le_parent` is the factor-`1` containment
`Tube.GridCoverSystem.le_tube_assign`. -/
noncomputable def nodeFactorFamily (cfg : VeryNotSticky.{u})
    (𝒰 : Tube.UniformTubeSet cfg.s (fun i ↦ (cfg.T i).toTube) (Tube.ssfGridLen cfg.δ) cfg.C₀)
    {k : ℕ} (hk : k ≤ Tube.ssfGridLen cfg.δ) :
    ShadedBody.FactorFamily (EuclideanSpace ℝ (Fin 3)) cfg.ι cfg.ι where
  innerSet := cfg.s
  innerBody := fun i ↦ (cfg.T i).toShadedBody
  outerSet := cfg.activeTubeNodes 𝒰 k
  outerBody := fun j ↦ (𝒰.cover.tube k j).toConvexSpaceBody
  parent := 𝒰.cover.assign k
  parent_mem := by
    classical
    intro i hi
    rw [activeTubeNodes, Finset.mem_filter]
    refine ⟨𝒰.cover.assign_mem k hk i hi, ⟨i, ?_⟩⟩
    simp [tubeFibre, Tube.coverClass, hi]
  inner_le_parent := by
    intro i hi
    simpa using 𝒰.cover.le_tube_assign k hk i hi

/-- The tubes of the configuration have positive volume, so the nondegeneracy hypothesis
`hs0` of `Kakeya.ShadedBody.shadingMultiplicityEstimateForRhoTubesUndilated_lam` is met. -/
theorem sum_volume_carrier_ne_zero (cfg : VeryNotSticky.{u}) :
    ∑ i ∈ cfg.s, volume ((cfg.T i).toShadedBody.carrier) ≠ 0 := by
  have hs : cfg.s.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    have := cfg.tube_count
    rw [h] at this
    simp at this
  obtain ⟨i₀, hi₀⟩ := hs
  have hpos : 0 < volume ((cfg.T i₀).toShadedBody.carrier) := by
    have h := _root_.Tube.le_volume (cfg.T i₀).toTube
    refine lt_of_lt_of_le ?_ (by simpa using h)
    have hc : (0 : ENNReal) < (_root_.Tube.le_volume.c 3 : ENNReal) :=
      ENNReal.coe_pos.mpr (_root_.Tube.le_volume.c_pos _)
    have hδp : (0 : ENNReal) < (cfg.δ : ENNReal) ^ 2 :=
      ENNReal.pow_pos (ENNReal.coe_pos.mpr cfg.hδ) _
    exact ENNReal.mul_pos (ne_of_gt hc) (ne_of_gt hδp)
  intro h
  rw [Finset.sum_eq_zero_iff] at h
  exact absurd (h i₀ hi₀) (ne_of_gt hpos)

/-- **The loss constant Section 5 actually charges** at this configuration: the constant of
`Kakeya.ShadedBody.shadingMultiplicityEstimateForRhoTubesDilate` at the ambient dimension `3`,
the family size `|𝕋|`, the scale `δ` and dilation `1`. It is bounded below by `1`
(`Kakeya.ShadedBody.shadingMultiplicityEstimateForRhoTubesDilate.one_le_C`), and it is *not*
the placeholder `Kakeya.ShadedBody.shadingMultiplicityEstimateForRhoTubes.C = 1` that
`exists_coarseShadedFamilyAtGrid` below is stated with. -/
noncomputable abbrev coarseLoss (cfg : VeryNotSticky.{u}) : NNReal :=
  _root_.ShadedBody.shadingMultiplicityEstimateForRhoTubesDilate.C 3 cfg.s.card cfg.δ 1

/-- **Tripwire: the field `Kakeya.VeryNotSticky.coarseLoss_absorb` is about this quantity.**

The field is stated as `ShadedBody.rhoTubesSection9Loss 3 s.card δ ≤ δ^{-η}`, which is the
same term as `coarseLoss` by definitional unfolding of
`ShadedBody.rhoTubesSection9Loss`. That identification is what lets the residue
`Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid` be restated at the honest loss instead
of at the placeholder numeral `ShadedBody.shadingMultiplicityEstimateForRhoTubes.C = 1`; if
either side ever drifts, this `exact` stops elaborating. -/
theorem coarseLoss_le_rpow_neg_eta (cfg : VeryNotSticky.{u}) :
    (cfg.coarseLoss : ENNReal) ≤ (cfg.δ : ENNReal) ^ (-cfg.η) :=
  cfg.coarseLoss_absorb

/-- **GWZ Lemma 5.11 at the configuration's own hierarchy, on a subfamily of the node family.**

This is `Kakeya.ShadedBody.shadingMultiplicityEstimateForRhoTubesUndilated_lam` applied to
`Kakeya.VeryNotSticky.nodeFactorFamily`, with the two-sided density data read off the fields
`Kakeya.VeryNotSticky.shading_lb`, `Kakeya.VeryNotSticky.Cd` and
`Kakeya.VeryNotSticky.lam`, and the unit-ball hypothesis off
`Kakeya.VeryNotSticky.contained`. It is fully proved.

**It differs from `Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid` below in exactly two
places, and those two differences are the whole of the remaining residue.**

1. *Subfamily, not the full node family.* Here `G.outerSet ⊆ 𝕋_ρ` and correspondingly
   `G.innerSet` is the set of members whose node survives, whereas the residue asks for
   `G.outerSet = 𝕋_ρ` and `G.innerSet = cfg.s` on the nose. Passing to a subfamily is what
   Lemma 5.11 does — it is the pigeonholing that produces the outer shading — so this gap
   cannot be closed by a better proof of the same lemma. Either the residue's two equalities
   weaken to the containments above, and
   `Kakeya.VeryNotSticky.rScaleParentData_of_gridScale` is re-derived through the monotonicity
   of `maxDensity` and of the cardinality, or a genuinely new argument is needed.
2. *The loss constant.* Here the fullness and ball conjuncts carry
   `Kakeya.VeryNotSticky.coarseLoss`, which is `≥ 1` and depends on `|𝕋|` and `δ`; the residue
   carries `Kakeya.ShadedBody.shadingMultiplicityEstimateForRhoTubes.C`, which is the numeral
   `1`. A lossless fullness transfer from the inner family to the coarse family is not what
   Lemma 5.11 proves and is not what GWZ claim: the loss is precisely a multiplicity factor,
   the ratio between `∑_T |Y(T)|` and `|⋃_T Y(T)|`. So the residue is, at present, *stronger*
   than its only available deliverer by that factor. -/
theorem exists_coarseShadedFamilyAtGrid_subfamily (cfg : VeryNotSticky.{u})
    (𝒱 : ShadedTube.ShadedUniformTubeSet cfg.s cfg.T (Tube.ssfGridLen cfg.δ) cfg.C₀)
    {k : ℕ} (hk : k ≤ Tube.ssfGridLen cfg.δ)
    {ρ : NNReal} (hgrid : Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k = ρ)
    (hρ : ρ ∈ Set.Icc cfg.δ 1) :
    ∃ G : ShadedFactorFamily (EuclideanSpace ℝ (Fin 3)) cfg.ι cfg.ι,
      G.outerSet ⊆ cfg.activeTubeNodes 𝒱.tubeUniform k ∧
      G.innerSet = {i ∈ cfg.s | 𝒱.tubeUniform.cover.assign k i ∈ G.outerSet} ∧
      G.parent = 𝒱.tubeUniform.cover.assign k ∧
      (∀ j ∈ G.outerSet, (G.outerBody j).toConvexSpaceBody =
        (𝒱.tubeUniform.cover.tube k j).toConvexSpaceBody) ∧
      (∀ i ∈ cfg.s, (G.innerBody i).toConvexSpaceBody = (cfg.T i).toConvexSpaceBody) ∧
      (cfg.Cd * cfg.coarseLoss)⁻¹ * cfg.lam ≤ ShadedBody.fullness G.outerSet G.outerBody ∧
      (∀ x ∈ ⋃ j ∈ G.outerSet, (G.outerBody j).shade,
        (cfg.coarseLoss : ENNReal)⁻¹ *
            volume (⋃ j ∈ G.outerSet, (G.outerBody j).shade) *
              (volume ((⋃ i ∈ G.innerSet, (G.innerBody i).shade) ∩ ball x (ρ : ℝ)) /
                volume (ball x (ρ : ℝ))) ≤
          volume (⋃ i ∈ G.innerSet, (G.innerBody i).shade)) := by
  classical
  subst hgrid
  let F : ShadedBody.FactorFamily (EuclideanSpace ℝ (Fin 3)) cfg.ι cfg.ι :=
    cfg.nodeFactorFamily 𝒱.tubeUniform hk
  have hFi : F.innerSet = cfg.s := rfl
  have hFp : F.parent = 𝒱.tubeUniform.cover.assign k := rfl
  have hFo : F.outerSet = cfg.activeTubeNodes 𝒱.tubeUniform k := rfl
  have hFb : ∀ i, F.innerBody i = (cfg.T i).toShadedBody := fun _ => rfl
  have hFob : ∀ j, F.outerBody j = (𝒱.tubeUniform.cover.tube k j).toConvexSpaceBody :=
    fun _ => rfl
  have hCd : cfg.Cd ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one cfg.hCd)
  obtain ⟨G, h1, h2, h3, h4, h5, h6, hfull, h8, h9, h10, h11, _h12⟩ :=
    _root_.ShadedBody.shadingMultiplicityEstimateForRhoTubesUndilated_lam
      (E := EuclideanSpace ℝ (Fin 3)) (δ := cfg.δ) (Cd := cfg.Cd) (lam := cfg.lam)
      cfg.hδ hρ hCd F cfg.T (𝒱.tubeUniform.cover.tube k)
      (fun i _ => rfl) (fun j _ => rfl)
      (fun i hi => cfg.contained i hi)
      cfg.sum_volume_carrier_ne_zero
      cfg.shading_lb
  have hfr : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
  have hloss : _root_.ShadedBody.shadingMultiplicityEstimateForRhoTubesDilate.C
      (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) F.innerSet.card cfg.δ 1
      = cfg.coarseLoss := by
    rw [hfr, hFi]
  refine ⟨G, hFo ▸ h1, (by rw [h2]; congr 1), hFp ▸ h3, fun j hj => (hFob _) ▸ h4 j hj,
    fun i hi => by simpa [hFb] using h5 i (hFi ▸ hi), ?_, ?_⟩
  · rw [← hloss]; exact hfull
  · rw [← hloss]; exact h11

/-- **The ball conjunct from the configuration's own local-mass datum.**

Given any shaded factor family whose inner side is the configuration's family on the nose and
whose coarse shaded union lies in the `2ρ`-neighbourhood of the inner shaded union, the ball
conjunct at the gain `δ^η` follows from `Kakeya.VeryNotSticky.coarseLocalMass` and nothing else:
the loss constant appears only through its inverse, on the small side, and
`ShadedBody.one_le_rhoTubesInducedFullnessLoss` disposes of it.

The containment hypothesis is `ShadedBody.iUnion_inducedCoarseShading_subset_cthickening` at the
induced coarse shading, which is what makes the datum — statable with no reference to the
hierarchy — bound a union that does refer to it. -/
theorem coarseBallConjunct_of_coarseLocalMass (cfg : VeryNotSticky.{u})
    (G : ShadedFactorFamily (EuclideanSpace ℝ (Fin 3)) cfg.ι cfg.ι)
    (hinner : G.innerSet = cfg.s)
    (hbody : ∀ i ∈ cfg.s, G.innerBody i = (cfg.T i).toShadedBody)
    {k : ℕ} (hk : k ≤ Tube.ssfGridLen cfg.δ) {ρ : NNReal}
    (hgrid : Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k = ρ)
    (hsub : (⋃ j ∈ G.outerSet, (G.outerBody j).shade)
      ⊆ Metric.cthickening (2 * (ρ : ℝ)) (⋃ i ∈ cfg.s, (cfg.T i).toShadedBody.shade)) :
    ∀ x ∈ ⋃ j ∈ G.outerSet, (G.outerBody j).shade,
      (cfg.δ : ENNReal) ^ cfg.η *
          (((_root_.ShadedBody.rhoTubesInducedFullnessLoss 3 : NNReal) : ENNReal)⁻¹ *
              volume (⋃ j ∈ G.outerSet, (G.outerBody j).shade) *
            (volume ((⋃ i ∈ G.innerSet, (G.innerBody i).shade) ∩ ball x (ρ : ℝ)) /
              volume (ball x (ρ : ℝ)))) ≤
        volume (⋃ i ∈ G.innerSet, (G.innerBody i).shade) := by
  classical
  subst hgrid
  have hunion : (⋃ i ∈ G.innerSet, (G.innerBody i).shade) =
      ⋃ i ∈ cfg.s, (cfg.T i).toShadedBody.shade := by
    rw [hinner]
    exact Set.iUnion₂_congr fun i hi =>
      congrArg (fun b : ShadedBody (EuclideanSpace ℝ (Fin 3)) => b.shade) (hbody i hi)
  intro x _
  rw [hunion]
  have hL1 : (1 : ENNReal)
      ≤ ((_root_.ShadedBody.rhoTubesInducedFullnessLoss 3 : NNReal) : ENNReal) := by
    have h : (1 : NNReal) ≤ _root_.ShadedBody.rhoTubesInducedFullnessLoss 3 :=
      _root_.ShadedBody.one_le_rhoTubesInducedFullnessLoss 3
    exact_mod_cast h
  have hkey : ((_root_.ShadedBody.rhoTubesInducedFullnessLoss 3 : NNReal) : ENNReal)⁻¹ *
      volume (⋃ j ∈ G.outerSet, (G.outerBody j).shade)
      ≤ volume (Metric.cthickening
          (2 * (Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k : ℝ))
          (⋃ i ∈ cfg.s, (cfg.T i).toShadedBody.shade)) := by
    calc ((_root_.ShadedBody.rhoTubesInducedFullnessLoss 3 : NNReal) : ENNReal)⁻¹ *
          volume (⋃ j ∈ G.outerSet, (G.outerBody j).shade)
        ≤ 1 * volume (⋃ j ∈ G.outerSet, (G.outerBody j).shade) := by
          gcongr
          exact ENNReal.inv_le_one.2 hL1
      _ = volume (⋃ j ∈ G.outerSet, (G.outerBody j).shade) := one_mul _
      _ ≤ _ := measure_mono hsub
  exact le_trans (mul_le_mul' le_rfl (mul_le_mul' hkey le_rfl)) (cfg.coarseLocalMass k hk x)

/-- **The coarse shaded family at a grid scale, with the ball estimate** (blueprint
`shadingMultiplicityEstimateForRhoTubes` at `ρ = ρ_k`, whose ninth conclusion is
`boundVolumeAcrossTwoScales`, i.e. blueprint `lowerBoundTTScaleAAndABall`).

At every scale `ρ = δ^{k/N}` of the multiscale grid the node family of the hierarchy carries a
shading `Y_{𝕋_ρ}` for which

* the fully shaded factor family `G` has the pair `(𝕋, Y)` of Configuration `hyp:ml2setup`
  itself as its inner layer;
* its outer layer is the active node family `𝕋_ρ` at the grid index `k`, with the node tubes
  as convex bodies;
* the outer shading is at least as full as the inner density,
  `λ(𝕋_ρ, Y_{𝕋_ρ}) ≥ C⁻¹ lam` with `lam = cfg.lam`;
* and the ball estimate holds, re-centred at every shaded point, with the fixed constant
  `Kakeya.ShadedBody.shadingMultiplicityEstimateForRhoTubes.C` **and a factor `δ^{cfg.η}` on
  its small side**, which is the room the `C₀` of the substitution below is paid out of.

**Owned by Section 5.** This is blueprint `shadingMultiplicityEstimateForRhoTubes` at
`ρ = ρ_k`. Contrary to what this docstring used to say, that lemma is **not** unproved and there
is no Lean declaration by that name: GWZ Lemma 5.11 is
`Kakeya.ShadedBody.shadingMultiplicityEstimateForRhoTubesDilate`, proved, and its `c = 1`
specialisations `…Undilated` and `…Undilated_lam` are proved, all at the honest loss constant
`ShadedBody.shadingMultiplicityEstimateForRhoTubesDilate.C`. What is unproved is *this*
statement, which differs from all three; see "What is left to prove, exactly" below. The
hypotheses are the configuration's own: the bundle is
the *shaded* one that the field `Kakeya.VeryNotSticky.uniform` supplies, at the grid length
`⌈log log 1/δ⌉` and the constant `cfg.C₀`, because Section 5 asks for a
`Kakeya.ShadedTube.ShadedUniformTubeSet` at exactly that grid length and cannot be invoked
from the tube-level bundle alone.

Four things separate this statement from the raw one, and they are of three different kinds.

* **Essential distinctness is replaced by bounded overlap** (a genuine strengthening). Section 5
  asks its outer family to be pairwise essentially distinct (`hed`). The nodes of a
  `Tube.UniformTubeSet` are not, and the docstring of
  `Tube.UniformTubeSet.boundedOverlap` says why they cannot be made so without
  destroying the cardinality that the counting bounds need. What the nodes *do* have is
  Definition 2.1(ii): at most `C₀` of them meet any given `ρ`-tube through `𝕋`. That is the
  `∼1`-multiplicity content `hed` was there to provide, and it is what the proof of Section 5
  actually uses — the essential distinctness enters only through a packing count of the outer
  family against a test tube, which bounded overlap supplies directly, with `C₀` in place of
  the dimensional constant.
* **The `C₀` of that substitution is paid by the factor `δ^{cfg.η}` on the small side of the
  ball conjunct.** `Kakeya.VeryNotSticky.coe_C₀_le_rpow_neg_eta` gives `C₀ ≤ δ^{-η}` at the
  configuration's own constant — which is why pinning the bundle to `cfg.C₀` rather than
  quantifying `C₀` is what keeps the statement from being an assertion about arbitrarily bad
  hierarchies — so one factor `δ^{η}` is exactly the room a single substitution needs. Earlier
  versions asserted the ball estimate at the closed term
  `Kakeya.ShadedBody.shadingMultiplicityEstimateForRhoTubes.C` with no `δ`-power and no `C₀`
  anywhere on its small side, hence with no room for the loss at all; that made the statement
  strictly stronger than the Section-5 lemma it stands in for can deliver under the
  substitution, i.e. not honestly satisfiable. The room is affordable and is now taken:
  `Kakeya.VeryNotSticky.coarseBallEstimate_of_gridScale` transports the estimate from the grid
  scale `ρ` to the nominal radius `r` at the cost `(ρ/r)³ ≤ δ^{-3η}`, so with the extra `δ^{η}`
  it needs `ν/9 - η ≥ 3η`, i.e. `ν ≥ 36 η`, against the standing `ν ≥ 90 η` of
  Configuration `hyp:ml2setup`; the surplus `ν/9 - 4η ≥ 6η` is not spent
  (`Kakeya.VeryNotSticky.rpow_sub_eta_mul_cube_le_cube_of_gridStep`). Because the whole loss
  fits inside the gain, the *conclusion* of `coarseBallEstimate_of_gridScale`, and hence the
  statement of `Kakeya.VeryNotSticky.exists_aScaleInputs` and everything downstream of it in
  `Kakeya.DimensionThree.MainLemma2.Goals`, is unchanged.
* **Section 5's two-sided shading-density hypothesis is no longer absorbed.** `hlam_lb` and
  `hlam_ub` there say `|Y(T)| ∼_{Cd} lam |T|` for each inner tube, at a comparison constant
  `Cd`. `cfg.fullness_ge` is the *aggregate* ratio `(∑|Y(T)|)/(∑|T|) ≥ δ^η`, which is a ratio
  of sums and therefore bounds no individual tube; and the shaded bundle `𝒱` does not supply
  the missing half either, its four branching fields being statements about per-point counts
  and not about `|Y(T)|` for a single `T`. Earlier versions of this statement silently helped
  themselves to the two hypotheses anyway. They are now data on the configuration —
  `Kakeya.VeryNotSticky.lam`, `Kakeya.VeryNotSticky.Cd`, `Kakeya.VeryNotSticky.shading_lb`,
  `Kakeya.VeryNotSticky.shading_ub` — which is where they belong, being a property of the pair
  `(𝕋, Y)` alone, and which is the standing abuse of notation of the blueprint made explicit:
  the pigeonholing that makes the densities comparable happens while Configuration
  `hyp:ml2setup` is assembled. Whoever discharges this statement applies Section 5 with
  `lam := cfg.lam` and `Cd := cfg.Cd` and those two fields.
* **The outer-fullness conjunct is stated at `C⁻¹ lam`, which is what Section 5 delivers.**
  Section 5 concludes `λ(𝕋_ρ, Y_{𝕋_ρ}) ≥ C⁻¹ lam` at the *inner* density `lam`, not at the
  aggregate `δ^η`; asserting `δ^η` here would have been a second unstated absorption, since
  `lam` and `λ(𝕋, Y)` differ by up to `Cd`. The bridge to the `δ^{2η}` that
  `Kakeya.VeryNotSticky.coarseMassBound` consumes is the configuration field
  `Kakeya.VeryNotSticky.lam_ge`, `δ^{2η} ≤ lam`, and it is spent in the *proved*
  `Kakeya.VeryNotSticky.exists_aScaleInputs`.
* **The inner layer is the configuration's own pair, not a refinement of it.** Section 5
  returns `G.innerSet = {i ∈ F.innerSet | F.parent i ∈ G.outerSet}` and identifies inner bodies
  only as convex bodies. Per the first remark of blueprint `lem:ml2aScaleData` the `≈ 1`
  refinement is taken *while* Configuration `hyp:ml2setup` is assembled — blueprint
  `lem:ml2setupexists` lists `shadingMultiplicityEstimateForRhoTubes` among its inputs — so the
  pair recorded by `cfg` is already the refined one and there is nothing left to transfer. This
  is the standing abuse of notation of the blueprint, and it is why `hinner` and `hbody` below
  are equalities rather than comparisons.
**Not refutable by a trivial realisation.** Every conjunct is an existential statement about a
shading that is being constructed, at a family (`cfg.activeTubeNodes 𝒱.tubeUniform k`) and inner
pair (`cfg.s`, `cfg.T`) that are fixed in advance, and every constant occurring is either the
closed term `Kakeya.ShadedBody.shadingMultiplicityEstimateForRhoTubes.C` or a field of `cfg`.
In particular the trivial realisation of the threshold bundle that killed an earlier stub —
`Kakeya.VeryNotSticky.nonempty_scaleThresholds` at `aScaleConst ≡ 1` — is irrelevant here,
since no threshold bundle is mentioned; and the earlier version's universally quantified `C₀`,
the one quantifier order that *was* wrong, is gone. Neither of the two new occurrences of a
post-`δ` quantity weakens this: `cfg.lam` appears on the *small* side of the fullness conjunct,
where a larger value is a stronger claim, and `cfg.Cd` does not appear at all.

**Essential distinctness cannot be supplied instead, and this is why.** The development proves
`Kakeya.Tube.exists_maximal_essDistinct` and `Kakeya.Tube.refineToEssDistinctLeaves`, and
neither helps. The first returns a maximal essentially distinct *subfamily* with no cardinality
comparison at all. The second returns one with `#s ≤ C_n · D · #s'`, where `D` is any bound on
the maximal density of the family it is applied to; at the node family `𝕋_ρ` the only such
bound available is `Kakeya.VeryNotSticky.maxDensity_activeTubeNodes_le`, whose right-hand side
is polynomially large in `δ` (of size `ρ²/(δ^{2+η} |𝕋[T_ρ]|)`), so the cardinality loss is
polynomial and no gain of the layer can pay for it. Independently of that, passing to a
subfamily destroys the identity `G.outerSet = cfg.activeTubeNodes 𝒱.tubeUniform k`, which is
what lets `Kakeya.VeryNotSticky.rScaleParentData_of_gridScale` apply
`Kakeya.VeryNotSticky.maxDensity_activeTubeNodes_le` and
`Kakeya.VeryNotSticky.card_le_card_activeTubeNodes_mul` at all — both are statements about the
full node family. So bounded overlap is not a convenience here; it is the only form of the
hypothesis available.

The hypothesis `hρ` is the range `[δ, 1]` of blueprint `shadingMultiplicityEstimateForRhoTubes`,
which is where its `ρ`-tubes have to live; it is supplied by the rounding, since the radius
being rounded already satisfies `δ ≤ a ≤ r ≤ 1`.

**What is left to prove, exactly — settled.**
`Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid_subfamily` above is GWZ Lemma 5.11 run at
this configuration and is *proved*. Two things separate it from this statement — the subfamily,
and the loss constant — and the two are of completely different weight. The following is the
checked account; it replaces an earlier version of this paragraph that blamed the constant.

*The constant is not the obstruction.* The placeholder
`Kakeya.ShadedBody.shadingMultiplicityEstimateForRhoTubes.C = 1` is nevertheless **never a
correct reading of Lemma 5.11**: that lemma's loss is a product of four pigeonholings and a
geometric loss, it is bounded below by the dimension-only floor
`ShadedBody.rhoTubesBallLoss 3 = 2·10⁶` (`ShadedBody.one_lt_rhoTubesSection9Loss`), and what it
*is* is a multiplicity — the ratio `∑_T |Y(T)|` to `|⋃_T Y(T)|` at the coarse scale — so
asserting it equals `1` assumes the conclusion of Main Lemma 2. The placeholder must go. But it
is not what keeps this statement open, and that is now compiler-checked: each of the two
estimates below is realisable **at the full node family and at loss `1`**, by an explicit
shading —
`Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid_saturated` for the fullness conjunct and
`Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid_minimal` for the ball conjunct. In
particular no refutation of this statement can be extracted from either conjunct alone, unlike
`Kakeya.VeryNotSticky.coarseKatzTaoBound`.

*The honest fullness conjunct is proved, on the full family.*
`Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid_inducedFullness` delivers the fullness
clause at GWZ's own coarse shading `Y_{𝕋_ρ}(T_ρ) = T_ρ ∩ N_{2ρ}(⋃_{T ∈ 𝕋[T_ρ]} Y(T))`, with
`G.innerSet = cfg.s`, `G.outerSet = cfg.activeTubeNodes …` and `G.parent` all on the nose, at the
*purely dimensional* loss `ShadedBody.rhoTubesInducedFullnessLoss 3`. So the subfamily gap closes
for the fullness conjunct, and it closes at a constant that does not depend on `δ` or `|𝕋|`.

*What is genuinely open is the ball conjunct at the full family, and only jointly.* The residue is
equivalent to the existence of a single measurable set — see
`Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid_of_shadingSet` and
`Kakeya.VeryNotSticky.exists_shadingSet_of_exists_coarseShadedFamilyAtGrid` — namely a `Z` with
`U(𝕋, Y) ⊆ Z ⊆ ⋃ 𝕋_ρ`, whose intersections with the node tubes are `lam`-full on average and
whose own volume is small enough. The saturated shading maximises the first and destroys the
second; the minimal shading does the reverse.

*The supremum is not the obstruction, and that is now compiler-checked.* It was natural to read
the ball conjunct as an assertion about the **densest** `ρ`-ball of `U(𝕋, Y)` — the uniformity
that Step 5 of the proof of Lemma 5.11 buys by discarding coarse bodies — and hence as something
no proof of that lemma could supply on the full family. That reading is wrong.
`Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid_of_shadingSet_volume_max` proves that the
*whole* family of point estimates follows from one inequality in which no point occurs,

  `δ^η · |U(𝕋_ρ, Y_{𝕋_ρ})| ≤ max (|U(𝕋, Y)|, |B(0, ρ)|)`,

because the local density `|U(𝕋,Y) ∩ B(x,ρ)| / |B(x,ρ)|` is at most `1` and is also at most
`|U(𝕋,Y)| / |B(0,ρ)|`, and one of those two bounds always suffices. So the residue is not an
assertion about a worst `ρ`-ball at all; it is a **two-sided volume budget on one set**:

  produce a measurable `Z ⊇ U(𝕋, Y)` with `Cd⁻¹ · lam ≤ λ(𝕋_ρ, T_ρ ∩ Z)` and
  `δ^η · |Z| ≤ max (|U(𝕋, Y)|, |B(0, ρ)|)`

(`Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid_of_shadingSet_budget`); and the saturated
choice `Z = ⋃ 𝕋_ρ` collapses it to the displayed inequality, with no set and no point in it
(`Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid_of_coarseVolume`). The reduction is not
vacuous: `Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid_of_card_activeTubeNodes` discharges
the residue outright at any grid index with
`δ^η · |𝕋_ρ| · Tube.volume_le.C 3 · ρ² ≤ |B(0, ρ)|`.

*Where the budget is short, exactly.* Fullness costs volume: the coarse multiplicity is at most
`|𝕋_ρ|`, so a `Cd⁻¹ · lam`-full `Z` has `|Z| ≥ Cd⁻¹ · lam · ∑_j |T_{ρ,j}| / |𝕋_ρ|`, at least a
`Cd⁻¹ · lam` fraction of one node tube. The budget allows
`|Z| ≤ δ^{-η} max(|U(𝕋,Y)|, |B(0,ρ)|)`. What the configuration does **not** supply is any serious
lower bound on `|U(𝕋, Y)|`. `Kakeya.VeryNotSticky.maxDensity_le` bounds `Kakeya.maxDensity`,
which is built from `Kakeya.densityIn`, GWZ Eq. (2) — and that counts only the tubes *contained*
in the test body, not their intersections with it. At `K = closedBall 0 1` it therefore says
`∑_i |T_i| ≤ δ^{-η} |B_1|`, an **upper** bound on the total tube volume, and it says nothing at
all about the volume of the shaded union or about its density in a `ρ`-ball. The only lower bound
on `|U(𝕋, Y)|` derivable from the fields is a single tube's shading,
`|U(𝕋,Y)| ≥ Cd⁻¹ · lam · Tube.le_volume.c 3 · δ²`. So what is open is a genuine two-scale volume
comparison whose small side the configuration never pins down — not the supremum, and not either
conjunct on its own. Nor is there room in the constants: at `lam = Cd`, i.e. `Y(T) = T`
(`Kakeya.VeryNotSticky.lam_le_Cd` shows this is the top of the range), fullness at loss `1`
forces `Z = ⋃ 𝕋_ρ` up to null sets and the budget becomes `δ^η · |⋃ 𝕋_ρ| ≤ |U(𝕋, Y)|` on the
nose, with no slack anywhere. That is one more reason — and the first that bites the two
conjuncts *jointly* rather than either one alone — why the placeholder `C = 1` must be replaced
by the honest loss. The two structural routes are (i) weaken
`G.outerSet = cfg.activeTubeNodes …` to `⊆` (and `G.innerSet = cfg.s` to the induced subset) and
re-derive `Kakeya.VeryNotSticky.rScaleParentData_of_gridScale` through the monotonicity of
`maxDensity` and of `Finset.card`, or (ii) close `Kakeya.VeryNotSticky` under `C⁻¹`-refinement so
that the pigeonholed pair is again a configuration. Either is a cross-file repair touching
`Kakeya.DimensionThree.MainLemma2.AScaleConstants` (whose `aScaleDataConstant` reads the
placeholder as a *closed* term and must change shape, not merely value),
`Kakeya.DimensionThree.MainLemma2.AScaleInterface` and the tripwire in
`Kakeya.DimensionThree.MainLemma2.AScaleGuardrails`; it is not a local proof-search steps.

The `cfg.Cd` on the small side of the fullness conjunct is an earlier repair; see
`Kakeya.DimensionThree.MainLemma2.AScaleGuardrails` for the refutation of the form without it
and for the tripwire that keeps it. -/
theorem exists_coarseShadedFamilyAtGrid (cfg : VeryNotSticky.{u})
    (𝒱 : ShadedTube.ShadedUniformTubeSet cfg.s cfg.T (Tube.ssfGridLen cfg.δ) cfg.C₀)
    {k : ℕ} (hk : k ≤ Tube.ssfGridLen cfg.δ)
    {ρ : NNReal} (hgrid : Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k = ρ)
    (hρ : ρ ∈ Set.Icc cfg.δ 1) :
    ∃ G : ShadedFactorFamily (EuclideanSpace ℝ (Fin 3)) cfg.ι cfg.ι,
      G.innerSet = cfg.s ∧
      (∀ i ∈ cfg.s, G.innerBody i = (cfg.T i).toShadedBody) ∧
      G.outerSet = cfg.activeTubeNodes 𝒱.tubeUniform k ∧
      (∀ j ∈ G.outerSet,
        (G.outerBody j).toConvexSpaceBody =
          (𝒱.tubeUniform.cover.tube k j).toConvexSpaceBody) ∧
      (cfg.Cd * _root_.ShadedBody.rhoTubesInducedFullnessLoss 3)⁻¹ * cfg.lam ≤
        ShadedBody.fullness G.outerSet G.outerBody ∧
      (∀ x ∈ ⋃ j ∈ G.outerSet, (G.outerBody j).shade,
        (cfg.δ : ENNReal) ^ cfg.η *
            (((_root_.ShadedBody.rhoTubesInducedFullnessLoss 3 : NNReal) : ENNReal)⁻¹ *
                volume (⋃ j ∈ G.outerSet, (G.outerBody j).shade) *
              (volume ((⋃ i ∈ G.innerSet, (G.innerBody i).shade) ∩ ball x (ρ : ℝ)) /
                volume (ball x (ρ : ℝ)))) ≤
          volume (⋃ i ∈ G.innerSet, (G.innerBody i).shade)) := by
  classical
  have hfr : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
  obtain ⟨i₀, hi₀⟩ := s_nonempty cfg
  have hmaps : ∀ i ∈ cfg.s, 𝒱.tubeUniform.cover.assign k i
      ∈ cfg.activeTubeNodes 𝒱.tubeUniform k := by
    intro i hi
    rw [activeTubeNodes, Finset.mem_filter]
    refine ⟨𝒱.tubeUniform.cover.assign_mem k hk i hi, ⟨i, ?_⟩⟩
    simp [tubeFibre, Tube.coverClass, hi]
  have hle : ∀ i ∈ cfg.s,
      (cfg.T i).toConvexSpaceBody ≤
        (𝒱.tubeUniform.cover.tube k (𝒱.tubeUniform.cover.assign k i)).toConvexSpaceBody := by
    intro i hi
    simpa using 𝒱.tubeUniform.cover.le_tube_assign k hk i hi
  have hactive : ∀ j ∈ cfg.activeTubeNodes 𝒱.tubeUniform k,
      ∃ i ∈ cfg.s, 𝒱.tubeUniform.cover.assign k i = j := by
    intro j hj
    rw [activeTubeNodes, Finset.mem_filter] at hj
    obtain ⟨i, hi⟩ := hj.2
    rw [tubeFibre, Tube.coverClass, Finset.mem_filter] at hi
    exact ⟨i, hi.1, hi.2⟩
  have ht : (cfg.activeTubeNodes 𝒱.tubeUniform k).Nonempty :=
    ⟨𝒱.tubeUniform.cover.assign k i₀, hmaps i₀ hi₀⟩
  have hCd : cfg.Cd ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one cfg.hCd)
  have hcar : ∀ i ∈ cfg.s,
      ((cfg.T i).toConvexSpaceBody : Set (EuclideanSpace ℝ (Fin 3)))
        ⊆ ((𝒱.tubeUniform.cover.tube k (𝒱.tubeUniform.cover.assign k i)).toConvexSpaceBody :
            Set (EuclideanSpace ℝ (Fin 3))) :=
    fun i hi => SetLike.coe_subset_coe.mpr (hle i hi)
  have hsubU : ∀ i ∈ cfg.s, (cfg.T i).shade ⊆
      Metric.cthickening (2 * (ρ : ℝ))
        (⋃ i' ∈ ({i' ∈ cfg.s | 𝒱.tubeUniform.cover.assign k i'
            = 𝒱.tubeUniform.cover.assign k i} : Finset cfg.ι), (cfg.T i').shade) := by
    intro i hi
    refine subset_trans ?_ (Metric.self_subset_cthickening _)
    exact Set.subset_biUnion_of_mem (u := fun i' => (cfg.T i').shade)
      (Finset.mem_filter.mpr ⟨hi, rfl⟩)
  subst hgrid
  refine ⟨{ innerSet := cfg.s
            innerBody := fun i => (cfg.T i).toShadedBody
            outerSet := cfg.activeTubeNodes 𝒱.tubeUniform k
            outerBody := _root_.ShadedBody.inducedCoarseShading cfg.s cfg.T
              (𝒱.tubeUniform.cover.assign k) (𝒱.tubeUniform.cover.tube k)
            parent := 𝒱.tubeUniform.cover.assign k
            parent_mem := hmaps
            inner_le_parent := hle
            shade_subset_parent := by
              intro i hi
              exact Set.subset_inter (subset_trans (cfg.T i).shade_subset (hcar i hi))
                (hsubU i hi) },
    rfl, fun _ _ => rfl, rfl, fun _ _ => rfl, ?_, ?_⟩
  · -- the fullness conjunct is the engine of GWZ Lemma 5.11 on the full coarse family
    have h := _root_.ShadedBody.le_fullness_inducedCoarseShading
      (E := EuclideanSpace ℝ (Fin 3)) (δ := cfg.δ) (Cd := cfg.Cd) (lam := cfg.lam)
      cfg.hδ hρ hCd cfg.T (𝒱.tubeUniform.cover.tube k)
      (𝒱.tubeUniform.cover.assign k) hle hactive ht cfg.shading_lb
    rwa [hfr] at h
  · -- the ball conjunct is `coarseLocalMass` read through the induced shading
    exact coarseBallConjunct_of_coarseLocalMass cfg _ rfl (fun _ _ => rfl) hk rfl
      (_root_.ShadedBody.iUnion_inducedCoarseShading_subset_cthickening cfg.s cfg.T
        (𝒱.tubeUniform.cover.assign k) (𝒱.tubeUniform.cover.tube k)
        (cfg.activeTubeNodes 𝒱.tubeUniform k))

/-! ### `Kakeya.VeryNotSticky.coarseKatzTaoBound` is **gone**

Its proved replacement is
`Kakeya.VeryNotSticky.coarseKatzTaoBound_of_etaBudget_atPair`, read at the window pair the
configuration now carries as `Kakeya.VeryNotSticky.ckt`; its single consumer
`Kakeya.VeryNotSticky.rScaleParentData_of_gridScale` is rewired onto it.

The refutation itself is **kept**, and is now stated as a negation rather than as a tripwire on
a declaration that no longer exists: see
`Kakeya.VeryNotSticky.statement_of_universal_coarseKatzTao_false` in
`Kakeya.DimensionThree.MainLemma2.CoarseKatzTaoRepair`, together with
`Kakeya.VeryNotSticky.CoarseKatzTaoStatement` and
`Kakeya.VeryNotSticky.coarseKatzTao_refutes_config`, which are untouched. -/

/-- A `ρ`-tube inside the closed unit ball, for `ρ ≤ 1/2`: the `ρ`-neighbourhood of the unit
segment centred at the origin.  Used only as the *off-family* default value when a family
indexed by `cfg.ι` has to be extended from `G.outerSet` to all of `cfg.ι`, because
`Kakeya.KatzTaoEstimate.multiplicity_bound_generalize_window` asks for its ball hypothesis at
every index, not only at the indices of the finite set.  The window used there is
`Metric.closedBall 0 4`, so the unit ball is more than enough for the default. -/
private lemma exists_tube_subset_closedBall (ρ : NNReal) (hρ : ρ ≤ 1 / 2) :
    ∃ V : Tube ρ (EuclideanSpace ℝ (Fin 3)), V.carrier ⊆ closedBall 0 1 := by
  set e : EuclideanSpace ℝ (Fin 3) := EuclideanSpace.single 0 (1 : ℝ) with he_def
  have he : ‖e‖ = 1 := by simp [he_def]
  have hdist : dist (-((1 : ℝ) / 2) • e) (((1 : ℝ) / 2) • e) = 1 := by
    rw [dist_eq_norm]
    have hsub : -((1 : ℝ) / 2) • e - ((1 : ℝ) / 2) • e = (-1 : ℝ) • e := by
      module
    rw [hsub, norm_smul, he]
    norm_num
  refine ⟨Tube.mk' ρ hdist, ?_⟩
  have hcar : (Tube.mk' ρ hdist).carrier
      = ⋃ z ∈ segment ℝ (-((1 : ℝ) / 2) • e) (((1 : ℝ) / 2) • e), closedBall z (ρ : ℝ) := rfl
  have hρ' : (ρ : ℝ) ≤ 1 / 2 := by exact_mod_cast hρ
  have hseg : segment ℝ (-((1 : ℝ) / 2) • e) (((1 : ℝ) / 2) • e) ⊆ closedBall 0 (1 / 2 : ℝ) := by
    refine (convex_closedBall (0 : EuclideanSpace ℝ (Fin 3)) (1 / 2 : ℝ)).segment_subset ?_ ?_ <;>
      · simp [mem_closedBall, dist_eq_norm, norm_smul, he]
  rw [hcar]
  intro p hp
  simp only [Set.mem_iUnion, exists_prop] at hp
  obtain ⟨z, hz, hpz⟩ := hp
  have hz' : ‖z‖ ≤ 1 / 2 := by
    have := hseg hz
    simpa [mem_closedBall, dist_eq_norm] using this
  have hpz' : dist p z ≤ (ρ : ℝ) := by simpa [mem_closedBall] using hpz
  have : dist p 0 ≤ (ρ : ℝ) + 1 / 2 := by
    calc dist p 0 ≤ dist p z + dist z 0 := dist_triangle _ _ _
      _ ≤ (ρ : ℝ) + 1 / 2 := by
          gcongr
          simpa [dist_eq_norm] using hz'
  simp only [mem_closedBall]
  linarith

/-- **The Katz-Tao bound at the coarse family, with the fullness exponent left free.**

Identical to `Kakeya.VeryNotSticky.coarseKatzTaoBound_general_at` except that the fullness
exponent is a parameter `e` rather than the numeral `2 cfg.η`, tied to the window threshold by
`e ≤ cfg.exscal * ηKT`.  `hfull` enters the proof at exactly one place — the conversion of the
configuration's fullness into the `cfg.a ^ ηKT` the windowed estimate wants — and that conversion
reads `e` and nothing else, so nothing in the argument depends on the value.

It is stated because the honest fullness conjunct of
`Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid` converts to `δ^{3η}` and not to `δ^{2η}`
(`Kakeya.VeryNotSticky.rpow_three_eta_le_of_inducedFullness`), and the exponent budget has room
for that and five more `η` (`Kakeya.VeryNotSticky.coarseLossExponentHeadroom`).  The `2 cfg.η`
form below is this one at `e := 2 * cfg.η`, so no consumer of it moves. -/
theorem coarseKatzTaoBound_general_atFullness (cfg : VeryNotSticky.{u})
    {ν c ε₀ e : ℝ}
    (hε₀ν : ε₀ ≤ ν / 90)
    (hbudget : c ≤ cfg.exscal * (ν / 90 - ε₀))
    {ηKT : ℝ} (hηKT : 0 < ηKT) {ρ₀ : NNReal} (hρ₀half : ρ₀ ≤ 1 / 2)
    (hW : WindowFour.{u} (EuclideanSpace ℝ (Fin 3)) cfg.β ε₀ ηKT ρ₀) :
    ∀ (𝒰 : Tube.UniformTubeSet cfg.s (fun i ↦ (cfg.T i).toTube)
          (Tube.ssfGridLen cfg.δ) cfg.C₀) {k : ℕ}, k ≤ Tube.ssfGridLen cfg.δ →
      ∀ {ρ : NNReal}, Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k = ρ →
        ρ ∈ Set.Icc cfg.a 1 → ρ ≤ ρ₀ → e ≤ cfg.exscal * ηKT →
        ∀ (G : ShadedFactorFamily (EuclideanSpace ℝ (Fin 3)) cfg.ι cfg.ι),
          G.outerSet = cfg.activeTubeNodes 𝒰 k →
          (∀ j ∈ G.outerSet, (G.outerBody j).toConvexSpaceBody
              = (𝒰.cover.tube k j).toConvexSpaceBody) →
          (cfg.δ : NNReal) ^ e ≤ ShadedBody.fullness G.outerSet G.outerBody →
          ShadedBody.multiplicity G.outerSet G.outerBody ≤
            (cfg.a : ENNReal) ^ (-(ν / 90)) *
              ((cfg.δ : ENNReal) ^ c *
                  maxDensity (cfg.activeTubeNodes 𝒰 k)
                    (fun j ↦ (𝒰.cover.tube k j).toConvexSpaceBody) ^ (1 - cfg.β)) *
              (G.outerSet.card : ENNReal) ^ cfg.β
    := by
  classical
  have hexs : 0 < cfg.exscal := cfg.hexscal
  intro 𝒰 k hk ρ hgrid hρ hρ₀ hηb G houterSet houterBody hfull
  subst hgrid
  set ρ : NNReal := Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k with hρdef
  -- basic positivity
  have hδa : cfg.δ ≤ cfg.a := cfg.hdims.1
  have ha0 : 0 < cfg.a := lt_of_lt_of_le cfg.hδ hδa
  have haρ : cfg.a ≤ ρ := hρ.1
  have hρpos : 0 < ρ := lt_of_lt_of_le ha0 haρ
  have hρhalf : ρ ≤ (1 / 2 : NNReal) := le_trans hρ₀ hρ₀half
  -- the family of shaded `ρ`-tubes: the node tubes carrying the outer shades on `G.outerSet`,
  -- an arbitrary unit-ball tube elsewhere.
  obtain ⟨Vdef, hVdef⟩ := exists_tube_subset_closedBall ρ hρhalf
  let TT : cfg.ι → ShadedTube ρ (EuclideanSpace ℝ (Fin 3)) := fun j =>
    if hj : j ∈ G.outerSet then
      { toTube := 𝒰.cover.tube k j
        shade := (G.outerBody j).shade
        measurableSet_shade := (G.outerBody j).measurableSet_shade
        shade_subset := by
          have hcar : (G.outerBody j).carrier = (𝒰.cover.tube k j).carrier :=
            congrArg ConvexSpaceBody.carrier (houterBody j hj)
          exact hcar ▸ (G.outerBody j).shade_subset }
    else
      { toTube := Vdef
        shade := ∅
        measurableSet_shade := MeasurableSet.empty
        shade_subset := Set.empty_subset _ }
  have hTTshade : ∀ j ∈ G.outerSet, (TT j).shade = (G.outerBody j).shade := by
    intro j hj
    simp only [TT, dif_pos hj]
  have hTTnode : ∀ j ∈ G.outerSet,
      (TT j).toConvexSpaceBody = (𝒰.cover.tube k j).toConvexSpaceBody := by
    intro j hj
    simp only [TT, dif_pos hj]
  have hTTbody : ∀ j ∈ G.outerSet,
      (TT j).toConvexSpaceBody = (G.outerBody j).toConvexSpaceBody := by
    intro j hj
    rw [hTTnode j hj, houterBody j hj]
  have hTTcar : ∀ j ∈ G.outerSet, (TT j).carrier = (G.outerBody j).carrier := by
    intro j hj
    exact congrArg ConvexSpaceBody.carrier (hTTbody j hj)
  -- the containment the hierarchy really gives: radius `4`, not `1`
  have hnode : ∀ j ∈ G.outerSet, (𝒰.cover.tube k j).carrier ⊆ closedBall 0 4 := by
    intro j hj
    have hjIdx : j ∈ 𝒰.cover.indexSet k :=
      mem_indexSet_of_mem_activeTubeNodes cfg 𝒰 (houterSet ▸ hj)
    exact MultiScaleFac.node_carrier_subset_ball cfg.hδ cfg.hδ1 𝒰 (s_nonempty cfg)
      (fun i hi ↦ cfg.contained i hi) hk hjIdx
  have h4 : (((4 : NNReal)) : ℝ) = 4 := by norm_num
  have hballTT : ∀ j, (TT j).carrier ⊆ closedBall 0 (((4 : NNReal)) : ℝ) := by
    intro j
    rw [h4]
    by_cases hj : j ∈ G.outerSet
    · rw [show (TT j).carrier = (𝒰.cover.tube k j).carrier from
        congrArg ConvexSpaceBody.carrier (hTTnode j hj)]
      exact hnode j hj
    · simp only [TT, dif_neg hj]
      exact hVdef.trans (Metric.closedBall_subset_closedBall (by norm_num))
  -- transfers
  have hsumshade : ∑ j ∈ G.outerSet, volume (TT j).toShadedBody.shade
      = ∑ j ∈ G.outerSet, volume (G.outerBody j).shade :=
    Finset.sum_congr rfl fun j hj => by rw [show (TT j).toShadedBody.shade = (TT j).shade from rfl,
      hTTshade j hj]
  have hsumcar : ∑ j ∈ G.outerSet, volume (TT j).toShadedBody.carrier
      = ∑ j ∈ G.outerSet, volume (G.outerBody j).carrier :=
    Finset.sum_congr rfl fun j hj => by
      rw [show (TT j).toShadedBody.carrier = (TT j).carrier from rfl, hTTcar j hj]
  have hunion : (⋃ j ∈ G.outerSet, (TT j).toShadedBody.shade)
      = ⋃ j ∈ G.outerSet, (G.outerBody j).shade :=
    Set.iUnion₂_congr fun j hj => by
      rw [show (TT j).toShadedBody.shade = (TT j).shade from rfl, hTTshade j hj]
  have hmult : ShadedBody.multiplicity G.outerSet (fun j => (TT j).toShadedBody)
      = ShadedBody.multiplicity G.outerSet G.outerBody := by
    rw [ShadedBody.multiplicity_eq_div, ShadedBody.multiplicity_eq_div, hsumshade, hunion]
  have hfullTT : ShadedBody.fullness G.outerSet (fun j => (TT j).toShadedBody)
      = ShadedBody.fullness G.outerSet G.outerBody := by
    unfold ShadedBody.fullness ShadedBody.fullness'
    rw [hsumshade, hsumcar]
  have hmd : maxDensity G.outerSet (fun j => (TT j).toConvexSpaceBody)
      = maxDensity (cfg.activeTubeNodes 𝒰 k)
          (fun j => (𝒰.cover.tube k j).toConvexSpaceBody) := by
    rw [← houterSet]
    exact maxDensity_congr fun j hj => hTTnode j hj
  -- the fullness hypothesis at the auxiliary scale `cfg.a`
  have hadelta : cfg.a ≤ cfg.δ ^ cfg.exscal := le_trans cfg.hdims.2.1 cfg.hdims.2.2
  have hfullKT : cfg.a ^ ηKT ≤ ShadedBody.fullness G.outerSet (fun j => (TT j).toShadedBody) := by
    rw [hfullTT]
    refine le_trans ?_ hfull
    calc cfg.a ^ ηKT ≤ (cfg.δ ^ cfg.exscal) ^ ηKT := NNReal.rpow_le_rpow hadelta hηKT.le
      _ = cfg.δ ^ (cfg.exscal * ηKT) := by rw [← NNReal.rpow_mul]
      _ ≤ cfg.δ ^ e := NNReal.rpow_le_rpow_of_exponent_ge cfg.hδ cfg.hδ1 hηb
  have hballTT' : ∀ j, (TT j).carrier ⊆ closedBall 0 (4 : ℝ) := by
    intro j
    have hj := hballTT j
    rwa [h4] at hj
  have hmain := hW ρ hρpos hρ₀ cfg.a ha0 haρ G.outerSet TT hballTT' hfullKT
  rw [hmult, hmd] at hmain
  refine le_trans hmain ?_
  -- exponent bookkeeping
  set md : ENNReal := maxDensity (cfg.activeTubeNodes 𝒰 k)
    (fun j => (𝒰.cover.tube k j).toConvexSpaceBody) with hmd_def
  have ha0' : (cfg.a : ENNReal) ≠ 0 := by
    simpa using (ENNReal.coe_ne_zero.mpr ha0.ne')
  have hatop : (cfg.a : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hadelta' : (cfg.a : ENNReal) ≤ (cfg.δ : ENNReal) ^ cfg.exscal := by
    rw [← ENNReal.coe_rpow_of_nonneg _ hexs.le]
    exact_mod_cast hadelta
  have hδle1 : (cfg.δ : ENNReal) ≤ 1 := by
    exact_mod_cast cfg.hδ1
  have hkey : (cfg.a : ENNReal) ^ (-ε₀)
      ≤ (cfg.a : ENNReal) ^ (-(ν / 90)) * (cfg.δ : ENNReal) ^ c := by
    have hsplit : (cfg.a : ENNReal) ^ (-ε₀)
        = (cfg.a : ENNReal) ^ (-(ν / 90)) * (cfg.a : ENNReal) ^ (ν / 90 - ε₀) := by
      rw [← ENNReal.rpow_add _ _ ha0' hatop]
      congr 1
      ring
    rw [hsplit]
    refine mul_le_mul_right ?_ _
    calc (cfg.a : ENNReal) ^ (ν / 90 - ε₀)
        ≤ ((cfg.δ : ENNReal) ^ cfg.exscal) ^ (ν / 90 - ε₀) :=
          ENNReal.rpow_le_rpow hadelta' (by linarith)
      _ = (cfg.δ : ENNReal) ^ (cfg.exscal * (ν / 90 - ε₀)) := by
          rw [← ENNReal.rpow_mul]
      _ ≤ (cfg.δ : ENNReal) ^ c :=
          ENNReal.rpow_le_rpow_of_exponent_ge hδle1 hbudget
  calc (cfg.a : ENNReal) ^ (-ε₀) * md ^ (1 - cfg.β) * (G.outerSet.card : ENNReal) ^ cfg.β
      ≤ ((cfg.a : ENNReal) ^ (-(ν / 90)) * (cfg.δ : ENNReal) ^ c) * md ^ (1 - cfg.β) *
          (G.outerSet.card : ENNReal) ^ cfg.β := by
        gcongr
    _ = (cfg.a : ENNReal) ^ (-(ν / 90)) *
          ((cfg.δ : ENNReal) ^ c * md ^ (1 - cfg.β)) *
          (G.outerSet.card : ENNReal) ^ cfg.β := by ring

/-- **The windowed Katz–Tao estimate at the coarse family, at a *given* pair of thresholds.**

The whole content of the `∃`-form `coarseKatzTaoBound_general` below (private to this file),
with the two thresholds
of the windowed bound taken as parameters rather than produced existentially.  Factoring it this
way is not cosmetic: an existentially produced `ηKT` cannot be compared with `cfg.η` by any
statement that does not itself produce it, so the `∃`-form below is unusable by a consumer,
while this form can be instantiated at the *named* thresholds
`Kakeya.VeryNotSticky.coarseKTEta` and `Kakeya.VeryNotSticky.coarseKTRadius` of
`Kakeya.DimensionThree.MainLemma2.KTWindowThresholds`.

`hρ₀half` is what the off-family default tube of `exists_tube_subset_closedBall` needs; the
named radius satisfies it unconditionally by `Kakeya.VeryNotSticky.coarseKTRadius_le_half`.

(No longer `private`: it is the only form that takes its two thresholds as *parameters* together
with a `Kakeya.WindowFour` witness, so it is the only one a downstream file can instantiate at a
`β`-uniform pair rather than at the Skolem `Kakeya.VeryNotSticky.coarseKTEta`.  See
`Kakeya.DimensionThree.MainLemma2.CoarseKatzTaoRepair`.) -/
theorem coarseKatzTaoBound_general_at (cfg : VeryNotSticky.{u}) {ν c ε₀ : ℝ}
    (hε₀ν : ε₀ ≤ ν / 90)
    (hbudget : c ≤ cfg.exscal * (ν / 90 - ε₀))
    {ηKT : ℝ} (hηKT : 0 < ηKT) {ρ₀ : NNReal} (hρ₀half : ρ₀ ≤ 1 / 2)
    (hW : WindowFour.{u} (EuclideanSpace ℝ (Fin 3)) cfg.β ε₀ ηKT ρ₀) :
    ∀ (𝒰 : Tube.UniformTubeSet cfg.s (fun i ↦ (cfg.T i).toTube)
          (Tube.ssfGridLen cfg.δ) cfg.C₀) {k : ℕ}, k ≤ Tube.ssfGridLen cfg.δ →
      ∀ {ρ : NNReal}, Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k = ρ →
        ρ ∈ Set.Icc cfg.a 1 → ρ ≤ ρ₀ → 2 * cfg.η ≤ cfg.exscal * ηKT →
        ∀ (G : ShadedFactorFamily (EuclideanSpace ℝ (Fin 3)) cfg.ι cfg.ι),
          G.outerSet = cfg.activeTubeNodes 𝒰 k →
          (∀ j ∈ G.outerSet, (G.outerBody j).toConvexSpaceBody
              = (𝒰.cover.tube k j).toConvexSpaceBody) →
          (cfg.δ : NNReal) ^ (2 * cfg.η) ≤ ShadedBody.fullness G.outerSet G.outerBody →
          ShadedBody.multiplicity G.outerSet G.outerBody ≤
            (cfg.a : ENNReal) ^ (-(ν / 90)) *
              ((cfg.δ : ENNReal) ^ c *
                  maxDensity (cfg.activeTubeNodes 𝒰 k)
                    (fun j ↦ (𝒰.cover.tube k j).toConvexSpaceBody) ^ (1 - cfg.β)) *
              (G.outerSet.card : ENNReal) ^ cfg.β
    := by
  intro 𝒰 k hk ρ hgrid hρ hρ₀ hηb G houterSet houterBody hfull
  exact coarseKatzTaoBound_general_atFullness cfg (e := 2 * cfg.η) hε₀ν hbudget hηKT hρ₀half hW
    𝒰 hk hgrid hρ hρ₀ hηb G houterSet houterBody hfull

/-- **The Katz–Tao estimate at the coarse family, in the form the interface consumes, with the
density slot left as a single exponent `c` and the loss exponent `ε₀` left free.**

This is the whole mathematical content of `Kakeya.VeryNotSticky.coarseKatzTaoBound`, factored
so that the two named forms below differ only in the arithmetic of `c`.  It is
`Kakeya.KatzTaoEstimate.multiplicity_bound_generalize_window` at `R = 4` (itself proved, from
the field `Kakeya.VeryNotSticky.ktEstimate`) applied to the node family at the auxiliary scale
`τ := cfg.a`, with the three hypotheses that estimate needs and the target statement does not
carry — a smallness threshold `ρ ≤ ρ₀` on the *tube radius*, the fullness threshold
`cfg.η ≤ cfg.exscal * ηKT`, and the fullness hypothesis itself — left explicit.

**The containment hypothesis is gone.**  The earlier form of this statement also carried
`∀ j ∈ G.outerSet, (G.outerBody j).carrier ⊆ closedBall 0 1`, and that hypothesis is
*unsuppliable*: `Kakeya.VeryNotSticky.node_carrier_not_subset_closedBall_one` exhibits a
`Tube.UniformTubeSet` over a `δ`-tube in `B_1` whose node at *every* grid index leaves
`B_1`.  The sharpest containment the hierarchy proves is
`Kakeya.MultiScaleFac.node_carrier_subset_ball`, at radius `4`, and that is now enough:
`Kakeya.KatzTaoEstimate.multiplicity_bound_generalize_window` is the Katz–Tao multiplicity
bound for families in `closedBall 0 R`, so the containment is *derived* here from `houterSet`
and `houterBody` rather than assumed.

`hbudget` is the third input.  The conclusion reads the multiplicity at `δ^c Δ_max` rather than
at `Δ_max`; that is a *strengthening* by `δ^{-c}`, and it must be paid for out of the gain
`a^{-ν/90}`, i.e. the estimate has to be invoked at a strictly smaller loss exponent `ε₀`.  The
conversion from a power of `a` to a power of `δ` passes through `cfg.a ≤ cfg.δ ^ cfg.exscal` and
therefore costs the factor `cfg.exscal`, so what is needed is `c ≤ exscal · (ν/90 - ε₀)`.

**`ε₀` is a parameter and not `ν/90 - c/exscal`.**  Fixing it that way — which is what the
earlier form did — makes the produced `ηKT` and `ρ₀` depend on `c`, hence on `cfg.η`, and then
the threshold `cfg.η ≤ cfg.exscal * ηKT` is circular: it bounds `cfg.η` by a quantity that
moves with `cfg.η`.  With `ε₀` free, the caller may take it `cfg.η`-free — the two named forms
below take `ε₀ = ν/180` — and then `ηKT` and `ρ₀` depend only on the ambient space, `cfg.β` and
`ν`.  That is what a future hoisting of `ηKT` above the choice of `cfg.η` requires; it does not
by itself discharge the threshold, which remains a genuine constraint on the configuration. -/
private theorem coarseKatzTaoBound_general (cfg : VeryNotSticky.{u}) {ν c ε₀ : ℝ}
    (hε₀ : 0 < ε₀) (hε₀ν : ε₀ ≤ ν / 90)
    (hbudget : c ≤ cfg.exscal * (ν / 90 - ε₀)) :
    ∃ ηKT : ℝ, 0 < ηKT ∧ ∃ ρ₀ : NNReal, 0 < ρ₀ ∧
      ∀ (𝒰 : Tube.UniformTubeSet cfg.s (fun i ↦ (cfg.T i).toTube)
            (Tube.ssfGridLen cfg.δ) cfg.C₀) {k : ℕ}, k ≤ Tube.ssfGridLen cfg.δ →
        ∀ {ρ : NNReal}, Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k = ρ →
          ρ ∈ Set.Icc cfg.a 1 → ρ ≤ ρ₀ → 2 * cfg.η ≤ cfg.exscal * ηKT →
          ∀ (G : ShadedFactorFamily (EuclideanSpace ℝ (Fin 3)) cfg.ι cfg.ι),
            G.outerSet = cfg.activeTubeNodes 𝒰 k →
            (∀ j ∈ G.outerSet, (G.outerBody j).toConvexSpaceBody
                = (𝒰.cover.tube k j).toConvexSpaceBody) →
            (cfg.δ : NNReal) ^ (2 * cfg.η) ≤ ShadedBody.fullness G.outerSet G.outerBody →
            ShadedBody.multiplicity G.outerSet G.outerBody ≤
              (cfg.a : ENNReal) ^ (-(ν / 90)) *
                ((cfg.δ : ENNReal) ^ c *
                    maxDensity (cfg.activeTubeNodes 𝒰 k)
                      (fun j ↦ (𝒰.cover.tube k j).toConvexSpaceBody) ^ (1 - cfg.β)) *
                (G.outerSet.card : ENNReal) ^ cfg.β := by
  obtain ⟨p, hp1, hp2, hphalf, hW⟩ :=
    exists_windowFour (E := EuclideanSpace ℝ (Fin 3)) cfg.hβ.le cfg.hβ1
      cfg.ktEstimate hε₀
  exact ⟨p.1, hp1, p.2, hp2,
    coarseKatzTaoBound_general_at cfg hε₀ν hbudget hp1 hphalf hW⟩

/-- **The Katz–Tao estimate at the coarse family, repaired and proved.**

This is `Kakeya.VeryNotSticky.coarseKatzTaoBound` with the four defects of that statement
removed, and unlike it, it is *proved*, from `Kakeya.KatzTaoEstimate.multiplicity_bound_generalize`
(itself proved, from the field `Kakeya.VeryNotSticky.ktEstimate`).  The four repairs, and why
each is needed:

* **A fullness hypothesis.**  Without `hfull`, the conclusion is refutable: its right-hand side
  is a function of `cfg`, `𝒰`, `k` and `ν` only, while the left-hand side reads the outer
  *shades*, which `houterSet` and `houterBody` do not constrain at all (`houterBody` pins only
  `toConvexSpaceBody`, and the `ShadedFactorFamily` fields relating inner to outer are vacuous
  at `G.innerSet = ∅`).  Shading each node tube by its intersection with a small ball around a
  common point drives the left-hand side to `G.outerSet.card` and the right-hand side to `0`.
* **A smallness threshold on the tube radius `ρ`, not on `cfg.δ`.**  The `∀ᶠ δ in 𝓝[>] 0` of
  `Kakeya.KatzTaoEstimate.multiplicity_bound_generalize` is on the radius of the tubes of the
  family it is applied to.  Here that family is the *node* family, of radius `ρ`, and
  `hρ : ρ ∈ Set.Icc cfg.a 1` permits `ρ = 1` (at `k = 0`, `Tube.gridScale _ _ 0 = 1`).
  Shrinking `cfg.δ` does not shrink `ρ`, so the threshold has to be `hρ₀ : ρ ≤ ρ₀`.
* **The fullness threshold `hηb`.**  With the auxiliary scale `τ := cfg.a` forced by the shape
  of the conclusion, the estimate wants `fullness ≥ cfg.a ^ ηKT` with `ηKT` produced by it,
  while what is available is `cfg.δ ^ cfg.η ≤ fullness`; `cfg.hdims` bridges the two only
  through `cfg.a ≤ cfg.δ ^ cfg.exscal`, which needs `cfg.η ≤ cfg.exscal * ηKT`.
* **Unit-ball containment of the outer bodies.**  `Tube.UniformTubeSet` carries no such field
  for its nodes, and `cfg.contained` is about the `δ`-tubes only.

**And a fifth hypothesis, `hbudget`, which the four repairs above do not supply.**  The
conclusion reads the multiplicity at `δ^{ν/45} δ^{η} Δ_max` rather than at `Δ_max`; that is a
*strengthening* by `δ^{-(ν/45+η)(1-β)}`, and it must be paid for out of the gain `a^{-ν/90}`,
i.e. the estimate has to be invoked at the strictly smaller loss exponent
`ε₀ = ν/90 - (ν/45+η)(1-β)/exscal`.  The conversion from a power of `a` to a power of `δ`
passes through `cfg.a ≤ cfg.δ ^ cfg.exscal` and therefore costs the factor `cfg.exscal`, so
`ε₀ > 0` is exactly `hbudget`.  It is a relation between `ν`, `β`, `η` and `exscal` alone —
all fixed before `δ` — and it is *not* arrangeable by shrinking `δ`, contrary to the third
bullet of the docstring of `Kakeya.VeryNotSticky.coarseKatzTaoBound`. -/
theorem coarseKatzTaoBound_of_scaleBudget (cfg : VeryNotSticky.{u}) {ν : ℝ} (hν : 0 < ν)
    (hbudget : (ν / 45 + cfg.η) * (1 - cfg.β) ≤ cfg.exscal * (ν / 180)) :
    ∃ ηKT : ℝ, 0 < ηKT ∧ ∃ ρ₀ : NNReal, 0 < ρ₀ ∧
      ∀ (𝒰 : Tube.UniformTubeSet cfg.s (fun i ↦ (cfg.T i).toTube)
            (Tube.ssfGridLen cfg.δ) cfg.C₀) {k : ℕ}, k ≤ Tube.ssfGridLen cfg.δ →
        ∀ {ρ : NNReal}, Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k = ρ →
          ρ ∈ Set.Icc cfg.a 1 → ρ ≤ ρ₀ → 2 * cfg.η ≤ cfg.exscal * ηKT →
          ∀ (G : ShadedFactorFamily (EuclideanSpace ℝ (Fin 3)) cfg.ι cfg.ι),
            G.outerSet = cfg.activeTubeNodes 𝒰 k →
            (∀ j ∈ G.outerSet, (G.outerBody j).toConvexSpaceBody
                = (𝒰.cover.tube k j).toConvexSpaceBody) →
            (cfg.δ : NNReal) ^ (2 * cfg.η) ≤ ShadedBody.fullness G.outerSet G.outerBody →
            ShadedBody.multiplicity G.outerSet G.outerBody ≤
              (cfg.a : ENNReal) ^ (-(ν / 90)) *
                ((cfg.δ : ENNReal) ^ (ν / 45) *
                    ((cfg.δ : ENNReal) ^ cfg.η *
                      maxDensity (cfg.activeTubeNodes 𝒰 k)
                        (fun j ↦ (𝒰.cover.tube k j).toConvexSpaceBody))) ^
                  (1 - cfg.β) *
                (G.outerSet.card : ENNReal) ^ cfg.β := by
  classical
  set c : ℝ := (ν / 45 + cfg.η) * (1 - cfg.β) with hc_def
  have hβ1m : (0 : ℝ) ≤ 1 - cfg.β := by linarith [cfg.hβ1]
  have hc0 : 0 ≤ c := by
    rw [hc_def]
    have : (0 : ℝ) ≤ ν / 45 + cfg.η := by linarith [cfg.hη]
    exact mul_nonneg this hβ1m
  obtain ⟨ηKT, hηKT, ρ₀, hρ₀, H⟩ :=
    coarseKatzTaoBound_general cfg (ν := ν) (c := c) (ε₀ := ν / 180) (by linarith) (by linarith)
      (by rw [show ν / 90 - ν / 180 = ν / 180 by ring]; exact hbudget)
  refine ⟨ηKT, hηKT, ρ₀, hρ₀, ?_⟩
  intro 𝒰 k hk ρ hgrid hρ hρthr hηb G houterSet houterBody hfull
  refine le_trans (H 𝒰 hk hgrid hρ hρthr hηb G houterSet houterBody hfull) ?_
  set md : ENNReal := maxDensity (cfg.activeTubeNodes 𝒰 k)
    (fun j ↦ (𝒰.cover.tube k j).toConvexSpaceBody) with hmd_def
  have hδ0' : (cfg.δ : ENNReal) ≠ 0 := by
    simpa using (ENNReal.coe_ne_zero.mpr cfg.hδ.ne')
  have hδtop : (cfg.δ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hrw : ((cfg.δ : ENNReal) ^ (ν / 45) * ((cfg.δ : ENNReal) ^ cfg.η * md)) ^ (1 - cfg.β)
      = (cfg.δ : ENNReal) ^ c * md ^ (1 - cfg.β) := by
    rw [ENNReal.mul_rpow_of_nonneg _ _ hβ1m, ENNReal.mul_rpow_of_nonneg _ _ hβ1m,
      ← ENNReal.rpow_mul, ← ENNReal.rpow_mul, ← mul_assoc,
      ← ENNReal.rpow_add _ _ hδ0' hδtop]
    congr 2
    rw [hc_def]; ring
  rw [hrw]

/-- **The Katz–Tao estimate at the coarse family, at the `δ^{2η}` density slot** — the form
`Kakeya.VeryNotSticky.rScaleParentData_of_gridScale` actually needs, and the repaired form of
`Kakeya.VeryNotSticky.coarseKatzTaoBound`.

`Kakeya.VeryNotSticky.coarseKatzTaoBound_of_scaleBudget` above is the same statement with
`δ^{ν/45}` in the density slot, and it is **useless**: its `hbudget` reads
`(ν/45 + η)(1-β) < exscal · ν/90`, which together with `Kakeya.VeryNotSticky.CaseParams`
forces `β > 40/41`, while `Kakeya.katzTaoEstimateDimensionThree` applies Main Lemma 2 at every
`γ ∈ Set.Ioc 0 1`.  The `δ^{ν/45}` was inherited generosity: the only consumer of that factor
is the conversion of `ρ²` into `r²` in
`Kakeya.VeryNotSticky.rpow_mul_sq_le_sq_of_gridStep`, whose own proof passes through
`2η ≤ ν/45` and then throws the surplus away, so `δ^{2η}` suffices
(`Kakeya.VeryNotSticky.rpow_two_eta_mul_sq_le_sq_of_gridStep`).

With that slot the budget becomes `3η(1-β) < exscal · ν/90`, a bound on `η` alone once `ν`,
`β` and `exscal` are fixed, and `η` is chosen last: it is implied by `270η < exscal·ν`, and at
`β = 1/10`, `ζ = 2^30`, `exscal = 1/400`, `ϱ = 2^{-30}`, `η = 2^{-80}`, `τ = 2^{-13}`,
`τ' = 2^{-7}`, `ν = τ'β/2` it holds together with all twelve older fields of `CaseParams`. -/
theorem coarseKatzTaoBound_of_etaBudget (cfg : VeryNotSticky.{u}) {ν : ℝ} (hν : 0 < ν)
    (hηbudget : 3 * cfg.η * (1 - cfg.β) ≤ cfg.exscal * (ν / 180)) :
    ∃ ηKT : ℝ, 0 < ηKT ∧ ∃ ρ₀ : NNReal, 0 < ρ₀ ∧
      ∀ (𝒰 : Tube.UniformTubeSet cfg.s (fun i ↦ (cfg.T i).toTube)
            (Tube.ssfGridLen cfg.δ) cfg.C₀) {k : ℕ}, k ≤ Tube.ssfGridLen cfg.δ →
        ∀ {ρ : NNReal}, Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k = ρ →
          ρ ∈ Set.Icc cfg.a 1 → ρ ≤ ρ₀ → 2 * cfg.η ≤ cfg.exscal * ηKT →
          ∀ (G : ShadedFactorFamily (EuclideanSpace ℝ (Fin 3)) cfg.ι cfg.ι),
            G.outerSet = cfg.activeTubeNodes 𝒰 k →
            (∀ j ∈ G.outerSet, (G.outerBody j).toConvexSpaceBody
                = (𝒰.cover.tube k j).toConvexSpaceBody) →
            (cfg.δ : NNReal) ^ (2 * cfg.η) ≤ ShadedBody.fullness G.outerSet G.outerBody →
            ShadedBody.multiplicity G.outerSet G.outerBody ≤
              (cfg.a : ENNReal) ^ (-(ν / 90)) *
                ((cfg.δ : ENNReal) ^ (2 * cfg.η) *
                    ((cfg.δ : ENNReal) ^ cfg.η *
                      maxDensity (cfg.activeTubeNodes 𝒰 k)
                        (fun j ↦ (𝒰.cover.tube k j).toConvexSpaceBody))) ^
                  (1 - cfg.β) *
                (G.outerSet.card : ENNReal) ^ cfg.β := by
  classical
  set c : ℝ := 3 * cfg.η * (1 - cfg.β) with hc_def
  have hβ1m : (0 : ℝ) ≤ 1 - cfg.β := by linarith [cfg.hβ1]
  have hc0 : 0 ≤ c := by
    rw [hc_def]
    exact mul_nonneg (by linarith [cfg.hη]) hβ1m
  obtain ⟨ηKT, hηKT, ρ₀, hρ₀, H⟩ :=
    coarseKatzTaoBound_general cfg (ν := ν) (c := c) (ε₀ := ν / 180) (by linarith) (by linarith)
      (by rw [show ν / 90 - ν / 180 = ν / 180 by ring]; exact hηbudget)
  refine ⟨ηKT, hηKT, ρ₀, hρ₀, ?_⟩
  intro 𝒰 k hk ρ hgrid hρ hρthr hηb G houterSet houterBody hfull
  refine le_trans (H 𝒰 hk hgrid hρ hρthr hηb G houterSet houterBody hfull) ?_
  set md : ENNReal := maxDensity (cfg.activeTubeNodes 𝒰 k)
    (fun j ↦ (𝒰.cover.tube k j).toConvexSpaceBody) with hmd_def
  have hδ0' : (cfg.δ : ENNReal) ≠ 0 := by
    simpa using (ENNReal.coe_ne_zero.mpr cfg.hδ.ne')
  have hδtop : (cfg.δ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hrw : ((cfg.δ : ENNReal) ^ (2 * cfg.η) * ((cfg.δ : ENNReal) ^ cfg.η * md)) ^ (1 - cfg.β)
      = (cfg.δ : ENNReal) ^ c * md ^ (1 - cfg.β) := by
    rw [ENNReal.mul_rpow_of_nonneg _ _ hβ1m, ENNReal.mul_rpow_of_nonneg _ _ hβ1m,
      ← ENNReal.rpow_mul, ← ENNReal.rpow_mul, ← mul_assoc,
      ← ENNReal.rpow_add _ _ hδ0' hδtop]
    congr 2
    rw [hc_def]; ring
  rw [hrw]

/-- **The repaired coarse Katz–Tao estimate at the *named* thresholds** — the form a consumer
can actually apply.

`Kakeya.VeryNotSticky.coarseKatzTaoBound_of_etaBudget` above is the same estimate with its two
thresholds produced *existentially*, and in that shape it is unusable: a consumer that
`obtain`s `⟨ηKT, hηKT, ρ₀, hρ₀, H⟩` from it holds two opaque locals and can prove neither
`2 * cfg.η ≤ cfg.exscal * ηKT` nor `ρ ≤ ρ₀`, since neither is a statement about anything it
has.  Here the two are the *named* quantities `Kakeya.VeryNotSticky.coarseKTEta` and
`Kakeya.VeryNotSticky.coarseKTRadius`, functions of `(cfg.β, ν)` alone
(`Kakeya.DimensionThree.MainLemma2.KTWindowThresholds`), so both hypotheses are ordinary
comparisons that a caller can be asked for and a parameter package can carry:

* `hηKT : 2 * cfg.η ≤ cfg.exscal * coarseKTEta cfg.β ν` is an **upper bound on `cfg.η`** with a
  right-hand side fixed before `η` is chosen, hence of the shape
  `Kakeya.VeryNotSticky.CaseParams` already carries eight instances of;
* `hρ₀ : ρ ≤ coarseKTRadius cfg.β ν` is a smallness condition on the *node radius*, which
  `Kakeya.VeryNotSticky.rScaleParentData_of_gridScale` can reduce to one on `cfg.δ` through its
  own `hρr : ρ ≤ cfg.δ ^ (-cfg.η) * r` once `r` is known small.

**The binder shape is deliberately that of the refuted
`Kakeya.VeryNotSticky.coarseKatzTaoBound`**, curried and in the same order, with `hνη` replaced
by `hηbudget` and the two thresholds inserted: the single call site
`Kakeya.VeryNotSticky.rScaleParentData_of_gridScale` applies the refuted statement as
`coarseKatzTaoBound cfg hν hνη 𝒰 hk hgrid ⟨_, _⟩ G houterSet houterBody hfull`, and this
theorem is applicable there verbatim once those three hypotheses are available.

The conclusion is *identical* to that of `coarseKatzTaoBound_of_etaBudget`, at the `δ^{2η}`
density slot; only the packaging of the thresholds differs. -/
theorem coarseKatzTaoBound_of_etaBudget_atThresholds (cfg : VeryNotSticky.{u}) {ν : ℝ}
    (hν : 0 < ν)
    (hηbudget : 3 * cfg.η * (1 - cfg.β) ≤ cfg.exscal * (ν / 180))
    (hηKT : 2 * cfg.η ≤ cfg.exscal * coarseKTEta.{u} cfg.β ν)
    (𝒰 : Tube.UniformTubeSet cfg.s (fun i ↦ (cfg.T i).toTube)
      (Tube.ssfGridLen cfg.δ) cfg.C₀)
    {k : ℕ} (hk : k ≤ Tube.ssfGridLen cfg.δ)
    {ρ : NNReal} (hgrid : Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k = ρ)
    (hρ : ρ ∈ Set.Icc cfg.a 1) (hρ₀ : ρ ≤ coarseKTRadius.{u} cfg.β ν)
    (G : ShadedFactorFamily (EuclideanSpace ℝ (Fin 3)) cfg.ι cfg.ι)
    (houterSet : G.outerSet = cfg.activeTubeNodes 𝒰 k)
    (houterBody : ∀ j ∈ G.outerSet,
      (G.outerBody j).toConvexSpaceBody = (𝒰.cover.tube k j).toConvexSpaceBody)
    (hfull : (cfg.δ : NNReal) ^ (2 * cfg.η) ≤ ShadedBody.fullness G.outerSet G.outerBody) :
    ShadedBody.multiplicity G.outerSet G.outerBody ≤
      (cfg.a : ENNReal) ^ (-(ν / 90)) *
        ((cfg.δ : ENNReal) ^ (2 * cfg.η) *
            ((cfg.δ : ENNReal) ^ cfg.η *
              maxDensity (cfg.activeTubeNodes 𝒰 k)
                (fun j ↦ (𝒰.cover.tube k j).toConvexSpaceBody))) ^
          (1 - cfg.β) *
        (G.outerSet.card : ENNReal) ^ cfg.β := by
  classical
  set c : ℝ := 3 * cfg.η * (1 - cfg.β) with hc_def
  have hβ1m : (0 : ℝ) ≤ 1 - cfg.β := by linarith [cfg.hβ1]
  have hc0 : 0 ≤ c := by
    rw [hc_def]
    exact mul_nonneg (by linarith [cfg.hη]) hβ1m
  have hetapos : 0 < coarseKTEta.{u} cfg.β ν :=
    coarseKTEta_pos cfg.hβ.le cfg.hβ1 cfg.ktEstimate hν
  have H := coarseKatzTaoBound_general_at cfg (ν := ν) (c := c) (ε₀ := ν / 180)
    (by linarith) (by rw [show ν / 90 - ν / 180 = ν / 180 by ring]; exact hηbudget)
    hetapos (coarseKTRadius_le_half cfg.β ν)
    (coarseKT_windowFour cfg.hβ.le cfg.hβ1 cfg.ktEstimate hν)
    𝒰 hk hgrid hρ hρ₀ hηKT G houterSet houterBody hfull
  refine le_trans H ?_
  set md : ENNReal := maxDensity (cfg.activeTubeNodes 𝒰 k)
    (fun j ↦ (𝒰.cover.tube k j).toConvexSpaceBody) with hmd_def
  have hδ0' : (cfg.δ : ENNReal) ≠ 0 := by
    simpa using (ENNReal.coe_ne_zero.mpr cfg.hδ.ne')
  have hδtop : (cfg.δ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hrw : ((cfg.δ : ENNReal) ^ (2 * cfg.η) * ((cfg.δ : ENNReal) ^ cfg.η * md)) ^ (1 - cfg.β)
      = (cfg.δ : ENNReal) ^ c * md ^ (1 - cfg.β) := by
    rw [ENNReal.mul_rpow_of_nonneg _ _ hβ1m, ENNReal.mul_rpow_of_nonneg _ _ hβ1m,
      ← ENNReal.rpow_mul, ← ENNReal.rpow_mul, ← mul_assoc,
      ← ENNReal.rpow_add _ _ hδ0' hδtop]
    congr 2
    rw [hc_def]; ring
  rw [hrw]

/-- **The honest fullness conjunct converts to `δ^{3η}`, and to no less.**

`Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid` states its fullness conjunct at the
dimensional loss `ShadedBody.rhoTubesInducedFullnessLoss 3`, because GWZ write
`λ(𝕋_a, Y_{𝕋_a}) ⪆ λ` and §2.2 reads `⪆` as permitting a sub-polynomial factor.  The scale-`r`
layer consumes a `δ`-power instead, and this is the conversion: `Kakeya.VeryNotSticky.lam_ge`
gives `Cd δ^{2η} ≤ lam`, `Kakeya.VeryNotSticky.inducedFullnessLoss_absorb` gives
`L ≤ δ^{-η}`, and the two compose to `δ^{3η}`.

The one `η` is the price of honesty on the fullness side and it cannot be avoided: any loss `≥ 1`
has to be bridged against a `δ`-power by *some* smallness clause, and there is no room in
`lam_ge` — that clause and `Kakeya.VeryNotSticky.shading_lb` are exact duals through
`Cd⁻¹ lam`, so demanding `Cd · L · δ^{2η} ≤ lam` would demand a pointwise shading density of
`L δ^{2η}`, strictly more than the producer's input supplies.  The exponent budget, by contrast,
has room for six such (`Kakeya.VeryNotSticky.coarseLossExponentHeadroom`). -/
theorem rpow_three_eta_le_of_inducedFullness (cfg : VeryNotSticky.{u}) {κ : Type*}
    {t : Finset κ} {V : κ → ShadedBody (EuclideanSpace ℝ (Fin 3))}
    (hh : (cfg.Cd * _root_.ShadedBody.rhoTubesInducedFullnessLoss 3)⁻¹ * cfg.lam
      ≤ ShadedBody.fullness t V) :
    (cfg.δ : NNReal) ^ (3 * cfg.η) ≤ ShadedBody.fullness t V := by
  refine le_trans ?_ hh
  have habs : _root_.ShadedBody.rhoTubesInducedFullnessLoss 3 ≤ cfg.δ ^ (-cfg.η) := by
    have h := cfg.inducedFullnessLoss_absorb
    rw [← ENNReal.coe_rpow_of_ne_zero cfg.hδ.ne'] at h
    exact_mod_cast h
  have hCd0 : cfg.Cd ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one cfg.hCd)
  have hL0 : (0 : NNReal) < _root_.ShadedBody.rhoTubesInducedFullnessLoss 3 :=
    lt_of_lt_of_le zero_lt_one (_root_.ShadedBody.one_le_rhoTubesInducedFullnessLoss 3)
  have hδ0 : (cfg.δ : NNReal) ≠ 0 := cfg.hδ.ne'
  have hsplit : (cfg.δ : NNReal) ^ (-cfg.η) * (cfg.δ : NNReal) ^ (3 * cfg.η)
      = (cfg.δ : NNReal) ^ (2 * cfg.η) := by
    rw [← NNReal.rpow_add hδ0]
    congr 1
    ring
  have hkey : _root_.ShadedBody.rhoTubesInducedFullnessLoss 3 * (cfg.δ : NNReal) ^ (3 * cfg.η)
      ≤ (cfg.δ : NNReal) ^ (2 * cfg.η) := by
    calc _root_.ShadedBody.rhoTubesInducedFullnessLoss 3 * (cfg.δ : NNReal) ^ (3 * cfg.η)
        ≤ (cfg.δ : NNReal) ^ (-cfg.η) * (cfg.δ : NNReal) ^ (3 * cfg.η) := by gcongr
      _ = (cfg.δ : NNReal) ^ (2 * cfg.η) := hsplit
  have hstep : (cfg.δ : NNReal) ^ (3 * cfg.η)
      ≤ (_root_.ShadedBody.rhoTubesInducedFullnessLoss 3)⁻¹ * (cfg.δ : NNReal) ^ (2 * cfg.η) := by
    rw [le_inv_mul_iff₀ hL0]
    exact hkey
  refine le_trans hstep ?_
  calc (_root_.ShadedBody.rhoTubesInducedFullnessLoss 3)⁻¹ * (cfg.δ : NNReal) ^ (2 * cfg.η)
      = (cfg.Cd * _root_.ShadedBody.rhoTubesInducedFullnessLoss 3)⁻¹
          * (cfg.Cd * (cfg.δ : NNReal) ^ (2 * cfg.η)) := by
        rw [mul_inv]
        field_simp
    _ ≤ (cfg.Cd * _root_.ShadedBody.rhoTubesInducedFullnessLoss 3)⁻¹ * cfg.lam := by
        gcongr
        exact cfg.lam_ge

/-- **`Kakeya.VeryNotSticky.coarseKatzTaoBound_of_etaBudget_atPair` with the fullness exponent
left free.**  The `2 cfg.η` form is this one at `e := 2 * cfg.η`; the honest coarse family needs
it at `e := 3 * cfg.η`. -/
theorem coarseKatzTaoBound_of_etaBudget_atPair_atFullness (cfg : VeryNotSticky.{u})
    {ν ε₀ ηKT e : ℝ}
    {ρ₀ : NNReal} (hε₀ν : ε₀ ≤ ν / 90)
    (hηbudget : 3 * cfg.η * (1 - cfg.β) ≤ cfg.exscal * (ν / 90 - ε₀))
    (hηKT : 0 < ηKT) (hρ₀half : ρ₀ ≤ 1 / 2)
    (hW : WindowFour.{u} (EuclideanSpace ℝ (Fin 3)) cfg.β ε₀ ηKT ρ₀)
    (𝒰 : Tube.UniformTubeSet cfg.s (fun i ↦ (cfg.T i).toTube)
      (Tube.ssfGridLen cfg.δ) cfg.C₀)
    {k : ℕ} (hk : k ≤ Tube.ssfGridLen cfg.δ)
    {ρ : NNReal} (hgrid : Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k = ρ)
    (hρ : ρ ∈ Set.Icc cfg.a 1) (hρ₀ : ρ ≤ ρ₀) (hηb : e ≤ cfg.exscal * ηKT)
    (G : ShadedFactorFamily (EuclideanSpace ℝ (Fin 3)) cfg.ι cfg.ι)
    (houterSet : G.outerSet = cfg.activeTubeNodes 𝒰 k)
    (houterBody : ∀ j ∈ G.outerSet, (G.outerBody j).toConvexSpaceBody
        = (𝒰.cover.tube k j).toConvexSpaceBody)
    (hfull : (cfg.δ : NNReal) ^ e ≤ ShadedBody.fullness G.outerSet G.outerBody) :
    ShadedBody.multiplicity G.outerSet G.outerBody ≤
      (cfg.a : ENNReal) ^ (-(ν / 90)) *
        ((cfg.δ : ENNReal) ^ (2 * cfg.η) *
            ((cfg.δ : ENNReal) ^ cfg.η *
              maxDensity (cfg.activeTubeNodes 𝒰 k)
                (fun j ↦ (𝒰.cover.tube k j).toConvexSpaceBody))) ^
          (1 - cfg.β) *
        (G.outerSet.card : ENNReal) ^ cfg.β := by
  classical
  set c : ℝ := 3 * cfg.η * (1 - cfg.β) with hc_def
  have hβ1m : (0 : ℝ) ≤ 1 - cfg.β := by linarith [cfg.hβ1]
  have H := coarseKatzTaoBound_general_atFullness cfg (ν := ν) (c := c) (ε₀ := ε₀) (e := e)
    hε₀ν hηbudget hηKT hρ₀half hW 𝒰 hk hgrid hρ hρ₀ hηb G houterSet houterBody hfull
  refine le_trans H ?_
  set md : ENNReal := maxDensity (cfg.activeTubeNodes 𝒰 k)
    (fun j ↦ (𝒰.cover.tube k j).toConvexSpaceBody) with hmd_def
  have hδ0' : (cfg.δ : ENNReal) ≠ 0 := by
    simpa using (ENNReal.coe_ne_zero.mpr cfg.hδ.ne')
  have hδtop : (cfg.δ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hrw : ((cfg.δ : ENNReal) ^ (2 * cfg.η) * ((cfg.δ : ENNReal) ^ cfg.η * md)) ^ (1 - cfg.β)
      = (cfg.δ : ENNReal) ^ c * md ^ (1 - cfg.β) := by
    rw [ENNReal.mul_rpow_of_nonneg _ _ hβ1m, ENNReal.mul_rpow_of_nonneg _ _ hβ1m,
      ← ENNReal.rpow_mul, ← ENNReal.rpow_mul, ← mul_assoc,
      ← ENNReal.rpow_add _ _ hδ0' hδtop]
    congr 2
    rw [hc_def]; ring
  rw [hrw]

/-- **The repaired coarse Katz--Tao estimate at an *arbitrary* threshold pair.**

`Kakeya.VeryNotSticky.coarseKatzTaoBound_of_etaBudget_atThresholds` is this theorem instantiated
at the Skolem pair `(coarseKTEta cfg.β ν, coarseKTRadius cfg.β ν)`.  Taking the pair as a
parameter is what lets the `β`-uniform route instantiate at
`Kakeya.windowPairData`, whose components do not move with `β`.

The conclusion is identical; only the packaging of the thresholds differs.  The proof is
`Kakeya.VeryNotSticky.coarseKatzTaoBound_general_at` at `c = 3η(1-β)` followed by the same
`δ^{2η}` regrouping that `coarseKatzTaoBound_of_etaBudget_atThresholds` performs. -/
theorem coarseKatzTaoBound_of_etaBudget_atPair (cfg : VeryNotSticky.{u}) {ν ε₀ ηKT : ℝ}
    {ρ₀ : NNReal} (hε₀ν : ε₀ ≤ ν / 90)
    (hηbudget : 3 * cfg.η * (1 - cfg.β) ≤ cfg.exscal * (ν / 90 - ε₀))
    (hηKT : 0 < ηKT) (hρ₀half : ρ₀ ≤ 1 / 2)
    (hW : WindowFour.{u} (EuclideanSpace ℝ (Fin 3)) cfg.β ε₀ ηKT ρ₀)
    (𝒰 : Tube.UniformTubeSet cfg.s (fun i ↦ (cfg.T i).toTube)
      (Tube.ssfGridLen cfg.δ) cfg.C₀)
    {k : ℕ} (hk : k ≤ Tube.ssfGridLen cfg.δ)
    {ρ : NNReal} (hgrid : Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k = ρ)
    (hρ : ρ ∈ Set.Icc cfg.a 1) (hρ₀ : ρ ≤ ρ₀) (hηb : 2 * cfg.η ≤ cfg.exscal * ηKT)
    (G : ShadedFactorFamily (EuclideanSpace ℝ (Fin 3)) cfg.ι cfg.ι)
    (houterSet : G.outerSet = cfg.activeTubeNodes 𝒰 k)
    (houterBody : ∀ j ∈ G.outerSet, (G.outerBody j).toConvexSpaceBody
        = (𝒰.cover.tube k j).toConvexSpaceBody)
    (hfull : (cfg.δ : NNReal) ^ (2 * cfg.η) ≤ ShadedBody.fullness G.outerSet G.outerBody) :
    ShadedBody.multiplicity G.outerSet G.outerBody ≤
      (cfg.a : ENNReal) ^ (-(ν / 90)) *
        ((cfg.δ : ENNReal) ^ (2 * cfg.η) *
            ((cfg.δ : ENNReal) ^ cfg.η *
              maxDensity (cfg.activeTubeNodes 𝒰 k)
                (fun j ↦ (𝒰.cover.tube k j).toConvexSpaceBody))) ^
          (1 - cfg.β) *
        (G.outerSet.card : ENNReal) ^ cfg.β := by
  classical
  set c : ℝ := 3 * cfg.η * (1 - cfg.β) with hc_def
  have hβ1m : (0 : ℝ) ≤ 1 - cfg.β := by linarith [cfg.hβ1]
  have H := coarseKatzTaoBound_general_at cfg (ν := ν) (c := c) (ε₀ := ε₀) hε₀ν hηbudget
    hηKT hρ₀half hW 𝒰 hk hgrid hρ hρ₀ hηb G houterSet houterBody hfull
  refine le_trans H ?_
  set md : ENNReal := maxDensity (cfg.activeTubeNodes 𝒰 k)
    (fun j ↦ (𝒰.cover.tube k j).toConvexSpaceBody) with hmd_def
  have hδ0' : (cfg.δ : ENNReal) ≠ 0 := by
    simpa using (ENNReal.coe_ne_zero.mpr cfg.hδ.ne')
  have hδtop : (cfg.δ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hrw : ((cfg.δ : ENNReal) ^ (2 * cfg.η) * ((cfg.δ : ENNReal) ^ cfg.η * md)) ^ (1 - cfg.β)
      = (cfg.δ : ENNReal) ^ c * md ^ (1 - cfg.β) := by
    rw [ENNReal.mul_rpow_of_nonneg _ _ hβ1m, ENNReal.mul_rpow_of_nonneg _ _ hβ1m,
      ← ENNReal.rpow_mul, ← ENNReal.rpow_mul, ← mul_assoc,
      ← ENNReal.rpow_add _ _ hδ0' hδtop]
    congr 2
    rw [hc_def]; ring
  rw [hrw]

/-! ## What each conjunct of the residue costs, taken one at a time

Three realisations of the **full** active node family, each with an explicit outer shading.

* `Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid_saturated` shades every node tube
  entirely: outer fullness `1`, so every conjunct of
  `Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid` except the ball estimate holds, and the
  ball estimate is destroyed because the outer union becomes the whole of `⋃ 𝕋_ρ`.
* `Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid_minimal` shades each node tube by its
  intersection with the *inner* union `U(𝕋, Y)` — the smallest shading the `ShadedFactorFamily`
  clauses permit once the inner bodies are pinned. The outer union then *equals* the inner union,
  so the ball estimate is immediate and the fullness is destroyed.
* `Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid_inducedFullness` uses GWZ's own coarse
  shading `Y_{𝕋_ρ}(T_ρ) = T_ρ ∩ N_{2ρ}(⋃_{T ∈ 𝕋[T_ρ]} Y(T))` and is the *honest* fullness
  statement: it charges `ShadedBody.rhoTubesInducedFullnessLoss 3`, the dimensional constant of
  `Kakeya.Tube.volume_dilate_inter_cthickening_ge`, which is what GWZ Lemma 5.11's fullness
  clause actually costs.

The first two say that **neither conjunct of the residue is on its own the obstruction, and that
the placeholder constant is not the obstruction either**: both are realised at the strongest
constant, `1`. The obstruction is the *joint* demand at a single shading, which is the
un-pigeonholed two-scale (Córdoba) estimate; see the residue's docstring.

The third is the honest replacement for the fullness conjunct: it is the one clause of Lemma 5.11
that survives the passage from the pigeonholed subfamily to the full node family, and it survives
at a purely dimensional loss. It comes from
`ShadedBody.exists_rhoTubesSection9_fullFamily`.
-/

/-- **The per-tube shading density never exceeds its own comparison constant**, `lam ≤ Cd`.

Immediate from `Kakeya.VeryNotSticky.shading_lb` and `Y(T) ⊆ T` at any one tube of the family,
which is nonempty by `Kakeya.VeryNotSticky.tube_count`. It is the reason the fullness conjunct of
`Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid` is not, by itself, an obstruction, at any
loss constant `C ≥ 1` and in particular at the placeholder `C = 1`: `ShadedBody.fullness` is at
most `1`, and `(Cd · C)⁻¹ · lam ≤ Cd⁻¹ · lam ≤ 1`. -/
theorem lam_le_Cd (cfg : VeryNotSticky.{u}) : cfg.lam ≤ cfg.Cd := by
  have hs : cfg.s.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    have := cfg.tube_count
    rw [h] at this
    simp at this
  obtain ⟨i₀, hi₀⟩ := hs
  have hpos : 0 < volume ((cfg.T i₀).toShadedBody.carrier) := by
    have h := _root_.Tube.le_volume (cfg.T i₀).toTube
    refine lt_of_lt_of_le ?_ (by simpa using h)
    have hc : (0 : ENNReal) < (_root_.Tube.le_volume.c 3 : ENNReal) :=
      ENNReal.coe_pos.mpr (_root_.Tube.le_volume.c_pos _)
    have hδp : (0 : ENNReal) < (cfg.δ : ENNReal) ^ 2 :=
      ENNReal.pow_pos (ENNReal.coe_pos.mpr cfg.hδ) _
    exact ENNReal.mul_pos (ne_of_gt hc) (ne_of_gt hδp)
  have hfin : volume ((cfg.T i₀).toShadedBody.carrier) ≠ ⊤ :=
    ((cfg.T i₀).toShadedBody.toConvexSpaceBody.isCompact'.measure_lt_top).ne
  have hCd0 : (cfg.Cd : ENNReal) ≠ 0 :=
    (ENNReal.coe_pos.mpr (lt_of_lt_of_le zero_lt_one cfg.hCd)).ne'
  have hCdtop : (cfg.Cd : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have h1 := cfg.shading_lb i₀ hi₀
  have h2 : volume ((cfg.T i₀).toShadedBody.shade) ≤
      volume ((cfg.T i₀).toShadedBody.carrier) :=
    measure_mono (cfg.T i₀).toShadedBody.shade_subset
  have h3 : (cfg.Cd : ENNReal)⁻¹ *
      ((cfg.lam : ENNReal) * volume ((cfg.T i₀).toShadedBody.carrier)) ≤
      volume ((cfg.T i₀).toShadedBody.carrier) := le_trans h1 h2
  have h4 : (cfg.lam : ENNReal) * volume ((cfg.T i₀).toShadedBody.carrier) ≤
      (cfg.Cd : ENNReal) * volume ((cfg.T i₀).toShadedBody.carrier) := by
    have h : (cfg.Cd : ENNReal) *
        ((cfg.Cd : ENNReal)⁻¹ *
          ((cfg.lam : ENNReal) * volume ((cfg.T i₀).toShadedBody.carrier))) ≤
        (cfg.Cd : ENNReal) * volume ((cfg.T i₀).toShadedBody.carrier) := by gcongr
    rwa [← mul_assoc, ENNReal.mul_inv_cancel hCd0 hCdtop, one_mul] at h
  have h5 : (cfg.lam : ENNReal) ≤ (cfg.Cd : ENNReal) :=
    (ENNReal.mul_le_mul_iff_left hpos.ne' hfin).mp h4
  exact_mod_cast h5

/-- **The residue's fullness conjunct alone, at the full node family, at loss `1`.**

Every conjunct of `Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid` except the ball
estimate, realised by shading each node tube *entirely*. The outer fullness is then `1`, so the
conjunct is delivered here at `Cd⁻¹ · lam`, which by `Kakeya.VeryNotSticky.lam_le_Cd` is at most
`1` and which dominates `(Cd · C)⁻¹ · lam` for every loss constant `C ≥ 1` — in particular for
the placeholder `1`.

The point of the lemma is negative, and it is what distinguishes this residue from
`Kakeya.VeryNotSticky.coarseKatzTaoBound`: the fullness conjunct, and in particular the loss
constant it carries, is **not** what makes the residue hard, so no refutation of the residue can
be extracted from that conjunct. What this shading destroys is the ball conjunct, whose outer
union `U(𝕋_ρ, Y_{𝕋_ρ})` is now the whole of `⋃ 𝕋_ρ`.

This is *not* a witness for GWZ Lemma 5.11: the shading it uses is the saturated one, not
GWZ's `Y_{𝕋_ρ}`. For the honest fullness statement, at GWZ's own coarse shading and at the loss
Lemma 5.11 charges, see
`Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid_inducedFullness`. -/
theorem exists_coarseShadedFamilyAtGrid_saturated (cfg : VeryNotSticky.{u})
    (𝒱 : ShadedTube.ShadedUniformTubeSet cfg.s cfg.T (Tube.ssfGridLen cfg.δ) cfg.C₀)
    {k : ℕ} (hk : k ≤ Tube.ssfGridLen cfg.δ) :
    ∃ G : ShadedFactorFamily (EuclideanSpace ℝ (Fin 3)) cfg.ι cfg.ι,
      G.innerSet = cfg.s ∧
      (∀ i ∈ cfg.s, G.innerBody i = (cfg.T i).toShadedBody) ∧
      G.outerSet = cfg.activeTubeNodes 𝒱.tubeUniform k ∧
      (∀ j ∈ G.outerSet,
        (G.outerBody j).toConvexSpaceBody =
          (𝒱.tubeUniform.cover.tube k j).toConvexSpaceBody) ∧
      cfg.Cd⁻¹ * cfg.lam ≤ ShadedBody.fullness G.outerSet G.outerBody := by
  classical
  set W : cfg.ι → ShadedBody (EuclideanSpace ℝ (Fin 3)) := fun j =>
    { toConvexSpaceBody := (𝒱.tubeUniform.cover.tube k j).toConvexSpaceBody
      shade := (𝒱.tubeUniform.cover.tube k j).toConvexSpaceBody.carrier
      measurableSet_shade :=
        (𝒱.tubeUniform.cover.tube k j).toConvexSpaceBody.isCompact'.isClosed.measurableSet
      shade_subset := subset_rfl } with hW
  have hs : cfg.s.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    have := cfg.tube_count
    rw [h] at this
    simp at this
  obtain ⟨i₀, hi₀⟩ := hs
  have hparent_mem : ∀ i ∈ cfg.s, 𝒱.tubeUniform.cover.assign k i
      ∈ cfg.activeTubeNodes 𝒱.tubeUniform k := by
    intro i hi
    rw [activeTubeNodes, Finset.mem_filter]
    refine ⟨𝒱.tubeUniform.cover.assign_mem k hk i hi, ⟨i, ?_⟩⟩
    simp [tubeFibre, Tube.coverClass, hi]
  have hinner_le : ∀ i ∈ cfg.s,
      ((cfg.T i).toShadedBody).toConvexSpaceBody ≤
        (W (𝒱.tubeUniform.cover.assign k i)).toConvexSpaceBody := by
    intro i hi
    simpa using 𝒱.tubeUniform.cover.le_tube_assign k hk i hi
  have hshade_sub : ∀ i ∈ cfg.s,
      ((cfg.T i).toShadedBody).shade ⊆ (W (𝒱.tubeUniform.cover.assign k i)).shade := by
    intro i hi
    exact fun x hx => (hinner_le i hi) ((cfg.T i).toShadedBody.shade_subset hx)
  -- the total carrier volume of the active node family is positive and finite
  have hmem : 𝒱.tubeUniform.cover.assign k i₀ ∈ cfg.activeTubeNodes 𝒱.tubeUniform k :=
    hparent_mem i₀ hi₀
  have hsum0 : (∑ j ∈ cfg.activeTubeNodes 𝒱.tubeUniform k, volume (W j).carrier) ≠ 0 := by
    have hpos : 0 < volume ((cfg.T i₀).toShadedBody.carrier) := by
      have h := _root_.Tube.le_volume (cfg.T i₀).toTube
      refine lt_of_lt_of_le ?_ (by simpa using h)
      have hc : (0 : ENNReal) < (_root_.Tube.le_volume.c 3 : ENNReal) :=
        ENNReal.coe_pos.mpr (_root_.Tube.le_volume.c_pos _)
      have hδp : (0 : ENNReal) < (cfg.δ : ENNReal) ^ 2 :=
        ENNReal.pow_pos (ENNReal.coe_pos.mpr cfg.hδ) _
      exact ENNReal.mul_pos (ne_of_gt hc) (ne_of_gt hδp)
    have hle : volume ((cfg.T i₀).toShadedBody.carrier) ≤
        volume (W (𝒱.tubeUniform.cover.assign k i₀)).carrier :=
      measure_mono (hinner_le i₀ hi₀)
    intro h
    rw [Finset.sum_eq_zero_iff] at h
    exact absurd (h _ hmem) (ne_of_gt (lt_of_lt_of_le hpos hle))
  have hsumtop : (∑ j ∈ cfg.activeTubeNodes 𝒱.tubeUniform k, volume (W j).carrier) ≠ ⊤ := by
    refine (lt_top_iff_ne_top.mp ?_)
    refine ENNReal.sum_lt_top.mpr (fun j _ => ?_)
    exact (𝒱.tubeUniform.cover.tube k j).toConvexSpaceBody.isCompact'.measure_lt_top
  have hfull : ShadedBody.fullness (cfg.activeTubeNodes 𝒱.tubeUniform k) W = 1 := by
    have : ((ShadedBody.fullness (cfg.activeTubeNodes 𝒱.tubeUniform k) W : NNReal) : ENNReal)
        = 1 := by
      rw [ShadedBody.fullness_def]
      exact ENNReal.div_self hsum0 hsumtop
    exact_mod_cast this
  refine ⟨{ innerSet := cfg.s
            innerBody := fun i => (cfg.T i).toShadedBody
            outerSet := cfg.activeTubeNodes 𝒱.tubeUniform k
            outerBody := W
            parent := 𝒱.tubeUniform.cover.assign k
            parent_mem := hparent_mem
            inner_le_parent := hinner_le
            shade_subset_parent := hshade_sub }, rfl, fun i _ => rfl, rfl, fun j _ => rfl, ?_⟩
  rw [hfull]
  have hCd0 : cfg.Cd ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one cfg.hCd)
  calc cfg.Cd⁻¹ * cfg.lam ≤ cfg.Cd⁻¹ * cfg.Cd := by gcongr; exact cfg.lam_le_Cd
    _ = 1 := inv_mul_cancel₀ hCd0

/-- **The honest fullness clause of GWZ Lemma 5.11, on the full active node family.**

`ShadedBody.exists_rhoTubesSection9_fullFamily` at the configuration's own hierarchy: the coarse
family is `𝕋_ρ = cfg.activeTubeNodes 𝒱.tubeUniform k` **on the nose**, the fine pair is
`(cfg.s, cfg.T)` **on the nose**, the parent map is the hierarchy's own assignment, and the coarse
shading is GWZ's `Y_{𝕋_ρ}(T_ρ) = T_ρ ∩ N_{2ρ}(⋃_{T ∈ 𝕋[T_ρ]} Y(T))`.

**This is the honest restatement of the fullness conjunct of
`Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid`.** That conjunct is written against the
placeholder `Kakeya.ShadedBody.shadingMultiplicityEstimateForRhoTubes.C = 1`, i.e. against the
assertion that the fullness transfer from `(𝕋, Y)` to `(𝕋_ρ, Y_{𝕋_ρ})` is *lossless*. It is not,
at any parameter value: the transfer is `Kakeya.Tube.volume_dilate_inter_cthickening_ge` read at
dilation `c = 1`, a
`≳` and not an `=`, and the loss it charges is
`ShadedBody.rhoTubesInducedFullnessLoss 3 = max 1 (Kakeya.Tube.dilateFullness.C 3)`. The loss
here is *purely dimensional* — it involves neither `δ` nor `|𝕋|` — because the fullness clause
alone needs no pigeonholing; that is why this statement, unlike the ball conjunct, extends from
the pigeonholed subfamily of
`Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid_subfamily` to the full node family.

The hypothesis `hρ` is the range `[δ, 1]` of GWZ Lemma 5.11 and is supplied by the rounding, as
in the residue. Nonemptiness of the node family and of every node's fibre — the `hactive` of
`ShadedBody.exists_rhoTubesSection9_fullFamily`, which may not be dropped because a node with an
empty fibre carries an empty induced shading — are both immediate from
`Kakeya.VeryNotSticky.activeTubeNodes` being the *filter* on nonempty fibres and from
`Kakeya.VeryNotSticky.tube_count`. -/
theorem exists_coarseShadedFamilyAtGrid_inducedFullness (cfg : VeryNotSticky.{u})
    (𝒱 : ShadedTube.ShadedUniformTubeSet cfg.s cfg.T (Tube.ssfGridLen cfg.δ) cfg.C₀)
    {k : ℕ} (hk : k ≤ Tube.ssfGridLen cfg.δ)
    {ρ : NNReal} (hgrid : Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k = ρ)
    (hρ : ρ ∈ Set.Icc cfg.δ 1) :
    ∃ G : ShadedFactorFamily (EuclideanSpace ℝ (Fin 3)) cfg.ι cfg.ι,
      G.innerSet = cfg.s ∧
      (∀ i ∈ cfg.s, G.innerBody i = (cfg.T i).toShadedBody) ∧
      G.outerSet = cfg.activeTubeNodes 𝒱.tubeUniform k ∧
      G.parent = 𝒱.tubeUniform.cover.assign k ∧
      (∀ j ∈ G.outerSet,
        (G.outerBody j).toConvexSpaceBody =
          (𝒱.tubeUniform.cover.tube k j).toConvexSpaceBody) ∧
      (cfg.Cd * ShadedBody.rhoTubesInducedFullnessLoss 3)⁻¹ * cfg.lam ≤
        ShadedBody.fullness G.outerSet G.outerBody := by
  classical
  subst hgrid
  have hs : cfg.s.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    have := cfg.tube_count
    rw [h] at this
    simp at this
  obtain ⟨i₀, hi₀⟩ := hs
  have hmaps : ∀ i ∈ cfg.s, 𝒱.tubeUniform.cover.assign k i
      ∈ cfg.activeTubeNodes 𝒱.tubeUniform k := by
    intro i hi
    rw [activeTubeNodes, Finset.mem_filter]
    refine ⟨𝒱.tubeUniform.cover.assign_mem k hk i hi, ⟨i, ?_⟩⟩
    simp [tubeFibre, Tube.coverClass, hi]
  have hle : ∀ i ∈ cfg.s,
      (cfg.T i).toConvexSpaceBody ≤
        (𝒱.tubeUniform.cover.tube k (𝒱.tubeUniform.cover.assign k i)).toConvexSpaceBody := by
    intro i hi
    simpa using 𝒱.tubeUniform.cover.le_tube_assign k hk i hi
  have hactive : ∀ j ∈ cfg.activeTubeNodes 𝒱.tubeUniform k,
      ∃ i ∈ cfg.s, 𝒱.tubeUniform.cover.assign k i = j := by
    intro j hj
    rw [activeTubeNodes, Finset.mem_filter] at hj
    obtain ⟨i, hi⟩ := hj.2
    rw [tubeFibre, Tube.coverClass, Finset.mem_filter] at hi
    exact ⟨i, hi.1, hi.2⟩
  have ht : (cfg.activeTubeNodes 𝒱.tubeUniform k).Nonempty :=
    ⟨𝒱.tubeUniform.cover.assign k i₀, hmaps i₀ hi₀⟩
  have hCd : cfg.Cd ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one cfg.hCd)
  have hfr : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
  obtain ⟨G, h1, h2, h3, h4, h5, h6⟩ :=
    _root_.ShadedBody.exists_rhoTubesSection9_fullFamily
      (E := EuclideanSpace ℝ (Fin 3)) (δ := cfg.δ) (Cd := cfg.Cd) (lam := cfg.lam)
      cfg.hδ hρ hCd cfg.T (𝒱.tubeUniform.cover.tube k) (𝒱.tubeUniform.cover.assign k)
      hmaps hle hactive ht cfg.shading_lb
  refine ⟨G, h1, fun i _ => h2 i, h3, h4, fun j _ => h5 j, ?_⟩
  rwa [hfr] at h6

/-- **The residue's ball conjunct alone, at the full node family.**

Every conjunct of `Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid` except the outer
fullness, realised by the *minimal* admissible outer shading: each node tube is shaded by its
intersection with the inner shaded union `U(𝕋, Y)`. That is the smallest set a
`Kakeya.ShadedBody.ShadedFactorFamily` clause `shade_subset_parent` permits once the inner
bodies are pinned to `(cfg.T i).toShadedBody` on the nose, and it makes the outer union *equal*
to the inner union, so the ball estimate degenerates to `δ^η · |U| · d ≤ |U|` with `d ≤ 1`.

It is stated with **no** loss constant on the small side, which is stronger than the residue's
ball conjunct at any `C ≥ 1` and in particular at the placeholder `1`; so, as with
`Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid_saturated`, no refutation of the residue
can be extracted from this conjunct either.

Read together with that lemma this locates the residue precisely: both conjuncts are
individually realisable at the full node family, by explicit shadings, and at loss `1`. What is
open is that a *single* shading must satisfy both, i.e. that the outer union can be made
`lam`-full of the node family without growing past what the inner union's local density can pay
for. That is the un-pigeonholed two-scale estimate, and it is exactly the clause of GWZ
Lemma 5.11 that `ShadedBody.exists_rhoTubesSection9_fullFamily` does not extend to the full
family. -/
theorem exists_coarseShadedFamilyAtGrid_minimal (cfg : VeryNotSticky.{u})
    (𝒱 : ShadedTube.ShadedUniformTubeSet cfg.s cfg.T (Tube.ssfGridLen cfg.δ) cfg.C₀)
    {k : ℕ} (hk : k ≤ Tube.ssfGridLen cfg.δ)
    {ρ : NNReal} (hgrid : Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k = ρ)
    (hρ : ρ ∈ Set.Icc cfg.δ 1) :
    ∃ G : ShadedFactorFamily (EuclideanSpace ℝ (Fin 3)) cfg.ι cfg.ι,
      G.innerSet = cfg.s ∧
      (∀ i ∈ cfg.s, G.innerBody i = (cfg.T i).toShadedBody) ∧
      G.outerSet = cfg.activeTubeNodes 𝒱.tubeUniform k ∧
      (∀ j ∈ G.outerSet,
        (G.outerBody j).toConvexSpaceBody =
          (𝒱.tubeUniform.cover.tube k j).toConvexSpaceBody) ∧
      (∀ x ∈ ⋃ j ∈ G.outerSet, (G.outerBody j).shade,
        (cfg.δ : ENNReal) ^ cfg.η *
            (volume (⋃ j ∈ G.outerSet, (G.outerBody j).shade) *
              (volume ((⋃ i ∈ G.innerSet, (G.innerBody i).shade) ∩ ball x (ρ : ℝ)) /
                volume (ball x (ρ : ℝ)))) ≤
          volume (⋃ i ∈ G.innerSet, (G.innerBody i).shade)) := by
  classical
  subst hgrid
  set Uin : Set (EuclideanSpace ℝ (Fin 3)) := ⋃ i ∈ cfg.s, (cfg.T i).toShadedBody.shade with hUin
  have hUinMeas : MeasurableSet Uin := by
    rw [hUin]
    exact Finset.measurableSet_biUnion _ (fun i _ => (cfg.T i).measurableSet_shade)
  set W : cfg.ι → ShadedBody (EuclideanSpace ℝ (Fin 3)) := fun j =>
    { toConvexSpaceBody := (𝒱.tubeUniform.cover.tube k j).toConvexSpaceBody
      shade := (𝒱.tubeUniform.cover.tube k j).toConvexSpaceBody.carrier ∩ Uin
      measurableSet_shade :=
        ((𝒱.tubeUniform.cover.tube k j).toConvexSpaceBody.isCompact'.isClosed.measurableSet).inter
          hUinMeas
      shade_subset := Set.inter_subset_left } with hW
  have hparent_mem : ∀ i ∈ cfg.s, 𝒱.tubeUniform.cover.assign k i
      ∈ cfg.activeTubeNodes 𝒱.tubeUniform k := by
    intro i hi
    rw [activeTubeNodes, Finset.mem_filter]
    refine ⟨𝒱.tubeUniform.cover.assign_mem k hk i hi, ⟨i, ?_⟩⟩
    simp [tubeFibre, Tube.coverClass, hi]
  have hinner_le : ∀ i ∈ cfg.s,
      ((cfg.T i).toShadedBody).toConvexSpaceBody ≤
        (W (𝒱.tubeUniform.cover.assign k i)).toConvexSpaceBody := by
    intro i hi
    simpa using 𝒱.tubeUniform.cover.le_tube_assign k hk i hi
  have hshade_sub : ∀ i ∈ cfg.s,
      ((cfg.T i).toShadedBody).shade ⊆ (W (𝒱.tubeUniform.cover.assign k i)).shade := by
    intro i hi x hx
    refine ⟨?_, ?_⟩
    · exact (hinner_le i hi) ((cfg.T i).toShadedBody.shade_subset hx)
    · rw [hUin]
      exact Set.mem_biUnion hi hx
  -- the outer union is exactly the inner union, which is what trivialises the ball conjunct
  have hunion : (⋃ j ∈ cfg.activeTubeNodes 𝒱.tubeUniform k, (W j).shade) = Uin := by
    apply Set.Subset.antisymm
    · refine Set.iUnion₂_subset (fun j _ => ?_)
      exact Set.inter_subset_right
    · intro x hx
      rw [hUin] at hx
      obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp hx
      exact Set.mem_biUnion (hparent_mem i hi) (hshade_sub i hi hxi)
  have hδη : (cfg.δ : ENNReal) ^ cfg.η ≤ 1 :=
    ENNReal.rpow_le_one (by exact_mod_cast cfg.hδ1) cfg.hη.le
  have hball : ∀ x ∈ ⋃ j ∈ cfg.activeTubeNodes 𝒱.tubeUniform k, (W j).shade,
      (cfg.δ : ENNReal) ^ cfg.η *
          (volume (⋃ j ∈ cfg.activeTubeNodes 𝒱.tubeUniform k, (W j).shade) *
            (volume (Uin ∩ ball x (Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k : ℝ)) /
              volume (ball x (Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k : ℝ)))) ≤
        volume Uin := by
    intro x _
    rw [hunion]
    have hdens :
        volume (Uin ∩ ball x (Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k : ℝ)) /
            volume (ball x (Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k : ℝ)) ≤ 1 :=
      ENNReal.div_le_of_le_mul
        (by
          rw [one_mul]
          exact measure_mono (μ := (volume : Measure (EuclideanSpace ℝ (Fin 3))))
            Set.inter_subset_right)
    calc (cfg.δ : ENNReal) ^ cfg.η *
            (volume Uin *
              (volume (Uin ∩ ball x (Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k : ℝ)) /
                volume (ball x (Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k : ℝ))))
        ≤ 1 * (volume Uin * 1) := by gcongr
      _ = volume Uin := by rw [mul_one, one_mul]
  exact ⟨{ innerSet := cfg.s
           innerBody := fun i => (cfg.T i).toShadedBody
           outerSet := cfg.activeTubeNodes 𝒱.tubeUniform k
           outerBody := W
           parent := 𝒱.tubeUniform.cover.assign k
           parent_mem := hparent_mem
           inner_le_parent := hinner_le
           shade_subset_parent := hshade_sub }, rfl, fun i _ => rfl, rfl, fun j _ => rfl, hball⟩

/-! ## The residue is the choice of one set

`Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid` quantifies over shaded factor families,
but once its first four conjuncts pin the inner layer to `(cfg.s, cfg.T)` on the nose and the
outer layer to the full active node family, the only freedom left is the *shading of the node
tubes*, and even that is redundant: replacing each node shading by `T_ρ ∩ Z` with
`Z = U(𝕋_ρ, Y_{𝕋_ρ})` changes neither the outer union nor decreases any node's shade. So the
residue is equivalent to the existence of a single measurable set `Z` containing the inner
shaded union `U(𝕋, Y)`, and the two conjuncts become two conditions on that one set. The two
lemmas below are the two directions.
-/

/-- The node family shaded by a prescribed set: node `j` carries the tube `T_{ρ,j}` as its
convex body and `T_{ρ,j} ∩ Z` as its shade. This is the general form of the outer layer of
`Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid`; see
`Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid_iff_exists_shadingSet`. -/
noncomputable def coarseShadeAt (cfg : VeryNotSticky.{u})
    (𝒱 : ShadedTube.ShadedUniformTubeSet cfg.s cfg.T (Tube.ssfGridLen cfg.δ) cfg.C₀)
    (k : ℕ) (Z : Set (EuclideanSpace ℝ (Fin 3))) (hZ : MeasurableSet Z) (j : cfg.ι) :
    ShadedBody (EuclideanSpace ℝ (Fin 3)) where
  toConvexSpaceBody := (𝒱.tubeUniform.cover.tube k j).toConvexSpaceBody
  shade := (𝒱.tubeUniform.cover.tube k j).toConvexSpaceBody.carrier ∩ Z
  measurableSet_shade :=
    ((𝒱.tubeUniform.cover.tube k j).toConvexSpaceBody.isCompact'.isClosed.measurableSet).inter hZ
  shade_subset := Set.inter_subset_left

/-- **From a set to the family** (the direction a successor needs).

Given a measurable `Z` containing the inner shaded union and satisfying the residue's two
estimates at the shading `T_ρ ∩ Z`, the residue holds. All the factor-family bookkeeping —
the parent map, `parent_mem`, `inner_le_parent`, `shade_subset_parent`, and the four pinning
conjuncts — is discharged here, once and for all, so that what is left to prove is a statement
about one set and two volumes. -/
theorem exists_coarseShadedFamilyAtGrid_of_shadingSet (cfg : VeryNotSticky.{u})
    (𝒱 : ShadedTube.ShadedUniformTubeSet cfg.s cfg.T (Tube.ssfGridLen cfg.δ) cfg.C₀)
    {k : ℕ} (hk : k ≤ Tube.ssfGridLen cfg.δ)
    {ρ : NNReal} (hgrid : Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k = ρ)
    (Z : Set (EuclideanSpace ℝ (Fin 3))) (hZ : MeasurableSet Z)
    (hZin : (⋃ i ∈ cfg.s, ((cfg.T i).toShadedBody).shade) ⊆ Z)
    (hfullZ : (cfg.Cd * shadingMultiplicityEstimateForRhoTubes.C)⁻¹ * cfg.lam ≤
      ShadedBody.fullness (cfg.activeTubeNodes 𝒱.tubeUniform k)
        (cfg.coarseShadeAt 𝒱 k Z hZ))
    (hballZ : ∀ x ∈ ⋃ j ∈ cfg.activeTubeNodes 𝒱.tubeUniform k,
        (cfg.coarseShadeAt 𝒱 k Z hZ j).shade,
      (cfg.δ : ENNReal) ^ cfg.η *
          (((shadingMultiplicityEstimateForRhoTubes.C : NNReal) : ENNReal)⁻¹ *
              volume (⋃ j ∈ cfg.activeTubeNodes 𝒱.tubeUniform k,
                (cfg.coarseShadeAt 𝒱 k Z hZ j).shade) *
            (volume ((⋃ i ∈ cfg.s, ((cfg.T i).toShadedBody).shade) ∩ ball x (ρ : ℝ)) /
              volume (ball x (ρ : ℝ)))) ≤
        volume (⋃ i ∈ cfg.s, ((cfg.T i).toShadedBody).shade)) :
    ∃ G : ShadedFactorFamily (EuclideanSpace ℝ (Fin 3)) cfg.ι cfg.ι,
      G.innerSet = cfg.s ∧
      (∀ i ∈ cfg.s, G.innerBody i = (cfg.T i).toShadedBody) ∧
      G.outerSet = cfg.activeTubeNodes 𝒱.tubeUniform k ∧
      (∀ j ∈ G.outerSet,
        (G.outerBody j).toConvexSpaceBody =
          (𝒱.tubeUniform.cover.tube k j).toConvexSpaceBody) ∧
      (cfg.Cd * shadingMultiplicityEstimateForRhoTubes.C)⁻¹ * cfg.lam ≤
        ShadedBody.fullness G.outerSet G.outerBody ∧
      (∀ x ∈ ⋃ j ∈ G.outerSet, (G.outerBody j).shade,
        (cfg.δ : ENNReal) ^ cfg.η *
            (((shadingMultiplicityEstimateForRhoTubes.C : NNReal) : ENNReal)⁻¹ *
                volume (⋃ j ∈ G.outerSet, (G.outerBody j).shade) *
              (volume ((⋃ i ∈ G.innerSet, (G.innerBody i).shade) ∩ ball x (ρ : ℝ)) /
                volume (ball x (ρ : ℝ)))) ≤
          volume (⋃ i ∈ G.innerSet, (G.innerBody i).shade)) := by
  classical
  subst hgrid
  have hparent_mem : ∀ i ∈ cfg.s, 𝒱.tubeUniform.cover.assign k i
      ∈ cfg.activeTubeNodes 𝒱.tubeUniform k := by
    intro i hi
    rw [activeTubeNodes, Finset.mem_filter]
    refine ⟨𝒱.tubeUniform.cover.assign_mem k hk i hi, ⟨i, ?_⟩⟩
    simp [tubeFibre, Tube.coverClass, hi]
  have hinner_le : ∀ i ∈ cfg.s,
      ((cfg.T i).toShadedBody).toConvexSpaceBody ≤
        (cfg.coarseShadeAt 𝒱 k Z hZ (𝒱.tubeUniform.cover.assign k i)).toConvexSpaceBody := by
    intro i hi
    simpa [coarseShadeAt] using 𝒱.tubeUniform.cover.le_tube_assign k hk i hi
  have hshade_sub : ∀ i ∈ cfg.s,
      ((cfg.T i).toShadedBody).shade ⊆
        (cfg.coarseShadeAt 𝒱 k Z hZ (𝒱.tubeUniform.cover.assign k i)).shade := by
    intro i hi x hx
    exact ⟨(hinner_le i hi) ((cfg.T i).toShadedBody.shade_subset hx),
      hZin (Set.mem_biUnion hi hx)⟩
  exact ⟨{ innerSet := cfg.s
           innerBody := fun i => (cfg.T i).toShadedBody
           outerSet := cfg.activeTubeNodes 𝒱.tubeUniform k
           outerBody := cfg.coarseShadeAt 𝒱 k Z hZ
           parent := 𝒱.tubeUniform.cover.assign k
           parent_mem := hparent_mem
           inner_le_parent := hinner_le
           shade_subset_parent := hshade_sub }, rfl, fun i _ => rfl, rfl, fun j _ => rfl,
    hfullZ, hballZ⟩

/-- **From the family to a set** (the direction that certifies nothing is lost).

If the residue holds, then `Z = U(𝕋_ρ, Y_{𝕋_ρ})` is a set with the two properties above. The
only step is that replacing `Y_{𝕋_ρ}(T_{ρ,j})` by `T_{ρ,j} ∩ Z` leaves the outer union alone and
does not shrink any node's shade, so the fullness only goes up and the ball estimate is
unchanged. Together with `Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid_of_shadingSet`
this says the residue *is* the existence of such a set. -/
theorem exists_shadingSet_of_exists_coarseShadedFamilyAtGrid (cfg : VeryNotSticky.{u})
    (𝒱 : ShadedTube.ShadedUniformTubeSet cfg.s cfg.T (Tube.ssfGridLen cfg.δ) cfg.C₀)
    {k : ℕ} {ρ : NNReal}
    (H : ∃ G : ShadedFactorFamily (EuclideanSpace ℝ (Fin 3)) cfg.ι cfg.ι,
      G.innerSet = cfg.s ∧
      (∀ i ∈ cfg.s, G.innerBody i = (cfg.T i).toShadedBody) ∧
      G.outerSet = cfg.activeTubeNodes 𝒱.tubeUniform k ∧
      (∀ j ∈ G.outerSet,
        (G.outerBody j).toConvexSpaceBody =
          (𝒱.tubeUniform.cover.tube k j).toConvexSpaceBody) ∧
      (cfg.Cd * shadingMultiplicityEstimateForRhoTubes.C)⁻¹ * cfg.lam ≤
        ShadedBody.fullness G.outerSet G.outerBody ∧
      (∀ x ∈ ⋃ j ∈ G.outerSet, (G.outerBody j).shade,
        (cfg.δ : ENNReal) ^ cfg.η *
            (((shadingMultiplicityEstimateForRhoTubes.C : NNReal) : ENNReal)⁻¹ *
                volume (⋃ j ∈ G.outerSet, (G.outerBody j).shade) *
              (volume ((⋃ i ∈ G.innerSet, (G.innerBody i).shade) ∩ ball x (ρ : ℝ)) /
                volume (ball x (ρ : ℝ)))) ≤
          volume (⋃ i ∈ G.innerSet, (G.innerBody i).shade))) :
    ∃ (Z : Set (EuclideanSpace ℝ (Fin 3))) (hZ : MeasurableSet Z),
      (⋃ i ∈ cfg.s, ((cfg.T i).toShadedBody).shade) ⊆ Z ∧
      (cfg.Cd * shadingMultiplicityEstimateForRhoTubes.C)⁻¹ * cfg.lam ≤
        ShadedBody.fullness (cfg.activeTubeNodes 𝒱.tubeUniform k)
          (cfg.coarseShadeAt 𝒱 k Z hZ) ∧
      (∀ x ∈ ⋃ j ∈ cfg.activeTubeNodes 𝒱.tubeUniform k,
          (cfg.coarseShadeAt 𝒱 k Z hZ j).shade,
        (cfg.δ : ENNReal) ^ cfg.η *
            (((shadingMultiplicityEstimateForRhoTubes.C : NNReal) : ENNReal)⁻¹ *
                volume (⋃ j ∈ cfg.activeTubeNodes 𝒱.tubeUniform k,
                  (cfg.coarseShadeAt 𝒱 k Z hZ j).shade) *
              (volume ((⋃ i ∈ cfg.s, ((cfg.T i).toShadedBody).shade) ∩ ball x (ρ : ℝ)) /
                volume (ball x (ρ : ℝ)))) ≤
          volume (⋃ i ∈ cfg.s, ((cfg.T i).toShadedBody).shade)) := by
  classical
  obtain ⟨G, hinner, hbody, houterSet, houterBody, hfull, hball⟩ := H
  have hZmeas : MeasurableSet
      (⋃ j ∈ cfg.activeTubeNodes 𝒱.tubeUniform k, (G.outerBody j).shade) :=
    Finset.measurableSet_biUnion _ (fun j _ => (G.outerBody j).measurableSet_shade)
  -- each node's own shade sits inside `T_ρ ∩ Z`
  have hsub : ∀ j ∈ cfg.activeTubeNodes 𝒱.tubeUniform k,
      (G.outerBody j).shade ⊆
        (cfg.coarseShadeAt 𝒱 k
          (⋃ j ∈ cfg.activeTubeNodes 𝒱.tubeUniform k, (G.outerBody j).shade) hZmeas j).shade := by
    intro j hj y hy
    have hjG : j ∈ G.outerSet := by rw [houterSet]; exact hj
    refine ⟨?_, Set.mem_biUnion hj hy⟩
    have hcar : (G.outerBody j).carrier
        = (𝒱.tubeUniform.cover.tube k j).toConvexSpaceBody.carrier :=
      congrArg (fun B => B.carrier) (houterBody j hjG)
    have hy' := (G.outerBody j).shade_subset hy
    rwa [hcar] at hy'
  have hunion : (⋃ j ∈ cfg.activeTubeNodes 𝒱.tubeUniform k,
        (cfg.coarseShadeAt 𝒱 k
          (⋃ j ∈ cfg.activeTubeNodes 𝒱.tubeUniform k, (G.outerBody j).shade) hZmeas j).shade)
      = ⋃ j ∈ cfg.activeTubeNodes 𝒱.tubeUniform k, (G.outerBody j).shade := by
    apply Set.Subset.antisymm
    · exact Set.iUnion₂_subset (fun j _ => Set.inter_subset_right)
    · intro y hy
      obtain ⟨j, hj, hyj⟩ := Set.mem_iUnion₂.mp hy
      exact Set.mem_biUnion hj (hsub j hj hyj)
  refine ⟨_, hZmeas, ?_, ?_, ?_⟩
  · -- the inner shaded union is inside `Z`, because every inner shade is inside its parent's
    refine Set.iUnion₂_subset (fun i hi => ?_)
    have hpar : G.parent i ∈ cfg.activeTubeNodes 𝒱.tubeUniform k := by
      rw [← houterSet]; exact G.parent_mem i (by rw [hinner]; exact hi)
    have hcont := G.shade_subset_parent i (by rw [hinner]; exact hi)
    rw [hbody i hi] at hcont
    exact hcont.trans (Set.subset_biUnion_of_mem (u := fun j => (G.outerBody j).shade) hpar)
  · -- fullness only goes up when each shade is enlarged to `T_ρ ∩ Z`
    refine le_trans (houterSet ▸ hfull) ?_
    rw [← ENNReal.coe_le_coe, ShadedBody.fullness_def, ShadedBody.fullness_def]
    have hden : (∑ j ∈ cfg.activeTubeNodes 𝒱.tubeUniform k, volume (G.outerBody j).carrier)
        = ∑ j ∈ cfg.activeTubeNodes 𝒱.tubeUniform k,
            volume (cfg.coarseShadeAt 𝒱 k
              (⋃ j ∈ cfg.activeTubeNodes 𝒱.tubeUniform k, (G.outerBody j).shade)
                hZmeas j).carrier := by
      refine Finset.sum_congr rfl (fun j hj => ?_)
      have hcar : (G.outerBody j).carrier
          = (𝒱.tubeUniform.cover.tube k j).toConvexSpaceBody.carrier :=
        congrArg (fun B => B.carrier) (houterBody j (by rw [houterSet]; exact hj))
      rw [hcar]
      rfl
    have hnum : (∑ j ∈ cfg.activeTubeNodes 𝒱.tubeUniform k, volume (G.outerBody j).shade)
        ≤ ∑ j ∈ cfg.activeTubeNodes 𝒱.tubeUniform k,
            volume (cfg.coarseShadeAt 𝒱 k
              (⋃ j ∈ cfg.activeTubeNodes 𝒱.tubeUniform k, (G.outerBody j).shade) hZmeas j).shade :=
      Finset.sum_le_sum (fun j hj => measure_mono (hsub j hj))
    rw [hden]
    exact ENNReal.div_le_div_right hnum _
  · -- the ball estimate is unchanged, both outer unions being the same set
    intro x hx
    rw [hunion] at hx ⊢
    have hxG : x ∈ ⋃ j ∈ G.outerSet, (G.outerBody j).shade := by rw [houterSet]; exact hx
    have hcore := hball x hxG
    rw [hinner, houterSet] at hcore
    have hinner_union : (⋃ i ∈ cfg.s, (G.innerBody i).shade)
        = ⋃ i ∈ cfg.s, ((cfg.T i).toShadedBody).shade := by
      refine Set.iUnion_congr (fun i => Set.iUnion_congr (fun hi => ?_))
      rw [hbody i hi]
    rw [hinner_union] at hcore
    exact hcore

/-! ## Removing the supremum from the ball conjunct

The ball conjunct of `Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid` is quantified over
*every* point of the outer shaded union, so read naively it asks for the **densest** `ρ`-ball of
`U(𝕋, Y)` to be controlled. That reading is what made the conjunct look unreachable: the
uniformity of the ball masses of the coarse union is exactly what Step 5 of the proof of GWZ
Lemma 5.11 buys by *discarding coarse bodies*, which is why
`ShadedBody.exists_rhoTubesSection9_fullFamily` extends the fullness clause to the full node
family but nothing extends the ball clause.

The three lemmas below show that **the supremum is not what has to be controlled**. For any
admissible shading set `Z` the entire family of point estimates follows from a single inequality
in which no point occurs at all,

  `δ^η · |U(𝕋_ρ, Y_{𝕋_ρ})| ≤ max (|U(𝕋, Y)|, |B(0, ρ)|)`,

and each of the two branches of the maximum is one line of monotonicity:

* against `|U(𝕋, Y)|`, because the local density `|U(𝕋,Y) ∩ B(x,ρ)| / |B(x,ρ)|` is at most `1`;
* against `|B(0, ρ)|`, because the same density is at most `|U(𝕋,Y)| / |B(x,ρ)|`, and the
  volume of a ball in `EuclideanSpace ℝ (Fin 3)` does not depend on its centre.

Neither branch looks at where the mass of `U(𝕋, Y)` sits, so neither needs the pigeonholing. The
residue is therefore *not* an assertion about the worst `ρ`-ball; it is the assertion that the
outer shaded union can be made `Cd⁻¹ · lam`-full of the node family **without growing past
`δ^{-η} max(|U(𝕋,Y)|, |B(0,ρ)|)` in volume**. That is a two-sided volume budget, and it is what
a successor should attack.
-/

/-- **From a shading set with a volume bound to the residue, first branch.**

`Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid_of_shadingSet` with the pointwise ball
hypothesis replaced by the single volume inequality `δ^η · |U(𝕋_ρ, Y_{𝕋_ρ})| ≤ |U(𝕋, Y)|`. The
step is that the local density of the inner union in a ball is at most `1`, so no point of the
outer union is looked at. -/
theorem exists_coarseShadedFamilyAtGrid_of_shadingSet_volume (cfg : VeryNotSticky.{u})
    (𝒱 : ShadedTube.ShadedUniformTubeSet cfg.s cfg.T (Tube.ssfGridLen cfg.δ) cfg.C₀)
    {k : ℕ} (hk : k ≤ Tube.ssfGridLen cfg.δ)
    {ρ : NNReal} (hgrid : Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k = ρ)
    (Z : Set (EuclideanSpace ℝ (Fin 3))) (hZ : MeasurableSet Z)
    (hZin : (⋃ i ∈ cfg.s, ((cfg.T i).toShadedBody).shade) ⊆ Z)
    (hfullZ : (cfg.Cd * shadingMultiplicityEstimateForRhoTubes.C)⁻¹ * cfg.lam ≤
      ShadedBody.fullness (cfg.activeTubeNodes 𝒱.tubeUniform k)
        (cfg.coarseShadeAt 𝒱 k Z hZ))
    (hvol : (cfg.δ : ENNReal) ^ cfg.η *
        volume (⋃ j ∈ cfg.activeTubeNodes 𝒱.tubeUniform k,
          (cfg.coarseShadeAt 𝒱 k Z hZ j).shade) ≤
      volume (⋃ i ∈ cfg.s, ((cfg.T i).toShadedBody).shade)) :
    ∃ G : ShadedFactorFamily (EuclideanSpace ℝ (Fin 3)) cfg.ι cfg.ι,
      G.innerSet = cfg.s ∧
      (∀ i ∈ cfg.s, G.innerBody i = (cfg.T i).toShadedBody) ∧
      G.outerSet = cfg.activeTubeNodes 𝒱.tubeUniform k ∧
      (∀ j ∈ G.outerSet,
        (G.outerBody j).toConvexSpaceBody =
          (𝒱.tubeUniform.cover.tube k j).toConvexSpaceBody) ∧
      (cfg.Cd * shadingMultiplicityEstimateForRhoTubes.C)⁻¹ * cfg.lam ≤
        ShadedBody.fullness G.outerSet G.outerBody ∧
      (∀ x ∈ ⋃ j ∈ G.outerSet, (G.outerBody j).shade,
        (cfg.δ : ENNReal) ^ cfg.η *
            (((shadingMultiplicityEstimateForRhoTubes.C : NNReal) : ENNReal)⁻¹ *
                volume (⋃ j ∈ G.outerSet, (G.outerBody j).shade) *
              (volume ((⋃ i ∈ G.innerSet, (G.innerBody i).shade) ∩ ball x (ρ : ℝ)) /
                volume (ball x (ρ : ℝ)))) ≤
          volume (⋃ i ∈ G.innerSet, (G.innerBody i).shade)) := by
  classical
  refine exists_coarseShadedFamilyAtGrid_of_shadingSet cfg 𝒱 hk hgrid Z hZ hZin hfullZ ?_
  intro x _
  have hC : ((shadingMultiplicityEstimateForRhoTubes.C : NNReal) : ENNReal)⁻¹ = 1 := by
    rw [ShadedBody.shadingMultiplicityEstimateForRhoTubes.C]
    simp
  have hratio :
      volume ((⋃ i ∈ cfg.s, ((cfg.T i).toShadedBody).shade) ∩ ball x (ρ : ℝ)) /
          volume (ball x (ρ : ℝ)) ≤ 1 :=
    ENNReal.div_le_of_le_mul
      (by
        rw [one_mul]
        exact measure_mono (μ := (volume : Measure (EuclideanSpace ℝ (Fin 3))))
          Set.inter_subset_right)
  calc (cfg.δ : ENNReal) ^ cfg.η *
          (((shadingMultiplicityEstimateForRhoTubes.C : NNReal) : ENNReal)⁻¹ *
              volume (⋃ j ∈ cfg.activeTubeNodes 𝒱.tubeUniform k,
                (cfg.coarseShadeAt 𝒱 k Z hZ j).shade) *
            (volume ((⋃ i ∈ cfg.s, ((cfg.T i).toShadedBody).shade) ∩ ball x (ρ : ℝ)) /
              volume (ball x (ρ : ℝ))))
      = (cfg.δ : ENNReal) ^ cfg.η *
          (volume (⋃ j ∈ cfg.activeTubeNodes 𝒱.tubeUniform k,
              (cfg.coarseShadeAt 𝒱 k Z hZ j).shade) *
            (volume ((⋃ i ∈ cfg.s, ((cfg.T i).toShadedBody).shade) ∩ ball x (ρ : ℝ)) /
              volume (ball x (ρ : ℝ)))) := by rw [hC, one_mul]
    _ ≤ (cfg.δ : ENNReal) ^ cfg.η *
          (volume (⋃ j ∈ cfg.activeTubeNodes 𝒱.tubeUniform k,
            (cfg.coarseShadeAt 𝒱 k Z hZ j).shade) * 1) := by gcongr
    _ = (cfg.δ : ENNReal) ^ cfg.η *
          volume (⋃ j ∈ cfg.activeTubeNodes 𝒱.tubeUniform k,
            (cfg.coarseShadeAt 𝒱 k Z hZ j).shade) := by rw [mul_one]
    _ ≤ volume (⋃ i ∈ cfg.s, ((cfg.T i).toShadedBody).shade) := hvol

/-- **From a shading set with a volume bound to the residue, second branch.**

The companion of `Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid_of_shadingSet_volume`
that is useful when the inner shaded union is *large* compared with a single `ρ`-ball: there the
local density `|U(𝕋,Y) ∩ B(x,ρ)| / |B(x,ρ)|` is bounded by `|U(𝕋,Y)| / |B(x,ρ)|` instead, and the
volume of a ball in `EuclideanSpace ℝ (Fin 3)` is independent of its centre, so the hypothesis
can be stated at the centre `0`. Again no point of the outer union is looked at. -/
theorem exists_coarseShadedFamilyAtGrid_of_shadingSet_volume_ball (cfg : VeryNotSticky.{u})
    (𝒱 : ShadedTube.ShadedUniformTubeSet cfg.s cfg.T (Tube.ssfGridLen cfg.δ) cfg.C₀)
    {k : ℕ} (hk : k ≤ Tube.ssfGridLen cfg.δ)
    {ρ : NNReal} (hgrid : Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k = ρ)
    (hρ : ρ ∈ Set.Icc cfg.δ 1)
    (Z : Set (EuclideanSpace ℝ (Fin 3))) (hZ : MeasurableSet Z)
    (hZin : (⋃ i ∈ cfg.s, ((cfg.T i).toShadedBody).shade) ⊆ Z)
    (hfullZ : (cfg.Cd * shadingMultiplicityEstimateForRhoTubes.C)⁻¹ * cfg.lam ≤
      ShadedBody.fullness (cfg.activeTubeNodes 𝒱.tubeUniform k)
        (cfg.coarseShadeAt 𝒱 k Z hZ))
    (hvol : (cfg.δ : ENNReal) ^ cfg.η *
        volume (⋃ j ∈ cfg.activeTubeNodes 𝒱.tubeUniform k,
          (cfg.coarseShadeAt 𝒱 k Z hZ j).shade) ≤
      volume (ball (0 : EuclideanSpace ℝ (Fin 3)) (ρ : ℝ))) :
    ∃ G : ShadedFactorFamily (EuclideanSpace ℝ (Fin 3)) cfg.ι cfg.ι,
      G.innerSet = cfg.s ∧
      (∀ i ∈ cfg.s, G.innerBody i = (cfg.T i).toShadedBody) ∧
      G.outerSet = cfg.activeTubeNodes 𝒱.tubeUniform k ∧
      (∀ j ∈ G.outerSet,
        (G.outerBody j).toConvexSpaceBody =
          (𝒱.tubeUniform.cover.tube k j).toConvexSpaceBody) ∧
      (cfg.Cd * shadingMultiplicityEstimateForRhoTubes.C)⁻¹ * cfg.lam ≤
        ShadedBody.fullness G.outerSet G.outerBody ∧
      (∀ x ∈ ⋃ j ∈ G.outerSet, (G.outerBody j).shade,
        (cfg.δ : ENNReal) ^ cfg.η *
            (((shadingMultiplicityEstimateForRhoTubes.C : NNReal) : ENNReal)⁻¹ *
                volume (⋃ j ∈ G.outerSet, (G.outerBody j).shade) *
              (volume ((⋃ i ∈ G.innerSet, (G.innerBody i).shade) ∩ ball x (ρ : ℝ)) /
                volume (ball x (ρ : ℝ)))) ≤
          volume (⋃ i ∈ G.innerSet, (G.innerBody i).shade)) := by
  classical
  have hρpos : (0 : ℝ) < (ρ : ℝ) := by
    have : (0 : NNReal) < ρ := lt_of_lt_of_le cfg.hδ hρ.1
    exact_mod_cast this
  refine exists_coarseShadedFamilyAtGrid_of_shadingSet cfg 𝒱 hk hgrid Z hZ hZin hfullZ ?_
  intro x _
  have hC : ((shadingMultiplicityEstimateForRhoTubes.C : NNReal) : ENNReal)⁻¹ = 1 := by
    rw [ShadedBody.shadingMultiplicityEstimateForRhoTubes.C]
    simp
  have hcenter : volume (ball x (ρ : ℝ))
      = volume (ball (0 : EuclideanSpace ℝ (Fin 3)) (ρ : ℝ)) := by
    rw [EuclideanSpace.volume_ball, EuclideanSpace.volume_ball]
  have hB0 : volume (ball x (ρ : ℝ)) ≠ 0 :=
    (measure_ball_pos (volume : Measure (EuclideanSpace ℝ (Fin 3))) x hρpos).ne'
  have hBt : volume (ball x (ρ : ℝ)) ≠ ⊤ :=
    (measure_ball_lt_top (μ := (volume : Measure (EuclideanSpace ℝ (Fin 3))))).ne
  have hvol' : (cfg.δ : ENNReal) ^ cfg.η *
      volume (⋃ j ∈ cfg.activeTubeNodes 𝒱.tubeUniform k,
        (cfg.coarseShadeAt 𝒱 k Z hZ j).shade) ≤ volume (ball x (ρ : ℝ)) := by
    rw [hcenter]; exact hvol
  have hratio :
      volume ((⋃ i ∈ cfg.s, ((cfg.T i).toShadedBody).shade) ∩ ball x (ρ : ℝ)) /
          volume (ball x (ρ : ℝ)) ≤
        volume (⋃ i ∈ cfg.s, ((cfg.T i).toShadedBody).shade) / volume (ball x (ρ : ℝ)) :=
    ENNReal.div_le_div_right
      (measure_mono (μ := (volume : Measure (EuclideanSpace ℝ (Fin 3))))
        Set.inter_subset_left) _
  calc (cfg.δ : ENNReal) ^ cfg.η *
          (((shadingMultiplicityEstimateForRhoTubes.C : NNReal) : ENNReal)⁻¹ *
              volume (⋃ j ∈ cfg.activeTubeNodes 𝒱.tubeUniform k,
                (cfg.coarseShadeAt 𝒱 k Z hZ j).shade) *
            (volume ((⋃ i ∈ cfg.s, ((cfg.T i).toShadedBody).shade) ∩ ball x (ρ : ℝ)) /
              volume (ball x (ρ : ℝ))))
      = ((cfg.δ : ENNReal) ^ cfg.η *
          volume (⋃ j ∈ cfg.activeTubeNodes 𝒱.tubeUniform k,
            (cfg.coarseShadeAt 𝒱 k Z hZ j).shade)) *
          (volume ((⋃ i ∈ cfg.s, ((cfg.T i).toShadedBody).shade) ∩ ball x (ρ : ℝ)) /
            volume (ball x (ρ : ℝ))) := by rw [hC, one_mul, mul_assoc]
    _ ≤ volume (ball x (ρ : ℝ)) *
          (volume (⋃ i ∈ cfg.s, ((cfg.T i).toShadedBody).shade) / volume (ball x (ρ : ℝ))) := by
        gcongr
    _ = volume (⋃ i ∈ cfg.s, ((cfg.T i).toShadedBody).shade) := by
        rw [ENNReal.mul_div_cancel' (fun h => absurd h hB0) (fun h => absurd h hBt)]

/-- **The sup-free form of the residue's ball conjunct, both branches at once.**

Given a shading set `Z` that is `Cd⁻¹ · lam`-full of the node family, the residue follows as soon
as the outer shaded union obeys the volume budget
`δ^η · |U(𝕋_ρ, Y_{𝕋_ρ})| ≤ max (|U(𝕋, Y)|, |B(0, ρ)|)`. The maximum is a maximum in a linear
order, so this is exactly the disjunction of
`Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid_of_shadingSet_volume` and
`Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid_of_shadingSet_volume_ball`. -/
theorem exists_coarseShadedFamilyAtGrid_of_shadingSet_volume_max (cfg : VeryNotSticky.{u})
    (𝒱 : ShadedTube.ShadedUniformTubeSet cfg.s cfg.T (Tube.ssfGridLen cfg.δ) cfg.C₀)
    {k : ℕ} (hk : k ≤ Tube.ssfGridLen cfg.δ)
    {ρ : NNReal} (hgrid : Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k = ρ)
    (hρ : ρ ∈ Set.Icc cfg.δ 1)
    (Z : Set (EuclideanSpace ℝ (Fin 3))) (hZ : MeasurableSet Z)
    (hZin : (⋃ i ∈ cfg.s, ((cfg.T i).toShadedBody).shade) ⊆ Z)
    (hfullZ : (cfg.Cd * shadingMultiplicityEstimateForRhoTubes.C)⁻¹ * cfg.lam ≤
      ShadedBody.fullness (cfg.activeTubeNodes 𝒱.tubeUniform k)
        (cfg.coarseShadeAt 𝒱 k Z hZ))
    (hvol : (cfg.δ : ENNReal) ^ cfg.η *
        volume (⋃ j ∈ cfg.activeTubeNodes 𝒱.tubeUniform k,
          (cfg.coarseShadeAt 𝒱 k Z hZ j).shade) ≤
      max (volume (⋃ i ∈ cfg.s, ((cfg.T i).toShadedBody).shade))
        (volume (ball (0 : EuclideanSpace ℝ (Fin 3)) (ρ : ℝ)))) :
    ∃ G : ShadedFactorFamily (EuclideanSpace ℝ (Fin 3)) cfg.ι cfg.ι,
      G.innerSet = cfg.s ∧
      (∀ i ∈ cfg.s, G.innerBody i = (cfg.T i).toShadedBody) ∧
      G.outerSet = cfg.activeTubeNodes 𝒱.tubeUniform k ∧
      (∀ j ∈ G.outerSet,
        (G.outerBody j).toConvexSpaceBody =
          (𝒱.tubeUniform.cover.tube k j).toConvexSpaceBody) ∧
      (cfg.Cd * shadingMultiplicityEstimateForRhoTubes.C)⁻¹ * cfg.lam ≤
        ShadedBody.fullness G.outerSet G.outerBody ∧
      (∀ x ∈ ⋃ j ∈ G.outerSet, (G.outerBody j).shade,
        (cfg.δ : ENNReal) ^ cfg.η *
            (((shadingMultiplicityEstimateForRhoTubes.C : NNReal) : ENNReal)⁻¹ *
                volume (⋃ j ∈ G.outerSet, (G.outerBody j).shade) *
              (volume ((⋃ i ∈ G.innerSet, (G.innerBody i).shade) ∩ ball x (ρ : ℝ)) /
                volume (ball x (ρ : ℝ)))) ≤
          volume (⋃ i ∈ G.innerSet, (G.innerBody i).shade)) := by
  classical
  rcases max_cases (volume (⋃ i ∈ cfg.s, ((cfg.T i).toShadedBody).shade))
      (volume (ball (0 : EuclideanSpace ℝ (Fin 3)) (ρ : ℝ))) with ⟨he, _⟩ | ⟨he, _⟩
  · exact exists_coarseShadedFamilyAtGrid_of_shadingSet_volume cfg 𝒱 hk hgrid Z hZ hZin hfullZ
      (by rw [he] at hvol; exact hvol)
  · exact exists_coarseShadedFamilyAtGrid_of_shadingSet_volume_ball cfg 𝒱 hk hgrid hρ Z hZ hZin
      hfullZ (by rw [he] at hvol; exact hvol)

/-- **A shading set that swallows the node tubes makes the outer family completely full.**

Auxiliary to `Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid_of_coarseVolume`: if `Z`
contains every active node tube then `Kakeya.VeryNotSticky.coarseShadeAt` shades each of them
entirely, so the outer fullness is `1`. The total carrier volume is nonzero because the node
carrying any member of `𝕋` is active and its tube contains a `δ`-tube of positive volume, and
finite because node tubes are compact. -/
theorem fullness_coarseShadeAt_eq_one (cfg : VeryNotSticky.{u})
    (𝒱 : ShadedTube.ShadedUniformTubeSet cfg.s cfg.T (Tube.ssfGridLen cfg.δ) cfg.C₀)
    {k : ℕ} (hk : k ≤ Tube.ssfGridLen cfg.δ)
    {Z : Set (EuclideanSpace ℝ (Fin 3))} (hZ : MeasurableSet Z)
    (hsub : ∀ j ∈ cfg.activeTubeNodes 𝒱.tubeUniform k,
      (𝒱.tubeUniform.cover.tube k j).toConvexSpaceBody.carrier ⊆ Z) :
    ShadedBody.fullness (cfg.activeTubeNodes 𝒱.tubeUniform k)
      (cfg.coarseShadeAt 𝒱 k Z hZ) = 1 := by
  classical
  have hs : cfg.s.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    have := cfg.tube_count
    rw [h] at this
    simp at this
  obtain ⟨i₀, hi₀⟩ := hs
  have hmem : 𝒱.tubeUniform.cover.assign k i₀ ∈ cfg.activeTubeNodes 𝒱.tubeUniform k := by
    rw [activeTubeNodes, Finset.mem_filter]
    refine ⟨𝒱.tubeUniform.cover.assign_mem k hk i₀ hi₀, ⟨i₀, ?_⟩⟩
    simp [tubeFibre, Tube.coverClass, hi₀]
  have hcar : ∀ j, (cfg.coarseShadeAt 𝒱 k Z hZ j).carrier
      = (𝒱.tubeUniform.cover.tube k j).toConvexSpaceBody.carrier := fun _ => rfl
  have hshade : ∀ j ∈ cfg.activeTubeNodes 𝒱.tubeUniform k,
      (cfg.coarseShadeAt 𝒱 k Z hZ j).shade
        = (𝒱.tubeUniform.cover.tube k j).toConvexSpaceBody.carrier := by
    intro j hj
    show (𝒱.tubeUniform.cover.tube k j).toConvexSpaceBody.carrier ∩ Z
        = (𝒱.tubeUniform.cover.tube k j).toConvexSpaceBody.carrier
    exact Set.inter_eq_self_of_subset_left (hsub j hj)
  have hinner_le : ((cfg.T i₀).toShadedBody).toConvexSpaceBody ≤
      (cfg.coarseShadeAt 𝒱 k Z hZ (𝒱.tubeUniform.cover.assign k i₀)).toConvexSpaceBody := by
    simpa [coarseShadeAt] using 𝒱.tubeUniform.cover.le_tube_assign k hk i₀ hi₀
  have hpos : 0 < volume ((cfg.T i₀).toShadedBody.carrier) := by
    have h := _root_.Tube.le_volume (cfg.T i₀).toTube
    refine lt_of_lt_of_le ?_ (by simpa using h)
    have hc : (0 : ENNReal) < (_root_.Tube.le_volume.c 3 : ENNReal) :=
      ENNReal.coe_pos.mpr (_root_.Tube.le_volume.c_pos _)
    have hδp : (0 : ENNReal) < (cfg.δ : ENNReal) ^ 2 :=
      ENNReal.pow_pos (ENNReal.coe_pos.mpr cfg.hδ) _
    exact ENNReal.mul_pos (ne_of_gt hc) (ne_of_gt hδp)
  have hsum0 : (∑ j ∈ cfg.activeTubeNodes 𝒱.tubeUniform k,
      volume ((cfg.coarseShadeAt 𝒱 k Z hZ j).carrier)) ≠ 0 := by
    intro h
    rw [Finset.sum_eq_zero_iff] at h
    exact absurd (h _ hmem) (ne_of_gt (lt_of_lt_of_le hpos (measure_mono hinner_le)))
  have hsumtop : (∑ j ∈ cfg.activeTubeNodes 𝒱.tubeUniform k,
      volume ((cfg.coarseShadeAt 𝒱 k Z hZ j).carrier)) ≠ ⊤ := by
    refine (lt_top_iff_ne_top.mp ?_)
    refine ENNReal.sum_lt_top.mpr (fun j _ => ?_)
    rw [hcar j]
    exact (𝒱.tubeUniform.cover.tube k j).toConvexSpaceBody.isCompact'.measure_lt_top
  have hone : ((ShadedBody.fullness (cfg.activeTubeNodes 𝒱.tubeUniform k)
      (cfg.coarseShadeAt 𝒱 k Z hZ) : NNReal) : ENNReal) = 1 := by
    rw [ShadedBody.fullness_def]
    have hnum : (∑ j ∈ cfg.activeTubeNodes 𝒱.tubeUniform k,
        volume ((cfg.coarseShadeAt 𝒱 k Z hZ j).shade))
        = ∑ j ∈ cfg.activeTubeNodes 𝒱.tubeUniform k,
            volume ((cfg.coarseShadeAt 𝒱 k Z hZ j).carrier) := by
      refine Finset.sum_congr rfl (fun j hj => ?_)
      rw [hshade j hj, hcar j]
    rw [hnum]
    exact ENNReal.div_self hsum0 hsumtop
  exact_mod_cast hone

/-- **The residue from a volume budget on the shading set itself.**

The most usable sup-free form: the outer shaded union is contained in `Z`, so the budget of
`Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid_of_shadingSet_volume_max` may be imposed
on `Z` directly. What a successor has to produce is therefore a measurable `Z` with

* `U(𝕋, Y) ⊆ Z` (forced by `ShadedBody.ShadedFactorFamily.shade_subset_parent`),
* `Cd⁻¹ · lam ≤ λ(𝕋_ρ, T_ρ ∩ Z)`, and
* `δ^η · |Z| ≤ max (|U(𝕋, Y)|, |B(0, ρ)|)`.

No supremum, no point, no factor family. -/
theorem exists_coarseShadedFamilyAtGrid_of_shadingSet_budget (cfg : VeryNotSticky.{u})
    (𝒱 : ShadedTube.ShadedUniformTubeSet cfg.s cfg.T (Tube.ssfGridLen cfg.δ) cfg.C₀)
    {k : ℕ} (hk : k ≤ Tube.ssfGridLen cfg.δ)
    {ρ : NNReal} (hgrid : Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k = ρ)
    (hρ : ρ ∈ Set.Icc cfg.δ 1)
    (Z : Set (EuclideanSpace ℝ (Fin 3))) (hZ : MeasurableSet Z)
    (hZin : (⋃ i ∈ cfg.s, ((cfg.T i).toShadedBody).shade) ⊆ Z)
    (hfullZ : (cfg.Cd * shadingMultiplicityEstimateForRhoTubes.C)⁻¹ * cfg.lam ≤
      ShadedBody.fullness (cfg.activeTubeNodes 𝒱.tubeUniform k)
        (cfg.coarseShadeAt 𝒱 k Z hZ))
    (hbudget : (cfg.δ : ENNReal) ^ cfg.η * volume Z ≤
      max (volume (⋃ i ∈ cfg.s, ((cfg.T i).toShadedBody).shade))
        (volume (ball (0 : EuclideanSpace ℝ (Fin 3)) (ρ : ℝ)))) :
    ∃ G : ShadedFactorFamily (EuclideanSpace ℝ (Fin 3)) cfg.ι cfg.ι,
      G.innerSet = cfg.s ∧
      (∀ i ∈ cfg.s, G.innerBody i = (cfg.T i).toShadedBody) ∧
      G.outerSet = cfg.activeTubeNodes 𝒱.tubeUniform k ∧
      (∀ j ∈ G.outerSet,
        (G.outerBody j).toConvexSpaceBody =
          (𝒱.tubeUniform.cover.tube k j).toConvexSpaceBody) ∧
      (cfg.Cd * shadingMultiplicityEstimateForRhoTubes.C)⁻¹ * cfg.lam ≤
        ShadedBody.fullness G.outerSet G.outerBody ∧
      (∀ x ∈ ⋃ j ∈ G.outerSet, (G.outerBody j).shade,
        (cfg.δ : ENNReal) ^ cfg.η *
            (((shadingMultiplicityEstimateForRhoTubes.C : NNReal) : ENNReal)⁻¹ *
                volume (⋃ j ∈ G.outerSet, (G.outerBody j).shade) *
              (volume ((⋃ i ∈ G.innerSet, (G.innerBody i).shade) ∩ ball x (ρ : ℝ)) /
                volume (ball x (ρ : ℝ)))) ≤
          volume (⋃ i ∈ G.innerSet, (G.innerBody i).shade)) := by
  classical
  refine exists_coarseShadedFamilyAtGrid_of_shadingSet_volume_max cfg 𝒱 hk hgrid hρ Z hZ hZin
    hfullZ (le_trans ?_ hbudget)
  gcongr
  exact Set.iUnion₂_subset (fun _ _ => Set.inter_subset_right)

/-- **The residue from a single inequality, with no set and no point in it.**

Take the saturated shading `Z = ⋃ 𝕋_ρ`. Its outer fullness is `1`
(`Kakeya.VeryNotSticky.fullness_coarseShadeAt_eq_one`), which dominates
`(Cd · C)⁻¹ · lam` because `Kakeya.VeryNotSticky.lam_le_Cd`. So the whole residue follows from

  `δ^η · |⋃ 𝕋_ρ| ≤ max (|U(𝕋, Y)|, |B(0, ρ)|)`.

This is the strongest statement of the shape "the residue is a two-scale volume comparison": no
existential over shadings, no supremum over points, no factor-family bookkeeping. It is *not*
true for an arbitrary configuration — the saturated shading is the extreme choice, and the
inequality fails as soon as the coarse union is more than `δ^{-η}` times the inner shaded union
while `ρ` is small — but it isolates one honest sufficient condition, and it is the one that a
consumer able to bound `|⋃ 𝕋_ρ|` can discharge. The intermediate choices of `Z` are covered by
`Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid_of_shadingSet_budget`. -/
theorem exists_coarseShadedFamilyAtGrid_of_coarseVolume (cfg : VeryNotSticky.{u})
    (𝒱 : ShadedTube.ShadedUniformTubeSet cfg.s cfg.T (Tube.ssfGridLen cfg.δ) cfg.C₀)
    {k : ℕ} (hk : k ≤ Tube.ssfGridLen cfg.δ)
    {ρ : NNReal} (hgrid : Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k = ρ)
    (hρ : ρ ∈ Set.Icc cfg.δ 1)
    (hvol : (cfg.δ : ENNReal) ^ cfg.η *
        volume (⋃ j ∈ cfg.activeTubeNodes 𝒱.tubeUniform k,
          (𝒱.tubeUniform.cover.tube k j).toConvexSpaceBody.carrier) ≤
      max (volume (⋃ i ∈ cfg.s, ((cfg.T i).toShadedBody).shade))
        (volume (ball (0 : EuclideanSpace ℝ (Fin 3)) (ρ : ℝ)))) :
    ∃ G : ShadedFactorFamily (EuclideanSpace ℝ (Fin 3)) cfg.ι cfg.ι,
      G.innerSet = cfg.s ∧
      (∀ i ∈ cfg.s, G.innerBody i = (cfg.T i).toShadedBody) ∧
      G.outerSet = cfg.activeTubeNodes 𝒱.tubeUniform k ∧
      (∀ j ∈ G.outerSet,
        (G.outerBody j).toConvexSpaceBody =
          (𝒱.tubeUniform.cover.tube k j).toConvexSpaceBody) ∧
      (cfg.Cd * shadingMultiplicityEstimateForRhoTubes.C)⁻¹ * cfg.lam ≤
        ShadedBody.fullness G.outerSet G.outerBody ∧
      (∀ x ∈ ⋃ j ∈ G.outerSet, (G.outerBody j).shade,
        (cfg.δ : ENNReal) ^ cfg.η *
            (((shadingMultiplicityEstimateForRhoTubes.C : NNReal) : ENNReal)⁻¹ *
                volume (⋃ j ∈ G.outerSet, (G.outerBody j).shade) *
              (volume ((⋃ i ∈ G.innerSet, (G.innerBody i).shade) ∩ ball x (ρ : ℝ)) /
                volume (ball x (ρ : ℝ)))) ≤
          volume (⋃ i ∈ G.innerSet, (G.innerBody i).shade)) := by
  classical
  set Z : Set (EuclideanSpace ℝ (Fin 3)) :=
    ⋃ j ∈ cfg.activeTubeNodes 𝒱.tubeUniform k,
      (𝒱.tubeUniform.cover.tube k j).toConvexSpaceBody.carrier with hZdef
  have hZ : MeasurableSet Z :=
    Finset.measurableSet_biUnion _
      (fun j _ => (𝒱.tubeUniform.cover.tube k j).toConvexSpaceBody.isCompact'.isClosed.measurableSet)
  have hparent_mem : ∀ i ∈ cfg.s, 𝒱.tubeUniform.cover.assign k i
      ∈ cfg.activeTubeNodes 𝒱.tubeUniform k := by
    intro i hi
    rw [activeTubeNodes, Finset.mem_filter]
    refine ⟨𝒱.tubeUniform.cover.assign_mem k hk i hi, ⟨i, ?_⟩⟩
    simp [tubeFibre, Tube.coverClass, hi]
  have hZin : (⋃ i ∈ cfg.s, ((cfg.T i).toShadedBody).shade) ⊆ Z := by
    refine Set.iUnion₂_subset (fun i hi => ?_)
    have hle : ((cfg.T i).toShadedBody).toConvexSpaceBody ≤
        (𝒱.tubeUniform.cover.tube k (𝒱.tubeUniform.cover.assign k i)).toConvexSpaceBody := by
      simpa using 𝒱.tubeUniform.cover.le_tube_assign k hk i hi
    have hsub : ((cfg.T i).toShadedBody).shade ⊆
        (𝒱.tubeUniform.cover.tube k (𝒱.tubeUniform.cover.assign k i)).toConvexSpaceBody.carrier :=
      fun x hx => hle ((cfg.T i).toShadedBody.shade_subset hx)
    exact hsub.trans (Set.subset_biUnion_of_mem
      (u := fun j => (𝒱.tubeUniform.cover.tube k j).toConvexSpaceBody.carrier)
      (hparent_mem i hi))
  have hfull1 : ShadedBody.fullness (cfg.activeTubeNodes 𝒱.tubeUniform k)
      (cfg.coarseShadeAt 𝒱 k Z hZ) = 1 :=
    cfg.fullness_coarseShadeAt_eq_one 𝒱 hk hZ
      (fun j hj => Set.subset_biUnion_of_mem
        (u := fun j => (𝒱.tubeUniform.cover.tube k j).toConvexSpaceBody.carrier) hj)
  have hfullZ : (cfg.Cd * shadingMultiplicityEstimateForRhoTubes.C)⁻¹ * cfg.lam ≤
      ShadedBody.fullness (cfg.activeTubeNodes 𝒱.tubeUniform k)
        (cfg.coarseShadeAt 𝒱 k Z hZ) := by
    rw [hfull1, ShadedBody.shadingMultiplicityEstimateForRhoTubes.C, mul_one]
    have hCd0 : cfg.Cd ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one cfg.hCd)
    calc cfg.Cd⁻¹ * cfg.lam ≤ cfg.Cd⁻¹ * cfg.Cd := by gcongr; exact cfg.lam_le_Cd
      _ = 1 := inv_mul_cancel₀ hCd0
  exact exists_coarseShadedFamilyAtGrid_of_shadingSet_budget cfg 𝒱 hk hgrid hρ Z hZ hZin hfullZ
    hvol

/-- **A closed instance of the residue: few enough coarse bodies at the grid index.**

`Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid_of_coarseVolume` is a reduction, and this
is a check that it is a *usable* one: the coarse union is at most `|𝕋_ρ|` node-tube volumes, each
at most `Tube.volume_le.C 3 · ρ²`, so the residue holds outright at any grid index whose active
node family satisfies

  `δ^η · |𝕋_ρ| · C · ρ² ≤ |B(0, ρ)|`.

The regime is narrow — with `|B(0,ρ)| ≍ ρ³` it reads `|𝕋_ρ| ≲ ρ · δ^{-η}`, so it is the
few-coarse-bodies end of the range — but it is a genuine, unconditional instance of the residue
at the placeholder constant, and it shows that neither the volume reduction nor the residue is
vacuous. -/
theorem exists_coarseShadedFamilyAtGrid_of_card_activeTubeNodes (cfg : VeryNotSticky.{u})
    (𝒱 : ShadedTube.ShadedUniformTubeSet cfg.s cfg.T (Tube.ssfGridLen cfg.δ) cfg.C₀)
    {k : ℕ} (hk : k ≤ Tube.ssfGridLen cfg.δ)
    {ρ : NNReal} (hgrid : Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k = ρ)
    (hρ : ρ ∈ Set.Icc cfg.δ 1)
    (hcard : (cfg.δ : ENNReal) ^ cfg.η *
        (((cfg.activeTubeNodes 𝒱.tubeUniform k).card : ENNReal) *
          (((_root_.Tube.volume_le.C 3 : NNReal) : ENNReal) * (ρ : ENNReal) ^ 2)) ≤
      volume (ball (0 : EuclideanSpace ℝ (Fin 3)) (ρ : ℝ))) :
    ∃ G : ShadedFactorFamily (EuclideanSpace ℝ (Fin 3)) cfg.ι cfg.ι,
      G.innerSet = cfg.s ∧
      (∀ i ∈ cfg.s, G.innerBody i = (cfg.T i).toShadedBody) ∧
      G.outerSet = cfg.activeTubeNodes 𝒱.tubeUniform k ∧
      (∀ j ∈ G.outerSet,
        (G.outerBody j).toConvexSpaceBody =
          (𝒱.tubeUniform.cover.tube k j).toConvexSpaceBody) ∧
      (cfg.Cd * shadingMultiplicityEstimateForRhoTubes.C)⁻¹ * cfg.lam ≤
        ShadedBody.fullness G.outerSet G.outerBody ∧
      (∀ x ∈ ⋃ j ∈ G.outerSet, (G.outerBody j).shade,
        (cfg.δ : ENNReal) ^ cfg.η *
            (((shadingMultiplicityEstimateForRhoTubes.C : NNReal) : ENNReal)⁻¹ *
                volume (⋃ j ∈ G.outerSet, (G.outerBody j).shade) *
              (volume ((⋃ i ∈ G.innerSet, (G.innerBody i).shade) ∩ ball x (ρ : ℝ)) /
                volume (ball x (ρ : ℝ)))) ≤
          volume (⋃ i ∈ G.innerSet, (G.innerBody i).shade)) := by
  classical
  refine exists_coarseShadedFamilyAtGrid_of_coarseVolume cfg 𝒱 hk hgrid hρ
    (le_trans ?_ (le_trans hcard (le_max_right _ _)))
  have hfr : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
  have hg1 : Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k ≤ 1 := by rw [hgrid]; exact hρ.2
  have hper : ∀ j : cfg.ι,
      volume ((𝒱.tubeUniform.cover.tube k j).toConvexSpaceBody.carrier) ≤
        ((_root_.Tube.volume_le.C 3 : NNReal) : ENNReal) * (ρ : ENNReal) ^ 2 := by
    intro j
    have h := _root_.Tube.volume_le hg1 (𝒱.tubeUniform.cover.tube k j)
    rw [hfr] at h
    refine h.trans (le_of_eq ?_)
    rw [hgrid]
  have hcov : volume (⋃ j ∈ cfg.activeTubeNodes 𝒱.tubeUniform k,
      (𝒱.tubeUniform.cover.tube k j).toConvexSpaceBody.carrier) ≤
        ((cfg.activeTubeNodes 𝒱.tubeUniform k).card : ENNReal) *
          (((_root_.Tube.volume_le.C 3 : NNReal) : ENNReal) * (ρ : ENNReal) ^ 2) := by
    calc volume (⋃ j ∈ cfg.activeTubeNodes 𝒱.tubeUniform k,
            (𝒱.tubeUniform.cover.tube k j).toConvexSpaceBody.carrier)
        ≤ ∑ j ∈ cfg.activeTubeNodes 𝒱.tubeUniform k,
            volume ((𝒱.tubeUniform.cover.tube k j).toConvexSpaceBody.carrier) :=
          measure_biUnion_finset_le _ _
      _ ≤ ∑ _j ∈ cfg.activeTubeNodes 𝒱.tubeUniform k,
            (((_root_.Tube.volume_le.C 3 : NNReal) : ENNReal) * (ρ : ENNReal) ^ 2) :=
          Finset.sum_le_sum (fun j _ => hper j)
      _ = ((cfg.activeTubeNodes 𝒱.tubeUniform k).card : ENNReal) *
            (((_root_.Tube.volume_le.C 3 : NNReal) : ENNReal) * (ρ : ENNReal) ^ 2) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  gcongr

/-! ## The coarse end of the grid is unconditional, and the constant is priced

This section answers two questions about
`Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid` that the reduction lemmas above leave
open, and records a third reduction that supersedes the `max` form.

**1. A large unconditional range.** `Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid_of_coarseVolume`
reduces the residue to `δ^η · |⋃ 𝕋_ρ| ≤ max (|U(𝕋,Y)|, |B(0,ρ)|)`, and the *left* side of that
inequality is bounded with no hypotheses at all: every active node tube contains a member of
`𝕋`, every member lies in `B_1`, and a node tube has a unit core and radius `≤ 1`, so
`⋃ 𝕋_ρ ⊆ B(0,4)` (`Kakeya.VeryNotSticky.activeTubeNodes_carrier_subset_closedBall`). Hence the
residue holds outright at every grid scale with `64 · δ^η ≤ ρ³`, i.e. at every
`ρ ≥ 4 δ^{η/3}` (`Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid_of_gridScale_ge`). What
is left open is only the *fine* end of the grid,
`ρ < 4 δ^{η/3}` — a strictly smaller range than the `|𝕋_ρ| ≲ ρ δ^{-η}` window of
`Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid_of_card_activeTubeNodes`, and one that
does not read the node count at all.

That range is provably nonempty for *every* configuration, not merely for small `δ`: the
absorption clause `Kakeya.VeryNotSticky.aScaleData_absorb` already forces `δ^η ≤ 1/15625`
(`Kakeya.VeryNotSticky.rpow_eta_absorb_le_one`), because the accumulated scale-`r` constant
contains the covering number `5³` of the re-centring. Hence
`Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid_top` — the residue at the top grid index,
with **no hypothesis at all** — and
`Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid_of_gridScale_ge_const` at every
`ρ ≥ 4/25`.

**2. The loss constant is priced, and it is not the repair.** Read the shading-set route at a
free loss `C` in place of `Kakeya.ShadedBody.shadingMultiplicityEstimateForRhoTubes.C`: the
fullness demand becomes `(Cd·C)⁻¹ lam` and the budget becomes `δ^η |Z| ≤ C · max(…)`. Both
sides move, and `Kakeya.VeryNotSticky.shadingSet_budget_necessary` computes the net: any such
`Z` must satisfy

  `δ^{3η} · c · ρ² ≤ C² · max (|U(𝕋,Y)|, |B(0,ρ)|)`,   `c = Tube.le_volume.c 3`,

because fullness `f` forces `|Z| ≥ f · c · ρ²` (`Kakeya.VeryNotSticky.le_volume_of_fullness_coarseShadeAt`;
the coarse multiplicity is at most `|𝕋_ρ|`) and `lam_ge` forces `f ≥ C⁻¹ δ^{2η}`. So **the loss
constant buys exactly a factor `C²`, and nothing else.** Below the ball threshold this is a
lower bound on the shaded union of the order of *one node tube*
(`Kakeya.VeryNotSticky.shadingSet_budget_forces_volume`), while the only lower bound the
configuration supplies is of the order of *one `δ`-tube's shading*
(`Kakeya.VeryNotSticky.le_volume_innerShadedUnion`). The gap between `ρ²` and `δ²` is a power
of `δ`; a dimensional constant such as `ShadedBody.rhoTubesInducedFullnessLoss 3` cannot close
it. That settles, negatively, the question of whether replacing the placeholder `C = 1` by the
honest dimensional loss makes the two conjuncts jointly satisfiable through this route.

**3. Any lower bound on `|U(𝕋,Y)|` that closes the budget is circular.** The comparison
`δ^η |⋃ 𝕋_ρ| ≤ |U(𝕋,Y)|` — the weakest hypothesis that discharges
`…_of_coarseVolume` outright — implies a bound on the *shaded multiplicity*
`µ(𝕋,Y)` (`Kakeya.VeryNotSticky.multiplicity_le_of_coarseVolumeComparison`): with
`∑_i |T_i| ≤ δ^{-η} |B_1|` from `maxDensity_le` and `|⋃𝕋_ρ| ≥ c ρ²` from one node tube, it
gives `µ(𝕋,Y) ≤ δ^{-2η} |B_1| / (c ρ²)`. At the top grid index, where `ρ = 1`, that reads
`µ(𝕋,Y) ≤ δ^{-2η} |B_1| / c` (`Kakeya.VeryNotSticky.multiplicity_le_of_coarseVolumeComparison_zero`)
— an absolute multiplicity bound, strictly stronger than the conclusion
`µ ≤ δ^{ν-η} |𝕋|^β` that `Kakeya.multiplicity_le_of_card_isEssDistinct_ge` exists to prove. So
such a clause may not be added to `Kakeya.VeryNotSticky`: no producer can supply it without
already having Main Lemma 2.

**4. The `max` reduction is sufficient but not necessary.**
`Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid_of_shadingSet_supBall` reduces the residue
to the inequality it *really* is,

  `δ^η · |U(𝕋_ρ,Y_{𝕋_ρ})| · |U(𝕋,Y) ∩ B(x,ρ)| ≤ |U(𝕋,Y)| · |B(0,ρ)|`  for every `x`,

with no division and no fullness-independent slack. `Kakeya.VeryNotSticky.mul_volume_inter_le_of_max_le`
shows that the hypothesis of
`Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid_of_shadingSet_volume_max` implies it, so
the sup form is the more general of the two; the converse fails whenever `U(𝕋,Y)` is spread out
at scale `ρ`, since then `|U(𝕋,Y) ∩ B(x,ρ)| ≪ min(|U(𝕋,Y)|, |B(0,ρ)|)` for every `x`. The
content the `max` form discards is exactly the non-concentration of `U(𝕋,Y)` in `ρ`-balls. -/

open MeasureTheory Metric Set ShadedBody in
/-- **The active node family at a grid index is nonempty.**

Every member of `𝕋` is assigned to a node, and that node then has a nonempty fibre, so it is
active; `𝕋` is nonempty by the fixed-scale count `Kakeya.VeryNotSticky.tube_count`. (A
companion of this statement, taking the nonemptiness of `𝕋` as a hypothesis, is proved
downstream in `Kakeya.DimensionThree.MainLemma2.AScaleRounding`, which this module does not
import.) -/
theorem nonempty_activeTubeNodes (cfg : VeryNotSticky.{u})
    (𝒱 : ShadedTube.ShadedUniformTubeSet cfg.s cfg.T (Tube.ssfGridLen cfg.δ) cfg.C₀)
    {k : ℕ} (hk : k ≤ Tube.ssfGridLen cfg.δ) :
    (cfg.activeTubeNodes 𝒱.tubeUniform k).Nonempty := by
  classical
  have hs : cfg.s.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    have := cfg.tube_count
    rw [h] at this
    simp at this
  obtain ⟨i₀, hi₀⟩ := hs
  refine ⟨𝒱.tubeUniform.cover.assign k i₀, ?_⟩
  rw [activeTubeNodes, Finset.mem_filter]
  refine ⟨𝒱.tubeUniform.cover.assign_mem k hk i₀ hi₀, ⟨i₀, ?_⟩⟩
  simp [tubeFibre, Tube.coverClass, hi₀]

open MeasureTheory Metric Set ShadedBody in
/-- **Every active node tube lies in `B(0,4)`.**

An active node carries a member of `𝕋`, that member lies in `B_1` by
`Kakeya.VeryNotSticky.contained`, and `Tube.subset_ball_of_carrier_subset_ball` puts a
`ρ`-tube containing a tube of `B_1` inside `B(0, 1 + 1 + 2ρ)`; the grid scale is at most `1`.
This is the same computation as `Kakeya.MultiScaleFac.node_carrier_subset_ball`, re-run here
because that module is not in this file's import closure. -/
theorem activeTubeNodes_carrier_subset_closedBall (cfg : VeryNotSticky.{u})
    (𝒱 : ShadedTube.ShadedUniformTubeSet cfg.s cfg.T (Tube.ssfGridLen cfg.δ) cfg.C₀)
    {k : ℕ} (hk : k ≤ Tube.ssfGridLen cfg.δ)
    {j : cfg.ι} (hj : j ∈ cfg.activeTubeNodes 𝒱.tubeUniform k) :
    (𝒱.tubeUniform.cover.tube k j).toConvexSpaceBody.carrier
      ⊆ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 4 := by
  classical
  rw [activeTubeNodes, Finset.mem_filter] at hj
  obtain ⟨-, i, hi⟩ := hj
  simp only [tubeFibre, Tube.coverClass, Finset.mem_filter] at hi
  obtain ⟨his, hij⟩ := hi
  have hcov : ((cfg.T i).toTube).carrier ⊆ (𝒱.tubeUniform.cover.tube k j).carrier := by
    have h := 𝒱.tubeUniform.cover.le_tube_assign k hk i his
    rw [hij] at h
    exact SetLike.coe_subset_coe.mpr h
  have hmain := Tube.subset_ball_of_carrier_subset_ball cfg.hδ
    (Tube.gridScale_pos cfg.hδ (Tube.ssfGridLen cfg.δ) k)
    ((cfg.T i).toTube) (𝒱.tubeUniform.cover.tube k j) (cfg.contained i his) hcov
  refine subset_trans hmain (closedBall_subset_closedBall ?_)
  have hle : (Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k : ℝ) ≤ 1 := by
    exact_mod_cast Tube.gridScale_le_one cfg.hδ1 (Tube.ssfGridLen cfg.δ) k
  linarith

open MeasureTheory Metric Set ShadedBody in
/-- The volume of a ball of radius `ρ` in `EuclideanSpace ℝ (Fin 3)`, in the form the
comparisons below use. -/
theorem volume_ball_eq_pow_mul (ρ : NNReal) :
    volume (ball (0 : EuclideanSpace ℝ (Fin 3)) (ρ : ℝ))
      = (ρ : ENNReal) ^ 3 * volume (ball (0 : EuclideanSpace ℝ (Fin 3)) 1) := by
  have h := MeasureTheory.Measure.addHaar_ball
    (volume : Measure (EuclideanSpace ℝ (Fin 3))) 0 (ρ.coe_nonneg)
  have hfr : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
  rw [hfr] at h
  rw [h, ENNReal.ofReal_pow ρ.coe_nonneg, ENNReal.ofReal_coe_nnreal]

open MeasureTheory Metric Set ShadedBody in
/-- **The coarse union has bounded volume, unconditionally.** `64 = 4³` is the cube of the
containment radius of `Kakeya.VeryNotSticky.activeTubeNodes_carrier_subset_closedBall`. -/
theorem volume_iUnion_activeTubeNodes_le (cfg : VeryNotSticky.{u})
    (𝒱 : ShadedTube.ShadedUniformTubeSet cfg.s cfg.T (Tube.ssfGridLen cfg.δ) cfg.C₀)
    {k : ℕ} (hk : k ≤ Tube.ssfGridLen cfg.δ) :
    volume (⋃ j ∈ cfg.activeTubeNodes 𝒱.tubeUniform k,
        (𝒱.tubeUniform.cover.tube k j).toConvexSpaceBody.carrier)
      ≤ 64 * volume (ball (0 : EuclideanSpace ℝ (Fin 3)) 1) := by
  have hsub : (⋃ j ∈ cfg.activeTubeNodes 𝒱.tubeUniform k,
      (𝒱.tubeUniform.cover.tube k j).toConvexSpaceBody.carrier)
      ⊆ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 4 :=
    Set.iUnion₂_subset fun j hj => cfg.activeTubeNodes_carrier_subset_closedBall 𝒱 hk hj
  refine le_trans (measure_mono hsub) (le_of_eq ?_)
  have h := MeasureTheory.Measure.addHaar_closedBall
    (volume : Measure (EuclideanSpace ℝ (Fin 3))) 0 (by norm_num : (0:ℝ) ≤ 4)
  have hfr : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
  rw [hfr] at h
  rw [h]; norm_num

open MeasureTheory Metric Set ShadedBody in
/-- **The coarse union is at least one node tube.** Used both to price the fullness of a
shading set and to expose the circularity of a two-scale volume comparison. -/
theorem le_volume_iUnion_activeTubeNodes (cfg : VeryNotSticky.{u})
    (𝒱 : ShadedTube.ShadedUniformTubeSet cfg.s cfg.T (Tube.ssfGridLen cfg.δ) cfg.C₀)
    {k : ℕ} (hk : k ≤ Tube.ssfGridLen cfg.δ)
    {ρ : NNReal} (hgrid : Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k = ρ) :
    ((_root_.Tube.le_volume.c 3 : NNReal) : ENNReal) * (ρ : ENNReal) ^ 2
      ≤ volume (⋃ j ∈ cfg.activeTubeNodes 𝒱.tubeUniform k,
          (𝒱.tubeUniform.cover.tube k j).toConvexSpaceBody.carrier) := by
  subst hgrid
  obtain ⟨j₀, hj₀⟩ := cfg.nonempty_activeTubeNodes 𝒱 hk
  have hfr : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
  have h := _root_.Tube.le_volume (𝒱.tubeUniform.cover.tube k j₀)
  rw [hfr] at h
  refine le_trans (by simpa using h) (measure_mono ?_)
  exact Set.subset_biUnion_of_mem
    (u := fun j => (𝒱.tubeUniform.cover.tube k j).toConvexSpaceBody.carrier) hj₀

open MeasureTheory Metric Set ShadedBody in
/-- **The residue holds outright at the coarse end of the grid**, with no hypothesis on the
configuration beyond `64 δ^η ≤ ρ³`.

The saturated shading `Z = ⋃ 𝕋_ρ` is `1`-full, and its volume is at most `|B(0,4)| = 64 |B(0,1)|`
because every active node tube lies in `B(0,4)`; the budget's `|B(0,ρ)| = ρ³ |B(0,1)|` branch
then pays for it. Nothing about `𝕋`, `Y`, `lam`, `Cd`, `maxDensity` or the node count enters. -/
theorem exists_coarseShadedFamilyAtGrid_of_coarseBall (cfg : VeryNotSticky.{u})
    (𝒱 : ShadedTube.ShadedUniformTubeSet cfg.s cfg.T (Tube.ssfGridLen cfg.δ) cfg.C₀)
    {k : ℕ} (hk : k ≤ Tube.ssfGridLen cfg.δ)
    {ρ : NNReal} (hgrid : Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k = ρ)
    (hρ : ρ ∈ Set.Icc cfg.δ 1)
    (hbig : 64 * (cfg.δ : ENNReal) ^ cfg.η ≤ (ρ : ENNReal) ^ 3) :
    ∃ G : ShadedFactorFamily (EuclideanSpace ℝ (Fin 3)) cfg.ι cfg.ι,
      G.innerSet = cfg.s ∧
      (∀ i ∈ cfg.s, G.innerBody i = (cfg.T i).toShadedBody) ∧
      G.outerSet = cfg.activeTubeNodes 𝒱.tubeUniform k ∧
      (∀ j ∈ G.outerSet,
        (G.outerBody j).toConvexSpaceBody =
          (𝒱.tubeUniform.cover.tube k j).toConvexSpaceBody) ∧
      (cfg.Cd * shadingMultiplicityEstimateForRhoTubes.C)⁻¹ * cfg.lam ≤
        ShadedBody.fullness G.outerSet G.outerBody ∧
      (∀ x ∈ ⋃ j ∈ G.outerSet, (G.outerBody j).shade,
        (cfg.δ : ENNReal) ^ cfg.η *
            (((shadingMultiplicityEstimateForRhoTubes.C : NNReal) : ENNReal)⁻¹ *
                volume (⋃ j ∈ G.outerSet, (G.outerBody j).shade) *
              (volume ((⋃ i ∈ G.innerSet, (G.innerBody i).shade) ∩ ball x (ρ : ℝ)) /
                volume (ball x (ρ : ℝ)))) ≤
          volume (⋃ i ∈ G.innerSet, (G.innerBody i).shade)) := by
  refine exists_coarseShadedFamilyAtGrid_of_coarseVolume cfg 𝒱 hk hgrid hρ ?_
  refine le_trans ?_ (le_max_right _ _)
  calc (cfg.δ : ENNReal) ^ cfg.η *
        volume (⋃ j ∈ cfg.activeTubeNodes 𝒱.tubeUniform k,
          (𝒱.tubeUniform.cover.tube k j).toConvexSpaceBody.carrier)
      ≤ (cfg.δ : ENNReal) ^ cfg.η *
          (64 * volume (ball (0 : EuclideanSpace ℝ (Fin 3)) 1)) := by
        gcongr
        exact cfg.volume_iUnion_activeTubeNodes_le 𝒱 hk
    _ = (64 * (cfg.δ : ENNReal) ^ cfg.η) * volume (ball (0 : EuclideanSpace ℝ (Fin 3)) 1) := by
        ring
    _ ≤ (ρ : ENNReal) ^ 3 * volume (ball (0 : EuclideanSpace ℝ (Fin 3)) 1) := by gcongr
    _ = volume (ball (0 : EuclideanSpace ℝ (Fin 3)) (ρ : ℝ)) := (volume_ball_eq_pow_mul ρ).symm

open MeasureTheory Metric Set ShadedBody in
/-- **The same, in scale form**: the residue holds at every grid scale `ρ ≥ 4 δ^{η/3}`.

This is `Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid_of_coarseBall` with the cube taken.
Since `η` is small the threshold `4 δ^{η/3}` is `δ^{o(1)}`, so what is left open is only the
polynomially small end of the grid. -/
theorem exists_coarseShadedFamilyAtGrid_of_gridScale_ge (cfg : VeryNotSticky.{u})
    (𝒱 : ShadedTube.ShadedUniformTubeSet cfg.s cfg.T (Tube.ssfGridLen cfg.δ) cfg.C₀)
    {k : ℕ} (hk : k ≤ Tube.ssfGridLen cfg.δ)
    {ρ : NNReal} (hgrid : Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k = ρ)
    (hρ : ρ ∈ Set.Icc cfg.δ 1)
    (hbig : 4 * cfg.δ ^ (cfg.η / 3) ≤ ρ) :
    ∃ G : ShadedFactorFamily (EuclideanSpace ℝ (Fin 3)) cfg.ι cfg.ι,
      G.innerSet = cfg.s ∧
      (∀ i ∈ cfg.s, G.innerBody i = (cfg.T i).toShadedBody) ∧
      G.outerSet = cfg.activeTubeNodes 𝒱.tubeUniform k ∧
      (∀ j ∈ G.outerSet,
        (G.outerBody j).toConvexSpaceBody =
          (𝒱.tubeUniform.cover.tube k j).toConvexSpaceBody) ∧
      (cfg.Cd * shadingMultiplicityEstimateForRhoTubes.C)⁻¹ * cfg.lam ≤
        ShadedBody.fullness G.outerSet G.outerBody ∧
      (∀ x ∈ ⋃ j ∈ G.outerSet, (G.outerBody j).shade,
        (cfg.δ : ENNReal) ^ cfg.η *
            (((shadingMultiplicityEstimateForRhoTubes.C : NNReal) : ENNReal)⁻¹ *
                volume (⋃ j ∈ G.outerSet, (G.outerBody j).shade) *
              (volume ((⋃ i ∈ G.innerSet, (G.innerBody i).shade) ∩ ball x (ρ : ℝ)) /
                volume (ball x (ρ : ℝ)))) ≤
          volume (⋃ i ∈ G.innerSet, (G.innerBody i).shade)) := by
  refine exists_coarseShadedFamilyAtGrid_of_coarseBall cfg 𝒱 hk hgrid hρ ?_
  have hnn : (64 : NNReal) * cfg.δ ^ cfg.η ≤ ρ ^ (3 : ℕ) := by
    have hcube : (4 * cfg.δ ^ (cfg.η / 3)) ^ (3 : ℕ) = 64 * cfg.δ ^ cfg.η := by
      rw [mul_pow, ← NNReal.rpow_natCast (cfg.δ ^ (cfg.η / 3)) 3, ← NNReal.rpow_mul]
      norm_num
    calc (64 : NNReal) * cfg.δ ^ cfg.η = (4 * cfg.δ ^ (cfg.η / 3)) ^ (3 : ℕ) := hcube.symm
      _ ≤ ρ ^ (3 : ℕ) := by gcongr
  have h := ENNReal.coe_le_coe.mpr hnn
  rw [ENNReal.coe_mul, ENNReal.coe_pow, ENNReal.coe_rpow_of_nonneg _ cfg.hη.le] at h
  simpa using h

/-- **The ball half of the accumulated scale-`r` constant is `125`**, at the placeholder loss
`Kakeya.ShadedBody.shadingMultiplicityEstimateForRhoTubes.C = 1`: `5³` is the covering number of
blueprint `lem:ballCoverHalfRadius` spent by the re-centring. -/
theorem aScaleBallConstant_shadingMultiplicity_eq : Kakeya.aScaleBallConstant
    ShadedBody.shadingMultiplicityEstimateForRhoTubes.C = 125 := by
  rw [Kakeya.aScaleBallConstant, ShadedBody.shadingMultiplicityEstimateForRhoTubes.C,
    Kakeya.separatedNetCoverConstant]
  norm_num

/-- **The configuration's own absorption clause already forces `δ^η ≤ 1/15625`.**

`Kakeya.VeryNotSticky.aScaleData_absorb` says `C_⋆(C₀,D₀)² ≤ δ^{-η}`, and
`C_⋆ ≥ aScaleBallConstant 1 = 125` by
`Kakeya.aScaleBallConstant_le_aScaleDataConstant`. So `15625 ≤ δ^{-η}`. This is what makes the
unconditional range of `Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid_of_coarseBall`
nonempty: the threshold `64 δ^η ≤ ρ³` is met at `ρ = 1` outright, and in fact at every
`ρ ≥ 4/25`. -/
theorem rpow_eta_absorb_le_one (cfg : VeryNotSticky.{u}) :
    15625 * (cfg.δ : ENNReal) ^ cfg.η ≤ 1 := by
  have hmono : Kakeya.aScaleBallConstant _root_.ShadedBody.shadingMultiplicityEstimateForRhoTubes.C
      ≤ Kakeya.aScaleBallConstant (max 1 (Kakeya.Tube.dilateFullness.C 3)) := by
    unfold Kakeya.aScaleBallConstant
    rw [_root_.ShadedBody.shadingMultiplicityEstimateForRhoTubes.C]
    gcongr
    exact le_max_left _ _
  have h125 : (125 : NNReal) ≤ Kakeya.aScaleDataConstant cfg.C₀ cfg.D₀ := by
    rw [← aScaleBallConstant_shadingMultiplicity_eq]
    exact le_trans hmono (Kakeya.aScaleBallConstant_le_aScaleDataConstant cfg.C₀ cfg.D₀)
  have hsq : (15625 : ENNReal) ≤ (Kakeya.aScaleDataConstant cfg.C₀ cfg.D₀ : ENNReal) ^ 2 := by
    have hc : ((125 : NNReal) : ENNReal) ≤ (Kakeya.aScaleDataConstant cfg.C₀ cfg.D₀ : ENNReal) :=
      ENNReal.coe_le_coe.mpr h125
    calc (15625 : ENNReal) = ((125 : NNReal) : ENNReal) ^ 2 := by norm_num
      _ ≤ (Kakeya.aScaleDataConstant cfg.C₀ cfg.D₀ : ENNReal) ^ 2 := by gcongr
  have habs := cfg.aScaleData_absorb
  have hδ0 : (cfg.δ : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr cfg.hδ.ne'
  have hδtop : (cfg.δ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  calc (15625 : ENNReal) * (cfg.δ : ENNReal) ^ cfg.η
      ≤ (cfg.δ : ENNReal) ^ (-cfg.η) * (cfg.δ : ENNReal) ^ cfg.η := by
        gcongr
        exact le_trans hsq habs
    _ = 1 := by
        rw [← ENNReal.rpow_add _ _ hδ0 hδtop]
        simp

open MeasureTheory Metric Set ShadedBody in
/-- **The residue holds at the top grid index, with no hypotheses at all.**

At `k = 0` the grid scale is `1`, and `Kakeya.VeryNotSticky.rpow_eta_absorb_le_one` discharges
the threshold of `Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid_of_coarseBall`. This is
the non-vacuity check for that lemma — its range of grid scales is nonempty for *every*
configuration — and, incidentally, the first unconditional instance of
`Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid` that carries no side condition
whatsoever. -/
theorem exists_coarseShadedFamilyAtGrid_top (cfg : VeryNotSticky.{u})
    (𝒱 : ShadedTube.ShadedUniformTubeSet cfg.s cfg.T (Tube.ssfGridLen cfg.δ) cfg.C₀) :
    ∃ G : ShadedFactorFamily (EuclideanSpace ℝ (Fin 3)) cfg.ι cfg.ι,
      G.innerSet = cfg.s ∧
      (∀ i ∈ cfg.s, G.innerBody i = (cfg.T i).toShadedBody) ∧
      G.outerSet = cfg.activeTubeNodes 𝒱.tubeUniform 0 ∧
      (∀ j ∈ G.outerSet,
        (G.outerBody j).toConvexSpaceBody =
          (𝒱.tubeUniform.cover.tube 0 j).toConvexSpaceBody) ∧
      (cfg.Cd * shadingMultiplicityEstimateForRhoTubes.C)⁻¹ * cfg.lam ≤
        ShadedBody.fullness G.outerSet G.outerBody ∧
      (∀ x ∈ ⋃ j ∈ G.outerSet, (G.outerBody j).shade,
        (cfg.δ : ENNReal) ^ cfg.η *
            (((shadingMultiplicityEstimateForRhoTubes.C : NNReal) : ENNReal)⁻¹ *
                volume (⋃ j ∈ G.outerSet, (G.outerBody j).shade) *
              (volume ((⋃ i ∈ G.innerSet, (G.innerBody i).shade) ∩ ball x ((1 : NNReal) : ℝ)) /
                volume (ball x ((1 : NNReal) : ℝ)))) ≤
          volume (⋃ i ∈ G.innerSet, (G.innerBody i).shade)) := by
  refine exists_coarseShadedFamilyAtGrid_of_coarseBall cfg 𝒱 (Nat.zero_le _)
    (Tube.gridScale_zero _ _) ⟨cfg.hδ1, le_rfl⟩ ?_
  have h := cfg.rpow_eta_absorb_le_one
  calc 64 * (cfg.δ : ENNReal) ^ cfg.η ≤ 15625 * (cfg.δ : ENNReal) ^ cfg.η := by
        gcongr; norm_num
    _ ≤ 1 := h
    _ = ((1 : NNReal) : ENNReal) ^ 3 := by norm_num

open MeasureTheory Metric Set ShadedBody in
/-- **The residue holds at every grid scale `ρ ≥ 4/25`, with no hypotheses at all.**

The hypothesis is written division-free as `4 ≤ 25 ρ`. This is the coarsest, entirely
configuration-independent corner of
`Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid_of_gridScale_ge`, obtained by feeding it
the fixed bound `δ^η ≤ 1/15625` of `Kakeya.VeryNotSticky.rpow_eta_absorb_le_one` instead of the
sharp threshold `4 δ^{η/3}`; for small `δ` the sharp threshold is far smaller. -/
theorem exists_coarseShadedFamilyAtGrid_of_gridScale_ge_const (cfg : VeryNotSticky.{u})
    (𝒱 : ShadedTube.ShadedUniformTubeSet cfg.s cfg.T (Tube.ssfGridLen cfg.δ) cfg.C₀)
    {k : ℕ} (hk : k ≤ Tube.ssfGridLen cfg.δ)
    {ρ : NNReal} (hgrid : Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k = ρ)
    (hρ : ρ ∈ Set.Icc cfg.δ 1) (hρbig : (4 : NNReal) ≤ 25 * ρ) :
    ∃ G : ShadedFactorFamily (EuclideanSpace ℝ (Fin 3)) cfg.ι cfg.ι,
      G.innerSet = cfg.s ∧
      (∀ i ∈ cfg.s, G.innerBody i = (cfg.T i).toShadedBody) ∧
      G.outerSet = cfg.activeTubeNodes 𝒱.tubeUniform k ∧
      (∀ j ∈ G.outerSet,
        (G.outerBody j).toConvexSpaceBody =
          (𝒱.tubeUniform.cover.tube k j).toConvexSpaceBody) ∧
      (cfg.Cd * shadingMultiplicityEstimateForRhoTubes.C)⁻¹ * cfg.lam ≤
        ShadedBody.fullness G.outerSet G.outerBody ∧
      (∀ x ∈ ⋃ j ∈ G.outerSet, (G.outerBody j).shade,
        (cfg.δ : ENNReal) ^ cfg.η *
            (((shadingMultiplicityEstimateForRhoTubes.C : NNReal) : ENNReal)⁻¹ *
                volume (⋃ j ∈ G.outerSet, (G.outerBody j).shade) *
              (volume ((⋃ i ∈ G.innerSet, (G.innerBody i).shade) ∩ ball x (ρ : ℝ)) /
                volume (ball x (ρ : ℝ)))) ≤
          volume (⋃ i ∈ G.innerSet, (G.innerBody i).shade)) := by
  refine exists_coarseShadedFamilyAtGrid_of_coarseBall cfg 𝒱 hk hgrid hρ ?_
  have h := cfg.rpow_eta_absorb_le_one
  have hcube : (64 : ENNReal) ≤ 15625 * (ρ : ENNReal) ^ 3 := by
    have hn : (64 : NNReal) ≤ 15625 * ρ ^ 3 := by
      calc (64 : NNReal) = 4 ^ 3 := by norm_num
        _ ≤ (25 * ρ) ^ 3 := by gcongr
        _ = 15625 * ρ ^ 3 := by ring
    have hcoe := ENNReal.coe_le_coe.mpr hn
    push_cast at hcoe
    exact hcoe
  have h15 : (15625 : ENNReal) ≠ 0 := by norm_num
  have h15t : (15625 : ENNReal) ≠ ⊤ := by norm_num
  refine (ENNReal.mul_le_mul_iff_right h15 h15t).mp ?_
  calc (15625 : ENNReal) * (64 * (cfg.δ : ENNReal) ^ cfg.η)
      = 64 * (15625 * (cfg.δ : ENNReal) ^ cfg.η) := by ring
    _ ≤ 64 * 1 := by gcongr
    _ = 64 := by ring
    _ ≤ 15625 * (ρ : ENNReal) ^ 3 := hcube

open MeasureTheory Metric Set ShadedBody in
/-- **The `max` budget implies the sup-form budget.**

The one-line arithmetic behind
`Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid_of_shadingSet_volume_max`: whichever
branch of the maximum dominates, the corresponding trivial bound on `|U ∩ B(x,ρ)|` — by
`|B(x,ρ)| = |B(0,ρ)|` on one branch, by `|U|` on the other — closes the product estimate. The
converse is false: if `U` is spread out at scale `ρ` then `|U ∩ B(x,ρ)|` is far below both
bounds, and the sup form is satisfied with room the `max` form does not see. -/
theorem mul_volume_inter_le_of_max_le {ρ : NNReal} {a : ENNReal}
    {U : Set (EuclideanSpace ℝ (Fin 3))}
    (h : a ≤ max (volume U) (volume (ball (0 : EuclideanSpace ℝ (Fin 3)) (ρ : ℝ))))
    (x : EuclideanSpace ℝ (Fin 3)) :
    a * volume (U ∩ ball x (ρ : ℝ))
      ≤ volume U * volume (ball (0 : EuclideanSpace ℝ (Fin 3)) (ρ : ℝ)) := by
  have hcenter : volume (ball x (ρ : ℝ))
      = volume (ball (0 : EuclideanSpace ℝ (Fin 3)) (ρ : ℝ)) := by
    rw [EuclideanSpace.volume_ball, EuclideanSpace.volume_ball]
  rcases max_cases (volume U) (volume (ball (0 : EuclideanSpace ℝ (Fin 3)) (ρ : ℝ)))
    with ⟨he, _⟩ | ⟨he, _⟩
  · rw [he] at h
    calc a * volume (U ∩ ball x (ρ : ℝ))
        ≤ volume U * volume (ball x (ρ : ℝ)) := by
          gcongr
          exact Set.inter_subset_right
      _ = volume U * volume (ball (0 : EuclideanSpace ℝ (Fin 3)) (ρ : ℝ)) := by rw [hcenter]
  · rw [he] at h
    calc a * volume (U ∩ ball x (ρ : ℝ))
        ≤ volume (ball (0 : EuclideanSpace ℝ (Fin 3)) (ρ : ℝ)) * volume U := by
          gcongr
          exact Set.inter_subset_left
      _ = volume U * volume (ball (0 : EuclideanSpace ℝ (Fin 3)) (ρ : ℝ)) := by ring

open MeasureTheory Metric Set ShadedBody in
/-- **The residue from the sup-form budget**, which is what the ball conjunct actually is.

Clearing the division and the centre-free ball volume out of the ball conjunct leaves, for a
shading set `Z`,

  `δ^η · |U(𝕋_ρ, Y_{𝕋_ρ})| · |U(𝕋,Y) ∩ B(x,ρ)| ≤ |U(𝕋,Y)| · |B(0,ρ)|`.

This is strictly more general than
`Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid_of_shadingSet_volume_max`, whose
hypothesis implies it by `Kakeya.VeryNotSticky.mul_volume_inter_le_of_max_le`; the difference
is exactly the non-concentration of `U(𝕋, Y)` in `ρ`-balls, which the `max` form throws away
and which the proof of GWZ Lemma 5.11 buys in its Step 5. A successor attacking the fine end of
the grid should use this form, not the `max` form. -/
theorem exists_coarseShadedFamilyAtGrid_of_shadingSet_supBall (cfg : VeryNotSticky.{u})
    (𝒱 : ShadedTube.ShadedUniformTubeSet cfg.s cfg.T (Tube.ssfGridLen cfg.δ) cfg.C₀)
    {k : ℕ} (hk : k ≤ Tube.ssfGridLen cfg.δ)
    {ρ : NNReal} (hgrid : Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k = ρ)
    (Z : Set (EuclideanSpace ℝ (Fin 3))) (hZ : MeasurableSet Z)
    (hZin : (⋃ i ∈ cfg.s, ((cfg.T i).toShadedBody).shade) ⊆ Z)
    (hfullZ : (cfg.Cd * shadingMultiplicityEstimateForRhoTubes.C)⁻¹ * cfg.lam ≤
      ShadedBody.fullness (cfg.activeTubeNodes 𝒱.tubeUniform k)
        (cfg.coarseShadeAt 𝒱 k Z hZ))
    (hsup : ∀ x : EuclideanSpace ℝ (Fin 3),
      (cfg.δ : ENNReal) ^ cfg.η *
          volume (⋃ j ∈ cfg.activeTubeNodes 𝒱.tubeUniform k,
            (cfg.coarseShadeAt 𝒱 k Z hZ j).shade) *
          volume ((⋃ i ∈ cfg.s, ((cfg.T i).toShadedBody).shade) ∩ ball x (ρ : ℝ))
        ≤ volume (⋃ i ∈ cfg.s, ((cfg.T i).toShadedBody).shade) *
            volume (ball (0 : EuclideanSpace ℝ (Fin 3)) (ρ : ℝ))) :
    ∃ G : ShadedFactorFamily (EuclideanSpace ℝ (Fin 3)) cfg.ι cfg.ι,
      G.innerSet = cfg.s ∧
      (∀ i ∈ cfg.s, G.innerBody i = (cfg.T i).toShadedBody) ∧
      G.outerSet = cfg.activeTubeNodes 𝒱.tubeUniform k ∧
      (∀ j ∈ G.outerSet,
        (G.outerBody j).toConvexSpaceBody =
          (𝒱.tubeUniform.cover.tube k j).toConvexSpaceBody) ∧
      (cfg.Cd * shadingMultiplicityEstimateForRhoTubes.C)⁻¹ * cfg.lam ≤
        ShadedBody.fullness G.outerSet G.outerBody ∧
      (∀ x ∈ ⋃ j ∈ G.outerSet, (G.outerBody j).shade,
        (cfg.δ : ENNReal) ^ cfg.η *
            (((shadingMultiplicityEstimateForRhoTubes.C : NNReal) : ENNReal)⁻¹ *
                volume (⋃ j ∈ G.outerSet, (G.outerBody j).shade) *
              (volume ((⋃ i ∈ G.innerSet, (G.innerBody i).shade) ∩ ball x (ρ : ℝ)) /
                volume (ball x (ρ : ℝ)))) ≤
          volume (⋃ i ∈ G.innerSet, (G.innerBody i).shade)) := by
  classical
  refine exists_coarseShadedFamilyAtGrid_of_shadingSet cfg 𝒱 hk hgrid Z hZ hZin hfullZ ?_
  intro x _
  have hC : ((shadingMultiplicityEstimateForRhoTubes.C : NNReal) : ENNReal)⁻¹ = 1 := by
    rw [ShadedBody.shadingMultiplicityEstimateForRhoTubes.C]; simp
  have hcenter : volume (ball x (ρ : ℝ))
      = volume (ball (0 : EuclideanSpace ℝ (Fin 3)) (ρ : ℝ)) := by
    rw [EuclideanSpace.volume_ball, EuclideanSpace.volume_ball]
  have key := hsup x
  rw [← hcenter] at key
  calc (cfg.δ : ENNReal) ^ cfg.η *
        (((shadingMultiplicityEstimateForRhoTubes.C : NNReal) : ENNReal)⁻¹ *
            volume (⋃ j ∈ cfg.activeTubeNodes 𝒱.tubeUniform k,
              (cfg.coarseShadeAt 𝒱 k Z hZ j).shade) *
          (volume ((⋃ i ∈ cfg.s, ((cfg.T i).toShadedBody).shade) ∩ ball x (ρ : ℝ)) /
            volume (ball x (ρ : ℝ))))
      = ((cfg.δ : ENNReal) ^ cfg.η *
          volume (⋃ j ∈ cfg.activeTubeNodes 𝒱.tubeUniform k,
            (cfg.coarseShadeAt 𝒱 k Z hZ j).shade) *
          volume ((⋃ i ∈ cfg.s, ((cfg.T i).toShadedBody).shade) ∩ ball x (ρ : ℝ)))
          / volume (ball x (ρ : ℝ)) := by
        rw [hC, one_mul, div_eq_mul_inv, div_eq_mul_inv]
        ring
    _ ≤ volume (⋃ i ∈ cfg.s, ((cfg.T i).toShadedBody).shade) :=
        ENNReal.div_le_of_le_mul key

open MeasureTheory Metric Set ShadedBody in
/-- **Fullness costs volume**: a shading set that makes the node family `f`-full has volume at
least `f` times one node tube.

The coarse multiplicity is at most `|𝕋_ρ|`, so `∑_j |T_{ρ,j} ∩ Z| ≤ |𝕋_ρ| · |Z|`, while
`∑_j |T_{ρ,j}| ≥ |𝕋_ρ| · c ρ²` by `Tube.le_volume`; the node count cancels. This is the
lower end of the two-sided budget, and it is the only place where the constant of the residue
can be paid for. -/
theorem le_volume_of_fullness_coarseShadeAt (cfg : VeryNotSticky.{u})
    (𝒱 : ShadedTube.ShadedUniformTubeSet cfg.s cfg.T (Tube.ssfGridLen cfg.δ) cfg.C₀)
    {k : ℕ} (hk : k ≤ Tube.ssfGridLen cfg.δ)
    {ρ : NNReal} (hgrid : Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k = ρ)
    {Z : Set (EuclideanSpace ℝ (Fin 3))} (hZ : MeasurableSet Z) {f : NNReal}
    (hf : f ≤ ShadedBody.fullness (cfg.activeTubeNodes 𝒱.tubeUniform k)
      (cfg.coarseShadeAt 𝒱 k Z hZ)) :
    (f : ENNReal) * (((_root_.Tube.le_volume.c 3 : NNReal)) : ENNReal) * (ρ : ENNReal) ^ 2
      ≤ volume Z := by
  classical
  subst hgrid
  set A := cfg.activeTubeNodes 𝒱.tubeUniform k with hA
  set V := cfg.coarseShadeAt 𝒱 k Z hZ with hV
  obtain ⟨j₀, hj₀⟩ := cfg.nonempty_activeTubeNodes 𝒱 hk
  have hcard0 : (A.card : ENNReal) ≠ 0 := by
    have : 0 < A.card := Finset.card_pos.mpr ⟨j₀, hj₀⟩
    exact_mod_cast this.ne'
  have hcardtop : (A.card : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hfr : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
  have hcar : ((A.card : ENNReal)) *
      ((((_root_.Tube.le_volume.c 3 : NNReal)) : ENNReal) *
        ((Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k : NNReal) : ENNReal) ^ 2)
      ≤ ∑ j ∈ A, volume (V j).carrier := by
    rw [← nsmul_eq_mul]
    refine Finset.card_nsmul_le_sum A _ _ (fun j _ => ?_)
    have h := _root_.Tube.le_volume (𝒱.tubeUniform.cover.tube k j)
    rw [hfr] at h
    exact h
  have hsh : ∑ j ∈ A, volume (V j).shade ≤ ((A.card : ENNReal)) * volume Z := by
    rw [← nsmul_eq_mul]
    refine Finset.sum_le_card_nsmul A _ _ (fun j _ => ?_)
    exact measure_mono Set.inter_subset_right
  have hid : ∑ j ∈ A, volume (V j).shade
      = (ShadedBody.fullness A V : ENNReal) * ∑ j ∈ A, volume (V j).carrier :=
    ShadedBody.sum_volumeReal_shade_eq_fullness_mul A V
  have hchain : ((A.card : ENNReal)) *
      ((f : ENNReal) * ((((_root_.Tube.le_volume.c 3 : NNReal)) : ENNReal) *
        ((Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k : NNReal) : ENNReal) ^ 2))
      ≤ ((A.card : ENNReal)) * volume Z := by
    calc ((A.card : ENNReal)) *
          ((f : ENNReal) * ((((_root_.Tube.le_volume.c 3 : NNReal)) : ENNReal) *
            ((Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k : NNReal) : ENNReal) ^ 2))
        = (f : ENNReal) * (((A.card : ENNReal)) *
            ((((_root_.Tube.le_volume.c 3 : NNReal)) : ENNReal) *
              ((Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k : NNReal) : ENNReal) ^ 2)) := by
          ring
      _ ≤ (ShadedBody.fullness A V : ENNReal) * ∑ j ∈ A, volume (V j).carrier := by
          refine mul_le_mul' (by exact_mod_cast hf) hcar
      _ = ∑ j ∈ A, volume (V j).shade := hid.symm
      _ ≤ ((A.card : ENNReal)) * volume Z := hsh
  have hfin := (ENNReal.mul_le_mul_iff_right hcard0 hcardtop).mp hchain
  calc (f : ENNReal) * (((_root_.Tube.le_volume.c 3 : NNReal)) : ENNReal) *
        ((Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k : NNReal) : ENNReal) ^ 2
      = (f : ENNReal) * ((((_root_.Tube.le_volume.c 3 : NNReal)) : ENNReal) *
          ((Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k : NNReal) : ENNReal) ^ 2) := by ring
    _ ≤ volume Z := hfin

open MeasureTheory Metric Set ShadedBody in
/-- **What the shading-set route costs, at a free loss constant `C`.**

Read the two conjuncts of the residue at a loss `C` in place of the placeholder
`Kakeya.ShadedBody.shadingMultiplicityEstimateForRhoTubes.C = 1`: the fullness demand becomes
`(Cd·C)⁻¹ lam` and the budget becomes `δ^η |Z| ≤ C · max(|U(𝕋,Y)|, |B(0,ρ)|)`. Then any
admissible `Z` forces

  `δ^{3η} · c · ρ² ≤ C² · max (|U(𝕋,Y)|, |B(0,ρ)|)`.

(The exponent is `3η = η + 2η`: one `η` from the budget, and `2η` because the configuration
field `Kakeya.VeryNotSticky.lam_ge` reads `Cd · δ^{2η} ≤ lam`.)

Both occurrences of `C` are what the loss buys, and there are exactly two: one from relaxing
the fullness demand and one from relaxing the budget. **This is the whole of the constant's
contribution.** Since `C` is a dimensional constant while the deficit is a power of `δ` (see
`Kakeya.VeryNotSticky.shadingSet_budget_forces_volume` and
`Kakeya.VeryNotSticky.le_volume_innerShadedUnion`), replacing the placeholder by
`ShadedBody.rhoTubesInducedFullnessLoss 3` does not make this route work. -/
theorem shadingSet_budget_necessary (cfg : VeryNotSticky.{u})
    (𝒱 : ShadedTube.ShadedUniformTubeSet cfg.s cfg.T (Tube.ssfGridLen cfg.δ) cfg.C₀)
    {k : ℕ} (hk : k ≤ Tube.ssfGridLen cfg.δ)
    {ρ : NNReal} (hgrid : Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k = ρ)
    {C : NNReal} (hC : C ≠ 0)
    {Z : Set (EuclideanSpace ℝ (Fin 3))} (hZ : MeasurableSet Z)
    (hfullZ : (cfg.Cd * C)⁻¹ * cfg.lam ≤
      ShadedBody.fullness (cfg.activeTubeNodes 𝒱.tubeUniform k)
        (cfg.coarseShadeAt 𝒱 k Z hZ))
    (hbudget : (cfg.δ : ENNReal) ^ cfg.η * volume Z ≤
      (C : ENNReal) * max (volume (⋃ i ∈ cfg.s, ((cfg.T i).toShadedBody).shade))
        (volume (ball (0 : EuclideanSpace ℝ (Fin 3)) (ρ : ℝ)))) :
    (cfg.δ : ENNReal) ^ (3 * cfg.η) * (((_root_.Tube.le_volume.c 3 : NNReal)) : ENNReal) *
        (ρ : ENNReal) ^ 2
      ≤ (C : ENNReal) ^ 2 *
        max (volume (⋃ i ∈ cfg.s, ((cfg.T i).toShadedBody).shade))
          (volume (ball (0 : EuclideanSpace ℝ (Fin 3)) (ρ : ℝ))) := by
  have hCd0 : cfg.Cd ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one cfg.hCd)
  have h2η : (0 : ℝ) ≤ 2 * cfg.η := by linarith [cfg.hη]
  have hf0 : C⁻¹ * cfg.δ ^ (2 * cfg.η) ≤ (cfg.Cd * C)⁻¹ * cfg.lam := by
    calc C⁻¹ * cfg.δ ^ (2 * cfg.η) = (cfg.Cd * C)⁻¹ * (cfg.Cd * cfg.δ ^ (2 * cfg.η)) := by
          rw [mul_inv]
          field_simp
      _ ≤ (cfg.Cd * C)⁻¹ * cfg.lam := by gcongr; exact cfg.lam_ge
  have hf : C⁻¹ * cfg.δ ^ (2 * cfg.η)
      ≤ ShadedBody.fullness (cfg.activeTubeNodes 𝒱.tubeUniform k)
      (cfg.coarseShadeAt 𝒱 k Z hZ) := le_trans hf0 hfullZ
  have hZlb := cfg.le_volume_of_fullness_coarseShadeAt 𝒱 hk hgrid hZ hf
  have hcoe : ((C⁻¹ * cfg.δ ^ (2 * cfg.η) : NNReal) : ENNReal)
      = (C : ENNReal)⁻¹ * (cfg.δ : ENNReal) ^ (2 * cfg.η) := by
    rw [ENNReal.coe_mul, ENNReal.coe_inv hC, ENNReal.coe_rpow_of_nonneg _ h2η]
  rw [hcoe] at hZlb
  set M : ENNReal := max (volume (⋃ i ∈ cfg.s, ((cfg.T i).toShadedBody).shade))
    (volume (ball (0 : EuclideanSpace ℝ (Fin 3)) (ρ : ℝ))) with hM
  have step1 : (cfg.δ : ENNReal) ^ cfg.η *
      ((C : ENNReal)⁻¹ * (cfg.δ : ENNReal) ^ (2 * cfg.η) *
        (((_root_.Tube.le_volume.c 3 : NNReal)) : ENNReal) * (ρ : ENNReal) ^ 2)
      ≤ (C : ENNReal) * M := le_trans (by gcongr) hbudget
  have hCne : (C : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hC
  have hCtop : (C : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have step2 : (C : ENNReal) *
      ((cfg.δ : ENNReal) ^ cfg.η *
        ((C : ENNReal)⁻¹ * (cfg.δ : ENNReal) ^ (2 * cfg.η) *
          (((_root_.Tube.le_volume.c 3 : NNReal)) : ENNReal) * (ρ : ENNReal) ^ 2))
      ≤ (C : ENNReal) * ((C : ENNReal) * M) := by gcongr
  have hrw : (C : ENNReal) *
      ((cfg.δ : ENNReal) ^ cfg.η *
        ((C : ENNReal)⁻¹ * (cfg.δ : ENNReal) ^ (2 * cfg.η) *
          (((_root_.Tube.le_volume.c 3 : NNReal)) : ENNReal) * (ρ : ENNReal) ^ 2))
      = ((C : ENNReal) * (C : ENNReal)⁻¹) *
        ((cfg.δ : ENNReal) ^ (3 * cfg.η) *
          (((_root_.Tube.le_volume.c 3 : NNReal)) : ENNReal) * (ρ : ENNReal) ^ 2) := by
    rw [show (3 : ℝ) * cfg.η = cfg.η + 2 * cfg.η by ring,
      ENNReal.rpow_add _ _ (ENNReal.coe_ne_zero.mpr cfg.hδ.ne') ENNReal.coe_ne_top]
    ring
  rw [hrw, ENNReal.mul_inv_cancel hCne hCtop, one_mul] at step2
  calc (cfg.δ : ENNReal) ^ (3 * cfg.η) * (((_root_.Tube.le_volume.c 3 : NNReal)) : ENNReal) *
        (ρ : ENNReal) ^ 2 ≤ (C : ENNReal) * ((C : ENNReal) * M) := step2
    _ = (C : ENNReal) ^ 2 * M := by ring

open MeasureTheory Metric Set ShadedBody in
/-- **Below the ball threshold the route demands a lower bound of the order of one node tube.**

If the `|B(0,ρ)|` branch of the budget is too small to pay — which for `ρ` a grid scale below
`c δ^{3η} / (C² |B(0,1)|)` it is, since `|B(0,ρ)| = ρ³|B(0,1)|` while the demand is of order
`ρ²` — then `Kakeya.VeryNotSticky.shadingSet_budget_necessary` becomes a lower bound on the
*fine* shaded union at the *coarse* scale. Compare
`Kakeya.VeryNotSticky.le_volume_innerShadedUnion`, which is the strongest lower bound the
configuration supplies and is of order `δ²`: the two are compatible only for
`ρ ≲ C δ^{1 - η/2}`. -/
theorem shadingSet_budget_forces_volume (cfg : VeryNotSticky.{u})
    (𝒱 : ShadedTube.ShadedUniformTubeSet cfg.s cfg.T (Tube.ssfGridLen cfg.δ) cfg.C₀)
    {k : ℕ} (hk : k ≤ Tube.ssfGridLen cfg.δ)
    {ρ : NNReal} (hgrid : Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k = ρ)
    {C : NNReal} (hC : C ≠ 0)
    {Z : Set (EuclideanSpace ℝ (Fin 3))} (hZ : MeasurableSet Z)
    (hfullZ : (cfg.Cd * C)⁻¹ * cfg.lam ≤
      ShadedBody.fullness (cfg.activeTubeNodes 𝒱.tubeUniform k)
        (cfg.coarseShadeAt 𝒱 k Z hZ))
    (hbudget : (cfg.δ : ENNReal) ^ cfg.η * volume Z ≤
      (C : ENNReal) * max (volume (⋃ i ∈ cfg.s, ((cfg.T i).toShadedBody).shade))
        (volume (ball (0 : EuclideanSpace ℝ (Fin 3)) (ρ : ℝ))))
    (hsmall : (C : ENNReal) ^ 2 * volume (ball (0 : EuclideanSpace ℝ (Fin 3)) (ρ : ℝ))
      < (cfg.δ : ENNReal) ^ (3 * cfg.η) *
        (((_root_.Tube.le_volume.c 3 : NNReal)) : ENNReal) * (ρ : ENNReal) ^ 2) :
    (cfg.δ : ENNReal) ^ (3 * cfg.η) *
        (((_root_.Tube.le_volume.c 3 : NNReal)) : ENNReal) * (ρ : ENNReal) ^ 2
      ≤ (C : ENNReal) ^ 2 * volume (⋃ i ∈ cfg.s, ((cfg.T i).toShadedBody).shade) := by
  have hnec := cfg.shadingSet_budget_necessary 𝒱 hk hgrid hC hZ hfullZ hbudget
  rcases max_cases (volume (⋃ i ∈ cfg.s, ((cfg.T i).toShadedBody).shade))
      (volume (ball (0 : EuclideanSpace ℝ (Fin 3)) (ρ : ℝ))) with ⟨he, _⟩ | ⟨he, _⟩
  · rwa [he] at hnec
  · rw [he] at hnec
    exact absurd (lt_of_le_of_lt hnec hsmall) (lt_irrefl _)

open MeasureTheory Metric Set ShadedBody in
/-- **The only lower bound on `|U(𝕋, Y)|` the configuration supplies**: one `δ`-tube's shading,
`Cd⁻¹ · lam · c · δ²`.

`shading_lb` at any member, `Tube.le_volume` for that member's volume, and monotonicity
of the measure. Nothing in `Kakeya.VeryNotSticky` improves on this: `maxDensity_le` is an
*upper* bound on total tube volume, and `fullness_ge` is a ratio of sums. -/
theorem le_volume_innerShadedUnion (cfg : VeryNotSticky.{u}) :
    (cfg.Cd : ENNReal)⁻¹ *
        ((cfg.lam : ENNReal) *
          ((((_root_.Tube.le_volume.c 3 : NNReal)) : ENNReal) * (cfg.δ : ENNReal) ^ 2))
      ≤ volume (⋃ i ∈ cfg.s, ((cfg.T i).toShadedBody).shade) := by
  classical
  have hs : cfg.s.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    have := cfg.tube_count
    rw [h] at this
    simp at this
  obtain ⟨i₀, hi₀⟩ := hs
  have hfr : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
  have hvol : (((_root_.Tube.le_volume.c 3 : NNReal)) : ENNReal) * (cfg.δ : ENNReal) ^ 2
      ≤ volume ((cfg.T i₀).toShadedBody).carrier := by
    have h := _root_.Tube.le_volume ((cfg.T i₀).toTube)
    rw [hfr] at h
    exact h
  calc (cfg.Cd : ENNReal)⁻¹ *
        ((cfg.lam : ENNReal) *
          ((((_root_.Tube.le_volume.c 3 : NNReal)) : ENNReal) * (cfg.δ : ENNReal) ^ 2))
      ≤ (cfg.Cd : ENNReal)⁻¹ *
          ((cfg.lam : ENNReal) * volume ((cfg.T i₀).toShadedBody).carrier) := by gcongr
    _ ≤ volume ((cfg.T i₀).toShadedBody).shade := cfg.shading_lb i₀ hi₀
    _ ≤ volume (⋃ i ∈ cfg.s, ((cfg.T i).toShadedBody).shade) :=
        measure_mono (Set.subset_biUnion_of_mem
          (u := fun i => ((cfg.T i).toShadedBody).shade) hi₀)

open MeasureTheory Metric Set ShadedBody in
/-- **`maxDensity_le` read at the whole family**: `∑_i |T_i| ≤ δ^{-η} |B_1|`.

The unit ball is a convex test body containing every member, so `Kakeya.densityIn` at it is
the full sum divided by `|B_1|`, and `Kakeya.le_maxDensity` bounds it by `Δ_max(𝕋)`. This is
the *upper* bound recorded in the docstring of
`Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid`; the point of isolating it is that it is
also what makes a lower bound on `|U(𝕋,Y)|` circular. -/
theorem sum_volume_carrier_le (cfg : VeryNotSticky.{u}) :
    ∑ i ∈ cfg.s, volume ((cfg.T i).toShadedBody).carrier
      ≤ (cfg.δ : ENNReal) ^ (-cfg.η) *
          volume (closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1) := by
  have hle : ∀ i ∈ cfg.s, (cfg.T i).toConvexSpaceBody ≤
      (ConvexSpaceBody.closedUnitBall (E := EuclideanSpace ℝ (Fin 3))) :=
    fun i hi => cfg.contained i hi
  have h := Kakeya.sum_volume_eq_densityIn_mul_volume' (s := cfg.s)
    (W := fun i ↦ (cfg.T i).toConvexSpaceBody)
    (K := ConvexSpaceBody.closedUnitBall) hle
  calc ∑ i ∈ cfg.s, volume ((cfg.T i).toShadedBody).carrier
      = Kakeya.densityIn cfg.s (fun i ↦ (cfg.T i).toConvexSpaceBody)
          ConvexSpaceBody.closedUnitBall *
        volume (ConvexSpaceBody.closedUnitBall (E := EuclideanSpace ℝ (Fin 3))).carrier := h
    _ ≤ (cfg.δ : ENNReal) ^ (-cfg.η) *
        volume (closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1) := by
        gcongr
        · exact le_trans (Kakeya.le_maxDensity _ _ _) cfg.maxDensity_le
        · exact subset_rfl

open MeasureTheory Metric Set ShadedBody in
/-- **A lower bound on `|U(𝕋,Y)|` is a multiplicity bound.**

`µ(𝕋,Y) = (∑_i |Y(T_i)|)/|U(𝕋,Y)|`, the numerator is at most `δ^{-η}|B_1|` by
`Kakeya.VeryNotSticky.sum_volume_carrier_le`, so any lower bound `v ≤ |U(𝕋,Y)|` bounds the
multiplicity by anything `B` with `δ^{-η}|B_1| ≤ B v`. This is the mechanism that makes a
volume-comparison field on `Kakeya.VeryNotSticky` circular. -/
theorem multiplicity_le_of_le_volume_innerShadedUnion (cfg : VeryNotSticky.{u})
    {v B : ENNReal}
    (hv : v ≤ volume (⋃ i ∈ cfg.s, ((cfg.T i).toShadedBody).shade))
    (hB : (cfg.δ : ENNReal) ^ (-cfg.η) *
        volume (closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1) ≤ B * v) :
    ShadedBody.multiplicity cfg.s (fun i ↦ (cfg.T i).toShadedBody) ≤ B := by
  rw [ShadedBody.multiplicity_le_iff]
  calc ∑ i ∈ cfg.s, volume (((cfg.T i).toShadedBody)).shade
      ≤ ∑ i ∈ cfg.s, volume (((cfg.T i).toShadedBody)).carrier :=
        Finset.sum_le_sum (fun i _ => measure_mono ((cfg.T i).toShadedBody).shade_subset)
    _ ≤ (cfg.δ : ENNReal) ^ (-cfg.η) *
        volume (closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1) := cfg.sum_volume_carrier_le
    _ ≤ B * v := hB
    _ ≤ B * volume (⋃ i ∈ cfg.s, ((cfg.T i).toShadedBody).shade) := by gcongr

open MeasureTheory Metric Set ShadedBody in
/-- **The two-scale volume comparison is circular.**

`δ^η |⋃ 𝕋_ρ| ≤ |U(𝕋,Y)|` is the weakest hypothesis that discharges
`Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid_of_coarseVolume` outright, and it is the
form in which a successor is tempted to add it as a field of `Kakeya.VeryNotSticky`. It must
not be added: combined with `Kakeya.VeryNotSticky.le_volume_iUnion_activeTubeNodes` and
`Kakeya.VeryNotSticky.sum_volume_carrier_le` it bounds the shaded multiplicity by
`δ^{-2η} |B_1| / (c ρ²)`, and at the top grid index — where `ρ = 1`, see
`Kakeya.VeryNotSticky.multiplicity_le_of_coarseVolumeComparison_zero` — that is an absolute
bound `µ(𝕋,Y) ≤ δ^{-2η}|B_1|/c`, strictly stronger than the conclusion
`µ ≤ δ^{ν-η}|𝕋|^β` of `Kakeya.multiplicity_le_of_card_isEssDistinct_ge`. A field no producer can
supply without already proving Main Lemma 2 is the shell game this development forbids. -/
theorem multiplicity_le_of_coarseVolumeComparison (cfg : VeryNotSticky.{u})
    (𝒱 : ShadedTube.ShadedUniformTubeSet cfg.s cfg.T (Tube.ssfGridLen cfg.δ) cfg.C₀)
    {k : ℕ} (hk : k ≤ Tube.ssfGridLen cfg.δ)
    {ρ : NNReal} (hgrid : Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k = ρ)
    {B : ENNReal}
    (hcmp : (cfg.δ : ENNReal) ^ cfg.η *
        volume (⋃ j ∈ cfg.activeTubeNodes 𝒱.tubeUniform k,
          (𝒱.tubeUniform.cover.tube k j).toConvexSpaceBody.carrier)
      ≤ volume (⋃ i ∈ cfg.s, ((cfg.T i).toShadedBody).shade))
    (hB : (cfg.δ : ENNReal) ^ (-cfg.η) *
        volume (closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1)
      ≤ B * ((cfg.δ : ENNReal) ^ cfg.η *
          (((_root_.Tube.le_volume.c 3 : NNReal) : ENNReal) * (ρ : ENNReal) ^ 2))) :
    ShadedBody.multiplicity cfg.s (fun i ↦ (cfg.T i).toShadedBody) ≤ B := by
  refine cfg.multiplicity_le_of_le_volume_innerShadedUnion
    (v := (cfg.δ : ENNReal) ^ cfg.η *
      (((_root_.Tube.le_volume.c 3 : NNReal) : ENNReal) * (ρ : ENNReal) ^ 2)) ?_ hB
  exact le_trans (by gcongr; exact cfg.le_volume_iUnion_activeTubeNodes 𝒱 hk hgrid) hcmp

open MeasureTheory Metric Set ShadedBody in
/-- **The circularity, made numeric at the top grid index.**

At `k = 0` the grid scale is `1`, and the two-scale comparison becomes the absolute bound
`µ(𝕋, Y) ≤ δ^{-2η} |B_1| / c`. -/
theorem multiplicity_le_of_coarseVolumeComparison_zero (cfg : VeryNotSticky.{u})
    (𝒱 : ShadedTube.ShadedUniformTubeSet cfg.s cfg.T (Tube.ssfGridLen cfg.δ) cfg.C₀)
    (hcmp : (cfg.δ : ENNReal) ^ cfg.η *
        volume (⋃ j ∈ cfg.activeTubeNodes 𝒱.tubeUniform 0,
          (𝒱.tubeUniform.cover.tube 0 j).toConvexSpaceBody.carrier)
      ≤ volume (⋃ i ∈ cfg.s, ((cfg.T i).toShadedBody).shade)) :
    ShadedBody.multiplicity cfg.s (fun i ↦ (cfg.T i).toShadedBody)
      ≤ (cfg.δ : ENNReal) ^ (-(2 * cfg.η)) *
          volume (closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1) *
          (((_root_.Tube.le_volume.c 3 : NNReal) : ENNReal))⁻¹ := by
  have hgrid : Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) 0 = 1 := Tube.gridScale_zero _ _
  refine cfg.multiplicity_le_of_coarseVolumeComparison 𝒱 (Nat.zero_le _) hgrid hcmp ?_
  have hc0 : (((_root_.Tube.le_volume.c 3 : NNReal) : ENNReal)) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr (ne_of_gt (_root_.Tube.le_volume.c_pos 3))
  have hctop : (((_root_.Tube.le_volume.c 3 : NNReal) : ENNReal)) ≠ ⊤ := ENNReal.coe_ne_top
  have hδ0 : (cfg.δ : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr cfg.hδ.ne'
  have hδtop : (cfg.δ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  rw [show ((1 : NNReal) : ENNReal) ^ 2 = 1 by norm_num, mul_one]
  rw [show (cfg.δ : ENNReal) ^ (-(2 * cfg.η)) * volume (closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1)
      * (((_root_.Tube.le_volume.c 3 : NNReal) : ENNReal))⁻¹ *
      ((cfg.δ : ENNReal) ^ cfg.η * (((_root_.Tube.le_volume.c 3 : NNReal) : ENNReal)))
      = ((cfg.δ : ENNReal) ^ (-(2 * cfg.η)) * (cfg.δ : ENNReal) ^ cfg.η) *
        ((((_root_.Tube.le_volume.c 3 : NNReal) : ENNReal))⁻¹ *
          (((_root_.Tube.le_volume.c 3 : NNReal) : ENNReal))) *
        volume (closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1) by ring]
  rw [ENNReal.inv_mul_cancel hc0 hctop, ← ENNReal.rpow_add _ _ hδ0 hδtop]
  rw [show -(2 * cfg.η) + cfg.η = -cfg.η by ring]
  simp

/-! ## The sup form, run at the fine end of the grid

`Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid_of_shadingSet_supBall` reduces the residue
to a *local* inequality about each ball `B(x, ρ)` rather than to a global budget. This section
does three things with it.

**First, the circularity check**, because the two routes closed before this one were closed by
circularity. `Kakeya.VeryNotSticky.exists_shadingSet_supBall_free` shows the sup inequality
*alone* is satisfiable in **every** configuration, by the minimal shading set `Z = U(𝕋, Y)`. A
statement that holds unconditionally implies no bound that fails anywhere, so — unlike the field
`δ^η |⋃ 𝕋_ρ| ≤ |U(𝕋,Y)|` of
`Kakeya.VeryNotSticky.multiplicity_le_of_coarseVolumeComparison`, which forces `µ ≤ 3 δ^{-2η}` —
the sup form carries no multiplicity bound. **The sup route is not circular.** What the sup
inequality *does* cost, in conjunction with the fullness demand, is
`Kakeya.VeryNotSticky.supBall_necessary`: the necessary condition carries the extra factor
`|U(𝕋,Y) ∩ B(x,ρ)|` on its small side, and that factor is itself proportional to `|U(𝕋,Y)|`, so
the `|U(𝕋,Y)|` cancels and no absolute lower bound on `|U(𝕋,Y)|` — hence no upper bound on
`µ(𝕋, Y)` — follows. That is exactly the step the `max` form does not have.

**Second, the criterion.** `Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid_of_boostSet`
is the payoff, and it removes the ball estimate from the problem entirely:

> the residue holds as soon as there is a measurable **boost set** `V` with
> `2 δ^η |V| ≤ |B(0,ρ)|` such that `U(𝕋,Y) ∪ V` makes the node family `(Cd·C)⁻¹ lam`-full.

No supremum, no point, no density, no factor family, and — unlike every earlier reduction — no
hypothesis on `ρ` at all. The proof is the one place where the sup form beats the `max` form:
the two summands of `|Z| ≤ |U(𝕋,Y)| + |V|` are charged against *different* bounds on
`|U(𝕋,Y) ∩ B(x,ρ)|`, the first against `|B(0,ρ)|` and the second against `|U(𝕋,Y)|`. The `max`
form must pick one bound for the whole of `|Z|`, and that is what makes it lossy.

**Third, corollaries.** At `V = ⋃ 𝕋_ρ` the criterion recovers the ball branch of the earlier
route (`Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid_of_boostSet_saturated`), so nothing
is lost. And the budget `|V| ≤ δ^{-η} |B(0,ρ)| / 2` is generous — `δ^η ≤ 1/15625` by
`Kakeya.VeryNotSticky.rpow_eta_absorb_le_one` — so a *single* node tube fits inside it already
at `ρ ≳ δ^η`, which gives
`Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid_of_card_activeTubeNodes_boost`: the node
count may be as large as `≍ Cd/lam`, against the `≍ ρ δ^{-η}` that
`Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid_of_card_activeTubeNodes` demands — a gain
of a full factor `1/ρ` at the fine end.
-/

open MeasureTheory Metric Set ShadedBody in
/-- **The inner shaded union is measurable.** -/
theorem measurableSet_innerShadedUnion (cfg : VeryNotSticky.{u}) :
    MeasurableSet (⋃ i ∈ cfg.s, ((cfg.T i).toShadedBody).shade) :=
  Finset.measurableSet_biUnion _ (fun i _ => (cfg.T i).measurableSet_shade)

/-- **`2 δ^η ≤ 1`.** A restatement of `Kakeya.VeryNotSticky.rpow_eta_absorb_le_one` in the form
the boost-set estimate consumes; the true bound is `15625 δ^η ≤ 1`. -/
theorem two_rpow_eta_le_one (cfg : VeryNotSticky.{u}) :
    2 * (cfg.δ : ENNReal) ^ cfg.η ≤ 1 :=
  le_trans (by gcongr; norm_num) cfg.rpow_eta_absorb_le_one

open MeasureTheory Metric Set ShadedBody in
/-- **THE CIRCULARITY check OF THE SUP FORM: the sup inequality alone is free.**

For every configuration, every grid index and every scale there *is* an admissible shading set
satisfying the sup inequality of
`Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid_of_shadingSet_supBall`, namely the minimal
one `Z = U(𝕋, Y)`: it makes the coarse shaded union a subset of `U(𝕋, Y)` itself, and the
inequality degenerates to `δ^η · |U| · |U ∩ B(x,ρ)| ≤ |U| · |B(0,ρ)|`, true because
`|U ∩ B(x,ρ)| ≤ |B(x,ρ)| = |B(0,ρ)|` and `δ^η ≤ 1`.

**Consequence, and this is the point.** A statement provable in every configuration cannot imply
any bound that fails in some configuration. So the sup form, unlike the two-scale comparison
`δ^η |⋃ 𝕋_ρ| ≤ |U(𝕋,Y)|` of
`Kakeya.VeryNotSticky.multiplicity_le_of_coarseVolumeComparison` — which is *not* free, and
which forces `µ(𝕋,Y) ≤ 3 δ^{-2η}`, strictly stronger than GWZ 9.1's own conclusion — implies no
multiplicity bound whatsoever. **The sup route is not circular.**

The same lemma says the sup inequality is worth nothing *by itself*: all the content of the
residue sits in making it hold *simultaneously* with the fullness demand, which is what
`Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid_of_boostSet` below organises. -/
theorem exists_shadingSet_supBall_free (cfg : VeryNotSticky.{u})
    (𝒱 : ShadedTube.ShadedUniformTubeSet cfg.s cfg.T (Tube.ssfGridLen cfg.δ) cfg.C₀)
    (k : ℕ) (ρ : NNReal) :
    ∃ (Z : Set (EuclideanSpace ℝ (Fin 3))) (hZ : MeasurableSet Z),
      (⋃ i ∈ cfg.s, ((cfg.T i).toShadedBody).shade) ⊆ Z ∧
      ∀ x : EuclideanSpace ℝ (Fin 3),
        (cfg.δ : ENNReal) ^ cfg.η *
            volume (⋃ j ∈ cfg.activeTubeNodes 𝒱.tubeUniform k,
              (cfg.coarseShadeAt 𝒱 k Z hZ j).shade) *
            volume ((⋃ i ∈ cfg.s, ((cfg.T i).toShadedBody).shade) ∩ ball x (ρ : ℝ))
          ≤ volume (⋃ i ∈ cfg.s, ((cfg.T i).toShadedBody).shade) *
              volume (ball (0 : EuclideanSpace ℝ (Fin 3)) (ρ : ℝ)) := by
  classical
  refine ⟨⋃ i ∈ cfg.s, ((cfg.T i).toShadedBody).shade, cfg.measurableSet_innerShadedUnion,
    subset_rfl, fun x => ?_⟩
  have hsub : (⋃ j ∈ cfg.activeTubeNodes 𝒱.tubeUniform k,
      (cfg.coarseShadeAt 𝒱 k (⋃ i ∈ cfg.s, ((cfg.T i).toShadedBody).shade)
        cfg.measurableSet_innerShadedUnion j).shade)
      ⊆ (⋃ i ∈ cfg.s, ((cfg.T i).toShadedBody).shade) :=
    Set.iUnion₂_subset (fun _ _ => Set.inter_subset_right)
  have hcenter : volume (ball x (ρ : ℝ))
      = volume (ball (0 : EuclideanSpace ℝ (Fin 3)) (ρ : ℝ)) := by
    rw [EuclideanSpace.volume_ball, EuclideanSpace.volume_ball]
  have hδη : (cfg.δ : ENNReal) ^ cfg.η ≤ 1 :=
    ENNReal.rpow_le_one (by exact_mod_cast cfg.hδ1) cfg.hη.le
  calc (cfg.δ : ENNReal) ^ cfg.η *
        volume (⋃ j ∈ cfg.activeTubeNodes 𝒱.tubeUniform k,
          (cfg.coarseShadeAt 𝒱 k (⋃ i ∈ cfg.s, ((cfg.T i).toShadedBody).shade)
            cfg.measurableSet_innerShadedUnion j).shade) *
        volume ((⋃ i ∈ cfg.s, ((cfg.T i).toShadedBody).shade) ∩ ball x (ρ : ℝ))
      ≤ 1 * volume (⋃ i ∈ cfg.s, ((cfg.T i).toShadedBody).shade) * volume (ball x (ρ : ℝ)) := by
        exact mul_le_mul' (mul_le_mul' hδη (measure_mono hsub))
          (measure_mono Set.inter_subset_right)
    _ = volume (⋃ i ∈ cfg.s, ((cfg.T i).toShadedBody).shade) *
          volume (ball (0 : EuclideanSpace ℝ (Fin 3)) (ρ : ℝ)) := by rw [one_mul, hcenter]

open MeasureTheory Metric Set ShadedBody in
/-- **Fullness costs volume, measured on the coarse shaded union.**

`Kakeya.VeryNotSticky.le_volume_of_fullness_coarseShadeAt` with `|Z|` replaced by the smaller
`|⋃_j (T_{ρ,j} ∩ Z)|`, which is the quantity the sup inequality actually reads. Same proof: the
coarse multiplicity is at most `|𝕋_ρ|`, so `∑_j |T_{ρ,j} ∩ Z| ≤ |𝕋_ρ| · |⋃_j (T_{ρ,j} ∩ Z)|`,
while `∑_j |T_{ρ,j}| ≥ |𝕋_ρ| · c ρ²`; the node count cancels. -/
theorem le_volume_iUnion_coarseShadeAt_of_fullness (cfg : VeryNotSticky.{u})
    (𝒱 : ShadedTube.ShadedUniformTubeSet cfg.s cfg.T (Tube.ssfGridLen cfg.δ) cfg.C₀)
    {k : ℕ} (hk : k ≤ Tube.ssfGridLen cfg.δ)
    {ρ : NNReal} (hgrid : Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k = ρ)
    {Z : Set (EuclideanSpace ℝ (Fin 3))} (hZ : MeasurableSet Z) {f : NNReal}
    (hf : f ≤ ShadedBody.fullness (cfg.activeTubeNodes 𝒱.tubeUniform k)
      (cfg.coarseShadeAt 𝒱 k Z hZ)) :
    (f : ENNReal) * (((_root_.Tube.le_volume.c 3 : NNReal)) : ENNReal) * (ρ : ENNReal) ^ 2
      ≤ volume (⋃ j ∈ cfg.activeTubeNodes 𝒱.tubeUniform k,
          (cfg.coarseShadeAt 𝒱 k Z hZ j).shade) := by
  classical
  subst hgrid
  set A := cfg.activeTubeNodes 𝒱.tubeUniform k with hA
  set W := cfg.coarseShadeAt 𝒱 k Z hZ with hW
  set Zρ : Set (EuclideanSpace ℝ (Fin 3)) := ⋃ j ∈ A, (W j).shade with hZρ
  obtain ⟨j₀, hj₀⟩ := cfg.nonempty_activeTubeNodes 𝒱 hk
  have hcard0 : (A.card : ENNReal) ≠ 0 := by
    have : 0 < A.card := Finset.card_pos.mpr ⟨j₀, hj₀⟩
    exact_mod_cast this.ne'
  have hcardtop : (A.card : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hfr : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
  have hcar : ((A.card : ENNReal)) *
      ((((_root_.Tube.le_volume.c 3 : NNReal)) : ENNReal) *
        ((Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k : NNReal) : ENNReal) ^ 2)
      ≤ ∑ j ∈ A, volume (W j).carrier := by
    rw [← nsmul_eq_mul]
    refine Finset.card_nsmul_le_sum A _ _ (fun j _ => ?_)
    have h := _root_.Tube.le_volume (𝒱.tubeUniform.cover.tube k j)
    rw [hfr] at h
    exact h
  have hsh : ∑ j ∈ A, volume (W j).shade ≤ ((A.card : ENNReal)) * volume Zρ := by
    rw [← nsmul_eq_mul]
    refine Finset.sum_le_card_nsmul A _ _ (fun j hj => ?_)
    exact measure_mono (Set.subset_biUnion_of_mem (u := fun j => (W j).shade) hj)
  have hid : ∑ j ∈ A, volume (W j).shade
      = (ShadedBody.fullness A W : ENNReal) * ∑ j ∈ A, volume (W j).carrier :=
    ShadedBody.sum_volumeReal_shade_eq_fullness_mul A W
  have hchain : ((A.card : ENNReal)) *
      ((f : ENNReal) * ((((_root_.Tube.le_volume.c 3 : NNReal)) : ENNReal) *
        ((Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k : NNReal) : ENNReal) ^ 2))
      ≤ ((A.card : ENNReal)) * volume Zρ := by
    calc ((A.card : ENNReal)) *
          ((f : ENNReal) * ((((_root_.Tube.le_volume.c 3 : NNReal)) : ENNReal) *
            ((Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k : NNReal) : ENNReal) ^ 2))
        = (f : ENNReal) * (((A.card : ENNReal)) *
            ((((_root_.Tube.le_volume.c 3 : NNReal)) : ENNReal) *
              ((Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k : NNReal) : ENNReal) ^ 2)) := by
          ring
      _ ≤ (ShadedBody.fullness A W : ENNReal) * ∑ j ∈ A, volume (W j).carrier := by
          refine mul_le_mul' (by exact_mod_cast hf) hcar
      _ = ∑ j ∈ A, volume (W j).shade := hid.symm
      _ ≤ ((A.card : ENNReal)) * volume Zρ := hsh
  have hfin := (ENNReal.mul_le_mul_iff_right hcard0 hcardtop).mp hchain
  calc (f : ENNReal) * (((_root_.Tube.le_volume.c 3 : NNReal)) : ENNReal) *
        ((Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k : NNReal) : ENNReal) ^ 2
      = (f : ENNReal) * ((((_root_.Tube.le_volume.c 3 : NNReal)) : ENNReal) *
          ((Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k : NNReal) : ENNReal) ^ 2) := by ring
    _ ≤ volume Zρ := hfin

open MeasureTheory Metric Set ShadedBody in
/-- **What the sup route costs — the joint necessary condition.**

The counterpart of `Kakeya.VeryNotSticky.shadingSet_budget_necessary` for the sup form. Any `Z`
that is `f`-full for the node family and satisfies the sup inequality forces, at every point
`x`,

  `δ^η · f · c · ρ² · |U(𝕋,Y) ∩ B(x,ρ)| ≤ |U(𝕋,Y)| · |B(0,ρ)|`,   `c = Tube.le_volume.c 3`.

**Read the difference from the `max` form.** `shadingSet_budget_necessary` produces
`δ^{3η} c ρ² ≤ C² · max(|U|, |B(0,ρ)|)`, an *absolute* lower bound on `max(|U|, |B(0,ρ)|)`, and
that is what fed the circularity of the earlier experiment. Here the small side carries the
extra factor `|U ∩ B(x,ρ)|`, and *that factor is itself proportional to `|U|`*: `U` lies in the
unit ball, so covering the unit ball by `ρ`-balls produces an `x` with `|U ∩ B(x,ρ)| ≳ ρ³ |U|`,
and the condition then reads `δ^η f c ρ² · ρ³ |U| ≲ |U| ρ³`, i.e. `δ^η f c ρ² ≲ 1` — vacuous.
No lower bound on `|U|` survives, hence no upper bound on `µ(𝕋,Y)`, hence no circularity. -/
theorem supBall_necessary (cfg : VeryNotSticky.{u})
    (𝒱 : ShadedTube.ShadedUniformTubeSet cfg.s cfg.T (Tube.ssfGridLen cfg.δ) cfg.C₀)
    {k : ℕ} (hk : k ≤ Tube.ssfGridLen cfg.δ)
    {ρ : NNReal} (hgrid : Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k = ρ)
    {Z : Set (EuclideanSpace ℝ (Fin 3))} (hZ : MeasurableSet Z) {f : NNReal}
    (hf : f ≤ ShadedBody.fullness (cfg.activeTubeNodes 𝒱.tubeUniform k)
      (cfg.coarseShadeAt 𝒱 k Z hZ))
    (hsup : ∀ x : EuclideanSpace ℝ (Fin 3),
      (cfg.δ : ENNReal) ^ cfg.η *
          volume (⋃ j ∈ cfg.activeTubeNodes 𝒱.tubeUniform k,
            (cfg.coarseShadeAt 𝒱 k Z hZ j).shade) *
          volume ((⋃ i ∈ cfg.s, ((cfg.T i).toShadedBody).shade) ∩ ball x (ρ : ℝ))
        ≤ volume (⋃ i ∈ cfg.s, ((cfg.T i).toShadedBody).shade) *
            volume (ball (0 : EuclideanSpace ℝ (Fin 3)) (ρ : ℝ)))
    (x : EuclideanSpace ℝ (Fin 3)) :
    (cfg.δ : ENNReal) ^ cfg.η * ((f : ENNReal) *
          (((_root_.Tube.le_volume.c 3 : NNReal)) : ENNReal) * (ρ : ENNReal) ^ 2) *
        volume ((⋃ i ∈ cfg.s, ((cfg.T i).toShadedBody).shade) ∩ ball x (ρ : ℝ))
      ≤ volume (⋃ i ∈ cfg.s, ((cfg.T i).toShadedBody).shade) *
          volume (ball (0 : EuclideanSpace ℝ (Fin 3)) (ρ : ℝ)) := by
  refine le_trans ?_ (hsup x)
  gcongr
  exact cfg.le_volume_iUnion_coarseShadeAt_of_fullness 𝒱 hk hgrid hZ hf

open MeasureTheory Metric Set ShadedBody in
/-- **THE CRITERION: the residue from a boost set.**

Let `V` be any measurable set with

* `2 δ^η |V| ≤ |B(0, ρ)|`  (the **budget**), and
* `(Cd · C)⁻¹ lam · ∑_j |T_{ρ,j}| ≤ ∑_j |T_{ρ,j} ∩ (U(𝕋,Y) ∪ V)|`  (the **fullness demand**).

Then the residue holds at that grid scale. No supremum, no point, no density, no factor family,
and no hypothesis relating `ρ` to `δ`.

**Why this is the sup form and not the `max` form.** With `Z = U(𝕋,Y) ∪ V` the coarse shaded
union has `|Z_ρ| ≤ |U| + |V|`, and the sup inequality splits as

  `δ^η |U| · |U ∩ B(x,ρ)| + δ^η |V| · |U ∩ B(x,ρ)|
     ≤ δ^η |U| · |B(0,ρ)| + δ^η |V| · |U|
     ≤ ½ |U| |B(0,ρ)| + ½ |B(0,ρ)| |U| = |U| |B(0,ρ)|`,

using `|U ∩ B(x,ρ)| ≤ |B(x,ρ)| = |B(0,ρ)|` on the **first** summand and `|U ∩ B(x,ρ)| ≤ |U|` on
the **second**. Two different bounds on the same quantity, one per summand: that is precisely
the freedom `Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid_of_shadingSet_volume_max`
throws away, since it must charge the whole of `|Z|` against a single branch of the maximum.
The two factors of `½` come from `2 δ^η ≤ 1`
(`Kakeya.VeryNotSticky.two_rpow_eta_le_one`, itself a weakening of `δ^η ≤ 1/15625`) and from the
budget.

**What is left.** Exactly the fullness demand, now with a volume budget attached: cover a
`(Cd·C)⁻¹ lam` fraction of the node family's carrier mass by `U(𝕋, Y)` together with a set of
volume at most `δ^{-η} |B(0,ρ)| / 2`. The budget is generous — at least `7812` ball volumes. -/
theorem exists_coarseShadedFamilyAtGrid_of_boostSet (cfg : VeryNotSticky.{u})
    (𝒱 : ShadedTube.ShadedUniformTubeSet cfg.s cfg.T (Tube.ssfGridLen cfg.δ) cfg.C₀)
    {k : ℕ} (hk : k ≤ Tube.ssfGridLen cfg.δ)
    {ρ : NNReal} (hgrid : Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k = ρ)
    (V : Set (EuclideanSpace ℝ (Fin 3))) (hV : MeasurableSet V)
    (hbudget : 2 * (cfg.δ : ENNReal) ^ cfg.η * volume V
      ≤ volume (ball (0 : EuclideanSpace ℝ (Fin 3)) (ρ : ℝ)))
    (hfull : (((cfg.Cd * shadingMultiplicityEstimateForRhoTubes.C)⁻¹ * cfg.lam : NNReal) :
          ENNReal) *
        (∑ j ∈ cfg.activeTubeNodes 𝒱.tubeUniform k,
          volume ((𝒱.tubeUniform.cover.tube k j).toConvexSpaceBody.carrier))
      ≤ ∑ j ∈ cfg.activeTubeNodes 𝒱.tubeUniform k,
          volume ((𝒱.tubeUniform.cover.tube k j).toConvexSpaceBody.carrier ∩
            ((⋃ i ∈ cfg.s, ((cfg.T i).toShadedBody).shade) ∪ V))) :
    ∃ G : ShadedFactorFamily (EuclideanSpace ℝ (Fin 3)) cfg.ι cfg.ι,
      G.innerSet = cfg.s ∧
      (∀ i ∈ cfg.s, G.innerBody i = (cfg.T i).toShadedBody) ∧
      G.outerSet = cfg.activeTubeNodes 𝒱.tubeUniform k ∧
      (∀ j ∈ G.outerSet,
        (G.outerBody j).toConvexSpaceBody =
          (𝒱.tubeUniform.cover.tube k j).toConvexSpaceBody) ∧
      (cfg.Cd * shadingMultiplicityEstimateForRhoTubes.C)⁻¹ * cfg.lam ≤
        ShadedBody.fullness G.outerSet G.outerBody ∧
      (∀ x ∈ ⋃ j ∈ G.outerSet, (G.outerBody j).shade,
        (cfg.δ : ENNReal) ^ cfg.η *
            (((shadingMultiplicityEstimateForRhoTubes.C : NNReal) : ENNReal)⁻¹ *
                volume (⋃ j ∈ G.outerSet, (G.outerBody j).shade) *
              (volume ((⋃ i ∈ G.innerSet, (G.innerBody i).shade) ∩ ball x (ρ : ℝ)) /
                volume (ball x (ρ : ℝ)))) ≤
          volume (⋃ i ∈ G.innerSet, (G.innerBody i).shade)) := by
  classical
  set U : Set (EuclideanSpace ℝ (Fin 3)) := ⋃ i ∈ cfg.s, ((cfg.T i).toShadedBody).shade with hU
  have hUmeas : MeasurableSet U := cfg.measurableSet_innerShadedUnion
  have hZ : MeasurableSet (U ∪ V) := hUmeas.union hV
  have hZin : U ⊆ U ∪ V := Set.subset_union_left
  set A := cfg.activeTubeNodes 𝒱.tubeUniform k with hA
  set W := cfg.coarseShadeAt 𝒱 k (U ∪ V) hZ with hW
  -- the outer fullness
  obtain ⟨j₀, hj₀⟩ := cfg.nonempty_activeTubeNodes 𝒱 hk
  have hcar : ∀ j, (W j).carrier
      = (𝒱.tubeUniform.cover.tube k j).toConvexSpaceBody.carrier := fun _ => rfl
  have hshd : ∀ j, (W j).shade
      = (𝒱.tubeUniform.cover.tube k j).toConvexSpaceBody.carrier ∩ (U ∪ V) := fun _ => rfl
  have hpos : 0 < volume ((𝒱.tubeUniform.cover.tube k j₀).toConvexSpaceBody.carrier) := by
    have hfr : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
    have h := _root_.Tube.le_volume (𝒱.tubeUniform.cover.tube k j₀)
    rw [hfr] at h
    refine lt_of_lt_of_le ?_ h
    have hc : (0 : ENNReal) < ((_root_.Tube.le_volume.c 3 : NNReal) : ENNReal) :=
      ENNReal.coe_pos.mpr (_root_.Tube.le_volume.c_pos _)
    have hg : (0 : ENNReal) <
        ((Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k : NNReal) : ENNReal) ^ 2 := by
      refine ENNReal.pow_pos (ENNReal.coe_pos.mpr ?_) _
      exact Tube.gridScale_pos cfg.hδ _ _
    exact ENNReal.mul_pos (ne_of_gt hc) (ne_of_gt hg)
  have hsum0 : (∑ j ∈ A, volume ((W j).carrier)) ≠ 0 := by
    intro h
    rw [Finset.sum_eq_zero_iff] at h
    exact absurd (h _ hj₀) (ne_of_gt (by rw [hcar j₀]; exact hpos))
  have hsumtop : (∑ j ∈ A, volume ((W j).carrier)) ≠ ⊤ := by
    refine (lt_top_iff_ne_top.mp ?_)
    refine ENNReal.sum_lt_top.mpr (fun j _ => ?_)
    rw [hcar j]
    exact (𝒱.tubeUniform.cover.tube k j).toConvexSpaceBody.isCompact'.measure_lt_top
  have hfullZ : (cfg.Cd * shadingMultiplicityEstimateForRhoTubes.C)⁻¹ * cfg.lam ≤
      ShadedBody.fullness A W := by
    rw [← ENNReal.coe_le_coe, ShadedBody.fullness_def,
      ENNReal.le_div_iff_mul_le (Or.inl hsum0) (Or.inl hsumtop)]
    calc (((cfg.Cd * shadingMultiplicityEstimateForRhoTubes.C)⁻¹ * cfg.lam : NNReal) : ENNReal) *
          ∑ j ∈ A, volume ((W j).carrier)
        = (((cfg.Cd * shadingMultiplicityEstimateForRhoTubes.C)⁻¹ * cfg.lam : NNReal) : ENNReal) *
            ∑ j ∈ A, volume ((𝒱.tubeUniform.cover.tube k j).toConvexSpaceBody.carrier) := by
          simp only [hcar]
      _ ≤ ∑ j ∈ A, volume ((𝒱.tubeUniform.cover.tube k j).toConvexSpaceBody.carrier ∩ (U ∪ V)) :=
          hfull
      _ = ∑ j ∈ A, volume ((W j).shade) := by simp only [hshd]
  -- the sup inequality
  refine cfg.exists_coarseShadedFamilyAtGrid_of_shadingSet_supBall 𝒱 hk hgrid (U ∪ V) hZ hZin
    hfullZ ?_
  intro x
  have hZρ : volume (⋃ j ∈ A, (W j).shade) ≤ volume U + volume V := by
    refine le_trans (measure_mono (Set.iUnion₂_subset (fun _ _ => Set.inter_subset_right))) ?_
    exact measure_union_le _ _
  have hcenter : volume (ball x (ρ : ℝ))
      = volume (ball (0 : EuclideanSpace ℝ (Fin 3)) (ρ : ℝ)) := by
    rw [EuclideanSpace.volume_ball, EuclideanSpace.volume_ball]
  have hbx : volume (U ∩ ball x (ρ : ℝ))
      ≤ volume (ball (0 : EuclideanSpace ℝ (Fin 3)) (ρ : ℝ)) := by
    rw [← hcenter]
    exact measure_mono Set.inter_subset_right
  have hux : volume (U ∩ ball x (ρ : ℝ)) ≤ volume U := measure_mono Set.inter_subset_left
  have h2ne : (2 : ENNReal) ≠ 0 := by norm_num
  have h2top : (2 : ENNReal) ≠ ⊤ := by norm_num
  rw [← ENNReal.mul_le_mul_iff_left h2ne h2top]
  calc (cfg.δ : ENNReal) ^ cfg.η * volume (⋃ j ∈ A, (W j).shade) *
          volume (U ∩ ball x (ρ : ℝ)) * 2
      ≤ (cfg.δ : ENNReal) ^ cfg.η * (volume U + volume V) *
          volume (U ∩ ball x (ρ : ℝ)) * 2 := by gcongr
    _ = (2 * (cfg.δ : ENNReal) ^ cfg.η * volume U) * volume (U ∩ ball x (ρ : ℝ))
          + (2 * (cfg.δ : ENNReal) ^ cfg.η * volume V) * volume (U ∩ ball x (ρ : ℝ)) := by
        ring
    _ ≤ (1 * volume U) * volume (ball (0 : EuclideanSpace ℝ (Fin 3)) (ρ : ℝ))
          + volume (ball (0 : EuclideanSpace ℝ (Fin 3)) (ρ : ℝ)) * volume U := by
        refine add_le_add (mul_le_mul' ?_ hbx) (mul_le_mul' hbudget hux)
        exact mul_le_mul' cfg.two_rpow_eta_le_one le_rfl
    _ = volume U * volume (ball (0 : EuclideanSpace ℝ (Fin 3)) (ρ : ℝ)) * 2 := by ring

open MeasureTheory Metric Set ShadedBody in
/-- **The boost-set criterion at the saturated choice `V = ⋃ 𝕋_ρ`.**

Nothing is lost by passing to the boost-set form: at the extreme choice it recovers the ball
branch of `Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid_of_coarseVolume`, at the cost of
a factor `2` in the threshold. Together with
`Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid_of_boostSet` at `V = ∅` — which is the
residue from the *minimal* shading `Z = U(𝕋,Y)` — the criterion interpolates between the two
extreme shadings that were previously the only two available, and every intermediate `V` is new
ground. -/
theorem exists_coarseShadedFamilyAtGrid_of_boostSet_saturated (cfg : VeryNotSticky.{u})
    (𝒱 : ShadedTube.ShadedUniformTubeSet cfg.s cfg.T (Tube.ssfGridLen cfg.δ) cfg.C₀)
    {k : ℕ} (hk : k ≤ Tube.ssfGridLen cfg.δ)
    {ρ : NNReal} (hgrid : Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k = ρ)
    (hbudget : 2 * (cfg.δ : ENNReal) ^ cfg.η *
        volume (⋃ j ∈ cfg.activeTubeNodes 𝒱.tubeUniform k,
          (𝒱.tubeUniform.cover.tube k j).toConvexSpaceBody.carrier)
      ≤ volume (ball (0 : EuclideanSpace ℝ (Fin 3)) (ρ : ℝ))) :
    ∃ G : ShadedFactorFamily (EuclideanSpace ℝ (Fin 3)) cfg.ι cfg.ι,
      G.innerSet = cfg.s ∧
      (∀ i ∈ cfg.s, G.innerBody i = (cfg.T i).toShadedBody) ∧
      G.outerSet = cfg.activeTubeNodes 𝒱.tubeUniform k ∧
      (∀ j ∈ G.outerSet,
        (G.outerBody j).toConvexSpaceBody =
          (𝒱.tubeUniform.cover.tube k j).toConvexSpaceBody) ∧
      (cfg.Cd * shadingMultiplicityEstimateForRhoTubes.C)⁻¹ * cfg.lam ≤
        ShadedBody.fullness G.outerSet G.outerBody ∧
      (∀ x ∈ ⋃ j ∈ G.outerSet, (G.outerBody j).shade,
        (cfg.δ : ENNReal) ^ cfg.η *
            (((shadingMultiplicityEstimateForRhoTubes.C : NNReal) : ENNReal)⁻¹ *
                volume (⋃ j ∈ G.outerSet, (G.outerBody j).shade) *
              (volume ((⋃ i ∈ G.innerSet, (G.innerBody i).shade) ∩ ball x (ρ : ℝ)) /
                volume (ball x (ρ : ℝ)))) ≤
          volume (⋃ i ∈ G.innerSet, (G.innerBody i).shade)) := by
  classical
  have hmeas : MeasurableSet (⋃ j ∈ cfg.activeTubeNodes 𝒱.tubeUniform k,
      (𝒱.tubeUniform.cover.tube k j).toConvexSpaceBody.carrier) :=
    Finset.measurableSet_biUnion _
      (fun j _ => (𝒱.tubeUniform.cover.tube k j).toConvexSpaceBody.isCompact'.isClosed.measurableSet)
  refine cfg.exists_coarseShadedFamilyAtGrid_of_boostSet 𝒱 hk hgrid _ hmeas hbudget ?_
  have hCd0 : (cfg.Cd : NNReal) ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one cfg.hCd)
  have hle : ((cfg.Cd * shadingMultiplicityEstimateForRhoTubes.C)⁻¹ * cfg.lam : NNReal) ≤ 1 := by
    rw [ShadedBody.shadingMultiplicityEstimateForRhoTubes.C, mul_one]
    calc (cfg.Cd)⁻¹ * cfg.lam ≤ (cfg.Cd)⁻¹ * cfg.Cd := by gcongr; exact cfg.lam_le_Cd
      _ = 1 := inv_mul_cancel₀ hCd0
  have heq : ∀ j ∈ cfg.activeTubeNodes 𝒱.tubeUniform k,
      volume ((𝒱.tubeUniform.cover.tube k j).toConvexSpaceBody.carrier ∩
          ((⋃ i ∈ cfg.s, ((cfg.T i).toShadedBody).shade) ∪
            ⋃ j' ∈ cfg.activeTubeNodes 𝒱.tubeUniform k,
              (𝒱.tubeUniform.cover.tube k j').toConvexSpaceBody.carrier))
        = volume ((𝒱.tubeUniform.cover.tube k j).toConvexSpaceBody.carrier) := by
    intro j hj
    congr 1
    refine Set.inter_eq_self_of_subset_left (fun y hy => Or.inr ?_)
    exact Set.mem_biUnion hj hy
  rw [Finset.sum_congr rfl heq]
  calc (((cfg.Cd * shadingMultiplicityEstimateForRhoTubes.C)⁻¹ * cfg.lam : NNReal) : ENNReal) *
        ∑ j ∈ cfg.activeTubeNodes 𝒱.tubeUniform k,
          volume ((𝒱.tubeUniform.cover.tube k j).toConvexSpaceBody.carrier)
      ≤ 1 * ∑ j ∈ cfg.activeTubeNodes 𝒱.tubeUniform k,
          volume ((𝒱.tubeUniform.cover.tube k j).toConvexSpaceBody.carrier) := by
        gcongr
        exact_mod_cast hle
    _ = ∑ j ∈ cfg.activeTubeNodes 𝒱.tubeUniform k,
          volume ((𝒱.tubeUniform.cover.tube k j).toConvexSpaceBody.carrier) := one_mul _

open MeasureTheory Metric Set ShadedBody in
/-- **The boost-set criterion with the boost taken to be a sub-collection of node tubes.**

The most usable instance of `Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid_of_boostSet`:
saturate the nodes of a chosen subfamily `A ⊆ 𝕋_ρ` and leave the rest shaded only by
`U(𝕋, Y)`. The two hypotheses are then arithmetic in the carrier volumes alone —

* `2 δ^η ∑_{j ∈ A} |T_{ρ,j}| ≤ |B(0,ρ)|`, and
* `(Cd·C)⁻¹ lam ∑_{j ∈ 𝕋_ρ} |T_{ρ,j}| ≤ ∑_{j ∈ A} |T_{ρ,j}|`

— and they pull in opposite directions in exactly one parameter, the total carrier mass of `A`.
The saturated choice `A = 𝕋_ρ` is
`Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid_of_boostSet_saturated`; the interest is in
choosing `A` *just large enough* for the second, since the first then costs a factor
`(Cd·C)⁻¹ lam` less than it does at the saturated choice. -/
theorem exists_coarseShadedFamilyAtGrid_of_nodeSubset (cfg : VeryNotSticky.{u})
    (𝒱 : ShadedTube.ShadedUniformTubeSet cfg.s cfg.T (Tube.ssfGridLen cfg.δ) cfg.C₀)
    {k : ℕ} (hk : k ≤ Tube.ssfGridLen cfg.δ)
    {ρ : NNReal} (hgrid : Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k = ρ)
    (A : Finset cfg.ι) (hA : A ⊆ cfg.activeTubeNodes 𝒱.tubeUniform k)
    (hbudget : 2 * (cfg.δ : ENNReal) ^ cfg.η *
        (∑ j ∈ A, volume ((𝒱.tubeUniform.cover.tube k j).toConvexSpaceBody.carrier))
      ≤ volume (ball (0 : EuclideanSpace ℝ (Fin 3)) (ρ : ℝ)))
    (hfull : (((cfg.Cd * shadingMultiplicityEstimateForRhoTubes.C)⁻¹ * cfg.lam : NNReal) :
          ENNReal) *
        (∑ j ∈ cfg.activeTubeNodes 𝒱.tubeUniform k,
          volume ((𝒱.tubeUniform.cover.tube k j).toConvexSpaceBody.carrier))
      ≤ ∑ j ∈ A, volume ((𝒱.tubeUniform.cover.tube k j).toConvexSpaceBody.carrier)) :
    ∃ G : ShadedFactorFamily (EuclideanSpace ℝ (Fin 3)) cfg.ι cfg.ι,
      G.innerSet = cfg.s ∧
      (∀ i ∈ cfg.s, G.innerBody i = (cfg.T i).toShadedBody) ∧
      G.outerSet = cfg.activeTubeNodes 𝒱.tubeUniform k ∧
      (∀ j ∈ G.outerSet,
        (G.outerBody j).toConvexSpaceBody =
          (𝒱.tubeUniform.cover.tube k j).toConvexSpaceBody) ∧
      (cfg.Cd * shadingMultiplicityEstimateForRhoTubes.C)⁻¹ * cfg.lam ≤
        ShadedBody.fullness G.outerSet G.outerBody ∧
      (∀ x ∈ ⋃ j ∈ G.outerSet, (G.outerBody j).shade,
        (cfg.δ : ENNReal) ^ cfg.η *
            (((shadingMultiplicityEstimateForRhoTubes.C : NNReal) : ENNReal)⁻¹ *
                volume (⋃ j ∈ G.outerSet, (G.outerBody j).shade) *
              (volume ((⋃ i ∈ G.innerSet, (G.innerBody i).shade) ∩ ball x (ρ : ℝ)) /
                volume (ball x (ρ : ℝ)))) ≤
          volume (⋃ i ∈ G.innerSet, (G.innerBody i).shade)) := by
  classical
  set V : Set (EuclideanSpace ℝ (Fin 3)) :=
    ⋃ j ∈ A, (𝒱.tubeUniform.cover.tube k j).toConvexSpaceBody.carrier with hVdef
  have hVmeas : MeasurableSet V :=
    Finset.measurableSet_biUnion _ (fun j _ =>
      (𝒱.tubeUniform.cover.tube k j).toConvexSpaceBody.isCompact'.isClosed.measurableSet)
  have hVvol : volume V
      ≤ ∑ j ∈ A, volume ((𝒱.tubeUniform.cover.tube k j).toConvexSpaceBody.carrier) :=
    measure_biUnion_finset_le _ _
  refine cfg.exists_coarseShadedFamilyAtGrid_of_boostSet 𝒱 hk hgrid V hVmeas ?_ ?_
  · exact le_trans (by gcongr) hbudget
  · refine le_trans hfull ?_
    calc ∑ j ∈ A, volume ((𝒱.tubeUniform.cover.tube k j).toConvexSpaceBody.carrier)
        = ∑ j ∈ A, volume ((𝒱.tubeUniform.cover.tube k j).toConvexSpaceBody.carrier ∩
            ((⋃ i ∈ cfg.s, ((cfg.T i).toShadedBody).shade) ∪ V)) := by
          refine Finset.sum_congr rfl (fun j hj => ?_)
          congr 1
          refine (Set.inter_eq_self_of_subset_left (fun y hy => Or.inr ?_)).symm
          exact Set.mem_biUnion hj hy
      _ ≤ ∑ j ∈ cfg.activeTubeNodes 𝒱.tubeUniform k,
            volume ((𝒱.tubeUniform.cover.tube k j).toConvexSpaceBody.carrier ∩
              ((⋃ i ∈ cfg.s, ((cfg.T i).toShadedBody).shade) ∪ V)) :=
          Finset.sum_le_sum_of_subset hA

open MeasureTheory Metric Set ShadedBody in
/-- **A node count criterion at the fine end: one node tube is a legal boost set.**

Take `A = {j₀}` in `Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid_of_nodeSubset`. The
budget then only has to pay for a *single* node tube, `2 δ^η C_u ρ² ≤ |B(0,ρ)|`, i.e.
`ρ ≳ δ^η` — and `δ^η ≤ 1/15625`, so this is satisfied on all but the very finest scales. What is
left is a bound on the node count,

  `(Cd·C)⁻¹ lam · |𝕋_ρ| · C_u ρ² ≤ c ρ²`,   i.e.   `|𝕋_ρ| ≲ (Cd·C) / (lam · C_u/c)`,

which at the smallest admissible density `lam = Cd δ^{2η}` (`Kakeya.VeryNotSticky.lam_ge`)
reads `|𝕋_ρ| ≲ δ^{-2η}`.

**Compare `Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid_of_card_activeTubeNodes`**, the
previous node-count criterion: it demands `δ^η |𝕋_ρ| C_u ρ² ≤ |B(0,ρ)|`, i.e.
`|𝕋_ρ| ≲ ρ δ^{-η}`. This one is stronger by the full factor `1/ρ` whenever
`lam ≍ Cd δ^η`, which is the regime the section is about — the price being the mild extra
threshold `ρ ≳ δ^η` on the scale, against which the earlier criterion's own threshold is far
larger. -/
theorem exists_coarseShadedFamilyAtGrid_of_card_activeTubeNodes_boost (cfg : VeryNotSticky.{u})
    (𝒱 : ShadedTube.ShadedUniformTubeSet cfg.s cfg.T (Tube.ssfGridLen cfg.δ) cfg.C₀)
    {k : ℕ} (hk : k ≤ Tube.ssfGridLen cfg.δ)
    {ρ : NNReal} (hgrid : Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k = ρ) (hρ1 : ρ ≤ 1)
    (hbudget : 2 * (cfg.δ : ENNReal) ^ cfg.η *
        (((_root_.Tube.volume_le.C 3 : NNReal) : ENNReal) * (ρ : ENNReal) ^ 2)
      ≤ volume (ball (0 : EuclideanSpace ℝ (Fin 3)) (ρ : ℝ)))
    (hcard : (((cfg.Cd * shadingMultiplicityEstimateForRhoTubes.C)⁻¹ * cfg.lam : NNReal) :
          ENNReal) *
        (((cfg.activeTubeNodes 𝒱.tubeUniform k).card : ENNReal) *
          (((_root_.Tube.volume_le.C 3 : NNReal) : ENNReal) * (ρ : ENNReal) ^ 2))
      ≤ (((_root_.Tube.le_volume.c 3 : NNReal)) : ENNReal) * (ρ : ENNReal) ^ 2) :
    ∃ G : ShadedFactorFamily (EuclideanSpace ℝ (Fin 3)) cfg.ι cfg.ι,
      G.innerSet = cfg.s ∧
      (∀ i ∈ cfg.s, G.innerBody i = (cfg.T i).toShadedBody) ∧
      G.outerSet = cfg.activeTubeNodes 𝒱.tubeUniform k ∧
      (∀ j ∈ G.outerSet,
        (G.outerBody j).toConvexSpaceBody =
          (𝒱.tubeUniform.cover.tube k j).toConvexSpaceBody) ∧
      (cfg.Cd * shadingMultiplicityEstimateForRhoTubes.C)⁻¹ * cfg.lam ≤
        ShadedBody.fullness G.outerSet G.outerBody ∧
      (∀ x ∈ ⋃ j ∈ G.outerSet, (G.outerBody j).shade,
        (cfg.δ : ENNReal) ^ cfg.η *
            (((shadingMultiplicityEstimateForRhoTubes.C : NNReal) : ENNReal)⁻¹ *
                volume (⋃ j ∈ G.outerSet, (G.outerBody j).shade) *
              (volume ((⋃ i ∈ G.innerSet, (G.innerBody i).shade) ∩ ball x (ρ : ℝ)) /
                volume (ball x (ρ : ℝ)))) ≤
          volume (⋃ i ∈ G.innerSet, (G.innerBody i).shade)) := by
  classical
  obtain ⟨j₀, hj₀⟩ := cfg.nonempty_activeTubeNodes 𝒱 hk
  have hfr : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
  have hg1 : Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k ≤ 1 := by rw [hgrid]; exact hρ1
  have hper : ∀ j : cfg.ι,
      volume ((𝒱.tubeUniform.cover.tube k j).toConvexSpaceBody.carrier) ≤
        ((_root_.Tube.volume_le.C 3 : NNReal) : ENNReal) * (ρ : ENNReal) ^ 2 := by
    intro j
    have h := _root_.Tube.volume_le hg1 (𝒱.tubeUniform.cover.tube k j)
    rw [hfr] at h
    refine h.trans (le_of_eq ?_)
    rw [hgrid]
  have hlow : (((_root_.Tube.le_volume.c 3 : NNReal)) : ENNReal) * (ρ : ENNReal) ^ 2
      ≤ volume ((𝒱.tubeUniform.cover.tube k j₀).toConvexSpaceBody.carrier) := by
    have h := _root_.Tube.le_volume (𝒱.tubeUniform.cover.tube k j₀)
    rw [hfr] at h
    refine le_trans (le_of_eq ?_) h
    rw [hgrid]
  refine cfg.exists_coarseShadedFamilyAtGrid_of_nodeSubset 𝒱 hk hgrid {j₀}
    (Finset.singleton_subset_iff.mpr hj₀) ?_ ?_
  · rw [Finset.sum_singleton]
    exact le_trans (by gcongr; exact hper j₀) hbudget
  · rw [Finset.sum_singleton]
    refine le_trans ?_ (le_trans hcard hlow)
    gcongr
    rw [← nsmul_eq_mul]
    exact Finset.sum_le_card_nsmul _ _ _ (fun j _ => hper j)

/-- **Greedy selection, as a general fact about finite sums.**

If a target is at most the total and every summand is at most `b`, then some subset overshoots
the target by at most `b`: take one of minimal cardinality among the subsets that reach the
target, and remove any one of its elements. This is what turns the two competing hypotheses of
`Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid_of_nodeSubset` into a single one. -/
theorem exists_subset_sum_between {κ : Type*} (t : Finset κ) (g : κ → ENNReal)
    {target b : ENNReal} (htarget : target ≤ ∑ j ∈ t, g j) (hb : ∀ j ∈ t, g j ≤ b) :
    ∃ A ⊆ t, target ≤ ∑ j ∈ A, g j ∧ ∑ j ∈ A, g j ≤ target + b := by
  classical
  set S : Finset (Finset κ) := t.powerset.filter (fun A => target ≤ ∑ j ∈ A, g j) with hS
  have hSne : S.Nonempty := by
    refine ⟨t, ?_⟩
    rw [hS, Finset.mem_filter, Finset.mem_powerset]
    exact ⟨Finset.Subset.refl t, htarget⟩
  obtain ⟨A, hAS, hAmin⟩ := Finset.exists_min_image S Finset.card hSne
  have hAS' : A ⊆ t ∧ target ≤ ∑ j ∈ A, g j := by
    rw [hS, Finset.mem_filter, Finset.mem_powerset] at hAS
    exact hAS
  refine ⟨A, hAS'.1, hAS'.2, ?_⟩
  rcases A.eq_empty_or_nonempty with rfl | ⟨j, hj⟩
  · simp
  · have hsub : A.erase j ⊆ t := (Finset.erase_subset j A).trans hAS'.1
    have hlt : ¬ (target ≤ ∑ i ∈ A.erase j, g i) := by
      intro hcon
      have hmem : A.erase j ∈ S := by
        rw [hS, Finset.mem_filter, Finset.mem_powerset]
        exact ⟨hsub, hcon⟩
      have := hAmin _ hmem
      exact absurd this (by simpa using Finset.card_erase_lt_of_mem hj)
    have hle : ∑ i ∈ A.erase j, g i ≤ target := le_of_not_ge hlt
    calc ∑ i ∈ A, g i = ∑ i ∈ A.erase j, g i + g j := (Finset.sum_erase_add A g hj).symm
      _ ≤ target + b := add_le_add hle (hb j (hAS'.1 hj))

open MeasureTheory Metric Set ShadedBody in
/-- **The best node-count criterion available on this route.**

Feed `Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid_of_nodeSubset` the greedily chosen
subfamily of `Kakeya.VeryNotSticky.exists_subset_sum_between`: it reaches the fullness target
`(Cd·C)⁻¹ lam · ∑_j |T_{ρ,j}|` while overshooting by at most one node tube. The two hypotheses
collapse to the single budget

  `2 δ^η · ( (Cd·C)⁻¹ lam · |𝕋_ρ| · C_u ρ² + C_u ρ² ) ≤ |B(0,ρ)|`,

i.e., writing `f = (Cd·C)⁻¹ lam ∈ [δ^{2η}, 1]` and dropping constants,
`f · |𝕋_ρ| + 1 ≲ ρ δ^{-η}`, i.e.

  **`|𝕋_ρ| ≲ ρ δ^{-η} / f`  together with  `ρ ≳ δ^η`.**

Against the two earlier node-count criteria:

* `Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid_of_card_activeTubeNodes` asks
  `|𝕋_ρ| ≲ ρ δ^{-η}`, so this one is better by the factor `1/f`, which is `δ^{-2η}` at the
  smallest admissible density `lam = Cd δ^{2η}`;
* `Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid_of_card_activeTubeNodes_boost` (the
  single-node case) asks `|𝕋_ρ| ≲ 1/f`, so this one is better by the factor `ρ δ^{-η}`, which
  exceeds `1` exactly on the range `ρ ≳ δ^η` where the criterion applies at all.

So this statement dominates both. It is still not the residue: bounding `|𝕋_ρ|` on the fine part
of the grid is itself open, and `|𝕋_ρ|` may be as large as `|𝕋| ≍ δ^{-2}`. -/
theorem exists_coarseShadedFamilyAtGrid_of_card_activeTubeNodes_greedy (cfg : VeryNotSticky.{u})
    (𝒱 : ShadedTube.ShadedUniformTubeSet cfg.s cfg.T (Tube.ssfGridLen cfg.δ) cfg.C₀)
    {k : ℕ} (hk : k ≤ Tube.ssfGridLen cfg.δ)
    {ρ : NNReal} (hgrid : Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k = ρ) (hρ1 : ρ ≤ 1)
    (hbudget : 2 * (cfg.δ : ENNReal) ^ cfg.η *
        ((((cfg.Cd * shadingMultiplicityEstimateForRhoTubes.C)⁻¹ * cfg.lam : NNReal) : ENNReal) *
            (((cfg.activeTubeNodes 𝒱.tubeUniform k).card : ENNReal) *
              (((_root_.Tube.volume_le.C 3 : NNReal) : ENNReal) * (ρ : ENNReal) ^ 2))
          + ((_root_.Tube.volume_le.C 3 : NNReal) : ENNReal) * (ρ : ENNReal) ^ 2)
      ≤ volume (ball (0 : EuclideanSpace ℝ (Fin 3)) (ρ : ℝ))) :
    ∃ G : ShadedFactorFamily (EuclideanSpace ℝ (Fin 3)) cfg.ι cfg.ι,
      G.innerSet = cfg.s ∧
      (∀ i ∈ cfg.s, G.innerBody i = (cfg.T i).toShadedBody) ∧
      G.outerSet = cfg.activeTubeNodes 𝒱.tubeUniform k ∧
      (∀ j ∈ G.outerSet,
        (G.outerBody j).toConvexSpaceBody =
          (𝒱.tubeUniform.cover.tube k j).toConvexSpaceBody) ∧
      (cfg.Cd * shadingMultiplicityEstimateForRhoTubes.C)⁻¹ * cfg.lam ≤
        ShadedBody.fullness G.outerSet G.outerBody ∧
      (∀ x ∈ ⋃ j ∈ G.outerSet, (G.outerBody j).shade,
        (cfg.δ : ENNReal) ^ cfg.η *
            (((shadingMultiplicityEstimateForRhoTubes.C : NNReal) : ENNReal)⁻¹ *
                volume (⋃ j ∈ G.outerSet, (G.outerBody j).shade) *
              (volume ((⋃ i ∈ G.innerSet, (G.innerBody i).shade) ∩ ball x (ρ : ℝ)) /
                volume (ball x (ρ : ℝ)))) ≤
          volume (⋃ i ∈ G.innerSet, (G.innerBody i).shade)) := by
  classical
  have hfr : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
  have hg1 : Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k ≤ 1 := by rw [hgrid]; exact hρ1
  have hper : ∀ j : cfg.ι,
      volume ((𝒱.tubeUniform.cover.tube k j).toConvexSpaceBody.carrier) ≤
        ((_root_.Tube.volume_le.C 3 : NNReal) : ENNReal) * (ρ : ENNReal) ^ 2 := by
    intro j
    have h := _root_.Tube.volume_le hg1 (𝒱.tubeUniform.cover.tube k j)
    rw [hfr] at h
    refine h.trans (le_of_eq ?_)
    rw [hgrid]
  have hCd0 : (cfg.Cd : NNReal) ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one cfg.hCd)
  have hfle : ((cfg.Cd * shadingMultiplicityEstimateForRhoTubes.C)⁻¹ * cfg.lam : NNReal) ≤ 1 := by
    rw [ShadedBody.shadingMultiplicityEstimateForRhoTubes.C, mul_one]
    calc (cfg.Cd)⁻¹ * cfg.lam ≤ (cfg.Cd)⁻¹ * cfg.Cd := by gcongr; exact cfg.lam_le_Cd
      _ = 1 := inv_mul_cancel₀ hCd0
  set S : ENNReal := ∑ j ∈ cfg.activeTubeNodes 𝒱.tubeUniform k,
    volume ((𝒱.tubeUniform.cover.tube k j).toConvexSpaceBody.carrier) with hSdef
  have hStarget :
      (((cfg.Cd * shadingMultiplicityEstimateForRhoTubes.C)⁻¹ * cfg.lam : NNReal) : ENNReal) * S
        ≤ S := by
    calc (((cfg.Cd * shadingMultiplicityEstimateForRhoTubes.C)⁻¹ * cfg.lam : NNReal) : ENNReal) * S
        ≤ 1 * S := by gcongr; exact_mod_cast hfle
      _ = S := one_mul S
  obtain ⟨A, hA, hAlow, hAhigh⟩ :=
    exists_subset_sum_between (cfg.activeTubeNodes 𝒱.tubeUniform k)
      (fun j => volume ((𝒱.tubeUniform.cover.tube k j).toConvexSpaceBody.carrier))
      hStarget (fun j _ => hper j)
  have hScard : S ≤ ((cfg.activeTubeNodes 𝒱.tubeUniform k).card : ENNReal) *
      (((_root_.Tube.volume_le.C 3 : NNReal) : ENNReal) * (ρ : ENNReal) ^ 2) := by
    rw [hSdef, ← nsmul_eq_mul]
    exact Finset.sum_le_card_nsmul _ _ _ (fun j _ => hper j)
  refine cfg.exists_coarseShadedFamilyAtGrid_of_nodeSubset 𝒱 hk hgrid A hA ?_ hAlow
  refine le_trans ?_ hbudget
  gcongr
  refine hAhigh.trans ?_
  gcongr

open MeasureTheory Metric Set ShadedBody in
/-- **The `r`-ball pigeonhole for the node carrier mass.**

Every active node tube lies in `B(0,4)`
(`Kakeya.VeryNotSticky.activeTubeNodes_carrier_subset_closedBall`), so covering `B(0,4)` by
`N = coveringNumber r (B(0,4))` balls of radius `r` and summing shows some ball of radius `r`
carries at least a `1/N` share of the total carrier mass `∑_j |T_{ρ,j}|`. The covering number is
bounded through `Metric.coveringNumber_mul_pow_le_volume_cthickening` at
`cthickening r (B(0,4)) = B(0,4+r) ⊆ B(0,5)`, which is where the `125` comes from: the
hypothesis is exactly `N · t ≤ ∑_j |T_{ρ,j}|` with `N` replaced by that bound. -/
theorem exists_ball_capturing_node_mass (cfg : VeryNotSticky.{u})
    (𝒱 : ShadedTube.ShadedUniformTubeSet cfg.s cfg.T (Tube.ssfGridLen cfg.δ) cfg.C₀)
    {k : ℕ} (hk : k ≤ Tube.ssfGridLen cfg.δ)
    {r : NNReal} (hr : 0 < r) (hr1 : r ≤ 1) {t : ENNReal}
    (ht : 125 * volume (ball (0 : EuclideanSpace ℝ (Fin 3)) 1) * t
        ≤ ((Metric.coveringNumber_mul_pow_le_volume_cthickening.C 3 : NNReal) : ENNReal) *
            ((r : ENNReal) ^ 3 *
              ∑ j ∈ cfg.activeTubeNodes 𝒱.tubeUniform k,
                volume ((𝒱.tubeUniform.cover.tube k j).toConvexSpaceBody.carrier))) :
    ∃ y : EuclideanSpace ℝ (Fin 3),
      t ≤ ∑ j ∈ cfg.activeTubeNodes 𝒱.tubeUniform k,
        volume ((𝒱.tubeUniform.cover.tube k j).toConvexSpaceBody.carrier ∩
          closedBall y (r : ℝ)) := by
  classical
  set Cst : NNReal := Metric.coveringNumber_mul_pow_le_volume_cthickening.C 3 with hCst
  set A := cfg.activeTubeNodes 𝒱.tubeUniform k with hA
  set S : ENNReal := ∑ j ∈ A,
    volume ((𝒱.tubeUniform.cover.tube k j).toConvexSpaceBody.carrier) with hS
  have hfr : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
  -- a finite `r`-cover of `B(0,4)`
  have hbdd : Bornology.IsBounded (closedBall (0 : EuclideanSpace ℝ (Fin 3)) 4) :=
    Metric.isBounded_closedBall
  obtain ⟨C, -, hCcov, hCcard⟩ := hbdd.exists_finset_card_eq_coveringNumber hr
  have hcov : closedBall (0 : EuclideanSpace ℝ (Fin 3)) 4 ⊆ ⋃ y ∈ C, closedBall y (r : ℝ) := by
    intro x hx
    obtain ⟨y, hyC, hxy⟩ := hCcov hx
    refine Set.mem_biUnion hyC ?_
    rw [Metric.mem_closedBall]
    have : ENNReal.ofReal (dist x y) ≤ ENNReal.ofReal (r : ℝ) := by
      rw [← edist_dist]
      simpa [ENNReal.ofReal_coe_nnreal] using hxy
    exact (ENNReal.ofReal_le_ofReal_iff r.coe_nonneg).mp this
  have hCne : C.Nonempty := by
    have h0 : (0 : EuclideanSpace ℝ (Fin 3)) ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 4 := by
      simp
    obtain ⟨y, hy, -⟩ := hCcov h0
    exact ⟨y, hy⟩
  -- the mass is spread over the cover
  have hSle : S ≤ ∑ y ∈ C, ∑ j ∈ A,
      volume ((𝒱.tubeUniform.cover.tube k j).toConvexSpaceBody.carrier ∩
        closedBall y (r : ℝ)) := by
    rw [Finset.sum_comm]
    refine Finset.sum_le_sum (fun j hj => ?_)
    have hsub : (𝒱.tubeUniform.cover.tube k j).toConvexSpaceBody.carrier
        ⊆ ⋃ y ∈ C, ((𝒱.tubeUniform.cover.tube k j).toConvexSpaceBody.carrier ∩
            closedBall y (r : ℝ)) := by
      intro x hx
      obtain ⟨y, hy, hxy⟩ :=
        Set.mem_iUnion₂.mp (hcov (cfg.activeTubeNodes_carrier_subset_closedBall 𝒱 hk hj hx))
      exact Set.mem_biUnion hy ⟨hx, hxy⟩
    exact le_trans (measure_mono hsub) (measure_biUnion_finset_le _ _)
  -- the covering number is bounded
  have hCstpos : (0 : ENNReal) < (Cst : ENNReal) :=
    ENNReal.coe_pos.mpr (Metric.coveringNumber_mul_pow_le_volume_cthickening.C_pos 3)
  have hcard : (C.card : ENNReal) * ((Cst : ENNReal) * (r : ENNReal) ^ 3)
      ≤ 125 * volume (ball (0 : EuclideanSpace ℝ (Fin 3)) 1) := by
    have hbase := Metric.coveringNumber_mul_pow_le_volume_cthickening
      (E := EuclideanSpace ℝ (Fin 3)) r (closedBall (0 : EuclideanSpace ℝ (Fin 3)) 4)
    rw [hfr] at hbase
    have hcn : ((Metric.coveringNumber r (closedBall (0 : EuclideanSpace ℝ (Fin 3)) 4) :
        ℕ∞) : ENNReal) = (C.card : ENNReal) := by
      rw [← hCcard]; simp
    rw [hcn] at hbase
    have hct : Metric.cthickening (r : ℝ) (closedBall (0 : EuclideanSpace ℝ (Fin 3)) 4)
        = closedBall (0 : EuclideanSpace ℝ (Fin 3)) ((r : ℝ) + 4) :=
      _root_.cthickening_closedBall r.coe_nonneg (by norm_num) _
    have hvol : volume (closedBall (0 : EuclideanSpace ℝ (Fin 3)) ((r : ℝ) + 4))
        ≤ 125 * volume (ball (0 : EuclideanSpace ℝ (Fin 3)) 1) := by
      have h5 : closedBall (0 : EuclideanSpace ℝ (Fin 3)) ((r : ℝ) + 4)
          ⊆ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 5 := by
        refine closedBall_subset_closedBall ?_
        have : (r : ℝ) ≤ 1 := by exact_mod_cast hr1
        linarith
      refine le_trans (measure_mono h5) (le_of_eq ?_)
      have h := MeasureTheory.Measure.addHaar_closedBall
        (volume : Measure (EuclideanSpace ℝ (Fin 3))) 0 (by norm_num : (0:ℝ) ≤ 5)
      rw [hfr] at h
      rw [h]; norm_num
    calc (C.card : ENNReal) * ((Cst : ENNReal) * (r : ENNReal) ^ 3)
        = (Cst : ENNReal) * (C.card : ENNReal) * (r : ENNReal) ^ 3 := by ring
      _ ≤ volume (Metric.cthickening (r : ℝ) (closedBall (0 : EuclideanSpace ℝ (Fin 3)) 4)) :=
          hbase
      _ ≤ 125 * volume (ball (0 : EuclideanSpace ℝ (Fin 3)) 1) := by rw [hct]; exact hvol
  -- pigeonhole
  have hkey : ((Cst : ENNReal) * (r : ENNReal) ^ 3) * ((C.card : ENNReal) * t)
      ≤ ((Cst : ENNReal) * (r : ENNReal) ^ 3) * S := by
    calc ((Cst : ENNReal) * (r : ENNReal) ^ 3) * ((C.card : ENNReal) * t)
        = ((C.card : ENNReal) * ((Cst : ENNReal) * (r : ENNReal) ^ 3)) * t := by ring
      _ ≤ (125 * volume (ball (0 : EuclideanSpace ℝ (Fin 3)) 1)) * t := by gcongr
      _ ≤ (Cst : ENNReal) * ((r : ENNReal) ^ 3 * S) := ht
      _ = ((Cst : ENNReal) * (r : ENNReal) ^ 3) * S := by ring
  have hne : ((Cst : ENNReal) * (r : ENNReal) ^ 3) ≠ 0 := by
    refine mul_ne_zero hCstpos.ne' ?_
    exact (ENNReal.pow_pos (by exact_mod_cast hr) 3).ne'
  have htop : ((Cst : ENNReal) * (r : ENNReal) ^ 3) ≠ ⊤ := by
    refine ENNReal.mul_ne_top ENNReal.coe_ne_top ?_
    exact ENNReal.pow_ne_top ENNReal.coe_ne_top
  have hcardt : (C.card : ENNReal) * t ≤ S :=
    (ENNReal.mul_le_mul_iff_right hne htop).mp hkey
  -- the best ball of the cover
  obtain ⟨y, hyC, hymax⟩ := Finset.exists_max_image C
    (fun y => ∑ j ∈ A, volume ((𝒱.tubeUniform.cover.tube k j).toConvexSpaceBody.carrier ∩
      closedBall y (r : ℝ))) hCne
  refine ⟨y, ?_⟩
  have hcard0 : (C.card : ENNReal) ≠ 0 := by
    have : 0 < C.card := Finset.card_pos.mpr hCne
    exact_mod_cast this.ne'
  have hcardtop : (C.card : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top _
  refine (ENNReal.mul_le_mul_iff_right hcard0 hcardtop).mp ?_
  refine le_trans hcardt (le_trans hSle ?_)
  rw [← nsmul_eq_mul]
  exact Finset.sum_le_card_nsmul _ _ _ (fun y' hy' => hymax y' hy')

open MeasureTheory Metric Set ShadedBody in
/-- The volume of a *closed* ball of radius `r` in `EuclideanSpace ℝ (Fin 3)`, in the shape the
boost-set budget consumes. -/
theorem volume_closedBall_eq_pow_mul (y : EuclideanSpace ℝ (Fin 3)) (r : NNReal) :
    volume (closedBall y (r : ℝ))
      = (r : ENNReal) ^ 3 * volume (ball (0 : EuclideanSpace ℝ (Fin 3)) 1) := by
  have h := MeasureTheory.Measure.addHaar_closedBall
    (volume : Measure (EuclideanSpace ℝ (Fin 3))) y (r.coe_nonneg)
  have hfr : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
  rw [hfr] at h
  rw [h, ENNReal.ofReal_pow r.coe_nonneg, ENNReal.ofReal_coe_nnreal]

open MeasureTheory Metric Set ShadedBody in
/-- **THE BALL BOOST: the residue from a scale `r` alone.**

Combine `Kakeya.VeryNotSticky.exists_ball_capturing_node_mass` with
`Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid_of_boostSet`: the boost set is a single
*ball* `B(y, r)`, chosen by pigeonhole to carry a `1/N` share of the node carrier mass, `N` the
covering number of `B(0,4)` at scale `r`. The two hypotheses are

* the **budget** `2 δ^η r³ |B(0,1)| ≤ |B(0,ρ)|` — the ball must fit the boost-set budget, and
* the **pigeonhole** `125 |B(0,1)| · (Cd·C)⁻¹ lam ≤ C₃ r³` — the share `1/N ≳ r³` must reach the
  fullness target,

and they pull against each other only through `r³`. There is nothing else: no node count, no
density, no supremum. Eliminating `r³` between them gives the range recorded in
`Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid_of_gridScale_ge_lam`. -/
theorem exists_coarseShadedFamilyAtGrid_of_ballBoost (cfg : VeryNotSticky.{u})
    (𝒱 : ShadedTube.ShadedUniformTubeSet cfg.s cfg.T (Tube.ssfGridLen cfg.δ) cfg.C₀)
    {k : ℕ} (hk : k ≤ Tube.ssfGridLen cfg.δ)
    {ρ : NNReal} (hgrid : Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k = ρ)
    {r : NNReal} (hr : 0 < r) (hr1 : r ≤ 1)
    (hbudget : 2 * (cfg.δ : ENNReal) ^ cfg.η *
        ((r : ENNReal) ^ 3 * volume (ball (0 : EuclideanSpace ℝ (Fin 3)) 1))
      ≤ volume (ball (0 : EuclideanSpace ℝ (Fin 3)) (ρ : ℝ)))
    (hfrac : 125 * volume (ball (0 : EuclideanSpace ℝ (Fin 3)) 1) *
        (((cfg.Cd * shadingMultiplicityEstimateForRhoTubes.C)⁻¹ * cfg.lam : NNReal) : ENNReal)
      ≤ ((Metric.coveringNumber_mul_pow_le_volume_cthickening.C 3 : NNReal) : ENNReal) *
          (r : ENNReal) ^ 3) :
    ∃ G : ShadedFactorFamily (EuclideanSpace ℝ (Fin 3)) cfg.ι cfg.ι,
      G.innerSet = cfg.s ∧
      (∀ i ∈ cfg.s, G.innerBody i = (cfg.T i).toShadedBody) ∧
      G.outerSet = cfg.activeTubeNodes 𝒱.tubeUniform k ∧
      (∀ j ∈ G.outerSet,
        (G.outerBody j).toConvexSpaceBody =
          (𝒱.tubeUniform.cover.tube k j).toConvexSpaceBody) ∧
      (cfg.Cd * shadingMultiplicityEstimateForRhoTubes.C)⁻¹ * cfg.lam ≤
        ShadedBody.fullness G.outerSet G.outerBody ∧
      (∀ x ∈ ⋃ j ∈ G.outerSet, (G.outerBody j).shade,
        (cfg.δ : ENNReal) ^ cfg.η *
            (((shadingMultiplicityEstimateForRhoTubes.C : NNReal) : ENNReal)⁻¹ *
                volume (⋃ j ∈ G.outerSet, (G.outerBody j).shade) *
              (volume ((⋃ i ∈ G.innerSet, (G.innerBody i).shade) ∩ ball x (ρ : ℝ)) /
                volume (ball x (ρ : ℝ)))) ≤
          volume (⋃ i ∈ G.innerSet, (G.innerBody i).shade)) := by
  classical
  set f : ENNReal :=
    (((cfg.Cd * shadingMultiplicityEstimateForRhoTubes.C)⁻¹ * cfg.lam : NNReal) : ENNReal) with hf
  set S : ENNReal := ∑ j ∈ cfg.activeTubeNodes 𝒱.tubeUniform k,
    volume ((𝒱.tubeUniform.cover.tube k j).toConvexSpaceBody.carrier) with hS
  have ht : 125 * volume (ball (0 : EuclideanSpace ℝ (Fin 3)) 1) * (f * S)
      ≤ ((Metric.coveringNumber_mul_pow_le_volume_cthickening.C 3 : NNReal) : ENNReal) *
          ((r : ENNReal) ^ 3 * S) := by
    calc 125 * volume (ball (0 : EuclideanSpace ℝ (Fin 3)) 1) * (f * S)
        = (125 * volume (ball (0 : EuclideanSpace ℝ (Fin 3)) 1) * f) * S := by ring
      _ ≤ (((Metric.coveringNumber_mul_pow_le_volume_cthickening.C 3 : NNReal) : ENNReal) *
            (r : ENNReal) ^ 3) * S := by gcongr
      _ = ((Metric.coveringNumber_mul_pow_le_volume_cthickening.C 3 : NNReal) : ENNReal) *
            ((r : ENNReal) ^ 3 * S) := by ring
  obtain ⟨y, hy⟩ := cfg.exists_ball_capturing_node_mass 𝒱 hk hr hr1 ht
  refine cfg.exists_coarseShadedFamilyAtGrid_of_boostSet 𝒱 hk hgrid
    (closedBall y (r : ℝ)) measurableSet_closedBall ?_ ?_
  · rw [volume_closedBall_eq_pow_mul y r]
    exact hbudget
  · refine le_trans hy (Finset.sum_le_sum (fun j _ => measure_mono ?_))
    exact Set.inter_subset_inter_right _ Set.subset_union_right

open MeasureTheory Metric Set ShadedBody in
/-- **A NEW UNCONDITIONAL RANGE AT THE FINE END OF THE GRID.**

Eliminate `r` from `Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid_of_ballBoost` by taking
the largest ball the budget allows, `64 δ^η r³ = ρ³` (so `r ≤ 1` exactly on the range
`ρ³ ≤ 64 δ^η` that `Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid_of_coarseBall` leaves
open). What remains is the single threshold

  `8000 · |B(0,1)| · (Cd·C)⁻¹ lam · δ^η ≤ C₃ · ρ³`,   `C₃ = coveringNumber…C 3`,

which with the numerical values `|B(0,1)| = 4π/3` and `C₃ = π/6` reads `ρ³ ≥ 64000 · lam/Cd · δ^η`.

**This strictly improves the previously known unconditional range** whenever
`lam/Cd ≤ 1/1000`, and the improvement is a power of `δ` in the regime the section is about:
at the smallest admissible density `lam = Cd δ^{2η}` (the field
`Kakeya.VeryNotSticky.lam_ge` allows nothing smaller) the threshold is `ρ³ ≳ δ^{3η}`, i.e.
`ρ ≳ δ^η`, against the `ρ ≥ 4 δ^{η/3}` of
`Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid_of_gridScale_ge`. So the open window at
the fine end shrinks from `δ ≤ ρ < 4 δ^{η/3}` to `δ ≤ ρ ≲ δ^η`.

The mechanism, in one line: the *saturated* shading pays `|⋃𝕋_ρ| ≍ 1` for a fullness of `1`,
which is `1/lam` times more than the residue asks for; a pigeonholed ball of radius
`r ≍ ρ δ^{-η/3}` buys the fullness the residue *does* ask for at a cost of only `r³`. -/
theorem exists_coarseShadedFamilyAtGrid_of_gridScale_ge_lam (cfg : VeryNotSticky.{u})
    (𝒱 : ShadedTube.ShadedUniformTubeSet cfg.s cfg.T (Tube.ssfGridLen cfg.δ) cfg.C₀)
    {k : ℕ} (hk : k ≤ Tube.ssfGridLen cfg.δ)
    {ρ : NNReal} (hgrid : Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k = ρ) (hρ0 : 0 < ρ)
    (hρsmall : ρ ^ (3 : ℕ) ≤ 64 * (cfg.δ : NNReal) ^ cfg.η)
    (hthr : 8000 * volume (ball (0 : EuclideanSpace ℝ (Fin 3)) 1) *
          (((cfg.Cd * shadingMultiplicityEstimateForRhoTubes.C)⁻¹ * cfg.lam : NNReal) : ENNReal) *
          (cfg.δ : ENNReal) ^ cfg.η
      ≤ ((Metric.coveringNumber_mul_pow_le_volume_cthickening.C 3 : NNReal) : ENNReal) *
          (ρ : ENNReal) ^ 3) :
    ∃ G : ShadedFactorFamily (EuclideanSpace ℝ (Fin 3)) cfg.ι cfg.ι,
      G.innerSet = cfg.s ∧
      (∀ i ∈ cfg.s, G.innerBody i = (cfg.T i).toShadedBody) ∧
      G.outerSet = cfg.activeTubeNodes 𝒱.tubeUniform k ∧
      (∀ j ∈ G.outerSet,
        (G.outerBody j).toConvexSpaceBody =
          (𝒱.tubeUniform.cover.tube k j).toConvexSpaceBody) ∧
      (cfg.Cd * shadingMultiplicityEstimateForRhoTubes.C)⁻¹ * cfg.lam ≤
        ShadedBody.fullness G.outerSet G.outerBody ∧
      (∀ x ∈ ⋃ j ∈ G.outerSet, (G.outerBody j).shade,
        (cfg.δ : ENNReal) ^ cfg.η *
            (((shadingMultiplicityEstimateForRhoTubes.C : NNReal) : ENNReal)⁻¹ *
                volume (⋃ j ∈ G.outerSet, (G.outerBody j).shade) *
              (volume ((⋃ i ∈ G.innerSet, (G.innerBody i).shade) ∩ ball x (ρ : ℝ)) /
                volume (ball x (ρ : ℝ)))) ≤
          volume (⋃ i ∈ G.innerSet, (G.innerBody i).shade)) := by
  classical
  have hηnn : (0 : ℝ) ≤ cfg.η := cfg.hη.le
  have hδpow : (0 : NNReal) < (cfg.δ : NNReal) ^ cfg.η := NNReal.rpow_pos cfg.hδ
  have hden : (0 : NNReal) < 64 * (cfg.δ : NNReal) ^ cfg.η := by positivity
  set w : NNReal := ρ ^ (3 : ℕ) / (64 * (cfg.δ : NNReal) ^ cfg.η) with hwdef
  have hw0 : 0 < w := by
    rw [hwdef]
    exact div_pos (pow_pos hρ0 3) hden
  have hw1 : w ≤ 1 := by
    rw [hwdef, div_le_one hden]
    exact hρsmall
  have hcube : (w ^ ((3 : ℝ)⁻¹)) ^ (3 : ℕ) = w := by
    rw [← NNReal.rpow_natCast (w ^ ((3 : ℝ)⁻¹)) 3, ← NNReal.rpow_mul]
    norm_num
  have hmul : (64 * (cfg.δ : NNReal) ^ cfg.η) * ((w ^ ((3 : ℝ)⁻¹)) ^ (3 : ℕ)) = ρ ^ (3 : ℕ) := by
    rw [hcube, hwdef, mul_div_cancel₀ _ hden.ne']
  -- transport to `ENNReal`
  have hcoeδ : (((cfg.δ : NNReal) ^ cfg.η : NNReal) : ENNReal) = (cfg.δ : ENNReal) ^ cfg.η :=
    ENNReal.coe_rpow_of_nonneg _ hηnn
  have hmulE : 64 * (cfg.δ : ENNReal) ^ cfg.η * ((w ^ ((3 : ℝ)⁻¹) : NNReal) : ENNReal) ^ 3
      = (ρ : ENNReal) ^ 3 := by
    have := congrArg (fun x : NNReal => (x : ENNReal)) hmul
    push_cast at this
    rw [← hcoeδ]
    exact this
  refine cfg.exists_coarseShadedFamilyAtGrid_of_ballBoost 𝒱 hk hgrid
    (r := w ^ ((3 : ℝ)⁻¹)) (NNReal.rpow_pos hw0)
    (NNReal.rpow_le_one hw1 (by norm_num)) ?_ ?_
  · rw [volume_ball_eq_pow_mul ρ, ← hmulE]
    have h2 : (2 : ENNReal) * (cfg.δ : ENNReal) ^ cfg.η
        ≤ 64 * (cfg.δ : ENNReal) ^ cfg.η := by gcongr; norm_num
    calc 2 * (cfg.δ : ENNReal) ^ cfg.η *
          (((w ^ ((3 : ℝ)⁻¹) : NNReal) : ENNReal) ^ 3 *
            volume (ball (0 : EuclideanSpace ℝ (Fin 3)) 1))
        = (2 * (cfg.δ : ENNReal) ^ cfg.η * ((w ^ ((3 : ℝ)⁻¹) : NNReal) : ENNReal) ^ 3) *
            volume (ball (0 : EuclideanSpace ℝ (Fin 3)) 1) := by ring
      _ ≤ (64 * (cfg.δ : ENNReal) ^ cfg.η * ((w ^ ((3 : ℝ)⁻¹) : NNReal) : ENNReal) ^ 3) *
            volume (ball (0 : EuclideanSpace ℝ (Fin 3)) 1) := by gcongr
  · have hcanc0 : (64 : ENNReal) * (cfg.δ : ENNReal) ^ cfg.η ≠ 0 := by
      refine mul_ne_zero (by norm_num) ?_
      rw [← hcoeδ]
      exact ENNReal.coe_ne_zero.mpr hδpow.ne'
    have hcanctop : (64 : ENNReal) * (cfg.δ : ENNReal) ^ cfg.η ≠ ⊤ := by
      refine ENNReal.mul_ne_top (by norm_num) ?_
      rw [← hcoeδ]
      exact ENNReal.coe_ne_top
    refine (ENNReal.mul_le_mul_iff_right hcanc0 hcanctop).mp ?_
    calc 64 * (cfg.δ : ENNReal) ^ cfg.η *
          (125 * volume (ball (0 : EuclideanSpace ℝ (Fin 3)) 1) *
            (((cfg.Cd * shadingMultiplicityEstimateForRhoTubes.C)⁻¹ * cfg.lam : NNReal) :
              ENNReal))
        = 8000 * volume (ball (0 : EuclideanSpace ℝ (Fin 3)) 1) *
            (((cfg.Cd * shadingMultiplicityEstimateForRhoTubes.C)⁻¹ * cfg.lam : NNReal) :
              ENNReal) * (cfg.δ : ENNReal) ^ cfg.η := by ring
      _ ≤ ((Metric.coveringNumber_mul_pow_le_volume_cthickening.C 3 : NNReal) : ENNReal) *
            (ρ : ENNReal) ^ 3 := hthr
      _ = 64 * (cfg.δ : ENNReal) ^ cfg.η *
            (((Metric.coveringNumber_mul_pow_le_volume_cthickening.C 3 : NNReal) : ENNReal) *
              ((w ^ ((3 : ℝ)⁻¹) : NNReal) : ENNReal) ^ 3) := by
          rw [← hmulE]; ring

open MeasureTheory Metric Set ShadedBody in
/-- **`|B(0,1)| = 8 · C₃`.** The two dimensional constants of
`Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid_of_gridScale_ge_lam` differ by the
explicit factor `2³`, and no value of `Γ` has to be computed to see it: both
`EuclideanSpace.volume_ball` and
`Metric.coveringNumber_mul_pow_le_volume_cthickening.C` are built from the *same* expression
`√π ^ n / Γ(n/2 + 1)`, the latter carrying an extra `(1/2)^n`. -/
theorem volume_ball_one_eq_eight_mul_coveringConst :
    volume (ball (0 : EuclideanSpace ℝ (Fin 3)) 1)
      = 8 * ((Metric.coveringNumber_mul_pow_le_volume_cthickening.C 3 : NNReal) : ENNReal) := by
  have hX : (0 : ℝ) ≤ Real.sqrt Real.pi ^ 3 / Real.Gamma (((3 : ℕ) : ℝ) / 2 + 1) := by positivity
  have hCcoe : ((Metric.coveringNumber_mul_pow_le_volume_cthickening.C 3 : NNReal) : ENNReal)
      = ENNReal.ofReal ((1 / 2 : ℝ) ^ 3 *
          (Real.sqrt Real.pi ^ 3 / Real.Gamma (((3 : ℕ) : ℝ) / 2 + 1))) := by
    rw [← ENNReal.ofReal_coe_nnreal]
    rfl
  rw [EuclideanSpace.volume_ball]
  simp only [Fintype.card_fin, ENNReal.ofReal_one, one_pow, one_mul]
  rw [hCcoe, ← ENNReal.ofReal_ofNat 8, ← ENNReal.ofReal_mul (by norm_num)]
  congr 1
  ring

open MeasureTheory Metric Set ShadedBody in
/-- **THE NEW UNCONDITIONAL FINE-END RANGE, with the constant computed.**

`Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid_of_gridScale_ge_lam` with
`|B(0,1)| = 8 C₃` substituted: the residue holds at every grid scale with

  `64000 · (Cd·C)⁻¹ lam · δ^η ≤ ρ³ ≤ 64 δ^η`,

and `Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid_of_coarseBall` already covers
`ρ³ ≥ 64 δ^η`. So the residue holds at **every** grid scale with

  `ρ³ ≥ min (64 δ^η, 64000 · (lam/Cd) · δ^η)`,

and the second entry is the smaller as soon as `lam/Cd ≤ 1/1000`. At the smallest admissible
density, `lam = Cd δ^{2η}` (`Kakeya.VeryNotSticky.lam_ge`), it is `ρ³ ≥ 64000 δ^{3η}`, i.e.
`ρ ≳ δ^η` — a power of `δ` better than the `ρ ≥ 4 δ^{η/3}` that was the state of the art.
The residual open window at the fine end is `δ ≤ ρ ≲ (lam/Cd)^{1/3} δ^{η/3}`. -/
theorem exists_coarseShadedFamilyAtGrid_of_gridScale_ge_lam' (cfg : VeryNotSticky.{u})
    (𝒱 : ShadedTube.ShadedUniformTubeSet cfg.s cfg.T (Tube.ssfGridLen cfg.δ) cfg.C₀)
    {k : ℕ} (hk : k ≤ Tube.ssfGridLen cfg.δ)
    {ρ : NNReal} (hgrid : Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k = ρ) (hρ0 : 0 < ρ)
    (hρsmall : ρ ^ (3 : ℕ) ≤ 64 * (cfg.δ : NNReal) ^ cfg.η)
    (hthr : 64000 * ((cfg.Cd * shadingMultiplicityEstimateForRhoTubes.C)⁻¹ * cfg.lam) *
        (cfg.δ : NNReal) ^ cfg.η ≤ ρ ^ (3 : ℕ)) :
    ∃ G : ShadedFactorFamily (EuclideanSpace ℝ (Fin 3)) cfg.ι cfg.ι,
      G.innerSet = cfg.s ∧
      (∀ i ∈ cfg.s, G.innerBody i = (cfg.T i).toShadedBody) ∧
      G.outerSet = cfg.activeTubeNodes 𝒱.tubeUniform k ∧
      (∀ j ∈ G.outerSet,
        (G.outerBody j).toConvexSpaceBody =
          (𝒱.tubeUniform.cover.tube k j).toConvexSpaceBody) ∧
      (cfg.Cd * shadingMultiplicityEstimateForRhoTubes.C)⁻¹ * cfg.lam ≤
        ShadedBody.fullness G.outerSet G.outerBody ∧
      (∀ x ∈ ⋃ j ∈ G.outerSet, (G.outerBody j).shade,
        (cfg.δ : ENNReal) ^ cfg.η *
            (((shadingMultiplicityEstimateForRhoTubes.C : NNReal) : ENNReal)⁻¹ *
                volume (⋃ j ∈ G.outerSet, (G.outerBody j).shade) *
              (volume ((⋃ i ∈ G.innerSet, (G.innerBody i).shade) ∩ ball x (ρ : ℝ)) /
                volume (ball x (ρ : ℝ)))) ≤
          volume (⋃ i ∈ G.innerSet, (G.innerBody i).shade)) := by
  classical
  refine cfg.exists_coarseShadedFamilyAtGrid_of_gridScale_ge_lam 𝒱 hk hgrid hρ0 hρsmall ?_
  have hcoeδ : (((cfg.δ : NNReal) ^ cfg.η : NNReal) : ENNReal) = (cfg.δ : ENNReal) ^ cfg.η :=
    ENNReal.coe_rpow_of_nonneg _ cfg.hη.le
  have hthrE : ((64000 * ((cfg.Cd * shadingMultiplicityEstimateForRhoTubes.C)⁻¹ * cfg.lam) *
        (cfg.δ : NNReal) ^ cfg.η : NNReal) : ENNReal) ≤ ((ρ ^ (3 : ℕ) : NNReal) : ENNReal) :=
    ENNReal.coe_le_coe.mpr hthr
  push_cast at hthrE
  rw [hcoeδ] at hthrE
  rw [volume_ball_one_eq_eight_mul_coveringConst]
  calc 8000 * (8 * ((Metric.coveringNumber_mul_pow_le_volume_cthickening.C 3 : NNReal) :
          ENNReal)) *
        (((cfg.Cd * shadingMultiplicityEstimateForRhoTubes.C)⁻¹ * cfg.lam : NNReal) : ENNReal) *
        (cfg.δ : ENNReal) ^ cfg.η
      = ((Metric.coveringNumber_mul_pow_le_volume_cthickening.C 3 : NNReal) : ENNReal) *
          (64000 *
            (((cfg.Cd * shadingMultiplicityEstimateForRhoTubes.C)⁻¹ * cfg.lam : NNReal) :
              ENNReal) * (cfg.δ : ENNReal) ^ cfg.η) := by ring
    _ ≤ ((Metric.coveringNumber_mul_pow_le_volume_cthickening.C 3 : NNReal) : ENNReal) *
          (ρ : ENNReal) ^ 3 := by
        gcongr
        push_cast
        exact hthrE

open MeasureTheory Metric Set ShadedBody in
/-- **THE STATE OF THE ART FOR THIS RESIDUE, in one statement.**

The residue holds at every grid scale with

  `min (64 δ^η) (64000 · (Cd·C)⁻¹ lam · δ^η) ≤ ρ³`.

The first entry is
`Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid_of_coarseBall`; the second is
`Kakeya.VeryNotSticky.exists_coarseShadedFamilyAtGrid_of_gridScale_ge_lam'` (the pigeonholed
ball boost). The second is the smaller exactly when `(Cd·C)⁻¹ lam ≤ 1/1000`, and at the smallest
density the configuration permits, `lam = Cd δ^{2η}` (`Kakeya.VeryNotSticky.lam_ge`), it is
smaller by the factor `1000 δ^{2η}`, which `Kakeya.VeryNotSticky.rpow_eta_absorb_le_one` bounds
by `1000/15625²`. In exponents: `ρ ≳ δ^{η/3}` becomes `ρ ≳ δ^η`.

Nothing here reads the node count, the multiplicity, the max density, or the shaded union: it is
a statement about the grid scale, `δ^η` and `lam/Cd` alone. -/
theorem exists_coarseShadedFamilyAtGrid_of_gridScale_ge_min (cfg : VeryNotSticky.{u})
    (𝒱 : ShadedTube.ShadedUniformTubeSet cfg.s cfg.T (Tube.ssfGridLen cfg.δ) cfg.C₀)
    {k : ℕ} (hk : k ≤ Tube.ssfGridLen cfg.δ)
    {ρ : NNReal} (hgrid : Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k = ρ)
    (hρ : ρ ∈ Set.Icc cfg.δ 1)
    (hthr : min (64 * (cfg.δ : NNReal) ^ cfg.η)
        (64000 * ((cfg.Cd * shadingMultiplicityEstimateForRhoTubes.C)⁻¹ * cfg.lam) *
          (cfg.δ : NNReal) ^ cfg.η) ≤ ρ ^ (3 : ℕ)) :
    ∃ G : ShadedFactorFamily (EuclideanSpace ℝ (Fin 3)) cfg.ι cfg.ι,
      G.innerSet = cfg.s ∧
      (∀ i ∈ cfg.s, G.innerBody i = (cfg.T i).toShadedBody) ∧
      G.outerSet = cfg.activeTubeNodes 𝒱.tubeUniform k ∧
      (∀ j ∈ G.outerSet,
        (G.outerBody j).toConvexSpaceBody =
          (𝒱.tubeUniform.cover.tube k j).toConvexSpaceBody) ∧
      (cfg.Cd * shadingMultiplicityEstimateForRhoTubes.C)⁻¹ * cfg.lam ≤
        ShadedBody.fullness G.outerSet G.outerBody ∧
      (∀ x ∈ ⋃ j ∈ G.outerSet, (G.outerBody j).shade,
        (cfg.δ : ENNReal) ^ cfg.η *
            (((shadingMultiplicityEstimateForRhoTubes.C : NNReal) : ENNReal)⁻¹ *
                volume (⋃ j ∈ G.outerSet, (G.outerBody j).shade) *
              (volume ((⋃ i ∈ G.innerSet, (G.innerBody i).shade) ∩ ball x (ρ : ℝ)) /
                volume (ball x (ρ : ℝ)))) ≤
          volume (⋃ i ∈ G.innerSet, (G.innerBody i).shade)) := by
  classical
  have hρ0 : 0 < ρ := lt_of_lt_of_le cfg.hδ hρ.1
  have hconv : 64 * (cfg.δ : NNReal) ^ cfg.η ≤ ρ ^ (3 : ℕ) →
      64 * (cfg.δ : ENNReal) ^ cfg.η ≤ (ρ : ENNReal) ^ 3 := by
    intro h
    have hcoeδ : (((cfg.δ : NNReal) ^ cfg.η : NNReal) : ENNReal) = (cfg.δ : ENNReal) ^ cfg.η :=
      ENNReal.coe_rpow_of_nonneg _ cfg.hη.le
    have h' := ENNReal.coe_le_coe.mpr h
    push_cast at h'
    rwa [hcoeδ] at h'
  rcases min_cases (64 * (cfg.δ : NNReal) ^ cfg.η)
      (64000 * ((cfg.Cd * shadingMultiplicityEstimateForRhoTubes.C)⁻¹ * cfg.lam) *
        (cfg.δ : NNReal) ^ cfg.η) with ⟨heq, -⟩ | ⟨heq, -⟩
  · rw [heq] at hthr
    exact cfg.exists_coarseShadedFamilyAtGrid_of_coarseBall 𝒱 hk hgrid hρ (hconv hthr)
  · rw [heq] at hthr
    rcases le_total (ρ ^ (3 : ℕ)) (64 * (cfg.δ : NNReal) ^ cfg.η) with hsmall | hbig
    · exact cfg.exists_coarseShadedFamilyAtGrid_of_gridScale_ge_lam' 𝒱 hk hgrid hρ0 hsmall hthr
    · exact cfg.exists_coarseShadedFamilyAtGrid_of_coarseBall 𝒱 hk hgrid hρ (hconv hbig)

end Kakeya.VeryNotSticky
