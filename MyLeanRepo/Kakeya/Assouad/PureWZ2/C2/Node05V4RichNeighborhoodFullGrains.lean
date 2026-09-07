import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Node05V4RichFullLocalGrain
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Proposition64PreCommonBinGlobalGrainNeighborhoodProducer
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23LocalGraphFromFullGrains

/-!
# Direct-rich full grains on the selected global neighborhood

The global-neighborhood producer has already selected separated side-`sqrt rho`
parents and a genuine final-source witness on one fixed global-grain line in
each parent.  This module uses that same witness as the P1 normal anchor for
the heterogeneous first-coarse local grain.  Thus the local grains, normal
field, and fixed-line geometry remain indexed by one literal parent choice.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set Metric

attribute [local instance] Classical.propDecidable

namespace PureWZ2PreCommonBinGlobalGrainNeighborhoodData

variable
    {capability : PureWZ2PropStickyCapability}
    {sigma inputLoss delta rho outputLoss : ℝ}
    {schedule : PureWZ2Node05V4RichSecondCallSchedule sigma outputLoss}
    {current : PureWZ2ReentrantGrainSource
      sigma inputLoss delta capability.normalizationExponent}
    {rhoRequested : WZ2PaperRequestedScale delta}
    {inputLossLe :
      inputLoss ≤ (schedule.firstCallSchedule capability).kernel.sourceLoss}
    {sqrtRequested : WZ2PaperRequestedScale rhoRequested.1}
    {twoScale : PureWZ2Node05V4RichSecondCallData
      schedule current rhoRequested inputLossLe sqrtRequested}
    {pullback : PureWZ2Node05V4RichTwoScaleCellPullbackData
      (rho := rho) twoScale}
    (neighborhood : PureWZ2PreCommonBinGlobalGrainNeighborhoodData pullback)

/-- The genuine first-coarse carrier on the selected side-`sqrt rho`
parents.  This is the set `E` used by WZ Lemma 5.3; it is deliberately not
the final-`delta` pullback shading. -/
def coarseNeighborhood : Set Point3 :=
  ⋃ y ∈ neighborhood.sample,
    pullback.preCommonBinCoarseRegion (neighborhood.cube y)

theorem coarseNeighborhood_volume :
    MeasureTheory.volume neighborhood.coarseNeighborhood =
      (neighborhood.K : ENNReal) *
        twoScale.secondBalancedCover.cellMass := by
  let parentFamily : Finset (ℤ × ℤ × ℤ) :=
    neighborhood.sample.image neighborhood.cube
  have hparentFamily : parentFamily.card = neighborhood.K := by
    rw [Finset.card_image_of_injOn neighborhood.cube_injective]
    exact neighborhood.K_eq.symm
  have hactive : parentFamily ⊆
      twoScale.secondBalancedCover.activeCells := by
    intro parent hparent
    rcases Finset.mem_image.mp hparent with ⟨y, hy, rfl⟩
    exact neighborhood.cube_active hy
  have hunion :
      neighborhood.coarseNeighborhood =
        twoScale.secondRefinedFineShading.union ∩
          ⋃ parent ∈ parentFamily,
            wz1PaperGridCube sqrtRequested.1 parent := by
    rw [Set.inter_iUnion₂]
    ext point
    simp only [coarseNeighborhood, parentFamily, Set.mem_iUnion,
      Finset.mem_image]
    constructor
    · rintro ⟨y, hy, hpoint⟩
      refine ⟨neighborhood.cube y, ⟨y, hy, rfl⟩, ?_⟩
      simpa only [pullback.preCommonBinCoarseRegion_eq_parent] using hpoint
    · rintro ⟨parent, ⟨y, hy, hparent⟩, hpoint⟩
      subst parent
      refine ⟨y, hy, ?_⟩
      simpa only [pullback.preCommonBinCoarseRegion_eq_parent] using hpoint
  rw [hunion]
  have hvolume := twoScale.secondBalancedCover.selected_cells_volume
    parentFamily hactive
  simpa only [hparentFamily] using hvolume

/-- The sharp parent count and the second balanced-cell floor give the exact
paper volume threshold for the coarse neighborhood used by Lemma 5.3. -/
theorem coarseNeighborhood_volume_lower :
    Kakeya.realRpowENN rho
        (1 + sigma / 2 + neighborhood.neighborhoodLoss +
          twoScale.second.terminalLoss) ≤
      MeasureTheory.volume neighborhood.coarseNeighborhood := by
  have hrho : 0 < rho := by
    rw [← pullback.rhoRequested_eq]
    exact twoScale.first.publicSticky.coarse_extremal.delta_pos
  calc
    Kakeya.realRpowENN rho
          (1 + sigma / 2 + neighborhood.neighborhoodLoss +
            twoScale.second.terminalLoss) =
        Kakeya.realRpowENN rho
            (-1 / 2 + neighborhood.neighborhoodLoss) *
          Kakeya.realRpowENN rho
            (3 / 2 + sigma / 2 + twoScale.second.terminalLoss) := by
      rw [← realRpowENN_add hrho]
      congr 1
      ring
    _ ≤ (neighborhood.K : ENNReal) *
          twoScale.secondBalancedCover.cellMass := by
      gcongr
      · exact neighborhood.paper_K_lower
      · simpa only [pullback.rhoRequested_eq] using
          twoScale.second_cellMass_rho_power_lower
    _ = MeasureTheory.volume neighborhood.coarseNeighborhood :=
      neighborhood.coarseNeighborhood_volume.symm

/-- The fixed-line witnesses selected by the global neighborhood satisfy the
sharper distortion retained by the coordinate proof.  The margin below `4`
is used when the same anchors are reindexed by the finer graph y-layers. -/
theorem witness_dist_strong
    (first : ℝ) (hfirst : first ∈ neighborhood.sample)
    (second : ℝ) (hsecond : second ∈ neighborhood.sample) :
    dist (neighborhood.witness first) (neighborhood.witness second) ≤
      (33 / 10 : ℝ) * |first - second| := by
  by_cases heq : first = second
  · subst second
    simp
  · let firstPoint := neighborhood.witness first
    let secondPoint := neighborhood.witness second
    let root := sqrtRequested.1
    let d := |first - second|
    have hroot : 0 < root := twoScale.secondSticky.coarse_extremal.delta_pos
    have hrhoOne : rho ≤ 1 := by
      rw [← pullback.rhoRequested_eq]
      exact rhoRequested.property.2
    have hrhoRoot : rho ≤ root := by
      rw [show root = Real.sqrt rho by
        exact pullback.sqrtRequested_eq]
      nlinarith [Real.sq_sqrt (show 0 ≤ rho by
        rw [← pullback.rhoRequested_eq]
        exact twoScale.first.publicSticky.coarse_extremal.delta_pos.le),
        Real.sqrt_nonneg rho]
    have hdeltaRoot : delta ≤ root :=
      rhoRequested.property.1.trans_eq pullback.rhoRequested_eq |>.trans hrhoRoot
    have hfirstCube : firstPoint ∈
        wz1PaperGridCube root (neighborhood.cube first) := by
      exact pullback.preCommonBinFinePullback_subset_parent
        (neighborhood.witness_mem_pullback first hfirst)
    have hsecondCube : secondPoint ∈
        wz1PaperGridCube root (neighborhood.cube second) := by
      exact pullback.preCommonBinFinePullback_subset_parent
        (neighborhood.witness_mem_pullback second hsecond)
    rw [wz1PaperGridCube_eq_Ico hroot] at hfirstCube hsecondCube
    have hseparation : 500 * root ≤ d :=
      neighborhood.cube_separated first hfirst second hsecond heq
    have hfirstY : |firstPoint 1 - first| ≤ root / 2 := by
      rw [neighborhood.sample_eq_cube_center_y first hfirst]
      change |firstPoint 1 -
        (((neighborhood.cube first).2.1 : ℝ) + 1 / 2) * root| ≤ root / 2
      rw [abs_le]
      constructor <;> linarith [hfirstCube.2.2.1, hfirstCube.2.2.2.1]
    have hsecondY : |secondPoint 1 - second| ≤ root / 2 := by
      rw [neighborhood.sample_eq_cube_center_y second hsecond]
      change |secondPoint 1 -
        (((neighborhood.cube second).2.1 : ℝ) + 1 / 2) * root| ≤ root / 2
      rw [abs_le]
      constructor <;> linarith [hsecondCube.2.2.1, hsecondCube.2.2.2.1]
    have hy : |firstPoint 1 - secondPoint 1| ≤ d + root := by
      calc
        |firstPoint 1 - secondPoint 1| =
            |(firstPoint 1 - first) + (first - second) +
              (second - secondPoint 1)| := by ring_nf
        _ ≤ |firstPoint 1 - first| + |first - second| +
              |second - secondPoint 1| := by
          calc
            _ ≤ |(firstPoint 1 - first) + (first - second)| +
                  |second - secondPoint 1| := abs_add_le _ _
            _ ≤ (|firstPoint 1 - first| + |first - second|) +
                  |second - secondPoint 1| := by
              gcongr
              exact abs_add_le _ _
        _ ≤ d + root := by
          rw [abs_sub_comm second (secondPoint 1)]
          dsimp only [d]
          linarith
    have hprojection :
        |(firstPoint 0 +
              current.grain.globalGrains.slope neighborhood.lineHeight *
                firstPoint 1) -
            (secondPoint 0 +
              current.grain.globalGrains.slope neighborhood.lineHeight *
                secondPoint 1)| ≤ 2 * delta := by
      have hfirstLine := neighborhood.witness_near_global_grain first hfirst
      have hsecondLine := neighborhood.witness_near_global_grain second hsecond
      have hfirstInner :
          inner ℝ firstPoint
              (globalGrainDirection
                (current.grain.globalGrains.slope neighborhood.lineHeight)) =
            firstPoint 0 +
              current.grain.globalGrains.slope neighborhood.lineHeight *
                firstPoint 1 := by
        simp [globalGrainDirection, PiLp.inner_apply, Fin.sum_univ_succ]
      have hsecondInner :
          inner ℝ secondPoint
              (globalGrainDirection
                (current.grain.globalGrains.slope neighborhood.lineHeight)) =
            secondPoint 0 +
              current.grain.globalGrains.slope neighborhood.lineHeight *
                secondPoint 1 := by
        simp [globalGrainDirection, PiLp.inner_apply, Fin.sum_univ_succ]
      rw [hfirstInner] at hfirstLine
      rw [hsecondInner] at hsecondLine
      have htriangle := abs_sub
        ((firstPoint 0 +
            current.grain.globalGrains.slope neighborhood.lineHeight *
              firstPoint 1) - neighborhood.lineLevel)
        ((secondPoint 0 +
            current.grain.globalGrains.slope neighborhood.lineHeight *
              secondPoint 1) - neighborhood.lineLevel)
      have hrearrange :
          ((firstPoint 0 +
              current.grain.globalGrains.slope neighborhood.lineHeight *
                firstPoint 1) - neighborhood.lineLevel) -
            ((secondPoint 0 +
                current.grain.globalGrains.slope neighborhood.lineHeight *
                  secondPoint 1) - neighborhood.lineLevel) =
          (firstPoint 0 +
              current.grain.globalGrains.slope neighborhood.lineHeight *
                firstPoint 1) -
            (secondPoint 0 +
              current.grain.globalGrains.slope neighborhood.lineHeight *
                secondPoint 1) := by ring
      rw [hrearrange] at htriangle
      exact htriangle.trans (by linarith)
    have hslope :
        |current.grain.globalGrains.slope neighborhood.lineHeight| ≤ 3 :=
      current.grain.globalGrains.slope_bound
        neighborhood.lineHeight neighborhood.lineHeight_mem
    have hx : |firstPoint 0 - secondPoint 0| ≤ 3 * d + 5 * root := by
      have hsolve := abs_sub
        ((firstPoint 0 +
            current.grain.globalGrains.slope neighborhood.lineHeight *
              firstPoint 1) -
          (secondPoint 0 +
            current.grain.globalGrains.slope neighborhood.lineHeight *
              secondPoint 1))
        (current.grain.globalGrains.slope neighborhood.lineHeight *
          (firstPoint 1 - secondPoint 1))
      have hrearrange :
          ((firstPoint 0 +
              current.grain.globalGrains.slope neighborhood.lineHeight *
                firstPoint 1) -
            (secondPoint 0 +
              current.grain.globalGrains.slope neighborhood.lineHeight *
                secondPoint 1)) -
            current.grain.globalGrains.slope neighborhood.lineHeight *
              (firstPoint 1 - secondPoint 1) =
          firstPoint 0 - secondPoint 0 := by ring
      rw [hrearrange] at hsolve
      have hproduct :
          |current.grain.globalGrains.slope neighborhood.lineHeight *
              (firstPoint 1 - secondPoint 1)| ≤ 3 * (d + root) := by
        rw [abs_mul]
        exact mul_le_mul hslope hy (abs_nonneg _) (by positivity)
      calc
        |firstPoint 0 - secondPoint 0| ≤
            |(firstPoint 0 +
                current.grain.globalGrains.slope neighborhood.lineHeight *
                  firstPoint 1) -
              (secondPoint 0 +
                current.grain.globalGrains.slope neighborhood.lineHeight *
                  secondPoint 1)| +
              |current.grain.globalGrains.slope neighborhood.lineHeight *
                (firstPoint 1 - secondPoint 1)| := hsolve
        _ ≤ 2 * delta + 3 * (d + root) := by gcongr
        _ ≤ 3 * d + 5 * root := by linarith
    have hz : firstPoint 2 = secondPoint 2 :=
      (neighborhood.witness_height first hfirst).trans
        (neighborhood.witness_height second hsecond).symm
    have hdNonneg : 0 ≤ d := abs_nonneg _
    have hx' : |firstPoint 0 - secondPoint 0| ≤ 301 * d / 100 := by
      linarith [hx, hseparation]
    have hy' : |firstPoint 1 - secondPoint 1| ≤ 501 * d / 500 := by
      linarith [hy, hseparation]
    have hxSq :
        (firstPoint 0 - secondPoint 0) ^ 2 ≤ (301 * d / 100) ^ 2 := by
      rw [sq_le_sq]
      simpa [abs_of_nonneg (by positivity : 0 ≤ 301 * d / 100)] using hx'
    have hySq :
        (firstPoint 1 - secondPoint 1) ^ 2 ≤ (501 * d / 500) ^ 2 := by
      rw [sq_le_sq]
      simpa [abs_of_nonneg (by positivity : 0 ≤ 501 * d / 500)] using hy'
    have hzSq : (firstPoint 2 - secondPoint 2) ^ 2 = 0 := by
      rw [hz]
      ring
    have hcoeff :
        (301 * d / 100) ^ 2 + (501 * d / 500) ^ 2 ≤
          ((33 / 10 : ℝ) * d) ^ 2 := by
      nlinarith [sq_nonneg d]
    have hdistSq : dist firstPoint secondPoint ^ 2 ≤
        ((33 / 10 : ℝ) * d) ^ 2 := by
      rw [EuclideanSpace.dist_sq_eq, Fin.sum_univ_three]
      simpa [Real.dist_eq, sq_abs, hz] using
        (add_le_add hxSq hySq).trans hcoeff
    exact (sq_le_sq₀ dist_nonneg
      (by positivity : 0 ≤ (33 / 10 : ℝ) * d)).mp hdistSq

/-- The constant-four form consumed by the existing local-graph extension. -/
theorem witness_dist
    (first : ℝ) (hfirst : first ∈ neighborhood.sample)
    (second : ℝ) (hsecond : second ∈ neighborhood.sample) :
    dist (neighborhood.witness first) (neighborhood.witness second) ≤
      4 * |first - second| := by
  exact (neighborhood.witness_dist_strong first hfirst second hsecond).trans
    (by nlinarith [abs_nonneg (first - second)])

end PureWZ2PreCommonBinGlobalGrainNeighborhoodData

/-- Full local grains on exactly the side-`sqrt rho` parents selected by the
global-neighborhood step.  The stored anchor is the already selected
fixed-line witness, not a new existential point. -/
structure PureWZ2Node05V4RichNeighborhoodFullGrainData
    {capability : PureWZ2PropStickyCapability}
    {sigma inputLoss delta rho outputLoss eta : ℝ}
    {schedule : PureWZ2Node05V4RichSecondCallSchedule sigma outputLoss}
    {current : PureWZ2ReentrantGrainSource
      sigma inputLoss delta capability.normalizationExponent}
    {rhoRequested : WZ2PaperRequestedScale delta}
    {inputLossLe :
      inputLoss ≤ (schedule.firstCallSchedule capability).kernel.sourceLoss}
    {sqrtRequested : WZ2PaperRequestedScale rhoRequested.1}
    {twoScale : PureWZ2Node05V4RichSecondCallData
      schedule current rhoRequested inputLossLe sqrtRequested}
    {pullback : PureWZ2Node05V4RichTwoScaleCellPullbackData
      (rho := rho) twoScale}
    (witnesses : PureWZ2Node05V4RichCoarseCellWitnessData twoScale)
    (neighborhood : PureWZ2PreCommonBinGlobalGrainNeighborhoodData pullback) where
  sourceFor : ∀ y, y ∈ neighborhood.sample →
    PureWZ2Node05V4RichSecondStageSourceData
      pullback witnesses (neighborhood.cube y)
  fullGrainFor : ∀ y (hy : y ∈ neighborhood.sample),
    PureWZ2Node05V4RichFullLocalGrainData
      (eta := eta) (sourceFor y hy)
  fullGrain_anchor_eq : ∀ y (hy : y ∈ neighborhood.sample),
    (fullGrainFor y hy).anchor = neighborhood.witness y

namespace PureWZ2PreCommonBinGlobalGrainNeighborhoodData

/-- Construct the direct-rich local grain attached to every selected
global-neighborhood parent, using the neighborhood's own witness as anchor. -/
theorem directRichFullGrains
    {capability : PureWZ2PropStickyCapability}
    {sigma inputLoss delta rho outputLoss eta : ℝ}
    {schedule : PureWZ2Node05V4RichSecondCallSchedule sigma outputLoss}
    {current : PureWZ2ReentrantGrainSource
      sigma inputLoss delta capability.normalizationExponent}
    {rhoRequested : WZ2PaperRequestedScale delta}
    {inputLossLe :
      inputLoss ≤ (schedule.firstCallSchedule capability).kernel.sourceLoss}
    {sqrtRequested : WZ2PaperRequestedScale rhoRequested.1}
    {twoScale : PureWZ2Node05V4RichSecondCallData
      schedule current rhoRequested inputLossLe sqrtRequested}
    {pullback : PureWZ2Node05V4RichTwoScaleCellPullbackData
      (rho := rho) twoScale}
    (neighborhood : PureWZ2PreCommonBinGlobalGrainNeighborhoodData pullback)
    (witnesses : PureWZ2Node05V4RichCoarseCellWitnessData twoScale)
    (hbridge : PureWZ2PaperADBridgeStatement)
    (hcertificateOne : 4 * rhoRequested.1 ≤ 1)
    (hsourceFloor :
      Kakeya.realRpowENN (4 * rhoRequested.1)
          (3 / 2 + sigma / 2 + eta) ≤
        Kakeya.realRpowENN rhoRequested.1
          (3 / 2 + sigma / 2 + twoScale.second.terminalLoss))
    (hlocalPower :
      160 * Kakeya.realRpowENN delta (-inputLoss) ≤
        Kakeya.realRpowENN (4 * rhoRequested.1) (-eta)) :
    Nonempty (PureWZ2Node05V4RichNeighborhoodFullGrainData
      (eta := eta) witnesses neighborhood) := by
  let sourceFor : ∀ y, y ∈ neighborhood.sample →
      PureWZ2Node05V4RichSecondStageSourceData
        pullback witnesses (neighborhood.cube y) :=
    fun y hy => Classical.choice
      (pullback.secondStageSourceAt witnesses (neighborhood.cube y)
        (neighborhood.cube_active hy))
  have hanchorSource : ∀ y (hy : y ∈ neighborhood.sample),
      neighborhood.witness y ∈ current.grain.shading.union := by
    intro y hy
    exact pullback.subshading.union_subset
      (neighborhood.witness_mem_pullback y hy).1
  have hanchorParent : ∀ y (hy : y ∈ neighborhood.sample),
      neighborhood.witness y ∈
        wz1PaperGridCube sqrtRequested.1 (neighborhood.cube y) := by
    intro y hy
    exact pullback.preCommonBinFinePullback_subset_parent
      (neighborhood.witness_mem_pullback y hy)
  have hfull : ∀ y (hy : y ∈ neighborhood.sample),
      ∃ data : PureWZ2Node05V4RichFullLocalGrainData
          (eta := eta) (sourceFor y hy),
        data.anchor = neighborhood.witness y := by
    intro y hy
    exact (sourceFor y hy).fullLocalGrainAt
      (neighborhood.witness y) (hanchorSource y hy)
      (hanchorParent y hy) hbridge hcertificateOne hsourceFloor hlocalPower
  let fullGrainFor : ∀ y (hy : y ∈ neighborhood.sample),
      PureWZ2Node05V4RichFullLocalGrainData
        (eta := eta) (sourceFor y hy) :=
    fun y hy => Classical.choose (hfull y hy)
  exact ⟨{
    sourceFor := sourceFor
    fullGrainFor := fullGrainFor
    fullGrain_anchor_eq := fun y hy => Classical.choose_spec (hfull y hy)
  }⟩

end PureWZ2PreCommonBinGlobalGrainNeighborhoodData

namespace PureWZ2Node05V4RichNeighborhoodFullGrainData

variable
    {capability : PureWZ2PropStickyCapability}
    {sigma inputLoss delta rho outputLoss eta : ℝ}
    {schedule : PureWZ2Node05V4RichSecondCallSchedule sigma outputLoss}
    {current : PureWZ2ReentrantGrainSource
      sigma inputLoss delta capability.normalizationExponent}
    {rhoRequested : WZ2PaperRequestedScale delta}
    {inputLossLe :
      inputLoss ≤ (schedule.firstCallSchedule capability).kernel.sourceLoss}
    {sqrtRequested : WZ2PaperRequestedScale rhoRequested.1}
    {twoScale : PureWZ2Node05V4RichSecondCallData
      schedule current rhoRequested inputLossLe sqrtRequested}
    {pullback : PureWZ2Node05V4RichTwoScaleCellPullbackData
      (rho := rho) twoScale}
    {witnesses : PureWZ2Node05V4RichCoarseCellWitnessData twoScale}
    {neighborhood : PureWZ2PreCommonBinGlobalGrainNeighborhoodData pullback}
    (data : PureWZ2Node05V4RichNeighborhoodFullGrainData
      (eta := eta) witnesses neighborhood)

/-- The direct-rich selected parents produce the bounded local graph `g` when
global AD is supplied only after each full grain's actual Fubini height has
been selected. -/
theorem localGraphOfFubini
    (C : ENNReal)
    (hcertificateOne : 4 * rhoRequested.1 ≤ 1)
    (hglobalAt : ∀ y (hy : y ∈ neighborhood.sample),
      ∀ z (_hz : z ∈ Set.Ico
          (data.fullGrainFor y hy).graphLeft
          ((data.fullGrainFor y hy).graphLeft +
            Real.sqrt (data.fullGrainFor y hy).certificateScale)),
        Kakeya.realRpowENN
              (data.fullGrainFor y hy).certificateScale
              (3 / 2 + 2 * eta) ≤
            volume (wz1Lemma23PlanarSlice
              (data.fullGrainFor y hy).fiber.grain z) →
        ∃ projected : Set ℝ,
          IsADSet1 projected
              (data.fullGrainFor y hy).certificateScale
              (1 - sigma) C ∧
            (fun point : Point2 => point 0 +
                current.grain.globalGrains.slope z * point 1) ''
                wz1Lemma23PlanarSlice
                  (data.fullGrainFor y hy).fiber.grain z ⊆ projected)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (heta : 0 < eta) (hetaSigma : 4 * eta < sigma)
    (hCtop : C ≠ ⊤)
    (hCpower : C ≤ Kakeya.realRpowENN (4 * rhoRequested.1) (-eta))
    (hPlanarSmall : 32 * Real.rpow (4 * rhoRequested.1) eta ≤ 1)
    (hrootSmall20 : 20 * Real.sqrt (4 * rhoRequested.1) ≤ 1)
    (habsorb :
      Real.rpow (4 * rhoRequested.1) (1 - 4 * eta / sigma) ≤
        Real.sqrt (4 * rhoRequested.1) / 14) :
    ∃ g : ℝ → ℝ,
      LipschitzOnWith 64 g Set.univ ∧
      (∀ y, |g y| ≤ 2) ∧
      ∀ y (hy : y ∈ neighborhood.sample),
        g y =
          (data.fullGrainFor y hy).normal (2 : Fin 3) /
            (data.fullGrainFor y hy).normal (0 : Fin 3) := by
  let normal : Point3 → Point3 := fun point =>
    if hpoint : point ∈ current.grain.shading.union then
      current.grain.localGrains.planeMap ⟨point, hpoint⟩ else 0
  have hanchorSource : ∀ y (hy : y ∈ neighborhood.sample),
      neighborhood.witness y ∈ current.grain.shading.union := by
    intro y hy
    exact pullback.subshading.union_subset
      (neighborhood.witness_mem_pullback y hy).1
  have hnormalVertical : ∀ y ∈ neighborhood.sample,
      |normal (neighborhood.witness y) (2 : Fin 3)| ≤ 1 / 2 := by
    intro y hy
    simp only [normal, dif_pos (hanchorSource y hy)]
    exact current.grain.planeMap_vertical_bound _
  have hnormalFirst : ∀ y ∈ neighborhood.sample,
      1 / 4 ≤ |normal (neighborhood.witness y) (0 : Fin 3)| := by
    intro y hy
    let grain := data.fullGrainFor y hy
    have hfirst := grain.normal_firstOfFubini C (hglobalAt y hy)
      hsigma hsigmaOne heta hetaSigma hCtop
      (by simpa only [grain.certificateScale_eq] using hCpower)
      hcertificateOne
      (by simpa only [grain.certificateScale_eq] using hPlanarSmall)
      (by simpa only [grain.certificateScale_eq] using hrootSmall20)
      (by simpa only [grain.certificateScale_eq] using habsorb)
    have hnormalEq : grain.normal = normal (neighborhood.witness y) := by
      calc
        grain.normal = current.grain.localGrains.planeMap
            ⟨grain.anchor, grain.anchor_mem_source⟩ := grain.normal_eq
        _ = current.grain.localGrains.planeMap
            ⟨neighborhood.witness y, hanchorSource y hy⟩ := by
          congr 1
          apply Subtype.ext
          exact data.fullGrain_anchor_eq y hy
        _ = normal (neighborhood.witness y) := by
          simp [normal, hanchorSource y hy]
    rwa [hnormalEq] at hfirst
  have hnormalDist : ∀ first ∈ neighborhood.sample,
      ∀ second ∈ neighborhood.sample,
        dist (normal (neighborhood.witness first))
            (normal (neighborhood.witness second)) ≤
          dist (neighborhood.witness first) (neighborhood.witness second) := by
    intro first hfirst second hsecond
    simp only [normal, dif_pos (hanchorSource first hfirst),
      dif_pos (hanchorSource second hsecond)]
    simpa only [NNReal.coe_one, one_mul, Subtype.dist_eq] using
      current.grain.localGrains.planeMap_lipschitz.dist_le_mul
        (⟨neighborhood.witness first, hanchorSource first hfirst⟩ :
          {point : Point3 // point ∈ current.grain.shading.union})
        (⟨neighborhood.witness second, hanchorSource second hsecond⟩ :
          {point : Point3 // point ∈ current.grain.shading.union})
  rcases wz1_lemma23_local_graph_extension_of_distortion
      neighborhood.sample neighborhood.witness normal
      hnormalVertical hnormalFirst hnormalDist neighborhood.witness_dist with
    ⟨g, hgLip, hgBound, hgEq⟩
  refine ⟨g, hgLip, hgBound, ?_⟩
  intro y hy
  let grain := data.fullGrainFor y hy
  have hnormalEq : grain.normal = normal (neighborhood.witness y) := by
    calc
      grain.normal = current.grain.localGrains.planeMap
          ⟨grain.anchor, grain.anchor_mem_source⟩ := grain.normal_eq
      _ = current.grain.localGrains.planeMap
          ⟨neighborhood.witness y, hanchorSource y hy⟩ := by
        congr 1
        apply Subtype.ext
        exact data.fullGrain_anchor_eq y hy
      _ = normal (neighborhood.witness y) := by
        simp [normal, hanchorSource y hy]
  rw [hnormalEq]
  exact hgEq y hy

/-- Compatibility wrapper for callers that already have global AD throughout
each selected parent's height window. -/
theorem localGraph
    (C : ENNReal)
    (hcertificateOne : 4 * rhoRequested.1 ≤ 1)
    (hglobalAD : ∀ y (hy : y ∈ neighborhood.sample),
      ∀ z ∈ Set.Ico
          (data.fullGrainFor y hy).graphLeft
          ((data.fullGrainFor y hy).graphLeft +
            Real.sqrt (data.fullGrainFor y hy).certificateScale),
        IsADSet1
          (scalarProjection
            (globalGrainDirection (current.grain.globalGrains.slope z))
            (horizontalSlice (data.sourceFor y hy).fullSource z))
          (data.fullGrainFor y hy).certificateScale (1 - sigma) C)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (heta : 0 < eta) (hetaSigma : 4 * eta < sigma)
    (hCtop : C ≠ ⊤)
    (hCpower : C ≤ Kakeya.realRpowENN (4 * rhoRequested.1) (-eta))
    (hPlanarSmall : 32 * Real.rpow (4 * rhoRequested.1) eta ≤ 1)
    (hrootSmall20 : 20 * Real.sqrt (4 * rhoRequested.1) ≤ 1)
    (habsorb :
      Real.rpow (4 * rhoRequested.1) (1 - 4 * eta / sigma) ≤
        Real.sqrt (4 * rhoRequested.1) / 14) :
    ∃ g : ℝ → ℝ,
      LipschitzOnWith 64 g Set.univ ∧
      (∀ y, |g y| ≤ 2) ∧
      ∀ y (hy : y ∈ neighborhood.sample),
        g y =
          (data.fullGrainFor y hy).normal (2 : Fin 3) /
            (data.fullGrainFor y hy).normal (0 : Fin 3) := by
  apply data.localGraphOfFubini C hcertificateOne ?_ hsigma hsigmaOne
    heta hetaSigma hCtop hCpower hPlanarSmall hrootSmall20 habsorb
  intro y hy z hz _hslice
  let grain := data.fullGrainFor y hy
  refine ⟨scalarProjection
      (globalGrainDirection (current.grain.globalGrains.slope z))
      (horizontalSlice (data.sourceFor y hy).fullSource z),
    hglobalAD y hy z hz, ?_⟩
  rintro value ⟨point, hpoint, rfl⟩
  have hlift : point3 (point 0) (point 1) z ∈ grain.fiber.grain :=
    wz1Lemma23_mem_planarSlice_iff.mp hpoint
  have hsource := grain.fiber.grain_in_source hlift
  refine ⟨point3 (point 0) (point 1) z,
    ⟨hsource, by simp [point3]⟩, ?_⟩
  change inner ℝ (point3 (point 0) (point 1) z)
      (globalGrainDirection (current.grain.globalGrains.slope z)) =
    point 0 + current.grain.globalGrains.slope z * point 1
  rw [PiLp.inner_apply]
  simp [Fin.sum_univ_succ, globalGrainDirection, point3]

end PureWZ2Node05V4RichNeighborhoodFullGrainData

end Kakeya.Assouad

end
