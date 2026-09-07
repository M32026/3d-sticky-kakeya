import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Node05V4RichJointHeightBlockResidue
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.OrdinaryPaperOrderReentryTrace

/-!
# Aggregate the selected joint-height block lifts

The mod-64 selected whole-cell lifts are united carrierwise on the unchanged
current source family.  Cubicality and source containment are inherited
without reindexing or changing any block witness.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

structure PureWZ2Node05V4RichJointAggregatedShadingData
    {capability : PureWZ2PropStickyCapability}
    {sigma inputLoss delta rho stickyLoss eta finalLoss : ℝ}
    {schedule : PureWZ2Node05V4RichSecondCallSchedule sigma stickyLoss}
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
    {B₀ threshold : ENNReal}
    {hbridge : PureWZ2PaperADBridgeStatement}
    {projection :
      PureWZ2SourceHorizontalProjectionThreshold sigma finalLoss}
    {family : PureWZ2Node05V4RichJointBlockFamily
      (eta := eta) pullback B₀ threshold hbridge projection}
    (residue : PureWZ2Node05V4RichJointBlockResidueData family) where
  shading : WZ1PaperTubeShading current.grain.family
  carrier_eq : ∀ index,
    shading.carrier index =
      ⋃ heightIndex ∈ residue.selectedBlocks,
        (family.lift heightIndex).shading.carrier index
  subshading_current :
    PureWZ2PaperIsSubshading shading current.grain.shading
  whole_cells : WZ1PaperIsCubicalShading shading
  union_eq :
    shading.union =
      ⋃ heightIndex ∈ residue.selectedBlocks,
        (family.lift heightIndex).shading.union
  block_subshading :
    ∀ heightIndex ∈ residue.selectedBlocks,
      PureWZ2PaperIsSubshading
        (family.lift heightIndex).shading shading

structure PureWZ2Node05V4RichJointAggregatedGeometryData
    {capability : PureWZ2PropStickyCapability}
    {sigma inputLoss delta rho stickyLoss eta finalLoss : ℝ}
    {schedule : PureWZ2Node05V4RichSecondCallSchedule sigma stickyLoss}
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
    {B₀ threshold : ENNReal}
    {hbridge : PureWZ2PaperADBridgeStatement}
    {projection :
      PureWZ2SourceHorizontalProjectionThreshold sigma finalLoss}
    {family : PureWZ2Node05V4RichJointBlockFamily
      (eta := eta) pullback B₀ threshold hbridge projection}
    {residue : PureWZ2Node05V4RichJointBlockResidueData family}
    (aggregated : PureWZ2Node05V4RichJointAggregatedShadingData residue) where
  scale : ℝ := 1280 * rho
  scale_eq : scale = 1280 * rho
  trapezoids : Finset WZ1VerticalTrapezoid :=
    residue.selectedBlocks.image fun heightIndex =>
      (family.trapezoid heightIndex).trapezoid
  trapezoids_eq :
    trapezoids = residue.selectedBlocks.image fun heightIndex =>
      (family.trapezoid heightIndex).trapezoid
  trapezoids_nonempty : trapezoids.Nonempty
  height_eq :
    ∀ trapezoid ∈ trapezoids, trapezoid.height = scale
  slope_bound :
    ∀ trapezoid ∈ trapezoids, |trapezoid.slope| ≤ 2
  length_bounds :
    ∀ trapezoid ∈ trapezoids,
      Real.rpow scale (1 / 2 + finalLoss) ≤ trapezoid.length ∧
        trapezoid.length ≤ Real.sqrt scale
  separated_cores :
    ∀ trapezoid ∈ trapezoids,
      ∀ other ∈ trapezoids, trapezoid ≠ other →
        ∀ z ∈ trapezoid.core, ∀ w ∈ other.core,
          Real.sqrt scale ≤ |z - w|
  slope_approximation :
    ∀ trapezoid ∈ trapezoids,
      ∀ z ∈ trapezoid.core,
        horizontalSlice aggregated.shading.union z ≠ ∅ →
          |current.grain.globalGrains.slope z - trapezoid.affine z| ≤ scale
  active_height_coverage :
    ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      horizontalSlice aggregated.shading.union z ≠ ∅ →
        ∃ trapezoid ∈ trapezoids, z ∈ trapezoid.core

namespace PureWZ2Node05V4RichJointBlockResidueData

variable
    {capability : PureWZ2PropStickyCapability}
    {sigma inputLoss delta rho stickyLoss eta finalLoss : ℝ}
    {schedule : PureWZ2Node05V4RichSecondCallSchedule sigma stickyLoss}
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
    {B₀ threshold : ENNReal}
    {hbridge : PureWZ2PaperADBridgeStatement}
    {projection :
      PureWZ2SourceHorizontalProjectionThreshold sigma finalLoss}
    {family : PureWZ2Node05V4RichJointBlockFamily
      (eta := eta) pullback B₀ threshold hbridge projection}
    (residue : PureWZ2Node05V4RichJointBlockResidueData family)

theorem aggregateShading :
    Nonempty (PureWZ2Node05V4RichJointAggregatedShadingData residue) := by
  let carrier : Fin (wz1PaperBodyFamily current.grain.family).card →
      Set Point3 := fun index =>
    ⋃ heightIndex ∈ residue.selectedBlocks,
      (family.lift heightIndex).shading.carrier index
  have hcarrierMeas : ∀ index, MeasurableSet (carrier index) := by
    intro index
    exact MeasurableSet.biUnion
      residue.selectedBlocks.finite_toSet.countable
      (fun heightIndex _ =>
        (family.lift heightIndex).shading.measurable_carrier index)
  let shading : WZ1PaperTubeShading current.grain.family :=
    { carrier := carrier
      measurable_carrier := hcarrierMeas
      subset_body := by
        intro index point hpoint
        rcases Set.mem_iUnion₂.mp hpoint with
          ⟨heightIndex, _hheightIndex, hblock⟩
        exact (family.lift heightIndex).shading.subset_body index hblock }
  have hsub :
      PureWZ2PaperIsSubshading shading current.grain.shading := by
    intro index point hpoint
    rcases Set.mem_iUnion₂.mp hpoint with
      ⟨heightIndex, _hheightIndex, hblock⟩
    exact (family.lift heightIndex).subshading_current index hblock
  have hwhole : WZ1PaperIsCubicalShading shading := by
    intro index point hpoint other hother
    rcases Set.mem_iUnion₂.mp hpoint with
      ⟨heightIndex, hheightIndex, hblock⟩
    exact Set.mem_iUnion₂.mpr
      ⟨heightIndex, hheightIndex,
        (family.lift heightIndex).whole_cells index point hblock hother⟩
  have hunion :
      shading.union =
        ⋃ heightIndex ∈ residue.selectedBlocks,
          (family.lift heightIndex).shading.union := by
    apply Set.Subset.antisymm
    · rintro point ⟨index, hpoint⟩
      rcases Set.mem_iUnion₂.mp hpoint with
        ⟨heightIndex, hheightIndex, hblock⟩
      exact Set.mem_iUnion₂.mpr
        ⟨heightIndex, hheightIndex, ⟨index, hblock⟩⟩
    · intro point hpoint
      rcases Set.mem_iUnion₂.mp hpoint with
        ⟨heightIndex, hheightIndex, index, hblock⟩
      exact ⟨index, Set.mem_iUnion₂.mpr
        ⟨heightIndex, hheightIndex, hblock⟩⟩
  exact ⟨{
    shading := shading
    carrier_eq := fun _ => rfl
    subshading_current := hsub
    whole_cells := hwhole
    union_eq := hunion
    block_subshading := by
      intro heightIndex hheightIndex index point hpoint
      exact Set.mem_iUnion₂.mpr
        ⟨heightIndex, hheightIndex, hpoint⟩
  }⟩

theorem selectedBlock_index_gap
    {first second : {heightIndex //
      heightIndex ∈ pureWZ2Node05V4RichHeavySlabs pullback}}
    (hfirst : first ∈ residue.selectedBlocks)
    (hsecond : second ∈ residue.selectedBlocks)
    (hne : first ≠ second) :
    (64 : ℤ) ≤ |first.1.1 - second.1.1| := by
  have hfirstResidue := residue.block_residue first hfirst
  have hsecondResidue := residue.block_residue second hsecond
  have hindexNe : first.1.1 ≠ second.1.1 := by
    intro heq
    apply hne
    apply Subtype.ext
    apply Subtype.ext
    exact heq
  have hmod :
      (first.1.1 - second.1.1) % (64 : ℤ) = 0 := by
    rw [Int.sub_emod, hfirstResidue, hsecondResidue]
    simp
  exact Int.le_abs_of_dvd (sub_ne_zero.mpr hindexNe)
    (by rwa [Int.dvd_iff_emod_eq_zero])

theorem selectedBlock_union_disjoint
    {first second : {heightIndex //
      heightIndex ∈ pureWZ2Node05V4RichHeavySlabs pullback}}
    (hfirst : first ∈ residue.selectedBlocks)
    (hsecond : second ∈ residue.selectedBlocks)
    (hne : first ≠ second) :
    Disjoint (family.lift first).shading.union
      (family.lift second).shading.union := by
  rw [Set.disjoint_left]
  intro point hpointFirst hpointSecond
  have hsliceFirst :
      horizontalSlice (family.lift first).shading.union
        (point (2 : Fin 3)) ≠ ∅ := by
    exact Set.nonempty_iff_ne_empty.mp
      ⟨point, hpointFirst, rfl⟩
  have hsliceSecond :
      horizontalSlice (family.lift second).shading.union
        (point (2 : Fin 3)) ≠ ∅ := by
    exact Set.nonempty_iff_ne_empty.mp
      ⟨point, hpointSecond, rfl⟩
  have hheightFirst :=
    (family.trapezoid first).active_height_coverage
      (point (2 : Fin 3)) hsliceFirst
  have hheightSecond :=
    (family.trapezoid second).active_height_coverage
      (point (2 : Fin 3)) hsliceSecond
  rw [(family.trapezoid first).core_eq] at hheightFirst
  rw [(family.trapezoid second).core_eq] at hheightSecond
  have hgap := residue.selectedBlock_index_gap hfirst hsecond hne
  have hgapReal :
      (64 : ℝ) ≤
        |(first.1.1 : ℝ) - (second.1.1 : ℝ)| := by
    exact_mod_cast hgap
  have hrho : 0 < rho := by
    rw [← pullback.rhoRequested_eq]
    exact twoScale.first.publicSticky.coarse_extremal.delta_pos
  have hrhoOne : rho ≤ 1 := by
    rw [← pullback.rhoRequested_eq]
    exact rhoRequested.property.2
  have hroot : 0 < Real.sqrt rho := Real.sqrt_pos.mpr hrho
  have hrhoRoot : rho ≤ Real.sqrt rho := by
    nlinarith [Real.sq_sqrt hrho.le, Real.sqrt_nonneg rho]
  have hdeltaRho : delta ≤ rho := by
    rw [← pullback.rhoRequested_eq]
    exact rhoRequested.property.1
  have hdeltaRoot : delta ≤ Real.sqrt rho := by
    exact hdeltaRho.trans hrhoRoot
  rcases lt_or_gt_of_ne
      (show (first.1.1 : ℝ) ≠ (second.1.1 : ℝ) by
        exact_mod_cast (show first.1.1 ≠ second.1.1 by
          intro heq
          apply hne
          apply Subtype.ext
          apply Subtype.ext
          exact heq)) with hlt | hgt
  · have horder :
        (64 : ℝ) ≤ (second.1.1 : ℝ) - (first.1.1 : ℝ) := by
      rw [abs_of_nonpos (by linarith)] at hgapReal
      linarith
    nlinarith [hheightFirst.2, hheightSecond.1]
  · have horder :
        (64 : ℝ) ≤ (first.1.1 : ℝ) - (second.1.1 : ℝ) := by
      rw [abs_of_nonneg (by linarith)] at hgapReal
      linarith
    nlinarith [hheightSecond.2, hheightFirst.1]

theorem mass_eq_sum
    (aggregated : PureWZ2Node05V4RichJointAggregatedShadingData residue) :
    aggregated.shading.mass =
      ∑ heightIndex ∈ residue.selectedBlocks,
        (family.lift heightIndex).shading.mass := by
  unfold Kakeya.Streamlined.Shading.mass
  calc
    (∑ index,
        volume (aggregated.shading.carrier index)) =
        ∑ index, ∑ heightIndex ∈ residue.selectedBlocks,
          volume ((family.lift heightIndex).shading.carrier index) := by
      apply Finset.sum_congr rfl
      intro index _
      rw [aggregated.carrier_eq]
      exact MeasureTheory.measure_biUnion_finset
        (fun first hfirst second hsecond hne => by
          have hfirstSub :
              (family.lift first).shading.carrier index ⊆
                (family.lift first).shading.union :=
            fun point hpoint => ⟨index, hpoint⟩
          have hsecondSub :
              (family.lift second).shading.carrier index ⊆
                (family.lift second).shading.union :=
            fun point hpoint => ⟨index, hpoint⟩
          exact (residue.selectedBlock_union_disjoint
            hfirst hsecond hne).mono hfirstSub hsecondSub)
        (fun heightIndex _ =>
          (family.lift heightIndex).shading.measurable_carrier index)
    _ = ∑ heightIndex ∈ residue.selectedBlocks,
          ∑ index, volume ((family.lift heightIndex).shading.carrier index) := by
      rw [Finset.sum_comm]
    _ = ∑ heightIndex ∈ residue.selectedBlocks,
        (family.lift heightIndex).shading.mass := by
      rfl

theorem total_lift_mass_le
    (aggregated : PureWZ2Node05V4RichJointAggregatedShadingData residue) :
    (∑ heightIndex, (family.lift heightIndex).shading.mass) ≤
      64 * aggregated.shading.mass := by
  rw [mass_eq_sum residue aggregated]
  exact residue.mass_retention

theorem geometry
    (aggregated : PureWZ2Node05V4RichJointAggregatedShadingData residue) :
    Nonempty (PureWZ2Node05V4RichJointAggregatedGeometryData aggregated) := by
  let scale := 1280 * rho
  let trapezoids := residue.selectedBlocks.image fun heightIndex =>
    (family.trapezoid heightIndex).trapezoid
  have hscaleBlock :
      ∀ heightIndex,
        (family.trapezoid heightIndex).scale = scale := by
    intro heightIndex
    rw [(family.trapezoid heightIndex).scale_eq,
      (family.prepared heightIndex).graphScale_eq]
    dsimp only [scale]
    ring
  have hseparated :
      ∀ first ∈ residue.selectedBlocks,
        ∀ second ∈ residue.selectedBlocks, first ≠ second →
          ∀ z ∈ (family.trapezoid first).trapezoid.core,
            ∀ w ∈ (family.trapezoid second).trapezoid.core,
              Real.sqrt scale ≤ |z - w| := by
    intro first hfirst second hsecond hne z hz w hw
    rw [(family.trapezoid first).core_eq] at hz
    rw [(family.trapezoid second).core_eq] at hw
    have hgap := residue.selectedBlock_index_gap hfirst hsecond hne
    have hgapReal :
        (64 : ℝ) ≤
          |(first.1.1 : ℝ) - (second.1.1 : ℝ)| := by
      exact_mod_cast hgap
    have hrho : 0 < rho := by
      rw [← pullback.rhoRequested_eq]
      exact twoScale.first.publicSticky.coarse_extremal.delta_pos
    have hrhoOne : rho ≤ 1 := by
      rw [← pullback.rhoRequested_eq]
      exact rhoRequested.property.2
    have hrhoRoot : rho ≤ Real.sqrt rho := by
      nlinarith [Real.sq_sqrt hrho.le, Real.sqrt_nonneg rho]
    have hdeltaRoot : delta ≤ Real.sqrt rho := by
      exact (show delta ≤ rho by
        rw [← pullback.rhoRequested_eq]
        exact rhoRequested.property.1).trans hrhoRoot
    have hsqrtScale :
        Real.sqrt scale = 16 * Real.sqrt 5 * Real.sqrt rho := by
      dsimp only [scale]
      rw [show (1280 : ℝ) = 256 * 5 by norm_num,
        Real.sqrt_mul (by norm_num), Real.sqrt_mul (by norm_num)]
      norm_num
    have hsqrtFive : Real.sqrt 5 < 3 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5),
        Real.sqrt_nonneg (5 : ℝ)]
    rcases lt_or_gt_of_ne
        (show (first.1.1 : ℝ) ≠ (second.1.1 : ℝ) by
          exact_mod_cast (show first.1.1 ≠ second.1.1 by
            intro heq
            apply hne
            apply Subtype.ext
            apply Subtype.ext
            exact heq)) with hlt | hgt
    · have horder :
          (64 : ℝ) ≤ (second.1.1 : ℝ) - (first.1.1 : ℝ) := by
        rw [abs_of_nonpos (by linarith)] at hgapReal
        linarith
      rw [hsqrtScale, abs_of_nonpos (by
        nlinarith [hz.2, hw.1])]
      nlinarith [hz.2, hw.1, Real.sqrt_pos.mpr hrho]
    · have horder :
          (64 : ℝ) ≤ (first.1.1 : ℝ) - (second.1.1 : ℝ) := by
        rw [abs_of_nonneg (by linarith)] at hgapReal
        linarith
      rw [hsqrtScale, abs_of_nonneg (by
        nlinarith [hz.1, hw.2])]
      nlinarith [hz.1, hw.2, Real.sqrt_pos.mpr hrho]
  exact ⟨{
    scale := scale
    scale_eq := rfl
    trapezoids := trapezoids
    trapezoids_eq := rfl
    trapezoids_nonempty :=
      residue.selectedBlocks_nonempty.image fun heightIndex =>
        (family.trapezoid heightIndex).trapezoid
    height_eq := by
      intro trapezoid htrapezoid
      rcases Finset.mem_image.mp htrapezoid with
        ⟨heightIndex, _hheightIndex, rfl⟩
      rw [(family.trapezoid heightIndex).height_eq,
        hscaleBlock heightIndex]
    slope_bound := by
      intro trapezoid htrapezoid
      rcases Finset.mem_image.mp htrapezoid with
        ⟨heightIndex, _hheightIndex, rfl⟩
      exact (family.trapezoid heightIndex).slope_bound
    length_bounds := by
      intro trapezoid htrapezoid
      rcases Finset.mem_image.mp htrapezoid with
        ⟨heightIndex, _hheightIndex, rfl⟩
      simpa [hscaleBlock heightIndex] using
        (family.trapezoid heightIndex).length_bounds
    separated_cores := by
      intro trapezoid htrapezoid other hother hne z hz w hw
      rcases Finset.mem_image.mp htrapezoid with
        ⟨first, hfirst, hfirstEq⟩
      rcases Finset.mem_image.mp hother with
        ⟨second, hsecond, hsecondEq⟩
      subst trapezoid
      subst other
      have hblockNe : first ≠ second := by
        intro heq
        subst second
        exact hne rfl
      exact hseparated first hfirst second hsecond hblockNe z hz w hw
    slope_approximation := by
      intro trapezoid htrapezoid z hz hslice
      rcases Finset.mem_image.mp htrapezoid with
        ⟨heightIndex, hheightIndex, rfl⟩
      have hblockSlice :
          horizontalSlice (family.lift heightIndex).shading.union z ≠ ∅ := by
        rcases Set.nonempty_iff_ne_empty.mpr hslice with
          ⟨point, hpoint, hpointHeight⟩
        rw [aggregated.union_eq] at hpoint
        rcases Set.mem_iUnion₂.mp hpoint with
          ⟨sourceIndex, hsourceIndex, hsourcePoint⟩
        have hsourceCore :=
          (family.trapezoid sourceIndex).active_height_coverage z
            (Set.nonempty_iff_ne_empty.mp
              ⟨point, hsourcePoint, hpointHeight⟩)
        by_cases heq : sourceIndex = heightIndex
        · subst sourceIndex
          exact Set.nonempty_iff_ne_empty.mp
            ⟨point, hsourcePoint, hpointHeight⟩
        · have hgap := hseparated sourceIndex hsourceIndex
            heightIndex hheightIndex heq z hsourceCore z hz
          exfalso
          have hscalePos : 0 < Real.sqrt scale := by
            apply Real.sqrt_pos.2
            dsimp only [scale]
            have hrho : 0 < rho := by
              rw [← pullback.rhoRequested_eq]
              exact twoScale.first.publicSticky.coarse_extremal.delta_pos
            positivity
          have hgapZero : Real.sqrt scale ≤ 0 := by simpa using hgap
          exact (not_le_of_gt hscalePos) hgapZero
      simpa [hscaleBlock heightIndex] using
        (family.trapezoid heightIndex).slope_approximation
          z hz hblockSlice
    active_height_coverage := by
      intro z _hz hslice
      rcases Set.nonempty_iff_ne_empty.mpr hslice with
        ⟨point, hpoint, hpointHeight⟩
      rw [aggregated.union_eq] at hpoint
      rcases Set.mem_iUnion₂.mp hpoint with
        ⟨heightIndex, hheightIndex, hblockPoint⟩
      let trapezoid := (family.trapezoid heightIndex).trapezoid
      refine ⟨trapezoid, Finset.mem_image.mpr
        ⟨heightIndex, hheightIndex, rfl⟩, ?_⟩
      exact (family.trapezoid heightIndex).active_height_coverage z
        (Set.nonempty_iff_ne_empty.mp
          ⟨point, hblockPoint, hpointHeight⟩)
  }⟩

noncomputable def toLiteralGeometry
    {aggregated :
      PureWZ2Node05V4RichJointAggregatedShadingData residue}
    (geometry : PureWZ2Node05V4RichJointAggregatedGeometryData
      (rho := rho) (eta := eta) (finalLoss := finalLoss)
      (schedule := schedule) (current := current)
      (rhoRequested := rhoRequested) (inputLossLe := inputLossLe)
      (sqrtRequested := sqrtRequested) (twoScale := twoScale)
      (pullback := pullback) (B₀ := B₀) (threshold := threshold)
      (hbridge := hbridge) (projection := projection)
      (family := family) (residue := residue) aggregated) :
    PureWZ2LiteralCurrentSourceOneScaleGeometry
      current.grain aggregated.shading finalLoss geometry.scale := by
  have hrho : 0 < rho := by
    rw [← pullback.rhoRequested_eq]
    exact twoScale.first.publicSticky.coarse_extremal.delta_pos
  have hdeltaRho : delta ≤ rho := by
    rw [← pullback.rhoRequested_eq]
    exact rhoRequested.property.1
  have hscalePos : 0 < geometry.scale := by
    rw [geometry.scale_eq]
    positivity
  have hscaleOne : geometry.scale ≤ 1 := by
    rcases residue.selectedBlocks_nonempty with
      ⟨heightIndex, hheightIndex⟩
    have hblock := (family.trapezoid heightIndex).scale_le_one
    rw [(family.trapezoid heightIndex).scale_eq,
      (family.prepared heightIndex).graphScale_eq] at hblock
    rw [geometry.scale_eq]
    simpa only [show 5 * (256 * rho) = 1280 * rho by ring] using hblock
  exact {
    rho_pos := hscalePos
    delta_le_rho := by
      rw [geometry.scale_eq]
      nlinarith
    rho_le_one := hscaleOne
    trapezoids := geometry.trapezoids
    trapezoids_nonempty := geometry.trapezoids_nonempty
    height_eq := geometry.height_eq
    slope_bound := geometry.slope_bound
    length_bounds := geometry.length_bounds
    separated_cores := geometry.separated_cores
    slope_approximation := geometry.slope_approximation
    active_height_coverage := geometry.active_height_coverage
  }

/-- Weaken only the loss parameter of the assembled literal geometry.  All
same-witness shading, trapezoids, and affine data remain unchanged. -/
noncomputable def toLiteralGeometryMono
    {aggregated :
      PureWZ2Node05V4RichJointAggregatedShadingData residue}
    (geometry : PureWZ2Node05V4RichJointAggregatedGeometryData
      (rho := rho) (eta := eta) (finalLoss := finalLoss)
      (schedule := schedule) (current := current)
      (rhoRequested := rhoRequested) (inputLossLe := inputLossLe)
      (sqrtRequested := sqrtRequested) (twoScale := twoScale)
      (pullback := pullback) (B₀ := B₀) (threshold := threshold)
      (hbridge := hbridge) (projection := projection)
      (family := family) (residue := residue) aggregated)
    {requestedLoss : ℝ} (hloss : finalLoss ≤ requestedLoss) :
    PureWZ2LiteralCurrentSourceOneScaleGeometry
      current.grain aggregated.shading requestedLoss geometry.scale := by
  let base := PureWZ2Node05V4RichJointBlockResidueData.toLiteralGeometry
    residue geometry
  exact {
    rho_pos := base.rho_pos
    delta_le_rho := base.delta_le_rho
    rho_le_one := base.rho_le_one
    trapezoids := base.trapezoids
    trapezoids_nonempty := base.trapezoids_nonempty
    height_eq := base.height_eq
    slope_bound := base.slope_bound
    length_bounds := by
      intro trapezoid htrapezoid
      have hbase := base.length_bounds trapezoid htrapezoid
      have hpower : Real.rpow geometry.scale (1 / 2 + requestedLoss) ≤
          Real.rpow geometry.scale (1 / 2 + finalLoss) :=
        Real.rpow_le_rpow_of_exponent_ge base.rho_pos base.rho_le_one
          (by linarith)
      exact ⟨hpower.trans hbase.1, hbase.2⟩
    separated_cores := base.separated_cores
    slope_approximation := base.slope_approximation
    active_height_coverage := base.active_height_coverage
  }

end PureWZ2Node05V4RichJointBlockResidueData

end Kakeya.Assouad

end
