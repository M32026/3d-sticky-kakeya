import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.PureHierarchyMultiplicityRefinement
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.PureHierarchyVolumeRetention
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.AnchoredHierarchyAssembly
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.ActiveCellShadowGrains
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.PaperExactSliceSlabVolume

/-!
# Paper popularity assembly for the Pure WZ2 hierarchy

This is the post-iteration part of [16, Corollary 5.6].  A quantitative
constant-multiplicity band is first passed through the supplied same-extremizer
Node-4 refinement.  The resulting volume lower bound is then used for the
multi-scale popularity pruning, compactification, and endpoint reanchoring.

The final height-pruned shading is intentionally not asserted to be cubical.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

/-- The slab constant furnished by exact horizontal-slice AD on the restored
Node-4 refinement. -/
def pureWZ2HierarchySlabConstant
    (delta sigma targetLoss : ℝ) : ENNReal :=
  32 * (10 * Kakeya.realRpowENN delta (-targetLoss)) *
    Kakeya.realRpowENN delta sigma

/-- A quantitative multiplicity band together with the dependent Node-4
refinement that restores the critical volume lower bound on that exact band. -/
structure PureWZ2RestoredHierarchyData
    {sigma inputLoss delta : ℝ}
    (source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta)
    (terminalLoss hierarchyLoss selectionLoss targetLoss : ℝ) where
  band : PureWZ2MultiplicityRefinedHierarchyData
    source terminalLoss hierarchyLoss selectionLoss
  refined : PureWZ2GrainRefinementData band.shading sigma targetLoss
  refined_slope_eq :
    refined.globalGrains.slope = source.globalGrains.slope

/-- The quantitative information retained by the ordinary Corollary-5.6
popularity argument.  Compactification need not preserve the lower half of a
constant-multiplicity band, so the output records exactly the two facts that
survive: a pointwise upper cap and indexed shaded-mass retention. -/
structure PureWZ2QuantitativeLocallyLinearHierarchyData
    {sigma inputLoss delta : ℝ}
    (source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta)
    (finalLoss hierarchyLoss densityLoss : ℝ) where
  hierarchy : PureWZ2LocallyLinearHierarchyData
    source finalLoss hierarchyLoss
  multiplicity : ℕ
  multiplicity_pos : 0 < multiplicity
  pointMultiplicity_upper :
    ∀ point, hierarchy.shading.pointMultiplicity point ≤ 2 * multiplicity
  mass_retention :
    ENNReal.ofReal (1 / 6) *
        (Kakeya.realRpowENN delta densityLoss *
          (wz1PaperBodyFamily source.family).mass) ≤
      hierarchy.shading.mass

namespace PureWZ2MultiplicityRefinedHierarchyData

/-- The quantitative band is a cropped extremizer at its selection loss.
This is precisely the input expected by the same-extremizer Node-4 producer. -/
theorem toCroppedExtremal
    {sigma inputLoss delta terminalLoss hierarchyLoss selectionLoss : ℝ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    (data : PureWZ2MultiplicityRefinedHierarchyData
      source terminalLoss hierarchyLoss selectionLoss)
    (hloss : terminalLoss ≤ selectionLoss) :
    WZ2PaperCroppedIsExtremal
      sigma selectionLoss source.family data.shading := by
  have hbase := data.iterated.extremal.mono_loss hloss
  exact
    { delta_pos := hbase.delta_pos
      delta_le_one := hbase.delta_le_one
      nonempty := hbase.nonempty
      cwa_nearby_scales := hbase.cwa_nearby_scales
      cubical := data.whole_cells
      dense := data.mass_retention
      volume_upper :=
        (measure_mono data.subshading_iterated.union_subset).trans
          hbase.volume_upper }

/-- Apply the dependent Node-4 producer to the final quantitative
multiplicity band.  This is the same-extremizer restoration step immediately
before the popularity pruning in Corollary 5.6. -/
theorem restoreWithGrainProducer
    {sigma inputLoss delta terminalLoss hierarchyLoss selectionLoss
      targetLoss : ℝ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    (data : PureWZ2MultiplicityRefinedHierarchyData
      source terminalLoss hierarchyLoss selectionLoss)
    (hterminalSelection : terminalLoss ≤ selectionLoss)
    (grainProducer :
      ∀ targetFamily : Kakeya.Streamlined.TubeFamily delta,
        ∀ targetShading : WZ1PaperTubeShading targetFamily,
          WZ1PaperIsLineClass targetFamily →
          WZ2PaperCroppedIsExtremal
              sigma selectionLoss targetFamily targetShading →
            Nonempty
              (PureWZ2GrainRefinementData
                targetShading sigma targetLoss))
    (refinedSlope : ∀ refinement : PureWZ2GrainRefinementData
        data.shading sigma targetLoss,
      refinement.globalGrains.slope = source.globalGrains.slope) :
    Nonempty
      (PureWZ2RestoredHierarchyData source terminalLoss hierarchyLoss
        selectionLoss targetLoss) := by
  rcases grainProducer source.family data.shading source.line_class
      (data.toCroppedExtremal hterminalSelection) with ⟨refined⟩
  exact ⟨{ band := data
           refined := refined
           refined_slope_eq := refinedSlope refined }⟩

end PureWZ2MultiplicityRefinedHierarchyData

namespace PureWZ2RestoredHierarchyData

/-- Keep the constant-multiplicity band on precisely the spatial union retained
by the dependent Node-4 refinement.  This is the common spatial restriction
used in the proof of [16, Corollary 5.6]. -/
noncomputable def shading
    {sigma inputLoss delta terminalLoss hierarchyLoss selectionLoss
      targetLoss : ℝ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    (data : PureWZ2RestoredHierarchyData source terminalLoss hierarchyLoss
      selectionLoss targetLoss) :
    WZ1PaperTubeShading source.family :=
  spatialRestrictionToUnionGeneric data.band.shading data.refined.shading

/-- The restored shading remains a carrierwise refinement of the
constant-multiplicity band. -/
theorem shading_subshading_band
    {sigma inputLoss delta terminalLoss hierarchyLoss selectionLoss
      targetLoss : ℝ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    (data : PureWZ2RestoredHierarchyData source terminalLoss hierarchyLoss
      selectionLoss targetLoss) :
    PureWZ2PaperIsSubshading data.shading data.band.shading :=
  spatialRestrictionToUnionGeneric_subshading _ _

/-- The common restriction has exactly the Node-4 refined union. -/
theorem shading_union_eq_refined
    {sigma inputLoss delta terminalLoss hierarchyLoss selectionLoss
      targetLoss : ℝ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    (data : PureWZ2RestoredHierarchyData source terminalLoss hierarchyLoss
      selectionLoss targetLoss) :
    data.shading.union = data.refined.shading.union :=
  spatialRestrictionToUnionGeneric_union_eq data.refined.subshading

/-- Hence the restored shading carries the critical volume lower bound supplied
by Node 4, without changing Node 4's public interface. -/
theorem shading_volume_lower
    {sigma inputLoss delta terminalLoss hierarchyLoss selectionLoss
      targetLoss : ℝ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    (data : PureWZ2RestoredHierarchyData source terminalLoss hierarchyLoss
      selectionLoss targetLoss) :
    Kakeya.realRpowENN delta (sigma + targetLoss) ≤
      MeasureTheory.volume data.shading.union := by
  rw [data.shading_union_eq_refined]
  exact data.refined.volume_lower

/-- Point multiplicity is exactly that of the selected band on the restored
union. -/
theorem shading_pointMultiplicity_eq
    {sigma inputLoss delta terminalLoss hierarchyLoss selectionLoss
      targetLoss : ℝ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    (data : PureWZ2RestoredHierarchyData source terminalLoss hierarchyLoss
      selectionLoss targetLoss)
    {point : Point3} (hpoint : point ∈ data.shading.union) :
    data.shading.pointMultiplicity point =
      data.band.shading.pointMultiplicity point :=
  spatialRestrictionToUnionGeneric_pointMultiplicity_eq hpoint

/-- In particular, the Node-4 union is restored with the quantitative
constant-multiplicity band intact. -/
theorem shading_constantMultiplicity
    {sigma inputLoss delta terminalLoss hierarchyLoss selectionLoss
      targetLoss : ℝ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    (data : PureWZ2RestoredHierarchyData source terminalLoss hierarchyLoss
      selectionLoss targetLoss) :
    data.shading.HasConstantMultiplicity data.band.multiplicity
      (2 * data.band.multiplicity) :=
  spatialRestrictionToUnionGeneric_constantMultiplicity
    data.band.constant_multiplicity

/-- Both inputs consist of whole delta-cells, so their common spatial
restriction is cubical before the later height-popularity pruning. -/
theorem shading_cubical
    {sigma inputLoss delta terminalLoss hierarchyLoss selectionLoss
      targetLoss : ℝ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    (data : PureWZ2RestoredHierarchyData source terminalLoss hierarchyLoss
      selectionLoss targetLoss) :
    WZ1PaperIsCubicalShading data.shading :=
  spatialRestrictionToUnionGeneric_cubical
    data.band.whole_cells data.refined.cubical

/-- The restored shading is still a refinement of the original hierarchy
source. -/
theorem shading_subshading_source
    {sigma inputLoss delta terminalLoss hierarchyLoss selectionLoss
      targetLoss : ℝ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    (data : PureWZ2RestoredHierarchyData source terminalLoss hierarchyLoss
      selectionLoss targetLoss) :
    PureWZ2PaperIsSubshading data.shading source.shading := by
  intro index
  exact (data.shading_subshading_band index).trans
    (data.band.subshading_source index)

/-- Execute the popularity, compactification, and endpoint-anchoring steps of
Corollary 5.6.  The numerical hypotheses are exactly the small-scale
inequalities discharged by the outer parameter schedule. -/
theorem toQuantitativeLocallyLinearHierarchy
    {sigma inputLoss delta terminalLoss hierarchyLoss selectionLoss
      targetLoss : ℝ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    (data : PureWZ2RestoredHierarchyData source terminalLoss hierarchyLoss
      selectionLoss targetLoss)
    (hbridge : PureWZ2PaperADBridgeStatement)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hhierarchyLoss : 0 < hierarchyLoss)
    (hterminalHierarchy : terminalLoss ≤ hierarchyLoss)
    (htargetHierarchy : targetLoss ≤ hierarchyLoss)
    (htargetLevelZero : targetLoss ≤
      hierarchyLoss / (4 * (data.band.iterated.levelCount : ℝ)))
    (hdeltaStrict : delta < 1)
    (hgeometric : Real.rpow delta
      (hierarchyLoss / (data.band.iterated.levelCount : ℝ)) < 1 / 9)
    (hlevelZero :
      pureWZ2HierarchySlabConstant delta sigma targetLoss *
          ENNReal.ofReal (12 * Real.rpow delta
            (hierarchyLoss / (data.band.iterated.levelCount : ℝ))) <
        Kakeya.realRpowENN delta
          (sigma + hierarchyLoss /
            (4 * (data.band.iterated.levelCount : ℝ))))
    (hremoved :
      pureWZ2HierarchySlabConstant delta sigma targetLoss *
          ENNReal.ofReal
            (12 * ∑ level : Fin data.band.iterated.levelCount,
              Real.rpow
                (wz1Corollary26Scale delta
                  data.band.iterated.levelCount level) hierarchyLoss) ≤
        ENNReal.ofReal (1 / 3) *
          MeasureTheory.volume data.refined.shading.union)
    (hfinalVolume :
      Kakeya.realRpowENN delta (sigma + hierarchyLoss) <
        ENNReal.ofReal (2 / 3) *
          Kakeya.realRpowENN delta (sigma + targetLoss)) :
    Nonempty (PureWZ2QuantitativeLocallyLinearHierarchyData
      source hierarchyLoss hierarchyLoss targetLoss) := by
  let N := data.band.iterated.levelCount
  have hNpos : 0 < N := by
    exact lt_of_lt_of_le (by norm_num) data.band.iterated.levelCount_two
  let Z := data.shading
  let rawTrapezoids : Fin N → Finset WZ1VerticalTrapezoid :=
    data.band.trapezoids
  let L : Fin N → ℝ := fun level =>
    Real.rpow (wz1Corollary26Scale delta N level)
      (1 / 2 + hierarchyLoss)
  let Amax : ENNReal :=
    pureWZ2HierarchySlabConstant delta sigma targetLoss
  have hdelta := data.refined.extremal.delta_pos
  have hdeltaOne := data.refined.extremal.delta_le_one
  have hZBand : PureWZ2PaperIsSubshading Z data.band.shading :=
    data.shading_subshading_band
  have hZIterated :
      PureWZ2PaperIsSubshading Z data.band.iterated.shading :=
    fun index => (hZBand index).trans (data.band.subshading_iterated index)
  have hZSource : PureWZ2PaperIsSubshading Z source.shading :=
    data.shading_subshading_source
  have hLnonneg : ∀ level, 0 ≤ L level := by
    intro level
    exact Real.rpow_nonneg
      (Real.rpow_pos_of_pos hdelta _).le _
  have hLeq : ∀ level, L level =
      Real.rpow (wz1Corollary26Scale delta N level)
        (1 / 2 + hierarchyLoss) := fun _ => rfl
  have hZheight : ∀ point ∈ Z.union,
      point 2 ∈ Set.Icc (-1 : ℝ) 1 := by
    intro point hpoint
    have hbox := paperShading_subset_axisBox
      (Z := Z) hpoint
    exact abs_le.mp (by
      simpa [Kakeya.Streamlined.axisBox] using hbox.2.2)
  have hcoverage : ∀ level, ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      horizontalSlice Z.union z ≠ ∅ →
        ∃ trapezoid ∈ rawTrapezoids level, z ∈ trapezoid.core := by
    intro level z hz hactive
    have hactiveBand : horizontalSlice data.band.shading.union z ≠ ∅ := by
      apply Set.Nonempty.ne_empty
      apply Set.Nonempty.mono _ (Set.nonempty_iff_ne_empty.mpr hactive)
      intro point hpoint
      exact ⟨hZBand.union_subset hpoint.1, hpoint.2⟩
    exact data.band.active_height_coverage level z hz hactiveBand
  have hslopeApprox : ∀ level, ∀ trapezoid ∈ rawTrapezoids level,
      ∀ z ∈ trapezoid.core, horizontalSlice Z.union z ≠ ∅ →
        |data.band.sourceGlobalGrains.slope z - trapezoid.affine z| ≤
          wz1Corollary26Scale delta N level := by
    intro level trapezoid htrapezoid z hz hactive
    have hactiveBand : horizontalSlice data.band.shading.union z ≠ ∅ := by
      apply Set.Nonempty.ne_empty
      apply Set.Nonempty.mono _ (Set.nonempty_iff_ne_empty.mpr hactive)
      intro point hpoint
      exact ⟨hZBand.union_subset hpoint.1, hpoint.2⟩
    exact data.band.slope_approximation level trapezoid htrapezoid
      z hz hactiveBand
  have hslab : ∀ a b : ℝ, a ≤ b →
      volume (Z.union ∩ horizontalSlab a b) ≤
        Amax * ENNReal.ofReal (b - a) := by
    intro a b hab
    let shadow := pureWZ2ActiveCellShading data.refined.shading hdelta
    have hunion : shadow.union = data.refined.shading.union :=
      pureWZ2ActiveCellShading_union data.refined.shading hdelta
        data.refined.cubical
    have haxis : ∀ point ∈ shadow.union, ∀ coordinate : Fin 3,
        |point coordinate| ≤ 1 := by
      intro point hpoint coordinate
      have hbox : point ∈ Kakeya.Streamlined.axisBox 2 2 2 :=
        paperShading_subset_axisBox
          (Z := data.refined.shading) (by simpa [hunion] using hpoint)
      simp only [Kakeya.Streamlined.axisBox, Set.mem_setOf_eq] at hbox
      norm_num at hbox
      fin_cases coordinate <;> tauto
    have hexact : ∀ z ∈ Set.Icc (-1 : ℝ) 1,
        IsADSet1
          (scalarProjection
            (globalGrainDirection (data.refined.globalGrains.slope z))
            (horizontalSlice shadow.union z))
          delta (1 - sigma)
          (10 * Kakeya.realRpowENN delta (-targetLoss)) :=
      data.refined.globalGrains.activeCellShadow_exactAD
        hdelta data.refined.cubical hbridge
        (by
          intro z hz
          rw [data.refined_slope_eq]
          exact source.globalGrains.slope_bound z hz)
    have hraw := paper_exactSlice_slab_volume_le
      shadow haxis data.refined.globalGrains.slope
      (10 * Kakeya.realRpowENN delta (-targetLoss))
      hdelta hsigma hsigmaOne
      (ENNReal.mul_ne_top (by norm_num) (by simp [Kakeya.realRpowENN]))
      hexact hab
    rw [hunion] at hraw
    rw [← data.shading_union_eq_refined] at hraw
    simpa [Amax, pureWZ2HierarchySlabConstant, mul_assoc] using hraw
  have hlevelZeroPopular : ∃ trapezoid ∈ rawTrapezoids ⟨0, hNpos⟩,
      volumeInCoreGeneric Z trapezoid >
        Amax * ENNReal.ofReal (3 * L ⟨0, hNpos⟩) := by
    apply PureHierarchyGeneric.level0_popularity_from_volume_general_generic
      hNpos hdelta hdeltaStrict hhierarchyLoss hsigma Amax hZheight
      (fun trapezoid htrapezoid =>
        (data.band.length_bounds ⟨0, hNpos⟩ trapezoid htrapezoid).2)
      (data.band.separated_cores ⟨0, hNpos⟩)
      (hcoverage ⟨0, hNpos⟩)
      (by
        have hpower : Kakeya.realRpowENN delta
            (sigma + hierarchyLoss / (4 * (N : ℝ))) ≤
            Kakeya.realRpowENN delta (sigma + targetLoss) := by
          apply ENNReal.ofReal_mono
          exact Real.rpow_le_rpow_of_exponent_ge hdelta hdeltaOne
            (by simpa [N] using htargetLevelZero)
        exact hpower.trans data.shading_volume_lower)
    simpa [Amax, N] using hlevelZero
  rcases PureHierarchyGeneric.multi_level_thin_with_retention
      (Z := Z) (rawTrapezoids := rawTrapezoids)
      (A_max := Amax) (L := L)
      (by norm_num) hLnonneg hLeq hslab
      (fun level trapezoid htrapezoid =>
        (data.band.length_bounds level trapezoid htrapezoid).2)
      data.band.separated_cores hcoverage hZheight hdelta hdeltaStrict
      hhierarchyLoss hNpos
      (by simpa [N] using hgeometric) hlevelZeroPopular with
    ⟨Zthin, popular, hthinSub, hpopularSub, hthinCoverage,
      hcoreVolume, hpopularNonempty, hvolumeDecomp, hsameMultiplicity⟩
  let removed : ENNReal := Amax * ENNReal.ofReal
    (12 * ∑ level : Fin N,
      Real.rpow (wz1Corollary26Scale delta N level) hierarchyLoss)
  have hremovedBound : removed ≤ ENNReal.ofReal (1 / 3) * volume Z.union := by
    have hremovedRefined := hremoved
    rw [← data.shading_union_eq_refined] at hremovedRefined
    simpa [removed, Amax, N, Z] using hremovedRefined
  have hZvolumeFinite : volume Z.union ≠ ⊤ := by
    have hbox : Z.union ⊆ Kakeya.Streamlined.axisBox 2 2 2 :=
      paperShading_subset_axisBox
    have hboxFinite : volume (Kakeya.Streamlined.axisBox 2 2 2) ≠ ⊤ := by
      rw [Kakeya.Streamlined.volume_axisBox 2 2 2] <;> norm_num
    exact ne_top_of_le_ne_top hboxFinite (measure_mono hbox)
  have hZconstant : Z.HasConstantMultiplicity data.band.multiplicity
      (2 * data.band.multiplicity) := data.shading_constantMultiplicity
  have hZthinConstant : Zthin.HasConstantMultiplicity data.band.multiplicity
      (2 * data.band.multiplicity) := by
    intro point hpoint
    rw [hsameMultiplicity point hpoint]
    exact hZconstant point (hthinSub.union_subset hpoint)
  have hTwoThird : ENNReal.ofReal (2 / 3) * volume Z.union ≤
      volume Zthin.union := by
    let third : ENNReal := ENNReal.ofReal (1 / 3) * volume Z.union
    have hdecomp : volume Z.union ≤ volume Zthin.union + third :=
      hvolumeDecomp.trans (by gcongr)
    have hthirdFinite : third ≠ ⊤ :=
      ENNReal.mul_ne_top (by simp) hZvolumeFinite
    have hsum : ENNReal.ofReal (2 / 3) * volume Z.union + third =
        volume Z.union := by
      dsimp only [third]
      rw [← add_mul]
      have hcoeff : ENNReal.ofReal (2 / 3) +
          ENNReal.ofReal (1 / 3) = 1 := by
        rw [← ENNReal.ofReal_add] <;> norm_num
      rw [hcoeff, one_mul]
    rw [← hsum] at hdecomp
    exact (ENNReal.add_le_add_iff_right hthirdFinite).mp hdecomp
  have hfinalVolumeThin : Kakeya.realRpowENN delta
      (sigma + hierarchyLoss) < volume Zthin.union := by
    exact hfinalVolume.trans_le <|
      (mul_le_mul_left' data.shading_volume_lower
        (ENNReal.ofReal (2 / 3))).trans hTwoThird
  have hZthinVolumePos : 0 < volume Zthin.union :=
    (ENNReal.ofReal_pos.mpr
      (Real.rpow_pos_of_pos hdelta (sigma + hierarchyLoss))).trans_le
      hfinalVolumeThin.le
  have hZthinVolumeFinite : volume Zthin.union ≠ ⊤ :=
    ne_top_of_le_ne_top hZvolumeFinite
      (measure_mono hthinSub.union_subset)
  have hZthinMassPos : 0 < Zthin.mass := by
    have hunionMass : volume Zthin.union ≤ Zthin.mass := by
      have hunion : Zthin.union =
          ⋃ index : Fin (wz1PaperBodyFamily source.family).card,
            Zthin.carrier index := by
        ext point
        simp [Kakeya.Streamlined.Shading.union]
      rw [hunion]
      exact MeasureTheory.measure_iUnion_fintype_le
        MeasureTheory.volume Zthin.carrier
    exact hZthinVolumePos.trans_le hunionMass
  have hZthinMassFinite : Zthin.mass ≠ ⊤ := by
    exact ne_top_of_le_ne_top
      (ENNReal.mul_ne_top
        (ENNReal.mul_ne_top (by norm_num)
          (ENNReal.natCast_ne_top data.band.multiplicity))
        hZthinVolumeFinite)
      (constant_multiplicity_mass_volume_generic hZthinConstant).2
  have hthinMass : ENNReal.ofReal (1 / 3) * Z.mass ≤ Zthin.mass :=
    PureHierarchyGeneric.mass_retention_from_volume_generic
      hZconstant hZthinConstant hZvolumeFinite hTwoThird
  classical
  let allPopular : Finset WZ1VerticalTrapezoid :=
    Finset.biUnion Finset.univ popular
  let coreBound : WZ1VerticalTrapezoid → ENNReal := fun trapezoid =>
    Amax * ENNReal.ofReal
      (Real.rpow trapezoid.height (1 / 2 + hierarchyLoss))
  have hcoreAll : ∀ trapezoid ∈ allPopular,
      volumeInCoreGeneric Zthin trapezoid >
        coreBound trapezoid := by
    intro trapezoid htrapezoid
    rcases Finset.mem_biUnion.mp htrapezoid with
      ⟨level, _, hlevel⟩
    have hraw := hcoreVolume level trapezoid hlevel
    have hheight := data.band.height_eq level trapezoid
      (hpopularSub level hlevel)
    simpa [coreBound, hheight, hLeq] using hraw
  have hcoreFinite : ∀ trapezoid ∈ allPopular,
      coreBound trapezoid ≠ ⊤ := by
    intro trapezoid _
    apply ENNReal.mul_ne_top
    · dsimp only [Amax, pureWZ2HierarchySlabConstant]
      exact ENNReal.mul_ne_top
        (ENNReal.mul_ne_top (by norm_num)
          (ENNReal.mul_ne_top (by norm_num)
            (by simp [Kakeya.realRpowENN])))
        (by simp [Kakeya.realRpowENN])
    · simp
  rcases PureHierarchyGeneric.compact_subshading_with_full_retention_generic
      (Z := Zthin) (T := allPopular) (core_bound := coreBound)
      (vol_bound := Kakeya.realRpowENN delta (sigma + hierarchyLoss))
      (mass_bound := Zthin.mass / 2) data.refined.extremal.nonempty
      hZthinVolumeFinite hcoreAll hfinalVolumeThin
      (ENNReal.half_lt_self hZthinMassPos.ne' hZthinMassFinite)
      hcoreFinite (by simp [Kakeya.realRpowENN])
      (ENNReal.div_ne_top hZthinMassFinite (by norm_num)) with
    ⟨Zcompact, hcompactSub, hcompact, hcompactCore,
      hcompactVolume, hcompactMass⟩
  have hcompactZ : PureWZ2PaperIsSubshading Zcompact Z :=
    fun index => (hcompactSub index).trans (hthinSub index)
  have hcompactBand :
      PureWZ2PaperIsSubshading Zcompact data.band.shading :=
    fun index => (hcompactZ index).trans (hZBand index)
  have hcompactSource :
      PureWZ2PaperIsSubshading Zcompact source.shading :=
    fun index => (hcompactZ index).trans (hZSource index)
  have hslabCompact : ∀ a b : ℝ, a ≤ b →
      volume (Zcompact.union ∩ horizontalSlab a b) ≤
        Amax * ENNReal.ofReal (b - a) := by
    intro a b hab
    exact (measure_mono
      (Set.inter_subset_inter_left _ hcompactZ.union_subset)).trans
        (hslab a b hab)
  have hreanchor : ∀ level : Fin N,
      ∃ (shrunk : WZ1VerticalTrapezoid → WZ1VerticalTrapezoid)
        (anchored : Finset WZ1VerticalTrapezoid),
        (∀ trapezoid ∈ popular level,
          (shrunk trapezoid).core ⊆ trapezoid.core ∧
          (shrunk trapezoid).slope = trapezoid.slope ∧
          (shrunk trapezoid).intercept = trapezoid.intercept ∧
          (shrunk trapezoid).height = trapezoid.height ∧
          L level ≤ (shrunk trapezoid).length) ∧
        (∀ trapezoid ∈ popular level, shrunk trapezoid ∈ anchored) ∧
        (∀ trapezoid ∈ anchored, ∃ sourceTrapezoid ∈ popular level,
          trapezoid = shrunk sourceTrapezoid) ∧
        (∀ trapezoid ∈ anchored,
          horizontalSlice Zcompact.union trapezoid.left ≠ ∅ ∧
          horizontalSlice Zcompact.union trapezoid.right ≠ ∅) ∧
        (∀ trapezoid ∈ anchored, L level ≤ trapezoid.length) ∧
        (∀ trapezoid ∈ anchored, ∃ sourceTrapezoid ∈ popular level,
          trapezoid.core ⊆ sourceTrapezoid.core ∧
          trapezoid.slope = sourceTrapezoid.slope ∧
          trapezoid.intercept = sourceTrapezoid.intercept ∧
          trapezoid.height = sourceTrapezoid.height) ∧
        (∀ z : ℝ, horizontalSlice Zcompact.union z ≠ ∅ →
          (∃ trapezoid ∈ popular level, z ∈ trapezoid.core) →
            ∃ trapezoid ∈ anchored, z ∈ trapezoid.core) := by
    intro level
    have hvolume : ∀ trapezoid ∈ popular level,
        volumeInCoreGeneric Zcompact trapezoid >
          Amax * ENNReal.ofReal (L level) := by
      intro trapezoid htrapezoid
      have hall : trapezoid ∈ allPopular :=
        Finset.mem_biUnion.mpr ⟨level, Finset.mem_univ _, htrapezoid⟩
      have hraw := hcompactCore trapezoid hall
      have hheight := data.band.height_eq level trapezoid
        (hpopularSub level htrapezoid)
      simpa [coreBound, hheight, hLeq] using hraw
    exact PureHierarchyGeneric.reanchor_with_coverage_generic
      (hLnonneg level) hcompact hslabCompact hvolume
  choose shrunk anchored hshrunk hshrunkMem hanchoredFrom
    hactiveEndpoints hlengthLower hprovenance hcoverageAnchored using hreanchor
  let trapezoids : Fin N → Finset WZ1VerticalTrapezoid := anchored
  have hnonempty : ∀ level, (trapezoids level).Nonempty := by
    intro level
    rcases hpopularNonempty level with ⟨trapezoid, htrapezoid⟩
    exact ⟨shrunk level trapezoid, hshrunkMem level trapezoid htrapezoid⟩
  have hheight : ∀ level, ∀ trapezoid ∈ trapezoids level,
      trapezoid.height = wz1Corollary26Scale delta N level := by
    intro level trapezoid htrapezoid
    rcases hanchoredFrom level trapezoid htrapezoid with
      ⟨sourceTrapezoid, hsourceTrapezoid, rfl⟩
    exact (hshrunk level sourceTrapezoid hsourceTrapezoid).2.2.2.1.trans
      (data.band.height_eq level sourceTrapezoid
        (hpopularSub level hsourceTrapezoid))
  have hslope : ∀ level, ∀ trapezoid ∈ trapezoids level,
      |trapezoid.slope| ≤ 2 := by
    intro level trapezoid htrapezoid
    rcases hanchoredFrom level trapezoid htrapezoid with
      ⟨sourceTrapezoid, hsourceTrapezoid, rfl⟩
    rw [(hshrunk level sourceTrapezoid hsourceTrapezoid).2.1]
    exact data.band.slope_bound level sourceTrapezoid
      (hpopularSub level hsourceTrapezoid)
  have hlength : ∀ level, ∀ trapezoid ∈ trapezoids level,
      Real.rpow (wz1Corollary26Scale delta N level)
          (1 / 2 + hierarchyLoss) ≤ trapezoid.length ∧
        trapezoid.length ≤
          Real.sqrt (wz1Corollary26Scale delta N level) := by
    intro level trapezoid htrapezoid
    rcases hanchoredFrom level trapezoid htrapezoid with
      ⟨sourceTrapezoid, hsourceTrapezoid, rfl⟩
    have hprops := hshrunk level sourceTrapezoid hsourceTrapezoid
    have hupper : (shrunk level sourceTrapezoid).length ≤
        sourceTrapezoid.length := by
      have hleft : sourceTrapezoid.left ≤
          (shrunk level sourceTrapezoid).left :=
        (hprops.1 (Set.left_mem_Icc.mpr
          (shrunk level sourceTrapezoid).left_lt_right.le)).1
      have hright : (shrunk level sourceTrapezoid).right ≤
          sourceTrapezoid.right :=
        (hprops.1 (Set.right_mem_Icc.mpr
          (shrunk level sourceTrapezoid).left_lt_right.le)).2
      simp [WZ1VerticalTrapezoid.length]
      linarith
    constructor
    · simpa [L] using hprops.2.2.2.2
    · exact hupper.trans
        (data.band.length_bounds level sourceTrapezoid
          (hpopularSub level hsourceTrapezoid)).2
  have hseparated : ∀ level, ∀ first ∈ trapezoids level,
      ∀ second ∈ trapezoids level, first ≠ second →
        ∀ z ∈ first.core, ∀ w ∈ second.core,
          Real.sqrt (wz1Corollary26Scale delta N level) ≤ |z - w| := by
    intro level first hfirst second hsecond hne z hz w hw
    rcases hanchoredFrom level first hfirst with
      ⟨firstSource, hfirstSource, hfirstEq⟩
    rcases hanchoredFrom level second hsecond with
      ⟨secondSource, hsecondSource, hsecondEq⟩
    have hsourceNe : firstSource ≠ secondSource := by
      intro heq
      subst secondSource
      exact hne (hfirstEq.trans hsecondEq.symm)
    have hfirstCore := (hshrunk level firstSource hfirstSource).1
    have hsecondCore := (hshrunk level secondSource hsecondSource).1
    rw [hfirstEq] at hz
    rw [hsecondEq] at hw
    exact data.band.separated_cores level firstSource
      (hpopularSub level hfirstSource) secondSource
      (hpopularSub level hsecondSource) hsourceNe z (hfirstCore hz)
      w (hsecondCore hw)
  have hactive : ∀ level, ∀ trapezoid ∈ trapezoids level,
      horizontalSlice Zcompact.union trapezoid.left ≠ ∅ ∧
        horizontalSlice Zcompact.union trapezoid.right ≠ ∅ :=
    hactiveEndpoints
  have hslopeFinal : ∀ level, ∀ trapezoid ∈ trapezoids level,
      ∀ z ∈ trapezoid.core, horizontalSlice Zcompact.union z ≠ ∅ →
        |data.band.sourceGlobalGrains.slope z - trapezoid.affine z| ≤
          wz1Corollary26Scale delta N level := by
    intro level trapezoid htrapezoid z hz hslice
    rcases hprovenance level trapezoid htrapezoid with
      ⟨sourceTrapezoid, hsourceTrapezoid, hcore, hslopeEq, hinterceptEq, _⟩
    have hsliceZ : horizontalSlice Z.union z ≠ ∅ := by
      apply Set.Nonempty.ne_empty
      apply Set.Nonempty.mono _ (Set.nonempty_iff_ne_empty.mpr hslice)
      intro point hpoint
      exact ⟨hcompactZ.union_subset hpoint.1, hpoint.2⟩
    have hraw := hslopeApprox level sourceTrapezoid
      (hpopularSub level hsourceTrapezoid) z (hcore hz) hsliceZ
    simpa [WZ1VerticalTrapezoid.affine, hslopeEq, hinterceptEq] using hraw
  have hcoverageFinal : ∀ level, ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      horizontalSlice Zcompact.union z ≠ ∅ →
        ∃ trapezoid ∈ trapezoids level, z ∈ trapezoid.core := by
    intro level z _hz hslice
    have hsliceThin : horizontalSlice Zthin.union z ≠ ∅ := by
      apply Set.Nonempty.ne_empty
      apply Set.Nonempty.mono _ (Set.nonempty_iff_ne_empty.mpr hslice)
      intro point hpoint
      exact ⟨hcompactSub.union_subset hpoint.1, hpoint.2⟩
    exact hcoverageAnchored level z hslice
      (hthinCoverage level z hsliceThin)
  have hwithout : PureWZ2HierarchyWithoutParents
      Zcompact data.band.sourceGlobalGrains.slope hierarchyLoss :=
    { delta_pos := hdelta
      delta_le_one := hdeltaOne
      hierarchyLoss_pos := hhierarchyLoss
      vertical_bound := by
        intro point hpoint
        exact hZheight point (hcompactZ.union_subset hpoint)
      levelCount := N
      levelCount_two := data.band.iterated.levelCount_two
      trapezoids := trapezoids
      level_nonempty := hnonempty
      height_eq := hheight
      slope_bound := hslope
      length_bounds := hlength
      separated_cores := hseparated
      active_endpoints := hactive
      slope_approximation := hslopeFinal
      active_height_coverage := hcoverageFinal }
  have hconstant : Kakeya.realRpowENN delta (-terminalLoss) ≤
      Kakeya.realRpowENN delta (-hierarchyLoss) :=
    pureWZ2_grain_constant_mono hdelta hdeltaOne hterminalHierarchy
  have hconstantTop : Kakeya.realRpowENN delta (-hierarchyLoss) ≠ ⊤ := by
    simp [Kakeya.realRpowENN]
  let localGrains := data.band.localGrains.restrictWithConstant
    hcompactBand hconstant hconstantTop
  let restrictedGlobal := data.band.sourceGlobalGrains.restrict
    hcompactBand hconstant hconstantTop
  let globalGrains : PureWZ2BoundedLipschitzGlobalGrainData
      Zcompact sigma (Kakeya.realRpowENN delta (-hierarchyLoss)) :=
    PureWZ2BoundedLipschitzGlobalGrainData.ofSlopeBound restrictedGlobal <| by
      intro z hz
      change |data.band.sourceGlobalGrains.slope z| ≤ 3
      rw [data.band.source_slope_eq]
      exact source.globalGrains.slope_bound z hz
  let hierarchy : PureWZ2LocallyLinearHierarchyData
      source hierarchyLoss hierarchyLoss := {
    levelCount := N
    levelCount_two := data.band.iterated.levelCount_two
    delta_pos := hdelta
    delta_le_one := hdeltaOne
    shading := Zcompact
    subshading := hcompactSource
    volume_lower := hcompactVolume
    localGrains := localGrains
    planeMap_vertical_bound := by
      intro point
      exact data.band.planeMap_vertical_bound
        ⟨point, hcompactBand.union_subset point.property⟩
    sourceGlobalGrains := globalGrains
    source_slope_eq := data.band.source_slope_eq
    hierarchy := hwithout.toAnchoredHierarchy }
  have hcompactMultiplicityUpper : ∀ point,
      Zcompact.pointMultiplicity point ≤ 2 * data.band.multiplicity := by
    intro point
    by_cases hpoint : point ∈ Zcompact.union
    · exact (paperSubshading_pointMultiplicity_le Zcompact Z hcompactZ point).trans
        (hZconstant point (hcompactZ.union_subset hpoint)).2
    · have hzero : Zcompact.pointMultiplicity point = 0 := by
        classical
        unfold Kakeya.Streamlined.Shading.pointMultiplicity
        apply Finset.card_eq_zero.mpr
        rw [Finset.filter_eq_empty_iff]
        intro index _ hindex
        exact hpoint ⟨index, hindex⟩
      rw [hzero]
      omega
  have hrefinedSubZ :
      PureWZ2PaperIsSubshading data.refined.shading Z := by
    intro index point hpoint
    exact ⟨data.refined.subshading index hpoint, ⟨index, hpoint⟩⟩
  have hrefinedMassLeZ : data.refined.shading.mass ≤ Z.mass := by
    apply Finset.sum_le_sum
    intro index _
    exact measure_mono (hrefinedSubZ index)
  have hcompactHalf : ENNReal.ofReal (1 / 2) * Zthin.mass ≤
      Zcompact.mass := by
    have hdiv : Zthin.mass / 2 =
        ENNReal.ofReal (1 / 2) * Zthin.mass := by
      have h1 : Zthin.mass / 2 = Zthin.mass / ENNReal.ofReal 2 := by
        norm_cast
      rw [h1, ENNReal.div_eq_inv_mul]
      have hhalf : (ENNReal.ofReal 2)⁻¹ = ENNReal.ofReal (1 / 2) := by
        have hraw : (ENNReal.ofReal 2)⁻¹ =
            ENNReal.ofReal ((2 : ℝ)⁻¹) :=
          (ENNReal.ofReal_inv_of_pos (x := (2 : ℝ)) (by norm_num)).symm
        rw [hraw]
        norm_num
      rw [hhalf, mul_comm]
    rwa [← hdiv]
  have hcompactSixth : ENNReal.ofReal (1 / 6) * Z.mass ≤
      Zcompact.mass := by
    have hcoeff : ENNReal.ofReal (1 / 6) =
        ENNReal.ofReal (1 / 2) * ENNReal.ofReal (1 / 3) := by
      rw [← ENNReal.ofReal_mul] <;> norm_num
    calc
      ENNReal.ofReal (1 / 6) * Z.mass =
          ENNReal.ofReal (1 / 2) *
            (ENNReal.ofReal (1 / 3) * Z.mass) := by
              rw [hcoeff, mul_assoc]
      _ ≤ ENNReal.ofReal (1 / 2) * Zthin.mass := by gcongr
      _ ≤ Zcompact.mass := hcompactHalf
  have hsourceMass : Kakeya.realRpowENN delta targetLoss *
      (wz1PaperBodyFamily source.family).mass ≤ Z.mass :=
    data.refined.extremal.dense.trans hrefinedMassLeZ
  exact ⟨{
    hierarchy := hierarchy
    multiplicity := data.band.multiplicity
    multiplicity_pos := data.band.multiplicity_pos
    pointMultiplicity_upper := by
      simpa [hierarchy] using hcompactMultiplicityUpper
    mass_retention := by
      calc
        ENNReal.ofReal (1 / 6) *
              (Kakeya.realRpowENN delta targetLoss *
                (wz1PaperBodyFamily source.family).mass) ≤
            ENNReal.ofReal (1 / 6) * Z.mass := by gcongr
        _ ≤ Zcompact.mass := hcompactSixth
        _ = hierarchy.shading.mass := rfl }⟩

/-- Compatibility projection of the quantitative ordinary hierarchy. -/
theorem toLocallyLinearHierarchy
    {sigma inputLoss delta terminalLoss hierarchyLoss selectionLoss
      targetLoss : ℝ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    (data : PureWZ2RestoredHierarchyData source terminalLoss hierarchyLoss
      selectionLoss targetLoss)
    (hbridge : PureWZ2PaperADBridgeStatement)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hhierarchyLoss : 0 < hierarchyLoss)
    (hterminalHierarchy : terminalLoss ≤ hierarchyLoss)
    (htargetHierarchy : targetLoss ≤ hierarchyLoss)
    (htargetLevelZero : targetLoss ≤
      hierarchyLoss / (4 * (data.band.iterated.levelCount : ℝ)))
    (hdeltaStrict : delta < 1)
    (hgeometric : Real.rpow delta
      (hierarchyLoss / (data.band.iterated.levelCount : ℝ)) < 1 / 9)
    (hlevelZero :
      pureWZ2HierarchySlabConstant delta sigma targetLoss *
          ENNReal.ofReal (12 * Real.rpow delta
            (hierarchyLoss / (data.band.iterated.levelCount : ℝ))) <
        Kakeya.realRpowENN delta
          (sigma + hierarchyLoss /
            (4 * (data.band.iterated.levelCount : ℝ))))
    (hremoved :
      pureWZ2HierarchySlabConstant delta sigma targetLoss *
          ENNReal.ofReal
            (12 * ∑ level : Fin data.band.iterated.levelCount,
              Real.rpow
                (wz1Corollary26Scale delta
                  data.band.iterated.levelCount level) hierarchyLoss) ≤
        ENNReal.ofReal (1 / 3) *
          MeasureTheory.volume data.refined.shading.union)
    (hfinalVolume :
      Kakeya.realRpowENN delta (sigma + hierarchyLoss) <
        ENNReal.ofReal (2 / 3) *
          Kakeya.realRpowENN delta (sigma + targetLoss)) :
    Nonempty (PureWZ2LocallyLinearHierarchyData
      source hierarchyLoss hierarchyLoss) := by
  rcases data.toQuantitativeLocallyLinearHierarchy hbridge hsigma hsigmaOne
      hhierarchyLoss hterminalHierarchy htargetHierarchy htargetLevelZero
      hdeltaStrict hgeometric hlevelZero hremoved hfinalVolume with
    ⟨quantitative⟩
  exact ⟨quantitative.hierarchy⟩

end PureWZ2RestoredHierarchyData

end Kakeya.Assouad

end
