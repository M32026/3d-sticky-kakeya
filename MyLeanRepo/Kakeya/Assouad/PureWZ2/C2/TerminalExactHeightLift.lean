import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.TerminalScaleExactRichSetTrapezoid

/-!
# Exact terminal height-only lift

At the terminal scale the Lemma-23 graph is used only to select the rich
height set.  As in the proof of WZ Corollary 5.6, the final shading returns
to the original source family and is restricted only in the height variable.

Unlike the nonterminal lift, this endpoint is not enlarged to complete source
`delta`-cells: such an enlargement would turn the exact `delta` affine error
into a fixed multiple of `delta`.  The final Corollary-5.6 level does not feed
another Lemma-24 call, so no cubicality assertion is needed here.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

/-- Return from one terminal auxiliary graph to the original source shading,
keeping exactly the selected rich height slabs inside the local trapezoid
core. -/
structure PureWZ2TerminalExactHeightLift
    {sigma inputLoss delta stickyLoss eta theoremEta outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    {window : PureWZ2TerminalWindow prepared}
    {line : PureWZ2HorizontalFixedBinCore
      window.windowed source.globalGrains.slope}
    {parents : PureWZ2TerminalFixedBinParentData line}
    {selection : PureWZ2TerminalBinParentYSelection parents}
    {residue : PureWZ2TerminalBinParentYResidueData selection}
    {retained : PureWZ2TerminalBinRetainedShadingData residue}
    {sources : PureWZ2TerminalBinSourceFamily retained}
    {band : PureWZ2TerminalBinFixedBandSelection sources}
    {phase : PureWZ2TerminalBinHeightPhaseSelection band}
    {anchored : PureWZ2TerminalBinAnchoredPieceData phase}
    {prep : PureWZ2TerminalBinExactGraphPreparation anchored}
    {graphParents : PureWZ2TerminalExactGraphParentData prep}
    {localCells : PureWZ2TerminalExactLocalCellData (eta := eta) graphParents}
    {preparedGraph : PureWZ2TerminalExactPreparedGraphData localCells}
    {sharp : PureWZ2TerminalExactSharpGeometry preparedGraph}
    {first : PureWZ2TerminalExactReadyGraph
      (theoremEta := theoremEta) sharp}
    {ready : PureWZ2TerminalExactRefinedReadyGraph first}
    {rich : PureWZ2TerminalExactAlternativeAHeightData ready outputLoss}
    {weighted : PureWZ2TerminalExactRichHeightCellData rich}
    (exactTrapezoid : PureWZ2TerminalExactRichSetTrapezoid weighted) where
  richRegion : Set Point3 :=
    ⋃ heightIndex ∈ rich.heightIndices,
      wz1Lemma23HeightSlab delta heightIndex
  richRegion_eq : richRegion =
    ⋃ heightIndex ∈ rich.heightIndices,
      wz1Lemma23HeightSlab delta heightIndex
  coreRegion : Set Point3 :=
    {point | point (2 : Fin 3) ∈ exactTrapezoid.trapezoid.core}
  coreRegion_eq : coreRegion =
    {point | point (2 : Fin 3) ∈ exactTrapezoid.trapezoid.core}
  region : Set Point3 := richRegion ∩ coreRegion
  region_eq : region = richRegion ∩ coreRegion
  region_measurable : MeasurableSet region
  shading : WZ1PaperTubeShading source.family
  carrier_eq : ∀ index, shading.carrier index =
    source.shading.carrier index ∩ region
  subshading : PureWZ2PaperIsSubshading shading source.shading
  union_eq : shading.union = source.shading.union ∩ region
  exact_subshading :
    PureWZ2PaperIsSubshading exactTrapezoid.shading shading
  volume_lower : volume exactTrapezoid.shading.union ≤ volume shading.union
  mass_lower : exactTrapezoid.shading.mass ≤ shading.mass
  active_height_coverage :
    ∀ z, horizontalSlice shading.union z ≠ ∅ →
      z ∈ exactTrapezoid.trapezoid.core
  slope_approximation :
    ∀ z, horizontalSlice shading.union z ≠ ∅ →
      |source.globalGrains.slope z -
        exactTrapezoid.trapezoid.affine z| ≤ delta

theorem PureWZ2TerminalExactRichSetTrapezoid.toHeightLift
    {sigma inputLoss delta stickyLoss eta theoremEta outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    {window : PureWZ2TerminalWindow prepared}
    {line : PureWZ2HorizontalFixedBinCore
      window.windowed source.globalGrains.slope}
    {parents : PureWZ2TerminalFixedBinParentData line}
    {selection : PureWZ2TerminalBinParentYSelection parents}
    {residue : PureWZ2TerminalBinParentYResidueData selection}
    {retained : PureWZ2TerminalBinRetainedShadingData residue}
    {sources : PureWZ2TerminalBinSourceFamily retained}
    {band : PureWZ2TerminalBinFixedBandSelection sources}
    {phase : PureWZ2TerminalBinHeightPhaseSelection band}
    {anchored : PureWZ2TerminalBinAnchoredPieceData phase}
    {prep : PureWZ2TerminalBinExactGraphPreparation anchored}
    {graphParents : PureWZ2TerminalExactGraphParentData prep}
    {localCells : PureWZ2TerminalExactLocalCellData (eta := eta) graphParents}
    {preparedGraph : PureWZ2TerminalExactPreparedGraphData localCells}
    {sharp : PureWZ2TerminalExactSharpGeometry preparedGraph}
    {first : PureWZ2TerminalExactReadyGraph
      (theoremEta := theoremEta) sharp}
    {ready : PureWZ2TerminalExactRefinedReadyGraph first}
    {rich : PureWZ2TerminalExactAlternativeAHeightData ready outputLoss}
    {weighted : PureWZ2TerminalExactRichHeightCellData rich}
    (exactTrapezoid : PureWZ2TerminalExactRichSetTrapezoid weighted) :
    Nonempty (PureWZ2TerminalExactHeightLift exactTrapezoid) := by
  let richRegion : Set Point3 :=
    ⋃ heightIndex ∈ rich.heightIndices,
      wz1Lemma23HeightSlab delta heightIndex
  let coreRegion : Set Point3 :=
    {point | point (2 : Fin 3) ∈ exactTrapezoid.trapezoid.core}
  let region := richRegion ∩ coreRegion
  have hrichMeasurable : MeasurableSet richRegion :=
    MeasurableSet.biUnion rich.heightIndices.finite_toSet.countable
      (fun heightIndex _ => by
        change MeasurableSet ((fun point : Point3 => point 2) ⁻¹'
          wz1Lemma23HeightInterval delta heightIndex)
        exact measurableSet_Ico.preimage
          (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) 2).measurable)
  have hcoreMeasurable : MeasurableSet coreRegion := by
    change MeasurableSet ((fun point : Point3 => point 2) ⁻¹'
      exactTrapezoid.trapezoid.core)
    exact measurableSet_Icc.preimage
      (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) 2).measurable
  have hregionMeasurable : MeasurableSet region :=
    hrichMeasurable.inter hcoreMeasurable
  let shading : WZ1PaperTubeShading source.family :=
    { carrier := fun index => source.shading.carrier index ∩ region
      measurable_carrier := fun index =>
        (source.shading.measurable_carrier index).inter hregionMeasurable
      subset_body := fun index => Set.inter_subset_left.trans
        (source.shading.subset_body index) }
  have hsub : PureWZ2PaperIsSubshading shading source.shading := by
    intro index point hpoint
    exact hpoint.1
  have hunion : shading.union = source.shading.union ∩ region := by
    ext point
    constructor
    · rintro ⟨index, hsource, hregion⟩
      exact ⟨⟨index, hsource⟩, hregion⟩
    · rintro ⟨⟨index, hsource⟩, hregion⟩
      exact ⟨index, hsource, hregion⟩
  have hexactSub : PureWZ2PaperIsSubshading
      exactTrapezoid.shading shading := by
    intro index point hpoint
    have hlocal := hpoint
    rw [exactTrapezoid.carrier_eq] at hlocal
    have hsource : point ∈ source.shading.carrier index :=
      retained.subshading index
        (exactTrapezoid.subshading index hpoint)
    have hrichRegion : point ∈ richRegion := by
      have hrichSet := hlocal.2
      rw [weighted.richSet_eq] at hrichSet
      simpa [richRegion, weighted.richRegion_eq] using hrichSet.2
    have hslice : horizontalSlice exactTrapezoid.shading.union
        (point 2) ≠ ∅ := by
      apply Set.nonempty_iff_ne_empty.mp
      exact ⟨point, ⟨index, hpoint⟩, rfl⟩
    have hcore : point 2 ∈ exactTrapezoid.trapezoid.core :=
      exactTrapezoid.active_height_coverage (point 2) hslice
    exact ⟨hsource, hrichRegion, hcore⟩
  have hselectedPoint : ∀ point ∈ shading.union,
      point 2 ∈ exactTrapezoid.trapezoid.core ∧
        ∃ heightIndex ∈ rich.heightIndices,
          |point 2 - wz1Lemma23SnappedBaseHeight delta heightIndex| ≤
            delta / (2 * Real.sqrt 3) := by
    intro point hpoint
    rw [hunion] at hpoint
    rcases hpoint.2 with ⟨hrichRegion, hcore⟩
    rcases Set.mem_iUnion₂.mp hrichRegion with
      ⟨heightIndex, hheightIndex, hslab⟩
    refine ⟨hcore, heightIndex, hheightIndex, ?_⟩
    change point 2 ∈ wz1Lemma23HeightInterval delta heightIndex at hslab
    rw [wz1Lemma23HeightInterval] at hslab
    have hside : gridSide (delta / 2) = delta / Real.sqrt 3 := by
      simp [gridSide]
      ring
    have hcenter : wz1Lemma23SnappedBaseHeight delta heightIndex =
        ((heightIndex : ℝ) + 1 / 2) * gridSide (delta / 2) := by
      simp [wz1Lemma23SnappedBaseHeight]
    have hhalf : delta / (2 * Real.sqrt 3) =
        (delta / Real.sqrt 3) / 2 := by ring
    have hlower :
        (heightIndex : ℝ) * (delta / Real.sqrt 3) -
            ((heightIndex : ℝ) + 1 / 2) * (delta / Real.sqrt 3) =
          -(delta / Real.sqrt 3 / 2) := by ring
    have hupper :
        ((heightIndex : ℝ) + 1) * (delta / Real.sqrt 3) -
            ((heightIndex : ℝ) + 1 / 2) * (delta / Real.sqrt 3) =
          delta / Real.sqrt 3 / 2 := by ring
    rw [hside] at hslab
    rw [hcenter, abs_le, hside, hhalf]
    constructor
    · calc
        -(delta / Real.sqrt 3 / 2) =
            (heightIndex : ℝ) * (delta / Real.sqrt 3) -
              ((heightIndex : ℝ) + 1 / 2) *
                (delta / Real.sqrt 3) := hlower.symm
        _ ≤ point 2 - ((heightIndex : ℝ) + 1 / 2) *
              (delta / Real.sqrt 3) := sub_le_sub_right hslab.1 _
    · calc
        point 2 - ((heightIndex : ℝ) + 1 / 2) *
              (delta / Real.sqrt 3) ≤
            ((heightIndex : ℝ) + 1) * (delta / Real.sqrt 3) -
              ((heightIndex : ℝ) + 1 / 2) *
                (delta / Real.sqrt 3) :=
          sub_le_sub_right hslab.2.le _
        _ = delta / Real.sqrt 3 / 2 := hupper
  have hcoverage : ∀ z, horizontalSlice shading.union z ≠ ∅ →
      z ∈ exactTrapezoid.trapezoid.core := by
    intro z hslice
    rcases Set.nonempty_iff_ne_empty.mpr hslice with
      ⟨point, hpoint, hheight⟩
    have hselected := (hselectedPoint point hpoint).1
    rwa [hheight] at hselected
  have hslope : ∀ z, horizontalSlice shading.union z ≠ ∅ →
      |source.globalGrains.slope z -
        exactTrapezoid.trapezoid.affine z| ≤ delta := by
    intro z hslice
    rcases Set.nonempty_iff_ne_empty.mpr hslice with
      ⟨point, hpoint, hheight⟩
    have hsourcePoint : point ∈ source.shading.union :=
      hsub.union_subset hpoint
    have hbox := shading_union_subset_axisBox hsourcePoint
    have hz : z ∈ Set.Icc (-1 : ℝ) 1 := by
      rw [← hheight]
      have habs : |point 2| ≤ 1 := by
        convert hbox.2.2 using 1 <;> norm_num
      exact abs_le.mp habs
    rcases (hselectedPoint point hpoint).2 with
      ⟨heightIndex, hheightIndex, hclose⟩
    rw [hheight] at hclose
    exact exactTrapezoid.rich_height_approximation
      heightIndex hheightIndex z hz hclose
  exact ⟨{
    richRegion := richRegion
    richRegion_eq := rfl
    coreRegion := coreRegion
    coreRegion_eq := rfl
    region := region
    region_eq := rfl
    region_measurable := hregionMeasurable
    shading := shading
    carrier_eq := fun _ => rfl
    subshading := hsub
    union_eq := hunion
    exact_subshading := hexactSub
    volume_lower := measure_mono hexactSub.union_subset
    mass_lower := by
      apply Finset.sum_le_sum
      intro index _
      exact measure_mono (hexactSub index)
    active_height_coverage := hcoverage
    slope_approximation := hslope
  }⟩

end Kakeya.Assouad

end
