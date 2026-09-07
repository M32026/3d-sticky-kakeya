import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.OrdinaryPaperOrderOneScale
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.ReentryTraceFloorSchedule

/-!
# Re-entry trace closure for one paper-order height lift

The final `Z_lin` shading already lives on the original source family.  This
module applies the source re-entry normalization to that exact shading through
the identity subfamily, uses the scheduled ordinary critical floor, and then
restricts the source grains literally to the height lift.  No grain producer
for arbitrary families or shadings is exposed.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

/-- Identity-indexed view of the unchanged original source family. -/
private noncomputable def ordinaryPaperOrderIdentitySubfamily
    {sigma inputLoss delta : ℝ}
    (source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta) :
    Kakeya.Streamlined.TubeSubfamily source.family where
  family := source.family
  embedding := Function.Embedding.refl _
  tube_eq := fun _ => rfl

/-- Construction data for a one-scale object on an arbitrary literal
subshading of the current source.  This contains only the final trapezoid
geometry; density, extremality, volume, and grains are supplied by the generic
re-entry theorem below. -/
structure PureWZ2LiteralCurrentSourceOneScaleGeometry
    {sigma inputLoss delta : ℝ}
    (source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta)
    (target : WZ1PaperTubeShading source.family)
    (outputLoss rho : ℝ) where
  rho_pos : 0 < rho
  delta_le_rho : delta ≤ rho
  rho_le_one : rho ≤ 1
  trapezoids : Finset WZ1VerticalTrapezoid
  trapezoids_nonempty : trapezoids.Nonempty
  height_eq : ∀ trapezoid ∈ trapezoids, trapezoid.height = rho
  slope_bound : ∀ trapezoid ∈ trapezoids, |trapezoid.slope| ≤ 2
  length_bounds : ∀ trapezoid ∈ trapezoids,
    Real.rpow rho (1 / 2 + outputLoss) ≤ trapezoid.length ∧
      trapezoid.length ≤ Real.sqrt rho
  separated_cores : ∀ trapezoid ∈ trapezoids,
    ∀ other ∈ trapezoids, trapezoid ≠ other →
      ∀ z ∈ trapezoid.core, ∀ w ∈ other.core,
        Real.sqrt rho ≤ |z - w|
  slope_approximation : ∀ trapezoid ∈ trapezoids,
    ∀ z ∈ trapezoid.core,
      horizontalSlice target.union z ≠ ∅ →
        |source.globalGrains.slope z - trapezoid.affine z| ≤ rho
  active_height_coverage : ∀ z ∈ Set.Icc (-1 : ℝ) 1,
    horizontalSlice target.union z ≠ ∅ →
      ∃ trapezoid ∈ trapezoids, z ∈ trapezoid.core

/-- Generic exact closure on any literal current-source subshading.

The critical volume floor comes from the current re-entry trace.  The global
and local grains are restrictions of the current source grains, so no fresh
grain producer or arbitrary-family callback occurs. -/
theorem pureWZ2_literalCurrentSourceOneScale_of_reentryTrace
    {sigma inputLoss delta outputLoss rho structuralBudget traceSourceLoss : ℝ}
    {normalizationExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    (target : WZ1PaperTubeShading source.family)
    (subshading : PureWZ2PaperIsSubshading target source.shading)
    (cubical : WZ1PaperIsCubicalShading target)
    (floorSchedule : PureWZ2ReentryTraceFloorSchedule
      sigma outputLoss structuralBudget)
    (hinputDensity : inputLoss ≤ floorSchedule.densityLoss)
    (htraceSource : traceSourceLoss ≤ floorSchedule.traceSourceCeiling)
    (hdeltaSchedule : delta ≤ floorSchedule.delta₀)
    (dense : target.IsLambdaDense
      (Kakeya.realRpowENN delta floorSchedule.densityLoss))
    (reentry : PureWZ2PropStickyReentryData
      (sigma := sigma) source.shading normalizationExponent
      traceSourceLoss inputLoss)
    (geometry : PureWZ2LiteralCurrentSourceOneScaleGeometry
      source target outputLoss rho) :
    Nonempty (PureWZ2LocallyLinearOneScaleData source outputLoss rho) := by
  have hsourceDensity : WZ2PaperCroppedIsExtremal
      sigma floorSchedule.densityLoss source.family source.shading :=
    source.extremal.mono_loss hinputDensity
  have htargetDensity : WZ2PaperCroppedIsExtremal
      sigma floorSchedule.densityLoss source.family target :=
    { delta_pos := source.extremal.delta_pos
      delta_le_one := source.extremal.delta_le_one
      nonempty := source.extremal.nonempty
      cwa_nearby_scales := hsourceDensity.cwa_nearby_scales
      cubical := cubical
      dense := dense
      volume_upper :=
        (measure_mono subshading.union_subset).trans
          hsourceDensity.volume_upper }
  let normalized := reentry.toNormalizationData
  let selected := ordinaryPaperOrderIdentitySubfamily source
  have hfinalSubset : ∀ index, target.carrier index ⊆
      normalized.croppedRefined.carrier (selected.embedding index) := by
    intro index
    exact subshading index
  have hordinaryPerTube : ∀ index : Fin selected.family.card,
      (Kakeya.realRpowENN delta traceSourceLoss / 2) *
          volume (normalized.croppedFamily.tube
            (selected.embedding index)).carrier ≤
        volume (normalized.frame ''
          normalized.ordinaryRefined.carrier
            (normalized.ordinaryIndex selected index)) := by
    intro index
    exact normalized.framed_ordinary_per_tube selected index
  have hvolume : Kakeya.realRpowENN delta (sigma + outputLoss) ≤
      volume target.union := by
    exact normalized.volume_lower_of_trace_and_pure_floor selected target
      source.extremal.nonempty cubical hfinalSubset
      (Kakeya.realRpowENN delta traceSourceLoss / 2)
      (floorSchedule.lossConstant delta) hordinaryPerTube
      floorSchedule.criticalFloor
      (floorSchedule.lossConstant_one source.extremal.delta_pos
        hdeltaSchedule)
      (floorSchedule.lossConstant_ne_top delta)
      (floorSchedule.trace_absorption delta source.extremal.delta_pos
        hdeltaSchedule traceSourceLoss reentry.sourceLoss_pos.le htraceSource)
      hsourceDensity.cwa_nearby_scales dense
      (floorSchedule.cwa_absorption source.extremal.delta_pos).le
      (floorSchedule.density_absorption source.extremal.delta_pos).le
      (hdeltaSchedule.trans floorSchedule.delta₀_le_twelve)
      (hdeltaSchedule.trans floorSchedule.delta₀_le_floor)
  have hinputFinal : inputLoss ≤ outputLoss :=
    hinputDensity.trans floorSchedule.densityLoss_le_floor
  have hconstant : Kakeya.realRpowENN delta (-inputLoss) ≤
      Kakeya.realRpowENN delta (-outputLoss) :=
    pureWZ2_grain_constant_mono source.extremal.delta_pos
      source.extremal.delta_le_one hinputFinal
  have hconstantTop :
      Kakeya.realRpowENN delta (-outputLoss) ≠ ⊤ := by
    simp [Kakeya.realRpowENN]
  let localGrains := source.localGrains.restrictWithConstant
    subshading hconstant hconstantTop
  let globalGrains := source.globalGrains.restrict
    subshading hconstant hconstantTop
  have hvertical : ∀ point : {point : Point3 // point ∈ target.union},
      |localGrains.planeMap point (2 : Fin 3)| ≤ 1 / 2 := by
    intro point
    exact source.planeMap_vertical_bound
      ⟨point, subshading.union_subset point.property⟩
  exact ⟨{
    rho_pos := geometry.rho_pos
    delta_le_rho := geometry.delta_le_rho
    rho_le_one := geometry.rho_le_one
    shading := target
    subshading := subshading
    whole_cells := cubical
    extremal := htargetDensity.mono_loss
      floorSchedule.densityLoss_le_floor
    volume_lower := hvolume
    localGrains := localGrains
    planeMap_vertical_bound := hvertical
    globalGrains := globalGrains
    slope_eq := rfl
    trapezoids := geometry.trapezoids
    trapezoids_nonempty := geometry.trapezoids_nonempty
    height_eq := geometry.height_eq
    slope_bound := geometry.slope_bound
    length_bounds := geometry.length_bounds
    separated_cores := geometry.separated_cores
    slope_approximation := geometry.slope_approximation
    active_height_coverage := geometry.active_height_coverage
  }⟩

/-- The runtime scalar receipt left after the trace-floor schedule has been
chosen.  Its only geometric quantity is the mass of the exact source-height
lift; in particular it is not a callback over later families or shadings. -/
structure PureWZ2OrdinaryPaperOrderSourceHeightRuntimeMassReceipt
    {sigma finalLoss structuralBudget : ℝ}
    (floorSchedule : PureWZ2ReentryTraceFloorSchedule
      sigma finalLoss structuralBudget)
    {inputLoss delta rho middleLoss stickyLoss normalEta theoremEta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {carriers : PureWZ2OrdinaryPaperOrderCarrierData twoScale}
    {prepared : PureWZ2OrdinaryPaperOrderPreparationData carriers}
    {graphData : PureWZ2OrdinaryPaperOrderGraphData
      (normalEta := normalEta) prepared}
    (data : PureWZ2OrdinaryPaperOrderRichGraphData
      (finalLoss := finalLoss) (theoremEta := theoremEta) graphData)
    (traceSourceLoss : ℝ) where
  inputLoss_le_density : inputLoss ≤ floorSchedule.densityLoss
  traceSourceLoss_le_ceiling :
    traceSourceLoss ≤ floorSchedule.traceSourceCeiling
  delta_le_schedule : delta ≤ floorSchedule.delta₀
  source_height_density :
    Kakeya.realRpowENN delta floorSchedule.densityLoss *
        (wz1PaperBodyFamily source.family).mass ≤
      data.heightLift.shading.mass

namespace PureWZ2OrdinaryPaperOrderRichGraphData

/-- The scheduled critical volume floor on the literal original-family
height lift.  The selected family is identity-indexed, and cubicality,
density, and containment are the exact fields of `data.heightLift`. -/
theorem volumeLowerOfSourceReentryTraceSchedule
    {sigma finalLoss structuralBudget : ℝ}
    (floorSchedule : PureWZ2ReentryTraceFloorSchedule
      sigma finalLoss structuralBudget)
    {inputLoss delta rho middleLoss stickyLoss normalEta theoremEta
      traceSourceLoss : ℝ}
    {logExponent normalizationExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {carriers : PureWZ2OrdinaryPaperOrderCarrierData twoScale}
    {prepared : PureWZ2OrdinaryPaperOrderPreparationData carriers}
    {graphData : PureWZ2OrdinaryPaperOrderGraphData
      (normalEta := normalEta) prepared}
    (data : PureWZ2OrdinaryPaperOrderRichGraphData
      (finalLoss := finalLoss) (theoremEta := theoremEta) graphData)
    (reentry : PureWZ2PropStickyReentryData
      (sigma := sigma) source.shading normalizationExponent
      traceSourceLoss inputLoss)
    (receipt : PureWZ2OrdinaryPaperOrderSourceHeightRuntimeMassReceipt
      floorSchedule data traceSourceLoss) :
    Kakeya.realRpowENN delta (sigma + finalLoss) ≤
      volume data.heightLift.shading.union := by
  have hliftDense : data.heightLift.shading.IsLambdaDense
      (Kakeya.realRpowENN delta floorSchedule.densityLoss) := by
    simpa only [Kakeya.Streamlined.Shading.IsLambdaDense] using
      receipt.source_height_density
  have hsourceDensity : WZ2PaperCroppedIsExtremal
      sigma floorSchedule.densityLoss source.family source.shading :=
    source.extremal.mono_loss receipt.inputLoss_le_density
  let normalized := reentry.toNormalizationData
  let selected := ordinaryPaperOrderIdentitySubfamily source
  have hfinalSubset : ∀ index,
      data.heightLift.shading.carrier index ⊆
        normalized.croppedRefined.carrier (selected.embedding index) := by
    intro index
    exact data.heightLift.subshading index
  have hordinaryPerTube : ∀ index : Fin selected.family.card,
      (Kakeya.realRpowENN delta traceSourceLoss / 2) *
          volume (normalized.croppedFamily.tube
            (selected.embedding index)).carrier ≤
        volume (normalized.frame ''
          normalized.ordinaryRefined.carrier
            (normalized.ordinaryIndex selected index)) := by
    intro index
    exact normalized.framed_ordinary_per_tube selected index
  exact normalized.volume_lower_of_trace_and_pure_floor selected
    data.heightLift.shading source.extremal.nonempty
    data.heightLift.whole_cells hfinalSubset
    (Kakeya.realRpowENN delta traceSourceLoss / 2)
    (floorSchedule.lossConstant delta) hordinaryPerTube
    floorSchedule.criticalFloor
    (floorSchedule.lossConstant_one source.extremal.delta_pos
      receipt.delta_le_schedule)
    (floorSchedule.lossConstant_ne_top delta)
    (floorSchedule.trace_absorption delta source.extremal.delta_pos
      receipt.delta_le_schedule traceSourceLoss
      reentry.sourceLoss_pos.le receipt.traceSourceLoss_le_ceiling)
    hsourceDensity.cwa_nearby_scales hliftDense
    (floorSchedule.cwa_absorption source.extremal.delta_pos).le
    (floorSchedule.density_absorption source.extremal.delta_pos).le
    (receipt.delta_le_schedule.trans floorSchedule.delta₀_le_twelve)
    (receipt.delta_le_schedule.trans floorSchedule.delta₀_le_floor)

/-- Exact grain refinement on the unchanged height-lift shading.  Its global
and local grains are the current source grains restricted once along
`heightLift.subshading`; no second shading or family is selected. -/
theorem exactRefinementOfSourceReentryTraceSchedule
    {sigma finalLoss structuralBudget : ℝ}
    (floorSchedule : PureWZ2ReentryTraceFloorSchedule
      sigma finalLoss structuralBudget)
    {inputLoss delta rho middleLoss stickyLoss normalEta theoremEta
      traceSourceLoss : ℝ}
    {logExponent normalizationExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {carriers : PureWZ2OrdinaryPaperOrderCarrierData twoScale}
    {prepared : PureWZ2OrdinaryPaperOrderPreparationData carriers}
    {graphData : PureWZ2OrdinaryPaperOrderGraphData
      (normalEta := normalEta) prepared}
    (data : PureWZ2OrdinaryPaperOrderRichGraphData
      (finalLoss := finalLoss) (theoremEta := theoremEta) graphData)
    (reentry : PureWZ2PropStickyReentryData
      (sigma := sigma) source.shading normalizationExponent
      traceSourceLoss inputLoss)
    (receipt : PureWZ2OrdinaryPaperOrderSourceHeightRuntimeMassReceipt
      floorSchedule data traceSourceLoss) :
    Nonempty
      (PureWZ2GrainRefinementData
        data.heightLift.shading sigma finalLoss) := by
  have hliftDense : data.heightLift.shading.IsLambdaDense
      (Kakeya.realRpowENN delta floorSchedule.densityLoss) := by
    simpa only [Kakeya.Streamlined.Shading.IsLambdaDense] using
      receipt.source_height_density
  have hsourceDensity : WZ2PaperCroppedIsExtremal
      sigma floorSchedule.densityLoss source.family source.shading :=
    source.extremal.mono_loss receipt.inputLoss_le_density
  have hliftDensity : WZ2PaperCroppedIsExtremal
      sigma floorSchedule.densityLoss source.family
        data.heightLift.shading :=
    { delta_pos := source.extremal.delta_pos
      delta_le_one := source.extremal.delta_le_one
      nonempty := source.extremal.nonempty
      cwa_nearby_scales := hsourceDensity.cwa_nearby_scales
      cubical := data.heightLift.whole_cells
      dense := hliftDense
      volume_upper :=
        (measure_mono data.heightLift.subshading.union_subset).trans
          hsourceDensity.volume_upper }
  have hinputFinal : inputLoss ≤ finalLoss :=
    receipt.inputLoss_le_density.trans floorSchedule.densityLoss_le_floor
  have hconstant :
      Kakeya.realRpowENN delta (-inputLoss) ≤
        Kakeya.realRpowENN delta (-finalLoss) :=
    pureWZ2_grain_constant_mono source.extremal.delta_pos
      source.extremal.delta_le_one hinputFinal
  have hconstantTop :
      Kakeya.realRpowENN delta (-finalLoss) ≠ ⊤ := by
    simp [Kakeya.realRpowENN]
  let localGrains := source.localGrains.restrictWithConstant
    data.heightLift.subshading hconstant hconstantTop
  let globalGrains :=
    source.globalGrains.toPureWZ2LipschitzGlobalGrainData.restrict
      data.heightLift.subshading hconstant hconstantTop
  have hvertical :
      ∀ point : {point : Point3 // point ∈ data.heightLift.shading.union},
        |localGrains.planeMap point (2 : Fin 3)| ≤ 1 / 2 := by
    intro point
    exact source.planeMap_vertical_bound
      ⟨point, data.heightLift.subshading.union_subset point.property⟩
  have htop : WZ2PaperConvexWolffBound source.family
      (Kakeya.realRpowENN delta (-finalLoss)) := by
    intro convexSet hconvex
    exact (reentry.cropped_top_level_cwa convexSet hconvex).trans <| by
      gcongr
  exact ⟨{
    shading := data.heightLift.shading
    subshading := fun _index _point hpoint => hpoint
    line_class := source.line_class
    cubical := data.heightLift.whole_cells
    extremal :=
      hliftDensity.mono_loss floorSchedule.densityLoss_le_floor
    top_level_cwa := htop
    volume_lower :=
      data.volumeLowerOfSourceReentryTraceSchedule
        floorSchedule reentry receipt
    globalGrains := globalGrains
    localGrains := localGrains
    planeMap_vertical_bound := hvertical
  }⟩

/-- Assemble the one-scale object from one exact refinement of the actual
height lift.  This is the post-refinement half of the ordinary paper-order
assembly, without an arbitrary-family producer. -/
theorem toOneScaleOfExactRefinement
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss normalEta
      theoremEta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {carriers : PureWZ2OrdinaryPaperOrderCarrierData twoScale}
    {prepared : PureWZ2OrdinaryPaperOrderPreparationData carriers}
    {graphData : PureWZ2OrdinaryPaperOrderGraphData
      (normalEta := normalEta) prepared}
    (data : PureWZ2OrdinaryPaperOrderRichGraphData
      (finalLoss := finalLoss) (theoremEta := theoremEta) graphData)
    (hinputFinal : inputLoss ≤ finalLoss)
    (refined : PureWZ2GrainRefinementData
      data.heightLift.shading sigma finalLoss) :
    Nonempty (PureWZ2LocallyLinearOneScaleData
      source finalLoss data.richTrapezoid.scale) := by
  have hsub :
      PureWZ2PaperIsSubshading refined.shading source.shading := by
    intro index point hpoint
    exact data.heightLift.subshading index
      (refined.subshading index hpoint)
  have hconstant :
      Kakeya.realRpowENN delta (-inputLoss) ≤
        Kakeya.realRpowENN delta (-finalLoss) :=
    pureWZ2_grain_constant_mono source.extremal.delta_pos
      source.extremal.delta_le_one hinputFinal
  have hconstantTop :
      Kakeya.realRpowENN delta (-finalLoss) ≠ ⊤ := by
    simp [Kakeya.realRpowENN]
  let localGrains := source.localGrains.restrictWithConstant
    hsub hconstant hconstantTop
  let globalGrains := source.globalGrains.restrict
    hsub hconstant hconstantTop
  have hvertical :
      ∀ point : {point : Point3 // point ∈ refined.shading.union},
        |localGrains.planeMap point (2 : Fin 3)| ≤ 1 / 2 := by
    intro point
    exact source.planeMap_vertical_bound
      ⟨point, hsub.union_subset point.property⟩
  let trapezoids : Finset WZ1VerticalTrapezoid :=
    {data.richTrapezoid.trapezoid}
  have hdeltaScale : delta ≤ data.richTrapezoid.scale := by
    calc
      delta ≤ prepared.prep.graphScale :=
        prepared.prep.sourceScale_le_graphScale
      _ ≤ 5 * prepared.prep.graphScale := by
        nlinarith [prepared.prep.graphScale_pos]
      _ = data.richTrapezoid.scale :=
        data.richTrapezoid.scale_eq.symm
  exact ⟨{
    rho_pos := data.richTrapezoid.scale_pos
    delta_le_rho := hdeltaScale
    rho_le_one := data.richTrapezoid.scale_le_one
    shading := refined.shading
    subshading := hsub
    whole_cells := refined.cubical
    extremal := refined.extremal
    volume_lower := refined.volume_lower
    localGrains := localGrains
    planeMap_vertical_bound := hvertical
    globalGrains := globalGrains
    slope_eq := rfl
    trapezoids := trapezoids
    trapezoids_nonempty := by simp [trapezoids]
    height_eq := by
      intro trapezoid htrapezoid
      simp only [trapezoids, Finset.mem_singleton] at htrapezoid
      subst trapezoid
      exact data.richTrapezoid.height_eq
    slope_bound := by
      intro trapezoid htrapezoid
      simp only [trapezoids, Finset.mem_singleton] at htrapezoid
      subst trapezoid
      exact data.richTrapezoid.slope_bound
    length_bounds := by
      intro trapezoid htrapezoid
      simp only [trapezoids, Finset.mem_singleton] at htrapezoid
      subst trapezoid
      exact data.richTrapezoid.length_bounds
    separated_cores := by
      intro first hfirst second hsecond hne
      simp only [trapezoids, Finset.mem_singleton] at hfirst hsecond
      exact False.elim (hne (hfirst.trans hsecond.symm))
    slope_approximation := by
      intro trapezoid htrapezoid z _hz hslice
      simp only [trapezoids, Finset.mem_singleton] at htrapezoid
      subst trapezoid
      apply data.heightLift.slope_approximation z
      rcases Set.nonempty_iff_ne_empty.mpr hslice with ⟨point, hpoint⟩
      apply Set.nonempty_iff_ne_empty.mp
      exact ⟨point, refined.subshading.union_subset hpoint.1, hpoint.2⟩
    active_height_coverage := by
      intro z _hz hslice
      refine ⟨data.richTrapezoid.trapezoid, by simp [trapezoids], ?_⟩
      apply data.heightLift.active_height_coverage z
      rcases Set.nonempty_iff_ne_empty.mpr hslice with ⟨point, hpoint⟩
      apply Set.nonempty_iff_ne_empty.mp
      exact ⟨point, refined.subshading.union_subset hpoint.1, hpoint.2⟩
  }⟩

/-- Final public-scale closure from the preselected trace-floor schedule, the
exact source re-entry, and one source-height runtime mass receipt. -/
theorem toOneScaleOfSourceReentryTraceSchedule
    {sigma finalLoss structuralBudget : ℝ}
    (floorSchedule : PureWZ2ReentryTraceFloorSchedule
      sigma finalLoss structuralBudget)
    {inputLoss delta rho middleLoss stickyLoss normalEta theoremEta
      traceSourceLoss : ℝ}
    {logExponent normalizationExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {carriers : PureWZ2OrdinaryPaperOrderCarrierData twoScale}
    {prepared : PureWZ2OrdinaryPaperOrderPreparationData carriers}
    {graphData : PureWZ2OrdinaryPaperOrderGraphData
      (normalEta := normalEta) prepared}
    (data : PureWZ2OrdinaryPaperOrderRichGraphData
      (finalLoss := finalLoss) (theoremEta := theoremEta) graphData)
    (reentry : PureWZ2PropStickyReentryData
      (sigma := sigma) source.shading normalizationExponent
      traceSourceLoss inputLoss)
    (receipt : PureWZ2OrdinaryPaperOrderSourceHeightRuntimeMassReceipt
      floorSchedule data traceSourceLoss) :
    Nonempty (PureWZ2LocallyLinearOneScaleData
      source finalLoss (pureWZ2SourceHorizontalFinalScale rho)) := by
  rcases data.exactRefinementOfSourceReentryTraceSchedule
      floorSchedule reentry receipt with ⟨refined⟩
  have hscale : data.richTrapezoid.scale =
      pureWZ2SourceHorizontalFinalScale rho := by
    rw [data.richTrapezoid.scale_eq, prepared.prep.graphScale_eq]
    simp [pureWZ2SourceHorizontalFinalScale]
    ring
  rw [← hscale]
  exact data.toOneScaleOfExactRefinement
    (receipt.inputLoss_le_density.trans
      floorSchedule.densityLoss_le_floor) refined

end PureWZ2OrdinaryPaperOrderRichGraphData

end Kakeya.Assouad

end
