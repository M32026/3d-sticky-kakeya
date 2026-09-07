import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62CoarseScaleDensity
import MyLeanRepo.Kakeya.Assouad.PureWZ2.PureCriticalFloorSelection
import MyLeanRepo.Kakeya.Assouad.PureWZ2.PureCriticalCoarseMultiplicityCap
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperLiteralImageMultiplicity
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperLiteralImageMultiplicityFloor

/-!
# Proposition 6.2: critical-floor multiplicity inputs

This module implements the two multiplicity estimates immediately after the
fine- and coarse-density paragraphs of the paper.

The critical lower-volume theorem is formulated for ordinary shadings.
Accordingly, the cropped terminal coarse shading carries an explicit volume
floor, while every terminal complete metric fiber carries an explicit
`PureWZ2CriticalRescaledFiberWitness`.  No cropped shading is silently passed
to the ordinary critical floor.

Both estimates remain on the terminal families and shadings produced by the
four-degree lemma.  There is no further tube-family selection.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

/--
The non-circular critical-floor witness for one terminal rescaled fiber.

Unlike `PureWZ2CriticalRescaledFiberWitness`, this record does not contain a
completed rescaled extremal output.  It stores only the literal target used by
the multiplicity argument and an ordinary pure critical configuration whose
union lies inside that target.
-/
structure PureWZ2Prop62CriticalRescaledFiberFloorWitness
    {delta rho loss : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    (sourceShading : WZ1PaperTubeShading fine)
    (parentTube : Kakeya.DeltaTube rho)
    (hrho : 0 < rho) where
  familyData :
    WZ2PaperLiteralUnitRescaledFamilyData
      fine parentTube hrho
  literalShading :
    WZ2PaperLiteralUnitRescaledShadingData
      familyData sourceShading
  ordinaryFamily :
    Kakeya.Streamlined.TubeFamily (delta / rho)
  ordinaryShading :
    Kakeya.Streamlined.TubeShading ordinaryFamily
  ordinary_nonempty :
    ordinaryFamily.Nonempty
  ordinary_cwa :
    WZ2PaperPureCWAAtNearbyScales ordinaryFamily
      (Kakeya.realRpowENN (delta / rho) (-loss))
  ordinary_dense :
    ordinaryShading.IsLambdaDense
      (Kakeya.realRpowENN (delta / rho) loss)
  ordinary_union_subset_target :
    ordinaryShading.union ⊆
      literalShading.targetShading.union

/--
Cancel a positive critical volume factor from the standard multiplicity-floor
and quadratic-mass comparison.
-/
theorem pureWZ2_multiplicity_cap_from_volume_floor_and_mass_upper
    {scale sigma floorLoss outputLoss : ℝ}
    (scalePos : 0 < scale)
    {bodyFamily : Kakeya.Streamlined.BodyFamily}
    (shading : Kakeya.Streamlined.Shading bodyFamily)
    (multiplicity cardinality massConstant : ENNReal)
    (volumeFloor :
      Kakeya.realRpowENN scale (sigma + floorLoss) ≤
        volume shading.union)
    (multiplicityFloor :
      ∀ point ∈ shading.union,
        multiplicity ≤
          (shading.pointMultiplicity point : ENNReal))
    (massUpper :
      shading.mass ≤
        massConstant * Kakeya.realRpowENN scale 2 * cardinality)
    (constantAbsorption :
      massConstant ≤
        Kakeya.realRpowENN scale (-(outputLoss - floorLoss))) :
    multiplicity ≤
      Kakeya.realRpowENN scale (2 - sigma - outputLoss) *
        cardinality := by
  have floorMass :
      multiplicity *
          Kakeya.realRpowENN scale (sigma + floorLoss) ≤
        shading.mass := by
    calc
      multiplicity *
            Kakeya.realRpowENN scale (sigma + floorLoss) ≤
          multiplicity * volume shading.union := by
        gcongr
      _ ≤ shading.mass :=
        multiplicity_floor_le_mass multiplicityFloor
  have absorbed :
      multiplicity *
          Kakeya.realRpowENN scale (sigma + floorLoss) ≤
        Kakeya.realRpowENN scale
            (2 + floorLoss - outputLoss) *
          cardinality := by
    calc
      multiplicity *
            Kakeya.realRpowENN scale (sigma + floorLoss) ≤
          massConstant *
            Kakeya.realRpowENN scale 2 * cardinality :=
        floorMass.trans massUpper
      _ ≤
          Kakeya.realRpowENN scale (-(outputLoss - floorLoss)) *
            Kakeya.realRpowENN scale 2 * cardinality := by
        gcongr
      _ =
          Kakeya.realRpowENN scale
              (2 + floorLoss - outputLoss) *
            cardinality := by
        rw [realRpowENN_mul' scalePos]
        congr 1
        ring
  have factorization :
      Kakeya.realRpowENN scale (2 + floorLoss - outputLoss) =
        Kakeya.realRpowENN scale (sigma + floorLoss) *
          Kakeya.realRpowENN scale
            (2 - sigma - outputLoss) := by
    rw [realRpowENN_mul' scalePos]
    congr 1
    ring
  have floorFactor_ne_zero :
      Kakeya.realRpowENN scale (sigma + floorLoss) ≠ 0 := by
    simp [Kakeya.realRpowENN, Real.rpow_pos_of_pos scalePos]
  have floorFactor_ne_top :
      Kakeya.realRpowENN scale (sigma + floorLoss) ≠ ⊤ := by
    simp [Kakeya.realRpowENN]
  apply
    (ENNReal.mul_le_mul_iff_right
      floorFactor_ne_zero floorFactor_ne_top).mp
  calc
    Kakeya.realRpowENN scale (sigma + floorLoss) *
          multiplicity =
        multiplicity *
          Kakeya.realRpowENN scale (sigma + floorLoss) := by
      ring
    _ ≤
        Kakeya.realRpowENN scale
            (2 + floorLoss - outputLoss) *
          cardinality :=
      absorbed
    _ =
        Kakeya.realRpowENN scale (sigma + floorLoss) *
          (Kakeya.realRpowENN scale
              (2 - sigma - outputLoss) *
            cardinality) := by
      rw [factorization]
      ring

namespace PureWZ2Prop62PacketCellInput

variable
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {sourceShading : WZ1PaperTubeShading fine}
    (input : PureWZ2Prop62PacketCellInput cover sourceShading)
    (multiplicity : input.FineMultiplicityClassData)
    (parentClass : input.ParentClassData multiplicity)
    {ambientConstant scaleWindow : ENNReal}
    {schedule :
      PureWZ2Prop62LaminarPureSchedule
        coarse ambientConstant scaleWindow}
    (treeCleanup :
      input.ParentTreeCleanupData
        multiplicity parentClass schedule)
    (exactification :
      input.PacketCellExactificationData
        multiplicity parentClass treeCleanup)
    (parentDegree :
      input.ReferenceParentDegreeData
        multiplicity parentClass treeCleanup exactification)
    {bins :
      exactification.incidence.ThreeDegreeBinningData
        exactification.incidence.allEdges}
    {A0 : ℕ}
    (core :
      input.FourDegreeCoreAssemblyData
        multiplicity parentClass treeCleanup
        exactification parentDegree bins A0)
    {degreeLoss : ℕ}
    (good : core.ranges.GoodBalancingSampleData degreeLoss)
    (families :
      input.TerminalCompleteFamiliesData
        multiplicity parentClass treeCleanup exactification
          core.ranges)
    {fiberConstant densityConstant : ENNReal}
    {logExponent : ℕ}
    (output :
      input.FourDegreeLemmaOutputData
        multiplicity parentClass treeCleanup exactification
          parentDegree core good families
          fiberConstant densityConstant logExponent)

namespace FourDegreeLemmaOutputData

/--
The point multiplicity of the locally indexed terminal fiber shading is
exactly the metric-fiber point multiplicity on the final fine family.
-/
theorem terminalFiberShading_pointMultiplicity_eq
    (parent :
      Fin families.restriction.coarseSelected.family.card)
    (point : Point3) :
    (output.terminalFiberShading
      input multiplicity parentClass treeCleanup exactification
        parentDegree core good families parent).pointMultiplicity point =
      families.restriction.lineCover.fiberPointMultiplicity
        output.fineShading parent point := by
  let indices :=
    wz2PaperFullFiberIndices
      families.restriction.fineSelected.family
      families.restriction.coarseSelected.family parent
  let localFiber :=
    families.terminalFiber
      input multiplicity parentClass treeCleanup exactification
        parentDegree core parent
  let localActive : Finset (Fin localFiber.family.card) :=
    Finset.univ.filter fun source =>
      point ∈
        (output.terminalFiberShading
          input multiplicity parentClass treeCleanup exactification
            parentDegree core good families parent).carrier source
  let ambientActive :
      Finset
        (Fin families.restriction.fineSelected.family.card) :=
    indices.filter fun source =>
      point ∈ output.fineShading.carrier source
  have activeCard : localActive.card = ambientActive.card := by
    apply Finset.card_bij
      (fun source _ => localFiber.embedding source)
    · intro source sourceMem
      apply Finset.mem_filter.mpr
      refine
        ⟨Finset.orderEmbOfFin_mem indices rfl source, ?_⟩
      exact (Finset.mem_filter.mp sourceMem).2
    · intro first _ second _ equality
      exact localFiber.embedding.injective equality
    · intro source sourceMem
      let enumeration : Fin indices.card ≃ indices :=
        (indices.orderIsoOfFin rfl).toEquiv
      let localSource : Fin localFiber.family.card :=
        enumeration.symm
          ⟨source, (Finset.mem_filter.mp sourceMem).1⟩
      have embeddingEq :
          localFiber.embedding localSource = source :=
        congrArg Subtype.val <|
          enumeration.apply_symm_apply
            ⟨source, (Finset.mem_filter.mp sourceMem).1⟩
      refine ⟨localSource, ?_, embeddingEq⟩
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      change
        point ∈
          output.fineShading.carrier
            (localFiber.embedding localSource)
      rw [embeddingEq]
      exact (Finset.mem_filter.mp sourceMem).2
  change localActive.card =
    ((families.restriction.lineCover.fiberIndices parent).filter
      fun source =>
        point ∈ output.fineShading.carrier source).card
  rw [show
      families.restriction.lineCover.fiberIndices parent =
        indices by
    ext source
    exact
      mem_lineCover_fiberIndices_iff_fullFiber
        input multiplicity parentClass treeCleanup exactification
          parentDegree core families parent source]
  exact activeCard

theorem terminalFiberShading_multiplicity_lower
    (parent :
      Fin families.restriction.coarseSelected.family.card)
    {point : Point3}
    (pointMem :
      point ∈
        (output.terminalFiberShading
          input multiplicity parentClass treeCleanup exactification
            parentDegree core good families parent).union) :
    (output.muFine : ENNReal) ≤
      (output.terminalFiberShading
        input multiplicity parentClass treeCleanup exactification
          parentDegree core good families parent).pointMultiplicity point := by
  let sourceFiberShading :=
    output.terminalFiberShading
      input multiplicity parentClass treeCleanup exactification
        parentDegree core good families parent
  have sourcePositive :
      0 < sourceFiberShading.pointMultiplicity point := by
    rcases pointMem with ⟨source, sourceMem⟩
    apply Finset.card_pos.mpr
    exact
      ⟨source,
        Finset.mem_filter.mpr
          ⟨Finset.mem_univ source, sourceMem⟩⟩
  have fiberPositive :
      0 <
        families.restriction.lineCover.fiberPointMultiplicity
          output.fineShading parent point := by
    rw [← output.terminalFiberShading_pointMultiplicity_eq
      input multiplicity parentClass treeCleanup exactification
        parentDegree core good families parent point]
    exact sourcePositive
  have exactMultiplicity :=
    output.fiber_pointMultiplicity_eq_muFine_of_pos
      input multiplicity parentClass treeCleanup exactification
        parentDegree core good families parent point fiberPositive
  rw [output.terminalFiberShading_pointMultiplicity_eq
    input multiplicity parentClass treeCleanup exactification
      parentDegree core good families parent point,
    exactMultiplicity]

structure CriticalMultiplicityInputsData
    {sigma floorLoss capLoss : ℝ}
    (critical :
      PureWZ2CriticalFloorSelectionData
        sigma floorLoss capLoss) : Prop where
  rho_small : rho ≤ 1 / 24
  ratio_small : delta / rho ≤ 1 / 24
  ratio_critical : delta / rho ≤ critical.delta₀
  coarse_volume_floor :
    Kakeya.realRpowENN rho (sigma + floorLoss) ≤
      volume output.coarseShading.union
  fiber_witness :
    ∀ parent :
        Fin families.restriction.coarseSelected.family.card,
      Nonempty
        (PureWZ2Prop62CriticalRescaledFiberFloorWitness
          (loss := critical.structuralLoss)
          (output.terminalFiberShading
            input multiplicity parentClass treeCleanup exactification
              parentDegree core good families parent)
          (families.restriction.coarseSelected.family.tube parent)
          input.rho_pos)
  coarse_constant_absorption :
    55296 * Kakeya.deltaTubeVolume 1 ≤
      Kakeya.realRpowENN rho (-(capLoss - floorLoss))
  fine_constant_absorption :
    55296 * Kakeya.deltaTubeVolume 1 ≤
      Kakeya.realRpowENN (delta / rho)
        (-(capLoss - floorLoss))

theorem coarse_multiplicity_upper_of_critical_inputs
    {sigma floorLoss capLoss : ℝ}
    (critical :
      PureWZ2CriticalFloorSelectionData
        sigma floorLoss capLoss)
    (criticalInputs :
      output.CriticalMultiplicityInputsData
        input multiplicity parentClass treeCleanup exactification
          parentDegree core good families critical) :
    (output.muCoarse : ENNReal) ≤
      Kakeya.realRpowENN rho (2 - sigma - capLoss) *
        families.restriction.coarseSelected.family.enncard := by
  apply
    pureWZ2_multiplicity_cap_from_volume_floor_and_mass_upper
      input.rho_pos output.coarseShading
      output.muCoarse
      families.restriction.coarseSelected.family.enncard
      (55296 * Kakeya.deltaTubeVolume 1)
      criticalInputs.coarse_volume_floor
      (fun point pointMem =>
        output.coarse_pointMultiplicity_lower
          input multiplicity parentClass treeCleanup exactification
            parentDegree core good families pointMem)
  · exact
      wz2_paper_shading_mass_upper
        input.rho_pos criticalInputs.rho_small
        families.restriction.section6Cover.coarse_line_class
        output.coarseShading
  · exact criticalInputs.coarse_constant_absorption

theorem fine_multiplicity_upper_of_critical_inputs
    {sigma floorLoss capLoss : ℝ}
    (critical :
      PureWZ2CriticalFloorSelectionData
        sigma floorLoss capLoss)
    (criticalInputs :
      output.CriticalMultiplicityInputsData
        input multiplicity parentClass treeCleanup exactification
          parentDegree core good families critical) :
    ∀ parent :
        Fin families.restriction.coarseSelected.family.card,
      (output.muFine : ENNReal) ≤
        Kakeya.realRpowENN (delta / rho)
            (2 - sigma - capLoss) *
          (families.terminalFiber
            input multiplicity parentClass treeCleanup exactification
              parentDegree core parent).family.enncard := by
  intro parent
  let sourceFamily :=
    (families.terminalFiber
      input multiplicity parentClass treeCleanup exactification
        parentDegree core parent).family
  let sourceFiberShading :=
    output.terminalFiberShading
      input multiplicity parentClass treeCleanup exactification
        parentDegree core good families parent
  let witness := Classical.choice (criticalInputs.fiber_witness parent)
  let targetShading := witness.literalShading.targetShading
  have ratioPos : 0 < delta / rho :=
    div_pos input.delta_pos input.rho_pos
  have sourceFloor :
      ∀ point ∈ sourceFiberShading.union,
        (output.muFine : ENNReal) ≤
          (sourceFiberShading.pointMultiplicity point : ENNReal) := by
    intro point pointMem
    exact
      output.terminalFiberShading_multiplicity_lower
      input multiplicity parentClass treeCleanup exactification
        parentDegree core good families parent pointMem
  have targetFloor :
      ∀ point ∈ targetShading.union,
        (output.muFine : ENNReal) ≤
          (targetShading.pointMultiplicity point : ENNReal) :=
    wz2_paper_literal_image_multiplicity_floor
      wz2_paper_literal_image_multiplicity
      witness.familyData sourceFiberShading
      witness.literalShading output.muFine sourceFloor
  have ordinaryVolumeFloor :
      Kakeya.realRpowENN (delta / rho)
          (sigma + floorLoss) ≤
        volume witness.ordinaryShading.union :=
    critical.volume_floor
      (delta / rho) ratioPos criticalInputs.ratio_critical
      witness.ordinaryFamily witness.ordinary_nonempty
      witness.ordinaryShading witness.ordinary_cwa
      witness.ordinary_dense
  have targetVolumeFloor :
      Kakeya.realRpowENN (delta / rho)
          (sigma + floorLoss) ≤
        volume targetShading.union :=
    ordinaryVolumeFloor.trans <|
      measure_mono witness.ordinary_union_subset_target
  have targetMassUpper :
      targetShading.mass ≤
        (55296 * Kakeya.deltaTubeVolume 1) *
          Kakeya.realRpowENN (delta / rho) 2 *
          sourceFamily.enncard := by
    have targetCardinality :=
      (wz2_paper_literal_image_multiplicity
        (familyData := witness.familyData)
        (sourceShading := sourceFiberShading)
        (shadingData := witness.literalShading)).1
    have raw :=
      wz2_paper_shading_mass_upper
        ratioPos criticalInputs.ratio_small
        witness.familyData.target_line_class targetShading
    calc
      targetShading.mass ≤
          (55296 * Kakeya.deltaTubeVolume 1) *
            Kakeya.realRpowENN (delta / rho) 2 *
            witness.familyData.targetFamily.enncard :=
        raw
      _ =
          (55296 * Kakeya.deltaTubeVolume 1) *
            Kakeya.realRpowENN (delta / rho) 2 *
            sourceFamily.enncard := by
        rw [targetCardinality]
  exact
    pureWZ2_multiplicity_cap_from_volume_floor_and_mass_upper
      ratioPos targetShading output.muFine sourceFamily.enncard
      (55296 * Kakeya.deltaTubeVolume 1)
      targetVolumeFloor targetFloor targetMassUpper
      criticalInputs.fine_constant_absorption

/--
The final power gap from the critical multiplicity exponent to the public
Proposition 6.2 exponent.  The coarse field absorbs the frozen
`4 * A0^2` loss; the fine field only weakens the exponent.
-/
structure PublicMultiplicityAbsorptionData
    (sigma capLoss publicLoss : ℝ) : Prop where
  coarse_scalar :
    (output.coarseLoss : ENNReal) *
        Kakeya.realRpowENN rho (2 - sigma - capLoss) ≤
      Kakeya.realRpowENN rho (2 - sigma - publicLoss)
  fine_scalar :
    Kakeya.realRpowENN (delta / rho)
        (2 - sigma - capLoss) ≤
      Kakeya.realRpowENN (delta / rho)
        (2 - sigma - publicLoss)

/-- Conclusion (iii) on the exact terminal coarse family and shading. -/
theorem coarse_pointMultiplicity_upper_of_critical_inputs
    {sigma floorLoss capLoss publicLoss : ℝ}
    (critical :
      PureWZ2CriticalFloorSelectionData
        sigma floorLoss capLoss)
    (criticalInputs :
      output.CriticalMultiplicityInputsData
        input multiplicity parentClass treeCleanup exactification
          parentDegree core good families critical)
    (absorption :
      output.PublicMultiplicityAbsorptionData
        input multiplicity parentClass treeCleanup exactification
          parentDegree core good families
          sigma capLoss publicLoss) :
    ∀ point,
      (output.coarseShading.pointMultiplicity point : ENNReal) ≤
        Kakeya.realRpowENN rho
            (2 - sigma - publicLoss) *
          families.restriction.coarseSelected.family.enncard := by
  intro point
  have multiplicityCap :=
    output.coarse_multiplicity_upper_of_critical_inputs
      input multiplicity parentClass treeCleanup exactification
        parentDegree core good families critical criticalInputs
  calc
    (output.coarseShading.pointMultiplicity point : ENNReal) ≤
        ((output.coarseLoss * output.muCoarse : ℕ) : ENNReal) :=
      output.coarse_pointMultiplicity_le
        input multiplicity parentClass treeCleanup exactification
          parentDegree core good families point
    _ =
        (output.coarseLoss : ENNReal) *
          (output.muCoarse : ENNReal) := by
      simp
    _ ≤
        (output.coarseLoss : ENNReal) *
          (Kakeya.realRpowENN rho
              (2 - sigma - capLoss) *
            families.restriction.coarseSelected.family.enncard) := by
      gcongr
    _ =
        ((output.coarseLoss : ENNReal) *
          Kakeya.realRpowENN rho
            (2 - sigma - capLoss)) *
          families.restriction.coarseSelected.family.enncard := by
      ring
    _ ≤
        Kakeya.realRpowENN rho
            (2 - sigma - publicLoss) *
          families.restriction.coarseSelected.family.enncard := by
      gcongr
      exact absorption.coarse_scalar

/-- The public pointwise bound inside one terminal complete metric fiber. -/
theorem terminalFiber_pointMultiplicity_upper_of_critical_inputs
    {sigma floorLoss capLoss publicLoss : ℝ}
    (critical :
      PureWZ2CriticalFloorSelectionData
        sigma floorLoss capLoss)
    (criticalInputs :
      output.CriticalMultiplicityInputsData
        input multiplicity parentClass treeCleanup exactification
          parentDegree core good families critical)
    (absorption :
      output.PublicMultiplicityAbsorptionData
        input multiplicity parentClass treeCleanup exactification
          parentDegree core good families
          sigma capLoss publicLoss) :
    ∀ parent point,
      (families.restriction.lineCover.fiberPointMultiplicity
          output.fineShading parent point : ENNReal) ≤
        Kakeya.realRpowENN (delta / rho)
            (2 - sigma - publicLoss) *
          (families.terminalFiber
            input multiplicity parentClass treeCleanup exactification
              parentDegree core parent).family.enncard := by
  intro parent point
  have multiplicityCap :=
    output.fine_multiplicity_upper_of_critical_inputs
      input multiplicity parentClass treeCleanup exactification
        parentDegree core good families critical criticalInputs parent
  calc
    (families.restriction.lineCover.fiberPointMultiplicity
        output.fineShading parent point : ENNReal) ≤
        (output.muFine : ENNReal) :=
      output.fiber_pointMultiplicity_le
        input multiplicity parentClass treeCleanup exactification
          parentDegree core good families parent point
    _ ≤
        Kakeya.realRpowENN (delta / rho)
            (2 - sigma - capLoss) *
          (families.terminalFiber
            input multiplicity parentClass treeCleanup exactification
              parentDegree core parent).family.enncard :=
      multiplicityCap
    _ ≤
        Kakeya.realRpowENN (delta / rho)
            (2 - sigma - publicLoss) *
          (families.terminalFiber
            input multiplicity parentClass treeCleanup exactification
              parentDegree core parent).family.enncard := by
      gcongr
      exact absorption.fine_scalar

/-- Conclusion (iv), written with the literal genuine metric-fiber finset. -/
theorem fine_pointMultiplicity_upper_of_critical_inputs
    {sigma floorLoss capLoss publicLoss : ℝ}
    (critical :
      PureWZ2CriticalFloorSelectionData
        sigma floorLoss capLoss)
    (criticalInputs :
      output.CriticalMultiplicityInputsData
        input multiplicity parentClass treeCleanup exactification
          parentDegree core good families critical)
    (absorption :
      output.PublicMultiplicityAbsorptionData
        input multiplicity parentClass treeCleanup exactification
          parentDegree core good families
          sigma capLoss publicLoss) :
    ∀ parent point,
      (((wz2PaperFullFiberIndices
          families.restriction.fineSelected.family
          families.restriction.coarseSelected.family parent).filter
          fun source =>
            point ∈ output.fineShading.carrier source).card : ENNReal) ≤
        Kakeya.realRpowENN (delta / rho)
            (2 - sigma - publicLoss) *
          ((wz2PaperFullFiberIndices
            families.restriction.fineSelected.family
            families.restriction.coarseSelected.family parent).card :
              ENNReal) := by
  intro parent point
  have pointwise :=
    output.terminalFiber_pointMultiplicity_upper_of_critical_inputs
      input multiplicity parentClass treeCleanup exactification
        parentDegree core good families
        critical criticalInputs absorption parent point
  let fiberIndices :=
    wz2PaperFullFiberIndices
      families.restriction.fineSelected.family
      families.restriction.coarseSelected.family parent
  have lineFiberEq :
      families.restriction.lineCover.fiberIndices parent =
        fiberIndices := by
    ext source
    exact
      mem_lineCover_fiberIndices_iff_fullFiber
        input multiplicity parentClass treeCleanup exactification
          parentDegree core families parent source
  change
    ((fiberIndices.filter fun source =>
      point ∈ output.fineShading.carrier source).card : ENNReal) ≤
      Kakeya.realRpowENN (delta / rho)
          (2 - sigma - publicLoss) *
        (fiberIndices.card : ENNReal)
  change
    (((families.restriction.lineCover.fiberIndices parent).filter
      fun source =>
        point ∈ output.fineShading.carrier source).card : ENNReal) ≤
      Kakeya.realRpowENN (delta / rho)
          (2 - sigma - publicLoss) *
        (fiberIndices.card : ENNReal) at pointwise
  rw [lineFiberEq] at pointwise
  exact pointwise

end FourDegreeLemmaOutputData

end PureWZ2Prop62PacketCellInput

end Kakeya.Assouad

end
