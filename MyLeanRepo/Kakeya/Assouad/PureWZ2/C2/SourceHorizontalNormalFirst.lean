import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceHorizontalFineWitnesses
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.CoarseGlobalPreparation
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SecondStageSources
import MyLeanRepo.Kakeya.Assouad.WZ1.GeneralizedThickening
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23ProjectionHeavyFiberInSource
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23FullGrainNormalBound

/-!
# Large first component for the original source normals

For each retained residue parent, the second sticky refinement supplies a
strong source in the full side-`sqrt rho` cell.  Its projection is controlled
by original source witnesses in the first-stage side-`rho` cells.  The
certificate runs at the auxiliary scale `4 * rho`; only the resulting lower
bound for the original source normal is retained.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

private lemma sourceHorizontal_Ico_containment_closure
    {a b left right : ℝ} (hab : a < b)
    (hsub : Set.Ico a b ⊆ Set.Icc left right) :
    Set.Icc a b ⊆ Set.Icc left right := by
  rw [← closure_Ico hab.ne]
  exact closure_minimal hsub isClosed_Icc

structure PureWZ2SourceHorizontalFixedBinNormalFirstCertificate
    {sigma inputLoss delta rho middleLoss outputLoss eta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    {line : PureWZ2SourceHorizontalFixedBinData window}
    {parents : PureWZ2SourceHorizontalFixedBinParentData line}
    {selection : PureWZ2SourceHorizontalFixedBinYSelection parents}
    {residue : PureWZ2SourceHorizontalFixedBinYResidueData selection}
    {retained : PureWZ2SourceHorizontalFixedBinResidueShadingData residue}
    (fineWitnesses : PureWZ2SourceHorizontalFixedBinFineWitnessData retained) where
  certificateScale : ℝ := 4 * rho
  certificateScale_eq : certificateScale = 4 * rho
  strongSource : ∀ parent, parent ∈ residue.selected →
    PureWZ2SecondStageSourceData twoScale
  strongSource_cell : ∀ parent (hparent : parent ∈ residue.selected),
    (strongSource parent hparent).cell = parent
  normal_first : ∀ parent ∈ residue.selected,
    1 / 4 ≤ |fineWitnesses.normal parent (0 : Fin 3)|

theorem PureWZ2SourceHorizontalFixedBinFineWitnessData.normalFirstOfGlobalFixedBin
    {sigma inputLoss delta rho middleLoss outputLoss eta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    {line : PureWZ2SourceHorizontalFixedBinData window}
    {parents : PureWZ2SourceHorizontalFixedBinParentData line}
    {selection : PureWZ2SourceHorizontalFixedBinYSelection parents}
    {residue : PureWZ2SourceHorizontalFixedBinYResidueData selection}
    {retained : PureWZ2SourceHorizontalFixedBinResidueShadingData residue}
    (fineWitnesses : PureWZ2SourceHorizontalFixedBinFineWitnessData retained)
    (globalCarrier : Set Point3)
    (globalSlope : ℝ → ℝ)
    (hglobalSlopeBound :
      ∀ z ∈ Set.Icc (-1 : ℝ) 1, |globalSlope z| ≤ 3)
    (hglobalAD :
      ∀ z ∈ Set.Icc (-1 : ℝ) 1,
        IsADSet1
          (scalarProjection (globalGrainDirection (globalSlope z))
            (horizontalSlice globalCarrier z))
          rho (1 - sigma)
          (10 * Kakeya.realRpowENN rho (-middleLoss)))
    (hglobalCarrier :
      ∀ parent ∈ residue.selected,
        twoScale.fine.refined.union ∩
            wz1PaperGridCube twoScale.sqrtRequested.1 parent ⊆
          globalCarrier)
    (hbridge : PureWZ2PaperADBridgeStatement)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (heta : 0 < eta) (hetaSigma : 4 * eta < sigma)
    (hcertificateOne : 4 * rho ≤ 1)
    (hsourceFloor :
      Kakeya.realRpowENN (4 * rho)
          (3 / 2 + sigma / 2 + eta) ≤
        Kakeya.realRpowENN rho
          (3 / 2 + sigma / 2 + 3 * outputLoss / 2))
    (hlocalPower :
      160 * Kakeya.realRpowENN delta (-inputLoss) ≤
        Kakeya.realRpowENN (4 * rho) (-eta))
    (hglobalPower :
      10 * Kakeya.realRpowENN rho (-middleLoss) ≤
        Kakeya.realRpowENN (4 * rho) (-eta))
    (hPlanarSmall : 32 * Real.rpow (4 * rho) eta ≤ 1)
    (hrootSmall20 : 20 * Real.sqrt (4 * rho) ≤ 1)
    (habsorb :
      Real.rpow (4 * rho) (1 - 4 * eta / sigma) ≤
        Real.sqrt (4 * rho) / 14) :
    Nonempty
      (PureWZ2SourceHorizontalFixedBinNormalFirstCertificate
        (eta := eta) fineWitnesses) := by
  let certificateScale := 4 * rho
  let root := twoScale.sqrtRequested.1
  let localC : ENNReal :=
    160 * Kakeya.realRpowENN delta (-inputLoss)
  let globalC : ENNReal :=
    10 * Kakeya.realRpowENN rho (-middleLoss)
  have hdeltaRho : delta ≤ rho := by
    rw [← twoScale.rhoRequested_eq]
    exact twoScale.rhoRequested.property.1
  have hrho : 0 < rho := source.extremal.delta_pos.trans_le hdeltaRho
  have hcertificate : 0 < certificateScale := by positivity
  have hrhoCertificate : rho ≤ certificateScale := by
    dsimp only [certificateScale]
    nlinarith
  have hdeltaCertificate : delta ≤ certificateScale :=
    hdeltaRho.trans hrhoCertificate
  have hroot : 0 < root := twoScale.fine.coarse_extremal.delta_pos
  have hsqrtCertificate : Real.sqrt certificateScale = 2 * root := by
    rw [show certificateScale = 4 * rho by rfl, Real.sqrt_mul (by norm_num)]
    rw [show Real.sqrt (4 : ℝ) = 2 by norm_num, ← twoScale.sqrtRequested_eq]
  have hparentActive : ∀ parent ∈ residue.selected,
      parent ∈ twoScale.fine.balanced.activeCells := by
    intro parent hparent
    exact parents.parents_subset
      (selection.selected_subset (residue.selected_subset hparent))
  have hsourceExists :
      ∀ parent (hparent : parent ∈ residue.selected),
        ∃ data : PureWZ2SecondStageSourceData twoScale, data.cell = parent := by
    intro parent hparent
    exact twoScale.secondStageSourceAt parent (hparentActive parent hparent)
  let strongSource :
      ∀ parent, parent ∈ residue.selected →
        PureWZ2SecondStageSourceData twoScale := fun parent hparent =>
    Classical.choose (hsourceExists parent hparent)
  have hstrongCell :
      ∀ parent (hparent : parent ∈ residue.selected),
        (strongSource parent hparent).cell = parent := by
    intro parent hparent
    exact Classical.choose_spec (hsourceExists parent hparent)
  have hnormalFirst :
      ∀ parent (hparent : parent ∈ residue.selected),
        1 / 4 ≤ |fineWitnesses.normal parent (0 : Fin 3)| := by
    intro parent hparent
    let data := strongSource parent hparent
    let anchorCell := retained.cellFor parent
    let anchor := fineWitnesses.witness parent
    let normal := fineWitnesses.normal parent
    let strongSet := data.fullSource
    have hanchorSource : anchor ∈ source.shading.union :=
      fineWitnesses.witness_mem_source parent hparent
    have hanchorParent : anchor ∈ wz1PaperGridCube root parent :=
      fineWitnesses.witness_mem_parent parent hparent
    have hstrongMeasurable : MeasurableSet strongSet :=
      data.fullSource_measurable
    have hstrongNonempty : strongSet.Nonempty := data.fullSource_nonempty
    have hstrongParent :
        ∀ point ∈ strongSet, point ∈ wz1PaperGridCube root parent := by
      intro point hpoint
      dsimp only [strongSet] at hpoint
      rw [data.fullSource_eq] at hpoint
      have hcell := hpoint.2
      rwa [hstrongCell parent hparent] at hcell
    have hstrongBall :
        strongSet ⊆ Metric.closedBall anchor (Real.sqrt certificateScale) := by
      intro point hpoint
      rw [Metric.mem_closedBall, hsqrtCertificate]
      exact le_of_lt
        (wz1_paper_grid_cube_diameter_lt_two_rho hroot
          (hstrongParent point hpoint) hanchorParent)
    have hownerExists :
        ∀ point (hpoint : point ∈ strongSet),
          ∃ cell ∈ fineWitnesses.coarseWitnesses.activeCells,
            point ∈ wz1PaperGridCube rho cell := by
      intro point hpoint
      have hfull := hpoint
      dsimp only [strongSet] at hfull
      rw [data.fullSource_eq] at hfull
      rcases hfull.1 with ⟨fineIndex, hfineIndex⟩
      have hcoarseGrain :
          point ∈ twoScale.coarseGrains.shading.carrier
            (twoScale.fine.selected.embedding fineIndex) :=
        twoScale.fine.subshading fineIndex hfineIndex
      have hcropped : point ∈ twoScale.coarse.croppedCoarseShading.union :=
        ⟨twoScale.fine.selected.embedding fineIndex,
          twoScale.coarseGrains.subshading
            (twoScale.fine.selected.embedding fineIndex) hcoarseGrain⟩
      rw [twoScale.coarse.balanced.coarse_union_eq] at hcropped
      rcases Set.mem_iUnion₂.mp hcropped with ⟨cell, hcell, hpointCell⟩
      refine ⟨cell, ?_, by simpa only [twoScale.rhoRequested_eq] using hpointCell⟩
      rwa [fineWitnesses.coarseWitnesses.activeCells_eq]
    let ownerCell : Point3 → (ℤ × ℤ × ℤ) := fun point =>
      if hpoint : point ∈ strongSet then
        Classical.choose (hownerExists point hpoint) else anchorCell
    have hownerActive :
        ∀ point (hpoint : point ∈ strongSet),
          ownerCell point ∈ fineWitnesses.coarseWitnesses.activeCells := by
      intro point hpoint
      simp only [ownerCell, dif_pos hpoint]
      exact (Classical.choose_spec (hownerExists point hpoint)).1
    have hpointOwner :
        ∀ point (hpoint : point ∈ strongSet),
          point ∈ wz1PaperGridCube rho (ownerCell point) := by
      intro point hpoint
      simp only [ownerCell, dif_pos hpoint]
      exact (Classical.choose_spec (hownerExists point hpoint)).2
    have hownerWitnessParent :
        ∀ point (hpoint : point ∈ strongSet),
          fineWitnesses.coarseWitnesses.witness (ownerCell point) ∈
            wz1PaperGridCube root parent := by
      intro point hpoint
      have hfull := hpoint
      dsimp only [strongSet] at hfull
      rw [data.fullSource_eq] at hfull
      rcases hfull.1 with ⟨fineIndex, hfineIndex⟩
      rcases twoScale.fine.balanced.fine_cell_nested
          fineIndex point hfineIndex with
        ⟨secondParent, hsecondParent, hnested⟩
      have hcanonical :
          point ∈ wz1PaperGridCube twoScale.rhoRequested.1
            (wz1PaperGridIndex twoScale.rhoRequested.1 point) :=
        (mem_wz1PaperGridCube _ _ _).mpr rfl
      have hpointSecond :
          point ∈ wz1PaperGridCube root secondParent := hnested hcanonical
      have hpointParent' : point ∈ wz1PaperGridCube root parent :=
        hstrongParent point hpoint
      have hsecondEq : secondParent = parent :=
        ((mem_wz1PaperGridCube root secondParent point).mp hpointSecond).symm.trans
          ((mem_wz1PaperGridCube root parent point).mp hpointParent')
      have hownerEq :
          ownerCell point = wz1PaperGridIndex rho point :=
        ((mem_wz1PaperGridCube rho (ownerCell point) point).mp
          (hpointOwner point hpoint)).symm
      have hwitnessOwner :=
        fineWitnesses.coarseWitnesses.witness_mem_cell
          (ownerCell point) (hownerActive point hpoint)
      rw [hownerEq] at hwitnessOwner
      have hwitnessAtRequested :
          fineWitnesses.coarseWitnesses.witness (ownerCell point) ∈
            wz1PaperGridCube twoScale.rhoRequested.1
              (wz1PaperGridIndex twoScale.rhoRequested.1 point) := by
        simpa [twoScale.rhoRequested_eq, hownerEq] using hwitnessOwner
      rw [← hsecondEq]
      exact hnested hwitnessAtRequested
    have hownerWitnessBall :
        ∀ point (hpoint : point ∈ strongSet),
          fineWitnesses.coarseWitnesses.witness (ownerCell point) ∈
            Metric.closedBall anchor (Real.sqrt certificateScale) := by
      intro point hpoint
      rw [Metric.mem_closedBall, hsqrtCertificate]
      exact le_of_lt
        (wz1_paper_grid_cube_diameter_lt_two_rho hroot
          (hownerWitnessParent point hpoint) hanchorParent)
    have hnormalUnit : ‖normal‖ = 1 :=
      fineWitnesses.normal_unit parent hparent
    have hsourceAD :
        IsADSet1
          (scalarProjection normal
            (source.shading.union ∩
              Metric.closedBall anchor (Real.sqrt certificateScale)))
          certificateScale (1 - sigma)
          (10 * Kakeya.realRpowENN delta (-inputLoss)) := by
      have hliteral := source.localGrains.local_ad
        certificateScale hdeltaCertificate hcertificateOne
        ⟨anchor, hanchorSource⟩
      have hnormalEq :
          normal = source.localGrains.planeMap ⟨anchor, hanchorSource⟩ :=
        fineWitnesses.normal_eq parent hparent
      rw [hnormalEq]
      exact hbridge.1 _ certificateScale (1 - sigma)
        (Kakeya.realRpowENN delta (-inputLoss))
        (scalarProjection_paperShading_subset_Icc
          (source.localGrains.planeMap_unit ⟨anchor, hanchorSource⟩)
          Set.inter_subset_left) hliteral
    have hprojectionThick :
        scalarProjection normal strongSet ⊆
          Metric.cthickening (2 * rho)
            (scalarProjection normal
              (source.shading.union ∩
                Metric.closedBall anchor (Real.sqrt certificateScale))) := by
      rintro value ⟨point, hpoint, rfl⟩
      let finePoint :=
        fineWitnesses.coarseWitnesses.witness (ownerCell point)
      have hfineSource : finePoint ∈ source.shading.union :=
        ⟨fineWitnesses.coarseWitnesses.sourceIndex (ownerCell point),
          fineWitnesses.coarseWitnesses.witness_mem_source
            (ownerCell point) (hownerActive point hpoint)⟩
      have hfineBall :
          finePoint ∈ Metric.closedBall anchor (Real.sqrt certificateScale) :=
        hownerWitnessBall point hpoint
      have hfineProjection :
          inner ℝ finePoint normal ∈
            scalarProjection normal
              (source.shading.union ∩
                Metric.closedBall anchor (Real.sqrt certificateScale)) :=
        ⟨finePoint, ⟨hfineSource, hfineBall⟩, rfl⟩
      have hpointFine : dist point finePoint ≤ 2 * rho :=
        le_of_lt (wz1_paper_grid_cube_diameter_lt_two_rho hrho
          (hpointOwner point hpoint)
          (fineWitnesses.coarseWitnesses.witness_mem_cell
            (ownerCell point) (hownerActive point hpoint)))
      have hprojectionDist :
          dist (inner ℝ point normal) (inner ℝ finePoint normal) ≤
            2 * rho := by
        rw [Real.dist_eq]
        have heq :
            inner ℝ point normal - inner ℝ finePoint normal =
              inner ℝ (point - finePoint) normal := by
          simp [inner_sub_left]
        rw [heq]
        exact (abs_real_inner_le_norm (point - finePoint) normal).trans
          (by simpa [hnormalUnit, dist_eq_norm] using hpointFine)
      exact Metric.mem_cthickening_of_dist_le _ _ _ _
        hfineProjection hprojectionDist
    have hstrongCoarse : strongSet ⊆ twoScale.coarseGrains.shading.union := by
      intro point hpoint
      dsimp only [strongSet] at hpoint
      rw [data.fullSource_eq] at hpoint
      rcases hpoint.1 with ⟨fineIndex, hfineIndex⟩
      exact ⟨twoScale.fine.selected.embedding fineIndex,
        twoScale.fine.subshading fineIndex hfineIndex⟩
    have hstrongGlobal : strongSet ⊆ globalCarrier := by
      intro point hpoint
      apply hglobalCarrier parent hparent
      dsimp only [strongSet] at hpoint
      rw [data.fullSource_eq] at hpoint
      have hpointParent := hpoint.2
      rw [hstrongCell parent hparent] at hpointParent
      exact ⟨hpoint.1, hpointParent⟩
    have hprojectionBounded :
        scalarProjection normal strongSet ⊆ Set.Icc (-4 : ℝ) 4 :=
      scalarProjection_paperShading_subset_Icc hnormalUnit hstrongCoarse
    have hstrongADRaw := hsourceAD.generalized_thickening
      hprojectionThick hprojectionBounded hcertificate (by positivity : 0 < 2 * rho)
    have hratio : (2 * rho) / certificateScale = (1 / 2 : ℝ) := by
      dsimp only [certificateScale]
      field_simp [hrho.ne']
      norm_num
    have hstrongAD :
        IsADSet1 (scalarProjection normal strongSet)
          certificateScale (1 - sigma) localC := by
      rw [hratio] at hstrongADRaw
      have hceil : Nat.ceil (1 / 2 : ℝ) = 1 := by
        rw [Nat.ceil_eq_iff] <;> norm_num
      rw [hceil] at hstrongADRaw
      convert hstrongADRaw using 1 <;> dsimp only [localC] <;> norm_num <;> ring
    have hlocalTop : localC ≠ ⊤ := by
      exact ENNReal.mul_ne_top (by norm_num)
        (by simp [Kakeya.realRpowENN])
    rcases wz1_lemma23_projection_heavy_fiber_in_source
        localC normal anchor strongSet hnormalUnit
        hstrongMeasurable hstrongNonempty hstrongBall hstrongAD
        hcertificate hcertificateOne hlocalTop with
      ⟨fiber⟩
    have hsourceLower :
        Kakeya.realRpowENN certificateScale
            (3 / 2 + sigma / 2 + eta) ≤ volume strongSet := by
      calc
        _ ≤ Kakeya.realRpowENN rho
            (3 / 2 + sigma / 2 + 3 * outputLoss / 2) := by
              simpa [certificateScale] using hsourceFloor
        _ ≤ twoScale.fine.balanced.cellMass :=
          by simpa only [twoScale.rhoRequested_eq] using
            twoScale.second_source_floor_power
        _ = volume strongSet := data.fullSource_volume.symm
    have hlocalOne : 1 ≤ localC := hstrongAD.2.2.2.1
    have hgrainVolume :
        Kakeya.realRpowENN certificateScale (2 + 2 * eta) ≤
          volume fiber.grain :=
      fiber.grain_volume_of_source_lower
        hcertificate hlocalOne (by simpa [localC, certificateScale] using hlocalPower)
        hsourceLower
    let sourceLeft := (parent.2.2 : ℝ) * root
    let graphLeft := max (-1 : ℝ) (sourceLeft + root - Real.sqrt certificateScale)
    have hsourceHeight :
        ∀ point ∈ strongSet,
          point (2 : Fin 3) ∈ Set.Ico sourceLeft (sourceLeft + root) := by
      intro point hpoint
      have hp := hstrongParent point hpoint
      rw [wz1PaperGridCube_eq_Ico hroot parent] at hp
      exact ⟨hp.2.2.2.2.1, by linarith [hp.2.2.2.2.2]⟩
    have hsourceWindow :
        Set.Ico sourceLeft (sourceLeft + root) ⊆ Set.Icc (-1 : ℝ) 1 := by
      intro height hheight
      let point : Point3 :=
        point3 (((parent.1 : ℝ) + 1 / 2) * root)
          (((parent.2.1 : ℝ) + 1 / 2) * root) height
      have hpointParent : point ∈ wz1PaperGridCube root parent := by
        rw [wz1PaperGridCube_eq_Ico hroot parent]
        change
          (parent.1 : ℝ) * root ≤ point 0 ∧
          point 0 < ((parent.1 : ℝ) + 1) * root ∧
          (parent.2.1 : ℝ) * root ≤ point 1 ∧
          point 1 < ((parent.2.1 : ℝ) + 1) * root ∧
          (parent.2.2 : ℝ) * root ≤ point 2 ∧
          point 2 < ((parent.2.2 : ℝ) + 1) * root
        have hp0 : point 0 = ((parent.1 : ℝ) + 1 / 2) * root := by
          simp [point, point3]
        have hp1 : point 1 = ((parent.2.1 : ℝ) + 1 / 2) * root := by
          simp [point, point3]
        have hp2 : point 2 = height := by simp [point, point3]
        rw [hp0, hp1, hp2]
        dsimp only [sourceLeft] at hheight
        constructor
        · nlinarith
        constructor
        · nlinarith
        constructor
        · nlinarith
        constructor
        · nlinarith
        constructor
        · exact hheight.1
        · have hright :
              sourceLeft + root = ((parent.2.2 : ℝ) + 1) * root := by
            dsimp only [sourceLeft]
            ring
          rw [← hright]
          exact hheight.2
      have hcoarse : point ∈ twoScale.fine.croppedCoarseShading.union := by
        rw [twoScale.fine.balanced.coarse_union_eq]
        exact Set.mem_iUnion₂.mpr
          ⟨parent, hparentActive parent hparent, hpointParent⟩
      have hbox := shading_union_subset_axisBox hcoarse
      have hp2 : point (2 : Fin 3) = height := by simp [point, point3]
      rw [← hp2]
      simpa [Kakeya.Streamlined.axisBox, abs_le] using hbox.2.2
    have hwindowClosed :
        Set.Icc sourceLeft (sourceLeft + root) ⊆ Set.Icc (-1 : ℝ) 1 :=
      sourceHorizontal_Ico_containment_closure (by linarith [hroot]) hsourceWindow
    have hgraphHeight :
        ∀ point ∈ fiber.grain,
          point (2 : Fin 3) ∈
            Set.Ico graphLeft (graphLeft + Real.sqrt certificateScale) := by
      intro point hpoint
      have hp := hsourceHeight point (fiber.grain_in_source hpoint)
      have hminusOne : (-1 : ℝ) ≤ sourceLeft :=
        (hwindowClosed ⟨le_rfl, by linarith [hroot]⟩).1
      have hsecond :
          sourceLeft + root - Real.sqrt certificateScale ≤ sourceLeft := by
        rw [hsqrtCertificate]
        linarith
      have hleft : graphLeft ≤ sourceLeft := max_le hminusOne hsecond
      constructor
      · exact hleft.trans hp.1
      · have hright : sourceLeft + root ≤
            graphLeft + Real.sqrt certificateScale := by
          have := le_max_right (-1 : ℝ)
            (sourceLeft + root - Real.sqrt certificateScale)
          linarith
        exact hp.2.trans_le hright
    have hgraphWindow :
        Set.Ico graphLeft (graphLeft + Real.sqrt certificateScale) ⊆
          Set.Icc (-1 : ℝ) 1 := by
      intro z hz
      have hleft : (-1 : ℝ) ≤ graphLeft := le_max_left _ _
      have hright : graphLeft + Real.sqrt certificateScale ≤ 1 := by
        dsimp only [graphLeft]
        by_cases hcase : (-1 : ℝ) ≥
            sourceLeft + root - Real.sqrt certificateScale
        · rw [max_eq_left hcase]
          have hsqrtOne := Real.sqrt_le_one.mpr hcertificateOne
          linarith
        · rw [max_eq_right (le_of_not_ge hcase)]
          have hsourceRight : sourceLeft + root ≤ 1 :=
            (hwindowClosed ⟨by linarith [hroot], le_rfl⟩).2
          linarith
      exact ⟨hleft.trans hz.1, hz.2.le.trans hright⟩
    have hglobalTop : globalC ≠ ⊤ := by
      exact ENNReal.mul_ne_top (by norm_num)
        (by simp [Kakeya.realRpowENN])
    let fullInput :
        WZ1Lemma23FullLocalGrainInputGeneralized
          certificateScale sigma eta globalC
          globalSlope :=
      { grain := fiber.grain
        grain_measurable := fiber.grain_measurable
        grain_finite := fiber.grain_finite
        heightLeft := graphLeft
        grain_height := hgraphHeight
        grain_volume := hgrainVolume
        center := anchor
        normal := normal
        localProjectionCenter := fiber.center
        normal_unit := hnormalUnit
        normal_vertical := fineWitnesses.normal_vertical parent hparent
        grain_square := fiber.grain_square
        grain_local_strip := fiber.grain_local_strip
        slope_small := by
          intro z hz
          exact hglobalSlopeBound z (hgraphWindow hz)
        projected := fun z =>
          scalarProjection
            (globalGrainDirection (globalSlope z))
            (horizontalSlice globalCarrier z)
        globalAD := by
          intro z hz
          have h := (hglobalAD z (hgraphWindow hz)).coarsen_scale
            hcertificate hrhoCertificate hcertificateOne
          simpa only [globalC, certificateScale] using h
        global_projection_sub := by
          intro z hz
          rintro value ⟨point, hpoint, rfl⟩
          have hlift : point3 (point 0) (point 1) z ∈ fiber.grain :=
            wz1Lemma23_mem_planarSlice_iff.mp hpoint
          have hstrong := fiber.grain_in_source hlift
          have hglobal :
              point3 (point 0) (point 1) z ∈ globalCarrier :=
            hstrongGlobal hstrong
          refine ⟨point3 (point 0) (point 1) z,
            ⟨hglobal, by simp [point3]⟩, ?_⟩
          change inner ℝ (point3 (point 0) (point 1) z)
              (globalGrainDirection (globalSlope z)) =
            point 0 + globalSlope z * point 1
          rw [PiLp.inner_apply]
          simp [Fin.sum_univ_succ, globalGrainDirection, point3] }
    exact wz1_lemma23_full_grain_normal_first_component_generalized
      certificateScale sigma eta globalC
      globalSlope
      hcertificate hcertificateOne hsigma hsigmaOne heta hetaSigma
      hglobalTop (by simpa [globalC, certificateScale] using hglobalPower)
      hPlanarSmall hrootSmall20 habsorb fullInput
  exact ⟨{
    certificateScale := certificateScale
    certificateScale_eq := rfl
    strongSource := strongSource
    strongSource_cell := hstrongCell
    normal_first := hnormalFirst
  }⟩

 /-- Backwards-compatible normal-first certificate on the maximal global bin. -/
abbrev PureWZ2SourceHorizontalNormalFirstCertificate
    {sigma inputLoss delta rho middleLoss outputLoss eta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    {line : PureWZ2SourceHorizontalFixedLineData window}
    {parents : PureWZ2SourceHorizontalParentData line}
    {selection : PureWZ2SourceHorizontalYSelection parents}
    {residue : PureWZ2SourceHorizontalYResidueData selection}
    {retained : PureWZ2SourceHorizontalResidueShadingData residue}
    (fineWitnesses : PureWZ2SourceHorizontalFineWitnessData retained) :=
  PureWZ2SourceHorizontalFixedBinNormalFirstCertificate
    (eta := eta) fineWitnesses

/-- Compatibility wrapper using the global grains produced on the coarse
configuration.  The paper-order coarse-carrier path instead calls
`normalFirstOfGlobal` with the original source slope and carrier. -/
theorem PureWZ2SourceHorizontalFixedBinFineWitnessData.normalFirstFixedBin
    {sigma inputLoss delta rho middleLoss outputLoss eta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    {line : PureWZ2SourceHorizontalFixedBinData window}
    {parents : PureWZ2SourceHorizontalFixedBinParentData line}
    {selection : PureWZ2SourceHorizontalFixedBinYSelection parents}
    {residue : PureWZ2SourceHorizontalFixedBinYResidueData selection}
    {retained : PureWZ2SourceHorizontalFixedBinResidueShadingData residue}
    (fineWitnesses : PureWZ2SourceHorizontalFixedBinFineWitnessData retained)
    (hbridge : PureWZ2PaperADBridgeStatement)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (heta : 0 < eta) (hetaSigma : 4 * eta < sigma)
    (hcertificateOne : 4 * rho ≤ 1)
    (hsourceFloor :
      Kakeya.realRpowENN (4 * rho)
          (3 / 2 + sigma / 2 + eta) ≤
        Kakeya.realRpowENN rho
          (3 / 2 + sigma / 2 + 3 * outputLoss / 2))
    (hlocalPower :
      160 * Kakeya.realRpowENN delta (-inputLoss) ≤
        Kakeya.realRpowENN (4 * rho) (-eta))
    (hglobalPower :
      10 * Kakeya.realRpowENN rho (-middleLoss) ≤
        Kakeya.realRpowENN (4 * rho) (-eta))
    (hPlanarSmall : 32 * Real.rpow (4 * rho) eta ≤ 1)
    (hrootSmall20 : 20 * Real.sqrt (4 * rho) ≤ 1)
    (habsorb :
      Real.rpow (4 * rho) (1 - 4 * eta / sigma) ≤
        Real.sqrt (4 * rho) / 14) :
    Nonempty
      (PureWZ2SourceHorizontalFixedBinNormalFirstCertificate
        (eta := eta) fineWitnesses) := by
  rcases twoScale.toLemma23PreparedCoarse hbridge with ⟨coarsePrepared⟩
  apply PureWZ2SourceHorizontalFixedBinFineWitnessData.normalFirstOfGlobalFixedBin fineWitnesses
    coarsePrepared.shadow.union
    twoScale.coarseGrains.globalGrains.slope
    twoScale.coarseGrains_slope_bound
    (by
      intro z hz
      simpa only [twoScale.rhoRequested_eq] using
        coarsePrepared.exactAD z hz)
    (by
      intro parent hparent point hpoint
      rw [coarsePrepared.shadow_union]
      exact hpoint.1)
    hbridge hsigma hsigmaOne heta hetaSigma hcertificateOne
    hsourceFloor hlocalPower hglobalPower hPlanarSmall hrootSmall20 habsorb

/-- Compatibility wrapper for the former maximal-bin global-carrier API. -/
theorem PureWZ2SourceHorizontalFineWitnessData.normalFirstOfGlobal
    {sigma inputLoss delta rho middleLoss outputLoss eta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    {line : PureWZ2SourceHorizontalFixedLineData window}
    {parents : PureWZ2SourceHorizontalParentData line}
    {selection : PureWZ2SourceHorizontalYSelection parents}
    {residue : PureWZ2SourceHorizontalYResidueData selection}
    {retained : PureWZ2SourceHorizontalResidueShadingData residue}
    (fineWitnesses : PureWZ2SourceHorizontalFineWitnessData retained)
    (globalCarrier : Set Point3) (globalSlope : ℝ → ℝ)
    (hglobalSlopeBound : ∀ z ∈ Set.Icc (-1 : ℝ) 1, |globalSlope z| ≤ 3)
    (hglobalAD : ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      IsADSet1 (scalarProjection (globalGrainDirection (globalSlope z))
        (horizontalSlice globalCarrier z)) rho (1 - sigma)
        (10 * Kakeya.realRpowENN rho (-middleLoss)))
    (hglobalCarrier : ∀ parent ∈ residue.selected,
      twoScale.fine.refined.union ∩ wz1PaperGridCube twoScale.sqrtRequested.1 parent ⊆
        globalCarrier)
    (hbridge : PureWZ2PaperADBridgeStatement)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (heta : 0 < eta) (hetaSigma : 4 * eta < sigma)
    (hcertificateOne : 4 * rho ≤ 1)
    (hsourceFloor : Kakeya.realRpowENN (4 * rho)
      (3 / 2 + sigma / 2 + eta) ≤
      Kakeya.realRpowENN rho (3 / 2 + sigma / 2 + 3 * outputLoss / 2))
    (hlocalPower : 160 * Kakeya.realRpowENN delta (-inputLoss) ≤
      Kakeya.realRpowENN (4 * rho) (-eta))
    (hglobalPower : 10 * Kakeya.realRpowENN rho (-middleLoss) ≤
      Kakeya.realRpowENN (4 * rho) (-eta))
    (hPlanarSmall : 32 * Real.rpow (4 * rho) eta ≤ 1)
    (hrootSmall20 : 20 * Real.sqrt (4 * rho) ≤ 1)
    (habsorb : Real.rpow (4 * rho) (1 - 4 * eta / sigma) ≤
      Real.sqrt (4 * rho) / 14) :
    Nonempty (PureWZ2SourceHorizontalNormalFirstCertificate
      (eta := eta) fineWitnesses) :=
  PureWZ2SourceHorizontalFixedBinFineWitnessData.normalFirstOfGlobalFixedBin
    fineWitnesses globalCarrier globalSlope hglobalSlopeBound hglobalAD hglobalCarrier
    hbridge hsigma hsigmaOne heta hetaSigma hcertificateOne hsourceFloor
    hlocalPower hglobalPower hPlanarSmall hrootSmall20 habsorb

/-- Compatibility wrapper for the former maximal-bin normal-first API. -/
theorem PureWZ2SourceHorizontalFineWitnessData.normalFirst
    {sigma inputLoss delta rho middleLoss outputLoss eta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    {line : PureWZ2SourceHorizontalFixedLineData window}
    {parents : PureWZ2SourceHorizontalParentData line}
    {selection : PureWZ2SourceHorizontalYSelection parents}
    {residue : PureWZ2SourceHorizontalYResidueData selection}
    {retained : PureWZ2SourceHorizontalResidueShadingData residue}
    (fineWitnesses : PureWZ2SourceHorizontalFineWitnessData retained)
    (hbridge : PureWZ2PaperADBridgeStatement)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (heta : 0 < eta) (hetaSigma : 4 * eta < sigma)
    (hcertificateOne : 4 * rho ≤ 1)
    (hsourceFloor : Kakeya.realRpowENN (4 * rho)
      (3 / 2 + sigma / 2 + eta) ≤
      Kakeya.realRpowENN rho (3 / 2 + sigma / 2 + 3 * outputLoss / 2))
    (hlocalPower : 160 * Kakeya.realRpowENN delta (-inputLoss) ≤
      Kakeya.realRpowENN (4 * rho) (-eta))
    (hglobalPower : 10 * Kakeya.realRpowENN rho (-middleLoss) ≤
      Kakeya.realRpowENN (4 * rho) (-eta))
    (hPlanarSmall : 32 * Real.rpow (4 * rho) eta ≤ 1)
    (hrootSmall20 : 20 * Real.sqrt (4 * rho) ≤ 1)
    (habsorb : Real.rpow (4 * rho) (1 - 4 * eta / sigma) ≤
      Real.sqrt (4 * rho) / 14) :
    Nonempty (PureWZ2SourceHorizontalNormalFirstCertificate
      (eta := eta) fineWitnesses) :=
  PureWZ2SourceHorizontalFixedBinFineWitnessData.normalFirstFixedBin
    fineWitnesses hbridge hsigma hsigmaOne heta hetaSigma hcertificateOne
    hsourceFloor hlocalPower hglobalPower hPlanarSmall hrootSmall20 habsorb

end Kakeya.Assouad
