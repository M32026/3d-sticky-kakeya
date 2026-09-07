import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.FrameNormalCompatibilityCore
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.LocalSharedNormalCertificate
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.GridCubeCover
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.Node6FixedC2ZeroExtension

/-!
# Fixed-output Node-6 frame-normal compatibility

This is the fixed-scale analogue of the historical square-root assembly
argument.  It uses only the final fixed refinement, its balanced coarse cells,
and the exact same-family C2 zero extension.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Metric Set

/-- A whole side-`scale` grid cell in the paper box has both height endpoints
in the normalized interval. -/
private theorem fixed_gridCube_height_endpoints
    {scale : ℝ} (hscale : 0 < scale)
    (cell : WZ2PaperCellIndex)
    (hbox : wz1PaperGridCube scale cell ⊆
      Kakeya.Streamlined.axisBox 2 2 2) :
    -1 ≤ (cell.2.2 : ℝ) * scale ∧
      ((cell.2.2 : ℝ) + 1) * scale ≤ 1 := by
  let left : ℝ := (cell.2.2 : ℝ) * scale
  let right : ℝ := ((cell.2.2 : ℝ) + 1) * scale
  have hinterval : Set.Ico left right ⊆ Set.Icc (-1 : ℝ) 1 := by
    intro z hz
    let point : Point3 := point3
      (((cell.1 : ℝ) + 1 / 2) * scale)
      (((cell.2.1 : ℝ) + 1 / 2) * scale) z
    have hpoint0 : point 0 = ((cell.1 : ℝ) + 1 / 2) * scale := by
      simp [point, point3, EuclideanSpace.single_apply]
    have hpoint1 : point 1 = ((cell.2.1 : ℝ) + 1 / 2) * scale := by
      simp [point, point3, EuclideanSpace.single_apply]
    have hpoint2 : point 2 = z := by
      simp [point, point3, EuclideanSpace.single_apply]
    have hpoint : point ∈ wz1PaperGridCube scale cell := by
      rw [wz1PaperGridCube_eq_Ico hscale]
      change
        (cell.1 : ℝ) * scale ≤ point 0 ∧
        point 0 < ((cell.1 : ℝ) + 1) * scale ∧
        (cell.2.1 : ℝ) * scale ≤ point 1 ∧
        point 1 < ((cell.2.1 : ℝ) + 1) * scale ∧
        (cell.2.2 : ℝ) * scale ≤ point 2 ∧
        point 2 < ((cell.2.2 : ℝ) + 1) * scale
      rw [hpoint0, hpoint1, hpoint2]
      exact ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith,
        hz.1, hz.2⟩
    have hzbox : |z| ≤ 1 := by
      have hpbox := hbox hpoint
      simpa [Kakeya.Streamlined.axisBox, hpoint0, hpoint1, hpoint2] using
        hpbox.2.2
    exact abs_le.mp hzbox
  have hleft : -1 ≤ left := by
    exact (hinterval ⟨le_rfl, by dsimp only [left, right]; linarith⟩).1
  have hright : right ≤ 1 := by
    have hone : (1 : ℝ) ∈ upperBounds (Set.Ico left right) :=
      fun z hz => (hinterval hz).2
    rw [upperBounds_Ico (by dsimp only [left, right]; linarith)] at hone
    exact hone
  exact ⟨hleft, hright⟩

/-- Put a closed interval into a longer half-open interval without leaving
the normalized height window. -/
private lemma exists_fixed_frame_normal_height_window
    {a b length : ℝ}
    (ha : -1 ≤ a) (hab : a < b) (hb : b ≤ 1)
    (hwidth : b - a ≤ length) (hlength : length ≤ 2) :
    ∃ left : ℝ,
      Set.Ico a b ⊆ Set.Ico left (left + length) ∧
      Set.Icc a b ⊆ Set.Icc left (left + length) ∧
      Set.Ico left (left + length) ⊆ Set.Icc (-1 : ℝ) 1 := by
  let left := max (-1 : ℝ) (b - length)
  have hleftLower : -1 ≤ left := le_max_left _ _
  have hleftA : left ≤ a := by
    apply max_le
    · exact ha
    · linarith
  have hrightB : b ≤ left + length := by
    have h := le_max_right (-1 : ℝ) (b - length)
    dsimp only [left]
    linarith
  have hrightOne : left + length ≤ 1 := by
    by_cases hcase : (-1 : ℝ) ≤ b - length
    · rw [show left = b - length from max_eq_right hcase]
      linarith
    · rw [show left = -1 from max_eq_left (le_of_not_ge hcase)]
      linarith
  exact ⟨left,
    fun _ hz => ⟨hleftA.trans hz.1, hz.2.trans_le hrightB⟩,
    fun _ hz => ⟨hleftA.trans hz.1, hz.2.trans hrightB⟩,
    fun _ hz => ⟨hleftLower.trans hz.1, hz.2.le.trans hrightOne⟩⟩

/-- A square-root fixed-scale output supplies the pointwise frame-normal
compatibility needed by every later power-scale subfamily. -/
theorem PureWZ2Node6FixedScaleOutput.frameNormalCompatibility
    {sigma sourceLoss fixedLoss targetLoss delta localEta : ℝ}
    {cfg : PureWZ2C2GrainConfiguration sigma sourceLoss delta}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    (fixed : PureWZ2Node6FixedScaleOutput
      (sigma := sigma) (outputLoss := fixedLoss)
      cfg.shading rho logExponent)
    (zeroData : PureWZ2Node6FixedC2ZeroExtensionData
      (targetLoss := targetLoss) cfg fixed)
    (hrho : rho.1 = Real.sqrt delta)
    (hdeltaTiny : delta ≤ 1 / 1000000000000)
    (hsourceFloor :
      Kakeya.realRpowENN (3 * delta)
          (3 / 2 + sigma / 2 + localEta) ≤
        fixed.balanced.cellMass)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hlocalEta : 0 < localEta) (hlocalEtaSigma : 4 * localEta < sigma)
    (hTwoCOne : 1 ≤ 2 * Kakeya.realRpowENN delta (-targetLoss))
    (hTwoCPower :
      2 * Kakeya.realRpowENN delta (-targetLoss) ≤
        Kakeya.realRpowENN (3 * delta) (-localEta))
    (hPlanarSmall : 32 * Real.rpow (3 * delta) localEta ≤ 1)
    (hrootSmall20 : 20 * Real.sqrt (3 * delta) ≤ 1)
    (habsorb : Real.rpow (3 * delta)
        (1 - 4 * localEta / sigma) ≤ Real.sqrt (3 * delta) / 14) :
    PureWZ2FrameNormalCompatibility
      (zeroData.configuration (targetLoss := targetLoss)) := by
  let outputCfg := zeroData.configuration (targetLoss := targetLoss)
  intro frameSlope anchor hanchorFrame
  have hanchorRefined : (anchor : Point3) ∈ fixed.refined.union := by
    rw [← zeroData.configuration_union]
    exact anchor.property
  rcases hanchorRefined with ⟨index, hanchorCarrier⟩
  rcases fixed.fine_cell_nested index anchor hanchorCarrier with
    ⟨coarseCell, hcoarseCell, hfineCell⟩
  have hanchorCell : (anchor : Point3) ∈
      wz1PaperGridCube rho.1 coarseCell :=
    hfineCell (mem_wz1PaperGridCube delta
      (wz1PaperGridIndex delta anchor) anchor |>.mpr rfl)
  let source : Set Point3 :=
    outputCfg.shading.union ∩ wz1PaperGridCube rho.1 coarseCell
  have hsourceMeasurable : MeasurableSet source :=
    (measurableSet_shading_union outputCfg.shading).inter
      (wz1PaperGridCube_measurable coarseCell)
  have hsourceNonempty : source.Nonempty :=
    ⟨anchor, anchor.property, hanchorCell⟩
  have hsqrtCertificate : Real.sqrt (3 * delta) =
      Real.sqrt 3 * rho.1 := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3), hrho]
  have hsourceBall : source ⊆
      outputCfg.shading.union ∩
        Metric.closedBall (anchor : Point3) (Real.sqrt (3 * delta)) := by
    intro point hpoint
    refine ⟨hpoint.1, Metric.mem_closedBall.mpr ?_⟩
    rw [hsqrtCertificate]
    simpa [mul_comm] using
      dist_le_sqrt3_of_mem_wz1PaperGridCube
        (fixed.delta_pos.trans_le rho.2.1) hpoint.2 hanchorCell
  have hunion : outputCfg.shading.union = fixed.refined.union := by
    exact zeroData.configuration_union
  have hsourceVolume : Kakeya.realRpowENN (3 * delta)
        (3 / 2 + sigma / 2 + localEta) ≤ volume source := by
    calc
      _ ≤ fixed.balanced.cellMass := hsourceFloor
      _ = volume (fixed.refined.union ∩
          wz1PaperGridCube rho.1 coarseCell) :=
        (fixed.balanced.fine_cell_mass coarseCell hcoarseCell).symm
      _ = volume source := by rw [← hunion]
  have hcellBox : wz1PaperGridCube rho.1 coarseCell ⊆
      Kakeya.Streamlined.axisBox 2 2 2 := by
    intro point hpoint
    have hpointUnion : point ∈ fixed.croppedCoarseShading.union := by
      rw [fixed.balanced.coarse_union_eq]
      exact Set.mem_iUnion₂.mpr ⟨coarseCell, hcoarseCell, hpoint⟩
    rcases hpointUnion with ⟨coarseIndex, hpointCarrier⟩
    exact (fixed.croppedCoarseShading.subset_body
      coarseIndex hpointCarrier).2
  have hrhoPos : 0 < rho.1 := fixed.delta_pos.trans_le rho.2.1
  have hheightEndpoints := fixed_gridCube_height_endpoints
    hrhoPos coarseCell hcellBox
  have hcertificatePos : 0 < 3 * delta := by nlinarith [fixed.delta_pos]
  have hcertificateOne : 3 * delta ≤ 1 := by nlinarith [hdeltaTiny]
  have hdeltaCertificate : delta ≤ 3 * delta := by
    linarith [fixed.delta_pos]
  have hwindowSmall : Real.sqrt (3 * delta) ≤ 1 / 50 := by
    rw [hsqrtCertificate]
    have hsqrtDeltaSq : Real.sqrt delta ^ 2 ≤ (1 / 1000 : ℝ) ^ 2 := by
      rw [Real.sq_sqrt fixed.delta_pos.le]
      exact hdeltaTiny.trans (by norm_num)
    have hsqrtDelta : Real.sqrt delta ≤ 1 / 1000 :=
      (sq_le_sq₀ (Real.sqrt_nonneg delta) (by norm_num)).mp hsqrtDeltaSq
    have hsqrtThree : Real.sqrt 3 ≤ 2 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3),
        Real.sqrt_nonneg 3]
    calc
      Real.sqrt 3 * rho.1 =
          Real.sqrt 3 * Real.sqrt delta := by rw [hrho]
      _ ≤ 2 * (1 / 1000) := by gcongr
      _ ≤ 1 / 50 := by norm_num
  let cellLeft : ℝ := (coarseCell.2.2 : ℝ) * rho.1
  let cellRight : ℝ := ((coarseCell.2.2 : ℝ) + 1) * rho.1
  have hcellOrder : cellLeft < cellRight := by
    dsimp only [cellLeft, cellRight]
    nlinarith [hrhoPos]
  rcases exists_fixed_frame_normal_height_window hheightEndpoints.1 hcellOrder
      hheightEndpoints.2 (by
        dsimp only [cellLeft, cellRight]
        rw [hsqrtCertificate]
        have hone : 1 ≤ Real.sqrt 3 := by
          nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3),
            Real.sqrt_nonneg 3]
        have hrhoNonneg : 0 ≤ rho.1 := hrhoPos.le
        nlinarith) (hwindowSmall.trans (by norm_num)) with
    ⟨heightLeft, hcellWindow, hcellClosed, hwindowAmbient⟩
  have hsourceHeight : ∀ point ∈ source,
      point 2 ∈ Set.Ico heightLeft
        (heightLeft + Real.sqrt (3 * delta)) := by
    intro point hpoint
    have hcoords := hpoint.2
    rw [wz1PaperGridCube_eq_Ico hrhoPos coarseCell] at hcoords
    exact hcellWindow hcoords.2.2.2.2
  have hanchorClosed : (anchor : Point3) 2 ∈
      Set.Icc heightLeft (heightLeft + Real.sqrt (3 * delta)) := by
    have hcoords := hanchorCell
    rw [wz1PaperGridCube_eq_Ico hrhoPos coarseCell] at hcoords
    exact hcellClosed ⟨hcoords.2.2.2.2.1, hcoords.2.2.2.2.2.le⟩
  have hframeClose : ∀ height ∈
      Set.Ico heightLeft (heightLeft + Real.sqrt (3 * delta)),
      |outputCfg.globalGrains.slope height - frameSlope| ≤ 1 / 25 := by
    intro height hheight
    have hslopeLip := outputCfg.globalGrains.slope_lipschitzOn
    have hanchorBox : (anchor : Point3) ∈
        Kakeya.Streamlined.axisBox 2 2 2 := hcellBox hanchorCell
    have hanchorHeight : (anchor : Point3) 2 ∈ Set.Icc (-1 : ℝ) 1 := by
      simpa [Kakeya.Streamlined.axisBox, abs_le] using hanchorBox.2.2
    have hdist := hslopeLip.norm_sub_le (hwindowAmbient hheight)
      hanchorHeight
    have hheightDistance : |height - (anchor : Point3) 2| ≤
        Real.sqrt (3 * delta) := by
      rw [abs_le]
      constructor <;> linarith [hheight.1, hheight.2,
        hanchorClosed.1, hanchorClosed.2]
    have hslope : |outputCfg.globalGrains.slope height -
        outputCfg.globalGrains.slope ((anchor : Point3) 2)| ≤
          |height - (anchor : Point3) 2| := by
      simpa [Real.dist_eq] using hdist
    calc
      |outputCfg.globalGrains.slope height - frameSlope| ≤
          |outputCfg.globalGrains.slope height -
              outputCfg.globalGrains.slope ((anchor : Point3) 2)| +
            |outputCfg.globalGrains.slope ((anchor : Point3) 2) -
              frameSlope| := by
        simpa only [show outputCfg.globalGrains.slope height - frameSlope =
            (outputCfg.globalGrains.slope height -
              outputCfg.globalGrains.slope ((anchor : Point3) 2)) +
            (outputCfg.globalGrains.slope ((anchor : Point3) 2) -
              frameSlope) by ring] using abs_add_le _ _
      _ ≤ Real.sqrt (3 * delta) + 1 / 50 :=
        add_le_add (hslope.trans hheightDistance) hanchorFrame
      _ ≤ 1 / 25 := by linarith
  let heavy : PureWZ2HeavyLocalSource
      (rho := 3 * delta) (eta := localEta)
      (frameSlope := frameSlope) outputCfg :=
    { anchor := anchor
      source := source
      source_measurable := hsourceMeasurable
      source_nonempty := hsourceNonempty
      source_subset := hsourceBall
      source_volume := hsourceVolume
      heightLeft := heightLeft
      source_height := hsourceHeight
      height_window := hwindowAmbient
      frame_close := hframeClose }
  exact heavy.frameProjectedNormal_norm_lower hcertificatePos
    hcertificateOne hdeltaCertificate hsigma hsigmaOne hlocalEta
    hlocalEtaSigma hTwoCOne hTwoCPower hPlanarSmall hrootSmall20 habsorb

end Kakeya.Assouad

end
