import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Proposition64ExactParameters
import MyLeanRepo.Kakeya.Assouad.PureWZ2.TubeParameterLineDistance
import MyLeanRepo.Kakeya.Assouad.PureWZ2.OrdinaryLineConflictPacking

/-!
# Proposition 6.4 paper-conflict geometry

This file records the geometric part of the essentially-distinct cleanup in
`wz2_64.tex`.  A Definition-2.12 centered-containment conflict between two
localized final tubes first gives a paper line-distance bound.  That bound is
then converted to a four-parameter cluster before the isotropic and exact
`Phi` inverse maps are applied.
-/

noncomputable section

namespace Kakeya.Assouad

open Set

attribute [local instance] Classical.propDecidable

/-- On the positive vertical chart, the difference of the two affine-line
slope vectors is controlled by six times the angular distance. -/
lemma pureWZ2_verticalSlope_norm_sub_le_six_angle
    {first second : Point3}
    (hfirstNorm : ‖first‖ = 1) (hsecondNorm : ‖second‖ = 1)
    (hfirstVertical : 1 / 2 ≤ first 2)
    (hsecondVertical : 1 / 2 ≤ second 2) :
    ‖(1 / first 2) • first - (1 / second 2) • second‖ ≤
      6 * InnerProductGeometry.angle first second := by
  have hfirstPos : 0 < first 2 := by linarith
  have hsecondPos : 0 < second 2 := by linarith
  have hdirection : ‖first - second‖ ≤
      InnerProductGeometry.angle first second :=
    unit_norm_sub_le_angle hfirstNorm hsecondNorm
  have hcoordinate : |first 2 - second 2| ≤ ‖first - second‖ := by
    simpa only [PiLp.sub_apply, Real.norm_eq_abs] using
      (PiLp.norm_apply_le (first - second) (2 : Fin 3))
  have hinverseFirst : 1 / first 2 ≤ 2 := by
    calc
      1 / first 2 ≤ 1 / (1 / 2 : ℝ) := by gcongr
      _ = 2 := by norm_num
  have hinverseDifference :
      |1 / first 2 - 1 / second 2| ≤
        4 * |first 2 - second 2| := by
    rw [show 1 / first 2 - 1 / second 2 =
        (second 2 - first 2) / (first 2 * second 2) by
          field_simp [hfirstPos.ne', hsecondPos.ne'],
      abs_div, abs_of_pos (mul_pos hfirstPos hsecondPos), abs_sub_comm]
    have hdenominator : 1 / 4 ≤ first 2 * second 2 := by nlinarith
    calc
      |first 2 - second 2| / (first 2 * second 2) ≤
          |first 2 - second 2| / (1 / 4 : ℝ) := by gcongr
      _ = 4 * |first 2 - second 2| := by ring
  have hdecomposition :
      (1 / first 2) • first - (1 / second 2) • second =
        (1 / first 2) • (first - second) +
          (1 / first 2 - 1 / second 2) • second := by module
  rw [hdecomposition]
  calc
    ‖(1 / first 2) • (first - second) +
        (1 / first 2 - 1 / second 2) • second‖ ≤
      ‖(1 / first 2) • (first - second)‖ +
        ‖(1 / first 2 - 1 / second 2) • second‖ := norm_add_le _ _
    _ = (1 / first 2) * ‖first - second‖ +
        |1 / first 2 - 1 / second 2| := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_pos (one_div_pos.mpr hfirstPos), hsecondNorm, mul_one]
    _ ≤ 2 * ‖first - second‖ + 4 * |first 2 - second 2| := by
      gcongr
    _ ≤ 6 * ‖first - second‖ := by nlinarith
    _ ≤ 6 * InnerProductGeometry.angle first second := by gcongr

/-- Paper line distance controls all four vertical-line parameters.  The
intercepts cost one copy of the distance and the slopes cost six. -/
theorem pureWZ2_tubeParams_cluster_of_paperLineDistance
    {firstDelta secondDelta radius : ℝ}
    (first : Kakeya.DeltaTube firstDelta)
    (second : Kakeya.DeltaTube secondDelta)
    (hfirst : WZ1PaperTubeInLineClass first)
    (hsecond : WZ1PaperTubeInLineClass second)
    (hdistance : wz1PaperLineDistance first second ≤ radius) :
    |(tubeParamsOfTube first).a - (tubeParamsOfTube second).a| ≤ radius ∧
      |(tubeParamsOfTube first).b - (tubeParamsOfTube second).b| ≤ radius ∧
      |(tubeParamsOfTube first).c - (tubeParamsOfTube second).c| ≤
          6 * radius ∧
      |(tubeParamsOfTube first).d - (tubeParamsOfTube second).d| ≤
          6 * radius := by
  let firstZero := wz1TubeAxisZeroPoint first
  let secondZero := wz1TubeAxisZeroPoint second
  let firstDirection := wz1PaperDirection first
  let secondDirection := wz1PaperDirection second
  have hfirstVertical : first.direction 2 ≠ 0 := by
    exact abs_pos.mp (lt_of_lt_of_le (by norm_num) hfirst.vertical)
  have hsecondVertical : second.direction 2 ≠ 0 := by
    exact abs_pos.mp (lt_of_lt_of_le (by norm_num) hsecond.vertical)
  have hfirstA : (tubeParamsOfTube first).a = firstZero 0 := by
    have h := tubeAxisLine_coord_zero first hfirstVertical
      (wz1TubeAxisZeroPoint_mem_axis first)
    rw [wz1TubeAxisZeroPoint_coord_two first hfirst.vertical, mul_zero, add_zero] at h
    exact h.symm
  have hfirstB : (tubeParamsOfTube first).b = firstZero 1 := by
    have h := tubeAxisLine_coord_one first hfirstVertical
      (wz1TubeAxisZeroPoint_mem_axis first)
    rw [wz1TubeAxisZeroPoint_coord_two first hfirst.vertical, mul_zero, add_zero] at h
    exact h.symm
  have hsecondA : (tubeParamsOfTube second).a = secondZero 0 := by
    have h := tubeAxisLine_coord_zero second hsecondVertical
      (wz1TubeAxisZeroPoint_mem_axis second)
    rw [wz1TubeAxisZeroPoint_coord_two second hsecond.vertical, mul_zero, add_zero] at h
    exact h.symm
  have hsecondB : (tubeParamsOfTube second).b = secondZero 1 := by
    have h := tubeAxisLine_coord_one second hsecondVertical
      (wz1TubeAxisZeroPoint_mem_axis second)
    rw [wz1TubeAxisZeroPoint_coord_two second hsecond.vertical, mul_zero, add_zero] at h
    exact h.symm
  have hposition : dist firstZero secondZero ≤ radius := by
    exact (le_add_of_nonneg_right
      (InnerProductGeometry.angle_nonneg firstDirection secondDirection)).trans
        hdistance
  have ha : |(tubeParamsOfTube first).a -
      (tubeParamsOfTube second).a| ≤ radius := by
    rw [hfirstA, hsecondA]
    have hcoordinate : |firstZero 0 - secondZero 0| ≤
        dist firstZero secondZero := by
      simpa [Real.dist_eq] using
        (PiLp.dist_apply_le firstZero secondZero (0 : Fin 3))
    exact hcoordinate.trans hposition
  have hb : |(tubeParamsOfTube first).b -
      (tubeParamsOfTube second).b| ≤ radius := by
    rw [hfirstB, hsecondB]
    have hcoordinate : |firstZero 1 - secondZero 1| ≤
        dist firstZero secondZero := by
      simpa [Real.dist_eq] using
        (PiLp.dist_apply_le firstZero secondZero (1 : Fin 3))
    exact hcoordinate.trans hposition
  have hfirstSlope :
      (1 / firstDirection 2) • firstDirection =
        point3 (tubeParamsOfTube first).c (tubeParamsOfTube first).d 1 := by
    unfold firstDirection wz1PaperDirection
    split_ifs with hsign
    · ext coordinate
      fin_cases coordinate <;>
        simp [point3, tubeParamsOfTube, hfirstVertical] <;> ring
    · ext coordinate
      fin_cases coordinate <;>
        simp [point3, tubeParamsOfTube, hfirstVertical] <;> ring
  have hsecondSlope :
      (1 / secondDirection 2) • secondDirection =
        point3 (tubeParamsOfTube second).c (tubeParamsOfTube second).d 1 := by
    unfold secondDirection wz1PaperDirection
    split_ifs with hsign
    · ext coordinate
      fin_cases coordinate <;>
        simp [point3, tubeParamsOfTube, hsecondVertical] <;> ring
    · ext coordinate
      fin_cases coordinate <;>
        simp [point3, tubeParamsOfTube, hsecondVertical] <;> ring
  have hslopeNorm :
      ‖point3 (tubeParamsOfTube first).c (tubeParamsOfTube first).d 1 -
          point3 (tubeParamsOfTube second).c (tubeParamsOfTube second).d 1‖ ≤
        6 * InnerProductGeometry.angle firstDirection secondDirection := by
    rw [← hfirstSlope, ← hsecondSlope]
    exact pureWZ2_verticalSlope_norm_sub_le_six_angle
      (wz1PaperDirection_norm first) (wz1PaperDirection_norm second)
      hfirst.1 hsecond.1
  have hangle : InnerProductGeometry.angle firstDirection secondDirection ≤
      radius := by
    exact (le_add_of_nonneg_left (dist_nonneg :
      0 ≤ dist firstZero secondZero)).trans hdistance
  have hslopeCoordinate : ∀ coordinate : Fin 3,
      |(point3 (tubeParamsOfTube first).c (tubeParamsOfTube first).d 1 -
        point3 (tubeParamsOfTube second).c (tubeParamsOfTube second).d 1) coordinate| ≤
          6 * radius := by
    intro coordinate
    have hcoordinate :=
      (PiLp.norm_apply_le
        (point3 (tubeParamsOfTube first).c (tubeParamsOfTube first).d 1 -
          point3 (tubeParamsOfTube second).c (tubeParamsOfTube second).d 1)
        coordinate)
    have hcoordinate' :
        |(point3 (tubeParamsOfTube first).c (tubeParamsOfTube first).d 1 -
          point3 (tubeParamsOfTube second).c (tubeParamsOfTube second).d 1)
            coordinate| ≤
          ‖point3 (tubeParamsOfTube first).c (tubeParamsOfTube first).d 1 -
            point3 (tubeParamsOfTube second).c (tubeParamsOfTube second).d 1‖ := by
      simpa only [Real.norm_eq_abs] using hcoordinate
    exact hcoordinate'.trans (hslopeNorm.trans (by gcongr))
  refine ⟨ha, hb, ?_, ?_⟩
  · simpa [point3] using hslopeCoordinate 0
  · simpa [point3] using hslopeCoordinate 1

/-- A localized Definition-2.12 conflict puts the two final tubes in one
four-parameter box of radius `600 * delta`. -/
theorem pureWZ2Proposition64_targetParameterCluster_of_paperConflict
    {delta : ℝ} (hdelta : 0 < delta)
    (family : Kakeya.Streamlined.TubeFamily delta)
    {first second : Fin family.card}
    (hfirstLine : WZ1PaperTubeInLineClass (family.tube first))
    (hsecondLine : WZ1PaperTubeInLineClass (family.tube second))
    (hfirstLocal : ‖wz2PaperTubeMidpoint (family.tube first)‖ ≤ 3)
    (hsecondLocal : ‖wz2PaperTubeMidpoint (family.tube second)‖ ≤ 3)
    (hconflict : pureWZ2Proposition64PaperConflict family first second) :
    |(tubeParams first).a - (tubeParams second).a| ≤ 600 * delta ∧
      |(tubeParams first).b - (tubeParams second).b| ≤ 600 * delta ∧
      |(tubeParams first).c - (tubeParams second).c| ≤ 600 * delta ∧
      |(tubeParams first).d - (tubeParams second).d| ≤ 600 * delta := by
  have hcontainment :
      (family.tube first).carrier ⊆
          wz2PaperCenteredDilatedCarrier 2 (family.tube second) ∨
        (family.tube second).carrier ⊆
          wz2PaperCenteredDilatedCarrier 2 (family.tube first) := by
    unfold pureWZ2Proposition64PaperConflict at hconflict
    rcases hconflict with ⟨_, hconflict⟩
    by_cases hforward : (family.tube first).carrier ⊆
        wz2PaperCenteredDilatedCarrier 2 (family.tube second)
    · exact Or.inl hforward
    · exact Or.inr (by
        by_contra hbackward
        exact hconflict ⟨hforward, hbackward⟩)
  have hlineDistance :
      wz1PaperLineDistance (family.tube first) (family.tube second) ≤
        100 * delta := by
    rcases hcontainment with hforward | hbackward
    · exact wz2_paper_localized_centered_doubled_containment_lineDistance_le
        hdelta hdelta hfirstLine hsecondLine hfirstLocal hforward
    · rw [wz1PaperLineDistance_symm]
      exact wz2_paper_localized_centered_doubled_containment_lineDistance_le
        hdelta hdelta hsecondLine hfirstLine hsecondLocal hbackward
  have hparams := pureWZ2_tubeParams_cluster_of_paperLineDistance
    (family.tube first) (family.tube second) hfirstLine hsecondLine
      hlineDistance
  refine ⟨hparams.1.trans (by linarith),
    hparams.2.1.trans (by linarith), ?_, ?_⟩
  · change |(tubeParamsOfTube (family.tube first)).c -
      (tubeParamsOfTube (family.tube second)).c| ≤ 600 * delta
    convert hparams.2.2.1 using 1
    ring
  · change |(tubeParamsOfTube (family.tube first)).d -
      (tubeParamsOfTube (family.tube second)).d| ≤ 600 * delta
    convert hparams.2.2.2 using 1
    ring

/-- After discarding zero-mass saturated carriers, every final isotropic tube
lies in the paper line class.  The occupied point is taken from its own
carrier and traced back through the cubical saturation to the same source
index. -/
theorem pureWZ2Proposition64_positiveIsotropicFamily_lineClass
    {sourceDelta targetDelta width scale : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    (popular : PureWZ2Proposition64PopularBoxData sourceShading width)
    (hsourceLine : WZ1PaperIsLineClass sourceFamily)
    (hwidth : 0 < width)
    (hsourceDelta : 0 < sourceDelta) (htargetDelta : 0 < targetDelta)
    (htargetDeltaSmall : targetDelta ≤ 1 / 96)
    (hscale : 1 ≤ scale)
    (hradius : scale * (6 * sourceDelta) +
      2 * targetDelta ≤ 6 * targetDelta)
    (hboxScale : 18 * scale * width ≤ 1) :
    let sourceWindow := popular.union_subset_closedBall
      hwidth
      (lt_of_lt_of_le zero_lt_one hscale)
      (by linarith : 3 * scale * width ≤ 1)
    let finalShading := pureWZ2Proposition64FullIsotropicPaperShading
      popular.restricted popular.center scale hsourceDelta htargetDelta
      (htargetDeltaSmall.trans (by norm_num)) hscale hradius sourceWindow
    WZ1PaperIsLineClass
      (paperPositiveMassSubfamily finalShading).family := by
  dsimp only
  let sourceWindow := popular.union_subset_closedBall
    hwidth
    (lt_of_lt_of_le zero_lt_one hscale)
    (by linarith : 3 * scale * width ≤ 1)
  let finalShading := pureWZ2Proposition64FullIsotropicPaperShading
    popular.restricted popular.center scale hsourceDelta htargetDelta
      (htargetDeltaSmall.trans (by norm_num)) hscale hradius sourceWindow
  intro index
  let ambientIndex := (paperPositiveMassSubfamily finalShading).embedding index
  rcases paperPositiveMassSubfamily_carrier_nonempty finalShading index with
    ⟨targetPoint, htargetPoint⟩
  change WZ1PaperTubeInLineClass
    (pureWZ2Proposition64IsotropicRebasedPaperTube popular.center scale
      (sourceFamily.tube ambientIndex))
  have htargetPoint' : targetPoint ∈ wz1PaperCubicalSaturation targetDelta
      (pureWZ2Proposition64IsotropicMap popular.center scale ''
        popular.restricted.carrier ambientIndex) := by
    simpa [finalShading, paperPositiveMassSubfamily,
      restrictPaperShading, ambientIndex,
      pureWZ2Proposition64FullIsotropicPaperShading] using htargetPoint
  rcases htargetPoint' with
    ⟨imagePoint, ⟨sourcePoint, hsourcePoint, rfl⟩, _hcell⟩
  have hsourceCarrier :
      sourcePoint ∈ wz1PaperTubeCarrier (sourceFamily.tube ambientIndex) :=
    popular.restricted.subset_body ambientIndex hsourcePoint
  have hsourceCenter : dist sourcePoint popular.center ≤ 1 / (12 * scale) := by
    have hball := popular.union_subset_closedBall_twelve
      hwidth
      (lt_of_lt_of_le zero_lt_one hscale) hboxScale
      (show sourcePoint ∈ popular.restricted.union from
        ⟨ambientIndex, hsourcePoint⟩)
    simpa [Metric.mem_closedBall] using hball
  exact pureWZ2Proposition64IsotropicRebasedPaperTube_lineClass_of_occupied
    popular.center hscale (sourceFamily.tube ambientIndex) hsourceDelta
    (hsourceLine ambientIndex) sourcePoint hsourceCarrier hsourceCenter
      htargetDeltaSmall hradius

/-- The canonical height-zero rebase makes one final isotropic tube local
once its line-class certificate is available. -/
theorem pureWZ2Proposition64_isotropicTube_midpoint_norm_le_three
    {sourceDelta targetDelta : ℝ}
    (sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta)
    (center : Point3) (scale : ℝ)
    (index : Fin sourceFamily.card)
    (hline : WZ1PaperTubeInLineClass
      ((pureWZ2Proposition64IsotropicPaperFamily
        (targetDelta := targetDelta) sourceFamily center scale).tube index)) :
    ‖wz2PaperTubeMidpoint
      ((pureWZ2Proposition64IsotropicPaperFamily
        (targetDelta := targetDelta) sourceFamily center scale).tube index)‖ ≤ 3 := by
  let tube := (pureWZ2Proposition64IsotropicPaperFamily
    (targetDelta := targetDelta) sourceFamily center scale).tube index
  have hmidpoint : wz2PaperTubeMidpoint tube = wz1TubeAxisZeroPoint tube := by
    dsimp only [tube, pureWZ2Proposition64IsotropicPaperFamily]
    apply pureWZ2Proposition64IsotropicRebasedPaperTube_midpoint
    simpa [tube, pureWZ2Proposition64IsotropicPaperFamily,
      pureWZ2Proposition64IsotropicRebasedPaperTube,
      pureWZ2Proposition64IsotropicPaperTube] using hline.vertical
  have hzeroTwo : wz1TubeAxisZeroPoint tube 2 = 0 :=
    wz1TubeAxisZeroPoint_coord_two tube hline.vertical
  rw [hmidpoint]
  have hzeroNorm : ‖wz1TubeAxisZeroPoint tube‖ ≤ 1 := by
    rw [EuclideanSpace.norm_eq, Real.sqrt_le_iff]
    constructor
    · positivity
    · simp only [Real.norm_eq_abs, sq_abs, Fin.sum_univ_three]
      have hzero := sq_le_sq₀ (abs_nonneg (wz1TubeAxisZeroPoint tube 0))
        (by norm_num : 0 ≤ (1 / 3 : ℝ)) |>.2 (by
          exact hline.2.1)
      have hone := sq_le_sq₀ (abs_nonneg (wz1TubeAxisZeroPoint tube 1))
        (by norm_num : 0 ≤ (1 / 3 : ℝ)) |>.2 (by
          exact hline.2.2)
      rw [hzeroTwo]
      norm_num at *
      nlinarith
  exact hzeroNorm.trans (by norm_num)

/-- Family form of canonical-rebase midpoint locality. -/
theorem pureWZ2Proposition64_isotropicFamily_midpoint_norm_le_three
    {sourceDelta targetDelta : ℝ}
    (sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta)
    (center : Point3) (scale : ℝ)
    (hline : WZ1PaperIsLineClass
      (pureWZ2Proposition64IsotropicPaperFamily
        (targetDelta := targetDelta) sourceFamily center scale)) :
    ∀ index, ‖wz2PaperTubeMidpoint
      ((pureWZ2Proposition64IsotropicPaperFamily
        (targetDelta := targetDelta) sourceFamily center scale).tube index)‖ ≤ 3 :=
  fun index => pureWZ2Proposition64_isotropicTube_midpoint_norm_le_three
    sourceFamily center scale index (hline index)

/-- Pull a final paper conflict through the isotropic similarity and then
through the exact translated `Phi` map.  The conclusion is a parameter box
in the original source family, which is the level where the source CWA and
its Frostman consequence live. -/
theorem pureWZ2Proposition64_sourceParameterCluster_of_finalConflict
    {sourceDelta imageDelta finalDelta : ℝ}
    (g : ℝ → ℝ)
    (slabCenter anchorHeight halfHeight normalization : ℝ)
    (translation center : Point3) (scale : ℝ)
    (sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta)
    (htranslationHeight : translation 2 = 0)
    (hhalfHeight : 0 < halfHeight) (hhalfHeightOne : halfHeight ≤ 1)
    (hnormalization : 9 ≤ normalization)
    (hanchorSlope : |g anchorHeight| ≤ 8)
    (hslabCenter : |slabCenter| ≤ 1)
    (hsourceLine : WZ1PaperIsLineClass sourceFamily)
    (hexactLine : WZ1PaperIsLineClass
      (pureWZ2Proposition64ImageFamily imageDelta g slabCenter anchorHeight
        halfHeight normalization translation hhalfHeight
          (by linarith : 0 < normalization) sourceFamily))
    (hcenter : |center 2| ≤ 1) (hscale : 1 ≤ scale)
    (hfinalDelta : 0 < finalDelta)
    {first second : Fin sourceFamily.card}
    (hfirstFinalLine : WZ1PaperTubeInLineClass
      ((pureWZ2Proposition64IsotropicPaperFamily
        (targetDelta := finalDelta)
        (pureWZ2Proposition64ImageFamily imageDelta g slabCenter anchorHeight
          halfHeight normalization translation hhalfHeight
            (by linarith : 0 < normalization) sourceFamily) center scale).tube first))
    (hsecondFinalLine : WZ1PaperTubeInLineClass
      ((pureWZ2Proposition64IsotropicPaperFamily
        (targetDelta := finalDelta)
        (pureWZ2Proposition64ImageFamily imageDelta g slabCenter anchorHeight
          halfHeight normalization translation hhalfHeight
            (by linarith : 0 < normalization) sourceFamily) center scale).tube second))
    (hfirstFinalLocal : ‖wz2PaperTubeMidpoint
      ((pureWZ2Proposition64IsotropicPaperFamily
        (targetDelta := finalDelta)
        (pureWZ2Proposition64ImageFamily imageDelta g slabCenter anchorHeight
          halfHeight normalization translation hhalfHeight
            (by linarith : 0 < normalization) sourceFamily) center scale).tube
          first)‖ ≤ 3)
    (hsecondFinalLocal : ‖wz2PaperTubeMidpoint
      ((pureWZ2Proposition64IsotropicPaperFamily
        (targetDelta := finalDelta)
        (pureWZ2Proposition64ImageFamily imageDelta g slabCenter anchorHeight
          halfHeight normalization translation hhalfHeight
            (by linarith : 0 < normalization) sourceFamily) center scale).tube
          second)‖ ≤ 3)
    (hconflict : pureWZ2Proposition64PaperConflict
      (pureWZ2Proposition64IsotropicPaperFamily
        (targetDelta := finalDelta)
        (pureWZ2Proposition64ImageFamily imageDelta g slabCenter anchorHeight
          halfHeight normalization translation hhalfHeight
            (by linarith : 0 < normalization) sourceFamily) center scale)
      first second) :
    |(tubeParams first).a - (tubeParams second).a| ≤
        24000 * normalization * finalDelta / halfHeight ∧
      |(tubeParams first).b - (tubeParams second).b| ≤
        2400 * finalDelta / halfHeight ∧
      |(tubeParams first).c - (tubeParams second).c| ≤
        12000 * normalization * finalDelta / halfHeight ∧
      |(tubeParams first).d - (tubeParams second).d| ≤
        1200 * finalDelta / halfHeight := by
  let exactFamily := pureWZ2Proposition64ImageFamily imageDelta g slabCenter
    anchorHeight halfHeight normalization translation hhalfHeight
      (by linarith : 0 < normalization) sourceFamily
  let finalFamily := pureWZ2Proposition64IsotropicPaperFamily
    (targetDelta := finalDelta) exactFamily center scale
  have htarget := pureWZ2Proposition64_targetParameterCluster_of_paperConflict
    hfinalDelta finalFamily hfirstFinalLine hsecondFinalLine
      hfirstFinalLocal hsecondFinalLocal hconflict
  have hexactParams : ∀ index : Fin sourceFamily.card,
      tubeParamsOfTube (exactFamily.tube index) =
        pureWZ2Proposition64ExactTubeParams (g anchorHeight) slabCenter
          halfHeight normalization translation
            (tubeParamsOfTube (sourceFamily.tube index)) := by
    intro index
    apply tubeParamsOfTube_eq_proposition64Exact_of_axis_image g slabCenter
      anchorHeight halfHeight normalization translation htranslationHeight
      hhalfHeight (sourceFamily.tube index)
    · exact abs_ne_zero.mp (by linarith [(hsourceLine index).vertical])
    · exact abs_ne_zero.mp (by linarith [(hexactLine index).vertical])
    · exact pureWZ2Proposition64ImageFamily_axisLine imageDelta g slabCenter
        anchorHeight translation hhalfHeight (by linarith) sourceFamily index
  have hfinalParams : ∀ index : Fin sourceFamily.card,
      tubeParamsOfTube (finalFamily.tube index) =
        pureWZ2Proposition64IsotropicTubeParams center scale
          (pureWZ2Proposition64ExactTubeParams (g anchorHeight) slabCenter
            halfHeight normalization translation
              (tubeParamsOfTube (sourceFamily.tube index))) := by
    intro index
    rw [show finalFamily.tube index =
        pureWZ2Proposition64IsotropicRebasedPaperTube center scale
          (exactFamily.tube index) by rfl,
      tubeParamsOfTube_isotropicRebasedPaperTube center scale
        (exactFamily.tube index)
        (abs_ne_zero.mp (by linarith [(hexactLine index).vertical])),
      hexactParams index]
  change
    |(tubeParamsOfTube (finalFamily.tube first)).a -
        (tubeParamsOfTube (finalFamily.tube second)).a| ≤ 600 * finalDelta ∧
      |(tubeParamsOfTube (finalFamily.tube first)).b -
        (tubeParamsOfTube (finalFamily.tube second)).b| ≤ 600 * finalDelta ∧
      |(tubeParamsOfTube (finalFamily.tube first)).c -
        (tubeParamsOfTube (finalFamily.tube second)).c| ≤ 600 * finalDelta ∧
      |(tubeParamsOfTube (finalFamily.tube first)).d -
        (tubeParamsOfTube (finalFamily.tube second)).d| ≤ 600 * finalDelta at htarget
  rw [hfinalParams first, hfinalParams second] at htarget
  have hisotropic := pureWZ2Proposition64IsotropicTubeParams_inverse_cluster
    center hscale hcenter
    (pureWZ2Proposition64ExactTubeParams (g anchorHeight) slabCenter
      halfHeight normalization translation
        (tubeParamsOfTube (sourceFamily.tube first)))
    (pureWZ2Proposition64ExactTubeParams (g anchorHeight) slabCenter
      halfHeight normalization translation
        (tubeParamsOfTube (sourceFamily.tube second)))
    htarget.1 htarget.2.1 htarget.2.2.1 htarget.2.2.2
  have hexact := pureWZ2Proposition64ExactTubeParams_inverse_cluster
    translation hanchorSlope hslabCenter hhalfHeight hhalfHeightOne
      hnormalization
    (tubeParamsOfTube (sourceFamily.tube first))
    (tubeParamsOfTube (sourceFamily.tube second))
    hisotropic.1 hisotropic.2.1 hisotropic.2.2.1 hisotropic.2.2.2
  change
    |(tubeParamsOfTube (sourceFamily.tube first)).a -
        (tubeParamsOfTube (sourceFamily.tube second)).a| ≤ _ ∧
      |(tubeParamsOfTube (sourceFamily.tube first)).b -
        (tubeParamsOfTube (sourceFamily.tube second)).b| ≤ _ ∧
      |(tubeParamsOfTube (sourceFamily.tube first)).c -
        (tubeParamsOfTube (sourceFamily.tube second)).c| ≤ _ ∧
      |(tubeParamsOfTube (sourceFamily.tube first)).d -
        (tubeParamsOfTube (sourceFamily.tube second)).d| ≤ _
  refine ⟨?_, ?_, ?_, ?_⟩
  · convert hexact.1 using 1
    ring
  · convert hexact.2.1 using 1
    ring
  · convert hexact.2.2.1 using 1
    ring
  · convert hexact.2.2.2 using 1
    ring

/-- Source parameter Frostman non-concentration bounds the Definition-2.12
conflict degree after first deleting zero-mass final carriers.  Because the
exact and isotropic stages are one-to-one, no multiplicity factor is lost. -/
theorem pureWZ2Proposition64_positivePaperConflictDegree
    {sourceDelta imageDelta finalDelta : ℝ}
    (g : ℝ → ℝ)
    (slabCenter anchorHeight halfHeight normalization : ℝ)
    (translation center : Point3) (scale : ℝ)
    (sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta)
    (htranslationHeight : translation 2 = 0)
    (hhalfHeight : 0 < halfHeight) (hhalfHeightOne : halfHeight ≤ 1)
    (hnormalization : 9 ≤ normalization)
    (hanchorSlope : |g anchorHeight| ≤ 8)
    (hslabCenter : |slabCenter| ≤ 1)
    (hsourceLine : WZ1PaperIsLineClass sourceFamily)
    (hexactLine : WZ1PaperIsLineClass
      (pureWZ2Proposition64ImageFamily imageDelta g slabCenter anchorHeight
        halfHeight normalization translation hhalfHeight
          (by linarith : 0 < normalization) sourceFamily))
    (finalShading : WZ1PaperTubeShading
      (pureWZ2Proposition64IsotropicPaperFamily
        (targetDelta := finalDelta)
        (pureWZ2Proposition64ImageFamily imageDelta g slabCenter anchorHeight
          halfHeight normalization translation hhalfHeight
            (by linarith : 0 < normalization) sourceFamily) center scale))
    (hpositiveLine : WZ1PaperIsLineClass
      (paperPositiveMassSubfamily finalShading).family)
    (hcenter : |center 2| ≤ 1) (hscale : 1 ≤ scale)
    (hfinalDelta : 0 < finalDelta)
    (C : ENNReal) (hFrostman : TubeParameterFrostmanBound sourceFamily C)
    (hsourceWidth : sourceDelta ≤
      24000 * normalization * finalDelta / halfHeight)
    (hwidthOne : 24000 * normalization * finalDelta / halfHeight ≤ 1) :
    ∀ reference : Fin (paperPositiveMassSubfamily finalShading).family.card,
      (((Finset.univ.filter fun other =>
        pureWZ2Proposition64PaperConflict
          (paperPositiveMassSubfamily finalShading).family reference other).card :
          ENNReal)) ≤
        C * Kakeya.realRpowENN
          (24000 * normalization * finalDelta / halfHeight) 2 *
            sourceFamily.enncard := by
  let exactFamily := pureWZ2Proposition64ImageFamily imageDelta g slabCenter
    anchorHeight halfHeight normalization translation hhalfHeight
      (by linarith : 0 < normalization) sourceFamily
  let finalFamily := pureWZ2Proposition64IsotropicPaperFamily
    (targetDelta := finalDelta) exactFamily center scale
  let selected := paperPositiveMassIndices finalShading
  let positive := paperPositiveMassSubfamily finalShading
  let width := 24000 * normalization * finalDelta / halfHeight
  intro reference
  let neighbors : Finset (Fin positive.family.card) :=
    Finset.univ.filter fun other =>
      pureWZ2Proposition64PaperConflict positive.family reference other
  let sourceNeighbors : Finset (Fin sourceFamily.card) :=
    neighbors.image positive.embedding
  let fullCluster : Finset (Fin sourceFamily.card) :=
    Finset.univ.filter fun source =>
      |(@tubeParams sourceDelta sourceFamily source).a -
          (@tubeParams sourceDelta sourceFamily
            (positive.embedding reference)).a| ≤ width ∧
        |(@tubeParams sourceDelta sourceFamily source).b -
          (@tubeParams sourceDelta sourceFamily
            (positive.embedding reference)).b| ≤ width ∧
        |(@tubeParams sourceDelta sourceFamily source).c -
          (@tubeParams sourceDelta sourceFamily
            (positive.embedding reference)).c| ≤ width ∧
        |(@tubeParams sourceDelta sourceFamily source).d -
          (@tubeParams sourceDelta sourceFamily
            (positive.embedding reference)).d| ≤ width
  have hreferenceMem : positive.embedding reference ∈ selected := by
    exact Finset.orderEmbOfFin_mem selected rfl reference
  have hsourceSubset : sourceNeighbors ⊆ fullCluster := by
    intro source hsource
    rcases Finset.mem_image.mp hsource with ⟨other, hother, rfl⟩
    have hotherConflict :
        pureWZ2Proposition64PaperConflict positive.family reference other :=
      (Finset.mem_filter.mp hother).2
    have hotherMem : positive.embedding other ∈ selected :=
      Finset.orderEmbOfFin_mem selected rfl other
    have hreferenceLine : WZ1PaperTubeInLineClass
        (finalFamily.tube (positive.embedding reference)) := by
      convert hpositiveLine reference using 1 <;> rfl
    have hotherLine : WZ1PaperTubeInLineClass
        (finalFamily.tube (positive.embedding other)) := by
      convert hpositiveLine other using 1 <;> rfl
    have hambientConflict : pureWZ2Proposition64PaperConflict finalFamily
        (positive.embedding reference) (positive.embedding other) := by
      change pureWZ2Proposition64PaperConflict
        (paperPositiveMassSubfamily finalShading).family reference other at hotherConflict
      change pureWZ2Proposition64PaperConflict
        (pureWZ2Proposition64IsotropicPaperFamily
          (targetDelta := finalDelta)
          (pureWZ2Proposition64ImageFamily imageDelta g slabCenter anchorHeight
            halfHeight normalization translation hhalfHeight
              (by linarith : 0 < normalization) sourceFamily) center scale)
        ((paperPositiveMassSubfamily finalShading).embedding reference)
        ((paperPositiveMassSubfamily finalShading).embedding other)
      refine ⟨(paperPositiveMassSubfamily finalShading).embedding.injective.ne
        hotherConflict.1, ?_⟩
      simpa only [Kakeya.Streamlined.TubeSubfamily.tube_eq] using
        hotherConflict.2
    have hambientConflict' : pureWZ2Proposition64PaperConflict finalFamily
        (positive.embedding other) (positive.embedding reference) :=
      pureWZ2Proposition64PaperConflict_symm finalFamily _ _ hambientConflict
    have hcluster :=
      pureWZ2Proposition64_sourceParameterCluster_of_finalConflict g
        slabCenter anchorHeight halfHeight normalization translation center
        scale sourceFamily htranslationHeight hhalfHeight hhalfHeightOne
        hnormalization hanchorSlope hslabCenter hsourceLine hexactLine
        hcenter hscale hfinalDelta
        hotherLine hreferenceLine
        (pureWZ2Proposition64_isotropicTube_midpoint_norm_le_three
          exactFamily center scale (positive.embedding other) hotherLine)
        (pureWZ2Proposition64_isotropicTube_midpoint_norm_le_three
          exactFamily center scale (positive.embedding reference) hreferenceLine)
        hambientConflict'
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    change
      |(tubeParamsOfTube (sourceFamily.tube (positive.embedding other))).a -
          (tubeParamsOfTube (sourceFamily.tube
            (positive.embedding reference))).a| ≤ width ∧
        |(tubeParamsOfTube (sourceFamily.tube (positive.embedding other))).b -
          (tubeParamsOfTube (sourceFamily.tube
            (positive.embedding reference))).b| ≤ width ∧
        |(tubeParamsOfTube (sourceFamily.tube (positive.embedding other))).c -
          (tubeParamsOfTube (sourceFamily.tube
            (positive.embedding reference))).c| ≤ width ∧
        |(tubeParamsOfTube (sourceFamily.tube (positive.embedding other))).d -
          (tubeParamsOfTube (sourceFamily.tube
            (positive.embedding reference))).d| ≤ width
    have hb : 2400 * finalDelta / halfHeight ≤ width := by
      dsimp only [width]
      have hratio : 0 ≤ finalDelta / halfHeight := by positivity
      have hcoefficient : 2400 ≤ 24000 * normalization := by nlinarith
      calc
        2400 * finalDelta / halfHeight =
            2400 * (finalDelta / halfHeight) := by ring
        _ ≤ (24000 * normalization) * (finalDelta / halfHeight) :=
          mul_le_mul_of_nonneg_right hcoefficient hratio
        _ = 24000 * normalization * finalDelta / halfHeight := by ring
    have hc : 12000 * normalization * finalDelta / halfHeight ≤ width := by
      dsimp only [width]
      have hratio : 0 ≤ normalization * finalDelta / halfHeight := by positivity
      calc
        12000 * normalization * finalDelta / halfHeight =
            12000 * (normalization * finalDelta / halfHeight) := by ring
        _ ≤ 24000 * (normalization * finalDelta / halfHeight) :=
          mul_le_mul_of_nonneg_right (by norm_num) hratio
        _ = 24000 * normalization * finalDelta / halfHeight := by ring
    have hd : 1200 * finalDelta / halfHeight ≤ width := by
      have hratio : 0 ≤ finalDelta / halfHeight := by positivity
      have hsmall : 1200 * finalDelta / halfHeight ≤
          2400 * finalDelta / halfHeight := by
        calc
          1200 * finalDelta / halfHeight =
              1200 * (finalDelta / halfHeight) := by ring
          _ ≤ 2400 * (finalDelta / halfHeight) :=
            mul_le_mul_of_nonneg_right (by norm_num) hratio
          _ = 2400 * finalDelta / halfHeight := by ring
      exact hsmall.trans hb
    exact ⟨hcluster.1, hcluster.2.1.trans hb,
      hcluster.2.2.1.trans hc, hcluster.2.2.2.trans hd⟩
  have hsourceCard : (sourceNeighbors.card : ENNReal) ≤
      C * Kakeya.realRpowENN width 2 * sourceFamily.enncard := by
    have hcard : (sourceNeighbors.card : ENNReal) ≤
        (fullCluster.card : ENNReal) := by
      exact_mod_cast Finset.card_le_card hsourceSubset
    exact hcard.trans (by
      simpa [TubeParameterFrostmanBound, fullCluster, width] using
        hFrostman width hsourceWidth hwidthOne (positive.embedding reference))
  have hcardEq : sourceNeighbors.card = neighbors.card := by
    exact Finset.card_image_of_injective neighbors positive.embedding.injective
  change (neighbors.card : ENNReal) ≤ _
  rw [← hcardEq]
  exact hsourceCard

/-- Family-free packing bound for the final paper-conflict graph.

A final conflict pulls back to a four-parameter source box of width `width`.
On the fixed vertical chart this box lies in a paper line-metric ball of
radius `6 * width`.  Essential distinctness of the literal source family then
bounds the degree without retaining the ambient source cardinality. -/
theorem pureWZ2Proposition64_positivePaperConflictPackingDegree
    {sourceDelta imageDelta finalDelta : ℝ}
    (g : ℝ → ℝ)
    (slabCenter anchorHeight halfHeight normalization : ℝ)
    (translation center : Point3) (scale : ℝ)
    (sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta)
    (htranslationHeight : translation 2 = 0)
    (hhalfHeight : 0 < halfHeight) (hhalfHeightOne : halfHeight ≤ 1)
    (hnormalization : 9 ≤ normalization)
    (hanchorSlope : |g anchorHeight| ≤ 8)
    (hslabCenter : |slabCenter| ≤ 1)
    (hsourceLine : WZ1PaperIsLineClass sourceFamily)
    (hsourceDistinct : WZ2PaperOrdinaryIsEssentiallyDistinct sourceFamily)
    (hsourceBounded : HasBoundedBase sourceFamily 4)
    (hexactLine : WZ1PaperIsLineClass
      (pureWZ2Proposition64ImageFamily imageDelta g slabCenter anchorHeight
        halfHeight normalization translation hhalfHeight
          (by linarith : 0 < normalization) sourceFamily))
    (finalShading : WZ1PaperTubeShading
      (pureWZ2Proposition64IsotropicPaperFamily
        (targetDelta := finalDelta)
        (pureWZ2Proposition64ImageFamily imageDelta g slabCenter anchorHeight
          halfHeight normalization translation hhalfHeight
            (by linarith : 0 < normalization) sourceFamily) center scale))
    (hpositiveLine : WZ1PaperIsLineClass
      (paperPositiveMassSubfamily finalShading).family)
    (hcenter : |center 2| ≤ 1) (hscale : 1 ≤ scale)
    (hsourceDelta : 0 < sourceDelta) (hfinalDelta : 0 < finalDelta) :
    let width := 24000 * normalization * finalDelta / halfHeight
    ∀ reference : Fin (paperPositiveMassSubfamily finalShading).family.card,
      (((Finset.univ.filter fun other =>
        pureWZ2Proposition64PaperConflict
          (paperPositiveMassSubfamily finalShading).family reference other).card :
          ENNReal)) ≤
        ((2561 *
          (2 * Nat.ceil (6 * width / (sourceDelta / 10000)) + 1) ^ 6 : ℕ) :
          ENNReal) := by
  dsimp only
  let exactFamily := pureWZ2Proposition64ImageFamily imageDelta g slabCenter
    anchorHeight halfHeight normalization translation hhalfHeight
      (by linarith : 0 < normalization) sourceFamily
  let finalFamily := pureWZ2Proposition64IsotropicPaperFamily
    (targetDelta := finalDelta) exactFamily center scale
  let positive := paperPositiveMassSubfamily finalShading
  let width := 24000 * normalization * finalDelta / halfHeight
  have hwidth : 0 < width := by
    dsimp only [width]
    positivity
  intro reference
  let neighbors : Finset (Fin positive.family.card) :=
    Finset.univ.filter fun other =>
      pureWZ2Proposition64PaperConflict positive.family reference other
  let sourceNeighbors : Finset (Fin sourceFamily.card) :=
    neighbors.image positive.embedding
  let sourceBall : Finset (Fin sourceFamily.card) :=
    Finset.univ.filter fun source =>
      wz1PaperLineDistance (sourceFamily.tube source)
        (sourceFamily.tube (positive.embedding reference)) ≤ 6 * width
  have hsourceSubset : sourceNeighbors ⊆ sourceBall := by
    intro source hsource
    rcases Finset.mem_image.mp hsource with ⟨other, hother, rfl⟩
    have hotherConflict :
        pureWZ2Proposition64PaperConflict positive.family reference other :=
      (Finset.mem_filter.mp hother).2
    have hreferenceLine : WZ1PaperTubeInLineClass
        (finalFamily.tube (positive.embedding reference)) := by
      convert hpositiveLine reference using 1 <;> rfl
    have hotherLine : WZ1PaperTubeInLineClass
        (finalFamily.tube (positive.embedding other)) := by
      convert hpositiveLine other using 1 <;> rfl
    have hambientConflict : pureWZ2Proposition64PaperConflict finalFamily
        (positive.embedding reference) (positive.embedding other) := by
      change pureWZ2Proposition64PaperConflict
        (paperPositiveMassSubfamily finalShading).family reference other at hotherConflict
      change pureWZ2Proposition64PaperConflict finalFamily
        (positive.embedding reference) (positive.embedding other)
      refine ⟨positive.embedding.injective.ne hotherConflict.1, ?_⟩
      simpa only [Kakeya.Streamlined.TubeSubfamily.tube_eq] using
        hotherConflict.2
    have hcluster :=
      pureWZ2Proposition64_sourceParameterCluster_of_finalConflict g
        slabCenter anchorHeight halfHeight normalization translation center
        scale sourceFamily htranslationHeight hhalfHeight hhalfHeightOne
        hnormalization hanchorSlope hslabCenter hsourceLine hexactLine
        hcenter hscale hfinalDelta hreferenceLine hotherLine
        (pureWZ2Proposition64_isotropicTube_midpoint_norm_le_three
          exactFamily center scale (positive.embedding reference)
            hreferenceLine)
        (pureWZ2Proposition64_isotropicTube_midpoint_norm_le_three
          exactFamily center scale (positive.embedding other) hotherLine)
        hambientConflict
    have hb : 2400 * finalDelta / halfHeight ≤ width := by
      dsimp only [width]
      have hratio : 0 ≤ finalDelta / halfHeight := by positivity
      have hcoefficient : 2400 ≤ 24000 * normalization := by nlinarith
      calc
        2400 * finalDelta / halfHeight =
            2400 * (finalDelta / halfHeight) := by ring
        _ ≤ (24000 * normalization) * (finalDelta / halfHeight) :=
          mul_le_mul_of_nonneg_right hcoefficient hratio
        _ = 24000 * normalization * finalDelta / halfHeight := by ring
    have hc : 12000 * normalization * finalDelta / halfHeight ≤ width := by
      dsimp only [width]
      have hratio : 0 ≤ normalization * finalDelta / halfHeight := by positivity
      calc
        12000 * normalization * finalDelta / halfHeight =
            12000 * (normalization * finalDelta / halfHeight) := by ring
        _ ≤ 24000 * (normalization * finalDelta / halfHeight) :=
          mul_le_mul_of_nonneg_right (by norm_num) hratio
        _ = 24000 * normalization * finalDelta / halfHeight := by ring
    have hd : 1200 * finalDelta / halfHeight ≤ width := by
      have hratio : 0 ≤ finalDelta / halfHeight := by positivity
      calc
        1200 * finalDelta / halfHeight =
            1200 * (finalDelta / halfHeight) := by ring
        _ ≤ 2400 * (finalDelta / halfHeight) :=
          mul_le_mul_of_nonneg_right (by norm_num) hratio
        _ = 2400 * finalDelta / halfHeight := by ring
        _ ≤ width := hb
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    have hdistance := wz1PaperLineDistance_le_of_tubeParams_close
      (hsourceLine (positive.embedding reference))
      (hsourceLine (positive.embedding other)) hwidth.le
      hcluster.1 (hcluster.2.1.trans hb) (hcluster.2.2.1.trans hc)
      (hcluster.2.2.2.trans hd)
    rw [wz1PaperLineDistance_symm]
    exact hdistance
  have hsourceBoundedEight : HasBoundedBase sourceFamily 8 := by
    intro source
    exact (hsourceBounded source).trans (by norm_num)
  have hsourcePacked := pureWZ2_ordinary_line_conflict_degree_within
    hsourceDelta (6 * width) (by positivity) hsourceLine
      hsourceBoundedEight hsourceDistinct (positive.embedding reference)
  have hcard : sourceNeighbors.card ≤ sourceBall.card :=
    Finset.card_le_card hsourceSubset
  have hsourceBall : sourceBall.card ≤
      2561 * (2 * Nat.ceil (6 * width / (sourceDelta / 10000)) + 1) ^ 6 := by
    simpa [sourceBall, pureWZ2OrdinaryLineConflictDegreeWithin,
      Fin.prod_univ_succ, mul_assoc, mul_left_comm, mul_comm, pow_succ]
      using hsourcePacked
  have hcardEq : sourceNeighbors.card = neighbors.card :=
    Finset.card_image_of_injective neighbors positive.embedding.injective
  change (neighbors.card : ENNReal) ≤ _
  rw [← hcardEq]
  exact_mod_cast hcard.trans hsourceBall

end Kakeya.Assouad

end
