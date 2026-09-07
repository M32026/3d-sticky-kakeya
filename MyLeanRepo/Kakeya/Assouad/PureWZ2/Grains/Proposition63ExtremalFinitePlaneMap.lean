import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63ExtremalOneScalePlaneMap
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.FiniteScaleLipschitzBridge
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.AlignedPowerCoarseScale

/-!
# Extremality-restored finite plane-map iteration for WZ2 Proposition 6.3

This is the WZ1-style backward-loss/forward-runtime iteration.  Every
one-scale call returns an already-extremal shading on the fixed ambient
family before the next call starts.  The exact per-step mass losses are kept
only as an audit ledger; they are never used to restore extremality across
several spatial scales.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory Set Finset

attribute [local instance] Classical.propDecidable

/-- Final output of a finite sequence of extremality-restored one-scale
steps.  All variation estimates use restrictions of the caller's single
ambient plane-map function. -/
structure Proposition63ExtremalFinitePlaneMapData
    {delta sigma incidence : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (current : WZ1PaperTubeShading family)
    (currentMap : PaperWZ1WeakPlaneMapData current incidence)
    (outputLoss : ℝ) {N : ℕ}
    (targetScale : Fin N → WZ2PaperRequestedScale delta) where
  shading : WZ1PaperTubeShading family
  subshading : PaperIsSubshading shading current
  cubical : WZ1PaperIsCubicalShading shading
  planeMap : PaperWZ1WeakPlaneMapData shading incidence
  same_plane_map : planeMap.planeMap = currentMap.planeMap
  variation : ∀ index : Fin N, ∀ point ∈ shading.union,
    ∀ other ∈ shading.union,
      dist point other ≤ (targetScale index).1 →
        dist (planeMap.planeMap point) (planeMap.planeMap other) ≤
          (targetScale index).1
  massLoss : ENNReal
  massLoss_pos : 0 < massLoss
  massLoss_ne_top : massLoss ≠ ⊤
  mass_retention : massLoss⁻¹ * current.mass ≤ shading.mass
  extremal : WZ2PaperCroppedIsExtremal sigma outputLoss family shading

/-- Stable output after the finite metric assembly and its final fixed
residue refinement. -/
structure Proposition63ExtremalFiniteLipschitzData
    {delta sigma incidence : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (current : WZ1PaperTubeShading family)
    (currentMap : PaperWZ1WeakPlaneMapData current incidence)
    (outputLoss coefficient : ℝ) where
  shading : WZ1PaperTubeShading family
  subshading : PaperIsSubshading shading current
  cubical : WZ1PaperIsCubicalShading shading
  planeMap : PaperWZ1WeakPlaneMapData shading incidence
  same_plane_map : planeMap.planeMap = currentMap.planeMap
  lipschitz : LipschitzWith (Real.toNNReal coefficient)
    (fun point : {point : Point3 // point ∈ shading.union} =>
      planeMap.planeMap point)
  massLoss : ENNReal
  massLoss_pos : 0 < massLoss
  massLoss_ne_top : massLoss ≠ ⊤
  mass_retention : massLoss⁻¹ * current.mass ≤ shading.mass
  extremal : WZ2PaperCroppedIsExtremal sigma outputLoss family shading

/-- Backward-selected loss schedule for finitely many target scales.  Its
single runtime method accepts one genuine ambient re-entry whose losses are
strong enough for every constituent one-scale schedule. -/
structure Proposition63ExtremalFinitePlaneMapScheduleData
    (sigma outputLoss : ℝ) (N : ℕ) where
  rootSourceLoss : ℝ
  rootNormalizationLoss : ℝ
  inputLoss : ℝ
  stepOutputLoss : Fin N → ℝ
  delta₀ : ℝ
  rootSourceLoss_pos : 0 < rootSourceLoss
  rootNormalizationLoss_pos : 0 < rootNormalizationLoss
  rootSourceLoss_le_half : rootSourceLoss ≤ rootNormalizationLoss / 2
  rootNormalizationLoss_le_output : rootNormalizationLoss ≤ outputLoss
  inputLoss_pos : 0 < inputLoss
  inputLoss_le_output : inputLoss ≤ outputLoss
  stepOutputLoss_pos : ∀ index, 0 < stepOutputLoss index
  stepOutputLoss_le_output : ∀ index, stepOutputLoss index ≤ outputLoss
  delta₀_pos : 0 < delta₀
  delta₀_le_one : delta₀ ≤ 1
  run :
    ∀ {delta : ℝ}, 0 < delta → delta ≤ delta₀ →
      ∀ {ambientSourceLoss ambientNormalizationLoss : ℝ}
        {ambientFamily : Kakeya.Streamlined.TubeFamily delta}
        {ambientShading : WZ1PaperTubeShading ambientFamily},
        ∀ (ambientReentry : PureWZ2PropStickyReentryData
          (sigma := sigma) ambientShading 0 ambientSourceLoss
            ambientNormalizationLoss),
          ∀ (hambientSource : ambientSourceLoss ≤ rootSourceLoss)
            (hambientNormalization :
              ambientNormalizationLoss ≤ rootNormalizationLoss),
          ∀ (current : WZ1PaperTubeShading ambientFamily),
            WZ2PaperCroppedIsExtremal sigma inputLoss
              ambientFamily current →
            PaperIsSubshading current ambientShading →
            ∀ {incidence : ℝ},
              ∀ (currentMap : PaperWZ1WeakPlaneMapData current incidence),
                (∀ first second,
                  wz1PaperGridIndex delta first =
                      wz1PaperGridIndex delta second →
                    currentMap.planeMap first = currentMap.planeMap second) →
                0 ≤ incidence →
                ∀ targetScale : Fin N → WZ2PaperRequestedScale delta,
                  (∀ index, Real.rpow delta (1 - stepOutputLoss index) ≤
                    (targetScale index).1) →
                  (∀ index, (targetScale index).1 ≤
                    Real.rpow delta (stepOutputLoss index)) →
                  (∀ index, incidence ≤ (targetScale index).1) →
                  ∀ K : Fin N → ℕ, (∀ index, 0 < K index) →
                    (∀ index, (targetScale index).1 =
                      (K index : ℝ) * delta) →
                    Nonempty (Proposition63ExtremalFinitePlaneMapData
                      (sigma := sigma) current currentMap outputLoss
                        targetScale)

/-- The stable one-scale producer interface used by backward finite
iteration.  Its input loss and scale threshold are existential and precede
all runtime family, shading, map, and target-scale data. -/
def Proposition63ExtremalOneScalePlaneMapConclusion : Prop :=
  ∀ sigma : ℝ, PureWZ2CriticalPackage sigma →
    ∀ outputLoss : ℝ, 0 < outputLoss → outputLoss ≤ 1 →
      Nonempty (Proposition63ExtremalOneScalePlaneMapScheduleData
        sigma outputLoss)

theorem proposition63_extremal_one_scale_plane_map :
    Proposition63ExtremalOneScalePlaneMapConclusion := by
  intro sigma critical outputLoss outputLossPos outputLossOne
  exact proposition63_extremal_one_scale_plane_map_schedule sigma critical
    outputLoss outputLossPos outputLossOne

private theorem proposition63_extremal_finite_plane_map_schedule_zero
    (sigma outputLoss : ℝ) (houtputLoss : 0 < outputLoss) :
    Nonempty (Proposition63ExtremalFinitePlaneMapScheduleData
      sigma outputLoss 0) := by
  let rootNormalizationLoss := outputLoss / 2
  let rootSourceLoss := rootNormalizationLoss / 4
  refine ⟨{
    rootSourceLoss := rootSourceLoss
    rootNormalizationLoss := rootNormalizationLoss
    inputLoss := outputLoss
    stepOutputLoss := Fin.elim0
    delta₀ := 1
    rootSourceLoss_pos := by dsimp only [rootSourceLoss, rootNormalizationLoss]; positivity
    rootNormalizationLoss_pos := by dsimp only [rootNormalizationLoss]; positivity
    rootSourceLoss_le_half := by
      dsimp only [rootSourceLoss, rootNormalizationLoss]
      linarith [houtputLoss]
    rootNormalizationLoss_le_output := by
      dsimp only [rootNormalizationLoss]
      linarith [houtputLoss]
    inputLoss_pos := houtputLoss
    inputLoss_le_output := le_rfl
    stepOutputLoss_pos := fun index => Fin.elim0 index
    stepOutputLoss_le_output := fun index => Fin.elim0 index
    delta₀_pos := by norm_num
    delta₀_le_one := le_rfl
    run := ?_
  }⟩
  intro delta deltaPos deltaLe ambientSourceLoss ambientNormalizationLoss
    ambientFamily ambientShading ambientReentry ambientSourceLe
    ambientNormalizationLe current currentExtremal currentSub incidence
    currentMap currentCellwise incidenceNonnegative targetScale targetLower
    targetUpper incidenceTarget K KPos targetAligned
  refine ⟨{
    shading := current
    subshading := fun _ => Set.Subset.rfl
    cubical := currentExtremal.cubical
    planeMap := currentMap
    same_plane_map := rfl
    variation := ?_
    massLoss := 1
    massLoss_pos := by norm_num
    massLoss_ne_top := by norm_num
    mass_retention := by simp
    extremal := currentExtremal
  }⟩
  intro index
  exact Fin.elim0 index

/-- Build the finite schedule backwards in the number of remaining scales,
then run it forwards. -/
theorem proposition63_extremal_finite_plane_map_schedule
    (sigma : ℝ) (critical : PureWZ2CriticalPackage sigma)
    (outputLoss : ℝ) (houtputLoss : 0 < outputLoss)
    (houtputLossOne : outputLoss ≤ 1) :
    ∀ N : ℕ, Nonempty (Proposition63ExtremalFinitePlaneMapScheduleData
      sigma outputLoss N) := by
  intro N
  induction N with
  | zero =>
      exact proposition63_extremal_finite_plane_map_schedule_zero
        sigma outputLoss houtputLoss
  | succ N inductionHypothesis =>
      rcases inductionHypothesis with ⟨tail⟩
      rcases proposition63_extremal_one_scale_plane_map_schedule sigma critical
          tail.inputLoss tail.inputLoss_pos
          (tail.inputLoss_le_output.trans houtputLossOne) with ⟨head⟩
      let common : ℝ := min head.rootSourceLoss <|
        min head.rootNormalizationLoss <|
          min tail.rootSourceLoss tail.rootNormalizationLoss
      let rootNormalizationLoss : ℝ := common
      let rootSourceLoss : ℝ := common / 4
      let delta₀ : ℝ := min head.delta₀ tail.delta₀
      have commonPos : 0 < common := by
        dsimp only [common]
        exact lt_min head.rootSourceLoss_pos <|
          lt_min head.rootNormalizationLoss_pos <|
            lt_min tail.rootSourceLoss_pos tail.rootNormalizationLoss_pos
      refine ⟨{
        rootSourceLoss := rootSourceLoss
        rootNormalizationLoss := rootNormalizationLoss
        inputLoss := head.inputLoss
        stepOutputLoss := Fin.cases tail.inputLoss tail.stepOutputLoss
        delta₀ := delta₀
        rootSourceLoss_pos := by dsimp only [rootSourceLoss]; positivity
        rootNormalizationLoss_pos := by
          dsimp only [rootNormalizationLoss]
          exact commonPos
        rootSourceLoss_le_half := by
          dsimp only [rootSourceLoss, rootNormalizationLoss]
          linarith [commonPos]
        rootNormalizationLoss_le_output := by
          dsimp only [rootNormalizationLoss, common]
          exact (((min_le_right _ _).trans <|
            (min_le_right _ _)).trans <|
              (min_le_right _ _)).trans
                tail.rootNormalizationLoss_le_output
        inputLoss_pos := head.inputLoss_pos
        inputLoss_le_output :=
          head.inputLoss_le_output.trans tail.inputLoss_le_output
        stepOutputLoss_pos := Fin.cases tail.inputLoss_pos
          tail.stepOutputLoss_pos
        stepOutputLoss_le_output := Fin.cases tail.inputLoss_le_output
          tail.stepOutputLoss_le_output
        delta₀_pos := lt_min head.delta₀_pos tail.delta₀_pos
        delta₀_le_one := (min_le_left _ _).trans head.delta₀_le_one
        run := ?_
      }⟩
      intro delta deltaPos deltaLe ambientSourceLoss ambientNormalizationLoss
        ambientFamily ambientShading ambientReentry ambientSourceLe
        ambientNormalizationLe current currentExtremal currentSub incidence
        currentMap currentCellwise incidenceNonnegative targetScale
        targetLower targetUpper incidenceTarget K KPos targetAligned
      have deltaLeHead : delta ≤ head.delta₀ :=
        deltaLe.trans (min_le_left _ _)
      have deltaLeTail : delta ≤ tail.delta₀ :=
        deltaLe.trans (min_le_right _ _)
      have sourceLeHead : ambientSourceLoss ≤ head.rootSourceLoss :=
        ambientSourceLe.trans <| by
          dsimp only [rootSourceLoss, rootNormalizationLoss, common]
          exact (div_le_self commonPos.le (by norm_num)).trans <|
            min_le_left _ _
      have normalizationLeHead :
          ambientNormalizationLoss ≤ head.rootNormalizationLoss :=
        ambientNormalizationLe.trans <| by
          dsimp only [rootNormalizationLoss, common]
          exact (min_le_right _ _).trans (min_le_left _ _)
      have sourceLeTail : ambientSourceLoss ≤ tail.rootSourceLoss :=
        ambientSourceLe.trans <| by
          dsimp only [rootSourceLoss, rootNormalizationLoss, common]
          apply (div_le_self commonPos.le (by norm_num)).trans
          exact (min_le_right _ _).trans <|
            (min_le_right _ _).trans (min_le_left _ _)
      have normalizationLeTail :
          ambientNormalizationLoss ≤ tail.rootNormalizationLoss :=
        ambientNormalizationLe.trans <| by
          dsimp only [rootNormalizationLoss, common]
          exact (min_le_right _ _).trans <|
            (min_le_right _ _).trans (min_le_right _ _)
      let firstIndex : Fin (N + 1) := ⟨0, Nat.zero_lt_succ N⟩
      have headLower :
          Real.rpow delta (1 - tail.inputLoss) ≤
            (targetScale firstIndex).1 := by
        convert targetLower firstIndex using 1 <;> rfl
      have headUpper : (targetScale firstIndex).1 ≤
          Real.rpow delta tail.inputLoss := by
        convert targetUpper firstIndex using 1 <;> rfl
      rcases head.run deltaPos deltaLeHead ambientReentry sourceLeHead
          normalizationLeHead current currentExtremal currentSub currentMap
          currentCellwise incidenceNonnegative (targetScale firstIndex)
          headLower headUpper (incidenceTarget firstIndex) (K firstIndex)
          (KPos firstIndex) (targetAligned firstIndex) with ⟨first⟩
      let tailScale : Fin N → WZ2PaperRequestedScale delta :=
        fun index => targetScale index.succ
      let tailK : Fin N → ℕ := fun index => K index.succ
      have firstSubAmbient : PaperIsSubshading first.shading ambientShading :=
        fun index point pointMem => currentSub index
          (first.subshading index pointMem)
      have firstCellwise : ∀ firstPoint secondPoint,
          wz1PaperGridIndex delta firstPoint =
              wz1PaperGridIndex delta secondPoint →
            first.planeMap.planeMap firstPoint =
              first.planeMap.planeMap secondPoint := by
        intro firstPoint secondPoint sameCell
        rw [first.same_plane_map]
        exact currentCellwise firstPoint secondPoint sameCell
      rcases tail.run deltaPos deltaLeTail ambientReentry sourceLeTail
          normalizationLeTail first.shading first.extremal firstSubAmbient
          first.planeMap firstCellwise incidenceNonnegative tailScale
          (fun index => by simpa using targetLower index.succ)
          (fun index => by simpa using targetUpper index.succ)
          (fun index => incidenceTarget index.succ) tailK
          (fun index => KPos index.succ)
          (fun index => targetAligned index.succ) with ⟨final⟩
      let massLoss := first.massLoss * final.massLoss
      have massLossPos : 0 < massLoss :=
        ENNReal.mul_pos first.massLoss_pos.ne' final.massLoss_pos.ne'
      have massLossTop : massLoss ≠ ⊤ :=
        ENNReal.mul_ne_top first.massLoss_ne_top final.massLoss_ne_top
      have massRetention : massLoss⁻¹ * current.mass ≤ final.shading.mass := by
        rw [ENNReal.mul_inv (Or.inl first.massLoss_pos.ne')
          (Or.inl first.massLoss_ne_top)]
        calc
          (first.massLoss⁻¹ * final.massLoss⁻¹) * current.mass =
              final.massLoss⁻¹ * (first.massLoss⁻¹ * current.mass) := by ring
          _ ≤ final.massLoss⁻¹ * first.shading.mass := by
            exact mul_le_mul_left' first.mass_retention _
          _ ≤ final.shading.mass := final.mass_retention
      refine ⟨{
        shading := final.shading
        subshading := fun index point pointMem =>
          first.subshading index (final.subshading index pointMem)
        cubical := final.cubical
        planeMap := final.planeMap
        same_plane_map := final.same_plane_map.trans first.same_plane_map
        variation := ?_
        massLoss := massLoss
        massLoss_pos := massLossPos
        massLoss_ne_top := massLossTop
        mass_retention := massRetention
        extremal := final.extremal
      }⟩
      intro index
      refine Fin.cases ?_ (fun tailIndex => ?_) index
      · intro point pointMem other otherMem distanceBound
        have pointFirst : point ∈ first.shading.union := by
          rcases pointMem with ⟨index, pointMem⟩
          exact ⟨index, final.subshading index pointMem⟩
        have otherFirst : other ∈ first.shading.union := by
          rcases otherMem with ⟨index, otherMem⟩
          exact ⟨index, final.subshading index otherMem⟩
        rw [final.same_plane_map]
        exact first.variation point pointFirst other otherFirst distanceBound
      · intro point pointMem other otherMem distanceBound
        exact final.variation tailIndex point pointMem other otherMem
          distanceBound

/-- Add the final fixed residue refinement to an extremality-restored finite
iteration.  The only new loss is `27`; the product stored in `data.massLoss`
is retained for auditing and mass bookkeeping, but is not used to restore
extremality. -/
theorem Proposition63ExtremalFinitePlaneMapData.toLipschitz
    {delta sigma incidence sourceLoss outputLoss coefficient diameter : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {current : WZ1PaperTubeShading family}
    {currentMap : PaperWZ1WeakPlaneMapData current incidence}
    {N : ℕ} {targetScale : Fin N → WZ2PaperRequestedScale delta}
    (data : Proposition63ExtremalFinitePlaneMapData
      (sigma := sigma) current currentMap sourceLoss targetScale)
    (spatialScale variationScale : Fin N → ℝ)
    (hspatialScale : ∀ index, spatialScale index ≤ (targetScale index).1)
    (hvariationScale : ∀ index,
      (targetScale index).1 ≤ variationScale index)
    (hcoefficient : 0 < coefficient)
    (hcell : ∀ first second,
      wz1PaperGridIndex delta first = wz1PaperGridIndex delta second →
        data.planeMap.planeMap first = data.planeMap.planeMap second)
    (hdiameter : ∀ first ∈ data.shading.union,
      ∀ second ∈ data.shading.union, dist first second ≤ diameter)
    (hcovers : ∀ d : ℝ, delta < d → d ≤ diameter →
      coefficient * d < 2 →
      ∃ index : Fin N, d ≤ spatialScale index ∧
        variationScale index ≤ coefficient * d)
    (hsourceOutput : sourceLoss ≤ outputLoss)
    (houtputLoss : 0 < outputLoss)
    (hrestore :
      (27 : ENNReal) * Kakeya.realRpowENN delta outputLoss ≤
        Kakeya.realRpowENN delta sourceLoss) :
    Nonempty (Proposition63ExtremalFiniteLipschitzData
      (sigma := sigma) current currentMap outputLoss coefficient) := by
  let spatial : ℕ → ℝ := fun index =>
    if h : index < N then spatialScale ⟨index, h⟩ else 1
  let variationBound : ℕ → ℝ := fun index =>
    if h : index < N then variationScale ⟨index, h⟩ else 1
  have variation : ∀ index, index < N → ∀ first ∈ data.shading.union,
      ∀ second ∈ data.shading.union,
        dist first second ≤ spatial index →
        dist (data.planeMap.planeMap first)
            (data.planeMap.planeMap second) ≤ variationBound index := by
    intro index indexLt first firstMem second secondMem distanceBound
    have distanceSpatial : dist first second ≤
        spatialScale ⟨index, indexLt⟩ := by
      simpa only [spatial, dif_pos indexLt] using distanceBound
    have targetDistance : dist first second ≤
        (targetScale ⟨index, indexLt⟩).1 :=
      distanceSpatial.trans (hspatialScale ⟨index, indexLt⟩)
    have varied := data.variation ⟨index, indexLt⟩ first firstMem second
      secondMem targetDistance
    exact varied.trans <| by
      simpa only [variationBound, dif_pos indexLt] using
        hvariationScale ⟨index, indexLt⟩
  rcases paper_finite_scale_variation_to_lipschitz
      (coefficient := coefficient) (diameter := diameter)
      data.extremal.delta_pos hcoefficient data.cubical data.planeMap hcell
      N spatial variationBound variation hdiameter (by
        intro d deltaD dDiameter coefficientD
        rcases hcovers d deltaD dDiameter coefficientD with
          ⟨index, distanceLe, variationLe⟩
        exact ⟨index.val, index.isLt, by
          simpa only [spatial, dif_pos index.isLt] using distanceLe, by
          simpa only [variationBound, dif_pos index.isLt] using
            variationLe⟩) with
    ⟨selected, selectedMap, selectedSub, sameMap, selectedCubical,
      _multiplicity, massRetention27, selectedLipschitz⟩
  have selectedSubCurrent : PaperIsSubshading selected current :=
    fun index point pointMem =>
      data.subshading index (selectedSub index pointMem)
  have combinedMass :
      ((27 : ENNReal) * data.massLoss)⁻¹ * current.mass ≤ selected.mass := by
    rw [ENNReal.mul_inv (Or.inl (by norm_num))
      (Or.inl (by norm_num : (27 : ENNReal) ≠ ⊤))]
    calc
      ((27 : ENNReal)⁻¹ * data.massLoss⁻¹) * current.mass =
          27⁻¹ * (data.massLoss⁻¹ * current.mass) := by ring
      _ ≤ 27⁻¹ * data.shading.mass := by
        exact mul_le_mul_left' data.mass_retention _
      _ ≤ selected.mass := by
        apply (ENNReal.inv_mul_le_iff (by norm_num) (by norm_num)).2
        simpa [mul_comm] using massRetention27
  have selectedExtremal : WZ2PaperCroppedIsExtremal
      sigma outputLoss family selected := by
    have massRetentionInv :
        (27 : ENNReal)⁻¹ * data.shading.mass ≤ selected.mass := by
      apply (ENNReal.inv_mul_le_iff (by norm_num) (by norm_num)).2
      simpa [mul_comm] using massRetention27
    apply transfer_cropped_extremal_to_subshading 27 (by norm_num)
      (by norm_num) data.extremal selectedSub massRetentionInv selectedCubical
      hsourceOutput hrestore data.extremal.delta_pos
      data.extremal.delta_le_one houtputLoss
  exact ⟨{
    shading := selected
    subshading := selectedSubCurrent
    cubical := selectedCubical
    planeMap := selectedMap
    same_plane_map := sameMap.trans data.same_plane_map
    lipschitz := selectedLipschitz
    massLoss := 27 * data.massLoss
    massLoss_pos := ENNReal.mul_pos (by norm_num) data.massLoss_pos.ne'
    massLoss_ne_top := ENNReal.mul_ne_top (by norm_num) data.massLoss_ne_top
    mass_retention := combinedMass
    extremal := selectedExtremal
  }⟩

/-- WZ1's finite power-scale metric argument, stated for the integer-aligned
scales produced by the WZ2 one-scale iterator.  Coordinate `i` represents
the paper scale `s^(i+1)`; rounding is harmless because the actual target is
between that ideal scale and twice it. -/
theorem Proposition63ExtremalFinitePlaneMapData.toPowerScaleLipschitz
    {delta sigma incidence sourceLoss outputLoss coefficient diameter s : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {current : WZ1PaperTubeShading family}
    {currentMap : PaperWZ1WeakPlaneMapData current incidence}
    {N : ℕ} {targetScale : Fin (N - 1) → WZ2PaperRequestedScale delta}
    (data : Proposition63ExtremalFinitePlaneMapData
      (sigma := sigma) current currentMap sourceLoss targetScale)
    (hN : 2 ≤ N)
    (hs : 0 < s) (hsOne : s ≤ 1)
    (hsN : s ^ N = delta)
    (htargetLower : ∀ index, s ^ (index.val + 1) ≤
      (targetScale index).1)
    (htargetUpper : ∀ index, (targetScale index).1 ≤
      2 * s ^ (index.val + 1))
    (hcoefficient : 2 / s ≤ coefficient)
    (hcoefficientPos : 0 < coefficient)
    (hcell : ∀ first second,
      wz1PaperGridIndex delta first = wz1PaperGridIndex delta second →
        data.planeMap.planeMap first = data.planeMap.planeMap second)
    (hdiameter : ∀ first ∈ data.shading.union,
      ∀ second ∈ data.shading.union, dist first second ≤ diameter)
    (hsourceOutput : sourceLoss ≤ outputLoss)
    (houtputLoss : 0 < outputLoss)
    (hrestore :
      (27 : ENNReal) * Kakeya.realRpowENN delta outputLoss ≤
        Kakeya.realRpowENN delta sourceLoss) :
    Nonempty (Proposition63ExtremalFiniteLipschitzData
      (sigma := sigma) current currentMap outputLoss coefficient) := by
  apply data.toLipschitz
      (fun index => (targetScale index).1)
      (fun index => (targetScale index).1)
      (fun _ => le_rfl) (fun _ => le_rfl) hcoefficientPos hcell hdiameter
      ?_ hsourceOutput houtputLoss hrestore
  intro d hdeltaD _hdDiameter hcoefficientD
  have dNonnegative : 0 ≤ d := hdeltaD.le.trans' data.extremal.delta_pos.le
  have hdS : d < s := by
    have hscaled : (2 / s) * d ≤ coefficient * d := by
      exact mul_le_mul_of_nonneg_right hcoefficient dNonnegative
    have htwoDiv : (2 / s) * d < 2 := hscaled.trans_lt hcoefficientD
    have hsPositive : 0 < 2 / s := by positivity
    nlinarith [div_mul_cancel₀ 2 hs.ne']
  let admissible : Finset ℕ :=
    Finset.filter (fun k => d ≤ s ^ k) (Finset.range N)
  have oneMemRange : 1 ∈ Finset.range N := by
    simp only [Finset.mem_range]
    omega
  have oneMem : 1 ∈ admissible := by
    apply Finset.mem_filter.mpr
    exact ⟨oneMemRange, by simpa using hdS.le⟩
  have admissibleNonempty : admissible.Nonempty := ⟨1, oneMem⟩
  let k : ℕ := admissible.max' admissibleNonempty
  have kMem : k ∈ admissible := Finset.max'_mem _ _
  have kBounds : k < N ∧ d ≤ s ^ k := by
    simpa only [admissible, Finset.mem_filter, Finset.mem_range] using kMem
  have oneLeK : 1 ≤ k := Finset.le_max' admissible 1 oneMem
  have nextLt : s ^ (k + 1) < d := by
    by_cases nextBeforeEnd : k + 1 < N
    · have nextNotMem : k + 1 ∉ admissible := by
        intro nextMem
        have := Finset.le_max' admissible (k + 1) nextMem
        omega
      have nextInRange : k + 1 ∈ Finset.range N := by
        simpa only [Finset.mem_range] using nextBeforeEnd
      have notDistance : ¬ d ≤ s ^ (k + 1) := by
        intro distanceLe
        exact nextNotMem (Finset.mem_filter.mpr
          ⟨nextInRange, distanceLe⟩)
      exact lt_of_not_ge notDistance
    · have nextEq : k + 1 = N := by omega
      rw [nextEq, hsN]
      exact hdeltaD
  let index : Fin (N - 1) := ⟨k - 1, by omega⟩
  have indexSucc : index.val + 1 = k := by
    dsimp only [index]
    omega
  refine ⟨index, ?_, ?_⟩
  · exact kBounds.2.trans <| by
      simpa only [indexSucc] using htargetLower index
  · apply (htargetUpper index).trans
    rw [indexSucc]
    have hsk : s ^ k < d / s := by
      rw [pow_succ] at nextLt
      have hsNonnegative : 0 ≤ s := hs.le
      exact (lt_div_iff₀ hs).2 (by simpa [mul_comm] using nextLt)
    calc
      2 * s ^ k ≤ 2 * (d / s) :=
        mul_le_mul_of_nonneg_left hsk.le (by norm_num)
      _ = (2 / s) * d := by ring
      _ ≤ coefficient * d := by
        exact mul_le_mul_of_nonneg_right hcoefficient dNonnegative

/-- Pre-runtime schedule for the complete finite Lemma 4.7 plane-map step.
The finite iteration is run at the smaller loss `finiteLoss`; only after all
one-scale estimates are present is the fixed final residue loss absorbed into
`outputLoss`. -/
structure Proposition63ExtremalFiniteLipschitzScheduleData
    (sigma outputLoss : ℝ) (N : ℕ) where
  finiteLoss : ℝ
  rootSourceLoss : ℝ
  rootNormalizationLoss : ℝ
  inputLoss : ℝ
  delta₀ : ℝ
  finiteLoss_pos : 0 < finiteLoss
  finiteLoss_lt_output : finiteLoss < outputLoss
  rootSourceLoss_pos : 0 < rootSourceLoss
  rootNormalizationLoss_pos : 0 < rootNormalizationLoss
  rootSourceLoss_le_half : rootSourceLoss ≤ rootNormalizationLoss / 2
  rootNormalizationLoss_le_finite : rootNormalizationLoss ≤ finiteLoss
  inputLoss_pos : 0 < inputLoss
  inputLoss_le_output : inputLoss ≤ outputLoss
  delta₀_pos : 0 < delta₀
  delta₀_le_one : delta₀ ≤ 1
  run :
    ∀ {delta : ℝ}, 0 < delta → delta ≤ delta₀ →
      ∀ {ambientSourceLoss ambientNormalizationLoss : ℝ}
        {ambientFamily : Kakeya.Streamlined.TubeFamily delta}
        {ambientShading : WZ1PaperTubeShading ambientFamily},
        ∀ (ambientReentry : PureWZ2PropStickyReentryData
          (sigma := sigma) ambientShading 0 ambientSourceLoss
            ambientNormalizationLoss),
          ambientSourceLoss ≤ rootSourceLoss →
          ambientNormalizationLoss ≤ rootNormalizationLoss →
          ∀ (current : WZ1PaperTubeShading ambientFamily),
            WZ2PaperCroppedIsExtremal sigma inputLoss ambientFamily current →
            PaperIsSubshading current ambientShading →
            ∀ {incidence : ℝ},
              ∀ (currentMap : PaperWZ1WeakPlaneMapData current incidence),
                (∀ first second,
                  wz1PaperGridIndex delta first =
                      wz1PaperGridIndex delta second →
                    currentMap.planeMap first = currentMap.planeMap second) →
                0 ≤ incidence → incidence ≤ delta →
                Nonempty (Proposition63ExtremalFiniteLipschitzData
                  (sigma := sigma) current currentMap outputLoss
                    (Real.rpow delta (-outputLoss)))

/-- Construct the complete WZ1-style finite power-scale schedule.  The
hypothesis `2 / N < outputLoss` leaves one exponent gap for the metric factor
two and another for the final fixed residue refinement. -/
theorem proposition63_extremal_finite_lipschitz_schedule
    (sigma : ℝ) (critical : PureWZ2CriticalPackage sigma)
    (outputLoss : ℝ) (houtputLoss : 0 < outputLoss)
    (houtputLossOne : outputLoss ≤ 1)
    (N : ℕ) (hN : 2 ≤ N)
    (hNOutput : (2 : ℝ) / N < outputLoss) :
    Nonempty (Proposition63ExtremalFiniteLipschitzScheduleData
      sigma outputLoss N) := by
  have NPos : 0 < (N : ℝ) := by positivity
  let finiteLoss : ℝ := 1 / (2 * (N : ℝ))
  have finiteLossPos : 0 < finiteLoss := by
    dsimp only [finiteLoss]
    positivity
  have finiteLossOne : finiteLoss ≤ 1 := by
    dsimp only [finiteLoss]
    have NTwo : (2 : ℝ) ≤ N := by exact_mod_cast hN
    apply (div_le_one (by positivity : (0 : ℝ) < 2 * N)).2
    nlinarith
  have finiteLossLtOutput : finiteLoss < outputLoss := by
    dsimp only [finiteLoss]
    have : (1 : ℝ) / (2 * N) < 2 / N := by
      rw [show (1 : ℝ) / (2 * N) = (1 / 2 : ℝ) / N by ring]
      apply (div_lt_div_iff_of_pos_right NPos).2
      norm_num
    exact this.trans hNOutput
  rcases proposition63_extremal_finite_plane_map_schedule sigma critical
      finiteLoss finiteLossPos finiteLossOne (N - 1) with ⟨finite⟩
  have exponentGap : (1 : ℝ) / (2 * N) < 1 / N := by
    rw [show (1 : ℝ) / (2 * N) = (1 / 2 : ℝ) / N by ring]
    apply (div_lt_div_iff_of_pos_right NPos).2
    norm_num
  rcases exists_delta_mul_rpow_le_rpow (2 : ℝ) (by norm_num)
      exponentGap with
    ⟨roundingDelta, roundingDeltaPos, roundingDeltaOne, roundingAbsorb⟩
  have coefficientGap : -(2 / (N : ℝ)) < -(1 / (N : ℝ)) := by
    have : (1 : ℝ) / N < 2 / N := by
      apply (div_lt_div_iff_of_pos_right NPos).2
      norm_num
    linarith
  rcases exists_delta_mul_rpow_le_rpow (2 : ℝ) (by norm_num)
      coefficientGap with
    ⟨coefficientDelta, coefficientDeltaPos, coefficientDeltaOne,
      coefficientAbsorb⟩
  rcases exists_delta_realRpowENN_bound (27 : ENNReal) (by norm_num)
      (sub_pos.mpr finiteLossLtOutput) with
    ⟨residueDelta, residueDeltaPos, residueDeltaOne, residueAbsorb⟩
  let delta₀ := min finite.delta₀ <|
    min roundingDelta <| min coefficientDelta residueDelta
  refine ⟨{
    finiteLoss := finiteLoss
    rootSourceLoss := finite.rootSourceLoss
    rootNormalizationLoss := finite.rootNormalizationLoss
    inputLoss := finite.inputLoss
    delta₀ := delta₀
    finiteLoss_pos := finiteLossPos
    finiteLoss_lt_output := finiteLossLtOutput
    rootSourceLoss_pos := finite.rootSourceLoss_pos
    rootNormalizationLoss_pos := finite.rootNormalizationLoss_pos
    rootSourceLoss_le_half := finite.rootSourceLoss_le_half
    rootNormalizationLoss_le_finite :=
      finite.rootNormalizationLoss_le_output
    inputLoss_pos := finite.inputLoss_pos
    inputLoss_le_output := finite.inputLoss_le_output.trans
      finiteLossLtOutput.le
    delta₀_pos := by
      dsimp only [delta₀]
      exact lt_min finite.delta₀_pos <|
        lt_min roundingDeltaPos <|
          lt_min coefficientDeltaPos residueDeltaPos
    delta₀_le_one := (min_le_left _ _).trans finite.delta₀_le_one
    run := ?_
  }⟩
  intro delta deltaPos deltaLe ambientSourceLoss ambientNormalizationLoss
    ambientFamily ambientShading ambientReentry ambientSourceLe
    ambientNormalizationLe current currentExtremal currentSub incidence
    currentMap currentCellwise incidenceNonnegative incidenceLeDelta
  have deltaLeFinite : delta ≤ finite.delta₀ :=
    deltaLe.trans (min_le_left _ _)
  have deltaLeRounding : delta ≤ roundingDelta :=
    deltaLe.trans <| (min_le_right _ _).trans (min_le_left _ _)
  have deltaLeCoefficient : delta ≤ coefficientDelta :=
    deltaLe.trans <| (min_le_right _ _).trans <|
      (min_le_right _ _).trans (min_le_left _ _)
  have deltaLeResidue : delta ≤ residueDelta :=
    deltaLe.trans <| (min_le_right _ _).trans <|
      (min_le_right _ _).trans (min_le_right _ _)
  have deltaOne : delta ≤ 1 := deltaLeFinite.trans finite.delta₀_le_one
  have deltaStrict : delta < 1 := by
    have smallPower := roundingAbsorb delta deltaPos deltaLeRounding
    by_contra notStrict
    have deltaEq : delta = 1 := le_antisymm deltaOne (not_lt.mp notStrict)
    subst delta
    norm_num [finiteLoss] at smallPower
  let s : ℝ := Real.rpow delta ((N : ℝ)⁻¹)
  have sPos : 0 < s := Real.rpow_pos_of_pos deltaPos _
  have sOne : s ≤ 1 := by
    dsimp only [s]
    exact Real.rpow_le_one deltaPos.le deltaOne (by positivity)
  have sN : s ^ N = delta := by
    dsimp only [s]
    exact Real.rpow_inv_natCast_pow deltaPos.le (by omega)
  let exponent : Fin (N - 1) → ℝ := fun index =>
    ((index.val + 1 : ℕ) : ℝ) / (N : ℝ)
  have exponentPos : ∀ index, 0 < exponent index := by
    intro index
    dsimp only [exponent]
    positivity
  have exponentOne : ∀ index, exponent index ≤ 1 := by
    intro index
    dsimp only [exponent]
    apply (div_le_one NPos).2
    exact_mod_cast (show index.val + 1 ≤ N by omega)
  have powerAtOneOverN : Real.rpow delta (1 / (N : ℝ)) = s := by
    dsimp only [s]
    congr 1
    field_simp
  have roundingBound :
      2 * Real.rpow delta (1 / (N : ℝ)) ≤
        Real.rpow delta finiteLoss := by
    simpa only [finiteLoss] using
      roundingAbsorb delta deltaPos deltaLeRounding
  have powerHalf : ∀ index, Real.rpow delta (exponent index) ≤ 1 / 2 := by
    intro index
    have exponentGe : 1 / (N : ℝ) ≤ exponent index := by
      dsimp only [exponent]
      apply div_le_div_of_nonneg_right _ NPos.le
      exact_mod_cast (show 1 ≤ index.val + 1 by omega)
    have powerLe : Real.rpow delta (exponent index) ≤
        Real.rpow delta (1 / (N : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_ge deltaPos deltaOne exponentGe
    have finitePowerOne : Real.rpow delta finiteLoss ≤ 1 :=
      Real.rpow_le_one deltaPos.le deltaOne finiteLossPos.le
    nlinarith
  let aligned : ∀ index : Fin (N - 1),
      AlignedPowerCoarseScale delta (exponent index) := fun index =>
    Classical.choice <| aligned_power_coarse_scale deltaPos deltaOne
      (exponentPos index) (exponentOne index) (powerHalf index)
  let targetScale : Fin (N - 1) → WZ2PaperRequestedScale delta :=
    fun index => (aligned index).requested
  let K : Fin (N - 1) → ℕ := fun index => (aligned index).multiplicity
  have targetLower : ∀ index,
      Real.rpow delta (1 - finite.stepOutputLoss index) ≤
        (targetScale index).1 := by
    intro index
    have indexUpperNat : index.val + 1 ≤ N - 1 := by omega
    have indexUpperReal : ((index.val + 1 : ℕ) : ℝ) ≤ (N : ℝ) - 1 := by
      calc
        ((index.val + 1 : ℕ) : ℝ) ≤ ((N - 1 : ℕ) : ℝ) := by
          exact_mod_cast indexUpperNat
        _ = (N : ℝ) - 1 := by
          rw [Nat.cast_sub (by omega : 1 ≤ N)]
          norm_num
    have exponentUpper : exponent index ≤
        1 - finite.stepOutputLoss index := by
      have stepLe : finite.stepOutputLoss index ≤ finiteLoss :=
        finite.stepOutputLoss_le_output index
      dsimp only [exponent, finiteLoss] at stepLe ⊢
      have NPos' : 0 < (N : ℝ) := NPos
      have baseUpper :
          ((index.val + 1 : ℕ) : ℝ) / N ≤ 1 - 1 / N := by
        apply (div_le_iff₀ NPos').2
        field_simp [NPos'.ne']
        linarith
      linarith
    exact (Real.rpow_le_rpow_of_exponent_ge deltaPos deltaOne
      exponentUpper).trans <| by
        dsimp only [targetScale]
        rw [(aligned index).requested_eq]
        exact (aligned index).power_le
  have targetUpper : ∀ index, (targetScale index).1 ≤
      Real.rpow delta (finite.stepOutputLoss index) := by
    intro index
    have exponentGe : 1 / (N : ℝ) ≤ exponent index := by
      dsimp only [exponent]
      apply div_le_div_of_nonneg_right _ NPos.le
      exact_mod_cast (show 1 ≤ index.val + 1 by omega)
    have powerLe : Real.rpow delta (exponent index) ≤
        Real.rpow delta (1 / (N : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_ge deltaPos deltaOne exponentGe
    have finiteToStep : Real.rpow delta finiteLoss ≤
        Real.rpow delta (finite.stepOutputLoss index) :=
      Real.rpow_le_rpow_of_exponent_ge deltaPos deltaOne
        (finite.stepOutputLoss_le_output index)
    dsimp only [targetScale]
    rw [(aligned index).requested_eq]
    exact (aligned index).lt_two_power.le.trans <|
      (mul_le_mul_of_nonneg_left powerLe (by norm_num)).trans <|
        roundingBound.trans finiteToStep
  have incidenceTarget : ∀ index, incidence ≤ (targetScale index).1 := by
    intro index
    exact incidenceLeDelta.trans (targetScale index).2.1
  rcases finite.run deltaPos deltaLeFinite ambientReentry ambientSourceLe
      ambientNormalizationLe current currentExtremal currentSub currentMap
      currentCellwise incidenceNonnegative targetScale targetLower targetUpper
      incidenceTarget K (fun index => (aligned index).multiplicity_pos)
      (fun index => by
        change (aligned index).requested.1 =
          ((aligned index).multiplicity : ℝ) * delta
        rw [(aligned index).requested_eq, (aligned index).rho_eq]) with
    ⟨iterated⟩
  have targetIdealLower : ∀ index, s ^ (index.val + 1) ≤
      (targetScale index).1 := by
    intro index
    have idealEq : s ^ (index.val + 1) =
        Real.rpow delta (exponent index) := by
      calc
        s ^ (index.val + 1) =
            Real.rpow s ((index.val + 1 : ℕ) : ℝ) :=
          (Real.rpow_natCast s (index.val + 1)).symm
        _ = Real.rpow delta
            (((N : ℝ)⁻¹) * ((index.val + 1 : ℕ) : ℝ)) := by
          dsimp only [s]
          exact (Real.rpow_mul deltaPos.le _ _).symm
        _ = Real.rpow delta (exponent index) := by
          congr 1
          dsimp only [exponent]
          field_simp
    rw [idealEq]
    dsimp only [targetScale]
    rw [(aligned index).requested_eq]
    exact (aligned index).power_le
  have targetIdealUpper : ∀ index, (targetScale index).1 ≤
      2 * s ^ (index.val + 1) := by
    intro index
    have idealEq : s ^ (index.val + 1) =
        Real.rpow delta (exponent index) := by
      calc
        s ^ (index.val + 1) =
            Real.rpow s ((index.val + 1 : ℕ) : ℝ) :=
          (Real.rpow_natCast s (index.val + 1)).symm
        _ = Real.rpow delta
            (((N : ℝ)⁻¹) * ((index.val + 1 : ℕ) : ℝ)) := by
          dsimp only [s]
          exact (Real.rpow_mul deltaPos.le _ _).symm
        _ = Real.rpow delta (exponent index) := by
          congr 1
          dsimp only [exponent]
          field_simp
    rw [idealEq]
    dsimp only [targetScale]
    rw [(aligned index).requested_eq]
    exact (aligned index).lt_two_power.le
  have coefficientBound : 2 / s ≤ Real.rpow delta (-outputLoss) := by
    have first := coefficientAbsorb delta deltaPos deltaLeCoefficient
    have inverseEq : Real.rpow delta (-(1 / (N : ℝ))) = s⁻¹ := by
      dsimp only [s]
      rw [show -(1 / (N : ℝ)) = -((N : ℝ)⁻¹) by field_simp]
      exact Real.rpow_neg deltaPos.le ((N : ℝ)⁻¹)
    have second : Real.rpow delta (-(2 / (N : ℝ))) ≤
        Real.rpow delta (-outputLoss) :=
      Real.rpow_le_rpow_of_exponent_ge deltaPos deltaOne (by linarith)
    calc
      2 / s = 2 * Real.rpow delta (-(1 / (N : ℝ))) := by
        rw [inverseEq]
        exact div_eq_mul_inv 2 s
      _ ≤ Real.rpow delta (-(2 / (N : ℝ))) := first
      _ ≤ Real.rpow delta (-outputLoss) := second
  have coefficientPos : 0 < Real.rpow delta (-outputLoss) :=
    Real.rpow_pos_of_pos deltaPos _
  have iteratedCellwise : ∀ first second,
      wz1PaperGridIndex delta first = wz1PaperGridIndex delta second →
        iterated.planeMap.planeMap first =
          iterated.planeMap.planeMap second := by
    intro first second sameCell
    rw [iterated.same_plane_map]
    exact currentCellwise first second sameCell
  have restore : (27 : ENNReal) * Kakeya.realRpowENN delta outputLoss ≤
      Kakeya.realRpowENN delta finiteLoss := by
    have bound := residueAbsorb delta deltaPos deltaLeResidue
    calc
      (27 : ENNReal) * Kakeya.realRpowENN delta outputLoss ≤
          Kakeya.realRpowENN delta (-(outputLoss - finiteLoss)) *
            Kakeya.realRpowENN delta outputLoss := by gcongr
      _ = Kakeya.realRpowENN delta finiteLoss := by
        rw [← realRpowENN_add deltaPos]
        congr 1
        ring
  exact iterated.toPowerScaleLipschitz hN sPos sOne sN
    targetIdealLower targetIdealUpper coefficientBound coefficientPos
    iteratedCellwise
    (fun first firstMem second secondMem =>
      paper_shading_union_dist_le_four iterated.shading firstMem secondMem)
    finiteLossLtOutput.le houtputLoss restore

end Kakeya.Assouad.PureWZ2

end
