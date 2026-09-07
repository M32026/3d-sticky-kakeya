import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Proposition64SelectedImage

/-!
# The common horizontal window in Proposition 6.4

The fixed translation in `wz2_64.tex` is chosen once for a mass-heavy
subfamily.  It is not allowed to depend on the tube.  At the center of the
selected short slab, every exact image axis meets a fixed square.  We cover
that square by forty-nine squares of half-width `1 / 3`, pigeonhole using the
actual indexed shaded masses, and translate the winning square to the origin.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

/-- Centers of the seven intervals of radius `1 / 3` covering
`[-7/3,7/3]`. -/
def pureWZ2Proposition64WindowCenter (index : Fin 7) : ℝ :=
  -2 + (index : ℝ) * (2 / 3)

/-- A deterministic member of the seven-window cover. -/
def pureWZ2Proposition64WindowIndex (value : ℝ) : Fin 7 :=
  if value ≤ -5 / 3 then 0
  else if value ≤ -1 then 1
  else if value ≤ -1 / 3 then 2
  else if value ≤ 1 / 3 then 3
  else if value ≤ 1 then 4
  else if value ≤ 5 / 3 then 5
  else 6

theorem pureWZ2Proposition64WindowIndex_spec
    {value : ℝ} (hvalue : |value| ≤ 7 / 3) :
    |value - pureWZ2Proposition64WindowCenter
      (pureWZ2Proposition64WindowIndex value)| ≤ 1 / 3 := by
  rw [abs_le] at hvalue ⊢
  unfold pureWZ2Proposition64WindowIndex
  split_ifs with h₀ h₁ h₂ h₃ h₄ h₅
  · norm_num [pureWZ2Proposition64WindowCenter]
    constructor <;> linarith
  · norm_num [pureWZ2Proposition64WindowCenter]
    constructor <;> linarith
  · norm_num [pureWZ2Proposition64WindowCenter]
    constructor <;> linarith
  · norm_num [pureWZ2Proposition64WindowCenter]
    constructor <;> linarith
  · norm_num [pureWZ2Proposition64WindowCenter]
    constructor <;> linarith
  · norm_num [pureWZ2Proposition64WindowCenter]
    constructor <;> linarith
  · norm_num [pureWZ2Proposition64WindowCenter]
    constructor <;> linarith

/-- Every source paper axis in the selected slab has bounded horizontal
coordinates at the slab center. -/
theorem pureWZ2Proposition64SourceAxisPoint_horizontal_bound
    {sourceDelta : ℝ} (sourceTube : Kakeya.DeltaTube sourceDelta)
    (hsourceLine : WZ1PaperTubeInLineClass sourceTube)
    {slabCenter : ℝ} (hslabCenter : |slabCenter| ≤ 1)
    (coordinate : Fin 3)
    (hcoordinate : coordinate = 0 ∨ coordinate = 1) :
    |wz1PaperAxisPointAtHeight sourceTube slabCenter coordinate| ≤ 7 / 3 := by
  let direction := wz1PaperDirection sourceTube
  have hdirection (i : Fin 3) : |direction i| ≤ 1 := by
    have hcoord := PiLp.norm_apply_le direction i
    simpa [direction, Real.norm_eq_abs, wz1PaperDirection_norm] using hcoord
  have hvertical : 0 < direction 2 := by
    dsimp only [direction]
    linarith [hsourceLine.1]
  have hratio : |slabCenter / direction 2| ≤ 2 := by
    rw [abs_div, abs_of_pos hvertical]
    apply (div_le_iff₀ hvertical).2
    nlinarith [hsourceLine.1]
  have hzero :
      |wz1TubeAxisZeroPoint sourceTube coordinate| ≤ 1 / 3 := by
    rcases hcoordinate with rfl | rfl
    · exact hsourceLine.2.1
    · exact hsourceLine.2.2
  rw [show wz1PaperAxisPointAtHeight sourceTube slabCenter coordinate =
      wz1TubeAxisZeroPoint sourceTube coordinate +
        (slabCenter / direction 2) * direction coordinate by
    simp [wz1PaperAxisPointAtHeight, direction]]
  calc
    |wz1TubeAxisZeroPoint sourceTube coordinate +
        slabCenter / direction 2 * direction coordinate| ≤
      |wz1TubeAxisZeroPoint sourceTube coordinate| +
        |slabCenter / direction 2| * |direction coordinate| := by
          simpa [abs_mul] using abs_add_le
            (wz1TubeAxisZeroPoint sourceTube coordinate)
            ((slabCenter / direction 2) * direction coordinate)
    _ ≤ 1 / 3 + 2 * 1 := by
      gcongr
      exact hdirection coordinate
    _ = 7 / 3 := by norm_num

/-- The exact unshifted image zero-point lies in the fixed horizontal square
`[-7/3,7/3]^2`.  The lower bound `9 ≤ normalization` is the fixed absolute
normalization from Proposition 6.4. -/
theorem pureWZ2Proposition64ImageAxisZero_horizontal_bound
    {sourceDelta : ℝ} (g : ℝ → ℝ)
    (slabCenter anchorHeight halfHeight normalization : ℝ)
    (sourceTube : Kakeya.DeltaTube sourceDelta)
    (hsourceLine : WZ1PaperTubeInLineClass sourceTube)
    (hslabCenter : |slabCenter| ≤ 1)
    (hnormalization : 9 ≤ normalization)
    (hanchorSlope : |g anchorHeight| ≤ 8)
    (coordinate : Fin 3)
    (hcoordinate : coordinate = 0 ∨ coordinate = 1) :
    |pureWZ2Proposition64Map g slabCenter anchorHeight halfHeight
        normalization
        (wz1PaperAxisPointAtHeight sourceTube slabCenter) coordinate| ≤
      7 / 3 := by
  have hnormalizationPos : 0 < normalization := by linarith
  have hsource (i : Fin 3) (hi : i = 0 ∨ i = 1) :
      |wz1PaperAxisPointAtHeight sourceTube slabCenter i| ≤ 7 / 3 :=
    pureWZ2Proposition64SourceAxisPoint_horizontal_bound sourceTube
      hsourceLine hslabCenter i hi
  rcases hcoordinate with rfl | rfl
  · rw [pureWZ2Proposition64Map_apply_zero, abs_div,
      abs_of_pos hnormalizationPos]
    have hnumerator :
        |wz1PaperAxisPointAtHeight sourceTube slabCenter 0 +
            g anchorHeight *
              wz1PaperAxisPointAtHeight sourceTube slabCenter 1| ≤ 21 := by
      calc
        _ ≤ |wz1PaperAxisPointAtHeight sourceTube slabCenter 0| +
              |g anchorHeight| *
                |wz1PaperAxisPointAtHeight sourceTube slabCenter 1| := by
            simpa [abs_mul] using abs_add_le
              (wz1PaperAxisPointAtHeight sourceTube slabCenter 0)
              (g anchorHeight *
                wz1PaperAxisPointAtHeight sourceTube slabCenter 1)
        _ ≤ 7 / 3 + 8 * (7 / 3) := by
          gcongr
          · exact hsource 0 (Or.inl rfl)
          · exact hsource 1 (Or.inr rfl)
        _ = 21 := by norm_num
    apply (div_le_iff₀ hnormalizationPos).2
    nlinarith
  · simpa [pureWZ2Proposition64Map_apply_one] using
      hsource 1 (Or.inr rfl)

/-- Weighted pigeonhole over an arbitrary nonempty finite target type. -/
private theorem pureWZ2Proposition64_weighted_pigeonhole
    {α β : Type*} [DecidableEq α] [Fintype β] [DecidableEq β]
    [Nonempty β] (indices : Finset α) (weight : α → ENNReal)
    (color : α → β) :
    ∃ target : β,
      (∑ index ∈ indices, weight index) ≤
        (Fintype.card β : ENNReal) *
          ∑ index ∈ indices.filter (fun index => color index = target),
            weight index := by
  let fiberWeight : β → ENNReal := fun target =>
    ∑ index ∈ indices.filter (fun index => color index = target),
      weight index
  have htargets : (Finset.univ : Finset β).Nonempty :=
    Finset.univ_nonempty
  rcases Finset.exists_max_image Finset.univ fiberWeight htargets with
    ⟨target, _htarget, hmax⟩
  have htotal :
      (∑ other : β, fiberWeight other) =
        ∑ index ∈ indices, weight index := by
    simpa [fiberWeight] using
      Finset.sum_fiberwise indices color weight
  refine ⟨target, ?_⟩
  rw [← htotal]
  calc
    (∑ other : β, fiberWeight other) ≤
        ∑ _other : β, fiberWeight target := by
      exact Finset.sum_le_sum fun other _ =>
        hmax other (Finset.mem_univ other)
    _ = (Fintype.card β : ENNReal) * fiberWeight target := by
      simp [Finset.sum_const]
    _ = (Fintype.card β : ENNReal) *
          ∑ index ∈ indices.filter (fun index => color index = target),
            weight index := rfl

/-- The exact unshifted zero-point used to color source tubes. -/
def pureWZ2Proposition64SourceAxisImageZero
    {sourceDelta : ℝ} (g : ℝ → ℝ)
    (slabCenter anchorHeight halfHeight normalization : ℝ)
    (sourceTube : Kakeya.DeltaTube sourceDelta) : Point3 :=
  pureWZ2Proposition64Map g slabCenter anchorHeight halfHeight normalization
    (wz1PaperAxisPointAtHeight sourceTube slabCenter)

/-- The two-dimensional window label of one source tube. -/
def pureWZ2Proposition64TubeWindow
    {sourceDelta : ℝ} (g : ℝ → ℝ)
    (slabCenter anchorHeight halfHeight normalization : ℝ)
    (sourceTube : Kakeya.DeltaTube sourceDelta) : Fin 7 × Fin 7 :=
  let zeroPoint := pureWZ2Proposition64SourceAxisImageZero g slabCenter
    anchorHeight halfHeight normalization sourceTube
  (pureWZ2Proposition64WindowIndex (zeroPoint 0),
    pureWZ2Proposition64WindowIndex (zeroPoint 1))

/-- Data produced by the common-window mass pigeonhole. -/
structure PureWZ2Proposition64CommonWindowData
    {sourceDelta : ℝ}
    (g : ℝ → ℝ) (slabCenter anchorHeight halfHeight normalization : ℝ)
    (sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta)
    (sourceShading : WZ1PaperTubeShading sourceFamily) where
  window : Fin 7 × Fin 7
  selected : Finset (Fin sourceFamily.card)
  selected_eq : selected = Finset.univ.filter fun index =>
    pureWZ2Proposition64TubeWindow g slabCenter anchorHeight halfHeight
      normalization (sourceFamily.tube index) = window
  translation : Point3
  translation_eq : translation =
    point3 (-pureWZ2Proposition64WindowCenter window.1)
      (-pureWZ2Proposition64WindowCenter window.2) 0
  translation_height : translation 2 = 0
  retained_mass : sourceShading.mass ≤
    49 * ∑ index ∈ selected, volume (sourceShading.carrier index)
  axis_window_zero : ∀ index ∈ selected,
    |pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight halfHeight
        normalization translation
        (wz1PaperAxisPointAtHeight (sourceFamily.tube index) slabCenter)
        0| ≤ 1 / 3
  axis_window_one : ∀ index ∈ selected,
    |pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight halfHeight
        normalization translation
        (wz1PaperAxisPointAtHeight (sourceFamily.tube index) slabCenter)
        1| ≤ 1 / 3

/-- Every selected short-slab carrier is sent to the standard ambient box.
The three contributions are the common-window axis center, the short-slab
axis drift, and the same-height tube thickness. -/
theorem PureWZ2Proposition64CommonWindowData.image_mem_axisBox
    {sourceDelta : ℝ} {g : ℝ → ℝ}
    {slabCenter anchorHeight halfHeight normalization : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    (common : PureWZ2Proposition64CommonWindowData g slabCenter anchorHeight
      halfHeight normalization sourceFamily sourceShading)
    (hsourceDelta : 0 < sourceDelta)
    (hsourceDeltaSmall : 180 * sourceDelta ≤ 1 / 2)
    (hhalfHeight : 0 < halfHeight)
    (hhalfHeightSmall : 2 * halfHeight ≤ 1 / 6)
    (hnormalization : 9 ≤ normalization)
    (hanchorSlope : |g anchorHeight| ≤ 8)
    (hsourceLine : WZ1PaperIsLineClass sourceFamily)
    (hslab : ∀ index, sourceShading.carrier index ⊆
      horizontalSlab (slabCenter - halfHeight)
        (slabCenter + halfHeight)) :
    ∀ index : Fin
        (Kakeya.Streamlined.TubeSubfamily.fromFinset
          sourceFamily common.selected).family.card,
      ∀ point ∈
        (restrictPaperShading
          (Kakeya.Streamlined.TubeSubfamily.fromFinset
            sourceFamily common.selected) sourceShading).carrier index,
        pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight
            halfHeight normalization common.translation point ∈
          Kakeya.Streamlined.axisBox 2 2 2 := by
  let selectedSource :=
    Kakeya.Streamlined.TubeSubfamily.fromFinset sourceFamily common.selected
  intro index point hpoint
  have hselected : selectedSource.embedding index ∈ common.selected :=
    Finset.orderEmbOfFin_mem common.selected rfl index
  have hsourcePoint : point ∈ sourceShading.carrier
      (selectedSource.embedding index) := hpoint
  have hsourceBody : point ∈ wz1PaperTubeCarrier
      (sourceFamily.tube (selectedSource.embedding index)) :=
    sourceShading.subset_body (selectedSource.embedding index) hsourcePoint
  have hheightSlab : point 2 ∈
      Set.Icc (slabCenter - halfHeight) (slabCenter + halfHeight) := by
    exact hslab (selectedSource.embedding index) hsourcePoint
  let axisPoint := wz1PaperAxisPointAtHeight
    (sourceFamily.tube (selectedSource.embedding index)) (point 2)
  let imagePoint := pureWZ2Proposition64TranslatedMap g slabCenter
    anchorHeight halfHeight normalization common.translation point
  let imageAxis := pureWZ2Proposition64TranslatedMap g slabCenter
    anchorHeight halfHeight normalization common.translation axisPoint
  let imageCenter := pureWZ2Proposition64TranslatedMap g slabCenter
    anchorHeight halfHeight normalization common.translation
      (wz1PaperAxisPointAtHeight
        (sourceFamily.tube (selectedSource.embedding index)) slabCenter)
  have hpointAxis : dist imagePoint imageAxis ≤ 180 * sourceDelta := by
    exact pureWZ2Proposition64TranslatedMap_sameHeightAxis_dist_le
      hsourceDelta g slabCenter anchorHeight halfHeight normalization
      common.translation (by linarith) hanchorSlope
      (sourceFamily.tube (selectedSource.embedding index))
      (hsourceLine (selectedSource.embedding index)) hsourceBody
  have haxisCenter (coordinate : Fin 3)
      (hcoordinate : coordinate = 0 ∨ coordinate = 1) :
      |imageAxis coordinate - imageCenter coordinate| ≤ 2 * halfHeight := by
    exact pureWZ2Proposition64ImageAxis_horizontal_shift_le g slabCenter
      anchorHeight halfHeight normalization common.translation hhalfHeight
      hnormalization hanchorSlope
      (sourceFamily.tube (selectedSource.embedding index))
      (hsourceLine (selectedSource.embedding index)) hheightSlab
      coordinate hcoordinate
  have hpointAxisCoord (coordinate : Fin 3) :
      |imagePoint coordinate - imageAxis coordinate| ≤ 180 * sourceDelta := by
    have hcoord := PiLp.norm_apply_le (imagePoint - imageAxis) coordinate
    have hcoord' : |imagePoint coordinate - imageAxis coordinate| ≤
        ‖imagePoint - imageAxis‖ := by
      simpa [Real.norm_eq_abs] using hcoord
    exact hcoord'.trans (by simpa [dist_eq_norm] using hpointAxis)
  have hhorizontal (coordinate : Fin 3)
      (hcoordinate : coordinate = 0 ∨ coordinate = 1)
      (hcenter : |imageCenter coordinate| ≤ 1 / 3) :
      |imagePoint coordinate| ≤ 1 := by
    have hsplit : imagePoint coordinate =
        (imagePoint coordinate - imageAxis coordinate) +
          (imageAxis coordinate - imageCenter coordinate) +
            imageCenter coordinate := by ring
    rw [hsplit]
    calc
      |(imagePoint coordinate - imageAxis coordinate) +
          (imageAxis coordinate - imageCenter coordinate) +
            imageCenter coordinate| ≤
        |imagePoint coordinate - imageAxis coordinate| +
          |imageAxis coordinate - imageCenter coordinate| +
            |imageCenter coordinate| := (abs_add_le _ _).trans <|
              add_le_add (abs_add_le _ _) le_rfl
      _ ≤ 180 * sourceDelta + 2 * halfHeight + 1 / 3 := by
        exact add_le_add
          (add_le_add (hpointAxisCoord coordinate)
            (haxisCenter coordinate hcoordinate)) hcenter
      _ ≤ 1 := by linarith
  have hzero : |imagePoint 0| ≤ 1 :=
    hhorizontal 0 (Or.inl rfl) (common.axis_window_zero
      (selectedSource.embedding index) hselected)
  have hone : |imagePoint 1| ≤ 1 :=
    hhorizontal 1 (Or.inr rfl) (common.axis_window_one
      (selectedSource.embedding index) hselected)
  have htwo : |imagePoint 2| ≤ 1 := by
    rw [pureWZ2Proposition64TranslatedMap_apply_two,
      common.translation_height, add_zero, abs_le]
    constructor
    · apply (le_div_iff₀ hhalfHeight).2
      linarith [hheightSlab.1]
    · apply (div_le_iff₀ hhalfHeight).2
      linarith [hheightSlab.2]
  exact ⟨by simpa [imagePoint] using hzero,
    by simpa [imagePoint] using hone, by simpa [imagePoint] using htwo⟩

/-- Select one of the forty-nine common horizontal windows by the actual
indexed shaded mass. -/
theorem pureWZ2Proposition64_selectCommonWindow
    {sourceDelta : ℝ}
    (g : ℝ → ℝ) (slabCenter anchorHeight halfHeight normalization : ℝ)
    (sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta)
    (sourceShading : WZ1PaperTubeShading sourceFamily)
    (hline : WZ1PaperIsLineClass sourceFamily)
    (hslabCenter : |slabCenter| ≤ 1)
    (hnormalization : 9 ≤ normalization)
    (hanchorSlope : |g anchorHeight| ≤ 8) :
    Nonempty
      (PureWZ2Proposition64CommonWindowData g slabCenter anchorHeight
        halfHeight normalization sourceFamily sourceShading) := by
  let color : Fin sourceFamily.card → Fin 7 × Fin 7 := fun index =>
    pureWZ2Proposition64TubeWindow g slabCenter anchorHeight halfHeight
      normalization (sourceFamily.tube index)
  let weight : Fin sourceFamily.card → ENNReal := fun index =>
    volume (sourceShading.carrier index)
  rcases pureWZ2Proposition64_weighted_pigeonhole
      (Finset.univ : Finset (Fin sourceFamily.card)) weight color with
    ⟨window, hmass⟩
  let selected : Finset (Fin sourceFamily.card) :=
    Finset.univ.filter fun index => color index = window
  let translation : Point3 :=
    point3 (-pureWZ2Proposition64WindowCenter window.1)
      (-pureWZ2Proposition64WindowCenter window.2) 0
  refine ⟨{
    window := window
    selected := selected
    selected_eq := rfl
    translation := translation
    translation_eq := rfl
    translation_height := by simp [translation, point3]
    retained_mass := ?_
    axis_window_zero := ?_
    axis_window_one := ?_ }⟩
  · change (∑ index : Fin sourceFamily.card,
        volume (sourceShading.carrier index)) ≤ _
    simpa [weight, selected, color] using hmass
  · intro index hindex
    have hcolor : color index = window :=
      (Finset.mem_filter.mp hindex).2
    let zeroPoint := pureWZ2Proposition64SourceAxisImageZero g slabCenter
      anchorHeight halfHeight normalization (sourceFamily.tube index)
    have hbound : |zeroPoint 0| ≤ 7 / 3 := by
      exact pureWZ2Proposition64ImageAxisZero_horizontal_bound g slabCenter
        anchorHeight halfHeight normalization (sourceFamily.tube index)
        (hline index) hslabCenter hnormalization hanchorSlope 0 (Or.inl rfl)
    have hwindow :
        |zeroPoint 0 - pureWZ2Proposition64WindowCenter
          (pureWZ2Proposition64WindowIndex (zeroPoint 0))| ≤ 1 / 3 :=
      pureWZ2Proposition64WindowIndex_spec hbound
    have hfirst :
        pureWZ2Proposition64WindowIndex (zeroPoint 0) = window.1 := by
      exact congrArg Prod.fst hcolor
    change |zeroPoint 0 + translation 0| ≤ 1 / 3
    rw [show translation 0 =
      -pureWZ2Proposition64WindowCenter window.1 by simp [translation, point3],
      ← sub_eq_add_neg, ← hfirst]
    exact hwindow
  · intro index hindex
    have hcolor : color index = window :=
      (Finset.mem_filter.mp hindex).2
    let zeroPoint := pureWZ2Proposition64SourceAxisImageZero g slabCenter
      anchorHeight halfHeight normalization (sourceFamily.tube index)
    have hbound : |zeroPoint 1| ≤ 7 / 3 := by
      exact pureWZ2Proposition64ImageAxisZero_horizontal_bound g slabCenter
        anchorHeight halfHeight normalization (sourceFamily.tube index)
        (hline index) hslabCenter hnormalization hanchorSlope 1 (Or.inr rfl)
    have hwindow :
        |zeroPoint 1 - pureWZ2Proposition64WindowCenter
          (pureWZ2Proposition64WindowIndex (zeroPoint 1))| ≤ 1 / 3 :=
      pureWZ2Proposition64WindowIndex_spec hbound
    have hsecond :
        pureWZ2Proposition64WindowIndex (zeroPoint 1) = window.2 := by
      exact congrArg Prod.snd hcolor
    change |zeroPoint 1 + translation 1| ≤ 1 / 3
    rw [show translation 1 =
      -pureWZ2Proposition64WindowCenter window.2 by simp [translation, point3],
      ← sub_eq_add_neg, ← hsecond]
    exact hwindow

/-- The common-window selection followed by the exact one-to-one image and
whole-cell rediscretization. -/
structure PureWZ2Proposition64CommonWindowImageData
    {sourceDelta targetDelta : ℝ}
    (g : SlopeFunction)
    (slabCenter anchorHeight halfHeight normalization : ℝ)
    (sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta)
    (sourceShading : WZ1PaperTubeShading sourceFamily)
    (common : PureWZ2Proposition64CommonWindowData g slabCenter anchorHeight
      halfHeight normalization sourceFamily sourceShading)
    (hhalfHeight : 0 < halfHeight)
    (hnormalization : 0 < normalization) where
  image : PureWZ2Proposition64ActualImageRediscretizationData
    (targetDelta := targetDelta) g slabCenter anchorHeight halfHeight
      normalization common.translation hhalfHeight hnormalization
      sourceFamily sourceShading
  line_class : WZ1PaperIsLineClass image.family

/-- Every member of the selected exact-image family lies in the fixed line
class after the single common translation chosen by the window pigeonhole. -/
noncomputable def PureWZ2Proposition64CommonWindowData.toImage
    {sourceDelta targetDelta : ℝ}
    {g : SlopeFunction}
    {slabCenter anchorHeight halfHeight normalization : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    (common : PureWZ2Proposition64CommonWindowData g slabCenter anchorHeight
      halfHeight normalization sourceFamily sourceShading)
    (hsourceLine : WZ1PaperIsLineClass sourceFamily)
    (hhalfHeight : 0 < halfHeight)
    (hhalfHeightSmall : halfHeight ≤ 1 / 20)
    (hnormalization : 1 ≤ normalization)
    (hanchorSlope : |g anchorHeight| ≤ 8)
    (htargetDelta : 0 < targetDelta)
    (hnormalized :
      (pureWZ2Proposition64Slope g slabCenter anchorHeight halfHeight
        normalization).IsNormalized) :
    PureWZ2Proposition64CommonWindowImageData (targetDelta := targetDelta)
      g slabCenter anchorHeight
      halfHeight normalization sourceFamily sourceShading common
      hhalfHeight (lt_of_lt_of_le zero_lt_one hnormalization) := by
  let image :=
    pureWZ2Proposition64SelectedActualImageRediscretization g slabCenter
      anchorHeight halfHeight normalization common.translation hhalfHeight
      (lt_of_lt_of_le zero_lt_one hnormalization) common.translation_height
      htargetDelta hnormalized sourceFamily sourceShading common.selected
  refine { image := image, line_class := ?_ }
  let selectedSource :=
    Kakeya.Streamlined.TubeSubfamily.fromFinset sourceFamily common.selected
  have hselectedLine : WZ1PaperIsLineClass selectedSource.family :=
    hsourceLine.subfamily selectedSource
  intro target
  let sourceIndex : Fin selectedSource.family.card := target
  have hselected : selectedSource.embedding sourceIndex ∈ common.selected := by
    exact Finset.orderEmbOfFin_mem common.selected rfl sourceIndex
  have hzero := common.axis_window_zero
    (selectedSource.embedding sourceIndex) hselected
  have hone := common.axis_window_one
    (selectedSource.embedding sourceIndex) hselected
  change WZ1PaperTubeInLineClass
    (pureWZ2Proposition64ImageTube targetDelta g slabCenter anchorHeight
      halfHeight normalization common.translation hhalfHeight
      (lt_of_lt_of_le zero_lt_one hnormalization)
      (selectedSource.family.tube sourceIndex))
  apply pureWZ2Proposition64ImageTube_lineClass_of_axis_window targetDelta g
    slabCenter anchorHeight common.translation common.translation_height
    hhalfHeight (lt_of_lt_of_le zero_lt_one hnormalization)
    (selectedSource.family.tube sourceIndex) (hselectedLine sourceIndex)
  · exact pureWZ2Proposition64ImageTube_vertical g slabCenter anchorHeight
      common.translation hhalfHeight hhalfHeightSmall hnormalization
      hanchorSlope (selectedSource.family.tube sourceIndex)
      (hselectedLine sourceIndex).vertical
  · rw [selectedSource.tube_eq sourceIndex]
    exact hzero
  · rw [selectedSource.tube_eq sourceIndex]
    exact hone

/-- The prepared Proposition 6.4 data supplies the hypotheses of the common
window selection when the fixed normalization is at least nine. -/
theorem PureWZ2Proposition64PreparedData.selectCommonWindow
    {sigma inputLoss sourceDelta finalLoss hierarchyLoss rawLoss
      extensionConstant : ℝ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss sourceDelta}
    {hierarchy : PureWZ2LocallyLinearHierarchyData
      source finalLoss hierarchyLoss}
    {raw : PureWZ2RawC2GlobalGrainData hierarchy.shading sigma
      (Kakeya.realRpowENN sourceDelta (-finalLoss)) rawLoss
        extensionConstant}
    (prepared : PureWZ2Proposition64PreparedData hierarchy raw)
    (hnormalization : 9 ≤ prepared.normalization) :
    Nonempty
      (PureWZ2Proposition64CommonWindowData prepared.restrictedRaw.slope
        prepared.slab.center prepared.slab.anchorHeight
        prepared.slab.halfHeight prepared.normalization
        source.family prepared.slab.shading) := by
  have hcenterMem := prepared.slab.source_window 0 (by norm_num)
  have hcenter : |prepared.slab.center| ≤ 1 := by
    apply abs_le.mpr
    simpa using hcenterMem
  apply pureWZ2Proposition64_selectCommonWindow
    prepared.restrictedRaw.slope prepared.slab.center
    prepared.slab.anchorHeight prepared.slab.halfHeight
    prepared.normalization source.family prepared.slab.shading
    source.line_class hcenter hnormalization
  exact prepared.normalized.anchor_value_bound

end Kakeya.Assouad

end
