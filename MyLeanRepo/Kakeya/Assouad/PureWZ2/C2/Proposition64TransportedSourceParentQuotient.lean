import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Proposition64TransportedSourceParents
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Proposition64OwnerPairCardinality
import MyLeanRepo.Kakeya.Assouad.PureWZ2.FiniteMaximalQuotientNet
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.PureFiniteStrongParentSelection
import MyLeanRepo.Kakeya.Assouad.PureWZ2.GWZConversion.FiniteColoredDegreeSelection
import MyLeanRepo.Kakeya.Assouad.PureWZ2.GWZConversion.WeightedGraphSelection
import MyLeanRepo.Kakeya.Assouad.WZ1.PaperPackingRefinement

/-!
# Fixed-ratio quotient of Proposition 6.4 transported source parents

The transported source parents can cluster.  At each scheduled coordinate we
therefore take one maximal line-metric net at their own radius and relabel the
net centres at four times that radius.  The resulting conflict degree is an
absolute five-dimensional packing constant.  No `rho⁻²` cardinality estimate
for the final fine family is used.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

private theorem transportedFiniteColored_selected_nonempty
    {indexType : Type*}
    [Fintype indexType] [DecidableEq indexType] [LinearOrder indexType]
    {coordinateCount : ℕ}
    {Color Vertex : Fin coordinateCount → Type}
    [∀ coordinate, Fintype (Color coordinate)]
    [∀ coordinate, DecidableEq (Color coordinate)]
    [∀ coordinate, Nonempty (Color coordinate)]
    [∀ coordinate, Fintype (Vertex coordinate)]
    [∀ coordinate, DecidableEq (Vertex coordinate)]
    {color : ∀ coordinate, indexType → Color coordinate}
    {parent : ∀ coordinate, indexType → Vertex coordinate}
    {weight : indexType → ENNReal}
    (data : WZ2FiniteColoredDegreeSelectionData
      coordinateCount Color Vertex color parent weight)
    (htotal : 0 < ∑ index, weight index) :
    data.regularized.selected.Nonempty := by
  by_contra hempty
  have hselectedEmpty : data.regularized.selected = ∅ :=
    Finset.not_nonempty_iff_eq_empty.mp hempty
  have hselectedSum :
      (∑ index ∈ data.regularized.selected, weight index) = 0 := by
    rw [hselectedEmpty]
    simp
  have hcolorSum : (∑ index ∈ data.colorClass, weight index) ≤ 0 := by
    have hdegree := data.regularized.retained_weight
    have hleft :
        (∑ index, if index ∈ data.colorClass then weight index else 0) =
          ∑ index ∈ data.colorClass, weight index := by
      rw [Finset.sum_ite]
      simp
    have hright :
        (∑ index ∈ data.regularized.selected,
          if index ∈ data.colorClass then weight index else 0) =
          ∑ index ∈ data.regularized.selected, weight index := by
      apply Finset.sum_congr rfl
      intro index hindex
      rw [if_pos (data.selected_subset_colorClass hindex)]
    rw [hleft, hright, hselectedSum, mul_zero] at hdegree
    exact hdegree
  have htotalZero : (∑ index, weight index) ≤ 0 :=
    data.color_retained.trans <| by
      simpa using mul_le_mul_left' hcolorSum
        (Fintype.card (∀ coordinate, Color coordinate) : ENNReal)
  exact (not_le_of_gt htotal) htotalZero

namespace PureWZ2NormalizedHierarchyOutput.PureWZ2Proposition64Lemma35GeometricData

variable
    {sigma workLoss sourceDelta targetDelta₀ outputLoss : ℝ}
    {Grid : Type*} [PureWZ2Proposition64TargetGrid Grid]
    {hsourceSmall : sourceDelta ≤
      pureWZ2Proposition64Lemma35SourceCeiling targetDelta₀}
    (quantitativeOutput : PureWZ2QuantitativeNormalizedHierarchyOutput
      sigma workLoss sourceDelta)
    (geometry : PureWZ2Proposition64Lemma35GeometricData
      quantitativeOutput.normalized hsourceSmall)
    (frostman : SelectedSourceFrostmanReceipt geometry)
    (floor : Grid)

private noncomputable abbrev initialED :=
  quantitativeVerticalPaperED quantitativeOutput geometry frostman

private noncomputable abbrev schedule :=
  quantitativeVerticalRequestedScaleScheduleFor quantitativeOutput geometry floor

private noncomputable abbrev rawParents
    (coordinate : Fin (schedule quantitativeOutput geometry floor).levelCount) :=
  quantitativeVerticalTransportedSourceParents
    quantitativeOutput geometry frostman floor coordinate

private noncomputable abbrev sourceParents
    (coordinate : Fin (schedule quantitativeOutput geometry floor).levelCount) :=
  (quantitativeVerticalMatchedSourceNearby
    quantitativeOutput geometry floor coordinate).scaleData.cover
      |>.hitParentSubfamily
        (quantitativeVerticalExactSourcePacket
          quantitativeOutput geometry frostman)

private noncomputable abbrev rawParent
    (coordinate : Fin (schedule quantitativeOutput geometry floor).levelCount) :=
  quantitativeVerticalTransportedSourceParent
    quantitativeOutput geometry frostman floor coordinate

/-- Four times the raw transport radius leaves room both for the source-fibre
transport loss and for quotienting to a nearby raw parent. -/
def quantitativeVerticalTransportedQuotientScale
    (coordinate : Fin (schedule quantitativeOutput geometry floor).levelCount) :
    ℝ :=
  4 * quantitativeVerticalTransportedSourceParentScale
    quantitativeOutput geometry floor coordinate

/-- The honest quotient-parent radius costs only one source nearby-CWA power
and the explicit absolute transport constant. -/
theorem quantitativeVerticalTransportedQuotientScale_lt_requested
    (hinputLoss : 0 ≤ quantitativeOutput.normalized.inputLoss)
    (coordinate : Fin (schedule quantitativeOutput geometry floor).levelCount) :
    quantitativeVerticalTransportedQuotientScale
        quantitativeOutput geometry floor coordinate <
      57600004 *
        Real.rpow sourceDelta (-quantitativeOutput.normalized.inputLoss) *
          (schedule quantitativeOutput geometry floor).requested coordinate := by
  let target :=
    ((schedule quantitativeOutput geometry floor).requested coordinate).1
  let sourceRho :=
    (quantitativeVerticalMatchedSourceNearby
      quantitativeOutput geometry floor coordinate).rho
  let sourcePower :=
    Real.rpow sourceDelta (-quantitativeOutput.normalized.inputLoss)
  have hscalePos : 0 < pureWZ2Proposition64Lemma35Scale :=
    pureWZ2Proposition64Lemma35Scale_pos
  have htargetPos : 0 < target :=
    lt_of_lt_of_le geometry.scales.finalDelta_pos
      ((schedule quantitativeOutput geometry floor).requested coordinate).2.1
  have hsourcePowerOne : 1 ≤ sourcePower := by
    exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos
      quantitativeOutput.normalized.source.extremal.delta_pos
      quantitativeOutput.normalized.source.extremal.delta_le_one
      (by linarith)
  have hsourceRho :
      sourceRho <
        sourcePower *
          (target / (45 * pureWZ2Proposition64Lemma35Scale)) := by
    exact quantitativeVerticalMatchedSourceNearby_rho_lt_target
      quantitativeOutput geometry floor coordinate
  have hfinalLe :
      pureWZ2Proposition64Lemma35FinalDelta sourceDelta ≤ target :=
    ((schedule quantitativeOutput geometry floor).requested coordinate).2.1
  unfold quantitativeVerticalTransportedQuotientScale
    quantitativeVerticalTransportedSourceParentScale
    pureWZ2Proposition64RepresentativeTransportScale
  change
    4 * (648000000 * pureWZ2Proposition64Lemma35Scale * sourceRho +
        pureWZ2Proposition64Lemma35FinalDelta sourceDelta) <
      57600004 * sourcePower * target
  calc
    4 * (648000000 * pureWZ2Proposition64Lemma35Scale * sourceRho +
          pureWZ2Proposition64Lemma35FinalDelta sourceDelta) <
        4 * (648000000 * pureWZ2Proposition64Lemma35Scale *
              (sourcePower *
                (target / (45 * pureWZ2Proposition64Lemma35Scale))) +
            target) := by
      apply mul_lt_mul_of_pos_left _ (by norm_num)
      exact add_lt_add_of_lt_of_le
        (mul_lt_mul_of_pos_left hsourceRho
          (mul_pos (by norm_num) hscalePos))
        hfinalLe
    _ = 57600000 * sourcePower * target + 4 * target := by
      field_simp [hscalePos.ne']
      <;> ring
    _ ≤ 57600000 * sourcePower * target +
          4 * (sourcePower * target) := by
      gcongr
      simpa using
        mul_le_mul_of_nonneg_right hsourcePowerOne htargetPos.le
    _ = 57600004 * sourcePower * target := by ring

/-- Transport and fixed-ratio quotienting only round the target grid upward. -/
theorem quantitativeVerticalRequested_le_transportedQuotientScale
    (coordinate : Fin (schedule quantitativeOutput geometry floor).levelCount) :
    (schedule quantitativeOutput geometry floor).requested coordinate ≤
      quantitativeVerticalTransportedQuotientScale
        quantitativeOutput geometry floor coordinate := by
  let target :=
    ((schedule quantitativeOutput geometry floor).requested coordinate).1
  let sourceRho :=
    (quantitativeVerticalMatchedSourceNearby
      quantitativeOutput geometry floor coordinate).rho
  have hfactorPos : 0 < quantitativeVerticalSourceTransportScaleFactor := by
    unfold quantitativeVerticalSourceTransportScaleFactor
    exact mul_pos (by norm_num) pureWZ2Proposition64Lemma35Scale_pos
  have hsourceRequested :
      target / quantitativeVerticalSourceTransportScaleFactor ≤ sourceRho := by
    exact (le_max_right sourceDelta
      (target / quantitativeVerticalSourceTransportScaleFactor)).trans
        (quantitativeVerticalMatchedSourceNearby
          quantitativeOutput geometry floor coordinate).requested_le
  have htarget :
      target ≤ quantitativeVerticalSourceTransportScaleFactor * sourceRho := by
    have h :=
      (div_le_iff₀ hfactorPos).mp hsourceRequested
    simpa [mul_comm] using h
  have hfactor :
      quantitativeVerticalSourceTransportScaleFactor ≤
        4 * (648000000 * pureWZ2Proposition64Lemma35Scale) := by
    unfold quantitativeVerticalSourceTransportScaleFactor
    nlinarith [pureWZ2Proposition64Lemma35Scale_pos]
  calc
    target ≤ quantitativeVerticalSourceTransportScaleFactor * sourceRho :=
      htarget
    _ ≤ (4 * (648000000 * pureWZ2Proposition64Lemma35Scale)) *
          sourceRho := by
      exact mul_le_mul_of_nonneg_right hfactor
        (quantitativeVerticalMatchedSourceNearby
          quantitativeOutput geometry floor coordinate).scaleData.rho_pos.le
    _ ≤ 4 * (648000000 * pureWZ2Proposition64Lemma35Scale * sourceRho +
          pureWZ2Proposition64Lemma35FinalDelta sourceDelta) := by
      nlinarith [geometry.scales.finalDelta_pos]
    _ = quantitativeVerticalTransportedQuotientScale
          quantitativeOutput geometry floor coordinate := by
      simp only [quantitativeVerticalTransportedQuotientScale,
        quantitativeVerticalTransportedSourceParentScale,
        pureWZ2Proposition64RepresentativeTransportScale]
      ring

/-- Positive-gap scalar absorption upgrades the independent target grid to
the honest transported quotient scales. -/
theorem exists_transportedQuotientScale_rounding
    {nearbyLoss : ℝ}
    (hinputLoss : 0 ≤ quantitativeOutput.normalized.inputLoss)
    (habsorb :
      ENNReal.ofReal 57600004 *
          Kakeya.realRpowENN sourceDelta
            (-quantitativeOutput.normalized.inputLoss) *
          Kakeya.realRpowENN
            (pureWZ2Proposition64Lemma35FinalDelta sourceDelta)
            (-pureWZ2Proposition64TargetGridLoss floor) ≤
        Kakeya.realRpowENN
          (pureWZ2Proposition64Lemma35FinalDelta sourceDelta)
          (-nearbyLoss))
    (requested : WZ2PaperRequestedScale
      (pureWZ2Proposition64Lemma35FinalDelta sourceDelta)) :
    ∃ coordinate : Fin (schedule quantitativeOutput geometry floor).levelCount,
      requested.1 ≤
          quantitativeVerticalTransportedQuotientScale
            quantitativeOutput geometry floor coordinate ∧
        ENNReal.ofReal
            (quantitativeVerticalTransportedQuotientScale
              quantitativeOutput geometry floor coordinate) <
          Kakeya.realRpowENN
              (pureWZ2Proposition64Lemma35FinalDelta sourceDelta)
              (-nearbyLoss) *
            ENNReal.ofReal requested.1 := by
  rcases (schedule quantitativeOutput geometry floor).rounding requested with
    ⟨coordinate, hrequestedGrid, hgridWindow⟩
  refine ⟨coordinate,
    hrequestedGrid.trans
      (quantitativeVerticalRequested_le_transportedQuotientScale
        quantitativeOutput geometry floor coordinate), ?_⟩
  have hquotientReal :=
    quantitativeVerticalTransportedQuotientScale_lt_requested
      quantitativeOutput geometry floor hinputLoss coordinate
  have hquotientENN :
      ENNReal.ofReal
          (quantitativeVerticalTransportedQuotientScale
            quantitativeOutput geometry floor coordinate) <
        ENNReal.ofReal
          (57600004 *
            Real.rpow sourceDelta
              (-quantitativeOutput.normalized.inputLoss) *
            (schedule quantitativeOutput geometry floor).requested coordinate) :=
    (ENNReal.ofReal_lt_ofReal_iff (by
      have hrequestedPos :
          0 < ((schedule quantitativeOutput geometry floor).requested
            coordinate : ℝ) :=
        lt_of_lt_of_le geometry.scales.finalDelta_pos
          ((schedule quantitativeOutput geometry floor).requested coordinate).2.1
      exact mul_pos
        (mul_pos (by norm_num)
          (Real.rpow_pos_of_pos
            quantitativeOutput.normalized.source.extremal.delta_pos _))
        hrequestedPos)).mpr hquotientReal
  have hsourcePower :
      0 ≤ Real.rpow sourceDelta
        (-quantitativeOutput.normalized.inputLoss) :=
    Real.rpow_nonneg
      quantitativeOutput.normalized.source.extremal.delta_pos.le _
  have htargetNonneg :
      0 ≤ ((schedule quantitativeOutput geometry floor).requested coordinate : ℝ) :=
    ((schedule quantitativeOutput geometry floor).requested coordinate).2.1
      |>.trans' geometry.scales.finalDelta_pos.le
  have hquotientENN' :
      ENNReal.ofReal
          (quantitativeVerticalTransportedQuotientScale
            quantitativeOutput geometry floor coordinate) <
        ENNReal.ofReal 57600004 *
          Kakeya.realRpowENN sourceDelta
            (-quantitativeOutput.normalized.inputLoss) *
          ENNReal.ofReal
            ((schedule quantitativeOutput geometry floor).requested
              coordinate) := by
    rw [ENNReal.ofReal_mul
      (mul_nonneg (by norm_num) hsourcePower),
      ENNReal.ofReal_mul (by norm_num)] at hquotientENN
    exact hquotientENN
  let multiplier :=
    ENNReal.ofReal 57600004 *
      Kakeya.realRpowENN sourceDelta
        (-quantitativeOutput.normalized.inputLoss)
  have hmultiplierPos : 0 < multiplier := by
    exact ENNReal.mul_pos
      (ENNReal.ofReal_pos.mpr (by norm_num)).ne'
      (ENNReal.ofReal_pos.mpr <|
        Real.rpow_pos_of_pos
          quantitativeOutput.normalized.source.extremal.delta_pos _).ne'
  have hmultiplierTop : multiplier ≠ ⊤ := by
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (by simp [Kakeya.realRpowENN])
  have hgridScaled :
      multiplier *
          ENNReal.ofReal
            ((schedule quantitativeOutput geometry floor).requested coordinate) <
        multiplier *
          (Kakeya.realRpowENN
              (pureWZ2Proposition64Lemma35FinalDelta sourceDelta)
              (-pureWZ2Proposition64TargetGridLoss floor) *
            ENNReal.ofReal requested.1) := by
    simpa [Kakeya.realRpowENN, mul_comm] using
      ENNReal.mul_lt_mul_right
        hmultiplierPos.ne' hmultiplierTop hgridWindow
  calc
    ENNReal.ofReal
        (quantitativeVerticalTransportedQuotientScale
          quantitativeOutput geometry floor coordinate) <
        ENNReal.ofReal 57600004 *
          Kakeya.realRpowENN sourceDelta
            (-quantitativeOutput.normalized.inputLoss) *
          ENNReal.ofReal
            ((schedule quantitativeOutput geometry floor).requested
              coordinate) := hquotientENN'
    _ < ENNReal.ofReal 57600004 *
          Kakeya.realRpowENN sourceDelta
            (-quantitativeOutput.normalized.inputLoss) *
          (Kakeya.realRpowENN
              (pureWZ2Proposition64Lemma35FinalDelta sourceDelta)
              (-pureWZ2Proposition64TargetGridLoss floor) *
            ENNReal.ofReal requested.1) := by
      simpa [multiplier, mul_assoc] using hgridScaled
    _ = (ENNReal.ofReal 57600004 *
          Kakeya.realRpowENN sourceDelta
            (-quantitativeOutput.normalized.inputLoss) *
          Kakeya.realRpowENN
            (pureWZ2Proposition64Lemma35FinalDelta sourceDelta)
            (-pureWZ2Proposition64TargetGridLoss floor)) *
        ENNReal.ofReal requested.1 := by ring
    _ ≤ Kakeya.realRpowENN
          (pureWZ2Proposition64Lemma35FinalDelta sourceDelta)
          (-nearbyLoss) *
        ENNReal.ofReal requested.1 := by
      exact mul_le_mul_right' habsorb _

def quantitativeVerticalTransportedQuotientConflictDegree : ℕ :=
  (2 * 6400 + 1) ^ 5

/-- Two selector slots per requested scale: the conflict-color/target-owner
slot and the joint target-owner/source-owner slot. -/
def quantitativeVerticalTransportedSelectorCoordinateCount : ℕ :=
  (schedule quantitativeOutput geometry floor).levelCount * 2

theorem quantitativeVerticalTransportedScheduleLevelCount_eq :
    (schedule quantitativeOutput geometry floor).levelCount =
      pureWZ2Prop62RequestedScaleLevelCount
        (pureWZ2Proposition64TargetGridLoss floor) := by
  unfold schedule quantitativeVerticalRequestedScaleScheduleFor
    quantitativeVerticalRequestedScaleScheduleOfLoss
  rfl

/-- The number of transported selector coordinates is fixed by the
pre-runtime target-grid loss; it does not depend on the source family. -/
theorem quantitativeVerticalTransportedSelectorCoordinateCount_eq :
    quantitativeVerticalTransportedSelectorCoordinateCount
        quantitativeOutput geometry floor =
      2 * pureWZ2Prop62RequestedScaleLevelCount
        (pureWZ2Proposition64TargetGridLoss floor) := by
  unfold quantitativeVerticalTransportedSelectorCoordinateCount
  rw [quantitativeVerticalTransportedScheduleLevelCount_eq]
  omega

/-- The common degree loss from the one combined selection. -/
noncomputable def quantitativeVerticalTransportedPairDegreeConstant : ENNReal :=
  16 *
      (quantitativeVerticalTransportedSelectorCoordinateCount
        quantitativeOutput geometry floor : ENNReal) *
    (Nat.log 2
        (2 *
          (initialED quantitativeOutput geometry frostman).subfamily.family.card) +
        1 : ENNReal) ^
      quantitativeVerticalTransportedSelectorCoordinateCount
        quantitativeOutput geometry floor

/-- The color-vector and degree-regularization loss from the same combined
selection.  Only the direct slot has nontrivial colors. -/
noncomputable def quantitativeVerticalTransportedSelectionRetention : ENNReal :=
  ((quantitativeVerticalTransportedQuotientConflictDegree + 1) ^
      (schedule quantitativeOutput geometry floor).levelCount : ℕ) *
    8 *
      (Nat.log 2
          (2 *
            (initialED quantitativeOutput geometry frostman).subfamily.family.card) +
          1 : ENNReal) ^
        (quantitativeVerticalTransportedSelectorCoordinateCount
          quantitativeOutput geometry floor + 1)

/-- One maximal quotient net at every transported source-parent coordinate. -/
structure QuantitativeVerticalTransportedSourceParentQuotientData
    (raw : QuantitativeVerticalTransportedSourceParentScheduleData
      quantitativeOutput geometry frostman floor) where
  net : ∀ coordinate,
    WZ2FiniteMaximalQuotientNetData
      (rawParents quantitativeOutput geometry frostman floor coordinate).card
      (fun first second => wz1PaperLineDistance
        ((rawParents quantitativeOutput geometry frostman floor coordinate).tube
          first)
        ((rawParents quantitativeOutput geometry frostman floor coordinate).tube
          second))
      (quantitativeVerticalTransportedSourceParentScale
        quantitativeOutput geometry floor coordinate)

namespace QuantitativeVerticalTransportedSourceParentQuotientData

def centerPackingFamily
    {raw : QuantitativeVerticalTransportedSourceParentScheduleData
      quantitativeOutput geometry frostman floor}
    (data : QuantitativeVerticalTransportedSourceParentQuotientData
      quantitativeOutput geometry frostman floor raw)
    (coordinate : Fin (schedule quantitativeOutput geometry floor).levelCount) :
    Kakeya.Streamlined.TubeFamily
      (quantitativeVerticalTransportedSourceParentScale
        quantitativeOutput geometry floor coordinate) where
  card := (data.net coordinate).centers.card
  tube parent :=
    (rawParents quantitativeOutput geometry frostman floor coordinate).tube
      ((data.net coordinate).centerEmbedding parent)

def quotientParents
    {raw : QuantitativeVerticalTransportedSourceParentScheduleData
      quantitativeOutput geometry frostman floor}
    (data : QuantitativeVerticalTransportedSourceParentQuotientData
      quantitativeOutput geometry frostman floor raw)
    (coordinate : Fin (schedule quantitativeOutput geometry floor).levelCount) :
    Kakeya.Streamlined.TubeFamily
      (quantitativeVerticalTransportedQuotientScale
        quantitativeOutput geometry floor coordinate) where
  card := (data.net coordinate).centers.card
  tube parent := wz2PaperRelabelTube
    (targetScale := quantitativeVerticalTransportedQuotientScale
      quantitativeOutput geometry floor coordinate)
    ((rawParents quantitativeOutput geometry frostman floor coordinate).tube
      ((data.net coordinate).centerEmbedding parent))

def assignedParent
    {raw : QuantitativeVerticalTransportedSourceParentScheduleData
      quantitativeOutput geometry frostman floor}
    (data : QuantitativeVerticalTransportedSourceParentQuotientData
      quantitativeOutput geometry frostman floor raw)
    (coordinate : Fin (schedule quantitativeOutput geometry floor).levelCount) :
    Fin (initialED quantitativeOutput geometry frostman).subfamily.family.card →
      Fin (data.quotientParents quantitativeOutput geometry frostman floor
        coordinate).card :=
  fun source => (data.net coordinate).center
    (rawParent quantitativeOutput geometry frostman floor coordinate source)

theorem rawParentScale_pos
    {raw : QuantitativeVerticalTransportedSourceParentScheduleData
      quantitativeOutput geometry frostman floor}
    (data : QuantitativeVerticalTransportedSourceParentQuotientData
      quantitativeOutput geometry frostman floor raw)
    (coordinate : Fin (schedule quantitativeOutput geometry floor).levelCount) :
    0 < quantitativeVerticalTransportedSourceParentScale
      quantitativeOutput geometry floor coordinate :=
  (raw.toPreAssignedParentCover
    quantitativeOutput geometry frostman floor coordinate).rho_pos

theorem quotientScale_pos
    {raw : QuantitativeVerticalTransportedSourceParentScheduleData
      quantitativeOutput geometry frostman floor}
    (data : QuantitativeVerticalTransportedSourceParentQuotientData
      quantitativeOutput geometry frostman floor raw)
    (coordinate : Fin (schedule quantitativeOutput geometry floor).levelCount) :
    0 < quantitativeVerticalTransportedQuotientScale
      quantitativeOutput geometry floor coordinate := by
  unfold quantitativeVerticalTransportedQuotientScale
  have hraw := data.rawParentScale_pos
    quantitativeOutput geometry frostman floor coordinate
  linarith

theorem rawParents_centered
    {raw : QuantitativeVerticalTransportedSourceParentScheduleData
      quantitativeOutput geometry frostman floor}
    (data : QuantitativeVerticalTransportedSourceParentQuotientData
      quantitativeOutput geometry frostman floor raw)
    (coordinate : Fin (schedule quantitativeOutput geometry floor).levelCount)
    (parent : Fin
      (rawParents quantitativeOutput geometry frostman floor coordinate).card) :
    pureWZ2PaperCenteredTube
        ((rawParents quantitativeOutput geometry frostman floor coordinate).tube
          parent) =
      (rawParents quantitativeOutput geometry frostman floor coordinate).tube
        parent := by
  let ed := initialED quantitativeOutput geometry frostman
  let representative := quantitativeVerticalSourceParentRepresentative
    quantitativeOutput geometry frostman floor coordinate parent
  let finalTube := ed.subfamily.family.tube representative
  change pureWZ2PaperCenteredTube
      (wz2PaperRelabelTube
        (targetScale := quantitativeVerticalTransportedSourceParentScale
          quantitativeOutput geometry floor coordinate)
        (pureWZ2PaperCenteredTube finalTube)) = _
  apply pureWZ2PaperCenteredTube_eq_self
  · exact wz2PaperRelabelTube_lineClass <|
      pureWZ2PaperCenteredTube_lineClass <|
        geometry.paperED_lineClass ed representative
  · change 0 ≤ wz1PaperDirection finalTube 2
    linarith [(geometry.paperED_lineClass ed representative).1]
  · change wz2PaperTubeMidpoint
        (pureWZ2PaperCenteredTube finalTube) 2 = 0
    rw [pureWZ2PaperCenteredTube_midpoint]
    exact wz1TubeAxisZeroPoint_coord_two finalTube
      (geometry.paperED_lineClass ed representative).vertical

theorem centerPacking_lineClass
    {raw : QuantitativeVerticalTransportedSourceParentScheduleData
      quantitativeOutput geometry frostman floor}
    (data : QuantitativeVerticalTransportedSourceParentQuotientData
      quantitativeOutput geometry frostman floor raw)
    (coordinate : Fin (schedule quantitativeOutput geometry floor).levelCount) :
    WZ1PaperIsLineClass (data.centerPackingFamily
      quantitativeOutput geometry frostman floor coordinate) := by
  intro parent
  exact raw.targetCoarse_lineClass
    quantitativeOutput geometry frostman floor coordinate
      ((data.net coordinate).centerEmbedding parent)

theorem centerPacking_distinct
    {raw : QuantitativeVerticalTransportedSourceParentScheduleData
      quantitativeOutput geometry frostman floor}
    (data : QuantitativeVerticalTransportedSourceParentQuotientData
      quantitativeOutput geometry frostman floor raw)
    (coordinate : Fin (schedule quantitativeOutput geometry floor).levelCount) :
    WZ1PaperIsEssentiallyDistinct (data.centerPackingFamily
      quantitativeOutput geometry frostman floor coordinate) := by
  intro first second hne
  exact (data.net coordinate).centers_separated first second hne

theorem quotientParents_lineClass
    {raw : QuantitativeVerticalTransportedSourceParentScheduleData
      quantitativeOutput geometry frostman floor}
    (data : QuantitativeVerticalTransportedSourceParentQuotientData
      quantitativeOutput geometry frostman floor raw)
    (coordinate : Fin (schedule quantitativeOutput geometry floor).levelCount) :
    WZ1PaperIsLineClass (data.quotientParents
      quantitativeOutput geometry frostman floor coordinate) := by
  intro parent
  exact wz2PaperRelabelTube_lineClass <|
    raw.targetCoarse_lineClass
      quantitativeOutput geometry frostman floor coordinate
        ((data.net coordinate).centerEmbedding parent)

theorem assignedParent_surjective
    {raw : QuantitativeVerticalTransportedSourceParentScheduleData
      quantitativeOutput geometry frostman floor}
    (data : QuantitativeVerticalTransportedSourceParentQuotientData
      quantitativeOutput geometry frostman floor raw)
    (coordinate : Fin (schedule quantitativeOutput geometry floor).levelCount) :
    Function.Surjective (data.assignedParent
      quantitativeOutput geometry frostman floor coordinate) := by
  intro quotientParent
  change Fin (data.net coordinate).centers.card at quotientParent
  rcases (data.net coordinate).center_surjective quotientParent with
    ⟨rawParentIndex, hrawParent⟩
  rcases raw.targetParent_surjective
      quantitativeOutput geometry frostman floor coordinate rawParentIndex with
    ⟨source, hsource⟩
  refine ⟨source, ?_⟩
  change (data.net coordinate).center
      (rawParent quantitativeOutput geometry frostman floor coordinate source) =
    quotientParent
  have hsource' :
      rawParent quantitativeOutput geometry frostman floor coordinate source =
        rawParentIndex := hsource
  rw [hsource']
  exact hrawParent

def sourceOwner
    {raw : QuantitativeVerticalTransportedSourceParentScheduleData
      quantitativeOutput geometry frostman floor}
    (data : QuantitativeVerticalTransportedSourceParentQuotientData
      quantitativeOutput geometry frostman floor raw)
    (coordinate : Fin (schedule quantitativeOutput geometry floor).levelCount) :
    Fin (initialED quantitativeOutput geometry frostman).subfamily.family.card →
      Fin (quantitativeVerticalMatchedSourceNearby
        quantitativeOutput geometry floor coordinate).scaleData.coarse.card :=
  fun source =>
    (quantitativeVerticalMatchedSourceNearby
      quantitativeOutput geometry floor coordinate).scaleData.cover.parent
      ((quantitativeVerticalExactSourcePacket
        quantitativeOutput geometry frostman).embedding source)

/-- The quotient target owner is a function of the original source parent.
This is the exact source of the later local-fanout bound one. -/
theorem assignedParent_eq_of_sourceOwner_eq
    {raw : QuantitativeVerticalTransportedSourceParentScheduleData
      quantitativeOutput geometry frostman floor}
    (data : QuantitativeVerticalTransportedSourceParentQuotientData
      quantitativeOutput geometry frostman floor raw)
    (coordinate : Fin (schedule quantitativeOutput geometry floor).levelCount)
    (first second : Fin
      (initialED quantitativeOutput geometry frostman).subfamily.family.card)
    (howner : data.sourceOwner quantitativeOutput geometry frostman floor
      coordinate first =
      data.sourceOwner quantitativeOutput geometry frostman floor
        coordinate second) :
    data.assignedParent quantitativeOutput geometry frostman floor coordinate
        first =
      data.assignedParent quantitativeOutput geometry frostman floor coordinate
        second := by
  have hraw :
      rawParent quantitativeOutput geometry frostman floor coordinate first =
        rawParent quantitativeOutput geometry frostman floor coordinate second := by
    apply (sourceParents quantitativeOutput geometry frostman floor coordinate).embedding.injective
    rw [raw.source_parent_synchronized coordinate first,
      raw.source_parent_synchronized coordinate second]
    exact howner
  unfold assignedParent
  rw [hraw]

theorem quotientParents_lineDistance_eq_centerPacking
    {raw : QuantitativeVerticalTransportedSourceParentScheduleData
      quantitativeOutput geometry frostman floor}
    (data : QuantitativeVerticalTransportedSourceParentQuotientData
      quantitativeOutput geometry frostman floor raw)
    (coordinate : Fin (schedule quantitativeOutput geometry floor).levelCount)
    (first second : Fin (data.quotientParents
      quantitativeOutput geometry frostman floor coordinate).card) :
    wz1PaperLineDistance
        ((data.quotientParents quantitativeOutput geometry frostman floor
          coordinate).tube first)
        ((data.quotientParents quantitativeOutput geometry frostman floor
          coordinate).tube second) =
      wz1PaperLineDistance
        ((data.centerPackingFamily quantitativeOutput geometry frostman floor
          coordinate).tube first)
        ((data.centerPackingFamily quantitativeOutput geometry frostman floor
          coordinate).tube second) := by
  change wz1PaperLineDistance (wz2PaperRelabelTube _)
      (wz2PaperRelabelTube _) = _
  rw [wz2PaperRelabelTube_lineDistance_both]
  rfl

theorem quotientParentConflict_degree
    {raw : QuantitativeVerticalTransportedSourceParentScheduleData
      quantitativeOutput geometry frostman floor}
    (data : QuantitativeVerticalTransportedSourceParentQuotientData
      quantitativeOutput geometry frostman floor raw)
    (coordinate : Fin (schedule quantitativeOutput geometry floor).levelCount)
    (fixed : Fin (data.quotientParents
      quantitativeOutput geometry frostman floor coordinate).card) :
    ((Finset.univ : Finset (Fin (data.quotientParents
      quantitativeOutput geometry frostman floor coordinate).card)).filter
      (fun other =>
        wz1PaperLineDistance
            ((data.quotientParents quantitativeOutput geometry frostman floor
              coordinate).tube fixed)
            ((data.quotientParents quantitativeOutput geometry frostman floor
              coordinate).tube other) ≤
          2 * wz2PaperLocalizedDoubledFiberLineDistanceConstant *
            quantitativeVerticalTransportedQuotientScale
              quantitativeOutput geometry floor coordinate)).card ≤
      quantitativeVerticalTransportedQuotientConflictDegree := by
  let radius := quantitativeVerticalTransportedSourceParentScale
    quantitativeOutput geometry floor coordinate
  let quotientRadius := quantitativeVerticalTransportedQuotientScale
    quantitativeOutput geometry floor coordinate
  have hsep :
      0 < 2 * wz2PaperLocalizedDoubledFiberLineDistanceConstant *
        quotientRadius := by
    have hq := data.quotientScale_pos
      quantitativeOutput geometry frostman floor coordinate
    unfold wz2PaperLocalizedDoubledFiberLineDistanceConstant
    positivity
  have hpacking := tube_packing_bound_general
    (data.centerPacking_distinct
      quantitativeOutput geometry frostman floor coordinate)
    (data.centerPacking_lineClass
      quantitativeOutput geometry frostman floor coordinate)
    (data.rawParentScale_pos
      quantitativeOutput geometry frostman floor coordinate)
    (2 * wz2PaperLocalizedDoubledFiberLineDistanceConstant * quotientRadius)
    hsep fixed
  have hceil :
      Nat.ceil
          (8 *
            (2 * wz2PaperLocalizedDoubledFiberLineDistanceConstant *
              quotientRadius) / radius) =
        6400 := by
    have hradius := data.rawParentScale_pos
      quantitativeOutput geometry frostman floor coordinate
    have halgebra :
        8 *
            (2 * wz2PaperLocalizedDoubledFiberLineDistanceConstant *
              quotientRadius) / radius =
          (6400 : ℝ) := by
      dsimp only [quotientRadius, radius,
        quantitativeVerticalTransportedQuotientScale]
      unfold wz2PaperLocalizedDoubledFiberLineDistanceConstant
      field_simp [hradius.ne']
      ring
    rw [halgebra]
    norm_num
  have hpacking' :
      ((Finset.univ : Finset (Fin (data.centerPackingFamily
        quantitativeOutput geometry frostman floor coordinate).card)).filter
        (fun other =>
          wz1PaperLineDistance
              ((data.centerPackingFamily quantitativeOutput geometry frostman
                floor coordinate).tube other)
              ((data.centerPackingFamily quantitativeOutput geometry frostman
                floor coordinate).tube fixed) ≤
            2 * wz2PaperLocalizedDoubledFiberLineDistanceConstant *
              quotientRadius)).card ≤
        quantitativeVerticalTransportedQuotientConflictDegree := by
    rw [hceil] at hpacking
    exact hpacking
  have hfilter :
      (Finset.univ : Finset (Fin (data.quotientParents
        quantitativeOutput geometry frostman floor coordinate).card)).filter
          (fun other =>
            wz1PaperLineDistance
                ((data.quotientParents quantitativeOutput geometry frostman
                  floor coordinate).tube fixed)
                ((data.quotientParents quantitativeOutput geometry frostman
                  floor coordinate).tube other) ≤
              2 * wz2PaperLocalizedDoubledFiberLineDistanceConstant *
                quotientRadius) =
        (Finset.univ : Finset (Fin (data.centerPackingFamily
          quantitativeOutput geometry frostman floor coordinate).card)).filter
          (fun other =>
            wz1PaperLineDistance
                ((data.centerPackingFamily quantitativeOutput geometry frostman
                  floor coordinate).tube other)
                ((data.centerPackingFamily quantitativeOutput geometry frostman
                  floor coordinate).tube fixed) ≤
              2 * wz2PaperLocalizedDoubledFiberLineDistanceConstant *
                quotientRadius) := by
    apply Finset.filter_congr
    intro other _
    rw [data.quotientParents_lineDistance_eq_centerPacking
      quantitativeOutput geometry frostman floor coordinate fixed other]
    exact ⟨fun h => by rwa [wz1PaperLineDistance_symm],
      fun h => by rwa [wz1PaperLineDistance_symm] at h⟩
  rw [hfilter]
  exact hpacking'

theorem assigned_containment
    {raw : QuantitativeVerticalTransportedSourceParentScheduleData
      quantitativeOutput geometry frostman floor}
    (data : QuantitativeVerticalTransportedSourceParentQuotientData
      quantitativeOutput geometry frostman floor raw)
    (coordinate : Fin (schedule quantitativeOutput geometry floor).levelCount)
    (source : Fin
      (initialED quantitativeOutput geometry frostman).subfamily.family.card) :
    ((initialED quantitativeOutput geometry frostman).subfamily.family.tube
        source).carrier ⊆
      ((data.quotientParents quantitativeOutput geometry frostman floor
          coordinate).tube
        (data.assignedParent quantitativeOutput geometry frostman floor
          coordinate source)).carrier := by
  let rawIndex :=
    rawParent quantitativeOutput geometry frostman floor coordinate source
  let centerIndex := (data.net coordinate).center rawIndex
  let first :=
    (rawParents quantitativeOutput geometry frostman floor coordinate).tube
      rawIndex
  let second :=
    (rawParents quantitativeOutput geometry frostman floor coordinate).tube
      ((data.net coordinate).centerEmbedding centerIndex)
  have hdistance : wz1PaperLineDistance first second ≤
      quantitativeVerticalTransportedSourceParentScale
        quantitativeOutput geometry floor coordinate :=
    (data.net coordinate).center_close rawIndex
  have hbudget :
      (3 / 2 : ℝ) * wz1PaperLineDistance first second +
          quantitativeVerticalTransportedSourceParentScale
            quantitativeOutput geometry floor coordinate ≤
        quantitativeVerticalTransportedQuotientScale
          quantitativeOutput geometry floor coordinate := by
    unfold quantitativeVerticalTransportedQuotientScale
    have hpos := data.rawParentScale_pos
      quantitativeOutput geometry frostman floor coordinate
    nlinarith
  have hrawToCenter := pureWZ2_centered_carrier_subset_relabel_of_lineDistance
    (data.rawParentScale_pos quantitativeOutput geometry frostman floor
      coordinate)
    (data.quotientScale_pos quantitativeOutput geometry frostman floor
      coordinate)
    first second hbudget
  have hfirstCentered := data.rawParents_centered
    quantitativeOutput geometry frostman floor coordinate rawIndex
  have hsecondCentered := data.rawParents_centered
    quantitativeOutput geometry frostman floor coordinate
    ((data.net coordinate).centerEmbedding centerIndex)
  rw [hfirstCentered, hsecondCentered] at hrawToCenter
  exact (raw.target_carrier coordinate source).trans <| by
    simpa [quotientParents, assignedParent, rawIndex, centerIndex, first, second]
      using hrawToCenter

noncomputable def toPreAssignedParentCover
    {raw : QuantitativeVerticalTransportedSourceParentScheduleData
      quantitativeOutput geometry frostman floor}
    (data : QuantitativeVerticalTransportedSourceParentQuotientData
      quantitativeOutput geometry frostman floor raw)
    (coordinate : Fin (schedule quantitativeOutput geometry floor).levelCount) :
    PureWZ2LocalizedPreAssignedParentCoverData
      (initialED quantitativeOutput geometry frostman).subfamily.family
      (data.quotientParents quantitativeOutput geometry frostman floor
        coordinate) where
  delta_pos := geometry.scales.finalDelta_pos
  rho_pos := data.quotientScale_pos
    quantitativeOutput geometry frostman floor coordinate
  fine_line_class := geometry.paperED_lineClass
    (initialED quantitativeOutput geometry frostman)
  coarse_line_class := data.quotientParents_lineClass
    quantitativeOutput geometry frostman floor coordinate
  fine_midpoint_local := raw.targetFine_midpoint_local
  assignedParent := data.assignedParent
    quantitativeOutput geometry frostman floor coordinate
  assigned_containment := data.assigned_containment
    quantitativeOutput geometry frostman floor coordinate

/-- The complete finite pre-assigned target schedule on the unchanged final
paper-ED family. -/
noncomputable def preAssignedSchedule
    {raw : QuantitativeVerticalTransportedSourceParentScheduleData
      quantitativeOutput geometry frostman floor}
    (data : QuantitativeVerticalTransportedSourceParentQuotientData
      quantitativeOutput geometry frostman floor raw) :
    PureWZ2FiniteLocalizedPreAssignedParentScheduleData
      (initialED quantitativeOutput geometry frostman).subfamily.family
      (schedule quantitativeOutput geometry floor).levelCount where
  rho := quantitativeVerticalTransportedQuotientScale
    quantitativeOutput geometry floor
  coarse := data.quotientParents quantitativeOutput geometry frostman floor
  cover := data.toPreAssignedParentCover
    quantitativeOutput geometry frostman floor

def conflict
    {raw : QuantitativeVerticalTransportedSourceParentScheduleData
      quantitativeOutput geometry frostman floor}
    (data : QuantitativeVerticalTransportedSourceParentQuotientData
      quantitativeOutput geometry frostman floor raw)
    (coordinate : Fin (schedule quantitativeOutput geometry floor).levelCount)
    (first second : Fin (data.quotientParents
      quantitativeOutput geometry frostman floor coordinate).card) : Prop :=
  wz1PaperLineDistance
      ((data.quotientParents quantitativeOutput geometry frostman floor
        coordinate).tube first)
      ((data.quotientParents quantitativeOutput geometry frostman floor
        coordinate).tube second) ≤
    2 * wz2PaperLocalizedDoubledFiberLineDistanceConstant *
      quantitativeVerticalTransportedQuotientScale
        quantitativeOutput geometry floor coordinate

/-- Proper colors for the quotient-parent conflict graph at every coordinate. -/
structure QuantitativeVerticalTransportedQuotientColoringData
    {raw : QuantitativeVerticalTransportedSourceParentScheduleData
      quantitativeOutput geometry frostman floor}
    (data : QuantitativeVerticalTransportedSourceParentQuotientData
      quantitativeOutput geometry frostman floor raw) where
  color : ∀ coordinate,
    Fin (data.quotientParents quantitativeOutput geometry frostman floor
      coordinate).card →
      Fin (quantitativeVerticalTransportedQuotientConflictDegree + 1)
  proper : ∀ coordinate first second, first ≠ second →
    data.conflict quantitativeOutput geometry frostman floor coordinate
      first second →
    color coordinate first ≠ color coordinate second

theorem exists_coloring
    {raw : QuantitativeVerticalTransportedSourceParentScheduleData
      quantitativeOutput geometry frostman floor}
    (data : QuantitativeVerticalTransportedSourceParentQuotientData
      quantitativeOutput geometry frostman floor raw) :
    Nonempty (QuantitativeVerticalTransportedQuotientColoringData
      quantitativeOutput geometry frostman floor data) := by
  let coloring : ∀ coordinate, ∃ color :
      Fin (data.quotientParents quantitativeOutput geometry frostman floor
        coordinate).card →
        Fin (quantitativeVerticalTransportedQuotientConflictDegree + 1),
      ∀ first second, first ≠ second →
        data.conflict quantitativeOutput geometry frostman floor coordinate
          first second → color first ≠ color second := fun coordinate => by
    have hsymm : ∀ first second,
        (first ≠ second ∧
          data.conflict quantitativeOutput geometry frostman floor coordinate
            first second) →
        second ≠ first ∧
          data.conflict quantitativeOutput geometry frostman floor coordinate
            second first := by
      intro first second h
      exact ⟨h.1.symm, by
        unfold conflict at *
        rw [wz1PaperLineDistance_symm]
        exact h.2
      ⟩
    have hirrefl : ∀ parent, ¬(parent ≠ parent ∧
        data.conflict quantitativeOutput geometry frostman floor coordinate
          parent parent) := fun parent h => h.1 rfl
    have hdegree : ∀ fixed,
        (Finset.univ.filter fun other => fixed ≠ other ∧
          data.conflict quantitativeOutput geometry frostman floor coordinate
            fixed other).card ≤
          quantitativeVerticalTransportedQuotientConflictDegree := by
      intro fixed
      have hsubset :
          (Finset.univ.filter fun other => fixed ≠ other ∧
            data.conflict quantitativeOutput geometry frostman floor
              coordinate fixed other) ⊆
          (Finset.univ.filter fun other =>
            data.conflict quantitativeOutput geometry frostman floor
              coordinate fixed other) := by
        intro other hother
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, (Finset.mem_filter.mp hother).2.2⟩
      exact (Finset.card_le_card hsubset).trans
        (data.quotientParentConflict_degree
          quantitativeOutput geometry frostman floor coordinate fixed)
    rcases pureWZ2_greedy_proper_coloring
      (D := quantitativeVerticalTransportedQuotientConflictDegree)
      hsymm hirrefl (fun fixed => by
        rw [Finset.filter_congr_decidable]
        exact hdegree fixed) with
      ⟨color, proper⟩
    exact ⟨color, fun first second hne hconflict =>
      proper first second ⟨hne, hconflict⟩⟩
  refine ⟨{
    color := fun coordinate => Classical.choose (coloring coordinate)
    proper := ?_ }⟩
  intro coordinate first second hne hconflict
  exact (Classical.choose_spec (coloring coordinate))
    first second hne hconflict



theorem simultaneouslySeparate
    {raw : QuantitativeVerticalTransportedSourceParentScheduleData
      quantitativeOutput geometry frostman floor}
    (data : QuantitativeVerticalTransportedSourceParentQuotientData
      quantitativeOutput geometry frostman floor raw)
    (weight : Fin
      (initialED quantitativeOutput geometry frostman).subfamily.family.card →
        ENNReal) :
    Nonempty (PureWZ2FiniteStrongParentSelectionData
      weight (schedule quantitativeOutput geometry floor).levelCount
      (data.preAssignedSchedule
        quantitativeOutput geometry frostman floor).Parent
      (fun coordinate source =>
        ((data.preAssignedSchedule quantitativeOutput geometry frostman floor).cover
          coordinate).assignedParent source)
      data.conflict quantitativeVerticalTransportedQuotientConflictDegree) := by
  apply (data.preAssignedSchedule quantitativeOutput geometry frostman floor)
    |>.simultaneouslySeparate weight data.conflict
      quantitativeVerticalTransportedQuotientConflictDegree
  · intro coordinate parent
    unfold conflict
    have hdirection : wz1PaperDirection
        ((data.quotientParents quantitativeOutput geometry frostman floor
          coordinate).tube parent) ≠ 0 := by
      intro hzero
      have hnorm := wz1PaperDirection_norm
        ((data.quotientParents quantitativeOutput geometry frostman floor
          coordinate).tube parent)
      rw [hzero, norm_zero] at hnorm
      norm_num at hnorm
    simp [wz1PaperLineDistance,
      InnerProductGeometry.angle_self hdirection]
    have hq := data.quotientScale_pos
      quantitativeOutput geometry frostman floor coordinate
    unfold wz2PaperLocalizedDoubledFiberLineDistanceConstant
    positivity
  · intro coordinate first second hconflict
    unfold conflict at *
    rwa [wz1PaperLineDistance_symm]
  · exact data.quotientParentConflict_degree
      quantitativeOutput geometry frostman floor

end QuantitativeVerticalTransportedSourceParentQuotientData

/-- Construct the fixed-ratio quotient nets from a raw transported-parent
schedule. -/
theorem exists_quantitativeVerticalTransportedSourceParentQuotient
    (raw : QuantitativeVerticalTransportedSourceParentScheduleData
      quantitativeOutput geometry frostman floor) :
    Nonempty (QuantitativeVerticalTransportedSourceParentQuotientData
      quantitativeOutput geometry frostman floor raw) := by
  have hfinalNonempty :
      (initialED quantitativeOutput geometry frostman).subfamily.family.Nonempty :=
    geometry.paperED_family_nonempty
      (initialED quantitativeOutput geometry frostman)
  let packet := quantitativeVerticalExactSourcePacket
    quantitativeOutput geometry frostman
  have hpacketNonempty : packet.family.Nonempty := by
    change (initialED quantitativeOutput geometry frostman).subfamily.family.Nonempty
    exact hfinalNonempty
  refine ⟨{ net := fun coordinate => Classical.choice <| ?_ }⟩
  apply wz2_finite_maximal_quotient_net
  · exact
      (quantitativeVerticalMatchedSourceNearby
        quantitativeOutput geometry floor coordinate).scaleData.cover
        |>.hitParentSubfamily_nonempty packet hpacketNonempty
  · intro first second
    exact wz1PaperLineDistance_symm _ _
  · intro parent
    have hdirection : wz1PaperDirection
        ((rawParents quantitativeOutput geometry frostman floor coordinate).tube
          parent) ≠ 0 := by
      intro hzero
      have hnorm := wz1PaperDirection_norm
        ((rawParents quantitativeOutput geometry frostman floor coordinate).tube
          parent)
      rw [hzero, norm_zero] at hnorm
      norm_num at hnorm
    simp [wz1PaperLineDistance,
      InnerProductGeometry.angle_self hdirection]
  · exact (raw.toPreAssignedParentCover
      quantitativeOutput geometry frostman floor coordinate).rho_pos

end PureWZ2NormalizedHierarchyOutput.PureWZ2Proposition64Lemma35GeometricData

end Kakeya.Assouad

end
