import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63OneScaleFullGrainGlobal
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63OneScaleMultiplicityPreparation
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63LineHitGrains
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.CubicalSlabLower
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.FiniteIntervalGridOneScaleLocalAD
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma18CloseProjectionIntervalTransfer
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma18CenteredIntervalTransfer

/-!
# Mass-retaining one-scale full-grain candidate

This module composes the two logically distinct preparations needed before a
finite Lemma 4.12 step:

* a dyadic constant-multiplicity refinement of the actual one-scale shading;
* fresh balanced square-root cells on that same refined shading, followed by
  simultaneous full-grain/Fubini selection in every active cell.

The output candidate is the union of all original fine cells that meet the
selected good regions.  It is therefore cubical, contains every full-grain
witness, and retains mass with the explicit factor
`4 * (Nat.log 2 family.card + 1)`.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory Set ENNReal Metric

attribute [local instance] Classical.propDecidable

/-- The complete candidate after constant-multiplicity preparation and the
cellwise full-grain/Fubini construction. -/
structure Proposition63OneScaleFullGrainCandidateData
    {delta sigma firstLoss secondLoss queryScale sqrtScale : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source : WZ1PaperTubeShading family}
    (planeMap : Point3 → Point3)
    (original : PureWZ2OneScaleLocalGrainData
      (sigma := sigma) (outputLoss := firstLoss)
      (rho := queryScale) (Y := source) (fun point => planeMap point))
    (prepared : Proposition63OneScaleConstantMultiplicityData
      (secondLoss := secondLoss) planeMap original)
    (cells : Proposition63BalancedCellData (scale := sqrtScale)
      prepared.refined.shading)
    (lineVolume : ℝ) (coverBudget : ℕ) where
  cellCertificates : Proposition63OneScaleFullGrainCellsData planeMap
    prepared.refined cells lineVolume coverBudget
  lineHits : ∀ cell : {cell // cell ∈ cells.activeCells},
    (cellCertificates.cellData cell).LineHitData

/-- Assemble every active-cell certificate after the caller has obtained a
fresh balanced square-root cells on the constant-multiplicity refinement. -/
theorem proposition63_oneScale_fullGrainCandidate
    {delta sigma firstLoss secondLoss queryScale sqrtScale K lineVolume : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source : WZ1PaperTubeShading family}
    (planeMap : Point3 → Point3)
    (original : PureWZ2OneScaleLocalGrainData
      (sigma := sigma) (outputLoss := firstLoss)
      (rho := queryScale) (Y := source) (fun point => planeMap point))
    (prepared : Proposition63OneScaleConstantMultiplicityData
      (secondLoss := secondLoss) planeMap original)
    (cells : Proposition63BalancedCellData (scale := sqrtScale)
      prepared.refined.shading)
    (hqueryOne : queryScale ≤ 1)
    (hsqrtScale : sqrtScale = Real.sqrt queryScale)
    (hplaneUnit : ∀ point ∈ original.shading.union,
      ‖planeMap point‖ = 1)
    (hK : 1 ≤ K)
    (hplaneLipschitz : ∀ first ∈ original.shading.union,
      ∀ second ∈ original.shading.union,
        dist (planeMap first) (planeMap second) ≤
          K * dist first second)
    (coverBudget : ℕ) (hcoverBudgetPos : 0 < coverBudget)
    (hcoverBudget :
      (512 : ENNReal) *
          ((2 * Nat.ceil (2 * K) + 2 : ENNReal) *
            (9 * Kakeya.realRpowENN delta (-secondLoss) *
              Kakeya.realRpowENN (1 / queryScale) (1 - sigma))) ≤
        (coverBudget : ENNReal))
    (hlineVolume : 0 < lineVolume)
    (hlineFloor : ENNReal.ofReal lineVolume ≤ cells.cellMass / 2) :
    Nonempty
      (Proposition63OneScaleFullGrainCandidateData planeMap original
        prepared cells lineVolume coverBudget) := by
  have hunionSubset : prepared.refined.shading.union ⊆
      original.shading.union := by
    rintro point ⟨index, hpoint⟩
    exact ⟨index, prepared.subshading_original index hpoint⟩
  rcases proposition63_oneScale_fullGrainFubiniCells planeMap
      prepared.refined cells hqueryOne hsqrtScale
      (fun point hpoint => hplaneUnit point (hunionSubset hpoint)) hK
      (fun first hfirst second hsecond =>
        hplaneLipschitz first (hunionSubset hfirst)
          second (hunionSubset hsecond))
      coverBudget hcoverBudgetPos hcoverBudget hlineVolume hlineFloor with
    ⟨fullCells⟩
  have hlineHits : ∀ cell : {cell // cell ∈ cells.activeCells},
      Nonempty (fullCells.cellData cell).LineHitData := by
    intro cell
    have hqueryPos : 0 < queryScale :=
      (prepared.refined.local_ad
        (cells.cellRep cell.1 cell.2)
        (cells.cellRep_in_union cell.1 cell.2)).1
    have hsqrtPos : 0 < sqrtScale := by
      rw [hsqrtScale]
      exact Real.sqrt_pos.mpr hqueryPos
    exact (fullCells.cellData cell).exists_lineHitData
      (fullCells.cellData cell).normal_unit hqueryPos (by positivity)
  let lineHits := fun cell : {cell // cell ∈ cells.activeCells} =>
    Classical.choice (hlineHits cell)
  exact ⟨{ cellCertificates := fullCells, lineHits := lineHits }⟩

namespace Proposition63OneScaleFullGrainCandidateData

variable
    {delta sigma firstLoss secondLoss queryScale sqrtScale : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source : WZ1PaperTubeShading family}
    {planeMap : Point3 → Point3}
    {original : PureWZ2OneScaleLocalGrainData
      (sigma := sigma) (outputLoss := firstLoss)
      (rho := queryScale) (Y := source) (fun point => planeMap point)}
    {prepared : Proposition63OneScaleConstantMultiplicityData
      (secondLoss := secondLoss) planeMap original}
    {cells : Proposition63BalancedCellData (scale := sqrtScale)
      prepared.refined.shading}
    {lineVolume : ℝ} {coverBudget : ℕ}

/-- The cubical candidate on the original fine scale. -/
def candidate
    (data : Proposition63OneScaleFullGrainCandidateData planeMap original
      prepared cells lineVolume coverBudget)
    (hdelta : 0 < delta) : WZ1PaperTubeShading family :=
  data.cellCertificates.cubicalRetainedShading hdelta

theorem candidate_subshading_original
    (data : Proposition63OneScaleFullGrainCandidateData planeMap original
      prepared cells lineVolume coverBudget)
    (hdelta : 0 < delta) :
    PaperIsSubshading' (data.candidate hdelta) original.shading := by
  intro index point hpoint
  exact prepared.subshading_original index
    (data.cellCertificates.cubicalRetainedShading_subshading hdelta index hpoint)

theorem candidate_subshading_source
    (data : Proposition63OneScaleFullGrainCandidateData planeMap original
      prepared cells lineVolume coverBudget)
    (hdelta : 0 < delta) :
    PaperIsSubshading' (data.candidate hdelta) source := by
  intro index point hpoint
  exact original.subshading index
    (data.candidate_subshading_original hdelta index hpoint)

theorem candidate_cubical
    (data : Proposition63OneScaleFullGrainCandidateData planeMap original
      prepared cells lineVolume coverBudget)
    (hdelta : 0 < delta) :
    WZ1PaperIsCubicalShading (data.candidate hdelta) :=
  data.cellCertificates.cubicalRetainedShading_cubical hdelta

theorem candidate_local_ad
    (data : Proposition63OneScaleFullGrainCandidateData planeMap original
      prepared cells lineVolume coverBudget)
    (hdelta : 0 < delta) :
    ∀ point ∈ (data.candidate hdelta).union,
      IsADSet1
        (scalarProjection (planeMap point)
          ((data.candidate hdelta).union ∩
            Metric.closedBall point (Real.sqrt queryScale)))
        queryScale (1 - sigma)
        (Kakeya.realRpowENN delta (-secondLoss)) := by
  intro point hpoint
  have hunionSubset : (data.candidate hdelta).union ⊆
      prepared.refined.shading.union := by
    rintro other ⟨index, hindex⟩
    exact ⟨index,
      data.cellCertificates.cubicalRetainedShading_subshading hdelta index hindex⟩
  have hsetSubset :
      scalarProjection (planeMap point)
          ((data.candidate hdelta).union ∩
            Metric.closedBall point (Real.sqrt queryScale)) ⊆
        scalarProjection (planeMap point)
          (prepared.refined.shading.union ∩
            Metric.closedBall point (Real.sqrt queryScale)) := by
    rintro value ⟨other, hother, rfl⟩
    exact ⟨other, ⟨hunionSubset hother.1, hother.2⟩, rfl⟩
  exact (prepared.refined.local_ad point (hunionSubset hpoint)).mono
    hsetSubset

theorem candidate_variation
    (data : Proposition63OneScaleFullGrainCandidateData planeMap original
      prepared cells lineVolume coverBudget)
    (hdelta : 0 < delta)
    (coefficient : NNReal) (hlipschitz : LipschitzWith coefficient planeMap)
    (spatialScale variationScale : ℝ)
    (hbudget : (coefficient : ℝ) * spatialScale ≤ variationScale) :
    ∀ first ∈ (data.candidate hdelta).union,
      ∀ second ∈ (data.candidate hdelta).union,
        dist first second ≤ spatialScale →
          dist (planeMap first) (planeMap second) ≤ variationScale := by
  intro first _ second _ hdistance
  exact (hlipschitz.dist_le_mul first second).trans <|
    (mul_le_mul_of_nonneg_left hdistance coefficient.coe_nonneg).trans
      hbudget

/-- Every precise cellwise good region remains inside the cubical candidate. -/
theorem cellGood_subset_candidate
    (data : Proposition63OneScaleFullGrainCandidateData planeMap original
      prepared cells lineVolume coverBudget)
    (hdelta : 0 < delta)
    (cell : ℤ × ℤ × ℤ) (hcell : cell ∈ cells.activeCells) :
    data.cellCertificates.cellGood cell ⊆ (data.candidate hdelta).union := by
  intro point hpoint
  apply data.cellCertificates.goodRegion_subset_cubicalRetained_union hdelta
  exact Set.mem_iUnion₂.mpr ⟨cell, hcell, hpoint⟩

/-- The line-hit region in one active square-root cell. -/
def cellLineHitRegion
    (data : Proposition63OneScaleFullGrainCandidateData planeMap original
      prepared cells lineVolume coverBudget)
    (cell : ℤ × ℤ × ℤ) : Set Point3 :=
  if hcell : cell ∈ cells.activeCells then
    (data.lineHits ⟨cell, hcell⟩).region
  else ∅

lemma cellLineHitRegion_eq
    (data : Proposition63OneScaleFullGrainCandidateData planeMap original
      prepared cells lineVolume coverBudget)
    (cell : ℤ × ℤ × ℤ) (hcell : cell ∈ cells.activeCells) :
    data.cellLineHitRegion cell =
      (data.lineHits ⟨cell, hcell⟩).region := by
  simp [cellLineHitRegion, hcell]

/-- Union of the full grains indexed by separated actual parameters on all
selected good lines. -/
def lineHitRegion
    (data : Proposition63OneScaleFullGrainCandidateData planeMap original
      prepared cells lineVolume coverBudget) : Set Point3 :=
  ⋃ cell ∈ cells.activeCells, data.cellLineHitRegion cell

/-- Active square-root cells whose selected line-hit region meets a specified
spatial ball. -/
def lineHitRelevantCells
    (data : Proposition63OneScaleFullGrainCandidateData planeMap original
      prepared cells lineVolume coverBudget)
    (center : Point3) (radius : ℝ) : Finset (ℤ × ℤ × ℤ) :=
  cells.activeCells.filter fun cell =>
    (data.cellLineHitRegion cell ∩ Metric.closedBall center radius).Nonempty

theorem lineHitRegion_measurable
    (data : Proposition63OneScaleFullGrainCandidateData planeMap original
      prepared cells lineVolume coverBudget) :
    MeasurableSet data.lineHitRegion := by
  apply MeasurableSet.biUnion
    (Finset.finite_toSet cells.activeCells).countable
  intro cell hcell
  rw [data.cellLineHitRegion_eq cell hcell]
  exact (data.lineHits ⟨cell, hcell⟩).region_measurable

theorem cellLineHitRegion_subset_cell
    (data : Proposition63OneScaleFullGrainCandidateData planeMap original
      prepared cells lineVolume coverBudget)
    (cell : ℤ × ℤ × ℤ) (hcell : cell ∈ cells.activeCells) :
    data.cellLineHitRegion cell ⊆ wz1PaperGridCube sqrtScale cell := by
  rw [data.cellLineHitRegion_eq cell hcell]
  exact (Proposition63FullGrainFubiniCellData.LineHitData.region_subset_good
      (data.cellCertificates.cellData ⟨cell, hcell⟩)
      (data.lineHits ⟨cell, hcell⟩)).trans
    ((data.cellCertificates.cellData ⟨cell, hcell⟩).good_subset.trans
      Set.inter_subset_right)

theorem lineHitRegion_subset
    (data : Proposition63OneScaleFullGrainCandidateData planeMap original
      prepared cells lineVolume coverBudget) :
    data.lineHitRegion ⊆ prepared.refined.shading.union := by
  intro point hpoint
  rcases Set.mem_iUnion₂.mp hpoint with ⟨cell, hcell, hpointRegion⟩
  rw [data.cellLineHitRegion_eq cell hcell] at hpointRegion
  have hpointGood :
      point ∈ (data.cellCertificates.cellData ⟨cell, hcell⟩).good :=
    Proposition63FullGrainFubiniCellData.LineHitData.region_subset_good
      (data.cellCertificates.cellData ⟨cell, hcell⟩)
      (data.lineHits ⟨cell, hcell⟩) hpointRegion
  have hpointCellGood : point ∈ data.cellCertificates.cellGood cell := by
    rw [data.cellCertificates.cellGood_eq cell hcell]
    exact hpointGood
  exact data.cellCertificates.goodRegion_subset <|
    Set.mem_iUnion₂.mpr ⟨cell, hcell, hpointCellGood⟩

/-- Combine interval bounds from the line-hit regions in the relevant
square-root cells.  Normal variation and the number of nearby cells remain
explicit, so no relation between the interval scale and square-root cell
scale is hidden. -/
theorem lineHitRegion_interval_covering
    (data : Proposition63OneScaleFullGrainCandidateData planeMap original
      prepared cells lineVolume coverBudget)
    {resolutionScale intervalScale spatialRadius normalError : ℝ}
    (hresolution : 0 < resolutionScale)
    (hinterval : 0 < intervalScale)
    (hnormalError : 0 < normalError)
    (hnormalErrorInterval : normalError ≤ intervalScale)
    (neighborBudget : ℕ)
    (hneighbor : ∀ center,
      (data.lineHitRelevantCells center spatialRadius).card ≤
        neighborBudget)
    (hcentered : ∀ center,
      ∀ cell, ∀ hcellRelevant :
          cell ∈ data.lineHitRelevantCells center spatialRadius,
        ∀ point ∈
          data.cellLineHitRegion cell ∩
            Metric.closedBall center spatialRadius,
          dist
              (inner ℝ (point - center) (planeMap center))
              (inner ℝ (point - center)
                (planeMap (cells.cellRep cell
                  ((Finset.mem_filter.mp hcellRelevant).1)))) ≤
            normalError)
    (cellBound : ENNReal)
    (hcell : ∀ cell, ∀ hcell : cell ∈ cells.activeCells,
      ∀ intervalCenter : ℝ,
        (↑(Metric.externalCoveringNumber
          (Real.toNNReal resolutionScale)
          (scalarProjection
              (planeMap (cells.cellRep cell hcell))
              (data.cellLineHitRegion cell) ∩
            Metric.closedBall intervalCenter intervalScale)) : ENNReal) ≤
          cellBound) :
    ∀ center : Point3, ∀ intervalCenter : ℝ,
      (↑(Metric.externalCoveringNumber (Real.toNNReal resolutionScale)
        (scalarProjection (planeMap center)
            (data.lineHitRegion ∩ Metric.closedBall center spatialRadius) ∩
          Metric.closedBall intervalCenter intervalScale)) : ENNReal) ≤
        (2 * Nat.ceil (normalError / resolutionScale) + 2 : ENNReal) *
          ((neighborBudget : ENNReal) * (5 * cellBound)) := by
  intro center intervalCenter
  let relevant := data.lineHitRelevantCells center spatialRadius
  let piece : (ℤ × ℤ × ℤ) → Set Point3 := fun cell =>
    data.cellLineHitRegion cell ∩ Metric.closedBall center spatialRadius
  let normal : (ℤ × ℤ × ℤ) → Point3 := fun cell =>
    if hcell : cell ∈ cells.activeCells then
      planeMap (cells.cellRep cell hcell)
    else planeMap center
  let targetSet := data.lineHitRegion ∩
    Metric.closedBall center spatialRadius
  have hdecompose : ∀ point ∈ targetSet,
      ∃ cell ∈ relevant, point ∈ piece cell := by
    intro point hpoint
    rcases Set.mem_iUnion₂.mp hpoint.1 with
      ⟨cell, hcellActive, hpointCell⟩
    have hcellRelevant : cell ∈ relevant := by
      exact Finset.mem_filter.mpr
        ⟨hcellActive, ⟨point, hpointCell, hpoint.2⟩⟩
    exact ⟨cell, hcellRelevant, hpointCell, hpoint.2⟩
  have hlocal : ∀ cell ∈ relevant, ∀ sourceCenter : ℝ,
      (↑(Metric.externalCoveringNumber
        (Real.toNNReal resolutionScale)
        (scalarProjection (normal cell) (piece cell) ∩
          Metric.closedBall sourceCenter intervalScale)) : ENNReal) ≤
        cellBound := by
    intro cell hcellRelevant sourceCenter
    have hcellActive : cell ∈ cells.activeCells :=
      (Finset.mem_filter.mp hcellRelevant).1
    have hpiece : piece cell ⊆ data.cellLineHitRegion cell :=
      Set.inter_subset_left
    have hmono :
        (↑(Metric.externalCoveringNumber
          (Real.toNNReal resolutionScale)
          (scalarProjection (normal cell) (piece cell) ∩
            Metric.closedBall sourceCenter intervalScale)) : ENNReal) ≤
          (↑(Metric.externalCoveringNumber
            (Real.toNNReal resolutionScale)
            (scalarProjection (planeMap (cells.cellRep cell hcellActive))
                (data.cellLineHitRegion cell) ∩
              Metric.closedBall sourceCenter intervalScale)) : ENNReal) := by
      have hnormal : normal cell =
          planeMap (cells.cellRep cell hcellActive) := by
        simp [normal, hcellActive]
      rw [hnormal]
      exact_mod_cast Metric.externalCoveringNumber_mono_set
        (Set.inter_subset_inter (Set.image_mono hpiece) Set.Subset.rfl)
    exact hmono.trans (hcell cell hcellActive sourceCenter)
  have hraw := Kakeya.Assouad.wz1_lemma18_centered_finite_cell_interval_transfer
    relevant piece normal targetSet center (planeMap center)
    resolutionScale intervalScale normalError cellBound hresolution
    hinterval hnormalError hnormalErrorInterval hdecompose
    (by
      intro cell hcellRelevant point hpoint
      have hcellActive : cell ∈ cells.activeCells :=
        (Finset.mem_filter.mp hcellRelevant).1
      have hnormal : normal cell =
          planeMap (cells.cellRep cell hcellActive) := by
        simp [normal, hcellActive]
      rw [hnormal]
      exact hcentered center cell hcellRelevant point hpoint)
    hlocal intervalCenter
  exact hraw.trans <| by
    gcongr
    exact_mod_cast hneighbor center

/-- Sum the single-cell line-hit volume ledgers over the disjoint active
square-root cells. -/
theorem lineHitRegion_volume_lower
    (data : Proposition63OneScaleFullGrainCandidateData planeMap original
      prepared cells lineVolume coverBudget)
    (hqueryScale : 0 < queryScale) :
    (cells.activeCells.card : ENNReal) *
        (ENNReal.ofReal (lineVolume / (4 * (2 * sqrtScale) ^ 2)) *
          ((cells.cellMass / 2) /
            (2 * (coverBudget : ENNReal)))) ≤
      ENNReal.ofReal (4 * queryScale) * volume data.lineHitRegion := by
  have hdisjoint : Set.PairwiseDisjoint (↑cells.activeCells)
      data.cellLineHitRegion := by
    intro first hfirst second hsecond hne
    exact (wz1PaperGridCube_disjoint hne).mono
      (data.cellLineHitRegion_subset_cell first hfirst)
      (data.cellLineHitRegion_subset_cell second hsecond)
  have hmeasurable : ∀ cell ∈ cells.activeCells,
      MeasurableSet (data.cellLineHitRegion cell) := by
    intro cell hcell
    rw [data.cellLineHitRegion_eq cell hcell]
    exact (data.lineHits ⟨cell, hcell⟩).region_measurable
  have hsum :
      ∑ _cell ∈ cells.activeCells,
          ENNReal.ofReal (lineVolume / (4 * (2 * sqrtScale) ^ 2)) *
            ((cells.cellMass / 2) /
              (2 * (coverBudget : ENNReal))) ≤
        ∑ cell ∈ cells.activeCells,
          ENNReal.ofReal (4 * queryScale) *
            volume (data.cellLineHitRegion cell) := by
    apply Finset.sum_le_sum
    intro cell hcell
    rw [data.cellLineHitRegion_eq cell hcell]
    exact Proposition63FullGrainFubiniCellData.LineHitData.line_volume_mul_threshold_le
      (data.cellCertificates.cellData ⟨cell, hcell⟩)
      (data.lineHits ⟨cell, hcell⟩) hqueryScale
  have hunion : volume data.lineHitRegion =
      ∑ cell ∈ cells.activeCells, volume (data.cellLineHitRegion cell) :=
    measure_biUnion_finset hdisjoint hmeasurable
  rw [hunion]
  simpa only [data.cellLineHitRegion_eq, Finset.sum_const,
    Finset.mul_sum, nsmul_eq_mul] using hsum

/-- Fine cells meeting the genuine line-hit region. -/
def lineHitFineCells
    (data : Proposition63OneScaleFullGrainCandidateData planeMap original
      prepared cells lineVolume coverBudget)
    (hdelta : 0 < delta) : Finset (ℤ × ℤ × ℤ) :=
  (wz1PaperGridIndicesInWindow delta hdelta).filter fun cell =>
    (data.lineHitRegion ∩ wz1PaperGridCube delta cell).Nonempty

/-- Cubical hull of the genuine line-hit full grains. -/
def lineHitCandidate
    (data : Proposition63OneScaleFullGrainCandidateData planeMap original
      prepared cells lineVolume coverBudget)
    (hdelta : 0 < delta) : WZ1PaperTubeShading family :=
  wz2RefinedShading prepared.refined.shading (data.lineHitFineCells hdelta)

theorem lineHitCandidate_subshading
    (data : Proposition63OneScaleFullGrainCandidateData planeMap original
      prepared cells lineVolume coverBudget)
    (hdelta : 0 < delta) :
    PaperIsSubshading' (data.lineHitCandidate hdelta)
      prepared.refined.shading :=
  wz2RefinedShading_subshading

theorem lineHitCandidate_subshading_source
    (data : Proposition63OneScaleFullGrainCandidateData planeMap original
      prepared cells lineVolume coverBudget)
    (hdelta : 0 < delta) :
    PaperIsSubshading' (data.lineHitCandidate hdelta) source := by
  intro index point hpoint
  exact prepared.refined.subshading index
    (data.lineHitCandidate_subshading hdelta index hpoint)

theorem lineHitCandidate_cubical
    (data : Proposition63OneScaleFullGrainCandidateData planeMap original
      prepared cells lineVolume coverBudget)
    (hdelta : 0 < delta) :
    WZ1PaperIsCubicalShading (data.lineHitCandidate hdelta) :=
  wz2RefinedShading_cubical prepared.refined.extremal.cubical

theorem lineHitRegion_subset_candidate_union
    (data : Proposition63OneScaleFullGrainCandidateData planeMap original
      prepared cells lineVolume coverBudget)
    (hdelta : 0 < delta) :
    data.lineHitRegion ⊆ (data.lineHitCandidate hdelta).union := by
  intro point hpoint
  have hpointSource : point ∈ prepared.refined.shading.union :=
    data.lineHitRegion_subset hpoint
  have hpointBox : point ∈ Kakeya.Streamlined.axisBox 2 2 2 := by
    rcases hpointSource with ⟨index, hindex⟩
    exact (prepared.refined.shading.subset_body index hindex).2
  have hwindow : wz1PaperGridIndex delta point ∈
      wz1PaperGridIndicesInWindow delta hdelta :=
    Kakeya.Assouad.paper_point_gridIndex_in_window hdelta hpointBox
  have hpointCell : point ∈
      wz1PaperGridCube delta (wz1PaperGridIndex delta point) := by
    rw [mem_wz1PaperGridCube]
  have hselected : wz1PaperGridIndex delta point ∈
      data.lineHitFineCells hdelta := by
    rw [lineHitFineCells, Finset.mem_filter]
    exact ⟨hwindow, ⟨point, hpoint, hpointCell⟩⟩
  rw [lineHitCandidate, wz2RefinedShading_union_inter]
  refine ⟨hpointSource, ?_⟩
  exact Set.mem_iUnion₂.mpr
    ⟨wz1PaperGridIndex delta point, hselected, hpointCell⟩

/-- Every point of the final cubical hull lies in the same fine `delta`-cube
as a genuine point of the selected line-hit region. -/
theorem lineHitCandidate_close_to_lineHitRegion
    (data : Proposition63OneScaleFullGrainCandidateData planeMap original
      prepared cells lineVolume coverBudget)
    (hdelta : 0 < delta) :
    ∀ point ∈ (data.lineHitCandidate hdelta).union,
      ∃ sourcePoint ∈ data.lineHitRegion,
        dist point sourcePoint ≤ delta * Real.sqrt 3 := by
  intro point hpoint
  have hpointHull := hpoint
  rw [lineHitCandidate, wz2RefinedShading_union_inter] at hpointHull
  rcases Set.mem_iUnion₂.mp hpointHull.2 with
    ⟨cell, hcellSelected, hpointCell⟩
  have hcellHit :
      (data.lineHitRegion ∩ wz1PaperGridCube delta cell).Nonempty := by
    exact (Finset.mem_filter.mp hcellSelected).2
  rcases hcellHit with ⟨sourcePoint, hsourceRegion, hsourceCell⟩
  exact ⟨sourcePoint, hsourceRegion,
    wz1PaperGridCube_diameter hdelta cell hpointCell hsourceCell⟩

/-- Transfer an interval estimate from the genuine line-hit region to its
final cubical hull.  The enlargement costs exactly one `delta * sqrt 3`
thickening and expands the spatial ball by that same amount. -/
theorem lineHitCandidate_interval_covering
    (data : Proposition63OneScaleFullGrainCandidateData planeMap original
      prepared cells lineVolume coverBudget)
    (hdelta : 0 < delta)
    {resolutionScale intervalScale : NNReal} {spatialRadius : ℝ}
    (hresolution : 0 < (resolutionScale : ℝ))
    (hinterval : 0 < (intervalScale : ℝ))
    (hhullInterval : delta * Real.sqrt 3 ≤ (intervalScale : ℝ))
    (hspatialRadius : Real.sqrt queryScale + delta * Real.sqrt 3 ≤
      spatialRadius)
    (hplaneUnit : ∀ point ∈ prepared.refined.shading.union,
      ‖planeMap point‖ = 1)
    (regionBound : ENNReal)
    (hregion : ∀ center : Point3, ∀ intervalCenter : ℝ,
      (Metric.externalCoveringNumber resolutionScale
        (scalarProjection (planeMap center)
            (data.lineHitRegion ∩ Metric.closedBall center spatialRadius) ∩
          Metric.closedBall intervalCenter (intervalScale : ℝ)) : ENNReal) ≤
        regionBound) :
    PureWZ2IntervalCoveringAt (data.lineHitCandidate hdelta) planeMap
      queryScale resolutionScale intervalScale
      ((2 * Nat.ceil ((delta * Real.sqrt 3) /
          (resolutionScale : ℝ)) + 2 :
          ENNReal) * (5 * regionBound)) := by
  intro center intervalCenter
  let target := scalarProjection (planeMap center)
    ((data.lineHitCandidate hdelta).union ∩
      Metric.closedBall (center : Point3) (Real.sqrt queryScale))
  let sourceSet := scalarProjection (planeMap center)
    (data.lineHitRegion ∩ Metric.closedBall (center : Point3) spatialRadius)
  have hcenterPrepared : (center : Point3) ∈
      prepared.refined.shading.union := by
    rcases center.property with ⟨index, hindex⟩
    exact ⟨index, data.lineHitCandidate_subshading hdelta index hindex⟩
  have hclose : ∀ value ∈ target,
      ∃ sourceValue ∈ sourceSet,
        dist value sourceValue ≤ delta * Real.sqrt 3 := by
    intro value hvalue
    rcases hvalue with ⟨point, hpoint, rfl⟩
    rcases data.lineHitCandidate_close_to_lineHitRegion hdelta point
        hpoint.1 with
      ⟨sourcePoint, hsourcePoint, hdistance⟩
    let sourceValue := inner ℝ sourcePoint (planeMap center)
    have hsourceBall : sourcePoint ∈
        Metric.closedBall (center : Point3) spatialRadius := by
      rw [Metric.mem_closedBall]
      calc
        dist sourcePoint center ≤ dist sourcePoint point + dist point center :=
          dist_triangle _ _ _
        _ ≤ delta * Real.sqrt 3 + Real.sqrt queryScale := by
          exact add_le_add (by simpa [dist_comm] using hdistance) hpoint.2
        _ = Real.sqrt queryScale + delta * Real.sqrt 3 := by ring
        _ ≤ spatialRadius := hspatialRadius
    have hsourceValue : sourceValue ∈ sourceSet :=
      ⟨sourcePoint, ⟨hsourcePoint, hsourceBall⟩, rfl⟩
    have hprojectionDistance :
        dist (inner ℝ point (planeMap center)) sourceValue ≤
          delta * Real.sqrt 3 := by
      rw [Real.dist_eq]
      have hinner := abs_real_inner_le_norm
        (point - sourcePoint) (planeMap center)
      have hidentity :
          inner ℝ point (planeMap center) - sourceValue =
            inner ℝ (point - sourcePoint) (planeMap center) := by
        simp [sourceValue, inner_sub_left]
      rw [hidentity]
      calc
        |inner ℝ (point - sourcePoint) (planeMap center)| ≤
            ‖point - sourcePoint‖ * ‖planeMap center‖ := hinner
        _ = dist point sourcePoint := by
          rw [hplaneUnit center hcenterPrepared, mul_one, dist_eq_norm]
        _ ≤ delta * Real.sqrt 3 := hdistance
    exact ⟨sourceValue, hsourceValue, hprojectionDistance⟩
  have hsource : ∀ sourceCenter : ℝ,
      (↑(Metric.externalCoveringNumber resolutionScale
        (sourceSet ∩ Metric.closedBall sourceCenter
          (intervalScale : ℝ))) :
          ENNReal) ≤ regionBound := by
    intro sourceCenter
    exact hregion center sourceCenter
  have hsource' : ∀ sourceCenter : ℝ,
      (↑(Metric.externalCoveringNumber
        (Real.toNNReal (resolutionScale : ℝ))
        (sourceSet ∩ Metric.closedBall sourceCenter
          (intervalScale : ℝ))) : ENNReal) ≤ regionBound := by
    intro sourceCenter
    simpa [Real.toNNReal_of_nonneg resolutionScale.coe_nonneg] using
      hsource sourceCenter
  simpa [target, sourceSet,
      Real.toNNReal_of_nonneg resolutionScale.coe_nonneg]
    using
    Kakeya.Assouad.wz1_lemma18_close_projection_interval_transfer
      target sourceSet (resolutionScale : ℝ) (intervalScale : ℝ)
      (delta * Real.sqrt 3) regionBound hresolution hinterval
      (mul_pos hdelta (Real.sqrt_pos.mpr (by norm_num))) hhullInterval
      hclose hsource' intervalCenter

/-- End-to-end interval covering for the final cubical line-hit candidate.
The displayed constant records, in order, the cubical-hull thickening, the
enlarged interval, the finite set of relevant square-root cells, and the
single-cell good-line covering. -/
theorem lineHitCandidate_interval_covering_of_point_centered
    (data : Proposition63OneScaleFullGrainCandidateData planeMap original
      prepared cells lineVolume coverBudget)
    (hdelta : 0 < delta)
    {intervalScale : NNReal}
    {spatialRadius normalError : ℝ}
    (hquery : 0 < queryScale)
    (hinterval : 0 < (intervalScale : ℝ))
    (hqueryInterval : queryScale ≤ (intervalScale : ℝ))
    (hnormalError : 0 < normalError)
    (hnormalErrorInterval : normalError ≤ (intervalScale : ℝ))
    (hhullInterval : delta * Real.sqrt 3 ≤ (intervalScale : ℝ))
    (hspatialRadius : Real.sqrt queryScale + delta * Real.sqrt 3 ≤
      spatialRadius)
    (hplaneUnit : ∀ point ∈ prepared.refined.shading.union,
      ‖planeMap point‖ = 1)
    (neighborBudget : ℕ)
    (hneighbor : ∀ center,
      (data.lineHitRelevantCells center spatialRadius).card ≤
        neighborBudget)
    (hcentered : ∀ center,
      ∀ cell, ∀ hcellRelevant :
          cell ∈ data.lineHitRelevantCells center spatialRadius,
        ∀ point ∈
          data.cellLineHitRegion cell ∩
            Metric.closedBall center spatialRadius,
          dist
              (inner ℝ (point - center) (planeMap center))
              (inner ℝ (point - center)
                (planeMap (cells.cellRep cell
                  ((Finset.mem_filter.mp hcellRelevant).1)))) ≤
            normalError)
    (localBound : ENNReal)
    (hlocal : ∀ cell, ∀ hcell : cell ∈ cells.activeCells,
      ∀ parameter ∈
        (data.cellCertificates.cellData ⟨cell, hcell⟩).lineParameters,
        (↑(Metric.externalCoveringNumber (Real.toNNReal queryScale)
          (scalarProjection
            (planeMap (cells.cellRep cell hcell))
            ((prepared.refined.shading.union ∩
                wz1PaperGridCube sqrtScale cell) ∩
              Metric.closedBall
                ((data.cellCertificates.cellData
                  ⟨cell, hcell⟩).anchor +
                    parameter • planeMap (cells.cellRep cell hcell))
                (intervalScale : ℝ)))) : ENNReal) ≤ localBound) :
    PureWZ2IntervalCoveringAt (data.lineHitCandidate hdelta) planeMap
      queryScale (Real.toNNReal queryScale) intervalScale
      ((2 * Nat.ceil ((delta * Real.sqrt 3) /
          queryScale) + 2 : ENNReal) *
        (5 *
          ((2 * Nat.ceil (normalError / queryScale) + 2 :
              ENNReal) *
            ((neighborBudget : ENNReal) *
              (5 * (4 * (9 * localBound))))))) := by
  let regionBound : ENNReal :=
    (2 * Nat.ceil (normalError / queryScale) + 2 :
        ENNReal) *
      ((neighborBudget : ENNReal) * (5 * (4 * (9 * localBound))))
  have hcell : ∀ cell, ∀ hcell : cell ∈ cells.activeCells,
      ∀ intervalCenter : ℝ,
        (↑(Metric.externalCoveringNumber (Real.toNNReal queryScale)
          ((scalarProjection
              (planeMap (cells.cellRep cell hcell))
              (data.cellLineHitRegion cell)) ∩
            Metric.closedBall intervalCenter (intervalScale : ℝ))) : ENNReal) ≤
          4 * (9 * localBound) := by
    intro cell hcell intervalCenter
    rw [data.cellLineHitRegion_eq cell hcell]
    exact (data.lineHits ⟨cell, hcell⟩).region_interval_covering
      (data.cellCertificates.cellData ⟨cell, hcell⟩) hquery hinterval
      hqueryInterval localBound (hlocal cell hcell) intervalCenter
  have hregion : ∀ center : Point3, ∀ intervalCenter : ℝ,
      (↑(Metric.externalCoveringNumber (Real.toNNReal queryScale)
        ((scalarProjection (planeMap center)
            (data.lineHitRegion ∩ Metric.closedBall center spatialRadius)) ∩
          Metric.closedBall intervalCenter (intervalScale : ℝ))) : ENNReal) ≤
        regionBound := by
    intro center intervalCenter
    exact data.lineHitRegion_interval_covering hquery hinterval
      hnormalError hnormalErrorInterval neighborBudget hneighbor hcentered
      (4 * (9 * localBound)) hcell center intervalCenter
  have hqueryNN : 0 < (Real.toNNReal queryScale : ℝ) := by
    simpa [Real.toNNReal_of_nonneg hquery.le] using hquery
  have hqueryCoe : (Real.toNNReal queryScale : ℝ) = queryScale := by
    exact Real.coe_toNNReal _ hquery.le
  have hfinal := data.lineHitCandidate_interval_covering hdelta
    (resolutionScale := Real.toNNReal queryScale)
    (intervalScale := intervalScale) hqueryNN hinterval hhullInterval
    hspatialRadius hplaneUnit regionBound hregion
  simpa only [hqueryCoe, regionBound] using hfinal

theorem lineHitCandidate_local_ad
    (data : Proposition63OneScaleFullGrainCandidateData planeMap original
      prepared cells lineVolume coverBudget)
    (hdelta : 0 < delta) :
    ∀ point ∈ (data.lineHitCandidate hdelta).union,
      IsADSet1
        (scalarProjection (planeMap point)
          ((data.lineHitCandidate hdelta).union ∩
            Metric.closedBall point (Real.sqrt queryScale)))
        queryScale (1 - sigma)
        (Kakeya.realRpowENN delta (-secondLoss)) := by
  intro point hpoint
  have hunionSubset : (data.lineHitCandidate hdelta).union ⊆
      prepared.refined.shading.union := by
    rintro other ⟨index, hindex⟩
    exact ⟨index, data.lineHitCandidate_subshading hdelta index hindex⟩
  have hsetSubset :
      scalarProjection (planeMap point)
          ((data.lineHitCandidate hdelta).union ∩
            Metric.closedBall point (Real.sqrt queryScale)) ⊆
        scalarProjection (planeMap point)
          (prepared.refined.shading.union ∩
            Metric.closedBall point (Real.sqrt queryScale)) := by
    rintro value ⟨other, hother, rfl⟩
    exact ⟨other, ⟨hunionSubset hother.1, hother.2⟩, rfl⟩
  exact (prepared.refined.local_ad point (hunionSubset hpoint)).mono
    hsetSubset

theorem lineHitCandidate_variation
    (data : Proposition63OneScaleFullGrainCandidateData planeMap original
      prepared cells lineVolume coverBudget)
    (hdelta : 0 < delta)
    (coefficient : NNReal) (hlipschitz : LipschitzWith coefficient planeMap)
    (spatialScale variationScale : ℝ)
    (hbudget : (coefficient : ℝ) * spatialScale ≤ variationScale) :
    ∀ first ∈ (data.lineHitCandidate hdelta).union,
      ∀ second ∈ (data.lineHitCandidate hdelta).union,
        dist first second ≤ spatialScale →
          dist (planeMap first) (planeMap second) ≤ variationScale := by
  intro first _ second _ hdistance
  exact (hlipschitz.dist_le_mul first second).trans <|
    (mul_le_mul_of_nonneg_left hdistance coefficient.coe_nonneg).trans
      hbudget

/-- Multiplicative mass ledger for the genuine line-hit candidate.  No
division cancellation or hidden small-scale absorption is used. -/
theorem lineHitCandidate_mass_ledger
    (data : Proposition63OneScaleFullGrainCandidateData planeMap original
      prepared cells lineVolume coverBudget)
    (hdelta : 0 < delta) (hqueryScale : 0 < queryScale)
    (hsqrtScale : 0 < sqrtScale) :
    let lineFactor :=
      ENNReal.ofReal (lineVolume / (4 * (2 * sqrtScale) ^ 2))
    let threshold :=
      (cells.cellMass / 2) / (2 * (coverBudget : ENNReal))
    lineFactor * threshold * prepared.refined.shading.mass ≤
      (2 * cells.cellMass * ENNReal.ofReal (4 * queryScale)) *
        (data.lineHitCandidate hdelta).mass := by
  dsimp only
  let exactLineHit := paperRestrictShadingToSet
    prepared.refined.shading data.lineHitRegion data.lineHitRegion_measurable
  have hexactUnion : exactLineHit.union = data.lineHitRegion := by
    ext point
    constructor
    · rintro ⟨index, hpoint⟩
      exact hpoint.2
    · intro hpoint
      rcases data.lineHitRegion_subset hpoint with ⟨index, hindex⟩
      exact ⟨index, hindex, hpoint⟩
  have hexactMassLower :
      (2 ^ prepared.level : ENNReal) * volume data.lineHitRegion ≤
        exactLineHit.mass := by
    rw [← hexactUnion]
    apply Kakeya.Assouad.multiplicity_floor_le_mass
    intro point hpoint
    have hpointRegion : point ∈ data.lineHitRegion := by
      rw [← hexactUnion]
      exact hpoint
    change (2 ^ prepared.level : ENNReal) ≤
      (paperRestrictShadingToSet prepared.refined.shading
        data.lineHitRegion data.lineHitRegion_measurable).pointMultiplicity
        point
    rw [paperPmRestrictShadingToSet data.lineHitRegion_measurable
      hpointRegion]
    exact prepared.multiplicity_lower point
      (data.lineHitRegion_subset hpointRegion)
  have hexactLeCandidate : exactLineHit.mass ≤
      (data.lineHitCandidate hdelta).mass := by
    apply Finset.sum_le_sum
    intro index _
    apply measure_mono
    intro point hpoint
    refine ⟨hpoint.1, ?_⟩
    have hpointCandidate :=
      data.lineHitRegion_subset_candidate_union hdelta hpoint.2
    rw [lineHitCandidate, wz2RefinedShading_union_inter] at hpointCandidate
    exact hpointCandidate.2
  have htargetLower :
      (2 ^ prepared.level : ENNReal) * volume data.lineHitRegion ≤
        (data.lineHitCandidate hdelta).mass :=
    hexactMassLower.trans hexactLeCandidate
  have hsourceUpper : prepared.refined.shading.mass ≤
      (2 * (2 ^ prepared.level : ENNReal)) *
        volume prepared.refined.shading.union :=
    Kakeya.Assouad.mass_le_multiplicity_vol
      (ENNReal.mul_ne_top (by norm_num) (by simp))
      prepared.multiplicity_upper
  have hsourceVolume := cells.fine_union_volume
  have hregion := data.lineHitRegion_volume_lower hqueryScale
  rw [hsourceVolume] at hsourceUpper
  calc
    ENNReal.ofReal (lineVolume / (4 * (2 * sqrtScale) ^ 2)) *
          ((cells.cellMass / 2) /
            (2 * (coverBudget : ENNReal))) *
          prepared.refined.shading.mass
        ≤ ENNReal.ofReal (lineVolume / (4 * (2 * sqrtScale) ^ 2)) *
          ((cells.cellMass / 2) /
            (2 * (coverBudget : ENNReal))) *
          ((2 * (2 ^ prepared.level : ENNReal)) *
            ((cells.activeCells.card : ENNReal) * cells.cellMass)) :=
      mul_le_mul_left' hsourceUpper _
    _ = (2 * cells.cellMass * (2 ^ prepared.level : ENNReal)) *
          ((cells.activeCells.card : ENNReal) *
            (ENNReal.ofReal (lineVolume / (4 * (2 * sqrtScale) ^ 2)) *
              ((cells.cellMass / 2) /
                (2 * (coverBudget : ENNReal))))) := by ring
    _ ≤ (2 * cells.cellMass * (2 ^ prepared.level : ENNReal)) *
          (ENNReal.ofReal (4 * queryScale) * volume data.lineHitRegion) :=
      mul_le_mul_left' hregion _
    _ = (2 * cells.cellMass * ENNReal.ofReal (4 * queryScale)) *
          ((2 ^ prepared.level : ENNReal) * volume data.lineHitRegion) := by
      ring
    _ ≤ (2 * cells.cellMass * ENNReal.ofReal (4 * queryScale)) *
          (data.lineHitCandidate hdelta).mass :=
      mul_le_mul_left' htargetLower _

/-- Combine the explicit multiplicity/balancing preparation loss with the
geometric line-hit ledger. -/
theorem lineHitCandidate_mass_from_original
    (data : Proposition63OneScaleFullGrainCandidateData planeMap original
      prepared cells lineVolume coverBudget)
    (hdelta : 0 < delta) (hqueryScale : 0 < queryScale)
    (hsqrtScale : 0 < sqrtScale) :
    let lineFactor :=
      ENNReal.ofReal (lineVolume / (4 * (2 * sqrtScale) ^ 2))
    let threshold :=
      (cells.cellMass / 2) / (2 * (coverBudget : ENNReal))
    let preparationLoss := prepared.preparationLoss
    lineFactor * threshold * original.shading.mass ≤
      (preparationLoss *
          (2 * cells.cellMass * ENNReal.ofReal (4 * queryScale))) *
        (data.lineHitCandidate hdelta).mass := by
  dsimp only
  have hpreparedMass : original.shading.mass ≤
      prepared.refined.shading.mass * prepared.preparationLoss := by
    simpa [mul_comm] using prepared.mass_retention
  have hlineHit := data.lineHitCandidate_mass_ledger
    hdelta hqueryScale hsqrtScale
  calc
    ENNReal.ofReal (lineVolume / (4 * (2 * sqrtScale) ^ 2)) *
          ((cells.cellMass / 2) /
            (2 * (coverBudget : ENNReal))) * original.shading.mass
        ≤ ENNReal.ofReal (lineVolume / (4 * (2 * sqrtScale) ^ 2)) *
          ((cells.cellMass / 2) /
            (2 * (coverBudget : ENNReal))) *
          (prepared.refined.shading.mass * prepared.preparationLoss) :=
      mul_le_mul_left' hpreparedMass _
    _ = (ENNReal.ofReal (lineVolume / (4 * (2 * sqrtScale) ^ 2)) *
          ((cells.cellMass / 2) /
            (2 * (coverBudget : ENNReal))) *
          prepared.refined.shading.mass) * prepared.preparationLoss := by ring
    _ ≤ ((2 * cells.cellMass * ENNReal.ofReal (4 * queryScale)) *
          (data.lineHitCandidate hdelta).mass) * prepared.preparationLoss :=
      mul_le_mul_right' hlineHit prepared.preparationLoss
    _ = (prepared.preparationLoss *
          (2 * cells.cellMass * ENNReal.ofReal (4 * queryScale))) *
        (data.lineHitCandidate hdelta).mass := by ac_rfl

/-- Compose an incoming current-to-one-scale mass comparison with the exact
line-hit loss.  This is the multiplicative orientation expected by the finite
iterator's `candidateStep`. -/
theorem lineHitCandidate_mass_from_current
    (data : Proposition63OneScaleFullGrainCandidateData planeMap original
      prepared cells lineVolume coverBudget)
    {currentDelta : ℝ}
    {currentFamily : Kakeya.Streamlined.TubeFamily currentDelta}
    {current : WZ1PaperTubeShading currentFamily}
    (leftFactor rightFactor : ENNReal)
    (hincoming : leftFactor * current.mass ≤
      rightFactor * original.shading.mass)
    (hdelta : 0 < delta) (hqueryScale : 0 < queryScale)
    (hsqrtScale : 0 < sqrtScale) :
    let lineFactor :=
      ENNReal.ofReal (lineVolume / (4 * (2 * sqrtScale) ^ 2))
    let threshold :=
      (cells.cellMass / 2) / (2 * (coverBudget : ENNReal))
    let preparationLoss := prepared.preparationLoss
    let geometryFactor :=
      2 * cells.cellMass * ENNReal.ofReal (4 * queryScale)
    (lineFactor * threshold * leftFactor) * current.mass ≤
      (rightFactor * (preparationLoss * geometryFactor)) *
        (data.lineHitCandidate hdelta).mass := by
  dsimp only
  have hretention := data.lineHitCandidate_mass_from_original
    hdelta hqueryScale hsqrtScale
  calc
    (ENNReal.ofReal (lineVolume / (4 * (2 * sqrtScale) ^ 2)) *
          ((cells.cellMass / 2) /
            (2 * (coverBudget : ENNReal))) * leftFactor) * current.mass
        = ENNReal.ofReal (lineVolume / (4 * (2 * sqrtScale) ^ 2)) *
          ((cells.cellMass / 2) /
            (2 * (coverBudget : ENNReal))) *
          (leftFactor * current.mass) := by ac_rfl
    _ ≤ ENNReal.ofReal (lineVolume / (4 * (2 * sqrtScale) ^ 2)) *
          ((cells.cellMass / 2) /
            (2 * (coverBudget : ENNReal))) *
          (rightFactor * original.shading.mass) :=
      mul_le_mul_left' hincoming _
    _ = rightFactor *
          (ENNReal.ofReal (lineVolume / (4 * (2 * sqrtScale) ^ 2)) *
            ((cells.cellMass / 2) /
              (2 * (coverBudget : ENNReal))) * original.shading.mass) := by
      ac_rfl
    _ ≤ rightFactor *
          ((prepared.preparationLoss *
              (2 * cells.cellMass * ENNReal.ofReal (4 * queryScale))) *
            (data.lineHitCandidate hdelta).mass) :=
      mul_le_mul_left' hretention rightFactor
    _ = (rightFactor *
          (prepared.preparationLoss *
            (2 * cells.cellMass * ENNReal.ofReal (4 * queryScale)))) *
        (data.lineHitCandidate hdelta).mass := by ac_rfl

/-- Cancel the balanced-cell mass from the genuine line-hit ledger.  This is
legitimate because the cell data records that its common mass is both
positive and finite.  The remaining loss depends only on the chosen covering
budget, the query scale, and the fixed ambient-family logarithm. -/
theorem lineHitCandidate_mass_from_current_cancel_cellMass
    (data : Proposition63OneScaleFullGrainCandidateData planeMap original
      prepared cells lineVolume coverBudget)
    {currentDelta : ℝ}
    {currentFamily : Kakeya.Streamlined.TubeFamily currentDelta}
    {current : WZ1PaperTubeShading currentFamily}
    (leftFactor rightFactor : ENNReal)
    (hincoming : leftFactor * current.mass ≤
      rightFactor * original.shading.mass)
    (hdelta : 0 < delta) (hqueryScale : 0 < queryScale)
    (hsqrtScale : 0 < sqrtScale) :
    let lineFactor :=
      ENNReal.ofReal (lineVolume / (4 * (2 * sqrtScale) ^ 2))
    let inverseCoverFactor :=
      ((1 : ENNReal) / 2) / (2 * (coverBudget : ENNReal))
    let preparationLoss := prepared.preparationLoss
    let queryFactor := ENNReal.ofReal (4 * queryScale)
    (lineFactor * inverseCoverFactor * leftFactor) * current.mass ≤
      (rightFactor * (preparationLoss * (2 * queryFactor))) *
        (data.lineHitCandidate hdelta).mass := by
  dsimp only
  have hscaled := data.lineHitCandidate_mass_from_current
    leftFactor rightFactor hincoming hdelta hqueryScale hsqrtScale
  apply (ENNReal.mul_le_mul_iff_left cells.cellMass_pos.ne'
    cells.cellMass_ne_top).mp
  calc
    ((ENNReal.ofReal (lineVolume / (4 * (2 * sqrtScale) ^ 2)) *
            (((1 : ENNReal) / 2) /
              (2 * (coverBudget : ENNReal))) * leftFactor) * current.mass) *
          cells.cellMass =
        (ENNReal.ofReal (lineVolume / (4 * (2 * sqrtScale) ^ 2)) *
            ((cells.cellMass / 2) /
              (2 * (coverBudget : ENNReal))) * leftFactor) * current.mass := by
      simp only [div_eq_mul_inv]
      ring
    _ ≤ (rightFactor *
          (prepared.preparationLoss *
            (2 * cells.cellMass * ENNReal.ofReal (4 * queryScale)))) *
        (data.lineHitCandidate hdelta).mass := hscaled
    _ = ((rightFactor *
            (prepared.preparationLoss *
              (2 * ENNReal.ofReal (4 * queryScale)))) *
          (data.lineHitCandidate hdelta).mass) * cells.cellMass := by
      ring

/-- Package the genuine line-hit candidate directly in the shape consumed by
one step of the finite Lemma 4.11/4.12 iterator. -/
theorem lineHitCandidate_for_iteration
    (data : Proposition63OneScaleFullGrainCandidateData planeMap original
      prepared cells lineVolume coverBudget)
    (hdelta : 0 < delta) (hqueryScale : 0 < queryScale)
    (hsqrtScale : 0 < sqrtScale)
    (coefficient : NNReal) (hlipschitz : LipschitzWith coefficient planeMap)
    (spatialScale variationScale : ℝ)
    (hbudget : (coefficient : ℝ) * spatialScale ≤ variationScale) :
    ∃ candidate : WZ1PaperTubeShading family,
      PaperIsSubshading candidate source ∧
      WZ1PaperIsCubicalShading candidate ∧
      (∀ first ∈ candidate.union, ∀ second ∈ candidate.union,
        dist first second ≤ spatialScale →
          dist (planeMap first) (planeMap second) ≤ variationScale) ∧
      (∀ point ∈ candidate.union,
        IsADSet1
          (scalarProjection (planeMap point)
            (candidate.union ∩ Metric.closedBall point
              (Real.sqrt queryScale)))
          queryScale (1 - sigma)
          (Kakeya.realRpowENN delta (-secondLoss))) ∧
      ENNReal.ofReal (lineVolume / (4 * (2 * sqrtScale) ^ 2)) *
          ((cells.cellMass / 2) /
            (2 * (coverBudget : ENNReal))) * original.shading.mass ≤
        ((prepared.preparationLoss *
            (2 * cells.cellMass * ENNReal.ofReal (4 * queryScale))) *
          candidate.mass) := by
  exact ⟨data.lineHitCandidate hdelta,
    data.lineHitCandidate_subshading_source hdelta,
    data.lineHitCandidate_cubical hdelta,
    data.lineHitCandidate_variation hdelta coefficient hlipschitz
      spatialScale variationScale hbudget,
    data.lineHitCandidate_local_ad hdelta,
    data.lineHitCandidate_mass_from_original hdelta hqueryScale hsqrtScale⟩

/-- Exact combined loss ledger: the explicit preparation loss followed by
the constant-factor full-grain selection. -/
theorem candidate_mass_retention
    (data : Proposition63OneScaleFullGrainCandidateData planeMap original
      prepared cells lineVolume coverBudget)
    (hdelta : 0 < delta) (hsqrtScale : 0 < sqrtScale) :
    original.shading.mass ≤
      prepared.preparationLoss * (4 * (data.candidate hdelta).mass) := by
  exact prepared.mass_retention.trans <|
    mul_le_mul_left'
      (data.cellCertificates.cubicalRetainedShading_quarter_mass hdelta hsqrtScale
        (2 ^ prepared.level : ENNReal) (by simp)
        prepared.multiplicity_lower prepared.multiplicity_upper)
      prepared.preparationLoss

end Proposition63OneScaleFullGrainCandidateData

end Kakeya.Assouad.PureWZ2

end
