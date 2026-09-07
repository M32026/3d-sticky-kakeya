import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63NestedPointCover

/-!
# The paper line-hit candidate for Proposition 6.3

This file keeps the paper region indexed by every parameter of the Fubini
line, rather than only by the auxiliary maximal separated set.  The latter is
used only as a finite bookkeeping device in the volume proof.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory Set ENNReal Metric

attribute [local instance] Classical.propDecidable

namespace Proposition63NestedPointCoverData.FullGrainCells

variable
    {delta sigma inputLoss normalizationLoss firstLoss reentryLoss
      sqrtStickyLoss secondLoss finalLoss queryScale tauScale sqrtScale : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma inputLoss delta}
    {normalizationExponent : ℕ}
    {initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) source normalizationExponent}
    {planeMap : Point3 → Point3} {tauConstant sqrtConstant : ENNReal}
    {data : Proposition63NestedPointCoverData
      (firstLoss := firstLoss) (reentryLoss := reentryLoss)
      (sqrtStickyLoss := sqrtStickyLoss) (secondLoss := secondLoss)
      (finalLoss := finalLoss) (queryScale := queryScale)
      (tauScale := tauScale) (sqrtScale := sqrtScale)
      initialNormalized planeMap tauConstant sqrtConstant}
    {lineVolume : ℝ} {coverBudget : ℕ}

/-- The literal paper region in one active square-root cell: all full grains
whose central level is met by the selected Fubini line. -/
def paperCellRegion
    (full : data.FullGrainCells lineVolume coverBudget)
    (cell : {cell // cell ∈ data.cells.activeCells}) : Set Point3 :=
  ⋃ parameter ∈ (full.cellData cell).lineParameters,
    (full.cellData cell).good ∩ {point |
      |inner ℝ point (planeMap (data.cells.cellRep cell.1 cell.2)) -
        inner ℝ ((full.cellData cell).anchor +
          parameter • planeMap (data.cells.cellRep cell.1 cell.2))
          (planeMap (data.cells.cellRep cell.1 cell.2))| ≤ queryScale}

theorem paperCellRegion_subset_good
    (full : data.FullGrainCells lineVolume coverBudget)
    (cell : {cell // cell ∈ data.cells.activeCells}) :
    full.paperCellRegion cell ⊆ (full.cellData cell).good := by
  rintro point hpoint
  rcases Set.mem_iUnion₂.mp hpoint with ⟨parameter, _, hgrain⟩
  exact hgrain.1

theorem selectedRegion_subset_paperCellRegion
    (full : data.FullGrainCells lineVolume coverBudget)
    (cell : {cell // cell ∈ data.cells.activeCells}) :
    (full.lineHits cell).region ⊆ full.paperCellRegion cell := by
  rintro point hpoint
  rcases Set.mem_iUnion₂.mp hpoint with ⟨parameter, hparameter, hgrain⟩
  exact Set.mem_iUnion₂.mpr
    ⟨parameter, (full.lineHits cell).parameters_mem hparameter, hgrain⟩

/-- Cellwise mass ledger with the arbitrary `lineVolume` eliminated.  The
left side is exactly `volume good * threshold`; the two right-hand factors
are the Fubini cross-sectional area and the one-dimensional packing cost. -/
theorem paperCellRegion_relative_mass
    (full : data.FullGrainCells lineVolume coverBudget)
    (cell : {cell // cell ∈ data.cells.activeCells})
    (hquery : 0 < queryScale) :
    volume (full.cellData cell).good *
        ((data.cells.cellMass / 2) / (2 * (coverBudget : ENNReal))) ≤
      (ENNReal.ofReal (4 * (2 * sqrtScale) ^ 2) *
        ENNReal.ofReal (4 * queryScale)) *
        volume (full.paperCellRegion cell) := by
  let cellData := full.cellData cell
  let hit := full.lineHits cell
  have hparameters := hit.parameters_volume_cover cellData hquery
  have hselectedMass := hit.region_volume_lower cellData
  have hselectedSubset : hit.region ⊆ full.paperCellRegion cell :=
    full.selectedRegion_subset_paperCellRegion cell
  calc
    volume cellData.good *
          ((data.cells.cellMass / 2) / (2 * (coverBudget : ENNReal))) ≤
        (ENNReal.ofReal (4 * (2 * sqrtScale) ^ 2) *
          volume cellData.lineParameters) *
          ((data.cells.cellMass / 2) / (2 * (coverBudget : ENNReal))) :=
      mul_le_mul_left cellData.relative_line_volume _
    _ ≤ (ENNReal.ofReal (4 * (2 * sqrtScale) ^ 2) *
          ((hit.parameters.card : ENNReal) *
            ENNReal.ofReal (4 * queryScale))) *
          ((data.cells.cellMass / 2) / (2 * (coverBudget : ENNReal))) :=
      mul_le_mul_left (mul_le_mul_right hparameters _) _
    _ = (ENNReal.ofReal (4 * (2 * sqrtScale) ^ 2) *
          ENNReal.ofReal (4 * queryScale)) *
          ((hit.parameters.card : ENNReal) *
            ((data.cells.cellMass / 2) /
              (2 * (coverBudget : ENNReal)))) := by ring
    _ ≤ (ENNReal.ofReal (4 * (2 * sqrtScale) ^ 2) *
          ENNReal.ofReal (4 * queryScale)) * volume hit.region :=
      mul_le_mul_right hselectedMass _
    _ ≤ (ENNReal.ofReal (4 * (2 * sqrtScale) ^ 2) *
          ENNReal.ofReal (4 * queryScale)) *
          volume (full.paperCellRegion cell) :=
      mul_le_mul_right (measure_mono hselectedSubset) _

/-- Stronger bookkeeping form of `paperCellRegion_relative_mass`, retaining
the finite separated subregion on the right. -/
theorem selectedCellRegion_relative_mass
    (full : data.FullGrainCells lineVolume coverBudget)
    (cell : {cell // cell ∈ data.cells.activeCells})
    (hquery : 0 < queryScale) :
    volume (full.cellData cell).good *
        ((data.cells.cellMass / 2) / (2 * (coverBudget : ENNReal))) ≤
      (ENNReal.ofReal (4 * (2 * sqrtScale) ^ 2) *
        ENNReal.ofReal (4 * queryScale)) *
        volume (full.lineHits cell).region := by
  let cellData := full.cellData cell
  let hit := full.lineHits cell
  calc
    volume cellData.good *
          ((data.cells.cellMass / 2) / (2 * (coverBudget : ENNReal))) ≤
        (ENNReal.ofReal (4 * (2 * sqrtScale) ^ 2) *
          volume cellData.lineParameters) *
          ((data.cells.cellMass / 2) / (2 * (coverBudget : ENNReal))) :=
      mul_le_mul_left cellData.relative_line_volume _
    _ ≤ (ENNReal.ofReal (4 * (2 * sqrtScale) ^ 2) *
          ((hit.parameters.card : ENNReal) *
            ENNReal.ofReal (4 * queryScale))) *
          ((data.cells.cellMass / 2) / (2 * (coverBudget : ENNReal))) :=
      mul_le_mul_left
        (mul_le_mul_right (hit.parameters_volume_cover cellData hquery) _) _
    _ = (ENNReal.ofReal (4 * (2 * sqrtScale) ^ 2) *
          ENNReal.ofReal (4 * queryScale)) *
          ((hit.parameters.card : ENNReal) *
            ((data.cells.cellMass / 2) /
              (2 * (coverBudget : ENNReal)))) := by ring
    _ ≤ (ENNReal.ofReal (4 * (2 * sqrtScale) ^ 2) *
          ENNReal.ofReal (4 * queryScale)) * volume hit.region :=
      mul_le_mul_right (hit.region_volume_lower cellData) _

/-- Interval covering for the literal all-parameter paper region.  The
finite set here is selected afresh from the parameters relevant to the
queried interval; it does not alter the definition of the region. -/
theorem paperCellRegion_interval_covering
    (full : data.FullGrainCells lineVolume coverBudget)
    (cell : {cell // cell ∈ data.cells.activeCells})
    {tau : ℝ} (hquery : 0 < queryScale) (htau : 0 < tau)
    (hqueryTau : queryScale ≤ tau)
    (bound : ENNReal)
    (hlocal : ∀ parameter ∈ (full.cellData cell).lineParameters,
      (Metric.externalCoveringNumber (Real.toNNReal queryScale)
        (scalarProjection (planeMap (data.cells.cellRep cell.1 cell.2))
          ((data.prepared.refined.shading.union ∩
              wz1PaperGridCube sqrtScale cell.1) ∩ Metric.closedBall
            ((full.cellData cell).anchor + parameter •
              planeMap (data.cells.cellRep cell.1 cell.2)) tau)) : ENNReal) ≤
        bound) :
    ∀ intervalCenter : ℝ,
      (Metric.externalCoveringNumber (Real.toNNReal queryScale)
        (scalarProjection (planeMap (data.cells.cellRep cell.1 cell.2))
            (full.paperCellRegion cell) ∩
          Metric.closedBall intervalCenter tau) : ENNReal) ≤
        4 * (9 * bound) := by
  intro intervalCenter
  let cellData := full.cellData cell
  let normal := planeMap (data.cells.cellRep cell.1 cell.2)
  let E := data.prepared.refined.shading.union ∩
    wz1PaperGridCube sqrtScale cell.1
  let offset := inner ℝ cellData.anchor normal
  let intervalParameters := cellData.lineParameters ∩
    Metric.closedBall (intervalCenter - offset) (2 * tau)
  have hintervalSubset : intervalParameters ⊆
      Metric.closedBall (intervalCenter - offset) (2 * tau) :=
    Set.inter_subset_right
  rcases Kakeya.Assouad.real_subset_self_centered_cover
      htau (by positivity : 0 < 2 * tau) hintervalSubset with
    ⟨selected, hselectedParameters, hselectedCard, hselectedCover⟩
  have hcardNine : (selected.card : ENNReal) ≤ 9 := by
    have hceil : Nat.ceil (4 * (2 * tau) / tau) = 8 := by
      have htauNe : tau ≠ 0 := htau.ne'
      have hratio : 4 * (2 * tau) / tau = (8 : ℝ) := by
        field_simp [htauNe]
        ring
      rw [hratio]
      norm_num
    rw [hceil] at hselectedCard
    norm_num at hselectedCard ⊢
    exact hselectedCard
  let linePoint : ℝ → Point3 := fun parameter =>
    cellData.anchor + parameter • normal
  let localProjection : ℝ → Set ℝ := fun parameter =>
    scalarProjection normal (E ∩ Metric.closedBall (linePoint parameter) tau)
  let sourceSet : Set ℝ :=
    ⋃ parameter ∈ selected, localProjection parameter
  have hlocalCover : ∀ parameter ∈ selected,
      (Metric.externalCoveringNumber (Real.toNNReal queryScale)
        (localProjection parameter) : ENNReal) ≤ bound := by
    intro parameter hparameter
    exact hlocal parameter (hselectedParameters hparameter).1
  have hsourceCover :
      (Metric.externalCoveringNumber (Real.toNNReal queryScale) sourceSet :
          ENNReal) ≤ 9 * bound := by
    have hunion := Kakeya.Assouad.externalCoveringNumber_biUnion_le_card
      (ε := Real.toNNReal queryScale) (s := selected)
      (A := localProjection) hlocalCover
    exact hunion.trans <| by gcongr
  have htargetSubset :
      scalarProjection normal (full.paperCellRegion cell) ∩
          Metric.closedBall intervalCenter tau ⊆
        Metric.cthickening queryScale sourceSet := by
    intro value hvalue
    rcases hvalue.1 with ⟨point, hpointRegion, rfl⟩
    rcases Set.mem_iUnion₂.mp hpointRegion with
      ⟨parameter, hparameterLine, hpointGrain⟩
    have hparameterInterval : parameter ∈
        Metric.closedBall (intervalCenter - offset) (2 * tau) := by
      have hvalueInterval := hvalue.2
      rw [Metric.mem_closedBall, Real.dist_eq] at hvalueInterval ⊢
      have hprojection : inner ℝ (linePoint parameter) normal =
          offset + parameter := by
        dsimp only [linePoint, offset, normal, cellData]
        rw [inner_add_left, real_inner_smul_left,
          real_inner_self_eq_norm_sq, (full.cellData cell).normal_unit]
        norm_num
      have hgrain := hpointGrain.2
      change |inner ℝ point normal - inner ℝ (linePoint parameter) normal| ≤
        queryScale at hgrain
      rw [hprojection] at hgrain
      calc
        |parameter - (intervalCenter - offset)| =
            |((offset + parameter) - inner ℝ point normal) +
              (inner ℝ point normal - intervalCenter)| := by ring_nf
        _ ≤ |(offset + parameter) - inner ℝ point normal| +
              |inner ℝ point normal - intervalCenter| := abs_add_le _ _
        _ ≤ queryScale + tau := by
          exact add_le_add (by simpa [abs_sub_comm] using hgrain)
            hvalueInterval
        _ ≤ 2 * tau := by linarith
    have hparameterIn : parameter ∈ intervalParameters :=
      ⟨hparameterLine, hparameterInterval⟩
    rcases Set.mem_iUnion₂.mp (hselectedCover hparameterIn) with
      ⟨selectedParameter, hselectedParameter, hparameterBall⟩
    have hlineBall : linePoint parameter ∈
        Metric.closedBall (linePoint selectedParameter) tau := by
      change dist
        (Kakeya.Assouad.wz1Lemma18LinePoint cellData.anchor normal parameter)
        (Kakeya.Assouad.wz1Lemma18LinePoint cellData.anchor normal
          selectedParameter) ≤ tau
      rw [Kakeya.Assouad.wz1Lemma18LinePoint_dist cellData.anchor normal
        parameter selectedParameter cellData.normal_unit]
      exact hparameterBall
    let sourceValue := inner ℝ (linePoint parameter) normal
    have hsourceValue : sourceValue ∈ sourceSet := by
      exact Set.mem_iUnion₂.mpr
        ⟨selectedParameter, hselectedParameter,
          ⟨linePoint parameter,
            ⟨cellData.good_subset hparameterLine, hlineBall⟩, rfl⟩⟩
    have hdistance : dist (inner ℝ point normal) sourceValue ≤ queryScale := by
      rw [Real.dist_eq]
      simpa [sourceValue, linePoint] using hpointGrain.2
    exact Metric.mem_cthickening_of_dist_le
      (inner ℝ point normal) sourceValue queryScale sourceSet
      hsourceValue hdistance
  have hthick := Kakeya.Assouad.externalCoveringNumber_of_subset_cthickening
    hquery hquery htargetSubset hsourceCover
  have hfactor :
      (2 * Nat.ceil (queryScale / queryScale) + 2 : ENNReal) = 4 := by
    have hqueryNe : queryScale ≠ 0 := hquery.ne'
    have hratio : queryScale / queryScale = (1 : ℝ) := by
      field_simp [hqueryNe]
    rw [hratio]
    norm_num
  simpa only [hfactor] using hthick

/-- The paper region, unioned over all active square-root cells. -/
def paperRegion
    (full : data.FullGrainCells lineVolume coverBudget) : Set Point3 :=
  ⋃ cell ∈ data.cells.activeCells, full.paperCellRegion ⟨cell, by assumption⟩

theorem paperRegion_subset
    (full : data.FullGrainCells lineVolume coverBudget) :
    full.paperRegion ⊆ data.prepared.refined.shading.union := by
  rintro point hpoint
  rcases Set.mem_iUnion₂.mp hpoint with ⟨cell, hcell, hpointCell⟩
  exact (full.cellData ⟨cell, hcell⟩).good_subset
    (full.paperCellRegion_subset_good ⟨cell, hcell⟩ hpointCell) |>.1

theorem selectedRegion_subset_paperRegion
    (full : data.FullGrainCells lineVolume coverBudget) :
    full.lineHitRegion ⊆ full.paperRegion := by
  rintro point hpoint
  rcases Set.mem_iUnion₂.mp hpoint with ⟨cell, hcell, hpointCell⟩
  rw [full.cellLineHitRegion_eq cell hcell] at hpointCell
  exact Set.mem_iUnion₂.mpr
    ⟨cell, hcell, full.selectedRegion_subset_paperCellRegion
      ⟨cell, hcell⟩ hpointCell⟩

def paperRelevantCells
    (full : data.FullGrainCells lineVolume coverBudget)
    (center : Point3) (radius : ℝ) : Finset (ℤ × ℤ × ℤ) :=
  data.cells.activeCells.filter fun cell =>
    if hcell : cell ∈ data.cells.activeCells then
      (full.paperCellRegion ⟨cell, hcell⟩ ∩
        Metric.closedBall center radius).Nonempty
    else False

theorem paperCellRegion_subset_cell
    (full : data.FullGrainCells lineVolume coverBudget)
    (cell : {cell // cell ∈ data.cells.activeCells}) :
    full.paperCellRegion cell ⊆ wz1PaperGridCube sqrtScale cell.1 :=
  (full.paperCellRegion_subset_good cell).trans
    ((full.cellData cell).good_subset.trans Set.inter_subset_right)

/-- Finite-cell assembly of the all-parameter interval bounds. -/
theorem paperRegion_interval_covering
    (full : data.FullGrainCells lineVolume coverBudget)
    {spatialRadius resolutionScale intervalScale normalError : ℝ}
    (hresolution : 0 < resolutionScale) (hinterval : 0 < intervalScale)
    (hnormalError : 0 < normalError)
    (hnormalErrorInterval : normalError ≤ intervalScale)
    (neighborBudget : ℕ)
    (hneighbor : ∀ center,
      (full.paperRelevantCells center spatialRadius).card ≤ neighborBudget)
    (hcentered : ∀ center cell, ∀ hcellRelevant :
        cell ∈ full.paperRelevantCells center spatialRadius,
      ∀ point ∈ full.paperCellRegion
          ⟨cell, (Finset.mem_filter.mp hcellRelevant).1⟩ ∩
          Metric.closedBall center spatialRadius,
        dist (inner ℝ (point - center) (planeMap center))
          (inner ℝ (point - center)
            (planeMap (data.cells.cellRep cell
              ((Finset.mem_filter.mp hcellRelevant).1)))) ≤ normalError)
    (cellBound : ENNReal)
    (hcellBound : ∀ cell : {cell // cell ∈ data.cells.activeCells},
      ∀ intervalCenter : ℝ,
        (Metric.externalCoveringNumber (Real.toNNReal resolutionScale)
          (scalarProjection (planeMap (data.cells.cellRep cell.1 cell.2))
              (full.paperCellRegion cell) ∩
            Metric.closedBall intervalCenter intervalScale) : ENNReal) ≤
          cellBound) :
    ∀ center intervalCenter,
      (Metric.externalCoveringNumber (Real.toNNReal resolutionScale)
        (scalarProjection (planeMap center)
            (full.paperRegion ∩ Metric.closedBall center spatialRadius) ∩
          Metric.closedBall intervalCenter intervalScale) : ENNReal) ≤
        (2 * Nat.ceil (normalError / resolutionScale) + 2 : ENNReal) *
          ((neighborBudget : ENNReal) * (5 * cellBound)) := by
  intro center intervalCenter
  let relevant := full.paperRelevantCells center spatialRadius
  let piece : (ℤ × ℤ × ℤ) → Set Point3 := fun cell =>
    if hcell : cell ∈ data.cells.activeCells then
      full.paperCellRegion ⟨cell, hcell⟩ ∩ Metric.closedBall center spatialRadius
    else ∅
  let normal : (ℤ × ℤ × ℤ) → Point3 := fun cell =>
    if hcell : cell ∈ data.cells.activeCells then
      planeMap (data.cells.cellRep cell hcell) else planeMap center
  let targetSet := full.paperRegion ∩ Metric.closedBall center spatialRadius
  have hdecompose : ∀ point ∈ targetSet,
      ∃ cell ∈ relevant, point ∈ piece cell := by
    intro point hpoint
    rcases Set.mem_iUnion₂.mp hpoint.1 with ⟨cell, hactive, hpointCell⟩
    have hrelevant : cell ∈ relevant := by
      dsimp only [relevant]
      unfold paperRelevantCells
      rw [Finset.mem_filter]
      refine ⟨hactive, ?_⟩
      simp only [hactive, dite_true]
      exact ⟨point, hpointCell, hpoint.2⟩
    exact ⟨cell, hrelevant, by simp [piece, hactive, hpointCell, hpoint.2]⟩
  have hlocal : ∀ cell ∈ relevant, ∀ sourceCenter : ℝ,
      (Metric.externalCoveringNumber (Real.toNNReal resolutionScale)
        (scalarProjection (normal cell) (piece cell) ∩
          Metric.closedBall sourceCenter intervalScale) : ENNReal) ≤
        cellBound := by
    intro cell hrelevant sourceCenter
    have hactive := (Finset.mem_filter.mp hrelevant).1
    have hmono :
        (Metric.externalCoveringNumber (Real.toNNReal resolutionScale)
          (scalarProjection (planeMap (data.cells.cellRep cell hactive))
              (full.paperCellRegion ⟨cell, hactive⟩ ∩
                Metric.closedBall center spatialRadius) ∩
            Metric.closedBall sourceCenter intervalScale) : ENNReal) ≤
          (Metric.externalCoveringNumber (Real.toNNReal resolutionScale)
            (scalarProjection (planeMap (data.cells.cellRep cell hactive))
                (full.paperCellRegion ⟨cell, hactive⟩) ∩
              Metric.closedBall sourceCenter intervalScale) : ENNReal) := by
      exact_mod_cast Metric.externalCoveringNumber_mono_set
        (Set.inter_subset_inter
          (Set.image_mono Set.inter_subset_left) Set.Subset.rfl)
    simpa only [normal, piece, dif_pos hactive] using
      hmono.trans (hcellBound ⟨cell, hactive⟩ sourceCenter)
  have hraw := Kakeya.Assouad.wz1_lemma18_centered_finite_cell_interval_transfer
    relevant piece normal targetSet center (planeMap center) resolutionScale
    intervalScale normalError cellBound hresolution hinterval hnormalError
    hnormalErrorInterval hdecompose (by
      intro cell hrelevant point hpoint
      have hactive := (Finset.mem_filter.mp hrelevant).1
      have hpoint' : point ∈ full.paperCellRegion ⟨cell, hactive⟩ ∩
          Metric.closedBall center spatialRadius := by
        simpa only [piece, dif_pos hactive] using hpoint
      simpa only [normal, dif_pos hactive] using
        hcentered center cell hrelevant point hpoint') hlocal intervalCenter
  exact hraw.trans <| by gcongr; exact_mod_cast hneighbor center

/-- Cubicalization of the literal all-parameter paper region. -/
def paperCandidate
    (full : data.FullGrainCells lineVolume coverBudget)
    (hdelta : 0 < delta) :
    WZ1PaperTubeShading data.reentry.normalization.croppedFamily :=
  wz2RefinedShading data.prepared.refined.shading <|
    (wz1PaperGridIndicesInWindow delta hdelta).filter fun cell =>
      (full.paperRegion ∩ wz1PaperGridCube delta cell).Nonempty

theorem paperCandidate_subshading
    (full : data.FullGrainCells lineVolume coverBudget)
    (hdelta : 0 < delta) :
    PaperIsSubshading (full.paperCandidate hdelta)
      data.prepared.refined.shading :=
  wz2RefinedShading_subshading

theorem paperCandidate_cubical
    (full : data.FullGrainCells lineVolume coverBudget)
    (hdelta : 0 < delta) :
    WZ1PaperIsCubicalShading (full.paperCandidate hdelta) :=
  wz2RefinedShading_cubical data.prepared.refined.extremal.cubical

theorem paperCandidate_union_measurable
    (full : data.FullGrainCells lineVolume coverBudget)
    (hdelta : 0 < delta) :
    MeasurableSet (full.paperCandidate hdelta).union :=
  (full.paperCandidate hdelta).union_measurable

theorem paperRegion_subset_candidate_union
    (full : data.FullGrainCells lineVolume coverBudget)
    (hdelta : 0 < delta) :
    full.paperRegion ⊆ (full.paperCandidate hdelta).union := by
  intro point hpoint
  have hpointPrepared := full.paperRegion_subset hpoint
  have hpointBox : point ∈ Kakeya.Streamlined.axisBox 2 2 2 := by
    rcases hpointPrepared with ⟨index, hindex⟩
    exact (data.prepared.refined.shading.subset_body index hindex).2
  have hwindow : wz1PaperGridIndex delta point ∈
      wz1PaperGridIndicesInWindow delta hdelta :=
    Kakeya.Assouad.paper_point_gridIndex_in_window hdelta hpointBox
  have hpointCell : point ∈
      wz1PaperGridCube delta (wz1PaperGridIndex delta point) := by
    rw [mem_wz1PaperGridCube]
  have hselected : wz1PaperGridIndex delta point ∈
      (wz1PaperGridIndicesInWindow delta hdelta).filter fun cell =>
        (full.paperRegion ∩ wz1PaperGridCube delta cell).Nonempty := by
    rw [Finset.mem_filter]
    exact ⟨hwindow, ⟨point, hpoint, hpointCell⟩⟩
  rw [paperCandidate, wz2RefinedShading_union_inter]
  exact ⟨hpointPrepared, Set.mem_iUnion₂.mpr
    ⟨wz1PaperGridIndex delta point, hselected, hpointCell⟩⟩

theorem paperCandidate_close_to_paperRegion
    (full : data.FullGrainCells lineVolume coverBudget)
    (hdelta : 0 < delta) :
    ∀ point ∈ (full.paperCandidate hdelta).union,
      ∃ sourcePoint ∈ full.paperRegion,
        dist point sourcePoint ≤ delta * Real.sqrt 3 := by
  intro point hpoint
  rw [paperCandidate, wz2RefinedShading_union_inter] at hpoint
  rcases Set.mem_iUnion₂.mp hpoint.2 with
    ⟨cell, hcellSelected, hpointCell⟩
  rcases (Finset.mem_filter.mp hcellSelected).2 with
    ⟨sourcePoint, hsourceRegion, hsourceCell⟩
  exact ⟨sourcePoint, hsourceRegion,
    wz1PaperGridCube_diameter hdelta cell hpointCell hsourceCell⟩

/-- Transfer any assembled paper-region interval bound through the ambient
`delta`-cell cubical hull.  In particular, combining this theorem with
`paperCellRegion_interval_covering` and `paperRegion_interval_covering` gives
the exact all-parameter analogue of the historical line-hit candidate. -/
theorem paperCandidate_interval_covering
    (full : data.FullGrainCells lineVolume coverBudget)
    (hdelta : 0 < delta) (hquery : 0 < queryScale)
    (htau : 0 < tauScale)
    (hplaneUnit : ∀ point ∈ data.prepared.refined.shading.union,
      ‖planeMap point‖ = 1)
    (spatialRadius : ℝ)
    (hspatialRadius : Real.sqrt queryScale + delta * Real.sqrt 3 ≤
      spatialRadius)
    (hhullTau : delta * Real.sqrt 3 ≤ tauScale)
    (regionBound : ENNReal)
    (hregion : ∀ center intervalCenter,
      (Metric.externalCoveringNumber (Real.toNNReal queryScale)
        (scalarProjection (planeMap center)
            (full.paperRegion ∩ Metric.closedBall center spatialRadius) ∩
          Metric.closedBall intervalCenter tauScale) : ENNReal) ≤
        regionBound) :
    PureWZ2IntervalCoveringAt (full.paperCandidate hdelta) planeMap
      queryScale (Real.toNNReal queryScale) (Real.toNNReal tauScale)
      ((2 * Nat.ceil ((delta * Real.sqrt 3) / queryScale) + 2 : ENNReal) *
        (5 * regionBound)) := by
  intro center intervalCenter
  let target := scalarProjection (planeMap center)
    ((full.paperCandidate hdelta).union ∩
      Metric.closedBall (center : Point3) (Real.sqrt queryScale))
  let sourceSet := scalarProjection (planeMap center)
    (full.paperRegion ∩ Metric.closedBall (center : Point3) spatialRadius)
  have hcenterPrepared : (center : Point3) ∈
      data.prepared.refined.shading.union := by
    rcases center.property with ⟨index, hindex⟩
    exact ⟨index, full.paperCandidate_subshading hdelta index hindex⟩
  have hclose : ∀ value ∈ target, ∃ sourceValue ∈ sourceSet,
      dist value sourceValue ≤ delta * Real.sqrt 3 := by
    intro value hvalue
    rcases hvalue with ⟨point, hpoint, rfl⟩
    rcases full.paperCandidate_close_to_paperRegion hdelta point hpoint.1 with
      ⟨sourcePoint, hsourcePoint, hdistance⟩
    let sourceValue := inner ℝ sourcePoint (planeMap center)
    have hsourceBall : sourcePoint ∈
        Metric.closedBall (center : Point3) spatialRadius := by
      rw [Metric.mem_closedBall]
      calc
        dist sourcePoint center ≤ dist sourcePoint point + dist point center :=
          dist_triangle _ _ _
        _ ≤ delta * Real.sqrt 3 + Real.sqrt queryScale :=
          add_le_add (by simpa [dist_comm] using hdistance) hpoint.2
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
  have hfinal :=
    Kakeya.Assouad.wz1_lemma18_close_projection_interval_transfer
      target sourceSet queryScale tauScale (delta * Real.sqrt 3) regionBound
      hquery htau (mul_pos hdelta (Real.sqrt_pos.mpr (by norm_num)))
      hhullTau hclose (hregion center) intervalCenter
  have hqueryCoe : (Real.toNNReal queryScale : ℝ) = queryScale :=
    Real.coe_toNNReal _ hquery.le
  have htauCoe : (Real.toNNReal tauScale : ℝ) = tauScale :=
    Real.coe_toNNReal _ htau.le
  simpa only [target, sourceSet, hqueryCoe, htauCoe] using hfinal

/-- End-to-end interval cover from the literal all-parameter cell bounds,
through finite-cell normal transfer and the ambient `delta`-grid hull. -/
theorem paperCandidate_interval_covering_of_cell_bounds
    (full : data.FullGrainCells lineVolume coverBudget)
    (hdelta : 0 < delta) (hquery : 0 < queryScale)
    (htau : 0 < tauScale)
    (hplaneUnit : ∀ point ∈ data.prepared.refined.shading.union,
      ‖planeMap point‖ = 1)
    (spatialRadius normalError : ℝ)
    (hspatialRadius : Real.sqrt queryScale + delta * Real.sqrt 3 ≤
      spatialRadius)
    (hnormalError : 0 < normalError)
    (hnormalErrorTau : normalError ≤ tauScale)
    (hhullTau : delta * Real.sqrt 3 ≤ tauScale)
    (neighborBudget : ℕ)
    (hneighbor : ∀ center,
      (full.paperRelevantCells center spatialRadius).card ≤ neighborBudget)
    (hcentered : ∀ center cell, ∀ hcellRelevant :
        cell ∈ full.paperRelevantCells center spatialRadius,
      ∀ point ∈ full.paperCellRegion
          ⟨cell, (Finset.mem_filter.mp hcellRelevant).1⟩ ∩
          Metric.closedBall center spatialRadius,
        dist (inner ℝ (point - center) (planeMap center))
          (inner ℝ (point - center)
            (planeMap (data.cells.cellRep cell
              ((Finset.mem_filter.mp hcellRelevant).1)))) ≤ normalError)
    (cellBound : ENNReal)
    (hcellBound : ∀ cell : {cell // cell ∈ data.cells.activeCells},
      ∀ intervalCenter : ℝ,
        (Metric.externalCoveringNumber (Real.toNNReal queryScale)
          (scalarProjection (planeMap (data.cells.cellRep cell.1 cell.2))
              (full.paperCellRegion cell) ∩
            Metric.closedBall intervalCenter tauScale) : ENNReal) ≤
          cellBound) :
    PureWZ2IntervalCoveringAt (full.paperCandidate hdelta) planeMap
      queryScale (Real.toNNReal queryScale) (Real.toNNReal tauScale)
      ((2 * Nat.ceil ((delta * Real.sqrt 3) / queryScale) + 2 : ENNReal) *
        (5 * ((2 * Nat.ceil (normalError / queryScale) + 2 : ENNReal) *
          ((neighborBudget : ENNReal) * (5 * cellBound))))) := by
  let regionBound :=
    (2 * Nat.ceil (normalError / queryScale) + 2 : ENNReal) *
      ((neighborBudget : ENNReal) * (5 * cellBound))
  apply full.paperCandidate_interval_covering hdelta hquery htau hplaneUnit
    spatialRadius hspatialRadius hhullTau regionBound
  intro center intervalCenter
  exact full.paperRegion_interval_covering hquery htau hnormalError
    hnormalErrorTau neighborBudget hneighbor hcentered cellBound hcellBound
    center intervalCenter

/-- Fully instantiated paper-candidate interval theorem.  The first nested
point-cover estimate is queried only at actual all-line parameters. -/
theorem paperCandidate_interval_covering_of_nested_cover
    (full : data.FullGrainCells lineVolume coverBudget)
    (hdelta : 0 < delta) (hquery : 0 < queryScale)
    (htau : 0 < tauScale) (hqueryTau : queryScale ≤ tauScale)
    (htauSqrt : tauScale ≤ Real.sqrt queryScale)
    (hsqrtScale : sqrtScale = Real.sqrt queryScale)
    (K : ℝ) (hK : 1 ≤ K)
    (hplaneLipschitz : ∀ first ∈ data.prepared.refined.shading.union,
      ∀ second ∈ data.prepared.refined.shading.union,
        dist (planeMap first) (planeMap second) ≤ K * dist first second)
    (hplaneUnit : ∀ point ∈ data.prepared.refined.shading.union,
      ‖planeMap point‖ = 1)
    (spatialRadius normalError : ℝ)
    (hspatialRadius : Real.sqrt queryScale + delta * Real.sqrt 3 ≤
      spatialRadius)
    (hnormalError : 0 < normalError)
    (hnormalErrorTau : normalError ≤ tauScale)
    (hhullTau : delta * Real.sqrt 3 ≤ tauScale)
    (neighborBudget : ℕ)
    (hneighbor : ∀ center,
      (full.paperRelevantCells center spatialRadius).card ≤ neighborBudget)
    (hcentered : ∀ center cell, ∀ hcellRelevant :
        cell ∈ full.paperRelevantCells center spatialRadius,
      ∀ point ∈ full.paperCellRegion
          ⟨cell, (Finset.mem_filter.mp hcellRelevant).1⟩ ∩
          Metric.closedBall center spatialRadius,
        dist (inner ℝ (point - center) (planeMap center))
          (inner ℝ (point - center)
            (planeMap (data.cells.cellRep cell
              ((Finset.mem_filter.mp hcellRelevant).1)))) ≤ normalError) :
    PureWZ2IntervalCoveringAt (full.paperCandidate hdelta) planeMap
      queryScale (Real.toNNReal queryScale) (Real.toNNReal tauScale)
      ((2 * Nat.ceil ((delta * Real.sqrt 3) / queryScale) + 2 : ENNReal) *
        (5 * ((2 * Nat.ceil (normalError / queryScale) + 2 : ENNReal) *
          ((neighborBudget : ENNReal) *
            (5 * nestedCellIntervalBound queryScale K tauConstant))))) := by
  apply full.paperCandidate_interval_covering_of_cell_bounds hdelta hquery
    htau hplaneUnit spatialRadius normalError hspatialRadius hnormalError
    hnormalErrorTau hhullTau neighborBudget hneighbor hcentered
    (nestedCellIntervalBound queryScale K tauConstant)
  intro cell intervalCenter
  have hcell := full.paperCellRegion_interval_covering cell hquery htau
    hqueryTau
    (bound := (2 * Nat.ceil ((2 * K * queryScale) / queryScale) + 2 :
      ENNReal) * tauConstant)
    (full.tauCoverAtLineParameters hquery htau.le htauSqrt hsqrtScale
      K hK hplaneLipschitz cell.1 cell.2
    ) intervalCenter
  rw [nestedCellIntervalBound_eq]
  exact hcell

/-- Aggregate relative-volume ledger.  Unlike the historical ledger, its
left factor contains no caller-supplied `lineVolume`: the Fubini certificate
itself supplies `volume good ≤ area * line-volume`, and the separated
subcover converts that line-volume to disjoint full grains. -/
theorem prepared_paperCandidate_mass_ledger
    (full : data.FullGrainCells lineVolume coverBudget)
    (hdelta : 0 < delta) (hquery : 0 < queryScale) :
    ((data.cells.cellMass / 2) / (2 * (coverBudget : ENNReal))) *
        data.prepared.refined.shading.mass ≤
      (4 * (ENNReal.ofReal (4 * (2 * sqrtScale) ^ 2) *
        ENNReal.ofReal (4 * queryScale))) *
        (full.paperCandidate hdelta).mass := by
  let areaCost := ENNReal.ofReal (4 * (2 * sqrtScale) ^ 2) *
    ENNReal.ofReal (4 * queryScale)
  have hsourceVolume : data.prepared.refined.shading.mass ≤
      (2 * (2 ^ data.prepared.level : ENNReal)) *
        ((data.cells.activeCells.card : ENNReal) *
          data.cells.cellMass) := by
    calc
      data.prepared.refined.shading.mass ≤
          (2 * (2 ^ data.prepared.level : ENNReal)) *
            volume data.prepared.refined.shading.union :=
        Kakeya.Assouad.mass_le_multiplicity_vol
          (ENNReal.mul_ne_top (by norm_num) (by simp))
          data.prepared.multiplicity_upper
      _ = (2 * (2 ^ data.prepared.level : ENNReal)) *
          ((data.cells.activeCells.card : ENNReal) *
            data.cells.cellMass) := by rw [data.cells.fine_union_volume]
  let activeCells := data.cells.activeCells.attach
  have hgoodMass :
      (data.cells.activeCells.card : ENNReal) *
          (data.cells.cellMass / 2) ≤
        ∑ cell ∈ activeCells, volume (full.cellData cell).good := by
    calc
      (data.cells.activeCells.card : ENNReal) *
          (data.cells.cellMass / 2) =
          ∑ _cell ∈ activeCells, data.cells.cellMass / 2 := by
            simp [activeCells, Finset.sum_const]
      _ ≤ ∑ cell ∈ activeCells, volume (full.cellData cell).good := by
        apply Finset.sum_le_sum
        intro cell _
        exact (full.cellData cell).good_volume
  have hselectedSum :
      (∑ cell ∈ activeCells, volume (full.cellData cell).good) *
          ((data.cells.cellMass / 2) /
            (2 * (coverBudget : ENNReal))) ≤
        areaCost * volume full.lineHitRegion := by
    have hsum :
        ∑ cell ∈ activeCells,
            volume (full.cellData cell).good *
              ((data.cells.cellMass / 2) /
                (2 * (coverBudget : ENNReal))) ≤
          ∑ cell ∈ activeCells,
            areaCost * volume (full.cellLineHitRegion cell.1) := by
      apply Finset.sum_le_sum
      intro cell _
      rw [full.cellLineHitRegion_eq cell.1 cell.2]
      exact full.selectedCellRegion_relative_mass cell hquery
    have hdisjoint : Set.PairwiseDisjoint (↑data.cells.activeCells)
        full.cellLineHitRegion := by
      intro first hfirst second hsecond hne
      exact (wz1PaperGridCube_disjoint hne).mono
        (full.cellLineHitRegion_subset_cell first hfirst)
        (full.cellLineHitRegion_subset_cell second hsecond)
    have hmeasurable : ∀ cell ∈ data.cells.activeCells,
        MeasurableSet (full.cellLineHitRegion cell) := by
      intro cell hcell
      rw [full.cellLineHitRegion_eq cell hcell]
      exact (full.lineHits ⟨cell, hcell⟩).region_measurable
    have hunion : volume full.lineHitRegion =
        ∑ cell ∈ activeCells, volume (full.cellLineHitRegion cell.1) := by
      have hraw : volume full.lineHitRegion =
          ∑ cell ∈ data.cells.activeCells,
            volume (full.cellLineHitRegion cell) :=
        measure_biUnion_finset hdisjoint hmeasurable
      rw [← Finset.sum_attach] at hraw
      exact hraw
    rw [hunion]
    simpa only [Finset.sum_mul, Finset.mul_sum] using hsum
  have hselectedLedger :
      ((data.cells.activeCells.card : ENNReal) *
        (data.cells.cellMass / 2)) *
          ((data.cells.cellMass / 2) /
            (2 * (coverBudget : ENNReal))) ≤
        areaCost * volume full.lineHitRegion :=
    (mul_le_mul_left hgoodMass _).trans hselectedSum
  have hhalf : (2 : ENNReal) * (data.cells.cellMass / 2) =
      data.cells.cellMass := by
    exact ENNReal.mul_div_cancel (by norm_num) (by norm_num)
  have hexactMassLower :
      (2 ^ data.prepared.level : ENNReal) *
          volume full.lineHitRegion ≤
        (full.paperCandidate hdelta).mass := by
    let exactHit := paperRestrictShadingToSet
      data.prepared.refined.shading full.lineHitRegion
        full.lineHitRegion_measurable
    have hexactUnion : exactHit.union = full.lineHitRegion := by
      ext point
      constructor
      · rintro ⟨index, hpoint⟩
        exact hpoint.2
      · intro hpoint
        rcases full.lineHitRegion_subset hpoint with ⟨index, hindex⟩
        exact ⟨index, hindex, hpoint⟩
    have hlower :
        (2 ^ data.prepared.level : ENNReal) *
            volume full.lineHitRegion ≤ exactHit.mass := by
      rw [← hexactUnion]
      apply Kakeya.Assouad.multiplicity_floor_le_mass
      intro point hpoint
      have hpointRegion : point ∈ full.lineHitRegion := by
        rw [← hexactUnion]
        exact hpoint
      change (2 ^ data.prepared.level : ENNReal) ≤
        (paperRestrictShadingToSet data.prepared.refined.shading
          full.lineHitRegion full.lineHitRegion_measurable).pointMultiplicity point
      rw [paperPmRestrictShadingToSet full.lineHitRegion_measurable
        hpointRegion]
      exact data.prepared.multiplicity_lower point
        (full.lineHitRegion_subset hpointRegion)
    exact hlower.trans <| by
      apply Finset.sum_le_sum
      intro index _
      apply measure_mono
      rintro point ⟨hpointPrepared, hpointRegion⟩
      refine ⟨hpointPrepared, ?_⟩
      have hpointPaper : point ∈ full.paperRegion :=
        full.selectedRegion_subset_paperRegion hpointRegion
      have hpointCandidate :=
        full.paperRegion_subset_candidate_union hdelta hpointPaper
      rw [paperCandidate, wz2RefinedShading_union_inter] at hpointCandidate
      exact hpointCandidate.2
  calc
    ((data.cells.cellMass / 2) /
          (2 * (coverBudget : ENNReal))) *
        data.prepared.refined.shading.mass ≤
      ((data.cells.cellMass / 2) /
          (2 * (coverBudget : ENNReal))) *
        ((2 * (2 ^ data.prepared.level : ENNReal)) *
          ((data.cells.activeCells.card : ENNReal) *
            data.cells.cellMass)) :=
      mul_le_mul_right hsourceVolume _
    _ = (4 * (2 ^ data.prepared.level : ENNReal)) *
        (((data.cells.activeCells.card : ENNReal) *
            (data.cells.cellMass / 2)) *
          ((data.cells.cellMass / 2) /
            (2 * (coverBudget : ENNReal)))) := by
      rw [show (4 : ENNReal) = 2 * 2 by norm_num]
      nth_rewrite 2 [← hhalf]
      ring
    _ ≤ (4 * (2 ^ data.prepared.level : ENNReal)) *
        (areaCost * volume full.lineHitRegion) :=
      mul_le_mul_right hselectedLedger _
    _ = (4 * areaCost) *
        ((2 ^ data.prepared.level : ENNReal) *
          volume full.lineHitRegion) := by ring
    _ ≤ (4 * areaCost) * (full.paperCandidate hdelta).mass :=
      mul_le_mul_right hexactMassLower _

/-- Restore the local interval-grain package from the paper candidate.  Its
mass loss depends on cell mass, cover budget and the geometric
`queryScale * sqrtScale^2` cost, but not on an arbitrary external line
volume. -/
theorem prepared_paperCandidate_intervalLocalGrain
    {outputCandidateLoss : ℝ}
    (full : data.FullGrainCells lineVolume coverBudget)
    (hdelta : 0 < delta) (hquery : 0 < queryScale)
    (hcoverBudget : 0 < coverBudget)
    {constant : ENNReal}
    (hcover : PureWZ2IntervalCoveringAt (full.paperCandidate hdelta)
      planeMap queryScale (Real.toNNReal queryScale)
      (Real.toNNReal tauScale) constant)
    (hfinalOutput : finalLoss ≤ outputCandidateLoss)
    (houtputCandidateLoss : 0 < outputCandidateLoss)
    (hrestore :
      proposition63Lemma43MassLoss
          ((data.cells.cellMass / 2) / (2 * (coverBudget : ENNReal)))
          (4 * (ENNReal.ofReal (4 * (2 * sqrtScale) ^ 2) *
            ENNReal.ofReal (4 * queryScale))) *
        Kakeya.realRpowENN delta outputCandidateLoss ≤
          Kakeya.realRpowENN delta finalLoss) :
    ∃ restored : PureWZ2IntervalLocalGrainData
        (sigma := sigma) (outputLoss := outputCandidateLoss)
        (source := data.prepared.refined.shading) planeMap queryScale
        (Real.toNNReal queryScale) (Real.toNNReal tauScale) constant,
      restored.shading = full.paperCandidate hdelta := by
  let leftFactor :=
    (data.cells.cellMass / 2) / (2 * (coverBudget : ENNReal))
  let rightFactor := 4 *
    (ENNReal.ofReal (4 * (2 * sqrtScale) ^ 2) *
      ENNReal.ofReal (4 * queryScale))
  have hbudgetPos : (0 : ENNReal) < coverBudget := by exact_mod_cast hcoverBudget
  have hdenomPos : (0 : ENNReal) < 2 * coverBudget := by positivity
  have hdenomTop : (2 * (coverBudget : ENNReal)) ≠ ⊤ :=
    ENNReal.mul_ne_top (by norm_num) (ENNReal.natCast_ne_top coverBudget)
  have hleftPos : 0 < leftFactor := by
    dsimp only [leftFactor]
    exact ENNReal.div_pos
      (ENNReal.div_pos data.cells.cellMass_pos.ne' (by norm_num)).ne'
      hdenomTop
  have hleftTop : leftFactor ≠ ⊤ := by
    dsimp only [leftFactor]
    exact ENNReal.div_ne_top
      (ENNReal.div_ne_top data.cells.cellMass_ne_top (by norm_num))
      hdenomPos.ne'
  have hrightTop : rightFactor ≠ ⊤ := by
    dsimp only [rightFactor]
    exact ENNReal.mul_ne_top (by norm_num) <|
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  have hmass : leftFactor * data.prepared.refined.shading.mass ≤
      rightFactor * (full.paperCandidate hdelta).mass := by
    simpa only [leftFactor, rightFactor] using
      full.prepared_paperCandidate_mass_ledger hdelta hquery
  let massLoss := proposition63Lemma43MassLoss leftFactor rightFactor
  have hmassRetention : massLoss⁻¹ *
      data.prepared.refined.shading.mass ≤
        (full.paperCandidate hdelta).mass :=
    proposition63Lemma43MassLoss_inv_mul_le
      hleftPos hleftTop hrightTop hmass
  exact intervalLocalGrain_of_mass_ledger planeMap
    data.prepared.refined.extremal data.prepared.refined.cwa
    (full.paperCandidate_subshading hdelta)
    (full.paperCandidate_cubical hdelta) hcover massLoss
    (proposition63Lemma43MassLoss_pos _ _)
    (proposition63Lemma43MassLoss_ne_top hleftPos hrightTop)
    hmassRetention hfinalOutput houtputCandidateLoss
    (by simpa only [massLoss, leftFactor, rightFactor] using hrestore)

/-- Zero-extension and common spatial hull of the paper candidate, restoring
the outer tube family without referring to the historical final candidate. -/
def paperOuterCandidate
    (full : data.FullGrainCells lineVolume coverBudget)
    (hdelta : 0 < delta) :
    WZ1PaperTubeShading initialNormalized.croppedFamily :=
  paperCommonSpatialHull data.first.shading <|
    data.reentry.extendCandidate (full.paperCandidate hdelta)

theorem paperOuterCandidate_subshading
    (full : data.FullGrainCells lineVolume coverBudget)
    (hdelta : 0 < delta) :
    PaperIsSubshading (full.paperOuterCandidate hdelta) data.current := by
  intro index point hpoint
  exact data.first.subshading index
    (paperCommonSpatialHull_subshading _ _ index hpoint)

theorem paperOuterCandidate_cubical
    (full : data.FullGrainCells lineVolume coverBudget)
    (hdelta : 0 < delta) :
    WZ1PaperIsCubicalShading (full.paperOuterCandidate hdelta) := by
  apply paperCommonSpatialHull_cubical data.first.extremal.cubical
  exact extendShading_cubical data.reentry.regularized.selected
    (full.paperCandidate_cubical hdelta)

theorem paperOuterCandidate_union
    (full : data.FullGrainCells lineVolume coverBudget)
    (hdelta : 0 < delta) :
    (full.paperOuterCandidate hdelta).union =
      (full.paperCandidate hdelta).union := by
  let selectedCandidate := full.paperCandidate hdelta
  have hselectedSub : PaperIsSubshading selectedCandidate
      data.reentry.normalization.croppedRefined := fun index =>
    (full.paperCandidate_subshading hdelta index).trans
      (data.prepared.refined.subshading index)
  have hambientSub : PaperIsSubshading
      (data.reentry.extendCandidate selectedCandidate) data.first.shading :=
    data.reentry.extendCandidate_subshading hselectedSub
  calc
    (full.paperOuterCandidate hdelta).union =
        (data.reentry.extendCandidate selectedCandidate).union :=
      paperCommonSpatialHull_union hambientSub
    _ = selectedCandidate.union := data.reentry.extendCandidate_union _

/-- The outer paper candidate preserves the point multiplicity of the current
shading at every point in its union, as required by the interval iterator. -/
theorem paperOuterCandidate_pointMultiplicity_eq
    (full : data.FullGrainCells lineVolume coverBudget)
    (hdelta : 0 < delta) (point : Point3)
    (hpoint : point ∈ (full.paperOuterCandidate hdelta).union) :
    (full.paperOuterCandidate hdelta).pointMultiplicity point =
      data.current.pointMultiplicity point := by
  exact (paperCommonSpatialHull_pointMultiplicity_eq data.first.shading
    (data.reentry.extendCandidate (full.paperCandidate hdelta)) point
    hpoint).trans (data.first_multiplicity point <| by
      exact paperSubshading_union
        (paperCommonSpatialHull_subshading _ _) hpoint)

/-- Full current-to-paper-candidate mass ledger.  The selected factor is the
intrinsic threshold `(cellMass/2)/(2*coverBudget)`; no external line-volume
parameter occurs. -/
theorem paperOuterCandidate_mass_ledger
    (full : data.FullGrainCells lineVolume coverBudget)
    (hdelta : 0 < delta) (hquery : 0 < queryScale) :
    let threshold :=
      (data.cells.cellMass / 2) / (2 * (coverBudget : ENNReal))
    let retainedFactor := data.secondRetainedFactor *
      ((73 / 100 : ENNReal) * data.reentry.normalizationWeight) *
      data.firstRetainedFactor
    let lossFactor := data.reentry.regularized.regularizationLoss *
      data.prepared.preparationLoss
    let areaCost := ENNReal.ofReal (4 * (2 * sqrtScale) ^ 2) *
      ENNReal.ofReal (4 * queryScale)
    (threshold * retainedFactor) * data.current.mass ≤
      (lossFactor * (4 * areaCost)) *
        (full.paperOuterCandidate hdelta).mass := by
  dsimp only
  have hprepared := full.prepared_paperCandidate_mass_ledger hdelta hquery
  have hsource := data.prepared_mass_ledger
  have hselectedMass : (full.paperCandidate hdelta).mass ≤
      (full.paperOuterCandidate hdelta).mass := by
    let selectedCandidate := full.paperCandidate hdelta
    have hselectedSub : PaperIsSubshading selectedCandidate
        data.reentry.normalization.croppedRefined := fun index =>
      (full.paperCandidate_subshading hdelta index).trans
        (data.prepared.refined.subshading index)
    have hambientSub : PaperIsSubshading
        (data.reentry.extendCandidate selectedCandidate) data.first.shading :=
      data.reentry.extendCandidate_subshading hselectedSub
    calc
      (full.paperCandidate hdelta).mass =
          (data.reentry.extendCandidate selectedCandidate).mass :=
        (data.reentry.extendCandidate_mass selectedCandidate).symm
      _ ≤ (full.paperOuterCandidate hdelta).mass :=
        paperCommonSpatialHull_mass_lower hambientSub
  calc
    (((data.cells.cellMass / 2) / (2 * (coverBudget : ENNReal))) *
        (data.secondRetainedFactor *
          ((73 / 100 : ENNReal) * data.reentry.normalizationWeight) *
          data.firstRetainedFactor)) * data.current.mass ≤
      ((data.cells.cellMass / 2) / (2 * (coverBudget : ENNReal))) *
        ((data.reentry.regularized.regularizationLoss *
          data.prepared.preparationLoss) *
          data.prepared.refined.shading.mass) := by
      simpa only [mul_assoc] using
        mul_le_mul_right hsource
          ((data.cells.cellMass / 2) / (2 * (coverBudget : ENNReal)))
    _ = (data.reentry.regularized.regularizationLoss *
          data.prepared.preparationLoss) *
        (((data.cells.cellMass / 2) / (2 * (coverBudget : ENNReal))) *
          data.prepared.refined.shading.mass) := by ring
    _ ≤ (data.reentry.regularized.regularizationLoss *
          data.prepared.preparationLoss) *
        ((4 * (ENNReal.ofReal (4 * (2 * sqrtScale) ^ 2) *
          ENNReal.ofReal (4 * queryScale))) *
          (full.paperCandidate hdelta).mass) :=
      mul_le_mul_right hprepared _
    _ ≤ ((data.reentry.regularized.regularizationLoss *
          data.prepared.preparationLoss) *
          (4 * (ENNReal.ofReal (4 * (2 * sqrtScale) ^ 2) *
            ENNReal.ofReal (4 * queryScale)))) *
        (full.paperOuterCandidate hdelta).mass := by
      simpa only [mul_assoc] using
        mul_le_mul_right hselectedMass
          ((data.reentry.regularized.regularizationLoss *
            data.prepared.preparationLoss) *
            (4 * (ENNReal.ofReal (4 * (2 * sqrtScale) ^ 2) *
              ENNReal.ofReal (4 * queryScale))))

/-- Restore the final interval-local-grain state over `data.current` using
the all-parameter paper candidate and its intrinsic mass ledger. -/
theorem paperOuterCandidate_intervalLocalGrain
    {outputLoss : ℝ}
    (full : data.FullGrainCells lineVolume coverBudget)
    (hdelta : 0 < delta) (hquery : 0 < queryScale)
    (currentLoss : ℝ)
    (hcurrentExtremal : WZ2PaperCroppedIsExtremal sigma currentLoss
      initialNormalized.croppedFamily data.current)
    (hcurrentCWA : WZ2PaperConvexWolffBound
      initialNormalized.croppedFamily
      (Kakeya.realRpowENN delta (-currentLoss)))
    (constant : ENNReal)
    (hcover : PureWZ2IntervalCoveringAt (full.paperOuterCandidate hdelta)
      planeMap queryScale (Real.toNNReal queryScale)
      (Real.toNNReal tauScale) constant)
    (leftFactor rightFactor : ENNReal)
    (hleft : leftFactor ≤
      ((data.cells.cellMass / 2) / (2 * (coverBudget : ENNReal))) *
        (data.secondRetainedFactor *
          ((73 / 100 : ENNReal) * data.reentry.normalizationWeight) *
          data.firstRetainedFactor))
    (hright :
      (data.reentry.regularized.regularizationLoss *
        data.prepared.preparationLoss) *
        (4 * (ENNReal.ofReal (4 * (2 * sqrtScale) ^ 2) *
          ENNReal.ofReal (4 * queryScale))) ≤ rightFactor)
    (hleftPos : 0 < leftFactor) (hleftTop : leftFactor ≠ ⊤)
    (hrightTop : rightFactor ≠ ⊤)
    (hcurrentOutput : currentLoss ≤ outputLoss)
    (houtputLoss : 0 < outputLoss)
    (hrestore : proposition63Lemma43MassLoss leftFactor rightFactor *
      Kakeya.realRpowENN delta outputLoss ≤
        Kakeya.realRpowENN delta currentLoss) :
    ∃ restored : PureWZ2IntervalLocalGrainData
        (sigma := sigma) (outputLoss := outputLoss)
        (source := data.current) planeMap queryScale
        (Real.toNNReal queryScale) (Real.toNNReal tauScale) constant,
      restored.shading = full.paperOuterCandidate hdelta := by
  have hmass : leftFactor * data.current.mass ≤
      rightFactor * (full.paperOuterCandidate hdelta).mass := by
    calc
      leftFactor * data.current.mass ≤
          (((data.cells.cellMass / 2) / (2 * (coverBudget : ENNReal))) *
            (data.secondRetainedFactor *
              ((73 / 100 : ENNReal) * data.reentry.normalizationWeight) *
              data.firstRetainedFactor)) * data.current.mass :=
        mul_le_mul_left hleft _
      _ ≤ ((data.reentry.regularized.regularizationLoss *
              data.prepared.preparationLoss) *
            (4 * (ENNReal.ofReal (4 * (2 * sqrtScale) ^ 2) *
              ENNReal.ofReal (4 * queryScale)))) *
          (full.paperOuterCandidate hdelta).mass :=
        full.paperOuterCandidate_mass_ledger hdelta hquery
      _ ≤ rightFactor * (full.paperOuterCandidate hdelta).mass :=
        mul_le_mul_left hright _
  let massLoss := proposition63Lemma43MassLoss leftFactor rightFactor
  have hmassRetention : massLoss⁻¹ * data.current.mass ≤
      (full.paperOuterCandidate hdelta).mass :=
    proposition63Lemma43MassLoss_inv_mul_le
      hleftPos hleftTop hrightTop hmass
  exact intervalLocalGrain_of_mass_ledger planeMap
    hcurrentExtremal hcurrentCWA
    (full.paperOuterCandidate_subshading hdelta)
    (full.paperOuterCandidate_cubical hdelta) hcover massLoss
    (proposition63Lemma43MassLoss_pos _ _)
    (proposition63Lemma43MassLoss_ne_top hleftPos hrightTop)
    hmassRetention hcurrentOutput houtputLoss
    (by simpa only [massLoss] using hrestore)

end Proposition63NestedPointCoverData.FullGrainCells

end Kakeya.Assouad.PureWZ2

end
