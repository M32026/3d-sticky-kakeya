import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.SourceWitnessCoarseShading
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.CubicalSlabLower
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.OneScaleVariationGeometry
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.NearbyCellResidueRefinement
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.MultiplicityPreservingVariation

/-!
# Coarse plane maps from parent-specific source witnesses

The frozen balanced cover does not provide one fine representative associated
to every coarse parent meeting a spatial cell.  Instead, the source-witness
coarse shading provides an honest fine shaded point separately for each
parent-cell pair.

Sample one common fine point from the active cell.  Lipschitz variation of the
fine plane map compares its normal to the parent-specific honest source in the
same `rho`-cell.  Fine incidence at that source and direction alignment under
the paper cover relation then transfer incidence to the coarse parent.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open InnerProductGeometry MeasureTheory Set

attribute [local instance] Classical.propDecidable

private lemma abs_inner_raw_eq_paper
    {scale : ℝ} (tube : Kakeya.DeltaTube scale) (normal : Point3) :
    |inner ℝ tube.direction normal| =
      |inner ℝ (wz1PaperDirection tube) normal| := by
  unfold wz1PaperDirection
  split_ifs
  · rfl
  · simp [inner_neg_left]

/-- A total representative map which uses an honest fine shaded point on every
active balanced cell.  Values outside the active cells are irrelevant. -/
noncomputable def sourceWitnessFineCellRepresentative
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    (balanced :
      PureWZ2BalancedCoverData cover fineShading coarseShading)
    (cell : ℤ × ℤ × ℤ) : Point3 :=
  if hcell : cell ∈ balanced.activeCells then
    balanced.cellRep cell hcell
  else
    0

private lemma coarse_point_cell_active
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    (balanced :
      PureWZ2BalancedCoverData cover fineShading coarseShading)
    {point : Point3} (hpoint : point ∈ coarseShading.union) :
    wz1PaperGridIndex rho point ∈ balanced.activeCells := by
  rw [balanced.coarse_union_eq] at hpoint
  rcases Set.mem_iUnion.mp hpoint with ⟨cell, hpoint⟩
  rcases Set.mem_iUnion.mp hpoint with ⟨hcell, hpointCell⟩
  have hindex : wz1PaperGridIndex rho point = cell :=
    (mem_wz1PaperGridCube rho cell point).mp hpointCell
  rwa [hindex]

private lemma sourceWitnessFineCellRepresentative_spec
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    (balanced :
      PureWZ2BalancedCoverData cover fineShading coarseShading)
    {point : Point3} (hpoint : point ∈ coarseShading.union) :
    sourceWitnessFineCellRepresentative balanced
          (wz1PaperGridIndex rho point) ∈ fineShading.union ∧
      sourceWitnessFineCellRepresentative balanced
          (wz1PaperGridIndex rho point) ∈
        wz1PaperGridCube rho (wz1PaperGridIndex rho point) := by
  have hactive := coarse_point_cell_active balanced hpoint
  simp only [sourceWitnessFineCellRepresentative, dif_pos hactive]
  exact ⟨balanced.cellRep_in_union _ hactive,
    balanced.cellRep_in_cell _ hactive⟩

/-- Parent-specific source witnesses replace the unavailable common-associated
representative in the coarse plane-map construction.  The explicit budget is

`fine incidence + same-cell normal variation + cover direction error`.

No shading is discarded: the output lives on the whole source-witness coarse
shading and is constant on literal `rho`-grid cells. -/
theorem source_witness_coarse_plane_map
    {delta rho incidence variation target : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    {balanced :
      PureWZ2BalancedCoverData cover fineShading coarseShading}
    (sourceWitness : PureWZ2SourceWitnessCoarseShadingData balanced)
    (hrho : 0 < rho)
    (finePlaneMap : PaperWZ1WeakPlaneMapData fineShading incidence)
    (hfineCellVariation : ∀ first ∈ fineShading.union,
      ∀ second ∈ fineShading.union,
        wz1PaperGridIndex rho first = wz1PaperGridIndex rho second →
          dist (finePlaneMap.planeMap first)
            (finePlaneMap.planeMap second) ≤ variation)
    (hbudget :
      incidence + variation + rho / 2 ≤ target) :
    ∃ coarsePlaneMap :
        PaperWZ1WeakPlaneMapData sourceWitness.shading target,
      (∀ first second,
          wz1PaperGridIndex rho first = wz1PaperGridIndex rho second →
            coarsePlaneMap.planeMap first = coarsePlaneMap.planeMap second) ∧
      (∀ point, coarsePlaneMap.planeMap point =
        finePlaneMap.planeMap
          (sourceWitnessFineCellRepresentative sourceWitness.balanced
            (wz1PaperGridIndex rho point))) := by
  let representative : (ℤ × ℤ × ℤ) → Point3 :=
    sourceWitnessFineCellRepresentative sourceWitness.balanced
  let coarseMap : Point3 → Point3 := fun point =>
    finePlaneMap.planeMap (representative (wz1PaperGridIndex rho point))

  have hrepresentativeMeasurable : Measurable representative :=
    measurable_of_countable representative
  have hgridMeasurable : Measurable (wz1PaperGridIndex rho) := by
    have h : Measurable (fun point : Point3 =>
        (⌊point 0 / rho⌋, ⌊point 1 / rho⌋, ⌊point 2 / rho⌋)) := by
      fun_prop
    convert h using 1
    funext point
    simp [wz1PaperGridIndex, gridIndex]
  have hcoarseMeasurable : Measurable coarseMap :=
    finePlaneMap.measurable.comp
      (hrepresentativeMeasurable.comp hgridMeasurable)

  have hcoarseUnit :
      ∀ point ∈ sourceWitness.shading.union, ‖coarseMap point‖ = 1 := by
    intro point hpoint
    have hrep :=
      (sourceWitnessFineCellRepresentative_spec
        sourceWitness.balanced hpoint).1
    exact finePlaneMap.unit _ hrep

  have hcoarseIncidence :
      ∀ parent point, point ∈ sourceWitness.shading.carrier parent →
        |inner ℝ (coarse.tube parent).direction (coarseMap point)| ≤
          target := by
    intro parent point hpoint
    have hpointUnion : point ∈ sourceWitness.shading.union :=
      ⟨parent, hpoint⟩
    rw [sourceWitness.shading_carrier_eq parent] at hpoint
    rcases Set.mem_iUnion.mp hpoint with ⟨cell, hpoint⟩
    rcases Set.mem_iUnion.mp hpoint with ⟨hcell, hpointCell⟩
    rcases sourceWitness.source_witness parent cell hcell with
      ⟨source, sourcePoint, hsourceParent, hsourcePoint, hsourceCell⟩

    let pointCell := wz1PaperGridIndex rho point
    have hpointCellIndex : pointCell = cell :=
      (mem_wz1PaperGridCube rho cell point).mp hpointCell
    let commonPoint := representative pointCell
    have hcommonSpec :=
      sourceWitnessFineCellRepresentative_spec
        sourceWitness.balanced hpointUnion
    have hcommonFine : commonPoint ∈ fineShading.union := by
      simpa [commonPoint, representative, pointCell] using hcommonSpec.1
    have hcommonCell : commonPoint ∈ wz1PaperGridCube rho cell := by
      have hmem : commonPoint ∈ wz1PaperGridCube rho pointCell := by
        simpa [commonPoint, representative, pointCell] using hcommonSpec.2
      rwa [hpointCellIndex] at hmem
    have hsourceUnion : sourcePoint ∈ fineShading.union :=
      ⟨source, hsourcePoint⟩
    have hmapDistance :
        dist (finePlaneMap.planeMap commonPoint)
            (finePlaneMap.planeMap sourcePoint) ≤
          variation := by
      apply hfineCellVariation commonPoint hcommonFine sourcePoint hsourceUnion
      exact ((mem_wz1PaperGridCube rho cell commonPoint).mp hcommonCell).trans
        ((mem_wz1PaperGridCube rho cell sourcePoint).mp hsourceCell).symm

    have hfineAtSource :
        |inner ℝ (wz1PaperDirection (fine.tube source))
            (finePlaneMap.planeMap sourcePoint)| ≤ incidence := by
      have hraw := finePlaneMap.incidence source sourcePoint hsourcePoint
      have heq := abs_inner_raw_eq_paper
        (fine.tube source) (finePlaneMap.planeMap sourcePoint)
      rw [← heq]
      exact hraw
    have hfineAtCommon :
        |inner ℝ (wz1PaperDirection (fine.tube source))
            (finePlaneMap.planeMap commonPoint)| ≤
          incidence + variation := by
      have hinnerDifference :
          |inner ℝ (wz1PaperDirection (fine.tube source))
              (finePlaneMap.planeMap commonPoint -
                finePlaneMap.planeMap sourcePoint)| ≤
            dist (finePlaneMap.planeMap commonPoint)
              (finePlaneMap.planeMap sourcePoint) := by
        calc
          |inner ℝ (wz1PaperDirection (fine.tube source))
              (finePlaneMap.planeMap commonPoint -
                finePlaneMap.planeMap sourcePoint)|
              ≤ ‖wz1PaperDirection (fine.tube source)‖ *
                  ‖finePlaneMap.planeMap commonPoint -
                    finePlaneMap.planeMap sourcePoint‖ :=
                abs_real_inner_le_norm _ _
          _ = dist (finePlaneMap.planeMap commonPoint)
                (finePlaneMap.planeMap sourcePoint) := by
              rw [wz1PaperDirection_norm]
              simp [dist_eq_norm]
      have hdecompose :
          inner ℝ (wz1PaperDirection (fine.tube source))
              (finePlaneMap.planeMap commonPoint) =
            inner ℝ (wz1PaperDirection (fine.tube source))
                (finePlaneMap.planeMap sourcePoint) +
              inner ℝ (wz1PaperDirection (fine.tube source))
                (finePlaneMap.planeMap commonPoint -
                  finePlaneMap.planeMap sourcePoint) := by
        rw [inner_sub_right]
        ring
      rw [hdecompose]
      calc
        |inner ℝ (wz1PaperDirection (fine.tube source))
              (finePlaneMap.planeMap sourcePoint) +
            inner ℝ (wz1PaperDirection (fine.tube source))
              (finePlaneMap.planeMap commonPoint -
                finePlaneMap.planeMap sourcePoint)|
            ≤ |inner ℝ (wz1PaperDirection (fine.tube source))
                  (finePlaneMap.planeMap sourcePoint)| +
                |inner ℝ (wz1PaperDirection (fine.tube source))
                  (finePlaneMap.planeMap commonPoint -
                    finePlaneMap.planeMap sourcePoint)| :=
              abs_add_le _ _
        _ ≤ incidence + variation :=
              add_le_add hfineAtSource (hinnerDifference.trans hmapDistance)

    have hcover : WZ1PaperTubeCovers
        (fine.tube source) (coarse.tube parent) := by
      rw [← hsourceParent]
      exact cover.toPaperTubeCover.parent_covers source
    have hcommonUnit : ‖finePlaneMap.planeMap commonPoint‖ = 1 :=
      finePlaneMap.unit commonPoint hcommonFine
    have hparentIncidence :
        |inner ℝ (wz1PaperDirection (coarse.tube parent))
            (finePlaneMap.planeMap commonPoint)| ≤
          incidence + variation + rho / 2 :=
      paper_cover_parent_incidence hcover hcommonUnit hfineAtCommon
    have hrawParent :
        |inner ℝ (coarse.tube parent).direction
            (finePlaneMap.planeMap commonPoint)| ≤ target := by
      have heq := abs_inner_raw_eq_paper
        (coarse.tube parent) (finePlaneMap.planeMap commonPoint)
      rw [heq]
      exact hparentIncidence.trans hbudget
    simpa [coarseMap, commonPoint, pointCell] using hrawParent

  let coarsePlaneMap :
      PaperWZ1WeakPlaneMapData sourceWitness.shading target :=
    { planeMap := coarseMap
      measurable := hcoarseMeasurable
      unit := hcoarseUnit
      incidence := hcoarseIncidence }
  refine ⟨coarsePlaneMap, ?_, ?_⟩
  · intro first second hcell
    simp only [coarsePlaneMap, coarseMap]
    rw [hcell]
  · intro point
    rfl

/-- A fixed residue selection turns the sampled coarse map into a genuine
`5 * K`-Lipschitz map.  Nearby selected points have the same `rho`-cell and
hence the same sampled normal.  For points farther than `rho`, the two cell
representatives are at distance at most five times the original points. -/
theorem source_witness_coarse_plane_map_lipschitz
    {delta rho incidence target : ℝ}
    {K : NNReal}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    {balanced :
      PureWZ2BalancedCoverData cover fineShading coarseShading}
    (sourceWitness : PureWZ2SourceWitnessCoarseShadingData balanced)
    (hrho : 0 < rho)
    (finePlaneMap : PaperWZ1WeakPlaneMapData fineShading incidence)
    (hfineLipschitz : LipschitzWith K
      (fun point : {point : Point3 // point ∈ fineShading.union} =>
        finePlaneMap.planeMap point))
    (hbudget :
      incidence + (K : ℝ) * (rho * Real.sqrt 3) + rho / 2 ≤ target) :
    ∃ (selected : WZ1PaperTubeShading coarse)
      (coarsePlaneMap : PaperWZ1WeakPlaneMapData selected target),
      PaperIsSubshading selected sourceWitness.shading ∧
      WZ1PaperIsCubicalShading selected ∧
      (∀ point ∈ selected.union,
        selected.pointMultiplicity point =
          sourceWitness.shading.pointMultiplicity point) ∧
      sourceWitness.shading.mass ≤ 27 * selected.mass ∧
      LipschitzWith (5 * K)
        (fun point : {point : Point3 // point ∈ selected.union} =>
          coarsePlaneMap.planeMap point) := by
  have hfineCellVariation : ∀ first ∈ fineShading.union,
      ∀ second ∈ fineShading.union,
        wz1PaperGridIndex rho first = wz1PaperGridIndex rho second →
          dist (finePlaneMap.planeMap first)
            (finePlaneMap.planeMap second) ≤
              (K : ℝ) * (rho * Real.sqrt 3) := by
    intro first hfirst second hsecond hcell
    have hfirstCell : first ∈
        wz1PaperGridCube rho (wz1PaperGridIndex rho first) :=
      (mem_wz1PaperGridCube rho _ first).mpr rfl
    have hsecondCell : second ∈
        wz1PaperGridCube rho (wz1PaperGridIndex rho first) :=
      (mem_wz1PaperGridCube rho _ second).mpr hcell.symm
    have hdistance : dist first second ≤ rho * Real.sqrt 3 :=
      wz1PaperGridCube_diameter hrho _ hfirstCell hsecondCell
    exact (hfineLipschitz.dist_le_mul ⟨first, hfirst⟩ ⟨second, hsecond⟩).trans
      (mul_le_mul_of_nonneg_left hdistance K.coe_nonneg)
  rcases source_witness_coarse_plane_map sourceWitness hrho finePlaneMap
      hfineCellVariation hbudget with
    ⟨coarsePlaneMap, hcoarseCell, hcoarseSample⟩
  rcases paper_fine_cell_residue_refinement_cubical
      coarsePlaneMap.planeMap hrho sourceWitness.balanced.coarse_cubical
      (scale := 0) (by
        intro first hfirst second hsecond hcell
        rw [hcoarseCell first second hcell]
        simp) with
    ⟨selected, hselectedSub, hselectedCubical, hnearby,
      hselectedMultiplicity, hselectedMass⟩
  let selectedPlaneMap := paperWeakPlaneMapRestrict coarsePlaneMap hselectedSub
  have hselectedInWitness : selected.union ⊆ sourceWitness.shading.union := by
    rintro point ⟨index, hpoint⟩
    exact ⟨index, hselectedSub index hpoint⟩
  have hselectedLipschitz : LipschitzWith (5 * K)
      (fun point : {point : Point3 // point ∈ selected.union} =>
        selectedPlaneMap.planeMap point) := by
    apply LipschitzWith.of_dist_le_mul
    intro first second
    let firstPoint : Point3 := first
    let secondPoint : Point3 := second
    by_cases hnear : dist firstPoint secondPoint ≤ rho
    · have hzero := hnearby firstPoint first.prop secondPoint second.prop hnear
      have heq : selectedPlaneMap.planeMap first =
          selectedPlaneMap.planeMap second :=
        dist_eq_zero.mp (le_antisymm hzero dist_nonneg)
      rw [heq, dist_self]
      positivity
    · have hrhoDistance : rho < dist firstPoint secondPoint :=
        lt_of_not_ge hnear
      let firstRepresentative :=
        sourceWitnessFineCellRepresentative sourceWitness.balanced
          (wz1PaperGridIndex rho firstPoint)
      let secondRepresentative :=
        sourceWitnessFineCellRepresentative sourceWitness.balanced
          (wz1PaperGridIndex rho secondPoint)
      have hfirstSpec := sourceWitnessFineCellRepresentative_spec
        sourceWitness.balanced (hselectedInWitness first.prop)
      have hsecondSpec := sourceWitnessFineCellRepresentative_spec
        sourceWitness.balanced (hselectedInWitness second.prop)
      have hfirstDistance : dist firstRepresentative firstPoint ≤
          rho * Real.sqrt 3 := by
        let cell := wz1PaperGridIndex rho firstPoint
        have hfirstCell : firstPoint ∈ wz1PaperGridCube rho cell :=
          (mem_wz1PaperGridCube rho cell firstPoint).mpr rfl
        have hrepresentativeCell :
            firstRepresentative ∈ wz1PaperGridCube rho cell := by
          simpa [firstRepresentative, firstPoint, cell] using hfirstSpec.2
        exact wz1PaperGridCube_diameter hrho cell
          hrepresentativeCell hfirstCell
      have hsecondDistance : dist secondPoint secondRepresentative ≤
          rho * Real.sqrt 3 := by
        let cell := wz1PaperGridIndex rho secondPoint
        have hsecondCell : secondPoint ∈ wz1PaperGridCube rho cell :=
          (mem_wz1PaperGridCube rho cell secondPoint).mpr rfl
        have hrepresentativeCell :
            secondRepresentative ∈ wz1PaperGridCube rho cell := by
          simpa [secondRepresentative, secondPoint, cell] using hsecondSpec.2
        exact wz1PaperGridCube_diameter hrho cell
          hsecondCell hrepresentativeCell
      have hrepresentativeDistance :
          dist firstRepresentative secondRepresentative ≤
            dist firstPoint secondPoint + 2 * (rho * Real.sqrt 3) := by
        calc
          dist firstRepresentative secondRepresentative ≤
              dist firstRepresentative firstPoint +
                dist firstPoint secondPoint +
                  dist secondPoint secondRepresentative := by
            linarith [dist_triangle firstRepresentative firstPoint
              secondRepresentative,
              dist_triangle firstPoint secondPoint secondRepresentative]
          _ ≤ rho * Real.sqrt 3 + dist firstPoint secondPoint +
                rho * Real.sqrt 3 := by gcongr
          _ = dist firstPoint secondPoint + 2 * (rho * Real.sqrt 3) := by ring
      have hsqrt : Real.sqrt 3 ≤ 2 := by
        rw [Real.sqrt_le_iff]
        norm_num
      have hrepresentativeFive :
          dist firstRepresentative secondRepresentative ≤
            5 * dist firstPoint secondPoint := by
        calc
          dist firstRepresentative secondRepresentative ≤
              dist firstPoint secondPoint + 2 * (rho * Real.sqrt 3) :=
            hrepresentativeDistance
          _ ≤ dist firstPoint secondPoint + 4 * rho := by
            nlinarith
          _ ≤ 5 * dist firstPoint secondPoint := by
            nlinarith
      have hmapDistance :
          dist (finePlaneMap.planeMap firstRepresentative)
              (finePlaneMap.planeMap secondRepresentative) ≤
            (K : ℝ) * dist firstRepresentative secondRepresentative :=
        hfineLipschitz.dist_le_mul
          ⟨firstRepresentative, hfirstSpec.1⟩
          ⟨secondRepresentative, hsecondSpec.1⟩
      change dist (coarsePlaneMap.planeMap firstPoint)
          (coarsePlaneMap.planeMap secondPoint) ≤
        ((5 * K : NNReal) : ℝ) * dist firstPoint secondPoint
      rw [hcoarseSample firstPoint, hcoarseSample secondPoint]
      calc
        dist (finePlaneMap.planeMap firstRepresentative)
            (finePlaneMap.planeMap secondRepresentative) ≤
              (K : ℝ) * dist firstRepresentative secondRepresentative :=
          hmapDistance
        _ ≤ (K : ℝ) * (5 * dist firstPoint secondPoint) := by
          gcongr
        _ = ((5 * K : NNReal) : ℝ) * dist firstPoint secondPoint := by
          norm_num
          ring
  exact ⟨selected, selectedPlaneMap, hselectedSub, hselectedCubical,
    hselectedMultiplicity, hselectedMass, hselectedLipschitz⟩

/-- A fixed residue selection turns the sampled coarse map into a genuine
Lipschitz map.  Nearby selected points have the same `rho`-cell and hence the
same sampled normal.  For points farther than `rho`, the two cell
representatives cost at most `2 * sqrt(3) * rho`; thus a fine Lipschitz
constant at most `1/5` is enough for a coarse Lipschitz constant one. -/
theorem source_witness_coarse_plane_map_lipschitz_one
    {delta rho incidence target : ℝ}
    {K : NNReal}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    {balanced :
      PureWZ2BalancedCoverData cover fineShading coarseShading}
    (sourceWitness : PureWZ2SourceWitnessCoarseShadingData balanced)
    (hrho : 0 < rho)
    (finePlaneMap : PaperWZ1WeakPlaneMapData fineShading incidence)
    (hfineLipschitz : LipschitzWith K
      (fun point : {point : Point3 // point ∈ fineShading.union} =>
        finePlaneMap.planeMap point))
    (hK : (K : ℝ) ≤ 1 / 5)
    (hbudget :
      incidence + (K : ℝ) * (rho * Real.sqrt 3) + rho / 2 ≤ target) :
    ∃ (selected : WZ1PaperTubeShading coarse)
      (coarsePlaneMap : PaperWZ1WeakPlaneMapData selected target),
      PaperIsSubshading selected sourceWitness.shading ∧
      WZ1PaperIsCubicalShading selected ∧
      (∀ point ∈ selected.union,
        selected.pointMultiplicity point =
          sourceWitness.shading.pointMultiplicity point) ∧
      sourceWitness.shading.mass ≤ 27 * selected.mass ∧
      (∀ first second,
        wz1PaperGridIndex rho first = wz1PaperGridIndex rho second →
          coarsePlaneMap.planeMap first = coarsePlaneMap.planeMap second) ∧
      LipschitzWith 1
        (fun point : {point : Point3 // point ∈ selected.union} =>
          coarsePlaneMap.planeMap point) := by
  have hfineCellVariation : ∀ first ∈ fineShading.union,
      ∀ second ∈ fineShading.union,
        wz1PaperGridIndex rho first = wz1PaperGridIndex rho second →
          dist (finePlaneMap.planeMap first)
            (finePlaneMap.planeMap second) ≤
              (K : ℝ) * (rho * Real.sqrt 3) := by
    intro first hfirst second hsecond hcell
    have hfirstCell : first ∈
        wz1PaperGridCube rho (wz1PaperGridIndex rho first) :=
      (mem_wz1PaperGridCube rho _ first).mpr rfl
    have hsecondCell : second ∈
        wz1PaperGridCube rho (wz1PaperGridIndex rho first) :=
      (mem_wz1PaperGridCube rho _ second).mpr hcell.symm
    have hdistance : dist first second ≤ rho * Real.sqrt 3 :=
      wz1PaperGridCube_diameter hrho _ hfirstCell hsecondCell
    exact (hfineLipschitz.dist_le_mul ⟨first, hfirst⟩ ⟨second, hsecond⟩).trans
      (mul_le_mul_of_nonneg_left hdistance K.coe_nonneg)
  rcases source_witness_coarse_plane_map sourceWitness hrho finePlaneMap
      hfineCellVariation hbudget with
    ⟨coarsePlaneMap, hcoarseCell, hcoarseSample⟩
  rcases paper_fine_cell_residue_refinement_cubical
      coarsePlaneMap.planeMap hrho sourceWitness.balanced.coarse_cubical
      (scale := 0) (by
        intro first hfirst second hsecond hcell
        rw [hcoarseCell first second hcell]
        simp) with
    ⟨selected, hselectedSub, hselectedCubical, hnearby,
      hselectedMultiplicity, hselectedMass⟩
  let selectedPlaneMap := paperWeakPlaneMapRestrict coarsePlaneMap hselectedSub
  have hselectedInWitness : selected.union ⊆ sourceWitness.shading.union := by
    rintro point ⟨index, hpoint⟩
    exact ⟨index, hselectedSub index hpoint⟩
  have hselectedLipschitz : LipschitzWith 1
      (fun point : {point : Point3 // point ∈ selected.union} =>
        selectedPlaneMap.planeMap point) := by
    apply LipschitzWith.mk_one
    intro first second
    let firstPoint : Point3 := first
    let secondPoint : Point3 := second
    by_cases hnear : dist firstPoint secondPoint ≤ rho
    · have hzero := hnearby firstPoint first.prop secondPoint second.prop hnear
      change dist (selectedPlaneMap.planeMap first)
          (selectedPlaneMap.planeMap second) ≤ dist firstPoint secondPoint
      have heq : selectedPlaneMap.planeMap first =
          selectedPlaneMap.planeMap second :=
        dist_eq_zero.mp (le_antisymm hzero dist_nonneg)
      rw [heq, dist_self]
      exact dist_nonneg
    · have hrhoDistance : rho < dist firstPoint secondPoint :=
        lt_of_not_ge hnear
      let firstRepresentative :=
        sourceWitnessFineCellRepresentative sourceWitness.balanced
          (wz1PaperGridIndex rho firstPoint)
      let secondRepresentative :=
        sourceWitnessFineCellRepresentative sourceWitness.balanced
          (wz1PaperGridIndex rho secondPoint)
      have hfirstSpec := sourceWitnessFineCellRepresentative_spec
        sourceWitness.balanced (hselectedInWitness first.prop)
      have hsecondSpec := sourceWitnessFineCellRepresentative_spec
        sourceWitness.balanced (hselectedInWitness second.prop)
      have hfirstDistance : dist firstRepresentative firstPoint ≤
          rho * Real.sqrt 3 := by
        let cell := wz1PaperGridIndex rho firstPoint
        have hfirstCell : firstPoint ∈ wz1PaperGridCube rho cell :=
          (mem_wz1PaperGridCube rho cell firstPoint).mpr rfl
        have hrepresentativeCell :
            firstRepresentative ∈ wz1PaperGridCube rho cell := by
          simpa [firstRepresentative, firstPoint, cell] using hfirstSpec.2
        exact wz1PaperGridCube_diameter hrho cell
          hrepresentativeCell hfirstCell
      have hsecondDistance : dist secondPoint secondRepresentative ≤
          rho * Real.sqrt 3 := by
        let cell := wz1PaperGridIndex rho secondPoint
        have hsecondCell : secondPoint ∈ wz1PaperGridCube rho cell :=
          (mem_wz1PaperGridCube rho cell secondPoint).mpr rfl
        have hrepresentativeCell :
            secondRepresentative ∈ wz1PaperGridCube rho cell := by
          simpa [secondRepresentative, secondPoint, cell] using hsecondSpec.2
        exact wz1PaperGridCube_diameter hrho cell
          hsecondCell hrepresentativeCell
      have hrepresentativeDistance :
          dist firstRepresentative secondRepresentative ≤
            dist firstPoint secondPoint + 2 * (rho * Real.sqrt 3) := by
        calc
          dist firstRepresentative secondRepresentative ≤
              dist firstRepresentative firstPoint +
                dist firstPoint secondPoint +
                  dist secondPoint secondRepresentative := by
            linarith [dist_triangle firstRepresentative firstPoint
              secondRepresentative,
              dist_triangle firstPoint secondPoint secondRepresentative]
          _ ≤ rho * Real.sqrt 3 + dist firstPoint secondPoint +
                rho * Real.sqrt 3 := by gcongr
          _ = dist firstPoint secondPoint + 2 * (rho * Real.sqrt 3) := by ring
      have hsqrt : Real.sqrt 3 ≤ 2 := by
        rw [Real.sqrt_le_iff]
        norm_num
      have hrepresentativeFive :
          dist firstRepresentative secondRepresentative ≤
            5 * dist firstPoint secondPoint := by
        calc
          dist firstRepresentative secondRepresentative ≤
              dist firstPoint secondPoint + 2 * (rho * Real.sqrt 3) :=
            hrepresentativeDistance
          _ ≤ dist firstPoint secondPoint + 4 * rho := by
            nlinarith
          _ ≤ 5 * dist firstPoint secondPoint := by
            nlinarith
      have hmapDistance :
          dist (finePlaneMap.planeMap firstRepresentative)
              (finePlaneMap.planeMap secondRepresentative) ≤
            (K : ℝ) * dist firstRepresentative secondRepresentative :=
        hfineLipschitz.dist_le_mul
          ⟨firstRepresentative, hfirstSpec.1⟩
          ⟨secondRepresentative, hsecondSpec.1⟩
      change dist (coarsePlaneMap.planeMap firstPoint)
          (coarsePlaneMap.planeMap secondPoint) ≤ dist firstPoint secondPoint
      rw [hcoarseSample firstPoint, hcoarseSample secondPoint]
      calc
        dist (finePlaneMap.planeMap firstRepresentative)
            (finePlaneMap.planeMap secondRepresentative) ≤
              (K : ℝ) * dist firstRepresentative secondRepresentative :=
          hmapDistance
        _ ≤ (1 / 5 : ℝ) * (5 * dist firstPoint secondPoint) := by
          gcongr
        _ = dist firstPoint secondPoint := by ring
  have hselectedCellwise : ∀ first second,
      wz1PaperGridIndex rho first = wz1PaperGridIndex rho second →
        selectedPlaneMap.planeMap first = selectedPlaneMap.planeMap second := by
    intro first second hcell
    exact hcoarseCell first second hcell
  exact ⟨selected, selectedPlaneMap, hselectedSub, hselectedCubical,
    hselectedMultiplicity, hselectedMass, hselectedCellwise,
    hselectedLipschitz⟩

end Kakeya.Assouad.PureWZ2

end
