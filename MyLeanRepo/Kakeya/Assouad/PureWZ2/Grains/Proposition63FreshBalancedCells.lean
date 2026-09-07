import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63BalancedCellData
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63OneScaleMultiplicityPreparation
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.RebalancedFiniteRefinement
import MyLeanRepo.Kakeya.Assouad.ExtremalHelpers
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperBoundaryCoefficient
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperActiveCellLogBound
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.SelectedCardinalityCancellation

/-!
# Fresh square-root balanced cells for one Proposition 6.3 step

This is the honest finite/geometric producer missing between a one-scale
local-AD output and the full-grain/Fubini argument.  It balances literal
whole fine cells directly at the requested square-root scale.  No coarse tube
family, unrelated sticky witness, or inherited parent map is introduced.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory Set ENNReal Metric

attribute [local instance] Classical.propDecidable

/-- The exact loss incurred by boundary pruning followed by equal-cell
balancing, starting from an already constant-multiplicity one-scale shading. -/
def proposition63FreshBalancingLoss
    {delta scale : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    {hdelta : 0 < delta}
    {multiplicityCap : ENNReal}
    (pruning : WZ2PaperBoundaryCellPruningData
      (rho := scale) shading hdelta multiplicityCap) : ENNReal :=
  (2 : ENNReal) *
    ((4 : ENNReal) *
      ((Nat.log 2
        (∑ cell ∈ pruning.coarseCells,
          (pruning.availableFineCells cell).card) + 1 : ℕ) : ENNReal))

/-- Fixed physical logarithmic envelope for the fresh exact-balancing loss. -/
def proposition63FreshBalancingEnvelope (delta : ℝ) : ENNReal :=
  (8 : ENNReal) * ENNReal.ofReal
    (wz2PaperBoundaryLogCoefficient * (1 + Real.log delta⁻¹))

/-- Fixed total preparation loss: one tube-multiplicity pigeonhole followed
by one fresh whole-cell balancing. -/
def proposition63UniformPreparationLoss
    {delta : ℝ} (family : Kakeya.Streamlined.TubeFamily delta) : ENNReal :=
  ((Nat.log 2 family.card + 1 : ℕ) : ENNReal) *
    proposition63FreshBalancingEnvelope delta

/-- Result of balancing an already constant-multiplicity one-scale shading at
the exact square-root scale. -/
structure Proposition63FreshBalancedCellsData
    {delta sigma firstLoss preparedLoss queryScale sqrtScale : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source : WZ1PaperTubeShading family}
    (planeMap : Point3 → Point3)
    (original : PureWZ2OneScaleLocalGrainData
      (sigma := sigma) (outputLoss := firstLoss)
      (rho := queryScale) (Y := source) (fun point => planeMap point))
    (prepared : Proposition63OneScaleConstantMultiplicityData
      (secondLoss := preparedLoss) planeMap original)
    (hdelta : 0 < delta) where
  multiplicityCap : ENNReal :=
    2 * (2 ^ prepared.level : ENNReal)
  pruning : WZ2PaperBoundaryCellPruningData
    (rho := sqrtScale) prepared.refined.shading hdelta multiplicityCap
  balancing : WZ2PaperExactCellBalancingData
    (rho := sqrtScale) pruning.pruned pruning.coarseCells
      pruning.availableFineCells
  retention : WZ2PaperExactBalancingMassRetentionData
    prepared.refined.shading hdelta multiplicityCap pruning balancing
      prepared.level
  freshLoss : ENNReal := proposition63FreshBalancingLoss pruning
  freshLoss_eq : freshLoss = proposition63FreshBalancingLoss pruning
  freshLoss_pos : 0 < freshLoss
  freshLoss_ne_top : freshLoss ≠ ⊤
  prepared_mass_retention : prepared.refined.shading.mass ≤
    freshLoss * balancing.refined.mass
  preparedLoss : ENNReal :=
    prepared.preparationLoss * freshLoss
  preparedLoss_eq : preparedLoss =
    prepared.preparationLoss * freshLoss
  preparedLoss_pos : 0 < preparedLoss
  preparedLoss_ne_top : preparedLoss ≠ ⊤
  mass_retention : original.shading.mass ≤
    preparedLoss * balancing.refined.mass
  cells : Proposition63BalancedCellData (scale := sqrtScale)
    balancing.refined

theorem Proposition63FreshBalancedCellsData.freshLoss_le_envelope
    {delta sigma firstLoss preparedLoss queryScale sqrtScale : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source : WZ1PaperTubeShading family}
    {planeMap : Point3 → Point3}
    {original : PureWZ2OneScaleLocalGrainData
      (sigma := sigma) (outputLoss := firstLoss)
      (rho := queryScale) (Y := source) (fun point => planeMap point)}
    {prepared : Proposition63OneScaleConstantMultiplicityData
      (secondLoss := preparedLoss) planeMap original}
    {hdelta : 0 < delta}
    (data : Proposition63FreshBalancedCellsData
      (sqrtScale := sqrtScale) planeMap original prepared hdelta) :
    data.freshLoss ≤ proposition63FreshBalancingEnvelope delta := by
  have hlog := wz2_paper_available_cell_log_bound_ennreal
    hdelta original.extremal.delta_le_one data.pruning
  rw [data.freshLoss_eq]
  unfold proposition63FreshBalancingLoss
  unfold proposition63FreshBalancingEnvelope
  calc
    (2 : ENNReal) *
        (4 *
          ((Nat.log 2
            (∑ cell ∈ data.pruning.coarseCells,
              (data.pruning.availableFineCells cell).card) + 1 : ℕ) :
            ENNReal)) =
      8 *
        ((Nat.log 2
          (∑ cell ∈ data.pruning.coarseCells,
            (data.pruning.availableFineCells cell).card) + 1 : ℕ) :
          ENNReal) := by ring
    _ ≤ 8 * ENNReal.ofReal
        (wz2PaperBoundaryLogCoefficient * (1 + Real.log delta⁻¹)) := by
      gcongr

/-- Finish fresh balancing from an already constructed boundary pruning whose
pruned shading retains at least half of the source mass.  This common tail is
shared by the elementary multiplicity-cap entry point and the paper-faithful
Convex-Wolff boundary-mass entry point below. -/
theorem proposition63_fresh_balancedCells_of_pruning
    {delta sigma firstLoss preparedLoss queryScale sqrtScale : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source : WZ1PaperTubeShading family}
    (planeMap : Point3 → Point3)
    (original : PureWZ2OneScaleLocalGrainData
      (sigma := sigma) (outputLoss := firstLoss)
      (rho := queryScale) (Y := source) (fun point => planeMap point))
    (prepared : Proposition63OneScaleConstantMultiplicityData
      (secondLoss := preparedLoss) planeMap original)
    (hsqrtPos : 0 < sqrtScale)
    (pruning : WZ2PaperBoundaryCellPruningData
      (rho := sqrtScale) prepared.refined.shading original.extremal.delta_pos
        (2 * (2 ^ prepared.level : ENNReal)))
    (hsourcePruned : prepared.refined.shading.mass ≤
      2 * pruning.pruned.mass) :
    Nonempty (Proposition63FreshBalancedCellsData
      (sqrtScale := sqrtScale) planeMap original prepared
      original.extremal.delta_pos) := by
  let cap : ENNReal := 2 * (2 ^ prepared.level : ENNReal)
  rcases wz2_prop_sticky_exact_cell_balancing
      original.extremal.delta_pos hsqrtPos pruning.pruned
      pruning.pruned_cubical pruning.coarseCells
      pruning.coarseCells_nonempty pruning.availableFineCells
      pruning.availableFineCells_nonempty pruning.availableFineCells_ready with
    ⟨balancing⟩
  rcases wz2_paper_exact_balancing_mass_retention
      original.extremal.delta_pos prepared.refined.shading prepared.level
      (fun point hpoint =>
        ⟨prepared.multiplicity_lower point hpoint, by
          simpa [pow_succ, mul_comm] using prepared.multiplicity_upper point hpoint⟩)
      cap pruning balancing with ⟨retention⟩
  let freshLoss := proposition63FreshBalancingLoss pruning
  have hfreshPos : 0 < freshLoss := by
    dsimp only [freshLoss, proposition63FreshBalancingLoss]
    positivity
  have hfreshTop : freshLoss ≠ ⊤ := by
    exact ENNReal.mul_ne_top (by norm_num) <|
      ENNReal.mul_ne_top (by norm_num) (by simp)
  have hpreparedBalancing : prepared.refined.shading.mass ≤
      freshLoss * balancing.refined.mass := by
    calc
      prepared.refined.shading.mass ≤ 2 * pruning.pruned.mass :=
        hsourcePruned
      _ ≤ 2 *
          (((4 : ENNReal) *
            ((Nat.log 2
              (∑ cell ∈ pruning.coarseCells,
                (pruning.availableFineCells cell).card) + 1 : ℕ) : ENNReal)) *
              balancing.refined.mass) := by
        gcongr
        simpa using retention.mass_retention
      _ = freshLoss * balancing.refined.mass := by
        simp only [freshLoss, proposition63FreshBalancingLoss]
        ring
  let totalLoss := prepared.preparationLoss * freshLoss
  have htotalPos : 0 < totalLoss :=
    ENNReal.mul_pos prepared.preparationLoss_pos.ne' hfreshPos.ne'
  have htotalTop : totalLoss ≠ ⊤ :=
    ENNReal.mul_ne_top prepared.preparationLoss_ne_top hfreshTop
  have htotalMass : original.shading.mass ≤
      totalLoss * balancing.refined.mass := by
    calc
      original.shading.mass ≤ prepared.preparationLoss *
          prepared.refined.shading.mass := prepared.mass_retention
      _ ≤ prepared.preparationLoss *
          (freshLoss * balancing.refined.mass) := by gcongr
      _ = totalLoss * balancing.refined.mass := by
        simp only [totalLoss]
        ring
  exact ⟨{
    multiplicityCap := cap
    pruning := pruning
    balancing := balancing
    retention := retention
    freshLoss := freshLoss
    freshLoss_eq := rfl
    freshLoss_pos := hfreshPos
    freshLoss_ne_top := hfreshTop
    prepared_mass_retention := hpreparedBalancing
    preparedLoss := totalLoss
    preparedLoss_eq := rfl
    preparedLoss_pos := htotalPos
    preparedLoss_ne_top := htotalTop
    mass_retention := htotalMass
    cells := Proposition63BalancedCellData.ofExactBalancing balancing hsqrtPos
  }⟩

/-- Produce fresh balanced square-root cells after the caller has supplied
the explicit boundary-layer absorption.  This is exactly the non-aligned
whole-cell step; all losses remain visible in the output. -/
theorem proposition63_fresh_balancedCells
    {delta sigma firstLoss preparedLoss queryScale sqrtScale : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source : WZ1PaperTubeShading family}
    (planeMap : Point3 → Point3)
    (original : PureWZ2OneScaleLocalGrainData
      (sigma := sigma) (outputLoss := firstLoss)
      (rho := queryScale) (Y := source) (fun point => planeMap point))
    (prepared : Proposition63OneScaleConstantMultiplicityData
      (secondLoss := preparedLoss) planeMap original)
    (hdeltaSqrt : delta ≤ sqrtScale)
    (hsqrtPos : 0 < sqrtScale)
    (hsqrtOne : sqrtScale ≤ 1)
    (hboundary :
      2 * ((2 * (2 ^ prepared.level : ENNReal)) *
          ENNReal.ofReal (1000 * delta / sqrtScale)) <
        prepared.refined.shading.mass) :
    Nonempty (Proposition63FreshBalancedCellsData
      (sqrtScale := sqrtScale) planeMap original prepared
      original.extremal.delta_pos) := by
  let cap : ENNReal := 2 * (2 ^ prepared.level : ENNReal)
  have hcap : ∀ point,
      (prepared.refined.shading.pointMultiplicity point : ENNReal) ≤ cap := by
    intro point
    by_cases hpoint : point ∈ prepared.refined.shading.union
    · exact (prepared.multiplicity_upper point hpoint).le
    · have hzero : prepared.refined.shading.pointMultiplicity point = 0 := by
        simp only [Kakeya.Streamlined.Shading.pointMultiplicity]
        apply Finset.card_eq_zero.mpr
        rw [Finset.filter_eq_empty_iff]
        intro index _ hindex
        exact hpoint ⟨index, hindex⟩
      rw [hzero]
      norm_num
  have hboundarySmall :
      cap * ENNReal.ofReal (1000 * delta / sqrtScale) <
        prepared.refined.shading.mass := by
    exact (le_mul_of_one_le_left' (by norm_num : (1 : ENNReal) ≤ 2)).trans_lt
      (by simpa [cap, mul_assoc] using hboundary)
  rcases wz2_prop_sticky_boundary_cell_pruning
      original.extremal.delta_pos hdeltaSqrt hsqrtPos hsqrtOne
      prepared.refined.shading prepared.refined.extremal.cubical cap hcap
      hboundarySmall with ⟨pruning⟩
  have hcrossingUpper :=
    wz2_paper_boundary_crossing_mass_le_of_multiplicity_cap
      original.extremal.delta_pos hdeltaSqrt hsqrtPos hsqrtOne
      prepared.refined.shading prepared.refined.extremal.cubical cap hcap
  have hcrossingRegion : pruning.crossingRegion =
      wz2PaperBoundaryCrossingRegion
        (rho := sqrtScale) prepared.refined.shading
          original.extremal.delta_pos := by
    exact pruning.crossingRegion_eq_source
  rw [← hcrossingRegion] at hcrossingUpper
  have hcrossing :
      2 *
          (∑ index : Fin family.card,
            volume (prepared.refined.shading.carrier index ∩
              pruning.crossingRegion)) <
        prepared.refined.shading.mass := by
    calc
      2 *
          (∑ index : Fin family.card,
            volume (prepared.refined.shading.carrier index ∩
              pruning.crossingRegion)) ≤
          2 *
            (cap * ENNReal.ofReal (1000 * delta / sqrtScale)) := by
        gcongr
      _ < prepared.refined.shading.mass := by
        simpa [cap, mul_assoc] using hboundary
  have hsourcePruned : prepared.refined.shading.mass ≤
      2 * pruning.pruned.mass := by
    have hcrossingMassTop :
        (∑ index : Fin family.card,
          volume (prepared.refined.shading.carrier index ∩
            pruning.crossingRegion)) ≠ ⊤ := by
      apply ne_top_of_lt
      exact (le_mul_of_one_le_left' (by norm_num : (1 : ENNReal) ≤ 2)).trans_lt
        hcrossing
    have hcrossing' := hcrossing
    rw [pruning.source_mass_eq_crossing] at hcrossing'
    rw [pruning.source_mass_eq_crossing]
    have hcrossingLe :
        (∑ index : Fin family.card,
          volume (prepared.refined.shading.carrier index ∩
            pruning.crossingRegion)) ≤ pruning.pruned.mass := by
      by_contra hnot
      have hprunedCrossing := lt_of_not_ge hnot
      have : pruning.pruned.mass +
            (∑ index : Fin family.card,
              volume (prepared.refined.shading.carrier index ∩
                pruning.crossingRegion)) <
          2 *
            (∑ index : Fin family.card,
              volume (prepared.refined.shading.carrier index ∩
                pruning.crossingRegion)) := by
        calc
          _ < _ + _ := ENNReal.add_lt_add_right
            hcrossingMassTop hprunedCrossing
          _ = _ := by ring
      exact (not_lt_of_ge hcrossing'.le) this
    calc
      pruning.pruned.mass +
          (∑ index : Fin family.card,
            volume (prepared.refined.shading.carrier index ∩
              pruning.crossingRegion)) ≤
        pruning.pruned.mass + pruning.pruned.mass := by gcongr
      _ = 2 * pruning.pruned.mass := by ring
  exact proposition63_fresh_balancedCells_of_pruning planeMap original
    prepared hsqrtPos pruning hsourcePruned

/-- Paper-faithful non-aligned entry point.  Instead of estimating the grid
boundary by the pointwise multiplicity cap, use the top-level Convex-Wolff
boundary-layer bound on the whole ambient family and compare it with the
actual multiplicity-band mass. -/
theorem proposition63_fresh_balancedCells_of_cwa
    {delta sigma firstLoss preparedLoss queryScale sqrtScale : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source : WZ1PaperTubeShading family}
    (planeMap : Point3 → Point3)
    (original : PureWZ2OneScaleLocalGrainData
      (sigma := sigma) (outputLoss := firstLoss)
      (rho := queryScale) (Y := source) (fun point => planeMap point))
    (prepared : Proposition63OneScaleConstantMultiplicityData
      (secondLoss := preparedLoss) planeMap original)
    (hline : WZ1PaperIsLineClass family)
    (hdeltaSmall : delta ≤ 1 / 24)
    (hperiodicScale : 50 * delta ≤ sqrtScale)
    (hsqrtPos : 0 < sqrtScale)
    (hsqrtOne : sqrtScale ≤ 1)
    (hboundary :
      2 * (family.enncard *
        ((24000000 : ENNReal) *
          (Kakeya.realRpowENN delta (-preparedLoss) *
              wz2PaperBoundaryGeometryConstant + 1) *
          Kakeya.realRpowENN delta 2 *
          ENNReal.ofReal (Real.sqrt (delta / sqrtScale)))) <
        prepared.refined.shading.mass) :
    Nonempty (Proposition63FreshBalancedCellsData
      (sqrtScale := sqrtScale) planeMap original prepared
      original.extremal.delta_pos) := by
  let cap : ENNReal := 2 * (2 ^ prepared.level : ENNReal)
  have hcap : ∀ point,
      (prepared.refined.shading.pointMultiplicity point : ENNReal) ≤ cap := by
    intro point
    by_cases hpoint : point ∈ prepared.refined.shading.union
    · exact (prepared.multiplicity_upper point hpoint).le
    · have hzero : prepared.refined.shading.pointMultiplicity point = 0 := by
        simp only [Kakeya.Streamlined.Shading.pointMultiplicity]
        apply Finset.card_eq_zero.mpr
        rw [Finset.filter_eq_empty_iff]
        intro index _ hindex
        exact hpoint ⟨index, hindex⟩
      rw [hzero]
      norm_num
  have hdeltaSqrt : delta ≤ sqrtScale := by linarith
  have htwiceCrossingRaw :
      2 * (∑ index : Fin family.card,
          volume (prepared.refined.shading.carrier index ∩
            wz2PaperBoundaryCrossingRegion
              (rho := sqrtScale) prepared.refined.shading
                original.extremal.delta_pos)) <
        prepared.refined.shading.mass := by
    have hgrid := wz2_paper_grid_boundary_mass_normalized
      original.extremal.delta_pos hdeltaSmall hsqrtPos hsqrtOne
      hperiodicScale hline
      prepared.refined.shading prepared.refined.cwa
    let crossingCells := wz2PaperBoundaryCrossingFineCells
      (rho := sqrtScale) prepared.refined.shading
        original.extremal.delta_pos
    have hcrossingData : ∀ cell ∈ crossingCells,
        cell ∈ wz1PaperActiveCells prepared.refined.shading
            original.extremal.delta_pos ∧
          ¬ (wz1PaperGridCube delta cell ⊆
            wz1PaperGridCube sqrtScale
              (wz1PaperGridIndex sqrtScale (cellCorner delta cell))) := by
      intro cell hcell
      have hsplit := Finset.mem_sdiff.mp hcell
      refine ⟨hsplit.1, ?_⟩
      rw [wz2PaperBoundarySafeFineCells, Finset.mem_filter] at hsplit
      intro hcontain
      exact hsplit.2 ⟨hsplit.1, hcontain⟩
    have hcrossingSubset :
        wz2PaperBoundaryCrossingRegion
            (rho := sqrtScale) prepared.refined.shading
              original.extremal.delta_pos ⊆
          wz2PaperGridBoundaryRegion delta sqrtScale := by
      dsimp only [wz2PaperBoundaryCrossingRegion]
      exact wz2_paper_crossing_region_subset_grid_boundary
        prepared.refined.extremal.cubical original.extremal.delta_pos
        hsqrtPos crossingCells hcrossingData
    calc
      2 * (∑ index : Fin family.card,
          volume (prepared.refined.shading.carrier index ∩
            wz2PaperBoundaryCrossingRegion
              (rho := sqrtScale) prepared.refined.shading
                original.extremal.delta_pos)) ≤
          2 * (∑ index : Fin family.card,
            volume (prepared.refined.shading.carrier index ∩
              wz2PaperGridBoundaryRegion delta sqrtScale)) := by
        gcongr
      _ ≤ 2 * (family.enncard *
          ((24000000 : ENNReal) *
            (Kakeya.realRpowENN delta (-preparedLoss) *
                wz2PaperBoundaryGeometryConstant + 1) *
            Kakeya.realRpowENN delta 2 *
            ENNReal.ofReal (Real.sqrt (delta / sqrtScale)))) := by gcongr
      _ < prepared.refined.shading.mass := by
        exact hboundary
  have hcrossingMass :
      (∑ index : Fin family.card,
          volume (prepared.refined.shading.carrier index ∩
            wz2PaperBoundaryCrossingRegion
              (rho := sqrtScale) prepared.refined.shading
                original.extremal.delta_pos)) <
        prepared.refined.shading.mass :=
    (le_mul_of_one_le_left'
      (by norm_num : (1 : ENNReal) ≤ 2)).trans_lt htwiceCrossingRaw
  rcases wz2_paper_boundary_cell_pruning_of_crossing_mass
      original.extremal.delta_pos hdeltaSqrt hsqrtPos hsqrtOne
      prepared.refined.shading prepared.refined.extremal.cubical cap hcap
      hcrossingMass with ⟨pruning⟩
  have htwiceCrossing :
      2 *
          (∑ index : Fin family.card,
            volume (prepared.refined.shading.carrier index ∩
              pruning.crossingRegion)) <
        prepared.refined.shading.mass := by
    have hregion : pruning.crossingRegion =
        wz2PaperBoundaryCrossingRegion
          (rho := sqrtScale) prepared.refined.shading
            original.extremal.delta_pos :=
      pruning.crossingRegion_eq_source
    rw [hregion]
    exact htwiceCrossingRaw
  have hsourcePruned : prepared.refined.shading.mass ≤
      2 * pruning.pruned.mass := by
    have hcrossingTop :
        (∑ index : Fin family.card,
          volume (prepared.refined.shading.carrier index ∩
            pruning.crossingRegion)) ≠ ⊤ := by
      apply ne_top_of_lt
      exact (le_mul_of_one_le_left'
        (by norm_num : (1 : ENNReal) ≤ 2)).trans_lt htwiceCrossing
    have htwiceCrossing' := htwiceCrossing
    rw [pruning.source_mass_eq_crossing] at htwiceCrossing'
    rw [pruning.source_mass_eq_crossing]
    have hcrossingLe :
        (∑ index : Fin family.card,
          volume (prepared.refined.shading.carrier index ∩
            pruning.crossingRegion)) ≤ pruning.pruned.mass := by
      by_contra hnot
      have hprunedCrossing := lt_of_not_ge hnot
      have hsum : pruning.pruned.mass +
            (∑ index : Fin family.card,
              volume (prepared.refined.shading.carrier index ∩
                pruning.crossingRegion)) <
          2 *
            (∑ index : Fin family.card,
              volume (prepared.refined.shading.carrier index ∩
                pruning.crossingRegion)) := by
        calc
          _ < _ + _ := ENNReal.add_lt_add_right hcrossingTop hprunedCrossing
          _ = _ := by ring
      exact (not_lt_of_ge htwiceCrossing'.le) hsum
    calc
      pruning.pruned.mass +
          (∑ index : Fin family.card,
            volume (prepared.refined.shading.carrier index ∩
              pruning.crossingRegion)) ≤
        pruning.pruned.mass + pruning.pruned.mass := by gcongr
      _ = 2 * pruning.pruned.mass := by ring
  exact proposition63_fresh_balancedCells_of_pruning planeMap original
    prepared hsqrtPos pruning hsourcePruned

/-- Scalar form of the paper boundary absorption.  Cropped extremality
supplies `delta^(preparedLoss+2) * #family` mass, so the family cardinality
and tube-volume scale cancel from the CWA boundary estimate. -/
theorem proposition63_fresh_balancedCells_of_cwa_scalar
    {delta sigma firstLoss preparedLoss queryScale sqrtScale : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source : WZ1PaperTubeShading family}
    (planeMap : Point3 → Point3)
    (original : PureWZ2OneScaleLocalGrainData
      (sigma := sigma) (outputLoss := firstLoss)
      (rho := queryScale) (Y := source) (fun point => planeMap point))
    (prepared : Proposition63OneScaleConstantMultiplicityData
      (secondLoss := preparedLoss) planeMap original)
    (hline : WZ1PaperIsLineClass family)
    (hdeltaSmall : delta ≤ 1 / 24)
    (hperiodicScale : 50 * delta ≤ sqrtScale)
    (hsqrtPos : 0 < sqrtScale)
    (hsqrtOne : sqrtScale ≤ 1)
    (hscalar :
      2 * 24000000 *
          (Kakeya.realRpowENN delta (-preparedLoss) *
              wz2PaperBoundaryGeometryConstant + 1) *
          ENNReal.ofReal (Real.sqrt (delta / sqrtScale)) <
        Kakeya.realRpowENN delta preparedLoss) :
    Nonempty (Proposition63FreshBalancedCellsData
      (sqrtScale := sqrtScale) planeMap original prepared
      original.extremal.delta_pos) := by
  have hmassFloor :
      Kakeya.realRpowENN delta (preparedLoss + 2) * family.enncard ≤
        prepared.refined.shading.mass := by
    let all := Kakeya.Streamlined.TubeSubfamily.fromFinset family Finset.univ
    have h := selected_cardinality_cancellation prepared.refined.extremal
      hline all (hdeltaSmall.trans (by norm_num))
    simpa [all, Kakeya.Streamlined.TubeSubfamily.fromFinset,
      Kakeya.Streamlined.TubeFamily.enncard] using h
  have hscalePos : 0 < Kakeya.realRpowENN delta 2 * family.enncard := by
    apply ENNReal.mul_pos
    · exact (ENNReal.ofReal_pos.mpr
        (Real.rpow_pos_of_pos original.extremal.delta_pos 2)).ne'
    · simpa [Kakeya.Streamlined.TubeFamily.enncard] using
        prepared.refined.extremal.nonempty.ne'
  have hscaleTop : Kakeya.realRpowENN delta 2 * family.enncard ≠ ⊤ :=
    ENNReal.mul_ne_top (by simp [Kakeya.realRpowENN])
      (ENNReal.natCast_ne_top _)
  have hscaled := ENNReal.mul_lt_mul_left hscalePos.ne' hscaleTop hscalar
  have hboundary :
      2 * (family.enncard *
        ((24000000 : ENNReal) *
          (Kakeya.realRpowENN delta (-preparedLoss) *
              wz2PaperBoundaryGeometryConstant + 1) *
          Kakeya.realRpowENN delta 2 *
          ENNReal.ofReal (Real.sqrt (delta / sqrtScale)))) <
        prepared.refined.shading.mass := by
    apply lt_of_lt_of_le ?_ hmassFloor
    calc
      2 * (family.enncard *
          ((24000000 : ENNReal) *
            (Kakeya.realRpowENN delta (-preparedLoss) *
                wz2PaperBoundaryGeometryConstant + 1) *
            Kakeya.realRpowENN delta 2 *
            ENNReal.ofReal (Real.sqrt (delta / sqrtScale)))) =
          (2 * 24000000 *
            (Kakeya.realRpowENN delta (-preparedLoss) *
                wz2PaperBoundaryGeometryConstant + 1) *
            ENNReal.ofReal (Real.sqrt (delta / sqrtScale))) *
              (Kakeya.realRpowENN delta 2 * family.enncard) := by ring
      _ < Kakeya.realRpowENN delta preparedLoss *
          (Kakeya.realRpowENN delta 2 * family.enncard) := hscaled
      _ = Kakeya.realRpowENN delta (preparedLoss + 2) *
          family.enncard := by
        rw [realRpowENN_add original.extremal.delta_pos]
        ring
  exact proposition63_fresh_balancedCells_of_cwa planeMap original prepared
    hline hdeltaSmall hperiodicScale hsqrtPos hsqrtOne hboundary

namespace Proposition63FreshBalancedCellsData

/-- Repackage the freshly balanced shading as the exact
constant-multiplicity one-scale datum consumed by the line-hit construction.
The loss gap pays only the explicit boundary/equal-cell loss. -/
noncomputable def toConstantMultiplicity
    {delta sigma firstLoss middleLoss finalLoss queryScale sqrtScale : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source : WZ1PaperTubeShading family}
    {planeMap : Point3 → Point3}
    {original : PureWZ2OneScaleLocalGrainData
      (sigma := sigma) (outputLoss := firstLoss)
      (rho := queryScale) (Y := source) (fun point => planeMap point)}
    {prepared : Proposition63OneScaleConstantMultiplicityData
      (secondLoss := middleLoss) planeMap original}
    {hdelta : 0 < delta}
    (data : Proposition63FreshBalancedCellsData
      (sqrtScale := sqrtScale) planeMap original prepared hdelta)
    (hloss : middleLoss ≤ finalLoss)
    (hfinalLoss : 0 < finalLoss)
    (hslack : data.freshLoss * Kakeya.realRpowENN delta finalLoss ≤
      Kakeya.realRpowENN delta middleLoss) :
    Proposition63OneScaleConstantMultiplicityData
      (secondLoss := finalLoss) planeMap original := by
  have hsubPrepared : PaperIsSubshading data.balancing.refined
      prepared.refined.shading := fun index point hpoint =>
    data.pruning.pruned_subshading index
      (data.balancing.refined_subshading index hpoint)
  have hmassInv : data.freshLoss⁻¹ * prepared.refined.shading.mass ≤
      data.balancing.refined.mass := by
    exact (ENNReal.inv_mul_le_iff data.freshLoss_pos.ne'
      data.freshLoss_ne_top).2 data.prepared_mass_retention
  have hextremal : WZ2PaperCroppedIsExtremal sigma finalLoss family
      data.balancing.refined :=
    transfer_cropped_extremal_to_subshading data.freshLoss
      data.freshLoss_pos data.freshLoss_ne_top prepared.refined.extremal
      hsubPrepared hmassInv data.balancing.refined_cubical hloss hslack
      prepared.refined.extremal.delta_pos
      prepared.refined.extremal.delta_le_one hfinalLoss
  have hcwa : WZ2PaperConvexWolffBound family
      (Kakeya.realRpowENN delta (-finalLoss)) :=
    transfer_cwa_to_subshading
      (_shading1 := prepared.refined.shading)
      (_shading2 := data.balancing.refined)
      prepared.refined.cwa hloss
      prepared.refined.extremal.delta_pos
      prepared.refined.extremal.delta_le_one
  have hsubOriginal : PaperIsSubshading' data.balancing.refined
      original.shading := fun index point hpoint =>
    prepared.subshading_original index (hsubPrepared index hpoint)
  have hunionSubset : data.balancing.refined.union ⊆
      prepared.refined.shading.union := by
    rintro point ⟨index, hpoint⟩
    exact ⟨index, hsubPrepared index hpoint⟩
  have hlocal : ∀ point ∈ data.balancing.refined.union,
      IsADSet1
        (scalarProjection (planeMap point)
          (data.balancing.refined.union ∩
            Metric.closedBall point (Real.sqrt queryScale)))
        queryScale (1 - sigma)
        (Kakeya.realRpowENN delta (-finalLoss)) := by
    intro point hpoint
    have hsetSubset :
        scalarProjection (planeMap point)
            (data.balancing.refined.union ∩
              Metric.closedBall point (Real.sqrt queryScale)) ⊆
          scalarProjection (planeMap point)
            (prepared.refined.shading.union ∩
              Metric.closedBall point (Real.sqrt queryScale)) := by
      rintro value ⟨other, hother, rfl⟩
      exact ⟨other, ⟨hunionSubset hother.1, hother.2⟩, rfl⟩
    have hrestricted := (prepared.refined.local_ad point
      (hunionSubset hpoint)).mono hsetSubset
    have hconstant : Kakeya.realRpowENN delta (-middleLoss) ≤
        Kakeya.realRpowENN delta (-finalLoss) :=
      Kakeya.Assouad.realRpowENN_antitone
        prepared.refined.extremal.delta_pos
        prepared.refined.extremal.delta_le_one (by linarith)
    exact hrestricted.mono_constant hconstant
  let refined : PureWZ2OneScaleLocalGrainData
      (sigma := sigma) (outputLoss := finalLoss)
      (rho := queryScale) (Y := source) (fun point => planeMap point) :=
    { shading := data.balancing.refined
      subshading := fun index point hpoint =>
        original.subshading index (hsubOriginal index hpoint)
      extremal := hextremal
      cwa := hcwa
      local_ad := hlocal }
  exact
    { level := prepared.level
      refined := refined
      subshading_original := hsubOriginal
      multiplicity_lower := by
        intro point hpoint
        exact data.retention.refined_multiplicity_band point hpoint |>.1
      multiplicity_upper := by
        intro point hpoint
        have hband :=
          data.retention.refined_multiplicity_band point hpoint |>.2
        simpa [pow_succ, mul_comm] using hband
      preparationLoss := data.preparedLoss
      preparationLoss_pos := data.preparedLoss_pos
      preparationLoss_ne_top := data.preparedLoss_ne_top
      mass_retention := by
        simpa only [refined] using data.mass_retention }

end Proposition63FreshBalancedCellsData

/-- Fresh whole-cell balancing for an extremal shading before the one-scale
AD conclusion has been assembled.  This is the point-cover-native analogue
of `Proposition63FreshBalancedCellsData`. -/
structure Proposition63FreshBalancedExtremalCellsData
    {delta sigma firstLoss preparedLoss sqrtScale : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source : WZ1PaperTubeShading family}
    (original : Proposition63ExtremalShadingData
      (sigma := sigma) (outputLoss := firstLoss) source)
    (prepared : Proposition63ConstantMultiplicityShadingData
      (secondLoss := preparedLoss) original)
    (hdelta : 0 < delta) where
  multiplicityCap : ENNReal := 2 * (2 ^ prepared.level : ENNReal)
  pruning : WZ2PaperBoundaryCellPruningData
    (rho := sqrtScale) prepared.refined.shading hdelta multiplicityCap
  balancing : WZ2PaperExactCellBalancingData
    (rho := sqrtScale) pruning.pruned pruning.coarseCells
      pruning.availableFineCells
  retention : WZ2PaperExactBalancingMassRetentionData
    prepared.refined.shading hdelta multiplicityCap pruning balancing
      prepared.level
  freshLoss : ENNReal := proposition63FreshBalancingLoss pruning
  freshLoss_eq : freshLoss = proposition63FreshBalancingLoss pruning
  freshLoss_pos : 0 < freshLoss
  freshLoss_ne_top : freshLoss ≠ ⊤
  prepared_mass_retention : prepared.refined.shading.mass ≤
    freshLoss * balancing.refined.mass
  preparedLoss : ENNReal := prepared.preparationLoss * freshLoss
  preparedLoss_eq : preparedLoss = prepared.preparationLoss * freshLoss
  preparedLoss_pos : 0 < preparedLoss
  preparedLoss_ne_top : preparedLoss ≠ ⊤
  mass_retention : original.shading.mass ≤
    preparedLoss * balancing.refined.mass
  cells : Proposition63BalancedCellData (scale := sqrtScale)
    balancing.refined

/-- Complete exact balancing from an already prepared boundary pruning,
without assuming any local-AD field on the source. -/
theorem proposition63_fresh_balancedExtremalCells_of_pruning
    {delta sigma firstLoss preparedLoss sqrtScale : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source : WZ1PaperTubeShading family}
    (original : Proposition63ExtremalShadingData
      (sigma := sigma) (outputLoss := firstLoss) source)
    (prepared : Proposition63ConstantMultiplicityShadingData
      (secondLoss := preparedLoss) original)
    (hsqrtPos : 0 < sqrtScale)
    (pruning : WZ2PaperBoundaryCellPruningData
      (rho := sqrtScale) prepared.refined.shading original.extremal.delta_pos
        (2 * (2 ^ prepared.level : ENNReal)))
    (hsourcePruned : prepared.refined.shading.mass ≤
      2 * pruning.pruned.mass) :
    Nonempty (Proposition63FreshBalancedExtremalCellsData
      (sqrtScale := sqrtScale) original prepared
      original.extremal.delta_pos) := by
  let cap : ENNReal := 2 * (2 ^ prepared.level : ENNReal)
  rcases wz2_prop_sticky_exact_cell_balancing
      original.extremal.delta_pos hsqrtPos pruning.pruned
      pruning.pruned_cubical pruning.coarseCells
      pruning.coarseCells_nonempty pruning.availableFineCells
      pruning.availableFineCells_nonempty pruning.availableFineCells_ready with
    ⟨balancing⟩
  rcases wz2_paper_exact_balancing_mass_retention
      original.extremal.delta_pos prepared.refined.shading prepared.level
      (fun point hpoint =>
        ⟨prepared.multiplicity_lower point hpoint, by
          simpa [pow_succ, mul_comm] using
            prepared.multiplicity_upper point hpoint⟩)
      cap pruning balancing with
    ⟨retention⟩
  let freshLoss := proposition63FreshBalancingLoss pruning
  have hfreshPos : 0 < freshLoss := by
    dsimp only [freshLoss, proposition63FreshBalancingLoss]
    positivity
  have hfreshTop : freshLoss ≠ ⊤ := by
    exact ENNReal.mul_ne_top (by norm_num) <|
      ENNReal.mul_ne_top (by norm_num) (by simp)
  have hpreparedBalancing : prepared.refined.shading.mass ≤
      freshLoss * balancing.refined.mass := by
    calc
      prepared.refined.shading.mass ≤ 2 * pruning.pruned.mass :=
        hsourcePruned
      _ ≤ 2 *
          (((4 : ENNReal) *
            ((Nat.log 2
              (∑ cell ∈ pruning.coarseCells,
                (pruning.availableFineCells cell).card) + 1 : ℕ) : ENNReal)) *
              balancing.refined.mass) := by
        gcongr
        simpa using retention.mass_retention
      _ = freshLoss * balancing.refined.mass := by
        simp only [freshLoss, proposition63FreshBalancingLoss]
        ring
  let totalLoss := prepared.preparationLoss * freshLoss
  have htotalPos : 0 < totalLoss :=
    ENNReal.mul_pos prepared.preparationLoss_pos.ne' hfreshPos.ne'
  have htotalTop : totalLoss ≠ ⊤ :=
    ENNReal.mul_ne_top prepared.preparationLoss_ne_top hfreshTop
  have htotalMass : original.shading.mass ≤
      totalLoss * balancing.refined.mass := by
    calc
      original.shading.mass ≤ prepared.preparationLoss *
          prepared.refined.shading.mass := prepared.mass_retention
      _ ≤ prepared.preparationLoss *
          (freshLoss * balancing.refined.mass) := by gcongr
      _ = totalLoss * balancing.refined.mass := by
        simp only [totalLoss]
        ring
  exact ⟨{
    multiplicityCap := cap
    pruning := pruning
    balancing := balancing
    retention := retention
    freshLoss := freshLoss
    freshLoss_eq := rfl
    freshLoss_pos := hfreshPos
    freshLoss_ne_top := hfreshTop
    prepared_mass_retention := hpreparedBalancing
    preparedLoss := totalLoss
    preparedLoss_eq := rfl
    preparedLoss_pos := htotalPos
    preparedLoss_ne_top := htotalTop
    mass_retention := htotalMass
    cells := Proposition63BalancedCellData.ofExactBalancing balancing hsqrtPos
  }⟩

/-- A CWA boundary estimate produces fresh balanced cells without assuming
the one-scale AD conclusion which these cells will later help prove. -/
theorem proposition63_fresh_balancedExtremalCells_of_cwa_scalar
    {delta sigma firstLoss preparedLoss sqrtScale : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source : WZ1PaperTubeShading family}
    (original : Proposition63ExtremalShadingData
      (sigma := sigma) (outputLoss := firstLoss) source)
    (prepared : Proposition63ConstantMultiplicityShadingData
      (secondLoss := preparedLoss) original)
    (hline : WZ1PaperIsLineClass family)
    (hdeltaSmall : delta ≤ 1 / 24)
    (hperiodicScale : 50 * delta ≤ sqrtScale)
    (hsqrtPos : 0 < sqrtScale)
    (hsqrtOne : sqrtScale ≤ 1)
    (hscalar :
      2 * 24000000 *
          (Kakeya.realRpowENN delta (-preparedLoss) *
              wz2PaperBoundaryGeometryConstant + 1) *
          ENNReal.ofReal (Real.sqrt (delta / sqrtScale)) <
        Kakeya.realRpowENN delta preparedLoss) :
    Nonempty (Proposition63FreshBalancedExtremalCellsData
      (sqrtScale := sqrtScale) original prepared
      original.extremal.delta_pos) := by
  let cap : ENNReal := 2 * (2 ^ prepared.level : ENNReal)
  have hcap : ∀ point,
      (prepared.refined.shading.pointMultiplicity point : ENNReal) ≤ cap := by
    intro point
    by_cases hpoint : point ∈ prepared.refined.shading.union
    · exact (prepared.multiplicity_upper point hpoint).le
    · have hzero : prepared.refined.shading.pointMultiplicity point = 0 := by
        simp only [Kakeya.Streamlined.Shading.pointMultiplicity]
        apply Finset.card_eq_zero.mpr
        rw [Finset.filter_eq_empty_iff]
        intro index _ hindex
        exact hpoint ⟨index, hindex⟩
      rw [hzero]
      norm_num
  have hdeltaSqrt : delta ≤ sqrtScale := by linarith
  have htwiceCrossingRaw :
      2 * (∑ index : Fin family.card,
          volume (prepared.refined.shading.carrier index ∩
            wz2PaperBoundaryCrossingRegion
              (rho := sqrtScale) prepared.refined.shading
                original.extremal.delta_pos)) <
        prepared.refined.shading.mass := by
    have hgrid := wz2_paper_grid_boundary_mass_normalized
      original.extremal.delta_pos hdeltaSmall hsqrtPos hsqrtOne
      hperiodicScale hline prepared.refined.shading prepared.refined.cwa
    let crossingCells := wz2PaperBoundaryCrossingFineCells
      (rho := sqrtScale) prepared.refined.shading original.extremal.delta_pos
    have hcrossingData : ∀ cell ∈ crossingCells,
        cell ∈ wz1PaperActiveCells prepared.refined.shading
            original.extremal.delta_pos ∧
          ¬ (wz1PaperGridCube delta cell ⊆
            wz1PaperGridCube sqrtScale
              (wz1PaperGridIndex sqrtScale (cellCorner delta cell))) := by
      intro cell hcell
      have hsplit := Finset.mem_sdiff.mp hcell
      refine ⟨hsplit.1, ?_⟩
      rw [wz2PaperBoundarySafeFineCells, Finset.mem_filter] at hsplit
      intro hcontain
      exact hsplit.2 ⟨hsplit.1, hcontain⟩
    have hcrossingSubset :
        wz2PaperBoundaryCrossingRegion
            (rho := sqrtScale) prepared.refined.shading
              original.extremal.delta_pos ⊆
          wz2PaperGridBoundaryRegion delta sqrtScale := by
      dsimp only [wz2PaperBoundaryCrossingRegion]
      exact wz2_paper_crossing_region_subset_grid_boundary
        prepared.refined.extremal.cubical original.extremal.delta_pos
        hsqrtPos crossingCells hcrossingData
    calc
      2 * (∑ index : Fin family.card,
          volume (prepared.refined.shading.carrier index ∩
            wz2PaperBoundaryCrossingRegion
              (rho := sqrtScale) prepared.refined.shading
                original.extremal.delta_pos)) ≤
          2 * (∑ index : Fin family.card,
            volume (prepared.refined.shading.carrier index ∩
              wz2PaperGridBoundaryRegion delta sqrtScale)) := by
        gcongr
      _ ≤ 2 * (family.enncard *
          ((24000000 : ENNReal) *
            (Kakeya.realRpowENN delta (-preparedLoss) *
                wz2PaperBoundaryGeometryConstant + 1) *
            Kakeya.realRpowENN delta 2 *
            ENNReal.ofReal (Real.sqrt (delta / sqrtScale)))) := by gcongr
      _ < prepared.refined.shading.mass := by
        have hmassFloor : Kakeya.realRpowENN delta (preparedLoss + 2) *
            family.enncard ≤ prepared.refined.shading.mass := by
          let all := Kakeya.Streamlined.TubeSubfamily.fromFinset family
            Finset.univ
          have h := selected_cardinality_cancellation prepared.refined.extremal
            hline all (hdeltaSmall.trans (by norm_num))
          simpa [all, Kakeya.Streamlined.TubeSubfamily.fromFinset,
            Kakeya.Streamlined.TubeFamily.enncard] using h
        have hscalePos : 0 < Kakeya.realRpowENN delta 2 * family.enncard := by
          apply ENNReal.mul_pos
          · exact (ENNReal.ofReal_pos.mpr
              (Real.rpow_pos_of_pos original.extremal.delta_pos 2)).ne'
          · simpa [Kakeya.Streamlined.TubeFamily.enncard] using
              prepared.refined.extremal.nonempty.ne'
        have hscaleTop : Kakeya.realRpowENN delta 2 * family.enncard ≠ ⊤ :=
          ENNReal.mul_ne_top (by simp [Kakeya.realRpowENN])
            (ENNReal.natCast_ne_top _)
        have hscaled := ENNReal.mul_lt_mul_left
          hscalePos.ne' hscaleTop hscalar
        apply lt_of_lt_of_le ?_ hmassFloor
        calc
          2 * (family.enncard *
              ((24000000 : ENNReal) *
                (Kakeya.realRpowENN delta (-preparedLoss) *
                    wz2PaperBoundaryGeometryConstant + 1) *
                Kakeya.realRpowENN delta 2 *
                ENNReal.ofReal (Real.sqrt (delta / sqrtScale)))) =
              (2 * 24000000 *
                (Kakeya.realRpowENN delta (-preparedLoss) *
                    wz2PaperBoundaryGeometryConstant + 1) *
                ENNReal.ofReal (Real.sqrt (delta / sqrtScale))) *
                  (Kakeya.realRpowENN delta 2 * family.enncard) := by ring
          _ < Kakeya.realRpowENN delta preparedLoss *
              (Kakeya.realRpowENN delta 2 * family.enncard) := hscaled
          _ = Kakeya.realRpowENN delta (preparedLoss + 2) *
              family.enncard := by
            rw [realRpowENN_add original.extremal.delta_pos]
            ring
  have hcrossingMass :
      (∑ index : Fin family.card,
          volume (prepared.refined.shading.carrier index ∩
            wz2PaperBoundaryCrossingRegion
              (rho := sqrtScale) prepared.refined.shading
                original.extremal.delta_pos)) <
        prepared.refined.shading.mass :=
    (le_mul_of_one_le_left'
      (by norm_num : (1 : ENNReal) ≤ 2)).trans_lt htwiceCrossingRaw
  rcases wz2_paper_boundary_cell_pruning_of_crossing_mass
      original.extremal.delta_pos hdeltaSqrt hsqrtPos hsqrtOne
      prepared.refined.shading prepared.refined.extremal.cubical cap hcap
      hcrossingMass with
    ⟨pruning⟩
  have htwiceCrossing :
      2 * (∑ index : Fin family.card,
          volume (prepared.refined.shading.carrier index ∩
            pruning.crossingRegion)) < prepared.refined.shading.mass := by
    rw [pruning.crossingRegion_eq_source]
    exact htwiceCrossingRaw
  have hcrossingTop :
      (∑ index : Fin family.card,
          volume (prepared.refined.shading.carrier index ∩
            pruning.crossingRegion)) ≠ ⊤ := by
    apply ne_top_of_lt
    exact (le_mul_of_one_le_left'
      (by norm_num : (1 : ENNReal) ≤ 2)).trans_lt htwiceCrossing
  have hsourcePruned : prepared.refined.shading.mass ≤
      2 * pruning.pruned.mass := by
    have htwiceCrossing' := htwiceCrossing
    rw [pruning.source_mass_eq_crossing] at htwiceCrossing'
    rw [pruning.source_mass_eq_crossing]
    have hcrossingLe :
        (∑ index : Fin family.card,
          volume (prepared.refined.shading.carrier index ∩
            pruning.crossingRegion)) ≤ pruning.pruned.mass := by
      by_contra hnot
      have hprunedCrossing := lt_of_not_ge hnot
      have hsum : pruning.pruned.mass +
            (∑ index : Fin family.card,
              volume (prepared.refined.shading.carrier index ∩
                pruning.crossingRegion)) <
          2 * (∑ index : Fin family.card,
            volume (prepared.refined.shading.carrier index ∩
              pruning.crossingRegion)) := by
        calc
          _ < _ + _ := ENNReal.add_lt_add_right hcrossingTop
            hprunedCrossing
          _ = _ := by ring
      exact (not_lt_of_ge htwiceCrossing'.le) hsum
    calc
      pruning.pruned.mass +
          (∑ index : Fin family.card,
            volume (prepared.refined.shading.carrier index ∩
              pruning.crossingRegion)) ≤
        pruning.pruned.mass + pruning.pruned.mass := by gcongr
      _ = 2 * pruning.pruned.mass := by ring
  exact proposition63_fresh_balancedExtremalCells_of_pruning
    original prepared hsqrtPos pruning hsourcePruned

namespace Proposition63FreshBalancedExtremalCellsData

theorem freshLoss_le_envelope
    {delta sigma firstLoss preparedLoss sqrtScale : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source : WZ1PaperTubeShading family}
    {original : Proposition63ExtremalShadingData
      (sigma := sigma) (outputLoss := firstLoss) source}
    {prepared : Proposition63ConstantMultiplicityShadingData
      (secondLoss := preparedLoss) original}
    {hdelta : 0 < delta}
    (data : Proposition63FreshBalancedExtremalCellsData
      (sqrtScale := sqrtScale) original prepared hdelta) :
    data.freshLoss ≤ proposition63FreshBalancingEnvelope delta := by
  have hlog := wz2_paper_available_cell_log_bound_ennreal
    hdelta original.extremal.delta_le_one data.pruning
  rw [data.freshLoss_eq]
  unfold proposition63FreshBalancingLoss proposition63FreshBalancingEnvelope
  calc
    (2 : ENNReal) *
        (4 *
          ((Nat.log 2
            (∑ cell ∈ data.pruning.coarseCells,
              (data.pruning.availableFineCells cell).card) + 1 : ℕ) :
            ENNReal)) =
      8 *
        ((Nat.log 2
          (∑ cell ∈ data.pruning.coarseCells,
            (data.pruning.availableFineCells cell).card) + 1 : ℕ) :
          ENNReal) := by ring
    _ ≤ 8 * ENNReal.ofReal
        (wz2PaperBoundaryLogCoefficient * (1 + Real.log delta⁻¹)) := by
      gcongr

/-- Repackage fresh balancing as the final constant-multiplicity extremal
state used by the point-cover full-grain construction. -/
noncomputable def toConstantMultiplicity
    {delta sigma firstLoss middleLoss finalLoss sqrtScale : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source : WZ1PaperTubeShading family}
    {original : Proposition63ExtremalShadingData
      (sigma := sigma) (outputLoss := firstLoss) source}
    {prepared : Proposition63ConstantMultiplicityShadingData
      (secondLoss := middleLoss) original}
    {hdelta : 0 < delta}
    (data : Proposition63FreshBalancedExtremalCellsData
      (sqrtScale := sqrtScale) original prepared hdelta)
    (hloss : middleLoss ≤ finalLoss)
    (hfinalLoss : 0 < finalLoss)
    (hslack : data.freshLoss * Kakeya.realRpowENN delta finalLoss ≤
      Kakeya.realRpowENN delta middleLoss) :
    Proposition63ConstantMultiplicityShadingData
      (secondLoss := finalLoss) original := by
  have hsubPrepared : PaperIsSubshading data.balancing.refined
      prepared.refined.shading := fun index point hpoint =>
    data.pruning.pruned_subshading index
      (data.balancing.refined_subshading index hpoint)
  have hmassInv : data.freshLoss⁻¹ * prepared.refined.shading.mass ≤
      data.balancing.refined.mass :=
    (ENNReal.inv_mul_le_iff data.freshLoss_pos.ne'
      data.freshLoss_ne_top).2 data.prepared_mass_retention
  have hextremal : WZ2PaperCroppedIsExtremal sigma finalLoss family
      data.balancing.refined :=
    transfer_cropped_extremal_to_subshading data.freshLoss
      data.freshLoss_pos data.freshLoss_ne_top prepared.refined.extremal
      hsubPrepared hmassInv data.balancing.refined_cubical hloss hslack
      prepared.refined.extremal.delta_pos
      prepared.refined.extremal.delta_le_one hfinalLoss
  have hcwa : WZ2PaperConvexWolffBound family
      (Kakeya.realRpowENN delta (-finalLoss)) :=
    transfer_cwa_to_subshading
      (_shading1 := prepared.refined.shading)
      (_shading2 := data.balancing.refined) prepared.refined.cwa hloss
      prepared.refined.extremal.delta_pos
      prepared.refined.extremal.delta_le_one
  let refined : Proposition63ExtremalShadingData
      (sigma := sigma) (outputLoss := finalLoss) source :=
    { shading := data.balancing.refined
      subshading := fun index point hpoint =>
        original.subshading index <|
          prepared.subshading_original index <| hsubPrepared index hpoint
      extremal := hextremal
      cwa := hcwa }
  exact
    { level := prepared.level
      refined := refined
      subshading_original := fun index point hpoint =>
        prepared.subshading_original index <| hsubPrepared index hpoint
      multiplicity_lower := fun point hpoint =>
        (data.retention.refined_multiplicity_band point hpoint).1
      multiplicity_upper := by
        intro point hpoint
        have hband := data.retention.refined_multiplicity_band point hpoint |>.2
        simpa [pow_succ, mul_comm] using hband
      preparationLoss := data.preparedLoss
      preparationLoss_pos := data.preparedLoss_pos
      preparationLoss_ne_top := data.preparedLoss_ne_top
      mass_retention := by
        simpa only [refined] using data.mass_retention }

end Proposition63FreshBalancedExtremalCellsData

end Kakeya.Assouad.PureWZ2

end
