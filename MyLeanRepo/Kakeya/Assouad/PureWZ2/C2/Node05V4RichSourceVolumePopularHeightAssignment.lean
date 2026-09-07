import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Node05V4RichSourceVolumePopularEnvelope
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceCommonBinAnchoredTheorem52

/-!
# Assign final graph heights to genuine V4 source-volume-popular heights

If the graph carrier is built inside the complete source-cell envelope of the
preselected volume-popular band, every final Theorem-5.2 height is adjacent to
a genuine popular height index.  The assignment has fibres of size at most
three.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

private lemma v4_source_floor_sub_abs_le_one
    {x y : ℝ} (h : |x - y| ≤ 1) :
    |(Int.floor x : ℤ) - (Int.floor y : ℤ)| ≤ (1 : ℤ) := by
  have hxy : x - y ≤ 1 := (abs_le.mp h).2
  have hyx : y - x ≤ 1 := by linarith [(abs_le.mp h).1]
  have hforward : (Int.floor x : ℤ) - Int.floor y ≤ 1 := by
    by_contra hnot
    have hlower : (2 : ℤ) ≤ (Int.floor x : ℤ) - Int.floor y := by omega
    have hlowerReal : (2 : ℝ) ≤
        (Int.floor x : ℝ) - Int.floor y := by exact_mod_cast hlower
    have hfloorX : (Int.floor x : ℝ) ≤ x := Int.floor_le x
    have hyFloor : y < (Int.floor y : ℝ) + 1 := Int.lt_floor_add_one y
    linarith
  have hbackward : (Int.floor y : ℤ) - Int.floor x ≤ 1 := by
    by_contra hnot
    have hlower : (2 : ℤ) ≤ (Int.floor y : ℤ) - Int.floor x := by omega
    have hlowerReal : (2 : ℝ) ≤
        (Int.floor y : ℝ) - Int.floor x := by exact_mod_cast hlower
    have hfloorY : (Int.floor y : ℝ) ≤ y := Int.floor_le y
    have hxFloor : x < (Int.floor x : ℝ) + 1 := Int.lt_floor_add_one x
    linarith
  exact abs_le.mpr ⟨by linarith, hforward⟩

/-- Construction-independent bounded-fibre assignment. -/
structure PureWZ2Node05V4RichHeightAssignmentData
    (richHeights popularHeights : Finset ℤ) where
  assigned : ℤ → ℤ
  assigned_mem : ∀ heightIndex ∈ richHeights,
    assigned heightIndex ∈ popularHeights
  assigned_near : ∀ heightIndex ∈ richHeights,
    |heightIndex - assigned heightIndex| ≤ (1 : ℤ)
  assigned_fiber_card : ∀ popularHeight : ℤ,
    (richHeights.filter fun heightIndex =>
      assigned heightIndex = popularHeight).card ≤ 3

theorem pureWZ2Node05V4Rich_heightAssignment
    {richHeights popularHeights : Finset ℤ}
    (hnear : ∀ heightIndex ∈ richHeights,
      ∃ popularHeight ∈ popularHeights,
        |heightIndex - popularHeight| ≤ (1 : ℤ)) :
    Nonempty
      (PureWZ2Node05V4RichHeightAssignmentData richHeights popularHeights) := by
  let assigned : ℤ → ℤ := fun heightIndex =>
    if hheight : heightIndex ∈ richHeights then
      Classical.choose (hnear heightIndex hheight)
    else 0
  have hassignedMem : ∀ heightIndex ∈ richHeights,
      assigned heightIndex ∈ popularHeights := by
    intro heightIndex hheight
    simp only [assigned, dif_pos hheight]
    exact (Classical.choose_spec (hnear heightIndex hheight)).1
  have hassignedNear : ∀ heightIndex ∈ richHeights,
      |heightIndex - assigned heightIndex| ≤ (1 : ℤ) := by
    intro heightIndex hheight
    simp only [assigned, dif_pos hheight]
    exact (Classical.choose_spec (hnear heightIndex hheight)).2
  refine ⟨{
    assigned := assigned
    assigned_mem := hassignedMem
    assigned_near := hassignedNear
    assigned_fiber_card := ?_
  }⟩
  intro popularHeight
  have hsubset :
      richHeights.filter (fun heightIndex =>
          assigned heightIndex = popularHeight) ⊆
        Finset.Icc (popularHeight - 1) (popularHeight + 1) := by
    intro heightIndex hheight
    rw [Finset.mem_filter] at hheight
    rw [Finset.mem_Icc]
    have hnearAssigned := hassignedNear heightIndex hheight.1
    rw [hheight.2] at hnearAssigned
    have hb := abs_le.mp hnearAssigned
    omega
  have hcard :
      (Finset.Icc (popularHeight - 1) (popularHeight + 1)).card = 3 := by
    rw [Int.card_Icc]
    omega
  exact (Finset.card_le_card hsubset).trans_eq hcard

namespace PureWZ2Node05V4RichHeightAssignmentData

theorem assigned_image_subset
    {richHeights popularHeights : Finset ℤ}
    (assignment :
      PureWZ2Node05V4RichHeightAssignmentData richHeights popularHeights) :
    richHeights.image assignment.assigned ⊆ popularHeights := by
  intro popularHeight hheight
  rcases Finset.mem_image.mp hheight with ⟨heightIndex, hheightIndex, rfl⟩
  exact assignment.assigned_mem heightIndex hheightIndex

theorem rich_card_le_three_mul_assigned_card
    {richHeights popularHeights : Finset ℤ}
    (assignment :
      PureWZ2Node05V4RichHeightAssignmentData richHeights popularHeights) :
    richHeights.card ≤ 3 * (richHeights.image assignment.assigned).card := by
  rw [Finset.card_eq_sum_card_image assignment.assigned richHeights]
  calc
    (∑ popularHeight ∈ richHeights.image assignment.assigned,
        (richHeights.filter fun heightIndex =>
          assignment.assigned heightIndex = popularHeight).card) ≤
      ∑ _popularHeight ∈ richHeights.image assignment.assigned, 3 := by
        exact Finset.sum_le_sum fun popularHeight _ =>
          assignment.assigned_fiber_card popularHeight
    _ = 3 * (richHeights.image assignment.assigned).card := by
      simp [Finset.sum_const, Nat.mul_comm]

end PureWZ2Node05V4RichHeightAssignmentData

namespace PureWZ2AnchoredTheorem52Output

variable
    {deltaGraph graphScale sigma finalLoss : ℝ}
    {family : Kakeya.Streamlined.TubeFamily deltaGraph}
    {shadow : Kakeya.Streamlined.TubeShading family}
    {C : ENNReal}
    {input : PureWZ2AnchoredGraphGlobalInput
      (rho := graphScale) (sigma := sigma) shadow C}
    {prep : PureWZ2AnchoredGraphPreparationData input}
    {localBins : WZ1Lemma23LocalBinPackage
      (rho := graphScale) (sigma := sigma) C prep.windowed.global.cells}
    {finiteGraph : PureWZ2AnchoredFiniteGraphData prep localBins}
    {projection : PureWZ2SourceHorizontalProjectionThreshold sigma finalLoss}
    (output : PureWZ2AnchoredTheorem52Output finiteGraph projection)

def richHeightIndex (point : Point2) : ℤ :=
  (output.lineData.graphCell point).2.2

def richHeightIndices : Finset ℤ :=
  output.lineData.richF.image output.richHeightIndex

theorem richHeightIndices_card :
    output.richHeightIndices.card = output.lineData.richF.card := by
  apply Finset.card_image_of_injOn
  intro first hfirst second hsecond heq
  apply output.lineData.sourceHeight_injective hfirst hsecond
  rw [output.lineData.sourceHeight_eq, output.lineData.sourceHeight_eq]
  change
    (wz1Lemma23SnappedPoint graphScale
      (output.lineData.graphCell first)) (2 : Fin 3) =
    (wz1Lemma23SnappedPoint graphScale
      (output.lineData.graphCell second)) (2 : Fin 3)
  change (output.lineData.graphCell first).2.2 =
    (output.lineData.graphCell second).2.2 at heq
  simp [wz1Lemma23SnappedPoint, wz1Lemma23CellCenter, point3, heq]

end PureWZ2AnchoredTheorem52Output

/-- Every rich graph height is adjacent to a genuinely source-volume-popular
height when graph representatives lie in the complete popular envelope. -/
theorem pureWZ2Node05V4Rich_richHeights_near_sourceVolumePopular
    {capability : PureWZ2PropStickyCapability}
    {sigma inputLoss delta rho stickyLoss finalLoss : ℝ}
    {schedule : PureWZ2Node05V4RichSecondCallSchedule sigma stickyLoss}
    {current : PureWZ2ReentrantGrainSource
      sigma inputLoss delta capability.normalizationExponent}
    {rhoRequested : WZ2PaperRequestedScale delta}
    {inputLossLe :
      inputLoss ≤ (schedule.firstCallSchedule capability).kernel.sourceLoss}
    {sqrtRequested : WZ2PaperRequestedScale rhoRequested.1}
    {twoScale : PureWZ2Node05V4RichSecondCallData
      schedule current rhoRequested inputLossLe sqrtRequested}
    {pullback : PureWZ2Node05V4RichTwoScaleCellPullbackData
      (rho := rho) twoScale}
    {heightIndex : {heightIndex //
      heightIndex ∈ pureWZ2Node05V4RichHeavySlabs pullback}}
    {popular :
      PureWZ2Node05V4RichSourceVolumePopularHeightData pullback heightIndex}
    (_popularEnvelope :
      PureWZ2Node05V4RichSourceVolumePopularEnvelopeData popular)
    {deltaGraph graphScale : ℝ}
    {family : Kakeya.Streamlined.TubeFamily deltaGraph}
    {shadow : Kakeya.Streamlined.TubeShading family}
    {C : ENNReal}
    {input : PureWZ2AnchoredGraphGlobalInput
      (rho := graphScale) (sigma := sigma) shadow C}
    {prep : PureWZ2AnchoredGraphPreparationData input}
    {localBins : WZ1Lemma23LocalBinPackage
      (rho := graphScale) (sigma := sigma) C prep.windowed.global.cells}
    {finiteGraph : PureWZ2AnchoredFiniteGraphData prep localBins}
    {projection : PureWZ2SourceHorizontalProjectionThreshold sigma finalLoss}
    (output : PureWZ2AnchoredTheorem52Output finiteGraph projection)
    (hscale : graphScale = 256 * rho)
    (representative : WZ2PaperCellIndex → Point3)
    (representative_mem :
      ∀ cell ∈ prep.windowed.global.cells, representative cell ∈ shadow.union)
    (representative_index :
      ∀ cell ∈ prep.windowed.global.cells,
        wz1Lemma23CellIndex graphScale (representative cell) = cell)
    (hcarrier :
      ∀ point ∈ shadow.union,
        ∃ anchor ∈ popular.popular.heightRegion,
          dist point anchor < 2 * rho) :
    ∀ graphHeight ∈ output.richHeightIndices,
      ∃ popularHeight ∈ popular.popular.heightIndices,
        |graphHeight - popularHeight| ≤ (1 : ℤ) := by
  intro graphHeight hgraphHeight
  rw [PureWZ2AnchoredTheorem52Output.richHeightIndices] at hgraphHeight
  rcases Finset.mem_image.mp hgraphHeight with
    ⟨richPoint, hrichPoint, hgraphHeightEq⟩
  let cell := output.lineData.graphCell richPoint
  have hcellResidue :=
    output.lineData.graphCell_mem_residue richPoint hrichPoint
  have hcellGlobal := finiteGraph.graph.residue.cells_subset hcellResidue
  have hrepresentative := representative_mem cell hcellGlobal
  rcases hcarrier (representative cell) hrepresentative with
    ⟨anchor, hanchor, hnear⟩
  rw [popular.popular.heightRegion_eq] at hanchor
  rcases Set.mem_iUnion₂.mp hanchor with
    ⟨popularHeight, hpopularHeight, hslab⟩
  refine ⟨popularHeight, hpopularHeight, ?_⟩
  have hfloorPopular := (wz1Lemma23_mem_heightSlab_iff
    popular.popular.graphScale_pos popularHeight anchor).mp hslab
  have hcellHeight := congrArg
    (fun index : WZ2PaperCellIndex => index.2.2)
    (representative_index cell hcellGlobal)
  have hfloorCell :
      Int.floor
          (representative cell (2 : Fin 3) /
            gridSide ((256 * rho) / 2)) = cell.2.2 := by
    rw [← hscale]
    simpa [wz1Lemma23CellIndex, rhoGridIndex, gridIndex] using hcellHeight
  have hrho : 0 < rho := by
    rw [← pullback.rhoRequested_eq]
    exact twoScale.first.publicSticky.coarse_extremal.delta_pos
  let width := gridSide ((256 * rho) / 2)
  have hwidth : 0 < width := by
    dsimp only [width, gridSide]
    positivity
  have hsqrtThreePos : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have hnearWidth : 2 * rho ≤ width := by
    change 2 * rho ≤ 2 * ((256 * rho) / 2) / Real.sqrt 3
    rw [le_div_iff₀ hsqrtThreePos]
    have hsqrtThreeLe : Real.sqrt 3 ≤ 2 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    nlinarith
  have hcoordinate :
      |representative cell (2 : Fin 3) - anchor (2 : Fin 3)| < 2 * rho := by
    have hcoordinateLe := PiLp.dist_apply_le
      (representative cell) anchor (2 : Fin 3)
    have hcoordinateLe' :
        |representative cell (2 : Fin 3) - anchor (2 : Fin 3)| ≤
          dist (representative cell) anchor := by
      simpa [Real.dist_eq] using hcoordinateLe
    exact hcoordinateLe'.trans_lt hnear
  have hscaled :
      |representative cell (2 : Fin 3) / width -
          anchor (2 : Fin 3) / width| ≤ 1 := by
    rw [show representative cell (2 : Fin 3) / width -
        anchor (2 : Fin 3) / width =
          (representative cell (2 : Fin 3) - anchor (2 : Fin 3)) / width by
      ring]
    rw [abs_div, abs_of_pos hwidth]
    calc
      _ ≤ width / width := by
        gcongr
        exact hcoordinate.le.trans hnearWidth
      _ = 1 := div_self hwidth.ne'
  have hfloor := v4_source_floor_sub_abs_le_one hscaled
  have hfloorGraph :
      Int.floor (representative cell (2 : Fin 3) / width) = graphHeight := by
    have hheightEq : cell.2.2 = graphHeight := by
      simpa [cell,
        PureWZ2AnchoredTheorem52Output.richHeightIndex] using hgraphHeightEq
    have hfloorCell' :
        Int.floor (representative cell (2 : Fin 3) / width) = cell.2.2 := by
      simpa [width] using hfloorCell
    exact hfloorCell'.trans hheightEq
  have hfloorPopular' :
      Int.floor (anchor (2 : Fin 3) / width) = popularHeight := by
    simpa [width] using hfloorPopular
  simpa [hfloorGraph, hfloorPopular'] using hfloor

/-- Package the nearby assignment with fibres bounded by three. -/
theorem pureWZ2Node05V4Rich_sourceVolumePopularHeightAssignment
    {capability : PureWZ2PropStickyCapability}
    {sigma inputLoss delta rho stickyLoss finalLoss : ℝ}
    {schedule : PureWZ2Node05V4RichSecondCallSchedule sigma stickyLoss}
    {current : PureWZ2ReentrantGrainSource
      sigma inputLoss delta capability.normalizationExponent}
    {rhoRequested : WZ2PaperRequestedScale delta}
    {inputLossLe :
      inputLoss ≤ (schedule.firstCallSchedule capability).kernel.sourceLoss}
    {sqrtRequested : WZ2PaperRequestedScale rhoRequested.1}
    {twoScale : PureWZ2Node05V4RichSecondCallData
      schedule current rhoRequested inputLossLe sqrtRequested}
    {pullback : PureWZ2Node05V4RichTwoScaleCellPullbackData
      (rho := rho) twoScale}
    {heightIndex : {heightIndex //
      heightIndex ∈ pureWZ2Node05V4RichHeavySlabs pullback}}
    {popular :
      PureWZ2Node05V4RichSourceVolumePopularHeightData pullback heightIndex}
    (popularEnvelope :
      PureWZ2Node05V4RichSourceVolumePopularEnvelopeData popular)
    {deltaGraph graphScale : ℝ}
    {family : Kakeya.Streamlined.TubeFamily deltaGraph}
    {shadow : Kakeya.Streamlined.TubeShading family}
    {C : ENNReal}
    {input : PureWZ2AnchoredGraphGlobalInput
      (rho := graphScale) (sigma := sigma) shadow C}
    {prep : PureWZ2AnchoredGraphPreparationData input}
    {localBins : WZ1Lemma23LocalBinPackage
      (rho := graphScale) (sigma := sigma) C prep.windowed.global.cells}
    {finiteGraph : PureWZ2AnchoredFiniteGraphData prep localBins}
    {projection : PureWZ2SourceHorizontalProjectionThreshold sigma finalLoss}
    (output : PureWZ2AnchoredTheorem52Output finiteGraph projection)
    (hscale : graphScale = 256 * rho)
    (representative : WZ2PaperCellIndex → Point3)
    (representative_mem :
      ∀ cell ∈ prep.windowed.global.cells, representative cell ∈ shadow.union)
    (representative_index :
      ∀ cell ∈ prep.windowed.global.cells,
        wz1Lemma23CellIndex graphScale (representative cell) = cell)
    (hcarrier :
      ∀ point ∈ shadow.union,
        ∃ anchor ∈ popular.popular.heightRegion,
          dist point anchor < 2 * rho) :
    Nonempty
      (PureWZ2Node05V4RichHeightAssignmentData
        output.richHeightIndices popular.popular.heightIndices) := by
  apply pureWZ2Node05V4Rich_heightAssignment
  exact pureWZ2Node05V4Rich_richHeights_near_sourceVolumePopular
    popularEnvelope output hscale representative representative_mem
      representative_index hcarrier

/-- Original-family source mass on the genuinely volume-popular heights
assigned to the final rich graph heights. -/
structure PureWZ2Node05V4RichAssignedSourceMassData
    {capability : PureWZ2PropStickyCapability}
    {sigma inputLoss delta rho stickyLoss finalLoss : ℝ}
    {schedule : PureWZ2Node05V4RichSecondCallSchedule sigma stickyLoss}
    {current : PureWZ2ReentrantGrainSource
      sigma inputLoss delta capability.normalizationExponent}
    {rhoRequested : WZ2PaperRequestedScale delta}
    {inputLossLe :
      inputLoss ≤ (schedule.firstCallSchedule capability).kernel.sourceLoss}
    {sqrtRequested : WZ2PaperRequestedScale rhoRequested.1}
    {twoScale : PureWZ2Node05V4RichSecondCallData
      schedule current rhoRequested inputLossLe sqrtRequested}
    {pullback : PureWZ2Node05V4RichTwoScaleCellPullbackData
      (rho := rho) twoScale}
    {heightIndex : {heightIndex //
      heightIndex ∈ pureWZ2Node05V4RichHeavySlabs pullback}}
    (popular :
      PureWZ2Node05V4RichSourceVolumePopularHeightData pullback heightIndex)
    {deltaGraph graphScale : ℝ}
    {family : Kakeya.Streamlined.TubeFamily deltaGraph}
    {shadow : Kakeya.Streamlined.TubeShading family}
    {C : ENNReal}
    {input : PureWZ2AnchoredGraphGlobalInput
      (rho := graphScale) (sigma := sigma) shadow C}
    {prep : PureWZ2AnchoredGraphPreparationData input}
    {localBins : WZ1Lemma23LocalBinPackage
      (rho := graphScale) (sigma := sigma) C prep.windowed.global.cells}
    {finiteGraph : PureWZ2AnchoredFiniteGraphData prep localBins}
    {projection : PureWZ2SourceHorizontalProjectionThreshold sigma finalLoss}
    (output : PureWZ2AnchoredTheorem52Output finiteGraph projection)
    (assignment : PureWZ2Node05V4RichHeightAssignmentData
      output.richHeightIndices popular.popular.heightIndices) where
  assignedHeights : Finset ℤ :=
    output.richHeightIndices.image assignment.assigned
  assignedHeights_eq :
    assignedHeights = output.richHeightIndices.image assignment.assigned
  assignedHeights_subset :
    assignedHeights ⊆ popular.popular.heightIndices
  richHeight_card_le :
    output.richHeightIndices.card ≤ 3 * assignedHeights.card
  assignedRegion : Set Point3 :=
    ⋃ heightIndex ∈ assignedHeights,
      wz1Lemma23HeightSlab graphScale heightIndex
  assignedRegion_eq :
    assignedRegion =
      ⋃ heightIndex ∈ assignedHeights,
        wz1Lemma23HeightSlab graphScale heightIndex
  graphScale_eq : graphScale = 256 * rho
  assignedRegion_subset_popular :
    assignedRegion ⊆ popular.popular.heightRegion
  shading : WZ1PaperTubeShading current.grain.family
  carrier_eq : ∀ index,
    shading.carrier index =
      popular.sourcePopularShading.carrier index ∩
        assignedRegion
  subshading_sourcePopular :
    PureWZ2PaperIsSubshading shading popular.sourcePopularShading
  subshading_slab :
    PureWZ2PaperIsSubshading shading
      (pullback.standardSqrtSlabSourceShading heightIndex.1.1)
  subshading_current :
    PureWZ2PaperIsSubshading shading current.grain.shading
  union_eq :
    shading.union =
      popular.sourcePopularShading.union ∩
        assignedRegion
  source_height_mem_ZS :
    ∀ point ∈ shading.union,
      point (2 : Fin 3) ∈ popular.continuous.popularHeights
  constantMultiplicity :
    shading.HasConstantMultiplicity
      (twoScale.first.fourDegreeReceipts.fineDegreeFloor *
        twoScale.first.fourDegreeReceipts.muFine)
      ((twoScale.first.fourDegreeReceipts.regularity *
        twoScale.first.fourDegreeReceipts.fineDegreeFloor) *
          twoScale.first.fourDegreeReceipts.muFine)
  rich_mass_lower :
    (((twoScale.first.fourDegreeReceipts.fineDegreeFloor *
          twoScale.first.fourDegreeReceipts.muFine : ℕ) : ENNReal) *
      ((output.richHeightIndices.card : ENNReal) *
        popular.popular.layerMass)) ≤
      3 * shading.mass

theorem pureWZ2Node05V4Rich_assignedSourceMass
    {capability : PureWZ2PropStickyCapability}
    {sigma inputLoss delta rho stickyLoss finalLoss : ℝ}
    {schedule : PureWZ2Node05V4RichSecondCallSchedule sigma stickyLoss}
    {current : PureWZ2ReentrantGrainSource
      sigma inputLoss delta capability.normalizationExponent}
    {rhoRequested : WZ2PaperRequestedScale delta}
    {inputLossLe :
      inputLoss ≤ (schedule.firstCallSchedule capability).kernel.sourceLoss}
    {sqrtRequested : WZ2PaperRequestedScale rhoRequested.1}
    {twoScale : PureWZ2Node05V4RichSecondCallData
      schedule current rhoRequested inputLossLe sqrtRequested}
    {pullback : PureWZ2Node05V4RichTwoScaleCellPullbackData
      (rho := rho) twoScale}
    {heightIndex : {heightIndex //
      heightIndex ∈ pureWZ2Node05V4RichHeavySlabs pullback}}
    (popular :
      PureWZ2Node05V4RichSourceVolumePopularHeightData pullback heightIndex)
    {deltaGraph graphScale : ℝ}
    {family : Kakeya.Streamlined.TubeFamily deltaGraph}
    {shadow : Kakeya.Streamlined.TubeShading family}
    {C : ENNReal}
    {input : PureWZ2AnchoredGraphGlobalInput
      (rho := graphScale) (sigma := sigma) shadow C}
    {prep : PureWZ2AnchoredGraphPreparationData input}
    {localBins : WZ1Lemma23LocalBinPackage
      (rho := graphScale) (sigma := sigma) C prep.windowed.global.cells}
    {finiteGraph : PureWZ2AnchoredFiniteGraphData prep localBins}
    {projection : PureWZ2SourceHorizontalProjectionThreshold sigma finalLoss}
    (output : PureWZ2AnchoredTheorem52Output finiteGraph projection)
    (assignment : PureWZ2Node05V4RichHeightAssignmentData
      output.richHeightIndices popular.popular.heightIndices)
    (hscale : graphScale = 256 * rho) :
    Nonempty
      (PureWZ2Node05V4RichAssignedSourceMassData popular output assignment) := by
  let assignedHeights := output.richHeightIndices.image assignment.assigned
  let assignedRegion : Set Point3 :=
    ⋃ heightIndex ∈ assignedHeights,
      wz1Lemma23HeightSlab graphScale heightIndex
  have hregionMeas : MeasurableSet assignedRegion :=
    MeasurableSet.biUnion assignedHeights.finite_toSet.countable
      (fun heightIndex _ => by
        change MeasurableSet ((fun point : Point3 => point 2) ⁻¹'
          wz1Lemma23HeightInterval graphScale heightIndex)
        exact measurableSet_Ico.preimage
          (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) 2).measurable)
  let slabShading := popular.sourcePopularShading
  let shading : WZ1PaperTubeShading current.grain.family :=
    { carrier := fun index => slabShading.carrier index ∩ assignedRegion
      measurable_carrier := fun index =>
        (slabShading.measurable_carrier index).inter hregionMeas
      subset_body := fun index => Set.inter_subset_left.trans
        (slabShading.subset_body index) }
  have hunion :
      shading.union = slabShading.union ∩ assignedRegion := by
    ext point
    constructor
    · rintro ⟨index, hslab, hregion⟩
      exact ⟨⟨index, hslab⟩, hregion⟩
    · rintro ⟨⟨index, hslab⟩, hregion⟩
      exact ⟨index, hslab, hregion⟩
  have hconstant :
      shading.HasConstantMultiplicity
        (twoScale.first.fourDegreeReceipts.fineDegreeFloor *
          twoScale.first.fourDegreeReceipts.muFine)
        ((twoScale.first.fourDegreeReceipts.regularity *
          twoScale.first.fourDegreeReceipts.fineDegreeFloor) *
            twoScale.first.fourDegreeReceipts.muFine) := by
    have hfull :=
      pullback.standardSqrtSlabSourceShading_constantMultiplicity
        heightIndex.1.1
    intro point hpoint
    have hmultiplicityAssigned := wholeCellRestriction_pointMultiplicity_eq
      (fun index => show shading.carrier index =
        slabShading.carrier index ∩ assignedRegion from rfl) hpoint
    have hpointSource : point ∈ popular.sourcePopularShading.union := by
      rcases hpoint with ⟨index, hindex⟩
      exact ⟨index, hindex.1⟩
    have hmultiplicityZS := wholeCellRestriction_pointMultiplicity_eq
      (fun index => popular.sourcePopularShading_carrier index) hpointSource
    rw [hmultiplicityAssigned, hmultiplicityZS]
    exact hfull point
      (popular.sourcePopularShading_sub_slab.union_subset hpointSource)
  have hassignedSubset :
      assignedHeights ⊆ popular.popular.heightIndices :=
    assignment.assigned_image_subset
  have hregionSubset :
      assignedRegion ⊆ popular.popular.heightRegion := by
    intro point hpoint
    rcases Set.mem_iUnion₂.mp hpoint with
      ⟨selectedHeight, hselectedHeight, hpointSlab⟩
    rw [popular.popular.heightRegion_eq]
    refine Set.mem_iUnion₂.mpr
      ⟨selectedHeight, hassignedSubset hselectedHeight, ?_⟩
    simpa [hscale] using hpointSlab
  have hvolume :
      ((assignedHeights.card : ENNReal) * popular.popular.layerMass) ≤
        volume shading.union := by
    rw [hunion]
    have hpartition :
        slabShading.union ∩ assignedRegion =
          ⋃ heightIndex ∈ assignedHeights,
            slabShading.union ∩
              wz1Lemma23HeightSlab graphScale heightIndex := by
      ext point
      simp [assignedRegion]
    rw [hpartition]
    rw [MeasureTheory.measure_biUnion_finset]
    · calc
        (assignedHeights.card : ENNReal) * popular.popular.layerMass =
            ∑ _heightIndex ∈ assignedHeights,
              popular.popular.layerMass := by simp [Finset.sum_const]
        _ ≤ ∑ heightIndex ∈ assignedHeights,
            volume (slabShading.union ∩
              wz1Lemma23HeightSlab graphScale heightIndex) := by
          apply Finset.sum_le_sum
          intro selectedHeight hselectedHeight
          have hpopular :
              selectedHeight ∈ popular.popular.heightIndices :=
            assignment.assigned_image_subset hselectedHeight
          have hband :=
            popular.popular.layer_volume_band selectedHeight hpopular
          simpa [slabShading, hscale] using hband.1
    · intro first _ second _ hne
      exact (wz1Lemma23_heightSlab_disjoint
        (by
          rw [hscale]
          have hrho : 0 < rho := by
            rw [← pullback.rhoRequested_eq]
            exact twoScale.first.publicSticky.coarse_extremal.delta_pos
          positivity) hne).mono
        Set.inter_subset_right Set.inter_subset_right
    · intro selectedHeight _
      exact (measurableSet_shading_union slabShading).inter (by
        change MeasurableSet ((fun point : Point3 => point 2) ⁻¹'
          wz1Lemma23HeightInterval graphScale selectedHeight)
        exact measurableSet_Ico.preimage
          (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) 2).measurable)
  have hmass :
      (((twoScale.first.fourDegreeReceipts.fineDegreeFloor *
            twoScale.first.fourDegreeReceipts.muFine : ℕ) : ENNReal) *
        ((assignedHeights.card : ENNReal) * popular.popular.layerMass)) ≤
          shading.mass := by
    calc
      _ ≤ ((twoScale.first.fourDegreeReceipts.fineDegreeFloor *
            twoScale.first.fourDegreeReceipts.muFine : ℕ) : ENNReal) *
          volume shading.union := by gcongr
      _ ≤ shading.mass := by
        apply multiplicity_floor_le_mass
        intro point hpoint
        exact_mod_cast (hconstant point hpoint).1
  have hcardNat := assignment.rich_card_le_three_mul_assigned_card
  have hcard :
      (output.richHeightIndices.card : ENNReal) ≤
        3 * (assignedHeights.card : ENNReal) := by
    exact_mod_cast hcardNat
  have hrichMass :
      (((twoScale.first.fourDegreeReceipts.fineDegreeFloor *
            twoScale.first.fourDegreeReceipts.muFine : ℕ) : ENNReal) *
        ((output.richHeightIndices.card : ENNReal) *
          popular.popular.layerMass)) ≤
        3 * shading.mass := by
    calc
      _ ≤ ((twoScale.first.fourDegreeReceipts.fineDegreeFloor *
            twoScale.first.fourDegreeReceipts.muFine : ℕ) : ENNReal) *
          ((3 * (assignedHeights.card : ENNReal)) *
            popular.popular.layerMass) := by gcongr
      _ = 3 * (((twoScale.first.fourDegreeReceipts.fineDegreeFloor *
            twoScale.first.fourDegreeReceipts.muFine : ℕ) : ENNReal) *
          ((assignedHeights.card : ENNReal) *
            popular.popular.layerMass)) := by ring
      _ ≤ 3 * shading.mass := by gcongr
  exact ⟨{
    assignedHeights := assignedHeights
    assignedHeights_eq := rfl
    assignedHeights_subset := hassignedSubset
    richHeight_card_le := hcardNat
    assignedRegion := assignedRegion
    assignedRegion_eq := rfl
    graphScale_eq := hscale
    assignedRegion_subset_popular := hregionSubset
    shading := shading
    carrier_eq := fun _ => rfl
    subshading_sourcePopular := fun _ => Set.inter_subset_left
    subshading_slab := fun _ => Set.inter_subset_left
      |>.trans (popular.sourcePopularShading_sub_slab _)
    subshading_current := fun index =>
      Set.inter_subset_left.trans
        (popular.sourcePopularShading_sub_slab index) |>.trans
          (pullback.standardSqrtSlabSourceShading_sub_source
            heightIndex.1.1 index)
    union_eq := hunion
    source_height_mem_ZS := by
      intro point hpoint
      rw [hunion] at hpoint
      rw [popular.sourcePopularShading_union,
        popular.continuous.popularRegion_eq,
        PureWZ2Node05V4RichTwoScaleCellPullbackData.sourcePopularRegion,
        ← popular.continuous.popularHeights_eq] at hpoint
      exact hpoint.1.2
    constantMultiplicity := hconstant
    rich_mass_lower := hrichMass
  }⟩

end Kakeya.Assouad

end
