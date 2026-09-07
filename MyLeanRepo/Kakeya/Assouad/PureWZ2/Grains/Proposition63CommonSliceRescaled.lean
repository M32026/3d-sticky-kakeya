import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.CommonSliceAxialAssembly
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63RescaledMetricFiber
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.LocalGrainRestriction

/-!
# Common-slice and unit rescaling in Proposition 6.3

This is the dependent package corresponding to the paragraph after the
metric-fibre selection in `wz2_63.tex`.  The common-slice refinement is made
on the original selected fibre.  Its literal image is then refreshed on the
same frozen Node 3 family and rescaling certificate, and extremality is
rebuilt from the retained source density.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

attribute [local instance] Classical.propDecidable

/-- The frozen literal map multiplies the longitudinal coordinate by
`1 / 100`.  Hence a paper interval of length `Delta` has this width in the
literal target coordinates. -/
def proposition63LiteralSliceWidth (Delta : ℝ) : ℝ := Delta / 100

/-- The paper's common-slice shading together with its refreshed unit
rescaling and the restricted local-grain data on the original fibre. -/
structure Proposition63CommonSliceRescaledData
    {delta rho Delta sigma stickyLoss localLoss targetLoss coefficient : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    {original : PureWZ2BalancedCoverData cover fineShading coarseShading}
    {initial : PropertyThreeSelectedInitialLocalData
      (sigma := sigma) (outputLoss := localLoss)
      (coefficient := coefficient) fineShading}
    {hdelta : 0 < delta}
    {rebalanced : Proposition63InitialRebalancedData
      original initial hdelta}
    {hrho : 0 < rho}
    (input : Proposition63MetricFiberInputData
      (stickyLoss := stickyLoss) rebalanced hrho)
    (sourceDensity : ENNReal) where
  commonSlice : Proposition63AxialCommonSliceData
    (Delta := proposition63LiteralSliceWidth Delta) input.selectedFiber
      (coarse.tube input.parent) hrho
      (sourceDensity * input.fiberFamily.family.enncard *
        Kakeya.realRpowENN delta 2)
  localGrains : Proposition63InitialWeakLocalGrainData
    (incidence := initial.incidence)
    commonSlice.shading sigma
    (Kakeya.realRpowENN delta (-localLoss))
    (Real.toNNReal coefficient)
  literalImage : WZ2PaperLiteralUnitRescaledShadingData
    input.frozenRescaled.familyData commonSlice.shading
  extremal : WZ2PaperCroppedIsExtremal sigma targetLoss
    input.frozenRescaled.rescalingCertificate.publicFamily
    (input.frozenRescaled.rescalingCertificate.publicShading
      literalImage.targetShading)

/-- The common-slice density extracted from the actual chosen metric fibre.
Its denominator is exactly the double-counting cost in the proof of
Proposition 6.3. -/
noncomputable def proposition63CanonicalSliceDensity
    {delta rho sigma stickyLoss localLoss coefficient Delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    {original : PureWZ2BalancedCoverData cover fineShading coarseShading}
    {initial : PropertyThreeSelectedInitialLocalData
      (sigma := sigma) (outputLoss := localLoss)
      (coefficient := coefficient) fineShading}
    {hdelta : 0 < delta}
    {rebalanced : Proposition63InitialRebalancedData
      original initial hdelta}
    {hrho : 0 < rho}
    (input : Proposition63MetricFiberInputData
      (stickyLoss := stickyLoss) rebalanced hrho) : ENNReal :=
  input.selectedFiber.mass ^ 2 /
    ((input.fiberFamily.family.card : ENNReal) *
      input.fiberFamily.family.enncard *
      Kakeya.realRpowENN delta 2 *
      ((Fintype.card (commonSliceIntervalType
          (proposition63LiteralSliceWidth Delta)) : ENNReal) *
        commonSliceSingleTubeBound delta Delta))

/-- The canonical slice density satisfies the exact energy inequality once
the selected metric fibre has positive mass. -/
theorem proposition63CanonicalSliceDensity_spec
    {delta rho sigma stickyLoss localLoss coefficient Delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    {original : PureWZ2BalancedCoverData cover fineShading coarseShading}
    {initial : PropertyThreeSelectedInitialLocalData
      (sigma := sigma) (outputLoss := localLoss)
      (coefficient := coefficient) fineShading}
    {hdelta : 0 < delta}
    {rebalanced : Proposition63InitialRebalancedData
      original initial hdelta}
    {hrho : 0 < rho}
    (input : Proposition63MetricFiberInputData
      (stickyLoss := stickyLoss) rebalanced hrho) :
    (input.fiberFamily.family.card : ENNReal) *
          (proposition63CanonicalSliceDensity (Delta := Delta) input *
            input.fiberFamily.family.enncard *
            Kakeya.realRpowENN delta 2) *
          ((Fintype.card (commonSliceIntervalType
              (proposition63LiteralSliceWidth Delta)) : ENNReal) *
            commonSliceSingleTubeBound delta Delta) ≤
        input.selectedFiber.mass ^ 2 := by
  let denominator : ENNReal :=
    (input.fiberFamily.family.card : ENNReal) *
      input.fiberFamily.family.enncard *
      Kakeya.realRpowENN delta 2 *
      ((Fintype.card (commonSliceIntervalType
          (proposition63LiteralSliceWidth Delta)) : ENNReal) *
        commonSliceSingleTubeBound delta Delta)
  change
    (input.fiberFamily.family.card : ENNReal) *
          ((input.selectedFiber.mass ^ 2 / denominator) *
            input.fiberFamily.family.enncard *
            Kakeya.realRpowENN delta 2) *
          ((Fintype.card (commonSliceIntervalType
              (proposition63LiteralSliceWidth Delta)) : ENNReal) *
            commonSliceSingleTubeBound delta Delta) ≤ _
  have heq :
      (input.fiberFamily.family.card : ENNReal) *
          ((input.selectedFiber.mass ^ 2 / denominator) *
            input.fiberFamily.family.enncard *
            Kakeya.realRpowENN delta 2) *
          ((Fintype.card (commonSliceIntervalType
              (proposition63LiteralSliceWidth Delta)) : ENNReal) *
            commonSliceSingleTubeBound delta Delta) =
        (input.selectedFiber.mass ^ 2 / denominator) * denominator := by
    dsimp only [denominator]
    ring
  rw [heq]
  simpa [mul_comm] using
    (ENNReal.mul_div_le (a := denominator)
      (b := input.selectedFiber.mass ^ 2))

namespace Proposition63CommonSliceRescaledData

/-- The distinguished tube `T₀` selected by common-slice double counting. -/
def anchorTube
    {delta rho Delta sigma stickyLoss localLoss targetLoss coefficient : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    {original : PureWZ2BalancedCoverData cover fineShading coarseShading}
    {initial : PropertyThreeSelectedInitialLocalData
      (sigma := sigma) (outputLoss := localLoss)
      (coefficient := coefficient) fineShading}
    {hdelta : 0 < delta}
    {rebalanced : Proposition63InitialRebalancedData
      original initial hdelta}
    {hrho : 0 < rho}
    {input : Proposition63MetricFiberInputData
      (stickyLoss := stickyLoss) rebalanced hrho}
    {sourceDensity : ENNReal}
    (data : Proposition63CommonSliceRescaledData
      (Delta := Delta) (targetLoss := targetLoss) input sourceDensity) :
    Kakeya.DeltaTube delta :=
  input.fiberFamily.family.tube data.commonSlice.distinguished

/-- The finite set `mathcal Z` of retained longitudinal intervals, before
converting interval indices into their base heights. -/
def retainedIntervals
    {delta rho Delta sigma stickyLoss localLoss targetLoss coefficient : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    {original : PureWZ2BalancedCoverData cover fineShading coarseShading}
    {initial : PropertyThreeSelectedInitialLocalData
      (sigma := sigma) (outputLoss := localLoss)
      (coefficient := coefficient) fineShading}
    {hdelta : 0 < delta}
    {rebalanced : Proposition63InitialRebalancedData
      original initial hdelta}
    {hrho : 0 < rho}
    {input : Proposition63MetricFiberInputData
      (stickyLoss := stickyLoss) rebalanced hrho}
    {sourceDensity : ENNReal}
    (data : Proposition63CommonSliceRescaledData
      (Delta := Delta) (targetLoss := targetLoss) input sourceDensity) :
    Finset (commonSliceIntervalType
      (proposition63LiteralSliceWidth Delta)) :=
  Finset.univ.filter fun interval =>
    proposition63AxialPartitionMeets
      (Delta := proposition63LiteralSliceWidth Delta) input.selectedFiber
      (coarse.tube input.parent) hrho
      data.commonSlice.distinguished interval

@[simp] theorem mem_retainedIntervals_iff
    {delta rho Delta sigma stickyLoss localLoss targetLoss coefficient : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    {original : PureWZ2BalancedCoverData cover fineShading coarseShading}
    {initial : PropertyThreeSelectedInitialLocalData
      (sigma := sigma) (outputLoss := localLoss)
      (coefficient := coefficient) fineShading}
    {hdelta : 0 < delta}
    {rebalanced : Proposition63InitialRebalancedData
      original initial hdelta}
    {hrho : 0 < rho}
    {input : Proposition63MetricFiberInputData
      (stickyLoss := stickyLoss) rebalanced hrho}
    {sourceDensity : ENNReal}
    (data : Proposition63CommonSliceRescaledData
      (Delta := Delta) (targetLoss := targetLoss) input sourceDensity)
    (interval : commonSliceIntervalType
      (proposition63LiteralSliceWidth Delta)) :
    interval ∈ data.retainedIntervals ↔
      proposition63AxialPartitionMeets
        (Delta := proposition63LiteralSliceWidth Delta) input.selectedFiber
        (coarse.tube input.parent) hrho
        data.commonSlice.distinguished interval := by
  simp [retainedIntervals]

/-- The common-slice shading is still a subshading of the frozen source
fibre used by Node 3. -/
theorem source_subshading
    {delta rho Delta sigma stickyLoss localLoss targetLoss coefficient : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    {original : PureWZ2BalancedCoverData cover fineShading coarseShading}
    {initial : PropertyThreeSelectedInitialLocalData
      (sigma := sigma) (outputLoss := localLoss)
      (coefficient := coefficient) fineShading}
    {hdelta : 0 < delta}
    {rebalanced : Proposition63InitialRebalancedData
      original initial hdelta}
    {hrho : 0 < rho}
    {input : Proposition63MetricFiberInputData
      (stickyLoss := stickyLoss) rebalanced hrho}
    {sourceDensity : ENNReal}
    (data : Proposition63CommonSliceRescaledData
      (Delta := Delta) (targetLoss := targetLoss) input sourceDensity) :
    PaperIsSubshading data.commonSlice.shading input.sourceFiber :=
  fun index => (data.commonSlice.subshading index).trans
    (input.source_subshading index)

end Proposition63CommonSliceRescaledData

/-- Perform the paper's common-slice restriction on the selected metric
fibre and then refresh its unit rescaling on the frozen Node 3 family. -/
theorem proposition63_common_slice_rescaled
    {delta rho Delta sigma stickyLoss localLoss targetLoss coefficient : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    {original : PureWZ2BalancedCoverData cover fineShading coarseShading}
    {initial : PropertyThreeSelectedInitialLocalData
      (sigma := sigma) (outputLoss := localLoss)
      (coefficient := coefficient) fineShading}
    {hdelta : 0 < delta}
    {rebalanced : Proposition63InitialRebalancedData
      original initial hdelta}
    {hrho : 0 < rho}
    (input : Proposition63MetricFiberInputData
      (stickyLoss := stickyLoss) rebalanced hrho)
    (hdeltaSmall : delta ≤ 1 / 24)
    (hDelta : 0 < Delta)
    (sourceDensity : ENNReal)
    (haggregate :
      (input.fiberFamily.family.card : ENNReal) *
          (sourceDensity * input.fiberFamily.family.enncard *
            Kakeya.realRpowENN delta 2) *
          ((Fintype.card (commonSliceIntervalType
              (proposition63LiteralSliceWidth Delta)) : ENNReal) *
            commonSliceSingleTubeBound delta Delta) ≤
        input.selectedFiber.mass ^ 2)
    (hloss : stickyLoss ≤ targetLoss)
    (htargetLoss : 0 < targetLoss)
    (hrhoOne : rho ≤ 1)
    (hscaleSmall : delta / rho ≤ 1 / 24)
    (hdensityAbsorb :
      Kakeya.realRpowENN (delta / rho) targetLoss *
          (55296 * Kakeya.deltaTubeVolume 1) ≤
        ENNReal.ofReal ((1 / 100 : ℝ) ^ 3) * sourceDensity) :
    Nonempty (Proposition63CommonSliceRescaledData
      (Delta := Delta) (targetLoss := targetLoss) input sourceDensity) := by
  have hfamilyNonempty : input.fiberFamily.family.Nonempty := by
    change 0 < (wz2PaperFullFiberIndices fine coarse input.parent).card
    exact Finset.card_pos.mpr <| by
      rcases cover.parent_hit input.parent with ⟨source, hsource⟩
      exact ⟨source, (mem_wz2PaperFullFiberIndices_iff
        input.parent source).2 hsource⟩
  have hline : WZ1PaperIsLineClass input.fiberFamily.family :=
    cover.fine_line_class.subfamily input.fiberFamily
  have hliteralWidth : 0 < proposition63LiteralSliceWidth Delta := by
    simp [proposition63LiteralSliceWidth]
    positivity
  have hanchorLine : WZ1PaperTubeInLineClass (coarse.tube input.parent) :=
    cover.coarse_line_class input.parent
  have hcovered : ∀ source : Fin input.fiberFamily.family.card,
      WZ1PaperTubeCovers (input.fiberFamily.family.tube source)
        (coarse.tube input.parent) := by
    intro source
    rw [input.fiberFamily.tube_eq source]
    apply (mem_wz2PaperFullFiberIndices_iff input.parent
      (input.fiberFamily.embedding source)).mp
    change (Finset.orderEmbOfFin
      (wz2PaperFullFiberIndices fine coarse input.parent) rfl source) ∈
        wz2PaperFullFiberIndices fine coarse input.parent
    exact Finset.orderEmbOfFin_mem
      (wz2PaperFullFiberIndices fine coarse input.parent) rfl source
  rcases proposition63_axial_common_slice input.selectedFiber
      (coarse.tube input.parent) hrho hanchorLine hfamilyNonempty hline
      hcovered hdelta hdeltaSmall hrhoOne hliteralWidth
      (sourceDensity * input.fiberFamily.family.enncard *
        Kakeya.realRpowENN delta 2) (by
          have hwidth :
              100 * proposition63LiteralSliceWidth Delta = Delta := by
            dsimp only [proposition63LiteralSliceWidth]
            ring
          rw [hwidth]
          exact haggregate) with
      ⟨commonSlice⟩
  have hunion : commonSlice.shading.union ⊆ input.selectedFiber.union :=
    paper_subshading_union_subset commonSlice.subshading
  let localGrains : Proposition63InitialWeakLocalGrainData
      (incidence := initial.incidence) commonSlice.shading sigma
      (Kakeya.realRpowENN delta (-localLoss))
      (Real.toNNReal coefficient) :=
    { planeMap := fun point => input.localGrains.planeMap
        ⟨point, hunion point.prop⟩
      planeMap_lipschitz := by
        intro first second
        exact input.localGrains.planeMap_lipschitz
          ⟨first, hunion first.prop⟩ ⟨second, hunion second.prop⟩
      planeMap_unit := fun point =>
        input.localGrains.planeMap_unit ⟨point, hunion point.prop⟩
      planeMap_incidence := by
        intro index point hpoint
        exact input.localGrains.planeMap_incidence index point
          (commonSlice.subshading index hpoint)
      local_ad := by
        intro queryScale hdeltaQuery hqueryOne point
        apply (input.localGrains.local_ad queryScale hdeltaQuery hqueryOne
          ⟨point, hunion point.prop⟩).mono_set
        rintro value ⟨other, hother, rfl⟩
        exact ⟨other, ⟨hunion hother.1, hother.2⟩, rfl⟩ }
  rcases proposition63_literal_unit_rescaled_shading input
      commonSlice.shading hrhoOne hscaleSmall with ⟨literalImage⟩
  have hsourceSub : PaperIsSubshading commonSlice.shading
      input.sourceFiber := fun index =>
    (commonSlice.subshading index).trans (input.source_subshading index)
  have hextremal := rescaledSubfiber_extremal_of_source_density
    input.frozenRescaled hsourceSub literalImage sourceDensity
    commonSlice.retained_mass hloss htargetLoss hscaleSmall hdensityAbsorb
  exact ⟨{
    commonSlice := commonSlice
    localGrains := localGrains
    literalImage := literalImage
    extremal := hextremal
  }⟩

end Kakeya.Assouad.PureWZ2

end
