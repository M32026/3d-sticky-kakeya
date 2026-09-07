import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63Lemma47
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63ExtremalOneScaleFullGrain
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.CanonicalCoarsePropertyPParameters
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.CoarsePropertyThreeLocalGrain
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.ExtremalCWATransfer
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.FiniteGridEveryScaleLocalAD
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.FiniteIntervalCoveringIteration
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.FiniteIntervalGridOneScaleLocalAD
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.FiniteScaleLipschitzBridge
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63NestedPointCover

/-!
# The Lemma 4.12 step in Proposition 6.3

After Lemma 4.7, the same coarse plane map is Lipschitz on a spatial
refinement.  The canonical Property-(P) selection and the Cordoba estimate
then produce every-scale local AD on a further refinement.  No plane map is
selected in this module: the final local-grain map is the restriction of the
Lemma 4.4 map `W`.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory Set ENNReal

/-- The paper Lemma 4.12 output, retaining the exact provenance of the plane
map and the half-mass Property-(P) refinement. -/
structure Proposition63Lemma412Data
    {delta sigma lemma43SourceLoss lemma43Loss stickyLoss lemma44Loss
      lemma47Loss coefficient : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source : WZ1PaperTubeShading family}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    {lemma43 : Proposition63Lemma43Data
      (sigma := sigma) (sourceLoss := lemma43SourceLoss)
      (targetLoss := lemma43Loss) source (rho.1 / 2)}
    {sticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := stickyLoss)
      lemma43.shading rho logExponent}
    {lemma44 : Proposition63Lemma44Data lemma43 sticky lemma44Loss}
    (lemma47 : Proposition63Lemma47Data lemma44 lemma47Loss coefficient)
    (outputLoss : ℝ) where
  epsilon₁ : ℝ
  epsilon₃ : ℝ
  tau : ℝ
  propertyP : PureWZ2PropertyPData
    (sigma := sigma) (L := rho.1) (tau := tau)
    (coarseShading := lemma47.shading) epsilon₁ epsilon₃
  shading : WZ1PaperTubeShading sticky.coarse
  property_subshading : PaperIsSubshading shading propertyP.propertyThree
  subshading : PaperIsSubshading shading lemma47.shading
  cubical : WZ1PaperIsCubicalShading shading
  localGrains : PureWZ2RelaxedLocalGrainData shading sigma
    (Kakeya.realRpowENN rho.1 (-outputLoss))
    (Real.toNNReal coefficient)
  same_plane_map : ∀ point,
    localGrains.planeMap point = lemma44.planeMap.planeMap point
  mass_retention : (2 : ENNReal)⁻¹ * lemma47.shading.mass ≤ shading.mass
  extremal : WZ2PaperCroppedIsExtremal
    sigma outputLoss sticky.coarse shading
  top_level_cwa : WZ2PaperConvexWolffBound sticky.coarse
    (Kakeya.realRpowENN rho.1 (-outputLoss))

/-- The stable output actually consumed after Lemma 4.12.  Unlike the older
single-critical-scale package, this interface does not retain an arbitrary
Property-(P) witness: the finite full-grain proof may use a fresh witness at
each grid coordinate, while all coordinates end on this one shading and the
same Lemma 4.4 plane map. -/
structure Proposition63Lemma412OutputData
    {delta sigma lemma43SourceLoss lemma43Loss stickyLoss lemma44Loss
      lemma47Loss coefficient : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source : WZ1PaperTubeShading family}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    {lemma43 : Proposition63Lemma43Data
      (sigma := sigma) (sourceLoss := lemma43SourceLoss)
      (targetLoss := lemma43Loss) source (rho.1 / 2)}
    {sticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := stickyLoss)
      lemma43.shading rho logExponent}
    {lemma44 : Proposition63Lemma44Data lemma43 sticky lemma44Loss}
    (lemma47 : Proposition63Lemma47Data lemma44 lemma47Loss coefficient)
    (outputLoss : ℝ) where
  shading : WZ1PaperTubeShading sticky.coarse
  subshading : PaperIsSubshading shading lemma47.shading
  cubical : WZ1PaperIsCubicalShading shading
  localGrains : PureWZ2RelaxedLocalGrainData shading sigma
    (Kakeya.realRpowENN rho.1 (-outputLoss))
    (Real.toNNReal coefficient)
  same_plane_map : ∀ point,
    localGrains.planeMap point = lemma44.planeMap.planeMap point
  extremal : WZ2PaperCroppedIsExtremal
    sigma outputLoss sticky.coarse shading
  top_level_cwa : WZ2PaperConvexWolffBound sticky.coarse
    (Kakeya.realRpowENN rho.1 (-outputLoss))

/-- Forget the historical single Property-(P) witness and retain exactly the
stable Lemma 4.12 output used by the later global-grain assembly. -/
def Proposition63Lemma412Data.toOutput
    {delta sigma lemma43SourceLoss lemma43Loss stickyLoss lemma44Loss
      lemma47Loss coefficient outputLoss : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source : WZ1PaperTubeShading family}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    {lemma43 : Proposition63Lemma43Data
      (sigma := sigma) (sourceLoss := lemma43SourceLoss)
      (targetLoss := lemma43Loss) source (rho.1 / 2)}
    {sticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := stickyLoss)
      lemma43.shading rho logExponent}
    {lemma44 : Proposition63Lemma44Data lemma43 sticky lemma44Loss}
    {lemma47 : Proposition63Lemma47Data lemma44 lemma47Loss coefficient}
    (data : Proposition63Lemma412Data lemma47 outputLoss) :
    Proposition63Lemma412OutputData lemma47 outputLoss where
  shading := data.shading
  subshading := data.subshading
  cubical := data.cubical
  localGrains := data.localGrains
  same_plane_map := data.same_plane_map
  extremal := data.extremal
  top_level_cwa := data.top_level_cwa

/-- The exact finite input used by the Lemma 4.12 interpolation.  Local AD is
required only on the central power-grid interval.  The endpoint estimates are
proved analytically by `finite_grid_isAD_to_relaxed_local_grain`, while the
finite Lipschitz selection still sees all `N` spatial coordinates. -/
structure Proposition63Lemma412FiniteGridData
    {delta sigma incidence gridLoss : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (current : WZ1PaperTubeShading family)
    (currentMap : PaperWZ1WeakPlaneMapData current incidence)
    (N kMin kMax : ℕ)
    (spatialScale variationScale : ℕ → ℝ) where
  shading : WZ1PaperTubeShading family
  subshading : PaperIsSubshading shading current
  cubical : WZ1PaperIsCubicalShading shading
  planeMap : PaperWZ1WeakPlaneMapData shading incidence
  same_plane_map : planeMap.planeMap = currentMap.planeMap
  variation : ∀ index, index < N → ∀ first ∈ shading.union,
    ∀ second ∈ shading.union, dist first second ≤ spatialScale index →
      dist (planeMap.planeMap first) (planeMap.planeMap second) ≤
        variationScale index
  local_ad : ∀ index, kMin ≤ index ∧ index ≤ kMax →
    ∀ point ∈ shading.union,
      IsADSet1
        (scalarProjection (planeMap.planeMap point)
          (shading.union ∩ Metric.closedBall point
            (Real.sqrt (finiteGridScaleVal delta N index))))
        (finiteGridScaleVal delta N index) (1 - sigma)
        (Kakeya.realRpowENN delta (-gridLoss))
  massLoss : ENNReal
  massLoss_pos : 0 < massLoss
  massLoss_ne_top : massLoss ≠ ⊤
  mass_retention : massLoss⁻¹ * current.mass ≤ shading.mass
  extremal : WZ2PaperCroppedIsExtremal sigma gridLoss family shading

/-- Convert the mathematically minimal central-grid package into the stable
Lemma 4.12 output.  No M7 call is required below `kMin` or above `kMax`; those
query endpoints are handled inside the finite-grid interpolation theorem. -/
theorem proposition63_lemma412_output_of_finite_grid_data
    {delta sigma lemma43SourceLoss lemma43Loss stickyLoss lemma44Loss
      lemma47Loss coefficient gridLoss midLoss outputLoss : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source : WZ1PaperTubeShading family}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent N kMin kMax : ℕ}
    {lemma43 : Proposition63Lemma43Data
      (sigma := sigma) (sourceLoss := lemma43SourceLoss)
      (targetLoss := lemma43Loss) source (rho.1 / 2)}
    {sticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := stickyLoss)
      lemma43.shading rho logExponent}
    {lemma44 : Proposition63Lemma44Data lemma43 sticky lemma44Loss}
    (lemma47 : Proposition63Lemma47Data lemma44 lemma47Loss coefficient)
    (spatialScale variationScale : ℕ → ℝ)
    (finite : Proposition63Lemma412FiniteGridData
      (sigma := sigma) (gridLoss := gridLoss) lemma47.shading
        lemma47.planeMap N kMin kMax
        spatialScale variationScale)
    (hgridLossPos : 0 < gridLoss)
    (houtputLossPos : 0 < outputLoss)
    (hlemma47Output : lemma47Loss ≤ outputLoss)
    (houtputLossLe : gridLoss ≤ outputLoss)
    (hresidue : 27 * Kakeya.realRpowENN rho.1 outputLoss ≤
      Kakeya.realRpowENN rho.1 gridLoss)
    (hcoefficientPos : 0 < coefficient)
    (hvariationCovers : ∀ d : ℝ, rho.1 < d → d ≤ 4 →
      coefficient * d < 2 →
      ∃ index, index < N ∧ d ≤ spatialScale index ∧
        variationScale index ≤ coefficient * d)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hmidLoss : 0 < midLoss) (hN : 0 < (N : ℝ))
    (hkMin : kMin = Nat.ceil ((N : ℝ) * midLoss))
    (hkMinMax : kMin ≤ kMax)
    (hkMaxLower : (N : ℝ) * (1 - midLoss) - 1 ≤ (kMax : ℝ))
    (hgridAdmissible : ∀ k, kMin ≤ k ∧ k ≤ kMax →
      rho.1 ≤ finiteGridScaleVal rho.1 N k ∧
        finiteGridScaleVal rho.1 N k ≤ 1)
    (habsorbInterpolation :
      (100 : ℝ) * Real.rpow rho.1
          (-gridLoss - midLoss - 1 / (N : ℝ)) ≤
        Real.rpow rho.1 (-outputLoss))
    (habsorbFine :
      (100 : ℝ) * Real.rpow rho.1
          (-midLoss - 1 / (N : ℝ)) ≤
        Real.rpow rho.1 (-outputLoss)) :
    Nonempty (Proposition63Lemma412OutputData lemma47 outputLoss) := by
  let finalMap := finite.planeMap
  have finalCellwise : ∀ first second,
      wz1PaperGridIndex rho.1 first = wz1PaperGridIndex rho.1 second →
        finalMap.planeMap first = finalMap.planeMap second := by
    intro first second sameCell
    rw [finite.same_plane_map, lemma47.same_plane_map]
    exact lemma44.planeMap_constant_on_cells first second sameCell
  rcases paper_finite_scale_variation_to_lipschitz
      lemma47.extremal.delta_pos hcoefficientPos finite.cubical finalMap
      finalCellwise N spatialScale variationScale finite.variation
      (by
        intro first firstMem second secondMem
        exact paper_shading_union_dist_le_four finite.shading firstMem
          secondMem) hvariationCovers with
    ⟨selected, selectedMap, selectedSubFinal, selectedMapEq, selectedCubical,
      _selectedMultiplicity, finalMassLe, selectedLipschitz⟩
  have selectedSubLemma47 : PaperIsSubshading selected lemma47.shading :=
    fun index point pointMem =>
      finite.subshading index (selectedSubFinal index pointMem)
  have selectedMass : (27 : ENNReal)⁻¹ * finite.shading.mass ≤
      selected.mass := by
    apply (ENNReal.inv_mul_le_iff (by norm_num) (by norm_num)).2
    simpa [mul_comm] using finalMassLe
  have selectedExtremal : WZ2PaperCroppedIsExtremal sigma outputLoss
      sticky.coarse selected := by
    apply transfer_cropped_extremal_to_subshading 27 (by norm_num)
      (by norm_num) finite.extremal selectedSubFinal selectedMass
      selectedCubical houtputLossLe hresidue lemma47.extremal.delta_pos
      lemma47.extremal.delta_le_one houtputLossPos
  have selectedCWA : WZ2PaperConvexWolffBound sticky.coarse
      (Kakeya.realRpowENN rho.1 (-outputLoss)) := by
    apply weaken_convex_wolff_bound lemma47.top_level_cwa
    exact realRpowENN_antitone lemma47.extremal.delta_pos
      lemma47.extremal.delta_le_one (by linarith [hlemma47Output])
  let selectedFn : {point : Point3 // point ∈ selected.union} → Point3 :=
    fun point => selectedMap.planeMap point
  have selectedUnit : ∀ point, ‖selectedFn point‖ = 1 := by
    intro point
    exact selectedMap.unit point point.prop
  have selectedIncidence : ∀ index point,
      ∀ hpoint : point ∈ selected.carrier index,
        |inner ℝ (sticky.coarse.tube index).direction
          (selectedFn ⟨point, ⟨index, hpoint⟩⟩)| ≤ rho.1 := by
    intro index point hpoint
    exact selectedMap.incidence index point hpoint
  have selectedFiniteAD : ∀ k, kMin ≤ k ∧ k ≤ kMax →
      ∀ point : {point : Point3 // point ∈ selected.union},
        IsADSet1
          (scalarProjection (selectedFn point)
            (selected.union ∩ Metric.closedBall (point : Point3)
              (Real.sqrt (finiteGridScaleVal rho.1 N k))))
          (finiteGridScaleVal rho.1 N k) (1 - sigma)
          (Kakeya.realRpowENN rho.1 (-gridLoss)) := by
    intro k hk point
    have pointFinal : (point : Point3) ∈ finite.shading.union := by
      rcases point.prop with ⟨index, pointMem⟩
      exact ⟨index, selectedSubFinal index pointMem⟩
    have sourceAD := finite.local_ad k hk point pointFinal
    have pointMapEq : selectedFn point =
        finite.planeMap.planeMap point := by
      dsimp only [selectedFn]
      exact congrFun selectedMapEq point
    rw [pointMapEq]
    apply sourceAD.mono
    rintro value ⟨other, ⟨otherMem, otherBall⟩, rfl⟩
    exact ⟨other, ⟨
      paperSubshading_union selectedSubFinal otherMem, otherBall⟩, rfl⟩
  let localGrains : PureWZ2RelaxedLocalGrainData selected sigma
      (Kakeya.realRpowENN rho.1 (-outputLoss))
      (Real.toNNReal coefficient) :=
    finite_grid_isAD_to_relaxed_local_grain selectedFn
      (by simpa only [selectedFn] using selectedLipschitz) selectedUnit
      selectedIncidence lemma47.extremal.delta_pos
      lemma47.extremal.delta_le_one hsigma hsigmaOne hgridLossPos hmidLoss
      hN hkMin hkMinMax hkMaxLower hgridAdmissible selectedFiniteAD
      habsorbInterpolation habsorbFine
  exact ⟨{
    shading := selected
    subshading := selectedSubLemma47
    cubical := selectedCubical
    localGrains := localGrains
    same_plane_map := by
      intro point
      change selectedMap.planeMap point = lemma44.planeMap.planeMap point
      rw [selectedMapEq, finite.same_plane_map, lemma47.same_plane_map]
    extremal := selectedExtremal
    top_level_cwa := selectedCWA
  }⟩

/-- Convert the restored finite full-grain output into the stable Lemma 4.12
output.  Only the final 27-residue refinement is charged here; every
one-scale mass loss has already been absorbed before the next coordinate. -/
theorem proposition63_lemma412_output_of_extremal_finite_full_grain
    {delta sigma lemma43SourceLoss lemma43Loss stickyLoss lemma44Loss
      lemma47Loss coefficient gridLoss midLoss outputLoss : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source : WZ1PaperTubeShading family}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent N kMin kMax : ℕ}
    {lemma43 : Proposition63Lemma43Data
      (sigma := sigma) (sourceLoss := lemma43SourceLoss)
      (targetLoss := lemma43Loss) source (rho.1 / 2)}
    {sticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := stickyLoss)
      lemma43.shading rho logExponent}
    {lemma44 : Proposition63Lemma44Data lemma43 sticky lemma44Loss}
    (lemma47 : Proposition63Lemma47Data lemma44 lemma47Loss coefficient)
    (loss : ℕ → ℝ)
    (queryScale spatialScale variationScale : ℕ → ℝ)
    (finite : Proposition63ExtremalFiniteFullGrainData
      (sigma := sigma) lemma47.shading lemma47.planeMap loss N queryScale
        spatialScale variationScale)
    (hgridLoss : loss N = gridLoss)
    (hgridLossPos : 0 < gridLoss)
    (houtputLossPos : 0 < outputLoss)
    (hlemma47Output : lemma47Loss ≤ outputLoss)
    (houtputLossLe : gridLoss ≤ outputLoss)
    (hresidue : 27 * Kakeya.realRpowENN rho.1 outputLoss ≤
      Kakeya.realRpowENN rho.1 gridLoss)
    (hcoefficientPos : 0 < coefficient)
    (hincidenceLeDelta : rho.1 ≤ rho.1)
    (hvariationCovers : ∀ d : ℝ, rho.1 < d → d ≤ 4 →
      coefficient * d < 2 →
      ∃ index, index < N ∧ d ≤ spatialScale index ∧
        variationScale index ≤ coefficient * d)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hmidLoss : 0 < midLoss) (hN : 0 < (N : ℝ))
    (hkMin : kMin = Nat.ceil ((N : ℝ) * midLoss))
    (hkMinMax : kMin ≤ kMax) (hkMaxLt : kMax < N)
    (hkMaxLower : (N : ℝ) * (1 - midLoss) - 1 ≤ (kMax : ℝ))
    (hqueryEq : ∀ index, index < N →
      queryScale index = finiteGridScaleVal rho.1 N index)
    (hgridAdmissible : ∀ k, kMin ≤ k ∧ k ≤ kMax →
      rho.1 ≤ finiteGridScaleVal rho.1 N k ∧
        finiteGridScaleVal rho.1 N k ≤ 1)
    (habsorbInterpolation :
      (100 : ℝ) * Real.rpow rho.1
          (-gridLoss - midLoss - 1 / (N : ℝ)) ≤
        Real.rpow rho.1 (-outputLoss))
    (habsorbFine :
      (100 : ℝ) * Real.rpow rho.1
          (-midLoss - 1 / (N : ℝ)) ≤
        Real.rpow rho.1 (-outputLoss)) :
    Nonempty (Proposition63Lemma412OutputData lemma47 outputLoss) := by
  let finalMap := finite.planeMap
  have finalCellwise : ∀ first second,
      wz1PaperGridIndex rho.1 first = wz1PaperGridIndex rho.1 second →
        finalMap.planeMap first = finalMap.planeMap second := by
    intro first second sameCell
    rw [finite.same_plane_map, lemma47.same_plane_map]
    exact lemma44.planeMap_constant_on_cells first second sameCell
  rcases paper_finite_scale_variation_to_lipschitz
      lemma47.extremal.delta_pos hcoefficientPos finite.cubical finalMap
      finalCellwise N spatialScale variationScale finite.variation
      (by
        intro first firstMem second secondMem
        exact paper_shading_union_dist_le_four finite.shading firstMem
          secondMem) hvariationCovers with
    ⟨selected, selectedMap, selectedSubFinal, selectedMapEq, selectedCubical,
      _selectedMultiplicity, finalMassLe, selectedLipschitz⟩
  have selectedSubLemma47 : PaperIsSubshading selected lemma47.shading :=
    fun index point pointMem =>
      finite.subshading index (selectedSubFinal index pointMem)
  have selectedMass : (27 : ENNReal)⁻¹ * finite.shading.mass ≤
      selected.mass := by
    apply (ENNReal.inv_mul_le_iff (by norm_num) (by norm_num)).2
    simpa [mul_comm] using finalMassLe
  have selectedExtremal : WZ2PaperCroppedIsExtremal sigma outputLoss
      sticky.coarse selected := by
    apply transfer_cropped_extremal_to_subshading 27 (by norm_num)
      (by norm_num) (by simpa only [hgridLoss] using finite.extremal)
      selectedSubFinal selectedMass selectedCubical houtputLossLe hresidue
      lemma47.extremal.delta_pos lemma47.extremal.delta_le_one
      houtputLossPos
  have selectedCWA : WZ2PaperConvexWolffBound sticky.coarse
      (Kakeya.realRpowENN rho.1 (-outputLoss)) := by
    apply weaken_convex_wolff_bound lemma47.top_level_cwa
    exact realRpowENN_antitone lemma47.extremal.delta_pos
      lemma47.extremal.delta_le_one (by linarith [hlemma47Output])
  let selectedFn : {point : Point3 // point ∈ selected.union} → Point3 :=
    fun point => selectedMap.planeMap point
  have selectedUnit : ∀ point, ‖selectedFn point‖ = 1 := by
    intro point
    exact selectedMap.unit point point.prop
  have selectedIncidence : ∀ index point,
      ∀ hpoint : point ∈ selected.carrier index,
        |inner ℝ (sticky.coarse.tube index).direction
          (selectedFn ⟨point, ⟨index, hpoint⟩⟩)| ≤ rho.1 := by
    intro index point hpoint
    exact (selectedMap.incidence index point hpoint).trans hincidenceLeDelta
  have selectedFiniteAD : ∀ k, kMin ≤ k ∧ k ≤ kMax →
      ∀ point : {point : Point3 // point ∈ selected.union},
        IsADSet1
          (scalarProjection (selectedFn point)
            (selected.union ∩ Metric.closedBall (point : Point3)
              (Real.sqrt (finiteGridScaleVal rho.1 N k))))
          (finiteGridScaleVal rho.1 N k) (1 - sigma)
          (Kakeya.realRpowENN rho.1 (-gridLoss)) := by
    intro k hk point
    have pointFinal : (point : Point3) ∈ finite.shading.union := by
      rcases point.prop with ⟨index, pointMem⟩
      exact ⟨index, selectedSubFinal index pointMem⟩
    have sourceAD := finite.local_ad k (hk.2.trans_lt hkMaxLt) point pointFinal
    rw [hqueryEq k (hk.2.trans_lt hkMaxLt)] at sourceAD
    rw [hgridLoss] at sourceAD
    have pointMapEq : selectedFn point =
        finite.planeMap.planeMap point := by
      dsimp only [selectedFn]
      exact congrFun selectedMapEq point
    rw [pointMapEq]
    apply sourceAD.mono
    rintro value ⟨other, ⟨otherMem, otherBall⟩, rfl⟩
    exact ⟨other, ⟨
      paperSubshading_union selectedSubFinal otherMem, otherBall⟩, rfl⟩
  let localGrains : PureWZ2RelaxedLocalGrainData selected sigma
      (Kakeya.realRpowENN rho.1 (-outputLoss))
      (Real.toNNReal coefficient) :=
    finite_grid_isAD_to_relaxed_local_grain selectedFn
      (by simpa only [selectedFn] using selectedLipschitz) selectedUnit
      selectedIncidence lemma47.extremal.delta_pos
      lemma47.extremal.delta_le_one hsigma hsigmaOne hgridLossPos hmidLoss
      hN hkMin hkMinMax hkMaxLower hgridAdmissible selectedFiniteAD
      habsorbInterpolation habsorbFine
  exact ⟨{
    shading := selected
    subshading := selectedSubLemma47
    cubical := selectedCubical
    localGrains := localGrains
    same_plane_map := by
      intro point
      change selectedMap.planeMap point = lemma44.planeMap.planeMap point
      rw [selectedMapEq, finite.same_plane_map, lemma47.same_plane_map]
    extremal := selectedExtremal
    top_level_cwa := selectedCWA
  }⟩

/-- Run a preselected restored full-grain schedule on the actual Lemma 4.7
state and immediately apply the terminal finite-grid interpolation.  This is
the direct scheduler-to-Lemma-4.12 bridge; no external one-scale producer or
Lemma 4.12 certificate callback remains. -/
theorem proposition63_lemma412_output_of_full_grain_schedule
    {delta sigma lemma43SourceLoss lemma43Loss stickyLoss lemma44Loss
      lemma47Loss coefficient gridLoss midLoss outputLoss : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source : WZ1PaperTubeShading family}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent N kMin kMax : ℕ}
    {lemma43 : Proposition63Lemma43Data
      (sigma := sigma) (sourceLoss := lemma43SourceLoss)
      (targetLoss := lemma43Loss) source (rho.1 / 2)}
    {sticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := stickyLoss)
      lemma43.shading rho logExponent}
    {lemma44 : Proposition63Lemma44Data lemma43 sticky lemma44Loss}
    (lemma47 : Proposition63Lemma47Data lemma44 lemma47Loss coefficient)
    {ambientSourceLoss ambientNormalizationLoss : ℝ}
    (ambientReentry : PureWZ2PropStickyReentryData
      (sigma := sigma) sticky.croppedCoarseShading 0 ambientSourceLoss
        ambientNormalizationLoss)
    (schedule : Proposition63ExtremalFiniteFullGrainScheduleData
      sigma gridLoss N)
    (hrhoSchedule : rho.1 ≤ schedule.delta₀)
    (hambientSource : ambientSourceLoss ≤ schedule.rootSourceLoss)
    (hambientNormalization :
      ambientNormalizationLoss ≤ schedule.rootNormalizationLoss)
    (hlemma47Input : lemma47Loss ≤ schedule.inputLoss)
    (hcoefficientOne : 1 ≤ (Real.toNNReal coefficient : ℝ))
    (queryScale spatialScale variationScale : ℕ → ℝ)
    (queryPos : ∀ index, index < N → 0 < queryScale index)
    (querySmall : ∀ index, index < N → queryScale index ≤ 1 / 4)
    (queryGridFloor : ∀ index, index < N →
      48 * rho.1 ^ 2 ≤ queryScale index)
    (alignedLower : ∀ index, index < N →
      Real.rpow rho.1 (1 - schedule.producerWindowLoss index) ≤
        alignedCoarseScale rho.1 (queryScale index))
    (phase1Lower : ∀ index, index < N →
      Real.rpow rho.1 (schedule.phase1StickyLoss index) ≤
        alignedCoarseScale rho.1 (queryScale index))
    (alignedUpper : ∀ index, index < N →
      alignedCoarseScale rho.1 (queryScale index) ≤
        Real.rpow rho.1 (schedule.producerWindowLoss index))
    (periodicScale : ∀ index, index < N →
      50 * rho.1 ≤ Real.sqrt (queryScale index))
    (sqrtOne : ∀ index, index < N →
      Real.sqrt (queryScale index) ≤ 1)
    (variationBudget : ∀ index, index < N →
      (Real.toNNReal coefficient : ℝ) * spatialScale index ≤
        variationScale index)
    (hgridLossPos : 0 < gridLoss)
    (houtputLossPos : 0 < outputLoss)
    (hlemma47Output : lemma47Loss ≤ outputLoss)
    (hgridOutput : gridLoss ≤ outputLoss)
    (hresidue : 27 * Kakeya.realRpowENN rho.1 outputLoss ≤
      Kakeya.realRpowENN rho.1 gridLoss)
    (hcoefficientPos : 0 < coefficient)
    (hvariationCovers : ∀ d : ℝ, rho.1 < d → d ≤ 4 →
      coefficient * d < 2 →
      ∃ index, index < N ∧ d ≤ spatialScale index ∧
        variationScale index ≤ coefficient * d)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hmidLoss : 0 < midLoss) (hN : 0 < (N : ℝ))
    (hkMin : kMin = Nat.ceil ((N : ℝ) * midLoss))
    (hkMinMax : kMin ≤ kMax) (hkMaxLt : kMax < N)
    (hkMaxLower : (N : ℝ) * (1 - midLoss) - 1 ≤ (kMax : ℝ))
    (hqueryEq : ∀ index, index < N →
      queryScale index = finiteGridScaleVal rho.1 N index)
    (hgridAdmissible : ∀ k, kMin ≤ k ∧ k ≤ kMax →
      rho.1 ≤ finiteGridScaleVal rho.1 N k ∧
        finiteGridScaleVal rho.1 N k ≤ 1)
    (habsorbInterpolation :
      (100 : ℝ) * Real.rpow rho.1
          (-gridLoss - midLoss - 1 / (N : ℝ)) ≤
        Real.rpow rho.1 (-outputLoss))
    (habsorbFine :
      (100 : ℝ) * Real.rpow rho.1
          (-midLoss - 1 / (N : ℝ)) ≤
        Real.rpow rho.1 (-outputLoss)) :
    Nonempty (Proposition63Lemma412OutputData lemma47 outputLoss) := by
  have currentExtremal : WZ2PaperCroppedIsExtremal sigma schedule.inputLoss
      sticky.coarse lemma47.shading :=
    lemma47.extremal.mono_loss hlemma47Input
  have currentSubAmbient : PaperIsSubshading lemma47.shading
      sticky.croppedCoarseShading := fun index point pointMem =>
    lemma44.coarse_subshading index (lemma47.subshading index pointMem)
  rcases schedule.run lemma47.extremal.delta_pos hrhoSchedule
      ambientReentry hambientSource hambientNormalization lemma47.shading
      currentExtremal currentSubAmbient lemma47.planeMap
      (Real.toNNReal coefficient) lemma47.lipschitz queryScale spatialScale
      variationScale queryPos querySmall queryGridFloor alignedLower
      phase1Lower alignedUpper periodicScale sqrtOne hcoefficientOne
      variationBudget with ⟨finite⟩
  exact proposition63_lemma412_output_of_extremal_finite_full_grain lemma47
    schedule.loss queryScale spatialScale variationScale finite
    schedule.finalLoss_eq hgridLossPos houtputLossPos hlemma47Output
    hgridOutput hresidue hcoefficientPos le_rfl hvariationCovers hsigma
    hsigmaOne hmidLoss hN hkMin hkMinMax hkMaxLt hkMaxLower hqueryEq
    hgridAdmissible habsorbInterpolation habsorbFine

/-- Apply the analogue of Lemma 4.12 to a Lemma 4.7 output.  The canonical
Property-(P) package contains the high-multiplicity and transverse-pair
selection.  The remaining hypotheses are precisely the Cordoba and endpoint
inequalities paid by the outer parameter hierarchy. -/
theorem proposition63_paper_lemma412_same_plane_map
    {delta sigma lemma43SourceLoss lemma43Loss stickyLoss lemma44Loss
      lemma47Loss outputLoss coefficient : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source : WZ1PaperTubeShading family}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    {lemma43 : Proposition63Lemma43Data
      (sigma := sigma) (sourceLoss := lemma43SourceLoss)
      (targetLoss := lemma43Loss) source (rho.1 / 2)}
    {sticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := stickyLoss)
      lemma43.shading rho logExponent}
    {lemma44 : Proposition63Lemma44Data lemma43 sticky lemma44Loss}
    (lemma47 : Proposition63Lemma47Data lemma44 lemma47Loss coefficient)
    (parameters : CanonicalCoarsePropertyPParameters
      (sigma := sigma) (loss := lemma47Loss) lemma47.shading)
    (hsigma : 0 < sigma)
    (hsigmaOne : sigma < 1)
    (hsourceOutput : lemma47Loss ≤ outputLoss)
    (houtputLoss : 0 < outputLoss)
    (hslack : (2 : ENNReal) *
        Kakeya.realRpowENN rho.1 outputLoss ≤
      Kakeya.realRpowENN rho.1 lemma47Loss)
    (hrhoSmall : rho.1 ≤ 1 / 1000)
    (W0 Vmin Vtotal : ℝ)
    (hW0 : W0 = 40 * rho.1) (hW0Pos : 0 < W0)
    (hVmin : Vmin =
      Real.rpow rho.1
          (1 + 7 * parameters.epsilon₁ + parameters.epsilon₃) *
        parameters.tau ^ 2 / 200)
    (hVminPos : 0 < Vmin)
    (hVtotalPos : 0 < Vtotal)
    (hVtotal : volume lemma47.shading.union ≤ ENNReal.ofReal Vtotal)
    (sourceConstant : ENNReal)
    (hsourceOne : 1 ≤ sourceConstant)
    (hsourceTop : sourceConstant ≠ ⊤)
    (hcriticalArithmetic :
      let criticalScale := 48 * rho.1 ^ 2
      ENNReal.ofReal
        ((Vtotal / Vmin) *
          (2 * (2 * W0) / criticalScale + 2)) ≤ sourceConstant)
    (hsmallCost :
      let criticalScale := 48 * rho.1 ^ 2
      10 * ((10 * sourceConstant) *
          ENNReal.ofReal (10 * criticalScale / rho.1)) ≤
        Kakeya.realRpowENN rho.1 (-outputLoss))
    (hlargeEndpoint :
      let criticalScale := 48 * rho.1 ^ 2
      3 * (2 / Real.sqrt criticalScale) ^ sigma ≤
        rho.1 ^ (-outputLoss)) :
    Nonempty (Proposition63Lemma412Data lemma47 outputLoss) := by
  have hpropertySub : PaperIsSubshading parameters.propP.propertyThree
      lemma47.shading := fun index =>
    (parameters.propP.propertyThree_sub index).trans
      (parameters.propP.propertyOne_sub index)
  let propertyPlaneMap :=
    paperWeakPlaneMapRestrict lemma47.planeMap hpropertySub
  have hpropertyUnion : parameters.propP.propertyThree.union ⊆
      lemma47.shading.union := by
    rintro point ⟨index, hpoint⟩
    exact ⟨index, hpropertySub index hpoint⟩
  have hpropertyLipschitz : LipschitzWith (Real.toNNReal coefficient)
      (fun point : {point : Point3 //
          point ∈ parameters.propP.propertyThree.union} =>
        propertyPlaneMap.planeMap point) := by
    intro first second
    exact lemma47.lipschitz
      ⟨first, hpropertyUnion first.prop⟩
      ⟨second, hpropertyUnion second.prop⟩
  rcases coarse_property_three_subshading_relaxed_local_grain
      parameters.propP propertyPlaneMap hpropertyLipschitz
      (fun _ => Set.Subset.rfl) lemma47.extremal.delta_pos
      lemma47.extremal.delta_le_one hsigma hsigmaOne
      houtputLoss parameters.tau_def parameters.tau_pos
      parameters.tau_le_twenty parameters.scale_le_tau parameters.tau_sq
      parameters.tau_le_one hrhoSmall parameters.epsilon₁_pos
      parameters.epsilon₃_pos parameters.epsilon_sum parameters.logScale
      parameters.scale_le_logScale parameters.log_absorption
      parameters.propertyThree_full parameters.ax_condition
      W0 Vmin Vtotal hW0 hW0Pos hVmin hVminPos hVtotalPos hVtotal
      sourceConstant hsourceOne hsourceTop hcriticalArithmetic
      hsmallCost hlargeEndpoint with
    ⟨localGrains, hlocalMap⟩
  have hhalfMass : (2 : ENNReal)⁻¹ * lemma47.shading.mass ≤
      parameters.propP.propertyThree.mass := by
    rw [show (2 : ENNReal)⁻¹ = 1 / 2 by norm_num]
    exact parameters.propP.propertyThree_mass
  have hpropertyExtremal : WZ2PaperCroppedIsExtremal
      sigma outputLoss sticky.coarse parameters.propP.propertyThree := by
    exact transfer_cropped_extremal_to_subshading 2 (by norm_num)
      (by norm_num) lemma47.extremal hpropertySub hhalfMass
      parameters.propP.propertyThree_cubical hsourceOutput hslack
      lemma47.extremal.delta_pos lemma47.extremal.delta_le_one houtputLoss
  have hpropertyCWA : WZ2PaperConvexWolffBound sticky.coarse
      (Kakeya.realRpowENN rho.1 (-outputLoss)) :=
    transfer_cwa_to_subshading
      (_shading1 := lemma47.shading)
      (_shading2 := parameters.propP.propertyThree)
      lemma47.top_level_cwa hsourceOutput lemma47.extremal.delta_pos
      lemma47.extremal.delta_le_one
  refine ⟨{
    epsilon₁ := parameters.epsilon₁
    epsilon₃ := parameters.epsilon₃
    tau := parameters.tau
    propertyP := parameters.propP
    shading := parameters.propP.propertyThree
    property_subshading := fun _ => Set.Subset.rfl
    subshading := hpropertySub
    cubical := parameters.propP.propertyThree_cubical
    localGrains := localGrains
    same_plane_map := ?_
    mass_retention := hhalfMass
    extremal := hpropertyExtremal
    top_level_cwa := hpropertyCWA
  }⟩
  intro point
  rw [hlocalMap]
  change lemma47.planeMap.planeMap point = lemma44.planeMap.planeMap point
  exact congrFun lemma47.same_plane_map point

end Kakeya.Assouad.PureWZ2

end
