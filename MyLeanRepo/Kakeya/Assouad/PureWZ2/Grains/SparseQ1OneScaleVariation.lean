import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.SparseQ1PlaneMap
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.AmplifiedOneScaleCardinalityCancellation
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.PaperBroadMassBudget

/-!
# One-scale variation on the sparse-close Q=1 branch

This module connects the sparse cellwise plane map to the amplified
coarse-parent-pair refinement.  Narrow pruning and every later refinement are
common spatial restrictions, so point multiplicity agrees with the original
sparse shading at every surviving point.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory Set Finset

attribute [local instance] Classical.propDecidable

/-- A fiber-cardinality upper bound transfers to any paper subshading. -/
lemma paper_fiber_card_bound_mono_subshading
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {source selected : WZ1PaperTubeShading fine}
    (hsub : PaperIsSubshading selected source)
    (fiberPower : ENNReal)
    (hfiber : ∀ parent point,
      (((Finset.univ.filter fun index : Fin fine.card =>
        PureWZ2.selectParent cover index = parent ∧
          point ∈ source.carrier index).card : ℕ) : ENNReal) ≤
        fiberPower *
          ((wz2PaperFullFiberIndices fine coarse parent).card : ENNReal)) :
    ∀ parent point,
      (((Finset.univ.filter fun index : Fin fine.card =>
        PureWZ2.selectParent cover index = parent ∧
          point ∈ selected.carrier index).card : ℕ) : ENNReal) ≤
        fiberPower *
          ((wz2PaperFullFiberIndices fine coarse parent).card : ENNReal) := by
  intro parent point
  have hcard :
      (Finset.univ.filter fun index : Fin fine.card =>
        PureWZ2.selectParent cover index = parent ∧
          point ∈ selected.carrier index).card ≤
      (Finset.univ.filter fun index : Fin fine.card =>
        PureWZ2.selectParent cover index = parent ∧
          point ∈ source.carrier index).card := by
    apply Finset.card_le_card
    intro index hindex
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hindex ⊢
    exact ⟨hindex.1, hsub index hindex.2⟩
  have hcardENN :
      (((Finset.univ.filter fun index : Fin fine.card =>
        PureWZ2.selectParent cover index = parent ∧
          point ∈ selected.carrier index).card : ℕ) : ENNReal) ≤
      (((Finset.univ.filter fun index : Fin fine.card =>
        PureWZ2.selectParent cover index = parent ∧
          point ∈ source.carrier index).card : ℕ) : ENNReal) := by
    exact_mod_cast hcard
  exact hcardENN.trans (hfiber parent point)

/-- One sparse-close scale produces a cellwise weak plane map and then a
nearby-point variation refinement at scale `rho`.  The source mass loss is
the explicit factor `1/2` from `Q = 1` narrow pruning; all later losses are
the amplified parent-pair and orientation factors. -/
theorem paper_sparse_q1_one_scale_nearby_variation
    {delta rho kappa tau : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading source : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    (balanced : PureWZ2BalancedCoverData cover fineShading coarseShading)
    (hfineNonempty : fine.Nonempty)
    (hcoarseNonempty : coarse.Nonempty)
    (hsourceSubFine : PaperIsSubshading source fineShading)
    (hsourceCubical : WZ1PaperIsCubicalShading source)
    (fineMultiplicity : ℕ)
    (hFineMultiplicity : ∀ point ∈ source.union,
      fineMultiplicity ≤ source.pointMultiplicity point)
    (hclose : ∀ point ∈ source.union, ∀ index,
      point ∈ source.carrier index →
      2 * paperCloseDirectionCount source point index kappa ≤
        fineMultiplicity)
    (hbroadSmall :
      2 * (∫⁻ point in paperCountedBroadSet source tau 1,
        (source.pointMultiplicity point : ENNReal)) ≤ source.mass)
    (fiberPower densityPower : ENNReal)
    (hfiber : ∀ parent point,
      (((Finset.univ.filter fun index : Fin fine.card =>
        PureWZ2.selectParent cover index = parent ∧
          point ∈ source.carrier index).card : ℕ) : ENNReal) ≤
        fiberPower *
          ((wz2PaperFullFiberIndices fine coarse parent).card : ENNReal))
    (hdensity : densityPower * fine.enncard ≤
      (fineMultiplicity : ENNReal))
    (hdelta : 0 < delta) (htau : 0 ≤ tau)
    (hkappa : 0 < kappa)
    (hrho : 0 < rho) (hrhoKappa : rho < kappa)
    (K : ℕ) (hK : 0 < K) (hrhoAligned : rho = (K : ℝ) * delta) :
    ∃ (narrow : PaperWZ1NarrowRefinementData source tau 1)
      (selection :
        PaperWZ1NarrowDirectionSelection narrow.shading kappa)
      (planeMap :
        PaperWZ1WeakPlaneMapData narrow.shading (tau / kappa))
      (selected : WZ1PaperTubeShading fine),
      WZ1PaperIsCubicalShading narrow.shading ∧
      (∀ first second,
        wz1PaperGridIndex delta first =
          wz1PaperGridIndex delta second →
        selection.first first = selection.first second ∧
        selection.second first = selection.second second) ∧
      (∀ first second,
        wz1PaperGridIndex delta first =
          wz1PaperGridIndex delta second →
        planeMap.planeMap first = planeMap.planeMap second) ∧
      (∀ point, planeMap.planeMap point = selection.normal point) ∧
      PaperIsSubshading selected narrow.shading ∧
      WZ1PaperIsCubicalShading selected ∧
      (∀ point ∈ selected.union, ∀ other ∈ selected.union,
        dist point other ≤ rho →
          dist (planeMap.planeMap point)
            (planeMap.planeMap other) ≤ rho) ∧
      (∀ point ∈ selected.union,
        selected.pointMultiplicity point =
          source.pointMultiplicity point) ∧
      (1 / 2 : ENNReal) * source.mass ≤ narrow.shading.mass ∧
      (1 / 2 : ENNReal) * densityPower ^ 2 * source.mass ≤
        27 * ((2 * fiberPower ^ 2) *
          (wz1OrientationCapCount
            (10 * (tau / kappa + rho / 2) / (kappa - rho)) rho :
              ENNReal)) * selected.mass := by
  have hbroadMeasurable :
      MeasurableSet (paperCountedBroadSet source tau 1) :=
    paperCountedBroadSet_measurable source tau 1
  rcases paper_narrow_pruning hbroadMeasurable hbroadSmall with
    ⟨narrow⟩
  rcases paper_sparse_q1_cellwise_plane_map
      hdelta hkappa hfineNonempty hsourceCubical
      fineMultiplicity hFineMultiplicity hclose narrow with
    ⟨selection, planeMap, hnarrowCubical, hselectionCell,
      hplaneCell, hplaneSelection, hnarrowMass⟩
  have hnarrowSubFine : PaperIsSubshading narrow.shading fineShading :=
    fun index => (narrow.subshading index).trans (hsourceSubFine index)
  have hnarrowMultiplicity : ∀ point ∈ narrow.shading.union,
      fineMultiplicity ≤ narrow.shading.pointMultiplicity point := by
    intro point hpoint
    rw [paper_narrow_pointMultiplicity_eq narrow hpoint]
    have hpointSource : point ∈ source.union := by
      rcases hpoint with ⟨index, hindex⟩
      exact ⟨index, narrow.subshading index hindex⟩
    exact hFineMultiplicity point hpointSource
  have hnarrowClose : ∀ point ∈ narrow.shading.union, ∀ index,
      point ∈ narrow.shading.carrier index →
      2 * paperCloseDirectionCount narrow.shading point index kappa ≤
        fineMultiplicity := by
    intro point hpoint index hindex
    rw [paper_narrow_closeDirectionCount_eq narrow hpoint index]
    have hpointSource : point ∈ source.union :=
      ⟨index, narrow.subshading index hindex⟩
    exact hclose point hpointSource index (narrow.subshading index hindex)
  have hnarrowFiber := paper_fiber_card_bound_mono_subshading
    narrow.subshading fiberPower hfiber
  have hincidenceNonnegative : 0 ≤ tau / kappa :=
    div_nonneg htau hkappa.le
  rcases paper_amplified_one_scale_nearby_variation_cancel_cardinality
      balanced hfineNonempty hcoarseNonempty hnarrowSubFine hnarrowCubical
      planeMap hplaneCell
      fineMultiplicity hnarrowMultiplicity hnarrowClose
      fiberPower densityPower hnarrowFiber hdensity
      hincidenceNonnegative hrho hrhoKappa K hK hrhoAligned with
    ⟨selected, hselectedSub, hselectedCubical, hvariation,
      hselectedMultiplicityNarrow,
      hselectedMass⟩
  have hselectedMultiplicity : ∀ point ∈ selected.union,
      selected.pointMultiplicity point = source.pointMultiplicity point := by
    intro point hpoint
    have hpointNarrow : point ∈ narrow.shading.union := by
      rcases hpoint with ⟨index, hindex⟩
      exact ⟨index, hselectedSub index hindex⟩
    exact (hselectedMultiplicityNarrow point hpoint).trans
      (paper_narrow_pointMultiplicity_eq narrow hpointNarrow)
  have hsourceMass :
      (1 / 2 : ENNReal) * densityPower ^ 2 * source.mass ≤
        densityPower ^ 2 * narrow.shading.mass := by
    calc
      (1 / 2 : ENNReal) * densityPower ^ 2 * source.mass =
          densityPower ^ 2 * ((1 / 2 : ENNReal) * source.mass) := by
        ring
      _ ≤ densityPower ^ 2 * narrow.shading.mass := by
        gcongr
  exact ⟨narrow, selection, planeMap, selected, hnarrowCubical,
    hselectionCell, hplaneCell, hplaneSelection, hselectedSub,
    hselectedCubical, hvariation,
    hselectedMultiplicity, hnarrowMass, hsourceMass.trans hselectedMass⟩

end Kakeya.Assouad.PureWZ2

end
