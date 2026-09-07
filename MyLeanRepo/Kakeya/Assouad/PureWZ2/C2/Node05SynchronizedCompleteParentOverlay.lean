import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Node05SynchronizedCompleteParentPullback

/-!
# Spatial overlay on a complete-parent pullback

The synchronized post-grain coarse shading is generally a strict subshading
of the first sticky coarse shading.  After retaining all complete fine fibers
over its coarse family, the fine shading must therefore also be restricted to
the literal union of that synchronized coarse shading.  This module performs
that second, spatial restriction.

Under the owner route's point-multiplicity-one coarse certificate, every fine
tube meeting the overlay has the unique retained parent visible at that point.
Consequently the overlay preserves the original balanced `cellMass`, the
ambient fine point multiplicity, and the exact complete-parent provenance.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

/-- Restrict the complete-parent fine shading to the literal selected coarse
overlay. -/
noncomputable def pureWZ2Node05CompleteParentOverlayFineShading
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    {selectedCoarse : Kakeya.Streamlined.TubeSubfamily coarse}
    (data : PureWZ2Node05CompleteParentPullbackData
      cover fineShading coarseShading selectedCoarse)
    (overlay : WZ1PaperTubeShading selectedCoarse.family) :
    WZ1PaperTubeShading data.selectedFine.family where
  carrier source := data.selectedFineShading.carrier source ∩ overlay.union
  measurable_carrier source :=
    (data.selectedFineShading.measurable_carrier source).inter
      (measurableSet_shading_union overlay)
  subset_body source :=
    Set.inter_subset_left.trans (data.selectedFineShading.subset_body source)

namespace PureWZ2Node05CompleteParentPullbackData

variable
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    {selectedCoarse : Kakeya.Streamlined.TubeSubfamily coarse}
    (data : PureWZ2Node05CompleteParentPullbackData
      cover fineShading coarseShading selectedCoarse)
    (overlay : WZ1PaperTubeShading selectedCoarse.family)

/-- The spatial overlay remains a literal subshading of the complete-parent
fine shading. -/
theorem overlayFine_subshading :
    PureWZ2PaperIsSubshading
      (pureWZ2Node05CompleteParentOverlayFineShading data overlay)
      data.selectedFineShading :=
  fun _ => Set.inter_subset_left

/-- Every overlay point lies in the carrier of its exact restricted parent. -/
theorem overlayFine_point_compatibility
    (balanced : PureWZ2BalancedCoverData cover fineShading coarseShading)
    (coarseMultiplicityOne : ∀ point,
      (coarseShading.pointMultiplicity point : ENNReal) ≤ 1)
    (overlaySubshading :
      PureWZ2PaperIsSubshading overlay data.selectedCoarseShading) :
    ∀ source point,
      point ∈ (pureWZ2Node05CompleteParentOverlayFineShading
        data overlay).carrier source →
      point ∈ overlay.carrier
        (data.restrictedCover.toWZ1PaperTubeCover.parent source) := by
  intro source point hpoint
  rcases hpoint.2 with ⟨overlayParent, hoverlay⟩
  have hselectedParent : point ∈ data.selectedCoarseShading.carrier
      (data.restrictedCover.toWZ1PaperTubeCover.parent source) :=
    data.point_compatibility source point hpoint.1
  have hambientSource : point ∈ fineShading.carrier
      (data.selectedFine.embedding source) := by
    have hselected : point ∈ data.selectedFineShading.carrier source :=
      hpoint.1
    rw [data.selectedFineShading_eq] at hselected
    exact hselected
  have hsourceParent := data.ambient_parent_eq_of_mem balanced
    coarseMultiplicityOne
    (data.restrictedCover.toWZ1PaperTubeCover.parent source)
    (data.selectedFine.embedding source) point hselectedParent hambientSource
  have hoverlaySelected : point ∈ data.selectedCoarseShading.carrier
      overlayParent := overlaySubshading overlayParent hoverlay
  have hoverlayParent := data.ambient_parent_eq_of_mem balanced
    coarseMultiplicityOne overlayParent
    (data.selectedFine.embedding source) point hoverlaySelected hambientSource
  have hparent : overlayParent =
      data.restrictedCover.toWZ1PaperTubeCover.parent source := by
    apply selectedCoarse.embedding.injective
    exact hoverlayParent.symm.trans hsourceParent
  rwa [← hparent]

/-- The ambient fine-cell nesting and the cubical overlay choose the same
coarse cell through every retained point. -/
theorem overlayFine_cell_nested
    {ambientBase : PureWZ2BalancedCoverData cover fineShading coarseShading}
    (balanced : PureWZ2Node5BalancedCoverData ambientBase)
    (overlayCubical : WZ1PaperIsCubicalShading overlay)
    (hrho : 0 < rho) :
    ∀ source point,
      point ∈ (pureWZ2Node05CompleteParentOverlayFineShading
        data overlay).carrier source →
      ∃ cell ∈ wz1PaperActiveCells overlay hrho,
        wz1PaperGridCube delta (wz1PaperGridIndex delta point) ⊆
          wz1PaperGridCube rho cell := by
  intro source point hpoint
  have hambientPoint : point ∈ fineShading.carrier
      (data.selectedFine.embedding source) := by
    have hselected : point ∈ data.selectedFineShading.carrier source :=
      hpoint.1
    rw [data.selectedFineShading_eq] at hselected
    exact hselected
  rcases balanced.fine_cell_nested
      (data.selectedFine.embedding source) point hambientPoint with
    ⟨ambientCell, _hambientCell, hnested⟩
  rcases hpoint.2 with ⟨overlayParent, hoverlay⟩
  have hoverlayCell : wz1PaperGridCube rho
      (wz1PaperGridIndex rho point) ⊆ overlay.carrier overlayParent :=
    overlayCubical overlayParent point hoverlay
  have hpointFineCell : point ∈
      wz1PaperGridCube delta (wz1PaperGridIndex delta point) :=
    (mem_wz1PaperGridCube delta
      (wz1PaperGridIndex delta point) point).mpr rfl
  have hpointAmbientCell : point ∈ wz1PaperGridCube rho ambientCell :=
    hnested hpointFineCell
  have hcellEq : ambientCell = wz1PaperGridIndex rho point :=
    ((mem_wz1PaperGridCube rho ambientCell point).mp
      hpointAmbientCell).symm
  have hbody := overlay.subset_body overlayParent hoverlay
  have hwindow : wz1PaperGridIndex rho point ∈
      wz1PaperGridIndicesInWindow rho hrho :=
    paper_point_gridIndex_in_window hrho hbody.2
  have hactive : wz1PaperGridIndex rho point ∈
      wz1PaperActiveCells overlay hrho := by
    apply (mem_wz1PaperActiveCells overlay hrho _).mpr
    exact ⟨hwindow, ⟨point, ⟨overlayParent, hoverlay⟩,
      (mem_wz1PaperGridCube rho
        (wz1PaperGridIndex rho point) point).mpr rfl⟩⟩
  refine ⟨wz1PaperGridIndex rho point, hactive, ?_⟩
  rw [← hcellEq]
  exact hnested

/-- The overlay fine shading is cubical at the original fine scale. -/
theorem overlayFine_cubical
    {ambientBase : PureWZ2BalancedCoverData cover fineShading coarseShading}
    (balanced : PureWZ2Node5BalancedCoverData ambientBase)
    (ambientFineCubical : WZ1PaperIsCubicalShading fineShading)
    (overlayCubical : WZ1PaperIsCubicalShading overlay)
    (hrho : 0 < rho) :
    WZ1PaperIsCubicalShading
      (pureWZ2Node05CompleteParentOverlayFineShading data overlay) := by
  intro source point hpoint
  rcases data.overlayFine_cell_nested overlay balanced overlayCubical
      hrho source point hpoint with
    ⟨cell, _hcell, hnested⟩
  intro other hother
  refine ⟨?_, ?_⟩
  · have hselectedCubical : WZ1PaperIsCubicalShading
        data.selectedFineShading := by
      rw [data.selectedFineShading_eq]
      exact restrictPaperShading_cubical data.selectedFine
        ambientFineCubical
    exact hselectedCubical source point hpoint.1 hother
  · rcases hpoint.2 with ⟨overlayParent, hoverlay⟩
    have hcoarse := overlayCubical overlayParent point hoverlay
    have hpointFineCell : point ∈
        wz1PaperGridCube delta (wz1PaperGridIndex delta point) :=
      (mem_wz1PaperGridCube delta
        (wz1PaperGridIndex delta point) point).mpr rfl
    have hpointCell : point ∈ wz1PaperGridCube rho cell :=
      hnested hpointFineCell
    have hcellEq : cell = wz1PaperGridIndex rho point :=
      ((mem_wz1PaperGridCube rho cell point).mp hpointCell).symm
    exact ⟨overlayParent, hcoarse (by
      rw [← hcellEq]
      exact hnested hother)⟩

/-- On an active overlay cell, intersecting the complete-parent fine shading
with the overlay changes nothing inside that whole coarse cell. -/
theorem overlayFine_inter_activeCell_eq
    (overlayCubical : WZ1PaperIsCubicalShading overlay)
    (hrho : 0 < rho)
    (cell : ℤ × ℤ × ℤ)
    (hcell : cell ∈ wz1PaperActiveCells overlay hrho) :
    (pureWZ2Node05CompleteParentOverlayFineShading data overlay).union ∩
        wz1PaperGridCube rho cell =
      data.selectedFineShading.union ∩ wz1PaperGridCube rho cell := by
  have hoverlayCell : overlay.union ∩ wz1PaperGridCube rho cell =
      wz1PaperGridCube rho cell :=
    overlayCubical.inter_activeCell_eq hrho hcell
  apply Set.Subset.antisymm
  · rintro point ⟨⟨source, hsource⟩, hpointCell⟩
    exact ⟨⟨source, hsource.1⟩, hpointCell⟩
  · rintro point ⟨⟨source, hsource⟩, hpointCell⟩
    have hoverlay : point ∈ overlay.union := by
      have hinter : point ∈ overlay.union ∩ wz1PaperGridCube rho cell := by
        rw [hoverlayCell]
        exact hpointCell
      exact hinter.1
    exact ⟨⟨source, hsource, hoverlay⟩, hpointCell⟩

/-- Every active overlay cell is active in the selected coarse parent
shading whenever the overlay is an honest subshading of it. -/
theorem overlay_activeCells_subset
    (overlaySubshading :
      PureWZ2PaperIsSubshading overlay data.selectedCoarseShading)
    (hrho : 0 < rho) :
    wz1PaperActiveCells overlay hrho ⊆
      wz1PaperActiveCells data.selectedCoarseShading hrho := by
  intro cell hcell
  rw [mem_wz1PaperActiveCells] at hcell ⊢
  rcases hcell.2 with ⟨point, ⟨parent, hoverlay⟩, hpointCell⟩
  exact ⟨hcell.1, ⟨point,
    ⟨parent, overlaySubshading parent hoverlay⟩, hpointCell⟩⟩

/-- The selected overlay itself carries the original balanced `cellMass`. -/
noncomputable def toOverlayBalanced
    (balanced : PureWZ2BalancedCoverData cover fineShading coarseShading)
    (coarseMultiplicityOne : ∀ point,
      (coarseShading.pointMultiplicity point : ENNReal) ≤ 1)
    (overlaySubshading :
      PureWZ2PaperIsSubshading overlay data.selectedCoarseShading)
    (overlayCubical : WZ1PaperIsCubicalShading overlay)
    (hrho : 0 < rho) :
    PureWZ2BalancedCoverData data.restrictedCover
      (pureWZ2Node05CompleteParentOverlayFineShading data overlay)
      overlay where
  point_compatibility := by
    intro source parent hcovered point hpoint
    have hparentEq : parent =
        data.restrictedCover.toWZ1PaperTubeCover.parent source :=
      data.restrictedCover.toWZ1PaperTubeCover.parent_unique
        source parent hcovered
    rw [hparentEq]
    exact data.overlayFine_point_compatibility overlay balanced
      coarseMultiplicityOne overlaySubshading source point hpoint
  coarse_cubical := overlayCubical
  activeCells := wz1PaperActiveCells overlay hrho
  coarse_union_eq := overlayCubical.union_eq_activeCells hrho
  cellMass := balanced.cellMass
  cellMass_pos := balanced.cellMass_pos
  cellMass_ne_top := balanced.cellMass_ne_top
  fine_cell_mass := by
    intro cell hcell
    rw [data.overlayFine_inter_activeCell_eq overlay overlayCubical
      hrho cell hcell]
    have hselectedCell := data.overlay_activeCells_subset overlay
      overlaySubshading hrho hcell
    rw [data.fine_inter_activeCell_eq balanced coarseMultiplicityOne
      hrho cell hselectedCell]
    exact balanced.fine_cell_mass cell
      (data.selected_activeCells_subset balanced hrho hselectedCell)

/-- At a point surviving the overlay, all complete-parent fine sources
survive the common spatial intersection, so point multiplicity is unchanged. -/
theorem overlayFine_pointMultiplicity_eq_selectedFine
    (point : Point3)
    (hpoint : point ∈
      (pureWZ2Node05CompleteParentOverlayFineShading data overlay).union) :
    (pureWZ2Node05CompleteParentOverlayFineShading data overlay).pointMultiplicity
        point =
      data.selectedFineShading.pointMultiplicity point := by
  rcases hpoint with ⟨witness, hwitness⟩
  have hoverlay : point ∈ overlay.union := hwitness.2
  unfold Kakeya.Streamlined.Shading.pointMultiplicity
  congr 1
  ext source
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hsource
    exact hsource.1
  · intro hsource
    exact ⟨hsource, hoverlay⟩

/-- Combining the overlay equality with unique coarse ownership transports an
ambient fine multiplicity band unchanged. -/
theorem overlayFine_constantMultiplicity
    (balanced : PureWZ2BalancedCoverData cover fineShading coarseShading)
    (coarseMultiplicityOne : ∀ point,
      (coarseShading.pointMultiplicity point : ENNReal) ≤ 1)
    {m M : ℕ}
    (ambientMultiplicity : fineShading.HasConstantMultiplicity m M) :
    Kakeya.Streamlined.Shading.HasConstantMultiplicity
      (pureWZ2Node05CompleteParentOverlayFineShading data overlay) m M := by
  intro point hpoint
  rw [data.overlayFine_pointMultiplicity_eq_selectedFine overlay point hpoint]
  apply data.selectedFine_constantMultiplicity balanced
    coarseMultiplicityOne ambientMultiplicity
  exact data.overlayFine_subshading overlay |>.union_subset hpoint

/-- Inside one complete selected parent, overlay restriction cannot increase
the ambient parent-fiber point multiplicity. -/
theorem overlayFiber_pointMultiplicity_le_ambient
    (parent : Fin selectedCoarse.family.card) (point : Point3) :
    (restrictPaperShading
      (Kakeya.Streamlined.TubeSubfamily.fromFinset
        data.selectedFine.family
        (wz2PaperFullFiberIndices data.selectedFine.family
          selectedCoarse.family parent))
      (pureWZ2Node05CompleteParentOverlayFineShading data overlay)
      ).pointMultiplicity point ≤
      (restrictPaperShading
        (Kakeya.Streamlined.TubeSubfamily.fromFinset fine
          (wz2PaperFullFiberIndices fine coarse
            (selectedCoarse.embedding parent)))
        fineShading).pointMultiplicity point := by
  let selectedFiber := Kakeya.Streamlined.TubeSubfamily.fromFinset
    data.selectedFine.family
    (wz2PaperFullFiberIndices data.selectedFine.family
      selectedCoarse.family parent)
  have hsub : PureWZ2PaperIsSubshading
      (restrictPaperShading selectedFiber
        (pureWZ2Node05CompleteParentOverlayFineShading data overlay))
      (restrictPaperShading selectedFiber data.selectedFineShading) := by
    intro source
    exact data.overlayFine_subshading overlay
      (selectedFiber.embedding source)
  exact (paperSubshading_pointMultiplicity_le _ _ hsub point).trans_eq
    (data.full_fiber_pointMultiplicity_eq parent point)

/-- Exact ambient fine multiplicity upgrades the overlay balanced cover to
the full Node-5 indexed-incidence receipt. -/
noncomputable def toOverlayNode5BalancedOfExactMultiplicity
    {ambientBase : PureWZ2BalancedCoverData cover fineShading coarseShading}
    (balanced : PureWZ2Node5BalancedCoverData ambientBase)
    (coarseMultiplicityOne : ∀ point,
      (coarseShading.pointMultiplicity point : ENNReal) ≤ 1)
    (overlaySubshading :
      PureWZ2PaperIsSubshading overlay data.selectedCoarseShading)
    (ambientFineCubical : WZ1PaperIsCubicalShading fineShading)
    (overlayCubical : WZ1PaperIsCubicalShading overlay)
    (hrho : 0 < rho)
    (m : ℕ) (hm : 0 < m)
    (ambientExact : fineShading.HasConstantMultiplicity m m) :
    PureWZ2Node5BalancedCoverData
      (data.toOverlayBalanced overlay ambientBase coarseMultiplicityOne
        overlaySubshading overlayCubical hrho) :=
  (data.toOverlayBalanced overlay ambientBase coarseMultiplicityOne
      overlaySubshading overlayCubical hrho)
    |>.toNode5OfExactMultiplicity m hm
      (data.overlayFine_constantMultiplicity overlay ambientBase
        coarseMultiplicityOne ambientExact)
      (data.overlayFine_cell_nested overlay balanced overlayCubical hrho)

end PureWZ2Node05CompleteParentPullbackData

/-- The exact remaining receipt for repackaging a first owner output after a
synchronized coarse selection.  Its dependent parameters bind the pullback
to the literal fine/coarse data of `ambient`; it cannot be paired with an
unrelated sticky output. -/
structure PureWZ2Node05CompleteParentOverlayReceipt
    {delta sigma ambientLoss outputLoss : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {rhoRequested : WZ2PaperRequestedScale delta}
    {ambientLogExponent : ℕ}
    (ambient : PureWZ2Node5StickyData
      (sigma := sigma) (outputLoss := ambientLoss)
      sourceShading rhoRequested ambientLogExponent)
    (selectedCoarse : Kakeya.Streamlined.TubeSubfamily ambient.coarse)
    (pullback : PureWZ2Node05CompleteParentPullbackData
      ambient.cover ambient.refined ambient.croppedCoarseShading
      selectedCoarse)
    (overlay : WZ1PaperTubeShading selectedCoarse.family)
    (outputLogExponent : ℕ) where
  overlaySubshading :
    PureWZ2PaperIsSubshading overlay pullback.selectedCoarseShading
  overlayCubical : WZ1PaperIsCubicalShading overlay
  ambientCoarseMultiplicityOne : ∀ point,
    (ambient.croppedCoarseShading.pointMultiplicity point : ENNReal) ≤ 1
  exactMultiplicity : ℕ
  exactMultiplicity_pos : 0 < exactMultiplicity
  ambientExactMultiplicity :
    ambient.refined.HasConstantMultiplicity
      exactMultiplicity exactMultiplicity
  fineRefinementExponent : ℕ
  fineRefinement :
    WZ1PaperRefinement ambient.seed.data.refined fineRefinementExponent
  coarseRefinementExponent : ℕ
  coarseRefinement : WZ1PaperRefinement
    ambient.seed.data.croppedCoarseShading coarseRefinementExponent
  logExponent_eq :
    outputLogExponent = ambient.seedLogExponent + fineRefinementExponent
  selected_eq :
    ambient.selected.comp pullback.selectedFine =
      ambient.seed.data.selected.comp fineRefinement.selected
  refined_eq : HEq
    (pureWZ2Node05CompleteParentOverlayFineShading pullback overlay)
    fineRefinement.refined
  coarse_eq : selectedCoarse.family = coarseRefinement.selected.family
  croppedCoarseShading_eq : HEq overlay coarseRefinement.refined
  retained_mass :
    wz2PaperPureRefinementFraction delta outputLogExponent *
        sourceShading.mass ≤
      (pureWZ2Node05CompleteParentOverlayFineShading
        pullback overlay).mass
  refined_extremal :
    WZ2PaperCroppedIsExtremal sigma outputLoss
      pullback.selectedFine.family
      (pureWZ2Node05CompleteParentOverlayFineShading pullback overlay)
  refined_volume_lower :
    Kakeya.realRpowENN delta (sigma + outputLoss) ≤
      volume (pureWZ2Node05CompleteParentOverlayFineShading
        pullback overlay).union
  coarse_extremal :
    WZ2PaperCroppedIsExtremal sigma outputLoss
      selectedCoarse.family overlay
  rescaledFiber :
    ∀ parent : Fin selectedCoarse.family.card,
      Nonempty
        (WZ2PaperPureRescaledFullFiberOutput
          (sigma := sigma) (loss := outputLoss)
          (restrictPaperShading
            (Kakeya.Streamlined.TubeSubfamily.fromFinset
              pullback.selectedFine.family
              (wz2PaperFullFiberIndices pullback.selectedFine.family
                selectedCoarse.family parent))
            (pureWZ2Node05CompleteParentOverlayFineShading
              pullback overlay))
          (selectedCoarse.family.tube parent)
          coarse_extremal.delta_pos)
  ambientLoss_le : ambientLoss ≤ outputLoss
  coarse_cardinality_absorption :
    Kakeya.realRpowENN rhoRequested.1 (2 - sigma - ambientLoss) *
        ambient.coarse.enncard ≤
      Kakeya.realRpowENN rhoRequested.1 (2 - sigma - outputLoss) *
        selectedCoarse.family.enncard
  coarse_volume_lower :
    Kakeya.realRpowENN rhoRequested.1 (sigma + outputLoss) ≤
      volume overlay.union

namespace PureWZ2Node05CompleteParentOverlayReceipt

variable
    {delta sigma ambientLoss outputLoss : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {rhoRequested : WZ2PaperRequestedScale delta}
    {ambientLogExponent outputLogExponent : ℕ}
    {ambient : PureWZ2Node5StickyData
      (sigma := sigma) (outputLoss := ambientLoss)
      sourceShading rhoRequested ambientLogExponent}
    {selectedCoarse : Kakeya.Streamlined.TubeSubfamily ambient.coarse}
    {pullback : PureWZ2Node05CompleteParentPullbackData
      ambient.cover ambient.refined ambient.croppedCoarseShading
      selectedCoarse}
    {overlay : WZ1PaperTubeShading selectedCoarse.family}

/-- Public sticky data on the synchronized coarse overlay and its complete
fine fibers. -/
noncomputable def toPropStickyData
    (receipt : PureWZ2Node05CompleteParentOverlayReceipt
      (outputLoss := outputLoss)
      ambient selectedCoarse pullback overlay outputLogExponent) :
    PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := outputLoss)
      sourceShading rhoRequested outputLogExponent where
  selected := ambient.selected.comp pullback.selectedFine
  selected_nonempty := pullback.selectedFine_nonempty
  refined := pureWZ2Node05CompleteParentOverlayFineShading pullback overlay
  subshading := by
    intro source point hpoint
    apply ambient.subshading (pullback.selectedFine.embedding source)
    have hselected : point ∈ pullback.selectedFineShading.carrier source :=
      hpoint.1
    rw [pullback.selectedFineShading_eq] at hselected
    exact hselected
  retained_mass := receipt.retained_mass
  refined_cubical := pullback.overlayFine_cubical overlay ambient.balanced
    ambient.refined_cubical receipt.overlayCubical
    ambient.coarse_extremal.delta_pos
  coarse := selectedCoarse.family
  cover := pullback.restrictedCover
  croppedCoarseShading := overlay
  balanced := pullback.toOverlayBalanced overlay ambient.data.balanced
    receipt.ambientCoarseMultiplicityOne receipt.overlaySubshading
    receipt.overlayCubical ambient.coarse_extremal.delta_pos
  coarse_extremal := receipt.coarse_extremal
  rescaledFiber := receipt.rescaledFiber
  coarse_multiplicity_upper := by
    intro point
    have hselectedNat : overlay.pointMultiplicity point ≤
        ambient.croppedCoarseShading.pointMultiplicity point := by
      calc
        overlay.pointMultiplicity point ≤
            pullback.selectedCoarseShading.pointMultiplicity point :=
          paperSubshading_pointMultiplicity_le overlay
            pullback.selectedCoarseShading receipt.overlaySubshading point
        _ ≤ ambient.croppedCoarseShading.pointMultiplicity point := by
          rw [pullback.selectedCoarseShading_eq]
          exact restrictPaperShading_pointMultiplicity_le selectedCoarse
            ambient.croppedCoarseShading point
    have hselected : (overlay.pointMultiplicity point : ENNReal) ≤
        (ambient.croppedCoarseShading.pointMultiplicity point : ENNReal) := by
      exact_mod_cast hselectedNat
    exact hselected.trans <| (ambient.coarse_multiplicity_upper point).trans
      receipt.coarse_cardinality_absorption
  fiber_multiplicity_upper := by
    intro parent point
    let localSet :=
      (wz2PaperFullFiberIndices pullback.selectedFine.family
        selectedCoarse.family parent).filter fun source =>
          point ∈ (pureWZ2Node05CompleteParentOverlayFineShading
            pullback overlay).carrier source
    let ambientSet :=
      (wz2PaperFullFiberIndices ambient.selected.family ambient.coarse
        (selectedCoarse.embedding parent)).filter fun source =>
          point ∈ ambient.refined.carrier source
    have hmaps : Set.MapsTo pullback.selectedFine.embedding
        (localSet : Set (Fin (wz1PaperBodyFamily
          pullback.selectedFine.family).card))
        (ambientSet : Set (Fin (wz1PaperBodyFamily
          ambient.selected.family).card)) := by
      intro source hsource
      have hsource' := Finset.mem_filter.mp hsource
      apply Finset.mem_filter.mpr
      refine ⟨?_, ?_⟩
      · have himage : pullback.selectedFine.embedding source ∈
            Finset.image pullback.selectedFine.embedding
              (wz2PaperFullFiberIndices pullback.selectedFine.family
                selectedCoarse.family parent) :=
          Finset.mem_image.mpr ⟨source, hsource'.1, rfl⟩
        rw [pullback.full_fiber_complete parent] at himage
        exact himage
      · have hselected : point ∈ pullback.selectedFineShading.carrier source :=
          hsource'.2.1
        rw [pullback.selectedFineShading_eq] at hselected
        exact hselected
    have hpointNat : localSet.card ≤ ambientSet.card :=
      Finset.card_le_card_of_injOn pullback.selectedFine.embedding hmaps
        pullback.selectedFine.embedding.injective.injOn
    have hpoint : (localSet.card : ENNReal) ≤ (ambientSet.card : ENNReal) := by
      exact_mod_cast hpointNat
    have hambient := ambient.fiber_multiplicity_upper
      (selectedCoarse.embedding parent) point
    have hpower : Kakeya.realRpowENN (delta / rhoRequested.1)
        (2 - sigma - ambientLoss) ≤
      Kakeya.realRpowENN (delta / rhoRequested.1)
        (2 - sigma - outputLoss) := by
      have hratioPos : 0 < delta / rhoRequested.1 :=
        div_pos ambient.refined_extremal.delta_pos
          ambient.coarse_extremal.delta_pos
      have hratioOne : delta / rhoRequested.1 ≤ 1 :=
        (div_le_one ambient.coarse_extremal.delta_pos).mpr
          rhoRequested.property.1
      apply ENNReal.ofReal_mono
      exact Real.rpow_le_rpow_of_exponent_ge hratioPos hratioOne
        (by linarith [receipt.ambientLoss_le])
    have hcardEq := pullback.full_fiber_card_eq parent
    calc
      (localSet.card : ENNReal) ≤
          Kakeya.realRpowENN (delta / rhoRequested.1)
            (2 - sigma - ambientLoss) *
          ((wz2PaperFullFiberIndices ambient.selected.family ambient.coarse
            (selectedCoarse.embedding parent)).card : ENNReal) :=
        hpoint.trans hambient
      _ ≤ Kakeya.realRpowENN (delta / rhoRequested.1)
            (2 - sigma - outputLoss) *
          ((wz2PaperFullFiberIndices ambient.selected.family ambient.coarse
            (selectedCoarse.embedding parent)).card : ENNReal) := by gcongr
      _ = Kakeya.realRpowENN (delta / rhoRequested.1)
            (2 - sigma - outputLoss) *
          ((wz2PaperFullFiberIndices pullback.selectedFine.family
            selectedCoarse.family parent).card : ENNReal) := by rw [hcardEq]

/-- Repackage the synchronized first output as the full Node-5 object.  All
structural fields are derived; the receipt exposes only the two honest paper
refinements and the non-hereditary quantitative estimates. -/
noncomputable def toNode5StickyData
    (receipt : PureWZ2Node05CompleteParentOverlayReceipt
      (outputLoss := outputLoss)
      ambient selectedCoarse pullback overlay outputLogExponent) :
    PureWZ2Node5StickyData
      (sigma := sigma) (outputLoss := outputLoss)
      sourceShading rhoRequested outputLogExponent where
  seedLoss := ambient.seedLoss
  seedNormalizationExponent := ambient.seedNormalizationExponent
  seedLogExponent := ambient.seedLogExponent
  seed := ambient.seed
  fineRefinementExponent := receipt.fineRefinementExponent
  fineRefinement := receipt.fineRefinement
  coarseRefinementExponent := receipt.coarseRefinementExponent
  coarseRefinement := receipt.coarseRefinement
  data := receipt.toPropStickyData
  logExponent_eq := receipt.logExponent_eq
  selected_eq := receipt.selected_eq
  refined_eq := receipt.refined_eq
  coarse_eq := receipt.coarse_eq
  croppedCoarseShading_eq := receipt.croppedCoarseShading_eq
  balanced := pullback.toOverlayNode5BalancedOfExactMultiplicity overlay
    ambient.balanced receipt.ambientCoarseMultiplicityOne
    receipt.overlaySubshading ambient.refined_cubical receipt.overlayCubical
    ambient.coarse_extremal.delta_pos receipt.exactMultiplicity
    receipt.exactMultiplicity_pos receipt.ambientExactMultiplicity
  fineMultiplicity := receipt.exactMultiplicity
  fineMultiplicity_pos := receipt.exactMultiplicity_pos
  refined_multiplicity_band := by
    intro point hpoint
    have hexact := pullback.overlayFine_constantMultiplicity overlay
      ambient.data.balanced receipt.ambientCoarseMultiplicityOne
      receipt.ambientExactMultiplicity point hpoint
    exact ⟨hexact.1, hexact.2.trans (by omega)⟩
  refined_extremal := receipt.refined_extremal
  refined_volume_lower := receipt.refined_volume_lower
  full_fiber_uniform := by
    apply pullback.full_fiber_uniform
      (Kakeya.realRpowENN rhoRequested.1 (-outputLoss))
    intro first second
    have hambient := ambient.full_fiber_uniform first second
    have hpower : Kakeya.realRpowENN rhoRequested.1 (-ambientLoss) ≤
        Kakeya.realRpowENN rhoRequested.1 (-outputLoss) :=
      pureWZ2_grain_constant_mono ambient.coarse_extremal.delta_pos
        ambient.coarse_extremal.delta_le_one receipt.ambientLoss_le
    exact hambient.trans <| by gcongr
  coarse_volume_lower := receipt.coarse_volume_lower

end PureWZ2Node05CompleteParentOverlayReceipt

end Kakeya.Assouad

end
