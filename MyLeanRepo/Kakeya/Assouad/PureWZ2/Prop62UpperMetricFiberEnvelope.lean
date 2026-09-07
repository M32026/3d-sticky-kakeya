import MyLeanRepo.Kakeya.Assouad.PureWZ2.LineCoverCarrierContainment
import MyLeanRepo.Kakeya.Assouad.PureWZ2.NormalizationOrdinaryPaperCWABridge
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62UpperPaperCarrierHomothety
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperJohnHomotheticEnvelope
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Section6CoverParentMap
import MyLeanRepo.Kakeya.Streamlined.RandomTranslation.TubeDensityTestNet.GeometricLemmas

/-!
# Proposition 6.2: a common envelope for contained metric children

The Section 6 relation is a supporting-line relation, not ordinary carrier
containment.  For normalized tubes in the fixed crop box, a fine ordinary
carrier lies in its cropped paper carrier; the scale gap sends that paper
carrier into the metric child's paper carrier; and a centered metric child's
paper carrier lies in a factor-`100` homothety of its ordinary carrier.

Taking the convex hull of all contained metric-child carriers and applying
the outer-John common-envelope theorem gives one convex set containing every
complete genuine metric fiber, with an absolute volume loss.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

theorem pureWZ2_prop62_metric_children_common_envelope
    {delta rho : ℝ}
    (deltaPos : 0 < delta)
    (rhoPos : 0 < rho)
    (scaleGap : 4 * delta ≤ rho)
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : PureWZ2Section6Cover fine coarse)
    (fineAxisBox :
      ∀ source,
        (fine.tube source).carrier ⊆
          Kakeya.Streamlined.axisBox 2 2 2)
    (coarseCentered :
      ∀ parent,
        wz2PaperCenteredLineTube (targetScale := rho)
            (coarse.tube parent) =
          coarse.tube parent)
    (selected : Finset (Fin coarse.card))
    (selectedNonempty : selected.Nonempty)
    (convexSet : Set Point3)
    (convexSetConvex : Convex ℝ convexSet)
    (selectedContained :
      ∀ parent ∈ selected,
        (coarse.tube parent).carrier ⊆ convexSet) :
    ∃ envelope : Set Point3,
      Convex ℝ envelope ∧
      volume envelope ≤
        (212776173 : ENNReal) * volume convexSet ∧
      ∀ source,
        cover.toWZ1PaperTubeCover.parent source ∈ selected →
          (fine.tube source).carrier ⊆ envelope := by
  let selectedUnion : Set Point3 :=
    ⋃ parent ∈ selected, (coarse.tube parent).carrier
  let convexBody : Set Point3 :=
    convexHull ℝ selectedUnion
  have convexBodyCompact : IsCompact convexBody := by
    exact
      Kakeya.Streamlined.RandomTranslation.isCompact_convexHull_finite_union
        selected
        (fun parent => (coarse.tube parent).carrier)
        (by
          intro parent _parentMem
          exact
            ⟨wz2_paper_ordinary_tube_carrier_compact
                (coarse.tube parent) rhoPos,
              wz2_paper_ordinary_tube_carrier_convex
                (coarse.tube parent)⟩)
  have convexBodyConvex : Convex ℝ convexBody :=
    convex_convexHull ℝ selectedUnion
  have convexBodySubset : convexBody ⊆ convexSet := by
    apply convexHull_min
    · intro point pointMem
      simp only [selectedUnion, Set.mem_iUnion] at pointMem
      rcases pointMem with ⟨parent, pointMem⟩
      rcases pointMem with ⟨parentMem, pointMem⟩
      exact selectedContained parent parentMem pointMem
    · exact convexSetConvex
  rcases selectedNonempty with ⟨reference, referenceMem⟩
  have referenceCarrierSubset :
      (coarse.tube reference).carrier ⊆ convexBody := by
    intro point pointMem
    apply subset_convexHull ℝ selectedUnion
    exact
      Set.mem_iUnion.mpr
        ⟨reference,
          Set.mem_iUnion.mpr ⟨referenceMem, pointMem⟩⟩
  have convexBodyInterior :
      (interior convexBody).Nonempty := by
    exact
      (Kakeya.Streamlined.RandomTranslation.deltaTube_nonempty_interior
        rhoPos (coarse.tube reference)).mono
          (interior_mono referenceCarrierSubset)
  have convexBodyIsBody :
      JohnEllipsoid.IsConvexBody convexBody :=
    ⟨convexBodyConvex, convexBodyCompact, convexBodyInterior⟩
  rcases
      wz2_paper_john_homothetic_envelope
        convexBody convexBodyIsBody
    with
    ⟨envelope, envelopeConvex, envelopeVolume,
      envelopeContains⟩
  refine
    ⟨envelope, envelopeConvex,
      envelopeVolume.trans ?_, ?_⟩
  · exact
      mul_le_mul_left'
        (measure_mono convexBodySubset)
        (212776173 : ENNReal)
  · intro source sourceOwnerMem
    let parent :=
      cover.toWZ1PaperTubeCover.parent source
    have parentCarrierSubset :
        (coarse.tube parent).carrier ⊆ convexBody := by
      intro point pointMem
      apply subset_convexHull ℝ selectedUnion
      exact
        Set.mem_iUnion.mpr
          ⟨parent,
            Set.mem_iUnion.mpr
              ⟨sourceOwnerMem, pointMem⟩⟩
    have parentMidpointMem :
        wz2PaperTubeMidpoint (coarse.tube parent) ∈ convexBody :=
      parentCarrierSubset
        (wz2_paper_tubeMidpoint_mem_carrier
          (coarse.tube parent) rhoPos.le)
    have ordinaryToFinePaper :
        (fine.tube source).carrier ⊆
          wz1PaperTubeCarrier (fine.tube source) :=
      ordinary_carrier_subset_paper_of_axisBox
        deltaPos (fine.tube source) (fineAxisBox source)
    have finePaperToParentPaper :
        wz1PaperTubeCarrier (fine.tube source) ⊆
          wz1PaperTubeCarrier (coarse.tube parent) :=
      wz1PaperTubeCarrier_subset_of_lineCover
        deltaPos rhoPos scaleGap
        (fine.tube source) (coarse.tube parent)
        (cover.fine_line_class source)
        (cover.coarse_line_class parent)
        (cover.toWZ1PaperTubeCover.parent_covers source)
    have parentPaperToHomothety :
        wz1PaperTubeCarrier (coarse.tube parent) ⊆
          AffineMap.homothety
              (wz2PaperTubeMidpoint (coarse.tube parent))
              (100 : ℝ) ''
            (coarse.tube parent).carrier :=
      wz1PaperTubeCarrier_subset_centered_homothety_hundred
        rhoPos (coarse.tube parent)
        (cover.coarse_line_class parent)
        (coarseCentered parent)
    exact
      ordinaryToFinePaper.trans <|
        finePaperToParentPaper.trans <|
          parentPaperToHomothety.trans <|
            (Set.image_mono parentCarrierSubset).trans <|
              envelopeContains
                (wz2PaperTubeMidpoint (coarse.tube parent))
                parentMidpointMem

end Kakeya.Assouad

end
