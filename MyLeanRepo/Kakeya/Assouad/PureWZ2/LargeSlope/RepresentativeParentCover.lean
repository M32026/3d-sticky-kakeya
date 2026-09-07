import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.LocalizedAssignedParentCover
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.LocalizedRelabelParent
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.PureFiniteStrongParentSelection
import MyLeanRepo.Kakeya.Assouad.WZ1.PaperPackingRefinement

/-!
# Representative-axis parents for a localized target family

At one source Definition 2.12 scale, choose one target tube above each
nonempty complete source fiber.  Every target tube in that fiber is close to
the representative in the target paper-line metric.  Centering the
representative segment and enlarging only its radius therefore gives a strict
ordinary parent.

This is the scale-covariant parent construction used in Proposition 6.5.  It
does not transform the stored segment of the source parent and hence avoids
the endpoint mismatch of the historical direct-parent route.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

/-- One-scale inputs for the representative-axis parent construction. -/
structure PureWZ2RepresentativeParentCoverData
    {sourceDelta sourceRho targetDelta targetRho lineBound : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceConstant : ENNReal}
    (sourceScale :
      WZ2PaperPureScaleCoverData sourceFine sourceRho sourceConstant)
    (targetFine : Kakeya.Streamlined.TubeFamily targetDelta)
    (sourceEquiv : Fin targetFine.card ≃ Fin sourceFine.card) where
  source_nonempty : sourceFine.Nonempty
  target_delta_pos : 0 < targetDelta
  target_rho_pos : 0 < targetRho
  target_line_class : WZ1PaperIsLineClass targetFine
  target_ordinary_distinct : WZ2PaperOrdinaryIsEssentiallyDistinct targetFine
  target_midpoint_local : ∀ target,
    ‖wz2PaperTubeMidpoint (targetFine.tube target)‖ ≤ 3
  target_packing_distinct : WZ1PaperIsEssentiallyDistinct
    (wz2PaperRelabelFamily
      (sourceScale := targetDelta)
      (targetScale := (2 / 3 : ℝ) * targetDelta) targetFine)
  target_carrier_subset_relabel :
    ∀ {rho : ℝ}, 0 < rho → ∀ first second,
      (3 / 2 : ℝ) *
          wz1PaperLineDistance
            (targetFine.tube first) (targetFine.tube second) +
        targetDelta ≤ rho →
      (targetFine.tube first).carrier ⊆
        (wz2PaperRelabelTube (targetScale := rho)
          (targetFine.tube second)).carrier
  common_source_parent_lineDistance :
    ∀ first second,
      sourceScale.cover.parent (sourceEquiv first) =
          sourceScale.cover.parent (sourceEquiv second) →
        wz1PaperLineDistance
          (targetFine.tube first) (targetFine.tube second) ≤ lineBound
  containment_budget :
    (3 / 2 : ℝ) * lineBound + targetDelta ≤ targetRho

namespace PureWZ2RepresentativeParentCoverData

/-- A source child chosen from each nonempty complete source fiber. -/
noncomputable def sourceRepresentative
    {sourceDelta sourceRho targetDelta targetRho lineBound : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceConstant : ENNReal}
    {sourceScale :
      WZ2PaperPureScaleCoverData sourceFine sourceRho sourceConstant}
    {targetFine : Kakeya.Streamlined.TubeFamily targetDelta}
    {sourceEquiv : Fin targetFine.card ≃ Fin sourceFine.card}
    (data : PureWZ2RepresentativeParentCoverData
      (targetRho := targetRho) (lineBound := lineBound)
      sourceScale targetFine sourceEquiv)
    (parent : Fin sourceScale.coarse.card) : Fin sourceFine.card :=
  Classical.choose
    (sourceScale.cover.fullFiber_nonempty_of_uniform
      data.source_nonempty sourceScale.full_fiber_uniform parent)

theorem sourceRepresentative_mem
    {sourceDelta sourceRho targetDelta targetRho lineBound : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceConstant : ENNReal}
    {sourceScale :
      WZ2PaperPureScaleCoverData sourceFine sourceRho sourceConstant}
    {targetFine : Kakeya.Streamlined.TubeFamily targetDelta}
    {sourceEquiv : Fin targetFine.card ≃ Fin sourceFine.card}
    (data : PureWZ2RepresentativeParentCoverData
      (targetRho := targetRho) (lineBound := lineBound)
      sourceScale targetFine sourceEquiv)
    (parent : Fin sourceScale.coarse.card) :
    data.sourceRepresentative parent ∈
      wz2PaperOrdinaryFullFiberIndices
        sourceFine sourceScale.coarse parent :=
  Classical.choose_spec
    (sourceScale.cover.fullFiber_nonempty_of_uniform
      data.source_nonempty sourceScale.full_fiber_uniform parent)

theorem sourceRepresentative_parent
    {sourceDelta sourceRho targetDelta targetRho lineBound : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceConstant : ENNReal}
    {sourceScale :
      WZ2PaperPureScaleCoverData sourceFine sourceRho sourceConstant}
    {targetFine : Kakeya.Streamlined.TubeFamily targetDelta}
    {sourceEquiv : Fin targetFine.card ≃ Fin sourceFine.card}
    (data : PureWZ2RepresentativeParentCoverData
      (targetRho := targetRho) (lineBound := lineBound)
      sourceScale targetFine sourceEquiv)
    (parent : Fin sourceScale.coarse.card) :
    sourceScale.cover.parent (data.sourceRepresentative parent) = parent :=
  (sourceScale.cover.mem_fullFiber_iff_parent_eq
    sourceScale.rho_pos.le parent (data.sourceRepresentative parent)).mp
      (data.sourceRepresentative_mem parent)

theorem sourceRepresentative_injective
    {sourceDelta sourceRho targetDelta targetRho lineBound : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceConstant : ENNReal}
    {sourceScale :
      WZ2PaperPureScaleCoverData sourceFine sourceRho sourceConstant}
    {targetFine : Kakeya.Streamlined.TubeFamily targetDelta}
    {sourceEquiv : Fin targetFine.card ≃ Fin sourceFine.card}
    (data : PureWZ2RepresentativeParentCoverData
      (targetRho := targetRho) (lineBound := lineBound)
      sourceScale targetFine sourceEquiv) :
    Function.Injective data.sourceRepresentative := by
  intro first second heq
  have hparents := congrArg sourceScale.cover.parent heq
  simpa [data.sourceRepresentative_parent first,
    data.sourceRepresentative_parent second] using hparents

/-- The synchronized target representative above a source parent. -/
noncomputable def targetRepresentative
    {sourceDelta sourceRho targetDelta targetRho lineBound : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceConstant : ENNReal}
    {sourceScale :
      WZ2PaperPureScaleCoverData sourceFine sourceRho sourceConstant}
    {targetFine : Kakeya.Streamlined.TubeFamily targetDelta}
    {sourceEquiv : Fin targetFine.card ≃ Fin sourceFine.card}
    (data : PureWZ2RepresentativeParentCoverData
      (targetRho := targetRho) (lineBound := lineBound)
      sourceScale targetFine sourceEquiv)
    (parent : Fin sourceScale.coarse.card) : Fin targetFine.card :=
  sourceEquiv.symm (data.sourceRepresentative parent)

theorem targetRepresentative_injective
    {sourceDelta sourceRho targetDelta targetRho lineBound : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceConstant : ENNReal}
    {sourceScale :
      WZ2PaperPureScaleCoverData sourceFine sourceRho sourceConstant}
    {targetFine : Kakeya.Streamlined.TubeFamily targetDelta}
    {sourceEquiv : Fin targetFine.card ≃ Fin sourceFine.card}
    (data : PureWZ2RepresentativeParentCoverData
      (targetRho := targetRho) (lineBound := lineBound)
      sourceScale targetFine sourceEquiv) :
    Function.Injective data.targetRepresentative :=
  sourceEquiv.symm.injective.comp data.sourceRepresentative_injective

/-- The representative target axes at the canonical radius `2 delta / 3`,
used only for paper-line packing. -/
def representativePackingFamily
    {sourceDelta sourceRho targetDelta targetRho lineBound : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceConstant : ENNReal}
    {sourceScale :
      WZ2PaperPureScaleCoverData sourceFine sourceRho sourceConstant}
    {targetFine : Kakeya.Streamlined.TubeFamily targetDelta}
    {sourceEquiv : Fin targetFine.card ≃ Fin sourceFine.card}
    (data : PureWZ2RepresentativeParentCoverData
      (targetRho := targetRho) (lineBound := lineBound)
      sourceScale targetFine sourceEquiv) :
    Kakeya.Streamlined.TubeFamily ((2 / 3 : ℝ) * targetDelta) where
  card := sourceScale.coarse.card
  tube parent := wz2PaperRelabelTube
    (targetScale := (2 / 3 : ℝ) * targetDelta)
    (targetFine.tube (data.targetRepresentative parent))

/-- The actual ordinary parent family: center each representative segment and
enlarge only its radius. -/
def parentFamily
    {sourceDelta sourceRho targetDelta targetRho lineBound : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceConstant : ENNReal}
    {sourceScale :
      WZ2PaperPureScaleCoverData sourceFine sourceRho sourceConstant}
    {targetFine : Kakeya.Streamlined.TubeFamily targetDelta}
    {sourceEquiv : Fin targetFine.card ≃ Fin sourceFine.card}
    (data : PureWZ2RepresentativeParentCoverData
      (targetRho := targetRho) (lineBound := lineBound)
      sourceScale targetFine sourceEquiv) :
    Kakeya.Streamlined.TubeFamily targetRho where
  card := sourceScale.coarse.card
  tube parent :=
    wz2PaperRelabelTube (targetScale := targetRho)
      (targetFine.tube (data.targetRepresentative parent))

theorem representativePacking_line_class
    {sourceDelta sourceRho targetDelta targetRho lineBound : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceConstant : ENNReal}
    {sourceScale :
      WZ2PaperPureScaleCoverData sourceFine sourceRho sourceConstant}
    {targetFine : Kakeya.Streamlined.TubeFamily targetDelta}
    {sourceEquiv : Fin targetFine.card ≃ Fin sourceFine.card}
    (data : PureWZ2RepresentativeParentCoverData
      (targetRho := targetRho) (lineBound := lineBound)
      sourceScale targetFine sourceEquiv) :
    WZ1PaperIsLineClass data.representativePackingFamily := by
  intro parent
  exact wz2PaperRelabelTube_lineClass
    (data.target_line_class (data.targetRepresentative parent))

theorem representativePacking_paper_distinct
    {sourceDelta sourceRho targetDelta targetRho lineBound : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceConstant : ENNReal}
    {sourceScale :
      WZ2PaperPureScaleCoverData sourceFine sourceRho sourceConstant}
    {targetFine : Kakeya.Streamlined.TubeFamily targetDelta}
    {sourceEquiv : Fin targetFine.card ≃ Fin sourceFine.card}
    (data : PureWZ2RepresentativeParentCoverData
      (targetRho := targetRho) (lineBound := lineBound)
      sourceScale targetFine sourceEquiv) :
    WZ1PaperIsEssentiallyDistinct data.representativePackingFamily := by
  intro first second hne
  exact data.target_packing_distinct
    (data.targetRepresentative first) (data.targetRepresentative second)
    (data.targetRepresentative_injective.ne hne)

theorem parent_line_class
    {sourceDelta sourceRho targetDelta targetRho lineBound : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceConstant : ENNReal}
    {sourceScale :
      WZ2PaperPureScaleCoverData sourceFine sourceRho sourceConstant}
    {targetFine : Kakeya.Streamlined.TubeFamily targetDelta}
    {sourceEquiv : Fin targetFine.card ≃ Fin sourceFine.card}
    (data : PureWZ2RepresentativeParentCoverData
      (targetRho := targetRho) (lineBound := lineBound)
      sourceScale targetFine sourceEquiv) :
    WZ1PaperIsLineClass data.parentFamily := by
  intro parent
  exact wz2PaperRelabelTube_lineClass
    (data.target_line_class (data.targetRepresentative parent))

theorem parent_lineDistance
    {sourceDelta sourceRho targetDelta targetRho lineBound : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceConstant : ENNReal}
    {sourceScale :
      WZ2PaperPureScaleCoverData sourceFine sourceRho sourceConstant}
    {targetFine : Kakeya.Streamlined.TubeFamily targetDelta}
    {sourceEquiv : Fin targetFine.card ≃ Fin sourceFine.card}
    (data : PureWZ2RepresentativeParentCoverData
      (targetRho := targetRho) (lineBound := lineBound)
      sourceScale targetFine sourceEquiv)
    (first second : Fin sourceScale.coarse.card) :
    wz1PaperLineDistance
        (data.parentFamily.tube first) (data.parentFamily.tube second) =
      wz1PaperLineDistance
        (targetFine.tube (data.targetRepresentative first))
        (targetFine.tube (data.targetRepresentative second)) := by
  change wz1PaperLineDistance
      (wz2PaperRelabelTube
        (targetFine.tube (data.targetRepresentative first)))
      (wz2PaperRelabelTube
        (targetFine.tube (data.targetRepresentative second))) = _
  rw [wz2PaperRelabelTube_lineDistance_both]

theorem representativePacking_lineDistance
    {sourceDelta sourceRho targetDelta targetRho lineBound : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceConstant : ENNReal}
    {sourceScale :
      WZ2PaperPureScaleCoverData sourceFine sourceRho sourceConstant}
    {targetFine : Kakeya.Streamlined.TubeFamily targetDelta}
    {sourceEquiv : Fin targetFine.card ≃ Fin sourceFine.card}
    (data : PureWZ2RepresentativeParentCoverData
      (targetRho := targetRho) (lineBound := lineBound)
      sourceScale targetFine sourceEquiv)
    (first second : Fin sourceScale.coarse.card) :
    wz1PaperLineDistance
        (data.representativePackingFamily.tube first)
        (data.representativePackingFamily.tube second) =
      wz1PaperLineDistance
        (targetFine.tube (data.targetRepresentative first))
        (targetFine.tube (data.targetRepresentative second)) := by
  change wz1PaperLineDistance
      (wz2PaperRelabelTube
        (targetFine.tube (data.targetRepresentative first)))
      (wz2PaperRelabelTube
        (targetFine.tube (data.targetRepresentative second))) = _
  rw [wz2PaperRelabelTube_lineDistance_both]

/-- Every target child is strictly contained in the relabelled target
representative of its complete source fiber. -/
theorem assigned_containment
    {sourceDelta sourceRho targetDelta targetRho lineBound : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceConstant : ENNReal}
    {sourceScale :
      WZ2PaperPureScaleCoverData sourceFine sourceRho sourceConstant}
    {targetFine : Kakeya.Streamlined.TubeFamily targetDelta}
    {sourceEquiv : Fin targetFine.card ≃ Fin sourceFine.card}
    (data : PureWZ2RepresentativeParentCoverData
      (targetRho := targetRho) (lineBound := lineBound)
      sourceScale targetFine sourceEquiv)
    (target : Fin targetFine.card) :
    (targetFine.tube target).carrier ⊆
      (data.parentFamily.tube
        (sourceScale.cover.parent (sourceEquiv target))).carrier := by
  let parent := sourceScale.cover.parent (sourceEquiv target)
  have hrepresentativeParent :
      sourceScale.cover.parent
          (sourceEquiv (data.targetRepresentative parent)) = parent := by
    simpa [targetRepresentative] using data.sourceRepresentative_parent parent
  have hdistance :
      wz1PaperLineDistance
          (targetFine.tube target)
          (targetFine.tube (data.targetRepresentative parent)) ≤
        lineBound := by
    apply data.common_source_parent_lineDistance
    exact hrepresentativeParent.symm
  exact data.target_carrier_subset_relabel data.target_rho_pos target
    (data.targetRepresentative parent)
    (hdistance |> fun h => data.containment_budget.trans' <| by gcongr)

/-- Before strong separation, the representative-axis construction is an
honest strict assigned-parent cover. -/
noncomputable def toPreAssignedParentCover
    {sourceDelta sourceRho targetDelta targetRho lineBound : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceConstant : ENNReal}
    {sourceScale :
      WZ2PaperPureScaleCoverData sourceFine sourceRho sourceConstant}
    {targetFine : Kakeya.Streamlined.TubeFamily targetDelta}
    {sourceEquiv : Fin targetFine.card ≃ Fin sourceFine.card}
    (data : PureWZ2RepresentativeParentCoverData
      (targetRho := targetRho) (lineBound := lineBound)
      sourceScale targetFine sourceEquiv) :
    PureWZ2LocalizedPreAssignedParentCoverData
      targetFine data.parentFamily where
  delta_pos := data.target_delta_pos
  rho_pos := data.target_rho_pos
  fine_line_class := data.target_line_class
  coarse_line_class := data.parent_line_class
  fine_midpoint_local := data.target_midpoint_local
  assignedParent := fun target =>
    sourceScale.cover.parent (sourceEquiv target)
  assigned_containment := data.assigned_containment

/-- Packing degree for the strong-separation conflict graph on target
representative parents. -/
def parentConflictDegree
    {sourceDelta sourceRho targetDelta targetRho lineBound : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceConstant : ENNReal}
    {sourceScale :
      WZ2PaperPureScaleCoverData sourceFine sourceRho sourceConstant}
    {targetFine : Kakeya.Streamlined.TubeFamily targetDelta}
    {sourceEquiv : Fin targetFine.card ≃ Fin sourceFine.card}
    (_data : PureWZ2RepresentativeParentCoverData
      (targetRho := targetRho) (lineBound := lineBound)
      sourceScale targetFine sourceEquiv) : ℕ :=
  (2 * Nat.ceil
      (8 * (2 * wz2PaperLocalizedDoubledFiberLineDistanceConstant *
        targetRho) / ((2 / 3 : ℝ) * targetDelta)) + 1) ^ 5

theorem parentConflict_degree
    {sourceDelta sourceRho targetDelta targetRho lineBound : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceConstant : ENNReal}
    {sourceScale :
      WZ2PaperPureScaleCoverData sourceFine sourceRho sourceConstant}
    {targetFine : Kakeya.Streamlined.TubeFamily targetDelta}
    {sourceEquiv : Fin targetFine.card ≃ Fin sourceFine.card}
    (data : PureWZ2RepresentativeParentCoverData
      (targetRho := targetRho) (lineBound := lineBound)
      sourceScale targetFine sourceEquiv)
    (parent : Fin sourceScale.coarse.card) :
    ((Finset.univ : Finset (Fin sourceScale.coarse.card)).filter
      (fun other =>
        wz1PaperLineDistance
            (data.parentFamily.tube parent)
            (data.parentFamily.tube other) ≤
          2 * wz2PaperLocalizedDoubledFiberLineDistanceConstant *
            targetRho)).card ≤ data.parentConflictDegree := by
  have hsep :
      0 < 2 * wz2PaperLocalizedDoubledFiberLineDistanceConstant *
        targetRho := by
    unfold wz2PaperLocalizedDoubledFiberLineDistanceConstant
    nlinarith [data.target_rho_pos]
  have hpacking := tube_packing_bound_general
    data.representativePacking_paper_distinct
    data.representativePacking_line_class
    (by nlinarith [data.target_delta_pos] :
      0 < (2 / 3 : ℝ) * targetDelta)
    (2 * wz2PaperLocalizedDoubledFiberLineDistanceConstant * targetRho)
    hsep parent
  have hpacking' :
      ((Finset.univ : Finset (Fin sourceScale.coarse.card)).filter
        (fun other =>
          wz1PaperLineDistance
              (data.representativePackingFamily.tube other)
              (data.representativePackingFamily.tube parent) ≤
            2 * wz2PaperLocalizedDoubledFiberLineDistanceConstant *
              targetRho)).card ≤ data.parentConflictDegree := by
    exact hpacking
  have hfilter :
      (Finset.univ : Finset (Fin sourceScale.coarse.card)).filter
          (fun other =>
            wz1PaperLineDistance
                (data.parentFamily.tube parent)
                (data.parentFamily.tube other) ≤
              2 * wz2PaperLocalizedDoubledFiberLineDistanceConstant *
                targetRho) =
        (Finset.univ : Finset (Fin sourceScale.coarse.card)).filter
          (fun other =>
            wz1PaperLineDistance
                (data.representativePackingFamily.tube other)
                (data.representativePackingFamily.tube parent) ≤
              2 * wz2PaperLocalizedDoubledFiberLineDistanceConstant *
                targetRho) := by
    ext other
    constructor
    · intro hother
      have hdistance := (Finset.mem_filter.mp hother).2
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [data.representativePacking_lineDistance]
      rw [← wz1PaperLineDistance_symm]
      rw [← data.parent_lineDistance]
      exact hdistance
    · intro hother
      have hdistance := (Finset.mem_filter.mp hother).2
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [data.parent_lineDistance]
      rw [wz1PaperLineDistance_symm]
      rw [← data.representativePacking_lineDistance]
      exact hdistance
  rw [hfilter]
  exact hpacking'

end PureWZ2RepresentativeParentCoverData

/-- A finite schedule of preliminary representative-axis parents.  Strong
separation is selected simultaneously across every coordinate before any
public cover is formed. -/
structure PureWZ2FiniteRepresentativeParentScheduleData
    {sourceDelta targetDelta : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    (targetFine : Kakeya.Streamlined.TubeFamily targetDelta)
    (sourceEquiv : Fin targetFine.card ≃ Fin sourceFine.card)
    (sourceConstant : ENNReal) (scaleCount : ℕ) where
  sourceRho : Fin scaleCount → ℝ
  targetRho : Fin scaleCount → ℝ
  lineBound : Fin scaleCount → ℝ
  sourceScale : ∀ coordinate,
    WZ2PaperPureScaleCoverData
      sourceFine (sourceRho coordinate) sourceConstant
  parentData : ∀ coordinate,
    PureWZ2RepresentativeParentCoverData
      (targetRho := targetRho coordinate)
      (lineBound := lineBound coordinate)
      (sourceScale coordinate) targetFine sourceEquiv

namespace PureWZ2FiniteRepresentativeParentScheduleData

abbrev Parent
    {sourceDelta targetDelta : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {targetFine : Kakeya.Streamlined.TubeFamily targetDelta}
    {sourceEquiv : Fin targetFine.card ≃ Fin sourceFine.card}
    {sourceConstant : ENNReal} {scaleCount : ℕ}
    (schedule : PureWZ2FiniteRepresentativeParentScheduleData
      targetFine sourceEquiv sourceConstant scaleCount)
    (coordinate : Fin scaleCount) : Type :=
  Fin (schedule.sourceScale coordinate).coarse.card

/-- Select complete source-parent fibers at every coordinate.  The selected
target support loses only the product of the explicit packing degrees. -/
theorem simultaneouslySeparate
    {sourceDelta targetDelta : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {targetFine : Kakeya.Streamlined.TubeFamily targetDelta}
    {sourceEquiv : Fin targetFine.card ≃ Fin sourceFine.card}
    {sourceConstant : ENNReal} {scaleCount : ℕ}
    (schedule : PureWZ2FiniteRepresentativeParentScheduleData
      targetFine sourceEquiv sourceConstant scaleCount)
    (weight : Fin targetFine.card → ENNReal) :
    Nonempty (PureWZ2FiniteStrongParentSelectionData
      weight scaleCount schedule.Parent
      (fun coordinate target =>
        (schedule.sourceScale coordinate).cover.parent
          (sourceEquiv target))
      (fun coordinate first second =>
        wz1PaperLineDistance
            ((schedule.parentData coordinate).parentFamily.tube first)
            ((schedule.parentData coordinate).parentFamily.tube second) ≤
          2 * wz2PaperLocalizedDoubledFiberLineDistanceConstant *
            schedule.targetRho coordinate)
      (Finset.univ.sup fun coordinate =>
        (schedule.parentData coordinate).parentConflictDegree)) := by
  let conflict : ∀ coordinate,
      schedule.Parent coordinate → schedule.Parent coordinate → Prop :=
    fun coordinate first second =>
      wz1PaperLineDistance
          ((schedule.parentData coordinate).parentFamily.tube first)
          ((schedule.parentData coordinate).parentFamily.tube second) ≤
        2 * wz2PaperLocalizedDoubledFiberLineDistanceConstant *
          schedule.targetRho coordinate
  let degree : ℕ := Finset.univ.sup fun coordinate =>
    (schedule.parentData coordinate).parentConflictDegree
  apply pureWZ2_finite_strong_parent_selection
      weight scaleCount schedule.Parent
      (fun coordinate target =>
        (schedule.sourceScale coordinate).cover.parent
          (sourceEquiv target))
      conflict degree
  · intro coordinate parent
    dsimp only [conflict]
    have hdirection :
        wz1PaperDirection
            ((schedule.parentData coordinate).parentFamily.tube parent) ≠ 0 := by
      intro hzero
      have hnorm := wz1PaperDirection_norm
        ((schedule.parentData coordinate).parentFamily.tube parent)
      rw [hzero, norm_zero] at hnorm
      norm_num at hnorm
    have hzero : wz1PaperLineDistance
        ((schedule.parentData coordinate).parentFamily.tube parent)
        ((schedule.parentData coordinate).parentFamily.tube parent) = 0 := by
      simp [wz1PaperLineDistance, dist_self,
        InnerProductGeometry.angle_self hdirection]
    rw [hzero]
    have hrho := (schedule.parentData coordinate).target_rho_pos
    unfold wz2PaperLocalizedDoubledFiberLineDistanceConstant
    nlinarith
  · intro coordinate first second hconflict
    dsimp only [conflict] at *
    rw [wz1PaperLineDistance_symm]
    exact hconflict
  · intro coordinate parent
    have hcoordinate :
        (schedule.parentData coordinate).parentConflictDegree ≤ degree := by
      dsimp only [degree]
      exact Finset.le_sup
        (f := fun other : Fin scaleCount =>
          (schedule.parentData other).parentConflictDegree)
        (Finset.mem_univ coordinate)
    exact ((schedule.parentData coordinate).parentConflict_degree parent).trans
      hcoordinate

/-- At every coordinate, the parents hit after simultaneous selection are
strongly separated, so the preliminary assignment becomes a genuine public
partitioning cover with complete strict fibers. -/
noncomputable def selectedCover
    {sourceDelta targetDelta : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {targetFine : Kakeya.Streamlined.TubeFamily targetDelta}
    {sourceEquiv : Fin targetFine.card ≃ Fin sourceFine.card}
    {sourceConstant : ENNReal} {scaleCount : ℕ}
    (schedule : PureWZ2FiniteRepresentativeParentScheduleData
      targetFine sourceEquiv sourceConstant scaleCount)
    (weight : Fin targetFine.card → ENNReal)
    (selection : PureWZ2FiniteStrongParentSelectionData
      weight scaleCount schedule.Parent
      (fun coordinate target =>
        (schedule.sourceScale coordinate).cover.parent
          (sourceEquiv target))
      (fun coordinate first second =>
        wz1PaperLineDistance
            ((schedule.parentData coordinate).parentFamily.tube first)
            ((schedule.parentData coordinate).parentFamily.tube second) ≤
          2 * wz2PaperLocalizedDoubledFiberLineDistanceConstant *
            schedule.targetRho coordinate)
      (Finset.univ.sup fun coordinate =>
        (schedule.parentData coordinate).parentConflictDegree))
    (coordinate : Fin scaleCount) :
    let selected := WZ2PaperPureTubeSubfamily.fromFinset
      targetFine selection.selected
    PureWZ2LocalizedAssignedParentCoverData
      selected.family
      (((schedule.parentData coordinate).toPreAssignedParentCover
        |>.hitParentSubfamily selected).family) := by
  dsimp only
  let selected := WZ2PaperPureTubeSubfamily.fromFinset
    targetFine selection.selected
  let pre := (schedule.parentData coordinate).toPreAssignedParentCover
  apply pre.restrictToSeparatedHitParents selected
  intro first second hne
  have hambientNe :
      (pre.hitParentSubfamily selected).embedding first ≠
        (pre.hitParentSubfamily selected).embedding second :=
    (pre.hitParentSubfamily selected).embedding.injective.ne hne
  have hfirst : ∃ target ∈ selection.selected,
      (schedule.sourceScale coordinate).cover.parent
          (sourceEquiv target) =
        (pre.hitParentSubfamily selected).embedding first := by
    rcases pre.hitParent_surjective selected first with ⟨target, htarget⟩
    refine ⟨selected.embedding target, ?_, ?_⟩
    · exact Finset.orderEmbOfFin_mem selection.selected rfl target
    · change pre.assignedParent (selected.embedding target) = _
      rw [← pre.hitParent_ambient selected target, htarget]
  have hsecond : ∃ target ∈ selection.selected,
      (schedule.sourceScale coordinate).cover.parent
          (sourceEquiv target) =
        (pre.hitParentSubfamily selected).embedding second := by
    rcases pre.hitParent_surjective selected second with ⟨target, htarget⟩
    refine ⟨selected.embedding target, ?_, ?_⟩
    · exact Finset.orderEmbOfFin_mem selection.selected rfl target
    · change pre.assignedParent (selected.embedding target) = _
      rw [← pre.hitParent_ambient selected target, htarget]
  have hnotConflict := selection.hit_parent_separated coordinate
    ((pre.hitParentSubfamily selected).embedding first)
    ((pre.hitParentSubfamily selected).embedding second)
    hambientNe hfirst hsecond
  apply lt_of_not_ge
  intro hle
  apply hnotConflict
  simpa only [(pre.hitParentSubfamily selected).tube_eq] using hle

/-- Fine family left after the simultaneous strong-parent selection. -/
noncomputable def separatedFine
    {sourceDelta targetDelta : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {targetFine : Kakeya.Streamlined.TubeFamily targetDelta}
    {sourceEquiv : Fin targetFine.card ≃ Fin sourceFine.card}
    {sourceConstant : ENNReal} {scaleCount : ℕ}
    (schedule : PureWZ2FiniteRepresentativeParentScheduleData
      targetFine sourceEquiv sourceConstant scaleCount)
    (weight : Fin targetFine.card → ENNReal)
    (selection : PureWZ2FiniteStrongParentSelectionData
      weight scaleCount schedule.Parent
      (fun coordinate target =>
        (schedule.sourceScale coordinate).cover.parent
          (sourceEquiv target))
      (fun coordinate first second =>
        wz1PaperLineDistance
            ((schedule.parentData coordinate).parentFamily.tube first)
            ((schedule.parentData coordinate).parentFamily.tube second) ≤
          2 * wz2PaperLocalizedDoubledFiberLineDistanceConstant *
            schedule.targetRho coordinate)
      (Finset.univ.sup fun coordinate =>
        (schedule.parentData coordinate).parentConflictDegree)) :
    WZ2PaperPureTubeSubfamily targetFine :=
  WZ2PaperPureTubeSubfamily.fromFinset targetFine selection.selected

/-- The genuine public covers on the once-selected target family. -/
noncomputable def separatedSchedule
    {sourceDelta targetDelta : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {targetFine : Kakeya.Streamlined.TubeFamily targetDelta}
    {sourceEquiv : Fin targetFine.card ≃ Fin sourceFine.card}
    {sourceConstant : ENNReal} {scaleCount : ℕ}
    (schedule : PureWZ2FiniteRepresentativeParentScheduleData
      targetFine sourceEquiv sourceConstant scaleCount)
    (weight : Fin targetFine.card → ENNReal)
    (selection : PureWZ2FiniteStrongParentSelectionData
      weight scaleCount schedule.Parent
      (fun coordinate target =>
        (schedule.sourceScale coordinate).cover.parent
          (sourceEquiv target))
      (fun coordinate first second =>
        wz1PaperLineDistance
            ((schedule.parentData coordinate).parentFamily.tube first)
            ((schedule.parentData coordinate).parentFamily.tube second) ≤
          2 * wz2PaperLocalizedDoubledFiberLineDistanceConstant *
            schedule.targetRho coordinate)
      (Finset.univ.sup fun coordinate =>
        (schedule.parentData coordinate).parentConflictDegree)) :
    PureWZ2FiniteLocalizedAssignedParentScheduleData
      (schedule.separatedFine weight selection).family scaleCount where
  rho := schedule.targetRho
  coarse coordinate :=
    (((schedule.parentData coordinate).toPreAssignedParentCover
      |>.hitParentSubfamily (schedule.separatedFine weight selection)).family)
  cover coordinate := schedule.selectedCover weight selection coordinate

/-- After the one common strong-parent selection, simultaneously regularize
the genuine public full fibers.  This second pass changes only the fine
subfamily; it does not reconstruct or weaken any cover. -/
theorem simultaneouslyRegularizeSeparated
    {sourceDelta targetDelta : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {targetFine : Kakeya.Streamlined.TubeFamily targetDelta}
    {sourceEquiv : Fin targetFine.card ≃ Fin sourceFine.card}
    {sourceConstant : ENNReal} {scaleCount : ℕ}
    (schedule : PureWZ2FiniteRepresentativeParentScheduleData
      targetFine sourceEquiv sourceConstant scaleCount)
    (weight : Fin targetFine.card → ENNReal)
    (selection : PureWZ2FiniteStrongParentSelectionData
      weight scaleCount schedule.Parent
      (fun coordinate target =>
        (schedule.sourceScale coordinate).cover.parent
          (sourceEquiv target))
      (fun coordinate first second =>
        wz1PaperLineDistance
            ((schedule.parentData coordinate).parentFamily.tube first)
            ((schedule.parentData coordinate).parentFamily.tube second) ≤
          2 * wz2PaperLocalizedDoubledFiberLineDistanceConstant *
            schedule.targetRho coordinate)
      (Finset.univ.sup fun coordinate =>
        (schedule.parentData coordinate).parentConflictDegree))
    (selectedWeight : Fin (schedule.separatedFine weight selection).family.card →
      ENNReal) :
    ∃ selected : Finset
        (Fin (schedule.separatedFine weight selection).family.card),
      let degreeConstant : ENNReal :=
        16 * (scaleCount : ENNReal) *
          (Nat.log 2
            (2 * (schedule.separatedFine weight selection).family.card) + 1 :
              ENNReal) ^ scaleCount
      let retentionConstant : ENNReal :=
        (8 : ENNReal) *
          (Nat.log 2
            (2 * (schedule.separatedFine weight selection).family.card) + 1 :
              ENNReal) ^ (scaleCount + 1)
      (∑ index, selectedWeight index) ≤
          retentionConstant * ∑ index ∈ selected, selectedWeight index ∧
        (∀ index ∈ selected, 0 < selectedWeight index) ∧
        ∀ coordinate,
          let finalFine := WZ2PaperPureTubeSubfamily.fromFinset
            (schedule.separatedFine weight selection).family selected
          WZ2PaperPureFullFibersAreCUniform
            finalFine.family
            (((schedule.separatedSchedule weight selection).cover coordinate)
              |>.toPartitioningCover.hitParentSubfamily finalFine).family
            degreeConstant :=
  (schedule.separatedSchedule weight selection).simultaneouslyRegularize
    selectedWeight

end PureWZ2FiniteRepresentativeParentScheduleData

end Kakeya.Assouad

end
