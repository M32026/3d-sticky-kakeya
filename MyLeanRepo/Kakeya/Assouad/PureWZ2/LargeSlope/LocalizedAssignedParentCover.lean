import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12LocalizedDoubledFiber
import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12PureHitParentRestriction
import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12PureFiberRestriction
import MyLeanRepo.Kakeya.Assouad.PropStickyFiniteRegularizedRefinement

/-!
# Localized public covers from an explicit parent assignment

This module packages the final, model-independent step in the nearby-scale
construction used by Proposition 6.5.  The input is an honest ordinary parent
family together with a surjective assignment of every retained fine tube to a
strictly containing parent.  A quantitative separation of the parent axes
then gives the literal centered-doubled-fiber disjointness required by
Definition 2.12.

The resulting full fibers are proved to be exactly the assigned fibers.  In
particular, later cardinality regularization applies to genuine geometric
fibers rather than to an auxiliary partition.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

/-- Geometric data turning an explicit finite parent assignment into a public
Definition 2.12 partitioning cover. -/
structure PureWZ2LocalizedAssignedParentCoverData
    {delta rho : ℝ}
    (fine : Kakeya.Streamlined.TubeFamily delta)
    (coarse : Kakeya.Streamlined.TubeFamily rho) where
  delta_pos : 0 < delta
  rho_pos : 0 < rho
  fine_line_class : WZ1PaperIsLineClass fine
  coarse_line_class : WZ1PaperIsLineClass coarse
  fine_midpoint_local : ∀ source,
    ‖wz2PaperTubeMidpoint (fine.tube source)‖ ≤ 3
  assignedParent : Fin fine.card → Fin coarse.card
  assignedParent_surjective : Function.Surjective assignedParent
  assigned_containment : ∀ source,
    (fine.tube source).carrier ⊆
      (coarse.tube (assignedParent source)).carrier
  parent_separated : ∀ first second, first ≠ second →
    2 * wz2PaperLocalizedDoubledFiberLineDistanceConstant * rho <
      wz1PaperLineDistance (coarse.tube first) (coarse.tube second)

/-- Geometric parent data before the strong-separation selection.  At this
stage every fine tube has a strictly containing assigned parent, but distinct
parents are not yet required to have disjoint centered doubled fibers. -/
structure PureWZ2LocalizedPreAssignedParentCoverData
    {delta rho : ℝ}
    (fine : Kakeya.Streamlined.TubeFamily delta)
    (coarse : Kakeya.Streamlined.TubeFamily rho) where
  delta_pos : 0 < delta
  rho_pos : 0 < rho
  fine_line_class : WZ1PaperIsLineClass fine
  coarse_line_class : WZ1PaperIsLineClass coarse
  fine_midpoint_local : ∀ source,
    ‖wz2PaperTubeMidpoint (fine.tube source)‖ ≤ 3
  assignedParent : Fin fine.card → Fin coarse.card
  assigned_containment : ∀ source,
    (fine.tube source).carrier ⊆
      (coarse.tube (assignedParent source)).carrier

namespace PureWZ2LocalizedPreAssignedParentCoverData

/-- Ambient parent indices hit by a selected fine subfamily. -/
def hitParentIndices
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (data : PureWZ2LocalizedPreAssignedParentCoverData fine coarse)
    (selected : WZ2PaperPureTubeSubfamily fine) :
    Finset (Fin coarse.card) :=
  Finset.univ.image fun source =>
    data.assignedParent (selected.embedding source)

/-- The preliminary coarse subfamily consisting exactly of parents hit by
the selected fine support. -/
noncomputable def hitParentSubfamily
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (data : PureWZ2LocalizedPreAssignedParentCoverData fine coarse)
    (selected : WZ2PaperPureTubeSubfamily fine) :
    WZ2PaperPureTubeSubfamily coarse :=
  WZ2PaperPureTubeSubfamily.fromFinset coarse
    (data.hitParentIndices selected)

/-- The hit-parent index of one selected fine tube. -/
noncomputable def hitParent
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (data : PureWZ2LocalizedPreAssignedParentCoverData fine coarse)
    (selected : WZ2PaperPureTubeSubfamily fine) :
    Fin selected.family.card →
      Fin (data.hitParentSubfamily selected).family.card := fun source =>
  let parents := data.hitParentIndices selected
  let equivalence : Fin parents.card ≃ parents :=
    (parents.orderIsoOfFin rfl).toEquiv
  equivalence.symm
    ⟨data.assignedParent (selected.embedding source), by
      exact Finset.mem_image.mpr
        ⟨source, Finset.mem_univ source, rfl⟩⟩

@[simp] theorem hitParent_ambient
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (data : PureWZ2LocalizedPreAssignedParentCoverData fine coarse)
    (selected : WZ2PaperPureTubeSubfamily fine)
    (source : Fin selected.family.card) :
    (data.hitParentSubfamily selected).embedding
        (data.hitParent selected source) =
      data.assignedParent (selected.embedding source) := by
  let parents := data.hitParentIndices selected
  let equivalence : Fin parents.card ≃ parents :=
    (parents.orderIsoOfFin rfl).toEquiv
  change
    (parents.orderEmbOfFin rfl)
        (equivalence.symm
          ⟨data.assignedParent (selected.embedding source), _⟩) =
      data.assignedParent (selected.embedding source)
  exact congrArg Subtype.val
    (equivalence.apply_symm_apply
      ⟨data.assignedParent (selected.embedding source), by
        exact Finset.mem_image.mpr
          ⟨source, Finset.mem_univ source, rfl⟩⟩)

theorem hitParent_surjective
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (data : PureWZ2LocalizedPreAssignedParentCoverData fine coarse)
    (selected : WZ2PaperPureTubeSubfamily fine) :
    Function.Surjective (data.hitParent selected) := by
  intro parent
  have hparent :
      (data.hitParentSubfamily selected).embedding parent ∈
        data.hitParentIndices selected :=
    Finset.orderEmbOfFin_mem
      (data.hitParentIndices selected) rfl parent
  rcases Finset.mem_image.mp hparent with
    ⟨source, _hsource, hsourceParent⟩
  refine ⟨source, ?_⟩
  apply (data.hitParentSubfamily selected).embedding.injective
  rw [data.hitParent_ambient]
  exact hsourceParent

/-- Once the hit preliminary parents are strongly separated, the selected
fine support has an honest localized public assigned-parent cover. -/
noncomputable def restrictToSeparatedHitParents
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (data : PureWZ2LocalizedPreAssignedParentCoverData fine coarse)
    (selected : WZ2PaperPureTubeSubfamily fine)
    (hseparated : ∀ first second :
        Fin (data.hitParentSubfamily selected).family.card,
      first ≠ second →
        2 * wz2PaperLocalizedDoubledFiberLineDistanceConstant * rho <
          wz1PaperLineDistance
            ((data.hitParentSubfamily selected).family.tube first)
            ((data.hitParentSubfamily selected).family.tube second)) :
    PureWZ2LocalizedAssignedParentCoverData
      selected.family (data.hitParentSubfamily selected).family where
  delta_pos := data.delta_pos
  rho_pos := data.rho_pos
  fine_line_class := data.fine_line_class.subfamily selected.toTubeSubfamily
  coarse_line_class :=
    data.coarse_line_class.subfamily
      (data.hitParentSubfamily selected).toTubeSubfamily
  fine_midpoint_local source := by
    rw [selected.tube_eq]
    exact data.fine_midpoint_local (selected.embedding source)
  assignedParent := data.hitParent selected
  assignedParent_surjective := data.hitParent_surjective selected
  assigned_containment source := by
    rw [selected.tube_eq,
      (data.hitParentSubfamily selected).tube_eq,
      data.hitParent_ambient]
    exact data.assigned_containment (selected.embedding source)
  parent_separated := hseparated

end PureWZ2LocalizedPreAssignedParentCoverData

/-- A finite schedule of preliminary localized parent assignments on one
fixed fine family. -/
structure PureWZ2FiniteLocalizedPreAssignedParentScheduleData
    {delta : ℝ}
    (fine : Kakeya.Streamlined.TubeFamily delta)
    (scaleCount : ℕ) where
  rho : Fin scaleCount → ℝ
  coarse : ∀ coordinate, Kakeya.Streamlined.TubeFamily (rho coordinate)
  cover : ∀ coordinate,
    PureWZ2LocalizedPreAssignedParentCoverData
      fine (coarse coordinate)

namespace PureWZ2FiniteLocalizedPreAssignedParentScheduleData

abbrev Parent
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {scaleCount : ℕ}
    (schedule : PureWZ2FiniteLocalizedPreAssignedParentScheduleData
      fine scaleCount)
    (coordinate : Fin scaleCount) : Type :=
  Fin (schedule.coarse coordinate).card

end PureWZ2FiniteLocalizedPreAssignedParentScheduleData

namespace PureWZ2LocalizedAssignedParentCoverData

/-- The explicit assignment gives a genuine public partitioning cover. -/
noncomputable def toPartitioningCover
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (data : PureWZ2LocalizedAssignedParentCoverData fine coarse) :
    WZ2PaperPurePartitioningCover fine coarse where
  covers source := by
    refine ⟨data.assignedParent source, ?_⟩
    rw [mem_wz2PaperOrdinaryFullFiberIndices_iff]
    exact data.assigned_containment source
  doubled_fibers_disjoint :=
    wz2_paper_localized_ordinary_dilatedFiberIndices_disjoint
      data.delta_pos data.rho_pos data.fine_line_class
      data.coarse_line_class data.fine_midpoint_local data.parent_separated

/-- The parent derived from the public cover is exactly the supplied
assignment. -/
theorem parent_eq_assigned
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (data : PureWZ2LocalizedAssignedParentCoverData fine coarse)
    (source : Fin fine.card) :
    data.toPartitioningCover.parent source = data.assignedParent source := by
  apply data.toPartitioningCover.fullFiber_parent_unique data.rho_pos.le
  · exact data.toPartitioningCover.parent_mem_fullFiber source
  · rw [mem_wz2PaperOrdinaryFullFiberIndices_iff]
    exact data.assigned_containment source

/-- A strict geometric full fiber is exactly one fiber of the explicit
assignment. -/
theorem fullFiberIndices_eq_assigned
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (data : PureWZ2LocalizedAssignedParentCoverData fine coarse)
    (parent : Fin coarse.card) :
    wz2PaperOrdinaryFullFiberIndices fine coarse parent =
      (Finset.univ : Finset (Fin fine.card)).filter
        (fun source => data.assignedParent source = parent) := by
  ext source
  rw [data.toPartitioningCover.mem_fullFiber_iff_parent_eq data.rho_pos.le]
  rw [data.parent_eq_assigned]
  simp

/-- Surjectivity of the assignment makes every strict geometric fiber
nonempty. -/
theorem fullFiber_nonempty
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (data : PureWZ2LocalizedAssignedParentCoverData fine coarse)
    (parent : Fin coarse.card) :
    (wz2PaperOrdinaryFullFiberIndices fine coarse parent).Nonempty := by
  rcases data.assignedParent_surjective parent with ⟨source, hsource⟩
  rw [data.fullFiberIndices_eq_assigned]
  exact ⟨source, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsource⟩⟩

/-- Uniform assigned degrees are precisely uniform public strict-fiber
cardinalities. -/
theorem fullFibers_uniform
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (data : PureWZ2LocalizedAssignedParentCoverData fine coarse)
    (C : ENNReal)
    (degreeUniform : ∀ first second : Fin coarse.card,
      (((Finset.univ : Finset (Fin fine.card)).filter
          (fun source => data.assignedParent source = first)).card : ENNReal) ≤
        C *
          (((Finset.univ : Finset (Fin fine.card)).filter
            (fun source => data.assignedParent source = second)).card :
              ENNReal)) :
    WZ2PaperPureFullFibersAreCUniform fine coarse C := by
  intro first second
  unfold wz2PaperOrdinaryFullFiberCount
  rw [data.fullFiberIndices_eq_assigned,
    data.fullFiberIndices_eq_assigned]
  exact degreeUniform first second

/-- Restrict an assigned-parent package to a fine subfamily while retaining
exactly the parents hit by that subfamily.  This is the operation used after
simultaneous degree regularization: separation survives because the coarse
family only shrinks, and the new assignment remains surjective by
construction. -/
noncomputable def restrictToHitParents
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (data : PureWZ2LocalizedAssignedParentCoverData fine coarse)
    (selected : WZ2PaperPureTubeSubfamily fine) :
    PureWZ2LocalizedAssignedParentCoverData
      selected.family
      (data.toPartitioningCover.hitParentSubfamily selected).family where
  delta_pos := data.delta_pos
  rho_pos := data.rho_pos
  fine_line_class := data.fine_line_class.subfamily selected.toTubeSubfamily
  coarse_line_class :=
    data.coarse_line_class.subfamily
      (data.toPartitioningCover.hitParentSubfamily selected).toTubeSubfamily
  fine_midpoint_local source := by
    rw [selected.tube_eq]
    exact data.fine_midpoint_local (selected.embedding source)
  assignedParent := data.toPartitioningCover.hitParent selected
  assignedParent_surjective :=
    data.toPartitioningCover.hitParent_surjective selected
  assigned_containment source := by
    have hparent :
        (data.toPartitioningCover.hitParentSubfamily selected).family.tube
            (data.toPartitioningCover.hitParent selected source) =
          coarse.tube (data.assignedParent (selected.embedding source)) := by
      rw [(data.toPartitioningCover.hitParentSubfamily selected).tube_eq,
        data.toPartitioningCover.hitParent_ambient,
        data.parent_eq_assigned]
    rw [selected.tube_eq, hparent]
    exact data.assigned_containment (selected.embedding source)
  parent_separated first second hne := by
    have hambientNe :
        (data.toPartitioningCover.hitParentSubfamily selected).embedding first ≠
          (data.toPartitioningCover.hitParentSubfamily selected).embedding second :=
      (data.toPartitioningCover.hitParentSubfamily selected).embedding.injective.ne hne
    simpa only [
      (data.toPartitioningCover.hitParentSubfamily selected).tube_eq
    ] using data.parent_separated
      ((data.toPartitioningCover.hitParentSubfamily selected).embedding first)
      ((data.toPartitioningCover.hitParentSubfamily selected).embedding second)
      hambientNe

/-- After restriction to hit parents, the new public strict fiber is exactly
the selected part of the old assigned fiber. -/
theorem restrictToHitParents_fullFiberIndices_eq
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (data : PureWZ2LocalizedAssignedParentCoverData fine coarse)
    (selected : WZ2PaperPureTubeSubfamily fine)
    (parent :
      Fin (data.toPartitioningCover.hitParentSubfamily selected).family.card) :
    wz2PaperOrdinaryFullFiberIndices
        selected.family
        (data.toPartitioningCover.hitParentSubfamily selected).family parent =
      (Finset.univ : Finset (Fin selected.family.card)).filter
        (fun source =>
          data.assignedParent (selected.embedding source) =
            (data.toPartitioningCover.hitParentSubfamily selected).embedding
              parent) := by
  rw [(data.restrictToHitParents selected).fullFiberIndices_eq_assigned]
  ext source
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  change data.toPartitioningCover.hitParent selected source = parent ↔ _
  constructor
  · intro hparent
    calc
      data.assignedParent (selected.embedding source) =
          data.toPartitioningCover.parent
            (selected.embedding source) :=
        (data.parent_eq_assigned (selected.embedding source)).symm
      _ = (data.toPartitioningCover.hitParentSubfamily selected).embedding
            (data.toPartitioningCover.hitParent selected source) :=
        (data.toPartitioningCover.hitParent_ambient selected source).symm
      _ = (data.toPartitioningCover.hitParentSubfamily selected).embedding
            parent := congrArg _ hparent
  · intro hparent
    apply (data.toPartitioningCover.hitParentSubfamily selected).embedding.injective
    rw [data.toPartitioningCover.hitParent_ambient]
    rw [data.parent_eq_assigned]
    exact hparent

/-- The parent family is publicly essentially distinct as a consequence of
the literal partitioning cover and nonempty full fibers. -/
theorem coarse_essentiallyDistinct
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (data : PureWZ2LocalizedAssignedParentCoverData fine coarse) :
    WZ2PaperOrdinaryIsEssentiallyDistinct coarse :=
  data.toPartitioningCover.coarse_essentiallyDistinct_of_fullFiber_nonempty
    data.rho_pos.le data.fullFiber_nonempty

end PureWZ2LocalizedAssignedParentCoverData

/-- A finite schedule of genuine localized assigned-parent covers on one fixed
fine family.  Keeping the fine family fixed is what makes simultaneous
regularization meaningful. -/
structure PureWZ2FiniteLocalizedAssignedParentScheduleData
    {delta : ℝ}
    (fine : Kakeya.Streamlined.TubeFamily delta)
    (scaleCount : ℕ) where
  rho : Fin scaleCount → ℝ
  coarse : ∀ coordinate, Kakeya.Streamlined.TubeFamily (rho coordinate)
  cover : ∀ coordinate,
    PureWZ2LocalizedAssignedParentCoverData
      fine (coarse coordinate)

namespace PureWZ2FiniteLocalizedAssignedParentScheduleData

/-- The dependent parent types in the finite schedule. -/
abbrev Parent
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {scaleCount : ℕ}
    (schedule : PureWZ2FiniteLocalizedAssignedParentScheduleData
      fine scaleCount)
    (coordinate : Fin scaleCount) : Type :=
  Fin (schedule.coarse coordinate).card

/-- The parent map at one coordinate of the schedule. -/
def assignedParent
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {scaleCount : ℕ}
    (schedule : PureWZ2FiniteLocalizedAssignedParentScheduleData
      fine scaleCount) :
    ∀ coordinate, Fin fine.card → schedule.Parent coordinate :=
  fun coordinate => (schedule.cover coordinate).assignedParent

/-- Simultaneously regularize the actual assigned parent maps of a localized
target schedule.  No new cover is chosen here. -/
theorem simultaneouslyRegularize
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {scaleCount : ℕ}
    (schedule : PureWZ2FiniteLocalizedAssignedParentScheduleData
      fine scaleCount)
    (weight : Fin fine.card → ENNReal) :
    ∃ selected : Finset (Fin fine.card),
      let degreeConstant : ENNReal :=
        16 * (scaleCount : ENNReal) *
          (Nat.log 2 (2 * fine.card) + 1 : ENNReal) ^ scaleCount
      let retentionConstant : ENNReal :=
        (8 : ENNReal) *
          (Nat.log 2 (2 * fine.card) + 1 : ENNReal) ^
            (scaleCount + 1)
      (∑ index : Fin fine.card, weight index) ≤
          retentionConstant * ∑ index ∈ selected, weight index ∧
        (∀ index ∈ selected, 0 < weight index) ∧
        ∀ coordinate,
          let selectedFine :=
            WZ2PaperPureTubeSubfamily.fromFinset fine selected
          WZ2PaperPureFullFibersAreCUniform
            selectedFine.family
            ((schedule.cover coordinate).toPartitioningCover
              |>.hitParentSubfamily selectedFine).family
            degreeConstant := by
  let Parent : Fin scaleCount → Type := schedule.Parent
  let parent : ∀ coordinate, Fin fine.card → Parent coordinate :=
    fun coordinate => (schedule.cover coordinate).toPartitioningCover.parent
  rcases simultaneous_degree_regularization_with_support_and_weight_band
      scaleCount Parent parent weight with
    ⟨selected, hdegree, hretained, hpositive, _hfloor, _hband⟩
  refine ⟨selected, ?_, hpositive, ?_⟩
  · simpa [Fintype.card_fin] using hretained
  · intro coordinate
    let selectedFine : WZ2PaperPureTubeSubfamily fine :=
      WZ2PaperPureTubeSubfamily.fromFinset fine selected
    apply (schedule.cover coordinate).toPartitioningCover
      |>.restrictToHitParents_fullFiber_uniform_of_subfamily
        (schedule.cover coordinate).rho_pos.le selectedFine _
    intro first second hfirst hsecond
    have hraw := hdegree coordinate first second
    have hfirstEq := fromFinset_filter_card selected
      (parent coordinate) first
    have hsecondEq := fromFinset_filter_card selected
      (parent coordinate) second
    have hfirst' : 0 <
        (selected.filter fun index =>
          parent coordinate index = first).card := by
      rw [← hfirstEq]
      change 0 <
        ((Finset.univ : Finset (Fin selected.card)).filter
          (fun source =>
            (schedule.cover coordinate).toPartitioningCover.parent
              (selected.orderEmbOfFin rfl source) = first)).card at hfirst
      exact hfirst
    have hsecond' : 0 <
        (selected.filter fun index =>
          parent coordinate index = second).card := by
      rw [← hsecondEq]
      change 0 <
        ((Finset.univ : Finset (Fin selected.card)).filter
          (fun source =>
            (schedule.cover coordinate).toPartitioningCover.parent
              (selected.orderEmbOfFin rfl source) = second)).card at hsecond
      exact hsecond
    have hbound := hraw hfirst' hsecond'
    rw [← hfirstEq, ← hsecondEq] at hbound
    change
      (((Finset.univ : Finset (Fin selected.card)).filter
          (fun source =>
            (schedule.cover coordinate).toPartitioningCover.parent
              (selected.orderEmbOfFin rfl source) = first)).card : ENNReal) ≤
        (16 * (scaleCount : ENNReal) *
          (Nat.log 2 (2 * fine.card) + 1 : ENNReal) ^ scaleCount) *
          (((Finset.univ : Finset (Fin selected.card)).filter
            (fun source =>
              (schedule.cover coordinate).toPartitioningCover.parent
                (selected.orderEmbOfFin rfl source) = second)).card : ENNReal)
    simpa [parent, Fintype.card_fin] using hbound

end PureWZ2FiniteLocalizedAssignedParentScheduleData

end Kakeya.Assouad

end
