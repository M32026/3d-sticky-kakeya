import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.AnisotropicParentQuotient
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.AnisotropicRepresentativeParentSchedule
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.PureFiniteStrongParentSelection

/-!
# Finite quotient-parent schedule for Proposition 6.5

Each source nearby-scale witness first produces a maximal quotient net of the
exact triangular target representative axes.  A single weighted selection is
then performed across the finite schedule.  Its conflict degree is the same
absolute constant at every coordinate; in particular, the selection does not
pay a power of the target/source scale ratio.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

/-- A finite schedule of one-scale target quotient parents. -/
structure PureWZ2FiniteAnisotropicParentQuotientScheduleData
    {sourceDelta targetDelta : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {targetFine : Kakeya.Streamlined.TubeFamily targetDelta}
    {sourceEquiv : Fin targetFine.card ≃ Fin sourceFine.card}
    {sourceConstant : ENNReal} {scaleCount : ℕ}
    (representativeSchedule : PureWZ2FiniteRepresentativeParentScheduleData
      targetFine sourceEquiv sourceConstant scaleCount) where
  callerRho : Fin scaleCount → ℝ
  quotient : ∀ coordinate,
    PureWZ2AnisotropicParentQuotientData
      (callerRho := callerRho coordinate)
      (representativeSchedule.parentData coordinate)

/-- Public quotient-parent radius used at every coordinate.  The first term
pays for the exact-triangular image of a complete source fiber, while the
second pays for the target fine radius. -/
def anisotropicQuotientCallerScale
    (targetDelta sourceRho : ℝ) : ℝ :=
  6000000 * sourceRho + 2 * targetDelta

theorem anisotropicQuotientCallerScale_pos
    {targetDelta sourceRho : ℝ}
    (htargetDelta : 0 < targetDelta) (hsourceRho : 0 < sourceRho) :
    0 < anisotropicQuotientCallerScale targetDelta sourceRho := by
  unfold anisotropicQuotientCallerScale
  positivity

theorem anisotropicQuotientCallerScale_containment
    {targetDelta sourceRho : ℝ}
    (htargetDelta : 0 < targetDelta) (hsourceRho : 0 < sourceRho) :
    (3 / 2 : ℝ) *
          (anisotropicRepresentativeLineBound sourceRho +
            anisotropicQuotientCallerScale targetDelta sourceRho / 4) +
        targetDelta ≤
      anisotropicQuotientCallerScale targetDelta sourceRho := by
  unfold anisotropicRepresentativeLineBound
    anisotropicQuotientCallerScale
  nlinarith

/-- Build all quotient nets on a finite exact-triangular representative
schedule using the same explicit caller-radius formula. -/
noncomputable def anisotropicParentQuotientSchedule
    {sourceDelta targetDelta : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {targetFine : Kakeya.Streamlined.TubeFamily targetDelta}
    {sourceEquiv : Fin targetFine.card ≃ Fin sourceFine.card}
    {sourceConstant : ENNReal} {scaleCount : ℕ}
    (representativeSchedule :
      PureWZ2FiniteRepresentativeParentScheduleData
        targetFine sourceEquiv sourceConstant scaleCount)
    (hlineBound : ∀ coordinate,
      representativeSchedule.lineBound coordinate =
        anisotropicRepresentativeLineBound
          (representativeSchedule.sourceRho coordinate)) :
    PureWZ2FiniteAnisotropicParentQuotientScheduleData
      representativeSchedule where
  callerRho coordinate :=
    anisotropicQuotientCallerScale targetDelta
      (representativeSchedule.sourceRho coordinate)
  quotient coordinate := Classical.choice <|
    pureWZ2_anisotropic_parent_quotient
      (representativeSchedule.parentData coordinate)
      (anisotropicQuotientCallerScale_pos
        (representativeSchedule.parentData coordinate).target_delta_pos
        (representativeSchedule.sourceScale coordinate).rho_pos)
      (by
        rw [hlineBound coordinate]
        exact anisotropicQuotientCallerScale_containment
          (representativeSchedule.parentData coordinate).target_delta_pos
          (representativeSchedule.sourceScale coordinate).rho_pos)

namespace PureWZ2FiniteAnisotropicParentQuotientScheduleData

universe u v w

abbrev Parent
    {sourceDelta targetDelta : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {targetFine : Kakeya.Streamlined.TubeFamily targetDelta}
    {sourceEquiv : Fin targetFine.card ≃ Fin sourceFine.card}
    {sourceConstant : ENNReal} {scaleCount : ℕ}
    {representativeSchedule :
      PureWZ2FiniteRepresentativeParentScheduleData
        targetFine sourceEquiv sourceConstant scaleCount}
    (schedule : PureWZ2FiniteAnisotropicParentQuotientScheduleData
      representativeSchedule)
    (coordinate : Fin scaleCount) : Type :=
  Fin (schedule.quotient coordinate).parentFamily.card

/-- The center conflict relation used for the simultaneous selection. -/
def conflict
    {sourceDelta targetDelta : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {targetFine : Kakeya.Streamlined.TubeFamily targetDelta}
    {sourceEquiv : Fin targetFine.card ≃ Fin sourceFine.card}
    {sourceConstant : ENNReal} {scaleCount : ℕ}
    {representativeSchedule :
      PureWZ2FiniteRepresentativeParentScheduleData
        targetFine sourceEquiv sourceConstant scaleCount}
    (schedule : PureWZ2FiniteAnisotropicParentQuotientScheduleData
      representativeSchedule)
    (coordinate : Fin scaleCount)
    (first second : schedule.Parent coordinate) : Prop :=
  wz1PaperLineDistance
      ((schedule.quotient coordinate).parentFamily.tube second)
      ((schedule.quotient coordinate).parentFamily.tube first) ≤
    2 * wz2PaperLocalizedDoubledFiberLineDistanceConstant *
      schedule.callerRho coordinate

/-- Select complete quotient-center fibers simultaneously across all scheduled
scales.  The loss base is an absolute constant. -/
theorem simultaneouslySeparate
    {sourceDelta targetDelta : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {targetFine : Kakeya.Streamlined.TubeFamily targetDelta}
    {sourceEquiv : Fin targetFine.card ≃ Fin sourceFine.card}
    {sourceConstant : ENNReal} {scaleCount : ℕ}
    {representativeSchedule :
      PureWZ2FiniteRepresentativeParentScheduleData
        targetFine sourceEquiv sourceConstant scaleCount}
    (schedule : PureWZ2FiniteAnisotropicParentQuotientScheduleData
      representativeSchedule)
    (weight : Fin targetFine.card → ENNReal) :
    Nonempty (PureWZ2FiniteStrongParentSelectionData
      weight scaleCount schedule.Parent
      (fun coordinate target =>
        (schedule.quotient coordinate).assignedParent target)
      schedule.conflict pureWZ2AnisotropicQuotientCenterConflictDegree) := by
  apply pureWZ2_finite_strong_parent_selection
  · intro coordinate parent
    unfold conflict
    have hzero :
        wz1PaperLineDistance
            ((schedule.quotient coordinate).parentFamily.tube parent)
            ((schedule.quotient coordinate).parentFamily.tube parent) = 0 := by
      have hdirection :
          wz1PaperDirection
              ((schedule.quotient coordinate).parentFamily.tube parent) ≠ 0 := by
        intro hzero
        have hnorm := wz1PaperDirection_norm
          ((schedule.quotient coordinate).parentFamily.tube parent)
        rw [hzero, norm_zero] at hnorm
        norm_num at hnorm
      simp [wz1PaperLineDistance,
        InnerProductGeometry.angle_self hdirection]
    rw [hzero]
    have hrho := (schedule.quotient coordinate).caller_rho_pos
    unfold wz2PaperLocalizedDoubledFiberLineDistanceConstant
    nlinarith
  · intro coordinate first second hconflict
    unfold conflict at *
    rw [wz1PaperLineDistance_symm]
    exact hconflict
  · intro coordinate parent
    exact (schedule.quotient coordinate).centerConflict_degree parent

/-- The target fine subfamily retained by the one common center selection. -/
noncomputable def separatedFine
    {sourceDelta targetDelta : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {targetFine : Kakeya.Streamlined.TubeFamily targetDelta}
    {sourceEquiv : Fin targetFine.card ≃ Fin sourceFine.card}
    {sourceConstant : ENNReal} {scaleCount : ℕ}
    {representativeSchedule :
      PureWZ2FiniteRepresentativeParentScheduleData
        targetFine sourceEquiv sourceConstant scaleCount}
    (schedule : PureWZ2FiniteAnisotropicParentQuotientScheduleData
      representativeSchedule)
    (weight : Fin targetFine.card → ENNReal)
    (selection : PureWZ2FiniteStrongParentSelectionData
      weight scaleCount schedule.Parent
      (fun coordinate target =>
        (schedule.quotient coordinate).assignedParent target)
      schedule.conflict pureWZ2AnisotropicQuotientCenterConflictDegree) :
    WZ2PaperPureTubeSubfamily targetFine :=
  WZ2PaperPureTubeSubfamily.fromFinset targetFine selection.selected

/-- At each coordinate the hit selected centers are strongly separated, so
the quotient assignment becomes a genuine public Definition 2.12 cover. -/
noncomputable def selectedCover
    {sourceDelta targetDelta : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {targetFine : Kakeya.Streamlined.TubeFamily targetDelta}
    {sourceEquiv : Fin targetFine.card ≃ Fin sourceFine.card}
    {sourceConstant : ENNReal} {scaleCount : ℕ}
    {representativeSchedule :
      PureWZ2FiniteRepresentativeParentScheduleData
        targetFine sourceEquiv sourceConstant scaleCount}
    (schedule : PureWZ2FiniteAnisotropicParentQuotientScheduleData
      representativeSchedule)
    (weight : Fin targetFine.card → ENNReal)
    (selection : PureWZ2FiniteStrongParentSelectionData
      weight scaleCount schedule.Parent
      (fun coordinate target =>
        (schedule.quotient coordinate).assignedParent target)
      schedule.conflict pureWZ2AnisotropicQuotientCenterConflictDegree)
    (coordinate : Fin scaleCount) :
    let selected := schedule.separatedFine weight selection
    PureWZ2LocalizedAssignedParentCoverData
      selected.family
      ((((schedule.quotient coordinate).toPreAssignedParentCover
        |>.hitParentSubfamily selected).family)) := by
  dsimp only
  let selected := schedule.separatedFine weight selection
  let pre := (schedule.quotient coordinate).toPreAssignedParentCover
  apply pre.restrictToSeparatedHitParents selected
  intro first second hne
  have hambientNe :
      (pre.hitParentSubfamily selected).embedding first ≠
        (pre.hitParentSubfamily selected).embedding second :=
    (pre.hitParentSubfamily selected).embedding.injective.ne hne
  have hfirst : ∃ target ∈ selection.selected,
      pre.assignedParent target =
        (pre.hitParentSubfamily selected).embedding first := by
    rcases pre.hitParent_surjective selected first with ⟨target, htarget⟩
    refine ⟨selected.embedding target, ?_, ?_⟩
    · exact Finset.orderEmbOfFin_mem selection.selected rfl target
    · rw [← pre.hitParent_ambient selected target, htarget]
  have hsecond : ∃ target ∈ selection.selected,
      pre.assignedParent target =
        (pre.hitParentSubfamily selected).embedding second := by
    rcases pre.hitParent_surjective selected second with ⟨target, htarget⟩
    refine ⟨selected.embedding target, ?_, ?_⟩
    · exact Finset.orderEmbOfFin_mem selection.selected rfl target
    · rw [← pre.hitParent_ambient selected target, htarget]
  have hnotConflict := selection.hit_parent_separated coordinate
    ((pre.hitParentSubfamily selected).embedding first)
    ((pre.hitParentSubfamily selected).embedding second)
    hambientNe hfirst hsecond
  apply lt_of_not_ge
  intro hclose
  apply hnotConflict
  unfold conflict
  rw [wz1PaperLineDistance_symm]
  simpa only [(pre.hitParentSubfamily selected).tube_eq] using hclose

/-- The genuine public quotient covers on the once-selected target family. -/
noncomputable def separatedSchedule
    {sourceDelta targetDelta : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {targetFine : Kakeya.Streamlined.TubeFamily targetDelta}
    {sourceEquiv : Fin targetFine.card ≃ Fin sourceFine.card}
    {sourceConstant : ENNReal} {scaleCount : ℕ}
    {representativeSchedule :
      PureWZ2FiniteRepresentativeParentScheduleData
        targetFine sourceEquiv sourceConstant scaleCount}
    (schedule : PureWZ2FiniteAnisotropicParentQuotientScheduleData
      representativeSchedule)
    (weight : Fin targetFine.card → ENNReal)
    (selection : PureWZ2FiniteStrongParentSelectionData
      weight scaleCount schedule.Parent
      (fun coordinate target =>
        (schedule.quotient coordinate).assignedParent target)
      schedule.conflict pureWZ2AnisotropicQuotientCenterConflictDegree) :
    PureWZ2FiniteLocalizedAssignedParentScheduleData
      (schedule.separatedFine weight selection).family scaleCount where
  rho := schedule.callerRho
  coarse coordinate :=
    ((((schedule.quotient coordinate).toPreAssignedParentCover
      |>.hitParentSubfamily
        (schedule.separatedFine weight selection)).family))
  cover coordinate := schedule.selectedCover weight selection coordinate

/-- Regularize the genuine selected quotient fibers after the common center
selection.  This changes only the target fine subfamily and preserves all
public covers by hit-parent restriction. -/
theorem simultaneouslyRegularizeSeparated
    {sourceDelta targetDelta : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {targetFine : Kakeya.Streamlined.TubeFamily targetDelta}
    {sourceEquiv : Fin targetFine.card ≃ Fin sourceFine.card}
    {sourceConstant : ENNReal} {scaleCount : ℕ}
    {representativeSchedule :
      PureWZ2FiniteRepresentativeParentScheduleData
        targetFine sourceEquiv sourceConstant scaleCount}
    (schedule : PureWZ2FiniteAnisotropicParentQuotientScheduleData
      representativeSchedule)
    (weight : Fin targetFine.card → ENNReal)
    (selection : PureWZ2FiniteStrongParentSelectionData
      weight scaleCount schedule.Parent
      (fun coordinate target =>
        (schedule.quotient coordinate).assignedParent target)
      schedule.conflict pureWZ2AnisotropicQuotientCenterConflictDegree)
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
            (((schedule.separatedSchedule weight selection).cover coordinate
              |>.toPartitioningCover.hitParentSubfamily finalFine).family)
            degreeConstant :=
  (schedule.separatedSchedule weight selection).simultaneouslyRegularize
    selectedWeight

/-- The public strict fiber before the final degree regularization is exactly
the corresponding quotient-center packet. -/
theorem selectedCover_fullFiber_eq_ambient_packet
    {sourceDelta targetDelta : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {targetFine : Kakeya.Streamlined.TubeFamily targetDelta}
    {sourceEquiv : Fin targetFine.card ≃ Fin sourceFine.card}
    {sourceConstant : ENNReal} {scaleCount : ℕ}
    {representativeSchedule :
      PureWZ2FiniteRepresentativeParentScheduleData
        targetFine sourceEquiv sourceConstant scaleCount}
    (schedule : PureWZ2FiniteAnisotropicParentQuotientScheduleData
      representativeSchedule)
    (weight : Fin targetFine.card → ENNReal)
    (selection : PureWZ2FiniteStrongParentSelectionData
      weight scaleCount schedule.Parent
      (fun coordinate target =>
        (schedule.quotient coordinate).assignedParent target)
      schedule.conflict pureWZ2AnisotropicQuotientCenterConflictDegree)
    (coordinate : Fin scaleCount)
    (parent : Fin
      (((schedule.quotient coordinate).toPreAssignedParentCover
        |>.hitParentSubfamily
          (schedule.separatedFine weight selection)).family).card) :
    Finset.image
        (schedule.separatedFine weight selection).embedding
        (wz2PaperOrdinaryFullFiberIndices
          (schedule.separatedFine weight selection).family
          (((schedule.quotient coordinate).toPreAssignedParentCover
            |>.hitParentSubfamily
              (schedule.separatedFine weight selection)).family) parent) =
      (selection.selected.filter fun target =>
        (schedule.quotient coordinate).assignedParent target =
          ((schedule.quotient coordinate).toPreAssignedParentCover
            |>.hitParentSubfamily
              (schedule.separatedFine weight selection)).embedding parent) := by
  let selected := schedule.separatedFine weight selection
  let pre := (schedule.quotient coordinate).toPreAssignedParentCover
  let cover := schedule.selectedCover weight selection coordinate
  change Finset.image selected.embedding
      (wz2PaperOrdinaryFullFiberIndices selected.family
        (pre.hitParentSubfamily selected).family parent) = _
  have hfiber := cover.fullFiberIndices_eq_assigned parent
  rw [hfiber]
  ext target
  constructor
  · intro htarget
    rcases Finset.mem_image.mp htarget with ⟨source, hsource, rfl⟩
    have hcoverParent : cover.assignedParent source = parent :=
      (Finset.mem_filter.mp hsource).2
    have hlocal : pre.hitParent selected source = parent := by
      change pre.hitParent selected source = parent at hcoverParent
      exact hcoverParent
    have hambient := congrArg
      (pre.hitParentSubfamily selected).embedding hlocal
    rw [pre.hitParent_ambient selected source] at hambient
    exact Finset.mem_filter.mpr
      ⟨Finset.orderEmbOfFin_mem selection.selected rfl source,
        hambient⟩
  · intro htarget
    have hselected := (Finset.mem_filter.mp htarget).1
    let source : Fin selected.family.card :=
      (selection.selected.orderIsoOfFin rfl).symm
        ⟨target, hselected⟩
    have hembedding : selected.embedding source = target :=
      congrArg Subtype.val
        (selection.selected.orderIsoOfFin rfl |>.apply_symm_apply
          ⟨target, hselected⟩)
    refine Finset.mem_image.mpr ⟨source, ?_, hembedding⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ source, by
        have hcoverAssigned : cover.assignedParent source = parent := by
          change pre.hitParent selected source = parent
          apply (pre.hitParentSubfamily selected).embedding.injective
          rw [pre.hitParent_ambient selected source]
          rw [hembedding]
          exact (Finset.mem_filter.mp htarget).2
        change cover.assignedParent source = parent
        exact hcoverAssigned⟩

/-! ## Joint quotient/source-parent regularization

The center selection above is complete at every quotient parent, but later
coordinates of the same simultaneous selection may cut a source actual
fiber.  For the actual-John argument we therefore make one further global
selection with two coordinates for every scale: the public quotient parent
and the original source actual parent.  This is one finite pigeonhole pass,
not a scale-by-scale deletion.
-/

/-- The final target subfamily after the joint quotient/source-parent
regularization. -/
noncomputable def jointlyRegularizedFine
    {sourceDelta targetDelta : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {targetFine : Kakeya.Streamlined.TubeFamily targetDelta}
    {sourceEquiv : Fin targetFine.card ≃ Fin sourceFine.card}
    {sourceConstant : ENNReal} {scaleCount : ℕ}
    {representativeSchedule :
      PureWZ2FiniteRepresentativeParentScheduleData
        targetFine sourceEquiv sourceConstant scaleCount}
    (schedule : PureWZ2FiniteAnisotropicParentQuotientScheduleData
      representativeSchedule)
    (weight : Fin targetFine.card → ENNReal)
    (selection : PureWZ2FiniteStrongParentSelectionData
      weight scaleCount schedule.Parent
      (fun coordinate target =>
        (schedule.quotient coordinate).assignedParent target)
      schedule.conflict pureWZ2AnisotropicQuotientCenterConflictDegree)
    (selected : Finset
      (Fin (schedule.separatedFine weight selection).family.card)) :
    WZ2PaperPureTubeSubfamily
      (schedule.separatedFine weight selection).family :=
  WZ2PaperPureTubeSubfamily.fromFinset
    (schedule.separatedFine weight selection).family selected

/-- Indices in the final family that belong to one complete source actual
fiber at the indicated scale. -/
def jointlyRegularizedSourcePacket
    {sourceDelta targetDelta : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {targetFine : Kakeya.Streamlined.TubeFamily targetDelta}
    {sourceEquiv : Fin targetFine.card ≃ Fin sourceFine.card}
    {sourceConstant : ENNReal} {scaleCount : ℕ}
    {representativeSchedule :
      PureWZ2FiniteRepresentativeParentScheduleData
        targetFine sourceEquiv sourceConstant scaleCount}
    (schedule : PureWZ2FiniteAnisotropicParentQuotientScheduleData
      representativeSchedule)
    (weight : Fin targetFine.card → ENNReal)
    (selection : PureWZ2FiniteStrongParentSelectionData
      weight scaleCount schedule.Parent
      (fun coordinate target =>
        (schedule.quotient coordinate).assignedParent target)
      schedule.conflict pureWZ2AnisotropicQuotientCenterConflictDegree)
    (selected : Finset
      (Fin (schedule.separatedFine weight selection).family.card))
    (coordinate : Fin scaleCount)
    (sourceParent : Fin
      (representativeSchedule.sourceScale coordinate).coarse.card) :
    Finset (Fin (schedule.jointlyRegularizedFine
      weight selection selected).family.card) :=
  Finset.univ.filter fun target =>
    (representativeSchedule.sourceScale coordinate).cover.parent
        (sourceEquiv
          ((schedule.separatedFine weight selection).embedding
            ((schedule.jointlyRegularizedFine
              weight selection selected).embedding target))) =
      sourceParent

/-- Data produced by the one joint regularization pass. -/
structure PureWZ2AnisotropicJointRegularizationData
    {sourceDelta targetDelta : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {targetFine : Kakeya.Streamlined.TubeFamily targetDelta}
    {sourceEquiv : Fin targetFine.card ≃ Fin sourceFine.card}
    {sourceConstant : ENNReal} {scaleCount : ℕ}
    {representativeSchedule :
      PureWZ2FiniteRepresentativeParentScheduleData
        targetFine sourceEquiv sourceConstant scaleCount}
    (schedule : PureWZ2FiniteAnisotropicParentQuotientScheduleData
      representativeSchedule)
    (weight : Fin targetFine.card → ENNReal)
    (selection : PureWZ2FiniteStrongParentSelectionData
      weight scaleCount schedule.Parent
      (fun coordinate target =>
        (schedule.quotient coordinate).assignedParent target)
      schedule.conflict pureWZ2AnisotropicQuotientCenterConflictDegree) where
  selected : Finset
    (Fin (schedule.separatedFine weight selection).family.card)
  retained_weight :
    (∑ index : Fin (schedule.separatedFine weight selection).family.card,
        weight ((schedule.separatedFine weight selection).embedding index)) ≤
      (8 : ENNReal) *
          (Nat.log 2
            (2 * (schedule.separatedFine weight selection).family.card) + 1 :
              ENNReal) ^ (scaleCount + scaleCount + 1) *
        ∑ index ∈ selected,
          weight ((schedule.separatedFine weight selection).embedding index)
  selected_weight_pos : ∀ index ∈ selected,
    0 < weight ((schedule.separatedFine weight selection).embedding index)
  quotient_uniform : ∀ coordinate,
    WZ2PaperPureFullFibersAreCUniform
      (schedule.jointlyRegularizedFine weight selection selected).family
      (((schedule.separatedSchedule weight selection).cover coordinate
        |>.toPartitioningCover.hitParentSubfamily
          (schedule.jointlyRegularizedFine
            weight selection selected)).family)
      (16 * ((scaleCount + scaleCount : ℕ) : ENNReal) *
        (Nat.log 2
          (2 * (schedule.separatedFine weight selection).family.card) + 1 :
            ENNReal) ^ (scaleCount + scaleCount))
  source_packet_uniform : ∀ coordinate first second,
    0 < (schedule.jointlyRegularizedSourcePacket
      weight selection selected coordinate first).card →
    0 < (schedule.jointlyRegularizedSourcePacket
      weight selection selected coordinate second).card →
    ((schedule.jointlyRegularizedSourcePacket
        weight selection selected coordinate first).card : ENNReal) ≤
      (16 * ((scaleCount + scaleCount : ℕ) : ENNReal) *
        (Nat.log 2
          (2 * (schedule.separatedFine weight selection).family.card) + 1 :
            ENNReal) ^ (scaleCount + scaleCount)) *
      ((schedule.jointlyRegularizedSourcePacket
        weight selection selected coordinate second).card : ENNReal)

/-- Pointwise ambient-to-selected ratio when only hit selected fibers are
uniform.  Empty selected fibers are harmless; the requested packet is
explicitly required to be nonempty. -/
private theorem weightedFiberRatioAtPositiveSelected'
    {Parent : Type*} [Fintype Parent] [Nonempty Parent]
    (ambient selected : Parent → ENNReal)
    (weight ambientConstant selectedConstant retentionConstant : ENNReal)
    (hambient : ∀ first second,
      ambient first ≤ ambientConstant * ambient second)
    (hselected : ∀ first second,
      0 < selected first → 0 < selected second →
      selected first ≤ selectedConstant * selected second)
    (hretained :
      weight * (∑ parent, ambient parent) ≤
        retentionConstant * ∑ parent, selected parent)
    (parent : Parent)
    (hparent : 0 < selected parent) :
    weight * ambient parent ≤
      ambientConstant * retentionConstant * selectedConstant *
        selected parent := by
  let parentCount : ENNReal := Fintype.card Parent
  have hparentCountPos : 0 < parentCount := by
    simpa [parentCount] using
      (Nat.cast_pos.mpr (Fintype.card_pos : 0 < Fintype.card Parent) :
        (0 : ENNReal) < Fintype.card Parent)
  have hparentCountTop : parentCount ≠ ⊤ := by
    simp [parentCount]
  have hambientSum :
      parentCount * ambient parent ≤
        ambientConstant * ∑ other, ambient other := by
    calc
      parentCount * ambient parent = ∑ _other : Parent, ambient parent := by
        simp [parentCount]
      _ ≤ ∑ other : Parent, ambientConstant * ambient other := by
        exact Finset.sum_le_sum fun other _ => hambient parent other
      _ = ambientConstant * ∑ other, ambient other := by
        rw [Finset.mul_sum]
  have hselectedTo : ∀ other,
      selected other ≤ selectedConstant * selected parent := by
    intro other
    by_cases hother : 0 < selected other
    · exact hselected other parent hother hparent
    · have hzero : selected other = 0 := by simpa [not_lt] using hother
      rw [hzero]
      exact bot_le
  have hselectedSum :
      (∑ other, selected other) ≤
        parentCount * (selectedConstant * selected parent) := by
    calc
      (∑ other, selected other) ≤
          ∑ _other : Parent, selectedConstant * selected parent := by
        exact Finset.sum_le_sum fun other _ => hselectedTo other
      _ = parentCount * (selectedConstant * selected parent) := by
        simp [parentCount]
  have hwithCount :
      parentCount * (weight * ambient parent) ≤
        parentCount *
          (ambientConstant * retentionConstant * selectedConstant *
            selected parent) := by
    calc
      parentCount * (weight * ambient parent) =
          weight * (parentCount * ambient parent) := by ring
      _ ≤ weight * (ambientConstant * ∑ other, ambient other) := by
        gcongr
      _ = ambientConstant *
          (weight * ∑ other, ambient other) := by ring
      _ ≤ ambientConstant *
          (retentionConstant * ∑ other, selected other) := by
        gcongr
      _ ≤ ambientConstant *
          (retentionConstant *
            (parentCount * (selectedConstant * selected parent))) := by
        gcongr
      _ = parentCount *
          (ambientConstant * retentionConstant * selectedConstant *
            selected parent) := by ring
  have hwithCount' :
      (weight * ambient parent) * parentCount ≤
        (ambientConstant * retentionConstant * selectedConstant *
          selected parent) * parentCount := by
    simpa [mul_comm] using hwithCount
  exact (ENNReal.mul_le_mul_iff_left
    hparentCountPos.ne' hparentCountTop).mp hwithCount'

namespace PureWZ2AnisotropicJointRegularizationData

/-- The selected source packets partition the final target index set. -/
theorem sum_source_packet_card
    {sourceDelta targetDelta : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {targetFine : Kakeya.Streamlined.TubeFamily targetDelta}
    {sourceEquiv : Fin targetFine.card ≃ Fin sourceFine.card}
    {sourceConstant : ENNReal} {scaleCount : ℕ}
    {representativeSchedule :
      PureWZ2FiniteRepresentativeParentScheduleData
        targetFine sourceEquiv sourceConstant scaleCount}
    {schedule : PureWZ2FiniteAnisotropicParentQuotientScheduleData
      representativeSchedule}
    {weight : Fin targetFine.card → ENNReal}
    {selection : PureWZ2FiniteStrongParentSelectionData
      weight scaleCount schedule.Parent
      (fun coordinate target =>
        (schedule.quotient coordinate).assignedParent target)
      schedule.conflict pureWZ2AnisotropicQuotientCenterConflictDegree}
    (data : PureWZ2AnisotropicJointRegularizationData
      schedule weight selection)
    (coordinate : Fin scaleCount) :
    (∑ sourceParent,
        ((schedule.jointlyRegularizedSourcePacket
          weight selection data.selected coordinate sourceParent).card :
            ENNReal)) =
      (schedule.jointlyRegularizedFine
        weight selection data.selected).family.enncard := by
  change (∑ sourceParent,
      (((Finset.univ : Finset (Fin data.selected.card)).filter
        (fun target =>
          (representativeSchedule.sourceScale coordinate).cover.parent
            (sourceEquiv
              ((schedule.separatedFine weight selection).embedding
                (data.selected.orderEmbOfFin rfl target))) =
            sourceParent)).card : ENNReal)) =
    (data.selected.card : ENNReal)
  have hpartition :
      (∑ sourceParent : Fin
          (representativeSchedule.sourceScale coordinate).coarse.card,
        ((Finset.univ : Finset (Fin data.selected.card)).filter
          (fun target =>
            (representativeSchedule.sourceScale coordinate).cover.parent
              (sourceEquiv
                ((schedule.separatedFine weight selection).embedding
                  (data.selected.orderEmbOfFin rfl target))) =
              sourceParent)).card) =
        data.selected.card :=
    (Finset.sum_card_fiberwise_eq_card_filter
      (Finset.univ : Finset (Fin data.selected.card))
      (Finset.univ : Finset
        (Fin (representativeSchedule.sourceScale coordinate).coarse.card))
      (fun target =>
        (representativeSchedule.sourceScale coordinate).cover.parent
          (sourceEquiv
            ((schedule.separatedFine weight selection).embedding
              (data.selected.orderEmbOfFin rfl target))))).trans (by simp)
  rw [← Nat.cast_sum]
  exact_mod_cast hpartition

/-- The ambient complete source fibers partition the synchronized source
family. -/
theorem sum_source_fullFiber_card
    {sourceDelta targetDelta : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {targetFine : Kakeya.Streamlined.TubeFamily targetDelta}
    {sourceEquiv : Fin targetFine.card ≃ Fin sourceFine.card}
    {sourceConstant : ENNReal} {scaleCount : ℕ}
    {representativeSchedule :
      PureWZ2FiniteRepresentativeParentScheduleData
        targetFine sourceEquiv sourceConstant scaleCount}
    {schedule : PureWZ2FiniteAnisotropicParentQuotientScheduleData
      representativeSchedule}
    {weight : Fin targetFine.card → ENNReal}
    {selection : PureWZ2FiniteStrongParentSelectionData
      weight scaleCount schedule.Parent
      (fun coordinate target =>
        (schedule.quotient coordinate).assignedParent target)
      schedule.conflict pureWZ2AnisotropicQuotientCenterConflictDegree}
    (_data : PureWZ2AnisotropicJointRegularizationData
      schedule weight selection)
    (coordinate : Fin scaleCount) :
    (∑ sourceParent,
        ((wz2PaperOrdinaryFullFiberIndices sourceFine
          (representativeSchedule.sourceScale coordinate).coarse
          sourceParent).card : ENNReal)) =
      sourceFine.enncard :=
  (representativeSchedule.sourceScale coordinate).cover.sum_fullFiberCount
    (representativeSchedule.sourceScale coordinate).rho_pos.le

/-- Exact equality of the synchronized target and source cardinalities. -/
theorem separatedFine_card_eq_source
    {sourceDelta targetDelta : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {targetFine : Kakeya.Streamlined.TubeFamily targetDelta}
    {sourceEquiv : Fin targetFine.card ≃ Fin sourceFine.card}
    {sourceConstant : ENNReal} {scaleCount : ℕ}
    {representativeSchedule :
      PureWZ2FiniteRepresentativeParentScheduleData
        targetFine sourceEquiv sourceConstant scaleCount}
    {schedule : PureWZ2FiniteAnisotropicParentQuotientScheduleData
      representativeSchedule}
    {weight : Fin targetFine.card → ENNReal}
    {selection : PureWZ2FiniteStrongParentSelectionData
      weight scaleCount schedule.Parent
      (fun coordinate target =>
        (schedule.quotient coordinate).assignedParent target)
      schedule.conflict pureWZ2AnisotropicQuotientCenterConflictDegree}
    (_data : PureWZ2AnisotropicJointRegularizationData
      schedule weight selection) :
    (schedule.separatedFine weight selection).family.enncard =
      (selection.selected.card : ENNReal) := rfl

/-- A selected source actual packet controls its ambient complete source fiber
once global cardinality retention and source-packet uniformity are available.
The normalization factor is explicit so downstream CWA restriction does not
silently divide by zero or infinity. -/
theorem source_fullFiber_weighted_card_le_packet
    {sourceDelta targetDelta : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {targetFine : Kakeya.Streamlined.TubeFamily targetDelta}
    {sourceEquiv : Fin targetFine.card ≃ Fin sourceFine.card}
    {sourceConstant : ENNReal} {scaleCount : ℕ}
    {representativeSchedule :
      PureWZ2FiniteRepresentativeParentScheduleData
        targetFine sourceEquiv sourceConstant scaleCount}
    {schedule : PureWZ2FiniteAnisotropicParentQuotientScheduleData
      representativeSchedule}
    {weight : Fin targetFine.card → ENNReal}
    {selection : PureWZ2FiniteStrongParentSelectionData
      weight scaleCount schedule.Parent
      (fun coordinate target =>
        (schedule.quotient coordinate).assignedParent target)
      schedule.conflict pureWZ2AnisotropicQuotientCenterConflictDegree}
    (data : PureWZ2AnisotropicJointRegularizationData
      schedule weight selection)
    (coordinate : Fin scaleCount)
    (normalizationWeight retentionConstant : ENNReal)
    (hglobal : normalizationWeight * sourceFine.enncard ≤
      retentionConstant *
        (schedule.jointlyRegularizedFine
          weight selection data.selected).family.enncard)
    (sourceParent : Fin
      (representativeSchedule.sourceScale coordinate).coarse.card)
    (hpacket : 0 < (schedule.jointlyRegularizedSourcePacket
      weight selection data.selected coordinate sourceParent).card) :
    normalizationWeight *
        ((wz2PaperOrdinaryFullFiberIndices sourceFine
          (representativeSchedule.sourceScale coordinate).coarse
          sourceParent).card : ENNReal) ≤
      sourceConstant * retentionConstant *
          (16 * ((scaleCount + scaleCount : ℕ) : ENNReal) *
            (Nat.log 2
              (2 * (schedule.separatedFine weight selection).family.card) + 1 :
                ENNReal) ^ (scaleCount + scaleCount)) *
        ((schedule.jointlyRegularizedSourcePacket
          weight selection data.selected coordinate sourceParent).card :
            ENNReal) := by
  let ambient : Fin
      (representativeSchedule.sourceScale coordinate).coarse.card →
      ENNReal := fun parent =>
    (wz2PaperOrdinaryFullFiberIndices sourceFine
      (representativeSchedule.sourceScale coordinate).coarse parent).card
  let selectedPacket : Fin
      (representativeSchedule.sourceScale coordinate).coarse.card →
      ENNReal := fun parent =>
    (schedule.jointlyRegularizedSourcePacket
      weight selection data.selected coordinate parent).card
  have hambient : ∀ first second,
      ambient first ≤ sourceConstant * ambient second :=
    (representativeSchedule.sourceScale coordinate).full_fiber_uniform
  have hselected : ∀ first second,
      0 < selectedPacket first → 0 < selectedPacket second →
      selectedPacket first ≤
        (16 * ((scaleCount + scaleCount : ℕ) : ENNReal) *
          (Nat.log 2
            (2 * (schedule.separatedFine weight selection).family.card) + 1 :
              ENNReal) ^ (scaleCount + scaleCount)) *
          selectedPacket second := by
    intro first second hfirst hsecond
    apply data.source_packet_uniform coordinate first second
    · exact (Nat.cast_pos (α := ENNReal)).mp
        (by simpa only [selectedPacket] using hfirst)
    · exact (Nat.cast_pos (α := ENNReal)).mp
        (by simpa only [selectedPacket] using hsecond)
  have hsum :
      normalizationWeight * (∑ parent, ambient parent) ≤
        retentionConstant * ∑ parent, selectedPacket parent := by
    rw [show (∑ parent, ambient parent) = sourceFine.enncard by
      simpa [ambient] using data.sum_source_fullFiber_card coordinate]
    rw [show (∑ parent, selectedPacket parent) =
        (schedule.jointlyRegularizedFine
          weight selection data.selected).family.enncard by
      simpa [selectedPacket] using data.sum_source_packet_card coordinate]
    exact hglobal
  letI : Nonempty
      (Fin (representativeSchedule.sourceScale coordinate).coarse.card) :=
    ⟨sourceParent⟩
  have hratio := weightedFiberRatioAtPositiveSelected' ambient selectedPacket
    normalizationWeight sourceConstant
      (16 * ((scaleCount + scaleCount : ℕ) : ENNReal) *
        (Nat.log 2
          (2 * (schedule.separatedFine weight selection).family.card) + 1 :
            ENNReal) ^ (scaleCount + scaleCount))
      retentionConstant hambient hselected hsum sourceParent
      (by
        change (0 : ENNReal) <
          ((schedule.jointlyRegularizedSourcePacket
            weight selection data.selected coordinate sourceParent).card :
              ENNReal)
        exact Nat.cast_pos.mpr hpacket)
  simpa only [ambient, selectedPacket] using hratio

end PureWZ2AnisotropicJointRegularizationData

/-- One global pass simultaneously regularizes public quotient fibers and
the source actual-parent packets needed by the actual-John CWA transfer. -/
private theorem simultaneousDegreeRegularizationFiniteCoordinates
    {Index : Type u} {Coordinate : Type v}
    [Fintype Index] [DecidableEq Index]
    [Fintype Coordinate] [DecidableEq Coordinate]
    (Parent : Coordinate → Type w)
    [∀ coordinate, Fintype (Parent coordinate)]
    [∀ coordinate, DecidableEq (Parent coordinate)]
    (parent : ∀ coordinate, Index → Parent coordinate)
    (weight : Index → ENNReal) :
    ∃ selected : Finset Index,
      (∀ coordinate, ∀ first second : Parent coordinate,
        0 < (selected.filter fun index =>
          parent coordinate index = first).card →
        0 < (selected.filter fun index =>
          parent coordinate index = second).card →
        ((selected.filter fun index =>
          parent coordinate index = first).card : ENNReal) ≤
          (16 * (Fintype.card Coordinate : ENNReal) *
            (Nat.log 2 (2 * Fintype.card Index) + 1 : ENNReal) ^
              Fintype.card Coordinate) *
          ((selected.filter fun index =>
            parent coordinate index = second).card : ENNReal)) ∧
      (∑ index : Index, weight index) ≤
        (8 : ENNReal) *
          (Nat.log 2 (2 * Fintype.card Index) + 1 : ENNReal) ^
            (Fintype.card Coordinate + 1) *
          ∑ index ∈ selected, weight index ∧
      (∀ index ∈ selected, 0 < weight index) := by
  let coordinateEquiv : Fin (Fintype.card Coordinate) ≃ Coordinate :=
    (Fintype.equivFin Coordinate).symm
  let FinParent : Fin (Fintype.card Coordinate) → Type w := fun coordinate =>
    Parent (coordinateEquiv coordinate)
  let finParent : ∀ coordinate, Index → FinParent coordinate :=
    fun coordinate => parent (coordinateEquiv coordinate)
  rcases simultaneous_degree_regularization_with_support_and_weight_band
      (Fintype.card Coordinate) FinParent finParent weight with
    ⟨selected, hdegree, hretained, hpositive, _hfloor, _hband⟩
  refine ⟨selected, ?_, hretained, hpositive⟩
  let property : Coordinate → Prop := fun coordinate =>
    ∀ first second : Parent coordinate,
      0 < (selected.filter fun index =>
        parent coordinate index = first).card →
      0 < (selected.filter fun index =>
        parent coordinate index = second).card →
      ((selected.filter fun index =>
        parent coordinate index = first).card : ENNReal) ≤
        (16 * (Fintype.card Coordinate : ENNReal) *
          (Nat.log 2 (2 * Fintype.card Index) + 1 : ENNReal) ^
            Fintype.card Coordinate) *
        ((selected.filter fun index =>
          parent coordinate index = second).card : ENNReal)
  exact (Equiv.piCongrLeft property coordinateEquiv) (by
    intro finiteCoordinate
    simpa [property, FinParent, finParent] using hdegree finiteCoordinate)

/-- Pointwise ambient-to-selected ratio when only the selected fibers that
are actually hit are uniform.  This is the form needed after restricting a
parent map: empty selected fibers cause no loss, while the requested fiber is
assumed nonempty. -/
private theorem weightedFiberRatioAtPositiveSelected
    {Parent : Type*} [Fintype Parent] [Nonempty Parent]
    (ambient selected : Parent → ENNReal)
    (weight ambientConstant selectedConstant retentionConstant : ENNReal)
    (hambient : ∀ first second,
      ambient first ≤ ambientConstant * ambient second)
    (hselected : ∀ first second,
      0 < selected first → 0 < selected second →
      selected first ≤ selectedConstant * selected second)
    (hretained :
      weight * (∑ parent, ambient parent) ≤
        retentionConstant * ∑ parent, selected parent)
    (parent : Parent)
    (hparent : 0 < selected parent) :
    weight * ambient parent ≤
      ambientConstant * retentionConstant * selectedConstant *
        selected parent := by
  let parentCount : ENNReal := Fintype.card Parent
  have hparentCountPos : 0 < parentCount := by
    simpa [parentCount] using
      (Nat.cast_pos.mpr (Fintype.card_pos : 0 < Fintype.card Parent) :
        (0 : ENNReal) < Fintype.card Parent)
  have hparentCountTop : parentCount ≠ ⊤ := by
    simp [parentCount]
  have hambientSum :
      parentCount * ambient parent ≤
        ambientConstant * ∑ other, ambient other := by
    calc
      parentCount * ambient parent = ∑ _other : Parent, ambient parent := by
        simp [parentCount]
      _ ≤ ∑ other : Parent, ambientConstant * ambient other := by
        exact Finset.sum_le_sum fun other _ => hambient parent other
      _ = ambientConstant * ∑ other, ambient other := by
        rw [Finset.mul_sum]
  have hselectedTo : ∀ other,
      selected other ≤ selectedConstant * selected parent := by
    intro other
    by_cases hother : 0 < selected other
    · exact hselected other parent hother hparent
    · have hzero : selected other = 0 := by simpa [not_lt] using hother
      rw [hzero]
      exact bot_le
  have hselectedSum :
      (∑ other, selected other) ≤
        parentCount * (selectedConstant * selected parent) := by
    calc
      (∑ other, selected other) ≤
          ∑ _other : Parent, selectedConstant * selected parent := by
        exact Finset.sum_le_sum fun other _ => hselectedTo other
      _ = parentCount * (selectedConstant * selected parent) := by
        simp [parentCount]
  have hwithCount :
      parentCount * (weight * ambient parent) ≤
        parentCount *
          (ambientConstant * retentionConstant * selectedConstant *
            selected parent) := by
    calc
      parentCount * (weight * ambient parent) =
          weight * (parentCount * ambient parent) := by ring
      _ ≤ weight * (ambientConstant * ∑ other, ambient other) := by
        gcongr
      _ = ambientConstant *
          (weight * ∑ other, ambient other) := by ring
      _ ≤ ambientConstant *
          (retentionConstant * ∑ other, selected other) := by
        gcongr
      _ ≤ ambientConstant *
          (retentionConstant *
            (parentCount * (selectedConstant * selected parent))) := by
        gcongr
      _ = parentCount *
          (ambientConstant * retentionConstant * selectedConstant *
            selected parent) := by ring
  have hwithCount' :
      (weight * ambient parent) * parentCount ≤
        (ambientConstant * retentionConstant * selectedConstant *
          selected parent) * parentCount := by
    simpa [mul_comm] using hwithCount
  exact (ENNReal.mul_le_mul_iff_left
    hparentCountPos.ne' hparentCountTop).mp hwithCount'

theorem simultaneouslyRegularizeQuotientAndSource
    {sourceDelta targetDelta : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {targetFine : Kakeya.Streamlined.TubeFamily targetDelta}
    {sourceEquiv : Fin targetFine.card ≃ Fin sourceFine.card}
    {sourceConstant : ENNReal} {scaleCount : ℕ}
    {representativeSchedule :
      PureWZ2FiniteRepresentativeParentScheduleData
        targetFine sourceEquiv sourceConstant scaleCount}
    (schedule : PureWZ2FiniteAnisotropicParentQuotientScheduleData
      representativeSchedule)
    (weight : Fin targetFine.card → ENNReal)
    (selection : PureWZ2FiniteStrongParentSelectionData
      weight scaleCount schedule.Parent
      (fun coordinate target =>
        (schedule.quotient coordinate).assignedParent target)
      schedule.conflict pureWZ2AnisotropicQuotientCenterConflictDegree) :
    Nonempty (PureWZ2AnisotropicJointRegularizationData
      schedule weight selection) := by
  let separated := schedule.separatedFine weight selection
  let publicSchedule := schedule.separatedSchedule weight selection
  let JointCoordinate := Fin scaleCount ⊕ Fin scaleCount
  let JointParent : JointCoordinate → Type := fun
    | Sum.inl coordinate => publicSchedule.Parent coordinate
    | Sum.inr coordinate =>
        Fin (representativeSchedule.sourceScale coordinate).coarse.card
  letI jointParentFintype : ∀ coordinate, Fintype (JointParent coordinate) :=
    fun
    | Sum.inl _coordinate => inferInstance
    | Sum.inr _coordinate => inferInstance
  letI jointParentDecidableEq :
      ∀ coordinate, DecidableEq (JointParent coordinate) := fun
    | Sum.inl _coordinate => inferInstance
    | Sum.inr _coordinate => inferInstance
  let jointParent : ∀ jointCoordinate,
      Fin separated.family.card → JointParent jointCoordinate := fun
    | Sum.inl coordinate => fun target =>
        (publicSchedule.cover coordinate).toPartitioningCover.parent target
    | Sum.inr coordinate => fun target =>
        (representativeSchedule.sourceScale coordinate).cover.parent
          (sourceEquiv (separated.embedding target))
  let separatedWeight : Fin separated.family.card → ENNReal := fun index =>
    weight (separated.embedding index)
  rcases simultaneousDegreeRegularizationFiniteCoordinates
      JointParent jointParent separatedWeight with
    ⟨selected, hdegree, hretained, hpositive⟩
  refine ⟨{
    selected := selected
    retained_weight := ?_
    selected_weight_pos := ?_
    quotient_uniform := ?_
    source_packet_uniform := ?_
  }⟩
  · simpa [separated, separatedWeight, JointCoordinate, Fintype.card_fin,
      Nat.add_assoc] using
      hretained
  · intro index hindex
    simpa [separated, separatedWeight] using hpositive index hindex
  · intro coordinate
    let finalFine := schedule.jointlyRegularizedFine
      weight selection selected
    apply (publicSchedule.cover coordinate).toPartitioningCover
      |>.restrictToHitParents_fullFiber_uniform_of_subfamily
        (publicSchedule.cover coordinate).rho_pos.le finalFine _
    intro first second hfirst hsecond
    have hraw := hdegree (Sum.inl coordinate) first second
    have hfirstEq := fromFinset_filter_card selected
      (jointParent (Sum.inl coordinate)) first
    have hsecondEq := fromFinset_filter_card selected
      (jointParent (Sum.inl coordinate)) second
    have hfirst' : 0 < (selected.filter fun index =>
        jointParent (Sum.inl coordinate) index = first).card := by
      rw [← hfirstEq]
      change 0 < ((Finset.univ : Finset (Fin selected.card)).filter
        (fun source =>
          (publicSchedule.cover coordinate).toPartitioningCover.parent
            (selected.orderEmbOfFin rfl source) = first)).card at hfirst
      simpa [jointParent] using hfirst
    have hsecond' : 0 < (selected.filter fun index =>
        jointParent (Sum.inl coordinate) index = second).card := by
      rw [← hsecondEq]
      change 0 < ((Finset.univ : Finset (Fin selected.card)).filter
        (fun source =>
          (publicSchedule.cover coordinate).toPartitioningCover.parent
            (selected.orderEmbOfFin rfl source) = second)).card at hsecond
      simpa [jointParent] using hsecond
    have hbound := hraw hfirst' hsecond'
    rw [← hfirstEq, ← hsecondEq] at hbound
    change
      (((Finset.univ : Finset (Fin selected.card)).filter
        (fun source =>
          (publicSchedule.cover coordinate).toPartitioningCover.parent
            (selected.orderEmbOfFin rfl source) = first)).card : ENNReal) ≤
        (16 * ((scaleCount + scaleCount : ℕ) : ENNReal) *
          (Nat.log 2 (2 * separated.family.card) + 1 : ENNReal) ^
            (scaleCount + scaleCount)) *
        (((Finset.univ : Finset (Fin selected.card)).filter
          (fun source =>
            (publicSchedule.cover coordinate).toPartitioningCover.parent
              (selected.orderEmbOfFin rfl source) = second)).card : ENNReal)
    simpa [jointParent, JointCoordinate, Fintype.card_fin] using hbound
  · intro coordinate first second hfirst hsecond
    have hraw := hdegree (Sum.inr coordinate) first second
    have hfirstEq := fromFinset_filter_card selected
      (jointParent (Sum.inr coordinate)) first
    have hsecondEq := fromFinset_filter_card selected
      (jointParent (Sum.inr coordinate)) second
    have hfirst' : 0 < (selected.filter fun index =>
        jointParent (Sum.inr coordinate) index = first).card := by
      rw [← hfirstEq]
      change 0 < ((Finset.univ : Finset (Fin selected.card)).filter
        (fun target =>
          (representativeSchedule.sourceScale coordinate).cover.parent
            (sourceEquiv
              (separated.embedding
                (selected.orderEmbOfFin rfl target))) = first)).card at hfirst
      simpa [jointParent] using hfirst
    have hsecond' : 0 < (selected.filter fun index =>
        jointParent (Sum.inr coordinate) index = second).card := by
      rw [← hsecondEq]
      change 0 < ((Finset.univ : Finset (Fin selected.card)).filter
        (fun target =>
          (representativeSchedule.sourceScale coordinate).cover.parent
            (sourceEquiv
              (separated.embedding
                (selected.orderEmbOfFin rfl target))) = second)).card at hsecond
      simpa [jointParent] using hsecond
    have hbound := hraw hfirst' hsecond'
    rw [← hfirstEq, ← hsecondEq] at hbound
    change
      (((Finset.univ : Finset (Fin selected.card)).filter
        (fun target =>
          (representativeSchedule.sourceScale coordinate).cover.parent
            (sourceEquiv
              (separated.embedding
                (selected.orderEmbOfFin rfl target))) = first)).card :
          ENNReal) ≤
        (16 * ((scaleCount + scaleCount : ℕ) : ENNReal) *
          (Nat.log 2 (2 * separated.family.card) + 1 : ENNReal) ^
            (scaleCount + scaleCount)) *
        (((Finset.univ : Finset (Fin selected.card)).filter
          (fun target =>
            (representativeSchedule.sourceScale coordinate).cover.parent
              (sourceEquiv
                (separated.embedding
                  (selected.orderEmbOfFin rfl target))) = second)).card :
            ENNReal)
    simpa [jointParent, JointCoordinate, Fintype.card_fin] using hbound

end PureWZ2FiniteAnisotropicParentQuotientScheduleData

end Kakeya.Assouad

end
