import MyLeanRepo.Kakeya.Integration.CompetitorExactAllRealBridge
import MyLeanRepo.Kakeya.Integration.CompetitorQuotientFrostman
import MyLeanRepo.Kakeya.Integration.WeightedFiniteCoordinateFiberCore
import MyLeanRepo.Kakeya.Streamlined.MainLemmaTwo.DilatedBodySubfamilyTubeRecovery
import MyLeanRepo.Kakeya.Streamlined.RandomTranslation.FineSubfamilyActiveDilatedTubeCover
import MyLeanRepo.Kakeya.Streamlined.RandomTranslation.WithShading.RestrictedFiberFrostmanTransfer.Proof
import MyLeanRepo.Kakeya.Streamlined.RhoTubeMultiplicity.DilatedVolumeProduct
import MyLeanRepo.Kakeya.Streamlined.RandomTranslation.AllScaleBalancedFromDilatedCoverFrostman
import MyLeanRepo.Kakeya.Streamlined.RandomTranslation.FullContainmentFrostmanFromAssigned
import MyLeanRepo.Kakeya.Streamlined.TubeNormalizedShadingWeight
import MyLeanRepo.Kakeya.Streamlined.RandomTranslation.WithShading.ScaleTransport

/-!
# One common selection on all competitor quotient levels

Every reversed-grid level first receives the supporting-line/maximal-ED
quotient from `CompetitorSupportingLineQuotient`.  We then run one simultaneous
degree regularization on the vector of all quotient parent labels.  Thus one
and the same selected source family and restricted shading are used at every
level.

No raw occupied-node conflict-degree or scale-independent bound on the number
of raw nodes in one supporting-line cell is assumed.
-/

noncomputable section

open scoped Classical

namespace Kakeya.Integration

open Kakeya.Streamlined
open Kakeya.Streamlined.RandomTranslation

namespace CompetitorStickyInput

variable {delta : NNReal} {ι : Type*} {N : ℕ} {C : NNReal}
  {lambda frostmanConstant : ENNReal} {supportRadius : ℝ}

open Kakeya.Streamlined.RandomTranslation.WithShading

/-- The one-scale quotient at an increasing reversed-grid cut. -/
abbrev ReverseGridSupportingLineQuotientPackage
    (input :
      CompetitorStickyInput delta ι N C lambda frostmanConstant supportRadius)
    (hN : 0 < N) (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (hsourceBall : input.source.IsInUnitBall)
    (cut : Fin N) :=
  input.OneScaleSupportingLineQuotientPackage
    hN hdelta hdeltaOne hsourceBall
    (Fin.castSucc cut).rev.val
    (Nat.le_of_lt_succ (Fin.castSucc cut).rev.isLt)

/-- Canonical choice of the quotient package at one reversed-grid cut. -/
def reverseGridSupportingLineQuotient
    (input :
      CompetitorStickyInput delta ι N C lambda frostmanConstant supportRadius)
    (hN : 0 < N) (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (hsourceBall : input.source.IsInUnitBall)
    (cut : Fin N) :
    input.ReverseGridSupportingLineQuotientPackage
      hN hdelta hdeltaOne hsourceBall cut :=
  Classical.choice <|
    input.exists_oneScaleSupportingLineQuotientPackage
      hN hdelta hdeltaOne hsourceBall
      (Fin.castSucc cut).rev.val
      (Nat.le_of_lt_succ (Fin.castSucc cut).rev.isLt)

/-- Uniformity produced by one simultaneous regularization of all quotient
parent maps. -/
def competitorFiniteQuotientUniformity
    (N sourceCard : ℕ) : ENNReal :=
  weightedFiniteCoordinateFiberCoreUniformity N sourceCard

/-- Shading-mass loss of the same one-shot regularization. -/
def competitorFiniteQuotientWeightLoss
    (N sourceCard : ℕ) : ENNReal :=
  weightedFiniteCoordinateFiberCoreWeightLoss N sourceCard

/-- Loss converting an ambient quotient fiber into the corresponding fiber
of the one common selected source family. -/
def competitorFiniteQuotientFiberRetentionLoss
    (lambda : ENNReal) (N sourceCard : ℕ) : ENNReal :=
  2 * (lambda⁻¹ * competitorFiniteQuotientWeightLoss N sourceCard) *
    competitorFiniteQuotientUniformity N sourceCard

/--
One source survivor and all of its active ED quotient covers on the reversed
competitor grid.
-/
structure FiniteQuotientSelectionPackage
    (input :
      CompetitorStickyInput delta ι N C lambda frostmanConstant supportRadius)
    (hN : 0 < N) (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (hsourceBall : input.source.IsInUnitBall) where
  level :
    (cut : Fin N) →
      input.ReverseGridSupportingLineQuotientPackage
        hN hdelta hdeltaOne hsourceBall cut
  selectedIndices : Finset (Fin input.source.card)
  selectedFine : TubeSubfamily input.source :=
    TubeSubfamily.fromFinset input.source selectedIndices
  selectedFine_eq :
    selectedFine = TubeSubfamily.fromFinset input.source selectedIndices
  selectedNonempty : selectedFine.Nonempty
  selectedFineED : selectedFine.family.IsEssentiallyDistinct
  active :
    (cut : Fin N) →
      FineSubfamilyActiveDilatedTubeCover
        (level cut).quotientCover selectedFine
  activeCoarseED :
    ∀ cut, (active cut).R.family.IsEssentiallyDistinct
  activeCoverUniform :
    ∀ cut,
      (active cut).Q.toFactoring.FibersAreCUniform
        (competitorFiniteQuotientUniformity N input.source.card)
  ambientFiberComparable :
    ∀ (cut : Fin N),
    ∀ first second : Fin (level cut).quotientCoarse.card,
      0 < (selectedIndices.filter fun sourceIndex =>
        (level cut).quotientCover.parent sourceIndex = first).card →
      0 < (selectedIndices.filter fun sourceIndex =>
        (level cut).quotientCover.parent sourceIndex = second).card →
      ComparableBy 2
        (((Finset.univ.filter fun sourceIndex : Fin input.source.card =>
          (level cut).quotientCover.parent sourceIndex = first).card : ℕ) :
            ENNReal)
        (((Finset.univ.filter fun sourceIndex : Fin input.source.card =>
          (level cut).quotientCover.parent sourceIndex = second).card : ℕ) :
            ENNReal)
  shadingRetention :
    input.sourceShading.mass ≤
      competitorFiniteQuotientWeightLoss N input.source.card *
        (selectedFine.restrictShading input.sourceShading).mass
  sourceCardinalityRetention :
    (input.source.card : ENNReal) ≤
      lambda⁻¹ * competitorFiniteQuotientWeightLoss N input.source.card *
        (selectedFine.family.card : ENNReal)
  ambientFiberCountRetention :
    ∀ (cut : Fin N)
      (activeParent : Fin (active cut).R.family.card),
      (level cut).quotientCover.toFactoring.fiberCount
          ((active cut).R.embedding activeParent) ≤
        competitorFiniteQuotientFiberRetentionLoss
            lambda N input.source.card *
          (active cut).Q.toFactoring.fiberCount activeParent
  rawParentCompatibility :
    ∀ (cut : Fin N) (index : Fin selectedFine.family.card),
      (level cut).rawParentToQuotient
          (input.levelParent (Fin.castSucc cut).rev.val
            (selectedFine.embedding index)) =
        (active cut).R.embedding ((active cut).Q.parent index)

namespace FiniteQuotientSelectionPackage

variable
    {input :
      CompetitorStickyInput delta ι N C lambda frostmanConstant supportRadius}
    {hN : 0 < N} {hdelta : 0 < delta} {hdeltaOne : delta ≤ 1}
    {hsourceBall : input.source.IsInUnitBall}
    (selection :
      input.FiniteQuotientSelectionPackage
        hN hdelta hdeltaOne hsourceBall)

/-- Active lower family in the increasing reversed grid. -/
def lower (cut : Fin N) :
    Kakeya.Streamlined.TubeFamily
      (competitorReverseGrid delta N hN hdelta hdeltaOne
        (Fin.castSucc cut)).1 :=
  scaleTransportTubeFamily
    (by rfl :
      (Tube.gridScale delta N (Fin.castSucc cut).rev.val : ℝ) =
        (competitorReverseGrid delta N hN hdelta hdeltaOne
          (Fin.castSucc cut)).1)
    (selection.active cut).R.family

/-- The genuine fixed-dilation cover of the same selected source family. -/
def cover (cut : Fin N) :
    DilatedTubeCover competitorSupportingLineQuotientDilation
      selection.selectedFine.family (lower selection cut) :=
  scaleTransportDilatedTubeCover
    (by rfl :
      (Tube.gridScale delta N (Fin.castSucc cut).rev.val : ℝ) =
        (competitorReverseGrid delta N hN hdelta hdeltaOne
          (Fin.castSucc cut)).1)
    (selection.active cut).Q

/-- Explicit strong-conflict degree on one adjacent interval. -/
def competitorFiniteQuotientDegree
    (delta : NNReal) (N : ℕ)
    (hN : 0 < N) (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (cut : Fin N) : ℕ :=
  Nat.ceil
    (explicitConflictConstant (fixedDepthPowerGridKRatio (delta : ℝ) N) *
      ((competitorReverseGrid delta N hN hdelta hdeltaOne
            (Fin.succ cut)).1 /
        (competitorReverseGrid delta N hN hdelta hdeltaOne
            (Fin.castSucc cut)).1) ^ 4)

/-- The unique selected source inherits the global `deltaMax` bound obtained
from the original competitor node-Frostman partition at the top grid level. -/
theorem selectedFine_deltaMax_le_nodeFrostman_mul_sourceMass
    (hdelta : 0 < delta) :
    selection.selectedFine.family.toBodyFamily.deltaMax ≤
      frostmanConstant * input.source.toBodyFamily.mass /
        Kakeya.deltaTubeVolume 1 := by
  calc
    selection.selectedFine.family.toBodyFamily.deltaMax
        ≤ input.source.toBodyFamily.deltaMax :=
      Kakeya.Streamlined.subfamily_deltaMax_le
        selection.selectedFine.toBodySubfamily
    _ ≤ frostmanConstant * input.source.toBodyFamily.mass /
          Kakeya.deltaTubeVolume 1 := by
      simpa [Tube.gridScale_zero] using
        input.source_deltaMax_le_nodeFrostman_mul_mass_div_levelVolume
          hdelta (k := 0) (Nat.zero_le N)

/-- Every active quotient fiber retains a fixed fraction of its ambient
quotient fiber.  This is deduced from global cardinality retention plus the
ambient and selected fiber-profile comparisons; it is not asserted directly
by the weighted core. -/
theorem ambientFiberCount_le_activeFiberCount
    (cut : Fin N)
    (activeParent : Fin (selection.active cut).R.family.card) :
    (selection.level cut).quotientCover.toFactoring.fiberCount
        ((selection.active cut).R.embedding activeParent) ≤
      competitorFiniteQuotientFiberRetentionLoss
          lambda N input.source.card *
        (selection.active cut).Q.toFactoring.fiberCount activeParent := by
  exact selection.ambientFiberCountRetention cut activeParent

/-- The same common survivor has assigned-fiber Frostman control on every
active quotient level.  The only selection loss is the proved ambient-to-
selected fiber-mass ratio above. -/
theorem activeCover_assignedFrostman
    (cut : Fin N) :
    (selection.active cut).Q.toFactoring.FibersAreCFrostman
      (competitorFiniteQuotientFiberRetentionLoss
          lambda N input.source.card *
        (competitorSupportingLineQuotientFrostmanLoss * frostmanConstant)) := by
  let ambientCover := (selection.level cut).quotientCover
  let fineBodySel := selection.selectedFine.toBodySubfamily
  let coarseBodySel :=
    (selection.active cut).R.toDilatedBodySubfamily
      (B := competitorSupportingLineQuotientDilation)
  apply RandomTranslation.WithShading.restricted_fiber_frostman_transfer
      ambientCover.toFactoring fineBodySel coarseBodySel
      (selection.active cut).Q.toFactoring
      (fun index => by
        change
          (selection.active cut).R.embedding
              ((selection.active cut).Q.parent index) =
            (selection.level cut).quotientCover.parent
              (selection.selectedFine.embedding index)
        exact (selection.active cut).Q_parent index)
      (competitorSupportingLineQuotientFrostmanLoss * frostmanConstant)
      (competitorFiniteQuotientFiberRetentionLoss
        lambda N input.source.card)
  · exact (selection.level cut).quotientCover_assignedFrostman
  · intro parent
    change
      ambientCover.toFactoring.fiberMass
          ((selection.active cut).R.embedding parent) ≤
        competitorFiniteQuotientFiberRetentionLoss
            lambda N input.source.card *
          (selection.active cut).Q.toFactoring.fiberMass parent
    rw [dilated_cover_fiberMass_eq ambientCover
        ((selection.active cut).R.embedding parent),
      dilated_cover_fiberMass_eq (selection.active cut).Q parent]
    simpa only [ambientCover, mul_assoc] using
      mul_le_mul_right'
        (selection.ambientFiberCount_le_activeFiberCount cut parent)
        (Kakeya.deltaTubeVolume (delta : ℝ))

/-- All-real package type built from the common selected quotient grid. -/
abbrev AllRealPackage :=
  AllScaleBalancedFromDilatedCoverPackage
    selection.selectedFine.family
    (competitorReverseGrid delta N hN hdelta hdeltaOne)
    (lower selection) (cover selection)
    (reverseGridK delta N)
    (competitorFiniteQuotientUniformity N input.source.card)
    (competitorFiniteQuotientDegree delta N hN hdelta hdeltaOne)

/--
The common selected quotient grid satisfies every analytic input of the
finite-grid-to-all-real constructor.  In particular, its strong-degree bound
is proved from coarse ED and is not an external hypothesis.
-/
theorem exists_allRealPackage
    (hdeltaStrict : delta < 1) :
    Nonempty selection.AllRealPackage := by
  have hgate := fixed_depth_power_grid_k_ratio_gate
    (delta := (delta : ℝ)) (N := N)
    (by exact_mod_cast hdelta) (by exact_mod_cast hdeltaOne) hN
    (canonicalFixedDepthPowerGrid N hN (delta : ℝ)
      (by exact_mod_cast hdelta) (by exact_mod_cast hdeltaStrict))
  apply all_scale_balanced_from_dilated_cover
    (by exact_mod_cast hdelta) selection.selectedNonempty hN
    (competitorReverseGrid delta N hN hdelta hdeltaOne)
    (competitorReverseGrid_strict hN hdelta hdeltaOne hdeltaStrict)
    (competitorReverseGrid_zero hN hdelta hdeltaOne)
    (competitorReverseGrid_last hN hdelta hdeltaOne)
    (lower selection) (cover selection)
    (one_le_composedDilatedCoverDilation
      (by norm_num [competitorSupportingLineCellDilation])
      (by norm_num))
    (reverseGridK delta N)
    (competitorFiniteQuotientUniformity N input.source.card)
    (reverseGrid_cVol_budget hN hdelta hdeltaOne hdeltaStrict)
  · dsimp only [competitorFiniteQuotientUniformity]
    exact weightedFiniteCoordinateFiberCoreUniformity_one_le hN
  · dsimp only [competitorFiniteQuotientUniformity]
    exact weightedFiniteCoordinateFiberCoreUniformity_ne_top _ _
  · exact selection.activeCoverUniform
  · intro cut parent
    have hsigma :
        0 < (competitorReverseGrid delta N hN hdelta hdeltaOne
          (Fin.castSucc cut)).1 :=
      lt_of_lt_of_le (by exact_mod_cast hdelta)
        (competitorReverseGrid delta N hN hdelta hdeltaOne
          (Fin.castSucc cut)).2.1
    simpa [competitorFiniteQuotientDegree, reverseGridK] using
      support_free_strong_enlargement_conflict_degree_explicit
        (fixedDepthPowerGridKRatio (delta : ℝ) N) hgate.1
        hsigma
        (competitorReverseGrid_strict
          hN hdelta hdeltaOne hdeltaStrict cut).le
        (competitorReverseGrid delta N hN hdelta hdeltaOne
          (Fin.succ cut)).2.2
        (lower selection cut)
        (by
          change (selection.active cut).R.family.IsEssentiallyDistinct
          exact selection.activeCoarseED cut)
        parent

/-- The all-real construction inherits the selected grid's assigned-fiber
Frostman estimate through the actual nearby-scale parent regrouping. -/
theorem allReal_assignedFrostman
    (hdeltaStrict : delta < 1)
    (package : selection.AllRealPackage) :
    ∀ rho, (package.uts.cover rho).toFactoring.FibersAreCFrostman
      (allScaleAssignedFrostmanTransportLoss
          competitorSupportingLineQuotientDilation
          (reverseGridK delta N) *
        (competitorFiniteQuotientFiberRetentionLoss
            lambda N input.source.card *
          (competitorSupportingLineQuotientFrostmanLoss *
            frostmanConstant))) := by
  apply all_scale_balanced_from_dilated_cover_assigned_frostman
      (hdelta := by exact_mod_cast hdelta)
      (sigma := competitorReverseGrid delta N hN hdelta hdeltaOne)
      (lower := lower selection) (cover := cover selection)
      (K := reverseGridK delta N)
      (Cbase := competitorFiniteQuotientUniformity N input.source.card)
      (degree := competitorFiniteQuotientDegree
        delta N hN hdelta hdeltaOne)
      package
      (one_le_composedDilatedCoverDilation
        (by norm_num [competitorSupportingLineCellDilation])
        (by norm_num))
      (reverseGrid_cVol_budget hN hdelta hdeltaOne hdeltaStrict)
  intro cut
  exact scaleTransportDilatedTubeCover_assignedFrostman
    (by rfl :
      (Tube.gridScale delta N (Fin.castSucc cut).rev.val : ℝ) =
        (competitorReverseGrid delta N hN hdelta hdeltaOne
          (Fin.castSucc cut)).1)
    (selection.active cut).Q _
    (selection.activeCover_assignedFrostman cut)

/-- Paper-semantic complete-fiber Frostman control for the all-real output.
The owner-count and assigned-uniformity factors are explicit; assigned and
complete fibers are never identified. -/
theorem allReal_fullContainmentFrostman
    (hdeltaStrict : delta < 1)
    (package : selection.AllRealPackage) :
    package.uts.toDilatedUniformTubeStructure.IsFrostmanAtEveryScale
      (fullContainmentBranchingLoss
          (dominatingUpperFromDilatedCoverDilation
            competitorSupportingLineQuotientDilation)
          package.outputDilation_one *
        ((allScaleBalancedFromDilatedCoverDegreeFactor
            (competitorFiniteQuotientDegree
              delta N hN hdelta hdeltaOne) : ℕ) : ENNReal) *
        competitorFiniteQuotientUniformity N input.source.card *
        (allScaleAssignedFrostmanTransportLoss
            competitorSupportingLineQuotientDilation
            (reverseGridK delta N) *
          (competitorFiniteQuotientFiberRetentionLoss
              lambda N input.source.card *
            (competitorSupportingLineQuotientFrostmanLoss *
              frostmanConstant)))) := by
  have hassigned := selection.allReal_assignedFrostman hdeltaStrict package
  have hfull := RandomTranslation.AssignedDilatedUniformTubeStructure.fullContainmentFrostman_of_assigned
    (by exact_mod_cast hdelta) package.outputDilation_one package.uts hassigned
  rw [package.assignedUniformity_eq] at hfull
  simpa [mul_assoc] using hfull

end FiniteQuotientSelectionPackage

/-- Construct all quotient levels and make one common source selection. -/
theorem exists_finiteQuotientSelectionPackage
    (input :
      CompetitorStickyInput delta ι N C lambda frostmanConstant supportRadius)
    (hN : 0 < N) (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (hsourceBall : input.source.IsInUnitBall)
    (hsourceShadingMass : 0 < input.sourceShading.mass)
    (hlambda : 0 < lambda) :
    Nonempty
      (input.FiniteQuotientSelectionPackage
        hN hdelta hdeltaOne hsourceBall) := by
  let level := fun cut : Fin N =>
    input.reverseGridSupportingLineQuotient
      hN hdelta hdeltaOne hsourceBall cut
  let Label := fun cut : Fin N =>
    Fin (level cut).quotientCoarse.card
  let parent : (cut : Fin N) → Fin input.source.card → Label cut :=
    fun cut index => (level cut).quotientCover.parent index
  let weight : Fin input.source.card → ENNReal :=
    tubeNormalizedShadingWeight input.sourceShading
  have hweightTotal : 0 < ∑ index : Fin input.source.card, weight index := by
    rw [show (∑ index : Fin input.source.card, weight index) =
        input.sourceShading.mass / Kakeya.deltaTubeVolume (delta : ℝ) by
      exact sum_tubeNormalizedShadingWeight
        (by exact_mod_cast hdelta) input.sourceShading]
    exact ENNReal.div_pos hsourceShadingMass.ne'
      RandomTranslation.deltaTubeVolume_ne_top
  have hweightTop : ∀ index, weight index ≠ ⊤ := by
    intro index
    exact ne_top_of_le_ne_top (by simp) <|
      tubeNormalizedShadingWeight_le_one
        (by exact_mod_cast hdelta) input.sourceShading index
  letI : Nonempty (Fin N) := Fin.pos_iff_nonempty.mp hN
  let regularization := Classical.choice <|
    weighted_finite_coordinate_fiber_core
      (Fin input.source.card) (Fin N) Label parent weight
        hweightTotal hweightTop
  have hselectedNonempty : regularization.selected.Nonempty := by
    by_contra hnone
    have hempty : regularization.selected = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hnone
    have hzero : ∑ index ∈ regularization.selected, weight index = 0 := by
      rw [hempty]
      simp
    have hretention := regularization.weightRetention
    rw [hzero, mul_zero] at hretention
    exact (not_le_of_gt hweightTotal) hretention
  let selectedFine : TubeSubfamily input.source :=
    TubeSubfamily.fromFinset input.source regularization.selected
  have hselectedImage :
      Finset.image selectedFine.embedding Finset.univ =
        regularization.selected :=
    Finset.image_orderEmbOfFin_univ regularization.selected rfl
  have hselectedFineNonempty : selectedFine.Nonempty := by
    change 0 < regularization.selected.card
    exact hselectedNonempty.card_pos
  have hsourceED : input.source.IsEssentiallyDistinct :=
    (competitorTubeFamily_isEssentiallyDistinct_iff input.s input.V).2
      input.leaf_separation
  have hselectedFineED : selectedFine.family.IsEssentiallyDistinct :=
    TubeSubfamily.isEssentiallyDistinct selectedFine hsourceED
  let active := fun cut : Fin N =>
    fineSubfamilyActiveDilatedTubeCover
      (level cut).quotientCover selectedFine
  have hactiveED :
      ∀ cut, (active cut).R.family.IsEssentiallyDistinct := by
    intro cut
    exact TubeSubfamily.isEssentiallyDistinct (active cut).R
      (level cut).quotientCoarse_essentiallyDistinct
  have hactiveFiberCard :
      ∀ (cut : Fin N) (activeParent : Fin (active cut).R.family.card),
        (active cut).Q.toFactoring.fiberCount activeParent =
          ((regularization.selected.filter fun sourceIndex =>
            parent cut sourceIndex =
              (active cut).R.embedding activeParent).card : ENNReal) := by
    intro cut activeParent
    rw [(active cut).Q_fiberCount activeParent]
    congr 1
    let selectedFiber : Finset (Fin selectedFine.family.card) :=
      Finset.univ.filter fun index =>
        (level cut).quotientCover.parent
            (selectedFine.embedding index) =
          (active cut).R.embedding activeParent
    let ambientFiber : Finset (Fin input.source.card) :=
      regularization.selected.filter fun index =>
        parent cut index = (active cut).R.embedding activeParent
    have himage :
        Finset.image selectedFine.embedding selectedFiber = ambientFiber := by
      ext sourceIndex
      constructor
      · intro hsource
        rcases Finset.mem_image.mp hsource with ⟨index, hindex, rfl⟩
        have hdata := Finset.mem_filter.mp hindex
        exact Finset.mem_filter.mpr
          ⟨by
            have himageMem :
                selectedFine.embedding index ∈
                  Finset.image selectedFine.embedding Finset.univ :=
              Finset.mem_image.mpr ⟨index, Finset.mem_univ index, rfl⟩
            rwa [hselectedImage] at himageMem,
           by
             change
               (level cut).quotientCover.parent
                   (selectedFine.embedding index) =
                 (active cut).R.embedding activeParent
             exact hdata.2⟩
      · intro hsource
        have hdata := Finset.mem_filter.mp hsource
        have himageMem : sourceIndex ∈
            Finset.image selectedFine.embedding Finset.univ := by
          rw [hselectedImage]
          exact hdata.1
        rcases Finset.mem_image.mp himageMem with ⟨index, _, rfl⟩
        exact Finset.mem_image.mpr
          ⟨index, Finset.mem_filter.mpr
            ⟨Finset.mem_univ index, by
              change
                (level cut).quotientCover.parent
                    (selectedFine.embedding index) =
                  (active cut).R.embedding activeParent
              exact hdata.2⟩, rfl⟩
    have hcard := Finset.card_image_of_injective
      selectedFiber selectedFine.embedding.injective
    rw [himage] at hcard
    exact_mod_cast hcard.symm
  have hactiveUniform :
      ∀ cut,
        (active cut).Q.toFactoring.FibersAreCUniform
          (competitorFiniteQuotientUniformity N input.source.card) := by
    intro cut
    refine ⟨?_, ?_⟩
    · dsimp only [competitorFiniteQuotientUniformity]
      exact weightedFiniteCoordinateFiberCoreUniformity_one_le hN
    · intro first second
      rw [hactiveFiberCard cut first, hactiveFiberCard cut second]
      have hfirstPos :
          0 < (regularization.selected.filter fun sourceIndex =>
            parent cut sourceIndex =
              (active cut).R.embedding first).card := by
        rcases (active cut).Q.parent_surjective first with ⟨index, hindex⟩
        apply Finset.card_pos.mpr
        refine ⟨selectedFine.embedding index, Finset.mem_filter.mpr ⟨?_, ?_⟩⟩
        · have himageMem :
              selectedFine.embedding index ∈
                Finset.image selectedFine.embedding Finset.univ :=
            Finset.mem_image.mpr ⟨index, Finset.mem_univ index, rfl⟩
          rwa [hselectedImage] at himageMem
        · have hcompat := (active cut).Q_parent index
          rw [hindex] at hcompat
          change parent cut (selectedFine.embedding index) =
            (active cut).R.embedding first
          exact hcompat.symm
      have hsecondPos :
          0 < (regularization.selected.filter fun sourceIndex =>
            parent cut sourceIndex =
              (active cut).R.embedding second).card := by
        rcases (active cut).Q.parent_surjective second with ⟨index, hindex⟩
        apply Finset.card_pos.mpr
        refine ⟨selectedFine.embedding index, Finset.mem_filter.mpr ⟨?_, ?_⟩⟩
        · have himageMem :
              selectedFine.embedding index ∈
                Finset.image selectedFine.embedding Finset.univ :=
            Finset.mem_image.mpr ⟨index, Finset.mem_univ index, rfl⟩
          rwa [hselectedImage] at himageMem
        · have hcompat := (active cut).Q_parent index
          rw [hindex] at hcompat
          change parent cut (selectedFine.embedding index) =
            (active cut).R.embedding second
          exact hcompat.symm
      have h := regularization.fiberUniformity cut
        ((active cut).R.embedding first)
        ((active cut).R.embedding second)
        hfirstPos hsecondPos
      simpa [competitorFiniteQuotientUniformity] using h
  have hambientComparable :
      ∀ (cut : Fin N),
      ∀ first second : Fin (level cut).quotientCoarse.card,
        0 < (regularization.selected.filter fun sourceIndex =>
          (level cut).quotientCover.parent sourceIndex = first).card →
        0 < (regularization.selected.filter fun sourceIndex =>
          (level cut).quotientCover.parent sourceIndex = second).card →
        ComparableBy 2
          (((Finset.univ.filter fun sourceIndex : Fin input.source.card =>
            (level cut).quotientCover.parent sourceIndex = first).card : ℕ) :
              ENNReal)
          (((Finset.univ.filter fun sourceIndex : Fin input.source.card =>
            (level cut).quotientCover.parent sourceIndex = second).card : ℕ) :
              ENNReal) := by
    intro cut first second hfirst hsecond
    have h := regularization.ambientFiberComparable cut first second
      (by simpa only [parent] using hfirst)
      (by simpa only [parent] using hsecond)
    simpa only [parent] using h
  have hshadingRetention :
      input.sourceShading.mass ≤
        competitorFiniteQuotientWeightLoss N input.source.card *
          (selectedFine.restrictShading input.sourceShading).mass := by
    apply shadingMass_le_of_normalizedWeight
      (by exact_mod_cast hdelta) input.sourceShading selectedFine
        (competitorFiniteQuotientWeightLoss N input.source.card)
    rw [← sum_selected_tubeNormalizedShadingWeight
      input.sourceShading regularization.selected selectedFine hselectedImage]
    simpa [weight, competitorFiniteQuotientWeightLoss] using
      regularization.weightRetention
  have hsourceNonempty : input.s.Nonempty := by
    by_contra hnone
    have hempty : input.s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hnone
    have hzero : input.sourceShading.mass = 0 := by
      change (competitorTubeShading input.s input.V).mass = 0
      rw [competitorTubeShading_mass, hempty]
      simp
    exact (ne_of_gt hsourceShadingMass) hzero
  have hlambdaTop : lambda ≠ ⊤ := by
    have hleOne : lambda ≤ 1 :=
      input.fullness.trans <|
        ShadedBody.fullness'_le_one input.s
          (fun index => (input.V index).toShadedBody)
    exact ne_top_of_le_ne_top (by simp) hleOne
  have haverageWeight :
      lambda * (input.source.card : ENNReal) ≤
        ∑ index : Fin input.source.card, weight index := by
    have hdense : input.sourceShading.IsLambdaDense lambda :=
      (competitorFullness_le_iff_isLambdaDense
        hdelta hsourceNonempty input.V lambda).1 input.fullness
    let tubeVolume := Kakeya.deltaTubeVolume (delta : ℝ)
    have htubeVolumeZero : tubeVolume ≠ 0 :=
      (RandomTranslation.deltaTubeVolume_pos
        (by exact_mod_cast hdelta)).ne'
    have htubeVolumeTop : tubeVolume ≠ ⊤ :=
      RandomTranslation.deltaTubeVolume_ne_top
    rw [show (∑ index : Fin input.source.card, weight index) =
        input.sourceShading.mass / tubeVolume by
      exact sum_tubeNormalizedShadingWeight
        (by exact_mod_cast hdelta) input.sourceShading]
    apply (ENNReal.le_div_iff_mul_le
      (Or.inl htubeVolumeZero) (Or.inl htubeVolumeTop)).2
    calc
      lambda * (input.source.card : ENNReal) * tubeVolume =
          lambda * input.source.toBodyFamily.mass := by
        change lambda * input.source.enncard * tubeVolume =
          lambda * input.source.toBodyFamily.mass
        rw [input.source.bodyMass_eq_nominalMass]
        simp only [TubeFamily.nominalMass]
        ring
      _ ≤ input.sourceShading.mass := hdense
  have hsourceCardinality :
      (input.source.card : ENNReal) ≤
        lambda⁻¹ * competitorFiniteQuotientWeightLoss N input.source.card *
          (selectedFine.family.card : ENNReal) := by
    have haverageWeight' :
        lambda * (Fintype.card (Fin input.source.card) : ENNReal) ≤
          ∑ index : Fin input.source.card, weight index := by
      simpa using haverageWeight
    have hcore := regularization.cardinalityRetention_of_averageWeight
      lambda hlambda.ne' hlambdaTop haverageWeight'
      (fun index => tubeNormalizedShadingWeight_le_one
        (by exact_mod_cast hdelta) input.sourceShading index)
    simpa [selectedFine, competitorFiniteQuotientWeightLoss,
      TubeSubfamily.fromFinset] using hcore
  have hambientFiberRetention :
      ∀ (cut : Fin N)
        (activeParent : Fin (active cut).R.family.card),
        (level cut).quotientCover.toFactoring.fiberCount
            ((active cut).R.embedding activeParent) ≤
          competitorFiniteQuotientFiberRetentionLoss
              lambda N input.source.card *
            (active cut).Q.toFactoring.fiberCount activeParent := by
    intro cut activeParent
    have hactivePositive :
        0 < (regularization.selected.filter fun sourceIndex =>
          parent cut sourceIndex =
            (active cut).R.embedding activeParent).card := by
      rcases (active cut).Q.parent_surjective activeParent with
        ⟨index, hindex⟩
      apply Finset.card_pos.mpr
      refine ⟨selectedFine.embedding index, Finset.mem_filter.mpr ⟨?_, ?_⟩⟩
      · have himageMem :
            selectedFine.embedding index ∈
              Finset.image selectedFine.embedding Finset.univ :=
          Finset.mem_image.mpr ⟨index, Finset.mem_univ index, rfl⟩
        rwa [hselectedImage] at himageMem
      · have hcompat := (active cut).Q_parent index
        rw [hindex] at hcompat
        exact hcompat.symm
    have hcore := regularization.ambientFiber_le_of_cardinalityRetention
      (lambda⁻¹ * competitorFiniteQuotientWeightLoss N input.source.card)
      (by simpa [selectedFine, TubeSubfamily.fromFinset] using
        hsourceCardinality) cut
      ((active cut).R.embedding activeParent) hactivePositive
    rw [hactiveFiberCard cut activeParent]
    change
      (((Finset.univ.filter fun sourceIndex : Fin input.source.card =>
        (level cut).quotientCover.parent sourceIndex =
          (active cut).R.embedding activeParent).card : ℕ) : ENNReal) ≤ _
    simpa only [parent, Fintype.card_fin,
      competitorFiniteQuotientFiberRetentionLoss,
      competitorFiniteQuotientUniformity] using hcore
  refine ⟨{
    level := level
    selectedIndices := regularization.selected
    selectedFine := selectedFine
    selectedFine_eq := rfl
    selectedNonempty := hselectedFineNonempty
    selectedFineED := hselectedFineED
    active := active
    activeCoarseED := hactiveED
    activeCoverUniform := hactiveUniform
    ambientFiberComparable := hambientComparable
    shadingRetention := hshadingRetention
    sourceCardinalityRetention := hsourceCardinality
    ambientFiberCountRetention := hambientFiberRetention
    rawParentCompatibility := ?_
  }⟩
  intro cut index
  have hquotient :=
    (level cut).rawParentToQuotient_rawParentOfSource
      (selectedFine.embedding index)
  have hactive := (active cut).Q_parent index
  exact hquotient.trans hactive.symm

end CompetitorStickyInput
end Kakeya.Integration

end
