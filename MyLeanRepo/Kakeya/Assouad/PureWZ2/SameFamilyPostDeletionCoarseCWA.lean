import MyLeanRepo.Kakeya.Assouad.PureWZ2.SameFamilyPostDeletionCardinality
import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12PureNearbyRestriction
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperLinePackingCardinality

/-!
# Coarse pure CWA after positive parent deletion

Positive whole-parent deletion gives the required global coarse-cardinality
retention, but cardinality retention alone does not preserve normalized pure
CWA.  The exact remaining mathematical leaf is degree uniformity of the
surviving callers inside every actual nearby witness of the pre-deletion
coarse pure CWA.

Once that leaf is supplied, the closed weighted-restriction theorem restores
pure nearby-scale CWA mechanically.  No second coarse regularization is
performed.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

namespace PureWZ2SameFamilyPositiveParentDeletionData

noncomputable def postDeletionPureCoarseSubfamily
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant fiberConstant coarseConstant : ENNReal}
    {actualRequested : WZ2PaperRequestedScale delta}
    {actualNearby :
      WZ2PaperPureNearbyScaleCoverData
        fine actualRequested ambientConstant}
    {callerRequested : WZ2PaperRequestedScale delta}
    {shading : WZ1PaperTubeShading fine}
    {quotient :
      PureWZ2ParentQuotientNetSelectionData
        actualNearby callerRequested shading}
    {support : PureWZ2PositiveCallerSupportData quotient}
    {coordinateCount : ℕ}
    {regularized :
      PureWZ2AllPositiveCallerRegularizationData
        (outputConstant := fiberConstant)
        actualNearby quotient support coordinateCount}
    {merged :
      PureWZ2MergedCallerClassRegularizationData
        actualNearby quotient support coordinateCount regularized}
    {scales :
      Fin coordinateCount → WZ2PaperRequestedScale delta}
    {scheduled :
      ∀ coordinate,
        WZ2PaperPureNearbyScaleCoverData
          fine (scales coordinate) ambientConstant}
    {sameFamily :
      PureWZ2SameFamilyCallerNearbyAssemblyData
        (coarseConstant := coarseConstant)
        actualNearby quotient support coordinateCount regularized merged
        scales scheduled}
    {scaleSeparation : 18 * delta ≤ callerRequested.1}
    {balancing :
      PureWZ2SameFamilyFixedOriginBalancingData
        actualNearby quotient support coordinateCount regularized merged
        scales scheduled sameFamily scaleSeparation}
    {deletionExponent : ℕ}
    (data :
      PureWZ2SameFamilyPositiveParentDeletionData
        actualNearby quotient support coordinateCount regularized merged
        scales scheduled sameFamily scaleSeparation balancing
        deletionExponent) :
    WZ2PaperPureTubeSubfamily sameFamily.selectedCoarse.family where
  family := data.selectedCoarse.family
  embedding := data.selectedCoarse.embedding
  tube_eq := data.selectedCoarse.tube_eq

def postDeletionCoarseRestrictionConstant
    (coarseConstant degreeConstant balancingLoss : ENNReal) : ENNReal :=
  wz2PaperPureNearbyRestrictionConstant
    coarseConstant 1 degreeConstant (4 * balancingLoss)

/-- Polynomial packing bound for the final caller-scale line family. -/
def postDeletionCoarsePackingDegreeConstant (rho : ℝ) : ENNReal :=
  (((2 * Nat.ceil (80 / rho) + 1) ^ 5 : ℕ) : ENNReal)

/--
The exact missing class-degree condition after whole-parent deletion.
-/
def PostDeletionCoarseClassDegreeUniform
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant fiberConstant coarseConstant : ENNReal}
    {actualRequested : WZ2PaperRequestedScale delta}
    {actualNearby :
      WZ2PaperPureNearbyScaleCoverData
        fine actualRequested ambientConstant}
    {callerRequested : WZ2PaperRequestedScale delta}
    {shading : WZ1PaperTubeShading fine}
    {quotient :
      PureWZ2ParentQuotientNetSelectionData
        actualNearby callerRequested shading}
    {support : PureWZ2PositiveCallerSupportData quotient}
    {coordinateCount : ℕ}
    {regularized :
      PureWZ2AllPositiveCallerRegularizationData
        (outputConstant := fiberConstant)
        actualNearby quotient support coordinateCount}
    {merged :
      PureWZ2MergedCallerClassRegularizationData
        actualNearby quotient support coordinateCount regularized}
    {scales :
      Fin coordinateCount → WZ2PaperRequestedScale delta}
    {scheduled :
      ∀ coordinate,
        WZ2PaperPureNearbyScaleCoverData
          fine (scales coordinate) ambientConstant}
    {sameFamily :
      PureWZ2SameFamilyCallerNearbyAssemblyData
        (coarseConstant := coarseConstant)
        actualNearby quotient support coordinateCount regularized merged
        scales scheduled}
    {scaleSeparation : 18 * delta ≤ callerRequested.1}
    {balancing :
      PureWZ2SameFamilyFixedOriginBalancingData
        actualNearby quotient support coordinateCount regularized merged
        scales scheduled sameFamily scaleSeparation}
    {deletionExponent : ℕ}
    (data :
      PureWZ2SameFamilyPositiveParentDeletionData
        actualNearby quotient support coordinateCount regularized merged
        scales scheduled sameFamily scaleSeparation balancing
        deletionExponent)
    (degreeConstant : ENNReal) : Prop :=
  ∀ requested : WZ2PaperRequestedScale callerRequested.1,
    let nearby :=
      Classical.choice (sameFamily.coarse_pure_cwa.2.2.2 requested)
    ∀ first second : Fin nearby.scaleData.coarse.card,
      0 <
          ((Finset.univ :
            Finset
              (Fin data.postDeletionPureCoarseSubfamily.family.card)).filter
            fun source =>
              nearby.scaleData.cover.parent
                  (data.postDeletionPureCoarseSubfamily.embedding source) =
                first).card →
      0 <
          ((Finset.univ :
            Finset
              (Fin data.postDeletionPureCoarseSubfamily.family.card)).filter
            fun source =>
              nearby.scaleData.cover.parent
                  (data.postDeletionPureCoarseSubfamily.embedding source) =
                second).card →
      (((Finset.univ :
        Finset
          (Fin data.postDeletionPureCoarseSubfamily.family.card)).filter
        fun source =>
          nearby.scaleData.cover.parent
              (data.postDeletionPureCoarseSubfamily.embedding source) =
            first).card : ENNReal) ≤
        degreeConstant *
          (((Finset.univ :
            Finset
              (Fin data.postDeletionPureCoarseSubfamily.family.card)).filter
            fun source =>
              nearby.scaleData.cover.parent
                  (data.postDeletionPureCoarseSubfamily.embedding source) =
                second).card : ENNReal)

theorem post_deletion_coarse_class_degree_uniform
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant fiberConstant coarseConstant : ENNReal}
    {actualRequested : WZ2PaperRequestedScale delta}
    {actualNearby :
      WZ2PaperPureNearbyScaleCoverData
        fine actualRequested ambientConstant}
    {callerRequested : WZ2PaperRequestedScale delta}
    {shading : WZ1PaperTubeShading fine}
    {quotient :
      PureWZ2ParentQuotientNetSelectionData
        actualNearby callerRequested shading}
    {support : PureWZ2PositiveCallerSupportData quotient}
    {coordinateCount : ℕ}
    {regularized :
      PureWZ2AllPositiveCallerRegularizationData
        (outputConstant := fiberConstant)
        actualNearby quotient support coordinateCount}
    {merged :
      PureWZ2MergedCallerClassRegularizationData
        actualNearby quotient support coordinateCount regularized}
    {scales :
      Fin coordinateCount → WZ2PaperRequestedScale delta}
    {scheduled :
      ∀ coordinate,
        WZ2PaperPureNearbyScaleCoverData
          fine (scales coordinate) ambientConstant}
    {sameFamily :
      PureWZ2SameFamilyCallerNearbyAssemblyData
        (coarseConstant := coarseConstant)
        actualNearby quotient support coordinateCount regularized merged
        scales scheduled}
    {scaleSeparation : 18 * delta ≤ callerRequested.1}
    {balancing :
      PureWZ2SameFamilyFixedOriginBalancingData
        actualNearby quotient support coordinateCount regularized merged
        scales scheduled sameFamily scaleSeparation}
    {deletionExponent : ℕ}
    (data :
      PureWZ2SameFamilyPositiveParentDeletionData
        actualNearby quotient support coordinateCount regularized merged
        scales scheduled sameFamily scaleSeparation balancing
        deletionExponent) :
    data.PostDeletionCoarseClassDegreeUniform
      (postDeletionCoarsePackingDegreeConstant callerRequested.1) := by
  have familyCardinality :
      data.selectedCoarse.family.card ≤
        (2 * Nat.ceil (80 / callerRequested.1) + 1) ^ 5 :=
    paper_essentially_distinct_card_bound_nat
      data.section6Cover.coarse_essentially_distinct
      data.section6Cover.coarse_line_class
      (actualNearby.scaleData.delta_pos.trans_le callerRequested.2.1)
      callerRequested.2.2
  intro requested
  dsimp only
  intro first second _hfirst hsecond
  let firstClass :=
    (Finset.univ :
      Finset (Fin data.postDeletionPureCoarseSubfamily.family.card)).filter
        fun source =>
          (Classical.choice
            (sameFamily.coarse_pure_cwa.2.2.2 requested)
          ).scaleData.cover.parent
              (data.postDeletionPureCoarseSubfamily.embedding source) =
            first
  let secondClass :=
    (Finset.univ :
      Finset (Fin data.postDeletionPureCoarseSubfamily.family.card)).filter
        fun source =>
          (Classical.choice
            (sameFamily.coarse_pure_cwa.2.2.2 requested)
          ).scaleData.cover.parent
              (data.postDeletionPureCoarseSubfamily.embedding source) =
            second
  have firstClassCard :
      firstClass.card ≤ data.selectedCoarse.family.card := by
    calc
      firstClass.card ≤
          data.postDeletionPureCoarseSubfamily.family.card :=
        by
          simpa using
            Finset.card_le_card
              (Finset.subset_univ firstClass)
      _ = data.selectedCoarse.family.card := rfl
  have firstClassBound :
      (firstClass.card : ENNReal) ≤
        postDeletionCoarsePackingDegreeConstant callerRequested.1 := by
    unfold postDeletionCoarsePackingDegreeConstant
    exact_mod_cast firstClassCard.trans familyCardinality
  have secondClassOne : (1 : ENNReal) ≤ secondClass.card := by
    exact_mod_cast hsecond
  change
    (firstClass.card : ENNReal) ≤
      postDeletionCoarsePackingDegreeConstant callerRequested.1 *
        (secondClass.card : ENNReal)
  exact
    firstClassBound.trans <| by
      simpa only [mul_one] using
        mul_le_mul_left'
          secondClassOne
          (postDeletionCoarsePackingDegreeConstant callerRequested.1)

theorem post_deletion_coarse_pure_cwa
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant fiberConstant coarseConstant : ENNReal}
    {actualRequested : WZ2PaperRequestedScale delta}
    {actualNearby :
      WZ2PaperPureNearbyScaleCoverData
        fine actualRequested ambientConstant}
    {callerRequested : WZ2PaperRequestedScale delta}
    {shading : WZ1PaperTubeShading fine}
    {quotient :
      PureWZ2ParentQuotientNetSelectionData
        actualNearby callerRequested shading}
    {support : PureWZ2PositiveCallerSupportData quotient}
    {coordinateCount : ℕ}
    {regularized :
      PureWZ2AllPositiveCallerRegularizationData
        (outputConstant := fiberConstant)
        actualNearby quotient support coordinateCount}
    {merged :
      PureWZ2MergedCallerClassRegularizationData
        actualNearby quotient support coordinateCount regularized}
    {scales :
      Fin coordinateCount → WZ2PaperRequestedScale delta}
    {scheduled :
      ∀ coordinate,
        WZ2PaperPureNearbyScaleCoverData
          fine (scales coordinate) ambientConstant}
    {sameFamily :
      PureWZ2SameFamilyCallerNearbyAssemblyData
        (coarseConstant := coarseConstant)
        actualNearby quotient support coordinateCount regularized merged
        scales scheduled}
    {scaleSeparation : 18 * delta ≤ callerRequested.1}
    {balancing :
      PureWZ2SameFamilyFixedOriginBalancingData
        actualNearby quotient support coordinateCount regularized merged
        scales scheduled sameFamily scaleSeparation}
    {deletionExponent : ℕ}
    (data :
      PureWZ2SameFamilyPositiveParentDeletionData
        actualNearby quotient support coordinateCount regularized merged
        scales scheduled sameFamily scaleSeparation balancing
        deletionExponent)
    (degreeConstant : ENNReal)
    (degreeConstant_ne_top : degreeConstant ≠ ⊤)
    (degreeUniform :
      PostDeletionCoarseClassDegreeUniform data degreeConstant) :
    WZ2PaperPureCWAAtNearbyScales
      data.selectedCoarse.family
      (postDeletionCoarseRestrictionConstant
        coarseConstant degreeConstant
        (pureWZ2SameFamilyFixedOriginBalancingLoss
          balancing.balanced)) := by
  let selected := data.postDeletionPureCoarseSubfamily
  have selectedNonempty : selected.family.Nonempty := by
    change
      0 <
        (data.post.postDeletion.deletion.deletion.retainedParents).card
    exact
      data.post.postDeletion.deletion.deletion
        |>.retainedParents_nonempty.card_pos
  have retentionTop :
      4 *
          pureWZ2SameFamilyFixedOriginBalancingLoss
            balancing.balanced ≠
        ⊤ := by
    unfold pureWZ2SameFamilyFixedOriginBalancingLoss
    unfold wz2PaperFinalBalancedCoverLoss
    repeat' apply ENNReal.mul_ne_top
    all_goals
      first
      | exact ENNReal.natCast_ne_top _
      | exact
          ENNReal.add_ne_top.mpr
            ⟨ENNReal.natCast_ne_top _, by norm_num⟩
      | norm_num
  have cardinality :
      (1 : ENNReal) * sameFamily.selectedCoarse.family.enncard ≤
        (4 *
          pureWZ2SameFamilyFixedOriginBalancingLoss
            balancing.balanced) *
          selected.family.enncard := by
    change
      (1 : ENNReal) * sameFamily.selectedCoarse.family.enncard ≤
        (4 *
          pureWZ2SameFamilyFixedOriginBalancingLoss
            balancing.balanced) *
          data.selectedCoarse.family.enncard
    simpa only [one_mul] using data.retained_coarse_cardinality
  exact
    sameFamily.coarse_pure_cwa.restrictOfWeightedRetention
      selected selectedNonempty
      (by norm_num) (by norm_num)
      retentionTop degreeConstant_ne_top cardinality degreeUniform

theorem post_deletion_coarse_pure_cwa_of_packing
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant fiberConstant coarseConstant : ENNReal}
    {actualRequested : WZ2PaperRequestedScale delta}
    {actualNearby :
      WZ2PaperPureNearbyScaleCoverData
        fine actualRequested ambientConstant}
    {callerRequested : WZ2PaperRequestedScale delta}
    {shading : WZ1PaperTubeShading fine}
    {quotient :
      PureWZ2ParentQuotientNetSelectionData
        actualNearby callerRequested shading}
    {support : PureWZ2PositiveCallerSupportData quotient}
    {coordinateCount : ℕ}
    {regularized :
      PureWZ2AllPositiveCallerRegularizationData
        (outputConstant := fiberConstant)
        actualNearby quotient support coordinateCount}
    {merged :
      PureWZ2MergedCallerClassRegularizationData
        actualNearby quotient support coordinateCount regularized}
    {scales :
      Fin coordinateCount → WZ2PaperRequestedScale delta}
    {scheduled :
      ∀ coordinate,
        WZ2PaperPureNearbyScaleCoverData
          fine (scales coordinate) ambientConstant}
    {sameFamily :
      PureWZ2SameFamilyCallerNearbyAssemblyData
        (coarseConstant := coarseConstant)
        actualNearby quotient support coordinateCount regularized merged
        scales scheduled}
    {scaleSeparation : 18 * delta ≤ callerRequested.1}
    {balancing :
      PureWZ2SameFamilyFixedOriginBalancingData
        actualNearby quotient support coordinateCount regularized merged
        scales scheduled sameFamily scaleSeparation}
    {deletionExponent : ℕ}
    (data :
      PureWZ2SameFamilyPositiveParentDeletionData
        actualNearby quotient support coordinateCount regularized merged
        scales scheduled sameFamily scaleSeparation balancing
        deletionExponent) :
    WZ2PaperPureCWAAtNearbyScales
      data.selectedCoarse.family
      (postDeletionCoarseRestrictionConstant
        coarseConstant
        (postDeletionCoarsePackingDegreeConstant callerRequested.1)
        (pureWZ2SameFamilyFixedOriginBalancingLoss
          balancing.balanced)) :=
  data.post_deletion_coarse_pure_cwa
    (postDeletionCoarsePackingDegreeConstant callerRequested.1)
    (by
      unfold postDeletionCoarsePackingDegreeConstant
      exact ENNReal.natCast_ne_top _)
    data.post_deletion_coarse_class_degree_uniform

end PureWZ2SameFamilyPositiveParentDeletionData

end Kakeya.Assouad

end
