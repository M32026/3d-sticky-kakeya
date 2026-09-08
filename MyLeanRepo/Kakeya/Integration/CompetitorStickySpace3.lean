import MyLeanRepo.Kakeya.Integration.CompetitorPowerAbsorption
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Theorem5_2Unconditional
import MyLeanRepo.Kakeya.Assouad.Targets.PureWZ2Node09GWZRemark
import MyLeanRepo.Kakeya.Streamlined.RandomTranslation.KatzTaoEveryScaleAlgebra

/-!
# The competitor Sticky theorem in the coordinate three-space

This is the end-to-end mathematical integration in
`EuclideanSpace Real (Fin 3)`.  It uses the original competitor hierarchy,
one common selected source, the all-real complete-fiber bridge, the reanchored
Node 9 comparison, and the proved pure WZ2 Theorem 5.2.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Integration

open Kakeya.Streamlined
open Kakeya.Streamlined.RandomTranslation
open Kakeya.Streamlined.RandomTranslation.WithShading
open CompetitorStickyInput

universe u

/-- The actual fixed dilation produced by the supporting-line quotient route. -/
def competitorAllRealOutputDilation : ℝ :=
  dominatingUpperFromDilatedCoverDilation
    competitorSupportingLineQuotientDilation

lemma competitorAllRealOutputDilation_eq :
    competitorAllRealOutputDilation = 561626000 := by
  norm_num [competitorAllRealOutputDilation,
    dominatingUpperFromDilatedCoverDilation,
    competitorSupportingLineQuotientDilation,
    competitorSupportingLineCellDilation, composedDilatedCoverDilation]

lemma selectedShading_union_subset
    {delta : NNReal} {ι : Type*} {N : ℕ} {C : NNReal}
    {lambda frostmanConstant : ENNReal} {supportRadius : ℝ}
    {input :
      CompetitorStickyInput delta ι N C lambda frostmanConstant supportRadius}
    {hN : 0 < N} {hdelta : 0 < delta} {hdeltaOne : delta ≤ 1}
    {hsourceBall : input.source.IsInUnitBall}
    (selection : input.FiniteQuotientSelectionPackage
      hN hdelta hdeltaOne hsourceBall) :
    (selection.selectedFine.restrictShading input.sourceShading).union ⊆
      input.sourceShading.union := by
  rintro point ⟨index, hpoint⟩
  exact ⟨selection.selectedFine.embedding index, hpoint⟩

/-- The repaired competitor Sticky Frostman estimate in the concrete
three-dimensional coordinate model. -/
theorem stickyFrostmanEstimate_space3 :
    StickyKakeya.StickyFrostmanEstimate.{0, u}
      (E := Space3) := by
  intro epsilon hepsilon
  let A := competitorAllRealOutputDilation
  have hA : 1 ≤ A := by
    simpa [A, competitorAllRealOutputDilation] using
      competitorAllRealOutputDilation_one
  have semantic :
      Kakeya.Assouad.PureWZ2FixedSupportDilatedStickyContract A 1 :=
    Kakeya.Assouad.pure_wz2_to_fixed_support_dilated_sticky
      Kakeya.Assouad.pure_wz2_node09_gwz_remark A 1 hA (by norm_num)
      Kakeya.Assouad.PureWZ2Theorem5_2Unconditional
  rcases semantic epsilon hepsilon with
    ⟨inputLoss, semanticThreshold, hinputLoss,
      hsemanticThreshold, hsemanticThresholdOne, hsemantic⟩
  let eta : ℝ := inputLoss / 16
  let p : ℝ := inputLoss / 16
  have heta : 0 < eta := by dsimp only [eta]; positivity
  have hp : 0 < p := by dsimp only [p]; positivity
  have hbudget : 2 * eta + 10 * p ≤ inputLoss := by
    dsimp only [eta, p]
    linarith
  rcases exists_threshold_competitorAllRealFullFiberCoefficient_le
      heta hp hbudget with
    ⟨coefficientThreshold, hcoefficientThreshold,
      hcoefficientThresholdOne, hcoefficient⟩
  rcases exists_threshold_competitorAllRealPowerInputs p hp with
    ⟨inputThreshold, hinputThreshold, hinputThresholdHalf, hinputs⟩
  let delta₀ : ℝ := min semanticThreshold
    (min (coefficientThreshold : ℝ) (inputThreshold : ℝ))
  have hdelta₀ : 0 < delta₀ := by
    dsimp only [delta₀]
    exact lt_min hsemanticThreshold <|
      lt_min (by exact_mod_cast hcoefficientThreshold)
        (by exact_mod_cast hinputThreshold)
  refine ⟨eta, delta₀, heta, hdelta₀, ?_⟩
  intro delta hdelta hdeltaSmall ι s V hsupport hED C hC hierarchy
    hfullness hnodeFrostman
  have hsemanticSmall : (delta : ℝ) ≤ semanticThreshold :=
    hdeltaSmall.trans (min_le_left _ _)
  have hcoefficientSmall : delta ≤ coefficientThreshold := by
    exact_mod_cast hdeltaSmall.trans <|
      (min_le_right _ _).trans (min_le_left _ _)
  have hinputSmall : delta ≤ inputThreshold := by
    exact_mod_cast hdeltaSmall.trans <|
      (min_le_right _ _).trans (min_le_right _ _)
  have hdeltaOne : delta ≤ 1 :=
    hcoefficientSmall.trans hcoefficientThresholdOne
  rcases hinputs hdelta hinputSmall with
    ⟨hN, hdeltaStrict, hgrid, hprofileAll, hfixed⟩
  have hlambda :
      0 < Kakeya.realRpowENN (delta : ℝ) eta := by
    exact ENNReal.ofReal_pos.mpr <|
      Real.rpow_pos_of_pos (by exact_mod_cast hdelta) eta
  have hsourceNonempty : s.Nonempty := by
    by_contra hnone
    have hempty : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hnone
    have hzero : ShadedBody.fullness' s
        (fun i => (V i).toShadedBody) = 0 := by
      subst s
      simp [ShadedBody.fullness']
    rw [hzero] at hfullness
    exact (not_le_of_gt hlambda) hfullness
  let input : CompetitorStickyInput delta ι (Tube.ssfGridLen delta) C
      (Kakeya.realRpowENN (delta : ℝ) eta)
      (Kakeya.realRpowENN (delta : ℝ) (-eta)) 1 := {
    s := s
    V := V
    shadedUniform := hierarchy
    uniformConstant_le := by simpa using hC
    fullness := hfullness
    support := hsupport
    leaf_separation := hED
    node_frostman := hnodeFrostman
  }
  have hsourceBall : input.source.IsInUnitBall :=
    (competitorTubeFamily_isInUnitBall_iff s V).2 hsupport
  have hsourceShadingMass : 0 < input.sourceShading.mass := by
    have hdense : input.sourceShading.IsLambdaDense
        (Kakeya.realRpowENN (delta : ℝ) eta) :=
      (competitorFullness_le_iff_isLambdaDense
        hdelta hsourceNonempty V _).1 hfullness
    have hsourceMass : 0 < input.source.toBodyFamily.mass := by
      rw [input.source.bodyMass_eq_nominalMass]
      exact ENNReal.mul_pos
        (by
          change (input.source.card : ENNReal) ≠ 0
          rw [show input.source.card = s.card by rfl]
          exact_mod_cast Finset.card_ne_zero.mpr hsourceNonempty)
        (RandomTranslation.deltaTubeVolume_pos
          (by exact_mod_cast hdelta)).ne'
    exact (ENNReal.mul_pos hlambda.ne' hsourceMass.ne').trans_le hdense
  let selection := Classical.choice <|
    input.exists_finiteQuotientSelectionPackage hN hdelta hdeltaOne
      hsourceBall hsourceShadingMass hlambda
  let package := Classical.choice <|
    selection.exists_allRealPackage hdeltaStrict
  have hlambdaInv :
      (Kakeya.realRpowENN (delta : ℝ) eta)⁻¹ ≤
        Kakeya.realRpowENN (delta : ℝ) (-eta) := by
    rw [GeneralizedFrostman.realRpowENN_neg
      (by exact_mod_cast hdelta)]
  have hcoefficientPower := hcoefficient hdelta hcoefficientSmall
    input hsourceBall hN hdeltaOne hdeltaStrict selection package
    hlambdaInv (le_refl _)
  have fullFiberData :
      Kakeya.Assouad.PureWZ2GWZFullFiberStructure
        (A := A) selection.selectedFine.family
        (Kakeya.realRpowENN (delta : ℝ) (-inputLoss)) := by
    change Kakeya.Assouad.PureWZ2GWZFullFiberStructure
      (A := dominatingUpperFromDilatedCoverDilation
        competitorSupportingLineQuotientDilation)
      selection.selectedFine.family
      (Kakeya.realRpowENN (delta : ℝ) (-inputLoss))
    exact
      selection.allReal_pureWZ2GWZFullFiberStructure_of_coefficient_le
        hdeltaStrict hlambda (by simp [Kakeya.realRpowENN]) package
        hcoefficientPower
  have hselectedSupport :
      Kakeya.Assouad.PureWZ2FixedBallSupport
        selection.selectedFine.family 1 := by
    intro index
    rw [selection.selectedFine.tube_eq]
    exact hsourceBall (selection.selectedFine.embedding index)
  have hweight :
      competitorFiniteQuotientWeightLoss
          (Tube.ssfGridLen delta) input.source.card ≤
        Kakeya.realRpowENN (delta : ℝ) (-p) :=
    (competitorFiniteQuotientWeightLoss_le_profileEnvelope
      (Tube.ssfGridLen delta) input.source.card).trans
        (hprofileAll input.source
          ((competitorTubeFamily_isEssentiallyDistinct_iff input.s input.V).2
            input.leaf_separation) hsourceBall)
  have hpowerInverse :
      Kakeya.realRpowENN (delta : ℝ) p ≤
        (competitorFiniteQuotientWeightLoss
          (Tube.ssfGridLen delta) input.source.card)⁻¹ := by
    calc
      Kakeya.realRpowENN (delta : ℝ) p =
          (Kakeya.realRpowENN (delta : ℝ) (-p))⁻¹ := by
            rw [GeneralizedFrostman.realRpowENN_neg
              (by exact_mod_cast hdelta), inv_inv]
      _ ≤ (competitorFiniteQuotientWeightLoss
          (Tube.ssfGridLen delta) input.source.card)⁻¹ :=
        ENNReal.inv_le_inv.mpr hweight
  have hselectedRawDense := selection.selectedShading_isLambdaDense hlambda
  have hselectedPowerDense :
      (selection.selectedFine.restrictShading input.sourceShading).IsLambdaDense
        (Kakeya.realRpowENN (delta : ℝ) inputLoss) := by
    apply Kakeya.Streamlined.isLambdaDense_weaken _ hselectedRawDense
    calc
      Kakeya.realRpowENN (delta : ℝ) inputLoss ≤
          Kakeya.realRpowENN (delta : ℝ) (eta + p) := by
        exact GeneralizedFrostman.realRpowENN_anti
          (by exact_mod_cast hdelta) (by exact_mod_cast hdeltaOne)
          (by dsimp only [eta, p]; linarith)
      _ = Kakeya.realRpowENN (delta : ℝ) eta *
          Kakeya.realRpowENN (delta : ℝ) p := by
        exact GeneralizedFrostman.realRpowENN_add
          (by exact_mod_cast hdelta)
      _ ≤ Kakeya.realRpowENN (delta : ℝ) eta *
          (competitorFiniteQuotientWeightLoss
            (Tube.ssfGridLen delta) input.source.card)⁻¹ := by gcongr
  have hselectedLower := hsemantic (delta : ℝ)
    (by exact_mod_cast hdelta) hsemanticSmall
    selection.selectedFine.family selection.selectedNonempty
    hselectedSupport selection.selectedFineED fullFiberData
    (selection.selectedFine.restrictShading input.sourceShading)
    hselectedPowerDense
  calc
    ENNReal.ofReal ((delta : ℝ) ^ epsilon) =
        Kakeya.realRpowENN (delta : ℝ) epsilon := rfl
    _ ≤ volume
        (selection.selectedFine.restrictShading input.sourceShading).union :=
      hselectedLower
    _ ≤ volume input.sourceShading.union :=
      measure_mono (selectedShading_union_subset selection)
    _ = volume (⋃ i ∈ s, (V i).shade) := by
      exact congrArg volume (competitorTubeShading_union s V)

end Kakeya.Integration

end
