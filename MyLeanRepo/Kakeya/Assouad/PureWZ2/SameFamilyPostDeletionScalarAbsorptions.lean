import MyLeanRepo.Kakeya.Assouad.PureWZ2.SameFamilyPostDeletionLeaves
import MyLeanRepo.Kakeya.Assouad.ConstantAbsorption

noncomputable section

namespace Kakeya.Assouad

namespace PureWZ2SameFamilyPositiveParentDeletionData

variable
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

structure PostDeletionUniformScalarCore
    (data :
      PureWZ2SameFamilyPositiveParentDeletionData
        actualNearby quotient support coordinateCount regularized merged
        scales scheduled sameFamily scaleSeparation balancing
        deletionExponent) where
  degreeConstant : ENNReal
  degreeConstant_ne_top : degreeConstant ≠ ⊤
  degree_uniform :
    data.PostDeletionCoarseClassDegreeUniform degreeConstant
  rho_small : callerRequested.1 ≤ 1 / 24
  fiber_ratio_small : delta / callerRequested.1 ≤ 1 / 24

structure PostDeletionScalarAbsorptions
    {outputLoss : ℝ}
    (data :
      PureWZ2SameFamilyPositiveParentDeletionData
        actualNearby quotient support coordinateCount regularized merged
        scales scheduled sameFamily scaleSeparation balancing
        deletionExponent)
    (logExponent : ℕ)
    extends PostDeletionUniformScalarCore data where
  retention_absorption :
    wz2PaperPureRefinementFraction delta logExponent *
          (2 *
            (((pureWZ2ParentQuotientNetConflictDegree : ENNReal) *
                pureWZ2CompleteParentRegularizationLoss
                  actualNearby.scaleData.coarse.card coordinateCount *
                sameFamily.retentionConstant) *
              pureWZ2SameFamilyFixedOriginBalancingLoss
                balancing.balanced)) ≤
      1
  coarse_cwa_absorption :
    postDeletionCoarseRestrictionConstant
        coarseConstant degreeConstant
        (pureWZ2SameFamilyFixedOriginBalancingLoss balancing.balanced) ≤
      Kakeya.realRpowENN callerRequested.1 (-outputLoss)

def postDeletionUniformScalarCore
    (data :
      PureWZ2SameFamilyPositiveParentDeletionData
        actualNearby quotient support coordinateCount regularized merged
        scales scheduled sameFamily scaleSeparation balancing
        deletionExponent)
    (rhoSmall : callerRequested.1 ≤ 1 / 24)
    (fiberRatioSmall : delta / callerRequested.1 ≤ 1 / 24) :
    PostDeletionUniformScalarCore data where
  degreeConstant :=
    postDeletionCoarsePackingDegreeConstant callerRequested.1
  degreeConstant_ne_top := by
    unfold postDeletionCoarsePackingDegreeConstant
    exact ENNReal.natCast_ne_top _
  degree_uniform :=
    data.post_deletion_coarse_class_degree_uniform
  rho_small := rhoSmall
  fiber_ratio_small := fiberRatioSmall

def PostDeletionUniformScalarCore.withAbsorptions
    {outputLoss : ℝ}
    {data :
      PureWZ2SameFamilyPositiveParentDeletionData
        actualNearby quotient support coordinateCount regularized merged
        scales scheduled sameFamily scaleSeparation balancing
        deletionExponent}
    (core : PostDeletionUniformScalarCore data)
    (logExponent : ℕ)
    (retentionAbsorption :
      wz2PaperPureRefinementFraction delta logExponent *
            (2 *
              (((pureWZ2ParentQuotientNetConflictDegree : ENNReal) *
                  pureWZ2CompleteParentRegularizationLoss
                    actualNearby.scaleData.coarse.card coordinateCount *
                  sameFamily.retentionConstant) *
                pureWZ2SameFamilyFixedOriginBalancingLoss
                  balancing.balanced)) ≤
        1)
    (coarseCWAAbsorption :
      postDeletionCoarseRestrictionConstant
          coarseConstant core.degreeConstant
          (pureWZ2SameFamilyFixedOriginBalancingLoss balancing.balanced) ≤
        Kakeya.realRpowENN callerRequested.1 (-outputLoss)) :
    PostDeletionScalarAbsorptions
      (outputLoss := outputLoss) data logExponent where
  degreeConstant := core.degreeConstant
  degreeConstant_ne_top := core.degreeConstant_ne_top
  degree_uniform := core.degree_uniform
  rho_small := core.rho_small
  fiber_ratio_small := core.fiber_ratio_small
  retention_absorption := retentionAbsorption
  coarse_cwa_absorption := coarseCWAAbsorption

theorem node3_fiber_ratio_le_power
    {outputLoss rho : ℝ}
    (deltaPos : 0 < delta)
    (rhoPos : 0 < rho)
    (rhoLower : Real.rpow delta (1 - outputLoss) ≤ rho) :
    delta / rho ≤ Real.rpow delta outputLoss := by
  have split :
      delta =
        Real.rpow delta (1 - outputLoss) *
          Real.rpow delta outputLoss := by
    calc
      delta = Real.rpow delta 1 := by simp
      _ =
          Real.rpow delta ((1 - outputLoss) + outputLoss) := by
            congr 1
            ring
      _ =
          Real.rpow delta (1 - outputLoss) *
            Real.rpow delta outputLoss :=
        Real.rpow_add deltaPos (1 - outputLoss) outputLoss
  rw [div_le_iff₀ rhoPos]
  calc
    delta =
        Real.rpow delta (1 - outputLoss) *
          Real.rpow delta outputLoss := split
    _ ≤ rho * Real.rpow delta outputLoss :=
      mul_le_mul_of_nonneg_right rhoLower
        (Real.rpow_nonneg deltaPos.le outputLoss)
    _ = Real.rpow delta outputLoss * rho := mul_comm _ _

theorem exists_node3_uniform_twenty_four_scale
    (outputLoss : ℝ)
    (outputLossPos : 0 < outputLoss) :
    ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
        ∀ rho : ℝ, 0 < rho →
          Real.rpow delta (1 - outputLoss) ≤ rho →
          rho ≤ Real.rpow delta outputLoss →
            rho ≤ 1 / 24 ∧ delta / rho ≤ 1 / 24 := by
  rcases
      exists_delta_mul_rpow_le_rpow
        24 (by norm_num)
        (alpha := outputLoss) (beta := 0)
        outputLossPos with
    ⟨delta₀, delta₀Pos, delta₀One, absorb⟩
  refine ⟨delta₀, delta₀Pos, delta₀One, ?_⟩
  intro delta deltaPos deltaBound rho rhoPos rhoLower rhoUpper
  have powerSmall : Real.rpow delta outputLoss ≤ 1 / 24 := by
    have bound := absorb delta deltaPos deltaBound
    have boundOne :
        24 * Real.rpow delta outputLoss ≤ 1 := by
      simpa using bound
    nlinarith [Real.rpow_nonneg deltaPos.le outputLoss]
  exact
    ⟨rhoUpper.trans powerSmall,
      (node3_fiber_ratio_le_power
        deltaPos rhoPos rhoLower).trans powerSmall⟩

theorem exists_postDeletionUniformScalarCore
    (outputLoss : ℝ)
    (outputLossPos : 0 < outputLoss) :
    ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ {delta : ℝ}, 0 < delta → delta ≤ delta₀ →
        ∀ {fine : Kakeya.Streamlined.TubeFamily delta}
          {ambientConstant fiberConstant coarseConstant : ENNReal}
          {actualRequested : WZ2PaperRequestedScale delta}
          (actualNearby :
            WZ2PaperPureNearbyScaleCoverData
              fine actualRequested ambientConstant)
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
              deletionExponent),
          Real.rpow delta (1 - outputLoss) ≤ callerRequested.1 →
          callerRequested.1 ≤ Real.rpow delta outputLoss →
            Nonempty (PostDeletionUniformScalarCore data) := by
  rcases
      exists_node3_uniform_twenty_four_scale
        outputLoss outputLossPos with
    ⟨delta₀, delta₀Pos, delta₀One, small⟩
  refine ⟨delta₀, delta₀Pos, delta₀One, ?_⟩
  intro delta deltaPos deltaBound
  intro fine ambientConstant fiberConstant coarseConstant
    actualRequested actualNearby callerRequested shading quotient support
    coordinateCount regularized merged scales scheduled sameFamily
    scaleSeparation balancing deletionExponent data
    callerLower callerUpper
  have callerPos : 0 < callerRequested.1 :=
    deltaPos.trans_le callerRequested.2.1
  rcases
      small delta deltaPos deltaBound callerRequested.1 callerPos
        callerLower callerUpper with
    ⟨rhoSmall, fiberRatioSmall⟩
  exact
    ⟨postDeletionUniformScalarCore
      data rhoSmall fiberRatioSmall⟩

end PureWZ2SameFamilyPositiveParentDeletionData

end Kakeya.Assouad

end
