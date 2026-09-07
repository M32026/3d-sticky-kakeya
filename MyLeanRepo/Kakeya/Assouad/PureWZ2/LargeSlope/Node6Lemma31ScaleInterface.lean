import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.FrameNormalCompatibilityCore
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.FaithfulStep4Witness
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.Section6ScaleData

/-!
# Minimal Node-6 source for the Lemma 31 contradiction

This record is the common boundary between a Section-6 source construction
and the paper's Lemma 31 contradiction.  It deliberately contains only the
fields used after the power-scale slab has been selected.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

structure PureWZ2Lemma31ScaleAssembly
    (sigma epsilon delta : ℝ) where
  eta : ℝ
  eta_pos : 0 < eta
  eta_budget : 1000 * eta ≤ epsilon * sigma ^ 2
  targetLoss : ℝ
  targetLoss_eq : targetLoss = eta / 8
  stickyLoss : ℝ
  stickyLoss_eq : stickyLoss = eta / 4096
  sourceLoss : ℝ
  sourceLoss_pos : 0 < sourceLoss
  sourceLoss_le_stickyLoss : sourceLoss ≤ stickyLoss
  cfg : PureWZ2C2GrainConfiguration sigma targetLoss delta
  cfg_bounded_base : HasBoundedBase cfg.family 4
  rho : WZ2PaperRequestedScale delta
  rho_eq_power : rho.1 = Real.rpow delta epsilon
  globalSlope : SlopeFunction
  globalSlope_eq_on : ∀ z ∈ Set.Icc (-1 : ℝ) 1,
    globalSlope z = cfg.globalGrains.slope z
  globalSlope_normalized : globalSlope.IsNormalized
  scaleData : PureWZ2Section6ScaleData
    cfg.shading sigma targetLoss rho
  frameNormalCompatibility : PureWZ2FrameNormalCompatibility cfg
  faithful_overload : ∀ a b : ℝ, b - a ≤ Real.rpow delta epsilon →
    ∀ step4 : LargeSlopeFaithfulStep4Witness cfg.family sigma eta a b,
      ∃ W : Set Point3, Convex ℝ W ∧
        Kakeya.realRpowENN delta (-eta) * volume W *
            cfg.family.enncard <
          (wz1PaperBodyFamily cfg.family).containedCount W
  pointMultiplicity_upper : ∀ point,
    (scaleData.slabShading.pointMultiplicity point : ENNReal) ≤
      (Kakeya.realRpowENN delta (2 - sigma - stickyLoss) *
        Kakeya.realRpowENN rho.1 (-stickyLoss)) *
          cfg.family.enncard

end Kakeya.Assouad

end
