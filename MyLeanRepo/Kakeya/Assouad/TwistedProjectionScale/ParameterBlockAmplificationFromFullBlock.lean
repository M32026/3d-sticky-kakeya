import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ParameterBlockAmplificationStatement
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ParameterLocalFullBlockStatements

/-!
# Apply amplification to a full local block
-/

noncomputable section

namespace Kakeya.Assouad

lemma parameterBlockAmplification_from_fullBlock
    (hAmplification : ParameterBlockAmplificationStatement)
    {delta epsilon : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    {C lambda : ENNReal}
    {clustered :
      TubeParameterClusterFrostmanData
        F Y C lambda delta}
    (localBlock :
      ParameterLocalFullBlockData clustered epsilon)
    (hdelta : 0 < delta)
    (hepsilon : 0 < epsilon)
    (hepsilon_small : epsilon < 1 / 10) :
    Nonempty
      (ParameterBlockAmplificationData
        delta localBlock.blockScale
        (1 - 20 * epsilon ^ 2)
        localBlock.centeredPoints) := by
  have hkt_pos : 0 < 1 - epsilon ^ 2 := by
    nlinarith [sq_nonneg epsilon]
  have hkt_one : 1 - epsilon ^ 2 ≤ 1 := by
    nlinarith [sq_nonneg epsilon]
  have hcard_pos : 0 < 1 - 20 * epsilon ^ 2 := by
    have heps_sq : epsilon ^ 2 < 1 / 100 := by
      nlinarith
    nlinarith
  have hcard_kt :
      1 - 20 * epsilon ^ 2 ≤
        1 - epsilon ^ 2 := by
    nlinarith [sq_nonneg epsilon]
  exact hAmplification
    delta localBlock.blockScale
    (1 - epsilon ^ 2)
    (1 - 20 * epsilon ^ 2)
    hdelta localBlock.fine_le_block
    localBlock.blockScale_small
    hkt_pos hkt_one hcard_pos hcard_kt
    0 (by simp)
    localBlock.centeredPoints
    localBlock.centeredPoints_nonempty
    localBlock.centered_containment
    localBlock.local_katzTao
    localBlock.local_cardinality

end Kakeya.Assouad
