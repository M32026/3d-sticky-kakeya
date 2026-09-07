import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.AssemblyStatements
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ParameterBlockAmplificationStatement
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ParameterLocalFullBlockStatements

/-!
# Cinematic amplification of one full parameter block

Section 7 copies the complete projected shading attached to one local
parameter block.  It does not merely copy the finite set of parameter
centers.  The amplified center set supplies the cinematic Katz--Tao family,
while indexed four-parameter Frostman control bounds the number of copied
tube pieces assigned to one selected cinematic curve.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Assouad

/--
The arbitrary-fixed-constant half-parameter cinematic bridge needed after
parameter-block amplification.

The input constant is quantified before the PYZ loss and the small-scale
threshold.  Every point lies in the half parameter box, so its curve belongs
to the fixed extended cinematic family with absolute two-jet bound `40`.
-/
def HalfParameterCinematicPYZGeneralStatement : Prop :=
  ∀ inputConstant : ENNReal,
    1 ≤ inputConstant → inputConstant ≠ ⊤ →
      ∀ epsilon : ℝ, 0 < epsilon →
        ∃ threshold : ℝ,
          0 < threshold ∧ threshold ≤ 1 / 6000 ∧
          ∀ f : SlopeFunction,
            f.IsNonsingular → f 0 = 0 →
              ∀ fineScale : ℝ,
                0 < fineScale → fineScale ≤ threshold →
                  ∀ points : DiscreteSet 3,
                    points.IsKatzTao fineScale 1 inputConstant →
                    (∀ p ∈ points,
                      |p 0| ≤ 1 / 2 ∧
                        |p 1| ≤ 1 / 2 ∧
                        |p 2| ≤ 1 / 2) →
                    ∃ selected :
                        Kakeya.Cinematic.FiniteFunctionFamily,
                      selected.carrier ⊆
                          (halfParameterCinematicFamily f points).carrier ∧
                      IsCinematicDeltaSeparated selected fineScale ∧
                      (∀ g ∈
                          (halfParameterCinematicFamily f points).carrier,
                        ∃ h ∈ selected.carrier,
                          Kakeya.Cinematic.c2Distance g h ≤ fineScale) ∧
                      eLpNorm
                          (Kakeya.Cinematic.multiplicity selected
                            (6000 * fineScale))
                          (3 / 2 : ENNReal) volume ≤
                        ENNReal.ofReal
                          (Real.rpow fineScale (-epsilon))

/--
The copied-tube fiber cap used in the amplified Hölder estimate.

The factor is absolute.  The scale-dependent part is exactly the indexed
four-parameter Frostman quantity `C * delta² * #F`; there is no extra
cardinality ratio between the local block and the ambient center set.
-/
def parameterBlockCopiedFiberCap
    {delta : ℝ}
    (C : ENNReal)
    (F : Kakeya.Streamlined.TubeFamily delta) :
    ENNReal :=
  1000000000000 * C *
    Kakeya.realRpowENN delta 2 * F.enncard

/--
The local source shading recovered after applying PYZ to all translated
copies and dividing by the number of copies.
-/
structure ParameterBlockCinematicPullbackData
    {delta epsilon : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    {C lambda : ENNReal}
    {clustered :
      TubeParameterClusterFrostmanData F Y C lambda delta}
    (localBlock : ParameterLocalFullBlockData clustered epsilon)
    (amplification :
      ParameterBlockAmplificationData
        delta localBlock.blockScale
        (1 - 20 * epsilon ^ 2) localBlock.centeredPoints)
    (f : SlopeFunction)
    (pyzLoss : ℝ) where
  shading :
    Kakeya.Streamlined.TubeShading
      (parameterLocalBlockFamily clustered localBlock.sourcePoints)
  subshading :
    IsSubshading shading
      (parameterLocalBlockShading clustered localBlock.sourcePoints)
  half_local_mass :
    (1 / 2 : ENNReal) *
        (parameterLocalBlockShading
          clustered localBlock.sourcePoints).mass ≤
      shading.mass
  volume_lower :
    volume (twistedUnion shading f) ≥
      (((amplification.translations.enncard * shading.mass /
            ENNReal.ofReal (20 * delta)) /
          (parameterBlockCopiedFiberCap C F *
            ENNReal.ofReal
              (Real.rpow delta (-pyzLoss)))) ^ 3) /
        amplification.translations.enncard

/--
Apply the cinematic estimate to the translated copies of one full local
block, then pull the area bound back to that source block.

The proof must:

1. compactly regularize the actual local source shading;
2. copy every projected tube piece for every translation;
3. assign copied pieces to a separated subfamily of the amplified
   half-parameter cinematic family;
4. obtain the copied-tube fiber cap from the original indexed
   four-parameter Frostman hypothesis;
5. apply Hölder and PYZ to the amplified projected union; and
6. use `volume_biUnion_fiberwiseTranslate_le` to divide by the number of
   translated copies.

It may not replace the copied shading by synthetic unrelated tubes or lose
the ratio between the local block and the full center set.
-/
def ParameterBlockCinematicPullbackStatement : Prop :=
  HalfParameterCinematicPYZGeneralStatement →
    CompactSubshadingSelectionStatement →
      CompactTubeTwistedProjectionAreaStatement →
        AssignedCurveProjectionContainmentFromVerticalChartStatement →
          ∀ epsilon pyzLoss : ℝ,
            0 < epsilon → epsilon < 1 / 10 →
            0 < pyzLoss →
              ∃ threshold : ℝ,
                0 < threshold ∧ threshold < 1 ∧
                ∀ delta : ℝ,
                  0 < delta → delta ≤ threshold →
                    ∀ F : Kakeya.Streamlined.TubeFamily delta,
                      IsInVerticalChart F →
                      ∀ Y : Kakeya.Streamlined.TubeShading F,
                        ∀ C lambda : ENNReal,
                          C ≠ ⊤ →
                          TubeParameterFrostmanBound F C →
                          ∀ clustered :
                              TubeParameterClusterFrostmanData
                                F Y C lambda delta,
                            clustered.shading.union ⊆
                                horizontalSlab 0 1 →
                            ∀ localBlock :
                                ParameterLocalFullBlockData
                                  clustered epsilon,
                              ∀ amplification :
                                  ParameterBlockAmplificationData
                                    delta localBlock.blockScale
                                    (1 - 20 * epsilon ^ 2)
                                    localBlock.centeredPoints,
                                ∀ f : SlopeFunction,
                                  f.IsNonsingular → f 0 = 0 →
                                    Nonempty
                                      (ParameterBlockCinematicPullbackData
                                        localBlock amplification f pyzLoss)

end Kakeya.Assouad
