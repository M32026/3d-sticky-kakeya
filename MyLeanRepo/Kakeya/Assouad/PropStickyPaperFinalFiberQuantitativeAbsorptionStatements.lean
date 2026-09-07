import MyLeanRepo.Kakeya.Assouad.Definitions

/-!
# Final quantitative absorption for the paper fibers

The last paragraph of the proof of `prop: sticky` first obtains the lower
power bounds for the common fine multiplicity and the final fiber density.
Only after those paper bounds are fixed are the absolute tube-volume
constants absorbed by taking the scale sufficiently small.

This module records that numerical boundary without carrying any of the
finite parent-selection data.
-/

noncomputable section

namespace Kakeya.Assouad

structure WZ2PaperFinalFiberGeometricAbsorptionData
    (floorLoss strongLoss : ℝ) where
  delta₀ : ℝ
  delta₀_pos : 0 < delta₀
  delta₀_le_one : delta₀ ≤ 1
  absorb :
    ∀ scale : ℝ, 0 < scale → scale ≤ delta₀ →
      55296 * Kakeya.deltaTubeVolume 1 ≤
        Kakeya.realRpowENN scale (-(strongLoss - floorLoss))

structure WZ2PaperFinalFiberQuantitativeAbsorptionData
    (scale sigma floorLoss strongLoss : ℝ)
    (sourceDensity multiplicityFloor targetCardinality : ENNReal) where
  density_absorb :
    Kakeya.realRpowENN scale strongLoss *
          (55296 * Kakeya.deltaTubeVolume 1) ≤
      ENNReal.ofReal ((1 / 100 : ℝ) ^ 3) * sourceDensity
  volume_absorb :
    (55296 * Kakeya.deltaTubeVolume 1) *
          Kakeya.realRpowENN scale 2 * targetCardinality ≤
      multiplicityFloor *
        Kakeya.realRpowENN scale (sigma - strongLoss)

structure WZ2PaperFinalFiberPowerFloorData
    {Parent : Type}
    (scale sigma floorLoss : ℝ)
    (sourceDensity multiplicityFloor targetCardinality :
      Parent → ENNReal) where
  /--
  Paper input corresponding to the density part of extremality after unit
  rescaling.
  -/
  density_floor :
    ∀ parent,
      Kakeya.realRpowENN scale floorLoss ≤
        ENNReal.ofReal ((1 / 100 : ℝ) ^ 3) *
          sourceDensity parent
  /--
  Literal fine-multiplicity lower bound from the final display in the proof:

  “`(delta/rho)^(2-sigma+epsilon/10) (# T'[T]) ≤ mu_fine`.”
  -/
  multiplicity_floor :
    ∀ parent,
      Kakeya.realRpowENN scale (2 - sigma + floorLoss) *
          targetCardinality parent ≤
        multiplicityFloor parent

structure WZ2PaperFinalFiberQuantitativeAbsorptionFamilyData
    {Parent : Type}
    (scale sigma floorLoss strongLoss : ℝ)
    (sourceDensity multiplicityFloor targetCardinality :
      Parent → ENNReal) where
  fiber :
    ∀ parent,
      WZ2PaperFinalFiberQuantitativeAbsorptionData
        scale sigma floorLoss strongLoss
        (sourceDensity parent)
        (multiplicityFloor parent)
        (targetCardinality parent)

def WZ2PaperFinalFiberGeometricAbsorptionStatement : Prop :=
  ∀ floorLoss strongLoss : ℝ,
    floorLoss < strongLoss →
      Nonempty
        (WZ2PaperFinalFiberGeometricAbsorptionData
          floorLoss strongLoss)

def WZ2PaperFinalFiberQuantitativeAbsorptionStatement : Prop :=
  ∀ {scale sigma floorLoss strongLoss : ℝ},
    0 < scale →
    ∀ (geometric :
        WZ2PaperFinalFiberGeometricAbsorptionData
          floorLoss strongLoss),
      scale ≤ geometric.delta₀ →
      ∀ sourceDensity multiplicityFloor targetCardinality : ENNReal,
        Kakeya.realRpowENN scale floorLoss ≤
            ENNReal.ofReal ((1 / 100 : ℝ) ^ 3) * sourceDensity →
        Kakeya.realRpowENN scale (2 - sigma + floorLoss) *
              targetCardinality ≤
            multiplicityFloor →
        Nonempty
          (WZ2PaperFinalFiberQuantitativeAbsorptionData
            scale sigma floorLoss strongLoss
            sourceDensity multiplicityFloor targetCardinality)

def WZ2PaperFinalFiberQuantitativeAbsorptionFamilyStatement : Prop :=
  ∀ {Parent : Type},
    ∀ {scale sigma floorLoss strongLoss : ℝ},
      0 < scale →
      ∀ (geometric :
          WZ2PaperFinalFiberGeometricAbsorptionData
            floorLoss strongLoss),
        scale ≤ geometric.delta₀ →
        ∀ (sourceDensity multiplicityFloor targetCardinality :
            Parent → ENNReal),
          WZ2PaperFinalFiberPowerFloorData
              scale sigma floorLoss
              sourceDensity multiplicityFloor targetCardinality →
          Nonempty
            (WZ2PaperFinalFiberQuantitativeAbsorptionFamilyData
              scale sigma floorLoss strongLoss
              sourceDensity multiplicityFloor targetCardinality)

end Kakeya.Assouad

end
