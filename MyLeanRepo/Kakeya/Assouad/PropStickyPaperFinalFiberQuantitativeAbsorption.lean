import MyLeanRepo.Kakeya.Assouad.PropStickyPaperFinalFiberQuantitativeAbsorptionStatements
import MyLeanRepo.Kakeya.Assouad.AbsorptionHelpers

/-! # Absorb the final fixed geometric fiber constant -/

noncomputable section

namespace Kakeya.Assouad

theorem wz2_paper_final_fiber_geometric_absorption :
    WZ2PaperFinalFiberGeometricAbsorptionStatement := by
  intro floorLoss strongLoss hgap
  rcases
      exists_delta_realRpowENN_bound
        (55296 * Kakeya.deltaTubeVolume 1)
        (ENNReal.mul_ne_top
          (ENNReal.natCast_ne_top 55296)
          deltaTubeVolume_one_ne_top)
        (show 0 < strongLoss - floorLoss by linarith)
    with ⟨delta₀, hdelta₀, hdelta₀One, hAbsorb⟩
  exact
    ⟨{
      delta₀ := delta₀
      delta₀_pos := hdelta₀
      delta₀_le_one := hdelta₀One
      absorb := hAbsorb
    }⟩

theorem wz2_paper_final_fiber_quantitative_absorption :
    WZ2PaperFinalFiberQuantitativeAbsorptionStatement := by
  intro scale sigma floorLoss strongLoss hscale geometric hscaleBound
    sourceDensity multiplicityFloor targetCardinality
    hDensityFloor hMultiplicityFloor
  have hGeometry :=
    geometric.absorb scale hscale hscaleBound
  have hDensity :
      Kakeya.realRpowENN scale strongLoss *
            (55296 * Kakeya.deltaTubeVolume 1) ≤
        ENNReal.ofReal ((1 / 100 : ℝ) ^ 3) * sourceDensity := by
    calc
      Kakeya.realRpowENN scale strongLoss *
            (55296 * Kakeya.deltaTubeVolume 1) ≤
          Kakeya.realRpowENN scale strongLoss *
            Kakeya.realRpowENN scale
              (-(strongLoss - floorLoss)) := by
        gcongr
      _ = Kakeya.realRpowENN scale floorLoss := by
        rw [← realRpowENN_add hscale]
        congr 2
        ring
      _ ≤
          ENNReal.ofReal ((1 / 100 : ℝ) ^ 3) * sourceDensity :=
        hDensityFloor
  have hVolume :
      (55296 * Kakeya.deltaTubeVolume 1) *
            Kakeya.realRpowENN scale 2 * targetCardinality ≤
        multiplicityFloor *
          Kakeya.realRpowENN scale (sigma - strongLoss) := by
    calc
      (55296 * Kakeya.deltaTubeVolume 1) *
            Kakeya.realRpowENN scale 2 * targetCardinality ≤
          Kakeya.realRpowENN scale (-(strongLoss - floorLoss)) *
            Kakeya.realRpowENN scale 2 * targetCardinality := by
        gcongr
      _ =
          Kakeya.realRpowENN scale (2 - strongLoss + floorLoss) *
            targetCardinality := by
        rw [← realRpowENN_add hscale]
        congr 2
        ring
      _ =
          (Kakeya.realRpowENN scale (2 - sigma + floorLoss) *
              targetCardinality) *
            Kakeya.realRpowENN scale (sigma - strongLoss) := by
        calc
          Kakeya.realRpowENN scale (2 - strongLoss + floorLoss) *
                targetCardinality =
              (Kakeya.realRpowENN scale
                    (2 - sigma + floorLoss) *
                  Kakeya.realRpowENN scale
                    (sigma - strongLoss)) *
                targetCardinality := by
            rw [← realRpowENN_add hscale]
            congr 2
            ring
          _ =
              (Kakeya.realRpowENN scale
                    (2 - sigma + floorLoss) *
                  targetCardinality) *
                Kakeya.realRpowENN scale
                  (sigma - strongLoss) := by
            ring
      _ ≤
          multiplicityFloor *
            Kakeya.realRpowENN scale (sigma - strongLoss) := by
        gcongr
  exact
    ⟨{
      density_absorb := hDensity
      volume_absorb := hVolume
    }⟩

theorem wz2_paper_final_fiber_quantitative_absorption_family :
    WZ2PaperFinalFiberQuantitativeAbsorptionFamilyStatement := by
  intro Parent scale sigma floorLoss strongLoss hscale
    geometric hscaleBound sourceDensity multiplicityFloor
    targetCardinality powerFloor
  refine
    ⟨{
      fiber := ?_
    }⟩
  intro parent
  exact
    Classical.choice <|
      wz2_paper_final_fiber_quantitative_absorption
        hscale geometric hscaleBound
        (sourceDensity parent)
        (multiplicityFloor parent)
        (targetCardinality parent)
        (powerFloor.density_floor parent)
        (powerFloor.multiplicity_floor parent)

end Kakeya.Assouad

end
