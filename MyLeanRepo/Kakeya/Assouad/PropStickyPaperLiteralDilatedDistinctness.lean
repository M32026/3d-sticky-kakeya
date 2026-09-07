import MyLeanRepo.Kakeya.Assouad.PropStickyPaperLiteralDilatedDistinctnessStatements
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperDilatedLowerDistortion
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperLongitudinalCompressionLineDistance
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperLiteralMapRelation
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperCanonicalRescaledTube

/-!
# Target: distinctness after literal rescaling from a doubled anchor cover

Prove the pairwise lower-distortion estimate needed for the selected middle
family.  Do not alter the doubled-cover hypothesis or separation constant.

## Proof route

1. Construct historical target tubes via `wz2_paper_canonical_dilated_unit_rescaled_tube_from_geometry`
2. Show literal axis = longitudinal compression of historical axis via the map relation
3. Apply longitudinal compression monotonicity (`wz2_paper_longitudinal_compression_lineDistance`)
4. Apply dilated lower distortion (`wz1PaperUnitRescaling_dilated_source_lineDistance_le_target`)
5. Conclude from the frozen strong source separation that the literal target
   distance exceeds the scale needed for partitioning.
-/

noncomputable section

namespace Kakeya.Assouad

theorem wz2_paper_literal_dilated_strong_separation :
    WZ2PaperLiteralDilatedStrongSeparationStatement := by
  intro rho sigma hrho hrho_sigma hsigma hsigma_one
    sourceFirst sourceSecond anchor
    hsourceFirst hsourceSecond hanchor
    hcoverFirst hcoverSecond hsep
    targetFirst targetSecond
    htargetFirst htargetSecond
    haxisFirst haxisSecond

  -- Step 1: Construct historical target tubes
  have hhistoricalFirstData :
      Nonempty (WZ2PaperCanonicalUnitRescaledTubeData
        sourceFirst anchor hsigma) :=
    wz2_paper_canonical_dilated_unit_rescaled_tube_from_geometry
      hsigma hsigma_one
      sourceFirst anchor hsourceFirst hanchor hcoverFirst
  rcases hhistoricalFirstData with ⟨historicalFirstData⟩
  let historicalFirst := historicalFirstData.target

  have hhistoricalSecondData :
      Nonempty (WZ2PaperCanonicalUnitRescaledTubeData
        sourceSecond anchor hsigma) :=
    wz2_paper_canonical_dilated_unit_rescaled_tube_from_geometry
      hsigma hsigma_one
      sourceSecond anchor hsourceSecond hanchor hcoverSecond
  rcases hhistoricalSecondData with ⟨historicalSecondData⟩
  let historicalSecond := historicalSecondData.target

  have hhistoricalFirstLC :
      WZ1PaperTubeInLineClass historicalFirst :=
    historicalFirstData.target_line_class
  have hhistoricalSecondLC :
      WZ1PaperTubeInLineClass historicalSecond :=
    historicalSecondData.target_line_class
  have hhistoricalAxisFirst :
      tubeAxisLine historicalFirst =
        wz1PaperUnitRescalingMap anchor hsigma ''
          tubeAxisLine sourceFirst :=
    historicalFirstData.target_axis
  have hhistoricalAxisSecond :
      tubeAxisLine historicalSecond =
        wz1PaperUnitRescalingMap anchor hsigma ''
          tubeAxisLine sourceSecond :=
    historicalSecondData.target_axis

  -- Step 2: Literal axis = longitudinal compression of historical axis
  have hmapRelation :
      WZ2PaperLiteralMapCoordinateRelationStatement :=
    wz2_paper_literal_map_coordinate_relation
  have himageRelation :
      ∀ {rho : ℝ},
        ∀ (anchor : Kakeya.DeltaTube rho),
          ∀ (hrho : 0 < rho),
            ∀ (source : Set Point3),
              wz2PaperLiteralUnitRescalingMap anchor hrho '' source =
                wz2PaperLongitudinalCompression ''
                  (wz1PaperUnitRescalingMap anchor hrho '' source) :=
    wz2_paper_literal_map_image_relation hmapRelation
  have hliteralAxisFirst_compressed :
      wz2PaperLiteralUnitRescalingMap anchor hsigma ''
        tubeAxisLine sourceFirst =
      wz2PaperLongitudinalCompression ''
        (wz1PaperUnitRescalingMap anchor hsigma ''
          tubeAxisLine sourceFirst) :=
    himageRelation anchor hsigma (tubeAxisLine sourceFirst)
  have hliteralAxisSecond_compressed :
      wz2PaperLiteralUnitRescalingMap anchor hsigma ''
        tubeAxisLine sourceSecond =
      wz2PaperLongitudinalCompression ''
        (wz1PaperUnitRescalingMap anchor hsigma ''
          tubeAxisLine sourceSecond) :=
    himageRelation anchor hsigma (tubeAxisLine sourceSecond)

  have hcompressedAxisFirst :
      tubeAxisLine targetFirst =
        wz2PaperLongitudinalCompression ''
          tubeAxisLine historicalFirst := by
    rw [haxisFirst, hliteralAxisFirst_compressed,
      hhistoricalAxisFirst]
  have hcompressedAxisSecond :
      tubeAxisLine targetSecond =
        wz2PaperLongitudinalCompression ''
          tubeAxisLine historicalSecond := by
    rw [haxisSecond, hliteralAxisSecond_compressed,
      hhistoricalAxisSecond]

  -- Step 3: Longitudinal compression monotonicity
  have hcompression :
      wz1PaperLineDistance historicalFirst historicalSecond ≤
        wz1PaperLineDistance targetFirst targetSecond :=
    wz2_paper_longitudinal_compression_lineDistance
      (historicalScale := rho / sigma)
      (literalScale := rho / sigma)
      historicalFirst historicalSecond
      targetFirst targetSecond
      hhistoricalFirstLC hhistoricalSecondLC
      htargetFirst htargetSecond
      hcompressedAxisFirst hcompressedAxisSecond

  -- Step 4: Dilated lower distortion
  have hlower :
      wz1PaperLineDistance sourceFirst sourceSecond ≤
        7350 * sigma *
          wz1PaperLineDistance historicalFirst historicalSecond :=
    wz1PaperUnitRescaling_dilated_source_lineDistance_le_target
      (hrho := hsigma) (hrho_one := hsigma_one)
      (hcover₁ := hcoverFirst)
      (hcover₂ := hcoverSecond)
      hsourceFirst hsourceSecond
      hhistoricalFirstLC hhistoricalSecondLC
      hhistoricalAxisFirst hhistoricalAxisSecond

  -- Step 5: retain the literal doubled-fiber partitioning margin.
  have h2 :
      1600 * (rho / sigma) <
        wz1PaperLineDistance historicalFirst historicalSecond := by
    have h3 :
        wz2PaperLiteralSourceSeparationFactor * rho <
          7350 * sigma *
            wz1PaperLineDistance historicalFirst historicalSecond :=
      lt_of_lt_of_le hsep hlower
    have h4 :
        1600 * rho < sigma *
          wz1PaperLineDistance historicalFirst historicalSecond := by
      unfold wz2PaperLiteralSourceSeparationFactor at h3
      nlinarith
    have h5 :
        (1600 * rho) / sigma <
          wz1PaperLineDistance historicalFirst historicalSecond :=
      (div_lt_iff₀ hsigma).mpr <| by
        simpa [mul_comm] using h4
    simpa [div_eq_mul_inv, mul_assoc] using h5
  exact lt_of_lt_of_le h2 hcompression

end Kakeya.Assouad

end
