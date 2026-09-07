import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62PaperAudit.StatementsV4

/-!
# Fixed-grid boundary removal

Closed concept module for the fixed-grid input used by the reusable
Proposition 6.2 kernel.
-/

namespace Kakeya.Assouad.Prop62PaperAudit.V4

open MeasureTheory

theorem fixed_grid_boundary_removal :
    FixedGridBoundaryRemovalStatement := by
  let gridConstant : ENNReal :=
    15 * pureWZ2Prop62FixedGridPlaneConstant
  let outerConstant : ENNReal :=
    6 * pureWZ2Prop62OuterFaceConstant
  refine ⟨gridConstant, outerConstant, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp only [gridConstant, pureWZ2Prop62FixedGridPlaneConstant,
      pureWZ2Prop62FixedGridSlowConstant,
      pureWZ2Prop62FixedGridBandConstant]
    positivity
  · dsimp only [gridConstant, pureWZ2Prop62FixedGridPlaneConstant,
      pureWZ2Prop62FixedGridSlowConstant,
      pureWZ2Prop62FixedGridBandConstant]
    exact ENNReal.mul_ne_top (by norm_num) <|
      ENNReal.add_ne_top.mpr
        ⟨ENNReal.mul_ne_top (by norm_num)
            Kakeya.Assouad.deltaTubeVolume_one_ne_top,
          by norm_num⟩
  · dsimp only [outerConstant, pureWZ2Prop62OuterFaceConstant,
      pureWZ2Prop62OuterSlowConstant,
      pureWZ2Prop62OuterBandConstant]
    positivity
  · dsimp only [outerConstant, pureWZ2Prop62OuterFaceConstant,
      pureWZ2Prop62OuterSlowConstant,
      pureWZ2Prop62OuterBandConstant]
    exact ENNReal.mul_ne_top (by norm_num) <|
      ENNReal.add_ne_top.mpr
        ⟨ENNReal.mul_ne_top (by norm_num)
            Kakeya.Assouad.deltaTubeVolume_one_ne_top,
          by norm_num⟩
  · intro delta rho hdelta hdeltaSmall hrho hrhoOne hdeltaRho
      family hline shading hcubical constant _hconstant hcwa
    let fullShading : WZ1PaperTubeShading family :=
      { carrier := fun index =>
          wz1PaperTubeCarrier (family.tube index)
        measurable_carrier := fun index =>
          wz1PaperTubeCarrier_measurable (family.tube index)
        subset_body := fun _ => Set.Subset.rfl }
    have hsmallTwentyFour : delta ≤ 1 / 24 := by
      linarith
    have hgrid :=
      pureWZ2_prop62_grid_boundary_mass
        hdelta hsmallTwentyFour hrho hrhoOne hline fullShading hcwa
    have houter :=
      pureWZ2_prop62_outer_boundary_mass
        hdelta hsmallTwentyFour hrho hrhoOne hdeltaRho
        hline fullShading hcwa
    have hinverse :
        1 / rho ≤ 1 / delta :=
      one_div_le_one_div_of_le hdelta hdeltaRho
    have hlog :
        Real.log (1 / rho) ≤ Real.log (1 / delta) :=
      Real.log_le_log (by positivity) hinverse
    have hquotient :
        Real.log (1 / rho) / Real.log 2 ≤
          Real.log (1 / delta) / Real.log 2 := by
      exact
        (div_le_div_iff_of_pos_right
          (Real.log_pos (by norm_num : (1 : ℝ) < 2))).2 hlog
    have hlevelNat :
        pureWZ2Prop62OuterDirectionLevelCount rho ≤
          pureWZ2Prop62DirectionLevelCount delta := by
      unfold pureWZ2Prop62OuterDirectionLevelCount
        pureWZ2Prop62DirectionLevelCount
      gcongr
    have hlevel :
        (pureWZ2Prop62OuterDirectionLevelCount rho : ENNReal) ≤
          logarithmicLoss delta := by
      change
        (pureWZ2Prop62OuterDirectionLevelCount rho : ENNReal) ≤
          (pureWZ2Prop62DirectionLevelCount delta : ENNReal)
      exact_mod_cast hlevelNat
    dsimp only [gridBoundaryBadSet, outerBoundaryBadSet,
      logarithmicLoss]
    refine ⟨?_, ?_, ?_⟩
    · simpa [fullShading, gridConstant, mul_assoc, mul_left_comm,
        mul_comm] using hgrid
    · calc
        (∑ source : Fin family.card,
            volume
              (wz1PaperTubeCarrier (family.tube source) ∩
                wz2PaperCropBoundaryRegion rho)) ≤
            6 * constant *
              (pureWZ2Prop62OuterDirectionLevelCount rho : ENNReal) *
              pureWZ2Prop62OuterFaceConstant *
              ENNReal.ofReal rho *
              (wz1PaperBodyFamily family).mass := by
                simpa [fullShading] using houter
        _ ≤
            6 * constant *
              (pureWZ2Prop62DirectionLevelCount delta : ENNReal) *
              pureWZ2Prop62OuterFaceConstant *
              ENNReal.ofReal rho *
              (wz1PaperBodyFamily family).mass := by
                gcongr
        _ =
            outerConstant * constant *
              ENNReal.ofReal rho *
              (pureWZ2Prop62DirectionLevelCount delta : ENNReal) *
              (wz1PaperBodyFamily family).mass := by
              dsimp only [outerConstant]
              ring
    · intro hsmall
      apply pureWZ2_prop62_fixed_grid_cleanup
        hdelta hsmallTwentyFour hrho hrhoOne hdeltaRho
        hline shading hcubical hcwa
      calc
        (15 : ENNReal) * constant *
                (pureWZ2Prop62DirectionLevelCount delta : ENNReal) *
                pureWZ2Prop62FixedGridPlaneConstant *
                ENNReal.ofReal (delta / rho) *
                (wz1PaperBodyFamily family).mass +
              6 * constant *
                (pureWZ2Prop62OuterDirectionLevelCount rho : ENNReal) *
                pureWZ2Prop62OuterFaceConstant *
                ENNReal.ofReal rho *
                (wz1PaperBodyFamily family).mass ≤
            gridConstant * constant *
                (pureWZ2Prop62DirectionLevelCount delta : ENNReal) *
                ENNReal.ofReal (delta / rho) *
                (wz1PaperBodyFamily family).mass +
              outerConstant * constant *
                (pureWZ2Prop62DirectionLevelCount delta : ENNReal) *
                ENNReal.ofReal rho *
                (wz1PaperBodyFamily family).mass := by
          apply add_le_add
          · dsimp only [gridConstant]
            exact le_of_eq (by ring)
          · calc
              6 * constant *
                    (pureWZ2Prop62OuterDirectionLevelCount rho :
                      ENNReal) *
                    pureWZ2Prop62OuterFaceConstant *
                    ENNReal.ofReal rho *
                    (wz1PaperBodyFamily family).mass ≤
                  6 * constant *
                    (pureWZ2Prop62DirectionLevelCount delta : ENNReal) *
                    pureWZ2Prop62OuterFaceConstant *
                    ENNReal.ofReal rho *
                    (wz1PaperBodyFamily family).mass := by
                      gcongr
              _ =
                  outerConstant * constant *
                    (pureWZ2Prop62DirectionLevelCount delta : ENNReal) *
                    ENNReal.ofReal rho *
                    (wz1PaperBodyFamily family).mass := by
                    dsimp only [outerConstant]
                    ring
        _ =
            gridConstant * constant * ENNReal.ofReal (delta / rho) *
                (pureWZ2Prop62DirectionLevelCount delta : ENNReal) *
                (wz1PaperBodyFamily family).mass +
              outerConstant * constant * ENNReal.ofReal rho *
                (pureWZ2Prop62DirectionLevelCount delta : ENNReal) *
                (wz1PaperBodyFamily family).mass := by ring
        _ ≤ shading.mass / 2 := hsmall

end Kakeya.Assouad.Prop62PaperAudit.V4
