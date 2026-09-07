import MyLeanRepo.Kakeya.Assouad.PureWZ2.Critical
import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12CroppedExtremal
import MyLeanRepo.Kakeya.Assouad.AbsorptionHelpers

/-!
# Ordinary-to-cropped critical-floor bridge

The pure critical package controls ordinary unit-segment shadings.  Section 6
uses cubical shadings inside cropped full-line carriers.  The remaining model
conversion is isolated below: replace one cropped configuration by an
ordinary pure configuration at the same scale and constants, without
increasing union volume.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

structure PureWZ2CroppedFloorReductionData
    {delta : ℝ}
    (croppedFamily : Kakeya.Streamlined.TubeFamily delta)
    (croppedShading : WZ1PaperTubeShading croppedFamily)
    (lossConstant cwaConstant densityConstant : ENNReal) where
  ordinaryFamily : Kakeya.Streamlined.TubeFamily delta
  ordinaryShading :
    Kakeya.Streamlined.TubeShading ordinaryFamily
  ordinary_nonempty : ordinaryFamily.Nonempty
  ordinary_cwa :
    WZ2PaperPureCWAAtNearbyScales
      ordinaryFamily (lossConstant * cwaConstant)
  ordinary_dense :
    ordinaryShading.IsLambdaDense
      (lossConstant⁻¹ * densityConstant)
  ordinary_union_volume_le :
    volume ordinaryShading.union ≤
      volume croppedShading.union

def PureWZ2CroppedFloorReductionStatement : Prop :=
  ∃ lossConstant : ENNReal,
    1 ≤ lossConstant ∧
    lossConstant ≠ ⊤ ∧
    ∀ {delta : ℝ},
      0 < delta →
      delta ≤ 1 →
      ∀ {family : Kakeya.Streamlined.TubeFamily delta},
        family.Nonempty →
        ∀ (shading : WZ1PaperTubeShading family),
          WZ1PaperIsCubicalShading shading →
          ∀ cwaConstant densityConstant : ENNReal,
            WZ2PaperPureCWAAtNearbyScales family cwaConstant →
            shading.IsLambdaDense densityConstant →
              Nonempty
                (PureWZ2CroppedFloorReductionData
                  family shading lossConstant
                  cwaConstant densityConstant)

theorem PureWZ2CriticalPackage.cropped_critical_floor_of_reduction
    {sigma : ℝ}
    (critical : PureWZ2CriticalPackage sigma)
    (reduction : PureWZ2CroppedFloorReductionStatement) :
    HasWZ2PaperCroppedCriticalVolumeFloor sigma := by
  rcases reduction with
    ⟨lossConstant, lossConstant_one,
      lossConstant_top, reduce⟩
  intro floorLoss structuralBudget
    floorLossPos structuralBudgetPos
  rcases
      critical.critical_floor
        floorLoss structuralBudget
        floorLossPos structuralBudgetPos
    with
    ⟨ordinaryLoss, ordinaryDelta₀,
      ordinaryLossPos, ordinaryLossLe,
      ordinaryDelta₀Pos, ordinaryDelta₀One, ordinaryFloor⟩
  let croppedLoss := ordinaryLoss / 2
  have croppedLossPos : 0 < croppedLoss := by
    dsimp only [croppedLoss]
    positivity
  have croppedLossLe : croppedLoss ≤ structuralBudget := by
    dsimp only [croppedLoss]
    exact (by linarith : ordinaryLoss / 2 ≤ ordinaryLoss).trans
      ordinaryLossLe
  let gap := ordinaryLoss - croppedLoss
  have gapPos : 0 < gap := by
    dsimp only [gap, croppedLoss]
    linarith
  rcases
      exists_delta_realRpowENN_bound
        lossConstant lossConstant_top gapPos
    with
    ⟨absorptionDelta₀, absorptionDelta₀Pos,
      absorptionDelta₀One, absorb⟩
  let delta₀ := min ordinaryDelta₀ absorptionDelta₀
  have delta₀Pos : 0 < delta₀ := by
    exact lt_min ordinaryDelta₀Pos absorptionDelta₀Pos
  have delta₀One : delta₀ ≤ 1 := by
    exact (min_le_left _ _).trans ordinaryDelta₀One
  refine
    ⟨croppedLoss, delta₀,
      croppedLossPos, croppedLossLe,
      delta₀Pos, delta₀One, ?_⟩
  intro delta deltaPos deltaLe family familyNonempty
    shading pureCWA cubical dense
  have ordinaryDeltaLe : delta ≤ ordinaryDelta₀ :=
    deltaLe.trans (min_le_left _ _)
  have absorptionDeltaLe : delta ≤ absorptionDelta₀ :=
    deltaLe.trans (min_le_right _ _)
  have deltaOne : delta ≤ 1 := deltaLe.trans delta₀One
  let reduced :=
    Classical.choice <|
      reduce deltaPos deltaOne familyNonempty
        shading cubical
        (Kakeya.realRpowENN delta (-croppedLoss))
        (Kakeya.realRpowENN delta croppedLoss)
        pureCWA dense
  have lossAbsorption :
      lossConstant ≤
        Kakeya.realRpowENN delta (-gap) :=
    absorb delta deltaPos absorptionDeltaLe
  have cwaAbsorption :
      lossConstant *
          Kakeya.realRpowENN delta (-croppedLoss) ≤
        Kakeya.realRpowENN delta (-ordinaryLoss) := by
    calc
      lossConstant *
            Kakeya.realRpowENN delta (-croppedLoss) ≤
          Kakeya.realRpowENN delta (-gap) *
            Kakeya.realRpowENN delta (-croppedLoss) := by
        gcongr
      _ =
          Kakeya.realRpowENN delta
            ((-gap) + (-croppedLoss)) := by
        rw [realRpowENN_add deltaPos]
      _ =
          Kakeya.realRpowENN delta (-ordinaryLoss) := by
        congr 2
        dsimp only [gap, croppedLoss]
        ring
  have densityAbsorption :
      Kakeya.realRpowENN delta ordinaryLoss ≤
        lossConstant⁻¹ *
          Kakeya.realRpowENN delta croppedLoss := by
    have lossConstant_zero : lossConstant ≠ 0 := by
      exact (zero_lt_one.trans_le lossConstant_one).ne'
    have scaled :
        lossConstant *
            Kakeya.realRpowENN delta ordinaryLoss ≤
          lossConstant *
            (lossConstant⁻¹ *
              Kakeya.realRpowENN delta croppedLoss) := by
      calc
        lossConstant *
              Kakeya.realRpowENN delta ordinaryLoss ≤
          Kakeya.realRpowENN delta (-gap) *
            Kakeya.realRpowENN delta ordinaryLoss := by
          gcongr
        _ =
          Kakeya.realRpowENN delta
            ((-gap) + ordinaryLoss) := by
          rw [realRpowENN_add deltaPos]
        _ =
          Kakeya.realRpowENN delta croppedLoss := by
          congr 2
          dsimp only [gap]
          ring
        _ =
            lossConstant *
              (lossConstant⁻¹ *
                Kakeya.realRpowENN delta croppedLoss) := by
          rw [← mul_assoc,
            ENNReal.mul_inv_cancel
              lossConstant_zero lossConstant_top,
            one_mul]
    apply
      (ENNReal.mul_le_mul_iff_left
        lossConstant_zero lossConstant_top).mp
    simpa [mul_comm] using scaled
  have ordinaryCWA :
      WZ2PaperPureCWAAtNearbyScales
        reduced.ordinaryFamily
        (Kakeya.realRpowENN delta (-ordinaryLoss)) :=
    reduced.ordinary_cwa.mono
      cwaAbsorption (by simp [Kakeya.realRpowENN])
  have ordinaryDense :
      reduced.ordinaryShading.IsLambdaDense
        (Kakeya.realRpowENN delta ordinaryLoss) := by
    exact
      (mul_le_mul_right'
        densityAbsorption
        reduced.ordinaryFamily.toBodyFamily.mass).trans
        reduced.ordinary_dense
  exact
    (ordinaryFloor delta deltaPos ordinaryDeltaLe
      reduced.ordinaryFamily reduced.ordinary_nonempty
      reduced.ordinaryShading ordinaryCWA
      ordinaryDense).trans
      reduced.ordinary_union_volume_le

end Kakeya.Assouad

end
