import MyLeanRepo.Kakeya.Assouad.PureWZ2.NestedSameAxisJohnCWA

/-!
# Pure nearby CWA on one complete actual fiber

Fix one actual Definition 2.12 witness and one complete strict parent fiber.
For a requested scale:

* above the actual scale, use a singleton same-axis coarser parent and
  transport the actual-John fiber CWA;
* below the actual scale with the tree gap, restrict the ambient requested
  witness to the complete actual fiber;
* in the narrow transition range, reuse the actual singleton scale.

All three branches refer to the same complete selected family.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

/--
The complete strict fiber over one actual parent satisfies literal pure
Definition 2.12 at every nearby scale.
-/
theorem pureWZ2_completeFiber_pureNearby
    {delta actual : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientC outputC : ENNReal}
    (ambient :
      WZ2PaperPureCWAAtNearbyScales fine ambientC)
    (fineNonempty : fine.Nonempty)
    (actualScale :
      WZ2PaperPureScaleCoverData fine actual ambientC)
    (parent : Fin actualScale.coarse.card)
    (deltaActual : delta ≤ actual)
    (actualLeOne : actual ≤ 1)
    (outputOne : 1 ≤ outputC)
    (outputTop : outputC ≠ ⊤)
    (fourAmbientLtOutput :
      (4 : ENNReal) * ambientC < outputC)
    (ambientLeOutput : ambientC ≤ outputC)
    (coarserAbsorption :
      ∀ coarser : ℝ,
        actual ≤ coarser →
        coarser ≤ 1 →
          ENNReal.ofReal (81 * (coarser / actual) ^ 2) * ambientC ≤
            outputC) :
    WZ2PaperPureCWAAtNearbyScales
      (PureWZ2CompleteParentRestrictionData.pureWZ2CompleteParentRestriction
        actualScale.cover
        ({parent} : Finset (Fin actualScale.coarse.card))
        (Finset.singleton_nonempty parent)).selectedFine.family
      outputC := by
  let complete :=
    PureWZ2CompleteParentRestrictionData.pureWZ2CompleteParentRestriction
      actualScale.cover
      ({parent} : Finset (Fin actualScale.coarse.card))
      (Finset.singleton_nonempty parent)
  have selectedNonempty :
      complete.selectedFine.family.Nonempty := by
    have ambientFiber :=
      actualScale.cover.fullFiber_nonempty_of_uniform
        fineNonempty
        actualScale.full_fiber_uniform parent
    change 0 < complete.selectedFineIndices.card
    rw [pureWZ2_singletonComplete_selectedFineIndices
      actualScale.cover actualScale.rho_pos.le parent]
    exact ambientFiber.card_pos
  have selectedDistinct :
      WZ2PaperOrdinaryIsEssentiallyDistinct
        complete.selectedFine.family :=
    ambient.2.2.1.subfamily complete.selectedFine
  refine
    ⟨ambient.1, ⟨outputOne, outputTop⟩,
      selectedDistinct, ?_⟩
  intro requested
  by_cases actualRequested : actual ≤ requested.1
  · let scale :=
      pureWZ2_completeFiber_coarserScale
        actualScale parent actualRequested
        (actualScale.rho_pos.trans_le actualRequested)
        requested.2.2 outputOne
        (coarserAbsorption requested.1 actualRequested requested.2.2)
    have requestedPos : 0 < requested.1 :=
      ambient.1.trans_le requested.2.1
    have ambientOne : (1 : ENNReal) ≤ ambientC :=
      ambient.2.1.1
    have oneLtFourAmbient :
        (1 : ENNReal) < 4 * ambientC := by
      calc
        (1 : ENNReal) < 4 := by norm_num
        _ = 4 * 1 := by simp
        _ ≤ 4 * ambientC := by gcongr
    have outputStrict : (1 : ENNReal) < outputC :=
      oneLtFourAmbient.trans fourAmbientLtOutput
    have window :
        ENNReal.ofReal requested.1 <
          outputC * ENNReal.ofReal requested.1 := by
      calc
        ENNReal.ofReal requested.1 =
            1 * ENNReal.ofReal requested.1 := by simp
        _ <
            outputC * ENNReal.ofReal requested.1 :=
          ENNReal.mul_lt_mul_left
            (ENNReal.ofReal_pos.mpr requestedPos).ne'
            ENNReal.ofReal_ne_top outputStrict
    exact
      ⟨{
        rho := requested.1
        requested_le := le_rfl
        within_factor := window
        scaleData := scale
      }⟩
  · rcases ambient.2.2.2 requested with ⟨nearby⟩
    by_cases gap :
        4 * (nearby.rho - delta) ≤ actual
    · let restricted :=
        pureWZ2_completeFiber_finerScale
          actualScale nearby.scaleData parent
          (requested.2.1.trans nearby.requested_le)
          deltaActual gap
      let restrictedMono := restricted.mono ambientLeOutput
      exact
        ⟨{
          rho := nearby.rho
          requested_le := nearby.requested_le
          within_factor :=
            nearby.within_factor.trans_le <| by
              gcongr
          scaleData := restrictedMono
        }⟩
    · have transition :
        actual < 4 * nearby.rho := by
        have raw : actual < 4 * (nearby.rho - delta) :=
          lt_of_not_ge gap
        nlinarith [actualScale.delta_pos]
      let actualRestricted :=
        pureWZ2_completeFiber_actualScale
          actualScale ambient.2.1.1 parent
      let actualMono := actualRestricted.mono ambientLeOutput
      have requestedPos : 0 < requested.1 :=
        ambient.1.trans_le requested.2.1
      have window :
          ENNReal.ofReal actual <
            outputC * ENNReal.ofReal requested.1 := by
        have firstWindow :
            ENNReal.ofReal actual <
              (4 : ENNReal) * ENNReal.ofReal nearby.rho := by
          rw [← ENNReal.ofReal_ofNat (n := 4),
            ← ENNReal.ofReal_mul (by norm_num)]
          exact
            (ENNReal.ofReal_lt_ofReal_iff
              (mul_pos (by norm_num) nearby.scaleData.rho_pos)).mpr
              transition
        have secondWindow :
            (4 : ENNReal) * ENNReal.ofReal nearby.rho <
              ((4 : ENNReal) * ambientC) *
                ENNReal.ofReal requested.1 := by
          have scaled :=
            ENNReal.mul_lt_mul_left
              (by norm_num : (4 : ENNReal) ≠ 0)
              (by norm_num : (4 : ENNReal) ≠ ⊤)
              nearby.within_factor
          simpa [mul_comm, mul_left_comm, mul_assoc] using scaled
        have thirdWindow :
            ((4 : ENNReal) * ambientC) *
                  ENNReal.ofReal requested.1 <
              outputC * ENNReal.ofReal requested.1 :=
          ENNReal.mul_lt_mul_left
            (ENNReal.ofReal_pos.mpr requestedPos).ne'
            ENNReal.ofReal_ne_top fourAmbientLtOutput
        exact firstWindow.trans (secondWindow.trans thirdWindow)
      exact
        ⟨{
          rho := actual
          requested_le := le_of_not_ge actualRequested
          within_factor := window
          scaleData := actualMono
        }⟩

end Kakeya.Assouad

end
