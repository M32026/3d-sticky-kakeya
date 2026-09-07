import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.PositiveWindowStatements
import MyLeanRepo.Kakeya.Assouad.ConstantAbsorption

/-!
WZ2 Proposition 7.1: assemble the bounded signed-window one-scale estimate
for iterable parameter states without an essential-distinctness premise.

Select a half-window, absorb the one-half mass loss, use the no-distinct
positive theorem in the positive branch, and apply exact vertical reflection
plus pullback in the negative branch.
-/

namespace Kakeya.Assouad

theorem signed_window_parameter_frostman_scale_from_parameters_bounded_no_distinct :
    SignedWindowParameterFrostmanScaleFromParametersBoundedNoDistinctStatement := by
  intro hHalfWindow hReflectedSlope hReflection hPositive hHolder hPYZ
  intro epsilon rhoMax hepsilon hepsilonOne hrhoMax hrhoMaxOne hrhoMaxLower
  rcases hPositive hHolder hPYZ epsilon rhoMax hepsilon hepsilonOne
      hrhoMax hrhoMaxOne hrhoMaxLower with
    ⟨etaMax, hetaMax, hetaMaxEpsilon, hPositiveEta⟩
  refine ⟨etaMax, hetaMax, hetaMaxEpsilon, ?_⟩
  intro eta heta hetaEtaMax
  rcases hPositiveEta eta heta hetaEtaMax with
    ⟨deltaPositive, hdeltaPositive, hdeltaPositiveOne, hPositiveAt⟩
  rcases exists_delta_realRpowENN_bound (2 : ENNReal)
      (by norm_num) (show 0 < eta / 2 by positivity) with
    ⟨deltaAbsorb, hdeltaAbsorb, hdeltaAbsorbOne, hAbsorb⟩
  let delta₀ : ℝ := min deltaPositive deltaAbsorb
  have hdelta₀ : 0 < delta₀ := by
    dsimp only [delta₀]
    positivity
  have hdelta₀One : delta₀ < 1 := by
    exact (min_le_left deltaPositive deltaAbsorb).trans_lt
      hdeltaPositiveOne
  refine ⟨delta₀, hdelta₀, hdelta₀One, ?_⟩
  intro delta hdelta hdeltaSmall F hFNonempty hFVertical hFParams
    C hCOne hCTop hCBound hParameterFrostman
    Y hYDense hYWindow f hf hfZero
  have hdeltaPositiveSmall : delta ≤ deltaPositive :=
    hdeltaSmall.trans (min_le_left deltaPositive deltaAbsorb)
  have hdeltaAbsorbSmall : delta ≤ deltaAbsorb :=
    hdeltaSmall.trans (min_le_right deltaPositive deltaAbsorb)
  have hTwo :
      (2 : ENNReal) ≤
        Kakeya.realRpowENN delta (-(eta / 2)) :=
    hAbsorb delta hdelta hdeltaAbsorbSmall
  have hPowerProduct :
      Kakeya.realRpowENN delta (-(eta / 2)) *
          Kakeya.realRpowENN delta eta =
        Kakeya.realRpowENN delta (eta / 2) := by
    simp only [Kakeya.realRpowENN]
    have hreal :
        Real.rpow delta (-(eta / 2)) *
            Real.rpow delta eta =
          Real.rpow delta (eta / 2) := by
      calc
        Real.rpow delta (-(eta / 2)) *
            Real.rpow delta eta =
          Real.rpow delta (-(eta / 2) + eta) := by
            exact (Real.rpow_add hdelta _ _).symm
        _ = Real.rpow delta (eta / 2) := by
          congr 1
          ring
    calc
      ENNReal.ofReal (Real.rpow delta (-(eta / 2))) *
          ENNReal.ofReal (Real.rpow delta eta) =
        ENNReal.ofReal
          (Real.rpow delta (-(eta / 2)) *
            Real.rpow delta eta) := by
          exact (ENNReal.ofReal_mul
            (Real.rpow_nonneg hdelta.le (-(eta / 2)))).symm
      _ = ENNReal.ofReal (Real.rpow delta (eta / 2)) := by
        rw [hreal]
  have hPowerHalf :
      Kakeya.realRpowENN delta eta ≤
        (1 / 2 : ENNReal) *
          Kakeya.realRpowENN delta (eta / 2) := by
    have htwice :
        (2 : ENNReal) * Kakeya.realRpowENN delta eta ≤
          Kakeya.realRpowENN delta (eta / 2) := by
      calc
        (2 : ENNReal) * Kakeya.realRpowENN delta eta ≤
            Kakeya.realRpowENN delta (-(eta / 2)) *
              Kakeya.realRpowENN delta eta := by
          gcongr
        _ = Kakeya.realRpowENN delta (eta / 2) := hPowerProduct
    calc
      Kakeya.realRpowENN delta eta =
          (1 / 2 : ENNReal) *
            ((2 : ENNReal) * Kakeya.realRpowENN delta eta) := by
        have hhalfTwo : (1 / 2 : ENNReal) * 2 = 1 := by
          simpa [one_div] using
            ENNReal.inv_mul_cancel
              (show (2 : ENNReal) ≠ 0 by norm_num)
              (show (2 : ENNReal) ≠ ⊤ by norm_num)
        rw [← mul_assoc, hhalfTwo, one_mul]
      _ ≤ (1 / 2 : ENNReal) *
          Kakeya.realRpowENN delta (eta / 2) := by
        gcongr
  rcases hHalfWindow F Y hYWindow with
    ⟨sign, hsign, Yhalf, hYhalfSub, hYhalfMass, hYhalfWindow⟩
  have hYhalfDense :
      Yhalf.IsLambdaDense (Kakeya.realRpowENN delta eta) := by
    have hYDense' :
        Kakeya.realRpowENN delta (eta / 2) *
            F.toBodyFamily.mass ≤
          Y.mass := hYDense
    calc
      Kakeya.realRpowENN delta eta * F.toBodyFamily.mass ≤
          ((1 / 2 : ENNReal) *
            Kakeya.realRpowENN delta (eta / 2)) *
              F.toBodyFamily.mass := by
        gcongr
      _ = (1 / 2 : ENNReal) *
          (Kakeya.realRpowENN delta (eta / 2) *
            F.toBodyFamily.mass) := by
        ring
      _ ≤ (1 / 2 : ENNReal) * Y.mass := by
        exact (mul_le_mul_right hYDense') (1 / 2 : ENNReal)
      _ ≤ Yhalf.mass := hYhalfMass
  rcases hsign with rfl | rfl
  · have hYhalfPositive :
        Yhalf.union ⊆ horizontalSlab 0 1 := by
      simpa using hYhalfWindow
    rcases hPositiveAt delta hdelta hdeltaPositiveSmall
        F hFNonempty hFVertical hFParams
        C hCOne hCTop hCBound hParameterFrostman
        Yhalf hYhalfDense hYhalfPositive f hf hfZero with
      ⟨rho, hrhoLower, hrhoMax, Z, hZSub, hZDense, hProjection⟩
    refine ⟨rho, hrhoLower, hrhoMax, Z, ?_, hZDense, hProjection⟩
    intro i
    exact (hZSub i).trans (hYhalfSub i)
  · have hYhalfNegative :
        Yhalf.union ⊆ horizontalSlab (-1) 0 := by
      simpa only [if_neg (by norm_num : (-1 : ℝ) ≠ 1)] using
        hYhalfWindow
    rcases hReflection F Yhalf with
      ⟨reflectedFamily, reflectedShading,
        hReflectedNonempty, _hReflectedBase, _hReflectedDistinct,
        hReflectedVertical, hReflectedParams,
        hReflectedFrostman, hReflectedDense,
        hReflectedWindow, hPullback⟩
    have hfReflected := (hReflectedSlope f hf).1
    have hfReflectedZero : f.reflected 0 = 0 := by
      simpa [SlopeFunction.reflected] using hfZero
    rcases hPositiveAt delta hdelta hdeltaPositiveSmall
        reflectedFamily (hReflectedNonempty hFNonempty)
        (hReflectedVertical hFVertical)
        (hReflectedParams hFParams)
        C hCOne hCTop hCBound
        (hReflectedFrostman C hParameterFrostman)
        reflectedShading
        (hReflectedDense
          (Kakeya.realRpowENN delta eta) hYhalfDense)
        (hReflectedWindow hYhalfNegative)
        f.reflected hfReflected hfReflectedZero with
      ⟨rho, hrhoLower, hrhoMax, W, hWSub, hWDense, hProjection⟩
    rcases hPullback W hWSub with
      ⟨Z, hZSub, hZDenseTransfer, hVolumeTransfer⟩
    have hVolumes := hVolumeTransfer f
    rw [hVolumes.1, hVolumes.2 rho] at hProjection
    refine
      ⟨rho, hrhoLower, hrhoMax, Z, ?_,
        hZDenseTransfer
          (Kakeya.realRpowENN delta (4 * eta)) hWDense,
        hProjection⟩
    intro i
    exact (hZSub i).trans (hYhalfSub i)

end Kakeya.Assouad
