import MyLeanRepo.Kakeya.Assouad.WolffFloorStatements
import MyLeanRepo.Kakeya.Assouad.TubeVolumeLowerBound
import MyLeanRepo.Kakeya.Assouad.ConstantAbsorption

/-!
# Wolff volume floor from Assertion D

This module applies the ordinary Assertion D hairbrush theorem to a supplied
same-configuration admissible refinement.  It then performs the WZ2-owned
cardinality, tube-volume, and fixed-constant absorption algebra.
-/

noncomputable section

namespace Kakeya.Assouad

lemma realRpowENN_mul_wolff
    {delta a b : ℝ} (hdelta : 0 < delta) :
    Kakeya.realRpowENN delta a * Kakeya.realRpowENN delta b =
      Kakeya.realRpowENN delta (a + b) := by
  simp only [Kakeya.realRpowENN]
  have hreal :
      Real.rpow delta a * Real.rpow delta b =
        Real.rpow delta (a + b) :=
    (Real.rpow_add hdelta a b).symm
  have hnonneg : 0 ≤ Real.rpow delta a :=
    Real.rpow_nonneg hdelta.le a
  rw [← ENNReal.ofReal_mul hnonneg, hreal]

lemma realRpowENN_rpow_wolff
    {delta : ℝ} (hdelta : 0 < delta) (a b : ℝ) :
    ENNReal.rpow (Kakeya.realRpowENN delta a) b =
      Kakeya.realRpowENN delta (a * b) := by
  simp only [Kakeya.realRpowENN]
  calc
    ENNReal.rpow (ENNReal.ofReal (Real.rpow delta a)) b =
        ENNReal.ofReal (Real.rpow (Real.rpow delta a) b) :=
      ENNReal.ofReal_rpow_of_pos (Real.rpow_pos_of_pos hdelta a)
    _ = ENNReal.ofReal (Real.rpow delta (a * b)) := by
      congr 1
      exact (Real.rpow_mul hdelta.le a b).symm

lemma assertionD_normalization_eq_wolff
    (N V : ENNReal)
    (hN0 : N ≠ 0) (hNtop : N ≠ ⊤)
    (hV0 : V ≠ 0) (hVtop : V ≠ ⊤) :
    N * V *
        ENNReal.rpow
          (N * ENNReal.rpow V (1 / 2)) (-(1 / 2)) =
      ENNReal.rpow N (1 / 2) * ENNReal.rpow V (3 / 4) := by
  have hNhalf0 : ENNReal.rpow N (1 / 2) ≠ 0 :=
    (ENNReal.rpow_pos (bot_lt_iff_ne_bot.mpr hN0) hNtop).ne'
  have hNhalfTop : ENNReal.rpow N (1 / 2) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by norm_num) hNtop
  have hVquarter0 : ENNReal.rpow V (1 / 4) ≠ 0 :=
    (ENNReal.rpow_pos (bot_lt_iff_ne_bot.mpr hV0) hVtop).ne'
  have hVquarterTop : ENNReal.rpow V (1 / 4) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by norm_num) hVtop
  have hN :
      N =
        ENNReal.rpow N (1 / 2) * ENNReal.rpow N (1 / 2) := by
    calc
      N = ENNReal.rpow N 1 := (ENNReal.rpow_one N).symm
      _ = ENNReal.rpow N ((1 / 2) + (1 / 2)) := by norm_num
      _ =
          ENNReal.rpow N (1 / 2) *
            ENNReal.rpow N (1 / 2) :=
        ENNReal.rpow_add (x := N) (1 / 2) (1 / 2) hN0 hNtop
  have hV :
      V =
        ENNReal.rpow V (1 / 4) * ENNReal.rpow V (3 / 4) := by
    calc
      V = ENNReal.rpow V 1 := (ENNReal.rpow_one V).symm
      _ = ENNReal.rpow V ((1 / 4) + (3 / 4)) := by norm_num
      _ =
          ENNReal.rpow V (1 / 4) *
            ENNReal.rpow V (3 / 4) :=
        ENNReal.rpow_add (x := V) (1 / 4) (3 / 4) hV0 hVtop
  have hVsqrtQuarter :
      ENNReal.rpow (ENNReal.rpow V (1 / 2)) (1 / 2) =
        ENNReal.rpow V (1 / 4) := by
    calc
      ENNReal.rpow (ENNReal.rpow V (1 / 2)) (1 / 2) =
          ENNReal.rpow V ((1 / 2) * (1 / 2)) :=
        (ENNReal.rpow_mul V (1 / 2) (1 / 2)).symm
      _ = ENNReal.rpow V (1 / 4) := by norm_num
  have hdenom :
      ENNReal.rpow
          (N * ENNReal.rpow V (1 / 2)) (1 / 2) =
        ENNReal.rpow N (1 / 2) *
          ENNReal.rpow V (1 / 4) := by
    calc
      ENNReal.rpow
          (N * ENNReal.rpow V (1 / 2)) (1 / 2) =
          ENNReal.rpow N (1 / 2) *
            ENNReal.rpow
              (ENNReal.rpow V (1 / 2)) (1 / 2) :=
        ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)
      _ =
          ENNReal.rpow N (1 / 2) *
            ENNReal.rpow V (1 / 4) := by
        rw [hVsqrtQuarter]
  have hneg :
      ENNReal.rpow
          (N * ENNReal.rpow V (1 / 2)) (-(1 / 2)) =
        (ENNReal.rpow
          (N * ENNReal.rpow V (1 / 2)) (1 / 2))⁻¹ :=
    ENNReal.rpow_neg _ _
  let A := ENNReal.rpow N (1 / 2)
  let B := ENNReal.rpow V (1 / 4)
  let C := ENNReal.rpow V (3 / 4)
  have hAB0 : A * B ≠ 0 := mul_ne_zero hNhalf0 hVquarter0
  have hABtop : A * B ≠ ⊤ :=
    ENNReal.mul_ne_top hNhalfTop hVquarterTop
  have hNV : N * V = (A * A) * (B * C) := by
    rw [hN, hV]
  rw [hneg, hdenom]
  change N * V * (A * B)⁻¹ = A * C
  rw [hNV]
  calc
    (A * A) * (B * C) * (A * B)⁻¹ =
        (A * C) * ((A * B) * (A * B)⁻¹) := by
      ring
    _ = A * C := by
      rw [ENNReal.mul_inv_cancel hAB0 hABtop, mul_one]

lemma assertionD_power_lower_wolff
    {delta epsilon : ℝ} (hdelta : 0 < delta)
    (N V : ENNReal)
    (hN :
      Kakeya.realRpowENN delta (-2 + epsilon / 2) ≤ N)
    (hV : Kakeya.realRpowENN delta 2 ≤ V) :
    Kakeya.realRpowENN delta (1 / 2 + epsilon / 2) ≤
      Kakeya.realRpowENN delta (epsilon / 4) *
        (ENNReal.rpow N (1 / 2) * ENNReal.rpow V (3 / 4)) := by
  have hNpow :=
    ENNReal.rpow_le_rpow hN (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hVpow :=
    ENNReal.rpow_le_rpow hV (by norm_num : (0 : ℝ) ≤ 3 / 4)
  have hNpow' :
      Kakeya.realRpowENN delta
          ((-2 + epsilon / 2) * (1 / 2)) ≤
        ENNReal.rpow N (1 / 2) := by
    calc
      Kakeya.realRpowENN delta
          ((-2 + epsilon / 2) * (1 / 2)) =
          ENNReal.rpow
            (Kakeya.realRpowENN delta (-2 + epsilon / 2))
            (1 / 2) :=
        (realRpowENN_rpow_wolff hdelta _ _).symm
      _ ≤ ENNReal.rpow N (1 / 2) := hNpow
  have hVpow' :
      Kakeya.realRpowENN delta (2 * (3 / 4)) ≤
        ENNReal.rpow V (3 / 4) := by
    calc
      Kakeya.realRpowENN delta (2 * (3 / 4)) =
          ENNReal.rpow
            (Kakeya.realRpowENN delta 2) (3 / 4) :=
        (realRpowENN_rpow_wolff hdelta _ _).symm
      _ ≤ ENNReal.rpow V (3 / 4) := hVpow
  have hmul :=
    mul_le_mul hNpow' hVpow' bot_le bot_le
  calc
    Kakeya.realRpowENN delta (1 / 2 + epsilon / 2) =
        Kakeya.realRpowENN delta (epsilon / 4) *
          (Kakeya.realRpowENN delta
              ((-2 + epsilon / 2) * (1 / 2)) *
            Kakeya.realRpowENN delta (2 * (3 / 4))) := by
      rw [realRpowENN_mul_wolff hdelta,
        realRpowENN_mul_wolff hdelta]
      congr 1
      ring
    _ ≤
        Kakeya.realRpowENN delta (epsilon / 4) *
          (ENNReal.rpow N (1 / 2) *
            ENNReal.rpow V (3 / 4)) := by
      gcongr

lemma exists_delta_power_le_ofReal_wolff
    {kappa gamma : ℝ}
    (hkappa : 0 < kappa) (hgamma : 0 < gamma) :
    ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
        Kakeya.realRpowENN delta gamma ≤
          ENNReal.ofReal kappa := by
  let K : ENNReal := ENNReal.ofReal kappa
  have hK0 : K ≠ 0 := by
    simp [K]
    linarith
  have hDtop : K⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr hK0
  rcases exists_delta_realRpowENN_bound K⁻¹ hDtop hgamma with
    ⟨delta₀, hdelta₀, hdelta₀One, hbound⟩
  refine ⟨delta₀, hdelta₀, hdelta₀One, ?_⟩
  intro delta hdelta hdeltaBound
  have hinv :=
    (ENNReal.inv_le_inv).mpr
      (hbound delta hdelta hdeltaBound)
  have hleft : (K⁻¹)⁻¹ = K := inv_inv K
  have hright :
      (Kakeya.realRpowENN delta (-gamma))⁻¹ =
        Kakeya.realRpowENN delta gamma := by
    simp only [Kakeya.realRpowENN]
    have hreal :
        Real.rpow delta (-gamma) =
          (Real.rpow delta gamma)⁻¹ :=
      Real.rpow_neg hdelta.le gamma
    rw [hreal]
    have hofReal :
        ENNReal.ofReal (Real.rpow delta gamma)⁻¹ =
          (ENNReal.ofReal (Real.rpow delta gamma))⁻¹ :=
      ENNReal.ofReal_inv_of_pos
        (Real.rpow_pos_of_pos hdelta gamma)
    rw [hofReal, inv_inv]
  rw [hleft, hright] at hinv
  exact hinv

theorem wolff_volume_floor_from_assertionD_refinement :
    WolffVolumeFloorFromAssertionDRefinementStatement := by
  intro hAssertion hRefinement epsilon hepsilon
  rcases hAssertion with ⟨_, _, hAssertionAt⟩
  rcases hAssertionAt (epsilon / 4) (by positivity) with
    ⟨kappa, assertionEta, hkappa, hAssertionEta,
      hAssertionAtDelta⟩
  rcases hRefinement
      (epsilon / 2) assertionEta (by positivity) hAssertionEta with
    ⟨inputEta, deltaRefine, hInputEta, hDeltaRefine,
      hDeltaRefineOne, hRefineAtDelta⟩
  rcases exists_delta_power_le_ofReal_wolff
      hkappa (show 0 < epsilon / 2 by positivity) with
    ⟨deltaKappa, hDeltaKappa, _hDeltaKappaOne,
      hKappaAbsorb⟩
  let delta₀ := min deltaRefine deltaKappa
  have hdelta₀ : 0 < delta₀ := by positivity
  have hdelta₀One : delta₀ ≤ 1 :=
    (min_le_left _ _).trans hDeltaRefineOne
  refine
    ⟨inputEta, delta₀, hInputEta, hdelta₀,
      hdelta₀One, ?_⟩
  intro delta hdelta hdeltaBound F hFNonempty hFBall
    hFDistinct U hUUniform hUFrostman Y hYDense
  have hdeltaRefine : delta ≤ deltaRefine :=
    hdeltaBound.trans (min_le_left _ _)
  have hdeltaKappa : delta ≤ deltaKappa :=
    hdeltaBound.trans (min_le_right _ _)
  rcases hRefineAtDelta delta hdelta hdeltaRefine F
      hFNonempty hFBall hFDistinct U hUUniform hUFrostman
      Y hYDense with
    ⟨G, source, Z, hGBall, hGDistinct, _hSource, hZSub,
      hZDense, hKT, hFrost, hCard⟩
  have hD :=
    hAssertionAtDelta delta hdelta G hGBall hGDistinct Z
      hZDense hKT hFrost
  let N := G.enncard
  let V := Kakeya.deltaTubeVolume delta
  have hNLower :
      Kakeya.realRpowENN delta (-2 + epsilon / 2) ≤ N :=
    hCard
  have hVLower : Kakeya.realRpowENN delta 2 ≤ V := by
    simpa [V, Kakeya.realRpowENN, Real.rpow_two] using
      canonical_volume_lower hdelta
  have hNPos : 0 < N := by
    have hpositive :
        0 <
          Kakeya.realRpowENN delta (-2 + epsilon / 2) := by
      simp [Kakeya.realRpowENN]
      positivity
    exact hpositive.trans_le hNLower
  have hN0 : N ≠ 0 := hNPos.ne'
  have hNTop : N ≠ ⊤ := by
    simp [N, Kakeya.TubeFamily.enncard]
  have hVPos : 0 < V := by
    have hpositive :
        0 < Kakeya.realRpowENN delta 2 := by
      simp [Kakeya.realRpowENN]
      positivity
    exact hpositive.trans_le hVLower
  have hV0 : V ≠ 0 := hVPos.ne'
  have hdeltaOne : delta ≤ 1 :=
    hdeltaBound.trans hdelta₀One
  have hVTop : V ≠ ⊤ :=
    (tube_volume_scaling.2.1 delta hdelta hdeltaOne).2
  have hNorm :=
    assertionD_normalization_eq_wolff
      N V hN0 hNTop hV0 hVTop
  have hPower :=
    assertionD_power_lower_wolff
      hdelta N V hNLower hVLower
  have hKappa :=
    hKappaAbsorb delta hdelta hdeltaKappa
  have hCore :
      Kakeya.realRpowENN delta (1 / 2 + epsilon) ≤
        ENNReal.ofReal kappa *
          Kakeya.realRpowENN delta (epsilon / 4) *
          (N * V *
            ENNReal.rpow
              (N * ENNReal.rpow V (1 / 2)) (-(1 / 2))) := by
    calc
      Kakeya.realRpowENN delta (1 / 2 + epsilon) =
          Kakeya.realRpowENN delta (epsilon / 2) *
            Kakeya.realRpowENN delta
              (1 / 2 + epsilon / 2) := by
        rw [realRpowENN_mul_wolff hdelta]
        congr 1
        ring
      _ ≤
          ENNReal.ofReal kappa *
            (Kakeya.realRpowENN delta (epsilon / 4) *
              (ENNReal.rpow N (1 / 2) *
                ENNReal.rpow V (3 / 4))) :=
        mul_le_mul hKappa hPower bot_le bot_le
      _ =
          ENNReal.ofReal kappa *
            Kakeya.realRpowENN delta (epsilon / 4) *
            (N * V *
              ENNReal.rpow
                (N * ENNReal.rpow V (1 / 2)) (-(1 / 2))) := by
        rw [hNorm]
        ring
  have hZLower :
      Kakeya.realRpowENN delta (1 / 2 + epsilon) ≤
        MeasureTheory.volume Z.union := by
    apply hCore.trans
    calc
      ENNReal.ofReal kappa *
          Kakeya.realRpowENN delta (epsilon / 4) *
          (N * V *
            ENNReal.rpow
              (N * ENNReal.rpow V (1 / 2)) (-(1 / 2))) =
          ENNReal.ofReal kappa *
            Kakeya.realRpowENN delta (epsilon / 4) *
            G.enncard * Kakeya.deltaTubeVolume delta *
            ENNReal.rpow
              (G.enncard *
                ENNReal.rpow
                  (Kakeya.deltaTubeVolume delta) (1 / 2))
              (-(1 / 2)) := by
        simp only [N, V]
        ring
      _ ≤ MeasureTheory.volume Z.union := by
        simpa [Kakeya.AssertionDLowerBound] using hD
  have hUnion : Z.union ⊆ Y.union := by
    intro x hx
    rcases hx with ⟨T, hTG, hxZ⟩
    exact ⟨source T hTG, hZSub T hTG hxZ⟩
  exact hZLower.trans (MeasureTheory.measure_mono hUnion)

end Kakeya.Assouad
