import MyLeanRepo.Kakeya.Assouad.ConstantAbsorption
import MyLeanRepo.Kakeya.Assouad.WZ1.KaufmanExponentArithmetic
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma8_13FaithfulSanity

/-!
# Closing arithmetic for the faithful PDF Lemma 8.13 freeze

This module verifies the numerical inequality used after the explicit affine
and endpoint-distance transport.  The factor `7 * delta^(-epsilon₁)` is the
worst one-dimensional coarsening loss from the transported scale to `delta`.
-/

namespace Kakeya.Assouad

noncomputable section

/-- For the one-dimensional exponents used here, Kaufman's total constant is
monotone in the Frostman constant. -/
lemma kaufman_total_const_mono_first
    {firstConstant secondConstant gamma : ℝ}
    (hfirst : 0 ≤ firstConstant)
    (hconstants : firstConstant ≤ secondConstant)
    (hgamma : 0 < gamma)
    (hgammaOne : gamma < 1) :
    kaufman_total_const firstConstant 1 1 gamma ≤
      kaufman_total_const secondConstant 1 1 gamma := by
  dsimp only [kaufman_total_const]
  let angularConstant := kaufman_K_ang 1 gamma
  let frostmanConstant := kaufman_K_frost0 1 gamma
  have hangular : 0 < angularConstant := by
    dsimp only [angularConstant]
    exact kaufman_K_ang_one_positive hgammaOne
  have hfrostman : 0 < frostmanConstant := by
    dsimp only [frostmanConstant]
    exact kaufman_K_frost0_one_positive hgammaOne
  have hsecond : 0 ≤ secondConstant :=
    hfirst.trans hconstants
  have hdifference :
      (secondConstant +
            angularConstant * frostmanConstant *
              (1 + secondConstant) +
            angularConstant) * secondConstant -
          (firstConstant +
            angularConstant * frostmanConstant *
              (1 + firstConstant) +
            angularConstant) * firstConstant =
        (secondConstant - firstConstant) *
          ((secondConstant + firstConstant) +
            angularConstant * frostmanConstant *
              (1 + secondConstant + firstConstant) +
            angularConstant) := by
    ring
  have hnonnegative :
      0 ≤
        (secondConstant - firstConstant) *
          ((secondConstant + firstConstant) +
            angularConstant * frostmanConstant *
              (1 + secondConstant + firstConstant) +
            angularConstant) := by
    apply mul_nonneg
    · linarith
    · have hsum : 0 ≤ secondConstant + firstConstant := by
        linarith
      have hweighted :
          0 ≤
            angularConstant * frostmanConstant *
              (1 + secondConstant + firstConstant) := by
        positivity
      linarith
  linarith

/-- The exponent left after the Kaufman gain and the worst coarsening loss is
strictly negative. -/
lemma wz1Lemma8_13_closing_power_strict
    {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (hepsilonOne : epsilon < 1) :
    4 * wz1Lemma8_13FaithfulNormalizedEta epsilon -
          epsilon *
            (2 * wz1Lemma8_13FaithfulNormalizedEta epsilon +
              epsilon / 2) <
      -wz1Lemma8_13FaithfulEpsilonOne epsilon := by
  have hgap :=
    wz1Lemma8_13_closing_exponent_gap
      hepsilon hepsilonOne
  linarith

/--
The exact Kaufman coefficient with graph density `delta^normalizedEta` and
common Frostman constant `delta^(-normalizedEta)` dominates a fixed positive
constant times `delta^(4 * normalizedEta)`.
-/
lemma wz1Lemma8_13_kaufman_coefficient_lower
    {epsilon delta : ℝ}
    (hepsilon : 0 < epsilon)
    (hepsilonOne : epsilon < 1)
    (hdelta : 0 < delta)
    (hdeltaOne : delta ≤ 1) :
    let normalizedEta :=
      wz1Lemma8_13FaithfulNormalizedEta epsilon
    let gamma := 2 * normalizedEta + 1 - epsilon / 2
    let angularConstant :=
      1 +
        2 * kaufman_K_ang 1 gamma *
          kaufman_K_frost0 1 gamma +
        kaufman_K_ang 1 gamma
    let fixedCoefficient :=
      1 / (2 * angularConstant * (2 : ℝ) ^ gamma)
    fixedCoefficient * delta ^ (4 * normalizedEta) ≤
      (delta ^ normalizedEta) ^ 2 /
        (2 *
          kaufman_total_const
            (delta ^ (-normalizedEta)) 1 1 gamma *
          (2 : ℝ) ^ gamma) := by
  dsimp only
  let normalizedEta :=
    wz1Lemma8_13FaithfulNormalizedEta epsilon
  let gamma := 2 * normalizedEta + 1 - epsilon / 2
  let angularConstant :=
    1 +
      2 * kaufman_K_ang 1 gamma *
        kaufman_K_frost0 1 gamma +
      kaufman_K_ang 1 gamma
  have hnormalizedEta :
      0 < normalizedEta := by
    dsimp only [normalizedEta,
      wz1Lemma8_13FaithfulNormalizedEta]
    positivity
  have hnormalizedEtaUpper :
      normalizedEta < epsilon / 4 := by
    exact
      wz1Lemma8_13_normalizedEta_lt_quarter
        hepsilon hepsilonOne
  have hgamma :
      0 < gamma ∧ gamma < 1 := by
    dsimp only [gamma]
    constructor <;> linarith
  have hconstant :
      1 ≤ delta ^ (-normalizedEta) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos
      hdelta hdeltaOne (by linarith)
  have htotal :=
    kaufman_total_const_quadratic_bound
      hconstant hgamma.1 hgamma.2
  have hangularConstant :
      0 < angularConstant := by
    dsimp only [angularConstant]
    have hangular :=
      kaufman_K_ang_one_positive hgamma.2
    have hfrostman :=
      kaufman_K_frost0_one_positive hgamma.2
    positivity
  have htwoGamma :
      0 < (2 : ℝ) ^ gamma := by
    positivity
  have hdenominatorPositive :
      0 <
        2 *
          kaufman_total_const
            (delta ^ (-normalizedEta)) 1 1 gamma *
          (2 : ℝ) ^ gamma := by
    have htotalPositive :
        0 <
          kaufman_total_const
            (delta ^ (-normalizedEta)) 1 1 gamma :=
      kaufman_total_const_one_pos
        (lt_of_lt_of_le zero_lt_one hconstant)
        hgamma.2
    positivity
  have htotalPositive :
      0 <
        kaufman_total_const
          (delta ^ (-normalizedEta)) 1 1 gamma :=
    kaufman_total_const_one_pos
      (lt_of_lt_of_le zero_lt_one hconstant)
      hgamma.2
  have hupperDenominator :
      2 *
          kaufman_total_const
            (delta ^ (-normalizedEta)) 1 1 gamma *
          (2 : ℝ) ^ gamma ≤
        2 * angularConstant *
          (delta ^ (-normalizedEta)) ^ 2 *
          (2 : ℝ) ^ gamma := by
    have hscaled :
        2 *
            kaufman_total_const
              (delta ^ (-normalizedEta)) 1 1 gamma ≤
          2 * (angularConstant *
            (delta ^ (-normalizedEta)) ^ 2) :=
      mul_le_mul_of_nonneg_left
        (by simpa [angularConstant] using htotal)
        (by norm_num)
    calc
      2 *
            kaufman_total_const
              (delta ^ (-normalizedEta)) 1 1 gamma *
            (2 : ℝ) ^ gamma
          ≤
        (2 * (angularConstant *
          (delta ^ (-normalizedEta)) ^ 2)) *
            (2 : ℝ) ^ gamma :=
        mul_le_mul_of_nonneg_right hscaled htwoGamma.le
      _ =
        2 * angularConstant *
          (delta ^ (-normalizedEta)) ^ 2 *
          (2 : ℝ) ^ gamma := by ring
  have hpowerIdentity :
      (delta ^ normalizedEta) ^ 2 /
          (2 * angularConstant *
            (delta ^ (-normalizedEta)) ^ 2 *
            (2 : ℝ) ^ gamma) =
        (1 / (2 * angularConstant * (2 : ℝ) ^ gamma)) *
          delta ^ (4 * normalizedEta) := by
    have hdeltaNormalized :
        0 < delta ^ normalizedEta :=
      Real.rpow_pos_of_pos hdelta _
    have hdeltaNegative :
        0 < delta ^ (-normalizedEta) :=
      Real.rpow_pos_of_pos hdelta _
    have hpositive :
        0 < 2 * angularConstant * (2 : ℝ) ^ gamma := by
      positivity
    have hpositivePower :
        0 < (delta ^ (-normalizedEta)) ^ 2 := by
      positivity
    have hnegative :
        delta ^ (-normalizedEta) =
          (delta ^ normalizedEta)⁻¹ :=
      Real.rpow_neg hdelta.le normalizedEta
    rw [hnegative]
    have hfour :
        delta ^ (4 * normalizedEta) =
          (delta ^ normalizedEta) ^ 4 := by
      rw [show 4 * normalizedEta =
        normalizedEta * 4 by ring]
      exact Real.rpow_mul_natCast hdelta.le normalizedEta 4
    rw [hfour]
    field_simp
      [hpositive.ne', hpositivePower.ne',
        hdeltaNormalized.ne', hdeltaNegative.ne']
  calc
    (1 / (2 * angularConstant * (2 : ℝ) ^ gamma)) *
          delta ^ (4 * normalizedEta) =
        (delta ^ normalizedEta) ^ 2 /
          (2 * angularConstant *
            (delta ^ (-normalizedEta)) ^ 2 *
            (2 : ℝ) ^ gamma) :=
      hpowerIdentity.symm
    _ ≤
        (delta ^ normalizedEta) ^ 2 /
          (2 *
            kaufman_total_const
              (delta ^ (-normalizedEta)) 1 1 gamma *
            (2 : ℝ) ^ gamma) := by
      exact div_le_div_of_nonneg_left
        (sq_nonneg _)
        hdenominatorPositive
        hupperDenominator

/--
The Kaufman lower bound absorbs both the desired long-projection power and
the worst `7 * delta^(-epsilon₁)` coarsening factor.
-/
theorem wz1Lemma8_13_faithful_closing_numerical :
    ∀ epsilon : ℝ, 0 < epsilon → epsilon < 1 →
      ∃ delta₀ : ℝ,
        0 < delta₀ ∧ delta₀ ≤ 1 ∧
        ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
          ∀ scale : ℝ, 0 < scale →
            scale ≤ delta ^ epsilon →
            let normalizedEta :=
              wz1Lemma8_13FaithfulNormalizedEta epsilon
            let epsilonOne :=
              wz1Lemma8_13FaithfulEpsilonOne epsilon
            let gamma :=
              2 * normalizedEta + 1 - epsilon / 2
            7 * delta ^ (-epsilonOne) *
                  (2 / scale) ^ (1 - epsilon) ≤
              ((delta ^ normalizedEta) ^ 2 /
                (2 *
                  kaufman_total_const
                    (delta ^ (-normalizedEta)) 1 1 gamma *
                  (2 : ℝ) ^ gamma)) *
                scale ^ (-gamma) := by
  intro epsilon hepsilon hepsilonOne
  let normalizedEta :=
    wz1Lemma8_13FaithfulNormalizedEta epsilon
  let epsilonAux :=
    wz1Lemma8_13FaithfulEpsilonOne epsilon
  let gamma :=
    2 * normalizedEta + 1 - epsilon / 2
  let angularConstant :=
    1 +
      2 * kaufman_K_ang 1 gamma *
        kaufman_K_frost0 1 gamma +
      kaufman_K_ang 1 gamma
  let fixedCoefficient :=
    1 / (2 * angularConstant * (2 : ℝ) ^ gamma)
  let angularGap := 2 * normalizedEta + epsilon / 2
  let closingPower :=
    4 * normalizedEta - epsilon * angularGap
  have hnormalizedEta :
      0 < normalizedEta := by
    dsimp only [normalizedEta,
      wz1Lemma8_13FaithfulNormalizedEta]
    positivity
  have hnormalizedEtaUpper :
      normalizedEta < epsilon / 4 := by
    exact
      wz1Lemma8_13_normalizedEta_lt_quarter
        hepsilon hepsilonOne
  have hgamma :
      0 < gamma ∧ gamma < 1 := by
    dsimp only [gamma]
    constructor <;> linarith
  have hangularConstant :
      0 < angularConstant := by
    dsimp only [angularConstant]
    have hangular :=
      kaufman_K_ang_one_positive hgamma.2
    have hfrostman :=
      kaufman_K_frost0_one_positive hgamma.2
    positivity
  have hfixedCoefficient :
      0 < fixedCoefficient := by
    dsimp only [fixedCoefficient]
    positivity
  have hangularGap :
      0 < angularGap := by
    dsimp only [angularGap]
    positivity
  have hclosingPower :
      closingPower < -epsilonAux := by
    dsimp only [closingPower, angularGap,
      normalizedEta, epsilonAux]
    exact
      wz1Lemma8_13_closing_power_strict
        hepsilon hepsilonOne
  let fixedLoss :=
    7 * (2 : ℝ) ^ (1 - epsilon) / fixedCoefficient
  have hfixedLoss :
      0 ≤ fixedLoss := by
    dsimp only [fixedLoss]
    positivity
  rcases
      exists_delta_mul_rpow_le_rpow
        fixedLoss hfixedLoss hclosingPower with
    ⟨delta₀, hdelta₀, hdelta₀One, habsorb⟩
  refine ⟨delta₀, hdelta₀, hdelta₀One, ?_⟩
  intro delta hdelta hdeltaSmall scale hscale hscaleUpper
  change
    7 * delta ^ (-epsilonAux) *
          (2 / scale) ^ (1 - epsilon) ≤
      ((delta ^ normalizedEta) ^ 2 /
        (2 *
          kaufman_total_const
            (delta ^ (-normalizedEta)) 1 1 gamma *
          (2 : ℝ) ^ gamma)) *
        scale ^ (-gamma)
  have hdeltaOne : delta ≤ 1 :=
    hdeltaSmall.trans hdelta₀One
  have hcoefficient :=
    wz1Lemma8_13_kaufman_coefficient_lower
      hepsilon hepsilonOne hdelta hdeltaOne
  have hscalePower :
      delta ^ (-epsilon * angularGap) ≤
        scale ^ (-angularGap) := by
    have hbase :
        (delta ^ epsilon) ^ (-angularGap) ≤
          scale ^ (-angularGap) :=
      Real.rpow_le_rpow_of_nonpos
        hscale hscaleUpper (by linarith)
    have hrewrite :
        (delta ^ epsilon) ^ (-angularGap) =
          delta ^ (-epsilon * angularGap) := by
      rw [← Real.rpow_mul hdelta.le]
      congr 1
      ring
    rw [hrewrite] at hbase
    exact hbase
  have hgammaSplit :
      -gamma = -(1 - epsilon) + (-angularGap) := by
    dsimp only [gamma, angularGap]
    ring
  have hscaleSplit :
      scale ^ (-gamma) =
        scale ^ (-(1 - epsilon)) *
          scale ^ (-angularGap) := by
    rw [hgammaSplit, Real.rpow_add hscale]
  have hdeltaSplit :
      delta ^ closingPower =
        delta ^ (4 * normalizedEta) *
          delta ^ (-epsilon * angularGap) := by
    dsimp only [closingPower]
    rw [show
      4 * normalizedEta - epsilon * angularGap =
        4 * normalizedEta + (-epsilon * angularGap) by ring]
    exact Real.rpow_add hdelta _ _
  have habsorbAt :
      fixedLoss * delta ^ (-epsilonAux) ≤
        delta ^ closingPower :=
    habsorb delta hdelta hdeltaSmall
  have hleftRewrite :
      7 * delta ^ (-epsilonAux) *
          (2 / scale) ^ (1 - epsilon) =
        fixedCoefficient *
          (fixedLoss * delta ^ (-epsilonAux)) *
          scale ^ (-(1 - epsilon)) := by
    have hdivision :
        (2 / scale) ^ (1 - epsilon) =
          (2 : ℝ) ^ (1 - epsilon) *
            scale ^ (-(1 - epsilon)) := by
      rw [show 2 / scale = (2 : ℝ) * scale⁻¹ by ring]
      rw [Real.mul_rpow (by norm_num)
        (inv_nonneg.mpr hscale.le)]
      rw [Real.inv_rpow hscale.le]
      congr 1
      exact (Real.rpow_neg hscale.le _).symm
    rw [hdivision]
    dsimp only [fixedLoss]
    field_simp [hfixedCoefficient.ne']
  rw [hleftRewrite]
  calc
    fixedCoefficient *
          (fixedLoss * delta ^ (-epsilonAux)) *
          scale ^ (-(1 - epsilon))
        ≤
      fixedCoefficient * delta ^ closingPower *
          scale ^ (-(1 - epsilon)) := by
        gcongr
    _ =
      fixedCoefficient *
          (delta ^ (4 * normalizedEta) *
            delta ^ (-epsilon * angularGap)) *
          scale ^ (-(1 - epsilon)) := by
        rw [hdeltaSplit]
    _ ≤
      fixedCoefficient *
          (delta ^ (4 * normalizedEta) *
            scale ^ (-angularGap)) *
          scale ^ (-(1 - epsilon)) := by
        gcongr
    _ =
      (fixedCoefficient * delta ^ (4 * normalizedEta)) *
        scale ^ (-gamma) := by
        rw [hscaleSplit]
        ring
    _ ≤
      ((delta ^ normalizedEta) ^ 2 /
          (2 *
            kaufman_total_const
              (delta ^ (-normalizedEta)) 1 1 gamma *
            (2 : ℝ) ^ gamma)) *
        scale ^ (-gamma) := by
      gcongr

end

end Kakeya.Assouad
