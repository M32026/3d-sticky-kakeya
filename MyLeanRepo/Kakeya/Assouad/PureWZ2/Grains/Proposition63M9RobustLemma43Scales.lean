import MyLeanRepo.Kakeya.Assouad.WZ1.Corollary26DeltaBudget
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63M9Lemma43RestoreAbsorption

/-!
# Proposition 6.3 M9: robust Lemma 4.3 power scales

This file freezes the three power scales in the robust-transversality version
of paper Lemma 4.3.  The scale called `theta` is independent of the robust
`kappa` call and is used only for the subsequent broad-set deletion.

The incidence quotient has a positive spare exponent:

`theta / kappa = r^(11 * sigma / 16)
                 = q * r^(3 * sigma / 16)`.

Consequently a pre-runtime cutoff absorbing the fixed factor two gives
`theta / kappa <= q / 2`.  The separate broad gap records the exact exponent
needed when the common CV coefficient is `r^(-normalizationLoss)`.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

/-- Robust-transversality scale in the rescaled Lemma 4.3 problem. -/
def proposition63M9RobustLemma43Kappa (r sigma : ℝ) : ℝ :=
  Real.rpow r (sigma / 16)

/-- Triple-product threshold for the broad-set deletion after the robust call. -/
def proposition63M9RobustLemma43Theta (r sigma : ℝ) : ℝ :=
  Real.rpow r (3 * sigma / 4)

/-- Paper weak-incidence target at the rescaled scale. -/
def proposition63M9RobustLemma43Incidence (r sigma : ℝ) : ℝ :=
  Real.rpow r (sigma / 2)

/-- The exact exponent identity behind the branch-local incidence estimate. -/
lemma proposition63_m9_robustLemma43_theta_div_kappa
    {r sigma : ℝ} (hr : 0 < r) :
    proposition63M9RobustLemma43Theta r sigma /
          proposition63M9RobustLemma43Kappa r sigma =
      proposition63M9RobustLemma43Incidence r sigma *
        Real.rpow r (3 * sigma / 16) := by
  rw [proposition63M9RobustLemma43Theta,
    proposition63M9RobustLemma43Kappa,
    proposition63M9RobustLemma43Incidence]
  calc
    Real.rpow r (3 * sigma / 4) / Real.rpow r (sigma / 16) =
        Real.rpow r (3 * sigma / 4 - sigma / 16) :=
      (Real.rpow_sub hr _ _).symm
    _ = Real.rpow r (sigma / 2 + 3 * sigma / 16) := by
      congr 1
      ring
    _ = Real.rpow r (sigma / 2) * Real.rpow r (3 * sigma / 16) :=
      Real.rpow_add hr _ _

/-- A family-independent cutoff for the robust Lemma 4.3 scales.  Besides the
three elementary scale bounds, it stores the half-incidence margin and the
strict broad exponent gap. -/
structure Proposition63M9RobustLemma43ScaleData
    (sigma sourceLoss normalizationLoss : ℝ) where
  cutoff : ℝ
  cutoff_pos : 0 < cutoff
  cutoff_le_one : cutoff ≤ 1
  cutoff_le_tiny : cutoff ≤ 1 / 100000
  sigma_pos : 0 < sigma
  sigma_lt_one : sigma < 1
  broad_gap_pos :
    0 < sigma / 4 - 5 * sourceLoss - 2 * normalizationLoss
  broad_exponent_eq :
    3 * sigma / 4 - sigma + 5 * sourceLoss + 2 * normalizationLoss =
      -(sigma / 4 - 5 * sourceLoss - 2 * normalizationLoss)
  broad_exponent_neg :
    3 * sigma / 4 - sigma + 5 * sourceLoss + 2 * normalizationLoss < 0
  broad_exponent_lt_normalization :
    3 * sigma / 4 - sigma + 5 * sourceLoss < -2 * normalizationLoss
  kappa_pos : ∀ {r : ℝ}, 0 < r → r ≤ cutoff →
    0 < proposition63M9RobustLemma43Kappa r sigma
  theta_pos : ∀ {r : ℝ}, 0 < r → r ≤ cutoff →
    0 < proposition63M9RobustLemma43Theta r sigma
  incidence_pos : ∀ {r : ℝ}, 0 < r → r ≤ cutoff →
    0 < proposition63M9RobustLemma43Incidence r sigma
  kappa_power : ∀ {r : ℝ}, 0 < r →
    ENNReal.ofReal (proposition63M9RobustLemma43Kappa r sigma) =
      Kakeya.realRpowENN r (sigma / 16)
  theta_power : ∀ {r : ℝ}, 0 < r →
    ENNReal.ofReal (proposition63M9RobustLemma43Theta r sigma) =
      Kakeya.realRpowENN r (3 * sigma / 4)
  incidence_power : ∀ {r : ℝ}, 0 < r →
    ENNReal.ofReal (proposition63M9RobustLemma43Incidence r sigma) =
      Kakeya.realRpowENN r (sigma / 2)
  root_le_kappa : ∀ {r : ℝ}, 0 < r → r ≤ cutoff →
    r ≤ proposition63M9RobustLemma43Kappa r sigma
  kappa_le_one : ∀ {r : ℝ}, 0 < r → r ≤ cutoff →
    proposition63M9RobustLemma43Kappa r sigma ≤ 1
  theta_le_one : ∀ {r : ℝ}, 0 < r → r ≤ cutoff →
    proposition63M9RobustLemma43Theta r sigma ≤ 1
  incidence_le_one : ∀ {r : ℝ}, 0 < r → r ≤ cutoff →
    proposition63M9RobustLemma43Incidence r sigma ≤ 1
  incidence_le_twentyFour : ∀ {r : ℝ}, 0 < r → r ≤ cutoff →
    proposition63M9RobustLemma43Incidence r sigma ≤ 1 / 24
  theta_le_incidence : ∀ {r : ℝ}, 0 < r → r ≤ cutoff →
    proposition63M9RobustLemma43Theta r sigma ≤
      proposition63M9RobustLemma43Incidence r sigma
  incidence_half : ∀ {r : ℝ}, 0 < r → r ≤ cutoff →
    proposition63M9RobustLemma43Theta r sigma /
        proposition63M9RobustLemma43Kappa r sigma ≤
      proposition63M9RobustLemma43Incidence r sigma / 2
  broad_power_split : ∀ {r : ℝ}, 0 < r →
    Kakeya.realRpowENN r
        (3 * sigma / 4 - sigma + 5 * sourceLoss) =
      Kakeya.realRpowENN r (-2 * normalizationLoss) *
        Kakeya.realRpowENN r
          (-(sigma / 4 - 5 * sourceLoss - 2 * normalizationLoss))
  broad_power_budget : ∀ {r inputLoss : ℝ}
      {source : PureWZ2ExtremalConfiguration sigma inputLoss r}
      {normalizationExponent : ℕ}
      (normalized : PureWZ2CroppedCriticalNormalizationData
        (outputLoss := normalizationLoss) source normalizationExponent),
      r ≤ cutoff →
        (8192 : ENNReal) *
            (((Nat.log 2 normalized.croppedFamily.card + 1 : ℕ) :
              ENNReal)) ^ 2 *
              Kakeya.realRpowENN r (-normalizationLoss) ^ 2 ≤
          Kakeya.realRpowENN r
            (3 * sigma / 4 - sigma + 5 * sourceLoss)

/-- Freeze the robust Lemma 4.3 scale cutoff before the runtime scale and
family are known.  The only smallness used for incidence is
`r^(3*sigma/16) <= 1/2`. -/
theorem proposition63_m9_robust_lemma43_scales
    (sigma sourceLoss normalizationLoss : ℝ)
    (hsigma : 0 < sigma)
    (hsigmaOne : sigma < 1)
    (hbroadGap : 5 * sourceLoss + 2 * normalizationLoss < sigma / 4) :
    Nonempty (Proposition63M9RobustLemma43ScaleData
      sigma sourceLoss normalizationLoss) := by
  have hspare : 0 < 3 * sigma / 16 := by positivity
  rcases exists_delta_rpow_le_single
      (3 * sigma / 16) (1 / 2) hspare (by norm_num) (by norm_num) with
    ⟨incidenceCutoff, incidenceCutoffPos, incidenceCutoffOne, absorbHalf⟩
  have broadGapPos :
      0 < sigma / 4 - 5 * sourceLoss - 2 * normalizationLoss := by
    linarith
  have broadExponentEq :
      3 * sigma / 4 - sigma + 5 * sourceLoss + 2 * normalizationLoss =
        -(sigma / 4 - 5 * sourceLoss - 2 * normalizationLoss) := by
    ring
  rcases exists_delta_C_pow_log_absorbed_ennreal
      (n := 2) (8192 : ENNReal) (by norm_num)
      proposition63OneScaleLogCoefficient
      proposition63OneScaleLogCoefficient_nonneg broadGapPos (by norm_num) with
    ⟨broadCutoff, broadCutoffPos, broadCutoffOne, absorbBroad⟩
  rcases exists_delta_rpow_le_single
      (sigma / 2) (1 / 24) (by positivity) (by norm_num) (by norm_num) with
    ⟨qCutoff, qCutoffPos, qCutoffOne, qSmall⟩
  let cutoff : ℝ :=
    min incidenceCutoff (min broadCutoff (min qCutoff (1 / 100000)))
  have cutoffOne : cutoff ≤ 1 :=
    (min_le_left _ _).trans incidenceCutoffOne
  refine ⟨{
    cutoff := cutoff
    cutoff_pos := lt_min incidenceCutoffPos <|
      lt_min broadCutoffPos <| lt_min qCutoffPos (by norm_num)
    cutoff_le_one := cutoffOne
    cutoff_le_tiny := (min_le_right _ _).trans <|
      (min_le_right _ _).trans (min_le_right _ _)
    sigma_pos := hsigma
    sigma_lt_one := hsigmaOne
    broad_gap_pos := broadGapPos
    broad_exponent_eq := broadExponentEq
    broad_exponent_neg := by rw [broadExponentEq]; linarith
    broad_exponent_lt_normalization := by linarith
    kappa_pos := ?_
    theta_pos := ?_
    incidence_pos := ?_
    kappa_power := ?_
    theta_power := ?_
    incidence_power := ?_
    root_le_kappa := ?_
    kappa_le_one := ?_
    theta_le_one := ?_
    incidence_le_one := ?_
    incidence_le_twentyFour := ?_
    theta_le_incidence := ?_
    incidence_half := ?_
    broad_power_split := ?_
    broad_power_budget := ?_ }⟩
  · intro r hr _
    exact Real.rpow_pos_of_pos hr _
  · intro r hr _
    exact Real.rpow_pos_of_pos hr _
  · intro r hr _
    exact Real.rpow_pos_of_pos hr _
  · intro r _
    rfl
  · intro r _
    rfl
  · intro r _
    rfl
  · intro r hr hrCutoff
    have exponentLe : sigma / 16 ≤ 1 := by linarith
    simpa [proposition63M9RobustLemma43Kappa] using
      Real.rpow_le_rpow_of_exponent_ge hr (hrCutoff.trans cutoffOne) exponentLe
  · intro r hr hrCutoff
    exact Real.rpow_le_one hr.le (hrCutoff.trans cutoffOne) (by positivity)
  · intro r hr hrCutoff
    exact Real.rpow_le_one hr.le (hrCutoff.trans cutoffOne) (by positivity)
  · intro r hr hrCutoff
    exact Real.rpow_le_one hr.le (hrCutoff.trans cutoffOne) (by positivity)
  · intro r hr hrCutoff
    simpa [proposition63M9RobustLemma43Incidence] using
      qSmall r hr (hrCutoff.trans <|
        (min_le_right _ _).trans <|
          (min_le_right _ _).trans (min_le_left _ _))
  · intro r hr hrCutoff
    unfold proposition63M9RobustLemma43Theta
      proposition63M9RobustLemma43Incidence
    exact Real.rpow_le_rpow_of_exponent_ge hr (hrCutoff.trans cutoffOne)
      (by linarith)
  · intro r hr hrCutoff
    have hrIncidence : r ≤ incidenceCutoff :=
      hrCutoff.trans (min_le_left _ _)
    rw [proposition63_m9_robustLemma43_theta_div_kappa hr]
    have hhalf : Real.rpow r (3 * sigma / 16) ≤ 1 / 2 :=
      absorbHalf r hr hrIncidence
    have hq : 0 ≤ proposition63M9RobustLemma43Incidence r sigma :=
      (Real.rpow_pos_of_pos hr _).le
    calc
      proposition63M9RobustLemma43Incidence r sigma *
            Real.rpow r (3 * sigma / 16) ≤
          proposition63M9RobustLemma43Incidence r sigma * (1 / 2) := by
            gcongr
      _ = proposition63M9RobustLemma43Incidence r sigma / 2 := by ring
  · intro r hr
    rw [← Kakeya.Assouad.realRpowENN_add hr]
    congr 1
    ring
  · intro r inputLoss source normalizationExponent normalized hrCutoff
    have hrBroad : r ≤ broadCutoff :=
      hrCutoff.trans <| (min_le_right _ _).trans (min_le_left _ _)
    have hrTiny : r ≤ 1 / 100000 :=
      hrCutoff.trans <| (min_le_right _ _).trans <|
        (min_le_right _ _).trans (min_le_right _ _)
    let logCount : ENNReal :=
      ((Nat.log 2 normalized.croppedFamily.card + 1 : ℕ) : ENNReal)
    have logCountLe :
        logCount ≤ proposition63OneScaleLogEnvelope r := by
      have logCountMono : Nat.log 2 normalized.croppedFamily.card + 1 ≤
          Nat.log 2 (2 * normalized.croppedFamily.card) + 1 :=
        Nat.add_le_add_right (Nat.log_mono_right <|
          Nat.le_mul_of_pos_left _ (by norm_num)) 1
      have logCountCast : logCount ≤
          ((Nat.log 2 (2 * normalized.croppedFamily.card) + 1 : ℕ) :
            ENNReal) := by
        dsimp only [logCount]
        exact_mod_cast logCountMono
      exact logCountCast.trans <| by
        simpa only [Nat.cast_add, Nat.cast_one] using
          proposition63_cropped_cardLog_le_oneScaleEnvelope normalized hrTiny
    have logAbsorb :
        (8192 : ENNReal) * proposition63OneScaleLogEnvelope r ^ 2 ≤
          Kakeya.realRpowENN r
            (-(sigma / 4 - 5 * sourceLoss - 2 * normalizationLoss)) := by
      simpa [proposition63OneScaleLogEnvelope] using
        absorbBroad r normalized.final_extremal.delta_pos hrBroad
    have coefficientSquare :
        Kakeya.realRpowENN r (-normalizationLoss) ^ 2 =
          Kakeya.realRpowENN r (-2 * normalizationLoss) := by
      rw [pow_two, ← Kakeya.Assouad.realRpowENN_add
        normalized.final_extremal.delta_pos]
      congr 1
      ring
    calc
      (8192 : ENNReal) * logCount ^ 2 *
            Kakeya.realRpowENN r (-normalizationLoss) ^ 2 ≤
          ((8192 : ENNReal) * proposition63OneScaleLogEnvelope r ^ 2) *
            Kakeya.realRpowENN r (-normalizationLoss) ^ 2 := by gcongr
      _ ≤ Kakeya.realRpowENN r
            (-(sigma / 4 - 5 * sourceLoss - 2 * normalizationLoss)) *
          Kakeya.realRpowENN r (-normalizationLoss) ^ 2 := by gcongr
      _ = Kakeya.realRpowENN r (-2 * normalizationLoss) *
          Kakeya.realRpowENN r
            (-(sigma / 4 - 5 * sourceLoss - 2 * normalizationLoss)) := by
        rw [coefficientSquare]
        ring
      _ = Kakeya.realRpowENN r
          (3 * sigma / 4 - sigma + 5 * sourceLoss) := by
        rw [← Kakeya.Assouad.realRpowENN_add
          normalized.final_extremal.delta_pos]
        congr 1
        ring

end Kakeya.Assouad.PureWZ2
