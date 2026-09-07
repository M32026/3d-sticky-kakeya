import MyLeanRepo.Kakeya.Cinematic.Section5.DyadicLogLossAbsorption
import MyLeanRepo.Kakeya.Cinematic.Section5.FaithfulCanonicalScaleLoss

/-!
# Ordinary dyadic losses at the faithful canonical scales

This module groups the local dyadic and logarithmic factors that remain after
the canonical parent scale, retention, cluster parameter, and center cover
have been separated.  Each of the eight factors receives exponent budget
`a / 16`, for a total ordinary-loss budget `a / 2`.
-/

namespace Kakeya.Cinematic

noncomputable def faithfulCanonicalOrdinaryDyadicLoss
    (outerLoss logTail : ℝ)
    (layerCount ambientCard fineCard selectedCard : ℕ) : ℝ :=
  outerLoss *
    (((8 * layerCount * (Nat.log2 ambientCard + 1) ^ 2 : ℕ) : ℝ) *
      ((Nat.log2 selectedCard + 1 : ℕ) : ℝ) *
      ((Nat.log2 fineCard + 1 : ℕ) : ℝ) *
      ((Nat.log2 ambientCard + 1 : ℕ) : ℝ) *
      logTail)

lemma faithful_canonical_ordinary_dyadic_loss_le
    (delta metricExponent outerLoss logTail : ℝ)
    (layerCount ambientCard fineCard selectedCard : ℕ)
    (hdelta : 0 < delta)
    (houter : outerLoss ≤
      Real.rpow delta (-(metricExponent / 16)))
    (hlayer : ((8 * layerCount : ℕ) : ℝ) ≤
      Real.rpow delta (-(metricExponent / 16)))
    (hambient : (((Nat.log2 ambientCard + 1 : ℕ) : ℝ)) ≤
      Real.rpow delta (-(metricExponent / 16)))
    (hfine : (((Nat.log2 fineCard + 1 : ℕ) : ℝ)) ≤
      Real.rpow delta (-(metricExponent / 16)))
    (hselected : selectedCard ≤ fineCard)
    (htailNonneg : 0 ≤ logTail)
    (htail : logTail ≤
      Real.rpow delta (-(metricExponent / 16))) :
    faithfulCanonicalOrdinaryDyadicLoss outerLoss logTail
        layerCount ambientCard fineCard selectedCard ≤
      Real.rpow delta
        (-faithfulCanonicalOrdinaryLoss metricExponent) := by
  let p : ℝ := Real.rpow delta (-(metricExponent / 16))
  have hp : 0 ≤ p := Real.rpow_nonneg hdelta.le _
  have houter' : outerLoss ≤ p := houter
  have hlayer' : ((8 * layerCount : ℕ) : ℝ) ≤ p := hlayer
  have hambient' : (((Nat.log2 ambientCard + 1 : ℕ) : ℝ)) ≤ p :=
    hambient
  have hfine' : (((Nat.log2 fineCard + 1 : ℕ) : ℝ)) ≤ p := hfine
  have htail' : logTail ≤ p := htail
  have hselectedLogNat :
      Nat.log2 selectedCard + 1 ≤ Nat.log2 fineCard + 1 := by
    gcongr
    rw [Nat.log2_eq_log_two, Nat.log2_eq_log_two]
    exact Nat.log_mono_right hselected
  have hselected' :
      (((Nat.log2 selectedCard + 1 : ℕ) : ℝ)) ≤ p := by
    have hcast :
        (((Nat.log2 selectedCard + 1 : ℕ) : ℝ)) ≤
          (((Nat.log2 fineCard + 1 : ℕ) : ℝ)) := by
      exact_mod_cast hselectedLogNat
    exact hcast.trans hfine'
  have hlayerCast : (8 : ℝ) * layerCount ≤ p := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using hlayer'
  have hambientCast :
      (Nat.log2 ambientCard : ℝ) + 1 ≤ p := by
    simpa only [Nat.cast_add, Nat.cast_one] using hambient'
  have hfineCast :
      (Nat.log2 fineCard : ℝ) + 1 ≤ p := by
    simpa only [Nat.cast_add, Nat.cast_one] using hfine'
  have hselectedCast :
      (Nat.log2 selectedCard : ℝ) + 1 ≤ p := by
    simpa only [Nat.cast_add, Nat.cast_one] using hselected'
  have hmassNonneg :
      0 ≤ (8 : ℝ) * layerCount *
        ((Nat.log2 ambientCard : ℝ) + 1) ^ 2 := by
    positivity
  have hmass :
      (8 : ℝ) * layerCount *
          ((Nat.log2 ambientCard : ℝ) + 1) ^ 2 ≤
        p ^ 3 := by
    have hambientSq :
        ((Nat.log2 ambientCard : ℝ) + 1) ^ 2 ≤ p ^ 2 :=
      pow_le_pow_left₀ (by positivity) hambientCast 2
    calc
      (8 : ℝ) * layerCount *
            ((Nat.log2 ambientCard : ℝ) + 1) ^ 2 ≤
          p * p ^ 2 :=
        mul_le_mul hlayerCast hambientSq (sq_nonneg _) hp
      _ = p ^ 3 := by ring
  have h1 :
      outerLoss *
          ((8 : ℝ) * layerCount *
            ((Nat.log2 ambientCard : ℝ) + 1) ^ 2) ≤
        p ^ 4 := by
    calc
      outerLoss *
          ((8 : ℝ) * layerCount *
            ((Nat.log2 ambientCard : ℝ) + 1) ^ 2) ≤
        p * p ^ 3 :=
          mul_le_mul houter' hmass hmassNonneg hp
      _ = p ^ 4 := by ring
  have h2 :
      outerLoss *
          ((8 : ℝ) * layerCount *
            ((Nat.log2 ambientCard : ℝ) + 1) ^ 2) *
          ((Nat.log2 selectedCard : ℝ) + 1) ≤
        p ^ 5 := by
    calc
      _ ≤ p ^ 4 * p :=
        mul_le_mul h1 hselectedCast (by positivity)
          (pow_nonneg hp 4)
      _ = p ^ 5 := by ring
  have h3 :
      outerLoss *
          ((8 : ℝ) * layerCount *
            ((Nat.log2 ambientCard : ℝ) + 1) ^ 2) *
          ((Nat.log2 selectedCard : ℝ) + 1) *
          ((Nat.log2 fineCard : ℝ) + 1) ≤
        p ^ 6 := by
    calc
      _ ≤ p ^ 5 * p :=
        mul_le_mul h2 hfineCast (by positivity)
          (pow_nonneg hp 5)
      _ = p ^ 6 := by ring
  have h4 :
      outerLoss *
          ((8 : ℝ) * layerCount *
            ((Nat.log2 ambientCard : ℝ) + 1) ^ 2) *
          ((Nat.log2 selectedCard : ℝ) + 1) *
          ((Nat.log2 fineCard : ℝ) + 1) *
          ((Nat.log2 ambientCard : ℝ) + 1) ≤
        p ^ 7 := by
    calc
      _ ≤ p ^ 6 * p :=
        mul_le_mul h3 hambientCast (by positivity)
          (pow_nonneg hp 6)
      _ = p ^ 7 := by ring
  have hproduct :
      faithfulCanonicalOrdinaryDyadicLoss outerLoss logTail
          layerCount ambientCard fineCard selectedCard ≤ p ^ 8 := by
    dsimp only [faithfulCanonicalOrdinaryDyadicLoss]
    norm_num only [Nat.cast_mul, Nat.cast_pow, Nat.cast_add,
      Nat.cast_ofNat]
    calc
      outerLoss *
          (8 * (layerCount : ℝ) *
              ((Nat.log2 ambientCard : ℝ) + 1) ^ 2 *
            ((Nat.log2 selectedCard : ℝ) + 1) *
            ((Nat.log2 fineCard : ℝ) + 1) *
            ((Nat.log2 ambientCard : ℝ) + 1) *
            logTail) =
        (outerLoss *
              (8 * (layerCount : ℝ) *
                ((Nat.log2 ambientCard : ℝ) + 1) ^ 2) *
              ((Nat.log2 selectedCard : ℝ) + 1) *
              ((Nat.log2 fineCard : ℝ) + 1) *
              ((Nat.log2 ambientCard : ℝ) + 1)) *
            logTail := by ring
      _ ≤ p ^ 7 * p :=
        mul_le_mul h4 htail' htailNonneg (pow_nonneg hp 7)
      _ = p ^ 8 := by ring
  have hpowers : p ^ 8 =
      Real.rpow delta
        (-faithfulCanonicalOrdinaryLoss metricExponent) := by
    dsimp only [p, faithfulCanonicalOrdinaryLoss]
    calc
      Real.rpow delta (-(metricExponent / 16)) ^ (8 : ℕ) =
          Real.rpow
            (Real.rpow delta (-(metricExponent / 16))) (8 : ℝ) :=
        (Real.rpow_natCast
          (Real.rpow delta (-(metricExponent / 16))) 8).symm
      _ =
          Real.rpow delta
            ((-(metricExponent / 16)) * (8 : ℝ)) :=
        (Real.rpow_mul hdelta.le
          (-(metricExponent / 16)) (8 : ℝ)).symm
      _ = Real.rpow delta (-(metricExponent / 2)) := by
        congr 1
        ring
  rw [hpowers] at hproduct
  exact hproduct

lemma faithful_canonical_ordinary_dyadic_loss_absorption
    (metricExponent outerA outerC layerA layerC tailA tailC
      ambientExponent fineExponent : ℝ)
    (hmetric : 0 < metricExponent)
    (houterA : 0 < outerA)
    (houterC : 0 < outerC)
    (hlayerA : 0 < layerA)
    (hlayerC : 0 < layerC)
    (htailA : 0 < tailA)
    (htailC : 0 < tailC)
    (hambientExponent : 0 ≤ ambientExponent)
    (hfineExponent : 0 ≤ fineExponent) :
    ∃ delta₀ : ℝ,
      0 < delta₀ ∧
      delta₀ ≤ 1 / 2 ∧
      ∀ {delta outerLoss logTail : ℝ}
        {layerCount ambientCard fineCard selectedCard : ℕ},
        0 < delta →
        delta ≤ delta₀ →
        outerLoss ≤
          outerA * (Real.log (outerC / delta) + 1) →
        ((8 * layerCount : ℕ) : ℝ) ≤
          layerA * (Real.logb 2 (layerC / delta) + 1) →
        (ambientCard : ℝ) ≤
          Real.rpow delta (-ambientExponent) →
        (fineCard : ℝ) ≤
          Real.rpow delta (-fineExponent) →
        selectedCard ≤ fineCard →
        0 ≤ logTail →
        logTail ≤
          tailA * (Real.log (tailC / delta) + 1) →
        faithfulCanonicalOrdinaryDyadicLoss outerLoss logTail
            layerCount ambientCard fineCard selectedCard ≤
          Real.rpow delta
            (-faithfulCanonicalOrdinaryLoss metricExponent) := by
  let exponent := metricExponent / 16
  have hexponent : 0 < exponent := by
    dsimp only [exponent]
    positivity
  rcases localAssembly_log_absorption_general
      outerA outerC exponent
      houterA houterC hexponent with
    ⟨deltaOuter, hdeltaOuter, hdeltaOuterOne, houterMain⟩
  rcases localAssembly_logb_absorption_general
      layerA layerC exponent
      hlayerA hlayerC hexponent with
    ⟨deltaLayer, hdeltaLayer, hdeltaLayerOne, hlayerMain⟩
  rcases dyadic_log_loss_absorption
      ambientExponent exponent
      hambientExponent hexponent with
    ⟨deltaAmbient, hdeltaAmbient, hdeltaAmbientHalf,
      hambientMain⟩
  rcases dyadic_log_loss_absorption
      fineExponent exponent
      hfineExponent hexponent with
    ⟨deltaFine, hdeltaFine, hdeltaFineHalf, hfineMain⟩
  rcases localAssembly_log_absorption_general
      tailA tailC exponent
      htailA htailC hexponent with
    ⟨deltaTail, hdeltaTail, hdeltaTailOne, htailMain⟩
  let delta₀ :=
    min deltaOuter
      (min deltaLayer
        (min deltaAmbient (min deltaFine deltaTail)))
  have hdelta₀ : 0 < delta₀ := by
    dsimp only [delta₀]
    positivity
  have hdelta₀Half : delta₀ ≤ 1 / 2 := by
    dsimp only [delta₀]
    exact
      (min_le_right _ _).trans
        ((min_le_right _ _).trans
          ((min_le_left _ _).trans hdeltaAmbientHalf))
  refine ⟨delta₀, hdelta₀, hdelta₀Half, ?_⟩
  intro delta outerLoss logTail layerCount ambientCard fineCard
    selectedCard hdelta hdeltaBound houter hlayer hambient
    hfine hselected htailNonneg htail
  have hdeltaOuter' : delta ≤ deltaOuter :=
    hdeltaBound.trans (by
      dsimp only [delta₀]
      exact min_le_left _ _)
  have hdeltaLayer' : delta ≤ deltaLayer :=
    hdeltaBound.trans (by
      dsimp only [delta₀]
      exact (min_le_right _ _).trans (min_le_left _ _))
  have hdeltaAmbient' : delta ≤ deltaAmbient :=
    hdeltaBound.trans (by
      dsimp only [delta₀]
      exact
        (min_le_right _ _).trans
          ((min_le_right _ _).trans (min_le_left _ _)))
  have hdeltaFine' : delta ≤ deltaFine :=
    hdeltaBound.trans (by
      dsimp only [delta₀]
      exact
        (min_le_right _ _).trans
          ((min_le_right _ _).trans
            ((min_le_right _ _).trans (min_le_left _ _))))
  have hdeltaTail' : delta ≤ deltaTail :=
    hdeltaBound.trans (by
      dsimp only [delta₀]
      exact
        (min_le_right _ _).trans
          ((min_le_right _ _).trans
            ((min_le_right _ _).trans (min_le_right _ _))))
  have houterBound :
      outerLoss ≤
        Real.rpow delta (-(metricExponent / 16)) :=
    houter.trans <| by
      simpa [exponent] using
        houterMain delta hdelta hdeltaOuter'
  have hlayerBound :
      ((8 * layerCount : ℕ) : ℝ) ≤
        Real.rpow delta (-(metricExponent / 16)) :=
    hlayer.trans <| by
      simpa [exponent] using
        hlayerMain delta hdelta hdeltaLayer'
  have hambientRaw :=
    hambientMain hdelta hdeltaAmbient' hambient
  have hambientBound :
      (((Nat.log2 ambientCard + 1 : ℕ) : ℝ)) ≤
        Real.rpow delta (-(metricExponent / 16)) := by
    calc
      (((Nat.log2 ambientCard + 1 : ℕ) : ℝ)) ≤
          ((4 * (Nat.log2 ambientCard + 1) : ℕ) : ℝ) := by
        exact_mod_cast
          (Nat.le_mul_of_pos_left
            (Nat.log2 ambientCard + 1) (by norm_num))
      _ ≤ Real.rpow delta (-exponent) := hambientRaw
      _ = Real.rpow delta (-(metricExponent / 16)) := by
        rfl
  have hfineRaw :=
    hfineMain hdelta hdeltaFine' hfine
  have hfineBound :
      (((Nat.log2 fineCard + 1 : ℕ) : ℝ)) ≤
        Real.rpow delta (-(metricExponent / 16)) := by
    calc
      (((Nat.log2 fineCard + 1 : ℕ) : ℝ)) ≤
          ((4 * (Nat.log2 fineCard + 1) : ℕ) : ℝ) := by
        exact_mod_cast
          (Nat.le_mul_of_pos_left
            (Nat.log2 fineCard + 1) (by norm_num))
      _ ≤ Real.rpow delta (-exponent) := hfineRaw
      _ = Real.rpow delta (-(metricExponent / 16)) := by
        rfl
  have htailBound :
      logTail ≤
        Real.rpow delta (-(metricExponent / 16)) :=
    htail.trans <| by
      simpa [exponent] using
        htailMain delta hdelta hdeltaTail'
  exact faithful_canonical_ordinary_dyadic_loss_le
    delta metricExponent outerLoss logTail
    layerCount ambientCard fineCard selectedCard
    hdelta houterBound hlayerBound hambientBound hfineBound
    hselected htailNonneg htailBound

lemma faithful_canonical_remaining_dyadic_loss_absorption
    (metricExponent layerA layerC tailA tailC
      ambientExponent fineExponent : ℝ)
    (hmetric : 0 < metricExponent)
    (hlayerA : 0 < layerA)
    (hlayerC : 0 < layerC)
    (htailA : 0 < tailA)
    (htailC : 0 < tailC)
    (hambientExponent : 0 ≤ ambientExponent)
    (hfineExponent : 0 ≤ fineExponent) :
    ∃ delta₀ : ℝ,
      0 < delta₀ ∧
      delta₀ ≤ 1 / 2 ∧
      ∀ {delta outerLoss logTail : ℝ}
        {layerCount ambientCard fineCard selectedCard : ℕ},
        0 < delta →
        delta ≤ delta₀ →
        outerLoss ≤
          Real.rpow delta (-(metricExponent / 16)) →
        ((8 * layerCount : ℕ) : ℝ) ≤
          layerA * (Real.logb 2 (layerC / delta) + 1) →
        (ambientCard : ℝ) ≤
          Real.rpow delta (-ambientExponent) →
        (fineCard : ℝ) ≤
          Real.rpow delta (-fineExponent) →
        selectedCard ≤ fineCard →
        0 ≤ logTail →
        logTail ≤
          tailA * (Real.log (tailC / delta) + 1) →
        faithfulCanonicalOrdinaryDyadicLoss outerLoss logTail
            layerCount ambientCard fineCard selectedCard ≤
          Real.rpow delta
            (-faithfulCanonicalOrdinaryLoss metricExponent) := by
  let exponent := metricExponent / 16
  have hexponent : 0 < exponent := by
    dsimp only [exponent]
    positivity
  rcases localAssembly_logb_absorption_general
      layerA layerC exponent
      hlayerA hlayerC hexponent with
    ⟨deltaLayer, hdeltaLayer, hdeltaLayerOne, hlayerMain⟩
  rcases dyadic_log_loss_absorption
      ambientExponent exponent
      hambientExponent hexponent with
    ⟨deltaAmbient, hdeltaAmbient, hdeltaAmbientHalf,
      hambientMain⟩
  rcases dyadic_log_loss_absorption
      fineExponent exponent
      hfineExponent hexponent with
    ⟨deltaFine, hdeltaFine, hdeltaFineHalf, hfineMain⟩
  rcases localAssembly_log_absorption_general
      tailA tailC exponent
      htailA htailC hexponent with
    ⟨deltaTail, hdeltaTail, hdeltaTailOne, htailMain⟩
  let delta₀ :=
    min deltaLayer
      (min deltaAmbient (min deltaFine deltaTail))
  have hdelta₀ : 0 < delta₀ := by
    dsimp only [delta₀]
    positivity
  have hdelta₀Half : delta₀ ≤ 1 / 2 := by
    dsimp only [delta₀]
    exact
      (min_le_right _ _).trans
        ((min_le_left _ _).trans hdeltaAmbientHalf)
  refine ⟨delta₀, hdelta₀, hdelta₀Half, ?_⟩
  intro delta outerLoss logTail layerCount ambientCard fineCard
    selectedCard hdelta hdeltaBound houter hlayer hambient
    hfine hselected htailNonneg htail
  have hdeltaLayer' : delta ≤ deltaLayer :=
    hdeltaBound.trans (by
      dsimp only [delta₀]
      exact min_le_left _ _)
  have hdeltaAmbient' : delta ≤ deltaAmbient :=
    hdeltaBound.trans (by
      dsimp only [delta₀]
      exact (min_le_right _ _).trans (min_le_left _ _))
  have hdeltaFine' : delta ≤ deltaFine :=
    hdeltaBound.trans (by
      dsimp only [delta₀]
      exact
        (min_le_right _ _).trans
          ((min_le_right _ _).trans (min_le_left _ _)))
  have hdeltaTail' : delta ≤ deltaTail :=
    hdeltaBound.trans (by
      dsimp only [delta₀]
      exact
        (min_le_right _ _).trans
          ((min_le_right _ _).trans (min_le_right _ _)))
  have hlayerBound :
      ((8 * layerCount : ℕ) : ℝ) ≤
        Real.rpow delta (-(metricExponent / 16)) :=
    hlayer.trans <| by
      simpa [exponent] using
        hlayerMain delta hdelta hdeltaLayer'
  have hambientRaw :=
    hambientMain hdelta hdeltaAmbient' hambient
  have hambientBound :
      (((Nat.log2 ambientCard + 1 : ℕ) : ℝ)) ≤
        Real.rpow delta (-(metricExponent / 16)) := by
    calc
      (((Nat.log2 ambientCard + 1 : ℕ) : ℝ)) ≤
          ((4 * (Nat.log2 ambientCard + 1) : ℕ) : ℝ) := by
        exact_mod_cast
          (Nat.le_mul_of_pos_left
            (Nat.log2 ambientCard + 1) (by norm_num))
      _ ≤ Real.rpow delta (-exponent) := hambientRaw
      _ = Real.rpow delta (-(metricExponent / 16)) := by
        rfl
  have hfineRaw :=
    hfineMain hdelta hdeltaFine' hfine
  have hfineBound :
      (((Nat.log2 fineCard + 1 : ℕ) : ℝ)) ≤
        Real.rpow delta (-(metricExponent / 16)) := by
    calc
      (((Nat.log2 fineCard + 1 : ℕ) : ℝ)) ≤
          ((4 * (Nat.log2 fineCard + 1) : ℕ) : ℝ) := by
        exact_mod_cast
          (Nat.le_mul_of_pos_left
            (Nat.log2 fineCard + 1) (by norm_num))
      _ ≤ Real.rpow delta (-exponent) := hfineRaw
      _ = Real.rpow delta (-(metricExponent / 16)) := by
        rfl
  have htailBound :
      logTail ≤
        Real.rpow delta (-(metricExponent / 16)) :=
    htail.trans <| by
      simpa [exponent] using
        htailMain delta hdelta hdeltaTail'
  exact faithful_canonical_ordinary_dyadic_loss_le
    delta metricExponent outerLoss logTail
    layerCount ambientCard fineCard selectedCard
    hdelta houter hlayerBound hambientBound hfineBound
    hselected htailNonneg htailBound

end Kakeya.Cinematic
