import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.SparseRelativeBandCountAbsorption
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.PaperCV
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.SelectedCardinalityCancellation

/-!
# Uniform CV package for a prepared sparse relative band

The parameter choice here is the WZ1 Section 6 choice with the structural
loss used as the balancing loss. The relative-band logarithm and the universal
CV constant are absorbed once, before any individual normalized configuration
is selected.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory Set

/-- Prepared sparse branch data receives both the universal paper CV estimate
and the broad-mass absorption inequality needed by finite coordination. -/
structure SparseRelativeBandCVPackage
    {delta sigma loss kappa : Real}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (ambient : WZ1PaperTubeShading family)
    (prepared : SparseRelativeBandPreparationData
      (kappa := kappa) ambient
      (Kakeya.realRpowENN delta (2 - sigma + 3 * loss))) where
  coefficient : ENNReal
  coefficient_ne_top : Ne coefficient Top.top
  tauExponent : Real := sigma - (17 / 2 : Real) * loss
  tau : Real := Real.rpow delta tauExponent
  tau_eq : tau = Real.rpow delta (sigma - (17 / 2 : Real) * loss)
  tau_pos : 0 < tau
  tau_ofReal : ENNReal.ofReal tau =
    Kakeya.realRpowENN delta tauExponent
  cv : ∀ (E : Set Point3), MeasurableSet E →
    E ⊆ prepared.shading.union →
    ∀ (L : ENNReal),
      (∀ point ∈ E,
        L <= (paperShadingTrilinearMultiplicity
          prepared.shading point) ^ (1 / 2 : Real)) →
      L * volume E <=
        coefficient *
          (ENNReal.ofReal (delta ^ 2) * family.enncard) ^
            (3 / 2 : Real)
  absorb :
    let Q : Nat := prepared.multiplicity ^ 3 / 4
    (2 : ENNReal) * (2 * prepared.multiplicity : Nat) * coefficient *
        (ENNReal.ofReal (delta ^ 2) * family.enncard) ^
          (3 / 2 : Real) <=
      (((Q : ENNReal) * ENNReal.ofReal tau) ^
        (1 / 2 : Real)) * prepared.shading.mass

/-- The universal paper CV constant and the relative-band loss can be fixed
uniformly for every sufficiently small sparse configuration. -/
theorem exists_sparse_relative_band_cv_package
    (sigma loss : Real)
    (hloss : 0 < loss)
    (hdensityExponent : 0 <= 2 - sigma + 3 * loss) :
    ∃ delta0 : Real, 0 < delta0 ∧ delta0 <= 1 / 12 ∧
      ∀ {delta kappa : Real}
        {family : Kakeya.Streamlined.TubeFamily delta}
        {ambient : WZ1PaperTubeShading family}
        (prepared : SparseRelativeBandPreparationData
          (kappa := kappa) ambient
          (Kakeya.realRpowENN delta (2 - sigma + 3 * loss))),
        family.Nonempty →
        WZ1PaperIsLineClass family →
        WZ2PaperCroppedIsExtremal sigma loss family ambient →
        0 < delta → delta <= delta0 →
        Nonempty (SparseRelativeBandCVPackage ambient prepared) := by
  rcases paper_cv_broad_set_estimate with
    ⟨coefficient, hcoefficient, hcv⟩
  let gap : Real := (7 / 2 : Real) * loss
  have hgap : 0 < gap := by
    dsimp only [gap]
    positivity
  rcases SparseRelativeBandPreparationData.exists_power_budget_scale
      (2 - sigma + 3 * loss) gap coefficient hdensityExponent hgap
      hcoefficient with
    ⟨powerScale, hpowerScale, hpowerScaleOne, hpowerBudget⟩
  let delta0 : Real := min powerScale (1 / 12)
  have hdelta0 : 0 < delta0 := by
    dsimp only [delta0]
    positivity
  have hdelta0Small : delta0 <= 1 / 12 := min_le_right _ _
  refine ⟨delta0, hdelta0, hdelta0Small, ?_⟩
  intro delta kappa family ambient prepared hfamily hline hextremal
    hdelta hdeltaBound
  have hdeltaPower : delta <= powerScale :=
    hdeltaBound.trans (min_le_left _ _)
  have hdeltaSmall : delta <= 1 / 12 :=
    hdeltaBound.trans (min_le_right _ _)
  have hdeltaOne : delta <= 1 := hdeltaSmall.trans (by norm_num)
  let tauExponent : Real := sigma - (17 / 2 : Real) * loss
  let tau : Real := Real.rpow delta tauExponent
  have htau : 0 < tau := by
    dsimp only [tau]
    exact Real.rpow_pos_of_pos hdelta tauExponent
  have htauOfReal : ENNReal.ofReal tau =
      Kakeya.realRpowENN delta tauExponent := by
    simp [tau, Kakeya.realRpowENN,
      Real.rpow_pos_of_pos hdelta tauExponent]
  have hambient :
      Kakeya.realRpowENN delta (loss + 2) * family.enncard <=
        ambient.mass := by
    have hbody := paperBodyFamily_mass_lower_rpow_two hdelta hdeltaSmall hline
    calc
      Kakeya.realRpowENN delta (loss + 2) * family.enncard =
          Kakeya.realRpowENN delta loss *
            (Kakeya.realRpowENN delta 2 * family.enncard) := by
        rw [Kakeya.Assouad.realRpowENN_add hdelta]
        ring
      _ <= Kakeya.realRpowENN delta loss *
          (wz1PaperBodyFamily family).mass := by gcongr
      _ <= ambient.mass := hextremal.dense
  have hpowerRaw := hpowerBudget prepared hfamily hdelta hdeltaPower
  have hpower :
      (8192 : ENNReal) * (prepared.bandCount : ENNReal) ^ 2 *
          coefficient ^ 2 <=
        Kakeya.realRpowENN delta
          (tauExponent - sigma + 5 * loss) := by
    have hexponent : tauExponent - sigma + 5 * loss = -gap := by
      dsimp only [tauExponent, gap]
      ring
    rwa [hexponent]
  have habsorb := prepared.broad_absorption_of_power_budget
    hdelta htauOfReal hambient hpower
  let hcvPrepared : ∀ (E : Set Point3), MeasurableSet E →
      E ⊆ prepared.shading.union →
      ∀ (L : ENNReal),
        (∀ point ∈ E,
          L <= (paperShadingTrilinearMultiplicity
            prepared.shading point) ^ (1 / 2 : Real)) →
        L * volume E <=
          coefficient *
            (ENNReal.ofReal (delta ^ 2) * family.enncard) ^
              (3 / 2 : Real) := by
    intro E hE _hsub L hL
    exact hcv delta hdelta hdeltaOne family prepared.shading E L hE hL
  exact ⟨{
    coefficient := coefficient
    coefficient_ne_top := hcoefficient
    tauExponent := tauExponent
    tau := tau
    tau_eq := rfl
    tau_pos := htau
    tau_ofReal := htauOfReal
    cv := hcvPrepared
    absorb := habsorb
  }⟩

end Kakeya.Assouad.PureWZ2

end
