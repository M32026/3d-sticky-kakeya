import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.CanonicalCoarsePropertyPParameters
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.SparseRelativeBandCVPackage
import MyLeanRepo.Kakeya.Assouad.WZ1.Corollary26DeltaBudget

/-!
# Pre-runtime analytic schedule for preliminary Proposition 6.3 grains

The preliminary Lemmas 4.8/4.12 argument needs two analytic producers after
its first sticky call: canonical Property-(P) on the produced coarse pair and
the multilinear-CV package used only if finite planiness selects its sparse
branch.  Their scale thresholds depend only on the already frozen losses, so
they must be selected before the critical sequence chooses its runtime scale.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

/-- Uniform analytic inputs for the preliminary single-sticky finite-grid
construction.  No runtime tube family or shading is stored in this record. -/
structure Proposition63PreliminaryAnalyticSchedule
    (sigma stickyLoss planinessLoss : ℝ) where
  propertyPScale : ℝ
  propertyPScale_pos : 0 < propertyPScale
  propertyPScale_small : propertyPScale ≤ 1 / 10000
  first_power_small : ∀ {L : ℝ}, 0 < L → L ≤ propertyPScale →
    Real.rpow L (sigma / (2 + sigma)) ≤ 1 / 200
  propertyP : ∀ {L : ℝ}
      {family : Kakeya.Streamlined.TubeFamily L}
      {shading : WZ1PaperTubeShading family},
      WZ2PaperCroppedIsExtremal sigma stickyLoss family shading →
      WZ1PaperIsEssentiallyDistinct family →
      WZ1PaperIsLineClass family →
      0 < L → L ≤ propertyPScale →
      Nonempty (CanonicalCoarsePropertyPParameters
        (sigma := sigma) (loss := stickyLoss) shading)
  sparseCVScale : ℝ
  sparseCVScale_pos : 0 < sparseCVScale
  sparseCVScale_small : sparseCVScale ≤ 1 / 12
  sparseCV : ∀ {delta kappa : ℝ}
      {family : Kakeya.Streamlined.TubeFamily delta}
      {ambient : WZ1PaperTubeShading family}
      (prepared : SparseRelativeBandPreparationData
        (kappa := kappa) ambient
        (Kakeya.realRpowENN delta
          (2 - sigma + 3 * planinessLoss))),
      family.Nonempty →
      WZ1PaperIsLineClass family →
      WZ2PaperCroppedIsExtremal sigma planinessLoss family ambient →
      0 < delta → delta ≤ sparseCVScale →
      Nonempty (SparseRelativeBandCVPackage ambient prepared)

namespace Proposition63PreliminaryAnalyticSchedule

/-- The canonical Property-(P) witness selected by the pre-runtime schedule
for one admissible sticky coarse output. -/
noncomputable def parameters
    {sigma stickyLoss planinessLoss delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading family}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    (schedule : Proposition63PreliminaryAnalyticSchedule
      sigma stickyLoss planinessLoss)
    (sticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := stickyLoss)
      sourceShading rho logExponent)
    (hscale : rho.1 ≤ schedule.propertyPScale) :
    CanonicalCoarsePropertyPParameters
      (sigma := sigma) (loss := stickyLoss) sticky.croppedCoarseShading :=
  Classical.choice <| schedule.propertyP sticky.coarse_extremal
    sticky.cover.coarse_essentially_distinct sticky.cover.coarse_line_class
    sticky.coarse_extremal.delta_pos hscale

end Proposition63PreliminaryAnalyticSchedule

/-- Choose both preliminary analytic thresholds before any runtime scale or
configuration. -/
theorem proposition63_preliminary_analytic_schedule
    (sigma stickyLoss planinessLoss : ℝ)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hstickyLoss : 0 < stickyLoss)
    (hstickyQuarter : stickyLoss < sigma / 4)
    (hplaninessLoss : 0 < planinessLoss) :
    Nonempty (Proposition63PreliminaryAnalyticSchedule
      sigma stickyLoss planinessLoss) := by
  have hpowerExponent : 0 < sigma / (2 + sigma) := by
    positivity
  rcases exists_delta_rpow_le_single
      (sigma / (2 + sigma)) (1 / 200) hpowerExponent
      (by norm_num) (by norm_num) with
    ⟨powerScale, powerScalePos, _powerScaleOne, powerHalf⟩
  rcases exists_canonical_coarse_property_p_parameters
      sigma stickyLoss hsigma hsigmaOne hstickyLoss hstickyQuarter with
    ⟨propertyPScale, propertyPScale_pos, propertyPScale_small, propertyP⟩
  have hdensityExponent : 0 ≤ 2 - sigma + 3 * planinessLoss := by
    linarith
  rcases exists_sparse_relative_band_cv_package sigma planinessLoss
      hplaninessLoss hdensityExponent with
    ⟨sparseCVScale, sparseCVScale_pos, sparseCVScale_small, sparseCV⟩
  let commonScale := min powerScale (min propertyPScale sparseCVScale)
  exact ⟨{
    propertyPScale := commonScale
    propertyPScale_pos := lt_min powerScalePos
      (lt_min propertyPScale_pos sparseCVScale_pos)
    propertyPScale_small := (min_le_right _ _).trans <|
      (min_le_left _ _).trans propertyPScale_small
    first_power_small := by
      intro L hL hLScale
      exact powerHalf L hL (hLScale.trans (min_le_left _ _))
    propertyP := by
      intro L family shading extremal distinct line hL hLScale
      exact propertyP extremal distinct line hL <| hLScale.trans <|
        (min_le_right _ _).trans (min_le_left _ _)
    sparseCVScale := commonScale
    sparseCVScale_pos := lt_min powerScalePos
      (lt_min propertyPScale_pos sparseCVScale_pos)
    sparseCVScale_small := (min_le_right _ _).trans <|
      (min_le_right _ _).trans sparseCVScale_small
    sparseCV := by
      intro delta kappa family ambient prepared nonempty line extremal
        hdelta hdeltaScale
      exact sparseCV prepared nonempty line extremal hdelta <|
        hdeltaScale.trans <| (min_le_right _ _).trans (min_le_right _ _)
  }⟩

end Kakeya.Assouad.PureWZ2

end
