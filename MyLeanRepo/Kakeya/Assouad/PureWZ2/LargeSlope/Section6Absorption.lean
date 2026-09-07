import MyLeanRepo.Kakeya.Assouad.AbsorptionHelpers
import MyLeanRepo.Kakeya.Assouad.ExtremalHelpers
import MyLeanRepo.Kakeya.Assouad.PureWZ2.PropSticky

/-!
# Small-scale absorption for the pure Section-6 route

This file contains only scalar estimates.  In particular, the first theorem
turns the literal Proposition-5 polylogarithmic retention factor into an
arbitrarily small positive power loss.
-/

noncomputable section

namespace Kakeya.Assouad

/-- A positive power gap absorbs the literal Proposition-5 polylogarithmic
retention factor. -/
theorem exists_delta_pure_refinement_fraction_absorbs
    (sourceLoss targetLoss : ℝ)
    (hLoss : sourceLoss < targetLoss)
    (logExponent : ℕ) :
    ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ {delta : ℝ}, 0 < delta → delta ≤ delta₀ →
        Kakeya.realRpowENN delta targetLoss ≤
          wz2PaperPureRefinementFraction delta logExponent *
            Kakeya.realRpowENN delta sourceLoss := by
  by_cases hExponent : logExponent = 0
  · subst logExponent
    refine ⟨1, by norm_num, le_rfl, ?_⟩
    intro delta hdelta hdeltaOne
    simpa [wz2PaperPureRefinementFraction] using
      (realRpowENN_antitone hdelta hdeltaOne hLoss.le)
  let gap : ℝ := targetLoss - sourceLoss
  have hGap : 0 < gap := by
    dsimp only [gap]
    linarith
  have hExponentPos : 0 < logExponent := Nat.pos_of_ne_zero hExponent
  rcases exists_delta_log_absorbed_ennreal
      (1 : ENNReal) (by norm_num) hGap hExponentPos with
    ⟨absorptionScale, hAbsorptionScalePos, hAbsorptionScaleOne, hAbsorb⟩
  let delta₀ : ℝ := min absorptionScale (Real.exp (-1))
  refine
    ⟨delta₀, lt_min hAbsorptionScalePos (Real.exp_pos _),
      (min_le_left _ _).trans hAbsorptionScaleOne, ?_⟩
  intro delta hdelta hdeltaBound
  have hdeltaAbsorption : delta ≤ absorptionScale :=
    hdeltaBound.trans (min_le_left _ _)
  have hdeltaExp : delta ≤ Real.exp (-1) :=
    hdeltaBound.trans (min_le_right _ _)
  have hdeltaOne : delta ≤ 1 :=
    hdeltaBound.trans
      ((min_le_left _ _).trans hAbsorptionScaleOne)
  have hdeltaStrict : delta < 1 :=
    hdeltaExp.trans_lt (Real.exp_lt_one_iff.mpr (by norm_num))
  let logTerm : ENNReal := ENNReal.ofReal (Real.log (1 / delta))
  let envelope : ENNReal := ENNReal.ofReal (1 + Real.log delta⁻¹)
  have hLogRealPos : 0 < Real.log (1 / delta) :=
    Real.log_pos (one_lt_one_div hdelta hdeltaStrict)
  have hLogZero : logTerm ≠ 0 :=
    (ENNReal.ofReal_pos.mpr hLogRealPos).ne'
  have hLogTop : logTerm ≠ ⊤ := ENNReal.ofReal_ne_top
  have hInvEq : delta⁻¹ = 1 / delta := by
    field_simp [hdelta.ne']
  have hLogEnvelope : logTerm ≤ envelope := by
    dsimp only [logTerm, envelope]
    apply ENNReal.ofReal_mono
    rw [hInvEq]
    linarith
  have hEnvelope : envelope ^ logExponent ≤
      Kakeya.realRpowENN delta (-gap) := by
    change ENNReal.ofReal (1 + Real.log delta⁻¹) ^ logExponent ≤
      Kakeya.realRpowENN delta (-gap)
    simpa only [one_mul] using
      hAbsorb delta hdelta hdeltaAbsorption
  have hLogPower : logTerm ^ logExponent ≤
      Kakeya.realRpowENN delta (-gap) :=
    (pow_le_pow_left' hLogEnvelope logExponent).trans hEnvelope
  have hLogPowZero : logTerm ^ logExponent ≠ 0 :=
    pow_ne_zero _ hLogZero
  have hLogPowTop : logTerm ^ logExponent ≠ ⊤ :=
    ENNReal.pow_ne_top hLogTop
  have hFractionGap :
      Kakeya.realRpowENN delta gap ≤
        wz2PaperPureRefinementFraction delta logExponent := by
    have hInv :
        (Kakeya.realRpowENN delta (-gap))⁻¹ ≤
          (logTerm ^ logExponent)⁻¹ :=
      (ENNReal.inv_le_inv).2 hLogPower
    have hPowerInv :
        (Kakeya.realRpowENN delta (-gap))⁻¹ =
          Kakeya.realRpowENN delta gap := by
      dsimp only [Kakeya.realRpowENN]
      calc
        (ENNReal.ofReal (Real.rpow delta (-gap)))⁻¹ =
            ENNReal.ofReal ((Real.rpow delta (-gap))⁻¹) :=
          (ENNReal.ofReal_inv_of_pos
            (Real.rpow_pos_of_pos hdelta (-gap))).symm
        _ = ENNReal.ofReal (Real.rpow delta gap) := by
          congr 1
          calc
            (Real.rpow delta (-gap))⁻¹ =
                ((Real.rpow delta gap)⁻¹)⁻¹ :=
              congrArg Inv.inv (Real.rpow_neg hdelta.le gap)
            _ = Real.rpow delta gap := inv_inv _
    rw [hPowerInv, ENNReal.inv_pow] at hInv
    simpa [wz2PaperPureRefinementFraction, logTerm] using hInv
  have hPower :
      Kakeya.realRpowENN delta targetLoss =
        Kakeya.realRpowENN delta sourceLoss *
          Kakeya.realRpowENN delta gap := by
    rw [← realRpowENN_add hdelta]
    dsimp only [gap]
    congr 2
    ring
  rw [hPower]
  calc
    Kakeya.realRpowENN delta sourceLoss *
          Kakeya.realRpowENN delta gap ≤
        Kakeya.realRpowENN delta sourceLoss *
          wz2PaperPureRefinementFraction delta logExponent :=
      mul_le_mul_left' hFractionGap _
    _ = wz2PaperPureRefinementFraction delta logExponent *
          Kakeya.realRpowENN delta sourceLoss := by ring

/-- The same polylogarithmic absorption with one fixed finite coefficient. -/
theorem exists_delta_constant_mul_pure_refinement_fraction_absorbs
    (constant : ENNReal) (hConstantTop : constant ≠ ⊤)
    (sourceLoss targetLoss : ℝ)
    (hLoss : sourceLoss < targetLoss)
    (logExponent : ℕ) :
    ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ {delta : ℝ}, 0 < delta → delta ≤ delta₀ →
        constant * Kakeya.realRpowENN delta targetLoss ≤
          wz2PaperPureRefinementFraction delta logExponent *
            Kakeya.realRpowENN delta sourceLoss := by
  let middleLoss : ℝ := (sourceLoss + targetLoss) / 2
  have hSourceMiddle : sourceLoss < middleLoss := by
    dsimp only [middleLoss]
    linarith
  have hMiddleTarget : middleLoss < targetLoss := by
    dsimp only [middleLoss]
    linarith
  rcases exists_delta_pure_refinement_fraction_absorbs
      sourceLoss middleLoss hSourceMiddle logExponent with
    ⟨refinementScale, hRefinementScalePos, hRefinementScaleOne,
      hRefinement⟩
  rcases exists_delta_realRpowENN_bound constant hConstantTop
      (sub_pos.mpr hMiddleTarget) with
    ⟨constantScale, hConstantScalePos, hConstantScaleOne, hConstant⟩
  let delta₀ : ℝ := min refinementScale constantScale
  refine
    ⟨delta₀, lt_min hRefinementScalePos hConstantScalePos,
      (min_le_left _ _).trans hRefinementScaleOne, ?_⟩
  intro delta hdelta hdeltaBound
  have hdeltaRefinement : delta ≤ refinementScale :=
    hdeltaBound.trans (min_le_left _ _)
  have hdeltaConstant : delta ≤ constantScale :=
    hdeltaBound.trans (min_le_right _ _)
  have hFixed := hConstant delta hdelta hdeltaConstant
  have hPolylog := hRefinement hdelta hdeltaRefinement
  calc
    constant * Kakeya.realRpowENN delta targetLoss ≤
        Kakeya.realRpowENN delta (-(targetLoss - middleLoss)) *
          Kakeya.realRpowENN delta targetLoss := by gcongr
    _ = Kakeya.realRpowENN delta middleLoss := by
      rw [← realRpowENN_add hdelta]
      congr 2
      ring
    _ ≤ wz2PaperPureRefinementFraction delta logExponent *
          Kakeya.realRpowENN delta sourceLoss := hPolylog

/-- A fixed finite coefficient is absorbed by a positive gap between two
ordinary powers. -/
theorem exists_delta_constant_mul_power_le_power
    (constant : ENNReal) (hConstantTop : constant ≠ ⊤)
    (sourceExponent targetExponent : ℝ)
    (hExponent : sourceExponent < targetExponent) :
    ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ {delta : ℝ}, 0 < delta → delta ≤ delta₀ →
        constant * Kakeya.realRpowENN delta targetExponent ≤
          Kakeya.realRpowENN delta sourceExponent := by
  let gap := targetExponent - sourceExponent
  have hgap : 0 < gap := by dsimp only [gap]; linarith
  rcases exists_delta_realRpowENN_bound constant hConstantTop hgap with
    ⟨delta₀, hdelta₀Pos, hdelta₀One, hbound⟩
  refine ⟨delta₀, hdelta₀Pos, hdelta₀One, ?_⟩
  intro delta hdelta hdeltaBound
  calc
    constant * Kakeya.realRpowENN delta targetExponent ≤
        Kakeya.realRpowENN delta (-gap) *
          Kakeya.realRpowENN delta targetExponent := by
      gcongr
      exact hbound delta hdelta hdeltaBound
    _ = Kakeya.realRpowENN delta sourceExponent := by
      rw [← realRpowENN_add hdelta]
      dsimp only [gap]
      congr 2
      ring

/-- The two exponent gaps used by the square-root Section-6 scale give the
mass-supply and incidence-cover scalar absorptions simultaneously. -/
theorem exists_delta_section6_sqrt_scalar_absorptions
    (sourceLoss stickyLoss slabLoss : ℝ)
    (hSourceSlab : sourceLoss < slabLoss)
    (hCellGap : sourceLoss + stickyLoss / 2 < 2 * slabLoss)
    (hSlabPos : 0 < slabLoss)
    (logExponent : ℕ) :
    ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ {delta : ℝ}, 0 < delta → delta ≤ delta₀ →
        (ENNReal.ofReal Real.pi *
              Kakeya.realRpowENN delta slabLoss ≤
            wz2PaperPureRefinementFraction delta logExponent *
              Kakeya.realRpowENN delta sourceLoss) ∧
        (ENNReal.ofReal (4 * Real.pi) *
              Kakeya.realRpowENN delta (2 * slabLoss - sourceLoss) ≤
            wz2PaperPureRefinementFraction delta logExponent *
              Kakeya.realRpowENN delta (stickyLoss / 2)) ∧
        (16 : ENNReal) ≤ Kakeya.realRpowENN delta (-slabLoss) := by
  rcases exists_delta_constant_mul_pure_refinement_fraction_absorbs
      (ENNReal.ofReal Real.pi) ENNReal.ofReal_ne_top
      sourceLoss slabLoss hSourceSlab logExponent with
    ⟨massScale, hMassScalePos, hMassScaleOne, hMass⟩
  have hCellExponent : stickyLoss / 2 < 2 * slabLoss - sourceLoss := by
    linarith
  rcases exists_delta_constant_mul_pure_refinement_fraction_absorbs
      (ENNReal.ofReal (4 * Real.pi)) ENNReal.ofReal_ne_top
      (stickyLoss / 2) (2 * slabLoss - sourceLoss)
      hCellExponent logExponent with
    ⟨cellScale, hCellScalePos, hCellScaleOne, hCell⟩
  rcases exists_delta_realRpowENN_bound (16 : ENNReal)
      (by norm_num) hSlabPos with
    ⟨coverScale, hCoverScalePos, hCoverScaleOne, hCover⟩
  let delta₀ : ℝ := min massScale (min cellScale coverScale)
  refine
    ⟨delta₀, lt_min hMassScalePos (lt_min hCellScalePos hCoverScalePos),
      (min_le_left _ _).trans hMassScaleOne, ?_⟩
  intro delta hdelta hdeltaBound
  exact
    ⟨hMass hdelta (hdeltaBound.trans (min_le_left _ _)),
      hCell hdelta
        (hdeltaBound.trans
          ((min_le_right _ _).trans (min_le_left _ _))),
      hCover delta hdelta
        (hdeltaBound.trans
          ((min_le_right _ _).trans (min_le_right _ _)))⟩

/-- Spatial-volume supply and spatial-cell cardinality absorption at the
square-root scale. -/
theorem exists_delta_section6_sqrt_spatial_absorptions
    (stickyLoss slabLoss : ℝ)
    (hStickySlab : stickyLoss < slabLoss)
    (hCellGap : 3 * stickyLoss / 2 < 2 * slabLoss) :
    ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ {delta : ℝ}, 0 < delta → delta ≤ delta₀ →
        ((4 : ENNReal) * Kakeya.realRpowENN delta slabLoss ≤
          Kakeya.realRpowENN delta stickyLoss) ∧
        ((16 : ENNReal) * Kakeya.realRpowENN delta slabLoss ≤
          Kakeya.realRpowENN delta
            (-slabLoss + 3 * stickyLoss / 2)) := by
  rcases exists_delta_constant_mul_power_le_power
      (4 : ENNReal) (by norm_num) stickyLoss slabLoss hStickySlab with
    ⟨volumeScale, hVolumeScalePos, hVolumeScaleOne, hVolume⟩
  have hSpatialExponent :
      -slabLoss + 3 * stickyLoss / 2 < slabLoss := by linarith
  rcases exists_delta_constant_mul_power_le_power
      (16 : ENNReal) (by norm_num)
      (-slabLoss + 3 * stickyLoss / 2) slabLoss hSpatialExponent with
    ⟨cellScale, hCellScalePos, hCellScaleOne, hCell⟩
  let delta₀ := min volumeScale cellScale
  refine ⟨delta₀, lt_min hVolumeScalePos hCellScalePos,
    (min_le_left _ _).trans hVolumeScaleOne, ?_⟩
  intro delta hdelta hdeltaBound
  exact ⟨hVolume hdelta (hdeltaBound.trans (min_le_left _ _)),
    hCell hdelta (hdeltaBound.trans (min_le_right _ _))⟩

end Kakeya.Assouad

end
