import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63Lemma43

/-!
# Prepared paper Lemma 4.3 input

This module records the *actual* high-multiplicity refinement and the actual
global dyadic band selected from it.  Quantitative absorption assumptions for
the paper Lemma 4.3 step are consequently required only for this dependent
pair, rather than universally for unrelated shadings and bands.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory Set

/-- The dependent preparation produced by the first two selections in the
paper proof of Lemma 4.3.  All fields after `band` retain the provenance of
the actual high-multiplicity call. -/
structure Proposition63PaperLemma43Preparation
    {delta sigma sourceLoss densityLoss : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (source : WZ1PaperTubeShading family) where
  m0 : ℕ
  high : WZ1PaperTubeShading family
  band : WZ2PaperGlobalMultiplicityBandData high
  high_subshading : PaperIsSubshading high source
  high_cubical : WZ1PaperIsCubicalShading high
  high_multiplicity : ∀ point ∈ high.union,
    m0 ≤ high.pointMultiplicity point
  density_lower : Kakeya.realRpowENN delta densityLoss * family.enncard ≤
    (m0 : ENNReal)
  high_mass : (1 / 2 : ENNReal) * source.mass ≤ high.mass
  high_common : ∀ index, high.carrier index =
    source.carrier index ∩ high.union
  m0_pos : 0 < m0

/-- Run the actual high-multiplicity selection and then the actual global
multiplicity-band selection, retaining their dependent provenance. -/
theorem proposition63_prepare_paper_lemma43
    {delta sigma sourceLoss densityLoss : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source : WZ1PaperTubeShading family}
    (sourceExtremal : WZ2PaperCroppedIsExtremal
      sigma sourceLoss family source)
    (hline : WZ1PaperIsLineClass family)
    (hdensityLoss : densityLoss = 2 - sigma + 3 * sourceLoss)
    (hsourceLoss : 0 < sourceLoss)
    (hdeltaSmall : delta ≤ 1 / 10000)
    (hsmall : Kakeya.realRpowENN delta sourceLoss < 1 / 4) :
    Nonempty (Proposition63PaperLemma43Preparation
      (sigma := sigma) (sourceLoss := sourceLoss)
      (densityLoss := densityLoss) source) := by
  rcases high_multiplicity_direction_input sourceExtremal hline
      (hdeltaSmall.trans (by norm_num)) hdensityLoss hsourceLoss hsmall with
    ⟨m0, high, hhighSub, hhighCubical, hhighMultiplicity, hdensity,
      hhighMass, hhighCommon, hm0Pos⟩
  rcases wz2_paper_global_multiplicity_band high hhighCubical with ⟨band⟩
  exact ⟨{
    m0 := m0
    high := high
    band := band
    high_subshading := hhighSub
    high_cubical := hhighCubical
    high_multiplicity := hhighMultiplicity
    density_lower := hdensity
    high_mass := hhighMass
    high_common := hhighCommon
    m0_pos := hm0Pos
  }⟩

/-- The paper Lemma 4.3 argument for the one high/band pair produced by
`proposition63_prepare_paper_lemma43`. -/
theorem proposition63_paper_lemma43_from_preparation
    {delta sigma sourceLoss targetLoss densityLoss kappa tau
      incidenceBudget : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source : WZ1PaperTubeShading family}
    {C : ENNReal}
    (sourceExtremal : WZ2PaperCroppedIsExtremal
      sigma sourceLoss family source)
    (prepared : Proposition63PaperLemma43Preparation
      (sigma := sigma) (sourceLoss := sourceLoss)
      (densityLoss := densityLoss) source)
    (hsourceCWA : WZ2PaperConvexWolffBound family C)
    (hCTop : C ≠ ⊤)
    (hCV : ∀ (E : Set Point3), MeasurableSet E →
      E ⊆ source.union → ∀ (L : ENNReal),
        (∀ point ∈ E, L ≤
          (paperShadingTrilinearMultiplicity source point) ^
            (1 / 2 : ℝ)) →
        L * volume E ≤
          C * (ENNReal.ofReal (delta ^ 2) * family.enncard) ^
            (3 / 2 : ℝ))
    (htargetLoss : 0 < targetLoss)
    (hsourceTarget : sourceLoss ≤ targetLoss)
    (hdeltaSmall : delta ≤ 1 / 10000)
    (hkappa : 0 < kappa)
    (hkappaOne : kappa ≤ 1)
    (hdeltaKappa : delta ≤ kappa)
    (htau : 0 < tau)
    (hincidence : tau / kappa ≤ incidenceBudget)
    (hcloseBudget :
      let X := C * ENNReal.ofReal (10000 * kappa ^ 2) * family.enncard
      let R := Nat.ceil X.toReal + 1
      12 * R ≤ 2 ^ prepared.band.level)
    (hbroadAbsorb :
      let m := 2 ^ prepared.band.level
      let Q : ℕ := m ^ 3 / 4
      (2 : ENNReal) * (2 * m : ℕ) * C *
          (ENNReal.ofReal (delta ^ 2) * family.enncard) ^
            (3 / 2 : ℝ) ≤
        (((Q : ENNReal) * ENNReal.ofReal tau) ^
          (1 / 2 : ℝ)) * prepared.band.band.mass)
    (hrestore :
      proposition63PaperLemma43MassLoss
          (source := source) prepared.high prepared.band *
          Kakeya.realRpowENN delta targetLoss ≤
        Kakeya.realRpowENN delta sourceLoss) :
    Nonempty (Proposition63Lemma43Data
      (sigma := sigma) (sourceLoss := sourceLoss)
      (targetLoss := targetLoss) source incidenceBudget) := by
  let high := prepared.high
  let band := prepared.band
  let m : ℕ := 2 ^ band.level
  let X : ENNReal :=
    C * ENNReal.ofReal (10000 * kappa ^ 2) * family.enncard
  let R : ℕ := Nat.ceil X.toReal + 1
  let Q : ℕ := m ^ 3 / 4
  have hXTop : X ≠ ⊤ := by
    dsimp only [X]
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top hCTop ENNReal.ofReal_ne_top)
      (by simp [Kakeya.Streamlined.TubeFamily.enncard])
  have hRPos : 0 < R := by
    dsimp only [R]
    omega
  have hRBudget : 12 * R ≤ m := by
    simpa [X, R, m, band] using hcloseBudget
  have hmTwelve : 12 ≤ m := by omega
  have hQPos : 0 < Q := by
    dsimp only [Q]
    have hfour : 4 ≤ m ^ 3 := by
      calc
        4 ≤ 2 ^ 3 := by norm_num
        _ ≤ m ^ 3 := Nat.pow_le_pow_left (by omega) 3
    exact Nat.div_pos hfour (by norm_num)
  have hQBudget : 4 * Q ≤ m ^ 3 := by
    dsimp only [Q]
    exact Nat.mul_div_le (m ^ 3) 4
  have hbandLower : ∀ point ∈ band.band.union,
      m ≤ band.band.pointMultiplicity point := by
    intro point hpoint
    have hcoerced : (m : ENNReal) ≤
        (band.band.pointMultiplicity point : ENNReal) := by
      simpa [m] using (band.band_multiplicity point hpoint).1
    exact Nat.cast_le.mp hcoerced
  have hbandUpper : ∀ point ∈ band.band.union,
      (band.band.pointMultiplicity point : ENNReal) ≤ (2 * m : ℕ) := by
    intro point hpoint
    have hupper := (band.band_multiplicity point hpoint).2.le
    simpa [m, pow_succ, mul_comm] using hupper
  have hbandSubSource : PaperIsSubshading band.band source := fun index => by
    intro point hpoint
    rw [band.band_eq] at hpoint
    exact prepared.high_subshading index hpoint.1
  have hCVBand : ∀ (E : Set Point3), MeasurableSet E →
      E ⊆ band.band.union → ∀ (L : ENNReal),
        (∀ point ∈ E, L ≤
          (paperShadingTrilinearMultiplicity band.band point) ^
            (1 / 2 : ℝ)) →
        L * volume E ≤
          C * (ENNReal.ofReal (delta ^ 2) * family.enncard) ^
            (3 / 2 : ℝ) :=
    transfer_cv_to_subshading hbandSubSource C hCV
  have hbroadSmall :
      2 * (∫⁻ point in paperCountedBroadSet band.band tau Q,
        (band.band.pointMultiplicity point : ENNReal)) ≤ band.band.mass :=
    paper_broad_mass_budget_main C hCVBand (2 * m : ℕ) hbandUpper
      Q tau hQPos htau (by simpa [m, Q, band] using hbroadAbsorb)
  have hbroadMeasurable :
      MeasurableSet (paperCountedBroadSet band.band tau Q) :=
    paperCountedBroadSet_measurable band.band tau Q
  rcases paper_narrow_pruning hbroadMeasurable hbroadSmall with ⟨narrow⟩
  have hnarrowClose : ∀ point ∈ narrow.shading.union, ∀ index,
      point ∈ narrow.shading.carrier index →
        paperCloseDirectionCount narrow.shading point index kappa < R := by
    intro point hpoint index hindex
    have hcountBand := paper_cwa_close_direction_count
      (coarseShading := band.band) hsourceCWA
      sourceExtremal.delta_pos hdeltaSmall kappa hkappa hkappaOne
      hdeltaKappa point index (narrow.subshading index hindex)
    have hcountNarrow :
        paperCloseDirectionCount narrow.shading point index kappa ≤
          paperCloseDirectionCount band.band point index kappa := by
      unfold paperCloseDirectionCount
      apply Finset.card_le_card
      intro other hother
      simp only [Finset.mem_filter] at hother ⊢
      exact ⟨hother.1, narrow.subshading other hother.2.1, hother.2.2⟩
    have hcountCoerced :
        (paperCloseDirectionCount narrow.shading point index kappa :
          ENNReal) ≤
        (paperCloseDirectionCount band.band point index kappa : ENNReal) :=
      Nat.cast_le.mpr hcountNarrow
    have hcountX :
        (paperCloseDirectionCount narrow.shading point index kappa :
          ENNReal) ≤ X :=
      hcountCoerced.trans (by simpa [X] using hcountBand)
    have hreal :
        (paperCloseDirectionCount narrow.shading point index kappa : ℝ) ≤
          X.toReal := by
      rw [← ENNReal.toReal_natCast]
      exact (ENNReal.toReal_le_toReal (by simp) hXTop).mpr hcountX
    exact Nat.lt_succ_of_le <|
      Nat.cast_le.mp (hreal.trans (Nat.le_ceil X.toReal))
  have hnarrowMultiplicity : ∀ point ∈ narrow.shading.union,
      narrow.shading.pointMultiplicity point =
        band.band.pointMultiplicity point :=
    fun point hpoint => paper_narrow_pointMultiplicity_eq narrow hpoint
  have hnarrowBudget : ∀ point ∈ narrow.shading.union,
      let mu := narrow.shading.pointMultiplicity point
      4 * (Q + 3 * R * mu ^ 2) ≤ 3 * mu ^ 3 := by
    intro point hpoint
    have hmPoint : m ≤ narrow.shading.pointMultiplicity point := by
      rw [hnarrowMultiplicity point hpoint]
      rcases hpoint with ⟨index, hindex⟩
      exact hbandLower point ⟨index, narrow.subshading index hindex⟩
    exact wz1_good_triple_budget m Q R
      (narrow.shading.pointMultiplicity point) hmPoint hQBudget hRBudget
  rcases paper_cellwise_weak_planiness_from_narrow
      sourceExtremal.delta_pos hkappa sourceExtremal.nonempty
      band.band_cubical narrow hnarrowClose hnarrowBudget with
    ⟨selected, _selection, weakMap, hselectedSub, hselectedCubical,
      hplaneCell, _hselectionCell, _hplaneSelection, _hmultiplicity,
      hselectedMass⟩
  have hselectedSource : PaperIsSubshading selected source := fun index =>
    (hselectedSub index).trans <|
      (narrow.subshading index).trans (hbandSubSource index)
  let bandCount : ENNReal :=
    ((Nat.log 2 family.card + 1 : ℕ) : ENNReal)
  have hbandCountPos : 0 < bandCount := by
    dsimp only [bandCount]
    positivity
  have hbandCountTop : bandCount ≠ ⊤ := by simp [bandCount]
  have hhighBand : high.mass ≤ bandCount * band.band.mass := by
    have hdivision := band.band_mass_retention
    change high.mass / bandCount ≤ band.band.mass at hdivision
    rw [ENNReal.div_le_iff hbandCountPos.ne' hbandCountTop] at hdivision
    simpa [mul_comm] using hdivision
  have hbandNarrowSelected : (1 / 8 : ENNReal) * band.band.mass ≤
      selected.mass := by
    calc
      (1 / 8 : ENNReal) * band.band.mass =
          (1 / 4 : ENNReal) * ((1 / 2 : ENNReal) * band.band.mass) := by
        have hmul : (4 : ENNReal) * 2 = 8 := by norm_num
        have hinv : ((4 : ENNReal) * 2)⁻¹ =
            (4 : ENNReal)⁻¹ * 2⁻¹ := by
          rw [ENNReal.mul_inv] <;> norm_num
        rw [show (1 / 8 : ENNReal) = (1 / 4) * (1 / 2) by
          simpa [one_div, hmul] using hinv]
        ring
      _ ≤ (1 / 4 : ENNReal) * narrow.shading.mass := by
        exact mul_le_mul_right narrow.mass_lower _
      _ ≤ selected.mass := hselectedMass
  have hmass : (1 / 16 : ENNReal) * source.mass ≤
      bandCount * selected.mass := by
    have hhalfHigh := mul_le_mul_right prepared.high_mass (1 / 8 : ENNReal)
    calc
      (1 / 16 : ENNReal) * source.mass =
          (1 / 8 : ENNReal) * ((1 / 2 : ENNReal) * source.mass) := by
        have hmul : (8 : ENNReal) * 2 = 16 := by norm_num
        have hinv : ((8 : ENNReal) * 2)⁻¹ =
            (8 : ENNReal)⁻¹ * 2⁻¹ := by
          rw [ENNReal.mul_inv] <;> norm_num
        rw [show (1 / 16 : ENNReal) = (1 / 8) * (1 / 2) by
          simpa [one_div, hmul] using hinv]
        ring
      _ ≤ (1 / 8 : ENNReal) * high.mass := hhalfHigh
      _ ≤ (1 / 8 : ENNReal) * (bandCount * band.band.mass) := by gcongr
      _ = bandCount * ((1 / 8 : ENNReal) * band.band.mass) := by ring
      _ ≤ bandCount * selected.mass := by gcongr
  let finalMap : PaperWZ1WeakPlaneMapData selected incidenceBudget :=
    paperWeakPlaneMapMono hincidence weakMap
  let massLoss := proposition63Lemma43MassLoss (1 / 16) bandCount
  have hmassLossPos : 0 < massLoss :=
    proposition63Lemma43MassLoss_pos _ _
  have hmassLossTop : massLoss ≠ ⊤ :=
    proposition63Lemma43MassLoss_ne_top (by norm_num) hbandCountTop
  have hinverse : massLoss⁻¹ * source.mass ≤ selected.mass :=
    proposition63Lemma43MassLoss_inv_mul_le
      (by norm_num) (by norm_num) hbandCountTop hmass
  have hextremal : WZ2PaperCroppedIsExtremal
      sigma targetLoss family selected := by
    apply transfer_cropped_extremal_to_subshading massLoss
      hmassLossPos hmassLossTop sourceExtremal hselectedSource
      hinverse hselectedCubical hsourceTarget
    · simpa [massLoss, bandCount, band, high,
        proposition63PaperLemma43MassLoss] using hrestore
    · exact sourceExtremal.delta_pos
    · exact sourceExtremal.delta_le_one
    · exact htargetLoss
  exact ⟨{
    shading := selected
    subshading := hselectedSource
    cubical := hselectedCubical
    planeMap := finalMap
    leftFactor := 1 / 16
    rightFactor := bandCount
    leftFactor_pos := by norm_num
    leftFactor_ne_top := by norm_num
    rightFactor_ne_top := hbandCountTop
    mass_retention := hmass
    extremal := hextremal
  }⟩

end Kakeya.Assouad.PureWZ2
