import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63PaperLemma43Prepared
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.OneScaleVariationGeometry

/-!
# Proposition 6.3 M9: paper Lemma 4.3 from robust transversality

This is the paper-order weak-plane-map argument on the actual prepared
dyadic band.  Its close-direction input comes from a preceding robust-scale
Proposition 6.2 call; no fine-scale CWA `kappa^2` count is used here.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory Set

/-- Construction witness for the M9 pointwise Lemma 4.3 output.  The generic
public refinement record intentionally forgets the selected transverse pair;
this private companion retains it so later Node 5 code can audit the actual
normalized-cross plane map instead of postulating an unrelated bound. -/
structure Proposition63M9PointwiseWeakMapWitness
    {delta kappa incidenceBudget : ℝ}
    {theta : ℝ} {Q : ℕ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (source band : WZ1PaperTubeShading family) where
  narrow : PaperWZ1NarrowRefinementData band theta Q
  selection : PaperWZ1NarrowDirectionSelection narrow.shading kappa
  data : Proposition63PointwiseWeakMapRefinementData source incidenceBudget
  data_sub_narrow : PaperIsSubshading data.shading narrow.shading
  planeMap_eq_normal : data.planeMap.planeMap = selection.normal

/-- Restore the usual Proposition 6.3 Lemma 4.3 record while retaining the
actual transverse-pair witness that produced its plane map. -/
structure Proposition63M9Lemma43Witness
    {delta sigma sourceLoss targetLoss kappa theta incidenceBudget : ℝ}
    {Q : ℕ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (source band : WZ1PaperTubeShading family) where
  pointwise : Proposition63M9PointwiseWeakMapWitness
    (source := source) (band := band) (kappa := kappa)
    (incidenceBudget := incidenceBudget) (theta := theta) (Q := Q)
  lemma43 : Proposition63Lemma43Data
    (sigma := sigma) (sourceLoss := sourceLoss)
    (targetLoss := targetLoss) source incidenceBudget
  planeMap_eq : lemma43.planeMap.planeMap = pointwise.data.planeMap.planeMap

/-- A normalized cross of two unit directions with a quantitative transverse
lower bound has small vertical coordinate whenever both directions lie in a
fixed cone about the vertical axis. -/
lemma normalized_cross_vertical_bound_of_narrow_cone
    (first second : Point3) (kappa aperture : ℝ)
    (hfirstUnit : ‖first‖ = 1) (hsecondUnit : ‖second‖ = 1)
    (hkappa : 0 < kappa)
    (htransverse : kappa ≤ ‖wz1Cross first second‖)
    (hfirstCone : ∃ sign : ℝ, (sign = 1 ∨ sign = -1) ∧
      ‖first - sign • e3‖ ≤ aperture)
    (hsecondCone : ∃ sign : ℝ, (sign = 1 ∨ sign = -1) ∧
      ‖second - sign • e3‖ ≤ aperture) :
    |((‖wz1Cross first second‖)⁻¹ •
      wz1Cross first second) (2 : Fin 3)| ≤ 2 * aperture / kappa := by
  rcases hfirstCone with ⟨firstSign, hfirstSign, hfirstClose⟩
  rcases hsecondCone with ⟨secondSign, hsecondSign, hsecondClose⟩
  have haperture : 0 ≤ aperture :=
    (norm_nonneg (first - firstSign • e3)).trans hfirstClose
  have hfirstZero : |first 0| ≤ aperture := by
    have hzero : (first - firstSign • e3) 0 = first 0 := by
      rcases hfirstSign with (rfl | rfl) <;> simp [e3]
    simpa [hzero, Real.norm_eq_abs] using
      (PiLp.norm_apply_le (first - firstSign • e3) (0 : Fin 3)).trans
        hfirstClose
  have hsecondZero : |second 0| ≤ aperture := by
    have hzero : (second - secondSign • e3) 0 = second 0 := by
      rcases hsecondSign with (rfl | rfl) <;> simp [e3]
    simpa [hzero, Real.norm_eq_abs] using
      (PiLp.norm_apply_le (second - secondSign • e3) (0 : Fin 3)).trans
        hsecondClose
  have hfirstOneUnit : |first 1| ≤ 1 := by
    simpa [hfirstUnit, Real.norm_eq_abs] using
      PiLp.norm_apply_le first (1 : Fin 3)
  have hsecondOneUnit : |second 1| ≤ 1 := by
    simpa [hsecondUnit, Real.norm_eq_abs] using
      PiLp.norm_apply_le second (1 : Fin 3)
  have hcrossCoordinate :
      (wz1Cross first second) (2 : Fin 3) =
        first 0 * second 1 - first 1 * second 0 := by
    simp [wz1Cross, cross_apply]
  have hcrossCoordinateBound :
      |(wz1Cross first second) (2 : Fin 3)| ≤ 2 * aperture := by
    rw [hcrossCoordinate]
    calc
      |first 0 * second 1 - first 1 * second 0| ≤
          |first 0 * second 1| + |first 1 * second 0| := abs_sub _ _
      _ = |first 0| * |second 1| + |first 1| * |second 0| := by
        rw [abs_mul, abs_mul]
      _ ≤ aperture * 1 + 1 * aperture := by gcongr
      _ = 2 * aperture := by ring
  have hcrossPos : 0 < ‖wz1Cross first second‖ :=
    hkappa.trans_le htransverse
  change |‖wz1Cross first second‖⁻¹ *
    (wz1Cross first second) (2 : Fin 3)| ≤ 2 * aperture / kappa
  rw [abs_mul, abs_inv, abs_of_pos hcrossPos, inv_mul_eq_div]
  calc
    |(wz1Cross first second) (2 : Fin 3)| / ‖wz1Cross first second‖ ≤
        (2 * aperture) / ‖wz1Cross first second‖ :=
      div_le_div_of_nonneg_right hcrossCoordinateBound (norm_nonneg _)
    _ ≤ (2 * aperture) / kappa :=
      div_le_div_of_nonneg_left (mul_nonneg (by norm_num) haperture)
        hkappa htransverse

/-- A unit normal orthogonal to a unit direction whose positive paper
orientation has vertical coordinate at least `sqrt 3 / 2` has vertical
coordinate at most `1 / 2`.  This is the scale-free estimate needed after
the first literal unit rescaling: it uses the actual selected direction and
does not divide a fixed cone aperture by the robust separation scale. -/
lemma vertical_bound_of_orthogonal_to_steep_paper_direction
    (direction normal : Point3)
    (hdirectionUnit : ‖direction‖ = 1)
    (hnormalUnit : ‖normal‖ = 1)
    (hvertical : Real.sqrt 3 / 2 ≤ direction (2 : Fin 3))
    (horthogonal : inner ℝ direction normal = 0) :
    |normal (2 : Fin 3)| ≤ 1 / 2 := by
  have hinnerExpand : inner ℝ direction normal =
      direction 0 * normal 0 + direction 1 * normal 1 +
        direction 2 * normal 2 := by
    rw [PiLp.inner_apply, Fin.sum_univ_succ, Fin.sum_univ_succ,
      Fin.sum_univ_succ]
    simp
    ring
  have hdirectionSq :
      direction 0 ^ 2 + direction 1 ^ 2 + direction 2 ^ 2 = 1 := by
    have hsq := EuclideanSpace.real_norm_sq_eq direction
    rw [hdirectionUnit] at hsq
    simp [Fin.sum_univ_succ] at hsq
    nlinarith
  have hnormalSq :
      normal 0 ^ 2 + normal 1 ^ 2 + normal 2 ^ 2 = 1 := by
    have hsq := EuclideanSpace.real_norm_sq_eq normal
    rw [hnormalUnit] at hsq
    simp [Fin.sum_univ_succ] at hsq
    nlinarith
  have hsqrtSq : (Real.sqrt 3 / 2) ^ 2 = (3 / 4 : ℝ) := by
    rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    norm_num
  have hdirectionVerticalSq : (3 / 4 : ℝ) ≤ direction 2 ^ 2 := by
    rw [← hsqrtSq]
    nlinarith [Real.sqrt_nonneg 3]
  have hhorizontalSq :
      direction 0 ^ 2 + direction 1 ^ 2 ≤ 1 / 4 := by
    nlinarith [hdirectionSq, hdirectionVerticalSq]
  have hhorizontalCauchy :
      (direction 0 * normal 0 + direction 1 * normal 1) ^ 2 ≤
        (direction 0 ^ 2 + direction 1 ^ 2) *
          (normal 0 ^ 2 + normal 1 ^ 2) := by
    nlinarith [sq_nonneg (direction 0 * normal 1 -
      direction 1 * normal 0)]
  have hnormalVerticalIdentity :
      (direction 2 * normal 2) ^ 2 =
        (direction 0 * normal 0 + direction 1 * normal 1) ^ 2 := by
    rw [hinnerExpand] at horthogonal
    have heq : direction 2 * normal 2 =
        -(direction 0 * normal 0 + direction 1 * normal 1) := by
      linarith
    calc
      (direction 2 * normal 2) ^ 2 =
          (-(direction 0 * normal 0 + direction 1 * normal 1)) ^ 2 := by
        rw [heq]
      _ = (direction 0 * normal 0 + direction 1 * normal 1) ^ 2 := by ring
  have hnormalVerticalSq : normal 2 ^ 2 ≤ 1 / 4 := by
    have hnormalHorizontalEq :
        normal 0 ^ 2 + normal 1 ^ 2 = 1 - normal 2 ^ 2 := by
      linarith [hnormalSq]
    have hnormalHorizontalNonneg :
        0 ≤ normal 0 ^ 2 + normal 1 ^ 2 := by positivity
    have hnormalHorizontalLeOne :
        normal 0 ^ 2 + normal 1 ^ 2 ≤ 1 := by
      nlinarith [hnormalSq, sq_nonneg (normal 2)]
    have hlower :
        (3 / 4 : ℝ) * normal 2 ^ 2 ≤
          direction 2 ^ 2 * normal 2 ^ 2 :=
      mul_le_mul_of_nonneg_right hdirectionVerticalSq (sq_nonneg _)
    have hidentity : direction 2 ^ 2 * normal 2 ^ 2 =
        (direction 0 * normal 0 + direction 1 * normal 1) ^ 2 := by
      calc
        direction 2 ^ 2 * normal 2 ^ 2 =
            (direction 2 * normal 2) ^ 2 := by ring
        _ = _ := hnormalVerticalIdentity
    have hupper :
        (direction 0 * normal 0 + direction 1 * normal 1) ^ 2 ≤
          (1 / 4 : ℝ) * (normal 0 ^ 2 + normal 1 ^ 2) :=
      hhorizontalCauchy.trans <|
        mul_le_mul_of_nonneg_right hhorizontalSq hnormalHorizontalNonneg
    have hcombined : (3 / 4 : ℝ) * normal 2 ^ 2 ≤
        (1 / 4 : ℝ) * (1 - normal 2 ^ 2) := by
      calc
        (3 / 4 : ℝ) * normal 2 ^ 2 ≤
            direction 2 ^ 2 * normal 2 ^ 2 := hlower
        _ = (direction 0 * normal 0 + direction 1 * normal 1) ^ 2 :=
          hidentity
        _ ≤ (1 / 4 : ℝ) * (normal 0 ^ 2 + normal 1 ^ 2) := hupper
        _ = (1 / 4 : ℝ) * (1 - normal 2 ^ 2) := by
          rw [hnormalHorizontalEq]
    linarith
  nlinarith [sq_abs (normal 2), abs_nonneg (normal 2)]

/-- The same vertical estimate for the raw tube orientation.  The normal is
orthogonal to the raw direction selected by Lemma 4.3, while the strong
vertical bound is naturally stated for the positive paper orientation. -/
lemma vertical_bound_of_orthogonal_to_steep_tube_direction
    {delta : ℝ} (tube : Kakeya.DeltaTube delta) (normal : Point3)
    (hnormalUnit : ‖normal‖ = 1)
    (hvertical : Real.sqrt 3 / 2 ≤
      wz1PaperDirection tube (2 : Fin 3))
    (horthogonal : inner ℝ tube.direction normal = 0) :
    |normal (2 : Fin 3)| ≤ 1 / 2 := by
  rcases paperDirection_sign tube with ⟨sign, hsign, hdirection⟩
  have hpaperOrthogonal :
      inner ℝ (wz1PaperDirection tube) normal = 0 := by
    rw [hdirection, inner_smul_left] at horthogonal
    rcases hsign with rfl | rfl <;> simpa using horthogonal
  exact vertical_bound_of_orthogonal_to_steep_paper_direction
    (wz1PaperDirection tube) normal (wz1PaperDirection_norm tube)
    hnormalUnit hvertical hpaperOrthogonal

/-- The construction-aware Lemma 4.3 witness inherits a pointwise vertical
bound from the sharp direction margin of its ambient family. -/
theorem Proposition63M9PointwiseWeakMapWitness.vertical_bound
    {delta kappa incidenceBudget theta : ℝ} {Q : ℕ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source band : WZ1PaperTubeShading family}
    (witness : Proposition63M9PointwiseWeakMapWitness
      (source := source) (band := band) (kappa := kappa)
      (incidenceBudget := incidenceBudget) (theta := theta) (Q := Q))
    (hfamilyVertical : ∀ index, Real.sqrt 3 / 2 ≤
      wz1PaperDirection (family.tube index) (2 : Fin 3)) :
    ∀ point ∈ witness.data.shading.union,
      |witness.data.planeMap.planeMap point (2 : Fin 3)| ≤ 1 / 2 := by
  intro point hpoint
  have hpointNarrow : point ∈ witness.narrow.shading.union := by
    rcases hpoint with ⟨index, hindex⟩
    exact ⟨index, witness.data_sub_narrow index hindex⟩
  let tube := family.tube (witness.selection.first point)
  have hnormalUnit : ‖witness.data.planeMap.planeMap point‖ = 1 :=
    witness.data.planeMap.unit point hpoint
  have horthogonal : inner ℝ tube.direction
      (witness.data.planeMap.planeMap point) = 0 := by
    rw [witness.planeMap_eq_normal]
    exact narrowSelection_normal_first_inner_zero witness.selection point
  exact vertical_bound_of_orthogonal_to_steep_tube_direction tube
    (witness.data.planeMap.planeMap point) hnormalUnit
    (hfamilyVertical (witness.selection.first point)) horthogonal

/-- Construct the pointwise weak plane map from an actual prepared band with
an externally supplied robust close-count certificate.  This is the
pointwise-only core: it records the cubical receipt needed by the later
extremality wrapper, but does not assume or restore extremality itself. -/
theorem proposition63_pointwise_weak_map_from_robust_preparation_with_witness
    {delta sigma sourceLoss densityLoss kappa theta
      incidenceBudget : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source : WZ1PaperTubeShading family}
    {C : ENNReal}
    (prepared : Proposition63PaperLemma43Preparation
      (sigma := sigma) (sourceLoss := sourceLoss)
      (densityLoss := densityLoss) source)
    (hCV : ∀ (E : Set Point3), MeasurableSet E →
      E ⊆ source.union → ∀ (L : ENNReal),
        (∀ point ∈ E, L ≤
          (paperShadingTrilinearMultiplicity source point) ^
            (1 / 2 : ℝ)) →
        L * volume E ≤
          C * (ENNReal.ofReal (delta ^ 2) * family.enncard) ^
            (3 / 2 : ℝ))
    (hkappa : 0 < kappa)
    (htheta : 0 < theta)
    (hincidence : theta / kappa ≤ incidenceBudget)
    (hm24 : 24 ≤ 2 ^ prepared.band.level)
    (hclose : ∀ point ∈ prepared.band.band.union, ∀ index,
      point ∈ prepared.band.band.carrier index →
        paperCloseDirectionCount prepared.band.band point index kappa <
          (2 ^ prepared.band.level) / 24)
    (hbroadAbsorb :
      let m := 2 ^ prepared.band.level
      let Q : ℕ := m ^ 3 / 4
      (2 : ENNReal) * (2 * m : ℕ) * C *
          (ENNReal.ofReal (delta ^ 2) * family.enncard) ^
            (3 / 2 : ℝ) ≤
        (((Q : ENNReal) * ENNReal.ofReal theta) ^
          (1 / 2 : ℝ)) * prepared.band.band.mass)
    (hdelta : 0 < delta)
    (hfamily : family.Nonempty) :
    ∃ witness : Proposition63M9PointwiseWeakMapWitness
        (source := source) (band := prepared.band.band)
        (kappa := kappa) (incidenceBudget := incidenceBudget)
        (theta := theta) (Q := (2 ^ prepared.band.level) ^ 3 / 4),
      WZ1PaperIsCubicalShading witness.data.shading ∧
      witness.data.leftFactor = 1 / 16 ∧
      witness.data.rightFactor =
        ((Nat.log 2 family.card + 1 : ℕ) : ENNReal) := by
  let m : ℕ := 2 ^ prepared.band.level
  let R : ℕ := m / 24
  let Q : ℕ := m ^ 3 / 4
  have hRPos : 0 < R := by
    dsimp only [R, m]
    exact Nat.div_pos hm24 (by norm_num)
  have hRBudget : 12 * R ≤ m := by
    have htwentyFour : 24 * R ≤ m := by
      dsimp only [R]
      exact Nat.mul_div_le m 24
    omega
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
  have hbandLower : ∀ point ∈ prepared.band.band.union,
      m ≤ prepared.band.band.pointMultiplicity point := by
    intro point hpoint
    exact_mod_cast (prepared.band.band_multiplicity point hpoint).1
  have hbandUpper : ∀ point ∈ prepared.band.band.union,
      (prepared.band.band.pointMultiplicity point : ENNReal) ≤
        (2 * m : ℕ) := by
    intro point hpoint
    exact (prepared.band.band_multiplicity point hpoint).2.le.trans_eq <| by
      simp [m, pow_succ, mul_comm]
  have hbandSubHigh : PaperIsSubshading
      prepared.band.band prepared.high := by
    rw [prepared.band.band_eq]
    exact wz1PaperDyadicBandSubshading_isSubshading
      prepared.high prepared.band.level
  have hbandSubSource : PaperIsSubshading
      prepared.band.band source := fun index =>
    (hbandSubHigh index).trans (prepared.high_subshading index)
  have hCVBand : ∀ (E : Set Point3), MeasurableSet E →
      E ⊆ prepared.band.band.union → ∀ (L : ENNReal),
        (∀ point ∈ E, L ≤
          (paperShadingTrilinearMultiplicity prepared.band.band point) ^
            (1 / 2 : ℝ)) →
        L * volume E ≤
          C * (ENNReal.ofReal (delta ^ 2) * family.enncard) ^
            (3 / 2 : ℝ) :=
    transfer_cv_to_subshading hbandSubSource C hCV
  have hbroadSmall :
      2 * (∫⁻ point in paperCountedBroadSet prepared.band.band theta Q,
        (prepared.band.band.pointMultiplicity point : ENNReal)) ≤
          prepared.band.band.mass :=
    paper_broad_mass_budget_main C hCVBand (2 * m : ℕ) hbandUpper
      Q theta hQPos htheta (by simpa [m, Q] using hbroadAbsorb)
  have hbroadMeasurable :
      MeasurableSet (paperCountedBroadSet prepared.band.band theta Q) :=
    paperCountedBroadSet_measurable prepared.band.band theta Q
  rcases paper_narrow_pruning hbroadMeasurable hbroadSmall with ⟨narrow⟩
  have hnarrowClose : ∀ point ∈ narrow.shading.union, ∀ index,
      point ∈ narrow.shading.carrier index →
        paperCloseDirectionCount narrow.shading point index kappa < R := by
    intro point hpoint index hindex
    have hpointBand : point ∈ prepared.band.band.union :=
      ⟨index, narrow.subshading index hindex⟩
    have hmono :
        paperCloseDirectionCount narrow.shading point index kappa ≤
          paperCloseDirectionCount prepared.band.band point index kappa := by
      unfold paperCloseDirectionCount
      apply Finset.card_le_card
      intro other hother
      simp only [Finset.mem_filter] at hother ⊢
      exact ⟨hother.1, narrow.subshading other hother.2.1, hother.2.2⟩
    exact hmono.trans_lt <|
      hclose point hpointBand index (narrow.subshading index hindex)
  have hnarrowMultiplicity : ∀ point ∈ narrow.shading.union,
      narrow.shading.pointMultiplicity point =
        prepared.band.band.pointMultiplicity point :=
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
      hdelta hkappa hfamily
      prepared.band.band_cubical narrow hnarrowClose hnarrowBudget with
    ⟨selected, selection, weakMap, hselectedSub, hselectedCubical,
      _hplaneCell, _hselectionCell, hplaneSelection, _hmultiplicity,
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
  have hhighBand : prepared.high.mass ≤
      bandCount * prepared.band.band.mass := by
    have hdivision := prepared.band.band_mass_retention
    change prepared.high.mass / bandCount ≤ prepared.band.band.mass at hdivision
    rw [ENNReal.div_le_iff hbandCountPos.ne' hbandCountTop] at hdivision
    simpa [mul_comm] using hdivision
  have hbandNarrowSelected : (1 / 8 : ENNReal) *
      prepared.band.band.mass ≤ selected.mass := by
    calc
      (1 / 8 : ENNReal) * prepared.band.band.mass =
          (1 / 4 : ENNReal) *
            ((1 / 2 : ENNReal) * prepared.band.band.mass) := by
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
    have hhalfHigh :=
      mul_le_mul_right prepared.high_mass (1 / 8 : ENNReal)
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
      _ ≤ (1 / 8 : ENNReal) * prepared.high.mass := hhalfHigh
      _ ≤ (1 / 8 : ENNReal) *
          (bandCount * prepared.band.band.mass) := by gcongr
      _ = bandCount *
          ((1 / 8 : ENNReal) * prepared.band.band.mass) := by ring
      _ ≤ bandCount * selected.mass := by gcongr
  let finalMap : PaperWZ1WeakPlaneMapData selected incidenceBudget :=
    paperWeakPlaneMapMono hincidence weakMap
  let data : Proposition63PointwiseWeakMapRefinementData
      source incidenceBudget := {
    shading := selected
    subshading := hselectedSource
    planeMap := finalMap
    leftFactor := 1 / 16
    rightFactor := bandCount
    leftFactor_pos := by norm_num
    leftFactor_ne_top := by norm_num
    rightFactor_ne_top := hbandCountTop
    mass_retention := hmass }
  refine ⟨{
    narrow := narrow
    selection := selection
    data := data
    data_sub_narrow := hselectedSub
    planeMap_eq_normal := ?_
  }, hselectedCubical, rfl, rfl⟩
  funext point
  exact hplaneSelection point

/-- Compatibility projection of the construction-aware producer. -/
theorem proposition63_pointwise_weak_map_from_robust_preparation
    {delta sigma sourceLoss densityLoss kappa theta
      incidenceBudget : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source : WZ1PaperTubeShading family}
    {C : ENNReal}
    (prepared : Proposition63PaperLemma43Preparation
      (sigma := sigma) (sourceLoss := sourceLoss)
      (densityLoss := densityLoss) source)
    (hCV : ∀ (E : Set Point3), MeasurableSet E →
      E ⊆ source.union → ∀ (L : ENNReal),
        (∀ point ∈ E, L ≤
          (paperShadingTrilinearMultiplicity source point) ^
            (1 / 2 : ℝ)) →
        L * volume E ≤
          C * (ENNReal.ofReal (delta ^ 2) * family.enncard) ^
            (3 / 2 : ℝ))
    (hkappa : 0 < kappa)
    (htheta : 0 < theta)
    (hincidence : theta / kappa ≤ incidenceBudget)
    (hm24 : 24 ≤ 2 ^ prepared.band.level)
    (hclose : ∀ point ∈ prepared.band.band.union, ∀ index,
      point ∈ prepared.band.band.carrier index →
        paperCloseDirectionCount prepared.band.band point index kappa <
          (2 ^ prepared.band.level) / 24)
    (hbroadAbsorb :
      let m := 2 ^ prepared.band.level
      let Q : ℕ := m ^ 3 / 4
      (2 : ENNReal) * (2 * m : ℕ) * C *
          (ENNReal.ofReal (delta ^ 2) * family.enncard) ^
            (3 / 2 : ℝ) ≤
        (((Q : ENNReal) * ENNReal.ofReal theta) ^
          (1 / 2 : ℝ)) * prepared.band.band.mass)
    (hdelta : 0 < delta)
    (hfamily : family.Nonempty) :
    ∃ data : Proposition63PointwiseWeakMapRefinementData
        source incidenceBudget,
      WZ1PaperIsCubicalShading data.shading ∧
      data.leftFactor = 1 / 16 ∧
      data.rightFactor =
        ((Nat.log 2 family.card + 1 : ℕ) : ENNReal) := by
  rcases proposition63_pointwise_weak_map_from_robust_preparation_with_witness
      (incidenceBudget := incidenceBudget) prepared hCV hkappa htheta
      hincidence hm24 hclose hbroadAbsorb
      hdelta hfamily with ⟨witness, hcubical, hleft, hright⟩
  exact ⟨witness.data, hcubical, hleft, hright⟩

/-- Restore the Proposition 6.3 extremality wrapper around the robust
pointwise weak-plane-map core. -/
theorem proposition63_paper_lemma43_from_robust_preparation
    {delta sigma sourceLoss targetLoss densityLoss kappa theta
      incidenceBudget : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source : WZ1PaperTubeShading family}
    {C : ENNReal}
    (sourceExtremal : WZ2PaperCroppedIsExtremal
      sigma sourceLoss family source)
    (prepared : Proposition63PaperLemma43Preparation
      (sigma := sigma) (sourceLoss := sourceLoss)
      (densityLoss := densityLoss) source)
    (hCV : ∀ (E : Set Point3), MeasurableSet E →
      E ⊆ source.union → ∀ (L : ENNReal),
        (∀ point ∈ E, L ≤
          (paperShadingTrilinearMultiplicity source point) ^
            (1 / 2 : ℝ)) →
        L * volume E ≤
          C * (ENNReal.ofReal (delta ^ 2) * family.enncard) ^
            (3 / 2 : ℝ))
    (hkappa : 0 < kappa)
    (htheta : 0 < theta)
    (hincidence : theta / kappa ≤ incidenceBudget)
    (hm24 : 24 ≤ 2 ^ prepared.band.level)
    (hclose : ∀ point ∈ prepared.band.band.union, ∀ index,
      point ∈ prepared.band.band.carrier index →
        paperCloseDirectionCount prepared.band.band point index kappa <
          (2 ^ prepared.band.level) / 24)
    (hbroadAbsorb :
      let m := 2 ^ prepared.band.level
      let Q : ℕ := m ^ 3 / 4
      (2 : ENNReal) * (2 * m : ℕ) * C *
          (ENNReal.ofReal (delta ^ 2) * family.enncard) ^
            (3 / 2 : ℝ) ≤
        (((Q : ENNReal) * ENNReal.ofReal theta) ^
          (1 / 2 : ℝ)) * prepared.band.band.mass)
    (htargetLoss : 0 < targetLoss)
    (hsourceTarget : sourceLoss ≤ targetLoss)
    (hrestore :
      proposition63PaperLemma43MassLoss
          (source := source) prepared.high prepared.band *
        Kakeya.realRpowENN delta targetLoss ≤
      Kakeya.realRpowENN delta sourceLoss) :
    Nonempty (Proposition63Lemma43Data
      (sigma := sigma) (sourceLoss := sourceLoss)
      (targetLoss := targetLoss) source incidenceBudget) := by
  rcases proposition63_pointwise_weak_map_from_robust_preparation
      prepared hCV hkappa htheta hincidence hm24 hclose hbroadAbsorb
      sourceExtremal.delta_pos sourceExtremal.nonempty with
    ⟨pointwise, hselectedCubical, hleftFactor, hrightFactor⟩
  let selected := pointwise.shading
  let bandCount := pointwise.rightFactor
  let massLoss := proposition63Lemma43MassLoss
    pointwise.leftFactor pointwise.rightFactor
  have hmassLossPos : 0 < massLoss :=
    proposition63Lemma43MassLoss_pos _ _
  have hmassLossTop : massLoss ≠ ⊤ :=
    proposition63Lemma43MassLoss_ne_top pointwise.leftFactor_pos
      pointwise.rightFactor_ne_top
  have hinverse : massLoss⁻¹ * source.mass ≤ selected.mass :=
    proposition63Lemma43MassLoss_inv_mul_le
      pointwise.leftFactor_pos pointwise.leftFactor_ne_top
        pointwise.rightFactor_ne_top
        pointwise.mass_retention
  have hextremal : WZ2PaperCroppedIsExtremal
      sigma targetLoss family selected := by
    apply transfer_cropped_extremal_to_subshading massLoss
      hmassLossPos hmassLossTop sourceExtremal pointwise.subshading
      hinverse hselectedCubical hsourceTarget
    · simpa [massLoss, hleftFactor, hrightFactor,
        proposition63PaperLemma43MassLoss] using hrestore
    · exact sourceExtremal.delta_pos
    · exact sourceExtremal.delta_le_one
    · exact htargetLoss
  exact ⟨{
    shading := selected
    subshading := pointwise.subshading
    planeMap := pointwise.planeMap
    leftFactor := pointwise.leftFactor
    rightFactor := bandCount
    leftFactor_pos := pointwise.leftFactor_pos
    leftFactor_ne_top := pointwise.leftFactor_ne_top
    rightFactor_ne_top := pointwise.rightFactor_ne_top
    mass_retention := pointwise.mass_retention
    cubical := hselectedCubical
    extremal := hextremal }⟩

/-- Construction-aware extremality wrapper.  Unlike the compatibility
theorem above, this retains the actual Lemma 4.3 transverse pair. -/
theorem proposition63_paper_lemma43_witness_from_robust_preparation
    {delta sigma sourceLoss targetLoss densityLoss kappa theta
      incidenceBudget : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source : WZ1PaperTubeShading family}
    {C : ENNReal}
    (sourceExtremal : WZ2PaperCroppedIsExtremal
      sigma sourceLoss family source)
    (prepared : Proposition63PaperLemma43Preparation
      (sigma := sigma) (sourceLoss := sourceLoss)
      (densityLoss := densityLoss) source)
    (hCV : ∀ (E : Set Point3), MeasurableSet E →
      E ⊆ source.union → ∀ (L : ENNReal),
        (∀ point ∈ E, L ≤
          (paperShadingTrilinearMultiplicity source point) ^
            (1 / 2 : ℝ)) →
        L * volume E ≤
          C * (ENNReal.ofReal (delta ^ 2) * family.enncard) ^
            (3 / 2 : ℝ))
    (hkappa : 0 < kappa)
    (htheta : 0 < theta)
    (hincidence : theta / kappa ≤ incidenceBudget)
    (hm24 : 24 ≤ 2 ^ prepared.band.level)
    (hclose : ∀ point ∈ prepared.band.band.union, ∀ index,
      point ∈ prepared.band.band.carrier index →
        paperCloseDirectionCount prepared.band.band point index kappa <
          (2 ^ prepared.band.level) / 24)
    (hbroadAbsorb :
      let m := 2 ^ prepared.band.level
      let Q : ℕ := m ^ 3 / 4
      (2 : ENNReal) * (2 * m : ℕ) * C *
          (ENNReal.ofReal (delta ^ 2) * family.enncard) ^
            (3 / 2 : ℝ) ≤
        (((Q : ENNReal) * ENNReal.ofReal theta) ^
          (1 / 2 : ℝ)) * prepared.band.band.mass)
    (htargetLoss : 0 < targetLoss)
    (hsourceTarget : sourceLoss ≤ targetLoss)
    (hrestore :
      proposition63PaperLemma43MassLoss
          (source := source) prepared.high prepared.band *
        Kakeya.realRpowENN delta targetLoss ≤
      Kakeya.realRpowENN delta sourceLoss) :
    Nonempty (Proposition63M9Lemma43Witness
      (source := source) (band := prepared.band.band)
      (sigma := sigma) (sourceLoss := sourceLoss)
      (targetLoss := targetLoss) (kappa := kappa)
      (theta := theta) (incidenceBudget := incidenceBudget)
      (Q := (2 ^ prepared.band.level) ^ 3 / 4)) := by
  rcases proposition63_pointwise_weak_map_from_robust_preparation_with_witness
      (incidenceBudget := incidenceBudget) prepared hCV hkappa htheta
      hincidence hm24 hclose hbroadAbsorb sourceExtremal.delta_pos
      sourceExtremal.nonempty with
    ⟨pointwise, hselectedCubical, hleftFactor, hrightFactor⟩
  let selected := pointwise.data.shading
  let massLoss := proposition63Lemma43MassLoss
    pointwise.data.leftFactor pointwise.data.rightFactor
  have hmassLossPos : 0 < massLoss :=
    proposition63Lemma43MassLoss_pos _ _
  have hmassLossTop : massLoss ≠ ⊤ :=
    proposition63Lemma43MassLoss_ne_top pointwise.data.leftFactor_pos
      pointwise.data.rightFactor_ne_top
  have hinverse : massLoss⁻¹ * source.mass ≤ selected.mass :=
    proposition63Lemma43MassLoss_inv_mul_le
      pointwise.data.leftFactor_pos pointwise.data.leftFactor_ne_top
      pointwise.data.rightFactor_ne_top pointwise.data.mass_retention
  have hextremal : WZ2PaperCroppedIsExtremal
      sigma targetLoss family selected := by
    apply transfer_cropped_extremal_to_subshading massLoss
      hmassLossPos hmassLossTop sourceExtremal pointwise.data.subshading
      hinverse hselectedCubical hsourceTarget
    · simpa [massLoss, hleftFactor, hrightFactor,
        proposition63PaperLemma43MassLoss] using hrestore
    · exact sourceExtremal.delta_pos
    · exact sourceExtremal.delta_le_one
    · exact htargetLoss
  let lemma43 : Proposition63Lemma43Data
      (sigma := sigma) (sourceLoss := sourceLoss)
      (targetLoss := targetLoss) source incidenceBudget := {
    shading := selected
    subshading := pointwise.data.subshading
    planeMap := pointwise.data.planeMap
    leftFactor := pointwise.data.leftFactor
    rightFactor := pointwise.data.rightFactor
    leftFactor_pos := pointwise.data.leftFactor_pos
    leftFactor_ne_top := pointwise.data.leftFactor_ne_top
    rightFactor_ne_top := pointwise.data.rightFactor_ne_top
    mass_retention := pointwise.data.mass_retention
    cubical := hselectedCubical
    extremal := hextremal }
  exact ⟨{ pointwise := pointwise, lemma43 := lemma43, planeMap_eq := rfl }⟩

end Kakeya.Assouad.PureWZ2

end
