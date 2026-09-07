import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.PureFiniteNearbyScheduleRestriction
import MyLeanRepo.Kakeya.Assouad.PropStickyFiniteRegularizedRefinement

/-!
# Whole-tube regularization for a pure finite schedule

Run the finite representative schedule and the simultaneous parent-degree
regularizer on one genuine tube subfamily.  The selected family retains
explicit shaded mass and cardinality and recovers the complete pure
nearby-scale CWA predicate with actual-John strict fibers.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

/-- Whole-tube regularization together with restored pure nearby CWA. -/
structure WZ2PaperPureFiniteRegularizedRefinementData
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (shading : WZ1PaperTubeShading family)
    (density ambientConstant outputConstant : ENNReal)
    (levelCount : ℕ) where
  schedule :
    WZ2PaperPureFiniteNearbyScheduleData
      (fine := family) ambientConstant outputConstant levelCount
  Parent : Fin schedule.scaleCount → Type _
  parent_fintype : ∀ coordinate, Fintype (Parent coordinate)
  parent_decidableEq : ∀ coordinate, DecidableEq (Parent coordinate)
  parent : ∀ coordinate, Fin family.card → Parent coordinate
  regularized :
    @WZ2PaperFiniteRegularizedRefinementData
      delta family shading density schedule.scaleCount Parent
      parent_fintype parent_decidableEq parent
  selected_nonempty : regularized.selected.family.Nonempty
  pure_cwa_nearby :
    WZ2PaperPureCWAAtNearbyScales
      regularized.selected.family outputConstant

/--
Select one whole-tube subfamily which is degree-regular at every finite
representative scale and hence inherits the full pure nearby-scale CWA.
All asymptotic absorption is an explicit premise.
-/
theorem paper_pure_finite_regularized_refinement
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {density ambientConstant outputConstant : ENNReal}
    (shading : WZ1PaperTubeShading family)
    (hdelta : 0 < delta)
    (hdeltaSmall : delta ≤ 1 / 24)
    (hfamilyNonempty : family.Nonempty)
    (hdensityZero : density ≠ 0)
    (hdensityTop : density ≠ ⊤)
    (hline : WZ1PaperIsLineClass family)
    (hcubical : WZ1PaperIsCubicalShading shading)
    (hdense :
      density * family.enncard *
          Kakeya.realRpowENN delta 2 ≤
        shading.mass)
    (levelCount : ℕ)
    (hambientTwo : 2 < ambientConstant)
    (hlevels :
      ENNReal.ofReal (1 / delta) ≤
        ambientConstant ^ levelCount)
    (hwindow :
      ambientConstant * ambientConstant ≤ outputConstant)
    (houtputTop : outputConstant ≠ ⊤)
    (hcwa :
      WZ2PaperPureCWAAtNearbyScales family ambientConstant)
    (habsorb :
      let degreeConstant :=
        16 * ((levelCount + 1 : ℕ) : ENNReal) *
          (Nat.log 2 (2 * family.card) + 1 : ENNReal) ^
            (levelCount + 1)
      let regularizationLoss :=
        (8 : ENNReal) *
          (Nat.log 2 (2 * family.card) + 1 : ENNReal) ^
            (levelCount + 2)
      let weight := (1 / 2 : ENNReal) * density
      let cardinalityLoss :=
        (2 * regularizationLoss) *
          (55296 * Kakeya.deltaTubeVolume 1)
      max degreeConstant
          ((weight⁻¹ *
              (ambientConstant * cardinalityLoss * degreeConstant)) *
            ambientConstant) ≤
        outputConstant) :
    Nonempty
      (WZ2PaperPureFiniteRegularizedRefinementData
        shading density ambientConstant outputConstant levelCount) := by
  have hdeltaOne : delta ≤ 1 := hdeltaSmall.trans (by norm_num)
  rcases paper_pure_finite_nearby_schedule
      levelCount hdelta hdeltaOne hambientTwo hcwa.2.1.2
      hlevels hwindow hcwa with
    ⟨schedule⟩
  let Parent : Fin schedule.scaleCount → Type :=
    fun coordinate =>
      Fin (schedule.witness coordinate).scaleData.coarse.card
  let parent : ∀ coordinate, Fin family.card → Parent coordinate :=
    fun coordinate =>
      (schedule.witness coordinate).scaleData.cover.parent
  rcases wz2PaperFiniteRegularizedRefinement
      hdelta hdeltaSmall hline shading hcubical density hdense
      schedule.scaleCount Parent parent with
    ⟨regularized⟩
  let actualDegreeConstant : ENNReal :=
    16 * (schedule.scaleCount : ENNReal) *
      (Nat.log 2 (2 * family.card) + 1 : ENNReal) ^
        schedule.scaleCount
  let degreeConstant : ENNReal :=
    16 * ((levelCount + 1 : ℕ) : ENNReal) *
      (Nat.log 2 (2 * family.card) + 1 : ENNReal) ^
        (levelCount + 1)
  let actualRegularizationLoss : ENNReal :=
    regularized.regularizationLoss
  let regularizationLoss : ENNReal :=
    (8 : ENNReal) *
      (Nat.log 2 (2 * family.card) + 1 : ENNReal) ^
        (levelCount + 2)
  let weight : ENNReal := (1 / 2 : ENNReal) * density
  let actualCardinalityLoss : ENNReal :=
    (2 * actualRegularizationLoss) *
      (55296 * Kakeya.deltaTubeVolume 1)
  let cardinalityLoss : ENNReal :=
    (2 * regularizationLoss) *
      (55296 * Kakeya.deltaTubeVolume 1)
  have hlogOne :
      (1 : ENNReal) ≤
        (Nat.log 2 (2 * family.card) + 1 : ENNReal) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le _)
  have hscaleCount :
      (schedule.scaleCount : ENNReal) ≤
        ((levelCount + 1 : ℕ) : ENNReal) := by
    exact_mod_cast schedule.scaleCount_le
  have hdegreeConstant :
      actualDegreeConstant ≤ degreeConstant := by
    dsimp only [actualDegreeConstant, degreeConstant]
    calc
      16 * (schedule.scaleCount : ENNReal) *
            (Nat.log 2 (2 * family.card) + 1 : ENNReal) ^
              schedule.scaleCount
          ≤ 16 * ((levelCount + 1 : ℕ) : ENNReal) *
            (Nat.log 2 (2 * family.card) + 1 : ENNReal) ^
              schedule.scaleCount := by gcongr
      _ ≤ 16 * ((levelCount + 1 : ℕ) : ENNReal) *
            (Nat.log 2 (2 * family.card) + 1 : ENNReal) ^
              (levelCount + 1) := by
        exact mul_le_mul_left'
          (pow_le_pow_right' hlogOne schedule.scaleCount_le) _
  have hregularizationLoss :
      actualRegularizationLoss ≤ regularizationLoss := by
    rw [show actualRegularizationLoss =
        regularized.regularizationLoss by rfl,
      regularized.regularizationLoss_eq]
    dsimp only [regularizationLoss]
    have hexponent :
        schedule.scaleCount + 1 ≤ levelCount + 2 := by
      exact Nat.add_le_add_right schedule.scaleCount_le 1
    exact mul_le_mul_left'
      (pow_le_pow_right' hlogOne hexponent) _
  have hcardinality :
      weight * family.enncard ≤
        cardinalityLoss * regularized.selected.family.enncard := by
    exact regularized.cardinality_retention.trans (by
      dsimp only [weight, cardinalityLoss, actualCardinalityLoss,
        actualRegularizationLoss]
      gcongr)
  have hweightZero : weight ≠ 0 := by
    dsimp only [weight]
    exact mul_ne_zero (by norm_num) hdensityZero
  have hweightTop : weight ≠ ⊤ := by
    dsimp only [weight]
    exact ENNReal.mul_ne_top (by norm_num) hdensityTop
  have hfamilyCardPositive : 0 < family.enncard := by
    change 0 < (family.card : ENNReal)
    exact_mod_cast hfamilyNonempty
  have hselectedNonempty : regularized.selected.family.Nonempty := by
    have hleftPositive :
        0 < weight * family.enncard :=
      ENNReal.mul_pos hweightZero hfamilyCardPositive.ne'
    have hrightPositive :
        0 < cardinalityLoss * regularized.selected.family.enncard :=
      hleftPositive.trans_le hcardinality
    have hselectedCardPositive :
        0 < regularized.selected.family.enncard := by
      by_contra hnot
      have hzero : regularized.selected.family.enncard = 0 := by
        simpa [not_lt] using hnot
      rw [hzero, mul_zero] at hrightPositive
      exact (lt_irrefl 0) hrightPositive
    simpa [Kakeya.Streamlined.TubeFamily.Nonempty,
      Kakeya.Streamlined.TubeFamily.enncard] using hselectedCardPositive
  have hdegree :
      ∀ coordinate,
        ∀ first second :
            Fin (schedule.witness coordinate).scaleData.coarse.card,
          0 <
              ((Finset.univ :
                Finset (Fin regularized.selected.family.card)).filter
                fun source =>
                  (schedule.witness coordinate).scaleData.cover.parent
                      (regularized.selected.embedding source) =
                    first).card →
            0 <
              ((Finset.univ :
                Finset (Fin regularized.selected.family.card)).filter
                fun source =>
                  (schedule.witness coordinate).scaleData.cover.parent
                      (regularized.selected.embedding source) =
                    second).card →
            (((Finset.univ :
              Finset (Fin regularized.selected.family.card)).filter
              fun source =>
                (schedule.witness coordinate).scaleData.cover.parent
                    (regularized.selected.embedding source) =
                  first).card : ENNReal) ≤
              degreeConstant *
                (((Finset.univ :
                  Finset (Fin regularized.selected.family.card)).filter
                  fun source =>
                    (schedule.witness coordinate).scaleData.cover.parent
                        (regularized.selected.embedding source) =
                      second).card : ENNReal) := by
    intro coordinate first second hfirst hsecond
    exact
      (regularized.degree_uniform coordinate first second
        hfirst hsecond).trans (by gcongr)
  have hpureCWA :
      WZ2PaperPureCWAAtNearbyScales
        regularized.selected.family outputConstant :=
    schedule.regularize hcwa regularized.selected hselectedNonempty
      ⟨hcwa.2.1.1.trans <|
          calc
            ambientConstant ≤ ambientConstant * ambientConstant := by
              exact le_mul_of_one_le_right' hcwa.2.1.1
            _ ≤ outputConstant := hwindow,
        houtputTop⟩
      hweightZero hweightTop hcardinality hdegree (by
        simpa [degreeConstant, regularizationLoss, weight,
          cardinalityLoss] using habsorb)
  exact
    ⟨{
      schedule := schedule
      Parent := Parent
      parent_fintype := inferInstance
      parent_decidableEq := inferInstance
      parent := parent
      regularized := regularized
      selected_nonempty := hselectedNonempty
      pure_cwa_nearby := hpureCWA
    }⟩

end Kakeya.Assouad

end
