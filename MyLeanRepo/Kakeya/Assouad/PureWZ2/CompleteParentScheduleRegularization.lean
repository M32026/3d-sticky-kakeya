import MyLeanRepo.Kakeya.Assouad.PureWZ2.PureCompleteParentRestriction
import MyLeanRepo.Kakeya.Assouad.PureWZ2.PureCWARoundingFromSelectedUniform
import MyLeanRepo.Kakeya.Assouad.PureWZ2.PureNearbyTree
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperFiniteWeightedDegreeSelection

/-!
# Multiscale regularization with complete actual fibers as atoms

Fix one actual Definition 2.12 cover.  The finite regularizer acts on its
parents, never on individual fine tubes.  Selecting a parent retains its
entire complete strict fiber.

At each scheduled scale there are two valid geometric cases:

* the scheduled scale is sufficiently finer than the actual scale, so every
  scheduled fiber lies inside one actual fiber and is retained in full;
* the scheduled scale is sufficiently coarser, so every actual fiber lies
  inside one scheduled fiber and selected scheduled-fiber cardinality is a
  weighted sum of selected actual-fiber cardinalities.

The first case inherits ambient uniformity without loss.  The second combines
ambient actual-fiber uniformity with simultaneous degree uniformity of the
selected actual parents.  Rounding then supplies pure CWA at every requested
scale.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

/-- Common weight-retention loss of complete-parent schedule regularization. -/
def pureWZ2CompleteParentRegularizationLoss
    (actualParentCount coordinateCount : ℕ) : ENNReal :=
  8 *
    (Nat.log 2 (2 * actualParentCount) + 1 : ENNReal) ^
      (coordinateCount + 1)

/-- Degree loss actually produced by complete-parent schedule selection. -/
def pureWZ2CompleteParentDegreeConstant
    (actualParentCount coordinateCount : ℕ) : ENNReal :=
  16 * (coordinateCount : ENNReal) *
    (Nat.log 2 (2 * actualParentCount) + 1 : ENNReal) ^
      coordinateCount

/--
Select complete actual fibers with external-weight retention and recover pure
CWA at every nearby scale.
-/
theorem complete_parent_schedule_regularization
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant outputConstant R : ENNReal}
    (ambient :
      WZ2PaperPureCWAAtNearbyScales fine ambientConstant)
    {actualRequested : WZ2PaperRequestedScale delta}
    (actualNearby :
      WZ2PaperPureNearbyScaleCoverData
        fine actualRequested ambientConstant)
    (fineNonempty : fine.Nonempty)
    (actualWeight :
      Fin actualNearby.scaleData.coarse.card → ENNReal)
    (normalizationWeight weightUpper : ENNReal)
    (normalizationWeight_ne_zero :
      normalizationWeight ≠ 0)
    (normalizationWeight_ne_top :
      normalizationWeight ≠ ⊤)
    (weightUpper_ne_top : weightUpper ≠ ⊤)
    (totalWeightLower :
      normalizationWeight * fine.enncard ≤
        ∑ parent : Fin actualNearby.scaleData.coarse.card,
          actualWeight parent)
    (weightUpperByFiber :
      ∀ parent,
        actualWeight parent ≤
          weightUpper *
            wz2PaperOrdinaryFullFiberCount
              fine actualNearby.scaleData.coarse parent)
    (coordinateCount : ℕ)
    (coordinateCountPos : 0 < coordinateCount)
    (scales :
      Fin coordinateCount → WZ2PaperRequestedScale delta)
    (scheduled :
      ∀ coordinate : Fin coordinateCount,
        WZ2PaperPureNearbyScaleCoverData
          fine (scales coordinate) ambientConstant)
    (scaleGap :
      ∀ coordinate : Fin coordinateCount,
        4 * ((scheduled coordinate).rho - delta) ≤
            actualNearby.rho ∨
          4 * (actualNearby.rho - delta) ≤
            (scheduled coordinate).rho)
    (R_pos : 0 < R)
    (R_ne_top : R ≠ ⊤)
    (R_one : 1 ≤ R)
    (rounding :
      ∀ requested : WZ2PaperRequestedScale delta,
        ∃ coordinate : Fin coordinateCount,
          requested.1 ≤ (scales coordinate).1 ∧
          ENNReal.ofReal (scales coordinate).1 <
            R * ENNReal.ofReal requested.1)
    (window_absorption :
      R * ambientConstant ≤ outputConstant)
    (output_ne_top : outputConstant ≠ ⊤)
    (restriction_absorption :
      wz2PaperPureNearbyRestrictionConstant
          ambientConstant normalizationWeight
          (max ambientConstant
            (ambientConstant *
              pureWZ2CompleteParentDegreeConstant
                actualNearby.scaleData.coarse.card coordinateCount))
          (pureWZ2CompleteParentRegularizationLoss
              actualNearby.scaleData.coarse.card coordinateCount *
            weightUpper) ≤
        outputConstant) :
    ∃ (selectedActualParents :
        Finset (Fin actualNearby.scaleData.coarse.card))
      (complete :
        PureWZ2CompleteParentRestrictionData
          actualNearby.scaleData.cover selectedActualParents)
      (degreeConstant regularizationLoss selectedWeightLevel : ENNReal),
      degreeConstant ≠ ⊤ ∧
      regularizationLoss ≠ ⊤ ∧
      regularizationLoss =
        pureWZ2CompleteParentRegularizationLoss
          actualNearby.scaleData.coarse.card coordinateCount ∧
      0 < selectedWeightLevel ∧
      selectedWeightLevel ≠ ⊤ ∧
      (∀ parent ∈ selectedActualParents,
        0 < actualWeight parent) ∧
      (∑ parent : Fin actualNearby.scaleData.coarse.card,
          actualWeight parent) ≤
        regularizationLoss *
          ∑ parent ∈ selectedActualParents,
            actualWeight parent ∧
      (∀ parent ∈ selectedActualParents,
        selectedWeightLevel ≤ actualWeight parent ∧
          actualWeight parent ≤ 2 * selectedWeightLevel) ∧
      normalizationWeight * fine.enncard ≤
        (regularizationLoss * weightUpper) *
          complete.selectedFine.family.enncard ∧
      WZ2PaperPureCWAAtNearbyScales
        complete.selectedFine.family outputConstant := by
  have actualFibersNonempty :
      ∀ parent : Fin actualNearby.scaleData.coarse.card,
        (wz2PaperOrdinaryFullFiberIndices
          fine actualNearby.scaleData.coarse parent).Nonempty :=
    actualNearby.scaleData.cover
      |>.fullFiber_nonempty_of_uniform
        fineNonempty
        actualNearby.scaleData.full_fiber_uniform
  let representative :
      Fin actualNearby.scaleData.coarse.card → Fin fine.card :=
    fun parent =>
      Classical.choose (actualFibersNonempty parent)
  have representativeParent :
      ∀ parent,
        actualNearby.scaleData.cover.parent
            (representative parent) = parent := by
    intro parent
    exact
      (actualNearby.scaleData.cover.mem_fullFiber_iff_parent_eq
        actualNearby.scaleData.rho_pos.le parent
        (representative parent)).mp
        (Classical.choose_spec
          (actualFibersNonempty parent))
  let Vertex : Fin coordinateCount → Type :=
    fun coordinate =>
      Fin (scheduled coordinate).scaleData.coarse.card
  let parent :
      ∀ coordinate,
        Fin actualNearby.scaleData.coarse.card →
          Vertex coordinate :=
    fun coordinate actualParent =>
      (scheduled coordinate).scaleData.cover.parent
        (representative actualParent)
  rcases
      wz2_finite_weighted_degree_selection
        coordinateCount Vertex parent actualWeight
        coordinateCountPos
    with
    ⟨regularized⟩
  let selectedActualParents := regularized.selected
  let degreeConstant : ENNReal :=
    pureWZ2CompleteParentDegreeConstant
      actualNearby.scaleData.coarse.card coordinateCount
  let regularizationLoss : ENNReal :=
    pureWZ2CompleteParentRegularizationLoss
      actualNearby.scaleData.coarse.card coordinateCount
  have fineENNPos : 0 < fine.enncard := by
    change (0 : ENNReal) < (fine.card : ENNReal)
    exact_mod_cast fineNonempty
  have totalWeightPos :
      0 <
        ∑ parent : Fin actualNearby.scaleData.coarse.card,
          actualWeight parent :=
    (ENNReal.mul_pos
      normalizationWeight_ne_zero fineENNPos.ne').trans_le
      totalWeightLower
  have selectedParentsNonempty :
      selectedActualParents.Nonempty := by
    by_contra hnonempty
    have selectedEmpty :
        regularized.selected = ∅ := by
      simpa [selectedActualParents] using hnonempty
    have retained := regularized.retained_weight
    rw [selectedEmpty] at retained
    simp only [Finset.sum_empty, mul_zero] at retained
    exact (not_le_of_gt totalWeightPos) retained
  let complete :=
    PureWZ2CompleteParentRestrictionData.pureWZ2CompleteParentRestriction
      actualNearby.scaleData.cover
      selectedActualParents selectedParentsNonempty
  have selectedFineNonempty :
      complete.selectedFine.family.Nonempty := by
    rcases selectedParentsNonempty with
      ⟨actualParent, actualParentMem⟩
    let ambientSource := representative actualParent
    have sourceSelected :
        ambientSource ∈ complete.selectedFineIndices := by
      unfold
        PureWZ2CompleteParentRestrictionData.selectedFineIndices
      exact
        Finset.mem_filter.mpr
          ⟨Finset.mem_univ ambientSource,
            representativeParent actualParent ▸
              actualParentMem⟩
    rcases
        complete.selectedFine_ambient_surjective
          ambientSource sourceSelected
      with
      ⟨selectedSource, _⟩
    exact Fin.pos_iff_nonempty.mpr ⟨selectedSource⟩
  have degreeTop : degreeConstant ≠ ⊤ :=
    ENNReal.coe_ne_top
  have regularizationTop :
      regularizationLoss ≠ ⊤ :=
    ENNReal.coe_ne_top
  have retainedWeight :
      (∑ parent : Fin actualNearby.scaleData.coarse.card,
          actualWeight parent) ≤
        regularizationLoss *
          ∑ parent ∈ selectedActualParents,
            actualWeight parent := by
    have retained := regularized.retained_weight
    have cardFin :
        Fintype.card
            (Fin actualNearby.scaleData.coarse.card) =
          actualNearby.scaleData.coarse.card := by
      simp
    simpa [selectedActualParents, regularizationLoss,
      pureWZ2CompleteParentRegularizationLoss,
      cardFin] using retained
  have selectedWeightBand :
      ∀ parent ∈ selectedActualParents,
        regularized.weightLevel ≤ actualWeight parent ∧
          actualWeight parent ≤
            2 * regularized.weightLevel := by
    intro parent hparent
    exact regularized.weight_band parent hparent
  have selectedWeightLevelTop :
      regularized.weightLevel ≠ ⊤ := by
    rcases selectedParentsNonempty with
      ⟨parent, hparent⟩
    have lower := (selectedWeightBand parent hparent).1
    have parentWeightTop :
        actualWeight parent ≠ ⊤ :=
      ne_top_of_le_ne_top
        (ENNReal.mul_ne_top weightUpper_ne_top (by
          rw [wz2PaperOrdinaryFullFiberCount]
          simp))
        (weightUpperByFiber parent)
    intro htop
    rw [htop] at lower
    exact parentWeightTop (top_unique lower)
  have selectedWeightUpper :
      (∑ parent ∈ selectedActualParents,
          actualWeight parent) ≤
        weightUpper *
          complete.selectedFine.family.enncard := by
    calc
      (∑ parent ∈ selectedActualParents,
          actualWeight parent) ≤
          ∑ parent ∈ selectedActualParents,
            weightUpper *
              wz2PaperOrdinaryFullFiberCount
                fine actualNearby.scaleData.coarse parent := by
        exact
          Finset.sum_le_sum fun parent _ =>
            weightUpperByFiber parent
      _ =
          weightUpper *
            ∑ parent ∈ selectedActualParents,
              wz2PaperOrdinaryFullFiberCount
                fine actualNearby.scaleData.coarse parent := by
        rw [Finset.mul_sum]
      _ =
          weightUpper *
            complete.selectedFine.family.enncard := by
        rw [
          complete.selectedFine_enncard_eq_sum_actual_fullFiberCount
            actualNearby.scaleData.rho_pos.le
        ]
  have cardinalityRetention :
      normalizationWeight * fine.enncard ≤
        (regularizationLoss * weightUpper) *
          complete.selectedFine.family.enncard := by
    calc
      normalizationWeight * fine.enncard ≤
          ∑ parent : Fin actualNearby.scaleData.coarse.card,
            actualWeight parent :=
        totalWeightLower
      _ ≤
          regularizationLoss *
            ∑ parent ∈ selectedActualParents,
              actualWeight parent :=
        retainedWeight
      _ ≤
          regularizationLoss *
            (weightUpper *
              complete.selectedFine.family.enncard) := by
        gcongr
      _ =
          (regularizationLoss * weightUpper) *
            complete.selectedFine.family.enncard := by
        ring
  let selectedConstant :=
    max ambientConstant
      (ambientConstant * degreeConstant)
  have selectedConstantTop :
      selectedConstant ≠ ⊤ :=
    max_ne_top ambient.2.1.2
      (ENNReal.mul_ne_top ambient.2.1.2 degreeTop)
  have selectedUniform :
      ∀ coordinate : Fin coordinateCount,
        WZ2PaperPureFullFibersAreCUniform
          complete.selectedFine.family
          ((scheduled coordinate).scaleData.cover
            |>.hitParentSubfamily complete.selectedFine).family
          selectedConstant := by
    intro coordinate
    rcases scaleGap coordinate with finerGap | coarserGap
    · have nested :
          ∀ first second,
            (scheduled coordinate).scaleData.cover.parent first =
                (scheduled coordinate).scaleData.cover.parent second →
              actualNearby.scaleData.cover.parent first =
                actualNearby.scaleData.cover.parent second :=
        (scheduled coordinate).scaleData.cover
          |>.parent_maps_nested_of_gap
            actualNearby.scaleData.cover
            ambient.1.le
            (scheduled coordinate).scaleData.rho_pos
            actualNearby.scaleData.rho_pos
            ((scales coordinate).2.1.trans
              (scheduled coordinate).requested_le)
            (actualRequested.2.1.trans
              actualNearby.requested_le)
            finerGap
      have raw :=
        complete.finer_restricted_fullFiber_uniform
          (scheduled coordinate).scaleData.cover
          (scheduled coordinate).scaleData.rho_pos.le
          nested
          (scheduled coordinate).scaleData.full_fiber_uniform
      intro first second
      exact
        (raw first second).trans <| by
          gcongr
          exact le_max_left _ _
    · have nested :
          ∀ first second,
            actualNearby.scaleData.cover.parent first =
                actualNearby.scaleData.cover.parent second →
              (scheduled coordinate).scaleData.cover.parent first =
                (scheduled coordinate).scaleData.cover.parent second :=
        actualNearby.scaleData.cover
          |>.parent_maps_nested_of_gap
            (scheduled coordinate).scaleData.cover
            ambient.1.le
            actualNearby.scaleData.rho_pos
            (scheduled coordinate).scaleData.rho_pos
            (actualRequested.2.1.trans
              actualNearby.requested_le)
            ((scales coordinate).2.1.trans
              (scheduled coordinate).requested_le)
            coarserGap
      have compatible :
          ∀ source,
            parent coordinate
                (actualNearby.scaleData.cover.parent source) =
              (scheduled coordinate).scaleData.cover.parent source := by
        intro source
        apply nested
        exact
          representativeParent
            (actualNearby.scaleData.cover.parent source)
      have degreeUniform :
          ∀ first second,
            0 <
                (selectedActualParents.filter fun actualParent =>
                  parent coordinate actualParent = first).card →
            0 <
                (selectedActualParents.filter fun actualParent =>
                  parent coordinate actualParent = second).card →
            ((selectedActualParents.filter fun actualParent =>
              parent coordinate actualParent = first).card : ENNReal) ≤
              degreeConstant *
                ((selectedActualParents.filter fun actualParent =>
                  parent coordinate actualParent = second).card : ENNReal) := by
        intro first second hfirst hsecond
        have raw :=
          regularized.degree_uniform
            coordinate first second hfirst hsecond
        have cardFin :
            Fintype.card
                (Fin actualNearby.scaleData.coarse.card) =
              actualNearby.scaleData.coarse.card := by
          simp
        simpa [selectedActualParents, degreeConstant,
          pureWZ2CompleteParentDegreeConstant, cardFin] using raw
      have raw :=
        complete.coarser_restricted_fullFiber_uniform
          (scheduled coordinate).scaleData.cover
          (parent coordinate) compatible
          actualNearby.scaleData.rho_pos.le
          (scheduled coordinate).scaleData.rho_pos.le
          actualNearby.scaleData.full_fiber_uniform
          degreeUniform
      intro first second
      exact
        (raw first second).trans <| by
          gcongr
          exact le_max_right _ _
  have restrictedAbsorption :
      wz2PaperPureNearbyRestrictionConstant
          ambientConstant normalizationWeight
          selectedConstant
          (regularizationLoss * weightUpper) ≤
        outputConstant :=
    restriction_absorption
  have selectedCWA :
      WZ2PaperPureCWAAtNearbyScales
        complete.selectedFine.family outputConstant :=
    pure_cwa_restrict_with_rounding_of_selected_uniform
      ambient complete.selectedFine selectedFineNonempty
      coordinateCount coordinateCountPos scales scheduled
      selectedConstant
      (regularizationLoss * weightUpper)
      normalizationWeight
      normalizationWeight_ne_zero
      normalizationWeight_ne_top
      (ENNReal.mul_ne_top
        regularizationTop weightUpper_ne_top)
      selectedConstantTop
      cardinalityRetention selectedUniform
      R_pos R_ne_top R_one rounding
      window_absorption output_ne_top
      restrictedAbsorption
  exact
    ⟨selectedActualParents, complete,
      degreeConstant, regularizationLoss,
      regularized.weightLevel,
      degreeTop, regularizationTop,
      rfl,
      regularized.weightLevel_pos,
      selectedWeightLevelTop,
      (fun parent hparent =>
        regularized.selected_weight_pos parent hparent),
      retainedWeight, selectedWeightBand,
      cardinalityRetention, selectedCWA⟩

end Kakeya.Assouad

end
