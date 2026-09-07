import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63ExtremalOneScalePlaneMap
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.DyadicPropertyThreeMass

/-!
# Paper coarse-to-fine density lift for Proposition 6.3

The whole-cell pullback has two logically separate ledgers.  Its raw mass
comparison records the ancestry and cardinality costs, while extremality is
recovered from the actual fine-family cardinality after the common
`delta ^ 2` tube-volume factor has been cancelled.  This module packages the
second argument and keeps the raw comparison only as an iterator receipt.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory Set

/-- Extremality of an actual coarse candidate forces a family-free fraction
of the balanced active cells to be good.  The coarse-family cardinality is
cancelled between the candidate density lower bound and the sticky
multiplicity upper bound; it does not survive in the conclusion. -/
theorem proposition63_paper_coarseCandidate_goodCells_fraction
    {delta sigma stickyLoss coarseLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading source}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    (sticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := stickyLoss)
      sourceShading rho logExponent)
    (candidate : WZ1PaperTubeShading sticky.coarse)
    (candidateExtremal : WZ2PaperCroppedIsExtremal
      sigma coarseLoss sticky.coarse candidate)
    (candidateSub : PaperIsSubshading
      candidate sticky.croppedCoarseShading)
    (candidateCubical : WZ1PaperIsCubicalShading candidate)
    (hrhoSmall : rho.1 ≤ 1 / 12) :
    Kakeya.realRpowENN rho.1 (coarseLoss + 2 * stickyLoss) *
        (sticky.balanced.activeCells.card : ENNReal) ≤
      ((propertyThreeGoodCells sticky.balanced candidate).card :
        ENNReal) := by
  let active : ENNReal := sticky.balanced.activeCells.card
  let good : ENNReal :=
    (propertyThreeGoodCells sticky.balanced candidate).card
  let cubeVolume : ENNReal :=
    volume (wz1PaperGridCube rho.1 (0, 0, 0))
  let coarseCard : ENNReal := sticky.coarse.enncard
  let coarsePower : ENNReal :=
    Kakeya.realRpowENN rho.1 (2 - sigma - stickyLoss)
  have hrho : 0 < rho.1 := sticky.coarse_extremal.delta_pos
  have hcube : cubeVolume = Kakeya.realRpowENN rho.1 3 := by
    dsimp only [cubeVolume]
    rw [wz1PaperGridCube_volume_exact hrho]
    simp [Kakeya.realRpowENN, Real.rpow_natCast]
  have hcardZero : coarseCard ≠ 0 := by
    dsimp only [coarseCard]
    simpa [Kakeya.Streamlined.TubeFamily.enncard] using
      candidateExtremal.nonempty.ne'
  have hcardTop : coarseCard ≠ ⊤ := by
    simp [coarseCard, Kakeya.Streamlined.TubeFamily.enncard]
  have hcandidateLower :
      Kakeya.realRpowENN rho.1 (coarseLoss + 2) * coarseCard ≤
        candidate.mass := by
    calc
      Kakeya.realRpowENN rho.1 (coarseLoss + 2) * coarseCard =
          Kakeya.realRpowENN rho.1 coarseLoss *
            (Kakeya.realRpowENN rho.1 2 * coarseCard) := by
        rw [Kakeya.Assouad.realRpowENN_add hrho coarseLoss 2]
        ring
      _ ≤ Kakeya.realRpowENN rho.1 coarseLoss *
          (wz1PaperBodyFamily sticky.coarse).mass := by
        gcongr
        exact paperBodyFamily_mass_lower_rpow_two hrho hrhoSmall
          sticky.cover.coarse_line_class
      _ ≤ candidate.mass := candidateExtremal.dense
  have hcandidateUpper : candidate.mass ≤
      (coarsePower * coarseCard) * (good * cubeVolume) := by
    calc
      candidate.mass ≤ (coarsePower * coarseCard) *
          volume candidate.union := by
        apply mass_le_of_pointMultiplicity_le
        intro point hpoint
        have hsubMultiplicity := paperSubshading_pointMultiplicity_le
          candidate sticky.croppedCoarseShading candidateSub point
        have hcast : (candidate.pointMultiplicity point : ENNReal) ≤
            (sticky.croppedCoarseShading.pointMultiplicity point :
              ENNReal) := by
          exact_mod_cast hsubMultiplicity
        exact hcast.trans (sticky.coarse_multiplicity_upper point)
      _ = (coarsePower * coarseCard) * (good * cubeVolume) := by
        rw [propertyThree_volume_eq_goodCells sticky.balanced
          candidateSub candidateCubical hrho]
  have hcandidateNoCard :
      Kakeya.realRpowENN rho.1 (coarseLoss + 2) ≤
        coarsePower * (good * cubeVolume) := by
    apply (ENNReal.mul_le_mul_iff_right hcardZero hcardTop).mp
    simpa only [mul_assoc, mul_comm, mul_left_comm] using (show
      Kakeya.realRpowENN rho.1 (coarseLoss + 2) * coarseCard ≤
          (coarsePower * (good * cubeVolume)) * coarseCard from by
        calc
          Kakeya.realRpowENN rho.1 (coarseLoss + 2) * coarseCard ≤
              candidate.mass := hcandidateLower
          _ ≤ (coarsePower * coarseCard) * (good * cubeVolume) :=
            hcandidateUpper
          _ = (coarsePower * (good * cubeVolume)) * coarseCard := by ring)
  have hactiveVolume : active * cubeVolume ≤
      Kakeya.realRpowENN rho.1 (sigma - stickyLoss) := by
    calc
      active * cubeVolume =
          volume sticky.croppedCoarseShading.union := by
        exact (balanced_cover_coarse_volume sticky.balanced hrho).symm
      _ ≤ Kakeya.realRpowENN rho.1 (sigma - stickyLoss) :=
        sticky.coarse_extremal.volume_upper
  have hcancelPowerPos : 0 <
      Kakeya.realRpowENN rho.1 (5 - sigma - stickyLoss) := by
    simp [Kakeya.realRpowENN, Real.rpow_pos_of_pos hrho]
  have hcancelPowerTop :
      Kakeya.realRpowENN rho.1 (5 - sigma - stickyLoss) ≠ ⊤ := by
    simp [Kakeya.realRpowENN]
  apply (ENNReal.mul_le_mul_iff_right hcancelPowerPos.ne'
    hcancelPowerTop).mp
  simpa only [active, good, mul_assoc, mul_comm, mul_left_comm] using (show
      (Kakeya.realRpowENN rho.1 (coarseLoss + 2 * stickyLoss) * active) *
          Kakeya.realRpowENN rho.1 (5 - sigma - stickyLoss) ≤
        good * Kakeya.realRpowENN rho.1
          (5 - sigma - stickyLoss) from by
    calc
      (Kakeya.realRpowENN rho.1 (coarseLoss + 2 * stickyLoss) * active) *
            Kakeya.realRpowENN rho.1 (5 - sigma - stickyLoss) =
        Kakeya.realRpowENN rho.1
            (coarseLoss + 2 * stickyLoss) *
          (active * cubeVolume) * coarsePower := by
        rw [hcube]
        dsimp only [coarsePower]
        have hpower : Kakeya.realRpowENN rho.1
              (5 - sigma - stickyLoss) =
            Kakeya.realRpowENN rho.1 3 *
              Kakeya.realRpowENN rho.1
                (2 - sigma - stickyLoss) := by
          rw [← Kakeya.Assouad.realRpowENN_add hrho]
          congr 1
          ring
        rw [hpower]
        ring
      _ ≤ Kakeya.realRpowENN rho.1
          (coarseLoss + 2 * stickyLoss) *
        Kakeya.realRpowENN rho.1 (sigma - stickyLoss) *
          coarsePower := by gcongr
      _ = Kakeya.realRpowENN rho.1 (coarseLoss + 2) := by
        dsimp only [coarsePower]
        rw [← Kakeya.Assouad.realRpowENN_add hrho
          (coarseLoss + 2 * stickyLoss) (sigma - stickyLoss)]
        rw [← Kakeya.Assouad.realRpowENN_add hrho
          (coarseLoss + 2 * stickyLoss + (sigma - stickyLoss))
          (2 - sigma - stickyLoss)]
        congr 1
        ring
      _ ≤ coarsePower * (good * cubeVolume) := hcandidateNoCard
      _ = good * Kakeya.realRpowENN rho.1
          (5 - sigma - stickyLoss) := by
        rw [hcube]
        dsimp only [coarsePower]
        have hpower : Kakeya.realRpowENN rho.1
              (5 - sigma - stickyLoss) =
            Kakeya.realRpowENN rho.1
                (2 - sigma - stickyLoss) *
              Kakeya.realRpowENN rho.1 3 := by
          rw [← Kakeya.Assouad.realRpowENN_add hrho]
          congr 1
          ring
        rw [hpower]
        ring)

/-- The actual sticky whole-cell pullback produces the absolute density
receipt needed by the coarse-to-fine extremality bridge.  Both family
cardinalities cancel: the coarse one in
`proposition63_paper_coarseCandidate_goodCells_fraction`, and the fine one
against source density.  The sole numerical premise is family-free and may
therefore be frozen before the runtime choice of `rho`. -/
theorem proposition63_paper_sticky_goodCell_densityLift
    {delta sigma stickyLoss coarseLoss sourceLoss outputLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading source}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent multiplicity : ℕ}
    (sticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := stickyLoss)
      sourceShading rho logExponent)
    (candidate : WZ1PaperTubeShading sticky.coarse)
    (candidateExtremal : WZ2PaperCroppedIsExtremal
      sigma coarseLoss sticky.coarse candidate)
    (candidateSub : PaperIsSubshading
      candidate sticky.croppedCoarseShading)
    (candidateCubical : WZ1PaperIsCubicalShading candidate)
    (sourceExtremal : WZ2PaperCroppedIsExtremal
      sigma sourceLoss source sourceShading)
    (sourceLineClass : WZ1PaperIsLineClass source)
    (hdeltaSmall : delta ≤ 1 / 12)
    (hrhoSmall : rho.1 ≤ 1 / 12)
    (hsourceLower : ∀ point ∈ sourceShading.union,
      multiplicity ≤ sourceShading.pointMultiplicity point)
    (hsourceUpper : ∀ point ∈ sourceShading.union,
      sourceShading.pointMultiplicity point < 2 * multiplicity)
    (hpowerCutoff : ∀ requested : WZ2PaperRequestedScale delta,
      ((55296 : ENNReal) * Kakeya.deltaTubeVolume 1) *
          Kakeya.realRpowENN delta outputLoss *
          Kakeya.realRpowENN delta 2 ≤
        (1 / 2 : ENNReal) *
          Kakeya.realRpowENN requested.1
            (coarseLoss + 2 * stickyLoss) *
          wz2PaperPureRefinementFraction delta logExponent *
          Kakeya.realRpowENN delta (sourceLoss + 2)) :
    ((55296 : ENNReal) * Kakeya.deltaTubeVolume 1) *
        Kakeya.realRpowENN delta outputLoss *
        (Kakeya.realRpowENN delta 2 * source.enncard) ≤
      (ambientPropertyThreeCommonHull sticky candidate).mass := by
  let active : ENNReal := sticky.balanced.activeCells.card
  let good : ENNReal :=
    (propertyThreeGoodCells sticky.balanced candidate).card
  let cellMass : ENNReal := sticky.balanced.cellMass
  have hgood :
      Kakeya.realRpowENN rho.1 (coarseLoss + 2 * stickyLoss) * active ≤
        good := by
    simpa only [active, good] using
      proposition63_paper_coarseCandidate_goodCells_fraction sticky
        candidate candidateExtremal candidateSub candidateCubical hrhoSmall
  have hrefinedVolume : volume sticky.refined.union = active * cellMass := by
    simpa only [active, cellMass] using
      balanced_cover_fine_union_volume sticky.balanced
        sticky.coarse_extremal.delta_pos
  have hrefinedUpper : ∀ point ∈ sticky.refined.union,
      sticky.refined.pointMultiplicity point < 2 * multiplicity := by
    intro point hpoint
    have hsourcePoint : point ∈ sourceShading.union := by
      rcases hpoint with ⟨index, hindex⟩
      exact ⟨sticky.selected.embedding index,
        sticky.subshading index hindex⟩
    exact (sticky_refined_pointMultiplicity_le_source sticky point).trans_lt
      (hsourceUpper point hsourcePoint)
  have hrefinedMassUpper : sticky.refined.mass ≤
      (2 * multiplicity : ENNReal) * (active * cellMass) := by
    calc
      sticky.refined.mass ≤ (2 * multiplicity : ENNReal) *
          volume sticky.refined.union := by
        apply mass_le_of_pointMultiplicity_le
        intro point hpoint
        exact_mod_cast (hrefinedUpper point hpoint).le
      _ = (2 * multiplicity : ENNReal) * (active * cellMass) := by
        rw [hrefinedVolume]
  have htargetVolume :
      volume (ambientPropertyThreeCommonHull sticky candidate).union =
        good * cellMass := by
    rw [ambientPropertyThreeCommonHull_union]
    simpa only [good, cellMass] using
      propertyThreeFinePullback_volume_eq_goodCells
        sticky.balanced candidateSub
  have htargetMultiplicity : ∀ point ∈
      (ambientPropertyThreeCommonHull sticky candidate).union,
      multiplicity ≤
        (ambientPropertyThreeCommonHull sticky candidate).pointMultiplicity
          point := by
    intro point hpoint
    rw [ambientPropertyThreeCommonHull_pointMultiplicity_eq
      sticky candidate point hpoint]
    have hsourcePoint : point ∈ sourceShading.union := by
      rcases hpoint with ⟨index, hindex⟩
      exact ⟨index, ambientPropertyThreeCommonHull_subshading
        sticky candidate index hindex⟩
    exact hsourceLower point hsourcePoint
  have htargetMassLower : (multiplicity : ENNReal) *
      (good * cellMass) ≤
        (ambientPropertyThreeCommonHull sticky candidate).mass := by
    rw [← htargetVolume]
    exact multiplicity_floor_le_mass fun point hpoint => by
      exact_mod_cast htargetMultiplicity point hpoint
  have hhalfRefined :
      ((1 / 2 : ENNReal) *
          Kakeya.realRpowENN rho.1 (coarseLoss + 2 * stickyLoss)) *
          sticky.refined.mass ≤
        (ambientPropertyThreeCommonHull sticky candidate).mass := by
    calc
      ((1 / 2 : ENNReal) *
          Kakeya.realRpowENN rho.1 (coarseLoss + 2 * stickyLoss)) *
          sticky.refined.mass ≤
        ((1 / 2 : ENNReal) *
          Kakeya.realRpowENN rho.1 (coarseLoss + 2 * stickyLoss)) *
          ((2 * multiplicity : ENNReal) * (active * cellMass)) := by
        exact mul_le_mul_left' hrefinedMassUpper _
      _ = (multiplicity : ENNReal) *
          ((Kakeya.realRpowENN rho.1
            (coarseLoss + 2 * stickyLoss) * active) * cellMass) := by
        rw [show
          (1 / 2 : ENNReal) *
                Kakeya.realRpowENN rho.1
                  (coarseLoss + 2 * stickyLoss) *
                (2 * (multiplicity : ENNReal) * (active * cellMass)) =
              ((1 / 2 : ENNReal) * 2) *
                ((multiplicity : ENNReal) *
                  (Kakeya.realRpowENN rho.1
                    (coarseLoss + 2 * stickyLoss) * active * cellMass)) by
            ring]
        rw [show (1 / 2 : ENNReal) * 2 = 1 by
          simpa [div_eq_mul_inv] using
            ENNReal.inv_mul_cancel
              (show (2 : ENNReal) ≠ 0 by norm_num)
              (show (2 : ENNReal) ≠ ⊤ by norm_num), one_mul]
      _ ≤ (multiplicity : ENNReal) * (good * cellMass) := by gcongr
      _ ≤ (ambientPropertyThreeCommonHull sticky candidate).mass :=
        htargetMassLower
  have hsourceCard :
      Kakeya.realRpowENN delta (sourceLoss + 2) * source.enncard ≤
        sourceShading.mass := by
    let identity : Kakeya.Streamlined.TubeSubfamily source :=
      { family := source
        embedding := Function.Embedding.refl _
        tube_eq := fun _ => rfl }
    simpa only [identity] using selected_cardinality_cancellation sourceExtremal
      sourceLineClass identity hdeltaSmall
  calc
    ((55296 : ENNReal) * Kakeya.deltaTubeVolume 1) *
          Kakeya.realRpowENN delta outputLoss *
          (Kakeya.realRpowENN delta 2 * source.enncard) =
        (((55296 : ENNReal) * Kakeya.deltaTubeVolume 1) *
          Kakeya.realRpowENN delta outputLoss *
          Kakeya.realRpowENN delta 2) * source.enncard := by ring
    _ ≤ (((1 / 2 : ENNReal) *
          Kakeya.realRpowENN rho.1 (coarseLoss + 2 * stickyLoss)) *
          wz2PaperPureRefinementFraction delta logExponent *
          Kakeya.realRpowENN delta (sourceLoss + 2)) *
        source.enncard :=
      mul_le_mul_right' (hpowerCutoff rho) source.enncard
    _ = ((1 / 2 : ENNReal) *
          Kakeya.realRpowENN rho.1 (coarseLoss + 2 * stickyLoss)) *
        (wz2PaperPureRefinementFraction delta logExponent *
          (Kakeya.realRpowENN delta (sourceLoss + 2) *
            source.enncard)) := by ring
    _ ≤ ((1 / 2 : ENNReal) *
          Kakeya.realRpowENN rho.1 (coarseLoss + 2 * stickyLoss)) *
        (wz2PaperPureRefinementFraction delta logExponent *
          sourceShading.mass) := by gcongr
    _ ≤ ((1 / 2 : ENNReal) *
          Kakeya.realRpowENN rho.1 (coarseLoss + 2 * stickyLoss)) *
        sticky.refined.mass :=
      mul_le_mul_left' sticky.retained_mass _
    _ ≤ (ambientPropertyThreeCommonHull sticky candidate).mass :=
      hhalfRefined

/-- A whole-cell pullback on the fixed fine family is extremal once its
actual-cardinality density estimate has been proved.  The estimate is stated
after exposing the common `delta ^ 2 * family.enncard` term; in particular no
ancestry-retention or coarse multiplicity factor is charged through Lemma 4.3.
-/
theorem proposition63_paper_coarseToFine_pulledCandidate_extremal
    {delta sigma currentLoss outputLoss : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {current pulled : WZ1PaperTubeShading family}
    (currentExtremal : WZ2PaperCroppedIsExtremal
      sigma currentLoss family current)
    (lineClass : WZ1PaperIsLineClass family)
    (hdeltaSmall : delta ≤ 1 / 24)
    (pulledSub : PaperIsSubshading pulled current)
    (pulledCubical : WZ1PaperIsCubicalShading pulled)
    (hcurrentOutput : currentLoss ≤ outputLoss)
    (hdensityLift :
      ((55296 : ENNReal) * Kakeya.deltaTubeVolume 1) *
          Kakeya.realRpowENN delta outputLoss *
          (Kakeya.realRpowENN delta 2 * family.enncard) ≤
        pulled.mass) :
    WZ2PaperCroppedIsExtremal sigma outputLoss family pulled := by
  have bodyUpper :
      (wz1PaperBodyFamily family).mass ≤
        ((55296 : ENNReal) * Kakeya.deltaTubeVolume 1) *
          Kakeya.realRpowENN delta 2 * family.enncard := by
    let fullShading : WZ1PaperTubeShading family :=
      { carrier := fun index => wz1PaperTubeCarrier (family.tube index)
        measurable_carrier := fun index =>
          wz1PaperTubeCarrier_measurable (family.tube index)
        subset_body := fun _ => Set.Subset.rfl }
    have upper := wz2_paper_shading_mass_upper
      currentExtremal.delta_pos
      hdeltaSmall
      lineClass fullShading
    change (wz1PaperBodyFamily family).mass ≤
      ((55296 : ENNReal) * Kakeya.deltaTubeVolume 1) *
        Kakeya.realRpowENN delta 2 * family.enncard at upper
    exact upper
  have pulledDense : pulled.IsLambdaDense
      (Kakeya.realRpowENN delta outputLoss) := by
    rw [Kakeya.Streamlined.Shading.IsLambdaDense]
    calc
      Kakeya.realRpowENN delta outputLoss *
            (wz1PaperBodyFamily family).mass ≤
          Kakeya.realRpowENN delta outputLoss *
            (((55296 : ENNReal) * Kakeya.deltaTubeVolume 1) *
              Kakeya.realRpowENN delta 2 * family.enncard) := by
        gcongr
      _ = ((55296 : ENNReal) * Kakeya.deltaTubeVolume 1) *
          Kakeya.realRpowENN delta outputLoss *
          (Kakeya.realRpowENN delta 2 * family.enncard) := by ring
      _ ≤ pulled.mass := hdensityLift
  have weakened := currentExtremal.mono_loss hcurrentOutput
  exact {
    delta_pos := weakened.delta_pos
    delta_le_one := weakened.delta_le_one
    nonempty := weakened.nonempty
    cwa_nearby_scales := weakened.cwa_nearby_scales
    cubical := pulledCubical
    dense := pulledDense
    volume_upper := by
      apply (measure_mono ?_).trans weakened.volume_upper
      rintro point ⟨index, pointMem⟩
      exact ⟨index, pulledSub index pointMem⟩
  }

/-- Consumer-facing coarse-to-fine bridge.  Geometry and the raw pullback
mass comparison are merely transported receipts; extremality is supplied by
`proposition63_paper_coarseToFine_pulledCandidate_extremal`, hence is
independent of `leftFactor` and `rightFactor`.
-/
theorem proposition63_paper_coarseToFine_lift_with_receipts
    {delta sigma currentLoss outputLoss queryScale spatialScale
      variationScale : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {current pulled : WZ1PaperTubeShading family}
    (planeMap : Point3 → Point3)
    (resolutionScale windowScale : NNReal)
    (constant leftFactor rightFactor : ENNReal)
    (currentExtremal : WZ2PaperCroppedIsExtremal
      sigma currentLoss family current)
    (currentCWA : WZ2PaperConvexWolffBound family
      (Kakeya.realRpowENN delta (-currentLoss)))
    (lineClass : WZ1PaperIsLineClass family)
    (hdeltaSmall : delta ≤ 1 / 24)
    (pulledSub : PaperIsSubshading pulled current)
    (pulledCubical : WZ1PaperIsCubicalShading pulled)
    (pulledMultiplicity : ∀ point ∈ pulled.union,
      pulled.pointMultiplicity point = current.pointMultiplicity point)
    (pulledVariation : ∀ first ∈ pulled.union, ∀ second ∈ pulled.union,
      dist first second ≤ spatialScale →
        dist (planeMap first) (planeMap second) ≤ variationScale)
    (pulledInterval : PureWZ2IntervalCoveringAt pulled planeMap queryScale
      resolutionScale windowScale constant)
    (rawMassRetention : leftFactor * current.mass ≤
      rightFactor * pulled.mass)
    (hcurrentOutput : currentLoss ≤ outputLoss)
    (hdensityLift :
      ((55296 : ENNReal) * Kakeya.deltaTubeVolume 1) *
          Kakeya.realRpowENN delta outputLoss *
          (Kakeya.realRpowENN delta 2 * family.enncard) ≤
        pulled.mass) :
    WZ2PaperCroppedIsExtremal sigma outputLoss family pulled ∧
      WZ2PaperConvexWolffBound family
        (Kakeya.realRpowENN delta (-outputLoss)) ∧
      (∀ point ∈ pulled.union, pulled.pointMultiplicity point =
        current.pointMultiplicity point) ∧
      PureWZ2IntervalCoveringAt pulled planeMap queryScale
        resolutionScale windowScale constant ∧
      (∀ first ∈ pulled.union, ∀ second ∈ pulled.union,
        dist first second ≤ spatialScale →
          dist (planeMap first) (planeMap second) ≤ variationScale) ∧
      leftFactor * current.mass ≤ rightFactor * pulled.mass := by
  have pulledExtremal :=
    proposition63_paper_coarseToFine_pulledCandidate_extremal
      currentExtremal lineClass hdeltaSmall pulledSub pulledCubical hcurrentOutput
      hdensityLift
  have pulledCWA : WZ2PaperConvexWolffBound family
      (Kakeya.realRpowENN delta (-outputLoss)) :=
    transfer_cwa_to_subshading
      (_shading1 := current) (_shading2 := pulled) currentCWA hcurrentOutput
      currentExtremal.delta_pos currentExtremal.delta_le_one
  exact ⟨pulledExtremal, pulledCWA,
    pulledMultiplicity, pulledInterval, pulledVariation, rawMassRetention⟩

end Kakeya.Assouad.PureWZ2
