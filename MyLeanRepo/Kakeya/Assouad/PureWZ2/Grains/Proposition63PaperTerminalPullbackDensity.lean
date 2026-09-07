import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63RichStickyKernel
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.PropertyThreeFinePullbackMass
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.CommonSpatialPropertyThreePullback
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.DyadicPropertyThreeMass
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63StickyReentry
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63DyadicCurrentReentry
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63PaperCoarseToFineLift

/-!
# Terminal cardinality cancellation for the Proposition 6.3 pullback

This file isolates the cardinality and balanced-cell part of the paper's
coarse-to-fine pullback.  Raw ancestry costs remain confined to their own
iterator receipts and do not enter the density input passed to Lemma 4.3.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

/-- The complete fibers of a Section 6 cover partition the fine family. -/
theorem proposition63_terminal_sum_fullFiberCount
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : PureWZ2Section6Cover fine coarse) :
    (∑ parent : Fin coarse.card,
        (wz2PaperFullFiberCount fine coarse parent : ENNReal)) =
      fine.enncard := by
  have hnatural :
      (∑ parent : Fin coarse.card,
          (cover.toPaperTubeCover.fiberIndices parent).card) =
        fine.card := by
    have hfiberwise :=
      Finset.sum_card_fiberwise_eq_card_filter
        (Finset.univ : Finset (Fin fine.card))
        (Finset.univ : Finset (Fin coarse.card))
        cover.toPaperTubeCover.parent
    simpa [WZ1PaperTubeCover.fiberIndices] using hfiberwise
  calc
    (∑ parent : Fin coarse.card,
        (wz2PaperFullFiberCount fine coarse parent : ENNReal)) =
        ∑ parent : Fin coarse.card,
          ((cover.toPaperTubeCover.fiberIndices parent).card :
            ENNReal) := by
      apply Finset.sum_congr rfl
      intro parent _
      rw [wz2PaperFullFiberCount, cover.fullFiberIndices_eq parent]
    _ = (fine.card : ENNReal) := by
      rw [← Nat.cast_sum]
      exact_mod_cast hnatural
    _ = fine.enncard := by
      simp [Kakeya.Streamlined.TubeFamily.enncard]

/-- Summing the terminal upper fiber-cardinality band gives the global fine
cardinality upper bound.  The proof uses the actual cover partition, rather
than treating the complete fibers as an arbitrary family of subsets. -/
theorem Proposition63TerminalMultiplicityCertificate.fine_enncard_le_two_mul_fiberFloor_mul_coarse
    {delta rho sigma terminalLoss : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    (terminal : Proposition63TerminalMultiplicityCertificate
      (sigma := sigma) (terminalLoss := terminalLoss)
      cover fineShading coarseShading) :
    fine.enncard ≤
      2 * (terminal.fiberFloor : ENNReal) * coarse.enncard := by
  rw [← proposition63_terminal_sum_fullFiberCount cover]
  calc
    (∑ parent : Fin coarse.card,
        (wz2PaperFullFiberCount fine coarse parent : ENNReal)) ≤
        ∑ _parent : Fin coarse.card,
          (2 * (terminal.fiberFloor : ENNReal)) := by
      exact Finset.sum_le_sum fun parent _ =>
        (terminal.fiber_cardinality parent).2.le
    _ = 2 * (terminal.fiberFloor : ENNReal) * coarse.enncard := by
      simp [Kakeya.Streamlined.TubeFamily.enncard, Finset.sum_const,
        nsmul_eq_mul]
      ring

/-- The balanced-cell identity computes the spatial volume of a whole-cell
pullback from its good-cell count and the exact fine-cell quota `W`. -/
theorem Proposition63TerminalMultiplicityCertificate.pullback_volume_eq_goodCells_mul_W
    {delta rho sigma terminalLoss : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading candidate : WZ1PaperTubeShading coarse}
    (terminal : Proposition63TerminalMultiplicityCertificate
      (sigma := sigma) (terminalLoss := terminalLoss)
      cover fineShading coarseShading)
    (candidateSub : PaperIsSubshading candidate coarseShading) :
    volume (propertyThreeFinePullbackShading cover fineShading candidate).union =
      ((propertyThreeGoodCells terminal.balanced candidate).card : ENNReal) *
        ((terminal.W : ENNReal) *
          volume (wz1PaperGridCube delta (0, 0, 0))) := by
  rw [propertyThreeFinePullback_volume_eq_goodCells
    terminal.balanced candidateSub, terminal.balanced_cell_mass]

/-- The same lower bound for the consumer-facing common-spatial pullback. -/
theorem Proposition63RichTerminalStickyData.terminal_commonHull_mass_lower
    {delta sigma outputLoss sourceLoss normalizationLoss : ℝ}
    {croppedFamily : Kakeya.Streamlined.TubeFamily delta}
    {normalizationExponent : ℕ}
    {croppedShading : WZ1PaperTubeShading croppedFamily}
    {reentry : PureWZ2PropStickyReentryData
      (sigma := sigma) croppedShading normalizationExponent
      sourceLoss normalizationLoss}
    {rho : WZ2PaperRequestedScale delta}
    (rich : Proposition63RichTerminalStickyData
      (outputLoss := outputLoss) croppedShading reentry rho)
    (candidate : WZ1PaperTubeShading rich.data.coarse)
    (candidateSub : PaperIsSubshading
      candidate rich.data.croppedCoarseShading) :
    ((rich.terminal.fineDegreeFloor * rich.terminal.muFine : ℕ) : ENNReal) *
        (((propertyThreeGoodCells rich.terminal.balanced candidate).card :
            ENNReal) *
          ((rich.terminal.W : ENNReal) *
            volume (wz1PaperGridCube delta (0, 0, 0)))) ≤
      (ambientPropertyThreeCommonHull rich.data candidate).mass := by
  have htargetVolume :
      volume (ambientPropertyThreeCommonHull rich.data candidate).union =
        ((propertyThreeGoodCells rich.terminal.balanced candidate).card :
            ENNReal) *
          ((rich.terminal.W : ENNReal) *
            volume (wz1PaperGridCube delta (0, 0, 0))) := by
    rw [ambientPropertyThreeCommonHull_union]
    exact rich.terminal.pullback_volume_eq_goodCells_mul_W candidateSub
  have htargetFloor : ∀ point ∈
      (ambientPropertyThreeCommonHull rich.data candidate).union,
      (rich.terminal.fineDegreeFloor * rich.terminal.muFine : ℕ) ≤
        (ambientPropertyThreeCommonHull rich.data candidate).pointMultiplicity
          point := by
    intro point hpoint
    have hpullback : point ∈
        (propertyThreeFinePullbackShading rich.data.cover
          rich.data.refined candidate).union := by
      rw [← ambientPropertyThreeCommonHull_union rich.data candidate]
      exact hpoint
    have hrefined : point ∈ rich.data.refined.union := by
      rcases hpullback with ⟨source, hsource, _⟩
      exact ⟨source, hsource⟩
    have hfloor :=
      rich.terminal.fine_pointMultiplicity_floor_on_union hrefined
    have hle := sticky_refined_pointMultiplicity_le_source rich.data point
    rw [ambientPropertyThreeCommonHull_pointMultiplicity_eq
      rich.data candidate point hpoint]
    exact hfloor.trans hle
  rw [← htargetVolume]
  exact multiplicity_floor_le_mass fun point hpoint => by
    exact_mod_cast htargetFloor point hpoint

/-- Final cancellation wrapper for `hdensityLift`.  All geometric and
cardinality facts have been discharged; the remaining premise is the pure
scalar comparison between the desired density and the terminal
`goodCells * W * fineDegreeFloor * muFine` contribution. -/
theorem Proposition63RichTerminalStickyData.terminal_commonHull_densityLift
    {delta sigma outputLoss sourceLoss normalizationLoss densityLoss : ℝ}
    {croppedFamily : Kakeya.Streamlined.TubeFamily delta}
    {normalizationExponent : ℕ}
    {croppedShading : WZ1PaperTubeShading croppedFamily}
    {reentry : PureWZ2PropStickyReentryData
      (sigma := sigma) croppedShading normalizationExponent
      sourceLoss normalizationLoss}
    {rho : WZ2PaperRequestedScale delta}
    (rich : Proposition63RichTerminalStickyData
      (outputLoss := outputLoss) croppedShading reentry rho)
    (candidate : WZ1PaperTubeShading rich.data.coarse)
    (candidateSub : PaperIsSubshading
      candidate rich.data.croppedCoarseShading)
    (harithmetic :
      ((55296 : ENNReal) * Kakeya.deltaTubeVolume 1) *
          Kakeya.realRpowENN delta densityLoss *
          (Kakeya.realRpowENN delta 2 * croppedFamily.enncard) ≤
        ((rich.terminal.fineDegreeFloor * rich.terminal.muFine : ℕ) :
            ENNReal) *
          (((propertyThreeGoodCells rich.terminal.balanced candidate).card :
              ENNReal) *
            ((rich.terminal.W : ENNReal) *
              volume (wz1PaperGridCube delta (0, 0, 0))))) :
    ((55296 : ENNReal) * Kakeya.deltaTubeVolume 1) *
        Kakeya.realRpowENN delta densityLoss *
        (Kakeya.realRpowENN delta 2 * croppedFamily.enncard) ≤
      (ambientPropertyThreeCommonHull rich.data candidate).mass :=
  harithmetic.trans (rich.terminal_commonHull_mass_lower candidate candidateSub)

/-- Without an ambient dyadic multiplicity band, the terminal fine-degree
floor still cancels against the terminal fine-mass upper bound.  One copy of
`regularity` is spent in the coarse good-cell count and a second copy in the
fine multiplicity upper bound. -/
theorem Proposition63RichTerminalStickyData.terminal_commonHull_source_mass_lower
    {delta sigma outputLoss sourceLoss normalizationLoss coarseLoss : ℝ}
    {croppedFamily : Kakeya.Streamlined.TubeFamily delta}
    {normalizationExponent : ℕ}
    {croppedShading : WZ1PaperTubeShading croppedFamily}
    {reentry : PureWZ2PropStickyReentryData
      (sigma := sigma) croppedShading normalizationExponent
      sourceLoss normalizationLoss}
    {rho : WZ2PaperRequestedScale delta}
    (rich : Proposition63RichTerminalStickyData
      (outputLoss := outputLoss) croppedShading reentry rho)
    (candidate : WZ1PaperTubeShading rich.data.coarse)
    (candidateExtremal : WZ2PaperCroppedIsExtremal
      sigma coarseLoss rich.data.coarse candidate)
    (candidateSub : PaperIsSubshading
      candidate rich.data.croppedCoarseShading)
    (hhalf : (1 / 2 : ENNReal) *
        rich.data.croppedCoarseShading.mass ≤ candidate.mass) :
    (((2 : ENNReal) * (rich.terminal.regularity : ENNReal) ^ 2) *
        (wz2PaperPureRefinementFraction delta 61)⁻¹)⁻¹ *
        croppedShading.mass ≤
      (ambientPropertyThreeCommonHull rich.data candidate).mass := by
  let regularity : ENNReal := rich.terminal.regularity
  let fineMultiplicity : ENNReal :=
    (rich.terminal.fineDegreeFloor * rich.terminal.muFine : ℕ)
  have hregularityPos : 0 < regularity := by
    simpa only [regularity] using
      (show (0 : ENNReal) < rich.terminal.regularity by
        exact_mod_cast rich.terminal.regularity_pos)
  have hregularityTop : regularity ≠ ⊤ := ENNReal.natCast_ne_top _
  have hfinePos : 0 < fineMultiplicity := by
    dsimp only [fineMultiplicity]
    exact_mod_cast Nat.mul_pos rich.terminal.fineDegreeFloor_pos
      rich.terminal.muFine_pos
  have hfineTop : fineMultiplicity ≠ ⊤ := ENNReal.natCast_ne_top _
  have hpullbackVolume :=
    propertyThreeFinePullback_volume_lower_of_coarse_band
      rich.data candidate candidateSub candidateExtremal.cubical hhalf
      (rich.terminal.muCoarse : ENNReal) regularity
      (by exact_mod_cast rich.terminal.muCoarse_pos)
      (ENNReal.natCast_ne_top _) hregularityPos hregularityTop
      (fun point hpoint =>
        (rich.terminal.coarse_pointMultiplicity_band hpoint).1)
      (fun point hpoint => by
        simpa only [regularity, Nat.cast_mul] using
          (rich.terminal.coarse_pointMultiplicity_band hpoint).2)
  have htargetFloor : fineMultiplicity *
      volume (ambientPropertyThreeCommonHull rich.data candidate).union ≤
        (ambientPropertyThreeCommonHull rich.data candidate).mass := by
    apply multiplicity_floor_le_mass
    intro point hpoint
    have hpullback : point ∈
        (propertyThreeFinePullbackShading rich.data.cover
          rich.data.refined candidate).union := by
      rw [← ambientPropertyThreeCommonHull_union rich.data candidate]
      exact hpoint
    have hrefined : point ∈ rich.data.refined.union := by
      rcases hpullback with ⟨source, hsource, _⟩
      exact ⟨source, hsource⟩
    have hfloor :=
      rich.terminal.fine_pointMultiplicity_floor_on_union hrefined
    have hle := sticky_refined_pointMultiplicity_le_source rich.data point
    rw [ambientPropertyThreeCommonHull_pointMultiplicity_eq
      rich.data candidate point hpoint]
    change ((rich.terminal.fineDegreeFloor * rich.terminal.muFine : ℕ) :
      ENNReal) ≤ (croppedShading.pointMultiplicity point : ENNReal)
    exact_mod_cast hfloor.trans hle
  have hrefinedToTarget :
      ((2 : ENNReal) * regularity ^ 2)⁻¹ * rich.data.refined.mass ≤
        (ambientPropertyThreeCommonHull rich.data candidate).mass := by
    have htwoRegInv : ((2 : ENNReal) * regularity)⁻¹ =
        (2 : ENNReal)⁻¹ * regularity⁻¹ :=
      ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inr hregularityPos.ne')
    have htwoRegSqInv : ((2 : ENNReal) * regularity ^ 2)⁻¹ =
        (2 : ENNReal)⁻¹ * regularity⁻¹ * regularity⁻¹ := by
      rw [pow_two, ENNReal.mul_inv
          (Or.inl (by norm_num))
          (Or.inr (mul_ne_zero hregularityPos.ne' hregularityPos.ne')),
        ENNReal.mul_inv (Or.inr hregularityTop)
          (Or.inl hregularityTop)]
      ring
    calc
      ((2 : ENNReal) * regularity ^ 2)⁻¹ * rich.data.refined.mass ≤
          ((2 : ENNReal) * regularity ^ 2)⁻¹ *
            ((regularity * fineMultiplicity) *
              volume rich.data.refined.union) := by
        gcongr
        simpa only [regularity, fineMultiplicity, Nat.cast_mul, mul_assoc]
          using rich.terminal.fine_mass_le_degree_mul_volume
      _ = fineMultiplicity *
          (((2 : ENNReal) * regularity)⁻¹ *
            volume rich.data.refined.union) := by
        rw [htwoRegSqInv, htwoRegInv]
        calc
          (2 : ENNReal)⁻¹ * regularity⁻¹ * regularity⁻¹ *
                (regularity * fineMultiplicity *
                  volume rich.data.refined.union) =
              (regularity⁻¹ * regularity) *
                (fineMultiplicity * ((2 : ENNReal)⁻¹ * regularity⁻¹ *
                  volume rich.data.refined.union)) := by ring
          _ = fineMultiplicity * ((2 : ENNReal)⁻¹ * regularity⁻¹ *
                volume rich.data.refined.union) := by
            rw [ENNReal.inv_mul_cancel hregularityPos.ne' hregularityTop,
              one_mul]
      _ ≤ fineMultiplicity *
          volume (propertyThreeFinePullbackShading rich.data.cover
            rich.data.refined candidate).union := by gcongr
      _ = fineMultiplicity *
          volume (ambientPropertyThreeCommonHull rich.data candidate).union := by
        rw [ambientPropertyThreeCommonHull_union]
      _ ≤ (ambientPropertyThreeCommonHull rich.data candidate).mass :=
        htargetFloor
  have hinverse :
      (((2 : ENNReal) * regularity ^ 2) *
          (wz2PaperPureRefinementFraction delta 61)⁻¹)⁻¹ =
        ((2 : ENNReal) * regularity ^ 2)⁻¹ *
          wz2PaperPureRefinementFraction delta 61 := by
    rw [ENNReal.mul_inv
      (Or.inl (mul_ne_zero (by norm_num) <| pow_ne_zero 2 hregularityPos.ne'))
      (Or.inl (ENNReal.mul_ne_top (by norm_num) <|
        ENNReal.pow_ne_top hregularityTop)), inv_inv]
  rw [hinverse]
  calc
    ((2 : ENNReal) * regularity ^ 2)⁻¹ *
          wz2PaperPureRefinementFraction delta 61 * croppedShading.mass =
        ((2 : ENNReal) * regularity ^ 2)⁻¹ *
          (wz2PaperPureRefinementFraction delta 61 *
            croppedShading.mass) := by ring
    _ ≤ ((2 : ENNReal) * regularity ^ 2)⁻¹ * rich.data.refined.mass := by
      gcongr
      exact rich.total_mass_retention
    _ ≤ (ambientPropertyThreeCommonHull rich.data candidate).mass :=
      hrefinedToTarget

/-- Family-free scalar form of the terminal density lift.  The precise
small-scale requirement is
`C * delta^densityLoss * delta^2 ≤ (2 R^2)⁻¹ * fraction *
delta^(normalizationLoss + 2)`, where `R` is the terminal regularity. -/
theorem Proposition63RichTerminalStickyData.terminal_commonHull_densityLift_of_scalar
    {delta sigma outputLoss sourceLoss normalizationLoss densityLoss
      coarseLoss : ℝ}
    {croppedFamily : Kakeya.Streamlined.TubeFamily delta}
    {normalizationExponent : ℕ}
    {croppedShading : WZ1PaperTubeShading croppedFamily}
    {reentry : PureWZ2PropStickyReentryData
      (sigma := sigma) croppedShading normalizationExponent
      sourceLoss normalizationLoss}
    {rho : WZ2PaperRequestedScale delta}
    (rich : Proposition63RichTerminalStickyData
      (outputLoss := outputLoss) croppedShading reentry rho)
    (candidate : WZ1PaperTubeShading rich.data.coarse)
    (candidateExtremal : WZ2PaperCroppedIsExtremal
      sigma coarseLoss rich.data.coarse candidate)
    (candidateSub : PaperIsSubshading
      candidate rich.data.croppedCoarseShading)
    (hhalf : (1 / 2 : ENNReal) *
        rich.data.croppedCoarseShading.mass ≤ candidate.mass)
    (hdeltaSmall : delta ≤ 1 / 12)
    (hscalar :
      ((55296 : ENNReal) * Kakeya.deltaTubeVolume 1) *
          Kakeya.realRpowENN delta densityLoss *
          Kakeya.realRpowENN delta 2 ≤
        (((2 : ENNReal) * (rich.terminal.regularity : ENNReal) ^ 2)⁻¹ *
          wz2PaperPureRefinementFraction delta 61) *
            Kakeya.realRpowENN delta (normalizationLoss + 2)) :
    ((55296 : ENNReal) * Kakeya.deltaTubeVolume 1) *
        Kakeya.realRpowENN delta densityLoss *
        (Kakeya.realRpowENN delta 2 * croppedFamily.enncard) ≤
      (ambientPropertyThreeCommonHull rich.data candidate).mass := by
  have hsourceCard :
      Kakeya.realRpowENN delta (normalizationLoss + 2) *
          croppedFamily.enncard ≤ croppedShading.mass := by
    let all := Kakeya.Streamlined.TubeSubfamily.fromFinset croppedFamily
      (Finset.univ : Finset (Fin croppedFamily.card))
    have hselected := selected_cardinality_cancellation
      reentry.cropped_extremal reentry.geometry.line_class all hdeltaSmall
    have hallCard : all.family.enncard = croppedFamily.enncard := by
      simp [all, Kakeya.Streamlined.TubeSubfamily.fromFinset,
        Kakeya.Streamlined.TubeFamily.enncard]
    simpa only [hallCard] using hselected
  calc
    ((55296 : ENNReal) * Kakeya.deltaTubeVolume 1) *
          Kakeya.realRpowENN delta densityLoss *
          (Kakeya.realRpowENN delta 2 * croppedFamily.enncard) =
        (((55296 : ENNReal) * Kakeya.deltaTubeVolume 1) *
          Kakeya.realRpowENN delta densityLoss *
          Kakeya.realRpowENN delta 2) * croppedFamily.enncard := by ring
    _ ≤ ((((2 : ENNReal) *
          (rich.terminal.regularity : ENNReal) ^ 2)⁻¹ *
            wz2PaperPureRefinementFraction delta 61) *
          Kakeya.realRpowENN delta (normalizationLoss + 2)) *
            croppedFamily.enncard := mul_le_mul_right' hscalar _
    _ = (((2 : ENNReal) *
          (rich.terminal.regularity : ENNReal) ^ 2)⁻¹ *
            wz2PaperPureRefinementFraction delta 61) *
          (Kakeya.realRpowENN delta (normalizationLoss + 2) *
            croppedFamily.enncard) := by ring
    _ ≤ (((2 : ENNReal) *
          (rich.terminal.regularity : ENNReal) ^ 2)⁻¹ *
            wz2PaperPureRefinementFraction delta 61) *
          croppedShading.mass := by gcongr
    _ = (((2 : ENNReal) *
          (rich.terminal.regularity : ENNReal) ^ 2) *
            (wz2PaperPureRefinementFraction delta 61)⁻¹)⁻¹ *
          croppedShading.mass := by
      rw [ENNReal.mul_inv
        (Or.inl (mul_ne_zero (by norm_num) <|
          pow_ne_zero 2 (by exact_mod_cast rich.terminal.regularity_pos.ne')))
        (Or.inl (ENNReal.mul_ne_top (by norm_num) <|
          ENNReal.pow_ne_top (ENNReal.natCast_ne_top _))), inv_inv]
    _ ≤ (ambientPropertyThreeCommonHull rich.data candidate).mass :=
      rich.terminal_commonHull_source_mass_lower candidate candidateExtremal
        candidateSub hhalf

/-- Absolute density from an extremal coarse candidate, without a retained
half-mass hypothesis on that candidate and without an ambient source
multiplicity band.  Candidate extremality supplies the good-cell fraction;
the terminal fine-degree upper and lower bounds cancel internally, leaving
only one factor of terminal regularity in the scalar cutoff. -/
theorem Proposition63RichTerminalStickyData.terminal_commonHull_candidateExtremal_densityLift
    {delta sigma outputLoss sourceLoss normalizationLoss densityLoss
      coarseLoss : ℝ}
    {croppedFamily : Kakeya.Streamlined.TubeFamily delta}
    {normalizationExponent : ℕ}
    {croppedShading : WZ1PaperTubeShading croppedFamily}
    {reentry : PureWZ2PropStickyReentryData
      (sigma := sigma) croppedShading normalizationExponent
      sourceLoss normalizationLoss}
    {rho : WZ2PaperRequestedScale delta}
    (rich : Proposition63RichTerminalStickyData
      (outputLoss := outputLoss) croppedShading reentry rho)
    (candidate : WZ1PaperTubeShading rich.data.coarse)
    (candidateExtremal : WZ2PaperCroppedIsExtremal
      sigma coarseLoss rich.data.coarse candidate)
    (candidateSub : PaperIsSubshading
      candidate rich.data.croppedCoarseShading)
    (candidateCubical : WZ1PaperIsCubicalShading candidate)
    (hdeltaSmall : delta ≤ 1 / 12)
    (hrhoSmall : rho.1 ≤ 1 / 12)
    (hscalar :
      ((55296 : ENNReal) * Kakeya.deltaTubeVolume 1) *
          Kakeya.realRpowENN delta densityLoss *
          Kakeya.realRpowENN delta 2 ≤
        (rich.terminal.regularity : ENNReal)⁻¹ *
          Kakeya.realRpowENN rho.1 (coarseLoss + 2 * outputLoss) *
          wz2PaperPureRefinementFraction delta 61 *
          Kakeya.realRpowENN delta (normalizationLoss + 2)) :
    ((55296 : ENNReal) * Kakeya.deltaTubeVolume 1) *
        Kakeya.realRpowENN delta densityLoss *
        (Kakeya.realRpowENN delta 2 * croppedFamily.enncard) ≤
      (ambientPropertyThreeCommonHull rich.data candidate).mass := by
  let regularity : ENNReal := rich.terminal.regularity
  let fineMultiplicity : ENNReal :=
    (rich.terminal.fineDegreeFloor * rich.terminal.muFine : ℕ)
  let active : ENNReal := rich.data.balanced.activeCells.card
  let good : ENNReal :=
    (propertyThreeGoodCells rich.data.balanced candidate).card
  let cellMass : ENNReal := rich.data.balanced.cellMass
  let rhoPower : ENNReal :=
    Kakeya.realRpowENN rho.1 (coarseLoss + 2 * outputLoss)
  have hregularityPos : 0 < regularity := by
    simpa only [regularity] using
      (show (0 : ENNReal) < rich.terminal.regularity by
        exact_mod_cast rich.terminal.regularity_pos)
  have hregularityTop : regularity ≠ ⊤ := ENNReal.natCast_ne_top _
  have hgood : rhoPower * active ≤ good := by
    simpa only [rhoPower, active, good] using
      proposition63_paper_coarseCandidate_goodCells_fraction rich.data
        candidate candidateExtremal candidateSub candidateCubical hrhoSmall
  have hrefinedVolume : volume rich.data.refined.union = active * cellMass := by
    simpa only [active, cellMass] using
      balanced_cover_fine_union_volume rich.data.balanced
        rich.data.coarse_extremal.delta_pos
  have hrefinedMassUpper : rich.data.refined.mass ≤
      (regularity * fineMultiplicity) * (active * cellMass) := by
    calc
      rich.data.refined.mass ≤
          ((((rich.terminal.regularity *
              rich.terminal.fineDegreeFloor : ℕ) : ENNReal) *
            rich.terminal.muFine) *
              volume rich.data.refined.union) :=
        rich.terminal.fine_mass_le_degree_mul_volume
      _ = (regularity * fineMultiplicity) * (active * cellMass) := by
        rw [hrefinedVolume]
        simp only [regularity, fineMultiplicity, Nat.cast_mul]
        ring
  have htargetLower : fineMultiplicity * (good * cellMass) ≤
      (ambientPropertyThreeCommonHull rich.data candidate).mass := by
    have htargetVolume :
        volume (ambientPropertyThreeCommonHull rich.data candidate).union =
          good * cellMass := by
      rw [ambientPropertyThreeCommonHull_union]
      simpa only [good, cellMass] using
        propertyThreeFinePullback_volume_eq_goodCells
          rich.data.balanced candidateSub
    rw [← htargetVolume]
    apply multiplicity_floor_le_mass
    intro point hpoint
    have hpullback : point ∈
        (propertyThreeFinePullbackShading rich.data.cover
          rich.data.refined candidate).union := by
      rw [← ambientPropertyThreeCommonHull_union rich.data candidate]
      exact hpoint
    have hrefined : point ∈ rich.data.refined.union := by
      rcases hpullback with ⟨source, hsource, _⟩
      exact ⟨source, hsource⟩
    have hfloor :=
      rich.terminal.fine_pointMultiplicity_floor_on_union hrefined
    have hle := sticky_refined_pointMultiplicity_le_source rich.data point
    rw [ambientPropertyThreeCommonHull_pointMultiplicity_eq
      rich.data candidate point hpoint]
    change ((rich.terminal.fineDegreeFloor * rich.terminal.muFine : ℕ) :
      ENNReal) ≤ (croppedShading.pointMultiplicity point : ENNReal)
    exact_mod_cast hfloor.trans hle
  have hrefinedToTarget :
      (regularity⁻¹ * rhoPower) * rich.data.refined.mass ≤
        (ambientPropertyThreeCommonHull rich.data candidate).mass := by
    calc
      (regularity⁻¹ * rhoPower) * rich.data.refined.mass ≤
          (regularity⁻¹ * rhoPower) *
            ((regularity * fineMultiplicity) * (active * cellMass)) := by
        gcongr
      _ = (regularity⁻¹ * regularity) *
          (fineMultiplicity * ((rhoPower * active) * cellMass)) := by ring
      _ = fineMultiplicity * ((rhoPower * active) * cellMass) := by
        rw [ENNReal.inv_mul_cancel hregularityPos.ne' hregularityTop, one_mul]
      _ ≤ fineMultiplicity * (good * cellMass) := by gcongr
      _ ≤ (ambientPropertyThreeCommonHull rich.data candidate).mass :=
        htargetLower
  have hsourceCard :
      Kakeya.realRpowENN delta (normalizationLoss + 2) *
          croppedFamily.enncard ≤ croppedShading.mass := by
    let all := Kakeya.Streamlined.TubeSubfamily.fromFinset croppedFamily
      (Finset.univ : Finset (Fin croppedFamily.card))
    have hselected := selected_cardinality_cancellation
      reentry.cropped_extremal reentry.geometry.line_class all hdeltaSmall
    have hallCard : all.family.enncard = croppedFamily.enncard := by
      simp [all, Kakeya.Streamlined.TubeSubfamily.fromFinset,
        Kakeya.Streamlined.TubeFamily.enncard]
    simpa only [hallCard] using hselected
  calc
    ((55296 : ENNReal) * Kakeya.deltaTubeVolume 1) *
          Kakeya.realRpowENN delta densityLoss *
          (Kakeya.realRpowENN delta 2 * croppedFamily.enncard) =
        (((55296 : ENNReal) * Kakeya.deltaTubeVolume 1) *
          Kakeya.realRpowENN delta densityLoss *
          Kakeya.realRpowENN delta 2) * croppedFamily.enncard := by ring
    _ ≤ ((regularity⁻¹ * rhoPower *
          wz2PaperPureRefinementFraction delta 61 *
          Kakeya.realRpowENN delta (normalizationLoss + 2)) *
            croppedFamily.enncard) := by
      simpa only [regularity, rhoPower] using
        mul_le_mul_right' hscalar croppedFamily.enncard
    _ = (regularity⁻¹ * rhoPower) *
        (wz2PaperPureRefinementFraction delta 61 *
          (Kakeya.realRpowENN delta (normalizationLoss + 2) *
            croppedFamily.enncard)) := by ring
    _ ≤ (regularity⁻¹ * rhoPower) *
        (wz2PaperPureRefinementFraction delta 61 * croppedShading.mass) := by
      gcongr
    _ ≤ (regularity⁻¹ * rhoPower) * rich.data.refined.mass := by
      gcongr
      exact rich.total_mass_retention
    _ ≤ (ambientPropertyThreeCommonHull rich.data candidate).mass :=
      hrefinedToTarget

/-- Production two-band receipt.  The terminal coarse multiplicity band is
read from the same rich certificate as the sticky pullback, while the outer
dyadic band is transported by the caller's current-multiplicity equality.
Only `regularity` and the genuine sticky refinement fraction remain. -/
theorem Proposition63RichTerminalStickyData.terminal_twoBand_mass_lower
    {delta sigma outputLoss sourceLoss normalizationLoss : ℝ}
    {croppedFamily : Kakeya.Streamlined.TubeFamily delta}
    {normalizationExponent : ℕ}
    {croppedShading : WZ1PaperTubeShading croppedFamily}
    {reentry : PureWZ2PropStickyReentryData
      (sigma := sigma) croppedShading normalizationExponent
      sourceLoss normalizationLoss}
    {rho : WZ2PaperRequestedScale delta}
    (rich : Proposition63RichTerminalStickyData
      (outputLoss := outputLoss) croppedShading reentry rho)
    (candidate : WZ1PaperTubeShading rich.data.coarse)
    (candidateSub : PaperIsSubshading
      candidate rich.data.croppedCoarseShading)
    (candidateCubical : WZ1PaperIsCubicalShading candidate)
    (hhalf : (1 / 2 : ENNReal) *
        rich.data.croppedCoarseShading.mass ≤ candidate.mass)
    (hsourceLower : ∀ point ∈ croppedShading.union,
      rich.terminal.muFine ≤ croppedShading.pointMultiplicity point)
    (hsourceUpper : ∀ point ∈ croppedShading.union,
      croppedShading.pointMultiplicity point < 2 * rich.terminal.muFine) :
    ((4 * (rich.terminal.regularity : ENNReal)) *
        (wz2PaperPureRefinementFraction delta 61)⁻¹)⁻¹ *
        croppedShading.mass ≤
      (ambientSubfamilyPropertyThreeCommonHull croppedShading
        (proposition63IdentitySubfamily croppedFamily)
          (sourceShading := croppedShading)
          (sticky := rich.data) candidate).mass := by
  apply ambientPropertyThreeCommonHull_source_mass_lower_of_two_bands
    croppedShading (proposition63IdentitySubfamily croppedFamily)
      (fun _ _ h => h) rich.data candidate candidateSub candidateCubical hhalf
      (rich.terminal.muCoarse : ENNReal)
      (rich.terminal.regularity : ENNReal)
  · exact_mod_cast rich.terminal.muCoarse_pos
  · exact ENNReal.natCast_ne_top _
  · exact_mod_cast rich.terminal.regularity_pos
  · exact ENNReal.natCast_ne_top _
  · intro point hpoint
    exact (rich.terminal.coarse_pointMultiplicity_band hpoint).1
  · intro point hpoint
    simpa only [Nat.cast_mul] using
      (rich.terminal.coarse_pointMultiplicity_band hpoint).2
  · exact hsourceLower
  · intro point hpoint
    exact_mod_cast hsourceUpper point hpoint

/-- Direct `hdensityLift` producer after a scalar absorption against the
two-band receipt.  Its conclusion contains no raw ancestry pullback cost and
is therefore suitable for the cardinality-aware Lemma 4.3 bridge. -/
theorem Proposition63RichTerminalStickyData.terminal_twoBand_densityLift
    {delta sigma outputLoss sourceLoss normalizationLoss densityLoss : ℝ}
    {croppedFamily : Kakeya.Streamlined.TubeFamily delta}
    {normalizationExponent : ℕ}
    {croppedShading : WZ1PaperTubeShading croppedFamily}
    {reentry : PureWZ2PropStickyReentryData
      (sigma := sigma) croppedShading normalizationExponent
      sourceLoss normalizationLoss}
    {rho : WZ2PaperRequestedScale delta}
    (rich : Proposition63RichTerminalStickyData
      (outputLoss := outputLoss) croppedShading reentry rho)
    (candidate : WZ1PaperTubeShading rich.data.coarse)
    (candidateSub : PaperIsSubshading
      candidate rich.data.croppedCoarseShading)
    (candidateCubical : WZ1PaperIsCubicalShading candidate)
    (hhalf : (1 / 2 : ENNReal) *
        rich.data.croppedCoarseShading.mass ≤ candidate.mass)
    (hsourceLower : ∀ point ∈ croppedShading.union,
      rich.terminal.muFine ≤ croppedShading.pointMultiplicity point)
    (hsourceUpper : ∀ point ∈ croppedShading.union,
      croppedShading.pointMultiplicity point < 2 * rich.terminal.muFine)
    (harithmetic :
      ((55296 : ENNReal) * Kakeya.deltaTubeVolume 1) *
          Kakeya.realRpowENN delta densityLoss *
          (Kakeya.realRpowENN delta 2 * croppedFamily.enncard) ≤
        ((4 * (rich.terminal.regularity : ENNReal)) *
          (wz2PaperPureRefinementFraction delta 61)⁻¹)⁻¹ *
            croppedShading.mass) :
    ((55296 : ENNReal) * Kakeya.deltaTubeVolume 1) *
        Kakeya.realRpowENN delta densityLoss *
        (Kakeya.realRpowENN delta 2 * croppedFamily.enncard) ≤
      (ambientSubfamilyPropertyThreeCommonHull croppedShading
        (proposition63IdentitySubfamily croppedFamily)
          (sourceShading := croppedShading)
          (sticky := rich.data) candidate).mass :=
  harithmetic.trans <| rich.terminal_twoBand_mass_lower candidate candidateSub
    candidateCubical hhalf hsourceLower hsourceUpper

/-- Exact production receipt after the iterator first dyadically regularizes
its current shading and then re-enters Proposition 6.2.  The ambient
multiplicity band is read directly from `dyadic`; the rich call starts from
the freshly normalized selected-family shading.  Thus no earlier iterator
mass loss appears in this comparison. -/
theorem Proposition63RichTerminalStickyData.dyadicCurrent_twoBand_mass_lower
    {delta sigma initialInputLoss normalizationLoss densityLoss incidence
      currentLoss dyadicLoss weightLoss reentryLoss reentryNormalizationLoss
      outputLoss coarseLoss : ℝ}
    {initialSource : PureWZ2ExtremalConfiguration sigma initialInputLoss delta}
    {normalizationExponent : ℕ}
    {root : Proposition63RootNormalizationData
      (outputLoss := normalizationLoss) initialSource normalizationExponent
        densityLoss}
    {current : WZ1PaperTubeShading root.normalization.croppedFamily}
    {currentMap : PaperWZ1WeakPlaneMapData current incidence}
    (dyadic : Proposition63DyadicCurrentReentryData
      (currentLoss := currentLoss) (dyadicLoss := dyadicLoss)
      (weightLoss := weightLoss) (reentryLoss := reentryLoss)
      (reentryNormalizationLoss := reentryNormalizationLoss)
      root current currentMap)
    (hreentryLossPos : 0 < reentryLoss)
    {rho : WZ2PaperRequestedScale delta}
    (rich : Proposition63RichTerminalStickyData
      (outputLoss := outputLoss)
      dyadic.reentry.normalization.croppedRefined
      (dyadic.reentry.normalization.toPropStickyReentryData
        hreentryLossPos
        dyadic.reentry.reentry_normalization_loss_pos) rho)
    (candidate : WZ1PaperTubeShading rich.data.coarse)
    (candidateExtremal : WZ2PaperCroppedIsExtremal
      sigma coarseLoss rich.data.coarse candidate)
    (candidateSub : PaperIsSubshading
      candidate rich.data.croppedCoarseShading)
    (hhalf : (1 / 2 : ENNReal) *
        rich.data.croppedCoarseShading.mass ≤ candidate.mass) :
    ((4 * (rich.terminal.regularity : ENNReal)) *
        (wz2PaperPureRefinementFraction delta 61)⁻¹)⁻¹ *
        dyadic.reentry.normalization.croppedRefined.mass ≤
      (ambientSubfamilyPropertyThreeCommonHull dyadic.shading
        dyadic.reentry.regularized.selected
          (sourceShading := dyadic.reentry.normalization.croppedRefined)
          (sticky := rich.data) candidate).mass := by
  apply ambientPropertyThreeCommonHull_source_mass_lower_of_two_bands
    (fineMultiplicity := 2 ^ dyadic.level)
    dyadic.shading dyadic.reentry.regularized.selected
      dyadic.reentry.denseSubshading rich.data candidate candidateSub
      candidateExtremal.cubical hhalf
      (rich.terminal.muCoarse : ENNReal)
      (rich.terminal.regularity : ENNReal)
  · exact_mod_cast rich.terminal.muCoarse_pos
  · exact ENNReal.natCast_ne_top _
  · exact_mod_cast rich.terminal.regularity_pos
  · exact ENNReal.natCast_ne_top _
  · intro point hpoint
    exact (rich.terminal.coarse_pointMultiplicity_band hpoint).1
  · intro point hpoint
    simpa only [Nat.cast_mul] using
      (rich.terminal.coarse_pointMultiplicity_band hpoint).2
  · intro point hpoint
    exact_mod_cast dyadic.multiplicity_lower point hpoint
  · intro point hpoint
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using
      dyadic.multiplicity_upper point hpoint

end Kakeya.Assouad.PureWZ2
