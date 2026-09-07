import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63RichStickyKernel
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.StickyRobustCloseCount
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.HighMultiplicityThreshold
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.SelectedCardinalityCancellation

/-!
# Robust transversality from the rich Proposition 6.2 terminal certificate

The robust-scale call in paper Lemma 4.7 must retain both sides of the same
incidence decomposition.  The terminal certificate supplies exactly these:
the fine point multiplicity is at least `fineDegreeFloor * muFine`, while the
contribution of each coarse parent is at most `muFine`.  Coarse direction
packing therefore bounds a fine direction cap by
`stickyCoarseCloseCount * muFine`.

No `UniformTubeStructure`, arbitrary subfamily CWA inheritance, or unrelated
multiplicity band is used here.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory Set Finset

attribute [local instance] Classical.propDecidable

namespace Proposition63TerminalMultiplicityCertificate

variable
    {delta rho sigma terminalLoss : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    (certificate : Proposition63TerminalMultiplicityCertificate
      (sigma := sigma) (terminalLoss := terminalLoss)
      cover fineShading coarseShading)

/-- The exact terminal fiber cap and coarse direction packing give the robust
fine close-count bound used before the target-scale variation step. -/
theorem robust_close_count
    (hrho : 0 < rho)
    (hrhoSmall : rho ≤ 1 / 10000) :
    ∀ point ∈ fineShading.union, ∀ index,
      point ∈ fineShading.carrier index →
        (paperCloseDirectionCount fineShading point index rho : ENNReal) ≤
          stickyCoarseCloseCount * (certificate.muFine : ENNReal) := by
  have hcoarse : ∀ point ∈ coarseShading.union, ∀ index,
      point ∈ coarseShading.carrier index →
        (paperCloseDirectionCount coarseShading point index
          (10 * rho) : ENNReal) ≤ stickyCoarseCloseCount := by
    exact pureWz2_close_direction_count
      (delta := delta) (sigma := sigma)
      cover.coarse_essentially_distinct cover.coarse_line_class
      hrho hrhoSmall
  have halign : ∀ index : Fin fine.card,
      ∃ sign : ℝ, (sign = 1 ∨ sign = -1) ∧
        ‖(coarse.tube (selectParent cover index)).direction -
            sign • (fine.tube index).direction‖ ≤ rho / 2 :=
    fun index => directionAlignment_from_cover cover
      hrho index
  have parent_eq : ∀ index : Fin fine.card,
      cover.toWZ1PaperTubeCover.parent index = selectParent cover index := by
    intro index
    exact
      (cover.toWZ1PaperTubeCover.parent_unique index
        (selectParent cover index) (selectedParent_covers cover index)).symm
  intro point _point_mem index point_index
  exact pureWz2_robust_close_count
    (hsub := fun _ => Set.Subset.rfl) halign
    certificate.balanced.point_compatibility
    (certificate.muFine : ENNReal)
    (fun parent point => by
      have multiplicity_le :
          PureWZ2.fiberPointMultiplicity cover fineShading parent point ≤
            cover.toWZ1PaperTubeCover.fiberPointMultiplicity
              fineShading parent point := by
        unfold PureWZ2.fiberPointMultiplicity
          WZ1PaperTubeCover.fiberPointMultiplicity
        apply Finset.card_le_card
        intro source source_mem
        rcases Finset.mem_filter.mp source_mem with
          ⟨_source_univ, source_parent, source_point⟩
        apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_filter.mpr
          ⟨Finset.mem_univ source, by simpa [parent_eq] using source_parent⟩,
          source_point⟩
      have multiplicity_le_enn :
          (PureWZ2.fiberPointMultiplicity cover fineShading parent point :
              ENNReal) ≤
            (cover.toWZ1PaperTubeCover.fiberPointMultiplicity
              fineShading parent point : ENNReal) := by
        exact_mod_cast multiplicity_le
      exact multiplicity_le_enn.trans
        (certificate.fiber_pointMultiplicity_le parent point))
    stickyCoarseCloseCount hcoarse
    hrho point index point_index

/-- Once the terminal fine degree dominates twice the absolute coarse packing
constant, robust close directions occupy at most half of the exact fine
point multiplicity. -/
theorem robust_close_count_absorbed
    (hrho : 0 < rho)
    (hrhoSmall : rho ≤ 1 / 10000)
    (hdegree :
      2 * stickyCoarseCloseCount ≤
        (certificate.fineDegreeFloor : ENNReal)) :
    ∀ point ∈ fineShading.union, ∀ index,
      point ∈ fineShading.carrier index →
        2 * paperCloseDirectionCount fineShading point index rho ≤
          certificate.fineDegreeFloor * certificate.muFine := by
  intro point point_mem index point_index
  have closeBound := certificate.robust_close_count hrho hrhoSmall
    point point_mem index point_index
  have boundENN :
      (2 * paperCloseDirectionCount fineShading point index rho : ℕ) ≤
        certificate.fineDegreeFloor * certificate.muFine := by
    exact_mod_cast
      (calc
        (2 : ENNReal) *
              (paperCloseDirectionCount fineShading point index rho :
                ENNReal) ≤
            2 * (stickyCoarseCloseCount *
              (certificate.muFine : ENNReal)) := by gcongr
        _ = (2 * stickyCoarseCloseCount) *
              (certificate.muFine : ENNReal) := by ring
        _ ≤ (certificate.fineDegreeFloor : ENNReal) *
              (certificate.muFine : ENNReal) := by gcongr)
  exact boundENN

end Proposition63TerminalMultiplicityCertificate

namespace Proposition63RichTerminalStickyData

variable
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

/-- Coarse CWA cardinality, the terminal coarse multiplicity floor, and the
cross-degree ledger together force the terminal fine packet degree above any
fixed finite target once the corresponding small-scale power has been
absorbed.  This is the absolute degree margin needed by the robust-scale step
of paper Lemma 4.7; it is not an additional runtime certificate. -/
theorem fineDegreeFloor_ge_fixed
    (target : ENNReal)
    (houtputLoss : 0 ≤ outputLoss)
    (hrhoSmall : rho.1 ≤ 1 / 24)
    (habsorb :
      (12 * target) * ENNReal.ofReal Real.pi ≤
        Kakeya.realRpowENN rho.1 (-sigma + 4 * outputLoss)) :
    target ≤ (rich.terminal.fineDegreeFloor : ENNReal) := by
  have cardinalityLower :
      target ≤
        Kakeya.realRpowENN rho.1 (2 - sigma + 3 * outputLoss) *
          rich.data.coarse.enncard :=
    density_power_cardinality_ge_fixed
      rich.data.coarse_extremal target hrhoSmall rfl habsorb
  have exponentCompare :
      2 - sigma + rich.terminalLoss + outputLoss ≤
        2 - sigma + 3 * outputLoss := by
    linarith [rich.terminalLoss_le_output]
  have powerCompare :
      Kakeya.realRpowENN rho.1 (2 - sigma + 3 * outputLoss) ≤
        Kakeya.realRpowENN rho.1
          (2 - sigma + rich.terminalLoss + outputLoss) :=
    realRpowENN_antitone rich.data.coarse_extremal.delta_pos
      rich.data.coarse_extremal.delta_le_one exponentCompare
  have geometryOne :
      (1 : ENNReal) ≤ 55296 * Kakeya.deltaTubeVolume 1 := by
    calc
      (1 : ENNReal) ≤ Kakeya.deltaTubeVolume 1 :=
        one_le_deltaTubeVolume_one
      _ ≤ 55296 * Kakeya.deltaTubeVolume 1 := by
        simpa using mul_le_mul_right'
          (show (1 : ENNReal) ≤ 55296 by norm_num)
          (Kakeya.deltaTubeVolume 1)
  have coarseFloor :
      Kakeya.realRpowENN rho.1 (2 - sigma + rich.terminalLoss) *
          rich.data.coarse.enncard ≤
        (rich.terminal.muCoarse : ENNReal) := by
    calc
      Kakeya.realRpowENN rho.1 (2 - sigma + rich.terminalLoss) *
            rich.data.coarse.enncard =
          1 * (Kakeya.realRpowENN rho.1
            (2 - sigma + rich.terminalLoss) *
              rich.data.coarse.enncard) := by simp
      _ ≤ (55296 * Kakeya.deltaTubeVolume 1) *
          (Kakeya.realRpowENN rho.1
            (2 - sigma + rich.terminalLoss) *
              rich.data.coarse.enncard) := by gcongr
      _ = ((55296 * Kakeya.deltaTubeVolume 1) *
            Kakeya.realRpowENN rho.1
              (2 - sigma + rich.terminalLoss)) *
          rich.data.coarse.enncard := by ring
      _ ≤ (rich.terminal.muCoarse : ENNReal) :=
        rich.terminal.coarse_multiplicity_floor
  have muCoarseLeRegular :
      rich.terminal.muCoarse ≤
        rich.terminal.regularity * rich.terminal.muCoarse := by
    calc
      rich.terminal.muCoarse =
          1 * rich.terminal.muCoarse := by simp
      _ ≤ rich.terminal.regularity * rich.terminal.muCoarse :=
        Nat.mul_le_mul_right rich.terminal.muCoarse
          rich.terminal.regularity_pos
  calc
    target ≤
        Kakeya.realRpowENN rho.1 (2 - sigma + 3 * outputLoss) *
          rich.data.coarse.enncard := cardinalityLower
    _ ≤ Kakeya.realRpowENN rho.1
          (2 - sigma + rich.terminalLoss + outputLoss) *
            rich.data.coarse.enncard := by gcongr
    _ = Kakeya.realRpowENN rho.1 outputLoss *
          (Kakeya.realRpowENN rho.1
            (2 - sigma + rich.terminalLoss) *
              rich.data.coarse.enncard) := by
        rw [← mul_assoc, ← realRpowENN_add
          rich.data.coarse_extremal.delta_pos]
        congr 1 <;> ring
    _ ≤ Kakeya.realRpowENN rho.1 outputLoss *
          (rich.terminal.muCoarse : ENNReal) := by gcongr
    _ ≤ Kakeya.realRpowENN rho.1 outputLoss *
          (rich.terminal.regularity * rich.terminal.muCoarse : ℕ) := by
        gcongr
    _ ≤ (rich.terminal.fineDegreeFloor : ENNReal) := rich.cross_degree

/-- The rich terminal output supplies the robust close-count absorption after
the fixed packing constant has been absorbed uniformly into the coarse-scale
CWA cardinality lower bound. -/
theorem robust_close_count_absorbed_of_cwa
    (houtputLoss : 0 ≤ outputLoss)
    (hrhoSmall : rho.1 ≤ 1 / 10000)
    (habsorb :
      (12 * (2 * stickyCoarseCloseCount)) * ENNReal.ofReal Real.pi ≤
        Kakeya.realRpowENN rho.1 (-sigma + 4 * outputLoss)) :
    ∀ point ∈ rich.data.refined.union, ∀ index,
      point ∈ rich.data.refined.carrier index →
        2 * paperCloseDirectionCount rich.data.refined point index rho.1 ≤
          rich.terminal.fineDegreeFloor * rich.terminal.muFine := by
  apply rich.terminal.robust_close_count_absorbed
    rich.data.coarse_extremal.delta_pos hrhoSmall
  exact rich.fineDegreeFloor_ge_fixed
    (2 * stickyCoarseCloseCount) houtputLoss
    (hrhoSmall.trans (by norm_num)) habsorb

/-- The exact one-scale density cancellation on the selected terminal fine
family.  The caller chooses a positive `densityPower` small enough to pay the
single Node 3 refinement, its terminal regularity, and the source volume
upper bound.  No loss from another spatial scale appears in this statement. -/
theorem fineMultiplicity_density_of_scalar
    (densityPower : ENNReal)
    (hdeltaSmall : delta ≤ 1 / 12)
    (hdensityScalar :
      densityPower *
          ((rich.terminal.regularity : ENNReal) *
            Kakeya.realRpowENN delta (sigma - normalizationLoss)) ≤
        wz2PaperPureRefinementFraction delta 61 *
          Kakeya.realRpowENN delta (normalizationLoss + 2)) :
    densityPower * rich.data.selected.family.enncard ≤
      (rich.terminal.fineDegreeFloor * rich.terminal.muFine : ℕ) := by
  let scaleFactor : ENNReal :=
    (rich.terminal.regularity : ENNReal) *
      Kakeya.realRpowENN delta (sigma - normalizationLoss)
  have scaleFactorPos : 0 < scaleFactor := by
    apply ENNReal.mul_pos
    · exact_mod_cast rich.terminal.regularity_pos.ne'
    · exact (ENNReal.ofReal_pos.mpr
        (Real.rpow_pos_of_pos reentry.cropped_extremal.delta_pos _)).ne'
  have scaleFactorTop : scaleFactor ≠ ⊤ := by
    exact ENNReal.mul_ne_top (by simp) (by simp [Kakeya.realRpowENN])
  have selectedCardinality :=
    selected_cardinality_cancellation reentry.cropped_extremal
      reentry.geometry.line_class rich.data.selected hdeltaSmall
  have terminalVolume :
      volume rich.data.refined.union ≤
        Kakeya.realRpowENN delta (sigma - normalizationLoss) := by
    apply (measure_mono ?_).trans reentry.cropped_extremal.volume_upper
    rintro point ⟨index, point_mem⟩
    exact ⟨rich.data.selected.embedding index,
      rich.data.subshading index point_mem⟩
  apply (ENNReal.mul_le_mul_iff_right
    scaleFactorPos.ne' scaleFactorTop).mp
  calc
    scaleFactor * (densityPower * rich.data.selected.family.enncard) =
        (densityPower * scaleFactor) *
          rich.data.selected.family.enncard := by ring
    _ ≤ (wz2PaperPureRefinementFraction delta 61 *
          Kakeya.realRpowENN delta (normalizationLoss + 2)) *
        rich.data.selected.family.enncard := by gcongr
    _ = wz2PaperPureRefinementFraction delta 61 *
        (Kakeya.realRpowENN delta (normalizationLoss + 2) *
          rich.data.selected.family.enncard) := by ring
    _ ≤ wz2PaperPureRefinementFraction delta 61 * croppedShading.mass := by
      gcongr
    _ ≤ rich.data.refined.mass := rich.total_mass_retention
    _ ≤ (((rich.terminal.regularity *
          rich.terminal.fineDegreeFloor : ℕ) : ENNReal) *
        rich.terminal.muFine) * volume rich.data.refined.union :=
      rich.terminal.fine_mass_le_degree_mul_volume
    _ ≤ (((rich.terminal.regularity *
          rich.terminal.fineDegreeFloor : ℕ) : ENNReal) *
        rich.terminal.muFine) *
          Kakeya.realRpowENN delta (sigma - normalizationLoss) := by gcongr
    _ = scaleFactor *
          ((rich.terminal.fineDegreeFloor * rich.terminal.muFine : ℕ) :
            ENNReal) := by
      dsimp only [scaleFactor]
      simp only [Nat.cast_mul]
      ring

/-- The same terminal mass ledger controls the cardinality of the whole
cropped source, not merely the final selected subfamily.  This stronger form
is the one needed to compare an outer robust fiber cap with the total degree
of a dependent target-scale call. -/
theorem fineMultiplicity_density_of_source_cardinality
    (densityPower : ENNReal)
    (hdeltaSmall : delta ≤ 1 / 12)
    (hdensityScalar :
      densityPower *
          ((rich.terminal.regularity : ENNReal) *
            Kakeya.realRpowENN delta (sigma - normalizationLoss)) ≤
        wz2PaperPureRefinementFraction delta 61 *
          Kakeya.realRpowENN delta (normalizationLoss + 2)) :
    densityPower * croppedFamily.enncard ≤
      (rich.terminal.fineDegreeFloor * rich.terminal.muFine : ℕ) := by
  let scaleFactor : ENNReal :=
    (rich.terminal.regularity : ENNReal) *
      Kakeya.realRpowENN delta (sigma - normalizationLoss)
  have scaleFactorPos : 0 < scaleFactor := by
    apply ENNReal.mul_pos
    · exact_mod_cast rich.terminal.regularity_pos.ne'
    · exact (ENNReal.ofReal_pos.mpr
        (Real.rpow_pos_of_pos reentry.cropped_extremal.delta_pos _)).ne'
  have scaleFactorTop : scaleFactor ≠ ⊤ := by
    exact ENNReal.mul_ne_top (by simp) (by simp [Kakeya.realRpowENN])
  let all := Kakeya.Streamlined.TubeSubfamily.fromFinset
    croppedFamily (Finset.univ : Finset (Fin croppedFamily.card))
  have sourceCardinality :
      Kakeya.realRpowENN delta (normalizationLoss + 2) *
          croppedFamily.enncard ≤ croppedShading.mass := by
    have selectedCardinality :=
      selected_cardinality_cancellation reentry.cropped_extremal
        reentry.geometry.line_class all hdeltaSmall
    have allCard : all.family.enncard = croppedFamily.enncard := by
      simp [all, Kakeya.Streamlined.TubeSubfamily.fromFinset,
        Kakeya.Streamlined.TubeFamily.enncard]
    simpa only [allCard] using selectedCardinality
  have terminalVolume :
      volume rich.data.refined.union ≤
        Kakeya.realRpowENN delta (sigma - normalizationLoss) := by
    apply (measure_mono ?_).trans reentry.cropped_extremal.volume_upper
    rintro point ⟨index, point_mem⟩
    exact ⟨rich.data.selected.embedding index,
      rich.data.subshading index point_mem⟩
  apply (ENNReal.mul_le_mul_iff_right
    scaleFactorPos.ne' scaleFactorTop).mp
  calc
    scaleFactor * (densityPower * croppedFamily.enncard) =
        (densityPower * scaleFactor) * croppedFamily.enncard := by ring
    _ ≤ (wz2PaperPureRefinementFraction delta 61 *
          Kakeya.realRpowENN delta (normalizationLoss + 2)) *
        croppedFamily.enncard := by gcongr
    _ = wz2PaperPureRefinementFraction delta 61 *
        (Kakeya.realRpowENN delta (normalizationLoss + 2) *
          croppedFamily.enncard) := by ring
    _ ≤ wz2PaperPureRefinementFraction delta 61 * croppedShading.mass := by
      gcongr
    _ ≤ rich.data.refined.mass := rich.total_mass_retention
    _ ≤ (((rich.terminal.regularity *
          rich.terminal.fineDegreeFloor : ℕ) : ENNReal) *
        rich.terminal.muFine) * volume rich.data.refined.union :=
      rich.terminal.fine_mass_le_degree_mul_volume
    _ ≤ (((rich.terminal.regularity *
          rich.terminal.fineDegreeFloor : ℕ) : ENNReal) *
        rich.terminal.muFine) *
          Kakeya.realRpowENN delta (sigma - normalizationLoss) := by gcongr
    _ = scaleFactor *
          ((rich.terminal.fineDegreeFloor * rich.terminal.muFine : ℕ) :
            ENNReal) := by
      dsimp only [scaleFactor]
      simp only [Nat.cast_mul]
      ring

/-- Uncancelled source-cardinality ledger for the terminal total fine degree.
Keeping the regularity/volume scale factor on the right lets the two-call
argument compare directly with the outer fiber cap, without choosing an
auxiliary runtime density power. -/
theorem fineMultiplicity_source_cardinality_ledger
    (hdeltaSmall : delta ≤ 1 / 12) :
    wz2PaperPureRefinementFraction delta 61 *
        Kakeya.realRpowENN delta (normalizationLoss + 2) *
          croppedFamily.enncard ≤
      ((rich.terminal.regularity : ENNReal) *
        Kakeya.realRpowENN delta (sigma - normalizationLoss)) *
        ((rich.terminal.fineDegreeFloor * rich.terminal.muFine : ℕ) :
          ENNReal) := by
  let all := Kakeya.Streamlined.TubeSubfamily.fromFinset
    croppedFamily (Finset.univ : Finset (Fin croppedFamily.card))
  have sourceCardinality :
      Kakeya.realRpowENN delta (normalizationLoss + 2) *
          croppedFamily.enncard ≤ croppedShading.mass := by
    have selectedCardinality :=
      selected_cardinality_cancellation reentry.cropped_extremal
        reentry.geometry.line_class all hdeltaSmall
    have allCard : all.family.enncard = croppedFamily.enncard := by
      simp [all, Kakeya.Streamlined.TubeSubfamily.fromFinset,
        Kakeya.Streamlined.TubeFamily.enncard]
    simpa only [allCard] using selectedCardinality
  have terminalVolume :
      volume rich.data.refined.union ≤
        Kakeya.realRpowENN delta (sigma - normalizationLoss) := by
    apply (measure_mono ?_).trans reentry.cropped_extremal.volume_upper
    rintro point ⟨index, point_mem⟩
    exact ⟨rich.data.selected.embedding index,
      rich.data.subshading index point_mem⟩
  calc
    wz2PaperPureRefinementFraction delta 61 *
          Kakeya.realRpowENN delta (normalizationLoss + 2) *
            croppedFamily.enncard =
        wz2PaperPureRefinementFraction delta 61 *
          (Kakeya.realRpowENN delta (normalizationLoss + 2) *
            croppedFamily.enncard) := by ring
    _ ≤ wz2PaperPureRefinementFraction delta 61 * croppedShading.mass := by
      gcongr
    _ ≤ rich.data.refined.mass := rich.total_mass_retention
    _ ≤ (((rich.terminal.regularity *
          rich.terminal.fineDegreeFloor : ℕ) : ENNReal) *
        rich.terminal.muFine) * volume rich.data.refined.union :=
      rich.terminal.fine_mass_le_degree_mul_volume
    _ ≤ (((rich.terminal.regularity *
          rich.terminal.fineDegreeFloor : ℕ) : ENNReal) *
        rich.terminal.muFine) *
          Kakeya.realRpowENN delta (sigma - normalizationLoss) := by gcongr
    _ = ((rich.terminal.regularity : ENNReal) *
          Kakeya.realRpowENN delta (sigma - normalizationLoss)) *
        ((rich.terminal.fineDegreeFloor * rich.terminal.muFine : ℕ) :
          ENNReal) := by
      simp only [Nat.cast_mul]
      ring

end Proposition63RichTerminalStickyData

end Kakeya.Assouad.PureWZ2

end
