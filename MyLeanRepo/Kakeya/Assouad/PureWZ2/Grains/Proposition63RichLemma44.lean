import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63Lemma44
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63RichStickyKernel

/-!
# Paper-faithful Lemma 4.4 from the rich Node 3 terminal certificate

This module joins the weak map produced by Lemma 4.3 to the exact terminal
fine/coarse pair produced by the second Node 3 call.  The coarse shading is
defined by one common, maximal-fine-multiplicity representative in each
coarse cell.  Its density is obtained from the exact terminal fiber cap, not
from the obsolete public coarse-cardinality cap.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

/-- Terminal-certificate specialization of the sharp common-representative
mass bridge.  This is the precise Node 3 datum consumed by Lemma 4.4. -/
theorem Proposition63TerminalMultiplicityCertificate.fine_mass_le_lemma44
    {delta rho sigma terminalLoss : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    (terminal : Proposition63TerminalMultiplicityCertificate
      (sigma := sigma) (terminalLoss := terminalLoss)
      cover fineShading coarseShading) :
    fineShading.mass ≤
      (terminal.muFine : ENNReal) *
        (proposition63Lemma44CoarseShading terminal.balanced).mass := by
  exact proposition63Lemma44_fine_mass_le terminal.balanced
    terminal.muFine terminal.fiber_pointMultiplicity_le

/-- The Node 3 terminal fiber cap can be bounded by one representative
complete-fiber cardinality at the public terminal loss. -/
theorem Proposition63TerminalMultiplicityCertificate.muFine_le_fiber_power
    {delta rho sigma terminalLoss : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    (terminal : Proposition63TerminalMultiplicityCertificate
      (sigma := sigma) (terminalLoss := terminalLoss)
      cover fineShading coarseShading) :
    ∃ parent : Fin coarse.card,
      (terminal.muFine : ENNReal) ≤
        Kakeya.realRpowENN (delta / rho)
            (2 - sigma - terminalLoss) *
          ((wz2PaperFullFiberIndices fine coarse parent).card : ENNReal) := by
  let parent : Fin coarse.card :=
    (Classical.choose terminal.packetCells_nonempty).1
  exact ⟨parent, terminal.fine_multiplicity_upper parent⟩

/-- The terminal cross-degree ledger supplies the exact cellwise absorption
used by Lemma 4.4.  Spending one further copy of the sticky loss weakens its
`rho ^ stickyLoss` factor to the required
`rho ^ (outputLoss - stickyLoss)` factor. -/
theorem Proposition63RichTerminalStickyData.fineDegree_absorption
    {delta sigma reentrySourceLoss reentryNormalizationLoss
      stickyLoss outputLoss : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source : WZ1PaperTubeShading family}
    {rho : WZ2PaperRequestedScale delta}
    {normalizationExponent : ℕ}
    {reentry : PureWZ2PropStickyReentryData
      (sigma := sigma) source normalizationExponent
      reentrySourceLoss reentryNormalizationLoss}
    (rich : Proposition63RichTerminalStickyData
      (sigma := sigma) (outputLoss := stickyLoss) source reentry rho)
    (hdouble : 2 * stickyLoss ≤ outputLoss) :
    Kakeya.realRpowENN rho.1 (outputLoss - stickyLoss) *
          (rich.terminal.regularity * rich.terminal.muCoarse : ℕ) ≤
        rich.terminal.fineDegreeFloor := by
  have powerLe :
      Kakeya.realRpowENN rho.1 (outputLoss - stickyLoss) ≤
        Kakeya.realRpowENN rho.1 stickyLoss := by
    apply pure_wz2_rpowENN_antitone
      rich.data.coarse_extremal.delta_pos
      rich.data.coarse_extremal.delta_le_one
    linarith
  exact (mul_le_mul_right' powerLe _).trans rich.cross_degree

/-- Construction-aware Lemma 4.4 on the exact rich terminal pair.  Besides
the usual output, retain the genuine fine representative at which the coarse
plane map is sampled.  This companion certificate is intentionally kept out
of `Proposition63Lemma44Data`: later M9 code can use the construction fact
without strengthening the stable Lemma-4.4 interface. -/
theorem proposition63_paper_lemma44_coarse_pair_of_terminal_with_map_witness
    {delta sigma lemma43SourceLoss lemma43Loss reentrySourceLoss
      reentryNormalizationLoss stickyLoss terminalLoss outputLoss : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source : WZ1PaperTubeShading family}
    {rho : WZ2PaperRequestedScale delta}
    {normalizationExponent : ℕ}
    (lemma43 : Proposition63Lemma43Data
      (sigma := sigma) (sourceLoss := lemma43SourceLoss)
      (targetLoss := lemma43Loss) source (rho.1 / 2))
    (reentry : PureWZ2PropStickyReentryData
      (sigma := sigma) lemma43.shading normalizationExponent
      reentrySourceLoss reentryNormalizationLoss)
    (rich : Proposition63RichTerminalStickyData
      (sigma := sigma) (outputLoss := stickyLoss)
      lemma43.shading reentry rho)
    (hdouble : 2 * stickyLoss ≤ outputLoss)
    (houtputLoss : 0 < outputLoss)
    :
    ∃ lemma44 : Proposition63Lemma44Data lemma43 rich.data outputLoss,
      ∀ point ∈ lemma44.coarseShading.union,
        ∃ finePoint ∈ lemma43.shading.union,
          lemma44.planeMap.planeMap point =
            lemma43.planeMap.planeMap finePoint := by
  let coarseShading :=
    proposition63Lemma44CoarseShading rich.terminal.balanced
  let fineMap := proposition63Lemma44FinePlaneMap lemma43 rich.data
  let fineMultiplicityFloor : ENNReal :=
    (rich.terminal.fineDegreeFloor * rich.terminal.muFine : ℕ)
  have fine_multiplicity_lower :
      ∀ cell ∈ rich.terminal.balanced.activeCells,
        fineMultiplicityFloor ≤
          (rich.data.refined.pointMultiplicity
            (proposition63Lemma44CellRepresentative
              rich.terminal.balanced cell) : ENNReal) := by
    intro cell cell_mem
    dsimp only [fineMultiplicityFloor]
    exact_mod_cast
      rich.terminal.fine_pointMultiplicity_floor_on_union
        (proposition63Lemma44CellRepresentative_in_union
          rich.terminal.balanced cell cell_mem)
  have cellwise_absorption :
      (Kakeya.realRpowENN rho.1 (outputLoss - stickyLoss) *
          (rich.terminal.regularity * rich.terminal.muCoarse : ℕ)) *
        (rich.terminal.muFine : ENNReal) ≤
        fineMultiplicityFloor := by
    have fineDegree_absorption :=
      rich.fineDegree_absorption hdouble
    dsimp only [fineMultiplicityFloor]
    rw [Nat.cast_mul]
    simpa only [Nat.cast_mul] using
      mul_le_mul_right' fineDegree_absorption
        (rich.terminal.muFine : ENNReal)
  have coarseDense : coarseShading.IsLambdaDense
      (Kakeya.realRpowENN rho.1 outputLoss) := by
    let coarseCap : ENNReal :=
      (rich.terminal.regularity * rich.terminal.muCoarse : ℕ)
    have coarseMultiplicityUpper : ∀ point,
        (rich.data.croppedCoarseShading.pointMultiplicity point : ENNReal) ≤
          coarseCap := by
      intro point
      by_cases point_mem : point ∈ rich.data.croppedCoarseShading.union
      · simpa only [coarseCap] using
          (rich.terminal.coarse_pointMultiplicity_band point_mem).2
      · have point_zero :
            rich.data.croppedCoarseShading.pointMultiplicity point = 0 := by
          simp only [Kakeya.Streamlined.Shading.pointMultiplicity]
          apply Finset.card_eq_zero.mpr
          rw [Finset.filter_eq_empty_iff]
          intro parent _ parent_point
          exact point_mem ⟨parent, parent_point⟩
        simp [point_zero]
    have cellwiseDense := proposition63Lemma44_associated_dense
      rich.terminal.balanced fineMultiplicityFloor coarseCap
      rich.terminal.muFine
      (Kakeya.realRpowENN rho.1 (outputLoss - stickyLoss))
      (Kakeya.realRpowENN rho.1 stickyLoss)
      (by exact_mod_cast rich.terminal.muFine_pos)
      (ENNReal.natCast_ne_top rich.terminal.muFine)
      fine_multiplicity_lower coarseMultiplicityUpper
      rich.terminal.fiber_pointMultiplicity_le cellwise_absorption
      rich.data.coarse_extremal.dense
    have power_identity :
        Kakeya.realRpowENN rho.1 outputLoss =
          Kakeya.realRpowENN rho.1 (outputLoss - stickyLoss) *
            Kakeya.realRpowENN rho.1 stickyLoss := by
      rw [← realRpowENN_add rich.data.coarse_extremal.delta_pos]
      congr 2
      ring
    simpa only [power_identity] using cellwiseDense
  have stickyPos : 0 < stickyLoss :=
    rich.terminalLoss_pos.trans_le rich.terminalLoss_le_output
  have weakened := rich.data.coarse_extremal.mono_loss (by linarith)
  have coarseExtremal : WZ2PaperCroppedIsExtremal
      sigma outputLoss rich.data.coarse coarseShading :=
    { delta_pos := weakened.delta_pos
      delta_le_one := weakened.delta_le_one
      nonempty := weakened.nonempty
      cwa_nearby_scales := weakened.cwa_nearby_scales
      cubical := proposition63Lemma44CoarseShading_cubical
        rich.terminal.balanced
      dense := coarseDense
      volume_upper := by
        rw [proposition63Lemma44CoarseShading_union_eq
          rich.terminal.balanced]
        exact weakened.volume_upper }
  refine ⟨{
    fineShading := rich.data.refined
    fine_subshading := ?_
    coarseShading := coarseShading
    coarse_subshading :=
      proposition63Lemma44CoarseShading_subshading rich.terminal.balanced
    coarse_extremal := coarseExtremal
    planeMap :=
      proposition63Lemma44CoarsePlaneMapOfBalanced
        fineMap rich.terminal.balanced
    planeMap_constant_on_cells :=
      proposition63Lemma44CoarsePlaneMapOfBalanced_constant_on_cells
        fineMap rich.terminal.balanced
    coarse_point_has_fine_witness := ?_
  }, ?_⟩
  · intro index point point_mem
    exact lemma43.subshading _ (rich.data.subshading index point_mem)
  · intro point point_mem
    let finePoint := proposition63Lemma44CellRepresentative
      rich.terminal.balanced (wz1PaperGridIndex rho.1 point)
    have representative :=
      proposition63Lemma44CoarseShading_representative
        rich.terminal.balanced point_mem
    exact ⟨finePoint, representative.1, representative.2⟩
  · intro point point_mem
    change point ∈ coarseShading.union at point_mem
    let finePoint := proposition63Lemma44CellRepresentative
      rich.terminal.balanced (wz1PaperGridIndex rho.1 point)
    have representative :=
      proposition63Lemma44CoarseShading_representative
        rich.terminal.balanced point_mem
    refine ⟨finePoint, ?_, ?_⟩
    · rcases representative.1 with ⟨index, hindex⟩
      exact ⟨rich.data.selected.embedding index,
        rich.data.subshading index hindex⟩
    · rfl

/-- Compatibility projection of the construction-aware terminal Lemma 4.4
producer. -/
theorem proposition63_paper_lemma44_coarse_pair_of_terminal
    {delta sigma lemma43SourceLoss lemma43Loss reentrySourceLoss
      reentryNormalizationLoss stickyLoss terminalLoss outputLoss : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source : WZ1PaperTubeShading family}
    {rho : WZ2PaperRequestedScale delta}
    {normalizationExponent : ℕ}
    (lemma43 : Proposition63Lemma43Data
      (sigma := sigma) (sourceLoss := lemma43SourceLoss)
      (targetLoss := lemma43Loss) source (rho.1 / 2))
    (reentry : PureWZ2PropStickyReentryData
      (sigma := sigma) lemma43.shading normalizationExponent
      reentrySourceLoss reentryNormalizationLoss)
    (rich : Proposition63RichTerminalStickyData
      (sigma := sigma) (outputLoss := stickyLoss)
      lemma43.shading reentry rho)
    (hdouble : 2 * stickyLoss ≤ outputLoss)
    (houtputLoss : 0 < outputLoss) :
    Nonempty (Proposition63Lemma44Data lemma43 rich.data outputLoss) := by
  rcases proposition63_paper_lemma44_coarse_pair_of_terminal_with_map_witness
      (terminalLoss := terminalLoss) lemma43 reentry rich hdouble houtputLoss
      with ⟨lemma44, _⟩
  exact ⟨lemma44⟩

end Kakeya.Assouad.PureWZ2

end
