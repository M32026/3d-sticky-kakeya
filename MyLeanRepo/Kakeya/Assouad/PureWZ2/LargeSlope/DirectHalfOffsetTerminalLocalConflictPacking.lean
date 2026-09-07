import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.DirectHalfOffsetTerminalConflictCleanupClosure
import MyLeanRepo.Kakeya.Assouad.PureWZ2.OrdinaryLineConflictPacking

/-!
# Local packing for the actual half-offset terminal conflict graph

A centered conflict in the literal terminal pulls back to a four-coordinate
box of width `w` in the original source parameters.  The tube-parameter to
paper-line-distance bridge puts the two source supporting lines at distance
at most `6 * w`.  Ordinary essential distinctness of the original source then
gives a seven-coordinate packing bound, including the bounded longitudinal
parameter.  In particular, this estimate has no ambient-family-cardinality
factor.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

namespace PureWZ2DirectCommonYSourceAssembly

variable
    {logExponent : ℕ}
    {sigma epsilon delta : ℝ}
    (commonSource : PureWZ2DirectCommonYSourceAssembly
      logExponent sigma epsilon delta)

namespace TerminalGeometry

/-- Explicit local-packing degree at source parameter width `width`. -/
def actualLocalConflictPackingDegree (width : ℝ) : ℕ :=
  2561 *
    (2 * Nat.ceil (6 * width / (delta / 10000)) + 1) ^ 6

/-- The local-packing degree used by the actual terminal cleanup. -/
abbrev actualLocalConflictDegreeBound
    (terminal : commonSource.TerminalGeometry) : ENNReal :=
  (actualLocalConflictPackingDegree (delta := delta)
    (actualConflictWidth commonSource terminal) : ENNReal)

/-- A fixed coefficient absorbing the ceiling in the local packing degree. -/
def actualLocalConflictPackingCoefficient : ENNReal :=
  ENNReal.ofReal
    (2561 *
      (120003 * actualConflictWidthCoefficient) ^ 6)

/--
The actual terminal centered-conflict degree is bounded by a local source-line
packing number.  Unlike the Frostman estimate, this bound has no factor of the
ambient source cardinality.
-/
theorem centered_conflict_degree_le_local_packing
    (hInverse : AnisotropicTubeParamsInverseClusterStatement)
    (terminal : commonSource.TerminalGeometry)
    (width : ℝ)
    (hwidth : width = actualConflictWidth commonSource terminal)
    (hwidthNonnegative : 0 ≤ width) :
    ∀ reference : Fin terminal.centeredFamily.card,
      ((Finset.univ : Finset (Fin terminal.centeredFamily.card)).filter
        (pureWZ2PaperCenteredConflict terminal.centeredFamily reference)).card ≤
          actualLocalConflictPackingDegree
            (delta := delta) width := by
  intro reference
  let conflicts : Finset (Fin terminal.centeredFamily.card) :=
    Finset.univ.filter
      (pureWZ2PaperCenteredConflict terminal.centeredFamily reference)
  let sourceConflicts :
      Finset (Fin (conflictSourceFamily commonSource).card) :=
    conflicts.image (centeredSourceParent commonSource terminal)
  let sourceBall :
      Finset (Fin (conflictSourceFamily commonSource).card) :=
    Finset.univ.filter fun source =>
      wz1PaperLineDistance
          ((conflictSourceFamily commonSource).tube source)
          ((conflictSourceFamily commonSource).tube
            (centeredSourceParent commonSource terminal reference)) ≤
        6 * width
  have hdelta : 0 < delta :=
    commonSource.halfOffsetAssembly.cfg.extremal.delta_pos
  have hsourceSubset : sourceConflicts ⊆ sourceBall := by
    intro source hsource
    rcases Finset.mem_image.mp hsource with ⟨target, htarget, rfl⟩
    have hconflict := (Finset.mem_filter.mp htarget).2
    have hcluster :=
      source_parameter_cluster_of_totalAffineMap_centered_conflict
        commonSource hInverse terminal reference target hconflict
    have hline :
        wz1PaperLineDistance
            ((conflictSourceFamily commonSource).tube
              (centeredSourceParent commonSource terminal target))
            ((conflictSourceFamily commonSource).tube
              (centeredSourceParent commonSource terminal reference)) ≤
          6 * width := by
      rw [wz1PaperLineDistance_symm]
      apply wz1PaperLineDistance_le_of_tubeParams_close
        (commonSource.halfOffsetAssembly.cfg.line_class
          (centeredSourceParent commonSource terminal reference))
        (commonSource.halfOffsetAssembly.cfg.line_class
          (centeredSourceParent commonSource terminal target))
        hwidthNonnegative
      rw [hwidth]
      exact hcluster.1
      rw [hwidth]
      exact hcluster.2.1
      rw [hwidth]
      exact hcluster.2.2.1
      rw [hwidth]
      exact hcluster.2.2.2
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, hline⟩
  have hsourceCard :
      sourceBall.card ≤
        pureWZ2OrdinaryLineConflictDegreeWithin delta (6 * width) := by
    have hboundedBase :
        HasBoundedBase (conflictSourceFamily commonSource) 8 := by
      intro source
      exact
        (commonSource.halfOffsetAssembly.cfg.bounded_base source).trans
          (by norm_num)
    exact pureWZ2_ordinary_line_conflict_degree_within
      hdelta (6 * width) (by positivity)
      commonSource.halfOffsetAssembly.cfg.line_class
      hboundedBase
      commonSource.halfOffsetAssembly.cfg.extremal.cwa_nearby_scales.2.2.1
      (centeredSourceParent commonSource terminal reference)
  have htargetCard : conflicts.card = sourceConflicts.card := by
    exact (Finset.card_image_of_injective _
      (centeredSourceParent_injective commonSource terminal)).symm
  change conflicts.card ≤ actualLocalConflictPackingDegree
    (delta := delta) width
  rw [htargetCard]
  calc
    sourceConflicts.card ≤ sourceBall.card :=
      Finset.card_le_card hsourceSubset
    _ ≤ pureWZ2OrdinaryLineConflictDegreeWithin delta (6 * width) :=
      hsourceCard
    _ = actualLocalConflictPackingDegree (delta := delta) width := by
      unfold pureWZ2OrdinaryLineConflictDegreeWithin
        actualLocalConflictPackingDegree
      norm_num [Fin.prod_univ_succ]
      ring

/-- The unconditional actual-map specialization of the local packing bound. -/
theorem actual_centered_conflict_degree_le_local_packing
    (terminal : commonSource.TerminalGeometry) :
    ∀ reference : Fin terminal.centeredFamily.card,
      ((Finset.univ : Finset (Fin terminal.centeredFamily.card)).filter
        (pureWZ2PaperCenteredConflict terminal.centeredFamily reference)).card ≤
          actualLocalConflictPackingDegree (delta := delta)
            (actualConflictWidth commonSource terminal) := by
  exact centered_conflict_degree_le_local_packing
    commonSource anisotropic_tube_params_inverse_cluster terminal
    (actualConflictWidth commonSource terminal) rfl
    (commonSource.halfOffsetAssembly.cfg.extremal.delta_pos.le.trans
      (delta_le_actualConflictWidth commonSource terminal))

/-- Construct the ordinary-distinct cleanup using local line-parameter
packing.  Unlike the earlier Frostman wrapper, this introduces no ambient
family-cardinality factor and requires no upper restriction on the conflict
width. -/
theorem toLocalDistinctCleanup
    (terminal : commonSource.TerminalGeometry) :
    Nonempty (PureWZ2HalfOffsetTerminalDistinctCleanupData
      commonSource terminal
        (actualLocalConflictDegreeBound commonSource terminal)) := by
  apply centered_distinct_selection commonSource terminal
    (actualLocalConflictDegreeBound commonSource terminal)
  intro reference
  exact_mod_cast actual_centered_conflict_degree_le_local_packing
    commonSource terminal reference

/-- The local packing degree has the expected six-fold source-scale loss. -/
theorem actualLocalConflictPackingDegree_le_source_power
    (terminal : commonSource.TerminalGeometry)
    (htarget :
      terminal.targetDelta ≤ Real.rpow delta (1 - 2 * epsilon)) :
    (actualLocalConflictPackingDegree (delta := delta)
        (actualConflictWidth commonSource terminal) : ENNReal) ≤
      actualLocalConflictPackingCoefficient *
        Kakeya.realRpowENN delta (-30 * epsilon) := by
  let coefficient := actualConflictWidthCoefficient
  let width := actualConflictWidth commonSource terminal
  let sourcePower := Real.rpow delta (-5 * epsilon)
  let ratio := 6 * width / (delta / 10000)
  let cells := 2 * Nat.ceil ratio + 1
  have hdelta : 0 < delta :=
    commonSource.halfOffsetAssembly.cfg.extremal.delta_pos
  have hwidthNonnegative : 0 ≤ width := by
    dsimp only [width]
    exact hdelta.le.trans (delta_le_actualConflictWidth commonSource terminal)
  have hcoefficientNonnegative : 0 ≤ coefficient := by
    exact actualConflictWidthCoefficient_pos.le
  have hsourcePowerPositive : 0 < sourcePower := by
    exact Real.rpow_pos_of_pos hdelta _
  have hpowerIdentity :
      Real.rpow delta (1 - 5 * epsilon) = delta * sourcePower := by
    calc
      Real.rpow delta (1 - 5 * epsilon) =
          Real.rpow delta (1 + (-5 * epsilon)) := by
        congr 1
        ring
      _ = Real.rpow delta 1 * Real.rpow delta (-5 * epsilon) :=
        Real.rpow_add hdelta 1 (-5 * epsilon)
      _ = delta * sourcePower := by
        dsimp only [sourcePower]
        congr 1
        exact Real.rpow_one delta
  have hwidthPower : width ≤ coefficient * delta * sourcePower := by
    calc
      width ≤ coefficient * Real.rpow delta (1 - 5 * epsilon) := by
        exact actualConflictWidth_le_source_power commonSource terminal htarget
      _ = coefficient * delta * sourcePower := by
        rw [hpowerIdentity, mul_assoc]
  have hone : 1 ≤ coefficient * sourcePower := by
    have hsourceWidth : delta ≤ width :=
      delta_le_actualConflictWidth commonSource terminal
    nlinarith
  have hratioNonnegative : 0 ≤ ratio := by
    dsimp only [ratio]
    positivity
  have hratio :
      ratio ≤ 60000 * coefficient * sourcePower := by
    dsimp only [ratio]
    apply (div_le_iff₀ (by positivity : 0 < delta / 10000)).2
    nlinarith
  have hceil :
      (Nat.ceil ratio : ℝ) ≤
        60001 * coefficient * sourcePower := by
    have hceilRaw : (Nat.ceil ratio : ℝ) ≤ ratio + 1 :=
      (Nat.ceil_lt_add_one hratioNonnegative).le
    calc
      (Nat.ceil ratio : ℝ) ≤ ratio + 1 := hceilRaw
      _ ≤ 60000 * coefficient * sourcePower + 1 := by
        linarith
      _ ≤ 60001 * coefficient * sourcePower := by
        nlinarith
  have hcells :
      (cells : ℝ) ≤ 120003 * coefficient * sourcePower := by
    dsimp only [cells]
    norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    nlinarith
  have hsourcePowerSix :
      sourcePower ^ 6 = Real.rpow delta (-30 * epsilon) := by
    dsimp only [sourcePower]
    calc
      Real.rpow delta (-5 * epsilon) ^ 6 =
          Real.rpow (Real.rpow delta (-5 * epsilon)) (6 : ℝ) :=
        (Real.rpow_natCast _ 6).symm
      _ = Real.rpow delta ((-5 * epsilon) * 6) :=
        (Real.rpow_mul hdelta.le (-5 * epsilon) 6).symm
      _ = Real.rpow delta (-30 * epsilon) := by ring
  have hreal :
      ((actualLocalConflictPackingDegree (delta := delta) width : ℕ) : ℝ) ≤
        (2561 * (120003 * coefficient) ^ 6) *
          Real.rpow delta (-30 * epsilon) := by
    have hcellsSix :
        (cells : ℝ) ^ 6 ≤
          (120003 * coefficient * sourcePower) ^ 6 := by
      gcongr
    calc
      ((actualLocalConflictPackingDegree (delta := delta) width : ℕ) : ℝ) =
          2561 * (cells : ℝ) ^ 6 := by
        simp only [actualLocalConflictPackingDegree, cells, ratio,
          Nat.cast_mul, Nat.cast_pow, Nat.cast_add, Nat.cast_ofNat]
      _ ≤ 2561 * (120003 * coefficient * sourcePower) ^ 6 := by
        gcongr
      _ = (2561 * (120003 * coefficient) ^ 6) *
          Real.rpow delta (-30 * epsilon) := by
        rw [mul_pow, hsourcePowerSix]
        ring
  rw [← ENNReal.ofReal_natCast]
  unfold actualLocalConflictPackingCoefficient Kakeya.realRpowENN
  rw [← ENNReal.ofReal_mul (by positivity)]
  exact ENNReal.ofReal_mono hreal

/-- The actual terminal conflict degree inherits the local source-power bound. -/
theorem centered_conflict_degree_le_local_source_power
    (terminal : commonSource.TerminalGeometry)
    (htarget :
      terminal.targetDelta ≤ Real.rpow delta (1 - 2 * epsilon)) :
    ∀ reference : Fin terminal.centeredFamily.card,
      (((Finset.univ : Finset (Fin terminal.centeredFamily.card)).filter
        (pureWZ2PaperCenteredConflict terminal.centeredFamily reference)).card :
          ENNReal) ≤
        actualLocalConflictPackingCoefficient *
          Kakeya.realRpowENN delta (-30 * epsilon) := by
  intro reference
  have hpacking := actual_centered_conflict_degree_le_local_packing
    commonSource terminal reference
  have hpackingENN :
      (((Finset.univ : Finset (Fin terminal.centeredFamily.card)).filter
        (pureWZ2PaperCenteredConflict terminal.centeredFamily reference)).card :
          ENNReal) ≤
        (actualLocalConflictPackingDegree (delta := delta)
          (actualConflictWidth commonSource terminal) : ENNReal) := by
    exact_mod_cast hpacking
  exact hpackingENN.trans
    (actualLocalConflictPackingDegree_le_source_power
      commonSource terminal htarget)

/-- The cleanup loss `degree + 1` has the same source exponent as the local
packing degree; the additional one is absorbed into the fixed coefficient. -/
theorem actualLocalConflictDegreeBound_add_one_le_source_power
    (terminal : commonSource.TerminalGeometry)
    (htarget :
      terminal.targetDelta ≤ Real.rpow delta (1 - 2 * epsilon)) :
    actualLocalConflictDegreeBound commonSource terminal + 1 ≤
      (actualLocalConflictPackingCoefficient + 1) *
        Kakeya.realRpowENN delta (-30 * epsilon) := by
  have hdelta := commonSource.halfOffsetAssembly.cfg.extremal.delta_pos
  have hdeltaOne := commonSource.halfOffsetAssembly.cfg.extremal.delta_le_one
  have hpowerOne : (1 : ENNReal) ≤
      Kakeya.realRpowENN delta (-30 * epsilon) := by
    simpa [Kakeya.realRpowENN] using
      (realRpowENN_antitone hdelta hdeltaOne
        (show -30 * epsilon ≤ 0 by
          linarith [commonSource.lemma31.epsilon_pos]))
  calc
    actualLocalConflictDegreeBound commonSource terminal + 1 ≤
        actualLocalConflictPackingCoefficient *
            Kakeya.realRpowENN delta (-30 * epsilon) + 1 := by
      gcongr
      exact actualLocalConflictPackingDegree_le_source_power
        commonSource terminal htarget
    _ ≤ actualLocalConflictPackingCoefficient *
          Kakeya.realRpowENN delta (-30 * epsilon) +
        1 * Kakeya.realRpowENN delta (-30 * epsilon) := by
      simpa only [one_mul] using add_le_add_right hpowerOne
        (actualLocalConflictPackingCoefficient *
          Kakeya.realRpowENN delta (-30 * epsilon))
    _ = (actualLocalConflictPackingCoefficient + 1) *
        Kakeya.realRpowENN delta (-30 * epsilon) := by ring

end TerminalGeometry

end PureWZ2DirectCommonYSourceAssembly

end Kakeya.Assouad

end
