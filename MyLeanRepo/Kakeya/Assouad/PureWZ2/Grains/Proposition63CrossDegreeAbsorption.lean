import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62V4PureScalarInputs

/-!
# The scalar absorption behind Proposition 6.3, Lemma 4.4

The four-degree construction loses two copies of its terminal regularity
factor when its fine-cell degree is compared with the coarse point
multiplicity.  This file absorbs those two polylogarithmic factors together
with the sixty-one-log refinement loss.  The remaining positive power is

`outputLoss ^ 2 - 2 * sourceLoss - capLoss`.

All choices are made before the runtime scales and families.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open Kakeya.Assouad Prop62PaperAudit.V4

theorem proposition63_logarithmicLoss_le_two_logEnvelope
    {delta : ℝ}
    (deltaPos : 0 < delta)
    (deltaLeOne : delta ≤ 1) :
    (pureWZ2Prop62DirectionLevelCount delta : ENNReal) ≤
      2 * ENNReal.ofReal (1 + Real.log delta⁻¹) := by
  have logNonneg : 0 ≤ Real.log delta⁻¹ :=
    Real.log_nonneg ((one_le_inv₀ deltaPos).mpr deltaLeOne)
  have quotientNonneg :
      0 ≤ Real.log delta⁻¹ / Real.log 2 := by
    positivity
  have floorLe :
      (Nat.floor (Real.log delta⁻¹ / Real.log 2) : ℝ) ≤
        Real.log delta⁻¹ / Real.log 2 :=
    Nat.floor_le quotientNonneg
  have logTwoHalf : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have bound :
        Real.log (1 / 2 : ℝ) ≤ (1 / 2 : ℝ) - 1 :=
      Real.log_le_sub_one_of_pos (by norm_num)
    have rewrite :
        Real.log (1 / 2 : ℝ) = -Real.log 2 := by
      rw [Real.log_div (by norm_num) (by norm_num)]
      simp
    rw [rewrite] at bound
    linarith
  have quotientLe :
      Real.log delta⁻¹ / Real.log 2 ≤
        2 * Real.log delta⁻¹ := by
    rw [div_le_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))]
    nlinarith
  have realBound :
      (pureWZ2Prop62DirectionLevelCount delta : ℝ) ≤
        2 * (1 + Real.log delta⁻¹) := by
    change
      ((Nat.floor (Real.log (1 / delta) / Real.log 2) + 1 : ℕ) : ℝ) ≤
        2 * (1 + Real.log delta⁻¹)
    rw [show 1 / delta = delta⁻¹ by simp]
    norm_num only [Nat.cast_add, Nat.cast_one]
    linarith
  have converted := ENNReal.ofReal_mono realBound
  rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)] at converted
  norm_num at converted ⊢
  simpa using converted

/-- A uniform scalar receipt for the cellwise cross-degree comparison. -/
structure Proposition63CrossDegreeAbsorptionData
    (sourceLoss capLoss outputLoss : ℝ) where
  delta₀ : ℝ
  delta₀_pos : 0 < delta₀
  delta₀_le_one : delta₀ ≤ 1
  delta₀_lt_one : delta₀ < 1
  absorb :
    ∀ {delta rho : ℝ},
      0 < delta → delta ≤ delta₀ →
      0 < rho → rho ≤ Real.rpow delta outputLoss →
      ∀ {regularity : ℕ},
        (regularity : ENNReal) ≤ logarithmicLoss delta ^ 10 →
        Kakeya.realRpowENN rho outputLoss *
              ((regularity : ENNReal) ^ 2 * 2) ≤
          wz2PaperPureRefinementFraction delta 61 *
            Kakeya.realRpowENN delta (2 * sourceLoss + capLoss)

/-- Choose the cross-degree threshold from its strict power gap. -/
theorem proposition63_cross_degree_absorption
    (sourceLoss capLoss outputLoss : ℝ)
    (outputLossPos : 0 < outputLoss)
    (gap : 0 < outputLoss ^ 2 - 2 * sourceLoss - capLoss) :
    Nonempty
      (Proposition63CrossDegreeAbsorptionData
        sourceLoss capLoss outputLoss) := by
  let exponentGap : ℝ :=
    outputLoss ^ 2 - 2 * sourceLoss - capLoss
  have exponentGapPos : 0 < exponentGap := by
    simpa [exponentGap] using gap
  rcases
      exists_delta_C_pow_log_absorbed_ennreal
        (2 : ENNReal) (by norm_num)
        2 (by norm_num) exponentGapPos
        (show 0 < (81 : ℕ) by norm_num)
    with
    ⟨logDelta, logDeltaPos, logDeltaLeOne, logarithmicAbsorption⟩
  let delta₀ : ℝ := min logDelta (Real.exp (-1))
  have delta₀Pos : 0 < delta₀ := by
    exact lt_min logDeltaPos (Real.exp_pos _)
  have delta₀LeOne : delta₀ ≤ 1 := by
    exact (min_le_left _ _).trans logDeltaLeOne
  refine
    ⟨{
      delta₀ := delta₀
      delta₀_pos := delta₀Pos
      delta₀_le_one := delta₀LeOne
      delta₀_lt_one :=
        (min_le_right logDelta (Real.exp (-1))).trans_lt
          (Real.exp_lt_one_iff.mpr (by norm_num))
      absorb := ?_
    }⟩
  intro delta rho deltaPos deltaLe rhoPos rhoUpper regularity regularityLe
  have deltaLeOne : delta ≤ 1 := deltaLe.trans delta₀LeOne
  let envelope : ENNReal :=
    ENNReal.ofReal (2 * (1 + Real.log delta⁻¹))
  have logarithmicLe : logarithmicLoss delta ≤ envelope := by
    have bound := proposition63_logarithmicLoss_le_two_logEnvelope
      deltaPos deltaLeOne
    change
      (pureWZ2Prop62DirectionLevelCount delta : ENNReal) ≤
        ENNReal.ofReal (2 * (1 + Real.log delta⁻¹))
    calc
      (pureWZ2Prop62DirectionLevelCount delta : ENNReal) ≤
          2 * ENNReal.ofReal (1 + Real.log delta⁻¹) := bound
      _ = ENNReal.ofReal (2 * (1 + Real.log delta⁻¹)) := by
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
        norm_num
  have logNonnegative : 0 ≤ Real.log delta⁻¹ :=
    Real.log_nonneg ((one_le_inv₀ deltaPos).mpr deltaLeOne)
  let logTerm : ENNReal :=
    ENNReal.ofReal (Real.log (1 / delta))
  have logTermLe : logTerm ≤ envelope := by
    dsimp only [logTerm, envelope]
    apply ENNReal.ofReal_mono
    rw [show 1 / delta = delta⁻¹ by simp]
    linarith
  have regularitySquare :
      (regularity : ENNReal) ^ 2 ≤ envelope ^ 20 := by
    calc
      (regularity : ENNReal) ^ 2 ≤
          (logarithmicLoss delta ^ 10) ^ 2 := by gcongr
      _ = logarithmicLoss delta ^ 20 := by ring
      _ ≤ envelope ^ 20 := by gcongr
  have combinedLog :
      ((regularity : ENNReal) ^ 2 * 2) * logTerm ^ 61 ≤
        2 * envelope ^ 81 := by
    calc
      ((regularity : ENNReal) ^ 2 * 2) * logTerm ^ 61 ≤
          (envelope ^ 20 * 2) * envelope ^ 61 := by gcongr
      _ = 2 * envelope ^ 81 := by ring
  have envelopeAbsorption :
      2 * envelope ^ 81 ≤
        Kakeya.realRpowENN delta (-exponentGap) := by
    simpa [envelope] using
      logarithmicAbsorption delta deltaPos
        (deltaLe.trans (min_le_left _ _))
  have powerProduct :
      Kakeya.realRpowENN delta exponentGap *
          (((regularity : ENNReal) ^ 2 * 2) * logTerm ^ 61) ≤ 1 := by
    calc
      Kakeya.realRpowENN delta exponentGap *
            (((regularity : ENNReal) ^ 2 * 2) * logTerm ^ 61) ≤
          Kakeya.realRpowENN delta exponentGap *
            Kakeya.realRpowENN delta (-exponentGap) := by
        gcongr
        exact combinedLog.trans envelopeAbsorption
      _ = 1 := by
        rw [← realRpowENN_add deltaPos]
        simp [Kakeya.realRpowENN]
  have rhoPower :
      Kakeya.realRpowENN rho outputLoss ≤
        Kakeya.realRpowENN delta (outputLoss ^ 2) := by
    have monotone := ENNReal.ofReal_mono <|
      Real.rpow_le_rpow rhoPos.le rhoUpper outputLossPos.le
    calc
      Kakeya.realRpowENN rho outputLoss ≤
          ENNReal.ofReal (Real.rpow delta outputLoss ^ outputLoss) := by
        simpa [Kakeya.realRpowENN] using monotone
      _ = Kakeya.realRpowENN delta (outputLoss ^ 2) := by
        apply congrArg ENNReal.ofReal
        rw [show outputLoss ^ 2 = outputLoss * outputLoss by ring]
        exact (Real.rpow_mul deltaPos.le outputLoss outputLoss).symm
  have multiplied :
      (Kakeya.realRpowENN rho outputLoss *
          ((regularity : ENNReal) ^ 2 * 2)) * logTerm ^ 61 ≤
        Kakeya.realRpowENN delta (2 * sourceLoss + capLoss) := by
    calc
    (Kakeya.realRpowENN rho outputLoss *
          ((regularity : ENNReal) ^ 2 * 2)) * logTerm ^ 61 ≤
        (Kakeya.realRpowENN delta (outputLoss ^ 2) *
          ((regularity : ENNReal) ^ 2 * 2)) * logTerm ^ 61 := by
      gcongr
    _ =
        Kakeya.realRpowENN delta (2 * sourceLoss + capLoss) *
          (Kakeya.realRpowENN delta exponentGap *
            (((regularity : ENNReal) ^ 2 * 2) * logTerm ^ 61)) := by
      have powerSplit :
          Kakeya.realRpowENN delta (outputLoss ^ 2) =
            Kakeya.realRpowENN delta (2 * sourceLoss + capLoss) *
              Kakeya.realRpowENN delta exponentGap := by
        rw [← realRpowENN_add deltaPos]
        congr 1
        dsimp only [exponentGap]
        ring
      rw [powerSplit]
      ring
    _ ≤ Kakeya.realRpowENN delta (2 * sourceLoss + capLoss) * 1 := by
      gcongr
    _ = Kakeya.realRpowENN delta (2 * sourceLoss + capLoss) := by simp
  rw [wz2PaperPureRefinementFraction, ← ENNReal.inv_pow]
  have deltaLtOne : delta < 1 := by
    exact deltaLe.trans_lt <|
      (min_le_right _ _).trans_lt
        (Real.exp_lt_one_iff.mpr (by norm_num))
  have logTermPos : 0 < logTerm := by
    apply ENNReal.ofReal_pos.mpr
    exact Real.log_pos (one_lt_one_div deltaPos deltaLtOne)
  have logTermTop : logTerm ≠ ⊤ := by simp [logTerm]
  have logPowerPos : 0 < logTerm ^ 61 := by positivity
  have logPowerTop : logTerm ^ 61 ≠ ⊤ :=
    ENNReal.pow_ne_top logTermTop
  rw [← ENNReal.div_eq_inv_mul]
  apply
    (ENNReal.le_div_iff_mul_le
      (Or.inl logPowerPos.ne') (Or.inl logPowerTop)).mpr
  simpa [mul_comm, mul_left_comm, mul_assoc] using multiplied

/--
The finite mass/cardinality cancellation used by the rich Node 3 producer.
It is kept separate from the asymptotic receipt above: this lemma only
rearranges the exact terminal ledger.
-/
theorem proposition63_cross_degree_of_mass_ledger
    {delta rho sigma sourceLoss capLoss outputLoss : ℝ}
    (deltaPos : 0 < delta)
    (rhoPos : 0 < rho)
    (refinementLoss regularity fineDegree muFine muCoarse fiberFloor
      fineCard coarseCard fineMass fineVolume : ENNReal)
    (refinementLossPos : 0 < refinementLoss)
    (refinementLossTop : refinementLoss ≠ ⊤)
    (fiberFloorPos : 0 < fiberFloor)
    (fiberFloorTop : fiberFloor ≠ ⊤)
    (massLower :
      refinementLoss * Kakeya.realRpowENN delta sourceLoss *
            fineCard * Kakeya.realRpowENN delta 2 ≤
        fineMass)
    (massUpper :
      fineMass ≤
        (regularity * fineDegree) * muFine * fineVolume)
    (volumeUpper :
      fineVolume ≤
        Kakeya.realRpowENN delta (sigma - sourceLoss))
    (fiberCardinality : fiberFloor * coarseCard ≤ fineCard)
    (fineCap :
      muFine ≤
        Kakeya.realRpowENN (delta / rho) (2 - sigma - capLoss) *
          (2 * fiberFloor))
    (coarseCap :
      muCoarse ≤
        Kakeya.realRpowENN rho (2 - sigma - capLoss) * coarseCard)
    (scalar :
      Kakeya.realRpowENN rho outputLoss *
            (regularity ^ 2 * 2) ≤
        refinementLoss *
          Kakeya.realRpowENN delta (2 * sourceLoss + capLoss)) :
    Kakeya.realRpowENN rho outputLoss *
          (regularity * muCoarse) ≤
      fineDegree := by
  have massComparison :
      refinementLoss * Kakeya.realRpowENN delta sourceLoss *
            (fiberFloor * coarseCard) * Kakeya.realRpowENN delta 2 ≤
        (regularity * fineDegree) *
          (Kakeya.realRpowENN (delta / rho)
              (2 - sigma - capLoss) * (2 * fiberFloor)) *
          Kakeya.realRpowENN delta (sigma - sourceLoss) := by
    calc
      refinementLoss * Kakeya.realRpowENN delta sourceLoss *
            (fiberFloor * coarseCard) * Kakeya.realRpowENN delta 2 ≤
          refinementLoss * Kakeya.realRpowENN delta sourceLoss *
            fineCard * Kakeya.realRpowENN delta 2 := by gcongr
      _ ≤ fineMass := massLower
      _ ≤ (regularity * fineDegree) * muFine * fineVolume := massUpper
      _ ≤
          (regularity * fineDegree) *
            (Kakeya.realRpowENN (delta / rho)
                (2 - sigma - capLoss) * (2 * fiberFloor)) *
            Kakeya.realRpowENN delta (sigma - sourceLoss) := by gcongr
  have cancelledFiber :
      refinementLoss * Kakeya.realRpowENN delta sourceLoss *
            coarseCard * Kakeya.realRpowENN delta 2 ≤
        (regularity * fineDegree) *
          (Kakeya.realRpowENN (delta / rho)
            (2 - sigma - capLoss) * 2) *
          Kakeya.realRpowENN delta (sigma - sourceLoss) := by
    apply
      (ENNReal.mul_le_mul_iff_right
        fiberFloorPos.ne' fiberFloorTop).mp
    simpa [mul_comm, mul_left_comm, mul_assoc] using massComparison
  let coefficient : ENNReal :=
    refinementLoss * Kakeya.realRpowENN delta sourceLoss *
      Kakeya.realRpowENN delta 2
  have coefficientPos : 0 < coefficient := by
    dsimp only [coefficient]
    rw [ENNReal.mul_pos_iff, ENNReal.mul_pos_iff]
    exact
      ⟨⟨refinementLossPos, ENNReal.ofReal_pos.mpr
        (Real.rpow_pos_of_pos deltaPos sourceLoss)⟩,
        ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos deltaPos 2)⟩
  have coefficientTop : coefficient ≠ ⊤ := by
    dsimp only [coefficient]
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top refinementLossTop
        (by simp [Kakeya.realRpowENN]))
      (by simp [Kakeya.realRpowENN])
  have cardinalityComparison :
      coefficient * coarseCard ≤
        (regularity * fineDegree) *
          (Kakeya.realRpowENN (delta / rho)
            (2 - sigma - capLoss) * 2) *
          Kakeya.realRpowENN delta (sigma - sourceLoss) := by
    simpa [coefficient, mul_comm, mul_left_comm, mul_assoc] using
      cancelledFiber
  apply
    (ENNReal.mul_le_mul_iff_right coefficientPos.ne' coefficientTop).mp
  calc
    coefficient *
          (Kakeya.realRpowENN rho outputLoss *
            (regularity * muCoarse)) ≤
        coefficient *
          (Kakeya.realRpowENN rho outputLoss *
            (regularity *
              (Kakeya.realRpowENN rho (2 - sigma - capLoss) *
                coarseCard))) := by gcongr
    _ =
        Kakeya.realRpowENN rho outputLoss * regularity *
          Kakeya.realRpowENN rho (2 - sigma - capLoss) *
          (coefficient * coarseCard) := by ring
    _ ≤
        Kakeya.realRpowENN rho outputLoss * regularity *
          Kakeya.realRpowENN rho (2 - sigma - capLoss) *
          ((regularity * fineDegree) *
            (Kakeya.realRpowENN (delta / rho)
              (2 - sigma - capLoss) * 2) *
            Kakeya.realRpowENN delta (sigma - sourceLoss)) := by
      gcongr
    _ =
        fineDegree *
          ((Kakeya.realRpowENN rho outputLoss *
              (regularity ^ 2 * 2)) *
            ((Kakeya.realRpowENN rho (2 - sigma - capLoss) *
                Kakeya.realRpowENN (delta / rho)
                  (2 - sigma - capLoss)) *
              Kakeya.realRpowENN delta (sigma - sourceLoss))) := by ring
    _ ≤
        fineDegree *
          ((refinementLoss *
              Kakeya.realRpowENN delta (2 * sourceLoss + capLoss)) *
            (Kakeya.realRpowENN delta (2 - sigma - capLoss) *
              Kakeya.realRpowENN delta (sigma - sourceLoss))) := by
      apply mul_le_mul_left'
      calc
        Kakeya.realRpowENN rho outputLoss * (regularity ^ 2 * 2) *
              (Kakeya.realRpowENN rho (2 - sigma - capLoss) *
                Kakeya.realRpowENN (delta / rho)
                  (2 - sigma - capLoss) *
                Kakeya.realRpowENN delta (sigma - sourceLoss)) =
            (Kakeya.realRpowENN rho outputLoss *
              (regularity ^ 2 * 2)) *
              ((Kakeya.realRpowENN rho (2 - sigma - capLoss) *
                Kakeya.realRpowENN (delta / rho)
                  (2 - sigma - capLoss)) *
                Kakeya.realRpowENN delta (sigma - sourceLoss)) := by ring
        _ ≤
            (refinementLoss *
              Kakeya.realRpowENN delta (2 * sourceLoss + capLoss)) *
              ((Kakeya.realRpowENN rho (2 - sigma - capLoss) *
                Kakeya.realRpowENN (delta / rho)
                  (2 - sigma - capLoss)) *
                Kakeya.realRpowENN delta (sigma - sourceLoss)) := by
          gcongr
        _ =
            (refinementLoss *
              Kakeya.realRpowENN delta (2 * sourceLoss + capLoss)) *
              (Kakeya.realRpowENN delta (2 - sigma - capLoss) *
                Kakeya.realRpowENN delta (sigma - sourceLoss)) := by
          rw [← realRpowENN_mul rhoPos (div_pos deltaPos rhoPos)]
          congr 1
          field_simp [rhoPos.ne']
    _ = coefficient * fineDegree := by
      dsimp only [coefficient]
      have exponentEq :
          2 * sourceLoss + capLoss +
              (2 - sigma - capLoss + (sigma - sourceLoss)) =
            sourceLoss + 2 := by ring
      have powersEq :
          Kakeya.realRpowENN delta (2 * sourceLoss + capLoss) *
                (Kakeya.realRpowENN delta (2 - sigma - capLoss) *
                  Kakeya.realRpowENN delta (sigma - sourceLoss)) =
            Kakeya.realRpowENN delta sourceLoss *
              Kakeya.realRpowENN delta 2 := by
        rw [← realRpowENN_add deltaPos]
        rw [← realRpowENN_add deltaPos]
        rw [exponentEq]
        exact realRpowENN_add deltaPos sourceLoss 2
      calc
        fineDegree *
              (refinementLoss *
                Kakeya.realRpowENN delta (2 * sourceLoss + capLoss) *
                (Kakeya.realRpowENN delta (2 - sigma - capLoss) *
                  Kakeya.realRpowENN delta (sigma - sourceLoss))) =
            fineDegree * (refinementLoss *
              (Kakeya.realRpowENN delta (2 * sourceLoss + capLoss) *
                (Kakeya.realRpowENN delta (2 - sigma - capLoss) *
                  Kakeya.realRpowENN delta (sigma - sourceLoss)))) := by ring
        _ = fineDegree * (refinementLoss *
              (Kakeya.realRpowENN delta sourceLoss *
                Kakeya.realRpowENN delta 2)) := by rw [powersEq]
        _ = refinementLoss * Kakeya.realRpowENN delta sourceLoss *
            Kakeya.realRpowENN delta 2 * fineDegree := by ring

end Kakeya.Assouad.PureWZ2

end
