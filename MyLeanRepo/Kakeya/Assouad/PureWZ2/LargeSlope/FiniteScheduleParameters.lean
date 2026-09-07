import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12
import MyLeanRepo.Kakeya.Assouad.AbsorptionHelpers

/-!
# Elementary parameters for finite nearby-scale schedules

The several simultaneous regularizations used in the final Node-6
construction all require the same two elementary facts: a finite constant
strictly larger than two has a sufficiently large natural power, and its
square is again an admissible finite error constant.
-/

noncomputable section

namespace Kakeya.Assouad

/-- A finite `ENNReal` strictly larger than two eventually dominates every
finite target by a natural power. -/
theorem exists_levelCount_for_finite_error_constant
    {C target : ENNReal} (hC : 2 < C) (hCtop : C ≠ ⊤)
    (htargetTop : target ≠ ⊤) :
    ∃ levelCount : ℕ, target ≤ C ^ levelCount := by
  have hCReal : 2 < C.toReal := by
    have htwoTop : (2 : ENNReal) ≠ ⊤ := by norm_num
    exact (ENNReal.toReal_lt_toReal htwoTop hCtop).2 hC
  obtain ⟨levelCount, hlevelCount⟩ :=
    pow_unbounded_of_one_lt target.toReal (by linarith : 1 < C.toReal)
  refine ⟨levelCount, ?_⟩
  rw [← ENNReal.ofReal_toReal htargetTop, ← ENNReal.ofReal_toReal hCtop,
    ← ENNReal.ofReal_pow (ENNReal.toReal_nonneg)]
  exact ENNReal.ofReal_mono hlevelCount.le

/-- The square of a finite constant larger than two is again a finite error
constant. -/
theorem finite_error_constant_sq
    {C : ENNReal} (hC : 2 < C) (hCtop : C ≠ ⊤) :
    WZ2PaperFiniteErrorConstant (C ^ 2) := by
  constructor
  · have hOne : (1 : ENNReal) ≤ C :=
      le_trans (by norm_num : (1 : ENNReal) ≤ 2) hC.le
    simpa using (one_le_pow₀ hOne : (1 : ENNReal) ≤ C ^ 2)
  · exact ENNReal.pow_ne_top hCtop

/--
The canonical finite schedule chosen from one ambient nearby-CWA constant.

This record packages only the finite combinatorial choice: the square of the
ambient constant pays for the restriction step, while a sufficiently large
natural power dominates the requested finite target.  It deliberately carries
no small-scale or power-absorption hypothesis.
-/
structure PureWZ2FiniteScheduleParameters
    (ambientConstant target : ENNReal) where
  scheduleConstant : ENNReal
  levelCount : ℕ
  scheduleConstant_eq : scheduleConstant = ambientConstant ^ 2
  schedule_finite : WZ2PaperFiniteErrorConstant scheduleConstant
  target_le_power : target ≤ ambientConstant ^ levelCount
  square_le_schedule :
    ambientConstant * ambientConstant ≤ scheduleConstant

/-- Every finite ambient constant strictly larger than two admits the canonical
finite schedule above for every finite target. -/
theorem exists_finite_schedule_parameters
    {ambientConstant target : ENNReal}
    (hambientTwo : 2 < ambientConstant)
    (hambientTop : ambientConstant ≠ ⊤)
    (htargetTop : target ≠ ⊤) :
    Nonempty (PureWZ2FiniteScheduleParameters ambientConstant target) := by
  rcases exists_levelCount_for_finite_error_constant
      hambientTwo hambientTop htargetTop with
    ⟨levelCount, hlevelCount⟩
  exact
    ⟨{ scheduleConstant := ambientConstant ^ 2
       levelCount := levelCount
       scheduleConstant_eq := rfl
       schedule_finite := finite_error_constant_sq hambientTwo hambientTop
       target_le_power := hlevelCount
       square_le_schedule := by simp [pow_two] }⟩

/-- The fixed schedule depth attached to a positive power loss.  It is chosen
before any runtime scale. -/
def pureWZ2FixedScheduleLevelCount (loss : ℝ) : ℕ :=
  Nat.ceil (1 / loss) + 1

theorem pureWZ2FixedScheduleLevelCount_mul_loss
    {loss : ℝ} (hloss : 0 < loss) :
    1 ≤ (pureWZ2FixedScheduleLevelCount loss : ℝ) * loss := by
  have hceil : (Nat.ceil (1 / loss) : ℝ) ≥ 1 / loss := Nat.le_ceil _
  have hlevel : (pureWZ2FixedScheduleLevelCount loss : ℝ) =
      (Nat.ceil (1 / loss) : ℝ) + 1 := by
    simp [pureWZ2FixedScheduleLevelCount]
  rw [hlevel]
  have hmul :
      (1 / loss + 1) * loss ≤
        ((Nat.ceil (1 / loss) : ℝ) + 1) * loss := by
    exact mul_le_mul_of_nonneg_right (by linarith) hloss.le
  have heq : (1 / loss + 1) * loss = 1 + loss := by
    field_simp [hloss.ne'] <;> ring
  linarith

/-- The fixed loss-dependent schedule reaches the inverse runtime scale. -/
theorem pureWZ2FixedScheduleLevelCount_covers_inv
    {delta loss : ℝ} (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (hloss : 0 < loss) :
    ENNReal.ofReal (1 / delta) ≤
      Kakeya.realRpowENN delta (-loss) ^
        pureWZ2FixedScheduleLevelCount loss := by
  let levelCount := pureWZ2FixedScheduleLevelCount loss
  have hlevelMul : 1 ≤ (levelCount : ℝ) * loss :=
    pureWZ2FixedScheduleLevelCount_mul_loss hloss
  have hreal : 1 / delta ≤
      Real.rpow delta (-(levelCount : ℝ) * loss) := by
    have hpower : Real.rpow delta (-1) ≤
        Real.rpow delta (-(levelCount : ℝ) * loss) :=
      Real.rpow_le_rpow_of_exponent_ge hdelta hdeltaOne (by linarith)
    have hone : Real.rpow delta (-1) = 1 / delta := by
      calc
        Real.rpow delta (-1) = (Real.rpow delta 1)⁻¹ :=
          Real.rpow_neg hdelta.le 1
        _ = delta⁻¹ := by simpa using congrArg Inv.inv (Real.rpow_one delta)
        _ = 1 / delta := by ring
    rwa [hone] at hpower
  have hpow :
      (ENNReal.ofReal (Real.rpow delta (-loss))) ^ levelCount =
        ENNReal.ofReal (Real.rpow delta (-(levelCount : ℝ) * loss)) := by
    have hnonneg : 0 ≤ Real.rpow delta (-loss) :=
      Real.rpow_nonneg hdelta.le _
    rw [← ENNReal.ofReal_pow hnonneg]
    rw [rpow_nat_pow hdelta (-loss) levelCount]
    congr 2
    ring
  change ENNReal.ofReal (1 / delta) ≤
    (ENNReal.ofReal (Real.rpow delta (-loss))) ^ levelCount
  rw [hpow]
  exact ENNReal.ofReal_mono hreal

/-- The canonical fixed loss-dependent schedule for any finite ambient
constant which dominates `delta^{-loss}`. -/
noncomputable def fixedFiniteScheduleParameters
    {delta loss : ℝ} {ambientConstant : ENNReal}
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (hloss : 0 < loss)
    (hambientLower :
      Kakeya.realRpowENN delta (-loss) ≤ ambientConstant)
    (hambientTwo : (2 : ENNReal) < ambientConstant)
    (hambientTop : ambientConstant ≠ ⊤) :
    PureWZ2FiniteScheduleParameters ambientConstant
      (ENNReal.ofReal (1 / delta)) := by
  let levelCount := pureWZ2FixedScheduleLevelCount loss
  have hbase := pureWZ2FixedScheduleLevelCount_covers_inv
    hdelta hdeltaOne hloss
  have hlevels : ENNReal.ofReal (1 / delta) ≤
      ambientConstant ^ levelCount :=
    hbase.trans (pow_le_pow_left' hambientLower levelCount)
  exact
    { scheduleConstant := ambientConstant ^ 2
      levelCount := levelCount
      scheduleConstant_eq := rfl
      schedule_finite := finite_error_constant_sq hambientTwo hambientTop
      target_le_power := hlevels
      square_le_schedule := by simp [pow_two] }

@[simp] theorem fixedFiniteScheduleParameters_levelCount
    {delta loss : ℝ} {ambientConstant : ENNReal}
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (hloss : 0 < loss)
    (hambientLower :
      Kakeya.realRpowENN delta (-loss) ≤ ambientConstant)
    (hambientTwo : (2 : ENNReal) < ambientConstant)
    (hambientTop : ambientConstant ≠ ⊤) :
    (fixedFiniteScheduleParameters hdelta hdeltaOne hloss hambientLower
      hambientTwo hambientTop).levelCount =
        pureWZ2FixedScheduleLevelCount loss := rfl

/-- A single finite target constant dominating one scale-window cost and every
member of a finite family of coordinate costs. -/
structure PureWZ2FiniteBudgetEnvelope
    {count : ℕ} (scaleBudget : ENNReal)
    (coordinateBudget : Fin count → ENNReal) where
  targetConstant : ENNReal
  target_finite : WZ2PaperFiniteErrorConstant targetConstant
  scale_le : scaleBudget ≤ targetConstant
  coordinate_le : ∀ coordinate, coordinateBudget coordinate ≤ targetConstant

/-- Take the maximum of one and the sum of all finite costs. -/
theorem exists_finite_budget_envelope
    {count : ℕ} {scaleBudget : ENNReal}
    {coordinateBudget : Fin count → ENNReal}
    (hscaleTop : scaleBudget ≠ ⊤)
    (hcoordinateTop : ∀ coordinate, coordinateBudget coordinate ≠ ⊤) :
    Nonempty (PureWZ2FiniteBudgetEnvelope scaleBudget coordinateBudget) := by
  let total := ∑ coordinate, coordinateBudget coordinate
  let targetConstant := max 1 (max scaleBudget total)
  have htotalTop : total ≠ ⊤ := by
    apply ENNReal.sum_ne_top.mpr
    intro coordinate _
    exact hcoordinateTop coordinate
  have htargetTop : targetConstant ≠ ⊤ := by
    dsimp only [targetConstant]
    exact max_ne_top (by norm_num) (max_ne_top hscaleTop htotalTop)
  have hone : (1 : ENNReal) ≤ targetConstant := by
    exact le_max_left _ _
  have hscale : scaleBudget ≤ targetConstant := by
    exact (le_max_left scaleBudget total).trans (le_max_right _ _)
  have hcoordinate : ∀ coordinate,
      coordinateBudget coordinate ≤ targetConstant := by
    intro coordinate
    have hsum : coordinateBudget coordinate ≤ total := by
      exact Finset.single_le_sum (fun _ _ => bot_le) (Finset.mem_univ coordinate)
    exact hsum.trans <|
      (le_max_right scaleBudget total).trans (le_max_right _ _)
  exact ⟨{ targetConstant := targetConstant
           target_finite := ⟨hone, htargetTop⟩
           scale_le := hscale
           coordinate_le := hcoordinate }⟩

end Kakeya.Assouad

end
