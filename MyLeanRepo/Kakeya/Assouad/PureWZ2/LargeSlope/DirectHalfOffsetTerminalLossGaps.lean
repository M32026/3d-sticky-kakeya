import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.FinalQuotientLossSchedule

/-!
# Loss gaps for the direct half-offset terminal

These are the numerical gaps needed by the fixed-lambda terminal route.
They are consequences of the pre-runtime final quotient loss schedule, except
that the volume gap necessarily records the sign condition on `sigma`: the
schedule itself does not constrain `sigma`.
-/

noncomputable section

namespace Kakeya.Assouad

namespace PureWZ2FinalQuotientLossSchedule

private theorem epsilon_eq_nearby_div_thousand
    {sigma outputLoss : ℝ}
    (schedule : PureWZ2FinalQuotientLossSchedule sigma outputLoss) :
    schedule.epsilon = schedule.nearbyLoss / 1000 := by
  rw [schedule.epsilon_eq, schedule.nearbyLoss_eq]
  rfl

private theorem nearby_le_output_div_sixteen
    {sigma outputLoss : ℝ}
    (schedule : PureWZ2FinalQuotientLossSchedule sigma outputLoss) :
    schedule.nearbyLoss ≤ outputLoss / 16 := by
  rw [schedule.nearbyLoss_eq]
  exact min_le_left _ _

/-- The actual direct-half-offset CWA ledger spends at most `136 * epsilon`. -/
theorem directHalfOffsetTerminal_cwa_gap
    {sigma outputLoss : ℝ}
    (schedule : PureWZ2FinalQuotientLossSchedule sigma outputLoss) :
    136 * schedule.epsilon <
      (1 - 2 * schedule.epsilon) * schedule.nearbyLoss := by
  rw [epsilon_eq_nearby_div_thousand schedule]
  nlinarith [schedule.nearby_loss_pos, schedule.nearby_loss_le_one]

/-- The fixed-lambda density transport has two geometric powers and
`34 * epsilon` of scalar loss. -/
theorem directHalfOffsetTerminal_density_gap
    {sigma outputLoss : ℝ}
    (schedule : PureWZ2FinalQuotientLossSchedule sigma outputLoss) :
    2 + 34 * schedule.epsilon <
      (1 - 2 * schedule.epsilon) * (outputLoss + 2) := by
  rw [epsilon_eq_nearby_div_thousand schedule]
  nlinarith [schedule.nearby_loss_pos, schedule.nearby_loss_le_one,
    nearby_le_output_div_sixteen schedule]

/-- Taking the global internal loss to be `nearbyLoss` leaves the required
eight-epsilon source-to-terminal gap. -/
theorem directHalfOffsetTerminal_global_gap
    {sigma outputLoss : ℝ}
    (schedule : PureWZ2FinalQuotientLossSchedule sigma outputLoss) :
    8 * schedule.epsilon <
      (1 - 2 * schedule.epsilon) * schedule.nearbyLoss := by
  rw [epsilon_eq_nearby_div_thousand schedule]
  nlinarith [schedule.nearby_loss_pos, schedule.nearby_loss_le_one]

/-- The local fixed-lambda loss spends four epsilon powers. -/
theorem directHalfOffsetTerminal_local_gap
    {sigma outputLoss : ℝ}
    (schedule : PureWZ2FinalQuotientLossSchedule sigma outputLoss) :
    4 * schedule.epsilon <
      (1 - 2 * schedule.epsilon) * outputLoss := by
  rw [epsilon_eq_nearby_div_thousand schedule]
  nlinarith [schedule.nearby_loss_pos, schedule.nearby_loss_le_one,
    nearby_le_output_div_sixteen schedule]

/-- The volume gap follows once `sigma` has its intended nonnegative sign.
This hypothesis cannot be removed from this lemma: the loss schedule records
only `sigma ^ 2`, so negative `sigma` remains compatible with its fields. -/
theorem directHalfOffsetTerminal_volume_gap
    {sigma outputLoss : ℝ}
    (schedule : PureWZ2FinalQuotientLossSchedule sigma outputLoss)
    (hsigma : 0 ≤ sigma) :
    2 * schedule.epsilon * (1 - sigma) <
      (1 - 2 * schedule.epsilon) *
        (outputLoss - schedule.nearbyLoss) := by
  rw [epsilon_eq_nearby_div_thousand schedule]
  nlinarith [schedule.top_level_gap, schedule.nearby_loss_pos,
    schedule.nearby_loss_le_one, nearby_le_output_div_sixteen schedule]

/-- Re-export the schedule's strict top-level loss separation under the
direct-half-offset naming used by terminal callers. -/
theorem directHalfOffsetTerminal_top_level_gap
    {sigma outputLoss : ℝ}
    (schedule : PureWZ2FinalQuotientLossSchedule sigma outputLoss) :
    0 < outputLoss - 3 * schedule.nearbyLoss :=
  schedule.top_level_gap

end PureWZ2FinalQuotientLossSchedule

end Kakeya.Assouad
