import MyLeanRepo.Kakeya.Assouad.EssentiallyDistinctCardBound

/-!
# Log-cardinality bound in a fixed support ball

The six-parameter packing estimate gives a polynomial bound for an
essentially-distinct family supported in `B(0,R)`.  Taking logarithms yields
the fixed-coefficient estimate needed to absorb every finite simultaneous
selection loss.
-/

noncomputable section

namespace Kakeya.Assouad

/-- Fixed coefficient in the support-ball logarithmic cardinality bound. -/
def pureWZ2FixedBallCardLogConstant (R : ℝ) : ℝ :=
  max
    (Real.log (2 * (37 * R) ^ 6) / Real.log 2 + 1)
    (6 / Real.log 2)

/--
For an essentially-distinct nonempty family supported in `B(0,R)`,
`log₂(2 card) + 1` is bounded by a fixed multiple of
`1 + log(delta⁻¹)`.
-/
theorem pureWZ2_fixed_ball_card_log_bound
    {delta R : ℝ}
    (hdelta : 0 < delta)
    (hdeltaOne : delta ≤ 1)
    (hdeltaSmall : delta < 1 / 16)
    (hR : 1 ≤ R)
    {family : Kakeya.Streamlined.TubeFamily delta}
    (familyNonempty : family.Nonempty)
    (familySupport :
      ∀ index,
        (family.tube index).carrier ⊆
          Metric.closedBall (0 : Point3) R)
    (familyDistinct : family.IsEssentiallyDistinct) :
    (Nat.log 2 (2 * family.card) + 1 : ℝ) ≤
      pureWZ2FixedBallCardLogConstant R *
        (1 + Real.log delta⁻¹) := by
  have hlogTwo : 0 < Real.log 2 :=
    Real.log_pos (by norm_num)
  have hcard :=
    essentially_distinct_card_bound_fixed_ball
      hdelta hdeltaOne hdeltaSmall hR
      familySupport familyDistinct
  have hfamilyCardPos : 0 < family.card := familyNonempty
  have hdoubleCardPos : 0 < 2 * family.card := by
    positivity
  have hdoubleCardRealPos :
      (0 : ℝ) < (2 * family.card : ℕ) := by
    exact_mod_cast hdoubleCardPos
  have hKPos : 0 < 2 * (37 * R : ℝ) ^ 6 := by
    positivity
  have hdeltaPowerPos :
      0 < delta ^ (-6 : ℝ) := by
    positivity
  have hdoubleCardBound :
      ((2 * family.card : ℕ) : ℝ) ≤
        (2 * (37 * R : ℝ) ^ 6) *
          delta ^ (-6 : ℝ) := by
    have hscaled :
        2 * (family.card : ℝ) ≤
          2 * ((37 * R : ℝ) ^ 6 *
            delta ^ (-6 : ℝ)) := by
      gcongr
    simpa [mul_assoc] using hscaled
  have hnatLog :
      (Nat.log 2 (2 * family.card) : ℝ) ≤
        Real.log ((2 * family.card : ℕ) : ℝ) /
          Real.log 2 := by
    have hpow :
        (2 : ℕ) ^ Nat.log 2 (2 * family.card) ≤
          2 * family.card :=
      Nat.pow_log_le_self 2 hdoubleCardPos.ne'
    have hpowReal :
        (2 : ℝ) ^ Nat.log 2 (2 * family.card) ≤
          ((2 * family.card : ℕ) : ℝ) := by
      exact_mod_cast hpow
    have hlog :=
      Real.log_le_log (by positivity) hpowReal
    rw [Real.log_pow] at hlog
    exact (le_div_iff₀ hlogTwo).mpr (by simpa using hlog)
  have hlogCard :
      Real.log ((2 * family.card : ℕ) : ℝ) ≤
        Real.log
          ((2 * (37 * R : ℝ) ^ 6) *
            delta ^ (-6 : ℝ)) :=
    Real.log_le_log hdoubleCardRealPos hdoubleCardBound
  have hlogProduct :
      Real.log
          ((2 * (37 * R : ℝ) ^ 6) *
            delta ^ (-6 : ℝ)) =
        Real.log (2 * (37 * R : ℝ) ^ 6) +
          6 * Real.log delta⁻¹ := by
    rw [Real.log_mul hKPos.ne' hdeltaPowerPos.ne',
      Real.log_rpow hdelta (-6 : ℝ),
      Real.log_inv]
    ring
  have hraw :
      (Nat.log 2 (2 * family.card) + 1 : ℝ) ≤
        (Real.log (2 * (37 * R : ℝ) ^ 6) /
            Real.log 2 + 1) +
          (6 / Real.log 2) * Real.log delta⁻¹ := by
    calc
      (Nat.log 2 (2 * family.card) + 1 : ℝ) ≤
          Real.log ((2 * family.card : ℕ) : ℝ) /
              Real.log 2 + 1 := by
        linarith
      _ ≤
          Real.log
              ((2 * (37 * R : ℝ) ^ 6) *
                delta ^ (-6 : ℝ)) /
              Real.log 2 + 1 := by
        gcongr
      _ =
          (Real.log (2 * (37 * R : ℝ) ^ 6) /
              Real.log 2 + 1) +
            (6 / Real.log 2) * Real.log delta⁻¹ := by
        rw [hlogProduct]
        field_simp [hlogTwo.ne']
        ring
  have hlogNonnegative : 0 ≤ Real.log delta⁻¹ := by
    apply Real.log_nonneg
    calc
      (1 : ℝ) = (1 : ℝ)⁻¹ := by norm_num
      _ ≤ delta⁻¹ := by gcongr
  let first :=
    Real.log (2 * (37 * R : ℝ) ^ 6) / Real.log 2 + 1
  let second := 6 / Real.log 2
  have hfirst :
      first ≤ pureWZ2FixedBallCardLogConstant R :=
    le_max_left _ _
  have hsecond :
      second ≤ pureWZ2FixedBallCardLogConstant R :=
    le_max_right _ _
  calc
    (Nat.log 2 (2 * family.card) + 1 : ℝ) ≤
        first + second * Real.log delta⁻¹ := by
      simpa [first, second] using hraw
    _ ≤
        pureWZ2FixedBallCardLogConstant R +
          pureWZ2FixedBallCardLogConstant R *
            Real.log delta⁻¹ := by
      gcongr
    _ =
        pureWZ2FixedBallCardLogConstant R *
          (1 + Real.log delta⁻¹) := by
      ring

end Kakeya.Assouad

end
