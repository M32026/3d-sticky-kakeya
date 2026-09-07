import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceHorizontalGoodBlockFamily

/-!
# Outer scale schedule for the source-horizontal one-scale argument

The local source-horizontal construction runs at an internal sticky scale
`targetScale / 1280`, while its trapezoids have the public scale
`targetScale`.  The fixed factor cannot be absorbed if the sticky loss and
the final one-scale loss are identified.  This module chooses the sticky
loss to be half the final loss and performs the two required fixed-constant
absorptions before any geometric data are constructed.
-/

noncomputable section

namespace Kakeya.Assouad

/-- Internal sticky scale producing trapezoids at `targetScale`. -/
def pureWZ2SourceHorizontalInternalScale (targetScale : ℝ) : ℝ :=
  targetScale / 1280

/-- Loss used only by the two nested sticky decompositions. -/
def pureWZ2SourceHorizontalStickyLoss (finalLoss : ℝ) : ℝ :=
  finalLoss / 2

/-- Exact arithmetic facts needed to call the nested sticky schedule at the
internal scale and return a one-scale output at the caller's scale. -/
structure PureWZ2SourceHorizontalOuterScaleData
    (delta targetScale finalLoss : ℝ) where
  internal_pos :
    0 < pureWZ2SourceHorizontalInternalScale targetScale
  delta_le_internal :
    delta ≤ pureWZ2SourceHorizontalInternalScale targetScale
  internal_le_one :
    pureWZ2SourceHorizontalInternalScale targetScale ≤ 1
  sticky_lower :
    Real.rpow delta
        (1 - pureWZ2SourceHorizontalStickyLoss finalLoss) ≤
      pureWZ2SourceHorizontalInternalScale targetScale
  sticky_upper :
    pureWZ2SourceHorizontalInternalScale targetScale ≤
      Real.rpow delta
        (pureWZ2SourceHorizontalStickyLoss finalLoss)
  final_scale_eq :
    pureWZ2SourceHorizontalFinalScale
        (pureWZ2SourceHorizontalInternalScale targetScale) =
      targetScale
  final_scale_le_one :
    pureWZ2SourceHorizontalFinalScale
        (pureWZ2SourceHorizontalInternalScale targetScale) ≤ 1
  graph_scale_le_one :
    256 * pureWZ2SourceHorizontalInternalScale targetScale ≤ 1
  certificate_scale_le_one :
    4 * pureWZ2SourceHorizontalInternalScale targetScale ≤ 1
  length_lower :
    Real.rpow targetScale (1 / 2 + finalLoss) ≤
      Real.sqrt (pureWZ2SourceHorizontalInternalScale targetScale)

private lemma sourceHorizontal_delta_le_internal
    {delta targetScale finalLoss : ℝ}
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (hfinal : 0 < finalLoss)
    (htargetLower : Real.rpow delta (1 - finalLoss) ≤ targetScale)
    (hscaleAbsorb : Real.rpow delta (finalLoss / 2) ≤ 1 / 1280) :
    delta ≤ pureWZ2SourceHorizontalInternalScale targetScale := by
  have hfinalHalf : finalLoss / 2 ≤ finalLoss := by linarith
  have hfinalPower :
      Real.rpow delta finalLoss ≤ Real.rpow delta (finalLoss / 2) :=
    Real.rpow_le_rpow_of_exponent_ge hdelta hdeltaOne hfinalHalf
  have hfactor : 1280 * Real.rpow delta finalLoss ≤ 1 := by
    nlinarith
  have hsplit :
      Real.rpow delta (1 - finalLoss) * Real.rpow delta finalLoss = delta := by
    have hadd := Real.rpow_add hdelta (1 - finalLoss) finalLoss
    rw [show (1 - finalLoss) + finalLoss = 1 by ring] at hadd
    simpa using hadd.symm
  unfold pureWZ2SourceHorizontalInternalScale
  rw [le_div_iff₀ (by norm_num)]
  calc
    delta * 1280 =
        (Real.rpow delta (1 - finalLoss) *
          Real.rpow delta finalLoss) * 1280 := by
      exact congrArg (fun value : ℝ => value * 1280) hsplit.symm
    _ =
        Real.rpow delta (1 - finalLoss) *
          (1280 * Real.rpow delta finalLoss) := by
      ring
    _ ≤ Real.rpow delta (1 - finalLoss) * 1 := by
      exact mul_le_mul_of_nonneg_left hfactor
        (Real.rpow_nonneg hdelta.le (1 - finalLoss))
    _ = Real.rpow delta (1 - finalLoss) := by ring
    _ ≤ targetScale := htargetLower

private lemma sourceHorizontal_sticky_lower
    {delta targetScale finalLoss : ℝ}
    (hdelta : 0 < delta)
    (htargetLower : Real.rpow delta (1 - finalLoss) ≤ targetScale)
    (hscaleAbsorb : Real.rpow delta (finalLoss / 2) ≤ 1 / 1280) :
    Real.rpow delta
        (1 - pureWZ2SourceHorizontalStickyLoss finalLoss) ≤
      pureWZ2SourceHorizontalInternalScale targetScale := by
  have hsplit :
      Real.rpow delta (1 - finalLoss) *
          Real.rpow delta (finalLoss / 2) =
        Real.rpow delta
          (1 - pureWZ2SourceHorizontalStickyLoss finalLoss) := by
    have hadd := Real.rpow_add hdelta
      (1 - finalLoss) (finalLoss / 2)
    rw [show (1 - finalLoss) + finalLoss / 2 =
        1 - pureWZ2SourceHorizontalStickyLoss finalLoss by
      simp [pureWZ2SourceHorizontalStickyLoss]
      ring] at hadd
    exact hadd.symm
  unfold pureWZ2SourceHorizontalInternalScale
  rw [le_div_iff₀ (by norm_num), ← hsplit]
  calc
    (Real.rpow delta (1 - finalLoss) *
          Real.rpow delta (finalLoss / 2)) * 1280 =
        Real.rpow delta (1 - finalLoss) *
          (1280 * Real.rpow delta (finalLoss / 2)) := by ring
    _ ≤ Real.rpow delta (1 - finalLoss) * 1 := by
      gcongr
      · exact Real.rpow_nonneg hdelta.le _
      · nlinarith
    _ = Real.rpow delta (1 - finalLoss) := by ring
    _ ≤ targetScale := htargetLower

private lemma sourceHorizontal_sticky_upper
    {delta targetScale finalLoss : ℝ}
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (hfinal : 0 < finalLoss) (htarget : 0 < targetScale)
    (htargetUpper : targetScale ≤ Real.rpow delta finalLoss) :
    pureWZ2SourceHorizontalInternalScale targetScale ≤
      Real.rpow delta
        (pureWZ2SourceHorizontalStickyLoss finalLoss) := by
  have hdivide : targetScale / 1280 ≤ targetScale := by
    exact div_le_self htarget.le (by norm_num)
  have hhalf : finalLoss / 2 ≤ finalLoss := by linarith
  exact hdivide.trans <| htargetUpper.trans <|
    Real.rpow_le_rpow_of_exponent_ge hdelta hdeltaOne hhalf

theorem pureWZ2_sourceHorizontal_length_lower
    {delta targetScale finalLoss : ℝ}
    (hdelta : 0 < delta)
    (hfinal : 0 < finalLoss) (htarget : 0 < targetScale)
    (htargetUpper : targetScale ≤ Real.rpow delta finalLoss)
    (hlengthAbsorb : Real.rpow delta (finalLoss ^ 2) ≤ 1 / 36) :
    Real.rpow targetScale (1 / 2 + finalLoss) ≤
      Real.sqrt (pureWZ2SourceHorizontalInternalScale targetScale) := by
  have htargetFinal :
      Real.rpow targetScale finalLoss ≤
        Real.rpow delta (finalLoss ^ 2) := by
    calc
      Real.rpow targetScale finalLoss ≤
          Real.rpow (Real.rpow delta finalLoss) finalLoss := by
        exact Real.rpow_le_rpow htarget.le htargetUpper hfinal.le
      _ = Real.rpow delta (finalLoss ^ 2) := by
        have hmul := Real.rpow_mul hdelta.le finalLoss finalLoss
        rw [show finalLoss * finalLoss = finalLoss ^ 2 by ring] at hmul
        exact hmul.symm
  have hfirst :
      Real.rpow targetScale (1 / 2 + finalLoss) ≤
        Real.sqrt targetScale / 36 := by
    have hadd := Real.rpow_add htarget (1 / 2) finalLoss
    change targetScale ^ (1 / 2 + finalLoss) ≤
      Real.sqrt targetScale / 36
    rw [hadd, ← Real.sqrt_eq_rpow]
    calc
      Real.sqrt targetScale * Real.rpow targetScale finalLoss ≤
          Real.sqrt targetScale * (1 / 36) := by
        exact mul_le_mul_of_nonneg_left
          (htargetFinal.trans hlengthAbsorb) (Real.sqrt_nonneg targetScale)
      _ = Real.sqrt targetScale / 36 := by ring
  have hsecond :
      Real.sqrt targetScale / 36 ≤
        Real.sqrt (targetScale / 1280) := by
    have hsqrtTarget : (Real.sqrt targetScale) ^ 2 = targetScale :=
      Real.sq_sqrt htarget.le
    have hinternal : 0 ≤ targetScale / 1280 := by positivity
    have hsqrtInternal :
        (Real.sqrt (targetScale / 1280)) ^ 2 = targetScale / 1280 :=
      Real.sq_sqrt hinternal
    have hleft : 0 ≤ Real.sqrt targetScale / 36 := by positivity
    have hright : 0 ≤ Real.sqrt (targetScale / 1280) :=
      Real.sqrt_nonneg _
    nlinarith [sq_nonneg
      (Real.sqrt (targetScale / 1280) - Real.sqrt targetScale / 36)]
  simpa [pureWZ2SourceHorizontalInternalScale] using hfirst.trans hsecond

/-- Uniform outer schedule.  The two smallness hypotheses are precisely the
fixed-factor losses caused by replacing the public scale with
`targetScale / 1280`. -/
theorem pureWZ2_sourceHorizontal_outerScale
    {delta targetScale finalLoss : ℝ}
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (hfinal : 0 < finalLoss)
    (htargetLower : Real.rpow delta (1 - finalLoss) ≤ targetScale)
    (htargetUpper : targetScale ≤ Real.rpow delta finalLoss)
    (hscaleAbsorb : Real.rpow delta (finalLoss / 2) ≤ 1 / 1280)
    (hlengthAbsorb : Real.rpow delta (finalLoss ^ 2) ≤ 1 / 36) :
    Nonempty
      (PureWZ2SourceHorizontalOuterScaleData
        delta targetScale finalLoss) := by
  have htarget : 0 < targetScale :=
    (Real.rpow_pos_of_pos hdelta _).trans_le htargetLower
  have htargetOne : targetScale ≤ 1 := by
    exact htargetUpper.trans
      (Real.rpow_le_one hdelta.le hdeltaOne hfinal.le)
  have hinternalPos :
      0 < pureWZ2SourceHorizontalInternalScale targetScale := by
    unfold pureWZ2SourceHorizontalInternalScale
    positivity
  have hfinalScale :
      pureWZ2SourceHorizontalFinalScale
          (pureWZ2SourceHorizontalInternalScale targetScale) =
        targetScale := by
    simp [pureWZ2SourceHorizontalFinalScale,
      pureWZ2SourceHorizontalInternalScale]
    ring
  refine ⟨{
    internal_pos := hinternalPos
    delta_le_internal := sourceHorizontal_delta_le_internal
      hdelta hdeltaOne hfinal htargetLower hscaleAbsorb
    internal_le_one := ?_
    sticky_lower := sourceHorizontal_sticky_lower
      hdelta htargetLower hscaleAbsorb
    sticky_upper := sourceHorizontal_sticky_upper
      hdelta hdeltaOne hfinal htarget htargetUpper
    final_scale_eq := hfinalScale
    final_scale_le_one := by simpa [hfinalScale] using htargetOne
    graph_scale_le_one := ?_
    certificate_scale_le_one := ?_
    length_lower := pureWZ2_sourceHorizontal_length_lower
      hdelta hfinal htarget htargetUpper hlengthAbsorb }⟩
  · unfold pureWZ2SourceHorizontalInternalScale
    calc
      targetScale / 1280 ≤ targetScale :=
        div_le_self htarget.le (by norm_num)
      _ ≤ 1 := htargetOne
  · unfold pureWZ2SourceHorizontalInternalScale
    calc
      256 * (targetScale / 1280) = targetScale / 5 := by ring
      _ ≤ targetScale := div_le_self htarget.le (by norm_num)
      _ ≤ 1 := htargetOne
  · unfold pureWZ2SourceHorizontalInternalScale
    calc
      4 * (targetScale / 1280) = targetScale / 320 := by ring
      _ ≤ targetScale := div_le_self htarget.le (by norm_num)
      _ ≤ 1 := htargetOne

/-- Choose one delta threshold that absorbs both fixed scale losses. -/
theorem pureWZ2_sourceHorizontal_outerScale_schedule
    {finalLoss : ℝ} (hfinal : 0 < finalLoss) :
    ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
        ∀ targetScale : ℝ,
          Real.rpow delta (1 - finalLoss) ≤ targetScale →
          targetScale ≤ Real.rpow delta finalLoss →
            Nonempty
              (PureWZ2SourceHorizontalOuterScaleData
                delta targetScale finalLoss) := by
  rcases exists_delta_rpow_le_single
      (finalLoss / 2) (1 / 1280)
      (by positivity) (by norm_num) (by norm_num) with
    ⟨scaleDelta₀, hscaleDelta₀, hscaleDelta₀One, hscale⟩
  rcases exists_delta_rpow_le_single
      (finalLoss ^ 2) (1 / 36)
      (sq_pos_of_pos hfinal) (by norm_num) (by norm_num) with
    ⟨lengthDelta₀, hlengthDelta₀, hlengthDelta₀One, hlength⟩
  let delta₀ := min scaleDelta₀ lengthDelta₀
  refine ⟨delta₀, by positivity,
    (min_le_left _ _).trans hscaleDelta₀One, ?_⟩
  intro delta hdelta hdeltaSmall targetScale htargetLower htargetUpper
  apply pureWZ2_sourceHorizontal_outerScale
    hdelta (hdeltaSmall.trans ((min_le_left _ _).trans hscaleDelta₀One))
    hfinal htargetLower htargetUpper
  · exact hscale delta hdelta
      (hdeltaSmall.trans (min_le_left _ _))
  · exact hlength delta hdelta
      (hdeltaSmall.trans (min_le_right _ _))

/-- Flexible variant used by Proposition 6.4, where the sticky loss is
chosen strictly below the final hierarchy loss. -/
structure PureWZ2SourceHorizontalFlexibleOuterScaleData
    (delta targetScale stickyLoss finalLoss : ℝ) where
  internal_pos :
    0 < pureWZ2SourceHorizontalInternalScale targetScale
  delta_le_internal :
    delta ≤ pureWZ2SourceHorizontalInternalScale targetScale
  internal_le_one :
    pureWZ2SourceHorizontalInternalScale targetScale ≤ 1
  sticky_lower :
    Real.rpow delta (1 - stickyLoss) ≤
      pureWZ2SourceHorizontalInternalScale targetScale
  sticky_upper :
    pureWZ2SourceHorizontalInternalScale targetScale ≤
      Real.rpow delta stickyLoss
  final_scale_eq :
    pureWZ2SourceHorizontalFinalScale
        (pureWZ2SourceHorizontalInternalScale targetScale) =
      targetScale
  final_scale_le_one :
    pureWZ2SourceHorizontalFinalScale
        (pureWZ2SourceHorizontalInternalScale targetScale) ≤ 1
  graph_scale_le_one :
    256 * pureWZ2SourceHorizontalInternalScale targetScale ≤ 1
  certificate_scale_le_one :
    4 * pureWZ2SourceHorizontalInternalScale targetScale ≤ 1
  length_lower :
    Real.rpow targetScale (1 / 2 + finalLoss) ≤
      Real.sqrt (pureWZ2SourceHorizontalInternalScale targetScale)

/-- Absorb the fixed factor 1280 using the genuine gap between the final
and sticky losses. -/
theorem pureWZ2_sourceHorizontal_outerScale_flexible
    {delta targetScale stickyLoss finalLoss : ℝ}
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (hsticky : 0 < stickyLoss) (hstickyFinal : stickyLoss < finalLoss)
    (htargetLower : Real.rpow delta (1 - finalLoss) ≤ targetScale)
    (htargetUpper : targetScale ≤ Real.rpow delta finalLoss)
    (hscaleAbsorb :
      Real.rpow delta (finalLoss - stickyLoss) ≤ 1 / 1280)
    (hlengthAbsorb : Real.rpow delta (finalLoss ^ 2) ≤ 1 / 36) :
    Nonempty
      (PureWZ2SourceHorizontalFlexibleOuterScaleData
        delta targetScale stickyLoss finalLoss) := by
  have hfinal : 0 < finalLoss := hsticky.trans hstickyFinal
  have htarget : 0 < targetScale :=
    (Real.rpow_pos_of_pos hdelta _).trans_le htargetLower
  have htargetOne : targetScale ≤ 1 :=
    htargetUpper.trans
      (Real.rpow_le_one hdelta.le hdeltaOne hfinal.le)
  have hinternalPos :
      0 < pureWZ2SourceHorizontalInternalScale targetScale := by
    unfold pureWZ2SourceHorizontalInternalScale
    positivity
  have hdeltaInternal :
      delta ≤ pureWZ2SourceHorizontalInternalScale targetScale := by
    have hfinalPower :
        Real.rpow delta finalLoss ≤
          Real.rpow delta (finalLoss - stickyLoss) :=
      Real.rpow_le_rpow_of_exponent_ge hdelta hdeltaOne (by linarith)
    have hfactor : 1280 * Real.rpow delta finalLoss ≤ 1 := by
      nlinarith [hfinalPower.trans hscaleAbsorb]
    have hsplit :
        Real.rpow delta (1 - finalLoss) *
            Real.rpow delta finalLoss = delta := by
      have hadd := Real.rpow_add hdelta (1 - finalLoss) finalLoss
      rw [show (1 - finalLoss) + finalLoss = 1 by ring] at hadd
      simpa using hadd.symm
    unfold pureWZ2SourceHorizontalInternalScale
    rw [le_div_iff₀ (by norm_num)]
    calc
      delta * 1280 =
          (Real.rpow delta (1 - finalLoss) *
            Real.rpow delta finalLoss) * 1280 := by
        exact congrArg (fun value : ℝ => value * 1280) hsplit.symm
      _ = Real.rpow delta (1 - finalLoss) *
            (1280 * Real.rpow delta finalLoss) := by ring
      _ ≤ Real.rpow delta (1 - finalLoss) * 1 := by
        exact mul_le_mul_of_nonneg_left hfactor
          (Real.rpow_nonneg hdelta.le _)
      _ = Real.rpow delta (1 - finalLoss) := by ring
      _ ≤ targetScale := htargetLower
  have hstickyLower :
      Real.rpow delta (1 - stickyLoss) ≤
        pureWZ2SourceHorizontalInternalScale targetScale := by
    have hsplit :
        Real.rpow delta (1 - finalLoss) *
            Real.rpow delta (finalLoss - stickyLoss) =
          Real.rpow delta (1 - stickyLoss) := by
      have hadd := Real.rpow_add hdelta
        (1 - finalLoss) (finalLoss - stickyLoss)
      rw [show (1 - finalLoss) + (finalLoss - stickyLoss) =
          1 - stickyLoss by ring] at hadd
      exact hadd.symm
    unfold pureWZ2SourceHorizontalInternalScale
    rw [le_div_iff₀ (by norm_num), ← hsplit]
    calc
      (Real.rpow delta (1 - finalLoss) *
            Real.rpow delta (finalLoss - stickyLoss)) * 1280 =
          Real.rpow delta (1 - finalLoss) *
            (1280 * Real.rpow delta (finalLoss - stickyLoss)) := by ring
      _ ≤ Real.rpow delta (1 - finalLoss) * 1 := by
        gcongr
        · exact Real.rpow_nonneg hdelta.le _
        · nlinarith
      _ = Real.rpow delta (1 - finalLoss) := by ring
      _ ≤ targetScale := htargetLower
  have hstickyUpper :
      pureWZ2SourceHorizontalInternalScale targetScale ≤
        Real.rpow delta stickyLoss := by
    have hdivide : targetScale / 1280 ≤ targetScale :=
      div_le_self htarget.le (by norm_num)
    exact hdivide.trans <| htargetUpper.trans <|
      Real.rpow_le_rpow_of_exponent_ge hdelta hdeltaOne hstickyFinal.le
  have hfinalScale :
      pureWZ2SourceHorizontalFinalScale
          (pureWZ2SourceHorizontalInternalScale targetScale) =
        targetScale := by
    simp [pureWZ2SourceHorizontalFinalScale,
      pureWZ2SourceHorizontalInternalScale]
    ring
  have hlengthLower :
      Real.rpow targetScale (1 / 2 + finalLoss) ≤
        Real.sqrt (pureWZ2SourceHorizontalInternalScale targetScale) :=
    pureWZ2_sourceHorizontal_length_lower hdelta hfinal htarget htargetUpper
      hlengthAbsorb
  exact ⟨{
    internal_pos := hinternalPos
    delta_le_internal := hdeltaInternal
    internal_le_one := by
      unfold pureWZ2SourceHorizontalInternalScale
      exact (div_le_self htarget.le (by norm_num)).trans htargetOne
    sticky_lower := hstickyLower
    sticky_upper := hstickyUpper
    final_scale_eq := hfinalScale
    final_scale_le_one := by simpa [hfinalScale] using htargetOne
    graph_scale_le_one := by
      unfold pureWZ2SourceHorizontalInternalScale
      calc
        256 * (targetScale / 1280) = targetScale / 5 := by ring
        _ ≤ targetScale := div_le_self htarget.le (by norm_num)
        _ ≤ 1 := htargetOne
    certificate_scale_le_one := by
      unfold pureWZ2SourceHorizontalInternalScale
      calc
        4 * (targetScale / 1280) = targetScale / 320 := by ring
        _ ≤ targetScale := div_le_self htarget.le (by norm_num)
        _ ≤ 1 := htargetOne
    length_lower := hlengthLower }⟩

/-- Uniform source threshold for the flexible outer scale. -/
theorem pureWZ2_sourceHorizontal_outerScale_flexible_schedule
    {stickyLoss finalLoss : ℝ}
    (hsticky : 0 < stickyLoss) (hstickyFinal : stickyLoss < finalLoss) :
    ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
        ∀ targetScale : ℝ,
          Real.rpow delta (1 - finalLoss) ≤ targetScale →
          targetScale ≤ Real.rpow delta finalLoss →
            Nonempty
              (PureWZ2SourceHorizontalFlexibleOuterScaleData
                delta targetScale stickyLoss finalLoss) := by
  have hfinal : 0 < finalLoss := hsticky.trans hstickyFinal
  rcases exists_delta_rpow_le_single
      (finalLoss - stickyLoss) (1 / 1280)
      (sub_pos.mpr hstickyFinal) (by norm_num) (by norm_num) with
    ⟨scaleDelta₀, hscaleDelta₀, hscaleDelta₀One, hscale⟩
  rcases exists_delta_rpow_le_single
      (finalLoss ^ 2) (1 / 36)
      (sq_pos_of_pos hfinal) (by norm_num) (by norm_num) with
    ⟨lengthDelta₀, hlengthDelta₀, hlengthDelta₀One, hlength⟩
  let delta₀ := min scaleDelta₀ lengthDelta₀
  refine ⟨delta₀, by positivity,
    (min_le_left _ _).trans hscaleDelta₀One, ?_⟩
  intro delta hdelta hdeltaSmall targetScale htargetLower htargetUpper
  exact pureWZ2_sourceHorizontal_outerScale_flexible
    hdelta (hdeltaSmall.trans ((min_le_left _ _).trans hscaleDelta₀One))
    hsticky hstickyFinal htargetLower htargetUpper
    (hscale delta hdelta (hdeltaSmall.trans (min_le_left _ _)))
    (hlength delta hdelta (hdeltaSmall.trans (min_le_right _ _)))

end Kakeya.Assouad
