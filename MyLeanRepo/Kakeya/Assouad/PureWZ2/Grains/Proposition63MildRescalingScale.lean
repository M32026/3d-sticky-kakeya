import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12

/-!
# Scale bookkeeping for the final Proposition 6.3 mild rescaling

The last step of Proposition 6.3 restricts to a small box and applies a
positive isotropic dilation by a factor `scale >= 1`.  A requested target
scale `targetRho` must therefore be pulled back to the exact source request
`targetRho / scale`.  Definition 2.12 may answer that request at a nearby
actual source scale; multiplying that actual scale by `scale` preserves the
same multiplicative nearby window.

This module records only that exact scale bookkeeping.  It constructs no
target tube family and makes no carrier-containment claim.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

/-- Pull a target requested scale back through a positive isotropic
dilation. -/
def proposition63MildRescalingSourceRequest
    {sourceDelta scale : ℝ}
    (hsourceDelta : 0 < sourceDelta)
    (hscale : 1 ≤ scale)
    (target : WZ2PaperRequestedScale (scale * sourceDelta)) :
    WZ2PaperRequestedScale sourceDelta := by
  have hscalePos : 0 < scale := lt_of_lt_of_le zero_lt_one hscale
  refine ⟨target.1 / scale, ?_, ?_⟩
  · exact (le_div_iff₀ hscalePos).2 (by
      simpa [mul_comm] using target.2.1)
  · exact (div_le_one hscalePos).2 (target.2.2.trans hscale)

/-- The pulled-back requested scale is exactly the original target request
after applying the dilation factor. -/
lemma proposition63MildRescalingSourceRequest_scale
    {sourceDelta scale : ℝ}
    (hsourceDelta : 0 < sourceDelta)
    (hscale : 1 ≤ scale)
    (target : WZ2PaperRequestedScale (scale * sourceDelta)) :
    scale *
        (proposition63MildRescalingSourceRequest
          hsourceDelta hscale target).1 =
      target.1 := by
  have hscalePos : 0 < scale := lt_of_lt_of_le zero_lt_one hscale
  dsimp only [proposition63MildRescalingSourceRequest]
  field_simp [hscalePos.ne']

/-- If the actual source scale lies above the pulled-back request, then its
isotropic image lies above the original target request. -/
lemma proposition63MildRescaling_requested_le_targetActual
    {sourceDelta scale sourceActual : ℝ}
    (hsourceDelta : 0 < sourceDelta)
    (hscale : 1 ≤ scale)
    (target : WZ2PaperRequestedScale (scale * sourceDelta))
    (hnearby :
      (proposition63MildRescalingSourceRequest
        hsourceDelta hscale target).1 ≤ sourceActual) :
    target.1 ≤ scale * sourceActual := by
  have hscaleNonnegative : 0 ≤ scale := zero_le_one.trans hscale
  calc
    target.1 = scale *
        (proposition63MildRescalingSourceRequest
          hsourceDelta hscale target).1 :=
      (proposition63MildRescalingSourceRequest_scale
        hsourceDelta hscale target).symm
    _ ≤ scale * sourceActual :=
      mul_le_mul_of_nonneg_left hnearby hscaleNonnegative

/-- Multiplying both actual and requested scales by the same positive factor
preserves the Definition 2.12 nearby-scale window. -/
lemma proposition63MildRescaling_withinFactor
    {sourceDelta scale sourceActual : ℝ}
    {C : ENNReal}
    (hsourceDelta : 0 < sourceDelta)
    (hscale : 1 ≤ scale)
    (target : WZ2PaperRequestedScale (scale * sourceDelta))
    (hnearby :
      ENNReal.ofReal sourceActual <
        C * ENNReal.ofReal
          (proposition63MildRescalingSourceRequest
            hsourceDelta hscale target).1) :
    ENNReal.ofReal (scale * sourceActual) <
      C * ENNReal.ofReal target.1 := by
  have hscaleNonnegative : 0 ≤ scale := zero_le_one.trans hscale
  have hscalePositive : 0 < ENNReal.ofReal scale :=
    ENNReal.ofReal_pos.mpr (lt_of_lt_of_le zero_lt_one hscale)
  have hscaled := ENNReal.mul_lt_mul_left hscalePositive.ne'
    ENNReal.ofReal_ne_top hnearby
  have hscaled' :
      ENNReal.ofReal scale * ENNReal.ofReal sourceActual <
        C *
          (ENNReal.ofReal scale *
            ENNReal.ofReal
              (proposition63MildRescalingSourceRequest
                hsourceDelta hscale target).1) := by
    calc
      ENNReal.ofReal scale * ENNReal.ofReal sourceActual =
          ENNReal.ofReal sourceActual * ENNReal.ofReal scale := by
        rw [mul_comm]
      _ <
          (C * ENNReal.ofReal
            (proposition63MildRescalingSourceRequest
              hsourceDelta hscale target).1) *
            ENNReal.ofReal scale := hscaled
      _ = C *
          (ENNReal.ofReal scale *
            ENNReal.ofReal
              (proposition63MildRescalingSourceRequest
                hsourceDelta hscale target).1) := by
        ac_rfl
  have hrequest :
      ENNReal.ofReal scale *
          ENNReal.ofReal
            (proposition63MildRescalingSourceRequest
              hsourceDelta hscale target).1 =
        ENNReal.ofReal target.1 := by
    rw [← ENNReal.ofReal_mul hscaleNonnegative]
    rw [proposition63MildRescalingSourceRequest_scale
      hsourceDelta hscale target]
  calc
    ENNReal.ofReal (scale * sourceActual) =
        ENNReal.ofReal scale * ENNReal.ofReal sourceActual := by
      rw [ENNReal.ofReal_mul hscaleNonnegative]
    _ < C *
        (ENNReal.ofReal scale *
          ENNReal.ofReal
            (proposition63MildRescalingSourceRequest
              hsourceDelta hscale target).1) := hscaled'
    _ = C * ENNReal.ofReal target.1 := by rw [hrequest]

end Kakeya.Assouad.PureWZ2

end
