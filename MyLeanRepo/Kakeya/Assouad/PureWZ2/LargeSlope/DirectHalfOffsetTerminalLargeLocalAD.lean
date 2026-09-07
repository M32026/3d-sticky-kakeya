import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.DirectHalfOffsetTerminalSmallLocalAD
import MyLeanRepo.Kakeya.Assouad.WZ1.IntervalADHelpers

/-!
# Large-scale exact local AD for the direct half-offset terminal

Above the fixed cutoff `1 / 6400`, the enlarged exact terminal window has a
uniformly bounded one-dimensional covering number.
-/

noncomputable section

namespace Kakeya.Assouad

open Metric Set Real

/-- A diameter bound `D` gives paper AD once the elementary interval-covering
constant `2 * D / delta + 2` is absorbed. -/
lemma trivial_ad_set1_of_diameter
    {delta alpha D : ℝ} {C : ENNReal}
    (hdelta : 0 < delta) (halpha : 0 < alpha) (halphaOne : alpha ≤ 1)
    (hCOne : 1 ≤ C) (hCTop : C ≠ ⊤)
    (hconstant : ENNReal.ofReal (2 * D / delta + 2) ≤ C)
    {A : Set ℝ}
    (hdiameter : ∀ x y, x ∈ A → y ∈ A → dist x y ≤ D) :
    PureWZ2PaperADSet1 A delta alpha C := by
  by_cases hA : A.Nonempty
  · rcases hA with ⟨sample, hsample⟩
    have hD : 0 ≤ D := by simpa using hdiameter sample sample hsample hsample
    refine ⟨hdelta, halpha, halphaOne, hCOne, hCTop, ?_⟩
    intro scale hscaleNonneg hdeltaScale left length hscaleLength
    have hscale : 0 < scale := hdelta.trans_le hdeltaScale
    have hlocalDiameter : ∀ x y,
        x ∈ A ∩ Set.Icc left (left + length) →
        y ∈ A ∩ Set.Icc left (left + length) → dist x y ≤ D := by
      intro x y hx hy
      exact hdiameter x y hx.1 hy.1
    have hcover : (Metric.externalCoveringNumber ⟨scale, hscaleNonneg⟩
        (A ∩ Set.Icc left (left + length)) : ENNReal) ≤
        ENNReal.ofReal (2 * D / scale + 2) :=
      covering_by_diameter hscale hD hlocalDiameter
    have hquotient : 2 * D / scale + 2 ≤ 2 * D / delta + 2 := by
      have hdiv := div_le_div_of_nonneg_left (show 0 ≤ 2 * D by nlinarith)
        hdelta hdeltaScale
      linarith
    have hcovered : (Metric.externalCoveringNumber ⟨scale, hscaleNonneg⟩
        (A ∩ Set.Icc left (left + length)) : ENNReal) ≤ C :=
      hcover.trans <| (ENNReal.ofReal_le_ofReal hquotient).trans hconstant
    have hratio : 1 ≤ length / scale := by
      exact (le_div_iff₀ hscale).2 (by simpa using hscaleLength)
    have hpower : 1 ≤ Kakeya.realRpowENN (length / scale) alpha := by
      rw [Kakeya.realRpowENN, ENNReal.one_le_ofReal]
      exact one_le_rpow hratio halpha.le
    exact hcovered.trans (le_mul_of_one_le_right' hpower)
  · simp only [Set.not_nonempty_iff_eq_empty] at hA
    subst A
    exact ⟨hdelta, halpha, halphaOne, hCOne, hCTop, by
      intro scale hscale _ left length _
      simp⟩

namespace PureWZ2DirectCommonYSourceAssembly.TerminalGeometry

variable
    {logExponent : ℕ}
    {sigma epsilon delta : ℝ}
    (commonSource : PureWZ2DirectCommonYSourceAssembly
      logExponent sigma epsilon delta)

/-- The enlarged exact terminal ball has projected diameter at most twice its
spatial radius because the exact normal is unit. -/
theorem exactLocalSet_projection_diameter
    (terminal : commonSource.TerminalGeometry)
    (anchor0 : {point : Point3 // point ∈ terminal.exactShading.union})
    {radius : ℝ} (_hradius : 0 ≤ radius)
    (x y : ℝ)
    (hx : x ∈ scalarProjection (exactPlaneMap commonSource terminal anchor0)
      (exactLocalSet commonSource terminal anchor0 radius))
    (hy : y ∈ scalarProjection (exactPlaneMap commonSource terminal anchor0)
      (exactLocalSet commonSource terminal anchor0 radius)) :
    dist x y ≤ 2 * radius := by
  rcases hx with ⟨px, hpx, rfl⟩
  rcases hy with ⟨py, hpy, rfl⟩
  have hunit : ‖exactPlaneMap commonSource terminal anchor0‖ = 1 := by
    exact commonSource.halfOffsetTerminalExactPlaneMap_unit terminal.retubing
      terminal.box (exactSetPoint commonSource terminal anchor0)
  have hinner := abs_real_inner_le_norm (px - py)
    (exactPlaneMap commonSource terminal anchor0)
  have hdistPoints : dist px py ≤ 2 * radius := by
    calc
      dist px py ≤ dist px (anchor0 : Point3) +
          dist (anchor0 : Point3) py := dist_triangle _ _ _
      _ ≤ radius + radius := by
        exact add_le_add (Metric.mem_closedBall.mp hpx.2) <| by
          rw [dist_comm]
          exact Metric.mem_closedBall.mp hpy.2
      _ = 2 * radius := by ring
  rw [Real.dist_eq, ← inner_sub_left]
  exact hinner.trans <| by rw [hunit, mul_one]; simpa [dist_eq_norm] using hdistPoints

/-- The fixed cutoff makes the elementary enlarged-ball covering constant at
most `338`. -/
theorem enlarged_ball_covering_constant_le
    (terminal : commonSource.TerminalGeometry)
    {rho : ℝ} (hrhoLower : 1 / 6400 ≤ rho) (_hrhoOne : rho ≤ 1)
    (htarget : terminal.targetDelta ≤ rho) :
    2 * (2 * pureWZ2DirectHalfOffsetTerminalLocalADR rho terminal.targetDelta) /
        rho + 2 ≤ 338 := by
  have hrho : 0 < rho := (by norm_num : (0 : ℝ) < 1 / 6400).trans_le hrhoLower
  have hsqrtNonneg := Real.sqrt_nonneg rho
  have hsqrtSq := Real.sq_sqrt hrho.le
  have hsqrtThreeNonneg := Real.sqrt_nonneg 3
  have hsqrtThreeSq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have hsqrtThree : Real.sqrt 3 ≤ 2 := by nlinarith
  have hsqrtLower : 1 / 80 ≤ Real.sqrt rho := by nlinarith
  have hR : pureWZ2DirectHalfOffsetTerminalLocalADR rho terminal.targetDelta ≤
      Real.sqrt rho + 4 * rho := by
    unfold pureWZ2DirectHalfOffsetTerminalLocalADR
    have htargetNonneg := commonSource.halfOffsetLineClassTargetDelta_pos.le
    nlinarith [mul_le_mul_of_nonneg_left hsqrtThree htargetNonneg, htarget]
  have hquot : Real.sqrt rho / rho ≤ 80 := by
    have hsqrtPos : 0 < Real.sqrt rho :=
      (by norm_num : (0 : ℝ) < 1 / 80).trans_le hsqrtLower
    have heq : Real.sqrt rho / rho = 1 / Real.sqrt rho := by
      field_simp [hrho.ne', hsqrtPos.ne']
      nlinarith
    rw [heq]
    exact (div_le_iff₀ hsqrtPos).2 (by nlinarith [hsqrtLower])
  have hscaled := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hR (by norm_num : (0 : ℝ) ≤ 4)) hrho.le
  have hexpanded : 4 * (Real.sqrt rho + 4 * rho) / rho =
      4 * (Real.sqrt rho / rho) + 16 := by
    field_simp [hrho.ne']
    ring
  rw [hexpanded] at hscaled
  have hleft :
      2 * (2 * pureWZ2DirectHalfOffsetTerminalLocalADR rho
        terminal.targetDelta) / rho + 2 =
      4 * pureWZ2DirectHalfOffsetTerminalLocalADR rho terminal.targetDelta /
        rho + 2 := by ring
  rw [hleft]
  linarith

/-- Large-scale exact local AD for the actual enlarged terminal window. -/
theorem exact_local_ad_large
    (terminal : commonSource.TerminalGeometry)
    (anchor0 : {point : Point3 // point ∈ terminal.exactShading.union})
    {rho : ℝ} (hrhoLower : 1 / 6400 ≤ rho) (hrhoOne : rho ≤ 1)
    (htarget : terminal.targetDelta ≤ rho)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1) :
    PureWZ2PaperADSet1
      (scalarProjection (exactPlaneMap commonSource terminal anchor0)
        (exactLocalSet commonSource terminal anchor0
          (pureWZ2DirectHalfOffsetTerminalLocalADR rho terminal.targetDelta)))
      rho (1 - sigma) 338 := by
  let radius := pureWZ2DirectHalfOffsetTerminalLocalADR rho terminal.targetDelta
  have hrho : 0 < rho := (by norm_num : (0 : ℝ) < 1 / 6400).trans_le hrhoLower
  have hradius : 0 ≤ radius := by
    dsimp only [radius, pureWZ2DirectHalfOffsetTerminalLocalADR]
    positivity [commonSource.halfOffsetLineClassTargetDelta_pos]
  apply trivial_ad_set1_of_diameter hrho (by linarith) (by linarith)
    (by norm_num) (by norm_num)
  · simpa only [radius, ENNReal.ofReal_ofNat] using
      ENNReal.ofReal_le_ofReal
        (enlarged_ball_covering_constant_le commonSource terminal hrhoLower
          hrhoOne htarget)
  · exact exactLocalSet_projection_diameter commonSource terminal anchor0
      hradius

/-- Uniform exact local AD at every requested target scale, obtained by the
small-scale finite-cover argument or the large-scale diameter argument. -/
theorem exact_local_ad_all_scales
    (terminal : commonSource.TerminalGeometry)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    {Ctarget : ENNReal}
    (hCtargetOne : 1 ≤ Ctarget) (hCtargetTop : Ctarget ≠ ⊤)
    (hlarge : (338 : ENNReal) ≤ Ctarget)
    (hsmall : ∀ (rho : ℝ) (n : ℕ),
      0 < rho → rho ≤ 1 / 6400 →
      (n : ℝ) ≤ 9 *
        (commonSource.halfOffsetAssembly.horizontalSource.m *
          (commonSource.halfOffsetAssembly.horizontalSource.d -
            commonSource.halfOffsetAssembly.horizontalSource.c) / 2)⁻¹ →
      (n : ENNReal) *
          ((2 * (Nat.ceil ((5 * rho) / rho) + 1) : ENNReal) ^ 3 *
            Kakeya.realRpowENN delta
              (-commonSource.halfOffsetAssembly.technicalLoss)) ≤ Ctarget) :
    ∀ rho : ℝ, terminal.targetDelta ≤ rho → rho ≤ 1 →
      ∀ anchor0 : {point : Point3 // point ∈ terminal.exactShading.union},
        PureWZ2PaperADSet1
          (scalarProjection (exactPlaneMap commonSource terminal anchor0)
            (exactLocalSet commonSource terminal anchor0
              (pureWZ2DirectHalfOffsetTerminalLocalADR rho
                terminal.targetDelta)))
          rho (1 - sigma) Ctarget := by
  intro rho htarget hrhoOne anchor0
  have hrho : 0 < rho :=
    commonSource.halfOffsetLineClassTargetDelta_pos.trans_le htarget
  by_cases hrhoTiny : rho ≤ 1 / 6400
  · exact exact_local_ad_small commonSource terminal anchor0 hrho hrhoTiny
      htarget hCtargetOne hCtargetTop (fun n hn =>
        hsmall rho n hrho hrhoTiny hn)
  · have hrhoLarge : 1 / 6400 ≤ rho := le_of_not_ge hrhoTiny
    exact (exact_local_ad_large commonSource terminal anchor0 hrhoLarge hrhoOne
      htarget hsigma hsigmaOne).weaken_constant hlarge hCtargetOne hCtargetTop

end PureWZ2DirectCommonYSourceAssembly.TerminalGeometry

end Kakeya.Assouad

end
