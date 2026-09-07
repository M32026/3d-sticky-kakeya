import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12

/-!
# Extremality in the pure Definition 2.12 model

These declarations use ordinary unit-segment tubes, ordinary shadings, and the
parent-map-free nearby-scale condition.  WZ cubical and line-chart data are
deliberately absent.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Assouad

/-- A polylogarithmic mass-retention factor selected before the fine scale. -/
def wz2PaperPureRefinementFraction
    (delta : ℝ) (logExponent : ℕ) : ENNReal :=
  (ENNReal.ofReal (Real.log (1 / delta)))⁻¹ ^ logExponent

/-- An ordinary-tube refinement in the paper's indexed multiset model. -/
structure WZ2PaperPureRefinement
    {delta : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    (shading : Kakeya.Streamlined.TubeShading source)
    (logExponent : ℕ) where
  selected : WZ2PaperPureTubeSubfamily source
  refined :
    Kakeya.Streamlined.TubeShading selected.family
  subshading :
    ∀ index,
      refined.carrier index ⊆
        shading.carrier (selected.embedding index)
  retained_mass :
    wz2PaperPureRefinementFraction delta logExponent *
        shading.mass ≤
      refined.mass

/-- Extremality in the literal public Definition 2.12 model. -/
structure WZ2PaperPureIsExtremal
    {delta : ℝ}
    (sigma loss : ℝ)
    (family : Kakeya.Streamlined.TubeFamily delta)
    (shading : Kakeya.Streamlined.TubeShading family) : Prop where
  delta_pos : 0 < delta
  delta_le_one : delta ≤ 1
  nonempty : family.Nonempty
  cwa_nearby_scales :
    WZ2PaperPureCWAAtNearbyScales family
      (Kakeya.realRpowENN delta (-loss))
  dense :
    shading.IsLambdaDense
      (Kakeya.realRpowENN delta loss)
  volume_upper :
    volume shading.union ≤
      Kakeya.realRpowENN delta (sigma - loss)

/--
The lower-volume consequence of the critical exponent, formulated in exactly
the same pure Definition 2.12 model as public extremality.
-/
def HasWZ2PaperPureCriticalVolumeFloor (sigma : ℝ) : Prop :=
  ∀ floorLoss structuralBudget : ℝ,
    0 < floorLoss →
    0 < structuralBudget →
    ∃ structuralLoss delta₀ : ℝ,
      0 < structuralLoss ∧
      structuralLoss ≤ structuralBudget ∧
      0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
        ∀ family : Kakeya.Streamlined.TubeFamily delta,
          family.Nonempty →
          ∀ shading : Kakeya.Streamlined.TubeShading family,
            WZ2PaperPureCWAAtNearbyScales family
                (Kakeya.realRpowENN delta (-structuralLoss)) →
            shading.IsLambdaDense
                (Kakeya.realRpowENN delta structuralLoss) →
              Kakeya.realRpowENN delta (sigma + floorLoss) ≤
                volume shading.union

private theorem realRpowENN_antitone
    {delta first second : ℝ}
    (hdelta : 0 < delta)
    (hdeltaOne : delta ≤ 1)
    (h : first ≤ second) :
    Kakeya.realRpowENN delta second ≤
      Kakeya.realRpowENN delta first := by
  apply ENNReal.ofReal_mono
  exact
    Real.rpow_le_rpow_of_exponent_ge
      hdelta hdeltaOne h

namespace WZ2PaperPureScaleCoverData

/-- Increasing the finite error constant preserves one pure scale witness. -/
noncomputable def mono
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {firstConstant secondConstant : ENNReal}
    (data :
      WZ2PaperPureScaleCoverData fine rho firstConstant)
    (hC : firstConstant ≤ secondConstant) :
    WZ2PaperPureScaleCoverData fine rho secondConstant where
  delta_pos := data.delta_pos
  rho_pos := data.rho_pos
  coarse := data.coarse
  cover := data.cover
  full_fiber_uniform first second :=
    (data.full_fiber_uniform first second).trans (by
      gcongr)
  rescaledFiber parent := by
    rcases data.rescaledFiber parent with ⟨fiber⟩
    refine
      ⟨{
        normalization := fiber.normalization
        convex_wolff := fun convexSet hconvex =>
          (fiber.convex_wolff convexSet hconvex).trans (by
            gcongr)
      }⟩

end WZ2PaperPureScaleCoverData

namespace WZ2PaperPureCWAAtNearbyScales

/-- Increasing a finite constant preserves the pure nearby-scale condition. -/
theorem mono
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {firstConstant secondConstant : ENNReal}
    (hC : firstConstant ≤ secondConstant)
    (hSecondFinite : secondConstant ≠ ⊤)
    (data :
      WZ2PaperPureCWAAtNearbyScales family firstConstant) :
    WZ2PaperPureCWAAtNearbyScales family secondConstant := by
  refine
    ⟨data.1,
      ⟨data.2.1.1.trans hC, hSecondFinite⟩,
      data.2.2.1,
      ?_⟩
  intro rho₀
  rcases data.2.2.2 rho₀ with ⟨nearby⟩
  exact
    ⟨{
      rho := nearby.rho
      requested_le := nearby.requested_le
      within_factor :=
        nearby.within_factor.trans_le (by gcongr)
      scaleData := nearby.scaleData.mono hC
    }⟩

end WZ2PaperPureCWAAtNearbyScales

namespace WZ2PaperPureCWAAtNearbyScales

/-- Weakening the loss enlarges the allowed pure CWA constant. -/
theorem mono_loss
    {delta firstLoss secondLoss : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (hdelta : 0 < delta)
    (hdeltaOne : delta ≤ 1)
    (hloss : firstLoss ≤ secondLoss)
    (data :
      WZ2PaperPureCWAAtNearbyScales family
        (Kakeya.realRpowENN delta (-firstLoss))) :
    WZ2PaperPureCWAAtNearbyScales family
      (Kakeya.realRpowENN delta (-secondLoss)) := by
  have hC :
      Kakeya.realRpowENN delta (-firstLoss) ≤
        Kakeya.realRpowENN delta (-secondLoss) := by
    apply ENNReal.ofReal_mono
    exact
      Real.rpow_le_rpow_of_exponent_ge
        hdelta hdeltaOne (by linarith)
  exact
    data.mono hC (by simp [Kakeya.realRpowENN])

end WZ2PaperPureCWAAtNearbyScales

namespace WZ2PaperPureIsExtremal

/-- A pure extremal pair remains extremal after weakening the loss. -/
theorem mono_loss
    {delta sigma firstLoss secondLoss : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : Kakeya.Streamlined.TubeShading family}
    (data :
      WZ2PaperPureIsExtremal
        sigma firstLoss family shading)
    (hloss : firstLoss ≤ secondLoss) :
    WZ2PaperPureIsExtremal
      sigma secondLoss family shading := by
  have hcwaPower :
      Kakeya.realRpowENN delta (-firstLoss) ≤
        Kakeya.realRpowENN delta (-secondLoss) :=
    realRpowENN_antitone data.delta_pos data.delta_le_one
      (by linarith)
  have hdensePower :
      Kakeya.realRpowENN delta secondLoss ≤
        Kakeya.realRpowENN delta firstLoss :=
    realRpowENN_antitone data.delta_pos data.delta_le_one hloss
  have hvolumePower :
      Kakeya.realRpowENN delta (sigma - firstLoss) ≤
        Kakeya.realRpowENN delta (sigma - secondLoss) :=
    realRpowENN_antitone data.delta_pos data.delta_le_one
      (by linarith)
  exact
    {
      delta_pos := data.delta_pos
      delta_le_one := data.delta_le_one
      nonempty := data.nonempty
      cwa_nearby_scales :=
        data.cwa_nearby_scales.mono
          hcwaPower (by simp [Kakeya.realRpowENN])
      dense :=
        (mul_le_mul_right'
          hdensePower family.toBodyFamily.mass).trans
          data.dense
      volume_upper :=
        data.volume_upper.trans hvolumePower
    }

end WZ2PaperPureIsExtremal

end Kakeya.Assouad

end
