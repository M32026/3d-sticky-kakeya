import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains
import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12CroppedExtremal
import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12Extremal
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Critical

/-!
# Loss-weakening lemmas for grain configurations

When `loss_src ≤ outputLoss` and `0 < delta ≤ 1`, all bounds parameterized by
`loss` weaken as `loss` increases:
- `delta^(-loss)` increases → CWA bound weakens
- `delta^(sigma - loss)` increases → volume upper bound weakens
- `delta^loss` decreases → density condition weakens

This allows converting extremal/CWA data from `loss_src` to `outputLoss`.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

/-- Weaken a `WZ2PaperConvexWolffBound` from a smaller constant to a larger one. -/
lemma weaken_convex_wolff_bound
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {C1 C2 : ENNReal}
    (h : WZ2PaperConvexWolffBound family C1)
    (hC : C1 ≤ C2) :
    WZ2PaperConvexWolffBound family C2 := by
  intro convexSet hconv
  have h1 := h convexSet hconv
  calc
    (wz1PaperBodyFamily family).containedCount convexSet
      ≤ C1 * volume convexSet * family.enncard := h1
    _ ≤ C2 * volume convexSet * family.enncard := by
      gcongr

/-- Weaken `WZ2PaperPureFullFibersAreCUniform` from a smaller constant to a larger one. -/
lemma weaken_full_fibers_c_uniform
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {C1 C2 : ENNReal}
    (h : WZ2PaperPureFullFibersAreCUniform fine coarse C1)
    (hC : C1 ≤ C2) :
    WZ2PaperPureFullFibersAreCUniform fine coarse C2 := by
  intro first second
  have h1 := h first second
  calc
    wz2PaperOrdinaryFullFiberCount fine coarse first
      ≤ C1 * wz2PaperOrdinaryFullFiberCount fine coarse second := h1
    _ ≤ C2 * wz2PaperOrdinaryFullFiberCount fine coarse second := by
      gcongr

/-- Weaken `WZ2PaperBodyConvexWolffBound` from a smaller constant to a larger one. -/
lemma weaken_body_convex_wolff_bound
    {family : Kakeya.Streamlined.BodyFamily}
    {C1 C2 : ENNReal}
    (h : WZ2PaperBodyConvexWolffBound family C1)
    (hC : C1 ≤ C2) :
    WZ2PaperBodyConvexWolffBound family C2 := by
  intro convexSet hconv
  have h1 := h convexSet hconv
  calc
    family.containedCount convexSet
      ≤ C1 * volume convexSet * family.enncard := h1
    _ ≤ C2 * volume convexSet * family.enncard := by gcongr

/-- Weaken `WZ2PaperPureScaleCoverData` from a smaller constant to a larger one. -/
def weaken_scale_cover_data
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {C1 C2 : ENNReal}
    (h : WZ2PaperPureScaleCoverData fine rho C1)
    (hC : C1 ≤ C2) :
    WZ2PaperPureScaleCoverData fine rho C2 := by
  refine' {
    delta_pos := h.delta_pos,
    rho_pos := h.rho_pos,
    coarse := h.coarse,
    cover := h.cover,
    full_fiber_uniform := weaken_full_fibers_c_uniform h.full_fiber_uniform hC,
    rescaledFiber := _
  }
  intro parent
  rcases h.rescaledFiber parent with ⟨data⟩
  let bodyFam := wz2PaperPureUnitRescaledFullFiberBodyFamily
    (fine := fine) (coarse := h.coarse) parent data.normalization
  refine' ⟨{
    normalization := data.normalization,
    convex_wolff := weaken_body_convex_wolff_bound data.convex_wolff hC
  }⟩

/-- Weaken `WZ2PaperPureNearbyScaleCoverData` from a smaller constant to a larger one. -/
def weaken_nearby_scale_cover_data
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {rho₀ : WZ2PaperRequestedScale delta}
    {C1 C2 : ENNReal}
    (h : WZ2PaperPureNearbyScaleCoverData family rho₀ C1)
    (hC : C1 ≤ C2) :
    WZ2PaperPureNearbyScaleCoverData family rho₀ C2 := by
  refine' {
    rho := h.rho,
    requested_le := h.requested_le,
    within_factor := _,
    scaleData := weaken_scale_cover_data h.scaleData hC
  }
  calc
    ENNReal.ofReal h.rho
      < C1 * ENNReal.ofReal rho₀.1 := h.within_factor
    _ ≤ C2 * ENNReal.ofReal rho₀.1 := by gcongr

/-- Weaken `WZ2PaperPureCWAAtNearbyScales` from a smaller constant to a larger one. -/
lemma weaken_cwa_nearby_scales
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {C1 C2 : ENNReal}
    (h : WZ2PaperPureCWAAtNearbyScales family C1)
    (hC : C1 ≤ C2)
    (hC2_finite : WZ2PaperFiniteErrorConstant C2) :
    WZ2PaperPureCWAAtNearbyScales family C2 := by
  have h1 : 0 < delta := h.1
  have h2 : WZ2PaperOrdinaryIsEssentiallyDistinct family := h.2.2.1
  have h3 : ∀ rho₀, Nonempty (WZ2PaperPureNearbyScaleCoverData family rho₀ C1) := h.2.2.2
  refine' ⟨h1, hC2_finite, h2, _⟩
  intro rho₀
  rcases h3 rho₀ with ⟨data⟩
  exact ⟨weaken_nearby_scale_cover_data data hC⟩

/-- Weaken `WZ2PaperCroppedIsExtremal` from `loss_src` to `outputLoss`
when `loss_src ≤ outputLoss` and `0 < delta ≤ 1`. -/
theorem weaken_cropped_extremal
    {sigma loss_src outputLoss delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    (h : WZ2PaperCroppedIsExtremal sigma loss_src family shading)
    (hloss_le : loss_src ≤ outputLoss)
    (houtputLoss_pos : 0 < outputLoss)
    (hdelta_pos : 0 < delta)
    (hdelta_le_one : delta ≤ 1) :
    WZ2PaperCroppedIsExtremal sigma outputLoss family shading := by
  have hC1_le_C2 : Kakeya.realRpowENN delta (-loss_src) ≤ Kakeya.realRpowENN delta (-outputLoss) := by
    simp only [Kakeya.realRpowENN]
    have h_exp : -outputLoss ≤ -loss_src := by linarith
    have h2 : Real.rpow delta (-loss_src) ≤ Real.rpow delta (-outputLoss) :=
      Real.rpow_le_rpow_of_exponent_ge hdelta_pos hdelta_le_one h_exp
    exact ENNReal.ofReal_le_ofReal h2
  have h_density_weak : Kakeya.realRpowENN delta outputLoss ≤ Kakeya.realRpowENN delta loss_src := by
    simp only [Kakeya.realRpowENN]
    have h_exp : loss_src ≤ outputLoss := hloss_le
    have h4 : Real.rpow delta outputLoss ≤ Real.rpow delta loss_src :=
      Real.rpow_le_rpow_of_exponent_ge hdelta_pos hdelta_le_one h_exp
    exact ENNReal.ofReal_le_ofReal h4
  have h_vol_weak : Kakeya.realRpowENN delta (sigma - loss_src) ≤ Kakeya.realRpowENN delta (sigma - outputLoss) := by
    simp only [Kakeya.realRpowENN]
    have h_exp : sigma - outputLoss ≤ sigma - loss_src := by linarith
    have h6 : Real.rpow delta (sigma - loss_src) ≤ Real.rpow delta (sigma - outputLoss) :=
      Real.rpow_le_rpow_of_exponent_ge hdelta_pos hdelta_le_one h_exp
    exact ENNReal.ofReal_le_ofReal h6
  have hC2_finite : WZ2PaperFiniteErrorConstant (Kakeya.realRpowENN delta (-outputLoss)) := by
    have h7 : 1 ≤ Kakeya.realRpowENN delta (-outputLoss) := by
      simp only [Kakeya.realRpowENN]
      have h8 : Real.rpow delta (-outputLoss) ≥ 1 := by
        have h10 : Real.rpow delta 0 ≤ Real.rpow delta (-outputLoss) :=
          Real.rpow_le_rpow_of_exponent_ge hdelta_pos hdelta_le_one (show -outputLoss ≤ 0 by linarith)
        simpa using h10
      have h7' : (1 : ENNReal) ≤ ENNReal.ofReal (Real.rpow delta (-outputLoss)) := by
        simpa [ENNReal.ofReal] using h8
      exact h7'
    have h9 : Kakeya.realRpowENN delta (-outputLoss) ≠ ⊤ := by
      simp [Kakeya.realRpowENN, ENNReal.ofReal_ne_top]
    exact ⟨h7, h9⟩
  refine' {
    delta_pos := h.delta_pos,
    delta_le_one := h.delta_le_one,
    nonempty := h.nonempty,
    cwa_nearby_scales := weaken_cwa_nearby_scales h.cwa_nearby_scales hC1_le_C2 hC2_finite,
    cubical := h.cubical,
    dense := _,
    volume_upper := _
  }
  · -- Density: lambda * F.mass ≤ Y.mass, lambda decreases, so condition weakens
    have hdense : shading.IsLambdaDense (Kakeya.realRpowENN delta loss_src) := h.dense
    let bodyFam := wz1PaperBodyFamily family
    have h11 : (Kakeya.realRpowENN delta outputLoss) * bodyFam.mass ≤
          (Kakeya.realRpowENN delta loss_src) * bodyFam.mass := by
      gcongr
    simpa [Streamlined.Shading.IsLambdaDense] using le_trans h11 hdense
  · -- Volume upper bound
    calc
      volume shading.union
        ≤ Kakeya.realRpowENN delta (sigma - loss_src) := h.volume_upper
      _ ≤ Kakeya.realRpowENN delta (sigma - outputLoss) := h_vol_weak

/-- Weaken `WZ2PaperPureIsExtremal` from `loss_src` to `outputLoss`. -/
theorem weaken_pure_is_extremal
    {sigma loss_src outputLoss delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : Kakeya.Streamlined.TubeShading family}
    (h : WZ2PaperPureIsExtremal sigma loss_src family shading)
    (hloss_le : loss_src ≤ outputLoss)
    (houtputLoss_pos : 0 < outputLoss)
    (hdelta_pos : 0 < delta)
    (hdelta_le_one : delta ≤ 1) :
    WZ2PaperPureIsExtremal sigma outputLoss family shading := by
  have hC1_le_C2 : Kakeya.realRpowENN delta (-loss_src) ≤
        Kakeya.realRpowENN delta (-outputLoss) := by
    simp only [Kakeya.realRpowENN]
    have h_exp : -outputLoss ≤ -loss_src := by linarith
    have h2 : Real.rpow delta (-loss_src) ≤ Real.rpow delta (-outputLoss) :=
      Real.rpow_le_rpow_of_exponent_ge hdelta_pos hdelta_le_one h_exp
    exact ENNReal.ofReal_le_ofReal h2
  have h_density_weak : Kakeya.realRpowENN delta outputLoss ≤
        Kakeya.realRpowENN delta loss_src := by
    simp only [Kakeya.realRpowENN]
    have h_exp : loss_src ≤ outputLoss := hloss_le
    have h4 : Real.rpow delta outputLoss ≤ Real.rpow delta loss_src :=
      Real.rpow_le_rpow_of_exponent_ge hdelta_pos hdelta_le_one h_exp
    exact ENNReal.ofReal_le_ofReal h4
  have h_vol_weak : Kakeya.realRpowENN delta (sigma - loss_src) ≤
        Kakeya.realRpowENN delta (sigma - outputLoss) := by
    simp only [Kakeya.realRpowENN]
    have h_exp : sigma - outputLoss ≤ sigma - loss_src := by linarith
    have h6 : Real.rpow delta (sigma - loss_src) ≤ Real.rpow delta (sigma - outputLoss) :=
      Real.rpow_le_rpow_of_exponent_ge hdelta_pos hdelta_le_one h_exp
    exact ENNReal.ofReal_le_ofReal h6
  have hC2_finite : WZ2PaperFiniteErrorConstant
        (Kakeya.realRpowENN delta (-outputLoss)) := by
    have h7 : 1 ≤ Kakeya.realRpowENN delta (-outputLoss) := by
      simp only [Kakeya.realRpowENN]
      have h8 : Real.rpow delta (-outputLoss) ≥ 1 := by
        have h9 : Real.rpow delta 0 ≤ Real.rpow delta (-outputLoss) :=
          Real.rpow_le_rpow_of_exponent_ge hdelta_pos hdelta_le_one (show -outputLoss ≤ 0 by linarith)
        simpa using h9
      have h10 : (1 : ENNReal) = ENNReal.ofReal (1 : ℝ) := by simp
      rw [h10]
      exact ENNReal.ofReal_le_ofReal h8
    have h9 : Kakeya.realRpowENN delta (-outputLoss) ≠ ⊤ := by
      simp [Kakeya.realRpowENN, ENNReal.ofReal_ne_top]
    exact ⟨h7, h9⟩
  refine' {
    delta_pos := h.delta_pos,
    delta_le_one := h.delta_le_one,
    nonempty := h.nonempty,
    cwa_nearby_scales := weaken_cwa_nearby_scales h.cwa_nearby_scales hC1_le_C2 hC2_finite,
    dense := _,
    volume_upper := _
  }
  · have hdense : shading.IsLambdaDense (Kakeya.realRpowENN delta loss_src) := h.dense
    have h11 : (Kakeya.realRpowENN delta outputLoss) * family.toBodyFamily.mass ≤
          (Kakeya.realRpowENN delta loss_src) * family.toBodyFamily.mass := by gcongr
    simpa [Streamlined.Shading.IsLambdaDense] using le_trans h11 hdense
  · calc
      volume shading.union
        ≤ Kakeya.realRpowENN delta (sigma - loss_src) := h.volume_upper
      _ ≤ Kakeya.realRpowENN delta (sigma - outputLoss) := h_vol_weak

/-- Weaken a `PureWZ2ExtremalConfiguration` from `loss_src` to `outputLoss`. -/
def weaken_extremal_configuration
    {sigma loss_src outputLoss delta : ℝ}
    (config : PureWZ2ExtremalConfiguration sigma loss_src delta)
    (hloss_le : loss_src ≤ outputLoss)
    (houtputLoss_pos : 0 < outputLoss)
    (hdelta_pos : 0 < delta)
    (hdelta_le_one : delta ≤ 1) :
    PureWZ2ExtremalConfiguration sigma outputLoss delta :=
  { family := config.family
    shading := config.shading
    extremal := weaken_pure_is_extremal config.extremal hloss_le
        houtputLoss_pos hdelta_pos hdelta_le_one }

/-- Re-root a `PureWZ2CroppedCriticalNormalizationData` at a weakened source.

Since `weaken_extremal_configuration` preserves `family` and `shading`
definitionally, all fields of the normalized data transfer unchanged.
Requires `inputLoss_s ≤ outputLoss / 2` for the strengthened normalization
loss gap. -/
def weaken_normalized_data_source
    {sigma inputLoss_n inputLoss_s outputLoss delta : ℝ}
    {nE : ℕ}
    {source_n : PureWZ2ExtremalConfiguration sigma inputLoss_n delta}
    (normalized : PureWZ2CroppedCriticalNormalizationData
        (outputLoss := outputLoss) source_n nE)
    (hloss_le : inputLoss_n ≤ inputLoss_s)
    (hinputLoss_s_le_half : inputLoss_s ≤ outputLoss / 2)
    (hinputLoss_s_pos : 0 < inputLoss_s)
    (hdelta_pos : 0 < delta)
    (hdelta_le_one : delta ≤ 1) :
    PureWZ2CroppedCriticalNormalizationData
        (outputLoss := outputLoss)
        (weaken_extremal_configuration source_n hloss_le hinputLoss_s_pos hdelta_pos hdelta_le_one)
        nE :=
  let source_s := weaken_extremal_configuration source_n hloss_le hinputLoss_s_pos hdelta_pos hdelta_le_one
  { input_loss_le_half := hinputLoss_s_le_half
    selected := normalized.selected
    selected_nonempty := normalized.selected_nonempty
    ordinaryRefined := normalized.ordinaryRefined
    ordinary_subshading := normalized.ordinary_subshading
    retained_mass := normalized.retained_mass
    frame := normalized.frame
    croppedFamily := normalized.croppedFamily
    indexEquiv := normalized.indexEquiv
    ordinary_carrier_image_eq := normalized.ordinary_carrier_image_eq
    ordinary_per_tube := by
      intro index
      calc
        (Kakeya.realRpowENN delta inputLoss_s / 2) *
              volume (normalized.selected.family.tube index).carrier ≤
            (Kakeya.realRpowENN delta inputLoss_n / 2) *
              volume (normalized.selected.family.tube index).carrier := by
          gcongr
          apply ENNReal.ofReal_mono
          exact Real.rpow_le_rpow_of_exponent_ge
            hdelta_pos hdelta_le_one hloss_le
        _ ≤ volume (normalized.ordinaryRefined.carrier index) :=
          normalized.ordinary_per_tube index
    ordinary_axial_window := normalized.ordinary_axial_window
    croppedRefined := normalized.croppedRefined
    cropped_carrier_eq_dense_cubicalization := normalized.cropped_carrier_eq_dense_cubicalization
    cropped_cubical := normalized.cropped_cubical
    line_class := normalized.line_class
    cropped_top_level_cwa := normalized.cropped_top_level_cwa
    final_extremal := normalized.final_extremal
    ordinary_cell_containment := normalized.ordinary_cell_containment
    ordinary_bounded_base := normalized.ordinary_bounded_base }

/-- Weaken both the source loss and the outputLoss parameter of a
`PureWZ2CroppedCriticalNormalizationData`.

The family and shading are preserved definitionally. The CWA and extremal
bounds are weakened from `old_output_loss` to `new_output_loss`. -/
def weaken_normalized_data
    {sigma old_input_loss new_input_loss old_output_loss new_output_loss delta : ℝ}
    {nE : ℕ}
    {source_old : PureWZ2ExtremalConfiguration sigma old_input_loss delta}
    (normalized : PureWZ2CroppedCriticalNormalizationData
        (outputLoss := old_output_loss) source_old nE)
    (h_input_le : old_input_loss ≤ new_input_loss)
    (h_output_le : old_output_loss ≤ new_output_loss)
    (h_new_input_pos : 0 < new_input_loss)
    (h_new_output_pos : 0 < new_output_loss)
    (hdelta_pos : 0 < delta)
    (hdelta_le_one : delta ≤ 1)
    (h_input_le_output : new_input_loss ≤ new_output_loss / 2) :
    PureWZ2CroppedCriticalNormalizationData
        (outputLoss := new_output_loss)
        (weaken_extremal_configuration source_old h_input_le h_new_input_pos hdelta_pos hdelta_le_one)
        nE :=
  let source_new := weaken_extremal_configuration source_old h_input_le h_new_input_pos hdelta_pos hdelta_le_one
  have h_cwa_le : Kakeya.realRpowENN delta (-old_output_loss) ≤
        Kakeya.realRpowENN delta (-new_output_loss) := by
    simp only [Kakeya.realRpowENN]
    have h_exp : -new_output_loss ≤ -old_output_loss := by linarith
    have h2 : Real.rpow delta (-old_output_loss) ≤ Real.rpow delta (-new_output_loss) :=
      Real.rpow_le_rpow_of_exponent_ge hdelta_pos hdelta_le_one h_exp
    exact ENNReal.ofReal_le_ofReal h2
  { input_loss_le_half := h_input_le_output
    selected := normalized.selected
    selected_nonempty := normalized.selected_nonempty
    ordinaryRefined := normalized.ordinaryRefined
    ordinary_subshading := normalized.ordinary_subshading
    retained_mass := normalized.retained_mass
    frame := normalized.frame
    croppedFamily := normalized.croppedFamily
    indexEquiv := normalized.indexEquiv
    ordinary_carrier_image_eq := normalized.ordinary_carrier_image_eq
    ordinary_per_tube := by
      intro index
      calc
        (Kakeya.realRpowENN delta new_input_loss / 2) *
              volume (normalized.selected.family.tube index).carrier ≤
            (Kakeya.realRpowENN delta old_input_loss / 2) *
              volume (normalized.selected.family.tube index).carrier := by
          gcongr
          apply ENNReal.ofReal_mono
          exact Real.rpow_le_rpow_of_exponent_ge
            hdelta_pos hdelta_le_one h_input_le
        _ ≤ volume (normalized.ordinaryRefined.carrier index) :=
          normalized.ordinary_per_tube index
    ordinary_axial_window := normalized.ordinary_axial_window
    croppedRefined := normalized.croppedRefined
    cropped_carrier_eq_dense_cubicalization := normalized.cropped_carrier_eq_dense_cubicalization
    cropped_cubical := normalized.cropped_cubical
    line_class := normalized.line_class
    cropped_top_level_cwa := weaken_convex_wolff_bound normalized.cropped_top_level_cwa h_cwa_le
    final_extremal := weaken_cropped_extremal normalized.final_extremal
        h_output_le h_new_output_pos hdelta_pos hdelta_le_one
    ordinary_cell_containment := normalized.ordinary_cell_containment
    ordinary_bounded_base := normalized.ordinary_bounded_base }

end Kakeya.Assouad

end
