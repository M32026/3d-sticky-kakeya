import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma8_13FaithfulStatements
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma8_13FaithfulExtremeCases
import MyLeanRepo.Kakeya.Assouad.WZ1.IncidenceGraph
import MyLeanRepo.Kakeya.Assouad.WZ1.Definitions

/-!
# Helper lemmas for the faithful Kaufman closing

These lemmas support the main closing proof by isolating:
1. Transporting the normalized Kaufman fiber projection to the original
   dot-difference set with the exact `4 * normalizationWidth * D` factor.
2. The upper bound on `rho = max delta transportedScale`.
-/

namespace Kakeya.Assouad

open scoped ENNReal
attribute [local instance] Classical.propDecidable

/-- Transport the normalized Kaufman fiber projection to the original
dot-difference set.

For every fiber point `f`, the original dot product equals
`4 * normalizationWidth * D * inner ℝ direction f`, where `D` is the
endpoint distance. This follows from `sourceDot_eq` and the direction
equation `b1 - b2 = D • direction`.
-/
lemma dot_diff_transport_inclusion
    {delta epsilon : ℝ}
    {input : WZ1Lemma8_13ResidualInput
        delta epsilon (wz1Lemma8_13FaithfulEta epsilon)}
    {hdelta : 0 < delta}
    {affine : WZ1Lemma8_13FaithfulViewpointAffineData input hdelta}
    {kaufman : WZ1Lemma8_13FaithfulKaufmanInputData affine}
    (direction : Point2)
    (hdirection : direction ∈ kaufman.radial.directions) :
    (fun x : ℝ =>
      (4 * wz1Lemma8_13FaithfulNormalizationWidth input *
        dist (kaufman.firstEndpoint direction)
          (kaufman.secondEndpoint direction)) * x) ''
      (inner ℝ direction ''
        (kaufmanFiber kaufman.finalH
          (kaufman.firstEndpoint direction)
          (kaufman.secondEndpoint direction) : Set Point2)) ⊆
    wz1DotDifferenceSet input.H ∩
      Metric.closedBall 0
        (4 * wz1Lemma8_13FaithfulNormalizationWidth input *
          dist (kaufman.firstEndpoint direction)
            (kaufman.secondEndpoint direction)) := by
  set b1 := kaufman.firstEndpoint direction with hb1_def
  set b2 := kaufman.secondEndpoint direction with hb2_def
  set D := dist b1 b2 with hD_def
  set normalizationWidth :=
    wz1Lemma8_13FaithfulNormalizationWidth input with hnw_def
  set transportedRadius := 4 * normalizationWidth * D with htr_def
  have hdir_unit : ‖direction‖ = 1 :=
    kaufman.radial.unit direction hdirection
  have hdir_eq :
      direction = (‖b1 - b2‖⁻¹ : ℝ) • (b1 - b2) :=
    kaufman.direction_eq direction hdirection
  have hD_eq : D = ‖b1 - b2‖ := by
    simp [hD_def, dist_eq_norm]
  have hD_pos : 0 < D := by
    have hlower : 1 / (4 * wz1Lemma8_13FaithfulAspect input) ≤ D :=
      kaufman.endpointDistance_lower direction hdirection
    have haspect_pos : 0 < wz1Lemma8_13FaithfulAspect input := by
      dsimp only [wz1Lemma8_13FaithfulAspect]
      exact zero_lt_one.trans_le (le_max_left _ _)
    have hpos : 0 < 1 / (4 * wz1Lemma8_13FaithfulAspect input) := by
      positivity
    linarith
  have h2 : ‖b1 - b2‖ * ‖b1 - b2‖⁻¹ = 1 := by
    have h3 : ‖b1 - b2‖ ≠ 0 := by
      exact hD_eq.symm ▸ hD_pos.ne'
    field_simp [h3]
  have hvector_eq : b1 - b2 = D • direction := by
    have h1 : ‖b1 - b2‖ = D := hD_eq.symm
    calc
      b1 - b2
        = ‖b1 - b2‖ • direction := by
          rw [hdir_eq, smul_smul, h2, one_smul]
      _ = D • direction := by rw [h1]
  intro y hy
  have h_exists1 : ∃ (x : ℝ), x ∈ (inner ℝ direction ''
        (kaufmanFiber kaufman.finalH b1 b2 : Set Point2)) ∧
      transportedRadius * x = y := by
    simpa [Set.mem_image] using hy
  rcases h_exists1 with ⟨x, hx, rfl⟩
  have h_exists2 : ∃ (f : Point2),
      f ∈ (kaufmanFiber kaufman.finalH b1 b2 : Set Point2) ∧
      inner ℝ direction f = x := by
    simpa [Set.mem_image] using hx
  rcases h_exists2 with ⟨f, hf, hx_eq⟩
  have hf_in_fiber : f ∈ kaufmanFiber kaufman.finalH b1 b2 := hf
  rcases Finset.mem_image.mp hf_in_fiber with
    ⟨finalEdge, hfinalEdge, hf_eq⟩
  have hfilter : finalEdge.2.1 = b1 ∧ finalEdge.2.2 = b2 :=
    (Finset.mem_filter.mp hfinalEdge).2
  have hfe1 : finalEdge.1 = f := by simpa using hf_eq
  have hfe21 : finalEdge.2.1 = b1 := hfilter.1
  have hfe22 : finalEdge.2.2 = b2 := hfilter.2
  have hfinalEdge_in_H : finalEdge ∈ kaufman.finalH :=
    (Finset.mem_filter.mp hfinalEdge).1
  rcases kaufman.sourceWitness finalEdge hfinalEdge_in_H with
    ⟨sourceEdge, hsourceEdge, hsourceViewpoint, hfinalEdge_eq⟩
  have htriple_eq :
      finalEdge =
        (wz1Lemma8_13FaithfulFMap input affine.normalizationWidth_pos sourceEdge.1,
          wz1Lemma8_13FaithfulGMap input affine.normalizationWidth_pos sourceEdge.2.1,
          wz1Lemma8_13FaithfulGMap input affine.normalizationWidth_pos sourceEdge.2.2) := by
    simpa [wz1Lemma8_13FaithfulTripleMap] using hfinalEdge_eq
  have h_f_map :
      wz1Lemma8_13FaithfulFMap input affine.normalizationWidth_pos
        sourceEdge.1 = f := by
    have h : finalEdge.1 = (wz1Lemma8_13FaithfulFMap input affine.normalizationWidth_pos sourceEdge.1) := by
      rw [htriple_eq]
    rw [hfe1] at h
    exact h.symm
  have h_b1_map :
      wz1Lemma8_13FaithfulGMap input affine.normalizationWidth_pos
        sourceEdge.2.1 = b1 := by
    have h : finalEdge.2.1 = (wz1Lemma8_13FaithfulGMap input affine.normalizationWidth_pos sourceEdge.2.1) := by
      rw [htriple_eq]
    rw [hfe21] at h
    exact h.symm
  have h_b2_map :
      wz1Lemma8_13FaithfulGMap input affine.normalizationWidth_pos
        sourceEdge.2.2 = b2 := by
    have h : finalEdge.2.2 = (wz1Lemma8_13FaithfulGMap input affine.normalizationWidth_pos sourceEdge.2.2) := by
      rw [htriple_eq]
    rw [hfe22] at h
    exact h.symm
  have h_dot_eq :
      inner ℝ sourceEdge.1 (sourceEdge.2.1 - sourceEdge.2.2) =
        4 * normalizationWidth *
          inner ℝ f (b1 - b2) := by
    have h := kaufman.sourceDot_eq sourceEdge hsourceEdge
    rw [h_f_map, h_b1_map, h_b2_map] at h
    exact h
  have h_inner_dir :
      inner ℝ f (b1 - b2) = D * inner ℝ f direction := by
    rw [hvector_eq, inner_smul_right]
  have h_x : inner ℝ f direction = x := by
    have hcomm : inner ℝ direction f = inner ℝ f direction :=
      (real_inner_comm direction f).symm
    exact hcomm.symm.trans hx_eq
  have h_original_dot :
      inner ℝ sourceEdge.1 (sourceEdge.2.1 - sourceEdge.2.2) =
        transportedRadius * x := by
    rw [h_dot_eq, h_inner_dir, h_x]
    simp [htr_def]
    ring
  have h_y_in_dotdiff :
      transportedRadius * x ∈ wz1DotDifferenceSet input.H := by
    rw [← h_original_dot]
    exact Finset.mem_image.mpr ⟨sourceEdge, hsourceEdge, rfl⟩
  have hf_in_finalF : f ∈ kaufman.finalF := by
    have hsup := kaufman.finalSupport finalEdge hfinalEdge_in_H
    have h : finalEdge.1 ∈ kaufman.finalF := hsup.1
    rw [hfe1.symm]
    exact h
  have hf_ball : ‖f‖ ≤ 1 := by
    simpa [dist_zero_right] using kaufman.finalF_ball f hf_in_finalF
  have h_abs_inner : |inner ℝ f direction| ≤ 1 := by
    calc
      |inner ℝ f direction| ≤ ‖f‖ * ‖direction‖ :=
        abs_real_inner_le_norm f direction
      _ = ‖f‖ * 1 := by rw [hdir_unit]
      _ ≤ 1 := by
        rw [mul_one]
        exact hf_ball
  have h_abs_x : |x| ≤ 1 := by
    rw [← h_x]
    exact h_abs_inner
  have htransportedRadius_pos : 0 < transportedRadius := by
    have hnorm_pos2 : 0 < normalizationWidth :=
      affine.normalizationWidth_pos
    positivity
  have h_y_in_ball :
      transportedRadius * x ∈ Metric.closedBall 0 transportedRadius := by
    simp only [Metric.mem_closedBall, dist_zero_right]
    have h : |transportedRadius * x| ≤ transportedRadius := by
      calc
        |transportedRadius * x|
          = transportedRadius * |x| := by
            rw [abs_mul]
            rw [abs_of_pos htransportedRadius_pos]
        _ ≤ transportedRadius * 1 := by gcongr
        _ = transportedRadius := by ring
    exact h
  exact ⟨h_y_in_dotdiff, h_y_in_ball⟩

/-- Upper bound on `rho = max delta transportedScale`.

The transported scale simplifies to `4 * D * width` after substituting
`s = width / T`. With `D ≤ 2` and `width ≤ 1/8`, this is at most 1.
-/
lemma closing_rho_upper
    {delta epsilon : ℝ}
    {input : WZ1Lemma8_13ResidualInput
        delta epsilon (wz1Lemma8_13FaithfulEta epsilon)}
    {hdelta : 0 < delta}
    {affine : WZ1Lemma8_13FaithfulViewpointAffineData input hdelta}
    {kaufman : WZ1Lemma8_13FaithfulKaufmanInputData affine}
    (direction : Point2)
    (hdirection : direction ∈ kaufman.radial.directions)
    (hdeltaOne : delta ≤ 1) :
    max delta
      (4 * wz1Lemma8_13FaithfulNormalizationWidth input *
        dist (kaufman.firstEndpoint direction)
          (kaufman.secondEndpoint direction) *
        wz1Lemma8_13FaithfulAngularScale input) ≤ 1 := by
  set b1 := kaufman.firstEndpoint direction with hb1_def
  set b2 := kaufman.secondEndpoint direction with hb2_def
  set D := dist b1 b2 with hD_def
  set normalizationWidth :=
    wz1Lemma8_13FaithfulNormalizationWidth input with hnw_def
  set angularScale := wz1Lemma8_13FaithfulAngularScale input with has_def
  set width := input.width with hw_def
  have hD_upper : D ≤ 2 :=
    kaufman.endpointDistance_upper direction hdirection
  have hwidth_eighth : width ≤ 1 / 8 :=
    affine.width_le_eighth
  have hwidth_pos : 0 < width := input.width_pos
  have hscale_identity :
      4 * normalizationWidth * D * angularScale = 4 * D * width :=
    wz1Lemma8_13_transport_scale_identity
      affine.normalizationWidth_pos
      (by simp [has_def, hw_def, hnw_def,
        wz1Lemma8_13FaithfulAngularScale])
  have hscale_upper :
      4 * normalizationWidth * D * angularScale ≤ 1 := by
    rw [hscale_identity]
    have h : 4 * D * width ≤ 1 := by
      calc
        4 * D * width
          ≤ 4 * (2 : ℝ) * width := by gcongr
        _ ≤ 4 * (2 : ℝ) * (1 / 8) := by gcongr
        _ = 1 := by norm_num
    exact h
  exact max_le hdeltaOne hscale_upper

/-- Long-radius condition for the faithful Kaufman closing.

Shows `delta^(-eta) * rho ≤ 2 * transportedRadius`, where
`rho = max delta transportedScale`. The stronger bound
`delta^(-eta) * rho ≤ transportedRadius` follows from the endpoint
window and the transport-radius conditions.
-/
lemma closing_long_radius
    {delta epsilon : ℝ}
    {input : WZ1Lemma8_13ResidualInput
        delta epsilon (wz1Lemma8_13FaithfulEta epsilon)}
    {hdelta : 0 < delta}
    {affine : WZ1Lemma8_13FaithfulViewpointAffineData input hdelta}
    {kaufman : WZ1Lemma8_13FaithfulKaufmanInputData affine}
    (direction : Point2)
    (hdirection : direction ∈ kaufman.radial.directions)
    (hdeltaOne : delta ≤ 1)
    (hepsilon : 0 < epsilon)
    (hepsilon_lt_one : epsilon < 1) :
    Real.rpow delta (-wz1Lemma8_13FaithfulEta epsilon) *
      max delta
        (4 * wz1Lemma8_13FaithfulNormalizationWidth input *
          dist (kaufman.firstEndpoint direction)
            (kaufman.secondEndpoint direction) *
          wz1Lemma8_13FaithfulAngularScale input) ≤
    2 * (4 * wz1Lemma8_13FaithfulNormalizationWidth input *
      dist (kaufman.firstEndpoint direction)
        (kaufman.secondEndpoint direction)) := by
  set b1 := kaufman.firstEndpoint direction with hb1_def
  set b2 := kaufman.secondEndpoint direction with hb2_def
  set D := dist b1 b2 with hD_def
  set normalizationWidth :=
    wz1Lemma8_13FaithfulNormalizationWidth input with hnw_def
  set angularScale := wz1Lemma8_13FaithfulAngularScale input with has_def
  set aspect := wz1Lemma8_13FaithfulAspect input with hasp_def
  let epsilonOne := wz1Lemma8_13FaithfulEpsilonOne epsilon
  let eta := wz1Lemma8_13FaithfulEta epsilon
  set radius := 4 * normalizationWidth * D with hr_def
  set rho₀ := radius * angularScale with hr0_def
  set rho := max delta rho₀ with hrho_def
  have hepsilonOne_pos : 0 < epsilonOne := by
    dsimp only [epsilonOne, wz1Lemma8_13FaithfulEpsilonOne]
    positivity
  have hepsilonOne_upper : epsilonOne < 1 := by
    dsimp only [epsilonOne, wz1Lemma8_13FaithfulEpsilonOne]
    nlinarith [sq_pos_of_pos hepsilon]
  have heta_pos : 0 < eta := by
    dsimp only [eta, wz1Lemma8_13FaithfulEta]
    positivity
  have heta_lt_epsilon : eta < epsilon := by
    dsimp only [eta, wz1Lemma8_13FaithfulEta]
    nlinarith [sq_pos_of_pos hepsilon]
  have heta_lt_epsilonOne : eta < epsilonOne :=
    wz1Lemma8_13_eta_lt_epsilonOne hepsilon
  have hangularScale_pos : 0 < angularScale :=
    affine.angularScale_pos
  have hangularScale_upper :
      angularScale ≤ Real.rpow delta epsilon := by
    have h := wz1Lemma8_13_angularScale_lt_rpow input hdelta
    rw [has_def]
    exact h.le
  have hnormalization_lower :
      Real.rpow delta (1 - epsilonOne) ≤ normalizationWidth :=
    affine.normalizationWidth_lower
  have haspect_eq : aspect = max 1 normalizationWidth := by
    dsimp only [aspect, wz1Lemma8_13FaithfulAspect]
  have hendpoint_lower : 1 / (4 * aspect) ≤ D :=
    kaufman.endpointDistance_lower direction hdirection
  have hradius_lower :
      Real.rpow delta (1 - epsilonOne) ≤ radius :=
    wz1Lemma8_13_transport_radius_lower
      hdelta hdeltaOne hepsilonOne_pos hepsilonOne_upper
      affine.normalizationWidth_pos haspect_eq
      hnormalization_lower hendpoint_lower
  have hD_pos : 0 < D := by
    have haspect_pos : 0 < aspect := by
      dsimp only [aspect, wz1Lemma8_13FaithfulAspect]
      exact zero_lt_one.trans_le (le_max_left _ _)
    have hpos : 0 < 1 / (4 * aspect) := by positivity
    linarith
  have hradius_pos : 0 < radius := by
    dsimp only [radius]
    have hnorm_pos : 0 < normalizationWidth := affine.normalizationWidth_pos
    exact mul_pos (mul_pos (by norm_num) hnorm_pos) hD_pos
  have hrho₀_eq : rho₀ = radius * angularScale := by
    simp [hr0_def, has_def, hr_def]
  have h_conditions :
      Real.rpow delta (-eta) * rho₀ ≤ radius ∧
      Real.rpow delta (-eta) * delta ≤ radius :=
    wz1Lemma8_13_transport_radius_conditions
      hdelta hdeltaOne heta_pos heta_lt_epsilon
      heta_lt_epsilonOne hepsilonOne_upper
      hangularScale_pos hangularScale_upper
      hradius_pos hradius_lower hrho₀_eq
  have h_main : Real.rpow delta (-eta) * rho ≤ radius := by
    have h_nonneg : 0 ≤ Real.rpow delta (-eta) := Real.rpow_nonneg hdelta.le _
    rw [hrho_def]
    have h : Real.rpow delta (-eta) * max delta rho₀ =
        max (Real.rpow delta (-eta) * delta)
          (Real.rpow delta (-eta) * rho₀) := by
      rw [mul_max_of_nonneg _ _ h_nonneg]
    rw [h]
    exact max_le h_conditions.2 h_conditions.1
  have h_final : Real.rpow delta (-eta) * rho ≤ 2 * radius := by
    calc
      Real.rpow delta (-eta) * rho ≤ radius := h_main
      _ ≤ 2 * radius := by
        have h : 0 ≤ radius := hradius_pos.le
        linarith
  exact h_final

end Kakeya.Assouad
