import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma49EndpointConstruction
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma8_13FaithfulAffineTransport
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma8_13FaithfulStatements

/-!
# Endpoint construction for faithful Lemma 8.13 Kaufman input

Given radial projection data over `finalG₁` and the faithful affine package,
construct the two endpoint functions and prove the distance bounds.
-/

namespace Kakeya.Assouad

noncomputable section

/-- Construct endpoint functions from radial projection data and the faithful
affine package, with all required membership, direction, and distance properties. -/
lemma wz1Lemma8_13_faithful_endpoint_construction
    {delta epsilon : ℝ}
    {input : WZ1Lemma8_13ResidualInput delta epsilon (wz1Lemma8_13FaithfulEta epsilon)}
    {hdelta : 0 < delta}
    (affine : WZ1Lemma8_13FaithfulViewpointAffineData input hdelta)
    {finalG₁ : DiscreteSet 2}
    {angularScale constant : ℝ}
    (radial : WZ1Lemma49RadialProjectionData finalG₁ affine.normalizedViewpoint angularScale constant)
    (hfinalG₁_subset : finalG₁ ⊆ affine.normalizedG₁) :
    ∃ (firstEndpoint : Point2 → Point2) (secondEndpoint : Point2 → Point2),
      (∀ direction ∈ radial.directions, firstEndpoint direction ∈ finalG₁) ∧
      (∀ direction, secondEndpoint direction = affine.normalizedViewpoint) ∧
      (∀ direction ∈ radial.directions, secondEndpoint direction ∈ affine.normalizedG₂) ∧
      (∀ direction ∈ radial.directions,
        direction =
          (‖firstEndpoint direction - secondEndpoint direction‖⁻¹ : ℝ) •
          (firstEndpoint direction - secondEndpoint direction)) ∧
      (∀ direction ∈ radial.directions,
        1 / (4 * wz1Lemma8_13FaithfulAspect input) ≤
          dist (firstEndpoint direction) (secondEndpoint direction)) ∧
      (∀ direction ∈ radial.directions,
        dist (firstEndpoint direction) (secondEndpoint direction) ≤ 2) := by
  let firstEndpoint : Point2 → Point2 :=
    wz1Lemma49_firstEndpoint affine.normalizedViewpoint finalG₁
  let secondEndpoint : Point2 → Point2 :=
    wz1Lemma49_secondEndpoint affine.normalizedViewpoint
  have hsource_image :
      radial.directions =
        finalG₁.image (wz1Lemma49RadialDirection affine.normalizedViewpoint) :=
    radial.source_image
  have h1 : ∀ direction ∈ radial.directions, firstEndpoint direction ∈ finalG₁ := by
    intro direction hdirection
    rw [hsource_image] at hdirection
    exact wz1Lemma49_firstEndpoint_mem affine.normalizedViewpoint finalG₁ direction hdirection
  have h2 : ∀ direction, secondEndpoint direction = affine.normalizedViewpoint := by
    intro direction
    rfl
  have h3 : ∀ direction ∈ radial.directions, secondEndpoint direction ∈ affine.normalizedG₂ := by
    intro direction _
    simpa [secondEndpoint, wz1Lemma49_secondEndpoint] using affine.normalizedViewpoint_mem
  have h4 : ∀ direction ∈ radial.directions,
      direction =
        (‖firstEndpoint direction - secondEndpoint direction‖⁻¹ : ℝ) •
        (firstEndpoint direction - secondEndpoint direction) := by
    intro direction hdirection
    rw [hsource_image] at hdirection
    exact wz1Lemma49_direction_eq affine.normalizedViewpoint finalG₁ direction hdirection
  have h5 : ∀ direction ∈ radial.directions,
      1 / (4 * wz1Lemma8_13FaithfulAspect input) ≤
        dist (firstEndpoint direction) (secondEndpoint direction) := by
    intro direction hdirection
    let p : Point2 := firstEndpoint direction
    have hp_in_finalG₁ : p ∈ finalG₁ := h1 direction hdirection
    have hp_in_normalizedG₁ : p ∈ affine.normalizedG₁ := hfinalG₁_subset hp_in_finalG₁
    rw [affine.normalizedG₁_eq] at hp_in_normalizedG₁
    rcases Finset.mem_image.mp hp_in_normalizedG₁ with ⟨q, hq_sourceG₁, hq_eq⟩
    have hq_selected : q ∈ affine.separatedSource.selected :=
      affine.sourceG₁_subset hq_sourceG₁
    have hq_viewpoint_source : q ∈ affine.viewpoint.source :=
      affine.separatedSource.selected_subset hq_selected
    have hlower :
        1 / (4 * wz1Lemma8_13FaithfulAspect input) ≤
          dist (wz1Lemma8_13FaithfulGMap input affine.normalizationWidth_pos q)
            (wz1Lemma8_13FaithfulGMap input affine.normalizationWidth_pos affine.viewpoint.viewpoint) :=
      wz1Lemma8_13FaithfulGMap_endpoint_distance_lower
        input affine.normalizationWidth_pos affine.viewpoint hq_viewpoint_source
    have hfirst_eq :
        wz1Lemma8_13FaithfulGMap input affine.normalizationWidth_pos q = p := hq_eq
    have hsecond_eq :
        wz1Lemma8_13FaithfulGMap input affine.normalizationWidth_pos affine.viewpoint.viewpoint =
          affine.normalizedViewpoint := affine.normalizedViewpoint_eq.symm
    rw [hfirst_eq, hsecond_eq] at hlower
    simpa [secondEndpoint, wz1Lemma49_secondEndpoint] using hlower
  have h6 : ∀ direction ∈ radial.directions,
      dist (firstEndpoint direction) (secondEndpoint direction) ≤ 2 := by
    intro direction hdirection
    let p : Point2 := firstEndpoint direction
    let v : Point2 := secondEndpoint direction
    have hp_in_finalG₁ : p ∈ finalG₁ := h1 direction hdirection
    have hp_in_normalizedG₁ : p ∈ affine.normalizedG₁ := hfinalG₁_subset hp_in_finalG₁
    have hp_ball : dist p 0 ≤ 1 := affine.normalizedG₁_ball p hp_in_normalizedG₁
    have hv_ball : dist v 0 ≤ 1 := by
      have hv_eq : v = affine.normalizedViewpoint := by
        simp [v, secondEndpoint, wz1Lemma49_secondEndpoint]
      rw [hv_eq]
      exact affine.normalizedG₂_ball affine.normalizedViewpoint affine.normalizedViewpoint_mem
    have hnorm_p : ‖p‖ ≤ 1 := by simpa [dist_zero_right] using hp_ball
    have hnorm_v : ‖v‖ ≤ 1 := by simpa [dist_zero_right] using hv_ball
    calc
      dist p v = ‖p - v‖ := by rw [dist_eq_norm]
      _ ≤ ‖p‖ + ‖v‖ := norm_sub_le _ _
      _ ≤ 1 + 1 := by linarith
      _ = 2 := by norm_num
  exact ⟨firstEndpoint, secondEndpoint, h1, h2, h3, h4, h5, h6⟩

end

end Kakeya.Assouad
