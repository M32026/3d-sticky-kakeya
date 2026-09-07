import MyLeanRepo.Kakeya.Assouad.Subunit.HairbrushSelfContainedLeaves
import MyLeanRepo.Kakeya.Assouad.Targets.HairbrushAsymmetricFarShading
import MyLeanRepo.Kakeya.Assouad.Subunit.OrientationInfrastructure

/-!
# Homogeneous oriented far-shading adapter

Transport the absolute homogeneous two-ends estimate through an oriented
angle band, then invoke the validated core-independent equation-(19)
far-shading theorem.

This is an adapter only: do not select parameters, a stem, or angle band.
-/

open MeasureTheory Metric Set Finset Real

attribute [local instance] Classical.propDecidable

namespace Kakeya.Assouad

theorem hairbrush_homogeneous_oriented_far_shading :
    HairbrushHomogeneousOrientedFarShadingStatement := by
  intro h_asymm δ zeta familyLoss bandLoss angleScale hδ
        H Z h_ed hairDensity twoEnds
        B ZB hB_sub hZB_eq stem band farFraction radii

  -- Step 1: Prove 0 ≤ band.sigma from source angle nonnegativity
  have hsigma_nonneg : 0 ≤ band.sigma := by
    rcases band.source_nonempty with ⟨U, hU⟩
    have h_angle : hairbrushAcuteAngle stem U ≤ 2 * band.sigma :=
      (band.source_angle U hU).2
    have h1 : 0 ≤ Real.arccos (inner ℝ stem.direction U.direction) :=
      Real.arccos_nonneg _
    have h2 : Real.arccos (inner ℝ stem.direction U.direction) ≤ Real.pi :=
      Real.arccos_le_pi _
    have h3 : 0 ≤ Real.pi - Real.arccos (inner ℝ stem.direction U.direction) := by linarith
    have h4 : 0 ≤ hairbrushAcuteAngle stem U := by
      have h5 : hairbrushAcuteAngle stem U =
          min (Real.arccos (inner ℝ stem.direction U.direction))
            (Real.pi - Real.arccos (inner ℝ stem.direction U.direction)) := by rfl
      rw [h5]
      exact le_min h1 h3
    linarith

  -- Step 2: Prove 0 < band.sigma (sigma=0 would force farRadius=0)
  have hsigma_pos : 0 < band.sigma := by
    by_cases h : band.sigma = 0
    · have h_far_zero : radii.farRadius = 0 := by
        rw [radii.far_radius_eq, h] <;> ring
      linarith [radii.farRadius_pos]
    · exact lt_of_le_of_ne hsigma_nonneg (Ne.symm h)

  -- Step 3: Angle condition: oriented angleBetween equals acuteAngle (≤ π/2)
  have h_angles : ∀ (U : Kakeya.DeltaTube δ), U ∈ band.oriented →
      band.sigma ≤ hairbrushAcuteAngle stem U ∧
      hairbrushAcuteAngle stem U ≤ 2 * band.sigma := by
    intro U hU
    have hU' : U ∈ Finset.image (orientTube stem) band.source := by
      rwa [band.oriented_eq] at hU
    rcases Finset.mem_image.mp hU' with ⟨V, hV, rfl⟩
    have h_le_pi2 : angleBetween stem (orientTube stem V) ≤ Real.pi / 2 :=
      orientTube_angle_le_pi2 stem V
    have h_eq : hairbrushAcuteAngle stem (orientTube stem V) =
        angleBetween stem (orientTube stem V) :=
      acuteAngle_eq_angleBetween_le_pi2 stem (orientTube stem V) h_le_pi2
    rw [h_eq]
    exact band.oriented_angle (orientTube stem V) (by
      rw [band.oriented_eq]
      exact Finset.mem_image_of_mem _ hV)

  -- Step 4: Intersection condition from band data
  have h_inter : ∀ (U : Kakeya.DeltaTube δ), U ∈ band.oriented →
      (stem.carrier ∩ U.carrier).Nonempty :=
    band.oriented_intersects

  -- Step 5: Near-ball mass transfers from twoEnds through ZB to band shading
  have h_near_bound : ∀ (U : Kakeya.DeltaTube δ), U ∈ band.oriented →
      ∀ (x : Point3),
        Metric.infDist x (Kakeya.unitSegment U.base U.direction) ≤ δ →
        volume (band.shading.carrier U ∩ Metric.ball x radii.nearRadius) ≤
          (1 / 4 : ENNReal) * volume (band.shading.carrier U) := by
    intro U hU x _
    have hU' : U ∈ Finset.image (orientTube stem) band.source := by
      rwa [band.oriented_eq] at hU
    rcases Finset.mem_image.mp hU' with ⟨V, hV, rfl⟩
    have hV_B : V ∈ B := band.source_subset hV
    have h_carrier_eq : band.shading.carrier (orientTube stem V) =
        twoEnds.shading.carrier V := by
      have h1 : band.shading.carrier (orientTube stem V) = ZB.carrier V :=
        band.shading_carrier V hV
      have h2 : ZB.carrier V = twoEnds.shading.carrier V := hZB_eq V hV_B
      rw [h1, h2]
    have hV_family : V ∈ twoEnds.family := hB_sub hV_B
    have h_mass : volume (twoEnds.shading.carrier V ∩ Metric.ball x radii.nearRadius) ≤
        (1 / 4 : ENNReal) * volume (twoEnds.shading.carrier V) :=
      radii.near_ball_mass V hV_family x
    rw [h_carrier_eq]
    exact h_mass

  -- Apply the validated asymmetric far-shading theorem
  exact h_asymm δ band.sigma radii.farRadius radii.nearRadius
    hδ hsigma_pos band.sigma_le_one
    radii.farRadius_pos radii.nearRadius_pos
    radii.geometric_radius
    band.oriented band.shading stem
    h_angles h_inter h_near_bound

end Kakeya.Assouad
