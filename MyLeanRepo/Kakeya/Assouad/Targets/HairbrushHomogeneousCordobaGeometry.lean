import MyLeanRepo.Kakeya.Assouad.Subunit.HairbrushSelfContainedLeaves
import MyLeanRepo.Kakeya.Assouad.Targets.HairbrushOrientedFamilyTransfer
import MyLeanRepo.Kakeya.Assouad.Targets.HairbrushAsymmetricFixedStemCordoba
import MyLeanRepo.Kakeya.Assouad.Targets.HairbrushCordobaDenominatorAbsorption

/-!
# Homogeneous fixed-stem Córdoba geometry assembly

Combine orientation transfer, far-shading density retention, the validated
fixed-stem Córdoba estimate, and denominator absorption into the exact
radius-weighted B.27 lower bound.
-/

open MeasureTheory Metric Set Finset Real
open scoped Classical

namespace Kakeya.Assouad

theorem hairbrush_homogeneous_cordoba_geometry :
    HairbrushHomogeneousCordobaGeometryStatement := by
  intro hTransfer hCordoba hAbsorb
  intro katzExponent cordobaLoss farFraction hkatz_nonneg hkatz_lt hfarFrac_pos

  rcases hAbsorb katzExponent cordobaLoss farFraction (1 / 4 : ℝ)
      hkatz_nonneg hkatz_lt hfarFrac_pos (by norm_num)
    with ⟨delta₀, hdelta₀_pos, hdelta₀_le, hAbsorb_main⟩

  refine ⟨delta₀, hdelta₀_pos, hdelta₀_le, fun δ hδ hδ_le => ?_⟩

  intro katzTaoConstant hkatzTao_nonneg hkatzTao_bound
  intro F Y hED hKT
  intro zeta familyLoss bandLoss angleScale
  intro H Z hH_subF hZ_subY
  intro hairDensity hhairDensity_ne_top
  intro twoEnds
  intro B ZB hB_subFamily hZB_eq
  intro stem band radii far

  let radius := twoEnds.radius
  let sigma := band.sigma
  let farRadius := radii.farRadius
  let oriented := band.oriented
  let density : ENNReal :=
      (1 / 4 : ENNReal) * ENNReal.ofReal (Real.rpow radius zeta) * hairDensity

  have hδ1 : δ ≤ 1 := by linarith [hδ_le, hdelta₀_le]
  have hδ1000 : δ ≤ 1 / 1000 := by linarith [hδ_le, hdelta₀_le]
  have hradius_pos : 0 < radius := by linarith [twoEnds.delta_le_radius, hδ]
  have hsigma_pos : 0 < sigma := by
    have h1 : 0 < farRadius := radii.farRadius_pos
    have h2 : farRadius = farFraction * sigma * radius := radii.far_radius_eq
    rw [h2] at h1
    have h3 : farFraction * sigma * radius = farFraction * radius * sigma := by ring
    rw [h3] at h1
    have h4 : 0 < farFraction * radius := mul_pos hfarFrac_pos hradius_pos
    exact (mul_pos_iff_of_pos_left h4).mp h1
  have hsigma1 : sigma ≤ 1 := band.sigma_le_one

  have hsource_subF : band.source ⊆ F := by
    calc
      band.source ⊆ B := band.source_subset
      _ ⊆ twoEnds.family := hB_subFamily
      _ ⊆ H := twoEnds.family_subset
      _ ⊆ F := hH_subF

  have h_oriented_eq : oriented = band.source.image (orientTube stem) :=
    band.oriented_eq

  have hTransfer_all :=
    hTransfer δ katzTaoConstant hδ hδ1 F band.source hED hsource_subF
      band.source_nonempty hKT stem
  rcases hTransfer_all with ⟨h_img_nonempty, _henncard_eq, h_img_ED, h_img_KT⟩

  have horiented_nonempty : oriented.Nonempty := by
    rw [h_oriented_eq]
    exact h_img_nonempty
  have hED_oriented : oriented.IsEssentiallyDistinct := by
    rw [h_oriented_eq]
    exact h_img_ED
  have hKT_oriented : Kakeya.KatzTaoConvexWolffBound oriented katzTaoConstant := by
    rw [h_oriented_eq]
    exact h_img_KT

  have hdensity_per : ∀ U' ∈ oriented,
      density * U'.volume ≤ volume (far.shading.carrier U') := by
    intro U' hU'
    have h_img : U' ∈ band.source.image (orientTube stem) := by
      rw [← h_oriented_eq]
      exact hU'
    rcases Finset.mem_image.mp h_img with ⟨U, hU, rfl⟩
    let U' := orientTube stem U
    have hcar_shading : band.shading.carrier U' = ZB.carrier U :=
      band.shading_carrier U hU
    have hcar_ZB : ZB.carrier U = twoEnds.shading.carrier U :=
      hZB_eq U (band.source_subset hU)
    have hvol : U'.volume = U.volume := orientTube_volume stem U
    have hU_in_family : U ∈ twoEnds.family :=
      hB_subFamily (band.source_subset hU)
    have h1 : ENNReal.ofReal (Real.rpow radius zeta) * hairDensity * U.volume ≤
          volume (twoEnds.shading.carrier U) :=
      twoEnds.per_hair_mass U hU_in_family
    have hU'_in_oriented : U' ∈ oriented := by
      rw [h_oriented_eq]
      exact Finset.mem_image.mpr ⟨U, hU, rfl⟩
    have h2 : (1 / 4 : ENNReal) * volume (band.shading.carrier U') ≤
          volume (far.shading.carrier U') :=
      far.mass_lower U' hU'_in_oriented
    calc
      density * U'.volume
        = (1 / 4 : ENNReal) *
            (ENNReal.ofReal (Real.rpow radius zeta) * hairDensity * U.volume) := by
              simp [density, hvol] <;> ring
      _ ≤ (1 / 4 : ENNReal) * volume (twoEnds.shading.carrier U) := by
            gcongr
      _ = (1 / 4 : ENNReal) * volume (band.shading.carrier U') := by
            rw [← hcar_ZB, ← hcar_shading]
      _ ≤ volume (far.shading.carrier U') := h2

  have hFar : HairbrushFarFromStem (farRadius := farRadius) far.shading stem := by
    intro U' hU'
    have h_eq : far.shading.carrier U' =
          band.shading.carrier U' ∩
            {x | farRadius ≤ ‖perpProj stem.direction (x - stem.base)‖} :=
      far.carrier_eq U' hU'
    rw [h_eq]
    exact Set.inter_subset_right

  have hdensity_ne_top : density ≠ ⊤ := by
    have h1 : (1 / 4 : ENNReal) ≠ ⊤ := by simp
    have h2 : ENNReal.ofReal (Real.rpow radius zeta) ≠ ⊤ :=
      ENNReal.ofReal_ne_top
    have h3 : ((1 / 4 : ENNReal) *
        ENNReal.ofReal (Real.rpow radius zeta)) ≠ ⊤ :=
      ENNReal.mul_ne_top h1 h2
    have h4 : density =
        ((1 / 4 : ENNReal) * ENNReal.ofReal (Real.rpow radius zeta)) *
          hairDensity := by
      simp [density]
    rw [h4]
    exact ENNReal.mul_ne_top h3 hhairDensity_ne_top

  have hV_lower : ENNReal.ofReal (δ ^ 2) ≤ Kakeya.deltaTubeVolume δ :=
    canonical_volume_lower hδ

  let D := hairbrushFixedStemCordobaDenominator δ katzTaoConstant
  let M : ENNReal := ENNReal.ofReal (100 * (sigma / farRadius + 1))

  have hCordoba_result :
      density ^ 2 * oriented.enncard * Kakeya.deltaTubeVolume δ / (D * M) ≤
        volume far.shading.union :=
    hCordoba δ sigma farRadius katzTaoConstant hδ hδ1000 hsigma_pos hsigma1
      radii.farRadius_pos hkatzTao_nonneg oriented far.shading
      horiented_nonempty hED_oriented hKT_oriented stem
      band.oriented_angle band.oriented_intersects hFar
      density hdensity_ne_top hdensity_per hV_lower

  have hAbsorb_result :
      Kakeya.realRpowENN δ cordobaLoss * ENNReal.ofReal radius ≤
        ENNReal.ofReal (1 / 4 : ℝ) ^ 2 * (D * M)⁻¹ :=
    hAbsorb_main δ hδ hδ_le katzTaoConstant hkatzTao_nonneg hkatzTao_bound
      sigma radius farRadius hsigma_pos
      (by linarith [twoEnds.delta_le_radius])
      (by linarith [twoEnds.radius_le_two])
      radii.far_radius_eq

  have h_alg1 : density ^ 2 =
        ENNReal.ofReal (1 / 4 : ℝ) ^ 2 *
          (ENNReal.ofReal (Real.rpow radius zeta) * hairDensity) ^ 2 := by
    simp [density, mul_pow] <;> ring

  let X : ENNReal :=
    (ENNReal.ofReal (Real.rpow radius zeta) * hairDensity) ^ 2 *
      oriented.enncard * Kakeya.deltaTubeVolume δ

  have h_main1 :
      Kakeya.realRpowENN δ cordobaLoss * ENNReal.ofReal radius * X ≤
        volume far.shading.union := by
    have h3 :
        Kakeya.realRpowENN δ cordobaLoss * ENNReal.ofReal radius * X ≤
          ENNReal.ofReal (1 / 4 : ℝ) ^ 2 * (D * M)⁻¹ * X := by
      gcongr
    have h4 : ENNReal.ofReal (1 / 4 : ℝ) ^ 2 * (D * M)⁻¹ * X =
          density ^ 2 * oriented.enncard * Kakeya.deltaTubeVolume δ /
            (D * M) := by
      simp [X, h_alg1, div_eq_mul_inv] <;> ring
    rw [h4] at h3
    exact le_trans h3 hCordoba_result

  let Y2 : ENNReal :=
    (ENNReal.ofReal (Real.rpow radius zeta) * hairDensity) ^ 2 *
      oriented.enncard * ENNReal.ofReal (δ ^ 2)

  have h5 : Y2 ≤ X := by
    dsimp only [Y2, X]
    gcongr

  have h_main2 :
      Kakeya.realRpowENN δ cordobaLoss * ENNReal.ofReal radius * Y2 ≤
        volume far.shading.union := by
    have h6 :
        Kakeya.realRpowENN δ cordobaLoss * ENNReal.ofReal radius * Y2 ≤
          Kakeya.realRpowENN δ cordobaLoss * ENNReal.ofReal radius * X := by
      gcongr
    exact le_trans h6 h_main1

  have h_union_sub : far.shading.union ⊆ Y.union := by
    intro x hx
    rcases hx with ⟨U', hU', hxU'⟩
    have h_img : U' ∈ band.source.image (orientTube stem) := by
      rw [← h_oriented_eq]
      exact hU'
    rcases Finset.mem_image.mp h_img with ⟨U, hU, rfl⟩
    let U' := orientTube stem U
    have hU'_in_oriented : U' ∈ oriented := by
      rw [h_oriented_eq]
      exact Finset.mem_image.mpr ⟨U, hU, rfl⟩
    have h2 : far.shading.carrier U' ⊆ band.shading.carrier U' := by
      rw [far.carrier_eq U' hU'_in_oriented]
      exact Set.inter_subset_left
    have h3 : x ∈ band.shading.carrier U' := h2 hxU'
    have h4 : band.shading.carrier U' = ZB.carrier U :=
      band.shading_carrier U hU
    have h5 : x ∈ ZB.carrier U := by
      rw [← h4]
      exact h3
    have h6 : ZB.carrier U = twoEnds.shading.carrier U :=
      hZB_eq U (band.source_subset hU)
    have h7 : x ∈ twoEnds.shading.carrier U := by
      rw [← h6]
      exact h5
    have hU_in_H : U ∈ H :=
      twoEnds.family_subset (hB_subFamily (band.source_subset hU))
    have h8 : twoEnds.shading.carrier U ⊆ Z.carrier U :=
      twoEnds.shading_subset U (hB_subFamily (band.source_subset hU))
    have h9 : x ∈ Z.carrier U := h8 h7
    have h10 : Z.carrier U ⊆ Y.carrier U := hZ_subY U hU_in_H
    have h11 : x ∈ Y.carrier U := h10 h9
    have hU_in_F : U ∈ F := hH_subF hU_in_H
    exact ⟨U, hU_in_F, h11⟩

  have h_final : volume far.shading.union ≤ volume Y.union :=
    measure_mono h_union_sub

  have h_goal :
      Kakeya.realRpowENN δ cordobaLoss * ENNReal.ofReal radius *
          (ENNReal.ofReal (Real.rpow radius zeta) * hairDensity) ^ 2 *
          oriented.enncard * ENNReal.ofReal (δ ^ 2) ≤
        volume Y.union := by
    have h13 :
        Kakeya.realRpowENN δ cordobaLoss * ENNReal.ofReal radius * Y2 =
          Kakeya.realRpowENN δ cordobaLoss * ENNReal.ofReal radius *
            (ENNReal.ofReal (Real.rpow radius zeta) * hairDensity) ^ 2 *
            oriented.enncard * ENNReal.ofReal (δ ^ 2) := by
      simp [Y2] <;> ring
    rw [← h13]
    exact le_trans h_main2 h_final

  exact h_goal

end Kakeya.Assouad
