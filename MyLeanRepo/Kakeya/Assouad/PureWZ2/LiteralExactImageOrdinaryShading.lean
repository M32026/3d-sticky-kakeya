import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12RescalingProducer
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperLiteralUnitRescalingVolume

/-!
# Exact literal images as an ordinary shading

The Section 6 target shading is a cubical saturation of the literal affine
images.  Before saturation, those exact images already form a measurable
ordinary shading on the public recentered family in the Assouad-to-literal
certificate.  This is the pure-model witness needed by Node 2's critical
volume floor.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

namespace WZ2PaperAssouadToLiteralRescalingCertificate

noncomputable def literalExactCroppedImageShading
    {delta rho : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily delta}
    {anchor : Kakeya.DeltaTube rho}
    {hrho : 0 < rho}
    {normalization : WZ2PaperAssouadUnitRescalingData anchor}
    {literal :
      WZ2PaperLiteralUnitRescaledFamilyData
        sourceFamily anchor hrho}
    {jacobianConstant : ENNReal}
    (certificate :
      WZ2PaperAssouadToLiteralRescalingCertificate
        hrho normalization literal jacobianConstant)
    (sourceShading : WZ1PaperTubeShading sourceFamily)
    (image_subset_public :
      ∀ publicIndex,
        wz2PaperLiteralUnitRescalingMap anchor hrho ''
            sourceShading.carrier
              (literal.sourceIndex
                (certificate.section6Index.symm publicIndex)) ⊆
          (certificate.publicFamily.tube publicIndex).carrier) :
    Kakeya.Streamlined.TubeShading certificate.publicFamily where
  carrier publicIndex :=
    wz2PaperLiteralUnitRescalingMap anchor hrho ''
      sourceShading.carrier
        (literal.sourceIndex
          (certificate.section6Index.symm publicIndex))
  measurable_carrier publicIndex := by
    let equivalence :=
      wz2PaperLiteralUnitRescalingAffineEquiv anchor hrho
    let measurableEquivalence : Point3 ≃ᵐ Point3 :=
      {
        toFun := equivalence
        invFun := equivalence.symm
        left_inv := equivalence.left_inv
        right_inv := equivalence.right_inv
        measurable_toFun :=
          equivalence.continuous_of_finiteDimensional.measurable
        measurable_invFun :=
          equivalence.symm.continuous_of_finiteDimensional.measurable
      }
    have hmeasurable :=
      (measurableEquivalence.measurableSet_image).mpr
        (sourceShading.measurable_carrier
          (literal.sourceIndex
            (certificate.section6Index.symm publicIndex)))
    have hmap :
        (measurableEquivalence :
            Point3 → Point3) =
          wz2PaperLiteralUnitRescalingMap anchor hrho := by
      funext point
      exact
        wz2PaperLiteralUnitRescalingAffineEquiv_apply
          anchor hrho point
    rwa [hmap] at hmeasurable
  subset_body := image_subset_public

theorem literalExactCroppedImageShading_mass
    {delta rho : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily delta}
    {anchor : Kakeya.DeltaTube rho}
    {hrho : 0 < rho}
    {normalization : WZ2PaperAssouadUnitRescalingData anchor}
    {literal :
      WZ2PaperLiteralUnitRescaledFamilyData
        sourceFamily anchor hrho}
    {jacobianConstant : ENNReal}
    (certificate :
      WZ2PaperAssouadToLiteralRescalingCertificate
        hrho normalization literal jacobianConstant)
    (sourceShading : WZ1PaperTubeShading sourceFamily)
    (image_subset_public :
      ∀ publicIndex,
        wz2PaperLiteralUnitRescalingMap anchor hrho ''
            sourceShading.carrier
              (literal.sourceIndex
                (certificate.section6Index.symm publicIndex)) ⊆
          (certificate.publicFamily.tube publicIndex).carrier) :
    (certificate.literalExactCroppedImageShading
        sourceShading image_subset_public).mass =
      (ENNReal.ofReal ((1 / 100 : ℝ) ^ 3) *
          ENNReal.ofReal ((1 / rho : ℝ) ^ 2)) *
        sourceShading.mass := by
  let sourceEquiv :
      Fin certificate.publicFamily.card ≃ Fin sourceFamily.card :=
    certificate.section6Index.symm.trans
      (Equiv.ofBijective
        literal.sourceIndex literal.sourceIndex_bijective)
  let jacobian : ENNReal :=
    ENNReal.ofReal ((1 / 100 : ℝ) ^ 3) *
      ENNReal.ofReal ((1 / rho : ℝ) ^ 2)
  change
    (∑ publicIndex : Fin certificate.publicFamily.card,
      volume
        (wz2PaperLiteralUnitRescalingMap anchor hrho ''
          sourceShading.carrier (sourceEquiv publicIndex))) =
      jacobian *
        ∑ sourceIndex : Fin sourceFamily.card,
          volume (sourceShading.carrier sourceIndex)
  calc
    (∑ publicIndex : Fin certificate.publicFamily.card,
        volume
          (wz2PaperLiteralUnitRescalingMap anchor hrho ''
            sourceShading.carrier (sourceEquiv publicIndex))) =
        ∑ publicIndex : Fin certificate.publicFamily.card,
          jacobian *
            volume
              (sourceShading.carrier
                (sourceEquiv publicIndex)) := by
      apply Finset.sum_congr rfl
      intro publicIndex _
      exact
        wz2_paper_literal_unit_rescaling_volume
          anchor hrho
          (sourceShading.carrier (sourceEquiv publicIndex))
          (sourceShading.measurable_carrier
            (sourceEquiv publicIndex))
    _ =
        jacobian *
          ∑ publicIndex : Fin certificate.publicFamily.card,
            volume
              (sourceShading.carrier
                (sourceEquiv publicIndex)) := by
      rw [Finset.mul_sum]
    _ =
        jacobian *
          ∑ sourceIndex : Fin sourceFamily.card,
            volume (sourceShading.carrier sourceIndex) := by
      congr 1
      exact
        Finset.sum_equiv sourceEquiv
          (by simp) (fun _ _ => rfl)

/-- The union of the exact-image ordinary shading is exactly the affine image
of the source union.  Unlike the cubical literal target, this shading adds no
points beyond the genuine images. -/
theorem literalExactCroppedImageShading_union_eq
    {delta rho : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily delta}
    {anchor : Kakeya.DeltaTube rho}
    {hrho : 0 < rho}
    {normalization : WZ2PaperAssouadUnitRescalingData anchor}
    {literal :
      WZ2PaperLiteralUnitRescaledFamilyData
        sourceFamily anchor hrho}
    {jacobianConstant : ENNReal}
    (certificate :
      WZ2PaperAssouadToLiteralRescalingCertificate
        hrho normalization literal jacobianConstant)
    (sourceShading : WZ1PaperTubeShading sourceFamily)
    (image_subset_public :
      ∀ publicIndex,
        wz2PaperLiteralUnitRescalingMap anchor hrho ''
            sourceShading.carrier
              (literal.sourceIndex
                (certificate.section6Index.symm publicIndex)) ⊆
          (certificate.publicFamily.tube publicIndex).carrier) :
    (certificate.literalExactCroppedImageShading
        sourceShading image_subset_public).union =
      wz2PaperLiteralUnitRescalingMap anchor hrho ''
        sourceShading.union := by
  ext point
  constructor
  · rintro ⟨publicIndex, sourcePoint, sourcePointMem, rfl⟩
    exact ⟨sourcePoint,
      ⟨literal.sourceIndex
          (certificate.section6Index.symm publicIndex), sourcePointMem⟩, rfl⟩
  · rintro ⟨sourcePoint, ⟨sourceIndex, sourcePointMem⟩, rfl⟩
    rcases literal.sourceIndex_bijective.surjective sourceIndex with
      ⟨targetIndex, targetIndexEq⟩
    let publicIndex := certificate.section6Index targetIndex
    refine ⟨publicIndex, sourcePoint, ?_, rfl⟩
    change sourcePoint ∈
      sourceShading.carrier
        (literal.sourceIndex
          (certificate.section6Index.symm publicIndex))
    rw [show certificate.section6Index.symm publicIndex = targetIndex by
      exact certificate.section6Index.symm_apply_apply targetIndex]
    rwa [targetIndexEq]

theorem literalExactCroppedImageShading_dense_of_mass
    {delta rho : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily delta}
    {anchor : Kakeya.DeltaTube rho}
    {hrho : 0 < rho}
    {normalization : WZ2PaperAssouadUnitRescalingData anchor}
    {literal :
      WZ2PaperLiteralUnitRescaledFamilyData
        sourceFamily anchor hrho}
    {jacobianConstant lambda : ENNReal}
    (certificate :
      WZ2PaperAssouadToLiteralRescalingCertificate
        hrho normalization literal jacobianConstant)
    (sourceShading : WZ1PaperTubeShading sourceFamily)
    (image_subset_public :
      ∀ publicIndex,
        wz2PaperLiteralUnitRescalingMap anchor hrho ''
            sourceShading.carrier
              (literal.sourceIndex
                (certificate.section6Index.symm publicIndex)) ⊆
          (certificate.publicFamily.tube publicIndex).carrier)
    (mass_lower :
      lambda * certificate.publicFamily.toBodyFamily.mass ≤
        (ENNReal.ofReal ((1 / 100 : ℝ) ^ 3) *
            ENNReal.ofReal ((1 / rho : ℝ) ^ 2)) *
          sourceShading.mass) :
    (certificate.literalExactCroppedImageShading
      sourceShading image_subset_public).IsLambdaDense lambda := by
  rw [Kakeya.Streamlined.Shading.IsLambdaDense]
  rw [certificate.literalExactCroppedImageShading_mass
    sourceShading image_subset_public]
  exact mass_lower

theorem literalExactCroppedImageShading_union_subset
    {delta rho : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily delta}
    {anchor : Kakeya.DeltaTube rho}
    {hrho : 0 < rho}
    {normalization : WZ2PaperAssouadUnitRescalingData anchor}
    {literal :
      WZ2PaperLiteralUnitRescaledFamilyData
        sourceFamily anchor hrho}
    {jacobianConstant : ENNReal}
    (certificate :
      WZ2PaperAssouadToLiteralRescalingCertificate
        hrho normalization literal jacobianConstant)
    (sourceShading : WZ1PaperTubeShading sourceFamily)
    (image_subset_public :
      ∀ publicIndex,
        wz2PaperLiteralUnitRescalingMap anchor hrho ''
            sourceShading.carrier
              (literal.sourceIndex
                (certificate.section6Index.symm publicIndex)) ⊆
          (certificate.publicFamily.tube publicIndex).carrier)
    (literalShading :
      WZ2PaperLiteralUnitRescaledShadingData
        literal sourceShading) :
    (certificate.literalExactCroppedImageShading
      sourceShading image_subset_public).union ⊆
        literalShading.targetShading.union := by
  rintro point ⟨publicIndex, sourcePoint, hsourcePoint, rfl⟩
  let target := certificate.section6Index.symm publicIndex
  refine ⟨target, ?_⟩
  rw [literalShading.target_carrier_eq target]
  exact
    ⟨wz2PaperLiteralUnitRescalingMap anchor hrho sourcePoint,
      ⟨sourcePoint, hsourcePoint, rfl⟩,
      rfl⟩

noncomputable def literalExactImageShading
    {delta rho : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily delta}
    {anchor : Kakeya.DeltaTube rho}
    {hrho : 0 < rho}
    {normalization : WZ2PaperAssouadUnitRescalingData anchor}
    {literal :
      WZ2PaperLiteralUnitRescaledFamilyData
        sourceFamily anchor hrho}
    {jacobianConstant : ENNReal}
    (certificate :
      WZ2PaperAssouadToLiteralRescalingCertificate
        hrho normalization literal jacobianConstant)
    (sourceShading :
      Kakeya.Streamlined.TubeShading sourceFamily) :
    Kakeya.Streamlined.TubeShading certificate.publicFamily where
  carrier publicIndex :=
    wz2PaperLiteralUnitRescalingMap anchor hrho ''
      sourceShading.carrier
        (literal.sourceIndex
          (certificate.section6Index.symm publicIndex))
  measurable_carrier publicIndex := by
    let equivalence :=
      wz2PaperLiteralUnitRescalingAffineEquiv anchor hrho
    let measurableEquivalence : Point3 ≃ᵐ Point3 :=
      {
        toFun := equivalence
        invFun := equivalence.symm
        left_inv := equivalence.left_inv
        right_inv := equivalence.right_inv
        measurable_toFun :=
          equivalence.continuous_of_finiteDimensional.measurable
        measurable_invFun :=
          equivalence.symm.continuous_of_finiteDimensional.measurable
      }
    have hmeasurable :=
      (measurableEquivalence.measurableSet_image).mpr
        (sourceShading.measurable_carrier
          (literal.sourceIndex
            (certificate.section6Index.symm publicIndex)))
    have hmap :
        (measurableEquivalence :
            Point3 → Point3) =
          wz2PaperLiteralUnitRescalingMap anchor hrho := by
      funext point
      exact
        wz2PaperLiteralUnitRescalingAffineEquiv_apply
          anchor hrho point
    rwa [hmap] at hmeasurable
  subset_body publicIndex := by
    let target := certificate.section6Index.symm publicIndex
    have hindex :
        certificate.section6Index target = publicIndex :=
      certificate.section6Index.apply_symm_apply publicIndex
    have himage :
        wz2PaperLiteralUnitRescalingMap anchor hrho ''
            sourceShading.carrier (literal.sourceIndex target) ⊆
          wz2PaperLiteralUnitRescalingMap anchor hrho ''
            (sourceFamily.tube
              (literal.sourceIndex target)).carrier :=
      Set.image_mono
        (sourceShading.subset_body
          (literal.sourceIndex target))
    change
      wz2PaperLiteralUnitRescalingMap anchor hrho ''
          sourceShading.carrier (literal.sourceIndex target) ⊆
        (certificate.publicFamily.tube publicIndex).carrier
    rw [← hindex]
    exact himage.trans
      (certificate.literal_image_subset_public target)

/-- The ordinary exact-image shading adds no points: its union is literally
the affine image of the source union. -/
theorem literalExactImageShading_union_eq
    {delta rho : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily delta}
    {anchor : Kakeya.DeltaTube rho}
    {hrho : 0 < rho}
    {normalization : WZ2PaperAssouadUnitRescalingData anchor}
    {literal :
      WZ2PaperLiteralUnitRescaledFamilyData
        sourceFamily anchor hrho}
    {jacobianConstant : ENNReal}
    (certificate :
      WZ2PaperAssouadToLiteralRescalingCertificate
        hrho normalization literal jacobianConstant)
    (sourceShading : Kakeya.Streamlined.TubeShading sourceFamily) :
    (certificate.literalExactImageShading sourceShading).union =
      wz2PaperLiteralUnitRescalingMap anchor hrho ''
        sourceShading.union := by
  ext point
  constructor
  · rintro ⟨publicIndex, sourcePoint, sourcePointMem, rfl⟩
    exact ⟨sourcePoint,
      ⟨literal.sourceIndex
          (certificate.section6Index.symm publicIndex), sourcePointMem⟩, rfl⟩
  · rintro ⟨sourcePoint, ⟨sourceIndex, sourcePointMem⟩, rfl⟩
    rcases literal.sourceIndex_bijective.surjective sourceIndex with
      ⟨targetIndex, targetIndexEq⟩
    let publicIndex := certificate.section6Index targetIndex
    refine ⟨publicIndex, sourcePoint, ?_, rfl⟩
    change sourcePoint ∈
      sourceShading.carrier
        (literal.sourceIndex
          (certificate.section6Index.symm publicIndex))
    rw [show certificate.section6Index.symm publicIndex = targetIndex by
      exact certificate.section6Index.symm_apply_apply targetIndex]
    rwa [targetIndexEq]

theorem literalExactImageShading_mass
    {delta rho : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily delta}
    {anchor : Kakeya.DeltaTube rho}
    {hrho : 0 < rho}
    {normalization : WZ2PaperAssouadUnitRescalingData anchor}
    {literal :
      WZ2PaperLiteralUnitRescaledFamilyData
        sourceFamily anchor hrho}
    {jacobianConstant : ENNReal}
    (certificate :
      WZ2PaperAssouadToLiteralRescalingCertificate
        hrho normalization literal jacobianConstant)
    (sourceShading :
      Kakeya.Streamlined.TubeShading sourceFamily) :
    (certificate.literalExactImageShading sourceShading).mass =
      (ENNReal.ofReal ((1 / 100 : ℝ) ^ 3) *
          ENNReal.ofReal ((1 / rho : ℝ) ^ 2)) *
        sourceShading.mass := by
  let sourceEquiv :
      Fin certificate.publicFamily.card ≃ Fin sourceFamily.card :=
    certificate.section6Index.symm.trans
      (Equiv.ofBijective
        literal.sourceIndex literal.sourceIndex_bijective)
  let jacobian : ENNReal :=
    ENNReal.ofReal ((1 / 100 : ℝ) ^ 3) *
      ENNReal.ofReal ((1 / rho : ℝ) ^ 2)
  change
    (∑ publicIndex : Fin certificate.publicFamily.card,
      volume
        (wz2PaperLiteralUnitRescalingMap anchor hrho ''
          sourceShading.carrier (sourceEquiv publicIndex))) =
      jacobian *
        ∑ sourceIndex : Fin sourceFamily.card,
          volume (sourceShading.carrier sourceIndex)
  calc
    (∑ publicIndex : Fin certificate.publicFamily.card,
        volume
          (wz2PaperLiteralUnitRescalingMap anchor hrho ''
            sourceShading.carrier (sourceEquiv publicIndex))) =
        ∑ publicIndex : Fin certificate.publicFamily.card,
          jacobian *
            volume
              (sourceShading.carrier
                (sourceEquiv publicIndex)) := by
      apply Finset.sum_congr rfl
      intro publicIndex _
      exact
        wz2_paper_literal_unit_rescaling_volume
          anchor hrho
          (sourceShading.carrier (sourceEquiv publicIndex))
          (sourceShading.measurable_carrier
            (sourceEquiv publicIndex))
    _ =
        jacobian *
          ∑ publicIndex : Fin certificate.publicFamily.card,
            volume
              (sourceShading.carrier
                (sourceEquiv publicIndex)) := by
      rw [Finset.mul_sum]
    _ =
        jacobian *
          ∑ sourceIndex : Fin sourceFamily.card,
            volume (sourceShading.carrier sourceIndex) := by
      congr 1
      exact
        Finset.sum_equiv sourceEquiv
          (by simp) (fun _ _ => rfl)

theorem literalExactImageShading_dense_of_mass
    {delta rho : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily delta}
    {anchor : Kakeya.DeltaTube rho}
    {hrho : 0 < rho}
    {normalization : WZ2PaperAssouadUnitRescalingData anchor}
    {literal :
      WZ2PaperLiteralUnitRescaledFamilyData
        sourceFamily anchor hrho}
    {jacobianConstant lambda : ENNReal}
    (certificate :
      WZ2PaperAssouadToLiteralRescalingCertificate
        hrho normalization literal jacobianConstant)
    (sourceShading :
      Kakeya.Streamlined.TubeShading sourceFamily)
    (mass_lower :
      lambda * certificate.publicFamily.toBodyFamily.mass ≤
        (ENNReal.ofReal ((1 / 100 : ℝ) ^ 3) *
            ENNReal.ofReal ((1 / rho : ℝ) ^ 2)) *
          sourceShading.mass) :
    Kakeya.Streamlined.Shading.IsLambdaDense
      (certificate.literalExactImageShading sourceShading)
      lambda := by
  rw [Kakeya.Streamlined.Shading.IsLambdaDense]
  rw [certificate.literalExactImageShading_mass sourceShading]
  exact mass_lower

theorem literalExactImageShading_union_subset
    {delta rho : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily delta}
    {anchor : Kakeya.DeltaTube rho}
    {hrho : 0 < rho}
    {normalization : WZ2PaperAssouadUnitRescalingData anchor}
    {literal :
      WZ2PaperLiteralUnitRescaledFamilyData
        sourceFamily anchor hrho}
    {jacobianConstant : ENNReal}
    (certificate :
      WZ2PaperAssouadToLiteralRescalingCertificate
        hrho normalization literal jacobianConstant)
    (sourceShading :
      Kakeya.Streamlined.TubeShading sourceFamily)
    (croppedShading : WZ1PaperTubeShading sourceFamily)
    (source_subset :
      ∀ index,
        sourceShading.carrier index ⊆
          croppedShading.carrier index)
    (literalShading :
      WZ2PaperLiteralUnitRescaledShadingData
        literal croppedShading) :
    (certificate.literalExactImageShading sourceShading).union ⊆
      literalShading.targetShading.union := by
  rintro point ⟨publicIndex, sourcePoint, hsourcePoint, rfl⟩
  let target := certificate.section6Index.symm publicIndex
  refine ⟨target, ?_⟩
  rw [literalShading.target_carrier_eq target]
  exact
    ⟨wz2PaperLiteralUnitRescalingMap anchor hrho sourcePoint,
      ⟨sourcePoint,
        source_subset
          (literal.sourceIndex target) hsourcePoint,
        rfl⟩,
      rfl⟩

end WZ2PaperAssouadToLiteralRescalingCertificate

end Kakeya.Assouad

end
