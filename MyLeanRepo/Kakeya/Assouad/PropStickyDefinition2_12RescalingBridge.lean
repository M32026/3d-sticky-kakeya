import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12BodyReindex
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperLiteralCanonicalRescaledTube
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperLiteralImageAssemblyStatements

/-!
# Assouad-to-WZ unit-rescaling bridge

Definition 2.12 attaches Convex-Wolff data to the actual affine images under
the outer-John normalization.  Section 6 uses the WZ convention: a standard
`TubeFamily (delta / rho)` with the transformed coaxial lines and cubical
shadings.

These are different geometric families.  This module freezes the comparison
certificate needed to justify the paper's phrase “the distinction is
harmless”.  Axis equality alone is deliberately insufficient.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

/-- Translation by a fixed vector preserves Lebesgue volume. -/
private theorem wz2Paper_volume_translation
    (translation : Point3) (source : Set Point3) :
    volume ((fun point : Point3 => point + translation) '' source) =
      volume source := by
  have himage :
      (fun point : Point3 => point + translation) '' source =
        (fun point : Point3 => point + (-translation)) ⁻¹' source := by
    ext point
    simp only [Set.mem_image, Set.mem_preimage]
    constructor
    · rintro ⟨sourcePoint, hsource, rfl⟩
      simpa using hsource
    · intro hsource
      refine ⟨point - translation, ?_, by abel⟩
      simpa [sub_eq_add_neg] using hsource
  rw [himage]
  exact
    MeasureTheory.measure_preimage_add_right
      volume (-translation) source

/-- Exact determinant scaling for an arbitrary affine equivalence. -/
theorem wz2PaperAffineEquiv_volume_image_eq
    (equivalence : Point3 ≃ᵃ[ℝ] Point3)
    (source : Set Point3) :
    volume (equivalence '' source) =
      ENNReal.ofReal
          |LinearMap.det
            (equivalence.linear : Point3 →ₗ[ℝ] Point3)| *
        volume source := by
  let linear : Point3 →L[ℝ] Point3 :=
    equivalence.linear.toContinuousLinearMap
  let translation : Point3 := equivalence 0
  have hdecomposition :
      equivalence '' source =
        (fun point : Point3 => point + translation) ''
          (linear '' source) := by
    ext point
    constructor
    · rintro ⟨sourcePoint, hsource, rfl⟩
      refine ⟨linear sourcePoint, ⟨sourcePoint, hsource, rfl⟩, ?_⟩
      have h :=
        equivalence.map_vadd (0 : Point3) sourcePoint
      simpa [linear, translation] using h.symm
    · rintro ⟨linearPoint, ⟨sourcePoint, hsource, rfl⟩, rfl⟩
      refine ⟨sourcePoint, hsource, ?_⟩
      have h :=
        equivalence.map_vadd (0 : Point3) sourcePoint
      simpa [linear, translation] using h
  rw [hdecomposition,
    wz2Paper_volume_translation translation (linear '' source)]
  exact
    MeasureTheory.Measure.addHaar_image_continuousLinearMap
      volume linear source

/-- The invertible linear part of the literal WZ unit rescaling. -/
noncomputable def wz2PaperLiteralUnitRescalingLinearEquiv
    {rho : ℝ} (anchor : Kakeya.DeltaTube rho)
    (hrho : 0 < rho) :
    Point3 ≃ₗ[ℝ] Point3 :=
  LinearEquiv.ofInjectiveEndo
    (wz2PaperLiteralUnitRescalingLinear anchor)
    (wz2PaperLiteralUnitRescalingLinear_injective anchor hrho)

/-- The literal WZ rescaling as an affine equivalence. -/
noncomputable def wz2PaperLiteralUnitRescalingAffineEquiv
    {rho : ℝ} (anchor : Kakeya.DeltaTube rho)
    (hrho : 0 < rho) :
    Point3 ≃ᵃ[ℝ] Point3 :=
  AffineEquiv.ofLinearEquiv
    (wz2PaperLiteralUnitRescalingLinearEquiv anchor hrho)
    (wz1TubeAxisZeroPoint anchor) 0

@[simp] theorem wz2PaperLiteralUnitRescalingAffineEquiv_apply
    {rho : ℝ} (anchor : Kakeya.DeltaTube rho)
    (hrho : 0 < rho) (point : Point3) :
    wz2PaperLiteralUnitRescalingAffineEquiv anchor hrho point =
      wz2PaperLiteralUnitRescalingMap anchor hrho point := by
  rw [wz2PaperLiteralUnitRescalingAffineEquiv,
    AffineEquiv.ofLinearEquiv_apply]
  rw [vadd_eq_add, add_zero]
  change
    wz2PaperLiteralUnitRescalingLinear anchor
        (point - wz1TubeAxisZeroPoint anchor) =
      wz2PaperLiteralUnitRescalingMap anchor hrho point
  rfl

/-- The common coordinate change from outer-John to literal WZ coordinates. -/
noncomputable def wz2PaperJohnToLiteralCoordinateChange
    {rho : ℝ} {anchor : Kakeya.DeltaTube rho}
    (hrho : 0 < rho)
    (normalization : WZ2PaperAssouadUnitRescalingData anchor) :
    Point3 ≃ᵃ[ℝ] Point3 :=
  normalization.map.symm.trans
    (wz2PaperLiteralUnitRescalingAffineEquiv anchor hrho)

@[simp] theorem wz2PaperJohnToLiteralCoordinateChange_apply_map
    {rho : ℝ} {anchor : Kakeya.DeltaTube rho}
    (hrho : 0 < rho)
    (normalization : WZ2PaperAssouadUnitRescalingData anchor)
    (point : Point3) :
    wz2PaperJohnToLiteralCoordinateChange hrho normalization
        (normalization.map point) =
      wz2PaperLiteralUnitRescalingMap anchor hrho point := by
  simp [wz2PaperJohnToLiteralCoordinateChange,
    AffineEquiv.trans_apply]

theorem wz2PaperJohnToLiteralCoordinateChange_image
    {rho : ℝ} {anchor : Kakeya.DeltaTube rho}
    (hrho : 0 < rho)
    (normalization : WZ2PaperAssouadUnitRescalingData anchor)
    (source : Set Point3) :
    wz2PaperJohnToLiteralCoordinateChange hrho normalization ''
        (normalization.map '' source) =
      wz2PaperLiteralUnitRescalingMap anchor hrho '' source := by
  ext point
  constructor
  · rintro ⟨johnPoint, ⟨sourcePoint, hsource, rfl⟩, rfl⟩
    exact
      ⟨sourcePoint, hsource,
        wz2PaperJohnToLiteralCoordinateChange_apply_map
          hrho normalization sourcePoint |>.symm⟩
  · rintro ⟨sourcePoint, hsource, rfl⟩
    exact
      ⟨normalization.map sourcePoint,
        ⟨sourcePoint, hsource, rfl⟩,
        wz2PaperJohnToLiteralCoordinateChange_apply_map
          hrho normalization sourcePoint⟩

/-- Actual Assouad images, reindexed by a supplied WZ target family. -/
noncomputable def wz2PaperLiteralIndexedAssouadBodyFamily
    {delta rho : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily delta}
    {anchor : Kakeya.DeltaTube rho}
    {hrho : 0 < rho}
    (normalization : WZ2PaperAssouadUnitRescalingData anchor)
    (literal :
      WZ2PaperLiteralUnitRescaledFamilyData
        sourceFamily anchor hrho) :
    Kakeya.Streamlined.BodyFamily where
  card := literal.targetFamily.card
  body target :=
    ⟨normalization.map ''
      (sourceFamily.tube (literal.sourceIndex target)).carrier⟩

/--
The complete geometric comparison between the actual Assouad rescaling, an
ordinary public target family, and the WZ Section 6 target family.

`coordinateChange` is a single affine equivalence, common to the complete
fiber.  The first carrier identity says that it sends the actual John image
back to the literal WZ affine image.  `publicFamily` is allowed to recenter
the unit segment while keeping the same coaxial line as the WZ target.  Its
ordinary carriers contain the affine images and therefore support the public
pure CWA.  The WZ target remains the carrier for the cropped cubical shading.
The Jacobian loss is explicit.
-/
structure WZ2PaperAssouadToLiteralRescalingCertificate
    {delta rho : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily delta}
    {anchor : Kakeya.DeltaTube rho}
    (hrho : 0 < rho)
    (normalization : WZ2PaperAssouadUnitRescalingData anchor)
    (literal :
      WZ2PaperLiteralUnitRescaledFamilyData
        sourceFamily anchor hrho)
    (jacobianConstant : ENNReal) where
  publicFamily :
    Kakeya.Streamlined.TubeFamily (delta / rho)
  publicSourceIndex :
    Fin publicFamily.card → Fin sourceFamily.card
  publicSourceIndex_bijective :
    Function.Bijective publicSourceIndex
  section6Index :
    Fin literal.targetFamily.card ≃ Fin publicFamily.card
  sourceIndex_compatibility :
    ∀ target,
      publicSourceIndex (section6Index target) =
        literal.sourceIndex target
  same_axis :
    ∀ target,
      tubeAxisLine (publicFamily.tube (section6Index target)) =
        tubeAxisLine (literal.targetFamily.tube target)
  coordinateChange : Point3 ≃ᵃ[ℝ] Point3
  image_eq :
    ∀ target,
      coordinateChange ''
          (normalization.map ''
            (sourceFamily.tube
              (literal.sourceIndex target)).carrier) =
        wz2PaperLiteralUnitRescalingMap anchor hrho ''
          (sourceFamily.tube
            (literal.sourceIndex target)).carrier
  literal_image_subset_public :
    ∀ target,
      wz2PaperLiteralUnitRescalingMap anchor hrho ''
          (sourceFamily.tube
            (literal.sourceIndex target)).carrier ⊆
        (publicFamily.tube (section6Index target)).carrier
  convex_preimage :
    ∀ convexSet : Set Point3,
      Convex ℝ convexSet →
        Convex ℝ (coordinateChange.symm '' convexSet)
  preimage_volume :
    ∀ targetSet : Set Point3,
      volume (coordinateChange.symm '' targetSet) ≤
        jacobianConstant * volume targetSet

/--
The exact remaining geometric theorem for one complete fiber.

The fixed constant is quantified existentially before all scales and
families.  This is the paper's dimension-only loss; it must not depend on
`delta`, `rho`, the parent, or the fiber cardinality.
-/
def WZ2PaperAssouadToLiteralRescalingStatement : Prop :=
  ∃ jacobianConstant : ENNReal,
    1 ≤ jacobianConstant ∧
    jacobianConstant ≠ ⊤ ∧
    ∀ {delta rho : ℝ},
      0 < delta →
      ∀ (hrho : 0 < rho),
        rho ≤ 1 →
        ∀ (sourceFamily :
            Kakeya.Streamlined.TubeFamily delta),
          ∀ (anchor : Kakeya.DeltaTube rho),
            (∀ source,
              WZ1PaperTubeCovers
                (sourceFamily.tube source) anchor) →
            ∀ (literal :
                WZ2PaperLiteralUnitRescaledFamilyData
                  sourceFamily anchor hrho),
              Nonempty
                (WZ2PaperAssouadToLiteralRescalingCertificate
                  hrho
                  (WZ2PaperAssouadUnitRescalingData.ofTube
                    anchor hrho)
                  literal jacobianConstant)

/--
One Section 6 literal target family together with the public ordinary family
on which hereditary pure CWA is actually asserted.

The loss is measured at the normalized fine scale `delta / rho`.  Packaging
the certificate and the CWA witness together prevents downstream code from
choosing unrelated public and WZ families.
-/
structure WZ2PaperAssouadLiteralPureNearbyBridge
    {delta rho loss : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily delta}
    {anchor : Kakeya.DeltaTube rho}
    (hrho : 0 < rho)
    (literal :
      WZ2PaperLiteralUnitRescaledFamilyData
        sourceFamily anchor hrho) where
  jacobianConstant : ENNReal
  jacobianConstant_one : 1 ≤ jacobianConstant
  jacobianConstant_finite : jacobianConstant ≠ ⊤
  certificate :
    WZ2PaperAssouadToLiteralRescalingCertificate
      hrho
      (WZ2PaperAssouadUnitRescalingData.ofTube
        anchor hrho)
      literal jacobianConstant
  pure_cwa :
    WZ2PaperPureCWAAtNearbyScales
      certificate.publicFamily
      (Kakeya.realRpowENN (delta / rho) (-loss))

namespace WZ2PaperAssouadToLiteralRescalingCertificate

/-- Reindex a cropped WZ shading onto the ordinary public target family. -/
noncomputable def publicShading
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
    (shading : WZ1PaperTubeShading literal.targetFamily) :
    WZ1PaperTubeShading certificate.publicFamily where
  carrier publicIndex :=
    shading.carrier
      (certificate.section6Index.symm publicIndex)
  measurable_carrier publicIndex :=
    shading.measurable_carrier
      (certificate.section6Index.symm publicIndex)
  subset_body publicIndex := by
    let literalIndex :=
      certificate.section6Index.symm publicIndex
    have hindex :
        certificate.section6Index literalIndex = publicIndex :=
      certificate.section6Index.apply_symm_apply publicIndex
    have hsubset :=
      shading.subset_body literalIndex
    change
      shading.carrier literalIndex ⊆
        wz1PaperTubeCarrier
          (certificate.publicFamily.tube publicIndex)
    rw [← hindex, wz1PaperTubeCarrier,
      certificate.same_axis literalIndex]
    exact hsubset

theorem publicFamily_enncard_eq
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
        hrho normalization literal jacobianConstant) :
    certificate.publicFamily.enncard =
      literal.targetFamily.enncard := by
  have hcard :
      certificate.publicFamily.card =
        literal.targetFamily.card := by
    simpa using
      Fintype.card_congr certificate.section6Index.symm
  simp [Kakeya.Streamlined.TubeFamily.enncard, hcard]

theorem publicFamily_nonempty
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
    (hliteral : literal.targetFamily.Nonempty) :
    certificate.publicFamily.Nonempty := by
  have hcard :
      certificate.publicFamily.card =
        literal.targetFamily.card := by
    simpa using
      Fintype.card_congr certificate.section6Index.symm
  simpa [Kakeya.Streamlined.TubeFamily.Nonempty, hcard] using hliteral

theorem publicBody_mass_eq
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
        hrho normalization literal jacobianConstant) :
    (wz1PaperBodyFamily certificate.publicFamily).mass =
      (wz1PaperBodyFamily literal.targetFamily).mass := by
  change
    (∑ publicIndex : Fin certificate.publicFamily.card,
      volume
        (wz1PaperTubeCarrier
          (certificate.publicFamily.tube publicIndex))) =
      ∑ literalIndex : Fin literal.targetFamily.card,
        volume
          (wz1PaperTubeCarrier
            (literal.targetFamily.tube literalIndex))
  exact
    Finset.sum_equiv certificate.section6Index.symm
      (by simp)
      (fun publicIndex _ => by
        have haxis :
            tubeAxisLine
                (certificate.publicFamily.tube publicIndex) =
              tubeAxisLine
                (literal.targetFamily.tube
                  (certificate.section6Index.symm publicIndex)) := by
          calc
            tubeAxisLine
                (certificate.publicFamily.tube publicIndex) =
                tubeAxisLine
                  (certificate.publicFamily.tube
                    (certificate.section6Index
                      (certificate.section6Index.symm publicIndex))) := by
              rw [certificate.section6Index.apply_symm_apply]
            _ =
                tubeAxisLine
                  (literal.targetFamily.tube
                    (certificate.section6Index.symm publicIndex)) :=
              certificate.same_axis
                (certificate.section6Index.symm publicIndex)
        simp only [wz1PaperTubeCarrier, haxis])

theorem publicShading_mass_eq
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
    (shading : WZ1PaperTubeShading literal.targetFamily) :
    (certificate.publicShading shading).mass = shading.mass := by
  change
    (∑ publicIndex : Fin certificate.publicFamily.card,
      volume
        (shading.carrier
          (certificate.section6Index.symm publicIndex))) =
      ∑ literalIndex : Fin literal.targetFamily.card,
        volume (shading.carrier literalIndex)
  exact
    Finset.sum_equiv certificate.section6Index.symm
      (by simp) (fun _ _ => rfl)

theorem publicShading_union_eq
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
    (shading : WZ1PaperTubeShading literal.targetFamily) :
    (certificate.publicShading shading).union = shading.union := by
  ext point
  constructor
  · rintro ⟨publicIndex, hpoint⟩
    exact
      ⟨certificate.section6Index.symm publicIndex, hpoint⟩
  · rintro ⟨literalIndex, hpoint⟩
    refine
      ⟨certificate.section6Index literalIndex, ?_⟩
    simpa [publicShading] using hpoint

theorem publicShading_pointMultiplicity_eq
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
    (shading : WZ1PaperTubeShading literal.targetFamily)
    (point : Point3) :
    (certificate.publicShading shading).pointMultiplicity point =
      shading.pointMultiplicity point := by
  classical
  let publicIndices :=
    Finset.univ.filter fun publicIndex :
        Fin certificate.publicFamily.card =>
      point ∈ (certificate.publicShading shading).carrier publicIndex
  let literalIndices :=
    Finset.univ.filter fun literalIndex :
        Fin literal.targetFamily.card =>
      point ∈ shading.carrier literalIndex
  have himage :
      Finset.image certificate.section6Index.symm publicIndices =
        literalIndices := by
    ext literalIndex
    constructor
    · intro hmember
      rcases Finset.mem_image.mp hmember with
        ⟨publicIndex, hpublic, heq⟩
      have hpoint :
          point ∈
            shading.carrier
              (certificate.section6Index.symm publicIndex) := by
        simpa [publicIndices, publicShading] using hpublic
      have hliteral :
          point ∈ shading.carrier literalIndex := by
        rwa [heq] at hpoint
      simpa [literalIndices] using hliteral
    · intro hmember
      have hpoint :
          point ∈ shading.carrier literalIndex := by
        simpa [literalIndices] using hmember
      let publicIndex :=
        certificate.section6Index literalIndex
      have hpublic :
          publicIndex ∈ publicIndices := by
        simpa [publicIndices, publicShading, publicIndex] using hpoint
      exact
        Finset.mem_image.mpr
          ⟨publicIndex, hpublic,
            certificate.section6Index.symm_apply_apply literalIndex⟩
  change publicIndices.card = literalIndices.card
  rw [← himage]
  exact
    Finset.card_image_of_injective
      publicIndices certificate.section6Index.symm.injective |>.symm

theorem publicShading_cubical
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
    {shading : WZ1PaperTubeShading literal.targetFamily}
    (hcubical : WZ1PaperIsCubicalShading shading) :
    WZ1PaperIsCubicalShading
      (certificate.publicShading shading) := by
  intro publicIndex point hpoint
  exact
    hcubical
      (certificate.section6Index.symm publicIndex)
      point hpoint

/--
Transport actual John-image Convex-Wolff counting to the ordinary public
target family.  The proof uses only the explicit common coordinate change,
its volume bound, and the literal-image carrier inclusion.
-/
theorem public_convexWolff
    {delta rho : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily delta}
    {anchor : Kakeya.DeltaTube rho}
    {hrho : 0 < rho}
    {normalization : WZ2PaperAssouadUnitRescalingData anchor}
    {literal :
      WZ2PaperLiteralUnitRescaledFamilyData
        sourceFamily anchor hrho}
    {jacobianConstant C : ENNReal}
    (certificate :
      WZ2PaperAssouadToLiteralRescalingCertificate
        hrho normalization literal jacobianConstant)
    (hactual :
      WZ2PaperBodyConvexWolffBound
        (wz2PaperLiteralIndexedAssouadBodyFamily
          normalization literal) C) :
    WZ2PaperBodyConvexWolffBound
      certificate.publicFamily.toBodyFamily
      (jacobianConstant * C) := by
  apply
    wz2PaperBodyConvexWolffBound_of_indexed_envelope
      (source :=
        wz2PaperLiteralIndexedAssouadBodyFamily
          normalization literal)
      (target := certificate.publicFamily.toBodyFamily)
      certificate.section6Index.symm
  · intro targetConvexSet htargetConvex
    refine
      ⟨certificate.coordinateChange.symm '' targetConvexSet,
        certificate.convex_preimage targetConvexSet htargetConvex,
        certificate.preimage_volume targetConvexSet,
        ?_⟩
    intro publicIndex hpublicCarrier
    let literalIndex :=
      certificate.section6Index.symm publicIndex
    have hindex :
        certificate.section6Index literalIndex = publicIndex :=
      certificate.section6Index.apply_symm_apply publicIndex
    intro point hpoint
    have hcoordinateImage :
        certificate.coordinateChange point ∈
          certificate.coordinateChange ''
            (normalization.map ''
              (sourceFamily.tube
                (literal.sourceIndex literalIndex)).carrier) :=
      ⟨point, hpoint, rfl⟩
    have hliteralImage :
        certificate.coordinateChange point ∈
          wz2PaperLiteralUnitRescalingMap anchor hrho ''
            (sourceFamily.tube
              (literal.sourceIndex literalIndex)).carrier := by
      rw [← certificate.image_eq literalIndex]
      exact hcoordinateImage
    have hpublicTube :
        certificate.coordinateChange point ∈
          (certificate.publicFamily.tube publicIndex).carrier := by
      have :=
        certificate.literal_image_subset_public literalIndex
          hliteralImage
      rwa [hindex] at this
    have htarget :
        certificate.coordinateChange point ∈ targetConvexSet :=
      hpublicCarrier hpublicTube
    refine
      ⟨certificate.coordinateChange point, htarget, ?_⟩
    exact certificate.coordinateChange.symm_apply_apply point
  · exact hactual

end WZ2PaperAssouadToLiteralRescalingCertificate

end Kakeya.Assouad

end
