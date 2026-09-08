import MyLeanRepo.Kakeya.Streamlined.ProfileUniformRefinement.PointwiseFullFiberUniformShading
import MyLeanRepo.Kakeya.Streamlined.RandomTranslation.DilatedUniformTubeStructure

/-!
# Quantitative all-real-scale dilated tube shadings

This is the all-real-scale fixed-dilation version of paper Definition 2.2.
The ambient family and every pointwise shading-incident family carry genuine
complete-containment `DilatedUniformTubeStructure`s. The auxiliary parent maps
inside those structures are geometric cover witnesses only; no assigned-fiber
uniformity is part of this paper-facing API.

The historical finite-grid producer
`PointwiseFullFiberUniformShadingRefinementStatement` remains as internal
quantitative compatibility data. The canonical paper producer is
split into `PaperFiniteGridUniformPigeonholingStatement` and
`PaperGridToAllRealDefinitionTwoTwoStatement`. The former freezes the absolute
finite-grid branching constant before runtime parameters; the latter
constructs this module's all-real-scale certificate.

The raw structure below carries one finite runtime loss.  Paper `≈`
uniformity is represented by
`ApproxDilatedPointwiseFullFiberUniformTubeShading epsilon F Y`, which
requires that loss to be at most `delta⁻ᵉᵖˢⁱˡᵒⁿ`.
-/

noncomputable section

namespace Kakeya.Streamlined

/--
Raw quantitative carrier for Definition 2.2 at all admissible real scales
and one fixed cover dilation.

`shadingUniformity` simultaneously bounds the ambient branching constant,
the branching constants of all pointwise incident families, and the
comparison of incident branching numbers between different shaded points.

The paper `≈` certificate is the `Approx...` wrapper below. The accepted
Definition 2.1(iv) Frostman and `deltaMax` profile fields remain part of the
finite distinguished-grid structure; a consumer needing them at a selected
real scale must run the explicit profile-refinement bridge.
-/
structure DilatedPointwiseFullFiberUniformTubeShading
    {delta A : ℝ} (F : TubeFamily delta) (Y : TubeShading F) extends
    DilatedUniformTubeStructure (A := A) F where
  shadingUniformity : ENNReal
  one_le_shadingUniformity : 1 ≤ shadingUniformity
  shadingUniformity_ne_top : shadingUniformity ≠ ⊤
  ambientUniformity_le :
    toDilatedUniformTubeStructure.uniformity ≤ shadingUniformity
  incidentStructure :
    ∀ (point : Point3), point ∈ Y.union →
      DilatedUniformTubeStructure
        (A := A) (shadingIncidentSubfamily Y point).family
  incidentUniformity_le :
    ∀ point hpoint,
      (incidentStructure point hpoint).uniformity ≤ shadingUniformity
  incidentBranchingNumbersComparable :
    ∀ first hfirst second hsecond (rho : AdmissibleScale delta),
      ComparableBy shadingUniformity
        (geometricFullContainmentBranchingNumber
          (A := A)
          (shadingIncidentSubfamily Y first).family
          ((incidentStructure first hfirst).coarse rho))
        (geometricFullContainmentBranchingNumber
          (A := A)
          (shadingIncidentSubfamily Y second).family
          ((incidentStructure second hsecond).coarse rho))

/--
Paper-facing all-real Definition 2.2 at one requested subpolynomial loss.

Both family branching and the pointwise incident branching comparisons are
controlled by the same `delta⁻ᵉᵖˢⁱˡᵒⁿ` budget through `shadingUniformity`.
-/
structure ApproxDilatedPointwiseFullFiberUniformTubeShading
    {delta A : ℝ} (epsilon : ℝ)
    (F : TubeFamily delta) (Y : TubeShading F) extends
    DilatedPointwiseFullFiberUniformTubeShading (A := A) F Y where
  shadingUniformity_le :
    toDilatedPointwiseFullFiberUniformTubeShading.shadingUniformity ≤
      Kakeya.realRpowENN delta (-epsilon)

namespace ApproxDilatedPointwiseFullFiberUniformTubeShading

/-- Forget the explicit `≈` budget and retain the raw all-real structure. -/
abbrev raw
    {delta A epsilon : ℝ} {F : TubeFamily delta} {Y : TubeShading F}
    (U : ApproxDilatedPointwiseFullFiberUniformTubeShading
      (A := A) epsilon F Y) :
    DilatedPointwiseFullFiberUniformTubeShading (A := A) F Y :=
  U.toDilatedPointwiseFullFiberUniformTubeShading

end ApproxDilatedPointwiseFullFiberUniformTubeShading

namespace DilatedPointwiseFullFiberUniformTubeShading

/-- Forget the pointwise shading data and retain the raw ambient carrier. -/
abbrev ambientStructure
    {delta A : ℝ} {F : TubeFamily delta} {Y : TubeShading F}
    (U : DilatedPointwiseFullFiberUniformTubeShading
      (A := A) F Y) :
    DilatedUniformTubeStructure (A := A) F :=
  U.toDilatedUniformTubeStructure

/-- The raw ambient constant is controlled by the raw pointwise constant. -/
lemma ambient_uniformity_le
    {delta A : ℝ} {F : TubeFamily delta} {Y : TubeShading F}
    (U : DilatedPointwiseFullFiberUniformTubeShading
      (A := A) F Y) :
    U.ambientStructure.uniformity ≤ U.shadingUniformity :=
  U.ambientUniformity_le

end DilatedPointwiseFullFiberUniformTubeShading

end Kakeya.Streamlined

end
