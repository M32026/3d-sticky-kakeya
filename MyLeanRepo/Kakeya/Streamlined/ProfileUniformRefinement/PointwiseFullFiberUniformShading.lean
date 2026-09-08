import MyLeanRepo.Kakeya.Streamlined.ProfileUniformRefinement.GeometricFullContainmentFibers
import MyLeanRepo.Kakeya.Streamlined.UniformScaleGrid

/-!
# Quantitative pointwise full-fiber tube shadings

The raw structure in this module is construction data for Definition 2.2. The
incident family at a point consists of exactly the tubes whose shading
contains that point.  Its branching counts are geometric full-containment
counts and do not depend on an auxiliary parent assignment.

The paper-facing finite-grid semantics are exposed separately by
`PaperGridPointwiseFullFiberUniformTubeShading`: branching uses one fixed
absolute constant (`∼`), while the accepted Frostman and `deltaMax` profile
repair carries an explicit subpolynomial loss.
-/

noncomputable section

namespace Kakeya.Streamlined

/-- Fine indices whose shaded pieces contain a point. -/
def shadingIncidentIndices
    {delta : ℝ} {F : TubeFamily delta}
    (Y : TubeShading F) (x : Point3) :
    Finset (Fin F.card) := by
  classical
  exact Finset.univ.filter fun i => x ∈ Y.carrier i

@[simp]
lemma mem_shadingIncidentIndices_iff
    {delta : ℝ} {F : TubeFamily delta}
    (Y : TubeShading F) (x : Point3) (i : Fin F.card) :
    i ∈ shadingIncidentIndices Y x ↔ x ∈ Y.carrier i := by
  simp [shadingIncidentIndices]

/-- The indexed tube family incident to a shaded point. -/
def shadingIncidentSubfamily
    {delta : ℝ} {F : TubeFamily delta}
    (Y : TubeShading F) (x : Point3) :
    TubeSubfamily F :=
  TubeSubfamily.fromFinset F (shadingIncidentIndices Y x)

lemma shadingIncidentSubfamily_nonempty
    {delta : ℝ} {F : TubeFamily delta}
    (Y : TubeShading F) {x : Point3}
    (hx : x ∈ Y.union) :
    (shadingIncidentSubfamily Y x).Nonempty := by
  rcases hx with ⟨i, hi⟩
  change 0 < (shadingIncidentIndices Y x).card
  exact Finset.card_pos.mpr
    ⟨i, (mem_shadingIncidentIndices_iff Y x i).2 hi⟩

/--
Raw corrected Definition 2.2 construction structure.

The historical single `uniformity` field controls the ambient full fibers,
every pointwise incident full-fiber cover, the accepted Definition 2.1(iv)
Frostman and `deltaMax` profiles, and comparison of pointwise branching
numbers. It is retained for internal proof algebra, but it is not the
paper-facing distinction between finite-grid `∼` and all-real `≈`.
No parent assignment is stored in this public full-fiber structure.
-/
structure PointwiseFullFiberUniformTubeShading
    {delta A : ℝ} (F : TubeFamily delta)
    (Y : TubeShading F) (hdelta_le_one : delta ≤ 1) where
  coarse :
    ∀ r : UniformScaleIndex delta,
      TubeFamily (uniformScale delta hdelta_le_one r).1
  coarseDistinct :
    ∀ r, (coarse r).IsEssentiallyDistinct
  covered :
    ∀ r, ∀ i : Fin F.card,
      ∃ j : Fin (coarse r).card,
        (F.tube i).carrier ⊆
          dilatedTubeCarrier A ((coarse r).tube j)
  uniformity : ENNReal
  oneLeUniformity : 1 ≤ uniformity
  uniformityNeTop : uniformity ≠ ⊤
  uniform :
    ∀ r,
      GeometricFullContainmentFibersAreCUniform
        (A := A) F (coarse r) uniformity
  frostmanProfilesUniform :
    ∀ r,
      GeometricFullContainmentFrostmanProfilesAreCUniform
        (A := A) F (coarse r) uniformity
  deltaMaxProfilesUniform :
    ∀ r,
      GeometricFullContainmentDeltaMaxProfilesAreCUniform
        (A := A) F (coarse r) uniformity
  incidentFine :
    ∀ x, x ∈ Y.union → TubeSubfamily F
  incidentFine_image :
    ∀ x (hx : x ∈ Y.union),
      Finset.image (incidentFine x hx).embedding Finset.univ =
        shadingIncidentIndices Y x
  incidentCoarse :
    ∀ x, x ∈ Y.union →
      ∀ r : UniformScaleIndex delta,
        TubeFamily (uniformScale delta hdelta_le_one r).1
  incidentCoarseDistinct :
    ∀ x (hx : x ∈ Y.union) r,
      (incidentCoarse x hx r).IsEssentiallyDistinct
  incidentCovered :
    ∀ x (hx : x ∈ Y.union) r,
      ∀ i : Fin (incidentFine x hx).family.card,
        ∃ j : Fin (incidentCoarse x hx r).card,
          ((incidentFine x hx).family.tube i).carrier ⊆
            dilatedTubeCarrier A ((incidentCoarse x hx r).tube j)
  incidentUniform :
    ∀ x (hx : x ∈ Y.union) r,
      GeometricFullContainmentFibersAreCUniform
        (A := A) (incidentFine x hx).family
          (incidentCoarse x hx r) uniformity
  incidentFrostmanProfilesUniform :
    ∀ x (hx : x ∈ Y.union) r,
      GeometricFullContainmentFrostmanProfilesAreCUniform
        (A := A) (incidentFine x hx).family
          (incidentCoarse x hx r) uniformity
  incidentDeltaMaxProfilesUniform :
    ∀ x (hx : x ∈ Y.union) r,
      GeometricFullContainmentDeltaMaxProfilesAreCUniform
        (A := A) (incidentFine x hx).family
          (incidentCoarse x hx r) uniformity
  incidentBranchingNumbersComparable :
    ∀ x (hx : x ∈ Y.union) y (hy : y ∈ Y.union) r,
      ComparableBy uniformity
        (geometricFullContainmentBranchingNumber
          (A := A) (incidentFine x hx).family
            (incidentCoarse x hx r))
        (geometricFullContainmentBranchingNumber
          (A := A) (incidentFine y hy).family
            (incidentCoarse y hy r))

/--
Paper-faithful finite-grid Definition 2.1 data.

The branching constant is an absolute `∼` constant fixed before the runtime
scale and family. The accepted Frostman and `deltaMax` profiles carry the
separate subpolynomial loss allowed by Definition 2.1(iv).
-/
structure PaperGridFullFiberUniformTubeStructure
    {delta A : ℝ}
    (branchingConstant : ENNReal)
    (profileEpsilon : ℝ)
    (F : TubeFamily delta)
    (hdelta_le_one : delta ≤ 1) where
  one_le_branchingConstant : 1 ≤ branchingConstant
  branchingConstant_ne_top : branchingConstant ≠ ⊤
  coarse :
    ∀ r : UniformScaleIndex delta,
      TubeFamily (uniformScale delta hdelta_le_one r).1
  coarseDistinct :
    ∀ r, (coarse r).IsEssentiallyDistinct
  covered :
    ∀ r, ∀ i : Fin F.card,
      ∃ j : Fin (coarse r).card,
        (F.tube i).carrier ⊆
          dilatedTubeCarrier A ((coarse r).tube j)
  ambientBranchingUniform :
    ∀ r,
      GeometricFullContainmentFibersAreCUniform
        (A := A) F (coarse r) branchingConstant
  ambientFrostmanProfilesApprox :
    ∀ r,
      GeometricFullContainmentFrostmanProfilesAreCUniform
        (A := A) F (coarse r)
          (Kakeya.realRpowENN delta (-profileEpsilon))
  ambientDeltaMaxProfilesApprox :
    ∀ r,
      GeometricFullContainmentDeltaMaxProfilesAreCUniform
        (A := A) F (coarse r)
          (Kakeya.realRpowENN delta (-profileEpsilon))

/--
Paper-faithful finite-grid Definition 2.2 data.

The paper uses `∼` on the distinguished grid, so `branchingConstant` is fixed
before the runtime scale and controls branching with an absolute factor.
The accepted Definition 2.1(iv) Frostman and `deltaMax` profiles are allowed
the explicit subpolynomial loss `delta⁻ᵖʳᵒᶠⁱˡᵉᴱᵖˢⁱˡᵒⁿ`.

The underlying quantitative structure is retained only as construction data;
its single historical `uniformity` field is not the paper-facing semantic
constant.
-/
structure PaperGridPointwiseFullFiberUniformTubeShading
    {delta A : ℝ}
    (branchingConstant : ENNReal)
    (profileEpsilon : ℝ)
    (F : TubeFamily delta)
    (Y : TubeShading F)
    (hdelta_le_one : delta ≤ 1) where
  raw :
    PointwiseFullFiberUniformTubeShading
      (A := A) F Y hdelta_le_one
  one_le_branchingConstant : 1 ≤ branchingConstant
  branchingConstant_ne_top : branchingConstant ≠ ⊤
  ambientBranchingUniform :
    ∀ r,
      GeometricFullContainmentFibersAreCUniform
        (A := A) F (raw.coarse r) branchingConstant
  ambientFrostmanProfilesApprox :
    ∀ r,
      GeometricFullContainmentFrostmanProfilesAreCUniform
        (A := A) F (raw.coarse r)
          (Kakeya.realRpowENN delta (-profileEpsilon))
  ambientDeltaMaxProfilesApprox :
    ∀ r,
      GeometricFullContainmentDeltaMaxProfilesAreCUniform
        (A := A) F (raw.coarse r)
          (Kakeya.realRpowENN delta (-profileEpsilon))
  incidentBranchingUniform :
    ∀ x (hx : x ∈ Y.union) r,
      GeometricFullContainmentFibersAreCUniform
        (A := A) (raw.incidentFine x hx).family
          (raw.incidentCoarse x hx r) branchingConstant
  incidentFrostmanProfilesApprox :
    ∀ x (hx : x ∈ Y.union) r,
      GeometricFullContainmentFrostmanProfilesAreCUniform
        (A := A) (raw.incidentFine x hx).family
          (raw.incidentCoarse x hx r)
          (Kakeya.realRpowENN delta (-profileEpsilon))
  incidentDeltaMaxProfilesApprox :
    ∀ x (hx : x ∈ Y.union) r,
      GeometricFullContainmentDeltaMaxProfilesAreCUniform
        (A := A) (raw.incidentFine x hx).family
          (raw.incidentCoarse x hx r)
          (Kakeya.realRpowENN delta (-profileEpsilon))
  incidentBranchingNumbersComparable :
    ∀ x (hx : x ∈ Y.union) y (hy : y ∈ Y.union) r,
      ComparableBy branchingConstant
        (geometricFullContainmentBranchingNumber
          (A := A) (raw.incidentFine x hx).family
            (raw.incidentCoarse x hx r))
        (geometricFullContainmentBranchingNumber
          (A := A) (raw.incidentFine y hy).family
            (raw.incidentCoarse y hy r))

/--
Legacy quantitative finite-grid refinement retained for internal proof
compatibility.

Its one runtime `uniformity` field may depend on `epsilon` and `delta`, so this
is not the canonical paper Definition 2.2 `∼` interface. The corrected
paper-facing producer is
`PaperFiniteGridUniformPigeonholingStatement`, whose branching constant is
fixed before `epsilon`, `delta`, and the runtime family. Its structural
all-real extension is the separate
`PaperGridToAllRealDefinitionTwoTwoStatement`.

The selected shading is carried by one selected indexed tube subfamily. Its
public certificate contains only geometric full fibers; a proof may use
assigned covers privately while constructing the output.
-/
def PointwiseFullFiberUniformShadingRefinementStatement : Prop :=
  ∃ A : ℝ, 1 ≤ A ∧
    ∀ epsilon : ℝ, 0 < epsilon →
      ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
        ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
          ∀ F : TubeFamily delta,
            F.Nonempty →
            F.IsInUnitBall →
            F.IsEssentiallyDistinct →
            ∀ Y : TubeShading F, 0 < Y.mass →
              ∃ S : TubeSubfamily F,
              ∃ Y' : TubeShading S.family,
                S.Nonempty ∧
                (∀ i, Y'.carrier i ⊆ Y.carrier (S.embedding i)) ∧
                Kakeya.realRpowENN delta epsilon * Y.mass ≤ Y'.mass ∧
                ∃ hdelta_le_one : delta ≤ 1,
                ∃ U :
                    PointwiseFullFiberUniformTubeShading
                      (A := A) S.family Y' hdelta_le_one,
                  U.uniformity ≤
                    Kakeya.realRpowENN delta (-epsilon)

end Kakeya.Streamlined
