import MyLeanRepo.Kakeya.BorsukUlam
import MyLeanRepo.Kakeya.CV.PolynomialMollification
import MyLeanRepo.Kakeya.CV.ShapeSpace

/-!
# Frozen statements for Carbery--Valdimarsson

These propositions isolate the six first-wave proof targets for the
three-dimensional endpoint multilinear Kakeya theorem.
-/

noncomputable section

open MeasureTheory TopCat
open scoped BigOperators ENNReal NNReal Real

namespace Kakeya.CV

/--
Finite weighted form of CV Proposition 2 in the trilinear case.

The hypothesis supplies normalized local factorizations with one unit of
budget along each tube.  The conclusion is the endpoint square-root estimate.
-/
def PreliminaryReductionStatement : Prop :=
  ∀ (Cube T₁ T₂ T₃ : Type*) [Fintype Cube] [Fintype T₁] [Fintype T₂] [Fintype T₃],
    ∀ weight : Cube → T₁ → T₂ → T₃ → ℝ≥0,
      (∀ M : Cube → ℝ≥0, (∑ q, M q ^ 3) = 1 →
        ∃ (S₁ : Cube → T₁ → ℝ≥0) (S₂ : Cube → T₂ → ℝ≥0)
            (S₃ : Cube → T₃ → ℝ≥0),
          (∀ q t₁ t₂ t₃,
            weight q t₁ t₂ t₃ * M q ^ 3 ≤
              S₁ q t₁ * S₂ q t₂ * S₃ q t₃) ∧
          (∀ t₁, ∑ q, S₁ q t₁ ≤ 1) ∧
          (∀ t₂, ∑ q, S₂ q t₂ ≤ 1) ∧
          (∀ t₃, ∑ q, S₃ q t₃ ≤ 1)) →
      (∑ q, NNReal.sqrt (∑ t₁, ∑ t₂, ∑ t₃, weight q t₁ t₂ t₃)) ≤
        NNReal.sqrt
          ((Fintype.card T₁ * Fintype.card T₂ * Fintype.card T₃ : ℕ) : ℝ≥0)

/--
Three-dimensional form of Guth's polynomial cylinder estimate (CV Lemma 1).
-/
def PolynomialCylinderEstimateStatement : Prop :=
  ∃ C : ℝ≥0, 0 < C ∧
    ∀ (k : ℕ) (p : MvPolynomial (Fin 3) ℝ) (a e : Point 3),
      p ≠ 0 →
      HasNegligibleSingularSet p →
      p.totalDegree ≤ k →
      ‖e‖ = 1 →
      directionalSurfaceArea e p (polynomialZeroSet p ∩ unitTube a e) ≤
        (C : ℝ≥0∞) * (k : ℝ≥0∞)

/--
Convex-geometric core of CV Lemma 2.

For a centrally symmetric convex body `K`, the points
`(s i)⁻¹ • v i ∈ K` force a lower bound for `volume K`, equivalently the
displayed upper bound for visibility.
-/
def VisibilityDirectionalBoundStatement : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (K : Set (Point 3)),
      JohnEllipsoid.IsConvexBody K →
      (∀ x, x ∈ K → -x ∈ K) →
      ∀ (v : Fin 3 → Point 3) (s : Fin 3 → ℝ),
        (∀ i, ‖v i‖ = 1) →
        (∀ i, 0 < s i) →
        (∀ i, (s i)⁻¹ • v i ∈ K) →
        Real.rpow (tripleVolume v) (1 / 3 : ℝ) *
            Real.rpow (volume K).toReal (-1 / 3 : ℝ) ≤
          C * Real.rpow (∏ i, s i) (1 / 3 : ℝ)

/--
Finite-colour ellipsoid net with the separation margin required by CV Lemma 10.

The selected ellipsoid is `α`-close to the convex body, while two ellipsoids of
the same colour that are `α³`-close about a common center must coincide.
-/
def StableEllipsoidColouringStatement : Prop :=
  ∃ (α : ℝ) (N : ℕ) (net : Set EllipsoidParameter)
      (colour : EllipsoidParameter → Fin N),
    1 < α ∧
    0 < N ∧
    (∀ E ∈ net, E.1 = 0) ∧
    (∀ K : Set (Point 3),
      JohnEllipsoid.IsConvexBody K →
      (∀ x, x ∈ K → -x ∈ K) →
      ∃ E, E ∈ net ∧
        AreHomotheticallyCloseAt 0 α K (ellipsoidCarrier E)) ∧
    (∀ E₁ E₂ : EllipsoidParameter,
      E₁ ∈ net →
      E₂ ∈ net →
      colour E₁ = colour E₂ →
      AreHomotheticallyCloseAt 0 (α ^ 3)
        (ellipsoidCarrier E₁) (ellipsoidCarrier E₂) →
      E₁ = E₂)

/--
Principal-axis weighted form of CV Lemma 9.

For pairwise-disjoint translates of an ellipsoid with principal directions
`b i` and semiaxes `ℓ i`, every 40/40 cut contributes a fixed multiple of
`η² * ∏ i, ℓ i` to the weighted directional surface area.
-/
def PrincipalAxesManyBisectionsStatement : Prop :=
  ∃ C : ℝ≥0, 0 < C ∧
    ∀ (ι : Type*) [Fintype ι] (p : MvPolynomial (Fin 3) ℝ)
        (A : Point 3 ≃ₗ[ℝ] Point 3) (η : ℝ) (z : ι → Point 3)
        (b : OrthonormalBasis (Fin 3) ℝ (Point 3)) (ℓ : Fin 3 → ℝ),
      p ≠ 0 →
      HasNegligibleSingularSet p →
      0 < η →
      η ≤ 1 →
      (∀ i, 0 < ℓ i) →
      (∀ i, A ((EuclideanSpace.basisFun (Fin 3) ℝ) i) = ℓ i • b i) →
      Pairwise (fun i j =>
        Disjoint (scaledEllipsoid A η (z i))
          (scaledEllipsoid A η (z j))) →
      (∀ i, PolynomialCutsAtLeast p (scaledEllipsoid A η (z i))
        (2 / 5 : ℝ≥0∞)) →
      (Fintype.card ι : ℝ≥0∞) *
          ENNReal.ofReal (η ^ 2 * ∏ i, ℓ i) *
          codimensionOneMeasure 3 (unitSphere 3) ≤
        (C : ℝ≥0∞) *
          ∑ i, ENNReal.ofReal (ℓ i) *
            directionalSurfaceArea (b i) p
              (polynomialZeroSet p ∩ ⋃ j, scaledEllipsoid A η (z j))

/--
Every centered ellipsoid admits a principal-axis parameterization with positive
semiaxes and the same carrier.
-/
def PrincipalAxesRepresentationStatement : Prop :=
  ∀ A : Point 3 ≃ₗ[ℝ] Point 3,
    ∃ (A' : Point 3 ≃ₗ[ℝ] Point 3)
        (b : OrthonormalBasis (Fin 3) ℝ (Point 3)) (ℓ : Fin 3 → ℝ),
      (∀ i, 0 < ℓ i) ∧
      (∀ i, A' ((EuclideanSpace.basisFun (Fin 3) ℝ) i) = ℓ i • b i) ∧
      JohnEllipsoid.ellipsoid 0 A' = JohnEllipsoid.ellipsoid 0 A

/--
One coefficient radius works simultaneously for every normalized center and a
fixed finite family of regions.

The conclusion is conditional region by region: whenever the center
polynomial exactly bisects one region, every parameter in the common ball
makes a 40/40 cut of that region.
-/
def UniformFiniteBisectionStabilityStatement : Prop :=
  ∀ (k : ℕ) (P : PolynomialParameterization k)
      (ι : Type*) [Fintype ι] (regions : ι → Set (Point 3)),
    (∀ i, MeasurableSet (regions i)) →
    (∀ i, volume (regions i) < ⊤) →
    ∃ δ : ℝ, 0 < δ ∧
      ∀ x ∈ normalizedPolynomialParameters P,
        ∀ y ∈ Metric.ball x δ, ∀ i,
          PolynomialBisects (parameterPolynomial P x) (regions i) →
          PolynomialCutsAtLeast (parameterPolynomial P y) (regions i)
            (2 / 5 : ℝ≥0∞)

/--
Every principal semiaxis of an ellipsoid selected homothetically outside a
concrete mollified visibility body has the corresponding directional-area
budget.

This is the convex-geometric bridge used when the weighted output of the
principal-axis many-bisections estimate is summed over selected atoms.
-/
def PrincipalAxesMollifiedDirectionalBudgetStatement : Prop :=
  ∀ (k : ℕ) (P : PolynomialParameterization k)
      (U : Set (Point 3)) (ε : ℝ) (x : CoefficientSpace P.dim)
      (α : ℝ) (A : Point 3 ≃ₗ[ℝ] Point 3)
      (b : OrthonormalBasis (Fin 3) ℝ (Point 3)) (ℓ : Fin 3 → ℝ),
    0 ≤ α →
    (∀ i, 0 ≤ ℓ i) →
    (∀ i, A ((EuclideanSpace.basisFun (Fin 3) ℝ) i) = ℓ i • b i) →
    AreHomotheticallyCloseAt 0 α
      (concreteMollifiedVisibilityBody P ε x U)
      (JohnEllipsoid.ellipsoid 0 A) →
    ∀ i,
      ℓ i * concreteMollifiedDirectionalArea P ε x (b i) U ≤ α

/--
Centered ellipsoids with uniformly bounded outer radius and a positive volume
lower bound occupy a bounded band in inverse-shape space.

Together with separation of `shapeNet`, this is the finite-band input needed
to choose one mollification radius for the finitely many palette ellipsoids
relevant to fixed dyadic levels.
-/
def BoundedEllipsoidShapeBandStatement : Prop :=
  ∀ (R v : ℝ),
    0 < R →
    0 < v →
    ∃ C : ℝ, 0 < C ∧
      ∀ A : Point 3 ≃ₗ[ℝ] Point 3,
        JohnEllipsoid.ellipsoid 0 A ⊆ Metric.closedBall 0 R →
        ENNReal.ofReal v ≤ volume (JohnEllipsoid.ellipsoid 0 A) →
        ShapeSpace.ShapeClose C
          (1 : Point 3 ≃ₗ[ℝ] Point 3) A.symm

/--
Every bounded radius/positive volume band of a stable finite-colour centered
ellipsoid palette is finite.

This is the exact finiteness used to take a minimum of the finitely many
coefficient-neighborhood radii supplied by finite bisection stability.
-/
def StableEllipsoidPaletteBandFinitenessStatement : Prop :=
  ∀ (α : ℝ) (N : ℕ) (net : Set EllipsoidParameter)
      (colour : EllipsoidParameter → Fin N),
    1 < α →
    (∀ E ∈ net, E.1 = 0) →
    (∀ E₁ ∈ net, ∀ E₂ ∈ net,
      colour E₁ = colour E₂ →
      AreHomotheticallyCloseAt 0 (α ^ 3)
        (ellipsoidCarrier E₁) (ellipsoidCarrier E₂) →
      E₁ = E₂) →
    ∀ (R v : ℝ),
      0 < R →
      0 < v →
      Set.Finite
        {E | E ∈ net ∧
          ellipsoidCarrier E ⊆ Metric.closedBall 0 R ∧
          ENNReal.ofReal v ≤ volume (ellipsoidCarrier E)}

/-- CV Lemma 3: a small directional area forces visibility to be degree-controlled. -/
def VisibilityDegreeBoundStatement : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (k : ℕ) (p : MvPolynomial (Fin 3) ℝ)
        (Q : Set (Point 3)) (c e : Point 3),
      1 ≤ k →
      p ≠ 0 →
      HasNegligibleSingularSet p →
      p.totalDegree ≤ k →
      ‖e‖ = 1 →
      Q ⊆ Metric.closedBall c 1 →
      directionalSurfaceArea e p (polynomialZeroSet p ∩ Q) ≤ 1 →
      Real.rpow (visibility p (polynomialZeroSet p ∩ Q)) (3 / 2 : ℝ) ≤
        C * k

/--
Continuity of convolution with a normalized ball indicator in finite-dimensional
coefficient space, the analytic input for mollifying directional surface area.
-/
def MollifiedSurfaceContinuityStatement : Prop :=
  ∀ (N : ℕ) (ε : ℝ) (f : CoefficientSpace N → ℝ),
    0 < ε →
    LocallyIntegrable f volume →
    Continuous (ballAverage ε f)

/--
CV Lemma 10: a same-colour ellipsoid selected from a separated net is locally
constant along a convergent sequence of visibility bodies.
-/
def EllipsoidSelectionStabilityStatement : Prop :=
  ∀ (α : ℝ) (N : ℕ) (net : Set EllipsoidParameter)
      (colour : EllipsoidParameter → Fin N) (z : Point 3)
      (K : Set (Point 3)) (Kseq : ℕ → Set (Point 3))
      (E : EllipsoidParameter) (Eseq : ℕ → EllipsoidParameter),
    1 < α →
    HomotheticConvergesAt z Kseq K →
    E ∈ net →
    (∀ m, Eseq m ∈ net) →
    (∀ m, colour (Eseq m) = colour E) →
    AreHomotheticallyCloseAt z α K (ellipsoidCarrier E) →
    (∀ m, AreHomotheticallyCloseAt z α (Kseq m)
      (ellipsoidCarrier (Eseq m))) →
    (∀ E₁ ∈ net, ∀ E₂ ∈ net,
      colour E₁ = colour E₂ →
      AreHomotheticallyCloseAt z (α ^ 3)
        (ellipsoidCarrier E₁) (ellipsoidCarrier E₂) →
      E₁ = E₂) →
    ∀ᶠ m in Filter.atTop,
      Eseq m = E

/--
Finite antipodal bad-set cover used in the final polynomial visibility
argument.  The cardinality bound is the output of the dyadic counting step.
-/
def PolynomialBadSetCoverStatement : Prop :=
  ∀ (N : ℕ) (I : Type*) [Fintype I],
    Fintype.card I ≤ N →
    ∀ (A : I → Set (TopCat.sphere.{0} N))
        (bad : Set (TopCat.sphere.{0} N)),
      (∀ i, A i ∩ closure (TopCat.sphereAntipodal N '' A i) = ∅) →
      bad ⊆ ⋃ i, (A i ∪ TopCat.sphereAntipodal N '' A i) →
      ∃ x : TopCat.sphere.{0} N, x ∉ bad

/--
The singular locus of a nonzero squarefree polynomial hypersurface in
three-dimensional real space has zero two-dimensional Hausdorff measure.
-/
def SquarefreeSingularSetNullStatement : Prop :=
  ∀ p : MvPolynomial (Fin 3) ℝ,
    p ≠ 0 →
    Squarefree p →
    HasNegligibleSingularSet p

/--
The bounded-degree polynomial subspace has the expected finite-dimensional
Euclidean coordinate model.
-/
def PolynomialParameterSpaceStatement : Prop :=
  ∀ k : ℕ,
    ∃ P : PolynomialParameterization k,
      P.dim = Nat.choose (k + 3) 3

/--
Nonzero squarefree polynomials have full measure in every positive-radius ball
of bounded-degree coefficient space.
-/
def GenericPolynomialRegularityStatement : Prop :=
  ∀ (k : ℕ) (P : PolynomialParameterization k)
      (x : CoefficientSpace P.dim) (ε : ℝ),
    0 < ε →
    ∀ᵐ y ∂(volume.restrict (Metric.ball x ε)),
      parameterPolynomial P y ≠ 0 ∧ Squarefree (parameterPolynomial P y)

/--
For a measurable bounded spatial region, directional surface area is almost
everywhere measurable as a function of polynomial coefficients.

Only almost-everywhere measurability is required.  A pointwise slab-limit
identity is false for general measurable regions whose boundary can contain a
positive-area piece of one exceptional zero set.
-/
def CoefficientSurfaceFunctionalAEMeasurabilityStatement : Prop :=
  ∀ (k : ℕ) (P : PolynomialParameterization k)
      (U : Set (Point 3)) (c : Point 3),
    MeasurableSet U →
    U ⊆ Metric.closedBall c 1 →
    ∀ u : Point 3,
      AEMeasurable (coefficientSurfaceFunctional P u U) volume

/--
The principal-axis 40/40 many-bisections estimate survives coefficient-ball
averaging.

The pointwise theorem is applied at almost every nonzero squarefree parameter.
The polynomial cylinder estimate makes every directional surface area finite,
so its `ENNReal.toReal` value is faithful, and local integrability permits
conversion of the pointwise estimate into the normalized Bochner average used
by `concreteMollifiedDirectionalArea`.
-/
def PrincipalAxesMollifiedManyBisectionsStatement.{u} : Prop :=
  PrincipalAxesManyBisectionsStatement.{u} →
  GenericPolynomialRegularityStatement →
  SquarefreeSingularSetNullStatement →
  PolynomialCylinderEstimateStatement →
  ∃ C : ℝ≥0, 0 < C ∧
    ∀ (k : ℕ) (P : PolynomialParameterization k)
        (U : Set (Point 3)) (c : Point 3) (ε : ℝ)
        (x : CoefficientSpace P.dim)
        (ι : Type u) [Fintype ι]
        (A : Point 3 ≃ₗ[ℝ] Point 3) (η : ℝ) (z : ι → Point 3)
        (b : OrthonormalBasis (Fin 3) ℝ (Point 3)) (ℓ : Fin 3 → ℝ),
      MeasurableSet U →
      U ⊆ Metric.closedBall c 1 →
      0 < ε →
      (∀ i, LocallyIntegrable
        (coefficientSurfaceFunctional P (b i) U) volume) →
      0 < η →
      η ≤ 1 →
      (∀ i, 0 < ℓ i) →
      (∀ i,
        A ((EuclideanSpace.basisFun (Fin 3) ℝ) i) = ℓ i • b i) →
      (∀ j, scaledEllipsoid A η (z j) ⊆ U) →
      Pairwise (fun i j =>
        Disjoint (scaledEllipsoid A η (z i))
          (scaledEllipsoid A η (z j))) →
      (∀ y ∈ Metric.ball x ε, ∀ j,
        PolynomialCutsAtLeast (parameterPolynomial P y)
          (scaledEllipsoid A η (z j)) (2 / 5 : ℝ≥0∞)) →
      (Fintype.card ι : ℝ≥0∞) *
          ENNReal.ofReal (η ^ 2 * ∏ i, ℓ i) *
          codimensionOneMeasure 3 (unitSphere 3) ≤
        (C : ℝ≥0∞) *
          ∑ i, ENNReal.ofReal (ℓ i) *
            ENNReal.ofReal
              (concreteMollifiedDirectionalArea P ε x (b i) U)

/--
Concrete polynomial directional surface area is locally integrable in
coefficient coordinates, and normalized ball averaging is continuous.
-/
def ConcreteMollifiedSurfaceStatement : Prop :=
  ∀ (k : ℕ) (P : PolynomialParameterization k)
      (U : Set (Point 3)) (c : Point 3) (ε : ℝ),
    MeasurableSet U →
    U ⊆ Metric.closedBall c 1 →
    0 < ε →
    (∀ u : Point 3,
      LocallyIntegrable (coefficientSurfaceFunctional P u U) volume) ∧
    (∀ u : Point 3,
      Continuous (fun x =>
        concreteMollifiedDirectionalArea P ε x u U))

/--
The concrete mollified directional mass produces a centrally symmetric convex
body with nonempty interior, suitable for John ellipsoid selection.
-/
def ConcreteMollifiedVisibilityStatement : Prop :=
  ∀ (k : ℕ) (P : PolynomialParameterization k)
      (U : Set (Point 3)) (c : Point 3) (ε : ℝ)
      (x : CoefficientSpace P.dim),
    MeasurableSet U →
    U ⊆ Metric.closedBall c 1 →
    0 < ε →
    JohnEllipsoid.IsConvexBody
      (concreteMollifiedVisibilityBody P ε x U) ∧
    (∀ u, u ∈ concreteMollifiedVisibilityBody P ε x U →
      -u ∈ concreteMollifiedVisibilityBody P ε x U)

/--
Concrete visibility bodies vary continuously in the homothetic topology when
their coefficient centers converge.
-/
def ConcreteVisibilityHomotheticContinuityStatement : Prop :=
  ∀ (k : ℕ) (P : PolynomialParameterization k)
      (U : Set (Point 3)) (c : Point 3) (ε : ℝ)
      (x : CoefficientSpace P.dim) (xseq : ℕ → CoefficientSpace P.dim),
    MeasurableSet U →
    U ⊆ Metric.closedBall c 1 →
    0 < ε →
    Filter.Tendsto xseq Filter.atTop (nhds x) →
    HomotheticConvergesAt 0
      (fun m => concreteMollifiedVisibilityBody P ε (xseq m) U)
      (concreteMollifiedVisibilityBody P ε x U)

/--
Positive-visibility bad parameters admit a dyadic decomposition and a
finite-colour choice of nearby ellipsoids.
-/
def DyadicPolynomialBadSetDecompositionStatement : Prop :=
  ∃ (α : ℝ) (N : ℕ) (net : Set EllipsoidParameter)
      (colour : EllipsoidParameter → Fin N),
    1 < α ∧
    0 < N ∧
    (∀ E ∈ net, E.1 = 0) ∧
    (∀ (E₁ E₂ : EllipsoidParameter),
      E₁ ∈ net →
      E₂ ∈ net →
      colour E₁ = colour E₂ →
      AreHomotheticallyCloseAt 0 (α ^ 3)
        (ellipsoidCarrier E₁) (ellipsoidCarrier E₂) →
      E₁ = E₂) ∧
    ∀ (k : ℕ) (P : PolynomialParameterization k)
        (ε : ℝ) (c : Point 3) (M : ℝ),
      0 < ε →
      0 < M →
      ∃ selected : CoefficientSpace P.dim → EllipsoidParameter,
      (∀ x, selected (-x) = selected x) ∧
      (∀ x, x ∈ concretePolynomialBadSet P ε (unitCube c) M →
        0 < concreteMollifiedVisibility P ε x (unitCube c) →
        selected x ∈ net ∧
          AreHomotheticallyCloseAt 0 α
            (concreteMollifiedVisibilityBody P ε x (unitCube c))
            (ellipsoidCarrier (selected x))) ∧
      {x | x ∈ concretePolynomialBadSet P ε (unitCube c) M ∧
        0 < concreteMollifiedVisibility P ε x (unitCube c)} =
        ⋃ r : ℕ, ⋃ θ : Fin N,
          {x | x ∈ concretePolynomialBadLayer P ε (unitCube c) M r ∧
            colour (selected x) = θ}

/--
Finite-level form of the positive-visibility dyadic decomposition.

The uniform lower visibility of the John-eligible body makes all sufficiently
large dyadic levels empty, producing the finite index needed by the
Borsuk--Ulam atom count.
-/
def FiniteDyadicPolynomialBadSetDecompositionStatement : Prop :=
  ∃ (α : ℝ) (N : ℕ) (net : Set EllipsoidParameter)
      (colour : EllipsoidParameter → Fin N),
    1 < α ∧
    0 < N ∧
    (∀ E ∈ net, E.1 = 0) ∧
    (∀ (E₁ E₂ : EllipsoidParameter),
      E₁ ∈ net →
      E₂ ∈ net →
      colour E₁ = colour E₂ →
      AreHomotheticallyCloseAt 0 (α ^ 3)
        (ellipsoidCarrier E₁) (ellipsoidCarrier E₂) →
      E₁ = E₂) ∧
    ∀ (k : ℕ) (P : PolynomialParameterization k)
        (ε : ℝ) (c : Point 3) (M : ℝ),
      0 < ε →
      0 < M →
      ∃ (selected : CoefficientSpace P.dim → EllipsoidParameter)
          (levels : ℕ),
      (∀ x, selected (-x) = selected x) ∧
      (∀ x, x ∈ concretePolynomialBadSet P ε (unitCube c) M →
        0 < concreteMollifiedVisibility P ε x (unitCube c) →
        selected x ∈ net ∧
          AreHomotheticallyCloseAt 0 α
            (concreteMollifiedVisibilityBody P ε x (unitCube c))
            (ellipsoidCarrier (selected x))) ∧
      {x | x ∈ concretePolynomialBadSet P ε (unitCube c) M ∧
        0 < concreteMollifiedVisibility P ε x (unitCube c)} =
        ⋃ r : Fin levels, ⋃ θ : Fin N,
          {x | x ∈ concretePolynomialBadLayer P ε (unitCube c) M (r : ℕ) ∧
            colour (selected x) = θ}

/--
A small centered ellipsoid admits a volume-efficient finite packing by
pairwise-disjoint translates inside the unit ball.
-/
def EllipsoidTranslatePackingStatement : Prop :=
  ∃ C : ℝ≥0, 0 < C ∧
    ∀ (A : Point 3 ≃ₗ[ℝ] Point 3) (η : ℝ),
      0 < η →
      scaledEllipsoid A (2 * η) 0 ⊆ unitBall 3 →
      ∃ (n : ℕ) (z : Fin n → Point 3),
        (∀ i, scaledEllipsoid A η (z i) ⊆ unitBall 3) ∧
        Pairwise (fun i j =>
          Disjoint (scaledEllipsoid A η (z i))
            (scaledEllipsoid A η (z j))) ∧
        volume (unitBall 3) / volume (scaledEllipsoid A η 0) ≤
          (C : ℝ≥0∞) * n ∧
        (n : ℝ≥0∞) ≤
          (C : ℝ≥0∞) * volume (unitBall 3) /
            volume (scaledEllipsoid A η 0)

/--
Volume-efficient packing of a sufficiently small centered ellipsoid into an
actual closed unit cube.

The margin hypothesis is expressed in the normalized unit ball before the
affine map that sends its inscribed half-ball into the cube.
-/
def UnitCubeEllipsoidPackingStatement : Prop :=
  ∃ C : ℝ≥0, 0 < C ∧
    ∀ (A : Point 3 ≃ₗ[ℝ] Point 3) (η : ℝ) (c : Point 3),
      0 < η →
      scaledEllipsoid A (4 * η) 0 ⊆ unitBall 3 →
      ∃ (n : ℕ) (z : Fin n → Point 3),
        (∀ i, scaledEllipsoid A η (z i) ⊆ unitCube c) ∧
        Pairwise (fun i j =>
          Disjoint (scaledEllipsoid A η (z i))
            (scaledEllipsoid A η (z j))) ∧
        volume (unitCube c) / volume (scaledEllipsoid A η 0) ≤
          (C : ℝ≥0∞) * n ∧
        (n : ℝ≥0∞) ≤
          (C : ℝ≥0∞) * volume (unitCube c) /
            volume (scaledEllipsoid A η 0)

/--
A finite palette of centered ellipsoid shapes admits one common positive scale,
and at that scale every palette element has a fixed volume-efficient translate
packing in every unit cube.
-/
def FinitePaletteTranslatePackingStatement : Prop :=
  ∃ C : ℝ≥0, 0 < C ∧
    ∀ palette : Set EllipsoidParameter,
      Set.Finite palette →
      (∀ E ∈ palette, E.1 = 0) →
      ∀ (R ηMax : ℝ),
      0 < R →
      0 < ηMax →
      (∀ E ∈ palette,
        ellipsoidCarrier E ⊆ Metric.closedBall 0 R) →
      let η := min ηMax 1 / (8 * max R 1)
      0 < η ∧
      η ≤ ηMax ∧
      ∀ (E : EllipsoidParameter), E ∈ palette →
        ∀ c : Point 3,
          ∃ (n : ℕ) (z : Fin n → Point 3),
            (∀ i, scaledEllipsoid E.2 η (z i) ⊆ unitCube c) ∧
            Pairwise (fun i j =>
              Disjoint (scaledEllipsoid E.2 η (z i))
                (scaledEllipsoid E.2 η (z j))) ∧
            volume (unitCube c) / volume (scaledEllipsoid E.2 η 0) ≤
              (C : ℝ≥0∞) * n ∧
            (n : ℝ≥0∞) ≤
              (C : ℝ≥0∞) * volume (unitCube c) /
                volume (scaledEllipsoid E.2 η 0)

/--
Three-dimensional volume comparison for a centered ellipsoid homothetically
close to a convex body.
-/
def CenteredHomotheticVolumeComparisonStatement : Prop :=
  ∀ (α : ℝ) (K : Set (Point 3)) (A : Point 3 ≃ₗ[ℝ] Point 3),
    1 ≤ α →
    JohnEllipsoid.IsConvexBody K →
    AreHomotheticallyCloseAt 0 α K (JohnEllipsoid.ellipsoid 0 A) →
    ENNReal.ofReal (α⁻¹ ^ 3) * volume K ≤
      volume (JohnEllipsoid.ellipsoid 0 A) ∧
    volume (JohnEllipsoid.ellipsoid 0 A) ≤
      ENNReal.ofReal (α ^ 3) * volume K

/--
Locally constant selected regions and nonvanishing polynomial boundaries force
strict sign classes to be separated from their antipodal closures.
-/
def AntipodalSignSeparationStatement : Prop :=
  ∀ (k : ℕ) (P : PolynomialParameterization k)
      (selectedRegion : CoefficientSpace P.dim → Set (Point 3))
      (D : Set (CoefficientSpace P.dim)),
    (∀ x, x ∈ D → -x ∈ D) →
    (∀ x, x ∈ D → selectedRegion (-x) = selectedRegion x) →
    (∀ x, x ∈ D → MeasurableSet (selectedRegion x)) →
    (∀ x, x ∈ D → volume (selectedRegion x) < ⊤) →
    (∀ x, x ∈ D → parameterPolynomial P x ≠ 0) →
    (∀ x, x ∈ D →
      ¬PolynomialBisects (parameterPolynomial P x) (selectedRegion x)) →
    (∀ (xseq : ℕ → CoefficientSpace P.dim) x,
      (∀ m, xseq m ∈ D) →
      x ∈ D →
      Filter.Tendsto xseq Filter.atTop (nhds x) →
      ∀ᶠ m in Filter.atTop, selectedRegion (xseq m) = selectedRegion x) →
    positiveSignClass P selectedRegion D ∩
      closure ((fun x => -x) '' positiveSignClass P selectedRegion D) = ∅

/--
The normalized coefficient sphere is the standard sphere of one lower
dimension, with compatible antipodal maps.
-/
def NormalizedPolynomialSphereStatement : Prop :=
  ∀ (k : ℕ) (P : PolynomialParameterization k),
    0 < P.dim →
    ∃ h : normalizedPolynomialParameters P ≃ₜ
        TopCat.sphere.{0} (P.dim - 1),
      ∀ x,
        h (normalizedParameterAntipodal P x) =
          TopCat.sphereAntipodal (P.dim - 1) (h x)

/--
The finite atom sets generated by dyadic layers and colours satisfy the
geometric-series cardinality bound required by Borsuk--Ulam.
-/
def BadSetAtomCardinalityStatement : Prop :=
  ∀ (Cube Colour : Type*) [Fintype Cube] [Fintype Colour]
      (levels : Cube → ℕ)
      (Atom : ∀ q, Fin (levels q) → Colour → Type*)
      [∀ q r c, Fintype (Atom q r c)]
      (M : Cube → ℝ≥0) (D : ℝ≥0),
    (∀ q r c,
      (Fintype.card (Atom q r c) : ℝ≥0) ≤
        (1 / 8 : ℝ≥0) ^ (r : ℕ) * M q ^ 3) →
    (∑ q, M q ^ 3) ≤ D →
    (Fintype.card (Σ q, Σ r, Σ c, Atom q r c) : ℝ≥0) ≤
      (Fintype.card Colour : ℝ≥0) * ((8 : ℝ≥0) / 7) * D

/-- The reusable output of finite CV bad-set atomization and Borsuk--Ulam. -/
def PolynomialBadSetAvoidanceConclusion.{u} : Prop :=
  ∃ Ccount Cvis : ℝ, 0 < Ccount ∧ 0 < Cvis ∧
    ∀ (Cube : Type u) [Fintype Cube]
        (k : ℕ) (P : PolynomialParameterization k)
        (center : Cube → Point 3) (M : Cube → ℝ≥0),
      0 < P.dim →
      Ccount * ∑ q, (M q : ℝ) ^ 3 < (P.dim : ℝ) →
      ∃ (ε : ℝ) (x : CoefficientSpace P.dim),
        0 < ε ∧
        x ∈ normalizedPolynomialParameters P ∧
        ∀ q, Cvis * (M q : ℝ) <
          concreteMollifiedVisibility P ε x (unitCube (center q))

/--
Three-dimensional specialization of the CV polynomial visibility theorem:
one normalized bounded-degree polynomial has visibility above every prescribed
weight on a finite family of unit cubes.
-/
def PolynomialVisibilityStatement.{u} : Prop :=
  ∃ Cdeg Cvis : ℝ, 0 < Cdeg ∧ 0 < Cvis ∧
    ∀ (Cube : Type u) [Fintype Cube]
        (center : Cube → Point 3)
        (M : Cube → ℝ≥0),
      ∃ (k : ℕ) (P : PolynomialParameterization k) (ε : ℝ)
          (x : CoefficientSpace P.dim),
        0 < ε ∧
        x ∈ normalizedPolynomialParameters P ∧
        (k : ℝ) ≤
          Cdeg * Real.rpow (∑ q, (M q : ℝ) ^ 3) (1 / 3 : ℝ) ∧
        ∀ q, Cvis * (M q : ℝ) ≤
          concreteMollifiedVisibility P ε x (unitCube (center q))

end Kakeya.CV
