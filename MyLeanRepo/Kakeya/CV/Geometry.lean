import MyLeanRepo.Kakeya.CV.Isoperimetric.Statements
import MyLeanRepo.Kakeya.Geometry.OuterJohnEllipsoid

/-!
# Geometric objects for Carbery--Valdimarsson

This file contains the concrete geometric definitions shared by the CV proof
targets.  The locked `JohnEllipsoid` API is used directly.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal Pointwise Real RealInnerProductSpace

namespace Kakeya.CV

/-- The zero set of a real multivariable polynomial. -/
def polynomialZeroSet {n : ℕ} (p : MvPolynomial (Fin n) ℝ) : Set (Point n) :=
  {x | polynomialValue p x = 0}

/-- The affine line through `a` in direction `e`. -/
def affineLine {n : ℕ} (a e : Point n) : Set (Point n) :=
  {x | ∃ t : ℝ, x = a + t • e}

/-- The closed unit neighborhood of an affine line. -/
def unitTube {n : ℕ} (a e : Point n) : Set (Point n) :=
  {x | Metric.infDist x (affineLine a e) ≤ 1}

/-- The gradient of a multivariable polynomial at a Euclidean point. -/
def polynomialGradient {n : ℕ} (p : MvPolynomial (Fin n) ℝ) (x : Point n) : Point n :=
  (EuclideanSpace.equiv (Fin n) ℝ).symm
    (fun i => polynomialValue (MvPolynomial.pderiv i p) x)

/-- Singular locus of the polynomial hypersurface. -/
def polynomialSingularSet (p : MvPolynomial (Fin 3) ℝ) : Set (Point 3) :=
  {x | polynomialValue p x = 0 ∧ polynomialGradient p x = 0}

/--
The condition ensuring that the gradient-normal integral agrees almost
everywhere with the geometric surface normal.
-/
def HasNegligibleSingularSet (p : MvPolynomial (Fin 3) ℝ) : Prop :=
  codimensionOneMeasure 3 (polynomialSingularSet p) = 0

/-- The regular normalized polynomial gradient, set to zero at singular points. -/
def polynomialUnitNormal {n : ℕ} (p : MvPolynomial (Fin n) ℝ) (x : Point n) : Point n :=
  if h : ‖polynomialGradient p x‖ = 0 then 0
  else ‖polynomialGradient p x‖⁻¹ • polynomialGradient p x

/--
Regular directional surface area of a polynomial zero set, expressed as a
Hausdorff surface integral of the absolute normal component.  For a polynomial
with `HasNegligibleSingularSet`, this is the geometric directional surface
area; without that condition it can depend on the chosen polynomial equation.
-/
def directionalSurfaceArea (e : Point 3) (p : MvPolynomial (Fin 3) ℝ)
    (s : Set (Point 3)) : ℝ≥0∞ :=
  ∫⁻ x in s, ENNReal.ofReal ‖inner ℝ e (polynomialUnitNormal p x)‖
    ∂(MeasureTheory.Measure.hausdorffMeasure 2)

/-- Absolute volume of the parallelepiped spanned by three vectors. -/
def tripleVolume (v : Fin 3 → Point 3) : ℝ :=
  |Matrix.det (fun i j => v i j)|

/-- Homothetic dilation of a set about a center. -/
def dilateAbout (z : Point 3) (r : ℝ) (s : Set (Point 3)) : Set (Point 3) :=
  AffineMap.homothety z r '' s

/-- Parameters describing a three-dimensional ellipsoid in the locked API. -/
abbrev EllipsoidParameter := Point 3 × (Point 3 ≃ₗ[ℝ] Point 3)

/-- The carrier of an ellipsoid parameter. -/
def ellipsoidCarrier (E : EllipsoidParameter) : Set (Point 3) :=
  JohnEllipsoid.ellipsoid E.1 E.2

/-- Two sets are close up to reciprocal homothetic dilations about some center. -/
def AreHomotheticallyClose (α : ℝ) (K L : Set (Point 3)) : Prop :=
  ∃ z : Point 3,
    dilateAbout z α⁻¹ K ⊆ L ∧ L ⊆ dilateAbout z α K

/-- Homothetic closeness with a specified common center. -/
def AreHomotheticallyCloseAt (z : Point 3) (α : ℝ)
    (K L : Set (Point 3)) : Prop :=
  dilateAbout z α⁻¹ K ⊆ L ∧ L ⊆ dilateAbout z α K

/-- The convex body whose inverse-volume scale is the visibility. -/
def visibilityBody (p : MvPolynomial (Fin 3) ℝ) (s : Set (Point 3)) :
    Set (Point 3) :=
  unitBall 3 ∩ {u | directionalSurfaceArea u p s ≤ 1}

/-- Visibility of a polynomial hypersurface inside a region. -/
def visibility (p : MvPolynomial (Fin 3) ℝ) (s : Set (Point 3)) : ℝ :=
  Real.rpow (volume (visibilityBody p s)).toReal (-1 / 3 : ℝ)

/-- A polynomial zero set bisects a measurable region by sign. -/
def PolynomialBisects (p : MvPolynomial (Fin 3) ℝ) (s : Set (Point 3)) : Prop :=
  volume (s ∩ {x | polynomialValue p x < 0}) =
    volume (s ∩ {x | 0 < polynomialValue p x})

/--
Both strict sign regions of `p` occupy at least the proportion `τ` of `s`.

CV uses this with `τ = 2 / 5` when an exact bisection is perturbed in
coefficient space.
-/
def PolynomialCutsAtLeast (p : MvPolynomial (Fin 3) ℝ) (s : Set (Point 3))
    (τ : ℝ≥0∞) : Prop :=
  τ * volume s ≤ volume (s ∩ {x | polynomialValue p x < 0}) ∧
    τ * volume s ≤ volume (s ∩ {x | 0 < polynomialValue p x})

/-- A translated copy of `A` applied to the ball of radius `η`. -/
def scaledEllipsoid (A : Point 3 ≃ₗ[ℝ] Point 3) (η : ℝ) (z : Point 3) :
    Set (Point 3) :=
  z +ᵥ A '' Metric.closedBall 0 η

/-- Dilation about the same center composes by multiplication of factors. -/
lemma dilateAbout_comp (z : Point 3) (r s : ℝ) (S : Set (Point 3)) :
    dilateAbout z r (dilateAbout z s S) = dilateAbout z (r * s) S := by
  have h : (AffineMap.homothety z r).comp (AffineMap.homothety z s) =
      AffineMap.homothety z (r * s) :=
    (AffineMap.homothety_mul z r s).symm
  have h_eq : ∀ (x : Point 3),
      (AffineMap.homothety z r) ((AffineMap.homothety z s) x) =
      (AffineMap.homothety z (r * s)) x := by
    intro x
    have h2 : ((AffineMap.homothety z r).comp (AffineMap.homothety z s)) x =
        (AffineMap.homothety z (r * s)) x := by
      rw [h]
    simpa [AffineMap.comp_apply] using h2
  ext y
  simp only [dilateAbout, Set.mem_image]
  constructor
  · rintro ⟨x, ⟨w, hw, hx⟩, hy⟩
    have h_goal : (AffineMap.homothety z (r * s)) w = y := by
      calc
        (AffineMap.homothety z (r * s)) w
          = (AffineMap.homothety z r) ((AffineMap.homothety z s) w) := (h_eq w).symm
        _ = (AffineMap.homothety z r) x := by rw [hx]
        _ = y := hy
    exact ⟨w, hw, h_goal⟩
  · rintro ⟨w, hw, hy⟩
    have h_goal : (AffineMap.homothety z r) ((AffineMap.homothety z s) w) = y := by
      calc
        (AffineMap.homothety z r) ((AffineMap.homothety z s) w)
          = (AffineMap.homothety z (r * s)) w := h_eq w
        _ = y := hy
    exact ⟨(AffineMap.homothety z s) w, ⟨w, hw, rfl⟩, h_goal⟩

/-- Dilation is monotone in the set argument. -/
lemma dilateAbout_mono (z : Point 3) (r : ℝ) {A B : Set (Point 3)}
    (h : A ⊆ B) : dilateAbout z r A ⊆ dilateAbout z r B :=
  Set.image_mono h

/-- Dilation by 1 is the identity. -/
lemma dilateAbout_one (z : Point 3) (S : Set (Point 3)) :
    dilateAbout z 1 S = S := by
  simp [dilateAbout, AffineMap.homothety_one]

namespace AreHomotheticallyCloseAt

/-- Symmetry: if K is α-close to L at z, then L is α-close to K at z. -/
lemma symm {z : Point 3} {α : ℝ} {K L : Set (Point 3)}
    (hα : α ≠ 0) (h : AreHomotheticallyCloseAt z α K L) :
    AreHomotheticallyCloseAt z α L K := by
  have h1 : dilateAbout z α⁻¹ K ⊆ L := h.1
  have h2 : L ⊆ dilateAbout z α K := h.2
  have hmul1 : α⁻¹ * α = 1 := by field_simp [hα]
  have hmul2 : α * α⁻¹ = 1 := by field_simp [hα]
  have h3 : dilateAbout z α⁻¹ L ⊆ K := by
    calc
      dilateAbout z α⁻¹ L
        ⊆ dilateAbout z α⁻¹ (dilateAbout z α K) := dilateAbout_mono z α⁻¹ h2
      _ = dilateAbout z (α⁻¹ * α) K := by rw [dilateAbout_comp]
      _ = dilateAbout z 1 K := by rw [hmul1]
      _ = K := dilateAbout_one z K
  have h4 : K ⊆ dilateAbout z α L := by
    calc
      K = dilateAbout z 1 K := (dilateAbout_one z K).symm
      _ = dilateAbout z (α * α⁻¹) K := by rw [hmul2]
      _ = dilateAbout z α (dilateAbout z α⁻¹ K) := by rw [dilateAbout_comp]
      _ ⊆ dilateAbout z α L := dilateAbout_mono z α h1
  exact ⟨h3, h4⟩

/-- Transitivity: α-close plus β-close gives (α*β)-close. -/
lemma trans {z : Point 3} {α β : ℝ} {K L M : Set (Point 3)}
    (h1 : AreHomotheticallyCloseAt z α K L)
    (h2 : AreHomotheticallyCloseAt z β L M) :
    AreHomotheticallyCloseAt z (α * β) K M := by
  have hcomm : β * α = α * β := by ring
  have h₁ : dilateAbout z (α * β)⁻¹ K ⊆ M := by
    have hinv : (α * β)⁻¹ = β⁻¹ * α⁻¹ := by ring
    calc
      dilateAbout z (α * β)⁻¹ K
        = dilateAbout z β⁻¹ (dilateAbout z α⁻¹ K) := by
          rw [hinv, ←dilateAbout_comp]
      _ ⊆ dilateAbout z β⁻¹ L := dilateAbout_mono z β⁻¹ h1.1
      _ ⊆ M := h2.1
  have h₂ : M ⊆ dilateAbout z (α * β) K := by
    calc
      M ⊆ dilateAbout z β L := h2.2
      _ ⊆ dilateAbout z β (dilateAbout z α K) := dilateAbout_mono z β h1.2
      _ = dilateAbout z (β * α) K := by rw [dilateAbout_comp]
      _ = dilateAbout z (α * β) K := by rw [hcomm]
  exact ⟨h₁, h₂⟩

end AreHomotheticallyCloseAt

end Kakeya.CV
