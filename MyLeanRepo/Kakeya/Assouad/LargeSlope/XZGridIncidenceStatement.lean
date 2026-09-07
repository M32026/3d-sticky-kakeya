import MyLeanRepo.Kakeya.Assouad.LargeSlope.Step4WitnessGeometry

/-!
# Tube incidence with the xz-grid prisms

Paper Section 6 covers the fixed plane `{y = y₀}` by squares whose side
length is the slab height `b - a`, then extends each square in the
y-direction.  The resulting vertical prisms are indexed by an integer
x-grid.

The existing closed theorem uses the direction-free projection estimate
`2 * (b - a) + 6 * delta` and therefore returns the safe bound four.  The
paper's bound three uses the additional unit-direction geometry: in the
vertical chart, the ratio of the x- and z-components is strictly below two.
After making the tube thickness small relative to the slab height, the
x-diameter is strictly below two grid widths.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

/--
The vertical prism above one square in a translated integer xz-grid.

The x-interval is half-open so distinct grid columns are genuinely disjoint.
The z-interval is the common slab `[a,b]`, while y is unrestricted.
-/
def xzGridPrism (x₀ a b : ℝ) (k : ℤ) : Set Point3 :=
  let W := b - a
  {p |
    p (0 : Fin 3) ∈
        Set.Ico (x₀ + (k : ℝ) * W) (x₀ + ((k : ℝ) + 1) * W) ∧
      p (2 : Fin 3) ∈ Set.Icc a b}

/--
A vertical-chart delta-tube meets at most four prisms from the translated
xz-grid of square side length `b - a`.

This is the tube-incidence input needed by the repaired Step 4 producer.  It
does not assume that an arbitrary ball cover already carries grid or slice
provenance.
-/
def LargeSlopeXZGridIncidenceStatement : Prop :=
  ∀ (delta a b x₀ : ℝ) (T : Kakeya.DeltaTube delta) (s : Finset ℤ),
    0 < delta →
    a < b →
    6 * delta < b - a →
    (1 / 2 : ℝ) ≤ |T.direction (2 : Fin 3)| →
      (s.filter fun k =>
        (T.carrier ∩ xzGridPrism x₀ a b k).Nonempty).card ≤ 4

/--
The paper-faithful three-prism incidence bound.

The quantitative separation `32 * delta ≤ b - a` absorbs the closed-tube
endpoint thickness.  Unlike `LargeSlopeXZGridIncidenceStatement`, this
statement must use the unit-direction relation between the x- and z-
components rather than the direction-free scalar-projection estimate.
-/
def LargeSlopeXZGridThreeIncidenceStatement : Prop :=
  ∀ (delta a b x₀ : ℝ) (T : Kakeya.DeltaTube delta) (s : Finset ℤ),
    0 < delta →
    a < b →
    32 * delta ≤ b - a →
    (1 / 2 : ℝ) ≤ |T.direction (2 : Fin 3)| →
      (s.filter fun k =>
        (T.carrier ∩ xzGridPrism x₀ a b k).Nonempty).card ≤ 3

end Kakeya.Assouad
