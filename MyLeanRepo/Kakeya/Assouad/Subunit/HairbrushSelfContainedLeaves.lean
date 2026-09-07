import MyLeanRepo.Kakeya.Assouad.Subunit.HairbrushStatements
import MyLeanRepo.Kakeya.Assouad.Subunit.HairbrushTwoBroadLeaves
import MyLeanRepo.Kakeya.Assouad.Subunit.OrientationInfrastructure
import MyLeanRepo.Kakeya.Hairbrush.PlaneCovering.Basic

/-!
# Frozen leaves for the self-contained Appendix-B hairbrush route

These declarations follow
`reference/wang_zahl_3d_kakeya_2502.17655/appendix-b-self-contained-proof.md`.
They replace the old symmetric multiplicity core by the asymmetric structure
actually used in the robust-transverse shaded hairbrush argument:

* pointwise angular stopping retains labelled cap incidences at one scale;
* multiplicity and density regularization selects the hairs but leaves the
  ambient family unchanged as the source of possible stems;
* the fixed-stem Córdoba leaf consumes a supplied transverse hairbrush and
  performs only the plane-covering and planar `L²` estimate.

The global cap/slab incidence grouping and the two assembly layers are frozen
separately after these local leaves.
-/

noncomputable section

open MeasureTheory Metric Set Finset Real

attribute [local instance] Classical.propDecidable

namespace Kakeya.Assouad

/-- Aggregate shaded density with respect to the common nominal tube volume. -/
def HairbrushAggregateDense {δ : ℝ}
    {F : Kakeya.TubeFamily δ} (Y : Kakeya.Shading F)
    (density : ENNReal) : Prop :=
  density * F.enncard * Kakeya.deltaTubeVolume δ ≤ Y.mass

/--
Output of the pointwise angular stopping argument.

The retained shading keeps a polynomial fraction of the incidence mass.  At
every retained point a labelled cap contains all retained incidences, and the
same incidences obey the relative broadness estimate at the common dyadic
scale `theta`.  The finite measurable label exposes the direction-cap fibers
needed by the downstream slab grouping.
-/
structure HairbrushLabeledAngularStoppingData
    {δ : ℝ} {F : Kakeya.TubeFamily δ} (Y : Kakeya.Shading F)
    (eta stopLoss : ℝ) where
  theta : ℝ
  delta_le_theta : δ ≤ theta
  theta_le_one : theta ≤ 1
  capRadius : ℝ
  theta_le_capRadius : theta ≤ capRadius
  capRadius_le_six_theta : capRadius ≤ 6 * theta
  capRadius_le_one : capRadius ≤ 1
  shading : Kakeya.Shading F
  shading_subset :
    ∀ T ∈ F, shading.carrier T ⊆ Y.carrier T
  mass_retention :
    Kakeya.realRpowENN δ stopLoss * Y.mass ≤ shading.mass
  labelCount : ℕ
  labelCount_pos : 0 < labelCount
  label : Point3 → Fin labelCount
  label_measurable : Measurable label
  center : Fin labelCount → Point3
  center_unit :
    ∀ j, ‖center j‖ = 1
  pointwise_confined :
    ∀ x ∈ shading.union,
      ∀ T ∈ F, x ∈ shading.carrier T →
        hairbrushAcuteDirectionAngle T.direction
          (center (label x)) ≤ capRadius
  label_overlap :
    ∀ T ∈ F,
      ((Finset.univ.filter fun j : Fin labelCount =>
          ∃ x ∈ shading.carrier T, label x = j).card : ENNReal) ≤
        1000
  two_broad :
    IsTwoBroadAtScale shading theta eta

/--
Pointwise max-score angular stopping followed by a dyadic pigeonhole in the
selected radius and rounding of cap centers to a separated direction net.

The strict inequality `eta < stopLoss` is exactly the budget used to absorb
the logarithmic number of dyadic scales.  Tube incidences, not the set of
distinct direction vectors, must be counted: coincident directions may occur
with multiplicity in an essentially-distinct tube family.  Rounding may enlarge
the confinement cap by a fixed factor but does not alter the relative
broadness scale.  The explicit label-overlap bound is the input needed for
the global incidence estimate (B.32).
-/
def HairbrushLabeledAngularStoppingStatement : Prop :=
  ∀ eta stopLoss : ℝ,
    0 < eta → eta < stopLoss →
      ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
        ∀ δ : ℝ, 0 < δ → δ ≤ delta₀ →
          ∀ (F : Kakeya.TubeFamily δ) (Y : Kakeya.Shading F),
            Nonempty
              (HairbrushLabeledAngularStoppingData
                Y eta stopLoss)

/--
Raw global cap/slab incidence grouping.

Each group is indexed by one finite direction label and one spatial strip
normal to that label's cap center.  The group shading is obtained by
restricting all retained incidences according to the point label and strip.
Thus group unions are disjoint, incidence mass is exactly additive, and the
relative broadness through-family is unchanged at every surviving point.
-/
structure HairbrushSlabIncidenceGroupingData
    {δ eta stopLoss : ℝ}
    {F : Kakeya.TubeFamily δ} {Y : Kakeya.Shading F}
    (angular :
      HairbrushLabeledAngularStoppingData
        Y eta stopLoss) where
  groupCount : ℕ
  groupCount_pos : 0 < groupCount
  family : Fin groupCount → Kakeya.TubeFamily δ
  shading : ∀ j, Kakeya.Shading (family j)
  family_nonempty : ∀ j, (family j).Nonempty
  family_subset : ∀ j, family j ⊆ F
  directionLabel : Fin groupCount → Fin angular.labelCount
  label_consistency :
    ∀ j T, ∀ hT : T ∈ family j,
      ∀ x ∈ (shading j).carrier T,
        angular.label x = directionLabel j
  shading_subset :
    ∀ j T, ∀ hT : T ∈ family j,
      (shading j).carrier T ⊆ angular.shading.carrier T
  angular_confinement :
    ∀ j,
      HairbrushAngularlyConfined
        (family j) angular.capRadius
  two_broad :
    ∀ j,
      IsTwoBroadAtScale
        (shading j) angular.theta eta
  slab : Fin groupCount → Kakeya.Slab
  slab_containment :
    ∀ j T, ∀ hT : T ∈ family j,
      T.carrier ⊆ (slab j).carrier
  slab_volume :
    ∀ j,
      volume (slab j).carrier ≤
        ENNReal.ofReal (100 * angular.capRadius)
  union_disjoint :
    ∀ j k, j ≠ k →
      Disjoint (shading j).union (shading k).union
  union_exact :
    (⋃ j, (shading j).union) = angular.shading.union
  incidence_mass_additive :
    ∑ j, (shading j).mass = angular.shading.mass
  tube_occurrence_bound :
    ∑ j, (family j).enncard ≤ 1000000 * F.enncard

/--
Partition a finite-labelled angular stopping output into slab-contained
incidence groups.

For each point, first use its finite direction label.  For that label choose
a unit normal perpendicular to the cap center, and assign the point to the
integer strip of width `capRadius` determined by its projection on the normal.
Every retained incidence at the same point receives the same pair of labels.

The cap radius is comparable to `theta`, and each fixed tube occurs in only
boundedly many direction labels.  Since its direction lies within
`capRadius` of the corresponding center, its projection on the chosen normal
varies by only `O(capRadius)` along the unit segment; hence it meets only
boundedly many spatial strips for each direction label.  This proves the
absolute tube-occurrence bound.
-/
def HairbrushSlabIncidenceGroupingStatement : Prop :=
  ∀ δ eta stopLoss : ℝ,
    0 < δ →
      ∀ (F : Kakeya.TubeFamily δ) (Y : Kakeya.Shading F),
        F.IsInUnitBall →
          ∀ angular :
            HairbrushLabeledAngularStoppingData
              Y eta stopLoss,
            angular.shading.mass ≠ 0 →
              Nonempty
                (HairbrushSlabIncidenceGroupingData angular)

/--
Paper-faithful coarse-tube incidence grouping for (B.32)--(B.33).

The embedded grouping has exactly the API consumed by the existing balancing
and Frostman summation leaves.  In addition, every group lies in one convex
container of volume `O(capRadius²)`.  This quadratic, rather than slab-scale,
volume is the input needed to recover the normalized local Katz--Tao
cardinality bound after affine normalization.
-/
structure HairbrushCoarseTubeIncidenceGroupingData
    {δ eta stopLoss : ℝ}
    {F : Kakeya.TubeFamily δ} {Y : Kakeya.Shading F}
    (angular :
      HairbrushLabeledAngularStoppingData
        Y eta stopLoss) where
  grouping : HairbrushSlabIncidenceGroupingData angular
  container : Fin grouping.groupCount → Set Point3
  container_convex :
    ∀ j, Convex ℝ (container j)
  container_volume :
    ∀ j,
      volume (container j) ≤
        ENNReal.ofReal (1000000 * angular.capRadius ^ 2)
  container_containment :
    ∀ j T, ∀ hT : T ∈ grouping.family j,
      T.carrier ⊆ container j

/--
Replace the one-transverse-coordinate slab grouping by the actual
coarse-`theta`-tube grouping used in Appendix B.

For each finite direction label, extend the cap center to an orthonormal
frame and label every retained point by both transverse strips of width
`capRadius`.  All retained tubes through one point receive the same triple
of labels.  Tubes in one group lie in the intersection of the corresponding
two thick strips and the unit ball, a convex container of volume
`O(capRadius²)`.  Each fixed tube meets only boundedly many label/strip
triples, so the embedded grouping retains the absolute occurrence bound.
-/
def HairbrushCoarseTubeIncidenceGroupingStatement : Prop :=
  ∀ δ eta stopLoss : ℝ,
    0 < δ →
      ∀ (F : Kakeya.TubeFamily δ) (Y : Kakeya.Shading F),
        F.IsInUnitBall →
          ∀ angular :
            HairbrushLabeledAngularStoppingData
              Y eta stopLoss,
            angular.shading.mass ≠ 0 →
              Nonempty
                (HairbrushCoarseTubeIncidenceGroupingData angular)

/--
Convert the quadratic-volume coarse container into the normalized local
Katz--Tao cardinality bound.

The container has volume at most `10^6 * capRadius²`, while
`capRadius ≤ 6 * theta`.  The ambient Katz--Tao estimate and
`deltaTubeVolume δ ≥ δ²` therefore give
`#group ≤ 10^8 * K * (theta / δ)²`.  The round constant is deliberately
larger than `36 * 10^6`; no asymptotic loss is hidden in this leaf.
-/
def HairbrushCoarseTubeKatzTaoCardinalityStatement : Prop :=
  ∀ δ eta stopLoss katzTaoConstant : ℝ,
    0 < δ →
      0 ≤ katzTaoConstant →
        ∀ (F : Kakeya.TubeFamily δ) (Y : Kakeya.Shading F),
          Kakeya.KatzTaoConvexWolffBound F katzTaoConstant →
            ∀ angular :
              HairbrushLabeledAngularStoppingData
                Y eta stopLoss,
              ∀ coarse :
                HairbrushCoarseTubeIncidenceGroupingData angular,
                ENNReal.ofReal (δ ^ 2) ≤
                    Kakeya.deltaTubeVolume δ →
                  ∀ j,
                    (coarse.grouping.family j).enncard ≤
                      ENNReal.ofReal 100000000 *
                        ENNReal.ofReal katzTaoConstant *
                        ENNReal.ofReal
                          ((angular.theta / δ) ^ 2)

/--
Balanced subcollection of raw slab incidence groups.

The selected groups have comparable tube cardinality and comparable average
shading density.  Their total shaded incidence mass retains a polynomial
fraction of the raw grouped mass.
-/
structure HairbrushBalancedSlabGroupsData
    {δ eta stopLoss densityFloor balanceLoss : ℝ}
    {F : Kakeya.TubeFamily δ} {Y : Kakeya.Shading F}
    {angular :
      HairbrushLabeledAngularStoppingData
        Y eta stopLoss}
    (grouping : HairbrushSlabIncidenceGroupingData angular) where
  selectedCount : ℕ
  selectedCount_pos : 0 < selectedCount
  select : Fin selectedCount → Fin grouping.groupCount
  select_injective : Function.Injective select
  typicalCard : ℕ
  typicalCard_pos : 0 < typicalCard
  typicalDensity : ENNReal
  typicalDensity_pos : typicalDensity ≠ 0
  typicalDensity_ne_top : typicalDensity ≠ ⊤
  density_floor :
    Kakeya.realRpowENN δ densityFloor ≤ typicalDensity
  card_lower :
    ∀ j, typicalCard ≤ (grouping.family (select j)).card
  card_upper :
    ∀ j, (grouping.family (select j)).card < 2 * typicalCard
  density_lower :
    ∀ j,
      typicalDensity *
            (grouping.family (select j)).enncard *
            Kakeya.deltaTubeVolume δ ≤
        (grouping.shading (select j)).mass
  density_upper :
    ∀ j,
      (grouping.shading (select j)).mass <
        2 * typicalDensity *
          (grouping.family (select j)).enncard *
          Kakeya.deltaTubeVolume δ
  mass_retention :
    Kakeya.realRpowENN δ balanceLoss * angular.shading.mass ≤
      ∑ j, (grouping.shading (select j)).mass

/--
Discard low-average-density slab groups and pigeonhole the remaining groups
simultaneously by tube cardinality and average shading density.

The raw angular shading has aggregate density at least
`δ^inputExponent`.  Groups below average density `δ^densityFloor` contribute
at most that threshold times the total tube-group occurrence, so they are
negligible when `inputExponent < densityFloor`.  The explicit polynomial
cardinality bound controls the number of cardinality and density dyadic
levels.  Their logarithmic cost is absorbed into `δ^balanceLoss`.
-/
def HairbrushSlabGroupBalancingStatement : Prop :=
  ∀ inputExponent densityFloor cardExponent balanceLoss : ℝ,
    0 < inputExponent →
      inputExponent < densityFloor →
        0 < cardExponent →
          0 < balanceLoss →
            ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 / 1000 ∧
              ∀ δ : ℝ, 0 < δ → δ ≤ delta₀ →
                ∀ eta stopLoss : ℝ,
                  ∀ (F : Kakeya.TubeFamily δ)
                      (Y : Kakeya.Shading F),
                    F.Nonempty →
                      F.enncard ≤
                        Kakeya.realRpowENN δ (-cardExponent) →
                      ∀ angular :
                        HairbrushLabeledAngularStoppingData
                          Y eta stopLoss,
                        HairbrushAggregateDense angular.shading
                          (Kakeya.realRpowENN δ inputExponent) →
                        ∀ grouping :
                          HairbrushSlabIncidenceGroupingData angular,
                          Nonempty
                            (HairbrushBalancedSlabGroupsData
                              (densityFloor := densityFloor)
                              (balanceLoss := balanceLoss) grouping)

/--
Multiplicity and density regularization with asymmetric ambient stems.

`layer` is obtained by restricting every ambient tube to the same measurable
set `support`, so pointwise broadness of the input shading is inherited
without changing the through-family at surviving points.  Only `hairs` are
then selected by the individual-density pigeonhole; the ambient family `F`
and `layer` remain available as possible stems.
-/
structure HairbrushAmbientMultiplicityCoreData
    {δ : ℝ} {F : Kakeya.TubeFamily δ} (Y : Kakeya.Shading F)
    (inputExponent layerLoss hairLoss : ℝ) where
  support : Set Point3
  support_measurable : MeasurableSet support
  layer : Kakeya.Shading F
  layer_eq :
    ∀ T ∈ F, layer.carrier T = Y.carrier T ∩ support
  mu : ℕ
  mu_pos : 0 < mu
  multiplicity_lower :
    ∀ x ∈ layer.union,
      mu ≤ (F.filter fun T => x ∈ layer.carrier T).card
  multiplicity_upper :
    ∀ x ∈ layer.union,
      (F.filter fun T => x ∈ layer.carrier T).card < 2 * mu
  layerDensity : ENNReal
  layerDensity_pos : layerDensity ≠ 0
  layerDensity_ne_top : layerDensity ≠ ⊤
  input_density_retention :
    Kakeya.realRpowENN δ (inputExponent + layerLoss) ≤
      layerDensity
  layer_mass_lower :
    layerDensity * F.enncard * Kakeya.deltaTubeVolume δ ≤ layer.mass
  layer_mass_upper :
    layer.mass ≤
      2 * layerDensity * F.enncard * Kakeya.deltaTubeVolume δ
  hairs : Kakeya.TubeFamily δ
  hairs_subset : hairs ⊆ F
  hairs_nonempty : hairs.Nonempty
  hairShading : Kakeya.Shading hairs
  hair_shading_eq :
    ∀ T ∈ hairs, hairShading.carrier T = layer.carrier T
  hairDensity : ENNReal
  hairDensity_pos : hairDensity ≠ 0
  hairDensity_ne_top : hairDensity ≠ ⊤
  layer_density_le_hair :
    layerDensity / 2 ≤ hairDensity
  per_hair_density_lower :
    ∀ T ∈ hairs,
      hairDensity * T.volume ≤ volume (hairShading.carrier T)
  per_hair_density_upper :
    ∀ T ∈ hairs,
      volume (hairShading.carrier T) ≤ 2 * hairDensity * T.volume
  weighted_hair_retention :
    Kakeya.realRpowENN δ hairLoss * layerDensity * F.enncard ≤
      hairDensity * hairs.enncard

/--
The multiplicity layer and individual-density pigeonholes, corresponding to
(B.11)--(B.15) in the self-contained Appendix-B proof.

The input is aggregate density.  Both logarithmic pigeonhole losses are
absorbed into caller-supplied positive powers of `δ`.  The explicit
polynomial upper bound on the family cardinality and the polynomial input
density are essential for that uniform absorption.  No angular selection,
two-ends reduction, stem selection, or Córdoba estimate belongs to this leaf.
-/
def HairbrushAmbientMultiplicityCoreStatement : Prop :=
  ∀ inputExponent cardExponent layerLoss hairLoss : ℝ,
    0 < inputExponent →
      0 < cardExponent →
        0 < layerLoss → 0 < hairLoss →
      ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
        ∀ δ : ℝ, 0 < δ → δ ≤ delta₀ →
          ∀ (F : Kakeya.TubeFamily δ) (Y : Kakeya.Shading F),
            F.Nonempty →
              F.enncard ≤
                Kakeya.realRpowENN δ (-cardExponent) →
              HairbrushAggregateDense Y
                (Kakeya.realRpowENN δ inputExponent) →
                Nonempty
                  (HairbrushAmbientMultiplicityCoreData
                    Y inputExponent layerLoss hairLoss)

/--
The lower side of the multiplicity incidence identity (B.13).

The layer has total incidence mass at least
`layerDensity * #F * δ²`, while its pointwise multiplicity is strictly below
`2 * mu`.  Integrating that upper multiplicity gives the displayed estimate.
-/
def HairbrushAmbientIncidenceStatement : Prop :=
  ∀ δ inputExponent layerLoss hairLoss : ℝ,
    0 < δ →
      ∀ (F : Kakeya.TubeFamily δ) (Y : Kakeya.Shading F),
        ∀ core :
          HairbrushAmbientMultiplicityCoreData
            Y inputExponent layerLoss hairLoss,
          ENNReal.ofReal (δ ^ 2) ≤ Kakeya.deltaTubeVolume δ →
            core.layerDensity * F.enncard *
                ENNReal.ofReal (δ ^ 2) ≤
              2 * (core.mu : ENNReal) *
                volume core.layer.union

/--
Homogeneous per-hair two-ends output corresponding to (B.16)--(B.20).

The refined shading is measured relative to itself: the two-ends coefficient
is absolute and carries no inverse `δ`-power.  A common dyadic radius is
selected across a retained hair subfamily.
-/
structure HairbrushHomogeneousTwoEndsData
    {δ zeta familyLoss : ℝ}
    {H : Kakeya.TubeFamily δ} (Z : Kakeya.Shading H)
    (hairDensity : ENNReal) where
  family : Kakeya.TubeFamily δ
  family_subset : family ⊆ H
  family_nonempty : family.Nonempty
  family_retention :
    Kakeya.realRpowENN δ familyLoss * H.enncard ≤ family.enncard
  shading : Kakeya.Shading family
  shading_subset :
    ∀ T ∈ family, shading.carrier T ⊆ Z.carrier T
  radius : ℝ
  delta_le_radius : δ ≤ radius
  radius_le_two : radius ≤ 2
  per_hair_mass :
    ∀ T ∈ family,
      ENNReal.ofReal (Real.rpow radius zeta) *
          hairDensity * T.volume ≤
        volume (shading.carrier T)
  two_ends :
    ∀ T ∈ family, ∀ x : Point3,
      ∀ r : ℝ, δ ≤ r → r ≤ 2 →
        volume
            (shading.carrier T ∩ Metric.ball x r) ≤
          ENNReal.ofReal 4 *
            ENNReal.ofReal
              (Real.rpow (r / radius) zeta) *
            volume (shading.carrier T)
  density_radius_relation :
    hairDensity ≤
      ENNReal.ofReal 100 *
        ENNReal.ofReal
          (Real.rpow radius (1 - zeta))

/--
Apply the maximizing-ball homogeneous-piece argument independently to every
hair and pigeonhole a common dyadic radius.

The input hair shading has uniform individual density.  For each tube choose a
ball maximizing `r^-zeta` times shaded mass, restrict to that ball, and retain
the resulting absolute two-ends estimate.  Pigeonhole the selected radii,
losing only `δ^familyLoss` in family cardinality.  The cross-section volume
bound gives the density–radius relation.
-/
def HairbrushHomogeneousTwoEndsStatement : Prop :=
  ∀ zeta familyLoss cardExponent : ℝ,
    0 < zeta → zeta < 1 →
      0 < familyLoss →
        0 < cardExponent →
          ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 / 1000 ∧
            ∀ δ : ℝ, 0 < δ → δ ≤ delta₀ →
              ∀ (H : Kakeya.TubeFamily δ) (Z : Kakeya.Shading H),
                H.Nonempty →
                  H.enncard ≤
                    Kakeya.realRpowENN δ (-cardExponent) →
                  ∀ hairDensity : ENNReal,
                    hairDensity ≠ 0 →
                      hairDensity ≠ ⊤ →
                        (∀ T ∈ H,
                          hairDensity * T.volume ≤
                            volume (Z.carrier T)) →
                        (∀ T ∈ H,
                          volume (Z.carrier T) ≤
                            2 * hairDensity * T.volume) →
                          Nonempty
                            (HairbrushHomogeneousTwoEndsData
                              (zeta := zeta)
                              (familyLoss := familyLoss)
                              Z hairDensity)

/-- Effective radii for the hard homogeneous two-ends branch. -/
structure HairbrushHomogeneousFarRadiusData
    {δ zeta familyLoss sigma : ℝ}
    {H : Kakeya.TubeFamily δ} {Z : Kakeya.Shading H}
    {hairDensity : ENNReal}
    (twoEnds :
      HairbrushHomogeneousTwoEndsData
        (zeta := zeta) (familyLoss := familyLoss)
        Z hairDensity)
    (farFraction : ℝ) where
  farRadius : ℝ
  nearRadius : ℝ
  farRadius_pos : 0 < farRadius
  nearRadius_pos : 0 < nearRadius
  far_radius_eq :
    farRadius =
      farFraction * sigma * twoEnds.radius
  near_ball_mass :
    ∀ U ∈ twoEnds.family, ∀ x : Point3,
      volume
          (twoEnds.shading.carrier U ∩
            Metric.ball x nearRadius) ≤
        (1 / 4 : ENNReal) *
          volume (twoEnds.shading.carrier U)
  geometric_radius :
    2 * δ +
        Real.pi * (farRadius + 3 * δ) / (2 * sigma) <
      nearRadius

/--
Choose fixed-proportion far and near radii once the hard-branch scale
separation has already been certified.

Both the required separation constant and the far-radius fraction depend on
`zeta`, and are chosen before `δ`.  This quantifier order is essential: for
small `zeta`, a fixed separation such as `1000 * δ ≤ sigma * radius` does not
make `4 * (nearRadius / radius)^zeta` small.  The explicit equation
`farRadius = farFraction * sigma * radius` is the scale factor later consumed
by the fixed-stem Córdoba bound in (B.27).
-/
def HairbrushHomogeneousFarRadiusStatement : Prop :=
  ∀ zeta familyLoss : ℝ,
    0 < zeta → zeta < 1 →
      ∃ separation farFraction : ℝ,
        1000 ≤ separation ∧
          0 < farFraction ∧ farFraction ≤ 1 ∧
            ∀ δ : ℝ, 0 < δ →
              ∀ sigma : ℝ, 0 < sigma → sigma ≤ 1 →
                ∀ (H : Kakeya.TubeFamily δ) (Z : Kakeya.Shading H),
                  ∀ hairDensity : ENNReal,
                    ∀ twoEnds :
                      HairbrushHomogeneousTwoEndsData
                        (zeta := zeta) (familyLoss := familyLoss)
                        Z hairDensity,
                      separation * δ ≤ sigma * twoEnds.radius →
                        Nonempty
                          (HairbrushHomogeneousFarRadiusData
                            (sigma := sigma) twoEnds farFraction)

/--
The exact low-density threshold complementary to the homogeneous hard branch.

If the hair density exceeds this threshold, (B.20) forces the common
two-ends radius to be large enough compared with `δ / angleScale`.
-/
def hairbrushHomogeneousLowDensityThreshold
    (δ zeta separation angleScale : ℝ) : ENNReal :=
  ENNReal.ofReal 100 *
    ENNReal.ofReal
      (Real.rpow (separation * δ / angleScale) (1 - zeta))

/--
The density-radius relation gives the exact easy/hard scale dichotomy.

The easy branch is the low-density case (B.21).  In the complementary branch,
`density <= 100 * radius^(1-zeta)` and `angleScale <= sigma` force
`separation * δ <= sigma * radius`, which is precisely the input required by
the repaired homogeneous far-radius leaf.  No geometry or final target
algebra belongs here.
-/
def HairbrushHomogeneousScaleDichotomyStatement : Prop :=
  ∀ δ zeta familyLoss separation angleScale sigma : ℝ,
    0 < δ →
      0 < zeta → zeta < 1 →
        0 < separation →
          0 < angleScale → angleScale ≤ sigma →
            ∀ (H : Kakeya.TubeFamily δ) (Z : Kakeya.Shading H),
              ∀ hairDensity : ENNReal,
                ∀ twoEnds :
                  HairbrushHomogeneousTwoEndsData
                    (zeta := zeta) (familyLoss := familyLoss)
                    Z hairDensity,
                  hairDensity ≤
                      hairbrushHomogeneousLowDensityThreshold
                        δ zeta separation angleScale ∨
                    separation * δ ≤ sigma * twoEnds.radius

/--
Direct closure of the low hair-density alternative (B.21).

The ambient multiplicity core supplies the retained layer density, a
nonempty uniform-density hair family, and
`layerDensity / 2 ≤ hairDensity`.  One retained hair therefore gives the
union-volume floor `hairDensity * δ²`.  The normalized Katz--Tao cardinality
bound is stated in the original coordinates:
`#F ≤ O(K * (theta / δ)²)`.  Finally, the low-density threshold and the
polynomial comparison between `angleScale` and `theta` provide the three
extra powers of `δ / theta` used in the paper.

The strict exponent gap absorbs the fixed constants.  It records exactly
four uses of the input density, one square root of the Katz--Tao loss, and
three uses of the angle-scale loss.  Construction of the coarse
`theta`-tube giving the displayed cardinality bound is deliberately outside
this numerical/local leaf.
-/
def HairbrushHomogeneousLowDensityStatement : Prop :=
  ∀ zeta inputExponent layerLoss hairLoss angleLoss katzExponent
      outputLoss separation cardinalityConstant : ℝ,
    0 < zeta → zeta < 1 / 4 →
      0 < inputExponent →
        0 ≤ layerLoss →
          0 ≤ angleLoss →
            0 ≤ katzExponent →
              1 ≤ separation →
                1 ≤ cardinalityConstant →
                  4 * (inputExponent + layerLoss) +
                        katzExponent / 2 +
                        3 * angleLoss * (1 - zeta) <
                      outputLoss →
                    ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 / 1000 ∧
                      ∀ δ theta angleScale : ℝ,
                        0 < δ → δ ≤ delta₀ →
                          δ ≤ theta → theta ≤ 1 →
                            0 < angleScale →
                              Kakeya.realRpowENN δ angleLoss *
                                    ENNReal.ofReal theta ≤
                                ENNReal.ofReal angleScale /
                                  ENNReal.ofReal (1000 * Real.pi) →
                                ∀ katzTaoConstant : ℝ,
                                  0 ≤ katzTaoConstant →
                                    ENNReal.ofReal katzTaoConstant ≤
                                      Kakeya.realRpowENN δ
                                        (-katzExponent) →
                                      ∀ (F : Kakeya.TubeFamily δ)
                                          (Y : Kakeya.Shading F),
                                        F.enncard ≤
                                            ENNReal.ofReal
                                                cardinalityConstant *
                                              ENNReal.ofReal
                                                katzTaoConstant *
                                              ENNReal.ofReal
                                                ((theta / δ) ^ 2) →
                                          ∀ core :
                                            HairbrushAmbientMultiplicityCoreData
                                              Y inputExponent layerLoss
                                                hairLoss,
                                            ENNReal.ofReal (δ ^ 2) ≤
                                                Kakeya.deltaTubeVolume δ →
                                              core.hairDensity ≤
                                                hairbrushHomogeneousLowDensityThreshold
                                                  δ zeta separation
                                                    angleScale →
                                                HairbrushFiberTarget
                                                  (theta := theta)
                                                  (loss := outputLoss) Y

/--
Uniform angle-scale parameters for the broad transverse stem argument.

Choose `angleScale = c(eta) * theta` with a sufficiently small positive
`c(eta)`.  The first two estimates make the two-broad cap contribute at most
one quarter.  Smallness of `δ` then supplies both the polynomial lower bound
used by angle-band pigeonholing and the fixed-constant loss needed to convert
the ambient-stem cardinality estimate into its normalized `theta` form.
-/
structure HairbrushHomogeneousParameterData
    (δ eta theta stemLoss : ℝ) where
  angleScale : ℝ
  angleScale_pos : 0 < angleScale
  angleScale_le_one : angleScale ≤ 1
  delta_le_angleScale : δ ≤ angleScale
  twice_angleScale_le_theta : 2 * angleScale ≤ theta
  transverse_cap_small :
    Real.rpow (2 * angleScale / theta) eta ≤ 1 / 4
  angle_polynomial_lower :
    Kakeya.realRpowENN δ 2 ≤ ENNReal.ofReal angleScale
  stem_factor_lower :
    Kakeya.realRpowENN δ stemLoss *
        ENNReal.ofReal theta ≤
      ENNReal.ofReal angleScale /
        ENNReal.ofReal (1000 * Real.pi)

/--
Choose the uniform angle scale used by ambient stem selection and the dyadic
angle-band step.

The conclusion keeps the constant-scale dichotomy from the proof of Lemma
B.3.  If `theta ≤ scaleSeparation * δ`, the normalized tube thickness
`δ / theta` is bounded below and the small-angular-scale easy branch applies.
Otherwise choose `angleScale = c(eta) * theta`, where
`scaleSeparation = c(eta)⁻¹`; then `δ ≤ angleScale` and all hard-branch
certificates hold.
-/
def HairbrushHomogeneousParameterSelectionStatement : Prop :=
  ∀ eta stemLoss : ℝ,
    0 < eta →
      0 < stemLoss →
        ∃ scaleSeparation delta₀ : ℝ,
          1 ≤ scaleSeparation ∧
            0 < delta₀ ∧ delta₀ ≤ 1 / 1000 ∧
              ∀ δ : ℝ, 0 < δ → δ ≤ delta₀ →
                ∀ theta : ℝ, δ ≤ theta → theta ≤ 1 →
                  theta ≤ scaleSeparation * δ ∨
                    Nonempty
                      (HairbrushHomogeneousParameterData
                        δ eta theta stemLoss)

/--
The constant-normalized-thickness easy branch of the local hairbrush lemma.

When `theta ≤ scaleSeparation * δ`, angular confinement and angle separation
give an absolute pointwise multiplicity bound depending only on
`scaleSeparation`: directions through one point form a separated set inside
one `theta`-cap.  The aggregate shaded incidence mass lower bound and this
multiplicity bound directly imply the original-coordinate square-root
target.  No per-tube pruning is needed.  The strict gap `eta < loss` absorbs
the fixed packing constant.
-/
def HairbrushHomogeneousSmallScaleStatement : Prop :=
  ∀ eta loss scaleSeparation : ℝ,
    0 < eta →
      eta < loss →
        1 ≤ scaleSeparation →
          ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 / 1000 ∧
            ∀ δ theta : ℝ,
              0 < δ → δ ≤ delta₀ →
                δ ≤ theta → theta ≤ 1 →
                  theta ≤ scaleSeparation * δ →
                    ∀ (F : Kakeya.TubeFamily δ),
                      F.Nonempty →
                        HairbrushAngleSeparated F →
                          HairbrushAngularlyConfined F theta →
                            ∀ Y : Kakeya.Shading F,
                              HairbrushAggregateDense Y
                                (Kakeya.realRpowENN δ eta) →
                                HairbrushFiberTarget
                                  (theta := theta) (loss := loss) Y

/--
The exponent appearing in (B.28):
`p_zeta = (1 + 3*zeta) / (1-zeta)`.
-/
def hairbrushHomogeneousDensityPower (zeta : ℝ) : ℝ :=
  (1 + 3 * zeta) / (1 - zeta)

/--
Pure power assembly for the hard homogeneous hairbrush branch.

The hypotheses are the normalized numerical content of:

* weighted hair retention (B.15);
* common-radius family retention (B.18);
* refined density and the radius-density relation (B.19)--(B.20);
* ambient-stem degree and angle-band retention (B.24);
* fixed-stem Córdoba after denominator absorption (B.27).

The conclusion is (B.28), with all fixed constants absorbed by the strict
`outputExponent` gap.  Geometry and construction of the displayed quantities
are deliberately outside this leaf.
-/
def HairbrushHomogeneousHardPowerStatement : Prop :=
  ∀ zeta stemLoss bandLoss familyLoss hairLoss cordobaLoss
      outputExponent : ℝ,
    0 < zeta → zeta < 1 →
      0 ≤ stemLoss → 0 ≤ bandLoss →
        0 ≤ familyLoss → 0 ≤ hairLoss →
          0 ≤ cordobaLoss →
            1 + stemLoss + bandLoss + familyLoss +
                hairLoss + cordobaLoss <
              outputExponent →
              ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 / 1000 ∧
                ∀ δ : ℝ, 0 < δ → δ ≤ delta₀ →
                  ∀ theta radius : ℝ,
                    0 < theta → theta ≤ 1 →
                      δ ≤ radius → radius ≤ 2 →
                        ∀ ambientCount hairCount refinedCount
                            brushCount bandCount mu
                            layerDensity hairDensity refinedDensity
                            targetVolume : ENNReal,
                          ambientCount ≠ 0 → ambientCount ≠ ⊤ →
                            hairCount ≠ 0 → hairCount ≠ ⊤ →
                              refinedCount ≠ 0 → refinedCount ≠ ⊤ →
                                brushCount ≠ 0 → brushCount ≠ ⊤ →
                                  bandCount ≠ 0 → bandCount ≠ ⊤ →
                                    mu ≠ 0 → mu ≠ ⊤ →
                                      layerDensity ≠ 0 →
                                        layerDensity ≠ ⊤ →
                                          hairDensity ≠ 0 →
                                            hairDensity ≠ ⊤ →
                                              refinedDensity ≠ 0 →
                                                refinedDensity ≠ ⊤ →
                                                  targetVolume ≠ ⊤ →
                                  layerDensity / 2 ≤ hairDensity →
                                  Kakeya.realRpowENN δ hairLoss *
                                          layerDensity * ambientCount ≤
                                      hairDensity * hairCount →
                                  Kakeya.realRpowENN δ familyLoss *
                                          hairCount ≤
                                      refinedCount →
                                  ENNReal.ofReal
                                          (Real.rpow radius zeta) *
                                        hairDensity ≤
                                      refinedDensity →
                                  hairDensity ≤
                                      ENNReal.ofReal 100 *
                                        ENNReal.ofReal
                                          (Real.rpow radius (1 - zeta)) →
                                  Kakeya.realRpowENN δ stemLoss *
                                          ENNReal.ofReal theta * mu *
                                          refinedDensity * refinedCount /
                                        (ENNReal.ofReal δ * ambientCount) ≤
                                      brushCount →
                                  Kakeya.realRpowENN δ bandLoss *
                                          brushCount ≤
                                      bandCount →
                                  Kakeya.realRpowENN δ cordobaLoss *
                                          ENNReal.ofReal radius *
                                          refinedDensity ^ 2 * bandCount *
                                          ENNReal.ofReal (δ ^ 2) ≤
                                      targetVolume →
                                  Kakeya.realRpowENN δ outputExponent *
                                          ENNReal.ofReal theta *
                                          ENNReal.rpow layerDensity
                                            (3 +
                                              hairbrushHomogeneousDensityPower
                                                zeta) *
                                          mu ≤
                                      targetVolume

/--
Output of the ambient-stem averaging argument.

The selected stem remains in the full ambient family.  The brush consists of
hairs whose selected shading has positive overlap with the stem shading and
whose acute angle from the stem is at least `angleScale`.
-/
structure HairbrushAmbientStemSelectionData
    {δ angleScale hairDensity : ℝ}
    {F : Kakeya.TubeFamily δ} (layer : Kakeya.Shading F)
    (mu : ℕ)
    {H : Kakeya.TubeFamily δ} (hairShading : Kakeya.Shading H) where
  stem : Kakeya.DeltaTube δ
  stem_mem : stem ∈ F
  brush : Kakeya.TubeFamily δ
  brush_subset : brush ⊆ H
  transverse_overlap :
    ∀ T ∈ brush,
      angleScale ≤ hairbrushAcuteAngle T stem ∧
        volume (hairShading.carrier T ∩ layer.carrier stem) ≠ 0
  brush_cardinality_lower :
    ENNReal.ofReal angleScale * (mu : ENNReal) *
          ENNReal.ofReal hairDensity * H.enncard /
        (ENNReal.ofReal (1000 * Real.pi) *
          ENNReal.ofReal δ * F.enncard) ≤
      brush.enncard

/--
Select one ambient stem with many transverse hairs, corresponding to
(B.22)--(B.24).

The input layer has multiplicity at least `mu` and is relatively broad at
scale `theta`.  The numerical condition on `angleScale` makes the cap of
directions within `angleScale` of a fixed hair contain at most one quarter of
the tubes through a surviving point.  Integrating the remaining transverse
multiplicity over every hair, using the standard transverse tube-intersection
volume bound, and averaging over the ambient stems yields the output.

The hair family may be a strict subfamily of the ambient family.
-/
def HairbrushAmbientStemSelectionStatement : Prop :=
  ∀ eta theta angleScale : ℝ,
    0 < eta →
      0 < theta → theta ≤ 1 →
        0 < angleScale →
          2 * angleScale ≤ theta →
            Real.rpow (2 * angleScale / theta) eta ≤ 1 / 4 →
              ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 / 1000 ∧
                ∀ δ : ℝ, 0 < δ → δ ≤ delta₀ →
                  δ ≤ angleScale →
                    ∀ (F : Kakeya.TubeFamily δ)
                        (layer : Kakeya.Shading F),
                      F.Nonempty →
                        ∀ mu : ℕ, 0 < mu →
                          (∀ x ∈ layer.union,
                            mu ≤
                              (F.filter fun T =>
                                x ∈ layer.carrier T).card) →
                          IsTwoBroadAtScale layer theta eta →
                            ∀ (H : Kakeya.TubeFamily δ),
                              H.Nonempty →
                                H ⊆ F →
                                  ∀ hairShading : Kakeya.Shading H,
                                    (∀ T ∈ H,
                                      hairShading.carrier T ⊆
                                        layer.carrier T) →
                                    ∀ hairDensity : ℝ,
                                      0 < hairDensity →
                                        (∀ T ∈ H,
                                          ENNReal.ofReal hairDensity *
                                              T.volume ≤
                                            volume
                                              (hairShading.carrier T)) →
                                        Nonempty
                                          (HairbrushAmbientStemSelectionData
                                            (angleScale := angleScale)
                                            (hairDensity := hairDensity)
                                            layer mu hairShading)

/--
One acute angle band and its orientation relative to a supplied stem.
-/
structure HairbrushOrientedAngleBandData
    {δ angleScale bandLoss : ℝ}
    {B : Kakeya.TubeFamily δ} (Z : Kakeya.Shading B)
    (stem : Kakeya.DeltaTube δ) where
  sigma : ℝ
  angleScale_le_sigma : angleScale ≤ sigma
  sigma_le_one : sigma ≤ 1
  source : Kakeya.TubeFamily δ
  source_subset : source ⊆ B
  source_nonempty : source.Nonempty
  source_retention :
    Kakeya.realRpowENN δ bandLoss * B.enncard ≤ source.enncard
  source_angle :
    ∀ U ∈ source,
      sigma ≤ hairbrushAcuteAngle stem U ∧
        hairbrushAcuteAngle stem U ≤ 2 * sigma
  source_intersects :
    ∀ U ∈ source, (stem.carrier ∩ U.carrier).Nonempty
  oriented : Kakeya.TubeFamily δ
  oriented_eq :
    oriented = source.image (orientTube stem)
  oriented_card :
    oriented.enncard = source.enncard
  shading : Kakeya.Shading oriented
  shading_carrier :
    ∀ U ∈ source,
      shading.carrier (orientTube stem U) = Z.carrier U
  oriented_angle :
    ∀ U ∈ oriented,
      sigma ≤ Kakeya.Hairbrush.angleBetween stem U ∧
        Kakeya.Hairbrush.angleBetween stem U ≤ 2 * sigma
  oriented_intersects :
    ∀ U ∈ oriented, (stem.carrier ∩ U.carrier).Nonempty

/--
Pigeonhole one acute angle band from a supplied transverse brush and orient
it toward the stem.

The lower bound `δ^angleExponent ≤ angleScale` makes the number of dyadic
bands logarithmic in `1/δ`, which is absorbed by the positive `bandLoss`.
The input brush already consists of hairs meeting the stem at acute angle at
least `angleScale`.
-/
def HairbrushOrientedAngleBandStatement : Prop :=
  ∀ angleExponent bandLoss : ℝ,
    0 < angleExponent → 0 < bandLoss →
      ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 / 1000 ∧
        ∀ δ : ℝ, 0 < δ → δ ≤ delta₀ →
          ∀ angleScale : ℝ,
            0 < angleScale →
              Kakeya.realRpowENN δ angleExponent ≤
                ENNReal.ofReal angleScale →
              angleScale ≤ 1 →
                ∀ (B : Kakeya.TubeFamily δ) (Z : Kakeya.Shading B),
                  B.Nonempty →
                    B.IsEssentiallyDistinct →
                      ∀ stem : Kakeya.DeltaTube δ,
                        (∀ U ∈ B,
                          angleScale ≤ hairbrushAcuteAngle stem U) →
                        (∀ U ∈ B,
                          (stem.carrier ∩ U.carrier).Nonempty) →
                          Nonempty
                            (HairbrushOrientedAngleBandData
                              (angleScale := angleScale)
                              (bandLoss := bandLoss) Z stem)

/--
Carrier-preserving orientation transports the structural hypotheses needed by
the fixed-stem Córdoba estimate.

For an arbitrary subfamily of an essentially-distinct ambient family,
`orientTube stem` is injective.  Since it preserves carriers and tube volume,
the oriented image has the same cardinality, remains nonempty and essentially
distinct, and inherits the same Katz--Tao convex Wolff bound.
-/
def HairbrushOrientedFamilyTransferStatement : Prop :=
  ∀ δ katzTaoConstant : ℝ,
    0 < δ → δ ≤ 1 →
      ∀ (F source : Kakeya.TubeFamily δ),
        F.IsEssentiallyDistinct →
          source ⊆ F →
            source.Nonempty →
              Kakeya.KatzTaoConvexWolffBound F katzTaoConstant →
                ∀ stem : Kakeya.DeltaTube δ,
                  let oriented : Kakeya.TubeFamily δ :=
                    source.image (orientTube stem)
                  oriented.Nonempty ∧
                    oriented.enncard = source.enncard ∧
                      oriented.IsEssentiallyDistinct ∧
                        Kakeya.KatzTaoConvexWolffBound
                          oriented katzTaoConstant

/-- Numerical radius package obtained from one spatial two-ends refinement. -/
structure HairbrushTwoEndsFarRadiusData
    {δ massLoss scaleLoss zetaEnds sigma kappa : ℝ}
    {F : Kakeya.TubeFamily δ} {Y : Kakeya.Shading F}
    (refinement :
      HairbrushSpatialTwoEndsRefinementData
        Y massLoss scaleLoss zetaEnds) where
  farRadius : ℝ
  nearRadius : ℝ
  far_radius_eq :
    farRadius =
      Real.rpow δ kappa * sigma * refinement.r0 / 64
  near_radius_eq :
    nearRadius = 8 * (farRadius / sigma + δ)
  delta_le_farRadius : δ ≤ farRadius
  nearRadius_pos : 0 < nearRadius
  nearRadius_le_r0 : nearRadius ≤ refinement.r0
  near_ball_mass :
    ∀ U ∈ F, ∀ x : Point3,
      Metric.infDist x
          (Kakeya.unitSegment U.base U.direction) ≤ δ →
        volume
            (refinement.shading.carrier U ∩
              Metric.ball x nearRadius) ≤
          (1 / 4 : ENNReal) *
            volume (refinement.shading.carrier U)

/--
Choose the effective far-cylinder and near-ball radii from a supplied spatial
two-ends refinement.

The angle band has lower endpoint at least `δ^angleExponent`.  The inequality
`kappa + scaleLoss + angleExponent < 1` makes the far radius exceed `δ`; the
inequality `massLoss < kappa * zetaEnds` makes the two-ends coefficient at the
near radius at most one quarter.  All fixed numerical factors are absorbed by
choosing `δ` sufficiently small.
-/
def HairbrushTwoEndsFarRadiusStatement : Prop :=
  ∀ angleExponent massLoss scaleLoss zetaEnds kappa : ℝ,
    0 < angleExponent →
      0 < massLoss →
        0 < scaleLoss → scaleLoss < 1 →
          0 < zetaEnds → zetaEnds < 1 →
            0 < kappa →
              kappa + scaleLoss + angleExponent < 1 →
                massLoss < kappa * zetaEnds →
                  ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 / 1000 ∧
                    ∀ δ : ℝ, 0 < δ → δ ≤ delta₀ →
                      ∀ sigma : ℝ,
                        Kakeya.realRpowENN δ angleExponent ≤
                            ENNReal.ofReal sigma →
                          sigma ≤ 1 →
                          ∀ (F : Kakeya.TubeFamily δ)
                              (Y : Kakeya.Shading F),
                            ∀ refinement :
                              HairbrushSpatialTwoEndsRefinementData
                                Y massLoss scaleLoss zetaEnds,
                              Nonempty
                                (HairbrushTwoEndsFarRadiusData
                                  (sigma := sigma) (kappa := kappa)
                                  refinement)

/--
Far-cylinder shading on an asymmetric supplied hair family.
-/
structure HairbrushAsymmetricFarShadingData
    {δ farRadius : ℝ}
    {H : Kakeya.TubeFamily δ} (Z : Kakeya.Shading H)
    (stem : Kakeya.DeltaTube δ) where
  shading : Kakeya.Shading H
  carrier_eq :
    ∀ U ∈ H,
      shading.carrier U =
        Z.carrier U ∩
          {x |
            farRadius ≤
              ‖Kakeya.Assouad.perpProj
                stem.direction (x - stem.base)‖}
  mass_lower :
    ∀ U ∈ H,
      (1 / 4 : ENNReal) * volume (Z.carrier U) ≤
        volume (shading.carrier U)

/--
Remove the part of every supplied transverse hair near the stem axis.

The geometric radius certificate places the near-cylinder portion of each
hair in one ball of radius `nearRadius`.  The supplied near-ball mass bound
then leaves at least one quarter of every hair shading outside the cylinder.
This is the core-independent form of the validated equation-(19) proof.
-/
def HairbrushAsymmetricFarShadingStatement : Prop :=
  ∀ δ sigma farRadius nearRadius : ℝ,
    0 < δ →
      0 < sigma → sigma ≤ 1 →
        0 < farRadius →
          0 < nearRadius →
            2 * δ +
                Real.pi * (farRadius + 3 * δ) / (2 * sigma) <
              nearRadius →
              ∀ (H : Kakeya.TubeFamily δ) (Z : Kakeya.Shading H),
                ∀ stem : Kakeya.DeltaTube δ,
                  (∀ U ∈ H,
                    sigma ≤ hairbrushAcuteAngle stem U ∧
                    hairbrushAcuteAngle stem U ≤ 2 * sigma) →
                  (∀ U ∈ H,
                    (stem.carrier ∩ U.carrier).Nonempty) →
                  (∀ U ∈ H, ∀ x : Point3,
                    Metric.infDist x
                        (Kakeya.unitSegment U.base U.direction) ≤ δ →
                      volume
                          (Z.carrier U ∩
                            Metric.ball x nearRadius) ≤
                        (1 / 4 : ENNReal) *
                          volume (Z.carrier U)) →
                    Nonempty
                      (HairbrushAsymmetricFarShadingData
                        (farRadius := farRadius) Z stem)

/--
Transport a two-ends near-ball estimate through angle-band orientation and
apply the core-independent far-shading theorem.

The source band shading agrees with the supplied two-ends refinement.  Tube
orientation preserves both the carrier and the underlying unit segment, so
the original near-ball estimate transfers to every oriented hair.
-/
def HairbrushOrientedFarShadingStatement : Prop :=
  HairbrushAsymmetricFarShadingStatement →
    ∀ δ angleScale bandLoss massLoss scaleLoss zetaEnds kappa : ℝ,
      0 < δ →
        0 < angleScale →
          ∀ (F : Kakeya.TubeFamily δ) (Y : Kakeya.Shading F),
            ∀ refinement :
              HairbrushSpatialTwoEndsRefinementData
                Y massLoss scaleLoss zetaEnds,
              ∀ (B : Kakeya.TubeFamily δ) (Z : Kakeya.Shading B),
                B ⊆ F →
                  (∀ U ∈ B,
                    Z.carrier U =
                      refinement.shading.carrier U) →
                  ∀ stem : Kakeya.DeltaTube δ,
                    ∀ band :
                      HairbrushOrientedAngleBandData
                        (angleScale := angleScale)
                        (bandLoss := bandLoss) Z stem,
                      ∀ radii :
                        HairbrushTwoEndsFarRadiusData
                          (sigma := band.sigma) (kappa := kappa)
                          refinement,
                        Nonempty
                          (HairbrushAsymmetricFarShadingData
                            (farRadius := radii.farRadius)
                            band.shading stem)

/--
Orient the relevant subfamily of a homogeneous two-ends output and transport
its shading, radius, and absolute two-ends estimate.
-/
def HairbrushHomogeneousOrientedFarShadingStatement : Prop :=
  HairbrushAsymmetricFarShadingStatement →
    ∀ δ zeta familyLoss bandLoss angleScale : ℝ,
      0 < δ →
        ∀ (H : Kakeya.TubeFamily δ) (Z : Kakeya.Shading H),
          H.IsEssentiallyDistinct →
            ∀ hairDensity : ENNReal,
              ∀ twoEnds :
                HairbrushHomogeneousTwoEndsData
                  (zeta := zeta) (familyLoss := familyLoss)
                  Z hairDensity,
                ∀ (B : Kakeya.TubeFamily δ)
                    (ZB : Kakeya.Shading B),
                  B ⊆ twoEnds.family →
                    (∀ U ∈ B,
                      ZB.carrier U =
                        twoEnds.shading.carrier U) →
                    ∀ stem : Kakeya.DeltaTube δ,
                      ∀ band :
                        HairbrushOrientedAngleBandData
                          (angleScale := angleScale)
                          (bandLoss := bandLoss) ZB stem,
                        ∀ farFraction : ℝ,
                          ∀ radii :
                            HairbrushHomogeneousFarRadiusData
                              (sigma := band.sigma) twoEnds farFraction,
                            Nonempty
                              (HairbrushAsymmetricFarShadingData
                                (farRadius := radii.farRadius)
                                band.shading stem)

/--
Frostman cardinality and coarse-count consequences for balanced slab groups.
-/
structure HairbrushBalancedFrostmanCountData
    {δ eta stopLoss densityFloor balanceLoss frostmanExponent
      totalLoss coarseLoss : ℝ}
    {F : Kakeya.TubeFamily δ} {Y : Kakeya.Shading F}
    {angular :
      HairbrushLabeledAngularStoppingData
        Y eta stopLoss}
    {grouping : HairbrushSlabIncidenceGroupingData angular}
    (balanced :
      HairbrushBalancedSlabGroupsData
        (densityFloor := densityFloor)
        (balanceLoss := balanceLoss) grouping) where
  typical_card_upper :
    (balanced.typicalCard : ENNReal) ≤
      ENNReal.ofReal
          (100 * Real.rpow δ (-frostmanExponent) *
            angular.capRadius) *
        F.enncard
  selected_cardinality_lower :
    Kakeya.realRpowENN δ totalLoss * F.enncard ≤
      (balanced.selectedCount : ENNReal) *
        (balanced.typicalCard : ENNReal)
  coarse_count_lower :
    Kakeya.realRpowENN δ coarseLoss ≤
      ENNReal.ofReal angular.theta *
        (balanced.selectedCount : ENNReal)

/--
Derive the balanced cardinality retention and Frostman lower bound for the
number of selected slab groups, corresponding to (B.36)--(B.41).

The aggregate density and balancing retention give
`q * M >= δ^totalLoss * #F`.  The Frostman slab bound and slab-volume field
give `M <= O(δ^-frostmanExponent * theta * #F)`.  Combining the two estimates
gives `theta * q >= δ^coarseLoss`, after absorbing fixed constants at small
`δ`.
-/
def HairbrushBalancedFrostmanCountStatement : Prop :=
  ∀ inputExponent balanceLoss frostmanExponent totalLoss coarseLoss : ℝ,
    0 < inputExponent →
      0 < balanceLoss →
        0 ≤ frostmanExponent →
          inputExponent + balanceLoss < totalLoss →
            totalLoss + frostmanExponent < coarseLoss →
              ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 / 1000 ∧
                ∀ δ : ℝ, 0 < δ → δ ≤ delta₀ →
                  ∀ eta stopLoss densityFloor : ℝ,
                    ∀ (F : Kakeya.TubeFamily δ)
                        (Y : Kakeya.Shading F),
                      F.Nonempty →
                        Kakeya.FrostmanSlabWolffBound F
                          (Real.rpow δ (-frostmanExponent)) →
                        ∀ angular :
                          HairbrushLabeledAngularStoppingData
                            Y eta stopLoss,
                          HairbrushAggregateDense angular.shading
                            (Kakeya.realRpowENN δ inputExponent) →
                          ∀ grouping :
                            HairbrushSlabIncidenceGroupingData angular,
                            ∀ balanced :
                              HairbrushBalancedSlabGroupsData
                                (densityFloor := densityFloor)
                                (balanceLoss := balanceLoss) grouping,
                              Nonempty
                                (HairbrushBalancedFrostmanCountData
                                  (frostmanExponent := frostmanExponent)
                                  (totalLoss := totalLoss)
                                  (coarseLoss := coarseLoss)
                                  balanced)

/--
Sum local square-root hairbrush estimates over balanced slab groups.

Pairwise disjoint group unions turn the sum of local volume lower bounds into
a lower bound for the original angular shading union.  The balanced
cardinality lower bound and Frostman coarse-count lower bound cancel the
selected group count and the common angular scale.
-/
def HairbrushBalancedGroupSummationStatement : Prop :=
  ∀ localLoss totalLoss coarseLoss outputLoss : ℝ,
    0 < localLoss →
      localLoss + (totalLoss + coarseLoss) / 2 < outputLoss →
        ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 / 1000 ∧
          ∀ δ : ℝ, 0 < δ → δ ≤ delta₀ →
            ∀ eta stopLoss densityFloor balanceLoss frostmanExponent : ℝ,
              ∀ (F : Kakeya.TubeFamily δ)
                  (Y : Kakeya.Shading F),
                F.Nonempty →
                  ∀ angular :
                    HairbrushLabeledAngularStoppingData
                      Y eta stopLoss,
                    ∀ grouping :
                      HairbrushSlabIncidenceGroupingData angular,
                      ∀ balanced :
                        HairbrushBalancedSlabGroupsData
                          (densityFloor := densityFloor)
                          (balanceLoss := balanceLoss) grouping,
                        ∀ counts :
                          HairbrushBalancedFrostmanCountData
                            (frostmanExponent := frostmanExponent)
                            (totalLoss := totalLoss)
                            (coarseLoss := coarseLoss) balanced,
                          (∀ j,
                            HairbrushFiberTarget
                              (theta := angular.theta)
                              (loss := localLoss)
                              (grouping.shading
                                (balanced.select j))) →
                            HairbrushFiberTarget
                              (theta := 1)
                              (loss := outputLoss)
                              angular.shading

/--
Pure numerical closure of the robust-transverse local hairbrush argument.

`incidenceUpper` is the constant in the lower side of the incidence identity
`density * N * δ² ≤ incidenceUpper * mu * V`.
`hairbrushConstant` and `hairbrushExponent` encode the hard hairbrush lower
bound
`hairbrushConstant * δ^hairbrushExponent * theta *
  density^densityPower * mu ≤ V`.
Their product eliminates the pointwise multiplicity `mu`.
-/
def HairbrushLocalNumericalClosureStatement : Prop :=
  ∀ densityExponent hairbrushExponent densityPower constantLoss outputLoss : ℝ,
    0 < densityExponent →
      1 ≤ densityPower →
        0 < hairbrushExponent →
          0 < constantLoss →
          (hairbrushExponent + 2 +
                densityExponent * (densityPower + 1) +
                2 * constantLoss) / 2 <
            3 / 2 + outputLoss →
            ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 / 1000 ∧
              ∀ δ : ℝ, 0 < δ → δ ≤ delta₀ →
                ∀ theta : ℝ, 0 < theta → theta ≤ 1 →
                  ∀ N mu : ENNReal,
                  N ≠ 0 → N ≠ ⊤ →
                    mu ≠ 0 → mu ≠ ⊤ →
                      ∀ density V : ENNReal,
                        density ≠ 0 → density ≠ ⊤ →
                          V ≠ ⊤ →
                            Kakeya.realRpowENN δ densityExponent ≤
                              density →
                            ∀ incidenceUpper hairbrushConstant : ENNReal,
                              incidenceUpper ≠ 0 →
                              incidenceUpper ≠ ⊤ →
                              hairbrushConstant ≠ 0 →
                              hairbrushConstant ≠ ⊤ →
                              incidenceUpper ≤
                                Kakeya.realRpowENN δ (-constantLoss) →
                              Kakeya.realRpowENN δ constantLoss ≤
                                hairbrushConstant →
                              ENNReal.ofReal
                                  (Real.rpow δ hairbrushExponent) *
                                  hairbrushConstant *
                                  ENNReal.ofReal theta *
                                  ENNReal.rpow density densityPower *
                                  mu ≤
                                V →
                              density * N *
                                  ENNReal.ofReal (δ ^ 2) ≤
                                incidenceUpper * mu * V →
                              Kakeya.realRpowENN δ
                                  (3 / 2 + outputLoss) *
                                  ENNReal.ofReal (Real.sqrt theta) *
                                  ENNReal.rpow N (1 / 2) ≤
                                V

/-- The logarithmic Córdoba denominator used by one fixed stem. -/
def hairbrushFixedStemCordobaDenominator
    (δ katzTaoConstant : ℝ) : ENNReal :=
  1 +
    ENNReal.ofReal
      (2000 * (3 : ℝ) * katzTaoConstant * 32 * Real.pi) *
      ENNReal.ofReal (Real.log (1 / δ))

/--
Absorb the fixed-stem Córdoba denominator and recover the homogeneous radius
factor in (B.27).

When `farRadius = farFraction * sigma * radius`,
`sigma / farRadius + 1` is `O_{farFraction}(radius⁻¹)`.  The Katz--Tao
denominator contributes `δ^(-katzExponent)` and one logarithm.  Any strict
loss `katzExponent < outputLoss` absorbs those constants and the logarithm.
-/
def HairbrushCordobaDenominatorAbsorptionStatement : Prop :=
  ∀ katzExponent outputLoss farFraction densityFraction : ℝ,
    0 ≤ katzExponent →
      katzExponent < outputLoss →
        0 < farFraction →
          0 < densityFraction →
            ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 / 1000 ∧
              ∀ δ : ℝ, 0 < δ → δ ≤ delta₀ →
                ∀ katzTaoConstant : ℝ,
                  0 ≤ katzTaoConstant →
                    ENNReal.ofReal katzTaoConstant ≤
                      Kakeya.realRpowENN δ (-katzExponent) →
                    ∀ sigma radius farRadius : ℝ,
                      0 < sigma →
                        δ ≤ radius → radius ≤ 2 →
                          farRadius =
                            farFraction * sigma * radius →
                            Kakeya.realRpowENN δ outputLoss *
                                ENNReal.ofReal radius ≤
                              ENNReal.ofReal densityFraction ^ 2 *
                                (hairbrushFixedStemCordobaDenominator
                                      δ katzTaoConstant *
                                    ENNReal.ofReal
                                      (100 * (sigma / farRadius + 1)))⁻¹

/--
The supplied hair shading lies outside a cylinder of radius `farRadius`
around the stem axis.
-/
def HairbrushFarFromStem {δ farRadius : ℝ}
    {H : Kakeya.TubeFamily δ} (Z : Kakeya.Shading H)
    (stem : Kakeya.DeltaTube δ) : Prop :=
  ∀ U ∈ H,
    Z.carrier U ⊆
      {x |
        farRadius ≤
          ‖Kakeya.Assouad.perpProj
            stem.direction (x - stem.base)‖}

/--
The asymmetric fixed-stem plane-covering/Córdoba estimate.

The hairs have already been selected and oriented.  Every hair meets one
supplied stem at an ordinary angle in `[sigma, 2*sigma]`, carries a uniform
shading density, and lies outside the supplied far cylinder.  The conclusion
is the exact bound obtained by:

1. covering the hair directions by thickened planes through the stem;
2. applying the planar Córdoba estimate in every bin;
3. using the far-cylinder multiplicity bound to sum the bins.

Stem selection, the degree lower bound, two-ends localization, and final
parameter absorption are deliberately outside this leaf.
-/
def HairbrushAsymmetricFixedStemCordobaStatement : Prop :=
  ∀ δ sigma farRadius katzTaoConstant : ℝ,
    0 < δ → δ ≤ 1 / 1000 →
      0 < sigma → sigma ≤ 1 →
        0 < farRadius →
          0 ≤ katzTaoConstant →
            ∀ (H : Kakeya.TubeFamily δ) (Z : Kakeya.Shading H),
              H.Nonempty →
                H.IsEssentiallyDistinct →
                  Kakeya.KatzTaoConvexWolffBound H katzTaoConstant →
                    ∀ stem : Kakeya.DeltaTube δ,
                      (∀ U ∈ H,
                        sigma ≤ Kakeya.Hairbrush.angleBetween stem U ∧
                        Kakeya.Hairbrush.angleBetween stem U ≤ 2 * sigma) →
                      (∀ U ∈ H,
                        (stem.carrier ∩ U.carrier).Nonempty) →
                      HairbrushFarFromStem
                          (farRadius := farRadius) Z stem →
                      ∀ density : ENNReal,
                        density ≠ ⊤ →
                        (∀ U ∈ H,
                          density * U.volume ≤ volume (Z.carrier U)) →
                        ENNReal.ofReal (δ ^ 2) ≤
                            Kakeya.deltaTubeVolume δ →
                          density ^ 2 * H.enncard *
                                Kakeya.deltaTubeVolume δ /
                              (hairbrushFixedStemCordobaDenominator
                                  δ katzTaoConstant *
                                ENNReal.ofReal
                                  (100 * (sigma / farRadius + 1))) ≤
                            volume Z.union

/--
Geometric fixed-stem Córdoba assembly for one homogeneous angle band.

The source band is a subfamily of the homogeneous two-ends output.  Its
oriented far shading has retained a fixed fraction of the refined per-hair
density.  Carrier-preserving orientation transfers essential distinctness and
Katz--Tao control; the validated fixed-stem Córdoba estimate is then combined
with denominator absorption to produce the exact radius-weighted B.27 input
consumed by `HairbrushHomogeneousHardPowerStatement`.
-/
def HairbrushHomogeneousCordobaGeometryStatement : Prop :=
  HairbrushOrientedFamilyTransferStatement →
    HairbrushAsymmetricFixedStemCordobaStatement →
      HairbrushCordobaDenominatorAbsorptionStatement →
        ∀ katzExponent cordobaLoss farFraction : ℝ,
          0 ≤ katzExponent →
            katzExponent < cordobaLoss →
              0 < farFraction →
                ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 / 1000 ∧
                  ∀ δ : ℝ, 0 < δ → δ ≤ delta₀ →
                    ∀ katzTaoConstant : ℝ,
                      0 ≤ katzTaoConstant →
                        ENNReal.ofReal katzTaoConstant ≤
                          Kakeya.realRpowENN δ (-katzExponent) →
                        ∀ (F : Kakeya.TubeFamily δ)
                            (Y : Kakeya.Shading F),
                          F.IsEssentiallyDistinct →
                            Kakeya.KatzTaoConvexWolffBound
                              F katzTaoConstant →
                            ∀ zeta familyLoss bandLoss angleScale : ℝ,
                              ∀ (H : Kakeya.TubeFamily δ)
                                  (Z : Kakeya.Shading H),
                                H ⊆ F →
                                  (∀ U ∈ H,
                                    Z.carrier U ⊆ Y.carrier U) →
                                  ∀ hairDensity : ENNReal,
                                    hairDensity ≠ ⊤ →
                                    ∀ twoEnds :
                                      HairbrushHomogeneousTwoEndsData
                                        (zeta := zeta)
                                        (familyLoss := familyLoss)
                                        Z hairDensity,
                                      ∀ (B : Kakeya.TubeFamily δ)
                                          (ZB : Kakeya.Shading B),
                                        B ⊆ twoEnds.family →
                                          (∀ U ∈ B,
                                            ZB.carrier U =
                                              twoEnds.shading.carrier U) →
                                          ∀ stem : Kakeya.DeltaTube δ,
                                            ∀ band :
                                              HairbrushOrientedAngleBandData
                                                (angleScale := angleScale)
                                                (bandLoss := bandLoss)
                                                ZB stem,
                                              ∀ radii :
                                                HairbrushHomogeneousFarRadiusData
                                                  (sigma := band.sigma)
                                                  twoEnds farFraction,
                                                ∀ far :
                                                  HairbrushAsymmetricFarShadingData
                                                    (farRadius :=
                                                      radii.farRadius)
                                                    band.shading stem,
                                                  Kakeya.realRpowENN δ
                                                        cordobaLoss *
                                                      ENNReal.ofReal
                                                        twoEnds.radius *
                                                      (ENNReal.ofReal
                                                            (Real.rpow
                                                              twoEnds.radius
                                                              zeta) *
                                                          hairDensity) ^ 2 *
                                                      band.oriented.enncard *
                                                      ENNReal.ofReal (δ ^ 2) ≤
                                                    volume Y.union

/--
Canonical local Lemma B.3 in the original coordinates.

Unlike the historical local API, this statement uses the aggregate/average
shading density from the paper.  It also separates the target broadness scale
`theta` from the rounded confinement radius `confinementScale`; the global
finite-label grouping only guarantees these scales are comparable.  The
explicit cardinality input is exactly the normalized Katz--Tao bound produced
by `HairbrushCoarseTubeKatzTaoCardinalityStatement`.  In accordance with
(B.34)--(B.38), the broadness and Katz--Tao exponent is `eta`, while the
balanced average density is only bounded below by `δ^(4*eta)`.
-/
def HairbrushSelfContainedFiberEstimateStatement : Prop :=
  ∀ loss : ℝ, 0 < loss →
    ∃ eta delta₀ : ℝ,
      0 < eta ∧ eta ≤ min (loss / 100) (1 / 100) ∧
        0 < delta₀ ∧ delta₀ ≤ 1 / 1000 ∧
          ∀ δ theta confinementScale : ℝ,
            0 < δ → δ ≤ delta₀ →
              δ ≤ theta → theta ≤ confinementScale →
                confinementScale ≤ 6 * theta →
                  confinementScale ≤ 1 →
                    ∀ (F : Kakeya.TubeFamily δ),
                      F.Nonempty →
                        F.IsInUnitBall →
                          F.IsEssentiallyDistinct →
                            HairbrushAngleSeparated F →
                              HairbrushAngularlyConfined
                                F confinementScale →
                                ∀ Y : Kakeya.Shading F,
                                  HairbrushAggregateDense Y
                                      (Kakeya.realRpowENN δ (4 * eta)) →
                                    Kakeya.KatzTaoConvexWolffBound F
                                      (Real.rpow δ (-eta)) →
                                      F.enncard ≤
                                        ENNReal.ofReal 100000000 *
                                          Kakeya.realRpowENN δ (-eta) *
                                          ENNReal.ofReal
                                            ((theta / δ) ^ 2) →
                                        IsTwoBroadAtScale Y theta eta →
                                          HairbrushFiberTarget
                                            (theta := theta)
                                            (loss := loss) Y

/--
Assembly boundary for the self-contained homogeneous proof of Lemma B.3.

Every hypothesis is one canonical leaf from (B.11)--(B.29).  The assembly
chooses all loss exponents, handles the constant-thickness and low-density
alternatives, constructs the hard hairbrush data, and invokes the final
incidence/numerical closure.  It must not use the historical symmetric Raw-B
core or the spatial two-ends API carrying an inverse power of `δ`.
-/
def HairbrushSelfContainedFiberAssemblyStatement : Prop :=
  HairbrushHomogeneousSmallScaleStatement →
    HairbrushAmbientMultiplicityCoreStatement →
      HairbrushAmbientIncidenceStatement →
        HairbrushHomogeneousTwoEndsStatement →
          HairbrushHomogeneousParameterSelectionStatement →
            HairbrushHomogeneousLowDensityStatement →
              HairbrushHomogeneousScaleDichotomyStatement →
                HairbrushAmbientStemSelectionStatement →
                  HairbrushOrientedAngleBandStatement →
                    HairbrushHomogeneousFarRadiusStatement →
                      HairbrushAsymmetricFarShadingStatement →
                        HairbrushHomogeneousOrientedFarShadingStatement →
                          HairbrushOrientedFamilyTransferStatement →
                            HairbrushAsymmetricFixedStemCordobaStatement →
                              HairbrushCordobaDenominatorAbsorptionStatement →
                                HairbrushHomogeneousCordobaGeometryStatement →
                                  HairbrushHomogeneousHardPowerStatement →
                                    HairbrushLocalNumericalClosureStatement →
                                      HairbrushSelfContainedFiberEstimateStatement

/--
Canonical global Appendix-B assembly.

Starting from the existing Assertion-D preprocessing, use pointwise angular
stopping, the paper-faithful coarse-`theta`-tube grouping, balancing, the
canonical local Lemma B.3, and the already validated Frostman/square-root
summation.  A convenient bookkeeping choice is:

* preprocessing/cardinality loss `eta / 2`;
* angular stopping loss `2 * eta`;
* balanced aggregate-density exponent `3 * eta`;
* local density floor `4 * eta`.

These are exactly the relative exponents in (B.30)--(B.38).  The remaining
cardinality, balancing, Frostman, and local losses are chosen strictly inside
the requested final `epsilon`.
-/
def HairbrushSelfContainedExpandedAssemblyStatement : Prop :=
  HairbrushPreprocessingStatement →
    HairbrushLabeledAngularStoppingStatement →
      HairbrushCoarseTubeIncidenceGroupingStatement →
        HairbrushCoarseTubeKatzTaoCardinalityStatement →
          HairbrushSlabGroupBalancingStatement →
            HairbrushBalancedFrostmanCountStatement →
              HairbrushBalancedGroupSummationStatement →
                HairbrushSelfContainedFiberEstimateStatement →
                  HairbrushExpandedEstimate

end Kakeya.Assouad
