import MyLeanRepo.Kakeya.Assouad.Subunit.HairbrushStatements
import MyLeanRepo.Kakeya.Hairbrush.Pigeonhole
import MyLeanRepo.Kakeya.Hairbrush.PlaneCovering.Basic

/-!
# Frozen leaves for the two-broad Wolff estimate

These interfaces split the hard branch of
`HairbrushTwoBroadFiberEstimateStatement` into three independent producers:

1. a multiplicity-dense spatial two-ends core, with a direct-estimate
   alternative for the concentrated branch;
2. an acute-angle robust-transversality selection on a supplied core;
3. the fixed-stem orientation and one-stem Raw-B estimate.

The loss exponents are deliberately separated:

* `aCore` controls cardinality and pointwise-multiplicity retention;
* `zetaEnds` is the spatial two-ends exponent;
* `bTube` controls per-tube mass retention.

This prevents the false logarithmic absorption that results from using one
exponent for all three roles.
-/

noncomputable section

open MeasureTheory Metric Set Finset Real

attribute [local instance] Classical.propDecidable

namespace Kakeya.Assouad

/-- Robust-transversality angular loss
`q = (δ^aCore / 8)^(1/eta)`. -/
def hairbrushRobustQ (δ aCore eta : ℝ) : ℝ :=
  Real.rpow (Real.rpow δ aCore / 8) (1 / eta)

/-- Acute-angle analogue of the ordinary Wolff angle-band mass. -/
def hairbrushAcuteAngleBandMass {δ : ℝ}
    (F : Kakeya.TubeFamily δ) (Y : Kakeya.Shading F)
    (T : Kakeya.DeltaTube δ) (N : ℕ) (sigma : ℝ) : ENNReal :=
  volume <|
    Y.carrier T ∩ {x |
      ((F.filter fun U =>
        U ≠ T ∧ x ∈ U.carrier ∧
          sigma ≤ hairbrushAcuteAngle T U ∧
          hairbrushAcuteAngle T U ≤ 2 * sigma)).card ≥ N}

/-- The final square-root estimate required from a two-broad fiber. -/
def HairbrushFiberTarget {δ theta loss : ℝ}
    {F : Kakeya.TubeFamily δ} (Y : Kakeya.Shading F) : Prop :=
  Kakeya.realRpowENN δ (3 / 2 + loss) *
      ENNReal.ofReal (Real.sqrt theta) *
      ENNReal.rpow F.enncard (1 / 2) ≤
    volume Y.union

/--
Simultaneously regularized input for Raw A and Raw B.

The common spatial scale has the lower bound needed by the one-stem argument.
The construction theorem below is allowed to return the direct target instead
when the configuration is spatially concentrated and this core cannot be
produced.
-/
structure HairbrushMultiplicityDenseTwoEndsCoreData
    {δ : ℝ} {F : Kakeya.TubeFamily δ} (Y : Kakeya.Shading F)
    (eta theta aCore zetaEnds bTube : ℝ) where
  F3 : Kakeya.TubeFamily δ
  F3_subset : F3 ⊆ F
  F3_nonempty : F3.Nonempty
  Z : Kakeya.Shading F3
  Z_subset_Y : ∀ T ∈ F3, Z.carrier T ⊆ Y.carrier T
  mu : ℕ
  mu_pos : 0 < mu
  lambda3 : ENNReal
  lambda3_pos : 0 < lambda3
  lambda3_lower :
    Kakeya.realRpowENN δ (eta + aCore) ≤ lambda3
  alphaOld : ENNReal
  alphaOld_lower :
    Kakeya.realRpowENN δ aCore ≤ alphaOld
  alphaMu : ℝ
  alphaMu_lower : (1 / 4 : ℝ) ≤ alphaMu
  alphaTube : ENNReal
  alphaTube_pos : alphaTube ≠ 0
  alphaTube_ne_top : alphaTube ≠ ⊤
  alphaTube_lower :
    Kakeya.realRpowENN δ bTube ≤ alphaTube
  per_tube_density :
    ∀ T ∈ F3, lambda3 * T.volume ≤ volume (Z.carrier T)
  multiplicity_lower :
    ∀ x ∈ Z.union,
      Nat.ceil (alphaMu * (mu : ℝ)) ≤
        (F3.filter fun T => x ∈ Z.carrier T).card
  multiplicity_upper :
    ∀ x ∈ Z.union,
      (F3.filter fun T => x ∈ Z.carrier T).card ≤ 2 * mu
  multiplicity_retention :
    ∀ x ∈ Z.union,
      alphaOld *
          (↑((F.filter fun T => x ∈ Y.carrier T).card) : ENNReal) ≤
        (↑((F3.filter fun T => x ∈ Z.carrier T).card) : ENNReal)
  tube_mass_retention :
    ∀ T ∈ F3,
      alphaTube * volume (Y.carrier T) ≤ volume (Z.carrier T)
  card_retention :
    alphaOld * F.enncard ≤ F3.enncard
  r0 : ℝ
  delta_le_r0 : δ ≤ r0
  r0_le_one : r0 ≤ 1
  robust_scale_le_r0 :
    hairbrushRobustQ δ aCore eta * theta / 4 ≤ r0
  twoEndsC : ℝ
  twoEndsC_pos : 0 < twoEndsC
  twoEndsC_upper : twoEndsC ≤ 100
  two_ends :
    ∀ T ∈ F3, ∀ x : Point3,
      Metric.infDist x (Kakeya.unitSegment T.base T.direction) ≤ δ →
        ∀ r : ℝ, δ ≤ r → r ≤ r0 →
          volume (Z.carrier T ∩ Metric.ball x r) ≤
            ENNReal.ofReal twoEndsC * alphaTube⁻¹ *
              ENNReal.ofReal (Real.rpow (r / r0) zetaEnds) *
                volume (Z.carrier T)

/--
Generic output of Wolff's spatial two-ends regularization on an already
multiplicity-regularized shading.
-/
structure HairbrushSpatialTwoEndsRefinementData
    {δ : ℝ} {F : Kakeya.TubeFamily δ} (Y : Kakeya.Shading F)
    (massLoss scaleLoss zetaEnds : ℝ) where
  shading : Kakeya.Shading F
  r0 : ℝ
  delta_le_r0 : δ ≤ r0
  r0_le_one : r0 ≤ 1
  scale_lower : Kakeya.realRpowENN δ scaleLoss ≤ ENNReal.ofReal r0
  shading_subset :
    ∀ T ∈ F, shading.carrier T ⊆ Y.carrier T
  tube_mass_retention :
    ∀ T ∈ F,
      Kakeya.realRpowENN δ massLoss * volume (Y.carrier T) ≤
        volume (shading.carrier T)
  twoEndsC : ℝ
  twoEndsC_pos : 0 < twoEndsC
  twoEndsC_upper : twoEndsC ≤ 100
  two_ends :
    ∀ T ∈ F, ∀ x : Point3,
      Metric.infDist x (Kakeya.unitSegment T.base T.direction) ≤ δ →
        ∀ r : ℝ, δ ≤ r → r ≤ r0 →
          volume (shading.carrier T ∩ Metric.ball x r) ≤
            ENNReal.ofReal twoEndsC *
              Kakeya.realRpowENN δ (-massLoss) *
              ENNReal.ofReal (Real.rpow (r / r0) zetaEnds) *
                volume (shading.carrier T)

/--
Wolff's spatial two-ends reduction after multiplicity regularization.

The statement selects one common spatial scale and retains a prescribed
polynomial fraction of every tube's shading.  The two strict exponent
inequalities are the one-dimensional homogeneous-piece budgets: one controls
retained mass and the other controls the lower bound for the selected scale.
Multiplicity pruning is deliberately left to the subsequent core assembly.
-/
def HairbrushSpatialTwoEndsReductionStatement : Prop :=
  ∀ inputEta massLoss scaleLoss zetaEnds : ℝ,
    0 < inputEta →
      0 < massLoss →
        0 < scaleLoss →
          0 < zetaEnds → zetaEnds < 1 →
            inputEta * zetaEnds / (1 - zetaEnds) < massLoss →
              inputEta / (1 - zetaEnds) < scaleLoss →
                ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
                  ∀ δ : ℝ, 0 < δ → δ ≤ delta₀ →
                    ∀ (F : Kakeya.TubeFamily δ) (Y : Kakeya.Shading F),
                      F.Nonempty →
                        HairbrushPerTubeDense Y
                          (Kakeya.realRpowENN δ inputEta) →
                          Nonempty
                            (HairbrushSpatialTwoEndsRefinementData
                              Y massLoss scaleLoss zetaEnds)

/-- Output of the acute robust-transversality leaf. -/
structure HairbrushAcuteRobustTransverseData
    {δ : ℝ} {F : Kakeya.TubeFamily δ} {Y : Kakeya.Shading F}
    {eta theta aCore zetaEnds bTube : ℝ}
    (core :
      HairbrushMultiplicityDenseTwoEndsCoreData
        Y eta theta aCore zetaEnds bTube) where
  sigma : ℝ
  delta_le_sigma : δ ≤ sigma
  robust_scale_le_sigma :
    hairbrushRobustQ δ aCore eta * theta / 4 ≤ sigma
  sigma_le_one : sigma ≤ 1
  stem : Kakeya.DeltaTube δ
  stem_mem : stem ∈ core.F3
  bandMultiplicity : ℕ
  bandMultiplicity_pos : 0 < bandMultiplicity
  bandMultiplicity_lower :
    ENNReal.ofReal core.alphaMu * (core.mu : ENNReal) /
        ENNReal.ofReal (Real.log (1 / δ) ^ 2) ≤
      (bandMultiplicity : ENNReal)
  lossFactor : ℝ
  lossFactor_pos : 0 < lossFactor
  one_le_lossFactor : 1 ≤ lossFactor
  lossFactor_upper :
    ENNReal.ofReal lossFactor ≤
      ENNReal.ofReal (1000 * Real.log (1 / δ) ^ 2)
  stem_mass :
    (core.lambda3 / ENNReal.ofReal lossFactor) * stem.volume ≤
      hairbrushAcuteAngleBandMass
        core.F3 core.Z stem bandMultiplicity sigma

/-- Leaf 2: acute-angle robust transversality on a supplied core. -/
def HairbrushAcuteRobustTransversalityStatement : Prop :=
  ∀ (δ theta eta aCore zetaEnds bTube : ℝ),
    0 < δ → δ ≤ 1 / 1000 →
      δ ≤ theta → theta ≤ 1 →
        0 < eta → 0 < aCore → 0 < zetaEnds → 0 < bTube →
          ∀ (F : Kakeya.TubeFamily δ) (Y : Kakeya.Shading F),
            HairbrushAngleSeparated F →
              HairbrushAngularlyConfined F theta →
                IsTwoBroadAtScale Y theta eta →
                  ∀ core :
                    HairbrushMultiplicityDenseTwoEndsCoreData
                      Y eta theta aCore zetaEnds bTube,
                    2 ≤ Nat.ceil (core.alphaMu * (core.mu : ℝ)) →
                      Nonempty (HairbrushAcuteRobustTransverseData core)

/--
The radius at which the fixed-stem Raw-B argument removes the spatially
concentrated part of each hair.
-/
def hairbrushRawBEffectiveRadius {δ : ℝ}
    {F : Kakeya.TubeFamily δ} {Y : Kakeya.Shading F}
    {eta theta aCore zetaEnds bTube : ℝ}
    (core :
      HairbrushMultiplicityDenseTwoEndsCoreData
        Y eta theta aCore zetaEnds bTube)
    (transverse : HairbrushAcuteRobustTransverseData core)
    (kappa : ℝ) : ℝ :=
  δ ^ kappa * min core.r0 transverse.sigma / 8

/--
A ball radius that contains the part of one angle-band hair lying inside the
effective cylinder around the stem.  The fixed factor absorbs the two tube
radii and the axial length `O(rEff / sigma)`.
-/
def hairbrushRawBNearRadius {δ : ℝ}
    {F : Kakeya.TubeFamily δ} {Y : Kakeya.Shading F}
    {eta theta aCore zetaEnds bTube : ℝ}
    (core :
      HairbrushMultiplicityDenseTwoEndsCoreData
        Y eta theta aCore zetaEnds bTube)
    (transverse : HairbrushAcuteRobustTransverseData core)
    (kappa : ℝ) : ℝ :=
  8 *
    (hairbrushRawBEffectiveRadius core transverse kappa /
      transverse.sigma + δ)

/--
The exact spatial localization needed by the one-stem Wolff argument.

Every hair in the selected acute angle band that intersects the stem retains
at least one quarter of its shading outside the effective-radius cylinder
around the stem axis.  A ball two-ends estimate does not imply this statement
without an additional comparison between the axial intersection length and
the available two-ends scale.
-/
def HairbrushFarMassAtEffectiveRadius
    {δ : ℝ} {F : Kakeya.TubeFamily δ} {Y : Kakeya.Shading F}
    {eta theta aCore zetaEnds bTube : ℝ}
    (core :
      HairbrushMultiplicityDenseTwoEndsCoreData
        Y eta theta aCore zetaEnds bTube)
    (transverse : HairbrushAcuteRobustTransverseData core)
    (kappa : ℝ) : Prop :=
  ∀ U ∈ core.F3,
    U ≠ transverse.stem →
    transverse.sigma ≤ hairbrushAcuteAngle transverse.stem U →
    hairbrushAcuteAngle transverse.stem U ≤ 2 * transverse.sigma →
    (transverse.stem.carrier ∩ U.carrier).Nonempty →
      (1 / 4 : ENNReal) * volume (core.Z.carrier U) ≤
        volume
          (core.Z.carrier U ∩
            {x |
              hairbrushRawBEffectiveRadius core transverse kappa ≤
                ‖Kakeya.Assouad.perpProj
                  transverse.stem.direction
                  (x - transverse.stem.base)‖})

/--
Leaf 3: orient one acute hairbrush and prove the Raw-B estimate.

The spatial far-mass conclusion is supplied explicitly.  The complementary
case in which the effective radius is below `δ`, or in which the producer
cannot obtain this localization, is a direct-estimate branch owned by the
final two-broad assembly.
-/
def HairbrushOrientedRawBStatement : Prop :=
  ∀ (δ theta eta aCore zetaEnds bTube kappa : ℝ),
    0 < δ → δ ≤ 1 / 1000 →
      0 < theta → theta ≤ 1 →
        0 < eta → 0 < aCore → 0 < zetaEnds →
          0 < bTube → 0 < kappa →
            ∀ (F : Kakeya.TubeFamily δ) (Y : Kakeya.Shading F),
              HairbrushAngleSeparated F →
                F.IsEssentiallyDistinct →
                  Kakeya.KatzTaoConvexWolffBound F
                    (Real.rpow δ (-eta)) →
                    ENNReal.ofReal (δ ^ 2) ≤
                      Kakeya.deltaTubeVolume δ →
                    ∀ core :
                      HairbrushMultiplicityDenseTwoEndsCoreData
                        Y eta theta aCore zetaEnds bTube,
                    ∀ transverse :
                      HairbrushAcuteRobustTransverseData core,
                      δ ≤
                          hairbrushRawBEffectiveRadius
                            core transverse kappa →
                      HairbrushFarMassAtEffectiveRadius
                        core transverse kappa →
                      core.lambda3 ^ 3 *
                          (transverse.bandMultiplicity : ENNReal) *
                          ENNReal.ofReal δ *
                          ENNReal.ofReal
                            (hairbrushRobustQ δ aCore eta * theta) *
                          ENNReal.ofReal (δ ^ kappa) /
                          (ENNReal.ofReal 32 *
                            ENNReal.ofReal
                              (transverse.lossFactor ^ 2) *
                            (1 +
                              ENNReal.ofReal
                                (2000 * (3 : ℝ) *
                                  Real.rpow δ (-eta) * 32 * Real.pi) *
                                ENNReal.ofReal (Real.log (1 / δ))) *
                            ENNReal.ofReal
                              ((2 * Real.pi + 1) * 200 * 800)) ≤
                        volume Y.union

/--
A core is ready for the final Raw-B assembly.

This packages every condition that the downstream proof actually needs:
the acute-transversality leaf is applicable, the effective two-ends radius is
at least the tube thickness, the near-cylinder loss is absorbable, and the
resulting Raw-B lower bound closes the requested fiber estimate.  In
particular, a vacuous choice such as `r0 = δ` is not accepted merely because
the two-ends predicate then has only one radius to check.
-/
def HairbrushRawBReady {δ theta eta aCore zetaEnds bTube loss : ℝ}
    {F : Kakeya.TubeFamily δ} (Y : Kakeya.Shading F)
    (core :
      HairbrushMultiplicityDenseTwoEndsCoreData
        Y eta theta aCore zetaEnds bTube)
    (kappa : ℝ) : Prop :=
  0 < kappa ∧
  bTube < kappa * zetaEnds ∧
  2 ≤ Nat.ceil (core.alphaMu * (core.mu : ℝ)) ∧
  ∀ transverse : HairbrushAcuteRobustTransverseData core,
    HairbrushFiberTarget (theta := theta) (loss := loss) Y ∨
      (δ ≤ hairbrushRawBEffectiveRadius core transverse kappa ∧
        HairbrushFarMassAtEffectiveRadius core transverse kappa ∧
        (core.lambda3 ^ 3 *
              (transverse.bandMultiplicity : ENNReal) *
              ENNReal.ofReal δ *
              ENNReal.ofReal
                (hairbrushRobustQ δ aCore eta * theta) *
              ENNReal.ofReal (δ ^ kappa) /
              (ENNReal.ofReal 32 *
                ENNReal.ofReal (transverse.lossFactor ^ 2) *
                (1 +
                  ENNReal.ofReal
                    (2000 * (3 : ℝ) *
                      Real.rpow δ (-eta) * 32 * Real.pi) *
                    ENNReal.ofReal (Real.log (1 / δ))) *
                ENNReal.ofReal
                  ((2 * Real.pi + 1) * 200 * 800)) ≤
            volume Y.union →
          HairbrushFiberTarget (theta := theta) (loss := loss) Y))

/--
The exact numerical input for Wolff's far-cylinder localization.

For one selected transverse stem, the effective radius is at least the tube
thickness, the containing-ball radius lies in the available two-ends range,
and the two-ends coefficient at that radius is at most one quarter.  This
predicate contains no final fiber-target algebra.
-/
def HairbrushFarMassNumericalReady
    {δ theta eta aCore zetaEnds bTube : ℝ}
    {F : Kakeya.TubeFamily δ} {Y : Kakeya.Shading F}
    (core :
      HairbrushMultiplicityDenseTwoEndsCoreData
        Y eta theta aCore zetaEnds bTube)
    (transverse : HairbrushAcuteRobustTransverseData core)
    (kappa : ℝ) : Prop :=
  δ ≤ hairbrushRawBEffectiveRadius core transverse kappa ∧
    hairbrushRawBNearRadius core transverse kappa ≤ core.r0 ∧
    ENNReal.ofReal core.twoEndsC * core.alphaTube⁻¹ *
        ENNReal.ofReal
          (Real.rpow
            (hairbrushRawBNearRadius core transverse kappa / core.r0)
            zetaEnds) ≤
      1 / 4

/--
The numerical part of final Raw-B readiness, separated from the far-mass
geometry.

For every transverse stem it contains the independent numerical input for
far-cylinder localization together with the final algebraic implication from
the validated Raw-B lower bound to the requested fiber target.  It does not
assert the far-cylinder mass conclusion itself.
-/
def HairbrushRawBNumericalReady
    {δ theta eta aCore zetaEnds bTube loss : ℝ}
    {F : Kakeya.TubeFamily δ} (Y : Kakeya.Shading F)
    (core :
      HairbrushMultiplicityDenseTwoEndsCoreData
        Y eta theta aCore zetaEnds bTube)
    (kappa : ℝ) : Prop :=
  0 < kappa ∧
  bTube < kappa * zetaEnds ∧
  2 ≤ Nat.ceil (core.alphaMu * (core.mu : ℝ)) ∧
  ∀ transverse : HairbrushAcuteRobustTransverseData core,
    HairbrushFarMassNumericalReady core transverse kappa ∧
      (core.lambda3 ^ 3 *
            (transverse.bandMultiplicity : ENNReal) *
            ENNReal.ofReal δ *
            ENNReal.ofReal
              (hairbrushRobustQ δ aCore eta * theta) *
            ENNReal.ofReal (δ ^ kappa) /
            (ENNReal.ofReal 32 *
              ENNReal.ofReal (transverse.lossFactor ^ 2) *
              (1 +
                ENNReal.ofReal
                  (2000 * (3 : ℝ) *
                    Real.rpow δ (-eta) * 32 * Real.pi) *
                  ENNReal.ofReal (Real.log (1 / δ))) *
              ENNReal.ofReal
                ((2 * Real.pi + 1) * 200 * 800)) ≤
          volume Y.union →
        HairbrushFiberTarget (theta := theta) (loss := loss) Y)

/--
Leaf 1: Wolff spatial two-ends and multiplicity regularization.

The requested loss is known before the producer chooses `eta` and all other
internal exponents.  This matches the quantifier order in Wang--Zahl Appendix
B and Wolff's small-loss argument.  The producer either closes the fiber
target directly or returns a two-ends core with the numerical Raw-B budget.
-/
def HairbrushMultiplicityDenseTwoEndsCoreStatement : Prop :=
  ∀ loss : ℝ, 0 < loss →
    ∃ eta aCore zetaEnds bTube kappa delta₀ : ℝ,
        0 < eta ∧
        eta ≤ loss / 2 ∧
        0 < aCore ∧
        0 < zetaEnds ∧ zetaEnds ≤ 1 ∧
        0 < bTube ∧
        0 < kappa ∧
        bTube < kappa * zetaEnds ∧
        0 < delta₀ ∧ delta₀ ≤ 1 / 1000 ∧
          ∀ (δ theta : ℝ),
            0 < δ → δ ≤ delta₀ →
              δ ≤ theta → theta ≤ 1 →
            ∀ (F : Kakeya.TubeFamily δ),
              F.Nonempty →
                F.IsInUnitBall →
                  F.IsEssentiallyDistinct →
                    HairbrushAngleSeparated F →
                      HairbrushAngularlyConfined F theta →
                        ∀ Y : Kakeya.Shading F,
                          HairbrushPerTubeDense Y
                              (Kakeya.realRpowENN δ eta) →
                            Kakeya.KatzTaoConvexWolffBound F
                              (Real.rpow δ (-eta)) →
                                IsTwoBroadAtScale Y theta eta →
                                  HairbrushFiberTarget
                                      (theta := theta) (loss := loss) Y ∨
                                    ∃ core :
                                      HairbrushMultiplicityDenseTwoEndsCoreData
                                        Y eta theta aCore zetaEnds bTube,
                                      HairbrushRawBNumericalReady
                                        (loss := loss) Y core kappa

/--
The recovered Wolff multiplicity pruning and parameter algebra package a
numerically ready core once the generic spatial two-ends leaf is available.
-/
def HairbrushMultiplicityDenseTwoEndsCoreAssemblyStatement : Prop :=
  HairbrushSpatialTwoEndsReductionStatement →
    HairbrushMultiplicityDenseTwoEndsCoreStatement

/--
Leaf 2b: Wolff's far-cylinder localization, equation (19) in the proof of
Lemma 3.4.

For every transverse stem satisfying the three local numerical certificates,
every selected hair retains the required mass outside the effective cylinder.
This geometric leaf is independent of the final fiber target and its loss
parameter.
-/
def HairbrushFarMassFromTwoEndsStatement : Prop :=
  ∀ (δ theta eta aCore zetaEnds bTube kappa : ℝ),
    0 < δ →
      ∀ (F : Kakeya.TubeFamily δ) (Y : Kakeya.Shading F),
        ∀ core :
          HairbrushMultiplicityDenseTwoEndsCoreData
            Y eta theta aCore zetaEnds bTube,
          ∀ transverse : HairbrushAcuteRobustTransverseData core,
            HairbrushFarMassNumericalReady core transverse kappa →
              HairbrushFarMassAtEffectiveRadius core transverse kappa

/--
The four frozen producer leaves imply the original-coordinate two-broad
fiber estimate.

This is only an assembly boundary. In the non-direct branch, Leaf 1 supplies
a numerically ready core, Leaf 2 supplies one transverse stem, Leaf 2b supplies
Wolff's far-cylinder mass, and Leaf 3 supplies the Raw-B lower bound.
-/
def HairbrushTwoBroadFiberAssemblyStatement : Prop :=
  HairbrushMultiplicityDenseTwoEndsCoreStatement →
    HairbrushAcuteRobustTransversalityStatement →
      HairbrushFarMassFromTwoEndsStatement →
        HairbrushOrientedRawBStatement →
          HairbrushTwoBroadFiberEstimateStatement

end Kakeya.Assouad
