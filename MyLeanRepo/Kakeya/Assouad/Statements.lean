import MyLeanRepo.Kakeya.Assouad.Definitions
import MyLeanRepo.Kakeya.Assouad.CriticalInputs
import MyLeanRepo.Kakeya.Assouad.WZ1.Statements
import MyLeanRepo.Kakeya.Assouad.AnisotropicRescaling.TubeParameters
import MyLeanRepo.Kakeya.Assouad.CinematicFamilyFromSlope.Construction
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.TubeParameterPrism
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.TubeParameters

/-!
# Standalone statements from the proof of WZ2 Theorem 5.2

The corresponding one-sorry targets live in `Assouad/Targets`.  These
statements deliberately expose the paper's intermediate interfaces rather
than asking SeedProver to prove the complete theorem in one run.
-/

noncomputable section

open MeasureTheory Set

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

/--
The arithmetic crossing step in the proof of the spacing lemma: a scale
profile whose weighted average is near `s` must cross `s - ε` early.
-/
def ScaleProfileCrossingStatement : Prop :=
  ∀ N : ℕ, 0 < N →
    ∀ n s epsilon : ℝ,
      0 < n → 0 < epsilon → epsilon ≤ 1 / 2 → epsilon ≤ s → s ≤ n →
      ∀ a : Fin (N + 1) → ℝ, ∀ t : Fin N → ℝ,
        a 0 = 0 →
        a (Fin.last N) = 1 →
        (∀ i : Fin N, a i.castSucc < a i.succ) →
        (∀ i : Fin N, 0 ≤ t i ∧ t i ≤ n) →
        s - epsilon ^ 2 ≤
          ∑ i : Fin N, t i * (a i.succ - a i.castSucc) →
        ∃ i : Fin N,
          s - epsilon ≤ t i ∧
            a i.castSucc ≤ 1 - epsilon / (2 * n)

/--
Finite-set version of the Frostman-to-Katz--Tao extraction in Section 7.
The explicit factor absorbs the logarithmic and dimensional losses.
-/
def FrostmanToKatzTaoStatement : Prop :=
  ∀ n : ℕ, ∀ s : ℝ, 0 < s → s ≤ n →
    ∃ L : ENNReal, 1 ≤ L ∧ L ≠ ⊤ ∧
      ∀ delta : ℝ, ∀ C : ENNReal,
        0 < delta → delta < 1 →
        1 ≤ C → C ≠ ⊤ →
        ∀ A : DiscreteSet n,
          A.Nonempty →
          A.IsInUnitBall →
          A.IsDeltaSeparated delta →
          A.IsFrostman delta s C →
          Kakeya.realRpowENN delta (-s) ≤ A.enncard →
          ∃ A' : DiscreteSet n,
            A'.Nonempty ∧
              A' ⊆ A ∧
              A'.IsKatzTao delta s 100 ∧
              Kakeya.realRpowENN delta (-s) ≤
                L * ENNReal.ofReal (1 + Real.log delta⁻¹) *
                  C * A'.enncard

/-- Exact coordinate identity for the twisted image of a parameter line. -/
def TwistedLineIdentityStatement : Prop :=
  ∀ f : SlopeFunction, ∀ a b c d t : ℝ,
    twistedProjection f (parameterLine a b c d t) =
      twistedCurve f a b c d t

/--
Translation of a parameter block changes every horizontal cinematic slice by
an explicit scalar translation.  This is the identity used in the replication
argument of Section 7.
-/
def CinematicParameterTranslationStatement : Prop :=
  ∀ f : SlopeFunction, ∀ a b d a₀ b₀ d₀ t : ℝ,
    cinematicEval f (a + a₀) (b + b₀) (d + d₀) t =
      cinematicEval f a b d t +
        cinematicEval f a₀ b₀ d₀ t

/--
Failure of the sticky estimate produces coordinate-normalized extremal
configurations with the global and local `C²` grain structure inherited from
WZ1.
-/
def WolffVolumeFloorInput : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon →
    ∃ eta delta₀ : ℝ,
      0 < eta ∧ 0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
        ∀ F : Kakeya.Streamlined.TubeFamily delta,
          F.Nonempty →
          F.IsInUnitBall →
          F.IsEssentiallyDistinct →
          ∀ U : Kakeya.Streamlined.UniformTubeStructure F,
            U.uniformity ≤ Kakeya.realRpowENN delta (-eta) →
            U.IsFrostmanAtEveryScale
              (Kakeya.realRpowENN delta (-eta)) →
            ∀ Y : Kakeya.Streamlined.TubeShading F,
              Y.IsLambdaDense (Kakeya.realRpowENN delta eta) →
              Kakeya.realRpowENN delta (1 / 2 + epsilon) ≤
                MeasureTheory.volume Y.union

/--
The WZ2 extremal-exponent step.  A single non-admissible exponent below one
bounds the critical supremum away from one; failure of sticky supplies
positivity and arbitrarily small near-minimizers.
-/
def ExtremalCounterexamplesFromFailureStatement : Prop :=
  SubunitAdmissibleCeilingInput →
    ¬Kakeya.Streamlined.StickyInput →
      ∃ sigma : ℝ, 0 < sigma ∧ sigma < 1 ∧
        HasExtremalCounterexampleSequence sigma ∧
          HasCriticalVolumeFloor sigma

/--
After extremal counterexamples have been extracted, the frozen WZ1/CV/OSW
input returns a coordinate-normalized family with global and local `C²`
grain structure.
-/
def C2GrainsFromFailureStatement : Prop :=
  ¬Kakeya.Streamlined.StickyInput →
    ∃ sigma : ℝ, 0 < sigma ∧ sigma < 1 ∧
      HasCriticalVolumeFloor sigma ∧
        ∀ epsilon delta₀ : ℝ,
          0 < epsilon → 0 < delta₀ →
          ∃ delta : ℝ, 0 < delta ∧ delta ≤ delta₀ ∧
            ∃ F : Kakeya.Streamlined.TubeFamily delta,
            ∃ U : Kakeya.Streamlined.UniformTubeStructure F,
              ∃ Y : Kakeya.Streamlined.TubeShading F,
                ∃ C : ENNReal,
                  IsExtremalPair sigma epsilon F U Y ∧
                    HasExtremalCardinalityUpper F epsilon ∧
                    IsInVerticalChart F ∧
                    1 ≤ C ∧ C ≠ ⊤ ∧
                    C ≤ Kakeya.realRpowENN delta (-epsilon) ∧
                    Nonempty (C2GrainStructure Y sigma C)

/--
The elementary tube-volume package needed when converting the every-scale
Frostman condition into tube counts: equal volume at a fixed scale, positive
finite canonical volume, and quadratic scaling up to an absolute constant.
-/
def TubeVolumeScalingStatement : Prop :=
  (∀ delta : ℝ, ∀ T : Kakeya.DeltaTube delta,
    T.volume = Kakeya.deltaTubeVolume delta) ∧
  (∀ delta : ℝ, 0 < delta → delta ≤ 1 →
    0 < Kakeya.deltaTubeVolume delta ∧
      Kakeya.deltaTubeVolume delta ≠ ⊤) ∧
  (∀ rho : ℝ, 0 < rho → rho ≤ 1 →
    ∀ T : Kakeya.DeltaTube rho,
      T.volume ≤
        24 * Kakeya.realRpowENN rho 2 * Kakeya.deltaTubeVolume 1)

/--
The cardinality lower bound implicit in an extremal family.

Every-scale Frostman control first gives total tube mass at least
`delta^epsilon`.  The quadratic tube-volume upper bound then forces at least
`delta^(-2 + 2 epsilon)` indexed tubes after one fixed constant is absorbed
at sufficiently small scale.  No cardinality upper bound is asserted here.
-/
def ExtremalFamilyCardinalityLowerStatement : Prop :=
  TubeVolumeScalingStatement →
    ∀ epsilon : ℝ, 0 < epsilon →
      ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
        ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
          ∀ sigma : ℝ,
            ∀ F : Kakeya.Streamlined.TubeFamily delta,
              ∀ U : Kakeya.Streamlined.UniformTubeStructure F,
                ∀ Y : Kakeya.Streamlined.TubeShading F,
                  IsExtremalPair sigma epsilon F U Y →
                    Kakeya.realRpowENN delta (-2 + 2 * epsilon) ≤
                      F.enncard

/--
Select one refined configuration and one well-populated slab for the
large-slope argument.

The source loss is chosen only after the requested output loss is known.  This
quantifier order leaves room for the polynomial losses in the common
refinement that supplies both slab mass and slab covering.  Returning a
subshading is essential: arbitrary measurable shadings may contain
measure-zero outliers that do not affect extremality or the slice-wise AD
bounds but destroy a covering assertion for the original support.
-/
def LargeSlopeIntervalSelectionStatement : Prop :=
  TubeVolumeScalingStatement →
    ∀ epsilon sigma eta : ℝ,
      0 < epsilon → epsilon ≤ 1 / 2 →
      0 < sigma → sigma < 1 →
      0 < eta →
      HasCriticalVolumeFloor sigma →
      ∀ outputLoss : ℝ,
        0 < outputLoss → outputLoss ≤ eta / 1000 →
        ∃ sourceLoss delta₀ : ℝ,
          0 < sourceLoss ∧ sourceLoss ≤ outputLoss ∧
          0 < delta₀ ∧ delta₀ ≤ 1 ∧
          ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
            ∀ F : Kakeya.Streamlined.TubeFamily delta,
              ∀ U : Kakeya.Streamlined.UniformTubeStructure F,
                ∀ Y : Kakeya.Streamlined.TubeShading F,
                  IsExtremalPair sigma sourceLoss F U Y →
                  HasExtremalCardinalityUpper F sourceLoss →
                  IsInVerticalChart F →
                  ∀ C : ENNReal, 1 ≤ C → C ≠ ⊤ →
                    C ≤ Kakeya.realRpowENN delta (-sourceLoss) →
                    ∀ G : C2GrainStructure Y sigma C,
                      ∃ Z : Kakeya.Streamlined.TubeShading F,
                        ∃ hZY : IsSubshading Z Y,
                          IsExtremalPair sigma outputLoss F U Z ∧
                          ∃ a b : ℝ,
                            -1 ≤ a ∧ a < b ∧ b ≤ 1 ∧
                            Kakeya.realRpowENN delta (1 / 2 : ℝ) ≤
                              ENNReal.ofReal (b - a) ∧
                            Kakeya.realRpowENN delta (2 * epsilon) ≤
                              ENNReal.ofReal (b - a) ∧
                            b - a ≤ Real.rpow delta epsilon ∧
                            Kakeya.realRpowENN delta (eta / 100) *
                                ENNReal.ofReal (b - a) ≤
                              shadedMassInSlab Z a b ∧
                            CanCoverByBalls
                              (Z.union ∩ horizontalSlab a b) (b - a)
                              (Kakeya.realRpowENN delta (-(eta / 100)) *
                                Kakeya.realRpowENN
                                  (b - a) (-2 + sigma))

/--
Discard tubes whose retained shaded mass is too small.  This is the
per-tube fullness input used before the prism-incidence count in paper
Section 6, Step 4.
-/
def PerTubeMassPruningStatement : Prop :=
  ∀ delta eta : ℝ, 0 < delta → delta ≤ 1 → 0 < eta →
    ∀ F : Kakeya.Streamlined.TubeFamily delta,
      ∀ Y : Kakeya.Streamlined.TubeShading F,
        Y.IsLambdaDense (Kakeya.realRpowENN delta eta) →
          ∃ Z : Kakeya.Streamlined.TubeShading F,
            IsSubshading Z Y ∧
              (1 / 2 : ENNReal) * Y.mass ≤ Z.mass ∧
              (1 / 2 : ENNReal) * Kakeya.realRpowENN delta eta *
                  F.toBodyFamily.mass ≤ Z.mass ∧
              HasPerTubeMass Z
                ((1 / 2 : ENNReal) *
                  Kakeya.realRpowENN delta eta *
                    Kakeya.deltaTubeVolume delta) ∧
              IsWholeTubeSubshading Z Y

/--
Prune by shaded mass inside one already-selected horizontal slab.  The exact
discarded-mass error is exposed instead of assuming a global cardinality
normalization; downstream Step 4 arithmetic chooses the threshold and absorbs
`threshold * #F`.
-/
def SlabPerTubeMassPruningStatement : Prop :=
  ∀ {delta : ℝ},
    ∀ F : Kakeya.Streamlined.TubeFamily delta,
      ∀ Y : Kakeya.Streamlined.TubeShading F,
        ∀ (a b : ℝ) (threshold : ENNReal),
          ∃ Z : Kakeya.Streamlined.TubeShading F,
            IsSubshading Z Y ∧
              shadedMassInSlab Y a b ≤
                shadedMassInSlab Z a b +
                  threshold * F.enncard ∧
              HasPerTubeMassInSlab Z a b threshold

/--
Geometric lower bound from WZ Lemma 30.  A positive-density subset of a
`δ`-tube segment of length `sqrt ρ` needs many `ρ`-balls after projection in a
direction with axial component `tau`.  The generous absolute constant absorbs
the two end caps and closed-ball conventions.
-/
def TubeSegmentProjectionCoveringLowerBoundStatement : Prop :=
  ∀ (delta rho lambda start : ℝ)
      (hdelta : 0 < delta) (hdelta_rho : delta ≤ rho)
      (hrho_one : rho ≤ 1)
      (hlambda : 0 < lambda) (hlambda_one : lambda ≤ 1),
    ∀ (base direction v : Point3),
      ‖direction‖ = 1 → ‖v‖ = 1 →
      Real.sqrt rho ≤ |inner ℝ direction v| →
      ∀ E : Set Point3,
        MeasurableSet E →
        E ⊆ tubeSegmentCarrier delta base direction start rho →
        ENNReal.ofReal
            (lambda * delta ^ 2 * Real.sqrt rho) ≤
          MeasureTheory.volume E →
          ENNReal.ofReal
              (lambda * |inner ℝ direction v| * Real.sqrt rho) ≤
            10000 * ENNReal.ofReal rho *
              (↑(Metric.externalCoveringNumber
                ⟨rho, hdelta.le.trans hdelta_rho⟩
                (scalarProjection v E)) : ENNReal)

/--
The local volume estimate behind the preceding covering lower bound.  One
radius-`rho` scalar-projection ball cuts a `δ`-tube segment in volume
`O(δ² rho / tau)`, where `tau` is the axial projection speed.
-/
def TubeSegmentProjectionFiberVolumeStatement : Prop :=
  ∀ (delta rho start c : ℝ)
      (hdelta : 0 < delta) (hdelta_rho : delta ≤ rho)
      (hrho_one : rho ≤ 1),
    ∀ (base direction v : Point3),
      ‖direction‖ = 1 → ‖v‖ = 1 →
      Real.sqrt rho ≤ |inner ℝ direction v| →
        MeasureTheory.volume
            ({p | p ∈ tubeSegmentCarrier delta base direction start rho ∧
              dist (inner ℝ p v) c ≤ rho}) ≤
          ENNReal.ofReal
            (1000 * delta ^ 2 * rho / |inner ℝ direction v|)

/--
Exact localization of the scalar projection of a thickened tube segment.
The axis contribution is centered at the segment midpoint, while the radial
error contributes the full `delta`.  This is the local interval used when the
AD upper bound in WZ Lemma 30 is applied to the entire projected segment.
-/
def TubeSegmentProjectionLocalizationStatement : Prop :=
  ∀ (delta rho start : ℝ), 0 ≤ delta → 0 ≤ rho →
    ∀ (base direction v : Point3), ‖v‖ = 1 →
      scalarProjection v
          (tubeSegmentCarrier delta base direction start rho) ⊆
        Metric.closedBall
          (inner ℝ
            (base +
              (start + Real.sqrt rho / 2) • direction) v)
          (delta +
            |inner ℝ direction v| * Real.sqrt rho / 2)

/--
The exact power comparison in WZ Lemma 30 after writing
`x = tau / sqrt rho`.  It combines the projected-cover lower bound with the
AD upper bound without hiding any exponent arithmetic.
-/
def ADCoveringComparisonStatement : Prop :=
  ∀ (delta epsilon alpha x : ℝ) (N : ENNReal),
    0 < delta → delta ≤ 1 →
    0 < epsilon → 0 < alpha → alpha < 1 → 0 ≤ x →
    Kakeya.realRpowENN delta epsilon * ENNReal.ofReal x ≤
        10000 * N →
    N ≤ Kakeya.realRpowENN delta (-epsilon) *
        Kakeya.realRpowENN x alpha →
      Kakeya.realRpowENN x (1 - alpha) ≤
        10000 * Kakeya.realRpowENN delta (-2 * epsilon)

/--
The same WZ Lemma 30 power comparison with an explicit absolute loss in the
AD covering upper bound.  This is needed because localization of the
thickened segment enlarges the natural projection interval by a factor at
most two.
-/
def ADCoveringComparisonWithConstantStatement : Prop :=
  ∀ (delta epsilon alpha x : ℝ) (N K : ENNReal),
    0 < delta → delta ≤ 1 →
    0 < epsilon → 0 < alpha → alpha < 1 → 0 ≤ x →
    1 ≤ K →
    Kakeya.realRpowENN delta epsilon * ENNReal.ofReal x ≤
        10000 * N →
    N ≤ K * Kakeya.realRpowENN delta (-epsilon) *
        Kakeya.realRpowENN x alpha →
      Kakeya.realRpowENN x (1 - alpha) ≤
        10000 * K *
          Kakeya.realRpowENN delta (-2 * epsilon)

/--
Paper-faithful WZ Lemma 30 direction bound in power form.  The small-scale
assumption `rho ≤ 1/4` ensures that the radius
`2 * |direction · v| * sqrt rho` is at most one, so the local `IsADSet1`
covering estimate is applied only in its frozen range.  Larger scales are
handled separately by constant absorption in Step 4.
-/
def TubeSegmentADDirectionPowerStatement : Prop :=
  TubeSegmentProjectionCoveringLowerBoundStatement →
    TubeSegmentProjectionLocalizationStatement →
      ADCoveringComparisonWithConstantStatement →
        ∀ (delta rho epsilon alpha start : ℝ),
          0 < delta → delta ≤ rho → rho ≤ 1 / 4 →
          0 < epsilon → 0 < alpha → alpha < 1 →
          ∀ (base direction v : Point3),
            ‖direction‖ = 1 → ‖v‖ = 1 →
            ∀ E : Set Point3,
              MeasurableSet E →
              E ⊆ tubeSegmentCarrier delta base direction start rho →
              ENNReal.ofReal
                  (Real.rpow delta epsilon * delta ^ 2 *
                    Real.sqrt rho) ≤
                MeasureTheory.volume E →
              IsADSet1 (scalarProjection v E) rho alpha
                  (Kakeya.realRpowENN delta (-epsilon)) →
                Kakeya.realRpowENN
                    (|inner ℝ direction v| / Real.sqrt rho)
                    (1 - alpha) ≤
                  20000 *
                    Kakeya.realRpowENN delta (-2 * epsilon)

/--
The actual WZ Lemma 30 direction-width bound used by Step 4.  It specializes
the AD exponent to `1 - sigma`, applies the power-form lemma, absorbs the
fixed constant at sufficiently small `delta`, and takes the positive
`sigma`-th root.
-/
def TubeSegmentADDirectionBoundStatement : Prop :=
  TubeSegmentADDirectionPowerStatement →
    ∀ sigma eta : ℝ,
      0 < sigma → sigma < 1 → 0 < eta →
        ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
          ∀ delta rho start : ℝ,
            0 < delta → delta ≤ delta₀ →
            delta ≤ rho → rho ≤ 1 / 4 →
            ∀ (base direction v : Point3),
              ‖direction‖ = 1 → ‖v‖ = 1 →
              ∀ E : Set Point3,
                MeasurableSet E →
                E ⊆ tubeSegmentCarrier delta base direction start rho →
                ENNReal.ofReal
                    (Real.rpow delta eta * delta ^ 2 *
                      Real.sqrt rho) ≤
                  MeasureTheory.volume E →
                IsADSet1 (scalarProjection v E) rho (1 - sigma)
                    (Kakeya.realRpowENN delta (-eta)) →
                  ENNReal.ofReal
                      (|inner ℝ direction v| / Real.sqrt rho) ≤
                    Kakeya.realRpowENN delta (-(3 * eta / sigma))

/--
Finite mass pigeonholing for paper Section 6, Step 4.  If the total retained
mass is covered by finitely many tube--prism pieces and every piece has mass at
most `cap`, then one prism meets proportionally many active tubes.
-/
def PrismMassPigeonholeStatement : Prop :=
  ∀ {ι κ : Type} [DecidableEq ι] [DecidableEq κ],
    ∀ (tubes : Finset ι) (prisms : Finset κ),
      prisms.Nonempty →
      ∀ (pieceMass : ι → κ → ENNReal) (total cap : ENNReal),
        total ≤ ∑ i ∈ tubes, ∑ j ∈ prisms, pieceMass i j →
        (∀ i ∈ tubes, ∀ j ∈ prisms, pieceMass i j ≤ cap) →
          ∃ j ∈ prisms,
            total ≤
              (prisms.card : ENNReal) * cap *
                ((tubes.filter fun i => pieceMass i j ≠ 0).card : ENNReal)

/--
One-tube geometric containment used after WZ Lemma 30.  If a unit-ball tube
meets the chosen prism and its axis is nearly tangent to the prism plane, its
whole carrier lies in an explicitly bounded convex slab.
-/
def TubeContainedInOrientedSlabStatement : Prop :=
  ∀ (delta tau : ℝ), 0 ≤ delta → 0 ≤ tau →
    ∀ T : Kakeya.DeltaTube delta,
      T.IsInUnitBall →
      ∀ (normal q : Point3), ‖normal‖ = 1 →
        q ∈ T.carrier →
        |inner ℝ T.direction normal| ≤ tau →
          T.carrier ⊆
              orientedUnitSlab q normal (tau + 2 * delta) ∧
            Convex ℝ (orientedUnitSlab q normal (tau + 2 * delta))

/--
Uniform volume bound for the bounded oriented slab.  The constant eight is a
rational upper bound for twice the maximal unit-ball cross-sectional area.
-/
def OrientedUnitSlabVolumeStatement : Prop :=
  ∀ (center normal : Point3) (width : ℝ),
    ‖normal‖ = 1 → 0 ≤ width →
      MeasureTheory.volume (orientedUnitSlab center normal width) ≤
        ENNReal.ofReal (8 * width)

/--
Stable output of Steps 1--3 of the large-slope lemma.

The returned package retains the Proposition 5 refinement, inherited C²
structure, selected slab, mass, and cover.  The multiplicity and `F₂`/prism
refinements used under the small-slope contradiction are intentionally
produced later by `LargeSlopeStep4WitnessStatement`.
-/
def LargeSlopeRefinementStatement : Prop :=
  ∀ epsilon sigma eta : ℝ,
    0 < epsilon → epsilon ≤ 1 / 2 →
    0 < sigma → sigma < 1 →
    0 < eta →
    HasCriticalVolumeFloor sigma →
      ∃ inputLoss delta₀ : ℝ,
        0 < inputLoss ∧ inputLoss ≤ eta / 1000 ∧
        0 < delta₀ ∧ delta₀ ≤ 1 ∧
        ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
          ∀ F : Kakeya.Streamlined.TubeFamily delta,
            ∀ U : Kakeya.Streamlined.UniformTubeStructure F,
              ∀ Y : Kakeya.Streamlined.TubeShading F,
                IsExtremalPair sigma inputLoss F U Y →
                HasExtremalCardinalityUpper F inputLoss →
                IsInVerticalChart F →
                ∀ C : ENNReal, 1 ≤ C → C ≠ ⊤ →
                  C ≤ Kakeya.realRpowENN delta (-inputLoss) →
                  ∀ G : C2GrainStructure Y sigma C,
                    ∃ a b : ℝ,
                      Kakeya.realRpowENN delta (2 * epsilon) ≤
                          ENNReal.ofReal (b - a) ∧
                        b - a ≤ Real.rpow delta epsilon ∧
                        Nonempty
                          (LargeSlopeRefinementData
                            U Y sigma eta C G a b)

/--
Derive the complete Lemma 32 large-slope input from the fixed-scale spatial
cover output of Proposition 5.
-/
def LargeSlopeRefinementFromSpatialCoverStatement : Prop :=
  WZ1Proposition5SpatialCoverConclusion →
    LargeSlopeRefinementStatement

/--
Paper Section 6, Steps 1--3 under the small-slope contradiction hypothesis.

The witness is deliberately geometric rather than a prepackaged count:
it exports the refined `F₂` shading, slab-local per-tube fullness, a finite
vertical-prism decomposition with at most three active prisms per tube,
two-sided tube--prism piece masses, exact tube segments, local AD data, and
the common transverse strip attached to each prism.
-/
def LargeSlopeStep4WitnessStatement : Prop :=
  ∀ epsilon sigma : ℝ,
    0 < epsilon → epsilon ≤ 1 / 2 →
    0 < sigma → sigma < 1 →
    ∃ eta delta₀ : ℝ,
      0 < eta ∧ eta ≤ epsilon ∧
      1000 * eta ≤ epsilon * sigma ^ 2 ∧
      0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
        ∀ F : Kakeya.Streamlined.TubeFamily delta,
          ∀ U : Kakeya.Streamlined.UniformTubeStructure F,
            ∀ Y : Kakeya.Streamlined.TubeShading F,
              ∀ C : ENNReal,
                ∀ G : C2GrainStructure Y sigma C,
                  ∀ a b : ℝ,
                    ∀ refined :
                        LargeSlopeRefinementData
                          U Y sigma eta C G a b,
                      b - a ≤ Real.rpow delta epsilon →
                      ∀ z ∈ Set.Icc a b,
                        |deriv refined.grains.slope z| < b - a →
                          Nonempty
                            (LargeSlopeStep4Witness
                              refined.shading sigma eta a b)

/--
The geometric and quantitative core of Step 4 after the faithful prism
witness has been constructed.

The explicit relation `1000 η ≤ ε σ²` is the parameter gap spent on the
direction-width loss and the prism-count loss.  The conclusion is only the
convex overload certificate; contradiction with every-scale Frostman remains
the separate closed transition in `LargeSlopeFromOverload.lean`.
-/
def LargeSlopeConvexOverloadStatement : Prop :=
  ∀ epsilon sigma eta : ℝ,
    0 < epsilon → epsilon ≤ 1 / 2 →
    0 < sigma → sigma < 1 →
    0 < eta → eta ≤ epsilon →
    1000 * eta ≤ epsilon * sigma ^ 2 →
    ∃ delta₀ : ℝ,
      0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
        ∀ F : Kakeya.Streamlined.TubeFamily delta,
          ∀ U : Kakeya.Streamlined.UniformTubeStructure F,
            ∀ Y : Kakeya.Streamlined.TubeShading F,
              ∀ C : ENNReal,
                ∀ G : C2GrainStructure Y sigma C,
                  ∀ a b : ℝ,
                    ∀ refined :
                        LargeSlopeRefinementData
                          U Y sigma eta C G a b,
                    b - a ≤ Real.rpow delta epsilon →
                    ∀ step4 :
                        LargeSlopeStep4Witness
                          refined.shading sigma eta a b,
                      ∃ W : Set Point3,
                        Convex ℝ W ∧
                          Kakeya.realRpowENN delta (-eta) *
                              MeasureTheory.volume W * F.enncard <
                            F.toBodyFamily.containedCount W *
                              Kakeya.deltaTubeVolume 1

/--
Step 4 of the WZ2 replacement for the direction-separated large-slope lemma.
The input is the faithful stable refinement package rather than a loose list
of consequences that omits the paper's per-tube and prism geometry.
-/
def LargeSlopeTechnicalStatement : Prop :=
  ∀ epsilon sigma : ℝ,
    0 < epsilon → epsilon ≤ 1 / 2 →
    0 < sigma → sigma < 1 →
    ∃ eta delta₀ : ℝ,
      0 < eta ∧ eta ≤ epsilon ∧
      0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
        ∀ F : Kakeya.Streamlined.TubeFamily delta,
          ∀ U : Kakeya.Streamlined.UniformTubeStructure F,
            ∀ Y : Kakeya.Streamlined.TubeShading F,
              ∀ C : ENNReal,
                ∀ G : C2GrainStructure Y sigma C,
                  ∀ a b : ℝ,
                    ∀ refined :
                        LargeSlopeRefinementData
                          U Y sigma eta C G a b,
                    b - a ≤ Real.rpow delta epsilon →
                    ∀ z ∈ Set.Icc a b,
                      b - a ≤ |deriv refined.grains.slope z|

/--
The WZ Lemma 8 transport used after the large-slope interval.  It rescales the
tube family, slab shading, and global grain data, not merely the one-variable
slope.  The output records the bounded-window, density, Tube-Wolff, and small
projection properties consumed by Section 7 directly.  It does not fabricate
a coherent target `UniformTubeStructure` from carrier containment.
-/
def AnisotropicRescalingStatement : Prop :=
  TubeVolumeScalingStatement →
    ∀ sigma eta theta : ℝ,
      0 < sigma → sigma < 1 →
      0 < eta → eta < sigma →
      0 < theta → theta ≤ eta / 100 →
      ∀ rhoMax : ℝ, 0 < rhoMax →
        ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ < 1 ∧
          ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
            ∀ F : Kakeya.Streamlined.TubeFamily delta,
              ∀ U : Kakeya.Streamlined.UniformTubeStructure F,
                ∀ Y : Kakeya.Streamlined.TubeShading F,
                  IsExtremalPair sigma theta F U Y →
                  U.IsFrostmanAtEveryScale
                    (Kakeya.realRpowENN
                      delta (-(theta / 1000))) →
                  HasExtremalCardinalityUpper F (theta / 1000) →
                  IsInVerticalChart F →
                  ∀ C : ENNReal, 1 ≤ C → C ≠ ⊤ →
                    C ≤
                      Kakeya.realRpowENN delta (-(theta / 1000)) →
                    ∀ G : C2GrainStructure Y sigma C,
                      ∀ a b : ℝ,
                        -1 ≤ a → a < b → b ≤ 1 →
                        Kakeya.realRpowENN delta (1 / 2 : ℝ) ≤
                          ENNReal.ofReal (b - a) →
                        Kakeya.realRpowENN delta (eta / 100) ≤
                          ENNReal.ofReal (b - a) →
                        Kakeya.realRpowENN delta theta *
                            ENNReal.ofReal (b - a) ≤
                          shadedMassInSlab Y a b →
                        (∀ z ∈ Set.Icc a b,
                          b - a ≤ |deriv G.slope z|) →
                        ∃ c d m : ℝ,
                          a ≤ c ∧ c < d ∧ d ≤ b ∧
                          0 < m ∧
                          b - a ≤ m ∧ m ≤ 1 ∧
                          d - c = (b - a) / 50 ∧
                          ∃ rho : ℝ,
                            0 < rho ∧
                            rho ≤ rhoMax ∧
                            rho ≤ 200 * Real.sqrt delta ∧
                            rho < 1 ∧
                            ∃ F' : Kakeya.Streamlined.TubeFamily rho,
                              ∃ Y' : Kakeya.Streamlined.TubeShading F',
                                F'.Nonempty ∧
                                  HasBoundedBase F' 4 ∧
                                  F'.IsEssentiallyDistinct ∧
                                  IsInVerticalChart F' ∧
                                  TubeWolffBound F'
                                    (Kakeya.realRpowENN rho (-eta)) ∧
                                  TubeParameterFrostmanBound F'
                                    (Kakeya.realRpowENN rho (-eta)) ∧
                                  HasExtremalCardinalityUpper F' (eta / 10) ∧
                                  Y'.IsLambdaDense
                                    (Kakeya.realRpowENN rho eta) ∧
                                  IsInSlopeWindow Y' ∧
                                  Y'.union ⊆
                                    Metric.cthickening rho
                                      (anisotropicRescalingMap
                                        G.slope c d m ''
                                          (Y.union ∩ horizontalSlab c d)) ∧
                                  ENNReal.ofReal m *
                                      shadedMassInSlab Y c d ≤
                                    Kakeya.realRpowENN rho (-(eta / 10)) *
                                      Y'.mass ∧
                                  ∃ f : SlopeFunction,
                                    f.IsNonsingular ∧
                                    f 0 = 0 ∧
                                    (∀ t : ℝ,
                                      f t =
                                        G.slope
                                            (c + (d - c) / 2 * (t + 1)) /
                                              (m * (d - c) / 2) -
                                          G.slope (c + (d - c) / 2) /
                                            (m * (d - c) / 2)) ∧
                                    MeasureTheory.volume (twistedUnion Y' f) ≤
                                      Kakeya.realRpowENN rho (sigma - eta)

/--
Choose the WZ Lemma 8 subinterval, derivative bracket, normalized slope, and
target scale with every small-scale inequality needed by the cleaned
geometric and analytic leaves.

This isolates parameter selection from the later family construction.  The
source slab loss remains `theta`, while `eta` controls only the mild length
and target-scale absorption.
-/
def AnisotropicParameterPreparationStatement : Prop :=
  ∀ eta theta rhoMax : ℝ,
    0 < eta → eta < 1 →
    0 < theta → theta ≤ eta / 100 →
    0 < rhoMax →
      ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
        ∀ {delta a b : ℝ},
          0 < delta → delta ≤ delta₀ →
          -1 ≤ a → a < b → b ≤ 1 →
          Kakeya.realRpowENN delta (1 / 2 : ℝ) ≤
            ENNReal.ofReal (b - a) →
          Kakeya.realRpowENN delta (eta / 100) ≤
            ENNReal.ofReal (b - a) →
          ∀ F : Kakeya.Streamlined.TubeFamily delta,
            ∀ Y : Kakeya.Streamlined.TubeShading F,
              ∀ g : SlopeFunction, g.IsNormalized →
                Kakeya.realRpowENN delta theta *
                    ENNReal.ofReal (b - a) ≤
                  shadedMassInSlab Y a b →
                (∀ z ∈ Set.Icc a b,
                  b - a ≤ |deriv g z|) →
                ∃ c d m rho : ℝ,
                  ∃ f : SlopeFunction,
                    a ≤ c ∧ c < d ∧ d ≤ b ∧
                    d - c = (b - a) / 50 ∧
                    Set.Icc c d ⊆ Set.Icc (-1 : ℝ) 1 ∧
                    0 < m ∧ 50 * (d - c) ≤ m ∧ m ≤ 1 ∧
                    0 < rho ∧
                    rho = 2 * delta / (d - c) ∧
                    delta ≤ rho ∧
                    rho ≤ rhoMax ∧
                    rho ≤ 200 * Real.sqrt delta ∧
                    rho ≤ 1 / 10000 ∧
                    delta ≤ 1 / 100 ∧
                    Real.rpow delta (eta / 100) ≤
                      50 * (d - c) ∧
                    Kakeya.realRpowENN delta theta *
                        ENNReal.ofReal (d - c) ≤
                      shadedMassInSlab Y c d ∧
                    f.IsNonsingular ∧
                    f 0 = 0 ∧
                    ∀ t : ℝ,
                      f t =
                        g (c + (d - c) / 2 * (t + 1)) /
                            (m * (d - c) / 2) -
                          g (c + (d - c) / 2) /
                            (m * (d - c) / 2)

/--
Positive retained slab mass forces the cleaned target family to be nonempty.

The proof uses only `massLower` and `massLoss_ne_top`; no target density or
uniform structure is assumed.
-/
def CleanedAnisotropicTargetNonemptyStatement : Prop :=
  ∀ {delta rho c d m : ℝ},
    ∀ F : Kakeya.Streamlined.TubeFamily delta,
      ∀ Y : Kakeya.Streamlined.TubeShading F,
        ∀ g : SlopeFunction,
          ∀ cleaned :
              CleanedAnisotropicTarget
                (rho := rho) (c := c) (d := d) (m := m)
                F Y g,
            0 < m →
            0 < shadedMassInSlab Y c d →
              cleaned.family.Nonempty

/--
The geometric twisted-projection upper bound after cleaned anisotropic
rediscretization.

Exact projection normalization identifies the affine image with the
height-dependent source global-grain coordinate.  The source
`C2GrainStructure.global_slab_ad` condition controls each source
`delta`-slab; the scale identity `rho = 2 * delta / (d-c)` sends it to one
target `rho`-strip.  Source-local target shading containment then adds only
the target-radius thickening.
-/
def CleanedAnisotropicTwistedProjectionUpperStatement : Prop :=
  ∀ sigma delta rho c d m : ℝ,
    0 < sigma → sigma < 1 →
    0 < delta → delta ≤ rho → rho ≤ 1 →
    c < d →
    Set.Icc c d ⊆ Set.Icc (-1 : ℝ) 1 →
    rho = 2 * delta / (d - c) →
    0 < m →
    ∀ F : Kakeya.Streamlined.TubeFamily delta,
      ∀ Y : Kakeya.Streamlined.TubeShading F,
        ∀ C : ENNReal, 1 ≤ C → C ≠ ⊤ →
          ∀ G : C2GrainStructure Y sigma C,
            ∀ cleaned :
                CleanedAnisotropicTarget
                  (rho := rho) (c := c) (d := d) (m := m)
                  F Y G.slope,
              ∀ f : SlopeFunction,
                f.IsNonsingular →
                f 0 = 0 →
                (∀ t : ℝ,
                  f t =
                    G.slope (c + (d - c) / 2 * (t + 1)) /
                        (m * (d - c) / 2) -
                      G.slope (c + (d - c) / 2) /
                        (m * (d - c) / 2)) →
                MeasureTheory.volume
                    (twistedUnion cleaned.shading f) ≤
                  1000000 * C * Kakeya.realRpowENN rho sigma

/--
Absorb the raw global-AD projection constant into the paper's
`rho^(sigma-eta)` upper bound.
-/
def CleanedAnisotropicProjectionAbsorptionStatement : Prop :=
  CleanedAnisotropicTwistedProjectionUpperStatement →
    ∀ sigma eta delta rho c d m : ℝ,
      0 < sigma → sigma < 1 →
      0 < eta → eta < sigma →
      0 < delta → delta ≤ rho → rho ≤ 1 →
      c < d →
      Set.Icc c d ⊆ Set.Icc (-1 : ℝ) 1 →
      rho = 2 * delta / (d - c) →
      0 < m →
      ∀ F : Kakeya.Streamlined.TubeFamily delta,
        ∀ Y : Kakeya.Streamlined.TubeShading F,
          ∀ C : ENNReal, 1 ≤ C → C ≠ ⊤ →
            C ≤ Kakeya.realRpowENN rho (-(eta / 2)) →
            1000000 ≤ Kakeya.realRpowENN rho (-(eta / 2)) →
            ∀ G : C2GrainStructure Y sigma C,
              ∀ cleaned :
                  CleanedAnisotropicTarget
                    (rho := rho) (c := c) (d := d) (m := m)
                    F Y G.slope,
                ∀ f : SlopeFunction,
                  f.IsNonsingular →
                  f 0 = 0 →
                  (∀ t : ℝ,
                    f t =
                      G.slope (c + (d - c) / 2 * (t + 1)) /
                          (m * (d - c) / 2) -
                        G.slope (c + (d - c) / 2) /
                          (m * (d - c) / 2)) →
                  MeasureTheory.volume
                      (twistedUnion cleaned.shading f) ≤
                    Kakeya.realRpowENN rho (sigma - eta)

/--
Transfer the strong source constant bound to the target-scale loss needed by
the raw projection absorption.

The source exponent is only `theta / 1000`, while
`rho ≤ 200 sqrt(delta)` supplies nearly an `eta / 4` target exponent.  Thus a
fixed factor is absorbed with a wide positive gap.
-/
def CleanedProjectionConstantTransferStatement : Prop :=
  ∀ eta theta : ℝ,
    0 < eta → eta < 1 →
    0 < theta → theta ≤ eta / 100 →
      ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
        ∀ {delta rho : ℝ},
          0 < delta → delta ≤ delta₀ →
          0 < rho → rho ≤ 200 * Real.sqrt delta →
          ∀ C : ENNReal,
            C ≤
              Kakeya.realRpowENN delta (-(theta / 1000)) →
            C ≤ Kakeya.realRpowENN rho (-(eta / 2))

/--
Two cleaned target tubes contained in one coarser tube form a parameter
cluster at the coarse radius.

This is the scale-general analogue of nonessential-overlap clustering.  It is
the geometric input for transferring source parameter Frostman control to the
target Tube-Wolff bound at every scale.
-/
def CommonContainerTargetTubeParameterClusterStatement : Prop :=
  ∀ (rho tau : ℝ),
    0 < rho → rho ≤ tau → tau ≤ 1 / 10000 →
    ∀ A B : Kakeya.DeltaTube rho,
      (1 / 2 : ℝ) ≤ |A.direction (2 : Fin 3)| →
      (1 / 2 : ℝ) ≤ |B.direction (2 : Fin 3)| →
      ‖A.base‖ ≤ 3 → ‖B.base‖ ≤ 3 →
      ∀ U : Kakeya.DeltaTube tau,
        A.carrier ⊆ U.carrier →
        B.carrier ⊆ U.carrier →
          |(tubeParamsOfTube A).a - (tubeParamsOfTube B).a| ≤
              100000 * tau ∧
            |(tubeParamsOfTube A).b - (tubeParamsOfTube B).b| ≤
              100000 * tau ∧
            |(tubeParamsOfTube A).c - (tubeParamsOfTube B).c| ≤
              100000 * tau ∧
            |(tubeParamsOfTube A).d - (tubeParamsOfTube B).d| ≤
              100000 * tau

/--
The common-container parameter cluster in the radius-five basepoint window.

This is the version needed by selected-scale four-block families.  The
common-container construction places the auxiliary point on the second tube's
axis within `20 * tau` of the first basepoint, so its norm is at most six.
The resulting intercept loss is at most
`20 + 20 * 2 + 6 * 64 = 444`, leaving ample room in the same explicit
`100000 * tau` parameter box.
-/
def CommonContainerTargetTubeParameterClusterBaseFiveStatement : Prop :=
  ∀ (rho tau : ℝ),
    0 < rho → rho ≤ tau → tau ≤ 1 / 10000 →
    ∀ A B : Kakeya.DeltaTube rho,
      (1 / 2 : ℝ) ≤ |A.direction (2 : Fin 3)| →
      (1 / 2 : ℝ) ≤ |B.direction (2 : Fin 3)| →
      ‖A.base‖ ≤ 5 → ‖B.base‖ ≤ 5 →
      ∀ U : Kakeya.DeltaTube tau,
        A.carrier ⊆ U.carrier →
        B.carrier ⊆ U.carrier →
          |(tubeParamsOfTube A).a - (tubeParamsOfTube B).a| ≤
              100000 * tau ∧
            |(tubeParamsOfTube A).b - (tubeParamsOfTube B).b| ≤
              100000 * tau ∧
            |(tubeParamsOfTube A).c - (tubeParamsOfTube B).c| ≤
              100000 * tau ∧
            |(tubeParamsOfTube A).d - (tubeParamsOfTube B).d| ≤
              100000 * tau

/--
Source non-concentration and the exact finite loss attached to a cleaned
anisotropic target.

This certificate keeps the source Frostman constant tied to the input
Convex-Wolff constant `C`; a bare existential constant would be too weak for
the final small-scale absorption.
-/
structure CleanedAnisotropicSourceData
    {delta rho c d m : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    {g : SlopeFunction}
    (C : ENNReal)
    (cleaned :
      CleanedAnisotropicTarget
        (rho := rho) (c := c) (d := d) (m := m) F Y g) where
  parameterConstant : ENNReal
  parameterConstant_eq :
    parameterConstant =
      200 * C * (Kakeya.deltaTubeVolume 1)⁻¹
  parameterFrostman :
    TubeParameterFrostmanBound F parameterConstant
  massLoss_eq :
    cleaned.massLoss =
      3 *
        (parameterConstant *
          Kakeya.realRpowENN
            (100 * (100000 * rho) / (m * (d - c) ^ 2)) 2 *
            F.enncard) + 1

/--
Absorb the explicit finite cleanup degree into the final WZ Lemma 8 mass
loss.

The strong `theta / 1000` source bounds are kept separate from the
`eta / 100` mild-length input.  Together with `m ≥ 50(d-c)` and
`rho = 2 delta / (d-c)`, they leave a positive power gap before the requested
`rho^(-eta/10)` loss.
-/
def CleanedAnisotropicMassLossAbsorptionStatement : Prop :=
  ∀ eta theta : ℝ,
    0 < eta → eta < 1 →
    0 < theta → theta ≤ eta / 100 →
      ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
        ∀ {delta rho c d m : ℝ},
          0 < delta → delta ≤ delta₀ →
          c < d → d - c ≤ 1 / 25 →
          rho = 2 * delta / (d - c) →
          0 < m → 50 * (d - c) ≤ m → m ≤ 1 →
          Real.rpow delta (eta / 100) ≤ 50 * (d - c) →
          ∀ F : Kakeya.Streamlined.TubeFamily delta,
            ∀ Y : Kakeya.Streamlined.TubeShading F,
              ∀ g : SlopeFunction,
                ∀ C : ENNReal,
                  C ≤
                    Kakeya.realRpowENN delta (-(theta / 1000)) →
                  HasExtremalCardinalityUpper F (theta / 1000) →
                  ∀ cleaned :
                      CleanedAnisotropicTarget
                        (rho := rho) (c := c) (d := d) (m := m)
                        F Y g,
                    CleanedAnisotropicSourceData C cleaned →
                    cleaned.massLoss ≤
                      Kakeya.realRpowENN rho (-(eta / 10))

/--
Convert the cleaned mass refinement into a multiplicative comparison between
the source and target cardinalities.

The statement deliberately keeps the cleanup loss explicit.  The source
cardinality upper bound and the quadratic target-tube volume upper bound are
the only cardinality inputs; no coherent target cover or uniform structure is
fabricated.
-/
def CleanedTargetCardinalityProductStatement : Prop :=
  TubeVolumeScalingStatement →
    ∀ {delta rho c d m slabLoss cardinalityLoss : ℝ},
      0 < delta → delta ≤ 1 →
      0 < rho → rho ≤ 1 →
      c < d → 0 < m →
      ∀ F : Kakeya.Streamlined.TubeFamily delta,
        ∀ Y : Kakeya.Streamlined.TubeShading F,
        ∀ g : SlopeFunction,
          ∀ cleaned :
              CleanedAnisotropicTarget
                (rho := rho) (c := c) (d := d) (m := m)
                F Y g,
            HasExtremalCardinalityUpper F cardinalityLoss →
            Kakeya.realRpowENN delta slabLoss *
                ENNReal.ofReal (d - c) ≤
              shadedMassInSlab Y c d →
              ENNReal.ofReal m *
                    Kakeya.realRpowENN delta slabLoss *
                    ENNReal.ofReal (d - c) *
                    F.enncard ≤
                24 * cleaned.massLoss *
                    Kakeya.realRpowENN rho 2 *
                    Kakeya.deltaTubeVolume 1 *
                    Kakeya.realRpowENN delta (-2 - cardinalityLoss) *
                    cleaned.family.enncard

/--
The cleaned target family contains at most three indexed targets for each
source tube.

This is the global cardinality consequence of `sourceFiberCap`; it keeps
indexed multiplicity rather than silently deduplicating equal target tubes.
-/
def CleanedTargetCardinalityUpperStatement : Prop :=
  ∀ {delta rho c d m : ℝ},
    ∀ F : Kakeya.Streamlined.TubeFamily delta,
      ∀ Y : Kakeya.Streamlined.TubeShading F,
        ∀ g : SlopeFunction,
          ∀ cleaned :
              CleanedAnisotropicTarget
                (rho := rho) (c := c) (d := d) (m := m) F Y g,
            cleaned.family.enncard ≤ 3 * F.enncard

/--
Transfer the source extremal cardinality window to the cleaned target scale.

The target has at most three indices above each source tube.  The mild-scale
lower bound on `d - c` and `rho = 2 delta / (d-c)` convert the source
`delta^(-2-theta/1000)` bound into the target
`rho^(-2-eta/10)` bound after fixed constants are absorbed at small scale.
-/
def CleanedTargetCardinalityScaleTransferStatement : Prop :=
  CleanedTargetCardinalityUpperStatement →
    ∀ eta theta : ℝ,
      0 < eta → eta < 1 →
      0 < theta → theta ≤ eta / 100 →
        ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
          ∀ {delta rho c d m : ℝ},
            0 < delta → delta ≤ delta₀ →
            0 < rho → rho ≤ 1 →
            c < d →
            rho = 2 * delta / (d - c) →
            0 < m → 50 * (d - c) ≤ m → m ≤ 1 →
            Real.rpow delta (eta / 100) ≤ 50 * (d - c) →
            ∀ F : Kakeya.Streamlined.TubeFamily delta,
              ∀ Y : Kakeya.Streamlined.TubeShading F,
                ∀ g : SlopeFunction,
                  ∀ cleaned :
                      CleanedAnisotropicTarget
                        (rho := rho) (c := c) (d := d) (m := m)
                        F Y g,
                    HasExtremalCardinalityUpper F (theta / 1000) →
                      HasExtremalCardinalityUpper
                        cleaned.family (eta / 10)

/--
Solve the normalized cardinality product for the source cardinality.

All factors in the denominator are strictly positive and finite by the
explicit geometric hypotheses.  The conclusion is the exact
`cardinalityLoss` input consumed by the cleaned target Tube-Wolff transfer.
-/
def CleanedTargetCardinalityLossStatement : Prop :=
  CleanedTargetCardinalityProductStatement →
    ∀ {delta rho c d m slabLoss cardinalityLoss : ℝ},
      0 < delta → delta ≤ 1 →
      0 < rho → rho ≤ 1 →
      c < d → 0 < m →
      ∀ F : Kakeya.Streamlined.TubeFamily delta,
        ∀ Y : Kakeya.Streamlined.TubeShading F,
          ∀ g : SlopeFunction,
            ∀ cleaned :
                CleanedAnisotropicTarget
                  (rho := rho) (c := c) (d := d) (m := m)
                  F Y g,
              HasExtremalCardinalityUpper F cardinalityLoss →
              Kakeya.realRpowENN delta slabLoss *
                  ENNReal.ofReal (d - c) ≤
                shadedMassInSlab Y c d →
                F.enncard ≤
                  ((ENNReal.ofReal m *
                    Kakeya.realRpowENN delta slabLoss *
                    ENNReal.ofReal (d - c))⁻¹ *
                      (24 * cleaned.massLoss *
                        Kakeya.realRpowENN rho 2 *
                        Kakeya.deltaTubeVolume 1 *
                        Kakeya.realRpowENN
                          delta (-2 - cardinalityLoss))) *
                    cleaned.family.enncard

/--
Convert the cleaned mass refinement into aggregate density relative to the
cleaned target family.

The result exposes exactly the finite cleanup loss and the target/source
cardinality factor.  Later small-scale arithmetic may absorb these explicit
losses into a power of `rho`; this leaf does not assume a target uniform
structure.
-/
def CleanedTargetDensityTransferStatement : Prop :=
  TubeVolumeScalingStatement →
    CleanedTargetCardinalityUpperStatement →
      ∀ {delta rho c d m slabLoss cardinalityLoss : ℝ},
        0 < delta → delta ≤ 1 →
        0 < rho → rho ≤ 1 →
        c < d → 0 < m →
        ∀ F : Kakeya.Streamlined.TubeFamily delta,
          ∀ Y : Kakeya.Streamlined.TubeShading F,
            ∀ g : SlopeFunction,
              ∀ cleaned :
                  CleanedAnisotropicTarget
                    (rho := rho) (c := c) (d := d) (m := m)
                    F Y g,
                HasExtremalCardinalityUpper F cardinalityLoss →
                Kakeya.realRpowENN delta slabLoss *
                    ENNReal.ofReal (d - c) ≤
                  shadedMassInSlab Y c d →
                  (ENNReal.ofReal m *
                      Kakeya.realRpowENN delta slabLoss *
                      ENNReal.ofReal (d - c)) *
                      cleaned.family.toBodyFamily.mass ≤
                    (72 * cleaned.massLoss *
                      Kakeya.realRpowENN rho 2 *
                      Kakeya.deltaTubeVolume 1 *
                      Kakeya.realRpowENN
                        delta (-2 - cardinalityLoss)) *
                        cleaned.shading.mass

/--
Absorb the explicit density-transfer coefficient and obtain the aggregate
`rho^eta` density required by Section 7.

This is pure WZ Lemma 8 small-scale bookkeeping.  The geometric inputs are
the already-frozen cleaned density transfer and mass-loss absorption leaves;
the source slab and cardinality losses remain distinct.
-/
def CleanedTargetLambdaDensityAbsorptionStatement : Prop :=
  TubeVolumeScalingStatement →
    CleanedTargetCardinalityUpperStatement →
      CleanedTargetDensityTransferStatement →
        CleanedAnisotropicMassLossAbsorptionStatement →
          ∀ eta theta : ℝ,
            0 < eta → eta < 1 →
            0 < theta → theta ≤ eta / 100 →
              ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
                ∀ {delta rho c d m : ℝ},
                  0 < delta → delta ≤ delta₀ →
                  c < d → d - c ≤ 1 / 25 →
                  rho = 2 * delta / (d - c) →
                  0 < rho → rho ≤ 1 →
                  0 < m → 50 * (d - c) ≤ m → m ≤ 1 →
                  Real.rpow delta (eta / 100) ≤ 50 * (d - c) →
                  ∀ F : Kakeya.Streamlined.TubeFamily delta,
                    ∀ Y : Kakeya.Streamlined.TubeShading F,
                      ∀ g : SlopeFunction,
                        ∀ C : ENNReal,
                          C ≤
                            Kakeya.realRpowENN
                              delta (-(theta / 1000)) →
                          HasExtremalCardinalityUpper
                            F (theta / 1000) →
                          Kakeya.realRpowENN delta theta *
                              ENNReal.ofReal (d - c) ≤
                            shadedMassInSlab Y c d →
                          ∀ cleaned :
                              CleanedAnisotropicTarget
                                (rho := rho) (c := c) (d := d) (m := m)
                                F Y g,
                            CleanedAnisotropicSourceData C cleaned →
                            cleaned.shading.IsLambdaDense
                              (Kakeya.realRpowENN rho eta)

/--
Explicit inverse distortion for the mild anisotropic map.

The bound is deliberately written with the actual small singular scale
`m * (d - c)`.  It is the line-geometry input needed to pull target closeness
back to source coaxial lines; injectivity alone carries no quantitative
information.
-/
def AnisotropicRescalingInverseDistortionStatement : Prop :=
  ∀ (g : SlopeFunction) (c d m : ℝ),
    c < d → d - c ≤ 1 →
    0 < m → m ≤ 1 →
    |g (c + (d - c) / 2)| ≤ 1 →
      ∀ p q : Point3,
        dist p q ≤
          (10 / (m * (d - c))) *
            dist (anisotropicRescalingMap g c d m p)
              (anisotropicRescalingMap g c d m q)

/--
Exact projective direction recorded by whole-line provenance.

If a target tube's full axis is the affine image of a source tube's full
axis, then its unit direction is a nonzero scalar multiple of the source
direction transformed by the linear part of the anisotropic map.  The scalar
is not forced positive because tube orientations are arbitrary.
-/
def CoaxialImageDirectionStatement : Prop :=
  ∀ (g : SlopeFunction) (c d m rho delta : ℝ),
    c < d → 0 < m →
      ∀ S : Kakeya.DeltaTube delta,
        ∀ A : Kakeya.DeltaTube rho,
          tubeAxisLine A =
              anisotropicRescalingMap g c d m '' tubeAxisLine S →
            ∃ lambda : ℝ, lambda ≠ 0 ∧
              A.direction =
                lambda •
                  anisotropicImageDirection g c d m S.direction

/--
Package the already-proved one-tube anisotropic covering lemma uniformly over
a finite source family.  The output keeps all three target tubes per source
index; deduplication, essential distinctness, and coherent uniform structure
are separate later operations.
-/
def ThreeTubeImageCoverStatement : Prop :=
  ∀ (delta c d m rho : ℝ),
    0 < delta → c < d →
    d - c ≤ 1 / 25 →
    delta ≤ 1 / 100 →
    2 * delta / (d - c) ≤ 1 / 4 →
    rho = 2 * delta / (d - c) →
    0 < m → m ≤ 1 →
    Set.Icc c d ⊆ Set.Icc (-1 : ℝ) 1 →
    ∀ F : Kakeya.Streamlined.TubeFamily delta,
      IsInVerticalChart F →
      ∀ g : SlopeFunction, g.IsNormalized →
        Nonempty (ThreeTubeImageCover (rho := rho) F
          (anisotropicRescalingMap g c d m)
          (fun i => (F.tube i).carrier ∩ horizontalSlab c d))

/--
Flatten a three-tube image cover to the actual finite target `TubeFamily`
indexed by `Fin (F.card * 3)`.  This step preserves every indexed copy and
therefore does not claim essential distinctness or construct a uniform
structure.
-/
def FlattenThreeTubeImageCoverStatement : Prop :=
  ∀ {delta rho : ℝ},
    ∀ F : Kakeya.Streamlined.TubeFamily delta,
      ∀ Φ : Point3 → Point3,
        ∀ source : Fin F.card → Set Point3,
          ∀ W : ThreeTubeImageCover (rho := rho) F Φ source,
            ∃ coarse : Kakeya.Streamlined.TubeFamily rho,
              coarse.card = F.card * 3 ∧
                (∀ i, Φ '' source i ⊆ coarse.toBodyFamily.union) ∧
                IsInVerticalChart coarse

/--
Assemble the already-proved three-tube cover into the concrete target family
and its image-induced shading.  This leaf deliberately stops before
essential-distinctness extraction and the coherent every-scale structure.
-/
def AnisotropicTargetFamilyShadingStatement : Prop :=
  ThreeTubeImageCoverStatement →
    FlattenThreeTubeImageCoverStatement →
      ∀ (delta c d m rho : ℝ),
        0 < delta → c < d →
        d - c ≤ 1 / 25 →
        delta ≤ 1 / 100 →
        2 * delta / (d - c) ≤ 1 / 4 →
        rho = 2 * delta / (d - c) →
        0 < m → m ≤ 1 →
        Set.Icc c d ⊆ Set.Icc (-1 : ℝ) 1 →
        ∀ F : Kakeya.Streamlined.TubeFamily delta,
          IsInVerticalChart F →
          ∀ Y : Kakeya.Streamlined.TubeShading F,
            ∀ g : SlopeFunction, g.IsNormalized →
              ∃ coarse : Kakeya.Streamlined.TubeFamily rho,
                ∃ Y' : Kakeya.Streamlined.TubeShading coarse,
                  coarse.card = F.card * 3 ∧
                  IsInVerticalChart coarse ∧
                  anisotropicRescalingMap g c d m ''
                      (Y.union ∩ horizontalSlab c d) ⊆
                    Y'.union ∧
                  Y'.union ⊆
                    Metric.cthickening rho
                      (anisotropicRescalingMap g c d m ''
                        (Y.union ∩ horizontalSlab c d)) ∧
                  IsInSlopeWindow Y'

/--
Cover a segment of length less than three by three consecutive unit segments,
while retaining an explicit basepoint bound.

The direction condition is the normalized vertical-chart condition for the
segment.  In the degenerate case `P = Q`, any vertical unit direction may be
used.  The basepoint estimate is the quantitative input needed to keep the
anisotropically rediscretized family in a fixed bounded window.
-/
def BoundedThreeSegmentCoverStatement : Prop :=
  ∀ P Q : Point3, dist P Q < 3 →
    (P = Q ∨
      (1 / 2 : ℝ) ≤ |(Q - P) (2 : Fin 3)| / ‖Q - P‖) →
      ∃ base : Fin 3 → Point3,
        ∃ direction : Point3,
          ‖direction‖ = 1 ∧
          (1 / 2 : ℝ) ≤ |direction (2 : Fin 3)| ∧
          (∀ k, ‖base k‖ ≤ max ‖P‖ ‖Q‖ + 1) ∧
          ∀ x,
            (∃ t ∈ Set.Icc (0 : ℝ) 1,
              x = P + t • (Q - P)) →
              x ∈ ⋃ k : Fin 3,
                Kakeya.unitSegment (base k) direction

/--
Package the anisotropic image cover with the bounded-window information needed
downstream.

The source family is genuinely contained in the unit ball.  Clipped image-axis
endpoints therefore have norm at most two, and the bounded short-segment cover
places every target tube basepoint in the radius-three window.
-/
def BoundedThreeTubeImageCoverStatement : Prop :=
  BoundedThreeSegmentCoverStatement →
    ∀ (delta c d m rho : ℝ),
      0 < delta → c < d →
      d - c ≤ 1 / 25 →
      delta ≤ 1 / 100 →
      2 * delta / (d - c) ≤ 1 / 4 →
      rho = 2 * delta / (d - c) →
      0 < m → m ≤ 1 →
      Set.Icc c d ⊆ Set.Icc (-1 : ℝ) 1 →
      ∀ F : Kakeya.Streamlined.TubeFamily delta,
        F.IsInUnitBall →
        IsInVerticalChart F →
        ∀ g : SlopeFunction, g.IsNormalized →
          ∃ W : ThreeTubeImageCover (rho := rho) F
              (anisotropicRescalingMap g c d m)
              (fun i =>
                (F.tube i).carrier ∩ horizontalSlab c d),
            ∀ i k, ‖(W.tube i k).base‖ ≤ 3

/--
Strengthen the bounded anisotropic image cover with the line provenance stated
in WZ Lemma 8.  Every target tube is coaxial with the affine image of the full
source axis whenever the source tube actually contributes to the selected
slab.  Tubes missing the slab impose no provenance or basepoint obligation.
-/
def BoundedCoaxialThreeTubeImageCoverStatement : Prop :=
  ∀ (delta c d m rho : ℝ),
    0 < delta → c < d →
    d - c ≤ 1 / 25 →
    delta ≤ 1 / 100 →
    2 * delta / (d - c) ≤ 1 / 4 →
    rho = 2 * delta / (d - c) →
    0 < m → m ≤ 1 →
    Set.Icc c d ⊆ Set.Icc (-1 : ℝ) 1 →
    ∀ F : Kakeya.Streamlined.TubeFamily delta,
      F.IsInUnitBall →
      IsInVerticalChart F →
      ∀ g : SlopeFunction, g.IsNormalized →
        ∃ W : CoaxialThreeTubeImageCover (rho := rho) F
            (anisotropicRescalingMap g c d m)
            (fun i =>
              (F.tube i).carrier ∩ horizontalSlab c d),
          ∀ i,
            ((F.tube i).carrier ∩ horizontalSlab c d).Nonempty →
              ∀ k, ‖(W.tube i k).base‖ ≤ 3

/--
Finite maximal selection of pairwise essentially distinct tubes.  Every
discarded index fails essential distinctness with a selected representative.
This is the combinatorial half of the rediscretization cleanup.
-/
def MaximalEssentiallyDistinctSubfamilyStatement : Prop :=
  ∀ {delta : ℝ}, ∀ F : Kakeya.Streamlined.TubeFamily delta,
    ∃ selected : Finset (Fin F.card),
      (∀ i ∈ selected, ∀ j ∈ selected, i ≠ j →
        (F.tube i).EssentiallyDistinct (F.tube j)) ∧
      ∀ i : Fin F.card,
        i ∈ selected ∨
          ∃ j ∈ selected,
            ¬(F.tube i).EssentiallyDistinct (F.tube j)

/--
Geometric half of rediscretization cleanup.  If two thin unit tubes have
more than half-overlap in the repository's volume-based sense, their
unoriented axes are close: after possibly reversing one direction, the
directions are `O(delta)`-close and one base lies near the other's extended
axis over a bounded parameter interval.
-/
def NonessentialTubeAxisAlignmentStatement : Prop :=
  ∀ (delta : ℝ), 0 < delta → delta ≤ 1 / 1000 →
    ∀ T U : Kakeya.DeltaTube delta,
      ¬T.EssentiallyDistinct U →
        ∃ (sign : ℝ) (anchor : Point3),
          (sign = 1 ∧ anchor = U.base ∨
            sign = -1 ∧ anchor = U.base + U.direction) ∧
          ‖T.direction - sign • U.direction‖ ≤ 1000 * delta ∧
          ∃ s ∈ Set.Icc (-1 : ℝ) 1,
            ‖T.base - (anchor + s • (sign • U.direction))‖ ≤
              1002 * delta

/--
Pull a target-tube conflict back to proximity of the source coaxial lines.

Whole-line provenance supplies preimages of one target basepoint and the
nearby point on the other target axis.  The orientation-aware overlap lemma
localizes those target points, and inverse distortion returns source-line
points at the correct singular scale.  This deliberately does not assert
proximity of the stored source unit segments.
-/
def NonessentialImageTubesSourceLineProximityStatement : Prop :=
  NonessentialTubeAxisAlignmentStatement →
    AnisotropicRescalingInverseDistortionStatement →
      ∀ (g : SlopeFunction) (c d m rho : ℝ),
        c < d → d - c ≤ 1 →
        0 < m → m ≤ 1 →
        |g (c + (d - c) / 2)| ≤ 1 →
        0 < rho → rho ≤ 1 / 1000 →
        ∀ {delta : ℝ},
          ∀ S T : Kakeya.DeltaTube delta,
            ∀ A B : Kakeya.DeltaTube rho,
              tubeAxisLine A =
                  anisotropicRescalingMap g c d m '' tubeAxisLine S →
              tubeAxisLine B =
                  anisotropicRescalingMap g c d m '' tubeAxisLine T →
              ¬A.EssentiallyDistinct B →
                ∃ p ∈ tubeAxisLine S,
                  ∃ q ∈ tubeAxisLine T,
                    dist p q ≤
                      10020 * rho / (m * (d - c))

/--
Pull a target conflict back to a cluster in the two source direction
parameters.

Target verticality turns direction-norm alignment into closeness of the two
projective target slopes.  Exact image-direction provenance then inverts the
anisotropic diagonal scales.  This controls only the source direction
parameters; axial position remains separate.
-/
def NonessentialImageTubesSourceSlopeClusterStatement : Prop :=
  NonessentialTubeAxisAlignmentStatement →
    CoaxialImageDirectionStatement →
      ∀ (g : SlopeFunction) (c d m rho : ℝ),
        c < d → d - c ≤ 1 →
        0 < m → m ≤ 1 →
        |g (c + (d - c) / 2)| ≤ 1 →
        0 < rho → rho ≤ 1 / 1000 →
        ∀ {delta : ℝ},
          ∀ S T : Kakeya.DeltaTube delta,
            (1 / 2 : ℝ) ≤ |S.direction (2 : Fin 3)| →
            (1 / 2 : ℝ) ≤ |T.direction (2 : Fin 3)| →
            ∀ A B : Kakeya.DeltaTube rho,
              (1 / 2 : ℝ) ≤ |A.direction (2 : Fin 3)| →
              (1 / 2 : ℝ) ≤ |B.direction (2 : Fin 3)| →
              tubeAxisLine A =
                  anisotropicRescalingMap g c d m '' tubeAxisLine S →
              tubeAxisLine B =
                  anisotropicRescalingMap g c d m '' tubeAxisLine T →
              ¬A.EssentiallyDistinct B →
                |S.direction (0 : Fin 3) / S.direction (2 : Fin 3) -
                    T.direction (0 : Fin 3) / T.direction (2 : Fin 3)| ≤
                    100000 * rho / (m * (d - c) ^ 2) ∧
                  |S.direction (1 : Fin 3) / S.direction (2 : Fin 3) -
                    T.direction (1 : Fin 3) / T.direction (2 : Fin 3)| ≤
                    100000 * rho / (m * (d - c) ^ 2)

/--
A conflict between bounded target tubes gives a four-parameter box in the
vertical chart.

Unlike source-line proximity, this statement uses bounded target basepoints.
That window controls the height at which axis alignment is observed and hence
turns slope proximity into intercept proximity.
-/
def NonessentialTargetTubeParameterClusterStatement : Prop :=
  NonessentialTubeAxisAlignmentStatement →
    ∀ (rho : ℝ), 0 < rho → rho ≤ 1 / 1000 →
      ∀ A B : Kakeya.DeltaTube rho,
        (1 / 2 : ℝ) ≤ |A.direction (2 : Fin 3)| →
        (1 / 2 : ℝ) ≤ |B.direction (2 : Fin 3)| →
        ‖A.base‖ ≤ 3 → ‖B.base‖ ≤ 3 →
        ¬A.EssentiallyDistinct B →
          |(tubeParamsOfTube A).a - (tubeParamsOfTube B).a| ≤
              100000 * rho ∧
            |(tubeParamsOfTube A).b - (tubeParamsOfTube B).b| ≤
              100000 * rho ∧
            |(tubeParamsOfTube A).c - (tubeParamsOfTube B).c| ≤
              100000 * rho ∧
            |(tubeParamsOfTube A).d - (tubeParamsOfTube B).d| ≤
              100000 * rho

/--
The same target-parameter conflict bound in the radius-five basepoint window.

Selected-scale four-block enlargement spends one additional unit beyond the
WZ Lemma 8 radius-four source window.  The proof of the radius-three version
has enough numerical slack: the auxiliary point has norm at most seven and
the same final `100000 * rho` parameter box remains valid.
-/
def NonessentialTargetTubeParameterClusterBaseFiveStatement : Prop :=
  NonessentialTubeAxisAlignmentStatement →
    ∀ (rho : ℝ), 0 < rho → rho ≤ 1 / 1000 →
      ∀ A B : Kakeya.DeltaTube rho,
        (1 / 2 : ℝ) ≤ |A.direction (2 : Fin 3)| →
        (1 / 2 : ℝ) ≤ |B.direction (2 : Fin 3)| →
        ‖A.base‖ ≤ 5 → ‖B.base‖ ≤ 5 →
        ¬A.EssentiallyDistinct B →
          |(tubeParamsOfTube A).a - (tubeParamsOfTube B).a| ≤
              100000 * rho ∧
            |(tubeParamsOfTube A).b - (tubeParamsOfTube B).b| ≤
              100000 * rho ∧
            |(tubeParamsOfTube A).c - (tubeParamsOfTube B).c| ≤
              100000 * rho ∧
            |(tubeParamsOfTube A).d - (tubeParamsOfTube B).d| ≤
              100000 * rho

/--
Quantitative inverse of the exact four-parameter anisotropic transport.

The singular factor `m * (d-c)^2` is explicit.  The midpoint lies in the
normalized source window, and the shear value there is bounded; these are the
precise hypotheses needed to recover all four source line parameters from a
target parameter box.
-/
def AnisotropicTubeParamsInverseClusterStatement : Prop :=
  ∀ (g : SlopeFunction) (c d m r : ℝ),
    c < d → d - c ≤ 1 →
    Set.Icc c d ⊆ Set.Icc (-1 : ℝ) 1 →
    0 < m → m ≤ 1 →
    |g (c + (d - c) / 2)| ≤ 1 →
    0 ≤ r →
    ∀ p q : TubeParams,
      |(anisotropicTubeParams g c d m p).a -
          (anisotropicTubeParams g c d m q).a| ≤ r →
      |(anisotropicTubeParams g c d m p).b -
          (anisotropicTubeParams g c d m q).b| ≤ r →
      |(anisotropicTubeParams g c d m p).c -
          (anisotropicTubeParams g c d m q).c| ≤ r →
      |(anisotropicTubeParams g c d m p).d -
          (anisotropicTubeParams g c d m q).d| ≤ r →
        |p.a - q.a| ≤ 100 * r / (m * (d - c) ^ 2) ∧
          |p.b - q.b| ≤ 100 * r / (m * (d - c) ^ 2) ∧
          |p.c - q.c| ≤ 100 * r / (m * (d - c) ^ 2) ∧
          |p.d - q.d| ≤ 100 * r / (m * (d - c) ^ 2)

/--
Transport indexed four-parameter Frostman non-concentration from the source
family to a cleaned anisotropic target.

The exact coaxial identity pulls a target parameter box of radius `r` back to
a source box of radius `A r`, where `A = 100 / (m (d-c)^2)`.
`sourceFiberCap` contributes the factor three, and the explicit cardinality
loss converts source normalization to target normalization.  When `A r > 1`,
the separate `A^2` term absorbs the trivial target count.
-/
def CleanedTargetParameterFrostmanFromSourceStatement : Prop :=
  AnisotropicTubeParamsInverseClusterStatement →
    ∀ {delta rho c d m : ℝ},
      c < d → d - c ≤ 1 →
      Set.Icc c d ⊆ Set.Icc (-1 : ℝ) 1 →
      0 < m → m ≤ 1 →
      ∀ g : SlopeFunction,
        |g (c + (d - c) / 2)| ≤ 1 →
        0 < rho →
        ∀ F : Kakeya.Streamlined.TubeFamily delta,
          ∀ Y : Kakeya.Streamlined.TubeShading F,
            ∀ sourceConstant : ENNReal,
              TubeParameterFrostmanBound F sourceConstant →
              ∀ cleaned :
                  CleanedAnisotropicTarget
                    (rho := rho) (c := c) (d := d) (m := m)
                    F Y g,
                ∀ cardinalityLoss : ENNReal,
                  F.enncard ≤
                    cardinalityLoss * cleaned.family.enncard →
                  delta ≤
                    100 * rho / (m * (d - c) ^ 2) →
                  let A : ℝ := 100 / (m * (d - c) ^ 2)
                  TubeParameterFrostmanBound cleaned.family
                    (Kakeya.realRpowENN A 2 +
                      3 * sourceConstant *
                        Kakeya.realRpowENN A 2 *
                          cardinalityLoss)

/--
Absorb the exact source-to-target parameter-Frostman constant into the
Section 7 normalization `rho^(-eta)`.

This is the small-scale arithmetic companion to the raw transport statement.
It uses the same source-cardinality and cleanup-loss bookkeeping as the
cleaned Tube-Wolff normalization, but concludes the indexed parameter bound
needed to iterate the positive-window one-scale theorem.
-/
def CleanedTargetParameterFrostmanAbsorptionStatement : Prop :=
  CleanedTargetCardinalityProductStatement →
    CleanedTargetCardinalityLossStatement →
      CleanedTargetParameterFrostmanFromSourceStatement →
        CleanedAnisotropicMassLossAbsorptionStatement →
          AnisotropicTubeParamsInverseClusterStatement →
            ∀ eta theta : ℝ,
              0 < eta → eta < 1 →
              0 < theta → theta ≤ eta / 100 →
                ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
                  ∀ {delta rho c d m : ℝ},
                    0 < delta → delta ≤ delta₀ →
                    c < d → d - c ≤ 1 / 25 →
                    Set.Icc c d ⊆ Set.Icc (-1 : ℝ) 1 →
                    rho = 2 * delta / (d - c) →
                    0 < rho → rho ≤ 1 / 10000 →
                    0 < m → 50 * (d - c) ≤ m → m ≤ 1 →
                    Real.rpow delta (eta / 100) ≤
                      50 * (d - c) →
                    ∀ F : Kakeya.Streamlined.TubeFamily delta,
                      ∀ Y : Kakeya.Streamlined.TubeShading F,
                        ∀ g : SlopeFunction, g.IsNormalized →
                          ∀ C : ENNReal,
                            C ≤
                              Kakeya.realRpowENN
                                delta (-(theta / 1000)) →
                            HasExtremalCardinalityUpper
                              F (theta / 1000) →
                            Kakeya.realRpowENN delta theta *
                                ENNReal.ofReal (d - c) ≤
                              shadedMassInSlab Y c d →
                            ∀ cleaned :
                                CleanedAnisotropicTarget
                                  (rho := rho) (c := c)
                                  (d := d) (m := m) F Y g,
                              CleanedAnisotropicSourceData C cleaned →
                              TubeParameterFrostmanBound cleaned.family
                                (Kakeya.realRpowENN rho (-eta))

/--
Upgrade the source-normalized common-container count to a genuine all-scale
Tube-Wolff bound for the cleaned target family.

The small-scale range uses exact coaxial parameter transport and source
parameter Frostman.  At scales above `1/10000`, the trivial total-cardinality
bound supplies the explicit constant `100000000`.  The remaining
source-to-target cardinality loss is an honest input to be discharged from
the cleaned mass refinement.
-/
def CleanedTargetTubeWolffFromSourceStatement : Prop :=
  CommonContainerTargetTubeParameterClusterStatement →
    AnisotropicTubeParamsInverseClusterStatement →
      ∀ {delta rho c d m : ℝ},
        c < d → d - c ≤ 1 →
        Set.Icc c d ⊆ Set.Icc (-1 : ℝ) 1 →
        0 < m → m ≤ 1 →
        ∀ g : SlopeFunction,
          |g (c + (d - c) / 2)| ≤ 1 →
          0 < rho → rho ≤ 1 / 10000 →
          ∀ F : Kakeya.Streamlined.TubeFamily delta,
            ∀ Y : Kakeya.Streamlined.TubeShading F,
              ∀ sourceConstant : ENNReal,
                TubeParameterFrostmanBound F sourceConstant →
                ∀ cleaned :
                    CleanedAnisotropicTarget
                      (rho := rho) (c := c) (d := d) (m := m)
                      F Y g,
                  ∀ cardinalityLoss : ENNReal,
                    F.enncard ≤
                      cardinalityLoss * cleaned.family.enncard →
                    delta ≤
                      100 * (100000 * rho) /
                        (m * (d - c) ^ 2) →
                    TubeWolffBound cleaned.family
                      (100000000 +
                        Kakeya.realRpowENN
                          (100 * 100000 /
                            (m * (d - c) ^ 2)) 2 +
                        3 * sourceConstant *
                          Kakeya.realRpowENN
                            (100 * 100000 /
                              (m * (d - c) ^ 2)) 2 *
                            cardinalityLoss)

/--
Absorb every explicit source-to-target loss in the raw cleaned Tube-Wolff
constant.

The three geometric predecessors remain ordinary hypotheses.  This statement
only combines their exact constants with the mild-length regime and the strong
source `theta / 1000` bounds to obtain the Section 7 normalization
`rho^(-eta)`.
-/
def CleanedTargetTubeWolffAbsorptionStatement : Prop :=
  CleanedTargetCardinalityProductStatement →
    CleanedTargetCardinalityLossStatement →
      CleanedTargetTubeWolffFromSourceStatement →
        CleanedAnisotropicMassLossAbsorptionStatement →
          CommonContainerTargetTubeParameterClusterStatement →
            AnisotropicTubeParamsInverseClusterStatement →
              ∀ eta theta : ℝ,
                0 < eta → eta < 1 →
                0 < theta → theta ≤ eta / 100 →
                  ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
                    ∀ {delta rho c d m : ℝ},
                      0 < delta → delta ≤ delta₀ →
                      c < d → d - c ≤ 1 / 25 →
                      Set.Icc c d ⊆ Set.Icc (-1 : ℝ) 1 →
                      rho = 2 * delta / (d - c) →
                      0 < rho → rho ≤ 1 / 10000 →
                      0 < m → 50 * (d - c) ≤ m → m ≤ 1 →
                      Real.rpow delta (eta / 100) ≤
                        50 * (d - c) →
                      ∀ F : Kakeya.Streamlined.TubeFamily delta,
                        ∀ Y : Kakeya.Streamlined.TubeShading F,
                          ∀ g : SlopeFunction, g.IsNormalized →
                            ∀ C : ENNReal,
                              C ≤
                                Kakeya.realRpowENN
                                  delta (-(theta / 1000)) →
                              HasExtremalCardinalityUpper
                                F (theta / 1000) →
                              Kakeya.realRpowENN delta theta *
                                  ENNReal.ofReal (d - c) ≤
                                shadedMassInSlab Y c d →
                              ∀ cleaned :
                                  CleanedAnisotropicTarget
                                    (rho := rho) (c := c)
                                    (d := d) (m := m) F Y g,
                                CleanedAnisotropicSourceData C cleaned →
                                TubeWolffBound cleaned.family
                                  (Kakeya.realRpowENN rho (-eta))

/--
Enlarge one selected representative to cover a tube assigned to it.

Axis alignment places the source axis within `2002δ` of the representative's
signed extended axis over parameters `[-1,2]`.  Three consecutive unit
segments therefore cover the full source carrier after thickening to
`3000δ`.
-/
def RepresentativeTubeThreeCoverStatement : Prop :=
  NonessentialTubeAxisAlignmentStatement →
    ∀ (delta : ℝ), 0 < delta → delta ≤ 1 / 3000 →
      ∀ T U : Kakeya.DeltaTube delta,
        ¬T.EssentiallyDistinct U →
          ∃ coarse : Kakeya.Streamlined.TubeFamily (3000 * delta),
            coarse.card = 3 ∧
            T.carrier ⊆ coarse.toBodyFamily.union ∧
            ∀ j : Fin coarse.card,
              |(coarse.tube j).direction (2 : Fin 3)| =
                |U.direction (2 : Fin 3)|

/--
Uniform family-level version of the representative enlargement.

For a fixed selected representative `U`, six consecutive coarse tubes cover
every source tube that is not essentially distinct from `U`: three segments
handle alignment with `U.direction`, and three handle the reversed
orientation.
-/
def RepresentativeTubeSixCoverStatement : Prop :=
  NonessentialTubeAxisAlignmentStatement →
    ∀ (delta : ℝ), 0 < delta → delta ≤ 1 / 3000 →
      ∀ U : Kakeya.DeltaTube delta,
        ∃ coarse : Kakeya.Streamlined.TubeFamily (3000 * delta),
          coarse.card = 6 ∧
          (∀ j : Fin coarse.card,
            |(coarse.tube j).direction (2 : Fin 3)| =
              |U.direction (2 : Fin 3)|) ∧
          (∀ j : Fin coarse.card,
            ‖(coarse.tube j).base‖ ≤ ‖U.base‖ + 1) ∧
          ∀ T : Kakeya.DeltaTube delta,
            ¬T.EssentiallyDistinct U →
              T.carrier ⊆ coarse.toBodyFamily.union

/--
Small-radius coaxial unit tubes with distinct consecutive axial positions are
essentially distinct in the repository's volume-half sense.

The borderline case `|s-t| = 1` consists of adjacent unit segments.  Their
carrier intersection is localized near the common endpoint, while one tube
contains several disjoint radius-`rho` balls along its axis.  The explicit
`rho ≤ 1/8` margin keeps this comparison quantitative.
-/
def CoaxialShiftedTubesEssentiallyDistinctStatement : Prop :=
  TubeVolumeScalingStatement →
    ∀ (rho : ℝ), 0 < rho → rho ≤ 1 / 8 →
      ∀ (base direction : Point3),
        ∀ hdir : ‖direction‖ = 1,
        ∀ s t : ℝ, 1 ≤ |s - t| →
          let T : Kakeya.DeltaTube rho :=
            ⟨base + s • direction, direction, hdir⟩
          let U : Kakeya.DeltaTube rho :=
            ⟨base + t • direction, direction, hdir⟩
          T.EssentiallyDistinct U

/--
Deduplicate the fixed representative enlargement to four consecutive coarse
tubes on one oriented axis.

The four segments cover representative-axis parameters `[-2,2]`, hence cover
both signs returned by the alignment lemma.  Their start parameters are
pairwise separated by at least one, so the coaxial shifted-tube lemma proves
the resulting indexed family is essentially distinct.
-/
def RepresentativeTubeFourCoverStatement : Prop :=
  NonessentialTubeAxisAlignmentStatement →
    CoaxialShiftedTubesEssentiallyDistinctStatement →
      TubeVolumeScalingStatement →
        ∀ (delta : ℝ), 0 < delta → 3000 * delta ≤ 1 / 8 →
          ∀ U : Kakeya.DeltaTube delta,
            ∃ coarse : Kakeya.Streamlined.TubeFamily (3000 * delta),
              coarse.card = 4 ∧
              coarse.IsEssentiallyDistinct ∧
              (∀ j : Fin coarse.card,
                |(coarse.tube j).direction (2 : Fin 3)| =
                  |U.direction (2 : Fin 3)|) ∧
              (∀ j : Fin coarse.card,
                ‖(coarse.tube j).base‖ ≤ ‖U.base‖ + 1) ∧
              ∀ T : Kakeya.DeltaTube delta,
                ¬T.EssentiallyDistinct U →
                  T.carrier ⊆ coarse.toBodyFamily.union

/--
Four-tube representative cover at a prescribed selected scale.

The scale `rho` may be any radius with `3000 * delta ≤ rho ≤ 1 / 8`, rather
than the single fixed radius `3000 * delta`.  Every coarse tube keeps the
representative's supporting line up to orientation, so indexed parameter
provenance remains available for the later cross-block cleanup.
-/
def RepresentativeTubeFourCoverAtScaleConclusion : Prop :=
  ∀ (delta rho : ℝ),
    0 < delta → 3000 * delta ≤ rho → rho ≤ 1 / 8 →
    ∀ U : Kakeya.DeltaTube delta,
      ∃ coarse : Kakeya.Streamlined.TubeFamily rho,
        ∃ envelope : Kakeya.Streamlined.Body,
          coarse.card = 4 ∧
          coarse.IsEssentiallyDistinct ∧
          (∀ j : Fin coarse.card,
            tubeAxisLine (coarse.tube j) = tubeAxisLine U) ∧
          (∀ j : Fin coarse.card,
            |(coarse.tube j).direction (2 : Fin 3)| =
              |U.direction (2 : Fin 3)|) ∧
          (∀ j : Fin coarse.card,
            ‖(coarse.tube j).base‖ ≤ ‖U.base‖ + 1) ∧
          envelope.carrier = coarse.toBodyFamily.union ∧
          envelope.IsMeasurable ∧
          envelope.IsConvex ∧
          envelope.HasDimensions rho rho 4 3 ∧
          ∀ T : Kakeya.DeltaTube delta,
            ¬T.EssentiallyDistinct U →
              T.carrier ⊆ envelope.carrier

/-- Produce the selected-scale four-cover conclusion from closed geometry. -/
def RepresentativeTubeFourCoverAtScaleStatement : Prop :=
  NonessentialTubeAxisAlignmentStatement →
    CoaxialShiftedTubesEssentiallyDistinctStatement →
      TubeVolumeScalingStatement →
        RepresentativeTubeFourCoverAtScaleConclusion

/--
Assemble maximal source representatives with one four-tube distinct block per
representative.

Distinctness is asserted inside each block only.  Different representative
blocks may still overlap after coarse enlargement; cross-block cleanup remains
a later finite selection step.
-/
def RepresentativeFourBlockCoverStatement : Prop :=
  NonessentialTubeAxisAlignmentStatement →
    CoaxialShiftedTubesEssentiallyDistinctStatement →
      TubeVolumeScalingStatement →
        MaximalEssentiallyDistinctSubfamilyStatement →
          RepresentativeTubeFourCoverStatement →
            ∀ (delta : ℝ), 0 < delta → 3000 * delta ≤ 1 / 8 →
          ∀ F : Kakeya.Streamlined.TubeFamily delta,
            ∃ selected : Finset (Fin F.card),
              ∃ parent : Fin F.card → Fin selected.card,
                ∃ block :
                    ∀ j : Fin selected.card,
                      Kakeya.Streamlined.TubeFamily (3000 * delta),
                  (∀ i ∈ selected, ∀ j ∈ selected, i ≠ j →
                    (F.tube i).EssentiallyDistinct (F.tube j)) ∧
                  (∀ i,
                    ¬(F.tube i).EssentiallyDistinct
                      (F.tube (selected.equivFin.symm (parent i)).1)) ∧
                  Function.Surjective parent ∧
                  (∀ j, (block j).card = 4) ∧
                  (∀ j, (block j).IsEssentiallyDistinct) ∧
                  (∀ j, ∀ k : Fin (block j).card,
                    |((block j).tube k).direction (2 : Fin 3)| =
                      |(F.tube
                        (selected.equivFin.symm j).1).direction
                          (2 : Fin 3)|) ∧
                  (∀ j, ∀ k : Fin (block j).card,
                    ‖((block j).tube k).base‖ ≤
                      ‖(F.tube
                        (selected.equivFin.symm j).1).base‖ + 1) ∧
                  ∀ i,
                    (F.tube i).carrier ⊆
                      (block (parent i)).toBodyFamily.union

/--
Family-level four-block cover at one prescribed selected scale.

Each source tube is assigned to a maximal representative and is covered by
the union of that representative's four same-line coarse tubes.  Distinctness
is only internal to each block; cross-block cleanup and the relation-valued
induced shading are separate downstream steps.
-/
def RepresentativeFourBlockCoverAtScaleConclusion : Prop :=
  ∀ (delta rho : ℝ),
    0 < delta → 3000 * delta ≤ rho → rho ≤ 1 / 8 →
    ∀ F : Kakeya.Streamlined.TubeFamily delta,
      ∃ selected : Finset (Fin F.card),
        ∃ parent : Fin F.card → Fin selected.card,
          ∃ block :
              ∀ j : Fin selected.card,
                Kakeya.Streamlined.TubeFamily rho,
            ∃ envelope :
                Fin selected.card → Kakeya.Streamlined.Body,
              (∀ i ∈ selected, ∀ j ∈ selected, i ≠ j →
                (F.tube i).EssentiallyDistinct (F.tube j)) ∧
              (∀ i,
                ¬(F.tube i).EssentiallyDistinct
                  (F.tube (selected.equivFin.symm (parent i)).1)) ∧
              Function.Surjective parent ∧
              (∀ j, (block j).card = 4) ∧
              (∀ j, (block j).IsEssentiallyDistinct) ∧
              (∀ j, ∀ k : Fin (block j).card,
                tubeAxisLine ((block j).tube k) =
                  tubeAxisLine
                    (F.tube (selected.equivFin.symm j).1)) ∧
              (∀ j, ∀ k : Fin (block j).card,
                |((block j).tube k).direction (2 : Fin 3)| =
                  |(F.tube
                    (selected.equivFin.symm j).1).direction
                      (2 : Fin 3)|) ∧
              (∀ j, ∀ k : Fin (block j).card,
                ‖((block j).tube k).base‖ ≤
                  ‖(F.tube
                    (selected.equivFin.symm j).1).base‖ + 1) ∧
              (∀ j,
                (envelope j).carrier =
                  (block j).toBodyFamily.union) ∧
              (∀ j, (envelope j).IsMeasurable) ∧
              (∀ j, (envelope j).IsConvex) ∧
              (∀ j, (envelope j).HasDimensions rho rho 4 3) ∧
              ∀ i,
                (F.tube i).carrier ⊆
                  (envelope (parent i)).carrier

/-- Assemble the direct family-level selected-scale block conclusion. -/
def RepresentativeFourBlockCoverAtScaleStatement : Prop :=
  TubeVolumeScalingStatement →
    MaximalEssentiallyDistinctSubfamilyStatement →
      RepresentativeTubeFourCoverAtScaleConclusion →
        RepresentativeFourBlockCoverAtScaleConclusion

/--
Weighted finite-graph cleanup for anisotropic rediscretization.

If every target tube conflicts with at most `D` other indexed tubes, one can
retain a pairwise essentially-distinct subfamily carrying at least a
`1 / (D + 1)` fraction of any finite ENNReal weight.  The geometric conflict
degree is deliberately an explicit input; it must be proved separately from
the affine-line provenance and the source non-concentration hypotheses.
-/
def WeightedEssentiallyDistinctSelectionStatement : Prop :=
  ∀ {rho : ℝ},
    ∀ F : Kakeya.Streamlined.TubeFamily rho,
      ∀ weight : Fin F.card → ENNReal,
        (∀ i, weight i ≠ ⊤) →
        ∀ D : ℕ,
          (∀ i,
            (Finset.univ.filter fun j =>
              j ≠ i ∧
                ¬(F.tube i).EssentiallyDistinct (F.tube j)).card ≤ D) →
          ∃ selected : Finset (Fin F.card),
            (∀ i ∈ selected, ∀ j ∈ selected, i ≠ j →
              (F.tube i).EssentiallyDistinct (F.tube j)) ∧
            (∑ i, weight i) ≤
              (D + 1 : ENNReal) * ∑ i ∈ selected, weight i

/--
Assemble maximal representative selection and the fixed six-tube enlargement
into one family-level block cover.

The output deliberately remains a block cover rather than a `TubeCover`: one
source tube is covered by the union of six tubes attached to its selected
representative, and need not lie in any one member of that block.  The
tube-volume input is used only to show that a selected representative fails
essential distinctness with itself, so the same six-cover statement also
covers representatives.
-/
def RepresentativeBlockCoverStatement : Prop :=
  TubeVolumeScalingStatement →
    MaximalEssentiallyDistinctSubfamilyStatement →
      RepresentativeTubeSixCoverStatement →
        ∀ (delta : ℝ), 0 < delta → delta ≤ 1 / 3000 →
          ∀ F : Kakeya.Streamlined.TubeFamily delta,
            ∃ selected : Finset (Fin F.card),
              ∃ parent : Fin F.card → Fin selected.card,
                ∃ block :
                    ∀ j : Fin selected.card,
                      Kakeya.Streamlined.TubeFamily (3000 * delta),
                  (∀ i ∈ selected, ∀ j ∈ selected, i ≠ j →
                    (F.tube i).EssentiallyDistinct (F.tube j)) ∧
                  (∀ i,
                    ¬(F.tube i).EssentiallyDistinct
                      (F.tube (selected.equivFin.symm (parent i)).1)) ∧
                  Function.Surjective parent ∧
                  (∀ j, (block j).card = 6) ∧
                  (∀ j, ∀ k : Fin (block j).card,
                    |((block j).tube k).direction (2 : Fin 3)| =
                      |(F.tube
                        (selected.equivFin.symm j).1).direction
                          (2 : Fin 3)|) ∧
                  (∀ j, ∀ k : Fin (block j).card,
                    ‖((block j).tube k).base‖ ≤
                      ‖(F.tube
                        (selected.equivFin.symm j).1).base‖ + 1) ∧
                  ∀ i,
                    (F.tube i).carrier ⊆
                      (block (parent i)).toBodyFamily.union

/--
Apply the indexed four-parameter Frostman condition to one coordinate box.
This is the paper-faithful cluster count: it preserves indexed multiplicity,
does not pass through the axial position forgotten by `tubeParams`, and loses
only `C w² #F`.
-/
def TubeParameterClusterFiberCapStatement : Prop :=
  ∀ (delta w : ℝ),
    delta ≤ w → w ≤ 1 →
    ∀ F : Kakeya.Streamlined.TubeFamily delta,
      ∀ C : ENNReal,
        TubeParameterFrostmanBound F C →
        ∀ indices : Finset (Fin F.card),
          ∀ reference : Fin F.card,
            (∀ i ∈ indices,
              |(tubeParams i).a - (tubeParams reference).a| ≤ w ∧
              |(tubeParams i).b - (tubeParams reference).b| ≤ w ∧
              |(tubeParams i).c - (tubeParams reference).c| ≤ w ∧
              |(tubeParams i).d - (tubeParams reference).d| ≤ w) →
            (indices.card : ENNReal) ≤
              C * Kakeya.realRpowENN w 2 * F.enncard

/--
Place a four-parameter source cluster inside one convex-prism candidate.

The source unit-ball assumption fixes the axial-position ambiguity that
invalidated the former coarse-`DeltaTube` cover.  Verticality controls the two
source slopes, and the constant `5` absorbs the tube thickness plus the four
parameter errors on `z ∈ [-1,1]`.
-/
def TubeParameterClusterPrismContainmentStatement : Prop :=
  ∀ (delta w : ℝ),
    0 < delta → delta ≤ w → 0 < w → w ≤ 1 →
    ∀ F : Kakeya.Streamlined.TubeFamily delta,
      F.IsInUnitBall →
      IsInVerticalChart F →
      ∀ indices : Finset (Fin F.card),
        ∀ reference : Fin F.card,
          (∀ i ∈ indices,
            |(tubeParams i).a - (tubeParams reference).a| ≤ w ∧
            |(tubeParams i).b - (tubeParams reference).b| ≤ w ∧
            |(tubeParams i).c - (tubeParams reference).c| ≤ w ∧
            |(tubeParams i).d - (tubeParams reference).d| ≤ w) →
          ∀ i ∈ indices,
            (F.tube i).carrier ⊆
              tubeParameterPrism (tubeParams reference) (5 * w)

/--
The parameter prism is convex and has the exact quadratic-volume scale needed
for four-parameter Frostman counting.  It is an affine shear of
`[-radius,radius]² × [-1,1]`.
-/
def TubeParameterPrismGeometryStatement : Prop :=
  ∀ params : TubeParams,
    ∀ radius : ℝ, 0 ≤ radius →
      Convex ℝ (tubeParameterPrism params radius) ∧
        MeasureTheory.volume (tubeParameterPrism params radius) ≤
          ENNReal.ofReal (8 * radius ^ 2)

/--
Choose one selected cinematic curve for every active tube.  Tubes assigned
to the same selected curve have their raw cinematic curves within `2w`, so
the lower Lipschitz estimate controls `(a,b,d)`; the common `c`-window
controls the fourth tube parameter.  The round constant `500` is larger than
`2 * (7500 / 33)`.
-/
def SelectedCurveAssignmentClusterStatement : Prop :=
  ∀ {delta w : ℝ},
    0 < w →
    ∀ F : Kakeya.Streamlined.TubeFamily delta,
      ∀ Z : Kakeya.Streamlined.TubeShading F,
        ∀ f : SlopeFunction, f.IsNonsingular → f 0 = 0 →
          ∀ c0 : ℝ,
            (∀ i, Z.carrier i ≠ ∅ →
              |(tubeParams i).c - c0| ≤ w / 2) →
            ∀ G : Kakeya.Cinematic.FiniteFunctionFamily,
              (∀ i, Z.carrier i ≠ ∅ →
                ∃ g ∈ G.carrier,
                  Kakeya.Cinematic.c2Distance
                    (slopeCurve f (tubeParams i).a
                      (tubeParams i).b (tubeParams i).d) g ≤ w) →
              ∃ assign : Fin F.card → Kakeya.Cinematic.C2Function,
                (∀ i, Z.carrier i ≠ ∅ →
                  assign i ∈ G.carrier ∧
                    Kakeya.Cinematic.c2Distance
                      (slopeCurve f (tubeParams i).a
                        (tubeParams i).b (tubeParams i).d)
                      (assign i) ≤ w) ∧
                ∀ i, Z.carrier i ≠ ∅ →
                  ∀ j, Z.carrier j ≠ ∅ →
                    assign i = assign j →
                      |(tubeParams i).a - (tubeParams j).a| ≤ 500 * w ∧
                      |(tubeParams i).b - (tubeParams j).b| ≤ 500 * w ∧
                      |(tubeParams i).c - (tubeParams j).c| ≤ 500 * w ∧
                      |(tubeParams i).d - (tubeParams j).d| ≤ 500 * w

/--
Combine the explicit selected-curve assignment with indexed four-parameter
Frostman non-concentration.  Every selected curve has at most
`C (500w)^2 #F` active tube preimages, with no global `F.card` loss.
-/
def SelectedCurveAssignmentFiberCapStatement : Prop :=
  TubeParameterClusterFiberCapStatement →
    SelectedCurveAssignmentClusterStatement →
      ∀ (delta w : ℝ),
        0 < delta → delta ≤ 500 * w →
        0 < w → 500 * w ≤ 1 →
        ∀ F : Kakeya.Streamlined.TubeFamily delta,
          ∀ C : ENNReal,
            TubeParameterFrostmanBound F C →
            ∀ Z : Kakeya.Streamlined.TubeShading F,
              ∀ f : SlopeFunction, f.IsNonsingular → f 0 = 0 →
                ∀ c0 : ℝ,
                  (∀ i, Z.carrier i ≠ ∅ →
                    |(tubeParams i).c - c0| ≤ w / 2) →
                  ∀ G : Kakeya.Cinematic.FiniteFunctionFamily,
                    (∀ i, Z.carrier i ≠ ∅ →
                      ∃ g ∈ G.carrier,
                        Kakeya.Cinematic.c2Distance
                          (slopeCurve f (tubeParams i).a
                            (tubeParams i).b (tubeParams i).d) g ≤ w) →
                    ∃ assign : Fin F.card → Kakeya.Cinematic.C2Function,
                      (∀ i, Z.carrier i ≠ ∅ →
                        assign i ∈ G.carrier ∧
                          Kakeya.Cinematic.c2Distance
                            (slopeCurve f (tubeParams i).a
                              (tubeParams i).b (tubeParams i).d)
                            (assign i) ≤ w) ∧
                      ∀ g ∈ G.toFinset,
                        ((Finset.univ.filter fun i : Fin F.card =>
                          Z.carrier i ≠ ∅ ∧ assign i = g).card : ENNReal) ≤
                            C * Kakeya.realRpowENN (500 * w) 2 * F.enncard

/--
Geometric containment needed by the multiplicity transfer.  On the positive
half-window, subtracting the common `c₀ z` drift sends each active tube's
twisted projection into a controlled neighborhood of its assigned cinematic
curve.  The radius includes tube thickness, the `c`-window error, and the
selected-curve covering error.
-/
def AssignedCurveProjectionContainmentStatement : Prop :=
  ∀ {delta w : ℝ},
    0 < delta → delta ≤ 1 →
    0 < w →
    ∀ F : Kakeya.Streamlined.TubeFamily delta,
      HasBoundedBase F 4 →
      IsInVerticalChart F →
      ∀ Z : Kakeya.Streamlined.TubeShading F,
        Z.union ⊆ horizontalSlab 0 1 →
        ∀ f : SlopeFunction, f.IsNonsingular → f 0 = 0 →
          ∀ c0 : ℝ,
            ∀ assign : Fin F.card → Kakeya.Cinematic.C2Function,
              (∀ i, Z.carrier i ≠ ∅ →
                |(tubeParams i).c - c0| ≤ w / 2 ∧
                  Kakeya.Cinematic.c2Distance
                    (slopeCurve f (tubeParams i).a
                      (tubeParams i).b (tubeParams i).d)
                    (assign i) ≤ w) →
              ∀ i, Z.carrier i ≠ ∅ →
                cinematicShear c0 ''
                    (twistedProjection f '' Z.carrier i) ⊆
                  Kakeya.Cinematic.graphNeighborhood
                    (assign i) (20 * (delta + w))

/--
Basepoint-free form of the assigned-curve containment.

The proof only compares a point in a tube carrier with the point on the same
supporting line at the same height.  The vertical chart controls that
comparison; no bound on the stored segment basepoint or on the absolute line
parameters is used.
-/
def AssignedCurveProjectionContainmentFromVerticalChartStatement : Prop :=
  ∀ {delta w : ℝ},
    0 < delta → delta ≤ 1 →
    0 < w →
    ∀ F : Kakeya.Streamlined.TubeFamily delta,
      IsInVerticalChart F →
      ∀ Z : Kakeya.Streamlined.TubeShading F,
        Z.union ⊆ horizontalSlab 0 1 →
        ∀ f : SlopeFunction, f.IsNonsingular → f 0 = 0 →
          ∀ c0 : ℝ,
            ∀ assign : Fin F.card → Kakeya.Cinematic.C2Function,
              (∀ i, Z.carrier i ≠ ∅ →
                |(tubeParams i).c - c0| ≤ w / 2 ∧
                  Kakeya.Cinematic.c2Distance
                    (slopeCurve f (tubeParams i).a
                      (tubeParams i).b (tubeParams i).d)
                    (assign i) ≤ w) →
              ∀ i, Z.carrier i ≠ ∅ →
                cinematicShear c0 ''
                    (twistedProjection f '' Z.carrier i) ⊆
                  Kakeya.Cinematic.graphNeighborhood
                    (assign i) (20 * (delta + w))

/--
Inner-regularize a finite shading before applying Hölder to its projected
multiplicity.  Every retained carrier is compact, so its continuous twisted
image is compact and measurable.  At least half of the aggregate shaded mass
is retained.
-/
def CompactSubshadingSelectionStatement : Prop :=
  ∀ {delta : ℝ},
    ∀ F : Kakeya.Streamlined.TubeFamily delta,
      ∀ Y : Kakeya.Streamlined.TubeShading F,
        ∃ Z : Kakeya.Streamlined.TubeShading F,
          IsSubshading Z Y ∧
            (1 / 2 : ENNReal) * Y.mass ≤ Z.mass ∧
            ∀ i, IsCompact (Z.carrier i)

/--
Projection area lower bound for one compact shaded tube.  The vertical-chart
condition controls axial displacement at fixed height, so each horizontal
`y`-fiber has diameter `O(delta)`.  Compactness makes the twisted image
measurable; the explicit factor `20 * delta` safely contains the exact
coordinate losses.
-/
def CompactTubeTwistedProjectionAreaStatement : Prop :=
  ∀ {delta : ℝ},
    0 < delta →
    ∀ F : Kakeya.Streamlined.TubeFamily delta,
      IsInVerticalChart F →
      ∀ Z : Kakeya.Streamlined.TubeShading F,
        (∀ i, IsCompact (Z.carrier i)) →
        ∀ f : SlopeFunction,
          ∀ i,
            MeasurableSet (twistedProjection f '' Z.carrier i) ∧
              MeasureTheory.volume (Z.carrier i) ≤
                ENNReal.ofReal (20 * delta) *
                  MeasureTheory.volume
                    (twistedProjection f '' Z.carrier i)

/--
Select one vertical half-window carrying at least half of the shaded mass.
The sign `1` selects `[0,1]`; the sign `-1` selects `[-1,0]`.  The negative
case is transported to the cinematic domain by the separate reflected-slope
identity rather than silently assuming all shading already lies in `[0,1]`.
-/
def HalfWindowMassSelectionStatement : Prop :=
  ∀ {delta : ℝ},
    ∀ F : Kakeya.Streamlined.TubeFamily delta,
      ∀ Y : Kakeya.Streamlined.TubeShading F,
        IsInSlopeWindow Y →
          ∃ sign : ℝ, (sign = 1 ∨ sign = -1) ∧
            ∃ Z : Kakeya.Streamlined.TubeShading F,
              IsSubshading Z Y ∧
                (1 / 2 : ENNReal) * Y.mass ≤ Z.mass ∧
                Z.union ⊆
                  if sign = 1 then horizontalSlab 0 1
                  else horizontalSlab (-1) 0

/--
Exact negative-half-window normalization for the cinematic curve formula.
Reflection preserves nonsingularity and changes the curve parameters by
`(a,b,d,z) ↦ (a,b,-d,-z)`.
-/
def ReflectedSlopeCinematicStatement : Prop :=
  ∀ f : SlopeFunction,
    f.IsNonsingular →
      f.reflected.IsNonsingular ∧
        ∀ a b d z : ℝ,
          cinematicEval f a b d (-z) =
            cinematicEval f.reflected a b (-d) z

/--
Reflect a negative-half-window tube family and shading across `z = 0`.

The reflected family keeps the same scale, indexed parameter Frostman
constant, bounded-base radius, essential distinctness, and vertical chart.
Every reflected subshading can be pulled back to the original indexed family
without changing aggregate density or either twisted-projection volume in the
one-scale inequality.  This is an exact isometric transport, not a new
coarsening or a carrier-model implication.
-/
def Section7VerticalReflectionStatement : Prop :=
  ∀ {delta : ℝ},
    ∀ F : Kakeya.Streamlined.TubeFamily delta,
      ∀ Y : Kakeya.Streamlined.TubeShading F,
        ∃ reflectedFamily : Kakeya.Streamlined.TubeFamily delta,
          ∃ reflectedShading :
              Kakeya.Streamlined.TubeShading reflectedFamily,
            (F.Nonempty → reflectedFamily.Nonempty) ∧
            (∀ R : ℝ,
              HasBoundedBase F R →
                HasBoundedBase reflectedFamily R) ∧
            (F.IsEssentiallyDistinct →
              reflectedFamily.IsEssentiallyDistinct) ∧
            (IsInVerticalChart F →
              IsInVerticalChart reflectedFamily) ∧
            ((∀ i : Fin F.card,
              |(tubeParams i).a| ≤ 12 ∧
                |(tubeParams i).b| ≤ 12 ∧
                |(tubeParams i).c| ≤ 2 ∧
                |(tubeParams i).d| ≤ 2) →
              ∀ i : Fin reflectedFamily.card,
                |(tubeParams i).a| ≤ 12 ∧
                  |(tubeParams i).b| ≤ 12 ∧
                  |(tubeParams i).c| ≤ 2 ∧
                  |(tubeParams i).d| ≤ 2) ∧
            (∀ C : ENNReal,
              TubeParameterFrostmanBound F C →
                TubeParameterFrostmanBound reflectedFamily C) ∧
            (∀ lambda : ENNReal,
              Y.IsLambdaDense lambda →
                reflectedShading.IsLambdaDense lambda) ∧
            (Y.union ⊆ horizontalSlab (-1) 0 →
              reflectedShading.union ⊆ horizontalSlab 0 1) ∧
            ∀ W : Kakeya.Streamlined.TubeShading reflectedFamily,
              IsSubshading W reflectedShading →
                ∃ Z : Kakeya.Streamlined.TubeShading F,
                  IsSubshading Z Y ∧
                  (∀ lambda : ENNReal,
                    W.IsLambdaDense lambda →
                      Z.IsLambdaDense lambda) ∧
                  ∀ f : SlopeFunction,
                    MeasureTheory.volume
                        (twistedUnion W f.reflected) =
                      MeasureTheory.volume (twistedUnion Z f) ∧
                    ∀ r : ℝ,
                      MeasureTheory.volume
                          (Metric.cthickening r
                            (twistedUnion W f.reflected)) =
                        MeasureTheory.volume
                          (Metric.cthickening r (twistedUnion Z f))

/--
The intermediate scale-selection lemma from Section 7.  A dense shading has a
dense subshading whose twisted image controls its own `ρ`-neighborhood.
-/
def TwistedProjectionScaleStatement : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon → epsilon < 1 →
    ∃ eta delta₀ : ℝ,
      0 < eta ∧ eta ≤ epsilon ∧
      0 < delta₀ ∧ delta₀ < 1 ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
        ∀ F : Kakeya.Streamlined.TubeFamily delta,
          F.Nonempty → HasBoundedBase F 4 → F.IsEssentiallyDistinct →
          IsInVerticalChart F →
          TubeWolffBound F (Kakeya.realRpowENN delta (-eta)) →
          ∀ Y : Kakeya.Streamlined.TubeShading F,
            Y.IsLambdaDense (Kakeya.realRpowENN delta eta) →
            IsInSlopeWindow Y →
            ∀ f : SlopeFunction, f.IsNonsingular → f 0 = 0 →
              ∃ rho : ℝ,
                Real.rpow delta (1 - epsilon ^ 2) < rho ∧ rho < 1 ∧
                ∃ Z : Kakeya.Streamlined.TubeShading F,
                  IsSubshading Z Y ∧
                    Z.IsLambdaDense (Kakeya.realRpowENN delta (4 * eta)) ∧
                    MeasureTheory.volume (twistedUnion Z f) ≥
                      Kakeya.realRpowENN (delta / rho) epsilon *
                        MeasureTheory.volume
                          (Metric.cthickening rho (twistedUnion Z f))

/--
Geometric part of the paper's coarsening step.  The windowed exact induced
coarse shading has twisted image inside a fixed enlargement of the fine
twisted image.  The constant `16` follows from the normalized slope and the
bounded fine-tube basepoints.
-/
def TwistedProjectionInducedShadingStatement : Prop :=
  ∀ delta rho r : ℝ,
    0 < delta → delta ≤ 1 → 0 ≤ r →
    ∀ fine : Kakeya.Streamlined.TubeFamily delta,
      HasBoundedBase fine 4 →
      ∀ coarse : Kakeya.Streamlined.TubeFamily rho,
        ∀ P : Kakeya.Streamlined.TubeCover fine coarse,
          ∀ Y : Kakeya.Streamlined.TubeShading fine,
            IsInSlopeWindow Y →
            ∀ W : Kakeya.Streamlined.TubeShading coarse,
              IsWindowedExactInducedShading P Y W r →
              ∀ f : SlopeFunction, f.IsNonsingular → f 0 = 0 →
                twistedUnion W f ⊆
                  Metric.cthickening (16 * r) (twistedUnion Y f)

/--
Relation-valued version of the induced-shading projection geometry.

The relation may assign one fine index to several coarse block members, and
no single-parent `TubeCover` is fabricated.  This conclusion only uses the
fine indices actually appearing in the coarse shading.  Coverage of all fine
indices, density, distinctness, and non-concentration remain separate
selected-scale obligations.
-/
def TwistedProjectionRelationInducedShadingStatement : Prop :=
  ∀ delta rho r : ℝ,
    0 < delta → delta ≤ 1 → 0 ≤ r →
    ∀ fine : Kakeya.Streamlined.TubeFamily delta,
      HasBoundedBase fine 4 →
      ∀ coarse : Kakeya.Streamlined.TubeFamily rho,
        ∀ Rel : Fin fine.card → Fin coarse.card → Prop,
          ∀ Y : Kakeya.Streamlined.TubeShading fine,
            IsInSlopeWindow Y →
            ∀ W : Kakeya.Streamlined.TubeShading coarse,
              IsWindowedExactRelationInducedShading Rel Y W r →
              ∀ f : SlopeFunction, f.IsNonsingular → f 0 = 0 →
                twistedUnion W f ⊆
                  Metric.cthickening (16 * r) (twistedUnion Y f)

/--
Parameter-certificate version of the relation-induced projection geometry.

This is the boundary used after selected-scale block assembly.  The modeled
coarse family need not retain the original basepoint radius, but whole-line
provenance preserves the four vertical-chart line parameters.  Those
parameters bound the relevant fine shaded points and give the safe
twisted-projection enlargement `40r`.
-/
def TwistedProjectionRelationInducedShadingFromParametersStatement : Prop :=
  ∀ delta rho r : ℝ,
    0 < delta → delta ≤ 1 → 0 ≤ r →
    ∀ fine : Kakeya.Streamlined.TubeFamily delta,
      IsInVerticalChart fine →
      (∀ i : Fin fine.card,
        |(tubeParams i).a| ≤ 12 ∧ |(tubeParams i).b| ≤ 12 ∧
          |(tubeParams i).c| ≤ 2 ∧ |(tubeParams i).d| ≤ 2) →
      ∀ coarse : Kakeya.Streamlined.TubeFamily rho,
        ∀ Rel : Fin fine.card → Fin coarse.card → Prop,
          ∀ Y : Kakeya.Streamlined.TubeShading fine,
            IsInSlopeWindow Y →
            ∀ W : Kakeya.Streamlined.TubeShading coarse,
              IsWindowedExactRelationInducedShading Rel Y W r →
              ∀ f : SlopeFunction, f.IsNonsingular → f 0 = 0 →
                twistedUnion W f ⊆
                  Metric.cthickening (40 * r) (twistedUnion Y f)

/--
Indexed shaded-mass transfer through a relation-valued coarse cover.

Every fine shaded point is assigned to at least one related coarse shaded
piece.  If each coarse index is related to at most `K` fine indices, summing
the pointwise carrier cover loses exactly the factor `K`.  No disjointness or
division by a possibly zero mass is used.
-/
def RelationShadingMassBoundStatement : Prop :=
  ∀ {delta rho : ℝ},
    ∀ fine : Kakeya.Streamlined.TubeFamily delta,
      ∀ coarse : Kakeya.Streamlined.TubeFamily rho,
        ∀ Rel : Fin fine.card → Fin coarse.card → Prop,
          ∀ Y : Kakeya.Streamlined.TubeShading fine,
            ∀ W : Kakeya.Streamlined.TubeShading coarse,
              ∀ K : ℕ,
                (∀ i, ∀ p ∈ Y.carrier i,
                  ∃ j, Rel i j ∧ p ∈ W.carrier j) →
                (∀ j,
                  (Finset.univ.filter fun i : Fin fine.card =>
                    Rel i j).card ≤ K) →
                  Y.mass ≤ (K : ENNReal) * W.mass

/--
Planar volume doubling for the enlargement factor in the induced-shading
projection lemma.

A `35 × 35` grid of translates of an `r`-neighborhood covers the
`16r`-neighborhood.  The explicit constant is deliberately separated from
the Section 7 iteration so its fixed loss can be absorbed once per selected
scale.
-/
def PlanarThickeningSixteenVolumeStatement : Prop :=
  ∀ E : Set Point2, ∀ r : ℝ, 0 < r →
    MeasureTheory.volume (Metric.cthickening (16 * r) E) ≤
      (1225 : ENNReal) *
        MeasureTheory.volume (Metric.cthickening r E)

/--
Planar volume doubling for the parameter-certificate enlargement.

An `83 × 83` grid of translates of an `r`-neighborhood covers the
`40r`-neighborhood.  The factor `6889 = 83²` is kept explicit so the
selected-scale iteration pays and later absorbs the actual fixed loss.
-/
def PlanarThickeningFortyVolumeStatement : Prop :=
  ∀ E : Set Point2, ∀ r : ℝ, 0 < r →
    MeasureTheory.volume (Metric.cthickening (40 * r) E) ≤
      (6889 : ENNReal) *
        MeasureTheory.volume (Metric.cthickening r E)

/--
Boundary-cap volume for a vertical-chart tube.

When an exact induced shading is generated from source points in `z ∈ [0,1]`,
its part outside the iteration window `[-1,1]` can only occur in the top slab
`[1,1+rho]`.  A radius-`rho` tube crosses that slab in volume `O(rho³)`.
The round constant is kept explicit for the later additive-loss absorption.
-/
def VerticalTubeTopBoundaryVolumeStatement : Prop :=
  ∀ rho : ℝ, 0 < rho → rho ≤ 1 / 8 →
    ∀ T : Kakeya.DeltaTube rho,
      (1 / 2 : ℝ) ≤ |T.direction (2 : Fin 3)| →
        MeasureTheory.volume
            (T.carrier ∩ horizontalSlab 1 (1 + rho)) ≤
          ENNReal.ofReal (100 * rho ^ 3)

/--
The strengthened twisted-projection estimate of Section 7, with Tube Wolff
non-concentration as its geometric input.
-/
def TwistedProjectionEstimateStatement : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon →
    ∃ eta delta₀ : ℝ,
      0 < eta ∧ eta ≤ epsilon ∧
      0 < delta₀ ∧ delta₀ < 1 ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
        ∀ F : Kakeya.Streamlined.TubeFamily delta,
          F.Nonempty → HasBoundedBase F 4 → F.IsEssentiallyDistinct →
          IsInVerticalChart F →
          TubeWolffBound F (Kakeya.realRpowENN delta (-eta)) →
          ∀ Y : Kakeya.Streamlined.TubeShading F,
            Y.IsLambdaDense (Kakeya.realRpowENN delta eta) →
            IsInSlopeWindow Y →
            ∀ f : SlopeFunction, f.IsNonsingular → f 0 = 0 →
              MeasureTheory.volume (twistedUnion Y f) ≥
                Kakeya.realRpowENN delta epsilon

/--
The Section 7 lower bound in the faithful line-parameter model.

WZ Lemma 8 already exports both the carrier-based Tube-Wolff bound and the
indexed four-parameter Frostman bound.  The active Section 7 route consumes
the latter explicitly rather than inferring it from the former.
-/
def TwistedProjectionParameterFrostmanEstimateStatement : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon →
    ∃ eta delta₀ : ℝ,
      0 < eta ∧ eta ≤ epsilon ∧
      0 < delta₀ ∧ delta₀ < 1 ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
        ∀ F : Kakeya.Streamlined.TubeFamily delta,
          F.Nonempty → HasBoundedBase F 4 → F.IsEssentiallyDistinct →
          IsInVerticalChart F →
          TubeWolffBound F (Kakeya.realRpowENN delta (-eta)) →
          TubeParameterFrostmanBound F
            (Kakeya.realRpowENN delta (-eta)) →
          HasExtremalCardinalityUpper F (eta / 10) →
          ∀ Y : Kakeya.Streamlined.TubeShading F,
            Y.IsLambdaDense (Kakeya.realRpowENN delta eta) →
            IsInSlopeWindow Y →
            ∀ f : SlopeFunction, f.IsNonsingular → f 0 = 0 →
              MeasureTheory.volume (twistedUnion Y f) ≥
                Kakeya.realRpowENN delta epsilon

/--
All WZ1-derived structure and the WZ2 large-slope modification, packaged as
the small-twisted-projection counterexample produced by failure of Theorem
5.2.
-/
def SmallTwistedProjectionFromFailureStatement : Prop :=
  ¬Kakeya.Streamlined.StickyInput →
    ∃ sigma : ℝ, 0 < sigma ∧ sigma < 1 ∧
      ∀ eta delta₀ : ℝ,
        0 < eta → eta < sigma → 0 < delta₀ →
        ∃ delta : ℝ, 0 < delta ∧ delta ≤ delta₀ ∧ delta < 1 ∧
          ∃ F : Kakeya.Streamlined.TubeFamily delta,
            F.Nonempty ∧ HasBoundedBase F 4 ∧ F.IsEssentiallyDistinct ∧
            IsInVerticalChart F ∧
            TubeWolffBound F (Kakeya.realRpowENN delta (-eta)) ∧
            TubeParameterFrostmanBound F
              (Kakeya.realRpowENN delta (-eta)) ∧
            HasExtremalCardinalityUpper F (eta / 10) ∧
            ∃ Y : Kakeya.Streamlined.TubeShading F,
              Y.IsLambdaDense (Kakeya.realRpowENN delta eta) ∧
              IsInSlopeWindow Y ∧
              ∃ f : SlopeFunction, f.IsNonsingular ∧ f 0 = 0 ∧
                MeasureTheory.volume (twistedUnion Y f) ≤
                  Kakeya.realRpowENN delta (sigma - eta)

/--
Final short contradiction: the small-projection counterexample and the
twisted-projection lower bound imply the WZ2 sticky input consumed by GWZ.
-/
def StickyFromTwistedProjectionStatement : Prop :=
  SmallTwistedProjectionFromFailureStatement →
    TwistedProjectionEstimateStatement →
      Kakeya.Streamlined.StickyInput

/-- Final contradiction using the faithful parameter-Frostman Section 7 input. -/
def StickyFromParameterFrostmanProjectionStatement : Prop :=
  SmallTwistedProjectionFromFailureStatement →
    TwistedProjectionParameterFrostmanEstimateStatement →
      Kakeya.Streamlined.StickyInput

end Kakeya.Assouad
