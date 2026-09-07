import MyLeanRepo.Kakeya.Assouad.CriticalInputs
import MyLeanRepo.Kakeya.Hairbrush.Basic

/-!
# Frozen statements for the shaded Wolff hairbrush

These declarations split Wang--Zahl 2025, Proposition 1.8 / Appendix B into
three substantive leaves and two assembly gates.

The route is deliberately different from the historical monolithic WIP:

* no unconditional per-cluster square-root estimate is assumed;
* the broadness constant is encoded in the exact power-law predicate;
* aggregate density is converted to per-tube density before the Wolff
  low/high multiplicity dichotomy;
* the weak Frostman slab condition is used through a balanced scale
  decomposition, as in Appendix B.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Assouad

/-- Acute angle between two unit direction vectors. -/
def hairbrushAcuteDirectionAngle (v w : Point3) : ℝ :=
  min (Real.arccos (inner ℝ v w))
    (Real.pi - Real.arccos (inner ℝ v w))

/-- Acute angle between two tube directions. -/
def hairbrushAcuteAngle {δ : ℝ}
    (T U : Kakeya.DeltaTube δ) : ℝ :=
  hairbrushAcuteDirectionAngle T.direction U.direction

/-- Every retained tube carries the prescribed fraction of its own volume. -/
def HairbrushPerTubeDense {δ : ℝ}
    {F : Kakeya.TubeFamily δ} (Y : Kakeya.Shading F)
    (lambda : ENNReal) : Prop :=
  ∀ T ∈ F, lambda * T.volume ≤ volume (Y.carrier T)

/--
Distinct intersecting tubes have angular separation at least the tube
thickness. This is Wolff 1995, condition (15).
-/
def HairbrushAngleSeparated {δ : ℝ}
    (F : Kakeya.TubeFamily δ) : Prop :=
  ∀ T ∈ F, ∀ U ∈ F, T ≠ U →
    T.carrier ∩ U.carrier ≠ ∅ →
      δ ≤ hairbrushAcuteAngle T U

/-- The whole fiber lies in one projective direction cap of radius `theta`. -/
def HairbrushAngularlyConfined {δ : ℝ}
    (F : Kakeya.TubeFamily δ) (theta : ℝ) : Prop :=
  ∃ v : Point3, ‖v‖ = 1 ∧
    ∀ T ∈ F,
      hairbrushAcuteDirectionAngle T.direction v ≤ theta

/--
Exact two-broadness at a pointwise scale comparable to the selected common
scale `theta`.

At each retained shaded point, the max-score broad-subset argument produces
its own exact optimizing radius `thetaLocal`. Dyadic pigeonholing only makes
these radii comparable, so the frozen API records
`theta / 2 ≤ thetaLocal ≤ theta` rather than incorrectly forcing every
optimizer to equal one common radius.

The coefficient remains exactly `1`: fixed dyadic comparability losses are
carried by `thetaLocal`, not by an unconstrained `C_broad` field.
-/
def IsTwoBroadAtScale {δ : ℝ}
    {F : Kakeya.TubeFamily δ} (Y : Kakeya.Shading F)
    (theta eta : ℝ) : Prop :=
  ∀ x ∈ Y.union,
    ∃ thetaLocal : ℝ,
      δ ≤ thetaLocal ∧
      theta / 2 ≤ thetaLocal ∧
      thetaLocal ≤ theta ∧
      ∀ w : Point3, ‖w‖ = 1 →
        ∀ r : ℝ, δ ≤ r → r ≤ thetaLocal →
          let through : Kakeya.TubeFamily δ := by
            classical
            exact F.filter fun T => x ∈ Y.carrier T
          let near : Kakeya.TubeFamily δ := by
            classical
            exact through.filter fun T =>
              hairbrushAcuteDirectionAngle T.direction w ≤ r
          (near.card : ℝ) ≤
            Real.rpow (r / thetaLocal) eta * (through.card : ℝ)

/--
Output of aggregate-density pruning and the angle-separated refinement.
-/
structure HairbrushPreparedData {δ : ℝ}
    (F : Kakeya.TubeFamily δ) (Y : Kakeya.Shading F)
    (eta : ℝ) where
  family : Kakeya.TubeFamily δ
  family_subset : family ⊆ F
  shading : Kakeya.Shading family
  shading_subset :
    ∀ T, ∀ hT : T ∈ family,
      shading.carrier T ⊆ Y.carrier T
  nonempty : family.Nonempty
  in_unit_ball : family.IsInUnitBall
  essentially_distinct : family.IsEssentiallyDistinct
  union_subset : shading.union ⊆ Y.union
  card_retention :
    Kakeya.realRpowENN δ eta * F.enncard ≤ family.enncard
  per_tube_dense :
    HairbrushPerTubeDense shading (Kakeya.realRpowENN δ eta)
  angle_separated : HairbrushAngleSeparated family
  katz_tao :
    Kakeya.KatzTaoConvexWolffBound family
      (Real.rpow δ (-eta))
  frostman_slab :
    Kakeya.FrostmanSlabWolffBound family
      (Real.rpow δ (-eta))

/--
Preprocess an Assertion-D configuration into the faithful input of Wolff's
low/high multiplicity argument.
-/
def HairbrushPreprocessingStatement : Prop :=
  ∀ outputEta : ℝ, 0 < outputEta →
    ∃ inputEta delta₀ : ℝ,
      0 < inputEta ∧ 0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
        ∀ F : Kakeya.TubeFamily delta,
          F.Nonempty →
          F.IsInUnitBall →
          F.IsEssentiallyDistinct →
          ∀ Y : Kakeya.Shading F,
            Y.IsLambdaDense
                (Kakeya.realRpowENN delta inputEta) →
            Kakeya.KatzTaoConvexWolffBound F
                (Real.rpow delta (-inputEta)) →
            Kakeya.FrostmanSlabWolffBound F
                (Real.rpow delta (-inputEta)) →
              Nonempty (HairbrushPreparedData F Y outputEta)

/--
Balanced broad decomposition at one scale.

The displayed inequalities are the exact properties used in Appendix B:
balanced fiber cardinality, pairwise-additive shaded volume, a Frostman lower
bound on the number of coarse fibers, per-fiber fullness, and exact
two-broadness after normalization to scale `theta`.
-/
structure HairbrushScaleDecomposition {δ : ℝ}
    {F : Kakeya.TubeFamily δ} (Y : Kakeya.Shading F)
    (eta : ℝ) where
  theta : ℝ
  delta_le_theta : δ ≤ theta
  theta_le_one : theta ≤ 1
  theta_pos : 0 < theta
  fiberCount : ℕ
  fiberCount_pos : 0 < fiberCount
  fiber : Fin fiberCount → Kakeya.TubeFamily δ
  shading : ∀ j, Kakeya.Shading (fiber j)
  fiber_nonempty : ∀ j, (fiber j).Nonempty
  fiber_subset : ∀ j, fiber j ⊆ F
  fiber_disjoint :
    ∀ j k, j ≠ k → Disjoint (fiber j) (fiber k)
  shading_subset :
    ∀ j T, ∀ hT : T ∈ fiber j,
      (shading j).carrier T ⊆ Y.carrier T
  fiber_in_unit_ball : ∀ j, (fiber j).IsInUnitBall
  fiber_essentially_distinct :
    ∀ j, (fiber j).IsEssentiallyDistinct
  fiber_angle_separated :
    ∀ j, HairbrushAngleSeparated (fiber j)
  fiber_per_tube_dense :
    ∀ j, HairbrushPerTubeDense (shading j)
      (Kakeya.realRpowENN δ eta)
  fiber_katz_tao :
    ∀ j, Kakeya.KatzTaoConvexWolffBound (fiber j)
      (Real.rpow δ (-eta))
  fiber_angular_confinement :
    ∀ j, HairbrushAngularlyConfined (fiber j) theta
  fiber_two_broad :
    ∀ j, IsTwoBroadAtScale (shading j) theta eta
  retained_cardinality :
    Kakeya.realRpowENN δ eta * F.enncard ≤
      ∑ j, (fiber j).enncard
  balanced :
    ∀ j,
      Kakeya.realRpowENN δ eta * F.enncard ≤
        (fiberCount : ENNReal) * (fiber j).enncard
  coarse_count_lower :
    Kakeya.realRpowENN δ eta ≤
      ENNReal.ofReal theta * (fiberCount : ENNReal)
  shaded_volume_additive :
    ∑ j, volume (shading j).union ≤ volume Y.union

/--
The single-scale angular decomposition used in Wang--Zahl 2025 Appendix B.

This is the minimal output of the standard reduction preceding the Wolff
hairbrush estimate: one common angular scale, balanced fibers, additive shaded
volume, per-fiber density, and relative two-broadness.  It deliberately omits
the outer scale, nested parents, low-scale alternative, and multiplicity
product from Wang--Zahl Section 7.
-/
def HairbrushSingleScaleDecompositionStatement : Prop :=
  ∀ outputEta : ℝ, 0 < outputEta →
    ∃ inputEta delta₀ : ℝ,
      0 < inputEta ∧ 0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
        ∀ F : Kakeya.TubeFamily delta,
          ∀ Y : Kakeya.Shading F,
            ∀ P : HairbrushPreparedData F Y inputEta,
              Nonempty
                (HairbrushScaleDecomposition
                  P.shading outputEta)

/--
The paper-faithful Wang--Zahl Section 7 dichotomy.

For parameters `omega,zeta`, the broadness exponent is
`beta = omega*zeta/100`.  Either the retained prepared shading already has
large union, with loss `omega/2`, or it admits the balanced broad
decomposition consumed by Appendix B.
-/
def HairbrushBroadScaleDichotomyStatement : Prop :=
  ∀ omega zeta : ℝ,
    0 < omega →
    0 < zeta → zeta ≤ 1 →
      ∃ inputEta delta₀ : ℝ,
        0 < inputEta ∧ 0 < delta₀ ∧ delta₀ ≤ 1 ∧
        ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
          ∀ F : Kakeya.TubeFamily delta,
            ∀ Y : Kakeya.Shading F,
              ∀ P : HairbrushPreparedData F Y inputEta,
                Kakeya.realRpowENN delta (omega / 2) *
                      P.shading.mass ≤
                    volume P.shading.union ∨
                  Nonempty
                    (HairbrushScaleDecomposition
                      P.shading (omega * zeta / 100))

/--
The literal original-coordinate fiber estimate in Appendix B.

The historical unconditional per-cluster square-root API is not used.
Pointwise exact two-broadness at scales comparable to `theta` is an explicit
hypothesis.
-/
def HairbrushTwoBroadFiberEstimateStatement : Prop :=
  ∀ loss : ℝ, 0 < loss →
    ∃ eta delta₀ : ℝ,
      0 < eta ∧ eta ≤ loss / 2 ∧
      0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ delta theta : ℝ,
        0 < delta → delta ≤ delta₀ →
        delta ≤ theta → theta ≤ 1 →
        ∀ F : Kakeya.TubeFamily delta,
          F.Nonempty →
          F.IsInUnitBall →
          F.IsEssentiallyDistinct →
          HairbrushAngleSeparated F →
          HairbrushAngularlyConfined F theta →
          ∀ Y : Kakeya.Shading F,
            HairbrushPerTubeDense Y
                (Kakeya.realRpowENN delta eta) →
            Kakeya.KatzTaoConvexWolffBound F
                (Real.rpow delta (-eta)) →
            IsTwoBroadAtScale Y theta eta →
              Kakeya.realRpowENN delta (3 / 2 + loss) *
                  ENNReal.ofReal (Real.sqrt theta) *
                  ENNReal.rpow F.enncard (1 / 2) ≤
                volume Y.union

/-- The expanded volume estimate stated at the start of Appendix B. -/
def HairbrushExpandedEstimate : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon →
    ∃ kappa eta delta₀ : ℝ,
      0 < kappa ∧ 0 < eta ∧
      0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
        ∀ F : Kakeya.TubeFamily delta,
          F.IsInUnitBall →
          F.IsEssentiallyDistinct →
          ∀ Y : Kakeya.Shading F,
            Y.IsLambdaDense
                (Kakeya.realRpowENN delta eta) →
            Kakeya.KatzTaoConvexWolffBound F
                (Real.rpow delta (-eta)) →
            Kakeya.FrostmanSlabWolffBound F
                (Real.rpow delta (-eta)) →
              ENNReal.ofReal kappa *
                  Kakeya.realRpowENN delta (3 / 2 + epsilon) *
                  ENNReal.rpow F.enncard (1 / 2) ≤
                volume Y.union

/--
Legacy conditional assembly from an unconditional decomposition hypothesis.
The proof remains closed and reusable, but no producer for this stronger
hypothesis lies on the canonical Section 7 DAG.
-/
def HairbrushExpandedFromDecompositionAssemblyStatement : Prop :=
  HairbrushPreprocessingStatement →
    HairbrushSingleScaleDecompositionStatement →
      HairbrushTwoBroadFiberEstimateStatement →
        HairbrushExpandedEstimate

/--
Canonical Appendix-B assembly from preprocessing, the Section 7 dichotomy,
and the two-broad Wolff estimate.
-/
def HairbrushExpandedAssemblyStatement : Prop :=
  HairbrushPreprocessingStatement →
    HairbrushBroadScaleDichotomyStatement →
      HairbrushTwoBroadFiberEstimateStatement →
        HairbrushExpandedEstimate

/-- Convert the expanded small-scale estimate to the exact Assertion-D API. -/
def Proposition1_8AssemblyStatement : Prop :=
  HairbrushExpandedEstimate →
    Kakeya.AssertionD (1 / 2) 0

end Kakeya.Assouad
