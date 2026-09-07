import MyLeanRepo.Kakeya.Assouad.WZ1.Definitions
import MyLeanRepo.Kakeya.Assouad.WZ1.Inputs
import MyLeanRepo.Kakeya.Assouad.WZ1.RescaledCoveredParentFiberStatements
import MyLeanRepo.Kakeya.Assouad.CriticalInputs

/-!
# Standalone WZ1 migration statements

These are the first independent leaves needed to replace `C2GrainsInput` by
actual formal proofs.  The completed CV theorem is available through the
closed `WZ1.CVBridge` module; OSW remains an explicit external hypothesis.
-/

namespace Kakeya.Assouad

open MeasureTheory

/--
WZ1 Lemma 11, linear-algebra leaf.  A quantitatively transverse pair of unit
directions determines a unit normal, and a small scalar triple product forces
the third direction to be nearly tangent to that normal.
-/
def WZ1CrossNormalStatement : Prop :=
  ∀ u v w : Point3,
    ‖u‖ = 1 → ‖v‖ = 1 → ‖w‖ = 1 →
    ∀ kappa tau : ℝ,
      0 < kappa →
      kappa ≤ ‖wz1Cross u v‖ →
      |wz1TripleProduct u v w| ≤ tau →
        ∃ normal : Point3,
          ‖normal‖ = 1 ∧
          inner ℝ u normal = 0 ∧
          inner ℝ v normal = 0 ∧
          |inner ℝ w normal| ≤ tau / kappa

/--
Delete the counted broad set once its point-multiplicity-weighted mass is at
most half of the total shading mass.
-/
def WZ1NarrowPruningStatement : Prop :=
  ∀ delta tau : ℝ, ∀ Q : ℕ,
    ∀ F : Kakeya.Streamlined.TubeFamily delta,
      ∀ Y : Kakeya.Streamlined.TubeShading F,
        MeasurableSet (wz1CountedBroadSet Y tau Q) →
        2 * (∫⁻ p in wz1CountedBroadSet Y tau Q,
          (Y.pointMultiplicity p : ENNReal)) ≤ Y.mass →
          Nonempty (WZ1NarrowRefinementData Y tau Q)

/--
On a counted-narrow shading with robust transversality, choose one transverse
active pair at each point, retain the many third directions narrow relative
to that pair, and build the normalized-cross weak plane map on the resulting
same-configuration subshading.
-/
def WZ1WeakPlaninessFromNarrowStatement : Prop :=
  ∀ delta kappa tau : ℝ, ∀ Q R : ℕ,
    0 < kappa →
    ∀ F : Kakeya.Streamlined.TubeFamily delta,
      F.Nonempty →
      ∀ Y : Kakeya.Streamlined.TubeShading F,
        ∀ narrow : WZ1NarrowRefinementData Y tau Q,
          (∀ p ∈ narrow.shading.union, ∀ i,
            p ∈ narrow.shading.carrier i →
              wz1CloseDirectionCount narrow.shading p i kappa <
                R) →
          (∀ p ∈ narrow.shading.union,
            let mu := narrow.shading.pointMultiplicity p
            4 * (Q + 3 * R * mu ^ 2) ≤ 3 * mu ^ 3) →
            ∃ package : WZ1WeakPlaninessPackage Y tau Q kappa,
              package.narrow = narrow

/--
Assemble the WZ1 Lemma 11 preparation, counted-broad pruning, and validated
weak-planiness selection on one configuration.

The preparation's exact thresholds and budgets are passed directly to the two
closed predecessor statements.  The output records the resulting weak plane
map and the exact `1/8` aggregate mass retention.
-/
def WZ1WeakPlaninessAssemblyConclusion : Prop :=
  ∀ {sigma epsilon delta : ℝ},
        ∀ preparation :
            WZ1PlaninessPreparationData sigma epsilon delta,
          Nonempty (WZ1WeakPlaninessAssemblyData preparation)

/-- Assemble the direct Lemma 11 output from its two leaf proofs. -/
def WZ1WeakPlaninessAssemblyStatement : Prop :=
  WZ1NarrowPruningStatement →
    WZ1WeakPlaninessFromNarrowStatement →
      WZ1WeakPlaninessAssemblyConclusion

/--
WZ1 Lemma 7 geometric counting core.  At one shaded point, all active tubes
whose directions have cross product less than `kappa` with a fixed active
tube lie in one convex cylinder of volume at most `216 * kappa²`.  The
Convex-Wolff bound then controls their number.
-/
def WZ1RobustCloseDirectionCountStatement : Prop :=
  ∀ delta kappa : ℝ, ∀ C : ENNReal,
    0 < delta → delta ≤ 1 → delta ≤ kappa →
      ∀ F : Kakeya.Streamlined.TubeFamily delta,
        ∀ Y : Kakeya.Streamlined.TubeShading F,
          ∀ p : Point3, ∀ i : Fin F.card,
            p ∈ Y.carrier i →
              ConvexWolffBound F C →
                ∃ W : Set Point3,
                  Convex ℝ W ∧
                  MeasureTheory.volume W ≤
                    ENNReal.ofReal (216 * kappa ^ 2) ∧
                  (∀ j : Fin F.card,
                    p ∈ Y.carrier j →
                    ‖wz1Cross
                      (F.tube i).direction
                      (F.tube j).direction‖ < kappa →
                      (F.tube j).carrier ⊆ W) ∧
                  (wz1CloseDirectionCount Y p i kappa : ENNReal) *
                      Kakeya.deltaTubeVolume 1 ≤
                    C *
                      ENNReal.ofReal (216 * kappa ^ 2) *
                        F.enncard

/--
WZ1 Lemma 7, absolute packing at the coarse direction scale.

Among pairwise volume-essentially-distinct `rho`-tubes that all shade one
point, only an absolute finite number can lie in one unoriented direction cap
of radius `10 * rho`.  The common shaded point controls transverse and axial
offsets, while essential distinctness separates the resulting normalized
finite-dimensional tube parameters.

This is the geometric ingredient used in the paper after applying
Proposition 5 at the robust-transversality scale.  It is stronger and more
appropriate than applying the global Convex-Wolff cylinder count directly at
the fine scale.
-/
def WZ1CoarseDirectionPackingStatement : Prop :=
  ∃ D : ℕ, 0 < D ∧
    ∀ rho : ℝ, 0 < rho → rho ≤ 1 / 10000 →
      ∀ F : Kakeya.Streamlined.TubeFamily rho,
        F.IsEssentiallyDistinct →
          ∀ Y : Kakeya.Streamlined.TubeShading F,
            ∀ p : Point3, ∀ i : Fin F.card,
              p ∈ Y.carrier i →
                wz1CloseDirectionCount Y p i (10 * rho) ≤ D

/--
Direction-transfer core of WZ1 Lemma 12.  A fine direction that is weakly
incident to a unit plane normal remains incident after coarsening, provided
the coarse direction is within the remaining half-scale error.
-/
def WZ1CoarseDirectionIncidenceStatement : Prop :=
  ∀ normal fineDirection coarseDirection : Point3,
    ‖normal‖ = 1 →
      ∀ rho : ℝ, 0 ≤ rho →
        |inner ℝ normal fineDirection| ≤ rho / 2 →
        ‖coarseDirection - fineDirection‖ ≤ rho / 2 →
          |inner ℝ normal coarseDirection| ≤ rho

/--
WZ1 Lemma 13, geometric perturbation leaf.  If a unit normal is nearly
orthogonal to two quantitatively transverse unit directions, it lies close to
one of the two normalized cross-product normals.
-/
def WZ1PlaneProjectionPerturbationStatement : Prop :=
  ∀ u v normal : Point3,
    ‖u‖ = 1 → ‖v‖ = 1 → ‖normal‖ = 1 →
    ∀ kappa rho : ℝ,
      0 < kappa → 0 ≤ rho →
      kappa ≤ ‖wz1Cross u v‖ →
      |inner ℝ normal u| ≤ rho →
      |inner ℝ normal v| ≤ rho →
        ∃ sign : ℝ, (sign = 1 ∨ sign = -1) ∧
          ‖normal -
            sign • ((‖wz1Cross u v‖)⁻¹ • wz1Cross u v)‖ ≤
              10 * rho / kappa

/--
WZ1 Lemma 13, oriented finite-cap refinement.

Inside each spatial cell, fix two transverse unit tube directions.  The
closed perturbation theorem places every active unit plane-map value within
`10 * rho / kappa` of one of the two antipodal normalized cross-product
normals.  Partition those projective balls into a finite directed coordinate
grid of mesh `scale / sqrt 3`, then select one directed cap independently in
each cell according to aggregate shaded mass.

The resulting full measurable restriction loses at most the explicit factor
`wz1OrientationCapCount (10 * rho / kappa) scale` and satisfies the oriented
same-cell estimate used by Corollary 14.  This is the paper's final `E₄`
pigeonholing step together with its projective `±` perturbation input.
-/
def WZ1OrientedCellRefinementStatement : Prop :=
  WZ1PlaneProjectionPerturbationStatement →
    ∀ {delta : ℝ},
      ∀ {F : Kakeya.Streamlined.TubeFamily delta},
        ∀ (Y : Kakeya.Streamlined.TubeShading F),
          ∀ {cellCount : ℕ},
            ∀ cell : Point3 → Fin cellCount,
              Measurable cell →
              ∀ planeMap : Point3 → Point3,
                Measurable planeMap →
                ∀ firstDirection secondDirection :
                    Fin cellCount → Point3,
                  ∀ kappa rho scale : ℝ,
                    0 < kappa → 0 ≤ rho → 0 < scale →
                    (∀ c, ‖firstDirection c‖ = 1) →
                    (∀ c, ‖secondDirection c‖ = 1) →
                    (∀ c,
                      kappa ≤
                        ‖wz1Cross
                          (firstDirection c)
                          (secondDirection c)‖) →
                    (∀ p ∈ Y.union, ‖planeMap p‖ = 1) →
                    (∀ p ∈ Y.union,
                      |inner ℝ (planeMap p)
                        (firstDirection (cell p))| ≤ rho) →
                    (∀ p ∈ Y.union,
                      |inner ℝ (planeMap p)
                        (secondDirection (cell p))| ≤ rho) →
                      Nonempty
                        (WZ1OrientedCellRefinementData
                          Y cell planeMap
                            (wz1OrientationCapCount
                              (10 * rho / kappa) scale)
                            scale)

/--
Finest-scale exact-cell plane-map refinement for WZ1 Lemma 15.

The finite measurable cells have diameter at most `2 * delta` and uniformly
bounded nearby degree.  First choose one directed plane-map cap of radius
`delta / 2` per active cell.  Then color the nearby-cell graph and retain one
color class, so retained points at distance at most `delta` lie in the same
cell.  The representative map is therefore exactly constant at the finest
scale and remains within `delta / 2` of the original map.
-/
def WZ1FinestCellPlaneMapStatement : Prop :=
  ∀ {delta : ℝ}, 0 < delta →
    ∀ {F : Kakeya.Streamlined.TubeFamily delta},
      ∀ Y : Kakeya.Streamlined.TubeShading F,
        ∀ {cellCount : ℕ},
          ∀ cell : Point3 → Fin cellCount,
            Measurable cell →
            ∀ representative : Fin cellCount → Point3,
              ∀ neighborBound : ℕ, 0 < neighborBound →
                (∀ c : Fin cellCount,
                  {p | p ∈ Y.union ∧ cell p = c}.Nonempty →
                    wz1NearbyActiveCellCount
                      Y cell representative c ≤ neighborBound) →
                (∀ p ∈ Y.union,
                  representative (cell p) ∈ Y.union ∧
                    cell (representative (cell p)) = cell p ∧
                      dist p (representative (cell p)) ≤ 2 * delta) →
                ∀ planeMap : Point3 → Point3,
                  Measurable planeMap →
                  (∀ p ∈ Y.union, ‖planeMap p‖ = 1) →
                    Nonempty
                      (WZ1FinestCellPlaneMapData
                        Y cell planeMap
                          ((neighborBound + 1) *
                            wz1FinestPlaneMapCapCount delta))

/--
Normalize the full-carrier critical floor to the cropped WZ1 convention.

This is the precise bridge required by repeated applications of Proposition 5
to coarse families.  It must absorb only fixed geometric and finite-selection
losses; it may not assume that a cropped coarse family already satisfies
`F.IsInUnitBall`.
-/
def WZ1CriticalFloorNormalizationStatement : Prop :=
  ∀ sigma : ℝ,
    HasCriticalVolumeFloor sigma →
      HasWZ1CriticalVolumeFloor sigma

/--
The assembled output of WZ1 Proposition 5, Step 2.

The caller chooses the final extremality loss, the smaller retained-mass
loss, and the scale-window loss.  The output is a same-family refinement
which retains quantitative mass, has constant global multiplicity, and
satisfies the paper's pointwise multiplicity cap inside every `rho` parent.
The proof must use the critical-volume floor after unit rescaling; the
pointwise cap is not a consequence of `FibersAreCFrostman` alone.
-/
def WZ1Proposition5FiberRefinementConclusion : Prop :=
  ∀ sigma : ℝ, 0 < sigma → sigma < 1 →
    HasWZ1CriticalVolumeFloor sigma →
      ∀ outputLoss massLoss scaleLoss : ℝ,
        0 < outputLoss →
        0 < massLoss → massLoss < outputLoss →
        0 < scaleLoss →
          ∃ eta delta₀ : ℝ,
            0 < eta ∧ eta < massLoss ∧
            0 < delta₀ ∧ delta₀ ≤ 1 ∧
            ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
              ∀ F : Kakeya.Streamlined.TubeFamily delta,
                ∀ U : Kakeya.Streamlined.UniformTubeStructure F,
                  ∀ Y : Kakeya.Streamlined.TubeShading F,
                    WZ1ExtremalPair sigma eta F U Y →
                    ∀ rho : Kakeya.Streamlined.AdmissibleScale delta,
                      Real.rpow delta (1 - scaleLoss) ≤ rho.1 →
                      rho.1 ≤ Real.rpow delta scaleLoss →
                        Nonempty
                          (WZ1Proposition5FiberRefinementData
                            (sigma := sigma)
                            (outputLoss := outputLoss)
                            (massLoss := massLoss)
                            U Y rho)

/--
Assemble Proposition 5 Step 2 from the genuine one-parent unit-rescaled
Lemma 6.  The global proof first balances parent fibers, applies the supplied
leaf independently to each retained parent, unions those source refinements,
and only then performs the final global multiplicity pigeonhole.
-/
def WZ1Proposition5FiberRefinementStatement : Prop :=
  WZ1RescaledCoveredParentFiberStatement →
    WZ1Proposition5FiberRefinementConclusion

/--
WZ1 Proposition 5 before the associated-representative selection.

The windowed critical floor justifies lower-volume bounds after forming new
coarse configurations.  The coherent cover comes from the supplied
`UniformTubeStructure`; the output contains the fine and coarse extremal
configurations, directional parent alignment, the paper's coarse/fiber
point-multiplicity bounds, and the Step 5 simultaneous cell/fiber balancing
certificate.
-/
def WZ1BalancedCoverCoreStatement : Prop :=
  WZ1Proposition5FiberRefinementConclusion →
    ∀ sigma : ℝ, 0 < sigma → sigma < 1 →
      HasWZ1CriticalVolumeFloor sigma →
        ∀ coreLoss scaleLoss : ℝ,
          0 < coreLoss → 0 < scaleLoss →
          ∃ eta delta₀ : ℝ,
            0 < eta ∧ 0 < delta₀ ∧ delta₀ ≤ 1 ∧
            ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
              ∀ F : Kakeya.Streamlined.TubeFamily delta,
                ∀ U : Kakeya.Streamlined.UniformTubeStructure F,
                  ∀ Y : Kakeya.Streamlined.TubeShading F,
                    WZ1ExtremalPair sigma eta F U Y →
                    ∀ rho : Kakeya.Streamlined.AdmissibleScale delta,
                      Real.rpow delta (1 - scaleLoss) ≤ rho.1 →
                      rho.1 ≤ Real.rpow delta scaleLoss →
                        Nonempty
                          (WZ1BalancedCoverCoreData
                            (sigma := sigma) (epsilon := coreLoss)
                            U Y rho)

/--
Select the associated representatives used by WZ1 Lemmas 12--14.

For each retained `rho`-cell the producer chooses a point of high fine
multiplicity and keeps the coarse parents associated to that point.  The
Step 5 cell saturation and parent-fiber cell balance carried by the core make
this selection quantitatively mass-retaining.  The returned fine and coarse
shadings must refine that supplied core; an unrelated existential balanced
cover is not permitted.
-/
def WZ1AssociatedCellRefinementStatement : Prop :=
  ∀ sigma outputLoss : ℝ,
    0 < sigma → sigma < 1 → 0 < outputLoss →
      ∃ coreLoss delta₀ : ℝ,
        0 < coreLoss ∧ coreLoss < outputLoss ∧
        0 < delta₀ ∧ delta₀ ≤ 1 ∧
        ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
          ∀ F : Kakeya.Streamlined.TubeFamily delta,
            ∀ U : Kakeya.Streamlined.UniformTubeStructure F,
              ∀ Y : Kakeya.Streamlined.TubeShading F,
                ∀ rho : Kakeya.Streamlined.AdmissibleScale delta,
                  Real.rpow delta (1 - outputLoss) ≤ rho.1 →
                  rho.1 ≤ Real.rpow delta outputLoss →
                    ∀ core : WZ1BalancedCoverCoreData
                        (sigma := sigma) (epsilon := coreLoss) U Y rho,
                      Nonempty
                        (WZ1AssociatedCellRefinementData
                          (sigma := sigma)
                          (coreLoss := coreLoss)
                          (outputLoss := outputLoss)
                          U Y rho core)

/--
WZ1 Proposition 5 in the full form consumed by Lemmas 12--14.

The signature is retained as the stable downstream API.
-/
def WZ1BalancedCoverStatement : Prop :=
  ∀ sigma : ℝ, 0 < sigma → sigma < 1 →
    HasCriticalVolumeFloor sigma →
      ∀ epsilon : ℝ, 0 < epsilon →
        ∃ eta delta₀ : ℝ,
          0 < eta ∧ 0 < delta₀ ∧ delta₀ ≤ 1 ∧
          ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
            ∀ F : Kakeya.Streamlined.TubeFamily delta,
              ∀ U : Kakeya.Streamlined.UniformTubeStructure F,
                ∀ Y : Kakeya.Streamlined.TubeShading F,
                  WZ1ExtremalPair sigma eta F U Y →
                  ∀ rho : Kakeya.Streamlined.AdmissibleScale delta,
                    Real.rpow delta (1 - epsilon) ≤ rho.1 →
                    rho.1 ≤ Real.rpow delta epsilon →
                      Nonempty
                        (WZ1BalancedCoverData
                          (sigma := sigma) (epsilon := epsilon)
                          U Y rho)

/--
The fixed-scale spatial-cover conclusion extracted from Proposition 5.

The caller chooses `rho`; the conclusion returns one same-family extremal
subshading whose full shaded union has the paper's
`delta^(-loss) * rho^(-3+sigma)` cover.  Lemma 32 later pigeonholes one
horizontal interval from this particular output.
-/
def WZ1Proposition5SpatialCoverConclusion : Prop :=
  ∀ sigma : ℝ, 0 < sigma → sigma < 1 →
    HasCriticalVolumeFloor sigma →
      ∀ outputLoss scaleLoss : ℝ,
        0 < outputLoss → 0 < scaleLoss →
          ∃ inputLoss delta₀ : ℝ,
            0 < inputLoss ∧ inputLoss ≤ outputLoss ∧
            0 < delta₀ ∧ delta₀ ≤ 1 ∧
            ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
              ∀ F : Kakeya.Streamlined.TubeFamily delta,
                ∀ U : Kakeya.Streamlined.UniformTubeStructure F,
                  ∀ Y : Kakeya.Streamlined.TubeShading F,
                    IsExtremalPair sigma inputLoss F U Y →
                    ∀ rho : Kakeya.Streamlined.AdmissibleScale delta,
                      Real.rpow delta (1 - scaleLoss) ≤ rho.1 →
                      rho.1 ≤ Real.rpow delta scaleLoss →
                        Nonempty
                          (WZ1Proposition5SpatialCoverData
                            (sigma := sigma)
                            (outputLoss := outputLoss)
                            U Y rho)

/--
Derive the fixed-scale spatial cover from the assembled Proposition 5
balanced-cover theorem.
-/
def WZ1Proposition5SpatialCoverStatement : Prop :=
  WZ1BalancedCoverStatement →
    WZ1Proposition5SpatialCoverConclusion

/-- Assemble the stable balanced-cover API from its two mathematical leaves. -/
def WZ1BalancedCoverAssemblyStatement : Prop :=
  WZ1CriticalFloorNormalizationStatement →
    WZ1Proposition5FiberRefinementConclusion →
      WZ1BalancedCoverCoreStatement →
        WZ1AssociatedCellRefinementStatement →
          WZ1BalancedCoverStatement

/--
Transfer the absolute coarse direction packing bound through one balanced
cover.

If two active fine directions have cross norm less than `rho`, their assigned
coarse directions have cross norm less than `10 * rho`: the projective parent
alignment loses at most `4 * rho` for each direction.  There are at most `D`
such active coarse parents, and each parent fiber contributes at most the
balanced fiber multiplicity cap.
-/
def WZ1RobustCloseCountFromBalancedConclusion : Prop :=
  ∃ D : ℕ, 0 < D ∧
      ∀ {delta sigma epsilon : ℝ},
        ∀ {F : Kakeya.Streamlined.TubeFamily delta},
          ∀ {U : Kakeya.Streamlined.UniformTubeStructure F},
            ∀ {Y : Kakeya.Streamlined.TubeShading F},
              ∀ {rho : Kakeya.Streamlined.AdmissibleScale delta},
                rho.1 ≤ 1 / 10000 →
                ∀ balanced :
                    WZ1BalancedCoverData
                      (sigma := sigma) (epsilon := epsilon) U Y rho,
                  ∀ p ∈ balanced.refined.union,
                    ∀ i, p ∈ balanced.refined.carrier i →
                      (wz1CloseDirectionCount
                          balanced.refined p i rho.1 : ENNReal) ≤
                        (D : ENNReal) *
                          Kakeya.realRpowENN (delta / rho.1)
                            (-sigma - epsilon)

/-- Transfer the coarse packing theorem through one balanced cover. -/
def WZ1RobustCloseCountFromBalancedStatement : Prop :=
  WZ1CoarseDirectionPackingStatement →
    WZ1RobustCloseCountFromBalancedConclusion

/--
WZ1 Lemma 13, transverse coarse-pair producer.

At every retained fine point, the robust close-direction hypothesis leaves at
least half of the ordered fine pairs transverse.  The balanced fiber and
coarse multiplicity bounds then allow one coarse parent pair to be selected
in each spatial cell.  Restricting to the common fine mass of those pairs
loses the explicit factor
`4 * fiberCap^2 * coarseCap^2 / fineMultiplicity^2`.

The repository cover supplies only projective direction alignment at error
`4 * rho`.  Thus the selected coarse pair has cross norm at least
`fineKappa - 8 * rho`, while each parent direction is incident to the fine
plane map at scale `5 * rho`.
-/
def WZ1TransverseCoarsePairStatement : Prop :=
  ∀ {delta sigma epsilon : ℝ},
    ∀ {F : Kakeya.Streamlined.TubeFamily delta},
      ∀ {U : Kakeya.Streamlined.UniformTubeStructure F},
        ∀ {Y : Kakeya.Streamlined.TubeShading F},
          ∀ {rho : Kakeya.Streamlined.AdmissibleScale delta},
            ∀ balanced :
                WZ1BalancedCoverData
                  (sigma := sigma) (epsilon := epsilon) U Y rho,
              ∀ finePlaneMap : Point3 → Point3,
                Measurable finePlaneMap →
                (∀ p ∈ balanced.refined.union,
                  ‖finePlaneMap p‖ = 1) →
                (∀ i p, p ∈ balanced.refined.carrier i →
                  |inner ℝ (F.tube i).direction
                    (finePlaneMap p)| ≤ rho.1) →
                ∀ fineKappa : ℝ,
                  0 < fineKappa →
                  8 * rho.1 < fineKappa →
                  (∀ p ∈ balanced.refined.union,
                    ∀ i, p ∈ balanced.refined.carrier i →
                      2 *
                          wz1CloseDirectionCount
                            balanced.refined p i fineKappa ≤
                        balanced.fineMultiplicity) →
                    Nonempty
                      (WZ1TransverseCoarsePairData
                        balanced finePlaneMap fineKappa
                          (fineKappa - 8 * rho.1))

/--
WZ1 Corollary 14, bounded-neighbor cell separation.

Color active balanced cells using the graph that joins two cells when their
representatives are within `6 * rho`.  The balanced-cover neighbor bound gives
at most `neighborBound + 1` colors.  Keeping the heaviest color class retains
the corresponding fraction of oriented shaded mass.  Two retained points at
distance at most `rho` have representatives within `5 * rho`, so their cells
must coincide and the oriented same-cell estimate applies.
-/
def WZ1NearbyCellSeparationStatement : Prop :=
  ∀ {delta sigma epsilon : ℝ},
    ∀ {F : Kakeya.Streamlined.TubeFamily delta},
      ∀ {U : Kakeya.Streamlined.UniformTubeStructure F},
        ∀ {Y : Kakeya.Streamlined.TubeShading F},
          ∀ {rho : Kakeya.Streamlined.AdmissibleScale delta},
            ∀ balanced :
                WZ1BalancedCoverData
                  (sigma := sigma) (epsilon := epsilon) U Y rho,
              ∀ source : Kakeya.Streamlined.TubeShading F,
                ∀ planeMap : Point3 → Point3,
                  ∀ capCount : ℕ, ∀ scale : ℝ,
                    ∀ oriented :
                        WZ1OrientedCellRefinementData
                          source balanced.cell planeMap capCount scale,
                      IsSubshading source balanced.refined →
                        Nonempty
                          (WZ1NearbyCellSeparationData
                            balanced source planeMap capCount scale oriented)

/--
The direct one-configuration conclusion of WZ1 Lemma 13 and Corollary 14.

Separating this from the conditional assembly proposition prevents downstream
targets from treating a function `dependencies → conclusion` as though it
were already the instantiated conclusion.
-/
def WZ1OneScalePlaneMapConclusion : Prop :=
  ∀ {delta sigma epsilon : ℝ},
            ∀ {F : Kakeya.Streamlined.TubeFamily delta},
              ∀ {U : Kakeya.Streamlined.UniformTubeStructure F},
                ∀ {Y : Kakeya.Streamlined.TubeShading F},
                  ∀ {rho : Kakeya.Streamlined.AdmissibleScale delta},
                    ∀ balanced :
                        WZ1BalancedCoverData
                          (sigma := sigma) (epsilon := epsilon) U Y rho,
                      ∀ finePlaneMap : Point3 → Point3,
                        Measurable finePlaneMap →
                        (∀ p ∈ balanced.refined.union,
                          ‖finePlaneMap p‖ = 1) →
                        (∀ i p, p ∈ balanced.refined.carrier i →
                          |inner ℝ (F.tube i).direction
                            (finePlaneMap p)| ≤ rho.1) →
                        ∀ fineKappa : ℝ,
                          0 < fineKappa →
                          8 * rho.1 < fineKappa →
                          (∀ p ∈ balanced.refined.union,
                            ∀ i, p ∈ balanced.refined.carrier i →
                              2 *
                                  wz1CloseDirectionCount
                                    balanced.refined p i fineKappa ≤
                                balanced.fineMultiplicity) →
                            Nonempty
                              (WZ1OneScalePlaneMapData
                                balanced finePlaneMap fineKappa)

/--
WZ1 Lemma 13 and Corollary 14, complete one-scale assembly.

The transverse coarse-pair producer, directed-cap refinement, and
bounded-neighbor cell coloring are applied successively to one balanced
configuration.  The output retains the original measurable fine plane map,
its fine-scale incidence, the `rho`-scale nearby-point estimate, and the exact
product of all three mass losses.
-/
def WZ1OneScalePlaneMapStatement : Prop :=
  WZ1TransverseCoarsePairStatement →
    WZ1PlaneProjectionPerturbationStatement →
      WZ1OrientedCellRefinementStatement →
        WZ1NearbyCellSeparationStatement →
          WZ1OneScalePlaneMapConclusion

/-- The direct nested robust-scale and target-scale conclusion of WZ1 Lemma 13. -/
def WZ1TwoScalePlaneMapConclusion : Prop :=
  ∃ D : ℕ, 0 < D ∧
        ∀ {delta sigma robustLoss fineLoss : ℝ},
          ∀ {F : Kakeya.Streamlined.TubeFamily delta},
            ∀ {U : Kakeya.Streamlined.UniformTubeStructure F},
              ∀ {Y : Kakeya.Streamlined.TubeShading F},
                ∀ robustScale fineScale :
                    Kakeya.Streamlined.AdmissibleScale delta,
                  robustScale.1 ≤ 1 / 10000 →
                  8 * fineScale.1 < robustScale.1 →
                  ∀ robustCover :
                      WZ1BalancedCoverData
                        (sigma := sigma) (epsilon := robustLoss)
                        U Y robustScale,
                    ∀ fineCover :
                        WZ1BalancedCoverData
                          (sigma := sigma) (epsilon := fineLoss)
                          U robustCover.refined fineScale,
                      2 * (D : ENNReal) *
                          Kakeya.realRpowENN
                            (delta / robustScale.1)
                            (-sigma - robustLoss) ≤
                        (fineCover.fineMultiplicity : ENNReal) →
                      ∀ planeMap : Point3 → Point3,
                        Measurable planeMap →
                        (∀ p ∈ fineCover.refined.union,
                          ‖planeMap p‖ = 1) →
                        (∀ i p, p ∈ fineCover.refined.carrier i →
                          |inner ℝ (F.tube i).direction
                            (planeMap p)| ≤ fineScale.1) →
                          Nonempty
                            (WZ1TwoScalePlaneMapData
                              robustScale fineScale
                              robustCover fineCover planeMap)

/--
WZ1 Lemma 13, nested robust-scale and target-scale assembly.

The absolute packing constant is chosen before every configuration.  First a
balanced cover at `robustScale` supplies the robust close-direction count.
Then a second balanced cover at the smaller `fineScale` is formed on the same
refined configuration.  Once the displayed fixed-constant inequality is
absorbed by the second fine multiplicity, the complete one-scale assembly
applies with transversality threshold `robustScale`.
-/
def WZ1TwoScalePlaneMapStatement : Prop :=
  WZ1RobustCloseCountFromBalancedConclusion →
    WZ1OneScalePlaneMapConclusion →
      WZ1TwoScalePlaneMapConclusion

/--
Arithmetic parameter absorption for the nested Lemma 13 construction.

Set `kappa = delta^robustExponent`.  The exponent assumptions place `kappa`
inside the scale window used by the first balanced cover.  Since
`robustExponent < targetWindow`, every target scale
`rho ≤ delta^targetWindow` satisfies `8 * rho < kappa` after shrinking
`delta`.  The final inequality absorbs the absolute coarse packing constant
and the robust-cover fiber cap into the lower fine multiplicity supplied by
the second balanced cover.
-/
def WZ1TwoScaleParameterAbsorptionStatement : Prop :=
  ∀ D : ℕ, 0 < D →
    ∀ sigma robustExponent robustLoss fineLoss targetWindow : ℝ,
      0 < sigma →
      0 < robustLoss → 0 < fineLoss →
      0 < robustExponent →
      robustLoss ≤ robustExponent →
      robustExponent ≤ 1 - robustLoss →
      robustExponent < targetWindow →
      targetWindow ≤ 1 →
      robustLoss + fineLoss < robustExponent * sigma →
        ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
          ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
            let kappa := Real.rpow delta robustExponent
            delta ≤ kappa ∧
              kappa ≤ 1 ∧
              Real.rpow delta (1 - robustLoss) ≤ kappa ∧
              kappa ≤ Real.rpow delta robustLoss ∧
              (∀ rho : ℝ, 0 < rho →
                rho ≤ Real.rpow delta targetWindow →
                  8 * rho < kappa) ∧
              2 * (D : ENNReal) *
                  Kakeya.realRpowENN (delta / kappa)
                    (-sigma - robustLoss) ≤
                Kakeya.realRpowENN delta (-sigma + fineLoss)

/-- The direct extremal one-scale Corollary 14 conclusion. -/
def WZ1ExtremalOneScalePlaneMapConclusion : Prop :=
  ∀ sigma : ℝ, 0 < sigma → sigma < 1 →
          HasCriticalVolumeFloor sigma →
            ∀ outputLoss : ℝ, 0 < outputLoss →
              ∃ inputLoss delta₀ : ℝ,
                0 < inputLoss ∧ inputLoss ≤ outputLoss ∧
                0 < delta₀ ∧ delta₀ ≤ 1 ∧
                ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
                  ∀ F : Kakeya.Streamlined.TubeFamily delta,
                    ∀ U : Kakeya.Streamlined.UniformTubeStructure F,
                      ∀ Y : Kakeya.Streamlined.TubeShading F,
                        WZ1ExtremalPair sigma inputLoss F U Y →
                        ∀ planeMap : Point3 → Point3,
                          Measurable planeMap →
                          (∀ p ∈ Y.union, ‖planeMap p‖ = 1) →
                          (∀ i p, p ∈ Y.carrier i →
                            |inner ℝ (F.tube i).direction
                              (planeMap p)| ≤ 6 * delta) →
                          ∀ scale :
                              Kakeya.Streamlined.AdmissibleScale delta,
                            Real.rpow delta (1 - outputLoss) ≤ scale.1 →
                            scale.1 ≤ Real.rpow delta outputLoss →
                              Nonempty
                                (WZ1ExtremalOneScalePlaneMapData
                                  (sigma := sigma)
                                  (outputLoss := outputLoss)
                                  (incidenceScale := 6 * delta)
                                  U Y planeMap scale)

/--
WZ1 Corollary 14 with extremality restored after one target scale.

All geometry stays on the original fine family and coherent uniform structure.
The two balanced covers, robust-transversality transfer, directed-cap
selection, and nearby-cell coloring are internal.  Their exact mass loss is
absorbed into `outputLoss`, while the global critical floor restores the lower
union-volume side of extremality for the final subshading.

The input plane map already has the repository-normalized incidence
`6 * delta`; the target-scale lower bound and the small-scale threshold ensure
this is at most the scale consumed by the two-scale assembly.
-/
def WZ1ExtremalOneScalePlaneMapStatement : Prop :=
  WZ1BalancedCoverStatement →
    WZ1TwoScaleParameterAbsorptionStatement →
      WZ1TwoScalePlaneMapConclusion →
        WZ1ExtremalOneScalePlaneMapConclusion

/-- The direct finite-scale iteration conclusion of WZ1 Lemma 15. -/
def WZ1FinitePlaneMapIterationConclusion : Prop :=
  ∀ sigma outputLoss : ℝ,
      0 < sigma → sigma < 1 →
      0 < outputLoss →
      HasCriticalVolumeFloor sigma →
      ∀ N : ℕ, 2 ≤ N →
        ∃ inputLoss delta₀ : ℝ,
          0 < inputLoss ∧ inputLoss ≤ outputLoss ∧
          0 < delta₀ ∧ delta₀ ≤ 1 ∧
          ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
            ∀ F : Kakeya.Streamlined.TubeFamily delta,
              ∀ U : Kakeya.Streamlined.UniformTubeStructure F,
                ∀ Y : Kakeya.Streamlined.TubeShading F,
                  WZ1ExtremalPair sigma inputLoss F U Y →
                  ∀ planeMap : Point3 → Point3,
                    Measurable planeMap →
                    (∀ p ∈ Y.union, ‖planeMap p‖ = 1) →
                    (∀ i p, p ∈ Y.carrier i →
                      |inner ℝ (F.tube i).direction
                        (planeMap p)| ≤ 6 * delta) →
                      Nonempty
                        (WZ1FinitePlaneMapIterationData
                          (sigma := sigma)
                          (outputLoss := outputLoss)
                          (incidenceScale := 6 * delta)
                          U Y planeMap N)

/--
Iterate the extremal one-scale Corollary 14 producer over the finite geometric
scale list `delta^(k / N)`, `k = 1, ..., N - 1`.

Every step stays on the original fine family and coherent uniform structure,
uses the same measurable plane map, and returns an extremal subshading.  The
final shading therefore carries all one-scale estimates simultaneously.
-/
def WZ1FinitePlaneMapIterationStatement : Prop :=
  WZ1ExtremalOneScalePlaneMapConclusion →
    WZ1FinitePlaneMapIterationConclusion

/--
Finite-scale metric core of WZ1 Lemma 15.  Constancy at the finest scale,
unit range, and the one-scale estimates from Corollary 14 imply a global
`2 / s` Lipschitz bound.
-/
def WZ1FiniteScaleLipschitzStatement : Prop :=
  ∀ N : ℕ, 1 ≤ N →
    ∀ s : ℝ, 0 < s → s ≤ 1 →
      ∀ E : Set Point3, ∀ V : Point3 → Point3,
        (∀ p ∈ E, ‖V p‖ = 1) →
        (∀ p ∈ E, ∀ q ∈ E,
          dist p q ≤ s ^ N → V p = V q) →
        (∀ k : ℕ, 1 ≤ k → k < N →
          ∀ p ∈ E, ∀ q ∈ E,
            dist p q ≤ s ^ k →
              dist (V p) (V q) ≤ 2 * s ^ k) →
          LipschitzOnWith (Real.toNNReal (2 / s)) V E

/-- The direct global Lipschitz plane-map conclusion of WZ1 Lemma 15. -/
def WZ1LipschitzPlaneMapConclusion : Prop :=
  ∀ sigma outputLoss : ℝ,
          0 < sigma → sigma < 1 →
          0 < outputLoss →
          HasCriticalVolumeFloor sigma →
          ∀ N : ℕ, 2 ≤ N →
            (2 : ℝ) / N ≤ outputLoss →
              ∃ inputLoss delta₀ : ℝ,
                0 < inputLoss ∧ inputLoss ≤ outputLoss ∧
                0 < delta₀ ∧ delta₀ ≤ 1 ∧
                ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
                  ∀ F : Kakeya.Streamlined.TubeFamily delta,
                    ∀ U : Kakeya.Streamlined.UniformTubeStructure F,
                      ∀ Y : Kakeya.Streamlined.TubeShading F,
                        WZ1ExtremalPair sigma inputLoss F U Y →
                        ∀ planeMap : Point3 → Point3,
                          Measurable planeMap →
                          (∀ p ∈ Y.union, ‖planeMap p‖ = 1) →
                          (∀ i p, p ∈ Y.carrier i →
                            |inner ℝ (F.tube i).direction
                              (planeMap p)| ≤ 6 * delta) →
                          (∀ p ∈ Y.union, ∀ q ∈ Y.union,
                            dist p q ≤ delta →
                              planeMap p = planeMap q) →
                            ∃ data :
                              WZ1LipschitzPlaneMapData
                                (sigma := sigma)
                                (outputLoss := outputLoss)
                                U Y,
                              data.planeMap = planeMap

/--
Assemble WZ1 Lemma 15 from a plane map already constant at the finest spatial
scale, the finite list of Corollary 14 refinements, and the closed finite-scale
metric lemma.

The finest-scale constancy is the literal hypothesis of the paper's Lemma 15;
it is prepared before the iteration rather than by a new power-losing
refinement at the endpoint.  The final map preserves the input incidence
bound and has an explicit Lipschitz constant bounded by
`delta^(-outputLoss)`.
-/
def WZ1LipschitzPlaneMapStatement : Prop :=
  WZ1FinitePlaneMapIterationConclusion →
    WZ1FiniteScaleLipschitzStatement →
      WZ1LipschitzPlaneMapConclusion

/--
WZ1 Lemma 17, the first local-grain covering estimate.

The two balanced covers and the robust direction count are explicit
predecessors.  The conclusion stays on the original fine family and controls
the `rho`-covering number inside every spatial ball of radius `tau`.
-/
def WZ1LocalGrainCubeCountConclusion : Prop :=
  ∀ sigma outputLoss : ℝ,
        0 < sigma → sigma < 1 →
        0 < outputLoss →
        HasCriticalVolumeFloor sigma →
          ∃ inputLoss delta₀ : ℝ,
            0 < inputLoss ∧ inputLoss ≤ outputLoss ∧
            0 < delta₀ ∧ delta₀ ≤ 1 ∧
            ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
              ∀ F : Kakeya.Streamlined.TubeFamily delta,
                ∀ U : Kakeya.Streamlined.UniformTubeStructure F,
                  ∀ Y : Kakeya.Streamlined.TubeShading F,
                    WZ1ExtremalPair sigma inputLoss F U Y →
                    ∀ plane : WZ1PlaneMapData Y,
                      (plane.lipschitzConstant : ENNReal) ≤
                        Kakeya.realRpowENN delta (-inputLoss) →
                      ∀ rho tau :
                          Kakeya.Streamlined.AdmissibleScale delta,
                        Real.rpow delta (1 - outputLoss) ≤ rho.1 →
                        rho.1 ≤ Real.rpow delta outputLoss →
                        Real.rpow rho.1 (1 - outputLoss) ≤ tau.1 →
                        tau.1 ≤ Real.sqrt rho.1 →
                          Nonempty
                            (WZ1LocalGrainCubeCountData
                              (sigma := sigma)
                              (outputLoss := outputLoss)
                              U Y plane rho tau)

/-- WZ1 Lemma 17 assembled from its balanced-cover and robust-count inputs. -/
def WZ1LocalGrainCubeCountStatement : Prop :=
  WZ1BalancedCoverStatement →
    WZ1RobustCloseCountFromBalancedConclusion →
      WZ1LocalGrainCubeCountConclusion

/--
WZ1 Lemma 18, interval-localized local-grain covering.

At one fixed pair `rho ≤ tau`, the Lemma 17 cube estimate is refined to every
interval of radius `tau` inside the scalar projection of a `sqrt rho` ball.
-/
def WZ1LocalGrainIntervalConclusion : Prop :=
  ∀ sigma outputLoss : ℝ,
        0 < sigma → sigma < 1 →
        0 < outputLoss →
        HasCriticalVolumeFloor sigma →
          ∃ inputLoss delta₀ : ℝ,
            0 < inputLoss ∧ inputLoss ≤ outputLoss ∧
            0 < delta₀ ∧ delta₀ ≤ 1 ∧
            ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
              ∀ F : Kakeya.Streamlined.TubeFamily delta,
                ∀ U : Kakeya.Streamlined.UniformTubeStructure F,
                  ∀ Y : Kakeya.Streamlined.TubeShading F,
                    WZ1ExtremalPair sigma inputLoss F U Y →
                    ∀ plane : WZ1PlaneMapData Y,
                      (plane.lipschitzConstant : ENNReal) ≤
                        Kakeya.realRpowENN delta (-inputLoss) →
                      ∀ rho tau :
                          Kakeya.Streamlined.AdmissibleScale delta,
                        Real.rpow delta (1 - outputLoss) ≤ rho.1 →
                        rho.1 ≤ Real.rpow delta outputLoss →
                        Real.rpow rho.1 (1 - outputLoss) ≤ tau.1 →
                        tau.1 ≤ Real.sqrt rho.1 →
                          Nonempty
                            (WZ1LocalGrainIntervalData
                              (sigma := sigma)
                              (outputLoss := outputLoss)
                              U Y plane rho tau)

/-- WZ1 Lemma 18 assembled from the direct Lemma 17 conclusion. -/
def WZ1LocalGrainIntervalStatement : Prop :=
  WZ1LocalGrainCubeCountConclusion →
    WZ1LocalGrainIntervalConclusion

/--
WZ1 Lemma 19, one-scale local AD structure.

The interval estimate is iterated over finitely many intermediate radii.  The
result is the complete `IsADSet1` bound at one selected spatial scale `rho`.
-/
def WZ1LocalGrainOneScaleConclusion : Prop :=
  ∀ sigma outputLoss : ℝ,
      0 < sigma → sigma < 1 →
      0 < outputLoss →
      HasCriticalVolumeFloor sigma →
        ∃ inputLoss delta₀ : ℝ,
          0 < inputLoss ∧ inputLoss ≤ outputLoss ∧
          0 < delta₀ ∧ delta₀ ≤ 1 ∧
          ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
            ∀ F : Kakeya.Streamlined.TubeFamily delta,
              ∀ U : Kakeya.Streamlined.UniformTubeStructure F,
                ∀ Y : Kakeya.Streamlined.TubeShading F,
                  WZ1ExtremalPair sigma inputLoss F U Y →
                  ∀ plane : WZ1PlaneMapData Y,
                    (plane.lipschitzConstant : ENNReal) ≤
                      Kakeya.realRpowENN delta (-inputLoss) →
                    ∀ rho :
                        Kakeya.Streamlined.AdmissibleScale delta,
                      Real.rpow delta (1 - outputLoss) ≤ rho.1 →
                      rho.1 ≤ Real.rpow delta outputLoss →
                        Nonempty
                          (WZ1LocalGrainOneScaleData
                            (sigma := sigma)
                            (outputLoss := outputLoss)
                            U Y plane rho)

/-- WZ1 Lemma 19 assembled from the direct interval conclusion. -/
def WZ1LocalGrainOneScaleStatement : Prop :=
  WZ1LocalGrainIntervalConclusion →
    WZ1LocalGrainOneScaleConclusion

/--
WZ1 Lemma 20, every-scale local grains.

Finite iteration of Lemma 19 and the elementary transfers between adjacent
scales produce one extremal subshading on which the unchanged Lipschitz plane
map has the local AD property for every `rho ∈ [delta,1]`.
-/
def WZ1EveryScaleLocalGrainConclusion : Prop :=
  ∀ sigma outputLoss : ℝ,
      0 < sigma → sigma < 1 →
      0 < outputLoss →
      HasCriticalVolumeFloor sigma →
        ∃ inputLoss delta₀ : ℝ,
          0 < inputLoss ∧ inputLoss ≤ outputLoss ∧
          0 < delta₀ ∧ delta₀ ≤ 1 ∧
          ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
            ∀ F : Kakeya.Streamlined.TubeFamily delta,
              ∀ U : Kakeya.Streamlined.UniformTubeStructure F,
                ∀ Y : Kakeya.Streamlined.TubeShading F,
                  WZ1ExtremalPair sigma inputLoss F U Y →
                  ∀ plane : WZ1PlaneMapData Y,
                    (plane.lipschitzConstant : ENNReal) ≤
                      Kakeya.realRpowENN delta (-inputLoss) →
                      Nonempty
                        (WZ1EveryScaleLocalGrainData
                          (sigma := sigma)
                          (outputLoss := outputLoss)
                          U Y plane)

/-- WZ1 Lemma 20 assembled from the direct one-scale conclusion. -/
def WZ1EveryScaleLocalGrainStatement : Prop :=
  WZ1LocalGrainOneScaleConclusion →
    WZ1EveryScaleLocalGrainConclusion

/--
WZ1 Lemma 12, coarse plane-map construction from the balanced cover.

The fine plane map is sampled at the selected representative of each balanced
cell.  Projective direction alignment contributes `4 * rho` and the fine
incidence premise contributes `rho`, giving the repository-normalized coarse
incidence scale `5 * rho`.
-/
def WZ1CoarsePlaneMapConclusion : Prop :=
  ∀ {delta sigma epsilon : ℝ},
      ∀ {F : Kakeya.Streamlined.TubeFamily delta},
        ∀ {U : Kakeya.Streamlined.UniformTubeStructure F},
          ∀ {Y : Kakeya.Streamlined.TubeShading F},
            ∀ {rho : Kakeya.Streamlined.AdmissibleScale delta},
              ∀ balanced :
                  WZ1BalancedCoverData
                    (sigma := sigma) (epsilon := epsilon) U Y rho,
                ∀ finePlaneMap : Point3 → Point3,
                  Measurable finePlaneMap →
                  (∀ p ∈ balanced.refined.union,
                    ‖finePlaneMap p‖ = 1) →
                  (∀ i p, p ∈ balanced.refined.carrier i →
                    |inner ℝ (F.tube i).direction
                      (finePlaneMap p)| ≤ rho.1) →
                    Nonempty
                      (WZ1CoarsePlaneMapData
                        (incidenceScale := 5 * rho.1)
                        balanced finePlaneMap)

/-- Assemble the direct Lemma 12 coarse plane-map output. -/
def WZ1CoarsePlaneMapStatement : Prop :=
  WZ1CoarseDirectionIncidenceStatement →
    WZ1CoarsePlaneMapConclusion

/--
Finite two-step adapter for the OSW radial bootstrap used in the WZ1
projection theorem that upgrades the global grain slope to `C²`.  The local
grain Lemmas 17--20 do not use OSW.  The OSW theorem itself is supplied
exactly as an ordinary hypothesis.
-/
def WZ1RadialBootstrapTwoStepsStatement : Prop :=
  RadialBootstrappingMeasureThinTubesInput →
    ∀ β ε : ℝ, 0 < β → 0 < ε →
      ∃ τ : ℝ, 0 < τ ∧
        ∃ M : ℝ, 1 ≤ M ∧
          ∀ (σ c K C : ℝ)
              (ν₁ ν₂ :
                ProbabilityMeasure (EuclideanSpace ℝ (Fin 2))),
            (ν₁ : Measure (EuclideanSpace ℝ (Fin 2))).support ⊆
                Metric.closedBall 0 1 →
            (ν₂ : Measure (EuclideanSpace ℝ (Fin 2))).support ⊆
                Metric.closedBall 0 1 →
            σ ∈ Set.Icc β (1 - ε - τ) →
            c ∈ Set.Ioo (0 : ℝ) (1 / 30) →
            1 ≤ K → 1 ≤ C →
            (1 : ℝ) / 2 ≤
              sInf {d : ℝ |
                ∃ x ∈
                    (ν₁ : Measure
                      (EuclideanSpace ℝ (Fin 2))).support,
                  ∃ y ∈
                      (ν₂ : Measure
                        (EuclideanSpace ℝ (Fin 2))).support,
                    dist x y = d} →
            (∀ (x : EuclideanSpace ℝ (Fin 2)) (r : ℝ), 0 < r →
              ν₁ (Metric.ball x r) ≤ Real.toNNReal (C * r)) →
            (∀ (x : EuclideanSpace ℝ (Fin 2)) (r : ℝ), 0 < r →
              ν₂ (Metric.ball x r) ≤ Real.toNNReal (C * r)) →
            HasMeasureThinTubes σ K c ν₁ ν₂ →
            HasMeasureThinTubes σ K c ν₂ ν₁ →
              let K₁ : ℝ :=
                Real.rpow (max K (C ^ 2 * M / c)) M
              let K₂ : ℝ :=
                Real.rpow (max K₁ (C ^ 2 * M / (3 * c))) M
              HasMeasureThinTubes (σ + 2 * τ) K₂ (9 * c) ν₁ ν₂ ∧
                HasMeasureThinTubes (σ + 2 * τ) K₂ (9 * c) ν₂ ν₁

/--
Finite discretized form of WZ1 Theorem 22.

The only external hypothesis is the OSW radial bootstrap.  Every other step
in the paper's Section 8 argument—measure discretization, the initial
one-quarter thin-tube estimate, finite iteration, Kaufman projection, and
two-ends localization—belongs to this WZ1-owned statement.

The original theorem assumes AD sets.  For delta-separated representatives,
its absolute covering upper bound is the Katz--Tao predicate below, not the
normalized Frostman predicate used by the stronger intermediate Theorem 22′.
The final reduction from Theorem 22′ must handle the small-cardinality
vacuous-B case before normalizing the remaining vertex classes.

Conclusion A finds one affine strip carrying many points of both `G₁` and
`G₂`, and the orthogonal origin-centered strip carrying many points of `F`.
Conclusion B gives the long-interval covering lower bound for every sufficiently
large tripartite dot-difference graph.
-/
def WZ1ProjectionDichotomyConclusion : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon →
    ∃ eta delta₀ : ℝ,
      0 < eta ∧ 0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
        ∀ F G₁ G₂ : DiscreteSet 2,
          F.Nonempty → G₁.Nonempty → G₂.Nonempty →
          F.IsInUnitBall → G₁.IsInUnitBall → G₂.IsInUnitBall →
          F.IsDeltaSeparated delta →
          G₁.IsDeltaSeparated delta →
          G₂.IsDeltaSeparated delta →
          F.IsKatzTao delta 1
            (Kakeya.realRpowENN delta (-eta)) →
          G₁.IsKatzTao delta 1
            (Kakeya.realRpowENN delta (-eta)) →
          G₂.IsKatzTao delta 1
            (Kakeya.realRpowENN delta (-eta)) →
            (∃ base direction : Point2,
                ‖direction‖ = 1 ∧
                Kakeya.realRpowENN delta (epsilon - 1) ≤
                  wz1DiscreteLineCount
                    F 0 (wz1Perp2 direction) delta ∧
                Kakeya.realRpowENN delta (epsilon - 1) ≤
                  wz1DiscreteLineCount
                    G₁ base direction delta ∧
                Kakeya.realRpowENN delta (epsilon - 1) ≤
                  wz1DiscreteLineCount
                    G₂ base direction delta) ∨
              (∀ H : Finset (Point2 × Point2 × Point2),
                (∀ h ∈ H,
                  h.1 ∈ F ∧ h.2.1 ∈ G₁ ∧ h.2.2 ∈ G₂) →
                Kakeya.realRpowENN delta (eta - 3) ≤
                  (H.card : ENNReal) →
                  ∃ rho center radius : ℝ,
                    delta ≤ rho ∧ rho ≤ 1 ∧
                    0 < radius ∧
                    Real.rpow delta (-eta) * rho ≤
                      2 * radius ∧
                    (Kakeya.realRpowENN (2 * radius / rho)
                      (1 - epsilon)) ≤
                      (↑(Metric.externalCoveringNumber
                        (Real.toNNReal rho)
                        (wz1DotDifferenceSet H ∩
                          Metric.closedBall center radius)) : ENNReal))

/-- The OSW radial bootstrap implies the fully internal finite dichotomy. -/
def WZ1ProjectionDichotomyStatement : Prop :=
  RadialBootstrappingMeasureThinTubesInput →
    WZ1ProjectionDichotomyConclusion

/--
WZ1 Lemma 28 with its absolute extension constant fixed.
-/
def WZ1SmoothSegmentExtensionAtConstantStatement (A : ℝ) : Prop :=
  1 ≤ A ∧
    ∀ x₁ x₂ y₁ y₂ a : ℝ,
      x₁ < x₂ → 0 < a →
        ∃ G : SlopeFunction,
          (∀ x ∈ Set.Icc x₁ x₂,
            G x = y₁ + (x - x₁) * ((y₂ - y₁) / (x₂ - x₁))) ∧
          (∀ x ∉ Set.Icc (x₁ - a) (x₂ + a), G x = 0) ∧
          (∀ x : ℝ,
            |deriv G x| ≤
              A * ((|y₁| + |y₂|) / a +
                |(y₂ - y₁) / (x₂ - x₁)|)) ∧
          (∀ x : ℝ,
            |deriv (deriv G) x| ≤
              A * ((|y₁| + |y₂|) / a ^ 2 +
                |(y₂ - y₁) / (x₂ - x₁)| / a))

/--
WZ1 Lemma 28, smooth patching leaf.  A line segment can be extended to a
compactly supported global `C²` function with one uniform absolute constant.
-/
def WZ1SmoothSegmentExtensionStatement : Prop :=
  ∃ A : ℝ, WZ1SmoothSegmentExtensionAtConstantStatement A

/--
WZ1 Proposition 27 finite `C²` assembly, in the exact form needed to fill the
`global_grains` field of `WZ1C2GrainPackage`.

The segment-extension theorem is an explicit predecessor.  The disjoint
expanded supports are the paper's same-scale separation condition.  The three
finite cost bounds are the quantitative smallness obtained from the nested
trapezoid hierarchy after the final mild rescaling.
-/
def WZ1GlobalGrainsFromSegmentsAtConstantStatement (A : ℝ) : Prop :=
  1 ≤ A ∧
    ∀ {delta sigma : ℝ},
      ∀ {F : Kakeya.Streamlined.TubeFamily delta},
        ∀ {Y : Kakeya.Streamlined.TubeShading F},
          ∀ {C : ENNReal},
            ∀ segments : Finset WZ1SegmentCorrection,
              (∀ segment ∈ segments, ∀ other ∈ segments,
                segment ≠ other →
                  Disjoint segment.support other.support) →
              (∀ z ∈ Set.Icc (-1 : ℝ) 1,
                (∀ segment ∈ segments,
                  z ∈ segment.core ∨ z ∉ segment.support) ∨
                  horizontalSlice Y.union z = ∅) →
              (∑ segment ∈ segments, segment.valueCost ≤ 1 / A) →
              (∑ segment ∈ segments, segment.firstCost ≤ 1 / A) →
              (∑ segment ∈ segments, segment.secondCost ≤ 1 / A) →
              HasGlobalSlabAD Y
                (fun z =>
                  ∑ segment ∈ segments, segment.value z)
                sigma C →
                Nonempty (WZ1GlobalGrainData Y sigma C)

/-- Existential constant wrapper around the fixed-constant Proposition 27 core. -/
def WZ1GlobalGrainsFromSegmentsStatement : Prop :=
  WZ1SmoothSegmentExtensionStatement →
    ∃ A : ℝ, WZ1GlobalGrainsFromSegmentsAtConstantStatement A

/--
Pure Proposition 27 assembly on the output of Corollary 26.

All geometric work is already present in `package.corrections`; this theorem
only calls the closed segment-extension assembler and returns normalized
global `C²` grain data on the same shading.
-/
def WZ1GlobalGrainsFromNestedCorrectionsStatement : Prop :=
  ∀ {sigma inputLoss outputLoss delta A : ℝ},
    WZ1GlobalGrainsFromSegmentsAtConstantStatement A →
    ∀ {source :
        WZ1PlaninessGraininessPackage
          sigma inputLoss delta},
      ∀ package :
          WZ1NestedSlopeCorrectionPackage source outputLoss A,
        Nonempty
          (WZ1GlobalGrainData
            package.shading sigma source.constant)

/--
Paper-faithful Proposition 27 assembly from a level-indexed Corollary 26
hierarchy.

Unlike `WZ1GlobalGrainsFromSegmentsAtConstantStatement`, this theorem does
not assume that the source configuration is already normalized.  It sums the
Lemma 28 extensions, uses within-level support separation to bound only the
active correction at each height, and returns the raw power-size `C²` bounds
that Proposition 21 subsequently rescales.
-/
def WZ1RawGlobalGrainsFromMultiscaleCorrectionsStatement : Prop :=
  ∀ A : ℝ,
    WZ1SmoothSegmentExtensionAtConstantStatement A →
      ∀ {sigma inputLoss outputLoss delta : ℝ},
      ∀ {source :
          WZ1PlaninessGraininessPackage
            sigma inputLoss delta},
        ∀ package :
            WZ1MultiscaleSlopeCorrectionPackage source outputLoss,
          Nonempty
            (WZ1RawGlobalGrainData
              package.shading sigma source.constant
              package.rawLoss A)

/--
Same-configuration producer for the complete WZ1 planiness/graininess and
global `C²` output.  The completed CV broad-set theorem is available directly;
the still-external OSW theorem remains an explicit hypothesis.
-/
def WZ1C2GrainPackageStatement : Prop :=
  RadialBootstrappingMeasureThinTubesInput →
    ∀ sigma : ℝ, 0 < sigma → sigma < 1 →
      HasExtremalCounterexampleSequence sigma →
      HasCriticalVolumeFloor sigma →
        ∀ epsilon delta₀ : ℝ,
          0 < epsilon → 0 < delta₀ →
            ∃ delta : ℝ, 0 < delta ∧ delta ≤ delta₀ ∧
              Nonempty (WZ1C2GrainPackage sigma epsilon delta)

/-- The complete WZ1 package implies the legacy WZ2 input boundary. -/
def WZ1C2GrainPackageToInputStatement : Prop :=
  RadialBootstrappingMeasureThinTubesInput →
    WZ1C2GrainPackageStatement →
      C2GrainsInput

end Kakeya.Assouad
