module

public import Kakeya.DimensionThree.MainLemma1.RevisedSource.SourceQuotientGridW97
public import Kakeya.Tube.Rescale

@[expose] public section

open MeasureTheory ConvexSpaceBody ShadedBody
open scoped ENNReal NNReal

namespace Kakeya.ml1Boot.TrialRestartW94

noncomputable section
set_option autoImplicit false
attribute [local instance] Classical.propDecidable

universe uE uI

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

open RevisedLiteralProfileInterfaceFormalizerW87

/-- C4 output on one FULL old theta-fibre. The affine map, every old label,
every quotient assignment, and the complete-cell denominator remain visible. -/
structure ActualAssignedUnitNormalizationW97
    {iota : Type uI} [DecidableEq iota] {delta : NNReal}
    {A : Finset iota} {Y : iota -> ShadedTube delta E} {M : Nat} {Ccan : NNReal}
    (U : CanonicalProfileNetW87 A (fun i => (Y i).toTube) M Ccan)
    (Uext : CanonicalProfileNetW87 A (fun i => (Y i).toTube) (M * M) Ccan)
    (a b : Nat) (R : iota) (Z : iota -> ShadedTube (Tube.gridScale delta M b) E)
    (Rnorm Cext Cnorm CtwNorm CcellNorm : NNReal) where
  normalized : iota -> ShadedTube (Tube.gridScale delta M b / Tube.gridScale delta M a) E
  cells : DetailedTrialCellsW94 (actualDescendantsW95 A U.cover.assign a b R)
    normalized M (Tube.gridScale (Tube.gridScale delta M b / Tube.gridScale delta M a) M)
    CtwNorm CcellNorm
  assign_eq : ∀ l, l <= M -> cells.assign l =
    Kakeya.ML2Reduction.coarseNode Uext.cover.toChain (quotientGridIndexW97 M a b l) (b * M)
  parents_eq : ∀ l, l <= M -> cells.parentSet l =
    actualDescendantsW95 A Uext.cover.assign (a * M) (quotientGridIndexW97 M a b l) R
  assigned_eq : ∀ l, l <= M -> ∀ S ∈ cells.parentSet l,
    completeFibreW94 (actualDescendantsW95 A U.cover.assign a b R) (cells.assign l) S =
      actualDescendantsW95 A Uext.cover.assign (quotientGridIndexW97 M a b l) (b * M) S
  ball : ∀ Q ∈ actualDescendantsW95 A U.cover.assign a b R,
    (normalized Q).carrier ⊆ Metric.closedBall 0 1
  centred : ∀ Q ∈ actualDescendantsW95 A U.cover.assign a b R, centredTubeW94 (normalized Q).toTube
  line_ed : lineEssentiallyDistinctW94 (actualDescendantsW95 A U.cover.assign a b R)
    (fun Q => (normalized Q).toTube) CtwNorm
  fine_direction : ∀ Q ∈ actualDescendantsW95 A U.cover.assign a b R,
    let v := ((U.cover.tube a R).rescaleMap (Rnorm : Real)).linear (U.cover.tube b Q).direction
    (normalized Q).toTube.direction = ‖v‖⁻¹ • v
  fine_centre : ∀ Q ∈ actualDescendantsW95 A U.cover.assign a b R,
    let x := (U.cover.tube a R).rescaleMap (Rnorm : Real) (U.cover.tube b Q).center
    (normalized Q).toTube.center = x - inner Real x (normalized Q).toTube.direction •
      (normalized Q).toTube.direction
  image_carrier : ∀ Q ∈ actualDescendantsW95 A U.cover.assign a b R,
    (U.cover.tube a R).rescaleMap (Rnorm : Real) '' (U.cover.tube b Q).carrier ⊆
      (normalized Q).carrier
  image_shade : ∀ Q ∈ actualDescendantsW95 A U.cover.assign a b R,
    (normalized Q).shade = (U.cover.tube a R).rescaleMap (Rnorm : Real) '' (Z Q).shade
  jacobian : NNReal
  jacobian_pos : 0 < jacobian
  jacobian_eq : (jacobian : ENNReal) =
    (4 * (Rnorm : ENNReal)) ^ (-3 : Real) * (Tube.gridScale delta M a : ENNReal) ^ (-2 : Real)
  volume_image : ∀ S : Set E, MeasurableSet S ->
    volume ((U.cover.tube a R).rescaleMap (Rnorm : Real) '' S) = (jacobian : ENNReal) * volume S
  carrier_volume : ∀ Q ∈ actualDescendantsW95 A U.cover.assign a b R,
    (jacobian : ENNReal) * volume (U.cover.tube b Q).carrier <= volume (normalized Q).carrier ∧
    volume (normalized Q).carrier <= (Cext : ENNReal) * (jacobian : ENNReal) *
      volume (U.cover.tube b Q).carrier
  parent_image : ∀ l, l <= M -> ∀ S ∈ cells.parentSet l,
    (U.cover.tube a R).rescaleMap (Rnorm : Real) ''
      (Uext.cover.tube (quotientGridIndexW97 M a b l) S).carrier ⊆ (cells.parentTube l S).carrier
  parent_volume : ∀ l, l <= M -> ∀ S ∈ cells.parentSet l,
    (jacobian : ENNReal) * volume (Uext.cover.tube (quotientGridIndexW97 M a b l) S).carrier <=
      volume (cells.parentTube l S).carrier ∧
    volume (cells.parentTube l S).carrier <= (Cext : ENNReal) * (jacobian : ENNReal) *
      volume (Uext.cover.tube (quotientGridIndexW97 M a b l) S).carrier
  forward_test : ∀ K : ConvexSpaceBody E, ∃ D : ConvexSpaceBody E,
    volume D.carrier <= (Cext : ENNReal) * (jacobian : ENNReal) * volume K.carrier ∧
    (∀ Q ∈ actualDescendantsW95 A U.cover.assign a b R,
      (U.cover.tube b Q).toConvexSpaceBody <= K -> (normalized Q).toConvexSpaceBody <= D)
  backward_test : ∀ K : ConvexSpaceBody E, ∃ D : ConvexSpaceBody E,
    volume D.carrier <= (Cext : ENNReal) * (jacobian : ENNReal)⁻¹ * volume K.carrier ∧
    (∀ Q ∈ actualDescendantsW95 A U.cover.assign a b R,
      (normalized Q).toConvexSpaceBody <= K -> (U.cover.tube b Q).toConvexSpaceBody <= D)
  whole_cf :
    (Cnorm : ENNReal)⁻¹ * actualRelativeFrostmanW95 A U.cover.assign U.cover.tube a b R <=
      frostmanConstIn (actualDescendantsW95 A U.cover.assign a b R)
        (fun Q => (normalized Q).toConvexSpaceBody) ConvexSpaceBody.closedUnitBall ∧
    frostmanConstIn (actualDescendantsW95 A U.cover.assign a b R)
      (fun Q => (normalized Q).toConvexSpaceBody) ConvexSpaceBody.closedUnitBall <=
      (Cnorm : ENNReal) * actualRelativeFrostmanW95 A U.cover.assign U.cover.tube a b R
  assigned_cf : ∀ l, l <= M -> ∀ S ∈ cells.parentSet l,
    (Cnorm : ENNReal)⁻¹ * actualRelativeFrostmanW95 A Uext.cover.assign Uext.cover.tube
      (quotientGridIndexW97 M a b l) (b * M) S <=
      frostmanConstIn (completeFibreW94 (actualDescendantsW95 A U.cover.assign a b R) (cells.assign l) S)
        (fun Q => (normalized Q).toConvexSpaceBody) (cells.parentTube l S).toConvexSpaceBody ∧
    frostmanConstIn (completeFibreW94 (actualDescendantsW95 A U.cover.assign a b R) (cells.assign l) S)
      (fun Q => (normalized Q).toConvexSpaceBody) (cells.parentTube l S).toConvexSpaceBody <=
      (Cnorm : ENNReal) * actualRelativeFrostmanW95 A Uext.cover.assign Uext.cover.tube
        (quotientGridIndexW97 M a b l) (b * M) S
  nearby : Nat -> iota -> Finset iota
  nearby_subset : ∀ l, l <= M -> ∀ S ∈ cells.parentSet l, nearby l S ⊆ cells.parentSet l
  nearby_card : ∀ l, l <= M -> ∀ S ∈ cells.parentSet l, ((nearby l S).card : NNReal) <= Cnorm
  complete_cell_cover : ∀ l, l <= M -> ∀ S ∈ cells.parentSet l,
    exactTubeCellW87 (actualDescendantsW95 A U.cover.assign a b R)
      (fun Q => (normalized Q).toTube) (cells.parentTube l S) ⊆
      (nearby l S).biUnion (completeFibreW94 (actualDescendantsW95 A U.cover.assign a b R) (cells.assign l))
  enlarged_denominator : ∀ l, l <= M -> ∀ S ∈ cells.parentSet l,
    ∀ D : ConvexSpaceBody E, (cells.parentTube l S).toConvexSpaceBody <= D ->
      volume D.carrier <= (Cext : ENNReal) * volume (cells.parentTube l S).carrier ->
      ((familyIn (actualDescendantsW95 A U.cover.assign a b R)
          (fun Q => (normalized Q).toConvexSpaceBody) D).card : NNReal) <=
        Cnorm * ((completeFibreW94 (actualDescendantsW95 A U.cover.assign a b R) (cells.assign l) S).card : NNReal)
  fullness : (Cext : ENNReal)⁻¹ * fullness' (actualDescendantsW95 A U.cover.assign a b R)
      (fun Q => (Z Q).toShadedBody) <=
    fullness' (actualDescendantsW95 A U.cover.assign a b R) (fun Q => (normalized Q).toShadedBody)
  multiplicity : ShadedBody.multiplicity (actualDescendantsW95 A U.cover.assign a b R)
      (fun Q => (normalized Q).toShadedBody) =
    ShadedBody.multiplicity (actualDescendantsW95 A U.cover.assign a b R) (fun Q => (Z Q).toShadedBody)


end

end Kakeya.ml1Boot.TrialRestartW94
