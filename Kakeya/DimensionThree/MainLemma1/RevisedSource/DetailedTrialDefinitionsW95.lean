module

public import Kakeya.DimensionThree.MainLemma1.RevisedSource.TrialEntryLemmasW94
public import Kakeya.ChainUniform
public import Kakeya.PartialEstimates
public import Kakeya.DimensionThree.MainLemma1.LiteralProfileHelpersW93

@[expose] public section

open MeasureTheory ConvexSpaceBody ShadedBody
open scoped ENNReal NNReal

namespace Kakeya.ml1Boot.TrialRestartW94

noncomputable section
set_option autoImplicit false
attribute [local instance] Classical.propDecidable

universe uE uI

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [Nontrivial E]
  [MeasurableSpace E] [BorelSpace E]

open RevisedLiteralProfileInterfaceFormalizerW87

/-- The complete affine-line neighbourhood used in the revised definition. -/
def liesInFiveDeltaLineTubeW94 {d : NNReal} (T : Tube d E) (o v : E) : Prop :=
  ∀ x ∈ T.carrier, ∃ t : Real, dist x (o + t • v) <= 5 * (d : Real)

/-- The source controls entire affine lines, including axial translates. -/
def lineEssentiallyDistinctW94 {iota : Type uI} {d : NNReal}
    (F : Finset iota) (T : iota -> Tube d E) (C : NNReal) : Prop :=
  ∀ o v, ‖v‖ = 1 ->
    ((F.filter (fun i => liesInFiveDeltaLineTubeW94 (T i) o v)).card : NNReal) <= C

def centredTubeW94 {d : NNReal} (T : Tube d E) : Prop :=
  inner Real T.center T.direction = 0

/-- Actual listed parents and complete assigned cells in the detailed
Inner Trial. Nested maps are not an extra hypothesis of that source lemma. -/
structure DetailedTrialCellsW94 {iota : Type uI} [DecidableEq iota] {d : NNReal}
    (F : Finset iota) (Y : iota -> ShadedTube d E) (L : Nat)
    (rho : Nat -> NNReal) (Ctw Ccell : NNReal) where
  rho_zero : rho 0 = 1
  rho_bottom : rho L = d
  rho_pos : ∀ l, l <= L -> 0 < rho l
  rho_nonincreasing : ∀ l, l < L -> rho (l + 1) <= rho l
  rho_step : ∀ l, l < L ->
    (rho l : ENNReal) / (rho (l + 1) : ENNReal) <=
      (d : ENNReal) ^ (-(2 : Real) / (L : Real))
  parentSet : Nat -> Finset iota
  parentTube : (l : Nat) -> iota -> Tube (rho l) E
  assign : Nat -> iota -> iota
  assign_image : ∀ l, l <= L -> F.image (assign l) = parentSet l
  assigned_containment : ∀ l, l <= L -> ∀ i ∈ F,
    (Y i).toConvexSpaceBody <= (parentTube l (assign l i)).toConvexSpaceBody
  parent_ball : ∀ l, l <= L -> ∀ R ∈ parentSet l,
    (parentTube l R).carrier ⊆ Metric.closedBall 0 2
  parent_line_ed : ∀ l, l <= L ->
    lineEssentiallyDistinctW94 (parentSet l) (parentTube l) Ctw
  D : Nat -> NNReal
  D_pos : ∀ l, l <= L -> 0 < D l
  geometric_lower : ∀ l, l <= L -> ∀ R ∈ parentSet l,
    D l <= ((exactTubeCellW87 F (fun i => (Y i).toTube) (parentTube l R)).card : NNReal)
  geometric_upper : ∀ l, l <= L -> ∀ R ∈ parentSet l,
    ((exactTubeCellW87 F (fun i => (Y i).toTube) (parentTube l R)).card : NNReal) <
      2 * Ccell * D l
  assigned_lower : ∀ l, l <= L -> ∀ R ∈ parentSet l,
    D l <= ((completeFibreW94 F (assign l) R).card : NNReal)

/-- The actual analytic inputs, with the lower bound on old complete cells. -/
structure DetailedTrialInputW94 {iota : Type uI} [DecidableEq iota] {d : NNReal}
    {F : Finset iota} {Y : iota -> ShadedTube d E} {L : Nat}
    {rho : Nat -> NNReal} {Ctw Ccell : NNReal}
    (cells : DetailedTrialCellsW94 F Y L rho Ctw Ccell)
    (epsilon xi zetaPlus etaLambda : Real) : Prop where
  nonempty : F.Nonempty
  ball : ∀ i ∈ F, (Y i).carrier ⊆ Metric.closedBall 0 1
  centred : ∀ i ∈ F, centredTubeW94 (Y i).toTube
  line_ed : lineEssentiallyDistinctW94 F (fun i => (Y i).toTube) Ctw
  fullness : (d : ENNReal) ^ etaLambda <= fullness' F (fun i => (Y i).toShadedBody)
  frostman : frostmanConstIn F (fun i => (Y i).toConvexSpaceBody)
    ConvexSpaceBody.closedUnitBall <= (d : ENNReal) ^ (-xi / 160)
  complete_cell_lower : ∀ l, l <= L ->
    (d : ENNReal) ^ (1 - 3 * epsilon / 2) <= (rho l : ENNReal) ->
    (rho l : ENNReal) <= (d : ENNReal) ^ (3 * epsilon / 2) ->
    ∀ R ∈ cells.parentSet l,
      (1 / 2 : ENNReal) * ((rho l : ENNReal) / (d : ENNReal)) ^ zetaPlus <
        frostmanConstIn (completeFibreW94 F (cells.assign l) R)
          (fun i => (Y i).toConvexSpaceBody) (cells.parentTube l R).toConvexSpaceBody

/-- The detailed source has constant one in this literal Good alternative. -/
def detailedInnerGoodW94 {iota : Type uI} {d : NNReal}
    (F : Finset iota) (Y : iota -> ShadedTube d E)
    (gamma epsilon xi : Real) : Prop :=
  ShadedBody.multiplicity F (fun i => (Y i).toShadedBody) <=
    (d : ENNReal) ^ (20 * xi / epsilon) * (d : ENNReal) ^ (-2 * gamma) *
      ((d : ENNReal) ^ (2 : Nat) * (F.card : ENNReal)) ^ (1 - gamma / 2)

def trialRetainedFractionW94 (d : NNReal) (Ktr : Nat) : ENNReal :=
  ENNReal.ofReal ((1 + Real.log (1 / (d : Real))) ^ (-(Ktr : Real)))

/-- The same actual refinement witnesses both the per-cell and all-exact
Ns bounds. The new partition is not silently identified with an old cell. -/
structure DetailedTrialDropW94 {iota : Type uI} [DecidableEq iota] {d : NNReal}
    {F : Finset iota} {Y : iota -> ShadedTube d E} {L : Nat}
    {rho : Nat -> NNReal} {Ctw Ccell : NNReal}
    (cells : DetailedTrialCellsW94 F Y L rho Ctw Ccell)
    (epsilon zetaPlus : Real) (Ktr : Nat) where
  level : Fin (L + 1)
  Fplus : Finset iota
  Yplus : iota -> ShadedTube d E
  Fplus_nonempty : Fplus.Nonempty
  Fplus_subset : Fplus ⊆ F
  same_tube : ∀ i ∈ Fplus, (Yplus i).toTube = (Y i).toTube
  subshade : ∀ i ∈ Fplus, (Yplus i).shade ⊆ (Y i).shade
  nodes : Finset iota
  nodes_nonempty : nodes.Nonempty
  nodes_subset : nodes ⊆ cells.parentSet level.val
  assignPlus : iota -> iota
  assignPlus_image : Fplus.image assignPlus = nodes
  assigned_cover : Fplus = nodes.biUnion (completeFibreW94 Fplus assignPlus)
  assigned_disjoint : (nodes : Set iota).Pairwise (fun P Q =>
    Disjoint (completeFibreW94 Fplus assignPlus P) (completeFibreW94 Fplus assignPlus Q))
  assigned_containment : ∀ P ∈ nodes,
    completeFibreW94 Fplus assignPlus P ⊆
      exactTubeCellW87 F (fun i => (Y i).toTube) (cells.parentTube level.val P)
  card_le : Fplus.card <= F.card
  mass_retention : trialRetainedFractionW94 d Ktr * (∑ i ∈ F, volume (Y i).shade) <=
    ∑ i ∈ Fplus, volume (Yplus i).shade
  per_cell_density_drop : ∀ P ∈ nodes,
    Kakeya.maxDensity (completeFibreW94 Fplus assignPlus P)
        (fun i => (Yplus i).toConvexSpaceBody) <=
      (d : ENNReal) ^ (epsilon * zetaPlus / 4) *
        allExactTubeNsW87 F (fun i => (Y i).toTube) (rho level.val)
  exact_Ns_drop : allExactTubeNsW87 Fplus (fun i => (Yplus i).toTube) (rho level.val) <=
    (d : ENNReal) ^ (epsilon * zetaPlus / 8) *
      allExactTubeNsW87 F (fun i => (Y i).toTube) (rho level.val)

/-- This is an output specification of the actual threshold construction.
No producer theorem below takes it as an analytic callback. -/
def detailedTrialAtThresholdW94
    (gamma epsilon xi zetaPlus : Real) (Ctw Ccell : NNReal) (L : Nat)
    (etaLambda : Real) (d0 : NNReal) (Ktr : Nat) : Prop :=
  ∀ {d : NNReal}, 0 < d -> d < d0 ->
    ∀ {iota : Type uI} [DecidableEq iota]
      (F : Finset iota) (Y : iota -> ShadedTube d E) (rho : Nat -> NNReal)
      (cells : DetailedTrialCellsW94 F Y L rho Ctw Ccell),
      DetailedTrialInputW94 cells epsilon xi zetaPlus etaLambda ->
      detailedInnerGoodW94 F Y gamma epsilon xi ∨
        Nonempty (DetailedTrialDropW94 cells epsilon zetaPlus Ktr)

/-- A label uses zeta_(m+1), with its own returned threshold and loss.
This schedule is construction output, never an input to the trial theorem. -/
structure LabelledDetailedTrialThresholdsW94 (p : Params)
    (xi : Fin (p.N + 1) -> Real) (gamma : Real) (Ctw Ccell : NNReal) (L : Nat) where
  inner : Fin (p.N + 1) -> Real
  cutoff : Fin (p.N + 1) -> NNReal
  Ktr : Fin (p.N + 1) -> Nat
  inner_pos : ∀ m, 0 < inner m
  cutoff_pos : ∀ m, 0 < cutoff m
  cutoff_lt_one : ∀ m, cutoff m < 1
  Ktr_pos : ∀ m, 1 <= Ktr m
  actual_trial : ∀ m, m.val < p.N ->
    detailedTrialAtThresholdW94.{uE, uI} (E := E) gamma p.ε (xi m) (p.η (m.val + 1))
      Ctw Ccell L (inner m) (cutoff m) (Ktr m)


end

end Kakeya.ml1Boot.TrialRestartW94
