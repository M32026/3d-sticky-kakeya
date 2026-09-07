import Comparator.Statements.JohnEllipsoid
import Comparator.Statements.Families

noncomputable section

open MeasureTheory

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

abbrev WZ2PaperRequestedScale (delta : ℝ) :=
  {rho : ℝ // delta ≤ rho ∧ rho ≤ 1}

def wz2PaperTubeMidpoint
    {rho : ℝ} (tube : Kakeya.DeltaTube rho) : Point3 :=
  tube.base + (1 / 2 : ℝ) • tube.direction

def wz2PaperCenteredDilatedCarrier
    {rho : ℝ} (factor : ℝ) (tube : Kakeya.DeltaTube rho) :
    Set Point3 :=
  AffineMap.homothety (wz2PaperTubeMidpoint tube) factor ''
    tube.carrier

def wz2PaperOrdinaryFullFiberIndices
    {delta rho : ℝ}
    (fine : Kakeya.Streamlined.TubeFamily delta)
    (coarse : Kakeya.Streamlined.TubeFamily rho)
    (parent : Fin coarse.card) : Finset (Fin fine.card) :=
  Finset.univ.filter fun source =>
    (fine.tube source).carrier ⊆ (coarse.tube parent).carrier

def wz2PaperOrdinaryDilatedFiberIndices
    (factor : ℝ)
    {delta rho : ℝ}
    (fine : Kakeya.Streamlined.TubeFamily delta)
    (coarse : Kakeya.Streamlined.TubeFamily rho)
    (parent : Fin coarse.card) : Finset (Fin fine.card) :=
  Finset.univ.filter fun source =>
    (fine.tube source).carrier ⊆
      wz2PaperCenteredDilatedCarrier factor (coarse.tube parent)

def wz2PaperOrdinaryFullFiberCount
    {delta rho : ℝ}
    (fine : Kakeya.Streamlined.TubeFamily delta)
    (coarse : Kakeya.Streamlined.TubeFamily rho)
    (parent : Fin coarse.card) : ENNReal :=
  (wz2PaperOrdinaryFullFiberIndices fine coarse parent).card

def WZ2PaperOrdinaryIsEssentiallyDistinct
    {rho : ℝ}
    (family : Kakeya.Streamlined.TubeFamily rho) : Prop :=
  ∀ first second, first ≠ second →
    ¬(family.tube first).carrier ⊆
        wz2PaperCenteredDilatedCarrier 2 (family.tube second) ∧
      ¬(family.tube second).carrier ⊆
        wz2PaperCenteredDilatedCarrier 2 (family.tube first)

def WZ2PaperFiniteErrorConstant (C : ENNReal) : Prop :=
  1 ≤ C ∧ C ≠ ⊤

def WZ2PaperPureFullFibersAreCUniform
    {delta rho : ℝ}
    (fine : Kakeya.Streamlined.TubeFamily delta)
    (coarse : Kakeya.Streamlined.TubeFamily rho)
    (C : ENNReal) : Prop :=
  ∀ first second,
    wz2PaperOrdinaryFullFiberCount fine coarse first ≤
      C * wz2PaperOrdinaryFullFiberCount fine coarse second

structure WZ2PaperPurePartitioningCover
    {delta rho : ℝ}
    (fine : Kakeya.Streamlined.TubeFamily delta)
    (coarse : Kakeya.Streamlined.TubeFamily rho) : Prop where
  covers :
    ∀ source : Fin fine.card,
      ∃ parent : Fin coarse.card,
        source ∈ wz2PaperOrdinaryFullFiberIndices fine coarse parent
  doubled_fibers_disjoint :
    ∀ first second, first ≠ second →
      Disjoint
        (wz2PaperOrdinaryDilatedFiberIndices 2 fine coarse first)
        (wz2PaperOrdinaryDilatedFiberIndices 2 fine coarse second)

structure WZ2PaperAssouadUnitRescalingData
    {rho : ℝ} (parent : Kakeya.DeltaTube rho) where
  parent_convex_body :
    JohnEllipsoid.IsConvexBody parent.carrier

namespace WZ2PaperAssouadUnitRescalingData

noncomputable def map
    {rho : ℝ} {parent : Kakeya.DeltaTube rho}
    (normalization : WZ2PaperAssouadUnitRescalingData parent) :
    Point3 ≃ᵃ[ℝ] Point3 :=
  AffineEquiv.ofLinearEquiv
    normalization.parent_convex_body.outerJohnEllipsoidMap.symm
    normalization.parent_convex_body.outerJohnEllipsoidCenter
    0

end WZ2PaperAssouadUnitRescalingData

def WZ2PaperBodyConvexWolffBound
    (family : Kakeya.Streamlined.BodyFamily)
    (C : ENNReal) : Prop :=
  ∀ convexSet : Set Point3, Convex ℝ convexSet →
    family.containedCount convexSet ≤
      C * volume convexSet * family.enncard

noncomputable def wz2PaperOrdinaryFullFiberIndexEquiv
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (parent : Fin coarse.card) :
    Fin (wz2PaperOrdinaryFullFiberIndices fine coarse parent).card ≃
      {source : Fin fine.card //
        source ∈
          wz2PaperOrdinaryFullFiberIndices fine coarse parent} :=
  (wz2PaperOrdinaryFullFiberIndices fine coarse parent).orderIsoOfFin rfl
    |>.toEquiv

noncomputable def wz2PaperPureUnitRescaledFullFiberBodyFamily
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (parent : Fin coarse.card)
    (normalization :
      WZ2PaperAssouadUnitRescalingData (coarse.tube parent)) :
    Kakeya.Streamlined.BodyFamily where
  card := (wz2PaperOrdinaryFullFiberIndices fine coarse parent).card
  body target :=
    ⟨normalization.map ''
      (fine.tube
        ((wz2PaperOrdinaryFullFiberIndexEquiv parent) target).1).carrier⟩

structure WZ2PaperPureUnitRescaledFullFiberData
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (parent : Fin coarse.card)
    (C : ENNReal) where
  normalization :
    WZ2PaperAssouadUnitRescalingData (coarse.tube parent)
  convex_wolff :
    WZ2PaperBodyConvexWolffBound
      (wz2PaperPureUnitRescaledFullFiberBodyFamily
        (fine := fine) (coarse := coarse) parent normalization)
      C

structure WZ2PaperPureScaleCoverData
    {delta : ℝ}
    (fine : Kakeya.Streamlined.TubeFamily delta)
    (rho : ℝ)
    (C : ENNReal) where
  delta_pos : 0 < delta
  rho_pos : 0 < rho
  coarse : Kakeya.Streamlined.TubeFamily rho
  cover : WZ2PaperPurePartitioningCover fine coarse
  full_fiber_uniform :
    WZ2PaperPureFullFibersAreCUniform fine coarse C
  rescaledFiber :
    ∀ parent : Fin coarse.card,
      Nonempty
        (WZ2PaperPureUnitRescaledFullFiberData
          (fine := fine) (coarse := coarse) parent C)

structure WZ2PaperPureNearbyScaleCoverData
    {delta : ℝ}
    (family : Kakeya.Streamlined.TubeFamily delta)
    (rho₀ : WZ2PaperRequestedScale delta)
    (C : ENNReal) where
  rho : ℝ
  requested_le : rho₀.1 ≤ rho
  within_factor :
    ENNReal.ofReal rho <
      C * ENNReal.ofReal rho₀.1
  scaleData : WZ2PaperPureScaleCoverData family rho C

def WZ2PaperPureCWAAtNearbyScales
    {delta : ℝ}
    (family : Kakeya.Streamlined.TubeFamily delta)
    (C : ENNReal) : Prop :=
  0 < delta ∧
    WZ2PaperFiniteErrorConstant C ∧
      WZ2PaperOrdinaryIsEssentiallyDistinct family ∧
        ∀ rho₀ : WZ2PaperRequestedScale delta,
          Nonempty (WZ2PaperPureNearbyScaleCoverData family rho₀ C)

end Kakeya.Assouad
