import MyLeanRepo.Kakeya.Streamlined.DilatedCoverUniformization
import MyLeanRepo.Kakeya.Streamlined.TubeRefinement

/-!
# Assigned-fiber profiles for a dilated tube cover

These definitions are geometric data attached to one `DilatedTubeCover`.
They live below the one-scale profile-uniformization assembly so that
paper-level hypotheses may refer to dilated all-scale structures without
importing the higher Section 2 proof graph.
-/

noncomputable section

namespace Kakeya.Streamlined

namespace DilatedTubeCover

/--
Deprecated compatibility name for the cardinality of an assigned bookkeeping
fiber. Paper-facing code must use `fullContainmentFiberCount` instead.
-/
abbrev fiberCount
    {delta rho A : ℝ}
    {fine : TubeFamily delta} {coarse : TubeFamily rho}
    (P : DilatedTubeCover A fine coarse)
    (j : Fin coarse.card) : ENNReal :=
  P.toFactoring.fiberCount j

/-- The complete assigned fine fiber of one parent. -/
def assignedFiberSubfamily
    {delta rho A : ℝ}
    {fine : TubeFamily delta} {coarse : TubeFamily rho}
    (P : DilatedTubeCover A fine coarse)
    (j : Fin coarse.card) : TubeSubfamily fine :=
  TubeSubfamily.fromFinset fine (P.toFactoring.fiberIndices j)

/-- Frostman profile of one complete assigned fine fiber. -/
def assignedFiberFrostmanConstant
    {delta rho A : ℝ}
    {fine : TubeFamily delta} {coarse : TubeFamily rho}
    (P : DilatedTubeCover A fine coarse)
    (j : Fin coarse.card) : ENNReal :=
  (P.assignedFiberSubfamily j).family.toBodyFamily.frostmanConstantIn
    (dilatedTubeCarrier A (coarse.tube j))

/-- Maximal-density profile of one complete assigned fine fiber. -/
def assignedFiberDeltaMax
    {delta rho A : ℝ}
    {fine : TubeFamily delta} {coarse : TubeFamily rho}
    (P : DilatedTubeCover A fine coarse)
    (j : Fin coarse.card) : ENNReal :=
  (P.assignedFiberSubfamily j).family.toBodyFamily.deltaMax

end DilatedTubeCover

end Kakeya.Streamlined

end
