import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ProjectedFiberPullbackMassStatement
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ProjectedFiberPullbackMassHelpers

/-!
WZ2 Section 7: identify the mass of a planar projection pullback with the
fiber-multiplicity integral over the selected planar set.
-/

namespace Kakeya.Assouad

theorem projected_fiber_pullback_mass :
    ProjectedFiberPullbackMassStatement := by
  intro delta F Y f X hX
  let S : Set Point3 := twistedProjection f ⁻¹' X
  have hS : MeasurableSet S :=
    hX.preimage (continuous_twistedProjection f).measurable
  have h1 : (projectionPullbackShading Y f X hX).mass =
      ∫⁻ p in S, (Y.pointMultiplicity p : ENNReal) := by
    calc
      (projectionPullbackShading Y f X hX).mass
        = ∑ i : Fin F.toBodyFamily.card,
            MeasureTheory.volume ((projectionPullbackShading Y f X hX).carrier i) := rfl
      _ = ∑ i : Fin F.toBodyFamily.card,
            MeasureTheory.volume (Y.carrier i ∩ S) := by
          apply Finset.sum_congr rfl
          intro i _
          rfl
      _ = ∫⁻ p in S, (Y.pointMultiplicity p : ENNReal) :=
          sum_volume_inter_eq_setLIntegral_pointMultiplicity Y hS
  rw [h1]
  exact projectedFiberPullbackMass_identity Y f X hX

end Kakeya.Assouad
