import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12
import MyLeanRepo.Kakeya.Assouad.Targets.CoaxialShiftedTubesEssentiallyDistinct
import MyLeanRepo.Kakeya.Assouad.Targets.RepresentativeTubeFourCoverAtScale
import MyLeanRepo.Kakeya.Assouad.TubeVolumeScaling
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.NonessentialTubeAxisAlignment
import MyLeanRepo.Kakeya.Streamlined.VolumeHelpers

/-!
# Analytic conflict degree from public body CWA

For one radius-`delta` tube, every tube that is not essentially distinct from
it in the Assertion-D volume-overlap sense lies in a common convex envelope.
The envelope is the union of four coaxial tubes at radius `3000 * delta` and
has volume at most `972000000 * delta^2`.  The public body Convex-Wolff bound
therefore controls the entire analytic conflict neighborhood.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

/--
The broad Assertion-D conflict neighborhood of every indexed tube has size at
most `C * 972000000 * delta^2 * #family`.

No unit-ball hypothesis and no assigned-fiber data are used.
-/
theorem pure_wz2_analytic_conflict_degree_from_body_cwa
    {delta : ℝ}
    (hdelta : 0 < delta)
    (hscaleSmall : 3000 * delta ≤ 1 / 8)
    {family : Kakeya.Streamlined.TubeFamily delta}
    {C : ENNReal}
    (hCWA : WZ2PaperBodyConvexWolffBound family.toBodyFamily C) :
    ∀ index,
      ((Finset.univ.filter fun other =>
        ¬(family.tube index).EssentiallyDistinct
          (family.tube other)).card : ENNReal) ≤
        C * ENNReal.ofReal (972000000 * delta ^ 2) *
          family.enncard := by
  intro index
  have hcover :
      RepresentativeTubeFourCoverAtScaleConclusion :=
    representative_tube_four_cover_at_scale
      nonessential_tube_axis_alignment
      coaxial_shifted_tubes_essentially_distinct
      tube_volume_scaling
  rcases
      hcover delta (3000 * delta) hdelta le_rfl hscaleSmall
        (family.tube index) with
    ⟨coarse, envelope, _hcoarseCard, _hcoarseDistinct,
      _haxis, _hvertical, _hbase, _henvelopeCarrier,
      _henvelopeMeasurable, henvelopeConvex,
      henvelopeDimensions, hcontains⟩
  let conflicts : Finset (Fin family.card) :=
    Finset.univ.filter fun other =>
      ¬(family.tube index).EssentiallyDistinct
        (family.tube other)
  have hsubset :
      conflicts ⊆ family.toBodyFamily.containedIndices envelope.carrier := by
    intro other hother
    have hconflict :
        ¬(family.tube index).EssentiallyDistinct
          (family.tube other) := by
      simpa [conflicts] using hother
    have hconflictSymm :
        ¬(family.tube other).EssentiallyDistinct
          (family.tube index) := by
      simpa [Kakeya.DeltaTube.EssentiallyDistinct,
        Set.inter_comm, max_comm] using hconflict
    exact
      Kakeya.Streamlined.BodyFamily.mem_containedIndices_iff.mpr
        (hcontains (family.tube other) hconflictSymm)
  have hcount :
      (conflicts.card : ENNReal) ≤
        family.toBodyFamily.containedCount envelope.carrier := by
    change
      (conflicts.card : ENNReal) ≤
        ((family.toBodyFamily.containedIndices envelope.carrier).card :
          ENNReal)
    exact_mod_cast Finset.card_le_card hsubset
  have hcwa :
      family.toBodyFamily.containedCount envelope.carrier ≤
        C * MeasureTheory.volume envelope.carrier *
          family.enncard :=
    hCWA envelope.carrier henvelopeConvex
  have henvelopeVolume :
      MeasureTheory.volume envelope.carrier ≤
        ENNReal.ofReal (972000000 * delta ^ 2) := by
    rcases henvelopeDimensions with ⟨frame, hdimensionsInFrame⟩
    have hvolume :=
      Kakeya.Streamlined.hasDimensionsInFrame_volume_upper
        hdimensionsInFrame
    have harithmetic :
        (3 : ℝ) ^ 3 * (3000 * delta) *
            (3000 * delta) * 4 =
          972000000 * delta ^ 2 := by
      ring
    change
      MeasureTheory.volume envelope.carrier ≤
        ENNReal.ofReal
          ((3 : ℝ) ^ 3 * (3000 * delta) *
            (3000 * delta) * 4) at hvolume
    rw [harithmetic] at hvolume
    exact hvolume
  calc
    ((Finset.univ.filter fun other =>
        ¬(family.tube index).EssentiallyDistinct
          (family.tube other)).card : ENNReal) =
        (conflicts.card : ENNReal) := by rfl
    _ ≤ family.toBodyFamily.containedCount envelope.carrier :=
      hcount
    _ ≤ C * MeasureTheory.volume envelope.carrier *
          family.enncard :=
      hcwa
    _ ≤ C * ENNReal.ofReal (972000000 * delta ^ 2) *
          family.enncard := by
      gcongr

end Kakeya.Assouad

end
