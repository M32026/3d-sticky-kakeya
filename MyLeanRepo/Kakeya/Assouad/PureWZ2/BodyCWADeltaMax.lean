import MyLeanRepo.Kakeya.Assouad.PureWZ2.PublicCWAAnalyticConflictDegree
import MyLeanRepo.Kakeya.Assouad.TubeVolumeLowerBound
import MyLeanRepo.Kakeya.Streamlined.Estimates

/-!
# Delta-max consequences of public body CWA

For an equal-radius indexed tube family, body Convex-Wolff counting bounds
the maximal contained-mass density by `C * #F * |T|`.

After a Bernoulli thinning has reduced `deltaMax`, the four-tube analytic
conflict envelope gives a conflict-degree bound depending only on that new
`deltaMax`, with no ambient-cardinality factor.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

/-- Body CWA controls the maximal convex-set mass density. -/
theorem pure_wz2_deltaMax_le_of_body_cwa
    {delta : ℝ}
    (hdelta : 0 < delta)
    (hdeltaOne : delta ≤ 1)
    {family : Kakeya.Streamlined.TubeFamily delta}
    {C : ENNReal}
    (hCtop : C ≠ ⊤)
    (hCWA : WZ2PaperBodyConvexWolffBound family.toBodyFamily C) :
    family.toBodyFamily.deltaMax ≤
      C * family.enncard * Kakeya.deltaTubeVolume delta := by
  let tubeVolume : ENNReal := Kakeya.deltaTubeVolume delta
  have htubeVolumeTop : tubeVolume ≠ ⊤ :=
    (tube_volume_scaling.2.1 delta hdelta hdeltaOne).2
  have hboundTop :
      C * family.enncard * tubeVolume ≠ ⊤ := by
    exact
      ENNReal.mul_ne_top
        (ENNReal.mul_ne_top hCtop (by
          change (family.card : ENNReal) ≠ ⊤
          simp))
        htubeVolumeTop
  rw [Kakeya.Streamlined.BodyFamily.deltaMax]
  apply csSup_le
  · exact
      ⟨0, Set.univ, convex_univ, by
        simp [Kakeya.Streamlined.BodyFamily.density]⟩
  · intro density hdensity
    rcases hdensity with ⟨convexSet, hconvex, rfl⟩
    let contained :=
      family.toBodyFamily.containedIndices convexSet
    have hvolume :
        ∀ index : Fin family.card,
          (family.toBodyFamily.body index).volume = tubeVolume := by
      intro index
      exact tube_volume_scaling.1 delta (family.tube index)
    have hcontainedMass :
        family.toBodyFamily.containedMass convexSet =
          family.toBodyFamily.containedCount convexSet * tubeVolume := by
      change
        (∑ index ∈ contained,
          (family.toBodyFamily.body index).volume) =
          (contained.card : ENNReal) * tubeVolume
      calc
        (∑ index ∈ contained,
            (family.toBodyFamily.body index).volume) =
            ∑ _index ∈ contained, tubeVolume := by
          apply Finset.sum_congr rfl
          intro index _
          exact hvolume index
        _ = (contained.card : ENNReal) * tubeVolume := by
          simp [Finset.sum_const]
    have hcount :=
      hCWA convexSet hconvex
    have hmass :
        family.toBodyFamily.containedMass convexSet ≤
          (C * family.enncard * tubeVolume) *
            MeasureTheory.volume convexSet := by
      rw [hcontainedMass]
      have hcount' :
          family.toBodyFamily.containedCount convexSet ≤
            C * MeasureTheory.volume convexSet * family.enncard := by
        simpa [Kakeya.Streamlined.BodyFamily.enncard,
          Kakeya.Streamlined.TubeFamily.enncard,
          Kakeya.Streamlined.TubeFamily.toBodyFamily] using hcount
      calc
        family.toBodyFamily.containedCount convexSet * tubeVolume ≤
            (C * MeasureTheory.volume convexSet * family.enncard) *
              tubeVolume := by
          exact mul_le_mul_right' hcount' tubeVolume
        _ =
            (C * family.enncard * tubeVolume) *
              MeasureTheory.volume convexSet := by
          ring
    by_cases hzero : MeasureTheory.volume convexSet = 0
    · rw [hzero, mul_zero] at hmass
      have hmassZero :
          family.toBodyFamily.containedMass convexSet = 0 :=
        bot_unique hmass
      simp [Kakeya.Streamlined.BodyFamily.density,
        hmassZero, hzero]
    · by_cases htop : MeasureTheory.volume convexSet = ⊤
      · simp [Kakeya.Streamlined.BodyFamily.density, htop]
      · rw [Kakeya.Streamlined.BodyFamily.density]
        rw [ENNReal.div_le_iff hzero htop]
        exact hmass

/--
If `deltaMax ≤ D`, every broad Assertion-D conflict neighborhood has indexed
cardinality at most `972000000 * D`.
-/
theorem pure_wz2_analytic_conflict_degree_from_deltaMax
    {delta : ℝ}
    (hdelta : 0 < delta)
    (hdeltaOne : delta ≤ 1)
    (hscaleSmall : 3000 * delta ≤ 1 / 8)
    {family : Kakeya.Streamlined.TubeFamily delta}
    {D : ENNReal}
    (hD : family.toBodyFamily.deltaMax ≤ D) :
    ∀ index,
      ((Finset.univ.filter fun other =>
        ¬(family.tube index).EssentiallyDistinct
          (family.tube other)).card : ENNReal) ≤
        972000000 * D := by
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
      conflicts ⊆
        family.toBodyFamily.containedIndices envelope.carrier := by
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
  let tubeVolume : ENNReal := Kakeya.deltaTubeVolume delta
  have htubeVolumePositive : 0 < tubeVolume :=
    (tube_volume_scaling.2.1 delta hdelta hdeltaOne).1
  have htubeVolumeTop : tubeVolume ≠ ⊤ :=
    (tube_volume_scaling.2.1 delta hdelta hdeltaOne).2
  have hcontainedMassLower :
      (conflicts.card : ENNReal) * tubeVolume ≤
        family.toBodyFamily.containedMass envelope.carrier := by
    change
      (conflicts.card : ENNReal) * tubeVolume ≤
        ∑ other ∈
          family.toBodyFamily.containedIndices envelope.carrier,
            (family.toBodyFamily.body other).volume
    calc
      (conflicts.card : ENNReal) * tubeVolume =
          ∑ _other ∈ conflicts, tubeVolume := by
        simp [Finset.sum_const]
      _ =
          ∑ other ∈ conflicts,
            (family.toBodyFamily.body other).volume := by
        apply Finset.sum_congr rfl
        intro other _
        symm
        exact tube_volume_scaling.1 delta (family.tube other)
      _ ≤
          ∑ other ∈
            family.toBodyFamily.containedIndices envelope.carrier,
              (family.toBodyFamily.body other).volume := by
        exact
          Finset.sum_le_sum_of_subset_of_nonneg hsubset
            (fun _ _ _ => bot_le)
  have henvelopePositive : 0 < MeasureTheory.volume envelope.carrier := by
    rcases henvelopeDimensions with ⟨frame, hdimensions⟩
    exact
      (ENNReal.ofReal_pos.mpr (by positivity)).trans_le
        (Kakeya.Streamlined.hasDimensionsInFrame_volume_lower hdimensions)
  have henvelopeTop : MeasureTheory.volume envelope.carrier ≠ ⊤ := by
    rcases henvelopeDimensions with ⟨frame, hdimensions⟩
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      (Kakeya.Streamlined.hasDimensionsInFrame_volume_upper hdimensions)
  have hdensityLe :
      family.toBodyFamily.density envelope.carrier ≤ D := by
    have hle :
        family.toBodyFamily.density envelope.carrier ≤
          family.toBodyFamily.deltaMax := by
      apply le_csSup (s := {d : ENNReal |
        ∃ K : Set Point3, Convex ℝ K ∧
          d = family.toBodyFamily.density K})
      · exact ⟨⊤, fun _ _ => le_top⟩
      show family.toBodyFamily.density envelope.carrier ∈
        {d : ENNReal |
          ∃ K : Set Point3, Convex ℝ K ∧
            d = family.toBodyFamily.density K}
      exact ⟨envelope.carrier, henvelopeConvex, rfl⟩
    exact hle.trans hD
  have hcontainedMassUpper :
      family.toBodyFamily.containedMass envelope.carrier ≤
        D * MeasureTheory.volume envelope.carrier := by
    rw [Kakeya.Streamlined.BodyFamily.density] at hdensityLe
    have hmul :
        family.toBodyFamily.containedMass envelope.carrier /
              MeasureTheory.volume envelope.carrier *
            MeasureTheory.volume envelope.carrier ≤
          D * MeasureTheory.volume envelope.carrier := by
      gcongr
    rw [ENNReal.div_mul_cancel
      henvelopePositive.ne' henvelopeTop] at hmul
    exact hmul
  have henvelopeVolume :
      MeasureTheory.volume envelope.carrier ≤
        ENNReal.ofReal (972000000 * delta ^ 2) := by
    rcases henvelopeDimensions with ⟨frame, hdimensions⟩
    have hvolume :=
      Kakeya.Streamlined.hasDimensionsInFrame_volume_upper hdimensions
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
  have hdeltaVolume :
      ENNReal.ofReal (delta ^ 2) ≤ tubeVolume :=
    canonical_volume_lower hdelta
  have hwithDelta :
      (conflicts.card : ENNReal) *
          ENNReal.ofReal (delta ^ 2) ≤
        (972000000 * D) * ENNReal.ofReal (delta ^ 2) := by
    calc
      (conflicts.card : ENNReal) *
          ENNReal.ofReal (delta ^ 2) ≤
        (conflicts.card : ENNReal) * tubeVolume := by
          gcongr
      _ ≤ family.toBodyFamily.containedMass envelope.carrier :=
        hcontainedMassLower
      _ ≤ D * MeasureTheory.volume envelope.carrier :=
        hcontainedMassUpper
      _ ≤ D * ENNReal.ofReal (972000000 * delta ^ 2) := by
        gcongr
      _ =
          (972000000 * D) * ENNReal.ofReal (delta ^ 2) := by
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 972000000)]
        norm_num
        ring
  have hdeltaSquaredZero :
      ENNReal.ofReal (delta ^ 2) ≠ 0 := by
    positivity
  have hdeltaSquaredTop :
      ENNReal.ofReal (delta ^ 2) ≠ ⊤ :=
    ENNReal.ofReal_ne_top
  exact
    (ENNReal.mul_le_mul_iff_right
      hdeltaSquaredZero hdeltaSquaredTop).mp (by
        simpa [mul_comm] using hwithDelta)

end Kakeya.Assouad

end
