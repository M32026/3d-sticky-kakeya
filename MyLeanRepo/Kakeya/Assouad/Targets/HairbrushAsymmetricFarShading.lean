import MyLeanRepo.Kakeya.Assouad.Subunit.HairbrushSelfContainedLeaves
import MyLeanRepo.Kakeya.Hairbrush.TubeCylinderBallContainment

/-!
# Core-independent asymmetric far shading

This is Wolff 1995 Lemma 3.4 equation (19), used as (B.25) in the
self-contained Appendix-B proof.

For each supplied transverse hair:
1. `tube_cylinder_contained_in_closedBall` puts the near-cylinder part in one
   ball of the supplied `nearRadius`;
2. the supplied near-ball mass bound bounds the near-cylinder mass by 1/4;
3. the measurable far shading is defined explicitly and retains at least one
   quarter of every hair's mass.

The validated `hairbrush_far_mass_from_two_ends` proof is the direct template.
-/

namespace Kakeya.Assouad

open MeasureTheory Metric Set

theorem hairbrush_asymmetric_far_shading :
    HairbrushAsymmetricFarShadingStatement := by
  intro δ sigma farRadius nearRadius hδ hsigma hsigma1 hfarRadius_pos hnear_pos hR_lt
  intro H Z stem h_angles h_inter h_near_bound

  let nearSet : Set Point3 :=
    {x | ‖perpProj stem.direction (x - stem.base)‖ < farRadius}
  let farSet : Set Point3 :=
    {x | farRadius ≤ ‖perpProj stem.direction (x - stem.base)‖}

  have h_perp_cont : Continuous fun x : Point3 =>
      perpProj stem.direction (x - stem.base) := by
    have h1 : Continuous fun x : Point3 => x - stem.base :=
      continuous_id.sub continuous_const
    have h2 : Continuous fun x : Point3 => perpProj stem.direction x := by
      have h3 : Continuous fun x : Point3 => inner ℝ x stem.direction := by fun_prop
      exact continuous_id.sub (h3.smul continuous_const)
    exact h2.comp h1
  have h_norm_cont : Continuous fun x : Point3 =>
      ‖perpProj stem.direction (x - stem.base)‖ :=
    h_perp_cont.norm
  have hnear_meas : MeasurableSet nearSet :=
    h_norm_cont.measurable measurableSet_Iio
  have hfar_meas : MeasurableSet farSet :=
    h_norm_cont.measurable measurableSet_Ici

  let shading : Kakeya.Shading H :=
    { carrier := fun U => Z.carrier U ∩ farSet
      measurable_carrier := fun U hU =>
        (Z.measurable_carrier hU).inter hfar_meas
      subset_tube := fun U hU =>
        Set.inter_subset_left.trans (Z.subset_tube hU) }

  have h_main : ∀ (U : Kakeya.DeltaTube δ), U ∈ H →
      (1 / 4 : ENNReal) * volume (Z.carrier U) ≤
        volume (Z.carrier U ∩ farSet) := by
    intro U hU

    have h_angle1 : sigma ≤ hairbrushAcuteAngle stem U :=
      (h_angles U hU).1
    have h_angle2 : hairbrushAcuteAngle stem U ≤ 2 * sigma :=
      (h_angles U hU).2
    have h_interU : (stem.carrier ∩ U.carrier).Nonempty :=
      h_inter U hU

    set R : ℝ := 2 * δ + Real.pi * (farRadius + 3 * δ) / (2 * sigma) with hR_def

    have hfarRadius_nonneg : 0 ≤ farRadius := hfarRadius_pos.le
    rcases tube_cylinder_contained_in_closedBall hδ hsigma hsigma1 stem U
        h_angle1 h_angle2 h_interU farRadius hfarRadius_nonneg with
      ⟨x0, h_infDist, h_contain⟩

    have h_near_contain : nearSet ⊆
        {x | ‖perpProj stem.direction (x - stem.base)‖ ≤ farRadius} := by
      intro x hx
      simpa [nearSet] using le_of_lt hx

    have h_ball_contain : (U.carrier ∩ nearSet) ⊆ Metric.ball x0 nearRadius := by
      intro y hy
      have h1 : y ∈ U.carrier ∩
          {x | ‖perpProj stem.direction (x - stem.base)‖ ≤ farRadius} :=
        ⟨hy.1, h_near_contain hy.2⟩
      have h2 : y ∈ Metric.closedBall x0 R := h_contain h1
      have h3 : Metric.closedBall x0 R ⊆ Metric.ball x0 nearRadius := by
        intro z hz
        have h4 : dist z x0 ≤ R := hz
        exact lt_of_le_of_lt h4 hR_lt
      exact h3 h2

    have h_Z_near_contain : (Z.carrier U ∩ nearSet) ⊆ Metric.ball x0 nearRadius := by
      intro y hy
      have h1 : y ∈ Z.carrier U := hy.1
      have h2 : y ∈ U.carrier := Z.subset_tube hU h1
      exact h_ball_contain ⟨h2, hy.2⟩

    have h_vol_near : volume (Z.carrier U ∩ nearSet) ≤
        (1 / 4 : ENNReal) * volume (Z.carrier U) := by
      have h_sub : (Z.carrier U ∩ nearSet) ⊆
          (Z.carrier U ∩ Metric.ball x0 nearRadius) := by
        intro y hy
        exact ⟨hy.1, h_Z_near_contain hy⟩
      have h1 : volume (Z.carrier U ∩ nearSet) ≤
          volume (Z.carrier U ∩ Metric.ball x0 nearRadius) :=
        measure_mono h_sub
      have h2 := h_near_bound U hU x0 h_infDist
      exact le_trans h1 h2

    have hZ_meas : MeasurableSet (Z.carrier U) := Z.measurable_carrier hU

    have h_partition : (Z.carrier U ∩ nearSet) ∪ (Z.carrier U ∩ farSet) =
        Z.carrier U := by
      ext x
      simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_setOf_eq]
      constructor
      · rintro (h | h) <;> tauto
      · intro hx
        by_cases h : ‖perpProj stem.direction (x - stem.base)‖ < farRadius
        · exact Or.inl ⟨hx, h⟩
        · have h' : farRadius ≤ ‖perpProj stem.direction (x - stem.base)‖ := by
            linarith
          exact Or.inr ⟨hx, h'⟩

    have h_disjoint : Disjoint (Z.carrier U ∩ nearSet) (Z.carrier U ∩ farSet) := by
      rw [Set.disjoint_left]
      intro x hx1 hx2
      have h1 : ‖perpProj stem.direction (x - stem.base)‖ < farRadius := hx1.2
      have h2 : farRadius ≤ ‖perpProj stem.direction (x - stem.base)‖ := hx2.2
      linarith

    have h_union_vol : volume ((Z.carrier U ∩ nearSet) ∪ (Z.carrier U ∩ farSet)) =
        volume (Z.carrier U ∩ nearSet) + volume (Z.carrier U ∩ farSet) :=
      measure_union' h_disjoint (hZ_meas.inter hnear_meas)

    have h_vol_eq : volume (Z.carrier U) =
        volume (Z.carrier U ∩ nearSet) + volume (Z.carrier U ∩ farSet) := by
      have h1 : volume (Z.carrier U) =
          volume ((Z.carrier U ∩ nearSet) ∪ (Z.carrier U ∩ farSet)) :=
        congr_arg volume h_partition.symm
      rw [h1]
      exact h_union_vol

    set c : ENNReal := volume (Z.carrier U) with hc_def
    set a : ENNReal := volume (Z.carrier U ∩ nearSet) with ha_def
    set b : ENNReal := volume (Z.carrier U ∩ farSet) with hb_def

    have h_seg_comp : IsCompact (Kakeya.unitSegment U.base U.direction) :=
      isCompact_Icc.image (show Continuous (fun t : ℝ => U.base + t • U.direction)
        from by fun_prop)
    have h_carrier_comp : IsCompact U.carrier := by
      have h : U.carrier = Metric.cthickening δ (Kakeya.unitSegment U.base U.direction) := by rfl
      rw [h]
      exact h_seg_comp.cthickening
    have h_tube_fin : volume U.carrier ≠ ⊤ := h_carrier_comp.measure_lt_top.ne
    have h1 : Z.carrier U ⊆ U.carrier := Z.subset_tube hU
    have h2 : volume (Z.carrier U) ≤ volume U.carrier := measure_mono h1
    have h_fin : c ≠ ⊤ := ne_top_of_le_ne_top h_tube_fin h2

    have h_main_ineq : (1 / 4 : ENNReal) * c ≤ b := by
      have h_eq : a + b = c := h_vol_eq.symm
      have h_a_le : a ≤ (1 / 4 : ENNReal) * c := h_vol_near
      have h_a_le_c : a ≤ c := by
        have h1 : a ≤ (1 / 4 : ENNReal) * c := h_a_le
        have h2 : (1 / 4 : ENNReal) * c ≤ c := by
          exact mul_le_of_le_one_left (by simp) (by norm_num)
        exact le_trans h1 h2
      have h_a_ne_top : a ≠ ⊤ := ne_top_of_le_ne_top h_fin h_a_le_c
      by_contra h
      have h' : b < (1 / 4 : ENNReal) * c := by
        exact lt_of_not_ge h
      have h4 : a + b < a + (1 / 4 : ENNReal) * c :=
        ENNReal.add_lt_add_left h_a_ne_top h'
      have h5 : a + (1 / 4 : ENNReal) * c ≤
          (1 / 4 : ENNReal) * c + (1 / 4 : ENNReal) * c := by
        have h51 : a ≤ (1 / 4 : ENNReal) * c := h_a_le
        exact add_le_add_left h51 ((1 / 4 : ENNReal) * c)
      have h6 : a + b < (1 / 4 : ENNReal) * c + (1 / 4 : ENNReal) * c :=
        lt_of_lt_of_le h4 h5
      have h7 : (1 / 4 : ENNReal) * c + (1 / 4 : ENNReal) * c =
          (1 / 2 : ENNReal) * c := by
        have h71 : (1 / 4 : ENNReal) * c + (1 / 4 : ENNReal) * c =
            ((1 / 4 : ENNReal) + (1 / 4 : ENNReal)) * c := by
          rw [add_mul]
        rw [h71]
        have h72 : (1 / 4 : ENNReal) + (1 / 4 : ENNReal) = (1 / 2 : ENNReal) := by
          have h_pos1 : 0 ≤ (1 / 4 : ℝ) := by norm_num
          have h_pos2 : 0 ≤ (1 / 4 : ℝ) := by norm_num
          have h : ENNReal.ofReal (1 / 4 : ℝ) + ENNReal.ofReal (1 / 4 : ℝ) =
              ENNReal.ofReal ((1 / 2 : ℝ)) := by
            have h_add : ENNReal.ofReal (1 / 4 : ℝ) + ENNReal.ofReal (1 / 4 : ℝ) =
                ENNReal.ofReal ((1 / 4 : ℝ) + (1 / 4 : ℝ)) := by
              exact (ENNReal.ofReal_add h_pos1 h_pos2).symm
            rw [h_add]
            have h_eq : (1 / 4 : ℝ) + (1 / 4 : ℝ) = (1 / 2 : ℝ) := by norm_num
            rw [h_eq]
          simpa using h
        rw [h72]
      rw [h7] at h6
      have h8 : (1 / 2 : ENNReal) * c ≤ c := by
        exact mul_le_of_le_one_left (by simp) (by norm_num)
      rw [h_eq] at h6
      exact not_le.mpr h6 h8

    simpa [hc_def, hb_def] using h_main_ineq

  refine' ⟨shading, _, _⟩
  · intro U hU
    rfl
  · exact h_main

end Kakeya.Assouad
