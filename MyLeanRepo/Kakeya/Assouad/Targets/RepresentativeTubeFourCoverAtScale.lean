import MyLeanRepo.Kakeya.Assouad.AnisotropicRescaling.CoaxialOverlap
import MyLeanRepo.Kakeya.Assouad.AnisotropicRescaling.FourSegmentAxisCover
import MyLeanRepo.Kakeya.Assouad.AnisotropicRescaling.FourTubeEnvelopeGeometry
import MyLeanRepo.Kakeya.Assouad.Statements

/-!
WZ2 Section 7: cover one overlap class by four same-line coarse tubes at the
prescribed selected scale.
-/

namespace Kakeya.Assouad

/--
If two tubes have the same (or opposite) direction and one base lies on the
other's axis, their full affine axis lines coincide.
-/
lemma tubeAxisLine_of_coaxial
    {delta rho : ℝ} (T : Kakeya.DeltaTube rho) (U : Kakeya.DeltaTube delta)
    (hdir : T.direction = U.direction ∨ T.direction = -U.direction)
    (hbase : ∃ s : ℝ, T.base = U.base + s • U.direction) :
    tubeAxisLine T = tubeAxisLine U := by
  ext p
  simp only [tubeAxisLine, Set.mem_setOf_eq]
  rcases hbase with ⟨s, hs⟩
  constructor
  · rintro ⟨t, rfl⟩
    rcases hdir with (hdir | hdir)
    · refine ⟨s + t, ?_⟩
      have h : T.base + t • T.direction = U.base + (s + t) • U.direction := by
        simp [hs, hdir, add_smul] <;> module
      exact h
    · refine ⟨s - t, ?_⟩
      have h : T.base + t • T.direction = U.base + (s - t) • U.direction := by
        simp [hs, hdir, sub_smul, smul_neg] <;> module
      exact h
  · rintro ⟨r, rfl⟩
    rcases hdir with (hdir | hdir)
    · refine ⟨r - s, ?_⟩
      have h : U.base + r • U.direction = T.base + (r - s) • T.direction := by
        simp [hs, hdir, add_smul, sub_smul] <;> module
      exact h
    · refine ⟨s - r, ?_⟩
      have h : U.base + r • U.direction = T.base + (s - r) • T.direction := by
        simp [hs, hdir, sub_smul, smul_neg] <;> module
      exact h

theorem representative_tube_four_cover_at_scale :
    RepresentativeTubeFourCoverAtScaleStatement := by
  intro h_align h_coaxial hvolume delta rho hdelta hdelta_rho hrho U
  let direction : Point3 := U.direction
  have hdirection : ‖direction‖ = 1 := U.direction_unit
  have hrho_pos : 0 < rho := by linarith [hdelta, hdelta_rho]
  have hdelta_small : delta ≤ 1 / 1000 := by linarith
  let P0 : Kakeya.DeltaTube rho :=
    ⟨U.base + (-2 : ℝ) • direction, direction, hdirection⟩
  let P1 : Kakeya.DeltaTube rho :=
    ⟨U.base + (-1 : ℝ) • direction, direction, hdirection⟩
  let P2 : Kakeya.DeltaTube rho :=
    ⟨U.base, direction, hdirection⟩
  let P3 : Kakeya.DeltaTube rho :=
    ⟨U.base + direction, direction, hdirection⟩
  let C0 : Kakeya.DeltaTube rho := reverseTube P0
  have hC0_base : C0.base = U.base - direction := by
    dsimp only [C0, reverseTube, P0] <;> module
  have hC0_dir : C0.direction = -direction := by
    dsimp only [C0, reverseTube, P0] <;> rfl
  let coarse : Kakeya.Streamlined.TubeFamily rho :=
    { card := 4
      tube := fun j =>
        match j with
        | 0 => C0
        | 1 => P1
        | 2 => P2
        | 3 => P3 }
  have h01 : P0.EssentiallyDistinct P1 := by
    simpa [P0, P1] using
      h_coaxial hvolume rho hrho_pos hrho
        U.base direction hdirection (-2) (-1) (by norm_num)
  have h02 : P0.EssentiallyDistinct P2 := by
    simpa [P0, P2] using
      h_coaxial hvolume rho hrho_pos hrho
        U.base direction hdirection (-2) 0 (by norm_num)
  have h03 : P0.EssentiallyDistinct P3 := by
    simpa [P0, P3] using
      h_coaxial hvolume rho hrho_pos hrho
        U.base direction hdirection (-2) 1 (by norm_num)
  have h12 : P1.EssentiallyDistinct P2 := by
    simpa [P1, P2] using
      h_coaxial hvolume rho hrho_pos hrho
        U.base direction hdirection (-1) 0 (by norm_num)
  have h13 : P1.EssentiallyDistinct P3 := by
    simpa [P1, P3] using
      h_coaxial hvolume rho hrho_pos hrho
        U.base direction hdirection (-1) 1 (by norm_num)
  have h23 : P2.EssentiallyDistinct P3 := by
    simpa [P2, P3] using
      h_coaxial hvolume rho hrho_pos hrho
        U.base direction hdirection 0 1 (by norm_num)
  have hdistinct : coarse.IsEssentiallyDistinct := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact False.elim (hij rfl)
    · exact reverseTube_essentiallyDistinct_left P0 P1 h01
    · exact reverseTube_essentiallyDistinct_left P0 P2 h02
    · exact reverseTube_essentiallyDistinct_left P0 P3 h03
    · exact essentiallyDistinct_symm.mp
        (reverseTube_essentiallyDistinct_left P0 P1 h01)
    · exact False.elim (hij rfl)
    · exact h12
    · exact h13
    · exact essentiallyDistinct_symm.mp
        (reverseTube_essentiallyDistinct_left P0 P2 h02)
    · exact essentiallyDistinct_symm.mp h12
    · exact False.elim (hij rfl)
    · exact h23
    · exact essentiallyDistinct_symm.mp
        (reverseTube_essentiallyDistinct_left P0 P3 h03)
    · exact essentiallyDistinct_symm.mp h13
    · exact essentiallyDistinct_symm.mp h23
    · exact False.elim (hij rfl)
  have haxis : ∀ j : Fin coarse.card,
      tubeAxisLine (coarse.tube j) = tubeAxisLine U := by
    intro j
    fin_cases j
    · apply tubeAxisLine_of_coaxial C0 U
      · exact Or.inr hC0_dir
      · refine ⟨-1, ?_⟩
        rw [hC0_base]
        simp [sub_eq_add_neg] <;> abel
    · apply tubeAxisLine_of_coaxial P1 U
      · exact Or.inl rfl
      · refine ⟨-1, ?_⟩
        simp [P1] <;> abel
    · apply tubeAxisLine_of_coaxial P2 U
      · exact Or.inl rfl
      · refine ⟨0, ?_⟩
        simp [P2] <;> abel
    · apply tubeAxisLine_of_coaxial P3 U
      · exact Or.inl rfl
      · refine ⟨1, ?_⟩
        simp [P3] <;> abel
  have hvertical : ∀ j : Fin coarse.card,
      |(coarse.tube j).direction (2 : Fin 3)| =
        |U.direction (2 : Fin 3)| := by
    intro j
    fin_cases j
    · simp [coarse, C0, reverseTube, P0, direction]
    · rfl
    · rfl
    · rfl
  have hbase : ∀ j : Fin coarse.card,
      ‖(coarse.tube j).base‖ ≤ ‖U.base‖ + 1 := by
    intro j
    fin_cases j
    · change ‖(reverseTube P0).base‖ ≤ ‖U.base‖ + 1
      rw [show (reverseTube P0).base = U.base - direction from hC0_base]
      calc
        ‖U.base - direction‖ ≤ ‖U.base‖ + ‖direction‖ := norm_sub_le _ _
        _ = ‖U.base‖ + 1 := by rw [hdirection]
    · change ‖P1.base‖ ≤ ‖U.base‖ + 1
      have heq : P1.base = U.base - direction := by
        simp [P1, sub_eq_add_neg]
      rw [heq]
      calc
        ‖U.base - direction‖ ≤ ‖U.base‖ + ‖direction‖ := norm_sub_le _ _
        _ = ‖U.base‖ + 1 := by rw [hdirection]
    · change ‖P2.base‖ ≤ ‖U.base‖ + 1
      simp [P2]
    · change ‖P3.base‖ ≤ ‖U.base‖ + 1
      calc
        ‖P3.base‖ = ‖U.base + direction‖ := by rfl
        _ ≤ ‖U.base‖ + ‖direction‖ := norm_add_le _ _
        _ = ‖U.base‖ + 1 := by rw [hdirection]
  have hcover : ∀ T : Kakeya.DeltaTube delta,
      ¬T.EssentiallyDistinct U →
        T.carrier ⊆ coarse.toBodyFamily.union := by
    intro T hnot point hpoint
    rcases h_align delta hdelta hdelta_small T U hnot with
      ⟨sign, anchor, horient, hdir_close, shift, hshift, hbase_close⟩
    have hcompact :
        IsCompact (Kakeya.unitSegment T.base T.direction) := by
      exact isCompact_Icc.image
        (continuous_const.add (continuous_id.smul continuous_const))
    change point ∈ Metric.cthickening delta
      (Kakeya.unitSegment T.base T.direction) at hpoint
    rw [hcompact.cthickening_eq_biUnion_closedBall hdelta.le] at hpoint
    rcases Set.mem_iUnion₂.mp hpoint with ⟨axisPoint, haxis, hball⟩
    rcases haxis with ⟨a, ha, rfl⟩
    let signedDirection : Point3 := sign • direction
    let targetPoint : Point3 :=
      anchor + (shift + a) • signedDirection
    have hsource_target :
        dist (T.base + a • T.direction) targetPoint ≤ 2002 * delta := by
      rw [dist_eq_norm]
      have hvector :
          (T.base + a • T.direction) - targetPoint =
            (T.base - (anchor + shift • signedDirection)) +
              a • (T.direction - signedDirection) := by
        dsimp only [targetPoint]
        rw [add_smul] <;> module
      rw [hvector]
      have htriangle :
          ‖(T.base - (anchor + shift • signedDirection)) +
              a • (T.direction - signedDirection)‖ ≤
            ‖T.base - (anchor + shift • signedDirection)‖ +
              ‖a • (T.direction - signedDirection)‖ :=
        norm_add_le _ _
      have hsmul :
          ‖a • (T.direction - signedDirection)‖ =
            a * ‖T.direction - signedDirection‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ha.1]
      rw [hsmul] at htriangle
      have hdir_bound :
          ‖T.direction - signedDirection‖ ≤ 1000 * delta := by
        simpa [signedDirection, direction] using hdir_close
      have ha_bound :
          a * ‖T.direction - signedDirection‖ ≤ 1000 * delta := by
        calc
          a * ‖T.direction - signedDirection‖
              ≤ a * (1000 * delta) := by gcongr; exact ha.1
          _ ≤ 1000 * delta := by nlinarith [ha.2]
      have hbase_bound :
          ‖T.base - (anchor + shift • signedDirection)‖ ≤
            1002 * delta := by
        simpa [signedDirection, direction] using hbase_close
      linarith
    have hpoint_target :
        dist point targetPoint ≤ rho := by
      have hpoint_axis :
          dist point (T.base + a • T.direction) ≤ delta := by
        simpa [Metric.mem_closedBall] using hball
      calc
        dist point targetPoint
            ≤ dist point (T.base + a • T.direction) +
                dist (T.base + a • T.direction) targetPoint :=
          dist_triangle _ _ _
        _ ≤ delta + 2002 * delta := by gcongr
        _ = 2003 * delta := by ring
        _ ≤ 3000 * delta := by linarith
        _ ≤ rho := hdelta_rho
    have hparameter :
        shift + a ∈ Set.Icc (-1 : ℝ) 2 := by
      constructor <;> linarith [hshift.1, hshift.2, ha.1, ha.2]
    have htarget_axis :=
      oriented_anchor_axis_point_mem_four_segments
        U.base direction anchor horient hparameter
    rcases htarget_axis with hABC | hD
    · rcases hABC with hAB | hC
      · rcases hAB with hA | hB
        · refine ⟨(0 : Fin 4), ?_⟩
          change point ∈ C0.carrier
          have haxis_seg :
              targetPoint ∈ Kakeya.unitSegment C0.base C0.direction := by
            rw [hC0_base, hC0_dir]
            simpa [targetPoint, signedDirection, direction] using hA
          exact Metric.mem_cthickening_of_dist_le
            point targetPoint rho _ haxis_seg hpoint_target
        · refine ⟨(1 : Fin 4), ?_⟩
          change point ∈ P1.carrier
          have haxis_seg :
              targetPoint ∈ Kakeya.unitSegment P1.base P1.direction := by
            simpa [targetPoint, signedDirection, P1, direction,
              sub_eq_add_neg] using hB
          exact Metric.mem_cthickening_of_dist_le
            point targetPoint rho _ haxis_seg hpoint_target
      · refine ⟨(2 : Fin 4), ?_⟩
        change point ∈ P2.carrier
        have haxis_seg :
            targetPoint ∈ Kakeya.unitSegment P2.base P2.direction := by
          simpa [targetPoint, signedDirection, P2, direction] using hC
        exact Metric.mem_cthickening_of_dist_le
          point targetPoint rho _ haxis_seg hpoint_target
    · refine ⟨(3 : Fin 4), ?_⟩
      change point ∈ P3.carrier
      have haxis_seg :
          targetPoint ∈ Kakeya.unitSegment P3.base P3.direction := by
        simpa [targetPoint, signedDirection, P3, direction] using hD
      exact Metric.mem_cthickening_of_dist_le
        point targetPoint rho _ haxis_seg hpoint_target
  rcases four_tube_envelope_geometry U.base direction hdirection rho hrho_pos hrho
    with ⟨envelope, henvelope_carrier, henvelope_measurable, henvelope_convex,
      henvelope_dimensions⟩
  have h_family_union : coarse.toBodyFamily.union =
      C0.carrier ∪ P1.carrier ∪ P2.carrier ∪ P3.carrier := by
    ext y
    simp only [Kakeya.Streamlined.BodyFamily.union, Set.mem_setOf_eq]
    constructor
    · rintro ⟨i, hi⟩
      fin_cases i
      · exact Or.inl (Or.inl (Or.inl hi))
      · exact Or.inl (Or.inl (Or.inr hi))
      · exact Or.inl (Or.inr hi)
      · exact Or.inr hi
    · intro hy
      rcases hy with (h | h3)
      · rcases h with (h | h2)
        · rcases h with (h0 | h1)
          · let i0 : Fin coarse.toBodyFamily.card :=
              ⟨0, by simp [coarse, Kakeya.Streamlined.TubeFamily.toBodyFamily] <;> decide⟩
            refine ⟨i0, ?_⟩
            have h_eq : (coarse.toBodyFamily.body i0).carrier = C0.carrier := by
              simp [i0, coarse, Kakeya.Streamlined.TubeFamily.toBodyFamily,
                Kakeya.Streamlined.tubeBody] <;> rfl
            rw [h_eq]
            exact h0
          · let i1 : Fin coarse.toBodyFamily.card :=
              ⟨1, by simp [coarse, Kakeya.Streamlined.TubeFamily.toBodyFamily] <;> decide⟩
            refine ⟨i1, ?_⟩
            have h_eq : (coarse.toBodyFamily.body i1).carrier = P1.carrier := by
              simp [i1, coarse, Kakeya.Streamlined.TubeFamily.toBodyFamily,
                Kakeya.Streamlined.tubeBody] <;> rfl
            rw [h_eq]
            exact h1
        · let i2 : Fin coarse.toBodyFamily.card :=
            ⟨2, by simp [coarse, Kakeya.Streamlined.TubeFamily.toBodyFamily] <;> decide⟩
          refine ⟨i2, ?_⟩
          have h_eq : (coarse.toBodyFamily.body i2).carrier = P2.carrier := by
            simp [i2, coarse, Kakeya.Streamlined.TubeFamily.toBodyFamily,
              Kakeya.Streamlined.tubeBody] <;> rfl
          rw [h_eq]
          exact h2
      · let i3 : Fin coarse.toBodyFamily.card :=
          ⟨3, by simp [coarse, Kakeya.Streamlined.TubeFamily.toBodyFamily] <;> decide⟩
        refine ⟨i3, ?_⟩
        have h_eq : (coarse.toBodyFamily.body i3).carrier = P3.carrier := by
          simp [i3, coarse, Kakeya.Streamlined.TubeFamily.toBodyFamily,
            Kakeya.Streamlined.tubeBody] <;> rfl
        rw [h_eq]
        exact h3
  have henvelope_union : envelope.carrier = coarse.toBodyFamily.union := by
    rw [henvelope_carrier, h_family_union]
  have hcover_envelope : ∀ T : Kakeya.DeltaTube delta,
      ¬T.EssentiallyDistinct U → T.carrier ⊆ envelope.carrier := by
    intro T hnot
    rw [henvelope_union]
    exact hcover T hnot
  exact ⟨coarse, envelope, rfl, hdistinct, haxis, hvertical, hbase,
    henvelope_union, henvelope_measurable, henvelope_convex,
    henvelope_dimensions, hcover_envelope⟩

end Kakeya.Assouad
