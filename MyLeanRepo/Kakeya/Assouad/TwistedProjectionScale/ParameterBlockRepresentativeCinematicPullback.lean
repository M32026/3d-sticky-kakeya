import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ParameterBlockRepresentativeCinematicStatements
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.AmplifiedGeometricContainment

/-!
# Complete proof of parameter_block_representative_cinematic_pullback

WZ2 paper Lemma 7.12: copy one genuine source tube for every selected local
parameter, apply the cinematic estimate, and pull the area lower bound back to
the representative local block.

This is a simplified variant of `parameter_block_cinematic_pullback`: the copied
family has exactly one tube per collapsed `(a,b,d)` parameter, so the assignment
fiber cap is absolute (12500000) instead of the indexed four-parameter Frostman
quantity.
-/

noncomputable section

open MeasureTheory Set Finset

namespace Kakeya.Assouad

/-- `slopeCurve f a b d` equals `halfParameterSlopeCurve f (tubeParameterPoint3 i)`. -/
private lemma rep_setup_assign_contain_eq {δ : ℝ} {F : Kakeya.Streamlined.TubeFamily δ}
    (f : SlopeFunction) (i : Fin F.card) :
    slopeCurve f (tubeParams i).a (tubeParams i).b (tubeParams i).d =
    halfParameterSlopeCurve f (tubeParameterPoint3 i) := by
  have h0 : (tubeParameterPoint3 i) 0 = (tubeParams i).a / 24 := by
    simp [tubeParameterPoint3, point3]
  have h1 : (tubeParameterPoint3 i) 1 = (tubeParams i).b / 24 := by
    simp [tubeParameterPoint3, point3]
  have h2 : (tubeParameterPoint3 i) 2 = (tubeParams i).d / 4 := by
    simp [tubeParameterPoint3, point3]
  simp only [halfParameterSlopeCurve]
  rw [h0, h1, h2]
  ring_nf

/-- Coordinate bound for amplification translations. -/
private lemma rep_setup_v_bound
    {δ fineScale blockScale s : ℝ}
    {F : Kakeya.Streamlined.TubeFamily δ}
    {Y : Kakeya.Streamlined.TubeShading F} {C lambda : ENNReal}
    {clustered : TubeParameterClusterFrostmanData F Y C lambda δ}
    {epsilon : ℝ}
    {localBlock : ParameterLocalFullBlockData clustered epsilon}
    {amplification : ParameterBlockAmplificationData fineScale blockScale s localBlock.centeredPoints}
    (v : Point 3) (hv : v ∈ amplification.translations) (i : Fin 3) :
    |v i| ≤ 1 / 2 + localBlock.blockScale / 10 := by
  rcases localBlock.centeredPoints_nonempty with ⟨q, hqmem⟩
  have hcopy : q + v ∈ amplification.amplified := amplification.copy_source v hv q hqmem
  have hhalf : |(q + v) 0| ≤ 1 / 2 ∧ |(q + v) 1| ≤ 1 / 2 ∧ |(q + v) 2| ≤ 1 / 2 :=
    amplification.amplified_half (q + v) hcopy
  have hqi_dist : dist (q i) ((0 : Point 3) i) ≤ localBlock.blockScale / 10 :=
    (PiLp.dist_apply_le q (0 : Point 3) i).trans (localBlock.centered_containment q hqmem)
  have hqi : |q i| ≤ localBlock.blockScale / 10 := by
    simpa [dist_zero_right] using hqi_dist
  have h1 : |(q + v) i| ≤ 1 / 2 := by fin_cases i <;> tauto
  have h3 : |v i| ≤ |(q + v) i| + |q i| := by
    have h4 : v i = (q + v) i - q i := by simp
    rw [h4]
    exact abs_sub ((q + v) i) (q i)
  exact h3.trans (add_le_add h1 hqi)

/-- Coordinate bound for local center. -/
private lemma rep_setup_center_bound
    {δ : ℝ} {F : Kakeya.Streamlined.TubeFamily δ}
    {Y : Kakeya.Streamlined.TubeShading F} {C lambda : ENNReal}
    {clustered : TubeParameterClusterFrostmanData F Y C lambda δ}
    {epsilon : ℝ}
    (localBlock : ParameterLocalFullBlockData clustered epsilon)
    (i : Fin 3) :
    |localBlock.localCenter i| ≤ 1 + localBlock.blockScale / 10 := by
  rcases localBlock.sourcePoints_nonempty with ⟨p, hpem⟩
  have hpin : p ∈ clustered.points := localBlock.sourcePoints_subset hpem
  have hunit : dist p 0 ≤ 1 := clustered.points_in_unitBall p hpin
  have hpi_dist : dist (p i) ((0 : Point 3) i) ≤ dist p 0 := PiLp.dist_apply_le p (0 : Point 3) i
  have hpi : |p i| ≤ 1 := by
    have h : |p i| ≤ dist p 0 := by simpa [dist_zero_right] using hpi_dist
    exact h.trans hunit
  have hdist_dist : dist p localBlock.localCenter ≤ localBlock.blockScale / 10 :=
    localBlock.source_containment p hpem
  have hdist : |p i - localBlock.localCenter i| ≤ localBlock.blockScale / 10 := by
    have h : dist (p i) (localBlock.localCenter i) ≤ dist p localBlock.localCenter :=
      PiLp.dist_apply_le p localBlock.localCenter i
    simpa [Real.dist_eq] using h.trans hdist_dist
  have h_abs : |localBlock.localCenter i| ≤ |p i| + |p i - localBlock.localCenter i| := by
    have h7 : |p i - (p i - localBlock.localCenter i)| ≤ |p i| + |p i - localBlock.localCenter i| :=
      abs_sub (p i) (p i - localBlock.localCenter i)
    have h8 : p i - (p i - localBlock.localCenter i) = localBlock.localCenter i := by ring
    rw [h8] at h7
    exact h7
  exact h_abs.trans (add_le_add hpi hdist)

/-- Coordinate bound for shift parameter. -/
private lemma rep_setup_shift_bound
    {δ fineScale blockScale s : ℝ}
    {F : Kakeya.Streamlined.TubeFamily δ}
    {Y : Kakeya.Streamlined.TubeShading F} {C lambda : ENNReal}
    {clustered : TubeParameterClusterFrostmanData F Y C lambda δ}
    {epsilon : ℝ}
    {localBlock : ParameterLocalFullBlockData clustered epsilon}
    {amplification : ParameterBlockAmplificationData fineScale blockScale s localBlock.centeredPoints}
    (v : Point 3) (hv : v ∈ amplification.translations) (i : Fin 3) :
    |(v - localBlock.localCenter) i| ≤ 3 / 2 + localBlock.blockScale / 5 := by
  have h1 : |v i| ≤ 1 / 2 + localBlock.blockScale / 10 := rep_setup_v_bound v hv i
  have h2 : |localBlock.localCenter i| ≤ 1 + localBlock.blockScale / 10 := rep_setup_center_bound localBlock i
  have h3 : |(v - localBlock.localCenter) i| ≤ |v i| + |localBlock.localCenter i| := by
    have h4 : (v - localBlock.localCenter) i = v i - localBlock.localCenter i := by simp
    rw [h4]
    exact abs_sub (v i) (localBlock.localCenter i)
  calc |(v - localBlock.localCenter) i| ≤ |v i| + |localBlock.localCenter i| := h3
    _ ≤ (1 / 2 + localBlock.blockScale / 10) + (1 + localBlock.blockScale / 10) := by
      exact add_le_add h1 h2
    _ = 3 / 2 + localBlock.blockScale / 5 := by ring

theorem parameter_block_representative_cinematic_pullback :
    ParameterBlockRepresentativeCinematicPullbackStatement := by
  intro hPYZ hCompact hProjection hContainment
  intro epsilon pyzLoss hepsilon hepsilon_lt hpyzLoss

  -- Step 0: PYZ threshold
  rcases hPYZ (100000 : ENNReal) (by norm_num) (by norm_num) pyzLoss hpyzLoss with
    ⟨threshold_pyz, hthreshold_pyz_pos, hthreshold_pyz_le, hPYZ_main⟩
  let threshold : ℝ := min threshold_pyz (1 / 5000)
  have hthreshold_pos : 0 < threshold := by positivity
  have hthreshold_lt_one : threshold < 1 := by
    have h : threshold ≤ 1 / 5000 := min_le_right _ _
    linarith

  refine ⟨threshold, hthreshold_pos, hthreshold_lt_one, ?_⟩
  intro delta hdelta hdelta_threshold F hvertical Y C lambda clustered hY_union localBlock representatives amplification perTubeThreshold hpt_nonzero hpt_ne_top hMass f hf_ns hf0

  set F_local := parameterLocalRepresentativeFamily representatives with hF_local_def
  set Y_local := parameterLocalRepresentativeShading representatives with hY_local_def

  -- Step 1: Compact subshading
  rcases hCompact F_local Y_local with ⟨Z, hZ_sub, hZ_mass, hZ_compact⟩

  -- Step 2: PYZ on the amplified one-dimensional Katz--Tao set.
  have hKT1 : amplification.amplified.IsKatzTao delta 1 100000 :=
    amplification.amplified_katzTao

  rcases hPYZ_main f hf_ns hf0 delta hdelta
      (by have h : threshold ≤ threshold_pyz := min_le_left _ _; linarith)
      amplification.amplified hKT1 amplification.amplified_half with
    ⟨selected, hselected_subset, hselected_sep, hselected_cover, hselected_mult⟩

  let c0 := localBlock.windowCenter
  let w_contain : ℝ := delta
  let r_source : ℝ := 20 * (delta + w_contain)
  have hdelta1 : delta ≤ 1 := by
    have h : threshold ≤ 1 / 5000 := min_le_right _ _
    linarith

  -- Vertical chart for representative family
  have hvertical_local : IsInVerticalChart F_local := by
    intro j
    have h_tube : F_local.tube j = F.tube (representatives.sourceIndex j) := by
      simp [F_local, parameterLocalRepresentativeFamily]
    rw [h_tube]
    exact hvertical (representatives.sourceIndex j)

  -- Window bound for representative family
  let indices := parameterLocalBlockIndices clustered localBlock.sourcePoints
  have hsource_in_indices : ∀ j : Fin F_local.card, representatives.sourceIndex j ∈ indices := by
    intro j
    have h : clustered.assign (representatives.sourceIndex j) = parameterLocalBlockPoint localBlock j :=
      representatives.source_assign j
    have h2 : parameterLocalBlockPoint localBlock j ∈ localBlock.sourcePoints :=
      (localBlock.sourcePoints.equivFin.symm j).2
    simp only [indices, parameterLocalBlockIndices, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [h]
    exact h2

  have hcZ : ∀ j, Z.carrier j ≠ ∅ → |(tubeParams j).c - c0| ≤ w_contain / 2 := by
    intro j hj
    have hYne : Y_local.carrier j ≠ ∅ := by
      intro h; have hsub := hZ_sub j; rw [h] at hsub; exact hj (Set.subset_empty_iff.mp hsub)
    let F_block := parameterLocalBlockFamily clustered localBlock.sourcePoints
    let Y_block := parameterLocalBlockShading clustered localBlock.sourcePoints
    have hmem : representatives.sourceIndex j ∈ indices := hsource_in_indices j
    let i_local : Fin F_block.card := indices.equivFin ⟨representatives.sourceIndex j, hmem⟩
    have h_eq_tube : (indices.equivFin.symm i_local).1 = representatives.sourceIndex j := by
      simp [i_local]
    have h_localY_ne : Y_block.carrier i_local ≠ ∅ := by
      have h4 : Y_block.carrier i_local = clustered.shading.carrier (indices.equivFin.symm i_local).1 := by
        rfl
      rw [h4, h_eq_tube]
      exact hYne
    have h_window : |(tubeParams (indices.equivFin.symm i_local).1).c - c0| ≤ delta / 2 :=
      localBlock.local_window i_local h_localY_ne
    have h_goal1 : |(tubeParams (representatives.sourceIndex j)).c - c0| ≤ delta / 2 := by
      have h5 : (indices.equivFin.symm i_local).1 = representatives.sourceIndex j := h_eq_tube
      rw [h5] at h_window
      exact h_window
    have h_tube_params : (tubeParams j).c = (tubeParams (representatives.sourceIndex j)).c := by
      have h1 : tubeParams j = tubeParamsOfTube (F_local.tube j) := rfl
      have h2 : tubeParams (representatives.sourceIndex j) = tubeParamsOfTube (F.tube (representatives.sourceIndex j)) := rfl
      have h3 : F_local.tube j = F.tube (representatives.sourceIndex j) := by
        simp [F_local, parameterLocalRepresentativeFamily]
      rw [h1, h2, h3]
    rw [h_tube_params]
    exact h_goal1

  -- Assignment for containment: exact slope curve
  let assign_contain (j : Fin F_local.card) :=
    slopeCurve f (tubeParams j).a (tubeParams j).b (tubeParams j).d

  have hassign_dist : ∀ j, Z.carrier j ≠ ∅ →
      Kakeya.Cinematic.c2Distance (slopeCurve f (tubeParams j).a (tubeParams j).b (tubeParams j).d)
        (assign_contain j) ≤ w_contain := by
    intro j _
    have h_eq : slopeCurve f (tubeParams j).a (tubeParams j).b (tubeParams j).d = assign_contain j := by rfl
    rw [h_eq]
    have h : Kakeya.Cinematic.c2Distance (assign_contain j) (assign_contain j) = 0 := by
      simp [Kakeya.Cinematic.c2Distance, dist_self]
    rw [h]
    exact hdelta.le

  have hassign' : ∀ j, Z.carrier j ≠ ∅ →
      |(tubeParams j).c - c0| ≤ w_contain / 2 ∧
        Kakeya.Cinematic.c2Distance (slopeCurve f (tubeParams j).a (tubeParams j).b (tubeParams j).d)
          (assign_contain j) ≤ w_contain := by
    intro j hi
    exact ⟨hcZ j hi, hassign_dist j hi⟩

  have hZ_union : Z.union ⊆ horizontalSlab 0 1 := by
    intro p hp
    rcases hp with ⟨j, hj⟩
    have h1 : p ∈ Y_local.union := ⟨j, hZ_sub j hj⟩
    have h2 : p ∈ clustered.shading.union := by
      rcases h1 with ⟨k, hk⟩
      exact ⟨representatives.sourceIndex k, hk⟩
    exact hY_union h2

  have hsource_containment : ∀ j, Z.carrier j ≠ ∅ →
      cinematicShear c0 '' (twistedProjection f '' Z.carrier j) ⊆
        Kakeya.Cinematic.graphNeighborhood (assign_contain j) r_source :=
    hContainment hdelta hdelta1 hdelta F_local hvertical_local Z hZ_union f hf_ns hf0 c0 assign_contain hassign'

  -- Assignment for amplified family
  let assign_source (j : Fin F_local.card) :=
    halfParameterSlopeCurve f (clustered.assign (representatives.sourceIndex j))

  have hj_mem : ∀ j : Fin F_local.card, clustered.assign (representatives.sourceIndex j) ∈ localBlock.sourcePoints := by
    intro j
    have h : clustered.assign (representatives.sourceIndex j) = parameterLocalBlockPoint localBlock j :=
      representatives.source_assign j
    rw [h]
    exact (localBlock.sourcePoints.equivFin.symm j).2

  -- In representative family, tubeParameterPoint3 = clustered.assign exactly
  have h_center_eq : ∀ j, tubeParameterPoint3 (representatives.sourceIndex j) = clustered.assign (representatives.sourceIndex j) := by
    intro j
    have h1 : tubeParameterPoint3 (representatives.sourceIndex j) = parameterLocalBlockPoint localBlock j :=
      representatives.source_point j
    have h2 : clustered.assign (representatives.sourceIndex j) = parameterLocalBlockPoint localBlock j :=
      representatives.source_assign j
    rw [h1, h2]

  have h_contain_source_dist : ∀ j, Z.carrier j ≠ ∅ →
      Kakeya.Cinematic.c2Distance (assign_contain j) (assign_source j) ≤ 260 * delta := by
    intro j _
    have h1 : assign_contain j = halfParameterSlopeCurve f (tubeParameterPoint3 (representatives.sourceIndex j)) :=
      rep_setup_assign_contain_eq f (representatives.sourceIndex j)
    rw [h1]
    have h_eq : tubeParameterPoint3 (representatives.sourceIndex j) = clustered.assign (representatives.sourceIndex j) :=
      h_center_eq j
    rw [h_eq]
    have h : Kakeya.Cinematic.c2Distance (assign_source j) (assign_source j) = 0 := by
      simp [Kakeya.Cinematic.c2Distance, dist_self]
    rw [h]
    positivity

  -- Lipschitz bound for shift functions
  have hblock_small : localBlock.blockScale ≤ 1 / 100 := by
    have h : 100 * localBlock.blockScale ≤ 1 := localBlock.blockScale_small
    linarith

  have hv_bound : ∀ v ∈ amplification.translations, ∀ i : Fin 3, |v i| ≤ 1 / 2 + localBlock.blockScale / 10 :=
    fun v hv i => rep_setup_v_bound v hv i

  have hcenter_bound : ∀ i : Fin 3, |localBlock.localCenter i| ≤ 1 + localBlock.blockScale / 10 :=
    fun i => rep_setup_center_bound localBlock i

  have hshift_param_bound : ∀ v ∈ amplification.translations, ∀ i : Fin 3,
      |(v - localBlock.localCenter) i| ≤ 3 / 2 + localBlock.blockScale / 5 :=
    fun v hv i => rep_setup_shift_bound v hv i

  have hshift_lipschitzOn : ∀ v ∈ amplification.translations,
      LipschitzOnWith (128 : NNReal) ((halfParameterSlopeCurve f (v - localBlock.localCenter)).extension)
        (Set.Icc (0 : ℝ) 1) := by
    intro v hv
    have hB1 : |(v - localBlock.localCenter) 1| ≤ 2 := by
      have h := hshift_param_bound v hv 1
      have h2 : 3 / 2 + localBlock.blockScale / 5 ≤ 2 := by
        have h3 : localBlock.blockScale ≤ 1 / 100 := hblock_small
        linarith
      linarith
    have hB2 : |(v - localBlock.localCenter) 2| ≤ 2 := by
      have h := hshift_param_bound v hv 2
      have h2 : 3 / 2 + localBlock.blockScale / 5 ≤ 2 := by
        have h3 : localBlock.blockScale ≤ 1 / 100 := hblock_small
        linarith
      linarith
    have h128 := halfParameterSlopeCurve_lipschitzOn_Icc01 f hf_ns hf0 (v - localBlock.localCenter) hB1 hB2
    exact h128

  let shift v := (halfParameterSlopeCurve f (v - localBlock.localCenter)).extension
  have hshift_meas : ∀ v ∈ amplification.translations, Measurable (shift v) := by
    intro v _
    exact (halfParameterSlopeCurve f (v - localBlock.localCenter)).extension_contDiff.continuous.measurable

  let A (j : Fin F_local.card) (v : Point 3) : Set (ℝ × ℝ) :=
    Kakeya.Cinematic.fiberwiseTranslate (shift v) ''
      (cinematicShear c0 '' (twistedProjection f '' Z.carrier j))

  let amplified_curve j v := (assign_source j).add (halfParameterSlopeCurve f (v - localBlock.localCenter))

  have hamplified_curve_eq : ∀ j v, amplified_curve j v =
      halfParameterSlopeCurve f ((clustered.assign (representatives.sourceIndex j) - localBlock.localCenter) + v) := by
    intro j v
    dsimp only [amplified_curve]
    have h9 : assign_source j = halfParameterSlopeCurve f (clustered.assign (representatives.sourceIndex j)) := by rfl
    have h_add : (assign_source j).add (halfParameterSlopeCurve f (v - localBlock.localCenter)) =
        halfParameterSlopeCurve f (clustered.assign (representatives.sourceIndex j) + (v - localBlock.localCenter)) := by
      rw [h9]
      exact (halfParameterSlopeCurve_add f (clustered.assign (representatives.sourceIndex j)) (v - localBlock.localCenter)).symm
    rw [h_add]
    have h_eq : clustered.assign (representatives.sourceIndex j) + (v - localBlock.localCenter) =
        (clustered.assign (representatives.sourceIndex j) - localBlock.localCenter) + v := by
      ext k; simp; abel
    rw [h_eq]

  classical

  have hamplified_in_family : ∀ j v, Z.carrier j ≠ ∅ → v ∈ amplification.translations →
      amplified_curve j v ∈ (halfParameterCinematicFamily f amplification.amplified).carrier := by
    intro j v hj hv
    have hjp : clustered.assign (representatives.sourceIndex j) ∈ localBlock.sourcePoints := hj_mem j
    let q := clustered.assign (representatives.sourceIndex j) - localBlock.localCenter
    have hq : q ∈ localBlock.centeredPoints := by
      rw [localBlock.centeredPoints_eq]
      exact Finset.mem_image.mpr ⟨clustered.assign (representatives.sourceIndex j), hjp, by
        simp [q] <;> abel⟩
    have hcopy : q + v ∈ amplification.amplified := by
      rw [amplification.amplified_eq]
      exact Finset.mem_biUnion.mpr ⟨v, hv, Finset.mem_image.mpr ⟨q, hq, rfl⟩⟩
    have h_main : amplified_curve j v = halfParameterSlopeCurve f (q + v) := by
      rw [hamplified_curve_eq j v]
      <;> simp [q] <;> abel
    rw [h_main]
    exact Finset.mem_image.mpr ⟨q + v, hcopy, rfl⟩

  classical

  have hselected_nonempty : selected.carrier.Nonempty := by
    rcases localBlock.centeredPoints_nonempty with ⟨q, hq⟩
    rcases amplification.translations_nonempty with ⟨v, hv⟩
    have hcopy : q + v ∈ amplification.amplified := amplification.copy_source v hv q hq
    let g := halfParameterSlopeCurve f (q + v)
    have hg : g ∈ (halfParameterCinematicFamily f amplification.amplified).carrier :=
      Finset.mem_image.mpr ⟨q + v, hcopy, rfl⟩
    rcases hselected_cover g hg with ⟨h, hh, _⟩
    exact ⟨h, hh⟩

  let assign_sel j v :=
    if h : Z.carrier j ≠ ∅ ∧ v ∈ amplification.translations then
      Classical.choose (hselected_cover (amplified_curve j v)
        (hamplified_in_family j v h.1 h.2))
    else hselected_nonempty.some

  have hassign_sel_mem : ∀ j v, Z.carrier j ≠ ∅ → v ∈ amplification.translations →
      assign_sel j v ∈ selected.carrier := by
    intro j v hj hv
    have h : Z.carrier j ≠ ∅ ∧ v ∈ amplification.translations := ⟨hj, hv⟩
    have h' := Classical.choose_spec (hselected_cover (amplified_curve j v)
      (hamplified_in_family j v hj hv))
    simpa [assign_sel, dif_pos h] using h'.1

  have hassign_sel_dist : ∀ j v, Z.carrier j ≠ ∅ → v ∈ amplification.translations →
      Kakeya.Cinematic.c2Distance (amplified_curve j v) (assign_sel j v) ≤ delta := by
    intro j v hj hv
    have h : Z.carrier j ≠ ∅ ∧ v ∈ amplification.translations := ⟨hj, hv⟩
    have h' := Classical.choose_spec (hselected_cover (amplified_curve j v)
      (hamplified_in_family j v hj hv))
    simpa [assign_sel, dif_pos h] using h'.2

  let L : NNReal := 128
  let r_sel : ℝ := (1 + L : ℝ) * r_source + 260 * delta + delta
  have hr_sel_le : r_sel ≤ 6000 * delta := by
    simp only [r_sel, r_source, w_contain, L]
    have h1 : (1 + (128 : NNReal) : ℝ) = 129 := by norm_num
    rw [h1]
    nlinarith

  -- Domain condition
  have h_domain : ∀ (j : Fin F_local.card), ∀ p ∈ cinematicShear c0 '' (twistedProjection f '' Z.carrier j),
      p.1 ∈ Set.Icc (0 : ℝ) 1 := by
    intro j p hp
    rcases hp with ⟨q, hq, rfl⟩
    rcases hq with ⟨x, hx, rfl⟩
    have h_xin : x ∈ Z.carrier j := hx
    have h_xunion : x ∈ Z.union := ⟨j, h_xin⟩
    have h_xslab : x ∈ horizontalSlab (0 : ℝ) 1 := hZ_union h_xunion
    have h_coord : (cinematicShear c0 (twistedProjection f x)).1 = x 2 := by
      simp [cinematicShear, twistedProjection]
    rw [h_coord]
    simpa [horizontalSlab] using h_xslab

  -- Containment of amplified pieces
  have hA_containment : ∀ j v, Z.carrier j ≠ ∅ → v ∈ amplification.translations →
      A j v ⊆ Kakeya.Cinematic.graphNeighborhood (assign_sel j v) r_sel := by
    intro j v hj hv
    let shift_curve : Kakeya.Cinematic.C2Function := halfParameterSlopeCurve f (v - localBlock.localCenter)
    have hlip : LipschitzOnWith L (shift_curve.extension) (Set.Icc (0 : ℝ) 1) :=
      hshift_lipschitzOn v hv
    have h1 : cinematicShear c0 '' (twistedProjection f '' Z.carrier j) ⊆
        Kakeya.Cinematic.graphNeighborhood (assign_contain j) r_source :=
      hsource_containment j hj
    have h_dist1 : Kakeya.Cinematic.c2Distance
        ((assign_contain j).add shift_curve) (amplified_curve j v) ≤ 260 * delta := by
      have h9 : assign_contain j = halfParameterSlopeCurve f (tubeParameterPoint3 (representatives.sourceIndex j)) :=
          rep_setup_assign_contain_eq f (representatives.sourceIndex j)
      have h_eq1 : (assign_contain j).add shift_curve =
          halfParameterSlopeCurve f (tubeParameterPoint3 (representatives.sourceIndex j) + (v - localBlock.localCenter)) := by
        rw [h9]
        exact (halfParameterSlopeCurve_add f (tubeParameterPoint3 (representatives.sourceIndex j)) (v - localBlock.localCenter)).symm
      have h_eq_arg : (clustered.assign (representatives.sourceIndex j) - localBlock.localCenter) + v =
          clustered.assign (representatives.sourceIndex j) + (v - localBlock.localCenter) := by
        ext k; simp; abel
      have h_eq2 : amplified_curve j v =
          halfParameterSlopeCurve f (clustered.assign (representatives.sourceIndex j) + (v - localBlock.localCenter)) := by
        rw [hamplified_curve_eq j v]
        rw [h_eq_arg]
      rw [h_eq1, h_eq2]
      have h := halfParameterSlopeCurve_c2Distance_le f hf_ns hf0
          (tubeParameterPoint3 (representatives.sourceIndex j) + (v - localBlock.localCenter))
          (clustered.assign (representatives.sourceIndex j) + (v - localBlock.localCenter))
      have h_dist_pt : dist (tubeParameterPoint3 (representatives.sourceIndex j) + (v - localBlock.localCenter))
            (clustered.assign (representatives.sourceIndex j) + (v - localBlock.localCenter)) =
          dist (tubeParameterPoint3 (representatives.sourceIndex j)) (clustered.assign (representatives.sourceIndex j)) := by
        simp [dist_eq_norm, add_assoc]
      rw [h_dist_pt] at h
      have h_eq2 : tubeParameterPoint3 (representatives.sourceIndex j) = clustered.assign (representatives.sourceIndex j) := h_center_eq j
      have h_final : dist (tubeParameterPoint3 (representatives.sourceIndex j)) (clustered.assign (representatives.sourceIndex j)) ≤ delta := by
        rw [h_eq2]
        have h0 : dist (clustered.assign (representatives.sourceIndex j)) (clustered.assign (representatives.sourceIndex j)) = 0 := dist_self _
        rw [h0]
        exact hdelta.le
      have h_bound : Kakeya.Cinematic.c2Distance (halfParameterSlopeCurve f (tubeParameterPoint3 (representatives.sourceIndex j) + (v - localBlock.localCenter))) (halfParameterSlopeCurve f (clustered.assign (representatives.sourceIndex j) + (v - localBlock.localCenter))) ≤ 260 * delta := by
        calc
          _ ≤ 260 * dist (tubeParameterPoint3 (representatives.sourceIndex j)) (clustered.assign (representatives.sourceIndex j)) := h
          _ ≤ 260 * delta := by gcongr
      exact h_bound
    have h_dist2 : Kakeya.Cinematic.c2Distance (amplified_curve j v) (assign_sel j v) ≤ delta :=
      hassign_sel_dist j v hj hv
    have hclose : Kakeya.Cinematic.c2Distance
        ((assign_contain j).add shift_curve) (assign_sel j v) ≤ 260 * delta + delta := by
      have h_tri : Kakeya.Cinematic.c2Distance ((assign_contain j).add shift_curve) (assign_sel j v) ≤
          Kakeya.Cinematic.c2Distance ((assign_contain j).add shift_curve) (amplified_curve j v) +
          Kakeya.Cinematic.c2Distance (amplified_curve j v) (assign_sel j v) :=
        dist_triangle _ _ _
      have h_sum : Kakeya.Cinematic.c2Distance ((assign_contain j).add shift_curve) (amplified_curve j v) +
          Kakeya.Cinematic.c2Distance (amplified_curve j v) (assign_sel j v) ≤ 260 * delta + delta := by
        exact add_le_add h_dist1 h_dist2
      exact h_tri.trans h_sum
    have hR : 0 ≤ r_source := by positivity
    have hε : 0 ≤ (260 * delta + delta : ℝ) := by positivity
    have h_main := amplified_geometric_containment_on c0 (assign_contain j) (assign_sel j v) shift_curve
      hR hε hlip
      (twistedProjection f '' Z.carrier j) h1 hclose (h_domain j)
    have h_radius : ((↑(1 + L) : ℝ) * r_source + (260 * delta + delta)) = r_sel := by
      simp [r_sel] <;> ring
    rw [h_radius] at h_main
    exact h_main

  -- Index set and multiplicity
  let Idx := Finset.product (Finset.univ : Finset (Fin F_local.card)) amplification.translations
  let m_amp : (ℝ × ℝ) → ENNReal := fun q =>
    ∑ idx ∈ Idx, (A idx.1 idx.2).indicator (fun _ => (1 : ENNReal)) q

  have hcont_shear : Continuous (cinematicShear c0) := by
    have h1c : Continuous (fun p : Point2 => p 1) := PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 1
    have h2c : Continuous (fun p : Point2 => p 0) := PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 0
    have h3c : Continuous (fun p : Point2 => p 0 - c0 * p 1) := h2c.sub (continuous_const.mul h1c)
    have h4 : (cinematicShear c0) = (fun p : Point2 => (p 1, p 0 - c0 * p 1)) := by
      funext p; simp [cinematicShear]
    rw [h4]
    have hprod : Continuous (fun p : Point2 => (p 1, p 0 - c0 * p 1)) := Continuous.prodMk h1c h3c
    exact hprod

  have hinj_shear : Function.Injective (cinematicShear c0) := by
    intro p q h
    have h1 : p 1 = q 1 := by simpa [cinematicShear] using congr_arg Prod.fst h
    have h2 : p 0 - c0 * p 1 = q 0 - c0 * q 1 := by simpa [cinematicShear] using congr_arg Prod.snd h
    have h3 : p 0 = q 0 := by
      rw [h1] at h2
      linarith
    ext i; fin_cases i <;> tauto

  have hA_compact : ∀ idx ∈ Idx, IsCompact (A idx.1 idx.2) := by
    intro idx _
    have h1 : IsCompact (Z.carrier idx.1) := hZ_compact idx.1
    have h2 : IsCompact (twistedProjection f '' Z.carrier idx.1) :=
      h1.image (continuous_twistedProjection f)
    have h3 : IsCompact (cinematicShear c0 '' (twistedProjection f '' Z.carrier idx.1)) :=
      h2.image hcont_shear
    have hcont_fiber : Continuous (Kakeya.Cinematic.fiberwiseTranslate (shift idx.2)) := by
      have hcont_h : Continuous (shift idx.2) :=
        (halfParameterSlopeCurve f (idx.2 - localBlock.localCenter)).extension_contDiff.continuous
      have h : Continuous (fun p : ℝ × ℝ => (p.1, p.2 + shift idx.2 p.1)) := by fun_prop
      have h_eq : Kakeya.Cinematic.fiberwiseTranslate (shift idx.2) =
          (fun p : ℝ × ℝ => (p.1, p.2 + shift idx.2 p.1)) := by
        funext p; simp [Kakeya.Cinematic.fiberwiseTranslate]
      rw [h_eq]; exact h
    exact h3.image hcont_fiber

  have hm_meas : Measurable m_amp := by
    apply Finset.measurable_sum
    intro idx hidx
    exact measurable_const.indicator ((hA_compact idx hidx).measurableSet)

  have hvol_eq : ∀ (s : Set Point2), IsCompact s →
      volume (cinematicShear c0 '' s) = volume s := by
    intro s hs
    have hmp : MeasurePreserving (cinematicShear c0) volume volume := cinematicShear_measurePreserving c0
    have hcont : Continuous (cinematicShear c0) := hcont_shear
    have hms : MeasurableSet (cinematicShear c0 '' s) := (hs.image hcont).measurableSet
    have hpreimage : (cinematicShear c0) ⁻¹' (cinematicShear c0 '' s) = s := by
      ext x; simp [hinj_shear.mem_set_image]
    have hmap_eq : Measure.map (cinematicShear c0) volume = volume := hmp.map_eq
    have h6 : Measure.map (cinematicShear c0) volume (cinematicShear c0 '' s) =
        volume ((cinematicShear c0) ⁻¹' (cinematicShear c0 '' s)) :=
      Measure.map_apply hmp.measurable hms
    have h7 : volume (cinematicShear c0 '' s) =
        Measure.map (cinematicShear c0) volume (cinematicShear c0 '' s) := by
      rw [hmap_eq]
    rw [h7, h6, hpreimage]

  have hintegral : ∫⁻ q, m_amp q ≥
      amplification.translations.enncard * (Z.mass / ENNReal.ofReal (20 * delta)) := by
    have hproj := hProjection hdelta F_local hvertical_local Z hZ_compact f
    have harea : ∀ j, volume (Z.carrier j) ≤
        ENNReal.ofReal (20 * delta) * volume (twistedProjection f '' Z.carrier j) :=
      fun j => (hproj j).2
    have hsum1_lintegral : Z.mass / ENNReal.ofReal (20 * delta) ≤
        ∫⁻ p, twistedProjectionMultiplicity Z f p :=
      mass_div_le_lintegral_twistedProjectionMultiplicity hdelta Z f
        (fun j => (hproj j).1) harea
    have hsum1_eq : (∫⁻ p, twistedProjectionMultiplicity Z f p) =
        ∑ j : Fin F_local.card, volume (twistedProjection f '' Z.carrier j) :=
      lintegral_twistedProjectionMultiplicity Z f (fun j => (hproj j).1)
    have hsum1 : Z.mass / ENNReal.ofReal (20 * delta) ≤
        ∑ j : Fin F_local.card, volume (twistedProjection f '' Z.carrier j) :=
      hsum1_lintegral.trans (le_of_eq hsum1_eq)
    have hmain : ∫⁻ q, m_amp q =
        amplification.translations.enncard *
          ∑ j : Fin F_local.card, volume (twistedProjection f '' Z.carrier j) := by
      have hA_meas : ∀ idx ∈ Idx, MeasurableSet (A idx.1 idx.2) :=
        fun idx hidx => (hA_compact idx hidx).measurableSet
      have h1 : ∫⁻ q, m_amp q = ∑ idx ∈ Idx, volume (A idx.1 idx.2) := by
        have h_unfold : m_amp = fun q => ∑ idx ∈ Idx, (A idx.1 idx.2).indicator (fun _ : ℝ × ℝ => (1 : ENNReal)) q := by
          funext q; rfl
        rw [h_unfold]
        have h_meas : ∀ idx ∈ Idx, Measurable ((A idx.1 idx.2).indicator (fun _ : ℝ × ℝ => (1 : ENNReal))) :=
          fun idx hidx => measurable_const.indicator (hA_meas idx hidx)
        rw [MeasureTheory.lintegral_finsetSum Idx
          (f := fun idx => (A idx.1 idx.2).indicator (fun _ : ℝ × ℝ => (1 : ENNReal)))
          h_meas]
        apply Finset.sum_congr rfl
        intro idx hidx
        rw [MeasureTheory.lintegral_indicator_const (hA_meas idx hidx)]
        <;> simp
      rw [h1]
      have h2 : ∑ idx ∈ Idx, volume (A idx.1 idx.2) =
          ∑ v ∈ amplification.translations, ∑ j : Fin F_local.card, volume (A j v) := by
        let f : (Fin F_local.card × Point 3) → ENNReal := fun p => volume (A p.1 p.2)
        have h_sp : ∑ idx ∈ (Finset.univ : Finset (Fin F_local.card)) ×ˢ amplification.translations, f idx =
            ∑ i ∈ (Finset.univ : Finset (Fin F_local.card)), ∑ v ∈ amplification.translations, f (i, v) :=
          Finset.sum_product (Finset.univ : Finset (Fin F_local.card)) amplification.translations f
        have h_eq1 : ∑ idx ∈ Idx, volume (A idx.1 idx.2) =
            ∑ idx ∈ (Finset.univ : Finset (Fin F_local.card)) ×ˢ amplification.translations, f idx := by
          congr with ⟨i, v⟩ <;> rfl
        have h_eq2 : ∑ i ∈ (Finset.univ : Finset (Fin F_local.card)), ∑ v ∈ amplification.translations, f (i, v) =
            ∑ v ∈ amplification.translations, ∑ i : Fin F_local.card, volume (A i v) := by
          rw [Finset.sum_comm]
          <;> rfl
        rw [h_eq1, h_sp, h_eq2]
      rw [h2]
      have h3 : ∑ v ∈ amplification.translations, ∑ j : Fin F_local.card, volume (A j v) =
          ∑ v ∈ amplification.translations, ∑ j : Fin F_local.card,
            volume (cinematicShear c0 '' (twistedProjection f '' Z.carrier j)) := by
        apply Finset.sum_congr rfl; intro v hv
        apply Finset.sum_congr rfl; intro j _
        exact Kakeya.Cinematic.volume_fiberwiseTranslate_image
          (shift v) (hshift_meas v hv) _
      rw [h3]
      have h4 : ∑ v ∈ amplification.translations, ∑ j : Fin F_local.card,
            volume (cinematicShear c0 '' (twistedProjection f '' Z.carrier j)) =
          ∑ v ∈ amplification.translations, ∑ j : Fin F_local.card,
            volume (twistedProjection f '' Z.carrier j) := by
        apply Finset.sum_congr rfl; intro v _
        apply Finset.sum_congr rfl; intro j _
        have hs : IsCompact (twistedProjection f '' Z.carrier j) :=
          (hZ_compact j).image (continuous_twistedProjection f)
        exact hvol_eq (twistedProjection f '' Z.carrier j) hs
      rw [h4]
      simp [Finset.mul_sum] <;> rfl
    rw [hmain]
    gcongr

  let M := parameterBlockRepresentativeCopiedFiberCap

  have h_get_param : ∀ g ∈ selected.carrier,
      ∃ p_g ∈ amplification.amplified, g = halfParameterSlopeCurve f p_g := by
    intro g hg
    have hsub : g ∈ (halfParameterCinematicFamily f amplification.amplified).carrier :=
      hselected_subset hg
    rcases Finset.mem_image.mp hsub with ⟨p_g, hpg, rfl⟩
    exact ⟨p_g, hpg, rfl⟩

  -- Simplified fiber cap: q1 is injective on Bad, so Bad.card ≤ S.card ≤ 12500000
  have hfiber : ∀ g ∈ selected.toFinset,
      ((Idx.filter fun idx : Fin F_local.card × Point 3 =>
          Z.carrier idx.1 ≠ ∅ ∧ assign_sel idx.1 idx.2 = g).card : ENNReal) ≤ M := by
    intro g hg
    let Bad := Idx.filter fun idx : Fin F_local.card × Point 3 =>
      Z.carrier idx.1 ≠ ∅ ∧ assign_sel idx.1 idx.2 = g
    have hg_carrier : g ∈ selected.carrier := selected.finite.mem_toFinset.mp hg
    rcases h_get_param g hg_carrier with ⟨p_g, hpg, h_eq_g⟩

    let q1 : (Fin F_local.card × Point 3) → Point 3 := fun idx =>
      clustered.assign (representatives.sourceIndex idx.1) - localBlock.localCenter + idx.2

    have h_ball : ∀ idx ∈ Bad, dist (q1 idx) p_g ≤ 125 * delta := by
      intro idx hidx
      have h1 : Z.carrier idx.1 ≠ ∅ ∧ assign_sel idx.1 idx.2 = g :=
        (Finset.mem_filter.mp hidx).2
      have h2 : idx ∈ Idx := (Finset.mem_filter.mp hidx).1
      have h3 : idx.2 ∈ amplification.translations := (Finset.mem_product.mp h2).2
      have h4 : Kakeya.Cinematic.c2Distance (amplified_curve idx.1 idx.2) (assign_sel idx.1 idx.2) ≤ delta :=
        hassign_sel_dist idx.1 idx.2 h1.1 h3
      have h4g : Kakeya.Cinematic.c2Distance (amplified_curve idx.1 idx.2) g ≤ delta := by
        exact h1.2 ▸ h4
      have h5 : amplified_curve idx.1 idx.2 = halfParameterSlopeCurve f (q1 idx) :=
        hamplified_curve_eq idx.1 idx.2
      have h6 : dist (q1 idx) p_g ≤ 125 * Kakeya.Cinematic.c2Distance
            (halfParameterSlopeCurve f (q1 idx)) (halfParameterSlopeCurve f p_g) :=
        halfParameterSlopeCurve_dist_le f hf_ns hf0 (q1 idx) p_g
      have h7 : Kakeya.Cinematic.c2Distance (halfParameterSlopeCurve f (q1 idx))
            (halfParameterSlopeCurve f p_g) ≤ delta := by
        rw [←h5, ←h_eq_g]
        exact h4g
      linarith

    let S := amplification.amplified.filter fun y => dist y p_g ≤ 125 * delta
    have h125pos : 0 < 125 * delta := by positivity
    have h125le1 : 125 * delta ≤ 1 := by
      have hth : threshold ≤ 1 / 5000 := min_le_right _ _
      linarith [hdelta_threshold, hth]
    have hdelta_le_125 : delta ≤ 125 * delta := by
      have h : 0 < delta := hdelta
      linarith
    have hS_card : (S.card : ENNReal) ≤ 100000 * Kakeya.realRpowENN ((125 * delta) / delta) 1 := by
      simpa [S, DiscreteSet.ballCount] using hKT1 p_g (125 * delta) hdelta_le_125 h125le1
    have hS_card2 : (S.card : ENNReal) ≤ 12500000 := by
      have h : Kakeya.realRpowENN ((125 * delta) / delta) 1 = 125 := by
        simp [Kakeya.realRpowENN]
        <;> field_simp [hdelta.ne'] <;> norm_num
      rw [h] at hS_card
      exact hS_card.trans (by norm_num)

    have h_f_map_mem : ∀ idx ∈ Bad, q1 idx ∈ S := by
      intro idx hidx
      have h2 : Z.carrier idx.1 ≠ ∅ := (Finset.mem_filter.mp hidx).2.1
      have h3 : idx.2 ∈ amplification.translations := by
        have h4 : idx ∈ Idx := (Finset.mem_filter.mp hidx).1
        have h4' := Finset.mem_product.mp h4
        exact h4'.2
      have hq_centered : clustered.assign (representatives.sourceIndex idx.1) - localBlock.localCenter ∈ localBlock.centeredPoints := by
        rw [localBlock.centeredPoints_eq]
        exact Finset.mem_image.mpr ⟨clustered.assign (representatives.sourceIndex idx.1), hj_mem idx.1, rfl⟩
      have h1 : q1 idx ∈ amplification.amplified := by
        rw [amplification.amplified_eq]
        exact Finset.mem_biUnion.mpr ⟨idx.2, h3, Finset.mem_image.mpr ⟨clustered.assign (representatives.sourceIndex idx.1) - localBlock.localCenter, hq_centered, rfl⟩⟩
      have h_ball' : dist (q1 idx) p_g ≤ 125 * delta := h_ball idx hidx
      exact Finset.mem_filter.mpr ⟨h1, h_ball'⟩

    -- Key injectivity of q1 on Bad
    have h_inj : Set.InjOn q1 (Bad : Set (Fin F_local.card × Point 3)) := by
      intro idx1 hidx1 idx2 hidx2 h_eq
      have h1_1 : idx1.2 ∈ amplification.translations := by
        have h4 : idx1 ∈ Idx := (Finset.mem_filter.mp hidx1).1
        exact (Finset.mem_product.mp h4).2
      have h2_1 : idx2.2 ∈ amplification.translations := by
        have h4 : idx2 ∈ Idx := (Finset.mem_filter.mp hidx2).1
        exact (Finset.mem_product.mp h4).2
      -- Show idx1.2 = idx2.2 using translated_disjoint
      have h_v_eq : idx1.2 = idx2.2 := by
        by_contra h_v_ne
        have h_disj : Disjoint (translateParameterSet localBlock.centeredPoints idx1.2)
            (translateParameterSet localBlock.centeredPoints idx2.2) :=
          amplification.translated_disjoint h1_1 h2_1 h_v_ne
        have hq1_centered : clustered.assign (representatives.sourceIndex idx1.1) - localBlock.localCenter ∈ localBlock.centeredPoints := by
          rw [localBlock.centeredPoints_eq]
          exact Finset.mem_image.mpr ⟨clustered.assign (representatives.sourceIndex idx1.1), hj_mem idx1.1, rfl⟩
        have hq2_centered : clustered.assign (representatives.sourceIndex idx2.1) - localBlock.localCenter ∈ localBlock.centeredPoints := by
          rw [localBlock.centeredPoints_eq]
          exact Finset.mem_image.mpr ⟨clustered.assign (representatives.sourceIndex idx2.1), hj_mem idx2.1, rfl⟩
        have h4 : q1 idx1 ∈ translateParameterSet localBlock.centeredPoints idx1.2 :=
          Finset.mem_image.mpr ⟨clustered.assign (representatives.sourceIndex idx1.1) - localBlock.localCenter, hq1_centered, rfl⟩
        have h5 : q1 idx1 ∈ translateParameterSet localBlock.centeredPoints idx2.2 := by
          rw [h_eq]
          exact Finset.mem_image.mpr ⟨clustered.assign (representatives.sourceIndex idx2.1) - localBlock.localCenter, hq2_centered, rfl⟩
        have h_empty : (translateParameterSet localBlock.centeredPoints idx1.2) ∩ (translateParameterSet localBlock.centeredPoints idx2.2) = ∅ :=
          Finset.disjoint_iff_inter_eq_empty.mp h_disj
        have h_inter : q1 idx1 ∈ (translateParameterSet localBlock.centeredPoints idx1.2) ∩ (translateParameterSet localBlock.centeredPoints idx2.2) :=
          Finset.mem_inter.mpr ⟨h4, h5⟩
        rw [h_empty] at h_inter
        simpa using h_inter
      -- Now show idx1.1 = idx2.1
      have h_assign_eq : clustered.assign (representatives.sourceIndex idx1.1) = clustered.assign (representatives.sourceIndex idx2.1) := by
        have h_eq2 : q1 idx1 = q1 idx2 := h_eq
        simp only [q1] at h_eq2
        rw [h_v_eq] at h_eq2
        simpa using add_right_cancel h_eq2
      have hsa1 : clustered.assign (representatives.sourceIndex idx1.1) = parameterLocalBlockPoint localBlock idx1.1 :=
        representatives.source_assign idx1.1
      have hsa2 : clustered.assign (representatives.sourceIndex idx2.1) = parameterLocalBlockPoint localBlock idx2.1 :=
        representatives.source_assign idx2.1
      have h_point_eq : parameterLocalBlockPoint localBlock idx1.1 = parameterLocalBlockPoint localBlock idx2.1 := by
        rw [←hsa1, ←hsa2]
        exact h_assign_eq
      have h_i_eq : idx1.1 = idx2.1 := by
        have h_inj_point : Function.Injective (parameterLocalBlockPoint localBlock) := by
          intro a b h
          apply localBlock.sourcePoints.equivFin.symm.injective
          exact Subtype.ext h
        exact h_inj_point h_point_eq
      exact Prod.ext h_i_eq h_v_eq

    have h_image_subset : Bad.image q1 ⊆ S := by
      intro x hx
      rcases Finset.mem_image.mp hx with ⟨idx, hidx, rfl⟩
      exact h_f_map_mem idx hidx
    have h_card_image : (Bad.image q1).card = Bad.card :=
      Finset.card_image_of_injOn h_inj
    have h_card_le : Bad.card ≤ S.card := by
      rw [←h_card_image]
      exact Finset.card_le_card h_image_subset
    have h_final : (Bad.card : ENNReal) ≤ (S.card : ENNReal) := by exact_mod_cast h_card_le
    exact h_final.trans hS_card2

  have hpointwise : ∀ q, m_amp q ≤ M * cinematicMultiplicityENN selected r_sel q := by
    intro q
    classical
    let contributing := Idx.filter fun idx => Z.carrier idx.1 ≠ ∅ ∧ q ∈ A idx.1 idx.2
    have h1 : m_amp q = ∑ idx ∈ contributing, (1 : ENNReal) := by
      have hA_empty : ∀ (j : Fin F_local.card) (v : Point 3), Z.carrier j = ∅ → A j v = ∅ := by
        intro j v h
        simp only [A, h, Set.image_empty]
      have h_iff : ∀ idx ∈ Idx, q ∈ A idx.1 idx.2 ↔ idx ∈ contributing := by
        intro idx hidx
        constructor
        · intro hq
          have hne : Z.carrier idx.1 ≠ ∅ := by
            by_contra h
            have h' : A idx.1 idx.2 = ∅ := hA_empty idx.1 idx.2 h
            rw [h'] at hq
            simpa using hq
          exact Finset.mem_filter.mpr ⟨hidx, ⟨hne, hq⟩⟩
        · intro h
          exact (Finset.mem_filter.mp h).2.2
      have h_indicator : ∀ idx ∈ Idx, (A idx.1 idx.2).indicator (fun _ : ℝ × ℝ => (1 : ENNReal)) q =
          if idx ∈ contributing then (1 : ENNReal) else 0 := by
        intro idx hidx
        by_cases h : idx ∈ contributing
        · have hq : q ∈ A idx.1 idx.2 := (h_iff idx hidx).mpr h
          simp [h, hq, Set.indicator_of_mem]
        · have hq : q ∉ A idx.1 idx.2 := by
            intro hq'
            exact h ((h_iff idx hidx).mp hq')
          simp [h, hq, Set.indicator_of_notMem]
      calc m_amp q
        = ∑ idx ∈ Idx, (A idx.1 idx.2).indicator (fun _ : ℝ × ℝ => (1 : ENNReal)) q := by rfl
      _ = ∑ idx ∈ Idx, (if idx ∈ contributing then (1 : ENNReal) else 0) := by
          apply Finset.sum_congr rfl; intro idx hidx; exact h_indicator idx hidx
      _ = ∑ idx ∈ contributing, (1 : ENNReal) := by
          have h_filter : Idx.filter (fun idx => idx ∈ contributing) = contributing := by
            ext x
            simp only [Finset.mem_filter]
            <;> constructor
            · rintro ⟨h1, h2⟩; exact h2
            · intro h; exact ⟨(Finset.mem_filter.mp h).1, h⟩
          have h_sum1 : ∑ idx ∈ Idx, (if idx ∈ contributing then (1 : ENNReal) else 0) =
              (contributing.card : ENNReal) := by
            rw [Finset.sum_boole, h_filter]
            <;> rfl
          have h_sum2 : ∑ idx ∈ contributing, (1 : ENNReal) = (contributing.card : ENNReal) := by
            simp
          rw [h_sum1, h_sum2]
    rw [h1]
    have h2 : ∀ idx ∈ contributing, assign_sel idx.1 idx.2 ∈ selected.toFinset := by
      intro idx hidx
      have h3 : Z.carrier idx.1 ≠ ∅ := (Finset.mem_filter.mp hidx).2.1
      have h4 : idx.2 ∈ amplification.translations := by
        have h5 : idx ∈ Idx := (Finset.mem_filter.mp hidx).1
        have h5' := Finset.mem_product.mp h5
        exact h5'.2
      have h_mem : assign_sel idx.1 idx.2 ∈ selected.carrier := hassign_sel_mem idx.1 idx.2 h3 h4
      exact selected.finite.mem_toFinset.mpr h_mem
    have h3 : ∀ idx ∈ contributing, q ∈ Kakeya.Cinematic.graphNeighborhood (assign_sel idx.1 idx.2) r_sel := by
      intro idx hidx
      have h4 : Z.carrier idx.1 ≠ ∅ := (Finset.mem_filter.mp hidx).2.1
      have h5 : idx.2 ∈ amplification.translations := by
        have h6 : idx ∈ Idx := (Finset.mem_filter.mp hidx).1
        have h6' := Finset.mem_product.mp h6
        exact h6'.2
      have h7 : q ∈ A idx.1 idx.2 := (Finset.mem_filter.mp hidx).2.2
      exact hA_containment idx.1 idx.2 h4 h5 h7
    have h4 : ∑ idx ∈ contributing, (1 : ENNReal) ≤
        ∑ y ∈ selected.toFinset, M * (Kakeya.Cinematic.graphNeighborhood y r_sel).indicator (fun _ => (1 : ENNReal)) q := by
      have h_main : ∑ y ∈ selected.toFinset, ∑ idx ∈ contributing.filter (fun idx => assign_sel idx.1 idx.2 = y), (1 : ENNReal) =
          ∑ idx ∈ contributing, (1 : ENNReal) := by
        exact Finset.sum_fiberwise_of_maps_to h2 (fun _ => (1 : ENNReal))
      rw [←h_main]
      apply Finset.sum_le_sum
      intro y hy
      by_cases hq : q ∈ Kakeya.Cinematic.graphNeighborhood y r_sel
      · have h5 : ((contributing.filter fun idx => assign_sel idx.1 idx.2 = y).card : ENNReal) ≤ M := by
          have h6 : contributing.filter fun idx => assign_sel idx.1 idx.2 = y ⊆
              Idx.filter fun idx => Z.carrier idx.1 ≠ ∅ ∧ assign_sel idx.1 idx.2 = y := by
            intro idx hidx
            have h7 : idx ∈ contributing := (Finset.mem_filter.mp hidx).1
            have h8 : Z.carrier idx.1 ≠ ∅ := (Finset.mem_filter.mp h7).2.1
            have h9 : assign_sel idx.1 idx.2 = y := (Finset.mem_filter.mp hidx).2
            exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp h7).1, ⟨h8, h9⟩⟩
          have h7 : ((contributing.filter fun idx => assign_sel idx.1 idx.2 = y).card : ENNReal) ≤
              ((Idx.filter fun idx => Z.carrier idx.1 ≠ ∅ ∧ assign_sel idx.1 idx.2 = y).card : ENNReal) := by
            exact_mod_cast Finset.card_le_card h6
          exact h7.trans (hfiber y hy)
        have h_sum_card : ∑ idx ∈ contributing.filter (fun idx => assign_sel idx.1 idx.2 = y), (1 : ENNReal) =
            ((contributing.filter fun idx => assign_sel idx.1 idx.2 = y).card : ENNReal) := by
          simp
        have h_ind : (Kakeya.Cinematic.graphNeighborhood y r_sel).indicator (fun _ => (1 : ENNReal)) q = 1 := by
          rw [Set.indicator_of_mem hq] <;> norm_num
        rw [h_sum_card, h_ind]
        simp
        exact h5
      · have h_empty : (contributing.filter fun idx => assign_sel idx.1 idx.2 = y) = ∅ := by
          by_contra hne
          have hne' : (contributing.filter fun idx => assign_sel idx.1 idx.2 = y).Nonempty :=
            Finset.nonempty_iff_ne_empty.mpr hne
          rcases hne' with ⟨idx, hidx⟩
          have h7 : idx ∈ contributing := (Finset.mem_filter.mp hidx).1
          have h8 : q ∈ Kakeya.Cinematic.graphNeighborhood (assign_sel idx.1 idx.2) r_sel := h3 idx h7
          have h9 : assign_sel idx.1 idx.2 = y := (Finset.mem_filter.mp hidx).2
          rw [h9] at h8
          exact hq h8
        have h_sum_card : ∑ idx ∈ contributing.filter (fun idx => assign_sel idx.1 idx.2 = y), (1 : ENNReal) = 0 := by
          simp [h_empty]
        rw [h_sum_card]
        simp [Set.indicator_of_notMem hq]
        <;> positivity
    have h_eq2 : M * cinematicMultiplicityENN selected r_sel q =
        ∑ y ∈ selected.toFinset, M * (Kakeya.Cinematic.graphNeighborhood y r_sel).indicator (fun _ => (1 : ENNReal)) q := by
      simp [cinematicMultiplicityENN, Finset.mul_sum]
      <;> rfl
    rw [h_eq2]
    exact h4

  have hLp : eLpNorm m_amp (3 / 2 : ENNReal) volume ≤
      M * ENNReal.ofReal (Real.rpow delta (-pyzLoss)) := by
    have hgraph_meas : Measurable (cinematicMultiplicityENN selected r_sel) :=
      measurable_cinematicMultiplicityENN selected r_sel
    have hnorm : eLpNorm m_amp (3 / 2 : ENNReal) volume ≤
        M * eLpNorm (cinematicMultiplicityENN selected r_sel) (3 / 2 : ENNReal) volume := by
      apply MeasureTheory.eLpNorm_le_mul_eLpNorm_of_ae_le_mul''
        (p := (3 / 2 : ENNReal)) hgraph_meas.aestronglyMeasurable
      exact Filter.Eventually.of_forall hpointwise
    have hmon : eLpNorm (cinematicMultiplicityENN selected r_sel) (3 / 2 : ENNReal) volume ≤
        eLpNorm (cinematicMultiplicityENN selected (6000 * delta)) (3 / 2 : ENNReal) volume :=
      eLpNorm_cinematicMultiplicityENN_mono_radius selected hr_sel_le (3 / 2 : ENNReal)
    have h_eq : eLpNorm (cinematicMultiplicityENN selected (6000 * delta)) (3 / 2 : ENNReal) volume =
        eLpNorm (Kakeya.Cinematic.multiplicity selected (6000 * delta)) (3 / 2 : ENNReal) volume :=
      eLpNorm_cinematicMultiplicityENN selected (6000 * delta) (3 / 2 : ENNReal)
    have hpyznorm : eLpNorm (Kakeya.Cinematic.multiplicity selected (6000 * delta))
        (3 / 2 : ENNReal) volume ≤ ENNReal.ofReal (Real.rpow delta (-pyzLoss)) :=
      hselected_mult
    have h_le : eLpNorm (cinematicMultiplicityENN selected r_sel) (3 / 2 : ENNReal) volume ≤
        ENNReal.ofReal (Real.rpow delta (-pyzLoss)) := by
      calc
        eLpNorm (cinematicMultiplicityENN selected r_sel) (3 / 2 : ENNReal) volume
          ≤ eLpNorm (cinematicMultiplicityENN selected (6000 * delta)) (3 / 2 : ENNReal) volume := hmon
        _ = eLpNorm (Kakeya.Cinematic.multiplicity selected (6000 * delta)) (3 / 2 : ENNReal) volume := h_eq
        _ ≤ ENNReal.ofReal (Real.rpow delta (-pyzLoss)) := hpyznorm
    have h_final : M * eLpNorm (cinematicMultiplicityENN selected r_sel) (3 / 2 : ENNReal) volume ≤
        M * ENNReal.ofReal (Real.rpow delta (-pyzLoss)) := by
      gcongr
    exact hnorm.trans h_final

  let U : Set (ℝ × ℝ) := {q | m_amp q ≠ 0}
  have hU_meas : MeasurableSet U := by
    have h1 : MeasurableSet ({0} : Set ENNReal) := measurableSet_singleton 0
    exact (hm_meas h1).compl

  have hholder : volume U ≥ ((amplification.translations.enncard * Z.mass / ENNReal.ofReal (20 * delta)) /
        (M * ENNReal.ofReal (Real.rpow delta (-pyzLoss)))) ^ 3 := by
    have h_main : volume U ≥ ((∫⁻ q, m_amp q) /
          (M * ENNReal.ofReal (Real.rpow delta (-pyzLoss)))) ^ 3 :=
      holder_volume_lower_bound hm_meas (∫⁻ q, m_amp q)
        (M * ENNReal.ofReal (Real.rpow delta (-pyzLoss))) rfl hLp
    have h_inner_eq : amplification.translations.enncard * (Z.mass / ENNReal.ofReal (20 * delta)) =
        (amplification.translations.enncard * Z.mass) / ENNReal.ofReal (20 * delta) := by
      simp [div_eq_mul_inv, mul_assoc]
    have h_inner : (amplification.translations.enncard * Z.mass) / ENNReal.ofReal (20 * delta) ≤ ∫⁻ q, m_amp q := by
      rw [←h_inner_eq]
      exact hintegral
    have h_div : ((amplification.translations.enncard * Z.mass) / ENNReal.ofReal (20 * delta)) /
          (M * ENNReal.ofReal (Real.rpow delta (-pyzLoss))) ≤
        (∫⁻ q, m_amp q) / (M * ENNReal.ofReal (Real.rpow delta (-pyzLoss))) := by
      simpa [div_eq_mul_inv] using mul_le_mul_right' h_inner _
    have h_S_le : (((amplification.translations.enncard * Z.mass) / ENNReal.ofReal (20 * delta)) /
          (M * ENNReal.ofReal (Real.rpow delta (-pyzLoss)))) ^ 3 ≤
        ((∫⁻ q, m_amp q) / (M * ENNReal.ofReal (Real.rpow delta (-pyzLoss)))) ^ 3 := by
      gcongr
    exact h_S_le.trans h_main

  classical
  have hU_eq : U = ⋃ v ∈ amplification.translations,
      Kakeya.Cinematic.fiberwiseTranslate (shift v) ''
        (cinematicShear c0 '' twistedUnion Z f) := by
    ext q
    simp only [U, Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · intro hq
      have h5 : m_amp q ≠ 0 := hq
      have h6 : ∃ idx ∈ Idx, q ∈ A idx.1 idx.2 := by
        by_contra h7
        have h7' : ∀ idx ∈ Idx, q ∉ A idx.1 idx.2 := by
          intro idx hidx h
          exact h7 ⟨idx, hidx, h⟩
        have h8 : m_amp q = 0 := by
          dsimp only [m_amp]
          have h9 : ∀ idx ∈ Idx, (A idx.1 idx.2).indicator (fun _ : ℝ × ℝ => (1 : ENNReal)) q = 0 := by
            intro idx hidx
            have h10 : q ∉ A idx.1 idx.2 := h7' idx hidx
            rw [Set.indicator_of_notMem h10]
            <;> rfl
          rw [Finset.sum_congr rfl h9, Finset.sum_const_zero]
        exact h5 h8
      rcases h6 with ⟨idx, hidx, hqA⟩
      have h9 : idx.2 ∈ amplification.translations := (Finset.mem_product.mp hidx).2
      rcases hqA with ⟨w, hw, h_eq⟩
      rcases hw with ⟨y, hy, h_eq2⟩
      rcases hy with ⟨z, hz, h_eq3⟩
      have hz1 : z ∈ Z.union := ⟨idx.1, hz⟩
      have hz2 : twistedProjection f z ∈ twistedUnion Z f := ⟨z, hz1, rfl⟩
      let w' := cinematicShear c0 (twistedProjection f z)
      have hw' : w' ∈ cinematicShear c0 '' twistedUnion Z f := ⟨twistedProjection f z, hz2, rfl⟩
      have h_eq' : Kakeya.Cinematic.fiberwiseTranslate (shift idx.2) w' = q := by
        dsimp only [w']
        rw [h_eq3, h_eq2, h_eq]
      exact ⟨idx.2, h9, w', hw', h_eq'⟩
    · rintro ⟨v, hv, hq⟩
      rcases hq with ⟨w, hw, h_eq⟩
      rcases hw with ⟨y, hy, h_eq2⟩
      rcases hy with ⟨z, hz, h_eq3⟩
      rcases hz with ⟨j, hj⟩
      have h11 : q ∈ A j v := by
        dsimp only [A]
        refine ⟨cinematicShear c0 (twistedProjection f z), ?_, ?_⟩
        · refine ⟨twistedProjection f z, ?_, rfl⟩
          exact ⟨z, hj, rfl⟩
        · rw [h_eq3, h_eq2, h_eq]
      have h12 : (j, v) ∈ Idx := by
        apply Finset.mem_product.mpr
        exact ⟨Finset.mem_univ j, hv⟩
      have h13 : m_amp q ≠ 0 := by
        let g : (Fin F_local.card × Point 3) → ENNReal := fun idx =>
          (A idx.1 idx.2).indicator (fun _ : ℝ × ℝ => (1 : ENNReal)) q
        have h14 : g (j, v) = 1 := by
          dsimp only [g]
          rw [Set.indicator_of_mem h11] <;> norm_num
        have h15 : 1 ≤ m_amp q := by
          have h_mamp : m_amp q = ∑ idx ∈ Idx, g idx := by rfl
          rw [h_mamp]
          have h_ge : g (j, v) ≤ ∑ idx ∈ Idx, g idx :=
            Finset.single_le_sum (fun _ _ => by positivity) h12
          rw [h14] at h_ge
          exact h_ge
        have h16 : 0 < m_amp q := by
          exact lt_of_lt_of_le (show (0 : ENNReal) < 1 from by norm_num) h15
        exact ne_of_gt h16
      exact h13

  have hdiv : volume U ≤ amplification.translations.enncard *
        volume (cinematicShear c0 '' twistedUnion Z f) := by
    rw [hU_eq]
    exact volume_biUnion_fiberwiseTranslate_le amplification.translations
      (fun v => shift v) hshift_meas (cinematicShear c0 '' twistedUnion Z f)

  have hvol_eq2 : volume (cinematicShear c0 '' twistedUnion Z f) = volume (twistedUnion Z f) := by
    have hcompact : IsCompact (twistedUnion Z f) := by
      have h1 : IsCompact Z.union := by
        have h2 : Z.union = ⋃ (i : Fin _), Z.carrier i := by
          ext x; simp [Streamlined.Shading.union]
        rw [h2]
        exact isCompact_iUnion (fun i => hZ_compact i)
      exact h1.image (continuous_twistedProjection f)
    exact hvol_eq (twistedUnion Z f) hcompact

  have hfinal : volume (twistedUnion Z f) ≥
      (((amplification.translations.enncard * Z.mass / ENNReal.ofReal (20 * delta)) /
        (M * ENNReal.ofReal (Real.rpow delta (-pyzLoss)))) ^ 3) /
      amplification.translations.enncard := by
    have h1 : volume U ≤ amplification.translations.enncard * volume (twistedUnion Z f) := by
      calc
        volume U ≤ amplification.translations.enncard * volume (cinematicShear c0 '' twistedUnion Z f) := hdiv
        _ = amplification.translations.enncard * volume (twistedUnion Z f) := by rw [hvol_eq2]
    have hN_pos : (0 : ENNReal) < amplification.translations.enncard := by
      have h : 0 < amplification.translations.card := amplification.translations_nonempty.card_pos
      have h' : (0 : ENNReal) < ↑(amplification.translations.card) := by exact_mod_cast h
      simpa [DiscreteSet.enncard] using h'
    have hN_ne_top : amplification.translations.enncard ≠ ⊤ := by
      have h_eq : amplification.translations.enncard = (amplification.translations.card : ENNReal) := by rfl
      rw [h_eq]
      simp
    have h1' : volume U ≤ volume (twistedUnion Z f) * amplification.translations.enncard := by
      rw [mul_comm] at h1
      exact h1
    calc
      volume (twistedUnion Z f)
        ≥ volume U / amplification.translations.enncard := by
          exact (ENNReal.div_le_iff (ne_of_gt hN_pos) hN_ne_top).mpr h1'
      _ ≥ (((amplification.translations.enncard * Z.mass / ENNReal.ofReal (20 * delta)) /
            (M * ENNReal.ofReal (Real.rpow delta (-pyzLoss)))) ^ 3) /
          amplification.translations.enncard := by
          gcongr

  -- Mass lower bound
  have hmass_lower1 : (1 / 2 : ENNReal) * (parameterLocalRepresentativeShading representatives).mass ≤ Z.mass := hZ_mass
  have hmass_lower2 : (1 / 2 : ENNReal) * (perTubeThreshold * localBlock.sourcePoints.enncard) ≤ Z.mass := by
    have h : perTubeThreshold * localBlock.sourcePoints.enncard ≤ (parameterLocalRepresentativeShading representatives).mass :=
      parameterLocalRepresentativeShading_mass_lower representatives hMass
    calc
      (1 / 2 : ENNReal) * (perTubeThreshold * localBlock.sourcePoints.enncard)
        ≤ (1 / 2 : ENNReal) * (parameterLocalRepresentativeShading representatives).mass := by gcongr
      _ ≤ Z.mass := hmass_lower1

  exact ⟨{
    shading := Z
    subshading := hZ_sub
    half_representative_mass := hZ_mass
    mass_lower := hmass_lower2
    volume_lower := hfinal
  }⟩

end Kakeya.Assouad
