import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma8_13ActualRepresentativeStatements
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma8_13ActualRepresentativeHelpers
import MyLeanRepo.Kakeya.Assouad.WZ1.InducedTripleRefinement
import MyLeanRepo.Kakeya.Assouad.WZ1.WellSeparatedRestriction

/-!
PDF Lemma 8.13, Step 2: replace balanced coarse `F` cells by separated actual
affine representatives and refine the literal graph on those points.
-/

namespace Kakeya.Assouad

theorem wz1_lemma8_13_actual_representative_selection :
    WZ1Lemma8_13ActualRepresentativeSelectionStatement := by
  intro F G₁ G₂ fineScale coarseScale sourceConstant hcoarseScale hcoarseScaleOne
    hsourceConstant hFball coarsening density hdensity H hUniform hselectedActive hRefine
  classical
  let Cset := coarsening.coarse
  let logLoss := coarsening.logarithmicLoss

  let h_result :=
    heavy_separated_color_class
      hcoarseScale coarsening.coarse_nonempty coarsening.coarse_separated
  let retainedCenters : DiscreteSet 2 := h_result.choose
  have h_result_spec :
      retainedCenters ⊆ Cset ∧
        retainedCenters.Nonempty ∧
        Cset.enncard ≤ 81 * retainedCenters.enncard ∧
        retainedCenters.IsDeltaSeparated (4 * coarseScale) :=
    h_result.choose_spec
  have hretained_subset : retainedCenters ⊆ Cset :=
    h_result_spec.1
  have hretained_nonempty : retainedCenters.Nonempty :=
    h_result_spec.2.1
  have hretention_enn :
      Cset.enncard ≤ 81 * retainedCenters.enncard :=
    h_result_spec.2.2.1
  have hretained_4sep :
      retainedCenters.IsDeltaSeparated (4 * coarseScale) :=
    h_result_spec.2.2.2

  have hlogLoss_nonneg : 0 ≤ logLoss :=
    coarsening.logarithmicLoss_pos.le
  have hlogLoss_ge_one : 1 ≤ logLoss := by
    have h_sel_card_pos : 0 < coarsening.selected.card :=
      Finset.card_pos.mpr coarsening.selected_nonempty
    have h_ret_enn :
        F.enncard ≤
          ENNReal.ofReal logLoss * coarsening.selected.enncard :=
      coarsening.retention
    have h3 :
        ENNReal.ofReal logLoss * coarsening.selected.enncard =
          ENNReal.ofReal
            (logLoss * (coarsening.selected.card : ℝ)) := by
      simp only [DiscreteSet.enncard]
      have h4 :
          (coarsening.selected.card : ENNReal) =
            ENNReal.ofReal (coarsening.selected.card : ℝ) := by
        norm_cast
      rw [h4, ← ENNReal.ofReal_mul hlogLoss_nonneg] <;> ring
    have h5 :
        (F.card : ENNReal) ≤
          ENNReal.ofReal
            (logLoss * (coarsening.selected.card : ℝ)) := by
      have h51 : F.enncard = (F.card : ENNReal) := by
        simp [DiscreteSet.enncard]
      rw [h51] at h_ret_enn
      rw [h3] at h_ret_enn
      exact h_ret_enn
    have h5' :
        ENNReal.ofReal (F.card : ℝ) ≤
          ENNReal.ofReal
            (logLoss * (coarsening.selected.card : ℝ)) := by
      have h_eq :
          ENNReal.ofReal (F.card : ℝ) = (F.card : ENNReal) := by
        norm_cast
      rw [h_eq]
      exact h5
    have h_ret_real :
        (F.card : ℝ) ≤
          logLoss * (coarsening.selected.card : ℝ) :=
      (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h5'
    have h_sel_le_F :
        (coarsening.selected.card : ℝ) ≤ (F.card : ℝ) := by
      exact_mod_cast
        Finset.card_le_card coarsening.selected_subset
    have h1 :
        (coarsening.selected.card : ℝ) ≤
          logLoss * (coarsening.selected.card : ℝ) :=
      h_sel_le_F.trans h_ret_real
    have h2 : 0 < (coarsening.selected.card : ℝ) := by
      exact_mod_cast h_sel_card_pos
    nlinarith

  let C_coarse : ENNReal :=
    ENNReal.ofReal (100 * logLoss) *
      ENNReal.ofReal sourceConstant
  let f : ENNReal := 1 / 81
  have hf_pos : 0 < f := by
    dsimp only [f]
    exact ENNReal.div_pos (by norm_num) (by norm_num)
  have hf_ne_top : f ≠ ⊤ := by
    dsimp only [f]
    simp
  have h_mul_cancel :
      (1 / 81 : ENNReal) * (81 : ENNReal) = 1 := by
    simp [one_div]
    <;> exact
      ENNReal.inv_mul_cancel (by norm_num) (by simp)
  have h_ret :
      f * Cset.enncard ≤ retainedCenters.enncard := by
    calc
      (1 / 81 : ENNReal) * Cset.enncard
          ≤ (1 / 81 : ENNReal) *
              (81 * retainedCenters.enncard) := by
            gcongr
      _ =
          ((1 / 81 : ENNReal) * (81 : ENNReal)) *
            retainedCenters.enncard := by ring
      _ = (1 : ENNReal) * retainedCenters.enncard := by
        rw [h_mul_cancel]
      _ = retainedCenters.enncard := by ring
  have hretained_frostman :
      retainedCenters.IsFrostman
        coarseScale 1 (C_coarse / f) :=
    frostman_retained_subset
      coarsening.coarse_frostman hretained_subset
      h_ret hf_pos hf_ne_top
  let C_ret : ENNReal := C_coarse / f
  have hC_ret_eq :
      C_ret =
        ENNReal.ofReal
          (8100 * logLoss * sourceConstant) := by
    have h1 : C_coarse / f = C_coarse * 81 := by
      dsimp only [f]
      simp [div_eq_mul_inv] <;> ring_nf <;> norm_num
    have h_goal :
        C_coarse * 81 =
          ENNReal.ofReal
            (8100 * logLoss * sourceConstant) := by
      simp only [C_coarse]
      have h_comm :
          ENNReal.ofReal (100 * logLoss) *
                ENNReal.ofReal sourceConstant *
                (81 : ENNReal) =
            (81 : ENNReal) *
                ENNReal.ofReal (100 * logLoss) *
                ENNReal.ofReal sourceConstant := by
        ring
      rw [h_comm]
      have h_mult81 :
          (81 : ENNReal) *
              ENNReal.ofReal (100 * logLoss) =
            ENNReal.ofReal (8100 * logLoss) := by
        rw [show (81 : ENNReal) = ENNReal.ofReal 81 by
          norm_num]
        rw [← ENNReal.ofReal_mul (by norm_num)] <;>
          ring_nf
      rw [h_mult81]
      rw [← ENNReal.ofReal_mul (by positivity)] <;> ring
    dsimp only [C_ret]
    rw [h1]
    exact h_goal

  let rep_of_center : Point2 → Point2 :=
    fun q =>
      if hq : q ∈ retainedCenters then
        Classical.choose
          (coarsening.assignment_surjective q
            (hretained_subset hq))
      else q
  have hrep_of_center_mem :
      ∀ q ∈ retainedCenters,
        rep_of_center q ∈ coarsening.selected := by
    intro q hq
    simp only [rep_of_center, dif_pos hq]
    exact
      (Classical.choose_spec
        (coarsening.assignment_surjective q
          (hretained_subset hq))).1
  have hrep_of_center_assignment :
      ∀ q ∈ retainedCenters,
        coarsening.assignment (rep_of_center q) = q := by
    intro q hq
    simp only [rep_of_center, dif_pos hq]
    exact
      (Classical.choose_spec
        (coarsening.assignment_surjective q
          (hretained_subset hq))).2
  let normalizedF : DiscreteSet 2 :=
    retainedCenters.image rep_of_center

  have hnormalizedF_subset :
      normalizedF ⊆ coarsening.selected := by
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨q, hq, rfl⟩
    exact hrep_of_center_mem q hq

  have hnormalizedF_nonempty : normalizedF.Nonempty := by
    rcases hretained_nonempty with ⟨q, hq⟩
    exact
      ⟨rep_of_center q,
        Finset.mem_image.mpr ⟨q, hq, rfl⟩⟩

  have hnormalizedF_ball : normalizedF.IsInUnitBall := by
    intro y hy
    have h_y_in_F :
        y ∈ F :=
      coarsening.selected_subset (hnormalizedF_subset hy)
    exact hFball y h_y_in_F

  have hinj :
      Set.InjOn rep_of_center
        (retainedCenters : Set Point2) := by
    intro q1 hq1 q2 hq2 h
    have h1 :
        coarsening.assignment (rep_of_center q1) = q1 :=
      hrep_of_center_assignment q1 hq1
    have h2 :
        coarsening.assignment (rep_of_center q2) = q2 :=
      hrep_of_center_assignment q2 hq2
    rw [h] at h1
    exact h1.symm.trans h2

  have hnormalizedF_enncard :
      normalizedF.enncard = retainedCenters.enncard := by
    have h :
        normalizedF.card = retainedCenters.card :=
      Finset.card_image_of_injOn hinj
    simpa [DiscreteSet.enncard] using
      congr_arg (fun x : ℕ => (x : ENNReal)) h

  have hseparation :
      normalizedF.IsDeltaSeparated coarseScale := by
    intro y1 hy1 y2 hy2 hne
    rcases Finset.mem_image.mp hy1 with
      ⟨q1, hq1, rfl⟩
    rcases Finset.mem_image.mp hy2 with
      ⟨q2, hq2, rfl⟩
    have hq12 : q1 ≠ q2 := by
      intro h
      apply hne
      simp [h]
    have hdist4 :
        4 * coarseScale ≤ dist q1 q2 :=
      hretained_4sep hq1 hq2 hq12
    have h_close1 :
        dist (rep_of_center q1) q1 ≤ coarseScale := by
      have h1 :
          dist
              (rep_of_center q1)
              (coarsening.assignment (rep_of_center q1)) ≤
            coarseScale :=
        coarsening.assignment_close
          (rep_of_center q1) (hrep_of_center_mem q1 hq1)
      have h2 :
          coarsening.assignment (rep_of_center q1) = q1 :=
        hrep_of_center_assignment q1 hq1
      rw [h2] at h1
      exact h1
    have h_close2 :
        dist (rep_of_center q2) q2 ≤ coarseScale := by
      have h1 :
          dist
              (rep_of_center q2)
              (coarsening.assignment (rep_of_center q2)) ≤
            coarseScale :=
        coarsening.assignment_close
          (rep_of_center q2) (hrep_of_center_mem q2 hq2)
      have h2 :
          coarsening.assignment (rep_of_center q2) = q2 :=
        hrep_of_center_assignment q2 hq2
      rw [h2] at h1
      exact h1
    have h4 :
        dist q1 q2 ≤
          dist q1 (rep_of_center q1) +
            dist (rep_of_center q1) (rep_of_center q2) +
            dist (rep_of_center q2) q2 := by
      calc
        dist q1 q2
            ≤ dist q1 (rep_of_center q1) +
                dist (rep_of_center q1) q2 :=
          dist_triangle _ _ _
        _ ≤ dist q1 (rep_of_center q1) +
              (dist (rep_of_center q1) (rep_of_center q2) +
                dist (rep_of_center q2) q2) := by
            gcongr
            exact dist_triangle _ _ _
        _ = _ := by ring
    linarith [dist_comm q1 (rep_of_center q1)]

  have hC_ret_one : (1 : ENNReal) ≤ C_ret := by
    rw [hC_ret_eq]
    have h :
        (1 : ℝ) ≤
          8100 * logLoss * sourceConstant := by
      have h1 : 1 ≤ logLoss := hlogLoss_ge_one
      have h2 : 1 ≤ sourceConstant := hsourceConstant
      nlinarith
    simpa [ENNReal.ofReal_one] using
      ENNReal.ofReal_le_ofReal h
  have hC_ret_ne_top : (2 : ENNReal) * C_ret ≠ ⊤ := by
    rw [hC_ret_eq]
    exact
      ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top
  have h_close :
      ∀ q ∈ retainedCenters,
        dist q (rep_of_center q) ≤ coarseScale := by
    intro q hq
    have h1 :
        dist
            (rep_of_center q)
            (coarsening.assignment (rep_of_center q)) ≤
          coarseScale :=
      coarsening.assignment_close
        (rep_of_center q) (hrep_of_center_mem q hq)
    have h2 :
        coarsening.assignment (rep_of_center q) = q :=
      hrep_of_center_assignment q hq
    rw [h2] at h1
    have h3 :
        dist q (rep_of_center q) =
          dist (rep_of_center q) q :=
      dist_comm _ _
    rw [h3]
    exact h1
  let C_final : ENNReal := 2 * C_ret
  have hnormalizedF_frostman :
      normalizedF.IsFrostman coarseScale 1 C_final :=
    frostman_transfer_near_bijection
      hretained_frostman rep_of_center hinj rfl h_close
      hcoarseScale hcoarseScaleOne hC_ret_one hC_ret_ne_top

  have hactive :
      ∀ vertex ∈ normalizedF,
        ∃ edge ∈ H, edge.1 = vertex := by
    intro vertex hvertex
    have h_in :
        vertex ∈ coarsening.selected :=
      hnormalizedF_subset hvertex
    exact hselectedActive vertex h_in
  rcases
      restrict_zeroth_vertex_and_refine hUniform
        (hnormalizedF_subset.trans
          coarsening.selected_subset)
        hactive hnormalizedF_nonempty hRefine
    with
      ⟨normalizedH, hnormalizedH_subset, _,
        hnormalizedUniform⟩

  let constant : ℝ :=
    16200 * logLoss * sourceConstant
  have hconstant_eq :
      C_final = ENNReal.ofReal constant := by
    simp only [C_final, constant]
    rw [hC_ret_eq]
    have h :
        (2 : ENNReal) *
            ENNReal.ofReal
              (8100 * logLoss * sourceConstant) =
          ENNReal.ofReal
            (16200 * logLoss * sourceConstant) := by
      rw [show (2 : ENNReal) = ENNReal.ofReal 2 by
        norm_num]
      rw [← ENNReal.ofReal_mul (by positivity)] <;> ring
    exact h
  have hconstant_nonneg : 0 ≤ constant := by
    have h1 : 0 ≤ logLoss := hlogLoss_nonneg
    have h2 : 0 ≤ sourceConstant := by linarith
    positivity
  exact
    ⟨normalizedF, hnormalizedF_subset,
      hnormalizedF_nonempty, hnormalizedF_ball,
      hseparation, constant, rfl, hconstant_nonneg,
      (hconstant_eq ▸ hnormalizedF_frostman),
      normalizedH, hnormalizedH_subset,
      hnormalizedUniform⟩

end Kakeya.Assouad
