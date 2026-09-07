import MyLeanRepo.Kakeya.Cinematic.Section5.AmbientRestrictedParentTangencyScaleInputs

/-!
# Tangency scale for the selected parent multiplicity
-/

noncomputable section

namespace Kakeya.Cinematic

local instance ambientRestrictedParentTangencyScaleProofDecidableEq :
    DecidableEq C2Function := Classical.decEq _

theorem ambient_restricted_parent_tangency_scale :
    AmbientRestrictedParentTangencyScaleStatement := by
  intro family E K delta diameter epsilon eta tRep DeltaRep C_R₀
    data center hE C_R C_count C_shading C_volume
    fineSetup coarseSetup massExponent refinement
    degreeSetup q_fiber fiberBound heavySetup parentSetup
    retention fiberCoefficient incidenceScale
    hq hfiberBound hretention hfiberCoefficient
    hincidenceScale hfiberScale hqRetention hpairs
  let subfamily :=
    selectedCoarseSubfamily
      coarseSetup.coarseData heavySetup.selectedCoarse
  have hcard :
      subfamily.card = heavySetup.selectedCoarse.card :=
    selectedCoarseSubfamily_card _ _
  have hcard_pos : 0 < subfamily.card := by
    rw [hcard]
    exact heavySetup.selectedCoarse_nonempty.card_pos
  let index : Fin subfamily.card := ⟨0, hcard_pos⟩
  let coarse := subfamily.embedding index
  have hcoarse_sel : coarse ∈ heavySetup.selectedCoarse :=
    selectedCoarseSubfamily_parent_mem _ _ _
  have hcoarse_heavy : coarse ∈ heavySetup.heavy :=
    heavySetup.selectedCoarse_subset hcoarse_sel
  let parentEdges :=
    (incidenceParentEdges degreeSetup.selectedEdges
      coarseSetup.coarseData.parent coarse).card
  let support :=
    (selectedCoarseIncidenceSupport
      coarseSetup.coarseData degreeSetup.selectedEdges
        heavySetup.selectedCoarse index).card
  let pairLower := parentSetup.pairLower index
  let selectedRectangles :=
    (parentSetup.selectedRectangles index).card
  have hdegpos : 0 < heavySetup.degreeLoss := by
    rw [heavySetup.degreeLoss_eq]
    positivity
  have hdegpos' : (0 : ℝ) < (heavySetup.degreeLoss : ℝ) := by
    exact_mod_cast hdegpos
  have hlogpos : 0 < heavySetup.heavyLogLoss := by
    rw [heavySetup.heavyLogLoss_eq]
    positivity
  have hthresh :
      heavySetup.heavyThreshold ≤ (parentEdges : ℝ) := by
    rw [heavySetup.heavy_eq] at hcoarse_heavy
    have h :
        coarse ∈ heavySetup.active ∧
          heavySetup.heavyThreshold ≤ (parentEdges : ℝ) := by
      simpa [Finset.mem_filter, parentEdges] using hcoarse_heavy
    exact h.2
  have hparentEdges :
      (heavySetup.M_parent : ℝ) * (q_fiber : ℝ) ≤
        (2 * (heavySetup.degreeLoss : ℝ)) *
          (parentEdges : ℝ) := by
    rw [heavySetup.heavyThreshold_eq,
      heavySetup.rectangleBound_eq,
      heavySetup.heavyLogLoss_eq] at hthresh
    have h :
        (2 * (heavySetup.M_parent : ℝ)) *
              (q_fiber : ℝ) /
              (4 * (heavySetup.degreeLoss : ℝ)) ≤
            (parentEdges : ℝ) :=
      hthresh
    calc
      (heavySetup.M_parent : ℝ) * (q_fiber : ℝ) =
          (2 * (heavySetup.degreeLoss : ℝ)) *
            (((2 * (heavySetup.M_parent : ℝ)) *
              (q_fiber : ℝ) /
              (4 * (heavySetup.degreeLoss : ℝ)))) := by
        field_simp [hdegpos'.ne']
        ring
      _ ≤
          (2 * (heavySetup.degreeLoss : ℝ)) *
            (parentEdges : ℝ) := by
        gcongr
  have hmain :
      (heavySetup.M_parent : ℝ) ≤
        (5184 * incidenceScale * fiberCoefficient *
            (2 * (heavySetup.degreeLoss : ℝ)) *
            heavySetup.heavyLogLoss ^ 2 *
            Real.rpow retention (-3)) *
          Real.rpow (data.mu : ℝ) (-2) *
          Real.rpow (support : ℝ) 2 :=
    selected_parent_tangency_bound_of_fiber_scale
      heavySetup.M_parent q_fiber pairLower data.mu support
      parentEdges selectedRectangles retention
      (2 * (heavySetup.degreeLoss : ℝ))
      heavySetup.heavyLogLoss fiberBound fiberCoefficient
      incidenceScale hq data.mu_pos hretention
      (by positivity) hlogpos hfiberBound hincidenceScale
      hfiberScale hqRetention hparentEdges
      (parentSetup.selected_card_lower index)
      (parentSetup.q_fiber_le_pairLower index)
      (hpairs index)
  have hsupport_lt :
      support < 2 ^ (heavySetup.supportLevel + 1) :=
    (selectedCoarseIncidenceSupport_card_range
      coarseSetup.coarseData degreeSetup.selectedEdges
      heavySetup.selectedCoarse
      heavySetup.support_range index).2
  have hsupport_rpow :
      Real.rpow (support : ℝ) 2 ≤
        Real.rpow
          ((2 ^ (heavySetup.supportLevel + 1) : ℕ) : ℝ) 2 := by
    apply Real.rpow_le_rpow
    · positivity
    · exact_mod_cast hsupport_lt.le
    · norm_num
  let base : ℝ := (2 ^ heavySetup.supportLevel : ℕ)
  have hfactor :
      Real.rpow
          ((2 ^ (heavySetup.supportLevel + 1) : ℕ) : ℝ) 2 =
        4 * Real.rpow base 2 := by
    have hcast :
        ((2 ^ (heavySetup.supportLevel + 1) : ℕ) : ℝ) =
          (2 : ℝ) * base := by
      have h1 :
          (2 ^ (heavySetup.supportLevel + 1) : ℕ) =
            2 * 2 ^ heavySetup.supportLevel := by
        rw [pow_succ]
        ring
      calc
        ((2 ^ (heavySetup.supportLevel + 1) : ℕ) : ℝ) =
            ((2 * 2 ^ heavySetup.supportLevel : ℕ) : ℝ) := by
          rw [h1]
        _ =
            (2 : ℝ) *
              ((2 ^ heavySetup.supportLevel : ℕ) : ℝ) := by
          simp [Nat.cast_mul]
        _ = (2 : ℝ) * base := by rfl
    rw [hcast]
    have h2 :
        Real.rpow ((2 : ℝ) * base) 2 =
          ((2 : ℝ) * base) ^ 2 := by
      convert Real.rpow_natCast
        ((2 : ℝ) * base) (2 : ℕ) <;> norm_num
    have h3 : Real.rpow base 2 = base ^ 2 := by
      convert Real.rpow_natCast base (2 : ℕ) <;> norm_num
    rw [h2, h3]
    ring
  rw [hfactor] at hsupport_rpow
  have hcoeff_nonneg :
      0 ≤
        (5184 * incidenceScale * fiberCoefficient *
            (2 * (heavySetup.degreeLoss : ℝ)) *
            heavySetup.heavyLogLoss ^ 2 *
            Real.rpow retention (-3)) *
          Real.rpow (data.mu : ℝ) (-2) := by
    have h1 : 0 ≤ Real.rpow retention (-3) :=
      Real.rpow_nonneg hretention.le _
    have h2 : 0 ≤ Real.rpow (data.mu : ℝ) (-2) :=
      Real.rpow_nonneg (by exact_mod_cast data.mu_pos.le) _
    positivity
  calc
    ((heavySetup.M_parent : ℕ) : ℝ) ≤
        (5184 * incidenceScale * fiberCoefficient *
            (2 * (heavySetup.degreeLoss : ℝ)) *
            heavySetup.heavyLogLoss ^ 2 *
            Real.rpow retention (-3)) *
          Real.rpow (data.mu : ℝ) (-2) *
          Real.rpow (support : ℝ) 2 :=
      hmain
    _ ≤
        (5184 * incidenceScale * fiberCoefficient *
            (2 * (heavySetup.degreeLoss : ℝ)) *
            heavySetup.heavyLogLoss ^ 2 *
            Real.rpow retention (-3)) *
          Real.rpow (data.mu : ℝ) (-2) *
          (4 * Real.rpow base 2) :=
      mul_le_mul_of_nonneg_left hsupport_rpow hcoeff_nonneg
    _ =
        ambientRestrictedParentTangencyScale
            incidenceScale fiberCoefficient
            heavySetup.degreeLoss heavySetup.heavyLogLoss retention *
          Real.rpow (data.mu : ℝ) (-2) *
          Real.rpow (2 ^ heavySetup.supportLevel : ℕ) 2 := by
      simp [ambientRestrictedParentTangencyScale, base]
      ring

end Kakeya.Cinematic

end section
