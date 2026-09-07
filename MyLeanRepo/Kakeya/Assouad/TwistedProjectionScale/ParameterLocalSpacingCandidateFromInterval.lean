import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ParameterSpacingIntervalCertificateStatement
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ParameterSpacingProfileThreshold

/-!
# Assemble Lemma 7.10 from the interval certificate

All count, scale, retention, and geometry steps are closed.  The only analytic
input is the Shmerkin--Wang interval certificate.
-/

noncomputable section

namespace Kakeya.Assouad

theorem parameter_local_spacing_candidate_from_interval
    (hInterval : ParameterSpacingIntervalCertificateStatement) :
    ParameterLocalSpacingCandidateStatement := by
  intro _hCrossing epsilon hepsilon hepsilon_small
  have hloss_pos : 0 < epsilon ^ 2 / 1000 := by
    positivity
  rcases exists_large_base3
      (epsilon ^ 2 / 1000) hloss_pos with
    ⟨base, hbase, hlocal_loss⟩
  rcases exists_parameterSpacing_profile_threshold
      base hbase epsilon hepsilon hepsilon_small with
    ⟨deltaProfile, hdeltaProfile,
      hdeltaProfileOne, hprofile⟩
  rcases hInterval epsilon hepsilon hepsilon_small
      base hbase hlocal_loss with
    ⟨deltaInterval, hdeltaInterval,
      hdeltaIntervalOne, hinterval⟩
  let etaMax := epsilon ^ 2 / 1000
  let delta₀ :=
    min (min deltaProfile deltaInterval) (1 / 2000)
  have hetaMax : 0 < etaMax := by
    dsimp only [etaMax]
    positivity
  have hetaMax_le :
      etaMax ≤ epsilon ^ 2 / 1000 := le_rfl
  have hdelta₀ : 0 < delta₀ := by
    dsimp only [delta₀]
    positivity
  have hdelta₀_one : delta₀ < 1 := by
    exact (min_le_right _ _).trans_lt (by norm_num)
  refine ⟨etaMax, delta₀, hetaMax, hetaMax_le,
    hdelta₀, hdelta₀_one, ?_⟩
  intro eta heta heta_le delta hdelta hdelta_le
    F Y C lambda clustered hglobal
  have hdelta_profile : delta ≤ deltaProfile :=
    hdelta_le.trans
      ((min_le_left _ _).trans (min_le_left _ _))
  have hdelta_interval : delta ≤ deltaInterval :=
    hdelta_le.trans
      ((min_le_left _ _).trans (min_le_right _ _))
  have hdelta_small : delta < 1 / 1000 :=
    hdelta_le.trans_lt
      ((min_le_right _ _).trans_lt (by norm_num))
  have hdelta_one : delta < 1 :=
    hdelta_small.trans (by norm_num)
  have hthreshold :
      ∀ tree :
          ParameterSpacingUniformTreeData
            clustered epsilon,
        tree.base = base →
        ((cellCount tree.base tree.refinedPoints 0 : ℝ) *
              Real.rpow (tree.base : ℝ)
                ((tree.levels : ℝ) *
                  parameterSpacingAverageThreshold epsilon) ≤
            (tree.refinedPoints.card : ℝ)) ∧
          parameterSpacingStartIndex < tree.levels ∧
          (parameterSpacingStartIndex : ℝ) /
              (tree.levels : ℝ) ≤ epsilon ^ 2 / 100 := by
    intro tree htree
    exact hprofile eta heta
      (by simpa [etaMax] using heta_le)
      delta hdelta hdelta_profile
      F Y C lambda clustered tree htree hglobal
  rcases parameter_spacing_profile_assembly
      (clustered := clustered)
      base hbase hlocal_loss
      hepsilon hepsilon_small
      heta (by simpa [etaMax] using heta_le)
      hdelta hdelta_small
      (fun tree htree =>
        (hthreshold tree htree).1)
      (fun tree htree =>
        (hthreshold tree htree).2.1)
      (fun tree htree =>
        (hthreshold tree htree).2.2)
      hglobal with
    ⟨profile, hprofile_base⟩
  have hseparation :=
    parameterSpacing_selected_scale_separation
      profile hdelta hepsilon hepsilon_small
  rcases parameter_spacing_selected_cell
      profile hepsilon hepsilon_small
      hdelta hdelta_one hseparation with
    ⟨selectedCell⟩
  have hcertificate :=
    hinterval delta hdelta hdelta_interval
      F Y C lambda clustered profile
      hprofile_base selectedCell
  refine ⟨{
    blockScale := selectedCell.blockScale
    blockScale_pos := selectedCell.blockScale_pos
    ten_delta_lt := selectedCell.ten_delta_lt
    blockScale_small := selectedCell.blockScale_small
    separated_scale := selectedCell.separated_scale
    blockCenter := selectedCell.center
    points := selectedCell.points
    points_nonempty := selectedCell.points_nonempty
    points_subset := selectedCell.points_subset
    points_containment := selectedCell.points_containment
    normalized_frostman := hcertificate.1
    normalized_cardinality := hcertificate.2.1
    normalized_extraction_absorption := hcertificate.2.2
  }⟩

end Kakeya.Assouad
