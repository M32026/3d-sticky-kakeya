import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ParameterSpacingIntervalCertificateStatement

/-!
Paper Lemma 7.10: convert the selected exact-branching suffix into the
normalized target-dimensional Frostman certificate.
-/

namespace Kakeya.Assouad

theorem parameter_spacing_interval_certificate :
    ParameterSpacingIntervalCertificateStatement := by
  intro epsilon hepsilon hepsilon_small
    base hbase _hlocal_loss
  rcases
      exists_parameterSpacing_selectedCell_target_frostman
        base hbase epsilon hepsilon hepsilon_small with
    ⟨deltaFrostman, hdeltaFrostman,
      hdeltaFrostmanOne, hFrostman⟩
  rcases
      exists_parameterSpacing_extraction_absorption
        epsilon hepsilon with
    ⟨deltaAbsorption, hdeltaAbsorption,
      hdeltaAbsorptionOne, hAbsorption⟩
  let delta₀ :=
    min (min deltaFrostman deltaAbsorption) (1 / 2)
  have hdelta₀ : 0 < delta₀ := by
    dsimp only [delta₀]
    positivity
  have hdelta₀_one : delta₀ < 1 := by
    exact (min_le_right _ _).trans_lt (by norm_num)
  refine ⟨delta₀, hdelta₀, hdelta₀_one, ?_⟩
  intro delta hdelta hdelta_le
    F Y C lambda clustered profile hprofile_base
    selectedCell
  have hdelta_frostman : delta ≤ deltaFrostman :=
    hdelta_le.trans
      ((min_le_left _ _).trans (min_le_left _ _))
  have hdelta_absorption : delta ≤ deltaAbsorption :=
    hdelta_le.trans
      ((min_le_left _ _).trans (min_le_right _ _))
  let fineScale :=
    normalizedParameterBlockFineScale
      delta selectedCell.blockScale
  let normalized :=
    normalizedParameterBlock
      selectedCell.points selectedCell.center
        selectedCell.blockScale
  have hFrost :
      normalized.IsFrostman
        fineScale (1 - epsilon ^ 2)
        (Kakeya.realRpowENN
          fineScale (-12 * epsilon ^ 2)) :=
    hFrostman delta hdelta hdelta_frostman
      F Y C lambda clustered profile hprofile_base
      selectedCell
  have hblock : 0 < selectedCell.blockScale :=
    selectedCell.blockScale_pos
  have hfine_pos : 0 < fineScale := by
    dsimp only [fineScale,
      normalizedParameterBlockFineScale]
    positivity
  have hfine_one : fineScale ≤ 1 := by
    dsimp only [fineScale,
      normalizedParameterBlockFineScale]
    apply (div_le_one hblock).2
    linarith [selectedCell.ten_delta_lt]
  have hCard :
      Kakeya.realRpowENN
          fineScale (-(1 - epsilon ^ 2)) ≤
        Kakeya.realRpowENN fineScale
            (-12 * epsilon ^ 2) *
          normalized.enncard :=
    hFrost.weighted_cardinality
      (by
        dsimp only [normalized,
          normalizedParameterBlock]
        exact selectedCell.points_nonempty.image _)
      hfine_pos hfine_one
  exact ⟨hFrost, hCard,
    hAbsorption delta hdelta hdelta_absorption
      F Y C lambda clustered profile selectedCell⟩

end Kakeya.Assouad
