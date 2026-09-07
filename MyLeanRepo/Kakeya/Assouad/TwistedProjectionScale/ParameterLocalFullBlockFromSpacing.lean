import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ParameterLocalFullBlockFromSpacingStatements

/-!
# Full local block from spacing and content pruning

Compose the spacing candidate and finite-content pruning into the downstream
full local-block selection API.
-/

namespace Kakeya.Assouad

theorem parameter_local_full_block_from_spacing :
    ParameterLocalFullBlockFromSpacingStatement := by
  intro h_spacing h_pruning h_crossing epsilon h_eps_pos h_eps_lt
  rcases h_spacing h_crossing epsilon h_eps_pos h_eps_lt with
    ⟨etaMax, delta₀_s, h_etaMax_pos, h_etaMax_le, h_ds_pos, h_ds_lt1, h_main_s⟩
  rcases h_pruning epsilon h_eps_pos h_eps_lt with
    ⟨delta₀_p, h_dp_pos, h_dp_lt1, h_main_p⟩
  let delta₀ := min delta₀_s delta₀_p
  have h_d0_pos : 0 < delta₀ := lt_min h_ds_pos h_dp_pos
  have h_d0_lt1 : delta₀ < 1 := by
    exact lt_of_le_of_lt (min_le_left _ _) h_ds_lt1
  refine' ⟨etaMax, delta₀, h_etaMax_pos, h_etaMax_le, h_d0_pos, h_d0_lt1, _⟩
  intro eta h_eta_pos h_eta_le delta h_delta_pos h_delta_le
    F Y C lambda clustered c0 hwindow hcard
  have h_delta_le_s : delta ≤ delta₀_s :=
    le_trans h_delta_le (min_le_left _ _)
  have h_delta_le_p : delta ≤ delta₀_p :=
    le_trans h_delta_le (min_le_right _ _)
  have h_candidate : Nonempty (ParameterLocalSpacingCandidateData (epsilon := epsilon) clustered) :=
    h_main_s eta h_eta_pos h_eta_le delta h_delta_pos h_delta_le_s
      F Y C lambda clustered hcard
  rcases h_candidate with ⟨candidate⟩
  have h_delta_le_block : delta ≤ candidate.blockScale := by
    have h1 : 10 * delta < candidate.blockScale := candidate.ten_delta_lt
    have h2 : delta < candidate.blockScale / 10 := by linarith
    have h3 : candidate.blockScale / 10 < candidate.blockScale := by
      linarith [candidate.blockScale_pos]
    linarith
  have h_pruning_result :
      Nonempty (ParameterLocalFrostmanBlockPruningData
        (clustered := clustered)
        (epsilon := epsilon)
        candidate.points candidate.blockCenter candidate.blockScale) :=
    h_main_p delta h_delta_pos h_delta_le_p F Y C lambda clustered
      candidate.blockScale candidate.blockScale_pos h_delta_le_block
      candidate.ten_delta_lt candidate.blockScale_small candidate.separated_scale
      candidate.blockCenter candidate.points candidate.points_nonempty
      candidate.points_subset candidate.points_containment c0 hwindow
      candidate.normalized_frostman
      candidate.normalized_cardinality
      candidate.normalized_extraction_absorption
  rcases h_pruning_result with ⟨pruning_data⟩
  exact ⟨pruning_data.block⟩

end Kakeya.Assouad
