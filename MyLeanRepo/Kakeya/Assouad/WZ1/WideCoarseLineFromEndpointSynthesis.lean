import MyLeanRepo.Kakeya.Assouad.WZ1.WideCoarseEndpointLineStatements

/-!
# Assemble both wide endpoint line estimates
-/

namespace Kakeya.Assouad

theorem wz1_wide_coarse_line_from_endpoint_synthesis :
    WZ1WideCoarseLineFromEndpointSynthesisStatement := by
  intro hEndpoint epsilon parameters hepsilon hepsilonOne
  rcases
      hEndpoint epsilon parameters hepsilon hepsilonOne with
    ⟨etaCap, hetaCap, hEndpointAtEta⟩
  refine ⟨etaCap, hetaCap, ?_⟩
  intro eta heta hetaBound
  rcases hEndpointAtEta eta heta hetaBound with
    ⟨delta₀, hdelta₀, hdelta₀One, hEndpointAt⟩
  refine ⟨delta₀, hdelta₀, hdelta₀One, ?_⟩
  intro delta F G₁ G₂ H hdelta hdeltaBound
    data hwide sequential
  have hfirstActive :
      wz1ActiveTripleProjection data.refinedH 1 ⊆
        data.selectedG₁ :=
    active_triple_projection_subset data.uniform 1
  have hsecondActive :
      wz1ActiveTripleProjection sequential.firstGraph 2 ⊆
        data.selectedG₂ :=
    active_triple_projection_subset
      sequential.firstUniform 2
  have hfirstRetention :
      (((1 / 256 : ENNReal) *
          Kakeya.realRpowENN delta eta) / 16) *
          data.selectedG₁.enncard ≤
        (wz1ActiveTripleProjection
          data.refinedH 1).enncard := by
    have hraw :=
      active_triple_projection_card_lower data.uniform 1
    change
      ((1 / 256 : ENNReal) *
          Kakeya.realRpowENN delta eta) *
          data.selectedG₁.enncard ≤
        (wz1ActiveTripleProjection
          data.refinedH 1).enncard at hraw
    calc
      (((1 / 256 : ENNReal) *
            Kakeya.realRpowENN delta eta) / 16) *
            data.selectedG₁.enncard
          ≤
        ((1 / 256 : ENNReal) *
            Kakeya.realRpowENN delta eta) *
            data.selectedG₁.enncard := by
          apply mul_le_mul_right'
          rw [div_eq_mul_inv]
          calc
            ((1 / 256 : ENNReal) *
                  Kakeya.realRpowENN delta eta) *
                (16 : ENNReal)⁻¹
                ≤
              ((1 / 256 : ENNReal) *
                  Kakeya.realRpowENN delta eta) * 1 := by
                    gcongr
                    exact ENNReal.inv_le_one.mpr (by norm_num)
            _ =
              (1 / 256 : ENNReal) *
                Kakeya.realRpowENN delta eta := by simp
      _ ≤
        (wz1ActiveTripleProjection
          data.refinedH 1).enncard := hraw
  have hsecondRetention :
      (((1 / 256 : ENNReal) *
          Kakeya.realRpowENN delta eta) / 16) *
          data.selectedG₂.enncard ≤
        (wz1ActiveTripleProjection
          sequential.firstGraph 2).enncard := by
    have hraw :=
      active_triple_projection_card_lower
        sequential.firstUniform 2
    change
      ((((1 / 256 : ENNReal) *
          Kakeya.realRpowENN delta eta) / 16) *
          data.selectedG₂.enncard) ≤
        (wz1ActiveTripleProjection
          sequential.firstGraph 2).enncard at hraw
    exact hraw
  have hfirst :=
    hEndpointAt hdelta hdeltaBound data hwide
      data.firstRawWidth data.firstRawWidth_pos
      data.width_le_first_raw
      data.first_raw_nonconcentration
      data.selectedG₁_frostman data.selectedG₁_ball
      data.first_strip
      hfirstActive hfirstRetention sequential.firstRescale
  have hsecond :=
    hEndpointAt hdelta hdeltaBound data hwide
      data.secondRawWidth data.secondRawWidth_pos
      data.width_le_second_raw
      data.second_raw_nonconcentration
      data.selectedG₂_frostman data.selectedG₂_ball
      data.second_strip
      hsecondActive hsecondRetention sequential.secondRescale
  exact ⟨hfirst, hsecond⟩

end Kakeya.Assouad
