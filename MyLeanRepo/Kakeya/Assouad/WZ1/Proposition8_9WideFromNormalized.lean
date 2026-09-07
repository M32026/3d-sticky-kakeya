import MyLeanRepo.Kakeya.Assouad.WZ1.Theorem5_2LeafStatements

namespace Kakeya.Assouad

theorem wz1_proposition8_9_wide_from_normalized :
    WZ1Proposition8_9WideFromNormalizedStatement := by
  intro hprepare hHypergraph hAnisotropic epsilon parameters
    hepsilon hepsilonOne
  rcases hprepare hHypergraph hAnisotropic epsilon parameters
      hepsilon hepsilonOne with
    ⟨etaCap, hetaCap, htail⟩
  refine ⟨etaCap, hetaCap, ?_⟩
  intro eta heta hetaCapBound
  rcases htail eta heta hetaCapBound with
    ⟨delta₀, hdelta₀, hdelta₀One, hwide⟩
  refine ⟨delta₀, hdelta₀, hdelta₀One, ?_⟩
  intro delta F G₁ G₂ H hdelta hdeltaSmall data hwidth
  rcases hwide hdelta hdeltaSmall data hwidth with ⟨normalized⟩
  apply normalized.transport
  exact parameters.projection normalized.scale normalized.scale_pos
    normalized.scale_le_projectionDelta₀
    normalized.normalizedF normalized.normalizedG₁ normalized.normalizedG₂
    normalized.normalizedF_nonempty normalized.normalizedG₁_nonempty
    normalized.normalizedG₂_nonempty normalized.normalizedF_ball
    normalized.normalizedG₁_ball normalized.normalizedG₂_ball
    normalized.normalizedF_separated normalized.normalizedG₁_separated
    normalized.normalizedG₂_separated normalized.normalizedF_frostman
    normalized.normalizedG₁_frostman normalized.normalizedG₂_frostman
    normalized.standardSeparation normalized.first_line_nonconcentration
    normalized.second_line_nonconcentration normalized.normalizedH
    normalized.uniform

end Kakeya.Assouad
