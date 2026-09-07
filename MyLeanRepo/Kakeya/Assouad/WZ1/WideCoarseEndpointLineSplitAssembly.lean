import MyLeanRepo.Kakeya.Assouad.WZ1.WideCoarseEndpointLineSplitStatements

/-!
# Assemble wide coarse endpoint line synthesis from restricted normals
-/

namespace Kakeya.Assouad

theorem wz1_wide_coarse_endpoint_line_split_assembly :
    WZ1WideCoarseEndpointLineSplitAssemblyStatement := by
  intro hTransverse hAxial
  intro epsilon parameters hepsilon hepsilonOne
  rcases hTransverse epsilon parameters hepsilon hepsilonOne with
    ⟨etaTransverse, hetaTransverse, hTransverseAt⟩
  rcases hAxial epsilon parameters hepsilon hepsilonOne with
    ⟨etaAxial, hetaAxial, hAxialAt⟩
  let etaCap := min etaTransverse etaAxial
  have hetaCap : 0 < etaCap := by
    simp [etaCap, hetaTransverse, hetaAxial]
  refine ⟨etaCap, hetaCap, ?_⟩
  intro eta heta hetaSmall
  have hetaTransverseSmall : eta ≤ etaTransverse :=
    hetaSmall.trans (min_le_left _ _)
  have hetaAxialSmall : eta ≤ etaAxial :=
    hetaSmall.trans (min_le_right _ _)
  rcases hTransverseAt eta heta hetaTransverseSmall with
    ⟨deltaTransverse, hdeltaTransverse,
      hdeltaTransverseOne, hTransverseMain⟩
  rcases hAxialAt eta heta hetaAxialSmall with
    ⟨deltaAxial, hdeltaAxial,
      hdeltaAxialOne, hAxialMain⟩
  let delta₀ := min deltaTransverse deltaAxial
  have hdelta₀ : 0 < delta₀ := by
    simp [delta₀, hdeltaTransverse, hdeltaAxial]
  have hdelta₀One : delta₀ ≤ 1 :=
    (min_le_left _ _).trans hdeltaTransverseOne
  refine ⟨delta₀, hdelta₀, hdelta₀One, ?_⟩
  intro delta F G₁ G₂ ambient active H
    hdelta hdeltaSmall data hwidthLarge rawWidth hrawWidth
    hwidthRaw hraw hFrostman hBall hStrip hactive hretention
    rescale
  let input : WZ1WideCoarseEndpointLineInput parameters data :=
    {
      width_large := hwidthLarge
      rawWidth := rawWidth
      rawWidth_pos := hrawWidth
      width_le_raw := hwidthRaw
      raw_nonconcentration := hraw
      ambient_frostman := hFrostman
      ambient_ball := hBall
      ambient_strip := hStrip
      active_subset := hactive
      active_retention := hretention
      rescale := rescale
    }
  have hdeltaTransverseSmall : delta ≤ deltaTransverse :=
    hdeltaSmall.trans (min_le_left _ _)
  have hdeltaAxialSmall : delta ≤ deltaAxial :=
    hdeltaSmall.trans (min_le_right _ _)
  intro normal hnormal level radius hradius hradiusOne
  by_cases hcoefficient :
      1 / 2 ≤
        |inner ℝ normal (wz1Perp2 data.direction)|
  · exact
      hTransverseMain hdelta hdeltaTransverseSmall
        data input normal hnormal hcoefficient
        level radius hradius hradiusOne
  · have hcoefficientSmall :
        |inner ℝ normal (wz1Perp2 data.direction)| < 1 / 2 :=
      lt_of_not_ge hcoefficient
    exact
      hAxialMain hdelta hdeltaAxialSmall
        data input normal hnormal hcoefficientSmall
        level radius hradius hradiusOne

end Kakeya.Assouad
