import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma44BadPairStatements
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma44SelectedLines
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma44TripleAssembly
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma44Arithmetic

/-!
WZ1 Lemma 44: use the three-case estimates and heavy-line packing to bound
the exceptional pairs at one fixed scale.

Proof route:
1. Apply `construct_selected_lines` to obtain, for each `b1 ∈ G₁`, a maximal
   scale-separated collection of heavy lines through `b1`, with coverage of
   every bad-pair witness at enlarged width `13·scale` and a uniform
   cardinality bound `M`.
2. Apply `triple_count_assembly` to combine the selected-line coverage with
   the three-case geometric bounds and Cauchy–Schwarz, producing the final
   `sqrt 312002 * delta^(2*alpha)` pair fraction.
-/

namespace Kakeya.Assouad

theorem wz1_lemma44_single_scale_bad_pair :
    WZ1Lemma44SingleScaleBadPairStatement := by
  intro h_packing
  intro delta lambda zeta alpha hdelta hdelta1 hlambda hzeta halpha
  intro G₁ G₂ hG1ne hG2ne hG1ball hG2ball hG1sep hG2sep hFrost1 hFrost2
  intro hMutSep hNonConc
  intro K scale hK hscale_pos hdelta_scale hscale1 hK_small h13scale hprem2 hprem3

  rcases construct_selected_lines h_packing delta lambda zeta alpha
      hdelta hdelta1 hlambda hzeta halpha
      G₁ G₂ hG1ne hG2ne hG1ball hG2ball hG1sep hG2sep hFrost1 hFrost2
      hMutSep hNonConc
      K scale hK hscale_pos hdelta_scale hscale1 hK_small h13scale
    with ⟨badLines, M, hM_card, hM_through, hM_fin, h_coverage, hM_bound⟩

  have hD_bounds : delta ≤ Real.rpow delta (lambda + 4 * alpha) ∧
      Real.rpow delta (lambda + 4 * alpha) ≤ 1 :=
    D_bounds hdelta hdelta1 hlambda hzeta halpha hscale_pos hdelta_scale hprem2
  have hs_bounds : delta ≤ Real.rpow delta (lambda + 4 * alpha / zeta) ∧
      Real.rpow delta (lambda + 4 * alpha / zeta) ≤ 1 :=
    s_bounds hdelta hdelta1 hlambda hzeta halpha hscale_pos hdelta_scale hprem2

  exact triple_count_assembly delta lambda zeta alpha
      hdelta hdelta1 hlambda hzeta halpha
      G₁ G₂ hG1ne hG2ne hG1ball hG2ball hFrost1 hFrost2 hNonConc
      K scale hK hscale_pos hdelta_scale hscale1 h13scale
      hD_bounds.1 hs_bounds.1 hprem2 hprem3
      badLines M hM_card hM_through hM_fin h_coverage hM_bound

end Kakeya.Assouad
