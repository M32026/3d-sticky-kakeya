import MyLeanRepo.Kakeya.Cinematic.Section5.NormalCoarseCountFromPairsInputs
import MyLeanRepo.Kakeya.Cinematic.BipartiteTangencyReduction.SubfamilyTransfer

/-!
# Normal coarse count from explicit separated cluster pairs

Pigeonhole explicit rectangle-wise cluster pairs to one shared pair and apply
the robust bipartite tangency theorem in the normalized regime.
-/

namespace Kakeya.Cinematic

theorem normal_coarse_rectangle_count_from_pairs :
    NormalCoarseRectangleCountFromPairsStatement := by
  intro hSharedPair hRobust K hK
  obtain ⟨C, hC, hRobustC⟩ := hRobust K hK
  refine ⟨C, hC, ?_⟩
  intro family hCurvature I hI delta t r tangency A hdelta ht hdelta_t ht_one
    hr htangency hA hscale hdelta_At H hH_family hH_diameter R hR_centers
    hR_central hR_incomparable hR_nonempty centers hcenters q hq hFiberPairs
  obtain ⟨c, hc, d, hd, _hcd, hseparated, S, hR_card, hcounts⟩ :=
    hSharedPair H R hR_nonempty centers q hFiberPairs
  have hcluster_c_family : (H.cluster c r).carrier ⊆ family := by
    intro f hf
    exact hH_family hf.1
  have hcluster_d_family : (H.cluster d r).carrier ⊆ family := by
    intro f hf
    exact hH_family hf.1
  have hcluster_diameter :
      ∀ ⦃f⦄,
        f ∈ (H.cluster c r).carrier ∨ f ∈ (H.cluster d r).carrier →
        ∀ ⦃g⦄,
          g ∈ (H.cluster c r).carrier ∨ g ∈ (H.cluster d r).carrier →
          dist f g ≤ 6 * t := by
    intro f hf g hg
    apply hH_diameter f
    · exact hf.elim And.left And.left
    · exact hg.elim And.left And.left
  have hS_centers : S.family.CentersIn family :=
    S.centersIn_transfer hR_centers
  have hS_central : S.family.IsOverCentralQuarterOf I :=
    S.overCentralQuarter_transfer hR_central
  have hS_incomparable :
      S.family.IsPairwiseIncomparable family 100 := by
    intro i j hij
    exact hR_incomparable (S.embedding i) (S.embedding j) fun heq =>
      hij (S.embedding.injective heq)
  have hR_card_real :
      (R.card : ℝ) ≤ (centers.card : ℝ) ^ 2 * (S.card : ℝ) := by
    exact_mod_cast hR_card
  have hcenters_card_pos : 0 < (centers.card : ℝ) := by
    exact_mod_cast hcenters.card_pos
  have hS_nonempty : S.family.Nonempty :=
    S.nonempty_transfer hR_nonempty
      (sq_pos_of_pos hcenters_card_pos) hR_card_real
  have hseparated' :
      (H.cluster c r).AreSeparated (H.cluster d r) (t / A) := by
    rw [hscale]
    exact hseparated
  have hS_bound :
      (S.card : ℝ) ≤
        C * Real.rpow tangency C * Real.rpow A C *
          Real.rpow
              (RectangleFamily.bipartiteNormalizedCount
                (H.cluster c r) (H.cluster d r) q q)
              (3 / 2 : ℝ) *
            Real.log
              (RectangleFamily.bipartiteNormalizedCount
                (H.cluster c r) (H.cluster d r) q q) :=
    hRobustC tangency htangency family hCurvature I hI A delta t hA
      hdelta ht hdelta_t ht_one hdelta_At
      (H.cluster c r) (H.cluster d r)
      hcluster_c_family hcluster_d_family hcluster_diameter
      hseparated' S.family hS_centers hS_central hS_incomparable
      hS_nonempty q q hq hq hcounts
  refine ⟨c, hc, d, hd, hseparated, S, hS_nonempty, hcounts, ?_⟩
  exact hR_card_real.trans
    (mul_le_mul_of_nonneg_left hS_bound
      (sq_nonneg (centers.card : ℝ)))

end Kakeya.Cinematic
