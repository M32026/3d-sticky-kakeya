import MyLeanRepo.Kakeya.Cinematic.Section5.ScaleFreeNormalCoarseCountFromPairsInputs
import MyLeanRepo.Kakeya.Cinematic.Section5.ScaleFreeNormalCoarseRectangleCount
import MyLeanRepo.Kakeya.Cinematic.Section5.NormalCoarseCountFromPairs
import MyLeanRepo.Kakeya.Cinematic.BipartiteTangencyReduction.VerticalScalingRectangles

/-!
# Scale-free normal coarse count from explicit cluster pairs

Transfer the normalized explicit-pair Proposition 26 assembly to arbitrary
positive coarse second scale by vertical scaling.
-/

open Classical

namespace Kakeya.Cinematic

theorem scale_free_normal_coarse_rectangle_count_from_pairs :
    ScaleFreeNormalCoarseRectangleCountFromPairsStatement := by
  intro hShared hRobust hNormal K hK
  rcases hNormal hShared hRobust K hK with ⟨C, hC, hMain⟩
  refine ⟨C, hC, ?_⟩
  intro family hCurv I hI delta t r tangency A hdelta_pos ht_pos hdelta_le_t
    hr_pos htangency hA hEq hdelta_le_A H hH_sub hH_diam R hR_centers
    hR_central hR_incomp hR_nonempty centers hcenters_nonempty q hq_pos hPairs
  by_cases h_t_le_one : t ≤ 1
  · exact hMain hCurv hI hdelta_pos ht_pos hdelta_le_t h_t_le_one hr_pos
      htangency hA hEq hdelta_le_A H hH_sub hH_diam R hR_centers hR_central
      hR_incomp hR_nonempty centers hcenters_nonempty q hq_pos hPairs
  · have h_one_lt_t : 1 < t := by linarith
    set s : ℝ := 1 / t with hs_def
    have hs_pos : 0 < s := by positivity
    have hs_le_one : s ≤ 1 := by
      rw [hs_def]
      exact (div_le_one ht_pos).mpr (by linarith)
    have h_st_eq_one : s * t = 1 := by
      rw [hs_def]
      field_simp [ht_pos.ne']
    let family' : Set C2Function := Set.image (fun f => s • f) family
    let H' : FiniteFunctionFamily := s • H
    let R' : RectangleFamily (s * delta) (s * t) :=
      RectangleFamily.smul s hs_pos R
    have hR'card : R'.card = R.card := RectangleFamily.smul_card hs_pos R
    let eR : Fin R'.card → Fin R.card := Fin.cast hR'card
    let centers' : Finset C2Function := centers.image (fun f => s • f)
    let delta' : ℝ := s * delta
    let t' : ℝ := s * t
    let r' : ℝ := s * r
    have hCurv' : HasCinematicCurvature family' K :=
      hCurv.smul hs_pos hs_le_one
    have hdelta'_pos : 0 < delta' := by positivity
    have ht'_pos : 0 < t' := by positivity
    have hdelta'_le_t' : delta' ≤ t' := by
      dsimp only [delta', t']
      gcongr
    have ht'_le_one : t' ≤ 1 := by
      dsimp only [t']
      rw [h_st_eq_one]
    have hr'_pos : 0 < r' := by positivity
    have hEq' : t' / A = 8 * r' := by
      dsimp only [t', r']
      calc
        (s * t) / A = s * (t / A) := by ring
        _ = s * (8 * r) := by rw [hEq]
        _ = 8 * (s * r) := by ring
    have hdelta'_le_A : delta' ≤ A * t' := by
      dsimp only [delta', t']
      calc
        s * delta ≤ s * (A * t) := by gcongr
        _ = A * (s * t) := by ring
    have hH'_sub : H'.carrier ⊆ family' := by
      intro f' hf'
      rcases (FiniteFunctionFamily.mem_smul_iff hs_pos).mp hf' with ⟨f, hf, rfl⟩
      exact Set.mem_image_of_mem _ (hH_sub hf)
    have hH'_diam :
        ∀ f' ∈ H'.carrier, ∀ g' ∈ H'.carrier, dist f' g' ≤ 6 * t' := by
      intro f' hf' g' hg'
      rcases (FiniteFunctionFamily.mem_smul_iff hs_pos).mp hf' with ⟨f, hf, rfl⟩
      rcases (FiniteFunctionFamily.mem_smul_iff hs_pos).mp hg' with ⟨g, hg, rfl⟩
      have h1 : dist f g ≤ 6 * t := hH_diam f hf g hg
      have h2 : dist (s • f) (s • g) = s * dist f g := by
        simpa [c2Distance_eq_dist] using c2Distance_smul hs_pos.le f g
      rw [h2]
      calc
        s * dist f g ≤ s * (6 * t) := by gcongr
        _ = 6 * (s * t) := by ring
    have hR'_centers : R'.CentersIn family' :=
      RectangleFamily.smul_centersIn_forward hs_pos hR_centers
    have hR'_central : R'.IsOverCentralQuarterOf I :=
      RectangleFamily.smul_overCentralQuarterOf hs_pos hR_central
    have hR'_incomp : R'.IsPairwiseIncomparable family' 100 :=
      RectangleFamily.smul_pairwiseIncomparable_forward hs_pos hR_incomp
    have hR'_nonempty : R'.Nonempty :=
      (RectangleFamily.smul_nonempty hs_pos R).mpr hR_nonempty
    have hcenters'_nonempty : centers'.Nonempty :=
      Finset.Nonempty.image hcenters_nonempty (fun f : C2Function => s • f)
    have hPairs' : ∀ i,
        ∃ c' ∈ centers', ∃ d' ∈ centers',
          10 * r' ≤ c2Distance c' d' ∧
          q ≤ RectangleFamily.tangentCount (R'.rectangle i)
                (H'.cluster c' r') tangency ∧
          q ≤ RectangleFamily.tangentCount (R'.rectangle i)
                (H'.cluster d' r') tangency ∧
          (H'.cluster c' r').AreSeparated (H'.cluster d' r') (8 * r') := by
      intro i
      rcases hPairs (eR i) with
        ⟨c, hc, d, hd, hdist, htangentC, htangentD, hseparated⟩
      have hclusterC : H'.cluster (s • c) r' = s • (H.cluster c r) := by
        dsimp only [H', r']
        exact FiniteFunctionFamily.smul_cluster hs_pos H c r
      have hclusterD : H'.cluster (s • d) r' = s • (H.cluster d r) := by
        dsimp only [H', r']
        exact FiniteFunctionFamily.smul_cluster hs_pos H d r
      refine
        ⟨s • c, Finset.mem_image.mpr ⟨c, hc, rfl⟩,
          s • d, Finset.mem_image.mpr ⟨d, hd, rfl⟩, ?_, ?_, ?_, ?_⟩
      · dsimp only [r']
        rw [c2Distance_smul hs_pos.le]
        calc
          10 * (s * r) = s * (10 * r) := by ring
          _ ≤ s * c2Distance c d := by gcongr
      · rw [hclusterC]
        have h3 :
            RectangleFamily.tangentCount (R'.rectangle i)
                (s • H.cluster c r) tangency =
              RectangleFamily.tangentCount (R.rectangle (eR i))
                (H.cluster c r) tangency :=
          RectangleFamily.smul_tangentCount hs_pos
        rw [h3]
        exact htangentC
      · rw [hclusterD]
        have h4 :
            RectangleFamily.tangentCount (R'.rectangle i)
                (s • H.cluster d r) tangency =
              RectangleFamily.tangentCount (R.rectangle (eR i))
                (H.cluster d r) tangency :=
          RectangleFamily.smul_tangentCount hs_pos
        rw [h4]
        exact htangentD
      · rw [hclusterC, hclusterD]
        dsimp only [r']
        rw [show 8 * (s * r) = s * (8 * r) by ring]
        exact (FiniteFunctionFamily.smul_AreSeparated hs_pos).mpr hseparated
    rcases hMain hCurv' hI hdelta'_pos ht'_pos hdelta'_le_t' ht'_le_one
        hr'_pos htangency hA hEq' hdelta'_le_A H' hH'_sub hH'_diam R'
        hR'_centers hR'_central hR'_incomp hR'_nonempty centers'
        hcenters'_nonempty q hq_pos hPairs' with
      ⟨c', hc', d', hd', hseparated', S', hS'nonempty, hS'tangent, hS'card⟩
    rcases Finset.mem_image.mp hc' with ⟨c, hc, rfl⟩
    rcases Finset.mem_image.mp hd' with ⟨d, hd, rfl⟩
    have hclusterC : H'.cluster (s • c) r' = s • (H.cluster c r) := by
      dsimp only [H', r']
      exact FiniteFunctionFamily.smul_cluster hs_pos H c r
    have hclusterD : H'.cluster (s • d) r' = s • (H.cluster d r) := by
      dsimp only [H', r']
      exact FiniteFunctionFamily.smul_cluster hs_pos H d r
    have hseparated :
        (H.cluster c r).AreSeparated (H.cluster d r) (8 * r) := by
      rw [hclusterC, hclusterD] at hseparated'
      dsimp only [r'] at hseparated'
      rw [show 8 * (s * r) = s * (8 * r) by ring] at hseparated'
      exact (FiniteFunctionFamily.smul_AreSeparated hs_pos).mp hseparated'
    let S : RectangleSubfamily R := S'.ofSmul
    have hSnonempty : S.family.Nonempty := by
      have hfamily : (S.family).smul s hs_pos = S'.family :=
        RectangleSubfamily.ofSmul_family_smul S'
      rw [← hfamily] at hS'nonempty
      exact (RectangleFamily.smul_nonempty hs_pos S.family).mp hS'nonempty
    have hStangent : ∀ j,
        q ≤ RectangleFamily.tangentCount (S.family.rectangle j)
              (H.cluster c r) tangency ∧
        q ≤ RectangleFamily.tangentCount (S.family.rectangle j)
              (H.cluster d r) tangency := by
      intro j
      have h := hS'tangent j
      have hrectangle :
          S'.family.rectangle j =
            (S.family.rectangle j).smul s hs_pos :=
        RectangleFamily.smul_rectangle hs_pos S.family j
      rw [hrectangle, hclusterC, hclusterD] at h
      have hC :
          RectangleFamily.tangentCount
              ((S.family.rectangle j).smul s hs_pos)
              (s • H.cluster c r) tangency =
            RectangleFamily.tangentCount (S.family.rectangle j)
              (H.cluster c r) tangency :=
        RectangleFamily.smul_tangentCount hs_pos
      have hD :
          RectangleFamily.tangentCount
              ((S.family.rectangle j).smul s hs_pos)
              (s • H.cluster d r) tangency =
            RectangleFamily.tangentCount (S.family.rectangle j)
              (H.cluster d r) tangency :=
        RectangleFamily.smul_tangentCount hs_pos
      rw [hC, hD] at h
      exact h
    have hScard : (R.card : ℝ) ≤
        (centers.card : ℝ) ^ 2 *
          (C * Real.rpow tangency C * Real.rpow A C *
            Real.rpow (RectangleFamily.bipartiteNormalizedCount
              (H.cluster c r) (H.cluster d r) q q) (3 / 2 : ℝ) *
            Real.log (RectangleFamily.bipartiteNormalizedCount
              (H.cluster c r) (H.cluster d r) q q)) := by
      have hcenters : centers'.card = centers.card :=
        Finset.image_smul_card hs_pos centers
      have hnormalized :
          RectangleFamily.bipartiteNormalizedCount
              (H'.cluster (s • c) r') (H'.cluster (s • d) r') q q =
            RectangleFamily.bipartiteNormalizedCount
              (H.cluster c r) (H.cluster d r) q q := by
        rw [hclusterC, hclusterD]
        exact RectangleFamily.smul_bipartiteNormalizedCount hs_pos
      simpa [hR'card, hcenters, hnormalized] using hS'card
    exact ⟨c, hc, d, hd, hseparated, S, hSnonempty, hStangent, hScard⟩

theorem q_cluster_count_constants
    (hScaleFree : ScaleFreeNormalCoarseRectangleCountStatement)
    (hFiberSep : FiberwiseSeparatedTangentBallPairAtStatement)
    (hShared : SharedTangentBallPairPigeonholeAtStatement)
    (hRobust : BipartiteTangencyRobustFullStatement)
    (hNormal : NormalCoarseRectangleCountStatement)
    (K : ℝ) (hK : 1 ≤ K) :
    ∃ C_positive C_singleton : ℝ,
      1 ≤ C_positive ∧ 1 ≤ C_singleton := by
  rcases hScaleFree hFiberSep hShared hRobust hNormal K hK with
    ⟨C_positive, hC_positive, _⟩
  rcases scale_free_normal_coarse_rectangle_count_from_pairs
      hShared hRobust normal_coarse_rectangle_count_from_pairs K hK with
    ⟨C_singleton, hC_singleton, _⟩
  exact ⟨C_positive, C_singleton, hC_positive, hC_singleton⟩

end Kakeya.Cinematic
