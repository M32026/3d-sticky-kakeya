import MyLeanRepo.Kakeya.Cinematic.Section5.ScaleFreeNormalCoarseCountInputs
import MyLeanRepo.Kakeya.Cinematic.BipartiteTangencyReduction.VerticalScalingRectangles

/-!
# Transfer the normal coarse count beyond the normalized second scale
-/

open Classical

namespace Kakeya.Cinematic

theorem scale_free_normal_coarse_rectangle_count :
    ScaleFreeNormalCoarseRectangleCountStatement := by
  intro hFiberwise hShared hRobust hNormal K hK
  rcases hNormal hFiberwise hShared hRobust K hK with ⟨C, hC, hMain⟩
  refine' ⟨C, hC, _⟩
  intro family hCurv I hI delta t r tangency A hdelta_pos ht_pos hdelta_le_t
    hr_pos htangency hA hEq hdelta_le_A H hH_sub hH_diam R hR_centers
    hR_central hR_incomp hR_nonempty T hT_sub centers hcenters_nonempty hcover
    q hq_pos h_tangent_lower h_cluster_upper
  by_cases h_t_le_one : t ≤ 1
  · -- Case 1: t ≤ 1, apply the normalized theorem directly
    exact hMain hCurv hI hdelta_pos ht_pos hdelta_le_t h_t_le_one hr_pos
      htangency hA hEq hdelta_le_A H hH_sub hH_diam R hR_centers hR_central
      hR_incomp hR_nonempty T hT_sub centers hcenters_nonempty hcover q hq_pos
      h_tangent_lower h_cluster_upper
  · -- Case 2: 1 < t, scale by s := 1/t
    have h_one_lt_t : 1 < t := by linarith
    set s : ℝ := 1 / t with hs_def
    have hs_pos : 0 < s := by positivity
    have hs_le_one : s ≤ 1 := by
      rw [hs_def]
      exact (div_le_one ht_pos).mpr (by linarith)
    have h_st_eq_one : s * t = 1 := by
      rw [hs_def]
      field_simp [ht_pos.ne'] <;> ring
    -- Scaled data
    let family' : Set C2Function := Set.image (fun f => s • f) family
    let H' : FiniteFunctionFamily := s • H
    let R' : RectangleFamily (s * delta) (s * t) :=
      RectangleFamily.smul s hs_pos R
    have hR'card : R'.card = R.card := RectangleFamily.smul_card hs_pos R
    let eR : Fin R'.card → Fin R.card := Fin.cast hR'card
    let T' : Fin R'.card → FiniteFunctionFamily := fun i => s • T (eR i)
    let centers' : Finset C2Function := centers.image (fun f => s • f)
    let delta' : ℝ := s * delta
    let t' : ℝ := s * t
    let r' : ℝ := s * r
    -- Scaled hypotheses
    have hCurv' : HasCinematicCurvature family' K :=
      hCurv.smul hs_pos hs_le_one
    have hdelta'_pos : 0 < delta' := by positivity
    have ht'_pos : 0 < t' := by positivity
    have hdelta'_le_t' : delta' ≤ t' := by
      dsimp only [delta', t']
      gcongr
    have ht'_le_one : t' ≤ 1 := by
      dsimp only [t']
      rw [h_st_eq_one] <;> norm_num
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
      have h_f_in_family : f ∈ family := hH_sub hf
      exact Set.mem_image_of_mem _ h_f_in_family
    have hH'_diam : ∀ f' ∈ H'.carrier, ∀ g' ∈ H'.carrier, dist f' g' ≤ 6 * t' := by
      intro f' hf' g' hg'
      rcases (FiniteFunctionFamily.mem_smul_iff hs_pos).mp hf' with ⟨f, hf, rfl⟩
      rcases (FiniteFunctionFamily.mem_smul_iff hs_pos).mp hg' with ⟨g, hg, rfl⟩
      have h1 : dist f g ≤ 6 * t := hH_diam f hf g hg
      have h2 : dist (s • f) (s • g) = s * dist f g := by
        simpa [c2Distance_eq_dist] using c2Distance_smul hs_pos.le f g
      rw [h2]
      have h3 : s * dist f g ≤ s * (6 * t) := by gcongr
      have h4 : s * (6 * t) = 6 * (s * t) := by ring
      rw [h4] at h3
      exact h3
    have hR'_centers : R'.CentersIn family' :=
      RectangleFamily.smul_centersIn_forward hs_pos hR_centers
    have hR'_central : R'.IsOverCentralQuarterOf I :=
      RectangleFamily.smul_overCentralQuarterOf hs_pos hR_central
    have hR'_incomp : R'.IsPairwiseIncomparable family' 100 :=
      RectangleFamily.smul_pairwiseIncomparable_forward hs_pos hR_incomp
    have hR'_nonempty : R'.Nonempty :=
      (RectangleFamily.smul_nonempty hs_pos R).mpr hR_nonempty
    have hT'_sub : ∀ i, (T' i).carrier ⊆ H'.carrier :=
      fun i => FiniteFunctionFamily.smul_subset hs_pos (hT_sub (eR i))
    have hcenters'_nonempty : centers'.Nonempty := by
      exact Finset.Nonempty.image hcenters_nonempty (fun f : C2Function => s • f)
    have hcover' : ∀ i, (T' i).carrier ⊆ ⋃ c' ∈ centers', c2Ball c' r' := by
      intro i f' hf'
      rcases (FiniteFunctionFamily.mem_smul_iff hs_pos).mp hf' with ⟨f, hf, rfl⟩
      have h5 : f ∈ (T (eR i)).carrier := hf
      have h6 : f ∈ ⋃ c ∈ centers, c2Ball c r := hcover (eR i) h5
      have h_exists : ∃ (c : C2Function), c ∈ centers ∧ f ∈ c2Ball c r := by
        simpa [Set.mem_iUnion₂] using h6
      rcases h_exists with ⟨c, hc, hball⟩
      have h7 : s • f ∈ c2Ball (s • c) r' := by
        dsimp only [r']
        exact (mem_c2Ball_smul hs_pos).mpr hball
      have h8 : s • c ∈ centers' := by
        exact Finset.mem_image.mpr ⟨c, hc, rfl⟩
      exact Set.mem_iUnion₂.mpr ⟨s • c, h8, h7⟩
    have h_tangent_lower' : ∀ i,
        2 * centers'.card * q ≤
          RectangleFamily.tangentCount (R'.rectangle i) (T' i) tangency := by
      intro i
      have h13 : centers'.card = centers.card :=
        Finset.image_smul_card hs_pos centers
      have h14 : RectangleFamily.tangentCount (R'.rectangle i) (T' i) tangency =
          RectangleFamily.tangentCount (R.rectangle (eR i)) (T (eR i)) tangency := by
        dsimp only [T']
        exact RectangleFamily.smul_tangentCount hs_pos
      rw [h13, h14]
      exact h_tangent_lower (eR i)
    have h_cluster_upper' : ∀ i, ∀ c' ∈ centers',
        2 * RectangleFamily.tangentCount (R'.rectangle i)
              ((T' i).cluster c' (11 * r')) tangency ≤
          RectangleFamily.tangentCount (R'.rectangle i) (T' i) tangency := by
      intro i c' hc'
      rcases Finset.mem_image.mp hc' with ⟨c, hc, h_eq⟩
      have hc'_eq : c' = s • c := h_eq.symm
      have h9 : (T' i).cluster c' (11 * r') =
          s • ((T (eR i)).cluster c (11 * r)) := by
        dsimp only [T', r']
        rw [hc'_eq]
        have h10 : 11 * (s * r) = s * (11 * r) := by ring
        rw [h10]
        exact FiniteFunctionFamily.smul_cluster hs_pos (T (eR i)) c (11 * r)
      rw [h9]
      have h11 : RectangleFamily.tangentCount (R'.rectangle i)
            (s • (T (eR i)).cluster c (11 * r)) tangency =
          RectangleFamily.tangentCount (R.rectangle (eR i))
            ((T (eR i)).cluster c (11 * r)) tangency :=
        RectangleFamily.smul_tangentCount hs_pos
      have h12 : RectangleFamily.tangentCount (R'.rectangle i) (T' i) tangency =
          RectangleFamily.tangentCount (R.rectangle (eR i)) (T (eR i)) tangency := by
        dsimp only [T']
        exact RectangleFamily.smul_tangentCount hs_pos
      rw [h11, h12]
      exact h_cluster_upper (eR i) c hc
    -- Apply normalized theorem to scaled data
    have h_result := hMain hCurv' hI hdelta'_pos ht'_pos hdelta'_le_t' ht'_le_one
      hr'_pos htangency hA hEq' hdelta'_le_A H' hH'_sub hH'_diam R' hR'_centers
      hR'_central hR'_incomp hR'_nonempty T' hT'_sub centers' hcenters'_nonempty
      hcover' q hq_pos h_tangent_lower' h_cluster_upper'
    rcases h_result with ⟨c', hc'_in, d', hd'_in, h_sep', S', hS'_nonempty,
      hS'_tangent, hS'_card⟩
    -- Descale witnesses
    rcases Finset.mem_image.mp hc'_in with ⟨c, hc, h_eq1⟩
    rcases Finset.mem_image.mp hd'_in with ⟨d, hd, h_eq2⟩
    have hc'_eq : c' = s • c := h_eq1.symm
    have hd'_eq : d' = s • d := h_eq2.symm
    have hH'_cluster_c : H'.cluster c' r' = s • (H.cluster c r) := by
      dsimp only [H', r']
      rw [hc'_eq]
      exact FiniteFunctionFamily.smul_cluster hs_pos H c r
    have hH'_cluster_d : H'.cluster d' r' = s • (H.cluster d r) := by
      dsimp only [H', r']
      rw [hd'_eq]
      exact FiniteFunctionFamily.smul_cluster hs_pos H d r
    have h_sep : (H.cluster c r).AreSeparated (H.cluster d r) (8 * r) := by
      have h15 : (H'.cluster c' r').AreSeparated (H'.cluster d' r') (8 * r') := h_sep'
      rw [hH'_cluster_c, hH'_cluster_d] at h15
      dsimp only [r'] at h15
      have h16 : 8 * (s * r) = s * (8 * r) := by ring
      rw [h16] at h15
      exact (FiniteFunctionFamily.smul_AreSeparated hs_pos).mp h15
    let S : RectangleSubfamily R := S'.ofSmul
    have hS_family_smul : (S.family).smul s hs_pos = S'.family :=
      RectangleSubfamily.ofSmul_family_smul S'
    have hS_card_eq : S.family.card = S'.family.card := by rfl
    have hS_nonempty : S.family.Nonempty := by
      have h17 : S'.family.Nonempty := hS'_nonempty
      have h18 : (S.family).smul s hs_pos = S'.family := hS_family_smul
      rw [← h18] at h17
      exact (RectangleFamily.smul_nonempty hs_pos S.family).mp h17
    have hS_tangent : ∀ j,
        q ≤ RectangleFamily.tangentCount (S.family.rectangle j)
              (H.cluster c r) tangency ∧
        q ≤ RectangleFamily.tangentCount (S.family.rectangle j)
              (H.cluster d r) tangency := by
      intro j
      have h19 := hS'_tangent j
      have h20 : S'.family.rectangle j =
          (S.family.rectangle j).smul s hs_pos :=
        RectangleFamily.smul_rectangle hs_pos S.family j
      rw [h20, hH'_cluster_c, hH'_cluster_d] at h19
      have h25 : RectangleFamily.tangentCount
            ((S.family.rectangle j).smul s hs_pos)
            (s • H.cluster c r) tangency =
          RectangleFamily.tangentCount (S.family.rectangle j)
            (H.cluster c r) tangency :=
        RectangleFamily.smul_tangentCount hs_pos
      have h26 : RectangleFamily.tangentCount
            ((S.family.rectangle j).smul s hs_pos)
            (s • H.cluster d r) tangency =
          RectangleFamily.tangentCount (S.family.rectangle j)
            (H.cluster d r) tangency :=
        RectangleFamily.smul_tangentCount hs_pos
      rw [h25, h26] at h19
      exact h19
    have hS_card : (R.card : ℝ) ≤
        (centers.card : ℝ)^2 *
          (C * Real.rpow tangency C * Real.rpow A C *
            Real.rpow (RectangleFamily.bipartiteNormalizedCount
              (H.cluster c r) (H.cluster d r) q q) (3 / 2 : ℝ) *
            Real.log (RectangleFamily.bipartiteNormalizedCount
              (H.cluster c r) (H.cluster d r) q q)) := by
      have h27 := hS'_card
      have h28 : R'.card = R.card := hR'card
      have h29 : centers'.card = centers.card :=
        Finset.image_smul_card hs_pos centers
      have h30 : RectangleFamily.bipartiteNormalizedCount
            (H'.cluster c' r') (H'.cluster d' r') q q =
          RectangleFamily.bipartiteNormalizedCount
            (H.cluster c r) (H.cluster d r) q q := by
        rw [hH'_cluster_c, hH'_cluster_d]
        exact RectangleFamily.smul_bipartiteNormalizedCount hs_pos
      simp only [h28, h29, h30] at h27
      exact h27
    exact ⟨c, hc, d, hd, h_sep, S, hS_nonempty, hS_tangent, hS_card⟩

end Kakeya.Cinematic
