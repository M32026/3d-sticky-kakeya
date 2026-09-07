import MyLeanRepo.Kakeya.Cinematic.Section5.LevelSetInputs

/-!
# Two-ends bounds for the two bad sets in Lemma 45
-/

namespace Kakeya.Cinematic

theorem lemma45_bad_set_bounds :
    Lemma45BadSetBoundsStatement := by
  unfold Lemma45BadSetBoundsStatement
  intro delta t Delta metricExponent tangencyExponent
    metricCut tangencyCut hdelta ht hDelta hmetricExponent
    htangencyExponent hmetricCut_pos hmetricCut_lt hmetricScale
    htangencyCut_pos htangencyCut_lt htangencyScale I F G hGF
    hMetric hTangency hMetricRetention hTangencySmall g hg
  have hMetricSubset :
      G.carrier ∩ c2Ball g (metricCut * t) ⊆
        F.carrier ∩ c2Ball g (metricCut * t) := by
    intro f hf
    exact ⟨hGF hf.1, hf.2⟩
  have hMetricCard :
      ((G.carrier ∩ c2Ball g (metricCut * t)).ncard : ℝ) ≤
        ((F.carrier ∩ c2Ball g (metricCut * t)).ncard : ℝ) := by
    exact_mod_cast Set.ncard_le_ncard hMetricSubset
      (F.finite.subset Set.inter_subset_left)
  have hTangencySubset :
      G.carrier ∩
          {f | tangencyParameterOn I f g + delta <
            tangencyCut * Delta} ⊆
        F.carrier ∩
          {f | tangencyParameterOn I f g ≤ tangencyCut * Delta} := by
    intro f hf
    refine ⟨hGF hf.1, ?_⟩
    have hf' :
        tangencyParameterOn I f g + delta <
          tangencyCut * Delta := hf.2
    change tangencyParameterOn I f g ≤ tangencyCut * Delta
    exact le_of_lt (by linarith [hf'])
  have hTangencyCard :
      ((G.carrier ∩
          {f | tangencyParameterOn I f g + delta <
            tangencyCut * Delta}).ncard : ℝ) ≤
        ((F.carrier ∩
          {f | tangencyParameterOn I f g ≤
            tangencyCut * Delta}).ncard : ℝ) := by
    exact_mod_cast Set.ncard_le_ncard hTangencySubset
      (F.finite.subset Set.inter_subset_left)
  constructor
  · calc
      3 * ((G.carrier ∩
          c2Ball g (metricCut * t)).ncard : ℝ) ≤
          3 * ((F.carrier ∩
            c2Ball g (metricCut * t)).ncard : ℝ) :=
        mul_le_mul_of_nonneg_left hMetricCard (by norm_num)
      _ ≤ 3 * (4 * Real.rpow (2 * metricCut) metricExponent *
          (F.card : ℝ)) :=
        mul_le_mul_of_nonneg_left (hMetric g hg) (by norm_num)
      _ = 12 * Real.rpow (2 * metricCut) metricExponent *
          (F.card : ℝ) := by ring
      _ ≤ (G.card : ℝ) := hMetricRetention
  · calc
      3 * ((G.carrier ∩
          {f | tangencyParameterOn I f g + delta <
            tangencyCut * Delta}).ncard : ℝ) ≤
          3 * ((F.carrier ∩
            {f | tangencyParameterOn I f g ≤
              tangencyCut * Delta}).ncard : ℝ) :=
        mul_le_mul_of_nonneg_left hTangencyCard (by norm_num)
      _ ≤ 3 * (2 * Real.rpow tangencyCut tangencyExponent *
          (G.card : ℝ)) :=
        mul_le_mul_of_nonneg_left (hTangency g hg) (by norm_num)
      _ = (6 * Real.rpow tangencyCut tangencyExponent) *
          (G.card : ℝ) := by ring
      _ ≤ 1 * (G.card : ℝ) := by
        gcongr
      _ = (G.card : ℝ) := by ring

end Kakeya.Cinematic
