import MyLeanRepo.Kakeya.Assouad.WZ1.OSWSupportNormalizationStatement

/-!
# Quantitative transport through the common OSW similarity

The support normalization uses one midpoint-centered homothety on both
finite sets.  This module freezes the quantitative Frostman and thin-tube
transport needed before and after the OSW iteration.
-/

namespace Kakeya.Assouad

/--
Frostman and thin-tube certificates transported through one common
normalizing similarity.

The Frostman loss `C -> 2 * C` uses the lower scale bound `1 / 2 <= scale`.
For `0 <= beta <= 1`, the same bound gives
`scale ^ (-beta) <= 2`, so a thin-tube constant loses at most a factor two
in either direction.  The exceptional fraction is unchanged because the
common homothety is injective on pairs.
-/
structure WZ1OSWCommonSimilarityTransportData
    {delta : ℝ} {G₁ G₂ : DiscreteSet 2}
    (D : WZ1OSWSupportNormalizationData delta G₁ G₂)
    (C : ENNReal) where
  normalized₁_frostman :
    D.normalized₁.IsFrostman D.normalizedDelta 1 (2 * C)
  normalized₂_frostman :
    D.normalized₂.IsFrostman D.normalizedDelta 1 (2 * C)
  thin_forward₁₂ :
    ∀ {beta K c : ℝ}, beta ≤ 1 →
      HasDiscreteThinTubes delta beta K c G₁ G₂ →
        HasDiscreteThinTubes
          D.normalizedDelta beta (2 * K) c
          D.normalized₁ D.normalized₂
  thin_forward₂₁ :
    ∀ {beta K c : ℝ}, beta ≤ 1 →
      HasDiscreteThinTubes delta beta K c G₂ G₁ →
        HasDiscreteThinTubes
          D.normalizedDelta beta (2 * K) c
          D.normalized₂ D.normalized₁
  thin_backward₁₂ :
    ∀ {beta K c : ℝ}, beta ≤ 1 →
      HasDiscreteThinTubes
          D.normalizedDelta beta K c
          D.normalized₁ D.normalized₂ →
        HasDiscreteThinTubes delta beta (2 * K) c G₁ G₂
  thin_backward₂₁ :
    ∀ {beta K c : ℝ}, beta ≤ 1 →
      HasDiscreteThinTubes
          D.normalizedDelta beta K c
          D.normalized₂ D.normalized₁ →
        HasDiscreteThinTubes delta beta (2 * K) c G₂ G₁

/--
Transport the original Frostman estimates and all later discrete thin-tube
witnesses through the common similarity selected by
`WZ1OSWSupportNormalizationData`.

The forward direction is used before smoothing and OSW.  The backward
direction returns the boosted discrete thin-tube estimate to the original
coordinates before applying Lemma 40.  No independent map is permitted on
the two factors.
-/
def WZ1OSWCommonSimilarityTransportStatement : Prop :=
  ∀ {delta : ℝ} {G₁ G₂ : DiscreteSet 2}
      (D : WZ1OSWSupportNormalizationData delta G₁ G₂)
      {C : ENNReal},
    1 ≤ C →
    G₁.IsFrostman delta 1 C →
    G₂.IsFrostman delta 1 C →
      Nonempty (WZ1OSWCommonSimilarityTransportData D C)

end Kakeya.Assouad
