import MyLeanRepo.Kakeya.CV.MultilinearKakeya

/-!
# Restrict multilinear Kakeya to shadings

The monotonicity bridge from the full delta-tube carrier estimate to the
measurable shadings used by WZ1.
-/

namespace Kakeya.CV

open MeasureTheory

theorem multilinear_kakeya_shading_restriction
    (h : DeltaTubeMultilinearKakeyaStatement) :
    MultilinearKakeyaThreeStatement := by
  rcases h with ⟨C, hC, hcarrier⟩
  refine ⟨C, hC, ?_⟩
  intro δ hδ hδ1 F Y
  apply le_trans ?_ (hcarrier δ hδ hδ1 F)
  apply lintegral_mono
  intro x
  apply ENNReal.rpow_le_rpow ?_ (by norm_num)
  dsimp only [shadingTrilinearMultiplicity,
    deltaTubeTrilinearMultiplicity]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  apply Finset.sum_le_sum
  intro k _
  have hindicator : ∀ a : Fin F.card,
      setIndicator (Y.carrier a) x ≤
        setIndicator (F.tube a).carrier x := by
    intro a
    by_cases hx : x ∈ Y.carrier a
    · have hxtube : x ∈ (F.tube a).carrier :=
        Y.subset_body a hx
      simp [setIndicator, hx, hxtube]
    · simp [setIndicator, hx]
  have hi := hindicator i
  have hj := hindicator j
  have hk := hindicator k
  gcongr

end Kakeya.CV
