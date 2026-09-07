import MyLeanRepo.Kakeya.Assouad.AnisotropicRescaling.CoaxialOverlap

/-!
WZ Lemma 8 rediscretization: prove volume-half essential distinctness for
small-radius coaxial unit tubes at different consecutive axial positions.
-/

namespace Kakeya.Assouad

theorem coaxial_shifted_tubes_essentially_distinct :
    CoaxialShiftedTubesEssentiallyDistinctStatement := by
  intro _hvolume rho hrho hrho_small base direction hdir s t hsep
  by_cases hst : s ≤ t
  · have hordered : s + 1 ≤ t := by
      have habs : |s - t| = t - s := by
        rw [abs_of_nonpos (sub_nonpos.mpr hst)]
        ring
      rw [habs] at hsep
      linarith
    exact coaxial_shifted_ordered_essentiallyDistinct
      hrho hrho_small base direction hdir hordered
  · have hordered : t + 1 ≤ s := by
      have hts : t < s := lt_of_not_ge hst
      have habs : |s - t| = s - t := by
        rw [abs_of_pos (sub_pos.mpr hts)]
      rw [habs] at hsep
      linarith
    have hreverse :=
      coaxial_shifted_ordered_essentiallyDistinct
        hrho hrho_small base direction hdir hordered
    simpa [Kakeya.DeltaTube.EssentiallyDistinct,
      Set.inter_comm, max_comm] using hreverse

end Kakeya.Assouad
