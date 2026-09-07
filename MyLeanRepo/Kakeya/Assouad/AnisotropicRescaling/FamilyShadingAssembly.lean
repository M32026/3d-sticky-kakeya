import MyLeanRepo.Kakeya.Assouad.AnisotropicRescaling.ShadingConstruction

/-!
# Family-level shading assembly for anisotropic rescaling

Promote per-source-tube image coverage to coverage of the full shaded slab,
then construct the target shading with the exact forward, thickening, and
slope-window containments.
-/

noncomputable section

namespace Kakeya.Assouad

lemma shading_slab_image_subset_family_union
    {delta rho : ℝ}
    (F : Kakeya.Streamlined.TubeFamily delta)
    (Y : Kakeya.Streamlined.TubeShading F)
    (Phi : Point3 → Point3)
    (c d : ℝ)
    (coarse : Kakeya.Streamlined.TubeFamily rho)
    (hcover :
      ∀ i,
        Phi '' ((F.tube i).carrier ∩ horizontalSlab c d) ⊆
          coarse.toBodyFamily.union) :
    Phi '' (Y.union ∩ horizontalSlab c d) ⊆
      coarse.toBodyFamily.union := by
  intro z hz
  rcases hz with ⟨p, hp, rfl⟩
  rcases hp.1 with ⟨i, hi⟩
  exact hcover i ⟨p, ⟨Y.subset_body i hi, hp.2⟩, rfl⟩

lemma construct_anisotropic_target_shading
    {delta rho c d m : ℝ}
    (hcd : c < d)
    (hrho : 0 ≤ rho)
    (F : Kakeya.Streamlined.TubeFamily delta)
    (Y : Kakeya.Streamlined.TubeShading F)
    (g : SlopeFunction)
    (coarse : Kakeya.Streamlined.TubeFamily rho)
    (hcover :
      ∀ i,
        anisotropicRescalingMap g c d m ''
            ((F.tube i).carrier ∩ horizontalSlab c d) ⊆
          coarse.toBodyFamily.union) :
    ∃ Y' : Kakeya.Streamlined.TubeShading coarse,
      anisotropicRescalingMap g c d m ''
          (Y.union ∩ horizontalSlab c d) ⊆
        Y'.union ∧
      Y'.union ⊆
        Metric.cthickening rho
          (anisotropicRescalingMap g c d m ''
            (Y.union ∩ horizontalSlab c d)) ∧
      Y'.union ⊆ horizontalSlab (-1) 1 := by
  have hfamily :
      anisotropicRescalingMap g c d m ''
          (Y.union ∩ horizontalSlab c d) ⊆
        coarse.toBodyFamily.union :=
    shading_slab_image_subset_family_union F Y
      (anisotropicRescalingMap g c d m) c d coarse hcover
  have hwindow :
      anisotropicRescalingMap g c d m ''
          (Y.union ∩ horizontalSlab c d) ⊆
        horizontalSlab (-1) 1 :=
    anisotropicImage_in_slopeWindow hcd Set.inter_subset_right
  exact construct_target_shading Y
    (anisotropicRescalingMap g c d m) c d hrho hfamily hwindow

end Kakeya.Assouad
