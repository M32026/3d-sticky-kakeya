import MyLeanRepo.Kakeya.Assouad.PropStickyPaperSubfamilyZeroExtension
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperBoundaryCoefficient

/-!
# Fixed-origin boundary mass for a selected subfamily shading

An arbitrary subfamily does not inherit normalized Convex-Wolff axioms.
Instead extend its shading by zero to the ambient family and apply the ambient
top-level CWA.  The indexed boundary mass is unchanged by zero extension.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

theorem wz2_paper_subfamily_grid_boundary_mass_normalized
    {delta rho : ℝ}
    (hdelta : 0 < delta)
    (hdeltaSmall : delta ≤ 1 / 24)
    (hrho : 0 < rho)
    (hrhoOne : rho ≤ 1)
    (hperiodicScale : 50 * delta ≤ rho)
    {family : Kakeya.Streamlined.TubeFamily delta}
    (hline : WZ1PaperIsLineClass family)
    (selected : Kakeya.Streamlined.TubeSubfamily family)
    (shading : WZ1PaperTubeShading selected.family)
    {C : ENNReal}
    (hcwa : WZ2PaperConvexWolffBound family C) :
    (∑ index : Fin selected.family.card,
        volume
          (shading.carrier index ∩
            wz2PaperGridBoundaryRegion delta rho)) ≤
      family.enncard *
        ((24000000 : ENNReal) *
          (C * wz2PaperBoundaryGeometryConstant + 1) *
          Kakeya.realRpowENN delta 2 *
          ENNReal.ofReal (Real.sqrt (delta / rho))) := by
  rcases
      wz2_paper_subfamily_zero_extension selected shading
    with ⟨zeroExtension⟩
  have hAmbient :=
    wz2_paper_grid_boundary_mass_normalized
      hdelta hdeltaSmall hrho hrhoOne hperiodicScale
      hline zeroExtension.ambientShading hcwa
  have hBoundaryEq :
      (∑ index : Fin family.card,
          volume
            (zeroExtension.ambientShading.carrier index ∩
              wz2PaperGridBoundaryRegion delta rho)) =
        ∑ index : Fin selected.family.card,
          volume
            (shading.carrier index ∩
              wz2PaperGridBoundaryRegion delta rho) := by
    let selectedImage : Finset (Fin family.card) :=
      Finset.image selected.embedding Finset.univ
    calc
      (∑ index : Fin family.card,
          volume
            (zeroExtension.ambientShading.carrier index ∩
              wz2PaperGridBoundaryRegion delta rho)) =
          ∑ index ∈ selectedImage,
            volume
              (zeroExtension.ambientShading.carrier index ∩
                wz2PaperGridBoundaryRegion delta rho) := by
        symm
        apply Finset.sum_subset (Finset.subset_univ _)
        intro index _ hindex
        have hEmpty :
            zeroExtension.ambientShading.carrier index = ∅ := by
          apply Set.not_nonempty_iff_eq_empty.mp
          intro hnonempty
          rcases hnonempty with ⟨point, hpoint⟩
          rcases zeroExtension.carrier_support index point hpoint with
            ⟨sourceIndex, hsource, _⟩
          exact hindex <|
            Finset.mem_image.mpr
              ⟨sourceIndex, Finset.mem_univ _, hsource⟩
        rw [hEmpty]
        simp
      _ =
          ∑ sourceIndex : Fin selected.family.card,
            volume
              (zeroExtension.ambientShading.carrier
                  (selected.embedding sourceIndex) ∩
                wz2PaperGridBoundaryRegion delta rho) := by
        rw [Finset.sum_image]
        intro first _ second _ h
        exact selected.embedding.injective h
      _ =
          ∑ sourceIndex : Fin selected.family.card,
            volume
              (shading.carrier sourceIndex ∩
                wz2PaperGridBoundaryRegion delta rho) := by
        apply Finset.sum_congr rfl
        intro sourceIndex _
        rw [zeroExtension.carrier_embedding sourceIndex]
  rw [← hBoundaryEq]
  exact hAmbient

end Kakeya.Assouad

end
