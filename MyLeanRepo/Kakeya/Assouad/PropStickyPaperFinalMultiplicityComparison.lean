import MyLeanRepo.Kakeya.Assouad.PropStickyPaperFinalMultiplicityComparisonStatements
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperGlobalMultiplicityProduct
import MyLeanRepo.Kakeya.Assouad.PropStickyFullFiberHelpers

/-! # Final coarse/fiber multiplicity comparison -/

noncomputable section

namespace Kakeya.Assouad

theorem WZ2PaperPartitioningCover.restrict_fullFiber_pointMultiplicity_eq
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ2PaperPartitioningCover fine coarse)
    (shading : WZ1PaperTubeShading fine)
    (parent : Fin coarse.card) (point : Point3) :
    (restrictPaperShading
      (cover.fullFiberSubfamily parent)
      shading).pointMultiplicity point =
        cover.fiberPointMultiplicity shading parent point := by
  classical
  let indices := wz2PaperFullFiberIndices fine coarse parent
  let enumeration : Fin indices.card ≃ indices :=
    (indices.orderIsoOfFin rfl).toEquiv
  let localActive :
      Finset
        (Fin (cover.fullFiberSubfamily parent).family.card) :=
    Finset.univ.filter fun index =>
      point ∈
        (restrictPaperShading
          (cover.fullFiberSubfamily parent)
          shading).carrier index
  let ambientActive : Finset (Fin fine.card) :=
    indices.filter fun source =>
      point ∈ shading.carrier source
  have hCard : localActive.card = ambientActive.card := by
    apply Finset.card_bij
      (fun index _ =>
        (cover.fullFiberSubfamily parent).embedding index)
    · intro index hindex
      exact
        Finset.mem_filter.mpr
          ⟨cover.fullFiberSubfamily_mem parent index,
            (Finset.mem_filter.mp hindex).2⟩
    · intro first _ second _ h
      exact
        (cover.fullFiberSubfamily parent).embedding.injective h
    · intro source hsource
      let index :
          Fin (cover.fullFiberSubfamily parent).family.card :=
        enumeration.symm
          ⟨source, (Finset.mem_filter.mp hsource).1⟩
      have hEmbedding :
          (cover.fullFiberSubfamily parent).embedding index =
            source :=
        congrArg Subtype.val
          (enumeration.apply_symm_apply
            ⟨source, (Finset.mem_filter.mp hsource).1⟩)
      refine ⟨index, ?_, hEmbedding⟩
      exact
        Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, by
            change
              point ∈
                shading.carrier
                  ((cover.fullFiberSubfamily parent).embedding index)
            rw [hEmbedding]
            exact (Finset.mem_filter.mp hsource).2⟩
  change
    (Finset.univ.filter fun index :
        Fin (cover.fullFiberSubfamily parent).family.card =>
      point ∈
        shading.carrier
          ((cover.fullFiberSubfamily parent).embedding index)).card =
      ((cover.fiberIndices parent).filter fun source =>
        point ∈ shading.carrier source).card
  rw [← cover.fullFiberIndices_eq parent]
  exact hCard

theorem wz2_paper_final_multiplicity_comparison :
    WZ2PaperFinalMultiplicityComparisonStatement := by
  intro delta rho fine coarse cover fineShading coarseShading balanced
    coarseLevel fiberLevel hCoarseBand hFiberBand
    massLower volumeUpper hMass hVolume
  let coarseCap : ENNReal :=
    (2 ^ (coarseLevel + 1) : ENNReal)
  let fiberCap : ENNReal :=
    (2 ^ (fiberLevel + 1) : ENNReal)
  have hCoarseCap :
      ∀ point,
        (coarseShading.pointMultiplicity point : ENNReal) ≤
          coarseCap := by
    intro point
    by_cases hpoint : point ∈ coarseShading.union
    · exact (hCoarseBand point hpoint).2.le
    · have hzero :
          coarseShading.pointMultiplicity point = 0 := by
        classical
        simp [Kakeya.Streamlined.Shading.pointMultiplicity,
          show ∀ index, point ∉ coarseShading.carrier index by
            intro index hindex
            exact hpoint ⟨index, hindex⟩]
      rw [hzero]
      simp
  have hFiberCap :
      ∀ parent point,
        (cover.toWZ1PaperTubeCover.fiberPointMultiplicity
            fineShading parent point : ENNReal) ≤
          fiberCap := by
    intro parent point
    have hEq :=
      cover.restrict_fullFiber_pointMultiplicity_eq
        fineShading parent point
    let fiberShading :=
      restrictPaperShading
        (cover.fullFiberSubfamily parent) fineShading
    rw [← hEq]
    by_cases hpoint : point ∈ fiberShading.union
    · exact (hFiberBand parent point hpoint).2.le
    · have hzero :
          fiberShading.pointMultiplicity point = 0 := by
        classical
        simp [Kakeya.Streamlined.Shading.pointMultiplicity,
          show ∀ index, point ∉ fiberShading.carrier index by
            intro index hindex
            exact hpoint ⟨index, hindex⟩]
      rw [hzero]
      simp
  have hProduct :
      massLower ≤ (coarseCap * fiberCap) * volumeUpper :=
    wz2_paper_global_multiplicity_product
      cover.toWZ1PaperTubeCover fineShading coarseShading
      balanced.point_compatibility
      coarseCap fiberCap massLower volumeUpper
      hCoarseCap hFiberCap hMass hVolume
  exact
    ⟨{
      coarseCap := coarseCap
      coarseCap_eq := rfl
      fiberCap := fiberCap
      fiberCap_eq := rfl
      coarse_band := hCoarseBand
      fiber_band := hFiberBand
      mass_lower := hMass
      volume_upper := hVolume
      product_lower := hProduct
    }⟩

namespace WZ2PaperFinalMultiplicityComparisonData

theorem coarse_pointMultiplicity_le_cap
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : WZ2PaperPartitioningCover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    {balanced :
      WZ1PaperBalancedCoverData
        cover.toWZ1PaperTubeCover fineShading coarseShading}
    {coarseLevel fiberLevel : ℕ}
    {massLower volumeUpper : ENNReal}
    (data :
      WZ2PaperFinalMultiplicityComparisonData
        cover fineShading coarseShading balanced
        coarseLevel fiberLevel massLower volumeUpper) :
    ∀ point,
      (coarseShading.pointMultiplicity point : ENNReal) ≤
        data.coarseCap := by
  intro point
  by_cases hpoint : point ∈ coarseShading.union
  · exact (data.coarse_band point hpoint).2.le
  · have hzero :
        coarseShading.pointMultiplicity point = 0 := by
      classical
      simp [Kakeya.Streamlined.Shading.pointMultiplicity,
        show ∀ index, point ∉ coarseShading.carrier index by
          intro index hindex
          exact hpoint ⟨index, hindex⟩]
    rw [hzero]
    simp

theorem fiber_pointMultiplicity_le_cap
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : WZ2PaperPartitioningCover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    {balanced :
      WZ1PaperBalancedCoverData
        cover.toWZ1PaperTubeCover fineShading coarseShading}
    {coarseLevel fiberLevel : ℕ}
    {massLower volumeUpper : ENNReal}
    (data :
      WZ2PaperFinalMultiplicityComparisonData
        cover fineShading coarseShading balanced
        coarseLevel fiberLevel massLower volumeUpper) :
    ∀ parent point,
      (cover.toWZ1PaperTubeCover.fiberPointMultiplicity
          fineShading parent point : ENNReal) ≤
        data.fiberCap := by
  intro parent point
  have hEq :=
    cover.restrict_fullFiber_pointMultiplicity_eq
      fineShading parent point
  let fiberShading :=
    restrictPaperShading
      (cover.fullFiberSubfamily parent) fineShading
  rw [← hEq]
  by_cases hpoint : point ∈ fiberShading.union
  · exact (data.fiber_band parent point hpoint).2.le
  · have hzero :
        fiberShading.pointMultiplicity point = 0 := by
      classical
      simp [Kakeya.Streamlined.Shading.pointMultiplicity,
        show ∀ index, point ∉ fiberShading.carrier index by
          intro index hindex
          exact hpoint ⟨index, hindex⟩]
    rw [hzero]
    simp

end WZ2PaperFinalMultiplicityComparisonData

end Kakeya.Assouad

end
