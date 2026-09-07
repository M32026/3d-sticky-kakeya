import MyLeanRepo.Kakeya.Assouad.PropStickyPaperLiteralGlobalOutputV2Statements

/-! # Corrected literal-paper global `prop: sticky` assembly -/

noncomputable section

namespace Kakeya.Assouad

theorem WZ2PaperPartitioningCover.fullFiberShading_pointMultiplicity
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ2PaperPartitioningCover fine coarse)
    (shading : WZ1PaperTubeShading fine)
    (parent : Fin coarse.card)
    (point : Point3) :
    (restrictPaperShading
      (cover.fullFiberSubfamily parent)
      shading).pointMultiplicity point =
        wz2PaperFullFiberPointMultiplicity
          coarse shading parent point := by
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
      have hpoint :
          point ∈
            shading.carrier
              ((cover.fullFiberSubfamily parent).embedding index) :=
        (Finset.mem_filter.mp hindex).2
      have hfiber :
          (cover.fullFiberSubfamily parent).embedding index ∈
            indices :=
        cover.fullFiberSubfamily_mem parent index
      exact Finset.mem_filter.mpr ⟨hfiber, hpoint⟩
    · intro first _ second _ h
      exact
        (cover.fullFiberSubfamily parent).embedding.injective h
    · intro source hsource
      have hfiber : source ∈ indices :=
        (Finset.mem_filter.mp hsource).1
      have hpoint :
          point ∈ shading.carrier source :=
        (Finset.mem_filter.mp hsource).2
      let index :
          Fin (cover.fullFiberSubfamily parent).family.card :=
        enumeration.symm ⟨source, hfiber⟩
      have hEmbedding :
          (cover.fullFiberSubfamily parent).embedding index =
            source := by
        exact congrArg Subtype.val
          (enumeration.apply_symm_apply ⟨source, hfiber⟩)
      refine ⟨index, ?_, hEmbedding⟩
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      change
        point ∈
          shading.carrier
            ((cover.fullFiberSubfamily parent).embedding index)
      rw [hEmbedding]
      exact hpoint
  change
    (Finset.univ.filter fun index :
        Fin (cover.fullFiberSubfamily parent).family.card =>
      point ∈
        shading.carrier
          ((cover.fullFiberSubfamily parent).embedding index)).card =
      ((wz2PaperFullFiberIndices fine coarse parent).filter
        fun source => point ∈ shading.carrier source).card
  change
    (Finset.univ.filter fun index :
        Fin (cover.fullFiberSubfamily parent).family.card =>
      point ∈
        shading.carrier
          ((cover.fullFiberSubfamily parent).embedding index)).card =
      ((wz2PaperFullFiberIndices fine coarse parent).filter
        fun source => point ∈ shading.carrier source).card at hCard
  exact hCard

theorem WZ2PaperPartitioningCover.fullFiberSubfamily_enncard
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ2PaperPartitioningCover fine coarse)
    (parent : Fin coarse.card) :
    (cover.fullFiberSubfamily parent).family.enncard =
      wz2PaperFullFiberCount fine coarse parent := by
  rfl

theorem wz2_paper_literal_prop_sticky_assembly_v2 :
    WZ2PaperLiteralPropStickyAssemblyV2Statement := by
  intro normalize normalizeRelative delta sigma loss source shading rho logExponent
    strongLoss hStrongLoss hBudget refinement hCubical
    coarse cover coarseShading balanced coarseExtremalStrong
    coarseExtremal hCoarseMultiplicity hCoarseCardinality
    literalRescaledFiber
  have hCoarseOutput :
      ∀ point,
        (coarseShading.pointMultiplicity point : ENNReal) ≤
          Kakeya.realRpowENN rho.1 (2 - sigma - loss) *
            coarse.enncard :=
    normalize
      coarseExtremal.delta_pos
      coarseExtremal.delta_le_one
      hStrongLoss.le
      hBudget
      hCoarseMultiplicity
  have hFiberOutput :
      ∀ parent : Fin coarse.card,
        ∀ point,
          (wz2PaperFullFiberPointMultiplicity
              coarse refinement.refined parent point : ENNReal) ≤
            Kakeya.realRpowENN (delta / rho.1)
                (2 - sigma - loss) *
              wz2PaperFullFiberCount
                refinement.selected.family coarse parent := by
    intro parent
    rcases literalRescaledFiber parent with ⟨fiberData⟩
    intro point
    have hLocal :
        ((restrictPaperShading
            (cover.fullFiberSubfamily parent)
            refinement.refined).pointMultiplicity point : ENNReal) ≤
          Kakeya.realRpowENN (delta / rho.1)
              (2 - sigma - loss) *
            (cover.fullFiberSubfamily parent).family.enncard :=
      normalizeRelative
        (targetScale := delta / rho.1)
        (sigma := sigma)
        (strongLoss := strongLoss)
        (outputLoss := loss)
        fiberData.extremal_strong.delta_pos
        fiberData.extremal_strong.delta_le_one
        hStrongLoss.le
        hBudget
        (sourceScale := delta)
        (family := (cover.fullFiberSubfamily parent).family)
        (shading :=
          restrictPaperShading
            (cover.fullFiberSubfamily parent)
            refinement.refined)
        fiberData.source_multiplicity_upper_strong
        point
    rw [cover.fullFiberShading_pointMultiplicity
      refinement.refined parent point] at hLocal
    rw [cover.fullFiberSubfamily_enncard parent] at hLocal
    exact hLocal
  exact ⟨{
    strongLoss := strongLoss
    strongLoss_pos := hStrongLoss
    strongLoss_budget := hBudget
    refinement := refinement
    refined_cubical := hCubical
    coarse := coarse
    cover := cover
    coarseShading := coarseShading
    balanced := balanced
    coarse_extremal_strong := coarseExtremalStrong
    coarse_extremal := coarseExtremal
    coarse_multiplicity_upper_strong := hCoarseMultiplicity
    coarse_cardinality_lower := hCoarseCardinality
    literalRescaledFiber := literalRescaledFiber
    coarse_multiplicity_upper := hCoarseOutput
    fiber_multiplicity_upper := hFiberOutput
  }⟩

end Kakeya.Assouad

end
