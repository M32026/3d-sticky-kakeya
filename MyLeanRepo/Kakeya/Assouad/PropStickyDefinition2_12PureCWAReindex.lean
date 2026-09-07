import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12BodyReindex

/-!
# Pure Definition 2.12 under exact finite tube reindexing

An exact equivalence of the finite indices of two ordinary tube families
preserves every part of the pure Definition 2.12 interface.  The coarse
family is unchanged.  Strict and centered-doubled geometric fibers are
transported pointwise, while each canonical actual-John `BodyFamily` is
transported through the induced equivalence of its complete full-fiber
enumeration.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

/-- Exact tube reindexing transports every ordinary dilated fiber. -/
theorem wz2PaperOrdinaryDilatedFiberIndices_image_of_reindex
    {delta rho factor : ℝ}
    {source target : Kakeya.Streamlined.TubeFamily delta}
    (coarse : Kakeya.Streamlined.TubeFamily rho)
    (indexEquiv : Fin target.card ≃ Fin source.card)
    (tube_eq :
      ∀ index : Fin target.card,
        target.tube index = source.tube (indexEquiv index))
    (parent : Fin coarse.card) :
    Finset.image indexEquiv
        (wz2PaperOrdinaryDilatedFiberIndices
          factor target coarse parent) =
      wz2PaperOrdinaryDilatedFiberIndices
        factor source coarse parent := by
  ext sourceIndex
  constructor
  · intro hsource
    rcases Finset.mem_image.mp hsource with
      ⟨targetIndex, htarget, rfl⟩
    rw [mem_wz2PaperOrdinaryDilatedFiberIndices_iff] at htarget ⊢
    simpa only [tube_eq] using htarget
  · intro hsource
    refine Finset.mem_image.mpr
      ⟨indexEquiv.symm sourceIndex, ?_,
        indexEquiv.apply_symm_apply sourceIndex⟩
    rw [mem_wz2PaperOrdinaryDilatedFiberIndices_iff] at hsource ⊢
    simpa only [tube_eq, indexEquiv.apply_symm_apply] using hsource

/-- Exact tube reindexing transports every ordinary strict full fiber. -/
theorem wz2PaperOrdinaryFullFiberIndices_image_of_reindex
    {delta rho : ℝ}
    {source target : Kakeya.Streamlined.TubeFamily delta}
    (coarse : Kakeya.Streamlined.TubeFamily rho)
    (indexEquiv : Fin target.card ≃ Fin source.card)
    (tube_eq :
      ∀ index : Fin target.card,
        target.tube index = source.tube (indexEquiv index))
    (parent : Fin coarse.card) :
    Finset.image indexEquiv
        (wz2PaperOrdinaryFullFiberIndices target coarse parent) =
      wz2PaperOrdinaryFullFiberIndices source coarse parent := by
  ext sourceIndex
  constructor
  · intro hsource
    rcases Finset.mem_image.mp hsource with
      ⟨targetIndex, htarget, rfl⟩
    rw [mem_wz2PaperOrdinaryFullFiberIndices_iff] at htarget ⊢
    simpa only [tube_eq] using htarget
  · intro hsource
    refine Finset.mem_image.mpr
      ⟨indexEquiv.symm sourceIndex, ?_,
        indexEquiv.apply_symm_apply sourceIndex⟩
    rw [mem_wz2PaperOrdinaryFullFiberIndices_iff] at hsource ⊢
    simpa only [tube_eq, indexEquiv.apply_symm_apply] using hsource

/-- Exact tube reindexing transports every centered-doubled fiber. -/
theorem wz2PaperOrdinaryDoubledFiberIndices_image_of_reindex
    {delta rho : ℝ}
    {source target : Kakeya.Streamlined.TubeFamily delta}
    (coarse : Kakeya.Streamlined.TubeFamily rho)
    (indexEquiv : Fin target.card ≃ Fin source.card)
    (tube_eq :
      ∀ index : Fin target.card,
        target.tube index = source.tube (indexEquiv index))
    (parent : Fin coarse.card) :
    Finset.image indexEquiv
        (wz2PaperOrdinaryDilatedFiberIndices 2 target coarse parent) =
      wz2PaperOrdinaryDilatedFiberIndices 2 source coarse parent :=
  wz2PaperOrdinaryDilatedFiberIndices_image_of_reindex
    coarse indexEquiv tube_eq parent

/-- Exact tube reindexing preserves strict full-fiber cardinality. -/
theorem wz2PaperOrdinaryFullFiber_card_eq_of_reindex
    {delta rho : ℝ}
    {source target : Kakeya.Streamlined.TubeFamily delta}
    (coarse : Kakeya.Streamlined.TubeFamily rho)
    (indexEquiv : Fin target.card ≃ Fin source.card)
    (tube_eq :
      ∀ index : Fin target.card,
        target.tube index = source.tube (indexEquiv index))
    (parent : Fin coarse.card) :
    (wz2PaperOrdinaryFullFiberIndices target coarse parent).card =
      (wz2PaperOrdinaryFullFiberIndices source coarse parent).card := by
  rw [← wz2PaperOrdinaryFullFiberIndices_image_of_reindex
    coarse indexEquiv tube_eq parent]
  exact
    (Finset.card_image_of_injective _ indexEquiv.injective).symm

/-- Exact tube reindexing preserves centered-doubled-fiber cardinality. -/
theorem wz2PaperOrdinaryDoubledFiber_card_eq_of_reindex
    {delta rho : ℝ}
    {source target : Kakeya.Streamlined.TubeFamily delta}
    (coarse : Kakeya.Streamlined.TubeFamily rho)
    (indexEquiv : Fin target.card ≃ Fin source.card)
    (tube_eq :
      ∀ index : Fin target.card,
        target.tube index = source.tube (indexEquiv index))
    (parent : Fin coarse.card) :
    (wz2PaperOrdinaryDilatedFiberIndices 2 target coarse parent).card =
      (wz2PaperOrdinaryDilatedFiberIndices 2 source coarse parent).card := by
  rw [← wz2PaperOrdinaryDoubledFiberIndices_image_of_reindex
    coarse indexEquiv tube_eq parent]
  exact
    (Finset.card_image_of_injective _ indexEquiv.injective).symm

/-- Exact tube reindexing preserves the public strict full-fiber count. -/
theorem wz2PaperOrdinaryFullFiberCount_eq_of_reindex
    {delta rho : ℝ}
    {source target : Kakeya.Streamlined.TubeFamily delta}
    (coarse : Kakeya.Streamlined.TubeFamily rho)
    (indexEquiv : Fin target.card ≃ Fin source.card)
    (tube_eq :
      ∀ index : Fin target.card,
        target.tube index = source.tube (indexEquiv index))
    (parent : Fin coarse.card) :
    wz2PaperOrdinaryFullFiberCount target coarse parent =
      wz2PaperOrdinaryFullFiberCount source coarse parent := by
  unfold wz2PaperOrdinaryFullFiberCount
  rw [wz2PaperOrdinaryFullFiber_card_eq_of_reindex
    coarse indexEquiv tube_eq parent]

/-- The strict full-fiber subtypes are equivalent under exact reindexing. -/
noncomputable def wz2PaperOrdinaryFullFiberSubtypeEquiv
    {delta rho : ℝ}
    {source target : Kakeya.Streamlined.TubeFamily delta}
    (coarse : Kakeya.Streamlined.TubeFamily rho)
    (indexEquiv : Fin target.card ≃ Fin source.card)
    (tube_eq :
      ∀ index : Fin target.card,
        target.tube index = source.tube (indexEquiv index))
    (parent : Fin coarse.card) :
    {targetIndex : Fin target.card //
      targetIndex ∈
        wz2PaperOrdinaryFullFiberIndices target coarse parent} ≃
      {sourceIndex : Fin source.card //
        sourceIndex ∈
          wz2PaperOrdinaryFullFiberIndices source coarse parent} :=
  Equiv.subtypeEquiv indexEquiv fun targetIndex => by
    rw [mem_wz2PaperOrdinaryFullFiberIndices_iff,
      mem_wz2PaperOrdinaryFullFiberIndices_iff, tube_eq]

@[simp] theorem wz2PaperOrdinaryFullFiberSubtypeEquiv_apply_val
    {delta rho : ℝ}
    {source target : Kakeya.Streamlined.TubeFamily delta}
    (coarse : Kakeya.Streamlined.TubeFamily rho)
    (indexEquiv : Fin target.card ≃ Fin source.card)
    (tube_eq :
      ∀ index : Fin target.card,
        target.tube index = source.tube (indexEquiv index))
    (parent : Fin coarse.card)
    (targetIndex :
      {targetIndex : Fin target.card //
        targetIndex ∈
          wz2PaperOrdinaryFullFiberIndices target coarse parent}) :
    (wz2PaperOrdinaryFullFiberSubtypeEquiv
      coarse indexEquiv tube_eq parent targetIndex).1 =
        indexEquiv targetIndex.1 := by
  rfl

/-- The induced equivalence between the canonical finite fiber enumerations. -/
noncomputable def wz2PaperPureFullFiberBodyIndexEquiv
    {delta rho : ℝ}
    {source target : Kakeya.Streamlined.TubeFamily delta}
    (coarse : Kakeya.Streamlined.TubeFamily rho)
    (indexEquiv : Fin target.card ≃ Fin source.card)
    (tube_eq :
      ∀ index : Fin target.card,
        target.tube index = source.tube (indexEquiv index))
    (parent : Fin coarse.card) :
    Fin (wz2PaperOrdinaryFullFiberIndices target coarse parent).card ≃
      Fin (wz2PaperOrdinaryFullFiberIndices source coarse parent).card :=
  ((wz2PaperOrdinaryFullFiberIndexEquiv
      (fine := target) (coarse := coarse) parent).trans
    (wz2PaperOrdinaryFullFiberSubtypeEquiv
      coarse indexEquiv tube_eq parent)).trans
    (wz2PaperOrdinaryFullFiberIndexEquiv
      (fine := source) (coarse := coarse) parent).symm

theorem wz2PaperPureFullFiberBodyIndexEquiv_source
    {delta rho : ℝ}
    {source target : Kakeya.Streamlined.TubeFamily delta}
    (coarse : Kakeya.Streamlined.TubeFamily rho)
    (indexEquiv : Fin target.card ≃ Fin source.card)
    (tube_eq :
      ∀ index : Fin target.card,
        target.tube index = source.tube (indexEquiv index))
    (parent : Fin coarse.card)
    (targetIndex :
      Fin (wz2PaperOrdinaryFullFiberIndices
        target coarse parent).card) :
    ((wz2PaperOrdinaryFullFiberIndexEquiv
        (fine := source) (coarse := coarse) parent)
      (wz2PaperPureFullFiberBodyIndexEquiv
        coarse indexEquiv tube_eq parent targetIndex)).1 =
      indexEquiv
        ((wz2PaperOrdinaryFullFiberIndexEquiv
          (fine := target) (coarse := coarse) parent) targetIndex).1 := by
  simp [wz2PaperPureFullFiberBodyIndexEquiv]

/-- Exact fine-family reindexing preserves the pure partitioning cover. -/
theorem WZ2PaperPurePartitioningCover.reindex
    {delta rho : ℝ}
    {source target : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ2PaperPurePartitioningCover source coarse)
    (indexEquiv : Fin target.card ≃ Fin source.card)
    (tube_eq :
      ∀ index : Fin target.card,
        target.tube index = source.tube (indexEquiv index)) :
    WZ2PaperPurePartitioningCover target coarse where
  covers targetIndex := by
    rcases cover.covers (indexEquiv targetIndex) with
      ⟨parent, hparent⟩
    refine ⟨parent, ?_⟩
    rw [mem_wz2PaperOrdinaryFullFiberIndices_iff] at hparent ⊢
    simpa only [tube_eq] using hparent
  doubled_fibers_disjoint first second hne := by
    rw [Finset.disjoint_left]
    intro targetIndex hfirst hsecond
    have hsourceFirst :
        indexEquiv targetIndex ∈
          wz2PaperOrdinaryDilatedFiberIndices
            2 source coarse first := by
      rw [mem_wz2PaperOrdinaryDilatedFiberIndices_iff] at hfirst ⊢
      simpa only [tube_eq] using hfirst
    have hsourceSecond :
        indexEquiv targetIndex ∈
          wz2PaperOrdinaryDilatedFiberIndices
            2 source coarse second := by
      rw [mem_wz2PaperOrdinaryDilatedFiberIndices_iff] at hsecond ⊢
      simpa only [tube_eq] using hsecond
    exact
      Finset.disjoint_left.mp
        (cover.doubled_fibers_disjoint first second hne)
        hsourceFirst hsourceSecond

/-- Exact fine-family reindexing preserves strict full-fiber uniformity. -/
theorem WZ2PaperPureFullFibersAreCUniform.reindex
    {delta rho : ℝ}
    {source target : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {C : ENNReal}
    (uniform : WZ2PaperPureFullFibersAreCUniform source coarse C)
    (indexEquiv : Fin target.card ≃ Fin source.card)
    (tube_eq :
      ∀ index : Fin target.card,
        target.tube index = source.tube (indexEquiv index)) :
    WZ2PaperPureFullFibersAreCUniform target coarse C := by
  intro first second
  rw [wz2PaperOrdinaryFullFiberCount_eq_of_reindex
      coarse indexEquiv tube_eq first,
    wz2PaperOrdinaryFullFiberCount_eq_of_reindex
      coarse indexEquiv tube_eq second]
  exact uniform first second

/--
The canonical actual-John family on a reindexed full fiber is precisely a
finite reindexing of the source canonical family.
-/
theorem wz2PaperPureUnitRescaledFullFiberBodyFamily_eq_reindex
    {delta rho : ℝ}
    {source target : Kakeya.Streamlined.TubeFamily delta}
    (coarse : Kakeya.Streamlined.TubeFamily rho)
    (indexEquiv : Fin target.card ≃ Fin source.card)
    (tube_eq :
      ∀ index : Fin target.card,
        target.tube index = source.tube (indexEquiv index))
    (parent : Fin coarse.card)
    (normalization :
      WZ2PaperAssouadUnitRescalingData (coarse.tube parent)) :
    wz2PaperPureUnitRescaledFullFiberBodyFamily
        (fine := target) (coarse := coarse) parent normalization =
      wz2PaperReindexedBodyFamily
        (wz2PaperPureUnitRescaledFullFiberBodyFamily
          (fine := source) (coarse := coarse) parent normalization)
        (wz2PaperPureFullFiberBodyIndexEquiv
          coarse indexEquiv tube_eq parent) := by
  rw [Kakeya.Streamlined.BodyFamily.mk.injEq]
  constructor
  · rfl
  · apply heq_of_eq
    funext targetIndex
    rw [Kakeya.Streamlined.Body.mk.injEq]
    change
      normalization.map ''
          (target.tube
            ((wz2PaperOrdinaryFullFiberIndexEquiv
              (fine := target) (coarse := coarse) parent)
              targetIndex).1).carrier =
        normalization.map ''
          (source.tube
            ((wz2PaperOrdinaryFullFiberIndexEquiv
              (fine := source) (coarse := coarse) parent)
              (wz2PaperPureFullFiberBodyIndexEquiv
                coarse indexEquiv tube_eq parent targetIndex)).1).carrier
    rw [wz2PaperPureFullFiberBodyIndexEquiv_source,
      ← tube_eq]

/-- Canonical actual-John CWA is invariant under exact finite tube reindexing. -/
noncomputable def WZ2PaperPureUnitRescaledFullFiberData.reindex
    {delta rho : ℝ}
    {source target : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {parent : Fin coarse.card}
    {C : ENNReal}
    (data :
      WZ2PaperPureUnitRescaledFullFiberData
        (fine := source) (coarse := coarse) parent C)
    (indexEquiv : Fin target.card ≃ Fin source.card)
    (tube_eq :
      ∀ index : Fin target.card,
        target.tube index = source.tube (indexEquiv index)) :
    WZ2PaperPureUnitRescaledFullFiberData
      (fine := target) (coarse := coarse) parent C where
  normalization := data.normalization
  convex_wolff := by
    rw [wz2PaperPureUnitRescaledFullFiberBodyFamily_eq_reindex
      coarse indexEquiv tube_eq parent data.normalization]
    exact
      (wz2PaperReindexedBodyFamily.convexWolffBound_iff
        (wz2PaperPureUnitRescaledFullFiberBodyFamily
          (fine := source) (coarse := coarse) parent data.normalization)
        (wz2PaperPureFullFiberBodyIndexEquiv
          coarse indexEquiv tube_eq parent) C).2
        data.convex_wolff

/-- One pure Definition 2.12 scale witness transports by exact reindexing. -/
noncomputable def WZ2PaperPureScaleCoverData.reindex
    {delta rho : ℝ}
    {source target : Kakeya.Streamlined.TubeFamily delta}
    {C : ENNReal}
    (data : WZ2PaperPureScaleCoverData source rho C)
    (indexEquiv : Fin target.card ≃ Fin source.card)
    (tube_eq :
      ∀ index : Fin target.card,
        target.tube index = source.tube (indexEquiv index)) :
    WZ2PaperPureScaleCoverData target rho C where
  delta_pos := data.delta_pos
  rho_pos := data.rho_pos
  coarse := data.coarse
  cover := data.cover.reindex indexEquiv tube_eq
  full_fiber_uniform :=
    data.full_fiber_uniform.reindex indexEquiv tube_eq
  rescaledFiber parent := by
    rcases data.rescaledFiber parent with ⟨fiber⟩
    exact ⟨fiber.reindex indexEquiv tube_eq⟩

/-- A requested nearby-scale witness transports by exact reindexing. -/
noncomputable def WZ2PaperPureNearbyScaleCoverData.reindex
    {delta : ℝ}
    {source target : Kakeya.Streamlined.TubeFamily delta}
    {rho₀ : WZ2PaperRequestedScale delta}
    {C : ENNReal}
    (data : WZ2PaperPureNearbyScaleCoverData source rho₀ C)
    (indexEquiv : Fin target.card ≃ Fin source.card)
    (tube_eq :
      ∀ index : Fin target.card,
        target.tube index = source.tube (indexEquiv index)) :
    WZ2PaperPureNearbyScaleCoverData target rho₀ C where
  rho := data.rho
  requested_le := data.requested_le
  within_factor := data.within_factor
  scaleData := data.scaleData.reindex indexEquiv tube_eq

/-- Ordinary essential distinctness is invariant under exact tube equality. -/
theorem WZ2PaperOrdinaryIsEssentiallyDistinct.reindex
    {delta : ℝ}
    {source target : Kakeya.Streamlined.TubeFamily delta}
    (distinct : WZ2PaperOrdinaryIsEssentiallyDistinct source)
    (indexEquiv : Fin target.card ≃ Fin source.card)
    (tube_eq :
      ∀ index : Fin target.card,
        target.tube index = source.tube (indexEquiv index)) :
    WZ2PaperOrdinaryIsEssentiallyDistinct target := by
  intro first second hne
  have hsourceNe : indexEquiv first ≠ indexEquiv second := by
    intro heq
    exact hne (indexEquiv.injective heq)
  simpa only [tube_eq] using
    distinct (indexEquiv first) (indexEquiv second) hsourceNe

/-- Pure Definition 2.12 CWA at nearby scales transports by exact reindexing. -/
theorem WZ2PaperPureCWAAtNearbyScales.reindex
    {delta : ℝ}
    {source target : Kakeya.Streamlined.TubeFamily delta}
    {C : ENNReal}
    (data : WZ2PaperPureCWAAtNearbyScales source C)
    (indexEquiv : Fin target.card ≃ Fin source.card)
    (tube_eq :
      ∀ index : Fin target.card,
        target.tube index = source.tube (indexEquiv index)) :
    WZ2PaperPureCWAAtNearbyScales target C := by
  refine
    ⟨data.1, data.2.1, data.2.2.1.reindex indexEquiv tube_eq, ?_⟩
  intro rho₀
  rcases data.2.2.2 rho₀ with ⟨nearby⟩
  exact ⟨nearby.reindex indexEquiv tube_eq⟩

end Kakeya.Assouad

end
