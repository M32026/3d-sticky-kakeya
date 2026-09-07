import MyLeanRepo.Kakeya.Assouad.PropStickySelectedScaleCover

/-!
# Restrict nearby paper covers to a selected family

The low-level API below supports assigned factor-two covers as an internal
counting device.  The public nearby-scale adapter at the end starts from a
carrier-faithful literal cover, performs the weighted restriction through its
assigned view, then restores literal carrier uniqueness, doubled-fiber
disjointness, and strict full-fiber provenance.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

namespace WZ2PaperDilatedTubeCover

def hitParentIndices
    {factor delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ2PaperDilatedTubeCover factor fine coarse)
    (selected : Kakeya.Streamlined.TubeSubfamily fine) :
    Finset (Fin coarse.card) :=
  Finset.univ.image fun index =>
    cover.parent (selected.embedding index)

def hitParentSubfamily
    {factor delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ2PaperDilatedTubeCover factor fine coarse)
    (selected : Kakeya.Streamlined.TubeSubfamily fine) :
    Kakeya.Streamlined.TubeSubfamily coarse :=
  Kakeya.Streamlined.TubeSubfamily.fromFinset coarse
    (cover.hitParentIndices selected)

def hitParent
    {factor delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ2PaperDilatedTubeCover factor fine coarse)
    (selected : Kakeya.Streamlined.TubeSubfamily fine) :
    Fin selected.family.card →
      Fin (cover.hitParentSubfamily selected).family.card := fun index =>
  let parents := cover.hitParentIndices selected
  let equivalence : Fin parents.card ≃ parents :=
    (parents.orderIsoOfFin rfl).toEquiv
  equivalence.symm
    ⟨cover.parent (selected.embedding index), by
      apply Finset.mem_image.mpr
      exact ⟨index, Finset.mem_univ _, rfl⟩⟩

@[simp] theorem hitParent_ambient
    {factor delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ2PaperDilatedTubeCover factor fine coarse)
    (selected : Kakeya.Streamlined.TubeSubfamily fine)
    (index : Fin selected.family.card) :
    (cover.hitParentSubfamily selected).embedding
        (cover.hitParent selected index) =
      cover.parent (selected.embedding index) := by
  let parents := cover.hitParentIndices selected
  let equivalence : Fin parents.card ≃ parents :=
    (parents.orderIsoOfFin rfl).toEquiv
  change
    (parents.orderEmbOfFin rfl)
        (equivalence.symm
          ⟨cover.parent (selected.embedding index), _⟩) =
      cover.parent (selected.embedding index)
  exact congrArg Subtype.val
    (equivalence.apply_symm_apply _)

theorem hitParent_surjective
    {factor delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ2PaperDilatedTubeCover factor fine coarse)
    (selected : Kakeya.Streamlined.TubeSubfamily fine) :
    Function.Surjective (cover.hitParent selected) := by
  intro parent
  have hparent :
      (cover.hitParentSubfamily selected).embedding parent ∈
        cover.hitParentIndices selected :=
    Finset.orderEmbOfFin_mem
      (cover.hitParentIndices selected) rfl parent
  rcases Finset.mem_image.mp hparent with
    ⟨source, _hsource, hsourceParent⟩
  refine ⟨source, ?_⟩
  apply (cover.hitParentSubfamily selected).embedding.injective
  rw [cover.hitParent_ambient]
  exact hsourceParent

def restrictToHitParents
    {factor delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ2PaperDilatedTubeCover factor fine coarse)
    (selected : Kakeya.Streamlined.TubeSubfamily fine) :
    WZ2PaperDilatedTubeCover factor
      selected.family (cover.hitParentSubfamily selected).family where
  parent := cover.hitParent selected
  parent_surjective := cover.hitParent_surjective selected
  parent_covers index := by
    rw [selected.tube_eq index,
      (cover.hitParentSubfamily selected).tube_eq,
      cover.hitParent_ambient]
    exact cover.parent_covers (selected.embedding index)

@[simp] theorem restrictToHitParents_fiberIndices
    {factor delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ2PaperDilatedTubeCover factor fine coarse)
    (selected : Kakeya.Streamlined.TubeSubfamily fine)
    (parent :
      Fin (cover.hitParentSubfamily selected).family.card) :
    (cover.restrictToHitParents selected).fiberIndices parent =
      Finset.univ.filter fun source =>
        cover.parent (selected.embedding source) =
          (cover.hitParentSubfamily selected).embedding parent := by
  ext source
  simp only [fiberIndices, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h
    change cover.hitParent selected source = parent at h
    have hambient := congrArg
      (cover.hitParentSubfamily selected).embedding h
    rw [cover.hitParent_ambient] at hambient
    exact hambient
  · intro h
    change cover.hitParent selected source = parent
    apply (cover.hitParentSubfamily selected).embedding.injective
    rw [cover.hitParent_ambient]
    exact h

theorem restrictToHitParents_fiberCount_eq
    {factor delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ2PaperDilatedTubeCover factor fine coarse)
    (selectedIndices : Finset (Fin fine.card))
    (parent :
      Fin (cover.hitParentSubfamily
        (Kakeya.Streamlined.TubeSubfamily.fromFinset
          fine selectedIndices)).family.card) :
    (cover.restrictToHitParents
      (Kakeya.Streamlined.TubeSubfamily.fromFinset
        fine selectedIndices)).fiberCount parent =
      ((selectedIndices.filter fun source =>
        cover.parent source =
          (cover.hitParentSubfamily
            (Kakeya.Streamlined.TubeSubfamily.fromFinset
              fine selectedIndices)).embedding parent).card : ENNReal) := by
  unfold fiberCount
  rw [cover.restrictToHitParents_fiberIndices]
  have hcard :=
    fromFinset_filter_card selectedIndices cover.parent
      ((cover.hitParentSubfamily
        (Kakeya.Streamlined.TubeSubfamily.fromFinset
          fine selectedIndices)).embedding parent)
  exact congrArg (fun value : ℕ => (value : ENNReal)) hcard

theorem restrictToHitParents_fiber_uniform
    {factor delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ2PaperDilatedTubeCover factor fine coarse)
    (selectedIndices : Finset (Fin fine.card))
    (constant : ENNReal)
    (hdegree :
      ∀ first second : Fin coarse.card,
        0 <
            (selectedIndices.filter fun source =>
              cover.parent source = first).card →
          0 <
            (selectedIndices.filter fun source =>
              cover.parent source = second).card →
          (((selectedIndices.filter fun source =>
              cover.parent source = first).card : ℕ) : ENNReal) ≤
            constant *
              (((selectedIndices.filter fun source =>
                cover.parent source = second).card : ℕ) : ENNReal)) :
    ∀ first second :
        Fin (cover.hitParentSubfamily
          (Kakeya.Streamlined.TubeSubfamily.fromFinset
            fine selectedIndices)).family.card,
      (cover.restrictToHitParents
        (Kakeya.Streamlined.TubeSubfamily.fromFinset
          fine selectedIndices)).fiberCount first ≤
        constant *
          (cover.restrictToHitParents
            (Kakeya.Streamlined.TubeSubfamily.fromFinset
              fine selectedIndices)).fiberCount second := by
  intro first second
  rw [cover.restrictToHitParents_fiberCount_eq
      selectedIndices first,
    cover.restrictToHitParents_fiberCount_eq
      selectedIndices second]
  apply hdegree
  · apply Finset.card_pos.mpr
    have hfirst :
        (cover.hitParentSubfamily
          (Kakeya.Streamlined.TubeSubfamily.fromFinset
            fine selectedIndices)).embedding first ∈
          cover.hitParentIndices
            (Kakeya.Streamlined.TubeSubfamily.fromFinset
              fine selectedIndices) :=
      Finset.orderEmbOfFin_mem
        (cover.hitParentIndices
          (Kakeya.Streamlined.TubeSubfamily.fromFinset
            fine selectedIndices)) rfl first
    rcases Finset.mem_image.mp hfirst with
      ⟨source, _hsource, hsourceParent⟩
    refine
      ⟨(Kakeya.Streamlined.TubeSubfamily.fromFinset
          fine selectedIndices).embedding source, ?_⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.orderEmbOfFin_mem selectedIndices rfl source,
        hsourceParent⟩
  · apply Finset.card_pos.mpr
    have hsecond :
        (cover.hitParentSubfamily
          (Kakeya.Streamlined.TubeSubfamily.fromFinset
            fine selectedIndices)).embedding second ∈
          cover.hitParentIndices
            (Kakeya.Streamlined.TubeSubfamily.fromFinset
              fine selectedIndices) :=
      Finset.orderEmbOfFin_mem
        (cover.hitParentIndices
          (Kakeya.Streamlined.TubeSubfamily.fromFinset
            fine selectedIndices)) rfl second
    rcases Finset.mem_image.mp hsecond with
      ⟨source, _hsource, hsourceParent⟩
    refine
      ⟨(Kakeya.Streamlined.TubeSubfamily.fromFinset
          fine selectedIndices).embedding source, ?_⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.orderEmbOfFin_mem selectedIndices rfl source,
        hsourceParent⟩

theorem restrictToHitParents_fiber_uniform_of_subfamily
    {factor delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ2PaperDilatedTubeCover factor fine coarse)
    (selected : Kakeya.Streamlined.TubeSubfamily fine)
    (constant : ENNReal)
    (hdegree :
      ∀ first second : Fin coarse.card,
        0 <
            ((Finset.univ : Finset (Fin selected.family.card)).filter
              fun source =>
                cover.parent (selected.embedding source) = first).card →
          0 <
            ((Finset.univ : Finset (Fin selected.family.card)).filter
              fun source =>
                cover.parent (selected.embedding source) = second).card →
          ((((Finset.univ : Finset (Fin selected.family.card)).filter
              fun source =>
                cover.parent (selected.embedding source) = first).card :
                ℕ) : ENNReal) ≤
            constant *
              ((((Finset.univ : Finset (Fin selected.family.card)).filter
                fun source =>
                  cover.parent (selected.embedding source) = second).card :
                  ℕ) : ENNReal)) :
    ∀ first second :
        Fin (cover.hitParentSubfamily selected).family.card,
      (cover.restrictToHitParents selected).fiberCount first ≤
        constant *
          (cover.restrictToHitParents selected).fiberCount second := by
  intro first second
  unfold fiberCount
  rw [cover.restrictToHitParents_fiberIndices,
    cover.restrictToHitParents_fiberIndices]
  apply hdegree
  · apply Finset.card_pos.mpr
    rcases cover.hitParent_surjective selected first with
      ⟨source, hsource⟩
    refine ⟨source, Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, ?_⟩⟩
    have hambient := congrArg
      (cover.hitParentSubfamily selected).embedding hsource
    rw [cover.hitParent_ambient] at hambient
    exact hambient
  · apply Finset.card_pos.mpr
    rcases cover.hitParent_surjective selected second with
      ⟨source, hsource⟩
    refine ⟨source, Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, ?_⟩⟩
    have hambient := congrArg
      (cover.hitParentSubfamily selected).embedding hsource
    rw [cover.hitParent_ambient] at hambient
    exact hambient

def fiberSubfamily
    {factor delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ2PaperDilatedTubeCover factor fine coarse)
    (parent : Fin coarse.card) :
    Kakeya.Streamlined.TubeSubfamily fine :=
  Kakeya.Streamlined.TubeSubfamily.fromFinset fine
    (cover.fiberIndices parent)

end WZ2PaperDilatedTubeCover

namespace WZ2PaperDilatedUnitRescaledFamilyData

noncomputable def targetEquivFiber
    {factor delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : WZ2PaperDilatedTubeCover factor fine coarse}
    {parent : Fin coarse.card}
    {hrho : 0 < rho}
    {C : ENNReal}
    (data :
      WZ2PaperDilatedUnitRescaledFamilyData
        cover parent hrho C) :
    Fin data.targetFamily.card ≃
      Fin (cover.fiberSubfamily parent).family.card := by
  let indices := cover.fiberIndices parent
  let toFiber :
      Fin data.targetFamily.card → indices := fun target =>
    ⟨data.sourceIndex target, data.sourceIndex_mem target⟩
  let sourceEquiv : Fin data.targetFamily.card ≃ indices :=
    Equiv.ofBijective toFiber
      ⟨(by
          intro first second heq
          apply data.sourceIndex_injective
          exact congrArg Subtype.val heq),
        fun source => by
          rcases data.sourceIndex_surjective
              source.1 source.2 with ⟨target, htarget⟩
          refine ⟨target, Subtype.ext htarget⟩⟩
  exact sourceEquiv.trans
    ((indices.orderIsoOfFin rfl).toEquiv.symm)

@[simp] theorem targetEquivFiber_ambient
    {factor delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : WZ2PaperDilatedTubeCover factor fine coarse}
    {parent : Fin coarse.card}
    {hrho : 0 < rho}
    {C : ENNReal}
    (data :
      WZ2PaperDilatedUnitRescaledFamilyData
        cover parent hrho C)
    (target : Fin data.targetFamily.card) :
    (cover.fiberSubfamily parent).embedding
        (data.targetEquivFiber target) =
      data.sourceIndex target := by
  let indices := cover.fiberIndices parent
  let enumeration : Fin indices.card ≃ indices :=
    (indices.orderIsoOfFin rfl).toEquiv
  let toFiber :
      Fin data.targetFamily.card → indices := fun source =>
    ⟨data.sourceIndex source, data.sourceIndex_mem source⟩
  change
    (indices.orderEmbOfFin rfl)
        (enumeration.symm
          ((Equiv.ofBijective toFiber
            ⟨(by
                intro first second heq
                apply data.sourceIndex_injective
                exact congrArg Subtype.val heq),
              fun source => by
                rcases data.sourceIndex_surjective
                    source.1 source.2 with ⟨candidate, hcandidate⟩
                exact ⟨candidate, Subtype.ext hcandidate⟩⟩) target)) =
      data.sourceIndex target
  exact congrArg Subtype.val
    (enumeration.apply_symm_apply
      ((Equiv.ofBijective toFiber
        ⟨(by
            intro first second heq
            apply data.sourceIndex_injective
            exact congrArg Subtype.val heq),
          fun source => by
            rcases data.sourceIndex_surjective
                source.1 source.2 with ⟨candidate, hcandidate⟩
            exact ⟨candidate, Subtype.ext hcandidate⟩⟩) target))

theorem targetFamily_enncard_eq_fiber
    {factor delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : WZ2PaperDilatedTubeCover factor fine coarse}
    {parent : Fin coarse.card}
    {hrho : 0 < rho}
    {C : ENNReal}
    (data :
      WZ2PaperDilatedUnitRescaledFamilyData
        cover parent hrho C) :
    data.targetFamily.enncard =
      (cover.fiberSubfamily parent).family.enncard := by
  change (data.targetFamily.card : ENNReal) =
    ((cover.fiberSubfamily parent).family.card : ENNReal)
  have hcard :
      data.targetFamily.card =
        (cover.fiberSubfamily parent).family.card := by
    simpa using Fintype.card_congr data.targetEquivFiber
  exact congrArg (fun value : ℕ => (value : ENNReal)) hcard

noncomputable def targetSubfamilyForSource
    {factor delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : WZ2PaperDilatedTubeCover factor fine coarse}
    {parent : Fin coarse.card}
    {hrho : 0 < rho}
    {C : ENNReal}
    (data :
      WZ2PaperDilatedUnitRescaledFamilyData
        cover parent hrho C)
    (sourceSelected :
      Kakeya.Streamlined.TubeSubfamily
        (cover.fiberSubfamily parent).family) :
    Kakeya.Streamlined.TubeSubfamily data.targetFamily where
  family :=
    { card := sourceSelected.family.card
      tube := fun index =>
        data.targetFamily.tube
          (data.targetEquivFiber.symm
            (sourceSelected.embedding index)) }
  embedding :=
    { toFun := fun index =>
        data.targetEquivFiber.symm
          (sourceSelected.embedding index)
      inj' := fun first second heq =>
        sourceSelected.embedding.injective
          (data.targetEquivFiber.symm.injective heq) }
  tube_eq _ := rfl

theorem targetSubfamily_convex_wolff_of_weighted_source_ratio
    {factor delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : WZ2PaperDilatedTubeCover factor fine coarse}
    {parent : Fin coarse.card}
    {hrho : 0 < rho}
    {C weight K : ENNReal}
    (data :
      WZ2PaperDilatedUnitRescaledFamilyData
        cover parent hrho C)
    (sourceSelected :
      Kakeya.Streamlined.TubeSubfamily
        (cover.fiberSubfamily parent).family)
    (hweightZero : weight ≠ 0)
    (hweightTop : weight ≠ ⊤)
    (hsourceRatio :
      weight * (cover.fiberSubfamily parent).family.enncard ≤
        K * sourceSelected.family.enncard) :
    WZ2PaperConvexWolffBound
      (data.targetSubfamilyForSource sourceSelected).family
      ((weight⁻¹ * K) * C) := by
  apply data.convex_wolff.subfamily_of_weighted_cardinality
    (data.targetSubfamilyForSource sourceSelected)
    hweightZero hweightTop
  rw [data.targetFamily_enncard_eq_fiber]
  simpa only [targetSubfamilyForSource,
    Kakeya.Streamlined.TubeFamily.enncard] using hsourceRatio

end WZ2PaperDilatedUnitRescaledFamilyData

namespace WZ2PaperDilatedTubeCover

theorem sum_fiberCount_subfamily_le
    {factor delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ2PaperDilatedTubeCover factor fine coarse)
    (selectedCoarse : Kakeya.Streamlined.TubeSubfamily coarse) :
    (∑ parent : Fin selectedCoarse.family.card,
        cover.fiberCount (selectedCoarse.embedding parent)) ≤
      fine.enncard := by
  let indices : Finset (Fin coarse.card) :=
    Finset.univ.map selectedCoarse.embedding
  have hsum :
      (∑ parent : Fin selectedCoarse.family.card,
          cover.fiberCount (selectedCoarse.embedding parent)) =
        ∑ parent ∈ indices,
          ((cover.fiberIndices parent).card : ENNReal) := by
    unfold fiberCount
    rw [Finset.sum_map]
  rw [hsum]
  have hcount :
      ∑ parent ∈ indices,
          (cover.fiberIndices parent).card ≤ fine.card := by
    change
      ∑ parent ∈ indices,
          (Finset.univ.filter fun source =>
            cover.parent source = parent).card ≤ fine.card
    rw [Finset.sum_card_fiberwise_eq_card_filter]
    simpa only [Fintype.card_fin] using
      Finset.card_le_univ
        (Finset.univ.filter fun source : Fin fine.card =>
          cover.parent source ∈ indices)
  change
    (∑ parent ∈ indices,
        ((cover.fiberIndices parent).card : ENNReal)) ≤
      (fine.card : ENNReal)
  rw [← Nat.cast_sum]
  exact_mod_cast hcount

def selectedFiberInAmbient
    {factor delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ2PaperDilatedTubeCover factor fine coarse)
    (selected : Kakeya.Streamlined.TubeSubfamily fine)
    (parent : Fin (cover.hitParentSubfamily selected).family.card) :
    Kakeya.Streamlined.TubeSubfamily
      (cover.fiberSubfamily
        ((cover.hitParentSubfamily selected).embedding parent)).family := by
  let restricted := cover.restrictToHitParents selected
  let selectedFiber := restricted.fiberSubfamily parent
  let ambientParent :=
    (cover.hitParentSubfamily selected).embedding parent
  let ambientIndices := cover.fiberIndices ambientParent
  let ambientEnumeration : Fin ambientIndices.card ≃ ambientIndices :=
    (ambientIndices.orderIsoOfFin rfl).toEquiv
  let ambientIndex :
      Fin selectedFiber.family.card →
        Fin (cover.fiberSubfamily ambientParent).family.card :=
    fun index =>
      ambientEnumeration.symm
        ⟨selected.embedding (selectedFiber.embedding index), by
          have hselected :
              restricted.parent (selectedFiber.embedding index) =
                parent :=
            (Finset.mem_filter.mp
              (Finset.orderEmbOfFin_mem
                (restricted.fiberIndices parent) rfl index)).2
          change
            cover.hitParent selected (selectedFiber.embedding index) =
              parent at hselected
          have hambient :=
            congrArg (cover.hitParentSubfamily selected).embedding hselected
          rw [cover.hitParent_ambient] at hambient
          exact Finset.mem_filter.mpr
            ⟨Finset.mem_univ _, hambient⟩⟩
  refine
    { family := selectedFiber.family
      embedding :=
        { toFun := ambientIndex
          inj' := ?_ }
      tube_eq := ?_ }
  · intro first second heq
    apply selectedFiber.embedding.injective
    apply selected.embedding.injective
    have hvalues := congrArg ambientEnumeration heq
    have hfirst :=
      ambientEnumeration.apply_symm_apply
        ⟨selected.embedding (selectedFiber.embedding first), by
          have hselected :
              restricted.parent (selectedFiber.embedding first) =
                parent :=
            (Finset.mem_filter.mp
              (Finset.orderEmbOfFin_mem
                (restricted.fiberIndices parent) rfl first)).2
          change
            cover.hitParent selected (selectedFiber.embedding first) =
              parent at hselected
          have hambient :=
            congrArg (cover.hitParentSubfamily selected).embedding hselected
          rw [cover.hitParent_ambient] at hambient
          exact Finset.mem_filter.mpr
            ⟨Finset.mem_univ _, hambient⟩⟩
    have hsecond :=
      ambientEnumeration.apply_symm_apply
        ⟨selected.embedding (selectedFiber.embedding second), by
          have hselected :
              restricted.parent (selectedFiber.embedding second) =
                parent :=
            (Finset.mem_filter.mp
              (Finset.orderEmbOfFin_mem
                (restricted.fiberIndices parent) rfl second)).2
          change
            cover.hitParent selected (selectedFiber.embedding second) =
              parent at hselected
          have hambient :=
            congrArg (cover.hitParentSubfamily selected).embedding hselected
          rw [cover.hitParent_ambient] at hambient
          exact Finset.mem_filter.mpr
            ⟨Finset.mem_univ _, hambient⟩⟩
    rw [hfirst, hsecond] at hvalues
    exact congrArg Subtype.val hvalues
  · intro index
    rw [selectedFiber.tube_eq index,
      selected.tube_eq (selectedFiber.embedding index),
      (cover.fiberSubfamily ambientParent).tube_eq]
    change
      fine.tube
          (selected.embedding (selectedFiber.embedding index)) =
        fine.tube
          ((cover.fiberSubfamily ambientParent).embedding
            (ambientIndex index))
    have hambient :
        (cover.fiberSubfamily ambientParent).embedding
            (ambientIndex index) =
          selected.embedding (selectedFiber.embedding index) := by
      change
        (ambientIndices.orderEmbOfFin rfl)
            (ambientEnumeration.symm
              ⟨selected.embedding (selectedFiber.embedding index), _⟩) =
          selected.embedding (selectedFiber.embedding index)
      exact congrArg Subtype.val
        (ambientEnumeration.apply_symm_apply _)
    rw [hambient]

@[simp] theorem selectedFiberInAmbient_family
    {factor delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ2PaperDilatedTubeCover factor fine coarse)
    (selected : Kakeya.Streamlined.TubeSubfamily fine)
    (parent : Fin (cover.hitParentSubfamily selected).family.card) :
    (cover.selectedFiberInAmbient selected parent).family =
      ((cover.restrictToHitParents selected).fiberSubfamily
        parent).family :=
  rfl

@[simp] theorem selectedFiberInAmbient_ambient
    {factor delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ2PaperDilatedTubeCover factor fine coarse)
    (selected : Kakeya.Streamlined.TubeSubfamily fine)
    (parent : Fin (cover.hitParentSubfamily selected).family.card)
    (index :
      Fin ((cover.restrictToHitParents selected).fiberSubfamily
        parent).family.card) :
    (cover.fiberSubfamily
        ((cover.hitParentSubfamily selected).embedding parent)).embedding
        ((cover.selectedFiberInAmbient selected parent).embedding index) =
      selected.embedding
        (((cover.restrictToHitParents selected).fiberSubfamily
          parent).embedding index) := by
  let ambientParent :=
    (cover.hitParentSubfamily selected).embedding parent
  let ambientIndices := cover.fiberIndices ambientParent
  let ambientEnumeration : Fin ambientIndices.card ≃ ambientIndices :=
    (ambientIndices.orderIsoOfFin rfl).toEquiv
  change
    (ambientIndices.orderEmbOfFin rfl)
        (ambientEnumeration.symm
          ⟨selected.embedding
              (((cover.restrictToHitParents selected).fiberSubfamily
                parent).embedding index), _⟩) =
      selected.embedding
        (((cover.restrictToHitParents selected).fiberSubfamily
          parent).embedding index)
  exact congrArg Subtype.val
    (ambientEnumeration.apply_symm_apply _)

end WZ2PaperDilatedTubeCover

namespace WZ2PaperDilatedUnitRescaledFamilyData

def restrictToSelectedHitFiber
    {factor delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : WZ2PaperDilatedTubeCover factor fine coarse}
    {ambientParent : Fin coarse.card}
    {hrho : 0 < rho}
    {C weight K : ENNReal}
    (data :
      WZ2PaperDilatedUnitRescaledFamilyData
        cover ambientParent hrho C)
    (selected : Kakeya.Streamlined.TubeSubfamily fine)
    (parent : Fin (cover.hitParentSubfamily selected).family.card)
    (hparent :
      (cover.hitParentSubfamily selected).embedding parent =
        ambientParent)
    (hweightZero : weight ≠ 0)
    (hweightTop : weight ≠ ⊤)
    (hcardinality :
      weight *
          (cover.fiberSubfamily ambientParent).family.enncard ≤
        K *
          ((cover.restrictToHitParents selected).fiberSubfamily
            parent).family.enncard) :
    WZ2PaperDilatedUnitRescaledFamilyData
      (cover.restrictToHitParents selected)
      parent hrho ((weight⁻¹ * K) * C) := by
  subst ambientParent
  let sourceSelected := cover.selectedFiberInAmbient selected parent
  let targetSelected := data.targetSubfamilyForSource sourceSelected
  have htargetCWA :
      WZ2PaperConvexWolffBound targetSelected.family
        ((weight⁻¹ * K) * C) := by
    apply data.targetSubfamily_convex_wolff_of_weighted_source_ratio
      sourceSelected hweightZero hweightTop
    change
      weight *
          (cover.fiberSubfamily
            ((cover.hitParentSubfamily selected).embedding parent)).family.enncard ≤
        K *
          ((cover.restrictToHitParents selected).fiberSubfamily
            parent).family.enncard
    exact hcardinality
  refine
    { targetFamily := targetSelected.family
      sourceIndex := fun index =>
        ((cover.restrictToHitParents selected).fiberSubfamily
          parent).embedding index
      sourceIndex_mem := ?_
      sourceIndex_injective :=
        ((cover.restrictToHitParents selected).fiberSubfamily
          parent).embedding.injective
      sourceIndex_surjective := ?_
      target_axis := ?_
      target_line_class :=
        data.target_line_class.subfamily targetSelected
      convex_wolff := htargetCWA }
  · intro index
    exact Finset.orderEmbOfFin_mem
      ((cover.restrictToHitParents selected).fiberIndices parent)
      rfl index
  · intro source hsource
    let indices :=
      (cover.restrictToHitParents selected).fiberIndices parent
    let enumeration : Fin indices.card ≃ indices :=
      (indices.orderIsoOfFin rfl).toEquiv
    let index : Fin indices.card :=
      enumeration.symm ⟨source, hsource⟩
    exact ⟨index, congrArg Subtype.val
      (enumeration.apply_symm_apply ⟨source, hsource⟩)⟩
  · intro index
    let sourceIndex : Fin sourceSelected.family.card :=
      ⟨index.1, by
        simpa [targetSelected, targetSubfamilyForSource] using index.2⟩
    let restrictedIndex :
        Fin ((cover.restrictToHitParents selected).fiberSubfamily
          parent).family.card :=
      ⟨sourceIndex.1, by
        simpa only [sourceSelected,
          WZ2PaperDilatedTubeCover.selectedFiberInAmbient_family] using
          sourceIndex.2⟩
    have haxis :=
      data.target_axis
        ((data.targetEquivFiber).symm
          (sourceSelected.embedding sourceIndex))
    calc
      tubeAxisLine (targetSelected.family.tube index) =
          tubeAxisLine
            (data.targetFamily.tube
              ((data.targetEquivFiber).symm
                (sourceSelected.embedding sourceIndex))) := by
        rfl
      _ =
          wz1PaperUnitRescalingMap
              (coarse.tube
                ((cover.hitParentSubfamily selected).embedding parent))
              hrho ''
            tubeAxisLine
              (fine.tube
                (data.sourceIndex
                  ((data.targetEquivFiber).symm
                    (sourceSelected.embedding sourceIndex)))) :=
        haxis
      _ =
          wz1PaperUnitRescalingMap
              ((cover.hitParentSubfamily selected).family.tube parent)
              hrho ''
            tubeAxisLine
              (selected.family.tube
                (((cover.restrictToHitParents selected).fiberSubfamily
                  parent).embedding restrictedIndex)) := by
        rw [(cover.hitParentSubfamily selected).tube_eq]
        congr 1
        have hambient :=
          data.targetEquivFiber_ambient
            ((data.targetEquivFiber).symm
              (sourceSelected.embedding sourceIndex))
        rw [data.targetEquivFiber.apply_symm_apply] at hambient
        rw [← hambient]
        calc
          tubeAxisLine
              (fine.tube
                ((cover.fiberSubfamily
                    ((cover.hitParentSubfamily selected).embedding parent)).embedding
                  (sourceSelected.embedding sourceIndex))) =
              tubeAxisLine
                ((cover.fiberSubfamily
                    ((cover.hitParentSubfamily selected).embedding parent)).family.tube
                  (sourceSelected.embedding sourceIndex)) := by
            rw [(cover.fiberSubfamily
              ((cover.hitParentSubfamily selected).embedding parent)).tube_eq]
          _ =
              tubeAxisLine (sourceSelected.family.tube sourceIndex) := by
            rw [sourceSelected.tube_eq sourceIndex]
          _ =
              tubeAxisLine
                (((cover.restrictToHitParents selected).fiberSubfamily
                  parent).family.tube restrictedIndex) := by
            rfl
          _ =
              tubeAxisLine
                (selected.family.tube
                  (((cover.restrictToHitParents selected).fiberSubfamily
                    parent).embedding restrictedIndex)) := by
            rw [((cover.restrictToHitParents selected).fiberSubfamily
              parent).tube_eq]

end WZ2PaperDilatedUnitRescaledFamilyData

def WZ2PaperDilatedScaleCoverData.restrictToSelectedHitParents
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {rho : ℝ}
    {ambientConstant weight selectedConstant retentionConstant : ENNReal}
    (data :
      WZ2PaperDilatedScaleCoverData family rho ambientConstant)
    (selected : Kakeya.Streamlined.TubeSubfamily family)
    (hweightZero : weight ≠ 0)
    (hweightTop : weight ≠ ⊤)
    (hglobalRetention :
      weight * family.enncard ≤
        retentionConstant * selected.family.enncard)
    (hselectedUniform :
      ∀ first second :
          Fin (data.cover.hitParentSubfamily selected).family.card,
        (data.cover.restrictToHitParents selected).fiberCount first ≤
          selectedConstant *
            (data.cover.restrictToHitParents selected).fiberCount second) :
    let fiberRatioConstant :=
      ambientConstant * retentionConstant * selectedConstant
    let rescaledConstant :=
      (weight⁻¹ * fiberRatioConstant) * ambientConstant
    WZ2PaperDilatedScaleCoverData selected.family rho
      (max selectedConstant rescaledConstant) := by
  let hitCoarse := data.cover.hitParentSubfamily selected
  let restrictedCover := data.cover.restrictToHitParents selected
  let fiberRatioConstant :=
    ambientConstant * retentionConstant * selectedConstant
  let rescaledConstant :=
    (weight⁻¹ * fiberRatioConstant) * ambientConstant
  have hcoarseLine :
      WZ1PaperIsLineClass hitCoarse.family :=
    data.coarse_line_class.subfamily hitCoarse
  have hcoarseDistinct :
      WZ1PaperIsEssentiallyDistinct hitCoarse.family :=
    data.coarse_essentially_distinct.subfamily hitCoarse
  have hambientSumLe :
      (∑ parent : Fin hitCoarse.family.card,
          data.cover.fiberCount (hitCoarse.embedding parent)) ≤
        family.enncard :=
    data.cover.sum_fiberCount_subfamily_le hitCoarse
  have hselectedSum :
      (∑ parent : Fin hitCoarse.family.card,
          restrictedCover.fiberCount parent) =
        selected.family.enncard := by
    unfold WZ2PaperDilatedTubeCover.fiberCount
    change
      (∑ parent : Fin hitCoarse.family.card,
          (((Finset.univ : Finset (Fin selected.family.card)).filter
            fun source => restrictedCover.parent source = parent).card :
              ENNReal)) =
        (selected.family.card : ENNReal)
    rw [← Nat.cast_sum]
    exact_mod_cast
      ((Finset.sum_card_fiberwise_eq_card_filter
        (Finset.univ : Finset (Fin selected.family.card))
        (Finset.univ : Finset (Fin hitCoarse.family.card))
        restrictedCover.parent).trans (by simp))
  refine
    { rho_pos := data.rho_pos
      coarse := hitCoarse.family
      cover := restrictedCover
      coarse_line_class := hcoarseLine
      coarse_essentially_distinct := hcoarseDistinct
      assigned_fiber_uniform := ?_
      rescaledFiber := ?_ }
  · intro first second
    exact (hselectedUniform first second).trans (by
      gcongr
      exact le_max_left _ _)
  · intro parent
    let ambientParent := hitCoarse.embedding parent
    rcases data.rescaledFiber ambientParent with ⟨ambientFiber⟩
    have hweightedFiber :
        weight * data.cover.fiberCount ambientParent ≤
          fiberRatioConstant * restrictedCover.fiberCount parent := by
      let ambientFiberCount : Fin hitCoarse.family.card → ENNReal :=
        fun index => data.cover.fiberCount (hitCoarse.embedding index)
      let selectedFiberCount : Fin hitCoarse.family.card → ENNReal :=
        fun index => restrictedCover.fiberCount index
      have hambientUniformHit :
          ∀ first second,
            ambientFiberCount first ≤
              ambientConstant * ambientFiberCount second := by
        intro first second
        exact data.assigned_fiber_uniform
          (hitCoarse.embedding first) (hitCoarse.embedding second)
      have hretainedSums :
          weight * (∑ index, ambientFiberCount index) ≤
            retentionConstant * ∑ index, selectedFiberCount index := by
        calc
          weight * (∑ index, ambientFiberCount index) ≤
              weight * family.enncard := by
            gcongr
          _ ≤ retentionConstant * selected.family.enncard :=
            hglobalRetention
          _ = retentionConstant *
              ∑ index, selectedFiberCount index := by
            rw [hselectedSum]
      letI : Nonempty (Fin hitCoarse.family.card) := ⟨parent⟩
      have hratio :=
        finite_uniform_weighted_fiber_ratio
          ambientFiberCount selectedFiberCount
          weight ambientConstant selectedConstant retentionConstant
          hambientUniformHit hselectedUniform hretainedSums parent
      simpa [fiberRatioConstant, ambientFiberCount,
        selectedFiberCount, ambientParent] using hratio
    have hfiberCardinality :
        weight *
            (data.cover.fiberSubfamily ambientParent).family.enncard ≤
          fiberRatioConstant *
            (restrictedCover.fiberSubfamily parent).family.enncard := by
      change
        weight * (data.cover.fiberCount ambientParent) ≤
          fiberRatioConstant * restrictedCover.fiberCount parent
      exact hweightedFiber
    let restrictedFiber :
        WZ2PaperDilatedUnitRescaledFamilyData
          restrictedCover parent data.rho_pos rescaledConstant :=
      ambientFiber.restrictToSelectedHitFiber
        selected parent rfl hweightZero hweightTop
        hfiberCardinality
    exact
      ⟨restrictedFiber.mono
        (le_max_right selectedConstant rescaledConstant)⟩

/--
Restrict a carrier-faithful literal scale witness to selected fine tubes and
the coarse parents they still hit.

The weighted analytic restriction is performed through the auxiliary
assigned cover.  The restricted parent map is then repackaged with the
inherited literal carrier uniqueness and doubled-fiber disjointness, and the
assigned restricted fibers are identified with the resulting strict full
fibers.
-/
def WZ2PaperLiteralScaleCoverData.restrictToSelectedHitParents
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {rho : ℝ}
    {ambientConstant weight selectedConstant retentionConstant : ENNReal}
    (data :
      WZ2PaperLiteralScaleCoverData family rho ambientConstant)
    (selected : Kakeya.Streamlined.TubeSubfamily family)
    (hweightZero : weight ≠ 0)
    (hweightTop : weight ≠ ⊤)
    (hglobalRetention :
      weight * family.enncard ≤
        retentionConstant * selected.family.enncard)
    (hselectedUniform :
      ∀ first second :
          Fin (data.cover.toWZ2PaperDilatedTubeCover
            |>.hitParentSubfamily selected).family.card,
        (data.cover.toWZ2PaperDilatedTubeCover
            |>.restrictToHitParents selected).fiberCount first ≤
          selectedConstant *
            (data.cover.toWZ2PaperDilatedTubeCover
              |>.restrictToHitParents selected).fiberCount second) :
    let fiberRatioConstant :=
      ambientConstant * retentionConstant * selectedConstant
    let rescaledConstant :=
      (weight⁻¹ * fiberRatioConstant) * ambientConstant
    WZ2PaperLiteralScaleCoverData selected.family rho
      (max selectedConstant rescaledConstant) := by
  let assignedData :
      WZ2PaperDilatedScaleCoverData family rho ambientConstant :=
    { rho_pos := data.rho_pos
      coarse := data.coarse
      cover := data.cover.toWZ2PaperDilatedTubeCover
      coarse_line_class := data.coarse_line_class
      coarse_essentially_distinct := data.coarse_essentially_distinct
      assigned_fiber_uniform := by
        intro first second
        have h := data.full_fiber_uniform first second
        rw [data.cover.literalFullFiberCount_eq first,
          data.cover.literalFullFiberCount_eq second] at h
        exact h
      rescaledFiber := by
        intro parent
        rcases data.rescaledFiber parent with ⟨fiber⟩
        refine ⟨{
          targetFamily := fiber.targetFamily
          sourceIndex := fiber.sourceIndex
          sourceIndex_mem := ?_
          sourceIndex_injective := fiber.sourceIndex_injective
          sourceIndex_surjective := ?_
          target_axis := fiber.target_axis
          target_line_class := fiber.target_line_class
          convex_wolff := fiber.convex_wolff }⟩
        · intro target
          have h := fiber.sourceIndex_mem target
          rw [data.cover.literalFullFiberIndices_eq parent] at h
          exact h
        · intro source hsource
          have hsourceLiteral :
              source ∈ wz2PaperLiteralFullFiberIndices
                family data.coarse parent := by
            rw [data.cover.literalFullFiberIndices_eq parent]
            exact hsource
          exact fiber.sourceIndex_surjective source hsourceLiteral }
  let assignedRestricted :=
    assignedData.restrictToSelectedHitParents
      selected hweightZero hweightTop
      hglobalRetention hselectedUniform
  let ambientAssigned := data.cover.toWZ2PaperDilatedTubeCover
  let hitCoarse := ambientAssigned.hitParentSubfamily selected
  let restrictedAssigned := ambientAssigned.restrictToHitParents selected
  let literalCover :
      WZ2PaperLiteralDilatedPartitioningCover
        selected.family hitCoarse.family :=
    { toWZ2PaperDilatedTubeCover := restrictedAssigned
      parent_carrier_covers := by
        intro source
        have hparent :
            hitCoarse.embedding (restrictedAssigned.parent source) =
              data.cover.parent (selected.embedding source) := by
          change
            (ambientAssigned.hitParentSubfamily selected).embedding
                (ambientAssigned.hitParent selected source) =
              ambientAssigned.parent (selected.embedding source)
          exact ambientAssigned.hitParent_ambient selected source
        rw [selected.tube_eq source, hitCoarse.tube_eq, hparent]
        exact data.cover.parent_carrier_covers
          (selected.embedding source)
      literal_parent_unique := by
        intro source candidate hcovered
        apply hitCoarse.embedding.injective
        have hcoveredAmbient :
            WZ2PaperTubeCarrierCovers
              (family.tube (selected.embedding source))
              (data.coarse.tube (hitCoarse.embedding candidate)) := by
          rwa [← selected.tube_eq source,
            ← hitCoarse.tube_eq candidate]
        have hcandidate :
            hitCoarse.embedding candidate =
              data.cover.parent (selected.embedding source) :=
          data.cover.literal_parent_unique
            (selected.embedding source)
            (hitCoarse.embedding candidate)
            hcoveredAmbient
        have hparent :
            hitCoarse.embedding (restrictedAssigned.parent source) =
              data.cover.parent (selected.embedding source) := by
          change
            (ambientAssigned.hitParentSubfamily selected).embedding
                (ambientAssigned.hitParent selected source) =
              ambientAssigned.parent (selected.embedding source)
          exact ambientAssigned.hitParent_ambient selected source
        exact hcandidate.trans hparent.symm
      literal_doubled_fibers_disjoint := by
        intro first second hne
        rw [Finset.disjoint_left]
        intro source hfirst hsecond
        have hambientNe :
            hitCoarse.embedding first ≠ hitCoarse.embedding second :=
          hitCoarse.embedding.injective.ne hne
        have hambientFirst :
            selected.embedding source ∈
              wz2PaperLiteralDoubledFiberIndices
                family data.coarse (hitCoarse.embedding first) := by
          simpa [wz2PaperLiteralDoubledFiberIndices,
            selected.tube_eq source, hitCoarse.tube_eq first] using hfirst
        have hambientSecond :
            selected.embedding source ∈
              wz2PaperLiteralDoubledFiberIndices
                family data.coarse (hitCoarse.embedding second) := by
          simpa [wz2PaperLiteralDoubledFiberIndices,
            selected.tube_eq source, hitCoarse.tube_eq second] using hsecond
        exact
          ((Finset.disjoint_left.mp
              (data.cover.literal_doubled_fibers_disjoint
                (hitCoarse.embedding first)
                (hitCoarse.embedding second)
                hambientNe))
            hambientFirst) hambientSecond }
  refine
    { rho_pos := assignedRestricted.rho_pos
      coarse := hitCoarse.family
      cover := literalCover
      coarse_line_class := assignedRestricted.coarse_line_class
      coarse_essentially_distinct :=
        assignedRestricted.coarse_essentially_distinct
      full_fiber_uniform := ?_
      rescaledFiber := ?_ }
  · intro first second
    rw [literalCover.literalFullFiberCount_eq first,
      literalCover.literalFullFiberCount_eq second]
    exact assignedRestricted.assigned_fiber_uniform first second
  · intro parent
    rcases assignedRestricted.rescaledFiber parent with ⟨fiber⟩
    refine ⟨{
      targetFamily := fiber.targetFamily
      sourceIndex := fiber.sourceIndex
      sourceIndex_mem := ?_
      sourceIndex_injective := fiber.sourceIndex_injective
      sourceIndex_surjective := ?_
      target_axis := fiber.target_axis
      target_line_class := fiber.target_line_class
      convex_wolff := fiber.convex_wolff }⟩
    · intro target
      rw [literalCover.literalFullFiberIndices_eq parent]
      exact fiber.sourceIndex_mem target
    · intro source hsource
      rw [literalCover.literalFullFiberIndices_eq parent] at hsource
      exact fiber.sourceIndex_surjective source hsource

end Kakeya.Assouad

end
