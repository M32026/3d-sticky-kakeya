import MyLeanRepo.Kakeya.Assouad.PropStickyFiniteRegularizedCover
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperPerTubePruning

/-!
# Finite regularized paper refinement

Combine the low-per-tube-mass pruning with simultaneous regularization of a
finite list of parent maps.  The output retains explicit shaded mass,
per-tube mass, global indexed cardinality, and parent-fiber degree control.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

theorem fromFinset_filter_card
    {cardinality : ℕ}
    (selected : Finset (Fin cardinality))
    {Value : Type*} [DecidableEq Value]
    (coordinate : Fin cardinality → Value)
    (value : Value) :
    ((Finset.univ : Finset (Fin selected.card)).filter fun index =>
        coordinate (selected.orderEmbOfFin rfl index) = value).card =
      (selected.filter fun index =>
        coordinate index = value).card := by
  apply Finset.card_bij
      (fun index _ => selected.orderEmbOfFin rfl index)
  · intro index hindex
    apply Finset.mem_filter.mpr
    exact
      ⟨Finset.orderEmbOfFin_mem selected rfl index,
        (Finset.mem_filter.mp hindex).2⟩
  · intro first _ second _ heq
    exact (selected.orderEmbOfFin rfl).injective heq
  · intro ambient hambientMem
    have hambientSelected : ambient ∈ selected :=
      (Finset.mem_filter.mp hambientMem).1
    let index : Fin selected.card :=
      (selected.orderIsoOfFin rfl).symm
        ⟨ambient, hambientSelected⟩
    refine ⟨index, ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      have hindexAmbient :
          selected.orderEmbOfFin rfl index = ambient := by
        exact congrArg Subtype.val
          ((selected.orderIsoOfFin rfl).apply_symm_apply
            ⟨ambient, hambientSelected⟩)
      rw [hindexAmbient]
      exact (Finset.mem_filter.mp hambientMem).2
    · exact congrArg Subtype.val
        ((selected.orderIsoOfFin rfl).apply_symm_apply
          ⟨ambient, hambientSelected⟩)

structure WZ2PaperFiniteRegularizedRefinementData
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (shading : WZ1PaperTubeShading family)
    (density : ENNReal)
    (scaleCount : ℕ)
    (Parent : Fin scaleCount → Type _)
    [∀ scale, Fintype (Parent scale)]
    [∀ scale, DecidableEq (Parent scale)]
    (parent : ∀ scale, Fin family.card → Parent scale) where
  selected : Kakeya.Streamlined.TubeSubfamily family
  refined : WZ1PaperTubeShading selected.family
  refined_cubical : WZ1PaperIsCubicalShading refined
  subshading :
    ∀ index,
      refined.carrier index ⊆
        shading.carrier (selected.embedding index)
  regularizationLoss : ENNReal
  regularizationLoss_eq :
    regularizationLoss =
      (8 : ENNReal) *
        (Nat.log 2 (2 * family.card) + 1 : ENNReal) ^
          (scaleCount + 1)
  retained_mass :
    shading.mass ≤
      2 * regularizationLoss * refined.mass
  per_tube :
    ∀ index,
      (1 / 2 : ENNReal) * density *
          Kakeya.realRpowENN delta 2 ≤
        volume (refined.carrier index)
  cardinality_retention :
    (1 / 2 : ENNReal) * density * family.enncard ≤
      (2 * regularizationLoss) *
          (55296 * Kakeya.deltaTubeVolume 1) *
        selected.family.enncard
  degree_uniform :
    ∀ scale,
      ∀ first second : Parent scale,
        0 <
            (Finset.univ.filter fun index =>
              parent scale (selected.embedding index) = first).card →
          0 <
            (Finset.univ.filter fun index =>
              parent scale (selected.embedding index) = second).card →
          (((Finset.univ.filter fun index =>
              parent scale (selected.embedding index) = first).card : ℕ) :
                ENNReal) ≤
            (16 * (scaleCount : ENNReal) *
                (Nat.log 2 (2 * family.card) + 1 : ENNReal) ^
                  scaleCount) *
              (((Finset.univ.filter fun index =>
                parent scale (selected.embedding index) = second).card : ℕ) :
                  ENNReal)

theorem wz2PaperFiniteRegularizedRefinement
    {delta : ℝ}
    (hdelta : 0 < delta)
    (hdeltaSmall : delta ≤ 1 / 24)
    {family : Kakeya.Streamlined.TubeFamily delta}
    (hline : WZ1PaperIsLineClass family)
    (shading : WZ1PaperTubeShading family)
    (hcubical : WZ1PaperIsCubicalShading shading)
    (density : ENNReal)
    (hdense :
      density * family.enncard *
          Kakeya.realRpowENN delta 2 ≤
        shading.mass)
    (scaleCount : ℕ)
    (Parent : Fin scaleCount → Type)
    [∀ scale, Fintype (Parent scale)]
    [∀ scale, DecidableEq (Parent scale)]
    (parent : ∀ scale, Fin family.card → Parent scale) :
    Nonempty
      (WZ2PaperFiniteRegularizedRefinementData
        shading density scaleCount Parent parent) := by
  rcases wz2PaperPerTubePruning shading density hdense with
    ⟨pruned⟩
  let prunedSubfamily :=
    Kakeya.Streamlined.TubeSubfamily.fromFinset
      family pruned.selected
  let prunedShading :=
    restrictPaperShading prunedSubfamily shading
  let prunedParent :
      ∀ scale, Fin prunedSubfamily.family.card → Parent scale :=
    fun scale index =>
      parent scale (prunedSubfamily.embedding index)
  rcases
      wz2_prop_sticky_finite_parent_regularization
        prunedShading scaleCount Parent prunedParent
    with ⟨regularized⟩
  let innerSelected :=
    Kakeya.Streamlined.TubeSubfamily.fromFinset
      prunedSubfamily.family regularized.selected
  let selected := prunedSubfamily.comp innerSelected
  let refined :=
    restrictPaperShading innerSelected prunedShading
  let regularizationLoss : ENNReal :=
    (8 : ENNReal) *
      (Nat.log 2 (2 * prunedSubfamily.family.card) + 1 : ENNReal) ^
        (scaleCount + 1)
  have hregularizationLoss :
      regularizationLoss ≤
        (8 : ENNReal) *
          (Nat.log 2 (2 * family.card) + 1 : ENNReal) ^
            (scaleCount + 1) := by
    have hcard :
        prunedSubfamily.family.card ≤ family.card := by
      change pruned.selected.card ≤ family.card
      simpa only [Fintype.card_fin] using
        Finset.card_le_univ pruned.selected
    have hlog :
        Nat.log 2 (2 * prunedSubfamily.family.card) + 1 ≤
          Nat.log 2 (2 * family.card) + 1 := by
      gcongr
    dsimp only [regularizationLoss]
    gcongr
  let outputLoss : ENNReal :=
    (8 : ENNReal) *
      (Nat.log 2 (2 * family.card) + 1 : ENNReal) ^
        (scaleCount + 1)
  have hregularizedMass :
      prunedShading.mass ≤
        outputLoss * refined.mass := by
    calc
      prunedShading.mass ≤
          regularizationLoss * refined.mass := by
        simpa [regularizationLoss, refined, prunedShading,
          prunedSubfamily] using regularized.retained_mass
      _ ≤ outputLoss * refined.mass := by
        gcongr
  have hretained :
      shading.mass ≤ 2 * outputLoss * refined.mass := by
    calc
      shading.mass ≤ 2 * prunedShading.mass := by
        simpa [prunedShading, prunedSubfamily] using
          pruned.retained_mass
      _ ≤ 2 * (outputLoss * refined.mass) := by
        gcongr
      _ = 2 * outputLoss * refined.mass := by ring
  have hperTube :
      ∀ index,
        (1 / 2 : ENNReal) * density *
            Kakeya.realRpowENN delta 2 ≤
          volume (refined.carrier index) := by
    intro index
    exact pruned.per_tube (innerSelected.embedding index)
  have hcardinality :
      (1 / 2 : ENNReal) * density * family.enncard ≤
        (2 * outputLoss) *
            (55296 * Kakeya.deltaTubeVolume 1) *
          selected.family.enncard := by
    -- The exact selected index set is the image of the composed embedding.
    let selectedIndices : Finset (Fin family.card) :=
      Finset.univ.map selected.embedding
    have hselectedShading :
        (restrictPaperShading
          (Kakeya.Streamlined.TubeSubfamily.fromFinset
            family selectedIndices)
          shading).mass = refined.mass := by
      rw [restrictPaperShading_fromFinset_mass]
      change
        (∑ index ∈ selectedIndices,
          volume (shading.carrier index)) =
          ∑ index : Fin innerSelected.family.card,
            volume (refined.carrier index)
      rw [Finset.sum_map]
      rfl
    have hselectedFamilyCard :
        (Kakeya.Streamlined.TubeSubfamily.fromFinset
          family selectedIndices).family.enncard =
          selected.family.enncard := by
      change
        (selectedIndices.card : ENNReal) =
          (selected.family.card : ENNReal)
      have hcard :
          selectedIndices.card = selected.family.card := by
        dsimp only [selectedIndices]
        rw [Finset.card_map]
        simp
      exact congrArg (fun value : ℕ => (value : ENNReal)) hcard
    have hweightedFinal :=
      wz2PaperWeightedCardinality_retained_from_mass
        hdelta hdeltaSmall hline shading selectedIndices
        ((1 / 2 : ENNReal) * density)
        (2 * outputLoss)
        (by
          have hhalfDensity :
              (1 / 2 : ENNReal) * density ≤ density := by
            calc
              (1 / 2 : ENNReal) * density ≤
                  1 * density := by
                gcongr
                norm_num
              _ = density := one_mul density
          calc
            ((1 / 2 : ENNReal) * density) *
                  family.enncard *
                  Kakeya.realRpowENN delta 2
                ≤ density * family.enncard *
                    Kakeya.realRpowENN delta 2 := by
              exact mul_le_mul_right'
                (mul_le_mul_right' hhalfDensity family.enncard)
                (Kakeya.realRpowENN delta 2)
            _ ≤ shading.mass := hdense)
        (by simpa [hselectedShading] using hretained)
    simpa [hselectedFamilyCard] using hweightedFinal
  refine ⟨{
    selected := selected
    refined := refined
    refined_cubical :=
      restrictPaperShading_cubical innerSelected
        (restrictPaperShading_cubical prunedSubfamily hcubical)
    subshading := ?_
    regularizationLoss := outputLoss
    regularizationLoss_eq := rfl
    retained_mass := hretained
    per_tube := hperTube
    cardinality_retention := hcardinality
    degree_uniform := ?_ }⟩
  · intro index point hpoint
    exact hpoint
  · intro scale first second hfirst hsecond
    have hfirstCard :=
      fromFinset_filter_card regularized.selected
        (prunedParent scale) first
    have hsecondCard :=
      fromFinset_filter_card regularized.selected
        (prunedParent scale) second
    have hfirst' :
        0 <
          (regularized.selected.filter fun index =>
            prunedParent scale index = first).card := by
      change
        0 <
          ((Finset.univ : Finset (Fin regularized.selected.card)).filter
            fun index =>
              prunedParent scale
                (regularized.selected.orderEmbOfFin rfl index) =
                  first).card at hfirst
      rw [← hfirstCard]
      exact hfirst
    have hsecond' :
        0 <
          (regularized.selected.filter fun index =>
            prunedParent scale index = second).card := by
      change
        0 <
          ((Finset.univ : Finset (Fin regularized.selected.card)).filter
            fun index =>
              prunedParent scale
                (regularized.selected.orderEmbOfFin rfl index) =
                  second).card at hsecond
      rw [← hsecondCard]
      exact hsecond
    have huniform :=
      regularized.degree_uniform
        scale first second hfirst' hsecond'
    rw [← hfirstCard, ← hsecondCard] at huniform
    have hdegreeConstant :
        16 * (scaleCount : ENNReal) *
              (Nat.log 2
                  (2 * prunedSubfamily.family.card) +
                1 : ENNReal) ^
                scaleCount ≤
          16 * (scaleCount : ENNReal) *
              (Nat.log 2 (2 * family.card) + 1 : ENNReal) ^
                scaleCount := by
      have hcard :
          prunedSubfamily.family.card ≤ family.card := by
        change pruned.selected.card ≤ family.card
        simpa only [Fintype.card_fin] using
          Finset.card_le_univ pruned.selected
      have hlog :
          Nat.log 2 (2 * prunedSubfamily.family.card) + 1 ≤
            Nat.log 2 (2 * family.card) + 1 := by
        gcongr
      gcongr
    have huniform' := huniform.trans
      (mul_le_mul_right' hdegreeConstant _)
    change
      (((Finset.univ : Finset (Fin regularized.selected.card)).filter
        fun index =>
          prunedParent scale
            (regularized.selected.orderEmbOfFin rfl index) =
              first).card : ENNReal) ≤
        (16 * (scaleCount : ENNReal) *
            (Nat.log 2 (2 * family.card) + 1 : ENNReal) ^
              scaleCount) *
          (((Finset.univ : Finset (Fin regularized.selected.card)).filter
            fun index =>
              prunedParent scale
                (regularized.selected.orderEmbOfFin rfl index) =
                  second).card : ENNReal)
    exact huniform'

end Kakeya.Assouad

end
