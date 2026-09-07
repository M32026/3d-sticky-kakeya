import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Proposition64PaperConflictDegree
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperFiniteWeightedDegreeSelection
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperShadingMassUpper
import MyLeanRepo.Kakeya.Streamlined.RandomTranslation.TubeDensityTestNet.RoundingLemma

/-!
# Proposition 6.4 joint paper-ED selection

The mild-rescaling cleanup in `wz2_64.tex` chooses one essentially-distinct
refinement of the affine-image/final-saturation shading.  The same selected
indices must therefore carry both the retained shaded mass and the
per-tube/cardinality ledger used in the final density estimate.

This module first proves the finite combinatorial core.  It regularizes the
weights on one dyadic band and then colors the conflict graph, retaining one
single finset throughout.  In particular, every selected index inherits the
regularized lower weight

`totalWeight / (2 * ambientCardinality)`.

That is the same-witness receipt needed to cancel the natural source
cardinality against the source indexed-mass lower bound.  No polynomial
upper bound for the runtime family cardinality is used.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

/-- The logarithmic loss from one finite weight-band regularization. -/
noncomputable def pureWZ2Proposition64JointWeightRegularizationLoss
    (n : ℕ) : ENNReal :=
  8 * (Nat.log 2 (2 * n) + 1 : ENNReal) ^ 2

/-- Family-free degree bound obtained by pulling a final conflict back to a
source line-metric ball and packing the essentially-distinct source lines. -/
noncomputable def pureWZ2Proposition64PaperConflictPackingDegree
    (sourceDelta normalization finalDelta halfHeight : ℝ) : ENNReal :=
  ((2561 *
    (2 * Nat.ceil
      (6 * (24000 * normalization * finalDelta / halfHeight) /
        (sourceDelta / 10000)) + 1) ^ 6 : ℕ) : ENNReal)

/-- Every cropped paper-shading carrier has finite volume because it lies in
the fixed compact ambient box. -/
theorem WZ1PaperTubeShading.carrier_volume_ne_top
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (shading : WZ1PaperTubeShading family)
    (index : Fin family.card) :
    MeasureTheory.volume (shading.carrier index) ≠ ⊤ := by
  have hsubset :
      shading.carrier index ⊆ Kakeya.Streamlined.axisBox 2 2 2 := by
    intro point hpoint
    exact (shading.subset_body index hpoint).2
  have hcompact :
      IsCompact (Kakeya.Streamlined.axisBox (2 : ℝ) 2 2) :=
    Kakeya.Streamlined.isCompact_axisBox 2 2 2
      (by norm_num) (by norm_num) (by norm_num)
  exact ((MeasureTheory.measure_mono hsubset).trans_lt
    hcompact.measure_lt_top).ne

/--
One frozen finite set simultaneously carrying conflict-freeness, retained
weight, a positive dyadic weight band, and the ambient-average weight floor.
-/
structure PureWZ2Proposition64JointWeightedSelectionData
    {n : ℕ}
    (weight : Fin n → ENNReal)
    (conflict : Fin n → Fin n → Prop)
    (K : ENNReal) where
  selected : Finset (Fin n)
  independent :
    ∀ first ∈ selected, ∀ second ∈ selected,
      first ≠ second → ¬conflict first second
  retained_weight :
    (∑ index, weight index) ≤
      pureWZ2Proposition64JointWeightRegularizationLoss n *
        (K + 1) * ∑ index ∈ selected, weight index
  selected_weight_pos :
    ∀ index ∈ selected, 0 < weight index
  selected_weight_floor :
    ∀ index ∈ selected,
      (∑ source, weight source) / (2 * n : ENNReal) ≤ weight index
  weightLevel : ENNReal
  weightLevel_pos : 0 < weightLevel
  weight_band :
    ∀ index ∈ selected,
      weightLevel ≤ weight index ∧ weight index ≤ 2 * weightLevel
  selected_sum_lower :
    weightLevel * (selected.card : ENNReal) ≤
      ∑ index ∈ selected, weight index
  selected_sum_upper :
    (∑ index ∈ selected, weight index) ≤
      (2 * weightLevel) * (selected.card : ENNReal)

/--
Dyadically regularize finite weights first, then apply the symmetric
conflict-graph selection to the regularized support.  The final set is the
literal intersection of the graph color class with that support, so all
receipts refer to one finset.
-/
theorem pureWZ2Proposition64_jointWeightedSelection
    {n : ℕ}
    (weight : Fin n → ENNReal)
    (conflict : Fin n → Fin n → Prop)
    (hconflictSymm : ∀ first second,
      conflict first second → conflict second first)
    (hconflictIrrefl : ∀ index, ¬conflict index index)
    (K : ENNReal)
    (hdegree : ∀ index,
      ((Finset.univ.filter fun other =>
        conflict index other).card : ENNReal) ≤ K) :
    Nonempty
      (PureWZ2Proposition64JointWeightedSelectionData
        weight conflict K) := by
  let Vertex : Fin 1 → Type := fun _ => Unit
  let parent : ∀ coordinate, Fin n → Vertex coordinate :=
    fun _ _ => ()
  let regularized : WZ2FiniteWeightedDegreeSelectionData
      1 Vertex parent weight :=
    Classical.choice
      (wz2_finite_weighted_degree_selection
        1 Vertex parent weight (by omega))
  let regularizedWeight : Fin n → ENNReal := fun index =>
    if index ∈ regularized.selected then weight index else 0
  rcases weighted_symmetric_irreflexive_selection_of_ennreal_degree
      regularizedWeight conflict hconflictSymm hconflictIrrefl K hdegree with
    ⟨colorClass, hcolorIndependent, hcolorWeight⟩
  let selected := colorClass.filter fun index =>
    index ∈ regularized.selected
  have hselectedSubsetColor : selected ⊆ colorClass :=
    Finset.filter_subset _ _
  have hselectedSubsetRegularized : selected ⊆ regularized.selected := by
    intro index hindex
    exact (Finset.mem_filter.mp hindex).2
  have hregularizedSum :
      (∑ index, regularizedWeight index) =
        ∑ index ∈ regularized.selected, weight index := by
    change
      (∑ index : Fin n,
        if index ∈ regularized.selected then weight index else 0) = _
    rw [Finset.sum_ite]
    simp
  have hselectedSum :
      (∑ index ∈ colorClass, regularizedWeight index) =
        ∑ index ∈ selected, weight index := by
    change
      (∑ index ∈ colorClass,
        if index ∈ regularized.selected then weight index else 0) = _
    rw [Finset.sum_ite]
    simp [selected]
  have hindependent :
      ∀ first ∈ selected, ∀ second ∈ selected,
        first ≠ second → ¬conflict first second := by
    intro first hfirst second hsecond hne
    exact hcolorIndependent first (hselectedSubsetColor hfirst)
      second (hselectedSubsetColor hsecond) hne
  have hretained :
      (∑ index, weight index) ≤
        pureWZ2Proposition64JointWeightRegularizationLoss n *
          (K + 1) * ∑ index ∈ selected, weight index := by
    calc
      (∑ index, weight index) ≤
          pureWZ2Proposition64JointWeightRegularizationLoss n *
            ∑ index ∈ regularized.selected, weight index := by
        simpa [pureWZ2Proposition64JointWeightRegularizationLoss]
          using regularized.retained_weight
      _ = pureWZ2Proposition64JointWeightRegularizationLoss n *
          (∑ index, regularizedWeight index) := by rw [hregularizedSum]
      _ ≤ pureWZ2Proposition64JointWeightRegularizationLoss n *
          ((K + 1) *
            ∑ index ∈ colorClass, regularizedWeight index) := by
        gcongr
      _ = pureWZ2Proposition64JointWeightRegularizationLoss n *
          (K + 1) * ∑ index ∈ selected, weight index := by
        rw [hselectedSum]
        ring
  have hsumLower :
      regularized.weightLevel * (selected.card : ENNReal) ≤
        ∑ index ∈ selected, weight index := by
    calc
      regularized.weightLevel * (selected.card : ENNReal) =
          ∑ _index ∈ selected, regularized.weightLevel := by
        simp [Finset.sum_const]
        ring
      _ ≤ ∑ index ∈ selected, weight index := by
        apply Finset.sum_le_sum
        intro index hindex
        exact (regularized.weight_band index
          (hselectedSubsetRegularized hindex)).1
  have hsumUpper :
      (∑ index ∈ selected, weight index) ≤
        (2 * regularized.weightLevel) * (selected.card : ENNReal) := by
    calc
      (∑ index ∈ selected, weight index) ≤
          ∑ _index ∈ selected, 2 * regularized.weightLevel := by
        apply Finset.sum_le_sum
        intro index hindex
        exact (regularized.weight_band index
          (hselectedSubsetRegularized hindex)).2
      _ = (2 * regularized.weightLevel) *
          (selected.card : ENNReal) := by
        simp [Finset.sum_const]
        ring
  exact ⟨{
    selected := selected
    independent := hindependent
    retained_weight := hretained
    selected_weight_pos := fun index hindex =>
      regularized.selected_weight_pos index
        (hselectedSubsetRegularized hindex)
    selected_weight_floor := fun index hindex =>
      by
        simpa only [Fintype.card_fin] using
          regularized.selected_weight_floor index
            (hselectedSubsetRegularized hindex)
    weightLevel := regularized.weightLevel
    weightLevel_pos := regularized.weightLevel_pos
    weight_band := fun index hindex =>
      regularized.weight_band index
        (hselectedSubsetRegularized hindex)
    selected_sum_lower := hsumLower
    selected_sum_upper := hsumUpper }⟩

/--
The paper-facing joint selector.  The final family is a literal subfamily of
the positive-mass part of the supplied final saturated shading.  Its one
selected finset carries paper essential distinctness, mass retention,
average per-tube shaded mass, a factor-two mass band, body/cardinality
control, and exact ambient provenance.
-/
structure PureWZ2Proposition64JointPaperEDSelectionData
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (sourceShading : WZ1PaperTubeShading family)
    (K : ENNReal) where
  subfamily : Kakeya.Streamlined.TubeSubfamily family
  finalShading : WZ1PaperTubeShading subfamily.family
  shading_eq : finalShading =
    restrictPaperShading subfamily sourceShading
  essentially_distinct :
    WZ2PaperOrdinaryIsEssentiallyDistinct subfamily.family
  union_subset : finalShading.union ⊆ sourceShading.union
  mass_retention :
    sourceShading.mass ≤
      pureWZ2Proposition64JointWeightRegularizationLoss
          (paperPositiveMassSubfamily sourceShading).family.card *
        (K + 1) * finalShading.mass
  carrier_volume_pos :
    ∀ index, 0 < MeasureTheory.volume (finalShading.carrier index)
  average_carrier_floor :
    ∀ index,
      sourceShading.mass /
          (2 *
            (paperPositiveMassSubfamily sourceShading).family.card :
              ENNReal) ≤
        MeasureTheory.volume (finalShading.carrier index)
  weightLevel : ENNReal
  weightLevel_pos : 0 < weightLevel
  carrier_volume_band :
    ∀ index,
      weightLevel ≤ MeasureTheory.volume (finalShading.carrier index) ∧
        MeasureTheory.volume (finalShading.carrier index) ≤
          2 * weightLevel
  shaded_mass_lower :
    weightLevel * subfamily.family.enncard ≤ finalShading.mass
  shaded_mass_upper :
    finalShading.mass ≤
      (2 * weightLevel) * subfamily.family.enncard
  body_mass_upper :
    (wz1PaperBodyFamily subfamily.family).mass ≤
      (55296 * Kakeya.deltaTubeVolume 1) *
        Kakeya.realRpowENN delta 2 * subfamily.family.enncard
  sourceParent : Fin subfamily.family.card → Fin family.card
  sourceParent_eq : sourceParent = subfamily.embedding
  tube_provenance :
    ∀ index,
      subfamily.family.tube index = family.tube (sourceParent index)

/-- Loss parameter used when the stronger joint selector is viewed through
the older cleanup interface. -/
noncomputable def pureWZ2Proposition64JointCleanupLoss
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (sourceShading : WZ1PaperTubeShading family)
    (K : ENNReal) : ENNReal :=
  pureWZ2Proposition64JointWeightRegularizationLoss
      (paperPositiveMassSubfamily sourceShading).family.card *
    (K + 1)

namespace PureWZ2Proposition64JointPaperEDSelectionData

/-- Forget only the additional average-mass and weight-band receipts.  The
family, shading, source map, and essential-distinctness witness are
definitionally unchanged. -/
noncomputable def toPaperEDCleanupData
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading family}
    {K : ENNReal}
    (joint : PureWZ2Proposition64JointPaperEDSelectionData sourceShading K) :
    PureWZ2Proposition64PaperEDCleanupData sourceShading
      (pureWZ2Proposition64JointCleanupLoss sourceShading K) where
  subfamily := joint.subfamily
  finalShading := joint.finalShading
  shading_eq := joint.shading_eq
  essentially_distinct := joint.essentially_distinct
  union_subset := joint.union_subset
  mass_retention := joint.mass_retention.trans <| by
    apply mul_le_mul_right'
    exact le_add_of_nonneg_right (by norm_num)
  carrier_volume_pos := joint.carrier_volume_pos
  sourceParent := joint.sourceParent
  sourceParent_eq := joint.sourceParent_eq
  tube_provenance := joint.tube_provenance

end PureWZ2Proposition64JointPaperEDSelectionData

/--
Construct the joint paper selector on the positive-mass part of a final
saturated shading.  The conflict-degree hypothesis is exactly the output of
`pureWZ2Proposition64_positivePaperConflictDegree`; no cardinality estimate
is added.
-/
theorem pureWZ2Proposition64_jointPaperEDSelection
    {delta : ℝ}
    (hdelta : 0 < delta)
    (hdeltaSmall : delta ≤ 1 / 24)
    (family : Kakeya.Streamlined.TubeFamily delta)
    (sourceShading : WZ1PaperTubeShading family)
    (hpositiveLine : WZ1PaperIsLineClass
      (paperPositiveMassSubfamily sourceShading).family)
    (K : ENNReal)
    (hdegree :
      ∀ index : Fin
          (paperPositiveMassSubfamily sourceShading).family.card,
        ((Finset.univ.filter fun other =>
          pureWZ2Proposition64PaperConflict
            (paperPositiveMassSubfamily sourceShading).family
              index other).card : ENNReal) ≤ K) :
    Nonempty
      (PureWZ2Proposition64JointPaperEDSelectionData
        sourceShading K) := by
  let positive := paperPositiveMassSubfamily sourceShading
  let positiveShading := restrictPaperShading positive sourceShading
  let weight : Fin positive.family.card → ENNReal := fun index =>
    MeasureTheory.volume (positiveShading.carrier index)
  let conflict : Fin positive.family.card → Fin positive.family.card → Prop :=
    pureWZ2Proposition64PaperConflict positive.family
  let joint : PureWZ2Proposition64JointWeightedSelectionData
      weight conflict K :=
    Classical.choice
      (pureWZ2Proposition64_jointWeightedSelection weight conflict
        (pureWZ2Proposition64PaperConflict_symm positive.family)
        (pureWZ2Proposition64PaperConflict_irrefl positive.family)
        K hdegree)
  let inner := Kakeya.Streamlined.TubeSubfamily.fromFinset
    positive.family joint.selected
  let finalSubfamily := positive.comp inner
  let finalShading := restrictPaperShading finalSubfamily sourceShading
  have hfinalShading :
      finalShading = restrictPaperShading inner positiveShading := rfl
  have hpositiveMass :
      positiveShading.mass = sourceShading.mass :=
    restrictPaperShading_positiveMass_mass sourceShading
  have hselectedMass :
      finalShading.mass =
        ∑ index ∈ joint.selected, weight index := by
    rw [hfinalShading]
    change
      (∑ index : Fin inner.family.card,
        MeasureTheory.volume
          (positiveShading.carrier (inner.embedding index))) =
        ∑ index ∈ joint.selected, weight index
    let equivalence := joint.selected.orderIsoOfFin rfl
    calc
      (∑ index : Fin inner.family.card,
          MeasureTheory.volume
            (positiveShading.carrier (inner.embedding index))) =
          ∑ index : joint.selected,
            MeasureTheory.volume (positiveShading.carrier index.1) :=
        Equiv.sum_comp equivalence.toEquiv
          (fun index : joint.selected =>
            MeasureTheory.volume (positiveShading.carrier index.1))
      _ = ∑ index ∈ joint.selected, weight index := by
        simpa [weight] using
          Finset.sum_attach joint.selected
            (fun index =>
              MeasureTheory.volume (positiveShading.carrier index))
  have hfinalLine : WZ1PaperIsLineClass finalSubfamily.family := by
    exact hpositiveLine.subfamily inner
  have hbody :
      (wz1PaperBodyFamily finalSubfamily.family).mass ≤
        (55296 * Kakeya.deltaTubeVolume 1) *
          Kakeya.realRpowENN delta 2 * finalSubfamily.family.enncard := by
    let fullShading : WZ1PaperTubeShading finalSubfamily.family := {
      carrier := fun index =>
        wz1PaperTubeCarrier (finalSubfamily.family.tube index)
      measurable_carrier := fun index =>
        wz1PaperTubeCarrier_measurable
          (finalSubfamily.family.tube index)
      subset_body := fun _ => Set.Subset.rfl }
    have h := wz2_paper_shading_mass_upper
      hdelta hdeltaSmall hfinalLine fullShading
    change fullShading.mass ≤ _
    simpa [mul_assoc] using h
  refine ⟨{
    subfamily := finalSubfamily
    finalShading := finalShading
    shading_eq := rfl
    essentially_distinct := ?_
    union_subset := ?_
    mass_retention := ?_
    carrier_volume_pos := ?_
    average_carrier_floor := ?_
    weightLevel := joint.weightLevel
    weightLevel_pos := joint.weightLevel_pos
    carrier_volume_band := ?_
    shaded_mass_lower := ?_
    shaded_mass_upper := ?_
    body_mass_upper := hbody
    sourceParent := finalSubfamily.embedding
    sourceParent_eq := rfl
    tube_provenance := finalSubfamily.tube_eq }⟩
  · intro first second hne
    have hfirst : inner.embedding first ∈ joint.selected :=
      Finset.orderEmbOfFin_mem joint.selected rfl first
    have hsecond : inner.embedding second ∈ joint.selected :=
      Finset.orderEmbOfFin_mem joint.selected rfl second
    have hnoconflict := joint.independent
      (inner.embedding first) hfirst
      (inner.embedding second) hsecond
      (inner.embedding.injective.ne hne)
    unfold conflict at hnoconflict
    unfold pureWZ2Proposition64PaperConflict at hnoconflict
    by_contra hnot
    apply hnoconflict
    refine ⟨inner.embedding.injective.ne hne, ?_⟩
    intro hambient
    apply hnot
    constructor
    · change ¬((inner.family.tube first).carrier ⊆
        wz2PaperCenteredDilatedCarrier 2 (inner.family.tube second))
      rw [inner.tube_eq first, inner.tube_eq second]
      exact hambient.1
    · change ¬((inner.family.tube second).carrier ⊆
        wz2PaperCenteredDilatedCarrier 2 (inner.family.tube first))
      rw [inner.tube_eq first, inner.tube_eq second]
      exact hambient.2
  · rintro point ⟨index, hpoint⟩
    exact ⟨finalSubfamily.embedding index, hpoint⟩
  · rw [← hpositiveMass]
    change (∑ index, weight index) ≤ _
    rw [hselectedMass]
    exact joint.retained_weight
  · intro index
    rw [hfinalShading]
    change 0 < weight (inner.embedding index)
    exact joint.selected_weight_pos (inner.embedding index)
      (Finset.orderEmbOfFin_mem joint.selected rfl index)
  · intro index
    rw [hfinalShading, ← hpositiveMass]
    change (∑ source, weight source) /
        (2 * positive.family.card : ENNReal) ≤
      weight (inner.embedding index)
    exact joint.selected_weight_floor (inner.embedding index)
      (Finset.orderEmbOfFin_mem joint.selected rfl index)
  · intro index
    rw [hfinalShading]
    change joint.weightLevel ≤ weight (inner.embedding index) ∧
      weight (inner.embedding index) ≤ 2 * joint.weightLevel
    exact joint.weight_band (inner.embedding index)
      (Finset.orderEmbOfFin_mem joint.selected rfl index)
  · change joint.weightLevel *
      (joint.selected.card : ENNReal) ≤ finalShading.mass
    rw [hselectedMass]
    exact joint.selected_sum_lower
  · change finalShading.mass ≤
      (2 * joint.weightLevel) * (joint.selected.card : ENNReal)
    rw [hselectedMass]
    exact joint.selected_sum_upper

/--
Canonical Proposition-6.4 specialization: exact affine image, popular-box
restriction, final isotropic saturation, positive-mass deletion, weight-band
regularization, and paper-conflict coloring are performed in that order.
-/
theorem pureWZ2Proposition64_exactJointPaperEDSelection
    {sourceDelta imageDelta finalDelta width scale : ℝ}
    (g : ℝ → ℝ)
    (slabCenter anchorHeight halfHeight normalization : ℝ)
    (translation : Point3)
    (sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta)
    (htranslationHeight : translation 2 = 0)
    (hhalfHeight : 0 < halfHeight) (hhalfHeightOne : halfHeight ≤ 1)
    (hnormalization : 9 ≤ normalization)
    (hanchorSlope : |g anchorHeight| ≤ 8)
    (hslabCenter : |slabCenter| ≤ 1)
    (hsourceLine : WZ1PaperIsLineClass sourceFamily)
    (hexactLine : WZ1PaperIsLineClass
      (pureWZ2Proposition64ImageFamily imageDelta g slabCenter anchorHeight
        halfHeight normalization translation hhalfHeight
          (by linarith : 0 < normalization) sourceFamily))
    (exactShading : WZ1PaperTubeShading
      (pureWZ2Proposition64ImageFamily imageDelta g slabCenter anchorHeight
        halfHeight normalization translation hhalfHeight
          (by linarith : 0 < normalization) sourceFamily))
    (popular : PureWZ2Proposition64PopularBoxData exactShading width)
    (hwidth : 0 < width)
    (himageDelta : 0 < imageDelta)
    (hfinalDelta : 0 < finalDelta)
    (hfinalDeltaSmall : finalDelta ≤ 1 / 96)
    (hscale : 1 ≤ scale)
    (hradius : scale * (6 * imageDelta) +
      2 * finalDelta ≤ 6 * finalDelta)
    (hboxScale : 18 * scale * width ≤ 1)
    (C : ENNReal)
    (hFrostman : TubeParameterFrostmanBound sourceFamily C)
    (hsourceWidth : sourceDelta ≤
      24000 * normalization * finalDelta / halfHeight)
    (hwidthOne :
      24000 * normalization * finalDelta / halfHeight ≤ 1) :
    let sourceWindow := popular.union_subset_closedBall hwidth
      (lt_of_lt_of_le zero_lt_one hscale)
      (by linarith : 3 * scale * width ≤ 1)
    let finalShading := pureWZ2Proposition64FullIsotropicPaperShading
      popular.restricted popular.center scale himageDelta hfinalDelta
      (hfinalDeltaSmall.trans (by norm_num)) hscale hradius sourceWindow
    let K := C * Kakeya.realRpowENN
      (24000 * normalization * finalDelta / halfHeight) 2 *
        sourceFamily.enncard
    Nonempty
      (PureWZ2Proposition64JointPaperEDSelectionData
        finalShading K) := by
  dsimp only
  let sourceWindow := popular.union_subset_closedBall hwidth
    (lt_of_lt_of_le zero_lt_one hscale)
    (by linarith : 3 * scale * width ≤ 1)
  let finalShading := pureWZ2Proposition64FullIsotropicPaperShading
    popular.restricted popular.center scale himageDelta hfinalDelta
    (hfinalDeltaSmall.trans (by norm_num)) hscale hradius sourceWindow
  let positive := paperPositiveMassSubfamily finalShading
  let K := C * Kakeya.realRpowENN
    (24000 * normalization * finalDelta / halfHeight) 2 *
      sourceFamily.enncard
  have hpositiveLine : WZ1PaperIsLineClass positive.family := by
    apply pureWZ2Proposition64_positiveIsotropicFamily_lineClass popular
      hexactLine hwidth himageDelta hfinalDelta hfinalDeltaSmall
      hscale hradius hboxScale
  have hdegree : ∀ reference : Fin positive.family.card,
      ((Finset.univ.filter fun other =>
        pureWZ2Proposition64PaperConflict
          positive.family reference other).card : ENNReal) ≤ K := by
    exact pureWZ2Proposition64_positivePaperConflictDegree g slabCenter
      anchorHeight halfHeight normalization translation popular.center scale
      sourceFamily htranslationHeight hhalfHeight hhalfHeightOne
      hnormalization hanchorSlope hslabCenter hsourceLine hexactLine
      finalShading hpositiveLine (popular.center_mem 2) hscale hfinalDelta
      C hFrostman hsourceWidth hwidthOne
  exact pureWZ2Proposition64_jointPaperEDSelection
    hfinalDelta (hfinalDeltaSmall.trans (by norm_num))
    _ finalShading hpositiveLine K hdegree

/-- Canonical Proposition-6.4 joint selection with a family-free conflict
degree.  The degree comes from local packing in the original essentially
distinct source family, rather than from a Frostman constant times the
runtime source cardinality. -/
theorem pureWZ2Proposition64_exactJointPaperEDSelectionPacking
    {sourceDelta imageDelta finalDelta width scale : ℝ}
    (g : ℝ → ℝ)
    (slabCenter anchorHeight halfHeight normalization : ℝ)
    (translation : Point3)
    (sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta)
    (hsourceDelta : 0 < sourceDelta)
    (htranslationHeight : translation 2 = 0)
    (hhalfHeight : 0 < halfHeight) (hhalfHeightOne : halfHeight ≤ 1)
    (hnormalization : 9 ≤ normalization)
    (hanchorSlope : |g anchorHeight| ≤ 8)
    (hslabCenter : |slabCenter| ≤ 1)
    (hsourceLine : WZ1PaperIsLineClass sourceFamily)
    (hsourceDistinct : WZ2PaperOrdinaryIsEssentiallyDistinct sourceFamily)
    (hsourceBounded : HasBoundedBase sourceFamily 4)
    (hexactLine : WZ1PaperIsLineClass
      (pureWZ2Proposition64ImageFamily imageDelta g slabCenter anchorHeight
        halfHeight normalization translation hhalfHeight
          (by linarith : 0 < normalization) sourceFamily))
    (exactShading : WZ1PaperTubeShading
      (pureWZ2Proposition64ImageFamily imageDelta g slabCenter anchorHeight
        halfHeight normalization translation hhalfHeight
          (by linarith : 0 < normalization) sourceFamily))
    (popular : PureWZ2Proposition64PopularBoxData exactShading width)
    (hwidth : 0 < width)
    (himageDelta : 0 < imageDelta)
    (hfinalDelta : 0 < finalDelta)
    (hfinalDeltaSmall : finalDelta ≤ 1 / 96)
    (hscale : 1 ≤ scale)
    (hradius : scale * (6 * imageDelta) +
      2 * finalDelta ≤ 6 * finalDelta)
    (hboxScale : 18 * scale * width ≤ 1) :
    let sourceWindow := popular.union_subset_closedBall hwidth
      (lt_of_lt_of_le zero_lt_one hscale)
      (by linarith : 3 * scale * width ≤ 1)
    let finalShading := pureWZ2Proposition64FullIsotropicPaperShading
      popular.restricted popular.center scale himageDelta hfinalDelta
      (hfinalDeltaSmall.trans (by norm_num)) hscale hradius sourceWindow
    Nonempty
      (PureWZ2Proposition64JointPaperEDSelectionData finalShading
        (pureWZ2Proposition64PaperConflictPackingDegree sourceDelta
          normalization finalDelta halfHeight)) := by
  dsimp only
  let sourceWindow := popular.union_subset_closedBall hwidth
    (lt_of_lt_of_le zero_lt_one hscale)
    (by linarith : 3 * scale * width ≤ 1)
  let finalShading := pureWZ2Proposition64FullIsotropicPaperShading
    popular.restricted popular.center scale himageDelta hfinalDelta
    (hfinalDeltaSmall.trans (by norm_num)) hscale hradius sourceWindow
  let positive := paperPositiveMassSubfamily finalShading
  let K := pureWZ2Proposition64PaperConflictPackingDegree sourceDelta
    normalization finalDelta halfHeight
  have hpositiveLine : WZ1PaperIsLineClass positive.family := by
    apply pureWZ2Proposition64_positiveIsotropicFamily_lineClass popular
      hexactLine hwidth himageDelta hfinalDelta hfinalDeltaSmall
      hscale hradius hboxScale
  have hdegree : ∀ reference : Fin positive.family.card,
      ((Finset.univ.filter fun other =>
        pureWZ2Proposition64PaperConflict
          positive.family reference other).card : ENNReal) ≤ K := by
    exact pureWZ2Proposition64_positivePaperConflictPackingDegree g slabCenter
      anchorHeight halfHeight normalization translation popular.center scale
      sourceFamily htranslationHeight hhalfHeight hhalfHeightOne
      hnormalization hanchorSlope hslabCenter hsourceLine hsourceDistinct
      hsourceBounded hexactLine finalShading hpositiveLine
      (popular.center_mem 2) hscale
      hsourceDelta hfinalDelta
  exact pureWZ2Proposition64_jointPaperEDSelection
    hfinalDelta (hfinalDeltaSmall.trans (by norm_num))
    _ finalShading hpositiveLine K hdegree

namespace PureWZ2Proposition64JointPaperEDSelectionData

/--
Same-witness density cancellation.  Once the average per-tube source mass
dominates the target body cost, summing over the very same selected indices
proves lambda density; neither the conflict degree nor the ambient
cardinality remains in the conclusion.
-/
theorem dense_of_average_body_cost
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading family}
    {K targetDensity : ENNReal}
    (data : PureWZ2Proposition64JointPaperEDSelectionData
      sourceShading K)
    (haverage :
      targetDensity *
          ((55296 * Kakeya.deltaTubeVolume 1) *
            Kakeya.realRpowENN delta 2) ≤
        sourceShading.mass /
          (2 *
            (paperPositiveMassSubfamily sourceShading).family.card :
              ENNReal)) :
    data.finalShading.IsLambdaDense targetDensity := by
  calc
    targetDensity *
        (wz1PaperBodyFamily data.subfamily.family).mass ≤
      targetDensity *
        (((55296 * Kakeya.deltaTubeVolume 1) *
            Kakeya.realRpowENN delta 2) *
          data.subfamily.family.enncard) := by
      gcongr
      simpa [mul_assoc] using data.body_mass_upper
    _ ≤
      (sourceShading.mass /
          (2 *
            (paperPositiveMassSubfamily sourceShading).family.card :
              ENNReal)) *
        data.subfamily.family.enncard := by
      calc
        targetDensity *
            (((55296 * Kakeya.deltaTubeVolume 1) *
                Kakeya.realRpowENN delta 2) *
              data.subfamily.family.enncard) =
            (targetDensity *
                ((55296 * Kakeya.deltaTubeVolume 1) *
                  Kakeya.realRpowENN delta 2)) *
              data.subfamily.family.enncard := by ring
        _ ≤
            (sourceShading.mass /
                (2 *
                  (paperPositiveMassSubfamily sourceShading).family.card :
                    ENNReal)) *
              data.subfamily.family.enncard := by gcongr
    _ = ∑ index : Fin data.subfamily.family.card,
        sourceShading.mass /
          (2 *
            (paperPositiveMassSubfamily sourceShading).family.card :
              ENNReal) := by
      simp [Kakeya.Streamlined.TubeFamily.enncard, Finset.sum_const]
      ring
    _ ≤ ∑ index : Fin data.subfamily.family.card,
        MeasureTheory.volume (data.finalShading.carrier index) := by
      apply Finset.sum_le_sum
      intro index _
      exact data.average_carrier_floor index
    _ = data.finalShading.mass := rfl

end PureWZ2Proposition64JointPaperEDSelectionData

end Kakeya.Assouad

end
