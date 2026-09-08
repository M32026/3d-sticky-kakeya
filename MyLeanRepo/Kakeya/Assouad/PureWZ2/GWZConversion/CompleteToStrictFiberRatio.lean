import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12PureFiberRestriction
import MyLeanRepo.Kakeya.Assouad.PropStickyFiniteFiberRatio
import MyLeanRepo.Kakeya.Assouad.PureWZ2.GWZConversion.OneScaleAnchoredColoring

/-!
# Complete-to-strict fiber cardinality ratio

The complete GWZ fibers need not partition the source family.  Their total
incidence is nevertheless bounded by the explicit complete-parent overlap
constant.  Combining this incidence bound with:

* input complete-fiber uniformity;
* one global selected-cardinality retention inequality;
* final owner-degree uniformity;

gives a pointwise ratio from each original complete GWZ fiber to the
corresponding final literal strict fiber.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

/-- Total complete-fiber incidence is bounded by pointwise parent overlap. -/
theorem pureWZ2_complete_fiber_incidence_sum_le
    {delta A : ℝ}
    (hdelta : 0 < delta)
    (hA : 1 ≤ A)
    {source : Kakeya.Streamlined.TubeFamily delta}
    {constant : ENNReal}
    {scale : Kakeya.Streamlined.AdmissibleScale delta}
    (scaleData :
      PureWZ2GWZScaleData (A := A) source scale constant)
    (hscaleSmall : scale.1 ≤ 1 / (200 * A)) :
    (∑ parent : Fin scaleData.coarse.card,
        (scaleData.fullFiberIndices parent).card) ≤
      pureWZ2CompleteFiberOverlapBound A * source.card := by
  have hdegree :=
    pureWZ2_complete_fiber_parent_overlap
      hdelta hA scaleData hscaleSmall
  calc
    (∑ parent : Fin scaleData.coarse.card,
        (scaleData.fullFiberIndices parent).card) =
        ∑ parent : Fin scaleData.coarse.card,
          ∑ index : Fin source.card,
            if index ∈ scaleData.fullFiberIndices parent then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro parent _
      simpa using
        (Finset.sum_boole
          (fun index : Fin source.card =>
            index ∈ scaleData.fullFiberIndices parent)
          Finset.univ).symm
    _ =
        ∑ index : Fin source.card,
          ∑ parent : Fin scaleData.coarse.card,
            if index ∈ scaleData.fullFiberIndices parent then 1 else 0 := by
      rw [Finset.sum_comm]
    _ =
        ∑ index : Fin source.card,
          (Finset.univ.filter fun parent :
            Fin scaleData.coarse.card =>
              index ∈ scaleData.fullFiberIndices parent).card := by
      apply Finset.sum_congr rfl
      intro index _
      simpa using
        (Finset.sum_boole
          (fun parent : Fin scaleData.coarse.card =>
            index ∈ scaleData.fullFiberIndices parent)
          Finset.univ)
    _ ≤
        ∑ _index : Fin source.card,
          pureWZ2CompleteFiberOverlapBound A := by
      exact Finset.sum_le_sum fun index _ => hdegree index
    _ =
        pureWZ2CompleteFiberOverlapBound A * source.card := by
      simp [Nat.mul_comm]

/--
Restricting the parent sum to an embedded family of active parents preserves
the same complete-incidence bound.
-/
theorem pureWZ2_active_complete_fiber_incidence_sum_le
    {delta A : ℝ}
    (hdelta : 0 < delta)
    (hA : 1 ≤ A)
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : Kakeya.Streamlined.TubeShading source}
    (fine : PureWZ2LocalizedDistinctReanchoringData sourceShading)
    {constant : ENNReal}
    {scale : Kakeya.Streamlined.AdmissibleScale delta}
    (scaleData :
      PureWZ2GWZScaleData (A := A) source scale constant)
    (hscaleSmall : scale.1 ≤ 1 / (200 * A))
    (oneScale :
      PureWZ2OneScaleAnchoredOwnerCoverData fine scaleData)
    (selectedCoarse :
      WZ2PaperPureTubeSubfamily oneScale.coarse) :
    (∑ parent : Fin selectedCoarse.family.card,
        (scaleData.fullFiberIndices
          (oneScale.originalParent
            (selectedCoarse.embedding parent))).card) ≤
      pureWZ2CompleteFiberOverlapBound A * source.card := by
  let parentEmbedding :
      Fin selectedCoarse.family.card ↪
        Fin scaleData.coarse.card :=
    selectedCoarse.embedding.trans oneScale.originalParent
  let activeParents : Finset (Fin scaleData.coarse.card) :=
    Finset.univ.map parentEmbedding
  have hsum :
      (∑ parent : Fin selectedCoarse.family.card,
          (scaleData.fullFiberIndices
            (oneScale.originalParent
              (selectedCoarse.embedding parent))).card) =
        ∑ parent ∈ activeParents,
          (scaleData.fullFiberIndices parent).card := by
    dsimp only [activeParents, parentEmbedding]
    symm
    simpa using
      (Finset.sum_map
        (Finset.univ : Finset
          (Fin selectedCoarse.family.card))
        (selectedCoarse.embedding.trans oneScale.originalParent)
        (fun parent =>
          (scaleData.fullFiberIndices parent).card))
  rw [hsum]
  calc
    (∑ parent ∈ activeParents,
        (scaleData.fullFiberIndices parent).card) ≤
        ∑ parent : Fin scaleData.coarse.card,
          (scaleData.fullFiberIndices parent).card := by
      exact
        Finset.sum_le_sum_of_subset_of_nonneg
          (fun _ _ => Finset.mem_univ _)
          (fun _ _ _ => Nat.zero_le _)
    _ ≤ pureWZ2CompleteFiberOverlapBound A * source.card :=
      pureWZ2_complete_fiber_incidence_sum_le
        hdelta hA scaleData hscaleSmall

/--
Pointwise complete-to-strict cardinality ratio for one final monochromatic
anchored cover.
-/
theorem pureWZ2_complete_to_strict_fiber_ratio
    {delta A : ℝ}
    (hdelta : 0 < delta)
    (hA : 1 ≤ A)
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : Kakeya.Streamlined.TubeShading source}
    {fine : PureWZ2LocalizedDistinctReanchoringData sourceShading}
    {constant : ENNReal}
    {scale : Kakeya.Streamlined.AdmissibleScale delta}
    {scaleData :
      PureWZ2GWZScaleData (A := A) source scale constant}
    (hscaleSmall : scale.1 ≤ 1 / (200 * A))
    {oneScale :
      PureWZ2OneScaleAnchoredOwnerCoverData fine scaleData}
    {selected : WZ2PaperPureTubeSubfamily fine.family}
    (monochromatic :
      PureWZ2OneScaleMonochromaticCoverData
        (A := A) (scaleData := scaleData)
        (oneScale := oneScale) selected)
    (degreeConstant retentionConstant : ENNReal)
    (degreeUniform :
      ∀ first second : Fin oneScale.coarse.card,
        0 <
            ((Finset.univ :
              Finset (Fin selected.family.card)).filter fun index =>
                oneScale.cover.parent
                    (selected.embedding index) =
                  first).card →
        0 <
            ((Finset.univ :
              Finset (Fin selected.family.card)).filter fun index =>
                oneScale.cover.parent
                    (selected.embedding index) =
                  second).card →
        (((Finset.univ :
          Finset (Fin selected.family.card)).filter fun index =>
            oneScale.cover.parent
                (selected.embedding index) =
              first).card : ENNReal) ≤
          degreeConstant *
            (((Finset.univ :
              Finset (Fin selected.family.card)).filter fun index =>
                oneScale.cover.parent
                    (selected.embedding index) =
                  second).card : ENNReal))
    (cardinalityRetention :
      source.enncard ≤
        retentionConstant * selected.family.enncard) :
    ∀ parent : Fin monochromatic.selectedCoarse.family.card,
      ((scaleData.fullFiberIndices
        (oneScale.originalParent
          (monochromatic.selectedCoarse.embedding parent))).card :
          ENNReal) ≤
        constant *
          ((pureWZ2CompleteFiberOverlapBound A : ENNReal) *
            retentionConstant) *
          degreeConstant *
          (wz2PaperOrdinaryFullFiberIndices
            selected.family monochromatic.selectedCoarse.family
            parent).card := by
  let ambient :
      Fin monochromatic.selectedCoarse.family.card → ENNReal :=
    fun parent =>
      (scaleData.fullFiberIndices
        (oneScale.originalParent
          (monochromatic.selectedCoarse.embedding parent))).card
  let strict :
      Fin monochromatic.selectedCoarse.family.card → ENNReal :=
    fun parent =>
      (wz2PaperOrdinaryFullFiberIndices
        selected.family monochromatic.selectedCoarse.family parent).card
  have hambientUniform :
      ∀ first second,
        ambient first ≤ constant * ambient second := by
    intro first second
    exact
      scaleData.full_fiber_uniform
        (oneScale.originalParent
          (monochromatic.selectedCoarse.embedding first))
        (oneScale.originalParent
          (monochromatic.selectedCoarse.embedding second))
  have hstrictUniform :
      ∀ first second,
        strict first ≤ degreeConstant * strict second := by
    intro first second
    have hfirst :
        0 <
          ((Finset.univ :
            Finset (Fin selected.family.card)).filter fun index =>
              oneScale.cover.parent
                  (selected.embedding index) =
                monochromatic.selectedCoarse.embedding first).card := by
      rw [← monochromatic.fullFiberIndices_eq_owner first]
      exact
        Finset.card_pos.mpr
          (monochromatic.full_fiber_nonempty first)
    have hsecond :
        0 <
          ((Finset.univ :
            Finset (Fin selected.family.card)).filter fun index =>
              oneScale.cover.parent
                  (selected.embedding index) =
                monochromatic.selectedCoarse.embedding second).card := by
      rw [← monochromatic.fullFiberIndices_eq_owner second]
      exact
        Finset.card_pos.mpr
          (monochromatic.full_fiber_nonempty second)
    have huniform :=
      degreeUniform
        (monochromatic.selectedCoarse.embedding first)
        (monochromatic.selectedCoarse.embedding second)
        hfirst hsecond
    dsimp only [strict]
    rw [monochromatic.fullFiberIndices_eq_owner first,
      monochromatic.fullFiberIndices_eq_owner second]
    exact huniform
  have hambientSum :
      (∑ parent, ambient parent) ≤
        (pureWZ2CompleteFiberOverlapBound A : ENNReal) *
          source.enncard := by
    have hnatural :=
      pureWZ2_active_complete_fiber_incidence_sum_le
        hdelta hA fine scaleData hscaleSmall oneScale
          monochromatic.selectedCoarse
    calc
      (∑ parent, ambient parent) =
          ((∑ parent : Fin monochromatic.selectedCoarse.family.card,
            (scaleData.fullFiberIndices
              (oneScale.originalParent
                (monochromatic.selectedCoarse.embedding parent))).card :
              ℕ) : ENNReal) := by
        rw [Nat.cast_sum]
      _ ≤
          ((pureWZ2CompleteFiberOverlapBound A * source.card :
            ℕ) : ENNReal) := by
        exact_mod_cast hnatural
      _ =
          (pureWZ2CompleteFiberOverlapBound A : ENNReal) *
            source.enncard := by
        rw [Nat.cast_mul]
        rfl
  have hstrictSum :
      (∑ parent, strict parent) =
        selected.family.enncard := by
    exact
      monochromatic.cover.sum_fullFiberCount
        (show 0 ≤ 8 * A * scale.1 by
          have hscale : 0 < scale.1 :=
            hdelta.trans_le scale.property.1
          positivity)
  have hretained :
      (∑ parent, ambient parent) ≤
        ((pureWZ2CompleteFiberOverlapBound A : ENNReal) *
          retentionConstant) *
          ∑ parent, strict parent := by
    calc
      (∑ parent, ambient parent) ≤
          (pureWZ2CompleteFiberOverlapBound A : ENNReal) *
            source.enncard :=
        hambientSum
      _ ≤
          (pureWZ2CompleteFiberOverlapBound A : ENNReal) *
            (retentionConstant * selected.family.enncard) := by
        gcongr
      _ =
          ((pureWZ2CompleteFiberOverlapBound A : ENNReal) *
            retentionConstant) *
            ∑ parent, strict parent := by
        rw [hstrictSum]
        ring
  intro parent
  letI : Nonempty
      (Fin monochromatic.selectedCoarse.family.card) :=
    ⟨parent⟩
  exact
    finite_uniform_fiber_ratio
      ambient strict constant degreeConstant
      ((pureWZ2CompleteFiberOverlapBound A : ENNReal) *
        retentionConstant)
      hambientUniform hstrictUniform hretained parent

end Kakeya.Assouad

end
