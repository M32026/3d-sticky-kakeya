import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains

/-!
# Zero-extension of a shading from a tube subfamily

This closed utility module contains only the index re-embedding used to move
a shading on a genuine tube subfamily back to its ambient family.
-/

noncomputable section

namespace Kakeya.Assouad

open Metric Set MeasureTheory

attribute [local instance] Classical.propDecidable

/-- Carrier function for the ambient zero-extension. -/
noncomputable def extendShadingCarrier
    {delta : ℝ} {family : Kakeya.Streamlined.TubeFamily delta}
    (sub : Kakeya.Streamlined.TubeSubfamily family)
    (refined : WZ1PaperTubeShading sub.family)
    (i : Fin family.card) : Set Point3 :=
  if h : ∃ (j : Fin sub.family.card), sub.embedding j = i
  then refined.carrier (Classical.choose h)
  else ∅

lemma extendShadingCarrier.measurable
    {delta : ℝ} {family : Kakeya.Streamlined.TubeFamily delta}
    {sub : Kakeya.Streamlined.TubeSubfamily family}
    {refined : WZ1PaperTubeShading sub.family}
    (i : Fin family.card) :
    MeasurableSet (extendShadingCarrier sub refined i) := by
  unfold extendShadingCarrier
  by_cases h : ∃ (j : Fin sub.family.card), sub.embedding j = i
  · rw [dif_pos h]
    exact refined.measurable_carrier (Classical.choose h)
  · rw [dif_neg h]
    exact MeasurableSet.empty

lemma extendShadingCarrier.subset_body
    {delta : ℝ} {family : Kakeya.Streamlined.TubeFamily delta}
    {sub : Kakeya.Streamlined.TubeSubfamily family}
    {refined : WZ1PaperTubeShading sub.family}
    (i : Fin family.card) :
    extendShadingCarrier sub refined i ⊆
        Kakeya.Streamlined.Body.carrier ((wz1PaperBodyFamily family).body i) := by
  unfold extendShadingCarrier
  by_cases h : ∃ (j : Fin sub.family.card), sub.embedding j = i
  · rw [dif_pos h]
    let j : Fin sub.family.card := Classical.choose h
    have hj : sub.embedding j = i := Classical.choose_spec h
    have htube : sub.family.tube j = family.tube i := by
      rw [sub.tube_eq j, hj]
    have hsubset := refined.subset_body j
    simpa [wz1PaperBodyFamily, htube] using hsubset
  · rw [dif_neg h]
    exact Set.empty_subset _

/-- Extend a shading by the empty carrier outside the subfamily image. -/
noncomputable def extendShading
    {delta : ℝ} {family : Kakeya.Streamlined.TubeFamily delta}
    (sub : Kakeya.Streamlined.TubeSubfamily family)
    (refined : WZ1PaperTubeShading sub.family) :
    WZ1PaperTubeShading family :=
  { carrier := extendShadingCarrier sub refined
    measurable_carrier := extendShadingCarrier.measurable
    subset_body := extendShadingCarrier.subset_body }

lemma extendShading_carrier_mem
    {delta : ℝ} {family : Kakeya.Streamlined.TubeFamily delta}
    {sub : Kakeya.Streamlined.TubeSubfamily family}
    {refined : WZ1PaperTubeShading sub.family}
    {j : Fin sub.family.card} :
    (extendShading sub refined).carrier (sub.embedding j) =
      refined.carrier j := by
  have h : ∃ (k : Fin sub.family.card),
      sub.embedding k = sub.embedding j := ⟨j, rfl⟩
  have hchoose : Classical.choose h = j := by
    apply sub.embedding.inj'
    exact Classical.choose_spec h
  have hcarrier : (extendShading sub refined).carrier =
      extendShadingCarrier sub refined := by rfl
  have hgoal : (extendShading sub refined).carrier (sub.embedding j) =
      refined.carrier (Classical.choose h) := by
    rw [hcarrier]
    unfold extendShadingCarrier
    rw [dif_pos h]
    <;> rfl
  exact hgoal.trans (congr_arg refined.carrier hchoose)

lemma extendShading_carrier_empty
    {delta : ℝ} {family : Kakeya.Streamlined.TubeFamily delta}
    {sub : Kakeya.Streamlined.TubeSubfamily family}
    {refined : WZ1PaperTubeShading sub.family}
    {i : Fin family.card} (h : ¬ ∃ j, sub.embedding j = i) :
    (extendShading sub refined).carrier i = ∅ := by
  change extendShadingCarrier sub refined i = ∅
  rw [extendShadingCarrier, dif_neg h]

/-- A selected-family subshading zero-extends to an ambient subshading. -/
lemma extendShading_subshading
    {delta : ℝ} {family : Kakeya.Streamlined.TubeFamily delta}
    (sub : Kakeya.Streamlined.TubeSubfamily family)
    {refined : WZ1PaperTubeShading sub.family}
    {ambient : WZ1PaperTubeShading family}
    (hsub : ∀ index, refined.carrier index ⊆
      ambient.carrier (sub.embedding index)) :
    PaperIsSubshading (extendShading sub refined) ambient := by
  intro ambientIndex point pointMem
  by_cases imageMem : ∃ selectedIndex,
      sub.embedding selectedIndex = ambientIndex
  · rcases imageMem with ⟨selectedIndex, rfl⟩
    rw [extendShading_carrier_mem] at pointMem
    exact hsub selectedIndex pointMem
  · rw [extendShading_carrier_empty imageMem] at pointMem
    exact False.elim pointMem

lemma extendShading_union
    {delta : ℝ} {family : Kakeya.Streamlined.TubeFamily delta}
    (sub : Kakeya.Streamlined.TubeSubfamily family)
    (refined : WZ1PaperTubeShading sub.family) :
    (extendShading sub refined).union = refined.union := by
  ext point
  constructor
  · rintro ⟨index, hpoint⟩
    by_cases himage : ∃ selected, sub.embedding selected = index
    · rcases himage with ⟨selected, rfl⟩
      rw [extendShading_carrier_mem] at hpoint
      exact ⟨selected, hpoint⟩
    · rw [extendShading_carrier_empty himage] at hpoint
      exact False.elim hpoint
  · rintro ⟨selected, hpoint⟩
    exact ⟨sub.embedding selected, by
      rw [extendShading_carrier_mem]
      exact hpoint⟩

lemma extendShading_mass
    {delta : ℝ} {family : Kakeya.Streamlined.TubeFamily delta}
    (sub : Kakeya.Streamlined.TubeSubfamily family)
    (refined : WZ1PaperTubeShading sub.family) :
    (extendShading sub refined).mass = refined.mass := by
  let image : Finset (Fin family.card) :=
    Finset.image sub.embedding Finset.univ
  let weight : Fin family.card → ENNReal := fun index =>
    volume ((extendShading sub refined).carrier index)
  have houtside : ∀ index ∈ (Finset.univ : Finset (Fin family.card)),
      index ∉ image → weight index = 0 := by
    intro index _ hindex
    have himage : ¬ ∃ selected, sub.embedding selected = index := by
      simpa [image, Finset.mem_image] using hindex
    simp [weight, extendShading_carrier_empty himage]
  have hsum : ∑ index : Fin family.card, weight index =
      ∑ index ∈ image, weight index := by
    have hunion : image ∪
        ((Finset.univ : Finset (Fin family.card)) \ image) =
        Finset.univ := by simp
    have hdisjoint : Disjoint image
        ((Finset.univ : Finset (Fin family.card)) \ image) :=
      Finset.disjoint_sdiff
    have hcomplement :
        ∑ index ∈ ((Finset.univ : Finset (Fin family.card)) \ image),
          weight index = 0 := by
      apply Finset.sum_eq_zero
      intro index hindex
      exact houtside index (Finset.mem_univ index)
        (Finset.mem_sdiff.mp hindex).2
    have hsplit : ∑ index ∈ (Finset.univ : Finset (Fin family.card)),
          weight index =
        ∑ index ∈ image, weight index +
          ∑ index ∈ ((Finset.univ : Finset (Fin family.card)) \ image),
            weight index := by
      rw [← Finset.sum_union hdisjoint, hunion]
    simpa [hcomplement] using hsplit
  have hinjective : Set.InjOn sub.embedding
      (↑(Finset.univ : Finset (Fin sub.family.card)) :
        Set (Fin sub.family.card)) :=
    fun first _ second _ heq => sub.embedding.inj' heq
  have himageSum : ∑ index ∈ image, weight index =
      ∑ selected : Fin sub.family.card, weight (sub.embedding selected) :=
    Finset.sum_image (s := (Finset.univ : Finset (Fin sub.family.card)))
      (g := sub.embedding) (f := weight) hinjective
  change (∑ index : Fin family.card, weight index) =
    ∑ selected : Fin sub.family.card, volume (refined.carrier selected)
  rw [hsum, himageSum]
  apply Finset.sum_congr rfl
  intro selected _
  simp only [weight]
  rw [extendShading_carrier_mem]

end Kakeya.Assouad

end
