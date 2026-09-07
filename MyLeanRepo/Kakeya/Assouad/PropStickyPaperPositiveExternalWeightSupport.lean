import MyLeanRepo.Kakeya.Assouad.PropStickyPaperPositiveExternalWeightSupportStatements

/-!
# Recover packed support from positive external source weights

Recover the unique packed index of every selected ambient target, prove
injectivity, and identify both the total and selected zero-extended weights.
-/

noncomputable section

namespace Kakeya.Assouad

theorem sum_wz2PaperZeroExtendedExternalWeight
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (packed : Kakeya.Streamlined.TubeSubfamily family)
    (sourceWeight : Fin packed.family.card → ENNReal) :
    (∑ ambient : Fin family.card,
        wz2PaperZeroExtendedExternalWeight
          packed sourceWeight ambient) =
      ∑ source : Fin packed.family.card, sourceWeight source := by
  simp only [wz2PaperZeroExtendedExternalWeight]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro source _
  have hfilter :
      (Finset.univ.filter
        (fun ambient : Fin family.card =>
          packed.embedding source = ambient)) =
        {packed.embedding source} := by
    ext ambient
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton]
    exact eq_comm
  rw [Finset.sum_ite]
  simp [hfilter]

theorem wz2PaperZeroExtendedExternalWeight_le
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (packed : Kakeya.Streamlined.TubeSubfamily family)
    (sourceWeight : Fin packed.family.card → ENNReal)
    (weightUpper : ENNReal)
    (hupper : ∀ source, sourceWeight source ≤ weightUpper) :
    ∀ ambient,
      wz2PaperZeroExtendedExternalWeight
          packed sourceWeight ambient ≤
        weightUpper := by
  intro ambient
  simp only [wz2PaperZeroExtendedExternalWeight]
  by_cases hmem :
      ∃ source : Fin packed.family.card,
        packed.embedding source = ambient
  · rcases hmem with ⟨source, hsource⟩
    have hiff :
        ∀ candidate : Fin packed.family.card,
          packed.embedding candidate = ambient ↔
            candidate = source := by
      intro candidate
      constructor
      · intro hcandidate
        apply packed.embedding.injective
        rw [hcandidate, hsource]
      · rintro rfl
        exact hsource
    have hfilter :
        (Finset.univ.filter
          (fun candidate : Fin packed.family.card =>
            packed.embedding candidate = ambient)) =
          {source} := by
      ext candidate
      simp [hiff candidate]
    rw [Finset.sum_ite]
    simp [hfilter, hupper source]
  · have hnone :
        ∀ source : Fin packed.family.card,
          packed.embedding source ≠ ambient := by
      intro source hsource
      exact hmem ⟨source, hsource⟩
    simp [hnone]

theorem wz2_paper_positive_external_weight_support :
    WZ2PaperPositiveExternalWeightSupportStatement := by
  intro delta family packed sourceWeight selected h_pos
  have h_main :
      ∀ index : Fin selected.family.card,
        ∃ source : Fin packed.family.card,
          packed.embedding source = selected.embedding index ∧
            0 < sourceWeight source := by
    intro index
    have h1 :
        0 < wz2PaperZeroExtendedExternalWeight
          packed sourceWeight (selected.embedding index) :=
      h_pos index
    simp only [wz2PaperZeroExtendedExternalWeight] at h1
    have h2 :
        ∃ x : Fin packed.family.card,
          x ∈ (Finset.univ : Finset (Fin packed.family.card)) ∧
            0 <
              (if packed.embedding x = selected.embedding index then
                sourceWeight x
              else 0) := by
      rw [Finset.sum_pos_iff] at h1
      exact h1
    rcases h2 with ⟨source, _, hsource⟩
    by_cases h :
        packed.embedding source = selected.embedding index
    · have hweight : 0 < sourceWeight source := by
        rw [if_pos h] at hsource
        exact hsource
      exact ⟨source, h, hweight⟩
    · rw [if_neg h] at hsource
      simp at hsource
  let packedIndex :
      Fin selected.family.card → Fin packed.family.card :=
    fun index => Classical.choose (h_main index)
  have h_ambient_eq :
      ∀ index,
        packed.embedding (packedIndex index) =
          selected.embedding index :=
    fun index => (Classical.choose_spec (h_main index)).1
  have h_injective : Function.Injective packedIndex := by
    intro first second heq
    have hselected :
        selected.embedding first = selected.embedding second := by
      calc
        selected.embedding first =
            packed.embedding (packedIndex first) :=
          (h_ambient_eq first).symm
        _ = packed.embedding (packedIndex second) := by rw [heq]
        _ = selected.embedding second := h_ambient_eq second
    exact selected.embedding.inj' hselected
  have h_point_weight_eq :
      ∀ index,
        wz2PaperZeroExtendedExternalWeight
            packed sourceWeight (selected.embedding index) =
          sourceWeight (packedIndex index) := by
    intro index
    simp only [wz2PaperZeroExtendedExternalWeight]
    set packedSource : Fin packed.family.card :=
      packedIndex index
    have hpacked :
        packed.embedding packedSource = selected.embedding index :=
      h_ambient_eq index
    have h_iff :
        ∀ source : Fin packed.family.card,
          packed.embedding source = selected.embedding index ↔
            source = packedSource := by
      intro source
      constructor
      · intro hsource
        have heq :
            packed.embedding source =
              packed.embedding packedSource := by
          rw [hsource, hpacked]
        exact packed.embedding.inj' heq
      · intro hsource
        rw [hsource, hpacked]
    have h_filter :
        (Finset.univ.filter
          (fun source : Fin packed.family.card =>
            packed.embedding source = selected.embedding index)) =
          {packedSource} := by
      ext source
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_singleton]
      exact h_iff source
    have h_sum :
        (∑ source : Fin packed.family.card,
          if packed.embedding source = selected.embedding index then
            sourceWeight source
          else 0) =
          ∑ source ∈
              (Finset.univ.filter
                (fun source =>
                  packed.embedding source =
                    selected.embedding index)),
            sourceWeight source := by
      rw [Finset.sum_ite]
      simp
    rw [h_sum, h_filter]
    simp
  have h_total_weight_eq :
      (∑ ambient : Fin family.card,
          wz2PaperZeroExtendedExternalWeight
            packed sourceWeight ambient) =
        ∑ source : Fin packed.family.card, sourceWeight source := by
    exact
      sum_wz2PaperZeroExtendedExternalWeight
        packed sourceWeight
  have h_selected_weight_eq :
      (∑ index : Fin selected.family.card,
          wz2PaperZeroExtendedExternalWeight
            packed sourceWeight (selected.embedding index)) =
        ∑ index : Fin selected.family.card,
          sourceWeight (packedIndex index) := by
    apply Finset.sum_congr rfl
    intro index _
    exact h_point_weight_eq index
  exact
    ⟨packedIndex, h_injective, h_ambient_eq,
      h_point_weight_eq, h_total_weight_eq,
      h_selected_weight_eq⟩

end Kakeya.Assouad

end
