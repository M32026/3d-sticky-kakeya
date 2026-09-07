import MyLeanRepo.Kakeya.Assouad.PropStickyInducedCoverCounting

/-! # Uniform counting for a quotient of two nested parent maps -/

noncomputable section

namespace Kakeya.Assouad

open scoped ENNReal

theorem nested_quotient_parent_count_uniform_square
    {Source Middle Coarse : Type*}
    [Fintype Source] [DecidableEq Source]
    [Fintype Middle] [DecidableEq Middle] [Nonempty Middle]
    [Fintype Coarse] [DecidableEq Coarse]
    (fineParent : Source → Middle)
    (coarseParent : Source → Coarse)
    (quotientParent : Middle → Coarse)
    (fine_surjective : Function.Surjective fineParent)
    (compatible :
      ∀ source,
        quotientParent (fineParent source) = coarseParent source)
    (C : ENNReal)
    (fine_uniform :
      ∀ first second,
        ((Finset.univ.filter fun source =>
            fineParent source = first).card : ENNReal) ≤
          C *
            ((Finset.univ.filter fun source =>
              fineParent source = second).card : ENNReal))
    (coarse_uniform :
      ∀ first second,
        ((Finset.univ.filter fun source =>
            coarseParent source = first).card : ENNReal) ≤
          C *
            ((Finset.univ.filter fun source =>
              coarseParent source = second).card : ENNReal)) :
    ∀ first second,
      ((Finset.univ.filter fun middle =>
          quotientParent middle = first).card : ENNReal) ≤
        C * C *
          ((Finset.univ.filter fun middle =>
            quotientParent middle = second).card : ENNReal) := by
  let children : Middle → ENNReal := fun middle =>
    (Finset.univ.filter fun source =>
      fineParent source = middle).card
  obtain ⟨reference, _, hreference⟩ :=
    Finset.exists_min_image
      (Finset.univ : Finset Middle) children Finset.univ_nonempty
  let minimum := children reference
  have hminimum_pos : 0 < minimum := by
    rcases fine_surjective reference with ⟨source, hsource⟩
    have hmem :
        source ∈
          (Finset.univ.filter fun current =>
            fineParent current = reference) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsource⟩
    have hcard :
        0 <
          (Finset.univ.filter fun current =>
            fineParent current = reference).card :=
      Finset.card_pos.mpr ⟨source, hmem⟩
    dsimp only [minimum, children]
    exact_mod_cast hcard
  have hminimum_top : minimum ≠ ⊤ := by
    simp [minimum, children]
  have hchildren_lower :
      ∀ middle, minimum ≤ children middle := by
    intro middle
    exact hreference middle (Finset.mem_univ middle)
  have hchildren_upper :
      ∀ middle, children middle ≤ C * minimum := by
    intro middle
    exact fine_uniform middle reference
  have hsum :
      ∀ coarse,
        (∑ middle ∈
            (Finset.univ.filter fun current =>
              quotientParent current = coarse),
            children middle) =
          ((Finset.univ.filter fun source =>
            coarseParent source = coarse).card : ENNReal) := by
    intro coarse
    let selectedMiddle : Finset Middle :=
      Finset.univ.filter fun current =>
        quotientParent current = coarse
    have hnatural :=
      Finset.sum_card_fiberwise_eq_card_filter
        (Finset.univ : Finset Source)
        selectedMiddle fineParent
    have hmaps :
        ∀ source ∈ (Finset.univ : Finset Source),
          fineParent source ∈ selectedMiddle ↔
            coarseParent source = coarse := by
      intro source _
      simp only [selectedMiddle, Finset.mem_filter,
        Finset.mem_univ, true_and]
      rw [compatible source]
    have hfilter :
        (Finset.univ.filter fun source =>
            fineParent source ∈ selectedMiddle) =
          Finset.univ.filter fun source =>
            coarseParent source = coarse := by
      ext source
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hmaps source (Finset.mem_univ source)
    change
      (∑ middle ∈ selectedMiddle,
          ((Finset.univ.filter fun source =>
            fineParent source = middle).card : ENNReal)) =
        ((Finset.univ.filter fun source =>
          coarseParent source = coarse).card : ENNReal)
    rw [← Nat.cast_sum]
    exact_mod_cast hnatural.trans (congrArg Finset.card hfilter)
  intro first second
  apply
    induced_parent_count_uniform_square
      children
      (Finset.univ.filter fun middle =>
        quotientParent middle = first)
      (Finset.univ.filter fun middle =>
        quotientParent middle = second)
      C minimum hminimum_pos hminimum_top
  · intro middle _
    exact hchildren_lower middle
  · intro middle _
    exact hchildren_upper middle
  · rw [hsum first, hsum second]
    exact coarse_uniform first second

end Kakeya.Assouad

end
