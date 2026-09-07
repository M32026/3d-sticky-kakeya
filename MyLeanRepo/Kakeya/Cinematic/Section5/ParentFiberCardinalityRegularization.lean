import MyLeanRepo.Kakeya.Cinematic.Section5.ParentFiberCardinalityRegularizationInputs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Max

/-!
# Regularize selected fine rectangles per coarse parent
-/

namespace Kakeya.Cinematic

private lemma parent_fiber_mul_sum
    {α : Type*} [DecidableEq α]
    (elements : Finset α) (factor : ℕ) (weight : α → ℕ) :
    ∑ element ∈ elements, factor * weight element =
      factor * ∑ element ∈ elements, weight element := by
  induction elements using Finset.induction with
  | empty =>
      simp
  | @insert element elements helement ih =>
      have hleft :
          ∑ index ∈ insert element elements, factor * weight index =
            factor * weight element +
              ∑ index ∈ elements, factor * weight index := by
        rw [Finset.sum_insert helement]
      have hright :
          ∑ index ∈ insert element elements, weight index =
            weight element + ∑ index ∈ elements, weight index := by
        rw [Finset.sum_insert helement]
      rw [hleft, hright, ih]
      exact
        (Nat.mul_add factor (weight element)
          (∑ index ∈ elements, weight index)).symm

theorem parent_fiber_cardinality_regularization :
    ParentFiberCardinalityRegularizationStatement := by
  intro β γ _ _ rectangles parent hrectangles
  let label : β → ℕ := fun rectangle =>
    Nat.log2
      ((parentFiber rectangles parent (parent rectangle)).card)
  let levelCount := Nat.log2 rectangles.card + 1
  let classCard : ℕ → ℕ := fun level =>
    (rectangles.filter fun rectangle =>
      label rectangle = level).card

  have hfiber_nonempty :
      ∀ rectangle ∈ rectangles,
        (parentFiber rectangles parent
          (parent rectangle)).Nonempty := by
    intro rectangle hrectangle
    exact
      ⟨rectangle,
        Finset.mem_filter.mpr ⟨hrectangle, rfl⟩⟩

  have hfiber_pos :
      ∀ rectangle ∈ rectangles,
        0 < (parentFiber rectangles parent
          (parent rectangle)).card := by
    intro rectangle hrectangle
    exact Finset.Nonempty.card_pos
      (hfiber_nonempty rectangle hrectangle)

  have hfiber_le :
      ∀ rectangle ∈ rectangles,
        (parentFiber rectangles parent
          (parent rectangle)).card ≤ rectangles.card := by
    intro rectangle _
    apply Finset.card_le_card
    intro candidate hcandidate
    exact (Finset.mem_filter.mp hcandidate).1

  have hlabel_le :
      ∀ rectangle ∈ rectangles,
        label rectangle ≤ Nat.log2 rectangles.card := by
    intro rectangle hrectangle
    have hle :=
      hfiber_le rectangle hrectangle
    simp only [label, Nat.log2_eq_log_two]
    exact Nat.log_mono_right hle

  have hlabel_lt :
      ∀ rectangle ∈ rectangles,
        label rectangle < levelCount := by
    intro rectangle hrectangle
    exact Nat.lt_succ_of_le (hlabel_le rectangle hrectangle)

  have hlabel_mem :
      ∀ rectangle ∈ rectangles,
        label rectangle ∈ Finset.range levelCount := by
    intro rectangle hrectangle
    exact Finset.mem_range.mpr (hlabel_lt rectangle hrectangle)

  have hsum :
      rectangles.card =
        ∑ level ∈ Finset.range levelCount, classCard level := by
    have h :
        ∑ level ∈ Finset.range levelCount, classCard level =
          (rectangles.filter fun rectangle =>
            label rectangle ∈ Finset.range levelCount).card :=
      Finset.sum_card_fiberwise_eq_card_filter
        rectangles (Finset.range levelCount) label
    have hall :
        rectangles.filter (fun rectangle =>
          label rectangle ∈ Finset.range levelCount) =
            rectangles :=
      Finset.filter_true_of_mem hlabel_mem
    rw [hall] at h
    exact h.symm

  have hlevelCount_pos : 0 < levelCount := by
    obtain ⟨rectangle, hrectangle⟩ := hrectangles
    have h := hlabel_lt rectangle hrectangle
    exact Nat.pos_of_ne_zero fun hzero => by
      rw [hzero] at h
      simp at h

  have hrange_nonempty :
      (Finset.range levelCount).Nonempty :=
    Finset.nonempty_range_iff.mpr hlevelCount_pos.ne'

  have hpigeonhole :
      ∃ level ∈ Finset.range levelCount,
        rectangles.card ≤ levelCount * classCard level := by
    by_contra hnot
    push Not at hnot
    let deficit : ℕ → ℕ := fun level =>
      rectangles.card - levelCount * classCard level
    have hle :
        ∀ level ∈ Finset.range levelCount,
          levelCount * classCard level ≤ rectangles.card :=
      fun level hlevel => (hnot level hlevel).le
    have hdeficit_pos :
        ∀ level ∈ Finset.range levelCount,
          0 < deficit level := by
      intro level hlevel
      exact Nat.sub_pos_of_lt (hnot level hlevel)
    obtain ⟨firstLevel, hfirstLevel⟩ := hrange_nonempty
    have hsingleton :
        ({firstLevel} : Finset ℕ) ⊆ Finset.range levelCount := by
      simp [hfirstLevel]
    have hsplit :
        ∑ level ∈ Finset.range levelCount, deficit level =
          ∑ level ∈
              (Finset.range levelCount \ {firstLevel}),
              deficit level +
            deficit firstLevel := by
      have h :=
        Finset.sum_sdiff hsingleton (f := deficit)
      simpa [Finset.sum_singleton] using h.symm
    have hdeficit_sum_pos :
        0 < ∑ level ∈ Finset.range levelCount, deficit level := by
      rw [hsplit]
      exact Nat.add_pos_right _
        (hdeficit_pos firstLevel hfirstLevel)
    have hpointwise :
        ∀ level ∈ Finset.range levelCount,
          levelCount * classCard level + deficit level =
            rectangles.card := by
      intro level hlevel
      dsimp only [deficit]
      exact Nat.add_sub_of_le (hle level hlevel)
    have hsum_pointwise :
        ∑ level ∈ Finset.range levelCount,
            (levelCount * classCard level + deficit level) =
          ∑ _level ∈ Finset.range levelCount,
            rectangles.card := by
      apply Finset.sum_congr rfl
      intro level hlevel
      exact hpointwise level hlevel
    have hsum_add :
        ∑ level ∈ Finset.range levelCount,
            (levelCount * classCard level + deficit level) =
          (∑ level ∈ Finset.range levelCount,
              levelCount * classCard level) +
            ∑ level ∈ Finset.range levelCount,
              deficit level := by
      rw [Finset.sum_add_distrib]
    have hsum_weight :
        ∑ level ∈ Finset.range levelCount,
            levelCount * classCard level =
          levelCount * rectangles.card := by
      rw [parent_fiber_mul_sum
        (Finset.range levelCount) levelCount classCard, hsum]
    have hsum_const :
        ∑ _level ∈ Finset.range levelCount,
            rectangles.card =
          levelCount * rectangles.card := by
      simp [Finset.sum_const]
    rw [hsum_add, hsum_weight, hsum_const] at hsum_pointwise
    have hstrict :
        levelCount * rectangles.card <
          levelCount * rectangles.card +
            ∑ level ∈ Finset.range levelCount,
              deficit level :=
      Nat.lt_add_of_pos_right hdeficit_sum_pos
    rw [hsum_pointwise] at hstrict
    exact lt_irrefl _ hstrict

  obtain ⟨level, hlevel_mem, hlevel_card⟩ := hpigeonhole

  have hlevel_le :
      level ≤ Nat.log2 rectangles.card := by
    exact Nat.le_of_lt_succ (Finset.mem_range.mp hlevel_mem)

  let selectedParents : Finset γ :=
    (parentSupport rectangles parent).filter fun coarse =>
      2 ^ level ≤ (parentFiber rectangles parent coarse).card ∧
        (parentFiber rectangles parent coarse).card <
          2 ^ (level + 1)

  have hparent_iff :
      ∀ rectangle ∈ rectangles,
        parent rectangle ∈ selectedParents ↔
          label rectangle = level := by
    intro rectangle hrectangle
    have hparent_support :
        parent rectangle ∈ parentSupport rectangles parent :=
      Finset.mem_image.mpr ⟨rectangle, hrectangle, rfl⟩
    have hpositive :=
      hfiber_pos rectangle hrectangle
    have hlog :
        Nat.log2
              ((parentFiber rectangles parent
                (parent rectangle)).card) = level ↔
          2 ^ level ≤
              (parentFiber rectangles parent
                (parent rectangle)).card ∧
            (parentFiber rectangles parent
              (parent rectangle)).card <
                2 ^ (level + 1) := by
      rw [Nat.log2_eq_log_two]
      exact Nat.log_eq_iff
        (Or.inr ⟨Nat.lt_succ_self 1, hpositive.ne'⟩)
    simp only [selectedParents, Finset.mem_filter,
      hparent_support, true_and, label]
    exact hlog.symm

  let selectedRectangles :=
    rectanglesOverParents rectangles parent selectedParents

  have hselectedRectangles :
      selectedRectangles =
        rectangles.filter (fun rectangle =>
          label rectangle = level) := by
    ext rectangle
    simp only [selectedRectangles, rectanglesOverParents,
      Finset.mem_filter]
    constructor
    · rintro ⟨hrectangle, hparent⟩
      exact ⟨hrectangle,
        (hparent_iff rectangle hrectangle).mp hparent⟩
    · rintro ⟨hrectangle, hlabel⟩
      exact ⟨hrectangle,
        (hparent_iff rectangle hrectangle).mpr hlabel⟩

  have hretention :
      rectangles.card ≤
        (Nat.log2 rectangles.card + 1) *
          selectedRectangles.card := by
    rw [hselectedRectangles]
    simpa [levelCount] using hlevel_card

  have hselectedParents_nonempty :
      selectedParents.Nonempty := by
    have hclassCard_pos : 0 < classCard level := by
      by_contra hnot
      have hzero : classCard level = 0 :=
        Nat.eq_zero_of_not_pos hnot
      rw [hzero] at hlevel_card
      have hcard_zero : rectangles.card ≤ 0 := by
        simpa using hlevel_card
      exact (not_le.mpr (Finset.Nonempty.card_pos hrectangles))
        hcard_zero
    have hselectedRectangles_nonempty :
        selectedRectangles.Nonempty := by
      apply Finset.card_pos.mp
      rw [hselectedRectangles]
      exact hclassCard_pos
    obtain ⟨rectangle, hrectangle⟩ :=
      hselectedRectangles_nonempty
    exact
      ⟨parent rectangle,
        (Finset.mem_filter.mp hrectangle).2⟩

  have hsum_selected :
      selectedRectangles.card =
        ∑ coarse ∈ selectedParents,
          (parentFiber rectangles parent coarse).card := by
    have h :
        ∑ coarse ∈ selectedParents,
            (parentFiber rectangles parent coarse).card =
          (rectangles.filter fun rectangle =>
            parent rectangle ∈ selectedParents).card :=
      Finset.sum_card_fiberwise_eq_card_filter
        rectangles selectedParents parent
    have heq :
        rectangles.filter (fun rectangle =>
          parent rectangle ∈ selectedParents) =
            selectedRectangles := by
      rfl
    rw [heq] at h
    exact h.symm

  have hrange :
      ∀ coarse ∈ selectedParents,
        2 ^ level ≤ (parentFiber rectangles parent coarse).card ∧
          (parentFiber rectangles parent coarse).card <
            2 ^ (level + 1) := by
    intro coarse hcoarse
    exact (Finset.mem_filter.mp hcoarse).2

  exact
    ⟨level, selectedParents, hlevel_le,
      hselectedParents_nonempty, rfl, hretention,
      hsum_selected, hrange⟩

end Kakeya.Cinematic
