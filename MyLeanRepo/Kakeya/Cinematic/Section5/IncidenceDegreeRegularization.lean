import MyLeanRepo.Kakeya.Cinematic.Section5.IncidenceDegreeRegularizationInputs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Max

/-!
# Regularize coarse-parent incidence degrees

This is the finite dyadic pigeonholing step preceding PYZ Lemma 47.
-/

namespace Kakeya.Cinematic

private lemma incidence_degree_pigeonhole
    {α : Type*} [DecidableEq α]
    (elements : Finset α) (level : α → ℕ) (maximum : ℕ)
    (hlevel : ∀ element ∈ elements, level element ≤ maximum) :
    ∃ selectedLevel : ℕ,
      selectedLevel ≤ maximum ∧
      elements.card ≤
        (maximum + 1) *
          (elements.filter fun element =>
            level element = selectedLevel).card := by
  let levels := Finset.range (maximum + 1)
  let fiberCard : ℕ → ℕ := fun selectedLevel =>
    (elements.filter fun element =>
      level element = selectedLevel).card
  have hsum :
      ∑ selectedLevel ∈ levels, fiberCard selectedLevel =
        elements.card := by
    have hfilter :
        ∑ selectedLevel ∈ levels, fiberCard selectedLevel =
          (elements.filter fun element =>
            level element ∈ levels).card :=
      Finset.sum_card_fiberwise_eq_card_filter
        elements levels level
    rw [hfilter]
    have hall :
        elements.filter (fun element => level element ∈ levels) =
          elements := by
      apply Finset.filter_true_of_mem
      intro element helement
      have h := hlevel element helement
      simp only [levels, Finset.mem_range]
      exact Nat.lt_succ_of_le h
    rw [hall]
  have hlevels_nonempty : levels.Nonempty := by
    simp [levels]
  obtain ⟨selectedLevel, hselectedLevel, hmax⟩ :=
    Finset.exists_max_image levels fiberCard hlevels_nonempty
  have hselectedLevel_le : selectedLevel ≤ maximum := by
    simp only [levels, Finset.mem_range] at hselectedLevel
    exact Nat.lt_succ_iff.mp hselectedLevel
  have hsum_le :
      ∑ candidate ∈ levels, fiberCard candidate ≤
        levels.card * fiberCard selectedLevel := by
    calc
      ∑ candidate ∈ levels, fiberCard candidate ≤
          ∑ _candidate ∈ levels, fiberCard selectedLevel :=
        Finset.sum_le_sum fun candidate hcandidate =>
          hmax candidate hcandidate
      _ = levels.card * fiberCard selectedLevel := by
        simp [Finset.sum_const]
  have hfinal :
      elements.card ≤
        (maximum + 1) * fiberCard selectedLevel := by
    have hlevels_card : levels.card = maximum + 1 := by
      simp [levels]
    rw [hlevels_card] at hsum_le
    rw [← hsum]
    exact hsum_le
  exact ⟨selectedLevel, hselectedLevel_le, hfinal⟩

theorem incidence_degree_regularization :
    IncidenceDegreeRegularizationStatement := by
  intro α β γ _ _ _ _ edges parent hedges
  let degree : (α × β) → ℕ := fun edge =>
    incidenceDegree edges parent edge.1 (parent edge.2)
  have hdegree_pos : ∀ edge ∈ edges, 0 < degree edge := by
    intro edge hedge
    simp only [degree, incidenceDegree]
    have hmem :
        edge ∈ edges.filter (fun candidate : α × β =>
          candidate.1 = edge.1 ∧
            parent candidate.2 = parent edge.2) :=
      Finset.mem_filter.mpr ⟨hedge, by simp⟩
    exact Finset.card_pos.mpr ⟨edge, hmem⟩
  have hdegree_le :
      ∀ edge ∈ edges, degree edge ≤ Fintype.card β := by
    intro edge _
    simp only [degree, incidenceDegree]
    let fiber := edges.filter (fun candidate : α × β =>
      candidate.1 = edge.1 ∧
        parent candidate.2 = parent edge.2)
    have hinjective :
        Set.InjOn Prod.snd (fiber : Set (α × β)) := by
      intro left hleft right hright hsnd
      have hleft_fst : left.1 = edge.1 :=
        (Finset.mem_filter.mp hleft).2.1
      have hright_fst : right.1 = edge.1 :=
        (Finset.mem_filter.mp hright).2.1
      have hfst : left.1 = right.1 := by
        rw [hleft_fst, hright_fst]
      exact Prod.ext hfst (by simpa using hsnd)
    have hcard :
        fiber.card = (fiber.image Prod.snd).card := by
      rw [Finset.card_image_of_injOn hinjective]
    rw [hcard]
    exact Finset.card_le_card (Finset.subset_univ _)
  let maximum := Nat.log2 (Fintype.card β)
  let level : (α × β) → ℕ := fun edge =>
    Nat.log2 (degree edge)
  have hlevel :
      ∀ edge ∈ edges, level edge ≤ maximum := by
    intro edge hedge
    have hle : degree edge ≤ Fintype.card β :=
      hdegree_le edge hedge
    have hlog :
        Nat.log 2 (degree edge) ≤
          Nat.log 2 (Fintype.card β) :=
      Nat.log_mono_right hle
    simpa only [level, maximum, Nat.log2_eq_log_two] using hlog
  obtain ⟨selectedLevel, hselectedLevel, hcard⟩ :=
    incidence_degree_pigeonhole edges level maximum hlevel
  let selected := edges.filter (fun edge =>
    2 ^ selectedLevel ≤ degree edge ∧
      degree edge < 2 ^ (selectedLevel + 1))
  have hlevel_iff :
      ∀ edge ∈ edges,
        (2 ^ selectedLevel ≤ degree edge ∧
            degree edge < 2 ^ (selectedLevel + 1)) ↔
          level edge = selectedLevel := by
    intro edge hedge
    have hpositive : 0 < degree edge := hdegree_pos edge hedge
    have hne : degree edge ≠ 0 := hpositive.ne'
    have hlevel_eq :
        level edge = Nat.log 2 (degree edge) := by
      simp only [level, Nat.log2_eq_log_two]
    constructor
    · rintro ⟨hlower, hupper⟩
      rw [hlevel_eq]
      exact Nat.log_eq_of_pow_le_of_lt_pow hlower hupper
    · intro heq
      have hlog : Nat.log 2 (degree edge) = selectedLevel := by
        rw [← hlevel_eq, heq]
      exact
        (Nat.log_eq_iff
          (Or.inr ⟨by decide, hne⟩)).mp hlog
  have hselected_eq :
      selected =
        edges.filter (fun edge =>
          level edge = selectedLevel) := by
    ext edge
    simp only [selected, Finset.mem_filter]
    by_cases hedge : edge ∈ edges
    · simp [hedge, hlevel_iff edge hedge]
    · simp [hedge]
  have hcard_selected :
      edges.card ≤
        (maximum + 1) * selected.card := by
    rw [hselected_eq]
    exact hcard
  have hregular :
      ∀ function coarse,
        incidenceDegree selected parent function coarse = 0 ∨
          (2 ^ selectedLevel ≤
              incidenceDegree selected parent function coarse ∧
            incidenceDegree selected parent function coarse <
              2 ^ (selectedLevel + 1)) := by
    intro function coarse
    by_cases hpositive :
        incidenceDegree selected parent function coarse > 0
    · right
      let selectedFiber := selected.filter (fun edge : α × β =>
        edge.1 = function ∧ parent edge.2 = coarse)
      let originalFiber := edges.filter (fun edge : α × β =>
        edge.1 = function ∧ parent edge.2 = coarse)
      have hselectedFiber_nonempty : selectedFiber.Nonempty := by
        simpa [incidenceDegree, selectedFiber] using
          Finset.card_pos.mp hpositive
      obtain ⟨edge, hedge⟩ := hselectedFiber_nonempty
      have hedge_selected : edge ∈ selected :=
        (Finset.mem_filter.mp hedge).1
      have hedge_fiber :
          edge.1 = function ∧ parent edge.2 = coarse :=
        (Finset.mem_filter.mp hedge).2
      have hselected_sub : selected ⊆ edges :=
        Finset.filter_subset _ _
      have hedge_original : edge ∈ edges :=
        hselected_sub hedge_selected
      let originalDegree :=
        incidenceDegree edges parent function coarse
      have hedge_degree :
          degree edge = originalDegree := by
        simp only [degree, originalDegree, hedge_fiber]
      have hrange :
          2 ^ selectedLevel ≤ originalDegree ∧
            originalDegree < 2 ^ (selectedLevel + 1) := by
        have hfilter :
            2 ^ selectedLevel ≤ degree edge ∧
              degree edge < 2 ^ (selectedLevel + 1) :=
          (Finset.mem_filter.mp hedge_selected).2
        rwa [hedge_degree] at hfilter
      have horiginalFiber_sub : originalFiber ⊆ selected := by
        intro candidate hcandidate
        have hcandidate_original : candidate ∈ edges :=
          (Finset.mem_filter.mp hcandidate).1
        have hcandidate_fiber :
            candidate.1 = function ∧
              parent candidate.2 = coarse :=
          (Finset.mem_filter.mp hcandidate).2
        have hcandidate_degree :
            degree candidate = originalDegree := by
          simp only [degree, originalDegree, hcandidate_fiber]
        have hfilter :
            2 ^ selectedLevel ≤ degree candidate ∧
              degree candidate < 2 ^ (selectedLevel + 1) := by
          rwa [hcandidate_degree]
        exact Finset.mem_filter.mpr
          ⟨hcandidate_original, hfilter⟩
      have hfiber_eq : selectedFiber = originalFiber := by
        ext candidate
        simp only [selectedFiber, originalFiber, Finset.mem_filter]
        constructor
        · rintro ⟨hcandidate_selected, hcandidate_fiber⟩
          exact ⟨hselected_sub hcandidate_selected, hcandidate_fiber⟩
        · rintro ⟨hcandidate_original, hcandidate_fiber⟩
          have hcandidate_selected : candidate ∈ selected :=
            horiginalFiber_sub <|
              Finset.mem_filter.mpr
                ⟨hcandidate_original, hcandidate_fiber⟩
          exact ⟨hcandidate_selected, hcandidate_fiber⟩
      have hdegree_eq :
          incidenceDegree selected parent function coarse =
            originalDegree := by
        simp [incidenceDegree, selectedFiber, originalFiber, hfiber_eq]
        rfl
      rw [hdegree_eq]
      exact hrange
    · left
      simpa using hpositive
  exact
    ⟨selectedLevel, selected, hselectedLevel, rfl,
      hcard_selected, hregular⟩

end Kakeya.Cinematic
