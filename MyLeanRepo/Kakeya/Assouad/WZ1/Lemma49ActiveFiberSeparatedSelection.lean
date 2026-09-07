import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma49ActiveFiberSeparatedSelectionStatements
import MyLeanRepo.Kakeya.Assouad.WZ1.SeparatedPointsExtraction

/-!
# WZ1 Lemma 49 separated selection on the actual active fiber

Extract a maximal `u`-separated subset from the supplied actual active `G₁`
fiber and derive the normalized cardinality bound from the ambient Frostman
estimate.
-/

namespace Kakeya.Assouad

theorem wz1_lemma49_active_fiber_separated_selection :
    WZ1Lemma49ActiveFiberSeparatedSelectionStatement := by
  intro F G₁ G₂ H density C base direction width activeWidth delta u viewpoint
    hdelta hdelta_u hu_one hG1
  classical
  have h_u_pos : 0 < u := by linarith
  have h_half_u_nonneg : 0 ≤ u / 2 := by linarith
  have h_two_half : 2 * (u / 2) = u := by ring
  rcases exists_maximal_separated_subset viewpoint.source (u / 2) h_half_u_nonneg with
    ⟨selected, h_selected_subset, h_selected_sep, h_selected_cover⟩
  have h_sep' : ∀ x ∈ selected, ∀ y ∈ selected, x ≠ y → dist x y ≥ u := by
    intro x hx y hy hne
    have h := h_selected_sep x hx y hy hne
    rw [h_two_half] at h
    exact h
  have h_separated : DiscreteSet.IsDeltaSeparated selected u := by
    intro x hx y hy hne
    exact h_sep' x hx y hy hne
  have h_cover' :
      ∀ n ∈ viewpoint.source, n ∈ selected ∨ ∃ p ∈ selected, dist n p < u := by
    intro n hn
    rcases h_selected_cover n hn with (h_in | ⟨p, hp, hdist⟩)
    · exact Or.inl h_in
    · have hdist' : dist n p < u := by
        rw [h_two_half] at hdist
        exact hdist
      exact Or.inr ⟨p, hp, hdist'⟩
  have h_covers_source :
      ∀ point ∈ viewpoint.source,
        ∃ selectedPoint ∈ selected, dist point selectedPoint < u := by
    intro point hpoint
    rcases h_cover' point hpoint with (h_in | ⟨p, hp, hdist⟩)
    · refine ⟨point, h_in, ?_⟩
      rw [dist_self]
      exact h_u_pos
    · exact ⟨p, hp, hdist⟩
  have h_selected_nonempty : selected.Nonempty := by
    rcases viewpoint.source_nonempty with ⟨x, hx⟩
    rcases h_covers_source x hx with ⟨p, hp, _⟩
    exact ⟨p, hp⟩
  have h_actual :
      ∀ second ∈ selected,
        (viewpoint.sourceEdge.1, second, viewpoint.viewpoint) ∈ H := by
    intro second hsecond
    exact viewpoint.source_actual second (h_selected_subset hsecond)
  have hG1_pos : 0 < G₁.enncard := by
    rcases viewpoint.source_nonempty with ⟨x, hx⟩
    have h_x_in_G1 : x ∈ G₁ := viewpoint.source_subset hx
    have h_G1_nonempty : G₁.Nonempty := ⟨x, h_x_in_G1⟩
    simpa [DiscreteSet.enncard] using Finset.card_pos.mpr h_G1_nonempty
  have hG1_ne_top : G₁.enncard ≠ ⊤ := by
    simp [DiscreteSet.enncard]
  have h_ballCount_mono :
      ∀ p ∈ selected,
        viewpoint.source.ballCount p u ≤ G₁.ballCount p u := by
    intro p _
    simp only [DiscreteSet.ballCount]
    have h_filter :
        viewpoint.source.filter (fun y => dist y p ≤ u) ⊆
          G₁.filter (fun y => dist y p ≤ u) :=
      Finset.filter_subset_filter _ viewpoint.source_subset
    have h_card :
        (viewpoint.source.filter (fun y => dist y p ≤ u)).card ≤
          (G₁.filter (fun y => dist y p ≤ u)).card :=
      Finset.card_le_card h_filter
    exact_mod_cast h_card
  have h_frostman_ball :
      ∀ p ∈ selected,
        G₁.ballCount p u ≤
          C * Kakeya.realRpowENN u 1 * G₁.enncard := by
    intro p _
    exact hG1 p u hdelta_u hu_one
  let B : Point2 → DiscreteSet 2 := fun p =>
    viewpoint.source.filter (fun y => dist y p ≤ u)
  have h_source_subset : viewpoint.source ⊆ selected.biUnion B := by
    intro x hx
    rcases h_covers_source x hx with ⟨p, hp, hdist⟩
    have hdist_le : dist x p ≤ u := by linarith
    have hxB : x ∈ B p := by
      simp only [B, Finset.mem_filter]
      exact ⟨hx, hdist_le⟩
    exact Finset.mem_biUnion.mpr ⟨p, hp, hxB⟩
  have h_cover_card :
      viewpoint.source.enncard ≤
        ∑ p ∈ selected, viewpoint.source.ballCount p u := by
    have h_union_card :
        viewpoint.source.card ≤ (selected.biUnion B).card :=
      Finset.card_le_card h_source_subset
    have h_sum_card :
        (selected.biUnion B).card ≤ ∑ p ∈ selected, (B p).card :=
      Finset.card_biUnion_le
    have h_card :
        viewpoint.source.card ≤ ∑ p ∈ selected, (B p).card :=
      h_union_card.trans h_sum_card
    simpa [DiscreteSet.enncard, DiscreteSet.ballCount, B] using mod_cast h_card
  let selected_enncard : ENNReal := (selected.card : ENNReal)
  have h_sum_bound :
      (∑ p ∈ selected, viewpoint.source.ballCount p u) ≤
        selected_enncard *
          (C * Kakeya.realRpowENN u 1 * G₁.enncard) := by
    calc
      (∑ p ∈ selected, viewpoint.source.ballCount p u)
          ≤ ∑ p ∈ selected,
              (C * Kakeya.realRpowENN u 1 * G₁.enncard) :=
        Finset.sum_le_sum fun p hp =>
          (h_ballCount_mono p hp).trans (h_frostman_ball p hp)
      _ = selected_enncard *
            (C * Kakeya.realRpowENN u 1 * G₁.enncard) := by
        simp [selected_enncard, Finset.sum_const, mul_assoc]
  have h_main :
      density * G₁.enncard ≤
        selected_enncard *
          (C * Kakeya.realRpowENN u 1 * G₁.enncard) :=
    viewpoint.source_density.trans (h_cover_card.trans h_sum_bound)
  have h_rearrange :
      selected_enncard *
          (C * Kakeya.realRpowENN u 1 * G₁.enncard) =
        (C * Kakeya.realRpowENN u 1 * selected_enncard) *
          G₁.enncard := by
    simp [mul_comm, mul_assoc, mul_left_comm]
  rw [h_rearrange] at h_main
  have h_main' :
      G₁.enncard * density ≤
        G₁.enncard *
          (C * Kakeya.realRpowENN u 1 * selected_enncard) := by
    simpa [mul_comm, mul_assoc] using h_main
  have h_cardinality :
      density ≤
        C * Kakeya.realRpowENN u 1 * selected_enncard :=
    (ENNReal.mul_le_mul_iff_right hG1_pos.ne' hG1_ne_top).mp h_main'
  exact
    ⟨
      { selected := selected
        selected_subset := h_selected_subset
        selected_nonempty := h_selected_nonempty
        separated := h_separated
        covers_source := h_covers_source
        actual := h_actual
        cardinality := h_cardinality }⟩

end Kakeya.Assouad
