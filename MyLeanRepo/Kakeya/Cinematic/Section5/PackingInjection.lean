import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Data.Finset.Card

/-!
# Packing injection lemma

A strictly `t`-separated finite set whose points are covered by radius-`r` balls
with `2*r < t` injects into the set of ball centers, giving a cardinality bound.

This is used in the bounded-overlap ambient ball cover (PYZ Section 5.1.1):
a function in a triple-dilated ball can only be associated to `t`-separated
centers in a `4t` ball, and doubling bounds reduce the number of such centers.
-/

open Metric Finset

namespace Kakeya.Cinematic

/-- If a finite set of centers is strictly `t`-separated and each center lies in
some closed ball of radius `r` centered at a point of `balls`, with `2*r < t`,
then the number of centers is at most the number of balls. -/
lemma packing_injection {α : Type*} [MetricSpace α] {t r : ℝ}
    (_ht : 0 < t)
    (hr : 2 * r < t)
    (centers balls : Finset α)
    (h_sep : ∀ c ∈ centers, ∀ d ∈ centers, c ≠ d → t < dist c d)
    (h_cover : ∀ c ∈ centers, ∃ b ∈ balls, c ∈ closedBall b r) :
    centers.card ≤ balls.card := by
  by_cases h_empty : centers = ∅
  · rw [h_empty]
    simp
  · have h_ne : centers.Nonempty := Finset.nonempty_iff_ne_empty.mpr h_empty
    let c0 : α := Classical.choose h_ne
    classical
    let g : α → α := fun c =>
      if h : c ∈ centers then (h_cover c h).choose else c0
    have hg1 : ∀ c ∈ centers, g c ∈ balls := by
      intro c hc
      have hgc : g c = (h_cover c hc).choose := by
        simp [g, hc, dif_pos]
      rw [hgc]
      exact (h_cover c hc).choose_spec.1
    have hg2 : ∀ c ∈ centers, c ∈ closedBall (g c) r := by
      intro c hc
      have hgc : g c = (h_cover c hc).choose := by
        simp [g, hc, dif_pos]
      rw [hgc]
      exact (h_cover c hc).choose_spec.2
    have h_inj_on : Set.InjOn g (centers : Set α) := by
      intro c hc d hd h_eq
      have h1 : c ∈ closedBall (g c) r := hg2 c hc
      have h2 : d ∈ closedBall (g d) r := hg2 d hd
      have h3 : g c = g d := h_eq
      rw [h3] at h1
      have h1' : dist c (g d) ≤ r := h1
      have h2' : dist d (g d) ≤ r := h2
      have h2'' : dist (g d) d ≤ r := by
        rw [dist_comm]
        exact h2'
      have h4 : dist c d ≤ 2 * r := by
        calc dist c d
          ≤ dist c (g d) + dist (g d) d := dist_triangle _ _ _
        _ ≤ r + r := by linarith
        _ = 2 * r := by ring
      have h5 : dist c d < t := by linarith
      by_cases h : c = d
      · exact h
      · have h6 : t < dist c d := h_sep c hc d hd h
        linarith
    have h_image_card : (centers.image g).card = centers.card := by
      rw [Finset.card_image_of_injOn h_inj_on]
    have h_sub : centers.image g ⊆ balls := by
      intro x hx
      rcases Finset.mem_image.mp hx with ⟨c, hc, rfl⟩
      exact hg1 c hc
    have h_card : (centers.image g).card ≤ balls.card := Finset.card_le_card h_sub
    rw [h_image_card] at h_card
    exact h_card

end Kakeya.Cinematic
