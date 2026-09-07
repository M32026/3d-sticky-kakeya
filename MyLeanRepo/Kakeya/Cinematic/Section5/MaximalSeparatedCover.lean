import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Topology.MetricSpace.Basic

/-!
# Maximal t-separated subset that t-covers a finite set

Given a finite set `S` in a metric space and `t > 0`, there exists a subset
`centers ⊆ S` that is strictly `t`-separated and `t`-covers `S`.

This is a standard greedy/packing argument: among all `t`-separated subsets of
`S`, choose one of maximum cardinality. Maximality forces every point of `S` to
be within distance `t` of some selected center.
-/

namespace Kakeya.Cinematic

variable {α : Type*} [MetricSpace α]

/--
A finite set `S` admits a subset `centers` that is strictly `t`-separated and
`t`-covers `S`.
-/
lemma exists_maximal_separated_cover
    {S : Finset α} {t : ℝ} (ht : 0 < t) :
    ∃ (centers : Finset α),
      centers ⊆ S ∧
      (∀ c ∈ centers, ∀ d ∈ centers, c ≠ d → t < dist c d) ∧
      (∀ x ∈ S, ∃ c ∈ centers, dist x c ≤ t) := by
  classical
  let P : Finset α → Prop := fun C =>
    C ⊆ S ∧ ∀ c ∈ C, ∀ d ∈ C, c ≠ d → t < dist c d
  have hP_empty : P ∅ := by
    simp [P]
  let candidates : Finset (Finset α) := S.powerset.filter P
  have h_candidates_nonempty : candidates.Nonempty := by
    refine ⟨∅, ?_⟩
    rw [Finset.mem_filter]
    exact ⟨Finset.empty_mem_powerset S, hP_empty⟩
  have h_main : ∃ (C : Finset α), C ∈ candidates ∧
      ∀ (D : Finset α), D ∈ candidates → D.card ≤ C.card := by
    exact Finset.exists_max_image candidates (fun C : Finset α => C.card) h_candidates_nonempty
  rcases h_main with ⟨centers, hcenters_in, hcenters_max⟩
  have hP_centers : P centers := (Finset.mem_filter.mp hcenters_in).2
  have h_sub : centers ⊆ S := hP_centers.1
  have h_sep : ∀ c ∈ centers, ∀ d ∈ centers, c ≠ d → t < dist c d :=
    hP_centers.2
  have h_cover : ∀ x ∈ S, ∃ c ∈ centers, dist x c ≤ t := by
    intro x hx
    by_cases hxc : x ∈ centers
    · exact ⟨x, hxc, by
        have h : dist x x = 0 := dist_self x
        rw [h]
        exact ht.le⟩
    · by_cases h_uncov : (∀ c ∈ centers, t < dist x c)
      · have h_insert_sep : ∀ c ∈ insert x centers, ∀ d ∈ insert x centers,
            c ≠ d → t < dist c d := by
          intro c hc d hd hne
          have h_c : c = x ∨ c ∈ centers := by
            simpa [Finset.mem_insert] using hc
          have h_d : d = x ∨ d ∈ centers := by
            simpa [Finset.mem_insert] using hd
          cases h_c with
          | inl h_eq_c =>
            cases h_d with
            | inl h_eq_d =>
              exfalso
              have h_eq : c = d := by rw [h_eq_c, h_eq_d]
              exact hne h_eq
            | inr hd2 =>
              rw [h_eq_c]
              exact h_uncov d hd2
          | inr hc2 =>
            cases h_d with
            | inl h_eq_d =>
              rw [h_eq_d]
              have h' : t < dist x c := h_uncov c hc2
              have h'' : dist x c = dist c x := dist_comm x c
              exact h'' ▸ h'
            | inr hd2 =>
              exact h_sep c hc2 d hd2 hne
        have h_insert_sub : insert x centers ⊆ S := by
          intro y hy
          have h_y : y = x ∨ y ∈ centers := by
            simpa [Finset.mem_insert] using hy
          rcases h_y with (rfl | hy2)
          · exact hx
          · exact h_sub hy2
        have hP_insert : P (insert x centers) :=
          ⟨h_insert_sub, h_insert_sep⟩
        have h_insert_in_candidates : insert x centers ∈ candidates := by
          rw [Finset.mem_filter]
          exact ⟨Finset.mem_powerset.mpr h_insert_sub, hP_insert⟩
        have h_card : (insert x centers).card = centers.card + 1 :=
          Finset.card_insert_of_notMem hxc
        have h_contra := hcenters_max (insert x centers) h_insert_in_candidates
        rw [h_card] at h_contra
        omega
      · have h_exists : ∃ c ∈ centers, dist x c ≤ t := by
          simpa [not_lt] using h_uncov
        exact h_exists
  exact ⟨centers, h_sub, h_sep, h_cover⟩

end Kakeya.Cinematic
