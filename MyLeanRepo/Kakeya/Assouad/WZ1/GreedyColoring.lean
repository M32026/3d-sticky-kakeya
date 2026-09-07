import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Topology.MetricSpace.Basic

/-!
# Greedy coloring theorem

A finite simple graph with maximum degree at most `D` is `(D + 1)`-colorable.
-/

namespace SimpleGraph

variable {V : Type*} [Fintype V] {G : SimpleGraph V}
  [DecidableRel G.Adj]

theorem colorable_of_forall_degree_le {D : ℕ}
    (h : ∀ v, G.degree v ≤ D) :
    G.Colorable (D + 1) := by
  classical
  have h_main : ∀ (S : Finset V),
      ∃ f : V → Fin (D + 1),
        ∀ v ∈ S, ∀ w ∈ S, G.Adj v w → f v ≠ f w := by
    intro S
    induction S using Finset.strongInduction with
    | H S ih =>
      by_cases hS : S = ∅
      · refine ⟨fun _ => 0, ?_⟩
        simp [hS]
      · have hne : S.Nonempty :=
          Finset.nonempty_iff_ne_empty.mpr hS
        let z : V := hne.choose
        have hz : z ∈ S := hne.choose_spec
        let S' := S.erase z
        have hS' : S' ⊂ S := Finset.erase_ssubset hz
        obtain ⟨f, hf⟩ := ih S' hS'
        let usedColors : Finset (Fin (D + 1)) :=
          (S'.filter (fun x => G.Adj z x)).image f
        have h1 :
            usedColors.card ≤
              (S'.filter (fun x => G.Adj z x)).card :=
          Finset.card_image_le
        have h2 :
            (S'.filter (fun x => G.Adj z x)) ⊆
              G.neighborFinset z := by
          intro x hx
          have h_adj : G.Adj z x :=
            (Finset.mem_filter.mp hx).2
          simpa [G.mem_neighborFinset] using h_adj
        have h3 :
            (S'.filter (fun x => G.Adj z x)).card ≤
              G.degree z := by
          rw [← G.card_neighborFinset_eq_degree]
          exact Finset.card_le_card h2
        have h4 : usedColors.card ≤ D :=
          h1.trans (h3.trans (h z))
        have h5 :
            ∃ c : Fin (D + 1), c ∉ usedColors := by
          by_contra h6
          push Not at h6
          have h7 :
              (Finset.univ : Finset (Fin (D + 1))) ⊆
                usedColors :=
            fun x _ => h6 x
          have h8 :
              (Finset.univ : Finset (Fin (D + 1))).card ≤
                usedColors.card :=
            Finset.card_le_card h7
          simpa [Finset.card_fin] using h8.trans h4
        obtain ⟨c, hc⟩ := h5
        let f' : V → Fin (D + 1) :=
          Function.update f z c
        refine ⟨f', ?_⟩
        intro x hx y hy hxy
        by_cases hxz : x = z
        · subst hxz
          have hyz : y ≠ z := by
            intro h9
            rw [h9] at hxy
            exact G.loopless.irrefl z hxy
          have h_yS' : y ∈ S' := by
            simp only [S', Finset.mem_erase]
            exact ⟨hyz, hy⟩
          have h_yfilt :
              y ∈ S'.filter (fun x => G.Adj z x) := by
            simp only [Finset.mem_filter]
            exact ⟨h_yS', hxy⟩
          have h_fy : f y ∈ usedColors :=
            Finset.mem_image.mpr ⟨y, h_yfilt, rfl⟩
          have h_f'_y : f' y = f y := by
            simp [f', hyz]
          have h_f'_z : f' z = c := by
            simp [f']
          rw [h_f'_y, h_f'_z]
          intro h_cont
          exact hc (h_cont ▸ h_fy)
        · by_cases hyz : y = z
          · subst hyz
            have h_xS' : x ∈ S' := by
              simp only [S', Finset.mem_erase]
              exact ⟨hxz, hx⟩
            have h_adj' : G.Adj z x :=
              adj_symm G hxy
            have h_xfilt :
                x ∈ S'.filter (fun x => G.Adj z x) := by
              simp only [Finset.mem_filter]
              exact ⟨h_xS', h_adj'⟩
            have h_fx : f x ∈ usedColors :=
              Finset.mem_image.mpr ⟨x, h_xfilt, rfl⟩
            have h_f'_x : f' x = f x := by
              simp [f', hxz]
            have h_f'_z : f' z = c := by
              simp [f']
            rw [h_f'_x, h_f'_z]
            intro h_cont
            exact hc (h_cont ▸ h_fx)
          · have h_xS' : x ∈ S' := by
              simp only [S', Finset.mem_erase]
              exact ⟨hxz, hx⟩
            have h_yS' : y ∈ S' := by
              simp only [S', Finset.mem_erase]
              exact ⟨hyz, hy⟩
            have h_f'_x : f' x = f x := by
              simp [f', hxz]
            have h_f'_y : f' y = f y := by
              simp [f', hyz]
            rw [h_f'_x, h_f'_y]
            exact hf x h_xS' y h_yS' hxy
  obtain ⟨f, hf⟩ := h_main Finset.univ
  have h_valid :
      ∀ {v w : V}, G.Adj v w → f v ≠ f w := by
    intro v w h
    exact hf v (Finset.mem_univ v)
      w (Finset.mem_univ w) h
  exact ⟨Coloring.mk f h_valid⟩

end SimpleGraph

namespace Kakeya.Assouad

lemma nearby_cell_graph_degree_le
    {cellCount : ℕ} {α : Type*} [PseudoMetricSpace α]
    (active : Fin cellCount → Prop) [DecidablePred active]
    (representative : Fin cellCount → α)
    (rho : ℝ)
    (G : SimpleGraph (Fin cellCount)) [DecidableRel G.Adj]
    (hG : ∀ c d, G.Adj c d ↔
      c ≠ d ∧ active c ∧ active d ∧
        dist (representative c) (representative d) ≤ 6 * rho)
    (neighborBound : ℕ)
    (h_count : ∀ c, active c →
      (Finset.univ.filter fun d =>
        active d ∧
          dist (representative c) (representative d) ≤
            6 * rho).card ≤ neighborBound) :
    ∀ c : Fin cellCount,
      (G.neighborFinset c).card ≤ neighborBound := by
  intro c
  by_cases hc : active c
  · let S := Finset.univ.filter fun d : Fin cellCount =>
      active d ∧
        dist (representative c) (representative d) ≤ 6 * rho
    have h_neighbors : G.neighborFinset c ⊆ S.erase c := by
      intro d hd
      have h_adj : G.Adj c d :=
        (G.mem_neighborFinset c d).mp hd
      have h_spec := (hG c d).mp h_adj
      have h_ne : d ≠ c := Ne.symm h_spec.1
      have h_act : active d := h_spec.2.2.1
      have h_dist :
          dist (representative c) (representative d) ≤
            6 * rho :=
        h_spec.2.2.2
      simp only [S, Finset.mem_erase, Finset.mem_filter,
        Finset.mem_univ, true_and]
      exact ⟨h_ne, h_act, h_dist⟩
    have h_erase : S.erase c ⊆ S := by
      intro x hx
      exact Finset.mem_of_mem_erase hx
    calc
      (G.neighborFinset c).card ≤ (S.erase c).card :=
        Finset.card_le_card h_neighbors
      _ ≤ S.card := Finset.card_le_card h_erase
      _ ≤ neighborBound := h_count c hc
  · have h_no_neighbors : G.neighborFinset c = ∅ := by
      have h :
          G.neighborFinset c ⊆
            (∅ : Finset (Fin cellCount)) := by
        intro d hd
        have h_adj : G.Adj c d :=
          (G.mem_neighborFinset c d).mp hd
        have h_active_c : active c :=
          ((hG c d).mp h_adj).2.1
        exact False.elim (hc h_active_c)
      exact Finset.subset_empty.mp h
    rw [h_no_neighbors]
    <;> simp

end Kakeya.Assouad
