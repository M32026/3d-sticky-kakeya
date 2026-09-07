import MyLeanRepo.Kakeya.Cinematic.Section5.ShadingInputs

/-!
# Select a maximal incomparable fine rectangle family
-/

namespace Kakeya.Cinematic

theorem maximal_fine_rectangle_selection :
    MaximalFineRectangleSelectionStatement := by
  dsimp only [MaximalFineRectangleSelectionStatement]
  intro K delta t Delta C_R family E₂ hE₂ data N hbound
  classical
  let Candidate : ℕ → Prop := fun n =>
    ∃ source : Fin n → E₂,
      let rectangles : RectangleFamily delta (C_R * t * Delta / delta) := {
        card := n
        rectangle i := data.rectangle (source i)
      }
      rectangles.IsPairwiseIncomparable family 100
  have hCandidate_zero : Candidate 0 := by
    refine ⟨Fin.elim0, ?_⟩
    simp [RectangleFamily.IsPairwiseIncomparable]
  have hCandidate_bound : ∀ n, Candidate n → n ≤ N := by
    intro n hn
    rcases hn with ⟨source, hsource⟩
    let rectangles : RectangleFamily delta (C_R * t * Delta / delta) := {
      card := n
      rectangle i := data.rectangle (source i)
    }
    apply hbound rectangles
    · exact ⟨source, fun _ => rfl⟩
    · exact hsource
  let sizes : Finset ℕ := (Finset.range (N + 1)).filter Candidate
  have hsizes_nonempty : sizes.Nonempty := by
    refine ⟨0, ?_⟩
    simp [sizes, hCandidate_zero]
  rcases Finset.exists_max_image sizes id hsizes_nonempty with
    ⟨n, hn_sizes, hn_max⟩
  have hn_candidate : Candidate n := (Finset.mem_filter.mp hn_sizes).2
  rcases hn_candidate with ⟨source, hsource⟩
  let R : RectangleFamily delta (C_R * t * Delta / delta) := {
    card := n
    rectangle i := data.rectangle (source i)
  }
  have hR_incomparable : R.IsPairwiseIncomparable family 100 := hsource
  have hn_pos : 0 < n := by
    by_contra hn
    have hn_zero : n = 0 := Nat.eq_zero_of_not_pos hn
    rcases hE₂ with ⟨p, hp⟩
    let source' : Fin 1 → E₂ := fun _ => ⟨p, hp⟩
    let R' : RectangleFamily delta (C_R * t * Delta / delta) := {
      card := 1
      rectangle i := data.rectangle (source' i)
    }
    have hR'_incomparable : R'.IsPairwiseIncomparable family 100 := by
      intro i j hij
      exact (hij (Subsingleton.elim i j)).elim
    have hCandidate_one : Candidate 1 := ⟨source', hR'_incomparable⟩
    have hone_le_N : 1 ≤ N := hCandidate_bound 1 hCandidate_one
    have hone_sizes : 1 ∈ sizes := by
      simp only [sizes, Finset.mem_filter, Finset.mem_range, hCandidate_one, and_true]
      omega
    have := hn_max 1 hone_sizes
    simp [hn_zero] at this
  refine ⟨R, source, ?_⟩
  refine ⟨hn_pos, fun _ => rfl, ?_, ?_, hR_incomparable, ?_⟩
  · intro i
    rw [data.rectangle_function]
    exact data.center_mem (source i)
  · intro i
    exact data.rectangle_central (source i)
  · intro p
    by_contra hcover
    push Not at hcover
    let source' : Fin (n + 1) → E₂ := Fin.cons p source
    let R' : RectangleFamily delta (C_R * t * Delta / delta) := {
      card := n + 1
      rectangle i := data.rectangle (source' i)
    }
    have hR'_incomparable : R'.IsPairwiseIncomparable family 100 := by
      intro i j hij
      rcases Fin.eq_zero_or_eq_succ i with (rfl | ⟨i, rfl⟩)
      · rcases Fin.eq_zero_or_eq_succ j with (rfl | ⟨j, rfl⟩)
        · exact (hij rfl).elim
        · simpa only [R', source', R, Fin.cons_zero, Fin.cons_succ,
            CurvilinearRectangle.AreLambdaIncomparable] using (hcover j).2
      · rcases Fin.eq_zero_or_eq_succ j with (rfl | ⟨j, rfl⟩)
        · intro hcomp
          apply (hcover i).2
          rcases hcomp with ⟨U, hU_family, hU_cover⟩
          refine ⟨U, hU_family, ?_⟩
          simpa [R', source', Set.union_comm] using hU_cover
        · simpa only [R', source', R, Fin.cons_succ] using hR_incomparable i j (by
            exact fun h => hij (Fin.succ_inj.mpr h))
    have hCandidate_succ : Candidate (n + 1) :=
      ⟨source', hR'_incomparable⟩
    have hsucc_le_N : n + 1 ≤ N :=
      hCandidate_bound (n + 1) hCandidate_succ
    have hsucc_sizes : n + 1 ∈ sizes := by
      simp [sizes, hCandidate_succ, hsucc_le_N]
    have hmax := hn_max (n + 1) hsucc_sizes
    simp at hmax

end Kakeya.Cinematic
