import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12

/-!
# Generic weighted bounded-degree graph selection

This module contains only the finite combinatorics used by the localized
reanchored route: proper coloring and weighted independent-set selection for a
symmetric irreflexive relation of uniformly bounded degree.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

private lemma pureWZ2_greedy_coloring_fin
    (n D : ℕ)
    (R : Fin n → Fin n → Prop)
    (hR_symm : ∀ i j, R i j → R j i)
    (hR_irrefl : ∀ i, ¬R i i)
    (hR_deg :
      ∀ i,
        (Finset.univ.filter fun j => R i j).card ≤ D) :
    ∃ color : Fin n → Fin (D + 1),
      ∀ i j, R i j → color i ≠ color j := by
  induction n with
  | zero =>
    exact ⟨Fin.elim0, fun i => Fin.elim0 i⟩
  | succ n inductionHypothesis =>
    let restricted : Fin n → Fin n → Prop := fun i j =>
      R (Fin.castSucc i) (Fin.castSucc j)
    have hrestrictedSymm :
        ∀ i j, restricted i j → restricted j i := by
      intro i j h
      exact hR_symm _ _ h
    have hrestrictedIrrefl :
        ∀ i, ¬restricted i i := by
      intro i
      exact hR_irrefl (Fin.castSucc i)
    have hrestrictedDegree :
        ∀ i : Fin n,
          (Finset.univ.filter fun j : Fin n =>
            restricted i j).card ≤ D := by
      intro i
      let embedding : Fin n → Fin (n + 1) := Fin.castSucc
      let source :=
        Finset.univ.filter fun j : Fin n =>
          restricted i j
      let target :=
        Finset.univ.filter fun k : Fin (n + 1) =>
          R (embedding i) k
      have hsubset :
          Finset.image embedding source ⊆ target := by
        intro k hk
        rcases Finset.mem_image.mp hk with
          ⟨j, hj, rfl⟩
        simpa [source, target, restricted, embedding] using hj
      have hcard :
          source.card =
            (Finset.image embedding source).card := by
        symm
        exact
          Finset.card_image_of_injective _
            (Fin.castSucc_injective n)
      rw [hcard]
      exact
        (Finset.card_le_card hsubset).trans
          (hR_deg (embedding i))
    rcases
        inductionHypothesis restricted
          hrestrictedSymm hrestrictedIrrefl
          hrestrictedDegree with
      ⟨oldColor, holdColor⟩
    let last : Fin (n + 1) := Fin.last n
    let neighbors : Finset (Fin n) :=
      Finset.univ.filter fun j : Fin n =>
        R (Fin.castSucc j) last
    let forbidden : Finset (Fin (D + 1)) :=
      neighbors.image oldColor
    have hlastDegree :
        (Finset.univ.filter fun k : Fin (n + 1) =>
          R k last).card ≤ D := by
      have heq :
          (Finset.univ.filter fun k : Fin (n + 1) =>
              R k last) =
            Finset.univ.filter fun k : Fin (n + 1) =>
              R last k := by
        ext k
        simp only [Finset.mem_filter,
          Finset.mem_univ, true_and]
        exact ⟨hR_symm _ _, hR_symm _ _⟩
      rw [heq]
      exact hR_deg last
    have hneighbors : neighbors.card ≤ D := by
      let embedding : Fin n → Fin (n + 1) := Fin.castSucc
      let target :=
        Finset.univ.filter fun k : Fin (n + 1) =>
          R k last
      have hsubset :
          Finset.image embedding neighbors ⊆ target := by
        intro k hk
        rcases Finset.mem_image.mp hk with
          ⟨j, hj, rfl⟩
        simpa [neighbors, target, embedding] using hj
      have hcard :
          neighbors.card =
            (Finset.image embedding neighbors).card := by
        symm
        exact
          Finset.card_image_of_injective _
            (Fin.castSucc_injective n)
      rw [hcard]
      exact
        (Finset.card_le_card hsubset).trans
          hlastDegree
    have hforbidden : forbidden.card ≤ D :=
      Finset.card_image_le.trans hneighbors
    have hexists :
        ∃ color : Fin (D + 1),
          color ∉ forbidden := by
      by_contra hnot
      push Not at hnot
      have hsubset :
          (Finset.univ : Finset (Fin (D + 1))) ⊆
            forbidden := by
        intro color _
        exact hnot color
      have hcard :=
        (Finset.card_le_card hsubset).trans
          hforbidden
      simp at hcard
    let newColor : Fin (D + 1) :=
      Classical.choose hexists
    have hnewColor : newColor ∉ forbidden :=
      Classical.choose_spec hexists
    let color : Fin (n + 1) → Fin (D + 1) := fun i =>
      if h : i.val < n then
        oldColor ⟨i.val, h⟩
      else
        newColor
    have hlast : color last = newColor := by
      have h : ¬last.val < n := by
        simp [last, Fin.last]
      simp [color, h]
    have hcast :
        ∀ i : Fin n,
          color (Fin.castSucc i) = oldColor i := by
      intro i
      simp [color, i.isLt]
    refine ⟨color, ?_⟩
    intro i j hrelation
    by_cases hi : i.val < n
    · by_cases hj : j.val < n
      · let i' : Fin n := ⟨i.val, hi⟩
        let j' : Fin n := ⟨j.val, hj⟩
        have hi' : i = Fin.castSucc i' := by
          apply Fin.ext
          rfl
        have hj' : j = Fin.castSucc j' := by
          apply Fin.ext
          rfl
        have hrestricted : restricted i' j' := by
          change
            R (Fin.castSucc i') (Fin.castSucc j')
          rw [← hi', ← hj']
          exact hrelation
        rw [hi', hj', hcast, hcast]
        exact holdColor i' j' hrestricted
      · have hjVal : j.val = n := by omega
        have hjLast : j = last := by
          apply Fin.ext
          simp [last, Fin.last, hjVal]
        let i' : Fin n := ⟨i.val, hi⟩
        have hi' : i = Fin.castSucc i' := by
          apply Fin.ext
          rfl
        have hneighbor : i' ∈ neighbors := by
          simp only [neighbors, Finset.mem_filter,
            Finset.mem_univ, true_and]
          simpa [hi', hjLast] using hrelation
        have hforbid : oldColor i' ∈ forbidden :=
          Finset.mem_image.mpr
            ⟨i', hneighbor, rfl⟩
        rw [hi', hjLast, hcast, hlast]
        exact fun heq =>
          hnewColor (heq ▸ hforbid)
    · have hiVal : i.val = n := by omega
      have hiLast : i = last := by
        apply Fin.ext
        simp [last, Fin.last, hiVal]
      rw [hiLast, hlast]
      by_cases hj : j.val < n
      · let j' : Fin n := ⟨j.val, hj⟩
        have hj' : j = Fin.castSucc j' := by
          apply Fin.ext
          rfl
        have hneighbor : j' ∈ neighbors := by
          simp only [neighbors, Finset.mem_filter,
            Finset.mem_univ, true_and]
          have hsymm :
              R j last := by
            exact
              hR_symm last j
                (by simpa [hiLast] using hrelation)
          simpa [hj'] using hsymm
        have hforbid : oldColor j' ∈ forbidden :=
          Finset.mem_image.mpr
            ⟨j', hneighbor, rfl⟩
        rw [hj', hcast]
        exact fun heq =>
          hnewColor (heq ▸ hforbid)
      · have hjVal : j.val = n := by omega
        have hjLast : j = last := by
          apply Fin.ext
          simp [last, Fin.last, hjVal]
        rw [hiLast, hjLast] at hrelation
        exact
          (hR_irrefl last hrelation).elim

/-- Proper coloring by `D + 1` colors. -/
lemma pureWZ2_greedy_proper_coloring
    {n D : ℕ}
    {relation : Fin n → Fin n → Prop}
    (hsymm :
      ∀ first second,
        relation first second →
          relation second first)
    (hirrefl :
      ∀ index, ¬relation index index)
    (hdegree :
      ∀ index,
        (Finset.univ.filter fun other =>
          relation index other).card ≤ D) :
    ∃ color : Fin n → Fin (D + 1),
      ∀ first second,
        relation first second →
          color first ≠ color second :=
  pureWZ2_greedy_coloring_fin
    n D relation hsymm hirrefl hdegree

private lemma pureWZ2_weighted_pigeonhole
    {n D : ℕ}
    (weight : Fin n → ENNReal)
    (color : Fin n → Fin (D + 1)) :
    ∃ best : Fin (D + 1),
      (∑ index : Fin n, weight index) ≤
        (D + 1 : ENNReal) *
          ∑ index ∈
            (Finset.univ.filter fun index =>
              color index = best),
            weight index := by
  let classWeight : Fin (D + 1) → ENNReal := fun best =>
    ∑ index ∈
      Finset.univ.filter (fun index =>
        color index = best),
      weight index
  have hsingle :
      ∀ index : Fin n,
        (∑ best : Fin (D + 1),
          if color index = best then
            weight index
          else
            0) =
          weight index := by
    intro index
    rw [Finset.sum_eq_single_of_mem
      (color index) (Finset.mem_univ _)]
    · rw [if_pos rfl]
    · intro other _ hne
      rw [if_neg (fun heq => hne heq.symm)]
  have htotal :
      (∑ index : Fin n, weight index) =
        ∑ best : Fin (D + 1),
          classWeight best := by
    calc
      (∑ index : Fin n, weight index) =
          ∑ index : Fin n,
            ∑ best : Fin (D + 1),
              if color index = best then
                weight index
              else
                0 := by
        apply Finset.sum_congr rfl
        intro index _
        exact (hsingle index).symm
      _ =
          ∑ best : Fin (D + 1),
            ∑ index : Fin n,
              if color index = best then
                weight index
              else
                0 := by
        rw [Finset.sum_comm]
      _ =
          ∑ best : Fin (D + 1),
            classWeight best := by
        apply Finset.sum_congr rfl
        intro best _
        rw [Finset.sum_ite]
        simp [classWeight]
  rcases
      Finset.exists_max_image
        (Finset.univ : Finset (Fin (D + 1)))
        classWeight (by simp) with
    ⟨best, _, hbest⟩
  refine ⟨best, ?_⟩
  calc
    (∑ index : Fin n, weight index) =
        ∑ color : Fin (D + 1),
          classWeight color := htotal
    _ ≤
        ∑ _color : Fin (D + 1),
          classWeight best := by
      apply Finset.sum_le_sum
      intro color _
      exact hbest color (Finset.mem_univ color)
    _ = (D + 1 : ENNReal) *
          classWeight best := by
      simp

/-- Weighted independent-set selection for a bounded-degree conflict graph. -/
lemma pureWZ2_greedy_independent_set_weighted
    {n D : ℕ}
    {relation : Fin n → Fin n → Prop}
    {weight : Fin n → ENNReal}
    (hsymm :
      ∀ first second,
        relation first second →
          relation second first)
    (hirrefl :
      ∀ index, ¬relation index index)
    (hdegree :
      ∀ index,
        (Finset.univ.filter fun other =>
          relation index other).card ≤ D) :
    ∃ selected : Finset (Fin n),
      (∀ first ∈ selected,
        ∀ second ∈ selected,
          first ≠ second →
            ¬relation first second) ∧
      (∑ index : Fin n, weight index) ≤
        (D + 1 : ENNReal) *
          ∑ index ∈ selected, weight index := by
  rcases
      pureWZ2_greedy_proper_coloring
        hsymm hirrefl hdegree with
    ⟨color, hcolor⟩
  rcases
      pureWZ2_weighted_pigeonhole
        weight color with
    ⟨best, hbest⟩
  let selected : Finset (Fin n) :=
    Finset.univ.filter fun index =>
      color index = best
  have hindependent :
      ∀ first ∈ selected,
        ∀ second ∈ selected,
          first ≠ second →
            ¬relation first second := by
    intro first hfirst second hsecond hne
    have hfirstColor :
        color first = best := by
      simpa [selected] using hfirst
    have hsecondColor :
        color second = best := by
      simpa [selected] using hsecond
    intro hrelation
    exact
      hcolor first second hrelation
        (hfirstColor.trans hsecondColor.symm)
  exact ⟨selected, hindependent, hbest⟩

end Kakeya.Assouad

end
