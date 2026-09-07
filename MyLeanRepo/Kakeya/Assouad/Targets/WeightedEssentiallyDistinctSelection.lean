import MyLeanRepo.Kakeya.Assouad.Statements

/-!
WZ Lemma 8 rediscretization: retain a large-weight essentially-distinct
subfamily from a finite target family with bounded conflict degree.

The proof uses a greedy `(D + 1)`-coloring of the conflict graph followed by
selecting the heaviest color class.
-/

attribute [local instance] Classical.propDecidable

namespace Kakeya.Assouad

private lemma weighted_pigeonhole {n D : ℕ}
    (weight : Fin n → ENNReal)
    (color : Fin n → Fin (D + 1)) :
    ∃ k : Fin (D + 1),
      (∑ i : Fin n, weight i) ≤
        (D + 1 : ENNReal) *
          ∑ i ∈ Finset.univ.filter (fun i => color i = k), weight i := by
  let classWeight : Fin (D + 1) → ENNReal := fun k =>
    ∑ i ∈ Finset.univ.filter (fun i => color i = k), weight i
  have hsingle :
      ∀ i : Fin n,
        (∑ k : Fin (D + 1),
          if color i = k then weight i else 0) = weight i := by
    intro i
    rw [Finset.sum_eq_single_of_mem (color i) (Finset.mem_univ _)]
    · rw [if_pos rfl]
    · intro j _ hne
      rw [if_neg (fun h => hne h.symm)]
  have htotal :
      (∑ i : Fin n, weight i) =
        ∑ k : Fin (D + 1), classWeight k := by
    calc
      (∑ i : Fin n, weight i) =
          ∑ i : Fin n,
            ∑ k : Fin (D + 1),
              if color i = k then weight i else 0 := by
        apply Finset.sum_congr rfl
        intro i _
        exact (hsingle i).symm
      _ = ∑ k : Fin (D + 1),
          ∑ i : Fin n,
            if color i = k then weight i else 0 := by
        rw [Finset.sum_comm]
      _ = ∑ k : Fin (D + 1), classWeight k := by
        apply Finset.sum_congr rfl
        intro k _
        rw [Finset.sum_ite]
        simp [classWeight]
  rcases Finset.exists_max_image
      (Finset.univ : Finset (Fin (D + 1))) classWeight (by simp) with
    ⟨k, _, hk⟩
  refine ⟨k, ?_⟩
  calc
    (∑ i : Fin n, weight i)
        = ∑ j : Fin (D + 1), classWeight j := htotal
    _ ≤ ∑ _j : Fin (D + 1), classWeight k := by
      apply Finset.sum_le_sum
      intro j _
      exact hk j (Finset.mem_univ j)
    _ = (D + 1 : ENNReal) * classWeight k := by
      simp

private lemma greedy_coloring_fin (n D : ℕ)
    (R : Fin n → Fin n → Prop)
    (hR_symm : ∀ i j, R i j → R j i)
    (hR_irrefl : ∀ i, ¬R i i)
    (hR_deg :
      ∀ i, (Finset.univ.filter fun j => R i j).card ≤ D) :
    ∃ color : Fin n → Fin (D + 1),
      ∀ i j, R i j → color i ≠ color j := by
  have hmain :
      ∀ m : ℕ,
        ∀ S : Fin m → Fin m → Prop,
          (∀ i j, S i j → S j i) →
          (∀ i, ¬S i i) →
          (∀ i, (Finset.univ.filter fun j => S i j).card ≤ D) →
          ∃ color : Fin m → Fin (D + 1),
            ∀ i j, S i j → color i ≠ color j := by
    intro m
    induction m with
    | zero =>
        intro S _ _ _
        exact ⟨Fin.elim0, fun i => Fin.elim0 i⟩
    | succ m ih =>
        intro S hsymm hirrefl hdeg
        let S' : Fin m → Fin m → Prop := fun i j =>
          S (Fin.castSucc i) (Fin.castSucc j)
        have hS'_symm : ∀ i j, S' i j → S' j i := by
          intro i j h
          exact hsymm _ _ h
        have hS'_irrefl : ∀ i, ¬S' i i := by
          intro i
          exact hirrefl (Fin.castSucc i)
        have hS'_deg :
            ∀ i : Fin m,
              (Finset.univ.filter fun j : Fin m => S' i j).card ≤ D := by
          intro i
          let embedding : Fin m → Fin (m + 1) := Fin.castSucc
          let source :=
            Finset.univ.filter fun j : Fin m => S' i j
          let target :=
            Finset.univ.filter fun k : Fin (m + 1) =>
              S (embedding i) k
          have hsubset : Finset.image embedding source ⊆ target := by
            intro k hk
            rcases Finset.mem_image.mp hk with ⟨j, hj, rfl⟩
            simpa [source, target, S', embedding] using hj
          have hcard :
              source.card = (Finset.image embedding source).card := by
            symm
            exact Finset.card_image_of_injective _
              (Fin.castSucc_injective m)
          rw [hcard]
          exact (Finset.card_le_card hsubset).trans (hdeg (embedding i))
        rcases ih S' hS'_symm hS'_irrefl hS'_deg with
          ⟨oldColor, holdColor⟩
        let last : Fin (m + 1) := Fin.last m
        let neighbors : Finset (Fin m) :=
          Finset.univ.filter fun j : Fin m =>
            S (Fin.castSucc j) last
        let forbidden : Finset (Fin (D + 1)) :=
          neighbors.image oldColor
        have hlastDegree :
            (Finset.univ.filter fun k : Fin (m + 1) => S k last).card ≤ D := by
          have heq :
              (Finset.univ.filter fun k : Fin (m + 1) => S k last) =
                (Finset.univ.filter fun k : Fin (m + 1) => S last k) := by
            ext k
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨hsymm _ _, hsymm _ _⟩
          rw [heq]
          exact hdeg last
        have hneighbors : neighbors.card ≤ D := by
          let embedding : Fin m → Fin (m + 1) := Fin.castSucc
          let target :=
            Finset.univ.filter fun k : Fin (m + 1) => S k last
          have hsubset : Finset.image embedding neighbors ⊆ target := by
            intro k hk
            rcases Finset.mem_image.mp hk with ⟨j, hj, rfl⟩
            simpa [neighbors, target, embedding] using hj
          have hcard :
              neighbors.card = (Finset.image embedding neighbors).card := by
            symm
            exact Finset.card_image_of_injective _
              (Fin.castSucc_injective m)
          rw [hcard]
          exact (Finset.card_le_card hsubset).trans hlastDegree
        have hforbidden : forbidden.card ≤ D :=
          (Finset.card_image_le).trans hneighbors
        have hexists : ∃ c : Fin (D + 1), c ∉ forbidden := by
          by_contra h
          push Not at h
          have hsubset :
              (Finset.univ : Finset (Fin (D + 1))) ⊆ forbidden := by
            intro c _
            exact h c
          have hcard :=
            (Finset.card_le_card hsubset).trans hforbidden
          simpa using hcard
        let newColor : Fin (D + 1) := Classical.choose hexists
        have hnewColor : newColor ∉ forbidden :=
          Classical.choose_spec hexists
        let color : Fin (m + 1) → Fin (D + 1) := fun i =>
          if h : i.val < m then oldColor ⟨i.val, h⟩ else newColor
        have hlast : color last = newColor := by
          have h : ¬last.val < m := by simp [last, Fin.last]
          simp [color, h]
        have hcast : ∀ i : Fin m, color (Fin.castSucc i) = oldColor i := by
          intro i
          simp [color, i.is_lt]
        refine ⟨color, ?_⟩
        intro i j hS
        by_cases hi : i.val < m
        · by_cases hj : j.val < m
          · let i' : Fin m := ⟨i.val, hi⟩
            let j' : Fin m := ⟨j.val, hj⟩
            have hi' : i = Fin.castSucc i' := by
              apply Fin.ext
              rfl
            have hj' : j = Fin.castSucc j' := by
              apply Fin.ext
              rfl
            have hS' : S' i' j' := by
              have h : S (Fin.castSucc i') (Fin.castSucc j') := by
                rw [← hi', ← hj']
                exact hS
              exact h
            have hold : oldColor i' ≠ oldColor j' :=
              holdColor i' j' hS'
            rw [hi', hj', hcast, hcast]
            exact hold
          · have hjVal : j.val = m := by omega
            have hjLast : j = last := by
              apply Fin.ext
              simp [last, Fin.last, hjVal]
            let i' : Fin m := ⟨i.val, hi⟩
            have hi' : i = Fin.castSucc i' := by
              apply Fin.ext
              rfl
            have hneighbor : i' ∈ neighbors := by
              simp only [neighbors, Finset.mem_filter, Finset.mem_univ,
                true_and]
              simpa [hi', hjLast] using hS
            have hforbid : oldColor i' ∈ forbidden :=
              Finset.mem_image.mpr ⟨i', hneighbor, rfl⟩
            rw [hi', hjLast, hcast, hlast]
            exact fun heq => hnewColor (heq ▸ hforbid)
        · have hiVal : i.val = m := by omega
          have hiLast : i = last := by
            apply Fin.ext
            simp [last, Fin.last, hiVal]
          rw [hiLast, hlast]
          by_cases hj : j.val < m
          · let j' : Fin m := ⟨j.val, hj⟩
            have hj' : j = Fin.castSucc j' := by
              apply Fin.ext
              rfl
            have hneighbor : j' ∈ neighbors := by
              simp only [neighbors, Finset.mem_filter, Finset.mem_univ,
                true_and]
              have hS_last : S last j := by
                rw [hiLast] at hS
                exact hS
              have hS_symm : S j last := hsymm last j hS_last
              have h : S (Fin.castSucc j') last := by
                rw [← hj']
                exact hS_symm
              exact h
            have hforbid : oldColor j' ∈ forbidden :=
              Finset.mem_image.mpr ⟨j', hneighbor, rfl⟩
            rw [hj', hcast]
            exact fun heq => hnewColor (heq ▸ hforbid)
          · have hjVal : j.val = m := by omega
            have hjLast : j = last := by
              apply Fin.ext
              simp [last, Fin.last, hjVal]
            rw [hiLast, hjLast] at hS
            exact False.elim (hirrefl last hS)
  exact hmain n R hR_symm hR_irrefl hR_deg

/-- Weighted independent-set selection for an arbitrary finite symmetric
irreflexive conflict relation of degree at most `D`.  This is the purely
combinatorial core of both volume-overlap and paper-containment cleanup. -/
theorem weighted_symmetric_irreflexive_selection
    {n D : ℕ} (weight : Fin n → ENNReal)
    (conflict : Fin n → Fin n → Prop)
    (hconflictSymm : ∀ i j, conflict i j → conflict j i)
    (hconflictIrrefl : ∀ i, ¬conflict i i)
    (hdegree : ∀ i,
      (Finset.univ.filter fun j => conflict i j).card ≤ D) :
    ∃ selected : Finset (Fin n),
      (∀ i ∈ selected, ∀ j ∈ selected, i ≠ j → ¬conflict i j) ∧
      (∑ i, weight i) ≤
        (D + 1 : ENNReal) * ∑ i ∈ selected, weight i := by
  rcases greedy_coloring_fin n D conflict hconflictSymm hconflictIrrefl
      hdegree with ⟨color, hcolor⟩
  rcases weighted_pigeonhole weight color with ⟨best, hbest⟩
  let selected : Finset (Fin n) :=
    Finset.univ.filter fun i => color i = best
  refine ⟨selected, ?_, hbest⟩
  intro i hi j hj hij hconflict
  have hci : color i = best := by simpa [selected] using hi
  have hcj : color j = best := by simpa [selected] using hj
  exact hcolor i j hconflict (hci.trans hcj.symm)

/-- ENNReal-valued degree wrapper for the weighted finite-graph selection.
The actual degree remains the natural-valued maximum of the finite graph;
the supplied `K` is used only to state the retained-mass loss without an
external rounding convention. -/
theorem weighted_symmetric_irreflexive_selection_of_ennreal_degree
    {n : ℕ} (weight : Fin n → ENNReal)
    (conflict : Fin n → Fin n → Prop)
    (hconflictSymm : ∀ i j, conflict i j → conflict j i)
    (hconflictIrrefl : ∀ i, ¬conflict i i)
    (K : ENNReal)
    (hdegree : ∀ i,
      ((Finset.univ.filter fun j => conflict i j).card : ENNReal) ≤ K) :
    ∃ selected : Finset (Fin n),
      (∀ i ∈ selected, ∀ j ∈ selected, i ≠ j → ¬conflict i j) ∧
      (∑ i, weight i) ≤
        (K + 1) * ∑ i ∈ selected, weight i := by
  let conflictDegree : Fin n → ℕ := fun i =>
    (Finset.univ.filter fun j => conflict i j).card
  let D : ℕ := Finset.univ.sup conflictDegree
  have hdegreeNat : ∀ i, conflictDegree i ≤ D := by
    intro i
    exact Finset.le_sup (Finset.mem_univ i)
  rcases weighted_symmetric_irreflexive_selection weight conflict
      hconflictSymm hconflictIrrefl hdegreeNat with
    ⟨selected, hselected, hmass⟩
  have hD : (D : ENNReal) ≤ K := by
    by_cases hn : n = 0
    · have hDzero : D = 0 := by
        apply Nat.eq_zero_of_le_zero
        apply Finset.sup_le
        intro i _
        have himpossible : i.val < 0 := by simpa [hn] using i.isLt
        omega
      simp [hDzero]
    · have huniv : (Finset.univ : Finset (Fin n)).Nonempty := by
        have hnPos : 0 < n := Nat.pos_of_ne_zero hn
        exact ⟨⟨0, hnPos⟩, Finset.mem_univ _⟩
      rcases Finset.exists_mem_eq_sup Finset.univ huniv conflictDegree with
        ⟨index, _, hindex⟩
      change ((Finset.univ.sup conflictDegree : ℕ) : ENNReal) ≤ K
      rw [hindex]
      simpa [conflictDegree] using hdegree index
  refine ⟨selected, hselected, hmass.trans ?_⟩
  gcongr

theorem weighted_essentially_distinct_selection :
    WeightedEssentiallyDistinctSelectionStatement := by
  intro rho F weight _hweight D hdeg
  let conflict : Fin F.card → Fin F.card → Prop := fun i j =>
    j ≠ i ∧ ¬(F.tube i).EssentiallyDistinct (F.tube j)
  have hsymm : ∀ i j, conflict i j → conflict j i := by
    intro i j h
    have hrelation :
        (F.tube i).EssentiallyDistinct (F.tube j) ↔
          (F.tube j).EssentiallyDistinct (F.tube i) := by
      simp [Kakeya.DeltaTube.EssentiallyDistinct, Set.inter_comm, max_comm]
    exact ⟨h.1.symm, hrelation.not.mp h.2⟩
  have hirrefl : ∀ i, ¬conflict i i := by
    intro i h
    exact h.1 rfl
  have hdegree :
      ∀ i, (Finset.univ.filter fun j => conflict i j).card ≤ D := by
    intro i
    simpa [conflict] using hdeg i
  have hcoloring :
      ∃ color : Fin F.card → Fin (D + 1),
        ∀ i j, conflict i j → color i ≠ color j := by
    apply greedy_coloring_fin F.card D conflict hsymm hirrefl
    intro i
    simpa [conflict] using hdeg i
  rcases hcoloring with ⟨color, hcolor⟩
  rcases weighted_pigeonhole weight color with ⟨best, hbest⟩
  let selected : Finset (Fin F.card) :=
    Finset.univ.filter fun i => color i = best
  have hdistinct :
      ∀ i ∈ selected, ∀ j ∈ selected, i ≠ j →
        (F.tube i).EssentiallyDistinct (F.tube j) := by
    intro i hi j hj hij
    have hci : color i = best := by simpa [selected] using hi
    have hcj : color j = best := by simpa [selected] using hj
    by_contra h
    have hconflict : conflict i j := ⟨hij.symm, h⟩
    exact hcolor i j hconflict (hci.trans hcj.symm)
  exact ⟨selected, hdistinct, hbest⟩

end Kakeya.Assouad
