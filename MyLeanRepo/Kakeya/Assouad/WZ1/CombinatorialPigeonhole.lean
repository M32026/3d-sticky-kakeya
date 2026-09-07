import Mathlib.Tactic

/-!
# Combinatorial pigeonhole for WZ1 weak planiness

Abstract finite counting argument: bounds on broad triples and close pairs
produce a transverse ordered pair with many narrow third directions.
-/

namespace Kakeya.Assouad

/-- Sum over a Cartesian product equals the corresponding iterated sum. -/
lemma finset_sum_product {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (t : Finset β) (f : α × β → ℕ) :
    ∑ p ∈ s.product t, f p = ∑ x ∈ s, ∑ y ∈ t, f (x, y) := by
  have h_disj : ∀ (x : α), x ∈ s → ∀ (x' : α), x' ∈ s → x ≠ x' →
      Disjoint (t.image (fun y : β => (x, y)))
        (t.image (fun y : β => (x', y))) := by
    intro x _ x' _ hne
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    rcases Finset.mem_image.mp hp1 with ⟨y, _, rfl⟩
    rcases Finset.mem_image.mp hp2 with ⟨y', _, hxy⟩
    injection hxy with h1 _
    exact hne h1.symm
  have h1 :
      s.product t =
        s.biUnion (fun x => t.image (fun y : β => (x, y))) := by
    ext ⟨x, y⟩
    simp [Finset.mem_product, Finset.mem_biUnion]
  rw [h1, Finset.sum_biUnion h_disj]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_image]
  simp

/--
If fewer than `Q` triples are broad, each element has fewer than `R` close
partners, and the displayed cubic budget holds, then some transverse ordered
pair has at least one quarter of all indices as narrow third directions.
-/
lemma combinatorial_pigeonhole
    {α : Type*} [DecidableEq α]
    (A : Finset α)
    (Broad : α → α → α → Prop) [∀ i j k, Decidable (Broad i j k)]
    (Close : α → α → Prop) [∀ i j, Decidable (Close i j)]
    (Q R : ℕ)
    (h_broad : ((A.product (A.product A)).filter
        (fun p => Broad p.1 p.2.1 p.2.2)).card < Q)
    (h_close : ∀ i ∈ A, (A.filter (fun j => Close i j)).card < R)
    (h_main : 4 * (Q + 3 * R * A.card ^ 2) ≤ 3 * A.card ^ 3) :
    ∃ i ∈ A, ∃ j ∈ A, ¬Close i j ∧
      4 * (A.filter (fun k =>
        ¬Broad i j k ∧ ¬Close i j ∧ ¬Close i k ∧ ¬Close j k)).card ≥
          A.card := by
  set mu : ℕ := A.card with hmu_def
  have h_mu_pos : 0 < mu := by
    by_contra h
    have hmu0 : mu = 0 := by omega
    rw [hmu0] at h_main
    have hQ : Q = 0 := by omega
    rw [hQ] at h_broad
    omega

  set triples : Finset (α × (α × α)) :=
    A.product (A.product A) with htriples_def
  let Good (i j k : α) :=
    ¬Broad i j k ∧ ¬Close i j ∧ ¬Close i k ∧ ¬Close j k
  set goodTriples :=
    triples.filter (fun p => Good p.1 p.2.1 p.2.2) with hgood_def
  set B0 :=
    triples.filter (fun p => Broad p.1 p.2.1 p.2.2) with hB0_def
  set B1 := triples.filter (fun p => Close p.1 p.2.1) with hB1_def
  set B2 := triples.filter (fun p => Close p.1 p.2.2) with hB2_def
  set B3 := triples.filter (fun p => Close p.2.1 p.2.2) with hB3_def
  set badUnion := B0 ∪ B1 ∪ B2 ∪ B3 with hbad_def

  have h_total : triples.card = mu ^ 3 := by
    simp [htriples_def, hmu_def] <;> ring

  have h_subset : badUnion ⊆ triples := by
    apply Finset.union_subset
    · apply Finset.union_subset
      · apply Finset.union_subset
        · exact Finset.filter_subset _ _
        · exact Finset.filter_subset _ _
      · exact Finset.filter_subset _ _
    · exact Finset.filter_subset _ _

  have h_complement : goodTriples = triples \ badUnion := by
    ext p
    simp only [hgood_def, hbad_def, Finset.mem_sdiff, Finset.mem_filter,
      Finset.mem_union, hB0_def, hB1_def, hB2_def, hB3_def]
    tauto

  have h_sum_lt : ∀ (s : Finset α) (f g : α → ℕ),
      s.Nonempty → (∀ i ∈ s, f i < g i) →
        ∑ i ∈ s, f i < ∑ i ∈ s, g i := by
    intro s f g hne hlt
    have h1 : ∀ i ∈ s, f i + 1 ≤ g i := by
      intro i hi
      exact Nat.succ_le_iff.mpr (hlt i hi)
    have h2 : ∑ i ∈ s, (f i + 1) ≤ ∑ i ∈ s, g i :=
      Finset.sum_le_sum h1
    have h3 : ∑ i ∈ s, (f i + 1) = ∑ i ∈ s, f i + s.card := by
      rw [Finset.sum_add_distrib]
      simp
    rw [h3] at h2
    have h4 : 0 < s.card := Finset.Nonempty.card_pos hne
    omega

  have hne : A.Nonempty :=
    Finset.nonempty_of_ne_empty (by
      intro h
      rw [h] at hmu_def
      simp at hmu_def
      omega)

  have hB1_eq :
      B1.card =
        ∑ i ∈ A, (A.filter (fun j => Close i j)).card * mu := by
    calc
      B1.card
          = ∑ p ∈ triples, (if Close p.1 p.2.1 then 1 else 0) := by
              rw [hB1_def, Finset.card_filter]
      _ = ∑ i ∈ A, ∑ q ∈ A.product A,
            (if Close i q.1 then 1 else 0) := by
              rw [htriples_def]
              exact finset_sum_product A (A.product A) _
      _ = ∑ i ∈ A,
            ((A.product A).filter
              (fun q : α × α => Close i q.1)).card := by
              apply Finset.sum_congr rfl
              intro i _
              rw [Finset.card_filter]
      _ = ∑ i ∈ A, (A.filter (fun j => Close i j)).card * mu := by
              apply Finset.sum_congr rfl
              intro i _
              have h2 :
                  (A.product A).filter
                      (fun q : α × α => Close i q.1) =
                    (A.filter (fun j => Close i j)).product A := by
                ext ⟨j, k⟩
                simp [Finset.mem_filter, Finset.mem_product] <;> tauto
              rw [h2]
              simp [hmu_def] <;> ring

  have hB1_lt : B1.card < R * mu ^ 2 := by
    rw [hB1_eq]
    have h := h_sum_lt A
      (fun i => (A.filter (fun j => Close i j)).card * mu)
      (fun _ => R * mu) hne
      (fun i hi => mul_lt_mul_of_pos_right (h_close i hi) h_mu_pos)
    have h_rhs : ∑ i ∈ A, (R * mu) = R * mu ^ 2 := by
      simp [Finset.sum_const, hmu_def] <;> ring
    rw [h_rhs] at h
    exact h

  have hB2_eq :
      B2.card =
        ∑ i ∈ A, (A.filter (fun k => Close i k)).card * mu := by
    calc
      B2.card
          = ∑ p ∈ triples, (if Close p.1 p.2.2 then 1 else 0) := by
              rw [hB2_def, Finset.card_filter]
      _ = ∑ i ∈ A, ∑ q ∈ A.product A,
            (if Close i q.2 then 1 else 0) := by
              rw [htriples_def]
              exact finset_sum_product A (A.product A) _
      _ = ∑ i ∈ A,
            ((A.product A).filter
              (fun q : α × α => Close i q.2)).card := by
              apply Finset.sum_congr rfl
              intro i _
              rw [Finset.card_filter]
      _ = ∑ i ∈ A, (A.filter (fun k => Close i k)).card * mu := by
              apply Finset.sum_congr rfl
              intro i _
              have h2 :
                  (A.product A).filter
                      (fun q : α × α => Close i q.2) =
                    A.product (A.filter (fun k => Close i k)) := by
                ext ⟨j, k⟩
                simp [Finset.mem_filter, Finset.mem_product] <;> tauto
              rw [h2]
              simp [hmu_def, mul_comm] <;> ring

  have hB2_lt : B2.card < R * mu ^ 2 := by
    rw [hB2_eq]
    have h := h_sum_lt A
      (fun i => (A.filter (fun k => Close i k)).card * mu)
      (fun _ => R * mu) hne
      (fun i hi => mul_lt_mul_of_pos_right (h_close i hi) h_mu_pos)
    have h_rhs : ∑ i ∈ A, (R * mu) = R * mu ^ 2 := by
      simp [Finset.sum_const, hmu_def] <;> ring
    rw [h_rhs] at h
    exact h

  have hB3_eq :
      B3.card =
        ∑ j ∈ A, (A.filter (fun k => Close j k)).card * mu := by
    calc
      B3.card
          = ∑ p ∈ triples, (if Close p.2.1 p.2.2 then 1 else 0) := by
              rw [hB3_def, Finset.card_filter]
      _ = ∑ i ∈ A, ∑ q ∈ A.product A,
            (if Close q.1 q.2 then 1 else 0) := by
              rw [htriples_def]
              exact finset_sum_product A (A.product A) _
      _ = ∑ q ∈ A.product A,
            (if Close q.1 q.2 then 1 else 0) * mu := by
              rw [Finset.sum_comm]
              apply Finset.sum_congr rfl
              intro q _
              rw [Finset.sum_const] <;> ring
      _ = ((A.product A).filter
            (fun q : α × α => Close q.1 q.2)).card * mu := by
              have h_sum_mul :
                  ∑ q ∈ A.product A,
                      (if Close q.1 q.2 then 1 else 0) * mu =
                    (∑ q ∈ A.product A,
                      (if Close q.1 q.2 then 1 else 0)) * mu := by
                rw [Finset.sum_mul]
              rw [h_sum_mul, Finset.card_filter]
      _ = ∑ j ∈ A, (A.filter (fun k => Close j k)).card * mu := by
              have h2 :
                  ((A.product A).filter
                    (fun q : α × α => Close q.1 q.2)).card =
                    ∑ j ∈ A,
                      (A.filter (fun k => Close j k)).card := by
                rw [Finset.card_filter,
                  finset_sum_product A A
                    (fun p : α × α =>
                      if Close p.1 p.2 then 1 else 0)]
                apply Finset.sum_congr rfl
                intro j _
                rw [Finset.sum_ite] <;> simp
              rw [h2]
              exact
                (Finset.sum_mul A
                  (fun j => (A.filter (fun k => Close j k)).card)
                  mu)

  have hB3_lt : B3.card < R * mu ^ 2 := by
    rw [hB3_eq]
    have h := h_sum_lt A
      (fun j => (A.filter (fun k => Close j k)).card * mu)
      (fun _ => R * mu) hne
      (fun j hj => mul_lt_mul_of_pos_right (h_close j hj) h_mu_pos)
    have h_rhs : ∑ i ∈ A, (R * mu) = R * mu ^ 2 := by
      simp [Finset.sum_const, hmu_def] <;> ring
    rw [h_rhs] at h
    exact h

  have h_bad_lt : badUnion.card < Q + 3 * R * mu ^ 2 := by
    have h_union :
        badUnion.card ≤ B0.card + B1.card + B2.card + B3.card := by
      calc
        badUnion.card ≤ (B0 ∪ B1 ∪ B2).card + B3.card :=
          Finset.card_union_le _ _
        _ ≤ (B0 ∪ B1).card + B2.card + B3.card := by
          have h := Finset.card_union_le (B0 ∪ B1) B2
          linarith
        _ ≤ B0.card + B1.card + B2.card + B3.card := by
          have h := Finset.card_union_le B0 B1
          linarith
    linarith [h_broad, hB1_lt, hB2_lt, hB3_lt]

  have h_good_bad : goodTriples.card + badUnion.card = mu ^ 3 := by
    rw [h_complement]
    have h_card : (triples \ badUnion).card =
        triples.card - badUnion.card := by
      rw [Finset.card_sdiff]
      have h_int : badUnion ∩ triples = badUnion := by
        rw [Finset.inter_eq_left.mpr h_subset]
      rw [h_int]
    rw [h_card, h_total]
    omega

  have h4 : 4 * goodTriples.card > mu ^ 3 := by omega

  let goodThird (i j : α) := A.filter (fun k => Good i j k)

  have h_sum :
      goodTriples.card =
        ∑ i ∈ A, ∑ j ∈ A, (goodThird i j).card := by
    calc
      goodTriples.card
          = ∑ p ∈ triples,
              (if Good p.1 p.2.1 p.2.2 then 1 else 0) := by
                rw [hgood_def, Finset.card_filter]
      _ = ∑ i ∈ A, ∑ q ∈ A.product A,
            (if Good i q.1 q.2 then 1 else 0) := by
              rw [htriples_def]
              exact finset_sum_product A (A.product A) _
      _ = ∑ i ∈ A, ∑ j ∈ A, ∑ k ∈ A,
            (if Good i j k then 1 else 0) := by
              apply Finset.sum_congr rfl
              intro i _
              exact finset_sum_product A A _
      _ = ∑ i ∈ A, ∑ j ∈ A, (goodThird i j).card := by
              apply Finset.sum_congr rfl
              intro i _
              apply Finset.sum_congr rfl
              intro j _
              rw [Finset.card_filter]

  have h_pigeonhole :
      ∃ i ∈ A, ∃ j ∈ A, 4 * (goodThird i j).card ≥ mu := by
    by_contra h
    push Not at h
    have h5 : 4 * goodTriples.card ≤ mu ^ 2 * (mu - 1) := by
      calc
        4 * goodTriples.card
            = 4 * ∑ i ∈ A, ∑ j ∈ A,
                (goodThird i j).card := by rw [h_sum]
        _ = ∑ i ∈ A, ∑ j ∈ A,
              4 * (goodThird i j).card := by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro i _
                rw [Finset.mul_sum]
        _ ≤ ∑ i ∈ A, ∑ j ∈ A, (mu - 1) := by
                apply Finset.sum_le_sum
                intro i hi
                apply Finset.sum_le_sum
                intro j hj
                have h6 : 4 * (goodThird i j).card < mu := h i hi j hj
                omega
        _ = mu ^ 2 * (mu - 1) := by
                simp [Finset.sum_const, hmu_def] <;> ring
    have h6 : mu ^ 2 * (mu - 1) < mu ^ 3 := by
      have h7 : mu - 1 < mu := by omega
      have h8 : 0 < mu ^ 2 := by positivity
      exact mul_lt_mul_of_pos_left h7 h8
    have h9 : 4 * goodTriples.card < mu ^ 3 :=
      h5.trans_lt h6
    linarith [h4]

  rcases h_pigeonhole with ⟨i, hi, j, hj, h_ge⟩
  have h_pos : 0 < (goodThird i j).card := by
    by_contra h
    have h7 : (goodThird i j).card = 0 := by omega
    rw [h7] at h_ge
    omega
  have h_nonempty : (goodThird i j).Nonempty :=
    Finset.card_pos.mp h_pos
  rcases h_nonempty with ⟨k, hk⟩
  have h_good : Good i j k := (Finset.mem_filter.mp hk).2
  exact ⟨i, hi, j, hj, h_good.2.1, h_ge⟩

end Kakeya.Assouad
