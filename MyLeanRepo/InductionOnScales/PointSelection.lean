module

public import MyLeanRepo.InductionOnScales.Definitions
public import MyLeanRepo.InductionOnScales.Basic
public import MyLeanRepo.InductionOnScales.Homothety
public import MyLeanRepo.InductionOnScales.Pigeonhole
public import MyLeanRepo.OSWPrelude

@[expose] public section

/-!
# Point selection by coarse square

Provides lemmas for selecting subsets of fine points while maintaining
per-coarse-square density guarantees. These are used in the coarse phase
to establish conjuncts 3 and 4 of the target theorem.

## Main results

- `groupByCoarseSquare`: image of points under `containingSquare`
- `squareContained_iff_containingSquare`: key geometric equivalence
- `points_in_Q_eq_filter`: equivalence of two filter formulations
- `coarse_fibers_disjoint`: fibers for different coarse squares are disjoint
- `select_points_by_coarse_square`: find a coarse square with many points
- `per_q_density_preservation`: per-Q cardinality retention via dyadic pigeonholing

## Whiteprint node
`point_selection` under `InductionOnScales/PointSelection/`.
-/

attribute [local instance] Classical.propDecidable

open scoped BigOperators

namespace InductionOnScales

section PointSelection

/-- Group fine points by their containing coarse square. -/
noncomputable def groupByCoarseSquare {n m : ℕ} (hnm : m ≤ n)
    (points : Finset (DyadicSquare n)) : Finset (DyadicSquare m) :=
  points.image (containingSquare hnm)

/-- **Key equivalence**: `squareContained hnm p Q` iff `containingSquare hnm p = Q`. -/
lemma squareContained_iff_containingSquare {n m : ℕ} (hnm : m ≤ n)
    (p : DyadicSquare n) (Q : DyadicSquare m) :
    squareContained hnm p Q ↔ containingSquare hnm p = Q := by
  constructor
  · -- Forward: squareContained → containingSquare = Q
    intro h
    let R := coarseRefinementFactor n m
    have hR_pos : 0 < (R : ℝ) := by exact_mod_cast coarseRefinementFactor_pos n m
    have h_i1 : (Q.i : ℝ) ≤ (p.i : ℝ) / (R : ℝ) := by
      have h_int : (Q.i : ℤ) * R ≤ p.i := h.1
      have h_cast : (Q.i : ℝ) * (R : ℝ) ≤ (p.i : ℝ) := by exact_mod_cast h_int
      have h : (Q.i : ℝ) = (Q.i : ℝ) * (R : ℝ) / (R : ℝ) := by
        field_simp [hR_pos.ne'] <;> ring
      rw [h]
      gcongr
    have h_i2 : (p.i : ℝ) / (R : ℝ) < (Q.i + 1 : ℝ) := by
      have h_int : p.i < (Q.i + 1) * R := h.2.1
      have h_cast : (p.i : ℝ) < ((Q.i + 1 : ℝ)) * (R : ℝ) := by exact_mod_cast h_int
      have h : (Q.i + 1 : ℝ) = ((Q.i + 1 : ℝ)) * (R : ℝ) / (R : ℝ) := by
        field_simp [hR_pos.ne'] <;> ring
      rw [h]
      gcongr
    have hfloor_i : ⌊(p.i : ℝ) / (R : ℝ)⌋ = Q.i := by
      rw [Int.floor_eq_iff]
      exact ⟨h_i1, h_i2⟩
    have h_j1 : (Q.j : ℝ) ≤ (p.j : ℝ) / (R : ℝ) := by
      have h_int : (Q.j : ℤ) * R ≤ p.j := h.2.2.1
      have h_cast : (Q.j : ℝ) * (R : ℝ) ≤ (p.j : ℝ) := by exact_mod_cast h_int
      have h : (Q.j : ℝ) = (Q.j : ℝ) * (R : ℝ) / (R : ℝ) := by
        field_simp [hR_pos.ne'] <;> ring
      rw [h]
      gcongr
    have h_j2 : (p.j : ℝ) / (R : ℝ) < (Q.j + 1 : ℝ) := by
      have h_int : p.j < (Q.j + 1) * R := h.2.2.2
      have h_cast : (p.j : ℝ) < ((Q.j + 1 : ℝ)) * (R : ℝ) := by exact_mod_cast h_int
      have h : (Q.j + 1 : ℝ) = ((Q.j + 1 : ℝ)) * (R : ℝ) / (R : ℝ) := by
        field_simp [hR_pos.ne'] <;> ring
      rw [h]
      gcongr
    have hfloor_j : ⌊(p.j : ℝ) / (R : ℝ)⌋ = Q.j := by
      rw [Int.floor_eq_iff]
      exact ⟨h_j1, h_j2⟩
    have h_ci : coarseParentIndex n m p.i = Q.i := by
      simpa [coarseParentIndex] using hfloor_i
    have h_cj : coarseParentIndex n m p.j = Q.j := by
      simpa [coarseParentIndex] using hfloor_j
    have h_eq_lemma : ∀ (a b : DyadicSquare m), a.i = b.i → a.j = b.j → a = b := by
      intro a b hi hj
      cases a
      cases b
      simp_all
    have h1 : (containingSquare hnm p).i = Q.i := by
      simpa [containingSquare, coarseParentIndex] using h_ci
    have h2 : (containingSquare hnm p).j = Q.j := by
      simpa [containingSquare, coarseParentIndex] using h_cj
    exact h_eq_lemma (containingSquare hnm p) Q h1 h2
  · -- Reverse: containingSquare = Q → squareContained
    intro h_eq
    have h : squareContained hnm p (containingSquare hnm p) :=
      containingSquare_squareContained hnm p
    rw [h_eq] at h
    exact h

/-- The set of points contained in Q equals the set of points whose
`containingSquare` is Q. -/
lemma points_in_Q_eq_filter {n m : ℕ} (hnm : m ≤ n)
    (points : Finset (DyadicSquare n)) (Q : DyadicSquare m) :
    (points.filter fun p => squareContained hnm p Q) =
    points.filter fun p => containingSquare hnm p = Q := by
  apply Finset.filter_congr
  intro p _
  exact squareContained_iff_containingSquare hnm p Q

/-- Fibers for different coarse squares are disjoint. -/
lemma coarse_fibers_disjoint {n m : ℕ} (hnm : m ≤ n)
    (points : Finset (DyadicSquare n))
    {Q1 Q2 : DyadicSquare m} (hQ : Q1 ≠ Q2) :
    Disjoint (points.filter fun p => squareContained hnm p Q1)
      (points.filter fun p => squareContained hnm p Q2) := by
  rw [Finset.disjoint_left]
  intro p h1 h2
  have h1' : squareContained hnm p Q1 := (Finset.mem_filter.mp h1).2
  have h2' : squareContained hnm p Q2 := (Finset.mem_filter.mp h2).2
  have h_eq1 : containingSquare hnm p = Q1 :=
    (squareContained_iff_containingSquare hnm p Q1).mp h1'
  have h_eq2 : containingSquare hnm p = Q2 :=
    (squareContained_iff_containingSquare hnm p Q2).mp h2'
  have h_contra : Q1 = Q2 := h_eq1.symm.trans h_eq2
  exact hQ h_contra

/-- **Select points by coarse square** (large fiber version).

Given a nonempty set of fine points, group them by `containingSquare hnm`.
There exists a coarse square `Q` such that the fiber of points contained in `Q`
has cardinality at least the average `|points| / |groupByCoarseSquare|`.

This is a direct application of `exists_large_fiber`. -/
lemma select_points_by_coarse_square {n m : ℕ} (hnm : m ≤ n)
    (points : Finset (DyadicSquare n)) (hs : points.Nonempty) :
    ∃ (Q : DyadicSquare m),
      Q ∈ groupByCoarseSquare hnm points ∧
      (points.filter fun p => squareContained hnm p Q).card ≥
        points.card / (groupByCoarseSquare hnm points).card := by
  let f : DyadicSquare n → DyadicSquare m := containingSquare hnm
  have h_main := exists_large_fiber points f hs
  rcases h_main with ⟨Q, hQ_mem, h_card⟩
  have h_filter_eq : points.filter (fun p => f p = Q) =
      points.filter (fun p => squareContained hnm p Q) := by
    apply Finset.filter_congr
    intro p _
    exact (squareContained_iff_containingSquare hnm p Q).symm
  rw [h_filter_eq] at h_card
  exact ⟨Q, hQ_mem, h_card⟩

/-- **Per-Q density preservation** via dyadic pigeonholing.

For each coarse square Q, apply `uniformize_by_dyadic_level` to the points
in Q. Select the union of all per-Q selected subsets. Then for every Q:
```
|P ∩ points_in_Q| ≥ |points_in_Q| / numDyadicLevels N
```

The loss factor is `K = numDyadicLevels N = Nat.log 2 N + 2`, which is
polylogarithmic in N. -/
lemma per_q_density_preservation {n m : ℕ} (hnm : m ≤ n)
    (points : Finset (DyadicSquare n))
    (w : DyadicSquare n → ℕ) {N : ℕ} (hN : 0 < N)
    (h_bound : ∀ p ∈ points, w p ≤ N) :
    ∃ (P : Finset (DyadicSquare n)),
      P ⊆ points ∧
      (∀ Q ∈ groupByCoarseSquare hnm points,
        (P.filter fun p => squareContained hnm p Q).card ≥
          (points.filter fun p => squareContained hnm p Q).card / numDyadicLevels N) := by
  let Qs := groupByCoarseSquare hnm points
  let pointsInQ (Q : DyadicSquare m) : Finset (DyadicSquare n) :=
    points.filter fun p => squareContained hnm p Q
  have h_bound_all : ∀ (Q : DyadicSquare m), ∀ p ∈ pointsInQ Q, w p ≤ N := by
    intro Q p hp
    have h_in_points : p ∈ points := (Finset.mem_filter.mp hp).1
    exact h_bound p h_in_points
  choose PQ jQ h_subQ hj_leQ h_levelQ h_cardQ using
    fun (Q : DyadicSquare m) => uniformize_by_dyadic_level
      (pointsInQ Q) w hN (h_bound_all Q)
  let P : Finset (DyadicSquare n) := Qs.biUnion PQ
  have hP_sub : P ⊆ points := by
    intro x hx
    rcases Finset.mem_biUnion.mp hx with ⟨Q, hQ, hxQ⟩
    have h' : x ∈ pointsInQ Q := (h_subQ Q) hxQ
    exact (Finset.mem_filter.mp h').1
  have h_disj : ∀ Q1 ∈ Qs, ∀ Q2 ∈ Qs, Q1 ≠ Q2 → Disjoint (PQ Q1) (PQ Q2) := by
    intro Q1 _ Q2 _ hne
    have h1 : PQ Q1 ⊆ pointsInQ Q1 := h_subQ Q1
    have h2 : PQ Q2 ⊆ pointsInQ Q2 := h_subQ Q2
    have h_disj' : Disjoint (pointsInQ Q1) (pointsInQ Q2) :=
      coarse_fibers_disjoint hnm points hne
    exact Disjoint.mono h1 h2 h_disj'
  have h_main : ∀ Q ∈ Qs,
      (P.filter fun p => squareContained hnm p Q).card ≥
        (pointsInQ Q).card / numDyadicLevels N := by
    intro Q hQ
    have h1 : PQ Q ⊆ P.filter (fun p => squareContained hnm p Q) := by
      intro p hp
      have h_in_P : p ∈ P := Finset.mem_biUnion.mpr ⟨Q, hQ, hp⟩
      have h_contained : squareContained hnm p Q := by
        have h : p ∈ pointsInQ Q := (h_subQ Q) hp
        exact (Finset.mem_filter.mp h).2
      exact Finset.mem_filter.mpr ⟨h_in_P, h_contained⟩
    have h2 : (PQ Q).card ≤ (P.filter fun p => squareContained hnm p Q).card :=
      Finset.card_le_card h1
    have h3 : (PQ Q).card ≥ (pointsInQ Q).card / numDyadicLevels N := h_cardQ Q
    exact le_trans h3 h2
  exact ⟨P, hP_sub, h_main⟩

/-- **Select points with full coarse-square coverage and density preservation**.

For each coarse square Q in the image, select `ceil(|points ∩ Q| / L)` points,
where `L = numDyadicLevels N`. Guarantees P nonempty, full coverage, and
per-Q real-division density bound. -/
lemma select_with_coverage
    {n m : ℕ} (hnm : m ≤ n)
    (points : Finset (DyadicSquare n))
    (w : DyadicSquare n → ℕ) {N : ℕ} (hN : 0 < N)
    (h_bound : ∀ p ∈ points, w p ≤ N)
    (h_points_nonempty : points.Nonempty) :
    ∃ (P : Finset (DyadicSquare n)),
      P ⊆ points ∧
      P.Nonempty ∧
      (P.image (containingSquare hnm)) = (points.image (containingSquare hnm)) ∧
      (∀ Q ∈ points.image (containingSquare hnm),
        ((P.filter fun p => squareContained hnm p Q).card : ℝ) ≥
          ((points.filter fun p => squareContained hnm p Q).card : ℝ) / (numDyadicLevels N : ℝ)) := by
  let b := numDyadicLevels N
  have hb_pos : 0 < b := by simp [b, numDyadicLevels] <;> omega
  let Qs := points.image (containingSquare hnm)
  let pointsInQ (Q : DyadicSquare m) := points.filter (fun p => squareContained hnm p Q)
  have h_nonempty_Q : ∀ Q ∈ Qs, (pointsInQ Q).Nonempty := by
    intro Q hQ
    rcases Finset.mem_image.mp hQ with ⟨p, hp, rfl⟩
    have h_cont : squareContained hnm p (containingSquare hnm p) :=
      (squareContained_iff_containingSquare hnm p (containingSquare hnm p)).mpr rfl
    exact ⟨p, Finset.mem_filter.mpr ⟨hp, h_cont⟩⟩
  let k (Q : DyadicSquare m) : ℕ := ((pointsInQ Q).card + b - 1) / b
  have h_k_le : ∀ Q ∈ Qs, k Q ≤ (pointsInQ Q).card := by
    intro Q hQ
    set a := (pointsInQ Q).card with ha
    have ha1 : 1 ≤ a := (h_nonempty_Q Q hQ).card_pos
    have h1 : a + b - 1 ≤ a * b := by
      obtain ⟨a', ha'⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
      obtain ⟨b', hb'⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
      rw [ha', hb'] <;> ring_nf <;> omega
    have h3 : (a + b - 1) / b ≤ (a * b) / b := Nat.div_le_div_right h1
    have h4 : (a * b) / b = a := Nat.mul_div_cancel a hb_pos
    rw [h4] at h3; exact h3
  have h_k_pos : ∀ Q ∈ Qs, 0 < k Q := by
    intro Q hQ
    set a := (pointsInQ Q).card with ha
    have ha1 : 1 ≤ a := (h_nonempty_Q Q hQ).card_pos
    dsimp only [k]
    have h1 : b ≤ a + b - 1 := by omega
    have h2 : b / b ≤ (a + b - 1) / b := Nat.div_le_div_right h1
    have h3 : b / b = 1 := Nat.div_self hb_pos
    have h4 : 1 ≤ (a + b - 1) / b := by rw [h3] at h2; exact h2
    exact h4
  have h_ceil : ∀ (a : ℕ), 1 ≤ a → ((a + b - 1) / b) * b ≥ a := by
    intro a ha1
    set n := a + b - 1 with hn
    set q := n / b with hq
    have h_gt : n < (q + 1) * b := by
      have h1 : n = q * b + n % b := by exact Eq.symm (Nat.div_add_mod' n b)
      have h2 : n % b < b := Nat.mod_lt n hb_pos
      rw [h1]; linarith
    by_contra h2
    have h3 : q * b < a := by omega
    have h4 : q * b ≤ a - 1 := by omega
    have h5 : (q + 1) * b ≤ a + b - 1 := by
      calc (q + 1) * b = q * b + b := by ring
        _ ≤ (a - 1) + b := by gcongr
        _ = a + b - 1 := by omega
    linarith
  choose PQ hPQ_sub hPQ_card using fun (Q : DyadicSquare m) (hQ : Q ∈ Qs) =>
    Finset.exists_subset_card_eq (h_k_le Q hQ)
  let PQ' (Q : DyadicSquare m) : Finset (DyadicSquare n) :=
    if hQ : Q ∈ Qs then PQ Q hQ else ∅
  let P : Finset (DyadicSquare n) := Qs.biUnion PQ'
  have hPQ'_eq : ∀ (Q : DyadicSquare m) (hQ : Q ∈ Qs), PQ' Q = PQ Q hQ := by
    intro Q hQ; simp [PQ', hQ]
  have hP_sub : P ⊆ points := by
    intro x hx
    rcases Finset.mem_biUnion.mp hx with ⟨Q, hQ, hxQ⟩
    have h_eq : PQ' Q = PQ Q hQ := hPQ'_eq Q hQ
    rw [h_eq] at hxQ
    have h : PQ Q hQ ⊆ pointsInQ Q := hPQ_sub Q hQ
    exact (Finset.mem_filter.mp (h hxQ)).1
  have hQs_nonempty : Qs.Nonempty := h_points_nonempty.image _
  have hP_nonempty : P.Nonempty := by
    rcases hQs_nonempty with ⟨Q, hQ⟩
    have h2 : 0 < k Q := h_k_pos Q hQ
    have h3 : (PQ Q hQ).card = k Q := hPQ_card Q hQ
    have h4 : 0 < (PQ Q hQ).card := by rw [h3]; exact h2
    have h5 : (PQ Q hQ).Nonempty := Finset.card_pos.mp h4
    have h5' : (PQ' Q).Nonempty := by
      rw [hPQ'_eq Q hQ]; exact h5
    exact h5'.mono (Finset.subset_biUnion_of_mem PQ' hQ)
  have h_coverage : P.image (containingSquare hnm) = Qs := by
    apply Finset.ext
    intro Q
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨p, hp, rfl⟩
      rcases Finset.mem_biUnion.mp hp with ⟨Q', hQ', hpQ'⟩
      have h_eq1 : PQ' Q' = PQ Q' hQ' := hPQ'_eq Q' hQ'
      rw [h_eq1] at hpQ'
      have h_cont : squareContained hnm p Q' :=
        (Finset.mem_filter.mp (hPQ_sub Q' hQ' hpQ')).2
      have h_eq : containingSquare hnm p = Q' :=
        (squareContained_iff_containingSquare hnm p Q').mp h_cont
      rw [h_eq]; exact hQ'
    · intro hQ
      have h2 : 0 < k Q := h_k_pos Q hQ
      have h3 : (PQ Q hQ).card = k Q := hPQ_card Q hQ
      have h4 : 0 < (PQ Q hQ).card := by rw [h3]; exact h2
      have h5 : (PQ Q hQ).Nonempty := Finset.card_pos.mp h4
      rcases h5 with ⟨p, hp⟩
      have h_cont : squareContained hnm p Q :=
        (Finset.mem_filter.mp (hPQ_sub Q hQ hp)).2
      have h_eq : containingSquare hnm p = Q :=
        (squareContained_iff_containingSquare hnm p Q).mp h_cont
      have h6 : p ∈ P := Finset.mem_biUnion.mpr ⟨Q, hQ, by
        rw [hPQ'_eq Q hQ]; exact hp⟩
      exact ⟨p, h6, h_eq⟩
  have h_density : ∀ Q ∈ Qs,
      ((P.filter fun p => squareContained hnm p Q).card : ℝ) ≥
        ((pointsInQ Q).card : ℝ) / (b : ℝ) := by
    intro Q hQ
    have h1 : P.filter (fun p => squareContained hnm p Q) = PQ Q hQ := by
      apply Finset.ext
      intro p
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hp, hcont⟩
        rcases Finset.mem_biUnion.mp hp with ⟨Q', hQ', hpQ'⟩
        have h_eq1 : PQ' Q' = PQ Q' hQ' := hPQ'_eq Q' hQ'
        rw [h_eq1] at hpQ'
        have h_cont' : squareContained hnm p Q' :=
          (Finset.mem_filter.mp (hPQ_sub Q' hQ' hpQ')).2
        have h_eq : Q' = Q := by
          have h1 : containingSquare hnm p = Q' :=
            (squareContained_iff_containingSquare hnm p Q').mp h_cont'
          have h2 : containingSquare hnm p = Q :=
            (squareContained_iff_containingSquare hnm p Q).mp hcont
          rw [h1] at h2; exact h2
        subst h_eq; exact hpQ'
      · intro hp
        exact ⟨Finset.mem_biUnion.mpr ⟨Q, hQ, by
          rw [hPQ'_eq Q hQ]; exact hp⟩,
          (Finset.mem_filter.mp (hPQ_sub Q hQ hp)).2⟩
    rw [h1, hPQ_card Q hQ]
    set a := (pointsInQ Q).card with ha
    have ha1 : 1 ≤ a := (h_nonempty_Q Q hQ).card_pos
    set q := (a + b - 1) / b with hq
    have h5 : q * b ≥ a := h_ceil a ha1
    have h6 : (q : ℝ) * (b : ℝ) ≥ (a : ℝ) := by
      have h7 : (q * b : ℕ) ≥ a := h5
      exact_mod_cast h7
    have h7 : (b : ℝ) > 0 := by exact_mod_cast hb_pos
    have h8 : (q : ℝ) ≥ (a : ℝ) / (b : ℝ) := by
      calc (q : ℝ)
        = (q : ℝ) * (b : ℝ) / (b : ℝ) := by field_simp [h7.ne'] <;> ring
      _ ≥ (a : ℝ) / (b : ℝ) := by gcongr
    simpa [hq] using h8
  exact ⟨P, hP_sub, hP_nonempty, h_coverage, h_density⟩

end PointSelection

end InductionOnScales
