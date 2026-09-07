module

/-
  Bridge: RangeUniformityProp → IsDyadicUniform

  Develops the thinning argument that converts range uniformity
  (counts in [N, 2N)) to exact uniformity (counts exactly N).

  Whiteprint target: section9 / multiscale_decomposition bridge
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.BasicUniformization
public import MyLeanRepo.DiscretisedFurstenbergEstimate.MultiscaleDecomposition.Base.DyadicUniform
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

noncomputable section

namespace DiscretisedFurstenbergEstimate.Section9Bridge

open DiscretisedFurstenbergEstimate
open DiscretisedFurstenbergEstimate.BasicUniformization

/-- Single-level thinning: given a finset S where each parent has either 0
    or between N and 2N children, produce S' ⊆ S where each parent has
    exactly N children (or 0 if the parent had 0).

    This is the key building block for RangeUniformityProp → IsDyadicUniform. -/
lemma single_level_thin {m : ℕ} (hm : 0 < m)
    (S : Finset (ℤ × ℤ)) (N : ℕ) (hN_pos : 0 < N)
    (h_unif : ∀ (g : ℤ × ℤ),
      (S.filter (fun y => parentBy m y = g)).card = 0 ∨
      (N ≤ (S.filter (fun y => parentBy m y = g)).card ∧
       (S.filter (fun y => parentBy m y = g)).card < 2 * N)) :
    ∃ (S' : Finset (ℤ × ℤ)), S' ⊆ S ∧
      (∀ (g : ℤ × ℤ),
        (S'.filter (fun y => parentBy m y = g)).card =
          if (S.filter (fun y => parentBy m y = g)).card = 0 then 0 else N) := by
  classical
  let parents := S.image (parentBy m)
  have h_main_choice : ∀ (g : ℤ × ℤ), g ∈ parents →
      ∃ (T : Finset (ℤ × ℤ)), T ⊆ S.filter (fun y => parentBy m y = g) ∧ T.card = N := by
    intro g hg
    let children := S.filter (fun y => parentBy m y = g)
    have h_card_pos : 0 < children.card := by
      rcases Finset.mem_image.mp hg with ⟨x, hx, h_eq⟩
      have h2 : x ∈ children := by
        simp only [children, Finset.mem_filter] <;> exact ⟨hx, h_eq⟩
      exact Finset.card_pos.mpr ⟨x, h2⟩
    have h2 : N ≤ children.card := by
      have h3 := h_unif g
      rcases h3 with (h3 | h3)
      · exfalso
        rw [h3] at h_card_pos <;> simpa using h_card_pos
      · exact h3.1
    exact Finset.exists_subset_card_eq h2
  choose f hf using h_main_choice
  let chooseN (g : ℤ × ℤ) : Finset (ℤ × ℤ) :=
    if hg : g ∈ parents then f g hg else ∅
  have hchooseN_eq : ∀ (g : ℤ × ℤ) (hg : g ∈ parents), chooseN g = f g hg := by
    intro g hg
    simp [chooseN, hg]
  let S' : Finset (ℤ × ℤ) := parents.biUnion chooseN
  have hS'_sub : S' ⊆ S := by
    intro x hx
    rcases Finset.mem_biUnion.mp hx with ⟨g, hg, hxg'⟩
    have h_eq : chooseN g = f g hg := hchooseN_eq g hg
    rw [h_eq] at hxg'
    have h_sub : (f g hg) ⊆ S.filter (fun y => parentBy m y = g) := (hf g hg).1
    have h_in_children : x ∈ S.filter (fun y => parentBy m y = g) := h_sub hxg'
    exact (Finset.mem_filter.mp h_in_children).1
  refine ⟨S', hS'_sub, ?_⟩
  intro g
  by_cases hg : (S.filter (fun y => parentBy m y = g)).card = 0
  · -- Parent has 0 children in S
    have h1 : g ∉ parents := by
      intro h2
      rcases Finset.mem_image.mp h2 with ⟨x, hx, h_eq⟩
      have h3 : x ∈ S.filter (fun y => parentBy m y = g) := by
        simp only [Finset.mem_filter] <;> exact ⟨hx, h_eq⟩
      have h4 : (S.filter (fun y => parentBy m y = g)).Nonempty := ⟨x, h3⟩
      have h5 : 0 < (S.filter (fun y => parentBy m y = g)).card := Finset.card_pos.mpr h4
      rw [hg] at h5 <;> simpa using h5
    have h_not_mem : ∀ (x : ℤ × ℤ), x ∉ S'.filter (fun y => parentBy m y = g) := by
      intro x hx
      have h5 : x ∈ S' := (Finset.mem_filter.mp hx).1
      rcases Finset.mem_biUnion.mp h5 with ⟨g', hg', hxg'⟩
      have h_eq' : chooseN g' = f g' hg' := hchooseN_eq g' hg'
      have h_in_f : x ∈ f g' hg' := by rw [←h_eq']; exact hxg'
      have h_sub' : (f g' hg') ⊆ S.filter (fun y => parentBy m y = g') := (hf g' hg').1
      have h6 : x ∈ S.filter (fun y => parentBy m y = g') := h_sub' h_in_f
      have h7 : parentBy m x = g' := (Finset.mem_filter.mp h6).2
      have h8 : parentBy m x = g := (Finset.mem_filter.mp hx).2
      rw [h7] at h8
      have h9 : g' = g := h8
      rw [h9] at hg'
      exact h1 hg'
    have h4 : (S'.filter (fun y => parentBy m y = g)).card = 0 := by
      have h_empty : (S'.filter (fun y => parentBy m y = g)) = ∅ := by
        exact Finset.eq_empty_of_forall_notMem h_not_mem
      rw [h_empty]
      simp
    rw [if_pos hg]
    exact h4
  · -- Parent has > 0 children
    have hg' : g ∈ parents := by
      let children := S.filter (fun y => parentBy m y = g)
      have h_nonempty : children.Nonempty := Finset.card_pos.mp (Nat.pos_of_ne_zero hg)
      rcases h_nonempty with ⟨x, hx⟩
      have h_x_in_S : x ∈ S := (Finset.mem_filter.mp hx).1
      have h_par : parentBy m x = g := (Finset.mem_filter.mp hx).2
      exact Finset.mem_image.mpr ⟨x, h_x_in_S, h_par⟩
    have h_disj : ∀ (g1 g2 : ℤ × ℤ), g1 ≠ g2 →
        Disjoint (chooseN g1) (chooseN g2) := by
      intro g1 g2 hne
      by_cases h1 : g1 ∈ parents
      · by_cases h2 : g2 ∈ parents
        · have h_eq1 : chooseN g1 = f g1 h1 := hchooseN_eq g1 h1
          have h_eq2 : chooseN g2 = f g2 h2 := hchooseN_eq g2 h2
          rw [h_eq1, h_eq2]
          rw [Finset.disjoint_left]
          intro x hx1 hx2
          have h_in1 : x ∈ S.filter (fun y => parentBy m y = g1) := (hf g1 h1).1 hx1
          have h_in2 : x ∈ S.filter (fun y => parentBy m y = g2) := (hf g2 h2).1 hx2
          have hpar1 : parentBy m x = g1 := (Finset.mem_filter.mp h_in1).2
          have hpar2 : parentBy m x = g2 := (Finset.mem_filter.mp h_in2).2
          rw [hpar1] at hpar2
          exact hne hpar2
        · have h_empty2 : chooseN g2 = ∅ := by
            simp [chooseN, h2]
          rw [h_empty2]
          simp
      · have h_empty1 : chooseN g1 = ∅ := by
          simp [chooseN, h1]
        rw [h_empty1]
        simp
    have h_filter : S'.filter (fun y => parentBy m y = g) = chooseN g := by
      apply Finset.Subset.antisymm
      · intro x hx
        have h_x_in_S' : x ∈ S' := (Finset.mem_filter.mp hx).1
        have h_par : parentBy m x = g := (Finset.mem_filter.mp hx).2
        rcases Finset.mem_biUnion.mp h_x_in_S' with ⟨g', hg_mem, hxg'⟩
        have h_par' : parentBy m x = g' := by
          have h_eq' : chooseN g' = f g' hg_mem := hchooseN_eq g' hg_mem
          have h_in_f : x ∈ f g' hg_mem := by rw [←h_eq']; exact hxg'
          have h_sub' : (f g' hg_mem) ⊆ S.filter (fun y => parentBy m y = g') := (hf g' hg_mem).1
          exact (Finset.mem_filter.mp (h_sub' h_in_f)).2
        have h_eq_g : g' = g := by
          rw [←h_par', h_par]
        rw [h_eq_g] at hxg'
        exact hxg'
      · intro x hx
        have h_eq : chooseN g = f g hg' := hchooseN_eq g hg'
        have h_in_f : x ∈ f g hg' := by rw [←h_eq]; exact hx
        have h_sub : (f g hg') ⊆ S.filter (fun y => parentBy m y = g) := (hf g hg').1
        have h_par : parentBy m x = g := (Finset.mem_filter.mp (h_sub h_in_f)).2
        have h_x_in_S' : x ∈ S' := by
          rw [Finset.mem_biUnion]
          exact ⟨g, hg', hx⟩
        exact Finset.mem_filter.mpr ⟨h_x_in_S', h_par⟩
    rw [h_filter, if_neg hg]
    have h_eq : chooseN g = f g hg' := hchooseN_eq g hg'
    rw [h_eq]
    exact (hf g hg').2

/-- Helper: image composition for parentBy. -/
lemma image_parentBy_comp (S : Finset (ℤ × ℤ)) (m1 m2 : ℕ) :
    (S.image (parentBy m2)).image (parentBy m1) = S.image (parentBy (m2 + m1)) := by
  ext x
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    have h : parentBy m1 (parentBy m2 z) = parentBy (m2 + m1) z := by
      rw [parentBy_comp m1 m2 z, add_comm]
    exact ⟨z, hz, h.symm⟩
  · rintro ⟨z, hz, h_eq⟩
    refine ⟨parentBy m2 z, ⟨z, hz, rfl⟩, ?_⟩
    have h : parentBy m1 (parentBy m2 z) = parentBy (m2 + m1) z := by
      rw [parentBy_comp m1 m2 z, add_comm]
    exact h_eq ▸ h

/-- Thinning at scale m preserves the set of distinct images at all coarser scales m' ≥ m,
    provided the thinning keeps at least 1 element per non-empty parent. -/
lemma thin_preserves_coarser_images {m : ℕ}
    (S S' : Finset (ℤ × ℤ)) (N : ℕ) (hN_pos : 0 < N)
    (hS'_sub : S' ⊆ S)
    (h_thin : ∀ (g : ℤ × ℤ),
      (S'.filter (fun y => parentBy m y = g)).card =
        if (S.filter (fun y => parentBy m y = g)).card = 0 then 0 else N) :
    ∀ (m' : ℕ), m ≤ m' → S'.image (parentBy m') = S.image (parentBy m') := by
  intro m' hle
  have h1 : S'.image (parentBy m') ⊆ S.image (parentBy m') := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨y, hy, rfl⟩
    exact Finset.mem_image.mpr ⟨y, hS'_sub hy, rfl⟩
  apply Finset.Subset.antisymm h1
  intro x hx
  rcases Finset.mem_image.mp hx with ⟨y, hy, rfl⟩
  let g := parentBy m y
  have h_count_pos : 0 < (S.filter (fun y => parentBy m y = g)).card := by
    apply Finset.card_pos.mpr
    exact ⟨y, Finset.mem_filter.mpr ⟨hy, rfl⟩⟩
  have h_count_S'_pos : 0 < (S'.filter (fun y => parentBy m y = g)).card := by
    rw [h_thin g, if_neg (ne_of_gt h_count_pos)]
    exact hN_pos
  rcases Finset.card_pos.mp h_count_S'_pos with ⟨z, hz⟩
  have hz_in_S' : z ∈ S' := (Finset.mem_filter.mp hz).1
  have hpar : parentBy m z = g := (Finset.mem_filter.mp hz).2
  have h_sum : m + (m' - m) = m' := by omega
  have h_main : parentBy m' z = parentBy m' y := by
    have h3 : parentBy m' z = parentBy (m + (m' - m)) z := by rw [h_sum]
    have h4 : parentBy (m + (m' - m)) z = parentBy (m' - m) (parentBy m z) := by
      have h_comm : m + (m' - m) = (m' - m) + m := by omega
      rw [h_comm]
      exact (parentBy_comp (m' - m) m z).symm
    have h5 : parentBy m' y = parentBy (m + (m' - m)) y := by rw [h_sum]
    have h6 : parentBy (m + (m' - m)) y = parentBy (m' - m) (parentBy m y) := by
      have h_comm : m + (m' - m) = (m' - m) + m := by omega
      rw [h_comm]
      exact (parentBy_comp (m' - m) m y).symm
    rw [h3, h4, h5, h6, hpar]
  exact Finset.mem_image.mpr ⟨z, hz_in_S', h_main⟩

/-- parentBy 0 is the identity. -/
lemma parentBy_zero_eq : parentBy 0 = id := by
  funext x
  simp [parentBy]
  <;> ring_nf

/-- If a sequence on Fin (m+2) is strictly increasing at each step, it is monotone. -/
lemma fin_strict_mono_succ {m : ℕ} {f : Fin (m + 2) → ℕ}
    (h_strict : ∀ (j : Fin (m + 1)), f j.castSucc < f (Fin.succ j)) :
    ∀ (i k : Fin (m + 2)), i.val ≤ k.val → f i ≤ f k := by
  have h_main : ∀ (d : ℕ), ∀ (i k : Fin (m + 2)), k.val = i.val + d → f i ≤ f k := by
    intro d
    induction d with
    | zero =>
      intro i k hk
      have h_eq : i = k := by
        apply Fin.ext
        rw [hk] <;> simp
      rw [h_eq]
    | succ d ih =>
      intro i k hk
      have h_k_pos : 0 < k.val := by
        rw [hk] <;> omega
      let j : Fin (m + 1) := ⟨k.val - 1, by omega⟩
      have h_ih' : f i ≤ f j.castSucc := by
        apply ih i j.castSucc
        simp [j, Fin.succ, hk] <;> omega
      have h_strict' : f j.castSucc < f (Fin.succ j) := h_strict j
      have h_k_eq : k = Fin.succ j := by
        apply Fin.ext
        simp [j, Fin.succ] <;> omega
      rw [h_k_eq]
      exact le_trans h_ih' (le_of_lt h_strict')
  intro i k hik
  exact h_main (k.val - i.val) i k (by omega)

/-- Partition a finset by its parent images: cardinality equals sum of fiber cardinalities. -/
lemma card_partition_by_parent (S : Finset (ℤ × ℤ)) (m : ℕ) :
    S.card = ∑ g ∈ S.image (parentBy m), (S.filter (fun y => parentBy m y = g)).card := by
  let f : (ℤ × ℤ) → (ℤ × ℤ) := parentBy m
  let parents := S.image f
  have h_disj : ∀ (g1 : ℤ × ℤ), g1 ∈ parents → ∀ (g2 : ℤ × ℤ), g2 ∈ parents → g1 ≠ g2 →
      Disjoint (S.filter (fun y => f y = g1)) (S.filter (fun y => f y = g2)) := by
    intro g1 _ g2 _ hne
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    have h1 : f x = g1 := (Finset.mem_filter.mp hx1).2
    have h2 : f x = g2 := (Finset.mem_filter.mp hx2).2
    rw [h1] at h2
    exact hne h2
  have h_union : parents.biUnion (fun g => S.filter (fun y => f y = g)) = S := by
    ext x
    simp only [parents, f, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨g, _, hx, _⟩; exact hx
    · intro hx; refine ⟨f x, ⟨x, hx, rfl⟩, ⟨hx, rfl⟩⟩
  have h_card : (parents.biUnion (fun g => S.filter (fun y => f y = g))).card =
      ∑ g ∈ parents, (S.filter (fun y => f y = g)).card := Finset.card_biUnion h_disj
  have h_goal : S.card = (parents.biUnion (fun g => S.filter (fun y => f y = g))).card :=
    congr_arg Finset.card h_union.symm
  rw [h_goal]
  exact h_card

/-- Single-level thinning retains at least half the elements: |S1| * 2 ≥ |S|.
    Since each parent has c children with N ≤ c < 2N, and we retain exactly N,
    the total retained is > 1/2 of the original. -/
lemma thin_density_bound {m : ℕ} (S S1 : Finset (ℤ × ℤ)) (N : ℕ) (hN_pos : 0 < N)
    (hS1_sub : S1 ⊆ S)
    (h_exact : ∀ (g : ℤ × ℤ),
      (S1.filter (fun y => parentBy m y = g)).card =
        if (S.filter (fun y => parentBy m y = g)).card = 0 then 0 else N)
    (h_unif : ∀ (g : ℤ × ℤ),
      (S.filter (fun y => parentBy m y = g)).card = 0 ∨
      (N ≤ (S.filter (fun y => parentBy m y = g)).card ∧
       (S.filter (fun y => parentBy m y = g)).card < 2 * N)) :
    S.card ≤ 2 * S1.card := by
  let parents := S.image (parentBy m)
  have h_parents_eq : S1.image (parentBy m) = parents :=
    thin_preserves_coarser_images S S1 N hN_pos hS1_sub h_exact m (by rfl)
  have h1 : S.card = ∑ g ∈ parents, (S.filter (fun y => parentBy m y = g)).card :=
    card_partition_by_parent S m
  have h2 : S1.card = ∑ g ∈ parents, (S1.filter (fun y => parentBy m y = g)).card := by
    rw [←h_parents_eq]
    exact card_partition_by_parent S1 m
  rw [h1, h2]
  have h3 : ∀ g ∈ parents, (S.filter (fun y => parentBy m y = g)).card ≤
      2 * (S1.filter (fun y => parentBy m y = g)).card := by
    intro g hg
    have h_pos : 0 < (S.filter (fun y => parentBy m y = g)).card := by
      rcases Finset.mem_image.mp hg with ⟨x, hx, rfl⟩
      apply Finset.card_pos.mpr
      exact ⟨x, Finset.mem_filter.mpr ⟨hx, rfl⟩⟩
    have h4 : (S1.filter (fun y => parentBy m y = g)).card = N := by
      rw [h_exact g, if_neg (ne_of_gt h_pos)]
    rw [h4]
    have h5 := h_unif g
    rcases h5 with (h5 | h5)
    · exfalso; rw [h5] at h_pos; simpa using h_pos
    · exact le_of_lt h5.2
  calc
    ∑ g ∈ parents, (S.filter (fun y => parentBy m y = g)).card ≤
        ∑ g ∈ parents, 2 * (S1.filter (fun y => parentBy m y = g)).card :=
      Finset.sum_le_sum h3
    _ = 2 * ∑ g ∈ parents, (S1.filter (fun y => parentBy m y = g)).card := by
      rw [Finset.mul_sum]

/-- Cardinality of elements whose parent lies in a given finset T',
    assuming each parent in T' has exactly N children. -/
lemma filtered_card_by_parents (S1 : Finset (ℤ × ℤ)) (m : ℕ) (N : ℕ)
    (T' : Finset (ℤ × ℤ))
    (h_fiber : ∀ g ∈ T', (S1.filter (fun y => parentBy m y = g)).card = N) :
    (S1.filter (fun q => parentBy m q ∈ T')).card = T'.card * N := by
  have h_disj : ∀ (g1 : ℤ × ℤ), g1 ∈ T' → ∀ (g2 : ℤ × ℤ), g2 ∈ T' → g1 ≠ g2 →
      Disjoint (S1.filter (fun y => parentBy m y = g1))
        (S1.filter (fun y => parentBy m y = g2)) := by
    intro g1 _ g2 _ hne
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    have h1 : parentBy m x = g1 := (Finset.mem_filter.mp hx1).2
    have h2 : parentBy m x = g2 := (Finset.mem_filter.mp hx2).2
    rw [h1] at h2
    exact hne h2
  have h_union : (S1.filter (fun q => parentBy m q ∈ T')) =
      T'.biUnion (fun g => S1.filter (fun y => parentBy m y = g)) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_biUnion]
    <;> aesop
  rw [h_union]
  rw [Finset.card_biUnion h_disj]
  have h4 : ∑ g ∈ T', (S1.filter (fun y => parentBy m y = g)).card = ∑ g ∈ T', N := by
    apply Finset.sum_congr rfl
    intro g hg
    exact h_fiber g hg
  rw [h4]
  simp [Finset.sum_const]
  <;> ring

/-- Multi-level thinning: convert RangeUniformityProp to exact uniformity at all levels.
    Includes retained-density estimate: |S'| · 2^n ≥ |S|. -/
theorem multi_level_thin (n : ℕ) :
    ∀ (a : Fin (n + 1) → ℕ) (ha_strict : ∀ j : Fin n, a j.castSucc < a (Fin.succ j))
      (S : Finset (ℤ × ℤ)) (N : Fin n → ℕ),
      RangeUniformityProp n a S N →
      ∃ (S' : Finset (ℤ × ℤ)), S' ⊆ S ∧ S'.Nonempty ∧
        (∀ (j : Fin n) (g : ℤ × ℤ),
          let k := a (Fin.last n)
          let m_fine := k - a (Fin.succ j)
          let m_coarse := a (Fin.succ j) - a j.castSucc
          let fineSquares := S'.image (parentBy m_fine)
          let count := (fineSquares.filter (fun idx => parentBy m_coarse idx = g)).card
          count = 0 ∨ count = N j) ∧
        (S'.card : ℝ) * (2 : ℝ)^n ≥ (S.card : ℝ) := by
  induction n with
  | zero =>
    intro a _ S N h_range
    refine ⟨S, by tauto, h_range.1, ?_, ?_⟩
    · intro j; exact Fin.elim0 j
    · simp [pow_zero]
      <;> linarith
  | succ n ih =>
    intro a ha_strict S N h_range
    let j_last : Fin (n + 1) := Fin.last n
    let m_finest := a (Fin.succ j_last) - a j_last.castSucc
    have hm_finest_pos : 0 < m_finest := by
      have h := ha_strict j_last
      simpa [m_finest, j_last] using h
    have hN_last_pos : 0 < N j_last := by
      have h1 : 1 ≤ N j_last := h_range.2.1 j_last
      linarith
    have h_finest_m_fine : a (Fin.last (n + 1)) - a (Fin.succ j_last) = 0 := by
      simp [j_last, Fin.last] <;> omega
    have h_finest_m_coarse : a (Fin.succ j_last) - a j_last.castSucc = m_finest := by rfl
    have h_unif_finest : ∀ (g : ℤ × ℤ),
        (S.filter (fun y => parentBy m_finest y = g)).card = 0 ∨
        (N j_last ≤ (S.filter (fun y => parentBy m_finest y = g)).card ∧
         (S.filter (fun y => parentBy m_finest y = g)).card < 2 * N j_last) := by
      intro g
      have h := h_range.2.2 j_last g
      dsimp only at h
      rw [h_finest_m_fine, parentBy_zero_eq] at h
      simpa [h_finest_m_coarse] using h
    rcases single_level_thin hm_finest_pos S (N j_last) hN_last_pos h_unif_finest with
      ⟨S1, hS1_sub, h_exact_finest⟩
    have hS1_nonempty : S1.Nonempty := by
      rcases h_range.1 with ⟨x, hx⟩
      let g := parentBy m_finest x
      have h_count_pos : 0 < (S.filter (fun y => parentBy m_finest y = g)).card := by
        apply Finset.card_pos.mpr
        exact ⟨x, Finset.mem_filter.mpr ⟨hx, rfl⟩⟩
      have h_count_S1_pos : 0 < (S1.filter (fun y => parentBy m_finest y = g)).card := by
        rw [h_exact_finest g, if_neg (ne_of_gt h_count_pos)]
        exact hN_last_pos
      have h_S1_card_pos : 0 < S1.card := by
        have h_le : (S1.filter (fun y => parentBy m_finest y = g)).card ≤ S1.card :=
          Finset.card_le_card (Finset.filter_subset _ _)
        linarith
      exact Finset.card_pos.mp h_S1_card_pos
    let T1 := S1.image (parentBy m_finest)
    have hT1_nonempty : T1.Nonempty := hS1_nonempty.image _
    have h_pres := thin_preserves_coarser_images S S1 (N j_last) hN_last_pos hS1_sub h_exact_finest
    let a' : Fin (n + 1) → ℕ := fun i => a i.castSucc
    let N' : Fin n → ℕ := fun j => N j.castSucc
    have ha'_strict : ∀ j : Fin n, a' j.castSucc < a' (Fin.succ j) := by
      intro j; exact ha_strict j.castSucc
    have h_a'_last : a' (Fin.last n) = a j_last.castSucc := by
      unfold a'; rfl
    have h_a'_succ : ∀ (j : Fin n), a' (Fin.succ j) = a (Fin.succ j.castSucc) := by
      intro j; unfold a'; rfl
    have h_succ_jlast : a (Fin.succ j_last) = a (Fin.last (n + 1)) := by rfl
    have h_id1 : ∀ (j : Fin n),
        a' (Fin.last n) - a' (Fin.succ j) + m_finest =
        a (Fin.last (n + 1)) - a (Fin.succ j.castSucc) := by
      intro j
      have h_mfinest_eq : m_finest = a (Fin.succ j_last) - a j_last.castSucc := by rfl
      have h_mono := fin_strict_mono_succ ha_strict
      have h_le1 : a (Fin.succ j.castSucc) ≤ a j_last.castSucc := by
        apply h_mono (Fin.succ j.castSucc) j_last.castSucc
        simp [Fin.succ, j_last, Fin.last] <;> omega
      have h_le2 : a j_last.castSucc ≤ a (Fin.succ j_last) := by
        have h_strict : a j_last.castSucc < a (Fin.succ j_last) := ha_strict j_last
        exact le_of_lt h_strict
      have h_arith : a j_last.castSucc - a (Fin.succ j.castSucc) +
          (a (Fin.succ j_last) - a j_last.castSucc) =
          a (Fin.succ j_last) - a (Fin.succ j.castSucc) := by
        omega
      have h_main : a' (Fin.last n) - a' (Fin.succ j) + m_finest =
          a j_last.castSucc - a (Fin.succ j.castSucc) +
          (a (Fin.succ j_last) - a j_last.castSucc) := by
        rw [h_a'_last, h_a'_succ j, h_mfinest_eq]
      rw [h_main, h_arith, h_succ_jlast]
    have h_id2 : ∀ (j : Fin n),
        a' (Fin.succ j) - a' j.castSucc =
        a (Fin.succ j.castSucc) - a j.castSucc.castSucc := by
      intro j
      simp [a', Fin.succ] <;> rfl
    have h_image_eq : ∀ (j : Fin n),
        T1.image (parentBy (a' (Fin.last n) - a' (Fin.succ j))) =
        S.image (parentBy (a (Fin.last (n + 1)) - a (Fin.succ j.castSucc))) := by
      intro j
      have h_sum1 : a' (Fin.last n) - a' (Fin.succ j) + m_finest =
          a (Fin.last (n + 1)) - a (Fin.succ j.castSucc) := h_id1 j
      have h_sum2 : m_finest + (a' (Fin.last n) - a' (Fin.succ j)) =
          a (Fin.last (n + 1)) - a (Fin.succ j.castSucc) := by
        rw [add_comm]; exact h_sum1
      have h : T1.image (parentBy (a' (Fin.last n) - a' (Fin.succ j))) =
          S1.image (parentBy (a' (Fin.last n) - a' (Fin.succ j) + m_finest)) := by
        have h_T1_def : T1 = S1.image (parentBy m_finest) := by rfl
        rw [h_T1_def]
        have h_comm : a' (Fin.last n) - a' (Fin.succ j) + m_finest =
            m_finest + (a' (Fin.last n) - a' (Fin.succ j)) := by ring
        rw [h_comm]
        exact image_parentBy_comp S1 (a' (Fin.last n) - a' (Fin.succ j)) m_finest
      rw [h, h_sum1]
      exact h_pres _ (by omega)
    have h_range_T1 : RangeUniformityProp n a' T1 N' := by
      refine ⟨hT1_nonempty, ?_, ?_⟩
      · intro j; exact h_range.2.1 j.castSucc
      · intro j g
        have h_eq := h_image_eq j
        have h_orig := h_range.2.2 j.castSucc g
        dsimp only at h_orig ⊢
        rw [h_eq]
        rw [h_id2 j] at *
        exact h_orig
    rcases ih a' ha'_strict T1 N' h_range_T1 with
      ⟨T', hT'_sub, hT'_nonempty, h_exact_coarse, h_ih_density⟩
    let S' : Finset (ℤ × ℤ) := S1.filter (fun q => parentBy m_finest q ∈ T')
    have hS'_sub_S1 : S' ⊆ S1 := Finset.filter_subset _ _
    have hS'_sub : S' ⊆ S := hS'_sub_S1.trans hS1_sub
    have hS'_nonempty : S'.Nonempty := by
      rcases hT'_nonempty with ⟨t, ht⟩
      have h1 : t ∈ T1 := hT'_sub ht
      rcases Finset.mem_image.mp h1 with ⟨s1, hs1, rfl⟩
      have h2 : s1 ∈ S' := by
        simp only [S', Finset.mem_filter] <;> exact ⟨hs1, ht⟩
      exact ⟨s1, h2⟩
    have hT'_eq : S'.image (parentBy m_finest) = T' := by
      ext g
      simp only [S', Finset.mem_image, Finset.mem_filter]
      constructor
      · rintro ⟨q, ⟨hq, hq'⟩, rfl⟩; exact hq'
      · intro hg
        have h1 : g ∈ T1 := hT'_sub hg
        rcases Finset.mem_image.mp h1 with ⟨t, ht, rfl⟩
        have h2 : parentBy m_finest t ∈ T' := hg
        exact ⟨t, ⟨ht, h2⟩, rfl⟩
    have h_exact_S'_finest : ∀ (g : ℤ × ℤ),
        (S'.filter (fun y => parentBy m_finest y = g)).card = 0 ∨
        (S'.filter (fun y => parentBy m_finest y = g)).card = N j_last := by
      intro g
      by_cases hg : g ∈ T'
      · have h_eq : S'.filter (fun y => parentBy m_finest y = g) =
            S1.filter (fun y => parentBy m_finest y = g) := by
          ext x
          simp only [S', Finset.mem_filter]
          constructor
          · intro h
            exact ⟨h.1.1, h.2⟩
          · intro h
            have h_par : parentBy m_finest x = g := h.2
            have h_in_T' : parentBy m_finest x ∈ T' := by rw [h_par]; exact hg
            exact ⟨⟨h.1, h_in_T'⟩, h_par⟩
        rw [h_eq]
        have h_count_pos : 0 < (S.filter (fun y => parentBy m_finest y = g)).card := by
          have h_g_in_T1 : g ∈ T1 := hT'_sub hg
          rcases Finset.mem_image.mp h_g_in_T1 with ⟨x, hx, rfl⟩
          apply Finset.card_pos.mpr
          exact ⟨x, Finset.mem_filter.mpr ⟨hS1_sub hx, rfl⟩⟩
        have h : (S1.filter (fun y => parentBy m_finest y = g)).card = N j_last := by
          rw [h_exact_finest g, if_neg (ne_of_gt h_count_pos)]
        exact Or.inr h
      · have h_eq : S'.filter (fun y => parentBy m_finest y = g) = ∅ := by
          ext x
          simp only [S', Finset.mem_filter]
          constructor
          · intro h
            have h_x_in_S1 : x ∈ S1 := h.1.1
            have h_in_T' : parentBy m_finest x ∈ T' := h.1.2
            have h_par : parentBy m_finest x = g := h.2
            rw [h_par] at h_in_T'
            exact False.elim (hg h_in_T')
          · intro h; contradiction
        rw [h_eq]; simp
    have h_coarse_image : ∀ (j : Fin n),
        S'.image (parentBy (a (Fin.last (n + 1)) - a (Fin.succ j.castSucc))) =
        T'.image (parentBy (a' (Fin.last n) - a' (Fin.succ j))) := by
      intro j
      have h_sum1 : a' (Fin.last n) - a' (Fin.succ j) + m_finest =
          a (Fin.last (n + 1)) - a (Fin.succ j.castSucc) := h_id1 j
      have h_sum2 : a (Fin.last (n + 1)) - a (Fin.succ j.castSucc) =
          a' (Fin.last n) - a' (Fin.succ j) + m_finest := h_sum1.symm
      have h_sum3 : a (Fin.last (n + 1)) - a (Fin.succ j.castSucc) =
          m_finest + (a' (Fin.last n) - a' (Fin.succ j)) := by
        rw [h_sum2, add_comm]
      rw [h_sum3]
      have h : S'.image (parentBy (m_finest + (a' (Fin.last n) - a' (Fin.succ j)))) =
          (S'.image (parentBy m_finest)).image (parentBy (a' (Fin.last n) - a' (Fin.succ j))) := by
        have h_comm : m_finest + (a' (Fin.last n) - a' (Fin.succ j)) =
            a' (Fin.last n) - a' (Fin.succ j) + m_finest := by ring
        rw [h_comm]
        have h_comm2 : a' (Fin.last n) - a' (Fin.succ j) + m_finest =
            m_finest + (a' (Fin.last n) - a' (Fin.succ j)) := by ring
        rw [h_comm2]
        exact (image_parentBy_comp S' (a' (Fin.last n) - a' (Fin.succ j)) m_finest).symm
      rw [h, hT'_eq]
    have h_density1 : S.card ≤ 2 * S1.card :=
      thin_density_bound S S1 (N j_last) hN_last_pos hS1_sub h_exact_finest h_unif_finest
    have h_fiber_T1 : ∀ g ∈ T1, (S1.filter (fun y => parentBy m_finest y = g)).card = N j_last := by
      intro g hg
      have h_pos : 0 < (S.filter (fun y => parentBy m_finest y = g)).card := by
        rcases Finset.mem_image.mp hg with ⟨x, hx, rfl⟩
        apply Finset.card_pos.mpr
        exact ⟨x, Finset.mem_filter.mpr ⟨hS1_sub hx, rfl⟩⟩
      rw [h_exact_finest g, if_neg (ne_of_gt h_pos)]
    have h_S1_card : S1.card = T1.card * N j_last := by
      have h_filter_all : S1.filter (fun q => parentBy m_finest q ∈ T1) = S1 := by
        ext x
        simp only [T1, Finset.mem_filter, Finset.mem_image]
        constructor
        · intro h; exact h.1
        · intro hx
          exact ⟨hx, ⟨x, hx, rfl⟩⟩
      have h := filtered_card_by_parents S1 m_finest (N j_last) T1 h_fiber_T1
      rw [h_filter_all] at h
      exact h
    have h_fiber_T' : ∀ g ∈ T', (S1.filter (fun y => parentBy m_finest y = g)).card = N j_last := by
      intro g hg
      have h_g_in_T1 : g ∈ T1 := hT'_sub hg
      exact h_fiber_T1 g h_g_in_T1
    have h_S'_card : S'.card = T'.card * N j_last :=
      filtered_card_by_parents S1 m_finest (N j_last) T' h_fiber_T'
    have h_density_main : (S'.card : ℝ) * (2 : ℝ)^(n + 1) ≥ (S.card : ℝ) := by
      have h1 : (S'.card : ℝ) * (2 : ℝ)^n ≥ (S1.card : ℝ) := by
        rw [h_S'_card, h_S1_card]
        have hN_pos' : (N j_last : ℝ) > 0 := by exact_mod_cast hN_last_pos
        have h_mult : (T'.card : ℝ) * (2 : ℝ)^n ≥ (T1.card : ℝ) := h_ih_density
        have h : (T'.card : ℝ) * (2 : ℝ)^n * (N j_last : ℝ) ≥ (T1.card : ℝ) * (N j_last : ℝ) :=
          mul_le_mul_of_nonneg_right h_mult (by linarith)
        simpa [mul_assoc, mul_comm, mul_left_comm] using h
      have h2 : (S1.card : ℝ) * 2 ≥ (S.card : ℝ) := by
        have h3 : S.card ≤ 2 * S1.card := h_density1
        have h4 : (S.card : ℝ) ≤ (2 * S1.card : ℝ) := by exact_mod_cast h3
        have h5 : (2 * S1.card : ℝ) = (S1.card : ℝ) * 2 := by ring
        rw [h5] at h4
        exact h4
      calc
        (S'.card : ℝ) * (2 : ℝ)^(n + 1)
          = (S'.card : ℝ) * (2 : ℝ)^n * 2 := by ring_nf
        _ ≥ (S1.card : ℝ) * 2 := by gcongr
        _ ≥ (S.card : ℝ) := h2
    refine ⟨S', hS'_sub, hS'_nonempty, ?_, h_density_main⟩
    intro j g
    by_cases h : j = j_last
    · subst h
      dsimp only
      rw [h_finest_m_fine, parentBy_zero_eq, h_finest_m_coarse]
      have h_image_id : S'.image id = S' := by ext x; simp
      rw [h_image_id]
      exact h_exact_S'_finest g
    · have h_j_lt_last : j.val < n := by
        have h3 : j ≠ j_last := h
        have h4 : j.val ≤ n := j.is_le
        have h5 : j_last.val = n := by
          simp [j_last, Fin.last] <;> omega
        by_contra h6
        have h7 : j.val = n := by omega
        have h8 : j = j_last := by
          apply Fin.ext
          rw [h7, h5]
        exact h3 h8
      let j' : Fin n := ⟨j.val, h_j_lt_last⟩
      have h_jcast : j = j'.castSucc := by
        apply Fin.ext
        simp [j'] <;> omega
      have h_main_img : T'.image (parentBy (a' (Fin.last n) - a' (Fin.succ j'))) =
          S'.image (parentBy (a (Fin.last (n + 1)) - a (Fin.succ j'.castSucc))) :=
        (h_coarse_image j').symm
      have h_coarse := h_exact_coarse j' g
      dsimp only at h_coarse
      rw [h_main_img] at h_coarse
      rw [h_id2 j'] at h_coarse
      simpa [h_jcast] using h_coarse

end DiscretisedFurstenbergEstimate.Section9Bridge
