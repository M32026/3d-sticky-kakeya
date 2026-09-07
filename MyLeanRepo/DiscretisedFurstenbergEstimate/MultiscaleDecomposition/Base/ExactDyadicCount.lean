module

/-
  Exact dyadic cardinality formula for IsDyadicUniform with 1/Δ ∈ ℕ.
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.MultiscaleDecomposition.Base.DyadicUniform
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

noncomputable section

namespace DirecretisedFurstenbergEstimate.MultiscaleDecomposition

open DirecretisedFurstenbergEstimate


/-! # Integer division bounds -/

lemma int_ediv_bounds (n : ℕ) (hn_pos : 0 < n) (q : ℤ) :
    (↑(q / (n : ℤ)) : ℝ) ≤ (q : ℝ) / (n : ℝ) ∧
    ((q : ℝ) + 1) / (n : ℝ) ≤ (↑(q / (n : ℤ)) + 1) := by
  let n' : ℤ := (n : ℤ)
  have h_n'_pos : 0 < n' := by
    have h : (0 : ℤ) < (n : ℤ) := by exact_mod_cast hn_pos
    simpa [n'] using h
  have h1 : q = (q / n') * n' + (q % n') := Eq.symm (Int.ediv_mul_add_emod q n')
  have h2 : 0 ≤ q % n' := Int.emod_nonneg q h_n'_pos.ne'
  have h3 : q % n' < n' := Int.emod_lt_of_pos q h_n'_pos
  have h4 : q + 1 ≤ (q / n' + 1) * n' := by
    have h5 : q + 1 = (q / n') * n' + ((q % n') + 1) := by
      have h51 : q = (q / n') * n' + (q % n') := h1
      linarith
    rw [h5]
    have h6 : (q % n') + 1 ≤ n' := by linarith
    linarith
  have hpos : 0 < (n : ℝ) := by exact_mod_cast hn_pos
  constructor
  · have h5 : (↑(q / n') : ℝ) * (n : ℝ) ≤ (q : ℝ) := by
      have h6 : (q / n') * n' ≤ q := by omega
      exact_mod_cast h6
    calc (↑(q / n') : ℝ)
      = (↑(q / n') : ℝ) * (n : ℝ) / (n : ℝ) := by field_simp [hpos.ne'] <;> ring
    _ ≤ (q : ℝ) / (n : ℝ) := by gcongr
  · have h5 : (q : ℝ) + 1 ≤ (↑(q / n' + 1) : ℝ) * (n : ℝ) := by exact_mod_cast h4
    calc ((q : ℝ) + 1) / (n : ℝ)
      ≤ ((↑(q / n' + 1) : ℝ) * (n : ℝ)) / (n : ℝ) := by gcongr
    _ = (↑(q / n' + 1) : ℝ) := by field_simp [hpos.ne'] <;> ring
    _ = (↑(q / n') : ℝ) + 1 := by simp

/-- Overlap equality for integer-indexed half-open intervals. -/
lemma int_interval_overlap_eq (a b : ℤ) (L : ℝ) (hL_pos : 0 < L) (x : ℝ)
    (h1 : (a : ℝ) * L ≤ x) (h2 : x < ((a : ℝ) + 1) * L)
    (h3 : (b : ℝ) * L ≤ x) (h4 : x < ((b : ℝ) + 1) * L) : a = b := by
  by_cases h : a < b
  · have h5 : a + 1 ≤ b := by linarith
    have h6 : ((a : ℝ) + 1) * L ≤ (b : ℝ) * L :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast h5) hL_pos.le
    linarith
  · by_cases h' : b < a
    · have h5 : b + 1 ≤ a := by linarith
      have h6 : ((b : ℝ) + 1) * L ≤ (a : ℝ) * L :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast h5) hL_pos.le
      linarith
    · have h'' : a = b := by linarith
      exact h''

/-! # Parent-child containment -/

lemma dyadicSquare_child_contained_in_parent_general
    {n : ℕ} (hn_pos : 0 < n) {Δ : ℝ} (hΔ_int : (1 : ℝ) = (n : ℝ) * Δ)
    (k : ℕ) (q : ℤ × ℤ) :
    dyadicSquare (Δ ^ (k + 1)) q.1 q.2 ⊆
    dyadicSquare (Δ ^ k) (q.1 / (n : ℤ)) (q.2 / (n : ℤ)) := by
  have hΔ_pos : 0 < Δ := by
    have h : (n : ℝ) * Δ = 1 := Eq.symm hΔ_int
    have h' : 0 < (n : ℝ) := by exact_mod_cast hn_pos
    nlinarith
  have h1 : Δ ^ (k + 1) = Δ ^ k / (n : ℝ) := by
    have h2 : (n : ℝ) * Δ = 1 := Eq.symm hΔ_int
    have h' : 0 < (n : ℝ) := by exact_mod_cast hn_pos
    calc Δ ^ (k + 1) = Δ * Δ ^ k := by ring
      _ = (Δ ^ k) * Δ := by ring
      _ = (Δ ^ k) / (n : ℝ) := by
        have h3 : Δ = 1 / (n : ℝ) := by field_simp [h'] <;> linarith
        rw [h3] <;> ring
  intro x hx
  simp only [dyadicSquare, Set.mem_setOf_eq] at hx ⊢
  have hq1 := int_ediv_bounds n hn_pos q.1
  have hq2 := int_ediv_bounds n hn_pos q.2
  constructor
  · constructor
    · calc (↑(q.1 / (n : ℤ)) : ℝ) * Δ ^ k
        ≤ ((q.1 : ℝ) / (n : ℝ)) * Δ ^ k := by gcongr; exact hq1.1
      _ = (q.1 : ℝ) * (Δ ^ k / (n : ℝ)) := by ring
      _ = (q.1 : ℝ) * Δ ^ (k + 1) := by have h_eq := h1; rw [h_eq]
      _ ≤ x 0 := hx.1.1
    · calc x 0
        < ((q.1 : ℝ) + 1) * Δ ^ (k + 1) := hx.1.2
      _ = (((q.1 : ℝ) + 1) / (n : ℝ)) * Δ ^ k := by rw [h1] <;> ring
      _ ≤ (↑(q.1 / (n : ℤ)) + 1) * Δ ^ k := by gcongr; exact hq1.2
  constructor
  · calc (↑(q.2 / (n : ℤ)) : ℝ) * Δ ^ k
      ≤ ((q.2 : ℝ) / (n : ℝ)) * Δ ^ k := by gcongr; exact hq2.1
    _ = (q.2 : ℝ) * (Δ ^ k / (n : ℝ)) := by ring
    _ = (q.2 : ℝ) * Δ ^ (k + 1) := by have h_eq := h1; rw [h_eq]
    _ ≤ x 1 := hx.2.1
  · calc x 1
      < ((q.2 : ℝ) + 1) * Δ ^ (k + 1) := hx.2.2
    _ = (((q.2 : ℝ) + 1) / (n : ℝ)) * Δ ^ k := by rw [h1] <;> ring
    _ ≤ (↑(q.2 / (n : ℤ)) + 1) * Δ ^ k := by gcongr; exact hq2.2

/-! # Nested containment (b ≥ a) -/

lemma dyadicSquare_nested_containment
    {n : ℕ} (hn_pos : 0 < n) {Δ : ℝ} (hΔ_int : (1 : ℝ) = (n : ℝ) * Δ)
    {a b : ℕ} (hab : a ≤ b)
    {p q : ℤ × ℤ}
    (h_inter : (dyadicSquare (Δ ^ b) q.1 q.2 ∩ dyadicSquare (Δ ^ a) p.1 p.2).Nonempty) :
    dyadicSquare (Δ ^ b) q.1 q.2 ⊆ dyadicSquare (Δ ^ a) p.1 p.2 := by
  have h_main : ∀ (b : ℕ), a ≤ b → ∀ (q : ℤ × ℤ),
      (dyadicSquare (Δ ^ b) q.1 q.2 ∩ dyadicSquare (Δ ^ a) p.1 p.2).Nonempty →
      dyadicSquare (Δ ^ b) q.1 q.2 ⊆ dyadicSquare (Δ ^ a) p.1 p.2 := by
    intro b
    induction b with
    | zero =>
      intro hab q h_inter
      have ha0 : a = 0 := by omega
      subst ha0
      rcases h_inter with ⟨x, hx1, hx2⟩
      simp only [dyadicSquare, Set.mem_setOf_eq] at hx1 hx2
      have h_pos : (0 : ℝ) < Δ ^ 0 := by positivity
      have h_eq1 : q.1 = p.1 := int_interval_overlap_eq q.1 p.1 1 h_pos (x 0)
        hx1.1.1 hx1.1.2 hx2.1.1 hx2.1.2
      have h_eq2 : q.2 = p.2 := int_interval_overlap_eq q.2 p.2 1 h_pos (x 1)
        hx1.2.1 hx1.2.2 hx2.2.1 hx2.2.2
      rw [h_eq1, h_eq2] <;> exact subset_refl
    | succ b ih =>
      intro hab q h_inter
      by_cases h_ab : a ≤ b
      · rcases h_inter with ⟨x, hx_fine, hx_coarse⟩
        let parent : ℤ × ℤ := (q.1 / (n : ℤ), q.2 / (n : ℤ))
        have h_parent_contain : dyadicSquare (Δ ^ (b + 1)) q.1 q.2 ⊆ dyadicSquare (Δ ^ b) parent.1 parent.2 :=
          dyadicSquare_child_contained_in_parent_general hn_pos hΔ_int b q
        have h_parent_inter : (dyadicSquare (Δ ^ b) parent.1 parent.2 ∩ dyadicSquare (Δ ^ a) p.1 p.2).Nonempty :=
          ⟨x, h_parent_contain hx_fine, hx_coarse⟩
        have h_ih' := ih h_ab parent h_parent_inter
        exact subset_trans h_parent_contain h_ih'
      · have h_eq : a = b + 1 := by omega
        subst h_eq
        rcases h_inter with ⟨x, hx1, hx2⟩
        simp only [dyadicSquare, Set.mem_setOf_eq] at hx1 hx2
        have hΔ_pos : 0 < Δ := by
          have h : (n : ℝ) * Δ = 1 := Eq.symm hΔ_int
          have h' : 0 < (n : ℝ) := by exact_mod_cast hn_pos
          nlinarith
        have h_pos : 0 < Δ ^ (b + 1) := pow_pos hΔ_pos (b + 1)
        have h_eq1 : q.1 = p.1 := int_interval_overlap_eq q.1 p.1 (Δ ^ (b + 1)) h_pos (x 0)
          hx1.1.1 hx1.1.2 hx2.1.1 hx2.1.2
        have h_eq2 : q.2 = p.2 := int_interval_overlap_eq q.2 p.2 (Δ ^ (b + 1)) h_pos (x 1)
          hx1.2.1 hx1.2.2 hx2.2.1 hx2.2.2
        rw [h_eq1, h_eq2] <;> exact subset_refl
  exact h_main b hab q h_inter

/-! # Same-level dyadic square equality -/

lemma dyadicSquare_same_level_eq {δ : ℝ} (hδ : 0 < δ) {p q : ℤ × ℤ}
    (h_inter : (dyadicSquare δ p.1 p.2 ∩ dyadicSquare δ q.1 q.2).Nonempty) :
    p = q := by
  rcases h_inter with ⟨x, hx1, hx2⟩
  simp only [dyadicSquare, Set.mem_setOf_eq] at hx1 hx2
  have h_eq1 : p.1 = q.1 := int_interval_overlap_eq p.1 q.1 δ hδ (x 0)
    hx1.1.1 hx1.1.2 hx2.1.1 hx2.1.2
  have h_eq2 : p.2 = q.2 := int_interval_overlap_eq p.2 q.2 δ hδ (x 1)
    hx1.2.1 hx1.2.2 hx2.2.1 hx2.2.2
  exact Prod.ext h_eq1 h_eq2

/-! # Exact multilevel dyadic count formula (Prop 8.1 central identity)

    For 1/Δ = n ∈ ℕ, the number of level-b dyadic squares intersecting
    P ∩ Q_a equals the product of branching numbers N(a)⋯N(b-1). -/

lemma dyadicSquareCount_multilevel
    {P : Set EuclideanPlane} {m : ℕ} {Δ : ℝ} {N : ℕ → ℕ}
    (h_uniform : IsDyadicUniform P m Δ N)
    {n : ℕ} (hn_pos : 0 < n) (hΔ_int : (1 : ℝ) = (n : ℝ) * Δ)
    {a b : ℕ} (hab : a ≤ b) (hbm : b ≤ m)
    (i j : ℤ) (hQ : (P ∩ dyadicSquare (Δ ^ a) i j).Nonempty) :
    dyadicSquareCount (Δ ^ b) (P ∩ dyadicSquare (Δ ^ a) i j) =
      ↑(∏ k ∈ Finset.Ico a b, N k) := by
  classical
  let Q_a := dyadicSquare (Δ ^ a) i j
  let S (k : ℕ) : Set (ℤ × ℤ) :=
    {q | ((P ∩ Q_a) ∩ dyadicSquare (Δ ^ k) q.1 q.2).Nonempty}
  let children (k : ℕ) (q : ℤ × ℤ) : Set (ℤ × ℤ) :=
    {r | ((P ∩ dyadicSquare (Δ ^ k) q.1 q.2) ∩ dyadicSquare (Δ ^ (k + 1)) r.1 r.2).Nonempty}

  have hΔ_pos : 0 < Δ := h_uniform.1

  -- If q ∈ S(k), then R_q ⊆ Q_a
  have h_nested : ∀ (k : ℕ), a ≤ k → ∀ (q : ℤ × ℤ), q ∈ S k →
      dyadicSquare (Δ ^ k) q.1 q.2 ⊆ dyadicSquare (Δ ^ a) i j := by
    intro k hak q hq
    rcases hq with ⟨x, hx1, hx2⟩
    have h_inter' : (dyadicSquare (Δ ^ k) q.1 q.2 ∩ dyadicSquare (Δ ^ a) i j).Nonempty :=
      ⟨x, hx2, hx1.2⟩
    exact @dyadicSquare_nested_containment n hn_pos Δ hΔ_int a k hak (i, j) q h_inter'

  -- S(a) = {(i,j)}
  have hS_a : S a = {(i, j)} := by
    ext ⟨q1, q2⟩
    simp only [S, Set.mem_singleton_iff]
    constructor
    · rintro ⟨x, hx1, hx2⟩
      have h_pos : 0 < Δ ^ a := pow_pos hΔ_pos a
      have h_eq1 : q1 = i := int_interval_overlap_eq q1 i (Δ ^ a) h_pos (x 0)
        hx2.1.1 hx2.1.2 hx1.2.1.1 hx1.2.1.2
      have h_eq2 : q2 = j := int_interval_overlap_eq q2 j (Δ ^ a) h_pos (x 1)
        hx2.2.1 hx2.2.2 hx1.2.2.1 hx1.2.2.2
      exact Prod.ext h_eq1 h_eq2
    · rintro ⟨rfl, rfl⟩
      rcases hQ with ⟨x, hxP, hxQ⟩
      exact ⟨x, ⟨hxP, hxQ⟩, hxQ⟩

  -- Children count from uniformity
  have h_children_count : ∀ (k : ℕ), k < m → ∀ (q : ℤ × ℤ), q ∈ S k →
      Set.encard (children k q) = ↑(N k) := by
    intro k hk q hq
    rcases hq with ⟨x, hx1, hx2⟩
    have h_nonempty : (P ∩ dyadicSquare (Δ ^ k) q.1 q.2).Nonempty :=
      ⟨x, hx1.1, hx2⟩
    have h_unif : (dyadicSquareCount (Δ ^ (k + 1)) (P ∩ dyadicSquare (Δ ^ k) q.1 q.2) : ENNReal) =
        (↑(N k) : ENNReal) := h_uniform.2.2.2.2 k hk q.1 q.2 h_nonempty
    have h1 : (Set.encard (children k q) : ENNReal) = (↑(N k) : ENNReal) := by
      simpa [dyadicSquareCount, children] using h_unif
    exact_mod_cast h1

  -- Children are finite
  have h_children_finite : ∀ (k : ℕ), k < m → ∀ (q : ℤ × ℤ), q ∈ S k →
      (children k q).Finite := by
    intro k hk q hq
    have h_encard : Set.encard (children k q) = ↑(N k) := h_children_count k hk q hq
    exact Set.finite_of_encard_eq_coe h_encard

  -- Children of different parents are disjoint
  have h_children_disjoint : ∀ (k : ℕ) (q1 q2 : ℤ × ℤ),
      q1 ≠ q2 → Disjoint (children k q1) (children k q2) := by
    intro k q1 q2 hne
    rw [Set.disjoint_left]
    intro r hr1 hr2
    have h1 : ((P ∩ dyadicSquare (Δ ^ k) q1.1 q1.2) ∩
        dyadicSquare (Δ ^ (k + 1)) r.1 r.2).Nonempty := hr1
    have h2 : ((P ∩ dyadicSquare (Δ ^ k) q2.1 q2.2) ∩
        dyadicSquare (Δ ^ (k + 1)) r.1 r.2).Nonempty := hr2
    rcases h1 with ⟨x1, hx1⟩
    rcases h2 with ⟨x2, hx2⟩
    have hx1R : x1 ∈ dyadicSquare (Δ ^ k) q1.1 q1.2 := hx1.1.2
    have hx1_fine : x1 ∈ dyadicSquare (Δ ^ (k + 1)) r.1 r.2 := hx1.2
    have hx2R : x2 ∈ dyadicSquare (Δ ^ k) q2.1 q2.2 := hx2.1.2
    have hx2_fine : x2 ∈ dyadicSquare (Δ ^ (k + 1)) r.1 r.2 := hx2.2
    let q_parent : ℤ × ℤ := (r.1 / (n : ℤ), r.2 / (n : ℤ))
    have h_contain : dyadicSquare (Δ ^ (k + 1)) r.1 r.2 ⊆
        dyadicSquare (Δ ^ k) q_parent.1 q_parent.2 :=
      dyadicSquare_child_contained_in_parent_general hn_pos hΔ_int k r
    have hx1_parent : x1 ∈ dyadicSquare (Δ ^ k) q_parent.1 q_parent.2 := h_contain hx1_fine
    have hx2_parent : x2 ∈ dyadicSquare (Δ ^ k) q_parent.1 q_parent.2 := h_contain hx2_fine
    have h_inter1 : (dyadicSquare (Δ ^ k) q_parent.1 q_parent.2 ∩
        dyadicSquare (Δ ^ k) q1.1 q1.2).Nonempty := ⟨x1, hx1_parent, hx1R⟩
    have h_eq1 : q_parent = q1 := dyadicSquare_same_level_eq (pow_pos hΔ_pos k) h_inter1
    have h_inter2 : (dyadicSquare (Δ ^ k) q_parent.1 q_parent.2 ∩
        dyadicSquare (Δ ^ k) q2.1 q2.2).Nonempty := ⟨x2, hx2_parent, hx2R⟩
    have h_eq2 : q_parent = q2 := dyadicSquare_same_level_eq (pow_pos hΔ_pos k) h_inter2
    have h_eq3 : q1 = q2 := h_eq1.symm.trans h_eq2
    exact hne h_eq3

  -- S(k+1) = disjoint union of children of S(k)
  have h_S_succ : ∀ (k : ℕ), a ≤ k → k < m →
      S (k + 1) = ⋃ q ∈ S k, children k q := by
    intro k hak hk
    apply Set.ext
    intro r
    constructor
    · -- ⊆
      intro hr
      rcases hr with ⟨x, hx_PQa, hx_fine⟩
      let q : ℤ × ℤ := (r.1 / (n : ℤ), r.2 / (n : ℤ))
      have h_contain : dyadicSquare (Δ ^ (k + 1)) r.1 r.2 ⊆
          dyadicSquare (Δ ^ k) q.1 q.2 :=
        dyadicSquare_child_contained_in_parent_general hn_pos hΔ_int k r
      have hx_Rq : x ∈ dyadicSquare (Δ ^ k) q.1 q.2 := h_contain hx_fine
      have hq_S : q ∈ S k := ⟨x, hx_PQa, hx_Rq⟩
      have hr_child : r ∈ children k q := by
        simp only [children, Set.mem_setOf_eq]
        exact ⟨x, ⟨hx_PQa.1, hx_Rq⟩, hx_fine⟩
      simp only [S, Set.mem_iUnion] at *
      exact ⟨q, hq_S, hr_child⟩
    · -- ⊇
      intro hr
      simp only [S, Set.mem_iUnion] at hr
      rcases hr with ⟨q, hq_S, hr_child⟩
      have h3 : ((P ∩ dyadicSquare (Δ ^ k) q.1 q.2) ∩
          dyadicSquare (Δ ^ (k + 1)) r.1 r.2).Nonempty := by
        simpa [children, Set.mem_setOf_eq] using hr_child
      rcases h3 with ⟨x, hx_PRq, hx_fine⟩
      have hxP : x ∈ P := hx_PRq.1
      have hxRq : x ∈ dyadicSquare (Δ ^ k) q.1 q.2 := hx_PRq.2
      have h_Rq_sub_Qa : dyadicSquare (Δ ^ k) q.1 q.2 ⊆ dyadicSquare (Δ ^ a) i j :=
        h_nested k hak q hq_S
      have hx_Qa : x ∈ dyadicSquare (Δ ^ a) i j := h_Rq_sub_Qa hxRq
      simp only [S, Set.mem_setOf_eq]
      exact ⟨x, ⟨hxP, hx_Qa⟩, hx_fine⟩

  -- Main induction on d = b - a
  have h_main : ∀ (d : ℕ), a + d ≤ m →
      (S (a + d)).Finite ∧ (S (a + d)).ncard = ∏ l ∈ Finset.Ico a (a + d), N l := by
    intro d
    induction d with
    | zero =>
      intro h_le
      have h1 : S a = {(i, j)} := hS_a
      have h_fin : (S a).Finite := by
        rw [h1]; exact Set.finite_singleton _
      have h_ncard : (S a).ncard = ∏ l ∈ Finset.Ico a (a + 0), N l := by
        rw [h1]
        simp [Finset.Ico_self]
        <;> rfl
      exact ⟨h_fin, h_ncard⟩
    | succ d ih =>
      intro h_le
      have h_ad_le_m : a + d ≤ m := by linarith
      have h_ad_lt_m : a + d < m := by linarith
      rcases ih h_ad_le_m with ⟨hS_fin, hS_ncard⟩
      let S_fin : Finset (ℤ × ℤ) := hS_fin.toFinset
      have hS_mem : ∀ q, q ∈ S_fin ↔ q ∈ S (a + d) := by
        intro q; simp [S_fin, hS_fin.mem_toFinset] <;> rfl
      let children_fin (q : ℤ × ℤ) : Finset (ℤ × ℤ) :=
        if hq : q ∈ S (a + d) then
          (h_children_finite (a + d) h_ad_lt_m q hq).toFinset
        else
          ∅
      have h_child_eq : ∀ (q : ℤ × ℤ) (hq : q ∈ S (a + d)),
          children_fin q = (h_children_finite (a + d) h_ad_lt_m q hq).toFinset := by
        intro q hq
        simp only [children_fin]
        rw [dif_pos hq]
      have h_disj : ∀ q1 ∈ S_fin, ∀ q2 ∈ S_fin, q1 ≠ q2 →
          Disjoint (children_fin q1) (children_fin q2) := by
        intro q1 hq1 q2 hq2 hne
        have hq1' : q1 ∈ S (a + d) := (hS_mem q1).mp hq1
        have hq2' : q2 ∈ S (a + d) := (hS_mem q2).mp hq2
        have h_eq1 : children_fin q1 = (h_children_finite (a + d) h_ad_lt_m q1 hq1').toFinset := h_child_eq q1 hq1'
        have h_eq2 : children_fin q2 = (h_children_finite (a + d) h_ad_lt_m q2 hq2').toFinset := h_child_eq q2 hq2'
        rw [h_eq1, h_eq2]
        exact Set.Finite.disjoint_toFinset.mpr (h_children_disjoint (a + d) q1 q2 hne)
      let union_fin : Finset (ℤ × ℤ) := S_fin.biUnion children_fin
      have h_card : union_fin.card = ∑ q ∈ S_fin, (children_fin q).card :=
        Finset.card_biUnion h_disj
      have h_union_set : (↑union_fin : Set (ℤ × ℤ)) = S (a + d + 1) := by
        ext r
        simp only [union_fin, Finset.mem_coe, Finset.mem_biUnion]
        have h_eq : S (a + d + 1) = ⋃ q ∈ S (a + d), children (a + d) q :=
          h_S_succ (a + d) (by linarith) h_ad_lt_m
        rw [h_eq]
        simp only [Set.mem_iUnion, hS_mem]
        constructor
        · rintro ⟨q, hq, hr⟩
          have hq' : q ∈ S (a + d) := hq
          have hr' : r ∈ children (a + d) q := by
            rw [h_child_eq q hq'] at hr
            simpa [children_fin, h_children_finite] using hr
          exact ⟨q, hq, hr'⟩
        · rintro ⟨q, hq, hr⟩
          have hq' : q ∈ S (a + d) := hq
          have hr' : r ∈ children_fin q := by
            rw [h_child_eq q hq']
            simpa [children_fin, h_children_finite] using hr
          exact ⟨q, hq, hr'⟩
      have h_fin_succ : (S (a + d + 1)).Finite := by
        rw [← h_union_set]; exact Finset.finite_toSet union_fin
      have h_ncard_succ : (S (a + d + 1)).ncard = union_fin.card := by
        rw [← h_union_set] <;> simp
      have h_sum : ∑ q ∈ S_fin, (children_fin q).card =
          ∑ q ∈ S_fin, N (a + d) := by
        apply Finset.sum_congr rfl
        intro q hq
        have hq' : q ∈ S (a + d) := (hS_mem q).mp hq
        have h_encard : Set.encard (children (a + d) q) = ↑(N (a + d)) :=
          h_children_count (a + d) h_ad_lt_m q hq'
        let C := (h_children_finite (a + d) h_ad_lt_m q hq').toFinset
        have hC : (C : Set (ℤ × ℤ)) = children (a + d) q := Set.Finite.coe_toFinset (h_children_finite (a + d) h_ad_lt_m q hq')
        have h_encard2 : Set.encard (children (a + d) q) = ↑C.card := by
          rw [← hC]; simp
        have h_card_eq : C.card = N (a + d) := by
          rw [h_encard2] at h_encard
          exact_mod_cast h_encard
        have h_eq2 : (children_fin q).card = N (a + d) := by
          rw [h_child_eq q hq']
          exact h_card_eq
        exact h_eq2
      have h_S_fin_card : S_fin.card = ∏ l ∈ Finset.Ico a (a + d), N l := by
        have h1 : S_fin.card = (S (a + d)).ncard := by
          exact Eq.symm (Set.ncard_eq_toFinset_card (S (a + d)) hS_fin)
        rw [h1, hS_ncard]
      have h_prod : ∏ l ∈ Finset.Ico a (a + d + 1), N l =
          (∏ l ∈ Finset.Ico a (a + d), N l) * N (a + d) := by
        have h_Ico : Finset.Ico a (a + d + 1) = Finset.Ico a (a + d) ∪ {a + d} := by
          ext x; simp [Finset.mem_Ico] <;> omega
        rw [h_Ico]
        rw [Finset.prod_union] <;> simp [Finset.mem_Ico] <;> omega
      have h_goal : (S (a + (d + 1))).ncard = ∏ l ∈ Finset.Ico a (a + (d + 1)), N l := by
        have h_eq5 : a + (d + 1) = a + d + 1 := by ring
        rw [h_eq5]
        rw [h_ncard_succ, h_card, h_sum, Finset.sum_const, h_S_fin_card, h_prod] <;> ring
      exact ⟨h_fin_succ, h_goal⟩

  have h_final := h_main (b - a) (by omega)
  have h_eq : a + (b - a) = b := by omega
  rw [h_eq] at h_final
  have h_fin_b : (S b).Finite := h_final.1
  have h_encard : Set.encard (S b) = ↑(∏ k ∈ Finset.Ico a b, N k) := by
    have h1 : (S b).ncard = ∏ k ∈ Finset.Ico a b, N k := h_final.2
    have h2 : Set.encard (S b) = ↑((S b).ncard) := by
      let C := h_fin_b.toFinset
      have hC : (C : Set (ℤ × ℤ)) = S b := Set.Finite.coe_toFinset h_fin_b
      rw [← hC]
      simp
    rw [h2, h1]
  simpa [dyadicSquareCount, S] using h_encard

end DirecretisedFurstenbergEstimate.MultiscaleDecomposition

end
