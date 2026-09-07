import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.PlanarGridPartitionTreeStatement
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Int.Interval
import Mathlib.Tactic

/-!
WZ2 Section 7: prove that the planar floor grids form a nested atomic
partition tree with a uniform local child bound.

At level `k`, points are grouped by the integer pair
`(floor (x * base^k), floor (y * base^k))`. The partitions are nested,
each parent has at most `(base + 1)^2` children, and at a sufficiently
fine terminal mesh, separation makes every terminal cell a singleton.
-/

namespace Kakeya.Assouad

-- =====================================================================
-- Distance and terminal singleton helpers
-- =====================================================================

/-- If two real numbers have the same floor after scaling by `M > 0`,
their difference is strictly less than `1 / M`. -/
private lemma same_floor_abs_sub_lt_one_div
    {M x y : ℝ} (hM : 0 < M)
    (h : ⌊x * M⌋ = ⌊y * M⌋) :
    |x - y| < 1 / M := by
  have h1 : |x * M - y * M| < 1 :=
    Int.abs_sub_lt_one_of_floor_eq_floor h
  have h2 : |x * M - y * M| = |x - y| * M := by
    have h3 : x * M - y * M = (x - y) * M := by ring
    rw [h3]
    rw [abs_mul, abs_of_pos hM]
  rw [h2] at h1
  have h4 : |x - y| * M < 1 := h1
  have h5 : |x - y| < 1 / M := by
    calc |x - y|
      = (|x - y| * M) / M := by field_simp [hM.ne']
    _ < 1 / M := by gcongr
  exact h5

/-- In `EuclideanSpace ℝ (Fin 2)`, if each coordinate difference has
absolute value strictly less than `a > 0`, then the Euclidean distance
is strictly less than `2 * a`. -/
private lemma point2_dist_lt_two_mul
    {p q : Point2} {a : ℝ} (ha : 0 < a)
    (h0 : |p 0 - q 0| < a)
    (h1 : |p 1 - q 1| < a) :
    dist p q < 2 * a := by
  let v := p - q
  have hnorm : dist p q = ‖v‖ := by
    simp [v, dist_eq_norm]
  rw [hnorm]
  have hsq : ‖v‖ ^ 2 = (v 0) ^ 2 + (v 1) ^ 2 := by
    have h := EuclideanSpace.real_norm_sq_eq v
    simpa [Fin.sum_univ_two] using h
  have h0' : (v 0) ^ 2 < a ^ 2 := by
    have h : |v 0| < a := by simpa [v] using h0
    have h' : (v 0) ^ 2 = |v 0| ^ 2 := by rw [sq_abs]
    rw [h']
    gcongr
  have h1' : (v 1) ^ 2 < a ^ 2 := by
    have h : |v 1| < a := by simpa [v] using h1
    have h' : (v 1) ^ 2 = |v 1| ^ 2 := by rw [sq_abs]
    rw [h']
    gcongr
  have h2 : ‖v‖ ^ 2 < (2 * a) ^ 2 := by
    rw [hsq]
    have h3 : (v 0) ^ 2 + (v 1) ^ 2 < 2 * a ^ 2 := by linarith
    have h4 : 2 * a ^ 2 < (2 * a) ^ 2 := by
      have h5 : 0 < a := ha
      nlinarith
    linarith
  have h6 : 0 ≤ ‖v‖ := by positivity
  have h7 : 0 < 2 * a := by positivity
  nlinarith

/-- If two points of a `fineScale`-separated set share the same
`planarGridIndex` at the terminal level, and `2 < fineScale * base^levels`,
then the points are equal. -/
private lemma terminal_singleton_of_separation
    {A : DiscreteSet 2} {base levels : ℕ}
    (hbase : 2 ≤ base)
    {fineScale : ℝ} (hfine_pos : 0 < fineScale)
    (hA_sep : A.IsDeltaSeparated fineScale)
    (hmesh : 2 < fineScale * (base ^ levels : ℝ))
    {p q : Point2} (hp : p ∈ A) (hq : q ∈ A)
    (hidx : planarGridIndex base levels p = planarGridIndex base levels q) :
    p = q := by
  set M : ℝ := (base ^ levels : ℝ) with hM_def
  have hM_pos : 0 < M := by positivity
  have hfloor0 : ⌊p 0 * M⌋ = ⌊q 0 * M⌋ := by
    simpa [planarGridIndex, hM_def] using congr_arg Prod.fst hidx
  have hfloor1 : ⌊p 1 * M⌋ = ⌊q 1 * M⌋ := by
    simpa [planarGridIndex, hM_def] using congr_arg Prod.snd hidx
  have h0 : |p 0 - q 0| < 1 / M :=
    same_floor_abs_sub_lt_one_div hM_pos hfloor0
  have h1 : |p 1 - q 1| < 1 / M :=
    same_floor_abs_sub_lt_one_div hM_pos hfloor1
  have hdist : dist p q < 2 * (1 / M) :=
    point2_dist_lt_two_mul (by positivity) h0 h1
  have h9 : 2 * (1 / M) < fineScale := by
    have h10 : 2 / M < fineScale := by
      calc 2 / M
        < (fineScale * M) / M := by gcongr
        _ = fineScale := by field_simp [hM_pos.ne']
    have h_eq : 2 * (1 / M) = 2 / M := by ring
    rw [h_eq]
    exact h10
  have h12 : dist p q < fineScale := by
    calc dist p q < 2 * (1 / M) := hdist
         _ < fineScale := h9
  by_cases hne : p ≠ q
  · have h13 : fineScale ≤ dist p q := hA_sep hp hq hne
    linarith
  · have h_eq : p = q := by tauto
    exact h_eq

-- =====================================================================
-- Partition property helpers
-- =====================================================================

/-- Every cell in the planar grid partition is nonempty and a subset of `A`. -/
private lemma planarGridPartition_cell_nonempty_subset
    {base level : ℕ} {A : DiscreteSet 2}
    {cell : DiscreteSet 2}
    (hcell : cell ∈ planarGridPartition base level A) :
    cell.Nonempty ∧ cell ⊆ A := by
  rcases Finset.mem_image.mp hcell with ⟨p, hp, rfl⟩
  have hsub : planarGridCell base level A p ⊆ A :=
    Finset.filter_subset _ _
  have hmem : p ∈ planarGridCell base level A p := by
    simp [planarGridCell, hp]
  exact ⟨⟨p, hmem⟩, hsub⟩

/-- Distinct cells in the planar grid partition are disjoint. -/
private lemma planarGridPartition_disjoint
    {base level : ℕ} {A : DiscreteSet 2}
    {cell₁ cell₂ : DiscreteSet 2}
    (h₁ : cell₁ ∈ planarGridPartition base level A)
    (h₂ : cell₂ ∈ planarGridPartition base level A)
    (hne : cell₁ ≠ cell₂) :
    Disjoint cell₁ cell₂ := by
  rcases Finset.mem_image.mp h₁ with ⟨p₁, hp₁, rfl⟩
  rcases Finset.mem_image.mp h₂ with ⟨p₂, hp₂, rfl⟩
  by_contra h
  rw [Finset.not_disjoint_iff] at h
  rcases h with ⟨x, hx₁, hx₂⟩
  have hx₁' : planarGridIndex base level x = planarGridIndex base level p₁ := by
    have h := (Finset.mem_filter.mp hx₁).2
    exact h
  have hx₂' : planarGridIndex base level x = planarGridIndex base level p₂ := by
    have h := (Finset.mem_filter.mp hx₂).2
    exact h
  have h_eq_idx : planarGridIndex base level p₁ = planarGridIndex base level p₂ := by
    rw [←hx₁', hx₂']
  have h_eq_cell : planarGridCell base level A p₁ = planarGridCell base level A p₂ := by
    simp only [planarGridCell, h_eq_idx]
  exact hne h_eq_cell

/-- The planar grid partition covers all of `A`. -/
private lemma planarGridPartition_cover
    {base level : ℕ} {A : DiscreteSet 2} :
    A ⊆ Finset.biUnion (planarGridPartition base level A) id := by
  intro p hp
  have h1 : planarGridCell base level A p ∈ planarGridPartition base level A := by
    apply Finset.mem_image.mpr
    exact ⟨p, hp, rfl⟩
  have h2 : p ∈ planarGridCell base level A p := by
    simp [planarGridCell, hp]
  exact Finset.mem_biUnion.mpr ⟨planarGridCell base level A p, h1, h2⟩

-- =====================================================================
-- Nesting helper
-- =====================================================================

/-- Every child cell at level `level + 1` is contained in a parent cell
at level `level`. -/
private lemma planarGridPartition_nesting
    {base level : ℕ} {A : DiscreteSet 2}
    (hbase : 1 ≤ base)
    {child : DiscreteSet 2}
    (hchild : child ∈ planarGridPartition base (level + 1) A) :
    ∃ parent ∈ planarGridPartition base level A, child ⊆ parent := by
  rcases Finset.mem_image.mp hchild with ⟨p, hp, rfl⟩
  let child := planarGridCell base (level + 1) A p
  let parent := planarGridCell base level A p
  have hparent_in : parent ∈ planarGridPartition base level A := by
    apply Finset.mem_image.mpr
    exact ⟨p, hp, rfl⟩
  have hbase_ne : base ≠ 0 := by omega
  have h_main : child ⊆ parent := by
    intro q hq
    have hqA : q ∈ A := (Finset.mem_filter.mp hq).1
    have h_idx : planarGridIndex base (level + 1) q = planarGridIndex base (level + 1) p :=
      (Finset.mem_filter.mp hq).2
    have h0 : ⌊q 0 * (base ^ (level + 1) : ℝ)⌋ = ⌊p 0 * (base ^ (level + 1) : ℝ)⌋ :=
      congr_arg Prod.fst h_idx
    have h1 : ⌊q 1 * (base ^ (level + 1) : ℝ)⌋ = ⌊p 1 * (base ^ (level + 1) : ℝ)⌋ :=
      congr_arg Prod.snd h_idx
    have h_floor0 : ⌊q 0 * (base ^ level : ℝ)⌋ = ⌊p 0 * (base ^ level : ℝ)⌋ := by
      have hq0 : ⌊q 0 * (base ^ (level + 1) : ℝ)⌋ / (base : ℤ) = ⌊q 0 * (base ^ level : ℝ)⌋ := by
        have h : (q 0 * (base ^ (level + 1) : ℝ)) = (q 0 * (base ^ level : ℝ)) * (base : ℝ) := by
          simp [pow_succ]; ring
        rw [h]
        exact Int.mul_natCast_floor_div_cancel hbase_ne (q 0 * (base ^ level : ℝ))
      have hp0 : ⌊p 0 * (base ^ (level + 1) : ℝ)⌋ / (base : ℤ) = ⌊p 0 * (base ^ level : ℝ)⌋ := by
        have h : (p 0 * (base ^ (level + 1) : ℝ)) = (p 0 * (base ^ level : ℝ)) * (base : ℝ) := by
          simp [pow_succ]; ring
        rw [h]
        exact Int.mul_natCast_floor_div_cancel hbase_ne (p 0 * (base ^ level : ℝ))
      rw [←hq0, ←hp0, h0]
    have h_floor1 : ⌊q 1 * (base ^ level : ℝ)⌋ = ⌊p 1 * (base ^ level : ℝ)⌋ := by
      have hq1 : ⌊q 1 * (base ^ (level + 1) : ℝ)⌋ / (base : ℤ) = ⌊q 1 * (base ^ level : ℝ)⌋ := by
        have h : (q 1 * (base ^ (level + 1) : ℝ)) = (q 1 * (base ^ level : ℝ)) * (base : ℝ) := by
          simp [pow_succ]; ring
        rw [h]
        exact Int.mul_natCast_floor_div_cancel hbase_ne (q 1 * (base ^ level : ℝ))
      have hp1 : ⌊p 1 * (base ^ (level + 1) : ℝ)⌋ / (base : ℤ) = ⌊p 1 * (base ^ level : ℝ)⌋ := by
        have h : (p 1 * (base ^ (level + 1) : ℝ)) = (p 1 * (base ^ level : ℝ)) * (base : ℝ) := by
          simp [pow_succ]; ring
        rw [h]
        exact Int.mul_natCast_floor_div_cancel hbase_ne (p 1 * (base ^ level : ℝ))
      rw [←hq1, ←hp1, h1]
    have h_idx' : planarGridIndex base level q = planarGridIndex base level p := by
      simp [planarGridIndex, h_floor0, h_floor1]
    have hq_in_parent : q ∈ parent := by
      simp only [parent, planarGridCell, Finset.mem_filter]
      exact ⟨hqA, h_idx'⟩
    exact hq_in_parent
  exact ⟨parent, hparent_in, h_main⟩

-- =====================================================================
-- Child index helpers
-- =====================================================================

/-- Every occupied grid cell has a well-defined index: all points in the
cell share the same `planarGridIndex`. -/
private lemma planarGridCell_has_index
    {base level : ℕ} {A : DiscreteSet 2}
    {cell : DiscreteSet 2}
    (hcell : cell ∈ planarGridPartition base level A) :
    ∃ (idx : ℤ × ℤ), ∀ p ∈ cell, planarGridIndex base level p = idx := by
  rcases Finset.mem_image.mp hcell with ⟨p, _hp, rfl⟩
  let idx := planarGridIndex base level p
  refine ⟨idx, fun q hq => ?_⟩
  have h : planarGridIndex base level q = planarGridIndex base level p :=
    (Finset.mem_filter.mp hq).2
  exact h

/-- Two occupied cells that share an index are equal.  The cell-to-index
map is injective on `planarGridPartition`. -/
private lemma planarGridCell_index_injective
    {base level : ℕ} {A : DiscreteSet 2}
    {cell₁ cell₂ : DiscreteSet 2}
    (h₁ : cell₁ ∈ planarGridPartition base level A)
    (h₂ : cell₂ ∈ planarGridPartition base level A)
    {p₁ : Point2} (hp₁ : p₁ ∈ cell₁)
    {p₂ : Point2} (hp₂ : p₂ ∈ cell₂)
    (h_eq : planarGridIndex base level p₁ = planarGridIndex base level p₂) :
    cell₁ = cell₂ := by
  rcases Finset.mem_image.mp h₁ with ⟨r₁, _hr₁, rfl⟩
  rcases Finset.mem_image.mp h₂ with ⟨r₂, _hr₂, rfl⟩
  have h1 : planarGridIndex base level p₁ = planarGridIndex base level r₁ :=
    (Finset.mem_filter.mp hp₁).2
  have h2 : planarGridIndex base level p₂ = planarGridIndex base level r₂ :=
    (Finset.mem_filter.mp hp₂).2
  have h3 : planarGridIndex base level r₁ = planarGridIndex base level r₂ := by
    rw [←h1, h_eq, h2]
  simp only [planarGridCell, h3]

/-- Integer division of a level-(level+1) floor coordinate by `base`
recovers the level-`level` floor coordinate. -/
private lemma floor_child_div_base_eq_floor_parent
    {base level : ℕ} (hbase : 1 ≤ base)
    (x : ℝ) :
    ⌊x * (base ^ (level + 1) : ℝ)⌋ / (base : ℤ) =
    ⌊x * (base ^ level : ℝ)⌋ := by
  have hbase_ne : base ≠ 0 := by omega
  have h : (x * (base ^ (level + 1) : ℝ)) = (x * (base ^ level : ℝ)) * (base : ℝ) := by
    simp [pow_succ]; ring
  rw [h]
  exact Int.mul_natCast_floor_div_cancel hbase_ne (x * (base ^ level : ℝ))

-- =====================================================================
-- Child bound helpers
-- =====================================================================

/-- If `m / b = i` and `b > 0`, then `i * b ≤ m < (i + 1) * b`. -/
private lemma ediv_eq_bounds (base : ℕ) (hbase : 0 < base) (m i : ℤ)
    (hdiv : m / (base : ℤ) = i) :
    i * (base : ℤ) ≤ m ∧ m < (i + 1) * (base : ℤ) := by
  have hb_pos : (0 : ℤ) < (base : ℤ) := Int.natCast_pos.mpr hbase
  have hb_ne : (base : ℤ) ≠ 0 := hb_pos.ne'
  have h1 : m = i * (base : ℤ) + m % (base : ℤ) := by
    have h_ediv : m / (base : ℤ) * (base : ℤ) + m % (base : ℤ) = m :=
      Int.ediv_mul_add_emod m (base : ℤ)
    calc
      m = m / (base : ℤ) * (base : ℤ) + m % (base : ℤ) := h_ediv.symm
      _ = i * (base : ℤ) + m % (base : ℤ) := by rw [hdiv]
  have h2 : 0 ≤ m % (base : ℤ) := Int.emod_nonneg m hb_ne
  have h3 : m % (base : ℤ) < (base : ℤ) := Int.emod_lt_of_pos m hb_pos
  constructor <;> linarith

/-- For any finite set of integer pairs all mapping to the same parent index
    under division by `base`, the cardinality is at most `base^2`. -/
private lemma child_bound_general
    (base : ℕ) (hbase : 0 < base) (i j : ℤ)
    (S : Finset (ℤ × ℤ))
    (h : ∀ p ∈ S, p.1 / (base : ℤ) = i ∧ p.2 / (base : ℤ) = j) :
    S.card ≤ base ^ 2 := by
  have hb_pos : (0 : ℤ) < (base : ℤ) := Int.natCast_pos.mpr hbase
  let sI : Finset ℤ := Finset.Icc (i * (base : ℤ)) ((i + 1) * (base : ℤ) - 1)
  let sJ : Finset ℤ := Finset.Icc (j * (base : ℤ)) ((j + 1) * (base : ℤ) - 1)
  have h_sub : S ⊆ Finset.product sI sJ := by
    intro p hp
    have hpi := (h p hp).1
    have hpj := (h p hp).2
    have h1 := ediv_eq_bounds base hbase p.1 i hpi
    have h2 := ediv_eq_bounds base hbase p.2 j hpj
    have h1' : p.1 ∈ sI := by
      simp only [sI, Finset.mem_Icc]; omega
    have h2' : p.2 ∈ sJ := by
      simp only [sJ, Finset.mem_Icc]; omega
    exact Finset.mem_product.mpr ⟨h1', h2'⟩
  have h_card : S.card ≤ (Finset.product sI sJ).card := Finset.card_le_card h_sub
  have h_prod : (Finset.product sI sJ).card = sI.card * sJ.card :=
    Finset.card_product sI sJ
  have h_leI : i * (base : ℤ) ≤ ((i + 1) * (base : ℤ) - 1) + 1 := by ring_nf; linarith
  have hI : (sI.card : ℤ) = (base : ℤ) := by
    have h := Int.card_Icc_of_le (i * (base : ℤ)) ((i + 1) * (base : ℤ) - 1) h_leI
    have h' : (sI.card : ℤ) = (i + 1) * (base : ℤ) - 1 + 1 - i * (base : ℤ) := by
      simpa [sI] using h
    linarith
  have h_leJ : j * (base : ℤ) ≤ ((j + 1) * (base : ℤ) - 1) + 1 := by ring_nf; linarith
  have hJ : (sJ.card : ℤ) = (base : ℤ) := by
    have h := Int.card_Icc_of_le (j * (base : ℤ)) ((j + 1) * (base : ℤ) - 1) h_leJ
    have h' : (sJ.card : ℤ) = (j + 1) * (base : ℤ) - 1 + 1 - j * (base : ℤ) := by
      simpa [sJ] using h
    linarith
  have hI' : sI.card = base := by exact_mod_cast hI
  have hJ' : sJ.card = base := by exact_mod_cast hJ
  rw [h_prod, hI', hJ'] at h_card
  simpa [pow_two] using h_card

-- =====================================================================
-- Main theorem
-- =====================================================================

theorem planar_grid_partition_tree :
    PlanarGridPartitionTreeStatement := by
  intro A _hA_nonempty base levels hbase fineScale hfine_pos hA_sep hmesh
  dsimp only
  let P : ℕ → Finset (Finset Point2) := fun level => planarGridPartition base level A
  constructor
  · -- Partition properties for all level ≤ levels
    intro level _hle
    constructor
    · -- cells nonempty and subset of A
      intro cell hcell
      exact planarGridPartition_cell_nonempty_subset hcell
    constructor
    · -- distinct cells disjoint
      intro cell₁ h₁ cell₂ h₂ hne
      exact planarGridPartition_disjoint h₁ h₂ hne
    · -- coverage
      exact planarGridPartition_cover
  · constructor
    · -- terminal cells singleton
      intro cell hcell
      rcases Finset.mem_image.mp hcell with ⟨p, hpA, rfl⟩
      let cell := planarGridCell base levels A p
      have hsub : cell ⊆ A := Finset.filter_subset _ _
      have hp_in : p ∈ cell := by
        apply Finset.mem_filter.mpr
        exact ⟨hpA, by trivial⟩
      have h1 : ∀ q ∈ cell, q = p := by
        intro q hq
        have hqpA : q ∈ A := hsub hq
        have h_idx : planarGridIndex base levels q = planarGridIndex base levels p :=
          (Finset.mem_filter.mp hq).2
        exact terminal_singleton_of_separation hbase hfine_pos hA_sep hmesh hqpA hpA h_idx
      have h_card : cell = {p} := by
        apply Finset.eq_singleton_iff_unique_mem.mpr
        constructor
        · exact hp_in
        · intro x hx
          exact h1 x hx
      have h_goal : Finset.card cell = 1 := by
        rw [h_card]
        simp
      exact h_goal
    · constructor
      · -- nesting
        intro level _hlt child hchild
        exact planarGridPartition_nesting (by linarith) hchild
      · -- child bound
        intro level _hlt parent _hparent
        have hbase_pos : 0 < base := by linarith
        let children := partitionChildren P level parent
        have hparent_nonempty : parent.Nonempty :=
          (planarGridPartition_cell_nonempty_subset _hparent).1
        rcases hparent_nonempty with ⟨p_parent, hp_parent⟩
        let m0 : ℤ := ⌊p_parent 0 * (base ^ level : ℝ)⌋
        let m1 : ℤ := ⌊p_parent 1 * (base ^ level : ℝ)⌋
        have hparent_idx : ∀ x ∈ parent, planarGridIndex base level x = (m0, m1) := by
          rcases planarGridCell_has_index _hparent with ⟨idx, hidx⟩
          have h_eq : idx = (m0, m1) := by
            have h : planarGridIndex base level p_parent = idx := hidx p_parent hp_parent
            have h' : planarGridIndex base level p_parent = (m0, m1) := by
              simp [planarGridIndex, m0, m1]
            rw [h] at h'
            exact h'
          intro x hx
          have h1 : planarGridIndex base level x = idx := hidx x hx
          rw [h1, h_eq]
        let f : DiscreteSet 2 → Point2 := fun child =>
          if h : child.Nonempty then Classical.choose h else p_parent
        have hchild_in_P : ∀ child ∈ children, child ∈ P (level + 1) := by
          intro child hchild
          exact (Finset.mem_filter.mp hchild).1
        have hchild_nonempty : ∀ child ∈ children, child.Nonempty := by
          intro child hchild
          exact (planarGridPartition_cell_nonempty_subset (hchild_in_P child hchild)).1
        have hchild_sub_parent : ∀ child ∈ children, child ⊆ parent := by
          intro child hchild
          exact (Finset.mem_filter.mp hchild).2
        have hf_mem : ∀ child ∈ children, f child ∈ child := by
          intro child hchild
          have hne : child.Nonempty := hchild_nonempty child hchild
          have h_eq : f child = Classical.choose hne := by
            simp [f, hne]
          rw [h_eq]
          exact Classical.choose_spec hne
        let g : DiscreteSet 2 → ℤ × ℤ := fun child =>
          planarGridIndex base (level + 1) (f child)
        let S := children.image g
        have h_inj : Set.InjOn g children := by
          intro child1 hc1 child2 hc2 h_eq
          have h1 : f child1 ∈ child1 := hf_mem child1 hc1
          have h2 : f child2 ∈ child2 := hf_mem child2 hc2
          exact planarGridCell_index_injective
            (hchild_in_P child1 hc1) (hchild_in_P child2 hc2) h1 h2 h_eq
        have h_card_eq : S.card = children.card := by
          rw [Finset.card_image_of_injOn h_inj]
        have hS_prop : ∀ idx ∈ S,
            idx.1 / (base : ℤ) = m0 ∧ idx.2 / (base : ℤ) = m1 := by
          intro idx hidx
          rcases Finset.mem_image.mp hidx with ⟨child, hchild, rfl⟩
          have h_f_in_parent : f child ∈ parent :=
            hchild_sub_parent child hchild (hf_mem child hchild)
          have h_level_idx : planarGridIndex base level (f child) = (m0, m1) :=
            hparent_idx (f child) h_f_in_parent
          have h0 : ⌊(f child) 0 * (base ^ (level + 1) : ℝ)⌋ / (base : ℤ) =
              ⌊(f child) 0 * (base ^ level : ℝ)⌋ :=
            floor_child_div_base_eq_floor_parent (by linarith) ((f child) 0)
          have h1 : ⌊(f child) 1 * (base ^ (level + 1) : ℝ)⌋ / (base : ℤ) =
              ⌊(f child) 1 * (base ^ level : ℝ)⌋ :=
            floor_child_div_base_eq_floor_parent (by linarith) ((f child) 1)
          have h_floor0 : ⌊(f child) 0 * (base ^ level : ℝ)⌋ = m0 := by
            simpa [planarGridIndex, m0] using congr_arg Prod.fst h_level_idx
          have h_floor1 : ⌊(f child) 1 * (base ^ level : ℝ)⌋ = m1 := by
            simpa [planarGridIndex, m1] using congr_arg Prod.snd h_level_idx
          constructor
          · have hg1 : (g child).1 = ⌊(f child) 0 * (base ^ (level + 1) : ℝ)⌋ := by
              simp [g, planarGridIndex]
            rw [hg1, h0, h_floor0]
          · have hg2 : (g child).2 = ⌊(f child) 1 * (base ^ (level + 1) : ℝ)⌋ := by
              simp [g, planarGridIndex]
            rw [hg2, h1, h_floor1]
        have h_bound : S.card ≤ base ^ 2 :=
          child_bound_general base hbase_pos m0 m1 S hS_prop
        have h_final : children.card ≤ (base + 1) ^ 2 := by
          rw [←h_card_eq]
          have h : base ^ 2 ≤ (base + 1) ^ 2 := by gcongr; linarith
          exact h_bound.trans h
        exact h_final

end Kakeya.Assouad
