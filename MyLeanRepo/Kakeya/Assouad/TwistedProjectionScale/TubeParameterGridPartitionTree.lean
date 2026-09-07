import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.OSBranchingUniformRefinementStatement
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.TubeParameterGridPartitionTreeStatement
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Int.Interval
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# 4D tube-parameter floor-grid partition tree

At level `k`, four-dimensional parameter points are grouped by the integer
4-tuple `(floor (x₀ * base^k), ..., floor (x₃ * base^k))`.

The partitions are nested, each parent has at most `(base + 1)^4` children,
and at a sufficiently fine terminal mesh, separation makes every terminal
cell a singleton.

This is the four-dimensional analogue of `cubic_grid_partition_tree`.
-/

noncomputable section

namespace Kakeya.Assouad

-- =====================================================================
-- Distance and separation lemmas
-- =====================================================================

lemma same_floor_abs_sub_lt_one_div
    {M x y : ℝ} (hM : 0 < M)
    (h : ⌊x * M⌋ = ⌊y * M⌋) :
    |x - y| < 1 / M := by
  have h1 : |x * M - y * M| < 1 :=
    Int.abs_sub_lt_one_of_floor_eq_floor h
  have h2 : |x * M - y * M| = |x - y| * M := by
    have h3 : x * M - y * M = (x - y) * M := by ring
    rw [h3, abs_mul, abs_of_pos hM]
  rw [h2] at h1
  calc
    |x - y| = (|x - y| * M) / M := by field_simp [hM.ne']
    _ < 1 / M := by gcongr

private lemma point4_dist_lt_four_mul
    {p q : Point 4} {a : ℝ} (ha : 0 < a)
    (h0 : |p 0 - q 0| < a)
    (h1 : |p 1 - q 1| < a)
    (h2 : |p 2 - q 2| < a)
    (h3 : |p 3 - q 3| < a) :
    dist p q < 4 * a := by
  let v := p - q
  have hnorm : dist p q = ‖v‖ := by simp [v, dist_eq_norm]
  rw [hnorm]
  have hsq : ‖v‖ ^ 2 = (v 0) ^ 2 + (v 1) ^ 2 + (v 2) ^ 2 + (v 3) ^ 2 := by
    have h := EuclideanSpace.real_norm_sq_eq v
    simpa [Fin.sum_univ_four] using h
  have h0' : (v 0) ^ 2 < a ^ 2 := by
    have h : |v 0| < a := by simpa [v] using h0
    rw [show (v 0) ^ 2 = |v 0| ^ 2 by rw [sq_abs]]
    gcongr
  have h1' : (v 1) ^ 2 < a ^ 2 := by
    have h : |v 1| < a := by simpa [v] using h1
    rw [show (v 1) ^ 2 = |v 1| ^ 2 by rw [sq_abs]]
    gcongr
  have h2' : (v 2) ^ 2 < a ^ 2 := by
    have h : |v 2| < a := by simpa [v] using h2
    rw [show (v 2) ^ 2 = |v 2| ^ 2 by rw [sq_abs]]
    gcongr
  have h3' : (v 3) ^ 2 < a ^ 2 := by
    have h : |v 3| < a := by simpa [v] using h3
    rw [show (v 3) ^ 2 = |v 3| ^ 2 by rw [sq_abs]]
    gcongr
  have h4 : ‖v‖ ^ 2 < (4 * a) ^ 2 := by
    rw [hsq]
    nlinarith
  nlinarith [norm_nonneg v]

private lemma terminal_singleton_of_separation4
    {A : DiscreteSet 4} {base levels : ℕ}
    (hbase : 2 ≤ base)
    {fineScale : ℝ} (hfine_pos : 0 < fineScale)
    (hA_sep : A.IsDeltaSeparated fineScale)
    (hmesh : 4 < fineScale * (base ^ levels : ℝ))
    {p q : Point 4} (hp : p ∈ A) (hq : q ∈ A)
    (hidx : tubeParameterGridIndex base levels p =
      tubeParameterGridIndex base levels q) :
    p = q := by
  have hM_pos : 0 < (base ^ levels : ℝ) := by positivity
  have hcoord : ∀ i : Fin 4, |p i - q i| < 1 / (base ^ levels : ℝ) := by
    intro i
    exact same_floor_abs_sub_lt_one_div hM_pos (congrFun hidx i)
  have hdist :
      dist p q < 4 * (1 / (base ^ levels : ℝ)) :=
    point4_dist_lt_four_mul (by positivity)
      (hcoord 0) (hcoord 1) (hcoord 2) (hcoord 3)
  have hsmall : 4 * (1 / (base ^ levels : ℝ)) < fineScale := by
    have hpow_pos : 0 < (base ^ levels : ℝ) := by positivity
    calc
      4 * (1 / (base ^ levels : ℝ))
          = 4 / (base ^ levels : ℝ) := by ring
      _ < fineScale := (div_lt_iff₀ hpow_pos).2 (by simpa [mul_comm] using hmesh)
  have h12 : dist p q < fineScale := hdist.trans hsmall
  by_cases hne : p ≠ q
  · have h13 : fineScale ≤ dist p q := hA_sep hp hq hne
    linarith
  · exact not_ne_iff.mp hne

-- =====================================================================
-- Cell properties: nonempty, subset, disjoint, cover
-- =====================================================================

lemma tubeParameterGridPartition_cell_nonempty_subset
    {base level : ℕ} {A : DiscreteSet 4}
    {cell : DiscreteSet 4}
    (hcell : cell ∈ tubeParameterGridPartition base level A) :
    cell.Nonempty ∧ cell ⊆ A := by
  rcases Finset.mem_image.mp hcell with ⟨p, hp, rfl⟩
  exact ⟨⟨p, by simp [tubeParameterGridCell, hp]⟩, Finset.filter_subset _ _⟩

lemma tubeParameterGridPartition_disjoint
    {base level : ℕ} {A : DiscreteSet 4}
    {cell₁ cell₂ : DiscreteSet 4}
    (h₁ : cell₁ ∈ tubeParameterGridPartition base level A)
    (h₂ : cell₂ ∈ tubeParameterGridPartition base level A)
    (hne : cell₁ ≠ cell₂) :
    Disjoint cell₁ cell₂ := by
  rcases Finset.mem_image.mp h₁ with ⟨p₁, hp₁, rfl⟩
  rcases Finset.mem_image.mp h₂ with ⟨p₂, hp₂, rfl⟩
  by_contra h
  rw [Finset.not_disjoint_iff] at h
  rcases h with ⟨x, hx₁, hx₂⟩
  have hx₁' := (Finset.mem_filter.mp hx₁).2
  have hx₂' := (Finset.mem_filter.mp hx₂).2
  have h_eq_idx :
      tubeParameterGridIndex base level p₁ =
      tubeParameterGridIndex base level p₂ := by
    rw [← hx₁', hx₂']
  exact hne (by simp only [tubeParameterGridCell, h_eq_idx])

lemma tubeParameterGridPartition_cover
    {base level : ℕ} {A : DiscreteSet 4} :
    A ⊆ Finset.biUnion (tubeParameterGridPartition base level A) id := by
  intro p hp
  exact Finset.mem_biUnion.mpr
    ⟨tubeParameterGridCell base level A p,
      Finset.mem_image.mpr ⟨p, hp, rfl⟩,
      by simp [tubeParameterGridCell, hp]⟩

-- =====================================================================
-- Nesting: level k+1 cells lie in level k parents
-- =====================================================================

lemma floor_child_div_base_eq_floor_parent4
    {base level : ℕ} (hbase : 1 ≤ base) (x : ℝ) :
    ⌊x * (base ^ (level + 1) : ℝ)⌋ / (base : ℤ) =
      ⌊x * (base ^ level : ℝ)⌋ := by
  have hbase_ne : base ≠ 0 := by omega
  rw [show x * (base ^ (level + 1) : ℝ) =
    (x * (base ^ level : ℝ)) * (base : ℝ) by simp [pow_succ]; ring]
  exact Int.mul_natCast_floor_div_cancel hbase_ne
    (x * (base ^ level : ℝ))

lemma tubeParameterGridPartition_nesting
    {base level : ℕ} {A : DiscreteSet 4}
    (hbase : 1 ≤ base)
    {child : DiscreteSet 4}
    (hchild : child ∈ tubeParameterGridPartition base (level + 1) A) :
    ∃ parent ∈ tubeParameterGridPartition base level A, child ⊆ parent := by
  rcases Finset.mem_image.mp hchild with ⟨p, hp, rfl⟩
  let parent := tubeParameterGridCell base level A p
  refine ⟨parent, Finset.mem_image.mpr ⟨p, hp, rfl⟩, ?_⟩
  intro q hq
  have hqA : q ∈ A := (Finset.mem_filter.mp hq).1
  have h_idx := (Finset.mem_filter.mp hq).2
  have h_floor : ∀ i : Fin 4,
      ⌊q i * (base ^ level : ℝ)⌋ =
        ⌊p i * (base ^ level : ℝ)⌋ := by
    intro i
    have hq_i :
        ⌊q i * (base ^ (level + 1) : ℝ)⌋ =
          ⌊p i * (base ^ (level + 1) : ℝ)⌋ :=
      congrFun h_idx i
    have hq_div :
        ⌊q i * (base ^ (level + 1) : ℝ)⌋ / (base : ℤ) =
          ⌊q i * (base ^ level : ℝ)⌋ :=
      floor_child_div_base_eq_floor_parent4 hbase (q i)
    have hp_div :
        ⌊p i * (base ^ (level + 1) : ℝ)⌋ / (base : ℤ) =
          ⌊p i * (base ^ level : ℝ)⌋ :=
      floor_child_div_base_eq_floor_parent4 hbase (p i)
    rw [← hq_div, ← hp_div, hq_i]
  exact Finset.mem_filter.mpr
    ⟨hqA, funext fun i => h_floor i⟩

-- =====================================================================
-- Child bound: at most base^4 children per parent
-- =====================================================================

private lemma tubeParameterGridCell_has_index
    {base level : ℕ} {A : DiscreteSet 4}
    {cell : DiscreteSet 4}
    (hcell : cell ∈ tubeParameterGridPartition base level A) :
    ∃ idx : Fin 4 → ℤ, ∀ p ∈ cell, tubeParameterGridIndex base level p = idx := by
  rcases Finset.mem_image.mp hcell with ⟨p, _hp, rfl⟩
  exact ⟨tubeParameterGridIndex base level p,
    fun q hq => (Finset.mem_filter.mp hq).2⟩

private lemma tubeParameterGridCell_index_injective
    {base level : ℕ} {A : DiscreteSet 4}
    {cell₁ cell₂ : DiscreteSet 4}
    (h₁ : cell₁ ∈ tubeParameterGridPartition base level A)
    (h₂ : cell₂ ∈ tubeParameterGridPartition base level A)
    {p₁ : Point 4} (hp₁ : p₁ ∈ cell₁)
    {p₂ : Point 4} (hp₂ : p₂ ∈ cell₂)
    (h_eq : tubeParameterGridIndex base level p₁ =
      tubeParameterGridIndex base level p₂) :
    cell₁ = cell₂ := by
  rcases Finset.mem_image.mp h₁ with ⟨r₁, _hr₁, rfl⟩
  rcases Finset.mem_image.mp h₂ with ⟨r₂, _hr₂, rfl⟩
  have h1 := (Finset.mem_filter.mp hp₁).2
  have h2 := (Finset.mem_filter.mp hp₂).2
  have h3 :
      tubeParameterGridIndex base level r₁ =
      tubeParameterGridIndex base level r₂ := by
    rw [← h1, h_eq, h2]
  simp only [tubeParameterGridCell, h3]

private lemma ediv_eq_bounds4
    (base : ℕ) (hbase : 0 < base) (m i : ℤ)
    (hdiv : m / (base : ℤ) = i) :
    i * (base : ℤ) ≤ m ∧ m < (i + 1) * (base : ℤ) := by
  have hb_pos : (0 : ℤ) < (base : ℤ) := Int.natCast_pos.mpr hbase
  have hb_ne : (base : ℤ) ≠ 0 := hb_pos.ne'
  have h1 : m = i * (base : ℤ) + m % (base : ℤ) := by
    calc
      m = m / (base : ℤ) * (base : ℤ) + m % (base : ℤ) :=
        (Int.ediv_mul_add_emod m (base : ℤ)).symm
      _ = i * (base : ℤ) + m % (base : ℤ) := by rw [hdiv]
  have h2 : 0 ≤ m % (base : ℤ) := Int.emod_nonneg m hb_ne
  have h3 : m % (base : ℤ) < (base : ℤ) :=
    Int.emod_lt_of_pos m hb_pos
  constructor <;> linarith

private lemma child_bound_general4
    (base : ℕ) (hbase : 0 < base) (m : Fin 4 → ℤ)
    (S : Finset (Fin 4 → ℤ))
    (h : ∀ idx ∈ S, ∀ i : Fin 4,
      idx i / (base : ℤ) = m i) :
    S.card ≤ base ^ 4 := by
  let s : Fin 4 → Finset ℤ := fun i =>
    Finset.Icc (m i * (base : ℤ))
      ((m i + 1) * (base : ℤ) - 1)
  let toTuple : (Fin 4 → ℤ) → ℤ × (ℤ × (ℤ × ℤ)) :=
    fun f => (f 0, (f 1, (f 2, f 3)))
  let S' : Finset (ℤ × (ℤ × (ℤ × ℤ))) :=
    (s 0) ×ˢ ((s 1) ×ˢ ((s 2) ×ˢ (s 3)))
  have h_inj : Set.InjOn toTuple S := by
    intro f1 hf1 f2 hf2 h_eq
    funext i
    fin_cases i <;> simp [toTuple] at h_eq <;> tauto
  have h_image_card : (S.image toTuple).card = S.card := by
    rw [Finset.card_image_of_injOn h_inj]
  have h_sub : S.image toTuple ⊆ S' := by
    intro p hp
    rcases Finset.mem_image.mp hp with ⟨idx, hidx, rfl⟩
    have h_all : ∀ i, idx i ∈ s i := by
      intro i
      have hbounds :=
        ediv_eq_bounds4 base hbase (idx i) (m i) (h idx hidx i)
      simp only [s, Finset.mem_Icc]
      omega
    simp only [S', Finset.mem_product, toTuple]
    exact ⟨h_all 0, h_all 1, h_all 2, h_all 3⟩
  have h_card : (S.image toTuple).card ≤ S'.card :=
    Finset.card_le_card h_sub
  have h_S'_card :
      S'.card = (s 0).card * (s 1).card * (s 2).card * (s 3).card := by
    simp [S', Finset.card_product]
    <;> ring
  have h_each_card : ∀ i : Fin 4, (s i).card = base := by
    intro i
    have h_le :
        m i * (base : ℤ) ≤
          ((m i + 1) * (base : ℤ) - 1) + 1 := by
      ring_nf
      linarith
    have h' :
        ((Finset.Icc (m i * (base : ℤ))
          ((m i + 1) * (base : ℤ) - 1)).card : ℤ) =
          (base : ℤ) := by
      rw [Int.card_Icc_of_le _ _ h_le]
      <;> simp <;> ring
    exact_mod_cast h'
  rw [h_image_card] at h_card
  rw [h_S'_card, h_each_card 0, h_each_card 1, h_each_card 2, h_each_card 3] at h_card
  convert h_card using 1
  <;> ring

/-- Each occupied 4D grid parent has at most `base^4` occupied children. -/
lemma tube_parameter_grid_partition_child_bound
    {A : DiscreteSet 4} {base level : ℕ}
    (hbase : 2 ≤ base)
    (parent : DiscreteSet 4)
    (hparent : parent ∈ tubeParameterGridPartition base level A) :
    (partitionChildren
      (fun k => tubeParameterGridPartition base k A) level parent).card ≤
        base ^ 4 := by
  let P : ℕ → Finset (Finset (Point 4)) :=
    fun k => tubeParameterGridPartition base k A
  have hbase_pos : 0 < base := by linarith
  let children := partitionChildren P level parent
  have hparent_nonempty : parent.Nonempty :=
    (tubeParameterGridPartition_cell_nonempty_subset hparent).1
  rcases hparent_nonempty with ⟨p_parent, hp_parent⟩
  let parentIndex : Fin 4 → ℤ :=
    fun i => ⌊p_parent i * (base ^ level : ℝ)⌋
  have hparent_idx :
      ∀ x ∈ parent, tubeParameterGridIndex base level x = parentIndex := by
    rcases tubeParameterGridCell_has_index hparent with ⟨idx, hidx⟩
    have h_idx_eq : idx = parentIndex := by
      have h := hidx p_parent hp_parent
      exact h.symm.trans (by rfl)
    intro x hx
    rw [hidx x hx, h_idx_eq]
  let pick : DiscreteSet 4 → Point 4 := fun child =>
    if h : child.Nonempty then Classical.choose h else p_parent
  have hchild_in_partition :
      ∀ child ∈ children, child ∈ P (level + 1) := by
    intro child hchild
    exact (Finset.mem_filter.mp hchild).1
  have hchild_nonempty :
      ∀ child ∈ children, child.Nonempty := by
    intro child hchild
    exact
      (tubeParameterGridPartition_cell_nonempty_subset
        (hchild_in_partition child hchild)).1
  have hchild_sub_parent :
      ∀ child ∈ children, child ⊆ parent := by
    intro child hchild
    exact (Finset.mem_filter.mp hchild).2
  have hpick_mem : ∀ child ∈ children, pick child ∈ child := by
    intro child hchild
    have hne := hchild_nonempty child hchild
    simpa [pick, hne] using Classical.choose_spec hne
  let childIndex : DiscreteSet 4 → (Fin 4 → ℤ) := fun child =>
    tubeParameterGridIndex base (level + 1) (pick child)
  let indices := children.image childIndex
  have hindex_injective : Set.InjOn childIndex children := by
    intro child₁ hchild₁ child₂ hchild₂ h_eq
    exact tubeParameterGridCell_index_injective
      (hchild_in_partition child₁ hchild₁)
      (hchild_in_partition child₂ hchild₂)
      (hpick_mem child₁ hchild₁)
      (hpick_mem child₂ hchild₂) h_eq
  have hindices_card : indices.card = children.card := by
    rw [Finset.card_image_of_injOn hindex_injective]
  have hindices_parent :
      ∀ idx ∈ indices, ∀ i : Fin 4,
        idx i / (base : ℤ) = parentIndex i := by
    intro idx hidx i
    rcases Finset.mem_image.mp hidx with ⟨child, hchild, rfl⟩
    have hpick_parent : pick child ∈ parent :=
      hchild_sub_parent child hchild (hpick_mem child hchild)
    have hlevel_idx := hparent_idx (pick child) hpick_parent
    rw [show childIndex child i =
        ⌊(pick child) i * (base ^ (level + 1) : ℝ)⌋ by rfl,
      floor_child_div_base_eq_floor_parent4 (by linarith)]
    exact congrFun hlevel_idx i
  have hbound : indices.card ≤ base ^ 4 :=
    child_bound_general4 base hbase_pos parentIndex indices hindices_parent
  rwa [hindices_card] at hbound

-- =====================================================================
-- Main theorem
-- =====================================================================

theorem tube_parameter_grid_partition_tree_main
    (A : DiscreteSet 4) (hA_nonempty : A.Nonempty)
    (base levels : ℕ) (hbase : 2 ≤ base)
    (fineScale : ℝ) (hfine_pos : 0 < fineScale)
    (hA_sep : A.IsDeltaSeparated fineScale)
    (hmesh : 4 < fineScale * (base ^ levels : ℝ)) :
    let P : ℕ → Finset (Finset (Point 4)) :=
      fun level => tubeParameterGridPartition base level A
    (∀ level ≤ levels,
      (∀ cell ∈ P level, cell.Nonempty ∧ cell ⊆ A) ∧
      (∀ cell₁ ∈ P level, ∀ cell₂ ∈ P level,
        cell₁ ≠ cell₂ → Disjoint cell₁ cell₂) ∧
      A ⊆ Finset.biUnion (P level) id) ∧
    (∀ cell ∈ P levels, cell.card = 1) ∧
    (∀ level, level < levels →
      ∀ child ∈ P (level + 1),
        ∃ parent ∈ P level, child ⊆ parent) ∧
    ∀ level, level < levels →
      ∀ parent ∈ P level,
        (partitionChildren P level parent).card ≤ (base + 1) ^ 4 := by
  dsimp only
  let P : ℕ → Finset (Finset (Point 4)) :=
    fun level => tubeParameterGridPartition base level A
  constructor
  · intro level _hle
    exact ⟨fun cell hcell => tubeParameterGridPartition_cell_nonempty_subset hcell,
      fun cell₁ h₁ cell₂ h₂ hne =>
        tubeParameterGridPartition_disjoint h₁ h₂ hne,
      tubeParameterGridPartition_cover⟩
  · constructor
    · intro cell hcell
      rcases Finset.mem_image.mp hcell with ⟨p, hpA, rfl⟩
      let cell := tubeParameterGridCell base levels A p
      have hsub : cell ⊆ A := Finset.filter_subset _ _
      have hp_in : p ∈ cell := by
        exact Finset.mem_filter.mpr ⟨hpA, rfl⟩
      have h1 : ∀ q ∈ cell, q = p := by
        intro q hq
        exact terminal_singleton_of_separation4 hbase hfine_pos hA_sep hmesh
          (hsub hq) hpA (Finset.mem_filter.mp hq).2
      have h_card : cell = {p} := by
        apply Finset.eq_singleton_iff_unique_mem.mpr
        exact ⟨hp_in, h1⟩
      simpa [cell, h_card]
    · constructor
      · intro level _hlt child hchild
        exact tubeParameterGridPartition_nesting (by linarith) hchild
      · intro level _hlt parent hparent
        exact
          (tube_parameter_grid_partition_child_bound hbase parent hparent).trans
            (by gcongr; linarith)

end Kakeya.Assouad
