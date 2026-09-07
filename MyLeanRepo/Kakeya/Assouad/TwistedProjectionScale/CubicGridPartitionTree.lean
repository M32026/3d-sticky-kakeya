import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.OSBranchingUniformRefinementStatement
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Int.Interval
import Mathlib.Tactic

/-!
# 3D cubic floor-grid partition tree and ball-cell intersection bound

At level `k`, points are grouped by the integer triple
`(floor (x * base^k), floor (y * base^k), floor (z * base^k))`.
The partitions are nested, each parent has at most `(base + 1)^3` children,
and at a sufficiently fine terminal mesh, separation makes every terminal
cell a singleton.

Also provides the bound that a ball of radius `r` intersects at most
`(2*base+3)^3` grid cells when `r * base^level < base`.
-/

noncomputable section

namespace Kakeya.Assouad

-- =====================================================================
-- Index, cell, partition definitions
-- =====================================================================

/-- Integer index of the cubic `base^(-level)` grid cell containing `p`. -/
def cubicGridIndex (base level : ℕ) (p : Point 3) : Fin 3 → ℤ :=
  fun i => ⌊p i * (base ^ level : ℝ)⌋

/-- The points of `A` in the same cubic grid cell as `p`. -/
def cubicGridCell (base level : ℕ) (A : DiscreteSet 3) (p : Point 3) :
    DiscreteSet 3 :=
  A.filter fun q => cubicGridIndex base level q = cubicGridIndex base level p

/-- The nonempty occupied cubic grid cells at one level. -/
def cubicGridPartition (base level : ℕ) (A : DiscreteSet 3) :
    Finset (DiscreteSet 3) :=
  A.image (cubicGridCell base level A)

private lemma same_floor_abs_sub_lt_one_div
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

private lemma point3_dist_lt_three_mul
    {p q : Point 3} {a : ℝ} (ha : 0 < a)
    (h0 : |p 0 - q 0| < a)
    (h1 : |p 1 - q 1| < a)
    (h2 : |p 2 - q 2| < a) :
    dist p q < 3 * a := by
  let v := p - q
  have hnorm : dist p q = ‖v‖ := by simp [v, dist_eq_norm]
  rw [hnorm]
  have hsq : ‖v‖ ^ 2 = (v 0) ^ 2 + (v 1) ^ 2 + (v 2) ^ 2 := by
    have h := EuclideanSpace.real_norm_sq_eq v
    simpa [Fin.sum_univ_three] using h
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
  have h3 : ‖v‖ ^ 2 < (3 * a) ^ 2 := by
    rw [hsq]
    nlinarith
  nlinarith [norm_nonneg v]

private lemma terminal_singleton_of_separation
    {A : DiscreteSet 3} {base levels : ℕ}
    (hbase : 2 ≤ base)
    {fineScale : ℝ} (hfine_pos : 0 < fineScale)
    (hA_sep : A.IsDeltaSeparated fineScale)
    (hmesh : 3 < fineScale * (base ^ levels : ℝ))
    {p q : Point 3} (hp : p ∈ A) (hq : q ∈ A)
    (hidx : cubicGridIndex base levels p = cubicGridIndex base levels q) :
    p = q := by
  have hM_pos : 0 < (base ^ levels : ℝ) := by positivity
  have hcoord : ∀ i : Fin 3, |p i - q i| < 1 / (base ^ levels : ℝ) := by
    intro i
    exact same_floor_abs_sub_lt_one_div hM_pos (congrFun hidx i)
  have hdist :
      dist p q < 3 * (1 / (base ^ levels : ℝ)) :=
    point3_dist_lt_three_mul (by positivity) (hcoord 0) (hcoord 1) (hcoord 2)
  have hsmall : 3 * (1 / (base ^ levels : ℝ)) < fineScale := by
    have hpow_pos : 0 < (base ^ levels : ℝ) := by positivity
    calc
      3 * (1 / (base ^ levels : ℝ))
          = 3 / (base ^ levels : ℝ) := by ring
      _ < fineScale := (div_lt_iff₀ hpow_pos).2 (by simpa [mul_comm] using hmesh)
  have h12 : dist p q < fineScale := hdist.trans hsmall
  by_cases hne : p ≠ q
  · have h13 : fineScale ≤ dist p q := hA_sep hp hq hne
    linarith
  · exact not_ne_iff.mp hne

lemma cubicGridPartition_cell_nonempty_subset
    {base level : ℕ} {A : DiscreteSet 3}
    {cell : DiscreteSet 3}
    (hcell : cell ∈ cubicGridPartition base level A) :
    cell.Nonempty ∧ cell ⊆ A := by
  rcases Finset.mem_image.mp hcell with ⟨p, hp, rfl⟩
  exact ⟨⟨p, by simp [cubicGridCell, hp]⟩, Finset.filter_subset _ _⟩

lemma cubicGridPartition_disjoint
    {base level : ℕ} {A : DiscreteSet 3}
    {cell₁ cell₂ : DiscreteSet 3}
    (h₁ : cell₁ ∈ cubicGridPartition base level A)
    (h₂ : cell₂ ∈ cubicGridPartition base level A)
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
      cubicGridIndex base level p₁ = cubicGridIndex base level p₂ := by
    rw [← hx₁', hx₂']
  exact hne (by simp only [cubicGridCell, h_eq_idx])

lemma cubicGridPartition_cover
    {base level : ℕ} {A : DiscreteSet 3} :
    A ⊆ Finset.biUnion (cubicGridPartition base level A) id := by
  intro p hp
  exact Finset.mem_biUnion.mpr
    ⟨cubicGridCell base level A p,
      Finset.mem_image.mpr ⟨p, hp, rfl⟩,
      by simp [cubicGridCell, hp]⟩

lemma cubicGridPartition_nonempty
    {base level : ℕ} {A : DiscreteSet 3}
    (hA : A.Nonempty) :
    (cubicGridPartition base level A).Nonempty := by
  rcases hA with ⟨p, hp⟩
  exact ⟨cubicGridCell base level A p,
    Finset.mem_image.mpr ⟨p, hp, rfl⟩⟩

/--
If every occupied grid cell is a singleton, the number of occupied cells is
the cardinality of the point set.
-/
lemma cubicGridPartition_card_eq_of_atomic
    {base level : ℕ}
    {A : DiscreteSet 3}
    (hA : A.Nonempty)
    (hatomic :
      ∀ cell ∈ cubicGridPartition base level A,
        cell.card = 1) :
    (cubicGridPartition base level A).card =
      A.card := by
  have hcover :
      A =
        Finset.biUnion
          (cubicGridPartition base level A) id := by
    apply Finset.Subset.antisymm
    · exact cubicGridPartition_cover
    · intro p hp
      rcases Finset.mem_biUnion.mp hp with
        ⟨cell, hcell, hpcell⟩
      exact
        (cubicGridPartition_cell_nonempty_subset
          hcell).2 hpcell
  have hdisjoint :
      (cubicGridPartition base level A :
        Set (DiscreteSet 3)).PairwiseDisjoint id := by
    intro first hfirst second hsecond hne
    exact cubicGridPartition_disjoint
      hfirst hsecond hne
  calc
    (cubicGridPartition base level A).card =
        ∑ cell ∈ cubicGridPartition base level A,
          cell.card := by
      rw [Finset.sum_congr rfl
        (fun cell hcell => hatomic cell hcell)]
      simp
    _ =
        (Finset.biUnion
          (cubicGridPartition base level A) id).card := by
      rw [Finset.card_biUnion hdisjoint]
      rfl
    _ = A.card := by rw [← hcover]

/-- The occupied cubic-grid cells partition the point set. -/
lemma cubicGridPartition_sum_card
    {base level : ℕ}
    {A : DiscreteSet 3} :
    ∑ cell ∈ cubicGridPartition base level A,
        cell.card =
      A.card := by
  have hcover :
      A =
        Finset.biUnion
          (cubicGridPartition base level A) id := by
    apply Finset.Subset.antisymm
    · exact cubicGridPartition_cover
    · intro p hp
      rcases Finset.mem_biUnion.mp hp with
        ⟨cell, hcell, hpcell⟩
      exact
        (cubicGridPartition_cell_nonempty_subset
          hcell).2 hpcell
  have hdisjoint :
      (cubicGridPartition base level A :
        Set (DiscreteSet 3)).PairwiseDisjoint id := by
    intro first hfirst second hsecond hne
    exact cubicGridPartition_disjoint
      hfirst hsecond hne
  have hcard :=
    Finset.card_biUnion hdisjoint
  calc
    ∑ cell ∈ cubicGridPartition base level A,
          cell.card =
        (Finset.biUnion
          (cubicGridPartition base level A) id).card := by
      simpa using hcard.symm
    _ = A.card := by rw [← hcover]

/--
Two points in one occupied level-`level` cubic cell are less than
`3 * base⁻level` apart.
-/
lemma cubicGridPartition_cell_dist_lt
    {base level : ℕ} {A : DiscreteSet 3}
    (hbase : 2 ≤ base)
    {cell : DiscreteSet 3}
    (hcell : cell ∈ cubicGridPartition base level A)
    {p q : Point 3}
    (hp : p ∈ cell)
    (hq : q ∈ cell) :
    dist p q <
      3 * (1 / (base ^ level : ℝ)) := by
  rcases Finset.mem_image.mp hcell with
    ⟨representative, _hrepresentative, rfl⟩
  have hp_index :=
    (Finset.mem_filter.mp hp).2
  have hq_index :=
    (Finset.mem_filter.mp hq).2
  have hpq_index :
      cubicGridIndex base level p =
        cubicGridIndex base level q := by
    rw [hp_index, hq_index]
  have hpow_pos :
      0 < (base ^ level : ℝ) := by
    positivity
  have hcoord :
      ∀ i : Fin 3,
        |p i - q i| <
          1 / (base ^ level : ℝ) := by
    intro i
    exact
      same_floor_abs_sub_lt_one_div
        hpow_pos (congrFun hpq_index i)
  exact point3_dist_lt_three_mul
    (by positivity) (hcoord 0) (hcoord 1) (hcoord 2)

lemma floor_child_div_base_eq_floor_parent
    {base level : ℕ} (hbase : 1 ≤ base) (x : ℝ) :
    ⌊x * (base ^ (level + 1) : ℝ)⌋ / (base : ℤ) =
      ⌊x * (base ^ level : ℝ)⌋ := by
  have hbase_ne : base ≠ 0 := by omega
  rw [show x * (base ^ (level + 1) : ℝ) =
    (x * (base ^ level : ℝ)) * (base : ℝ) by simp [pow_succ]; ring]
  exact Int.mul_natCast_floor_div_cancel hbase_ne
    (x * (base ^ level : ℝ))

lemma cubicGridPartition_nesting
    {base level : ℕ} {A : DiscreteSet 3}
    (hbase : 1 ≤ base)
    {child : DiscreteSet 3}
    (hchild : child ∈ cubicGridPartition base (level + 1) A) :
    ∃ parent ∈ cubicGridPartition base level A, child ⊆ parent := by
  rcases Finset.mem_image.mp hchild with ⟨p, hp, rfl⟩
  let parent := cubicGridCell base level A p
  refine ⟨parent, Finset.mem_image.mpr ⟨p, hp, rfl⟩, ?_⟩
  intro q hq
  have hqA : q ∈ A := (Finset.mem_filter.mp hq).1
  have h_idx := (Finset.mem_filter.mp hq).2
  have h_floor : ∀ i : Fin 3,
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
      floor_child_div_base_eq_floor_parent hbase (q i)
    have hp_div :
        ⌊p i * (base ^ (level + 1) : ℝ)⌋ / (base : ℤ) =
          ⌊p i * (base ^ level : ℝ)⌋ :=
      floor_child_div_base_eq_floor_parent hbase (p i)
    rw [← hq_div, ← hp_div, hq_i]
  exact Finset.mem_filter.mpr
    ⟨hqA, funext fun i => h_floor i⟩

private lemma cubicGridCell_has_index
    {base level : ℕ} {A : DiscreteSet 3}
    {cell : DiscreteSet 3}
    (hcell : cell ∈ cubicGridPartition base level A) :
    ∃ idx : Fin 3 → ℤ, ∀ p ∈ cell, cubicGridIndex base level p = idx := by
  rcases Finset.mem_image.mp hcell with ⟨p, _hp, rfl⟩
  exact ⟨cubicGridIndex base level p,
    fun q hq => (Finset.mem_filter.mp hq).2⟩

private lemma cubicGridCell_index_injective
    {base level : ℕ} {A : DiscreteSet 3}
    {cell₁ cell₂ : DiscreteSet 3}
    (h₁ : cell₁ ∈ cubicGridPartition base level A)
    (h₂ : cell₂ ∈ cubicGridPartition base level A)
    {p₁ : Point 3} (hp₁ : p₁ ∈ cell₁)
    {p₂ : Point 3} (hp₂ : p₂ ∈ cell₂)
    (h_eq : cubicGridIndex base level p₁ =
      cubicGridIndex base level p₂) :
    cell₁ = cell₂ := by
  rcases Finset.mem_image.mp h₁ with ⟨r₁, _hr₁, rfl⟩
  rcases Finset.mem_image.mp h₂ with ⟨r₂, _hr₂, rfl⟩
  have h1 := (Finset.mem_filter.mp hp₁).2
  have h2 := (Finset.mem_filter.mp hp₂).2
  have h3 :
      cubicGridIndex base level r₁ = cubicGridIndex base level r₂ := by
    rw [← h1, h_eq, h2]
  simp only [cubicGridCell, h3]

private lemma ediv_eq_bounds
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

private lemma child_bound_general3
    (base : ℕ) (hbase : 0 < base) (m : Fin 3 → ℤ)
    (S : Finset (Fin 3 → ℤ))
    (h : ∀ idx ∈ S, ∀ i : Fin 3,
      idx i / (base : ℤ) = m i) :
    S.card ≤ base ^ 3 := by
  let s : Fin 3 → Finset ℤ := fun i =>
    Finset.Icc (m i * (base : ℤ))
      ((m i + 1) * (base : ℤ) - 1)
  let toTuple : (Fin 3 → ℤ) → ℤ × (ℤ × ℤ) :=
    fun f => (f 0, (f 1, f 2))
  let S' : Finset (ℤ × (ℤ × ℤ)) :=
    (s 0) ×ˢ ((s 1) ×ˢ (s 2))
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
        ediv_eq_bounds base hbase (idx i) (m i) (h idx hidx i)
      simp only [s, Finset.mem_Icc]
      omega
    simp only [S', Finset.mem_product, toTuple]
    exact ⟨h_all 0, h_all 1, h_all 2⟩
  have h_card : (S.image toTuple).card ≤ S'.card :=
    Finset.card_le_card h_sub
  have h_S'_card :
      S'.card = (s 0).card * (s 1).card * (s 2).card := by
    simp [S', Finset.card_product]
    <;> ring
  have h_each_card : ∀ i : Fin 3, (s i).card = base := by
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
  rw [h_S'_card, h_each_card 0, h_each_card 1, h_each_card 2] at h_card
  convert h_card using 1
  <;> ring

/-- Each occupied cubic-grid parent has at most `base^3` occupied children. -/
lemma cubic_grid_partition_child_bound
    {A : DiscreteSet 3} {base level : ℕ}
    (hbase : 2 ≤ base)
    (parent : DiscreteSet 3)
    (hparent : parent ∈ cubicGridPartition base level A) :
    (partitionChildren
      (fun k => cubicGridPartition base k A) level parent).card ≤
        base ^ 3 := by
  let P : ℕ → Finset (Finset (Point 3)) :=
    fun k => cubicGridPartition base k A
  have hbase_pos : 0 < base := by linarith
  let children := partitionChildren P level parent
  have hparent_nonempty : parent.Nonempty :=
    (cubicGridPartition_cell_nonempty_subset hparent).1
  rcases hparent_nonempty with ⟨p_parent, hp_parent⟩
  let parentIndex : Fin 3 → ℤ :=
    fun i => ⌊p_parent i * (base ^ level : ℝ)⌋
  have hparent_idx :
      ∀ x ∈ parent, cubicGridIndex base level x = parentIndex := by
    rcases cubicGridCell_has_index hparent with ⟨idx, hidx⟩
    have h_idx_eq : idx = parentIndex := by
      have h := hidx p_parent hp_parent
      exact h.symm.trans (by rfl)
    intro x hx
    rw [hidx x hx, h_idx_eq]
  let pick : DiscreteSet 3 → Point 3 := fun child =>
    if h : child.Nonempty then Classical.choose h else p_parent
  have hchild_in_partition :
      ∀ child ∈ children, child ∈ P (level + 1) := by
    intro child hchild
    exact (Finset.mem_filter.mp hchild).1
  have hchild_nonempty :
      ∀ child ∈ children, child.Nonempty := by
    intro child hchild
    exact
      (cubicGridPartition_cell_nonempty_subset
        (hchild_in_partition child hchild)).1
  have hchild_sub_parent :
      ∀ child ∈ children, child ⊆ parent := by
    intro child hchild
    exact (Finset.mem_filter.mp hchild).2
  have hpick_mem : ∀ child ∈ children, pick child ∈ child := by
    intro child hchild
    have hne := hchild_nonempty child hchild
    simpa [pick, hne] using Classical.choose_spec hne
  let childIndex : DiscreteSet 3 → (Fin 3 → ℤ) := fun child =>
    cubicGridIndex base (level + 1) (pick child)
  let indices := children.image childIndex
  have hindex_injective : Set.InjOn childIndex children := by
    intro child₁ hchild₁ child₂ hchild₂ h_eq
    exact cubicGridCell_index_injective
      (hchild_in_partition child₁ hchild₁)
      (hchild_in_partition child₂ hchild₂)
      (hpick_mem child₁ hchild₁)
      (hpick_mem child₂ hchild₂) h_eq
  have hindices_card : indices.card = children.card := by
    rw [Finset.card_image_of_injOn hindex_injective]
  have hindices_parent :
      ∀ idx ∈ indices, ∀ i : Fin 3,
        idx i / (base : ℤ) = parentIndex i := by
    intro idx hidx i
    rcases Finset.mem_image.mp hidx with ⟨child, hchild, rfl⟩
    have hpick_parent : pick child ∈ parent :=
      hchild_sub_parent child hchild (hpick_mem child hchild)
    have hlevel_idx := hparent_idx (pick child) hpick_parent
    rw [show childIndex child i =
        ⌊(pick child) i * (base ^ (level + 1) : ℝ)⌋ by rfl,
      floor_child_div_base_eq_floor_parent (by linarith)]
    exact congrFun hlevel_idx i
  have hbound : indices.card ≤ base ^ 3 :=
    child_bound_general3 base hbase_pos parentIndex indices hindices_parent
  rwa [hindices_card] at hbound

theorem cubic_grid_partition_tree
    (A : DiscreteSet 3) (hA_nonempty : A.Nonempty)
    (base levels : ℕ) (hbase : 2 ≤ base)
    (fineScale : ℝ) (hfine_pos : 0 < fineScale)
    (hA_sep : A.IsDeltaSeparated fineScale)
    (hmesh : 3 < fineScale * (base ^ levels : ℝ)) :
    let P : ℕ → Finset (Finset (Point 3)) :=
      fun level => cubicGridPartition base level A
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
        (partitionChildren P level parent).card ≤ (base + 1) ^ 3 := by
  dsimp only
  let P : ℕ → Finset (Finset (Point 3)) :=
    fun level => cubicGridPartition base level A
  constructor
  · intro level _hle
    exact ⟨fun cell hcell => cubicGridPartition_cell_nonempty_subset hcell,
      fun cell₁ h₁ cell₂ h₂ hne =>
        cubicGridPartition_disjoint h₁ h₂ hne,
      cubicGridPartition_cover⟩
  · constructor
    · intro cell hcell
      rcases Finset.mem_image.mp hcell with ⟨p, hpA, rfl⟩
      let cell := cubicGridCell base levels A p
      have hsub : cell ⊆ A := Finset.filter_subset _ _
      have hp_in : p ∈ cell := by
        exact Finset.mem_filter.mpr ⟨hpA, rfl⟩
      have h1 : ∀ q ∈ cell, q = p := by
        intro q hq
        exact terminal_singleton_of_separation hbase hfine_pos hA_sep hmesh
          (hsub hq) hpA (Finset.mem_filter.mp hq).2
      have h_card : cell = {p} := by
        apply Finset.eq_singleton_iff_unique_mem.mpr
        exact ⟨hp_in, h1⟩
      simpa [cell, h_card]
    · constructor
      · intro level _hlt child hchild
        exact cubicGridPartition_nesting (by linarith) hchild
      · intro level _hlt parent hparent
        exact
          (cubic_grid_partition_child_bound hbase parent hparent).trans
            (by gcongr; linarith)

private lemma floor_sub_le (a b : ℝ) :
    ⌊a⌋ - ⌊b⌋ ≤ ⌊a - b⌋ + 1 := by
  have h1 : (⌊a⌋ : ℝ) ≤ a := Int.floor_le a
  have h2 : (b : ℝ) < (⌊b⌋ : ℝ) + 1 := Int.lt_floor_add_one b
  have h3 : (⌊a⌋ : ℝ) - (⌊b⌋ : ℝ) < a - b + 1 := by
    linarith
  have h4 :
      ((⌊a⌋ - ⌊b⌋ : ℤ) : ℝ) =
        (⌊a⌋ : ℝ) - (⌊b⌋ : ℝ) := by
    simp
  have h5 : ((⌊a⌋ - ⌊b⌋ : ℤ) : ℝ) ≤ a - b + 1 := by
    rw [h4]
    exact le_of_lt h3
  have h6 : ⌊a⌋ - ⌊b⌋ ≤ ⌊a - b + 1⌋ := Int.le_floor.mpr h5
  have h7 : ⌊a - b + 1⌋ = ⌊a - b⌋ + 1 := by
    simp
  rw [h7] at h6
  exact h6

private lemma floor_interval_card {lo hi : ℝ} (h_lo_le_hi : lo ≤ hi) :
    (Finset.Icc ⌊lo⌋ ⌊hi⌋).card ≤ ⌊hi - lo⌋ + 2 := by
  by_cases h : ⌊lo⌋ ≤ ⌊hi⌋
  · have h_card :
        (Finset.Icc ⌊lo⌋ ⌊hi⌋).card =
          ⌊hi⌋ - ⌊lo⌋ + 1 := by
      simp
      omega
    rw [h_card]
    have h6 : ⌊hi⌋ - ⌊lo⌋ ≤ ⌊hi - lo⌋ + 1 :=
      floor_sub_le hi lo
    omega
  · have h_empty : Finset.Icc ⌊lo⌋ ⌊hi⌋ = ∅ := by
      apply Finset.Icc_eq_empty_of_lt
      omega
    rw [h_empty]
    have h9 : 0 ≤ hi - lo := by linarith
    have h10 : 0 ≤ ⌊hi - lo⌋ := Int.floor_nonneg.mpr h9
    have h11 : 0 ≤ ⌊hi - lo⌋ + 2 := by omega
    simpa using h11

private lemma coord_abs_le_norm (v : Point 3) (i : Fin 3) :
    |v i| ≤ ‖v‖ := by
  have h1 : (v i) ^ 2 ≤ ‖v‖ ^ 2 := by
    have h2 : ‖v‖ ^ 2 = ∑ j : Fin 3, (v j) ^ 2 := by
      simpa [EuclideanSpace.real_norm_sq_eq] using rfl
    rw [h2]
    exact Finset.single_le_sum (fun j _ => sq_nonneg (v j))
      (Finset.mem_univ i)
  nlinarith [abs_nonneg (v i), norm_nonneg v, sq_abs (v i)]

lemma cubic_grid_ball_cell_bound_with
    {A : DiscreteSet 3} {base level cellBound : ℕ}
    {x : Point 3} {r : ℝ}
    (hbase : 2 ≤ base) (hr_pos : 0 < r)
    (hr_scale :
      r * (base ^ level : ℝ) < (cellBound : ℝ)) :
    ((cubicGridPartition base level A).filter
      (fun c => ∃ p ∈ c, dist p x ≤ r)).card ≤
        (2 * cellBound + 1) ^ 3 := by
  set M : ℝ := (base ^ level : ℝ)
  have hM_pos : 0 < M := by positivity
  let intersecting := (cubicGridPartition base level A).filter
      (fun c => ∃ p ∈ c, dist p x ≤ r)
  let pick (c : DiscreteSet 3) : Point 3 :=
    if h : ∃ p ∈ c, dist p x ≤ r then Classical.choose h else x
  have hpick_mem : ∀ c ∈ intersecting, pick c ∈ c := by
    intro c hc
    have h := (Finset.mem_filter.mp hc).2
    simpa [pick, h] using (Classical.choose_spec h).1
  have hpick_dist : ∀ c ∈ intersecting, dist (pick c) x ≤ r := by
    intro c hc
    have h := (Finset.mem_filter.mp hc).2
    simpa [pick, h] using (Classical.choose_spec h).2
  let g : DiscreteSet 3 → (Fin 3 → ℤ) := fun c =>
    cubicGridIndex base level (pick c)
  let S := intersecting.image g
  have h_inj : Set.InjOn g intersecting := by
    intro c1 hc1 c2 hc2 h_eq
    exact cubicGridCell_index_injective
      (Finset.mem_filter.mp hc1).1 (Finset.mem_filter.mp hc2).1
      (hpick_mem c1 hc1) (hpick_mem c2 hc2) h_eq
  have h_card_eq : S.card = intersecting.card := by
    rw [Finset.card_image_of_injOn h_inj]
  let coordRange (i : Fin 3) : Finset ℤ :=
    Finset.Icc ⌊(x i - r) * M⌋ ⌊(x i + r) * M⌋
  have h_coord_bound :
      ∀ i : Fin 3, (coordRange i).card ≤
        2 * cellBound + 1 := by
    intro i
    have h_lo_le : (x i - r) * M ≤ (x i + r) * M := by
      gcongr
      linarith
    have h1 :
        (coordRange i).card ≤
          ⌊(x i + r) * M - ((x i - r) * M)⌋ + 2 :=
      floor_interval_card h_lo_le
    have h2 :
        (x i + r) * M - ((x i - r) * M) = 2 * r * M := by
      ring
    have h3 :
        ⌊(x i + r) * M - ((x i - r) * M)⌋ =
          ⌊2 * r * M⌋ := by
      rw [h2]
    rw [h3] at h1
    have h4 : 2 * r * M < 2 * (cellBound : ℝ) := by
      linarith
    have h6 : ⌊2 * r * M⌋ ≤ 2 * cellBound - 1 := by
      have h7 : ⌊2 * r * M⌋ < (2 * cellBound : ℤ) := by
        apply Int.floor_lt.mpr
        exact_mod_cast h4
      omega
    omega
  let S' : Finset (ℤ × (ℤ × ℤ)) :=
    (coordRange 0) ×ˢ ((coordRange 1) ×ˢ coordRange 2)
  let toTuple : (Fin 3 → ℤ) → ℤ × (ℤ × ℤ) :=
    fun f => (f 0, (f 1, f 2))
  have hS_sub : S.image toTuple ⊆ S' := by
    intro p hp
    rcases Finset.mem_image.mp hp with ⟨idx, hidx, rfl⟩
    rcases Finset.mem_image.mp hidx with ⟨c, hc, rfl⟩
    have h_dist := hpick_dist c hc
    have h_coord : ∀ i : Fin 3, |pick c i - x i| ≤ r := by
      intro i
      have h_norm : |(pick c - x) i| ≤ ‖pick c - x‖ :=
        coord_abs_le_norm (pick c - x) i
      simpa [dist_eq_norm] using h_norm.trans h_dist
    have h_all : ∀ i : Fin 3,
        cubicGridIndex base level (pick c) i ∈ coordRange i := by
      intro i
      simp only [coordRange, cubicGridIndex, Finset.mem_Icc]
      constructor
      · apply Int.floor_le_floor
        gcongr
        linarith [abs_le.mp (h_coord i)]
      · apply Int.floor_le_floor
        gcongr
        linarith [abs_le.mp (h_coord i)]
    have h_idx_in : toTuple (g c) ∈ S' := by
      simp only [S', Finset.mem_product, toTuple]
      exact ⟨h_all 0, h_all 1, h_all 2⟩
    exact h_idx_in
  have h_inj2 : Set.InjOn toTuple S := by
    intro f1 hf1 f2 hf2 h_eq
    funext i
    fin_cases i <;> simp [toTuple] at h_eq <;> tauto
  calc
    intersecting.card = S.card := h_card_eq.symm
    _ = (S.image toTuple).card := by
      rw [Finset.card_image_of_injOn h_inj2]
    _ ≤ S'.card := Finset.card_le_card hS_sub
    _ ≤ (2 * cellBound + 1) ^ 3 := by
      have h_S'_card :
          S'.card =
            (coordRange 0).card *
              (coordRange 1).card * (coordRange 2).card := by
        simp [S', Finset.card_product]
        <;> ring
      rw [h_S'_card]
      have h0 := h_coord_bound 0
      have h1 := h_coord_bound 1
      have h2 := h_coord_bound 2
      calc
        (coordRange 0).card *
              (coordRange 1).card * (coordRange 2).card ≤
            (2 * cellBound + 1) *
              (2 * cellBound + 1) *
                (2 * cellBound + 1) := by
          gcongr
        _ = (2 * cellBound + 1) ^ 3 := by ring

lemma cubic_grid_ball_cell_bound
    {A : DiscreteSet 3} {base level : ℕ}
    {x : Point 3} {r : ℝ}
    (hbase : 2 ≤ base) (hr_pos : 0 < r)
    (hr_scale : r * (base ^ level : ℝ) < (base : ℝ)) :
    ((cubicGridPartition base level A).filter
      (fun c => ∃ p ∈ c, dist p x ≤ r)).card ≤
        (2 * base + 1) ^ 3 :=
  cubic_grid_ball_cell_bound_with
    hbase hr_pos hr_scale

/--
A set in the unit ball occupies at most `125` cells of the level-zero cubic
grid.  The deliberately coarse constant comes from the general ball-cell
intersection lemma.
-/
lemma cubicGridPartition_zero_card_le
    {base : ℕ}
    {A : DiscreteSet 3}
    (hbase : 2 ≤ base)
    (hunit : A.IsInUnitBall) :
    (cubicGridPartition base 0 A).card ≤
      (2 * base + 1) ^ 3 := by
  have hbound :=
    cubic_grid_ball_cell_bound
      (A := A) (base := base) (level := 0)
      (x := 0) (r := 1)
      hbase (by norm_num)
      (by
        simp
        exact_mod_cast hbase)
  have hall :
      (cubicGridPartition base 0 A).filter
          (fun cell =>
            ∃ p ∈ cell, dist p 0 ≤ 1) =
        cubicGridPartition base 0 A := by
    apply Finset.filter_eq_self.mpr
    intro cell hcell
    rcases
        (cubicGridPartition_cell_nonempty_subset
          hcell).1 with
      ⟨p, hp⟩
    exact ⟨p, hp,
      hunit p
        ((cubicGridPartition_cell_nonempty_subset
          hcell).2 hp)⟩
  rwa [hall] at hbound

end Kakeya.Assouad
