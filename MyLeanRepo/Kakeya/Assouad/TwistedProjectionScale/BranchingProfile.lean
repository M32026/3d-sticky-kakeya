import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.CubicGridPartitionTree
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# Branching profile for 3D cubic grid

Computes local dimensions from cell counts and sets up scale weights
for the first-crossing argument.

Depends on `CubicGridPartitionTree` for grid definitions and basic properties.
-/

noncomputable section

namespace Kakeya.Assouad

-- =====================================================================
-- Tight child bound
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

/-- For any finite set of integer triples all mapping to the same parent
index under division by `base`, the cardinality is at most `base^3`. -/
private lemma child_bound_general3
    (base : ℕ) (hbase : 0 < base) (m : Fin 3 → ℤ)
    (S : Finset (Fin 3 → ℤ))
    (h : ∀ idx ∈ S, ∀ i : Fin 3, idx i / (base : ℤ) = m i) :
    S.card ≤ base ^ 3 := by
  let s : Fin 3 → Finset ℤ := fun i =>
    Finset.Icc (m i * (base : ℤ)) ((m i + 1) * (base : ℤ) - 1)
  let toTuple : (Fin 3 → ℤ) → ℤ × (ℤ × ℤ) := fun f => (f 0, (f 1, f 2))
  let S' : Finset (ℤ × (ℤ × ℤ)) := (s 0) ×ˢ ((s 1) ×ˢ (s 2))
  have h_inj : Set.InjOn toTuple S := by
    intro f1 hf1 f2 hf2 h_eq
    funext i; fin_cases i <;> simp [toTuple] at h_eq <;> tauto
  have h_sub : S.image toTuple ⊆ S' := by
    intro p hp
    rcases Finset.mem_image.mp hp with ⟨idx, hidx, rfl⟩
    have h_all : ∀ i, idx i ∈ s i := by
      intro i
      have hdiv := h idx hidx i
      have hbounds := ediv_eq_bounds base hbase (idx i) (m i) hdiv
      simp only [s, Finset.mem_Icc] <;> omega
    simp only [S', Finset.mem_product, toTuple]
    exact ⟨h_all 0, h_all 1, h_all 2⟩
  have h_card : (S.image toTuple).card ≤ S'.card := Finset.card_le_card h_sub
  have h_eq : (S.image toTuple).card = S.card := by
    rw [Finset.card_image_of_injOn h_inj]
  have h_S'_card : S'.card = (s 0).card * (s 1).card * (s 2).card := by
    simp [S', Finset.card_product] <;> ring
  have h_each : ∀ i, (s i).card = base := by
    intro i
    have h_le : m i * (base : ℤ) ≤ ((m i + 1) * (base : ℤ) - 1) + 1 := by ring_nf; linarith
    have h_int : ((Finset.Icc (m i * (base : ℤ)) ((m i + 1) * (base : ℤ) - 1)).card : ℤ) = (base : ℤ) := by
      rw [Int.card_Icc_of_le _ _ h_le] <;> simp <;> ring
    have h' : (s i).card = base := by exact_mod_cast h_int
    exact h'
  rw [h_eq] at h_card
  rw [h_S'_card] at h_card
  rw [h_each 0, h_each 1, h_each 2] at h_card
  have h_goal : S.card ≤ base ^ 3 := by
    convert h_card using 1
    <;> ring
  exact h_goal

/-- Tight child bound: each parent has at most `base^3` children. -/
lemma cubic_grid_child_bound_tight
    {A : DiscreteSet 3} {base level : ℕ} (hbase : 2 ≤ base)
    (parent : DiscreteSet 3)
    (hparent : parent ∈ cubicGridPartition base level A) :
    (partitionChildren (fun k => cubicGridPartition base k A) level parent).card ≤ base ^ 3 := by
  let P := fun k : ℕ => cubicGridPartition base k A
  have hbase_pos : 0 < base := by linarith
  let children := partitionChildren P level parent
  have hparent_nonempty : parent.Nonempty := by
    rcases Finset.mem_image.mp hparent with ⟨p, hp, rfl⟩
    have hmem : p ∈ cubicGridCell base level A p := by simp [cubicGridCell, hp]
    exact ⟨p, hmem⟩
  rcases hparent_nonempty with ⟨p_parent, hp_parent⟩
  let m : Fin 3 → ℤ := fun i => ⌊p_parent i * (base ^ level : ℝ)⌋
  have hparent_idx : ∀ x ∈ parent, cubicGridIndex base level x = m := by
    rcases Finset.mem_image.mp hparent with ⟨r, _hr, rfl⟩
    have h_idx : ∀ p ∈ cubicGridCell base level A r, cubicGridIndex base level p = cubicGridIndex base level r := by
      intro p hp; exact (Finset.mem_filter.mp hp).2
    have h_pp_idx : cubicGridIndex base level p_parent = cubicGridIndex base level r := h_idx p_parent hp_parent
    intro x hx
    have h1 : cubicGridIndex base level x = cubicGridIndex base level r := h_idx x hx
    have h2 : cubicGridIndex base level r = m := by
      funext i
      have h3 : cubicGridIndex base level p_parent i = cubicGridIndex base level r i := by
        rw [h_pp_idx]
      have h4 : cubicGridIndex base level p_parent i = m i := by
        simpa [cubicGridIndex, m] using rfl
      rw [←h3, h4]
    rw [h1, h2]
  let f : DiscreteSet 3 → Point 3 := fun child =>
    if h : child.Nonempty then Classical.choose h else p_parent
  have hchild_nonempty : ∀ child ∈ children, child.Nonempty := by
    intro child hchild
    have h_in_P : child ∈ P (level + 1) := (Finset.mem_filter.mp hchild).1
    rcases Finset.mem_image.mp h_in_P with ⟨p, hp, rfl⟩
    have hmem : p ∈ cubicGridCell base (level + 1) A p := by simp [cubicGridCell, hp]
    exact ⟨p, hmem⟩
  have hf_mem : ∀ child ∈ children, f child ∈ child := by
    intro child hchild
    have hne : child.Nonempty := hchild_nonempty child hchild
    have h_eq : f child = Classical.choose hne := by simp [f, hne]
    rw [h_eq]; exact Classical.choose_spec hne
  have hchild_sub_parent : ∀ child ∈ children, child ⊆ parent := by
    intro child hchild; exact (Finset.mem_filter.mp hchild).2
  let g : DiscreteSet 3 → (Fin 3 → ℤ) := fun child =>
    cubicGridIndex base (level + 1) (f child)
  let S := children.image g
  have h_inj : Set.InjOn g children := by
    intro c1 hc1 c2 hc2 h_eq
    have h1 : f c1 ∈ c1 := hf_mem c1 hc1
    have h2 : f c2 ∈ c2 := hf_mem c2 hc2
    have hc1' : c1 ∈ P (level + 1) := (Finset.mem_filter.mp hc1).1
    have hc2' : c2 ∈ P (level + 1) := (Finset.mem_filter.mp hc2).1
    rcases Finset.mem_image.mp hc1' with ⟨r1, _, rfl⟩
    rcases Finset.mem_image.mp hc2' with ⟨r2, _, rfl⟩
    have h_idx1 : cubicGridIndex base (level + 1) (f (cubicGridCell base (level + 1) A r1)) =
        cubicGridIndex base (level + 1) r1 :=
      (Finset.mem_filter.mp h1).2
    have h_idx2 : cubicGridIndex base (level + 1) (f (cubicGridCell base (level + 1) A r2)) =
        cubicGridIndex base (level + 1) r2 :=
      (Finset.mem_filter.mp h2).2
    have h_g1 : g (cubicGridCell base (level + 1) A r1) =
        cubicGridIndex base (level + 1) (f (cubicGridCell base (level + 1) A r1)) := by rfl
    have h_g2 : g (cubicGridCell base (level + 1) A r2) =
        cubicGridIndex base (level + 1) (f (cubicGridCell base (level + 1) A r2)) := by rfl
    have h_eq' : cubicGridIndex base (level + 1) (f (cubicGridCell base (level + 1) A r1)) =
        cubicGridIndex base (level + 1) (f (cubicGridCell base (level + 1) A r2)) := by
      have h : g (cubicGridCell base (level + 1) A r1) = g (cubicGridCell base (level + 1) A r2) := h_eq
      rw [h_g1, h_g2] at h
      exact h
    have h_eq2 : cubicGridIndex base (level + 1) r1 = cubicGridIndex base (level + 1) r2 := by
      calc
        cubicGridIndex base (level + 1) r1
          = cubicGridIndex base (level + 1) (f (cubicGridCell base (level + 1) A r1)) := h_idx1.symm
        _ = cubicGridIndex base (level + 1) (f (cubicGridCell base (level + 1) A r2)) := h_eq'
        _ = cubicGridIndex base (level + 1) r2 := h_idx2
    simp only [cubicGridCell, h_eq2]
  have h_card_eq : S.card = children.card := by
    rw [Finset.card_image_of_injOn h_inj]
  have hS_prop : ∀ idx ∈ S, ∀ i : Fin 3, idx i / (base : ℤ) = m i := by
    intro idx hidx i
    rcases Finset.mem_image.mp hidx with ⟨child, hchild, rfl⟩
    have h_f_in_parent : f child ∈ parent := hchild_sub_parent child hchild (hf_mem child hchild)
    have h_level_idx : cubicGridIndex base level (f child) = m := hparent_idx (f child) h_f_in_parent
    have h_div : ⌊(f child) i * (base ^ (level + 1) : ℝ)⌋ / (base : ℤ) =
        ⌊(f child) i * (base ^ level : ℝ)⌋ :=
      floor_child_div_base_eq_floor_parent (by linarith) ((f child) i)
    have h_floor : ⌊(f child) i * (base ^ level : ℝ)⌋ = m i := by
      have h' := congr_fun h_level_idx i
      simpa [cubicGridIndex, m] using h'
    have hg : (g child) i = ⌊(f child) i * (base ^ (level + 1) : ℝ)⌋ := by
      simp [g, cubicGridIndex]
    rw [hg, h_div, h_floor]
  have h_bound : S.card ≤ base ^ 3 := child_bound_general3 base hbase_pos m S hS_prop
  rw [←h_card_eq]
  exact h_bound

-- =====================================================================
-- Part 1: Cell count and local dimension
-- =====================================================================

/-- Number of occupied cells at level `k`. -/
def cellCount (base : ℕ) (A : DiscreteSet 3) (k : ℕ) : ℕ :=
  (cubicGridPartition base k A).card

/-- Number of cells increases (nesting). -/
lemma cellCount_mono {base A} {k : ℕ} (hbase : 2 ≤ base) :
    cellCount base A k ≤ cellCount base A (k + 1) := by
  let P := fun k => cubicGridPartition base k A
  let f : DiscreteSet 3 → DiscreteSet 3 := fun parent =>
    if h : parent.Nonempty then cubicGridCell base (k + 1) A (Classical.choose h)
    else parent
  have hf_mem : ∀ parent ∈ P k, f parent ∈ P (k + 1) := by
    intro parent hparent
    have hne : parent.Nonempty := (cubicGridPartition_cell_nonempty_subset hparent).1
    let p := Classical.choose hne
    have hp : p ∈ parent := Classical.choose_spec hne
    have hpA : p ∈ A := (cubicGridPartition_cell_nonempty_subset hparent).2 hp
    have h_eq : f parent = cubicGridCell base (k + 1) A p := by
      simp [f, hne, p] <;> rfl
    rw [h_eq]
    apply Finset.mem_image.mpr
    exact ⟨p, hpA, rfl⟩
  have hf_sub : ∀ parent ∈ P k, f parent ⊆ parent := by
    intro parent hparent
    rcases cubicGridPartition_nesting (by linarith) (hf_mem parent hparent) with ⟨par', hpar', hsub⟩
    have hne : parent.Nonempty := (cubicGridPartition_cell_nonempty_subset hparent).1
    let p := Classical.choose hne
    have hp : p ∈ parent := Classical.choose_spec hne
    have hpA : p ∈ A := (cubicGridPartition_cell_nonempty_subset hparent).2 hp
    have h_eq : f parent = cubicGridCell base (k + 1) A p := by
      simp [f, hne, p] <;> rfl
    have hp_f : p ∈ f parent := by
      rw [h_eq]
      simp [cubicGridCell, hpA]
    have hp_par' : p ∈ par' := hsub hp_f
    by_cases h_eq_par : parent = par'
    · exact h_eq_par.symm ▸ hsub
    · have h_disj : Disjoint parent par' := cubicGridPartition_disjoint hparent hpar' h_eq_par
      exact False.elim (Finset.disjoint_left.mp h_disj hp hp_par')
  have h_inj : Set.InjOn f (P k) := by
    intro c1 hc1 c2 hc2 h_eq
    have hne1 : c1.Nonempty := (cubicGridPartition_cell_nonempty_subset hc1).1
    let p1 := Classical.choose hne1
    have hp1 : p1 ∈ c1 := Classical.choose_spec hne1
    have hp1_f : p1 ∈ f c1 := by
      have h_eq1 : f c1 = cubicGridCell base (k + 1) A p1 := by
        simp [f, hne1, p1] <;> rfl
      rw [h_eq1]
      have hp1A : p1 ∈ A := (cubicGridPartition_cell_nonempty_subset hc1).2 hp1
      simp [cubicGridCell, hp1A]
    have h_p1_c2 : p1 ∈ c2 := by
      rw [h_eq] at hp1_f
      exact hf_sub c2 hc2 hp1_f
    by_cases h : c1 = c2
    · exact h
    · have h_disj : Disjoint c1 c2 := cubicGridPartition_disjoint hc1 hc2 h
      exact False.elim (Finset.disjoint_left.mp h_disj hp1 h_p1_c2)
  have h_image_card : (P k).card = ((P k).image f).card := by
    rw [Finset.card_image_of_injOn h_inj]
  have h_sub : (P k).image f ⊆ P (k + 1) := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨parent, hparent, rfl⟩
    exact hf_mem parent hparent
  have h : ((P k).image f).card ≤ (P (k + 1)).card := Finset.card_le_card h_sub
  rw [←h_image_card] at h
  exact h

/-- Each cell has at most `base^3` children, so total cells grow by at most `base^3`. -/
lemma cellCount_growth_bound {base A} {k : ℕ} (hbase : 2 ≤ base) :
    cellCount base A (k + 1) ≤ base ^ 3 * cellCount base A k := by
  let P := fun k => cubicGridPartition base k A
  have h_nesting : ∀ child ∈ P (k + 1), ∃ parent ∈ P k, child ⊆ parent := by
    intro child hchild
    rcases cubicGridPartition_nesting (by linarith) hchild with ⟨parent, hparent, hsub⟩
    exact ⟨parent, hparent, hsub⟩
  have h_sum : (P (k + 1)).card = ∑ parent ∈ P k, (partitionChildren P k parent).card := by
    have h1 : P (k + 1) = (P k).biUnion (fun parent => partitionChildren P k parent) := by
      ext child
      simp only [Finset.mem_biUnion, partitionChildren, Finset.mem_filter]
      constructor
      · intro hchild
        rcases h_nesting child hchild with ⟨parent, hparent, hsub⟩
        exact ⟨parent, hparent, hchild, hsub⟩
      · rintro ⟨parent, hparent, hchild, _⟩
        exact hchild
    rw [h1]
    apply Finset.card_biUnion
    intro p1 hp1 p2 hp2 hne
    simp only [partitionChildren, Finset.disjoint_left]
    intro c hc1 hc2
    have h_sub1 : c ⊆ p1 := (Finset.mem_filter.mp hc1).2
    have h_sub2 : c ⊆ p2 := (Finset.mem_filter.mp hc2).2
    have h_disj : Disjoint p1 p2 := cubicGridPartition_disjoint hp1 hp2 hne
    have h_c_nonempty : c.Nonempty := by
      have h_in_P : c ∈ P (k + 1) := (Finset.mem_filter.mp hc1).1
      exact (cubicGridPartition_cell_nonempty_subset h_in_P).1
    rcases h_c_nonempty with ⟨x, hx⟩
    exact Finset.disjoint_left.mp h_disj (h_sub1 hx) (h_sub2 hx)
  have h_final : (P (k + 1)).card ≤ base ^ 3 * (P k).card := by
    calc
      (P (k + 1)).card
        = ∑ parent ∈ P k, (partitionChildren P k parent).card := h_sum
      _ ≤ ∑ parent ∈ P k, base ^ 3 := by
          apply Finset.sum_le_sum
          intro parent hparent
          exact cubic_grid_child_bound_tight hbase parent hparent
      _ = (P k).card * base ^ 3 := by
          simp [Finset.sum_const]
          <;> ring
      _ = base ^ 3 * (P k).card := by ring
  exact h_final

/-- Local branching dimension at level `i`. -/
def localDim (base : ℕ) (A : DiscreteSet 3) (i : ℕ) : ℝ :=
  Real.log ((cellCount base A (i + 1) : ℝ) / (cellCount base A i : ℝ)) / Real.log base

/-- Local dimension is in `[0, 3]`. -/
lemma localDim_bound {base A i} (hbase : 2 ≤ base) :
    0 ≤ localDim base A i ∧ localDim base A i ≤ 3 := by
  have hbase_gt_one : 1 < (base : ℝ) := by exact_mod_cast (show 1 < base from by linarith)
  have h_log_base_pos : 0 < Real.log base := Real.log_pos hbase_gt_one
  by_cases hA : A.Nonempty
  · -- Nonempty case
    have hA_nonempty : A.Nonempty := hA
    have h1 : (cellCount base A i : ℝ) > 0 := by
      have h_nonempty : (cubicGridPartition base i A).Nonempty := cubicGridPartition_nonempty hA_nonempty
      exact_mod_cast h_nonempty.card_pos
    have h2 : (cellCount base A i : ℝ) ≤ (cellCount base A (i + 1) : ℝ) := by
      exact_mod_cast cellCount_mono hbase
    have h3 : (cellCount base A (i + 1) : ℝ) ≤ base ^ 3 * (cellCount base A i : ℝ) := by
      exact_mod_cast cellCount_growth_bound hbase
    have h4 : 1 ≤ (cellCount base A (i + 1) : ℝ) / (cellCount base A i : ℝ) := by
      have h_pos : (cellCount base A i : ℝ) > 0 := h1
      calc
        1 = (cellCount base A i : ℝ) / (cellCount base A i : ℝ) := by field_simp [h_pos.ne']
        _ ≤ (cellCount base A (i + 1) : ℝ) / (cellCount base A i : ℝ) := by gcongr
    have h5 : (cellCount base A (i + 1) : ℝ) / (cellCount base A i : ℝ) ≤ (base : ℝ) ^ 3 := by
      have h_pos : (cellCount base A i : ℝ) > 0 := h1
      calc
        (cellCount base A (i + 1) : ℝ) / (cellCount base A i : ℝ)
          ≤ ((base : ℝ) ^ 3 * (cellCount base A i : ℝ)) / (cellCount base A i : ℝ) := by gcongr
        _ = (base : ℝ) ^ 3 := by field_simp [h_pos.ne'] <;> ring
    have h_log1 : 0 ≤ Real.log ((cellCount base A (i + 1) : ℝ) / (cellCount base A i : ℝ)) := by
      apply Real.log_nonneg
      exact h4
    have h_log2 : Real.log ((cellCount base A (i + 1) : ℝ) / (cellCount base A i : ℝ)) ≤ 3 * Real.log base := by
      calc
        Real.log ((cellCount base A (i + 1) : ℝ) / (cellCount base A i : ℝ))
          ≤ Real.log ((base : ℝ) ^ 3) := Real.log_le_log (by positivity) h5
        _ = 3 * Real.log base := by
          rw [Real.log_pow] <;> ring
    constructor
    · exact div_nonneg h_log1 h_log_base_pos.le
    · have h : localDim base A i ≤ 3 := by
        rw [localDim]
        have h' : Real.log ((cellCount base A (i + 1) : ℝ) / (cellCount base A i : ℝ)) / Real.log base ≤ 3 := by
          calc
            Real.log ((cellCount base A (i + 1) : ℝ) / (cellCount base A i : ℝ)) / Real.log base
              ≤ (3 * Real.log base) / Real.log base := by gcongr
            _ = 3 := by
              field_simp [h_log_base_pos.ne'] <;> ring
        exact h'
      exact h
  · -- Empty case
    have hA_empty : A = ∅ := by simpa [Finset.not_nonempty_iff_eq_empty] using hA
    have h_cell_zero : cellCount base A i = 0 := by
      simp [hA_empty, cubicGridPartition, cellCount]
    have h_cell1_zero : cellCount base A (i + 1) = 0 := by
      simp [hA_empty, cubicGridPartition, cellCount]
    have h_localDim_zero : localDim base A i = 0 := by
      simp [localDim, h_cell_zero, h_cell1_zero]
      <;> norm_num
    rw [h_localDim_zero]
    <;> norm_num

-- =====================================================================
-- Part 2: Telescoping weighted average
-- =====================================================================

/-- Telescoping sum of local dimensions equals log of total cell count ratio. -/
lemma localDim_sum {base A levels} (hbase : 2 ≤ base) :
    ∑ i : Fin levels, localDim base A i * (1 / (levels : ℝ)) =
      (Real.log ((cellCount base A levels : ℝ) / (cellCount base A 0 : ℝ))) /
        ((levels : ℝ) * Real.log base) := by
  have hbase_gt_one : 1 < (base : ℝ) := by exact_mod_cast (show 1 < base from by linarith)
  have h_log_base_pos : 0 < Real.log base := Real.log_pos hbase_gt_one
  by_cases hA : A.Nonempty
  · -- Nonempty case
    have hA_nonempty : A.Nonempty := hA
    have h_pos : ∀ k, (cellCount base A k : ℝ) > 0 := by
      intro k
      have h_nonempty : (cubicGridPartition base k A).Nonempty := cubicGridPartition_nonempty hA_nonempty
      exact_mod_cast h_nonempty.card_pos
    let g : ℕ → ℝ := fun k => Real.log ((cellCount base A (k + 1) : ℝ) / (cellCount base A k : ℝ))
    have h_main : ∑ i : Fin levels, g (i : ℕ) = Real.log ((cellCount base A levels : ℝ) / (cellCount base A 0 : ℝ)) := by
      have h_telescoping : ∀ n : ℕ, ∑ i ∈ Finset.range n, g i =
          Real.log ((cellCount base A n : ℝ) / (cellCount base A 0 : ℝ)) := by
        intro n
        induction n with
        | zero => simp [g]
        | succ n ih =>
          rw [Finset.sum_range_succ, ih]
          have h_pos0 : (cellCount base A 0 : ℝ) > 0 := h_pos 0
          have h_posn : (cellCount base A n : ℝ) > 0 := h_pos n
          have h_pos1 : (cellCount base A (n + 1) : ℝ) > 0 := h_pos (n + 1)
          have h_div : Real.log ((cellCount base A n : ℝ) / (cellCount base A 0 : ℝ)) + g n =
              Real.log ((cellCount base A (n + 1) : ℝ) / (cellCount base A 0 : ℝ)) := by
            dsimp only [g]
            have h_mul : ((cellCount base A n : ℝ) / (cellCount base A 0 : ℝ)) *
                ((cellCount base A (n + 1) : ℝ) / (cellCount base A n : ℝ)) =
                (cellCount base A (n + 1) : ℝ) / (cellCount base A 0 : ℝ) := by
              field_simp [h_pos0.ne', h_posn.ne'] <;> ring
            rw [←Real.log_mul (by positivity) (by positivity), h_mul]
          exact h_div
      have h_inj : Set.InjOn (fun (i : Fin levels) => (i : ℕ)) (Finset.univ : Finset (Fin levels)) := by
        intro a _ b _ h
        exact Fin.ext h
      have h_image : Finset.image (fun (i : Fin levels) => (i : ℕ)) Finset.univ = Finset.range levels := by
        ext x
        simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_range]
        constructor
        · rintro ⟨i, rfl⟩
          exact i.is_lt
        · intro hx
          refine ⟨⟨x, hx⟩, by simp⟩
      have h_eq : ∑ i : Fin levels, g (i : ℕ) = ∑ i ∈ Finset.range levels, g i := by
        rw [←Finset.sum_image h_inj, h_image] <;> rfl
      rw [h_eq, h_telescoping levels]
    calc
      ∑ i : Fin levels, localDim base A i * (1 / (levels : ℝ))
        = (1 / (levels : ℝ)) * ∑ i : Fin levels, localDim base A i := by
          have h_comm : ∑ i : Fin levels, localDim base A i * (1 / (levels : ℝ)) =
              ∑ i : Fin levels, (1 / (levels : ℝ)) * localDim base A i := by
            apply Finset.sum_congr rfl
            intro i _
            ring
          rw [h_comm, Finset.mul_sum]
      _ = (1 / (levels : ℝ)) * ∑ i : Fin levels, (g (i : ℕ) / Real.log base) := by
          apply congr_arg ((· * ·) (1 / (levels : ℝ)))
          apply Finset.sum_congr rfl
          intro i _
          rfl
      _ = (1 / (levels : ℝ)) * (1 / Real.log base) * ∑ i : Fin levels, g (i : ℕ) := by
          have h_sum_extract : ∑ i : Fin levels, (g (i : ℕ) / Real.log base) =
              (1 / Real.log base) * ∑ i : Fin levels, g (i : ℕ) := by
            have h_eq1 : ∑ i : Fin levels, (g (i : ℕ) / Real.log base) =
                ∑ i : Fin levels, ((1 / Real.log base) * g (i : ℕ)) := by
              apply Finset.sum_congr rfl
              intro i _
              ring
            rw [h_eq1, Finset.mul_sum]
          rw [h_sum_extract] <;> ring
      _ = (Real.log ((cellCount base A levels : ℝ) / (cellCount base A 0 : ℝ))) /
            ((levels : ℝ) * Real.log base) := by
          rw [h_main] <;> field_simp [h_log_base_pos.ne'] <;> ring
  · -- Empty case
    have hA_empty : A = ∅ := by simpa [Finset.not_nonempty_iff_eq_empty] using hA
    have h_cell_zero : ∀ k, cellCount base A k = 0 := by
      intro k
      simp [hA_empty, cubicGridPartition, cellCount]
    have h_localDim_zero : ∀ (i : Fin levels), localDim base A i = 0 := by
      intro i
      simp [localDim, h_cell_zero] <;> norm_num
    have h_lhs_zero : ∑ i : Fin levels, localDim base A i * (1 / (levels : ℝ)) = 0 := by
      rw [Finset.sum_congr rfl (fun i _ => by rw [h_localDim_zero i])] <;> simp
    have h_rhs_zero : (Real.log ((cellCount base A levels : ℝ) / (cellCount base A 0 : ℝ))) /
          ((levels : ℝ) * Real.log base) = 0 := by
      simp [h_cell_zero] <;> norm_num
    rw [h_lhs_zero, h_rhs_zero]

-- =====================================================================
-- Part 3: Scale weights
-- =====================================================================

/-- Uniform scale weights from 0 to 1. -/
def scaleWeight (levels : ℕ) (i : Fin (levels + 1)) : ℝ :=
  (i : ℝ) / (levels : ℝ)

lemma scaleWeight_zero {levels} : scaleWeight levels 0 = 0 := by
  simp [scaleWeight]

lemma scaleWeight_last {levels} [NeZero levels] :
    scaleWeight levels (Fin.last levels) = 1 := by
  simp [scaleWeight, Fin.last]
  <;> field_simp <;> ring

lemma scaleWeight_strictMono {levels} {i : Fin levels} :
    scaleWeight levels i.castSucc < scaleWeight levels i.succ := by
  have hlevels_pos' : 0 < levels := by
    have h : i.val < levels := i.is_lt
    omega
  have hlevels_pos : (0 : ℝ) < (levels : ℝ) := by exact_mod_cast hlevels_pos'
  have h_lt : (i : ℝ) < (i.succ : ℝ) := by
    have h1 : (i.succ : ℝ) = (i : ℝ) + 1 := by
      simp [Fin.val_succ] <;> norm_cast
    rw [h1] <;> linarith
  simpa [scaleWeight, Fin.castSucc, Fin.succ] using
    div_lt_div_of_pos_right h_lt hlevels_pos

end Kakeya.Assouad
