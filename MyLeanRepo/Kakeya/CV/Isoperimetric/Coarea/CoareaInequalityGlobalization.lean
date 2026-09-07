import MyLeanRepo.Kakeya.CV.Isoperimetric.InnerMinkowski.Basic
import Mathlib.Geometry.Euclidean.Volume.Measure
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.Tactic

/-!
# Countable Assembly of the Local Coarea Inequality

Given a countable open cover of a measurable set `A` and a local coarea
inequality on each cover element, assemble the global coarea inequality
via disjointification.

This is the **inequality** analogue of raven's `countable_coarea_assembly`
(which proves an equality). For inequalities, we only need:
1. Disjointify the cover
2. Apply local inequality to each piece
3. Sum LHS by countable additivity of volume
4. Sum RHS: since pieces are disjoint, `μHE` of the union equals the sum
   (countable additivity), so `lintegral_tsum` gives the global RHS exactly.

## Proof sketch

Let `U i` be a countable open cover of `A`.
Define `V i = U i \\ ⋃_{j<i} U j` and `S i = A ∩ V i`.
Then `S i` are pairwise disjoint measurable sets with `⋃ S i = A`.

For each `i`, `S i ⊆ U i`, so the local inequality gives:
  `volume(S_i-slice) ≤ (1+ε) * ∫ μHE(S_i-level-set)`

Summing LHS:
  `volume(A-slice) = ∑ volume(S_i-slice)`

Summing RHS:
  `∑ ∫ μHE(S_i-level-set) = ∫ ∑ μHE(S_i-level-set)` (lintegral_tsum)
  `= ∫ μHE(A-level-set)` (countable additivity of μHE on disjoint sets)

Hence the global inequality.
-/

open MeasureTheory Metric Set ENNReal
open scoped MeasureTheory

namespace Geometry

variable {n : ℕ} [Nonempty (Fin n)]

/-- Countable sum of lintegrals ≤ lintegral of countable sum,
without any measurability assumptions. -/
lemma tsum_lintegral_le {α : Type*} {m : MeasurableSpace α} {μ : Measure α}
    {f : ℕ → α → ENNReal} :
    ∑' i, ∫⁻ a, f i a ∂μ ≤ ∫⁻ a, ∑' i, f i a ∂μ := by
  have h : ∀ (s : Finset ℕ), ∑ i ∈ s, ∫⁻ a, f i a ∂μ ≤ ∫⁻ a, ∑' i, f i a ∂μ := by
    intro s
    have h1 : ∑ i ∈ s, ∫⁻ a, f i a ∂μ ≤ ∫⁻ a, ∑ i ∈ s, f i a ∂μ := by
      induction s using Finset.induction with
      | empty => simp
      | @insert i s hi ih =>
        have h_step : ∑ j ∈ insert i s, ∫⁻ a, f j a ∂μ ≤ ∫⁻ a, ∑ j ∈ insert i s, f j a ∂μ := by
          calc
            ∑ j ∈ insert i s, ∫⁻ a, f j a ∂μ
              = ∫⁻ a, f i a ∂μ + ∑ j ∈ s, ∫⁻ a, f j a ∂μ := by
                rw [Finset.sum_insert hi] <;> ring
            _ ≤ ∫⁻ a, f i a ∂μ + ∫⁻ a, ∑ j ∈ s, f j a ∂μ := by
                exact add_le_add_right ih (∫⁻ a, f i a ∂μ)
            _ ≤ ∫⁻ a, f i a + ∑ j ∈ s, f j a ∂μ := le_lintegral_add (f i) (fun a => ∑ j ∈ s, f j a)
            _ = ∫⁻ a, ∑ j ∈ insert i s, f j a ∂μ := by
                congr with a
                rw [Finset.sum_insert hi] <;> ring
        exact h_step
    have h2 : ∀ a, (∑ i ∈ s, f i a) ≤ ∑' i, f i a := by
      intro a
      exact ENNReal.sum_le_tsum s
    have h3 : ∫⁻ a, ∑ i ∈ s, f i a ∂μ ≤ ∫⁻ a, ∑' i, f i a ∂μ :=
      lintegral_mono h2
    exact h1.trans h3
  have h4 : ∑' i, ∫⁻ a, f i a ∂μ = ⨆ (s : Finset ℕ), ∑ i ∈ s, ∫⁻ a, f i a ∂μ := by
    rw [ENNReal.tsum_eq_iSup_sum]
  rw [h4]
  exact iSup_le h

/-- **Countable assembly of the local coarea inequality.**

Given a countable open cover `{U i}` of `A` and a local coarea inequality
on each `U i` (valid for all measurable subsets), assemble the global
coarea inequality on `A`. -/
lemma countable_coarea_inequality_assembly
    {A : Set (E n)} (hA : MeasurableSet A)
    (f : E n → ℝ) (hf : Measurable f)
    (ε : ℝ) (hε : 0 < ε)
    (a b : ℝ) (hab : a < b)
    (U : ℕ → Set (E n))
    (hU_open : ∀ i, IsOpen (U i))
    (h_cover : A ⊆ ⋃ i, U i)
    (h_local : ∀ i (C : Set (E n)), MeasurableSet C → C ⊆ U i →
      volume {x ∈ C | a < f x ∧ f x ≤ b} ≤
        ENNReal.ofReal (1 + ε) * ∫⁻ s in Set.Ioc a b,
          μHE[n - 1] {x ∈ C | f x = s}) :
    volume {x ∈ A | a < f x ∧ f x ≤ b} ≤
      ENNReal.ofReal (1 + ε) * ∫⁻ s in Set.Ioc a b,
        μHE[n - 1] {x ∈ A | f x = s} := by
  classical

  -- Step 1: Disjointify the cover
  let V : ℕ → Set (E n) := fun i => U i \ ⋃ j ∈ Finset.range i, U j
  let S : ℕ → Set (E n) := fun i => A ∩ V i

  have hV_meas : ∀ i, MeasurableSet (V i) := by
    intro i
    have h1 : MeasurableSet (U i) := (hU_open i).measurableSet
    have h2 : MeasurableSet (⋃ j ∈ Finset.range i, U j) := by
      apply MeasurableSet.biUnion
      · exact Finset.countable_toSet _
      · intro j _; exact (hU_open j).measurableSet
    exact h1.diff h2

  have hS_meas : ∀ i, MeasurableSet (S i) :=
    fun i => hA.inter (hV_meas i)

  have hV_sub : ∀ i, V i ⊆ U i := by
    intro i x hx; exact hx.1

  have hS_sub_U : ∀ i, S i ⊆ U i := by
    intro i x hx; exact hV_sub i hx.2

  have h_disj : Pairwise (fun i j : ℕ => Disjoint (V i) (V j)) := by
    intro i j hne
    by_cases h : i < j
    · have h6 : V j ⊆ (U j) \ U i := by
        intro x hx
        have h7 : x ∈ U j := hx.1
        have h8 : x ∉ ⋃ k ∈ Finset.range j, U k := hx.2
        have h9 : x ∉ U i := by
          intro h10
          have h11 : x ∈ ⋃ k ∈ Finset.range j, U k := by
            apply Set.mem_iUnion₂.mpr
            exact ⟨i, Finset.mem_range.mpr h, h10⟩
          exact h8 h11
        exact ⟨h7, h9⟩
      have h7 : Disjoint (V i) ((U j) \ U i) := by
        rw [Set.disjoint_left]
        intro x hxi hxj
        exact hxj.2 (hV_sub i hxi)
      exact h7.mono_right h6
    · have h' : j < i := by omega
      have h6 : V i ⊆ (U i) \ U j := by
        intro x hx
        have h7 : x ∈ U i := hx.1
        have h8 : x ∉ ⋃ k ∈ Finset.range i, U k := hx.2
        have h9 : x ∉ U j := by
          intro h10
          have h11 : x ∈ ⋃ k ∈ Finset.range i, U k := by
            apply Set.mem_iUnion₂.mpr
            exact ⟨j, Finset.mem_range.mpr h', h10⟩
          exact h8 h11
        exact ⟨h7, h9⟩
      have h7 : Disjoint (V j) ((U i) \ U j) := by
        rw [Set.disjoint_left]
        intro x hxj hxi
        exact hxi.2 (hV_sub j hxj)
      exact (h7.mono_right h6).symm

  have hS_disj : Pairwise (fun i j : ℕ => Disjoint (S i) (S j)) := by
    intro i j hne
    have h : Disjoint (V i) (V j) := h_disj hne
    exact h.mono (fun x hx => hx.2) (fun x hx => hx.2)

  have h_union_V : (⋃ i, V i) = ⋃ i, U i := by
    ext x
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨i, hi⟩; exact ⟨i, hV_sub i hi⟩
    · intro h
      let P : ℕ → Prop := fun j => x ∈ U j
      have hP : ∃ j, P j := by rcases h with ⟨i, hi⟩; exact ⟨i, hi⟩
      let k : ℕ := Nat.find hP
      have hk : P k := Nat.find_spec hP
      have hmin : ∀ j < k, ¬ P j := by intro j hj; exact Nat.find_min hP hj
      have hk2 : x ∈ V k := by
        constructor
        · exact hk
        · intro h2
          rcases Set.mem_iUnion₂.mp h2 with ⟨j, hj_range, hj_U⟩
          have h_j_lt_k : j < k := Finset.mem_range.mp hj_range
          exact hmin j h_j_lt_k hj_U
      exact ⟨k, hk2⟩

  have hS_union : (⋃ i, S i) = A := by
    ext x
    constructor
    · intro hx
      rcases Set.mem_iUnion.mp hx with ⟨i, hi⟩
      exact hi.1
    · intro hx
      have h2 : x ∈ ⋃ i, V i := by
        have h3 : x ∈ ⋃ i, U i := h_cover hx
        rw [←h_union_V] at h3
        exact h3
      rcases Set.mem_iUnion.mp h2 with ⟨idx, hidx⟩
      have h3 : x ∈ S idx := ⟨hx, hidx⟩
      exact Set.mem_iUnion.mpr ⟨idx, h3⟩

  -- Step 2: Define slice sets
  let A_slice : Set (E n) := {y ∈ A | a < f y ∧ f y ≤ b}
  let S_slice : ℕ → Set (E n) := fun i => {y ∈ S i | a < f y ∧ f y ≤ b}

  have hS_slice_meas : ∀ i, MeasurableSet (S_slice i) := by
    intro i
    have h1 : MeasurableSet (S i) := hS_meas i
    have h2 : MeasurableSet {y : E n | a < f y} :=
      measurableSet_Ioi.preimage hf
    have h3 : MeasurableSet {y : E n | f y ≤ b} :=
      measurableSet_Iic.preimage hf
    exact h1.inter (h2.inter h3)

  have hS_slice_disj : Pairwise (fun i j => Disjoint (S_slice i) (S_slice j)) := by
    intro i j hne
    have h : Disjoint (S i) (S j) := hS_disj hne
    exact h.mono (fun x hx => hx.1) (fun x hx => hx.1)

  have hS_slice_union : (⋃ i, S_slice i) = A_slice := by
    ext x
    simp only [Set.mem_iUnion, S_slice, A_slice, Set.mem_setOf_eq]
    constructor
    · rintro ⟨i, hxi⟩
      exact ⟨hxi.1.1, hxi.2⟩
    · rintro ⟨hxA, hxf⟩
      have h2 : x ∈ ⋃ i, S i := by rw [hS_union]; exact hxA
      rcases Set.mem_iUnion.mp h2 with ⟨i, hxi⟩
      exact ⟨i, ⟨hxi, hxf⟩⟩

  -- Step 3: LHS = sum of volumes over disjoint slices
  have h_lhs : volume A_slice = ∑' i, volume (S_slice i) := by
    have h_eq : volume A_slice = volume (⋃ i, S_slice i) := by rw [hS_slice_union]
    rw [h_eq]
    exact MeasureTheory.measure_iUnion hS_slice_disj hS_slice_meas

  -- Step 4: Apply local inequality to each S i
  have h_each : ∀ i, volume (S_slice i) ≤
      ENNReal.ofReal (1 + ε) * ∫⁻ s in Set.Ioc a b,
        μHE[n - 1] {y ∈ S i | f y = s} := by
    intro i
    have h1 : S_slice i = {y ∈ S i | a < f y ∧ f y ≤ b} := by rfl
    rw [h1]
    exact h_local i (S i) (hS_meas i) (hS_sub_U i)

  -- Step 5: RHS - level set measures and countable additivity
  let level_slices : ℕ → ℝ → Set (E n) := fun i s => {y ∈ S i | f y = s}

  have h_level_meas : ∀ i s, MeasurableSet (level_slices i s) := by
    intro i s
    have h1 : MeasurableSet (S i) := hS_meas i
    have h2 : MeasurableSet {y : E n | f y = s} :=
      isClosed_singleton.measurableSet.preimage hf
    exact h1.inter h2

  have h_level_disj : ∀ s, Pairwise (fun i j => Disjoint (level_slices i s) (level_slices j s)) := by
    intro s i j hne
    have h : Disjoint (S i) (S j) := hS_disj hne
    exact h.mono (fun x hx => hx.1) (fun x hx => hx.1)

  have h_union_levels : ∀ s, (⋃ i, level_slices i s) = {y ∈ A | f y = s} := by
    intro s
    ext x
    simp only [Set.mem_iUnion, level_slices, Set.mem_setOf_eq]
    constructor
    · rintro ⟨i, hxi⟩
      exact ⟨hxi.1.1, hxi.2⟩
    · rintro ⟨hxA, hxf⟩
      have h2 : x ∈ ⋃ i, S i := by rw [hS_union]; exact hxA
      rcases Set.mem_iUnion.mp h2 with ⟨i, hxi⟩
      exact ⟨i, ⟨hxi, hxf⟩⟩

  have h_μHE_union : ∀ s, μHE[n - 1] (⋃ i, level_slices i s) =
      ∑' i, μHE[n - 1] (level_slices i s) := by
    intro s
    exact MeasureTheory.measure_iUnion (h_level_disj s) (h_level_meas · s)

  have h_rhs_le : ∑' i, ∫⁻ s in Set.Ioc a b, μHE[n - 1] (level_slices i s) ≤
      ∫⁻ s in Set.Ioc a b, μHE[n - 1] {y ∈ A | f y = s} := by
    have h1 : (fun s : ℝ => μHE[n - 1] {y ∈ A | f y = s}) =
        fun s : ℝ => ∑' i, μHE[n - 1] (level_slices i s) := by
      funext s
      have h2 : {y ∈ A | f y = s} = ⋃ i, level_slices i s := (h_union_levels s).symm
      rw [h2, h_μHE_union s]
    rw [h1]
    exact tsum_lintegral_le

  -- Step 6: Combine
  calc volume A_slice
      = ∑' i, volume (S_slice i) := h_lhs
    _ ≤ ∑' i, (ENNReal.ofReal (1 + ε) * ∫⁻ s in Set.Ioc a b, μHE[n - 1] (level_slices i s)) := by
        exact ENNReal.tsum_le_tsum h_each
    _ = ENNReal.ofReal (1 + ε) * ∑' i, (∫⁻ s in Set.Ioc a b, μHE[n - 1] (level_slices i s)) := by
        rw [ENNReal.tsum_mul_left]
    _ ≤ ENNReal.ofReal (1 + ε) * ∫⁻ s in Set.Ioc a b, μHE[n - 1] {y ∈ A | f y = s} := by
        exact mul_le_mul_left' h_rhs_le _

end Geometry
