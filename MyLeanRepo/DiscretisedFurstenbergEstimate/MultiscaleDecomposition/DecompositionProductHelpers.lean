module

/-
  Product and sum helper lemmas for the multiscale decomposition.

  Provides:
  - Product of real powers conversion to single power
  - Finset/List sum conversion lemmas
  - Bad sum and structured slope sum equalities
  - Interval count and sum length bounds
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.MultiscaleDecomposition.BlockConversion
public import MyLeanRepo.OSWPrelude

@[expose] public section

noncomputable section

open DirecretisedFurstenbergEstimate
open DirecretisedFurstenbergEstimate.MultiscaleDecomposition

namespace MultiscaleBlockConversion

/-- Product of real powers: product of base^{x_i} = base^{sum x_i}. -/
lemma prod_rpow_eq {α : Type*} [DecidableEq α] (s : Finset α) (x : α → ℝ)
    (base : ℝ) (hbase : 0 < base) :
    (∏ i ∈ s, Real.rpow base (x i)) = Real.rpow base (∑ i ∈ s, x i) := by
  have h : ∀ (t : Finset α), (∏ i ∈ t, Real.rpow base (x i)) = Real.rpow base (∑ i ∈ t, x i) := by
    intro t
    induction t using Finset.induction with
    | empty => simp
    | @insert a t ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha, ih]
      have h_add : Real.rpow base (x a + ∑ i ∈ t, x i) =
          Real.rpow base (x a) * Real.rpow base (∑ i ∈ t, x i) :=
        Real.rpow_add hbase (x a) (∑ i ∈ t, x i)
      exact h_add.symm
  exact h s

/-- Bad sum upper bound:
    If K ≤ 1/τ₀ and m ≥ 4/(η*τ₀), then 2K ≤ η*m. -/
lemma twoK_le_eta_m {m K : ℕ} {η τ₀ : ℝ}
    (hK_bound : (K : ℝ) ≤ 1 / τ₀) (hτ₀_pos : 0 < τ₀) (hη_pos : 0 < η)
    (hm0 : 4 / (η * τ₀) ≤ (m : ℝ)) :
    2 * (K : ℝ) ≤ η * (m : ℝ) := by
  have h3 : 2 * (K : ℝ) ≤ 2 / τ₀ := by
    calc 2 * (K : ℝ)
      ≤ 2 * (1 / τ₀) := by gcongr
      _ = 2 / τ₀ := by ring
  have h4 : 2 / τ₀ ≤ η * (m : ℝ) / 2 := by
    have h6 : 0 < η * τ₀ := mul_pos hη_pos hτ₀_pos
    calc 2 / τ₀
      = (4 / (η * τ₀)) * (η / 2) := by field_simp [h6.ne'] <;> ring
      _ ≤ (m : ℝ) * (η / 2) := by gcongr
      _ = η * (m : ℝ) / 2 := by ring
  linarith

/-- Sum of lengths of pairwise interior-disjoint intervals in [0, m] is ≤ m. -/
lemma fin_interval_sum_len_le {K : ℕ} {I : Fin K → ℝ × ℝ} {m : ℝ}
    (hm : 0 ≤ m)
    (h_disj : ∀ i j : Fin K, i ≠ j →
      Disjoint (Set.Ioo (I i).1 (I i).2) (Set.Ioo (I j).1 (I j).2))
    (h_bound : ∀ i, 0 ≤ (I i).1 ∧ (I i).1 < (I i).2 ∧ (I i).2 ≤ m) :
    ∑ i : Fin K, ((I i).2 - (I i).1) ≤ m := by
  let s : Finset (Fin K) := Finset.univ
  let f : Fin K → Set ℝ := fun i => Set.Ioo (I i).1 (I i).2
  have h_meas : ∀ i ∈ s, MeasurableSet (f i) := fun i _ => measurableSet_Ioo
  have h_disj' : Set.PairwiseDisjoint (↑s) f := by
    intro i _ j _ hne
    exact h_disj i j hne
  have h_union : (⋃ i ∈ s, f i) ⊆ Set.Icc (0 : ℝ) m := by
    intro x hx
    have h_exists : ∃ i ∈ s, x ∈ f i := by simpa using hx
    rcases h_exists with ⟨i, _, hxi⟩
    have h1 : (I i).1 < x := hxi.1
    have h2 : x < (I i).2 := hxi.2
    have h3 : 0 ≤ (I i).1 := (h_bound i).1
    have h4 : (I i).2 ≤ m := (h_bound i).2.2
    exact ⟨by linarith, by linarith⟩
  have h_sum_vol : MeasureTheory.volume (⋃ i ∈ s, f i) = ∑ i ∈ s, MeasureTheory.volume (f i) :=
    MeasureTheory.measure_biUnion_finset h_disj' h_meas
  have h_mono : MeasureTheory.volume (⋃ i ∈ s, f i) ≤ MeasureTheory.volume (Set.Icc (0 : ℝ) m) :=
    MeasureTheory.measure_mono h_union
  have h_vol_Icc : MeasureTheory.volume (Set.Icc (0 : ℝ) m) = ENNReal.ofReal m := by
    rw [Real.volume_Icc] <;> simp [hm]
  have h_vol_Ioo : ∀ i, MeasureTheory.volume (f i) = ENNReal.ofReal ((I i).2 - (I i).1) := by
    intro i
    have h : (I i).1 ≤ (I i).2 := by linarith [(h_bound i).2.1]
    rw [Real.volume_Ioo] <;> simp [h]
  have h_nonneg : ∀ i ∈ s, 0 ≤ (I i).2 - (I i).1 := by
    intro i _
    have h : (I i).1 < (I i).2 := (h_bound i).2.1
    linarith
  have h_sum_real : ∑ i ∈ s, MeasureTheory.volume (f i) =
      ENNReal.ofReal (∑ i ∈ s, ((I i).2 - (I i).1)) := by
    rw [Finset.sum_congr rfl (fun i _ => h_vol_Ioo i)]
    rw [ENNReal.ofReal_sum_of_nonneg h_nonneg]
  rw [h_sum_vol, h_sum_real, h_vol_Icc] at h_mono
  have h_mono' : ENNReal.ofReal (∑ i ∈ s, ((I i).2 - (I i).1)) ≤ ENNReal.ofReal m := h_mono
  exact (ENNReal.ofReal_le_ofReal_iff (by linarith)).mp h_mono'

/-- Number of intervals bound: K ≤ 1/τ₀ from pairwise disjointness and min length τ₀*m. -/
lemma interval_count_le {K : ℕ} {I : Fin K → ℝ × ℝ} {m τ₀ : ℝ}
    (hm_pos : 0 < m) (hτ₀_pos : 0 < τ₀)
    (h_disj : ∀ i j : Fin K, i ≠ j →
      Disjoint (Set.Ioo (I i).1 (I i).2) (Set.Ioo (I j).1 (I j).2))
    (h_bound : ∀ i, 0 ≤ (I i).1 ∧ (I i).1 < (I i).2 ∧ (I i).2 ≤ m ∧ τ₀ * m ≤ (I i).2 - (I i).1) :
    (K : ℝ) ≤ 1 / τ₀ := by
  have h_sum_le : ∑ i : Fin K, ((I i).2 - (I i).1) ≤ m :=
    fin_interval_sum_len_le (by linarith) h_disj
      (fun i => let h := h_bound i; ⟨h.1, h.2.1, h.2.2.1⟩)
  have h_min : ∀ i : Fin K, τ₀ * m ≤ (I i).2 - (I i).1 := fun i => (h_bound i).2.2.2
  have h_sum_ge : ∑ i : Fin K, ((I i).2 - (I i).1) ≥ (K : ℝ) * (τ₀ * m) := by
    have h : ∑ i : Fin K, ((I i).2 - (I i).1) ≥ ∑ i : Fin K, (τ₀ * m) := by
      apply Finset.sum_le_sum
      intro i _
      exact h_min i
    simpa [Finset.sum_const] using h
  have h_final : (K : ℝ) * (τ₀ * m) ≤ m := by linarith
  have h : (K : ℝ) * τ₀ ≤ 1 := by nlinarith
  have h6 : 0 < τ₀ := hτ₀_pos
  calc
    (K : ℝ) = (K : ℝ) * τ₀ / τ₀ := by field_simp [h6.ne'] <;> ring
    _ ≤ 1 / τ₀ := by gcongr

/-- Sum over Fin l.length of f(l.get i) equals (List.map f l).sum. -/
lemma fin_sum_map_eq_list_sum {α β : Type*} [AddCommMonoid β] {l : List α} {f : α → β} :
    ∑ i : Fin l.length, f (l.get i) = (l.map f).sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
    have h_main : ∑ i : Fin (t.length + 1), f ((a :: t).get i) =
        f a + ∑ i : Fin t.length, f (t.get i) := by
      rw [Fin.sum_univ_succ]
      <;> simp [List.get]
      <;> rfl
    calc
      ∑ i : Fin (t.length + 1), f ((a :: t).get i)
        = f a + ∑ i : Fin t.length, f (t.get i) := h_main
      _ = f a + (t.map f).sum := by rw [ih]
      _ = (List.map f (a :: t)).sum := by simp [List.map_cons, List.sum_cons]

/-- Filtered sum over Fin l.length equals (l.filter p |>.map f).sum. -/
lemma fin_sum_filter_eq_list_sum {α β : Type*} [AddCommMonoid β] {l : List α}
    {p : α → Bool} {f : α → β} :
    ∑ i ∈ (Finset.univ.filter (fun i : Fin l.length => p (l.get i))), f (l.get i) =
    ((l.filter p).map f).sum := by
  let g : α → β := fun x => if p x then f x else 0
  have h4 : ∀ (l : List α), (l.map g).sum = ((l.filter p).map f).sum := by
    intro l
    induction l with
    | nil => simp [g]
    | cons a t ih =>
      by_cases hpa : p a
      · have h5 : ((a :: t).map g).sum = f a + (t.map g).sum := by
          simp [g, hpa, List.map_cons, List.sum_cons]
        rw [h5, ih]
        <;> simp [List.filter, hpa, List.map_cons, List.sum_cons]
      · have h5 : ((a :: t).map g).sum = (t.map g).sum := by
          simp [g, hpa, List.map_cons, List.sum_cons]
        rw [h5, ih]
        <;> simp [List.filter, hpa]
  have h1 : ∑ i : Fin l.length, g (l.get i) = (l.map g).sum :=
    fin_sum_map_eq_list_sum (f := g)
  have h2 : ∑ i : Fin l.length, g (l.get i) =
      ∑ i ∈ (Finset.univ.filter (fun i : Fin l.length => p (l.get i))), f (l.get i) := by
    have h3 : ∑ i : Fin l.length, g (l.get i) =
        ∑ i : Fin l.length, (if p (l.get i) then f (l.get i) else 0) := by
      apply Finset.sum_congr rfl
      intro i _
      rfl
    rw [h3]
    have h_sum_ite : ∑ i : Fin l.length, (if p (l.get i) then f (l.get i) else 0) =
        ∑ i ∈ (Finset.univ.filter (fun i : Fin l.length => p (l.get i))), f (l.get i) +
        ∑ i ∈ (Finset.univ.filter (fun i : Fin l.length => ¬p (l.get i))), (0 : β) := by
      rw [Finset.sum_ite]
      <;> rfl
    rw [h_sum_ite]
    simp
  rw [←h2, h1, h4 l]

/-- Sum of block lengths over bad indices = total - structured. -/
lemma bad_sum_eq_total_minus_struct {blocks : List (ℕ × ℕ × Bool × ℝ)}
    (S B : Finset (Fin blocks.length))
    (h_univ : S ∪ B = Finset.univ)
    (h_disj : Disjoint S B)
    (hS : ∀ j : Fin blocks.length, j ∈ S ↔ isStruct (blocks.get j))
    (h_pos_len : ∀ b ∈ blocks, b.1 < b.2.1) :
    ∑ j ∈ B, (blockLen (blocks.get j) : ℝ) =
      (sumBlockLen blocks : ℝ) - (sumStructLen blocks : ℝ) := by
  let g : (ℕ × ℕ × Bool × ℝ) → ℝ := fun b => ↑(blockLen b)
  have h1 : ∑ j : Fin blocks.length, g (blocks.get j) = (sumBlockLen blocks : ℝ) := by
    have h_eq1 := @fin_sum_map_eq_list_sum _ _ _ blocks g
    rw [h_eq1]
    <;> simp [sumBlockLen, g]
    <;> rfl
  have hS' : S = Finset.univ.filter (fun j : Fin blocks.length => isStruct (blocks.get j)) := by
    ext j; simp [hS]
  have h2 : ∑ j ∈ S, g (blocks.get j) = (sumStructLen blocks : ℝ) := by
    rw [hS']
    have h_eq2 := @fin_sum_filter_eq_list_sum _ _ _ blocks isStruct g
    rw [h_eq2]
    <;> simp [sumStructLen, g]
    <;> rfl
  have h3 : ∑ j : Fin blocks.length, g (blocks.get j) =
      ∑ j ∈ S, g (blocks.get j) + ∑ j ∈ B, g (blocks.get j) := by
    rw [← Finset.sum_union h_disj, h_univ]
  linarith

/-- slopeLen b equals b.2.2.2 * blockLen b when structured, 0 otherwise. -/
lemma slopeLen_eq {b : ℕ × ℕ × Bool × ℝ} (hbl : b.1 ≤ b.2.1) :
    slopeLen b = if isStruct b then b.2.2.2 * (blockLen b : ℝ) else 0 := by
  have hcast : (blockLen b : ℝ) = (b.2.1 : ℝ) - (b.1 : ℝ) := by
    simp [blockLen, Nat.cast_sub hbl] <;> norm_cast
  unfold slopeLen
  congr 1
  · rw [hcast]

/-- Sum of slope-weighted lengths over structured indices = sumSlopeLen. -/
lemma struct_slope_sum_eq {blocks : List (ℕ × ℕ × Bool × ℝ)}
    (S : Finset (Fin blocks.length))
    (hS : ∀ j : Fin blocks.length, j ∈ S ↔ isStruct (blocks.get j))
    (h_pos_len : ∀ b ∈ blocks, b.1 < b.2.1)
    (t_j : ℕ → ℝ)
    (htj : ∀ j : Fin blocks.length, t_j j.val = (blocks.get j).2.2.2) :
    ∑ j ∈ S, t_j j.val * (blockLen (blocks.get j) : ℝ) =
      (sumSlopeLen blocks : ℝ) := by
  have hS' : S = Finset.univ.filter (fun j : Fin blocks.length => isStruct (blocks.get j)) := by
    ext j; simp [hS]
  let g : (ℕ × ℕ × Bool × ℝ) → ℝ := fun b =>
    if isStruct b then b.2.2.2 * (blockLen b : ℝ) else 0
  have h_eq_slope : ∀ b ∈ blocks, slopeLen b = g b := by
    intro b hb
    have hbl : b.1 ≤ b.2.1 := le_of_lt (h_pos_len b hb)
    rw [slopeLen_eq hbl]
    <;> rfl
  have h5 : ∀ j : Fin blocks.length, g (blocks.get j) =
      if isStruct (blocks.get j) then t_j j.val * (blockLen (blocks.get j) : ℝ) else 0 := by
    intro j
    have hbl : (blocks.get j).1 ≤ (blocks.get j).2.1 :=
      le_of_lt (h_pos_len (blocks.get j) (blocks.get_mem j))
    have h6 : t_j j.val = (blocks.get j).2.2.2 := htj j
    simp [g, h6, slopeLen_eq hbl]
  have h_main_eq : ∑ j ∈ S, t_j j.val * (blockLen (blocks.get j) : ℝ) =
      ∑ j : Fin blocks.length, g (blocks.get j) := by
    rw [hS']
    have h_sum_ite : ∑ j : Fin blocks.length, (if isStruct (blocks.get j) then t_j j.val * (blockLen (blocks.get j) : ℝ) else 0) =
        ∑ j ∈ (Finset.univ.filter (fun j : Fin blocks.length => isStruct (blocks.get j))),
          t_j j.val * (blockLen (blocks.get j) : ℝ) := by
      rw [Finset.sum_ite]
      <;> simp
    have h_congr : ∑ j : Fin blocks.length, g (blocks.get j) =
        ∑ j : Fin blocks.length, (if isStruct (blocks.get j) then t_j j.val * (blockLen (blocks.get j) : ℝ) else 0) := by
      apply Finset.sum_congr rfl
      intro j _
      exact h5 j
    rw [h_congr, h_sum_ite]
  have h1 : ∑ j : Fin blocks.length, slopeLen (blocks.get j) = (sumSlopeLen blocks : ℝ) := by
    have h_eq1 := @fin_sum_map_eq_list_sum _ _ _ blocks slopeLen
    rw [h_eq1]
    <;> simp [sumSlopeLen]
    <;> rfl
  have h2 : ∑ j : Fin blocks.length, g (blocks.get j) = ∑ j : Fin blocks.length, slopeLen (blocks.get j) := by
    apply Finset.sum_congr rfl
    intro j _
    exact (h_eq_slope (blocks.get j) (blocks.get_mem j)).symm
  rw [h_main_eq, h2, h1]

end MultiscaleBlockConversion
