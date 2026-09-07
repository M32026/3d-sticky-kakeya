import MyLeanRepo.Kakeya.Assouad.WZ1.SegmentConstruction

/-!
# Telescoping sum for WZ1 Corollary 26 segment corrections

At an active height z, the multiscale segment value equals the affine function
of the trapezoid at the finest level containing z.
-/

namespace Kakeya.Assouad

open Set

section

variable {delta : ℝ}
  {F : Kakeya.Streamlined.TubeFamily delta}
  {Y : Kakeya.Streamlined.TubeShading F}
  {sourceSlope : ℝ → ℝ}
  {hierarchyLoss : ℝ}
  (hierarchy : WZ1Corollary26AnchoredHierarchyData Y sourceSlope hierarchyLoss)

/-- At most one trapezoid at a given level can contain z in its core. -/
lemma unique_containing_trapezoid_at_height
    (hdelta : 0 < delta)
    (level : Fin hierarchy.levelCount)
    {z : ℝ}
    {t1 t2 : WZ1VerticalTrapezoid}
    (ht1 : t1 ∈ hierarchy.trapezoids level)
    (ht2 : t2 ∈ hierarchy.trapezoids level)
    (hz1 : z ∈ t1.core) (hz2 : z ∈ t2.core) :
    t1 = t2 := by
  by_contra hne
  have hlc : 2 ≤ hierarchy.levelCount := hierarchy.levelCount_two
  have hN_pos : 0 < hierarchy.levelCount := by omega
  have hexp_pos : 0 < (((level : ℕ) + 1 : ℝ) / (hierarchy.levelCount : ℝ)) := by
    have h1 : 0 < (hierarchy.levelCount : ℝ) := by exact_mod_cast hN_pos
    positivity
  let exp : ℝ := (((level : ℕ) + 1 : ℝ) / (hierarchy.levelCount : ℝ))
  have hscale_pos : 0 < Real.sqrt (wz1Corollary26Scale delta hierarchy.levelCount level) :=
    Real.sqrt_pos.mpr (Real.rpow_pos_of_pos hdelta exp)
  have h := hierarchy.separated_cores level t1 ht1 t2 ht2 hne z hz1 z hz2
  simp at h
  linarith

/-- There exists a unique trapezoid at each level containing an active height. -/
lemma exists_unique_containing_trapezoid
    (hdelta : 0 < delta)
    (level : Fin hierarchy.levelCount)
    {z : ℝ} (hz : z ∈ Icc (-1 : ℝ) 1)
    (hactive : horizontalSlice Y.union z ≠ ∅) :
    ∃! (t : WZ1VerticalTrapezoid),
      t ∈ hierarchy.trapezoids level ∧ z ∈ t.core := by
  rcases hierarchy.active_height_coverage level z hz hactive with
    ⟨t, ht, hzt⟩
  refine' ⟨t, ⟨ht, hzt⟩, _⟩
  intro t' ht'
  exact unique_containing_trapezoid_at_height hierarchy hdelta level
    ht'.1 ht ht'.2 hzt

end

section Telescoping

variable {delta : ℝ}
  {F : Kakeya.Streamlined.TubeFamily delta}
  {Y : Kakeya.Streamlined.TubeShading F}
  {sourceSlope : ℝ → ℝ}
  {hierarchyLoss : ℝ}
  (hierarchy : WZ1Corollary26AnchoredHierarchyData Y sourceSlope hierarchyLoss)
  (hdelta : 0 < delta)
  {z : ℝ}
  (hz : z ∈ Icc (-1 : ℝ) 1)
  (hactive : horizontalSlice Y.union z ≠ ∅)

/-- The unique trapezoid containing z at natural-number level n. -/
noncomputable def containingTrapezoid (n : ℕ) (hn : n < hierarchy.levelCount) :
    WZ1VerticalTrapezoid :=
  Classical.choose
    (exists_unique_containing_trapezoid hierarchy hdelta ⟨n, hn⟩ hz hactive)

lemma containingTrapezoid_spec (n : ℕ) (hn : n < hierarchy.levelCount) :
    containingTrapezoid hierarchy hdelta hz hactive n hn ∈
      hierarchy.trapezoids ⟨n, hn⟩ ∧
    z ∈ (containingTrapezoid hierarchy hdelta hz hactive n hn).core :=
  (Classical.choose_spec
    (exists_unique_containing_trapezoid hierarchy hdelta ⟨n, hn⟩ hz hactive)).1

/-- Parent chain: the parent of T_n is T_{n-1}. -/
lemma parent_chain (n : ℕ) (hn_pos : 0 < n) (hn : n < hierarchy.levelCount) :
    getParent hierarchy ⟨n, hn⟩
      (containingTrapezoid hierarchy hdelta hz hactive n hn)
      (containingTrapezoid_spec hierarchy hdelta hz hactive n hn).1 =
    some (containingTrapezoid hierarchy hdelta hz hactive (n - 1) (by omega)) := by
  let level : Fin hierarchy.levelCount := ⟨n, hn⟩
  let t := containingTrapezoid hierarchy hdelta hz hactive n hn
  let ht := (containingTrapezoid_spec hierarchy hdelta hz hactive n hn).1
  have hlevel_pos : (level : ℕ) ≠ 0 := by
    simp [level]; omega
  have hsub : n - 1 < hierarchy.levelCount := by omega
  let pl : Fin hierarchy.levelCount := ⟨n - 1, hsub⟩
  have hpe : (pl : ℕ) + 1 = (level : ℕ) := by
    simp [pl, level]; omega
  let h_ex := hierarchy.unique_parent pl level hpe t ht
  let p := Classical.choose h_ex
  have hp : p ∈ hierarchy.trapezoids pl ∧ t.IsNumericallyNestedIn p :=
    (Classical.choose_spec h_ex).1
  have hz_p : z ∈ p.core := hp.2.1 (containingTrapezoid_spec hierarchy hdelta hz hactive n hn).2
  have h_unique : p = containingTrapezoid hierarchy hdelta hz hactive (n - 1) hsub :=
    unique_containing_trapezoid_at_height hierarchy hdelta pl
      hp.1
      (containingTrapezoid_spec hierarchy hdelta hz hactive (n - 1) hsub).1
      hz_p
      (containingTrapezoid_spec hierarchy hdelta hz hactive (n - 1) hsub).2
  have h_getParent : getParent hierarchy level t ht = some p := by
    simp [getParent, hlevel_pos, p]
  rw [h_getParent, h_unique]

/-- The segment value at natural level n (total function). -/
noncomputable def segVal (n : ℕ) : ℝ :=
  if h : n < hierarchy.levelCount then
    (makeSegment hierarchy hdelta ⟨n, h⟩
      (containingTrapezoid hierarchy hdelta hz hactive n h)
      (containingTrapezoid_spec hierarchy hdelta hz hactive n h).1).value z
  else 0

/-- At level 0, segVal = T_0.affine(z). -/
lemma segVal_base (h0 : 0 < hierarchy.levelCount) :
    segVal hierarchy hdelta hz hactive 0 =
    (containingTrapezoid hierarchy hdelta hz hactive 0 h0).affine z := by
  let t := containingTrapezoid hierarchy hdelta hz hactive 0 h0
  let zeroFin : Fin hierarchy.levelCount := ⟨0, h0⟩
  have ht0 : t ∈ hierarchy.trapezoids zeroFin :=
    (containingTrapezoid_spec hierarchy hdelta hz hactive 0 h0).1
  let seg := makeSegment hierarchy hdelta zeroFin t ht0
  have h_core : z ∈ seg.core := by
    rw [segment_core_eq hierarchy hdelta zeroFin t ht0]
    exact (containingTrapezoid_spec hierarchy hdelta hz hactive 0 h0).2
  have h_val : seg.value z = seg.affine z := by
    simp [WZ1SegmentCorrection.value, h_core]
  have h_main : segVal hierarchy hdelta hz hactive 0 = seg.value z := by
    rw [segVal, dif_pos h0]
  have h_parent_none : getParent hierarchy zeroFin t ht0 = none := by
    simp [getParent, zeroFin]
  have h_affine : seg.affine z = t.affine z := by
    have h := segment_affine_eq hierarchy hdelta zeroFin t ht0 z h_core
    rw [h, h_parent_none]
  rw [h_main, h_val, h_affine]

/-- At level n > 0, segVal = T_n.affine(z) - T_{n-1}.affine(z). -/
lemma segVal_step (n : ℕ) (hn_pos : 0 < n) (hn : n < hierarchy.levelCount) :
    segVal hierarchy hdelta hz hactive n =
    (containingTrapezoid hierarchy hdelta hz hactive n hn).affine z -
    (containingTrapezoid hierarchy hdelta hz hactive (n - 1) (by omega)).affine z := by
  let t := containingTrapezoid hierarchy hdelta hz hactive n hn
  let ht : t ∈ hierarchy.trapezoids ⟨n, hn⟩ :=
    (containingTrapezoid_spec hierarchy hdelta hz hactive n hn).1
  let seg := makeSegment hierarchy hdelta ⟨n, hn⟩ t ht
  have h_core : z ∈ seg.core := by
    rw [segment_core_eq hierarchy hdelta ⟨n, hn⟩ t ht]
    exact (containingTrapezoid_spec hierarchy hdelta hz hactive n hn).2
  have h_val : seg.value z = seg.affine z := by
    simp [WZ1SegmentCorrection.value, h_core]
  have h_main : segVal hierarchy hdelta hz hactive n = seg.value z := by
    rw [segVal, dif_pos hn]

  have h_affine : seg.affine z = t.affine z -
      (containingTrapezoid hierarchy hdelta hz hactive (n - 1) (by omega)).affine z := by
    have h := segment_affine_eq hierarchy hdelta ⟨n, hn⟩ t ht z h_core
    rw [h, parent_chain hierarchy hdelta hz hactive n hn_pos hn]
  rw [h_main, h_val, h_affine]

/-- Induction: sum of first n segVals = T_{n-1}.affine(z) for n > 0. -/
lemma telescoping_induction (n : ℕ) (hn_pos : 0 < n)
    (hn : n ≤ hierarchy.levelCount) :
    ∑ k ∈ Finset.range n, segVal hierarchy hdelta hz hactive k =
    (containingTrapezoid hierarchy hdelta hz hactive (n - 1) (by omega)).affine z := by
  induction n with
  | zero =>
    exfalso; linarith
  | succ n ih =>
    by_cases h_n0 : n = 0
    · subst h_n0
      have h0 : 0 < hierarchy.levelCount := by
        have h := hierarchy.levelCount_two; omega
      simp [Finset.range_one, segVal_base hierarchy hdelta hz hactive h0]
    · have h_n_pos : 0 < n := by omega
      have h_n_lt : n < hierarchy.levelCount := by omega
      have h_ih' := ih h_n_pos (by omega)
      have hstep := segVal_step hierarchy hdelta hz hactive n h_n_pos h_n_lt
      rw [Finset.sum_range_succ, h_ih', hstep]
      have h_eq : containingTrapezoid hierarchy hdelta hz hactive (n + 1 - 1) (by omega) =
          containingTrapezoid hierarchy hdelta hz hactive n h_n_lt := by
        congr
      rw [h_eq]
      ring

/-- At each level, only the containing trapezoid's segment contributes. -/
lemma level_sum_reduces (level : Fin hierarchy.levelCount) :
    ∑ segment ∈ levelSegments hierarchy hdelta level, segment.value z =
    segVal hierarchy hdelta hz hactive (level : ℕ) := by
  let t := containingTrapezoid hierarchy hdelta hz hactive (level : ℕ) level.isLt
  have ht_mem : t ∈ hierarchy.trapezoids level :=
    (containingTrapezoid_spec hierarchy hdelta hz hactive (level : ℕ) level.isLt).1
  have hzt : z ∈ t.core :=
    (containingTrapezoid_spec hierarchy hdelta hz hactive (level : ℕ) level.isLt).2
  let seg := makeSegment hierarchy hdelta level t ht_mem
  have h_seg_core : z ∈ seg.core := by
    rw [segment_core_eq hierarchy hdelta level t ht_mem]
    exact hzt
  have h_seg_in : seg ∈ levelSegments hierarchy hdelta level := by
    have h : ∃ (x : {t // t ∈ hierarchy.trapezoids level}),
        x ∈ (hierarchy.trapezoids level).attach ∧
        makeSegment hierarchy hdelta level x.val x.property = seg := by
      refine ⟨⟨t, ht_mem⟩, by simp, rfl⟩
    simpa [levelSegments, Finset.mem_image] using h
  have h_uniq : ∀ (s : WZ1SegmentCorrection),
      s ∈ levelSegments hierarchy hdelta level →
        s ≠ seg → s.value z = 0 := by
    intro s hs hne
    have h_disj : Disjoint s.support seg.support :=
      disjoint_support_at_level hierarchy hdelta level s hs seg h_seg_in hne
    have h_seg_support : z ∈ seg.support := by
      have h_core_sub : seg.core ⊆ seg.support := by
        intro x hx
        simp only [WZ1SegmentCorrection.core, WZ1SegmentCorrection.support, Set.mem_Icc] at hx ⊢
        exact ⟨by linarith [seg.buffer_pos], by linarith [seg.buffer_pos]⟩
      exact h_core_sub h_seg_core
    have h_notin : z ∉ s.support := by
      have h_symm : Disjoint seg.support s.support := h_disj.symm
      exact Set.disjoint_left.mp h_symm h_seg_support
    have h_notin_core : z ∉ s.core := by
      intro h
      have h_core_sub : s.core ⊆ s.support := by
        intro x hx
        simp only [WZ1SegmentCorrection.core, WZ1SegmentCorrection.support, Set.mem_Icc] at hx ⊢
        exact ⟨by linarith [s.buffer_pos], by linarith [s.buffer_pos]⟩
      exact h_notin (h_core_sub h)
    simp [WZ1SegmentCorrection.value, h_notin_core]
  have h_sum : ∑ segment ∈ levelSegments hierarchy hdelta level, segment.value z =
      seg.value z := by
    rw [Finset.sum_eq_single_of_mem seg h_seg_in h_uniq]

  have h_seg_val : seg.value z = segVal hierarchy hdelta hz hactive (level : ℕ) := by
    have h1 : segVal hierarchy hdelta hz hactive (level : ℕ) =
        (makeSegment hierarchy hdelta level
          (containingTrapezoid hierarchy hdelta hz hactive (level : ℕ) level.isLt)
          (containingTrapezoid_spec hierarchy hdelta hz hactive (level : ℕ) level.isLt).1).value z := by
      rw [segVal, dif_pos level.isLt]

    rw [h1]

  rw [h_sum, h_seg_val]

/-- The full multiscale segment value telescopes to the finest trapezoid affine. -/
lemma telescoping_segment_sum
    (hz : z ∈ Icc (-1 : ℝ) 1)
    (hactive : horizontalSlice Y.union z ≠ ∅)
    (lastFin : Fin hierarchy.levelCount)
    (h_last : (lastFin : ℕ) = hierarchy.levelCount - 1)
    (t_last : WZ1VerticalTrapezoid)
    (ht_last : t_last ∈ hierarchy.trapezoids lastFin)
    (hzt_last : z ∈ t_last.core) :
    wz1MultiscaleSegmentValue hierarchy.levelCount (levelSegments hierarchy hdelta) z =
    t_last.affine z := by
  have hN_pos : 0 < hierarchy.levelCount :=
    Nat.pos_of_ne_zero (by
      have h := hierarchy.levelCount_two
      omega)
  have hsub : hierarchy.levelCount - 1 < hierarchy.levelCount := by omega
  have h1 : wz1MultiscaleSegmentValue hierarchy.levelCount (levelSegments hierarchy hdelta) z =
      ∑ level : Fin hierarchy.levelCount,
        segVal hierarchy hdelta hz hactive (level : ℕ) := by
    simp [wz1MultiscaleSegmentValue]
    apply Finset.sum_congr rfl
    intro level _
    exact level_sum_reduces hierarchy hdelta hz hactive level
  rw [h1]
  have h2 : ∑ level : Fin hierarchy.levelCount,
        segVal hierarchy hdelta hz hactive (level : ℕ) =
      ∑ k ∈ Finset.range hierarchy.levelCount,
        segVal hierarchy hdelta hz hactive k := by
    rw [Fin.sum_univ_eq_sum_range]

  rw [h2]
  have h3 := telescoping_induction hierarchy hdelta hz hactive
    hierarchy.levelCount hN_pos (by linarith)
  have h_eq_fin : (⟨hierarchy.levelCount - 1, hsub⟩ : Fin hierarchy.levelCount) = lastFin := by
    apply Fin.ext
    simp [h_last]
  have h_f_last : containingTrapezoid hierarchy hdelta hz hactive
      (hierarchy.levelCount - 1) hsub = t_last := by
    have h_spec1 : containingTrapezoid hierarchy hdelta hz hactive
        (hierarchy.levelCount - 1) hsub ∈
      hierarchy.trapezoids (⟨hierarchy.levelCount - 1, hsub⟩ : Fin hierarchy.levelCount) :=
      (containingTrapezoid_spec hierarchy hdelta hz hactive
        (hierarchy.levelCount - 1) hsub).1
    rw [h_eq_fin] at h_spec1
    exact unique_containing_trapezoid_at_height hierarchy hdelta lastFin
      h_spec1 ht_last
      (containingTrapezoid_spec hierarchy hdelta hz hactive
        (hierarchy.levelCount - 1) hsub).2
      hzt_last
  rw [h_f_last] at h3
  exact h3

end Telescoping

end Kakeya.Assouad
