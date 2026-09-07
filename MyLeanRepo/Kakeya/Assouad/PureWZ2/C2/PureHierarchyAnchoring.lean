import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.PureHierarchyVolumeRetention
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.OneScaleStatements
import MyLeanRepo.Kakeya.Assouad.WZ1.Corollary26TwoProducerIteration

/-!
# Carrier-generic endpoint anchoring and unique parents

This is the final one-dimensional step of Corollary 5.6.  It deliberately
does not assume cubicality: the paper's popularity restriction cuts the
source cells horizontally before the trapezoids are reanchored.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

/-- An active height lies in the supplied vertical window. -/
lemma active_height_in_Icc_generic
    {BF : Kakeya.Streamlined.BodyFamily}
    {Z : Kakeya.Streamlined.Shading BF}
    {z : ℝ}
    (hZ_height : ∀ point ∈ Z.union, point 2 ∈ Set.Icc (-1 : ℝ) 1)
    (hactive : horizontalSlice Z.union z ≠ ∅) :
    z ∈ Set.Icc (-1 : ℝ) 1 := by
  rcases Set.nonempty_iff_ne_empty.mpr hactive with ⟨point, hpoint⟩
  rw [← hpoint.2]
  exact hZ_height point hpoint.1

/-- Unique adjacent-level parent on an arbitrary finite body-family shading.
The proof is the numerical parent argument from Corollary 5.6 verbatim; the
only ambient input is the explicit vertical-coordinate bound. -/
lemma prove_unique_parent_generic
    {N : ℕ} {delta : ℝ} {hierarchyLoss : ℝ}
    {BF : Kakeya.Streamlined.BodyFamily}
    {Z : Kakeya.Streamlined.Shading BF}
    {sourceSlope : ℝ → ℝ}
    (hdelta_pos : 0 < delta)
    (hdelta_one : delta ≤ 1)
    (hhierarchyLoss : 0 < hierarchyLoss)
    (hZ_height : ∀ point ∈ Z.union, point 2 ∈ Set.Icc (-1 : ℝ) 1)
    (trapezoids : Fin N → Finset WZ1VerticalTrapezoid)
    (h_nonempty : ∀ j, (trapezoids j).Nonempty)
    (h_height_eq : ∀ j, ∀ t ∈ trapezoids j,
        t.height = wz1Corollary26Scale delta N j)
    (h_length_bounds : ∀ j, ∀ t ∈ trapezoids j,
        Real.rpow (wz1Corollary26Scale delta N j) (1 / 2 + hierarchyLoss) ≤ t.length ∧
        t.length ≤ Real.sqrt (wz1Corollary26Scale delta N j))
    (h_separated : ∀ j, ∀ t ∈ trapezoids j, ∀ s ∈ trapezoids j, t ≠ s →
        ∀ z ∈ t.core, ∀ w ∈ s.core,
          Real.sqrt (wz1Corollary26Scale delta N j) ≤ |z - w|)
    (h_coverage : ∀ j, ∀ z ∈ Set.Icc (-1 : ℝ) 1,
        horizontalSlice Z.union z ≠ ∅ → ∃ t ∈ trapezoids j, z ∈ t.core)
    (h_slope_approx : ∀ j, ∀ t ∈ trapezoids j, ∀ z ∈ t.core,
        horizontalSlice Z.union z ≠ ∅ →
          |sourceSlope z - t.affine z| ≤ wz1Corollary26Scale delta N j)
    (h_active_endpoints : ∀ j, ∀ t ∈ trapezoids j,
        horizontalSlice Z.union t.left ≠ ∅ ∧
        horizontalSlice Z.union t.right ≠ ∅) :
    ∀ (parentLevel childLevel : Fin N),
      (parentLevel : ℕ) + 1 = (childLevel : ℕ) →
        ∀ child ∈ trapezoids childLevel,
          ∃! parent, parent ∈ trapezoids parentLevel ∧
            child.IsNumericallyNestedIn parent := by
  let rho_j (j : Fin N) : ℝ := wz1Corollary26Scale delta N j
  have h_rho_pos : ∀ j, 0 < rho_j j := by
    intro j; exact Real.rpow_pos_of_pos hdelta_pos _
  have h_approx : ∀ j, ∀ t ∈ trapezoids j, ∀ z ∈ t.core,
      horizontalSlice Z.union z ≠ ∅ → |sourceSlope z - t.affine z| ≤ rho_j j := by
    simpa [rho_j] using h_slope_approx
  have h_sep : ∀ j, ∀ t ∈ trapezoids j, ∀ s ∈ trapezoids j, t ≠ s →
      ∀ z ∈ t.core, ∀ w ∈ s.core, Real.sqrt (rho_j j) ≤ |z - w| := by
    simpa [rho_j] using h_separated
  have h_height : ∀ j, ∀ t ∈ trapezoids j, t.height = rho_j j := by
    simpa [rho_j] using h_height_eq
  have h_length : ∀ j, ∀ t ∈ trapezoids j,
      Real.rpow (rho_j j) (1 / 2 + hierarchyLoss) ≤ t.length ∧
      t.length ≤ Real.sqrt (rho_j j) := by
    simpa [rho_j] using h_length_bounds
  have h_active_ep : ∀ j, ∀ t ∈ trapezoids j,
      horizontalSlice Z.union t.left ≠ ∅ ∧ horizontalSlice Z.union t.right ≠ ∅ :=
    h_active_endpoints
  have h_cov : ∀ j, ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      horizontalSlice Z.union z ≠ ∅ → ∃ t ∈ trapezoids j, z ∈ t.core :=
    h_coverage
  intro parentLevel childLevel h_adj child hchild
  by_cases hdelta_lt_one : delta < 1
  · -- delta < 1: scales are strictly decreasing
    have h_child_lt_parent : rho_j childLevel < rho_j parentLevel := by
      have h1 : (parentLevel : ℕ) < (childLevel : ℕ) := by omega
      have h_raw := hierarchyScale_strict_mono hdelta_pos hdelta_lt_one h1 childLevel.isLt
      have h_eq_c := hierarchyScale_eq_wz1Scale (delta := delta) (N := N) (j := childLevel)
      have h_eq_p := hierarchyScale_eq_wz1Scale (delta := delta) (N := N) (j := parentLevel)
      rw [h_eq_c, h_eq_p] at h_raw
      exact h_raw
    have h_rho_parent_pos : 0 < rho_j parentLevel := h_rho_pos parentLevel
    have h_rho_child_pos : 0 < rho_j childLevel := h_rho_pos childLevel
    have h_left_in_Icc : child.left ∈ Set.Icc (-1 : ℝ) 1 :=
      active_height_in_Icc_generic hZ_height (h_active_ep childLevel child hchild).1
    have h_right_in_Icc : child.right ∈ Set.Icc (-1 : ℝ) 1 :=
      active_height_in_Icc_generic hZ_height (h_active_ep childLevel child hchild).2
    have h_left_covered : ∃ p ∈ trapezoids parentLevel, child.left ∈ p.core :=
      h_cov parentLevel child.left h_left_in_Icc (h_active_ep childLevel child hchild).1
    have h_right_covered : ∃ p ∈ trapezoids parentLevel, child.right ∈ p.core :=
      h_cov parentLevel child.right h_right_in_Icc (h_active_ep childLevel child hchild).2
    have h_unique_core := unique_parent_core_containment
      h_rho_parent_pos h_rho_child_pos (h_sep parentLevel)
      (h_length childLevel child hchild |>.2) h_child_lt_parent
      h_left_covered h_right_covered
    rcases h_unique_core with ⟨parent, ⟨hp_mem, h_core_sub⟩, h_uniq_core⟩
    have h_child_left_active : horizontalSlice Z.union child.left ≠ ∅ :=
      (h_active_ep childLevel child hchild).1
    have h_child_right_active : horizontalSlice Z.union child.right ≠ ∅ :=
      (h_active_ep childLevel child hchild).2
    have h_child_approx_left := h_approx childLevel child hchild child.left
      (Set.left_mem_Icc.mpr child.left_lt_right.le) h_child_left_active
    have h_child_approx_right := h_approx childLevel child hchild child.right
      (Set.right_mem_Icc.mpr child.left_lt_right.le) h_child_right_active
    have h_parent_approx_left := h_approx parentLevel parent hp_mem child.left
      (h_core_sub (Set.left_mem_Icc.mpr child.left_lt_right.le)) h_child_left_active
    have h_parent_approx_right := h_approx parentLevel parent hp_mem child.right
      (h_core_sub (Set.right_mem_Icc.mpr child.left_lt_right.le)) h_child_right_active
    have h_nesting := numerical_nesting_from_endpoint_approximations
      (h_height childLevel child hchild) (h_height parentLevel parent hp_mem)
      h_core_sub h_child_approx_left h_child_approx_right
      h_parent_approx_left h_parent_approx_right
    refine ⟨parent, ⟨hp_mem, h_nesting⟩, ?_⟩
    intro q hq
    have hq_core_sub : child.core ⊆ q.core := hq.2.1
    exact h_uniq_core q ⟨hq.1, hq_core_sub⟩
  · -- delta = 1: all scales = 1, all lengths = 1, at most one trapezoid per level
    have hdelta_eq : delta = 1 := by linarith
    have h_rho_eq1 : ∀ (j : Fin N), rho_j j = 1 := by
      intro j
      simp [rho_j, wz1Corollary26Scale, hdelta_eq] <;> norm_num
    have h_len1 : ∀ (j : Fin N), ∀ t ∈ trapezoids j, t.length = 1 := by
      intro j t ht
      have hlb := h_length j t ht
      have hr : rho_j j = 1 := h_rho_eq1 j
      rw [hr] at hlb
      have h1 : Real.rpow (1 : ℝ) (1 / 2 + hierarchyLoss) = 1 := by simp
      have h2 : Real.sqrt (1 : ℝ) = 1 := by simp
      rw [h1, h2] at hlb <;> linarith
    have h_cores_in_Icc : ∀ (j : Fin N), ∀ t ∈ trapezoids j, t.core ⊆ Set.Icc (-1 : ℝ) 1 := by
      intro j t ht
      have h_left_Icc : t.left ∈ Set.Icc (-1 : ℝ) 1 :=
        active_height_in_Icc_generic hZ_height (h_active_ep j t ht).1
      have h_right_Icc : t.right ∈ Set.Icc (-1 : ℝ) 1 :=
        active_height_in_Icc_generic hZ_height (h_active_ep j t ht).2
      intro z hz
      have h1 : t.left ≤ z := (Set.mem_Icc.mp hz).1
      have h2 : z ≤ t.right := (Set.mem_Icc.mp hz).2
      exact Set.mem_Icc.mpr ⟨by linarith [(Set.mem_Icc.mp h_left_Icc).1, (Set.mem_Icc.mp h_right_Icc).2],
        by linarith [(Set.mem_Icc.mp h_left_Icc).1, (Set.mem_Icc.mp h_right_Icc).2]⟩
    have h_sep1 : ∀ (j : Fin N), ∀ t ∈ trapezoids j, ∀ s ∈ trapezoids j, t ≠ s →
        ∀ z ∈ t.core, ∀ w ∈ s.core, (1 : ℝ) ≤ |z - w| := by
      intro j t ht s hs hne z hz w hw
      have h := h_sep j t ht s hs hne z hz w hw
      have hr : rho_j j = 1 := h_rho_eq1 j
      rw [hr] at h
      have hsqrt1 : Real.sqrt (1 : ℝ) = 1 := by norm_num
      rw [hsqrt1] at h
      exact h
    have h_at_most_one : ∀ (j : Fin N), ∀ t ∈ trapezoids j, ∀ s ∈ trapezoids j, t = s :=
      fun j => at_most_one_trapezoid_delta_one (h_len1 j) (h_sep1 j) (h_cores_in_Icc j)
    rcases h_nonempty parentLevel with ⟨parent, hp_mem⟩
    have h_parent_unique : ∀ q ∈ trapezoids parentLevel, q = parent :=
      fun q hq => h_at_most_one parentLevel q hq parent hp_mem
    have h_left_covered : ∃ p ∈ trapezoids parentLevel, child.left ∈ p.core :=
      h_cov parentLevel child.left
        (active_height_in_Icc_generic hZ_height (h_active_ep childLevel child hchild).1)
        (h_active_ep childLevel child hchild).1
    rcases h_left_covered with ⟨p_left, hp_left_mem, h_left_in⟩
    have hp_left_eq : p_left = parent := h_parent_unique p_left hp_left_mem
    have h_core_sub : child.core ⊆ parent.core := by
      rw [hp_left_eq] at h_left_in
      intro z hz
      have h1 : child.left ≤ z := (Set.mem_Icc.mp hz).1
      have h2 : z ≤ child.right := (Set.mem_Icc.mp hz).2
      have h3 : parent.left ≤ child.left := (Set.mem_Icc.mp h_left_in).1
      have h4 : child.right ≤ parent.right := by
        rcases h_cov parentLevel child.right
          (active_height_in_Icc_generic hZ_height (h_active_ep childLevel child hchild).2)
          (h_active_ep childLevel child hchild).2 with ⟨p_right, hp_right_mem, h_right_in⟩
        have hp_right_eq : p_right = parent := h_parent_unique p_right hp_right_mem
        rw [hp_right_eq] at h_right_in
        exact (Set.mem_Icc.mp h_right_in).2
      exact Set.mem_Icc.mpr ⟨by linarith, by linarith⟩
    have h_child_left_active : horizontalSlice Z.union child.left ≠ ∅ :=
      (h_active_ep childLevel child hchild).1
    have h_child_right_active : horizontalSlice Z.union child.right ≠ ∅ :=
      (h_active_ep childLevel child hchild).2
    have h_child_approx_left := h_approx childLevel child hchild child.left
      (Set.left_mem_Icc.mpr child.left_lt_right.le) h_child_left_active
    have h_child_approx_right := h_approx childLevel child hchild child.right
      (Set.right_mem_Icc.mpr child.left_lt_right.le) h_child_right_active
    have h_parent_approx_left := h_approx parentLevel parent hp_mem child.left
      (h_core_sub (Set.left_mem_Icc.mpr child.left_lt_right.le)) h_child_left_active
    have h_parent_approx_right := h_approx parentLevel parent hp_mem child.right
      (h_core_sub (Set.right_mem_Icc.mpr child.left_lt_right.le)) h_child_right_active
    have h_nesting := numerical_nesting_from_endpoint_approximations
      (h_height childLevel child hchild) (h_height parentLevel parent hp_mem)
      h_core_sub h_child_approx_left h_child_approx_right
      h_parent_approx_left h_parent_approx_right
    refine ⟨parent, ⟨hp_mem, h_nesting⟩, ?_⟩
    intro q hq
    have hq_mem : q ∈ trapezoids parentLevel := hq.1
    exact h_parent_unique q hq_mem



end Kakeya.Assouad

end
