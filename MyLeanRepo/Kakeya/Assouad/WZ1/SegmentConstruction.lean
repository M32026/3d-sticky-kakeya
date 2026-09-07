import MyLeanRepo.Kakeya.Assouad.WZ1.Corollary26RepairedStatements

/-!
# Segment construction from anchored Corollary 26 hierarchy

Constructs `WZ1SegmentCorrection` values from trapezoids in an anchored hierarchy.
Level 0 uses the trapezoid's own affine values; level k>0 uses the difference
from the unique numerical parent.
-/

namespace Kakeya.Assouad

open WZ1VerticalTrapezoid

section

variable {delta : ℝ}
  {F : Kakeya.Streamlined.TubeFamily delta}
  {Y : Kakeya.Streamlined.TubeShading F}
  {sourceSlope : ℝ → ℝ}
  {hierarchyLoss : ℝ}
  (hierarchy : WZ1Corollary26AnchoredHierarchyData Y sourceSlope hierarchyLoss)

/-- The buffer size for segments at a given level: `sqrt(scale) / 4`. -/
noncomputable def segmentBuffer (level : Fin hierarchy.levelCount) : ℝ :=
  Real.sqrt (wz1Corollary26Scale delta hierarchy.levelCount level) / 4

lemma segmentBuffer_pos (hdelta : 0 < delta) (level : Fin hierarchy.levelCount) :
    0 < segmentBuffer hierarchy level := by
  have hscale_pos : 0 < wz1Corollary26Scale delta hierarchy.levelCount level :=
    Real.rpow_pos_of_pos hdelta _
  have hsqrt_pos : 0 < Real.sqrt (wz1Corollary26Scale delta hierarchy.levelCount level) :=
    Real.sqrt_pos.mpr hscale_pos
  exact div_pos hsqrt_pos (by norm_num)

/-- The zero level, known to exist since `2 ≤ levelCount`. -/
def zeroLevel : Fin hierarchy.levelCount :=
  ⟨0, by have h := hierarchy.levelCount_two; omega⟩

/-- Construct a correction segment from a trapezoid at level 0. -/
noncomputable def makeSegmentLevel0 (hdelta : 0 < delta)
    (trapezoid : WZ1VerticalTrapezoid) : WZ1SegmentCorrection :=
  { x₁ := trapezoid.left
    x₂ := trapezoid.right
    y₁ := trapezoid.affine trapezoid.left
    y₂ := trapezoid.affine trapezoid.right
    buffer := segmentBuffer hierarchy (zeroLevel hierarchy)
    x₁_lt_x₂ := trapezoid.left_lt_right
    buffer_pos := segmentBuffer_pos hierarchy hdelta (zeroLevel hierarchy) }

/-- Construct a correction segment from a trapezoid at level k > 0. -/
noncomputable def makeSegmentAfterFirst (hdelta : 0 < delta)
    (level : Fin hierarchy.levelCount)
    (hlevel : (level : ℕ) > 0)
    (trapezoid : WZ1VerticalTrapezoid)
    (htrapezoid : trapezoid ∈ hierarchy.trapezoids level) :
    WZ1SegmentCorrection := by
  let parentLevel : Fin hierarchy.levelCount := ⟨(level : ℕ) - 1, by omega⟩
  have h_parent_eq : (parentLevel : ℕ) + 1 = (level : ℕ) := by
    simp [parentLevel]; omega
  have h_unique : ∃! (parent : WZ1VerticalTrapezoid),
      parent ∈ hierarchy.trapezoids parentLevel ∧
        trapezoid.IsNumericallyNestedIn parent :=
    hierarchy.unique_parent parentLevel level h_parent_eq trapezoid htrapezoid
  let parent : WZ1VerticalTrapezoid := Classical.choose h_unique
  exact
    { x₁ := trapezoid.left
      x₂ := trapezoid.right
      y₁ := trapezoid.affine trapezoid.left - parent.affine trapezoid.left
      y₂ := trapezoid.affine trapezoid.right - parent.affine trapezoid.right
      buffer := segmentBuffer hierarchy level
      x₁_lt_x₂ := trapezoid.left_lt_right
      buffer_pos := segmentBuffer_pos hierarchy hdelta level }

/-- Construct a correction segment from a trapezoid at any level. -/
noncomputable def makeSegment (hdelta : 0 < delta)
    (level : Fin hierarchy.levelCount)
    (trapezoid : WZ1VerticalTrapezoid)
    (htrapezoid : trapezoid ∈ hierarchy.trapezoids level) :
    WZ1SegmentCorrection :=
  if h : (level : ℕ) = 0 then
    makeSegmentLevel0 hierarchy hdelta trapezoid
  else
    makeSegmentAfterFirst hierarchy hdelta level (by omega) trapezoid htrapezoid

/-- The set of correction segments at a given level. -/
noncomputable def levelSegments (hdelta : 0 < delta)
    (level : Fin hierarchy.levelCount) : Finset WZ1SegmentCorrection := by
  classical
  exact (hierarchy.trapezoids level).attach.image
    (fun p : {t // t ∈ hierarchy.trapezoids level} =>
      makeSegment hierarchy hdelta level p.val p.property)

/-- Extract the unique numerical parent of a trapezoid, or `none` at level 0. -/
noncomputable def getParent
    (level : Fin hierarchy.levelCount)
    (trapezoid : WZ1VerticalTrapezoid)
    (htrapezoid : trapezoid ∈ hierarchy.trapezoids level) :
    Option WZ1VerticalTrapezoid :=
  if h : (level : ℕ) = 0 then none
  else
    let parentLevel : Fin hierarchy.levelCount := ⟨(level : ℕ) - 1, by omega⟩
    have h_parent_eq : (parentLevel : ℕ) + 1 = (level : ℕ) := by
      simp [parentLevel]; omega
    let h_unique : ∃! (parent : WZ1VerticalTrapezoid),
        parent ∈ hierarchy.trapezoids parentLevel ∧
          trapezoid.IsNumericallyNestedIn parent :=
      hierarchy.unique_parent parentLevel level h_parent_eq trapezoid htrapezoid
    some (Classical.choose h_unique)

-- Field equalities

lemma makeSegment_x1 (hdelta : 0 < delta) (level : Fin hierarchy.levelCount)
    (trapezoid : WZ1VerticalTrapezoid) (htrapezoid : trapezoid ∈ hierarchy.trapezoids level) :
    (makeSegment hierarchy hdelta level trapezoid htrapezoid).x₁ = trapezoid.left := by
  by_cases h : (level : ℕ) = 0
  · simp [makeSegment, h, makeSegmentLevel0]
  · simp [makeSegment, h, makeSegmentAfterFirst]

lemma makeSegment_x2 (hdelta : 0 < delta) (level : Fin hierarchy.levelCount)
    (trapezoid : WZ1VerticalTrapezoid) (htrapezoid : trapezoid ∈ hierarchy.trapezoids level) :
    (makeSegment hierarchy hdelta level trapezoid htrapezoid).x₂ = trapezoid.right := by
  by_cases h : (level : ℕ) = 0
  · simp [makeSegment, h, makeSegmentLevel0]
  · simp [makeSegment, h, makeSegmentAfterFirst]

lemma makeSegment_buffer (hdelta : 0 < delta) (level : Fin hierarchy.levelCount)
    (trapezoid : WZ1VerticalTrapezoid) (htrapezoid : trapezoid ∈ hierarchy.trapezoids level) :
    (makeSegment hierarchy hdelta level trapezoid htrapezoid).buffer = segmentBuffer hierarchy level := by
  by_cases h : (level : ℕ) = 0
  · have hzl : (zeroLevel hierarchy : ℕ) = (level : ℕ) := by simp [zeroLevel, h]
    have h_eq : zeroLevel hierarchy = level := Fin.ext hzl
    simp [makeSegment, h, makeSegmentLevel0, h_eq]
  · simp [makeSegment, h, makeSegmentAfterFirst]

/-- The segment's core equals the trapezoid's core. -/
lemma segment_core_eq (hdelta : 0 < delta)
    (level : Fin hierarchy.levelCount)
    (trapezoid : WZ1VerticalTrapezoid)
    (htrapezoid : trapezoid ∈ hierarchy.trapezoids level) :
    (makeSegment hierarchy hdelta level trapezoid htrapezoid).core = trapezoid.core := by
  have h1 := makeSegment_x1 hierarchy hdelta level trapezoid htrapezoid
  have h2 := makeSegment_x2 hierarchy hdelta level trapezoid htrapezoid
  simp [WZ1SegmentCorrection.core, WZ1VerticalTrapezoid.core, h1, h2]

/-- Auxiliary: affine interpolation for affine functions. -/
lemma affine_interpolation_general (f : ℝ → ℝ) (x₁ x₂ z : ℝ) (h : x₁ < x₂)
    (m b : ℝ) (h_f : ∀ x, f x = m * x + b) :
    f x₁ + (z - x₁) * ((f x₂ - f x₁) / (x₂ - x₁)) = f z := by
  have hden : x₂ - x₁ ≠ 0 := by linarith
  rw [h_f x₁, h_f x₂, h_f z]
  field_simp [hden] <;> ring

/--
The segment's affine function matches the trapezoid (level 0) or the
trapezoid-parent difference (level k>0).
-/
lemma segment_affine_eq (hdelta : 0 < delta)
    (level : Fin hierarchy.levelCount)
    (trapezoid : WZ1VerticalTrapezoid)
    (htrapezoid : trapezoid ∈ hierarchy.trapezoids level)
    (z : ℝ) (_ : z ∈ (makeSegment hierarchy hdelta level trapezoid htrapezoid).core) :
    (makeSegment hierarchy hdelta level trapezoid htrapezoid).affine z =
      match getParent hierarchy level trapezoid htrapezoid with
      | none => trapezoid.affine z
      | some parent => trapezoid.affine z - parent.affine z := by
  by_cases h : (level : ℕ) = 0
  · let f : ℝ → ℝ := fun x => trapezoid.affine x
    have h_f : ∀ x, f x = trapezoid.slope * x + trapezoid.intercept := by
      intro x; simp [f, WZ1VerticalTrapezoid.affine]
    have h_goal : (makeSegment hierarchy hdelta level trapezoid htrapezoid).affine z = trapezoid.affine z := by
      dsimp only [makeSegment, WZ1SegmentCorrection.affine]
      rw [dif_pos h]
      dsimp only [makeSegmentLevel0]
      exact affine_interpolation_general f trapezoid.left trapezoid.right z
        trapezoid.left_lt_right trapezoid.slope trapezoid.intercept h_f
    rw [h_goal]
    have h_parent_none : getParent hierarchy level trapezoid htrapezoid = none := by
      simp [getParent, h]
    rw [h_parent_none]
  · let parentLevel : Fin hierarchy.levelCount := ⟨(level : ℕ) - 1, by omega⟩
    have h_parent_eq : (parentLevel : ℕ) + 1 = (level : ℕ) := by
      simp [parentLevel]; omega
    let h_unique : ∃! (parent : WZ1VerticalTrapezoid),
        parent ∈ hierarchy.trapezoids parentLevel ∧ trapezoid.IsNumericallyNestedIn parent :=
      hierarchy.unique_parent parentLevel level h_parent_eq trapezoid htrapezoid
    let parent : WZ1VerticalTrapezoid := Classical.choose h_unique
    let f : ℝ → ℝ := fun x => trapezoid.affine x - parent.affine x
    have h_f : ∀ x, f x = (trapezoid.slope - parent.slope) * x + (trapezoid.intercept - parent.intercept) := by
      intro x; simp [f, WZ1VerticalTrapezoid.affine] <;> ring
    have h_goal : (makeSegment hierarchy hdelta level trapezoid htrapezoid).affine z =
        trapezoid.affine z - parent.affine z := by
      dsimp only [makeSegment, WZ1SegmentCorrection.affine]
      rw [dif_neg h]
      dsimp only [makeSegmentAfterFirst]
      exact affine_interpolation_general f trapezoid.left trapezoid.right z
        trapezoid.left_lt_right (trapezoid.slope - parent.slope) (trapezoid.intercept - parent.intercept) h_f
    rw [h_goal]
    have h_parent_some : getParent hierarchy level trapezoid htrapezoid = some parent := by
      simp [getParent, h, parent]
    rw [h_parent_some]

/--
Supports of segments from different trapezoids at the same level are disjoint.
-/
lemma disjoint_support_at_level (hdelta : 0 < delta)
    (level : Fin hierarchy.levelCount) :
    ∀ segment ∈ levelSegments hierarchy hdelta level,
      ∀ other ∈ levelSegments hierarchy hdelta level,
        segment ≠ other → Disjoint segment.support other.support := by
  intro segment hsegment other hother hne
  classical
  rcases Finset.mem_image.mp hsegment with ⟨p, _, rfl⟩
  rcases Finset.mem_image.mp hother with ⟨q, _, rfl⟩
  set T := p.val with hT_eq
  set S := q.val with hS_eq
  have hT : T ∈ hierarchy.trapezoids level := p.property
  have hS : S ∈ hierarchy.trapezoids level := q.property
  by_cases hTS : T = S
  · have h_pq : p = q := by apply Subtype.ext; exact hTS
    have h_seg_eq : makeSegment hierarchy hdelta level p.val p.property =
        makeSegment hierarchy hdelta level q.val q.property := by rw [h_pq]
    exfalso; exact hne h_seg_eq
  · -- T ≠ S
    have h_sep : ∀ z ∈ T.core, ∀ w ∈ S.core,
        Real.sqrt (wz1Corollary26Scale delta hierarchy.levelCount level) ≤ |z - w| :=
      hierarchy.separated_cores level T hT S hS hTS
    have hsqrt_pos : 0 < Real.sqrt (wz1Corollary26Scale delta hierarchy.levelCount level) :=
      Real.sqrt_pos.mpr (Real.rpow_pos_of_pos hdelta _)
    have h_buf2 : 2 * segmentBuffer hierarchy level <
        Real.sqrt (wz1Corollary26Scale delta hierarchy.levelCount level) := by
      simp [segmentBuffer] <;> linarith
    rw [Set.disjoint_left]
    intro x hx1 hx2
    simp only [WZ1SegmentCorrection.support, Set.mem_Icc] at hx1 hx2
    rcases hx1 with ⟨h1, h2⟩
    rcases hx2 with ⟨h3, h4⟩
    have h_x1_T := makeSegment_x1 hierarchy hdelta level T hT
    have h_x2_T := makeSegment_x2 hierarchy hdelta level T hT
    have h_buf_T := makeSegment_buffer hierarchy hdelta level T hT
    have h_x1_S := makeSegment_x1 hierarchy hdelta level S hS
    have h_x2_S := makeSegment_x2 hierarchy hdelta level S hS
    have h_buf_S := makeSegment_buffer hierarchy hdelta level S hS
    rw [h_x1_T, h_buf_T] at h1
    rw [h_x2_T, h_buf_T] at h2
    rw [h_x1_S, h_buf_S] at h3
    rw [h_x2_S, h_buf_S] at h4
    have hT_right_in : T.right ∈ T.core := by
      have h : T.left ≤ T.right := le_of_lt T.left_lt_right
      exact ⟨h, le_refl T.right⟩
    have hS_left_in : S.left ∈ S.core := by
      have h : S.left ≤ S.right := le_of_lt S.left_lt_right
      exact ⟨le_refl S.left, h⟩
    have hT_left_in : T.left ∈ T.core := by
      have h : T.left ≤ T.right := le_of_lt T.left_lt_right
      exact ⟨le_refl T.left, h⟩
    have hS_right_in : S.right ∈ S.core := by
      have h : S.left ≤ S.right := le_of_lt S.left_lt_right
      exact ⟨h, le_refl S.right⟩
    by_cases h_case : T.right < S.left
    · -- T is left of S
      have h6 := h_sep T.right hT_right_in S.left hS_left_in
      have h_neg : T.right - S.left < 0 := by linarith
      have h7 : |T.right - S.left| = S.left - T.right := by
        rw [abs_of_neg h_neg] <;> linarith
      rw [h7] at h6
      have h9 : S.left - T.right ≤ 2 * segmentBuffer hierarchy level := by linarith
      linarith [h_buf2]
    · -- Not T.right < S.left, so S.left ≤ T.right
      have h_sl_le_tr : S.left ≤ T.right := by linarith
      by_cases h_case2 : T.left ≤ S.right
      · -- Cores overlap
        let z := max T.left S.left
        have hzT : z ∈ T.core := by
          have h1 : T.left ≤ z := le_max_left _ _
          have h2 : z ≤ T.right := max_le (le_of_lt T.left_lt_right) h_sl_le_tr
          exact ⟨h1, h2⟩
        have hzS : z ∈ S.core := by
          have h1 : S.left ≤ z := le_max_right _ _
          have h2 : z ≤ S.right := max_le h_case2 (le_of_lt S.left_lt_right)
          exact ⟨h1, h2⟩
        have h_contra := h_sep z hzT z hzS
        have h8 : |z - z| = 0 := by simp
        rw [h8] at h_contra
        linarith [hsqrt_pos]
      · -- S.right < T.left
        have h_sr_lt_tl : S.right < T.left := by linarith
        have h6 := h_sep T.left hT_left_in S.right hS_right_in
        have h_pos : 0 < T.left - S.right := by linarith
        have h7 : |T.left - S.right| = T.left - S.right := by
          rw [abs_of_pos h_pos]
        rw [h7] at h6
        have h9 : T.left - S.right ≤ 2 * segmentBuffer hierarchy level := by linarith
        linarith [h_buf2]

/--
At any active height, z is in the core of some segment at each level,
and off the support of all other segments at that level.
-/
lemma core_or_off_support (hdelta : 0 < delta) :
    ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      (∀ level, ∀ segment ∈ levelSegments hierarchy hdelta level,
        z ∈ segment.core ∨ z ∉ segment.support) ∨
      horizontalSlice Y.union z = ∅ := by
  intro z hz
  by_cases h_slice : horizontalSlice Y.union z = ∅
  · exact Or.inr h_slice
  · -- horizontal slice is non-empty
    have h_slice_nonempty : horizontalSlice Y.union z ≠ ∅ := h_slice
    refine Or.inl (fun level => ?_)
    have h_cov : ∃ (trapezoid : WZ1VerticalTrapezoid),
        trapezoid ∈ hierarchy.trapezoids level ∧ z ∈ trapezoid.core :=
      hierarchy.active_height_coverage level z hz h_slice_nonempty
    rcases h_cov with ⟨T, hT_mem, hzT_core⟩
    set segT := makeSegment hierarchy hdelta level T hT_mem with hsegT
    have h_segT_in : segT ∈ levelSegments hierarchy hdelta level := by
      have h_goal : ∃ (x : {t // t ∈ hierarchy.trapezoids level}),
          x ∈ (hierarchy.trapezoids level).attach ∧
          makeSegment hierarchy hdelta level x.val x.property = segT := by
        refine ⟨⟨T, hT_mem⟩, by simp, ?_⟩
        exact hsegT.symm
      simpa [levelSegments, Finset.mem_image] using h_goal
    have hzT_seg_core : z ∈ segT.core := by
      rw [segment_core_eq hierarchy hdelta level T hT_mem]
      exact hzT_core
    have hzT_seg_support : z ∈ segT.support := by
      have h_core_sub : segT.core ⊆ segT.support := by
        intro x hx
        simp only [WZ1SegmentCorrection.core, WZ1SegmentCorrection.support, Set.mem_Icc] at hx ⊢
        exact ⟨by linarith [segT.buffer_pos], by linarith [segT.buffer_pos]⟩
      exact h_core_sub hzT_seg_core
    intro segment hsegment
    by_cases h_eq : segment = segT
    · rw [h_eq]; exact Or.inl hzT_seg_core
    · have h_disj : Disjoint segment.support segT.support :=
        disjoint_support_at_level hierarchy hdelta level segment hsegment segT h_segT_in h_eq
      have h_notin : z ∉ segment.support := by
        have h_symm : Disjoint segT.support segment.support := h_disj.symm
        have h : ∀ x, x ∈ segT.support → x ∉ segment.support := Set.disjoint_left.mp h_symm
        exact h z hzT_seg_support
      exact Or.inr h_notin

/--
Construct a `WZ1Corollary26SegmentSource` certificate for a segment.
-/
noncomputable def segmentSourceCertificate (hdelta : 0 < delta)
    (level : Fin hierarchy.levelCount)
    (trapezoid : WZ1VerticalTrapezoid)
    (htrapezoid : trapezoid ∈ hierarchy.trapezoids level) :
    WZ1Corollary26SegmentSource hierarchy level
      (makeSegment hierarchy hdelta level trapezoid htrapezoid) := by
  by_cases h : (level : ℕ) = 0
  · -- Level 0: parent = none
    exact {
      trapezoid := trapezoid
      trapezoid_mem := htrapezoid
      parent := none
      parent_at_first := by intro _; rfl
      parent_after_first := by intro _ h2; exfalso; omega
      core_eq := segment_core_eq hierarchy hdelta level trapezoid htrapezoid
      affine_eq := by
        intro z hz
        dsimp only [makeSegment, WZ1SegmentCorrection.affine]
        rw [dif_pos h]
        dsimp only [makeSegmentLevel0]
        let f : ℝ → ℝ := fun x => trapezoid.affine x
        have h_f : ∀ x, f x = trapezoid.slope * x + trapezoid.intercept := by
          intro x; simp [f, WZ1VerticalTrapezoid.affine]
        exact affine_interpolation_general f trapezoid.left trapezoid.right z
          trapezoid.left_lt_right trapezoid.slope trapezoid.intercept h_f
    }
  · -- Level > 0: parent = some p
    let parentLevel : Fin hierarchy.levelCount := ⟨(level : ℕ) - 1, by omega⟩
    have hpe : (parentLevel : ℕ) + 1 = (level : ℕ) := by simp [parentLevel]; omega
    let p := Classical.choose (hierarchy.unique_parent parentLevel level hpe trapezoid htrapezoid)
    have hspec : p ∈ hierarchy.trapezoids parentLevel ∧ trapezoid.IsNumericallyNestedIn p :=
      (Classical.choose_spec (hierarchy.unique_parent parentLevel level hpe trapezoid htrapezoid)).1
    exact {
      trapezoid := trapezoid
      trapezoid_mem := htrapezoid
      parent := some p
      parent_at_first := by intro h2; exfalso; omega
      parent_after_first := by
        intro pl h_pl_eq
        have h_pl_eq2 : parentLevel = pl := by
          apply Fin.ext
          simp [parentLevel, h_pl_eq] <;> omega
        refine ⟨p, ?_, h_pl_eq2 ▸ hspec⟩
        rfl
      core_eq := segment_core_eq hierarchy hdelta level trapezoid htrapezoid
      affine_eq := by
        intro z hz
        dsimp only [makeSegment, WZ1SegmentCorrection.affine]
        rw [dif_neg h]
        dsimp only [makeSegmentAfterFirst]
        let f : ℝ → ℝ := fun x => trapezoid.affine x - p.affine x
        have h_f : ∀ x, f x = (trapezoid.slope - p.slope) * x + (trapezoid.intercept - p.intercept) := by
          intro x; simp [f, WZ1VerticalTrapezoid.affine] <;> ring
        exact affine_interpolation_general f trapezoid.left trapezoid.right z
          trapezoid.left_lt_right (trapezoid.slope - p.slope) (trapezoid.intercept - p.intercept) h_f
    }

end

section CostBounds

variable {sigma inputLoss delta finalLoss hierarchyLoss : ℝ}
  {source : WZ1PlaninessGraininessPackage sigma inputLoss delta}
  (hierarchy : WZ1Corollary26AnchoredHierarchyPackage source hierarchyLoss)

/-- If a horizontal slice is nonempty, the height lies in `[-1, 1]`. -/
lemma active_height_in_Icc {z : ℝ}
    (hz : horizontalSlice hierarchy.shading.union z ≠ ∅) :
    z ∈ Set.Icc (-1 : ℝ) 1 := by
  have h_union : hierarchy.shading.union ⊆ Metric.closedBall (0 : Point3) 1 :=
    hierarchy.extremal.2.2.2.1
  rcases Set.nonempty_iff_ne_empty.mpr hz with ⟨p, hp⟩
  have h1 : p ∈ hierarchy.shading.union := hp.1
  have h2 : p ∈ Metric.closedBall (0 : Point3) 1 := h_union h1
  have h3 : ‖p‖ ≤ 1 := by simpa [Metric.mem_closedBall] using h2
  have h4 : |p (2 : Fin 3)| ≤ ‖p‖ := by
    have h_nonneg : 0 ≤ ∑ i : Fin 3, |p i| ^ 2 := by positivity
    have h_norm_eq : ‖p‖ = Real.sqrt (∑ i : Fin 3, |p i| ^ 2) := EuclideanSpace.norm_eq p
    have h_norm2 : ‖p‖ ^ 2 = ∑ i : Fin 3, |p i| ^ 2 := by
      rw [h_norm_eq]
      exact Real.sq_sqrt h_nonneg
    have h : |p (2 : Fin 3)| ^ 2 ≤ ∑ i : Fin 3, |p i| ^ 2 := by
      have h9 : ∑ i : Fin 3, |p i| ^ 2 = |p 0| ^ 2 + |p 1| ^ 2 + |p 2| ^ 2 := by
        simp [Fin.sum_univ_succ] <;> ring
      rw [h9]
      have h10 : 0 ≤ |p 0| ^ 2 := by positivity
      have h11 : 0 ≤ |p 1| ^ 2 := by positivity
      simp [Fin.sum_univ_succ] at * <;> linarith
    have hsq : |p (2 : Fin 3)| ^ 2 ≤ ‖p‖ ^ 2 := by
      rw [h_norm2]
      exact h
    have hpos1 : 0 ≤ |p (2 : Fin 3)| := abs_nonneg _
    have hpos2 : 0 ≤ ‖p‖ := norm_nonneg _
    nlinarith
  have h5 : |p (2 : Fin 3)| ≤ 1 := by linarith
  have h6 : p (2 : Fin 3) = z := hp.2
  rw [h6] at h5
  exact ⟨by linarith [abs_le.mp h5], by linarith [abs_le.mp h5]⟩

/-- Bound on a level-0 trapezoid's affine value at active endpoints. -/
lemma level0_affine_endpoint_bound (hdelta : 0 < delta)
    (level : Fin hierarchy.hierarchy.levelCount)
    (trapezoid : WZ1VerticalTrapezoid)
    (htrapezoid : trapezoid ∈ hierarchy.hierarchy.trapezoids level)
    (hlevel0 : (level : ℕ) = 0) :
    |trapezoid.affine trapezoid.left| ≤ 4 ∧
    |trapezoid.affine trapezoid.right| ≤ 4 := by
  have h_endpoints := hierarchy.hierarchy.active_endpoints level trapezoid htrapezoid
  have h_left_active : horizontalSlice hierarchy.shading.union trapezoid.left ≠ ∅ :=
    h_endpoints.1
  have h_right_active : horizontalSlice hierarchy.shading.union trapezoid.right ≠ ∅ :=
    h_endpoints.2
  have h_left_in : trapezoid.left ∈ Set.Icc (-1 : ℝ) 1 :=
    active_height_in_Icc hierarchy h_left_active
  have h_right_in : trapezoid.right ∈ Set.Icc (-1 : ℝ) 1 :=
    active_height_in_Icc hierarchy h_right_active
  have h_slope_left : |source.global_grains.slope trapezoid.left| ≤ 3 :=
    source.slope_bound trapezoid.left h_left_in
  have h_slope_right : |source.global_grains.slope trapezoid.right| ≤ 3 :=
    source.slope_bound trapezoid.right h_right_in
  have h_scale_pos : 0 < wz1Corollary26Scale delta hierarchy.hierarchy.levelCount level :=
    Real.rpow_pos_of_pos hdelta _
  have hdelta_one : delta ≤ 1 := hierarchy.extremal.2.1
  have h_scale_le_one : wz1Corollary26Scale delta hierarchy.hierarchy.levelCount level ≤ 1 := by
    have h0 : 0 ≤ delta := by linarith
    exact Real.rpow_le_one h0 hdelta_one (by positivity)
  have h_approx_left : |source.global_grains.slope trapezoid.left - trapezoid.affine trapezoid.left| ≤
      wz1Corollary26Scale delta hierarchy.hierarchy.levelCount level :=
    hierarchy.hierarchy.slope_approximation level trapezoid htrapezoid
      trapezoid.left (by
        simp only [WZ1VerticalTrapezoid.core, Set.mem_Icc]
        exact ⟨le_refl trapezoid.left, le_of_lt trapezoid.left_lt_right⟩)
      h_left_active
  have h_approx_right : |source.global_grains.slope trapezoid.right - trapezoid.affine trapezoid.right| ≤
      wz1Corollary26Scale delta hierarchy.hierarchy.levelCount level :=
    hierarchy.hierarchy.slope_approximation level trapezoid htrapezoid
      trapezoid.right (by
        simp only [WZ1VerticalTrapezoid.core, Set.mem_Icc]
        exact ⟨le_of_lt trapezoid.left_lt_right, le_refl trapezoid.right⟩)
      h_right_active
  have h1 : |trapezoid.affine trapezoid.left| ≤ 3 + wz1Corollary26Scale delta hierarchy.hierarchy.levelCount level := by
    calc
      |trapezoid.affine trapezoid.left|
        = |source.global_grains.slope trapezoid.left - (source.global_grains.slope trapezoid.left - trapezoid.affine trapezoid.left)| := by ring_nf
      _ ≤ |source.global_grains.slope trapezoid.left| + |source.global_grains.slope trapezoid.left - trapezoid.affine trapezoid.left| := by exact abs_sub _ _
      _ ≤ 3 + wz1Corollary26Scale delta hierarchy.hierarchy.levelCount level := by linarith
  have h2 : |trapezoid.affine trapezoid.right| ≤ 3 + wz1Corollary26Scale delta hierarchy.hierarchy.levelCount level := by
    calc
      |trapezoid.affine trapezoid.right|
        = |source.global_grains.slope trapezoid.right - (source.global_grains.slope trapezoid.right - trapezoid.affine trapezoid.right)| := by ring_nf
      _ ≤ |source.global_grains.slope trapezoid.right| + |source.global_grains.slope trapezoid.right - trapezoid.affine trapezoid.right| := by exact abs_sub _ _
      _ ≤ 3 + wz1Corollary26Scale delta hierarchy.hierarchy.levelCount level := by linarith
  have h3 : 3 + wz1Corollary26Scale delta hierarchy.hierarchy.levelCount level ≤ 4 := by linarith
  exact ⟨by linarith, by linarith⟩

/-- General cost bound for a segment with bounded endpoint values and slope. -/
lemma segment_cost_bound (segment : WZ1SegmentCorrection)
    (A B W : ℝ) (hA1 : |segment.y₁| ≤ A) (hA2 : |segment.y₂| ≤ A)
    (hB : |(segment.y₂ - segment.y₁) / (segment.x₂ - segment.x₁)| ≤ B)
    (hW : segment.x₂ - segment.x₁ ≤ W)
    (hA_nonneg : 0 ≤ A) (hB_nonneg : 0 ≤ B) (hW_nonneg : 0 ≤ W) :
    segment.firstCost ≤ 2 * A / segment.buffer + B ∧
    segment.secondCost ≤ 2 * A / segment.buffer ^ 2 + B / segment.buffer ∧
    segment.valueCost ≤ (W + 2 * segment.buffer + 1) * (2 * A / segment.buffer + B) := by
  have hbuf_pos : 0 < segment.buffer := segment.buffer_pos
  have h1 : |segment.y₁| + |segment.y₂| ≤ 2 * A := by linarith
  have hfc : segment.firstCost ≤ 2 * A / segment.buffer + B := by
    dsimp only [WZ1SegmentCorrection.firstCost]
    have h2 : (|segment.y₁| + |segment.y₂|) / segment.buffer ≤ (2 * A) / segment.buffer := by
      gcongr
    linarith
  have hsc : segment.secondCost ≤ 2 * A / segment.buffer ^ 2 + B / segment.buffer := by
    dsimp only [WZ1SegmentCorrection.secondCost]
    have h2 : (|segment.y₁| + |segment.y₂|) / segment.buffer ^ 2 ≤ (2 * A) / segment.buffer ^ 2 := by
      gcongr
    have h3 : |(segment.y₂ - segment.y₁) / (segment.x₂ - segment.x₁)| / segment.buffer ≤ B / segment.buffer := by
      gcongr
    exact add_le_add h2 h3
  have hvc : segment.valueCost ≤ (W + 2 * segment.buffer + 1) * (2 * A / segment.buffer + B) := by
    dsimp only [WZ1SegmentCorrection.valueCost]
    have h4 : segment.x₂ - segment.x₁ + 2 * segment.buffer + 1 ≤ W + 2 * segment.buffer + 1 := by linarith
    have h5 : 0 ≤ segment.firstCost := by
      dsimp only [WZ1SegmentCorrection.firstCost]
      positivity
    have h6 : 0 ≤ 2 * A / segment.buffer + B := by positivity
    have h7 : 0 ≤ segment.x₂ - segment.x₁ + 2 * segment.buffer + 1 := by
      have h71 : 0 < segment.x₂ - segment.x₁ := sub_pos.mpr segment.x₁_lt_x₂
      have h72 : 0 < segment.buffer := segment.buffer_pos
      linarith
    calc
      (segment.x₂ - segment.x₁ + 2 * segment.buffer + 1) * segment.firstCost
        ≤ (segment.x₂ - segment.x₁ + 2 * segment.buffer + 1) * (2 * A / segment.buffer + B) := by
          exact mul_le_mul_of_nonneg_left hfc h7
      _ ≤ (W + 2 * segment.buffer + 1) * (2 * A / segment.buffer + B) := by
          exact mul_le_mul_of_nonneg_right h4 h6
  exact ⟨hfc, hsc, hvc⟩

/-- Bound on level-k>0 segment endpoint values from numerical nesting. -/
lemma levelk_affine_diff_bound
    (level : Fin hierarchy.hierarchy.levelCount)
    (child parent : WZ1VerticalTrapezoid)
    (hchild : child ∈ hierarchy.hierarchy.trapezoids level)
    (hnest : child.IsNumericallyNestedIn parent) :
    |child.affine child.left - parent.affine child.left| ≤ child.height + parent.height ∧
    |child.affine child.right - parent.affine child.right| ≤ child.height + parent.height := by
  have h_left_in : child.left ∈ child.core := by
    simp only [WZ1VerticalTrapezoid.core, Set.mem_Icc]
    exact ⟨le_refl child.left, le_of_lt child.left_lt_right⟩
  have h_right_in : child.right ∈ child.core := by
    simp only [WZ1VerticalTrapezoid.core, Set.mem_Icc]
    exact ⟨le_of_lt child.left_lt_right, le_refl child.right⟩
  exact ⟨hnest.2 child.left h_left_in, hnest.2 child.right h_right_in⟩

end CostBounds

/--
Convert an anchored Corollary 26 hierarchy into the level-indexed segment family
with all required certificates: membership, surjectivity, core equality, source
certificates, and disjoint supports.
-/
lemma wz1_corollary26_segments_from_hierarchy
    {delta sigma inputLoss hierarchyLoss : ℝ}
    {source : WZ1PlaninessGraininessPackage sigma inputLoss delta}
    (hierarchy : WZ1Corollary26AnchoredHierarchyPackage source hierarchyLoss)
    (hdelta : 0 < delta) (hdelta_one : delta ≤ 1) :
    ∃ (segments : Fin hierarchy.hierarchy.levelCount → Finset WZ1SegmentCorrection)
      (segmentFor : ∀ (level : Fin hierarchy.hierarchy.levelCount)
        (trapezoid : WZ1VerticalTrapezoid),
        trapezoid ∈ hierarchy.hierarchy.trapezoids level → WZ1SegmentCorrection),
      (∀ level trapezoid htrapezoid,
        segmentFor level trapezoid htrapezoid ∈ segments level) ∧
      (∀ level, ∀ segment ∈ segments level,
        ∃ trapezoid htrapezoid,
          segment = segmentFor level trapezoid htrapezoid) ∧
      (∀ level trapezoid htrapezoid,
        (segmentFor level trapezoid htrapezoid).core = trapezoid.core) ∧
      (∀ level trapezoid htrapezoid,
        Nonempty (WZ1Corollary26SegmentSource
          hierarchy.hierarchy level
          (segmentFor level trapezoid htrapezoid))) ∧
      (∀ level, ∀ segment ∈ segments level, ∀ other ∈ segments level,
        segment ≠ other → Disjoint segment.support other.support) := by
  let H := hierarchy.hierarchy
  let segments := levelSegments H hdelta
  let segmentFor : ∀ (level : Fin H.levelCount) (trapezoid : WZ1VerticalTrapezoid),
      trapezoid ∈ H.trapezoids level → WZ1SegmentCorrection :=
    fun level trapezoid htrapezoid => makeSegment H hdelta level trapezoid htrapezoid
  have h_mem : ∀ level trapezoid htrapezoid,
      segmentFor level trapezoid htrapezoid ∈ segments level := by
    intro level trapezoid htrapezoid
    have h_goal : ∃ (x : {t // t ∈ H.trapezoids level}),
        x ∈ (H.trapezoids level).attach ∧
        makeSegment H hdelta level x.val x.property = segmentFor level trapezoid htrapezoid := by
      refine ⟨⟨trapezoid, htrapezoid⟩, by simp, ?_⟩
      simp [segmentFor]
    simpa [segments, levelSegments, Finset.mem_image] using h_goal
  have h_surj : ∀ level, ∀ segment ∈ segments level,
      ∃ trapezoid htrapezoid, segment = segmentFor level trapezoid htrapezoid := by
    intro level segment hseg
    have h : ∃ (x : {t // t ∈ H.trapezoids level}),
        x ∈ (H.trapezoids level).attach ∧
        makeSegment H hdelta level x.val x.property = segment := by
      simpa [segments, levelSegments, Finset.mem_image] using hseg
    rcases h with ⟨p, _, h_eq⟩
    refine ⟨p.val, p.property, ?_⟩
    simpa [segmentFor] using h_eq.symm
  have h_core : ∀ level trapezoid htrapezoid,
      (segmentFor level trapezoid htrapezoid).core = trapezoid.core :=
    segment_core_eq H hdelta
  have h_source : ∀ level trapezoid htrapezoid,
      Nonempty (WZ1Corollary26SegmentSource H level
        (segmentFor level trapezoid htrapezoid)) := by
    intro level trapezoid htrapezoid
    exact ⟨segmentSourceCertificate H hdelta level trapezoid htrapezoid⟩
  have h_disjoint : ∀ level, ∀ segment ∈ segments level,
      ∀ other ∈ segments level, segment ≠ other →
        Disjoint segment.support other.support :=
    disjoint_support_at_level H hdelta
  exact ⟨segments, segmentFor, h_mem, h_surj, h_core, h_source, h_disjoint⟩

end Kakeya.Assouad
