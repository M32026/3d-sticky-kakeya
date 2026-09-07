import MyLeanRepo.Kakeya.Assouad.WZ1.Statements
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Add

/-!
# WZ1 global grains from segment corrections

Closed proof of WZ1 Proposition 27: assemble compatible smooth segment
extensions into one normalized global grain direction.
-/

namespace Kakeya.Assouad

/-- Zero-order bound for one segment extension on `[-1,1]`.

Pick a point one unit left of the expanded support where the extension vanishes,
then apply the global derivative bound (MVT) over the distance to any point in
the support.  The distance is at most `x₂ - x₁ + 2 * buffer + 1`, matching
`valueCost`. -/
lemma segment_zero_order_bound {A : ℝ} (hA : 1 ≤ A)
    (segment : WZ1SegmentCorrection) (G : SlopeFunction)
    (h_support : ∀ x ∉ segment.support, G x = 0)
    (h_deriv : ∀ x : ℝ, |deriv G x| ≤ A * segment.firstCost) :
    ∀ z : ℝ, |G z| ≤ A * segment.valueCost := by
  let a : ℝ := segment.x₁ - segment.buffer - 1
  have ha_not_support : a ∉ segment.support := by
    intro h
    have h' : segment.x₁ - segment.buffer ≤ a ∧ a ≤ segment.x₂ + segment.buffer := by
      simpa [WZ1SegmentCorrection.support, Set.mem_Icc] using h
    linarith [segment.buffer_pos]
  have hGa : G a = 0 := h_support a ha_not_support
  have h_diff : ∀ x : ℝ, DifferentiableAt ℝ G x :=
    fun x => (G.contDiff.differentiable (by norm_num)).differentiableAt
  have hM_nonneg : 0 ≤ A * segment.firstCost := by
    have hA2 : 0 ≤ A := by linarith
    have hfc : 0 ≤ segment.firstCost := by
      unfold WZ1SegmentCorrection.firstCost
      have hbuf : 0 ≤ segment.buffer := by linarith [segment.buffer_pos]
      have hden : 0 < segment.x₂ - segment.x₁ := by linarith [segment.x₁_lt_x₂]
      positivity
    exact mul_nonneg hA2 hfc
  intro z
  by_cases hzs : z ∈ segment.support
  · -- z ∈ support: apply MVT from the left zero point
    have h_lip : |G z - G a| ≤ (A * segment.firstCost) * |z - a| :=
      Convex.norm_image_sub_le_of_norm_deriv_le
        (fun x _ => h_diff x)
        (fun x _ => h_deriv x)
        convex_univ (by trivial) (by trivial)
    have h_pos : 0 ≤ z - a := by
      simp only [WZ1SegmentCorrection.support, Set.mem_Icc] at hzs
      simp [a]; linarith [segment.buffer_pos]
    have h_dist : z - a ≤ segment.x₂ - segment.x₁ + 2 * segment.buffer + 1 := by
      simp only [WZ1SegmentCorrection.support, Set.mem_Icc] at hzs
      simp [a] at hzs ⊢; linarith
    have h_abs : |z - a| = z - a := abs_of_nonneg h_pos
    calc |G z|
      = |G z - G a| := by simp [hGa]
    _ ≤ (A * segment.firstCost) * |z - a| := h_lip
    _ = (A * segment.firstCost) * (z - a) := by rw [h_abs]
    _ ≤ (A * segment.firstCost) * (segment.x₂ - segment.x₁ + 2 * segment.buffer + 1) := by
        gcongr
    _ = A * segment.valueCost := by
        simp [WZ1SegmentCorrection.valueCost]; ring
  · -- z ∉ support: G z = 0
    have hGz : G z = 0 := h_support z hzs
    rw [hGz]
    have hvc_nonneg : 0 ≤ A * segment.valueCost := by
      have hA2 : 0 ≤ A := by linarith
      have hvc : 0 ≤ segment.valueCost := by
        unfold WZ1SegmentCorrection.valueCost WZ1SegmentCorrection.firstCost
        have hbuf : 0 ≤ segment.buffer := by linarith [segment.buffer_pos]
        have hden : 0 < segment.x₂ - segment.x₁ := by linarith [segment.x₁_lt_x₂]
        positivity
      exact mul_nonneg hA2 hvc
    simpa using hvc_nonneg

/-- On a core-or-off-support point, the extension equals the prescribed segment value. -/
lemma segment_value_equality (segment : WZ1SegmentCorrection) (G : SlopeFunction)
    (h_affine : ∀ x ∈ segment.core, G x = segment.affine x)
    (h_support : ∀ x ∉ segment.support, G x = 0)
    {z : ℝ} (h : z ∈ segment.core ∨ z ∉ segment.support) :
    G z = segment.value z := by
  cases h with
  | inl hcore =>
    have h1 : G z = segment.affine z := h_affine z hcore
    have h2 : segment.value z = segment.affine z := by
      simp [WZ1SegmentCorrection.value, hcore]
    rw [h1, h2]
  | inr hnotsup =>
    have h1 : G z = 0 := h_support z hnotsup
    have hnotcore : z ∉ segment.core := by
      intro hc
      have h_core_sub_support : segment.core ⊆ segment.support := by
        intro x hx
        have h4 : segment.x₁ ≤ x ∧ x ≤ segment.x₂ := by
          simpa [WZ1SegmentCorrection.core, Set.mem_Icc] using hx
        simp only [WZ1SegmentCorrection.support, Set.mem_Icc]
        constructor <;> linarith [segment.buffer_pos]
      exact hnotsup (h_core_sub_support hc)
    have h2 : segment.value z = 0 := by
      simp [WZ1SegmentCorrection.value, hnotcore]
    rw [h1, h2]

theorem wz1_global_grains_from_segments : WZ1GlobalGrainsFromSegmentsStatement := by
  intro h_ext
  rcases h_ext with ⟨A, hA1, h_ext_prop⟩
  refine' ⟨A, hA1, _⟩
  intro delta sigma F Y C segments h_disjoint h_core_or_off h_value_cost h_first_cost h_second_cost h_ad

  -- For each segment, obtain a smooth extension
  let h_ext_seg : ∀ (segment : WZ1SegmentCorrection),
      ∃ G : SlopeFunction,
        (∀ x ∈ segment.core, G x = segment.affine x) ∧
        (∀ x ∉ segment.support, G x = 0) ∧
        (∀ x : ℝ, |deriv G x| ≤ A * segment.firstCost) ∧
        (∀ x : ℝ, |deriv (deriv G) x| ≤ A * segment.secondCost) := by
    intro segment
    exact h_ext_prop segment.x₁ segment.x₂ segment.y₁ segment.y₂ segment.buffer
      segment.x₁_lt_x₂ segment.buffer_pos

  classical
  let G : WZ1SegmentCorrection → SlopeFunction := fun segment =>
    Classical.choose (h_ext_seg segment)
  let hG : ∀ segment,
      (∀ x ∈ segment.core, G segment x = segment.affine x) ∧
      (∀ x ∉ segment.support, G segment x = 0) ∧
      (∀ x : ℝ, |deriv (G segment) x| ≤ A * segment.firstCost) ∧
      (∀ x : ℝ, |deriv (deriv (G segment)) x| ≤ A * segment.secondCost) :=
    fun segment => Classical.choose_spec (h_ext_seg segment)

  let hG_affine : ∀ segment, ∀ x ∈ segment.core, G segment x = segment.affine x :=
    fun segment => (hG segment).1
  let hG_support : ∀ segment, ∀ x ∉ segment.support, G segment x = 0 :=
    fun segment => (hG segment).2.1
  let hG_deriv1 : ∀ segment, ∀ x : ℝ, |deriv (G segment) x| ≤ A * segment.firstCost :=
    fun segment => (hG segment).2.2.1
  let hG_deriv2 : ∀ segment, ∀ x : ℝ, |deriv (deriv (G segment)) x| ≤ A * segment.secondCost :=
    fun segment => (hG segment).2.2.2

  -- Define slope as finite sum of extensions
  let g : ℝ → ℝ := fun z => ∑ segment ∈ segments, G segment z
  have hg_contDiff : ContDiff ℝ 2 g := by
    apply ContDiff.sum
    intro segment _
    exact (G segment).contDiff

  let slope : SlopeFunction := ⟨g, hg_contDiff⟩

  -- First derivative commutes with finite sum
  have h_deriv1_sum : ∀ z : ℝ, deriv g z = ∑ segment ∈ segments, deriv (G segment) z := by
    intro z
    rw [deriv_fun_sum]
    intro segment _
    exact ((G segment).contDiff.differentiable (by norm_num)).differentiableAt

  -- Second derivative commutes with finite sum
  have h_deriv2_sum : ∀ z : ℝ, deriv (deriv g) z = ∑ segment ∈ segments, deriv (deriv (G segment)) z := by
    intro z
    have h_eq1 : deriv g = fun z : ℝ => ∑ segment ∈ segments, deriv (G segment) z := by
      funext z
      exact h_deriv1_sum z
    rw [h_eq1]
    rw [deriv_fun_sum]
    intro segment _
    have hcd : ContDiff ℝ 2 (G segment) := (G segment).contDiff
    have h : ContDiff ℝ 1 (deriv (G segment)) := hcd.deriv'
    exact (h.differentiable (by norm_num)).differentiableAt

  -- Zero-order bound for each segment
  have h_zero_bound : ∀ segment ∈ segments, ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      |G segment z| ≤ A * segment.valueCost := by
    intro segment hseg
    intro z _hz
    exact segment_zero_order_bound hA1 segment (G segment)
      (hG_support segment) (hG_deriv1 segment) z

  -- Prove IsNormalized: |slope| ≤ 1, |deriv slope| ≤ 1, |deriv² slope| ≤ 1 on [-1,1]
  have h_normalized : slope.IsNormalized := by
    intro z hz
    have hA_pos : 0 < A := by linarith
    constructor
    · -- Zero-order bound
      calc |slope z|
        = |∑ segment ∈ segments, G segment z| := by rfl
      _ ≤ ∑ segment ∈ segments, |G segment z| := Finset.abs_sum_le_sum_abs (fun segment => G segment z) segments
      _ ≤ ∑ segment ∈ segments, (A * segment.valueCost) := by
          apply Finset.sum_le_sum
          intro segment hseg
          exact h_zero_bound segment hseg z hz
      _ = A * ∑ segment ∈ segments, segment.valueCost := by rw [Finset.mul_sum]
      _ ≤ A * (1 / A) := by gcongr
      _ = 1 := by field_simp [hA_pos.ne']
    constructor
    · -- First derivative bound
      calc |deriv slope z|
        = |deriv g z| := by rfl
      _ = |∑ segment ∈ segments, deriv (G segment) z| := by rw [h_deriv1_sum z]
      _ ≤ ∑ segment ∈ segments, |deriv (G segment) z| := Finset.abs_sum_le_sum_abs (fun segment => deriv (G segment) z) segments
      _ ≤ ∑ segment ∈ segments, (A * segment.firstCost) := by
          apply Finset.sum_le_sum
          intro segment hseg
          exact hG_deriv1 segment z
      _ = A * ∑ segment ∈ segments, segment.firstCost := by rw [Finset.mul_sum]
      _ ≤ A * (1 / A) := by gcongr
      _ = 1 := by field_simp [hA_pos.ne']
    · -- Second derivative bound
      calc |deriv (deriv slope) z|
        = |deriv (deriv g) z| := by rfl
      _ = |∑ segment ∈ segments, deriv (deriv (G segment)) z| := by rw [h_deriv2_sum z]
      _ ≤ ∑ segment ∈ segments, |deriv (deriv (G segment)) z| := Finset.abs_sum_le_sum_abs (fun segment => deriv (deriv (G segment)) z) segments
      _ ≤ ∑ segment ∈ segments, (A * segment.secondCost) := by
          apply Finset.sum_le_sum
          intro segment hseg
          exact hG_deriv2 segment z
      _ = A * ∑ segment ∈ segments, segment.secondCost := by rw [Finset.mul_sum]
      _ ≤ A * (1 / A) := by gcongr
      _ = 1 := by field_simp [hA_pos.ne']

  -- Extract AD parameter conditions from h_ad at z = 0
  have h_ad0 := h_ad 0 (by norm_num)
  rcases h_ad0 with ⟨hδ_pos, hα_pos, hα_le_one, hC_one, _, _⟩

  -- Transport the paper-faithful slab AD condition to the smooth slope.
  have h_global_slab_ad : HasGlobalSlabAD Y slope sigma C := by
    intro z hz
    apply (h_ad z hz).mono
    rintro value ⟨p, hp, rfl⟩
    have hp_height : p (2 : Fin 3) ∈ Set.Icc (-1 : ℝ) 1 := hp.2
    have h_all :
        ∀ segment ∈ segments,
          p (2 : Fin 3) ∈ segment.core ∨
            p (2 : Fin 3) ∉ segment.support := by
      rcases h_core_or_off (p (2 : Fin 3)) hp_height with h_all | h_empty
      · exact h_all
      · exfalso
        have hp_slice :
            p ∈ horizontalSlice Y.union (p (2 : Fin 3)) :=
          ⟨hp.1.1, rfl⟩
        rw [h_empty] at hp_slice
        exact hp_slice
    have h_sum_eq :
        slope (p (2 : Fin 3)) =
          ∑ segment ∈ segments, segment.value (p (2 : Fin 3)) := by
      change
        (∑ segment ∈ segments, G segment (p (2 : Fin 3))) =
          ∑ segment ∈ segments, segment.value (p (2 : Fin 3))
      apply Finset.sum_congr rfl
      intro segment hsegment
      exact
        segment_value_equality segment (G segment)
          (hG_affine segment) (hG_support segment)
          (h_all segment hsegment)
    refine ⟨p, hp, ?_⟩
    simp only [globalGrainProjection]
    rw [h_sum_eq]

  -- Assemble the global grain data structure
  exact ⟨slope, h_normalized, h_global_slab_ad⟩

end Kakeya.Assouad
