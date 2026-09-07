import MyLeanRepo.Kakeya.Assouad.WZ1.GlobalGrainsFromSegments
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Add

/-!
# Raw global grains from multiscale corrections

Closed proof of WZ1 Proposition 27.  Level-indexed smooth segment extensions
are summed into one raw `C²` slope; the active cost bounds control its value
and first two derivatives before Proposition 21 normalization.
-/

namespace Kakeya.Assouad

/-- Carrier-independent Proposition 27 output before choosing the global-AD
interface.  The active-slice identity is the common input to both the legacy
slab adapter and the pure exact-slice adapter. -/
structure WZ1RawGlobalSlopeCore
    {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    (Y : Kakeya.Streamlined.TubeShading F)
    (sourceValue : ℝ → ℝ)
    (rawLoss extensionConstant : ℝ) where
  slope : SlopeFunction
  extensionConstant_one : 1 ≤ extensionConstant
  value_bound :
    ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      |slope z| ≤ extensionConstant * Real.rpow delta (-rawLoss)
  first_derivative_bound :
    ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      |deriv slope z| ≤ extensionConstant * Real.rpow delta (-rawLoss)
  second_derivative_bound :
    ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      |deriv (deriv slope) z| ≤
        extensionConstant * Real.rpow delta (-rawLoss)
  global_value_bound :
    ∀ z : ℝ,
      |slope z| ≤ extensionConstant * Real.rpow delta (-rawLoss)
  global_first_derivative_bound :
    ∀ z : ℝ,
      |deriv slope z| ≤ extensionConstant * Real.rpow delta (-rawLoss)
  global_second_derivative_bound :
    ∀ z : ℝ,
      |deriv (deriv slope) z| ≤
        extensionConstant * Real.rpow delta (-rawLoss)
  slope_on_active :
    ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      horizontalSlice Y.union z ≠ ∅ →
        slope z = sourceValue z

/-- A smooth segment extension has zero derivative off its closed support. -/
lemma wz1SegmentDeriv_eq_zero_off_support
    {segment : WZ1SegmentCorrection} {G : SlopeFunction}
    (h_support : ∀ x ∉ segment.support, G x = 0)
    {z : ℝ} (hz : z ∉ segment.support) :
    deriv G z = 0 := by
  have h_open : IsOpen (segment.supportᶜ) := isClosed_Icc.isOpen_compl
  have h_nhd : segment.supportᶜ ∈ nhds z := h_open.mem_nhds hz
  have h_eventually : G =ᶠ[nhds z] 0 := by
    filter_upwards [h_nhd] with x hx
    exact h_support x hx
  have h_deriv : HasDerivAt G 0 z :=
    (hasDerivAt_const z (0 : ℝ)).congr_of_eventuallyEq h_eventually
  exact h_deriv.deriv

/-- A `C²` segment extension has zero second derivative off its support. -/
lemma wz1SegmentSecondDeriv_eq_zero_off_support
    {segment : WZ1SegmentCorrection} {G : SlopeFunction}
    (h_support : ∀ x ∉ segment.support, G x = 0)
    {z : ℝ} (hz : z ∉ segment.support) :
    deriv (deriv G) z = 0 := by
  have h_open : IsOpen (segment.supportᶜ) := isClosed_Icc.isOpen_compl
  have h_nhd : segment.supportᶜ ∈ nhds z := h_open.mem_nhds hz
  have h_eventually : deriv G =ᶠ[nhds z] 0 := by
    filter_upwards [h_nhd] with y hy
    exact wz1SegmentDeriv_eq_zero_off_support h_support hy
  have h_deriv : HasDerivAt (deriv G) 0 z :=
    (hasDerivAt_const z (0 : ℝ)).congr_of_eventuallyEq h_eventually
  exact h_deriv.deriv

theorem wz1_raw_global_slope_from_multiscale_data
    (A : ℝ)
    (hA : WZ1SmoothSegmentExtensionAtConstantStatement A)
    {delta rawLoss : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    (corr : WZ1MultiscaleSlopeCorrectionCoreData Y rawLoss) :
    Nonempty
      (WZ1RawGlobalSlopeCore Y
        (wz1MultiscaleSegmentValue corr.levelCount corr.segments)
        rawLoss A) := by
  rcases hA with ⟨hA1, h_ext_prop⟩
  let h_ext_seg : ∀ segment : WZ1SegmentCorrection,
      ∃ G : SlopeFunction,
        (∀ x ∈ segment.core, G x = segment.affine x) ∧
        (∀ x ∉ segment.support, G x = 0) ∧
        (∀ x : ℝ, |deriv G x| ≤ A * segment.firstCost) ∧
        (∀ x : ℝ,
          |deriv (deriv G) x| ≤ A * segment.secondCost) := by
    intro segment
    exact
      h_ext_prop segment.x₁ segment.x₂ segment.y₁ segment.y₂
        segment.buffer segment.x₁_lt_x₂ segment.buffer_pos
  classical
  let G : WZ1SegmentCorrection → SlopeFunction := fun segment =>
    Classical.choose (h_ext_seg segment)
  let hG : ∀ segment,
      (∀ x ∈ segment.core, G segment x = segment.affine x) ∧
      (∀ x ∉ segment.support, G segment x = 0) ∧
      (∀ x : ℝ,
        |deriv (G segment) x| ≤ A * segment.firstCost) ∧
      (∀ x : ℝ,
        |deriv (deriv (G segment)) x| ≤ A * segment.secondCost) :=
    fun segment => Classical.choose_spec (h_ext_seg segment)
  let hG_affine :
      ∀ segment, ∀ x ∈ segment.core,
        G segment x = segment.affine x :=
    fun segment => (hG segment).1
  let hG_support :
      ∀ segment, ∀ x ∉ segment.support, G segment x = 0 :=
    fun segment => (hG segment).2.1
  let hG_deriv1 :
      ∀ segment, ∀ x : ℝ,
        |deriv (G segment) x| ≤ A * segment.firstCost :=
    fun segment => (hG segment).2.2.1
  let hG_deriv2 :
      ∀ segment, ∀ x : ℝ,
        |deriv (deriv (G segment)) x| ≤ A * segment.secondCost :=
    fun segment => (hG segment).2.2.2
  let g : ℝ → ℝ := fun z =>
    ∑ level : Fin corr.levelCount,
      ∑ segment ∈ corr.segments level, G segment z
  have h_inner_contDiff :
      ∀ level : Fin corr.levelCount,
        ContDiff ℝ 2
          (fun x : ℝ =>
            ∑ segment ∈ corr.segments level, G segment x) := by
    intro level
    apply ContDiff.sum
    intro segment _
    exact (G segment).contDiff
  have hg_contDiff : ContDiff ℝ 2 g := by
    apply ContDiff.sum
    intro level _
    exact h_inner_contDiff level
  let slope : SlopeFunction := ⟨g, hg_contDiff⟩
  have h_deriv1_sum : ∀ z : ℝ,
      deriv g z =
        ∑ level : Fin corr.levelCount,
          ∑ segment ∈ corr.segments level,
            deriv (G segment) z := by
    intro z
    have h_diff1 :
        ∀ i : Fin corr.levelCount,
          i ∈ (Finset.univ : Finset (Fin corr.levelCount)) →
            DifferentiableAt ℝ
              (fun x : ℝ =>
                ∑ segment ∈ corr.segments i, G segment x) z := by
      intro i _
      have hdiff : Differentiable ℝ
          (fun x : ℝ =>
            ∑ segment ∈ corr.segments i, G segment x) :=
        (h_inner_contDiff i).differentiable (by norm_num)
      exact hdiff.differentiableAt
    have h_step1 :
        deriv g z =
          ∑ level : Fin corr.levelCount,
            deriv
              (fun x : ℝ =>
                ∑ segment ∈ corr.segments level, G segment x) z :=
      deriv_fun_sum h_diff1
    rw [h_step1]
    apply Finset.sum_congr rfl
    intro level _
    have h_diff2 :
        ∀ segment ∈ corr.segments level,
          DifferentiableAt ℝ (G segment) z := by
      intro segment _
      exact
        ((G segment).contDiff.differentiable (by norm_num)).differentiableAt
    exact deriv_fun_sum h_diff2
  have h_deriv2_sum : ∀ z : ℝ,
      deriv (deriv g) z =
        ∑ level : Fin corr.levelCount,
          ∑ segment ∈ corr.segments level,
            deriv (deriv (G segment)) z := by
    intro z
    have h_eq1 :
        deriv g = fun z : ℝ =>
          ∑ level : Fin corr.levelCount,
            ∑ segment ∈ corr.segments level,
              deriv (G segment) z := by
      funext z
      exact h_deriv1_sum z
    rw [h_eq1]
    have h_diff1 :
        ∀ i : Fin corr.levelCount,
          i ∈ (Finset.univ : Finset (Fin corr.levelCount)) →
            DifferentiableAt ℝ
              (fun x : ℝ =>
                ∑ segment ∈ corr.segments i,
                  deriv (G segment) x) z := by
      intro i _
      have hcd : ContDiff ℝ 1
          (fun x : ℝ =>
            ∑ segment ∈ corr.segments i,
              deriv (G segment) x) := by
        apply ContDiff.sum
        intro segment _
        exact (G segment).contDiff.deriv'
      have hdiff : Differentiable ℝ
          (fun x : ℝ =>
            ∑ segment ∈ corr.segments i,
              deriv (G segment) x) :=
        hcd.differentiable (by norm_num)
      exact hdiff.differentiableAt
    have h_step1 :
        deriv
            (fun z : ℝ =>
              ∑ level : Fin corr.levelCount,
                ∑ segment ∈ corr.segments level,
                  deriv (G segment) z) z =
          ∑ level : Fin corr.levelCount,
            deriv
              (fun x : ℝ =>
                ∑ segment ∈ corr.segments level,
                  deriv (G segment) x) z :=
      deriv_fun_sum h_diff1
    rw [h_step1]
    apply Finset.sum_congr rfl
    intro level _
    have h_diff2 :
        ∀ segment ∈ corr.segments level,
          DifferentiableAt ℝ (deriv (G segment)) z := by
      intro segment _
      have hcd : ContDiff ℝ 1 (deriv (G segment)) :=
        (G segment).contDiff.deriv'
      have hdiff : Differentiable ℝ (deriv (G segment)) :=
        hcd.differentiable (by norm_num)
      exact hdiff.differentiableAt
    exact deriv_fun_sum h_diff2
  have h_zero_bound :
      ∀ segment, ∀ z : ℝ,
        |G segment z| ≤ A * segment.valueCost := by
    intro segment
    exact
      segment_zero_order_bound hA1 segment (G segment)
        (hG_support segment) (hG_deriv1 segment)
  have h_filter_value :
      ∀ (level : Fin corr.levelCount) (z : ℝ),
        ∑ segment ∈ corr.segments level, |G segment z| =
          ∑ segment ∈
              (corr.segments level).filter
                (fun segment => z ∈ segment.support),
            |G segment z| := by
    intro level z
    have h :
        ∑ segment ∈ corr.segments level, |G segment z| =
          ∑ segment ∈ corr.segments level,
            if z ∈ segment.support then |G segment z| else 0 := by
      apply Finset.sum_congr rfl
      intro segment _
      by_cases hzs : z ∈ segment.support
      · simp [hzs]
      · have hzero : |G segment z| = 0 := by
          have hGz : G segment z = 0 := hG_support segment z hzs
          rw [hGz]
          simp
        simp [hzs, hzero]
    rw [h, Finset.sum_filter]
  have h_filter_deriv1 :
      ∀ (level : Fin corr.levelCount) (z : ℝ),
        ∑ segment ∈ corr.segments level,
            |deriv (G segment) z| =
          ∑ segment ∈
              (corr.segments level).filter
                (fun segment => z ∈ segment.support),
            |deriv (G segment) z| := by
    intro level z
    have h :
        ∑ segment ∈ corr.segments level,
            |deriv (G segment) z| =
          ∑ segment ∈ corr.segments level,
            if z ∈ segment.support then
              |deriv (G segment) z|
            else 0 := by
      apply Finset.sum_congr rfl
      intro segment _
      by_cases hzs : z ∈ segment.support
      · simp [hzs]
      · have hzero : |deriv (G segment) z| = 0 := by
          have hder :
              deriv (G segment) z = 0 :=
            wz1SegmentDeriv_eq_zero_off_support
              (hG_support segment) hzs
          rw [hder]
          simp
        simp [hzs, hzero]
    rw [h, Finset.sum_filter]
  have h_filter_deriv2 :
      ∀ (level : Fin corr.levelCount) (z : ℝ),
        ∑ segment ∈ corr.segments level,
            |deriv (deriv (G segment)) z| =
          ∑ segment ∈
              (corr.segments level).filter
                (fun segment => z ∈ segment.support),
            |deriv (deriv (G segment)) z| := by
    intro level z
    have h :
        ∑ segment ∈ corr.segments level,
            |deriv (deriv (G segment)) z| =
          ∑ segment ∈ corr.segments level,
            if z ∈ segment.support then
              |deriv (deriv (G segment)) z|
            else 0 := by
      apply Finset.sum_congr rfl
      intro segment _
      by_cases hzs : z ∈ segment.support
      · simp [hzs]
      · have hzero : |deriv (deriv (G segment)) z| = 0 := by
          have hder :
              deriv (deriv (G segment)) z = 0 :=
            wz1SegmentSecondDeriv_eq_zero_off_support
              (hG_support segment) hzs
          rw [hder]
          simp
        simp [hzs, hzero]
    rw [h, Finset.sum_filter]
  have h_value_bound :
      ∀ z : ℝ,
        |slope z| ≤ A * Real.rpow delta (-rawLoss) := by
    intro z
    calc
      |slope z| =
          |∑ level : Fin corr.levelCount,
            ∑ segment ∈ corr.segments level, G segment z| := by
              rfl
      _ ≤ ∑ level : Fin corr.levelCount,
            |∑ segment ∈ corr.segments level, G segment z| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ level : Fin corr.levelCount,
            ∑ segment ∈ corr.segments level, |G segment z| := by
          apply Finset.sum_le_sum
          intro level _
          exact Finset.abs_sum_le_sum_abs _ _
      _ = ∑ level : Fin corr.levelCount,
            ∑ segment ∈
                (corr.segments level).filter
                  (fun segment => z ∈ segment.support),
              |G segment z| := by
          apply Finset.sum_congr rfl
          intro level _
          exact h_filter_value level z
      _ ≤ ∑ level : Fin corr.levelCount,
            ∑ segment ∈
                (corr.segments level).filter
                  (fun segment => z ∈ segment.support),
              A * segment.valueCost := by
          apply Finset.sum_le_sum
          intro level _
          apply Finset.sum_le_sum
          intro segment _
          exact h_zero_bound segment z
      _ = A * wz1ActiveSegmentValueCost
            corr.levelCount corr.segments z := by
          simp [wz1ActiveSegmentValueCost, Finset.mul_sum]
      _ ≤ A * Real.rpow delta (-rawLoss) := by
          gcongr
          exact corr.active_value_cost z
  have h_first_bound :
      ∀ z : ℝ,
        |deriv slope z| ≤ A * Real.rpow delta (-rawLoss) := by
    intro z
    calc
      |deriv slope z| = |deriv g z| := by rfl
      _ =
          |∑ level : Fin corr.levelCount,
            ∑ segment ∈ corr.segments level,
              deriv (G segment) z| := by
          rw [h_deriv1_sum z]
      _ ≤ ∑ level : Fin corr.levelCount,
            |∑ segment ∈ corr.segments level,
              deriv (G segment) z| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ level : Fin corr.levelCount,
            ∑ segment ∈ corr.segments level,
              |deriv (G segment) z| := by
          apply Finset.sum_le_sum
          intro level _
          exact Finset.abs_sum_le_sum_abs _ _
      _ = ∑ level : Fin corr.levelCount,
            ∑ segment ∈
                (corr.segments level).filter
                  (fun segment => z ∈ segment.support),
              |deriv (G segment) z| := by
          apply Finset.sum_congr rfl
          intro level _
          exact h_filter_deriv1 level z
      _ ≤ ∑ level : Fin corr.levelCount,
            ∑ segment ∈
                (corr.segments level).filter
                  (fun segment => z ∈ segment.support),
              A * segment.firstCost := by
          apply Finset.sum_le_sum
          intro level _
          apply Finset.sum_le_sum
          intro segment _
          exact hG_deriv1 segment z
      _ = A * wz1ActiveSegmentFirstCost
            corr.levelCount corr.segments z := by
          simp [wz1ActiveSegmentFirstCost, Finset.mul_sum]
      _ ≤ A * Real.rpow delta (-rawLoss) := by
          gcongr
          exact corr.active_first_cost z
  have h_second_bound :
      ∀ z : ℝ,
        |deriv (deriv slope) z| ≤
          A * Real.rpow delta (-rawLoss) := by
    intro z
    calc
      |deriv (deriv slope) z| = |deriv (deriv g) z| := by rfl
      _ =
          |∑ level : Fin corr.levelCount,
            ∑ segment ∈ corr.segments level,
              deriv (deriv (G segment)) z| := by
          rw [h_deriv2_sum z]
      _ ≤ ∑ level : Fin corr.levelCount,
            |∑ segment ∈ corr.segments level,
              deriv (deriv (G segment)) z| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ level : Fin corr.levelCount,
            ∑ segment ∈ corr.segments level,
              |deriv (deriv (G segment)) z| := by
          apply Finset.sum_le_sum
          intro level _
          exact Finset.abs_sum_le_sum_abs _ _
      _ = ∑ level : Fin corr.levelCount,
            ∑ segment ∈
                (corr.segments level).filter
                  (fun segment => z ∈ segment.support),
              |deriv (deriv (G segment)) z| := by
          apply Finset.sum_congr rfl
          intro level _
          exact h_filter_deriv2 level z
      _ ≤ ∑ level : Fin corr.levelCount,
            ∑ segment ∈
                (corr.segments level).filter
                  (fun segment => z ∈ segment.support),
              A * segment.secondCost := by
          apply Finset.sum_le_sum
          intro level _
          apply Finset.sum_le_sum
          intro segment _
          exact hG_deriv2 segment z
      _ = A * wz1ActiveSegmentSecondCost
            corr.levelCount corr.segments z := by
          simp [wz1ActiveSegmentSecondCost, Finset.mul_sum]
      _ ≤ A * Real.rpow delta (-rawLoss) := by
          gcongr
          exact corr.active_second_cost z
  have h_slope_on_active :
      ∀ z ∈ Set.Icc (-1 : ℝ) 1,
        horizontalSlice Y.union z ≠ ∅ →
          slope z = wz1MultiscaleSegmentValue
            corr.levelCount corr.segments z := by
    intro z hz hactive
    have h_all :
        ∀ (level : Fin corr.levelCount)
          (segment : WZ1SegmentCorrection),
          segment ∈ corr.segments level →
            z ∈ segment.core ∨ z ∉ segment.support := by
      rcases corr.core_or_off_support z hz with h_all | h_empty
      · exact h_all
      · exfalso
        rw [h_empty] at hactive
        exact hactive rfl
    change
      (∑ level : Fin corr.levelCount,
        ∑ segment ∈ corr.segments level, G segment z) =
        ∑ level : Fin corr.levelCount,
          ∑ segment ∈ corr.segments level, segment.value z
    apply Finset.sum_congr rfl
    intro level _
    apply Finset.sum_congr rfl
    intro segment hsegment
    exact
      segment_value_equality segment (G segment)
        (hG_affine segment) (hG_support segment)
        (h_all level segment hsegment)
  exact
    ⟨slope, hA1, (fun z _ => h_value_bound z),
      (fun z _ => h_first_bound z), (fun z _ => h_second_bound z),
      h_value_bound, h_first_bound, h_second_bound, h_slope_on_active⟩

theorem wz1_raw_global_grains_from_multiscale_data
    (A : ℝ)
    (hA : WZ1SmoothSegmentExtensionAtConstantStatement A)
    {delta sigma rawLoss : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    {C : ENNReal}
    (corr : WZ1MultiscaleSlopeCorrectionData Y sigma C rawLoss) :
    Nonempty (WZ1RawGlobalGrainData Y sigma C rawLoss A) := by
  rcases wz1_raw_global_slope_from_multiscale_data A hA corr.toCore with ⟨core⟩
  have hglobal : HasGlobalSlabAD Y core.slope sigma C := by
    intro z hz
    apply (corr.global_slab_ad z hz).mono
    rintro value ⟨point, hpoint, rfl⟩
    have hheight : point 2 ∈ Set.Icc (-1 : ℝ) 1 := hpoint.2
    have hactive : horizontalSlice Y.union (point 2) ≠ ∅ := by
      exact Set.nonempty_iff_ne_empty.mp ⟨point, hpoint.1.1, rfl⟩
    refine ⟨point, hpoint, ?_⟩
    simp only [globalGrainProjection]
    rw [core.slope_on_active (point 2) hheight hactive]
    rfl
  exact
    ⟨core.slope, core.extensionConstant_one, core.value_bound,
      core.first_derivative_bound, core.second_derivative_bound, hglobal⟩

theorem wz1_raw_global_grains_from_multiscale_corrections :
    WZ1RawGlobalGrainsFromMultiscaleCorrectionsStatement := by
  intro A hA
  intro sigma inputLoss outputLoss delta source package
  exact wz1_raw_global_grains_from_multiscale_data
    A hA package.corrections

end Kakeya.Assouad
