import MyLeanRepo.Kakeya.CV.Isoperimetric.InnerMinkowski.Basic
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Tactic


/-!
# Almost-Everywhere Mean Value Theorem (Clean)

If `g : E n → ℝ` is Lipschitz and `‖fderiv g x‖ ≤ C` a.e. on an open convex set `s`,
then `g` is `C`-Lipschitz on `s`.
-/

open MeasureTheory Metric Set ENNReal Filter
open scoped MeasureTheory

namespace Geometry

variable {n : ℕ} [Nonempty (Fin n)]

/-- If g is Lipschitz and `‖fderiv g‖ ≤ C` a.e. on an open convex set s,
then g is C-Lipschitz on s. -/
theorem lipschitzOn_of_ae_norm_fderiv_le
    {g : E n → ℝ} {K : NNReal} (hg : LipschitzWith K g)
    {s : Set (E n)} (hs : Convex ℝ s) (hs_open : IsOpen s)
    {C : ℝ} (hC : 0 ≤ C)
    (h_bound : ∀ᵐ (x : E n) ∂volume.restrict s, ‖fderiv ℝ g x‖ ≤ C) :
    ∀ (x y : E n), x ∈ s → y ∈ s → ‖g y - g x‖ ≤ C * ‖y - x‖ := by
  -- Step 1: Construct measurable null superset N of the bad set within s
  have h_diff_ae : ∀ᵐ (x : E n), DifferentiableAt ℝ g x := hg.ae_differentiableAt
  have h_le : ae (volume.restrict s) ≤ ae volume := ae_mono Measure.restrict_le_self
  have h_diff_ae' : ∀ᵐ (x : E n) ∂volume.restrict s, DifferentiableAt ℝ g x :=
    h_diff_ae.filter_mono h_le
  have h_good_ae : ∀ᵐ (x : E n) ∂volume.restrict s,
      DifferentiableAt ℝ g x ∧ ‖fderiv ℝ g x‖ ≤ C := by
    filter_upwards [h_diff_ae', h_bound] with x h1 h2
    exact ⟨h1, h2⟩
  let bad : Set (E n) := {x | ¬(DifferentiableAt ℝ g x ∧ ‖fderiv ℝ g x‖ ≤ C)}
  have h_bad_null : (volume.restrict s) bad = 0 := by
    simpa [ae_iff, bad] using h_good_ae
  rcases MeasureTheory.exists_measurable_superset_of_null (h_bad_null) with
    ⟨N, hN_sub, hN_meas, hN_null⟩
  let N' := s ∩ N
  have hN'_meas : MeasurableSet N' := hs_open.measurableSet.inter hN_meas
  have hN'_null : volume N' = 0 := by
    have h : (volume.restrict s) N = 0 := hN_null
    have h2 : (volume.restrict s) N = volume (s ∩ N) := by
      rw [Measure.restrict_apply hN_meas] <;> simp [inter_comm]
    rw [h2] at h
    simpa [N'] using h
  have h_outside : ∀ (x : E n), x ∈ s → x ∉ N' →
      DifferentiableAt ℝ g x ∧ ‖fderiv ℝ g x‖ ≤ C := by
    intro x hxs hxn
    have h_x_notin_N : x ∉ N := by
      intro h
      exact hxn ⟨hxs, h⟩
    have h9 : x ∉ bad := by
      intro h10
      exact h_x_notin_N (hN_sub h10)
    simpa [bad] using h9

  intro x y hx hy
  by_cases hxy : y = x
  · rw [hxy]; simp [hC, norm_nonneg]
  · -- Direction and parameter
    let t : ℝ := ‖y - x‖
    have ht_pos : 0 < t := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
    let v : E n := (1 / t) • (y - x)
    have hv_norm : ‖v‖ = 1 := by
      calc ‖v‖
        = |1 / t| * ‖y - x‖ := by rw [norm_smul] <;> rfl
      _ = (1 / t) * t := by
        have h2 : |1 / t| = 1 / t := by rw [abs_of_pos] <;> positivity
        rw [h2] <;> ring
      _ = 1 := by field_simp [ht_pos.ne'] <;> ring
    have h_y_eq : x + t • v = y := by
      have h1 : t • v = y - x := by
        calc
          t • v = t • ((1 / t) • (y - x)) := by rfl
          _ = (t * (1 / t)) • (y - x) := by rw [smul_smul]
          _ = (1 : ℝ) • (y - x) := by
            have h3 : t * (1 / t) = 1 := by field_simp [ht_pos.ne'] <;> ring
            rw [h3]
          _ = y - x := by simp
      rw [h1] <;> abel

    -- Fubini: S = {(r,b) | b + r•v ∈ N'}, measure zero
    let S : Set (ℝ × E n) := {p | p.2 + p.1 • v ∈ N'}
    have hS_meas : MeasurableSet S := by
      have h_f : Measurable (fun p : ℝ × E n => p.2 + p.1 • v) := by fun_prop
      exact hN'_meas.preimage h_f
    have h_section_null : ∀ (r : ℝ), volume {b : E n | (r, b) ∈ S} = 0 := by
      intro r
      have h_eq : {b : E n | (r, b) ∈ S} = (fun b : E n => b + r • v) ⁻¹' N' := by
        ext b; simp [S]
      rw [h_eq]
      have hmp : MeasurePreserving (fun b : E n => b + r • v) :=
        measurePreserving_add_right volume (r • v)
      exact hmp.preimage_null hN'_null
    have hS_null : (volume.prod volume) S = 0 := by
      have h_eq : (volume.prod volume) S = ∫⁻ (r : ℝ), volume {b : E n | (r, b) ∈ S} := by
        rw [Measure.prod_apply hS_meas] <;> rfl
      rw [h_eq]
      have h3 : (fun r : ℝ => volume {b : E n | (r, b) ∈ S}) = 0 := by
        funext r; exact h_section_null r
      rw [h3]; exact lintegral_zero

    -- Swap to get sections indexed by b
    let S' : Set (E n × ℝ) := Prod.swap ⁻¹' S
    have hS'_meas : MeasurableSet S' := by
      have h : Measurable (Prod.swap : (E n × ℝ) → (ℝ × E n)) := by fun_prop
      exact hS_meas.preimage h
    have hS'_null : (volume.prod volume) S' = 0 := by
      have h : (volume.prod volume) S' = (volume.prod volume) S := by
        have hmp : MeasurePreserving (Prod.swap : (E n × ℝ) → (ℝ × E n)) :=
          MeasureTheory.Measure.measurePreserving_swap
        exact hmp.measure_preimage hS_meas.nullMeasurableSet
      rw [h, hS_null]
    have h_ae : ∀ᵐ (b : E n), volume {r : ℝ | (b, r) ∈ S'} = 0 := by
      have h_eq : (volume.prod volume) S' = ∫⁻ (b : E n), volume {r : ℝ | (b, r) ∈ S'} := by
        rw [Measure.prod_apply hS'_meas] <;> rfl
      rw [h_eq] at hS'_null
      have h : ∫⁻ (b : E n), volume {r : ℝ | (b, r) ∈ S'} = 0 := hS'_null
      have h_meas : Measurable (fun b : E n => volume {r : ℝ | (b, r) ∈ S'}) :=
        measurable_measure_prodMk_left hS'_meas
      have h_iff := @lintegral_eq_zero_iff' _ _ volume _ h_meas.aemeasurable
      have h2 : (fun b : E n => volume {r : ℝ | (b, r) ∈ S'}) =ᵐ[volume] 0 := h_iff.mp h
      exact h2
    have h_ae' : ∀ᵐ (b : E n), volume {r : ℝ | b + r • v ∈ N'} = 0 := by
      convert h_ae using 1
      ext r
      simp [S', S] <;> aesop

    -- For good b, bound on segment [b+s1•v, b+s2•v] if entirely in s, with s1 ≤ s2
    have h_good : ∀ (b : E n), volume {r : ℝ | b + r • v ∈ N'} = 0 →
        ∀ (s1 s2 : ℝ), s1 ≤ s2 → (∀ r ∈ Icc s1 s2, b + r • v ∈ s) →
          |g (b + s2 • v) - g (b + s1 • v)| ≤ C * (s2 - s1) := by
      intro b hb s1 s2 h_order hseg
      let h : ℝ → ℝ := fun r => g (b + r • v)
      have h_dir_norm : ∀ (r1 r2 : ℝ), ‖(b + r1 • v) - (b + r2 • v)‖ = |r1 - r2| := by
        intro r1 r2
        calc
          ‖(b + r1 • v) - (b + r2 • v)‖
            = ‖(r1 - r2) • v‖ := by simp [sub_smul] <;> abel
          _ = ‖(r1 - r2 : ℝ)‖ * ‖v‖ := by rw [norm_smul]
          _ = |r1 - r2| * ‖v‖ := by rw [Real.norm_eq_abs]
          _ = |r1 - r2| := by rw [hv_norm] <;> ring
      have h_dir_lip : LipschitzWith 1 (fun r : ℝ => b + r • v) := by
        intro r1 r2
        have h : dist (b + r1 • v) (b + r2 • v) = dist r1 r2 := by
          have h1 : dist (b + r1 • v) (b + r2 • v) = ‖(b + r1 • v) - (b + r2 • v)‖ := by
            rw [dist_eq_norm]
          have h2 : dist r1 r2 = |r1 - r2| := by
            rw [dist_eq_norm, Real.norm_eq_abs]
          rw [h1, h2, h_dir_norm r1 r2]
        rw [edist_dist, edist_dist, h] <;> simp
      have h_lip : LipschitzWith K h := by
        have h' : LipschitzWith (K * 1) h := hg.comp h_dir_lip
        have hK : K * 1 = K := by simp
        rw [hK] at h'
        exact h'
      have h_lip_on : LipschitzOnWith K h (uIcc s1 s2) := by
        intro r _ q _
        exact h_lip r q
      have h_ac : AbsolutelyContinuousOnInterval h s1 s2 :=
        h_lip_on.absolutelyContinuousOnInterval
      have h_deriv_bound : ∀ᵐ (r : ℝ) ∂volume.restrict (Icc s1 s2), |deriv h r| ≤ C := by
        have h1 : ∀ᵐ (r : ℝ), b + r • v ∉ N' := by simpa [ae_iff] using hb
        have h2 : ∀ᵐ (r : ℝ) ∂volume.restrict (Icc s1 s2), b + r • v ∉ N' :=
          h1.filter_mono (ae_mono Measure.restrict_le_self)
        have h3 : ∀ᵐ (r : ℝ) ∂volume.restrict (Icc s1 s2), r ∈ Icc s1 s2 :=
          ae_restrict_mem isCompact_Icc.measurableSet
        filter_upwards [h2, h3] with r hr2 hr3
        have h_in_s : b + r • v ∈ s := hseg r hr3
        have h_info := h_outside (b + r • v) h_in_s hr2
        have h_diff : DifferentiableAt ℝ g (b + r • v) := h_info.1
        have h_norm : ‖fderiv ℝ g (b + r • v)‖ ≤ C := h_info.2
        have h21 : HasDerivAt (fun r : ℝ => r • v) v r := by
          have h : HasDerivAt (fun r : ℝ => r • v) ((1 : ℝ) • v) r :=
            HasDerivAt.smul_const (hasDerivAt_id (x := r)) v
          have h2 : (1 : ℝ) • v = v := by simp
          rw [h2] at h
          exact h
        have h22 : HasDerivAt (fun r : ℝ => b + r • v) v r := h21.const_add b
        have h_fderiv : HasFDerivAt g (fderiv ℝ g (b + r • v)) (b + r • v) :=
          h_diff.hasFDerivAt
        have h_deriv : HasDerivAt h ((fderiv ℝ g (b + r • v)) v) r :=
          HasFDerivAt.comp_hasDerivAt r h_fderiv h22
        have h_eq : deriv h r = (fderiv ℝ g (b + r • v)) v := h_deriv.deriv
        rw [h_eq]
        have h4 : ‖(fderiv ℝ g (b + r • v)) v‖ ≤ ‖fderiv ℝ g (b + r • v)‖ * ‖v‖ :=
          (fderiv ℝ g (b + r • v)).le_opNorm v
        have h5 : ‖(fderiv ℝ g (b + r • v)) v‖ = |(fderiv ℝ g (b + r • v)) v| :=
          Real.norm_eq_abs _
        have h6 : |(fderiv ℝ g (b + r • v)) v| ≤ C := by
          calc
            |(fderiv ℝ g (b + r • v)) v|
              = ‖(fderiv ℝ g (b + r • v)) v‖ := h5.symm
            _ ≤ ‖fderiv ℝ g (b + r • v)‖ * ‖v‖ := h4
            _ = ‖fderiv ℝ g (b + r • v)‖ := by rw [hv_norm] <;> ring
            _ ≤ C := h_norm
        exact h6
      have h_ftc : ∫ (r : ℝ) in s1..s2, deriv h r = h s2 - h s1 :=
        h_ac.integral_deriv_eq_sub
      have h_int : IntervalIntegrable (deriv h) volume s1 s2 :=
        h_ac.intervalIntegrable_deriv
      have h_abs_int : IntervalIntegrable (fun r => |deriv h r|) volume s1 s2 :=
        h_int.abs
      have h_const_int : IntervalIntegrable (fun _ : ℝ => C) volume s1 s2 :=
        intervalIntegrable_const
      have h5 : |∫ (r : ℝ) in s1..s2, deriv h r| ≤ ∫ (r : ℝ) in s1..s2, |deriv h r| :=
        intervalIntegral.abs_integral_le_integral_abs h_order
      have h6 : ∫ (r : ℝ) in s1..s2, |deriv h r| ≤ ∫ (r : ℝ) in s1..s2, C :=
        intervalIntegral.integral_mono_ae_restrict h_order h_abs_int h_const_int h_deriv_bound
      have h7 : ∫ (r : ℝ) in s1..s2, C = C * (s2 - s1) := by
        simp [intervalIntegral.integral_const, h_order] <;> ring
      have h8 : |h s2 - h s1| ≤ C * (s2 - s1) := by
        rw [←h_ftc]
        exact le_trans h5 (h6.trans (le_of_eq h7))
      simpa [h] using h8

    -- Find open neighborhood U of x where segment property holds
    have h_near1 : ∀ᶠ (z : E n) in nhds x, z ∈ s := hs_open.mem_nhds hx
    have h_y_in_s : (x + t • v) ∈ s := by rw [h_y_eq] <;> exact hy
    have h_near2 : ∀ᶠ (z : E n) in nhds x, z + t • v ∈ s := by
      have h_cont : Continuous (fun z : E n => z + t • v) := by fun_prop
      exact h_cont.continuousAt.eventually (hs_open.mem_nhds h_y_in_s)
    have h_seg_nhds : ∀ᶠ (z : E n) in nhds x, ∀ r ∈ Icc (0 : ℝ) t, z + r • v ∈ s := by
      filter_upwards [h_near1, h_near2] with z hz1 hz2
      intro r hr
      have hr0 : 0 ≤ r := hr.1
      have hrt : r ≤ t := hr.2
      have h_a1 : 0 ≤ 1 - r / t := by
        have h : r / t ≤ 1 := by
          calc r / t ≤ t / t := by gcongr
            _ = 1 := by field_simp [ht_pos.ne']
        linarith
      have h_a2 : 0 ≤ r / t := by positivity
      have h6 : (r / t) • (z + t • v) = (r / t) • z + r • v := by
        rw [smul_add, smul_smul] <;> field_simp [ht_pos.ne'] <;> abel
      have h5 : z + r • v = (1 - r / t) • z + (r / t) • (z + t • v) := by
        have h_sum : (1 - r / t) • z + (r / t) • z = z := by
          simp [sub_smul, add_smul] <;> abel
        calc
          z + r • v
            = (1 - r / t) • z + (r / t) • z + r • v := by rw [h_sum] <;> abel
          _ = (1 - r / t) • z + ((r / t) • z + r • v) := by abel
          _ = (1 - r / t) • z + (r / t) • (z + t • v) := by rw [h6]
      rw [h5]
      exact hs hz1 hz2 h_a1 h_a2 (by ring)

    -- Extract open U from h_seg_nhds
    rcases _root_.mem_nhds_iff.mp h_seg_nhds with ⟨U, hU_sub, hU_open, hxU⟩
    have hU_seg : ∀ z ∈ U, ∀ r ∈ Icc (0 : ℝ) t, z + r • v ∈ s :=
      fun z hz => hU_sub hz

    -- For a.e. z in U, the bound holds
    have h_ae_U : ∀ᵐ (z : E n) ∂volume.restrict U,
        |g (z + t • v) - g z| ≤ C * t := by
      have h1 : ∀ᵐ (z : E n) ∂volume.restrict U, volume {r : ℝ | z + r • v ∈ N'} = 0 :=
        h_ae'.filter_mono (ae_mono Measure.restrict_le_self)
      have h2 : ∀ᵐ (z : E n) ∂volume.restrict U, z ∈ U :=
        ae_restrict_mem hU_open.measurableSet
      filter_upwards [h1, h2] with z hz1 hz2
      have h_res := h_good z hz1 0 t (by linarith) (hU_seg z hz2)
      have h_simp : g (z + (0 : ℝ) • v) = g z := by simp
      rw [h_simp] at h_res
      have h_final : C * (t - (0 : ℝ)) = C * t := by ring
      rw [h_final] at h_res
      exact h_res

    -- Continuous function bounded a.e. on open U is bounded everywhere on U
    let F : E n → ℝ := fun z => |g (z + t • v) - g z|
    have hF_cont : Continuous F := by
      exact Continuous.abs (hg.continuous.comp (by fun_prop) |>.sub hg.continuous)
    have h_bound_on_U : ∀ z ∈ U, F z ≤ C * t := by
      intro z hz
      by_contra h_strict
      have h_gt : C * t < F z := by linarith
      have h_nhds1 : ∀ᶠ (w : E n) in nhds z, C * t < F w :=
        hF_cont.continuousAt.eventually (IsOpen.mem_nhds isOpen_Ioi h_gt)
      have h_nhds2 : ∀ᶠ (w : E n) in nhds z, w ∈ U := hU_open.mem_nhds hz
      have h_both : ∀ᶠ (w : E n) in nhds z, C * t < F w ∧ w ∈ U :=
        h_nhds1.and h_nhds2
      rcases _root_.mem_nhds_iff.mp h_both with ⟨V, hV_sub, hV_open, hzV⟩
      have hV_nonempty : V.Nonempty := ⟨z, hzV⟩
      have hV_pos : 0 < volume V := hV_open.measure_pos volume hV_nonempty
      have hV_sub_U : V ⊆ U := by
        intro w hw
        exact (hV_sub hw).2
      have h_null : (volume.restrict U) V = 0 := by
        have h : ∀ᵐ (w : E n) ∂volume.restrict U, F w ≤ C * t := h_ae_U
        have h2 : (volume.restrict U) {w | ¬(F w ≤ C * t)} = 0 := by
          simpa [ae_iff] using h
        have h3 : V ⊆ {w : E n | ¬(F w ≤ C * t)} := by
          intro w hw
          have h4 : C * t < F w := (hV_sub hw).1
          exact not_le.mpr h4
        exact measure_mono_null h3 h2
      have h4 : (volume.restrict U) V = volume V := by
        rw [Measure.restrict_apply hV_open.measurableSet]
        have h5 : U ∩ V = V := inter_eq_right.mpr hV_sub_U
        have h6 : V ∩ U = V := by rw [inter_comm, h5]
        rw [h6]
      rw [h4] at h_null
      exact hV_pos.ne' h_null

    -- Conclude at x
    have h_final : F x ≤ C * t := h_bound_on_U x hxU
    have h_eq1 : F x = |g y - g x| := by
      simp [F, h_y_eq] <;> rfl
    have h_eq2 : ‖g y - g x‖ = |g y - g x| := by rfl
    rw [h_eq1] at h_final
    rw [h_eq2]
    exact h_final

end Geometry
