import MyLeanRepo.Kakeya.CV.Isoperimetric.Perimeter.Basic
import MyLeanRepo.Kakeya.CV.Isoperimetric.Perimeter.PerimeterMeasure
import MyLeanRepo.Kakeya.CV.Isoperimetric.Perimeter.CutoffFunctions
import MyLeanRepo.Kakeya.CV.Isoperimetric.Perimeter.IntersectionBallHelpers
import MyLeanRepo.Kakeya.CV.Isoperimetric.Coarea.DistanceCoareaEq
import MyLeanRepo.Kakeya.CV.Isoperimetric.Coarea.CoareaIntegral
import MyLeanRepo.Kakeya.CV.Isoperimetric.Measure.LevelSetMeasurability
import MyLeanRepo.Kakeya.CV.Isoperimetric.InnerMinkowski.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Tactic


open MeasureTheory Metric Set ENNReal Filter
open scoped MeasureTheory ContDiff

namespace Geometry.Perimeter

variable {n : ℕ}

section NGeTwo

variable [Nonempty (Fin n)]

private lemma sphere_section_hausdorff_lt_top_ae
    (hn : 2 ≤ n) (S : Set (E n)) (hS : MeasurableSet S) (x₀ : E n) :
    ∀ᵐ r : ℝ, μHE[n - 1] (S ∩ sphere x₀ r) < ⊤ := by
  let H : ℝ → ENNReal := fun t => μHE[n - 1] (S ∩ sphere x₀ t)
  have hH_local := H_locally_integrable hn S hS x₀
  have h_nonpos : ∀ t ≤ 0, H t = 0 :=
    fun t ht => H_zero_of_nonpos hn S x₀ ht
  have h_pos :
      ∀ k : ℕ, ∀ᵐ t ∂volume.restrict (Set.Ioc (k : ℝ) (k + 1)),
        H t < ⊤ := by
    intro k
    have h_integral :
        ∫⁻ t in Set.Ioc (k : ℝ) (k + 1), H t ≠ ⊤ :=
      hH_local (k : ℝ) (k + 1) (by positivity) (by simp)
    let f : E n → ℝ := fun x => dist x x₀
    have hf : LipschitzWith 1 f := LipschitzWith.dist_left x₀
    let B := S ∩ closedBall x₀ (k + 1)
    have hB_meas : MeasurableSet B :=
      hS.inter isClosed_closedBall.measurableSet
    have hB_bdd : Bornology.IsBounded B :=
      (Metric.isBounded_iff_subset_closedBall x₀).mpr
        ⟨k + 1, fun _ hx => hx.2⟩
    let G : ℝ → ENNReal := fun t => μHE[n - 1] (B ∩ f ⁻¹' {t})
    have hG_aeMeas :
        AEMeasurable G (volume.restrict (Set.Ioc (k : ℝ) (k + 1))) :=
      levelSetMeasure_aemeasurable hn hf hB_meas hB_bdd (by simp)
    have h_eq : ∀ t ∈ Set.Ioc (k : ℝ) (k + 1), H t = G t := by
      intro t ht
      have h_t_le : t ≤ (k + 1 : ℝ) := ht.2
      have h_set_eq : S ∩ sphere x₀ t = B ∩ f ⁻¹' {t} := by
        ext x
        simp only [B, Set.mem_inter_iff, Set.mem_preimage,
          Set.mem_singleton_iff, Metric.mem_sphere]
        constructor
        · rintro ⟨hxS, hdist⟩
          exact ⟨⟨hxS, by
            simpa [Metric.mem_closedBall] using hdist ▸ h_t_le⟩, hdist⟩
        · rintro ⟨⟨hxS, _⟩, hdist⟩
          exact ⟨hxS, hdist⟩
      exact congrArg (μHE[n - 1]) h_set_eq
    have h_ae :
        ∀ᵐ t ∂volume.restrict (Set.Ioc (k : ℝ) (k + 1)),
          H t = G t := by
      filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with t ht
      exact h_eq t ht
    have hH_aeMeas :
        AEMeasurable H (volume.restrict (Set.Ioc (k : ℝ) (k + 1))) :=
      AEMeasurable.congr hG_aeMeas (EventuallyEq.symm h_ae)
    have h_null :
        volume.restrict (Set.Ioc (k : ℝ) (k + 1)) {t | H t = ⊤} = 0 :=
      measure_eq_top_of_lintegral_ne_top hH_aeMeas h_integral
    have h_ne_top :
        ∀ᵐ t ∂volume.restrict (Set.Ioc (k : ℝ) (k + 1)), H t ≠ ⊤ := by
      rw [ae_iff]
      have hset : {t : ℝ | ¬ H t ≠ ⊤} = {t : ℝ | H t = ⊤} := by
        ext t
        simp
      rwa [hset]
    filter_upwards [h_ne_top] with t ht
    exact lt_top_iff_ne_top.mpr ht
  let S_top := {t : ℝ | H t = ⊤}
  have h_null_Iic : volume (S_top ∩ Set.Iic 0) = 0 := by
    have h_empty : S_top ∩ Set.Iic 0 = ∅ := by
      ext t
      simp only [S_top, Set.mem_inter_iff, Set.mem_empty_iff_false,
        iff_false]
      intro ht
      have hzero : H t = 0 := h_nonpos t ht.2
      have htop : H t = ⊤ := ht.1
      rw [hzero] at htop
      simpa using htop
    simp [h_empty]
  have h_null_Ioc :
      ∀ k : ℕ, volume (S_top ∩ Set.Ioc (k : ℝ) (k + 1)) = 0 := by
    intro k
    have hfinite :
        ∀ᵐ t ∂volume.restrict (Set.Ioc (k : ℝ) (k + 1)), H t < ⊤ :=
      h_pos k
    have hnull :
        volume.restrict (Set.Ioc (k : ℝ) (k + 1)) {t | ¬ H t < ⊤} = 0 :=
      ae_iff.mp hfinite
    have hset : {t : ℝ | ¬ H t < ⊤} = S_top := by
      ext t
      simp [S_top, lt_top_iff_ne_top]
    rw [hset] at hnull
    simpa [Measure.restrict_apply'] using hnull
  have h_null_Icc :
      ∀ k : ℕ, volume (S_top ∩ Set.Icc (k : ℝ) (k + 1)) = 0 := by
    intro k
    let pt : Set ℝ := {(k : ℝ)}
    have h_decomp :
        Set.Icc (k : ℝ) (k + 1) = pt ∪ Set.Ioc (k : ℝ) (k + 1) := by
      ext t
      simp only [Set.mem_Icc, Set.mem_Ioc, Set.mem_union,
        Set.mem_singleton_iff]
      constructor
      · rintro ⟨h1, h2⟩
        by_cases h3 : (k : ℝ) < t
        · exact Or.inr ⟨h3, h2⟩
        · exact Or.inl (le_antisymm h1 (le_of_not_gt h3)).symm
      · rintro (h | h)
        · rw [h]
          constructor <;> norm_num
        · exact ⟨h.1.le, h.2⟩
    rw [h_decomp, Set.inter_union_distrib_left]
    have h_pt_null : volume pt = 0 := Real.volume_singleton
    have h_singleton : volume (S_top ∩ pt) = 0 :=
      measure_mono_null inter_subset_right h_pt_null
    have h_union :
        volume ((S_top ∩ pt) ∪
            (S_top ∩ Set.Ioc (k : ℝ) (k + 1))) ≤
          volume (S_top ∩ pt) +
            volume (S_top ∩ Set.Ioc (k : ℝ) (k + 1)) :=
      measure_union_le _ _
    rw [h_singleton, h_null_Ioc k] at h_union
    exact le_zero_iff.mp (by simpa using h_union)
  have h_cover :
      S_top ⊆ Set.Iic 0 ∪ ⋃ k : ℕ, Set.Icc (k : ℝ) (k + 1) := by
    intro t ht
    by_cases h : t ≤ 0
    · exact Or.inl h
    · let k : ℕ := Nat.floor t
      have h1 : (k : ℝ) ≤ t := Nat.floor_le (by linarith)
      have h2 : t ≤ (k : ℝ) + 1 := (Nat.lt_floor_add_one t).le
      exact Or.inr (Set.mem_iUnion.mpr ⟨k, h1, h2⟩)
  have h_null_union :
      volume (S_top ∩
        (Set.Iic 0 ∪ ⋃ k : ℕ, Set.Icc (k : ℝ) (k + 1))) = 0 := by
    rw [Set.inter_union_distrib_left, Set.inter_iUnion]
    rw [measure_union_null_iff]
    simp [h_null_Iic, h_null_Icc, measure_iUnion_null]
  have h_null_top : volume S_top = 0 := by
    rw [show S_top =
      S_top ∩ (Set.Iic 0 ∪ ⋃ k : ℕ, Set.Icc (k : ℝ) (k + 1)) by
        exact (inter_eq_left.mpr h_cover).symm]
    exact h_null_union
  have h_ae : ∀ᵐ t : ℝ, H t < ⊤ := by
    rw [ae_iff]
    have hset : {t : ℝ | ¬ H t < ⊤} = S_top := by
      ext t
      simp [S_top, lt_top_iff_ne_top]
    rwa [hset]
  exact h_ae

private lemma closedBall_volume_continuous (x₀ : E n) :
    Continuous (fun t : ℝ => volume (closedBall x₀ t)) := by
  let ballConstant : ENNReal :=
    ENNReal.ofReal (√Real.pi ^ n / Real.Gamma (n / 2 + 1))
  have hconstant : ballConstant ≠ ⊤ := ENNReal.ofReal_ne_top
  have hn_pos : 0 < n := by
    exact Fin.pos_iff_nonempty.mpr inferInstance
  have hpow : Continuous (fun t : ℝ => (ENNReal.ofReal t) ^ n) := by
    have heq :
        (fun t : ℝ => (ENNReal.ofReal t) ^ n) =
          fun t : ℝ => ENNReal.ofReal ((max t 0) ^ n) := by
      funext t
      by_cases ht : 0 ≤ t
      · rw [max_eq_left ht]
        exact (ENNReal.ofReal_pow ht n).symm
      · have ht' : t < 0 := lt_of_not_ge ht
        rw [max_eq_right ht'.le, ENNReal.ofReal_eq_zero.mpr ht'.le]
        simp [hn_pos.ne']
    rw [heq]
    exact ENNReal.continuous_ofReal.comp
      ((continuous_id.max continuous_const).pow n)
  have hformula :
      ∀ t : ℝ, volume (closedBall x₀ t) =
        (ENNReal.ofReal t) ^ n * ballConstant := by
    intro t
    by_cases ht : 0 ≤ t
    · rw [InnerProductSpace.volume_closedBall x₀ t]
      have hfinrank : Module.finrank ℝ (E n) = n :=
        finrank_euclideanSpace_fin
      rw [hfinrank]
    · have ht' : t < 0 := lt_of_not_ge ht
      have hempty : closedBall x₀ t = ∅ := by
        ext x
        simp only [Metric.mem_closedBall, Set.mem_empty_iff_false, iff_false]
        intro h
        linarith [dist_nonneg (x := x) (y := x₀)]
      rw [hempty, measure_empty, ENNReal.ofReal_eq_zero.mpr ht'.le]
      simp [hn_pos.ne']
  have hcontinuous :
      Continuous (fun t : ℝ =>
        (ENNReal.ofReal t) ^ n * ballConstant) := by
    have hmul : Continuous (fun z : ENNReal => z * ballConstant) := by
      simpa [mul_comm] using ENNReal.continuous_const_mul hconstant
    exact hmul.comp hpow
  convert hcontinuous using 1
  funext t
  exact hformula t

private lemma radial_annulus_volume_tendsto_zero
    (x₀ : E n) (r : ℝ) :
    Tendsto
      (fun L : ℝ =>
        volume {x : E n |
          r < dist x x₀ ∧ dist x x₀ ≤ r + L})
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have hclosedBall_eq_ball :
      volume (closedBall x₀ r) = volume (ball x₀ r) := by
    rw [InnerProductSpace.volume_closedBall,
      InnerProductSpace.volume_ball]
  have hannulus :
      ∀ L : ℝ, 0 < L →
        volume {x : E n |
          r < dist x x₀ ∧ dist x x₀ ≤ r + L} =
        volume (closedBall x₀ (r + L)) -
          volume (ball x₀ r) := by
    intro L hL
    have hset :
        {x : E n | r < dist x x₀ ∧ dist x x₀ ≤ r + L} =
          closedBall x₀ (r + L) \ closedBall x₀ r := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_diff, Metric.mem_closedBall]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h2, not_le.mpr h1⟩
      · rintro ⟨h2, h1⟩
        exact ⟨lt_of_not_ge h1, h2⟩
    rw [hset]
    have hsub :
        closedBall x₀ r ⊆ closedBall x₀ (r + L) := by
      intro x hx
      change dist x x₀ ≤ r + L
      exact hx.trans (by linarith)
    rw [measure_diff hsub isClosed_closedBall.nullMeasurableSet
      isBounded_closedBall.measure_lt_top.ne, hclosedBall_eq_ball]
  have hadd :
      Tendsto (fun L : ℝ => r + L)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds r) := by
    have hr : Tendsto (fun _ : ℝ => r)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds r) :=
      tendsto_const_nhds
    have hid : Tendsto (fun L : ℝ => L)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    simpa using hr.add hid
  have hclosed :
      Tendsto (fun L : ℝ => volume (closedBall x₀ (r + L)))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (volume (closedBall x₀ r))) :=
    ((closedBall_volume_continuous x₀).tendsto r).comp hadd
  rw [tendsto_congr' (by
    filter_upwards [self_mem_nhdsWithin] with L hL
    exact hannulus L hL)]
  have hsub :
      Tendsto
        (fun L : ℝ =>
          volume (closedBall x₀ (r + L)) -
            volume (ball x₀ r))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (volume (closedBall x₀ r) -
          volume (ball x₀ r))) :=
    ENNReal.Tendsto.sub hclosed tendsto_const_nhds
      (Or.inl isBounded_closedBall.measure_lt_top.ne)
  simpa [hclosedBall_eq_ball] using hsub

/-- The n ≥ 2 case of perimeter_inter_ball_le. -/
theorem perimeter_inter_ball_le_n_ge_two (hn : 2 ≤ n)
    (S : Set (E n)) (hS : MeasurableSet S) (x₀ : E n) :
    ∀ᵐ (r : ℝ) ∂volume.restrict (Set.Ioi 0),
      perimeter (S ∩ ball x₀ r) ≤
      perimeterIn S (ball x₀ r) + μHE[n - 1] (S ∩ sphere x₀ r) := by
  let d : E n → ℝ := fun x => dist x x₀
  let H : ℝ → ENNReal := fun t => μHE[n - 1] (S ∩ sphere x₀ t)
  let h_real : ℝ → ℝ := fun t => ENNReal.toReal (H t)
  let C_w : ℝ := smoothStepDerivBound
  let w : ℝ → ℝ := fun s => |deriv smoothStep s|
  have hw_nonneg : ∀ t, 0 ≤ w t := fun t => abs_nonneg _
  have hw_int : ∫ t in (0 : ℝ)..1, w t = 1 := smoothStep_deriv_abs_integral
  have hC_w : ∀ t, w t ≤ C_w := fun t => smoothStep_deriv_bound
  have hw_cont : Continuous w := by
    have h1 : Continuous (deriv smoothStep) :=
      ContDiff.continuous_deriv smoothStep_contDiff (by norm_num)
    exact continuous_abs.comp h1
  have hH_local := H_locally_integrable hn S hS x₀
  have h_real_local := h_real_locally_integrable hn S hS x₀
  have h_right_good : ∀ᵐ (r : ℝ), Tendsto (fun ε : ℝ => perimeterIn S (ball x₀ (r + ε)))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (perimeterIn S (ball x₀ r))) :=
    perimeterIn_ball_rightContinuous_ae S x₀
  have h_leb_good : ∀ᵐ (r : ℝ), Tendsto (fun L : ℝ => (1 / L) * ∫ t in r..(r + L), |h_real t - h_real r|)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := oneSided_lebesgueDifferentiation h_real_local
  have hH_finite : ∀ᵐ r : ℝ, H r < ⊤ := by
    simpa [H] using sphere_section_hausdorff_lt_top_ae hn S hS x₀
  have hH_finite_r : ∀ᵐ (r : ℝ) ∂volume.restrict (Set.Ioi 0), H r < ⊤ :=
    hH_finite.filter_mono (ae_mono Measure.restrict_le_self)
  have h_right_good_r : ∀ᵐ (r : ℝ) ∂volume.restrict (Set.Ioi 0), _ :=
    h_right_good.filter_mono (ae_mono Measure.restrict_le_self)
  have h_leb_good_r : ∀ᵐ (r : ℝ) ∂volume.restrict (Set.Ioi 0), _ :=
    h_leb_good.filter_mono (ae_mono Measure.restrict_le_self)
  filter_upwards [h_right_good_r, h_leb_good_r, hH_finite_r, self_mem_ae_restrict measurableSet_Ioi]
    with r hr_right hr_leb hr_finite hr_pos
  have hH_r : H r = ENNReal.ofReal (h_real r) := by
    rw [ENNReal.ofReal_toReal hr_finite.ne]
  have h_main : ∀ (Φ : TestVectorField),
      ENNReal.ofReal |∫ x in (S ∩ ball x₀ r), divergence Φ.toFun x| ≤
      perimeterIn S (ball x₀ r) + H r := by
    intro Φ
    by_cases hP_top : perimeterIn S (ball x₀ r) = ⊤
    · rw [hP_top] <;> simp
    have hP_finite : perimeterIn S (ball x₀ r) < ⊤ := lt_top_iff_ne_top.mpr hP_top
    -- Bound on |div Φ|
    have hdiv_cont : Continuous (divergence Φ.toFun) :=
      (divergence_smooth Φ).continuous
    have hdiv_compact : HasCompactSupport (divergence Φ.toFun) :=
      divergence_hasCompactSupport Φ
    have hdiv_bdd : ∃ (M : ℝ), ∀ x, |divergence Φ.toFun x| ≤ M := by
      let K := tsupport (divergence Φ.toFun)
      have hK : IsCompact K := hdiv_compact
      have h_cont : Continuous (fun x => |divergence Φ.toFun x|) := continuous_abs.comp hdiv_cont
      have h_bdd : BddAbove (Set.image (fun x => |divergence Φ.toFun x|) K) :=
        hK.bddAbove_image h_cont.continuousOn
      rcases h_bdd with ⟨M, hM⟩
      refine ⟨max M 0, fun x => ?_⟩
      by_cases hx : x ∈ K
      · exact le_trans (hM ⟨x, hx, rfl⟩) (le_max_left _ _)
      · have h5 : divergence Φ.toFun x = 0 := by
          by_contra h6
          have h7 : x ∈ Function.support (divergence Φ.toFun) := by
            simpa [Function.mem_support] using h6
          have h8 : x ∈ K := by exact subset_tsupport (f := divergence Φ.toFun) h7
          exact hx h8
        rw [h5] <;> simp [le_max_right]
    rcases hdiv_bdd with ⟨M_div, hM_div⟩
    have hM_nonneg : 0 ≤ M_div := by
      haveI : Nonempty (E n) := inferInstance
      let x0 : E n := Classical.arbitrary (E n)
      have h : 0 ≤ |divergence Φ.toFun x0| := abs_nonneg _
      have h2 : |divergence Φ.toFun x0| ≤ M_div := hM_div x0
      linarith
    have h_eventually : ∀ᶠ (L : ℝ) in nhdsWithin 0 (Set.Ioi 0),
        perimeterIn S (ball x₀ (r + L)) < ⊤ := by
      have h_nhds : Set.Iio ⊤ ∈ nhds (perimeterIn S (ball x₀ r)) := Iio_mem_nhds hP_finite
      exact hr_right h_nhds
    have h_goal : ∀ (L : ℝ), 0 < L → perimeterIn S (ball x₀ (r + L)) < ⊤ →
        ENNReal.ofReal |∫ x in (S ∩ ball x₀ r), divergence Φ.toFun x| ≤
        perimeterIn S (ball x₀ (r + L)) +
        (ENNReal.ofReal M_div) * volume {x : E n | r < d x ∧ d x ≤ r + L} +
        ENNReal.ofReal (∫ t in r..(r + L), (w ((t - r) / L) / L) * h_real t) := by
      intro L hL hPL_finite
      let annulus := {x : E n | r < d x ∧ d x ≤ r + L}
      let η : E n → ℝ := radialCutoff x₀ r L
      let ΨtoFun : E n → E n := fun x => η x • Φ.toFun x
      have hη_smooth : ContDiff ℝ ∞ η := radialCutoff_contDiff hr_pos hL
      have hΨ_smooth : ContDiff ℝ ∞ ΨtoFun := hη_smooth.smul Φ.smooth
      have hΨ_bound : ∀ x, ‖ΨtoFun x‖ ≤ 1 := by
        intro x
        have h1 : ‖ΨtoFun x‖ = |η x| * ‖Φ.toFun x‖ := by
          rw [norm_smul, Real.norm_eq_abs]
        rw [h1]
        have h2 : 0 ≤ η x := smoothStep_range.1
        have h3 : |η x| ≤ 1 := by
          rw [abs_of_nonneg h2]
          exact smoothStep_range.2
        have h4 : 0 ≤ |η x| := abs_nonneg _
        nlinarith [h3, Φ.bound x]
      have hη_one : ∀ x ∈ ball x₀ r, η x = 1 := by
        intro x hx
        exact radialCutoff_one_of_mem_closedBall hr_pos hL (ball_subset_closedBall hx)
      have hη_zero : ∀ x ∉ ball x₀ (r + L), η x = 0 := by
        intro x hx
        exact radialCutoff_zero_of_not_mem_ball hr_pos hL hx
      have hΨ_support : Function.support ΨtoFun ⊆ ball x₀ (r + L) := by
        intro x hx
        by_contra h2
        have h3 : η x = 0 := hη_zero x h2
        have h4 : ΨtoFun x = 0 := by simp [ΨtoFun, h3]
        simpa [Function.mem_support] using hx h4
      have hΨ_compact : HasCompactSupport ΨtoFun := by
        have h1 : Function.support ΨtoFun ⊆ closedBall x₀ (r + L) := hΨ_support.trans ball_subset_closedBall
        have h2 : tsupport ΨtoFun ⊆ closedBall x₀ (r + L) := closure_minimal h1 isClosed_closedBall
        exact IsCompact.of_isClosed_subset (isCompact_closedBall x₀ (r + L)) (isClosed_tsupport _) h2
      let Ψ : TestVectorField :=
        { toFun := ΨtoFun, smooth := hΨ_smooth, compact := hΨ_compact, bound := hΨ_bound }
      let Ψ' : {Ψ' : TestVectorField // Function.support Ψ'.toFun ⊆ ball x₀ (r + L)} :=
        ⟨Ψ, hΨ_support⟩
      have h_perim_bound : ENNReal.ofReal |∫ x in S, divergence ΨtoFun x| ≤ perimeterIn S (ball x₀ (r + L)) :=
        le_iSup (fun (θ : {Ψ' : TestVectorField // Function.support Ψ'.toFun ⊆ ball x₀ (r + L)}) =>
          ENNReal.ofReal |∫ x in S, divergence θ.val.toFun x|) Ψ'
      have h_product : ∀ x, divergence ΨtoFun x =
          η x * divergence Φ.toFun x + (fderiv ℝ η x) (Φ.toFun x) := by
        intro x
        have h := divergence_product_rule (hη_smooth.of_le (by norm_num)) (Φ.smooth.of_le (by norm_num)) x
        rw [h]
        <;> ring
      -- Integrability
      have h_f1_cont : Continuous (fun x => η x * divergence Φ.toFun x) :=
        hη_smooth.continuous.mul hdiv_cont
      have h_f1_support : HasCompactSupport (fun x => η x * divergence Φ.toFun x) := by
        have h1 : Function.support (fun x => η x * divergence Φ.toFun x) ⊆ Function.support (divergence Φ.toFun) := by
          intro x hx
          by_contra h
          have h2 : divergence Φ.toFun x = 0 := by simpa [Function.mem_support] using h
          have h3 : η x * divergence Φ.toFun x = 0 := by rw [h2] <;> ring
          exact hx h3
        exact hdiv_compact.mono h1
      have h_f1_int : Integrable (fun x => η x * divergence Φ.toFun x) volume :=
        h_f1_cont.integrable_of_hasCompactSupport h_f1_support
      have h_f2_cont : Continuous (fun x => (fderiv ℝ η x) (Φ.toFun x)) := by
        have h1 : Continuous (fderiv ℝ η) := hη_smooth.continuous_fderiv (by norm_num)
        have h2 : Continuous Φ.toFun := Φ.smooth.continuous
        fun_prop
      have h_f2_support : HasCompactSupport (fun x => (fderiv ℝ η x) (Φ.toFun x)) :=
        Φ.compact.mono (by
          intro x hx
          by_contra h
          have h5 : Φ.toFun x = 0 := by simpa [Function.mem_support] using h
          have h6 : (fderiv ℝ η x) (Φ.toFun x) = 0 := by rw [h5] <;> simp
          simpa [Function.mem_support] using hx h6)
      have h_f2_int : Integrable (fun x => (fderiv ℝ η x) (Φ.toFun x)) volume :=
        h_f2_cont.integrable_of_hasCompactSupport h_f2_support
      -- Split integral over S
      have h_annulus_meas : MeasurableSet annulus := by
        have hd_meas : Measurable d := by fun_prop
        have h1 : MeasurableSet {x : E n | r < d x} := measurableSet_lt measurable_const hd_meas
        have h2 : MeasurableSet {x : E n | d x ≤ r + L} := measurableSet_le hd_meas measurable_const
        exact h1.inter h2
      have h_sphere_null : volume (sphere x₀ r) = 0 :=
        MeasureTheory.Measure.addHaar_sphere volume x₀ r
      have h_split1 : ∫ x in S, η x * divergence Φ.toFun x =
          (∫ x in (S ∩ ball x₀ r), divergence Φ.toFun x) +
          (∫ x in (S ∩ annulus), η x * divergence Φ.toFun x) := by
        let f := fun x : E n => η x * divergence Φ.toFun x
        have hf_int : Integrable f volume := h_f1_int
        have hB1_meas : MeasurableSet (S ∩ closedBall x₀ r) := hS.inter isClosed_closedBall.measurableSet
        have hB2_meas : MeasurableSet (S ∩ annulus) := hS.inter h_annulus_meas
        have hB3_meas : MeasurableSet (S \ closedBall x₀ (r + L)) := hS.diff isClosed_closedBall.measurableSet
        have h_disj12 : Disjoint (S ∩ closedBall x₀ r) (S ∩ annulus) := by
          rw [Set.disjoint_left]; intro x hx1 hx2
          have h1 : d x ≤ r := hx1.2; have h2 : r < d x := hx2.2.1; linarith
        have h_disj3 : Disjoint ((S ∩ closedBall x₀ r) ∪ (S ∩ annulus)) (S \ closedBall x₀ (r + L)) := by
          rw [Set.disjoint_left]; intro x hx1 hx2
          have h3 : d x ≤ r + L := by
            rcases hx1 with (h | h)
            · have h5 : d x ≤ r := h.2
              linarith
            · exact h.2.2
          have h4 : x ∉ closedBall x₀ (r + L) := hx2.2
          exact h4 h3
        have hη_one_B1 : ∀ x ∈ (S ∩ closedBall x₀ r), η x = 1 := by
          intro x hx; exact radialCutoff_one_of_mem_closedBall hr_pos hL hx.2
        have hη_zero_B3 : ∀ x ∈ (S \ closedBall x₀ (r + L)), η x = 0 := by
          intro x hx
          have h2 : x ∉ ball x₀ (r + L) := by
            intro h3; exact hx.2 (ball_subset_closedBall h3)
          exact hη_zero x h2
        have h_int_B3 : ∫ x in (S \ closedBall x₀ (r + L)), f x = 0 := by
          have h1 : ∀ᵐ x ∂volume, x ∈ (S \ closedBall x₀ (r + L)) → f x = 0 := by
            filter_upwards with x; intro hx; have h2 : η x = 0 := hη_zero_B3 x hx; simp [f, h2]
          rw [setIntegral_congr_ae hB3_meas h1] <;> simp
        have hS_eq : S = (S ∩ closedBall x₀ r) ∪ (S ∩ annulus) ∪ (S \ closedBall x₀ (r + L)) := by
          apply Set.ext
          intro x
          constructor
          · intro hxS
            by_cases h1 : d x ≤ r
            · have h : x ∈ S ∩ closedBall x₀ r := ⟨hxS, h1⟩
              exact Or.inl (Or.inl h)
            · by_cases h2 : d x ≤ r + L
              · have h3 : r < d x := by linarith
                have h : x ∈ S ∩ annulus := ⟨hxS, h3, h2⟩
                exact Or.inl (Or.inr h)
              · have h3 : x ∉ closedBall x₀ (r + L) := by simpa [Metric.mem_closedBall] using h2
                have h : x ∈ S \ closedBall x₀ (r + L) := ⟨hxS, h3⟩
                exact Or.inr h
          · intro h
            rcases h with (h | h)
            · rcases h with (h | h)
              · exact h.1
              · exact h.1
            · exact h.1
        have hUnion_meas : MeasurableSet ((S ∩ closedBall x₀ r) ∪ (S ∩ annulus)) := hB1_meas.union hB2_meas
        have h12 : ∫ x in S, f x = ∫ x in ((S ∩ closedBall x₀ r) ∪ (S ∩ annulus)), f x := by
          let B12 := (S ∩ closedBall x₀ r) ∪ (S ∩ annulus)
          let B3 := S \ closedBall x₀ (r + L)
          have h_disj : Disjoint B12 B3 := h_disj3
          have hB3m : MeasurableSet B3 := hB3_meas
          have h1 : IntegrableOn f B12 := hf_int.integrableOn
          have h2 : IntegrableOn f B3 := hf_int.integrableOn
          have h_eq : S = B12 ∪ B3 := hS_eq
          have h3 : ∫ x in S, f x = ∫ x in (B12 ∪ B3), f x := by rw [h_eq]
          rw [h3]
          have h4 := setIntegral_union h_disj hB3m h1 h2
          rw [h4, h_int_B3] <;> ring
        have h_i1 : IntegrableOn f (S ∩ closedBall x₀ r) := hf_int.integrableOn
        have h_i2 : IntegrableOn f (S ∩ annulus) := hf_int.integrableOn
        have h13 : ∫ x in ((S ∩ closedBall x₀ r) ∪ (S ∩ annulus)), f x ∂volume =
            ∫ x in (S ∩ closedBall x₀ r), f x ∂volume + ∫ x in (S ∩ annulus), f x ∂volume := by
          have h_set : ((S ∩ closedBall x₀ r) ∪ (S ∩ annulus)) = (S ∩ closedBall x₀ r ∪ S ∩ annulus) := by ext y; simp
          rw [h_set]
          exact setIntegral_union h_disj12 hB2_meas h_i1 h_i2
        have h14 : ∫ x in (S ∩ closedBall x₀ r), f x = ∫ x in (S ∩ closedBall x₀ r), divergence Φ.toFun x := by
          have h1 : ∀ᵐ x ∂volume, x ∈ (S ∩ closedBall x₀ r) → f x = divergence Φ.toFun x := by
            filter_upwards with x; intro hx; have h2 : η x = 1 := hη_one_B1 x hx; simp [f, h2] <;> ring
          exact setIntegral_congr_ae hB1_meas h1
        have hB1_eq : (S ∩ closedBall x₀ r) = (S ∩ ball x₀ r) ∪ (S ∩ sphere x₀ r) := by
          ext x
          simp only [Set.mem_inter_iff, Set.mem_union, Metric.mem_closedBall, Metric.mem_ball, Metric.mem_sphere]
          constructor
          · rintro ⟨hS, hle⟩
            by_cases h : d x < r
            · exact Or.inl ⟨hS, h⟩
            · have h' : d x = r := by linarith
              exact Or.inr ⟨hS, h'⟩
          · rintro (h | h)
            · exact ⟨h.1, h.2.le⟩
            · exact ⟨h.1, le_of_eq h.2⟩
        have h_disj_sphere : Disjoint (S ∩ ball x₀ r) (S ∩ sphere x₀ r) := by
          rw [Set.disjoint_left]; intro x hx1 hx2
          have h1 : d x < r := hx1.2; have h2 : d x = r := hx2.2; linarith
        have h_sphere_meas : MeasurableSet (S ∩ sphere x₀ r) := hS.inter isClosed_sphere.measurableSet
        have h_int_sphere : ∫ x in (S ∩ sphere x₀ r), divergence Φ.toFun x = 0 := by
          have h_null : volume (S ∩ sphere x₀ r) = 0 := measure_mono_null (show S ∩ sphere x₀ r ⊆ sphere x₀ r from Set.inter_subset_right) h_sphere_null
          have h_restrict : volume.restrict (S ∩ sphere x₀ r) = 0 := Measure.restrict_eq_zero.mpr h_null
          rw [h_restrict]
          <;> simp
        have hdiv_int : Integrable (divergence Φ.toFun) volume := by
          exact hdiv_cont.integrable_of_hasCompactSupport hdiv_compact
        have h15 : ∫ x in (S ∩ closedBall x₀ r), divergence Φ.toFun x = ∫ x in (S ∩ ball x₀ r), divergence Φ.toFun x := by
          rw [hB1_eq, setIntegral_union h_disj_sphere h_sphere_meas (hdiv_int.integrableOn) (hdiv_int.integrableOn), h_int_sphere, add_zero]
        have h_goal : ∫ x in S, f x =
            (∫ x in (S ∩ ball x₀ r), divergence Φ.toFun x) + (∫ x in (S ∩ annulus), f x) := by
          have h_step1 : ∫ x in ((S ∩ closedBall x₀ r) ∪ (S ∩ annulus)), f x =
              (∫ x in (S ∩ closedBall x₀ r), f x) + (∫ x in (S ∩ annulus), f x) := h13
          have h_step2 : (∫ x in (S ∩ closedBall x₀ r), f x) + (∫ x in (S ∩ annulus), f x) =
              (∫ x in (S ∩ closedBall x₀ r), divergence Φ.toFun x) + (∫ x in (S ∩ annulus), f x) := by
            exact congr_arg (fun y => y + (∫ x in (S ∩ annulus), f x)) h14
          have h_step3 : (∫ x in (S ∩ closedBall x₀ r), divergence Φ.toFun x) + (∫ x in (S ∩ annulus), f x) =
              (∫ x in (S ∩ ball x₀ r), divergence Φ.toFun x) + (∫ x in (S ∩ annulus), f x) := by
            exact congr_arg (fun y => y + (∫ x in (S ∩ annulus), f x)) h15
          exact h12.trans (h_step1.trans (h_step2.trans h_step3))
        simpa [f] using h_goal
      -- Gradient bound via coarea
      let A := S ∩ annulus
      have hA_meas : MeasurableSet A := hS.inter h_annulus_meas
      have hA_bdd : Bornology.IsBounded A := by
        have h1 : A ⊆ closedBall x₀ (r + L) := by
          intro x hx; have h2 : d x ≤ r + L := hx.2.2; simpa [closedBall] using h2
        have h_bdd : Bornology.IsBounded (closedBall x₀ (r + L)) := isBounded_closedBall
        exact h_bdd.subset h1
      have hA_sub : A ⊆ {x | 0 < infDist x ({x₀} : Set (E n))} := by
        intro x hx
        have h1 : r < d x := hx.2.1
        have h2 : 0 < r := hr_pos
        have h3 : 0 < d x := lt_trans h2 h1
        have h4 : infDist x ({x₀} : Set (E n)) = d x := by
          simp [infDist_singleton] <;> rfl
        have h5 : 0 < infDist x ({x₀} : Set (E n)) := by rw [h4] <;> exact h3
        exact h5
      let g : ℝ → ℝ := fun t => w ((t - r) / L) / L
      let g' : ℝ → ENNReal := fun t => ENNReal.ofReal (g t)
      have hg_nonneg : ∀ t, 0 ≤ g t := by intro t; positivity
      have hg_bdd : ∀ t, g t ≤ C_w / L := by
        intro t
        have h1 : w ((t - r) / L) ≤ C_w := hC_w ((t - r) / L)
        have hL_pos : 0 < L := hL
        exact div_le_div_of_nonneg_right h1 (by linarith)
      have h1_coarea : ∫⁻ x in A, g' (infDist x ({x₀} : Set (E n))) =
          ∫⁻ t, g' t * μHE[n - 1] {x ∈ A | infDist x ({x₀} : Set (E n)) = t} :=
        coarea_integral hn (isClosed_singleton) (singleton_nonempty x₀) hA_meas hA_bdd hA_sub (by fun_prop)
      have h_infDist_eq : ∀ x, infDist x ({x₀} : Set (E n)) = d x := by
        intro x; simp [infDist_singleton] <;> rfl
      have h_H_A : ∀ t ∈ Set.Ioc r (r + L), μHE[n - 1] {x ∈ A | infDist x ({x₀} : Set (E n)) = t} = H t := by
        intro t ht
        have h_set : {x ∈ A | infDist x ({x₀} : Set (E n)) = t} = S ∩ sphere x₀ t := by
          ext x
          simp only [A, Set.mem_inter_iff, Set.mem_sep_iff, Set.mem_setOf_eq, Metric.mem_sphere]
          have h_inf : infDist x ({x₀} : Set (E n)) = d x := by
            simp [infDist_singleton] <;> rfl
          constructor
          · rintro ⟨⟨hS, h1, h2⟩, h3⟩
            have h4 : d x = t := by rw [←h_inf]; exact h3
            exact ⟨hS, h4⟩
          · rintro ⟨hS, h4⟩
            have h5 : d x = t := h4
            have h6 : r < d x := by rw [h5]; exact ht.1
            have h7 : d x ≤ r + L := by rw [h5]; exact ht.2
            have h8 : infDist x ({x₀} : Set (E n)) = t := by rw [h_inf, h5]
            exact ⟨⟨hS, h6, h7⟩, h8⟩
        rw [h_set]
      have h_support : ∀ t ∉ Set.Icc r (r + L), g' t = 0 := by
        intro t ht
        have h7 : (t - r) / L ∉ Set.Icc (0 : ℝ) 1 := by
          simp only [Set.mem_Icc, not_and_or] at ht ⊢
          rcases ht with (h | h)
          · have h9 : (t - r) / L < 0 := by
              have h10 : t - r < 0 := by linarith
              exact div_neg_of_neg_of_pos h10 hL
            exact Or.inl (by linarith)
          · have h9 : 1 < (t - r) / L := by
              have h10 : t - r > L := by linarith
              have h11 : 0 < L := hL
              calc
                1 = L / L := by field_simp [h11.ne'] <;> ring
                _ < (t - r) / L := by gcongr
            exact Or.inr (by linarith)
        have h6 : w ((t - r) / L) = 0 := by
          have h8 : deriv smoothStep ((t - r) / L) = 0 := smoothStep_deriv_zero_outside h7
          simp [w, h8]
        simp [g', g, h6]
      have h2_coarea : ∫⁻ t, g' t * μHE[n - 1] {x ∈ A | infDist x ({x₀} : Set (E n)) = t} =
          ∫⁻ t in Set.Ioc r (r + L), g' t * H t := by
        have h3 : ∀ᵐ t, g' t * μHE[n - 1] {x ∈ A | infDist x ({x₀} : Set (E n)) = t} =
            g' t * H t := by
          have h_single_null : volume ({r} : Set ℝ) = 0 := by exact Real.volume_singleton
          have h_ae_ne : ∀ᵐ (t : ℝ), t ≠ r := by
            simpa [ae_iff] using h_single_null
          filter_upwards [h_ae_ne] with t ht
          by_cases h4 : t ∈ Set.Ioc r (r + L)
          · rw [h_H_A t h4]
          · have h5 : t ∉ Set.Icc r (r + L) := by
              intro h6
              have h7 : r ≤ t ∧ t ≤ r + L := h6
              by_cases h8 : r < t
              · exact h4 ⟨h8, h7.2⟩
              · have h9 : t = r := by linarith
                exact ht h9
            have h6 : g' t = 0 := h_support t h5
            rw [h6] <;> simp
        have h4 : ∀ᵐ t, t ∉ Set.Ioc r (r + L) → g' t * H t = 0 := by
          have h_single_null : volume ({r} : Set ℝ) = 0 := by exact Real.volume_singleton
          have h_ae_ne : ∀ᵐ (t : ℝ), t ≠ r := by simpa [ae_iff] using h_single_null
          filter_upwards [h_ae_ne] with t ht hnot
          have h5 : t ∉ Set.Icc r (r + L) := by
            intro h6
            have h7 : r ≤ t ∧ t ≤ r + L := h6
            by_cases h8 : r < t
            · exact hnot ⟨h8, h7.2⟩
            · have h9 : t = r := by linarith
              exact ht h9
          have h6 : g' t = 0 := h_support t h5
          rw [h6] <;> simp
        have h5 : ∫⁻ t, g' t * H t = ∫⁻ t in Set.Ioc r (r + L), g' t * H t := by
          let f : ℝ → ENNReal := fun t => g' t * H t
          have h6 : ∀ᵐ t, f t = Set.indicator (Set.Ioc r (r + L)) f t := by
            filter_upwards [h4] with t ht
            by_cases h7 : t ∈ Set.Ioc r (r + L)
            · have h10 : Set.indicator (Set.Ioc r (r + L)) f t = f t := by
                rw [Set.indicator_apply, if_pos h7]
              exact h10.symm
            · have h8 : f t = 0 := ht h7
              have h10 : Set.indicator (Set.Ioc r (r + L)) f t = 0 := by
                rw [Set.indicator_apply, if_neg h7]
              rw [h8, h10]
          have h9 : ∫⁻ t, f t = ∫⁻ t, Set.indicator (Set.Ioc r (r + L)) f t :=
            lintegral_congr_ae h6
          simpa [f] using h9
        rw [lintegral_congr_ae h3, h5]
      have h_eq_fun : (fun x => g' (infDist x ({x₀} : Set (E n)))) = (fun x => g' (d x)) := by
        funext x; rw [h_infDist_eq x]
      have h1_coarea' : ∫⁻ x in A, g' (d x) = ∫⁻ t, g' t * μHE[n - 1] {x ∈ A | infDist x ({x₀} : Set (E n)) = t} := by
        rw [← h_eq_fun]; exact h1_coarea
      have h_bdd : ∫⁻ x in A, g' (d x) ≤ ENNReal.ofReal (C_w / L) * volume A := by
          have h5 : ∀ x ∈ A, g' (d x) ≤ ENNReal.ofReal (C_w / L) := fun x _ =>
            ENNReal.ofReal_le_ofReal (hg_bdd (d x))
          calc ∫⁻ x in A, g' (d x)
            ≤ ∫⁻ x in A, ENNReal.ofReal (C_w / L) := MeasureTheory.setLIntegral_mono' hA_meas h5
          _ = ENNReal.ofReal (C_w / L) * volume A := by
            simp [MeasureTheory.setLIntegral_one, mul_comm]
      have h_finite1 : ∫⁻ x in A, g' (d x) ≠ ⊤ :=
        (h_bdd.trans_lt (mul_lt_top ofReal_lt_top hA_bdd.measure_lt_top)).ne
      have h_finite2 : ∫⁻ t in Set.Ioc r (r + L), g' t * H t ≠ ⊤ := by
        rw [← h2_coarea, ← h1_coarea'] <;> exact h_finite1
      have h5_coarea : ∀ᵐ t ∂volume.restrict (Set.Ioc r (r + L)), g' t * H t = ENNReal.ofReal (g t * h_real t) := by
        have hH_finite_Ioc : ∀ᵐ t ∂volume.restrict (Set.Ioc r (r + L)), H t < ⊤ := by
          have h : ∀ᵐ (t : ℝ), H t < ⊤ := hH_finite
          exact h.filter_mono (ae_mono Measure.restrict_le_self)
        filter_upwards [hH_finite_Ioc] with t ht
        have h6 : g' t * H t = ENNReal.ofReal (g t) * H t := rfl
        have hHt : H t = ENNReal.ofReal (h_real t) := by
          rw [ENNReal.ofReal_toReal (lt_top_iff_ne_top.mp ht)]
        have h_nonneg_hreal : 0 ≤ h_real t := by positivity
        rw [h6, hHt]
        exact (ENNReal.ofReal_mul (hg_nonneg t)).symm
      have h_real_integrable : IntegrableOn (fun t => g t * h_real t) (Set.Ioc r (r + L)) volume := by
        have h7 : ∫⁻ t in Set.Ioc r (r + L), ENNReal.ofReal (g t * h_real t) ≠ ⊤ := by
          rw [← lintegral_congr_ae h5_coarea] <;> exact h_finite2
        have h8 : AEStronglyMeasurable (fun t => g t * h_real t) (volume.restrict (Set.Ioc r (r + L))) := by
          have h81 : AEStronglyMeasurable h_real volume := h_real_local.aestronglyMeasurable
          have h82 : AEStronglyMeasurable h_real (volume.restrict (Set.Ioc r (r + L))) :=
            h81.mono_measure Measure.restrict_le_self
          have h83 : AEStronglyMeasurable g (volume.restrict (Set.Ioc r (r + L))) := by fun_prop
          exact h83.mul h82
        have h9 : 0 ≤ᵐ[volume.restrict (Set.Ioc r (r + L))] (fun t => g t * h_real t) :=
          ae_of_all _ (fun t => mul_nonneg (hg_nonneg t) (by positivity))
        exact (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable h8 h9).mp h7
      have h_real_eq : ∫⁻ t in Set.Ioc r (r + L), ENNReal.ofReal (g t * h_real t) =
          ENNReal.ofReal (∫ t in Set.Ioc r (r + L), g t * h_real t) := by
        have h_nn : ∀ᵐ t ∂volume.restrict (Set.Ioc r (r + L)), 0 ≤ g t * h_real t :=
          ae_of_all _ (fun t => mul_nonneg (hg_nonneg t) (by positivity))
        exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal h_real_integrable h_nn).symm
      have h2_coarea' : ∫⁻ t in Set.Ioc r (r + L), g' t * H t =
          ∫⁻ t in Set.Ioc r (r + L), ENNReal.ofReal (g t * h_real t) :=
        lintegral_congr_ae h5_coarea
      have h_left_eq : ∫⁻ x in A, g' (d x) = ENNReal.ofReal (∫ x in A, g (d x)) := by
        have h_integrable : IntegrableOn (fun x => g (d x)) A volume := by
          have h9 : ∫⁻ x in A, ENNReal.ofReal (g (d x)) ≠ ⊤ := by simpa [g'] using h_finite1
          have h10 : AEStronglyMeasurable (fun x => g (d x)) (volume.restrict A) := by fun_prop
          have h11 : 0 ≤ᵐ[volume.restrict A] (fun x => g (d x)) :=
            ae_of_all _ (fun x => hg_nonneg (d x))
          exact (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable h10 h11).mp h9
        have h_nn : ∀ᵐ x ∂volume.restrict A, 0 ≤ g (d x) :=
          ae_of_all _ (fun x => hg_nonneg (d x))
        exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal h_integrable h_nn).symm
      have h_final_eq : ∫ x in A, g (d x) = ∫ t in Set.Ioc r (r + L), g t * h_real t := by
        have h9 : ENNReal.ofReal (∫ x in A, g (d x)) = ENNReal.ofReal (∫ t in Set.Ioc r (r + L), g t * h_real t) := by
          calc
            ENNReal.ofReal (∫ x in A, g (d x))
              = ∫⁻ x in A, g' (d x) := h_left_eq.symm
            _ = ∫⁻ t, g' t * μHE[n - 1] {x ∈ A | infDist x ({x₀} : Set (E n)) = t} := h1_coarea'
            _ = ∫⁻ t in Set.Ioc r (r + L), g' t * H t := h2_coarea
            _ = ∫⁻ t in Set.Ioc r (r + L), ENNReal.ofReal (g t * h_real t) := h2_coarea'
            _ = ENNReal.ofReal (∫ t in Set.Ioc r (r + L), g t * h_real t) := h_real_eq
        have h10 : 0 ≤ ∫ x in A, g (d x) := by positivity
        have h11 : 0 ≤ ∫ t in Set.Ioc r (r + L), g t * h_real t := by positivity
        have h12 : ENNReal.toReal (ENNReal.ofReal (∫ x in A, g (d x))) =
            ENNReal.toReal (ENNReal.ofReal (∫ t in Set.Ioc r (r + L), g t * h_real t)) := by
          rw [h9]
        simpa [h10, h11] using h12
      have h10 : ∫ x in A, g (d x) = ∫ t in r..(r + L), g t * h_real t := by
        rw [h_final_eq]
        rw [intervalIntegral.integral_of_le (by linarith)] <;> rfl
      have h12 : ∀ x, ‖(fderiv ℝ η x) (Φ.toFun x)‖ ≤ g (d x) := by
        intro x
        by_cases hx : x = x₀
        · rw [hx, radialCutoff_fderiv_at_center hr_pos hL] <;> simp [g] <;> positivity
        · have h13 : ‖fderiv ℝ η x‖ ≤ g (d x) := by
            have h14 : ‖fderiv ℝ η x‖ ≤ |deriv smoothStep ((d x - r) / L)| / L :=
              radialCutoff_fderiv_tight_bound hr_pos hL hx
            simpa [g, w] using h14
          have h14 : ‖(fderiv ℝ η x) (Φ.toFun x)‖ ≤ ‖fderiv ℝ η x‖ * ‖Φ.toFun x‖ :=
            (fderiv ℝ η x).le_opNorm _
          calc
            ‖(fderiv ℝ η x) (Φ.toFun x)‖ ≤ ‖fderiv ℝ η x‖ * ‖Φ.toFun x‖ := h14
            _ ≤ ‖fderiv ℝ η x‖ * 1 := by gcongr <;> exact Φ.bound x
            _ = ‖fderiv ℝ η x‖ := by ring
            _ ≤ g (d x) := h13
      have h_fderiv_zero_ball : ∀ x ∈ ball x₀ r, fderiv ℝ η x = 0 := by
        intro x hx
        have h1 : ∀ᶠ y in nhds x, η y = 1 := by
          have h2 : ball x₀ r ∈ nhds x := IsOpen.mem_nhds isOpen_ball hx
          filter_upwards [h2] with y hy
          exact radialCutoff_one_of_mem_closedBall hr_pos hL (ball_subset_closedBall hy)
        have h1' : η =ᶠ[nhds x] (fun _ => (1 : ℝ)) := h1
        have h_const : HasFDerivAt (fun (_ : E n) => (1 : ℝ)) (0 : E n →L[ℝ] ℝ) x :=
          hasFDerivAt_const (1 : ℝ) x
        have h3 : HasFDerivAt η (0 : E n →L[ℝ] ℝ) x :=
          h_const.congr_of_eventuallyEq h1'
        exact h3.fderiv
      have h_fderiv_zero_outside : ∀ x ∈ {y | r + L < d y}, fderiv ℝ η x = 0 := by
        intro x hx
        have hd_cont : Continuous d := by fun_prop
        have h1 : ∀ᶠ y in nhds x, η y = 0 := by
          have h2 : {y | r + L < d y} ∈ nhds x :=
            IsOpen.mem_nhds (isOpen_lt continuous_const hd_cont) hx
          filter_upwards [h2] with y hy
          have h5 : y ∉ ball x₀ (r + L) := by
            simpa [ball, d] using show r + L ≤ d y from by linarith
          exact hη_zero y h5
        have h1' : η =ᶠ[nhds x] (fun _ => (0 : ℝ)) := h1
        have h_const : HasFDerivAt (fun (_ : E n) => (0 : ℝ)) (0 : E n →L[ℝ] ℝ) x :=
          hasFDerivAt_const (0 : ℝ) x
        have h3 : HasFDerivAt η (0 : E n →L[ℝ] ℝ) x :=
          h_const.congr_of_eventuallyEq h1'
        exact h3.fderiv
      have h_spheres_null : volume (sphere x₀ r ∪ sphere x₀ (r + L)) = 0 := by
        have h1 : volume (sphere x₀ r) = 0 := MeasureTheory.Measure.addHaar_sphere volume x₀ r
        have h2 : volume (sphere x₀ (r + L)) = 0 := MeasureTheory.Measure.addHaar_sphere volume x₀ (r + L)
        have h3 : volume (sphere x₀ r ∪ sphere x₀ (r + L)) ≤ volume (sphere x₀ r) + volume (sphere x₀ (r + L)) := measure_union_le _ _
        have h4 : volume (sphere x₀ r ∪ sphere x₀ (r + L)) ≤ 0 := by
          simpa [h1, h2] using h3
        have h5 : 0 ≤ volume (sphere x₀ r ∪ sphere x₀ (r + L)) := by positivity
        exact le_antisymm h4 h5
      have h_ae : ∀ᵐ x ∂volume, x ∉ sphere x₀ r ∪ sphere x₀ (r + L) := by
        rw [ae_iff]
        have h_set : {x : E n | ¬(x ∉ sphere x₀ r ∪ sphere x₀ (r + L))} = sphere x₀ r ∪ sphere x₀ (r + L) := by
          ext x
          simp only [Set.mem_setOf_eq, Classical.not_not]
          <;> rfl
        rw [h_set]
        exact h_spheres_null
      have h_main : ∀ᵐ x ∂volume, x ∈ (S \ A) → (fderiv ℝ η x) (Φ.toFun x) = 0 := by
        filter_upwards [h_ae] with x hx
        intro hx_SA
        have h_not_in_A : x ∉ A := hx_SA.2
        have h_in_S : x ∈ S := hx_SA.1
        by_cases h1 : d x < r
        · have h2 : fderiv ℝ η x = 0 := h_fderiv_zero_ball x h1
          simp [h2]
        · by_cases h2 : r + L < d x
          · have h3 : fderiv ℝ η x = 0 := h_fderiv_zero_outside x h2
            simp [h3]
          · have h3 : d x = r := by
              have h4 : r ≤ d x := by linarith
              have h5 : d x ≤ r + L := by linarith
              have h6 : ¬(r < d x) := by
                intro h7
                exact h_not_in_A ⟨h_in_S, h7, h5⟩
              linarith
            exact False.elim (hx (Or.inl (by simpa [Metric.mem_sphere, d, dist_eq_norm] using h3)))
      have hSA_meas : MeasurableSet (S \ A) := hS.diff hA_meas
      have h16 : ∀ᵐ x ∂volume.restrict (S \ A), (fderiv ℝ η x) (Φ.toFun x) = 0 := by
        rw [ae_restrict_iff' hSA_meas] <;> exact h_main
      have h18 : ∫ x in (S \ A), (fderiv ℝ η x) (Φ.toFun x) = 0 := by
        have h_congr : ∫ x in (S \ A), (fderiv ℝ η x) (Φ.toFun x) = ∫ x in (S \ A), (0 : ℝ) :=
          setIntegral_congr_ae hSA_meas h_main
        rw [h_congr] <;> simp
      have h_disj : Disjoint A (S \ A) := by simp [A, Set.disjoint_left] <;> tauto
      have hS_eq : S = A ∪ (S \ A) := by ext x; simp [A] <;> tauto
      have h15 : ∫ x in S, (fderiv ℝ η x) (Φ.toFun x) = ∫ x in A, (fderiv ℝ η x) (Φ.toFun x) := by
        rw [hS_eq]
        simpa [h18, add_zero] using setIntegral_union h_disj hSA_meas h_f2_int.integrableOn h_f2_int.integrableOn
      have h_grad_bound : |∫ x in S, (fderiv ℝ η x) (Φ.toFun x)| ≤
          ∫ t in r..(r + L), (w ((t - r) / L) / L) * h_real t := by
        rw [h15]
        have h19 : |∫ x in A, (fderiv ℝ η x) (Φ.toFun x)| ≤ ∫ x in A, ‖(fderiv ℝ η x) (Φ.toFun x)‖ :=
          MeasureTheory.abs_integral_le_integral_abs
        have h_cont1 : Continuous (fun x => ‖(fderiv ℝ η x) (Φ.toFun x)‖) := by fun_prop
        have h_cont2 : Continuous (fun x => g (d x)) := by fun_prop
        have h_compact : IsCompact (closedBall x₀ (r + L)) := isCompact_closedBall x₀ (r + L)
        have hA_sub_cb : A ⊆ closedBall x₀ (r + L) := by
          intro x hx; have h2 : d x ≤ r + L := hx.2.2; simpa [closedBall] using h2
        have h_loc1 : MeasureTheory.LocallyIntegrable (fun x => ‖(fderiv ℝ η x) (Φ.toFun x)‖) volume :=
          h_cont1.locallyIntegrable
        have h_loc2 : MeasureTheory.LocallyIntegrable (fun x => g (d x)) volume :=
          h_cont2.locallyIntegrable
        have h_int_c1 : IntegrableOn (fun x => ‖(fderiv ℝ η x) (Φ.toFun x)‖) (closedBall x₀ (r + L)) volume :=
          h_loc1.integrableOn_isCompact h_compact
        have h_int_c2 : IntegrableOn (fun x => g (d x)) (closedBall x₀ (r + L)) volume :=
          h_loc2.integrableOn_isCompact h_compact
        have h_int1 : IntegrableOn (fun x => ‖(fderiv ℝ η x) (Φ.toFun x)‖) A volume :=
          h_int_c1.mono_set hA_sub_cb
        have h_int2 : IntegrableOn (fun x => g (d x)) A volume :=
          h_int_c2.mono_set hA_sub_cb
        have h20 : ∫ x in A, ‖(fderiv ℝ η x) (Φ.toFun x)‖ ≤ ∫ x in A, g (d x) :=
          MeasureTheory.setIntegral_mono_on h_int1 h_int2 hA_meas (fun x _ => h12 x)
        have h21 : ∫ x in A, g (d x) = ∫ t in r..(r + L), g t * h_real t := h10
        exact h19.trans (h20.trans (le_of_eq h21))
      -- Middle bound
      have h_middle_bound : |∫ x in (S ∩ annulus), η x * divergence Φ.toFun x| ≤
          M_div * (volume annulus).toReal := by
        have h1 : |∫ x in (S ∩ annulus), η x * divergence Φ.toFun x| ≤
            ∫ x in (S ∩ annulus), |η x * divergence Φ.toFun x| :=
          MeasureTheory.abs_integral_le_integral_abs
        have h2 : ∀ x ∈ (S ∩ annulus), |η x * divergence Φ.toFun x| ≤ M_div := by
          intro x _
          have h3 : |η x * divergence Φ.toFun x| = |η x| * |divergence Φ.toFun x| := by rw [abs_mul]
          rw [h3]
          have h4 : |η x| ≤ 1 := by
            have h5 : 0 ≤ η x := smoothStep_range.1
            rw [abs_of_nonneg h5]
            exact smoothStep_range.2
          have h6 : |divergence Φ.toFun x| ≤ M_div := hM_div x
          have h7 : |η x| * |divergence Φ.toFun x| ≤ |divergence Φ.toFun x| :=
            mul_le_of_le_one_left (abs_nonneg _) h4
          exact h7.trans h6
        have h_ann_bdd : Bornology.IsBounded (S ∩ annulus) := hA_bdd
        have h_cont3 : Continuous (fun x => |η x * divergence Φ.toFun x|) := by fun_prop
        have h_loc3 : MeasureTheory.LocallyIntegrable (fun x => |η x * divergence Φ.toFun x|) volume :=
          h_cont3.locallyIntegrable
        have h_compact2 : IsCompact (closedBall x₀ (r + L)) := isCompact_closedBall x₀ (r + L)
        have h_int_c3 : IntegrableOn (fun x => |η x * divergence Φ.toFun x|) (closedBall x₀ (r + L)) volume :=
          h_loc3.integrableOn_isCompact h_compact2
        have h_ann_sub_cb : S ∩ annulus ⊆ closedBall x₀ (r + L) := by
          intro x hx; have h2 : d x ≤ r + L := hx.2.2; simpa [closedBall] using h2
        have h_ann_meas' : MeasurableSet (S ∩ annulus) := hS.inter h_annulus_meas
        have h_int3 : IntegrableOn (fun x => |η x * divergence Φ.toFun x|) (S ∩ annulus) volume :=
          h_int_c3.mono_set h_ann_sub_cb
        have h_int4 : IntegrableOn (fun (_ : E n) => M_div) (S ∩ annulus) volume := by
          have h_loc4 : MeasureTheory.LocallyIntegrable (fun (_ : E n) => M_div) volume :=
            continuous_const.locallyIntegrable
          have hc : IntegrableOn (fun (_ : E n) => M_div) (closedBall x₀ (r + L)) volume :=
            h_loc4.integrableOn_isCompact h_compact2
          exact hc.mono_set h_ann_sub_cb
        have h3 : ∫ x in (S ∩ annulus), |η x * divergence Φ.toFun x| ≤ ∫ x in (S ∩ annulus), M_div :=
          MeasureTheory.setIntegral_mono_on h_int3 h_int4 h_ann_meas' h2
        have h4 : ∫ x in (S ∩ annulus), M_div = M_div * (volume (S ∩ annulus)).toReal := by
          simp [integral_const, Measure.real] <;> ring
        have h_annulus_bdd : Bornology.IsBounded annulus := by
          have h1 : annulus ⊆ closedBall x₀ (r + L) := by
            intro x hx; simpa [closedBall] using hx.2
          exact isBounded_closedBall.subset h1
        have h_vol_fin : volume annulus < ⊤ := h_annulus_bdd.measure_lt_top
        have h_vol_le : volume (S ∩ annulus) ≤ volume annulus := measure_mono Set.inter_subset_right
        have h_toReal_le : (volume (S ∩ annulus)).toReal ≤ (volume annulus).toReal :=
          ENNReal.toReal_mono h_vol_fin.ne h_vol_le
        have h5 : M_div * (volume (S ∩ annulus)).toReal ≤ M_div * (volume annulus).toReal :=
          mul_le_mul_of_nonneg_left h_toReal_le hM_nonneg
        linarith [h1, h3, h4, h5]
      -- Combine
      have h9 : ∫ x in S, divergence ΨtoFun x =
          ∫ x in S, (η x * divergence Φ.toFun x + (fderiv ℝ η x) (Φ.toFun x)) := by
        have h_ae : ∀ᵐ x ∂volume.restrict S, divergence ΨtoFun x = η x * divergence Φ.toFun x + (fderiv ℝ η x) (Φ.toFun x) :=
          ae_of_all _ (fun x => h_product x)
        have h_ae' : ∀ᵐ x, x ∈ S → divergence ΨtoFun x = η x * divergence Φ.toFun x + (fderiv ℝ η x) (Φ.toFun x) :=
          (ae_restrict_iff' hS).mp h_ae
        exact MeasureTheory.setIntegral_congr_ae hS h_ae'
      have h10 : ∫ x in S, (η x * divergence Φ.toFun x + (fderiv ℝ η x) (Φ.toFun x)) =
          (∫ x in S, η x * divergence Φ.toFun x) + (∫ x in S, (fderiv ℝ η x) (Φ.toFun x)) := by
        have h_i1 : IntegrableOn (fun x => η x * divergence Φ.toFun x) S volume := h_f1_int.integrableOn
        have h_i2 : IntegrableOn (fun x => (fderiv ℝ η x) (Φ.toFun x)) S volume := h_f2_int.integrableOn
        simpa using integral_add h_i1 h_i2
      have h11 : ∫ x in S, divergence ΨtoFun x =
          (∫ x in S, η x * divergence Φ.toFun x) + (∫ x in S, (fderiv ℝ η x) (Φ.toFun x)) := by
        rw [h9, h10]
      have h_int_main : ∫ x in (S ∩ ball x₀ r), divergence Φ.toFun x =
          (∫ x in S, divergence ΨtoFun x) -
          (∫ x in (S ∩ annulus), η x * divergence Φ.toFun x) -
          (∫ x in S, (fderiv ℝ η x) (Φ.toFun x)) := by
        set a := ∫ x in (S ∩ ball x₀ r), divergence Φ.toFun x
        set b := ∫ x in (S ∩ annulus), η x * divergence Φ.toFun x
        set c := ∫ x in S, (fderiv ℝ η x) (Φ.toFun x)
        set d := ∫ x in S, η x * divergence Φ.toFun x
        set e := ∫ x in S, divergence ΨtoFun x
        have h12 : d = a + b := by simpa [a, b, d] using h_split1
        have h13 : e = d + c := by simpa [d, c, e] using h11
        linarith
      have h_abs : |∫ x in (S ∩ ball x₀ r), divergence Φ.toFun x| ≤
          |∫ x in S, divergence ΨtoFun x| +
          |∫ x in (S ∩ annulus), η x * divergence Φ.toFun x| +
          |∫ x in S, (fderiv ℝ η x) (Φ.toFun x)| := by
        rw [h_int_main]
        set a := ∫ x in S, divergence ΨtoFun x
        set b := ∫ x in (S ∩ annulus), η x * divergence Φ.toFun x
        set c := ∫ x in S, (fderiv ℝ η x) (Φ.toFun x)
        have h1 : |a - b - c| ≤ |a - b| + |c| := abs_sub _ _
        have h2 : |a - b| ≤ |a| + |b| := abs_sub _ _
        exact h1.trans (add_le_add h2 le_rfl)
      have h_annulus_bdd2 : Bornology.IsBounded annulus := by
        have h1 : annulus ⊆ closedBall x₀ (r + L) := by
          intro x hx; simpa [closedBall] using hx.2
        exact isBounded_closedBall.subset h1
      have h_vol_fin : volume annulus < ⊤ := Bornology.IsBounded.measure_lt_top h_annulus_bdd2
      have h_eq_middle : ENNReal.ofReal (M_div * (volume annulus).toReal) =
          (ENNReal.ofReal M_div) * volume annulus := by
        have h1 : ENNReal.ofReal (M_div * (volume annulus).toReal) =
            ENNReal.ofReal M_div * ENNReal.ofReal ((volume annulus).toReal) :=
          ENNReal.ofReal_mul hM_nonneg
        have h2 : ENNReal.ofReal ((volume annulus).toReal) = volume annulus :=
          ENNReal.ofReal_toReal h_vol_fin.ne
        rw [h1, h2]
      have h_sum : ENNReal.ofReal |∫ x in (S ∩ ball x₀ r), divergence Φ.toFun x| ≤
          ENNReal.ofReal (|∫ x in S, divergence ΨtoFun x| +
          |∫ x in (S ∩ annulus), η x * divergence Φ.toFun x| +
          |∫ x in S, (fderiv ℝ η x) (Φ.toFun x)|) := by
        exact ENNReal.ofReal_le_ofReal h_abs
      have h_nonneg1 : 0 ≤ |∫ x in S, divergence ΨtoFun x| := by positivity
      have h_nonneg2 : 0 ≤ |∫ x in (S ∩ annulus), η x * divergence Φ.toFun x| := by positivity
      have h_nonneg3 : 0 ≤ |∫ x in S, (fderiv ℝ η x) (Φ.toFun x)| := by positivity
      set a := |∫ x in S, divergence ΨtoFun x|
      set b := |∫ x in (S ∩ annulus), η x * divergence Φ.toFun x|
      set c := |∫ x in S, (fderiv ℝ η x) (Φ.toFun x)|
      have h_add : ENNReal.ofReal (a + b + c) =
          ENNReal.ofReal a + ENNReal.ofReal b + ENNReal.ofReal c := by
        have h1 : ENNReal.ofReal ((a + b) + c) = ENNReal.ofReal (a + b) + ENNReal.ofReal c :=
          ENNReal.ofReal_add (add_nonneg h_nonneg1 h_nonneg2) h_nonneg3
        have h2 : ENNReal.ofReal (a + b) = ENNReal.ofReal a + ENNReal.ofReal b :=
          ENNReal.ofReal_add h_nonneg1 h_nonneg2
        rw [h1, h2]
      have h_middle_ennreal : ENNReal.ofReal |∫ x in (S ∩ annulus), η x * divergence Φ.toFun x| ≤
          (ENNReal.ofReal M_div) * volume annulus := by
        rw [← h_eq_middle]
        exact ENNReal.ofReal_le_ofReal h_middle_bound
      calc
        ENNReal.ofReal |∫ x in (S ∩ ball x₀ r), divergence Φ.toFun x|
          ≤ ENNReal.ofReal (|∫ x in S, divergence ΨtoFun x| +
              |∫ x in (S ∩ annulus), η x * divergence Φ.toFun x| +
              |∫ x in S, (fderiv ℝ η x) (Φ.toFun x)|) := h_sum
        _ = ENNReal.ofReal |∫ x in S, divergence ΨtoFun x| +
              ENNReal.ofReal |∫ x in (S ∩ annulus), η x * divergence Φ.toFun x| +
              ENNReal.ofReal |∫ x in S, (fderiv ℝ η x) (Φ.toFun x)| := h_add
        _ ≤ perimeterIn S (ball x₀ (r + L)) +
              (ENNReal.ofReal M_div) * volume annulus +
              ENNReal.ofReal (∫ t in r..(r + L), (w ((t - r) / L) / L) * h_real t) := by
          have h11 : ENNReal.ofReal |∫ x in S, divergence ΨtoFun x| ≤ perimeterIn S (ball x₀ (r + L)) := h_perim_bound
          have h12 : ENNReal.ofReal |∫ x in (S ∩ annulus), η x * divergence Φ.toFun x| ≤ (ENNReal.ofReal M_div) * volume annulus := h_middle_ennreal
          have h13 : ENNReal.ofReal |∫ x in S, (fderiv ℝ η x) (Φ.toFun x)| ≤ ENNReal.ofReal (∫ t in r..(r + L), (w ((t - r) / L) / L) * h_real t) := ENNReal.ofReal_le_ofReal h_grad_bound
          exact add_le_add (add_le_add h11 h12) h13
    -- Take limit L → 0
    have h_vol_tendsto : Tendsto (fun L : ℝ => volume {x : E n | r < d x ∧ d x ≤ r + L})
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      simpa [d] using radial_annulus_volume_tendsto_zero x₀ r
    have h_c_ne_top : ENNReal.ofReal M_div ≠ ⊤ := ofReal_ne_top
    have h_middle_cont : Continuous (fun x : ENNReal => (ENNReal.ofReal M_div) * x) :=
      ENNReal.continuous_const_mul h_c_ne_top
    have h_middle_tendsto : Tendsto (fun L : ℝ => (ENNReal.ofReal M_div) * volume {x : E n | r < d x ∧ d x ≤ r + L})
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      have h : Tendsto (fun L : ℝ => (ENNReal.ofReal M_div) * volume {x : E n | r < d x ∧ d x ≤ r + L})
          (nhdsWithin 0 (Set.Ioi 0)) (nhds ((ENNReal.ofReal M_div) * 0)) :=
        (h_middle_cont.tendsto 0).comp h_vol_tendsto
      have h9 : (ENNReal.ofReal M_div) * 0 = 0 := by simp
      rw [h9] at h
      exact h
    have h_weighted : Tendsto (fun L : ℝ => ∫ t in r..(r + L), (w ((t - r) / L) / L) * h_real t)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (h_real r)) :=
      weighted_average_convergence h_real_local hw_nonneg hw_int C_w hC_w hw_cont r hr_leb
    have h_grad_tendsto : Tendsto (fun L : ℝ => ENNReal.ofReal (∫ t in r..(r + L), (w ((t - r) / L) / L) * h_real t))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (ENNReal.ofReal (h_real r))) :=
      (ENNReal.continuous_ofReal.tendsto (h_real r)).comp h_weighted
    have h_limit : Tendsto (fun L : ℝ => perimeterIn S (ball x₀ (r + L)) +
        (ENNReal.ofReal M_div) * volume {x : E n | r < d x ∧ d x ≤ r + L} +
        ENNReal.ofReal (∫ t in r..(r + L), (w ((t - r) / L) / L) * h_real t))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (perimeterIn S (ball x₀ r) + H r)) := by
        rw [hH_r]
        have h_ab : Tendsto (fun L : ℝ => perimeterIn S (ball x₀ (r + L)) +
            (ENNReal.ofReal M_div) * volume {x : E n | r < d x ∧ d x ≤ r + L})
          (nhdsWithin 0 (Set.Ioi 0)) (nhds (perimeterIn S (ball x₀ r) + 0)) :=
          hr_right.add h_middle_tendsto
        have h_abc : Tendsto (fun L : ℝ => (perimeterIn S (ball x₀ (r + L)) +
            (ENNReal.ofReal M_div) * volume {x : E n | r < d x ∧ d x ≤ r + L}) +
            ENNReal.ofReal (∫ t in r..(r + L), (w ((t - r) / L) / L) * h_real t))
          (nhdsWithin 0 (Set.Ioi 0)) (nhds ((perimeterIn S (ball x₀ r) + 0) + ENNReal.ofReal (h_real r))) :=
          h_ab.add h_grad_tendsto
        have h_simp : (perimeterIn S (ball x₀ r) + 0) + ENNReal.ofReal (h_real r) =
            perimeterIn S (ball x₀ r) + ENNReal.ofReal (h_real r) := by simp
        rw [h_simp] at h_abc
        exact h_abc
    have h6 : ∀ᶠ (L : ℝ) in nhdsWithin 0 (Set.Ioi 0),
        ENNReal.ofReal |∫ x in (S ∩ ball x₀ r), divergence Φ.toFun x| ≤
        perimeterIn S (ball x₀ (r + L)) +
        (ENNReal.ofReal M_div) * volume {x : E n | r < d x ∧ d x ≤ r + L} +
        ENNReal.ofReal (∫ t in r..(r + L), (w ((t - r) / L) / L) * h_real t) := by
      filter_upwards [self_mem_nhdsWithin, h_eventually] with L hL1 hL2
      exact h_goal L hL1 hL2
    have h_const : Tendsto (fun (_ : ℝ) => ENNReal.ofReal |∫ x in (S ∩ ball x₀ r), divergence Φ.toFun x|)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (ENNReal.ofReal |∫ x in (S ∩ ball x₀ r), divergence Φ.toFun x|)) :=
      tendsto_const_nhds
    exact le_of_tendsto_of_tendsto h_const h_limit h6
  have h_final : perimeter (S ∩ ball x₀ r) ≤ perimeterIn S (ball x₀ r) + H r := by
    rw [perimeter]
    exact iSup_le h_main
  exact h_final

end NGeTwo

end Geometry.Perimeter
