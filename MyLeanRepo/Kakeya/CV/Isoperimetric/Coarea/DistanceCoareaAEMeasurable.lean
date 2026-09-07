import MyLeanRepo.Kakeya.CV.Isoperimetric.Coarea.DistanceCoareaLower
import MyLeanRepo.Kakeya.CV.Isoperimetric.Measure.Eilenberg
import MyLeanRepo.Kakeya.CV.Isoperimetric.InnerMinkowski.Basic
import Mathlib.Tactic

/-!
# Distance-from-point coarea integrand AEMeasurability

Proves that for a measurable set `B ⊆ E^n` and `x₀ : E^n`, the function
`t ↦ μHE[n-1](B ∩ sphere x₀ t)` is `AEStronglyMeasurable` w.r.t. Lebesgue volume.

**Proof via polar coordinates + Fubini:**

1. Let `F(t, y) = x₀ + t • y` and `A = F ⁻¹' B`. Since `F` is continuous and
   `B` is measurable, `A` is a measurable subset of `ℝ × E^n`.
2. Let `ν = μHE[n-1].restrict(sphere 0 1)`. The unit sphere has finite
   `(n-1)`-dimensional Hausdorff measure, so `ν` is a finite measure.
3. By `measurable_measure_prodMk_left`, the slice function
   `f(t) := ν({y | (t, y) ∈ A})` is measurable.
4. For `t > 0`, the homothety `y ↦ x₀ + t • y` maps
   `B_t := {y ∈ sphere 0 1 | x₀ + t • y ∈ B}` onto `B ∩ sphere x₀ t`.
   By Hausdorff measure scaling:
   `μHE[n-1](B ∩ sphere x₀ t) = t^(n-1) · μHE[n-1](B_t) = t^(n-1) · f(t)`.
5. For `t < 0`, `sphere x₀ t = ∅`, so both sides are 0. Thus
   `t ↦ μHE[n-1](B ∩ sphere x₀ t)` equals the measurable function
   `t ↦ (t : ENNReal)^(n-1) · f(t)` for all `t ≠ 0`, hence a.e.

The finiteness of the unit sphere Hausdorff measure is proved via the
Eilenberg inequality applied to the norm function `f(x) = ‖x‖` on the
closed unit ball.
-/


open MeasureTheory Metric Set ENNReal Filter
open scoped MeasureTheory Pointwise

namespace Geometry

variable {n : ℕ} [Nonempty (Fin n)]

/-- Finiteness of unit sphere Hausdorff measure, via Eilenberg inequality + scaling. -/
lemma sphere_hausdorff_finite (hn : 2 ≤ n) :
    μHE[n - 1] (sphere (0 : E n) 1) < ⊤ := by
  let f : E n → ℝ := fun x => ‖x‖
  have hf : LipschitzWith 1 f := by
    intro x y
    have h : |‖x‖ - ‖y‖| ≤ ‖x - y‖ := abs_norm_sub_norm_le x y
    have h' : dist (‖x‖) (‖y‖) ≤ dist x y := by
      simpa [dist_eq_norm, Real.dist_eq] using h
    simpa [LipschitzWith, edist_dist] using ENNReal.ofReal_le_ofReal h'
  rcases eilenberg_μHE hn (hf := hf) (by norm_num) with ⟨C, hC_ne_top, hC_pos, h_eilenberg⟩
  let Bball : Set (E n) := closedBall (0 : E n) 1
  have hB_meas : MeasurableSet Bball := isClosed_closedBall.measurableSet
  have hB_fin : volume Bball < ⊤ := Metric.isBounded_closedBall.measure_lt_top
  have h1 : ∫⁻ (s : ℝ), μHE[n - 1] (Bball ∩ f ⁻¹' {s}) ≤ C * volume Bball := h_eilenberg Bball
  have h2 : ∀ s ∈ Set.Ioc (0 : ℝ) 1, Bball ∩ f ⁻¹' {s} = sphere (0 : E n) s := by
    intro s hs
    have hs_le_one : s ≤ 1 := hs.2
    ext x
    have h_fx : f x = ‖x‖ := by rfl
    have h_ball : x ∈ Bball ↔ ‖x‖ ≤ 1 := by
      simp [Bball, Metric.mem_closedBall, dist_eq_norm]
    have h_sphere : x ∈ sphere (0 : E n) s ↔ ‖x‖ = s := by
      simp [sphere, dist_eq_norm]
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · rintro ⟨_, hnorm⟩
      have h_goal : ‖x‖ = s := by rw [←h_fx] <;> exact hnorm
      exact h_sphere.mpr h_goal
    · intro hnorm
      have h_eq : ‖x‖ = s := h_sphere.mp hnorm
      have hball : x ∈ Bball := h_ball.mpr (by rw [h_eq] <;> exact hs_le_one)
      have hpreim : f x = s := by rw [h_fx, h_eq]
      exact ⟨hball, hpreim⟩
  let H : ℝ → ENNReal := fun s => μHE[n - 1] (sphere (0 : E n) s)
  have h_in : ∀ᵐ (s : ℝ) ∂volume.restrict (Set.Ioc (0 : ℝ) 1), s ∈ Set.Ioc (0 : ℝ) 1 :=
    ae_restrict_mem measurableSet_Ioc
  have h_eq_ae : ∀ᵐ (s : ℝ) ∂volume.restrict (Set.Ioc (0 : ℝ) 1),
      μHE[n - 1] (Bball ∩ f ⁻¹' {s}) = H s := by
    filter_upwards [h_in] with s hs
    exact congr_arg (μHE[n - 1]) (h2 s hs)
  have h5 : ∫⁻ s in Set.Ioc (0 : ℝ) 1, μHE[n - 1] (Bball ∩ f ⁻¹' {s}) ≤
      ∫⁻ (s : ℝ), μHE[n - 1] (Bball ∩ f ⁻¹' {s}) :=
    lintegral_mono' Measure.restrict_le_self (fun _ => le_refl _)
  have h6 : ∫⁻ s in Set.Ioc (0 : ℝ) 1, μHE[n - 1] (Bball ∩ f ⁻¹' {s}) =
      ∫⁻ s in Set.Ioc (0 : ℝ) 1, H s :=
    lintegral_congr_ae h_eq_ae
  rw [h6] at h5
  have h4 : ∫⁻ s in Set.Ioc (0 : ℝ) 1, H s ≤ C * volume Bball := le_trans h5 h1
  have h7 : (∫⁻ s in Set.Ioc (0 : ℝ) 1, H s) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top hC_ne_top hB_fin.ne) h4
  have h_pos : volume (Set.Ioc (0 : ℝ) 1) ≠ 0 := by
    have h9 : volume (Set.Ioc (0 : ℝ) 1) = 1 := by
      rw [Real.volume_Ioc] <;> norm_num
    rw [h9]; simp
  -- Find s0 ∈ Ioc 0 1 with H s0 < ⊤, by contradiction using finiteness of lintegral
  by_cases h_exists : ∃ (s0 : ℝ), s0 ∈ Set.Ioc (0 : ℝ) 1 ∧ H s0 < ⊤
  · rcases h_exists with ⟨s0, hs0_in, hs0_fin⟩
    have hs0_pos : 0 < s0 := hs0_in.1
    have h_sphere_scale : sphere (0 : E n) 1 = (s0⁻¹ : ℝ) • sphere (0 : E n) s0 := by
      ext y
      simp only [Metric.mem_sphere, Set.mem_smul_set]
      constructor
      · intro hy
        have h_norm_y : ‖y‖ = 1 := by simpa [dist_eq_norm] using hy
        refine ⟨s0 • y, ?_, ?_⟩
        · have h0 : dist (s0 • y) 0 = ‖s0 • y‖ := by
            rw [dist_eq_norm] <;> simp
          have h1 : dist (s0 • y) 0 = s0 := by
            rw [h0, norm_smul, Real.norm_eq_abs, abs_of_pos hs0_pos, h_norm_y] <;> ring
          exact h1
        · have h3 : (s0⁻¹ : ℝ) • (s0 • y) = ((s0⁻¹ * s0) : ℝ) • y := by
            rw [smul_smul]
          have h4 : (s0⁻¹ * s0 : ℝ) = 1 := by field_simp [hs0_pos.ne']
          have h2 : (s0⁻¹ : ℝ) • (s0 • y) = y := by
            rw [h3, h4, one_smul]
          exact h2
      · rintro ⟨z, hz, rfl⟩
        have h_norm_z : ‖z‖ = s0 := by simpa [dist_eq_norm] using hz
        have h_pos2 : 0 < (s0⁻¹ : ℝ) := by positivity
        have h0 : dist ((s0⁻¹ : ℝ) • z) 0 = ‖(s0⁻¹ : ℝ) • z‖ := by
          rw [dist_eq_norm] <;> simp
        have h1 : dist ((s0⁻¹ : ℝ) • z) 0 = 1 := by
          rw [h0, norm_smul, Real.norm_eq_abs, abs_of_pos h_pos2, h_norm_z]
          <;> field_simp [hs0_pos.ne']
        exact h1
    have h_pos2 : 0 < (s0⁻¹ : ℝ) := by positivity
    have h_nn : ‖(s0⁻¹ : ℝ)‖₊ = ⟨s0⁻¹, h_pos2.le⟩ := by
      apply NNReal.coe_injective
      calc (↑‖(s0⁻¹ : ℝ)‖₊ : ℝ)
        = ‖(s0⁻¹ : ℝ)‖ := by exact coe_nnnorm (s0⁻¹)
      _ = |(s0⁻¹ : ℝ)| := by exact Real.norm_eq_abs (s0⁻¹)
      _ = (s0⁻¹ : ℝ) := abs_of_pos h_pos2
      _ = ↑(⟨s0⁻¹, h_pos2.le⟩ : NNReal) := by simp
    have h_scale : μHE[n - 1] (sphere (0 : E n) 1) =
        ENNReal.ofReal (s0⁻¹) ^ (n - 1) * μHE[n - 1] (sphere (0 : E n) s0) := by
      rw [h_sphere_scale]
      have h_raw := MeasureTheory.Measure.euclideanHausdorffMeasure_smul₀ (n - 1)
        (show (s0⁻¹ : ℝ) ≠ 0 from by positivity) (sphere (0 : E n) s0)
      rw [h_raw]
      have h9 : (‖(s0⁻¹ : ℝ)‖₊ ^ (n - 1)) • μHE[n - 1] (sphere (0 : E n) s0) =
          (‖(s0⁻¹ : ℝ)‖₊ ^ (n - 1)) * μHE[n - 1] (sphere (0 : E n) s0) :=
        smul_eq_mul _ _
      rw [h9]
      have h10 : (‖(s0⁻¹ : ℝ)‖₊ : ENNReal) = ENNReal.ofReal (s0⁻¹) := by
        rw [ENNReal.ofReal_eq_coe_nnreal h_pos2.le, h_nn] <;> rfl
      rw [h10] <;> ring
    rw [h_scale]
    have h_lt_top1 : ENNReal.ofReal (s0⁻¹) ^ (n - 1) < ⊤ := by
      have h1 : ENNReal.ofReal (s0⁻¹) ≠ ⊤ := ENNReal.ofReal_ne_top
      have h2 : ENNReal.ofReal (s0⁻¹) ^ (n - 1) ≠ ⊤ := ENNReal.pow_ne_top h1
      exact h2.lt_top
    have h_lt_top2 : μHE[n - 1] (sphere (0 : E n) s0) < ⊤ := by
      simpa [H] using hs0_fin
    exact ENNReal.mul_lt_top h_lt_top1 h_lt_top2
  · -- No such s0: H s = ⊤ for all s ∈ Ioc 0 1, contradicting finite lintegral
    have h_contra : ∀ s ∈ Set.Ioc (0 : ℝ) 1, H s = ⊤ := by
      intro s hs
      have h9 : ¬(H s < ⊤) := by
        intro h10
        exact h_exists ⟨s, hs, h10⟩
      have h10 : H s = ⊤ := by
        by_contra h11
        have h12 : H s < ⊤ := lt_top_iff_ne_top.mpr h11
        exact h9 h12
      exact h10
    have h_ae_top : ∀ᵐ (s : ℝ) ∂volume.restrict (Set.Ioc (0 : ℝ) 1), H s = ⊤ := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      exact h_contra s hs
    have h_eq : ∫⁻ s in Set.Ioc (0 : ℝ) 1, H s = ⊤ := by
      rw [lintegral_congr_ae h_ae_top]
      simp [h_pos, ENNReal.top_mul]
    exfalso
    exact h7 h_eq

/-- **AEMeasurability of the distance-from-point coarea integrand.** -/
lemma distance_coarea_aemeasurable (hn : 2 ≤ n)
    (x₀ : E n) (B : Set (E n)) (hB : MeasurableSet B) :
    AEStronglyMeasurable (fun t : ℝ => μHE[n - 1] (B ∩ sphere x₀ t)) volume := by
  let F : ℝ × E n → E n := fun p => x₀ + p.1 • p.2
  have hF_cont : Continuous F :=
    continuous_const.add (continuous_fst.smul continuous_snd)
  let A : Set (ℝ × E n) := F ⁻¹' B
  have hA_meas : MeasurableSet A := hB.preimage hF_cont.measurable
  let ν : Measure (E n) := μHE[n - 1].restrict (sphere (0 : E n) 1)
  have hν_finite : ν Set.univ < ⊤ := by
    have h1 : ν Set.univ = μHE[n - 1] (sphere (0 : E n) 1) := by
      simp [ν] <;> rfl
    rw [h1]
    exact sphere_hausdorff_finite hn
  letI : IsFiniteMeasure ν := ⟨hν_finite⟩
  let f : ℝ → ENNReal := fun t => ν (Prod.mk t ⁻¹' A)
  have hf_meas : Measurable f := measurable_measure_prodMk_left hA_meas
  let g : ℝ → ENNReal := fun t => ENNReal.ofReal t ^ (n - 1)
  have hg_meas : Measurable g := by fun_prop
  have h_main : ∀ (t : ℝ), t ≠ 0 →
      μHE[n - 1] (B ∩ sphere x₀ t) = g t * f t := by
    intro t ht
    by_cases hpos : 0 < t
    · -- t > 0
      let Bt := {y : E n | x₀ + t • y ∈ B} ∩ sphere (0 : E n) 1
      let φ : E n → E n := fun y => x₀ + t • y
      have h1 : Prod.mk t ⁻¹' A = {y : E n | x₀ + t • y ∈ B} := by
        ext y; simp [A, F] <;> rfl
      have h_cont : Continuous (fun y : E n => (t, y)) := by fun_prop
      have h_meas_set : MeasurableSet (Prod.mk t ⁻¹' A) := hA_meas.preimage h_cont.measurable
      have h2 : f t = μHE[n - 1] Bt := by
        dsimp only [f, ν]
        rw [Measure.restrict_apply h_meas_set, h1] <;> rfl
      have h3 : φ '' Bt = B ∩ sphere x₀ t := by
        ext z
        simp only [Bt, φ, Set.mem_image, Set.mem_inter_iff, Metric.mem_sphere]
        constructor
        · rintro ⟨y, ⟨hyS, hysphere⟩, rfl⟩
          have h_norm : ‖y‖ = 1 := by simpa [Metric.mem_sphere, dist_eq_norm] using hysphere
          have h_dist : dist (x₀ + t • y) x₀ = t := by
            rw [dist_eq_norm, add_sub_cancel_left, norm_smul]
            rw [Real.norm_eq_abs, abs_of_pos hpos, h_norm] <;> ring
          exact ⟨hyS, h_dist⟩
        · rintro ⟨hzS, hzsphere⟩
          have h4 : ‖z - x₀‖ = t := by simpa [sphere, dist_eq_norm] using hzsphere
          let y : E n := t⁻¹ • (z - x₀)
          have hyS : x₀ + t • y ∈ B := by
            have h_eq : x₀ + t • y = z := by
              simp [y, smul_smul, hpos.ne'] <;> abel
            rw [h_eq]; exact hzS
          have hysphere : y ∈ sphere (0 : E n) 1 := by
            have h_norm : ‖t⁻¹ • (z - x₀)‖ = 1 := by
              rw [norm_smul, Real.norm_eq_abs, abs_of_pos (show 0 < t⁻¹ by positivity), h4]
              <;> field_simp [hpos.ne'] <;> ring
            simpa [y, Metric.mem_sphere, dist_eq_norm] using h_norm
          exact ⟨y, ⟨hyS, hysphere⟩, by simp [y, smul_smul, hpos.ne'] <;> abel⟩
      have h_isom : Isometry (fun z : E n => x₀ + z) := by
        intro z w; simp [dist_eq_norm] <;> rfl
      have h41 : μHE[n - 1] ((fun z : E n => x₀ + z) '' (t • Bt)) = μHE[n - 1] (t • Bt) :=
        Isometry.euclideanHausdorffMeasure_image h_isom (t • Bt)
      have h_norm_t : ‖(t : ℝ)‖₊ = ⟨t, hpos.le⟩ := by
        apply NNReal.coe_injective
        calc (↑‖(t : ℝ)‖₊ : ℝ)
          = ‖(t : ℝ)‖ := by exact coe_nnnorm t
        _ = |t| := by exact Real.norm_eq_abs t
        _ = t := abs_of_pos hpos
        _ = ↑(⟨t, hpos.le⟩ : NNReal) := by simp
      have h42 : μHE[n - 1] (t • Bt) = ENNReal.ofReal t ^ (n - 1) * μHE[n - 1] Bt := by
        have h_raw := MeasureTheory.Measure.euclideanHausdorffMeasure_smul₀ (n - 1)
          (show (t : ℝ) ≠ 0 from hpos.ne') Bt
        rw [h_raw]
        have h9 : (‖(t : ℝ)‖₊ ^ (n - 1)) • μHE[n - 1] Bt =
            (‖(t : ℝ)‖₊ ^ (n - 1)) * μHE[n - 1] Bt :=
          smul_eq_mul _ _
        rw [h9]
        have h10 : (‖(t : ℝ)‖₊ : ENNReal) = ENNReal.ofReal t := by
          rw [ENNReal.ofReal_eq_coe_nnreal hpos.le, h_norm_t] <;> rfl
        rw [h10] <;> ring
      have h43 : φ '' Bt = (fun z : E n => x₀ + z) '' (t • Bt) := by
        ext z
        simp only [φ, Set.mem_image]
        constructor
        · rintro ⟨y, hy, h_eq⟩
          exact ⟨t • y, Set.smul_mem_smul_set hy, h_eq⟩
        · rintro ⟨w, hw, h_eq⟩
          have h_exists : ∃ (y : E n), y ∈ Bt ∧ t • y = w := by
            simpa [Set.mem_smul_set] using hw
          rcases h_exists with ⟨y, hy, hwy⟩
          have h_goal : x₀ + t • y = z := by
            calc x₀ + t • y = x₀ + w := by rw [hwy]
                          _ = z := h_eq
          exact ⟨y, hy, h_goal⟩
      have h4 : μHE[n - 1] (φ '' Bt) = ENNReal.ofReal t ^ (n - 1) * μHE[n - 1] Bt := by
        rw [h43, h41, h42]
      have h5 : g t = ENNReal.ofReal t ^ (n - 1) := by rfl
      have h_goal : μHE[n - 1] (B ∩ sphere x₀ t) = g t * f t := by
        calc μHE[n - 1] (B ∩ sphere x₀ t)
          = μHE[n - 1] (φ '' Bt) := by rw [h3]
        _ = ENNReal.ofReal t ^ (n - 1) * μHE[n - 1] Bt := h4
        _ = g t * μHE[n - 1] Bt := by rw [h5] <;> ring
        _ = g t * f t := by rw [h2]
      exact h_goal
    · -- t < 0
      have hnonpos : t ≤ 0 := by linarith
      have hneg : t < 0 := lt_of_le_of_ne hnonpos ht
      have h_empty : sphere x₀ t = ∅ := by
        ext x
        have h1 : x ∈ sphere x₀ t ↔ dist x x₀ = t := by simp [sphere]
        rw [h1]
        have h2 : ¬(dist x x₀ = t) := by
          intro h3
          have h4 : 0 ≤ dist x x₀ := dist_nonneg
          rw [h3] at h4
          linarith [hneg]
        simpa using h2
      have hH_zero : μHE[n - 1] (B ∩ sphere x₀ t) = 0 := by
        rw [h_empty] <;> simp
      have h_n_minus_one_ne_zero : n - 1 ≠ 0 := by omega
      have hg_zero : g t = 0 := by
        have h6 : ENNReal.ofReal t = 0 := by
          rw [ENNReal.ofReal_eq_zero] <;> linarith
        have h7 : g t = ENNReal.ofReal t ^ (n - 1) := by rfl
        rw [h7, h6]
        exact zero_pow h_n_minus_one_ne_zero
      rw [hH_zero, hg_zero] <;> ring
  have h_null : volume ({0} : Set ℝ) = 0 := by simp
  have h_ae : ∀ᵐ (t : ℝ) ∂volume, t ≠ 0 := by
    simpa [ae_iff] using h_null
  have h_final : ∀ᵐ (t : ℝ) ∂volume,
      (g t * f t) = μHE[n - 1] (B ∩ sphere x₀ t) := by
    filter_upwards [h_ae] with t ht
    exact (h_main t ht).symm
  exact (hg_meas.mul hf_meas).aestronglyMeasurable.congr h_final

/-- **`FunctionLevelMeasurable` for distance from a point.** -/
lemma point_distance_level_measurable (hn : 2 ≤ n) (x₀ : E n) :
    FunctionLevelMeasurable (fun x : E n => dist x x₀) := by
  intro B hB a b
  have h_set_eq : ∀ (s : ℝ), {x ∈ B | dist x x₀ = s} = B ∩ sphere x₀ s := by
    intro s
    ext x
    simp [sphere, Set.mem_sep_iff] <;> tauto
  have h_eq : (fun s : ℝ => μHE[n - 1] {x ∈ B | dist x x₀ = s}) =
      fun s : ℝ => μHE[n - 1] (B ∩ sphere x₀ s) := by
    funext s
    rw [h_set_eq s]
  rw [h_eq]
  have h3 := distance_coarea_aemeasurable hn x₀ B hB
  rcases h3 with ⟨g, hg_meas, h_eq2⟩
  have h_ae_mono : ae (volume.restrict (Set.Ioc a b)) ≤ ae volume := by
    exact MeasureTheory.ae_mono Measure.restrict_le_self
  have h_eq3 : (fun t : ℝ => μHE[n - 1] (B ∩ sphere x₀ t)) =ᵐ[volume.restrict (Set.Ioc a b)] g :=
    h_eq2.filter_mono h_ae_mono
  have h4 : AEStronglyMeasurable (fun t : ℝ => μHE[n - 1] (B ∩ sphere x₀ t)) (volume.restrict (Set.Ioc a b)) :=
    ⟨g, hg_meas, h_eq3⟩
  exact h4.aemeasurable

/-- **Point-distance coarea lower bound.** -/
theorem distance_coarea_lower_point (hn : 2 ≤ n) (x₀ : E n)
    {A : Set (E n)} (hA : MeasurableSet A) (hA_bdd : Bornology.IsBounded A)
    (hA_sub : A ⊆ {x | 0 < dist x x₀})
    {a b : ℝ} (hab : a < b) {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1) :
    volume {x ∈ A | a < dist x x₀ ∧ dist x x₀ ≤ b} ≥
      ENNReal.ofReal (((1 - ε) ^ (n - 1 : ℕ)) / ((1 + ε) ^ n)) *
      ∫⁻ s in Set.Ioc a b, μHE[n - 1] {x ∈ A | dist x x₀ = s} := by
  let C : Set (E n) := {x₀}
  have hC : IsClosed C := isClosed_singleton
  have hne : C.Nonempty := singleton_nonempty x₀
  have h_infDist : ∀ (x : E n), infDist x C = dist x x₀ := by
    intro x
    exact Metric.infDist_singleton
  have h_infDist' : (fun x : E n => infDist x C) = fun x => dist x x₀ := by
    funext x; exact h_infDist x
  have h_d_meas : FunctionLevelMeasurable (fun x : E n => infDist x C) := by
    rw [h_infDist']
    exact point_distance_level_measurable hn x₀
  have hA_sub' : A ⊆ {x | 0 < infDist x C} := by
    intro x hx
    have h4 : 0 < dist x x₀ := hA_sub hx
    simpa [h_infDist] using h4
  have h_main := distance_coarea_lower hn
    (hC := hC) (hne := hne) (h_d_meas := h_d_meas)
    (hA := hA) (hA_bdd := hA_bdd)
    (hA_sub := hA_sub') (hab := hab) (hε := hε) (hε2 := hε2)
  have h_final : volume {x ∈ A | a < infDist x C ∧ infDist x C ≤ b} =
      volume {x ∈ A | a < dist x x₀ ∧ dist x x₀ ≤ b} := by
    congr with x; simp [h_infDist] <;> rfl
  have h_final2 : ∫⁻ s in Set.Ioc a b, μHE[n - 1] {x ∈ A | infDist x C = s} =
      ∫⁻ s in Set.Ioc a b, μHE[n - 1] {x ∈ A | dist x x₀ = s} := by
    congr with s; congr with x; simp [h_infDist] <;> rfl
  rw [h_final, h_final2] at h_main
  exact h_main

end Geometry
