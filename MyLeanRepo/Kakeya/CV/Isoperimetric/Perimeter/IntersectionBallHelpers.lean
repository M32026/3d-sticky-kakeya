import MyLeanRepo.Kakeya.CV.Isoperimetric.Perimeter.Basic
import MyLeanRepo.Kakeya.CV.Isoperimetric.Perimeter.PerimeterMeasure
import MyLeanRepo.Kakeya.CV.Isoperimetric.Perimeter.CutoffFunctions
import MyLeanRepo.Kakeya.CV.Isoperimetric.Coarea.DistanceCoareaEq
import MyLeanRepo.Kakeya.CV.Isoperimetric.Measure.LevelSetMeasurability
import MyLeanRepo.Kakeya.CV.Isoperimetric.InnerMinkowski.Basic
import Mathlib.Tactic

/-!
# Helper lemmas for IntersectionBallStub

Extracted from IntersectionBall.lean. These are independent of the broken
main theorem and compile cleanly.

## Main results

- `divergence_product_rule`: product rule for divergence
- `oneSided_lebesgueDifferentiation`: one-sided Lebesgue differentiation
- `H_zero_of_nonpos`, `H_locally_integrable`, `h_real_locally_integrable`
- `weighted_average_convergence`: weighted approximate identity limit
-/


open MeasureTheory Metric Set ENNReal Filter
open scoped MeasureTheory ContDiff

namespace Geometry.Perimeter

variable {n : ℕ}

/-- Product rule: `div(η • Φ) = (fderiv η)(Φ) + η · div Φ`. -/
lemma divergence_product_rule {η : E n → ℝ} {Φ : E n → E n}
    (hη : ContDiff ℝ 1 η) (hΦ : ContDiff ℝ 1 Φ) :
    ∀ (x : E n), divergence (fun y => η y • Φ y) x =
        (fderiv ℝ η x) (Φ x) + η x * divergence Φ x := by
  intro x
  have h1 : ∀ (i : Fin n), HasFDerivAt (fun y : E n => η y * Φ y i)
      ((Φ x i) • fderiv ℝ η x + (η x) • fderiv ℝ (fun y : E n => Φ y i) x) x := by
    intro i
    have hη' : HasFDerivAt η (fderiv ℝ η x) x :=
      (ContDiff.contDiffAt hη).differentiableAt (by norm_num) |>.hasFDerivAt
    have hΦ_diff : DifferentiableAt ℝ Φ x := (hΦ.differentiable (by norm_num)).differentiableAt
    have h_proj_diff : Differentiable ℝ (fun z : E n => z i) := by
      let proj : (E n) →L[ℝ] ℝ :=
        { toFun := fun z => z i
          map_add' := fun x y => by simp
          map_smul' := fun c x => by simp }
      exact proj.differentiable
    have hΦi_diff : DifferentiableAt ℝ (fun y : E n => Φ y i) x :=
      h_proj_diff.differentiableAt.comp x hΦ_diff
    have hΦi : HasFDerivAt (fun y : E n => Φ y i) (fderiv ℝ (fun y : E n => Φ y i) x) x :=
      hΦi_diff.hasFDerivAt
    have h_mul : HasFDerivAt (fun y : E n => η y * Φ y i)
        ((η x) • fderiv ℝ (fun y : E n => Φ y i) x + (Φ x i) • fderiv ℝ η x) x :=
      hη'.mul hΦi
    have h_comm : (η x) • fderiv ℝ (fun y : E n => Φ y i) x + (Φ x i) • fderiv ℝ η x =
        (Φ x i) • fderiv ℝ η x + (η x) • fderiv ℝ (fun y : E n => Φ y i) x := by
      exact add_comm _ _
    rw [h_comm] at h_mul
    exact h_mul
  have h2 : ∀ (i : Fin n), fderiv ℝ (fun y : E n => η y * Φ y i) x =
      (Φ x i) • fderiv ℝ η x + (η x) • fderiv ℝ (fun y : E n => Φ y i) x := by
    intro i
    exact (h1 i).fderiv
  have h_smul : ∀ (i : Fin n), (fun y : E n => (η y • Φ y) i) = (fun y : E n => η y * Φ y i) := by
    intro i; funext y; simp
  have h_target : ∑ i : Fin n, (fderiv ℝ (fun y : E n => (η y • Φ y) i) x) (EuclideanSpace.single i 1) =
      ∑ i : Fin n, (fderiv ℝ (fun y : E n => η y * Φ y i) x) (EuclideanSpace.single i 1) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [h_smul i]
  have h_sum : ∑ i : Fin n, (fderiv ℝ (fun y : E n => η y * Φ y i) x) (EuclideanSpace.single i 1) =
      ∑ i : Fin n, (((Φ x i) • fderiv ℝ η x + (η x) • fderiv ℝ (fun y : E n => Φ y i) x)
        (EuclideanSpace.single i 1)) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [h2 i]
  have h_add_apply : ∀ (i : Fin n),
      ((Φ x i) • fderiv ℝ η x + (η x) • fderiv ℝ (fun y : E n => Φ y i) x)
        (EuclideanSpace.single i 1) =
      ((Φ x i) • fderiv ℝ η x) (EuclideanSpace.single i 1) +
      ((η x) • fderiv ℝ (fun y : E n => Φ y i) x) (EuclideanSpace.single i 1) := by
    intro i
    exact ContinuousLinearMap.add_apply _ _ _
  have h_smul1 : ∀ (i : Fin n),
      ((Φ x i) • fderiv ℝ η x) (EuclideanSpace.single i 1) =
      (Φ x i) * (fderiv ℝ η x) (EuclideanSpace.single i 1) := by
    intro i
    exact ContinuousLinearMap.smul_apply _ _ _
  have h_smul2 : ∀ (i : Fin n),
      ((η x) • fderiv ℝ (fun y : E n => Φ y i) x) (EuclideanSpace.single i 1) =
      (η x) * (fderiv ℝ (fun y : E n => Φ y i) x) (EuclideanSpace.single i 1) := by
    intro i
    exact ContinuousLinearMap.smul_apply _ _ _
  have h_expand : Φ x = ∑ i : Fin n, (Φ x i) • EuclideanSpace.single i 1 := by
    let b := PiLp.basisFun 2 ℝ (Fin n)
    have hsum : ∑ i : Fin n, b.repr (Φ x) i • b i = Φ x := b.sum_repr (Φ x)
    have h2 : ∀ i, b.repr (Φ x) i = Φ x i := by
      intro i; simp [b, PiLp.basisFun_apply] <;> rfl
    have h3 : ∀ i, b i = EuclideanSpace.single i 1 := by
      intro i; simp [b, PiLp.basisFun_apply] <;> rfl
    have h4 : ∑ i : Fin n, b.repr (Φ x) i • b i = ∑ i : Fin n, (Φ x i) • EuclideanSpace.single i 1 := by
      apply Finset.sum_congr rfl; intro i _; rw [h2 i, h3 i]
    exact hsum.symm.trans h4
  have h_first : ∑ i : Fin n, (Φ x i) * (fderiv ℝ η x) (EuclideanSpace.single i 1) =
      (fderiv ℝ η x) (Φ x) := by
    have h_step1 : (fderiv ℝ η x) (Φ x) =
        (fderiv ℝ η x) (∑ i : Fin n, (Φ x i) • EuclideanSpace.single i 1) :=
      congr_arg (fderiv ℝ η x) h_expand
    have h_step2 : (fderiv ℝ η x) (∑ i : Fin n, (Φ x i) • EuclideanSpace.single i 1) =
        ∑ i : Fin n, (fderiv ℝ η x) ((Φ x i) • EuclideanSpace.single i 1) := by
      exact map_sum (fderiv ℝ η x) (fun x_1 => (Φ x).ofLp x_1 • EuclideanSpace.single x_1 1) Finset.univ
    have h_step3 : ∑ i : Fin n, (fderiv ℝ η x) ((Φ x i) • EuclideanSpace.single i 1) =
        ∑ i : Fin n, (Φ x i) * (fderiv ℝ η x) (EuclideanSpace.single i 1) := by
      apply Finset.sum_congr rfl
      intro i _
      have h3 : (fderiv ℝ η x) ((Φ x i) • EuclideanSpace.single i 1) =
          (Φ x i) * (fderiv ℝ η x) (EuclideanSpace.single i 1) := by
        rw [ContinuousLinearMap.map_smul] <;> rfl
      exact h3
    exact h_step3.symm.trans (h_step2.symm.trans h_step1.symm)
  have h_second : ∑ i : Fin n, (η x) * (fderiv ℝ (fun y : E n => Φ y i) x) (EuclideanSpace.single i 1) =
      (η x) * divergence Φ x := by
    have h3 : ∑ i : Fin n, (η x) * (fderiv ℝ (fun y : E n => Φ y i) x) (EuclideanSpace.single i 1) =
        (η x) * ∑ i : Fin n, (fderiv ℝ (fun y : E n => Φ y i) x) (EuclideanSpace.single i 1) := by
      simpa [Finset.mul_sum] using rfl
    rw [h3]
    <;> rfl
  have h_sum3 : ∑ i : Fin n, (((Φ x i) • fderiv ℝ η x + (η x) • fderiv ℝ (fun y : E n => Φ y i) x)
        (EuclideanSpace.single i 1)) =
      (∑ i : Fin n, (Φ x i) * (fderiv ℝ η x) (EuclideanSpace.single i 1)) +
      ∑ i : Fin n, (η x) * (fderiv ℝ (fun y : E n => Φ y i) x) (EuclideanSpace.single i 1) := by
    have h4 : ∀ i ∈ Finset.univ,
        (((Φ x i) • fderiv ℝ η x + (η x) • fderiv ℝ (fun y : E n => Φ y i) x)
          (EuclideanSpace.single i 1)) =
        (Φ x i) * (fderiv ℝ η x) (EuclideanSpace.single i 1) +
        (η x) * (fderiv ℝ (fun y : E n => Φ y i) x) (EuclideanSpace.single i 1) := by
      intro i _
      rw [h_add_apply i, h_smul1 i, h_smul2 i]
    rw [Finset.sum_congr rfl h4, Finset.sum_add_distrib]
  have h_main : ∑ i : Fin n, (((Φ x i) • fderiv ℝ η x + (η x) • fderiv ℝ (fun y : E n => Φ y i) x)
        (EuclideanSpace.single i 1)) =
      (fderiv ℝ η x) (Φ x) + η x * divergence Φ x := by
    rw [h_sum3, h_first, h_second] <;> ring
  simpa [divergence, h_target, h_sum] using h_main

/-- `μHE[n-1](S ∩ sphere x₀ t) = 0` for `t ≤ 0`. -/
lemma H_zero_of_nonpos {n : ℕ} [Nonempty (Fin n)] (hn : 2 ≤ n)
    (S : Set (E n)) (x₀ : E n) {t : ℝ} (ht : t ≤ 0) :
    μHE[n - 1] (S ∩ sphere x₀ t) = 0 := by
  by_cases h : t < 0
  · have h1 : sphere x₀ t = ∅ := by
      ext x
      simp only [Set.mem_empty_iff_false, iff_false, Metric.mem_sphere]
      <;> linarith [show 0 ≤ dist x x₀ from dist_nonneg]
    rw [h1] <;> simp
  · have h2 : t = 0 := by linarith
    rw [h2]
    have h3 : sphere x₀ 0 = {x₀} := by
      ext x
      simp [Metric.mem_sphere, dist_eq_zero]
    rw [h3]
    have h4 : (n : ℝ) ≥ 2 := by exact_mod_cast hn
    have h_pos : 0 < ((n : ℝ) - 1) := by linarith
    have hH_singleton : μH[n - 1] ({x₀} : Set (E n)) = 0 := by
      have h_atoms : NoAtoms (μH[n - 1] : Measure (E n)) :=
        MeasureTheory.Measure.noAtoms_hausdorff (E n) (hd := h_pos)
      exact h_atoms.measure_singleton x₀
    have h_dim : ((n : ℝ) - 1) = ↑(n - 1) := by
      have h_n2 : 1 ≤ n := by linarith
      have h : (↑(n - 1) : ℝ) = (n : ℝ) - 1 := by
        rw [Nat.cast_sub (R := ℝ) h_n2] <;> simp
      exact h.symm
    have hH_singleton' : μH[↑(n - 1)] ({x₀} : Set (E n)) = 0 := by
      rw [←h_dim]
      exact hH_singleton
    have h5 : μHE[n - 1] ({x₀} : Set (E n)) = 0 := by
      have h_def : (μHE[n - 1] : Measure (E n)) = _ :=
        MeasureTheory.Measure.euclideanHausdorffMeasure_def (n - 1)
      have h_ac : (μHE[n - 1] : Measure (E n)) ≪ μH[↑(n - 1)] := by
        rw [h_def]
        exact MeasureTheory.Measure.AbsolutelyContinuous.mk fun s _ hnull => by
          rw [Measure.smul_apply, hnull] <;> simp
      exact h_ac hH_singleton'
    have h6 : S ∩ ({x₀} : Set (E n)) ⊆ ({x₀} : Set (E n)) := by
      simp
    exact measure_mono_null h6 h5

/-- One-sided Lebesgue differentiation: for a.e. r,
`(1/L) * ∫_r^{r+L} |h(t) - h(r)| dt → 0` as `L → 0+`. -/
lemma oneSided_lebesgueDifferentiation {h : ℝ → ℝ} (hh : LocallyIntegrable h volume) :
    ∀ᵐ (r : ℝ), Tendsto (fun L : ℝ => (1 / L) * ∫ t in r..(r + L), |h t - h r|)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have h_main : ∀ (q : ℚ), ∀ᵐ (r : ℝ), Tendsto
      (fun L : ℝ => (1 / L) * ∫ t in r..(r + L), |h t - q|)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (|h r - q|)) := by
    intro q
    let f : ℝ → ℝ := fun t => |h t - q|
    have h1 : LocallyIntegrable (fun t : ℝ => h t - q) volume :=
      hh.sub (locallyIntegrable_const (q : ℝ))
    have h_meas : AEStronglyMeasurable f volume :=
      continuous_abs.comp_aestronglyMeasurable h1.aestronglyMeasurable
    have h_bound : ∀ᵐ (t : ℝ) ∂volume, ‖f t‖ ≤ ‖(h t - q)‖ := by
      filter_upwards with t
      simp [f, Real.norm_eq_abs]
    have hf : LocallyIntegrable f volume := h1.mono h_meas h_bound
    have h_ld : ∀ᵐ (r : ℝ), ∀ (c : ℝ), HasDerivAt (fun x => ∫ t in c..x, f t) (f r) r :=
      LocallyIntegrable.ae_hasDerivAt_integral hf
    filter_upwards [h_ld] with r hr
    let F : ℝ → ℝ := fun x => ∫ t in r..x, f t
    have hF_deriv : HasDerivAt F (f r) r := hr r
    have h_tendsto : Tendsto (fun L : ℝ => (F (r + L) - F r) / L)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (f r)) := by
      have h_raw := hF_deriv.tendsto_slope_zero_right
      simpa [div_eq_inv_mul, smul_eq_mul] using h_raw
    have h_eq : ∀ (L : ℝ), (F (r + L) - F r) / L = (1 / L) * ∫ t in r..(r + L), f t := by
      intro L
      have hF_r : F r = 0 := by
        simp [F, intervalIntegral.integral_same]
      have hF_rL : F (r + L) = ∫ t in r..(r + L), f t := by
        simp [F]
      rw [hF_r, hF_rL] <;> ring
    simpa [h_eq] using h_tendsto
  have h_count : ∀ᵐ (r : ℝ), ∀ (q : ℚ), Tendsto
      (fun L : ℝ => (1 / L) * ∫ t in r..(r + L), |h t - q|)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (|h r - q|)) :=
    ae_all_iff.mpr h_main
  filter_upwards [h_count] with r hr
  have h_goal : ∀ (ε : ℝ), 0 < ε → ∀ᶠ (L : ℝ) in nhdsWithin 0 (Set.Ioi 0),
      (1 / L) * ∫ t in r..(r + L), |h t - h r| < ε := by
    intro ε hε
    have hq : ∃ (q : ℚ), |h r - (q : ℝ)| < ε / 3 :=
      exists_rat_near (h r) (by linarith)
    rcases hq with ⟨q, hq⟩
    have h1 : Tendsto (fun L : ℝ => (1 / L) * ∫ t in r..(r + L), |h t - q|)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (|h r - (q : ℝ)|)) := hr q
    have h2 : ∀ᶠ (L : ℝ) in nhdsWithin 0 (Set.Ioi 0),
        (1 / L) * ∫ t in r..(r + L), |h t - q| < |h r - (q : ℝ)| + ε / 3 := by
      have h_nhds : Set.Iio (|h r - (q : ℝ)| + ε / 3) ∈ nhds (|h r - (q : ℝ)|) :=
        Iio_mem_nhds (by linarith)
      exact h1 h_nhds
    have h_self : Set.Ioi (0 : ℝ) ∈ nhdsWithin 0 (Set.Ioi 0) := by exact self_mem_nhdsWithin
    filter_upwards [h2, h_self] with L hL hLpos
    have hLpos' : 0 < L := hLpos
    have h4 : ∀ t ∈ Set.Icc r (r + L), |h t - h r| ≤ |h t - q| + |h r - (q : ℝ)| := by
      intro t _
      calc |h t - h r| = |(h t - q) - (h r - q)| := by ring_nf
        _ ≤ |h t - q| + |h r - q| := by exact abs_sub (h t - ↑q) (h r - ↑q)
    have h_abs1 : LocallyIntegrable (fun t => |h t - h r|) volume := by
      have h_sub : LocallyIntegrable (fun t => h t - h r) volume :=
        hh.sub (locallyIntegrable_const (h r))
      have h_meas : AEStronglyMeasurable (fun t => |h t - h r|) volume :=
        continuous_abs.comp_aestronglyMeasurable h_sub.aestronglyMeasurable
      have h_bound : ∀ᵐ (t : ℝ) ∂volume, ‖(|h t - h r|)‖ ≤ ‖(h t - h r)‖ := by
        filter_upwards with t <;> simp [Real.norm_eq_abs]
      exact h_sub.mono h_meas h_bound
    have h_abs2 : LocallyIntegrable (fun t => |h t - q|) volume := by
      have h_sub : LocallyIntegrable (fun t => h t - q) volume :=
        hh.sub (locallyIntegrable_const (q : ℝ))
      have h_meas : AEStronglyMeasurable (fun t => |h t - q|) volume :=
        continuous_abs.comp_aestronglyMeasurable h_sub.aestronglyMeasurable
      have h_bound : ∀ᵐ (t : ℝ) ∂volume, ‖(|h t - q|)‖ ≤ ‖(h t - q)‖ := by
        filter_upwards with t <;> simp [Real.norm_eq_abs]
      exact h_sub.mono h_meas h_bound
    have h_compact : IsCompact (Set.Icc r (r + L)) := isCompact_Icc
    have h_uIcc : Set.uIcc r (r + L) = Set.Icc r (r + L) := by
      rw [uIcc_of_le (by linarith)]
    have hfi1 : IntervalIntegrable (fun t => |h t - h r|) volume r (r + L) := by
      have h : IntegrableOn (fun t => |h t - h r|) (Set.Icc r (r + L)) volume :=
        h_abs1.integrableOn_isCompact h_compact
      rw [← h_uIcc] at h
      exact h.intervalIntegrable
    have hfi2_abs : IntervalIntegrable (fun t => |h t - q|) volume r (r + L) := by
      have h : IntegrableOn (fun t => |h t - q|) (Set.Icc r (r + L)) volume :=
        h_abs2.integrableOn_isCompact h_compact
      rw [← h_uIcc] at h
      exact h.intervalIntegrable
    have hfi2_const : IntervalIntegrable (fun t => |h r - (q : ℝ)|) volume r (r + L) := by
      have h : IntegrableOn (fun t => |h r - (q : ℝ)|) (Set.Icc r (r + L)) volume :=
        (locallyIntegrable_const (|h r - (q : ℝ)|)).integrableOn_isCompact h_compact
      rw [← h_uIcc] at h
      exact h.intervalIntegrable
    have hfi2 : IntervalIntegrable (fun t => |h t - q| + |h r - (q : ℝ)|) volume r (r + L) :=
      hfi2_abs.add hfi2_const
    have h5 : ∫ t in r..(r + L), |h t - h r| ≤
        ∫ t in r..(r + L), (|h t - q| + |h r - (q : ℝ)|) :=
      intervalIntegral.integral_mono_on (by linarith) hfi1 hfi2 h4
    have h61 : ∫ t in r..(r + L), (|h t - q| + |h r - (q : ℝ)|) =
        (∫ t in r..(r + L), |h t - q|) + ∫ t in r..(r + L), |h r - (q : ℝ)| :=
      intervalIntegral.integral_add hfi2_abs hfi2_const
    have h62 : ∫ t in r..(r + L), |h r - (q : ℝ)| = L * |h r - (q : ℝ)| := by
      have h_const : ∫ t in r..(r + L), |h r - (q : ℝ)| = (r + L - r) • |h r - (q : ℝ)| :=
        intervalIntegral.integral_const (|h r - (q : ℝ)|)
      rw [h_const]
      have h_smul : (r + L - r) • |h r - (q : ℝ)| = (r + L - r) * |h r - (q : ℝ)| := by exact smul_eq_mul (r + L - r) |h r - ↑q|
      rw [h_smul] <;> ring
    have h6 : ∫ t in r..(r + L), (|h t - q| + |h r - (q : ℝ)|) =
        (∫ t in r..(r + L), |h t - q|) + L * |h r - (q : ℝ)| := by
      rw [h61, h62]
    have h5' : ∫ t in r..(r + L), |h t - h r| ≤
        (∫ t in r..(r + L), |h t - q|) + L * |h r - (q : ℝ)| := by
      rw [← h6]; exact h5
    let I := (∫ t in r..(r + L), |h t - q|)
    have h_pos1 : 0 ≤ 1 / L := by positivity
    have h7 : (1 / L) * ∫ t in r..(r + L), |h t - h r| ≤
        (1 / L) * (I + L * |h r - (q : ℝ)|) :=
      mul_le_mul_of_nonneg_left h5' h_pos1
    have h8 : (1 / L) * (I + L * |h r - (q : ℝ)|) =
        (1 / L) * I + |h r - (q : ℝ)| := by
      have hL_ne : L ≠ 0 := hLpos'.ne'
      have h9 : (1 / L) * (I + L * |h r - (q : ℝ)|) =
          (1 / L) * I + (1 / L) * (L * |h r - (q : ℝ)|) := by
        rw [mul_add]
      rw [h9]
      have h10 : (1 / L) * (L * |h r - (q : ℝ)|) = |h r - (q : ℝ)| := by
        have h11 : (1 / L) * L = 1 := by field_simp [hL_ne]
        rw [← mul_assoc, h11, one_mul]
      rw [h10] <;> ring
    rw [h8] at h7
    have h9 : (1 / L) * I + |h r - (q : ℝ)| < ε := by
      have h10 : (1 / L) * I < |h r - (q : ℝ)| + ε / 3 := hL
      have h11 : |h r - (q : ℝ)| < ε / 3 := hq
      linarith
    exact h7.trans_lt h9
  have h_final : Tendsto (fun L : ℝ => (1 / L) * ∫ t in r..(r + L), |h t - h r|)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have h_goal' : ∀ (ε : ℝ), 0 < ε → ∀ᶠ (L : ℝ) in nhdsWithin 0 (Set.Ioi 0),
        dist ((1 / L) * ∫ t in r..(r + L), |h t - h r|) 0 < ε := by
      intro ε hε
      have h_goal2 := h_goal ε hε
      have h_self : Set.Ioi (0 : ℝ) ∈ nhdsWithin 0 (Set.Ioi 0) := by exact self_mem_nhdsWithin
      filter_upwards [h_goal2, h_self] with L hL hLpos
      have hLpos' : 0 < L := hLpos
      let J := (∫ t in r..(r + L), |h t - h r|)
      have h_int_nonneg : 0 ≤ J :=
        intervalIntegral.integral_nonneg_of_forall (by linarith) (fun t => abs_nonneg (h t - h r))
      let A := (1 / L) * J
      have h_pos : 0 ≤ A := mul_nonneg (one_div_nonneg.mpr (le_of_lt hLpos')) h_int_nonneg
      have h_dist : dist A 0 = A := by
        rw [Real.dist_eq, sub_zero, abs_of_nonneg h_pos]
      rwa [h_dist]
    simpa [Metric.tendsto_nhds] using h_goal'
  exact h_final

/-- `H(t) = μHE[n-1](S ∩ sphere x₀ t)` is locally integrable (ENNReal-valued). -/
lemma H_locally_integrable {n : ℕ} [Nonempty (Fin n)] (hn : 2 ≤ n)
    (S : Set (E n)) (hS : MeasurableSet S) (x₀ : E n) :
    ∀ (a b : ℝ), 0 ≤ a → a < b → ∫⁻ t in Set.Ioc a b, μHE[n - 1] (S ∩ sphere x₀ t) ≠ ⊤ := by
  intro a b ha hab
  let d : E n → ℝ := fun x => dist x x₀
  let H : ℝ → ENNReal := fun t => μHE[n - 1] (S ∩ sphere x₀ t)
  let C : Set (E n) := {x₀}
  let A := S ∩ {x | a < d x ∧ d x ≤ b}
  have hA_meas : MeasurableSet A := by
    apply hS.inter
    have hd_meas : Measurable d := by fun_prop
    have h1 : MeasurableSet {x : E n | a < d x} :=
      measurableSet_lt (measurable_const : Measurable (fun _ : E n => a)) hd_meas
    have h2 : MeasurableSet {x : E n | d x ≤ b} :=
      measurableSet_le hd_meas (measurable_const : Measurable (fun _ : E n => b))
    exact h1.inter h2
  have hA_bdd : Bornology.IsBounded A := by
    have h1 : A ⊆ closedBall x₀ b := by
      intro x hx
      have h2 : d x ≤ b := hx.2.2
      simpa [closedBall] using h2
    have h_bdd : Bornology.IsBounded (closedBall x₀ b) := by exact isBounded_closedBall
    exact Bornology.IsBounded.subset h_bdd h1
  have hA_sub : A ⊆ {x | 0 < infDist x C} := by
    intro x hx
    have h1 : a < d x := hx.2.1
    have h2 : 0 < d x := by linarith
    have h3 : infDist x C = d x := by
      simp [C, infDist_singleton, d] <;> rfl
    have h4 : 0 < infDist x C := by rw [h3]; exact h2
    exact h4
  have h_d_meas : FunctionLevelMeasurable (fun x : E n => infDist x C) :=
    functionLevelMeasurable_of_lipschitz hn (Metric.lipschitz_infDist_pt (s := C))
  have h3 : {x ∈ A | a < infDist x C ∧ infDist x C ≤ b} = A := by
    ext x
    simp only [A, Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · rintro ⟨h1, _h2⟩
      exact h1
    · intro h1
      have h4 : infDist x C = d x := by simp [C, infDist_singleton, d] <;> rfl
      have h5 : a < d x ∧ d x ≤ b := h1.2
      have h6 : a < infDist x C ∧ infDist x C ≤ b := by
        rw [h4] <;> exact h5
      exact ⟨h1, h6⟩
  have h_coarea := distance_coarea_eq hn (isClosed_singleton) (singleton_nonempty x₀) h_d_meas hA_meas hA_bdd hA_sub hab
  have h_eq1 : volume A = ∫⁻ s in Set.Ioc a b, μHE[n - 1] {x ∈ A | infDist x C = s} := by
    have h_vol : volume {x ∈ A | a < infDist x C ∧ infDist x C ≤ b} = volume A :=
      congr_arg volume h3
    rw [← h_vol]
    exact h_coarea
  have h4 : ∀ s ∈ Set.Ioc a b, μHE[n - 1] {x ∈ A | infDist x C = s} = H s := by
    intro s hs
    have h5 : a < s ∧ s ≤ b := hs
    have h6 : {x ∈ A | infDist x C = s} = {x ∈ S | infDist x C = s} := by
      ext x
      simp only [A, Set.mem_inter_iff, Set.mem_setOf_eq]
      constructor
      · rintro ⟨h7, h8⟩; exact ⟨h7.1, h8⟩
      · rintro ⟨h7, h8⟩
        have h9 : infDist x C = s := h8
        have h10 : a < infDist x C ∧ infDist x C ≤ b := by
          rw [h9] <;> exact h5
        have h11 : a < d x ∧ d x ≤ b := by
          have h12 : infDist x C = d x := by simp [C, infDist_singleton, d] <;> rfl
          rw [h12] at h10; exact h10
        exact ⟨⟨h7, h11⟩, h8⟩
    rw [h6]
    have h7 : {x ∈ S | infDist x C = s} = S ∩ sphere x₀ s := by
      ext x
      simp [sphere, C, infDist_singleton, d] <;> rfl
    rw [h7] <;> rfl
  have h5 : ∫⁻ s in Set.Ioc a b, μHE[n - 1] {x ∈ A | infDist x C = s} =
      ∫⁻ s in Set.Ioc a b, H s := by
    apply MeasureTheory.setLIntegral_congr_fun measurableSet_Ioc
    intro s hs
    exact h4 s hs
  have h_eq2 : ∫⁻ s in Set.Ioc a b, H s = volume A := by
    rw [← h5, ← h_eq1]
  rw [h_eq2]
  exact hA_bdd.measure_lt_top.ne

/-- Real-valued `h_real(t) = ENNReal.toReal(H(t))` is locally integrable. -/
lemma h_real_locally_integrable {n : ℕ} [Nonempty (Fin n)] (hn : 2 ≤ n)
    (S : Set (E n)) (hS : MeasurableSet S) (x₀ : E n) :
    LocallyIntegrable (fun t : ℝ => ENNReal.toReal (μHE[n - 1] (S ∩ sphere x₀ t))) volume := by
  let H : ℝ → ENNReal := fun t => μHE[n - 1] (S ∩ sphere x₀ t)
  let h_real : ℝ → ℝ := fun t => ENNReal.toReal (H t)
  have hH_local := H_locally_integrable hn S hS x₀
  have hH0 : ∀ t ≤ 0, H t = 0 := fun t ht => H_zero_of_nonpos hn S x₀ ht
  have h_ioc_integrable : ∀ (a b : ℝ), 0 ≤ a → a < b →
      IntegrableOn h_real (Set.Ioc a b) volume := by
    intro a b ha hab
    let B := S ∩ closedBall x₀ b
    have hB_meas : MeasurableSet B := hS.inter isClosed_closedBall.measurableSet
    have hB_sub : B ⊆ closedBall x₀ b := by
      intro x hx
      exact hx.2
    have hB_bdd : Bornology.IsBounded B :=
      (Metric.isBounded_iff_subset_closedBall x₀).mpr ⟨b, hB_sub⟩
    let f : E n → ℝ := fun x => dist x x₀
    have hf : LipschitzWith 1 f := LipschitzWith.dist_left x₀
    let G : ℝ → ENNReal := fun t => μHE[n - 1] (B ∩ f ⁻¹' {t})
    have h_eq : ∀ t ∈ Set.Ioc a b, H t = G t := by
      intro t ht
      have h_t_le_b : t ≤ b := ht.2
      have h_set_eq : S ∩ sphere x₀ t = B ∩ f ⁻¹' {t} := by
        ext x
        simp only [B, Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff,
          Metric.mem_sphere]
        constructor
        · rintro ⟨hS, hdist⟩
          exact ⟨⟨hS, by simpa [Metric.mem_closedBall] using hdist ▸ h_t_le_b⟩, hdist⟩
        · rintro ⟨⟨hS, _⟩, hdist⟩
          exact ⟨hS, hdist⟩
      exact congr_arg (μHE[n - 1]) h_set_eq
    have hG_aeMeas : AEMeasurable G (volume.restrict (Set.Ioc a b)) :=
      levelSetMeasure_aemeasurable hn hf hB_meas hB_bdd hab
    have h_ae : ∀ᵐ t ∂volume.restrict (Set.Ioc a b), H t = G t := by
      filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with t ht
      exact h_eq t ht
    have hH_aeMeas : AEMeasurable H (volume.restrict (Set.Ioc a b)) :=
      AEMeasurable.congr hG_aeMeas (EventuallyEq.symm h_ae)
    have h_lint : ∫⁻ t in Set.Ioc a b, H t ≠ ⊤ := hH_local a b ha hab
    exact integrable_toReal_of_lintegral_ne_top hH_aeMeas h_lint
  have h_zero_on_nonpos : ∀ (a b : ℝ), b ≤ 0 → IntegrableOn h_real (Set.Icc a b) volume := by
    intro a b hb
    have h1 : ∀ t ∈ Set.Icc a b, h_real t = 0 := by
      intro t ht
      have h2 : t ≤ 0 := by linarith [ht.2]
      have h3 : H t = 0 := hH0 t h2
      simp [h_real, h3]
    have h5 : h_real =ᵐ[volume.restrict (Set.Icc a b)] (0 : ℝ → ℝ) := by
      filter_upwards [self_mem_ae_restrict measurableSet_Icc] with t ht
      exact h1 t ht
    have h_zero_int : Integrable (0 : ℝ → ℝ) (volume.restrict (Set.Icc a b)) := by exact integrable_zero ℝ ℝ (volume.restrict (Icc a b))
    exact Integrable.congr h_zero_int h5.symm
  have h_singleton : ∀ (c : ℝ), IntegrableOn h_real {c} volume := by
    intro c
    simp [IntegrableOn]
  have h_extend_Ioc_to_Icc : ∀ (a b : ℝ), 0 ≤ a → a < b →
      IntegrableOn h_real (Set.Icc a b) volume := by
    intro a b ha hab
    have h_ioc : IntegrableOn h_real (Set.Ioc a b) volume := h_ioc_integrable a b ha hab
    have h9 : Set.Icc a b = Set.Ioc a b ∪ {a} := by
      ext x
      simp only [Set.mem_union, Set.mem_Icc, Set.mem_Ioc, Set.mem_singleton_iff]
      constructor
      · rintro ⟨h1, h2⟩
        by_cases h : a = x
        · exact Or.inr h.symm
        · have h' : a < x := by
            by_contra h''
            have : a = x := by linarith
            contradiction
          exact Or.inl ⟨h', h2⟩
      · rintro (h | rfl)
        · exact ⟨by linarith, h.2⟩
        · exact ⟨by linarith, by linarith⟩
    rw [h9]
    exact h_ioc.union (h_singleton a)
  have h_main : ∀ (a b : ℝ), IntegrableOn h_real (Set.Icc a b) volume := by
    intro a b
    by_cases hb : b ≤ 0
    · exact h_zero_on_nonpos a b hb
    · have hb' : 0 < b := by linarith
      by_cases ha : a ≤ 0
      · have h1 : Set.Icc a b = Set.Icc a 0 ∪ Set.Icc 0 b := by
          ext x
          simp only [Set.mem_union, Set.mem_Icc]
          constructor
          · rintro ⟨h1, h2⟩
            by_cases h3 : x ≤ 0
            · exact Or.inl ⟨h1, h3⟩
            · have h4 : 0 < x := by linarith
              exact Or.inr ⟨by linarith, h2⟩
          · rintro (h | h)
            · exact ⟨h.1, by linarith [ha, hb']⟩
            · exact ⟨by linarith [ha, hb'], h.2⟩
        rw [h1]
        have h2 : IntegrableOn h_real (Set.Icc a 0) volume := h_zero_on_nonpos a 0 (by linarith)
        have h3 : IntegrableOn h_real (Set.Icc 0 b) volume := h_extend_Ioc_to_Icc 0 b (by linarith) (by linarith)
        exact h2.union h3
      · have ha' : 0 < a := by linarith
        by_cases h_lt : a < b
        · exact h_extend_Ioc_to_Icc a b (by linarith) h_lt
        · by_cases h_eq : a = b
          · have h_goal : IntegrableOn h_real (Set.Icc a b) volume := by
              subst h_eq
              have h_Icc_singleton : Set.Icc a a = {a} := by
                ext x
                simp [Set.mem_Icc, Set.mem_singleton_iff]
                <;> constructor <;> intro h <;> linarith
              rw [h_Icc_singleton]
              exact h_singleton a
            exact h_goal
          · have h_le : b ≤ a := by linarith
            have h_ne : a ≠ b := h_eq
            have h_gt : b < a := lt_of_le_of_ne h_le h_ne.symm
            have h_empty : Set.Icc a b = ∅ := by
              ext x
              simp only [Set.mem_Icc, Set.mem_empty_iff_false, iff_false]
              intro h
              linarith
            rw [h_empty]
            exact integrableOn_empty
  apply locallyIntegrable_iff.mpr
  intro k hk
  by_cases h_empty : k = ∅
  · rw [h_empty]
    exact integrableOn_empty
  · have h_bdd : Bornology.IsBounded k := hk.isBounded
    rcases (Metric.isBounded_iff_subset_closedBall (0 : ℝ)).mp h_bdd with ⟨C, hC⟩
    have h_sub : k ⊆ Set.Icc (-C) C := by
      intro y hy
      have h_in : y ∈ closedBall (0 : ℝ) C := hC hy
      have h_dist : dist y 0 ≤ C := by simpa [Metric.mem_closedBall] using h_in
      have h_abs : |y| ≤ C := by simpa [Real.dist_eq] using h_dist
      have h_left : -C ≤ y := by linarith [abs_le.mp h_abs]
      have h_right : y ≤ C := by linarith [abs_le.mp h_abs]
      exact ⟨h_left, h_right⟩
    have h_int : IntegrableOn h_real (Set.Icc (-C) C) volume := h_main (-C) C
    exact h_int.mono_set h_sub

/-- Weighted average convergence: if `w ≥ 0`, `∫_0^1 w = 1`, `w` bounded and continuous,
and `h` is locally integrable with one-sided Lebesgue differentiation at `r`, then
`∫_r^{r+L} w((t-r)/L)/L * h(t) dt → h(r)` as `L → 0+`. -/
lemma weighted_average_convergence {h : ℝ → ℝ} (hh : LocallyIntegrable h volume)
    {w : ℝ → ℝ} (hw_nonneg : ∀ t, 0 ≤ w t)
    (hw_int : ∫ t in (0 : ℝ)..1, w t = 1)
    (C_w : ℝ) (hC_w : ∀ t, w t ≤ C_w)
    (hw_cont : Continuous w)
    (r : ℝ) (hr_leb : Tendsto (fun L : ℝ => (1 / L) * ∫ t in r..(r + L), |h t - h r|)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)) :
    Tendsto (fun L : ℝ => ∫ t in r..(r + L), (w ((t - r) / L) / L) * h t)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (h r)) := by
  have h1 : ∀ (L : ℝ), 0 < L → ∫ t in r..(r + L), (w ((t - r) / L) / L) = 1 := by
    intro L hL
    have hc : (1 / L : ℝ) ≠ 0 := by positivity
    have h_subst : ∫ t in r..(r + L), w ((t - r) / L) / L = ∫ s in (0 : ℝ)..1, w s := by
      have h_eq1 : ∫ t in r..(r + L), w ((t - r) / L) / L =
          ∫ t in r..(r + L), w ((1 / L : ℝ) * t + (-r / L)) / L := by
        apply intervalIntegral.integral_congr
        intro t _
        have h : (t - r) / L = (1 / L : ℝ) * t + (-r / L) := by ring
        exact congr_arg (fun x => w x / L) h
      rw [h_eq1]
      have h4 := intervalIntegral.integral_comp_mul_add (a := r) (b := r + L) (c := 1 / L)
          (fun s : ℝ => w s / L) hc (-r / L)
      rw [h4]
      have h_b1 : (1 / L : ℝ) * r + (-r / L) = 0 := by field_simp [hc] <;> ring
      have h_b2 : (1 / L : ℝ) * (r + L) + (-r / L) = 1 := by field_simp [hc] <;> ring
      rw [h_b1, h_b2]
      have h5 : (1 / L : ℝ)⁻¹ = L := by field_simp [hc] <;> ring
      rw [h5]
      have h7 : L * ∫ s in (0 : ℝ)..1, (w s / L) = ∫ s in (0 : ℝ)..1, w s := by
        have h8 : L * ∫ s in (0 : ℝ)..1, (w s / L) = ∫ s in (0 : ℝ)..1, L * (w s / L) := by
          rw [← intervalIntegral.integral_const_mul L (fun s => w s / L)] <;> ring
        rw [h8]
        apply intervalIntegral.integral_congr
        intro s _
        field_simp [hc] <;> ring
      have h_goal : L • ∫ s in (0 : ℝ)..1, (w s / L) = ∫ s in (0 : ℝ)..1, w s := by
        calc
          L • ∫ s in (0 : ℝ)..1, (w s / L)
            = L * ∫ s in (0 : ℝ)..1, (w s / L) := by simp [smul_eq_mul]
          _ = ∫ s in (0 : ℝ)..1, w s := h7
      exact h_goal
    rw [h_subst, hw_int]
  have h_main : ∀ (L : ℝ), 0 < L →
      |(∫ t in r..(r + L), (w ((t - r) / L) / L) * h t) - h r| ≤
      C_w * ((1 / L) * ∫ t in r..(r + L), |h t - h r|) := by
    intro L hL
    set W : ℝ → ℝ := fun t => w ((t - r) / L) / L with hW_def
    have hW_cont : Continuous W := by fun_prop
    have hW_interval : IntervalIntegrable W volume r (r + L) := hW_cont.intervalIntegrable r (r + L)
    have hh_int : IntervalIntegrable h volume r (r + L) := by
      have h_compact : IsCompact (Set.uIcc r (r + L)) := isCompact_uIcc
      have h_integ : IntegrableOn h (Set.uIcc r (r + L)) volume := hh.integrableOn_isCompact h_compact
      exact h_integ.intervalIntegrable
    have h_hr_int : IntervalIntegrable (fun t => W t * h r) volume r (r + L) :=
      hW_interval.mul_const (h r)
    have h_ht_int : IntervalIntegrable (fun t => W t * h t) volume r (r + L) := by
      have hW_on : ContinuousOn W (Set.uIcc r (r + L)) := hW_cont.continuousOn
      exact hh_int.continuousOn_mul hW_on
    have h_diff_int : IntervalIntegrable (fun t => W t * (h t - h r)) volume r (r + L) := by
      have h_sub : IntervalIntegrable (fun t => W t * h t - W t * h r) volume r (r + L) :=
        h_ht_int.sub h_hr_int
      have h_eq : (fun t => W t * h t - W t * h r) = (fun t => W t * (h t - h r)) := by
        funext t; ring
      rw [h_eq] at h_sub
      exact h_sub
    have h_const_int : IntervalIntegrable (fun _ : ℝ => h r) volume r (r + L) :=
      (continuous_const : Continuous (fun _ : ℝ => h r)).intervalIntegrable r (r + L)
    have h_h_diff_int : IntervalIntegrable (fun t => h t - h r) volume r (r + L) :=
      hh_int.sub h_const_int
    have h_abs_h_int : IntervalIntegrable (fun t => |h t - h r|) volume r (r + L) :=
      h_h_diff_int.norm
    have h_abs_int : IntervalIntegrable (fun t => W t * |h t - h r|) volume r (r + L) := by
      have hW_on : ContinuousOn W (Set.uIcc r (r + L)) := hW_cont.continuousOn
      exact h_abs_h_int.continuousOn_mul hW_on
    have h_bound_int : IntervalIntegrable (fun t => (C_w / L) * |h t - h r|) volume r (r + L) :=
      h_abs_h_int.const_mul (C_w / L)
    have hW_int_eq : ∫ t in r..(r + L), W t = 1 := h1 L hL
    let I_ht := ∫ t in r..(r + L), W t * h t
    let I_hr := ∫ t in r..(r + L), W t * h r
    have h51 : I_hr = (∫ t in r..(r + L), W t) * h r := by
      simp only [I_hr]
      rw [intervalIntegral.integral_mul_const (h r) W] <;> ring
    have h_hr_eq : I_hr = h r := by
      rw [h51, hW_int_eq] <;> ring
    have h3 : I_ht - h r = ∫ t in r..(r + L), W t * (h t - h r) := by
      have h52 : I_ht - h r = I_ht - I_hr := by rw [h_hr_eq]
      rw [h52]
      have h53 : I_ht - I_hr = ∫ t in r..(r + L), (W t * h t - W t * h r) := by
        exact (intervalIntegral.integral_sub h_ht_int h_hr_int).symm
      rw [h53]
      apply intervalIntegral.integral_congr
      intro t _
      ring
    rw [h3]
    have h_abs : |∫ t in r..(r + L), W t * (h t - h r)| ≤
        ∫ t in r..(r + L), |W t * (h t - h r)| := by
      exact intervalIntegral.abs_integral_le_integral_abs (by linarith)
    have h_abs2 : ∫ t in r..(r + L), |W t * (h t - h r)| =
        ∫ t in r..(r + L), W t * |h t - h r| := by
      apply intervalIntegral.integral_congr
      intro t _
      have h7 : 0 ≤ W t := by
        have h71 : 0 ≤ w ((t - r) / L) := hw_nonneg _
        exact div_nonneg h71 (by positivity)
      have h8 : |W t * (h t - h r)| = W t * |h t - h r| := by
        rw [abs_mul, abs_of_nonneg h7]
      exact h8
    rw [h_abs2] at h_abs
    have h9 : ∀ t, W t ≤ C_w / L := by
      intro t
      have h10 : w ((t - r) / L) ≤ C_w := hC_w _
      exact div_le_div_of_nonneg_right h10 (by positivity)
    have h_le : ∀ t, W t * |h t - h r| ≤ (C_w / L) * |h t - h r| := by
      intro t
      have h11 : W t ≤ C_w / L := h9 t
      have h12 : 0 ≤ |h t - h r| := abs_nonneg _
      nlinarith
    have h10 : ∫ t in r..(r + L), W t * |h t - h r| ≤
        (C_w / L) * ∫ t in r..(r + L), |h t - h r| := by
      have h_mul : ∫ t in r..(r + L), (C_w / L) * |h t - h r| =
          (C_w / L) * ∫ t in r..(r + L), |h t - h r| := by
        rw [intervalIntegral.integral_const_mul (C_w / L) (fun t => |h t - h r|)] <;> ring
      have h_ab : r ≤ r + L := by linarith
      have h_goal : ∫ t in r..(r + L), W t * |h t - h r| ≤
          ∫ t in r..(r + L), (C_w / L) * |h t - h r| :=
        intervalIntegral.integral_mono h_ab h_abs_int h_bound_int h_le
      rw [h_mul] at h_goal
      exact h_goal
    have h11 : (C_w / L) * ∫ t in r..(r + L), |h t - h r| =
        C_w * ((1 / L) * ∫ t in r..(r + L), |h t - h r|) := by ring
    rw [h11] at h10
    exact h_abs.trans h10
  have h_tendsto : Tendsto (fun L : ℝ => C_w * ((1 / L) * ∫ t in r..(r + L), |h t - h r|))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    simpa [mul_assoc] using hr_leb.const_mul C_w
  let f : ℝ → ℝ := fun L =>
    (∫ t in r..(r + L), (w ((t - r) / L) / L) * h t) - h r
  have h_eventually : ∀ᶠ (L : ℝ) in nhdsWithin 0 (Set.Ioi 0),
      ‖f L‖ ≤ C_w * ((1 / L) * ∫ t in r..(r + L), |h t - h r|) := by
    filter_upwards [self_mem_nhdsWithin] with L hL
    simpa [f, Real.norm_eq_abs] using h_main L hL
  have h_f_tendsto : Tendsto f (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
    squeeze_zero_norm' h_eventually h_tendsto
  have h_final : Tendsto (fun L : ℝ => ∫ t in r..(r + L), (w ((t - r) / L) / L) * h t)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (h r)) := by
    have h_eq : (fun L : ℝ => ∫ t in r..(r + L), (w ((t - r) / L) / L) * h t) =
        fun L => f L + h r := by
      funext L; simp [f]
    rw [h_eq]
    have h_const : Tendsto (fun (_ : ℝ) => h r) (nhdsWithin 0 (Set.Ioi 0)) (nhds (h r)) := tendsto_const_nhds
    have h_result : Tendsto (fun L : ℝ => f L + h r) (nhdsWithin 0 (Set.Ioi 0)) (nhds (h r)) := by
      simpa [add_zero] using h_f_tendsto.add h_const
    exact h_result
  exact h_final

end Geometry.Perimeter
