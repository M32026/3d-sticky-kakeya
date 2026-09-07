module

public import MyLeanRepo.Kakeya.CV.Analysis.Calculus.Sard.CriticalImageBase
public import MyLeanRepo.Kakeya.CV.Analysis.Calculus.Sard.TaylorEstimateGeneral
public import MyLeanRepo.Kakeya.CV.Analysis.Calculus.Sard.LocalCriticalImage
public import MyLeanRepo.Kakeya.CV.Analysis.Calculus.Sard.CoordinateHyperplane
public import MyLeanRepo.Kakeya.CV.Analysis.Calculus.Sard.LocalStraighteningHomeomorph
public import MyLeanRepo.Kakeya.CV.Analysis.Calculus.Sard.CriticalSet
public import MyLeanRepo.Kakeya.CV.Analysis.Calculus.Sard.CriticalLayer
public import MyLeanRepo.Kakeya.CV.Analysis.Calculus.Sard.General.Sard
public import Mathlib.Topology.MetricSpace.HausdorffDimension

@[expose] public section

namespace ForMathlib.Analysis.Calculus.Sard

open MeasureTheory
open scoped ContDiff

lemma volume_image_null_of_continuousLinearEquiv_euclidean_one
    (e : General.E 1 ≃L[ℝ] ℝ) (s : Set (General.E 1))
    (hs : volume s = 0) : (volume : Measure ℝ) (e '' s) = 0 := by
  have h_image : e '' s = e.symm ⁻¹' s := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa using hx
    · intro hy
      exact ⟨e.symm y, hy, e.apply_symm_apply y⟩
  rw [h_image]
  have h_map : (volume : Measure ℝ) (e.symm ⁻¹' s) =
      Measure.map e.symm (volume : Measure ℝ) s := by
    exact (e.symm.toHomeomorph.toMeasurableEquiv.map_apply s).symm
  rw [h_map]
  let μ' : Measure (General.E 1) := Measure.map e.symm (volume : Measure ℝ)
  let μ : Measure (General.E 1) := volume
  letI : μ'.IsAddHaarMeasure := e.symm.isAddHaarMeasure_map volume
  letI : IsFiniteMeasureOnCompacts μ' :=
    isFiniteMeasureOnCompacts_of_isLocallyFiniteMeasure
  have h_eq_smul : μ' = (μ'.addHaarScalarFactor μ : ENNReal) • μ :=
    MeasureTheory.Measure.isAddLeftInvariant_eq_smul μ' μ
  calc
    μ' s = ((μ'.addHaarScalarFactor μ : ENNReal) • μ) s := by
      exact congrArg (fun m : Measure (General.E 1) => m s) h_eq_smul
    _ = (μ'.addHaarScalarFactor μ : ENNReal) * μ s := by
      rfl
    _ = 0 := by
      rw [hs]
      simp

lemma uniform_taylor_estimate_aux (k : ℕ) :
  ∀ {m : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {K : Set (EuclideanSpace ℝ (Fin m))} (_hK : Convex ℝ K) (_hK' : IsCompact K)
    {f : EuclideanSpace ℝ (Fin m) → F} (_hf : ContDiff ℝ (k + 1) f),
    ∃ C : ℝ, ∀ (x : EuclideanSpace ℝ (Fin m)), x ∈ K →
      (∀ j, 1 ≤ j → j ≤ k → iteratedFDeriv ℝ j f x = 0) →
      ∀ (y : EuclideanSpace ℝ (Fin m)), y ∈ K →
        ‖f y - f x‖ ≤ C * ‖y - x‖ ^ (k + 1) := by
  induction k with
  | zero =>
    -- Base case k = 0: Lipschitz constant is uniform
    intro m F _ _ K hK hK' f hf
    have h1 : ContDiff ℝ 1 f := by simpa using hf
    have h1' : ContDiffOn ℝ 1 f K := h1.contDiffOn
    have h_lip : ∃ (C₁ : NNReal), LipschitzOnWith C₁ f K :=
      h1'.exists_lipschitzOnWith (by norm_num) hK hK'
    rcases h_lip with ⟨C₁, hC₁⟩
    have h_dist_le : ∀ (x : _), x ∈ K → ∀ (y : _), y ∈ K → ‖f y - f x‖ ≤ (C₁ : ℝ) * ‖y - x‖ := by
      intro x hx y hy
      have h4 : dist (f y) (f x) ≤ (C₁ : ℝ) * dist y x :=
        (lipschitzOnWith_iff_dist_le_mul.mp hC₁) y hy x hx
      have h6 : ‖f y - f x‖ = dist (f y) (f x) := by rw [dist_eq_norm]
      have h7 : ‖y - x‖ = dist y x := by rw [dist_eq_norm]
      rw [h6, h7]
      simpa [pow_one] using h4
    have h_final : ∀ (x : _), x ∈ K → (∀ j, 1 ≤ j → j ≤ 0 → iteratedFDeriv ℝ j f x = 0) →
        ∀ (y : _), y ∈ K → ‖f y - f x‖ ≤ (C₁ : ℝ) * ‖y - x‖ ^ (0 + 1) := by
      intro x hx _ y hy
      have h : ‖f y - f x‖ ≤ (C₁ : ℝ) * ‖y - x‖ := h_dist_le x hx y hy
      have h_pow : ‖y - x‖ ^ (0 + 1) = ‖y - x‖ := by simp
      rw [h_pow]
      exact h
    exact ⟨(C₁ : ℝ), h_final⟩
  | succ k ih =>
    -- Inductive step
    intro m F _ _ K hK hK' f hf
    let g : EuclideanSpace ℝ (Fin m) → (EuclideanSpace ℝ (Fin m) →L[ℝ] F) := fderiv ℝ f
    have h1 : ContDiff ℝ (k + 1) g := by
      have h11 : ContDiff ℝ ((k + 1) + 1) f := by simpa using hf
      have h12 := (contDiff_succ_iff_fderiv.mp h11)
      exact h12.2.2
    rcases @ih m (EuclideanSpace ℝ (Fin m) →L[ℝ] F) _ _ K hK hK' g h1 with ⟨C₁, hC₁⟩
    let C₁' : ℝ := max C₁ 0
    have hC₁'_nonneg : 0 ≤ C₁' := by
      simp [C₁']
    have h_diff : Differentiable ℝ f := by
      have h : ContDiff ℝ 1 f := hf.of_le (by simp)
      exact h.differentiable (by simp)
    refine ⟨C₁', fun x hx hderiv y hy => ?_⟩
    have hderiv' : ∀ j, 1 ≤ j → j ≤ k → iteratedFDeriv ℝ j g x = 0 := by
      intro j hj1 hj2
      have h10 : 1 ≤ j + 1 := by linarith
      have h11 : j + 1 ≤ k + 1 := by linarith
      have h12 : iteratedFDeriv ℝ (j + 1) f x = 0 := hderiv (j + 1) h10 h11
      have h9 : iteratedFDeriv ℝ (j + 1) f x =
          (continuousMultilinearCurryRightEquiv' ℝ j (EuclideanSpace ℝ (Fin m)) F).symm
            (iteratedFDeriv ℝ j g x) := by
        exact iteratedFDeriv_succ_eq_comp_right (f := f) (n := j)
      have h13 : (continuousMultilinearCurryRightEquiv' ℝ j (EuclideanSpace ℝ (Fin m)) F).symm
          (iteratedFDeriv ℝ j g x) = 0 := by
        rw [←h9, h12]
      have h14 : iteratedFDeriv ℝ j g x = 0 := by
        exact (continuousMultilinearCurryRightEquiv' ℝ j (EuclideanSpace ℝ (Fin m)) F).symm.injective h13
      exact h14
    have h_gx_zero : g x = 0 := by
      have h7 : iteratedFDeriv ℝ 1 f x = 0 := hderiv 1 (by norm_num) (by norm_num)
      have h_norm : ‖iteratedFDeriv ℝ 1 f x‖ = ‖g x‖ := by
        exact norm_iteratedFDeriv_one f
      have h8 : ‖iteratedFDeriv ℝ 1 f x‖ = 0 := by
        rw [h7]
        simp
      have h9 : ‖g x‖ = 0 := by linarith [h_norm]
      exact norm_eq_zero.mp h9
    let S := segment ℝ x y
    have hS_sub : S ⊆ K := hK.segment_subset hx hy
    have h4 : ∀ z ∈ S, ‖g z‖ ≤ C₁' * ‖z - x‖ ^ (k + 1) := by
      intro z hz
      have hzK : z ∈ K := hS_sub hz
      have h5 : ‖g z - g x‖ ≤ C₁ * ‖z - x‖ ^ (k + 1) := hC₁ x hx hderiv' z hzK
      have h6 : C₁ * ‖z - x‖ ^ (k + 1) ≤ C₁' * ‖z - x‖ ^ (k + 1) := by
        gcongr
        exact le_max_left C₁ 0
      have h7 : ‖g z - g x‖ ≤ C₁' * ‖z - x‖ ^ (k + 1) := le_trans h5 h6
      rw [h_gx_zero, sub_zero] at h7
      exact h7
    have h4' : ∀ z ∈ S, ‖g z‖ ≤ C₁' * ‖y - x‖ ^ (k + 1) := by
      intro z hz
      have h5 : ‖z - x‖ ≤ ‖y - x‖ := norm_sub_le_of_mem_segment hz
      have h6 : ‖g z‖ ≤ C₁' * ‖z - x‖ ^ (k + 1) := h4 z hz
      calc
        ‖g z‖ ≤ C₁' * ‖z - x‖ ^ (k + 1) := h6
        _ ≤ C₁' * ‖y - x‖ ^ (k + 1) := by
          gcongr
    have h_main : ‖f y - f x‖ ≤ C₁' * ‖y - x‖ ^ (k + 1) * ‖y - x‖ := by
      have h_conv : Convex ℝ S := convex_segment _ _
      exact h_conv.norm_image_sub_le_of_norm_fderiv_le
        (fun z _ => h_diff.differentiableAt) h4' (by exact left_mem_segment ℝ x y) (by exact right_mem_segment ℝ x y)
    have h_final : ‖f y - f x‖ ≤ C₁' * ‖y - x‖ ^ (k + 2) := by
      have h10 : C₁' * ‖y - x‖ ^ (k + 1) * ‖y - x‖ = C₁' * ‖y - x‖ ^ (k + 2) := by
        simp [pow_succ]
        ring
      rw [h10] at h_main
      exact h_main
    simpa using h_final

/-- Uniform Taylor estimate: there exists a constant `C` depending only on `K` such that
for all `x ∈ K` with `hderiv(x)` and `y ∈ K`, we have `‖f y - f x‖ ≤ C * ‖y - x‖^(k+1)`. -/
lemma uniform_taylor_estimate {k m : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {K : Set (EuclideanSpace ℝ (Fin m))} (hK : Convex ℝ K) (hK' : IsCompact K)
    {f : EuclideanSpace ℝ (Fin m) → F} (hf : ContDiff ℝ (k + 1) f) :
    ∃ C : ℝ, ∀ (x : EuclideanSpace ℝ (Fin m)), x ∈ K →
      (∀ j, 1 ≤ j → j ≤ k → iteratedFDeriv ℝ j f x = 0) →
      ∀ (y : EuclideanSpace ℝ (Fin m)), y ∈ K →
        ‖f y - f x‖ ≤ C * ‖y - x‖ ^ (k + 1) :=
  uniform_taylor_estimate_aux k hK hK' hf

/-- Sub-lemma B: For `k = m+2`, the image of `C k` has measure zero, where `C k` is the set
where all iterated derivatives of order `≤ k` vanish. -/
lemma sub_lemma_B {m : ℕ}
    (f : EuclideanSpace ℝ (Fin (m + 1)) → ℝ) (hf : ContDiff ℝ ∞ f) :
    (volume : Measure ℝ) (f '' C f (m + 2)) = 0 := by
  have h_main : ∀ (n : ℕ), (volume : Measure ℝ) (f '' (C f (m + 2) ∩ Metric.closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) n)) = 0 := by
    intro n
    let K := Metric.closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) n
    have hK_convex : Convex ℝ K := convex_closedBall 0 (n : ℝ)
    have hK_compact : IsCompact K := isCompact_closedBall 0 (n : ℝ)
    have h_top : (m + 3 : ℕ∞ω) ≤ (∞ : ℕ∞ω) := by
      have h : ∀ (n : ℕ), (n : ℕ∞ω) ≤ (∞ : ℕ∞ω) := by
        intro n
        exact WithTop.coe_le_coe.mpr (le_top : (n : ℕ∞) ≤ (⊤ : ℕ∞))
      exact h (m + 3)
    have h1 : ContDiff ℝ (m + 3) f := hf.of_le h_top
    rcases uniform_taylor_estimate hK_convex hK_compact h1 with ⟨Ct, hCt⟩
    let S := C f (m + 2) ∩ K
    have h_holder : ∀ (x : EuclideanSpace ℝ (Fin (m + 1))), x ∈ S →
        ∀ (y : EuclideanSpace ℝ (Fin (m + 1))), y ∈ S →
          dist (f y) (f x) ≤ Ct * dist y x ^ (m + 3) := by
      intro x hx y hy
      have h_x1 : x ∈ K := hx.2
      have h_x2 : ∀ j, 1 ≤ j → j ≤ m + 2 → iteratedFDeriv ℝ j f x = 0 := hx.1
      have h_y1 : y ∈ K := hy.2
      have h : |f y - f x| ≤ Ct * ‖y - x‖ ^ (m + 3) := by
        have h' : ‖f y - f x‖ ≤ Ct * ‖y - x‖ ^ (m + 3) := hCt x h_x1 h_x2 y h_y1
        simpa using h'
      have h_dist : dist (f y) (f x) = |f y - f x| := by
        rw [Real.dist_eq]
      have h_dist2 : dist y x = ‖y - x‖ := by
        rw [dist_eq_norm]
      rw [h_dist, h_dist2]
      exact h
    have hr_pos : 0 ≤ (m + 3 : ℝ) := by positivity
    let r : NNReal := ⟨(m + 3 : ℝ), hr_pos⟩
    have hCt_max_nonneg : 0 ≤ max Ct 0 := by exact le_max_right Ct 0
    let Ct_nnreal : NNReal := ⟨max Ct 0, hCt_max_nonneg⟩
    have hCt_max : Ct ≤ (Ct_nnreal : ℝ) := by
      have h_eq : (Ct_nnreal : ℝ) = max Ct 0 := by
        simp [Ct_nnreal]
        rfl
      rw [h_eq]
      exact le_max_left Ct 0
    have h_holder2 : HolderOnWith Ct_nnreal r f S := by
      intro x hx y hy
      have h1 : dist (f y) (f x) ≤ Ct * dist y x ^ (m + 3) := h_holder x hx y hy
      have h2 : Ct * dist y x ^ (m + 3) ≤ (Ct_nnreal : ℝ) * dist y x ^ (m + 3) := by
        gcongr
      have h3 : dist (f y) (f x) ≤ (Ct_nnreal : ℝ) * dist y x ^ (m + 3) := le_trans h1 h2
      have h4 : edist (f x) (f y) = ENNReal.ofReal (dist (f x) (f y)) := by
        rw [edist_dist]
      have h5 : edist x y = ENNReal.ofReal (dist x y) := by
        rw [edist_dist]
      rw [h4, h5]
      have h_dist_comm : dist (f x) (f y) = dist (f y) (f x) := dist_comm _ _
      have h_dist_comm2 : dist x y = dist y x := dist_comm _ _
      rw [h_dist_comm, h_dist_comm2]
      have h_nonneg1 : 0 ≤ dist y x := dist_nonneg
      have h_nonneg2 : 0 ≤ (Ct_nnreal : ℝ) := Ct_nnreal.coe_nonneg
      have h9 : ENNReal.ofReal (dist (f y) (f x)) ≤ ENNReal.ofReal ((Ct_nnreal : ℝ) * dist y x ^ (m + 3)) :=
        ENNReal.ofReal_le_ofReal h3
      have h10 : ENNReal.ofReal ((Ct_nnreal : ℝ) * dist y x ^ (m + 3)) =
          (Ct_nnreal : ENNReal) * (ENNReal.ofReal (dist y x)) ^ (r : ℝ) := by
        have h11 : ENNReal.ofReal ((Ct_nnreal : ℝ) * dist y x ^ (m + 3)) =
            ENNReal.ofReal (Ct_nnreal : ℝ) * ENNReal.ofReal (dist y x ^ (m + 3)) := by
          rw [ENNReal.ofReal_mul h_nonneg2]
        have h12 : ENNReal.ofReal (dist y x ^ (m + 3)) = (ENNReal.ofReal (dist y x)) ^ (r : ℝ) := by
          have hr_eq : (r : ℝ) = (m + 3 : ℝ) := by
            simp [r]
            norm_cast
          rw [ENNReal.ofReal_pow h_nonneg1, hr_eq]
          norm_cast
        have h13 : ENNReal.ofReal (Ct_nnreal : ℝ) = (Ct_nnreal : ENNReal) := by
          exact ENNReal.ofReal_coe_nnreal
        rw [h11, h12, h13]
      calc
        ENNReal.ofReal (dist (f y) (f x))
          ≤ ENNReal.ofReal ((Ct_nnreal : ℝ) * dist y x ^ (m + 3)) := h9
        _ = (Ct_nnreal : ENNReal) * (ENNReal.ofReal (dist y x)) ^ (r : ℝ) := h10
    have hr_pos' : (0 : ℝ) < (r : ℝ) := by
      have h9 : (r : ℝ) = (m + 3 : ℝ) := by
        simp [r]
        norm_cast
      rw [h9]
      have h10 : 0 ≤ (m : ℝ) := by positivity
      linarith
    have hd : 0 ≤ (1 : ℝ) := by norm_num
    have h4 : MeasureTheory.Measure.hausdorffMeasure 1 (f '' S) ≤
        (Ct_nnreal : ENNReal) ^ (1 : ℝ) * MeasureTheory.Measure.hausdorffMeasure ((r : ℝ) * (1 : ℝ)) S :=
      h_holder2.hausdorffMeasure_image_le hr_pos' hd
    have h5 : Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + 1))) = m + 1 := by simp
    have h6 : (↑(Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + 1)))) : ℝ) < (r : ℝ) * (1 : ℝ) := by
      have h9 : (r : ℝ) = (m + 3 : ℝ) := by
        simp [r]
        norm_cast
      rw [h5, h9]
      have h10 : 0 ≤ (m : ℝ) := by positivity
      simp
    have h71 : MeasureTheory.Measure.hausdorffMeasure ((r : ℝ) * (1 : ℝ)) = 0 :=
      Real.hausdorffMeasure_of_finrank_lt h6
    have h7 : MeasureTheory.Measure.hausdorffMeasure ((r : ℝ) * (1 : ℝ)) (S : Set (EuclideanSpace ℝ (Fin (m + 1)))) = 0 := by
      rw [h71]
      simp
    have h_haus : MeasureTheory.Measure.hausdorffMeasure 1 (f '' S) = 0 := by
      rw [h7] at h4
      simpa using h4
    have h_eq : (volume : Measure ℝ) = MeasureTheory.Measure.hausdorffMeasure 1 := by
      exact Eq.symm hausdorffMeasure_real
    have h_final : (volume : Measure ℝ) (f '' S) = 0 := by
      rw [h_eq]
      exact h_haus
    exact h_final
  have h_cover : C f (m + 2) = ⋃ n : ℕ, (C f (m + 2) ∩ Metric.closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) n) := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · intro hx
      have h : ∃ (n : ℕ), ‖x‖ ≤ (n : ℝ) := by
        exact ⟨Nat.ceil ‖x‖, by exact Nat.le_ceil ‖x‖⟩
      rcases h with ⟨n, hn⟩
      exact ⟨n, hx, by simpa [Metric.mem_closedBall] using hn⟩
    · rintro ⟨n, hx, _⟩
      exact hx
  have h_image_union : f '' C f (m + 2) = ⋃ k : ℕ, f '' (C f (m + 2) ∩ Metric.closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) k) := by
    have h1 : f '' C f (m + 2) = f '' (⋃ k : ℕ, C f (m + 2) ∩ Metric.closedBall (0 : _) k) := by
      congr
    rw [h1]
    rw [Set.image_iUnion]
  have h_goal : (volume : Measure ℝ) (f '' C f (m + 2)) = 0 := by
    rw [h_image_union]
    have h9 : ∀ k : ℕ, (volume : Measure ℝ) (f '' (C f (m + 2) ∩ Metric.closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) k)) = 0 := by
      intro k
      exact h_main k
    exact MeasureTheory.measure_iUnion_null h9
  exact h_goal

/-- The image of the critical set has measure zero: `volume (f '' {x | fderiv ℝ f x = 0}) = 0`.
Proven by induction on the dimension m. -/
theorem critical_image_null {m : ℕ} (f : EuclideanSpace ℝ (Fin m) → ℝ)
    (hf : ContDiff ℝ ∞ f) :
    (volume : Measure ℝ) (f '' {x | fderiv ℝ f x = 0}) = 0 := by
  induction m with
  | zero =>
    exact critical_image_null_m0 f hf
  | succ m ih =>
    -- We have the base case m=1 already proved
    by_cases h : m = 0
    · -- m+1 = 1, use the base case
      subst h
      exact critical_image_null_m1 f hf
    · -- Inductive step for m ≥ 1
      -- The critical set is the union of:
      --   C_1 \ C_2, C_2 \ C_3, ..., C_{m+1} \ C_{m+2}, C_{m+2}
      -- Each of these has measure zero image by Sub-lemmas A and B
      -- So the union has measure zero
      have h_critical_eq_C1 : {x : EuclideanSpace ℝ (Fin (m + 1)) | fderiv ℝ f x = 0} = C f 1 := by
        ext x
        simp only [C, Set.mem_setOf_eq]
        constructor
        · intro hx j hj1 hj2
          have h_j_eq_one : j = 1 := by omega
          rw [h_j_eq_one]
          have h_norm : ‖iteratedFDeriv ℝ 1 f x‖ = ‖fderiv ℝ f x‖ := norm_iteratedFDeriv_one f
          have h : ‖fderiv ℝ f x‖ = 0 := by
            rw [hx]
            simp
          have h' : ‖iteratedFDeriv ℝ 1 f x‖ = 0 := by rw [h_norm, h]
          exact norm_eq_zero.mp h'
        · intro hx
          have h1 : iteratedFDeriv ℝ 1 f x = 0 := hx 1 (by norm_num) (by norm_num)
          have h_norm : ‖iteratedFDeriv ℝ 1 f x‖ = ‖fderiv ℝ f x‖ := norm_iteratedFDeriv_one f
          have h2 : ‖iteratedFDeriv ℝ 1 f x‖ = 0 := by
            rw [h1]
            simp
          have h3 : ‖fderiv ℝ f x‖ = 0 := by
            rw [←h_norm, h2]
          exact norm_eq_zero.mp h3
      rw [h_critical_eq_C1]
      classical
      have h_union : C f 1 ⊆ (⋃ k ∈ Finset.Icc 1 (m + 1), C f k \ C f (k + 1)) ∪ C f (m + 2) := by
        intro x hx
        by_cases h : x ∈ C f (m + 2)
        · exact Or.inr h
        · have h' : x ∉ C f (m + 2) := h
          have h2 : ∃ (j : ℕ), j ≤ m + 1 ∧ ¬(x ∈ C f (j + 1)) := ⟨m + 1, by norm_num, h'⟩
          let k : ℕ := Nat.find h2
          have hk_spec : k ≤ m + 1 ∧ ¬(x ∈ C f (k + 1)) := Nat.find_spec h2
          have hk1 : k ≤ m + 1 := hk_spec.1
          have hk2 : ¬(x ∈ C f (k + 1)) := hk_spec.2
          have hk3 : k ≥ 1 := by
            by_contra h4
            have h5 : k = 0 := by omega
            rw [h5] at hk2
            have h6 : ¬(x ∈ C f 1) := hk2
            exact h6 hx
          have hk4 : x ∈ C f k := by
            by_cases h7 : k = 0
            · omega
            · have h8 : k - 1 < k := by omega
              have h9 : ¬((k - 1) ≤ m + 1 ∧ ¬(x ∈ C f ((k - 1) + 1))) := Nat.find_min h2 h8
              have h10 : k - 1 ≤ m + 1 := by omega
              have h11 : x ∈ C f ((k - 1) + 1) := by tauto
              have h12 : (k - 1) + 1 = k := by omega
              rw [h12] at h11
              exact h11
          have h_k_in : k ∈ Finset.Icc 1 (m + 1) := Finset.mem_Icc.mpr ⟨hk3, hk1⟩
          have h_xk : x ∈ C f k \ C f (k + 1) := ⟨hk4, hk2⟩
          exact Or.inl (Set.mem_iUnion₂.mpr ⟨k, h_k_in, h_xk⟩)
      have h_image_subset : f '' C f 1 ⊆ (⋃ k ∈ Finset.Icc 1 (m + 1), f '' (C f k \ C f (k + 1))) ∪ f '' C f (m + 2) := by
        intro y hy
        rcases hy with ⟨x, hx, rfl⟩
        have h_x_in : x ∈ (⋃ k ∈ Finset.Icc 1 (m + 1), C f k \ C f (k + 1)) ∪ C f (m + 2) := h_union hx
        cases h_x_in with
        | inl h_x_in1 =>
          rcases Set.mem_iUnion₂.mp h_x_in1 with ⟨k, hk, hxk⟩
          exact Or.inl (Set.mem_iUnion₂.mpr ⟨k, hk, ⟨x, hxk, rfl⟩⟩)
        | inr h_x_in2 =>
          exact Or.inr ⟨x, h_x_in2, rfl⟩
      have h1 : ∀ k ∈ Finset.Icc 1 (m + 1), (volume : Measure ℝ) (f '' (C f k \ C f (k + 1))) = 0 := by
        intro k hk
        have hk_pos : 1 ≤ k := (Finset.mem_Icc.mp hk).1
        exact sub_lemma_A k hk_pos f hf ih
      have h_count : (Finset.Icc 1 (m + 1) : Set ℕ).Countable := Set.Finite.countable (Finset.finite_toSet _)
      have h2 : (volume : Measure ℝ) (⋃ k ∈ Finset.Icc 1 (m + 1), f '' (C f k \ C f (k + 1))) = 0 := by
        have h_iff : (volume : Measure ℝ) (⋃ k ∈ Finset.Icc 1 (m + 1), f '' (C f k \ C f (k + 1))) = 0 ↔
            ∀ k ∈ Finset.Icc 1 (m + 1), (volume : Measure ℝ) (f '' (C f k \ C f (k + 1))) = 0 :=
          MeasureTheory.measure_biUnion_null_iff h_count
        exact h_iff.mpr h1
      have h3 : (volume : Measure ℝ) (f '' C f (m + 2)) = 0 := sub_lemma_B f hf
      have h4 : (volume : Measure ℝ) ((⋃ k ∈ Finset.Icc 1 (m + 1), f '' (C f k \ C f (k + 1))) ∪ f '' C f (m + 2)) = 0 := by
        exact MeasureTheory.measure_union_null h2 h3
      exact measure_mono_null h_image_subset h4

/-- Sard's theorem for scalar-valued maps: the critical values of a smooth
`f : ℝᵐ → ℝ` have Lebesgue measure zero. -/
theorem sard_criticalValues_null {m : ℕ} (f : EuclideanSpace ℝ (Fin m) → ℝ)
    (hf : ContDiff ℝ ∞ f) :
    (volume : Measure ℝ) (criticalValues f) = 0 := by
  by_cases hm0 : m = 0
  · subst m
    simpa [criticalValues] using critical_image_null_m0 f hf
  · have hm_pos : 0 < m := Nat.pos_of_ne_zero hm0
    let e : General.E 1 ≃L[ℝ] ℝ :=
      (EuclideanSpace.equiv (Fin 1) ℝ).trans
        (ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ)
    let g : General.E m → General.E 1 := fun x => e.symm (f x)
    have hg : ContDiff ℝ ∞ g := e.symm.contDiff.comp hf
    have h_general : volume (General.criticalValues g) = 0 :=
      General.criticalValues_null g hg
    have h_image_null : (volume : Measure ℝ) (e '' General.criticalValues g) = 0 :=
      volume_image_null_of_continuousLinearEquiv_euclidean_one e (General.criticalValues g) h_general
    have h_subset : criticalValues f ⊆ e '' General.criticalValues g := by
      rintro y ⟨x, hx, rfl⟩
      have h_diff_at : DifferentiableAt ℝ f x := (hf.differentiable (by simp)) x
      have h_hasDeriv_g : HasFDerivAt g ((e.symm : ℝ →L[ℝ] General.E 1).comp (fderiv ℝ f x)) x := by
        exact e.symm.hasFDerivAt.comp x h_diff_at.hasFDerivAt
      have h_fderiv_g : fderiv ℝ g x =
          (e.symm : ℝ →L[ℝ] General.E 1).comp (fderiv ℝ f x) :=
        h_hasDeriv_g.fderiv
      have h_fderiv_zero : fderiv ℝ g x = 0 := by
        rw [h_fderiv_g, hx]
        ext v
        simp
      have h_rank_zero : General.fderivRank g x = 0 := by
        simp [General.fderivRank, h_fderiv_zero]
      have hxcrit : General.IsCriticalPoint g x := by
        rw [General.IsCriticalPoint, h_rank_zero]
        exact ⟨hm_pos, by norm_num⟩
      refine ⟨g x, ⟨x, hxcrit, rfl⟩, ?_⟩
      simp [g, e]
    exact measure_mono_null h_subset h_image_null


end ForMathlib.Analysis.Calculus.Sard
