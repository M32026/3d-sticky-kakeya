import MyLeanRepo.Kakeya.CV.Isoperimetric.Coarea.GraphArea
import MyLeanRepo.Kakeya.CV.Isoperimetric.Coarea.GraphAreaBiLipschitz
import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.Tactic

/-!
# Graph Area Formula — Smooth Case

For a C¹ function `g : EuclideanSpace ℝ (Fin m) → ℝ` and measurable `A`:

  `μHE[m](graph(g) ∩ cylinder(A)) = ∫⁻ x in A, ENNReal.ofReal (√(1 + ‖fderiv ℝ g x‖²))`

Proof via Radon-Nikodym differentiation:
1. Define μ(S) := μHE[m](graph(g) ∩ cylinder(S))
2. μ ≪ volume (graph map is locally Lipschitz)
3. dμ/dvol(x) = √(1 + ‖fderiv g x‖²) a.e. (affine tangent approximation + Besicovitch)
4. RN theorem gives μ(A) = ∫_A dμ/dvol
-/

open MeasureTheory Metric Set ENNReal LinearMap Filter
open scoped MeasureTheory

namespace GraphAreaFormula

variable {m : ℕ} [Nonempty (Fin m)]

-- ============================================================================
-- Wrapper: Lipschitz image bound for μHE
-- ============================================================================

/-- Lipschitz image bound for Euclidean Hausdorff measure. -/
lemma lipschitzOnWith_euclideanHausdorffMeasure_image_le
    {X Y : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [EMetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    {K : NNReal} {f : X → Y} {s : Set X} {d : ℕ}
    (h : LipschitzOnWith K f s) :
    μHE[d] (f '' s) ≤ (K : ENNReal) ^ (d : ℝ) * μHE[d] s := by
  have h1 : μH[d] (f '' s) ≤ (K : ENNReal) ^ (d : ℝ) * μH[d] s :=
    h.hausdorffMeasure_image_le (by positivity)
  have h2 : ∀ (c : ENNReal), c * μH[d] (f '' s) ≤ (K : ENNReal) ^ (d : ℝ) * (c * μH[d] s) := by
    intro c
    have h3 : c * μH[d] (f '' s) ≤ c * ((K : ENNReal) ^ (d : ℝ) * μH[d] s) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have h4 : c * ((K : ENNReal) ^ (d : ℝ) * μH[d] s) = (K : ENNReal) ^ (d : ℝ) * (c * μH[d] s) := by ring
    exact le_trans h3 (le_of_eq h4)
  simpa [MeasureTheory.Measure.euclideanHausdorffMeasure_def, Measure.smul_apply] using h2 _

-- ============================================================================
-- Graph map Lipschitz property
-- ============================================================================

/-- If g is K-Lipschitz on S, then graphMap is √(1+K²)-Lipschitz on S. -/
lemma graphMap_lipschitzOnWith
    {g : EuclideanSpace ℝ (Fin m) → ℝ} {K : NNReal}
    {S : Set (EuclideanSpace ℝ (Fin m))}
    (h : LipschitzOnWith K g S) :
    LipschitzOnWith ⟨Real.sqrt (1 + (K : ℝ) ^ 2), by positivity⟩ (graphMap g) S := by
  let K' : NNReal := ⟨Real.sqrt (1 + (K : ℝ) ^ 2), by positivity⟩
  have hK'_val : (K' : ℝ) = Real.sqrt (1 + (K : ℝ) ^ 2) := by rfl
  rw [lipschitzOnWith_iff_dist_le_mul] at h ⊢
  intro x hx y hy
  have h1 : |g x - g y| ≤ (K : ℝ) * ‖x - y‖ := by
    simpa [dist_eq_norm] using h x hx y hy
  have h2 : (g x - g y) ^ 2 ≤ ((K : ℝ) * ‖x - y‖) ^ 2 := by
    have h21 : |g x - g y| ≤ (K : ℝ) * ‖x - y‖ := h1
    have h22 : 0 ≤ (K : ℝ) * ‖x - y‖ := by positivity
    calc
      (g x - g y) ^ 2 = |g x - g y| ^ 2 := by rw [sq_abs]
      _ ≤ ((K : ℝ) * ‖x - y‖) ^ 2 := by gcongr
  have h3 : ‖graphMap g x - graphMap g y‖ ^ 2 ≤
      (1 + (K : ℝ) ^ 2) * ‖x - y‖ ^ 2 := by
    rw [graphMap_norm_sq] <;> linarith
  have h51 : ((K' : ℝ) * ‖x - y‖) ^ 2 = (1 + (K : ℝ) ^ 2) * ‖x - y‖ ^ 2 := by
    have h52 : (K' : ℝ) ^ 2 = 1 + (K : ℝ) ^ 2 := by
      rw [hK'_val]
      exact Real.sq_sqrt (by positivity)
    rw [mul_pow, h52] <;> ring
  have h_pos1 : 0 ≤ ‖graphMap g x - graphMap g y‖ := by positivity
  have h_pos2 : 0 ≤ (K' : ℝ) * ‖x - y‖ := by positivity
  have h5 : ‖graphMap g x - graphMap g y‖ ≤ (K' : ℝ) * ‖x - y‖ := by
    nlinarith [h3, h51]
  have h6 : dist (graphMap g x) (graphMap g y) ≤ (K' : ℝ) * dist x y := by
    simpa [dist_eq_norm] using h5
  exact h6

-- ============================================================================
-- C¹ implies Lipschitz on bounded convex sets
-- ============================================================================

/-- A C¹ function is Lipschitz on every bounded convex set. -/
lemma contDiff_lipschitzOn_bounded
    {g : EuclideanSpace ℝ (Fin m) → ℝ}
    (hg : ContDiff ℝ 1 g)
    {A : Set (EuclideanSpace ℝ (Fin m))}
    (hA_conv : Convex ℝ A) (hA_bdd : Bornology.IsBounded A) :
    ∃ (K : NNReal), LipschitzOnWith K g A := by
  by_cases hA_empty : A = ∅
  · refine ⟨0, ?_⟩
    rw [lipschitzOnWith_iff_dist_le_mul]
    intro x hx
    rw [hA_empty] at hx
    simp at hx
  · have hA_nonempty : A.Nonempty := Set.nonempty_iff_ne_empty.mpr hA_empty
    have h_closure_conv : Convex ℝ (closure A) := hA_conv.closure
    have h1 : IsCompact (closure A) := hA_bdd.isCompact_closure
    have h_diff : Differentiable ℝ g := hg.differentiable (by norm_num)
    have h_cont_deriv : Continuous (fun x => ‖fderiv ℝ g x‖) :=
      (hg.continuous_fderiv (by norm_num)).norm
    have h2 : BddAbove (Set.image (fun x => ‖fderiv ℝ g x‖) (closure A)) :=
      h1.bddAbove_image h_cont_deriv.continuousOn
    rcases h2 with ⟨C, hC⟩
    have hC' : ∀ x ∈ closure A, ‖fderiv ℝ g x‖ ≤ C := by
      intro x hx
      exact hC (Set.mem_image_of_mem _ hx)
    have hC_nonneg : 0 ≤ C := by
      have h3 : A.Nonempty := hA_nonempty
      rcases h3 with ⟨x, hx⟩
      have h4 : 0 ≤ ‖fderiv ℝ g x‖ := by positivity
      have h5 : ‖fderiv ℝ g x‖ ≤ C := hC' x (subset_closure hx)
      linarith
    let K : NNReal := ⟨C, hC_nonneg⟩
    have h_bound : ∀ x ∈ A, ‖fderiv ℝ g x‖ ≤ C := by
      intro x hx
      exact hC' x (subset_closure hx)
    have h_mvt : ∀ (x : EuclideanSpace ℝ (Fin m)), x ∈ A →
        ∀ (y : EuclideanSpace ℝ (Fin m)), y ∈ A →
        dist (g x) (g y) ≤ (K : ℝ) * dist x y := by
      intro x hx y hy
      have h : ‖g y - g x‖ ≤ (K : ℝ) * ‖y - x‖ :=
        hA_conv.norm_image_sub_le_of_norm_fderiv_le
          (fun z _ => h_diff.differentiableAt) h_bound hx hy
      have h' : |g x - g y| ≤ (K : ℝ) * ‖x - y‖ := by
        have h_real : |g y - g x| ≤ (K : ℝ) * ‖y - x‖ := by exact h
        have h_abs : |g y - g x| = |g x - g y| := by rw [abs_sub_comm]
        have h_norm : ‖y - x‖ = ‖x - y‖ := by rw [norm_sub_rev]
        rw [h_abs, h_norm] at h_real
        exact h_real
      simpa [dist_eq_norm] using h'
    exact ⟨K, lipschitzOnWith_iff_dist_le_mul.mpr h_mvt⟩

-- ============================================================================
-- Measure definition
-- ============================================================================

section MeasureDef

variable (g : EuclideanSpace ℝ (Fin m) → ℝ)

/-- Measure on the base space: μ(S) = H^m(graph(g) ∩ cylinder(S)). -/
noncomputable def graphAreaMeasure : Measure (EuclideanSpace ℝ (Fin m)) :=
  Measure.map proj (μHE[m].restrict (graph g))

lemma graphAreaMeasure_apply {S : Set (EuclideanSpace ℝ (Fin m))}
    (hS : MeasurableSet S) :
    graphAreaMeasure g S = μHE[m] (graph g ∩ cylinder S) := by
  have hproj : Measurable (proj : EuclideanSpace ℝ (Fin (m + 1)) → EuclideanSpace ℝ (Fin m)) :=
    Continuous.measurable GraphAreaFormula.continuous_proj
  have h1 : graphAreaMeasure g S = (μHE[m].restrict (graph g)) (proj ⁻¹' S) := by
    simp [graphAreaMeasure, Measure.map_apply hproj hS] <;> rfl
  rw [h1]
  have h2 : proj ⁻¹' S = cylinder S := by
    ext z; simp [cylinder] <;> rfl
  rw [h2]
  have h_cyl_meas : MeasurableSet (cylinder S) := hproj hS
  rw [Measure.restrict_apply h_cyl_meas]
  <;> rw [inter_comm]

lemma graphAreaMeasure_apply_image {S : Set (EuclideanSpace ℝ (Fin m))}
    (hS : MeasurableSet S) :
    graphAreaMeasure g S = μHE[m] (graphMap g '' S) := by
  rw [graphAreaMeasure_apply g hS]
  have h : graph g ∩ cylinder S = graphMap g '' S := graph_cylinder_eq_image g S
  rw [h]

end MeasureDef

-- ============================================================================
-- Local finiteness and absolute continuity
-- ============================================================================

section MeasureProperties

variable (g : EuclideanSpace ℝ (Fin m) → ℝ)

/-- graphAreaMeasure g is locally finite. -/
lemma graphAreaMeasure_locallyFinite (hg : ContDiff ℝ 1 g) :
    IsLocallyFiniteMeasure (graphAreaMeasure g) := by
  refine' ⟨fun x => _⟩
  let B : Set (EuclideanSpace ℝ (Fin m)) := closedBall x 1
  have hB_bdd : Bornology.IsBounded B := isBounded_closedBall
  have hB_conv : Convex ℝ B := convex_closedBall x 1
  rcases contDiff_lipschitzOn_bounded hg hB_conv hB_bdd with ⟨K, hK⟩
  let K' : NNReal := ⟨Real.sqrt (1 + (K : ℝ) ^ 2), by positivity⟩
  have hK' : LipschitzOnWith K' (graphMap g) B := graphMap_lipschitzOnWith hK
  have hB_meas : MeasurableSet B := isClosed_closedBall.measurableSet
  have h1 : graphAreaMeasure g B = μHE[m] (graphMap g '' B) :=
    graphAreaMeasure_apply_image g hB_meas
  refine ⟨B, closedBall_mem_nhds x (by norm_num), ?_⟩
  rw [h1]
  have h2 : μHE[m] (graphMap g '' B) ≤ (K' : ENNReal) ^ (m : ℝ) * μHE[m] B :=
    lipschitzOnWith_euclideanHausdorffMeasure_image_le hK'
  have h3 : (μHE[m] : Measure (EuclideanSpace ℝ (Fin m))) = volume :=
    EuclideanSpace.euclideanHausdorffMeasure_eq_volume m
  rw [h3] at h2
  have h4 : volume B < ⊤ := hB_bdd.measure_lt_top
  have h5 : (K' : ENNReal) ^ (m : ℝ) * volume B < ⊤ :=
    mul_lt_top (by simp) h4
  exact lt_of_le_of_lt h2 h5

/-- graphAreaMeasure g ≪ volume. -/
lemma graphAreaMeasure_absolutelyContinuous (hg : ContDiff ℝ 1 g) :
    (graphAreaMeasure g).AbsolutelyContinuous volume := by
  have h_main : ∀ (S : Set (EuclideanSpace ℝ (Fin m))),
      volume S = 0 → graphAreaMeasure g S = 0 := by
    intro S hS_vol
    let S' := toMeasurable volume S
    have hS'_meas : MeasurableSet S' := measurableSet_toMeasurable volume S
    have hS_sub : S ⊆ S' := subset_toMeasurable volume S
    have hvol_S' : volume S' = 0 := by
      rw [measure_toMeasurable] <;> exact hS_vol
    have h3 : S' = ⋃ n : ℕ, S' ∩ closedBall (0 : EuclideanSpace ℝ (Fin m)) n := by
      ext x
      simp only [Set.mem_iUnion, Set.mem_inter_iff, mem_closedBall, dist_zero_right]
      constructor
      · intro hx
        refine ⟨Nat.ceil ‖x‖, hx, ?_⟩
        have h : ‖x‖ ≤ Nat.ceil ‖x‖ := Nat.le_ceil ‖x‖
        simpa using h
      · rintro ⟨n, ⟨hx, _⟩⟩
        exact hx
    have h4 : ∀ n : ℕ, graphAreaMeasure g (S' ∩ closedBall (0 : EuclideanSpace ℝ (Fin m)) n) = 0 := by
      intro n
      let B : Set (EuclideanSpace ℝ (Fin m)) := closedBall (0 : _) n
      have hB_bdd : Bornology.IsBounded B := isBounded_closedBall
      have hB_conv : Convex ℝ B := convex_closedBall (0 : _) n
      rcases contDiff_lipschitzOn_bounded hg hB_conv hB_bdd with ⟨K, hK⟩
      let K' : NNReal := ⟨Real.sqrt (1 + (K : ℝ) ^ 2), by positivity⟩
      have hK' : LipschitzOnWith K' (graphMap g) B := graphMap_lipschitzOnWith hK
      let SnB : Set (EuclideanSpace ℝ (Fin m)) := S' ∩ B
      have hSnB_sub_B : SnB ⊆ B := Set.inter_subset_right
      have hSnB_meas : MeasurableSet SnB :=
        hS'_meas.inter isClosed_closedBall.measurableSet
      have hK'' : LipschitzOnWith K' (graphMap g) SnB := hK'.mono hSnB_sub_B
      have hvol_SnB : volume SnB = 0 :=
        measure_mono_null (by exact Set.inter_subset_left) hvol_S'
      have h_μHE_SnB : μHE[m] SnB = 0 := by
        have h_eq : (μHE[m] : Measure (EuclideanSpace ℝ (Fin m))) = volume :=
          EuclideanSpace.euclideanHausdorffMeasure_eq_volume m
        rw [h_eq]
        exact hvol_SnB
      have h_img : μHE[m] (graphMap g '' SnB) ≤
          (K' : ENNReal) ^ (m : ℝ) * μHE[m] SnB :=
        lipschitzOnWith_euclideanHausdorffMeasure_image_le hK''
      rw [h_μHE_SnB] at h_img
      have h_img0 : μHE[m] (graphMap g '' SnB) = 0 := by simpa using h_img
      have h_meas_eq : graphAreaMeasure g SnB = μHE[m] (graphMap g '' SnB) :=
        graphAreaMeasure_apply_image g hSnB_meas
      rw [h_meas_eq, h_img0]
    have h5 : graphAreaMeasure g S' = 0 := by
      rw [h3]
      exact MeasureTheory.measure_iUnion_null h4
    have h6 : graphAreaMeasure g S ≤ graphAreaMeasure g S' := measure_mono hS_sub
    rw [h5] at h6
    simpa using h6
  exact Measure.AbsolutelyContinuous.mk (fun {_} hS hvol => h_main _ hvol)

end MeasureProperties

-- ============================================================================
-- Helper: ENNReal power conversion
-- ============================================================================

lemma nnreal_real_pow_eq {x : ℝ} (hx : 0 ≤ x) (n : ℕ) :
    (ENNReal.ofReal x) ^ (n : ℝ) = ENNReal.ofReal (x ^ n) := by
  by_cases h0 : x = 0
  · simp [h0]
  · have hpos : 0 < x := by
      exact lt_of_le_of_ne hx (Ne.symm h0)
    have h1 : (ENNReal.ofReal x) ^ (n : ℝ) = (ENNReal.ofReal x) ^ n := by
      simp [ENNReal.rpow_natCast]
      <;> rfl
    rw [h1]
    rw [ENNReal.ofReal_pow hpos.le]
    <;> rfl

-- ============================================================================
-- Density computation via tangent approximation
-- ============================================================================

section Density

variable (g : EuclideanSpace ℝ (Fin m) → ℝ) (hg : ContDiff ℝ 1 g)
include g hg

/-- For any x₀ and ε > 0 (ε ≤ 1), there exists δ > 0 such that on
closedBall x₀ r (r < δ), the graph area measure is squeezed between
(1±2ε)^{m/2} times the affine tangent area. -/
lemma density_squeeze (x₀ : EuclideanSpace ℝ (Fin m))
    (ε : ℝ) (hε_pos : 0 < ε) (hε_le_one : ε ≤ 1) :
    ∃ (δ : ℝ), 0 < δ ∧ ∀ (r : ℝ), 0 < r → r < δ →
      let a : EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ := fderiv ℝ g x₀
      let C : ENNReal := ENNReal.ofReal (Real.sqrt (1 + ‖a‖ ^ 2))
      let K : ENNReal := ENNReal.ofReal ((Real.sqrt (1 + 2 * ε)) ^ m)
      C / K * volume (closedBall x₀ r) ≤ graphAreaMeasure g (closedBall x₀ r) ∧
      graphAreaMeasure g (closedBall x₀ r) ≤ C * K * volume (closedBall x₀ r) := by
  let a : EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ := fderiv ℝ g x₀
  have h_cont : Continuous (fderiv ℝ g) :=
    ContDiff.continuous_fderiv hg (by norm_num)
  have h1 : ∃ (δ : ℝ), 0 < δ ∧ ∀ (y : EuclideanSpace ℝ (Fin m)),
      y ∈ Metric.ball x₀ δ → ‖fderiv ℝ g y - a‖ < ε := by
    have h_at : ContinuousAt (fderiv ℝ g) x₀ := h_cont.continuousAt
    have h2 : (fderiv ℝ g) ⁻¹' (Metric.ball a ε) ∈ nhds x₀ :=
      h_at.preimage_mem_nhds (Metric.ball_mem_nhds a hε_pos)
    have h : ∀ᶠ (y : EuclideanSpace ℝ (Fin m)) in nhds x₀, ‖fderiv ℝ g y - a‖ < ε := by
      filter_upwards [h2] with y hy
      simpa [Metric.mem_ball, dist_eq_norm] using hy
    have h_exists : ∃ (δ : ℝ), 0 < δ ∧ ∀ (y : EuclideanSpace ℝ (Fin m)),
        dist y x₀ < δ → ‖fderiv ℝ g y - a‖ < ε :=
      Metric.eventually_nhds_iff.mp h
    simpa [Metric.mem_ball, exists_prop] using h_exists
  rcases h1 with ⟨δ, hδ_pos, hδ⟩
  refine ⟨δ, hδ_pos, fun r hr_pos hr_lt => ?_⟩
  let B : Set (EuclideanSpace ℝ (Fin m)) := closedBall x₀ r
  have hB_sub : B ⊆ Metric.ball x₀ δ := by
    intro y hy
    have hdy : dist y x₀ ≤ r := (Metric.mem_closedBall.mp hy)
    have h : dist y x₀ < δ := by linarith
    simpa [Metric.mem_ball] using h
  have hB_convex : Convex ℝ B := convex_closedBall x₀ r
  let h_aff : EuclideanSpace ℝ (Fin m) → ℝ := fun y => g x₀ + a (y - x₀)
  have h_osc : ∀ (w : EuclideanSpace ℝ (Fin m)), w ∈ B → ‖fderiv ℝ g w - a‖ ≤ ε := by
    intro w hw
    have h5 : w ∈ Metric.ball x₀ δ := hB_sub hw
    have h6 : ‖fderiv ℝ g w - a‖ < ε := hδ w h5
    exact le_of_lt h6
  have h_bilip : ∀ (x y : EuclideanSpace ℝ (Fin m)), x ∈ B → y ∈ B →
      ‖graphMap g x - graphMap g y‖ ≤ Real.sqrt (1 + 2 * ε) * ‖graphMap h_aff x - graphMap h_aff y‖ ∧
      ‖graphMap h_aff x - graphMap h_aff y‖ ≤ Real.sqrt (1 + 2 * ε) * ‖graphMap g x - graphMap g y‖ :=
    graph_bilipschitz_comparison g hg B hB_convex x₀ ε (by linarith) hε_le_one h_osc
  have h_measB : MeasurableSet B := isClosed_closedBall.measurableSet
  let K_real : ℝ := Real.sqrt (1 + 2 * ε)
  have hK_pos : 0 < K_real := by positivity
  let K_nn : NNReal := ⟨K_real, hK_pos.le⟩
  let K : ENNReal := ENNReal.ofReal (K_real ^ m)
  have hK_eq : (K_nn : ENNReal) ^ (m : ℝ) = K := by
    have h1 : (K_nn : ENNReal) = ENNReal.ofReal K_real := by
      have h2 : (K_nn : ℝ) = K_real := by
        exact Subtype.coe_mk K_real hK_pos.le
      have h3 : (K_nn : ENNReal) = ENNReal.ofReal (K_nn : ℝ) := by
        have h4 : 0 ≤ (K_nn : ℝ) := K_nn.prop
        rw [ENNReal.ofReal_eq_coe_nnreal h4] <;> simp
      rw [h3, h2]
    rw [h1]
    exact nnreal_real_pow_eq hK_pos.le m
  have hK_ne_top : K ≠ ⊤ := ENNReal.ofReal_ne_top
  have hC_pos : 0 < Real.sqrt (1 + ‖a‖ ^ 2) := by positivity
  let C : ENNReal := ENNReal.ofReal (Real.sqrt (1 + ‖a‖ ^ 2))
  have hC_ne_top : C ≠ ⊤ := ENNReal.ofReal_ne_top
  -- Build Lipschitz maps between the two graph images via projection
  let F : E (m + 1) → E (m + 1) := fun z => graphMap g (proj z)
  let F_inv : E (m + 1) → E (m + 1) := fun z => graphMap h_aff (proj z)

  have hF_img : F '' (graphMap h_aff '' B) = graphMap g '' B := by
    ext z
    simp only [Set.mem_image, F]
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨x, hx, by simp [graphMap_proj]⟩
    · rintro ⟨x, hx, rfl⟩
      refine ⟨graphMap h_aff x, ⟨x, hx, rfl⟩, ?_⟩
      simp [graphMap_proj]

  have hF_inv_img : F_inv '' (graphMap g '' B) = graphMap h_aff '' B := by
    ext z
    simp only [Set.mem_image, F_inv]
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨x, hx, by simp [graphMap_proj]⟩
    · rintro ⟨x, hx, rfl⟩
      refine ⟨graphMap g x, ⟨x, hx, rfl⟩, ?_⟩
      simp [graphMap_proj]

  have hF_lip : LipschitzOnWith K_nn F (graphMap h_aff '' B) := by
    refine' lipschitzOnWith_iff_dist_le_mul.mpr _
    intro z1 hz1 z2 hz2
    rcases hz1 with ⟨x1, hx1, rfl⟩
    rcases hz2 with ⟨x2, hx2, rfl⟩
    have hK_real_coe : (K_nn : ℝ) = K_real := by rfl
    have h : ‖graphMap g x1 - graphMap g x2‖ ≤ (K_nn : ℝ) * ‖graphMap h_aff x1 - graphMap h_aff x2‖ := by
      rw [hK_real_coe]
      exact (h_bilip x1 x2 hx1 hx2).1
    simpa [F, graphMap_proj, dist_eq_norm] using h

  have hF_inv_lip : LipschitzOnWith K_nn F_inv (graphMap g '' B) := by
    refine' lipschitzOnWith_iff_dist_le_mul.mpr _
    intro z1 hz1 z2 hz2
    rcases hz1 with ⟨x1, hx1, rfl⟩
    rcases hz2 with ⟨x2, hx2, rfl⟩
    have hK_real_coe2 : (K_nn : ℝ) = K_real := by rfl
    have h : ‖graphMap h_aff x1 - graphMap h_aff x2‖ ≤ (K_nn : ℝ) * ‖graphMap g x1 - graphMap g x2‖ := by
      rw [hK_real_coe2]
      exact (h_bilip x1 x2 hx1 hx2).2
    simpa [F_inv, graphMap_proj, dist_eq_norm] using h

  have h_meas1 : μHE[m] (graphMap g '' B) ≤ (K_nn : ENNReal) ^ (m : ℝ) * μHE[m] (graphMap h_aff '' B) := by
    have h : μHE[m] (F '' (graphMap h_aff '' B)) ≤ (K_nn : ENNReal) ^ (m : ℝ) * μHE[m] (graphMap h_aff '' B) :=
      lipschitzOnWith_euclideanHausdorffMeasure_image_le hF_lip
    rw [hF_img] at h
    exact h

  have h_meas2 : μHE[m] (graphMap h_aff '' B) ≤ (K_nn : ENNReal) ^ (m : ℝ) * μHE[m] (graphMap g '' B) := by
    have h : μHE[m] (F_inv '' (graphMap g '' B)) ≤ (K_nn : ENNReal) ^ (m : ℝ) * μHE[m] (graphMap g '' B) :=
      lipschitzOnWith_euclideanHausdorffMeasure_image_le hF_inv_lip
    rw [hF_inv_img] at h
    exact h
  rw [hK_eq] at h_meas1 h_meas2
  have h_graph_eq : graphAreaMeasure g B = μHE[m] (graphMap g '' B) :=
    graphAreaMeasure_apply_image g h_measB
  have h_affine : μHE[m] (graphMap h_aff '' B) = C * volume B := by
    have h5 : graphMap h_aff '' B = graph h_aff ∩ cylinder B :=
      (graph_cylinder_eq_image h_aff B).symm
    rw [h5]
    let b : ℝ := g x₀ - a x₀
    have h6 : h_aff = fun y => a y + b := by
      funext y
      simp [h_aff, b] <;> abel
    rw [h6]
    exact graph_area_affine a b B h_measB
  rw [h_graph_eq]
  rw [h_affine] at h_meas1 h_meas2
  exact ⟨by
    have hK_ne_zero : K ≠ 0 := by
      have h_pos : 0 < K_real ^ m := by positivity
      have h : K = ENNReal.ofReal (K_real ^ m) := by rfl
      rw [h]
      have h4 : 0 < ENNReal.ofReal (K_real ^ m) :=
        ENNReal.ofReal_pos.mpr (by positivity)
      exact h4.ne'
    have h_lower : C * volume B ≤ K * μHE[m] (graphMap g '' B) := h_meas2
    have h9 : (C / K) * volume B = (C * volume B) / K := by
      simp [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]
    rw [h9]
    rw [ENNReal.div_le_iff' hK_ne_zero hK_ne_top]
    exact h_lower,
    by
      have h_upper : μHE[m] (graphMap g '' B) ≤ K * (C * volume B) := h_meas1
      have h9 : K * (C * volume B) = C * K * volume B := by
        calc K * (C * volume B)
          = K * C * volume B := by rw [mul_assoc]
        _ = C * K * volume B := by rw [mul_comm K C]
      rw [h9] at h_upper
      exact h_upper⟩

end Density

-- ============================================================================
-- RN derivative identification and final theorem
-- ============================================================================

section Final

variable (g : EuclideanSpace ℝ (Fin m) → ℝ) (hg : ContDiff ℝ 1 g)
include g hg

/-- The RN derivative of graphAreaMeasure w.r.t. volume equals √(1+‖fderiv g x‖²) a.e. -/
lemma graphAreaMeasure_rnDeriv :
    ∀ᵐ (x : EuclideanSpace ℝ (Fin m)) ∂volume,
      (graphAreaMeasure g).rnDeriv volume x =
        ENNReal.ofReal (Real.sqrt (1 + ‖fderiv ℝ g x‖ ^ 2)) := by
  let μ := graphAreaMeasure g
  have h_locfin : IsLocallyFiniteMeasure μ := graphAreaMeasure_locallyFinite g hg
  have h_ac : μ.AbsolutelyContinuous volume := graphAreaMeasure_absolutelyContinuous g hg
  have h_besicovitch : ∀ᵐ (x : EuclideanSpace ℝ (Fin m)) ∂volume,
      Filter.Tendsto (fun r : ℝ => μ (closedBall x r) / volume (closedBall x r))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (μ.rnDeriv volume x)) :=
    Besicovitch.ae_tendsto_rnDeriv μ volume
  filter_upwards [h_besicovitch] with x hx
  let a : EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ := fderiv ℝ g x
  let C : ENNReal := ENNReal.ofReal (Real.sqrt (1 + ‖a‖ ^ 2))
  have hC_ne_top : C ≠ ⊤ := ENNReal.ofReal_ne_top
  have h_main : ∀ (ε : ℝ), 0 < ε → ε ≤ 1 →
      C / ENNReal.ofReal ((Real.sqrt (1 + 2 * ε)) ^ m) ≤ μ.rnDeriv volume x ∧
      μ.rnDeriv volume x ≤ C * ENNReal.ofReal ((Real.sqrt (1 + 2 * ε)) ^ m) := by
    intro ε hε_pos hε_le_one
    rcases density_squeeze g hg x ε hε_pos hε_le_one with ⟨δ, hδ_pos, hδ⟩
    let K : ENNReal := ENNReal.ofReal ((Real.sqrt (1 + 2 * ε)) ^ m)
    have hK_ne_top : K ≠ ⊤ := ENNReal.ofReal_ne_top
    have h_nhds : ∀ᶠ (r : ℝ) in nhdsWithin 0 (Set.Ioi 0), 0 < r ∧ r < δ := by
      have h1 : Iio δ ∈ nhds (0 : ℝ) := Iio_mem_nhds (by linarith)
      have h2 : Iio δ ∈ nhdsWithin 0 (Ioi 0) := Filter.mem_inf_of_left h1
      filter_upwards [self_mem_nhdsWithin, h2] with r hr_pos hr_lt
      exact ⟨hr_pos, hr_lt⟩
    have h_eventually_lower : ∀ᶠ (r : ℝ) in nhdsWithin 0 (Set.Ioi 0),
        C / K ≤ μ (closedBall x r) / volume (closedBall x r) := by
      filter_upwards [h_nhds] with r hr
      have hvol_pos : 0 < volume (closedBall x r) :=
        Metric.measure_closedBall_pos volume x hr.1
      have hvol_ne_zero : volume (closedBall x r) ≠ 0 := hvol_pos.ne'
      have hvol_ne_top : volume (closedBall x r) ≠ ⊤ :=
        isBounded_closedBall.measure_lt_top.ne
      have h1 : C / K * volume (closedBall x r) ≤ μ (closedBall x r) :=
        (hδ r hr.1 hr.2).1
      have h_goal : C / K ≤ μ (closedBall x r) / volume (closedBall x r) := by
        have h_eq : (C / K) * volume (closedBall x r) / volume (closedBall x r) = C / K :=
          ENNReal.mul_div_cancel_right hvol_ne_zero hvol_ne_top
        rw [←h_eq]
        gcongr
      exact h_goal
    have h_eventually_upper : ∀ᶠ (r : ℝ) in nhdsWithin 0 (Set.Ioi 0),
        μ (closedBall x r) / volume (closedBall x r) ≤ C * K := by
      filter_upwards [h_nhds] with r hr
      have hvol_pos : 0 < volume (closedBall x r) :=
        Metric.measure_closedBall_pos volume x hr.1
      have hvol_ne_zero : volume (closedBall x r) ≠ 0 := hvol_pos.ne'
      have hvol_ne_top : volume (closedBall x r) ≠ ⊤ :=
        isBounded_closedBall.measure_lt_top.ne
      have h1 : μ (closedBall x r) ≤ C * K * volume (closedBall x r) :=
        (hδ r hr.1 hr.2).2
      have h_goal : μ (closedBall x r) / volume (closedBall x r) ≤ C * K := by
        rw [ENNReal.div_le_iff hvol_ne_zero hvol_ne_top]
        exact h1
      exact h_goal
    have h_lower : C / K ≤ μ.rnDeriv volume x :=
      ge_of_tendsto hx h_eventually_lower
    have h_upper : μ.rnDeriv volume x ≤ C * K :=
      le_of_tendsto hx h_eventually_upper
    exact ⟨h_lower, h_upper⟩
  -- Show μ.rnDeriv volume x = C by squeezing
  have h_top_ne : μ.rnDeriv volume x ≠ ⊤ := by
    rcases h_main 1 (by norm_num) (by norm_num) with ⟨_, h_upper⟩
    exact ne_top_of_le_ne_top (mul_ne_top hC_ne_top ENNReal.ofReal_ne_top) h_upper
  have h_real_bounds : ∀ (ε : ℝ), 0 < ε → ε ≤ 1 →
      C.toReal / (Real.sqrt (1 + 2 * ε)) ^ m ≤ (μ.rnDeriv volume x).toReal ∧
      (μ.rnDeriv volume x).toReal ≤ C.toReal * (Real.sqrt (1 + 2 * ε)) ^ m := by
    intro ε hε_pos hε_le_one
    rcases h_main ε hε_pos hε_le_one with ⟨h1, h2⟩
    let K : ENNReal := ENNReal.ofReal ((Real.sqrt (1 + 2 * ε)) ^ m)
    have hK_ne_top : K ≠ ⊤ := ENNReal.ofReal_ne_top
    have hK_real_pos : 0 < (Real.sqrt (1 + 2 * ε)) ^ m := by
      have h1 : 0 < Real.sqrt (1 + 2 * ε) := Real.sqrt_pos.mpr (by linarith)
      exact pow_pos h1 m
    exact ⟨by
      have h3 : (C / K).toReal ≤ (μ.rnDeriv volume x).toReal :=
        ENNReal.toReal_mono h_top_ne h1
      have h4 : (C / K).toReal = C.toReal / K.toReal := by
        rw [ENNReal.toReal_div]
        <;> rfl
      have h5 : K.toReal = (Real.sqrt (1 + 2 * ε)) ^ m := by
        rw [ENNReal.toReal_ofReal (by positivity)]
        <;> rfl
      rw [h4, h5] at h3
      exact h3,
      by
      have h3 : (μ.rnDeriv volume x).toReal ≤ (C * K).toReal :=
        ENNReal.toReal_mono (mul_ne_top hC_ne_top hK_ne_top) h2
      have h4 : (C * K).toReal = C.toReal * K.toReal := by
        rw [ENNReal.toReal_mul]
        <;> rfl
      have h5 : K.toReal = (Real.sqrt (1 + 2 * ε)) ^ m := by
        rw [ENNReal.toReal_ofReal (by positivity)]
        <;> rfl
      rw [h4, h5] at h3
      exact h3⟩
  have hC_real_pos : 0 < C.toReal := by
    have h : C.toReal = Real.sqrt (1 + ‖a‖ ^ 2) := by
      rw [ENNReal.toReal_ofReal (by positivity)] <;> rfl
    rw [h] <;> positivity
  have h_lim_lower : C.toReal ≤ (μ.rnDeriv volume x).toReal := by
    by_contra h
    have h' : (μ.rnDeriv volume x).toReal < C.toReal := by linarith
    let f : ℝ → ℝ := fun ε => C.toReal / (Real.sqrt (1 + 2 * ε)) ^ m
    have h_cont_at : ContinuousAt f 0 := by
      have h1 : Continuous (fun ε : ℝ => Real.sqrt (1 + 2 * ε)) := by fun_prop
      have h2 : ContinuousAt (fun ε : ℝ => (Real.sqrt (1 + 2 * ε)) ^ m) 0 := h1.continuousAt.pow m
      have h3 : (Real.sqrt (1 + 2 * (0 : ℝ))) ^ m ≠ 0 := by norm_num
      exact ContinuousAt.div continuousAt_const h2 h3
    have h4 : f 0 = C.toReal := by simp [f]
    have h6 : Tendsto f (nhdsWithin 0 (Ioi 0)) (nhds (f 0)) :=
      h_cont_at.tendsto.mono_left nhdsWithin_le_nhds
    have h_gt : Set.Ioi ((μ.rnDeriv volume x).toReal) ∈ nhds (f 0) := by
      rw [h4]
      exact Ioi_mem_nhds h'
    have h5 : ∀ᶠ (ε : ℝ) in nhdsWithin 0 (Ioi 0), f ε > (μ.rnDeriv volume x).toReal :=
      h6 h_gt
    have h_pos1 : Iio (1 : ℝ) ∈ nhdsWithin 0 (Ioi 0) := by
      apply Filter.mem_inf_of_left
      exact Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num)
    have h_pos : ∀ᶠ (ε : ℝ) in nhdsWithin 0 (Ioi 0), 0 < ε ∧ ε ≤ 1 := by
      filter_upwards [self_mem_nhdsWithin, h_pos1] with ε hε1 hε2
      exact ⟨hε1, le_of_lt hε2⟩
    have h8 : ∃ ε, (f ε > (μ.rnDeriv volume x).toReal) ∧ (0 < ε ∧ ε ≤ 1) :=
      (h5.and h_pos).exists
    rcases h8 with ⟨ε, hgt, ⟨hε_pos, hε_le_one⟩⟩
    have h9 := (h_real_bounds ε hε_pos hε_le_one).1
    linarith
  have h_lim_upper : (μ.rnDeriv volume x).toReal ≤ C.toReal := by
    by_contra h
    have h' : C.toReal < (μ.rnDeriv volume x).toReal := by linarith
    let f : ℝ → ℝ := fun ε => C.toReal * (Real.sqrt (1 + 2 * ε)) ^ m
    have h_cont_at : ContinuousAt f 0 := by
      have h1 : Continuous (fun ε : ℝ => Real.sqrt (1 + 2 * ε)) := by fun_prop
      have h2 : ContinuousAt (fun ε : ℝ => (Real.sqrt (1 + 2 * ε)) ^ m) 0 := h1.continuousAt.pow m
      exact continuousAt_const.mul h2
    have h4 : f 0 = C.toReal := by simp [f]
    have h6 : Tendsto f (nhdsWithin 0 (Ioi 0)) (nhds (f 0)) :=
      h_cont_at.tendsto.mono_left nhdsWithin_le_nhds
    have h_lt : Set.Iio ((μ.rnDeriv volume x).toReal) ∈ nhds (f 0) := by
      rw [h4]
      exact Iio_mem_nhds h'
    have h5 : ∀ᶠ (ε : ℝ) in nhdsWithin 0 (Ioi 0), f ε < (μ.rnDeriv volume x).toReal :=
      h6 h_lt
    have h_pos1 : Iio (1 : ℝ) ∈ nhdsWithin 0 (Ioi 0) := by
      apply Filter.mem_inf_of_left
      exact Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num)
    have h_pos : ∀ᶠ (ε : ℝ) in nhdsWithin 0 (Ioi 0), 0 < ε ∧ ε ≤ 1 := by
      filter_upwards [self_mem_nhdsWithin, h_pos1] with ε hε1 hε2
      exact ⟨hε1, le_of_lt hε2⟩
    have h8 : ∃ ε, (f ε < (μ.rnDeriv volume x).toReal) ∧ (0 < ε ∧ ε ≤ 1) :=
      (h5.and h_pos).exists
    rcases h8 with ⟨ε, hlt, ⟨hε_pos, hε_le_one⟩⟩
    have h9 := (h_real_bounds ε hε_pos hε_le_one).2
    linarith
  have h_toReal_eq : (μ.rnDeriv volume x).toReal = C.toReal := by linarith
  have h_final : μ.rnDeriv volume x = C :=
    (ENNReal.toReal_eq_toReal_iff' h_top_ne hC_ne_top).mp h_toReal_eq
  exact h_final

/-- **Smooth graph area formula.**
For a C¹ function `g : E m → ℝ` and measurable `A`,
the m-dimensional Hausdorff measure of the graph of g over A equals
the integral of the area element √(1 + ‖∇g‖²) over A. -/
theorem graph_area_smooth (hg : ContDiff ℝ 1 g)
    (A : Set (EuclideanSpace ℝ (Fin m))) (hA : MeasurableSet A) :
    μHE[m] (graph g ∩ cylinder A) =
      ∫⁻ x in A, ENNReal.ofReal (Real.sqrt (1 + ‖fderiv ℝ g x‖ ^ 2)) := by
  let μ := graphAreaMeasure g
  have h_ac : μ.AbsolutelyContinuous volume := graphAreaMeasure_absolutelyContinuous g hg
  have h_rn : ∀ᵐ (x : EuclideanSpace ℝ (Fin m)) ∂volume,
      μ.rnDeriv volume x = ENNReal.ofReal (Real.sqrt (1 + ‖fderiv ℝ g x‖ ^ 2)) :=
    graphAreaMeasure_rnDeriv g hg
  have h_locfin : IsLocallyFiniteMeasure μ := graphAreaMeasure_locallyFinite g hg
  letI : IsLocallyFiniteMeasure μ := h_locfin
  have h_main1 : μ A = ∫⁻ x in A, μ.rnDeriv volume x :=
    (MeasureTheory.Measure.setLIntegral_rnDeriv h_ac A).symm
  let f : EuclideanSpace ℝ (Fin m) → ENNReal := fun x =>
    ENNReal.ofReal (Real.sqrt (1 + ‖fderiv ℝ g x‖ ^ 2))
  have h11 : μHE[m] (graph g ∩ cylinder A) = μ A :=
    (graphAreaMeasure_apply g hA).symm
  have h_rn_A : ∀ᵐ (x : EuclideanSpace ℝ (Fin m)) ∂(volume.restrict A),
      μ.rnDeriv volume x = f x :=
    h_rn.filter_mono ae_restrict_le
  have h12 : (∫⁻ x in A, μ.rnDeriv volume x) = ∫⁻ x in A, f x :=
    lintegral_congr_ae h_rn_A
  rw [h11, h_main1, h12]

end Final

end GraphAreaFormula
