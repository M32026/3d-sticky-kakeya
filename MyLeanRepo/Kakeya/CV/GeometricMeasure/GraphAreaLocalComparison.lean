import MyLeanRepo.Kakeya.CV.GeometricMeasure.AffineGraphArea
import MyLeanRepo.Kakeya.CV.GeometricMeasure.GraphPullbackMeasure
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Covering.Besicovitch
import Mathlib.MeasureTheory.Covering.Differentiation

/-!
# Local comparison for the C¹ graph area density

For a globally C¹ function `g : R² → ℝ`, this module compares the graph map
with its tangent affine graph on one sufficiently small ball. The comparison
uses the same local radius throughout, so it can feed Besicovitch
differentiation of `graphPullbackMeasure`.
-/

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal Real

namespace Kakeya.CV

/-- Tangent plane map at x: affine graph of the first-order approximation of g. -/
def tangentPlaneMap (g : R2 → ℝ) (x : R2) : R2 → R3 :=
  graphMap (fun y : R2 => g x + fderiv ℝ g x (y - x))

lemma tangentPlaneMap_leftInverse (g : R2 → ℝ) (x : R2) :
    ∀ (y : R2), graphProjection (tangentPlaneMap g x y) = y := by
  intro y
  ext i
  fin_cases i <;> simp [graphProjection, tangentPlaneMap, graphMap] <;> rfl

/-- A C¹ graph is locally bilipschitz to its tangent plane. -/
lemma lipschitz_comparison
    {g : R2 → ℝ} {x : R2} {D : Set R2}
    (hD : IsOpen D) (hx : x ∈ D) (hg : ContDiffOn ℝ 1 g D)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (r : ℝ), 0 < r ∧ Metric.ball x r ⊆ D ∧
      ∀ (y z : R2), y ∈ Metric.ball x r → z ∈ Metric.ball x r →
        (1 - ε) * ‖tangentPlaneMap g x y - tangentPlaneMap g x z‖ ≤
          ‖graphMap g y - graphMap g z‖ ∧
        ‖graphMap g y - graphMap g z‖ ≤
          (1 + ε) * ‖tangentPlaneMap g x y - tangentPlaneMap g x z‖ := by
  have h_diff : DifferentiableOn ℝ g D := hg.differentiableOn (by norm_num)
  have h_cont : ContinuousOn (fderiv ℝ g) D :=
    (hg.fderiv_of_isOpen hD (m := 0) (by norm_num)).continuousOn
  have h_cont_at : ContinuousAt (fderiv ℝ g) x :=
    h_cont.continuousAt (IsOpen.mem_nhds hD hx)
  have h_ballD : ∃ (r1 : ℝ), 0 < r1 ∧ Metric.ball x r1 ⊆ D :=
    Metric.isOpen_iff.mp hD x hx
  rcases h_ballD with ⟨r1, hr1_pos, hr1_sub⟩
  have h21 :
      ∃ (r2 : ℝ), 0 < r2 ∧
        ∀ ξ, dist ξ x < r2 →
          dist (fderiv ℝ g ξ) (fderiv ℝ g x) < ε :=
    Metric.continuousAt_iff.mp h_cont_at ε hε
  rcases h21 with ⟨r2, hr2_pos, h22⟩
  have h2 :
      ∀ ξ ∈ Metric.ball x r2, ‖fderiv ℝ g ξ - fderiv ℝ g x‖ < ε := by
    intro ξ hξ
    simpa [dist_eq_norm] using h22 ξ hξ
  let r := min r1 r2
  have hr_pos : 0 < r := by positivity
  have hr_sub : Metric.ball x r ⊆ D := by
    intro ξ hξ
    have h6 : dist ξ x < r1 := by
      have h5 : dist ξ x < r := hξ
      linarith [min_le_left r1 r2]
    exact hr1_sub h6
  have hr_deriv :
      ∀ ξ ∈ Metric.ball x r, ‖fderiv ℝ g ξ - fderiv ℝ g x‖ < ε := by
    intro ξ hξ
    have h6 : dist ξ x < r2 := by
      have h5 : dist ξ x < r := hξ
      linarith [min_le_right r1 r2]
    exact h2 ξ h6
  refine ⟨r, hr_pos, hr_sub, ?_⟩
  intro y z hy hz
  let φ := graphMap g
  let ψ := tangentPlaneMap g x
  let E := Metric.ball x r
  have h_diff_at : ∀ ξ ∈ E, DifferentiableAt ℝ g ξ := by
    intro ξ hξ
    exact (h_diff ξ (hr_sub hξ)).differentiableAt
      (IsOpen.mem_nhds hD (hr_sub hξ))
  have h_bound :
      ∀ ξ ∈ E, ‖fderiv ℝ g ξ - fderiv ℝ g x‖ ≤ ε := by
    intro ξ hξ
    exact le_of_lt (hr_deriv ξ hξ)
  have h_mvt :
      ‖g z - g y - fderiv ℝ g x (z - y)‖ ≤ ε * ‖z - y‖ :=
    Convex.norm_image_sub_le_of_norm_fderiv_le'
      h_diff_at h_bound (convex_ball x r) hy hz
  have hψ_ge : ‖ψ y - ψ z‖ ≥ ‖y - z‖ := by
    have h :
        ‖ψ y - ψ z‖ ^ 2 ≥ ‖y - z‖ ^ 2 := by
      simp [ψ, tangentPlaneMap, graphMap, norm_sq_R3, norm_sq_R2] <;>
        nlinarith
    have h3 : 0 ≤ ‖ψ y - ψ z‖ := by positivity
    have h4 : 0 ≤ ‖y - z‖ := by positivity
    nlinarith
  have h_vec_diff :
      ‖φ y - φ z - (ψ y - ψ z)‖ =
        ‖g z - g y - fderiv ℝ g x (z - y)‖ := by
    let v := φ y - φ z - (ψ y - ψ z)
    let xval := g z - g y - fderiv ℝ g x (z - y)
    have h1 : v 0 = 0 := by
      simp [v, φ, ψ, tangentPlaneMap, graphMap] <;> ring
    have h2 : v 1 = 0 := by
      simp [v, φ, ψ, tangentPlaneMap, graphMap] <;> ring
    have h3 : v 2 = -xval := by
      simp [v, φ, ψ, tangentPlaneMap, graphMap, xval] <;> ring
    have h4 : ‖v‖ ^ 2 = xval ^ 2 := by
      rw [norm_sq_R3, h1, h2, h3]
      ring
    have h5 : 0 ≤ ‖v‖ := by positivity
    have h6 : ‖v‖ = |xval| := by
      cases' abs_cases xval with h7 h7 <;> nlinarith
    have h7 : ‖xval‖ = |xval| := by simp [Real.norm_eq_abs]
    rw [h6, h7]
  have h_main :
      ‖φ y - φ z - (ψ y - ψ z)‖ ≤ ε * ‖ψ y - ψ z‖ := by
    rw [h_vec_diff]
    calc
      ‖g z - g y - fderiv ℝ g x (z - y)‖ ≤ ε * ‖z - y‖ := h_mvt
      _ ≤ ε * ‖ψ y - ψ z‖ := by
        gcongr
        simpa [norm_sub_rev] using hψ_ge
  have h_upper :
      ‖φ y - φ z‖ ≤ (1 + ε) * ‖ψ y - ψ z‖ := by
    calc
      ‖φ y - φ z‖ =
          ‖(ψ y - ψ z) + (φ y - φ z - (ψ y - ψ z))‖ := by
        abel_nf
      _ ≤ ‖ψ y - ψ z‖ + ‖φ y - φ z - (ψ y - ψ z)‖ :=
        norm_add_le _ _
      _ ≤ ‖ψ y - ψ z‖ + ε * ‖ψ y - ψ z‖ := by gcongr
      _ = (1 + ε) * ‖ψ y - ψ z‖ := by ring
  have h_lower :
      (1 - ε) * ‖ψ y - ψ z‖ ≤ ‖φ y - φ z‖ := by
    have h :
        ‖ψ y - ψ z‖ ≤
          ‖φ y - φ z‖ + ‖φ y - φ z - (ψ y - ψ z)‖ := by
      calc
        ‖ψ y - ψ z‖ =
            ‖φ y - φ z - (φ y - φ z - (ψ y - ψ z))‖ := by
          abel_nf
        _ ≤ ‖φ y - φ z‖ + ‖φ y - φ z - (ψ y - ψ z)‖ :=
          norm_sub_le _ _
    calc
      (1 - ε) * ‖ψ y - ψ z‖ =
          ‖ψ y - ψ z‖ - ε * ‖ψ y - ψ z‖ := by
        ring
      _ ≤ ‖ψ y - ψ z‖ - ‖φ y - φ z - (ψ y - ψ z)‖ := by
        gcongr
      _ ≤ ‖φ y - φ z‖ := by linarith
  exact ⟨h_lower, h_upper⟩

/-- Hausdorff measure comparison between a C¹ graph and its tangent plane on
one sufficiently small ball. -/
lemma tangent_plane_hausdorff_comparison
    {g : R2 → ℝ} {x : R2} {D : Set R2}
    (hD : IsOpen D) (hx : x ∈ D) (hg : ContDiffOn ℝ 1 g D)
    (ε : ℝ) (hε : 0 < ε) (hε2 : ε < 1) :
    ∃ (r : ℝ), 0 < r ∧
      ∀ (E : Set R2), MeasurableSet E → E ⊆ Metric.ball x r →
        (ENNReal.ofReal (1 - ε)) ^ 2 *
            μH[2] (tangentPlaneMap g x '' E) ≤
          μH[2] (graphMap g '' E) ∧
        μH[2] (graphMap g '' E) ≤
          (ENNReal.ofReal (1 + ε)) ^ 2 *
            μH[2] (tangentPlaneMap g x '' E) := by
  rcases lipschitz_comparison hD hx hg ε hε with
    ⟨r, hr_pos, hr_sub, h_comp⟩
  let ψ := tangentPlaneMap g x
  let Φ := graphMap g ∘ graphProjection
  let Ψ := ψ ∘ graphProjection
  let K_up : NNReal := ⟨1 + ε, by linarith⟩
  let K_down : NNReal := ⟨1 / (1 - ε), by positivity⟩
  refine ⟨r, hr_pos, fun E hE_meas hE_sub => ?_⟩
  have h_lip : LipschitzOnWith K_up Φ (ψ '' E) := by
    rw [lipschitzOnWith_iff_dist_le_mul]
    intro p hp q hq
    rcases hp with ⟨y, hy, rfl⟩
    rcases hq with ⟨z, hz, rfl⟩
    have h := h_comp y z (hE_sub hy) (hE_sub hz)
    have h5 : Φ (ψ y) = graphMap g y := by
      have h10 : graphProjection (ψ y) = y :=
        tangentPlaneMap_leftInverse g x y
      simp [Φ, h10]
    have h6 : Φ (ψ z) = graphMap g z := by
      have h10 : graphProjection (ψ z) = z :=
        tangentPlaneMap_leftInverse g x z
      simp [Φ, h10]
    rw [h5, h6, dist_eq_norm, dist_eq_norm]
    exact h.2
  have h_lip_inv :
      LipschitzOnWith K_down Ψ (graphMap g '' E) := by
    rw [lipschitzOnWith_iff_dist_le_mul]
    intro p hp q hq
    rcases hp with ⟨y, hy, rfl⟩
    rcases hq with ⟨z, hz, rfl⟩
    have h := h_comp y z (hE_sub hy) (hE_sub hz)
    have h5 : Ψ (graphMap g y) = ψ y := by
      simp [Ψ, graphProjection_leftInverse g y]
    have h6 : Ψ (graphMap g z) = ψ z := by
      simp [Ψ, graphProjection_leftInverse g z]
    rw [h5, h6, dist_eq_norm, dist_eq_norm]
    have h_pos : 0 < 1 - ε := by linarith
    calc
      ‖ψ y - ψ z‖ =
          (1 / (1 - ε)) * ((1 - ε) * ‖ψ y - ψ z‖) := by
        field_simp [h_pos.ne']
      _ ≤ (1 / (1 - ε)) * ‖graphMap g y - graphMap g z‖ := by
        gcongr
        exact h.1
  have h_image1 : Φ '' (ψ '' E) = graphMap g '' E := by
    ext z
    simp only [Set.mem_image]
    constructor
    · rintro ⟨p, ⟨y, hy, rfl⟩, rfl⟩
      have h9 : Φ (ψ y) = graphMap g y := by
        have h10 : graphProjection (ψ y) = y :=
          tangentPlaneMap_leftInverse g x y
        simp [Φ, h10]
      exact ⟨y, hy, h9.symm⟩
    · rintro ⟨y, hy, rfl⟩
      have h9 : Φ (ψ y) = graphMap g y := by
        have h10 : graphProjection (ψ y) = y :=
          tangentPlaneMap_leftInverse g x y
        simp [Φ, h10]
      exact ⟨ψ y, ⟨y, hy, rfl⟩, h9⟩
  have h_image2 : Ψ '' (graphMap g '' E) = ψ '' E := by
    ext z
    simp only [Set.mem_image]
    constructor
    · rintro ⟨p, ⟨y, hy, rfl⟩, rfl⟩
      have h9 : Ψ (graphMap g y) = ψ y := by
        have h10 : graphProjection (graphMap g y) = y :=
          graphProjection_leftInverse g y
        simp [Ψ, h10]
      exact ⟨y, hy, h9.symm⟩
    · rintro ⟨y, hy, rfl⟩
      have h9 : Ψ (graphMap g y) = ψ y := by
        have h10 : graphProjection (graphMap g y) = y :=
          graphProjection_leftInverse g y
        simp [Ψ, h10]
      exact ⟨graphMap g y, ⟨y, hy, rfl⟩, h9⟩
  have h_pos : 0 < 1 - ε := by linarith
  have hK_down :
      (K_down : ENNReal) = ENNReal.ofReal (1 / (1 - ε)) := by
    have h1 : (K_down : ℝ) = 1 / (1 - ε) := by
      dsimp only [K_down] <;> rfl
    have h2 : ENNReal.ofReal ((K_down : ℝ)) = (K_down : ENNReal) := by
      simp
    rw [←h2, h1]
  have hK_up :
      (K_up : ENNReal) = ENNReal.ofReal (1 + ε) := by
    have h1 : (K_up : ℝ) = 1 + ε := by
      dsimp only [K_up] <;> rfl
    have h2 : ENNReal.ofReal ((K_up : ℝ)) = (K_up : ENNReal) := by
      simp
    rw [←h2, h1]
  have hpow_down :
      (K_down : ENNReal) ^ (2 : ℝ) =
        (ENNReal.ofReal (1 / (1 - ε))) ^ (2 : ℕ) := by
    rw [hK_down] <;> simp
  have hpow_up :
      (K_up : ENNReal) ^ (2 : ℝ) =
        (ENNReal.ofReal (1 + ε)) ^ (2 : ℕ) := by
    rw [hK_up] <;> simp
  constructor
  · have h :
        μH[2] (Ψ '' (graphMap g '' E)) ≤
          (K_down : ENNReal) ^ (2 : ℝ) *
            μH[2] (graphMap g '' E) :=
      h_lip_inv.hausdorffMeasure_image_le
        (d := (2 : ℝ)) (by norm_num)
    rw [h_image2] at h
    rw [hpow_down] at h
    calc
      (ENNReal.ofReal (1 - ε)) ^ 2 * μH[2] (ψ '' E)
          ≤ (ENNReal.ofReal (1 - ε)) ^ 2 *
              ((ENNReal.ofReal (1 / (1 - ε))) ^ 2 *
                μH[2] (graphMap g '' E)) := by
        gcongr
      _ = μH[2] (graphMap g '' E) := by
        have h11 :
            (ENNReal.ofReal (1 - ε)) ^ 2 *
                (ENNReal.ofReal (1 / (1 - ε))) ^ 2 =
              1 := by
          have h12 :
              ENNReal.ofReal (1 - ε) *
                  ENNReal.ofReal (1 / (1 - ε)) =
                1 := by
            rw [← ENNReal.ofReal_mul (by linarith)]
            have h13 : (1 - ε) * (1 / (1 - ε)) = 1 := by
              field_simp [h_pos.ne'] <;> ring
            rw [h13] <;> simp
          calc
            (ENNReal.ofReal (1 - ε)) ^ 2 *
                (ENNReal.ofReal (1 / (1 - ε))) ^ 2 =
              (ENNReal.ofReal (1 - ε) *
                ENNReal.ofReal (1 / (1 - ε))) ^ 2 := by ring
            _ = 1 ^ 2 := by rw [h12]
            _ = 1 := by ring
        rw [←mul_assoc, h11, one_mul]
  · have h :
        μH[2] (Φ '' (ψ '' E)) ≤
          (K_up : ENNReal) ^ (2 : ℝ) * μH[2] (ψ '' E) :=
      h_lip.hausdorffMeasure_image_le
        (d := (2 : ℝ)) (by norm_num)
    rw [h_image1] at h
    rw [hpow_up] at h
    exact h

/-- The density predicted by the affine tangent-plane formula. -/
def areaFactor (g : R2 → ℝ) (y : R2) : ENNReal :=
  planeConstant * ENNReal.ofReal (Real.sqrt (1 + ‖fderiv ℝ g y‖ ^ 2))

lemma areaFactor_continuousOn {g : R2 → ℝ} {D : Set R2}
    (hD : IsOpen D) (hg : ContDiffOn ℝ 1 g D) :
    ContinuousOn (areaFactor g) D := by
  have h1 : ContinuousOn (fderiv ℝ g) D :=
    (hg.fderiv_of_isOpen hD (m := 0) (by norm_num)).continuousOn
  have h2 :
      ContinuousOn
        (fun y => Real.sqrt (1 + ‖fderiv ℝ g y‖ ^ 2)) D := by
    have h_norm : ContinuousOn (fun y => ‖fderiv ℝ g y‖) D := h1.norm
    have h_sq : ContinuousOn (fun y => ‖fderiv ℝ g y‖ ^ 2) D :=
      h_norm.pow 2
    have h_add :
        ContinuousOn (fun y => 1 + ‖fderiv ℝ g y‖ ^ 2) D :=
      continuousOn_const.add h_sq
    exact Real.continuous_sqrt.comp_continuousOn h_add
  have h3 :
      ContinuousOn
        (fun y => ENNReal.ofReal
          (Real.sqrt (1 + ‖fderiv ℝ g y‖ ^ 2))) D :=
    ENNReal.continuous_ofReal.comp_continuousOn h2
  have h_mul : Continuous (fun z : ENNReal => planeConstant * z) :=
    ENNReal.continuous_const_mul planeConstant_ne_top
  exact h_mul.comp_continuousOn h3

/-- On one sufficiently small comparison ball, graph pullback measure is
bounded above and below by the tangent-plane density times volume. -/
lemma local_area_comparison
    {g : R2 → ℝ} {x : R2} {D : Set R2}
    (hD : IsOpen D) (hx : x ∈ D) (hg : ContDiffOn ℝ 1 g D)
    (ε : ℝ) (hε : 0 < ε) (hε2 : ε < 1) :
    ∃ (r : ℝ), 0 < r ∧
      ∀ (E : Set R2), MeasurableSet E → E ⊆ Metric.ball x r →
        (ENNReal.ofReal (1 - ε)) ^ 2 * areaFactor g x * volume E ≤
          μH[2] (graphMap g '' E) ∧
        μH[2] (graphMap g '' E) ≤
          (ENNReal.ofReal (1 + ε)) ^ 2 * areaFactor g x * volume E := by
  rcases tangent_plane_hausdorff_comparison hD hx hg ε hε hε2 with
    ⟨r, hr_pos, h_comp⟩
  let a : R2 →L[ℝ] ℝ := fderiv ℝ g x
  let b : ℝ := g x - a x
  have h_tangent :
      tangentPlaneMap g x = graphMap (fun y : R2 => a y + b) := by
    funext y
    simp [tangentPlaneMap, graphMap, b] <;> ring
  refine ⟨r, hr_pos, fun E hE_meas hE_sub => ?_⟩
  have h1 := h_comp E hE_meas hE_sub
  have h_affine :
      μH[2] (tangentPlaneMap g x '' E) =
        areaFactor g x * volume E := by
    rw [h_tangent]
    rw [affine_graph_area_unweighted hE_meas]
    <;> rfl
  rw [h_affine] at h1
  simpa [mul_assoc] using h1

end Kakeya.CV
