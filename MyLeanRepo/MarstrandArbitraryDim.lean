module

/-
# Arbitrary-Dimensional Marstrand Projection Theorem

Lower-bound form: for a probability measure μ on ℝ^d with regularized
1-energy I_1^ε(μ) ≤ B, there exists a unit direction θ such that the
ε-neighborhood of π_θ(supp μ) has Lebesgue measure ≥ c_d / B.

## Proof dependencies
- `spherical_geometric_bound`: standard spherical integral (sorry, deep geometric)
- `neighborhood_volume_le_covering`: from CoveringMeasureTranslation
-/

public import MyLeanRepo.Energy.AverageProjectionEnergy
public import MyLeanRepo.ProjectionBasic
public import MyLeanRepo.CoveringMeasureTranslation
public import MyLeanRepo.SphericalIntegral
public import MyLeanRepo.OSWPrelude

@[expose] public section

open MeasureTheory ENNReal Set Classical

noncomputable section

namespace ProductLikeIncidence

/-! ## Definitions -/

/-- Linear projection onto direction θ: π_θ(p) = inner ℝ θ p. -/
noncomputable def linearProjection {d : ℕ} (θ : EuclideanSpace ℝ (Fin d))
    (p : EuclideanSpace ℝ (Fin d)) : ℝ :=
  inner ℝ θ p

/-- ε-ball preimage measure for arbitrary-dimensional projection. -/
def projBallArb {d : ℕ} (ε : ℝ) (θ : EuclideanSpace ℝ (Fin d))
    (μ : Measure (EuclideanSpace ℝ (Fin d))) (t : ℝ) : ENNReal :=
  μ {p | |linearProjection θ p - t| < ε}

/-- ε-neighborhood of the projection of a set. -/
def projectionNeighborhood {d : ℕ} (ε : ℝ)
    (θ : EuclideanSpace ℝ (Fin d))
    (A : Set (EuclideanSpace ℝ (Fin d))) : Set ℝ :=
  {t | ∃ p ∈ A, |linearProjection θ p - t| < ε}

/-- Dimension-dependent constant for the spherical geometric bound. -/
def marstrandSphereConstant (d : ℕ) : ℝ := 4 * (d : ℝ) * Real.pi

/-- The unit sphere in Euclidean space, as a subtype. -/
abbrev Sphere (d : ℕ) : Type :=
  {x : EuclideanSpace ℝ (Fin d) // x ∈ Metric.sphere (0 : _) 1}

/-- Normalized spherical measure (uniform probability on the unit sphere). -/
def sphereProbabilityMeasure (d : ℕ) :
    Measure {x : EuclideanSpace ℝ (Fin d) // x ∈ Metric.sphere (0 : _) 1} :=
  let vol : Measure {x : EuclideanSpace ℝ (Fin d) // x ∈ Metric.sphere (0 : _) 1} :=
    volume.toSphere
  (vol Set.univ)⁻¹ • vol

/-- `sphereProbabilityMeasure d` is a probability measure when `d ≥ 1`. -/
lemma sphereProbabilityMeasure_isProbability {d : ℕ} (hd : 1 ≤ d) :
    IsProbabilityMeasure (sphereProbabilityMeasure d) := by
  let vol : Measure {x : EuclideanSpace ℝ (Fin d) // x ∈ Metric.sphere (0 : _) 1} :=
    volume.toSphere
  let total : ENNReal := vol Set.univ
  have h_total_ne_zero : total ≠ 0 := by
    intro h2
    have h3 : vol = 0 := Measure.measure_univ_eq_zero.mp h2
    have hfin : 0 < Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) := by
      have h : 0 < d := by linarith
      simpa using h
    let i0 : Fin d := ⟨0, by linarith⟩
    haveI : Nontrivial (EuclideanSpace ℝ (Fin d)) := by
      refine' ⟨EuclideanSpace.single i0 1, 0, _⟩
      intro h_eq
      have h9 : (EuclideanSpace.single i0 1 : EuclideanSpace ℝ (Fin d)) i0 = (0 : EuclideanSpace ℝ (Fin d)) i0 := by
        rw [h_eq]
      simpa [EuclideanSpace.single_apply] using h9
    have h5 : vol ≠ 0 := MeasureTheory.Measure.toSphere_ne_zero (μ := volume)
    exact h5 h3
  have h_total_ne_top : total ≠ ⊤ := MeasureTheory.measure_ne_top vol Set.univ
  refine' ⟨_⟩
  have h_def : sphereProbabilityMeasure d = (vol Set.univ)⁻¹ • vol := by rfl
  have h : (sphereProbabilityMeasure d) Set.univ = total⁻¹ * total := by
    rw [h_def]
    <;> simp
    <;> rfl
  rw [h]
  rw [ENNReal.inv_mul_cancel h_total_ne_zero h_total_ne_top] <;> simp

/-- Norm of a sphere point is 1. -/
lemma sphere_norm {d : ℕ} (θ : Sphere d) : ‖θ.val‖ = 1 := by
  have h : θ.val ∈ Metric.sphere (0 : _) 1 := θ.property
  simpa [Metric.mem_sphere, dist_zero_right] using h

/-! ## Helper lemmas -/

/-- Volume of intersection of two ε-intervals centered at a and b. -/
lemma interval_intersection_volume_arb {ε a b : ℝ} (hε : 0 < ε) :
    volume {t : ℝ | |a - t| < ε ∧ |b - t| < ε} =
    ENNReal.ofReal (max 0 (2 * ε - |a - b|)) := by
  let d := |a - b|
  by_cases h : d ≥ 2 * ε
  · have h_empty : {t : ℝ | |a - t| < ε ∧ |b - t| < ε} = (∅ : Set ℝ) := by
      ext t
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro h2
      have h3 : |a - b| ≤ |a - t| + |t - b| := by
        calc |a - b| = |(a - t) + (t - b)| := by ring_nf
          _ ≤ |a - t| + |t - b| := by exact abs_add_le (a - t) (t - b)
      have h4 : |a - t| < ε := h2.1
      have h5 : |b - t| < ε := h2.2
      have h6 : |t - b| = |b - t| := by rw [show t - b = -(b - t) by ring, abs_neg]
      rw [h6] at h3
      linarith
    rw [h_empty]
    have h7 : max 0 (2 * ε - d) = 0 := by rw [max_eq_left] <;> linarith
    rw [h7] <;> simp
  · have h_d_lt : d < 2 * ε := by linarith
    have hdd : d = |a - b| := by rfl
    by_cases h_ab : a ≤ b
    · have h_d : d = b - a := by
        calc d = |a - b| := hdd
          _ = |b - a| := by rw [show a - b = -(b - a) by ring, abs_neg]
          _ = b - a := by rw [abs_of_nonneg (show 0 ≤ b - a by linarith)]
      have h_set : {t : ℝ | |a - t| < ε ∧ |b - t| < ε} = Set.Ioo (b - ε) (a + ε) := by
        ext t
        simp only [Set.mem_setOf_eq, Set.mem_Ioo, abs_lt]
        constructor
        · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
        · rintro ⟨h1, h2⟩
          have h3 : -ε < a - t := by linarith
          have h4 : a - t < ε := by linarith [h_ab]
          have h5 : -ε < b - t := by linarith [h_ab]
          have h6 : b - t < ε := by linarith
          exact ⟨⟨h3, h4⟩, ⟨h5, h6⟩⟩
      rw [h_set, Real.volume_Ioo]
      have h_eq : (a + ε) - (b - ε) = 2 * ε - d := by rw [h_d] <;> ring
      rw [h_eq]
      have h9 : 0 ≤ 2 * ε - d := by linarith
      have h10 : max 0 (2 * ε - d) = 2 * ε - d := by rw [max_eq_right] <;> linarith
      rw [h10, h_d] <;> ring
    · have h_ba : b < a := by linarith
      have h_d : d = a - b := by
        calc d = |a - b| := hdd
          _ = a - b := by rw [abs_of_nonneg (show 0 ≤ a - b by linarith)]
      have h_set : {t : ℝ | |a - t| < ε ∧ |b - t| < ε} = Set.Ioo (a - ε) (b + ε) := by
        ext t
        simp only [Set.mem_setOf_eq, Set.mem_Ioo, abs_lt]
        constructor
        · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
        · rintro ⟨h1, h2⟩
          have h3 : -ε < a - t := by linarith [h_ba]
          have h4 : a - t < ε := by linarith
          have h5 : -ε < b - t := by linarith
          have h6 : b - t < ε := by linarith [h_ba]
          exact ⟨⟨h3, h4⟩, ⟨h5, h6⟩⟩
      rw [h_set, Real.volume_Ioo]
      have h_eq : (b + ε) - (a - ε) = 2 * ε - d := by rw [h_d] <;> ring
      rw [h_eq]
      have h9 : 0 ≤ 2 * ε - d := by linarith
      have h10 : max 0 (2 * ε - d) = 2 * ε - d := by rw [max_eq_right] <;> linarith
      rw [h10, h_d] <;> ring

/-- Measurability of projBallArb in t. -/
private lemma projBall_measurable {d : ℕ} {ε : ℝ} (hε : 0 < ε)
    (μ : Measure (EuclideanSpace ℝ (Fin d))) [SFinite μ]
    (θ : EuclideanSpace ℝ (Fin d)) :
    Measurable (projBallArb ε θ μ) := by
  let E := EuclideanSpace ℝ (Fin d)
  let π : E → ℝ := fun p => linearProjection θ p
  have hπ_cont : Continuous π := continuous_const.inner continuous_id
  let S : Set (ℝ × E) := {x | |π x.2 - x.1| < ε}
  have hS_meas : MeasurableSet S := by
    have h1 : Continuous (fun x : ℝ × E => π x.2 - x.1) :=
      (hπ_cont.comp continuous_snd).sub continuous_fst
    have h_cont : Continuous (fun x : ℝ × E => |π x.2 - x.1|) := h1.abs
    exact (h_cont.isOpen_preimage _ isOpen_Iio).measurableSet
  let f : ℝ × E → ENNReal := Set.indicator S (fun _ => (1 : ENNReal))
  have hf_meas : Measurable f := Measurable.indicator (by fun_prop) hS_meas
  have h_eq : (projBallArb ε θ μ) = fun t => ∫⁻ p, f (t, p) ∂μ := by
    funext t
    have h1 : projBallArb ε θ μ t = μ {p | |π p - t| < ε} := by rfl
    rw [h1]
    let St : Set E := {p | |π p - t| < ε}
    have hSt_meas : MeasurableSet St := by
      have h_cont : Continuous (fun p : E => |π p - t|) :=
        (hπ_cont.sub continuous_const).abs
      exact (h_cont.isOpen_preimage _ isOpen_Iio).measurableSet
    have h2 : (fun p : E => f (t, p)) = Set.indicator St (fun _ => (1 : ENNReal)) := by
      funext p
      simp [f, S, St, Set.indicator_apply] <;> aesop
    have h3 : ∫⁻ p, f (t, p) ∂μ = μ St := by
      rw [h2, lintegral_indicator hSt_meas] <;> simp
    exact h3.symm
  rw [h_eq]
  exact hf_meas.lintegral_prod_right'

/-- Integral of projBallArb over t equals 2ε for a probability measure. -/
lemma projBall_integral_arb {d : ℕ} {ε : ℝ} (hε : 0 < ε)
    (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ]
    (θ : EuclideanSpace ℝ (Fin d)) :
    ∫⁻ (t : ℝ), projBallArb ε θ μ t ∂volume = ENNReal.ofReal (2 * ε) := by
  let E := EuclideanSpace ℝ (Fin d)
  let π : E → ℝ := fun p => linearProjection θ p
  have hπ_cont : Continuous π := continuous_const.inner continuous_id
  let S : Set (ℝ × E) := {x | |π x.2 - x.1| < ε}
  have hS_meas : MeasurableSet S := by
    have h1 : Continuous (fun x : ℝ × E => π x.2 - x.1) :=
      (hπ_cont.comp continuous_snd).sub continuous_fst
    have h_cont : Continuous (fun x : ℝ × E => |π x.2 - x.1|) := h1.abs
    exact (h_cont.isOpen_preimage _ isOpen_Iio).measurableSet
  let f : ℝ × E → ENNReal := Set.indicator S (fun _ => (1 : ENNReal))
  have hf_meas : Measurable f := Measurable.indicator (by fun_prop) hS_meas
  have h_main : ∫⁻ (t : ℝ), projBallArb ε θ μ t ∂volume =
      ∫⁻ (p : E), ∫⁻ (t : ℝ), f (t, p) ∂volume ∂μ := by
    have h_eq1 : ∀ t, projBallArb ε θ μ t = ∫⁻ p, f (t, p) ∂μ := by
      intro t
      have h1 : projBallArb ε θ μ t = μ {p | |π p - t| < ε} := by rfl
      rw [h1]
      let St : Set E := {p | |π p - t| < ε}
      have hSt_meas : MeasurableSet St := by
        have h_cont : Continuous (fun p : E => |π p - t|) :=
          (hπ_cont.sub continuous_const).abs
        exact (h_cont.isOpen_preimage _ isOpen_Iio).measurableSet
      have h2 : (fun p : E => f (t, p)) = Set.indicator St (fun _ => (1 : ENNReal)) := by
        funext p
        simp [f, S, St, Set.indicator_apply] <;> aesop
      have h3 : ∫⁻ p, f (t, p) ∂μ = μ St := by
        rw [h2, lintegral_indicator hSt_meas] <;> simp
      exact h3.symm
    have h4 : ∫⁻ (t : ℝ), projBallArb ε θ μ t ∂volume =
        ∫⁻ (t : ℝ), ∫⁻ (p : E), f (t, p) ∂μ ∂volume := by
      congr with t; exact h_eq1 t
    rw [h4]
    exact lintegral_lintegral_swap hf_meas.aemeasurable
  rw [h_main]
  have h3 : ∀ (p : E), ∫⁻ (t : ℝ), f (t, p) ∂volume = ENNReal.ofReal (2 * ε) := by
    intro p
    let St : Set ℝ := {t | |π p - t| < ε}
    have hSt_meas : MeasurableSet St := by
      have h_cont : Continuous (fun t : ℝ => π p - t) := by continuity
      exact isOpen_Iio.preimage (h_cont.abs) |>.measurableSet
    have h4 : ∫⁻ (t : ℝ), f (t, p) ∂volume = volume St := by
      have h5 : ∀ (t : ℝ), f (t, p) = Set.indicator St (fun _ => (1 : ENNReal)) t := by
        intro t
        simp [f, S, St, Set.indicator_apply] <;> aesop
      rw [lintegral_congr h5, lintegral_indicator hSt_meas] <;> simp
    rw [h4]
    have hS_eq : St = Set.Ioo (π p - ε) (π p + ε) := by
      ext t
      simp only [St, Set.mem_Ioo, abs_lt] <;> constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
    rw [hS_eq, Real.volume_Ioo]
    have h7 : (π p + ε) - (π p - ε) = 2 * ε := by ring
    rw [h7]
  have h4 : ∫⁻ (p : E), ∫⁻ (t : ℝ), f (t, p) ∂volume ∂μ =
      ∫⁻ (p : E), ENNReal.ofReal (2 * ε) ∂μ := by
    congr with p; exact h3 p
  rw [h4]
  have h5 : ∫⁻ (p : E), ENNReal.ofReal (2 * ε) ∂μ =
      ENNReal.ofReal (2 * ε) * μ Set.univ := by
    rw [lintegral_const]
  rw [h5]
  have h6 : μ Set.univ = 1 := by simp
  rw [h6] <;> simp

/-! ## Key lemmas -/

/-- Fubini expansion: ∫ (projBall)² dt = ∫∫ volume of intersection. -/
lemma fubini_expansion_arb {d : ℕ} {ε : ℝ} (hε : 0 < ε)
    (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsFiniteMeasure μ]
    (θ : EuclideanSpace ℝ (Fin d)) :
    ∫⁻ (t : ℝ), (projBallArb ε θ μ t)^2 ∂volume =
    ∫⁻ (p : _), ∫⁻ (q : _),
      ENNReal.ofReal (max 0 (2 * ε - |linearProjection θ p - linearProjection θ q|))
      ∂μ ∂μ := by
  let E := EuclideanSpace ℝ (Fin d)
  let π : E → ℝ := fun p => linearProjection θ p
  have hπ_cont : Continuous π := continuous_const.inner continuous_id
  let A : ℝ → Set E := fun t => {p | |π p - t| < ε}
  have hA_meas : ∀ t, MeasurableSet (A t) := by
    intro t
    have h_set_eq : A t = π ⁻¹' (Set.Ioo (t - ε) (t + ε)) := by
      ext p
      simp only [A, Set.mem_preimage, Set.mem_Ioo, abs_lt]
      <;> constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
    rw [h_set_eq]
    exact isOpen_Ioo.preimage hπ_cont |>.measurableSet
  let h : ℝ → E → ENNReal := fun t p =>
    Set.indicator (A t) (fun _ => (1 : ENNReal)) p
  have h_meas : Measurable (Function.uncurry h) := by
    let S : Set (ℝ × E) := {x | |π x.2 - x.1| < ε}
    have hS_meas : MeasurableSet S := by
      have h1 : Continuous (fun x : ℝ × E => π x.2 - x.1) :=
        (hπ_cont.comp continuous_snd).sub continuous_fst
      exact (h1.abs.isOpen_preimage _ isOpen_Iio).measurableSet
    have h_eq : Function.uncurry h = Set.indicator S (fun _ => (1 : ENNReal)) := by
      ext x
      simp [h, Function.uncurry, Set.indicator] <;> aesop
    rw [h_eq]
    exact Measurable.indicator measurable_const hS_meas
  have h1 : ∀ t, projBallArb ε θ μ t = ∫⁻ p, h t p ∂μ := by
    intro t
    have h_eq1 : projBallArb ε θ μ t = μ (A t) := by rfl
    rw [h_eq1]
    have h2 : μ (A t) = ∫⁻ p, Set.indicator (A t) (fun _ => (1 : ENNReal)) p ∂μ := by
      rw [lintegral_indicator (hA_meas t)] <;> simp
    rw [h2] <;> rfl
  have h2 : ∀ t, (projBallArb ε θ μ t)^2 = ∫⁻ p, ∫⁻ q, h t p * h t q ∂μ ∂μ := by
    intro t
    have ht_meas : Measurable (h t) := by
      simpa [h] using Measurable.indicator measurable_const (hA_meas t)
    have hsq : (projBallArb ε θ μ t)^2 = (projBallArb ε θ μ t) * (projBallArb ε θ μ t) := by ring
    rw [hsq, h1 t]
    have h3 : (∫⁻ p, h t p ∂μ) * (∫⁻ q, h t q ∂μ) =
        ∫⁻ p, h t p * (∫⁻ q, h t q ∂μ) ∂μ := by
      rw [lintegral_mul_const] <;> exact ht_meas
    rw [h3]
    congr with p
    rw [lintegral_const_mul] <;> exact ht_meas
  have h_f1 : AEMeasurable (Function.uncurry fun (t : ℝ) (p : E) => ∫⁻ (q : E), h t p * h t q ∂μ)
      (Measure.prod volume μ) := by fun_prop
  have h_main : ∫⁻ (t : ℝ), (projBallArb ε θ μ t)^2 ∂volume =
      ∫⁻ (p : E), ∫⁻ (q : E), ∫⁻ (t : ℝ), h t p * h t q ∂volume ∂μ ∂μ := by
    have h4 : ∫⁻ (t : ℝ), (projBallArb ε θ μ t)^2 ∂volume =
        ∫⁻ (t : ℝ), ∫⁻ (p : E), ∫⁻ (q : E), h t p * h t q ∂μ ∂μ ∂volume := by
      congr with t; exact h2 t
    rw [h4]
    rw [lintegral_lintegral_swap h_f1]
    congr with p
    have h_f2 : AEMeasurable (Function.uncurry fun (t : ℝ) (q : E) => h t p * h t q)
        (Measure.prod volume μ) := by fun_prop
    rw [lintegral_lintegral_swap h_f2] <;> rfl
  rw [h_main]
  congr with p
  congr with q
  let S : Set ℝ := {t | |π p - t| < ε ∧ |π q - t| < ε}
  have hS_meas : MeasurableSet S := by
    have h_cont1 : Continuous (fun t : ℝ => π p - t) := by continuity
    have h_cont2 : Continuous (fun t : ℝ => π q - t) := by continuity
    have h1 : MeasurableSet {t : ℝ | |π p - t| < ε} :=
      isOpen_Iio.preimage (h_cont1.abs) |>.measurableSet
    have h2 : MeasurableSet {t : ℝ | |π q - t| < ε} :=
      isOpen_Iio.preimage (h_cont2.abs) |>.measurableSet
    exact h1.inter h2
  have h6 : ∫⁻ (t : ℝ), h t p * h t q ∂volume = volume S := by
    have h7 : ∀ (t : ℝ), h t p * h t q = Set.indicator S (fun _ => (1 : ENNReal)) t := by
      intro t
      simp [h, S, Set.indicator] <;> aesop
    have h8 : ∫⁻ (t : ℝ), h t p * h t q ∂volume =
        ∫⁻ (t : ℝ), Set.indicator S (fun _ => (1 : ENNReal)) t ∂volume := by
      congr with t
      exact h7 t
    rw [h8, lintegral_indicator hS_meas] <;> simp
  rw [h6]
  exact interval_intersection_volume_arb hε

/-- Spherical geometric bound for the uniform spherical measure. -/
lemma spherical_geometric_bound {d : ℕ} (hd : 2 ≤ d)
    {r ε : ℝ} (hr_pos : 0 < r) (hε_pos : 0 < ε)
    (v : EuclideanSpace ℝ (Fin d)) (hv : ‖v‖ = 1) :
    ∫⁻ (θ : Sphere d),
      ENNReal.ofReal (max 0 (2 * ε - r * |linearProjection θ.val v|))
      ∂(sphereProbabilityMeasure d)
    ≤ ENNReal.ofReal (marstrandSphereConstant d * ε^2 / max r ε) := by
  have h_inner : ∀ (x y : EuclideanSpace ℝ (Fin d)),
      inner ℝ x y = ∑ i : Fin d, x i * y i := by
    intro x y
    have h1 : inner ℝ x y = ∑ i : Fin d, y i * x i := by
      rw [EuclideanSpace.inner_eq_star_dotProduct x y]
      <;> simp [dotProduct] <;> rfl
    rw [h1]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have h_main := WeakTwoEndsSumProduct.spherical_geometric_bound hd hr_pos hε_pos v hv
  dsimp only at h_main
  have h_integrand : ∀ (θ : Sphere d),
      ENNReal.ofReal (max 0 (2 * ε - r * |linearProjection θ.val v|)) =
      ENNReal.ofReal (max 0 (2 * ε - r * |∑ i : Fin d, (θ : EuclideanSpace ℝ (Fin d)) i * v i|)) := by
    intro θ
    have h_eq : linearProjection θ.val v = ∑ i : Fin d, (θ : EuclideanSpace ℝ (Fin d)) i * v i := by
      simpa [linearProjection] using h_inner (θ : EuclideanSpace ℝ (Fin d)) v
    rw [h_eq]
  have h_eq : ∫⁻ (θ : Sphere d),
      ENNReal.ofReal (max 0 (2 * ε - r * |linearProjection θ.val v|)) ∂(sphereProbabilityMeasure d) =
      ∫⁻ (θ : Sphere d),
      ENNReal.ofReal (max 0 (2 * ε - r * |∑ i : Fin d, (θ : EuclideanSpace ℝ (Fin d)) i * v i|)) ∂(sphereProbabilityMeasure d) := by
    congr with θ
    exact h_integrand θ
  rw [h_eq]
  exact h_main

/-- Cauchy-Schwarz: 4ε² ≤ |neighborhood| * ∫ (projBall)² dt. -/
lemma projection_neighborhood_cs {d : ℕ} {ε : ℝ} (hε : 0 < ε)
    (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ]
    (θ : EuclideanSpace ℝ (Fin d)) :
    ENNReal.ofReal (4 * ε^2) ≤
      volume (projectionNeighborhood ε θ μ.support) *
        ∫⁻ (t : ℝ), (projBallArb ε θ μ t)^2 ∂volume := by
  let f : ℝ → ENNReal := fun t => projBallArb ε θ μ t
  let S : Set ℝ := projectionNeighborhood ε θ μ.support
  let I : ENNReal := ∫⁻ (t : ℝ), (f t)^2 ∂volume
  let V : ENNReal := volume S
  have hf_meas : Measurable f := projBall_measurable hε μ θ
  have hS_open : IsOpen S := by
    have h1 : S = ⋃ p ∈ μ.support, Set.Ioo (linearProjection θ p - ε) (linearProjection θ p + ε) := by
      ext t
      simp only [S, projectionNeighborhood, Set.mem_iUnion, Set.mem_Ioo, abs_lt, Set.mem_setOf_eq]
      <;> constructor
      · rintro ⟨p, hp, h1, h2⟩
        exact ⟨p, hp, by linarith, by linarith⟩
      · rintro ⟨p, hp, h1, h2⟩
        exact ⟨p, hp, by linarith, by linarith⟩
    rw [h1]
    exact isOpen_biUnion (fun _ _ => isOpen_Ioo)
  have hS_meas : MeasurableSet S := hS_open.measurableSet
  have h_ae : ∀ᵐ (p : EuclideanSpace ℝ (Fin d)) ∂μ, p ∈ μ.support :=
    MeasureTheory.Measure.support_mem_ae (μ := μ)
  have h_support : ∀ t, t ∉ S → f t = 0 := by
    intro t ht
    by_contra h
    have h_pos : 0 < f t := by exact Ne.pos h
    let A : Set (EuclideanSpace ℝ (Fin d)) := {p | |linearProjection θ p - t| < ε}
    have hA_pos : μ A > 0 := h_pos
    have hA_meas : MeasurableSet A := by
      have hπ_cont : Continuous (fun p : EuclideanSpace ℝ (Fin d) => linearProjection θ p) :=
        continuous_const.inner continuous_id
      have h_cont : Continuous (fun p : EuclideanSpace ℝ (Fin d) => |linearProjection θ p - t|) :=
        (hπ_cont.sub continuous_const).abs
      exact (h_cont.isOpen_preimage _ isOpen_Iio).measurableSet
    have h_inter_nonempty : (A ∩ μ.support).Nonempty := by
      by_contra h2
      have h_empty : A ∩ μ.support = ∅ := Set.not_nonempty_iff_eq_empty.mp h2
      have h_sub : A ⊆ μ.supportᶜ := by
        intro p hp
        have h : p ∉ μ.support := by
          intro h3
          have h4 : p ∈ A ∩ μ.support := ⟨hp, h3⟩
          rw [h_empty] at h4 <;> simpa using h4
        exact h
      have h_compl_null : μ (μ.supportᶜ) = 0 := by
        simpa [ae_iff] using h_ae
      have h4 : μ A = 0 := measure_mono_null h_sub h_compl_null
      have h5 : μ A ≤ 0 := by
        rw [h4] <;> simp
      exact not_le.mpr hA_pos h5
    rcases h_inter_nonempty with ⟨p, hp, hpsupp⟩
    exact ht ⟨p, hpsupp, hp⟩
  let g : ℝ → ENNReal := fun t => Set.indicator S (fun _ => (1 : ENNReal)) t
  have hg_meas : Measurable g := Measurable.indicator (by fun_prop) hS_meas
  have h_ind : ∀ t, f t * g t = f t := by
    intro t
    by_cases h : t ∈ S
    · simp [g, h, Set.indicator_apply]
    · have h0 : f t = 0 := h_support t h
      simp [h0, g, h, Set.indicator_apply]
  have h_int_f : ∫⁻ (t : ℝ), f t ∂volume = ENNReal.ofReal (2 * ε) :=
    projBall_integral_arb hε μ θ
  have h_int_g : ∫⁻ (t : ℝ), g t ∂volume = V := by
    rw [lintegral_indicator hS_meas] <;> simp [V, g] <;> rfl
  have h_g2 : ∀ t, (g t)^2 = g t := by
    intro t
    simp [g, Set.indicator_apply] <;> split_ifs <;> simp
  have h_h2 : (2 : ℝ).HolderConjugate (2 : ℝ) := Real.HolderConjugate.two_two
  have h_holder : ∫⁻ (t : ℝ), (f * g) t ∂volume ≤
      (∫⁻ (t : ℝ), (f t)^(2 : ℝ) ∂volume) ^ (1 / 2 : ℝ) *
      (∫⁻ (t : ℝ), (g t)^(2 : ℝ) ∂volume) ^ (1 / 2 : ℝ) :=
    ENNReal.lintegral_mul_le_Lp_mul_Lq volume h_h2 hf_meas.aemeasurable hg_meas.aemeasurable
  have h_fg_eq : ∫⁻ (t : ℝ), (f * g) t ∂volume = ∫⁻ (t : ℝ), f t ∂volume := by
    apply lintegral_congr
    intro t
    have h : (f * g) t = f t * g t := by rfl
    rw [h]
    exact h_ind t
  rw [h_fg_eq] at h_holder
  rw [h_int_f] at h_holder
  have h_int_g2 : ∫⁻ (t : ℝ), (g t)^(2 : ℝ) ∂volume = V := by
    have h_eq1 : ∀ t, (g t)^(2 : ℝ) = g t := by
      intro t
      have h1 : (g t)^2 = g t := h_g2 t
      have h2 : (g t)^(2 : ℝ) = (g t)^2 := by
        rw [← ENNReal.rpow_natCast] <;> norm_num
      rw [h2, h1]
    have h3 : ∫⁻ (t : ℝ), (g t)^(2 : ℝ) ∂volume = ∫⁻ (t : ℝ), g t ∂volume := by
      congr with t; exact h_eq1 t
    rw [h3, h_int_g]
  rw [h_int_g2] at h_holder
  have h_I_eq : ∫⁻ (t : ℝ), (f t)^(2 : ℝ) ∂volume = I := by
    have h1 : ∀ t, (f t)^(2 : ℝ) = (f t)^2 := by
      intro t
      rw [← ENNReal.rpow_natCast] <;> norm_num
    congr with t; exact h1 t
  rw [h_I_eq] at h_holder
  have h9 : ENNReal.ofReal (2 * ε) ≤ I ^ (1 / 2 : ℝ) * V ^ (1 / 2 : ℝ) := h_holder
  have h10 : (ENNReal.ofReal (2 * ε)) ^ (2 : ℝ) ≤ (I ^ (1 / 2 : ℝ) * V ^ (1 / 2 : ℝ)) ^ (2 : ℝ) := by
    gcongr
  have h11 : (ENNReal.ofReal (2 * ε)) ^ (2 : ℝ) = ENNReal.ofReal (4 * ε^2) := by
    have h11a : (ENNReal.ofReal (2 * ε)) ^ (2 : ℝ) = (ENNReal.ofReal (2 * ε)) ^ 2 :=
      ENNReal.rpow_natCast _ 2
    rw [h11a]
    have h11b : (ENNReal.ofReal (2 * ε)) ^ 2 = ENNReal.ofReal ((2 * ε)^2) := by
      have h11b1 : (ENNReal.ofReal (2 * ε)) ^ 2 =
          (ENNReal.ofReal (2 * ε)) * (ENNReal.ofReal (2 * ε)) := by ring
      rw [h11b1]
      have h_pos : 0 ≤ 2 * ε := by linarith
      rw [← ENNReal.ofReal_mul h_pos] <;> ring_nf
    rw [h11b]
    have h11c : (2 * ε)^2 = 4 * ε^2 := by ring
    rw [h11c]
  have h12 : (I ^ (1 / 2 : ℝ) * V ^ (1 / 2 : ℝ)) ^ (2 : ℝ) = I * V := by
    have h13 : (I ^ (1 / 2 : ℝ) * V ^ (1 / 2 : ℝ)) ^ (2 : ℝ) =
        (I ^ (1 / 2 : ℝ)) ^ (2 : ℝ) * (V ^ (1 / 2 : ℝ)) ^ (2 : ℝ) :=
      ENNReal.mul_rpow_of_nonneg (I ^ (1 / 2 : ℝ)) (V ^ (1 / 2 : ℝ)) (by norm_num)
    rw [h13]
    have h14 : (I ^ (1 / 2 : ℝ)) ^ (2 : ℝ) = I := by
      have h141 : I ^ ((1 / 2 : ℝ) * (2 : ℝ)) = (I ^ (1 / 2 : ℝ)) ^ (2 : ℝ) :=
        ENNReal.rpow_mul I (1 / 2 : ℝ) (2 : ℝ)
      have h142 : (1 / 2 : ℝ) * (2 : ℝ) = 1 := by norm_num
      rw [h142] at h141
      simpa using h141.symm
    have h15 : (V ^ (1 / 2 : ℝ)) ^ (2 : ℝ) = V := by
      have h151 : V ^ ((1 / 2 : ℝ) * (2 : ℝ)) = (V ^ (1 / 2 : ℝ)) ^ (2 : ℝ) :=
        ENNReal.rpow_mul V (1 / 2 : ℝ) (2 : ℝ)
      have h152 : (1 / 2 : ℝ) * (2 : ℝ) = 1 := by norm_num
      rw [h152] at h151
      simpa using h151.symm
    rw [h14, h15] <;> ring
  rw [h11, h12] at h10
  have h10' : ENNReal.ofReal (4 * ε^2) ≤ V * I := by
    rwa [mul_comm I V] at h10
  simpa [I, V] using h10'

/-! ## Main theorem -/

/-- **Arbitrary-dimensional Marstrand projection theorem (lower bound).** -/
theorem marstrand_projection_lower_bound {d : ℕ} (hd : 2 ≤ d)
    {ε B : ℝ} (hε : 0 < ε) (hB : 0 < B)
    (μ : Measure (EuclideanSpace ℝ (Fin d)))
    [IsProbabilityMeasure μ]
    (hI : robust_projection_main.rieszEnergy (α := 1) (hδ := hε) μ ≤ ENNReal.ofReal B) :
    ∃ (θ : Sphere d),
      ENNReal.ofReal (1 / (4 * marstrandSphereConstant d * B)) ≤
        volume (projectionNeighborhood ε θ.val μ.support) := by
  let σ : Measure (Sphere d) := sphereProbabilityMeasure d
  haveI : IsProbabilityMeasure σ := sphereProbabilityMeasure_isProbability (by linarith)
  let C := marstrandSphereConstant d
  let L : Sphere d → ENNReal := fun θ =>
    ∫⁻ (t : ℝ), (projBallArb ε θ.val μ t)^2 ∂volume
  let V : Sphere d → ENNReal := fun θ =>
    volume (projectionNeighborhood ε θ.val μ.support)
  have h_cs : ∀ θ, ENNReal.ofReal (4 * ε^2) ≤ V θ * L θ := by
    intro θ
    exact projection_neighborhood_cs hε μ θ.val
  have h_fubini : ∀ θ, L θ = ∫⁻ (p : _), ∫⁻ (q : _),
      ENNReal.ofReal (max 0 (2 * ε - |linearProjection θ.val p - linearProjection θ.val q|))
      ∂μ ∂μ := by
    intro θ
    exact fubini_expansion_arb hε μ θ.val
  let E := EuclideanSpace ℝ (Fin d)
  let g_uncurry : (E × E) × Sphere d → ENNReal := fun x =>
    ENNReal.ofReal (max 0 (2 * ε - |inner ℝ x.2.val x.1.1 - inner ℝ x.2.val x.1.2|))
  have h11 : Continuous (fun x : (E × E) × Sphere d => (x.2.val, x.1.1)) := by fun_prop
  have h12 : Continuous (fun x : (E × E) × Sphere d => (x.2.val, x.1.2)) := by fun_prop
  let f3 : (E × E) × Sphere d → ℝ := fun x => inner ℝ x.2.val x.1.1
  let f4 : (E × E) × Sphere d → ℝ := fun x => inner ℝ x.2.val x.1.2
  have h3 : Continuous f3 := by
    have h : Continuous (fun p : E × E => inner ℝ p.1 p.2) := continuous_inner
    exact h.comp h11
  have h4 : Continuous f4 := by
    have h : Continuous (fun p : E × E => inner ℝ p.1 p.2) := continuous_inner
    exact h.comp h12
  have h5 : Continuous (fun x : (E × E) × Sphere d => max 0 (2 * ε - |f3 x - f4 x|)) := by
    have h_sub : Continuous (fun x => f3 x - f4 x) := h3.sub h4
    have h_abs : Continuous (fun x => |f3 x - f4 x|) := h_sub.abs
    have h_neg : Continuous (fun x => (2 * ε : ℝ) - |f3 x - f4 x|) := continuous_const.sub h_abs
    exact continuous_const.max h_neg
  have h_g_cont : Continuous g_uncurry := (continuous_ofReal).comp h5
  have h_g_meas : Measurable g_uncurry := h_g_cont.measurable
  have h_g_eq : ∀ (p : E) (q : E) (θ : Sphere d),
      g_uncurry ((p, q), θ) = ENNReal.ofReal (max 0 (2 * ε - |linearProjection θ.val p - linearProjection θ.val q|)) := by
    intro p q θ
    simp [g_uncurry, linearProjection]
    <;> rfl
  -- Fubini swap 1
  let reindex1 : ((Sphere d × E) × E) → (E × E) × Sphere d := fun x => ((x.1.2, x.2), x.1.1)
  have h_reindex1_cont : Continuous reindex1 := by fun_prop
  have h1_meas : Measurable (fun x : ((Sphere d × E) × E) => g_uncurry (reindex1 x)) :=
    h_g_meas.comp h_reindex1_cont.measurable
  have h_f1_meas : Measurable (fun y : Sphere d × E => ∫⁻ (q : E), g_uncurry (reindex1 (y, q)) ∂μ) :=
    Measurable.lintegral_prod_right h1_meas
  have h_swap1 : ∫⁻ (θ : Sphere d), ∫⁻ (p : E), (∫⁻ (q : E), g_uncurry ((p, q), θ) ∂μ) ∂μ ∂σ =
      ∫⁻ (p : E), ∫⁻ (θ : Sphere d), (∫⁻ (q : E), g_uncurry ((p, q), θ) ∂μ) ∂σ ∂μ :=
    lintegral_lintegral_swap h_f1_meas.aemeasurable
  -- Fubini swap 2
  have h_swap2 : ∀ (p : E),
      ∫⁻ (θ : Sphere d), ∫⁻ (q : E), g_uncurry ((p, q), θ) ∂μ ∂σ =
      ∫⁻ (q : E), ∫⁻ (θ : Sphere d), g_uncurry ((p, q), θ) ∂σ ∂μ := by
    intro p
    have h2_meas : Measurable (Function.uncurry fun (θ : Sphere d) (q : E) => g_uncurry ((p, q), θ)) := by
      have h_const : Continuous (fun x : Sphere d × E => p) := by
        exact continuous_const
      have h_snd : Continuous (fun x : Sphere d × E => x.snd) := continuous_snd
      have h1 : Continuous (fun x : Sphere d × E => (p, x.snd)) := by fun_prop
      have h_fst : Continuous (fun x : Sphere d × E => x.fst) := continuous_fst
      have h_map : Continuous (fun x : Sphere d × E => ((p, x.snd), x.fst)) := by fun_prop
      exact h_g_meas.comp h_map.measurable
    exact lintegral_lintegral_swap (hf := h2_meas.aemeasurable)
  have h_swap : ∫⁻ (θ : Sphere d), L θ ∂σ =
      ∫⁻ (p : E), ∫⁻ (q : E), ∫⁻ (θ : Sphere d), g_uncurry ((p, q), θ) ∂σ ∂μ ∂μ := by
    have h1 : ∫⁻ (θ : Sphere d), L θ ∂σ =
        ∫⁻ (θ : Sphere d), ∫⁻ (p : E), ∫⁻ (q : E), g_uncurry ((p, q), θ) ∂μ ∂μ ∂σ := by
      congr with θ
      exact h_fubini θ
    rw [h1, h_swap1]
    congr with p
    exact h_swap2 p
  have h_spherical_uniform : ∀ (p q : E),
      ∫⁻ (θ : Sphere d), g_uncurry ((p, q), θ) ∂σ ≤
      ENNReal.ofReal (C * ε^2 * (max (dist p q) ε)^(-1 : ℝ)) := by
    intro p q
    by_cases h : p = q
    · -- Case p = q
      have hq : q = p := h.symm
      have h2 : ∀ θ, g_uncurry ((p, q), θ) = ENNReal.ofReal (2 * ε) := by
        intro θ
        rw [hq]
        have h_eq : g_uncurry ((p, p), θ) = ENNReal.ofReal (max 0 (2 * ε - |linearProjection θ.val p - linearProjection θ.val p|)) := h_g_eq p p θ
        rw [h_eq]
        have h_sub : linearProjection θ.val p - linearProjection θ.val p = 0 := by ring
        rw [h_sub] <;> norm_num
      have h3 : ∫⁻ (θ : Sphere d), g_uncurry ((p, q), θ) ∂σ = ENNReal.ofReal (2 * ε) := by
        have h31 : ∫⁻ (θ : Sphere d), g_uncurry ((p, q), θ) ∂σ =
            ∫⁻ (θ : Sphere d), ENNReal.ofReal (2 * ε) ∂σ := by
          congr with θ
          exact h2 θ
        rw [h31, lintegral_const] <;> simp
      rw [h3]
      have hC_pos : 0 < C := by
        dsimp only [C, marstrandSphereConstant]
        have h_d_pos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (show 0 < d from by linarith)
        positivity
      have h_dist : dist p q = 0 := by
        have h4 : dist p q = dist p p := by rw [h]
        rw [h4, dist_self]
      have h_max : max (dist p q) ε = ε := by
        rw [h_dist]
        have h5 : max (0 : ℝ) ε = ε := by
          rw [max_eq_right] <;> linarith
        exact h5
      have h_goal : ENNReal.ofReal (2 * ε) ≤
          ENNReal.ofReal (C * ε^2 * (max (dist p q) ε)^(-1 : ℝ)) := by
        rw [h_max]
        have h7 : (ε : ℝ)^(-1 : ℝ) = ε⁻¹ := by
          have h8 : (ε : ℝ)^(-1 : ℝ) = ((ε : ℝ)^(1 : ℝ))⁻¹ := by
            rw [Real.rpow_neg (by linarith)] <;> norm_num
          rw [h8] <;> simp
        have h6 : C * ε^2 * (ε : ℝ)^(-1 : ℝ) = C * ε := by
          rw [h7]
          field_simp [hε.ne'] <;> ring
        rw [h6]
        have h8 : 2 ≤ C := by
          dsimp only [C, marstrandSphereConstant]
          have h9 : (d : ℝ) ≥ 2 := by exact_mod_cast (show 2 ≤ d from by linarith)
          have h10 : 0 < Real.pi := Real.pi_pos
          calc
            2 ≤ 8 * Real.pi := by linarith [Real.pi_gt_three]
            _ = 4 * (2 : ℝ) * Real.pi := by ring
            _ ≤ 4 * (d : ℝ) * Real.pi := by gcongr
        have h10 : 2 * ε ≤ C * ε := by
          have h11 : 0 < ε := hε
          nlinarith
        exact ENNReal.ofReal_le_ofReal h10
      exact h_goal
    · -- Case p ≠ q
      have hpos : 0 < dist p q := by
        rw [dist_pos] <;> exact h
      set r : ℝ := dist p q with hr
      set v : E := r⁻¹ • (p - q) with hv
      have h1 : ‖p - q‖ = r := by
        have h_dist : dist p q = ‖p - q‖ := dist_eq_norm p q
        exact h_dist.symm
      have hv_norm : ‖v‖ = 1 := by
        rw [hv, norm_smul]
        have h_rinv_pos : 0 < r⁻¹ := by positivity
        have h_norm_rinv : ‖r⁻¹‖ = r⁻¹ := by
          simpa [Real.norm_eq_abs] using abs_of_pos h_rinv_pos
        rw [h_norm_rinv, h1]
        <;> field_simp [hpos.ne'] <;> norm_num
      have h9 : (p - q) = r • v := by
        rw [hv]
        have h_smul : r • (r⁻¹ • (p - q)) = (r * r⁻¹) • (p - q) := by exact smul_smul r r⁻¹ (p - q)
        rw [h_smul]
        have h12 : r * r⁻¹ = 1 := by field_simp [hpos.ne']
        rw [h12] <;> simp
      have hproj : ∀ (θ : Sphere d),
          linearProjection θ.val (p - q) = r * linearProjection θ.val v := by
        intro θ
        dsimp only [linearProjection]
        calc
          inner ℝ θ.val (p - q)
            = inner ℝ θ.val (r • v) := by rw [h9]
          _ = r * inner ℝ θ.val v := by
              rw [inner_smul_right] <;> ring
      have h4 : ∫⁻ (θ : Sphere d), g_uncurry ((p, q), θ) ∂σ =
          ∫⁻ (θ : Sphere d), ENNReal.ofReal (max 0 (2 * ε - r * |linearProjection θ.val v|)) ∂σ := by
        congr with θ
        have h_eq1 : g_uncurry ((p, q), θ) = ENNReal.ofReal (max 0 (2 * ε - |linearProjection θ.val p - linearProjection θ.val q|)) := h_g_eq p q θ
        rw [h_eq1]
        have h5 : |linearProjection θ.val p - linearProjection θ.val q| =
            |linearProjection θ.val (p - q)| := by
          have h6 : inner ℝ θ.val (p - q) = inner ℝ θ.val p - inner ℝ θ.val q := by
            rw [inner_sub_right]
          have h7 : linearProjection θ.val p - linearProjection θ.val q = linearProjection θ.val (p - q) := by
            simpa [linearProjection] using h6.symm
          rw [h7]
        rw [h5]
        have h8 : |linearProjection θ.val (p - q)| = r * |linearProjection θ.val v| := by
          rw [hproj θ, abs_mul]
          have h_abs_r : |r| = r := abs_of_pos hpos
          rw [h_abs_r] <;> ring
        rw [h8] <;> rfl
      rw [h4]
      have h5 := spherical_geometric_bound hd hpos hε v hv_norm
      have h_max_pos : 0 < max r ε := by positivity
      have h6 : C * ε^2 / max r ε = C * ε^2 * (max r ε)^(-1 : ℝ) := by
        have h_pos : 0 < max r ε := by positivity
        have h7 : (max r ε)^(-1 : ℝ) = (max r ε)⁻¹ := by
          have h_ne : (max r ε) ≠ 0 := h_max_pos.ne'
          exact Real.rpow_neg_one (max r ε)
        rw [h7] <;> ring
      rw [h6] at h5
      exact h5
  have hC_pos : 0 < C := by
    dsimp only [C, marstrandSphereConstant]
    have h_d_pos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (show 0 < d from by linarith)
    exact mul_pos (mul_pos (by positivity) h_d_pos) Real.pi_pos
  have h_avg_L : ∫⁻ (θ : Sphere d), L θ ∂σ ≤
      ENNReal.ofReal (C * ε^2) * robust_projection_main.rieszEnergy (α := 1) (hδ := hε) μ := by
    rw [h_swap]
    have h7 : ∫⁻ (p : _), ∫⁻ (q : _), ∫⁻ (θ : _), g_uncurry ((p, q), θ) ∂σ ∂μ ∂μ ≤
        ∫⁻ (p : _), ∫⁻ (q : _), ENNReal.ofReal (C * ε^2 * (max (dist p q) ε)^(-1 : ℝ)) ∂μ ∂μ := by
      gcongr with p q
      exact h_spherical_uniform p q
    have h9 : ∀ (p q : E), ENNReal.ofReal (C * ε^2 * (max (dist p q) ε)^(-1 : ℝ)) =
        ENNReal.ofReal (C * ε^2) * ENNReal.ofReal ((max (dist p q) ε)^(-1 : ℝ)) := by
      intro p q
      have h_pos1 : 0 ≤ C * ε^2 := by positivity
      have h_pos2 : 0 ≤ (max (dist p q) ε)^(-1 : ℝ) := by positivity
      rw [← ENNReal.ofReal_mul h_pos1] <;> rfl
    have h8 : ∫⁻ (p : _), ∫⁻ (q : _), ENNReal.ofReal (C * ε^2) * ENNReal.ofReal ((max (dist p q) ε)^(-1 : ℝ)) ∂μ ∂μ =
        ENNReal.ofReal (C * ε^2) * robust_projection_main.rieszEnergy (α := 1) (hδ := hε) μ := by
      have h_meas : Measurable (Function.uncurry (fun (p : E) (q : E) => ENNReal.ofReal ((max (dist p q) ε)^(-1 : ℝ)))) := by fun_prop
      have h1 : ∫⁻ (p : E), ∫⁻ (q : E), ENNReal.ofReal (C * ε^2) * ENNReal.ofReal ((max (dist p q) ε)^(-1 : ℝ)) ∂μ ∂μ =
          ∫⁻ (p : E), ENNReal.ofReal (C * ε^2) * ∫⁻ (q : E), ENNReal.ofReal ((max (dist p q) ε)^(-1 : ℝ)) ∂μ ∂μ := by
        congr with p
        have h2 : Measurable (fun q : E => ENNReal.ofReal ((max (dist p q) ε)^(-1 : ℝ))) := by fun_prop
        rw [lintegral_const_mul] <;> exact h2
      rw [h1]
      have h3 : Measurable (fun p : E => ∫⁻ (q : E), ENNReal.ofReal ((max (dist p q) ε)^(-1 : ℝ)) ∂μ) :=
        Measurable.lintegral_prod_right h_meas
      exact lintegral_const_mul (ENNReal.ofReal (C * ε^2)) h3
    have h91 : ∫⁻ (p : _), ∫⁻ (q : _), ∫⁻ (θ : _), g_uncurry ((p, q), θ) ∂σ ∂μ ∂μ ≤
        ∫⁻ (p : _), ∫⁻ (q : _), ENNReal.ofReal (C * ε^2 * (max (dist p q) ε)^(-1 : ℝ)) ∂μ ∂μ := h7
    have h92 : ∫⁻ (p : _), ∫⁻ (q : _), ENNReal.ofReal (C * ε^2 * (max (dist p q) ε)^(-1 : ℝ)) ∂μ ∂μ =
        ∫⁻ (p : _), ∫⁻ (q : _), ENNReal.ofReal (C * ε^2) * ENNReal.ofReal ((max (dist p q) ε)^(-1 : ℝ)) ∂μ ∂μ := by
      apply lintegral_congr
      intro p
      apply lintegral_congr
      intro q
      exact h9 p q
    have h93 : ∫⁻ (p : _), ∫⁻ (q : _), ENNReal.ofReal (C * ε^2) * ENNReal.ofReal ((max (dist p q) ε)^(-1 : ℝ)) ∂μ ∂μ =
        ENNReal.ofReal (C * ε^2) * robust_projection_main.rieszEnergy (α := 1) (hδ := hε) μ := h8
    have h94 : ∫⁻ (p : _), ∫⁻ (q : _), ∫⁻ (θ : _), g_uncurry ((p, q), θ) ∂σ ∂μ ∂μ ≤
        ENNReal.ofReal (C * ε^2) * robust_projection_main.rieszEnergy (α := 1) (hδ := hε) μ := by
      calc
        _ ≤ _ := h91
        _ = _ := h92
        _ = _ := h93
    exact h94
  have h_avg_L2 : ∫⁻ (θ : Sphere d), L θ ∂σ ≤ ENNReal.ofReal (C * ε^2 * B) := by
    calc ∫⁻ (θ : Sphere d), L θ ∂σ
      ≤ ENNReal.ofReal (C * ε^2) * robust_projection_main.rieszEnergy (α := 1) (hδ := hε) μ := h_avg_L
    _ ≤ ENNReal.ofReal (C * ε^2) * ENNReal.ofReal B := by
      exact mul_le_mul_of_nonneg_left hI (by positivity)
    _ = ENNReal.ofReal (C * ε^2 * B) := by
      have h_pos : 0 ≤ C * ε^2 := by positivity
      rw [← ENNReal.ofReal_mul h_pos] <;> ring
  let K : ENNReal := ENNReal.ofReal (1 / (4 * C * B))
  have hC_pos : 0 < C := by
    dsimp only [C, marstrandSphereConstant]
    have h_d_pos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (show 0 < d from by linarith)
    exact mul_pos (mul_pos (by positivity) h_d_pos) Real.pi_pos
  have hK_pos : 0 < K := by positivity
  have hK_lt_top : K ≠ ⊤ := ENNReal.ofReal_ne_top
  by_contra h_no
  push Not at h_no
  have h_all_le : ∀ θ, V θ ≤ K := by
    intro θ
    have h_lt : V θ < K := h_no θ
    exact le_of_lt h_lt
  have h_all_L_ge : ∀ θ, L θ ≥ ENNReal.ofReal (16 * C * B * ε^2) := by
    intro θ
    have h1 : ENNReal.ofReal (4 * ε^2) ≤ V θ * L θ := h_cs θ
    have hV_pos : 0 < V θ := by
      by_contra h2
      have hV0 : V θ = 0 := by
        have h2' : V θ ≤ 0 := by simpa using h2
        simpa using h2'
      rw [hV0, zero_mul] at h1
      have h_pos : 0 < ENNReal.ofReal (4 * ε^2) := by positivity
      exact not_le.mpr h_pos h1
    have hV_lt_top : V θ ≠ ⊤ := by
      intro h3
      have h4 : V θ ≤ K := h_all_le θ
      rw [h3] at h4
      simp at h4 <;> exact hK_lt_top h4
    have h2 : L θ ≥ ENNReal.ofReal (4 * ε^2) / V θ := by
      have h_pos : V θ ≠ 0 := hV_pos.ne'
      have h_top : V θ ≠ ⊤ := hV_lt_top
      have h : ENNReal.ofReal (4 * ε^2) * (V θ)⁻¹ ≤ L θ := by
        calc ENNReal.ofReal (4 * ε^2) * (V θ)⁻¹
          ≤ (V θ * L θ) * (V θ)⁻¹ := by gcongr
        _ = V θ * (V θ)⁻¹ * L θ := by
          rw [mul_assoc, mul_comm (L θ) ((V θ)⁻¹), ←mul_assoc]
        _ = 1 * L θ := by rw [ENNReal.mul_inv_cancel h_pos h_top]
        _ = L θ := by simp
      simpa [div_eq_mul_inv] using h
    have h3 : ENNReal.ofReal (4 * ε^2) / V θ ≥ ENNReal.ofReal (4 * ε^2) / K := by
      have h_inv : (V θ)⁻¹ ≥ K⁻¹ := by exact ENNReal.inv_le_inv.mpr (h_all_le θ)
      have h_mul : ENNReal.ofReal (4 * ε^2) * (V θ)⁻¹ ≥ ENNReal.ofReal (4 * ε^2) * K⁻¹ := by gcongr
      have h_div1 : ENNReal.ofReal (4 * ε^2) / V θ = ENNReal.ofReal (4 * ε^2) * (V θ)⁻¹ := by
        rfl
      have h_div2 : ENNReal.ofReal (4 * ε^2) / K = ENNReal.ofReal (4 * ε^2) * K⁻¹ := by
        rfl
      rw [h_div1, h_div2]
      exact h_mul
    have h4 : L θ ≥ ENNReal.ofReal (4 * ε^2) / K := le_trans h3 h2
    have h_pos1 : 0 < 4 * ε^2 := by positivity
    have h_pos2 : 0 < 1 / (4 * C * B) := by positivity
    have hK_eq : K = ENNReal.ofReal (1 / (4 * C * B)) := by rfl
    have h5 : ENNReal.ofReal (4 * ε^2) / K = ENNReal.ofReal (16 * C * B * ε^2) := by
      rw [hK_eq]
      have h_div : ENNReal.ofReal (4 * ε^2) / ENNReal.ofReal (1 / (4 * C * B)) =
          ENNReal.ofReal ((4 * ε^2) / (1 / (4 * C * B))) := by
        rw [ENNReal.ofReal_div_of_pos h_pos2] <;> rfl
      rw [h_div]
      have h_eq : (4 * ε^2) / (1 / (4 * C * B)) = 16 * C * B * ε^2 := by
        field_simp [hC_pos.ne', hB.ne'] <;> ring
      rw [h_eq]
    rw [h5] at h4
    exact h4
  have h_avg_ge : ∫⁻ (θ : Sphere d), L θ ∂σ ≥ ENNReal.ofReal (16 * C * B * ε^2) := by
    have h6 : ∫⁻ (θ : Sphere d), L θ ∂σ ≥ ∫⁻ (θ : Sphere d), ENNReal.ofReal (16 * C * B * ε^2) ∂σ :=
      lintegral_mono h_all_L_ge
    rw [lintegral_const] at h6
    simpa using h6
  have h_contra : ENNReal.ofReal (16 * C * B * ε^2) ≤ ENNReal.ofReal (C * ε^2 * B) :=
    le_trans h_avg_ge h_avg_L2
  have h7 : 16 * C * B * ε^2 > C * ε^2 * B := by
    have h8 : 0 < C * B * ε^2 := by positivity
    nlinarith
  have h9 : ¬ ENNReal.ofReal (16 * C * B * ε^2) ≤ ENNReal.ofReal (C * ε^2 * B) := by
    intro h_le
    have h10 : 16 * C * B * ε^2 ≤ C * ε^2 * B := by
      have h11 : 0 ≤ C * ε^2 * B := by positivity
      have h12 : 0 ≤ 16 * C * B * ε^2 := by positivity
      exact (ofReal_le_ofReal_iff h11).mp h_contra
    have h13 : 0 < C * B * ε^2 := by positivity
    nlinarith
  exact h9 h_contra

/-! ## Covering number corollary -/

/-- **Covering-number extraction from Marstrand.** -/
theorem marstrand_covering_extraction {d : ℕ} (hd : 2 ≤ d)
    {δ B : ℝ} (hδ : 0 < δ) (hB : 0 < B)
    (μ : Measure (EuclideanSpace ℝ (Fin d)))
    [IsProbabilityMeasure μ]
    (A : Set (EuclideanSpace ℝ (Fin d)))
    (hA_supp : μ.support ⊆ A)
    (hI : robust_projection_main.rieszEnergy (α := 1) (hδ := hδ) μ ≤ ENNReal.ofReal B) :
    ∃ (θ : Sphere d),
      ENNReal.ofReal (1 / (12 * marstrandSphereConstant d * B * δ)) ≤
        Nreal δ (linearProjection θ.val '' A) := by
  let C := marstrandSphereConstant d
  have h_main := marstrand_projection_lower_bound hd hδ hB μ hI
  rcases h_main with ⟨θ, hV⟩
  have h1 : projectionNeighborhood δ θ.val μ.support ⊆ projectionNeighborhood δ θ.val A := by
    intro t ht
    rcases ht with ⟨p, hp, hdist⟩
    exact ⟨p, hA_supp hp, hdist⟩
  have h2 : volume (projectionNeighborhood δ θ.val A) ≥ ENNReal.ofReal (1 / (4 * C * B)) := by
    calc volume (projectionNeighborhood δ θ.val A)
      ≥ volume (projectionNeighborhood δ θ.val μ.support) := measure_mono h1
    _ ≥ ENNReal.ofReal (1 / (4 * C * B)) := hV
  let S : Set ℝ := linearProjection θ.val '' A
  have h3 : projectionNeighborhood δ θ.val A = {t | ∃ s ∈ S, |s - t| < δ} := by
    ext t
    simp only [projectionNeighborhood, S, Set.mem_image, Set.mem_setOf_eq]
    constructor
    · rintro ⟨p, hp, hdist⟩
      exact ⟨linearProjection θ.val p, ⟨p, hp, rfl⟩, hdist⟩
    · rintro ⟨s, ⟨p, hp, rfl⟩, hdist⟩
      exact ⟨p, hp, hdist⟩
  rw [h3] at h2
  have h_set_eq : {t : ℝ | ∃ s ∈ S, |s - t| < δ} = {t : ℝ | ∃ x ∈ S, |t - x| < δ} := by
    ext t
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨s, hs, h⟩
      have h' : |t - s| < δ := by
        rw [show t - s = -(s - t) by ring, abs_neg] <;> exact h
      exact ⟨s, hs, h'⟩
    · rintro ⟨x, hx, h⟩
      have h' : |x - t| < δ := by
        rw [show x - t = -(t - x) by ring, abs_neg] <;> exact h
      exact ⟨x, hx, h'⟩
  rw [h_set_eq] at h2
  have h4 : volume {t | ∃ x ∈ S, |t - x| < δ} ≤ 3 * ENNReal.ofReal δ * Nreal δ S :=
    WeakTwoEndsSumProduct.neighborhood_volume_le_covering hδ
  have h5 : ENNReal.ofReal (1 / (4 * C * B)) ≤ 3 * ENNReal.ofReal δ * Nreal δ S :=
    le_trans h2 h4
  have h6 : (3 : ENNReal) * ENNReal.ofReal δ ≠ 0 := by positivity
  have h7 : (3 : ENNReal) * ENNReal.ofReal δ ≠ ⊤ :=
    ENNReal.mul_ne_top (by simp) (by simp)
  have hC_pos : 0 < C := by
    dsimp only [C, marstrandSphereConstant]
    have h_d_pos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (show 0 < d from by linarith)
    exact mul_pos (mul_pos (by positivity) h_d_pos) Real.pi_pos
  have h9 : (3 : ENNReal) * ENNReal.ofReal δ * ENNReal.ofReal (1 / (12 * C * B * δ)) =
      ENNReal.ofReal (1 / (4 * C * B)) := by
    have h10 : (3 : ENNReal) = ENNReal.ofReal 3 := by simp
    rw [h10]
    have h11 : ENNReal.ofReal 3 * ENNReal.ofReal δ * ENNReal.ofReal (1 / (12 * C * B * δ)) =
        ENNReal.ofReal (3 * δ * (1 / (12 * C * B * δ))) := by
      rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
      <;> ring
    rw [h11]
    have h12 : 3 * δ * (1 / (12 * C * B * δ)) = 1 / (4 * C * B) := by
      field_simp [hδ.ne', hC_pos.ne', hB.ne'] <;> ring
    rw [h12]
  have h10 : (3 : ENNReal) * ENNReal.ofReal δ * ENNReal.ofReal (1 / (12 * C * B * δ)) ≤
      (3 : ENNReal) * ENNReal.ofReal δ * Nreal δ S := by
    rw [h9] <;> exact h5
  have h11 : ENNReal.ofReal (1 / (12 * C * B * δ)) ≤ Nreal δ S :=
    (ENNReal.mul_le_mul_iff_right h6 h7).mp h10
  exact ⟨θ, h11⟩

/-! ## Average L² projection bound (extracted) -/

/-- Average over the unit sphere of the L² norm of projection balls.
This is the key energy estimate behind Marstrand's projection theorem. -/
lemma marstrand_average_L2 {d : ℕ} (hd : 2 ≤ d)
    {ε : ℝ} (hε : 0 < ε)
    (μ : Measure (EuclideanSpace ℝ (Fin d)))
    [IsProbabilityMeasure μ] :
    ∫⁻ (θ : Sphere d), (∫⁻ (t : ℝ), (projBallArb ε θ.val μ t)^2 ∂volume) ∂sphereProbabilityMeasure d ≤
    ENNReal.ofReal (marstrandSphereConstant d * ε^2) *
      robust_projection_main.rieszEnergy (α := 1) (hδ := hε) μ := by
  let σ : Measure (Sphere d) := sphereProbabilityMeasure d
  haveI : IsProbabilityMeasure σ := sphereProbabilityMeasure_isProbability (by linarith)
  let C := marstrandSphereConstant d
  let L : Sphere d → ENNReal := fun θ =>
    ∫⁻ (t : ℝ), (projBallArb ε θ.val μ t)^2 ∂volume
  have h_fubini : ∀ θ, L θ = ∫⁻ (p : _), ∫⁻ (q : _),
      ENNReal.ofReal (max 0 (2 * ε - |linearProjection θ.val p - linearProjection θ.val q|))
      ∂μ ∂μ := by
    intro θ; exact fubini_expansion_arb hε μ θ.val
  let E := EuclideanSpace ℝ (Fin d)
  let g_uncurry : (E × E) × Sphere d → ENNReal := fun x =>
    ENNReal.ofReal (max 0 (2 * ε - |inner ℝ x.2.val x.1.1 - inner ℝ x.2.val x.1.2|))
  have h11 : Continuous (fun x : (E × E) × Sphere d => (x.2.val, x.1.1)) := by fun_prop
  have h12 : Continuous (fun x : (E × E) × Sphere d => (x.2.val, x.1.2)) := by fun_prop
  let f3 : (E × E) × Sphere d → ℝ := fun x => inner ℝ x.2.val x.1.1
  let f4 : (E × E) × Sphere d → ℝ := fun x => inner ℝ x.2.val x.1.2
  have h3 : Continuous f3 := by
    have h : Continuous (fun p : E × E => inner ℝ p.1 p.2) := continuous_inner
    exact h.comp h11
  have h4 : Continuous f4 := by
    have h : Continuous (fun p : E × E => inner ℝ p.1 p.2) := continuous_inner
    exact h.comp h12
  have h5 : Continuous (fun x : (E × E) × Sphere d => max 0 (2 * ε - |f3 x - f4 x|)) := by
    have h_sub : Continuous (fun x => f3 x - f4 x) := h3.sub h4
    have h_abs : Continuous (fun x => |f3 x - f4 x|) := h_sub.abs
    have h_neg : Continuous (fun x => (2 * ε : ℝ) - |f3 x - f4 x|) := continuous_const.sub h_abs
    exact continuous_const.max h_neg
  have h_g_cont : Continuous g_uncurry := (continuous_ofReal).comp h5
  have h_g_meas : Measurable g_uncurry := h_g_cont.measurable
  have h_g_eq : ∀ (p : E) (q : E) (θ : Sphere d),
      g_uncurry ((p, q), θ) = ENNReal.ofReal (max 0 (2 * ε - |linearProjection θ.val p - linearProjection θ.val q|)) := by
    intro p q θ; simp [g_uncurry, linearProjection] <;> rfl
  let reindex1 : ((Sphere d × E) × E) → (E × E) × Sphere d := fun x => ((x.1.2, x.2), x.1.1)
  have h_reindex1_cont : Continuous reindex1 := by fun_prop
  have h1_meas : Measurable (fun x : ((Sphere d × E) × E) => g_uncurry (reindex1 x)) :=
    h_g_meas.comp h_reindex1_cont.measurable
  have h_f1_meas : Measurable (fun y : Sphere d × E => ∫⁻ (q : E), g_uncurry (reindex1 (y, q)) ∂μ) :=
    Measurable.lintegral_prod_right h1_meas
  have h_swap1 : ∫⁻ (θ : Sphere d), ∫⁻ (p : E), (∫⁻ (q : E), g_uncurry ((p, q), θ) ∂μ) ∂μ ∂σ =
      ∫⁻ (p : E), ∫⁻ (θ : Sphere d), (∫⁻ (q : E), g_uncurry ((p, q), θ) ∂μ) ∂σ ∂μ :=
    lintegral_lintegral_swap h_f1_meas.aemeasurable
  have h_swap2 : ∀ (p : E),
      ∫⁻ (θ : Sphere d), ∫⁻ (q : E), g_uncurry ((p, q), θ) ∂μ ∂σ =
      ∫⁻ (q : E), ∫⁻ (θ : Sphere d), g_uncurry ((p, q), θ) ∂σ ∂μ := by
    intro p
    have h2_meas : Measurable (Function.uncurry fun (θ : Sphere d) (q : E) => g_uncurry ((p, q), θ)) := by
      have h_map : Continuous (fun x : Sphere d × E => ((p, x.snd), x.fst)) := by fun_prop
      exact h_g_meas.comp h_map.measurable
    exact lintegral_lintegral_swap (hf := h2_meas.aemeasurable)
  have h_swap : ∫⁻ (θ : Sphere d), L θ ∂σ =
      ∫⁻ (p : E), ∫⁻ (q : E), ∫⁻ (θ : Sphere d), g_uncurry ((p, q), θ) ∂σ ∂μ ∂μ := by
    have h1 : ∫⁻ (θ : Sphere d), L θ ∂σ =
        ∫⁻ (θ : Sphere d), ∫⁻ (p : E), ∫⁻ (q : E), g_uncurry ((p, q), θ) ∂μ ∂μ ∂σ := by
      congr with θ; exact h_fubini θ
    rw [h1, h_swap1]; congr with p; exact h_swap2 p
  have h_spherical_uniform : ∀ (p q : E),
      ∫⁻ (θ : Sphere d), g_uncurry ((p, q), θ) ∂σ ≤
      ENNReal.ofReal (C * ε^2 * (max (dist p q) ε)^(-1 : ℝ)) := by
    intro p q
    by_cases h : p = q
    · have hq : q = p := h.symm
      have h2 : ∀ θ, g_uncurry ((p, q), θ) = ENNReal.ofReal (2 * ε) := by
        intro θ; rw [hq]
        have h_eq : g_uncurry ((p, p), θ) = ENNReal.ofReal (max 0 (2 * ε - |linearProjection θ.val p - linearProjection θ.val p|)) := h_g_eq p p θ
        rw [h_eq]; have h_sub : linearProjection θ.val p - linearProjection θ.val p = 0 := by ring
        rw [h_sub] <;> norm_num
      have h3 : ∫⁻ (θ : Sphere d), g_uncurry ((p, q), θ) ∂σ = ENNReal.ofReal (2 * ε) := by
        have h31 : ∫⁻ (θ : Sphere d), g_uncurry ((p, q), θ) ∂σ = ∫⁻ (θ : Sphere d), ENNReal.ofReal (2 * ε) ∂σ := by
          congr with θ; exact h2 θ
        rw [h31, lintegral_const] <;> simp
      rw [h3]
      have hC_pos : 0 < C := by
        dsimp only [C, marstrandSphereConstant]
        have h_d_pos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (show 0 < d from by linarith)
        exact mul_pos (mul_pos (by positivity) h_d_pos) Real.pi_pos
      have h_dist : dist p q = 0 := by rw [h, dist_self]
      have h_max : max (dist p q) ε = ε := by
        rw [h_dist]
        have h5 : max (0 : ℝ) ε = ε := by
          rw [max_eq_right] <;> linarith
        exact h5
      rw [h_max]
      have h7 : (ε : ℝ)^(-1 : ℝ) = ε⁻¹ := by
        have h8 : (ε : ℝ)^(-1 : ℝ) = ((ε : ℝ)^(1 : ℝ))⁻¹ := by rw [Real.rpow_neg (by linarith)] <;> norm_num
        rw [h8] <;> simp
      have h6 : C * ε^2 * (ε : ℝ)^(-1 : ℝ) = C * ε := by rw [h7]; field_simp [hε.ne'] <;> ring
      rw [h6]
      have h8 : 2 ≤ C := by
        dsimp only [C, marstrandSphereConstant]
        have h9 : (d : ℝ) ≥ 2 := by exact_mod_cast (show 2 ≤ d from by linarith)
        have h10 : 0 < Real.pi := Real.pi_pos
        calc 2 ≤ 8 * Real.pi := by linarith [Real.pi_gt_three]
          _ = 4 * (2 : ℝ) * Real.pi := by ring
          _ ≤ 4 * (d : ℝ) * Real.pi := by gcongr
      have h10 : 2 * ε ≤ C * ε := by have h11 : 0 < ε := hε; nlinarith
      exact ENNReal.ofReal_le_ofReal h10
    · have hpos : 0 < dist p q := by rw [dist_pos] <;> exact h
      set r : ℝ := dist p q with hr
      set v : E := r⁻¹ • (p - q) with hv
      have h1 : ‖p - q‖ = r := by have h_dist : dist p q = ‖p - q‖ := dist_eq_norm p q; exact h_dist.symm
      have hv_norm : ‖v‖ = 1 := by
        rw [hv, norm_smul]; have h_rinv_pos : 0 < r⁻¹ := by positivity
        have h_norm_rinv : ‖r⁻¹‖ = r⁻¹ := by simpa [Real.norm_eq_abs] using abs_of_pos h_rinv_pos
        rw [h_norm_rinv, h1] <;> field_simp [hpos.ne'] <;> norm_num
      have h9 : (p - q) = r • v := by
        rw [hv]
        have h_smul : r • (r⁻¹ • (p - q)) = (r * r⁻¹) • (p - q) := by
          rw [smul_smul]
        rw [h_smul]
        have h12 : r * r⁻¹ = 1 := by field_simp [hpos.ne']
        rw [h12] <;> simp
      have hproj : ∀ (θ : Sphere d), linearProjection θ.val (p - q) = r * linearProjection θ.val v := by
        intro θ; dsimp only [linearProjection]
        calc inner ℝ θ.val (p - q) = inner ℝ θ.val (r • v) := by rw [h9]
          _ = r * inner ℝ θ.val v := by rw [inner_smul_right] <;> ring
      have h4 : ∫⁻ (θ : Sphere d), g_uncurry ((p, q), θ) ∂σ =
          ∫⁻ (θ : Sphere d), ENNReal.ofReal (max 0 (2 * ε - r * |linearProjection θ.val v|)) ∂σ := by
        congr with θ
        have h_eq1 : g_uncurry ((p, q), θ) = ENNReal.ofReal (max 0 (2 * ε - |linearProjection θ.val p - linearProjection θ.val q|)) := h_g_eq p q θ
        rw [h_eq1]
        have h5 : |linearProjection θ.val p - linearProjection θ.val q| = |linearProjection θ.val (p - q)| := by
          have h6 : inner ℝ θ.val (p - q) = inner ℝ θ.val p - inner ℝ θ.val q := by rw [inner_sub_right]
          have h7 : linearProjection θ.val p - linearProjection θ.val q = linearProjection θ.val (p - q) := by
            simpa [linearProjection] using h6.symm
          rw [h7]
        rw [h5]
        have h8 : |linearProjection θ.val (p - q)| = r * |linearProjection θ.val v| := by
          rw [hproj θ, abs_mul]; have h_abs_r : |r| = r := abs_of_pos hpos
          rw [h_abs_r] <;> ring
        rw [h8] <;> rfl
      rw [h4]
      have h5 := spherical_geometric_bound hd hpos hε v hv_norm
      have h_max_pos : 0 < max r ε := by positivity
      have h6 : C * ε^2 / max r ε = C * ε^2 * (max r ε)^(-1 : ℝ) := by
        have h_pos : 0 < max r ε := by positivity
        have h7 : (max r ε)^(-1 : ℝ) = (max r ε)⁻¹ := by have h_ne : (max r ε) ≠ 0 := h_max_pos.ne'; exact Real.rpow_neg_one (max r ε)
        rw [h7] <;> ring
      rw [h6] at h5; exact h5
  have hC_pos : 0 < C := by
    dsimp only [C, marstrandSphereConstant]
    have h_d_pos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (show 0 < d from by linarith)
    exact mul_pos (mul_pos (by positivity) h_d_pos) Real.pi_pos
  rw [h_swap]
  have h7 : ∫⁻ (p : _), ∫⁻ (q : _), ∫⁻ (θ : _), g_uncurry ((p, q), θ) ∂σ ∂μ ∂μ ≤
      ∫⁻ (p : _), ∫⁻ (q : _), ENNReal.ofReal (C * ε^2 * (max (dist p q) ε)^(-1 : ℝ)) ∂μ ∂μ := by
    gcongr with p q; exact h_spherical_uniform p q
  have h9 : ∀ (p q : E), ENNReal.ofReal (C * ε^2 * (max (dist p q) ε)^(-1 : ℝ)) =
      ENNReal.ofReal (C * ε^2) * ENNReal.ofReal ((max (dist p q) ε)^(-1 : ℝ)) := by
    intro p q
    have h_pos1 : 0 ≤ C * ε^2 := by positivity
    have h_pos2 : 0 ≤ (max (dist p q) ε)^(-1 : ℝ) := by positivity
    rw [← ENNReal.ofReal_mul h_pos1] <;> rfl
  have h8 : ∫⁻ (p : _), ∫⁻ (q : _), ENNReal.ofReal (C * ε^2) * ENNReal.ofReal ((max (dist p q) ε)^(-1 : ℝ)) ∂μ ∂μ =
      ENNReal.ofReal (C * ε^2) * robust_projection_main.rieszEnergy (α := 1) (hδ := hε) μ := by
    have h_meas : Measurable (Function.uncurry (fun (p : E) (q : E) => ENNReal.ofReal ((max (dist p q) ε)^(-1 : ℝ)))) := by fun_prop
    have h1 : ∫⁻ (p : E), ∫⁻ (q : E), ENNReal.ofReal (C * ε^2) * ENNReal.ofReal ((max (dist p q) ε)^(-1 : ℝ)) ∂μ ∂μ =
        ∫⁻ (p : E), ENNReal.ofReal (C * ε^2) * ∫⁻ (q : E), ENNReal.ofReal ((max (dist p q) ε)^(-1 : ℝ)) ∂μ ∂μ := by
      congr with p
      have h2 : Measurable (fun q : E => ENNReal.ofReal ((max (dist p q) ε)^(-1 : ℝ))) := by fun_prop
      rw [lintegral_const_mul] <;> exact h2
    rw [h1]
    have h3 : Measurable (fun p : E => ∫⁻ (q : E), ENNReal.ofReal ((max (dist p q) ε)^(-1 : ℝ)) ∂μ) :=
      Measurable.lintegral_prod_right h_meas
    exact lintegral_const_mul (ENNReal.ofReal (C * ε^2)) h3
  calc
    ∫⁻ (p : _), ∫⁻ (q : _), ∫⁻ (θ : _), g_uncurry ((p, q), θ) ∂σ ∂μ ∂μ
      ≤ ∫⁻ (p : _), ∫⁻ (q : _), ENNReal.ofReal (C * ε^2 * (max (dist p q) ε)^(-1 : ℝ)) ∂μ ∂μ := h7
    _ = ∫⁻ (p : _), ∫⁻ (q : _), ENNReal.ofReal (C * ε^2) * ENNReal.ofReal ((max (dist p q) ε)^(-1 : ℝ)) ∂μ ∂μ := by
      apply lintegral_congr; intro p; apply lintegral_congr; intro q; exact h9 p q
    _ = ENNReal.ofReal (C * ε^2) * robust_projection_main.rieszEnergy (α := 1) (hδ := hε) μ := h8

/-! ## Strict ratio cap for [1/2,1] weights -/

/-- Open spherical cap: all components strictly positive and within factor 2.
After normalization `v_i = θ_i / max_j θ_j`, every weight lies in `(1/2, 1)`. -/
def ratioCapOpen (n : ℕ) : Set (Sphere n) :=
  {θ | (∀ i, 0 < θ.val i) ∧ ∀ (i j : Fin n), θ.val i < 2 * θ.val j}

lemma ratioCapOpen_nonempty {n : ℕ} (hn : 0 < n) : (ratioCapOpen n).Nonempty := by
  let f : Fin n → ℝ := fun _ => 1 / Real.sqrt (n : ℝ)
  let u : EuclideanSpace ℝ (Fin n) := (EuclideanSpace.equiv (Fin n) ℝ).symm f
  have h_apply : ∀ (i : Fin n), u i = f i := by
    intro i
    have h_eq : (EuclideanSpace.equiv (Fin n) ℝ) u = f :=
      (EuclideanSpace.equiv (Fin n) ℝ).apply_symm_apply f
    exact congr_fun h_eq i
  have hu_norm : ‖u‖ = 1 := by
    rw [EuclideanSpace.norm_eq]
    have h_n_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have h : ∀ i : Fin n, ‖u i‖ ^ 2 = 1 / (n : ℝ) := by
      intro i
      have h3 : ‖u i‖ = 1 / Real.sqrt (n : ℝ) := by
        rw [h_apply i]
        dsimp only [f]
        rw [Real.norm_eq_abs]
        rw [abs_of_pos] <;> positivity
      rw [h3]
      have h4 : (1 / Real.sqrt (n : ℝ)) ^ 2 = 1 / (n : ℝ) := by
        have h5 : 0 < Real.sqrt (n : ℝ) := by positivity
        field_simp [h5.ne'] <;> nlinarith [Real.sq_sqrt (show 0 ≤ (n : ℝ) from by positivity)]
      exact h4
    have h_sum : ∑ i : Fin n, ‖u i‖ ^ 2 = 1 := by
      rw [Finset.sum_congr rfl (fun i _ => h i)]
      have h6 : ∑ i : Fin n, (1 / (n : ℝ)) = 1 := by
        have h7 : ∑ i : Fin n, (1 / (n : ℝ)) = (n : ℝ) * (1 / (n : ℝ)) := by
          simp [Finset.sum_const, Finset.card_fin]
          <;> ring
        rw [h7]
        field_simp [h_n_pos.ne'] <;> ring
      exact h6
    rw [h_sum]
    rw [Real.sqrt_one]
  let θ : Sphere n := ⟨u, by simpa [Metric.mem_sphere, dist_zero_right] using hu_norm⟩
  refine ⟨θ, ?_⟩
  have h_pos : ∀ i : Fin n, 0 < θ.val i := by
    intro i
    have h_eq : θ.val i = f i := h_apply i
    rw [h_eq]; dsimp only [f]; positivity
  have h_lt : ∀ (i j : Fin n), θ.val i < 2 * θ.val j := by
    intro i j
    have h_eq_i : θ.val i = f i := h_apply i
    have h_eq_j : θ.val j = f j := h_apply j
    rw [h_eq_i, h_eq_j]
    dsimp only [f]
    have h_n_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have h : 1 / Real.sqrt (n : ℝ) < 2 * (1 / Real.sqrt (n : ℝ)) := by
      have h_pos2 : 0 < 1 / Real.sqrt (n : ℝ) := by positivity
      linarith
    exact h
  exact ⟨h_pos, h_lt⟩

lemma ratioCapOpen_isOpen {n : ℕ} : IsOpen (ratioCapOpen n) := by
  have h1 : IsOpen {θ : Sphere n | ∀ i, 0 < θ.val i} := by
    have h : ∀ i : Fin n, IsOpen {θ : Sphere n | 0 < θ.val i} := by
      intro i
      have h_cont : Continuous (fun θ : Sphere n => θ.val i) := by fun_prop
      exact h_cont.isOpen_preimage (Set.Ioi 0) isOpen_Ioi
    have h_set : {θ : Sphere n | ∀ i, 0 < θ.val i} = ⋂ i : Fin n, {θ : Sphere n | 0 < θ.val i} := by
      ext x; simp
    rw [h_set]
    exact isOpen_iInter_of_finite h
  have h2 : IsOpen {θ : Sphere n | ∀ (i j : Fin n), θ.val i < 2 * θ.val j} := by
    have h : ∀ (i : Fin n), IsOpen {θ : Sphere n | ∀ (j : Fin n), θ.val i < 2 * θ.val j} := by
      intro i
      have h' : ∀ (j : Fin n), IsOpen {θ : Sphere n | θ.val i < 2 * θ.val j} := by
        intro j
        have h_cont : Continuous (fun θ : Sphere n => θ.val i - 2 * θ.val j) := by fun_prop
        have h_set_eq : {θ : Sphere n | θ.val i < 2 * θ.val j} = (fun θ : Sphere n => θ.val i - 2 * θ.val j) ⁻¹' (Set.Iio (0 : ℝ)) := by
          ext θ; simp [Set.mem_preimage]
        rw [h_set_eq]
        exact h_cont.isOpen_preimage (Set.Iio (0 : ℝ)) (by exact isOpen_Iio)
      have h_set : {θ : Sphere n | ∀ (j : Fin n), θ.val i < 2 * θ.val j} = ⋂ j : Fin n, {θ : Sphere n | θ.val i < 2 * θ.val j} := by
        ext x; simp
      rw [h_set]
      exact isOpen_iInter_of_finite h'
    have h_set : {θ : Sphere n | ∀ (i j : Fin n), θ.val i < 2 * θ.val j} = ⋂ i : Fin n, {θ : Sphere n | ∀ (j : Fin n), θ.val i < 2 * θ.val j} := by
      ext x; simp
    rw [h_set]
    exact isOpen_iInter_of_finite h
  exact h1.inter h2

lemma ratioCapOpen_positiveMeasure {n : ℕ} (hn : 0 < n) :
    0 < sphereProbabilityMeasure n (ratioCapOpen n) := by
  let vol : Measure (Sphere n) := volume.toSphere
  have h_open : IsOpen (ratioCapOpen n) := ratioCapOpen_isOpen
  have h_nonempty : (ratioCapOpen n).Nonempty := ratioCapOpen_nonempty hn
  have h_vol_pos : 0 < vol (ratioCapOpen n) := h_open.measure_pos vol h_nonempty
  have h_def : sphereProbabilityMeasure n (ratioCapOpen n) = (vol Set.univ)⁻¹ * vol (ratioCapOpen n) := by rfl
  rw [h_def]
  have h_ne_top : vol Set.univ ≠ ⊤ := MeasureTheory.measure_ne_top vol Set.univ
  have h_inv_pos : 0 < (vol Set.univ)⁻¹ := by
    simpa [ENNReal.inv_eq_zero] using h_ne_top
  have h1 : (vol Set.univ)⁻¹ ≠ 0 := h_inv_pos.ne'
  have h2 : vol (ratioCapOpen n) ≠ 0 := h_vol_pos.ne'
  have h3 : (vol Set.univ)⁻¹ * vol (ratioCapOpen n) ≠ 0 := mul_ne_zero h1 h2
  exact ENNReal.mul_pos h1 h2


/-! ## Cone-restricted Marstrand projection -/

/-- Fixed-ε cone lower bound: for any measurable U with positive spherical measure,
there exists θ ∈ U whose ε-neighborhood projection volume is at least
`σ(U) / (C_d * B)`. -/
theorem marstrand_cone_lower_bound {d : ℕ} (hd : 2 ≤ d)
    {ε B : ℝ} (hε : 0 < ε) (hB : 0 < B)
    (μ : Measure (EuclideanSpace ℝ (Fin d)))
    [IsProbabilityMeasure μ]
    (hI : robust_projection_main.rieszEnergy (α := 1) (hδ := hε) μ ≤ ENNReal.ofReal B)
    (U : Set (Sphere d)) (hU_meas : MeasurableSet U)
    (hU_pos : 0 < sphereProbabilityMeasure d U) :
    ∃ (θ : Sphere d), θ ∈ U ∧
      ENNReal.ofReal ((sphereProbabilityMeasure d U).toReal / (marstrandSphereConstant d * B)) ≤
      volume (projectionNeighborhood ε θ.val μ.support) := by
  let σ := sphereProbabilityMeasure d
  haveI : IsProbabilityMeasure σ := sphereProbabilityMeasure_isProbability (by linarith)
  let C := marstrandSphereConstant d
  let L : Sphere d → ENNReal := fun θ =>
    ∫⁻ (t : ℝ), (projBallArb ε θ.val μ t)^2 ∂volume
  let V : Sphere d → ENNReal := fun θ => volume (projectionNeighborhood ε θ.val μ.support)
  let α : ℝ := (σ U).toReal
  have hα_pos : 0 < α := by
    dsimp only [α]
    have h1 : σ U ≠ 0 := hU_pos.ne'
    have h2 : σ U ≠ ⊤ := by
      have h3 : σ U ≤ σ Set.univ := measure_mono (subset_univ U)
      have h4 : σ Set.univ = 1 := measure_univ
      rw [h4] at h3
      intro h5
      rw [h5] at h3
      simp at h3
    exact ENNReal.toReal_pos h1 h2
  have hC_pos : 0 < C := by
    dsimp only [C, marstrandSphereConstant]
    have h_d_pos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (show 0 < d from by linarith)
    exact mul_pos (mul_pos (by positivity) h_d_pos) Real.pi_pos
  let K : ENNReal := ENNReal.ofReal (α / (C * B))
  have hK_pos : 0 < K := by positivity
  have hK_ne_top : K ≠ ⊤ := ENNReal.ofReal_ne_top
  have h_cs : ∀ θ, ENNReal.ofReal (4 * ε^2) ≤ V θ * L θ := by
    intro θ; exact projection_neighborhood_cs hε μ θ.val
  have h_avg_L2 : ∫⁻ (θ : Sphere d), L θ ∂σ ≤ ENNReal.ofReal (C * ε^2 * B) := by
    have h1 := marstrand_average_L2 hd hε μ
    calc ∫⁻ (θ : Sphere d), L θ ∂σ
      ≤ ENNReal.ofReal (C * ε^2) * robust_projection_main.rieszEnergy (α := 1) (hδ := hε) μ := h1
    _ ≤ ENNReal.ofReal (C * ε^2) * ENNReal.ofReal B := by gcongr
    _ = ENNReal.ofReal (C * ε^2 * B) := by
      have h_pos : 0 ≤ C * ε^2 := by positivity
      rw [← ENNReal.ofReal_mul h_pos] <;> ring
  have hσU_eq : σ U = ENNReal.ofReal α := by
    have h1 : σ U ≠ ⊤ := by
      have h2 : σ U ≤ σ Set.univ := measure_mono (subset_univ U)
      have h3 : σ Set.univ = 1 := measure_univ
      rw [h3] at h2
      intro h4
      rw [h4] at h2
      simp at h2
    exact (ENNReal.ofReal_toReal h1).symm
  by_contra h_no; push Not at h_no
  have h_all_le : ∀ θ ∈ U, V θ ≤ K := by
    intro θ hθ; have h_lt : V θ < K := h_no θ hθ; exact le_of_lt h_lt
  have h_all_L_ge : ∀ θ ∈ U, L θ ≥ ENNReal.ofReal (4 * ε^2) / K := by
    intro θ hθ
    have h1 : ENNReal.ofReal (4 * ε^2) ≤ V θ * L θ := h_cs θ
    have hV_pos : 0 < V θ := by
      by_contra h2
      have hV0 : V θ = 0 := by
        have h2' : V θ ≤ 0 := by simpa using h2
        simpa using h2'
      rw [hV0, zero_mul] at h1
      have h_pos : 0 < ENNReal.ofReal (4 * ε^2) := by positivity
      exact not_le.mpr h_pos h1
    have hV_lt_top : V θ ≠ ⊤ := by
      intro h3
      have h4 : V θ ≤ K := h_all_le θ hθ
      rw [h3] at h4
      have h5 : K = ⊤ := by simpa using h4
      exact hK_ne_top h5
    have h2 : ENNReal.ofReal (4 * ε^2) / V θ ≤ L θ := by
      have h_div : ENNReal.ofReal (4 * ε^2) / V θ = ENNReal.ofReal (4 * ε^2) * (V θ)⁻¹ := by rfl
      rw [h_div]
      have h_mul : ENNReal.ofReal (4 * ε^2) * (V θ)⁻¹ ≤ (V θ * L θ) * (V θ)⁻¹ := by gcongr
      have h5 : (V θ * L θ) * (V θ)⁻¹ = L θ := by
        rw [mul_assoc, mul_comm (L θ) ((V θ)⁻¹), ←mul_assoc]
        have h6 : V θ * (V θ)⁻¹ = 1 := ENNReal.mul_inv_cancel hV_pos.ne' hV_lt_top
        rw [h6, one_mul]
      rw [h5] at h_mul
      exact h_mul
    have h3 : ENNReal.ofReal (4 * ε^2) / K ≤ ENNReal.ofReal (4 * ε^2) / V θ := by
      have h_inv : K⁻¹ ≤ (V θ)⁻¹ := ENNReal.inv_le_inv.mpr (h_all_le θ hθ)
      have h_mul : ENNReal.ofReal (4 * ε^2) * K⁻¹ ≤ ENNReal.ofReal (4 * ε^2) * (V θ)⁻¹ := by gcongr
      have h_div1 : ENNReal.ofReal (4 * ε^2) / K = ENNReal.ofReal (4 * ε^2) * K⁻¹ := by rfl
      have h_div2 : ENNReal.ofReal (4 * ε^2) / V θ = ENNReal.ofReal (4 * ε^2) * (V θ)⁻¹ := by rfl
      rw [h_div1, h_div2]; exact h_mul
    exact le_trans h3 h2
  have h6 : ∫⁻ (θ : Sphere d), Set.indicator U L θ ∂σ ≥
      ENNReal.ofReal (4 * ε^2) / K * σ U := by
    have h7 : ∀ θ, Set.indicator U L θ ≥ Set.indicator U (fun (_ : Sphere d) => ENNReal.ofReal (4 * ε^2) / K) θ := by
      intro θ; by_cases hθ : θ ∈ U
      · simpa [hθ, Set.indicator_of_mem] using h_all_L_ge θ hθ
      · simp [hθ, Set.indicator_apply]
    have h8 : ∫⁻ (θ : Sphere d), Set.indicator U L θ ∂σ ≥
        ∫⁻ (θ : Sphere d), Set.indicator U (fun (_ : Sphere d) => ENNReal.ofReal (4 * ε^2) / K) θ ∂σ :=
      lintegral_mono h7
    have h9 : ∫⁻ (θ : Sphere d), Set.indicator U (fun (_ : Sphere d) => ENNReal.ofReal (4 * ε^2) / K) θ ∂σ =
        ENNReal.ofReal (4 * ε^2) / K * σ U := by
      rw [lintegral_indicator hU_meas, lintegral_const]
      <;> simp [Measure.restrict_apply, Set.inter_univ]
    rw [h9] at h8
    exact h8
  have h9 : ∫⁻ (θ : Sphere d), Set.indicator U L θ ∂σ ≤ ENNReal.ofReal (C * ε^2 * B) := by
    have h10 : ∫⁻ (θ : Sphere d), Set.indicator U L θ ∂σ ≤ ∫⁻ (θ : Sphere d), L θ ∂σ := by
      apply lintegral_mono; intro θ; exact Set.indicator_le_self U L θ
    exact le_trans h10 h_avg_L2
  have h_contra : ENNReal.ofReal (4 * ε^2) / K * σ U ≤ ENNReal.ofReal (C * ε^2 * B) := le_trans h6 h9
  have h10 : ENNReal.ofReal (4 * ε^2) / K * σ U = ENNReal.ofReal (4 * C * B * ε^2) := by
    dsimp only [K]
    have h_pos2 : 0 < α / (C * B) := by positivity
    have h_div : ENNReal.ofReal (4 * ε^2) / ENNReal.ofReal (α / (C * B)) =
        ENNReal.ofReal ((4 * ε^2) / (α / (C * B))) := by
      rw [ENNReal.ofReal_div_of_pos h_pos2] <;> rfl
    rw [h_div, hσU_eq]
    have h_mul : ENNReal.ofReal ((4 * ε^2) / (α / (C * B))) * ENNReal.ofReal α =
        ENNReal.ofReal (((4 * ε^2) / (α / (C * B))) * α) := by
      rw [← ENNReal.ofReal_mul (by positivity)] <;> ring
    rw [h_mul]
    have h_eq : ((4 * ε^2) / (α / (C * B))) * α = 4 * C * B * ε^2 := by
      field_simp [hα_pos.ne', hC_pos.ne', hB.ne'] <;> ring
    rw [h_eq]
  rw [h10] at h_contra
  have h11 : 0 < C * B * ε^2 := by positivity
  have h13 : ¬ ENNReal.ofReal (4 * C * B * ε^2) ≤ ENNReal.ofReal (C * ε^2 * B) := by
    intro h_le
    have h14 : 4 * C * B * ε^2 ≤ C * ε^2 * B := by
      exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h_le
    have h15 : C * ε^2 * B = C * B * ε^2 := by ring
    rw [h15] at h14
    linarith
  exact h13 h_contra

/-- **Cone-restricted Marstrand: positive exact projection volume.**

Given a probability measure μ with UNIFORM finite 1-energy `I_1^ε(μ) ≤ B` for all ε > 0,
compact support, and a measurable cone U with positive spherical measure, there exists
θ ∈ closure(U) such that the exact projection `π_θ(supp μ)` has positive Lebesgue volume. -/
theorem marstrand_cone_positive_volume {d : ℕ} (hd : 2 ≤ d)
    {B : ℝ} (hB : 0 < B)
    (μ : Measure (EuclideanSpace ℝ (Fin d)))
    [IsProbabilityMeasure μ]
    (hI_uniform : ∀ (ε : ℝ) (hε : 0 < ε), robust_projection_main.rieszEnergy (α := 1) (hδ := hε) μ ≤ ENNReal.ofReal B)
    (U : Set (Sphere d)) (hU_meas : MeasurableSet U) (hU_pos : 0 < sphereProbabilityMeasure d U)
    (hA_compact : IsCompact μ.support) :
    ∃ (θ : Sphere d), θ ∈ closure U ∧
      ENNReal.ofReal ((sphereProbabilityMeasure d U).toReal / (marstrandSphereConstant d * B)) ≤
      volume (linearProjection θ.val '' μ.support) := by
  let σ := sphereProbabilityMeasure d
  haveI : IsProbabilityMeasure σ := sphereProbabilityMeasure_isProbability (by linarith)
  let C := marstrandSphereConstant d
  let α : ℝ := (σ U).toReal
  have hα_pos : 0 < α := by
    dsimp only [α]
    have h_ne : (σ U).toReal ≠ 0 := by
      intro h
      have h' : σ U = 0 ∨ σ U = ⊤ := by
        rw [ENNReal.toReal_eq_zero_iff] at h; exact h
      rcases h' with (h' | h')
      · exact hU_pos.ne' h'
      · have h_bdd : σ U ≤ 1 := by
          have h3 : σ U ≤ σ Set.univ := measure_mono (subset_univ U)
          have h4 : σ Set.univ = 1 := measure_univ
          rw [h4] at h3; exact h3
        rw [h'] at h_bdd; simp at h_bdd
    have h_nonneg : 0 ≤ (σ U).toReal := by positivity
    exact lt_of_le_of_ne h_nonneg h_ne.symm
  have hC_pos : 0 < C := by
    dsimp only [C, marstrandSphereConstant]
    have h_d_pos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (show 0 < d from by linarith)
    exact mul_pos (mul_pos (by positivity) h_d_pos) Real.pi_pos
  let c : ℝ := α / (C * B)
  have hc_pos : 0 < c := by positivity
  let A := μ.support
  let E := EuclideanSpace ℝ (Fin d)
  have hA_bdd : Bornology.IsBounded A := hA_compact.isBounded
  rcases hA_bdd.subset_ball (0 : E) with ⟨R, hR⟩
  let R' := max R 1
  have hR'_pos : 0 < R' := by positivity
  have hR'_bound : ∀ p ∈ A, ‖p‖ ≤ R' := by
    intro p hp
    have h1 : p ∈ Metric.ball (0 : E) R := hR hp
    have h2 : ‖p‖ < R := by simpa [Metric.mem_ball, dist_zero_right] using h1
    exact le_trans (le_of_lt h2) (le_max_left R 1)
  choose θ hθ_U hθ_V using fun k : ℕ =>
    marstrand_cone_lower_bound hd (hε := by positivity) hB μ
      (hI_uniform (1 / (k + 1 : ℝ)) (by positivity)) U hU_meas hU_pos
  let θseq : ℕ → Sphere d := θ
  letI : CompactSpace (Sphere d) := Metric.sphere.compactSpace 0 1
  have h_seq : ∃ (θ : Sphere d) (φ : ℕ → ℕ), StrictMono φ ∧
      Filter.Tendsto (fun k => θseq (φ k)) Filter.atTop (nhds θ) :=
    CompactSpace.tendsto_subseq θseq
  rcases h_seq with ⟨θ, φ, hφ_mono, hθ_tendsto⟩
  have hθ_closure : θ ∈ closure U := by
    have h_inU : ∀ᶠ (k : ℕ) in Filter.atTop, θseq (φ k) ∈ U :=
      Filter.Eventually.of_forall (fun k => hθ_U (φ k))
    exact mem_closure_of_tendsto hθ_tendsto h_inU
  -- Correct ε→0 passage: rho_k = ε_k + R' * ‖θ - θ_k‖
  let epsilon : ℕ → ℝ := fun k => 1 / (φ k + 1 : ℝ)
  let rho : ℕ → ℝ := fun k => epsilon k + R' * ‖θ.val - (θseq (φ k)).val‖
  have h_tendsto_val : Filter.Tendsto (fun k => (θseq (φ k)).val) Filter.atTop (nhds θ.val) :=
    continuous_subtype_val.continuousAt.tendsto.comp hθ_tendsto
  have h_phi_le : ∀ k : ℕ, (k : ℝ) ≤ (φ k : ℝ) := by
    intro k
    have h : k ≤ φ k := hφ_mono.id_le k
    exact_mod_cast h
  have h_eps_tendsto : Filter.Tendsto epsilon Filter.atTop (nhds 0) := by
    have h_le : ∀ k, |epsilon k| ≤ 1 / (k + 1 : ℝ) := by
      intro k
      have h_pos : 0 < epsilon k := by positivity
      rw [abs_of_pos h_pos]
      have h2 : (k + 1 : ℝ) ≤ (φ k + 1 : ℝ) := by
        have h3 : (k : ℝ) ≤ (φ k : ℝ) := h_phi_le k
        linarith
      exact one_div_le_one_div_of_le (by positivity) h2
    have h4 : Filter.Tendsto (fun k : ℕ => 1 / (k + 1 : ℝ)) Filter.atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have h_nonneg : ∀ k, 0 ≤ epsilon k := by
      intro k; dsimp only [epsilon]; positivity
    have h_le2 : ∀ k, epsilon k ≤ 1 / (k + 1 : ℝ) := by
      intro k
      have h_pos : 0 < epsilon k := by positivity
      have h_abs : |epsilon k| = epsilon k := abs_of_pos h_pos
      calc epsilon k
        = |epsilon k| := h_abs.symm
      _ ≤ 1 / (k + 1 : ℝ) := h_le k
    exact squeeze_zero h_nonneg h_le2 h4
  have h_norm_tendsto : Filter.Tendsto (fun k => ‖θ.val - (θseq (φ k)).val‖) Filter.atTop (nhds 0) := by
    have h6 : Filter.Tendsto (fun k => (θseq (φ k)).val) Filter.atTop (nhds θ.val) :=
      continuous_subtype_val.continuousAt.tendsto.comp hθ_tendsto
    have h5 : Filter.Tendsto (fun k => θ.val - (θseq (φ k)).val) Filter.atTop (nhds 0) := by
      simpa [sub_self] using h6.const_sub θ.val
    simpa [norm_zero] using h5.norm
  have h_rho_tendsto : Filter.Tendsto rho Filter.atTop (nhds 0) := by
    have h2 : Filter.Tendsto (fun k => R' * ‖θ.val - (θseq (φ k)).val‖) Filter.atTop (nhds 0) := by
      simpa [mul_zero] using h_norm_tendsto.const_mul R'
    simpa [zero_add] using h_eps_tendsto.add h2
  have h_incl : ∀ k, projectionNeighborhood (epsilon k) (θseq (φ k)).val A ⊆
      projectionNeighborhood (rho k) θ.val A := by
    intro k t ht
    rcases ht with ⟨p, hp, hdist⟩
    set v := θ.val - (θseq (φ k)).val with hvdef
    have h_diff : |linearProjection θ.val p - linearProjection (θseq (φ k)).val p| ≤ ‖v‖ * ‖p‖ := by
      have h_eq : linearProjection θ.val p - linearProjection (θseq (φ k)).val p = inner ℝ v p := by
        dsimp only [linearProjection, v]
        exact (inner_sub_left θ.val (θseq (φ k)).val p).symm
      rw [h_eq]
      exact abs_real_inner_le_norm v p
    have h1 : |linearProjection θ.val p - t| ≤
        |linearProjection θ.val p - linearProjection (θseq (φ k)).val p| + |linearProjection (θseq (φ k)).val p - t| := by
      have h_eq : linearProjection θ.val p - t =
          (linearProjection θ.val p - linearProjection (θseq (φ k)).val p) + (linearProjection (θseq (φ k)).val p - t) := by ring
      rw [h_eq]
      exact abs_add_le _ _
    have h3 : |linearProjection (θseq (φ k)).val p - t| < epsilon k := hdist
    have h4 : |linearProjection θ.val p - t| < ‖v‖ * ‖p‖ + epsilon k := by
      calc
        |linearProjection θ.val p - t|
          ≤ |linearProjection θ.val p - linearProjection (θseq (φ k)).val p| + |linearProjection (θseq (φ k)).val p - t| := h1
        _ ≤ ‖v‖ * ‖p‖ + |linearProjection (θseq (φ k)).val p - t| := by gcongr
        _ < ‖v‖ * ‖p‖ + epsilon k := by gcongr
    have h5 : ‖p‖ ≤ R' := hR'_bound p hp
    have h6 : |linearProjection θ.val p - t| < rho k := by
      calc
        |linearProjection θ.val p - t|
          < ‖v‖ * ‖p‖ + epsilon k := h4
        _ ≤ ‖v‖ * R' + epsilon k := by gcongr
        _ = rho k := by
          simp [rho, epsilon, v, hvdef] <;> ring
    exact ⟨p, hp, h6⟩
  have h_vol_lower : ∀ k, ENNReal.ofReal c ≤ volume (projectionNeighborhood (rho k) θ.val A) := by
    intro k
    have h6 : ENNReal.ofReal c ≤ volume (projectionNeighborhood (epsilon k) (θseq (φ k)).val A) :=
      hθ_V (φ k)
    exact le_trans h6 (measure_mono (h_incl k))
  have h_main : ∀ (eta : ℝ), 0 < eta → ENNReal.ofReal c ≤ volume (projectionNeighborhood eta θ.val A) := by
    intro eta heta
    have h_nhds : Set.Iio eta ∈ nhds (0 : ℝ) := by
      apply IsOpen.mem_nhds isOpen_Iio
      exact heta
    have h1 : ∀ᶠ k in Filter.atTop, rho k ∈ Set.Iio eta := h_rho_tendsto.eventually h_nhds
    have h1' : ∀ᶠ k in Filter.atTop, rho k < eta := by
      simpa [Set.mem_Iio] using h1
    rcases Filter.eventually_atTop.mp h1' with ⟨k0, hk0⟩
    have h2 : rho k0 < eta := hk0 k0 (by linarith)
    have h3 : projectionNeighborhood (rho k0) θ.val A ⊆ projectionNeighborhood eta θ.val A := by
      intro t ht
      rcases ht with ⟨p, hp, hdist⟩
      exact ⟨p, hp, lt_trans hdist h2⟩
    exact le_trans (h_vol_lower k0) (measure_mono h3)
  let S : Set ℝ := linearProjection θ.val '' A
  have hμ_ne_zero : μ ≠ 0 := by
    intro h
    have h9 : μ Set.univ = 0 := by rw [h] <;> simp
    have h10 : μ Set.univ = 1 := measure_univ
    rw [h10] at h9 <;> simp at h9
  have hA_nonempty : A.Nonempty := MeasureTheory.Measure.nonempty_support hμ_ne_zero
  have hS_nonempty : S.Nonempty := hA_nonempty.image _
  have h_cont_proj : Continuous (linearProjection θ.val) := by
    have h2 : Continuous (fun p : EuclideanSpace ℝ (Fin d) => inner ℝ θ.val p) :=
      continuous_inner.comp (continuous_const.prodMk continuous_id)
    have h3 : (linearProjection θ.val) = (fun p : EuclideanSpace ℝ (Fin d) => inner ℝ θ.val p) := by
      funext p; rfl
    rw [h3]
    exact h2
  have hS_compact : IsCompact S := hA_compact.image h_cont_proj
  have hS_closed : IsClosed S := hS_compact.isClosed
  let N : ℕ → Set ℝ := fun m => projectionNeighborhood (1 / (m + 1 : ℝ)) θ.val A
  have hN_lower : ∀ m, ENNReal.ofReal c ≤ volume (N m) := by
    intro m
    have h_pos : 0 < (1 / (m + 1 : ℝ)) := by positivity
    exact h_main (1 / (m + 1 : ℝ)) h_pos
  have hN_eq_thickening : ∀ m, N m = Metric.thickening (1 / (m + 1 : ℝ)) S := by
    intro m
    ext t
    have h_iff : t ∈ N m ↔ t ∈ Metric.thickening (1 / (m + 1 : ℝ)) S := by
      simp only [N, projectionNeighborhood]
      rw [Metric.mem_thickening_iff]
      constructor
      · rintro ⟨p, hp, hdist⟩
        have h4 : |t - linearProjection θ.val p| < 1 / (m + 1 : ℝ) := by
          have h5 : |t - linearProjection θ.val p| = |linearProjection θ.val p - t| := by rw [abs_sub_comm]
          rw [h5]; exact hdist
        exact ⟨linearProjection θ.val p, ⟨p, hp, rfl⟩, by simpa [dist_eq_norm] using h4⟩
      · rintro ⟨y, hy, hdist⟩
        rcases hy with ⟨p, hp, rfl⟩
        have h1 : |linearProjection θ.val p - t| < 1 / (m + 1 : ℝ) := by
          simpa [dist_eq_norm, abs_sub_comm] using hdist
        exact ⟨p, hp, h1⟩
    exact h_iff
  have hN_open : ∀ m, IsOpen (N m) := by
    intro m
    rw [hN_eq_thickening m]
    exact Metric.isOpen_thickening
  have hN_meas : ∀ m, MeasurableSet (N m) := fun m => (hN_open m).measurableSet
  have hN_decr : ∀ m, N (m + 1) ⊆ N m := by
    intro m t ht
    rcases ht with ⟨p, hp, hdist⟩
    have h5 : (1 : ℝ) / (↑(m + 1) + 1) ≤ 1 / (↑m + 1) := by
      have h6 : (↑(m + 1) + 1 : ℝ) ≥ (↑m + 1 : ℝ) := by
        simp [Nat.cast_add] <;> linarith
      exact one_div_le_one_div_of_le (by positivity) h6
    exact ⟨p, hp, lt_of_lt_of_le hdist h5⟩
  have hN_decr' : ∀ (m1 m2 : ℕ), m1 ≤ m2 → N m2 ⊆ N m1 := by
    intro m1 m2 hmn
    induction' hmn with m2 hmn ih
    · exact subset_refl _
    · exact subset_trans (hN_decr m2) ih
  have h_dir : Directed (· ⊇ ·) N := by
    intro i j
    use max i j
    constructor
    · exact hN_decr' i (max i j) (le_max_left i j)
    · exact hN_decr' j (max i j) (le_max_right i j)
  have hN_inter : (⋂ m, N m) = S := by
    ext t
    simp only [Set.mem_iInter, N, projectionNeighborhood]
    constructor
    · intro h
      have h6 : ∀ m : ℕ, ∃ p ∈ A, |linearProjection θ.val p - t| < 1 / (m + 1 : ℝ) := h
      have h7 : t ∈ closure S := by
        rw [Metric.mem_closure_iff]
        intro ε hε
        have h10 : ∃ m : ℕ, 1 / (m + 1 : ℝ) < ε := by
          have h11 : Filter.Tendsto (fun m : ℕ => (1 / (m + 1 : ℝ))) Filter.atTop (nhds 0) :=
            tendsto_one_div_add_atTop_nhds_zero_nat
          have h12 := h11.eventually (gt_mem_nhds hε)
          exact h12.exists
        rcases h10 with ⟨m, hm⟩
        rcases h6 m with ⟨p, hp, hdist⟩
        refine ⟨linearProjection θ.val p, ⟨p, hp, rfl⟩, ?_⟩
        have h17 : dist t (linearProjection θ.val p) = |t - linearProjection θ.val p| := by
          simp [dist_eq_norm]
        rw [h17]
        have h18 : |t - linearProjection θ.val p| < 1 / (m + 1 : ℝ) := by
          have h19 : |linearProjection θ.val p - t| = |t - linearProjection θ.val p| := by rw [abs_sub_comm]
          rw [h19] at hdist
          exact hdist
        exact lt_trans h18 hm
      rw [hS_closed.closure_eq] at h7
      exact h7
    · intro ht
      rcases ht with ⟨p, hp, rfl⟩
      intro m
      have h_pos : 0 < 1 / (m + 1 : ℝ) := by positivity
      exact ⟨p, hp, by simpa using h_pos⟩
  have hN_finite : volume (N 0) < ⊤ := by
    have h_bdd : Bornology.IsBounded (N 0) := by
      rw [hN_eq_thickening 0]
      exact hS_compact.isBounded.thickening
    exact h_bdd.measure_lt_top
  have h_cont : volume S = ⨅ m, volume (N m) := by
    rw [← hN_inter]
    exact Directed.measure_iInter (fun m => (hN_meas m).nullMeasurableSet) h_dir ⟨0, hN_finite.ne⟩
  have h_final : ENNReal.ofReal c ≤ volume S := by
    rw [h_cont]
    exact le_iInf hN_lower
  have h_c_eq : c = (sphereProbabilityMeasure d U).toReal / (marstrandSphereConstant d * B) := by
    rfl
  rw [h_c_eq] at h_final
  exact ⟨θ, hθ_closure, h_final⟩

end ProductLikeIncidence
