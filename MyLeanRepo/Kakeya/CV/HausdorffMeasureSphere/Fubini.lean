import MyLeanRepo.Kakeya.CV.HausdorffMeasureSphere.Regions


open MeasureTheory Metric Set Filter
open scoped ENNReal Pointwise Topology Pointwise
open Classical

namespace Kakeya.CV

noncomputable section

-- ======================================================================
-- Fubini averaging and main equality
-- ======================================================================

/-- For two rotation-invariant finite measures on the sphere,
μ(sphere) * ν(cap_r) = ν(sphere) * μ(cap_r). -/
lemma fubini_averaging {μ ν : Measure (Point 3)} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ_support : μ Set.univ = μ (unitSphere 3))
    (hν_support : ν Set.univ = ν (unitSphere 3))
    (hμ_inv : ∀ (f : Point 3 →ₗᵢ[ℝ] Point 3), ∀ (A : Set (Point 3)), MeasurableSet A → μ (f '' A) = μ A)
    (hν_inv : ∀ (f : Point 3 →ₗᵢ[ℝ] Point 3), ∀ (A : Set (Point 3)), MeasurableSet A → ν (f '' A) = ν A)
    (r : ℝ) (hr : 0 ≤ r) (x0 : Point 3) (hx0 : x0 ∈ unitSphere 3) :
    μ Set.univ * ν (sphereCap x0 r) = ν Set.univ * μ (sphereCap x0 r) := by
  classical
  let f : Point 3 × Point 3 → ENNReal := fun p =>
    if p.1 ∈ unitSphere 3 ∧ p.2 ∈ unitSphere 3 ∧ dist p.1 p.2 ≤ r then 1 else 0
  have h_us_meas : MeasurableSet (unitSphere 3) := by
    simpa [unitSphere] using isClosed_sphere.measurableSet
  have hf_meas : Measurable f := by
    apply Measurable.ite
    · have hdist_meas : MeasurableSet {p : Point 3 × Point 3 | dist p.1 p.2 ≤ r} :=
        measurableSet_Iic.preimage continuous_dist.measurable
      have h_set_eq : {p : Point 3 × Point 3 | p.1 ∈ unitSphere 3 ∧ p.2 ∈ unitSphere 3 ∧ dist p.1 p.2 ≤ r} =
          (unitSphere 3 ×ˢ unitSphere 3) ∩ {p | dist p.1 p.2 ≤ r} := by
        ext p; simp [Set.mem_prod] <;> tauto
      rw [h_set_eq]
      exact (h_us_meas.prod h_us_meas).inter hdist_meas
    · exact measurable_const
    · exact measurable_const

  -- Helper: linear isometry maps sphere caps to sphere caps
  have h_cap_img : ∀ (g : Point 3 →ₗᵢ[ℝ] Point 3) (x y : Point 3),
      x ∈ unitSphere 3 → y ∈ unitSphere 3 → g x = y →
      g '' (sphereCap x r) = sphereCap y r := by
    intro g x y hx hy hgy
    ext z
    simp only [Set.mem_image, sphereCap, Set.mem_inter_iff, Metric.mem_closedBall]
    constructor
    · rintro ⟨z, ⟨hz_sphere, hz_dist⟩, rfl⟩
      have h5 : g z ∈ unitSphere 3 := by
        have h6 : ‖g z‖ = ‖z‖ := g.norm_map z
        have h7 : ‖z‖ = 1 := by simpa [unitSphere, Metric.mem_sphere, dist_zero_right] using hz_sphere
        have h8 : ‖g z‖ = 1 := by rw [h6, h7]
        simpa [unitSphere, Metric.mem_sphere, dist_zero_right] using h8
      have h9 : dist (g z) y ≤ r := by
        have h10 : dist (g z) y = dist (g z) (g x) := by rw [hgy]
        rw [h10]; exact g.isometry.dist_eq z x ▸ hz_dist
      exact ⟨h5, h9⟩
    · rintro ⟨hz_sphere, hz_dist⟩
      have h_surj : Function.Surjective g := by
        let g' : Point 3 →ₗ[ℝ] Point 3 := g.toLinearMap
        have h_inj : Function.Injective g' := g.injective
        exact LinearMap.injective_iff_surjective.mp h_inj
      rcases h_surj z with ⟨w, rfl⟩
      have hw_sphere : w ∈ unitSphere 3 := by
        have h6 : ‖g w‖ = ‖w‖ := g.norm_map w
        have h7 : ‖g w‖ = 1 := by simpa [unitSphere, Metric.mem_sphere, dist_zero_right] using hz_sphere
        have h8 : ‖w‖ = 1 := by rw [← h6, h7]
        simpa [unitSphere, Metric.mem_sphere, dist_zero_right] using h8
      have hw_dist : dist w x ≤ r := by
        have h10 : dist (g w) y = dist w x := by
          have h11 : dist (g w) (g x) = dist w x := g.isometry.dist_eq w x
          rw [hgy] at h11; exact h11
        rw [h10] at hz_dist; exact hz_dist
      exact ⟨w, ⟨hw_sphere, hw_dist⟩, rfl⟩

  -- ν-cap rotation invariance
  have h_cap_rot_ν : ∀ (x y : Point 3), x ∈ unitSphere 3 → y ∈ unitSphere 3 →
      ν (sphereCap x r) = ν (sphereCap y r) := by
    intro x y hx hy
    have hx' : ‖x‖ = 1 := by simpa [unitSphere, Metric.mem_sphere, dist_zero_right] using hx
    have hy' : ‖y‖ = 1 := by simpa [unitSphere, Metric.mem_sphere, dist_zero_right] using hy
    rcases exists_linear_isometry_map x y hx' hy' with ⟨g, hgx⟩
    have h_img : g '' (sphereCap x r) = sphereCap y r := h_cap_img g x y hx hy hgx
    have h6 : ν (g '' (sphereCap x r)) = ν (sphereCap x r) :=
      hν_inv g (sphereCap x r) (h_us_meas.inter isClosed_closedBall.measurableSet)
    rw [← h_img, h6]

  -- μ-cap rotation invariance
  have h_cap_rot_μ : ∀ (x y : Point 3), x ∈ unitSphere 3 → y ∈ unitSphere 3 →
      μ (sphereCap x r) = μ (sphereCap y r) := by
    intro x y hx hy
    have hx' : ‖x‖ = 1 := by simpa [unitSphere, Metric.mem_sphere, dist_zero_right] using hx
    have hy' : ‖y‖ = 1 := by simpa [unitSphere, Metric.mem_sphere, dist_zero_right] using hy
    rcases exists_linear_isometry_map x y hx' hy' with ⟨g, hgx⟩
    have h_img : g '' (sphereCap x r) = sphereCap y r := h_cap_img g x y hx hy hgx
    have h6 : μ (g '' (sphereCap x r)) = μ (sphereCap x r) :=
      hμ_inv g (sphereCap x r) (h_us_meas.inter isClosed_closedBall.measurableSet)
    rw [← h_img, h6]

  -- Inner integral over y, for x on sphere
  have h_inner_ν : ∀ (x : Point 3), x ∈ unitSphere 3 →
      ∫⁻ (y : Point 3), f (x, y) ∂ν = ν (sphereCap x0 r) := by
    intro x hx
    have h_meas : MeasurableSet (sphereCap x r) := h_us_meas.inter isClosed_closedBall.measurableSet
    have h_eq : ∀ y, f (x, y) = Set.indicator (sphereCap x r) (fun _ => (1 : ENNReal)) y := by
      intro y
      simp only [f, Set.indicator_apply]
      have h_iff : (y ∈ unitSphere 3 ∧ dist x y ≤ r) ↔ y ∈ sphereCap x r := by
        simp [sphereCap, Set.mem_inter_iff, Metric.mem_closedBall, dist_comm] <;> tauto
      by_cases h : y ∈ unitSphere 3 ∧ dist x y ≤ r
      · have h' : y ∈ sphereCap x r := h_iff.mp h
        have h_if : x ∈ unitSphere 3 ∧ y ∈ unitSphere 3 ∧ dist x y ≤ r := ⟨hx, h.1, h.2⟩
        rw [if_pos h_if, if_pos h'] <;> rfl
      · have h' : y ∉ sphereCap x r := by intro h''; exact h (h_iff.mpr h'')
        have h_if : ¬(x ∈ unitSphere 3 ∧ y ∈ unitSphere 3 ∧ dist x y ≤ r) := by
          intro h_cont; exact h ⟨h_cont.2.1, h_cont.2.2⟩
        rw [if_neg h_if, if_neg h'] <;> rfl
    have h_f_eq : (fun y => f (x, y)) = Set.indicator (sphereCap x r) (fun _ => (1 : ENNReal)) := by
      funext y; exact h_eq y
    have h_int : ∫⁻ (y : Point 3), f (x, y) ∂ν = ν (sphereCap x r) := by
      rw [h_f_eq, lintegral_indicator h_meas] <;> simp
    rw [h_int]
    exact h_cap_rot_ν x x0 hx hx0

  -- Inner integral over x, for y on sphere
  have h_inner_μ : ∀ (y : Point 3), y ∈ unitSphere 3 →
      ∫⁻ (x : Point 3), f (x, y) ∂μ = μ (sphereCap x0 r) := by
    intro y hy
    have h_meas : MeasurableSet (sphereCap y r) := h_us_meas.inter isClosed_closedBall.measurableSet
    have h_eq : ∀ x, f (x, y) = Set.indicator (sphereCap y r) (fun _ => (1 : ENNReal)) x := by
      intro x
      simp only [f, Set.indicator_apply]
      have h_iff : (x ∈ unitSphere 3 ∧ dist x y ≤ r) ↔ x ∈ sphereCap y r := by
        simp [sphereCap, Set.mem_inter_iff, Metric.mem_closedBall, dist_comm] <;> tauto
      by_cases h : x ∈ unitSphere 3 ∧ dist x y ≤ r
      · have h' : x ∈ sphereCap y r := h_iff.mp h
        have h_if : x ∈ unitSphere 3 ∧ y ∈ unitSphere 3 ∧ dist x y ≤ r := ⟨h.1, hy, h.2⟩
        rw [if_pos h_if, if_pos h'] <;> rfl
      · have h' : x ∉ sphereCap y r := by intro h''; exact h (h_iff.mpr h'')
        have h_if : ¬(x ∈ unitSphere 3 ∧ y ∈ unitSphere 3 ∧ dist x y ≤ r) := by
          intro h_cont; exact h ⟨h_cont.1, h_cont.2.2⟩
        rw [if_neg h_if, if_neg h'] <;> rfl
    have h_f_eq : (fun x => f (x, y)) = Set.indicator (sphereCap y r) (fun _ => (1 : ENNReal)) := by
      funext x; exact h_eq x
    have h_int : ∫⁻ (x : Point 3), f (x, y) ∂μ = μ (sphereCap y r) := by
      rw [h_f_eq, lintegral_indicator h_meas] <;> simp
    rw [h_int]
    exact h_cap_rot_μ y x0 hy hx0

  -- μ is supported on sphere: μ(sphereᶜ) = 0
  have hμ_ae : ∀ᵐ x ∂μ, x ∈ unitSphere 3 := by
    have h_compl_meas : MeasurableSet (unitSphere 3)ᶜ := h_us_meas.compl
    have h_disj : Disjoint (unitSphere 3) (unitSphere 3)ᶜ := disjoint_compl_right
    have h_union : (unitSphere 3) ∪ (unitSphere 3)ᶜ = Set.univ := by simp
    have h_eq : μ Set.univ = μ (unitSphere 3) + μ (unitSphere 3)ᶜ := by
      have h : μ ((unitSphere 3) ∪ (unitSphere 3)ᶜ) = μ (unitSphere 3) + μ (unitSphere 3)ᶜ :=
        measure_union h_disj h_compl_meas
      rw [h_union] at h
      exact h
    have h_fin : μ (unitSphere 3) < ⊤ := measure_lt_top μ (unitSphere 3)
    have h_eq2 : μ (unitSphere 3) + μ (unitSphere 3)ᶜ = μ (unitSphere 3) := by
      rw [← h_eq, hμ_support]
    have h_zero : μ (unitSphere 3)ᶜ = 0 := by
      have h_fin_ne : μ (unitSphere 3) ≠ ⊤ := h_fin.ne
      have h_compl_lt_top : μ (unitSphere 3)ᶜ < ⊤ := measure_lt_top μ (unitSphere 3)ᶜ
      have h_toReal : (μ (unitSphere 3) + μ (unitSphere 3)ᶜ).toReal = (μ (unitSphere 3)).toReal := by
        rw [h_eq2]
      have h_add : (μ (unitSphere 3) + μ (unitSphere 3)ᶜ).toReal =
          (μ (unitSphere 3)).toReal + (μ (unitSphere 3)ᶜ).toReal := by
        rw [ENNReal.toReal_add h_fin_ne h_compl_lt_top.ne]
      have h' : (μ (unitSphere 3)ᶜ).toReal = 0 := by
        rw [h_add] at h_toReal; linarith
      have h_iff := ENNReal.toReal_eq_zero_iff (μ (unitSphere 3)ᶜ)
      have h_or : μ (unitSphere 3)ᶜ = 0 ∨ μ (unitSphere 3)ᶜ = ⊤ := h_iff.mp h'
      exact h_or.resolve_right h_compl_lt_top.ne
    exact h_zero

  -- ν is supported on sphere: ν(sphereᶜ) = 0
  have hν_ae : ∀ᵐ y ∂ν, y ∈ unitSphere 3 := by
    have h_compl_meas : MeasurableSet (unitSphere 3)ᶜ := h_us_meas.compl
    have h_disj : Disjoint (unitSphere 3) (unitSphere 3)ᶜ := disjoint_compl_right
    have h_union : (unitSphere 3) ∪ (unitSphere 3)ᶜ = Set.univ := by simp
    have h_eq : ν Set.univ = ν (unitSphere 3) + ν (unitSphere 3)ᶜ := by
      have h : ν ((unitSphere 3) ∪ (unitSphere 3)ᶜ) = ν (unitSphere 3) + ν (unitSphere 3)ᶜ :=
        measure_union h_disj h_compl_meas
      rw [h_union] at h
      exact h
    have h_fin : ν (unitSphere 3) < ⊤ := measure_lt_top ν (unitSphere 3)
    have h_eq2 : ν (unitSphere 3) + ν (unitSphere 3)ᶜ = ν (unitSphere 3) := by
      rw [← h_eq, hν_support]
    have h_zero : ν (unitSphere 3)ᶜ = 0 := by
      have h_fin_ne : ν (unitSphere 3) ≠ ⊤ := h_fin.ne
      have h_compl_lt_top : ν (unitSphere 3)ᶜ < ⊤ := measure_lt_top ν (unitSphere 3)ᶜ
      have h_toReal : (ν (unitSphere 3) + ν (unitSphere 3)ᶜ).toReal = (ν (unitSphere 3)).toReal := by
        rw [h_eq2]
      have h_add : (ν (unitSphere 3) + ν (unitSphere 3)ᶜ).toReal =
          (ν (unitSphere 3)).toReal + (ν (unitSphere 3)ᶜ).toReal := by
        rw [ENNReal.toReal_add h_fin_ne h_compl_lt_top.ne]
      have h' : (ν (unitSphere 3)ᶜ).toReal = 0 := by
        rw [h_add] at h_toReal; linarith
      have h_iff := ENNReal.toReal_eq_zero_iff (ν (unitSphere 3)ᶜ)
      have h_or : ν (unitSphere 3)ᶜ = 0 ∨ ν (unitSphere 3)ᶜ = ⊤ := h_iff.mp h'
      exact h_or.resolve_right h_compl_lt_top.ne
    exact h_zero

  -- h1: Fubini first direction: integral = μ univ * ν cap
  have h1 : ∫⁻ p, f p ∂(μ.prod ν) = μ Set.univ * ν (sphereCap x0 r) := by
    have h_ae : AEMeasurable f (μ.prod ν) := hf_meas.aemeasurable
    rw [lintegral_prod f h_ae]
    have h2 : ∀ᵐ x ∂μ, ∫⁻ (y : Point 3), f (x, y) ∂ν = ν (sphereCap x0 r) := by
      filter_upwards [hμ_ae] with x hx
      exact h_inner_ν x hx
    rw [lintegral_congr_ae h2]
    simp [mul_comm]

  -- h5: Fubini symmetric direction: integral = ν univ * μ cap
  have h5 : ∫⁻ p, f p ∂(μ.prod ν) = ν Set.univ * μ (sphereCap x0 r) := by
    rw [MeasureTheory.lintegral_prod_symm' f hf_meas]
    have h2 : ∀ᵐ y ∂ν, ∫⁻ (x : Point 3), f (x, y) ∂μ = μ (sphereCap x0 r) := by
      filter_upwards [hν_ae] with y hy
      exact h_inner_μ y hy
    rw [lintegral_congr_ae h2]
    simp [mul_comm]

  exact h1.symm.trans h5
