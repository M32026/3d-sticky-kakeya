import MyLeanRepo.Kakeya.CV.Isoperimetric.Coarea.CoareaSinglePatch
import MyLeanRepo.Kakeya.CV.Isoperimetric.Coarea.CoareaInequalityGlobalization
import MyLeanRepo.Kakeya.CV.Isoperimetric.Measure.Eilenberg
import MyLeanRepo.Kakeya.CV.Isoperimetric.Measure.LevelSetMeasurability
import MyLeanRepo.Kakeya.CV.Isoperimetric.Perimeter.Basic
import MyLeanRepo.Kakeya.CV.Isoperimetric.InnerMinkowski.Basic
import Mathlib.Tactic


open MeasureTheory Metric Set ENNReal Filter
open scoped MeasureTheory

namespace Geometry

variable {n : ℕ} [Nonempty (Fin n)]

/-!
# Global Coarea Formula — Assembly
-/

-- ============================================================================
-- Helper: unrestricted level-set AEMeasurability for 1-Lipschitz functions
-- ============================================================================

/-- **Unrestricted level set AEMeasurability.**

For a 1-Lipschitz function `f` and a bounded measurable set `B`,
`s ↦ μHE[n-1](B ∩ f⁻¹{s})` is `AEMeasurable` w.r.t. unrestricted `volume`. -/
lemma levelSet_aemeasurable_global (hn : 2 ≤ n)
    {f : E n → ℝ} (hf : LipschitzWith 1 f)
    {B : Set (E n)} (hB : MeasurableSet B) (hBdd : Bornology.IsBounded B) :
    AEMeasurable (fun s : ℝ => μHE[n - 1] (B ∩ f ⁻¹' {s})) volume := by
  by_cases hB_empty : B = ∅
  · have h : (fun s : ℝ => μHE[n - 1] (B ∩ f ⁻¹' {s})) = fun _ => 0 := by
      funext s
      rw [hB_empty] <;> simp
    rw [h]
    exact measurable_const.aemeasurable
  · -- Pick x0 ∈ B
    have hB_nonempty : B.Nonempty := by
      rwa [Set.nonempty_iff_ne_empty]
    rcases hB_nonempty with ⟨x0, hx0⟩
    -- f '' B is bounded since f is Lipschitz and B is bounded
    have h_image_bdd : Bornology.IsBounded (f '' B) := hf.isBounded_image hBdd
    rcases (Metric.isBounded_iff_subset_ball (f x0)).mp h_image_bdd with ⟨r0, h_sub0⟩
    have h_r0_pos : 0 < r0 := by
      have h_fx0 : f x0 ∈ f '' B := mem_image_of_mem f hx0
      have h_in_ball : f x0 ∈ ball (f x0) r0 := h_sub0 h_fx0
      simpa [mem_ball, dist_self] using h_in_ball
    let r := r0 + 1
    have hr_pos : 0 < r := by simp [r, h_r0_pos] <;> linarith
    have h_sub : f '' B ⊆ ball (f x0) r := by
      intro y hy
      have h : y ∈ ball (f x0) r0 := h_sub0 hy
      have h2 : dist y (f x0) < r0 := by simpa [mem_ball] using h
      simpa [mem_ball, r] using by linarith
    let c := f x0
    let a := c - r - 1
    let b := c + r + 1
    have hab : a < b := by simp [a, b] <;> linarith
    have h_image_sub : f '' B ⊆ Set.Ioo a b := by
      intro y hy
      have h1 : y ∈ ball c r := h_sub hy
      have h2 : |y - c| < r := by simpa [Real.dist_eq, mem_ball] using h1
      have h3 : c - r < y := by linarith [abs_lt.mp h2]
      have h4 : y < c + r := by linarith [abs_lt.mp h2]
      exact ⟨by linarith, by linarith⟩
    have h_zero_outside : ∀ s, s ∉ Set.Ioc a b → μHE[n - 1] (B ∩ f ⁻¹' {s}) = 0 := by
      intro s hs
      have h5 : s ∉ f '' B := by
        intro h6
        have h7 : s ∈ Set.Ioo a b := h_image_sub h6
        exact hs ⟨h7.1, h7.2.le⟩
      have h8 : B ∩ f ⁻¹' {s} = ∅ := by
        ext x
        simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false]
        intro ⟨hx_B, hx_s⟩
        have h9 : f x ∈ f '' B := ⟨x, hx_B, rfl⟩
        have h10 : s ∈ f '' B := by
          have h11 : f x = s := hx_s
          rw [←h11]
          exact h9
        exact h5 h10
      rw [h8] <;> simp
    have h_restrict : AEMeasurable (fun s : ℝ => μHE[n - 1] (B ∩ f ⁻¹' {s}))
        (volume.restrict (Set.Ioc a b)) :=
      levelSetMeasure_aemeasurable hn hf hB hBdd hab
    have hS_meas : MeasurableSet (Set.Ioc a b) :=
      isOpen_Ioi.measurableSet.inter isClosed_Iic.measurableSet
    have h_indicator : AEMeasurable ((Set.Ioc a b).indicator (fun s : ℝ => μHE[n - 1] (B ∩ f ⁻¹' {s}))) volume :=
      (aemeasurable_indicator_iff hS_meas).mpr h_restrict
    have h_eq : (Set.Ioc a b).indicator (fun s : ℝ => μHE[n - 1] (B ∩ f ⁻¹' {s})) =
        (fun s : ℝ => μHE[n - 1] (B ∩ f ⁻¹' {s})) := by
      funext s
      by_cases h : s ∈ Set.Ioc a b
      · simp [Set.indicator, h]
      · have h10 : μHE[n - 1] (B ∩ f ⁻¹' {s}) = 0 := h_zero_outside s h
        simp [Set.indicator, h, h10]
    rw [h_eq] at h_indicator
    exact h_indicator

/-- **Level set AEMeasurability for arbitrary Lipschitz constant.**

For a Lipschitz function `f` with constant `L` and a bounded measurable `B`,
`s ↦ μHE[n-1](B ∩ f⁻¹{s})` is `AEMeasurable` w.r.t. unrestricted `volume`. -/
lemma levelSet_aemeasurable_lipschitz (hn : 2 ≤ n)
    {f : E n → ℝ} {L : NNReal} (hf : LipschitzWith L f)
    {B : Set (E n)} (hB : MeasurableSet B) (hBdd : Bornology.IsBounded B) :
    AEMeasurable (fun s : ℝ => μHE[n - 1] (B ∩ f ⁻¹' {s})) volume := by
  by_cases hL0 : L = 0
  · -- f is constant
    have h_const : ∀ x y, f x = f y := by
      intro x y
      have h : dist (f x) (f y) ≤ (0 : ℝ) := by
        simpa [hL0] using hf.dist_le_mul x y
      have h' : dist (f x) (f y) = 0 := by
        have h'' : 0 ≤ dist (f x) (f y) := dist_nonneg
        linarith
      exact dist_eq_zero.mp h'
    let c := f 0
    have hfc : ∀ x, f x = c := fun x => h_const x 0
    have h1 : ∀ (s : ℝ), f ⁻¹' {s} = if s = c then Set.univ else ∅ := by
      intro s
      by_cases hs : s = c
      · subst hs
        ext x
        simp [hfc]
      · ext x
        simp [hfc, hs] <;> tauto
    have h_main : (fun s : ℝ => μHE[n - 1] (B ∩ f ⁻¹' {s})) =
        fun s : ℝ => if s = c then μHE[n - 1] B else 0 := by
      funext s
      rw [h1 s]
      by_cases hs : s = c
      · subst hs
        simp
      · simp [hs]
    rw [h_main]
    have h_meas : Measurable (fun s : ℝ => if s = c then μHE[n - 1] B else 0) := by
      exact Measurable.ite (measurableSet_singleton c) measurable_const measurable_const
    exact h_meas.aemeasurable
  · -- L > 0: scale to 1-Lipschitz and apply levelSet_aemeasurable_global
    have hL_pos : 0 < (L : ℝ) := by
      have h : 0 < L := zero_lt_iff.mpr hL0
      exact_mod_cast h
    let g : E n → ℝ := fun x => f x / (L : ℝ)
    have hg_lip : LipschitzWith 1 g := by
      rw [lipschitzWith_iff_dist_le_mul]
      intro x y
      have h2 : dist (f x) (f y) ≤ (L : ℝ) * dist x y := hf.dist_le_mul x y
      have h3 : dist (g x) (g y) = dist (f x) (f y) / (L : ℝ) := by
        simp only [g]
        have h4 : dist (f x / (L : ℝ)) (f y / (L : ℝ)) = |(f x - f y) / (L : ℝ)| := by
          rw [Real.dist_eq]
          have h6 : f x / (L : ℝ) - f y / (L : ℝ) = (f x - f y) / (L : ℝ) := by ring
          rw [h6] <;> rfl
        rw [h4]
        have h5 : |(f x - f y) / (L : ℝ)| = |f x - f y| / (L : ℝ) := by
          rw [abs_div]
          <;> rw [abs_of_pos hL_pos]
        rw [h5]
        <;> rfl
      rw [h3]
      have h4 : dist (f x) (f y) / (L : ℝ) ≤ (L : ℝ) * dist x y / (L : ℝ) := by
        gcongr
        <;> linarith
      have h5 : (L : ℝ) * dist x y / (L : ℝ) = dist x y := by
        field_simp [hL_pos.ne'] <;> ring
      rw [h5] at h4
      simpa using h4
    let h_fun : ℝ → ENNReal := fun t => μHE[n - 1] (B ∩ g ⁻¹' {t})
    have h_ae : AEMeasurable h_fun volume :=
      levelSet_aemeasurable_global hn hg_lip hB hBdd
    let scale : ℝ → ℝ := fun s => s / (L : ℝ)
    have h_scale_meas : Measurable scale := by fun_prop
    have h_rel : ∀ s : ℝ, B ∩ f ⁻¹' {s} = B ∩ g ⁻¹' {scale s} := by
      intro s
      ext x
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff]
      constructor
      · rintro ⟨hxB, hxf⟩
        have hg : g x = scale s := by
          dsimp only [g, scale]
          rw [hxf]
          <;> field_simp
          <;> ring
        exact ⟨hxB, hg⟩
      · rintro ⟨hxB, hxg⟩
        have hf' : f x = s := by
          dsimp only [g, scale] at hxg
          have h6 : f x / (L : ℝ) = s / (L : ℝ) := hxg
          have h7 : f x = s := by
            apply_fun (fun y : ℝ => y * (L : ℝ)) at h6
            simpa [hL_pos.ne'] using h6
          exact h7
        exact ⟨hxB, hf'⟩
    have h_main_eq : (fun s : ℝ => μHE[n - 1] (B ∩ f ⁻¹' {s})) = h_fun ∘ scale := by
      funext s
      rw [h_rel s] <;> rfl
    rw [h_main_eq]
    have h_ac : Measure.map scale volume ≪ volume := by
      have h_eq : Measure.map scale volume = (ENNReal.ofReal (L : ℝ)) • volume := by
        apply Measure.ext
        intro s hs
        rw [Measure.map_apply h_scale_meas hs]
        have h_scale_eq : scale = fun x : ℝ => (1 / (L : ℝ)) * x := by
          funext x
          dsimp only [scale]
          rw [div_eq_mul_inv] <;> ring
        rw [h_scale_eq]
        rw [Real.volume_preimage_mul_left (show (1 / (L : ℝ)) ≠ 0 by positivity) s]
        have h4 : ENNReal.ofReal |(1 / (L : ℝ))⁻¹| = ENNReal.ofReal (L : ℝ) := by
          have h5 : (1 / (L : ℝ))⁻¹ = (L : ℝ) := by
            field_simp [hL_pos.ne'] <;> ring
          rw [h5, abs_of_pos hL_pos]
        rw [h4] <;> rfl
      rw [h_eq]
      intro s hs
      simpa [hs] using rfl
    rcases h_ae with ⟨h_meas, h_conj⟩
    have h_measurable : Measurable h_meas := h_conj.1
    have h_aeq : h_fun =ᵐ[volume] h_meas := h_conj.2
    have h_null : volume {x | h_fun x ≠ h_meas x} = 0 := by
      have h1 : ∀ᵐ x ∂volume, h_fun x = h_meas x := h_aeq
      exact (ae_iff).mp h1
    have h_null2 : (Measure.map scale volume) {x | h_fun x ≠ h_meas x} = 0 := h_ac h_null
    have h_eq2 : h_fun =ᵐ[Measure.map scale volume] h_meas := by
      have h2 : ∀ᵐ x ∂(Measure.map scale volume), h_fun x = h_meas x := (ae_iff).mpr h_null2
      exact h2
    have h_ae2 : AEMeasurable h_fun (Measure.map scale volume) :=
      ⟨h_meas, h_measurable, h_eq2⟩
    exact h_ae2.comp_measurable h_scale_meas

-- ============================================================================
-- Critical set bound via Eilenberg inequality + McShane extension
-- ============================================================================

/-- **Critical set Eilenberg bound.**

For a C¹ function u and δ > 0, let Z_δ = {‖∇u‖ < δ}.
Then `∫⁻ s, μHE[n-1](Z_δ ∩ {u = s}) ≤ C_n * δ * volume(Z_δ)`
where C_n depends only on n. -/
lemma critical_set_eilenberg_bound
    (u : E n → ℝ) (hu : ContDiff ℝ 1 u)
    (δ : ℝ) (hδ_pos : 0 < δ)
    (hn : 2 ≤ n) :
    ∃ (C : ENNReal), C ≠ ⊤ ∧
      ∫⁻ s : ℝ, μHE[n - 1] ({x | ‖fderiv ℝ u x‖ < δ} ∩ {x | u x = s})
        ≤ C * volume {x | ‖fderiv ℝ u x‖ < δ} := by
  classical
  let Z : Set (E n) := {x | ‖fderiv ℝ u x‖ < δ}
  have hZ_open : IsOpen Z := by
    have h1 : Continuous (fun x => ‖fderiv ℝ u x‖) :=
      (hu.continuous_fderiv (by norm_num)).norm
    exact h1.isOpen_preimage _ isOpen_Iio
  have hZ_meas : MeasurableSet Z := hZ_open.measurableSet

  -- For each x ∈ Z, find a ball where ‖∇u‖ < 2δ
  have h_cover : ∀ (x : E n), x ∈ Z → ∃ (r : ℝ), 0 < r ∧
      (∀ y ∈ ball x r, ‖fderiv ℝ u y‖ < 2 * δ) := by
    intro x hx
    have h1 : ‖fderiv ℝ u x‖ < δ := hx
    have h2 : ‖fderiv ℝ u x‖ < 2 * δ := by
      have h3 : δ < 2 * δ := by linarith
      exact h1.trans h3
    have h_set_open : IsOpen {y : E n | ‖fderiv ℝ u y‖ < 2 * δ} := by
      have h_cont : Continuous (fun y => ‖fderiv ℝ u y‖) :=
        (hu.continuous_fderiv (by norm_num)).norm
      exact h_cont.isOpen_preimage _ isOpen_Iio
    have h_nhds : {y : E n | ‖fderiv ℝ u y‖ < 2 * δ} ∈ nhds x :=
      h_set_open.mem_nhds h2
    rcases Metric.mem_nhds_iff.mp h_nhds with ⟨r, hr_pos, hr⟩
    exact ⟨r, hr_pos, fun y hy => hr hy⟩

  let r : E n → ℝ := fun x => if hx : x ∈ Z
    then Classical.choose (h_cover x hx)
    else 0
  have hr_pos : ∀ (x : E n), x ∈ Z → 0 < r x := by
    intro x hx
    have h1 : r x = Classical.choose (h_cover x hx) := by simp [r, hx]
    rw [h1]; exact (Classical.choose_spec (h_cover x hx)).1
  have hr_ball : ∀ (x : E n), x ∈ Z →
      ∀ y ∈ ball x (r x), ‖fderiv ℝ u y‖ < 2 * δ := by
    intro x hx
    have h1 : r x = Classical.choose (h_cover x hx) := by simp [r, hx]
    rw [h1]; exact (Classical.choose_spec (h_cover x hx)).2

  let B : E n → Set (E n) := fun x => ball x (r x)
  have hB_open : ∀ x, IsOpen (B x) := fun _ => isOpen_ball
  have h_coverZ : Z ⊆ ⋃ (x : E n), B x := by
    intro y hy
    have h2 : y ∈ B y := mem_ball_self (hr_pos y hy)
    exact Set.mem_iUnion.mpr ⟨y, h2⟩

  have hZ_lindelof : IsLindelof Z := HereditarilyLindelofSpace.isLindelof Z
  rcases IsLindelof.indexed_countable_subcover hZ_lindelof B hB_open h_coverZ
    with ⟨x', h_cover'⟩

  let B' : ℕ → Set (E n) := fun i => B (x' i)
  have hB'_open : ∀ i, IsOpen (B' i) := fun i => hB_open (x' i)

  -- Disjointify
  let A : ℕ → Set (E n) := fun i =>
    (Z ∩ B' i) \ ⋃ j ∈ Finset.range i, (Z ∩ B' j)
  have hA_meas : ∀ i, MeasurableSet (A i) := by
    intro i
    have h1 : MeasurableSet (Z ∩ B' i) := hZ_meas.inter (hB'_open i).measurableSet
    have h2 : MeasurableSet (⋃ j ∈ Finset.range i, (Z ∩ B' j)) := by
      apply MeasurableSet.biUnion
      · exact Finset.countable_toSet _
      · intro j _; exact hZ_meas.inter (hB'_open j).measurableSet
    exact h1.diff h2
  have hA_sub_B : ∀ i, A i ⊆ B' i := by
    intro i x hx; exact hx.1.2
  have hA_disj : Pairwise (fun i j => Disjoint (A i) (A j)) := by
    intro i j hne
    by_cases h : i < j
    · have h6 : A j ⊆ (Z ∩ B' j) \ (Z ∩ B' i) := by
        intro x hx
        have h7 : x ∈ Z ∩ B' j := hx.1
        have h8 : x ∉ ⋃ k ∈ Finset.range j, (Z ∩ B' k) := hx.2
        have h9 : x ∉ Z ∩ B' i := by
          intro h10
          have h11 : x ∈ ⋃ k ∈ Finset.range j, (Z ∩ B' k) := by
            apply Set.mem_iUnion₂.mpr
            exact ⟨i, Finset.mem_range.mpr h, h10⟩
          exact h8 h11
        exact ⟨h7, h9⟩
      have h7 : Disjoint (A i) ((Z ∩ B' j) \ (Z ∩ B' i)) := by
        rw [Set.disjoint_left]; intro x hxi hxj; exact hxj.2 hxi.1
      exact h7.mono_right h6
    · have h' : j < i := by omega
      have h6 : A i ⊆ (Z ∩ B' i) \ (Z ∩ B' j) := by
        intro x hx
        have h7 : x ∈ Z ∩ B' i := hx.1
        have h8 : x ∉ ⋃ k ∈ Finset.range i, (Z ∩ B' k) := hx.2
        have h9 : x ∉ Z ∩ B' j := by
          intro h10
          have h11 : x ∈ ⋃ k ∈ Finset.range i, (Z ∩ B' k) := by
            apply Set.mem_iUnion₂.mpr
            exact ⟨j, Finset.mem_range.mpr h', h10⟩
          exact h8 h11
        exact ⟨h7, h9⟩
      have h7 : Disjoint (A j) ((Z ∩ B' i) \ (Z ∩ B' j)) := by
        rw [Set.disjoint_left]; intro x hxj hxi; exact hxi.2 hxj.1
      exact (h7.mono_right h6).symm

  have hA_union : (⋃ i, A i) = Z := by
    ext x
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨i, hi⟩; exact hi.1.1
    · intro hx
      have h2 : x ∈ ⋃ i, B' i := h_cover' hx
      rcases Set.mem_iUnion.mp h2 with ⟨i, hi⟩
      let P : ℕ → Prop := fun j => x ∈ B' j
      have hP : ∃ j, P j := ⟨i, hi⟩
      let k := Nat.find hP
      have hk : P k := Nat.find_spec hP
      have hmin : ∀ j < k, ¬ P j := by intro j hj; exact Nat.find_min hP hj
      have h3 : x ∈ A k := by
        have h4 : x ∈ Z ∩ B' k := ⟨hx, hk⟩
        have h5 : x ∉ ⋃ j ∈ Finset.range k, (Z ∩ B' j) := by
          intro h6
          rcases Set.mem_iUnion₂.mp h6 with ⟨j, hj_range, hj_ZB⟩
          have h_j_lt_k : j < k := Finset.mem_range.mp hj_range
          exact hmin j h_j_lt_k hj_ZB.2
        exact ⟨h4, h5⟩
      exact ⟨k, h3⟩

  -- On each B' i, u is 2δ-Lipschitz (by convexity of ball and derivative bound)
  let L2δ : NNReal := ⟨2 * δ, by positivity⟩
  have h_lip_ball : ∀ i, LipschitzOnWith L2δ u (B' i) := by
    intro i
    by_cases hxi : x' i ∈ Z
    · have h1 : ∀ y ∈ B' i, ‖fderiv ℝ u y‖ < 2 * δ := hr_ball (x' i) hxi
      have h2 : ∀ y ∈ B' i, ‖fderiv ℝ u y‖₊ ≤ L2δ := by
        intro y hy
        have h3 : ‖fderiv ℝ u y‖ < 2 * δ := h1 y hy
        have h4 : ‖fderiv ℝ u y‖₊ = ⟨‖fderiv ℝ u y‖, norm_nonneg _⟩ := by rfl
        rw [h4]
        exact NNReal.coe_le_coe.mpr h3.le
      have h_diff : ∀ y ∈ B' i, DifferentiableAt ℝ u y := by
        intro y _; exact (hu.differentiable (by norm_num)).differentiableAt
      have h_conv : Convex ℝ (B' i) := by
        have h : B' i = ball (x' i) (r (x' i)) := by rfl
        rw [h]
        intro x hx y hy a b ha hb hab
        simp only [mem_ball] at hx hy ⊢
        have hsum : a + b = 1 := hab
        have h1 : a • x + b • y - x' i = a • (x - x' i) + b • (y - x' i) := by
          have h2 : (a + b) • x' i = a • x' i + b • x' i := by
            rw [add_smul]
          calc
            a • x + b • y - x' i
              = a • x + b • y - (a + b) • x' i := by rw [hsum] <;> simp
            _ = a • x + b • y - (a • x' i + b • x' i) := by rw [h2]
            _ = a • x - a • x' i + (b • y - b • x' i) := by abel
            _ = a • (x - x' i) + b • (y - x' i) := by
              have h3 : a • x - a • x' i = a • (x - x' i) := by rw [←smul_sub]
              have h4 : b • y - b • x' i = b • (y - x' i) := by rw [←smul_sub]
              rw [h3, h4] <;> abel
        have h_na : ‖a • (x - x' i)‖ = a * ‖x - x' i‖ := by
          calc
            ‖a • (x - x' i)‖ = |a| * ‖x - x' i‖ := norm_smul a (x - x' i)
            _ = a * ‖x - x' i‖ := by rw [abs_of_nonneg ha]
        have h_nb : ‖b • (y - x' i)‖ = b * ‖y - x' i‖ := by
          calc
            ‖b • (y - x' i)‖ = |b| * ‖y - x' i‖ := norm_smul b (y - x' i)
            _ = b * ‖y - x' i‖ := by rw [abs_of_nonneg hb]
        calc
          ‖a • x + b • y - x' i‖
            = ‖a • (x - x' i) + b • (y - x' i)‖ := by rw [h1]
          _ ≤ ‖a • (x - x' i)‖ + ‖b • (y - x' i)‖ := norm_add_le _ _
          _ = a * ‖x - x' i‖ + b * ‖y - x' i‖ := by rw [h_na, h_nb]
          _ < a * r (x' i) + b * r (x' i) := by
            have hxa : ‖x - x' i‖ < r (x' i) := hx
            have hya : ‖y - x' i‖ < r (x' i) := hy
            by_cases ha_pos : 0 < a
            · by_cases hb_pos : 0 < b
              · exact add_lt_add (mul_lt_mul_of_pos_left hxa ha_pos) (mul_lt_mul_of_pos_left hya hb_pos)
              · have hb0 : b = 0 := by linarith
                have ha1 : a = 1 := by linarith
                simp [hb0, ha1] at * <;> exact hxa
            · have ha0 : a = 0 := by linarith
              have hb1 : b = 1 := by linarith
              simp [ha0, hb1] at * <;> exact hya
          _ = r (x' i) := by
            have h7 : a * r (x' i) + b * r (x' i) = (a + b) * r (x' i) := by ring
            rw [h7, hsum] <;> ring
      exact h_conv.lipschitzOnWith_of_nnnorm_fderiv_le h_diff h2
    · -- x' i ∉ Z: r(x' i) = 0, B' i = ∅
      have hri0 : r (x' i) = 0 := by simp [r, hxi]
      have hB_empty : B' i = ∅ := by
        have h : B' i = ball (x' i) (r (x' i)) := by rfl
        rw [h, hri0]
        ext y; simp [Metric.mem_ball] <;> linarith
      rw [hB_empty]
      simp

  have h_lip_A : ∀ i, LipschitzOnWith L2δ u (A i) := by
    intro i
    exact (h_lip_ball i).mono (hA_sub_B i)

  -- Explicit Eilenberg constant for μHE
  let d : ℕ := n - 1
  let c_d : NNReal := MeasureTheory.Measure.addHaarScalarFactor
      (volume : Measure (E d)) (μH[d] : Measure (E d))
  let c_n : NNReal := MeasureTheory.Measure.addHaarScalarFactor
      (volume : Measure (E n)) (μH[n] : Measure (E n))
  let C_eil : ENNReal := (c_d : ENNReal) * (L2δ : ENNReal) / (c_n : ENNReal)
  have hc_d_pos : (c_d : ENNReal) ≠ 0 := by
    have h : (volume.addHaarScalarFactor μH[↑d]) ≠ 0 :=
      MeasureTheory.Measure.addHaarScalarFactor_volume_hausdorffMeasure_ne_zero d
    simpa [c_d] using h
  have hc_n_pos : (c_n : ENNReal) ≠ 0 := by
    have h : (volume.addHaarScalarFactor μH[↑n]) ≠ 0 :=
      MeasureTheory.Measure.addHaarScalarFactor_volume_hausdorffMeasure_ne_zero n
    simpa [c_n] using h
  have hc_n_ne_top : (c_n : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hC_eil_ne_top : C_eil ≠ ⊤ := by
    have h1 : (c_d : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
    have h2 : (L2δ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
    have h3 : (c_n : ENNReal)⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr hc_n_pos
    have h4 : (L2δ : ENNReal) * (c_n : ENNReal)⁻¹ ≠ ⊤ := ENNReal.mul_ne_top h2 h3
    have h_div : C_eil = (c_d : ENNReal) * ((L2δ : ENNReal) * (c_n : ENNReal)⁻¹) := by
      simp [C_eil, div_eq_mul_inv] <;> ring
    rw [h_div]
    exact ENNReal.mul_ne_top h1 h4

  -- Explicit Eilenberg bound
  have h_eilenberg_explicit : ∀ (f : E n → ℝ), LipschitzWith L2δ f →
      ∀ (A : Set (E n)), ∫⁻ s : ℝ, μHE[n - 1] (A ∩ f ⁻¹' {s}) ≤ C_eil * volume A := by
    intro f hf A
    have hd_pos : 0 < (d : ℝ) := by exact_mod_cast (show 0 < n - 1 by omega)
    have h_d1 : (d : ℝ) + 1 = (n : ℝ) := by
      have h : d + 1 = n := by omega
      exact_mod_cast h
    have hμHE_d : (μHE[d] : Measure (E n)) = (c_d : ENNReal) • μH[d] :=
      MeasureTheory.Measure.euclideanHausdorffMeasure_def (d := d)
    have hμHE_n : (μHE[n] : Measure (E n)) = (c_n : ENNReal) • μH[n] :=
      MeasureTheory.Measure.euclideanHausdorffMeasure_def (d := n)
    have hμHE_n_eq_vol : (μHE[n] : Measure (E n)) = volume :=
      EuclideanSpace.euclideanHausdorffMeasure_eq_volume n
    have h1 : ∫⁻ (s : ℝ), μH[(d : ℝ)] (A ∩ f ⁻¹' {s}) ≤ (L2δ : ENNReal) * μH[(n : ℝ)] A := by
      have h_eil := EilenbergInequality.eilenberg_inequality (A := A) (hd := hd_pos) (hf := hf)
      rw [h_d1] at h_eil
      exact h_eil
    have h2 : ∫⁻ (s : ℝ), μHE[d] (A ∩ f ⁻¹' {s}) =
        (c_d : ENNReal) * ∫⁻ (s : ℝ), μH[(d : ℝ)] (A ∩ f ⁻¹' {s}) := by
      have h3 : ∀ s, μHE[d] (A ∩ f ⁻¹' {s}) =
          (c_d : ENNReal) * μH[(d : ℝ)] (A ∩ f ⁻¹' {s}) := by
        intro s; rw [hμHE_d]; simp [smul_apply] <;> rfl
      rw [lintegral_congr h3, lintegral_const_mul'] <;> simp
    have h4 : (c_n : ENNReal) * μH[n] A = volume A := by
      have h5 : (c_n : ENNReal) * μH[n] A = ((c_n : ENNReal) • μH[n]) A := by rfl
      have h6 : ((c_n : ENNReal) • μH[n]) A = (μHE[n] : Measure (E n)) A := by
        rw [hμHE_n.symm] <;> rfl
      have h7 : (μHE[n] : Measure (E n)) A = volume A := by
        rw [hμHE_n_eq_vol] <;> rfl
      rw [h5, h6, h7]
    have h_alg : (c_d : ENNReal) * ((L2δ : ENNReal) * μH[n] A) = C_eil * volume A := by
      have h8 : μH[(n : ℝ)] A = μH[n] A := by rfl
      have h9 : C_eil * (c_n : ENNReal) = (c_d : ENNReal) * (L2δ : ENNReal) := by
        have h10 : C_eil * (c_n : ENNReal) = ((c_d : ENNReal) * (L2δ : ENNReal) / (c_n : ENNReal)) * (c_n : ENNReal) := by rfl
        rw [h10]
        exact ENNReal.div_mul_cancel hc_n_pos hc_n_ne_top
      calc
        (c_d : ENNReal) * ((L2δ : ENNReal) * μH[n] A)
          = ((c_d : ENNReal) * (L2δ : ENNReal)) * μH[n] A := by rw [mul_assoc]
        _ = (C_eil * (c_n : ENNReal)) * μH[n] A := by rw [h9]
        _ = C_eil * ((c_n : ENNReal) * μH[n] A) := by rw [mul_assoc]
        _ = C_eil * volume A := by rw [h4]
    calc
      ∫⁻ (s : ℝ), μHE[d] (A ∩ f ⁻¹' {s})
        = (c_d : ENNReal) * ∫⁻ (s : ℝ), μH[(d : ℝ)] (A ∩ f ⁻¹' {s}) := h2
      _ ≤ (c_d : ENNReal) * ((L2δ : ENNReal) * μH[(n : ℝ)] A) := by gcongr
      _ = C_eil * volume A := h_alg

  -- For each i, extend u|_{A i} and apply explicit Eilenberg bound
  have h_main : ∀ i, ∫⁻ s : ℝ, μHE[n - 1] (A i ∩ {x | u x = s})
      ≤ C_eil * volume (A i) := by
    intro i
    rcases (h_lip_A i).extend_real with ⟨g, hg_lip, hg_eq⟩
    have h_set_eq : ∀ s : ℝ, A i ∩ {x | g x = s} = A i ∩ {x | u x = s} := by
      intro s
      ext y
      simp only [Set.mem_inter_iff]
      constructor
      · rintro ⟨h_y_in_Ai, hyg⟩
        have h_eq : u y = g y := hg_eq h_y_in_Ai
        have h_goal : u y = s := by rw [h_eq]; exact hyg
        exact ⟨h_y_in_Ai, h_goal⟩
      · rintro ⟨h_y_in_Ai, hyu⟩
        have h_eq : u y = g y := hg_eq h_y_in_Ai
        have h_goal : g y = s := by rw [←h_eq]; exact hyu
        exact ⟨h_y_in_Ai, h_goal⟩
    have h : ∫⁻ s : ℝ, μHE[n - 1] (A i ∩ {x | u x = s}) =
        ∫⁻ s : ℝ, μHE[n - 1] (A i ∩ {x | g x = s}) := by
      apply lintegral_congr
      intro s
      rw [h_set_eq s]
    rw [h]
    exact h_eilenberg_explicit g hg_lip (A i)

  -- Sum over disjoint pieces
  have h_level_union : ∀ s : ℝ, (Z ∩ {x | u x = s}) = ⋃ i, (A i ∩ {x | u x = s}) := by
    intro s
    ext y
    simp only [Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · rintro ⟨hyZ, hyu⟩
      have h2 : y ∈ ⋃ i, A i := by rw [hA_union]; exact hyZ
      rcases Set.mem_iUnion.mp h2 with ⟨i, hi⟩
      exact ⟨i, hi, hyu⟩
    · rintro ⟨i, hi, hyu⟩
      exact ⟨hi.1.1, hyu⟩

  have h_disj_level : ∀ s : ℝ, Pairwise (fun i j => Disjoint (A i ∩ {x | u x = s}) (A j ∩ {x | u x = s})) := by
    intro s i j hne
    have h : Disjoint (A i) (A j) := hA_disj hne
    exact h.mono (fun x hx => hx.1) (fun x hx => hx.1)

  have h_meas_level : ∀ i s, MeasurableSet (A i ∩ {x | u x = s}) := by
    intro i s
    have h1 : MeasurableSet (A i) := hA_meas i
    have h2 : MeasurableSet {x : E n | u x = s} :=
      isClosed_singleton.measurableSet.preimage hu.continuous.measurable
    exact h1.inter h2

  -- Strict positivity of L2δ
  have hL2δ_pos : (0 : ℝ) < (L2δ : ℝ) := by
    have h : 0 < (2 * δ : ℝ) := by positivity
    exact_mod_cast h
  have hL2δ_ne_zero : (L2δ : ℝ) ≠ 0 := hL2δ_pos.ne'
  have hL2δ_nnreal_pos : (L2δ : ENNReal) ≠ 0 := by exact_mod_cast hL2δ_ne_zero

  -- AEMeasurability of each level-set function (via Lipschitz extension + scaling)
  have h_ae : ∀ i, AEMeasurable (fun s : ℝ => μHE[n - 1] (A i ∩ {x | u x = s})) volume := by
    intro i
    rcases (h_lip_A i).extend_real with ⟨g, hg_lip, hg_eq⟩
    let v : E n → ℝ := fun x => g x / (L2δ : ℝ)
    have hv_lip : LipschitzWith 1 v := by
      have h_dist_le : ∀ x y, dist (v x) (v y) ≤ (1 : ℝ) * dist x y := by
        intro x y
        have h1 : dist (v x) (v y) = dist (g x) (g y) / (L2δ : ℝ) := by
          have h : dist (v x) (v y) = |(g x - g y) / (L2δ : ℝ)| := by
            simp [v, Real.dist_eq] <;> ring_nf
          rw [h, abs_div]
          have h2 : |(L2δ : ℝ)| = (L2δ : ℝ) := abs_of_pos hL2δ_pos
          rw [h2] <;> rfl
        rw [h1]
        have h2 : dist (g x) (g y) ≤ (L2δ : ℝ) * dist x y := by
          have h3 : edist (g x) (g y) ≤ (L2δ : ENNReal) * edist x y := hg_lip x y
          have h4 : ENNReal.ofReal (dist (g x) (g y)) ≤ ENNReal.ofReal ((L2δ : ℝ) * dist x y) := by
            have h5 : (L2δ : ENNReal) * edist x y = ENNReal.ofReal ((L2δ : ℝ) * dist x y) := by
              rw [edist_dist]
              have h_coe : (L2δ : ENNReal) = ENNReal.ofReal (L2δ : ℝ) := by
                simp [ENNReal.ofReal_coe_nnreal]
                <;> rfl
              rw [h_coe]
              have h6 : ENNReal.ofReal (L2δ : ℝ) * ENNReal.ofReal (dist x y) = ENNReal.ofReal ((L2δ : ℝ) * dist x y) := by
                rw [←ENNReal.ofReal_mul (show 0 ≤ (L2δ : ℝ) by positivity)]
                <;> rfl
              exact h6
            rw [h5] at h3
            rw [edist_dist] at h3
            exact h3
          have h_pos : 0 ≤ (L2δ : ℝ) * dist x y := by positivity
          have h_iff : ENNReal.ofReal (dist (g x) (g y)) ≤ ENNReal.ofReal ((L2δ : ℝ) * dist x y) ↔
              dist (g x) (g y) ≤ (L2δ : ℝ) * dist x y :=
            ENNReal.ofReal_le_ofReal_iff h_pos
          exact h_iff.mp h4
        calc
          dist (g x) (g y) / (L2δ : ℝ)
            ≤ ((L2δ : ℝ) * dist x y) / (L2δ : ℝ) := by gcongr
          _ = (1 : ℝ) * dist x y := by
            field_simp [hL2δ_ne_zero] <;> ring
      exact LipschitzWith.of_dist_le_mul h_dist_le
    have hA_bdd : Bornology.IsBounded (A i) := by
      have h : A i ⊆ B' i := hA_sub_B i
      exact Metric.isBounded_ball.subset h
    let g_fun : ℝ → ENNReal := fun t => μHE[n - 1] (A i ∩ {x | v x = t})
    have h_ae_v : AEMeasurable g_fun volume :=
      levelSet_aemeasurable_global hn hv_lip (hA_meas i) hA_bdd
    -- Relate u level sets to v level sets: {u=s} ∩ A_i = {v=s/L2δ} ∩ A_i
    have h_rel : ∀ s : ℝ, (A i ∩ {x | u x = s}) = (A i ∩ {x | v x = s / (L2δ : ℝ)}) := by
      intro s
      ext y
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
      constructor
      · rintro ⟨hyA, hyu⟩
        have h_eq : u y = g y := hg_eq hyA
        have h_gy : g y = s := by rw [←h_eq]; exact hyu
        have h_goal : v y = s / (L2δ : ℝ) := by
          dsimp only [v]
          rw [h_gy] <;> field_simp [hL2δ_ne_zero] <;> ring
        exact ⟨hyA, h_goal⟩
      · rintro ⟨hyA, hyv⟩
        have h_eq : u y = g y := hg_eq hyA
        have h_gy : g y / (L2δ : ℝ) = s / (L2δ : ℝ) := hyv
        have h_gy2 : g y = s := by
          field_simp [hL2δ_ne_zero] at h_gy <;> linarith
        have h_goal : u y = s := by
          rw [h_eq] <;> exact h_gy2
        exact ⟨hyA, h_goal⟩
    let scale : ℝ → ℝ := fun s => s / (L2δ : ℝ)
    have h_scale_meas : Measurable scale := by fun_prop
    have h_main_eq : (fun s : ℝ => μHE[n - 1] (A i ∩ {x | u x = s})) = g_fun ∘ scale := by
      funext s
      rw [h_rel s]
      <;> rfl
    rw [h_main_eq]
    -- comp_measurable needs AEMeasurable g_fun (map scale volume)
    -- Since scale is a nonzero linear map, map scale volume ≪ volume
    have h_ac : Measure.map scale volume ≪ volume := by
      have h_eq : Measure.map scale volume = (L2δ : ENNReal) • volume := by
        apply Measure.ext
        intro s hs
        rw [Measure.map_apply h_scale_meas hs]
        have h_scale_eq : scale = fun x : ℝ => (1 / (L2δ : ℝ)) * x := by
          funext x
          dsimp only [scale]
          rw [div_eq_mul_inv]
          <;> ring
        rw [h_scale_eq]
        rw [Real.volume_preimage_mul_left (show (1 / (L2δ : ℝ)) ≠ 0 by positivity) s]
        <;> simp
      rw [h_eq]
      intro s hs
      simpa [hs] using rfl
    rcases h_ae_v with ⟨h_meas, h_conj⟩
    have h_measurable : Measurable h_meas := h_conj.1
    have h_aeq : g_fun =ᵐ[volume] h_meas := h_conj.2
    have h_null : volume {x | g_fun x ≠ h_meas x} = 0 := by
      have h1 : ∀ᵐ x ∂volume, g_fun x = h_meas x := h_aeq
      exact (ae_iff).mp h1
    have h_null2 : (Measure.map scale volume) {x | g_fun x ≠ h_meas x} = 0 := h_ac h_null
    have h_eq : g_fun =ᵐ[Measure.map scale volume] h_meas := by
      have h2 : ∀ᵐ x ∂(Measure.map scale volume), g_fun x = h_meas x := (ae_iff).mpr h_null2
      exact h2
    have h_ae2 : AEMeasurable g_fun (Measure.map scale volume) :=
      ⟨h_meas, h_measurable, h_eq⟩
    exact h_ae2.comp_measurable h_scale_meas

  have h_sum1 : ∫⁻ s : ℝ, μHE[n - 1] (Z ∩ {x | u x = s}) =
      ∑' i, ∫⁻ s : ℝ, μHE[n - 1] (A i ∩ {x | u x = s}) := by
    have h_eq1 : ∀ s, μHE[n - 1] (Z ∩ {x | u x = s}) =
        ∑' i, μHE[n - 1] (A i ∩ {x | u x = s}) := by
      intro s
      rw [h_level_union s]
      exact MeasureTheory.measure_iUnion (h_disj_level s) (h_meas_level · s)
    have h_congr : ∫⁻ s : ℝ, μHE[n - 1] (Z ∩ {x | u x = s}) =
        ∫⁻ s : ℝ, ∑' i, μHE[n - 1] (A i ∩ {x | u x = s}) := by
      apply lintegral_congr
      intro s
      exact h_eq1 s
    rw [h_congr]
    rw [lintegral_tsum h_ae]

  have h6 : ∑' i, ∫⁻ s : ℝ, μHE[n - 1] (A i ∩ {x | u x = s}) ≤
      ∑' i, (C_eil * volume (A i)) := ENNReal.tsum_le_tsum h_main
  have h7 : ∑' i, (C_eil * volume (A i)) = C_eil * ∑' i, volume (A i) := by
    rw [ENNReal.tsum_mul_left]
  have h8 : ∑' i, volume (A i) = volume Z := by
    have h9 : volume (⋃ i, A i) = ∑' i, volume (A i) :=
      MeasureTheory.measure_iUnion hA_disj hA_meas
    have h10 : volume (⋃ i, A i) = volume Z := by rw [hA_union]
    rw [←h10, h9]
  have h_final : ∫⁻ s : ℝ, μHE[n - 1] (Z ∩ {x | u x = s}) ≤ C_eil * volume Z := by
    rw [h_sum1]
    have h9 : ∑' i, (C_eil * volume (A i)) = C_eil * volume Z := by
      rw [h7, h8]
    rw [h9] at h6
    exact h6

  exact ⟨C_eil, hC_eil_ne_top, h_final⟩

/-- Uniform constant for critical set Eilenberg bound, depending only on `n`. -/
noncomputable def criticalSetConstant (n : ℕ) : ENNReal :=
  let d : ℕ := n - 1
  let c_d : NNReal := MeasureTheory.Measure.addHaarScalarFactor
      (volume : Measure (E d)) (μH[d] : Measure (E d))
  let c_n : NNReal := MeasureTheory.Measure.addHaarScalarFactor
      (volume : Measure (E n)) (μH[n] : Measure (E n))
  (c_d : ENNReal) * 2 / (c_n : ENNReal)

/-- The critical set constant is finite. -/
lemma criticalSetConstant_ne_top (n : ℕ) (hn : 1 ≤ n) : criticalSetConstant n ≠ ⊤ := by
  let d : ℕ := n - 1
  let c_d : NNReal := MeasureTheory.Measure.addHaarScalarFactor
      (volume : Measure (E d)) (μH[d] : Measure (E d))
  let c_n : NNReal := MeasureTheory.Measure.addHaarScalarFactor
      (volume : Measure (E n)) (μH[n] : Measure (E n))
  have hc_n_pos : (c_n : ENNReal) ≠ 0 := by
    have h : (volume.addHaarScalarFactor μH[↑n]) ≠ 0 :=
      MeasureTheory.Measure.addHaarScalarFactor_volume_hausdorffMeasure_ne_zero n
    simpa [c_n] using h
  have h1 : (c_d : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have h2 : (2 : ENNReal) ≠ ⊤ := by simp
  have h3 : (c_n : ENNReal)⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr hc_n_pos
  have h4 : (2 : ENNReal) * (c_n : ENNReal)⁻¹ ≠ ⊤ := ENNReal.mul_ne_top h2 h3
  have h5 : (c_d : ENNReal) * ((2 : ENNReal) * (c_n : ENNReal)⁻¹) ≠ ⊤ := ENNReal.mul_ne_top h1 h4
  have h6 : criticalSetConstant n = (c_d : ENNReal) * ((2 : ENNReal) * (c_n : ENNReal)⁻¹) := by
    simp [criticalSetConstant, div_eq_mul_inv] <;> ring
  rw [h6]
  exact h5

/-- **Critical set bound for arbitrary subsets with explicit δ-scaling.**

For any bounded measurable `A ⊆ {‖∇u‖ < δ}`,
`∫ μHE(A ∩ {u=s}) ≤ criticalSetConstant n * δ * volume A`.
The constant depends only on `n`. -/
lemma critical_set_bound_explicit
    (u : E n → ℝ) (hu : ContDiff ℝ 1 u)
    (δ : ℝ) (hδ_pos : 0 < δ) (hn : 2 ≤ n)
    (A : Set (E n)) (hA : MeasurableSet A) (hA_bdd : Bornology.IsBounded A)
    (hA_sub : A ⊆ {x | ‖fderiv ℝ u x‖ < δ}) :
    ∫⁻ (s : ℝ), μHE[n - 1] (A ∩ {x | u x = s}) ≤
      criticalSetConstant n * ENNReal.ofReal δ * volume A := by
  classical
  let Z : Set (E n) := {x | ‖fderiv ℝ u x‖ < δ}
  have hZ_open : IsOpen Z := by
    have h1 : Continuous (fun x => ‖fderiv ℝ u x‖) :=
      (hu.continuous_fderiv (by norm_num)).norm
    exact h1.isOpen_preimage _ isOpen_Iio
  have hZ_meas : MeasurableSet Z := hZ_open.measurableSet

  -- For each x ∈ A, find a ball where ‖∇u‖ < 2δ
  have h_cover : ∀ (x : E n), x ∈ A → ∃ (r : ℝ), 0 < r ∧
      (∀ y ∈ ball x r, ‖fderiv ℝ u y‖ < 2 * δ) := by
    intro x hx
    have h1 : ‖fderiv ℝ u x‖ < δ := hA_sub hx
    have h2 : ‖fderiv ℝ u x‖ < 2 * δ := by linarith
    have h_set_open : IsOpen {y : E n | ‖fderiv ℝ u y‖ < 2 * δ} := by
      have h_cont : Continuous (fun y => ‖fderiv ℝ u y‖) :=
        (hu.continuous_fderiv (by norm_num)).norm
      exact h_cont.isOpen_preimage _ isOpen_Iio
    have h_nhds : {y : E n | ‖fderiv ℝ u y‖ < 2 * δ} ∈ nhds x :=
      h_set_open.mem_nhds h2
    rcases Metric.mem_nhds_iff.mp h_nhds with ⟨r, hr_pos, hr⟩
    exact ⟨r, hr_pos, fun y hy => hr hy⟩

  let r : E n → ℝ := fun x => if hx : x ∈ A
    then Classical.choose (h_cover x hx)
    else 0
  have hr_pos : ∀ (x : E n), x ∈ A → 0 < r x := by
    intro x hx
    have h1 : r x = Classical.choose (h_cover x hx) := by simp [r, hx]
    rw [h1]; exact (Classical.choose_spec (h_cover x hx)).1
  have hr_ball : ∀ (x : E n), x ∈ A →
      ∀ y ∈ ball x (r x), ‖fderiv ℝ u y‖ < 2 * δ := by
    intro x hx
    have h1 : r x = Classical.choose (h_cover x hx) := by simp [r, hx]
    rw [h1]; exact (Classical.choose_spec (h_cover x hx)).2

  let B : E n → Set (E n) := fun x => ball x (r x)
  have hB_open : ∀ x, IsOpen (B x) := fun _ => isOpen_ball
  have h_coverA : A ⊆ ⋃ (x : E n), B x := by
    intro y hy
    have h2 : y ∈ B y := mem_ball_self (hr_pos y hy)
    exact Set.mem_iUnion.mpr ⟨y, h2⟩

  have hA_lindelof : IsLindelof A := HereditarilyLindelofSpace.isLindelof A
  rcases IsLindelof.indexed_countable_subcover hA_lindelof B hB_open h_coverA
    with ⟨x', h_cover'⟩

  let B' : ℕ → Set (E n) := fun i => B (x' i)
  have hB'_open : ∀ i, IsOpen (B' i) := fun i => hB_open (x' i)

  -- Disjointify the cover
  let V : ℕ → Set (E n) := fun i =>
    B' i \ ⋃ j ∈ Finset.range i, B' j
  let S : ℕ → Set (E n) := fun i => A ∩ V i

  have hV_meas : ∀ i, MeasurableSet (V i) := by
    intro i
    have h1 : MeasurableSet (B' i) := (hB'_open i).measurableSet
    have h2 : MeasurableSet (⋃ j ∈ Finset.range i, B' j) := by
      apply MeasurableSet.biUnion
      · exact Finset.countable_toSet _
      · intro j _; exact (hB'_open j).measurableSet
    exact h1.diff h2

  have hS_meas : ∀ i, MeasurableSet (S i) :=
    fun i => hA.inter (hV_meas i)

  have hV_sub : ∀ i, V i ⊆ B' i := by
    intro i x hx; exact hx.1

  have hS_sub_B : ∀ i, S i ⊆ B' i := by
    intro i x hx; exact hV_sub i hx.2

  have hS_sub_A : ∀ i, S i ⊆ A := by
    intro i x hx; exact hx.1

  have h_disj : Pairwise (fun i j : ℕ => Disjoint (V i) (V j)) := by
    intro i j hne
    by_cases h : i < j
    · have h6 : V j ⊆ (B' j) \ B' i := by
        intro x hx
        have h7 : x ∈ B' j := hx.1
        have h8 : x ∉ ⋃ k ∈ Finset.range j, B' k := hx.2
        have h9 : x ∉ B' i := by
          intro h10
          have h11 : x ∈ ⋃ k ∈ Finset.range j, B' k := by
            apply Set.mem_iUnion₂.mpr
            exact ⟨i, Finset.mem_range.mpr h, h10⟩
          exact h8 h11
        exact ⟨h7, h9⟩
      have h7 : Disjoint (V i) ((B' j) \ B' i) := by
        rw [Set.disjoint_left]; intro x hxi hxj
        exact hxj.2 (hV_sub i hxi)
      exact h7.mono_right h6
    · have h' : j < i := by omega
      have h6 : V i ⊆ (B' i) \ B' j := by
        intro x hx
        have h7 : x ∈ B' i := hx.1
        have h8 : x ∉ ⋃ k ∈ Finset.range i, B' k := hx.2
        have h9 : x ∉ B' j := by
          intro h10
          have h11 : x ∈ ⋃ k ∈ Finset.range i, B' k := by
            apply Set.mem_iUnion₂.mpr
            exact ⟨j, Finset.mem_range.mpr h', h10⟩
          exact h8 h11
        exact ⟨h7, h9⟩
      have h7 : Disjoint (V j) ((B' i) \ B' j) := by
        rw [Set.disjoint_left]; intro x hxj hxi
        exact hxi.2 (hV_sub j hxj)
      exact (h7.mono_right h6).symm

  have hS_disj : Pairwise (fun i j : ℕ => Disjoint (S i) (S j)) := by
    intro i j hne
    have h : Disjoint (V i) (V j) := h_disj hne
    exact h.mono (fun x hx => hx.2) (fun x hx => hx.2)

  have h_union_V : (⋃ i, V i) = ⋃ i, B' i := by
    ext x
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨i, hi⟩; exact ⟨i, hV_sub i hi⟩
    · intro h
      let P : ℕ → Prop := fun j => x ∈ B' j
      have hP : ∃ j, P j := by rcases h with ⟨i, hi⟩; exact ⟨i, hi⟩
      let k : ℕ := Nat.find hP
      have hk : P k := Nat.find_spec hP
      have hmin : ∀ j < k, ¬ P j := by intro j hj; exact Nat.find_min hP hj
      have hk2 : x ∈ V k := by
        constructor
        · exact hk
        · intro h2
          rcases Set.mem_iUnion₂.mp h2 with ⟨j, hj_range, hj_B⟩
          have h_j_lt_k : j < k := Finset.mem_range.mp hj_range
          exact hmin j h_j_lt_k hj_B
      exact ⟨k, hk2⟩

  have hS_union : (⋃ i, S i) = A := by
    ext x
    constructor
    · intro hx
      rcases Set.mem_iUnion.mp hx with ⟨i, hi⟩
      exact hi.1
    · intro hx
      have h2 : x ∈ ⋃ i, V i := by
        have h3 : x ∈ ⋃ i, B' i := h_cover' hx
        rw [←h_union_V] at h3
        exact h3
      rcases Set.mem_iUnion.mp h2 with ⟨idx, hidx⟩
      have h3 : x ∈ S idx := ⟨hx, hidx⟩
      exact Set.mem_iUnion.mpr ⟨idx, h3⟩

  -- u is 2δ-Lipschitz on each B' i
  let L2δ : NNReal := ⟨2 * δ, by positivity⟩
  have h_lip_ball : ∀ i, LipschitzOnWith L2δ u (B' i) := by
    intro i
    by_cases hxi : x' i ∈ A
    · have h1 : ∀ y ∈ B' i, ‖fderiv ℝ u y‖ < 2 * δ := hr_ball (x' i) hxi
      have h2 : ∀ y ∈ B' i, ‖fderiv ℝ u y‖₊ ≤ L2δ := by
        intro y hy
        have h3 : ‖fderiv ℝ u y‖ < 2 * δ := h1 y hy
        have h4 : ‖fderiv ℝ u y‖₊ = ⟨‖fderiv ℝ u y‖, norm_nonneg _⟩ := by rfl
        rw [h4]
        exact NNReal.coe_le_coe.mpr h3.le
      have h_diff : ∀ y ∈ B' i, DifferentiableAt ℝ u y := by
        intro y _; exact (hu.differentiable (by norm_num)).differentiableAt
      have h_conv : Convex ℝ (B' i) := by
        have h : B' i = ball (x' i) (r (x' i)) := by rfl
        rw [h]
        exact convex_ball (x' i) (r (x' i))
      exact h_conv.lipschitzOnWith_of_nnnorm_fderiv_le h_diff h2
    · have hri0 : r (x' i) = 0 := by simp [r, hxi]
      have hB_empty : B' i = ∅ := by
        have h : B' i = ball (x' i) (r (x' i)) := by rfl
        rw [h, hri0]
        ext y; simp [Metric.mem_ball] <;> linarith
      rw [hB_empty]
      simp

  have h_lip_S : ∀ i, LipschitzOnWith L2δ u (S i) := by
    intro i
    exact (h_lip_ball i).mono (hS_sub_B i)

  -- Eilenberg constant
  let d : ℕ := n - 1
  let c_d : NNReal := MeasureTheory.Measure.addHaarScalarFactor
      (volume : Measure (E d)) (μH[d] : Measure (E d))
  let c_n : NNReal := MeasureTheory.Measure.addHaarScalarFactor
      (volume : Measure (E n)) (μH[n] : Measure (E n))
  let C_eil : ENNReal := (c_d : ENNReal) * (L2δ : ENNReal) / (c_n : ENNReal)
  let K : ENNReal := criticalSetConstant n

  have hc_d_pos : (c_d : ENNReal) ≠ 0 := by
    have h : (volume.addHaarScalarFactor μH[↑d]) ≠ 0 :=
      MeasureTheory.Measure.addHaarScalarFactor_volume_hausdorffMeasure_ne_zero d
    simpa [c_d] using h
  have hc_n_pos : (c_n : ENNReal) ≠ 0 := by
    have h : (volume.addHaarScalarFactor μH[↑n]) ≠ 0 :=
      MeasureTheory.Measure.addHaarScalarFactor_volume_hausdorffMeasure_ne_zero n
    simpa [c_n] using h
  have hc_n_ne_top : (c_n : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hK_ne_top : K ≠ ⊤ := by
    have h1 : (c_d : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
    have h2 : (2 : ENNReal) ≠ ⊤ := by simp
    have h3 : (c_n : ENNReal)⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr hc_n_pos
    have h4 : (2 : ENNReal) * (c_n : ENNReal)⁻¹ ≠ ⊤ := ENNReal.mul_ne_top h2 h3
    have h_div : K = (c_d : ENNReal) * ((2 : ENNReal) * (c_n : ENNReal)⁻¹) := by
      have hK_eq : K = criticalSetConstant n := by rfl
      rw [hK_eq]
      simp [criticalSetConstant, div_eq_mul_inv] <;> ring
    rw [h_div]
    exact ENNReal.mul_ne_top h1 h4

  have hC_eil_eq : C_eil = K * ENNReal.ofReal δ := by
    have h1 : (L2δ : ENNReal) = 2 * ENNReal.ofReal δ := by
      have h2 : (L2δ : ℝ) = 2 * δ := by
        change (↑(⟨2 * δ, by positivity⟩ : NNReal) : ℝ) = 2 * δ
        <;> simp
      have h3 : (L2δ : ENNReal) = ENNReal.ofReal (L2δ : ℝ) := by
        exact coe_nnreal_eq L2δ
      rw [h3, h2]
      have h4 : ENNReal.ofReal (2 * δ) = ENNReal.ofReal 2 * ENNReal.ofReal δ := by
        rw [ENNReal.ofReal_mul (by positivity)]
      rw [h4]
      have h5 : ENNReal.ofReal (2 : ℝ) = (2 : ENNReal) := by simp
      rw [h5] <;> ring
    have h5 : C_eil = (c_d : ENNReal) * (L2δ : ENNReal) / (c_n : ENNReal) := by rfl
    rw [h5, h1]
    have h6 : (c_d : ENNReal) * (2 * ENNReal.ofReal δ) / (c_n : ENNReal) =
        ((c_d : ENNReal) * 2 / (c_n : ENNReal)) * ENNReal.ofReal δ := by
      simp [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] <;> ring
    rw [h6] <;> rfl

  -- Explicit Eilenberg bound for a globally L2δ-Lipschitz function
  have h_eilenberg_explicit : ∀ (f : E n → ℝ), LipschitzWith L2δ f →
      ∀ (X : Set (E n)), ∫⁻ s : ℝ, μHE[n - 1] (X ∩ f ⁻¹' {s}) ≤ C_eil * volume X := by
    intro f hf X
    have hd_pos : 0 < (d : ℝ) := by exact_mod_cast (show 0 < n - 1 by omega)
    have h_d1 : (d : ℝ) + 1 = (n : ℝ) := by
      have h : d + 1 = n := by omega
      exact_mod_cast h
    have hμHE_d : (μHE[d] : Measure (E n)) = (c_d : ENNReal) • μH[d] :=
      MeasureTheory.Measure.euclideanHausdorffMeasure_def (d := d)
    have hμHE_n : (μHE[n] : Measure (E n)) = (c_n : ENNReal) • μH[n] :=
      MeasureTheory.Measure.euclideanHausdorffMeasure_def (d := n)
    have hμHE_n_eq_vol : (μHE[n] : Measure (E n)) = volume :=
      EuclideanSpace.euclideanHausdorffMeasure_eq_volume n
    have h1 : ∫⁻ (s : ℝ), μH[(d : ℝ)] (X ∩ f ⁻¹' {s}) ≤ (L2δ : ENNReal) * μH[(n : ℝ)] X := by
      have h_eil := EilenbergInequality.eilenberg_inequality (A := X) (hd := hd_pos) (hf := hf)
      rw [h_d1] at h_eil
      exact h_eil
    have h2 : ∫⁻ (s : ℝ), μHE[d] (X ∩ f ⁻¹' {s}) =
        (c_d : ENNReal) * ∫⁻ (s : ℝ), μH[(d : ℝ)] (X ∩ f ⁻¹' {s}) := by
      have h3 : ∀ s, μHE[d] (X ∩ f ⁻¹' {s}) =
          (c_d : ENNReal) * μH[(d : ℝ)] (X ∩ f ⁻¹' {s}) := by
        intro s; rw [hμHE_d]; simp [smul_apply] <;> rfl
      rw [lintegral_congr h3, lintegral_const_mul'] <;> simp
    have h4 : (c_n : ENNReal) * μH[n] X = volume X := by
      have h5 : (c_n : ENNReal) * μH[n] X = ((c_n : ENNReal) • μH[n]) X := by rfl
      have h6 : ((c_n : ENNReal) • μH[n]) X = (μHE[n] : Measure (E n)) X := by
        rw [hμHE_n.symm] <;> rfl
      have h7 : (μHE[n] : Measure (E n)) X = volume X := by
        rw [hμHE_n_eq_vol] <;> rfl
      rw [h5, h6, h7]
    have h_alg : (c_d : ENNReal) * ((L2δ : ENNReal) * μH[n] X) = C_eil * volume X := by
      have h8 : μH[(n : ℝ)] X = μH[n] X := by rfl
      have h9 : C_eil * (c_n : ENNReal) = (c_d : ENNReal) * (L2δ : ENNReal) := by
        have h10 : C_eil * (c_n : ENNReal) = ((c_d : ENNReal) * (L2δ : ENNReal) / (c_n : ENNReal)) * (c_n : ENNReal) := by rfl
        rw [h10]
        exact ENNReal.div_mul_cancel hc_n_pos hc_n_ne_top
      calc
        (c_d : ENNReal) * ((L2δ : ENNReal) * μH[n] X)
          = ((c_d : ENNReal) * (L2δ : ENNReal)) * μH[n] X := by rw [mul_assoc]
        _ = (C_eil * (c_n : ENNReal)) * μH[n] X := by rw [h9]
        _ = C_eil * ((c_n : ENNReal) * μH[n] X) := by rw [mul_assoc]
        _ = C_eil * volume X := by rw [h4]
    calc
      ∫⁻ (s : ℝ), μHE[d] (X ∩ f ⁻¹' {s})
        = (c_d : ENNReal) * ∫⁻ (s : ℝ), μH[(d : ℝ)] (X ∩ f ⁻¹' {s}) := h2
      _ ≤ (c_d : ENNReal) * ((L2δ : ENNReal) * μH[(n : ℝ)] X) := by gcongr
      _ = C_eil * volume X := h_alg

  -- For each i, extend u|_{S i} and apply explicit Eilenberg bound
  have h_main : ∀ i, ∫⁻ s : ℝ, μHE[n - 1] (S i ∩ {x | u x = s})
      ≤ C_eil * volume (S i) := by
    intro i
    rcases (h_lip_S i).extend_real with ⟨g, hg_lip, hg_eq⟩
    have h_set_eq : ∀ s : ℝ, S i ∩ {x | g x = s} = S i ∩ {x | u x = s} := by
      intro s
      ext y
      simp only [Set.mem_inter_iff]
      constructor
      · rintro ⟨h_y_in_Si, hyg⟩
        have h_eq : u y = g y := hg_eq h_y_in_Si
        have h_goal : u y = s := by rw [h_eq]; exact hyg
        exact ⟨h_y_in_Si, h_goal⟩
      · rintro ⟨h_y_in_Si, hyu⟩
        have h_eq : u y = g y := hg_eq h_y_in_Si
        have h_goal : g y = s := by rw [←h_eq]; exact hyu
        exact ⟨h_y_in_Si, h_goal⟩
    have h : ∫⁻ s : ℝ, μHE[n - 1] (S i ∩ {x | u x = s}) =
        ∫⁻ s : ℝ, μHE[n - 1] (S i ∩ {x | g x = s}) := by
      apply lintegral_congr
      intro s
      rw [h_set_eq s]
    rw [h]
    exact h_eilenberg_explicit g hg_lip (S i)

  -- Level set union and disjointness
  have h_level_union : ∀ s : ℝ, (A ∩ {x | u x = s}) = ⋃ i, (S i ∩ {x | u x = s}) := by
    intro s
    ext y
    simp only [Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · rintro ⟨hyA, hyu⟩
      have h2 : y ∈ ⋃ i, S i := by rw [hS_union]; exact hyA
      rcases Set.mem_iUnion.mp h2 with ⟨i, hi⟩
      exact ⟨i, hi, hyu⟩
    · rintro ⟨i, hi, hyu⟩
      exact ⟨hi.1, hyu⟩

  have h_disj_level : ∀ s : ℝ, Pairwise (fun i j => Disjoint (S i ∩ {x | u x = s}) (S j ∩ {x | u x = s})) := by
    intro s i j hne
    have h : Disjoint (S i) (S j) := hS_disj hne
    exact h.mono (fun x hx => hx.1) (fun x hx => hx.1)

  have h_meas_level : ∀ i s, MeasurableSet (S i ∩ {x | u x = s}) := by
    intro i s
    have h1 : MeasurableSet (S i) := hS_meas i
    have h2 : MeasurableSet {x : E n | u x = s} :=
      isClosed_singleton.measurableSet.preimage hu.continuous.measurable
    exact h1.inter h2

  -- AEMeasurability of each level-set function
  have hL2δ_pos : (0 : ℝ) < (L2δ : ℝ) := by
    have h : 0 < (2 * δ : ℝ) := by positivity
    exact_mod_cast h
  have hL2δ_ne_zero : (L2δ : ℝ) ≠ 0 := hL2δ_pos.ne'

  have h_ae : ∀ i, AEMeasurable (fun s : ℝ => μHE[n - 1] (S i ∩ {x | u x = s})) volume := by
    intro i
    rcases (h_lip_S i).extend_real with ⟨g, hg_lip, hg_eq⟩
    let v : E n → ℝ := fun x => g x / (L2δ : ℝ)
    have hv_lip : LipschitzWith 1 v := by
      have h_dist_le : ∀ x y, dist (v x) (v y) ≤ (1 : ℝ) * dist x y := by
        intro x y
        have h1 : dist (v x) (v y) = dist (g x) (g y) / (L2δ : ℝ) := by
          have h : dist (v x) (v y) = |(g x - g y) / (L2δ : ℝ)| := by
            simp [v, Real.dist_eq] <;> ring_nf
          rw [h, abs_div]
          have h2 : |(L2δ : ℝ)| = (L2δ : ℝ) := abs_of_pos hL2δ_pos
          rw [h2] <;> rfl
        rw [h1]
        have h2 : dist (g x) (g y) ≤ (L2δ : ℝ) * dist x y := by
          have h3 : edist (g x) (g y) ≤ (L2δ : ENNReal) * edist x y := hg_lip x y
          have h4 : ENNReal.ofReal (dist (g x) (g y)) ≤ ENNReal.ofReal ((L2δ : ℝ) * dist x y) := by
            have h5 : (L2δ : ENNReal) * edist x y = ENNReal.ofReal ((L2δ : ℝ) * dist x y) := by
              rw [edist_dist]
              have h_coe : (L2δ : ENNReal) = ENNReal.ofReal (L2δ : ℝ) := by
                simp [ENNReal.ofReal_coe_nnreal] <;> rfl
              rw [h_coe]
              have h6 : ENNReal.ofReal (L2δ : ℝ) * ENNReal.ofReal (dist x y) = ENNReal.ofReal ((L2δ : ℝ) * dist x y) := by
                rw [←ENNReal.ofReal_mul (show 0 ≤ (L2δ : ℝ) by positivity)] <;> rfl
              exact h6
            rw [h5] at h3
            rw [edist_dist] at h3
            exact h3
          have h_pos : 0 ≤ (L2δ : ℝ) * dist x y := by positivity
          have h_iff : ENNReal.ofReal (dist (g x) (g y)) ≤ ENNReal.ofReal ((L2δ : ℝ) * dist x y) ↔
              dist (g x) (g y) ≤ (L2δ : ℝ) * dist x y :=
            ENNReal.ofReal_le_ofReal_iff h_pos
          exact h_iff.mp h4
        calc
          dist (g x) (g y) / (L2δ : ℝ)
            ≤ ((L2δ : ℝ) * dist x y) / (L2δ : ℝ) := by gcongr
          _ = (1 : ℝ) * dist x y := by
            field_simp [hL2δ_ne_zero] <;> ring
      exact LipschitzWith.of_dist_le_mul h_dist_le
    have hS_bdd : Bornology.IsBounded (S i) := by
      have h : S i ⊆ B' i := hS_sub_B i
      exact Metric.isBounded_ball.subset h
    let g_fun : ℝ → ENNReal := fun t => μHE[n - 1] (S i ∩ {x | v x = t})
    have h_ae_v : AEMeasurable g_fun volume :=
      levelSet_aemeasurable_global hn hv_lip (hS_meas i) hS_bdd
    have h_rel : ∀ s : ℝ, (S i ∩ {x | u x = s}) = (S i ∩ {x | v x = s / (L2δ : ℝ)}) := by
      intro s
      ext y
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
      constructor
      · rintro ⟨hyA, hyu⟩
        have h_eq : u y = g y := hg_eq hyA
        have h_gy : g y = s := by rw [←h_eq]; exact hyu
        have h_goal : v y = s / (L2δ : ℝ) := by
          dsimp only [v]
          rw [h_gy] <;> field_simp [hL2δ_ne_zero] <;> ring
        exact ⟨hyA, h_goal⟩
      · rintro ⟨hyA, hyv⟩
        have h_eq : u y = g y := hg_eq hyA
        have h_gy : g y / (L2δ : ℝ) = s / (L2δ : ℝ) := hyv
        have h_gy2 : g y = s := by
          field_simp [hL2δ_ne_zero] at h_gy <;> linarith
        have h_goal : u y = s := by
          rw [h_eq] <;> exact h_gy2
        exact ⟨hyA, h_goal⟩
    let scale : ℝ → ℝ := fun s => s / (L2δ : ℝ)
    have h_scale_meas : Measurable scale := by fun_prop
    have h_main_eq : (fun s : ℝ => μHE[n - 1] (S i ∩ {x | u x = s})) = g_fun ∘ scale := by
      funext s
      rw [h_rel s] <;> rfl
    rw [h_main_eq]
    have h_ac : Measure.map scale volume ≪ volume := by
      have h_eq : Measure.map scale volume = (L2δ : ENNReal) • volume := by
        apply Measure.ext
        intro s hs
        rw [Measure.map_apply h_scale_meas hs]
        have h_scale_eq : scale = fun x : ℝ => (1 / (L2δ : ℝ)) * x := by
          funext x
          dsimp only [scale]
          rw [div_eq_mul_inv] <;> ring
        rw [h_scale_eq]
        rw [Real.volume_preimage_mul_left (show (1 / (L2δ : ℝ)) ≠ 0 by positivity) s]
        <;> simp
      rw [h_eq]
      intro s hs
      simpa [hs] using rfl
    rcases h_ae_v with ⟨h_meas, h_conj⟩
    have h_measurable : Measurable h_meas := h_conj.1
    have h_aeq : g_fun =ᵐ[volume] h_meas := h_conj.2
    have h_null : volume {x | g_fun x ≠ h_meas x} = 0 := by
      have h1 : ∀ᵐ x ∂volume, g_fun x = h_meas x := h_aeq
      exact (ae_iff).mp h1
    have h_null2 : (Measure.map scale volume) {x | g_fun x ≠ h_meas x} = 0 := h_ac h_null
    have h_eq : g_fun =ᵐ[Measure.map scale volume] h_meas := by
      have h2 : ∀ᵐ x ∂(Measure.map scale volume), g_fun x = h_meas x := (ae_iff).mpr h_null2
      exact h2
    have h_ae2 : AEMeasurable g_fun (Measure.map scale volume) :=
      ⟨h_meas, h_measurable, h_eq⟩
    exact h_ae2.comp_measurable h_scale_meas

  -- Sum over disjoint pieces
  have h_sum1 : ∫⁻ s : ℝ, μHE[n - 1] (A ∩ {x | u x = s}) =
      ∑' i, ∫⁻ s : ℝ, μHE[n - 1] (S i ∩ {x | u x = s}) := by
    have h_eq1 : ∀ s, μHE[n - 1] (A ∩ {x | u x = s}) =
        ∑' i, μHE[n - 1] (S i ∩ {x | u x = s}) := by
      intro s
      rw [h_level_union s]
      exact MeasureTheory.measure_iUnion (h_disj_level s) (h_meas_level · s)
    have h_congr : ∫⁻ s : ℝ, μHE[n - 1] (A ∩ {x | u x = s}) =
        ∫⁻ s : ℝ, ∑' i, μHE[n - 1] (S i ∩ {x | u x = s}) := by
      apply lintegral_congr
      intro s
      exact h_eq1 s
    rw [h_congr]
    rw [lintegral_tsum h_ae]

  have h6 : ∑' i, ∫⁻ s : ℝ, μHE[n - 1] (S i ∩ {x | u x = s}) ≤
      ∑' i, (C_eil * volume (S i)) := ENNReal.tsum_le_tsum h_main
  have h7 : ∑' i, (C_eil * volume (S i)) = C_eil * ∑' i, volume (S i) := by
    rw [ENNReal.tsum_mul_left]
  have h8 : ∑' i, volume (S i) = volume A := by
    have h9 : volume (⋃ i, S i) = ∑' i, volume (S i) :=
      MeasureTheory.measure_iUnion hS_disj hS_meas
    have h10 : volume (⋃ i, S i) = volume A := by rw [hS_union]
    rw [←h10, h9]
  have h_final : ∫⁻ s : ℝ, μHE[n - 1] (A ∩ {x | u x = s}) ≤ C_eil * volume A := by
    rw [h_sum1]
    have h9 : ∑' i, (C_eil * volume (S i)) = C_eil * volume A := by
      rw [h7, h8]
    rw [h9] at h6
    exact h6

  have h_final2 : ∫⁻ s : ℝ, μHE[n - 1] (A ∩ {x | u x = s}) ≤
      K * ENNReal.ofReal δ * volume A := by
    rw [hC_eil_eq] at h_final
    exact h_final

  exact h_final2

/-- **Critical set bound for arbitrary subsets (existential form).**

For any bounded measurable `A ⊆ {‖∇u‖ < δ}`, there exists a finite constant `K`
such that `∫ μHE(A ∩ {u=s}) ≤ K * δ * volume A`. -/
lemma critical_set_bound_subset
    (u : E n → ℝ) (hu : ContDiff ℝ 1 u)
    (δ : ℝ) (hδ_pos : 0 < δ) (hn : 2 ≤ n)
    (A : Set (E n)) (hA : MeasurableSet A) (hA_bdd : Bornology.IsBounded A)
    (hA_sub : A ⊆ {x | ‖fderiv ℝ u x‖ < δ}) :
    ∃ (K : ENNReal), K ≠ ⊤ ∧
      ∫⁻ (s : ℝ), μHE[n - 1] (A ∩ {x | u x = s}) ≤
        K * ENNReal.ofReal δ * volume A := by
  have h_main := critical_set_bound_explicit u hu δ hδ_pos hn A hA hA_bdd hA_sub
  have hK_ne_top : criticalSetConstant n ≠ ⊤ := criticalSetConstant_ne_top n (by linarith)
  exact ⟨criticalSetConstant n, hK_ne_top, h_main⟩

end Geometry
