import MyLeanRepo.Kakeya.CV.Isoperimetric.InnerMinkowski.Basic
import MyLeanRepo.Kakeya.CV.Isoperimetric.Perimeter.PerimeterDefinition
import MyLeanRepo.Kakeya.CV.Isoperimetric.Perimeter.CutoffFunctions
import MyLeanRepo.Kakeya.CV.Isoperimetric.Perimeter.NonSharpIsoperimetric
import MyLeanRepo.Kakeya.CV.Isoperimetric.StructureTheorem.DistributionalDerivative
import MyLeanRepo.Kakeya.CV.Isoperimetric.StructureTheorem.TrueReducedBoundary
import MyLeanRepo.Kakeya.CV.Isoperimetric.StructureTheorem.PerimeterDensityUpperBound
import MyLeanRepo.Kakeya.CV.Isoperimetric.StructureTheorem.TwoSidedDensity
import MyLeanRepo.Kakeya.CV.Isoperimetric.Perimeter.IntersectionBallStub
import MyLeanRepo.Kakeya.CV.Isoperimetric.Coarea.DistanceCoareaEq
import MyLeanRepo.Kakeya.CV.Isoperimetric.Coarea.DistanceCoareaAEMeasurable
import MyLeanRepo.Kakeya.CV.Isoperimetric.Coarea.CoareaIntegral
import MyLeanRepo.Kakeya.CV.Isoperimetric.StructureTheorem.VectorMeasureInner
import MyLeanRepo.Kakeya.CV.Isoperimetric.StructureTheorem.SphereHausdorff
import MyLeanRepo.Kakeya.CV.Isoperimetric.StructureTheorem.PerimeterMeasureSupport
import MyLeanRepo.Kakeya.CV.Isoperimetric.StructureTheorem.ComplLocalityBasics
import MyLeanRepo.Kakeya.CV.Isoperimetric.Perimeter.IntersectionBallHelpers
import MyLeanRepo.Kakeya.CV.Isoperimetric.StructureTheorem.DensityEstimates
import MyLeanRepo.Kakeya.CV.Isoperimetric.Measure.Eilenberg
import Mathlib.Tactic

/-!
# Maggi Theorem 15.5: Volume Lower Density at Reduced Boundary

Proves Steps 1-2 of Maggi's Theorem 15.5:

**Step 1**: At a reduced boundary point x, for a.e. sufficiently small r:
`P(E; B(x,r)) ≤ 2 H^{n-1}(E ∩ ∂B(x,r))`

**Step 2**: Volume lower density:
`|E ∩ B(x,r)| ≥ (r / (3n))^n` and `|B(x,r) \\ E| ≥ (r / (3n))^n`

## Proof route

1. **Polar bound** (from Besicovitch differentiation):
   `μ(B(x,r)) ≤ 2 |Dχ_U(B(x,r)) · ν_E(x)|` for small r.

2. **Tight cutoff inequality**:
   `|Dχ_U(B(x,r)) · ν| ≤ H^{n-1}(U ∩ sphere(x,r))` for a.e. r.
   Proof via radial cutoff limit and coarea formula.

3. **Combine**: `μ(B(x,r)) ≤ 2 H^{n-1}(U ∩ sphere(x,r))`.

4. **Intersection perimeter bound**:
   `P(U ∩ B(x,r)) ≤ P(U; B(x,r)) + H^{n-1}(U ∩ sphere(x,r)) ≤ 3 H^{n-1}(U ∩ sphere(x,r))`.

5. **Global isoperimetric**: `m(r)^α ≤ P(U ∩ B(x,r)) ≤ 3 m'(r)`.

6. **Integrate differential inequality**: `m(r) ≥ (r/(3n))^n`.

## References
- Maggi, Sets of Finite Perimeter, Theorem 15.5, Steps 1-2 (pp. 175-178)
-/


open MeasureTheory Metric Set ENNReal Filter
open scoped MeasureTheory ContDiff

namespace Geometry.StructureTheorem

open Perimeter

variable {n : ℕ}

-- ============================================================================
-- Weighted distance coarea formula
-- ============================================================================

/-- Weighted distance coarea formula: for a bounded measurable set `A`,
`∫ y in A, g (dist y x) = ∫ t > 0, g t * H^{n-1}(A ∩ sphere x t)`. -/
lemma weighted_distance_coarea
    {A : Set (E n)} (hA : MeasurableSet A) (hA_bdd : Bornology.IsBounded A)
    (x : E n) (g : ℝ → ℝ) (hg_nonneg : ∀ t, 0 ≤ g t) (hg_cont : Continuous g)
    (hn : 2 ≤ n) :
    ∫ y in A, g (dist y x) =
      ∫ t in Set.Ioi 0, g t * (μHE[n - 1] (A ∩ sphere x t)).toReal := by
  letI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  let d : E n → ℝ := fun y => dist y x
  let A' := A \ {x}
  have hA'_meas : MeasurableSet A' := hA.diff (measurableSet_singleton x)
  have hA'_sub1 : A' ⊆ A := fun y hy => hy.1

  rcases hA_bdd with ⟨t, ht_in, ht_sub⟩
  have hA'_bdd : Bornology.IsBounded A' := by
    have h1 : WithLp.ofLp ⁻¹' t ⊆ (A')ᶜ :=
      subset_trans ht_sub (compl_subset_compl.mpr hA'_sub1)
    exact ⟨t, ht_in, h1⟩
  have hA_bdd' : Bornology.IsBounded A := ⟨t, ht_in, ht_sub⟩

  have hA'_sub : A' ⊆ {y | 0 < d y} := by
    intro y hy
    exact dist_pos.mpr hy.2

  have h_singleton_null : volume ({x} : Set (E n)) = 0 := by exact measure_singleton x
  have h_diff_null : volume (A \ A') = 0 := by
    have h : A \ A' ⊆ {x} := by
      intro y hy
      have h2 : y ∉ A' := hy.2
      simp only [A', Set.mem_diff, Set.mem_singleton_iff] at h2
      by_cases h3 : y = x
      · exact h3
      · exact False.elim (h2 ⟨hy.1, h3⟩)
    exact measure_mono_null h h_singleton_null
  have h4 : volume (A' \ A) = 0 := by
    have h5 : A' \ A = ∅ := Set.diff_eq_empty.mpr hA'_sub1
    rw [h5]; simp
  have hA_eq_A' : A =ᵐ[volume] A' := by
    have h1 : A' ⊆ A := hA'_sub1
    have h2 : volume (A \ A') = 0 := h_diff_null
    exact EventuallyEq.symm (sdiff_null_ae_eq_self h_singleton_null)


  let f : ℝ → ENNReal := fun s => μHE[n - 1] (A ∩ sphere x s)
  rcases distance_coarea_aemeasurable hn x A hA with ⟨f', hf'_strong, hfg_eq⟩
  have h_f_ae : AEMeasurable f volume := ⟨f', hf'_strong.measurable, hfg_eq⟩

  let ν : Measure ℝ := Measure.map d (volume.restrict A')
  let ν' : Measure ℝ := volume.withDensity f
  have h_d_meas : Measurable d := by fun_prop

  have h_ν_finite : ν Set.univ < ⊤ := by
    rw [Measure.map_apply h_d_meas MeasurableSet.univ]
    have h1 : d ⁻¹' (Set.univ : Set ℝ) = Set.univ := by ext y; simp
    rw [h1, show (volume.restrict A') Set.univ = volume A' from by simp]
    exact hA'_bdd.measure_lt_top

  have h_f_neg : ∀ s, s < 0 → f s = 0 := by
    intro s hs
    have h1 : sphere x s = ∅ := by
      ext y
      simp only [Set.mem_empty_iff_false, iff_false]
      intro h2
      have h3 : dist y x = s := by simpa [sphere] using h2
      have h4 : 0 ≤ dist y x := dist_nonneg
      linarith
    have h_fs : f s = μHE[n - 1] (A ∩ sphere x s) := by rfl
    rw [h_fs, h1]; simp

  have h1_single : volume ({0} : Set ℝ) = 0 := by exact Real.volume_singleton
  have h_ne_zero : ∀ᵐ (t : ℝ) ∂volume, t ≠ (0 : ℝ) := by
    simpa [ae_iff] using h1_single
  have h2 : ∀ᵐ (t : ℝ) ∂volume, t ∈ Set.Iic 0 → f t = 0 := by
    filter_upwards [h_ne_zero] with t ht
    intro h_t_in
    have h3 : t < 0 := by
      have h4 : t ≤ 0 := h_t_in
      have h5 : t ≠ 0 := ht
      exact lt_of_le_of_ne h4 h5
    exact h_f_neg t h3
  have h_f_ae_Iic : ∀ᵐ (t : ℝ) ∂volume.restrict (Set.Iic 0), f t = 0 := by
    have h3 : (∀ᵐ (t : ℝ) ∂volume.restrict (Set.Iic 0), f t = 0) ↔
             (∀ᵐ (t : ℝ) ∂volume, t ∈ Set.Iic 0 → f t = 0) :=
      ae_restrict_iff' isClosed_Iic.measurableSet
    exact h3.mpr h2

  have h_f_zero_on : ∀ (s : Set ℝ), s ⊆ Set.Iic 0 → ∫⁻ t in s, f t = 0 := by
    intro s hs
    have h3 : (volume.restrict s) {t | f t ≠ 0} ≤ (volume.restrict (Set.Iic 0)) {t | f t ≠ 0} :=
      Measure.restrict_mono hs le_rfl _
    have h4 : (volume.restrict (Set.Iic 0)) {t | f t ≠ 0} = 0 := by
      have h5 : (∀ᵐ (t : ℝ) ∂volume.restrict (Set.Iic 0), f t = 0) := h_f_ae_Iic
      rw [ae_iff] at h5
      exact h5
    have h6 : (volume.restrict s) {t | f t ≠ 0} = 0 := le_zero_iff.mp (h3.trans_eq h4)
    have h_ae : ∀ᵐ (t : ℝ) ∂volume.restrict s, f t = 0 := by
      rw [ae_iff]; exact h6
    rw [lintegral_congr_ae h_ae] <;> simp

  have hC_closed : IsClosed ({x} : Set (E n)) := isClosed_singleton
  have hC_nonempty : ({x} : Set (E n)).Nonempty := ⟨x, rfl⟩
  have h_eq_dist : (fun y : E n => infDist y ({x} : Set (E n))) = d := by
    funext y; simp [Metric.infDist_singleton, d]
  have h_d_level_meas : FunctionLevelMeasurable (fun y : E n => infDist y ({x} : Set (E n))) := by
    rw [h_eq_dist]; exact point_distance_level_measurable hn x
  have hA'_sub' : A' ⊆ {y | 0 < infDist y ({x} : Set (E n))} := by
    intro y hy
    have h5 : 0 < d y := hA'_sub hy
    have h6 : infDist y ({x} : Set (E n)) = d y := by
      rw [Metric.infDist_singleton] <;> rfl
    have h7 : 0 < infDist y ({x} : Set (E n)) := by rw [h6]; exact h5
    exact h7

  have h_integrand_eq : ∀ (s : ℝ), 0 < s →
      μHE[n - 1] {y ∈ A' | infDist y ({x} : Set (E n)) = s} = f s := by
    intro s hs
    have h1 : {y ∈ A' | infDist y ({x} : Set (E n)) = s} = A ∩ sphere x s := by
      ext y
      have h_eq1 : infDist y ({x} : Set (E n)) = dist y x := by
        rw [Metric.infDist_singleton] <;> rfl
      simp only [Set.mem_sep_iff, Set.mem_inter_iff, A', Set.mem_diff, Set.mem_singleton_iff]
      constructor
      · rintro ⟨hyA', h_eq⟩
        have h_dist : dist y x = s := by rw [←h_eq1, h_eq]
        exact ⟨hyA'.1, by simpa [sphere] using h_dist⟩
      · rintro ⟨hyA, h_sph⟩
        have h_dist : dist y x = s := by simpa [sphere] using h_sph
        have h_y_ne_x : y ≠ x := by
          intro h; rw [h] at h_dist; simp at h_dist <;> linarith
        exact ⟨⟨hyA, h_y_ne_x⟩, by rw [h_eq1]; exact h_dist⟩
    rw [h1]

  have hν'_apply : ∀ (s : Set ℝ), MeasurableSet s → ν' s = ∫⁻ t in s, f t := by
    intro s hs; exact withDensity_apply' f s

  have h_main_pos : ∀ (a b : ℝ), 0 ≤ a → a < b →
      ν (Set.Ioc a b) = ν' (Set.Ioc a b) := by
    intro a b ha_nonneg hab
    have hIoc_meas : MeasurableSet (Set.Ioc a b) := by exact measurableSet_Ioc
    have h1 : ν (Set.Ioc a b) = volume (A' ∩ d ⁻¹' (Set.Ioc a b)) := by
      rw [Measure.map_apply h_d_meas hIoc_meas]
      rw [Measure.restrict_apply (hIoc_meas.preimage h_d_meas), inter_comm]
    have h2 : A' ∩ d ⁻¹' (Set.Ioc a b) = {y ∈ A' | a < d y ∧ d y ≤ b} := by
      ext y; simp [Set.mem_preimage, Set.mem_Ioc] <;> tauto
    have h_coarea := distance_coarea_eq hn hC_closed hC_nonempty h_d_level_meas
      hA'_meas hA'_bdd hA'_sub' hab
    have h3 : volume {y ∈ A' | a < d y ∧ d y ≤ b} =
        ∫⁻ s in Set.Ioc a b, μHE[n - 1] {y ∈ A' | infDist y ({x} : Set (E n)) = s} := by
      simpa [h_eq_dist] using h_coarea
    have h4 : ∫⁻ s in Set.Ioc a b, μHE[n - 1] {y ∈ A' | infDist y ({x} : Set (E n)) = s} =
        ∫⁻ s in Set.Ioc a b, f s := by
      have h5 : ∀ᵐ (s : ℝ) ∂volume, s ∈ Set.Ioc a b →
          μHE[n - 1] {y ∈ A' | infDist y ({x} : Set (E n)) = s} = f s := by
        filter_upwards with s
        intro hs
        have h_s_pos : 0 < s := lt_of_le_of_lt ha_nonneg hs.1
        exact h_integrand_eq s h_s_pos
      have h5' : ∀ᵐ (s : ℝ) ∂volume.restrict (Set.Ioc a b),
          μHE[n - 1] {y ∈ A' | infDist y ({x} : Set (E n)) = s} = f s :=
        (ae_restrict_iff' hIoc_meas).mpr h5
      rw [lintegral_congr_ae h5']
    rw [h1, h2, h3, h4]
    exact (hν'_apply (Set.Ioc a b) hIoc_meas).symm

  have h_ν_reduce : ∀ (a b : ℝ), a < 0 → ν (Set.Ioc a b) = ν (Set.Ioc (0 : ℝ) b) := by
    intro a b ha_neg
    have hIoc_meas : MeasurableSet (Set.Ioc a b) := by exact measurableSet_Ioc
    have hIoc0_meas : MeasurableSet (Set.Ioc (0 : ℝ) b) := by exact measurableSet_Ioc
    have h_set_eq : A' ∩ d ⁻¹' (Set.Ioc a b) = A' ∩ d ⁻¹' (Set.Ioc (0 : ℝ) b) := by
      ext y
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_Ioc]
      constructor
      · rintro ⟨hyA', h1, h2⟩
        have h_pos : 0 < d y := hA'_sub hyA'
        exact ⟨hyA', h_pos, h2⟩
      · rintro ⟨hyA', h1, h2⟩
        have h_pos : 0 < d y := hA'_sub hyA'
        exact ⟨hyA', by linarith, h2⟩
    have h1 : ν (Set.Ioc a b) = volume (A' ∩ d ⁻¹' (Set.Ioc a b)) := by
      rw [Measure.map_apply h_d_meas hIoc_meas]
      rw [Measure.restrict_apply (hIoc_meas.preimage h_d_meas), inter_comm]
    have h2 : ν (Set.Ioc (0 : ℝ) b) = volume (A' ∩ d ⁻¹' (Set.Ioc (0 : ℝ) b)) := by
      rw [Measure.map_apply h_d_meas hIoc0_meas]
      rw [Measure.restrict_apply (hIoc0_meas.preimage h_d_meas), inter_comm]
    rw [h1, h2, h_set_eq]

  have h_ν'_reduce : ∀ (a b : ℝ), a < 0 → 0 < b →
      ν' (Set.Ioc a b) = ν' (Set.Ioc (0 : ℝ) b) := by
    intro a b ha_neg hb_pos
    have hIoc_a0_meas : MeasurableSet (Set.Ioc a (0 : ℝ)) := by exact measurableSet_Ioc
    have hIoc_0b_meas : MeasurableSet (Set.Ioc (0 : ℝ) b) := by exact measurableSet_Ioc
    have h_disj : Disjoint (Set.Ioc a (0 : ℝ)) (Set.Ioc (0 : ℝ) b) := by
      rw [Set.disjoint_left]
      intro t ht1 ht2
      have h1 : t ≤ 0 := ht1.2
      have h2 : 0 < t := ht2.1
      linarith
    have h_union : Set.Ioc a b = Set.Ioc a (0 : ℝ) ∪ Set.Ioc (0 : ℝ) b := by
      ext t
      simp only [Set.mem_Ioc, Set.mem_union]
      constructor
      · rintro ⟨h1, h2⟩
        by_cases h3 : t ≤ 0
        · exact Or.inl ⟨h1, h3⟩
        · exact Or.inr ⟨by linarith, h2⟩
      · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
        · exact ⟨by linarith, by linarith⟩
        · exact ⟨by linarith, by linarith⟩
    have h_sub_a0 : Set.Ioc a (0 : ℝ) ⊆ Set.Iic 0 := by
      intro t ht; exact ht.2
    have h_zero : ∫⁻ t in Set.Ioc a (0 : ℝ), f t = 0 :=
      h_f_zero_on (Set.Ioc a (0 : ℝ)) h_sub_a0
    have h : ∫⁻ t in (Set.Ioc a (0 : ℝ) ∪ Set.Ioc (0 : ℝ) b), f t =
        (∫⁻ t in Set.Ioc a (0 : ℝ), f t) + (∫⁻ t in Set.Ioc (0 : ℝ) b, f t) := by
      have h' : ∫⁻ (x : ℝ) in (Set.Ioc a (0 : ℝ) ∪ Set.Ioc (0 : ℝ) b), f x ∂volume =
          (∫⁻ (x : ℝ) in Set.Ioc a (0 : ℝ), f x ∂volume) + (∫⁻ (x : ℝ) in Set.Ioc (0 : ℝ) b, f x ∂volume) :=
        lintegral_union hIoc_0b_meas h_disj
      exact h'
    have h_main : ∫⁻ t in Set.Ioc a b, f t =
        ∫⁻ t in Set.Ioc (0 : ℝ) b, f t := by
      rw [h_union]
      rw [h]
      have h13 : (∫⁻ t in Set.Ioc a (0 : ℝ), f t) = 0 := h_zero
      rw [h13, zero_add]
    rw [hν'_apply (Set.Ioc a b) measurableSet_Ioc, h_main]
    exact (hν'_apply (Set.Ioc (0 : ℝ) b) hIoc_0b_meas).symm

  have h_ν_zero : ∀ (a b : ℝ), b ≤ 0 → ν (Set.Ioc a b) = 0 := by
    intro a b hb_nonpos
    have hIoc_meas : MeasurableSet (Set.Ioc a b) := by exact measurableSet_Ioc
    have h_empty : A' ∩ d ⁻¹' (Set.Ioc a b) = ∅ := by
      ext y
      simp only [Set.mem_empty_iff_false, iff_false, Set.mem_inter_iff, Set.mem_preimage, Set.mem_Ioc]
      intro ⟨hyA', h4, h5⟩
      have h6 : 0 < d y := hA'_sub hyA'
      have h7 : d y ≤ b := h5
      have h8 : b ≤ 0 := hb_nonpos
      linarith
    rw [Measure.map_apply h_d_meas hIoc_meas,
        Measure.restrict_apply (hIoc_meas.preimage h_d_meas), inter_comm, h_empty] <;> simp

  have h_ν'_zero : ∀ (a b : ℝ), b ≤ 0 → ν' (Set.Ioc a b) = 0 := by
    intro a b hb_nonpos
    have hIoc_meas : MeasurableSet (Set.Ioc a b) := by exact measurableSet_Ioc
    have h_sub : Set.Ioc a b ⊆ Set.Iic 0 := by
      intro t ht
      have h9 : t ≤ b := ht.2
      have h10 : b ≤ 0 := hb_nonpos
      exact le_trans h9 h10
    rw [hν'_apply (Set.Ioc a b) hIoc_meas]
    exact h_f_zero_on (Set.Ioc a b) h_sub

  have h_main_all : ∀ (a b : ℝ), a ≤ b → ν (Set.Ioc a b) = ν' (Set.Ioc a b) := by
    intro a b hab
    by_cases h_lt : a < b
    · by_cases h_b_pos : 0 < b
      · by_cases h_a_nonneg : 0 ≤ a
        · exact h_main_pos a b h_a_nonneg h_lt
        · have h_a_neg : a < 0 := by linarith
          rw [h_ν_reduce a b h_a_neg, h_ν'_reduce a b h_a_neg h_b_pos]
          exact h_main_pos 0 b (by norm_num) h_b_pos
      · have h_b_nonpos : b ≤ 0 := by linarith
        rw [h_ν_zero a b h_b_nonpos, h_ν'_zero a b h_b_nonpos]
    · have h_eq : a = b := by linarith
      have h_empty : Set.Ioc a b = ∅ := by rw [h_eq] <;> simp
      rw [h_empty] <;> simp

  let S : Set (Set ℝ) := {s | ∃ (a b : ℝ), a ≤ b ∧ s = Set.Ioc a b}
  have hS_pi : IsPiSystem S := by
    rintro s₁ hs₁ s₂ hs₂ _
    rcases hs₁ with ⟨a, b, hab, rfl⟩
    rcases hs₂ with ⟨c, d, hcd, rfl⟩
    let a' := max a c
    let b' := min b d
    by_cases h : a' ≤ b'
    · refine ⟨a', b', h, ?_⟩
      ext z; simp [Set.mem_Ioc, a', b'] <;> tauto
    · have h_empty : Set.Ioc a b ∩ Set.Ioc c d = ∅ := by
        ext z
        simp only [Set.mem_empty_iff_false, iff_false, Set.mem_inter_iff, Set.mem_Ioc]
        intro ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
        have h5 : a' ≤ z := by
          simp only [a', max_le_iff]
          exact ⟨le_of_lt h1, le_of_lt h3⟩
        have h6 : z ≤ b' := by
          simp only [b', le_min_iff]
          exact ⟨h2, h4⟩
        have h7 : a' ≤ b' := le_trans h5 h6
        exact h h7
      refine ⟨(0 : ℝ), (0 : ℝ), by norm_num, ?_⟩
      rw [h_empty] <;> simp
  have hS_eq : S = {S : Set ℝ | ∃ (l u : ℝ), l ≤ u ∧ Set.Ioc l u = S} := by
    ext s
    simp only [S, Set.mem_setOf_eq]
    constructor
    · rintro ⟨a, b, hab, rfl⟩
      exact ⟨a, b, hab, rfl⟩
    · rintro ⟨l, u, hlu, rfl⟩
      exact ⟨l, u, hlu, rfl⟩
  have hS_gen : (borel ℝ : MeasurableSpace ℝ) = MeasurableSpace.generateFrom S := by
    rw [hS_eq]
    exact borel_eq_generateFrom_Ioc_le (α := ℝ)
  let B : ℕ → Set ℝ := fun k => Set.Ioc (-(k : ℝ)) (k : ℝ)
  have hB_in_S : ∀ i, B i ∈ S := by
    intro i; refine ⟨-(i : ℝ), (i : ℝ), by simp, rfl⟩
  have hB_univ : (⋃ i, B i) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro z
    let i : ℕ := Nat.ceil |z| + 1
    have h1 : -(i : ℝ) < z := by
      have h11 : -|z| ≤ z := neg_abs_le z
      have h12 : |z| ≤ ↑(Nat.ceil |z|) := Nat.le_ceil |z|
      simp [i] <;> linarith
    have h2 : z ≤ (i : ℝ) := by
      have h21 : z ≤ |z| := le_abs_self z
      have h22 : |z| ≤ ↑(Nat.ceil |z|) := Nat.le_ceil |z|
      simp [i] <;> linarith
    exact Set.mem_iUnion.mpr ⟨i, ⟨h1, h2⟩⟩
  have hB_fin : ∀ i, ν (B i) ≠ ⊤ := by
    intro i
    have h : ν (B i) ≤ ν Set.univ := measure_mono (Set.subset_univ _)
    exact (h.trans_lt h_ν_finite).ne
  have h_eq_S : ∀ s ∈ S, ν s = ν' s := by
    intro s hs
    rcases hs with ⟨a, b, hab, rfl⟩
    exact h_main_all a b hab
  have h_eq : ν = ν' :=
    Measure.ext_of_generateFrom_of_iUnion S B hS_gen hS_pi hB_univ hB_in_S hB_fin h_eq_S

  have h_g_meas : Measurable g := hg_cont.measurable
  have h_main1 : ∫ t in Set.Ioi 0, g t ∂ν =
      ∫ y in d ⁻¹' Set.Ioi 0, g (d y) ∂(volume.restrict A') :=
    setIntegral_map isOpen_Ioi.measurableSet
      (h_g_meas.aestronglyMeasurable) (h_d_meas.aemeasurable)
  have h_preimage : d ⁻¹' Set.Ioi 0 = {y | 0 < d y} := by
    ext y; simp [Set.mem_preimage, Set.mem_Ioi]
  have h_d_cont : Continuous d := by fun_prop
  have h_meas_set : MeasurableSet {y : E n | 0 < d y} := by
    have h_open : IsOpen (d ⁻¹' Set.Ioi 0) := isOpen_Ioi.preimage h_d_cont
    have h_eq : d ⁻¹' Set.Ioi 0 = {y : E n | 0 < d y} := by
      ext y; simp [d, Set.mem_preimage, Set.mem_Ioi]
    rw [←h_eq]
    exact h_open.measurableSet
  have h_restrict_eq : (volume.restrict A').restrict {y | 0 < d y} = volume.restrict A' := by
    rw [Measure.restrict_restrict h_meas_set]
    have h2 : {y | 0 < d y} ∩ A' = A' := by
      rw [inter_comm]
      apply Set.inter_eq_left.mpr
      exact hA'_sub
    rw [h2] <;> exact hA'_meas
  have h_integral_A' : ∫ y in d ⁻¹' Set.Ioi 0, g (d y) ∂(volume.restrict A') =
      ∫ y in A', g (d y) := by
    rw [h_preimage]
    have h3 : ∫ y in {y | 0 < d y}, g (d y) ∂(volume.restrict A') =
        ∫ y, g (d y) ∂((volume.restrict A').restrict {y | 0 < d y}) := by rfl
    rw [h3, h_restrict_eq] <;> rfl
  have h_integral_A : ∫ y in A, g (d y) = ∫ y in A', g (d y) :=
    setIntegral_congr_set hA_eq_A'

  -- f < ⊤ a.e. on Ioi 0
  have h_ball : ∃ (R : ℝ), 0 < R ∧ A ⊆ ball x R := by
    rcases hA_bdd'.subset_ball x with ⟨r, hr⟩
    by_cases hpos : 0 < r
    · exact ⟨r, hpos, hr⟩
    · have h1 : A = ∅ := by
        ext y
        simp only [Set.mem_empty_iff_false, iff_false]
        intro hy
        have h4 : dist y x < r := hr hy
        have h5 : 0 ≤ dist y x := dist_nonneg
        linarith
      refine ⟨1, by norm_num, ?_⟩
      rw [h1] <;> simp
  rcases h_ball with ⟨R, hR_pos, hR_sub⟩
  have h_f_large : ∀ t, R ≤ t → f t = 0 := by
    intro t ht
    have h1 : A ∩ sphere x t = ∅ := by
      ext y
      simp only [Set.mem_empty_iff_false, iff_false, Set.mem_inter_iff]
      intro ⟨hyA, hsph⟩
      have h2 : dist y x = t := by simpa [sphere] using hsph
      have h3 : dist y x < R := hR_sub hyA
      rw [h2] at h3; linarith
    have h_fs : f t = μHE[n - 1] (A ∩ sphere x t) := by rfl
    rw [h_fs, h1]; simp

  let S2 := {y ∈ A' | 0 < d y ∧ d y ≤ R}
  have h_coarea_R := distance_coarea_eq hn hC_closed hC_nonempty h_d_level_meas
    hA'_meas hA'_bdd hA'_sub' hR_pos
  have hS2_eq : S2 = {y ∈ A' | 0 < infDist y ({x} : Set (E n)) ∧ infDist y ({x} : Set (E n)) ≤ R} := by
    ext y
    simp only [S2, Set.mem_sep_iff]
    have h_eq : infDist y ({x} : Set (E n)) = d y := by
      rw [Metric.infDist_singleton] <;> rfl
    rw [h_eq]
    <;> rfl
  have h_main2 : volume S2 = ∫⁻ s in Set.Ioc (0 : ℝ) R,
      μHE[n - 1] {y ∈ A' | infDist y ({x} : Set (E n)) = s} := by
    rw [hS2_eq]
    exact h_coarea_R
  have hIocR_meas : MeasurableSet (Set.Ioc (0 : ℝ) R) := by exact measurableSet_Ioc
  have h_integrand_R1 : ∀ᵐ (s : ℝ) ∂volume, s ∈ Set.Ioc (0 : ℝ) R →
      μHE[n - 1] {y ∈ A' | infDist y ({x} : Set (E n)) = s} = f s := by
    filter_upwards with s
    intro hs
    have h_s_pos : 0 < s := hs.1
    exact h_integrand_eq s h_s_pos
  have h_integrand_R : ∀ᵐ (s : ℝ) ∂volume.restrict (Set.Ioc (0 : ℝ) R),
      μHE[n - 1] {y ∈ A' | infDist y ({x} : Set (E n)) = s} = f s :=
    (ae_restrict_iff' hIocR_meas).mpr h_integrand_R1
  have h_eq_int : ∫⁻ s in Set.Ioc (0 : ℝ) R, f s = volume S2 := by
    have h_congr : ∫⁻ s in Set.Ioc (0 : ℝ) R,
        μHE[n - 1] {y ∈ A' | infDist y ({x} : Set (E n)) = s} =
        ∫⁻ s in Set.Ioc (0 : ℝ) R, f s :=
      lintegral_congr_ae h_integrand_R
    exact (h_main2.trans h_congr).symm
  have hS2_sub : S2 ⊆ A' := by intro y hy; exact hy.1
  have h_int : ∫⁻ s in Set.Ioc (0 : ℝ) R, f s < ⊤ := by
    rw [h_eq_int]
    exact (measure_mono hS2_sub).trans_lt hA'_bdd.measure_lt_top

  have h_f_ae_R : AEMeasurable f (volume.restrict (Set.Ioc (0 : ℝ) R)) :=
    h_f_ae.mono_measure Measure.restrict_le_self
  have h_ae_interval : ∀ᵐ (t : ℝ) ∂volume.restrict (Set.Ioc (0 : ℝ) R), f t < ⊤ :=
    ae_lt_top' h_f_ae_R h_int.ne
  have h_f_ae_Ioi : AEMeasurable f (volume.restrict (Set.Ioi 0)) :=
    h_f_ae.mono_measure Measure.restrict_le_self

  have h_ae' : ∀ᵐ (t : ℝ) ∂volume, t ∈ Set.Ioc (0 : ℝ) R → f t < ⊤ :=
    (ae_restrict_iff' hIocR_meas).mp h_ae_interval
  have h_f_lt_top : ∀ᵐ (t : ℝ) ∂volume.restrict (Set.Ioi 0), f t < ⊤ := by
    have h : ∀ᵐ (t : ℝ) ∂volume, t ∈ Set.Ioi 0 → f t < ⊤ := by
      filter_upwards [h_ae'] with t ht
      intro h_t_in
      by_cases h2 : t ∈ Set.Ioc (0 : ℝ) R
      · exact ht h2
      · have h3 : R ≤ t := by
          have h4 : 0 < t := h_t_in
          by_contra h5
          have h6 : t < R := by linarith
          exact h2 ⟨h4, le_of_lt h6⟩
        have h4 : f t = 0 := h_f_large t h3
        rw [h4] <;> simp
    have h_iff : (∀ᵐ (t : ℝ) ∂volume.restrict (Set.Ioi 0), f t < ⊤) ↔
        (∀ᵐ (t : ℝ) ∂volume, t ∈ Set.Ioi 0 → f t < ⊤) :=
      ae_restrict_iff' isOpen_Ioi.measurableSet
    exact h_iff.mpr h

  have h10 : ∫ t in Set.Ioi 0, g t ∂ν' =
      ∫ t in Set.Ioi 0, (f t).toReal • g t :=
    setIntegral_withDensity_eq_setIntegral_toReal_smul₀
      h_f_ae_Ioi h_f_lt_top g isOpen_Ioi.measurableSet
  have h11 : (fun t : ℝ => (f t).toReal • g t) = fun t : ℝ => g t * (f t).toReal := by
    funext t; simp [smul_eq_mul] <;> ring

  calc
    ∫ y in A, g (d y)
      = ∫ y in A', g (d y) := h_integral_A
    _ = ∫ t in Set.Ioi 0, g t ∂ν := by
        exact Eq.trans (Eq.symm h_integral_A') (Eq.symm h_main1)
    _ = ∫ t in Set.Ioi 0, g t ∂ν' := by rw [h_eq]
    _ = ∫ t in Set.Ioi 0, (f t).toReal • g t := h10
    _ = ∫ t in Set.Ioi 0, g t * (f t).toReal := by rw [h11]


-- ============================================================================
-- Weighted distance coarea formula (unbounded sets)
-- ============================================================================

/-- Weighted distance coarea formula for unbounded sets, when `g` has compact
support. Reduces to the bounded version by restricting `A` to the support. -/
lemma weighted_distance_coarea_unbounded
    {A : Set (E n)} (hA : MeasurableSet A)
    (x : E n) (g : ℝ → ℝ) (hg_nonneg : ∀ t, 0 ≤ g t) (hg_cont : Continuous g)
    {a b : ℝ} (hg_support : ∀ t ∉ Set.Icc a b, g t = 0)
    (hn : 2 ≤ n) :
    ∫ y in A, g (dist y x) =
      ∫ t in Set.Ioi 0, g t * (μHE[n - 1] (A ∩ sphere x t)).toReal := by
  let B_val : ℝ := max b 0
  let A' := A ∩ closedBall x B_val
  have hA'_meas : MeasurableSet A' := hA.inter isClosed_closedBall.measurableSet
  have hA'_bdd : Bornology.IsBounded A' :=
    (Metric.isBounded_iff_subset_closedBall x).mpr ⟨B_val, by simp [A']⟩

  have hA_diff_meas : MeasurableSet (A \ A') := hA.diff hA'_meas
  have h1 : ∫ y in A, g (dist y x) = ∫ y in A', g (dist y x) := by
    have h_forall : ∀ y ∈ (A \ A'), g (dist y x) = 0 := by
      intro y hy
      have hyA : y ∈ A := hy.1
      have hynA' : y ∉ A' := hy.2
      have h4 : y ∉ closedBall x B_val := by
        intro h5
        have h6 : y ∈ A' := ⟨hyA, h5⟩
        exact hynA' h6
      have h5 : B_val < dist y x := by simpa [closedBall, not_le] using h4
      have h6 : dist y x ∉ Set.Icc a b := by
        intro h7
        have h8 : dist y x ≤ b := h7.2
        have h9 : dist y x ≤ B_val := le_trans h8 (le_max_left b 0)
        exact not_le.mpr h5 h9
      exact hg_support (dist y x) h6
    have h2 : ∫ y in (A \ A'), g (dist y x) = 0 := by
      have h_ae : (fun y : E n => g (dist y x)) =ᵐ[volume.restrict (A \ A')] (0 : E n → ℝ) := by
        filter_upwards [self_mem_ae_restrict hA_diff_meas] with y hy
        exact h_forall y hy
      have h_eq_int : ∫ y in (A \ A'), g (dist y x) = ∫ y in (A \ A'), (0 : ℝ) :=
        integral_congr_ae h_ae
      rw [h_eq_int]
      simp
    have h_union : A = A' ∪ (A \ A') := by
      ext y; simp [A'] <;> tauto
    have h_disj : Disjoint A' (A \ A') := by
      rw [Set.disjoint_left]
      intro z hz1 hz2
      exact hz2.2 hz1
    have h_cont : Continuous (fun y : E n => g (dist y x)) := by fun_prop
    have h_closure_compact : IsCompact (closure A') := hA'_bdd.isCompact_closure
    have h_closure_meas : MeasurableSet (closure A') := isClosed_closure.measurableSet
    have h_int_closure : IntegrableOn (fun y : E n => g (dist y x)) (closure A') volume :=
      h_cont.continuousOn.integrableOn_compact' h_closure_compact h_closure_meas
    have h_int1 : IntegrableOn (fun y : E n => g (dist y x)) A' volume :=
      h_int_closure.mono_set subset_closure
    have h_int2 : IntegrableOn (fun y : E n => g (dist y x)) (A \ A') volume := by
      have h_zero_int : IntegrableOn (0 : E n → ℝ) (A \ A') volume := by
        simpa [IntegrableOn] using integrable_zero (E n) volume
      exact (integrableOn_congr_fun h_forall hA_diff_meas).mpr h_zero_int
    have h3 : ∫ y in (A' ∪ (A \ A')), g (dist y x) =
        (∫ y in A', g (dist y x)) + (∫ y in (A \ A'), g (dist y x)) :=
      MeasureTheory.setIntegral_union h_disj hA_diff_meas h_int1 h_int2
    rw [h_union, h3, h2, add_zero]

  have h_sphere_eq : ∀ (t : ℝ), t ∈ Set.Ioi 0 → g t ≠ 0 →
      A' ∩ sphere x t = A ∩ sphere x t := by
    intro t _ hgt
    have h7 : t ∈ Set.Icc a b := by
      by_contra h8
      exact hgt (hg_support t h8)
    have h8 : t ≤ b := h7.2
    have h9 : t ≤ B_val := le_trans h8 (le_max_left b 0)
    ext y
    simp only [A', Set.mem_inter_iff, Metric.mem_sphere]
    constructor
    · rintro ⟨⟨hA, h10⟩, h11⟩
      exact ⟨hA, h11⟩
    · rintro ⟨hA, h11⟩
      have hdist : dist y x = t := h11
      have h10 : y ∈ closedBall x B_val := by
        rw [Metric.mem_closedBall, hdist]
        exact h9
      exact ⟨⟨hA, h10⟩, h11⟩

  have h3 : ∫ t in Set.Ioi 0, g t * (μHE[n - 1] (A ∩ sphere x t)).toReal =
           ∫ t in Set.Ioi 0, g t * (μHE[n - 1] (A' ∩ sphere x t)).toReal := by
    apply integral_congr_ae
    have h4 : ∀ᵐ (t : ℝ) ∂volume.restrict (Set.Ioi 0),
        g t * (μHE[n - 1] (A ∩ sphere x t)).toReal =
        g t * (μHE[n - 1] (A' ∩ sphere x t)).toReal := by
      filter_upwards [self_mem_ae_restrict isOpen_Ioi.measurableSet] with t ht
      by_cases hgt : g t = 0
      · rw [hgt, zero_mul, zero_mul]
      · have h5 : A' ∩ sphere x t = A ∩ sphere x t := h_sphere_eq t ht hgt
        rw [h5]
    simpa [Filter.EventuallyEq] using h4

  rw [h1, h3]
  exact weighted_distance_coarea hA'_meas hA'_bdd x g hg_nonneg hg_cont hn


-- ============================================================================
-- One-sided approximate identity (helper for tight cutoff)
-- ============================================================================

/-- One-sided approximate identity at a strong Lebesgue point. -/
lemma approximate_identity_one_sided
    {f : ℝ → ℝ} (hf : LocallyIntegrable f volume)
    {w : ℝ → ℝ} (hw_cont : Continuous w)
    (hw_nonneg : ∀ t, 0 ≤ w t)
    (hw_support : ∀ t ∉ Set.Icc 0 1, w t = 0)
    (hw_int : ∫ t in (0 : ℝ)..1, w t = 1)
    (r : ℝ)
    (hr_leb : Tendsto (fun h : ℝ => (1 / h) * ∫ t in r..(r + h), |f t - f r|)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)) :
    Tendsto (fun L : ℝ => ∫ t in (0 : ℝ)..1, w t * f (r + L * t))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (f r)) := by
  have h_bdd_Icc : ∃ (M : ℝ), 0 ≤ M ∧ ∀ t ∈ Set.Icc (0 : ℝ) 1, |w t| ≤ M := by
    have h_cont_on : ContinuousOn w (Set.Icc (0 : ℝ) 1) := hw_cont.continuousOn
    have h : BddAbove (Set.image w (Set.Icc (0 : ℝ) 1)) :=
      isCompact_Icc.bddAbove_image h_cont_on
    rcases h with ⟨M, hM⟩
    refine ⟨max M 0, by positivity, fun t ht => ?_⟩
    have h1 : w t ∈ Set.image w (Set.Icc (0 : ℝ) 1) := ⟨t, ht, rfl⟩
    have h2 : w t ≤ M := hM h1
    have h3 : 0 ≤ w t := hw_nonneg t
    rw [abs_of_nonneg h3]
    exact le_trans h2 (le_max_left M 0)
  rcases h_bdd_Icc with ⟨M, hM_nonneg, hM_Icc⟩
  have hM_bdd : ∀ t, |w t| ≤ M := by
    intro t
    by_cases ht : t ∈ Set.Icc (0 : ℝ) 1
    · exact hM_Icc t ht
    · have h3 : w t = 0 := hw_support t ht
      rw [h3, abs_zero] <;> exact hM_nonneg
  have hM_pos : 0 < M := by
    by_contra h
    have h0 : M = 0 := by linarith
    have h1 : ∀ t, w t = 0 := by
      intro t
      have h2 : |w t| ≤ M := hM_bdd t
      rw [h0] at h2
      have h3 : |w t| = 0 := by linarith [abs_nonneg (w t)]
      exact abs_eq_zero.mp h3
    have h5 : ∫ t in (0 : ℝ)..1, w t = 0 := by
      rw [intervalIntegral.integral_congr (fun t _ => h1 t)] <;> simp
    rw [h5] at hw_int <;> linarith

  let g : ℝ → ℝ := fun L => ∫ t in (0 : ℝ)..1, w t * f (r + L * t)
  let A : ℝ → ℝ := fun h => (1 / h) * ∫ t in r..(r + h), |f t - f r|

  have h_main_bound : ∀ (L : ℝ), 0 < L → |g L - f r| ≤ M * A L := by
    intro L hL
    have hL_ne : L ≠ 0 := hL.ne'
    have hfl : LocallyIntegrableOn f Set.univ volume := by exact locallyIntegrableOn_univ.mpr hf
    have h_on : IntegrableOn f (Set.Icc r (r + L)) volume :=
      hfl.integrableOn_compact_subset (by simp) isCompact_Icc
    have h1_ii : IntegrableOn f (Set.Ioc r (r + L)) volume := h_on.mono_set Set.Ioc_subset_Icc_self
    have h2_ii : IntegrableOn f (Set.Ioc (r + L) r) volume := by
      have h_empty : Set.Ioc (r + L) r = ∅ := by
        ext x; simp only [Set.mem_Ioc, Set.mem_empty_iff_false, iff_false]
        intro h; linarith
      rw [h_empty]; simp
    let h_f_ii : IntervalIntegrable f volume r (r + L) := ⟨h1_ii, h2_ii⟩
    have h_f_ii' : IntervalIntegrable f volume (0 + r) (L + r) := by
      simpa [add_comm] using h_f_ii
    have h_shift : IntervalIntegrable (fun t : ℝ => f (t + r)) volume 0 L :=
      (IntervalIntegrable.comp_add_right_iff (c := r)).mpr h_f_ii'
    have h_f_comp_raw : IntervalIntegrable (fun x : ℝ => f (L * x + r)) volume 0 1 := by
      have h := h_shift.comp_mul_left (c := L) (h := by finiteness) (h' := by finiteness)
      simpa [div_eq_mul_inv, hL_ne] using h
    have h_eq1 : (fun x : ℝ => f (L * x + r)) = (fun x : ℝ => f (r + L * x)) := by
      funext x; ring_nf
    let h_f_comp_ii : IntervalIntegrable (fun t : ℝ => f (r + L * t)) volume 0 1 := by
      rw [h_eq1] at h_f_comp_raw; exact h_f_comp_raw
    have h_w_ii : IntervalIntegrable w volume 0 1 := hw_cont.intervalIntegrable 0 1
    have h_w_cont_on : ContinuousOn w (Set.Icc (0 : ℝ) 1) := hw_cont.continuousOn
    have h_prod_on1 : IntegrableOn (fun t : ℝ => f (r + L * t) * w t) (Set.Ioc 0 1) volume :=
      h_f_comp_ii.1.mul_continuousOn_of_subset h_w_cont_on measurableSet_Ioc isCompact_Icc Set.Ioc_subset_Icc_self
    have h_prod_on2 : IntegrableOn (fun t : ℝ => f (r + L * t) * w t) (Set.Ioc 1 0) volume :=
      h_f_comp_ii.2.mul_continuousOn_of_subset h_w_cont_on measurableSet_Ioc isCompact_Icc (by simp)
    have h_prod_ii : IntervalIntegrable (fun t : ℝ => w t * f (r + L * t)) volume 0 1 := by
      have h_eq : (fun t : ℝ => w t * f (r + L * t)) = (fun t : ℝ => f (r + L * t) * w t) := by funext t; ring
      rw [h_eq]; exact ⟨h_prod_on1, h_prod_on2⟩
    let h_const_ii : IntervalIntegrable (fun t : ℝ => f r * w t) volume 0 1 :=
      ⟨Integrable.const_mul h_w_ii.1 (f r), Integrable.const_mul h_w_ii.2 (f r)⟩
    let h_diff_raw_ii : IntervalIntegrable (fun t : ℝ => w t * f (r + L * t) - f r * w t) volume 0 1 :=
      ⟨Integrable.sub h_prod_ii.1 h_const_ii.1, Integrable.sub h_prod_ii.2 h_const_ii.2⟩
    have h_eq2 : (fun t : ℝ => w t * f (r + L * t) - f r * w t) =
        (fun t : ℝ => w t * (f (r + L * t) - f r)) := by funext t; ring
    let h_diff_ii : IntervalIntegrable (fun t : ℝ => w t * (f (r + L * t) - f r)) volume 0 1 := by
      rw [h_eq2] at h_diff_raw_ii; exact h_diff_raw_ii
    let h_abs_ii : IntervalIntegrable (fun t : ℝ => |w t * (f (r + L * t) - f r)|) volume 0 1 :=
      ⟨Integrable.abs h_diff_ii.1, Integrable.abs h_diff_ii.2⟩
    let h_const_f_ii : IntervalIntegrable (fun t : ℝ => f r) volume 0 1 := intervalIntegrable_const
    let h_diff_f_ii : IntervalIntegrable (fun t : ℝ => f (r + L * t) - f r) volume 0 1 :=
      ⟨Integrable.sub h_f_comp_ii.1 h_const_f_ii.1, Integrable.sub h_f_comp_ii.2 h_const_f_ii.2⟩
    let h_diff_f_abs_ii : IntervalIntegrable (fun t : ℝ => |f (r + L * t) - f r|) volume 0 1 :=
      ⟨Integrable.abs h_diff_f_ii.1, Integrable.abs h_diff_f_ii.2⟩
    let h_bound_ii : IntervalIntegrable (fun t : ℝ => M * |f (r + L * t) - f r|) volume 0 1 :=
      ⟨Integrable.const_mul h_diff_f_abs_ii.1 M, Integrable.const_mul h_diff_f_abs_ii.2 M⟩

    have h1 : f r = ∫ t in (0 : ℝ)..1, f r * w t := by
      have h2 : ∫ t in (0 : ℝ)..1, f r * w t = f r * ∫ t in (0 : ℝ)..1, w t := by
        rw [intervalIntegral.integral_const_mul] <;> ring
      rw [h2, hw_int] <;> ring
    have h3 : (g L) - ∫ t in (0 : ℝ)..1, f r * w t =
        ∫ t in (0 : ℝ)..1, (w t * f (r + L * t) - f r * w t) :=
      (intervalIntegral.integral_sub h_prod_ii h_const_ii).symm
    have h4 : ∫ t in (0 : ℝ)..1, (w t * f (r + L * t) - f r * w t) =
        ∫ t in (0 : ℝ)..1, w t * (f (r + L * t) - f r) := by
      apply intervalIntegral.integral_congr; intro t _; ring
    have h_goal : (g L) - f r = ∫ t in (0 : ℝ)..1, w t * (f (r + L * t) - f r) := by
      have h_step1 : (g L) - f r = (g L) - ∫ t in (0 : ℝ)..1, f r * w t := by
        apply congr_arg (fun x => (g L) - x); exact h1
      rw [h_step1, h3, h4]
    rw [h_goal]
    have h5 : |∫ t in (0 : ℝ)..1, w t * (f (r + L * t) - f r)| ≤
        ∫ t in (0 : ℝ)..1, |w t * (f (r + L * t) - f r)| :=
      intervalIntegral.abs_integral_le_integral_abs (by norm_num)
    have h_mono : ∀ t ∈ Set.Icc (0 : ℝ) 1,
        |w t * (f (r + L * t) - f r)| ≤ M * |f (r + L * t) - f r| := by
      intro t ht
      by_cases h_t0 : t = 0
      · rw [h_t0] <;> simp
      · have h_t_pos : 0 < t := by
          have h_ne : (0 : ℝ) ≠ t := by intro h; exact h_t0 h.symm
          exact lt_of_le_of_ne ht.1 h_ne
        have h7 : |w t * (f (r + L * t) - f r)| = |w t| * |f (r + L * t) - f r| := by rw [abs_mul]
        rw [h7]; have h9 : |w t| ≤ M := hM_bdd t; gcongr
    have h6 : (∫ t in (0 : ℝ)..1, |w t * (f (r + L * t) - f r)|) ≤
        (∫ t in (0 : ℝ)..1, M * |f (r + L * t) - f r|) := by
      rw [intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num),
        intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
      exact setIntegral_mono_on h_abs_ii.1 h_bound_ii.1 measurableSet_Ioc
        (fun x hx => h_mono x (Ioc_subset_Icc_self hx))
    have h6' : ∫ t in (0 : ℝ)..1, M * |f (r + L * t) - f r| =
        M * ∫ t in (0 : ℝ)..1, |f (r + L * t) - f r| := by
      rw [intervalIntegral.integral_const_mul] <;> ring
    let h_func : ℝ → ℝ := fun t => |f t - f r|
    let h_shift_func : ℝ → ℝ := fun t => h_func (r + t)
    have h_f_abs_ii : IntervalIntegrable h_func volume r (r + L) := by
      have h_const_ii' : IntervalIntegrable (fun t : ℝ => f r) volume r (r + L) := intervalIntegrable_const
      have h_const_on1 : IntegrableOn (fun t : ℝ => f r) (Set.Ioc r (r + L)) volume := h_const_ii'.1
      have h_fmc1 : IntegrableOn (fun t : ℝ => f t - f r) (Set.Ioc r (r + L)) volume :=
        IntegrableOn.sub h_f_ii.1 h_const_on1
      have h1 : Integrable (fun t : ℝ => |f t - f r|) (volume.restrict (Set.Ioc r (r + L))) :=
        Integrable.abs h_fmc1
      have h_const_on2 : IntegrableOn (fun t : ℝ => f r) (Set.Ioc (r + L) r) volume := h_const_ii'.2
      have h_fmc2 : IntegrableOn (fun t : ℝ => f t - f r) (Set.Ioc (r + L) r) volume :=
        IntegrableOn.sub h_f_ii.2 h_const_on2
      have h2 : Integrable (fun t : ℝ => |f t - f r|) (volume.restrict (Set.Ioc (r + L) r)) :=
        Integrable.abs h_fmc2
      exact ⟨h1, h2⟩
    have h_c1 : ∫ t in (0 : ℝ)..1, h_shift_func (L * t) =
        L⁻¹ * ∫ t in (0 : ℝ)..L, h_shift_func t := by
      have h := intervalIntegral.integral_comp_mul_left (f := h_shift_func) (a := 0) (b := 1) (hc := hL_ne)
      simpa [smul_eq_mul] using h
    have h_c2 : ∫ t in (0 : ℝ)..L, h_shift_func t = ∫ t in r..(r + L), h_func t := by
      have h : ∫ t in (0 : ℝ)..L, h_func (t + r) = ∫ t in (0 + r)..(L + r), h_func t :=
        intervalIntegral.integral_comp_add_right (f := h_func) (d := r) (a := 0) (b := L)
      have h_eq : h_shift_func = fun t => h_func (t + r) := by funext t; simp [h_shift_func]; ring_nf
      rw [h_eq]; simpa [add_comm] using h
    have h_eq3 : (fun t : ℝ => |f (r + L * t) - f r|) = fun t => h_shift_func (L * t) := by
      funext t; rfl
    have h_change : ∫ t in (0 : ℝ)..1, |f (r + L * t) - f r| = A L := by
      rw [h_eq3, h_c1, h_c2]
      have h9 : L⁻¹ * ∫ t in r..(r + L), h_func t = A L := by
        have h10 : h_func = fun t => |f t - f r| := by funext t; rfl
        rw [h10]; simp [A, hL_ne] <;> ring
      exact h9
    have h_final : |∫ t in (0 : ℝ)..1, w t * (f (r + L * t) - f r)| ≤ M * A L := by
      calc
        |∫ t in (0 : ℝ)..1, w t * (f (r + L * t) - f r)|
          ≤ ∫ t in (0 : ℝ)..1, |w t * (f (r + L * t) - f r)| := h5
        _ ≤ ∫ t in (0 : ℝ)..1, M * |f (r + L * t) - f r| := h6
        _ = M * ∫ t in (0 : ℝ)..1, |f (r + L * t) - f r| := h6'
        _ = M * A L := by rw [h_change] <;> ring
    exact h_final

  have h_tendsto_A : Tendsto A (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := hr_leb
  have h_tendsto_MA : Tendsto (fun L => M * A L) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have h : Tendsto (fun L => M * A L) (nhdsWithin 0 (Set.Ioi 0)) (nhds (M * 0)) :=
      tendsto_const_nhds.mul h_tendsto_A
    simpa using h

  have h_main : ∀ (ε : ℝ), 0 < ε → ∀ᶠ (L : ℝ) in nhdsWithin 0 (Set.Ioi 0), |g L - f r| < ε := by
    intro ε hε
    have hε' : 0 < ε / M := by positivity
    have h2' : Set.Iio (ε / M) ∈ nhds (0 : ℝ) := Iio_mem_nhds hε'
    have h2 : ∀ᶠ (L : ℝ) in nhdsWithin 0 (Set.Ioi 0), A L < ε / M := by
      have h3 : ∀ᶠ (L : ℝ) in nhdsWithin 0 (Set.Ioi 0), A L ∈ Set.Iio (ε / M) :=
        h_tendsto_A h2'
      simpa [Set.mem_Iio] using h3
    have h1 : ∀ᶠ (L : ℝ) in nhdsWithin 0 (Set.Ioi 0), M * A L < ε := by
      filter_upwards [h2] with L h3
      have h4 : M * A L < M * (ε / M) := by gcongr
      have h5 : M * (ε / M) = ε := by field_simp [hM_pos.ne'] <;> ring
      rw [h5] at h4; exact h4
    have h3 : ∀ᶠ (L : ℝ) in nhdsWithin 0 (Set.Ioi 0), |g L - f r| ≤ M * A L := by
      filter_upwards [self_mem_nhdsWithin] with L hL
      exact h_main_bound L hL
    filter_upwards [h3, h1] with L h4 h5
    linarith

  exact Metric.tendsto_nhds.mpr h_main

-- ============================================================================
-- Tight cutoff inequality (Maggi Proposition 15.3)
-- ============================================================================

/-- **Tight cutoff inequality**: for a.e. r > 0,
`|inner(Dχ_U(closedBall x r), ν)| ≤ H^{n-1}(U ∩ sphere x r).toReal`.

Proof: use radial cutoff η_{r,ε}, divergence theorem, and
weighted_distance_coarea with g = |η'|. As ε → 0, LHS → inner product,
RHS → H^{n-1}(U ∩ sphere x r) by Lebesgue differentiation. -/
lemma tight_cutoff_inequality
    {U : Set (E n)} (hU : MeasurableSet U) (hBdd : Bornology.IsBounded U)
    (hfin : perimeter U < ⊤) (hn : 2 ≤ n)
    (x : E n) (ν : E n) (hν_unit : ‖ν‖ = 1) :
    ∀ᵐ (r : ℝ) ∂volume.restrict (Set.Ioi 0),
      |inner ℝ ((distributionalDerivative U) (closedBall x r)) ν| ≤
        (μHE[n - 1] (U ∩ sphere x r)).toReal := by
  let D := distributionalDerivative U
  let μ := perimeterMeasure U
  let f_normal := measureTheoreticNormal U
  have hD_eq : D = μ.withDensityᵥ f_normal := (measureTheoreticNormal_withDensity hfin).2
  have hf_int : Integrable f_normal μ := (measureTheoreticNormal_withDensity hfin).1
  have hf_norm_one : ∀ᵐ y ∂μ, ‖f_normal y‖ = 1 := norm_measureTheoreticNormal_eq_one hfin
  have hf_norm_le_one : ∀ᵐ y ∂μ, ‖f_normal y‖ ≤ 1 := by
    filter_upwards [hf_norm_one] with y hy <;> rw [hy] <;> norm_num
  have h_perim_eq : μ Set.univ = perimeter U := by exact Eq.symm (perimeter_eq_variation U hfin)
  letI hμ_fin : IsFiniteMeasure μ :=
    ⟨by rw [h_perim_eq] <;> exact hfin⟩

  let f_sphere : ℝ → ℝ := fun t => (μHE[n - 1] (U ∩ sphere x t)).toReal
  let F_sphere : ℝ → ENNReal := fun t => μHE[n - 1] (U ∩ sphere x t)
  haveI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp (by linarith)

  -- Step 0a: F_sphere is a.e. measurable
  have h_F_ae : AEStronglyMeasurable F_sphere volume :=
    distance_coarea_aemeasurable hn x U hU

  -- Step 0b: F_sphere has finite lintegral via Eilenberg
  let dist_x : E n → ℝ := fun y => dist y x
  have h_dist_lip : LipschitzWith (1 : NNReal) dist_x := by
    apply LipschitzWith.of_dist_le_mul
    intro a b
    have h : |dist a x - dist b x| ≤ dist a b := abs_dist_sub_le a b x
    have h' : dist (dist a x) (dist b x) ≤ dist a b := by
      rw [Real.dist_eq] <;> exact h
    simpa [NNReal.coe_one, one_mul] using h'
  rcases eilenberg_μHE hn (hf := h_dist_lip) (by norm_num) with ⟨C, hC_ne_top, _, h_eilenberg⟩
  have h_vol_lt_top : volume U < ⊤ := hBdd.measure_lt_top
  have hC_lt_top : C < ⊤ := lt_top_iff_ne_top.mpr hC_ne_top
  have h_mul_lt_top : C * volume U < ⊤ := mul_lt_top hC_lt_top h_vol_lt_top
  have h_lint_fin : (∫⁻ (t : ℝ), F_sphere t) < ⊤ := by
    have h1 : (∫⁻ (t : ℝ), F_sphere t) ≤ C * volume U := h_eilenberg U
    exact h1.trans_lt h_mul_lt_top
  have h_ae_lt_top : ∀ᵐ (t : ℝ), F_sphere t < ⊤ :=
    ae_lt_top' h_F_ae.aemeasurable h_lint_fin.ne

  -- Step 0c: f_sphere is integrable (hence locally integrable)
  have h_enorm_eq : ∀ᵐ (t : ℝ), ‖f_sphere t‖ₑ = F_sphere t := by
    filter_upwards [h_ae_lt_top] with t ht
    have h_eq : f_sphere t = (F_sphere t).toReal := by rfl
    have h_nonneg : 0 ≤ (F_sphere t).toReal := ENNReal.toReal_nonneg
    have h9 : ENNReal.ofReal (F_sphere t).toReal = F_sphere t := by
      exact ENNReal.ofReal_toReal ht.ne
    rw [h_eq, Real.enorm_eq_ofReal h_nonneg, h9]
  have h4 : (∫⁻ (t : ℝ), ‖f_sphere t‖ₑ) = (∫⁻ (t : ℝ), F_sphere t) := by
    rw [lintegral_congr_ae h_enorm_eq]
  have h_finint : HasFiniteIntegral f_sphere volume := by
    have h5 : (∫⁻ (t : ℝ), ‖f_sphere t‖ₑ) < ⊤ := by
      rw [h4]
      exact h_lint_fin
    exact h5
  have h_f_ae : AEStronglyMeasurable f_sphere volume := by
    rcases h_F_ae with ⟨g, hg, h_eq⟩
    let g' : ℝ → ℝ := fun t => (g t).toReal
    have hgm : Measurable g' := hg.measurable.ennreal_toReal
    have h_eq' : f_sphere =ᵐ[volume] g' := by
      filter_upwards [h_eq] with t ht
      have h10 : f_sphere t = (F_sphere t).toReal := by rfl
      have h11 : (F_sphere t).toReal = (g t).toReal := by rw [ht]
      rw [h10, h11]
    exact hgm.aestronglyMeasurable.congr h_eq'.symm
  have h_f_int : Integrable f_sphere volume :=
    ⟨h_f_ae, h_finint⟩
  have h_f_sphere_locint : LocallyIntegrable f_sphere volume :=
    h_f_int.locallyIntegrable

  -- Step 0d: Strong Lebesgue differentiation (one-sided)
  have h_leb_ae : ∀ᵐ (r : ℝ) ∂volume.restrict (Set.Ioi 0),
      Tendsto (fun h : ℝ => (1 / h) * ∫ t in r..(r + h), |f_sphere t - f_sphere r|)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have h_main_ae : ∀ᵐ (r : ℝ) ∂volume,
        ∀ {ι : Type} {l : Filter ι} (w : ι → ℝ) (δ : ι → ℝ),
          Tendsto δ l (nhdsWithin 0 (Set.Ioi 0)) →
            (∀ᶠ (j : ι) in l, r ∈ Metric.closedBall (w j) (1 * δ j)) →
              Tendsto (fun j : ι => ⨍ (y : ℝ) in Metric.closedBall (w j) (δ j), ‖f_sphere y - f_sphere r‖)
                l (nhds 0) :=
      IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub volume h_f_sphere_locint (1 : ℝ)
    rw [ae_restrict_iff' isOpen_Ioi.measurableSet]
    filter_upwards [h_main_ae] with r hr
    let w : ℝ → ℝ := fun h => r + h / 2
    let δ : ℝ → ℝ := fun h => h / 2
    have hδ_cont : Continuous δ := by fun_prop
    have hδ_maps : ∀ h ∈ Set.Ioi (0 : ℝ), δ h ∈ Set.Ioi (0 : ℝ) := by
      intro h hh; exact half_pos (show 0 < h from hh)
    have h_le : (nhdsWithin (0 : ℝ) (Set.Ioi 0)) ≤ nhds (0 : ℝ) := nhdsWithin_le_nhds
    have hδ0 : δ 0 = 0 := by simp [δ]
    have h_tendsto_nhds : Tendsto δ (nhds 0) (nhds 0) := by
      simpa [hδ0] using hδ_cont.tendsto 0
    have hδ_tendsto1 : Tendsto δ (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
      h_tendsto_nhds.mono_left h_le
    have hδ_eventually : ∀ᶠ (h : ℝ) in nhdsWithin 0 (Set.Ioi 0), δ h ∈ Set.Ioi 0 := by
      filter_upwards [self_mem_nhdsWithin] with h hh
      exact hδ_maps h hh
    have hδ_tendsto : Tendsto δ (nhdsWithin 0 (Set.Ioi 0)) (nhdsWithin 0 (Set.Ioi 0)) := by
      rw [tendsto_nhdsWithin_iff]
      exact ⟨hδ_tendsto1, hδ_eventually⟩
    have h_mem : ∀ᶠ (h : ℝ) in nhdsWithin 0 (Set.Ioi 0), r ∈ Metric.closedBall (w h) (1 * δ h) := by
      filter_upwards [self_mem_nhdsWithin] with h hh
      have h_pos : 0 < h := hh
      have h9 : dist r (w h) = h / 2 := by
        have h_nonneg : 0 ≤ h := by linarith
        simp [w, dist_eq_norm, Real.norm_eq_abs, abs_of_nonneg h_nonneg] <;> ring
      simpa [Metric.mem_closedBall] using h9.le
    have h_tendsto := hr (w := w) (δ := δ) hδ_tendsto h_mem
    have h_final : Tendsto (fun h : ℝ => (1 / h) * ∫ t in r..(r + h), |f_sphere t - f_sphere r|)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      have h_congr : (fun h : ℝ => ⨍ (y : ℝ) in Metric.closedBall (w h) (δ h), ‖f_sphere y - f_sphere r‖)
          =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
          (fun h : ℝ => (1 / h) * ∫ t in r..(r + h), |f_sphere t - f_sphere r|) := by
        filter_upwards [self_mem_nhdsWithin] with h hh
        have h_pos : 0 < h := hh
        have h_ball : Metric.closedBall (w h) (δ h) = Set.Icc r (r + h) := by
          ext y
          simp only [w, δ, Metric.mem_closedBall, Set.mem_Icc]
          have h5 : dist y (r + h / 2) = |y - (r + h / 2)| := by
            simp [dist_eq_norm, Real.norm_eq_abs]
          rw [h5]
          constructor
          · intro h6
            have h7 : |y - (r + h / 2)| ≤ h / 2 := h6
            have h8 : -h / 2 ≤ y - (r + h / 2) := by linarith [abs_le.mp h7]
            have h9 : y - (r + h / 2) ≤ h / 2 := by linarith [abs_le.mp h7]
            constructor <;> linarith
          · rintro ⟨h10, h11⟩
            have h12 : -h / 2 ≤ y - (r + h / 2) := by linarith
            have h13 : y - (r + h / 2) ≤ h / 2 := by linarith
            have h14 : |y - (r + h / 2)| ≤ h / 2 := by
              rw [abs_le] <;> constructor <;> linarith
            exact h14
        rw [h_ball]
        have h_vol : volume (Set.Icc r (r + h)) = ENNReal.ofReal h := by
          rw [Real.volume_Icc] <;> simp [h_pos.ne'] <;> ring
        have h_int_eq : ∫ t in Set.Icc r (r + h), |f_sphere t - f_sphere r| =
            ∫ t in r..(r + h), |f_sphere t - f_sphere r| := by
          have h_union : Set.Icc r (r + h) = Set.Ioc r (r + h) ∪ {r} := by
            ext z
            simp only [Set.mem_Icc, Set.mem_Ioc, Set.mem_union, Set.mem_singleton_iff]
            constructor
            · rintro ⟨h1, h2⟩
              by_cases h_eq : r = z
              · exact Or.inr h_eq.symm
              · have h_lt : r < z := by
                  exact lt_of_le_of_ne h1 h_eq
                exact Or.inl ⟨h_lt, h2⟩
            · rintro (h | rfl)
              · exact ⟨h.1.le, h.2⟩
              · exact ⟨by linarith, by linarith⟩
          rw [h_union]
          have h_disj : Disjoint (Set.Ioc r (r + h)) ({r} : Set ℝ) := by simp
          have hfs1 : IntegrableOn f_sphere (Set.Ioc r (r + h)) volume :=
            h_f_int.integrableOn
          have hfs2 : IntegrableOn (fun (_ : ℝ) => f_sphere r) (Set.Ioc r (r + h)) volume :=
            integrable_const (f_sphere r)
          have hfs_diff : IntegrableOn (fun t : ℝ => f_sphere t - f_sphere r) (Set.Ioc r (r + h)) volume :=
            hfs1.sub hfs2
          have hfs : IntegrableOn (fun t : ℝ => |f_sphere t - f_sphere r|) (Set.Ioc r (r + h)) volume :=
            hfs_diff.abs
          have hft : IntegrableOn (fun t : ℝ => |f_sphere t - f_sphere r|) ({r} : Set ℝ) volume := by
            simp
          rw [MeasureTheory.setIntegral_union h_disj (measurableSet_singleton r) hfs hft]
          have h_singleton : ∫ t in ({r} : Set ℝ), |f_sphere t - f_sphere r| = 0 := by simp
          rw [h_singleton, add_zero]
          <;> rw [intervalIntegral.integral_of_le (by linarith)]
        have h_avg : (⨍ (y : ℝ) in Set.Icc r (r + h), ‖f_sphere y - f_sphere r‖) =
            (1 / h) * ∫ t in r..(r + h), |f_sphere t - f_sphere r| := by
          rw [MeasureTheory.setAverage_eq volume (fun y => ‖f_sphere y - f_sphere r‖) (Set.Icc r (r + h))]
          have h_real : volume.real (Set.Icc r (r + h)) = h := by
            rw [Measure.real, h_vol]
            rw [ENNReal.toReal_ofReal (by linarith)]
          rw [h_real]
          have h9 : h⁻¹ • ∫ (x : ℝ) in Set.Icc r (r + h), ‖f_sphere x - f_sphere r‖ =
              (1 / h) * ∫ t in r..(r + h), |f_sphere t - f_sphere r| := by
            have h10 : ∫ (x : ℝ) in Set.Icc r (r + h), ‖f_sphere x - f_sphere r‖ =
                ∫ t in r..(r + h), |f_sphere t - f_sphere r| := h_int_eq
            rw [h10]
            simp [smul_eq_mul] <;> field_simp [h_pos.ne'] <;> ring
          exact h9
        exact h_avg
      exact h_tendsto.congr' h_congr
    intro _
    exact h_final

  -- Sphere perimeter measure null a.e.
  have h_sphere_null : ∀ᵐ (r : ℝ) ∂volume.restrict (Set.Ioi 0), μ (sphere x r) = 0 :=
    sphere_measure_null_ae x

  -- Good r: both Lebesgue point and sphere null
  have h_good : ∀ᵐ (r : ℝ) ∂volume.restrict (Set.Ioi 0),
      (Tendsto (fun h : ℝ => (1 / h) * ∫ t in r..(r + h), |f_sphere t - f_sphere r|)
          (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)) ∧
      μ (sphere x r) = 0 := by
    filter_upwards [h_leb_ae, h_sphere_null] with r h1 h2
    exact ⟨h1, h2⟩

  have h_pos : ∀ᵐ (r : ℝ) ∂volume.restrict (Set.Ioi 0), 0 < r := by
    filter_upwards [ae_restrict_mem isOpen_Ioi.measurableSet] with r hr
    exact hr
  filter_upwards [h_pos, h_good] with r hr_pos hr
  rcases hr with ⟨hr_leb, hr_sphere⟩

  let η : ℝ → E n → ℝ := fun L => radialCutoff x r L
  let ψ : ℝ → E n → E n := fun L y => η L y • ν
  let w : ℝ → ℝ := fun s => |deriv smoothStep s|

  have hw_nonneg : ∀ t, 0 ≤ w t := fun t => abs_nonneg _
  have hw_int : ∫ t in (0 : ℝ)..1, w t = 1 := smoothStep_deriv_abs_integral
  have hw_cont : Continuous w := (smoothStep_contDiff.continuous_deriv (by norm_num)).abs
  have hw_support : ∀ t ∉ Set.Icc (0 : ℝ) 1, w t = 0 := by
    intro t ht
    have h : deriv smoothStep t = 0 := smoothStep_deriv_zero_outside ht
    simp [w, h]

  -- Step 1: For each L > 0, integral formula and bound
  have h_step1 : ∀ (L : ℝ), 0 < L →
      |∫ᵛ y, ψ L y ∂[innerBilinear; D]| ≤
      ∫ t in (0 : ℝ)..1, w t * f_sphere (r + L * t) := by
    intro L hL
    have hη_smooth := radialCutoff_contDiff (x₀ := x) hr_pos hL
    have hν_const : ContDiff ℝ ∞ (fun (_ : E n) => ν) := contDiff_const
    have hψ_smooth := hη_smooth.smul hν_const
    have hη_zero : ∀ y, y ∉ ball x (r + L) → η L y = 0 :=
      fun y hy => radialCutoff_zero_of_not_mem_ball (hr := hr_pos) (hL := hL) (h := hy)
    have hψ_support : Function.support (ψ L) ⊆ closedBall x (r + L) := by
      intro y hy
      by_cases h : y ∈ ball x (r + L)
      · exact ball_subset_closedBall h
      · have h2 : η L y = 0 := hη_zero y h
        have h3 : ψ L y = 0 := by simp [ψ, h2]
        simpa [Function.mem_support] using hy h3
    have hψ_compact : HasCompactSupport (ψ L) :=
      (isCompact_closedBall x (r + L)).of_isClosed_subset (isClosed_tsupport _)
        (closure_minimal hψ_support isClosed_closedBall)
    have h_div : ∀ y, divergence (ψ L) y = fderiv ℝ (η L) y ν := by
      intro y
      have h1 : divergence (ψ L) = fun y => fderiv ℝ (η L) y ν :=
        divergence_smul_const hη_smooth
      exact congrFun h1 y

    have h_main_eq : ∫ᵛ y, ψ L y ∂[innerBilinear; D] =
        ∫ y in U, fderiv ℝ (η L) y ν := by
      have h := distributionalDerivative_integral_formula U hfin (ψ L) hψ_smooth hψ_compact
      simpa [h_div] using h

    -- Bound by norm
    have h1_point : ∀ y, |fderiv ℝ (η L) y ν| ≤ ‖fderiv ℝ (η L) y‖ := by
      intro y
      have h2 : |fderiv ℝ (η L) y ν| ≤ ‖fderiv ℝ (η L) y‖ * ‖ν‖ :=
        ContinuousLinearMap.le_opNorm (fderiv ℝ (η L) y) ν
      rw [hν_unit] at h2 <;> linarith
    have hη1 : ContDiff ℝ 1 (η L) := ContDiff.of_le hη_smooth (by norm_num)
    have h_fderiv_cont : Continuous (fderiv ℝ (η L)) :=
      hη1.continuous_fderiv (by norm_num)
    have h_fderiv_support : Function.support (fderiv ℝ (η L)) ⊆ closedBall x (r + L) := by
      intro y hy
      by_cases h : y ∈ closedBall x (r + L)
      · exact h
      · have h_dist : r + L < dist y x := by simpa [closedBall, not_le] using h
        have h_dist_cont : Continuous (fun z : E n => dist z x) := by fun_prop
        have h4 : ∀ᶠ z in nhds y, r + L < dist z x :=
          h_dist_cont.continuousAt.eventually (IsOpen.mem_nhds isOpen_Ioi h_dist)
        have h5 : ∀ᶠ z in nhds y, η L z = 0 := by
          filter_upwards [h4] with z hz
          have h6 : z ∉ ball x (r + L) := by simpa [ball, not_lt] using le_of_lt hz
          exact radialCutoff_zero_of_not_mem_ball (hr := hr_pos) (hL := hL) (h := h6)
        have h_const : HasFDerivAt (fun (_ : E n) => (0 : ℝ)) (0 : E n →L[ℝ] ℝ) y :=
          hasFDerivAt_const (0 : ℝ) y
        have h6 : HasFDerivAt (η L) (0 : E n →L[ℝ] ℝ) y :=
          h_const.congr_of_eventuallyEq h5
        have h7 : fderiv ℝ (η L) y = 0 := h6.fderiv
        simpa [Function.mem_support] using hy h7
    have h_cb : IsCompact (closedBall x (r + L)) := isCompact_closedBall x (r + L)
    have h_norm_cont : Continuous (fun y : E n => ‖fderiv ℝ (η L) y‖) := h_fderiv_cont.norm
    have h_norm_support : Function.support (fun y : E n => ‖fderiv ℝ (η L) y‖) ⊆ closedBall x (r + L) := by
      intro y hy
      have h7 : fderiv ℝ (η L) y ≠ 0 := by
        intro h8; have h9 : ‖fderiv ℝ (η L) y‖ = 0 := by rw [h8] <;> simp
        exact hy h9
      exact h_fderiv_support h7
    have h_norm_compact : HasCompactSupport (fun y : E n => ‖fderiv ℝ (η L) y‖) :=
      h_cb.of_isClosed_subset (isClosed_tsupport _) (closure_minimal h_norm_support isClosed_closedBall)
    have h_norm_int : Integrable (fun y : E n => ‖fderiv ℝ (η L) y‖) (volume.restrict U) :=
      h_norm_cont.integrable_of_hasCompactSupport h_norm_compact
    have h_eval : Continuous (fun (g : E n →L[ℝ] ℝ) => g ν) := continuous_eval_const ν
    have h_cont : Continuous (fun y : E n => fderiv ℝ (η L) y ν) :=
      h_eval.comp h_fderiv_cont
    have h_support2 : Function.support (fun y : E n => fderiv ℝ (η L) y ν) ⊆ closedBall x (r + L) := by
      intro y hy
      have h8 : (fderiv ℝ (η L) y) ν ≠ 0 := by simpa [Function.mem_support] using hy
      have h9 : fderiv ℝ (η L) y ≠ 0 := by intro h10; rw [h10] at h8; simp at h8
      exact h_fderiv_support h9
    have h_compact2 : HasCompactSupport (fun y : E n => fderiv ℝ (η L) y ν) :=
      h_cb.of_isClosed_subset (isClosed_tsupport _) (closure_minimal h_support2 isClosed_closedBall)
    have h_int : Integrable (fun y : E n => fderiv ℝ (η L) y ν) (volume.restrict U) :=
      h_cont.integrable_of_hasCompactSupport h_compact2
    have h_bound : |∫ y in U, fderiv ℝ (η L) y ν| ≤ ∫ y in U, ‖fderiv ℝ (η L) y‖ := by
      have h_abs : |∫ y in U, fderiv ℝ (η L) y ν| ≤ ∫ y in U, |fderiv ℝ (η L) y ν| :=
        abs_integral_le_integral_abs
      have h_mono : ∫ y in U, |fderiv ℝ (η L) y ν| ≤ ∫ y in U, ‖fderiv ℝ (η L) y‖ :=
        integral_mono_ae h_int.abs h_norm_int (by filter_upwards with z; exact h1_point z)
      calc
        |∫ y in U, fderiv ℝ (η L) y ν|
          ≤ ∫ y in U, |fderiv ℝ (η L) y ν| := h_abs
        _ ≤ ∫ y in U, ‖fderiv ℝ (η L) y‖ := h_mono

    -- Coarea bound
    let g : ℝ → ℝ := fun t => w ((t - r) / L) / L
    have hg_nonneg : ∀ t, 0 ≤ g t := by intro t; positivity
    have hg_cont : Continuous g := by
      have hL_ne : L ≠ 0 := hL.ne'
      have h_inner : Continuous (fun t : ℝ => (t - r) / L) := by fun_prop
      exact hw_cont.comp h_inner |>.div continuous_const (by simp [hL_ne])
    have h_support_g : ∀ t ∉ Set.Icc r (r + L), g t = 0 := by
      intro t ht
      have h5 : (t - r) / L ∉ Set.Icc (0 : ℝ) 1 := by
        simp only [Set.mem_Icc, not_and_or] at ht
        rcases ht with (h | h)
        · have h52 : (t - r) / L < 0 := div_neg_of_neg_of_pos (by linarith) hL
          intro h53; have h54 : 0 ≤ (t - r) / L := h53.1; linarith
        · have h52 : 1 < (t - r) / L := by rw [one_lt_div hL] <;> linarith
          intro h53; have h54 : (t - r) / L ≤ 1 := h53.2; linarith
      have h6 : w ((t - r) / L) = 0 := hw_support ((t - r) / L) h5
      simp [g, h6]
    have h_grad_ae : ∀ᵐ (y : E n) ∂volume.restrict U,
        ‖fderiv ℝ (η L) y‖ ≤ g (dist y x) := by
      filter_upwards with y
      by_cases hy : y = x
      · rw [hy]
        have h_center : fderiv ℝ (η L) x = 0 := radialCutoff_fderiv_at_center hr_pos hL
        rw [h_center]
        have h_goal : ‖(0 : E n →L[ℝ] ℝ)‖ ≤ g (dist x x) := by
          simpa using hg_nonneg (dist x x)
        exact h_goal
      · have h : ‖fderiv ℝ (η L) y‖ ≤ w ((dist y x - r) / L) / L :=
          radialCutoff_fderiv_tight_bound hr_pos hL hy
        simpa [g, w] using h
    have h_g_cont : Continuous (fun y : E n => g (dist y x)) := by fun_prop
    have h_g_support : Function.support (fun y : E n => g (dist y x)) ⊆ closedBall x (r + L) := by
      intro y hy
      by_cases h : y ∈ closedBall x (r + L)
      · exact h
      · have h_dist : r + L < dist y x := by simpa [closedBall, not_le] using h
        have h_not : dist y x ∉ Set.Icc r (r + L) := by
          simp only [Set.mem_Icc, not_and_or]; right; linarith
        have h10 : g (dist y x) = 0 := h_support_g (dist y x) h_not
        simpa [Function.mem_support] using hy h10
    have h_g_compact : HasCompactSupport (fun y : E n => g (dist y x)) :=
      h_cb.of_isClosed_subset (isClosed_tsupport _) (closure_minimal h_g_support isClosed_closedBall)
    have h_g_int : Integrable (fun y : E n => g (dist y x)) (volume.restrict U) :=
      h_g_cont.integrable_of_hasCompactSupport h_g_compact
    have h_integral_mono : ∫ y in U, ‖fderiv ℝ (η L) y‖ ≤ ∫ y in U, g (dist y x) :=
      integral_mono_ae h_norm_int h_g_int h_grad_ae

    have h_coarea_eq : ∫ y in U, g (dist y x) =
        ∫ t in Set.Ioi 0, g t * f_sphere t :=
      weighted_distance_coarea hU hBdd x g hg_nonneg hg_cont hn

    have h_prod_ae : AEStronglyMeasurable (fun t : ℝ => g t * f_sphere t) volume :=
      hg_cont.aestronglyMeasurable.mul h_f_ae
    have h_bdd : ∃ M, 0 ≤ M ∧ ∀ t ∈ Set.Icc r (r + L), |g t| ≤ M := by
      have h_cont_on : ContinuousOn g (Set.Icc r (r + L)) := hg_cont.continuousOn
      have h : BddAbove (Set.image g (Set.Icc r (r + L))) :=
        isCompact_Icc.bddAbove_image h_cont_on
      rcases h with ⟨M, hM⟩
      refine ⟨max M 0, by positivity, fun t ht => ?_⟩
      have h1 : g t ∈ Set.image g (Set.Icc r (r + L)) := ⟨t, ht, rfl⟩
      have h2 : g t ≤ M := hM h1
      have h3 : 0 ≤ g t := hg_nonneg t
      rw [abs_of_nonneg h3]; exact le_trans h2 (le_max_left M 0)
    rcases h_bdd with ⟨M, hM_nonneg, hM_Icc⟩
    have hM_bdd : ∀ t, |g t| ≤ M := by
      intro t
      by_cases ht : t ∈ Set.Icc r (r + L)
      · exact hM_Icc t ht
      · have h3 : g t = 0 := h_support_g t ht
        rw [h3, abs_zero] <;> exact hM_nonneg
    have h4 : ∀ᵐ (t : ℝ), ‖(g t * f_sphere t)‖ ≤ ‖(M * |f_sphere t|)‖ := by
      filter_upwards with t
      have h5 : |g t * f_sphere t| ≤ M * |f_sphere t| := by
        calc
          |g t * f_sphere t| = |g t| * |f_sphere t| := by rw [abs_mul]
          _ ≤ M * |f_sphere t| := by gcongr <;> exact hM_bdd t
      have hM_abs : |M| = M := abs_of_nonneg hM_nonneg
      simpa [Real.norm_eq_abs, hM_abs] using h5
    have h5 : Integrable (fun t : ℝ => M * |f_sphere t|) volume :=
      h_f_int.abs.const_mul M
    have h_prod_int : Integrable (fun t : ℝ => g t * f_sphere t) volume :=
      Integrable.mono h5 h_prod_ae h4

    have h_deriv0 : deriv smoothStep 0 = 0 := by
      have h_cont : Continuous (deriv smoothStep) := smoothStep_contDiff.continuous_deriv (by norm_num)
      have h_neg : ∀ t < 0, deriv smoothStep t = 0 := by
        intro t ht
        exact smoothStep_deriv_zero_outside (by simp [ht])
      have h_lim1 : Tendsto (deriv smoothStep) (nhdsWithin 0 (Set.Iio 0)) (nhds (deriv smoothStep 0)) :=
        h_cont.continuousAt.tendsto.mono_left inf_le_left
      have h_lim2 : Tendsto (deriv smoothStep) (nhdsWithin 0 (Set.Iio 0)) (nhds 0) := by
        have h_eventually : (deriv smoothStep) =ᶠ[nhdsWithin 0 (Set.Iio 0)] (fun _ => 0) := by
          filter_upwards [self_mem_nhdsWithin] with t ht
          exact h_neg t ht
        exact tendsto_const_nhds.congr' h_eventually.symm
      exact tendsto_nhds_unique h_lim1 h_lim2
    have h_w0 : w 0 = 0 := by
      simp [w, h_deriv0]
    have h1 : ∀ t ∉ Set.Ioc r (r + L), g t * f_sphere t = 0 := by
      intro t ht
      by_cases h_eq : t = r
      · rw [h_eq]
        have h_gr : g r = 0 := by
          dsimp only [g]
          have h_eq : (r - r) / L = 0 := by ring
          rw [h_eq]
          have h : w 0 = 0 := h_w0
          rw [h] <;> ring
        rw [h_gr] <;> ring
      · have h2 : t ∉ Set.Icc r (r + L) := by
          intro h3
          have h4 : r < t := lt_of_le_of_ne h3.1 (Ne.symm h_eq)
          exact ht ⟨h4, h3.2⟩
        have h4 : g t = 0 := h_support_g t h2
        rw [h4] <;> ring
    have h3 : Set.Ioc r (r + L) ⊆ Set.Ioi 0 := by
      intro t ht
      have h4 : r < t := ht.1
      exact lt_trans hr_pos h4
    have h_integral_Ioc : ∫ t in Set.Ioi 0, g t * f_sphere t =
        ∫ t in Set.Ioc r (r + L), g t * f_sphere t := by
      have h5 : ∀ᵐ (t : ℝ) ∂volume.restrict (Set.Ioi 0),
          (g t * f_sphere t) = (Set.Ioc r (r + L)).indicator (fun t => g t * f_sphere t) t := by
        filter_upwards with t
        by_cases h6 : t ∈ Set.Ioc r (r + L)
        · simp [h6]
        · have h7 : g t * f_sphere t = 0 := h1 t h6
          simp [h6, h7]
      have h6 : ∫ t in Set.Ioi 0, g t * f_sphere t =
          ∫ t in Set.Ioi 0, (Set.Ioc r (r + L)).indicator (fun t => g t * f_sphere t) t := by
        rw [integral_congr_ae h5]
      rw [h6, integral_indicator measurableSet_Ioc]
      have h7 : (volume.restrict (Set.Ioi 0)).restrict (Set.Ioc r (r + L)) = volume.restrict (Set.Ioc r (r + L)) := by
        rw [Measure.restrict_restrict measurableSet_Ioc]
        have h_inter : (Set.Ioc r (r + L)) ∩ (Set.Ioi 0) = Set.Ioc r (r + L) := by
          rw [Set.inter_comm]
          exact Set.inter_eq_right.mpr h3
        rw [h_inter]
      simpa [h7] using rfl
    have h_interval : ∫ t in Set.Ioc r (r + L), g t * f_sphere t =
        ∫ t in r..(r + L), g t * f_sphere t := by
      rw [intervalIntegral.integral_of_le (by linarith)]
    let H : ℝ → ℝ := fun t => g t * f_sphere t
    have hH_on1 : IntegrableOn H (Set.Ioc r (r + L)) volume :=
      h_prod_int.mono_measure Measure.restrict_le_self
    have hH_on2 : IntegrableOn H (Set.Ioc (r + L) r) volume := by
      have h_empty : Set.Ioc (r + L) r = ∅ := by
        ext z; simp only [Set.mem_Ioc, Set.mem_empty_iff_false, iff_false]; intro h; linarith
      rw [h_empty]; simp
    let hH_ii : IntervalIntegrable H volume r (r + L) := ⟨hH_on1, hH_on2⟩
    have h_change : ∫ t in r..(r + L), H t = ∫ t in (0 : ℝ)..1, w t * f_sphere (r + L * t) := by
      have hL_ne : L ≠ 0 := hL.ne'
      have h_at : ∀ u : ℝ, H (L * u + r) = (w u * f_sphere (r + L * u)) / L := by
        intro u
        have h_div : ((L * u + r) - r) / L = u := by field_simp [hL_ne] <;> ring
        have h_comm : r + L * u = L * u + r := by ring
        dsimp only [H, g]
        calc
          (w (((L * u + r) - r) / L) / L) * f_sphere (L * u + r)
            = (w u / L) * f_sphere (r + L * u) := by rw [h_div, h_comm] <;> ring
        _ = (w u * f_sphere (r + L * u)) / L := by ring
      have h15 := intervalIntegral.integral_comp_mul_add (a := 0) (b := 1) (c := L) (d := r) H (by linarith)
      have h_end1 : L * (0 : ℝ) + r = r := by ring
      have h_end2 : L * (1 : ℝ) + r = r + L := by ring
      have h15' : ∫ u in (0 : ℝ)..1, H (L * u + r) = L⁻¹ • ∫ t in r..(r + L), H t := by
        rw [h15, h_end1, h_end2]
      have h16 : ∫ u in (0 : ℝ)..1, H (L * u + r) = ∫ u in (0 : ℝ)..1, (w u * f_sphere (r + L * u)) / L := by
        apply intervalIntegral.integral_congr; intro u _; exact h_at u
      have h17 : L⁻¹ • ∫ t in r..(r + L), H t = ∫ u in (0 : ℝ)..1, (w u * f_sphere (r + L * u)) / L := by
        rw [←h16, h15']
      have h18 : ∫ t in r..(r + L), H t = ∫ u in (0 : ℝ)..1, w u * f_sphere (r + L * u) := by
        have h19 : L * (L⁻¹ • ∫ t in r..(r + L), H t) = L * (∫ u in (0 : ℝ)..1, (w u * f_sphere (r + L * u)) / L) :=
          congr_arg (fun x : ℝ => L * x) h17
        have h_left : L * (L⁻¹ • ∫ t in r..(r + L), H t) = ∫ t in r..(r + L), H t := by
          simp [smul_eq_mul, hL_ne] <;> field_simp [hL_ne] <;> ring
        have h_right : L * (∫ u in (0 : ℝ)..1, (w u * f_sphere (r + L * u)) / L) =
            ∫ u in (0 : ℝ)..1, w u * f_sphere (r + L * u) := by
          simp [smul_eq_mul, hL_ne] <;> field_simp [hL_ne] <;> ring
        calc
          ∫ t in r..(r + L), H t
            = L * (L⁻¹ • ∫ t in r..(r + L), H t) := h_left.symm
          _ = L * (∫ u in (0 : ℝ)..1, (w u * f_sphere (r + L * u)) / L) := h19
          _ = ∫ u in (0 : ℝ)..1, w u * f_sphere (r + L * u) := h_right
      exact h18

    have h_coarea_bound : ∫ y in U, ‖fderiv ℝ (η L) y‖ ≤
        ∫ t in (0 : ℝ)..1, w t * f_sphere (r + L * t) := by
      calc
        ∫ y in U, ‖fderiv ℝ (η L) y‖
          ≤ ∫ y in U, g (dist y x) := h_integral_mono
        _ = ∫ t in Set.Ioi 0, g t * f_sphere t := h_coarea_eq
        _ = ∫ t in Set.Ioc r (r + L), g t * f_sphere t := h_integral_Ioc
        _ = ∫ t in r..(r + L), g t * f_sphere t := h_interval
        _ = ∫ t in (0 : ℝ)..1, w t * f_sphere (r + L * t) := h_change

    rw [h_main_eq]
    exact le_trans h_bound h_coarea_bound

  -- Step 2: LHS limit as L → 0 via DCT (adapted from CutoffInequality)
  classical
  let f_limit : E n → E n := fun y => if y ∈ closedBall x r then ν else 0
  let g_L : ℝ → E n → ℝ := fun L y => inner ℝ (ψ L y) (f_normal y)
  let g_limit : E n → ℝ := fun y => inner ℝ (f_limit y) (f_normal y)

  have h_pointwise : ∀ y ∉ sphere x r,
      Tendsto (fun L : ℝ => ψ L y) (nhdsWithin 0 (Set.Ioi 0)) (nhds (f_limit y)) := by
    intro y hy
    have h_dist : dist y x ≠ r := by simpa [Metric.mem_sphere, dist_eq_norm] using hy
    by_cases h_in : y ∈ closedBall x r
    · have h_lt : dist y x < r := by
        have h_le : dist y x ≤ r := by simpa [closedBall] using h_in
        exact lt_of_le_of_ne h_le h_dist
      have h_nhds : Set.Ioi (0 : ℝ) ∈ nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) := self_mem_nhdsWithin
      have h_eventually : (fun L : ℝ => ψ L y) =ᶠ[nhdsWithin 0 (Set.Ioi 0)] (fun (_ : ℝ) => ν) := by
        filter_upwards [h_nhds] with L hL
        have h : η L y = 1 := radialCutoff_one_of_mem_closedBall hr_pos hL h_in
        simp [ψ, h]
      have h_f : f_limit y = ν := by dsimp only [f_limit]; rw [if_pos h_in]
      rw [h_f]
      exact tendsto_const_nhds.congr' h_eventually.symm
    · have h_gt : r < dist y x := by
        by_contra h; have h_le : dist y x ≤ r := by linarith
        exact h_in (by simpa [closedBall] using h_le)
      have h_pos2 : 0 < dist y x - r := by linarith
      have h_small : Set.Ioo (0 : ℝ) (dist y x - r) ∈ nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) := by
        apply mem_nhdsWithin.mpr
        refine ⟨Set.Iio (dist y x - r), isOpen_Iio, h_pos2, ?_⟩
        intro z hz; exact ⟨hz.2, hz.1⟩
      have h_eventually : (fun L : ℝ => ψ L y) =ᶠ[nhdsWithin 0 (Set.Ioi 0)] (fun (_ : ℝ) => 0) := by
        filter_upwards [h_small] with L hL
        have hL_pos : 0 < L := hL.1
        have hL_lt : L < dist y x - r := hL.2
        have h3 : y ∉ ball x (r + L) := by simpa [ball, not_lt] using by linarith
        have h4 : η L y = 0 := radialCutoff_zero_of_not_mem_ball (hr := hr_pos) (hL := hL_pos) (h := h3)
        simp [ψ, h4]
      have h_f : f_limit y = 0 := by dsimp only [f_limit]; rw [if_neg h_in]
      rw [h_f]
      exact tendsto_const_nhds.congr' h_eventually.symm

  have h_sphere_ae : ∀ᵐ (y : E n) ∂μ, y ∉ sphere x r := by
    rw [ae_iff]
    have h_set : {y : E n | ¬(y ∉ sphere x r)} = sphere x r := by ext z; simp
    rw [h_set]; exact hr_sphere

  have h_ae : ∀ᵐ (y : E n) ∂μ,
      Tendsto (fun L : ℝ => ψ L y) (nhdsWithin 0 (Set.Ioi 0)) (nhds (f_limit y)) := by
    filter_upwards [h_sphere_ae] with y hy
    exact h_pointwise y hy

  have h_g_ae : ∀ᵐ (y : E n) ∂μ,
      Tendsto (fun L : ℝ => g_L L y) (nhdsWithin 0 (Set.Ioi 0)) (nhds (g_limit y)) := by
    filter_upwards [h_ae] with y hy
    have h_cont : Continuous (fun z : E n => inner ℝ z (f_normal y)) := by fun_prop
    exact h_cont.continuousAt.tendsto.comp hy

  have h_g_bound : ∃ (C : ℝ), ∀ᶠ (L : ℝ) in nhdsWithin 0 (Set.Ioi 0),
      ∀ᵐ (y : E n) ∂μ, ‖g_L L y‖ ≤ C := by
    refine ⟨1, ?_⟩
    have h_nhds : Set.Ioi (0 : ℝ) ∈ nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) := self_mem_nhdsWithin
    filter_upwards [h_nhds] with L hL
    have h_main : ∀ᵐ (y : E n) ∂μ, ‖g_L L y‖ ≤ 1 := by
      filter_upwards [hf_norm_le_one] with y hy
      have h1 : ‖g_L L y‖ = |inner ℝ (ψ L y) (f_normal y)| := by
        simp [g_L, Real.norm_eq_abs]
      rw [h1]
      have h2 : |inner ℝ (ψ L y) (f_normal y)| ≤ ‖ψ L y‖ * ‖f_normal y‖ := abs_real_inner_le_norm _ _
      have h3 : ‖ψ L y‖ ≤ 1 := by
        have h4 : 0 ≤ η L y := smoothStep_range.1
        have h5 : η L y ≤ 1 := smoothStep_range.2
        calc
          ‖ψ L y‖ = ‖η L y‖ * ‖ν‖ := norm_smul (η L y) ν
          _ = |η L y| * ‖ν‖ := by rw [Real.norm_eq_abs]
          _ = |η L y| := by rw [hν_unit] <;> ring
          _ ≤ 1 := by rw [abs_of_nonneg h4] <;> exact h5
      have h6 : ‖f_normal y‖ ≤ 1 := hy
      calc
        |inner ℝ (ψ L y) (f_normal y)| ≤ ‖ψ L y‖ * ‖f_normal y‖ := h2
        _ ≤ 1 * 1 := by gcongr
        _ = 1 := by ring
    exact h_main

  have h_nhds2 : Set.Ioi (0 : ℝ) ∈ nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) := self_mem_nhdsWithin
  have h_g_meas : ∀ᶠ (L : ℝ) in nhdsWithin 0 (Set.Ioi 0),
      AEStronglyMeasurable (g_L L) μ := by
    filter_upwards [h_nhds2] with L hL
    have h_cont : Continuous (ψ L) := by
      have hη_smooth := radialCutoff_contDiff (x₀ := x) hr_pos hL
      exact hη_smooth.continuous.smul continuous_const
    exact h_cont.aestronglyMeasurable.inner hf_int.1

  have hψ_int : ∀ (L : ℝ), 0 < L → Integrable (ψ L) μ := by
    intro L hL
    have h_cont : Continuous (ψ L) := by
      have hη_smooth := radialCutoff_contDiff (x₀ := x) hr_pos hL
      exact hη_smooth.continuous.smul continuous_const
    have h_support : Function.support (ψ L) ⊆ closedBall x (r + L) := by
      intro y hy
      by_cases h : y ∈ ball x (r + L)
      · exact ball_subset_closedBall h
      · have h2 : η L y = 0 := radialCutoff_zero_of_not_mem_ball hr_pos hL (h := h)
        have h3 : ψ L y = 0 := by simp [ψ, h2]
        simpa [Function.mem_support] using hy h3
    have h_cb : IsCompact (closedBall x (r + L)) := isCompact_closedBall x (r + L)
    have h_compact : HasCompactSupport (ψ L) :=
      h_cb.of_isClosed_subset (isClosed_tsupport _) (closure_minimal h_support isClosed_closedBall)
    exact h_cont.integrable_of_hasCompactSupport h_compact

  have h_flimit_int : Integrable f_limit μ := by
    have h1 : MeasurableSet (closedBall x r) := isClosed_closedBall.measurableSet
    have h_eq : f_limit = (closedBall x r).indicator (fun (_ : E n) => ν) := by
      funext y
      dsimp only [f_limit]
      by_cases h : y ∈ closedBall x r
      · rw [if_pos h, Set.indicator_apply, if_pos h]
      · rw [if_neg h, Set.indicator_apply, if_neg h]
    rw [h_eq]
    exact (integrable_const ν).indicator h1

  have h_dct : Tendsto (fun L : ℝ => ∫ y, g_L L y ∂μ)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (∫ y, g_limit y ∂μ)) :=
    tendsto_integral_filter_of_norm_le_const h_g_meas h_g_bound h_g_ae

  have h_conv1 : ∀ (L : ℝ), 0 < L →
      ∫ᵛ y, ψ L y ∂[innerBilinear; D] = ∫ y, g_L L y ∂μ := by
    intro L hL
    rw [hD_eq]
    exact integral_withDensityᵥ_inner hf_int hf_norm_le_one (hψ_int L hL)

  have h_conv2 : ∫ᵛ y, f_limit y ∂[innerBilinear; D] = ∫ y, g_limit y ∂μ := by
    rw [hD_eq]
    exact integral_withDensityᵥ_inner hf_int hf_norm_le_one h_flimit_int

  have h_eventually_eq : ∀ᶠ (L : ℝ) in nhdsWithin 0 (Set.Ioi 0),
      (∫ y, g_L L y ∂μ) = (∫ᵛ y, ψ L y ∂[innerBilinear; D]) :=
    Filter.mem_of_superset (self_mem_nhdsWithin) fun L hL => (h_conv1 L hL).symm

  have h_lhs_limit : Tendsto (fun L : ℝ => ∫ᵛ y, ψ L y ∂[innerBilinear; D])
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (∫ᵛ y, f_limit y ∂[innerBilinear; D])) := by
    have h5 : Tendsto (fun L : ℝ => ∫ y, g_L L y ∂μ)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (∫ᵛ y, f_limit y ∂[innerBilinear; D])) := by
      rw [←h_conv2] at h_dct
      exact h_dct
    exact h5.congr' h_eventually_eq

  have h_limit_eq : ∫ᵛ y, f_limit y ∂[innerBilinear; D] = inner ℝ (D (closedBall x r)) ν := by
    have h_cb : MeasurableSet (closedBall x r) := isClosed_closedBall.measurableSet
    have h_g_limit_eq : g_limit = (closedBall x r).indicator (fun y => inner ℝ ν (f_normal y)) := by
      funext y
      dsimp only [g_limit, f_limit]
      by_cases h : y ∈ closedBall x r
      · rw [if_pos h, Set.indicator_apply, if_pos h]
      · rw [if_neg h, Set.indicator_apply, if_neg h] <;> simp [inner_zero_left]
    have h_int_g : ∫ y, g_limit y ∂μ = ∫ y in closedBall x r, inner ℝ ν (f_normal y) ∂μ := by
      rw [h_g_limit_eq, MeasureTheory.integral_indicator h_cb]
    have hD_ball : D (closedBall x r) = ∫ y in closedBall x r, f_normal y ∂μ := by
      rw [hD_eq]
      exact withDensityᵥ_apply hf_int h_cb
    have h1 : ∫ y in closedBall x r, inner ℝ ν (f_normal y) ∂μ = inner ℝ ν (D (closedBall x r)) := by
      rw [hD_ball]
      exact integral_inner hf_int.integrableOn ν
    have h2 : inner ℝ ν (D (closedBall x r)) = inner ℝ (D (closedBall x r)) ν := by
      have h3 := inner_conj_symm (𝕜 := ℝ) (E := E n) ν (D (closedBall x r))
      exact h3.symm
    rw [h_conv2, h_int_g, h1, h2]

  rw [h_limit_eq] at h_lhs_limit

  -- Step 3: RHS limit via approximate identity
  have h_rhs_limit : Tendsto (fun L : ℝ => ∫ t in (0 : ℝ)..1, w t * f_sphere (r + L * t))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (f_sphere r)) :=
    approximate_identity_one_sided h_f_sphere_locint hw_cont hw_nonneg hw_support hw_int r hr_leb

  -- Step 4: Combine
  have h_main_bound : ∀ (L : ℝ), 0 < L →
      |∫ᵛ y, ψ L y ∂[innerBilinear; D]| ≤
      ∫ t in (0 : ℝ)..1, w t * f_sphere (r + L * t) := by
    intro L hL
    exact h_step1 L hL

  have h_eventually : ∀ᶠ (L : ℝ) in nhdsWithin 0 (Set.Ioi 0),
      |∫ᵛ y, ψ L y ∂[innerBilinear; D]| ≤
      ∫ t in (0 : ℝ)..1, w t * f_sphere (r + L * t) := by
    filter_upwards [self_mem_nhdsWithin] with L hL
    exact h_main_bound L hL

  exact le_of_tendsto_of_tendsto h_lhs_limit.abs h_rhs_limit h_eventually


-- ============================================================================
-- Tight cutoff inequality (unbounded sets)
-- ============================================================================

/-- **Tight cutoff inequality** for possibly unbounded sets.

For a.e. `r > 0`,
`|Dχ_U(closedBall x r) · ν| ≤ H^{n-1}(U ∩ sphere x r)`.

Same proof as `tight_cutoff_inequality`, but replaces the Eilenberg
global integrability step with `h_real_locally_integrable`, and uses
`weighted_distance_coarea_unbounded` for the coarea step. -/
lemma tight_cutoff_inequality_unbounded
    {U : Set (E n)} (hU : MeasurableSet U)
    (hfin : perimeter U < ⊤) (hn : 2 ≤ n)
    (x : E n) (ν : E n) (hν_unit : ‖ν‖ = 1) :
    ∀ᵐ (r : ℝ) ∂volume.restrict (Set.Ioi 0),
      |inner ℝ ((distributionalDerivative U) (closedBall x r)) ν| ≤
        (μHE[n - 1] (U ∩ sphere x r)).toReal := by
  let D := distributionalDerivative U
  let μ := perimeterMeasure U
  let f_normal := measureTheoreticNormal U
  have hD_eq : D = μ.withDensityᵥ f_normal := (measureTheoreticNormal_withDensity hfin).2
  have hf_int : Integrable f_normal μ := (measureTheoreticNormal_withDensity hfin).1
  have hf_norm_one : ∀ᵐ y ∂μ, ‖f_normal y‖ = 1 := norm_measureTheoreticNormal_eq_one hfin
  have hf_norm_le_one : ∀ᵐ y ∂μ, ‖f_normal y‖ ≤ 1 := by
    filter_upwards [hf_norm_one] with y hy <;> rw [hy] <;> norm_num
  have h_perim_eq : μ Set.univ = perimeter U := by exact Eq.symm (perimeter_eq_variation U hfin)
  letI hμ_fin : IsFiniteMeasure μ :=
    ⟨by rw [h_perim_eq] <;> exact hfin⟩

  let f_sphere : ℝ → ℝ := fun t => (μHE[n - 1] (U ∩ sphere x t)).toReal
  let F_sphere : ℝ → ENNReal := fun t => μHE[n - 1] (U ∩ sphere x t)
  haveI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp (by linarith)

  -- Step 0a: F_sphere is a.e. measurable
  have h_F_ae : AEStronglyMeasurable F_sphere volume :=
    distance_coarea_aemeasurable hn x U hU

  -- Step 0b (unbounded): f_sphere is locally integrable
  have h_f_sphere_locint : LocallyIntegrable f_sphere volume :=
    h_real_locally_integrable hn U hU x
  have h_f_ae : AEStronglyMeasurable f_sphere volume :=
    h_f_sphere_locint.aestronglyMeasurable

  -- Step 0c: Strong Lebesgue differentiation (one-sided)
  have h_leb_ae : ∀ᵐ (r : ℝ) ∂volume.restrict (Set.Ioi 0),
      Tendsto (fun h : ℝ => (1 / h) * ∫ t in r..(r + h), |f_sphere t - f_sphere r|)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have h_main_ae : ∀ᵐ (r : ℝ) ∂volume,
        ∀ {ι : Type} {l : Filter ι} (w : ι → ℝ) (δ : ι → ℝ),
          Tendsto δ l (nhdsWithin 0 (Set.Ioi 0)) →
            (∀ᶠ (j : ι) in l, r ∈ Metric.closedBall (w j) (1 * δ j)) →
              Tendsto (fun j : ι => ⨍ (y : ℝ) in Metric.closedBall (w j) (δ j), ‖f_sphere y - f_sphere r‖)
                l (nhds 0) :=
      IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub volume h_f_sphere_locint (1 : ℝ)
    rw [ae_restrict_iff' isOpen_Ioi.measurableSet]
    filter_upwards [h_main_ae] with r hr
    let w : ℝ → ℝ := fun h => r + h / 2
    let δ : ℝ → ℝ := fun h => h / 2
    have hδ_cont : Continuous δ := by fun_prop
    have hδ_maps : ∀ h ∈ Set.Ioi (0 : ℝ), δ h ∈ Set.Ioi (0 : ℝ) := by
      intro h hh; exact half_pos (show 0 < h from hh)
    have h_le : (nhdsWithin (0 : ℝ) (Set.Ioi 0)) ≤ nhds (0 : ℝ) := nhdsWithin_le_nhds
    have hδ0 : δ 0 = 0 := by simp [δ]
    have h_tendsto_nhds : Tendsto δ (nhds 0) (nhds 0) := by
      simpa [hδ0] using hδ_cont.tendsto 0
    have hδ_tendsto1 : Tendsto δ (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
      h_tendsto_nhds.mono_left h_le
    have hδ_eventually : ∀ᶠ (h : ℝ) in nhdsWithin 0 (Set.Ioi 0), δ h ∈ Set.Ioi 0 := by
      filter_upwards [self_mem_nhdsWithin] with h hh
      exact hδ_maps h hh
    have hδ_tendsto : Tendsto δ (nhdsWithin 0 (Set.Ioi 0)) (nhdsWithin 0 (Set.Ioi 0)) := by
      rw [tendsto_nhdsWithin_iff]
      exact ⟨hδ_tendsto1, hδ_eventually⟩
    have h_mem : ∀ᶠ (h : ℝ) in nhdsWithin 0 (Set.Ioi 0), r ∈ Metric.closedBall (w h) (1 * δ h) := by
      filter_upwards [self_mem_nhdsWithin] with h hh
      have h_pos : 0 < h := hh
      have h9 : dist r (w h) = h / 2 := by
        have h_nonneg : 0 ≤ h := by linarith
        simp [w, dist_eq_norm, Real.norm_eq_abs, abs_of_nonneg h_nonneg] <;> ring
      simpa [Metric.mem_closedBall] using h9.le
    have h_tendsto := hr (w := w) (δ := δ) hδ_tendsto h_mem
    have h_final : Tendsto (fun h : ℝ => (1 / h) * ∫ t in r..(r + h), |f_sphere t - f_sphere r|)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      have h_congr : (fun h : ℝ => ⨍ (y : ℝ) in Metric.closedBall (w h) (δ h), ‖f_sphere y - f_sphere r‖)
          =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
          (fun h : ℝ => (1 / h) * ∫ t in r..(r + h), |f_sphere t - f_sphere r|) := by
        filter_upwards [self_mem_nhdsWithin] with h hh
        have h_pos : 0 < h := hh
        have h_ball : Metric.closedBall (w h) (δ h) = Set.Icc r (r + h) := by
          ext y
          simp only [w, δ, Metric.mem_closedBall, Set.mem_Icc]
          have h5 : dist y (r + h / 2) = |y - (r + h / 2)| := by
            simp [dist_eq_norm, Real.norm_eq_abs]
          rw [h5]
          constructor
          · intro h6
            have h7 : |y - (r + h / 2)| ≤ h / 2 := h6
            have h8 : -h / 2 ≤ y - (r + h / 2) := by linarith [abs_le.mp h7]
            have h9 : y - (r + h / 2) ≤ h / 2 := by linarith [abs_le.mp h7]
            constructor <;> linarith
          · rintro ⟨h10, h11⟩
            have h12 : -h / 2 ≤ y - (r + h / 2) := by linarith
            have h13 : y - (r + h / 2) ≤ h / 2 := by linarith
            have h14 : |y - (r + h / 2)| ≤ h / 2 := by
              rw [abs_le] <;> constructor <;> linarith
            exact h14
        rw [h_ball]
        have h_vol : volume (Set.Icc r (r + h)) = ENNReal.ofReal h := by
          rw [Real.volume_Icc] <;> simp [h_pos.ne'] <;> ring
        have h_int_eq : ∫ t in Set.Icc r (r + h), |f_sphere t - f_sphere r| =
            ∫ t in r..(r + h), |f_sphere t - f_sphere r| := by
          have h_union : Set.Icc r (r + h) = Set.Ioc r (r + h) ∪ {r} := by
            ext z
            simp only [Set.mem_Icc, Set.mem_Ioc, Set.mem_union, Set.mem_singleton_iff]
            constructor
            · rintro ⟨h1, h2⟩
              by_cases h_eq : r = z
              · exact Or.inr h_eq.symm
              · have h_lt : r < z := by
                  exact lt_of_le_of_ne h1 h_eq
                exact Or.inl ⟨h_lt, h2⟩
            · rintro (h | rfl)
              · exact ⟨h.1.le, h.2⟩
              · exact ⟨by linarith, by linarith⟩
          rw [h_union]
          have h_disj : Disjoint (Set.Ioc r (r + h)) ({r} : Set ℝ) := by simp
          have h_Icc_compact : IsCompact (Set.Icc r (r + h)) := isCompact_Icc
          have hfs1 : IntegrableOn f_sphere (Set.Ioc r (r + h)) volume := by
            have h_Icc_int : IntegrableOn f_sphere (Set.Icc r (r + h)) volume :=
              h_f_sphere_locint.integrableOn_isCompact h_Icc_compact
            exact h_Icc_int.mono_set Set.Ioc_subset_Icc_self
          have hfs2 : IntegrableOn (fun (_ : ℝ) => f_sphere r) (Set.Ioc r (r + h)) volume :=
            integrable_const (f_sphere r)
          have hfs_diff : IntegrableOn (fun t : ℝ => f_sphere t - f_sphere r) (Set.Ioc r (r + h)) volume :=
            hfs1.sub hfs2
          have hfs : IntegrableOn (fun t : ℝ => |f_sphere t - f_sphere r|) (Set.Ioc r (r + h)) volume :=
            hfs_diff.abs
          have hft : IntegrableOn (fun t : ℝ => |f_sphere t - f_sphere r|) ({r} : Set ℝ) volume := by
            simp
          rw [MeasureTheory.setIntegral_union h_disj (measurableSet_singleton r) hfs hft]
          have h_singleton : ∫ t in ({r} : Set ℝ), |f_sphere t - f_sphere r| = 0 := by simp
          rw [h_singleton, add_zero]
          <;> rw [intervalIntegral.integral_of_le (by linarith)]
        have h_avg : (⨍ (y : ℝ) in Set.Icc r (r + h), ‖f_sphere y - f_sphere r‖) =
            (1 / h) * ∫ t in r..(r + h), |f_sphere t - f_sphere r| := by
          rw [MeasureTheory.setAverage_eq volume (fun y => ‖f_sphere y - f_sphere r‖) (Set.Icc r (r + h))]
          have h_real : volume.real (Set.Icc r (r + h)) = h := by
            rw [Measure.real, h_vol]
            rw [ENNReal.toReal_ofReal (by linarith)]
          rw [h_real]
          have h9 : h⁻¹ • ∫ (x : ℝ) in Set.Icc r (r + h), ‖f_sphere x - f_sphere r‖ =
              (1 / h) * ∫ t in r..(r + h), |f_sphere t - f_sphere r| := by
            have h10 : ∫ (x : ℝ) in Set.Icc r (r + h), ‖f_sphere x - f_sphere r‖ =
                ∫ t in r..(r + h), |f_sphere t - f_sphere r| := h_int_eq
            rw [h10]
            simp [smul_eq_mul] <;> field_simp [h_pos.ne'] <;> ring
          exact h9
        exact h_avg
      exact h_tendsto.congr' h_congr
    intro _
    exact h_final

  -- Sphere perimeter measure null a.e.
  have h_sphere_null : ∀ᵐ (r : ℝ) ∂volume.restrict (Set.Ioi 0), μ (sphere x r) = 0 :=
    sphere_measure_null_ae x

  -- Good r: both Lebesgue point and sphere null
  have h_good : ∀ᵐ (r : ℝ) ∂volume.restrict (Set.Ioi 0),
      (Tendsto (fun h : ℝ => (1 / h) * ∫ t in r..(r + h), |f_sphere t - f_sphere r|)
          (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)) ∧
      μ (sphere x r) = 0 := by
    filter_upwards [h_leb_ae, h_sphere_null] with r h1 h2
    exact ⟨h1, h2⟩

  have h_pos : ∀ᵐ (r : ℝ) ∂volume.restrict (Set.Ioi 0), 0 < r := by
    filter_upwards [ae_restrict_mem isOpen_Ioi.measurableSet] with r hr
    exact hr
  filter_upwards [h_pos, h_good] with r hr_pos hr
  rcases hr with ⟨hr_leb, hr_sphere⟩

  let η : ℝ → E n → ℝ := fun L => radialCutoff x r L
  let ψ : ℝ → E n → E n := fun L y => η L y • ν
  let w : ℝ → ℝ := fun s => |deriv smoothStep s|

  have hw_nonneg : ∀ t, 0 ≤ w t := fun t => abs_nonneg _
  have hw_int : ∫ t in (0 : ℝ)..1, w t = 1 := smoothStep_deriv_abs_integral
  have hw_cont : Continuous w := (smoothStep_contDiff.continuous_deriv (by norm_num)).abs
  have hw_support : ∀ t ∉ Set.Icc (0 : ℝ) 1, w t = 0 := by
    intro t ht
    have h : deriv smoothStep t = 0 := smoothStep_deriv_zero_outside ht
    simp [w, h]

  -- Step 1: For each L > 0, integral formula and bound
  have h_step1 : ∀ (L : ℝ), 0 < L →
      |∫ᵛ y, ψ L y ∂[innerBilinear; D]| ≤
      ∫ t in (0 : ℝ)..1, w t * f_sphere (r + L * t) := by
    intro L hL
    have hη_smooth := radialCutoff_contDiff (x₀ := x) hr_pos hL
    have hν_const : ContDiff ℝ ∞ (fun (_ : E n) => ν) := contDiff_const
    have hψ_smooth := hη_smooth.smul hν_const
    have hη_zero : ∀ y, y ∉ ball x (r + L) → η L y = 0 :=
      fun y hy => radialCutoff_zero_of_not_mem_ball (hr := hr_pos) (hL := hL) (h := hy)
    have hψ_support : Function.support (ψ L) ⊆ closedBall x (r + L) := by
      intro y hy
      by_cases h : y ∈ ball x (r + L)
      · exact ball_subset_closedBall h
      · have h2 : η L y = 0 := hη_zero y h
        have h3 : ψ L y = 0 := by simp [ψ, h2]
        simpa [Function.mem_support] using hy h3
    have hψ_compact : HasCompactSupport (ψ L) :=
      (isCompact_closedBall x (r + L)).of_isClosed_subset (isClosed_tsupport _)
        (closure_minimal hψ_support isClosed_closedBall)
    have h_div : ∀ y, divergence (ψ L) y = fderiv ℝ (η L) y ν := by
      intro y
      have h1 : divergence (ψ L) = fun y => fderiv ℝ (η L) y ν :=
        divergence_smul_const hη_smooth
      exact congrFun h1 y

    have h_main_eq : ∫ᵛ y, ψ L y ∂[innerBilinear; D] =
        ∫ y in U, fderiv ℝ (η L) y ν := by
      have h := distributionalDerivative_integral_formula U hfin (ψ L) hψ_smooth hψ_compact
      simpa [h_div] using h

    -- Bound by norm
    have h1_point : ∀ y, |fderiv ℝ (η L) y ν| ≤ ‖fderiv ℝ (η L) y‖ := by
      intro y
      have h2 : |fderiv ℝ (η L) y ν| ≤ ‖fderiv ℝ (η L) y‖ * ‖ν‖ :=
        ContinuousLinearMap.le_opNorm (fderiv ℝ (η L) y) ν
      rw [hν_unit] at h2 <;> linarith
    have hη1 : ContDiff ℝ 1 (η L) := ContDiff.of_le hη_smooth (by norm_num)
    have h_fderiv_cont : Continuous (fderiv ℝ (η L)) :=
      hη1.continuous_fderiv (by norm_num)
    have h_fderiv_support : Function.support (fderiv ℝ (η L)) ⊆ closedBall x (r + L) := by
      intro y hy
      by_cases h : y ∈ closedBall x (r + L)
      · exact h
      · have h_dist : r + L < dist y x := by simpa [closedBall, not_le] using h
        have h_dist_cont : Continuous (fun z : E n => dist z x) := by fun_prop
        have h4 : ∀ᶠ z in nhds y, r + L < dist z x :=
          h_dist_cont.continuousAt.eventually (IsOpen.mem_nhds isOpen_Ioi h_dist)
        have h5 : ∀ᶠ z in nhds y, η L z = 0 := by
          filter_upwards [h4] with z hz
          have h6 : z ∉ ball x (r + L) := by simpa [ball, not_lt] using le_of_lt hz
          exact radialCutoff_zero_of_not_mem_ball (hr := hr_pos) (hL := hL) (h := h6)
        have h_const : HasFDerivAt (fun (_ : E n) => (0 : ℝ)) (0 : E n →L[ℝ] ℝ) y :=
          hasFDerivAt_const (0 : ℝ) y
        have h6 : HasFDerivAt (η L) (0 : E n →L[ℝ] ℝ) y :=
          h_const.congr_of_eventuallyEq h5
        have h7 : fderiv ℝ (η L) y = 0 := h6.fderiv
        simpa [Function.mem_support] using hy h7
    have h_cb : IsCompact (closedBall x (r + L)) := isCompact_closedBall x (r + L)
    have h_norm_cont : Continuous (fun y : E n => ‖fderiv ℝ (η L) y‖) := h_fderiv_cont.norm
    have h_norm_support : Function.support (fun y : E n => ‖fderiv ℝ (η L) y‖) ⊆ closedBall x (r + L) := by
      intro y hy
      have h7 : fderiv ℝ (η L) y ≠ 0 := by
        intro h8; have h9 : ‖fderiv ℝ (η L) y‖ = 0 := by rw [h8] <;> simp
        exact hy h9
      exact h_fderiv_support h7
    have h_norm_compact : HasCompactSupport (fun y : E n => ‖fderiv ℝ (η L) y‖) :=
      h_cb.of_isClosed_subset (isClosed_tsupport _) (closure_minimal h_norm_support isClosed_closedBall)
    have h_norm_int : Integrable (fun y : E n => ‖fderiv ℝ (η L) y‖) (volume.restrict U) :=
      h_norm_cont.integrable_of_hasCompactSupport h_norm_compact
    have h_eval : Continuous (fun (g : E n →L[ℝ] ℝ) => g ν) := continuous_eval_const ν
    have h_cont : Continuous (fun y : E n => fderiv ℝ (η L) y ν) :=
      h_eval.comp h_fderiv_cont
    have h_support2 : Function.support (fun y : E n => fderiv ℝ (η L) y ν) ⊆ closedBall x (r + L) := by
      intro y hy
      have h8 : (fderiv ℝ (η L) y) ν ≠ 0 := by simpa [Function.mem_support] using hy
      have h9 : fderiv ℝ (η L) y ≠ 0 := by intro h10; rw [h10] at h8; simp at h8
      exact h_fderiv_support h9
    have h_compact2 : HasCompactSupport (fun y : E n => fderiv ℝ (η L) y ν) :=
      h_cb.of_isClosed_subset (isClosed_tsupport _) (closure_minimal h_support2 isClosed_closedBall)
    have h_int : Integrable (fun y : E n => fderiv ℝ (η L) y ν) (volume.restrict U) :=
      h_cont.integrable_of_hasCompactSupport h_compact2
    have h_bound : |∫ y in U, fderiv ℝ (η L) y ν| ≤ ∫ y in U, ‖fderiv ℝ (η L) y‖ := by
      have h_abs : |∫ y in U, fderiv ℝ (η L) y ν| ≤ ∫ y in U, |fderiv ℝ (η L) y ν| :=
        abs_integral_le_integral_abs
      have h_mono : ∫ y in U, |fderiv ℝ (η L) y ν| ≤ ∫ y in U, ‖fderiv ℝ (η L) y‖ :=
        integral_mono_ae h_int.abs h_norm_int (by filter_upwards with z; exact h1_point z)
      calc
        |∫ y in U, fderiv ℝ (η L) y ν|
          ≤ ∫ y in U, |fderiv ℝ (η L) y ν| := h_abs
        _ ≤ ∫ y in U, ‖fderiv ℝ (η L) y‖ := h_mono

    -- Coarea bound
    let g : ℝ → ℝ := fun t => w ((t - r) / L) / L
    have hg_nonneg : ∀ t, 0 ≤ g t := by intro t; positivity
    have hg_cont : Continuous g := by
      have hL_ne : L ≠ 0 := hL.ne'
      have h_inner : Continuous (fun t : ℝ => (t - r) / L) := by fun_prop
      exact hw_cont.comp h_inner |>.div continuous_const (by simp [hL_ne])
    have h_support_g : ∀ t ∉ Set.Icc r (r + L), g t = 0 := by
      intro t ht
      have h5 : (t - r) / L ∉ Set.Icc (0 : ℝ) 1 := by
        simp only [Set.mem_Icc, not_and_or] at ht
        rcases ht with (h | h)
        · have h52 : (t - r) / L < 0 := div_neg_of_neg_of_pos (by linarith) hL
          intro h53; have h54 : 0 ≤ (t - r) / L := h53.1; linarith
        · have h52 : 1 < (t - r) / L := by rw [one_lt_div hL] <;> linarith
          intro h53; have h54 : (t - r) / L ≤ 1 := h53.2; linarith
      have h6 : w ((t - r) / L) = 0 := hw_support ((t - r) / L) h5
      simp [g, h6]
    have h_grad_ae : ∀ᵐ (y : E n) ∂volume.restrict U,
        ‖fderiv ℝ (η L) y‖ ≤ g (dist y x) := by
      filter_upwards with y
      by_cases hy : y = x
      · rw [hy]
        have h_center : fderiv ℝ (η L) x = 0 := radialCutoff_fderiv_at_center hr_pos hL
        rw [h_center]
        have h_goal : ‖(0 : E n →L[ℝ] ℝ)‖ ≤ g (dist x x) := by
          simpa using hg_nonneg (dist x x)
        exact h_goal
      · have h : ‖fderiv ℝ (η L) y‖ ≤ w ((dist y x - r) / L) / L :=
          radialCutoff_fderiv_tight_bound hr_pos hL hy
        simpa [g] using h
    have h_g_cont : Continuous (fun y : E n => g (dist y x)) := by fun_prop
    have h_g_support : Function.support (fun y : E n => g (dist y x)) ⊆ closedBall x (r + L) := by
      intro y hy
      by_cases h : y ∈ closedBall x (r + L)
      · exact h
      · have h_dist : r + L < dist y x := by simpa [closedBall, not_le] using h
        have h_not : dist y x ∉ Set.Icc r (r + L) := by
          simp only [Set.mem_Icc, not_and_or]; right; linarith
        have h10 : g (dist y x) = 0 := h_support_g (dist y x) h_not
        simpa [Function.mem_support] using hy h10
    have h_g_compact : HasCompactSupport (fun y : E n => g (dist y x)) :=
      h_cb.of_isClosed_subset (isClosed_tsupport _) (closure_minimal h_g_support isClosed_closedBall)
    have h_g_int : Integrable (fun y : E n => g (dist y x)) (volume.restrict U) :=
      h_g_cont.integrable_of_hasCompactSupport h_g_compact
    have h_integral_mono : ∫ y in U, ‖fderiv ℝ (η L) y‖ ≤ ∫ y in U, g (dist y x) :=
      integral_mono_ae h_norm_int h_g_int h_grad_ae

    have h_coarea_eq : ∫ y in U, g (dist y x) =
        ∫ t in Set.Ioi 0, g t * f_sphere t :=
      weighted_distance_coarea_unbounded hU x g hg_nonneg hg_cont
        (hg_support := h_support_g) hn

    have h_prod_ae : AEStronglyMeasurable (fun t : ℝ => g t * f_sphere t) volume :=
      hg_cont.aestronglyMeasurable.mul h_f_ae
    have h_bdd : ∃ M, 0 ≤ M ∧ ∀ t ∈ Set.Icc r (r + L), |g t| ≤ M := by
      have h_cont_on : ContinuousOn g (Set.Icc r (r + L)) := hg_cont.continuousOn
      have h : BddAbove (Set.image g (Set.Icc r (r + L))) :=
        isCompact_Icc.bddAbove_image h_cont_on
      rcases h with ⟨M, hM⟩
      refine ⟨max M 0, by positivity, fun t ht => ?_⟩
      have h1 : g t ∈ Set.image g (Set.Icc r (r + L)) := ⟨t, ht, rfl⟩
      have h2 : g t ≤ M := hM h1
      have h3 : 0 ≤ g t := hg_nonneg t
      rw [abs_of_nonneg h3]; exact le_trans h2 (le_max_left M 0)
    rcases h_bdd with ⟨M, hM_nonneg, hM_Icc⟩
    have hM_bdd : ∀ t, |g t| ≤ M := by
      intro t
      by_cases ht : t ∈ Set.Icc r (r + L)
      · exact hM_Icc t ht
      · have h3 : g t = 0 := h_support_g t ht
        rw [h3, abs_zero] <;> exact hM_nonneg
    have h4 : ∀ᵐ (t : ℝ), ‖(g t * f_sphere t)‖ ≤ ‖(M * |f_sphere t|)‖ := by
      filter_upwards with t
      have h5 : |g t * f_sphere t| ≤ M * |f_sphere t| := by
        calc
          |g t * f_sphere t| = |g t| * |f_sphere t| := by rw [abs_mul]
          _ ≤ M * |f_sphere t| := by gcongr <;> exact hM_bdd t
      have hM_abs : |M| = M := abs_of_nonneg hM_nonneg
      simpa [Real.norm_eq_abs, hM_abs] using h5
    have h_Icc_meas : MeasurableSet (Set.Icc r (r + L)) := measurableSet_Icc
    have h_Icc_int : IntegrableOn f_sphere (Set.Icc r (r + L)) volume :=
      h_f_sphere_locint.integrableOn_isCompact isCompact_Icc
    have h_abs_Icc_int : IntegrableOn (fun t : ℝ => M * |f_sphere t|) (Set.Icc r (r + L)) volume :=
      h_Icc_int.abs.const_mul M
    have h4_on : ∀ᵐ (t : ℝ) ∂volume.restrict (Set.Icc r (r + L)),
        ‖(g t * f_sphere t)‖ ≤ ‖(M * |f_sphere t|)‖ :=
      ae_restrict_of_ae h4
    have h_prod_ae_restrict : AEStronglyMeasurable (fun t : ℝ => g t * f_sphere t) (volume.restrict (Set.Icc r (r + L))) :=
      h_prod_ae.restrict
    have h_prod_on : IntegrableOn (fun t : ℝ => g t * f_sphere t) (Set.Icc r (r + L)) volume :=
      Integrable.mono h_abs_Icc_int h_prod_ae_restrict h4_on
    have h_support_prod : Function.support (fun t : ℝ => g t * f_sphere t) ⊆ Set.Icc r (r + L) := by
      intro t ht
      by_cases h : t ∈ Set.Icc r (r + L)
      · exact h
      · have h6 : g t = 0 := h_support_g t h
        have h7 : g t * f_sphere t = 0 := by rw [h6] <;> ring
        exact False.elim (ht (by simpa [Function.mem_support] using h7))
    have h_Icc_compl_meas : MeasurableSet (Set.Icc r (r + L))ᶜ := measurableSet_Icc.compl
    have h6 : (fun t : ℝ => g t * f_sphere t) =ᵐ[volume.restrict (Set.Icc r (r + L))ᶜ] (0 : ℝ → ℝ) := by
      filter_upwards [self_mem_ae_restrict h_Icc_compl_meas] with t ht
      have h8 : t ∉ Set.Icc r (r + L) := ht
      have h9 : g t = 0 := h_support_g t h8
      have h10 : g t * f_sphere t = 0 := by rw [h9] <;> ring
      exact h10
    have h_outside : IntegrableOn (fun t : ℝ => g t * f_sphere t) (Set.Icc r (r + L))ᶜ volume := by
      have h7 : Integrable (0 : ℝ → ℝ) (volume.restrict (Set.Icc r (r + L))ᶜ) := by exact integrable_zero ℝ ℝ (volume.restrict (Icc r (r + L))ᶜ)
      exact (integrableOn_congr_fun_ae (id (EventuallyEq.symm h6))).mp h7
    have h_union : IntegrableOn (fun t : ℝ => g t * f_sphere t) ((Set.Icc r (r + L)) ∪ (Set.Icc r (r + L))ᶜ) volume :=
      h_prod_on.union h_outside
    have h_univ : (Set.Icc r (r + L)) ∪ (Set.Icc r (r + L))ᶜ = Set.univ := by simp
    have h_prod_int : Integrable (fun t : ℝ => g t * f_sphere t) volume := by
      rw [h_univ] at h_union
      simpa [IntegrableOn] using h_union

    have h_deriv0 : deriv smoothStep 0 = 0 := by
      have h_cont : Continuous (deriv smoothStep) := smoothStep_contDiff.continuous_deriv (by norm_num)
      have h_neg : ∀ t < 0, deriv smoothStep t = 0 := by
        intro t ht
        exact smoothStep_deriv_zero_outside (by simp [ht])
      have h_lim1 : Tendsto (deriv smoothStep) (nhdsWithin 0 (Set.Iio 0)) (nhds (deriv smoothStep 0)) :=
        h_cont.continuousAt.tendsto.mono_left inf_le_left
      have h_lim2 : Tendsto (deriv smoothStep) (nhdsWithin 0 (Set.Iio 0)) (nhds 0) := by
        have h_eventually : (deriv smoothStep) =ᶠ[nhdsWithin 0 (Set.Iio 0)] (fun _ => 0) := by
          filter_upwards [self_mem_nhdsWithin] with t ht
          exact h_neg t ht
        exact tendsto_const_nhds.congr' h_eventually.symm
      exact tendsto_nhds_unique h_lim1 h_lim2
    have h_w0 : w 0 = 0 := by
      simp [w, h_deriv0]
    have h1 : ∀ t ∉ Set.Ioc r (r + L), g t * f_sphere t = 0 := by
      intro t ht
      by_cases h_eq : t = r
      · rw [h_eq]
        have h_gr : g r = 0 := by
          dsimp only [g]
          have h_eq : (r - r) / L = 0 := by ring
          rw [h_eq]
          have h : w 0 = 0 := h_w0
          rw [h] <;> ring
        rw [h_gr] <;> ring
      · have h2 : t ∉ Set.Icc r (r + L) := by
          intro h3
          have h4 : r < t := lt_of_le_of_ne h3.1 (Ne.symm h_eq)
          exact ht ⟨h4, h3.2⟩
        have h4 : g t = 0 := h_support_g t h2
        rw [h4] <;> ring
    have h3 : Set.Ioc r (r + L) ⊆ Set.Ioi 0 := by
      intro t ht
      have h4 : r < t := ht.1
      exact lt_trans hr_pos h4
    have h_integral_Ioc : ∫ t in Set.Ioi 0, g t * f_sphere t =
        ∫ t in Set.Ioc r (r + L), g t * f_sphere t := by
      have h5 : ∀ᵐ (t : ℝ) ∂volume.restrict (Set.Ioi 0),
          (g t * f_sphere t) = (Set.Ioc r (r + L)).indicator (fun t => g t * f_sphere t) t := by
        filter_upwards with t
        by_cases h6 : t ∈ Set.Ioc r (r + L)
        · simp [h6]
        · have h7 : g t * f_sphere t = 0 := h1 t h6
          simp [h6, h7]
      have h6 : ∫ t in Set.Ioi 0, g t * f_sphere t =
          ∫ t in Set.Ioi 0, (Set.Ioc r (r + L)).indicator (fun t => g t * f_sphere t) t := by
        rw [integral_congr_ae h5]
      rw [h6, integral_indicator measurableSet_Ioc]
      have h7 : (volume.restrict (Set.Ioi 0)).restrict (Set.Ioc r (r + L)) = volume.restrict (Set.Ioc r (r + L)) := by
        rw [Measure.restrict_restrict measurableSet_Ioc]
        have h_inter : (Set.Ioc r (r + L)) ∩ (Set.Ioi 0) = Set.Ioc r (r + L) := by
          rw [Set.inter_comm]
          exact Set.inter_eq_right.mpr h3
        rw [h_inter]
      simpa [h7] using rfl
    have h_interval : ∫ t in Set.Ioc r (r + L), g t * f_sphere t =
        ∫ t in r..(r + L), g t * f_sphere t := by
      rw [intervalIntegral.integral_of_le (by linarith)]
    let H : ℝ → ℝ := fun t => g t * f_sphere t
    have hH_on1 : IntegrableOn H (Set.Ioc r (r + L)) volume :=
      h_prod_int.mono_measure Measure.restrict_le_self
    have hH_on2 : IntegrableOn H (Set.Ioc (r + L) r) volume := by
      have h_empty : Set.Ioc (r + L) r = ∅ := by
        ext z; simp only [Set.mem_Ioc, Set.mem_empty_iff_false, iff_false]; intro h; linarith
      rw [h_empty]; simp
    let hH_ii : IntervalIntegrable H volume r (r + L) := ⟨hH_on1, hH_on2⟩
    have h_change : ∫ t in r..(r + L), H t = ∫ t in (0 : ℝ)..1, w t * f_sphere (r + L * t) := by
      have hL_ne : L ≠ 0 := hL.ne'
      have h_at : ∀ u : ℝ, H (L * u + r) = (w u * f_sphere (r + L * u)) / L := by
        intro u
        have h_div : ((L * u + r) - r) / L = u := by field_simp [hL_ne] <;> ring
        have h_comm : r + L * u = L * u + r := by ring
        dsimp only [H, g]
        calc
          (w (((L * u + r) - r) / L) / L) * f_sphere (L * u + r)
            = (w u / L) * f_sphere (r + L * u) := by rw [h_div, h_comm] <;> ring
        _ = (w u * f_sphere (r + L * u)) / L := by ring
      have h15 := intervalIntegral.integral_comp_mul_add (a := 0) (b := 1) (c := L) (d := r) H (by linarith)
      have h_end1 : L * (0 : ℝ) + r = r := by ring
      have h_end2 : L * (1 : ℝ) + r = r + L := by ring
      have h15' : ∫ u in (0 : ℝ)..1, H (L * u + r) = L⁻¹ • ∫ t in r..(r + L), H t := by
        rw [h15, h_end1, h_end2]
      have h16 : ∫ u in (0 : ℝ)..1, H (L * u + r) = ∫ u in (0 : ℝ)..1, (w u * f_sphere (r + L * u)) / L := by
        apply intervalIntegral.integral_congr; intro u _; exact h_at u
      have h17 : L⁻¹ • ∫ t in r..(r + L), H t = ∫ u in (0 : ℝ)..1, (w u * f_sphere (r + L * u)) / L := by
        rw [←h16, h15']
      have h18 : ∫ t in r..(r + L), H t = ∫ u in (0 : ℝ)..1, w u * f_sphere (r + L * u) := by
        have h19 : L * (L⁻¹ • ∫ t in r..(r + L), H t) = L * (∫ u in (0 : ℝ)..1, (w u * f_sphere (r + L * u)) / L) :=
          congr_arg (fun x : ℝ => L * x) h17
        have h_left : L * (L⁻¹ • ∫ t in r..(r + L), H t) = ∫ t in r..(r + L), H t := by
          simp [smul_eq_mul, hL_ne] <;> field_simp [hL_ne] <;> ring
        have h_right : L * (∫ u in (0 : ℝ)..1, (w u * f_sphere (r + L * u)) / L) =
            ∫ u in (0 : ℝ)..1, w u * f_sphere (r + L * u) := by
          simp [smul_eq_mul, hL_ne] <;> field_simp [hL_ne] <;> ring
        calc
          ∫ t in r..(r + L), H t
            = L * (L⁻¹ • ∫ t in r..(r + L), H t) := h_left.symm
          _ = L * (∫ u in (0 : ℝ)..1, (w u * f_sphere (r + L * u)) / L) := h19
          _ = ∫ u in (0 : ℝ)..1, w u * f_sphere (r + L * u) := h_right
      exact h18

    have h_coarea_bound : ∫ y in U, ‖fderiv ℝ (η L) y‖ ≤
        ∫ t in (0 : ℝ)..1, w t * f_sphere (r + L * t) := by
      calc
        ∫ y in U, ‖fderiv ℝ (η L) y‖
          ≤ ∫ y in U, g (dist y x) := h_integral_mono
        _ = ∫ t in Set.Ioi 0, g t * f_sphere t := h_coarea_eq
        _ = ∫ t in Set.Ioc r (r + L), g t * f_sphere t := h_integral_Ioc
        _ = ∫ t in r..(r + L), g t * f_sphere t := h_interval
        _ = ∫ t in (0 : ℝ)..1, w t * f_sphere (r + L * t) := h_change

    rw [h_main_eq]
    exact le_trans h_bound h_coarea_bound

  -- Step 2: LHS limit as L → 0 via DCT
  classical
  let f_limit : E n → E n := fun y => if y ∈ closedBall x r then ν else 0
  let g_L : ℝ → E n → ℝ := fun L y => inner ℝ (ψ L y) (f_normal y)
  let g_limit : E n → ℝ := fun y => inner ℝ (f_limit y) (f_normal y)

  have h_pointwise : ∀ y ∉ sphere x r,
      Tendsto (fun L : ℝ => ψ L y) (nhdsWithin 0 (Set.Ioi 0)) (nhds (f_limit y)) := by
    intro y hy
    have h_dist : dist y x ≠ r := by simpa [Metric.mem_sphere, dist_eq_norm] using hy
    by_cases h_in : y ∈ closedBall x r
    · have h_lt : dist y x < r := by
        have h_le : dist y x ≤ r := by simpa [closedBall] using h_in
        exact lt_of_le_of_ne h_le h_dist
      have h_nhds : Set.Ioi (0 : ℝ) ∈ nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) := self_mem_nhdsWithin
      have h_eventually : (fun L : ℝ => ψ L y) =ᶠ[nhdsWithin 0 (Set.Ioi 0)] (fun (_ : ℝ) => ν) := by
        filter_upwards [h_nhds] with L hL
        have h : η L y = 1 := radialCutoff_one_of_mem_closedBall hr_pos hL h_in
        simp [ψ, h]
      have h_f : f_limit y = ν := by dsimp only [f_limit]; rw [if_pos h_in]
      rw [h_f]
      exact tendsto_const_nhds.congr' h_eventually.symm
    · have h_gt : r < dist y x := by
        by_contra h; have h_le : dist y x ≤ r := by linarith
        exact h_in (by simpa [closedBall] using h_le)
      have h_pos2 : 0 < dist y x - r := by linarith
      have h_small : Set.Ioo (0 : ℝ) (dist y x - r) ∈ nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) := by
        apply mem_nhdsWithin.mpr
        refine ⟨Set.Iio (dist y x - r), isOpen_Iio, h_pos2, ?_⟩
        intro z hz; exact ⟨hz.2, hz.1⟩
      have h_eventually : (fun L : ℝ => ψ L y) =ᶠ[nhdsWithin 0 (Set.Ioi 0)] (fun (_ : ℝ) => 0) := by
        filter_upwards [h_small] with L hL
        have hL_pos : 0 < L := hL.1
        have hL_lt : L < dist y x - r := hL.2
        have h3 : y ∉ ball x (r + L) := by simpa [ball, not_lt] using by linarith
        have h4 : η L y = 0 := radialCutoff_zero_of_not_mem_ball (hr := hr_pos) (hL := hL_pos) (h := h3)
        simp [ψ, h4]
      have h_f : f_limit y = 0 := by dsimp only [f_limit]; rw [if_neg h_in]
      rw [h_f]
      exact tendsto_const_nhds.congr' h_eventually.symm

  have h_sphere_ae : ∀ᵐ (y : E n) ∂μ, y ∉ sphere x r := by
    rw [ae_iff]
    have h_set : {y : E n | ¬(y ∉ sphere x r)} = sphere x r := by ext z; simp
    rw [h_set]; exact hr_sphere

  have h_ae : ∀ᵐ (y : E n) ∂μ,
      Tendsto (fun L : ℝ => ψ L y) (nhdsWithin 0 (Set.Ioi 0)) (nhds (f_limit y)) := by
    filter_upwards [h_sphere_ae] with y hy
    exact h_pointwise y hy

  have h_g_ae : ∀ᵐ (y : E n) ∂μ,
      Tendsto (fun L : ℝ => g_L L y) (nhdsWithin 0 (Set.Ioi 0)) (nhds (g_limit y)) := by
    filter_upwards [h_ae] with y hy
    have h_cont : Continuous (fun z : E n => inner ℝ z (f_normal y)) := by fun_prop
    exact h_cont.continuousAt.tendsto.comp hy

  have h_g_bound : ∃ (C : ℝ), ∀ᶠ (L : ℝ) in nhdsWithin 0 (Set.Ioi 0),
      ∀ᵐ (y : E n) ∂μ, ‖g_L L y‖ ≤ C := by
    refine ⟨1, ?_⟩
    have h_nhds : Set.Ioi (0 : ℝ) ∈ nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) := self_mem_nhdsWithin
    filter_upwards [h_nhds] with L hL
    have h_main : ∀ᵐ (y : E n) ∂μ, ‖g_L L y‖ ≤ 1 := by
      filter_upwards [hf_norm_le_one] with y hy
      have h1 : ‖g_L L y‖ = |inner ℝ (ψ L y) (f_normal y)| := by
        simp [g_L, Real.norm_eq_abs]
      rw [h1]
      have h2 : |inner ℝ (ψ L y) (f_normal y)| ≤ ‖ψ L y‖ * ‖f_normal y‖ := abs_real_inner_le_norm _ _
      have h3 : ‖ψ L y‖ ≤ 1 := by
        have h4 : 0 ≤ η L y := smoothStep_range.1
        have h5 : η L y ≤ 1 := smoothStep_range.2
        calc
          ‖ψ L y‖ = ‖η L y‖ * ‖ν‖ := norm_smul (η L y) ν
          _ = |η L y| * ‖ν‖ := by rw [Real.norm_eq_abs]
          _ = |η L y| := by rw [hν_unit] <;> ring
          _ ≤ 1 := by rw [abs_of_nonneg h4] <;> exact h5
      have h6 : ‖f_normal y‖ ≤ 1 := hy
      calc
        |inner ℝ (ψ L y) (f_normal y)| ≤ ‖ψ L y‖ * ‖f_normal y‖ := h2
        _ ≤ 1 * 1 := by gcongr
        _ = 1 := by ring
    exact h_main

  have h_nhds2 : Set.Ioi (0 : ℝ) ∈ nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) := self_mem_nhdsWithin
  have h_g_meas : ∀ᶠ (L : ℝ) in nhdsWithin 0 (Set.Ioi 0),
      AEStronglyMeasurable (g_L L) μ := by
    filter_upwards [h_nhds2] with L hL
    have h_cont : Continuous (ψ L) := by
      have hη_smooth := radialCutoff_contDiff (x₀ := x) hr_pos hL
      exact hη_smooth.continuous.smul continuous_const
    exact h_cont.aestronglyMeasurable.inner hf_int.1

  have hψ_int : ∀ (L : ℝ), 0 < L → Integrable (ψ L) μ := by
    intro L hL
    have h_cont : Continuous (ψ L) := by
      have hη_smooth := radialCutoff_contDiff (x₀ := x) hr_pos hL
      exact hη_smooth.continuous.smul continuous_const
    have h_support : Function.support (ψ L) ⊆ closedBall x (r + L) := by
      intro y hy
      by_cases h : y ∈ ball x (r + L)
      · exact ball_subset_closedBall h
      · have h2 : η L y = 0 := radialCutoff_zero_of_not_mem_ball hr_pos hL (h := h)
        have h3 : ψ L y = 0 := by simp [ψ, h2]
        simpa [Function.mem_support] using hy h3
    have h_cb : IsCompact (closedBall x (r + L)) := isCompact_closedBall x (r + L)
    have h_compact : HasCompactSupport (ψ L) :=
      h_cb.of_isClosed_subset (isClosed_tsupport _) (closure_minimal h_support isClosed_closedBall)
    exact h_cont.integrable_of_hasCompactSupport h_compact

  have h_flimit_int : Integrable f_limit μ := by
    have h1 : MeasurableSet (closedBall x r) := isClosed_closedBall.measurableSet
    have h_eq : f_limit = (closedBall x r).indicator (fun (_ : E n) => ν) := by
      funext y
      dsimp only [f_limit]
      by_cases h : y ∈ closedBall x r
      · rw [if_pos h, Set.indicator_apply, if_pos h]
      · rw [if_neg h, Set.indicator_apply, if_neg h]
    rw [h_eq]
    exact (integrable_const ν).indicator h1

  have h_dct : Tendsto (fun L : ℝ => ∫ y, g_L L y ∂μ)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (∫ y, g_limit y ∂μ)) :=
    tendsto_integral_filter_of_norm_le_const h_g_meas h_g_bound h_g_ae

  have h_conv1 : ∀ (L : ℝ), 0 < L →
      ∫ᵛ y, ψ L y ∂[innerBilinear; D] = ∫ y, g_L L y ∂μ := by
    intro L hL
    rw [hD_eq]
    exact integral_withDensityᵥ_inner hf_int hf_norm_le_one (hψ_int L hL)

  have h_conv2 : ∫ᵛ y, f_limit y ∂[innerBilinear; D] = ∫ y, g_limit y ∂μ := by
    rw [hD_eq]
    exact integral_withDensityᵥ_inner hf_int hf_norm_le_one h_flimit_int

  have h_eventually_eq : ∀ᶠ (L : ℝ) in nhdsWithin 0 (Set.Ioi 0),
      (∫ y, g_L L y ∂μ) = (∫ᵛ y, ψ L y ∂[innerBilinear; D]) :=
    Filter.mem_of_superset (self_mem_nhdsWithin) fun L hL => (h_conv1 L hL).symm

  have h_lhs_limit : Tendsto (fun L : ℝ => ∫ᵛ y, ψ L y ∂[innerBilinear; D])
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (∫ᵛ y, f_limit y ∂[innerBilinear; D])) := by
    have h5 : Tendsto (fun L : ℝ => ∫ y, g_L L y ∂μ)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (∫ᵛ y, f_limit y ∂[innerBilinear; D])) := by
      rw [←h_conv2] at h_dct
      exact h_dct
    exact h5.congr' h_eventually_eq

  have h_limit_eq : ∫ᵛ y, f_limit y ∂[innerBilinear; D] = inner ℝ (D (closedBall x r)) ν := by
    have h_cb : MeasurableSet (closedBall x r) := isClosed_closedBall.measurableSet
    have h_g_limit_eq : g_limit = (closedBall x r).indicator (fun y => inner ℝ ν (f_normal y)) := by
      funext y
      dsimp only [g_limit, f_limit]
      by_cases h : y ∈ closedBall x r
      · rw [if_pos h, Set.indicator_apply, if_pos h]
      · rw [if_neg h, Set.indicator_apply, if_neg h] <;> simp [inner_zero_left]
    have h_int_g : ∫ y, g_limit y ∂μ = ∫ y in closedBall x r, inner ℝ ν (f_normal y) ∂μ := by
      rw [h_g_limit_eq, MeasureTheory.integral_indicator h_cb]
    have hD_ball : D (closedBall x r) = ∫ y in closedBall x r, f_normal y ∂μ := by
      rw [hD_eq]
      exact withDensityᵥ_apply hf_int h_cb
    have h1 : ∫ y in closedBall x r, inner ℝ ν (f_normal y) ∂μ = inner ℝ ν (D (closedBall x r)) := by
      rw [hD_ball]
      exact integral_inner hf_int.integrableOn ν
    have h2 : inner ℝ ν (D (closedBall x r)) = inner ℝ (D (closedBall x r)) ν := by
      have h3 := inner_conj_symm (𝕜 := ℝ) (E := E n) ν (D (closedBall x r))
      exact h3.symm
    rw [h_conv2, h_int_g, h1, h2]

  rw [h_limit_eq] at h_lhs_limit

  -- Step 3: RHS limit via approximate identity
  have h_rhs_limit : Tendsto (fun L : ℝ => ∫ t in (0 : ℝ)..1, w t * f_sphere (r + L * t))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (f_sphere r)) :=
    approximate_identity_one_sided h_f_sphere_locint hw_cont hw_nonneg hw_support hw_int r hr_leb

  -- Step 4: Combine
  have h_main_bound : ∀ (L : ℝ), 0 < L →
      |∫ᵛ y, ψ L y ∂[innerBilinear; D]| ≤
      ∫ t in (0 : ℝ)..1, w t * f_sphere (r + L * t) := by
    intro L hL
    exact h_step1 L hL

  have h_eventually : ∀ᶠ (L : ℝ) in nhdsWithin 0 (Set.Ioi 0),
      |∫ᵛ y, ψ L y ∂[innerBilinear; D]| ≤
      ∫ t in (0 : ℝ)..1, w t * f_sphere (r + L * t) := by
    filter_upwards [self_mem_nhdsWithin] with L hL
    exact h_main_bound L hL

  exact le_of_tendsto_of_tendsto h_lhs_limit.abs h_rhs_limit h_eventually


-- ============================================================================
-- Volume radial derivative (coarea consequence)
-- ============================================================================

/-- **Volume function is absolutely continuous** with derivative equal to
the Hausdorff measure of the intersection with the sphere, a.e.

This follows from the distance coarea formula:
`volume(U ∩ ball x r) = ∫_0^r H^{n-1}(U ∩ sphere x t) dt`. -/
lemma volume_radial_derivative
    {U : Set (E n)} (hU : MeasurableSet U) (hBdd : Bornology.IsBounded U)
    (hn : 2 ≤ n) (x : E n) (R : ℝ) (hR_pos : 0 < R) :
    let m : ℝ → ℝ := fun r => (volume (U ∩ ball x r)).toReal
    AbsolutelyContinuousOnInterval m 0 R ∧
    MonotoneOn m (Set.Icc 0 R) ∧
    (m 0 = 0) ∧
    (∀ᵐ (r : ℝ), r ∈ Set.Ioo 0 R →
      deriv m r = (μHE[n - 1] (U ∩ sphere x r)).toReal) := by
  letI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  let d : E n → ℝ := fun y => dist y x
  let A' := U \ {x}
  let F_sphere : ℝ → ENNReal := fun t => μHE[n - 1] (U ∩ sphere x t)
  let f_sphere : ℝ → ℝ := fun t => (F_sphere t).toReal

  have hA'_meas : MeasurableSet A' := hU.diff (measurableSet_singleton x)
  have hA'_sub1 : A' ⊆ U := fun y hy => hy.1
  rcases hBdd with ⟨t, ht_in, ht_sub⟩
  have hA'_bdd : Bornology.IsBounded A' := by
    have h1 : WithLp.ofLp ⁻¹' t ⊆ (A')ᶜ :=
      subset_trans ht_sub (compl_subset_compl.mpr hA'_sub1)
    exact ⟨t, ht_in, h1⟩
  have hBdd' : Bornology.IsBounded U := ⟨t, ht_in, ht_sub⟩

  have hC_closed : IsClosed ({x} : Set (E n)) := isClosed_singleton
  have hC_nonempty : ({x} : Set (E n)).Nonempty := ⟨x, rfl⟩
  have h_eq_dist : (fun y : E n => infDist y ({x} : Set (E n))) = d := by
    funext y; simp [Metric.infDist_singleton, d]
  have h_d_level_meas : FunctionLevelMeasurable (fun y : E n => infDist y ({x} : Set (E n))) := by
    rw [h_eq_dist]; exact point_distance_level_measurable hn x
  have hA'_sub : A' ⊆ {y | 0 < infDist y ({x} : Set (E n))} := by
    intro y hy
    have h5 : 0 < d y := dist_pos.mpr hy.2
    have h6 : infDist y ({x} : Set (E n)) = d y := by
      rw [Metric.infDist_singleton] <;> rfl
    have h7 : 0 < infDist y ({x} : Set (E n)) := by rw [h6]; exact h5
    exact h7

  have h_singleton_null : volume ({x} : Set (E n)) = 0 := by exact measure_singleton x
  have h_sphere_null : ∀ r : ℝ, volume (sphere x r) = 0 := by
    intro r; exact Measure.addHaar_sphere volume x r

  have h_coarea : ∀ r : ℝ, 0 < r →
      volume (U ∩ ball x r) = ∫⁻ t in Set.Ioc (0 : ℝ) r, F_sphere t := by
    intro r hr_pos
    have h1 : volume {y ∈ A' | 0 < infDist y ({x} : Set (E n)) ∧ infDist y ({x} : Set (E n)) ≤ r} =
        ∫⁻ t in Set.Ioc (0 : ℝ) r, μHE[n - 1] {y ∈ A' | infDist y ({x} : Set (E n)) = t} :=
      distance_coarea_eq hn hC_closed hC_nonempty h_d_level_meas hA'_meas hA'_bdd hA'_sub (by linarith)
    have h2 : {y ∈ A' | 0 < infDist y ({x} : Set (E n)) ∧ infDist y ({x} : Set (E n)) ≤ r} = Set.inter A' (closedBall x r) := by
      ext y
      simp only [A', Set.mem_sep_iff, Set.mem_inter_iff, Set.mem_diff, Set.mem_singleton_iff]
      have h_eq : infDist y ({x} : Set (E n)) = dist y x := by
        rw [Metric.infDist_singleton] <;> rfl
      constructor
      · rintro ⟨hyA', h_pos, h_le⟩
        exact ⟨hyA', by simpa [h_eq, Metric.mem_closedBall] using h_le⟩
      · rintro ⟨hyA', h_in⟩
        have h_yne_x : y ≠ x := hyA'.2
        have h_pos : 0 < infDist y ({x} : Set (E n)) := by
          rw [h_eq]; exact dist_pos.mpr h_yne_x
        have h_le : infDist y ({x} : Set (E n)) ≤ r := by
          rw [h_eq]; simpa [Metric.mem_closedBall] using h_in
        exact ⟨hyA', h_pos, h_le⟩
    have h3 : ∀ t : ℝ, 0 < t → μHE[n - 1] {y ∈ A' | infDist y ({x} : Set (E n)) = t} = F_sphere t := by
      intro t ht
      have h4 : {y ∈ A' | infDist y ({x} : Set (E n)) = t} = U ∩ sphere x t := by
        ext y
        have h_eq1 : infDist y ({x} : Set (E n)) = dist y x := by
          rw [Metric.infDist_singleton] <;> rfl
        simp only [Set.mem_sep_iff, Set.mem_inter_iff, A', Set.mem_diff, Set.mem_singleton_iff]
        constructor
        · rintro ⟨hyA', h_eq⟩
          have h_dist : dist y x = t := by rw [←h_eq1, h_eq]
          exact ⟨hyA'.1, by simpa [sphere] using h_dist⟩
        · rintro ⟨hyA, h_sph⟩
          have h_dist : dist y x = t := by simpa [sphere] using h_sph
          have h_y_ne_x : y ≠ x := by
            intro h; rw [h] at h_dist; simp at h_dist <;> linarith
          exact ⟨⟨hyA, h_y_ne_x⟩, by rw [h_eq1]; exact h_dist⟩
      rw [h4]
    have h4 : ∫⁻ t in Set.Ioc (0 : ℝ) r, μHE[n - 1] {y ∈ A' | infDist y ({x} : Set (E n)) = t} =
        ∫⁻ t in Set.Ioc (0 : ℝ) r, F_sphere t := by
      have h5 : ∀ᵐ (t : ℝ) ∂volume, t ∈ Set.Ioc (0 : ℝ) r →
          μHE[n - 1] {y ∈ A' | infDist y ({x} : Set (E n)) = t} = F_sphere t := by
        filter_upwards with t; intro ht; exact h3 t ht.1
      have h5' : ∀ᵐ (t : ℝ) ∂volume.restrict (Set.Ioc (0 : ℝ) r),
          μHE[n - 1] {y ∈ A' | infDist y ({x} : Set (E n)) = t} = F_sphere t :=
        (ae_restrict_iff' measurableSet_Ioc).mpr h5
      rw [lintegral_congr_ae h5']
    let S1 := Set.inter A' (closedBall x r)
    let S2 := U ∩ ball x r
    have h_null1 : volume (S1 \ S2) = 0 := by
      have h_sub : S1 \ S2 ⊆ sphere x r := by
        intro y hy
        have h_inA' : y ∈ A' := hy.1.1
        have h_inCB : y ∈ closedBall x r := hy.1.2
        have h_notin : y ∉ S2 := hy.2
        have h_yinU : y ∈ U := h_inA'.1
        have h_notball : y ∉ ball x r := by intro h; exact h_notin ⟨h_yinU, h⟩
        have h_dist : dist y x ≤ r := by simpa [closedBall] using h_inCB
        have h_dist2 : ¬dist y x < r := by simpa [ball] using h_notball
        have h_eq : dist y x = r := by linarith
        simpa [sphere] using h_eq
      exact measure_mono_null h_sub (h_sphere_null r)
    have h_null2 : volume (S2 \ S1) = 0 := by
      have h_sub : S2 \ S1 ⊆ {x} := by
        intro y hy
        have h_inU : y ∈ U := hy.1.1
        have h_inball : y ∈ ball x r := hy.1.2
        have h_notin : y ∉ S1 := hy.2
        by_cases h : y = x
        · exact h
        · have h_inA' : y ∈ A' := ⟨h_inU, h⟩
          have h_inCB : y ∈ closedBall x r := ball_subset_closedBall h_inball
          exact False.elim (h_notin ⟨h_inA', h_inCB⟩)
      exact measure_mono_null h_sub h_singleton_null
    have h_vol1 : volume S1 ≤ volume S2 := by
      have h_sub : S1 ⊆ S2 ∪ (S1 \ S2) := by simp
      have h : volume S1 ≤ volume (S2 ∪ (S1 \ S2)) := measure_mono h_sub
      have h2 : volume (S2 ∪ (S1 \ S2)) ≤ volume S2 + volume (S1 \ S2) := measure_union_le _ _
      rw [h_null1] at h2; simpa using h.trans h2
    have h_vol2 : volume S2 ≤ volume S1 := by
      have h_sub : S2 ⊆ S1 ∪ (S2 \ S1) := by simp
      have h : volume S2 ≤ volume (S1 ∪ (S2 \ S1)) := measure_mono h_sub
      have h2 : volume (S1 ∪ (S2 \ S1)) ≤ volume S1 + volume (S2 \ S1) := measure_union_le _ _
      rw [h_null2] at h2; simpa using h.trans h2
    have h5 : volume S1 = volume S2 := le_antisymm h_vol1 h_vol2
    rw [h2] at h1
    rw [h5] at h1
    exact h1.trans h4

  -- F_sphere is a.e. measurable and finite via Eilenberg
  have h_F_ae : AEStronglyMeasurable F_sphere volume :=
    distance_coarea_aemeasurable hn x U hU
  let dist_x : E n → ℝ := fun y => dist y x
  have h_dist_lip : LipschitzWith (1 : NNReal) dist_x := by
    apply LipschitzWith.of_dist_le_mul
    intro a b
    have h : |dist a x - dist b x| ≤ dist a b := abs_dist_sub_le a b x
    have h' : dist (dist a x) (dist b x) ≤ dist a b := by
      rw [Real.dist_eq] <;> exact h
    simpa [NNReal.coe_one, one_mul] using h'
  rcases eilenberg_μHE hn (hf := h_dist_lip) (by norm_num) with ⟨C, hC_ne_top, _, h_eilenberg⟩
  have h_vol_lt_top : volume U < ⊤ := hBdd'.measure_lt_top
  have hC_lt_top : C < ⊤ := lt_top_iff_ne_top.mpr hC_ne_top
  have h_mul_lt_top : C * volume U < ⊤ := mul_lt_top hC_lt_top h_vol_lt_top
  have h_lint_fin : (∫⁻ (t : ℝ), F_sphere t) < ⊤ := by
    have h1 : (∫⁻ (t : ℝ), F_sphere t) ≤ C * volume U := h_eilenberg U
    exact h1.trans_lt h_mul_lt_top
  have h_ae_lt_top : ∀ᵐ (t : ℝ), F_sphere t < ⊤ :=
    ae_lt_top' h_F_ae.aemeasurable h_lint_fin.ne

  -- f_sphere is integrable
  have h_f_ae : AEStronglyMeasurable f_sphere volume := by
    rcases h_F_ae with ⟨g, hg, h_eq⟩
    let g' : ℝ → ℝ := fun t => (g t).toReal
    have hgm : Measurable g' := hg.measurable.ennreal_toReal
    have h_eq' : f_sphere =ᵐ[volume] g' := by
      filter_upwards [h_eq] with t ht
      have h10 : f_sphere t = (F_sphere t).toReal := by rfl
      have h11 : (F_sphere t).toReal = (g t).toReal := by rw [ht]
      rw [h10, h11]
    exact hgm.aestronglyMeasurable.congr h_eq'.symm
  have h_f_int : Integrable f_sphere volume := by
    have h_enorm : ∀ᵐ (t : ℝ), ‖f_sphere t‖ₑ = F_sphere t := by
      filter_upwards [h_ae_lt_top] with t ht
      have h_eq : f_sphere t = (F_sphere t).toReal := by rfl
      have h_nonneg : 0 ≤ (F_sphere t).toReal := ENNReal.toReal_nonneg
      have h9 : ENNReal.ofReal (F_sphere t).toReal = F_sphere t := ENNReal.ofReal_toReal ht.ne
      rw [h_eq, Real.enorm_eq_ofReal h_nonneg, h9]
    have h4 : (∫⁻ (t : ℝ), ‖f_sphere t‖ₑ) = (∫⁻ (t : ℝ), F_sphere t) := by
      rw [lintegral_congr_ae h_enorm]
    have h5 : (∫⁻ (t : ℝ), ‖f_sphere t‖ₑ) < ⊤ := by rw [h4]; exact h_lint_fin
    exact ⟨h_f_ae, h5⟩

  let m : ℝ → ℝ := fun r => (volume (U ∩ ball x r)).toReal

  have h_m_eq : ∀ r ∈ Set.Icc (0 : ℝ) R, m r = ∫ t in (0 : ℝ)..r, f_sphere t := by
    intro r hr
    by_cases h_r0 : r = 0
    · rw [h_r0]; simp [m]
    · have h_rpos : 0 < r := by
        have h : 0 ≤ r := hr.1
        exact lt_of_le_of_ne h (Ne.symm h_r0)
      have h6 : volume (U ∩ ball x r) = ∫⁻ t in Set.Ioc (0 : ℝ) r, F_sphere t := h_coarea r h_rpos
      have h7 : (∫⁻ (t : ℝ) in Set.Ioc (0 : ℝ) r, F_sphere t) < ⊤ := by
        have h_univ_eq : (∫⁻ (x : ℝ) in Set.univ, F_sphere x) = ∫⁻ (t : ℝ), F_sphere t := by simp
        have h_le : (∫⁻ (t : ℝ) in Set.Ioc (0 : ℝ) r, F_sphere t) ≤ (∫⁻ (x : ℝ) in Set.univ, F_sphere x) :=
          lintegral_mono_set (Set.subset_univ _)
        rw [h_univ_eq] at h_le
        exact h_le.trans_lt h_lint_fin
      have h_f_int_r : Integrable f_sphere (volume.restrict (Set.Ioc (0 : ℝ) r)) := h_f_int.restrict
      have h_nonneg : 0 ≤ᵐ[volume.restrict (Set.Ioc (0 : ℝ) r)] f_sphere := by
        filter_upwards with t; exact ENNReal.toReal_nonneg
      have h10 : ∀ᵐ (t : ℝ) ∂volume.restrict (Set.Ioc (0 : ℝ) r), ENNReal.ofReal (f_sphere t) = F_sphere t := by
        have h11 : ∀ᵐ (t : ℝ) ∂volume, F_sphere t < ⊤ := h_ae_lt_top
        have h12 : ∀ᵐ (t : ℝ) ∂volume.restrict (Set.Ioc (0 : ℝ) r), F_sphere t < ⊤ :=
          (ae_restrict_iff' measurableSet_Ioc).mpr (by filter_upwards [h11] with t ht _; exact ht)
        filter_upwards [h12] with t ht
        have h13 : 0 ≤ f_sphere t := ENNReal.toReal_nonneg
        exact ENNReal.ofReal_toReal ht.ne
      have h9 : ENNReal.ofReal (∫ t in Set.Ioc (0 : ℝ) r, f_sphere t) = ∫⁻ t in Set.Ioc (0 : ℝ) r, F_sphere t := by
        rw [ofReal_integral_eq_lintegral_ofReal h_f_int_r h_nonneg]
        rw [lintegral_congr_ae h10]
      have h11 : (∫⁻ t in Set.Ioc (0 : ℝ) r, F_sphere t) ≠ ⊤ := h7.ne
      have h12 : (∫⁻ t in Set.Ioc (0 : ℝ) r, F_sphere t).toReal = ∫ t in Set.Ioc (0 : ℝ) r, f_sphere t := by
        have h13 : ENNReal.ofReal (∫ t in Set.Ioc (0 : ℝ) r, f_sphere t) = ∫⁻ t in Set.Ioc (0 : ℝ) r, F_sphere t := h9
        have h14 : ENNReal.ofReal ((∫⁻ t in Set.Ioc (0 : ℝ) r, F_sphere t).toReal) = ∫⁻ t in Set.Ioc (0 : ℝ) r, F_sphere t :=
          ENNReal.ofReal_toReal h11
        have h_nonneg_int : 0 ≤ ∫ t in Set.Ioc (0 : ℝ) r, f_sphere t := integral_nonneg_of_ae h_nonneg
        have h_nonneg_tr : 0 ≤ (∫⁻ t in Set.Ioc (0 : ℝ) r, F_sphere t).toReal := ENNReal.toReal_nonneg
        have h_iff : ENNReal.ofReal (∫ t in Set.Ioc (0 : ℝ) r, f_sphere t) =
            ENNReal.ofReal ((∫⁻ t in Set.Ioc (0 : ℝ) r, F_sphere t).toReal) ↔
            (∫ t in Set.Ioc (0 : ℝ) r, f_sphere t) = (∫⁻ t in Set.Ioc (0 : ℝ) r, F_sphere t).toReal :=
          ENNReal.ofReal_eq_ofReal_iff h_nonneg_int h_nonneg_tr
        have h_eq5 : ENNReal.ofReal (∫ t in Set.Ioc (0 : ℝ) r, f_sphere t) =
            ENNReal.ofReal ((∫⁻ t in Set.Ioc (0 : ℝ) r, F_sphere t).toReal) := by
          rw [h13, h14]
        exact (h_iff.mp h_eq5).symm
      have h14 : ∫ t in Set.Ioc (0 : ℝ) r, f_sphere t = ∫ t in (0 : ℝ)..r, f_sphere t := by
        rw [intervalIntegral.integral_of_le (by linarith)] <;> rfl
      have h15 : m r = (volume (U ∩ ball x r)).toReal := by rfl
      rw [h15, h6, h12, h14]

  have h_mono : MonotoneOn m (Set.Icc 0 R) := by
    intro r1 hr1 r2 hr2 hle
    have h1 : U ∩ ball x r1 ⊆ U ∩ ball x r2 := by
      intro y hy; exact ⟨hy.1, ball_subset_ball hle hy.2⟩
    have h2 : volume (U ∩ ball x r1) ≤ volume (U ∩ ball x r2) := measure_mono h1
    have h3 : volume (U ∩ ball x r2) ≠ ⊤ := (measure_mono (show U ∩ ball x r2 ⊆ U from by simp)).trans_lt h_vol_lt_top |>.ne
    exact ENNReal.toReal_mono h3 h2

  have h_m0 : m 0 = 0 := by
    have h_ball0 : U ∩ ball x 0 = ∅ := by
      ext y; simp [ball]
    simp [m, h_ball0]

  have h_ii : IntervalIntegrable f_sphere volume 0 R := h_f_int.intervalIntegrable
  let F : ℝ → ℝ := fun r => ∫ t in (0 : ℝ)..r, f_sphere t
  have h_ac0 : AbsolutelyContinuousOnInterval F 0 R :=
    h_ii.absolutelyContinuousOnInterval_intervalIntegral (c := 0) (by simp)
  have h_uIcc_eq : Set.uIcc (0 : ℝ) R = Set.Icc (0 : ℝ) R := by
    rw [uIcc_of_le (show (0 : ℝ) ≤ R by linarith)]
  have h_ac : AbsolutelyContinuousOnInterval m 0 R := by
    rw [absolutelyContinuousOnInterval_iff m 0 R]
    intro ε hε
    have h_main := (absolutelyContinuousOnInterval_iff F 0 R).mp h_ac0 ε hε
    rcases h_main with ⟨δ, hδ_pos, hδ⟩
    refine ⟨δ, hδ_pos, fun E hE hsum => ?_⟩
    have h_endpoints : ∀ i ∈ Finset.range E.1,
        (E.2 i).1 ∈ Set.uIcc (0 : ℝ) R ∧ (E.2 i).2 ∈ Set.uIcc (0 : ℝ) R := hE.1
    have h_sums_eq : ∑ i ∈ Finset.range E.1, dist (m (E.2 i).1) (m (E.2 i).2) =
        ∑ i ∈ Finset.range E.1, dist (F (E.2 i).1) (F (E.2 i).2) := by
      apply Finset.sum_congr rfl
      intro i hi
      have h1 : (E.2 i).1 ∈ Set.uIcc (0 : ℝ) R := (h_endpoints i hi).1
      have h2 : (E.2 i).2 ∈ Set.uIcc (0 : ℝ) R := (h_endpoints i hi).2
      rw [h_uIcc_eq] at h1 h2
      have h3 : m (E.2 i).1 = F (E.2 i).1 := h_m_eq (E.2 i).1 h1
      have h4 : m (E.2 i).2 = F (E.2 i).2 := h_m_eq (E.2 i).2 h2
      rw [h3, h4]
    rw [h_sums_eq]
    exact hδ E hE hsum

  have h_deriv : ∀ᵐ (r : ℝ), r ∈ Set.Ioo 0 R → deriv m r = f_sphere r := by
    have h0_in : (0 : ℝ) ∈ Set.uIcc (0 : ℝ) R := by
      simp [uIcc_of_le (show (0 : ℝ) ≤ R by linarith)] <;> linarith
    have h_main : ∀ᵐ (r : ℝ), r ∈ Set.uIcc (0 : ℝ) R → HasDerivAt F (f_sphere r) r := by
      have h := h_ii.ae_hasDerivAt_integral
      filter_upwards [h] with r hr
      intro h_r_in
      exact hr h_r_in 0 h0_in
    filter_upwards [h_main] with r hr
    intro hr_oo
    have h_rpos : 0 < r := hr_oo.1
    have h_rlt : r < R := hr_oo.2
    have h1 : r ∈ Set.uIcc (0 : ℝ) R := by
      rw [h_uIcc_eq]
      exact ⟨le_of_lt h_rpos, le_of_lt h_rlt⟩
    have h2 : HasDerivAt F (f_sphere r) r := hr h1
    have h3 : m =ᶠ[nhds r] F := by
      have h4 : Set.Ioo 0 R ∈ nhds r := IsOpen.mem_nhds isOpen_Ioo ⟨h_rpos, h_rlt⟩
      filter_upwards [h4] with s hs
      have h5 : s ∈ Set.Icc 0 R := ⟨le_of_lt hs.1, le_of_lt hs.2⟩
      exact h_m_eq s h5
    have h5 : HasDerivAt m (f_sphere r) r := h2.congr_of_eventuallyEq h3
    exact h5.deriv

  exact ⟨h_ac, h_mono, h_m0, h_deriv⟩

-- ============================================================================
-- Maggi Theorem 15.5: Two-sided volume lower density (a.e. TRB version)
-- ============================================================================

/-- **Maggi Theorem 15.5 (Steps 1-2)**: Two-sided volume lower density at
a.e. true reduced boundary point.

There exists a `perimeterMeasure`-null set `N` such that for every
`x ∈ trueReducedBoundary U \\ N`, there exist `c > 0`, `R > 0` such that
for all `0 < r < R`:
- `volume(U ∩ ball x r) ≥ c · r^n`
- `volume((ball x r) \\ U) ≥ c · r^n`

## Proof route

1. **Polar bound** (a.e. from Besicovitch differentiation):
   `μ(B(x,r)) ≤ 2 |Dχ_U(B(x,r)) · ν|` for small r.
2. **Tight cutoff**: `|Dχ_U(B(x,r)) · ν| ≤ H^{n-1}(U ∩ sphere x r)` a.e.
3. **Combine**: `μ(B(x,r)) ≤ 2 H^{n-1}(U ∩ sphere x r)`.
4. **Intersection formula**: `P(U ∩ B(x,r)) ≤ P(U; B(x,r)) + H^{n-1}(U ∩ sphere x,r) ≤ 3 H^{n-1}(...)`.
5. **Non-sharp isoperimetric**: `m(r)^((n-1)/n) ≤ C · P(U ∩ B(x,r)) ≤ 3C · m'(r)`.
6. **Integrate ODE**: `m(r) ≥ (r/(3Cn))^n`.
7. **Repeat for complement `Uᶜ`**. -/
theorem maggi15_volume_lower_density
    {U : Set (E n)} (hU : IsOpen U) (hU_reg : U = interior (closure U))
    (hBdd : Bornology.IsBounded U) (hfin : perimeter U < ⊤) (hn : 2 ≤ n) :
    ∃ (N : Set (E n)), MeasurableSet N ∧ perimeterMeasure U N = 0 ∧
      ∀ x ∈ trueReducedBoundary U \ N,
        ∃ (c : ℝ) (R : ℝ), 0 < c ∧ 0 < R ∧
          ∀ r, 0 < r → r < R →
            volume (U ∩ ball x r) ≥ ENNReal.ofReal (c * r ^ n) ∧
            volume ((ball x r) \ U) ≥ ENNReal.ofReal (c * r ^ n) := by
  let μ := perimeterMeasure U
  have hU_meas : MeasurableSet U := hU.measurableSet
  have h_n_pos : 0 < n := by omega

  -- Step 1: A.e. polar bound from Besicovitch differentiation
  have h_polar_ae : ∀ᵐ (x : E n) ∂μ, ∃ (r0 : ℝ), 0 < r0 ∧ ∀ (r : ℝ), 0 < r → r < r0 →
      μ (closedBall x r) ≤
        2 * ENNReal.ofReal |inner ℝ ((distributionalDerivative U) (closedBall x r)) (measureTheoreticNormal U x)| :=
    polar_bound_at_reduced_boundary hfin hn

  -- Extract null exceptional set N from a.e. polar bound
  let P : E n → Prop := fun x => ∃ (r0 : ℝ), 0 < r0 ∧ ∀ (r : ℝ), 0 < r → r < r0 →
    μ (closedBall x r) ≤
      2 * ENNReal.ofReal |inner ℝ ((distributionalDerivative U) (closedBall x r)) (measureTheoreticNormal U x)|
  have h_polar_ae' : ∀ᵐ (x : E n) ∂μ, P x := h_polar_ae
  let S : Set (E n) := {x | ¬P x}
  have hS_null : μ S = 0 := by
    have h : (∀ᵐ (x : E n) ∂μ, P x) ↔ μ S = 0 := ae_iff
    exact h.mp h_polar_ae'
  rcases MeasureTheory.exists_measurable_superset_of_null hS_null with ⟨N, hS_sub_N, hN_meas, hN_null⟩
  have hN_good : ∀ x ∉ N, P x := by
    intro x hxn
    have h_x_not_S : x ∉ S := fun h => hxn (hS_sub_N h)
    simpa [S] using h_x_not_S

  refine ⟨N, hN_meas, hN_null, fun x hx => ?_⟩
  have hx_trb : x ∈ trueReducedBoundary U := hx.1
  have hx_not_N : x ∉ N := hx.2
  let ν := measureTheoreticNormal U x
  have hν_unit : ‖ν‖ = 1 := hx_trb.2

  -- Polar bound at this x
  have h_polar : ∃ (r0 : ℝ), 0 < r0 ∧ ∀ (r : ℝ), 0 < r → r < r0 →
      μ (closedBall x r) ≤
        2 * ENNReal.ofReal |inner ℝ ((distributionalDerivative U) (closedBall x r)) ν| :=
    hN_good x hx_not_N
  rcases h_polar with ⟨r0, hr0_pos, h_polar⟩

  -- Step 2: Tight cutoff inequality
  have h_tight : ∀ᵐ (r : ℝ) ∂volume.restrict (Set.Ioi 0),
      |inner ℝ ((distributionalDerivative U) (closedBall x r)) ν| ≤
        (μHE[n - 1] (U ∩ sphere x r)).toReal :=
    tight_cutoff_inequality hU_meas hBdd hfin hn x ν hν_unit

  -- Step 3: Intersection perimeter bound
  have h_inter : ∀ᵐ (r : ℝ) ∂volume.restrict (Set.Ioi 0),
      perimeter (U ∩ ball x r) ≤
        perimeterIn U (ball x r) + μHE[n - 1] (U ∩ sphere x r) := by
    letI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
    exact perimeter_inter_ball_le hn hU_meas x

  -- Choose R
  let R : ℝ := min r0 1
  have hR_pos : 0 < R := by positivity
  have hR_lt_r0 : R ≤ r0 := min_le_left _ _

  -- Step 4: Volume radial derivative
  let m : ℝ → ℝ := fun r => (volume (U ∩ ball x r)).toReal
  have h_vol_deriv := volume_radial_derivative hU_meas hBdd hn x R hR_pos
  have h_ac : AbsolutelyContinuousOnInterval m 0 R := h_vol_deriv.1
  have h_mono : MonotoneOn m (Set.Icc 0 R) := h_vol_deriv.2.1
  have h_m0 : m 0 = 0 := h_vol_deriv.2.2.1
  have h_deriv : ∀ᵐ (r : ℝ), r ∈ Set.Ioo 0 R →
      deriv m r = (μHE[n - 1] (U ∩ sphere x r)).toReal := h_vol_deriv.2.2.2

  have h_vol_lt_top : ∀ r, volume (U ∩ ball x r) < ⊤ := by
    intro r
    have h_sub : U ∩ ball x r ⊆ U := by simp
    have h : volume (U ∩ ball x r) ≤ volume U := measure_mono h_sub
    exact h.trans_lt hBdd.measure_lt_top

  -- Step 4b: m(r) > 0 for r > 0
  have h_m_pos : ∀ r ∈ Set.Ioc 0 R, 0 < m r := by
    intro r hr
    have h_rpos : 0 < r := hr.1
    -- Show x ∈ frontier U from TRB condition
    have hx_frontier : x ∈ frontier U := by
      by_contra h
      have h_compl_open : IsOpen (frontier U)ᶜ := isClosed_frontier.isOpen_compl
      have h1 : x ∈ (frontier U)ᶜ := h
      have h2 : ∃ (r' : ℝ), 0 < r' ∧ ball x r' ⊆ (frontier U)ᶜ := by
        have h_nhds : (frontier U)ᶜ ∈ nhds x := h_compl_open.mem_nhds h1
        exact (nhds_basis_ball).mem_iff.mp h_nhds
      rcases h2 with ⟨r', hr'_pos, h_sub⟩
      have h3 : perimeterMeasure U (ball x r') = 0 :=
        measure_mono_null h_sub (perimeterMeasure_support_frontier hU)
      have h4 : ∀ (r' : ℝ), 0 < r' → 0 < perimeterMeasure U (ball x r') := hx_trb.1
      have h5 : 0 < perimeterMeasure U (ball x r') := h4 r' hr'_pos
      rw [h3] at h5
      <;> simp at h5
    -- Apply two-sided positive volume theorem
    have h_pos : 0 < volume (U ∩ ball x r) :=
      (frontier_two_sided_positive_volume hU hU_reg hx_frontier h_rpos).1
    have h_vol_lt_top' : volume (U ∩ ball x r) < ⊤ := h_vol_lt_top r
    exact ENNReal.toReal_pos_iff.mpr ⟨h_pos, h_vol_lt_top'⟩

  -- Step 5: Combine perimeter bounds for a.e. r
  have h_perim_bound : ∀ᵐ (r : ℝ), r ∈ Set.Ioo 0 R →
      (perimeter (U ∩ ball x r)).toReal ≤ 3 * (μHE[n - 1] (U ∩ sphere x r)).toReal := by
    let H : ℝ → ENNReal := fun r => μHE[n - 1] (U ∩ sphere x r)
    let inner_val : ℝ → ℝ := fun r =>
      inner ℝ ((distributionalDerivative U) (closedBall x r)) ν
    letI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩

    -- Eilenberg gives H r < ⊤ a.e.
    let dist_x : E n → ℝ := fun y => dist y x
    have h_dist_lip : LipschitzWith (1 : NNReal) dist_x := by
      apply LipschitzWith.of_dist_le_mul
      intro a b
      have h : |dist a x - dist b x| ≤ dist a b := abs_dist_sub_le a b x
      have h' : dist (dist a x) (dist b x) ≤ dist a b := by
        rw [Real.dist_eq] <;> exact h
      simpa [NNReal.coe_one, one_mul] using h'
    rcases eilenberg_μHE hn (hf := h_dist_lip) (by norm_num) with ⟨C, hC_ne_top, _, h_eilenberg⟩
    have h_vol_lt_top2 : volume U < ⊤ := hBdd.measure_lt_top
    have hC_lt_top : C < ⊤ := lt_top_iff_ne_top.mpr hC_ne_top
    have h_lint_fin : (∫⁻ (t : ℝ), H t) < ⊤ := by
      have h1 : (∫⁻ (t : ℝ), H t) ≤ C * volume U := h_eilenberg U
      exact h1.trans_lt (mul_lt_top hC_lt_top h_vol_lt_top2)
    have h_H_ae : AEStronglyMeasurable H volume := distance_coarea_aemeasurable hn x U hU_meas
    have h_H_lt_top : ∀ᵐ (r : ℝ), H r < ⊤ := ae_lt_top' h_H_ae.aemeasurable h_lint_fin.ne

    -- Restrict tight and inter to Ioo 0 R
    have h_tight_ae : ∀ᵐ (r : ℝ), r ∈ Set.Ioo 0 R → |inner_val r| ≤ (H r).toReal := by
      have h1 : ∀ᵐ (r : ℝ), r ∈ Set.Ioi (0 : ℝ) → |inner_val r| ≤ (H r).toReal :=
        (ae_restrict_iff' isOpen_Ioi.measurableSet).mp h_tight
      filter_upwards [h1] with r hP hr; exact hP hr.1
    have h_inter_ae : ∀ᵐ (r : ℝ), r ∈ Set.Ioo 0 R →
        perimeter (U ∩ ball x r) ≤ perimeterIn U (ball x r) + H r := by
      have h1 : ∀ᵐ (r : ℝ), r ∈ Set.Ioi (0 : ℝ) →
          perimeter (U ∩ ball x r) ≤ perimeterIn U (ball x r) + H r :=
        (ae_restrict_iff' isOpen_Ioi.measurableSet).mp h_inter
      filter_upwards [h1] with r hP hr; exact hP hr.1
    have h_H_ae : ∀ᵐ (r : ℝ), r ∈ Set.Ioo 0 R → H r < ⊤ := by
      filter_upwards [h_H_lt_top] with r hH _; exact hH

    -- perimeterIn U (ball x r) ≤ perimeterMeasure U (closedBall x r)
    have h_perimIn_le : ∀ r : ℝ, perimeterIn U (ball x r) ≤ perimeterMeasure U (closedBall x r) := by
      intro r
      have h1 : perimeterIn U (ball x r) ≤ perimeterMeasure U (ball x r) :=
        perimeterIn_le_perimeterMeasure hfin
      have h2 : perimeterMeasure U (ball x r) ≤ perimeterMeasure U (closedBall x r) :=
        measure_mono ball_subset_closedBall
      exact le_trans h1 h2

    filter_upwards [h_tight_ae, h_inter_ae, h_H_ae] with r h_tight_r h_inter_r h_H_r
    intro hr_oo
    have h_rpos : 0 < r := hr_oo.1
    have h_rlt : r < R := hr_oo.2
    have h_rlt_r0 : r < r0 := by linarith

    -- From tight: ENNReal.ofReal |inner| ≤ H
    have h1 : 0 ≤ |inner_val r| := abs_nonneg _
    have h2 : ENNReal.ofReal |inner_val r| ≤ ENNReal.ofReal ((H r).toReal) :=
      ENNReal.ofReal_le_ofReal (h_tight_r hr_oo)
    have h3 : ENNReal.ofReal ((H r).toReal) = H r := ENNReal.ofReal_toReal (h_H_r hr_oo).ne
    have h4 : ENNReal.ofReal |inner_val r| ≤ H r := by rw [h3] at h2; exact h2

    -- Polar bound + perimeterIn ≤ 2 * H
    have h5 : perimeterMeasure U (closedBall x r) ≤ 2 * ENNReal.ofReal |inner_val r| :=
      h_polar r h_rpos h_rlt_r0
    have h6 : perimeterMeasure U (closedBall x r) ≤ 2 * H r := by
      calc perimeterMeasure U (closedBall x r)
        ≤ 2 * ENNReal.ofReal |inner_val r| := h5
      _ ≤ 2 * H r := by gcongr
    have h7 : perimeterIn U (ball x r) ≤ 2 * H r := le_trans (h_perimIn_le r) h6

    -- Intersection formula
    have h8 : perimeter (U ∩ ball x r) ≤ perimeterIn U (ball x r) + H r := h_inter_r hr_oo
    have h9 : perimeter (U ∩ ball x r) ≤ 3 * H r := by
      calc perimeter (U ∩ ball x r)
        ≤ perimeterIn U (ball x r) + H r := h8
      _ ≤ 2 * H r + H r := by gcongr
      _ = 3 * H r := by ring

    have h10 : 3 * H r < ⊤ := mul_lt_top (by norm_num) (h_H_r hr_oo)
    have h11 : perimeter (U ∩ ball x r) < ⊤ := h9.trans_lt h10
    have h12 : (perimeter (U ∩ ball x r)).toReal ≤ (3 * H r).toReal :=
      ENNReal.toReal_mono h10.ne h9
    have h13 : (3 * H r).toReal = 3 * (H r).toReal := by
      rw [ENNReal.toReal_mul] <;> norm_num
    rw [h13] at h12
    exact h12

  -- Step 6: Non-sharp isoperimetric constant
  let C_iso_real : ℝ := ((n : ENNReal) *
    ↑(MeasureTheory.eLpNormLESNormFDerivOneConst (E := E n) volume ((sobolevP n : ℝ)))).toReal
  have hC_iso_real_pos : 0 < C_iso_real := by
    let C_S : NNReal := MeasureTheory.eLpNormLESNormFDerivOneConst (E := E n) volume ((sobolevP n : ℝ))
    have hC_S_pos : 0 < C_S := by
      dsimp only [C_S]
      rw [MeasureTheory.eLpNormLESNormFDerivOneConst_def]
      have hp_pos : 0 < (sobolevP n : ℝ) := sobolevP_pos hn
      have h_main_pos : 0 < MeasureTheory.lintegralPowLePowLIntegralFDerivConst (E := E n) volume ((sobolevP n : ℝ)) := by
        rw [MeasureTheory.lintegralPowLePowLIntegralFDerivConst_def]
        dsimp only
        let ι := Fin (Module.finrank ℝ (E n))
        have h_finrank_eq : Module.finrank ℝ (E n) = n := by simp
        have h_n_pos : 0 < Module.finrank ℝ (E n) := by
          rw [h_finrank_eq] <;> omega
        have h1 : Fintype.card ι = Module.finrank ℝ (E n) := by simp [ι]
        have h2 : Module.finrank ℝ (ι → ℝ) = Fintype.card ι := by simp
        have h_eq : Module.finrank ℝ (E n) = Module.finrank ℝ (ι → ℝ) := (h2.trans h1).symm
        let e : (E n) ≃L[ℝ] (ι → ℝ) := ContinuousLinearEquiv.ofFinrankEq h_eq
        let c : NNReal := MeasureTheory.Measure.addHaarScalarFactor volume ((volume : Measure (ι → ℝ)).map e.symm)
        have h_n_pos' : 0 < n := by omega
        let i : Fin n := ⟨0, h_n_pos'⟩
        haveI : Nontrivial (E n) := by
          refine' ⟨0, EuclideanSpace.single i 1, _⟩
          intro h
          have h4 := congr_arg (fun f : E n => f i) h
          simp at h4 <;> norm_num at h4
        have hc : 0 < c := by
          exact MeasureTheory.Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure volume ((volume : Measure (ι → ℝ)).map e.symm)
        have he_pos : 0 < ‖(e.symm : (ι → ℝ) →L[ℝ] E n)‖₊ :=
          ContinuousLinearEquiv.nnnorm_symm_pos e
        have h1a : 0 < ‖(e.symm : (ι → ℝ) →L[ℝ] E n)‖₊ ^ (sobolevP n : ℝ) :=
          NNReal.rpow_pos (hx_pos := he_pos)
        have h1 : 0 < c * ‖(e.symm : (ι → ℝ) →L[ℝ] E n)‖₊ ^ (sobolevP n : ℝ) := mul_pos hc h1a
        have hcp : 0 < c ^ (sobolevP n : ℝ) := NNReal.rpow_pos (hx_pos := hc)
        have h2 : 0 < (c ^ (sobolevP n : ℝ))⁻¹ := inv_pos.mpr hcp
        exact mul_pos h1 h2
      have h : 0 < (MeasureTheory.lintegralPowLePowLIntegralFDerivConst (E := E n) volume ((sobolevP n : ℝ))) ^ ((sobolevP n : ℝ)⁻¹) :=
        NNReal.rpow_pos (hx_pos := h_main_pos)
      exact h
    have h1 : (n : ENNReal) ≠ 0 := by
      have h11 : 0 < n := by omega
      exact ne_of_gt (by exact_mod_cast h11)
    have h2 : (↑C_S : ENNReal) ≠ 0 := by exact_mod_cast hC_S_pos.ne'
    have h3 : (0 : ENNReal) < (n : ENNReal) * ↑C_S := ENNReal.mul_pos h1 h2
    have h4 : (n : ENNReal) * ↑C_S < ⊤ := by
      apply ENNReal.mul_lt_top
      · exact ENNReal.natCast_lt_top n
      · exact ENNReal.coe_lt_top
    have h5 : 0 < (((n : ENNReal) * ↑C_S).toReal) := ENNReal.toReal_pos h3.ne' h4.ne
    exact h5

  have h_isop : ∀ᵐ (r : ℝ), r ∈ Set.Ioo 0 R →
      (m r) ^ (((n : ℝ) - 1) / (n : ℝ)) ≤ C_iso_real * (perimeter (U ∩ ball x r)).toReal := by
    have h_sub : Set.Ioo 0 R ⊆ Set.Ioi 0 := by intro x hx; exact hx.1
    have h_inter_R : ∀ᵐ (r : ℝ) ∂volume.restrict (Set.Ioo 0 R),
        perimeter (U ∩ ball x r) ≤ perimeterIn U (ball x r) + μHE[n - 1] (U ∩ sphere x r) :=
      ae_restrict_of_ae_restrict_of_subset h_sub h_inter
    have h_inter_R' : ∀ᵐ (r : ℝ), r ∈ Set.Ioo 0 R →
        perimeter (U ∩ ball x r) ≤ perimeterIn U (ball x r) + μHE[n - 1] (U ∩ sphere x r) := by
      rwa [ae_restrict_iff' measurableSet_Ioo] at h_inter_R
    filter_upwards [h_inter_R'] with r hinter hr
    let S := U ∩ ball x r
    have hS_meas : MeasurableSet S := hU_meas.inter isOpen_ball.measurableSet
    have hS_bdd : Bornology.IsBounded S := Bornology.IsBounded.subset hBdd (fun x hx => hx.1)
    have hr_pos : 0 < r := hr.1
    have h_perim_lt_top : perimeter S < ⊤ := by
      have h1 : perimeter S ≤ perimeterIn U (ball x r) + μHE[n - 1] (U ∩ sphere x r) := hinter hr
      have h2 : perimeterIn U (ball x r) ≤ perimeter U := by
        have h2a : perimeterIn U (ball x r) ≤ perimeterMeasure U (ball x r) :=
          perimeterIn_le_perimeterMeasure hfin
        have h2b : perimeterMeasure U (ball x r) ≤ perimeterMeasure U Set.univ :=
          measure_mono (subset_univ _)
        have h2c : perimeterMeasure U Set.univ = perimeter U :=
          (perimeter_eq_variation U hfin).symm
        calc
          perimeterIn U (ball x r)
            ≤ perimeterMeasure U (ball x r) := h2a
          _ ≤ perimeterMeasure U Set.univ := h2b
          _ = perimeter U := h2c
      have h3 : μHE[n - 1] (U ∩ sphere x r) < ⊤ := by
        have h4 : μHE[n - 1] (U ∩ sphere x r) ≤ μHE[n - 1] (sphere x r) := measure_mono (by simp)
        have h5 : μHE[n - 1] (sphere x r) < ⊤ := by
          rw [sphere_hausdorff_scale x hr_pos]
          have h_unit : μHE[n - 1] (sphere (0 : E n) 1) < ⊤ := unit_sphere_hausdorff_finite hn
          have h_rpow_lt_top : ENNReal.ofReal (r ^ (n - 1)) < ⊤ := ENNReal.ofReal_lt_top
          exact mul_lt_top h_rpow_lt_top h_unit
        exact h4.trans_lt h5
      have h6 : perimeterIn U (ball x r) < ⊤ := h2.trans_lt hfin
      have h7 : perimeterIn U (ball x r) + μHE[n - 1] (U ∩ sphere x r) < ⊤ :=
        (add_lt_top).mpr ⟨h6, h3⟩
      exact h1.trans_lt h7
    have h_iso_ENNReal : (volume S) ^ ((n - 1 : ℝ) / n) ≤
        (n : ENNReal) * ↑(MeasureTheory.eLpNormLESNormFDerivOneConst (E := E n) volume ((sobolevP n : ℝ))) * perimeter S :=
      non_sharp_isoperimetric_perimeter hn hS_meas hS_bdd
    have h_vol_lt_top : volume S < ⊤ := by
      have h_sub : S ⊆ U := fun x hx => hx.1
      have h : volume S ≤ volume U := measure_mono h_sub
      exact h.trans_lt hBdd.measure_lt_top
    have h_lhs : (m r) ^ (((n : ℝ) - 1) / (n : ℝ)) =
        ((volume S) ^ ((n - 1 : ℝ) / n)).toReal := by
      have h_eq1 : m r = (volume S).toReal := by rfl
      rw [h_eq1]
      exact ENNReal.toReal_rpow (volume S) (((n : ℝ) - 1) / (n : ℝ))
    rw [h_lhs]
    have h_rhs : C_iso_real * (perimeter S).toReal =
        (((n : ENNReal) * ↑(MeasureTheory.eLpNormLESNormFDerivOneConst (E := E n) volume ((sobolevP n : ℝ))) * perimeter S).toReal) := by
      simp [C_iso_real, ENNReal.toReal_mul] <;> ring
    rw [h_rhs]
    have h_rhs_lt_top : (n : ENNReal) * ↑(MeasureTheory.eLpNormLESNormFDerivOneConst (E := E n) volume ((sobolevP n : ℝ))) * perimeter S < ⊤ := by
      apply ENNReal.mul_lt_top
      · apply ENNReal.mul_lt_top
        · exact ENNReal.natCast_lt_top n
        · exact ENNReal.coe_lt_top
      · exact h_perim_lt_top
    have h_exp_nonneg : 0 ≤ ((n - 1 : ℝ) / n) := by
      have h1 : 0 < (n : ℝ) := by positivity
      have h2 : 0 ≤ (n : ℝ) - 1 := by
        have h3 : (n : ℝ) ≥ 2 := by exact_mod_cast hn
        linarith
      exact div_nonneg h2 h1.le
    have h_lhs_lt_top : (volume S) ^ ((n - 1 : ℝ) / n) < ⊤ :=
      ENNReal.rpow_lt_top_of_nonneg h_exp_nonneg h_vol_lt_top.ne
    exact (ENNReal.toReal_le_toReal h_lhs_lt_top.ne h_rhs_lt_top.ne).mpr h_iso_ENNReal

  -- Step 7: Differential inequality m'(r) ≥ (1/(3*C_iso)) * m(r)^α
  have h_diff_ineq : ∀ᵐ (r : ℝ), r ∈ Set.Ioo 0 R →
      deriv m r ≥ (1 / (3 * C_iso_real)) * (m r) ^ (((n : ℝ) - 1) / (n : ℝ)) := by
    filter_upwards [h_deriv, h_perim_bound, h_isop] with r hderiv hperim h_isop_r
    intro hr
    have h1 : (m r) ^ (((n : ℝ) - 1) / (n : ℝ)) ≤ C_iso_real * (perimeter (U ∩ ball x r)).toReal :=
      h_isop_r hr
    have h2 : (perimeter (U ∩ ball x r)).toReal ≤ 3 * deriv m r := by
      rw [hderiv hr] at *
      <;> exact hperim hr
    have h3 : (m r) ^ (((n : ℝ) - 1) / (n : ℝ)) ≤ 3 * C_iso_real * deriv m r := by
      calc
        (m r) ^ (((n : ℝ) - 1) / (n : ℝ))
          ≤ C_iso_real * (perimeter (U ∩ ball x r)).toReal := h1
        _ ≤ C_iso_real * (3 * deriv m r) := by gcongr
        _ = 3 * C_iso_real * deriv m r := by ring
    have h4 : 0 < 3 * C_iso_real := by positivity
    have h5 : (1 / (3 * C_iso_real)) * (m r) ^ (((n : ℝ) - 1) / (n : ℝ)) ≤ deriv m r := by
      calc
        (1 / (3 * C_iso_real)) * (m r) ^ (((n : ℝ) - 1) / (n : ℝ))
          ≤ (1 / (3 * C_iso_real)) * (3 * C_iso_real * deriv m r) := by gcongr
        _ = deriv m r := by
          field_simp [h4.ne'] <;> ring
    exact h5

  -- Step 8: Integrate differential inequality to get lower volume bound
  have h_volume_U : ∃ (c_U : ℝ), 0 < c_U ∧
      ∀ r, 0 < r → r < R →
        volume (U ∩ ball x r) ≥ ENNReal.ofReal (c_U * r ^ n) := by
    let C := 3 * C_iso_real
    have hC_pos : 0 < C := by positivity
    have h_ode : ∀ r ∈ Set.Icc 0 R, m r ≥ (r / (C * (n : ℝ))) ^ n :=
      isoperimetric_differential_inequality (by linarith : 1 ≤ n) hC_pos hR_pos h_mono
        (fun r hr => by
          have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) R := ⟨by linarith, by linarith⟩
          have h_le : (0 : ℝ) ≤ r := (Set.mem_Icc.mp hr).1
          have h : m 0 ≤ m r := h_mono h0 hr h_le
          rw [h_m0] at h
          exact h)
        h_ac h_m0 h_m_pos h_diff_ineq
    let c_U : ℝ := (1 / (C * (n : ℝ))) ^ n
    have hc_U_pos : 0 < c_U := by positivity
    have h_main : ∀ r, 0 < r → r < R → m r ≥ c_U * r ^ n := by
      intro r hr_pos hr_lt
      have hr_in : r ∈ Set.Icc 0 R := ⟨by linarith, by linarith⟩
      have h1 : m r ≥ (r / (C * (n : ℝ))) ^ n := h_ode r hr_in
      have h2 : (r / (C * (n : ℝ))) ^ n = c_U * r ^ n := by
        have h3 : (r / (C * (n : ℝ))) = (1 / (C * (n : ℝ))) * r := by ring
        rw [h3]
        rw [mul_pow]
        <;> ring
      rw [h2] at h1
      exact h1
    refine ⟨c_U, hc_U_pos, fun r hr_pos hr_lt => ?_⟩
    have h4 : m r ≥ c_U * r ^ n := h_main r hr_pos hr_lt
    have h5 : 0 ≤ c_U * r ^ n := by positivity
    have h6 : volume (U ∩ ball x r) = ENNReal.ofReal (m r) := by
      have h7 : volume (U ∩ ball x r) < ⊤ := h_vol_lt_top r
      rw [ENNReal.ofReal_toReal h7.ne]
    rw [h6]
    exact ENNReal.ofReal_le_ofReal h4

  -- Step 9: Complement bound (Route 1: use Uᶜ directly with unbounded tight cutoff)
  have h_compl : ∃ (c_C : ℝ), 0 < c_C ∧
      ∀ r, 0 < r → r < R →
        volume ((ball x r) \ U) ≥ ENNReal.ofReal (c_C * r ^ n) := by
    let Uc := Uᶜ
    have hUc_meas : MeasurableSet Uc := hU_meas.compl
    have hfin_C : perimeter Uc < ⊤ := by
      rw [perimeter_compl hU_meas hfin] <;> exact hfin
    let ν_C := -ν
    have hν_C_unit : ‖ν_C‖ = 1 := by
      simp [ν_C, hν_unit] <;> rfl

    -- Complement facts
    have h_D_compl : distributionalDerivative Uc = -distributionalDerivative U :=
      distributionalDerivative_compl hU_meas hfin
    have h_perimMeasure_compl : perimeterMeasure Uc = perimeterMeasure U :=
      perimeterMeasure_compl hU_meas hfin

    -- Pick r' > R for volume radial derivative (V' must be bounded)
    let r' : ℝ := R + 1
    have hr'_gt_R : R < r' := by
      dsimp only [r'] <;> linarith
    have hr'_pos : 0 < r' := by
      dsimp only [r'] <;> linarith
    let V' := Uc ∩ ball x r'
    have hV'_meas : MeasurableSet V' := hUc_meas.inter isOpen_ball.measurableSet
    have hV'_bdd : Bornology.IsBounded V' :=
      Metric.isBounded_ball.subset (fun y hy => hy.2)

    -- Polar bound for Uc using complement facts
    have h_R_le_r0 : R ≤ r0 := by
      simp [R] <;> exact min_le_left _ _
    have h_polar_C : ∀ (r : ℝ), 0 < r → r < R →
        perimeterMeasure Uc (closedBall x r) ≤
          2 * ENNReal.ofReal |inner ℝ ((distributionalDerivative Uc) (closedBall x r)) ν_C| := by
      intro r hr_pos hr_lt_R
      have hr_lt_r0 : r < r0 := by linarith
      have h_goal := h_polar r hr_pos hr_lt_r0
      have h_abs_eq : |inner ℝ ((distributionalDerivative Uc) (closedBall x r)) ν_C| =
          |inner ℝ ((distributionalDerivative U) (closedBall x r)) ν| := by
        rw [h_D_compl]
        <;> simp [ν_C, inner_neg_left, inner_neg_right] <;> ring
      have h_main : perimeterMeasure Uc (closedBall x r) ≤
          2 * ENNReal.ofReal |inner ℝ ((distributionalDerivative Uc) (closedBall x r)) ν_C| := by
        rw [h_perimMeasure_compl, h_abs_eq]
        <;> exact h_goal
      exact h_main

    -- Tight cutoff for Uc (unbounded version)
    have h_tight_C : ∀ᵐ (r : ℝ) ∂volume.restrict (Set.Ioi 0),
        |inner ℝ ((distributionalDerivative Uc) (closedBall x r)) ν_C| ≤
          (μHE[n - 1] (Uc ∩ sphere x r)).toReal :=
      tight_cutoff_inequality_unbounded hUc_meas hfin_C hn x ν_C hν_C_unit

    -- Restrict to Ioo 0 R
    have h_sub_C : Set.Ioo 0 R ⊆ Set.Ioi 0 := by intro z hz; exact hz.1
    have h_tight_C_R : ∀ᵐ (r : ℝ), r ∈ Set.Ioo 0 R →
        |inner ℝ ((distributionalDerivative Uc) (closedBall x r)) ν_C| ≤
          (μHE[n - 1] (Uc ∩ sphere x r)).toReal := by
      have h1 : ∀ᵐ (r : ℝ) ∂volume.restrict (Set.Ioo 0 R),
          |inner ℝ ((distributionalDerivative Uc) (closedBall x r)) ν_C| ≤
            (μHE[n - 1] (Uc ∩ sphere x r)).toReal :=
          ae_restrict_of_ae_restrict_of_subset h_sub_C h_tight_C
      rwa [ae_restrict_iff' measurableSet_Ioo] at h1

    -- Intersection perimeter for Uc
    have h_inter_C : ∀ᵐ (r : ℝ) ∂volume.restrict (Set.Ioi 0),
        perimeter (Uc ∩ ball x r) ≤
          perimeterIn Uc (ball x r) + μHE[n - 1] (Uc ∩ sphere x r) := by
      letI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
      exact perimeter_inter_ball_le hn hUc_meas x
    have h_inter_C_R : ∀ᵐ (r : ℝ), r ∈ Set.Ioo 0 R →
        perimeter (Uc ∩ ball x r) ≤
          perimeterIn Uc (ball x r) + μHE[n - 1] (Uc ∩ sphere x r) := by
      have h1 : ∀ᵐ (r : ℝ) ∂volume.restrict (Set.Ioo 0 R),
          perimeter (Uc ∩ ball x r) ≤
            perimeterIn Uc (ball x r) + μHE[n - 1] (Uc ∩ sphere x r) :=
          ae_restrict_of_ae_restrict_of_subset h_sub_C h_inter_C
      rwa [ae_restrict_iff' measurableSet_Ioo] at h1

    -- Volume radial derivative for V' (bounded)
    let m_C : ℝ → ℝ := fun r => (volume (V' ∩ ball x r)).toReal
    have h_vol_deriv_C := volume_radial_derivative hV'_meas hV'_bdd hn x R hR_pos
    have h_ac_C : AbsolutelyContinuousOnInterval m_C 0 R := h_vol_deriv_C.1
    have h_mono_C : MonotoneOn m_C (Set.Icc 0 R) := h_vol_deriv_C.2.1
    have h_m0_C : m_C 0 = 0 := h_vol_deriv_C.2.2.1
    have h_deriv_C : ∀ᵐ (r : ℝ), r ∈ Set.Ioo 0 R →
        deriv m_C r = (μHE[n - 1] (V' ∩ sphere x r)).toReal := h_vol_deriv_C.2.2.2

    -- For r < R, V' ∩ ball x r = Uc ∩ ball x r = (ball x r) \ U
    have h_eq_set : ∀ r, 0 < r → r < R → V' ∩ ball x r = (ball x r) \ U := by
      intro r hr_pos hr_lt_R
      have h_r_lt_r' : r < r' := by linarith
      ext y
      simp only [V', Uc, Set.mem_inter_iff, Set.mem_diff, Set.mem_compl_iff]
      constructor
      · rintro ⟨⟨hny, hball1⟩, hball2⟩
        exact ⟨hball2, hny⟩
      · rintro ⟨hball, hny⟩
        have hball1 : y ∈ ball x r' := ball_subset_ball (by linarith) hball
        exact ⟨⟨hny, hball1⟩, hball⟩
    have h_eq_sphere : ∀ r, 0 < r → r < R → V' ∩ sphere x r = Uc ∩ sphere x r := by
      intro r hr_pos hr_lt_R
      have h_r_lt_r' : r < r' := by linarith [hr_lt_R, hr'_gt_R]
      ext y
      simp only [V', Set.mem_inter_iff]
      constructor
      · rintro ⟨⟨hUc, _⟩, hsphere⟩
        exact ⟨hUc, hsphere⟩
      · rintro ⟨hUc, hsphere⟩
        have h3 : y ∈ ball x r' := by
          have h4 : dist y x = r := by
            simpa [Metric.mem_sphere, dist_eq_norm] using hsphere
          simpa [Metric.mem_ball, h4] using h_r_lt_r'
        exact ⟨⟨hUc, h3⟩, hsphere⟩

    -- Hausdorff finiteness for Uc ∩ sphere
    have h_Haus_lt_top_C : ∀ r, 0 < r → r < R → μHE[n - 1] (Uc ∩ sphere x r) < ⊤ := by
      intro r hr_pos hr_lt_R
      have h1 : Uc ∩ sphere x r ⊆ sphere x r := by simp
      have h2 : μHE[n - 1] (sphere x r) < ⊤ := by
        rw [sphere_hausdorff_scale x hr_pos]
        have h_unit : μHE[n - 1] (sphere (0 : E n) 1) < ⊤ := unit_sphere_hausdorff_finite hn
        exact mul_lt_top ENNReal.ofReal_lt_top h_unit
      exact (measure_mono h1).trans_lt h2

    -- Combine perimeter bounds for Uc
    have h_perim_bound_C : ∀ᵐ (r : ℝ), r ∈ Set.Ioo 0 R →
        (perimeter (Uc ∩ ball x r)).toReal ≤ 3 * (μHE[n - 1] (Uc ∩ sphere x r)).toReal := by
      filter_upwards [h_tight_C_R, h_inter_C_R] with r h_tight_r h_inter_r
      intro hr_oo
      have hr_pos : 0 < r := hr_oo.1
      have hr_lt_R : r < R := hr_oo.2
      let H_C := μHE[n - 1] (Uc ∩ sphere x r)
      have h_H_lt_top : H_C < ⊤ := h_Haus_lt_top_C r hr_pos hr_lt_R
      have h_polar_r : perimeterMeasure Uc (closedBall x r) ≤
          2 * ENNReal.ofReal |inner ℝ ((distributionalDerivative Uc) (closedBall x r)) ν_C| :=
        h_polar_C r hr_pos hr_lt_R
      have h_tight_ENNReal : ENNReal.ofReal |inner ℝ ((distributionalDerivative Uc) (closedBall x r)) ν_C| ≤ H_C := by
        have h4 : |inner ℝ ((distributionalDerivative Uc) (closedBall x r)) ν_C| ≤ H_C.toReal := h_tight_r hr_oo
        have h5 : ENNReal.ofReal |inner ℝ ((distributionalDerivative Uc) (closedBall x r)) ν_C| ≤
            ENNReal.ofReal (H_C.toReal) := ENNReal.ofReal_le_ofReal h4
        rw [ENNReal.ofReal_toReal h_H_lt_top.ne] at h5
        exact h5
      have h1 : perimeterMeasure Uc (closedBall x r) ≤ 2 * H_C := by
        calc
          perimeterMeasure Uc (closedBall x r)
            ≤ 2 * ENNReal.ofReal |inner ℝ ((distributionalDerivative Uc) (closedBall x r)) ν_C| := h_polar_r
          _ ≤ 2 * H_C := by gcongr
      have h2 : perimeterIn Uc (ball x r) ≤ perimeterMeasure Uc (closedBall x r) := by
        have h2a : perimeterIn Uc (ball x r) ≤ perimeterMeasure Uc (ball x r) :=
          perimeterIn_le_perimeterMeasure hfin_C
        have h2b : perimeterMeasure Uc (ball x r) ≤ perimeterMeasure Uc (closedBall x r) :=
          measure_mono ball_subset_closedBall
        exact le_trans h2a h2b
      have h3 : perimeter (Uc ∩ ball x r) ≤ 3 * H_C := by
        calc
          perimeter (Uc ∩ ball x r)
            ≤ perimeterIn Uc (ball x r) + H_C := h_inter_r hr_oo
          _ ≤ perimeterMeasure Uc (closedBall x r) + H_C := by gcongr
          _ ≤ 2 * H_C + H_C := by gcongr
          _ = 3 * H_C := by ring
      have h_3H_lt_top : 3 * H_C < ⊤ := mul_lt_top (by norm_num) h_H_lt_top
      have h4 : perimeter (Uc ∩ ball x r) ≠ ⊤ := (h3.trans_lt h_3H_lt_top).ne
      have h5 : (perimeter (Uc ∩ ball x r)).toReal ≤ (3 * H_C).toReal :=
        (ENNReal.toReal_le_toReal h4 h_3H_lt_top.ne).mpr h3
      have h6 : (3 * H_C).toReal = 3 * H_C.toReal := by
        rw [ENNReal.toReal_mul] <;> norm_num
      rw [h6] at h5
      exact h5

    -- Non-sharp isoperimetric for Uc ∩ ball (ae)
    have h_isop_C : ∀ᵐ (r : ℝ), r ∈ Set.Ioo 0 R →
        (m_C r) ^ (((n : ℝ) - 1) / (n : ℝ)) ≤ C_iso_real * (perimeter (Uc ∩ ball x r)).toReal := by
      filter_upwards [h_inter_C_R, h_perim_bound_C, h_tight_C_R] with r h_inter_r h_perim_r h_tight_r
      intro hr_oo
      let S := Uc ∩ ball x r
      have hS_meas : MeasurableSet S := hUc_meas.inter isOpen_ball.measurableSet
      have hS_bdd : Bornology.IsBounded S :=
        Metric.isBounded_ball.subset (fun y hy => hy.2)
      have hr_pos : 0 < r := hr_oo.1
      have h_perim_lt_top : perimeter S < ⊤ := by
        have h1 : perimeter S ≤ perimeterIn Uc (ball x r) + μHE[n - 1] (Uc ∩ sphere x r) := h_inter_r hr_oo
        have h2 : perimeterIn Uc (ball x r) ≤ perimeterMeasure Uc (closedBall x r) := by
          have h2a : perimeterIn Uc (ball x r) ≤ perimeterMeasure Uc (ball x r) :=
            perimeterIn_le_perimeterMeasure hfin_C
          have h2b : perimeterMeasure Uc (ball x r) ≤ perimeterMeasure Uc (closedBall x r) :=
            measure_mono ball_subset_closedBall
          exact le_trans h2a h2b
        have h3 : perimeterMeasure Uc (closedBall x r) ≤ 2 * μHE[n - 1] (Uc ∩ sphere x r) := by
          have h4 := h_polar_C r hr_pos hr_oo.2
          have h5 : ENNReal.ofReal |inner ℝ ((distributionalDerivative Uc) (closedBall x r)) ν_C| ≤
              μHE[n - 1] (Uc ∩ sphere x r) := by
            have h6 : |inner ℝ ((distributionalDerivative Uc) (closedBall x r)) ν_C| ≤
                (μHE[n - 1] (Uc ∩ sphere x r)).toReal := h_tight_r hr_oo
            have h7 : μHE[n - 1] (Uc ∩ sphere x r) < ⊤ := h_Haus_lt_top_C r hr_pos hr_oo.2
            have h8 : ENNReal.ofReal |inner ℝ ((distributionalDerivative Uc) (closedBall x r)) ν_C| ≤
                ENNReal.ofReal ((μHE[n - 1] (Uc ∩ sphere x r)).toReal) :=
              ENNReal.ofReal_le_ofReal h6
            rw [ENNReal.ofReal_toReal h7.ne] at h8
            exact h8
          calc
            perimeterMeasure Uc (closedBall x r)
              ≤ 2 * ENNReal.ofReal |inner ℝ ((distributionalDerivative Uc) (closedBall x r)) ν_C| := h4
            _ ≤ 2 * μHE[n - 1] (Uc ∩ sphere x r) := by gcongr
        have h4 : μHE[n - 1] (Uc ∩ sphere x r) < ⊤ := h_Haus_lt_top_C r hr_pos hr_oo.2
        have h5 : 2 * μHE[n - 1] (Uc ∩ sphere x r) < ⊤ := mul_lt_top (by norm_num) h4
        have h6 : perimeterMeasure Uc (closedBall x r) < ⊤ := h3.trans_lt h5
        exact h1.trans_lt ((add_lt_top).mpr ⟨h2.trans_lt h6, h4⟩)
      have h_iso_ENNReal : (volume S) ^ ((n - 1 : ℝ) / n) ≤
          (n : ENNReal) * ↑(MeasureTheory.eLpNormLESNormFDerivOneConst (E := E n) volume ((sobolevP n : ℝ))) * perimeter S :=
        non_sharp_isoperimetric_perimeter hn hS_meas hS_bdd
      have h_vol_lt_top : volume S < ⊤ := by
        have h_sub : S ⊆ ball x r := fun y hy => hy.2
        have h : volume S ≤ volume (ball x r) := measure_mono h_sub
        exact h.trans_lt measure_ball_lt_top
      have h_r_lt_r' : r < r' := by linarith [hr_oo.2, hr'_gt_R]
      have h_set : V' ∩ ball x r = S := by
        ext y
        simp only [V', S, Set.mem_inter_iff]
        constructor
        · rintro ⟨⟨hUc, _⟩, hball⟩
          exact ⟨hUc, hball⟩
        · rintro ⟨hUc, hball⟩
          have h3 : y ∈ ball x r' := ball_subset_ball (le_of_lt h_r_lt_r') hball
          exact ⟨⟨hUc, h3⟩, hball⟩
      have h_eq1 : m_C r = (volume S).toReal := by
        dsimp only [m_C]
        rw [h_set] <;> rfl
      have h_lhs : (m_C r) ^ (((n : ℝ) - 1) / (n : ℝ)) =
          ((volume S) ^ ((n - 1 : ℝ) / n)).toReal := by
        rw [h_eq1]
        exact ENNReal.toReal_rpow (volume S) (((n : ℝ) - 1) / (n : ℝ))
      rw [h_lhs]
      have h_rhs : C_iso_real * (perimeter S).toReal =
          (((n : ENNReal) * ↑(MeasureTheory.eLpNormLESNormFDerivOneConst (E := E n) volume ((sobolevP n : ℝ))) * perimeter S).toReal) := by
        simp [C_iso_real, ENNReal.toReal_mul] <;> ring
      rw [h_rhs]
      have h_rhs_lt_top : (n : ENNReal) * ↑(MeasureTheory.eLpNormLESNormFDerivOneConst (E := E n) volume ((sobolevP n : ℝ))) * perimeter S < ⊤ := by
        apply ENNReal.mul_lt_top
        · apply ENNReal.mul_lt_top
          · exact ENNReal.natCast_lt_top n
          · exact ENNReal.coe_lt_top
        · exact h_perim_lt_top
      have h_exp_nonneg : 0 ≤ ((n - 1 : ℝ) / n) := by
        have h1 : 0 < (n : ℝ) := by positivity
        have h2 : 0 ≤ (n : ℝ) - 1 := by
          have h3 : (n : ℝ) ≥ 2 := by exact_mod_cast hn
          linarith
        exact div_nonneg h2 h1.le
      have h_lhs_lt_top : (volume S) ^ ((n - 1 : ℝ) / n) < ⊤ :=
        ENNReal.rpow_lt_top_of_nonneg h_exp_nonneg h_vol_lt_top.ne
      exact (ENNReal.toReal_le_toReal h_lhs_lt_top.ne h_rhs_lt_top.ne).mpr h_iso_ENNReal

    -- Differential inequality for m_C
    have h_diff_ineq_C : ∀ᵐ (r : ℝ), r ∈ Set.Ioo 0 R →
        deriv m_C r ≥ (1 / (3 * C_iso_real)) * (m_C r) ^ (((n : ℝ) - 1) / (n : ℝ)) := by
      filter_upwards [h_deriv_C, h_perim_bound_C, h_isop_C] with r hderiv hperim h_isop_r
      intro hr
      have h1 : (m_C r) ^ (((n : ℝ) - 1) / (n : ℝ)) ≤ C_iso_real * (perimeter (Uc ∩ ball x r)).toReal :=
        h_isop_r hr
      have h2 : (perimeter (Uc ∩ ball x r)).toReal ≤ 3 * deriv m_C r := by
        have h3 : deriv m_C r = (μHE[n - 1] (V' ∩ sphere x r)).toReal := hderiv hr
        have h4 : V' ∩ sphere x r = Uc ∩ sphere x r := h_eq_sphere r hr.1 hr.2
        rw [h3, h4]
        exact hperim hr
      have h3 : (m_C r) ^ (((n : ℝ) - 1) / (n : ℝ)) ≤ 3 * C_iso_real * deriv m_C r := by
        calc
          (m_C r) ^ (((n : ℝ) - 1) / (n : ℝ))
            ≤ C_iso_real * (perimeter (Uc ∩ ball x r)).toReal := h1
          _ ≤ C_iso_real * (3 * deriv m_C r) := by gcongr
          _ = 3 * C_iso_real * deriv m_C r := by ring
      have h4 : 0 < 3 * C_iso_real := by positivity
      have h5 : (1 / (3 * C_iso_real)) * (m_C r) ^ (((n : ℝ) - 1) / (n : ℝ)) ≤ deriv m_C r := by
        calc
          (1 / (3 * C_iso_real)) * (m_C r) ^ (((n : ℝ) - 1) / (n : ℝ))
            ≤ (1 / (3 * C_iso_real)) * (3 * C_iso_real * deriv m_C r) := by gcongr
          _ = deriv m_C r := by
            field_simp [h4.ne'] <;> ring
      exact h5

    -- m_C(r) > 0 for r > 0 (using two-sided positive volume at frontier)
    have h_m_pos_C : ∀ r ∈ Set.Ioc 0 R, 0 < m_C r := by
      intro r hr
      have hr_pos : 0 < r := hr.1
      have hx_frontier : x ∈ frontier U := by
        by_contra h
        have h_compl_open : IsOpen (frontier U)ᶜ := isClosed_frontier.isOpen_compl
        have h1 : x ∈ (frontier U)ᶜ := h
        have h2 : ∃ (r' : ℝ), 0 < r' ∧ ball x r' ⊆ (frontier U)ᶜ := by
          have h_nhds : (frontier U)ᶜ ∈ nhds x := h_compl_open.mem_nhds h1
          exact (nhds_basis_ball).mem_iff.mp h_nhds
        rcases h2 with ⟨r', hr'_pos, h_sub⟩
        have h3 : perimeterMeasure U (ball x r') = 0 :=
          measure_mono_null h_sub (perimeterMeasure_support_frontier hU)
        have h4 : ∀ (r' : ℝ), 0 < r' → 0 < perimeterMeasure U (ball x r') := hx_trb.1
        have h5 : 0 < perimeterMeasure U (ball x r') := h4 r' hr'_pos
        rw [h3] at h5 <;> simp at h5
      have h_pos : 0 < volume ((ball x r) \ U) :=
        (frontier_two_sided_positive_volume hU hU_reg hx_frontier hr_pos).2
      have h_r_lt_r' : r < r' := by
        have hr_le_R : r ≤ R := hr.2
        linarith [hr'_gt_R]
      have h_set_eq : V' ∩ ball x r = (ball x r) \ U := by
        ext y
        simp only [V', Uc, Set.mem_inter_iff, Set.mem_diff, Set.mem_compl_iff]
        constructor
        · rintro ⟨⟨hny, _⟩, hball2⟩
          exact ⟨hball2, hny⟩
        · rintro ⟨hball, hny⟩
          have hball1 : y ∈ ball x r' := ball_subset_ball (le_of_lt h_r_lt_r') hball
          exact ⟨⟨hny, hball1⟩, hball⟩
      have h_vol_pos : 0 < volume (V' ∩ ball x r) := by
        rw [h_set_eq]; exact h_pos
      have h_vol_lt_top : volume (V' ∩ ball x r) < ⊤ := by
        have h_sub : V' ∩ ball x r ⊆ ball x r := by simp
        exact (measure_mono h_sub).trans_lt measure_ball_lt_top
      exact ENNReal.toReal_pos_iff.mpr ⟨h_vol_pos, h_vol_lt_top⟩

    -- Integrate ODE
    let C_C := 3 * C_iso_real
    have hC_C_pos : 0 < C_C := by positivity
    have h_ode_C : ∀ r ∈ Set.Icc 0 R, m_C r ≥ (r / (C_C * (n : ℝ))) ^ n :=
      isoperimetric_differential_inequality (by linarith : 1 ≤ n) hC_C_pos hR_pos h_mono_C
        (fun r hr => by
          have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) R := ⟨by linarith, by linarith⟩
          have h_le : (0 : ℝ) ≤ r := (Set.mem_Icc.mp hr).1
          have h : m_C 0 ≤ m_C r := h_mono_C h0 hr h_le
          rw [h_m0_C] at h
          exact h)
        h_ac_C h_m0_C h_m_pos_C h_diff_ineq_C
    let c_C : ℝ := (1 / (C_C * (n : ℝ))) ^ n
    have hc_C_pos : 0 < c_C := by positivity
    have h_main_C : ∀ r, 0 < r → r < R → m_C r ≥ c_C * r ^ n := by
      intro r hr_pos hr_lt
      have hr_in : r ∈ Set.Icc 0 R := ⟨by linarith, by linarith⟩
      have h1 : m_C r ≥ (r / (C_C * (n : ℝ))) ^ n := h_ode_C r hr_in
      have h2 : (r / (C_C * (n : ℝ))) ^ n = c_C * r ^ n := by
        have h3 : (r / (C_C * (n : ℝ))) = (1 / (C_C * (n : ℝ))) * r := by ring
        rw [h3, mul_pow] <;> ring
      rw [h2] at h1
      exact h1
    refine ⟨c_C, hc_C_pos, fun r hr_pos hr_lt => ?_⟩
    have h4 : m_C r ≥ c_C * r ^ n := h_main_C r hr_pos hr_lt
    have h5 : 0 ≤ c_C * r ^ n := by positivity
    have h_set_eq : V' ∩ ball x r = (ball x r) \ U := h_eq_set r hr_pos hr_lt
    have h6 : volume (V' ∩ ball x r) = volume ((ball x r) \ U) := by rw [h_set_eq]
    have h7 : volume (V' ∩ ball x r) = ENNReal.ofReal (m_C r) := by
      have h8 : volume (V' ∩ ball x r) < ⊤ := by
        have h_sub : V' ∩ ball x r ⊆ ball x r := by simp
        exact (measure_mono h_sub).trans_lt measure_ball_lt_top
      rw [ENNReal.ofReal_toReal h8.ne]
    rw [h6] at h7
    have h9 : c_C * r ^ n ≤ m_C r := h4
    have h10 : ENNReal.ofReal (c_C * r ^ n) ≤ ENNReal.ofReal (m_C r) :=
      ENNReal.ofReal_le_ofReal h9
    have h11 : volume ((ball x r) \ U) = ENNReal.ofReal (m_C r) := by
      have h12 : volume (V' ∩ ball x r) = volume ((ball x r) \ U) := h6
      have h13 : volume (V' ∩ ball x r) = ENNReal.ofReal (m_C r) := by
        rw [h12, h7]
      rw [←h12, h13]
    rw [h11]
    exact h10

  rcases h_volume_U with ⟨c_U, hc_U_pos, h_volume_U⟩
  rcases h_compl with ⟨c_C, hc_C_pos, h_volume_C⟩
  let c := min c_U c_C
  have hc_pos : 0 < c := by positivity
  refine ⟨c, R, hc_pos, hR_pos, fun r hr_pos hr_lt => ?_⟩
  have h1 : c ≤ c_U := min_le_left _ _
  have h2 : c ≤ c_C := min_le_right _ _
  constructor
  · have h3 : c * r ^ n ≤ c_U * r ^ n := by gcongr <;> positivity
    exact le_trans (ENNReal.ofReal_le_ofReal h3) (h_volume_U r hr_pos hr_lt)
  · have h4 : c * r ^ n ≤ c_C * r ^ n := by gcongr <;> positivity
    exact le_trans (ENNReal.ofReal_le_ofReal h4) (h_volume_C r hr_pos hr_lt)

end Geometry.StructureTheorem
