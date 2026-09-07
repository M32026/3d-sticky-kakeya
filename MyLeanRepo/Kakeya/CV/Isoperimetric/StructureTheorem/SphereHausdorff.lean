import MyLeanRepo.Kakeya.CV.Isoperimetric.Measure.Eilenberg
import MyLeanRepo.Kakeya.CV.Isoperimetric.Coarea.DistanceCoareaAEMeasurable
import MyLeanRepo.Kakeya.CV.Isoperimetric.InnerMinkowski.Basic
import Mathlib.Tactic


open MeasureTheory Metric Set ENNReal Filter
open scoped MeasureTheory

namespace Geometry.StructureTheorem

variable {n : ℕ}

/-- Finiteness of unit sphere Hausdorff measure: `μHE[n-1](sphere 0 1) < ⊤` for `n ≥ 2`. -/
lemma unit_sphere_hausdorff_finite (hn : 2 ≤ n) :
    μHE[n - 1] (sphere (0 : E n) 1) < ⊤ := by
  haveI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp (by linarith)
  let f : E n → ℝ := fun x => dist x (0 : E n)
  have hf : LipschitzWith (1 : NNReal) f := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    have h : |f x - f y| ≤ dist x y := abs_dist_sub_le x y (0 : E n)
    have h' : dist (f x) (f y) ≤ dist x y := by
      rw [Real.dist_eq] <;> exact h
    simpa [NNReal.coe_one, one_mul] using h'
  rcases eilenberg_μHE hn hf (by simp) with ⟨C, hC_ne_top, _, h_main⟩
  let A : Set (E n) := ball (0 : E n) 2
  have hC_lt_top : C < ⊤ := lt_top_iff_ne_top.mpr hC_ne_top
  have hA_vol : volume A < ⊤ := by
    haveI : ProperSpace (E n) := by exact FiniteDimensional.proper_real (E n)
    exact measure_ball_lt_top
  have h_mul_lt : C * volume A < ⊤ := mul_lt_top hC_lt_top hA_vol
  have h_mainA : (∫⁻ (s : ℝ), μHE[n - 1] (A ∩ f ⁻¹' {s})) ≤ C * volume A := h_main A
  have h_int_lt_top : (∫⁻ (s : ℝ), μHE[n - 1] (A ∩ f ⁻¹' {s})) < ⊤ :=
    h_mainA.trans_lt h_mul_lt
  let g : ℝ → ENNReal := fun s => μHE[n - 1] (A ∩ f ⁻¹' {s})
  have h_flm : FunctionLevelMeasurable f := point_distance_level_measurable hn (0 : E n)
  have h_g_ae_Ioc : AEMeasurable g (volume.restrict (Set.Ioc (0 : ℝ) 2)) :=
    h_flm A isOpen_ball.measurableSet 0 2
  have h_sub : Set.Ioo (0 : ℝ) 2 ⊆ Set.Ioc (0 : ℝ) 2 := by
    intro x hx
    exact ⟨hx.1, hx.2.le⟩
  have h_g_ae : AEMeasurable g (volume.restrict (Set.Ioo (0 : ℝ) 2)) := by
    exact h_g_ae_Ioc.mono_measure (Measure.restrict_mono h_sub le_rfl)
  have h_int_Ioo_le : (∫⁻ s in Set.Ioo (0 : ℝ) 2, g s) ≤ (∫⁻ (s : ℝ), g s) :=
    MeasureTheory.setLIntegral_le_lintegral (Set.Ioo (0 : ℝ) 2) g
  have h_int_Ioo_ne_top : (∫⁻ s in Set.Ioo (0 : ℝ) 2, g s) ≠ ⊤ :=
    ne_top_of_le_ne_top h_int_lt_top.ne h_int_Ioo_le
  have h_ae : ∀ᵐ (s : ℝ) ∂volume.restrict (Set.Ioo (0 : ℝ) 2), g s < ⊤ :=
    MeasureTheory.ae_lt_top' h_g_ae h_int_Ioo_ne_top
  have h_vol_pos : 0 < volume (Set.Ioo (0 : ℝ) 2) := by
    rw [Real.volume_Ioo] <;> norm_num
  have h_exists : ∃ (s : ℝ), s ∈ Set.Ioo (0 : ℝ) 2 ∧ g s < ⊤ :=
    Measure.exists_mem_of_measure_ne_zero_of_ae h_vol_pos.ne' h_ae
  rcases h_exists with ⟨s, hs_in, hs_finite⟩
  have hs_pos : 0 < s := hs_in.1
  have h_sphere_eq : A ∩ f ⁻¹' {s} = sphere (0 : E n) s := by
    ext y
    simp only [A, f, Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff,
      Metric.mem_sphere, dist_zero_right]
    <;> constructor <;> intro h <;> aesop <;> linarith [hs_in.2]
  have h_gs : g s = μHE[n - 1] (sphere (0 : E n) s) := by
    dsimp only [g]
    rw [h_sphere_eq]
  rw [h_gs] at hs_finite
  have h_scale : μHE[n - 1] (sphere (0 : E n) s) =
      ENNReal.ofReal (s ^ (n - 1)) * μHE[n - 1] (sphere (0 : E n) 1) := by
    have h1 : sphere (0 : E n) s = AffineMap.homothety (0 : E n) s '' sphere (0 : E n) 1 := by
      ext y
      simp only [sphere, Set.mem_image, Metric.mem_sphere]
      constructor
      · intro hy
        refine ⟨(1 / s) • y, ?_, ?_⟩
        · have h_norm_y : ‖y‖ = s := by simpa [dist_zero_right] using hy
          have h : dist ((1 / s) • y) (0 : E n) = 1 := by
            rw [dist_zero_right, norm_smul, Real.norm_eq_abs,
              abs_of_pos (show 0 < 1 / s by positivity), h_norm_y]
            <;> field_simp [hs_pos.ne'] <;> ring
          exact h
        · simp [AffineMap.homothety_apply, hs_pos.ne'] <;> abel
      · rintro ⟨z, hz, rfl⟩
        have h_norm_z : ‖z‖ = 1 := by simpa [dist_zero_right] using hz
        have h : dist (AffineMap.homothety (0 : E n) s z) (0 : E n) = s := by
          have h9 : AffineMap.homothety (0 : E n) s z = s • z := by
            simp [AffineMap.homothety_apply]
          rw [h9, dist_zero_right, norm_smul, Real.norm_eq_abs,
            abs_of_pos hs_pos, h_norm_z] <;> ring
        exact h
    rw [h1]
    have h2 := MeasureTheory.euclideanHausdorffMeasure_homothety_image (n - 1) (0 : E n) hs_pos.ne' (sphere (0 : E n) 1)
    have h_scale2 : (↑‖s‖₊ : ENNReal) ^ (n - 1) = ENNReal.ofReal (s ^ (n - 1)) := by
      have h7 : (↑‖s‖₊ : ENNReal) = ENNReal.ofReal s := by
        have h71 : (‖s‖₊ : ℝ) = s := by
          have h_abs : (‖s‖₊ : ℝ) = |s| := by exact Real.ext_cauchy rfl
          rw [h_abs, abs_of_pos hs_pos]
        have h72 : (↑‖s‖₊ : ENNReal) = ENNReal.ofReal (↑‖s‖₊ : ℝ) := by exact coe_nnreal_eq ‖s‖₊
        rw [h72, h71]
      rw [h7, ← ENNReal.ofReal_pow]
      <;> positivity
    have h_smul : (‖s‖₊ ^ (n - 1)) • μHE[n - 1] (sphere (0 : E n) 1) =
        (↑‖s‖₊ : ENNReal) ^ (n - 1) * μHE[n - 1] (sphere (0 : E n) 1) := by
      have h9 : (‖s‖₊ ^ (n - 1)) • μHE[n - 1] (sphere (0 : E n) 1) =
          (↑(‖s‖₊ ^ (n - 1)) : ENNReal) * μHE[n - 1] (sphere (0 : E n) 1) := by exact Measure.nnreal_smul_coe_apply (‖s‖₊ ^ (n - 1)) μHE[n - 1] (sphere 0 1)
      have h10 : (↑(‖s‖₊ ^ (n - 1)) : ENNReal) = (↑‖s‖₊ : ENNReal) ^ (n - 1) := by exact coe_pow ‖s‖₊ (n - 1)
      rw [h9, h10]
    rw [h2, h_smul, h_scale2]
  rw [h_scale] at hs_finite
  have h_s_pos' : ENNReal.ofReal (s ^ (n - 1)) ≠ 0 := by
    positivity
  have h_main : μHE[n - 1] (sphere (0 : E n) 1) < ⊤ := by
    have h : (ENNReal.ofReal (s ^ (n - 1)) < ⊤ ∧ μHE[n - 1] (sphere (0 : E n) 1) < ⊤) ∨
        ENNReal.ofReal (s ^ (n - 1)) = 0 ∨ μHE[n - 1] (sphere (0 : E n) 1) = 0 :=
      ENNReal.mul_lt_top_iff.mp hs_finite
    rcases h with (h | h | h)
    · exact h.2
    · exfalso; exact h_s_pos' h
    · rw [h]; exact bot_lt_top
  exact h_main

/-- Sphere Hausdorff measure scaling: `μHE[n-1](sphere x r) = r^(n-1) · μHE[n-1](sphere 0 1)`. -/
lemma sphere_hausdorff_scale (x : E n) {r : ℝ} (hr : 0 < r) :
    μHE[n - 1] (sphere x r) =
    ENNReal.ofReal (r ^ (n - 1)) * μHE[n - 1] (sphere (0 : E n) 1) := by
  have h1 : sphere x r = AffineMap.homothety x r '' sphere x 1 := by
    ext y
    simp only [sphere, Set.mem_image, Metric.mem_sphere, AffineMap.homothety_apply]
    constructor
    · intro hy
      let z : E n := x + (1 / r) • (y - x)
      have hz1 : dist z x = 1 := by
        have h2 : z - x = (1 / r) • (y - x) := by simp [z] <;> abel
        rw [dist_eq_norm, h2, norm_smul]
        have h3 : ‖y - x‖ = r := by simpa [dist_eq_norm] using hy
        rw [h3]
        have h4 : ‖(1 / r : ℝ)‖ = 1 / r := by
          rw [Real.norm_eq_abs, abs_of_pos] <;> positivity
        rw [h4] <;> field_simp [hr.ne'] <;> ring
      have hz2 : x + r • (z - x) = y := by
        have h4 : z - x = (1 / r) • (y - x) := by simp [z] <;> abel
        rw [h4, smul_smul]
        have h5 : r * (1 / r) = 1 := by field_simp [hr.ne']
        rw [h5, one_smul] <;> abel
      have hz2' : r • (z -ᵥ x) +ᵥ x = y := by
        have h5 : r • (z -ᵥ x) +ᵥ x = x + r • (z - x) := by
          simp [vadd_eq_add] <;> abel
        rw [h5, hz2]
      exact ⟨z, hz1, hz2'⟩
    · rintro ⟨z, hz, rfl⟩
      have h5 : ‖z - x‖ = 1 := by simpa [dist_eq_norm] using hz
      have h_eq : r • (z -ᵥ x) +ᵥ x = x + r • (z - x) := by
        simp [vadd_eq_add] <;> abel
      rw [h_eq]
      have h : dist (x + r • (z - x)) x = r := by
        have h6 : ‖x + r • (z - x) - x‖ = ‖r • (z - x)‖ := by abel_nf
        rw [dist_eq_norm, h6, norm_smul, Real.norm_eq_abs, abs_of_pos hr, h5] <;> ring
      exact h
  rw [h1]
  have h2 := MeasureTheory.euclideanHausdorffMeasure_homothety_image (n - 1) x hr.ne' (sphere x 1)
  let f : E n → E n := fun y => y - x
  have hf_isom : Isometry f := by
    intro a b
    have h_dist : dist (f a) (f b) = dist a b := by
      simp only [f, dist_eq_norm]
      have h2 : (a - x) - (b - x) = a - b := by abel
      rw [h2]
    simpa [edist_dist] using congr_arg ENNReal.ofReal h_dist
  have h3 : f '' sphere x 1 = sphere (0 : E n) 1 := by
    ext z
    simp only [Set.mem_image, sphere, Metric.mem_sphere]
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa [f, dist_eq_norm] using hy
    · intro hz
      refine ⟨z + x, ?_, by simp [f] <;> abel⟩
      simpa [dist_eq_norm] using hz
  have h4 : μHE[n - 1] (sphere x 1) = μHE[n - 1] (sphere (0 : E n) 1) := by
    have h5 : μHE[n - 1] (f '' sphere x 1) = μHE[n - 1] (sphere x 1) :=
      hf_isom.euclideanHausdorffMeasure_image (sphere x 1)
    rw [h3] at h5
    exact h5.symm
  have h6 : (‖r‖₊ : ENNReal) ^ (n - 1) = ENNReal.ofReal (r ^ (n - 1)) := by
    have h7 : (↑‖r‖₊ : ENNReal) = ENNReal.ofReal r := by
      have h71 : (‖r‖₊ : ℝ) = r := by
        have h_abs : (‖r‖₊ : ℝ) = |r| := by exact Real.ext_cauchy rfl
        rw [h_abs, abs_of_pos hr]
      have h72 : (↑‖r‖₊ : ENNReal) = ENNReal.ofReal (↑‖r‖₊ : ℝ) := by exact coe_nnreal_eq ‖r‖₊
      rw [h72, h71]
    rw [h7, ← ENNReal.ofReal_pow] <;> positivity
  rw [h2]
  have h8 : (‖r‖₊ ^ (n - 1)) • μHE[n - 1] (sphere x 1) =
      (‖r‖₊ : ENNReal) ^ (n - 1) * μHE[n - 1] (sphere x 1) := by rfl
  rw [h8, h6, h4]

/-- For a finite measure μ on E n, μ(sphere x r) = 0 for a.e. r > 0. -/
lemma sphere_measure_null_ae {μ : Measure (E n)} [IsFiniteMeasure μ] (x : E n) :
    ∀ᵐ (r : ℝ) ∂volume.restrict (Set.Ioi 0), μ (sphere x r) = 0 := by
  have h_univ_lt_top : μ Set.univ < ⊤ := by (expose_names; exact (isFiniteMeasure_iff μ).mp inst)
  have h1 : ∀ (k : ℕ), Set.Finite {r : ℝ | 0 < r ∧ μ (sphere x r) > 1 / (k + 1 : ENNReal)} := by
    intro k
    by_contra h
    let S := {r : ℝ | 0 < r ∧ μ (sphere x r) > 1 / (k + 1 : ENNReal)}
    have h2 : Set.Infinite S := by exact Set.not_finite.mp h
    let g : ℕ ↪ ↑S := Set.Infinite.natEmbedding S h2
    let f : ℕ → ℝ := fun n => (g n : ℝ)
    have hf_inj : Function.Injective f := by
      intro n m h; exact g.inj' (Subtype.ext h)
    have hf_sub : ∀ n, f n ∈ S := fun n => (g n).property
    have h3 : ∀ (i j : ℕ), i ≠ j → Disjoint (sphere x (f i)) (sphere x (f j)) := by
      intro i j hne
      rw [Set.disjoint_left]; intro y hy1 hy2
      have h4 : dist y x = f i := hy1
      have h5 : dist y x = f j := hy2
      have h6 : f i = f j := by rw [←h4, h5]
      exact hne (hf_inj h6)
    have h_meas : ∀ i : ℕ, MeasurableSet (sphere x (f i)) :=
      fun i => (Metric.isClosed_sphere (x := x) (ε := f i)).measurableSet
    have h4 : μ (⋃ n : ℕ, sphere x (f n)) = ∑' n : ℕ, μ (sphere x (f n)) := by
      have h_pair : Pairwise (fun (i j : ℕ) => Disjoint (sphere x (f i)) (sphere x (f j))) :=
        fun {i j} hne => h3 i j hne
      let f' : ℕ → Set (E n) := fun n => sphere x (f n)
      have h_pair' : Pairwise (Function.onFun Disjoint f') := h_pair
      exact MeasureTheory.measure_iUnion (f := f') h_pair' h_meas
    have h_pos_elem : ∀ n : ℕ, (1 : ENNReal) / (k + 1) ≤ μ (sphere x (f n)) :=
      fun n => le_of_lt ((hf_sub n).2)
    have h6 : ∑' n : ℕ, (1 : ENNReal) / (k + 1) = ⊤ := by
      have h_ne_zero : (1 : ENNReal) / (k + 1 : ENNReal) ≠ 0 := by
        intro h
        have h10 : (1 : ENNReal) = 0 := by
          simpa [div_eq_mul_inv] using h
        simpa using h10
      have h_pos : (0 : ENNReal) < (1 : ENNReal) / (k + 1 : ENNReal) :=
        bot_lt_iff_ne_bot.mpr h_ne_zero
      have h : ∑' (_ : ℕ), (1 : ENNReal) / (k + 1) = ⊤ := by
        rw [ENNReal.tsum_const]
        <;> simp [h_pos.ne']
      exact h
    have h7 : ⊤ ≤ ∑' n : ℕ, μ (sphere x (f n)) := by
      rw [←h6]
      exact ENNReal.tsum_le_tsum h_pos_elem
    have h5 : ∑' n : ℕ, μ (sphere x (f n)) = ⊤ := le_antisymm le_top h7
    have h9 : μ (⋃ n : ℕ, sphere x (f n)) = ⊤ := by
      rw [h4, h5]
    have h11 : μ (⋃ n : ℕ, sphere x (f n)) ≤ μ Set.univ := measure_mono (Set.subset_univ _)
    rw [h9] at h11
    have h_cont : False := by
      have h12 : μ Set.univ = ⊤ := by simpa using h11
      rw [h12] at h_univ_lt_top
      simpa using h_univ_lt_top
    exact h_cont
  have h_arch : ∀ (x : ENNReal), 0 < x → ∃ (k : ℕ), (1 : ENNReal) / (k + 1) < x := by
    intro x hx
    by_cases h_top : x = ⊤
    · exact ⟨0, by rw [h_top]; simp⟩
    · have h_ne_top : x ≠ ⊤ := h_top
      have h_x_ne_zero : x ≠ 0 := hx.ne'
      have h_x_inv_ne_top : x⁻¹ ≠ ⊤ := by
        simp [h_ne_top, ENNReal.inv_eq_top, h_x_ne_zero]
      have h_x_inv_pos : 0 < x⁻¹ := by
        rw [ENNReal.inv_pos] <;> exact h_ne_top
      obtain ⟨k, hk⟩ := exists_nat_gt x⁻¹.toReal
      have hk_pos : 0 < k := by
        by_contra h
        rw [Nat.eq_zero_of_not_pos h] at hk
        have h' : x⁻¹.toReal < 0 := by exact_mod_cast hk
        have h'' : 0 ≤ x⁻¹.toReal := by positivity
        linarith
      have h_eq_inv : x⁻¹ = ENNReal.ofReal x⁻¹.toReal := (ENNReal.ofReal_toReal h_x_inv_ne_top).symm
      have h_nonneg : 0 ≤ x⁻¹.toReal := by positivity
      have h_k_ennreal : x⁻¹ < (k : ENNReal) := by
        rw [h_eq_inv]
        have h_k_ofReal : (k : ENNReal) = ENNReal.ofReal (k : ℝ) := by norm_cast
        rw [h_k_ofReal]
        exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg h_nonneg).mpr hk
      have h_k_ne_zero : (k : ENNReal) ≠ 0 := by exact_mod_cast hk_pos.ne'
      have h_k_inv : (k : ENNReal)⁻¹ < x :=
        inv_lt_iff_inv_lt.mp h_k_ennreal
      have h4 : (1 : ENNReal) / (k + 1) < (k : ENNReal)⁻¹ := by
        have h5 : (k : ENNReal) < (k + 1 : ENNReal) := by norm_cast <;> omega
        have h6 : (k + 1 : ENNReal)⁻¹ < (k : ENNReal)⁻¹ := by
          rw [ENNReal.inv_lt_inv] <;> exact h5
        have h7 : (1 : ENNReal) / (k + 1) = (k + 1 : ENNReal)⁻¹ := by
          simp [div_eq_mul_inv]
        rw [h7]
        exact h6
      exact ⟨k, h4.trans h_k_inv⟩
  have h2 : Set.Countable {r : ℝ | 0 < r ∧ μ (sphere x r) > 0} := by
    have h3 : {r : ℝ | 0 < r ∧ μ (sphere x r) > 0} =
        ⋃ k : ℕ, {r : ℝ | 0 < r ∧ μ (sphere x r) > 1 / (k + 1 : ENNReal)} := by
      ext r
      simp only [Set.mem_iUnion, Set.mem_setOf_eq]
      constructor
      · intro h
        have h4 : (0 : ENNReal) < μ (sphere x r) := h.2
        have h5 : ∃ (k : ℕ), (1 : ENNReal) / (k + 1) < μ (sphere x r) := h_arch (μ (sphere x r)) h4
        rcases h5 with ⟨k, hk⟩
        exact ⟨k, h.1, hk⟩
      · rintro ⟨k, h1, h2⟩
        have h_pos : (0 : ENNReal) < 1 / (k + 1 : ENNReal) := by
          apply bot_lt_iff_ne_bot.mpr
          intro h
          have h3 : (1 : ENNReal) = 0 := by
            rw [div_eq_mul_inv] at h
            simpa using h
          simpa using h3
        exact ⟨h1, h_pos.trans h2⟩
    rw [h3]
    exact Set.countable_iUnion (fun k => (h1 k).countable)
  have h_set_eq : {r : ℝ | 0 < r ∧ μ (sphere x r) > 0} = {r : ℝ | 0 < r ∧ μ (sphere x r) ≠ 0} := by
    ext r
    simp only [Set.mem_setOf_eq]
    have h_iff : (0 : ENNReal) < μ (sphere x r) ↔ μ (sphere x r) ≠ 0 := by
      exact bot_lt_iff_ne_bot
    tauto
  have h3 : volume {r : ℝ | 0 < r ∧ μ (sphere x r) ≠ 0} = 0 := by
    rw [←h_set_eq]
    exact h2.measure_zero volume
  have h4 : ∀ᵐ (r : ℝ) ∂volume, ¬(0 < r ∧ μ (sphere x r) ≠ 0) := by
    simpa [ae_iff] using h3
  rw [ae_restrict_iff' isOpen_Ioi.measurableSet]
  filter_upwards [h4] with r h5
  intro hr_pos
  have h6 : ¬(0 < r ∧ μ (sphere x r) ≠ 0) := h5
  have h7 : μ (sphere x r) = 0 := by
    by_contra h8
    exact h6 ⟨hr_pos, h8⟩
  exact h7

end Geometry.StructureTheorem
