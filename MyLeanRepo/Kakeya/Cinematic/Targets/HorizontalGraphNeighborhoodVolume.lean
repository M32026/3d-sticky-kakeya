import MyLeanRepo.Kakeya.Cinematic.Section5.LevelSetInputs
import MyLeanRepo.Kakeya.Cinematic.Section5.LocalAssembly.Infrastructure
import Mathlib.MeasureTheory.Measure.Prod

/-!
# Graph-neighborhood volume over a horizontal interval

This is the single-curve endpoint-stub estimate used in the short-curve
globalization after PYZ Lemma 39. The two endpoint intervals have horizontal
length `delta` and are handled by the trivial single-curve `O(delta^2)` area
bound. This target proves the general horizontal-length form.
-/

open MeasureTheory Set

namespace Kakeya.Cinematic

theorem horizontal_graphNeighborhood_volume :
    HorizontalGraphNeighborhoodVolumeStatement := by
  intro f delta L a b hdelta hab hsub hderiv
  let g : ℝ → ℝ := f.extension
  have hg_cont : Continuous g := f.extension_contDiff.continuous
  have hg_meas : Measurable g := hg_cont.measurable
  set c : ℝ := (1 + L) * delta with hc_def
  have hL_nonneg : 0 ≤ L := by
    have h1 : 0 ≤ |f.firstDeriv ⟨0, by simp [unitInterval]⟩| := abs_nonneg _
    have h2 : |f.firstDeriv ⟨0, by simp [unitInterval]⟩| ≤ L := hderiv _
    linarith
  have hc_nonneg : 0 ≤ c := by
    dsimp only [c]
    positivity
  set S : Set (ℝ × ℝ) :=
    graphNeighborhood f delta ∩ (Set.Icc a b ×ˢ (Set.univ : Set ℝ))
  set T : Set (ℝ × ℝ) :=
    {p | p.1 ∈ Set.Icc a b ∧ |p.2 - g p.1| ≤ c} with hT_def
  have hST : S ⊆ T := by
    intro p hp
    have h1 : p.1 ∈ Set.Icc a b := hp.2.1
    have h2 : p.1 ∈ unitInterval := hsub h1
    have h3 : p ∈ graphNeighborhood f delta := hp.1
    have h4 : |p.2 - f ⟨p.1, h2⟩| ≤ c :=
      localAssembly_graphNeighborhood_to_vertical hderiv h2 h3
    have h5 : g p.1 = f ⟨p.1, h2⟩ :=
      f.extension_eq_value ⟨p.1, h2⟩
    exact ⟨h1, by rw [h5]; exact h4⟩
  have hT_eq : T = (Set.Icc a b ×ˢ (Set.univ : Set ℝ)) ∩
      {p : ℝ × ℝ | |p.2 - g p.1| ≤ c} := by
    ext p
    simp [hT_def]
  have h1_meas : MeasurableSet (Set.Icc a b ×ˢ (Set.univ : Set ℝ)) :=
    measurableSet_Icc.prod MeasurableSet.univ
  have h2_meas : Measurable fun p : ℝ × ℝ => |p.2 - g p.1| := by
    fun_prop
  have h3_meas : MeasurableSet {p : ℝ × ℝ | |p.2 - g p.1| ≤ c} :=
    h2_meas measurableSet_Iic
  have hT_meas : MeasurableSet T := by
    rw [hT_eq]
    exact h1_meas.inter h3_meas
  have hvol_ST : volume S ≤ volume T := measure_mono hST
  have hvol_T : volume T ≤ ∫⁻ x : ℝ, volume (Prod.mk x ⁻¹' T) ∂volume := by
    rw [MeasureTheory.Measure.volume_eq_prod ℝ ℝ]
    exact MeasureTheory.Measure.prod_apply_le hT_meas
  have hfiber : ∀ x : ℝ, volume (Prod.mk x ⁻¹' T) =
      (Set.Icc a b).indicator (fun _ : ℝ => ENNReal.ofReal (2 * c)) x := by
    intro x
    by_cases hx : x ∈ Set.Icc a b
    · have h_fiber : Prod.mk x ⁻¹' T = Set.Icc (g x - c) (g x + c) := by
        ext y
        simp only [hT_def, Set.mem_preimage, Set.mem_setOf_eq, Set.mem_Icc]
        constructor
        · intro h
          have h6 : |y - g x| ≤ c := h.2
          have h7 : -c ≤ y - g x := (abs_le.mp h6).1
          have h8 : y - g x ≤ c := (abs_le.mp h6).2
          exact ⟨by linarith, by linarith⟩
        · intro h
          have h6 : -c ≤ y - g x := by linarith
          have h7 : y - g x ≤ c := by linarith
          have h8 : |y - g x| ≤ c := by
            rw [abs_le]
            exact ⟨h6, h7⟩
          exact ⟨hx, h8⟩
      rw [h_fiber, Real.volume_Icc]
      have h7 : (g x + c) - (g x - c) = 2 * c := by ring
      rw [h7, Set.indicator_of_mem hx]
    · have h_fiber : Prod.mk x ⁻¹' T = ∅ := by
        ext y
        simp only [hT_def, Set.mem_preimage, Set.mem_setOf_eq,
          Set.mem_empty_iff_false, iff_false]
        intro h
        exact hx h.1
      rw [h_fiber, measure_empty]
      have h_ind :
          (Set.Icc a b).indicator
              (fun _ : ℝ => ENNReal.ofReal (2 * c)) x = 0 := by
        rw [Set.indicator_apply, if_neg hx]
      rw [h_ind]
  set c' : ENNReal := ENNReal.ofReal (2 * c)
  have h_ind_eq : (Set.Icc a b).indicator (fun _ : ℝ => c') =
      fun x : ℝ =>
        c' * (Set.Icc a b).indicator (fun _ : ℝ => (1 : ENNReal)) x := by
    funext x
    by_cases hx : x ∈ Set.Icc a b
    · simp [hx]
    · simp [hx]
  have hlintegral :
      (∫⁻ x : ℝ, volume (Prod.mk x ⁻¹' T) ∂volume) =
        c' * volume (Set.Icc a b) := by
    rw [funext hfiber, h_ind_eq]
    rw [lintegral_const_mul c'
      (measurable_const.indicator measurableSet_Icc)]
    rw [lintegral_indicator measurableSet_Icc, setLIntegral_one]
  rw [hlintegral] at hvol_T
  have hvol_Icc : volume (Set.Icc a b) = ENNReal.ofReal (b - a) :=
    Real.volume_Icc
  rw [hvol_Icc] at hvol_T
  have h2c_nonneg : 0 ≤ 2 * c := by positivity
  have hfinal :
      ENNReal.ofReal (2 * c) * ENNReal.ofReal (b - a) =
        ENNReal.ofReal (2 * c * (b - a)) := by
    rw [ENNReal.ofReal_mul h2c_nonneg]
  rw [hfinal] at hvol_T
  have h9 : 2 * c = 2 * (1 + L) * delta := by
    simp [hc_def]
    ring
  rw [h9] at hvol_T
  exact hvol_ST.trans hvol_T

end Kakeya.Cinematic
