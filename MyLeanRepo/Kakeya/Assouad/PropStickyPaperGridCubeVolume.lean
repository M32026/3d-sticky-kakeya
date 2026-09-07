import MyLeanRepo.Kakeya.Assouad.PropStickyGridCubeBoxHelpers

/-!
# Exact volume of a literal paper grid cube
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

theorem wz1PaperGridCube_volume_exact
    {scale : ℝ} (hscale : 0 < scale) :
    volume (wz1PaperGridCube scale (0, 0, 0)) =
      ENNReal.ofReal (scale ^ 3) := by
  let raw : Set (Fin 3 → ℝ) :=
    Set.pi Set.univ (fun _ => Set.Ico 0 scale)
  let toLp : (Fin 3 → ℝ) → Point3 := WithLp.toLp 2
  have hset :
      wz1PaperGridCube scale (0, 0, 0) = toLp '' raw := by
    rw [wz1PaperGridCube_eq_Ico hscale]
    ext point
    constructor
    · rintro ⟨h0Lower, h0Upper, h1Lower, h1Upper,
        h2Lower, h2Upper⟩
      norm_num at h0Lower h0Upper h1Lower h1Upper h2Lower h2Upper
      refine ⟨point.ofLp, ?_, by simp [toLp]⟩
      intro coordinate _
      fin_cases coordinate
      · exact ⟨h0Lower, h0Upper⟩
      · exact ⟨h1Lower, h1Upper⟩
      · exact ⟨h2Lower, h2Upper⟩
    · rintro ⟨point, hpoint, rfl⟩
      have h0 := hpoint 0 (Set.mem_univ _)
      have h1 := hpoint 1 (Set.mem_univ _)
      have h2 := hpoint 2 (Set.mem_univ _)
      norm_num at h0 h1 h2 ⊢
      exact ⟨h0.1, h0.2, h1.1, h1.2, h2.1, h2.2⟩
  rw [hset]
  have hPreserving : MeasurePreserving toLp :=
    PiLp.volume_preserving_toLp (ι := Fin 3)
  have hInjective : Function.Injective toLp := by
    intro first second h
    exact WithLp.toLp_injective 2 h
  have hMeasurable : Measurable toLp :=
    (PiLp.continuous_toLp
      (p := 2) (β := fun _ : Fin 3 => ℝ)).measurable
  have hRawMeasurable : MeasurableSet raw :=
    MeasurableSet.pi Set.countable_univ
      (fun _ _ => measurableSet_Ico)
  have hImageMeasurable : MeasurableSet (toLp '' raw) := by
    have hImage :
        toLp '' raw = (fun point : Point3 => point.ofLp) ⁻¹' raw := by
      ext point
      constructor
      · rintro ⟨source, hsource, rfl⟩
        simpa [toLp] using hsource
      · intro hpoint
        exact ⟨point.ofLp, hpoint, by simp [toLp]⟩
    rw [hImage]
    exact
      (PiLp.continuous_ofLp
        (p := 2) (β := fun _ : Fin 3 => ℝ)).measurable
          hRawMeasurable
  have hVolume : volume (toLp '' raw) = volume raw := by
    calc
      volume (toLp '' raw) =
          Measure.map toLp volume (toLp '' raw) := by
        rw [hPreserving.map_eq]
      _ = volume (toLp ⁻¹' (toLp '' raw)) :=
        Measure.map_apply hMeasurable hImageMeasurable
      _ = volume raw := by
        rw [Set.preimage_image_eq raw hInjective]
  rw [hVolume]
  rw [show
    volume raw =
      ∏ _coordinate : Fin 3, ENNReal.ofReal (scale - 0) by
        exact Real.volume_pi_Ico]
  rw [Fin.prod_univ_three]
  simp only [sub_zero]
  rw [← ENNReal.ofReal_mul hscale.le]
  rw [← ENNReal.ofReal_mul
    (mul_nonneg hscale.le hscale.le)]
  congr 1
  ring

end Kakeya.Assouad

end
