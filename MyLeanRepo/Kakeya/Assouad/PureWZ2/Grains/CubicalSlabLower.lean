import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains
import MyLeanRepo.Kakeya.Assouad.WZ1.Proposition3_2PaperStatements
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperGridCubeVolume
import MyLeanRepo.Kakeya.Assouad.PropStickyGridCubeBoxHelpers

set_option maxHeartbeats 500000
set_option maxRecDepth 1000

namespace Kakeya.Assouad

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

/-- Diameter bound for a literal paper grid cube: any two points in the same
cube are at distance at most `scale * Real.sqrt 3`. -/
lemma wz1PaperGridCube_diameter
    {scale : ℝ} (hscale : 0 < scale)
    (cell : ℤ × ℤ × ℤ)
    {x y : Point3}
    (hx : x ∈ wz1PaperGridCube scale cell)
    (hy : y ∈ wz1PaperGridCube scale cell) :
    dist x y ≤ scale * Real.sqrt 3 := by
  rw [wz1PaperGridCube_eq_Ico hscale cell] at hx hy
  have h4 : ∀ (j : Fin 3), |x j - y j| ≤ scale := by
    intro j
    fin_cases j
    · simp only [Set.mem_setOf_eq] at hx hy
      have h : |x 0 - y 0| ≤ scale := by
        rw [abs_sub_le_iff] <;> constructor <;> linarith
      exact h
    · simp only [Set.mem_setOf_eq] at hx hy
      have h : |x 1 - y 1| ≤ scale := by
        rw [abs_sub_le_iff] <;> constructor <;> linarith
      exact h
    · simp only [Set.mem_setOf_eq] at hx hy
      have h : |x 2 - y 2| ≤ scale := by
        rw [abs_sub_le_iff] <;> constructor <;> linarith
      exact h
  have h5 : ∑ j : Fin 3, (x j - y j) ^ 2 ≤ ∑ _j : Fin 3, scale ^ 2 := by
    apply Finset.sum_le_sum
    intro j _
    have h6 : |x j - y j| ≤ scale := h4 j
    have h7 : (x j - y j) ^ 2 ≤ scale ^ 2 := by
      calc (x j - y j) ^ 2 = |x j - y j| ^ 2 := by rw [sq_abs]
        _ ≤ scale ^ 2 := by gcongr
    exact h7
  have h_sum_nonneg : 0 ≤ ∑ j : Fin 3, (x j - y j) ^ 2 := by positivity
  have h_norm2 : ‖x - y‖ ^ 2 = ∑ j : Fin 3, (x j - y j) ^ 2 := by
    simp [EuclideanSpace.norm_eq] <;> exact Real.sq_sqrt h_sum_nonneg
  have h_dist : dist x y = ‖x - y‖ := by simp [dist_eq_norm]
  rw [h_dist]
  have h_pos : 0 ≤ ‖x - y‖ := by positivity
  have h_sqrt : ‖x - y‖ = Real.sqrt (‖x - y‖ ^ 2) := by
    rw [Real.sqrt_sq_eq_abs] <;> rw [abs_of_nonneg h_pos]
  rw [h_sqrt, h_norm2]
  have h7 : Real.sqrt (∑ j : Fin 3, (x j - y j) ^ 2) ≤ Real.sqrt (∑ _j : Fin 3, scale ^ 2) :=
    Real.sqrt_le_sqrt h5
  have h8 : (∑ _j : Fin 3, scale ^ 2) = 3 * scale ^ 2 := by
    simp [Finset.sum_const] <;> ring
  rw [h8] at h7
  have h9 : Real.sqrt (3 * scale ^ 2) = scale * Real.sqrt 3 := by
    have h10 : Real.sqrt (3 * scale ^ 2) = Real.sqrt 3 * Real.sqrt (scale ^ 2) := by
      rw [Real.sqrt_mul] <;> norm_num
    rw [h10]
    have h11 : Real.sqrt (scale ^ 2) = scale := by
      rw [Real.sqrt_sq_eq_abs] <;> rw [abs_of_pos hscale]
    rw [h11] <;> ring
  rw [h9] at h7
  exact h7

/-- Volume of any literal paper grid cube is `scale^3`. -/
lemma wz1PaperGridCube_volume_any
    {scale : ℝ} (hscale : 0 < scale)
    (cell : ℤ × ℤ × ℤ) :
    volume (wz1PaperGridCube scale cell) = ENNReal.ofReal (scale ^ 3) := by
  rw [wz1PaperGridCube_eq_Ico hscale cell]
  let cellCoord : Fin 3 → ℤ := fun j =>
    match j with
    | 0 => cell.1
    | 1 => cell.2.1
    | 2 => cell.2.2
  let raw : Set (Fin 3 → ℝ) := Set.pi Set.univ (fun j =>
    Set.Ico ((cellCoord j : ℝ) * scale) (((cellCoord j : ℝ) + 1) * scale))
  let toLp : (Fin 3 → ℝ) → Point3 := WithLp.toLp 2
  have hset : {p : Point3 | (cell.1 : ℝ) * scale ≤ p 0 ∧ p 0 < ((cell.1 : ℝ) + 1) * scale ∧
      (cell.2.1 : ℝ) * scale ≤ p 1 ∧ p 1 < ((cell.2.1 : ℝ) + 1) * scale ∧
      (cell.2.2 : ℝ) * scale ≤ p 2 ∧ p 2 < ((cell.2.2 : ℝ) + 1) * scale} =
      toLp '' raw := by
    ext point
    constructor
    · rintro ⟨h0Lower, h0Upper, h1Lower, h1Upper, h2Lower, h2Upper⟩
      refine ⟨point.ofLp, ?_, by simp [toLp]⟩
      intro coordinate _
      fin_cases coordinate <;> simp [cellCoord, *] <;> omega
    · rintro ⟨point, hpoint, rfl⟩
      have h0 := hpoint 0 (Set.mem_univ _)
      have h1 := hpoint 1 (Set.mem_univ _)
      have h2 := hpoint 2 (Set.mem_univ _)
      simpa [cellCoord] using ⟨h0.1, h0.2, h1.1, h1.2, h2.1, h2.2⟩
  rw [hset]
  have hPreserving : MeasurePreserving toLp := PiLp.volume_preserving_toLp (ι := Fin 3)
  have hInjective : Function.Injective toLp := by
    intro first second h
    exact WithLp.toLp_injective 2 h
  have hMeasurable : Measurable toLp := (PiLp.continuous_toLp (p := 2) (β := fun _ : Fin 3 => ℝ)).measurable
  have hRawMeasurable : MeasurableSet raw :=
    MeasurableSet.pi Set.countable_univ (fun _ _ => measurableSet_Ico)
  have hImageMeasurable : MeasurableSet (toLp '' raw) := by
    have hImage : toLp '' raw = (fun point : Point3 => point.ofLp) ⁻¹' raw := by
      ext point
      constructor
      · rintro ⟨source, hsource, rfl⟩
        simpa [toLp] using hsource
      · intro hpoint
        exact ⟨point.ofLp, hpoint, by simp [toLp]⟩
    rw [hImage]
    exact (PiLp.continuous_ofLp (p := 2) (β := fun _ : Fin 3 => ℝ)).measurable hRawMeasurable
  have hVolume : volume (toLp '' raw) = volume raw := by
    calc
      volume (toLp '' raw)
        = Measure.map toLp volume (toLp '' raw) := by rw [hPreserving.map_eq]
      _ = volume (toLp ⁻¹' (toLp '' raw)) := Measure.map_apply hMeasurable hImageMeasurable
      _ = volume raw := by rw [Set.preimage_image_eq raw hInjective]
  rw [hVolume]
  have hRawVol : volume raw = ∏ i : Fin 3, ENNReal.ofReal (scale) := by
    have h : volume raw = ∏ i : Fin 3, ENNReal.ofReal ((((cellCoord i : ℝ) + 1) * scale) - ((cellCoord i : ℝ) * scale)) :=
      Real.volume_pi_Ico (ι := Fin 3)
    rw [h]
    apply Finset.prod_congr rfl
    intro i _
    have h5 : (((cellCoord i : ℝ) + 1) * scale) - ((cellCoord i : ℝ) * scale) = scale := by ring
    rw [h5]
  rw [hRawVol]
  rw [Fin.prod_univ_three]
  rw [← ENNReal.ofReal_mul hscale.le]
  rw [← ENNReal.ofReal_mul (mul_nonneg hscale.le hscale.le)]
  congr 1 <;> ring

/-- Slab lower bound from a cubical shading.

For any `t` in the scalar projection of the shading union onto a unit direction `v`,
the slab `{x | |inner(x,v) - t| ≤ scale * Real.sqrt 3}` contains at least one full
grid cube, hence has volume at least `scale^3`. -/
lemma cubical_slab_lower_bound
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    (hcubical : WZ1PaperIsCubicalShading shading)
    (v : Point3)
    (hv_unit : ‖v‖ = 1)
    (hdelta_pos : 0 < delta)
    (t : ℝ)
    (ht : t ∈ scalarProjection v shading.union) :
    volume (shading.union ∩ {x | |inner ℝ x v - t| ≤ delta * Real.sqrt 3}) ≥
      ENNReal.ofReal (delta ^ 3) := by
  rcases ht with ⟨x, hx, h_eq_t⟩
  rcases hx with ⟨i, hxi⟩
  let cell := wz1PaperGridIndex delta x
  let C := wz1PaperGridCube delta cell
  have hx_in_C : x ∈ C := by
    simpa [C, cell, mem_wz1PaperGridCube] using rfl
  have hC_sub : C ⊆ shading.carrier i := hcubical i x hxi
  have hC_sub_union : C ⊆ shading.union := by
    intro y hy
    exact ⟨i, hC_sub hy⟩
  have hC_slab : C ⊆ {z | |inner ℝ z v - t| ≤ delta * Real.sqrt 3} := by
    intro y hy
    have hdist : dist y x ≤ delta * Real.sqrt 3 :=
      wz1PaperGridCube_diameter hdelta_pos cell hy hx_in_C
    have h1 : inner ℝ y v - t = inner ℝ (y - x) v := by
      have h2 : t = inner ℝ x v := h_eq_t.symm
      rw [h2]
      simp [inner_sub_left] <;> abel
    have h3 : |inner ℝ y v - t| ≤ ‖y - x‖ := by
      rw [h1]
      have h4 : |inner ℝ (y - x) v| ≤ ‖y - x‖ * ‖v‖ := abs_real_inner_le_norm _ _
      rw [hv_unit] at h4
      simpa using h4
    have h5 : ‖y - x‖ = dist y x := by simp [dist_eq_norm]
    rw [h5] at h3
    exact le_trans h3 hdist
  have hC_inter : C ⊆ shading.union ∩ {z | |inner ℝ z v - t| ≤ delta * Real.sqrt 3} := by
    intro y hy
    exact ⟨hC_sub_union hy, hC_slab hy⟩
  have hvol : volume C = ENNReal.ofReal (delta ^ 3) :=
    wz1PaperGridCube_volume_any hdelta_pos cell
  calc volume (shading.union ∩ {z | |inner ℝ z v - t| ≤ delta * Real.sqrt 3})
      ≥ volume C := measure_mono hC_inter
    _ = ENNReal.ofReal (delta ^ 3) := hvol

end Kakeya.Assouad
