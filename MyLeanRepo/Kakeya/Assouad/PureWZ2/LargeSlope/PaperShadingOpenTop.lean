import MyLeanRepo.Kakeya.Assouad.WZ1.Proposition3_2PaperInfrastructure
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Removing the null top face of a paper shading

The Proposition 6.5 affine map sends the selected closed height interval to
the closed target window.  Removing the source top face loses no volume and
makes the target height interval half-open, which is compatible with the
fixed-origin half-open grid cubes used by the induced cubical shading.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

theorem volume_coordinate_hyperplane_zero
    (coordinate : Fin 3) (value : ℝ) :
    volume {point : Point3 | point coordinate = value} = 0 := by
  let raw : Set (Fin 3 → ℝ) :=
    {point | point coordinate = value}
  let toLp : (Fin 3 → ℝ) → Point3 := WithLp.toLp 2
  have hraw : volume raw = 0 := by
    rw [MeasureTheory.volume_pi]
    exact MeasureTheory.Measure.pi_hyperplane
      (fun _ : Fin 3 => (volume : Measure ℝ)) coordinate value
  have hset : {point : Point3 | point coordinate = value} =
      toLp '' raw := by
    ext point
    constructor
    · intro hpoint
      refine ⟨point.ofLp, ?_, by simp [toLp]⟩
      simpa [raw] using hpoint
    · rintro ⟨point, hpoint, rfl⟩
      simpa [toLp, raw] using hpoint
  rw [hset]
  have hpreserving : MeasurePreserving toLp :=
    PiLp.volume_preserving_toLp (Fin 3)
  have hinjective : Function.Injective toLp :=
    WithLp.toLp_injective 2
  have hmeasurable : Measurable toLp :=
    (PiLp.continuous_toLp
      (p := 2) (β := fun _ : Fin 3 => ℝ)).measurable
  have hrawMeasurable : MeasurableSet raw := by
    exact measurableSet_singleton value |>.preimage
      (measurable_pi_apply coordinate)
  have himageMeasurable : MeasurableSet (toLp '' raw) := by
    have heq : toLp '' raw =
        (fun point : Point3 => point.ofLp) ⁻¹' raw := by
      ext point
      constructor
      · rintro ⟨source, hsource, rfl⟩
        simpa [toLp] using hsource
      · intro hpoint
        exact ⟨point.ofLp, hpoint, by simp [toLp]⟩
    rw [heq]
    exact hrawMeasurable.preimage
      ((PiLp.continuous_ofLp
        (p := 2) (β := fun _ : Fin 3 => ℝ)).measurable)
  calc
    volume (toLp '' raw) =
        Measure.map toLp volume (toLp '' raw) := by
      rw [hpreserving.map_eq]
    _ = volume (toLp ⁻¹' (toLp '' raw)) :=
      Measure.map_apply hmeasurable himageMeasurable
    _ = volume raw := by rw [Set.preimage_image_eq raw hinjective]
    _ = 0 := hraw

/-- Delete the null source face at one fixed height. -/
def paperShadingRemoveTopFace
    {delta : ℝ} {family : Kakeya.Streamlined.TubeFamily delta}
    (shading : WZ1PaperTubeShading family) (top : ℝ) :
    WZ1PaperTubeShading family where
  carrier index := shading.carrier index \ {point | point 2 = top}
  measurable_carrier index :=
    (shading.measurable_carrier index).diff
      (measurableSet_singleton top |>.preimage (by fun_prop))
  subset_body index := diff_subset.trans (shading.subset_body index)

theorem paperShadingRemoveTopFace_mass
    {delta : ℝ} {family : Kakeya.Streamlined.TubeFamily delta}
    (shading : WZ1PaperTubeShading family) (top : ℝ) :
    (paperShadingRemoveTopFace shading top).mass = shading.mass := by
  apply Finset.sum_congr rfl
  intro index _
  change volume (shading.carrier index \ {point : Point3 | point 2 = top}) =
    volume (shading.carrier index)
  exact measure_diff_null (volume_coordinate_hyperplane_zero 2 top)

theorem paperShadingRemoveTopFace_height
    {delta c d : ℝ} {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    (hslab : ∀ index, shading.carrier index ⊆ horizontalSlab c d)
    (index : Fin family.card) {point : Point3}
    (hpoint : point ∈ (paperShadingRemoveTopFace shading d).carrier index) :
    c ≤ point 2 ∧ point 2 < d := by
  have hsource : point ∈ shading.carrier index := hpoint.1
  have hheight := hslab index hsource
  exact ⟨hheight.1, lt_of_le_of_ne hheight.2 (by
    intro heq
    exact hpoint.2 (by simpa using heq))⟩

end Kakeya.Assouad

end
