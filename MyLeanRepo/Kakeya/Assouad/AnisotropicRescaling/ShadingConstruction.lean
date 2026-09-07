import MyLeanRepo.Kakeya.Assouad.Definitions
import MyLeanRepo.Kakeya.Assouad.AnisotropicRescaling.ImageGeometry
import MyLeanRepo.Kakeya.Streamlined.Families
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Shading construction for the anisotropic rescaling

Given the target tube family F' covering the anisotropic image S, construct
the target shading Y' by intersecting each target tube with the rho-thickening
of S and the slope window.

This yields the three geometric containments:
1. S ⊆ Y'.union
2. Y'.union ⊆ cthickening rho S
3. Y'.union ⊆ horizontalSlab (-1) 1
-/

noncomputable section

open MeasureTheory Metric Set

namespace Kakeya.Assouad

/--
The anisotropic rescaling maps the z-coordinate affinely from [c,d] to [-1,1].
Hence the image of any subset of the horizontal slab [c,d] lies in the
slope window [-1,1].
-/
lemma anisotropicImage_in_slopeWindow
    {g : SlopeFunction} {c d m : ℝ} (hcd : c < d)
    {A : Set Point3} (hA : A ⊆ horizontalSlab c d) :
    anisotropicRescalingMap g c d m '' A ⊆ horizontalSlab (-1) 1 := by
  intro z hz
  rcases hz with ⟨p, hp, rfl⟩
  have hpz : p 2 ∈ Set.Icc c d := hA hp
  exact anisotropicImage_z_bound hcd hpz

/--
Construct the target shading Y' by intersecting each target tube with the
rho-thickening of the image S and the slope window.

Given a covering of S by the target tubes, this produces a shading Y'
satisfying the three geometric containment properties.
-/
lemma construct_target_shading
    {δ rho : ℝ} {F : Kakeya.Streamlined.TubeFamily δ}
    {F' : Kakeya.Streamlined.TubeFamily rho}
    (Y : Kakeya.Streamlined.TubeShading F)
    (Φ : Point3 → Point3)
    (c d : ℝ)
    (_hrho_nonneg : 0 ≤ rho)
    (hcover : Φ '' (Y.union ∩ horizontalSlab c d) ⊆ F'.toBodyFamily.union)
    (himage_window : Φ '' (Y.union ∩ horizontalSlab c d) ⊆ horizontalSlab (-1) 1) :
    ∃ Y' : Kakeya.Streamlined.TubeShading F',
      (Φ '' (Y.union ∩ horizontalSlab c d) ⊆ Y'.union) ∧
      (Y'.union ⊆ Metric.cthickening rho (Φ '' (Y.union ∩ horizontalSlab c d))) ∧
      (Y'.union ⊆ horizontalSlab (-1) 1) := by
  let S := Φ '' (Y.union ∩ horizontalSlab c d)
  let carrier : Fin F'.card → Set Point3 := fun j =>
    ((F'.tube j).carrier ∩ Metric.cthickening rho S) ∩ horizontalSlab (-1) 1
  have h1_meas : ∀ j, MeasurableSet (F'.tube j).carrier := by
    intro j
    exact Metric.isClosed_cthickening.measurableSet
  have h2_meas : MeasurableSet (Metric.cthickening rho S) :=
    Metric.isClosed_cthickening.measurableSet
  have h3_closed : IsClosed (horizontalSlab (-1) 1) := by
    have h_cont : Continuous (fun x : Point3 => x 2) :=
      PiLp.continuous_apply (p := 2) (β := fun _ : Fin 3 => ℝ) 2
    exact IsClosed.preimage h_cont isClosed_Icc
  have h3_meas : MeasurableSet (horizontalSlab (-1) 1) :=
    h3_closed.measurableSet
  have h_meas : ∀ j, MeasurableSet (carrier j) := by
    intro j
    have h12 : MeasurableSet ((F'.tube j).carrier ∩ Metric.cthickening rho S) :=
      (h1_meas j).inter h2_meas
    exact h12.inter h3_meas
  have h_subset : ∀ j, carrier j ⊆ (F'.toBodyFamily.body j).carrier := by
    intro j x hx
    exact hx.1.1
  let Y' : Kakeya.Streamlined.TubeShading F' :=
    { carrier := carrier
      measurable_carrier := h_meas
      subset_body := h_subset }
  refine' ⟨Y', _ , _ , _⟩
  · -- Property 1: S ⊆ Y'.union
    intro z hz
    have h_in_cover : z ∈ F'.toBodyFamily.union := hcover hz
    rcases h_in_cover with ⟨j, hj⟩
    have h_in_thick : z ∈ Metric.cthickening rho S :=
      Metric.self_subset_cthickening (E := S) hz
    have h_in_window : z ∈ horizontalSlab (-1) 1 := himage_window hz
    have h4 : z ∈ carrier j := ⟨⟨hj, h_in_thick⟩, h_in_window⟩
    exact ⟨j, h4⟩
  · -- Property 2: Y'.union ⊆ cthickening rho S
    intro z hz
    rcases hz with ⟨j, hj⟩
    exact hj.1.2
  · -- Property 3: Y'.union ⊆ horizontalSlab (-1) 1
    intro z hz
    rcases hz with ⟨j, hj⟩
    exact hj.2

end Kakeya.Assouad
