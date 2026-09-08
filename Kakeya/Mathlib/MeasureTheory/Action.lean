/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Mathlib.MeasureTheory.Group.Action
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Measure invariance
-/

@[expose] public section

namespace MeasureTheory

lemma measure_image_add {G : Type u_1} [MeasurableSpace G] [AddGroup G]
    [MeasurableAdd G] (μ : Measure G) [μ.IsAddLeftInvariant] (g : G) (A : Set G) :
    μ ((g + ·) '' A) = μ A := measure_vadd μ g A


/-- Translation by a constant vector preserves `volume.real` of a set. -/
lemma measureReal_image_add [MeasurableSpace G] [AddGroup G]
    [MeasurableAdd G] (μ : Measure G) [μ.IsAddLeftInvariant] (g : G) (A : Set G) :
    μ.real ((g + ·) '' A) = μ.real A :=
  congr(ENNReal.toReal $(measure_image_add μ g A))

end MeasureTheory

/-- **An affine isometry equivalence preserves Lebesgue measure** (blueprint
`lem:affineIsometryVolumePreserving`): it is the composite of its linear part, measure
preserving by `LinearIsometryEquiv.measurePreserving`, with a translation, measure preserving by
left invariance of the additive Haar measure. -/
theorem AffineIsometryEquiv.measurePreserving {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]
    (Φ : F ≃ᵃⁱ[ℝ] F) :
    MeasureTheory.MeasurePreserving Φ MeasureTheory.volume MeasureTheory.volume := by
  have hdecomp : ⇑Φ = (fun y : F => (Φ 0 : F) + y) ∘ (Φ.linearIsometryEquiv : F → F) := by
    funext x
    have h : Φ x = Φ.linearIsometryEquiv x + Φ 0 := by
      have hmap := Φ.map_vadd (p := (0 : F)) (v := x)
      simpa using hmap
    simp [h, add_comm]
  rw [hdecomp]
  exact MeasureTheory.MeasurePreserving.comp (f := (Φ.linearIsometryEquiv : F → F))
    (g := fun y : F => (Φ 0 : F) + y)
    (MeasureTheory.measurePreserving_add_left MeasureTheory.volume (Φ 0))
    (Φ.linearIsometryEquiv.measurePreserving)
