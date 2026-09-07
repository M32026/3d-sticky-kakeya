import MyLeanRepo.Kakeya.Assouad.SlopeRescaling

/-!
# Exact projection identity for the WZ2 anisotropic rescaling

This is the coordinate computation used by the full configuration transport.
-/

noncomputable section

namespace Kakeya.Assouad

@[simp]
private lemma anisotropicRescalingMap_apply_zero
    (g : SlopeFunction) (c d m : ℝ) (p : Point3) :
    anisotropicRescalingMap g c d m p (0 : Fin 3) =
      p (0 : Fin 3) +
        g (c + (d - c) / 2) * p (1 : Fin 3) := by
  simp [anisotropicRescalingMap, point3,
    EuclideanSpace.single_apply]

@[simp]
private lemma anisotropicRescalingMap_apply_one
    (g : SlopeFunction) (c d m : ℝ) (p : Point3) :
    anisotropicRescalingMap g c d m p (1 : Fin 3) =
      (m * (d - c) / 2) * p (1 : Fin 3) := by
  simp [anisotropicRescalingMap, point3,
    EuclideanSpace.single_apply]

@[simp]
private lemma anisotropicRescalingMap_apply_two
    (g : SlopeFunction) (c d m : ℝ) (p : Point3) :
    anisotropicRescalingMap g c d m p (2 : Fin 3) =
      2 * (p (2 : Fin 3) - c) / (d - c) - 1 := by
  simp [anisotropicRescalingMap, point3,
    EuclideanSpace.single_apply]

@[simp]
private lemma twistedProjection_apply_zero
    (f : SlopeFunction) (p : Point3) :
    twistedProjection f p (0 : Fin 2) =
      p (0 : Fin 3) + f (p (2 : Fin 3)) * p (1 : Fin 3) := by
  simp [twistedProjection, EuclideanSpace.single_apply]

@[simp]
private lemma twistedProjection_apply_one
    (f : SlopeFunction) (p : Point3) :
    twistedProjection f p (1 : Fin 2) = p (2 : Fin 3) := by
  simp [twistedProjection, EuclideanSpace.single_apply]

/--
The normalized slope formula makes the horizontal twisted-projection
coordinate invariant under `anisotropicRescalingMap`.
-/
lemma twistedProjection_anisotropicRescalingMap_zero
    (g f : SlopeFunction) {c d m : ℝ}
    (hcd : c < d) (hm : 0 < m)
    (hf : ∀ t : ℝ,
      f t =
        g (c + (d - c) / 2 * (t + 1)) /
            (m * (d - c) / 2) -
          g (c + (d - c) / 2) /
            (m * (d - c) / 2))
    (p : Point3) :
    twistedProjection f (anisotropicRescalingMap g c d m p)
        (0 : Fin 2) =
      p (0 : Fin 3) + g (p (2 : Fin 3)) * p (1 : Fin 3) := by
  have hell : d - c ≠ 0 := sub_ne_zero.mpr hcd.ne'
  have hscale : m * (d - c) / 2 ≠ 0 := by
    positivity
  simp only [twistedProjection_apply_zero,
    anisotropicRescalingMap_apply_zero,
    anisotropicRescalingMap_apply_one,
    anisotropicRescalingMap_apply_two]
  rw [hf]
  have hargument :
      c + (d - c) / 2 *
          (2 * (p (2 : Fin 3) - c) / (d - c) - 1 + 1) =
        p (2 : Fin 3) := by
    field_simp [hell]
    ring
  rw [hargument]
  field_simp [hscale]
  ring

/-- The vertical twisted-projection coordinate is affinely reparametrized. -/
lemma twistedProjection_anisotropicRescalingMap_one
    (g f : SlopeFunction) (c d m : ℝ) (p : Point3) :
    twistedProjection f (anisotropicRescalingMap g c d m p)
        (1 : Fin 2) =
      2 * (p (2 : Fin 3) - c) / (d - c) - 1 := by
  simp [twistedProjection_apply_one,
    anisotropicRescalingMap_apply_two]

end Kakeya.Assouad
