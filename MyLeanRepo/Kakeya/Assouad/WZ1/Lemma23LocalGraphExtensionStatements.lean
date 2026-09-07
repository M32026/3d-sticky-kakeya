import MyLeanRepo.Kakeya.Assouad.WZ1.Definitions
import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Extend the local-plane graph in WZ1 Lemma 23

After Step 1 of the locally-linear argument, one has a finite separated set of
y-layers and one anchor point on each layer.  The plane normal at every anchor
has horizontal component bounded below and vertical component bounded above.
Writing the normal as parallel to `(1, h(y), g(y))` therefore defines

`g(y) = normal(anchor y)_z / normal(anchor y)_x`.

The quotient is Lipschitz on the sampled y-layers.  A McShane extension
followed by clamping gives a globally defined bounded Lipschitz function.  We
use the safe absolute constant `64`; no downstream argument depends on the
paper's suppressed constant.
-/

namespace Kakeya.Assouad

noncomputable section

/-- Clamp a real number to the interval `[-2,2]`. -/
def wz1Lemma23ClampLocalGraph (value : ℝ) : ℝ :=
  max (-2) (min 2 value)

/--
Construct the bounded global local-plane graph from finite anchor normals.

The anchor distortion hypothesis is the output of the separated
`sqrt rho`-cell geometry.  The normal-distance hypothesis is the restriction
of the final one-Lipschitz plane map.
-/
def WZ1Lemma23LocalGraphExtensionStatement : Prop :=
  ∀ (sample : Finset ℝ)
    (anchor : ℝ → Point3) (normal : Point3 → Point3),
    (∀ y ∈ sample, anchor y (1 : Fin 3) = y) →
    (∀ y ∈ sample, ‖normal (anchor y)‖ = 1) →
    (∀ y ∈ sample,
      |normal (anchor y) (2 : Fin 3)| ≤ 1 / 2) →
    (∀ y ∈ sample,
      1 / 4 ≤ |normal (anchor y) (0 : Fin 3)|) →
    (∀ y₁ ∈ sample, ∀ y₂ ∈ sample,
      dist (normal (anchor y₁)) (normal (anchor y₂)) ≤
        dist (anchor y₁) (anchor y₂)) →
    (∀ y₁ ∈ sample, ∀ y₂ ∈ sample,
      dist (anchor y₁) (anchor y₂) ≤ 4 * |y₁ - y₂|) →
      ∃ g : ℝ → ℝ,
        LipschitzOnWith 64 g Set.univ ∧
        (∀ y, |g y| ≤ 2) ∧
        ∀ y ∈ sample,
          g y =
            normal (anchor y) (2 : Fin 3) /
              normal (anchor y) (0 : Fin 3)

end

end Kakeya.Assouad
