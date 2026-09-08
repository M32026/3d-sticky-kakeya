/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Prism
public import Kakeya.Shading

/-!
# Slabs in `ℝ³`

Basic definitions and incidence notation for `δ × 1 × 1` slabs.
-/

@[expose] public section

open MeasureTheory

noncomputable section

/-- A `Slab a` is an `a`-slab in `EuclideanSpace ℝ (Fin 3)` (i.e. `ℝ³`):
the `(a, 1, 1)`-prism, i.e. an `a`-thickening of a 2-dimensional unit disk.
Slabs have dimensions `a × 1 × 1`. -/
abbrev Slab (a : NNReal) (a_le_one : a ≤ 1) :=
  Prism3D a (1 : NNReal) (1 : NNReal) a_le_one le_rfl

namespace Slab

variable {a b : NNReal} {ha : a ≤ 1} {hb : b ≤ 1}

/-- The angle between the long planes of two slabs. -/
abbrev angle (S₁ : Slab a ha) (S₂ : Slab b hb) : ℝ :=
  Prism3D.angle S₁ S₂

end Slab

/-! ## Shaded slabs and incidence triples -/

/-- A `δ`-slab together with a measurable shading `Y(S) ⊆ S.carrier`. -/
structure ShadedSlab (δ : NNReal) (δ_le_one : δ ≤ 1) extends
    Slab δ δ_le_one, ShadedBody (EuclideanSpace ℝ (Fin 3))

attribute [nolint docBlame] ShadedSlab.toShadedBody

namespace ShadedSlab

variable {δ : NNReal} {h : δ ≤ 1} {ι : Type*}

/-- The mass of the incidence triples:
`|Tri| = ∑ᵢⱼ |Y(Sᵢ) ∩ Y(Sⱼ)|`. -/
noncomputable def tri
    (s : Finset ι) (V : ι → ShadedSlab δ h) : ENNReal :=
  ∑ i ∈ s, ∑ j ∈ s, volume ((V i).shade ∩ (V j).shade)

/-- The mass of incidence triples whose slab angle lies in the window
`θ - δ ≤ angle(Sᵢ, Sⱼ) ≤ 2 * θ`. -/
noncomputable def triAtAngle
    (s : Finset ι) (V : ι → ShadedSlab δ h) (θ : ℝ) : ENNReal :=
  ∑ i ∈ s, ∑ j ∈ s with θ - δ ≤ Slab.angle (V i).toPrism3D (V j).toPrism3D ∧
        Slab.angle (V i).toPrism3D (V j).toPrism3D ≤ 2 * θ ,
      volume ((V i).shade ∩ (V j).shade)

lemma tri_def (s : Finset ι) (V : ι → ShadedSlab δ h) :
    tri s V =
      ∑ i ∈ s, ∑ j ∈ s, volume ((V i).shade ∩ (V j).shade) := rfl

lemma triAtAngle_def
    (s : Finset ι) (V : ι → ShadedSlab δ h) (θ : ℝ) :
    triAtAngle s V θ =
      ∑ i ∈ s, ∑ j ∈ s with θ - δ ≤ Slab.angle (V i).toPrism3D (V j).toPrism3D ∧
            Slab.angle (V i).toPrism3D (V j).toPrism3D ≤ 2 * θ ,
          volume ((V i).shade ∩ (V j).shade) := rfl

@[simp] lemma tri_empty (V : ι → ShadedSlab δ h) :
    tri (∅ : Finset ι) V = 0 := by
  simp [tri]

@[simp] lemma triAtAngle_empty
    (V : ι → ShadedSlab δ h) (θ : ℝ) :
    triAtAngle (∅ : Finset ι) V θ = 0 := by
  simp [triAtAngle]

/-- `|Tri_θ(SSS)| ≤ |Tri(SSS)|`: restricting to a particular angle range
can only shrink the incidence-triples mass. -/
lemma triAtAngle_le_tri
    (s : Finset ι) (V : ι → ShadedSlab δ h) (θ : ℝ) :
    triAtAngle s V θ ≤ tri s V := by
  rw [triAtAngle_def, tri_def]
  refine Finset.sum_le_sum fun i _ => ?_
  exact Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)

/-- `θ` is typical if `Tri` is controlled by the incidences at angle `θ`,
up to the explicit loss factor `M`. -/
def IsTypicalIntersectionAngle
    (s : Finset ι) (V : ι → ShadedSlab δ h)
    (θ : ℝ) (M : ENNReal) : Prop :=
  tri s V ≤ M * triAtAngle s V θ

lemma IsTypicalIntersectionAngle.tri_le_smul_triAtAngle
    {s : Finset ι} {V : ι → ShadedSlab δ h} {θ : ℝ} {M : ENNReal}
    (hθ : IsTypicalIntersectionAngle s V θ M) :
    tri s V ≤ M * triAtAngle s V θ := hθ

end ShadedSlab

end

end
