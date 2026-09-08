/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Plank.TypedAnchorPrism
public import Kakeya.DimensionThree.Plank.RepresentativeFibres

/-!
# The slab-local typical angle, at retention one

The angular input the good-box layer needs is `Kakeya.IsTypicalPlankAngle` on a *slab-local*
family, while the plank witness supplies it on the whole refined family `s'`.  The transfer is free,
and this file is where that is recorded.

The mechanism is not a fibre retention.  It is that the *geometric* controlled slab family is
closed under passing to the whole shade fibre: at a point of the shading union of the small family
`inSlabFamilyC Cset Cang`, every plank of the full `s'`-fibre through that point makes an angle
`≤ (2 Cang + 4 C) θ` with the slab (`Plank.angle_le_of_mem_shadeFibre_slabLocal`) and is confined to
a fixed dilation of it, hence lies in the *enlarged* family
`inSlabFamilyC (Cset + 4 (2 Cang + 4 C) + 8) (2 Cang + 4 C)`.  So the enlarged family's shade fibre
*equals* the full fibre of `s'` there (`Plank.shadeFibre_inSlabFamilyC_eq_of_slabLocal`), the
retained fraction is `1`, and the typical-angle predicate transfers at the same `Cθ` and the same
stability scale `A`, with no `a^ε` spent.

This must be contrasted with `Plank.assignedSlabFamily`, which is a partition class of
`slabOf ∘ repr` and is *not* fibre-closed: for it no uniform retention exists, because the class
realising the bound moves with the point.  The good-box layer therefore selects on the geometric
families and pays the fixed index overlap `Nov`, never on the assigned families.

The domain of the fibre identity is the *small* family's shading union, and that is sharp: the
enlargement `(Cset, Cang) ↦ (Cset + 4(2 Cang + 4 C) + 8, 2 Cang + 4 C)` has no fixed point when
`0 < C`.  `Plank.isTypicalPlankAngle_inSlabFamilyC_of_shadeUnion` therefore carries the residual
shading-union inclusion as a hypothesis, and
`Plank.isTypicalPlankAngle_inSlabFamilyC_trimmed` discharges it unconditionally by trimming the
shadings to that union, at a cost paid on the fullness ledger.

These declarations support the representative-shading layer.  They
are stated here instead because that file imports
`Kakeya.DimensionThree.Plank.RepresentativeSelection`, so anything in it is downstream of
`Kakeya.plankReduction` and cannot be used to prove it; the good-box layer needs them upstream.
-/

@[expose] public section

open MeasureTheory Convexity
open scoped NNReal Real ENNReal

noncomputable section

namespace Plank

variable {ι : Type*}

/-! ## The slab-local angle bound -/

/-- **Angular domination of a fibre by the slab of any of its members** (extra69,
`note:angleLeOfMemShadeFibreSlabLocal`).

Let `x` lie in the shade of a plank `i₀` of the controlled slab subfamily of `S`.  Then *every*
plank of the full shade fibre through `x` makes an angle at most `(2·Cang + 4·C)·θ` with `S`.

Only the one-sided `Kakeya.HasMaxPlankAngleBound` is used — the absolute-constant clause that
`Kakeya.representativeWitness_strong_uniform` returns — so the enlarged constant is uniform.
The proof is the angular half of `Plank.inSlabFamilyC_normal_and_center_confined`:
`Plank.angle_le_two_mul_of_mem_shadeFibre` puts the two planks of the fibre within `2·C·θ` in the
plane angle, and `Prism3D.angle_le_two_mul_add_angle` chains that with `i₀`'s own `Cang·θ`
bound. -/
theorem angle_le_of_mem_shadeFibre_slabLocal {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
    (s : Finset ι) (V : ι → Plank a b hab hb1)
    (Y : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    {θ : ℝ≥0} {hθ1 : θ ≤ 1} (S : Slab θ hθ1) (Cset Cang C : ℝ≥0)
    (hmax : Kakeya.HasMaxPlankAngleBound s Y V θ C)
    (x : EuclideanSpace ℝ (Fin 3)) (i₀ : ι)
    (hi₀ : i₀ ∈ inSlabFamilyC Cset Cang s V S) (hxi₀ : x ∈ (Y i₀).shade)
    (j : ι) (hj : j ∈ Kakeya.shadeFibre s Y x) :
    Prism3D.angle (V j) S ≤ (2 * (Cang : ℝ) + 4 * (C : ℝ)) * (θ : ℝ) := by
  have hi₀_s : i₀ ∈ s := (Plank.mem_inSlabFamilyC.mp hi₀).1
  have hi₀_angle : Prism3D.angle (V i₀) S ≤ (Cang : ℝ) * (θ : ℝ) :=
    (Plank.mem_inSlabFamilyC.mp hi₀).2.2
  have hi₀_fib : i₀ ∈ Kakeya.shadeFibre s Y x :=
    (Kakeya.mem_shadeFibre s Y x i₀).mpr ⟨hi₀_s, hxi₀⟩
  have hxU : x ∈ ⋃ i ∈ s, (Y i).shade :=
    Set.mem_iUnion₂.mpr ⟨i₀, hi₀_s, hxi₀⟩
  have hangMid : Prism3D.angle (V j) (V i₀) ≤ 2 * (C : ℝ) * (θ : ℝ) :=
    Plank.angle_le_two_mul_of_mem_shadeFibre hmax hxU hj hi₀_fib
  calc
    Prism3D.angle (V j) S ≤ 2 * (Prism3D.angle (V j) (V i₀) + Prism3D.angle (V i₀) S) :=
      Prism3D.angle_le_two_mul_add_angle (V j) (V i₀) S
    _ ≤ 2 * (2 * (C : ℝ) * (θ : ℝ) + (Cang : ℝ) * (θ : ℝ)) := by
      nlinarith [hangMid, hi₀_angle]
    _ = (2 * (Cang : ℝ) + 4 * (C : ℝ)) * (θ : ℝ) := by
      ring

/-- **A fibre through a slab-local point lies in the enlarged slab family** (extra69,
`rem:memInSlabFamilyCOfMemShadeFibreSlabLocal`).

Both halves of `Plank.angle_le_of_mem_shadeFibre_slabLocal` at once.  The angular half is that
theorem; the carrier half is `Plank.plank_subset_dilation_of_angle_le` at `p := x`, which lies in
`(V j).carrier` because `x` is in `j`'s shade, and in the `Cset`-dilated slab because `x` is in
`i₀`'s shade and `i₀` is carrier-confined.  Both enlarged constants are fixed affine functions of
`(Cset, Cang, C)`. -/
theorem mem_inSlabFamilyC_of_mem_shadeFibre_slabLocal {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
    (s : Finset ι) (V : ι → Plank a b hab hb1)
    (Y : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    {θ : ℝ≥0} {hθ1 : θ ≤ 1} (S : Slab θ hθ1) (Cset Cang C : ℝ≥0)
    (haθb : a ≤ θ * b)
    (hshade : ∀ i ∈ s, (Y i).shade ⊆ ((V i).carrier : Set (EuclideanSpace ℝ (Fin 3))))
    (hmax : Kakeya.HasMaxPlankAngleBound s Y V θ C)
    (x : EuclideanSpace ℝ (Fin 3)) (i₀ : ι)
    (hi₀ : i₀ ∈ inSlabFamilyC Cset Cang s V S) (hxi₀ : x ∈ (Y i₀).shade)
    (j : ι) (hj : j ∈ Kakeya.shadeFibre s Y x) :
    j ∈ inSlabFamilyC (Cset + 4 * (2 * Cang + 4 * C) + 8) (2 * Cang + 4 * C) s V S := by
  have hjs : j ∈ s := ((Kakeya.mem_shadeFibre s Y x j).mp hj).1
  have hxj : x ∈ (Y j).shade := ((Kakeya.mem_shadeFibre s Y x j).mp hj).2
  have hangj : Prism3D.angle (V j) S ≤ (2 * (Cang : ℝ) + 4 * (C : ℝ)) * (θ : ℝ) :=
    angle_le_of_mem_shadeFibre_slabLocal s V Y S Cset Cang C hmax x i₀ hi₀ hxi₀ j hj
  have hxVj : x ∈ ((V j).carrier : Set (EuclideanSpace ℝ (Fin 3))) := hshade j hjs hxj
  have hi₀s : i₀ ∈ s := (mem_inSlabFamilyC.mp hi₀).1
  have hi₀car : ((V i₀).carrier : Set (EuclideanSpace ℝ (Fin 3)))
      ⊆ (S.toPrismNDim.dilation Cset).carrier := (mem_inSlabFamilyC.mp hi₀).2.1
  have hxS : x ∈ ((S.toPrismNDim.dilation Cset).carrier : Set (EuclideanSpace ℝ (Fin 3))) :=
    hi₀car (hshade i₀ hi₀s hxi₀)
  have hangj' : Prism3D.angle (V j) S ≤ ((2 * Cang + 4 * C : ℝ≥0) : ℝ) * (θ : ℝ) := by
    push_cast
    exact hangj
  rw [mem_inSlabFamilyC]
  exact ⟨hjs,
    plank_subset_dilation_of_angle_le (V j) S (2 * Cang + 4 * C) Cset haθb hangj' hxVj hxS,
    hangj'⟩

/-- **At a slab-local point the enlarged slab family sees the whole fibre** (extra69,
`rem:shadeFibreInSlabFamilyCEqOfSlabLocal`).

At every `x` in the shading union of `inSlabFamilyC Cset Cang s V S`, the shade fibre of the
*enlarged* family is the full shade fibre of `s`.  One inclusion is `inSlabFamilyC_subset`; the
other is `Plank.mem_inSlabFamilyC_of_mem_shadeFibre_slabLocal` followed by
`Plank.inSlabFamilyC_mono`.  The retained fraction is `1`, so no reserve stability scale is spent.

The domain is the *small* family's shading union.  That is not an artefact: the enlargement
`(Cset, Cang) ↦ (Cset + 4·(2·Cang + 4·C) + 8, 2·Cang + 4·C)` has no fixed point when `0 < C`, so no
uniform pair of constants makes the fibre identity hold on its own shading union. -/
theorem shadeFibre_inSlabFamilyC_eq_of_slabLocal {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
    (s : Finset ι) (V : ι → Plank a b hab hb1)
    (Y : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    {θ : ℝ≥0} {hθ1 : θ ≤ 1} (S : Slab θ hθ1) (Cset Cang C Cset' Cang' : ℝ≥0)
    (haθb : a ≤ θ * b)
    (hCset' : Cset + 4 * (2 * Cang + 4 * C) + 8 ≤ Cset')
    (hCang' : 2 * Cang + 4 * C ≤ Cang')
    (hshade : ∀ i ∈ s, (Y i).shade ⊆ ((V i).carrier : Set (EuclideanSpace ℝ (Fin 3))))
    (hmax : Kakeya.HasMaxPlankAngleBound s Y V θ C)
    (x : EuclideanSpace ℝ (Fin 3))
    (hx : x ∈ ⋃ i ∈ inSlabFamilyC Cset Cang s V S, (Y i).shade) :
    Kakeya.shadeFibre (inSlabFamilyC Cset' Cang' s V S) Y x = Kakeya.shadeFibre s Y x := by
  obtain ⟨i₀, hi₀, hxi₀⟩ := Set.mem_iUnion₂.mp hx
  ext j
  rw [Kakeya.mem_shadeFibre, Kakeya.mem_shadeFibre]
  constructor
  · rintro ⟨hjF, hjx⟩
    exact ⟨inSlabFamilyC_subset hjF, hjx⟩
  · rintro ⟨hjs, hjx⟩
    refine ⟨?_, hjx⟩
    have hj : j ∈ Kakeya.shadeFibre s Y x := (Kakeya.mem_shadeFibre s Y x j).mpr ⟨hjs, hjx⟩
    have hmem := mem_inSlabFamilyC_of_mem_shadeFibre_slabLocal s V Y S Cset Cang C haθb hshade hmax
      x i₀ hi₀ hxi₀ j hj
    exact inSlabFamilyC_mono hCset' hCang' hmem

/-- **The slab-local typical angle, at the same stability scale and the same angle constant**
(extra69, `rem:isTypicalPlankAngleInSlabFamilyC`).

Given the two-sided `Kakeya.IsTypicalPlankAngle` on all of `s` and the shading-union inclusion
`hU`, the predicate holds on the enlarged slab-local family at the *same* `Cθ` and the *same* `A`,
because `Plank.shadeFibre_inSlabFamilyC_eq_of_slabLocal` makes the fibres literally equal.

`hU` is the exact residual gap: without it the fibre identity is only available at points of the
*small* family's shading union.  `Plank.isTypicalPlankAngle_inSlabFamilyC_trimmed` discharges it by
trimming the shadings. -/
theorem isTypicalPlankAngle_inSlabFamilyC_of_shadeUnion {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
    (s : Finset ι) (V : ι → Plank a b hab hb1)
    (Y : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    {θ : ℝ≥0} {hθ1 : θ ≤ 1} (S : Slab θ hθ1) (Cset Cang C Cset' Cang' Cθ A : ℝ≥0)
    (haθb : a ≤ θ * b)
    (hCset' : Cset + 4 * (2 * Cang + 4 * C) + 8 ≤ Cset')
    (hCang' : 2 * Cang + 4 * C ≤ Cang')
    (hshade : ∀ i ∈ s, (Y i).shade ⊆ ((V i).carrier : Set (EuclideanSpace ℝ (Fin 3))))
    (hmax : Kakeya.HasMaxPlankAngleBound s Y V θ C)
    (hU : (⋃ i ∈ inSlabFamilyC Cset' Cang' s V S, (Y i).shade)
      ⊆ ⋃ i ∈ inSlabFamilyC Cset Cang s V S, (Y i).shade)
    (hty : Kakeya.IsTypicalPlankAngle s Y V θ Cθ A) :
    Kakeya.IsTypicalPlankAngle (inSlabFamilyC Cset' Cang' s V S) Y V θ Cθ A := by
  intro x hx
  have hxSmall : x ∈ ⋃ i ∈ inSlabFamilyC Cset Cang s V S, (Y i).shade := hU hx
  have hfib : Kakeya.shadeFibre (inSlabFamilyC Cset' Cang' s V S) Y x = Kakeya.shadeFibre s Y x :=
    shadeFibre_inSlabFamilyC_eq_of_slabLocal s V Y S Cset Cang C Cset' Cang' haθb hCset' hCang'
      hshade hmax x hxSmall
  rw [hfib]
  obtain ⟨i₀, hi₀, hxi₀⟩ := Set.mem_iUnion₂.mp hxSmall
  exact hty x (Set.mem_iUnion₂.mpr ⟨i₀, inSlabFamilyC_subset hi₀, hxi₀⟩)

/-! ## The trimmed fibre identity, and the three transfers it yields

`Plank.shadeFibre_trimmed_inSlabFamilyC_eq` below is the single fact behind every slab-local
transfer the good-box layer needs.  Stating it separately (rather than inlining it, as
`Plank.isTypicalPlankAngle_inSlabFamilyC_trimmed` used to) is what makes the max-angle bound and
the angular-stability clause transfer as well, not just the typical angle — and those two are
exactly the hypotheses of `Plank.localAngleConcentration_of_saturated`.
-/

/-- **The trimmed enlarged family has the full global shade fibre, everywhere on its own union.**

`Z` trims each shade to the shading union `U` of the *small* controlled slab family.  Then at every
point of the `Z`-shading union of the *enlarged* family, the `Z`-fibre of the enlarged family is the
full `Y`-fibre of `s`.

Two steps: trimming does not change the fibre at a point of `U` (a point of `U` is in `(Z j).shade`
iff it is in `(Y j).shade`), and there
`Plank.shadeFibre_inSlabFamilyC_eq_of_slabLocal` identifies the enlarged family's `Y`-fibre with the
`s`-fibre.  The retained fraction is `1`; nothing is spent. -/
theorem shadeFibre_trimmed_inSlabFamilyC_eq {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
    (s : Finset ι) (V : ι → Plank a b hab hb1)
    (Y Z : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    {θ : ℝ≥0} {hθ1 : θ ≤ 1} (S : Slab θ hθ1) (Cset Cang C Cset' Cang' : ℝ≥0)
    (haθb : a ≤ θ * b)
    (hCset' : Cset + 4 * (2 * Cang + 4 * C) + 8 ≤ Cset')
    (hCang' : 2 * Cang + 4 * C ≤ Cang')
    (hshade : ∀ i ∈ s, (Y i).shade ⊆ ((V i).carrier : Set (EuclideanSpace ℝ (Fin 3))))
    (hmax : Kakeya.HasMaxPlankAngleBound s Y V θ C)
    (hZ : ∀ i, (Z i).shade
      = (Y i).shade ∩ ⋃ i' ∈ inSlabFamilyC Cset Cang s V S, (Y i').shade)
    (x : EuclideanSpace ℝ (Fin 3))
    (hx : x ∈ ⋃ i ∈ inSlabFamilyC Cset' Cang' s V S, (Z i).shade) :
    Kakeya.shadeFibre (inSlabFamilyC Cset' Cang' s V S) Z x = Kakeya.shadeFibre s Y x := by
  obtain ⟨i₁, hi₁, hxi₁⟩ := Set.mem_iUnion₂.mp hx
  have hxZ : x ∈ (Z i₁).shade := hxi₁
  rw [hZ i₁] at hxZ
  have hxSmall : x ∈ ⋃ i ∈ inSlabFamilyC Cset Cang s V S, (Y i).shade := hxZ.2
  have hfib : Kakeya.shadeFibre (inSlabFamilyC Cset' Cang' s V S) Z x
      = Kakeya.shadeFibre (inSlabFamilyC Cset' Cang' s V S) Y x := by
    ext j
    rw [Kakeya.mem_shadeFibre, Kakeya.mem_shadeFibre, hZ j]
    simp [hxSmall]
  rw [hfib]
  exact shadeFibre_inSlabFamilyC_eq_of_slabLocal s V Y S Cset Cang C Cset' Cang' haθb
    hCset' hCang' hshade hmax x hxSmall

/-- **The max-angle bound transfers to the trimmed enlarged family, at the same constant.**

The first hypothesis of `Plank.localAngleConcentration_of_saturated` on the slab-local family.  It
is immediate from `Plank.shadeFibre_trimmed_inSlabFamilyC_eq`: the fibre is not merely smaller, it
is *equal* to the global one, so no monotonicity slack is used and the constant is unchanged. -/
theorem hasMaxPlankAngleBound_trimmed_inSlabFamilyC {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
    (s : Finset ι) (V : ι → Plank a b hab hb1)
    (Y Z : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    {θ : ℝ≥0} {hθ1 : θ ≤ 1} (S : Slab θ hθ1) (Cset Cang C Cset' Cang' : ℝ≥0)
    (haθb : a ≤ θ * b)
    (hCset' : Cset + 4 * (2 * Cang + 4 * C) + 8 ≤ Cset')
    (hCang' : 2 * Cang + 4 * C ≤ Cang')
    (hshade : ∀ i ∈ s, (Y i).shade ⊆ ((V i).carrier : Set (EuclideanSpace ℝ (Fin 3))))
    (hmax : Kakeya.HasMaxPlankAngleBound s Y V θ C)
    (hZ : ∀ i, (Z i).shade
      = (Y i).shade ∩ ⋃ i' ∈ inSlabFamilyC Cset Cang s V S, (Y i').shade) :
    Kakeya.HasMaxPlankAngleBound (inSlabFamilyC Cset' Cang' s V S) Z V θ C := by
  intro x hx
  rw [shadeFibre_trimmed_inSlabFamilyC_eq s V Y Z S Cset Cang C Cset' Cang' haθb hCset' hCang'
    hshade hmax hZ x hx]
  obtain ⟨i₁, hi₁, hxi₁⟩ := Set.mem_iUnion₂.mp hx
  have hxZ : x ∈ (Z i₁).shade := hxi₁
  rw [hZ i₁] at hxZ
  obtain ⟨i₀, hi₀, hxi₀⟩ := Set.mem_iUnion₂.mp hxZ.2
  exact hmax x (Set.mem_iUnion₂.mpr ⟨i₀, inSlabFamilyC_subset hi₀, hxi₀⟩)

/-- **The angular-stability clause transfers to the trimmed enlarged family, at the same scale.**

The last hypothesis of `Plank.localAngleConcentration_of_saturated` on the slab-local family.  Again
the fibre identity of `Plank.shadeFibre_trimmed_inSlabFamilyC_eq` makes this a rewriting, so the
stability scale `A` is the global one — no reserve scale and no `a^ε` are spent on
slab-localisation.

The stability constant `Cstab` is a free real: the transfer never inspects it.  Consumers that fix
the *stop scale* instantiate `Cstab := Kakeya.plankAngleScaleB a`, which is the form
`Plank.localAngleConcentration_of_saturated` consumes; the polynomial route of
`Plank.localAngleConcentration_trimmed_of_slabLocal_poly` instantiates it at `Cθ · a ^ (-ε)`. -/
theorem localStability_trimmed_inSlabFamilyC {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
    (s : Finset ι) (V : ι → Plank a b hab hb1)
    (Y Z : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    {θ : ℝ≥0} {hθ1 : θ ≤ 1} (S : Slab θ hθ1) (Cset Cang C Cset' Cang' : ℝ≥0) (A Cstab : ℝ)
    (haθb : a ≤ θ * b)
    (hCset' : Cset + 4 * (2 * Cang + 4 * C) + 8 ≤ Cset')
    (hCang' : 2 * Cang + 4 * C ≤ Cang')
    (hshade : ∀ i ∈ s, (Y i).shade ⊆ ((V i).carrier : Set (EuclideanSpace ℝ (Fin 3))))
    (hmax : Kakeya.HasMaxPlankAngleBound s Y V θ C)
    (hZ : ∀ i, (Z i).shade
      = (Y i).shade ∩ ⋃ i' ∈ inSlabFamilyC Cset Cang s V S, (Y i').shade)
    (hstab : ∀ x ∈ ⋃ i ∈ s, (Y i).shade, ∀ t ⊆ Kakeya.shadeFibre s Y x,
      A⁻¹ * ((Kakeya.shadeFibre s Y x).card : ℝ) ≤ (t.card : ℝ) →
        (θ : ℝ) / Cstab ≤ ((Kakeya.maxPlankAngle V t : ℝ≥0) : ℝ)) :
    ∀ x ∈ ⋃ i ∈ inSlabFamilyC Cset' Cang' s V S, (Z i).shade,
      ∀ t ⊆ Kakeya.shadeFibre (inSlabFamilyC Cset' Cang' s V S) Z x,
        A⁻¹ * ((Kakeya.shadeFibre (inSlabFamilyC Cset' Cang' s V S) Z x).card : ℝ)
            ≤ (t.card : ℝ) →
          (θ : ℝ) / Cstab ≤ ((Kakeya.maxPlankAngle V t : ℝ≥0) : ℝ) := by
  intro x hx t ht hcard
  have hfib := shadeFibre_trimmed_inSlabFamilyC_eq s V Y Z S Cset Cang C Cset' Cang' haθb
    hCset' hCang' hshade hmax hZ x hx
  rw [hfib] at ht hcard
  have hxU : x ∈ ⋃ i ∈ s, (Y i).shade := by
    obtain ⟨i₁, hi₁, hxi₁⟩ := Set.mem_iUnion₂.mp hx
    have hxZ : x ∈ (Z i₁).shade := hxi₁
    rw [hZ i₁] at hxZ
    obtain ⟨i₀, hi₀, hxi₀⟩ := Set.mem_iUnion₂.mp hxZ.2
    exact Set.mem_iUnion₂.mpr ⟨i₀, inSlabFamilyC_subset hi₀, hxi₀⟩
  exact hstab x hxU t ht hcard

/-- **The same transfer, unconditionally, after trimming the shadings** (extra69,
`rem:isTypicalPlankAngleInSlabFamilyCTrimmed`).

Let `U` be the shading union of the small slab-local family and let `Z` be any shading family with
`(Z i).shade = (Y i).shade ∩ U`.  Then the two-sided typical angle holds on the enlarged slab-local
family for `Z`, with no shading-union hypothesis: the `Z`-union is contained in `U` by construction,
and at a point of `U` the `Z`-fibre of the enlarged family is the `Y`-fibre of `s`.

The cost is moved to the fullness ledger: `Z` discards the shade of an enlarged-family plank lying
outside every small-family shade. -/
theorem isTypicalPlankAngle_inSlabFamilyC_trimmed {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
    (s : Finset ι) (V : ι → Plank a b hab hb1)
    (Y Z : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    {θ : ℝ≥0} {hθ1 : θ ≤ 1} (S : Slab θ hθ1) (Cset Cang C Cset' Cang' Cθ A : ℝ≥0)
    (haθb : a ≤ θ * b)
    (hCset' : Cset + 4 * (2 * Cang + 4 * C) + 8 ≤ Cset')
    (hCang' : 2 * Cang + 4 * C ≤ Cang')
    (hshade : ∀ i ∈ s, (Y i).shade ⊆ ((V i).carrier : Set (EuclideanSpace ℝ (Fin 3))))
    (hmax : Kakeya.HasMaxPlankAngleBound s Y V θ C)
    (hZ : ∀ i, (Z i).shade
      = (Y i).shade ∩ ⋃ i' ∈ inSlabFamilyC Cset Cang s V S, (Y i').shade)
    (hty : Kakeya.IsTypicalPlankAngle s Y V θ Cθ A) :
    Kakeya.IsTypicalPlankAngle (inSlabFamilyC Cset' Cang' s V S) Z V θ Cθ A := by
  intro x hx
  rw [shadeFibre_trimmed_inSlabFamilyC_eq s V Y Z S Cset Cang C Cset' Cang' haθb hCset' hCang'
    hshade hmax hZ x hx]
  obtain ⟨i₁, hi₁, hxi₁⟩ := Set.mem_iUnion₂.mp hx
  have hxZ : x ∈ (Z i₁).shade := hxi₁
  rw [hZ i₁] at hxZ
  obtain ⟨i₀, hi₀, hxi₀⟩ := Set.mem_iUnion₂.mp hxZ.2
  exact hty x (Set.mem_iUnion₂.mpr ⟨i₀, inSlabFamilyC_subset hi₀, hxi₀⟩)

end Plank

end
