/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Plank.SlabAssignment

/-!
# The index form of the slab overlap bound

`Plank.slab_pointwise_overlap_le` bounds, at a fixed *point*, the number of used slabs whose
`inSlabFamilyC`-indexed shading union contains that point.  The slab-local assembly of Item 2
needs the *index* form instead: for a fixed plank index `i`, the number of used slabs whose
controlled slab subfamily contains `i`.

The two are the same statement.  Collapse the shading of the whole family down to a single point
of the plank `V i` carried on the single index `i` (`Plank.pointShading`); then a slab whose
subfamily contains `i` automatically has that point in its shading union, so the index count is
dominated by the point count.  Since the witnessing point is a point of the *carrier*, which is
never empty, there is no degenerate case and no nonemptiness hypothesis on the shading.

Collapsing to one index is also what makes the argument free of the angular-clustering input: the
shade fibre over the chosen point is a singleton, whose maximal plank angle is `a / b` by
`Plank.effectivePlankAngle_self`, so the pointwise bound runs at the absolute constant `1`.
-/

@[expose] public section

open MeasureTheory Convexity
open scoped NNReal Real ENNReal

noncomputable section

namespace Plank

variable {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} {ι : Type*}

/-! ## The effective plank angle of a plank with itself -/

/-- **The effective plank angle of a plank with itself is `a / b`** (extra69,
`rem:effectivePlankAngleSelf`).

`Prism3D.planeAngle P P = arccos |⟪P₀, P₀⟫| = arccos 1 = 0` because the prism basis is orthonormal,
so `effectivePlankAngle P P = 1 ⊓ ((a / b) ⊔ 0) = a / b`.

This is the only angular fact needed to run the pointwise overlap bound against a shading supported
on a single plank: the shade fibre over the chosen point is a singleton, and a singleton's maximal
plank angle is exactly `a / b` — not `0`, because `Kakeya.effectivePlankAngle` is floored at
`a / b`. -/
theorem effectivePlankAngle_self (P : Plank a b hab hb1) :
    Kakeya.effectivePlankAngle P P = a / b := by
  have habs : |inner ℝ (P.basis 0) (P.basis 0)| = (1 : ℝ) := by
    rw [real_inner_self_eq_norm_sq, P.basis.orthonormal.1 0]
    norm_num
  rw [Kakeya.effectivePlankAngle, Prism3D.planeAngleNN, Prism3D.planeAngle, habs,
    Real.arccos_one, Real.toNNReal_zero, sup_eq_left.mpr zero_le,
    inf_eq_right.mpr (Kakeya.div_le_one_of_le hab)]

/-! ## The shading concentrated at one point of one plank -/

/-- The centre of a prism always lies in its carrier: the displacement `center -ᵥ center` is `0`,
whose basis coordinates are all bounded by the (nonnegative) half-widths. -/
private lemma center_mem_carrier {n : ℕ} {E S : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [PseudoMetricSpace S] [NormedAddTorsor E S]
    (P : PrismNDim n E S) : P.center ∈ (P.carrier : Set S) := by
  rw [P.mem_carrier_iff] -- (extracted by Fuse golfer)
  intro k
  simp only [vsub_self, map_zero, WithLp.ofLp_zero, Pi.zero_apply, abs_zero, NNReal.zero_le_coe]

open scoped Classical in
/-- **The one-point shading** (extra69, `rem:pointShading`): the shaded family over the plank
family `V` that shades the single point `x₀` on the single index `i₀`, and nothing anywhere else.

Its carrier at `j` is `V j`, so it is a legitimate shading of the *same* plank family, and its
shade fibre over any point is contained in `{i₀}`.  It is the device that converts the *point*
form of the slab overlap bound into the *index* form: a slab whose controlled family contains `i₀`
automatically contains `x₀` in its shading union. -/
def pointShading (V : ι → Plank a b hab hb1) (i₀ : ι) (x₀ : EuclideanSpace ℝ (Fin 3))
    (hx₀ : x₀ ∈ ((V i₀).carrier : Set (EuclideanSpace ℝ (Fin 3))))
    (j : ι) : ShadedBody (EuclideanSpace ℝ (Fin 3)) where
  toConvexSpaceBody := (V j).toPrismNDim.toConvexSpaceBody
  shade := if j = i₀ then {x₀} else ∅
  measurableSet_shade := by
    by_cases h : j = i₀ <;> simp [h]
  shade_subset := by
    by_cases h : j = i₀
    · subst h; simpa using hx₀
    · simp [h]

open scoped Classical in
@[simp] theorem pointShading_shade (V : ι → Plank a b hab hb1) (i₀ : ι)
    (x₀ : EuclideanSpace ℝ (Fin 3))
    (hx₀ : x₀ ∈ ((V i₀).carrier : Set (EuclideanSpace ℝ (Fin 3)))) (j : ι) :
    (pointShading V i₀ x₀ hx₀ j).shade = if j = i₀ then {x₀} else ∅ := rfl

@[simp] theorem pointShading_carrier (V : ι → Plank a b hab hb1) (i₀ : ι)
    (x₀ : EuclideanSpace ℝ (Fin 3))
    (hx₀ : x₀ ∈ ((V i₀).carrier : Set (EuclideanSpace ℝ (Fin 3)))) (j : ι) :
    ((pointShading V i₀ x₀ hx₀ j).carrier : Set (EuclideanSpace ℝ (Fin 3)))
      = ((V j).carrier : Set (EuclideanSpace ℝ (Fin 3))) := rfl

/-! ## The index form of the overlap bound -/

open Classical in
/-- **Index-form overlap bound for the `inSlabFamilyC`-indexed family** (extra69,
`rem:slabIndexOverlapLe`).

There is a uniform `Nov ≥ 1`, depending only on `(Cset, Cang)`, such that for every configuration
and every index `i ∈ s`, at most `Nov` of the slabs of a pairwise essentially distinct finite
family `used` have `i` in their controlled slab subfamily.

*Why this is the point form in disguise.*  Fix `i` and let `F` be the set of slabs in question.  If
`F = ∅` there is nothing to prove.  Otherwise pick `S₀ ∈ F` and the centre `x₀` of the plank `V i`,
which always lies in `V i`; run `Plank.slab_pointwise_overlap_le` on the *singleton* index family
`{i}`, the shading `Plank.pointShading` at `(i, x₀)`, the max-angle constant `C = 1`, and the ad hoc
slab assignment sending everything to `S₀` — legitimate precisely because `S₀ ∈ F` already witnesses
clause (e) on `{i}`.  The angle hypothesis is `Plank.effectivePlankAngle_self` together with
`a / b ≤ θ`.  Every `S ∈ F` then has `x₀` in its shading union, so `F` injects into the point-form
family at `x₀`.

*Why shrinking the index family is harmless.*  Instantiating at `s := {i}` changes the predicate in
the conclusion from `i ∈ inSlabFamilyC Cset Cang s V S` to `i ∈ inSlabFamilyC Cset Cang {i} V S`,
but by `Plank.mem_inSlabFamilyC` these unfold to `i ∈ s`, resp. `i ∈ {i}`, conjoined with the *same*
carrier and angle conditions, which mention only `V i` and `S`.  So for `i ∈ s` the two memberships
agree and the two filtered subsets of `used` coincide.

This is the degenerate-case-free route: the witnessing point is a point of the *carrier* `V i`,
which is never empty, so no nonemptiness hypothesis on the shading is needed and no carrier-form
generalisation of `Plank.slab_pointwise_overlap_le` is required.  The generalisation suggested by
replacing the shading union by the confinement region is *not* available: the proof of
`Plank.slab_pointwise_overlap_le` passes through `Kakeya.angularClustering` on the shade fibre, and
two planks merely sharing a carrier point need not have a small mutual angle.  Collapsing the family
to one index removes the need for clustering altogether. -/
theorem slab_index_overlap_le (Cset Cang : ℝ≥0) (hCang : 1 ≤ Cang) :
    ∃ Nov : ℕ, 1 ≤ Nov ∧
      ∀ {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} {ι : Type*}
        (s : Finset ι) (V : ι → Plank a b hab hb1)
        {θ : ℝ≥0} (hθ1 : θ ≤ 1) (used : Finset (Slab θ hθ1)),
        0 < θ → a / b ≤ θ →
        (↑used : Set (Slab θ hθ1)).Pairwise
          (fun S S' => PrismNDim.IsEssentiallyDistinct S.toPrismNDim S'.toPrismNDim) →
        ∀ i ∈ s,
          (used.filter (fun S => i ∈ inSlabFamilyC Cset Cang s V S)).card ≤ Nov := by
  classical
  obtain ⟨Nov, hNov1, hpoint⟩ := slab_pointwise_overlap_le 1 Cset Cang hCang
  refine ⟨Nov, hNov1, ?_⟩
  intro a b hab hb1 ι s V θ hθ1 used hθ0 hθa hpairwise i hi
  set F := used.filter (fun S => i ∈ inSlabFamilyC Cset Cang s V S)
  -- Shrinking the index family to `{i}` keeps the (carrier, angle) conditions,
  -- which only mention `V i`.
  have hshrink : ∀ S : Slab θ hθ1, i ∈ inSlabFamilyC Cset Cang s V S →
      i ∈ inSlabFamilyC Cset Cang ({i} : Finset ι) V S := fun _ hS =>
    mem_inSlabFamilyC.mpr ⟨Finset.mem_singleton_self i, (mem_inSlabFamilyC.mp hS).2⟩
  obtain hF | ⟨S₀, hS₀_mem⟩ := F.eq_empty_or_nonempty
  · simp [hF]
  obtain ⟨hS₀_used, hS₀_memC⟩ := Finset.mem_filter.mp hS₀_mem
  set x₀ : EuclideanSpace ℝ (Fin 3) := (V i).center
  have hx₀ : x₀ ∈ ((V i).carrier : Set (EuclideanSpace ℝ (Fin 3))) :=
    center_mem_carrier (V i).toPrismNDim
  let Y : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)) := pointShading V i x₀ hx₀
  have htyp : Kakeya.HasMaxPlankAngleBound ({i} : Finset ι) Y V θ 1 := fun x _ =>
    (Kakeya.maxPlankAngle_mono V (Finset.filter_subset _ _)).trans <|
      Kakeya.maxAngle_le fun j hj k hk => by
        obtain rfl := Finset.mem_singleton.mp hj
        obtain rfl := Finset.mem_singleton.mp hk
        rw [effectivePlankAngle_self, one_mul]
        exact hθa
  let repr : ι → ThickenedPlank θ b hθ1 hb1 := fun _ => (V i).thickened θ hθ1
  let SA : SlabAssignment ({i} : Finset ι) V θ hθ1 repr Cset Cang :=
    { slabOf := fun _ => S₀
      used := used
      slabOf_mem := fun _ _ => hS₀_used
      mem_inSlabFamily := fun j hj => by
        obtain rfl := Finset.mem_singleton.mp hj
        exact hshrink _ hS₀_memC }
  refine (Finset.card_le_card fun S hS => ?_).trans
    (hpoint ({i} : Finset ι) V Y hθ1 repr SA hθ0 htyp
      (fun j _ => (Y j).shade_subset) hpairwise x₀)
  obtain ⟨hS_used, hS_memC⟩ := Finset.mem_filter.mp hS
  exact Finset.mem_filter.mpr
    ⟨hS_used, Set.mem_iUnion₂.mpr ⟨i, hshrink _ hS_memC, by simp [Y]⟩⟩

end Plank

end
