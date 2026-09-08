/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Plank.Geometry

/-!
# The anchor/carrier prism API for the active thickened family

Each active index `t` of the thickened representative family of GWZ Lemma 6.13 carries **two**
prisms rather than one.

* The **anchor** `Qanchor t` is the *undilated* thickened representative of
  `Plank.ThickenedRepr`.  It is the scale at which `repr`, the pairwise essential distinctness of
  the active family, the representative fibres, the common fibre size `N` and all counting live.
* The **carrier** `Qcarrier t` is a *fixed dilation* of the anchor.  It is the scale at which the
  thickened shading's carrier, Item 2's fullness, the dense-box/dense-ball shading support and the
  thickened carrier volume live.

The two are tied by the two **directed** containments
`(Qanchor t).carrier ⊆ (Qcarrier t).carrier` and
`(Qcarrier t).carrier ⊆ ((Qanchor t).dilation Ccarrier).carrier`, with `Ccarrier ≥ 1` uniform and
quantified before the configuration.  A disjunction (`PrismNDim.IsCComparable`) would not do: it
leaves open which of the two containments holds and so supplies control in neither direction.

**Pairwise essential distinctness is asserted for the anchor only.**  A fixed dilation does *not*
preserve essential distinctness, so the carrier family is not, and must never be assumed to be,
pairwise essentially distinct.  This is exactly why the split exists: without it the interface has
to pick one scale and pay a dilation where it does not belong.

The shading-support clause `Plank.ThickenedAnchorCarrierData.shade_subset_carrier` is a **field**,
not something to be reconstructed at the point of use: the shading of a plank is only known to sit
in the plank, and the plank only in a *dilation* of its representative, so the containment in the
carrier holds precisely because the carrier is that dilation.  Requiring `Ccarrier` to dominate the
representative-comparability constant `cThk` is what makes the field available.

`Plank.exists_thickenedAnchorCarrierData` builds the data from the clauses that
`Kakeya.representativeWitness_strong_uniform` returns.  The exact anchor volume `8θb²` is
`Plank.volume_indexSet_eq`, and `Plank.ratio_mul_plankVolume_ennreal` puts it in the shape the
symbolic Item 4 reduction's `hcarrierVolume` hypothesis asks for.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal Real

noncomputable section

namespace Plank

variable {ι : Type*}

open scoped Classical in
/-- **The anchor/carrier data of an active thickened family.**  One index type `τ` carrying two
prism maps: the undilated `anchor`, which owns `repr`, essential distinctness and all fibre
counting, and the `carrier`, a fixed `Ccarrier`-dilation of the anchor, which owns the shading
support and all carrier volumes.  See the module docstring for why the split is necessary and why
`anchor_pairwise` is stated for the anchor only. -/
structure ThickenedAnchorCarrierData (τ : Type*) (s' : Finset ι)
    (Y' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3))) (Ccarrier cN : ℝ≥0) (N : ℕ) where
  /-- The representative map, from plank indices to active indices. -/
  repr : ι → τ
  /-- The active index set. -/
  active : Finset τ
  /-- The undilated anchor prism of an active index. -/
  anchor : τ → EnsemblePrism
  /-- The carrier prism of an active index: a fixed dilation of the anchor. -/
  carrier : τ → EnsemblePrism
  /-- The active set is the literal image of `repr`, so no active index has an empty fibre. -/
  active_eq : active = s'.image repr
  /-- Distinct anchors are essentially distinct.  Deliberately **not** asserted for `carrier`. -/
  anchor_pairwise : (↑active : Set τ).Pairwise
    fun t u => PrismNDim.IsEssentiallyDistinct (anchor t) (anchor u)
  /-- The anchor sits inside the carrier. -/
  anchor_subset_carrier : ∀ t ∈ active,
    ((anchor t).carrier : Set (EuclideanSpace ℝ (Fin 3)))
      ⊆ ((carrier t).carrier : Set (EuclideanSpace ℝ (Fin 3)))
  /-- The carrier sits inside the `Ccarrier`-dilation of the anchor. -/
  carrier_subset_dilation : ∀ t ∈ active,
    ((carrier t).carrier : Set (EuclideanSpace ℝ (Fin 3)))
      ⊆ (((anchor t).dilation Ccarrier).carrier : Set (EuclideanSpace ℝ (Fin 3)))
  /-- Every shading sits in the carrier of its representative. -/
  shade_subset_carrier : ∀ i ∈ s',
    (Y' i).shade ⊆ ((carrier (repr i)).carrier : Set (EuclideanSpace ℝ (Fin 3)))
  /-- Every active index has a nonempty `repr`-fibre. -/
  fibre_nonempty : ∀ t ∈ active, (s'.filter fun i => repr i = t).Nonempty
  /-- Lower half of the common fibre size. -/
  fibre_lower : ∀ t ∈ active,
    (N : ℝ) / (cN : ℝ) ≤ ((s'.filter fun i => repr i = t).card : ℝ)
  /-- Upper half of the common fibre size. -/
  fibre_upper : ∀ t ∈ active,
    ((s'.filter fun i => repr i = t).card : ℝ) ≤ (cN : ℝ) * (N : ℝ)

open scoped Classical in
/-- **Construction of the anchor/carrier data from the clauses of the witness.**  The anchor is the
prism map `Qanchor` that the witness returns (the undilated thickened representative), and the
carrier is its fixed `Ccarrier`-dilation, so `carrier_subset_dilation` holds by reflexivity and
`anchor_subset_carrier` is `PrismNDim.self_subset_dilation`.

The shading hypothesis `hshade` is stated at the *dilated* scale, which is what the witness has:
a shading sits in its plank, and a plank in the `cThk`-dilation of its representative, so it is
enough that `Ccarrier` dominate `cThk`.

The conclusion pins down all four components, so the data is not merely some anchor/carrier package
but the one built on the witness's own `repr`, active set and prisms. -/
theorem exists_thickenedAnchorCarrierData {τ : Type*} (s' : Finset ι)
    (Y' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3))) (repr : ι → τ) (𝒯 : Finset τ)
    (Qanchor : τ → EnsemblePrism) (Ccarrier cN : ℝ≥0) (N : ℕ) (hCcarrier : 1 ≤ Ccarrier)
    (hactive : 𝒯 = s'.image repr)
    (hpair : (↑𝒯 : Set τ).Pairwise
      fun t u => PrismNDim.IsEssentiallyDistinct (Qanchor t) (Qanchor u))
    (hshade : ∀ i ∈ s', (Y' i).shade
      ⊆ (((Qanchor (repr i)).dilation Ccarrier).carrier : Set (EuclideanSpace ℝ (Fin 3))))
    (hfibre : ∀ t ∈ 𝒯, (s'.filter fun i => repr i = t).Nonempty ∧
      (N : ℝ) / (cN : ℝ) ≤ ((s'.filter fun i => repr i = t).card : ℝ) ∧
        ((s'.filter fun i => repr i = t).card : ℝ) ≤ (cN : ℝ) * (N : ℝ)) :
    ∃ D : ThickenedAnchorCarrierData τ s' Y' Ccarrier cN N,
      D.repr = repr ∧ D.active = 𝒯 ∧ D.anchor = Qanchor ∧
        D.carrier = fun t => (Qanchor t).dilation Ccarrier := by
  exact ⟨⟨repr, 𝒯, Qanchor, fun t => (Qanchor t).dilation Ccarrier, hactive, hpair,
    fun t _ => PrismNDim.self_subset_dilation (Qanchor t) hCcarrier, fun _ _ => Set.Subset.rfl,
    hshade, fun t ht => (hfibre t ht).1, fun t ht => (hfibre t ht).2.1,
    fun t ht => (hfibre t ht).2.2⟩, rfl, rfl, rfl, rfl⟩

/-! ### The anchor volume of a thickened representative -/

/-- The anchor of an active index is the undilated `θb × b × 1` thickening of the selected plank, so
its volume is exactly `8θb²`.  Composed with `measure_mono` along
`PrismNDim.self_subset_dilation`, this supplies the carrier-volume lower bound of the symbolic
Item 4 reduction; `Plank.ratio_mul_plankVolume_ennreal` puts it in the `ratio · volP` shape that
hypothesis asks for. -/
theorem volume_repr_eq {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} {s : Finset ι}
    {V : ι → Plank a b hab hb1} {θ : ℝ≥0} {hθ1 : θ ≤ 1} {cThk : ℝ≥0}
    (R : ThickenedRepr s V θ hθ1 cThk) {i : ι} (hi : i ∈ s) :
    volume ((R.repr i).carrier : Set (EuclideanSpace ℝ (Fin 3)))
      = 8 * (θ : ENNReal) * (b : ENNReal) * (b : ENNReal) := by
  rw [R.repr_eq i hi]
  exact Plank.volume_thickened (V (R.sel i)) θ hθ1

open scoped Classical in
/-- The anchor volume, stated on the active index set `Plank.ThickenedRepr.indexSet`. -/
theorem volume_indexSet_eq {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} {s : Finset ι}
    {V : ι → Plank a b hab hb1} {θ : ℝ≥0} {hθ1 : θ ≤ 1} {cThk : ℝ≥0}
    (R : ThickenedRepr s V θ hθ1 cThk) :
    ∀ t ∈ R.indexSet, volume ((t.carrier : Set (EuclideanSpace ℝ (Fin 3))))
      = 8 * (θ : ENNReal) * (b : ENNReal) * (b : ENNReal) := by
  intro t ht
  rcases Finset.mem_image.1 ht with ⟨i, hi, rfl⟩
  exact volume_repr_eq R hi

/-! ### The plank/carrier volume ratio -/

/-- The scalar identity behind step 5 of the Item 4 reduction: the carrier/plank volume ratio
`θb/a` applied to the plank volume `8ab` returns the thickened volume `8θb²`.  Needs `a ≠ 0`, since
the ratio is a division. -/
theorem ratio_mul_plankVolume {a b θ : ℝ≥0} (ha : a ≠ 0) :
    (θ * b / a) * (8 * a * b) = 8 * θ * b * b := by
  field_simp [ha]

/-- The `ℝ≥0∞` form of `Plank.ratio_mul_plankVolume`: the step-5 hypothesis
`ratio · volP ≤ |Qcarrier t|` at `ratio = θb/a` and `volP = 8ab` is exactly the statement that the
carrier volume is at least `8θb²`. -/
theorem ratio_mul_plankVolume_ennreal {a b θ : ℝ≥0} (ha : a ≠ 0) :
    ((θ * b / a : ℝ≥0) : ENNReal) * (8 * (a : ENNReal) * (b : ENNReal))
      = 8 * (θ : ENNReal) * (b : ENNReal) * (b : ENNReal) := by
  exact_mod_cast ratio_mul_plankVolume ha

end Plank

end
