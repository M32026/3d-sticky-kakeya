/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.AffineTransport
public import Kakeya.DimensionThree.Plank.InnerSlabNonconcentration

/-!
# Transporting multiplicity across the inner normalisation

The Proposition 5.1 split (`Kakeya.Section6PartBData.Remark53Prop51.split`) bounds the
multiplicity of the fine family by a product in which the inner factor is the multiplicity of the
*tube* family on a fibre.  The inner block of GWZ 6.6(B), on the other hand, speaks about the
normalised *plank* family produced by `Kakeya.innerFamilySlabNonconcentration`.  This module is the
bridge between the two, and it is exact: the transport constant is `1`.

## Why the constant is `1`, and why only the shade matters

`ShadedBody.multiplicity s V = (∑ i ∈ s, volume (V i).shade) / volume (⋃ i ∈ s, (V i).shade)`
(`Kakeya/Multiplicity.lean:54`) depends on the family **only through its shades** — the carriers do
not appear.  This is what makes the transport exact, and it is worth being precise about, because
the normalisation treats carrier and shade differently:

* the carrier of the inner plank merely *contains* the affine image of the tube,
  `f '' (T i).carrier ⊆ (Pj i).carrier` — an enlargement, under which essential distinctness would
  not be preserved;
* the shade of the inner plank is the affine image *on the nose*,
  `(Pj i).shade = f '' (T i).shade`, because the inner plank is built by `Kakeya.attachShade` from
  exactly that set (`Kakeya/DimensionThree/Plank/InnerSlabNonconcentration.lean`, the `key`
  construction inside `Kakeya.innerShadedPlankFamily`).

So multiplicity — unlike fullness or maximal density, both of which see the carrier and therefore
pay the normalisation constant `Cnorm` — transports with no loss at all.  Numerator and denominator
are each scaled by the Jacobian of the affine equivalence, and the ratio is unchanged; this is
`ShadedBody.multiplicity_mapAffine` (`Kakeya/DimensionThree/AffineTransport.lean:429`).

## The exposed shade identity

`Kakeya.innerShadedPlankFamily` and `Kakeya.innerFamilySlabNonconcentration` now return the shade
identity as their last clause.  It was already established inside the proof of the former and was
simply not exported; nothing about the construction changed.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal Real ENNReal

noncomputable section

namespace Kakeya

/-- **Multiplicity depends on a shaded family only through its shades.**

Immediate from the definition, but not previously recorded; it is what lets the plank family and
the affine image of the tube family be identified for multiplicity purposes even though their
carriers differ. -/
theorem multiplicity_eq_of_shade_eqOn
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {ι : Type*}
    (s : Finset ι) (V V' : ι → ShadedBody E)
    (h : ∀ i ∈ s, (V i).shade = (V' i).shade) :
    ShadedBody.multiplicity s V = ShadedBody.multiplicity s V' := by
  unfold ShadedBody.multiplicity
  rw [Finset.sum_congr rfl fun i hi => by rw [h i hi],
    Set.iUnion₂_congr fun i hi => by rw [h i hi]]

/-- **Exact multiplicity transport across an affine normalisation.**

If each inner plank's shade is the image of the corresponding tube's shade under an affine
equivalence `F`, the two families have *equal* multiplicity.  The transport constant is `1`. -/
theorem inner_multiplicity_transport_affineEquiv
    {ι : Type*} {a' b' δ : ℝ≥0} {ha'b' : a' ≤ b'} {hb'1 : b' ≤ 1}
    (q : Finset ι) (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3)))
    (Pj : ι → ShadedPlank a' b' ha'b' hb'1)
    (F : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] EuclideanSpace ℝ (Fin 3))
    (hshade : ∀ i ∈ q, ((Pj i).shade : Set (EuclideanSpace ℝ (Fin 3)))
      = F '' ((T i).shade : Set (EuclideanSpace ℝ (Fin 3)))) :
    ShadedBody.multiplicity q (fun i => (Pj i).toShadedBody)
      = ShadedBody.multiplicity q (fun i => (T i).toShadedBody) := by
  let V' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)) := fun i => ((T i).toShadedBody).mapAffine F
  have hshade' : ∀ i ∈ q, ((Pj i).toShadedBody).shade = (V' i).shade := by
    intro i hi
    simpa [V', ShadedBody.mapAffine_shade] using hshade i hi
  rw [multiplicity_eq_of_shade_eqOn q (fun i => (Pj i).toShadedBody) V' hshade']
  exact ShadedBody.multiplicity_mapAffine q (fun i => (T i).toShadedBody) F

/-- **Multiplicity transport for the inner normalised family of GWZ 6.6(B).**

The form consumed by the Section 6(B) assembly: the hypothesis `hshade` is exactly the last clause
returned by `Kakeya.innerFamilySlabNonconcentration`, and `hnorm` is the plank-normalisation datum
already in the caller's hands.  The affine map `f` of a plank normalisation is invertible
(`Kakeya.Plank.exists_affineEquiv_of_isPlankNormalisation`), which is what turns the one-sided image
hypothesis into an equality of multiplicities.

The conclusion is an equality, so it may be used in either direction: left-to-right to feed the
inner plank multiplicity into `Kakeya.multiplicity_pigeon_transfer`, right-to-left to rewrite the
tube-side inner factor of the Proposition 5.1 split into the plank-side factor demanded by the
inner block of `Kakeya.factoringAndMultPropGlobal`. -/
theorem inner_multiplicity_transport
    {ι : Type*} {a b δ a' b' : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
    {ha'b' : a' ≤ b'} {hb'1 : b' ≤ 1} {κ : ℝ}
    (ha : 0 < a) (hκ : 0 < κ) (W : Plank a b hab hb1)
    {f : EuclideanSpace ℝ (Fin 3) →ᵃ[ℝ] EuclideanSpace ℝ (Fin 3)}
    {g : OrthonormalBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 3))}
    (hnorm : Plank.IsPlankNormalisation W f κ g)
    (q : Finset ι) (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3)))
    (Pj : ι → ShadedPlank a' b' ha'b' hb'1)
    (hshade : ∀ i ∈ q, ((Pj i).shade : Set (EuclideanSpace ℝ (Fin 3)))
      = f '' ((T i).shade : Set (EuclideanSpace ℝ (Fin 3)))) :
    ShadedBody.multiplicity q (fun i => (Pj i).toShadedBody)
      = ShadedBody.multiplicity q (fun i => (T i).toShadedBody) := by
  obtain ⟨F, hF⟩ := Plank.exists_affineEquiv_of_isPlankNormalisation ha W hκ hnorm
  have hFim (A : Set (EuclideanSpace ℝ (Fin 3))) :
      (F : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)) '' A
        = (f : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)) '' A := by
    apply congrArg (fun m : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) => m '' A)
    funext x
    exact hF x
  exact inner_multiplicity_transport_affineEquiv q T Pj F (fun i hi => by
    rw [hshade i hi, hFim ((T i).shade)])

end Kakeya

end

end
