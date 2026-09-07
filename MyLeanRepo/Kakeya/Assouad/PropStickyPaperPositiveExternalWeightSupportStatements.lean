import MyLeanRepo.Kakeya.Assouad.PropStickyPaperExternalWeightRegularizationStatements

/-!
# Recover support from positive zero-extended source weights

The fixed literal target family is larger than the packed source image.
Extend an arbitrary weight on the packed target subfamily by zero to the
ambient target indices.  Any ambient subfamily on which this external weight
is strictly positive must lie in the packed target subfamily.

This is the numerical support analogue of
`WZ2PaperZeroExtensionSupportData`.  It does not use target-shading mass.
-/

noncomputable section

namespace Kakeya.Assouad

/-- Zero-extension of weights from a tube subfamily to the ambient indices. -/
def wz2PaperZeroExtendedExternalWeight
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (packed : Kakeya.Streamlined.TubeSubfamily family)
    (sourceWeight : Fin packed.family.card → ENNReal)
    (ambient : Fin family.card) : ENNReal :=
  ∑ source : Fin packed.family.card,
    if packed.embedding source = ambient then sourceWeight source else 0

structure WZ2PaperPositiveExternalWeightSupportData
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (packed : Kakeya.Streamlined.TubeSubfamily family)
    (sourceWeight : Fin packed.family.card → ENNReal)
    (selected : Kakeya.Streamlined.TubeSubfamily family) where
  packedIndex :
    Fin selected.family.card → Fin packed.family.card
  packedIndex_injective :
    Function.Injective packedIndex
  ambient_eq :
    ∀ index,
      packed.embedding (packedIndex index) =
        selected.embedding index
  point_weight_eq :
    ∀ index,
      wz2PaperZeroExtendedExternalWeight
          packed sourceWeight (selected.embedding index) =
        sourceWeight (packedIndex index)
  total_weight_eq :
    (∑ ambient : Fin family.card,
        wz2PaperZeroExtendedExternalWeight
          packed sourceWeight ambient) =
      ∑ source : Fin packed.family.card, sourceWeight source
  selected_weight_eq :
    (∑ index : Fin selected.family.card,
        wz2PaperZeroExtendedExternalWeight
          packed sourceWeight (selected.embedding index)) =
      ∑ index : Fin selected.family.card,
        sourceWeight (packedIndex index)

namespace WZ2PaperPositiveExternalWeightSupportData

/-- Regard the positive-weight ambient selection as a packed subfamily. -/
noncomputable def toPackedSubfamily
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {packed : Kakeya.Streamlined.TubeSubfamily family}
    {sourceWeight : Fin packed.family.card → ENNReal}
    {selected : Kakeya.Streamlined.TubeSubfamily family}
    (data :
      WZ2PaperPositiveExternalWeightSupportData
        packed sourceWeight selected) :
    Kakeya.Streamlined.TubeSubfamily packed.family where
  family := selected.family
  embedding :=
    { toFun := data.packedIndex
      inj' := data.packedIndex_injective }
  tube_eq index := by
    change
      selected.family.tube index =
        packed.family.tube (data.packedIndex index)
    rw [selected.tube_eq, packed.tube_eq]
    exact congrArg family.tube (data.ambient_eq index).symm

end WZ2PaperPositiveExternalWeightSupportData

def WZ2PaperPositiveExternalWeightSupportStatement : Prop :=
  ∀ {delta : ℝ},
    ∀ {family : Kakeya.Streamlined.TubeFamily delta},
      ∀ (packed : Kakeya.Streamlined.TubeSubfamily family),
        ∀ (sourceWeight : Fin packed.family.card → ENNReal),
          ∀ (selected :
              Kakeya.Streamlined.TubeSubfamily family),
            (∀ index,
              0 <
                wz2PaperZeroExtendedExternalWeight
                  packed sourceWeight
                    (selected.embedding index)) →
              Nonempty
                (WZ2PaperPositiveExternalWeightSupportData
                  packed sourceWeight selected)

end Kakeya.Assouad

end
