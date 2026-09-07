import MyLeanRepo.Kakeya.Assouad.PropStickyPaperRefinementHelpers

/-!
# Zero extension of a paper shading from a tube subfamily

After the final fine-tube packing, the selected target tubes form a genuine
subfamily of the fixed literal family used by the geometric tree.  Extend the
packed shading by the empty set on every unselected ambient tube.

The output records exact support, mass, union, and cubicality.  These facts
allow the existing finite nearby-scale regularization theorem to run on the
fixed ambient family while ensuring that its positive-mass output still lies
inside the packed essentially-distinct subfamily.
-/

noncomputable section

namespace Kakeya.Assouad

structure WZ2PaperSubfamilyZeroExtensionData
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (selected : Kakeya.Streamlined.TubeSubfamily family)
    (shading : WZ1PaperTubeShading selected.family) where
  ambientShading : WZ1PaperTubeShading family
  carrier_embedding :
    ∀ index,
      ambientShading.carrier (selected.embedding index) =
        shading.carrier index
  carrier_support :
    ∀ ambient point,
      point ∈ ambientShading.carrier ambient →
        ∃ index,
          selected.embedding index = ambient ∧
            point ∈ shading.carrier index
  mass_eq : ambientShading.mass = shading.mass
  union_eq : ambientShading.union = shading.union
  cubical :
    WZ1PaperIsCubicalShading shading →
      WZ1PaperIsCubicalShading ambientShading

def WZ2PaperSubfamilyZeroExtensionStatement : Prop :=
  ∀ {delta : ℝ},
    ∀ {family : Kakeya.Streamlined.TubeFamily delta},
      ∀ (selected : Kakeya.Streamlined.TubeSubfamily family),
        ∀ (shading : WZ1PaperTubeShading selected.family),
          Nonempty
            (WZ2PaperSubfamilyZeroExtensionData selected shading)

end Kakeya.Assouad

end
