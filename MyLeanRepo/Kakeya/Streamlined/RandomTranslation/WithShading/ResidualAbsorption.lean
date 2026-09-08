import MyLeanRepo.Kakeya.Streamlined.GeometricLemmas.TubeRadius
import MyLeanRepo.Kakeya.Streamlined.RandomTranslation.TranslateUniformStructure
import MyLeanRepo.Kakeya.Streamlined.RandomTranslation.WithShading.ShiftAbsorption

/-!
# Residual shifts absorbed by radius enlargement

If a fine tube lies in a `sigma`-parent, then a residual translation of norm
at most `rho - sigma` lies in the coaxial radius-`rho` enlargement of that
parent.  This is the strict-containment input needed by shared coarse covers.

No essential-distinctness claim is made for the enlarged family.
-/

noncomputable section

open Kakeya.Streamlined.GeometricLemmas

namespace Kakeya.Streamlined.RandomTranslation.WithShading

/-- Enlarge every tube of a family to a common larger radius, preserving its
oriented unit segment. -/
def sameAxisEnlargedFamily {sigma rho : ℝ}
    (G : TubeFamily sigma) : TubeFamily rho where
  card := G.card
  tube i := withRadius rho (G.tube i)

@[simp] lemma sameAxisEnlargedFamily_card
    {sigma rho : ℝ} (G : TubeFamily sigma) :
    (sameAxisEnlargedFamily (rho := rho) G).card = G.card := rfl

@[simp] lemma sameAxisEnlargedFamily_tube
    {sigma rho : ℝ} (G : TubeFamily sigma) (i : Fin G.card) :
    (sameAxisEnlargedFamily (rho := rho) G).tube i =
      withRadius rho (G.tube i) := rfl

/-- A residual translation is absorbed by the radial gap between a parent and
its coaxial enlargement. -/
lemma translate_contained_in_same_axis_enlargement
    {delta sigma rho : ℝ}
    (hsigma : 0 ≤ sigma)
    (hsigma_rho : sigma ≤ rho)
    (fine : Kakeya.DeltaTube delta)
    (parent : Kakeya.DeltaTube sigma)
    (hnested : fine.carrier ⊆ parent.carrier)
    (v : Point3) (hv : ‖v‖ ≤ rho - sigma) :
    (translateTube fine v).carrier ⊆
      (withRadius rho parent).carrier := by
  have hparent :
      (translateTube parent v).carrier ⊆
        (withRadius rho parent).carrier :=
    translate_contained_of_same_axis
      hsigma hsigma_rho parent (withRadius rho parent)
      rfl rfl v hv
  have htranslate :
      (translateTube fine v).carrier ⊆
        (translateTube parent v).carrier := by
    rw [Kakeya.Streamlined.RandomTranslation.translateTube_carrier fine v,
      Kakeya.Streamlined.RandomTranslation.translateTube_carrier parent v]
    exact Set.image_mono hnested
  exact htranslate.trans hparent

end Kakeya.Streamlined.RandomTranslation.WithShading
