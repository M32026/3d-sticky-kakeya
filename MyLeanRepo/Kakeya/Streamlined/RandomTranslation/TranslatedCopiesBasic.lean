import MyLeanRepo.Kakeya.Streamlined.RandomTranslation.TranslateTubeBasic

/-!
# Basic indexed translated copies

This lightweight module defines the indexed union of finitely many common
translations of a tube family.  It has no cover, uniformity, Frostman, or
multiscale theorem dependencies.
-/

noncomputable section

namespace Kakeya.Streamlined.RandomTranslation

/--
The indexed union of `J` translated copies of a tube family. The same
translation vector is applied to every member of one copy.
-/
def translatedCopies {δ : ℝ} (F : TubeFamily δ) (J : ℕ)
    (shift : Fin J → Point3) : TubeFamily δ where
  card := J * F.card
  tube k :=
    let p : Fin J × Fin F.card := finProdFinEquiv.symm k
    translateTube (F.tube p.2) (shift p.1)

end Kakeya.Streamlined.RandomTranslation
