import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.TubeParameters

/-!
# Convex prisms for tube-parameter clusters

A box in the four supporting-line parameters is represented geometrically by
an affine prism in the fixed vertical chart.  Unlike a freely translated
coarse `DeltaTube`, this set does not choose an axial unit segment.
-/

noncomputable section

namespace Kakeya.Assouad

/--
The affine prism of points whose height lies in the normalized unit window
and whose two horizontal coordinates stay within `radius` of the line encoded
by `params`.
-/
def tubeParameterPrism (params : TubeParams) (radius : ℝ) : Set Point3 :=
  {point |
    point (2 : Fin 3) ∈ Set.Icc (-1 : ℝ) 1 ∧
      |point (0 : Fin 3) -
        (params.a + params.c * point (2 : Fin 3))| ≤ radius ∧
      |point (1 : Fin 3) -
        (params.b + params.d * point (2 : Fin 3))| ≤ radius}

end Kakeya.Assouad
