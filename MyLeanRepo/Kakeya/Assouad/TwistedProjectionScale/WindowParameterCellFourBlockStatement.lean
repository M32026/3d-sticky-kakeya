import MyLeanRepo.Kakeya.Assouad.AnisotropicRescaling.CoaxialOverlap
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.TubeParameter4OSCellIndexCardinalityStatement

/-!
# Four canonical coarse tubes for one parameter cell in the slope window

The repository `DeltaTube` stores a freely translated unit segment, while
the paper works with supporting lines clipped to a fixed spatial window.
Consequently a parameter cell need not place the full fine carriers inside
one coarse carrier.

The correct selected-scale boundary only covers the current shaded pieces in
`z ∈ [-1,1]`.  Four consecutive radius-`rho` unit segments on the reference
supporting line cover that fixed height window.  Parameter closeness controls
the transverse error at equal height, and the source tube radius supplies
the remaining error.
-/

noncomputable section

namespace Kakeya.Assouad

/--
One four-tube coarse block attached to a reference supporting line and
covering every shaded source piece in the same parameter cell.
-/
structure WindowParameterCellFourBlockData
    {delta rho : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (shading : Kakeya.Streamlined.TubeShading family)
    (indices : Finset (Fin family.card))
    (reference : Fin family.card) where
  coarse : Kakeya.Streamlined.TubeFamily rho
  coarse_card : coarse.card = 4
  coarse_distinct : coarse.IsEssentiallyDistinct
  coarse_vertical : IsInVerticalChart coarse
  coarse_base : HasBoundedBase coarse 23
  coarse_parameters :
    ∀ coarseIndex : Fin coarse.card,
      tubeParamsOfTube (coarse.tube coarseIndex) =
        tubeParams reference
  shading_cover :
    ∀ index ∈ indices,
      shading.carrier index ⊆ coarse.toBodyFamily.union

/--
Direct callable producer for the canonical windowed four-segment block.

The round error budget `3 * delta + 3 * mesh ≤ rho` consists of:

* distance at most `3 * delta` from a source tube point to its own
  supporting line at the same height;
* distance less than `3 * mesh` between two supporting lines whose four
  coordinates differ by at most `mesh` on `[-1,1]`.

The radius-23 base window contains the four fixed-height segments because the
reference parameters lie in `[-12,12]² × [-2,2]²`.
-/
def WindowParameterCellFourBlockInput : Prop :=
  ∀ {delta rho : ℝ},
      0 < delta →
      0 < rho →
      rho ≤ 1 / 8 →
      delta ≤ 1 →
      ∀ mesh : ℝ,
        0 ≤ mesh →
        3 * delta + 3 * mesh ≤ rho →
        ∀ family : Kakeya.Streamlined.TubeFamily delta,
          IsInVerticalChart family →
          (∀ index : Fin family.card,
            |(tubeParams index).a| ≤ 12 ∧
              |(tubeParams index).b| ≤ 12 ∧
              |(tubeParams index).c| ≤ 2 ∧
              |(tubeParams index).d| ≤ 2) →
          ∀ shading : Kakeya.Streamlined.TubeShading family,
            IsInSlopeWindow shading →
            ∀ indices : Finset (Fin family.card),
              indices.Nonempty →
              ∀ reference : Fin family.card,
                reference ∈ indices →
                (∀ index ∈ indices,
                  |(tubeParams index).a -
                      (tubeParams reference).a| ≤ mesh ∧
                    |(tubeParams index).b -
                      (tubeParams reference).b| ≤ mesh ∧
                    |(tubeParams index).c -
                      (tubeParams reference).c| ≤ mesh ∧
                    |(tubeParams index).d -
                      (tubeParams reference).d| ≤ mesh) →
                  Nonempty
                    (WindowParameterCellFourBlockData (rho := rho)
                      shading indices reference)

/--
Construct the direct windowed block producer from coaxial shifted-tube
distinctness.
-/
def WindowParameterCellFourBlockStatement : Prop :=
  CoaxialShiftedTubesEssentiallyDistinctStatement →
    WindowParameterCellFourBlockInput

end Kakeya.Assouad
