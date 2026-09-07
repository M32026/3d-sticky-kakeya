import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.UniformFourBlockRelationDensityStatement

/-!
# Parameter Frostman transfer through a uniform four-block coarsening

Each coarse block is attached to one source representative.  Every source
tube in that parent has supporting-line parameters within `mesh` of the
representative, and all four coarse slots have exactly the representative's
parameters.

For a coarse parameter box of width `r`, the corresponding complete source
parent fibers lie in a source box of width `2r` when
`mesh ≤ rho / 6 ≤ r`.  The four coarse slots and the factor-two parent-fiber
cardinality comparison leave the fixed output constant `8 * C`.
-/

namespace Kakeya.Assouad

/--
Transfer indexed four-parameter Frostman control to one uniform four-block
coarse family.
-/
def UniformFourBlockParameterFrostmanTransferStatement : Prop :=
  ∀ {delta rho : ℝ},
    0 < rho →
    delta ≤ rho →
    ∀ fine : Kakeya.Streamlined.TubeFamily delta,
      ∀ shading : Kakeya.Streamlined.TubeShading fine,
        ∀ data :
            UniformFourBlockRelationData
              (rho := rho) fine shading,
          ∀ representative : Fin data.parentCount → Fin fine.card,
            (∀ parentIndex,
              data.parent (representative parentIndex) = parentIndex) →
            (∀ parentIndex,
              ∀ slot : Fin (data.block parentIndex).card,
                tubeParamsOfTube
                    ((data.block parentIndex).tube slot) =
                  tubeParams (representative parentIndex)) →
            ∀ mesh : ℝ,
              0 ≤ mesh →
              mesh ≤ rho / 6 →
              (∀ fineIndex,
                let reference := representative (data.parent fineIndex)
                |(tubeParams fineIndex).a -
                    (tubeParams reference).a| ≤ mesh ∧
                  |(tubeParams fineIndex).b -
                    (tubeParams reference).b| ≤ mesh ∧
                  |(tubeParams fineIndex).c -
                    (tubeParams reference).c| ≤ mesh ∧
                  |(tubeParams fineIndex).d -
                    (tubeParams reference).d| ≤ mesh) →
              ∀ C : ENNReal,
                1 ≤ C →
                C ≠ ⊤ →
                TubeParameterFrostmanBound fine C →
                  TubeParameterFrostmanBound data.coarse (8 * C)

end Kakeya.Assouad
