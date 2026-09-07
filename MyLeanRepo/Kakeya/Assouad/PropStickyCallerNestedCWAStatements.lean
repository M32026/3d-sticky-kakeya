import MyLeanRepo.Kakeya.Assouad.PropStickyLeafStatements

/-!
# Caller-rooted nested CWA closure

This is the remaining geometric content of the stable-caller stage.  The
input is not an arbitrary exact-scale cover: it is the caller level of the
single nested strict tree retained by the preparation.

The two conclusions are exactly the two conclusions of
`multiScaleWolffLem`:

* the caller coarse family satisfies nearby-scale CWA;
* every complete historical unit-rescaled caller fiber satisfies hereditary
  nearby-scale cover data.
-/

noncomputable section

namespace Kakeya.Assouad

structure WZ2PaperCallerNestedCWAData
    {delta sourceLoss stableLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading source}
    {caller : Kakeya.Streamlined.AdmissibleScale delta}
    {preparationExponent : ℕ}
    (prepared :
      WZ2PaperCallerStrictPreparationData
        (sourceLoss := sourceLoss)
        (stableLoss := stableLoss)
        shading caller preparationExponent) where
  coarse_cwa_nearby :
    WZ2PaperCWAAtNearbyScales
      prepared.callerStrict.coarse prepared.closureConstant
  rescaledFiber :
    ∀ parent : Fin prepared.callerStrict.coarse.card,
      Nonempty
        (WZ2PaperStableUnitRescaledFamilyData
          prepared.callerStrict.cover parent
          prepared.callerStrict.rho_pos
          prepared.closureConstant)

def WZ2PropStickyPaperCallerNestedCWAStatement : Prop :=
  ∀ {delta sourceLoss stableLoss : ℝ},
    ∀ {source : Kakeya.Streamlined.TubeFamily delta},
      ∀ {shading : WZ1PaperTubeShading source},
        ∀ {caller :
            Kakeya.Streamlined.AdmissibleScale delta},
          ∀ {preparationExponent : ℕ},
            ∀ (prepared :
                WZ2PaperCallerStrictPreparationData
                  (sourceLoss := sourceLoss)
                  (stableLoss := stableLoss)
                  shading caller preparationExponent),
              Nonempty (WZ2PaperCallerNestedCWAData prepared)

end Kakeya.Assouad

end
