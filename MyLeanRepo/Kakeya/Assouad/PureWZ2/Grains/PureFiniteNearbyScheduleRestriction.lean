import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.PureFiniteNearbySchedule
import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12PureNearbyRestriction

/-!
# Restrict a pure finite nearby schedule

Simultaneous degree regularization is needed only for the finitely many
representative parent maps.  Each arbitrary requested scale reuses its
representative actual-John witness after restricting to the selected fine
family and exactly the coarse parents it hits.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

/--
Recover pure nearby-scale CWA on a selected family from degree uniformity on
the finite representative schedule.  The output constant simultaneously
pays the actual-John fiber-cardinality ratio and the enlarged scale window.
-/
theorem WZ2PaperPureFiniteNearbyScheduleData.regularize
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant outputConstant weight retentionConstant
      degreeConstant : ENNReal}
    {levelCount : ℕ}
    (schedule :
      WZ2PaperPureFiniteNearbyScheduleData
        (fine := fine) ambientConstant outputConstant levelCount)
    (ambient :
      WZ2PaperPureCWAAtNearbyScales fine ambientConstant)
    (selected : Kakeya.Streamlined.TubeSubfamily fine)
    (selectedNonempty : selected.family.Nonempty)
    (houtputFinite : WZ2PaperFiniteErrorConstant outputConstant)
    (hweightZero : weight ≠ 0)
    (hweightTop : weight ≠ ⊤)
    (hglobalRetention :
      weight * fine.enncard ≤
        retentionConstant * selected.family.enncard)
    (hdegree :
      ∀ coordinate,
        ∀ first second :
            Fin (schedule.witness coordinate).scaleData.coarse.card,
          0 <
              ((Finset.univ :
                Finset (Fin selected.family.card)).filter fun source =>
                  (schedule.witness coordinate).scaleData.cover.parent
                      (selected.embedding source) =
                    first).card →
            0 <
              ((Finset.univ :
                Finset (Fin selected.family.card)).filter fun source =>
                  (schedule.witness coordinate).scaleData.cover.parent
                      (selected.embedding source) =
                    second).card →
            (((Finset.univ :
              Finset (Fin selected.family.card)).filter fun source =>
                (schedule.witness coordinate).scaleData.cover.parent
                    (selected.embedding source) =
                  first).card : ENNReal) ≤
              degreeConstant *
                (((Finset.univ :
                  Finset (Fin selected.family.card)).filter fun source =>
                    (schedule.witness coordinate).scaleData.cover.parent
                        (selected.embedding source) =
                      second).card : ENNReal))
    (habsorb :
      max degreeConstant
          ((weight⁻¹ *
              (ambientConstant * retentionConstant * degreeConstant)) *
            ambientConstant) ≤
        outputConstant) :
    WZ2PaperPureCWAAtNearbyScales
      selected.family outputConstant := by
  let selectedPure : WZ2PaperPureTubeSubfamily fine :=
    { family := selected.family
      embedding := selected.embedding
      tube_eq := selected.tube_eq }
  refine
    ⟨ambient.1, houtputFinite,
      ambient.2.2.1.subfamily selectedPure, ?_⟩
  intro requested
  let coordinate := schedule.representative requested
  let source := schedule.witness coordinate
  let selectedCoarse :=
    source.scaleData.cover.hitParentSubfamily selectedPure
  have hselectedCoarseNonempty : selectedCoarse.family.Nonempty :=
    source.scaleData.cover.hitParentSubfamily_nonempty
      selectedPure selectedNonempty
  let restrictedCover :=
    source.scaleData.cover.restrictToHitParents selectedPure
  have hselectedUniform :
      WZ2PaperPureFullFibersAreCUniform
        selected.family selectedCoarse.family degreeConstant :=
    source.scaleData.cover
      |>.restrictToHitParents_fullFiber_uniform_of_subfamily
        source.scaleData.rho_pos.le selectedPure degreeConstant
        (hdegree coordinate)
  let rawScale :=
    source.scaleData.restrictOfWeightedRetention
      selectedPure selectedCoarse hselectedCoarseNonempty restrictedCover
      hweightZero hweightTop hglobalRetention hselectedUniform
  exact
    ⟨{
      rho := source.rho
      requested_le := schedule.requested_le requested
      within_factor := schedule.within_output requested
      scaleData := rawScale.mono habsorb
    }⟩

end Kakeya.Assouad

end
