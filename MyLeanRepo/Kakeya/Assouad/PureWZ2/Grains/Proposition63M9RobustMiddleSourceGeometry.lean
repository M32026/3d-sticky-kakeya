import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63M9RobustMiddleAssembly

/-! # Proposition 6.3 M9: terminal source-family geometry -/

noncomputable section

namespace Kakeya.Assouad.PureWZ2
namespace Proposition63M9RobustMiddleData

variable
    {sigma outputLoss r : ℝ}
    {hierarchy : Proposition63M9PreRuntimeHierarchy sigma outputLoss}
    {cutoff : Proposition63M9PreNode3CutoffData hierarchy}
    {source : PureWZ2ExtremalConfiguration sigma
      cutoff.twoCall.schedule.first.sourceLoss r}
    {normalizationExponent : ℕ}
    {root : Proposition63RootNormalizationData
      (outputLoss := cutoff.twoCall.schedule.first.normalizationLoss) source
      normalizationExponent (cutoff.twoCall.schedule.second.sourceLoss / 8)}
    {hr : 0 < r}
    {hrRobust : r ≤ cutoff.twoCall.rootCutoff}
    (middle : Proposition63M9RobustMiddleData cutoff root hr hrRobust)

/-- The family carrying the terminal Lemma 4.12 shading remains in the fixed
paper line class. -/
theorem lemma412Source_lineClass :
    WZ1PaperIsLineClass middle.second.sticky.coarse :=
  Kakeya.Assouad.PureWZ2Section6Cover.coarse_line_class
    middle.second.sticky.cover

/-- The family carrying the terminal Lemma 4.12 shading retains the coarse
cover's essential distinctness. -/
theorem lemma412Source_essentiallyDistinct :
    WZ1PaperIsEssentiallyDistinct middle.second.sticky.coarse :=
  Kakeya.Assouad.PureWZ2Section6Cover.coarse_essentially_distinct
    middle.second.sticky.cover

/-- Every tube in the terminal Lemma 4.12 source family has midpoint in the
fixed local ball inherited from the second rich terminal. -/
theorem lemma412Source_midpoint_le_three :
    ∀ index,
      ‖wz2PaperTubeMidpoint
          (middle.second.sticky.coarse.tube index)‖ ≤ 3 :=
  Kakeya.Assouad.PureWZ2.Proposition63M9RobustMiddleData.coarse_midpoint_local
    middle

/-- The first-chart vertical certificate survives the second restriction,
the Lemma-4.4 representative sampling, and the Lemma-4.7/4.12 spatial
refinements.  Every equality below is the actual stored plane-map equality;
no unrelated weak map is substituted. -/
theorem lemma412_planeMap_vertical_bound
    (hfirst : ∀ point ∈ middle.first.lemma43.shading.union,
      |middle.first.lemma43.planeMap.planeMap point (2 : Fin 3)| ≤ 1 / 2) :
    ∀ point : {point : Point3 //
        point ∈ middle.second.lemma412.shading.union},
      |middle.second.lemma412.localGrains.planeMap point (2 : Fin 3)| ≤
        1 / 2 := by
  intro point
  have hlemma47 : (point : Point3) ∈
      middle.second.lemma47.shading.union := by
    rcases point.prop with ⟨index, hindex⟩
    exact ⟨index, middle.second.lemma412.subshading index hindex⟩
  have hlemma44 : (point : Point3) ∈
      middle.second.lemma44.coarseShading.union := by
    rcases hlemma47 with ⟨index, hindex⟩
    exact ⟨index, middle.second.lemma47.subshading index hindex⟩
  rcases middle.lemma44_planeMap_first_witness point hlemma44 with
    ⟨finePoint, hfinePoint, hmap⟩
  rw [middle.second.lemma412.same_plane_map point, hmap]
  exact hfirst finePoint hfinePoint

end Proposition63M9RobustMiddleData
end Kakeya.Assouad.PureWZ2

end
