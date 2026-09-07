import MyLeanRepo.Kakeya.Cinematic.Section5.SelectedSupportTangentBallCoverInputs
import MyLeanRepo.Kakeya.Cinematic.BipartiteTangencyReduction.Clusters

/-!
# One tangent-ball cover for all selected supports
-/

namespace Kakeya.Cinematic

noncomputable local instance selectedSupportTangentBallCoverProofDecidableEq :
    DecidableEq C2Function := Classical.decEq _

theorem selected_support_tangent_ball_cover :
    SelectedSupportTangentBallCoverStatement := by
  intro hCover family E K D delta diameter epsilon eta tRep DeltaRep C_R₀
    data center hE C_R C_count C_shading C_volume
    fineSetup coarseSetup massExponent refinement degreeSetup
    q_fiber fiberBound heavySetup radius hD hfamily hC_R hradius
  let H := data.ambientSource.cluster center (3 * tRep)
  have htRep_pos : 0 < tRep := data.tRep_pos
  have hdiameter : 0 < 6 * (C_R * tRep) := by positivity
  have hH_subset : H.carrier ⊆ family := by
    exact Set.inter_subset_left.trans data.ambientSource_subset
  have hdiam : ∀ f ∈ H.carrier, ∀ g ∈ H.carrier,
      c2Distance f g ≤ 6 * (C_R * tRep) := by
    intro f hf g hg
    have h := fineSetup.fixed_ambient_diameter f hf g hg
    rw [c2Distance_eq_dist]
    exact h
  rcases finite_family_cluster_cover_polynomial
      hfamily hD hH_subset hdiameter hradius hdiam with
    ⟨centers, hcenters_subset, hcover, depth, hdepth, hcard,
      hcardPolynomial⟩
  have hH_nonempty : H.carrier.Nonempty := by
    rcases degreeSetup.selectedEdges_nonempty with ⟨edge, hedge⟩
    have h_raw : edge ∈ degreeSetup.rawEdges :=
      degreeSetup.selectedEdges_subset hedge
    rw [degreeSetup.rawEdges_eq] at h_raw
    have h_mem :
        edge.2 ∈ degreeSetup.retained ∧
          edge.1 ∈ (degreeSetup.fiber edge.2).carrier :=
      (mem_fineFiberIncidenceEdgesOn degreeSetup.retained
        degreeSetup.fiber edge.1 edge.2).mp h_raw
    have hf : edge.1 ∈ (degreeSetup.fiber edge.2).carrier := h_mem.2
    rw [degreeSetup.fiber_eq] at hf
    exact
      ⟨edge.1,
        fineSetup.point_fiber_ambient
          (fineSetup.source edge.2) hf⟩
  have hcenters_nonempty : centers.Nonempty := by
    by_contra h
    have h_empty : (centers : Set C2Function) = ∅ := by
      simpa [Finset.not_nonempty_iff_eq_empty] using h
    have h_union_empty :
        (⋃ c ∈ (centers : Set C2Function),
            c2Ball c radius) = ∅ := by
      rw [h_empty]
      simp
    rcases hH_nonempty with ⟨f, hf⟩
    have h_f_in :
        f ∈ ⋃ c ∈ (centers : Set C2Function),
          c2Ball c radius :=
      hcover hf
    rw [h_union_empty] at h_f_in
    simp at h_f_in
  have h_toFinset_eq :
      (heavySetup.ambient : Set C2Function) = H.carrier := by
    rw [heavySetup.ambient_eq]
    simp [H, FiniteFunctionFamily.toFinset]
  have hsupport_cover : ∀ coarse ∈ heavySetup.selectedCoarse,
      (incidenceFunctionSupport degreeSetup.selectedEdges
        coarseSetup.coarseData.parent coarse : Set C2Function) ⊆
      ⋃ c ∈ (centers : Set C2Function),
        c2Ball c radius := by
    intro coarse hcoarse
    have hheavy : coarse ∈ heavySetup.heavy :=
      heavySetup.selectedCoarse_subset hcoarse
    have h1 :
        (incidenceFunctionSupport degreeSetup.selectedEdges
          coarseSetup.coarseData.parent coarse : Set C2Function) ⊆
          (heavySetup.ambient : Set C2Function) :=
      heavySetup.support_ambient coarse hheavy
    rw [h_toFinset_eq] at h1
    exact h1.trans hcover
  have hselected_support_cover : ∀ index :
      Fin (selectedCoarseSubfamily coarseSetup.coarseData
        heavySetup.selectedCoarse).card,
      (selectedCoarseIncidenceSupport
        coarseSetup.coarseData degreeSetup.selectedEdges
          heavySetup.selectedCoarse index).carrier ⊆
        ⋃ c ∈ centers, c2Ball c radius := by
    intro index
    exact selectedCoarseIncidenceSupport_cover
      coarseSetup.coarseData degreeSetup.selectedEdges
      heavySetup.selectedCoarse centers radius
      hsupport_cover index
  exact
    ⟨centers, hcenters_subset,
      hcover, depth, hdepth, hcard,
      hcardPolynomial, hcenters_nonempty, hselected_support_cover⟩

lemma SelectedSupportTangentBallCoverData.centers_card_le_paper_parameter
    {family : Set C2Function} {E : Set (ℝ × ℝ)}
    {K D delta diameter epsilon eta tRep DeltaRep C_R₀ : ℝ}
    {data : DyadicFineAssignmentData
      family E K delta diameter epsilon eta tRep DeltaRep C_R₀}
    {center : C2Function}
    {hE : MeasurableSet E}
    {C_R C_count C_shading C_volume : ℝ}
    {fineSetup : AmbientRestrictedFSVSetupData
      data center hE C_R C_count C_shading C_volume}
    {coarseSetup : AmbientRestrictedCoarseSetupData
      data center hE fineSetup}
    {massExponent : ℝ}
    {refinement : AmbientRestrictedLargeBinRefinementData
      data center hE fineSetup coarseSetup massExponent}
    {degreeSetup : RetainedIncidenceDegreeSetupData
      data center hE fineSetup coarseSetup refinement}
    {q_fiber : ℕ}
    {fiberBound : ℝ}
    {heavySetup : RetainedHeavySupportSetupData
      data center hE fineSetup coarseSetup refinement
        degreeSetup q_fiber fiberBound}
    {radius A : ℝ}
    (cover : SelectedSupportTangentBallCoverData
      (D := D) data center hE fineSetup coarseSetup refinement
        degreeSetup q_fiber fiberBound heavySetup radius)
    (hradius : 0 < radius)
    (hA : 1 ≤ A)
    (hidentity : C_R * tRep / A = 8 * radius) :
    (cover.centers.card : ℝ) ≤
      D *
        Real.rpow (48 * A)
          (Real.log D / Real.log 2) := by
  have hApos : 0 < A := lt_of_lt_of_le zero_lt_one hA
  have hscale : C_R * tRep = 8 * radius * A :=
    (div_eq_iff hApos.ne').mp hidentity
  have hradius_le : radius ≤ 6 * (C_R * tRep) := by
    rw [hscale]
    nlinarith
  have hmax :
      max (6 * (C_R * tRep)) radius =
        6 * (C_R * tRep) :=
    max_eq_left hradius_le
  have hratio :
      6 * (C_R * tRep) / radius = 48 * A := by
    rw [hscale]
    field_simp [hradius.ne']
    ring
  simpa [hmax, hratio] using cover.centers_card_polynomial

end Kakeya.Cinematic
