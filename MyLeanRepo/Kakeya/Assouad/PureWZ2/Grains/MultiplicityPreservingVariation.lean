import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.SparseQ1OneScaleVariation

/-!
# Fixed-map one-scale variation under multiplicity-preserving restrictions

The amplified parent-pair and orientation refinements are common spatial
restrictions: at every surviving point they preserve total multiplicity.
For a subshading this forces equality of the entire active index finset, not
just equality of its cardinality.  Consequently close counts and a fixed weak
plane map transfer exactly to every later refinement.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory Set Finset

attribute [local instance] Classical.propDecidable

/-- A multiplicity-preserving subshading has exactly the same active tube
indices at every surviving point. -/
lemma paper_active_indices_eq_of_subshading_of_multiplicity_eq
    {delta : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    {source selected : WZ1PaperTubeShading F}
    (hsub : PaperIsSubshading selected source)
    {point : Point3} (hpoint : point ∈ selected.union)
    (hmultiplicity : selected.pointMultiplicity point =
      source.pointMultiplicity point) :
    (Finset.univ.filter fun index : Fin F.card =>
      point ∈ selected.carrier index) =
    (Finset.univ.filter fun index : Fin F.card =>
      point ∈ source.carrier index) := by
  apply Finset.eq_of_subset_of_card_le
  · intro index hindex
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hindex ⊢
    exact hsub index hindex
  · change source.pointMultiplicity point ≤ selected.pointMultiplicity point
    exact hmultiplicity.ge

/-- Carrier membership is preserved tube-by-tube at a surviving point. -/
lemma paper_carrier_mem_iff_of_subshading_of_multiplicity_eq
    {delta : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    {source selected : WZ1PaperTubeShading F}
    (hsub : PaperIsSubshading selected source)
    {point : Point3} (hpoint : point ∈ selected.union)
    (hmultiplicity : selected.pointMultiplicity point =
      source.pointMultiplicity point)
    (index : Fin F.card) :
    point ∈ selected.carrier index ↔ point ∈ source.carrier index := by
  have hactive := paper_active_indices_eq_of_subshading_of_multiplicity_eq
    hsub hpoint hmultiplicity
  have hmem := Finset.ext_iff.mp hactive index
  simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hmem

/-- Close-direction counts are exactly preserved at surviving points. -/
lemma paper_closeDirectionCount_eq_of_subshading_of_multiplicity_eq
    {delta kappa : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    {source selected : WZ1PaperTubeShading F}
    (hsub : PaperIsSubshading selected source)
    {point : Point3} (hpoint : point ∈ selected.union)
    (hmultiplicity : selected.pointMultiplicity point =
      source.pointMultiplicity point)
    (center : Fin F.card) :
    paperCloseDirectionCount selected point center kappa =
      paperCloseDirectionCount source point center kappa := by
  unfold paperCloseDirectionCount
  congr 1
  apply Finset.filter_congr
  intro index _
  rw [paper_carrier_mem_iff_of_subshading_of_multiplicity_eq
    hsub hpoint hmultiplicity index]

/-- A weak plane map restricts to any paper subshading without changing its
underlying ambient function. -/
def paperWeakPlaneMapRestrict
    {delta incidence : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {source selected : WZ1PaperTubeShading F}
    (planeMap : PaperWZ1WeakPlaneMapData source incidence)
    (hsub : PaperIsSubshading selected source) :
    PaperWZ1WeakPlaneMapData selected incidence where
  planeMap := planeMap.planeMap
  measurable := planeMap.measurable
  unit := by
    intro point hpoint
    apply planeMap.unit point
    rcases hpoint with ⟨index, hindex⟩
    exact ⟨index, hsub index hindex⟩
  incidence := by
    intro index point hpoint
    exact planeMap.incidence index point (hsub index hpoint)

/-- One amplified variation step with a plane map fixed on the original
source.  Multiplicity preservation on the current shading transfers every
pointwise source hypothesis needed by the one-scale theorem. -/
theorem paper_fixed_plane_map_one_scale_variation
    {delta rho kappa incidence : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading source current : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    (balanced : PureWZ2BalancedCoverData cover fineShading coarseShading)
    (hfineNonempty : fine.Nonempty)
    (hcoarseNonempty : coarse.Nonempty)
    (hsourceSubFine : PaperIsSubshading source fineShading)
    (planeMap : PaperWZ1WeakPlaneMapData source incidence)
    (hplaneCell : ∀ first second,
      wz1PaperGridIndex delta first =
        wz1PaperGridIndex delta second →
      planeMap.planeMap first = planeMap.planeMap second)
    (hcurrentSub : PaperIsSubshading current source)
    (hcurrentCubical : WZ1PaperIsCubicalShading current)
    (hcurrentMultiplicity : ∀ point ∈ current.union,
      current.pointMultiplicity point = source.pointMultiplicity point)
    (fineMultiplicity : ℕ)
    (hFineMultiplicity : ∀ point ∈ source.union,
      fineMultiplicity ≤ source.pointMultiplicity point)
    (hclose : ∀ point ∈ source.union, ∀ index,
      point ∈ source.carrier index →
      2 * paperCloseDirectionCount source point index kappa ≤
        fineMultiplicity)
    (fiberPower densityPower : ENNReal)
    (hfiber : ∀ parent point,
      (((Finset.univ.filter fun index : Fin fine.card =>
        PureWZ2.selectParent cover index = parent ∧
          point ∈ source.carrier index).card : ℕ) : ENNReal) ≤
        fiberPower *
          ((wz2PaperFullFiberIndices fine coarse parent).card : ENNReal))
    (hdensity : densityPower * fine.enncard ≤
      (fineMultiplicity : ENNReal))
    (hincidenceNonnegative : 0 ≤ incidence)
    (hrho : 0 < rho) (hrhoKappa : rho < kappa)
    (K : ℕ) (hK : 0 < K) (hrhoAligned : rho = (K : ℝ) * delta) :
    ∃ next : WZ1PaperTubeShading fine,
      PaperIsSubshading next current ∧
      WZ1PaperIsCubicalShading next ∧
      (∀ point ∈ next.union,
        next.pointMultiplicity point = current.pointMultiplicity point) ∧
      (∀ point ∈ next.union, ∀ other ∈ next.union,
        dist point other ≤ rho →
          dist (planeMap.planeMap point)
            (planeMap.planeMap other) ≤ rho) ∧
      densityPower ^ 2 * current.mass ≤
        27 * ((2 * fiberPower ^ 2) *
          (wz1OrientationCapCount
            (10 * (incidence + rho / 2) / (kappa - rho)) rho :
              ENNReal)) * next.mass := by
  have hcurrentSubFine : PaperIsSubshading current fineShading :=
    fun index => (hcurrentSub index).trans (hsourceSubFine index)
  let currentPlaneMap := paperWeakPlaneMapRestrict planeMap hcurrentSub
  have hcurrentFineMultiplicity : ∀ point ∈ current.union,
      fineMultiplicity ≤ current.pointMultiplicity point := by
    intro point hpoint
    have hpointSource : point ∈ source.union := by
      rcases hpoint with ⟨index, hindex⟩
      exact ⟨index, hcurrentSub index hindex⟩
    rw [hcurrentMultiplicity point hpoint]
    exact hFineMultiplicity point hpointSource
  have hcurrentClose : ∀ point ∈ current.union, ∀ index,
      point ∈ current.carrier index →
      2 * paperCloseDirectionCount current point index kappa ≤
        fineMultiplicity := by
    intro point hpoint index hindex
    rw [paper_closeDirectionCount_eq_of_subshading_of_multiplicity_eq
      hcurrentSub hpoint (hcurrentMultiplicity point hpoint) index]
    have hpointSource : point ∈ source.union :=
      ⟨index, hcurrentSub index hindex⟩
    exact hclose point hpointSource index (hcurrentSub index hindex)
  have hcurrentFiber := paper_fiber_card_bound_mono_subshading
    hcurrentSub fiberPower hfiber
  rcases paper_amplified_one_scale_nearby_variation_cancel_cardinality
      balanced hfineNonempty hcoarseNonempty hcurrentSubFine hcurrentCubical
      currentPlaneMap hplaneCell fineMultiplicity hcurrentFineMultiplicity
      hcurrentClose fiberPower densityPower hcurrentFiber hdensity
      hincidenceNonnegative hrho hrhoKappa K hK hrhoAligned with
    ⟨next, hnextSub, hnextCubical, hvariation, hnextMultiplicity, hmass⟩
  exact ⟨next, hnextSub, hnextCubical, hnextMultiplicity, hvariation, hmass⟩

end Kakeya.Assouad.PureWZ2

end
