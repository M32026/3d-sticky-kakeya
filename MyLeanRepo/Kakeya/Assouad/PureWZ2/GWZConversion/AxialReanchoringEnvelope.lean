import MyLeanRepo.Kakeya.Assouad.PropStickyPaperJohnHomotheticEnvelope
import MyLeanRepo.Kakeya.Assouad.PureWZ2.GWZConversion.DirectionConstraint
import MyLeanRepo.Kakeya.Assouad.PureWZ2.GWZConversion.Reanchoring
import MyLeanRepo.Kakeya.Streamlined.RandomTranslation.TubeDensityTestNet.GeometricLemmas

/-!
# Common convex envelope for bounded axial reanchoring

A source tube whose base is obtained from a reanchored tube by an axial shift
of size at most one lies in the factor-100 homothety of the reanchored carrier
about its midpoint.

For a finite nonempty collection of reanchored tubes contained in one convex
test set, take the convex hull of their carriers.  It is a compact convex body
with volume at most the test-set volume.  The existing outer-John homothetic
envelope then gives one common convex envelope, of volume loss `212776173`,
that contains all corresponding source tubes.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

/-- One bounded axial translate is covered by a fixed homothety of the
reanchored carrier. -/
theorem pureWZ2_source_carrier_subset_reanchored_homothety
    {delta : ℝ}
    (hdelta : 0 < delta)
    (source reanchored : Kakeya.DeltaTube delta)
    (shift : ℝ)
    (hdirection :
      reanchored.direction = source.direction)
    (hbase :
      source.base =
        reanchored.base + shift • reanchored.direction)
    (hshift : |shift| ≤ 1) :
    source.carrier ⊆
      AffineMap.homothety
          (wz2PaperTubeMidpoint reanchored) (100 : ℝ) ''
        reanchored.carrier := by
  intro point hpoint
  rcases
      exists_closest_on_axis
        hdelta.le source point hpoint with
    ⟨parameter, hparameter, hpointAxis⟩
  let midpoint := wz2PaperTubeMidpoint reanchored
  let sourceAxisPoint :=
    source.base + parameter • source.direction
  let coefficient := shift + parameter - 1 / 2
  let contractedCoefficient := coefficient / 100
  let contractedAxisPoint :=
    reanchored.base +
      (1 / 2 + contractedCoefficient) •
        reanchored.direction
  let contractedPoint :=
    AffineMap.homothety midpoint (1 / 100 : ℝ) point
  have hcoefficient :
      |coefficient| ≤ 3 / 2 := by
    dsimp only [coefficient]
    rw [abs_le] at hshift ⊢
    constructor <;> linarith [hparameter.1, hparameter.2,
      hshift.1, hshift.2]
  have hcontractedParameter :
      1 / 2 + contractedCoefficient ∈ Set.Icc (0 : ℝ) 1 := by
    dsimp only [contractedCoefficient]
    rw [Set.mem_Icc]
    have hcoefficientBounds := (abs_le.mp hcoefficient)
    constructor <;> linarith
  have hcontractedAxis :
      contractedAxisPoint ∈
        Kakeya.unitSegment
          reanchored.base reanchored.direction :=
    ⟨1 / 2 + contractedCoefficient,
      hcontractedParameter, rfl⟩
  have hsourceAxis :
      sourceAxisPoint =
        midpoint + coefficient • reanchored.direction := by
    dsimp only [sourceAxisPoint, midpoint, coefficient,
      wz2PaperTubeMidpoint]
    rw [hbase, ← hdirection]
    module
  have hcontractedAxisEq :
      contractedAxisPoint =
        AffineMap.homothety midpoint (1 / 100 : ℝ)
          sourceAxisPoint := by
    rw [hsourceAxis, AffineMap.homothety_apply]
    dsimp only [contractedAxisPoint, contractedCoefficient,
      midpoint, wz2PaperTubeMidpoint]
    simp only [vsub_eq_sub, vadd_eq_add]
    module
  have hcontractedDistance :
      dist contractedPoint contractedAxisPoint ≤ delta := by
    rw [hcontractedAxisEq]
    have hscale :
        dist
            (AffineMap.homothety midpoint (1 / 100 : ℝ) point)
            (AffineMap.homothety midpoint (1 / 100 : ℝ)
              sourceAxisPoint) =
          (1 / 100 : ℝ) * dist point sourceAxisPoint := by
      exact homothety_dist (by norm_num) point sourceAxisPoint
    rw [hscale]
    calc
      (1 / 100 : ℝ) * dist point sourceAxisPoint
          ≤ (1 / 100 : ℝ) * delta := by
        exact mul_le_mul_of_nonneg_left
          (by simpa [sourceAxisPoint, dist_comm] using hpointAxis)
          (by norm_num)
      _ ≤ delta := by nlinarith
  have hcontractedCarrier :
      contractedPoint ∈ reanchored.carrier := by
    exact
      Metric.mem_cthickening_of_dist_le
        contractedPoint contractedAxisPoint delta
        (Kakeya.unitSegment
          reanchored.base reanchored.direction)
        hcontractedAxis hcontractedDistance
  refine ⟨contractedPoint, hcontractedCarrier, ?_⟩
  dsimp only [contractedPoint, midpoint]
  rw [AffineMap.homothety_apply,
    AffineMap.homothety_apply]
  simp only [vsub_eq_sub, vadd_eq_add]
  module

/--
One common convex envelope for all source tubes represented by a nonempty
finite collection of reanchored tubes inside a convex test set.
-/
theorem pureWZ2_bounded_axial_reanchoring_common_envelope
    {delta : ℝ}
    (hdelta : 0 < delta)
    {source reanchored : Kakeya.Streamlined.TubeFamily delta}
    (sourceIndex : Fin reanchored.card ↪ Fin source.card)
    (axialShift : Fin reanchored.card → ℝ)
    (direction_eq :
      ∀ index,
        (reanchored.tube index).direction =
          (source.tube (sourceIndex index)).direction)
    (source_base_eq :
      ∀ index,
        (source.tube (sourceIndex index)).base =
          (reanchored.tube index).base +
            axialShift index •
              (reanchored.tube index).direction)
    (axialShift_bound :
      ∀ index, |axialShift index| ≤ 1)
    (selected : Finset (Fin reanchored.card))
    (selected_nonempty : selected.Nonempty)
    (convexSet : Set Point3)
    (convexSet_convex : Convex ℝ convexSet)
    (selected_contained :
      ∀ index ∈ selected,
        (reanchored.tube index).carrier ⊆ convexSet) :
    ∃ envelope : Set Point3,
      Convex ℝ envelope ∧
      volume envelope ≤
        (212776173 : ENNReal) * volume convexSet ∧
      ∀ index ∈ selected,
        (source.tube (sourceIndex index)).carrier ⊆ envelope := by
  let selectedUnion : Set Point3 :=
    ⋃ index ∈ selected, (reanchored.tube index).carrier
  let convexBody : Set Point3 :=
    convexHull ℝ selectedUnion
  have hselectedCompact :
      IsCompact convexBody := by
    exact
      Kakeya.Streamlined.RandomTranslation.isCompact_convexHull_finite_union
          selected
          (fun index => (reanchored.tube index).carrier)
          (by
            intro index hindex
            exact
              ⟨wz2_paper_ordinary_tube_carrier_compact
                  (reanchored.tube index) hdelta,
                wz2_paper_ordinary_tube_carrier_convex
                  (reanchored.tube index)⟩)
  have hconvexBody : Convex ℝ convexBody :=
    convex_convexHull ℝ selectedUnion
  have hconvexBodySubset : convexBody ⊆ convexSet := by
    apply convexHull_min
    · intro point hpoint
      simp only [selectedUnion, Set.mem_iUnion] at hpoint
      rcases hpoint with ⟨index, hpoint⟩
      rcases hpoint with ⟨hindex, hpoint⟩
      exact selected_contained index hindex hpoint
    · exact convexSet_convex
  rcases selected_nonempty with ⟨reference, hreference⟩
  have hreferenceCarrier :
      (reanchored.tube reference).carrier ⊆ convexBody := by
    intro point hpoint
    apply subset_convexHull ℝ selectedUnion
    exact Set.mem_iUnion.mpr
      ⟨reference, Set.mem_iUnion.mpr ⟨hreference, hpoint⟩⟩
  have hconvexBodyInterior :
      (interior convexBody).Nonempty := by
    exact
      (Kakeya.Streamlined.RandomTranslation.deltaTube_nonempty_interior
          hdelta (reanchored.tube reference)).mono
        (interior_mono hreferenceCarrier)
  have hbody :
      JohnEllipsoid.IsConvexBody convexBody :=
    ⟨hconvexBody, hselectedCompact, hconvexBodyInterior⟩
  rcases
      wz2_paper_john_homothetic_envelope
        convexBody hbody with
    ⟨envelope, henvelopeConvex, henvelopeVolume,
      henvelopeContains⟩
  refine
    ⟨envelope, henvelopeConvex,
      henvelopeVolume.trans ?_, ?_⟩
  · exact
      mul_le_mul_left'
        (measure_mono hconvexBodySubset)
        (212776173 : ENNReal)
  · intro index hindex
    have hcarrier :
        (reanchored.tube index).carrier ⊆ convexBody := by
      intro point hpoint
      apply subset_convexHull ℝ selectedUnion
      exact Set.mem_iUnion.mpr
        ⟨index, Set.mem_iUnion.mpr ⟨hindex, hpoint⟩⟩
    have hmidpoint :
        wz2PaperTubeMidpoint (reanchored.tube index) ∈
          convexBody :=
      hcarrier
        (wz2_paper_tubeMidpoint_mem_carrier
          (reanchored.tube index) hdelta.le)
    exact
      (pureWZ2_source_carrier_subset_reanchored_homothety
        hdelta
        (source.tube (sourceIndex index))
        (reanchored.tube index)
        (axialShift index)
        (direction_eq index)
        (source_base_eq index)
        (axialShift_bound index)).trans
        ((Set.image_mono hcarrier).trans
          (henvelopeContains
            (wz2PaperTubeMidpoint (reanchored.tube index))
            hmidpoint))

end Kakeya.Assouad

end
