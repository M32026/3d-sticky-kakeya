import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.AssemblyStatements

/-!
# Compact assigned cinematic Holder assembly

Closed Section 7 assembly of compactness, one-tube projection area,
selected-curve geometry, the parameter-Frostman fiber cap, and the cinematic
`L^(3/2)` input.
-/

open MeasureTheory Set

namespace Kakeya.Assouad

/--
The same Hölder assembly without a stored-basepoint hypothesis.

The supplied containment theorem already receives exactly the vertical-chart
geometry used by the proof.
-/
theorem compact_assigned_cinematic_holder_from_vertical_chart :
    CompactAssignedCinematicHolderFromVerticalChartStatement := by
  intro h_compact_subshading h_projection_area h_cluster h_assign_cluster
    h_fiber_cap h_containment
  intro delta w hdelta hdelta1 hw hdelta500 hw500
    F hvert C hFrostman Y hY_union f h_ns h0
    c0 hc G hG P hP
  rcases h_compact_subshading F Y with
    ⟨Z, hZ_sub, hZ_mass, hZ_compact⟩
  have hproj := h_projection_area hdelta F hvert Z hZ_compact f
  have himages :
      ∀ i, MeasurableSet (twistedProjection f '' Z.carrier i) :=
    fun i => (hproj i).1
  have harea :
      ∀ i, volume (Z.carrier i) ≤
        ENNReal.ofReal (20 * delta) *
          volume (twistedProjection f '' Z.carrier i) :=
    fun i => (hproj i).2
  have hY_nonempty :
      ∀ i, Z.carrier i ≠ ∅ → Y.carrier i ≠ ∅ := by
    intro i hne hYempty
    have hsub := hZ_sub i
    rw [hYempty] at hsub
    exact hne (Set.subset_empty_iff.mp hsub)
  have hcZ :
      ∀ i, Z.carrier i ≠ ∅ →
        |(tubeParams i).c - c0| ≤ w / 2 :=
    fun i hi => hc i (hY_nonempty i hi)
  have hGZ :
      ∀ i, Z.carrier i ≠ ∅ →
        ∃ g ∈ G.carrier,
          Kakeya.Cinematic.c2Distance
            (slopeCurve f (tubeParams i).a
              (tubeParams i).b (tubeParams i).d) g ≤ w :=
    fun i hi => hG i (hY_nonempty i hi)
  rcases h_fiber_cap h_cluster h_assign_cluster
      delta w hdelta hdelta500 hw hw500
      F C hFrostman Z f h_ns h0 c0 hcZ G hGZ with
    ⟨assign, hassign, hfiber⟩
  have hZ_union : Z.union ⊆ horizontalSlab 0 1 := by
    intro p hp
    rcases hp with ⟨i, hi⟩
    exact hY_union ⟨i, hZ_sub i hi⟩
  have hassign' :
      ∀ i, Z.carrier i ≠ ∅ →
        |(tubeParams i).c - c0| ≤ w / 2 ∧
          Kakeya.Cinematic.c2Distance
            (slopeCurve f (tubeParams i).a
              (tubeParams i).b (tubeParams i).d)
            (assign i) ≤ w := by
    intro i hi
    exact ⟨hcZ i hi, (hassign i hi).2⟩
  have himage :
      ∀ i, Z.carrier i ≠ ∅ →
        cinematicShear c0 ''
            (twistedProjection f '' Z.carrier i) ⊆
          Kakeya.Cinematic.graphNeighborhood
            (assign i) (20 * (delta + w)) :=
    h_containment hdelta hdelta1 hw F hvert
      Z hZ_union f h_ns h0 c0 assign hassign'
  let M : ENNReal :=
    C * Kakeya.realRpowENN (500 * w) 2 * F.enncard
  have hvolume :
      volume (twistedUnion Z f) ≥
        ((Z.mass / ENNReal.ofReal (20 * delta)) / (M * P)) ^ 3 :=
    holder_twistedUnion_volume_of_curve_fiber_cap
      hdelta Z f G assign c0 (20 * (delta + w)) M P
      himages harea
      (fun i hi => (hassign i hi).1)
      himage hfiber hP
  exact ⟨Z, hZ_sub, hZ_mass, hvolume⟩

/-- Compatibility wrapper for the original basepoint-bounded API. -/
theorem compact_assigned_cinematic_holder :
    CompactAssignedCinematicHolderStatement := by
  intro h_compact_subshading h_projection_area h_cluster h_assign_cluster
    h_fiber_cap h_containment
  intro delta w hdelta hdelta1 hw hdelta500 hw500
    F hbase hvert C hFrostman Y hY_union f h_ns h0
    c0 hc G hG P hP
  rcases h_compact_subshading F Y with
    ⟨Z, hZ_sub, hZ_mass, hZ_compact⟩
  have hproj := h_projection_area hdelta F hvert Z hZ_compact f
  have himages :
      ∀ i, MeasurableSet (twistedProjection f '' Z.carrier i) :=
    fun i => (hproj i).1
  have harea :
      ∀ i, volume (Z.carrier i) ≤
        ENNReal.ofReal (20 * delta) *
          volume (twistedProjection f '' Z.carrier i) :=
    fun i => (hproj i).2
  have hY_nonempty :
      ∀ i, Z.carrier i ≠ ∅ → Y.carrier i ≠ ∅ := by
    intro i hne hYempty
    have hsub := hZ_sub i
    rw [hYempty] at hsub
    exact hne (Set.subset_empty_iff.mp hsub)
  have hcZ :
      ∀ i, Z.carrier i ≠ ∅ →
        |(tubeParams i).c - c0| ≤ w / 2 :=
    fun i hi => hc i (hY_nonempty i hi)
  have hGZ :
      ∀ i, Z.carrier i ≠ ∅ →
        ∃ g ∈ G.carrier,
          Kakeya.Cinematic.c2Distance
            (slopeCurve f (tubeParams i).a
              (tubeParams i).b (tubeParams i).d) g ≤ w :=
    fun i hi => hG i (hY_nonempty i hi)
  rcases h_fiber_cap h_cluster h_assign_cluster
      delta w hdelta hdelta500 hw hw500
      F C hFrostman Z f h_ns h0 c0 hcZ G hGZ with
    ⟨assign, hassign, hfiber⟩
  have hZ_union : Z.union ⊆ horizontalSlab 0 1 := by
    intro p hp
    rcases hp with ⟨i, hi⟩
    exact hY_union ⟨i, hZ_sub i hi⟩
  have hassign' :
      ∀ i, Z.carrier i ≠ ∅ →
        |(tubeParams i).c - c0| ≤ w / 2 ∧
          Kakeya.Cinematic.c2Distance
            (slopeCurve f (tubeParams i).a
              (tubeParams i).b (tubeParams i).d)
            (assign i) ≤ w := by
    intro i hi
    exact ⟨hcZ i hi, (hassign i hi).2⟩
  have himage :
      ∀ i, Z.carrier i ≠ ∅ →
        cinematicShear c0 ''
            (twistedProjection f '' Z.carrier i) ⊆
          Kakeya.Cinematic.graphNeighborhood
            (assign i) (20 * (delta + w)) :=
    h_containment hdelta hdelta1 hw F hbase hvert
      Z hZ_union f h_ns h0 c0 assign hassign'
  let M : ENNReal :=
    C * Kakeya.realRpowENN (500 * w) 2 * F.enncard
  have hvolume :
      volume (twistedUnion Z f) ≥
        ((Z.mass / ENNReal.ofReal (20 * delta)) / (M * P)) ^ 3 :=
    holder_twistedUnion_volume_of_curve_fiber_cap
      hdelta Z f G assign c0 (20 * (delta + w)) M P
      himages harea
      (fun i hi => (hassign i hi).1)
      himage hfiber hP
  exact ⟨Z, hZ_sub, hZ_mass, hvolume⟩

end Kakeya.Assouad
