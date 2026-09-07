import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.UnitPlaneMapCapVariation
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.NearbyCellResidueRefinement
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.MultiplicityPreservingVariation

/-!
# Small global cap plus fine-cell constancy

A weak plane map which is constant on fine `delta`-cells can be made
arbitrarily Lipschitz without replacing it by a constant map.  Keep all fine
cells whose genuine plane-map value lies in one common small unit-sphere cap,
then apply the fixed fine-cell residue refinement.

On the final shading, pairs at distance at most `delta` have equal map values,
while arbitrary pairs have map distance at most the cap diameter `eta`.  The
unchanged map is therefore `eta / delta`-Lipschitz.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory Set Finset

attribute [local instance] Classical.propDecidable

/-- Restrict a paper shading to points whose plane-map value lies in a fixed
measurable cap. -/
def paperPlaneMapCapRestriction
    {delta incidence : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {S : WZ1PaperTubeShading F}
    (planeMap : PaperWZ1WeakPlaneMapData S incidence)
    (cap : Set Point3) (hcap : MeasurableSet cap) :
    WZ1PaperTubeShading F where
  carrier index := S.carrier index ∩ planeMap.planeMap ⁻¹' cap
  measurable_carrier index :=
    (S.measurable_carrier index).inter
      (planeMap.measurable hcap)
  subset_body index :=
    Set.inter_subset_left.trans (S.subset_body index)

lemma paperPlaneMapCapRestriction_subshading
    {delta incidence : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {S : WZ1PaperTubeShading F}
    (planeMap : PaperWZ1WeakPlaneMapData S incidence)
    (cap : Set Point3) (hcap : MeasurableSet cap) :
    PaperIsSubshading
      (paperPlaneMapCapRestriction planeMap cap hcap) S :=
  fun _ => Set.inter_subset_left

/-- Since the cap predicate depends only on the spatial point, every point
which survives the cap restriction keeps exactly the same active tube set. -/
lemma paperPlaneMapCapRestriction_pointMultiplicity_eq
    {delta incidence : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {S : WZ1PaperTubeShading F}
    (planeMap : PaperWZ1WeakPlaneMapData S incidence)
    (cap : Set Point3) (hcap : MeasurableSet cap) :
    ∀ point ∈ (paperPlaneMapCapRestriction planeMap cap hcap).union,
      (paperPlaneMapCapRestriction planeMap cap hcap).pointMultiplicity point =
        S.pointMultiplicity point := by
  intro point hpoint
  rcases hpoint with ⟨witness, hwitness⟩
  have hpointCap : planeMap.planeMap point ∈ cap := hwitness.2
  simp only [Kakeya.Streamlined.Shading.pointMultiplicity]
  congr 1
  ext index
  simp [paperPlaneMapCapRestriction, hpointCap]

/-- A cap restriction preserves cubicality when the plane map is constant on
fine paper cells. -/
lemma paperPlaneMapCapRestriction_cubical
    {delta incidence : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {S : WZ1PaperTubeShading F}
    (planeMap : PaperWZ1WeakPlaneMapData S incidence)
    (cap : Set Point3) (hcap : MeasurableSet cap)
    (hcubical : WZ1PaperIsCubicalShading S)
    (hcell : ∀ first second,
      wz1PaperGridIndex delta first =
        wz1PaperGridIndex delta second →
      planeMap.planeMap first = planeMap.planeMap second) :
    WZ1PaperIsCubicalShading
      (paperPlaneMapCapRestriction planeMap cap hcap) := by
  intro index point hpoint other hother
  have hgrid : wz1PaperGridIndex delta other =
      wz1PaperGridIndex delta point :=
    (mem_wz1PaperGridCube delta
      (wz1PaperGridIndex delta point) other).mp hother
  have hotherS : other ∈ S.carrier index :=
    hcubical index point hpoint.1 hother
  have hmap : planeMap.planeMap other = planeMap.planeMap point :=
    hcell other point hgrid
  exact ⟨hotherS, by simpa [hmap] using hpoint.2⟩

/-- One cap in a finite measurable cover of all unit plane-map values carries
at least the average shaded mass.  Overlap between caps is allowed. -/
lemma paper_global_plane_map_cap_refinement
    {delta incidence eta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {S : WZ1PaperTubeShading F}
    (planeMap : PaperWZ1WeakPlaneMapData S incidence)
    (heta : 0 < eta)
    (hcubical : WZ1PaperIsCubicalShading S)
    (hcell : ∀ first second,
      wz1PaperGridIndex delta first =
        wz1PaperGridIndex delta second →
      planeMap.planeMap first = planeMap.planeMap second) :
    ∃ selected : WZ1PaperTubeShading F,
      PaperIsSubshading selected S ∧
      WZ1PaperIsCubicalShading selected ∧
      (∀ point ∈ selected.union,
        selected.pointMultiplicity point = S.pointMultiplicity point) ∧
      (∀ first ∈ selected.union, ∀ second ∈ selected.union,
        dist (planeMap.planeMap first)
          (planeMap.planeMap second) ≤ eta) ∧
      S.mass ≤ (unitPlaneMapCapCount eta : ENNReal) * selected.mass := by
  classical
  let N : ℕ := Nat.ceil (2 * Real.sqrt 3 / eta) + 1
  have hN : 1 ≤ N := by
    dsimp only [N]
    omega
  have hceil : 2 * Real.sqrt 3 / eta ≤
      (Nat.ceil (2 * Real.sqrt 3 / eta) : ℝ) := Nat.le_ceil _
  have hNstrict : 2 * Real.sqrt 3 / eta < (N : ℝ) := by
    dsimp only [N]
    have hsucc : (Nat.ceil (2 * Real.sqrt 3 / eta) : ℝ) <
        (Nat.ceil (2 * Real.sqrt 3 / eta) + 1 : ℕ) := by
      simp
    exact hceil.trans_lt hsucc
  have hNpositive : 0 < (N : ℝ) := by exact_mod_cast hN
  have hdiam : Real.sqrt 3 * (2 * 1 / N) ≤ eta := by
    have hmul : 2 * Real.sqrt 3 < (N : ℝ) * eta := by
      calc
        2 * Real.sqrt 3 = (2 * Real.sqrt 3 / eta) * eta := by
          field_simp [heta.ne']
        _ < (N : ℝ) * eta := by gcongr
    have hdiv : 2 * Real.sqrt 3 / (N : ℝ) < eta := by
      calc
        2 * Real.sqrt 3 / (N : ℝ) <
            ((N : ℝ) * eta) / (N : ℝ) := by gcongr
        _ = eta := by field_simp [hNpositive.ne']
    have heq : Real.sqrt 3 * (2 * 1 / (N : ℝ)) =
        2 * Real.sqrt 3 / (N : ℝ) := by ring
    rw [heq]
    exact hdiv.le
  obtain ⟨cap, hcapMeasurable, hcapCover, hcapDiameter⟩ :=
    grid_covering_cover (0 : Point3) 1 eta (by norm_num)
      N hN heta hdiam
  let Label := Fin 3 → Fin N
  let restricted : Label → WZ1PaperTubeShading F := fun label =>
    paperPlaneMapCapRestriction planeMap (cap label)
      (hcapMeasurable label)
  have hcarrierCover : ∀ index, S.carrier index =
      ⋃ label : Label, (restricted label).carrier index := by
    intro index
    ext point
    constructor
    · intro hpoint
      have hunit := planeMap.unit point ⟨index, hpoint⟩
      have hball : dist (planeMap.planeMap point) (0 : Point3) ≤ 1 := by
        simpa [dist_zero_right, hunit]
      rcases hcapCover (planeMap.planeMap point) hball with
        ⟨label, hlabel⟩
      exact Set.mem_iUnion.mpr ⟨label, hpoint, hlabel⟩
    · intro hpoint
      rcases Set.mem_iUnion.mp hpoint with ⟨label, hlabel⟩
      exact hlabel.1
  have hcarrierMass : ∀ index, volume (S.carrier index) ≤
      ∑ label : Label, volume ((restricted label).carrier index) := by
    intro index
    rw [hcarrierCover index]
    exact MeasureTheory.measure_iUnion_fintype_le
      volume (fun label : Label => (restricted label).carrier index)
  have hmassSum : S.mass ≤ ∑ label : Label, (restricted label).mass := by
    calc
      S.mass = ∑ index : Fin F.card, volume (S.carrier index) := rfl
      _ ≤ ∑ index : Fin F.card,
          ∑ label : Label, volume ((restricted label).carrier index) := by
            exact Finset.sum_le_sum fun index _ => hcarrierMass index
      _ = ∑ label : Label, ∑ index : Fin F.card,
          volume ((restricted label).carrier index) := by
            rw [Finset.sum_comm]
      _ = ∑ label : Label, (restricted label).mass := rfl
  rcases finset_ennreal_pigeonhole
      (s := (Finset.univ : Finset Label)) Finset.univ_nonempty
      (fun label => (restricted label).mass) with
    ⟨label, _, hlabelMass⟩
  let selected := restricted label
  have hmass : S.mass ≤ (Fintype.card Label : ENNReal) * selected.mass :=
    hmassSum.trans hlabelMass
  refine ⟨selected,
    paperPlaneMapCapRestriction_subshading
      planeMap (cap label) (hcapMeasurable label),
    paperPlaneMapCapRestriction_cubical
      planeMap (cap label) (hcapMeasurable label) hcubical hcell,
    paperPlaneMapCapRestriction_pointMultiplicity_eq
      planeMap (cap label) (hcapMeasurable label),
    ?_, ?_⟩
  · intro first hfirst second hsecond
    have hfirstCap : planeMap.planeMap first ∈ cap label := by
      rcases hfirst with ⟨index, hindex⟩
      exact hindex.2
    have hsecondCap : planeMap.planeMap second ∈ cap label := by
      rcases hsecond with ⟨index, hindex⟩
      exact hindex.2
    exact hcapDiameter label
      (planeMap.planeMap first) (planeMap.planeMap second)
      hfirstCap hsecondCap
  · simpa [selected, restricted, Label, unitPlaneMapCapCount, N] using hmass

/-- A genuinely cellwise weak plane map can be refined to Lipschitz constant
`eta / delta` while remaining the same ambient function. -/
theorem paper_global_cap_fine_lipschitz
    {delta incidence eta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {S : WZ1PaperTubeShading F}
    (planeMap : PaperWZ1WeakPlaneMapData S incidence)
    (hdelta : 0 < delta) (heta : 0 < eta)
    (hcubical : WZ1PaperIsCubicalShading S)
    (hcell : ∀ first second,
      wz1PaperGridIndex delta first =
        wz1PaperGridIndex delta second →
      planeMap.planeMap first = planeMap.planeMap second) :
    ∃ (selected : WZ1PaperTubeShading F)
      (selectedPlaneMap : PaperWZ1WeakPlaneMapData selected incidence),
      PaperIsSubshading selected S ∧
      WZ1PaperIsCubicalShading selected ∧
      (∀ point ∈ selected.union,
        selected.pointMultiplicity point = S.pointMultiplicity point) ∧
      S.mass ≤
        (unitPlaneMapCapCount eta : ENNReal) * 27 * selected.mass ∧
      LipschitzWith (Real.toNNReal (eta / delta))
        (fun point : {point : Point3 // point ∈ selected.union} =>
          selectedPlaneMap.planeMap point) := by
  rcases paper_global_plane_map_cap_refinement
      planeMap heta hcubical hcell with
    ⟨capSelected, hcapSub, hcapCubical, hcapMultiplicity,
      hglobalDiameter, hcapMass⟩
  have hsameCell : ∀ first ∈ capSelected.union,
      ∀ second ∈ capSelected.union,
      wz1PaperGridIndex delta first =
        wz1PaperGridIndex delta second →
      dist (planeMap.planeMap first) (planeMap.planeMap second) ≤ 0 := by
    intro first _ second _ hgrid
    rw [hcell first second hgrid]
    simp
  rcases paper_fine_cell_residue_refinement_cubical
      planeMap.planeMap hdelta hcapCubical hsameCell with
    ⟨selected, hselectedSubCap, hselectedCubical,
      hfineVariation, hselectedMultiplicityCap, hresidueMass⟩
  have hselectedSub : PaperIsSubshading selected S := fun index =>
    (hselectedSubCap index).trans (hcapSub index)
  let selectedPlaneMap := paperWeakPlaneMapRestrict planeMap hselectedSub
  have hselectedMultiplicity' : ∀ point ∈ selected.union,
      selected.pointMultiplicity point = S.pointMultiplicity point := by
    intro point hpoint
    have hpointCap : point ∈ capSelected.union := by
      rcases hpoint with ⟨index, hindex⟩
      exact ⟨index, hselectedSubCap index hindex⟩
    exact (hselectedMultiplicityCap point hpoint).trans
      (hcapMultiplicity point hpointCap)
  have hmass : S.mass ≤
      (unitPlaneMapCapCount eta : ENNReal) * 27 * selected.mass := by
    calc
      S.mass ≤ (unitPlaneMapCapCount eta : ENNReal) * capSelected.mass :=
        hcapMass
      _ ≤ (unitPlaneMapCapCount eta : ENNReal) * (27 * selected.mass) := by
        gcongr
      _ = (unitPlaneMapCapCount eta : ENNReal) * 27 * selected.mass := by ring
  have hfineEquality : ∀ first ∈ selected.union, ∀ second ∈ selected.union,
      dist first second ≤ delta →
        selectedPlaneMap.planeMap first =
          selectedPlaneMap.planeMap second := by
    intro first hfirst second hsecond hdist
    have hzero := hfineVariation first hfirst second hsecond hdist
    exact dist_eq_zero.mp (le_antisymm hzero dist_nonneg)
  have hglobalSelected : ∀ first ∈ selected.union,
      ∀ second ∈ selected.union,
      dist (selectedPlaneMap.planeMap first)
        (selectedPlaneMap.planeMap second) ≤ eta := by
    intro first hfirst second hsecond
    have hfirstCap : first ∈ capSelected.union := by
      rcases hfirst with ⟨index, hindex⟩
      exact ⟨index, hselectedSubCap index hindex⟩
    have hsecondCap : second ∈ capSelected.union := by
      rcases hsecond with ⟨index, hindex⟩
      exact ⟨index, hselectedSubCap index hindex⟩
    exact hglobalDiameter first hfirstCap second hsecondCap
  have hlipschitz : LipschitzWith (Real.toNNReal (eta / delta))
      (fun point : {point : Point3 // point ∈ selected.union} =>
        selectedPlaneMap.planeMap point) := by
    have hratioPos : 0 < eta / delta := div_pos heta hdelta
    apply LipschitzWith.of_dist_le_mul
    intro first second
    rw [Real.coe_toNNReal _ hratioPos.le]
    by_cases hnear : dist (first : Point3) (second : Point3) ≤ delta
    · have heq := hfineEquality first first.prop second second.prop hnear
      rw [heq, dist_self]
      positivity
    · have hfar : delta < dist (first : Point3) (second : Point3) :=
        lt_of_not_ge hnear
      have hmap := hglobalSelected first first.prop second second.prop
      calc
        dist (selectedPlaneMap.planeMap first)
            (selectedPlaneMap.planeMap second) ≤ eta := hmap
        _ = (eta / delta) * delta := by field_simp [hdelta.ne']
        _ ≤ (eta / delta) * dist (first : Point3) (second : Point3) := by
          gcongr
  exact ⟨selected, selectedPlaneMap, hselectedSub, hselectedCubical,
    hselectedMultiplicity', hmass, hlipschitz⟩

/-- Choosing a cap of diameter `delta / 20` produces the normalization needed
by relaxed anchored transport: the unchanged cellwise plane map is
`1 / 20`-Lipschitz. -/
theorem paper_global_cap_fine_lipschitz_one_twentieth
    {delta incidence : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {S : WZ1PaperTubeShading F}
    (planeMap : PaperWZ1WeakPlaneMapData S incidence)
    (hdelta : 0 < delta)
    (hcubical : WZ1PaperIsCubicalShading S)
    (hcell : ∀ first second,
      wz1PaperGridIndex delta first =
        wz1PaperGridIndex delta second →
      planeMap.planeMap first = planeMap.planeMap second) :
    ∃ (selected : WZ1PaperTubeShading F)
      (selectedPlaneMap : PaperWZ1WeakPlaneMapData selected incidence),
      PaperIsSubshading selected S ∧
      WZ1PaperIsCubicalShading selected ∧
      (∀ point ∈ selected.union,
        selected.pointMultiplicity point = S.pointMultiplicity point) ∧
      S.mass ≤
        (unitPlaneMapCapCount (delta / 20) : ENNReal) * 27 *
          selected.mass ∧
      LipschitzWith (1 / 20 : NNReal)
        (fun point : {point : Point3 // point ∈ selected.union} =>
          selectedPlaneMap.planeMap point) := by
  have heta : 0 < delta / 20 := div_pos hdelta (by norm_num)
  rcases paper_global_cap_fine_lipschitz
      planeMap hdelta heta hcubical hcell with
    ⟨selected, selectedPlaneMap, hsub, hcubicalSelected,
      hmultiplicity, hmass, hlipschitz⟩
  refine ⟨selected, selectedPlaneMap, hsub, hcubicalSelected,
    hmultiplicity, hmass, ?_⟩
  have hratio : delta / 20 / delta = (1 / 20 : ℝ) := by
    field_simp [hdelta.ne']
  rw [hratio] at hlipschitz
  have hconstant : Real.toNNReal (1 / 20 : ℝ) = (1 / 20 : NNReal) := by
    ext
    norm_num
  rwa [hconstant] at hlipschitz

end Kakeya.Assouad.PureWZ2

end
