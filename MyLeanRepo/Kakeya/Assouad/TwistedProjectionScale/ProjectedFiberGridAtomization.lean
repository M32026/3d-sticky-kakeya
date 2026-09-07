import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ProjectedFiberGridAtomizationStatement
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ProjectedFiberMass
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ProjectedFiberPullbackMass
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.SingleLevelMeasureUniformRefinement
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ProjectedFiberGridAtomizationHelpers

/-!
# Projected-fiber grid atomization

Atomize a projected-fiber multiplicity band into comparable terminal planar
grid cells and pull their union back to a same-family shading.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Assouad

theorem projected_fiber_grid_atomization :
    ProjectedFiberGridAtomizationStatement := by
  intro hfm hpm delta F Y f threshold levelCount bandData
    hmass_pos hmass_top base levels indexBound hbase hcov

  let B := boundedPlanarGridCenters base levels indexBound
  let atom := projectedFiberGridAtom bandData.band base levels
  let C : Finset (Set Point2) := B.image atom
  let μ := projectedFiberMeasure Y f
  let N := B.card

  have hB_nonempty : B.Nonempty := by
    have h1 :
        (0 : ℤ) ∈
          Finset.Icc (-(indexBound : ℤ)) (indexBound : ℤ) := by
      simp <;> omega
    have h2 :
        ((0, 0) : ℤ × ℤ) ∈
          (Finset.Icc
              (-(indexBound : ℤ)) (indexBound : ℤ)).product
            (Finset.Icc
              (-(indexBound : ℤ)) (indexBound : ℤ)) := by
      simp [Finset.mem_product, h1]
    refine ⟨planarGridCenter base levels (0, 0), ?_⟩
    exact Finset.mem_image.mpr ⟨(0, 0), h2, rfl⟩
  have hNpos : 0 < N := Finset.Nonempty.card_pos hB_nonempty

  have hμ_band :
      μ bandData.band = bandData.shading.mass := by
    dsimp only [μ, projectedFiberMeasure]
    have h1 :
        (volume.withDensity
            (projectedFiberMultiplicity Y f)) bandData.band =
          ∫⁻ q in bandData.band,
            projectedFiberMultiplicity Y f q :=
      MeasureTheory.withDensity_apply₀
        (projectedFiberMultiplicity Y f)
        bandData.band_measurable.nullMeasurableSet
    rw [h1]
    exact bandData.mass_identity.symm

  have hmeas : ∀ c ∈ C, MeasurableSet c := by
    intro c hc
    rcases Finset.mem_image.mp hc with ⟨z, _, rfl⟩
    exact gridAtom_measurable
      bandData.band base levels z bandData.band_measurable

  have hdisj :
      ∀ c1 ∈ C, ∀ c2 ∈ C, c1 ≠ c2 → Disjoint c1 c2 := by
    intro c1 hc1 c2 hc2 hne
    rcases Finset.mem_image.mp hc1 with ⟨z1, _, rfl⟩
    rcases Finset.mem_image.mp hc2 with ⟨z2, _, rfl⟩
    have h_idx :
        planarGridIndex base levels z1 ≠
          planarGridIndex base levels z2 := by
      by_contra h
      have h_eq : atom z1 = atom z2 := by
        simp only [atom, projectedFiberGridAtom, h]
      exact hne h_eq
    exact gridAtom_disjoint
      bandData.band base levels z1 z2 h_idx

  have hcov' : bandData.band ⊆ ⋃ c ∈ C, c := by
    simpa [C, finiteAtomUnion, Finset.mem_image] using hcov
  have hcard : C.card ≤ N := Finset.card_image_le

  rcases single_level_measure_uniform_refinement
      μ bandData.band bandData.band_measurable
      (by rw [hμ_band]; exact hmass_pos)
      (by rw [hμ_band]; exact hmass_top)
      N hNpos C hmeas hdisj hcov' hcard with
    ⟨S, hS_sub, hY'meas, hY'pos, hretention, hcomparison⟩

  let Y' := bandData.band ∩ ⋃ c ∈ S, c

  have h_atom_sub_band :
      ∀ z ∈ B, atom z ⊆ bandData.band := by
    intro z _
    exact Set.inter_subset_left

  have h_S_sub_band : ∀ c ∈ S, c ⊆ bandData.band := by
    intro c hc
    rcases Finset.mem_image.mp (hS_sub hc) with ⟨z, hz, rfl⟩
    exact h_atom_sub_band z hz

  have hY'_eq : Y' = ⋃ c ∈ S, c := by
    dsimp only [Y']
    apply Set.Subset.antisymm
    · intro x hx
      exact hx.2
    · intro x hx
      have h_exists :
          ∃ c : Set Point2, c ∈ S ∧ x ∈ c := by
        simpa using hx
      rcases h_exists with ⟨c, hc, hxc⟩
      exact ⟨h_S_sub_band c hc hxc, hx⟩

  have h_inter_eq : ∀ c ∈ S, Y' ∩ c = c := by
    intro c hc
    apply Set.inter_eq_right.mpr
    rw [hY'_eq]
    intro x hx
    simpa using ⟨c, hc, hx⟩

  let S_pos : Finset (Set Point2) :=
    S.filter fun c => μ (Y' ∩ c) ≠ 0
  have hSpos_sub_S : S_pos ⊆ S := Finset.filter_subset _ _
  have hSpos_sub_C : S_pos ⊆ C := hSpos_sub_S.trans hS_sub

  have hSpos_nonempty : S_pos.Nonempty := by
    by_contra h
    have h_empty : S_pos = ∅ := by simpa using h
    have h_all_zero : ∀ c ∈ S, μ (Y' ∩ c) = 0 := by
      intro c hc
      by_contra h2
      have h3 : c ∈ S_pos := by
        rw [Finset.mem_filter]
        exact ⟨hc, h2⟩
      rw [h_empty] at h3
      simp at h3
    have h_all_null : ∀ c ∈ S, μ c = 0 := by
      intro c hc
      simpa [h_inter_eq c hc] using h_all_zero c hc
    have h_disj_S :
        ∀ c1 ∈ S, ∀ c2 ∈ S, c1 ≠ c2 → Disjoint c1 c2 := by
      intro c1 hc1 c2 hc2 hne
      exact hdisj c1 (hS_sub hc1) c2 (hS_sub hc2) hne
    have h_meas_S : ∀ c ∈ S, MeasurableSet c := by
      intro c hc
      exact hmeas c (hS_sub hc)
    have h_sum : μ Y' = ∑ c ∈ S, μ c := by
      rw [hY'_eq]
      exact MeasureTheory.measure_biUnion_finset h_disj_S h_meas_S
    rw [h_sum] at hY'pos
    have h4 : ∑ c ∈ S, μ c = 0 := by
      apply Finset.sum_eq_zero
      intro c hc
      exact h_all_null c hc
    rw [h4] at hY'pos
    simp at hY'pos

  let centers : DiscreteSet 2 :=
    B.filter fun z => atom z ∈ S_pos

  have h_centers_image : centers.image atom = S_pos := by
    apply Finset.Subset.antisymm
    · intro x hx
      rcases Finset.mem_image.mp hx with ⟨z, hz, rfl⟩
      exact (Finset.mem_filter.mp hz).2
    · intro c hc
      rcases Finset.mem_image.mp (hSpos_sub_C hc) with
        ⟨z, hz, rfl⟩
      exact Finset.mem_image.mpr
        ⟨z, Finset.mem_filter.mpr ⟨hz, hc⟩, rfl⟩

  have hcenters_nonempty : centers.Nonempty := by
    rcases hSpos_nonempty with ⟨c, hc⟩
    rcases Finset.mem_image.mp (hSpos_sub_C hc) with
      ⟨z, hz, rfl⟩
    exact ⟨z, Finset.mem_filter.mpr ⟨hz, hc⟩⟩

  have hcenters_sub_B : centers ⊆ B := Finset.filter_subset _ _
  have h_atom_in_Spos : ∀ z ∈ centers, atom z ∈ S_pos := by
    intro z hz
    exact (Finset.mem_filter.mp hz).2

  have h_mass_pos : ∀ z ∈ centers, μ (atom z) ≠ 0 := by
    intro z hz
    have h_in := h_atom_in_Spos z hz
    have h_pos : μ (Y' ∩ atom z) ≠ 0 :=
      (Finset.mem_filter.mp h_in).2
    simpa [h_inter_eq (atom z) (hSpos_sub_S h_in)] using h_pos

  have h_mass_ne_top : ∀ z ∈ centers, μ (atom z) ≠ ⊤ := by
    intro z hz
    have hsub :=
      h_atom_sub_band z (hcenters_sub_B hz)
    have hfin : μ bandData.band ≠ ⊤ := by
      rw [hμ_band]
      exact hmass_top
    exact ne_top_of_le_ne_top hfin (measure_mono hsub)

  let retainedBand : Set Point2 := finiteAtomUnion centers atom

  have h_retained_eq :
      retainedBand = ⋃ c ∈ S_pos, c := by
    dsimp only [retainedBand, finiteAtomUnion]
    have h :
        ⋃ a ∈ centers, atom a =
          ⋃ c ∈ centers.image atom, c := by
      ext x
      simp only [Set.mem_iUnion₂, Finset.mem_image]
      aesop
    rw [h]
    exact congr_arg
      (fun s : Finset (Set Point2) => ⋃ c ∈ s, c)
      h_centers_image

  have h_retained_measurable : MeasurableSet retainedBand := by
    rw [h_retained_eq]
    apply MeasurableSet.biUnion
      (Finset.finite_toSet S_pos).countable
    intro c hc
    exact hmeas c (hSpos_sub_C hc)

  have h_retained_subset : retainedBand ⊆ bandData.band := by
    rw [h_retained_eq]
    intro x hx
    rcases Set.mem_iUnion₂.mp hx with ⟨c, hc, hxc⟩
    exact h_S_sub_band c (hSpos_sub_S hc) hxc

  have h_Y'_retained : μ Y' = μ retainedBand := by
    rw [hY'_eq, h_retained_eq]
    have h_disj_S :
        ∀ c1 ∈ S, ∀ c2 ∈ S, c1 ≠ c2 → Disjoint c1 c2 := by
      intro c1 hc1 c2 hc2 hne
      exact hdisj c1 (hS_sub hc1) c2 (hS_sub hc2) hne
    have h_meas_S : ∀ c ∈ S, MeasurableSet c := by
      intro c hc
      exact hmeas c (hS_sub hc)
    have h_disj_Spos :
        ∀ c1 ∈ S_pos, ∀ c2 ∈ S_pos,
          c1 ≠ c2 → Disjoint c1 c2 := by
      intro c1 hc1 c2 hc2 hne
      exact h_disj_S c1 (hSpos_sub_S hc1)
        c2 (hSpos_sub_S hc2) hne
    have h_meas_Spos : ∀ c ∈ S_pos, MeasurableSet c := by
      intro c hc
      exact hmeas c (hSpos_sub_C hc)
    rw [MeasureTheory.measure_biUnion_finset h_disj_S h_meas_S,
      MeasureTheory.measure_biUnion_finset h_disj_Spos h_meas_Spos]
    symm
    apply Finset.sum_subset hSpos_sub_S
    intro c hc hns
    have h_not : μ (Y' ∩ c) = 0 := by
      by_contra h2
      exact hns (Finset.mem_filter.mpr ⟨hc, h2⟩)
    have h_eq : Y' ∩ c = c := h_inter_eq c hc
    rw [h_eq] at h_not
    exact h_not

  let shading : Kakeya.Streamlined.TubeShading F :=
    projectionPullbackShading
      Y f retainedBand h_retained_measurable

  have h_subshading : IsSubshading shading bandData.shading := by
    rw [bandData.shading_eq]
    exact pullbackSubshading_mono
      Y f retainedBand bandData.band
      h_retained_measurable bandData.band_measurable
      h_retained_subset

  have h_mass_identity : shading.mass = μ retainedBand := by
    have h1 :
        shading.mass =
          ∫⁻ q in retainedBand,
            projectedFiberMultiplicity Y f q :=
      hpm F Y f retainedBand h_retained_measurable
    have h2 :
        μ retainedBand =
          ∫⁻ q in retainedBand,
            projectedFiberMultiplicity Y f q := by
      dsimp only [μ, projectedFiberMeasure]
      exact MeasureTheory.withDensity_apply₀
        (projectedFiberMultiplicity Y f)
        h_retained_measurable.nullMeasurableSet
    rw [h1, h2]

  have h_cast :
      (2 * (↑(Nat.log 2 (2 * N)) + 1) : ENNReal) =
        ((2 * (Nat.log 2 (2 * N) + 1) : ℕ) : ENNReal) := by
    norm_cast

  have h_mass_retention :
      bandData.shading.mass ≤
        ((2 * (Nat.log 2 (2 * N) + 1) : ℕ) : ENNReal) *
          shading.mass := by
    calc
      bandData.shading.mass = μ bandData.band := hμ_band.symm
      _ ≤ (2 * (↑(Nat.log 2 (2 * N)) + 1) : ENNReal) *
          μ Y' := hretention
      _ = ((2 * (Nat.log 2 (2 * N) + 1) : ℕ) : ENNReal) *
          μ Y' := by rw [h_cast]
      _ = ((2 * (Nat.log 2 (2 * N) + 1) : ℕ) : ENNReal) *
          μ retainedBand := by rw [h_Y'_retained]
      _ = ((2 * (Nat.log 2 (2 * N) + 1) : ℕ) : ENNReal) *
          shading.mass := by rw [h_mass_identity]

  have h_centers_separated :
      centers.IsDeltaSeparated (base ^ levels : ℝ)⁻¹ := by
    intro z1 hz1 z2 hz2 hne
    rcases Finset.mem_image.mp (hcenters_sub_B hz1) with
      ⟨idx1, _, rfl⟩
    rcases Finset.mem_image.mp (hcenters_sub_B hz2) with
      ⟨idx2, _, rfl⟩
    have hne_idx : idx1 ≠ idx2 := by
      intro he
      exact hne (by rw [he])
    exact planarGridCenter_separated
      base levels idx1 idx2 hbase hne_idx

  have h_atom_disjoint :
      ∀ z1 ∈ centers, ∀ z2 ∈ centers, z1 ≠ z2 →
        Disjoint (atom z1) (atom z2) := by
    intro z1 hz1 z2 hz2 hne
    rcases Finset.mem_image.mp (hcenters_sub_B hz1) with
      ⟨idx1, _, rfl⟩
    rcases Finset.mem_image.mp (hcenters_sub_B hz2) with
      ⟨idx2, _, rfl⟩
    have hne_idx : idx1 ≠ idx2 := by
      intro he
      exact hne (by rw [he])
    have h_grid :
        planarGridIndex base levels
            (planarGridCenter base levels idx1) ≠
          planarGridIndex base levels
            (planarGridCenter base levels idx2) := by
      rw [planarGridIndex_center_eq base levels idx1 hbase,
        planarGridIndex_center_eq base levels idx2 hbase]
      exact hne_idx
    exact gridAtom_disjoint
      bandData.band base levels _ _ h_grid

  have h_atom_comparable :
      ∀ z1 ∈ centers, ∀ z2 ∈ centers,
        μ (atom z1) ≤ 2 * μ (atom z2) := by
    intro z1 hz1 z2 hz2
    let c1 := atom z1
    let c2 := atom z2
    have hc1 : c1 ∈ S_pos := h_atom_in_Spos z1 hz1
    have hc2 : c2 ∈ S_pos := h_atom_in_Spos z2 hz2
    have h_pos1 : μ (Y' ∩ c1) ≠ 0 :=
      (Finset.mem_filter.mp hc1).2
    have h_pos2 : μ (Y' ∩ c2) ≠ 0 :=
      (Finset.mem_filter.mp hc2).2
    have h_eq1 : Y' ∩ c1 = c1 :=
      h_inter_eq c1 (hSpos_sub_S hc1)
    have h_eq2 : Y' ∩ c2 = c2 :=
      h_inter_eq c2 (hSpos_sub_S hc2)
    have h :=
      hcomparison c1 (hSpos_sub_C hc1)
        c2 (hSpos_sub_C hc2) h_pos1 h_pos2
    rw [h_eq1, h_eq2] at h
    exact h

  have h_twisted_subset :
      twistedUnion shading f ⊆ retainedBand :=
    projectionPullback_twistedUnion_subset
      Y f retainedBand h_retained_measurable

  exact
    ⟨centers, hcenters_nonempty, hcenters_sub_B,
      h_centers_separated,
      (fun z _ =>
        gridAtom_measurable
          bandData.band base levels z
          bandData.band_measurable),
      h_atom_disjoint, h_mass_pos, h_mass_ne_top,
      h_atom_comparable,
      retainedBand,
      by
        dsimp only [atom, retainedBand, finiteAtomUnion],
      h_retained_measurable, h_retained_subset,
      shading, rfl, h_subshading, h_mass_identity,
      h_mass_retention, h_twisted_subset⟩

end Kakeya.Assouad
