import MyLeanRepo.Kakeya.Assouad.PropStickyPaperFiberMultiplicityBandStatements

/-!
# Fiber multiplicity band refinement

For each dyadic level, restrict every fine tube carrier by the point-multiplicity
band of its own complete parent fiber.  Prove the level masses partition the total
mass, select one common level with logarithmic retention, and prove the factor-two
fiber multiplicity band for the selected shading.

## Main results

- `wz2PaperFiberLevelRefined`: level-wise refined shading
- `wz2PaperFiberLevelRefined_mass_partition`: level masses sum to total mass
- `wz2PaperFiberMultiplicityBand_main`: existence of a good level and refinement
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set Finset

attribute [local instance] Classical.propDecidable

/--
Restrict every fine tube carrier by the dyadic point-multiplicity band of its
own complete parent fiber.
-/
def wz2PaperFiberLevelRefined
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ2PaperPartitioningCover fine coarse)
    (shading : WZ1PaperTubeShading fine)
    (level : ℕ) :
    WZ1PaperTubeShading fine where
  carrier source :=
    shading.carrier source ∩
      wz2PaperFiberMultiplicityBand cover shading level source
  measurable_carrier source :=
    (shading.measurable_carrier source).inter
      (wz1PaperDyadicMultiplicityBand_measurable
        (restrictPaperShading
          (cover.fullFiberSubfamily (cover.parent source))
          shading)
        level)
  subset_body source :=
    Set.inter_subset_left.trans (shading.subset_body source)

/-- A dyadic multiplicity band above the log of the family card is empty. -/
lemma paperDyadicBand_empty_of_level_gt_log
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    {level : ℕ}
    (h : Nat.log 2 family.card < level) :
    wz1PaperDyadicMultiplicityBand shading level = ∅ := by
  ext point
  simp only [wz1PaperDyadicMultiplicityBand, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  intro hband
  have hmult : shading.pointMultiplicity point ≤ family.card := by
    change (Finset.univ.filter fun i : Fin family.card => point ∈ shading.carrier i).card ≤ family.card
    have hsubset :
        (Finset.univ.filter fun i : Fin family.card => point ∈ shading.carrier i) ⊆
        (Finset.univ : Finset (Fin family.card)) :=
      Finset.filter_subset _ _
    have h : (Finset.univ.filter fun i : Fin family.card => point ∈ shading.carrier i).card ≤ (Finset.univ : Finset (Fin family.card)).card :=
      Finset.card_le_card hsubset
    simpa using h
  have hpow : (2 ^ level : ENNReal) ≤
      (shading.pointMultiplicity point : ENNReal) := hband.1
  have hle : (2 ^ level : ℕ) ≤ shading.pointMultiplicity point := by
    exact_mod_cast hpow
  have hle2 : (2 ^ level : ℕ) ≤ family.card := hle.trans hmult
  have hlog : level ≤ Nat.log 2 family.card :=
    Nat.le_log_of_pow_le (by norm_num) hle2
  exact not_le.mpr h hlog

/-- If the band is empty, the band subshading has zero mass. -/
lemma paperDyadicBandSubshading_mass_zero_of_empty
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    {level : ℕ}
    (h : wz1PaperDyadicMultiplicityBand shading level = ∅) :
    (wz1PaperDyadicBandSubshading shading level).mass = 0 := by
  simp [wz1PaperDyadicBandSubshading, h, Kakeya.Streamlined.Shading.mass]

/--
Mass of the band subshading on a full fiber, expressed as a sum over ambient
fine indices in that fiber.
-/
lemma fullFiberBandSubshading_mass
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ2PaperPartitioningCover fine coarse)
    (shading : WZ1PaperTubeShading fine)
    (parent : Fin coarse.card)
    (level : ℕ) :
    (wz1PaperDyadicBandSubshading
      (restrictPaperShading (cover.fullFiberSubfamily parent) shading)
      level).mass =
    ∑ source ∈ wz2PaperFullFiberIndices fine coarse parent,
      volume (shading.carrier source ∩
        wz1PaperDyadicMultiplicityBand
          (restrictPaperShading (cover.fullFiberSubfamily parent) shading)
          level) := by
  let fiberShading :=
    restrictPaperShading (cover.fullFiberSubfamily parent) shading
  let indices := wz2PaperFullFiberIndices fine coarse parent
  let equivalence : Fin indices.card ≃ indices :=
    (indices.orderIsoOfFin rfl).toEquiv
  calc
    (wz1PaperDyadicBandSubshading fiberShading level).mass
      = ∑ index : Fin (cover.fullFiberSubfamily parent).family.card,
          volume (fiberShading.carrier index ∩
            wz1PaperDyadicMultiplicityBand fiberShading level) := rfl
    _ = ∑ index : Fin (cover.fullFiberSubfamily parent).family.card,
          volume (shading.carrier
            ((cover.fullFiberSubfamily parent).embedding index) ∩
            wz1PaperDyadicMultiplicityBand fiberShading level) := by
      apply Finset.sum_congr rfl
      intro index _
      rfl
    _ = ∑ source : indices,
          volume (shading.carrier source.1 ∩
            wz1PaperDyadicMultiplicityBand fiberShading level) := by
      exact Fintype.sum_equiv equivalence
        (fun index : Fin (cover.fullFiberSubfamily parent).family.card =>
          volume (shading.carrier
            ((cover.fullFiberSubfamily parent).embedding index) ∩
            wz1PaperDyadicMultiplicityBand fiberShading level))
        (fun source : indices =>
          volume (shading.carrier source.1 ∩
            wz1PaperDyadicMultiplicityBand fiberShading level))
        (fun _ => rfl)
    _ = ∑ source ∈ indices,
          volume (shading.carrier source ∩
            wz1PaperDyadicMultiplicityBand fiberShading level) := by
      exact Finset.sum_coe_sort indices
        (fun source => volume (shading.carrier source ∩
          wz1PaperDyadicMultiplicityBand fiberShading level))

/--
The mass of a level-refined shading equals the sum over parents of the mass
of the corresponding band subshading on each full fiber.
-/
lemma wz2PaperFiberLevelRefined_mass_eq
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ2PaperPartitioningCover fine coarse)
    (shading : WZ1PaperTubeShading fine)
    (level : ℕ) :
    (wz2PaperFiberLevelRefined cover shading level).mass =
    ∑ parent : Fin coarse.card,
      (wz1PaperDyadicBandSubshading
        (restrictPaperShading (cover.fullFiberSubfamily parent) shading)
        level).mass := by
  let f : Fin fine.card → ENNReal := fun source =>
    volume (shading.carrier source ∩
      wz1PaperDyadicMultiplicityBand
        (restrictPaperShading
          (cover.fullFiberSubfamily (cover.parent source))
          shading)
        level)
  have hgroup :
      ∑ source : Fin fine.card, f source =
      ∑ parent : Fin coarse.card,
        ∑ source ∈ Finset.univ with cover.parent source = parent, f source := by
    exact (Finset.sum_fiberwise_of_maps_to
      (s := Finset.univ) (t := Finset.univ)
      (g := cover.parent)
      (fun _ _ => Finset.mem_univ _)
      f).symm
  have hmain : ∀ parent : Fin coarse.card,
      (∑ source ∈ Finset.univ with cover.parent source = parent, f source) =
      (wz1PaperDyadicBandSubshading
        (restrictPaperShading (cover.fullFiberSubfamily parent) shading)
        level).mass := by
    intro parent
    have hfiber_eq :
        (Finset.univ.filter fun source : Fin fine.card => cover.parent source = parent) =
        wz2PaperFullFiberIndices fine coarse parent := by
      ext source
      simp [cover.mem_fullFiber_iff_parent]
    have hsum2 : ∑ source ∈ wz2PaperFullFiberIndices fine coarse parent, f source =
        ∑ source ∈ wz2PaperFullFiberIndices fine coarse parent,
          volume (shading.carrier source ∩
            wz1PaperDyadicMultiplicityBand
              (restrictPaperShading (cover.fullFiberSubfamily parent) shading)
              level) := by
      apply Finset.sum_congr rfl
      intro source hsource
      have hparent : cover.parent source = parent := by
        simpa [cover.mem_fullFiber_iff_parent] using hsource
      dsimp only [f]
      rw [hparent]
    rw [hfiber_eq] at *
    rw [hsum2]
    exact (fullFiberBandSubshading_mass cover shading parent level).symm
  calc
    (wz2PaperFiberLevelRefined cover shading level).mass
      = ∑ source : Fin fine.card, f source := by
      simp [wz2PaperFiberLevelRefined, f, Kakeya.Streamlined.Shading.mass]
      <;> rfl
    _ = ∑ parent : Fin coarse.card,
          ∑ source ∈ Finset.univ with cover.parent source = parent, f source := hgroup
    _ = ∑ parent : Fin coarse.card,
          (wz1PaperDyadicBandSubshading
            (restrictPaperShading (cover.fullFiberSubfamily parent) shading)
            level).mass := by
      apply Finset.sum_congr rfl
      intro parent _
      exact hmain parent

/--
For each parent fiber, the sum of band masses over the ambient level range
equals the full fiber shading mass.
-/
lemma fiberBandSum_eq_fiberMass
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ2PaperPartitioningCover fine coarse)
    (shading : WZ1PaperTubeShading fine)
    (parent : Fin coarse.card) :
    ∑ level ∈ Finset.range (Nat.log 2 fine.card + 1),
      (wz1PaperDyadicBandSubshading
        (restrictPaperShading (cover.fullFiberSubfamily parent) shading)
        level).mass =
    (restrictPaperShading (cover.fullFiberSubfamily parent) shading).mass := by
  let fiberFamily := (cover.fullFiberSubfamily parent).family
  let fiberShading :=
    restrictPaperShading (cover.fullFiberSubfamily parent) shading
  have hle : fiberFamily.card ≤ fine.card := by
    have h : Fintype.card (Fin fiberFamily.card) ≤ Fintype.card (Fin fine.card) :=
      Fintype.card_le_of_injective
        (cover.fullFiberSubfamily parent).embedding
        (cover.fullFiberSubfamily parent).embedding.injective
    simpa using h
  have hlog : Nat.log 2 fiberFamily.card ≤ Nat.log 2 fine.card :=
    Nat.log_mono_right hle
  let smaller := Finset.range (Nat.log 2 fiberFamily.card + 1)
  let larger := Finset.range (Nat.log 2 fine.card + 1)
  have hsubset : smaller ⊆ larger := by
    intro x hx
    have hlt1 : x < Nat.log 2 fiberFamily.card + 1 := Finset.mem_range.mp hx
    have hlt2 : x < Nat.log 2 fine.card + 1 := by linarith [hlog]
    exact Finset.mem_range.mpr hlt2
  have hzero : ∀ level ∈ larger, level ∉ smaller →
      (wz1PaperDyadicBandSubshading fiberShading level).mass = 0 := by
    intro level hln hnot
    have hgt : Nat.log 2 fiberFamily.card < level := by
      have h1 : ¬(level < Nat.log 2 fiberFamily.card + 1) := by
        simpa [smaller, Finset.mem_range] using hnot
      omega
    have hempty : wz1PaperDyadicMultiplicityBand fiberShading level = ∅ :=
      paperDyadicBand_empty_of_level_gt_log hgt
    exact paperDyadicBandSubshading_mass_zero_of_empty hempty
  have hsum_eq : ∑ level ∈ larger, (wz1PaperDyadicBandSubshading fiberShading level).mass =
      ∑ level ∈ smaller, (wz1PaperDyadicBandSubshading fiberShading level).mass := by
    exact (Finset.sum_subset hsubset hzero).symm
  rw [hsum_eq]
  exact (paperDyadicBands_mass_sum (shading := fiberShading)).symm

/--
The level-refined masses partition the total shading mass exactly.
-/
theorem wz2PaperFiberLevelRefined_mass_partition
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ2PaperPartitioningCover fine coarse)
    (shading : WZ1PaperTubeShading fine) :
    ∑ level ∈ Finset.range (Nat.log 2 fine.card + 1),
      (wz2PaperFiberLevelRefined cover shading level).mass =
    shading.mass := by
  let levels := Finset.range (Nat.log 2 fine.card + 1)
  calc
    ∑ level ∈ levels, (wz2PaperFiberLevelRefined cover shading level).mass
      = ∑ level ∈ levels, ∑ parent : Fin coarse.card,
          (wz1PaperDyadicBandSubshading
            (restrictPaperShading (cover.fullFiberSubfamily parent) shading)
            level).mass := by
      apply Finset.sum_congr rfl
      intro level _
      exact wz2PaperFiberLevelRefined_mass_eq cover shading level
    _ = ∑ parent : Fin coarse.card, ∑ level ∈ levels,
          (wz1PaperDyadicBandSubshading
            (restrictPaperShading (cover.fullFiberSubfamily parent) shading)
            level).mass := by
      rw [Finset.sum_comm]
    _ = ∑ parent : Fin coarse.card,
          (restrictPaperShading (cover.fullFiberSubfamily parent) shading).mass := by
      apply Finset.sum_congr rfl
      intro parent _
      exact fiberBandSum_eq_fiberMass cover shading parent
    _ = shading.mass := cover.sum_fullFiberShading_mass shading

/--
The level-refined shading is cubical when the original shading is cubical.
-/
lemma wz2PaperFiberLevelRefined_cubical
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ2PaperPartitioningCover fine coarse)
    (shading : WZ1PaperTubeShading fine)
    (hcubical : WZ1PaperIsCubicalShading shading)
    (level : ℕ) :
    WZ1PaperIsCubicalShading
      (wz2PaperFiberLevelRefined cover shading level) := by
  intro index point hpoint second hsecond
  have hsame :
      wz1PaperGridIndex delta second = wz1PaperGridIndex delta point :=
    (mem_wz1PaperGridCube _ _ _).mp hsecond
  rcases hpoint with ⟨hcarrier, hband⟩
  have hsecondCarrier : second ∈ shading.carrier index :=
    (hcubical.carrier_mem_iff_of_same_cell index hsame.symm).mp hcarrier
  let fiberShading :=
    restrictPaperShading (cover.fullFiberSubfamily (cover.parent index)) shading
  have hfiberCubical : WZ1PaperIsCubicalShading fiberShading :=
    restrictPaperShading_cubical
      (cover.fullFiberSubfamily (cover.parent index)) hcubical
  have hsecondBand :
      second ∈ wz1PaperDyadicMultiplicityBand fiberShading level :=
    (hfiberCubical.dyadicBand_mem_iff_of_same_cell level hsame.symm).mp hband
  exact ⟨hsecondCarrier, hsecondBand⟩

/--
Main theorem: select a common dyadic level retaining a logarithmic fraction of
the total mass, with the factor-two fiber multiplicity band in every parent fiber.
-/
theorem wz2PaperFiberMultiplicityBand_main
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ2PaperPartitioningCover fine coarse)
    (shading : WZ1PaperTubeShading fine)
    (hcubical : WZ1PaperIsCubicalShading shading) :
    Nonempty (WZ2PaperFiberMultiplicityBandData cover shading) := by
  let levels := Finset.range (Nat.log 2 fine.card + 1)
  let levelMass : ℕ → ENNReal := fun level =>
    (wz2PaperFiberLevelRefined cover shading level).mass
  have hlevels_nonempty : levels.Nonempty := by
    simp [levels]
  rcases Finset.exists_max_image levels levelMass hlevels_nonempty with
    ⟨level, hlevel, hmax⟩
  let refined := wz2PaperFiberLevelRefined cover shading level
  have hsum : ∑ candidate ∈ levels, levelMass candidate = shading.mass :=
    wz2PaperFiberLevelRefined_mass_partition cover shading
  have hsum_le :
      ∑ candidate ∈ levels, levelMass candidate ≤
      levels.card • levelMass level :=
    Finset.sum_le_card_nsmul levels levelMass (levelMass level) hmax
  have hcard : (levels.card : ENNReal) =
      (Nat.log 2 fine.card + 1 : ℕ) := by
    simp [levels]
  have hcard_ne_zero : (levels.card : ENNReal) ≠ 0 := by
    exact_mod_cast hlevels_nonempty.card_pos.ne'
  have hcard_ne_top : (levels.card : ENNReal) ≠ ⊤ := by simp
  have hmass : shading.mass / (levels.card : ENNReal) ≤ levelMass level := by
    rw [ENNReal.div_le_iff hcard_ne_zero hcard_ne_top]
    have h : shading.mass ≤ levels.card • levelMass level := by
      rw [←hsum]
      exact hsum_le
    simpa [nsmul_eq_mul, mul_comm] using h
  have hretained :
      shading.mass / ((Nat.log 2 fine.card + 1 : ℕ) : ENNReal) ≤
      refined.mass := by
    simpa [refined, levelMass, hcard] using hmass
  have hrefined_cubical : WZ1PaperIsCubicalShading refined :=
    wz2PaperFiberLevelRefined_cubical cover shading hcubical level
  have hfiber_eq : ∀ (parent : Fin coarse.card) (point : Point3),
      point ∈ (restrictPaperShading (cover.fullFiberSubfamily parent) refined).union →
      (restrictPaperShading (cover.fullFiberSubfamily parent) refined).pointMultiplicity point =
      (restrictPaperShading (cover.fullFiberSubfamily parent) shading).pointMultiplicity point := by
    intro parent point hpoint
    rcases hpoint with ⟨j, hj⟩
    let source := (cover.fullFiberSubfamily parent).embedding j
    have hsource_parent : cover.parent source = parent := by
      have h := cover.fullFiberSubfamily_mem parent j
      exact (cover.mem_fullFiber_iff_parent parent source).mp h
    have hband : point ∈ wz1PaperDyadicMultiplicityBand
        (restrictPaperShading (cover.fullFiberSubfamily parent) shading) level := by
      have hset : wz2PaperFiberMultiplicityBand cover shading level source =
          wz1PaperDyadicMultiplicityBand
            (restrictPaperShading (cover.fullFiberSubfamily parent) shading) level := by
        unfold wz2PaperFiberMultiplicityBand
        rw [hsource_parent]
      have h : point ∈ wz2PaperFiberMultiplicityBand cover shading level source := hj.2
      rw [hset] at h
      exact h
    classical
    simp only [Kakeya.Streamlined.Shading.pointMultiplicity]
    congr 1
    apply Finset.filter_congr
    intro k _
    let source_k := (cover.fullFiberSubfamily parent).embedding k
    have hsource_k_parent : cover.parent source_k = parent := by
      have h := cover.fullFiberSubfamily_mem parent k
      exact (cover.mem_fullFiber_iff_parent parent source_k).mp h
    change
      (point ∈ refined.carrier source_k) ↔
      (point ∈ shading.carrier source_k)
    have h1 : point ∈ refined.carrier source_k ↔
        point ∈ shading.carrier source_k ∧
        point ∈ wz1PaperDyadicMultiplicityBand
          (restrictPaperShading (cover.fullFiberSubfamily parent) shading) level := by
      have hdef : refined.carrier source_k =
          shading.carrier source_k ∩
          wz1PaperDyadicMultiplicityBand
            (restrictPaperShading (cover.fullFiberSubfamily parent) shading) level := by
        dsimp only [refined, wz2PaperFiberLevelRefined]
        apply congr_arg (fun s : Set Point3 => shading.carrier source_k ∩ s)
        unfold wz2PaperFiberMultiplicityBand
        rw [hsource_k_parent]
      rw [hdef]
      simp
    rw [h1]
    exact and_iff_left hband
  have hfiber_band : ∀ (parent : Fin coarse.card) (point : Point3),
      point ∈ (restrictPaperShading (cover.fullFiberSubfamily parent) refined).union →
      (2 ^ level : ENNReal) ≤
          ((restrictPaperShading (cover.fullFiberSubfamily parent) refined).pointMultiplicity point : ENNReal) ∧
      ((restrictPaperShading (cover.fullFiberSubfamily parent) refined).pointMultiplicity point : ENNReal) <
          (2 ^ (level + 1) : ENNReal) := by
    intro parent point hpoint
    rcases hpoint with ⟨j, hj⟩
    let source := (cover.fullFiberSubfamily parent).embedding j
    have hsource_parent : cover.parent source = parent := by
      have h := cover.fullFiberSubfamily_mem parent j
      exact (cover.mem_fullFiber_iff_parent parent source).mp h
    have hband2 : point ∈ wz1PaperDyadicMultiplicityBand
        (restrictPaperShading (cover.fullFiberSubfamily parent) shading) level := by
      have hset : wz2PaperFiberMultiplicityBand cover shading level source =
          wz1PaperDyadicMultiplicityBand
            (restrictPaperShading (cover.fullFiberSubfamily parent) shading) level := by
        unfold wz2PaperFiberMultiplicityBand
        rw [hsource_parent]
      have h : point ∈ wz2PaperFiberMultiplicityBand cover shading level source := hj.2
      rw [hset] at h
      exact h
    have heq : (restrictPaperShading (cover.fullFiberSubfamily parent) refined).pointMultiplicity point =
        (restrictPaperShading (cover.fullFiberSubfamily parent) shading).pointMultiplicity point :=
      hfiber_eq parent point ⟨j, hj⟩
    rw [heq]
    exact hband2
  refine' ⟨{
    level := level,
    refined := refined,
    refined_carrier_eq := by
      intro source
      rfl,
    refined_subshading := by
      intro source
      exact Set.inter_subset_left,
    refined_cubical := hrefined_cubical,
    retained_mass := hretained,
    fiber_pointMultiplicity_eq := hfiber_eq,
    fiber_multiplicity_band := hfiber_band
  }⟩

theorem wz2_paper_fiber_multiplicity_band :
    WZ2PaperFiberMultiplicityBandStatement := by
  intro delta rho fine coarse cover shading hcubical
  exact wz2PaperFiberMultiplicityBand_main cover shading hcubical

end Kakeya.Assouad

end
