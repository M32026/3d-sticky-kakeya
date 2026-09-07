import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.PureHierarchyQuantitativeExactTerminal
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.PureHierarchyPopularityAssembly
import MyLeanRepo.Kakeya.Assouad.PureWZ2.PaperShadingMassFinite

/-!
# Popularity assembly for a mixed exact-terminal hierarchy

This applies the Corollary-5.6 popularity, compactification, endpoint
reanchoring, and unique-parent argument to a raw hierarchy whose last level
has the exact non-cubical terminal carrier.  The equal-union partial-cell
shadow supplies the slab AD estimate without asserting cubicality.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

/-- The common mixed-terminal popularity output.  Besides the anchored
hierarchy, it retains a conditional quantitative projection: whenever the
exact terminal input carries a factor-two multiplicity band and a source-mass
lower bound, the same run returns the corresponding pointwise cap and mass
retention on the compact final shading. -/
structure PureWZ2MixedPopularityOutput
    {sigma inputLoss delta finalLoss hierarchyLoss : ℝ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    (data : PureWZ2MixedRawHierarchyData source finalLoss hierarchyLoss) where
  hierarchy : PureWZ2LocallyLinearHierarchyData
    source hierarchyLoss hierarchyLoss
  levelCount_eq : hierarchy.hierarchy.levelCount = data.levelCount
  quantitative :
    ∀ (densityLoss : ℝ) (multiplicity : ℕ),
      0 < multiplicity →
      data.shading.HasConstantMultiplicity multiplicity (2 * multiplicity) →
      Kakeya.realRpowENN delta densityLoss *
          (wz1PaperBodyFamily source.family).mass ≤ data.shading.mass →
        { output : PureWZ2QuantitativeLocallyLinearHierarchyData
            source hierarchyLoss hierarchyLoss densityLoss //
          output.hierarchy = hierarchy }

namespace PureWZ2MixedRawHierarchyData

/-- Run mixed-terminal popularity while retaining the exact hierarchy-depth
index needed by the outer source-scale budget. -/
theorem toPopularityOutputWithLevelCount
    {sigma inputLoss delta finalLoss hierarchyLoss : ℝ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    (data : PureWZ2MixedRawHierarchyData source finalLoss hierarchyLoss)
    (hbridge : PureWZ2PaperADBridgeStatement)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hhierarchyLoss : 0 < hierarchyLoss)
    (hfinalHierarchy : finalLoss ≤ hierarchyLoss)
    (hfinalLevelZero : finalLoss ≤
      hierarchyLoss / (4 * (data.levelCount : ℝ)))
    (hdeltaStrict : delta < 1)
    (hgeometric : Real.rpow delta
      (hierarchyLoss / (data.levelCount : ℝ)) < 1 / 9)
    (hlevelZero :
      pureWZ2HierarchySlabConstant delta sigma finalLoss *
          ENNReal.ofReal (12 * Real.rpow delta
            (hierarchyLoss / (data.levelCount : ℝ))) <
        Kakeya.realRpowENN delta
          (sigma + hierarchyLoss /
            (4 * (data.levelCount : ℝ))))
    (hremoved :
      pureWZ2HierarchySlabConstant delta sigma finalLoss *
          ENNReal.ofReal
            (12 * ∑ level : Fin data.levelCount,
              Real.rpow
                (wz1Corollary26Scale delta
                  data.levelCount level) hierarchyLoss) ≤
        ENNReal.ofReal (1 / 3) *
          MeasureTheory.volume data.shading.union)
    (hfinalVolume :
      Kakeya.realRpowENN delta (sigma + hierarchyLoss) <
        ENNReal.ofReal (2 / 3) *
          Kakeya.realRpowENN delta (sigma + finalLoss)) :
    Nonempty (PureWZ2MixedPopularityOutput data) := by
  let N := data.levelCount
  have hNpos : 0 < N := by
    exact lt_of_lt_of_le (by norm_num) data.levelCount_two
  let Z := data.shading
  let rawTrapezoids : Fin N → Finset WZ1VerticalTrapezoid :=
    data.trapezoids
  let L : Fin N → ℝ := fun level =>
    Real.rpow (wz1Corollary26Scale delta N level)
      (1 / 2 + hierarchyLoss)
  let Amax : ENNReal :=
    pureWZ2HierarchySlabConstant delta sigma finalLoss
  have hdelta := source.extremal.delta_pos
  have hdeltaOne := source.extremal.delta_le_one
  have hZSource : PureWZ2PaperIsSubshading Z source.shading :=
    data.subshading
  have hLnonneg : ∀ level, 0 ≤ L level := by
    intro level
    exact Real.rpow_nonneg
      (Real.rpow_pos_of_pos hdelta _).le _
  have hLeq : ∀ level, L level =
      Real.rpow (wz1Corollary26Scale delta N level)
        (1 / 2 + hierarchyLoss) := fun _ => rfl
  have hZheight : ∀ point ∈ Z.union,
      point 2 ∈ Set.Icc (-1 : ℝ) 1 := by
    intro point hpoint
    have hbox := paperShading_subset_axisBox
      (Z := Z) hpoint
    exact abs_le.mp (by
      simpa [Kakeya.Streamlined.axisBox] using hbox.2.2)
  have hcoverage : ∀ level, ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      horizontalSlice Z.union z ≠ ∅ →
        ∃ trapezoid ∈ rawTrapezoids level, z ∈ trapezoid.core := by
    simpa [rawTrapezoids, Z] using data.active_height_coverage
  have hslopeApprox : ∀ level, ∀ trapezoid ∈ rawTrapezoids level,
      ∀ z ∈ trapezoid.core, horizontalSlice Z.union z ≠ ∅ →
        |data.sourceGlobalGrains.slope z - trapezoid.affine z| ≤
          wz1Corollary26Scale delta N level := by
    simpa [rawTrapezoids, Z, N] using data.slope_approximation
  have hslab : ∀ a b : ℝ, a ≤ b →
      volume (Z.union ∩ horizontalSlab a b) ≤
        Amax * ENNReal.ofReal (b - a) := by
    intro a b hab
    let shadow := pureWZ2PartialActiveCellShading Z hdelta
    have hunion : shadow.union = Z.union :=
      pureWZ2PartialActiveCellShading_union Z hdelta
    have haxis : ∀ point ∈ shadow.union, ∀ coordinate : Fin 3,
        |point coordinate| ≤ 1 := by
      intro point hpoint coordinate
      have hbox : point ∈ Kakeya.Streamlined.axisBox 2 2 2 :=
        paperShading_subset_axisBox
          (Z := Z) (by simpa [hunion] using hpoint)
      simp only [Kakeya.Streamlined.axisBox, Set.mem_setOf_eq] at hbox
      norm_num at hbox
      fin_cases coordinate <;> tauto
    have hexact : ∀ z ∈ Set.Icc (-1 : ℝ) 1,
        IsADSet1
          (scalarProjection
            (globalGrainDirection (data.sourceGlobalGrains.slope z))
            (horizontalSlice shadow.union z))
          delta (1 - sigma)
          (10 * Kakeya.realRpowENN delta (-finalLoss)) :=
      data.sourceGlobalGrains.partialActiveCellShadow_exactAD
        hdelta hbridge data.sourceGlobalGrains.slope_bound
    have hraw := paper_exactSlice_slab_volume_le
      shadow haxis data.sourceGlobalGrains.slope
      (10 * Kakeya.realRpowENN delta (-finalLoss))
      hdelta hsigma hsigmaOne
      (ENNReal.mul_ne_top (by norm_num) (by simp [Kakeya.realRpowENN]))
      hexact hab
    rw [hunion] at hraw
    simpa [Amax, pureWZ2HierarchySlabConstant, mul_assoc] using hraw
  have hlevelZeroPopular : ∃ trapezoid ∈ rawTrapezoids ⟨0, hNpos⟩,
      volumeInCoreGeneric Z trapezoid >
        Amax * ENNReal.ofReal (3 * L ⟨0, hNpos⟩) := by
    apply PureHierarchyGeneric.level0_popularity_from_volume_general_generic
      hNpos hdelta hdeltaStrict hhierarchyLoss hsigma Amax hZheight
      (fun trapezoid htrapezoid =>
        (data.length_bounds ⟨0, hNpos⟩ trapezoid htrapezoid).2)
      (data.separated_cores ⟨0, hNpos⟩)
      (hcoverage ⟨0, hNpos⟩)
      (by
        have hpower : Kakeya.realRpowENN delta
            (sigma + hierarchyLoss / (4 * (N : ℝ))) ≤
            Kakeya.realRpowENN delta (sigma + finalLoss) := by
          apply ENNReal.ofReal_mono
          exact Real.rpow_le_rpow_of_exponent_ge hdelta hdeltaOne
            (by simpa [N] using hfinalLevelZero)
        exact hpower.trans data.volume_lower)
    simpa [Amax, N] using hlevelZero
  rcases PureHierarchyGeneric.multi_level_thin_with_retention
      (Z := Z) (rawTrapezoids := rawTrapezoids)
      (A_max := Amax) (L := L)
      (by norm_num) hLnonneg hLeq hslab
      (fun level trapezoid htrapezoid =>
        (data.length_bounds level trapezoid htrapezoid).2)
      data.separated_cores hcoverage hZheight hdelta hdeltaStrict
      hhierarchyLoss hNpos
      (by simpa [N] using hgeometric) hlevelZeroPopular with
    ⟨Zthin, popular, hthinSub, hpopularSub, hthinCoverage,
      hcoreVolume, hpopularNonempty, hvolumeDecomp, hsameMultiplicity⟩
  let removed : ENNReal := Amax * ENNReal.ofReal
    (12 * ∑ level : Fin N,
      Real.rpow (wz1Corollary26Scale delta N level) hierarchyLoss)
  have hremovedBound : removed ≤ ENNReal.ofReal (1 / 3) * volume Z.union := by
    simpa [removed, Amax, N, Z] using hremoved
  have hZvolumeFinite : volume Z.union ≠ ⊤ := by
    have hbox : Z.union ⊆ Kakeya.Streamlined.axisBox 2 2 2 :=
      paperShading_subset_axisBox
    have hboxFinite : volume (Kakeya.Streamlined.axisBox 2 2 2) ≠ ⊤ := by
      rw [Kakeya.Streamlined.volume_axisBox 2 2 2] <;> norm_num
    exact ne_top_of_le_ne_top hboxFinite (measure_mono hbox)
  have hTwoThird : ENNReal.ofReal (2 / 3) * volume Z.union ≤
      volume Zthin.union := by
    let third : ENNReal := ENNReal.ofReal (1 / 3) * volume Z.union
    have hdecomp : volume Z.union ≤ volume Zthin.union + third :=
      hvolumeDecomp.trans (by gcongr)
    have hthirdFinite : third ≠ ⊤ :=
      ENNReal.mul_ne_top (by simp) hZvolumeFinite
    have hsum : ENNReal.ofReal (2 / 3) * volume Z.union + third =
        volume Z.union := by
      dsimp only [third]
      rw [← add_mul]
      have hcoeff : ENNReal.ofReal (2 / 3) +
          ENNReal.ofReal (1 / 3) = 1 := by
        rw [← ENNReal.ofReal_add] <;> norm_num
      rw [hcoeff, one_mul]
    rw [← hsum] at hdecomp
    exact (ENNReal.add_le_add_iff_right hthirdFinite).mp hdecomp
  have hfinalVolumeThin : Kakeya.realRpowENN delta
      (sigma + hierarchyLoss) < volume Zthin.union := by
    exact hfinalVolume.trans_le <|
      (mul_le_mul_left' data.volume_lower
        (ENNReal.ofReal (2 / 3))).trans hTwoThird
  have hZthinVolumePos : 0 < volume Zthin.union :=
    (ENNReal.ofReal_pos.mpr
      (Real.rpow_pos_of_pos hdelta (sigma + hierarchyLoss))).trans_le
      hfinalVolumeThin.le
  have hZthinVolumeFinite : volume Zthin.union ≠ ⊤ :=
    ne_top_of_le_ne_top hZvolumeFinite
      (measure_mono hthinSub.union_subset)
  have hZthinMassPos : 0 < Zthin.mass := by
    have hunionMass : volume Zthin.union ≤ Zthin.mass := by
      have hunion : Zthin.union =
          ⋃ index : Fin (wz1PaperBodyFamily source.family).card,
            Zthin.carrier index := by
        ext point
        simp [Kakeya.Streamlined.Shading.union]
      rw [hunion]
      exact MeasureTheory.measure_iUnion_fintype_le
        MeasureTheory.volume Zthin.carrier
    exact hZthinVolumePos.trans_le hunionMass
  have hZthinMassFinite : Zthin.mass ≠ ⊤ :=
    wz1PaperTubeShading_mass_ne_top Zthin
  classical
  let allPopular : Finset WZ1VerticalTrapezoid :=
    Finset.biUnion Finset.univ popular
  let coreBound : WZ1VerticalTrapezoid → ENNReal := fun trapezoid =>
    Amax * ENNReal.ofReal
      (Real.rpow trapezoid.height (1 / 2 + hierarchyLoss))
  have hcoreAll : ∀ trapezoid ∈ allPopular,
      volumeInCoreGeneric Zthin trapezoid >
        coreBound trapezoid := by
    intro trapezoid htrapezoid
    rcases Finset.mem_biUnion.mp htrapezoid with
      ⟨level, _, hlevel⟩
    have hraw := hcoreVolume level trapezoid hlevel
    have hheight := data.height_eq level trapezoid
      (hpopularSub level hlevel)
    simpa [coreBound, hheight, hLeq] using hraw
  have hcoreFinite : ∀ trapezoid ∈ allPopular,
      coreBound trapezoid ≠ ⊤ := by
    intro trapezoid _
    apply ENNReal.mul_ne_top
    · dsimp only [Amax, pureWZ2HierarchySlabConstant]
      exact ENNReal.mul_ne_top
        (ENNReal.mul_ne_top (by norm_num)
          (ENNReal.mul_ne_top (by norm_num)
            (by simp [Kakeya.realRpowENN])))
        (by simp [Kakeya.realRpowENN])
    · simp
  rcases PureHierarchyGeneric.compact_subshading_with_full_retention_generic
      (Z := Zthin) (T := allPopular) (core_bound := coreBound)
      (vol_bound := Kakeya.realRpowENN delta (sigma + hierarchyLoss))
      (mass_bound := Zthin.mass / 2) source.extremal.nonempty
      hZthinVolumeFinite hcoreAll hfinalVolumeThin
      (ENNReal.half_lt_self hZthinMassPos.ne' hZthinMassFinite)
      hcoreFinite (by simp [Kakeya.realRpowENN])
      (ENNReal.div_ne_top hZthinMassFinite (by norm_num)) with
    ⟨Zcompact, hcompactSub, hcompact, hcompactCore,
      hcompactVolume, hcompactMass⟩
  have hcompactZ : PureWZ2PaperIsSubshading Zcompact Z :=
    fun index => (hcompactSub index).trans (hthinSub index)
  have hcompactSource :
      PureWZ2PaperIsSubshading Zcompact source.shading :=
    fun index => (hcompactZ index).trans (hZSource index)
  have hslabCompact : ∀ a b : ℝ, a ≤ b →
      volume (Zcompact.union ∩ horizontalSlab a b) ≤
        Amax * ENNReal.ofReal (b - a) := by
    intro a b hab
    exact (measure_mono
      (Set.inter_subset_inter_left _ hcompactZ.union_subset)).trans
        (hslab a b hab)
  have hreanchor : ∀ level : Fin N,
      ∃ (shrunk : WZ1VerticalTrapezoid → WZ1VerticalTrapezoid)
        (anchored : Finset WZ1VerticalTrapezoid),
        (∀ trapezoid ∈ popular level,
          (shrunk trapezoid).core ⊆ trapezoid.core ∧
          (shrunk trapezoid).slope = trapezoid.slope ∧
          (shrunk trapezoid).intercept = trapezoid.intercept ∧
          (shrunk trapezoid).height = trapezoid.height ∧
          L level ≤ (shrunk trapezoid).length) ∧
        (∀ trapezoid ∈ popular level, shrunk trapezoid ∈ anchored) ∧
        (∀ trapezoid ∈ anchored, ∃ sourceTrapezoid ∈ popular level,
          trapezoid = shrunk sourceTrapezoid) ∧
        (∀ trapezoid ∈ anchored,
          horizontalSlice Zcompact.union trapezoid.left ≠ ∅ ∧
          horizontalSlice Zcompact.union trapezoid.right ≠ ∅) ∧
        (∀ trapezoid ∈ anchored, L level ≤ trapezoid.length) ∧
        (∀ trapezoid ∈ anchored, ∃ sourceTrapezoid ∈ popular level,
          trapezoid.core ⊆ sourceTrapezoid.core ∧
          trapezoid.slope = sourceTrapezoid.slope ∧
          trapezoid.intercept = sourceTrapezoid.intercept ∧
          trapezoid.height = sourceTrapezoid.height) ∧
        (∀ z : ℝ, horizontalSlice Zcompact.union z ≠ ∅ →
          (∃ trapezoid ∈ popular level, z ∈ trapezoid.core) →
            ∃ trapezoid ∈ anchored, z ∈ trapezoid.core) := by
    intro level
    have hvolume : ∀ trapezoid ∈ popular level,
        volumeInCoreGeneric Zcompact trapezoid >
          Amax * ENNReal.ofReal (L level) := by
      intro trapezoid htrapezoid
      have hall : trapezoid ∈ allPopular :=
        Finset.mem_biUnion.mpr ⟨level, Finset.mem_univ _, htrapezoid⟩
      have hraw := hcompactCore trapezoid hall
      have hheight := data.height_eq level trapezoid
        (hpopularSub level htrapezoid)
      simpa [coreBound, hheight, hLeq] using hraw
    exact PureHierarchyGeneric.reanchor_with_coverage_generic
      (hLnonneg level) hcompact hslabCompact hvolume
  choose shrunk anchored hshrunk hshrunkMem hanchoredFrom
    hactiveEndpoints hlengthLower hprovenance hcoverageAnchored using hreanchor
  let trapezoids : Fin N → Finset WZ1VerticalTrapezoid := anchored
  have hnonempty : ∀ level, (trapezoids level).Nonempty := by
    intro level
    rcases hpopularNonempty level with ⟨trapezoid, htrapezoid⟩
    exact ⟨shrunk level trapezoid, hshrunkMem level trapezoid htrapezoid⟩
  have hheight : ∀ level, ∀ trapezoid ∈ trapezoids level,
      trapezoid.height = wz1Corollary26Scale delta N level := by
    intro level trapezoid htrapezoid
    rcases hanchoredFrom level trapezoid htrapezoid with
      ⟨sourceTrapezoid, hsourceTrapezoid, rfl⟩
    exact (hshrunk level sourceTrapezoid hsourceTrapezoid).2.2.2.1.trans
      (data.height_eq level sourceTrapezoid
        (hpopularSub level hsourceTrapezoid))
  have hslope : ∀ level, ∀ trapezoid ∈ trapezoids level,
      |trapezoid.slope| ≤ 2 := by
    intro level trapezoid htrapezoid
    rcases hanchoredFrom level trapezoid htrapezoid with
      ⟨sourceTrapezoid, hsourceTrapezoid, rfl⟩
    rw [(hshrunk level sourceTrapezoid hsourceTrapezoid).2.1]
    exact data.slope_bound level sourceTrapezoid
      (hpopularSub level hsourceTrapezoid)
  have hlength : ∀ level, ∀ trapezoid ∈ trapezoids level,
      Real.rpow (wz1Corollary26Scale delta N level)
          (1 / 2 + hierarchyLoss) ≤ trapezoid.length ∧
        trapezoid.length ≤
          Real.sqrt (wz1Corollary26Scale delta N level) := by
    intro level trapezoid htrapezoid
    rcases hanchoredFrom level trapezoid htrapezoid with
      ⟨sourceTrapezoid, hsourceTrapezoid, rfl⟩
    have hprops := hshrunk level sourceTrapezoid hsourceTrapezoid
    have hupper : (shrunk level sourceTrapezoid).length ≤
        sourceTrapezoid.length := by
      have hleft : sourceTrapezoid.left ≤
          (shrunk level sourceTrapezoid).left :=
        (hprops.1 (Set.left_mem_Icc.mpr
          (shrunk level sourceTrapezoid).left_lt_right.le)).1
      have hright : (shrunk level sourceTrapezoid).right ≤
          sourceTrapezoid.right :=
        (hprops.1 (Set.right_mem_Icc.mpr
          (shrunk level sourceTrapezoid).left_lt_right.le)).2
      simp [WZ1VerticalTrapezoid.length]
      linarith
    constructor
    · simpa [L] using hprops.2.2.2.2
    · exact hupper.trans
        (data.length_bounds level sourceTrapezoid
          (hpopularSub level hsourceTrapezoid)).2
  have hseparated : ∀ level, ∀ first ∈ trapezoids level,
      ∀ second ∈ trapezoids level, first ≠ second →
        ∀ z ∈ first.core, ∀ w ∈ second.core,
          Real.sqrt (wz1Corollary26Scale delta N level) ≤ |z - w| := by
    intro level first hfirst second hsecond hne z hz w hw
    rcases hanchoredFrom level first hfirst with
      ⟨firstSource, hfirstSource, hfirstEq⟩
    rcases hanchoredFrom level second hsecond with
      ⟨secondSource, hsecondSource, hsecondEq⟩
    have hsourceNe : firstSource ≠ secondSource := by
      intro heq
      subst secondSource
      exact hne (hfirstEq.trans hsecondEq.symm)
    have hfirstCore := (hshrunk level firstSource hfirstSource).1
    have hsecondCore := (hshrunk level secondSource hsecondSource).1
    rw [hfirstEq] at hz
    rw [hsecondEq] at hw
    exact data.separated_cores level firstSource
      (hpopularSub level hfirstSource) secondSource
      (hpopularSub level hsecondSource) hsourceNe z (hfirstCore hz)
      w (hsecondCore hw)
  have hactive : ∀ level, ∀ trapezoid ∈ trapezoids level,
      horizontalSlice Zcompact.union trapezoid.left ≠ ∅ ∧
        horizontalSlice Zcompact.union trapezoid.right ≠ ∅ :=
    hactiveEndpoints
  have hslopeFinal : ∀ level, ∀ trapezoid ∈ trapezoids level,
      ∀ z ∈ trapezoid.core, horizontalSlice Zcompact.union z ≠ ∅ →
        |data.sourceGlobalGrains.slope z - trapezoid.affine z| ≤
          wz1Corollary26Scale delta N level := by
    intro level trapezoid htrapezoid z hz hslice
    rcases hprovenance level trapezoid htrapezoid with
      ⟨sourceTrapezoid, hsourceTrapezoid, hcore, hslopeEq, hinterceptEq, _⟩
    have hsliceZ : horizontalSlice Z.union z ≠ ∅ := by
      apply Set.Nonempty.ne_empty
      apply Set.Nonempty.mono _ (Set.nonempty_iff_ne_empty.mpr hslice)
      intro point hpoint
      exact ⟨hcompactZ.union_subset hpoint.1, hpoint.2⟩
    have hraw := hslopeApprox level sourceTrapezoid
      (hpopularSub level hsourceTrapezoid) z (hcore hz) hsliceZ
    simpa [WZ1VerticalTrapezoid.affine, hslopeEq, hinterceptEq] using hraw
  have hcoverageFinal : ∀ level, ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      horizontalSlice Zcompact.union z ≠ ∅ →
        ∃ trapezoid ∈ trapezoids level, z ∈ trapezoid.core := by
    intro level z _hz hslice
    have hsliceThin : horizontalSlice Zthin.union z ≠ ∅ := by
      apply Set.Nonempty.ne_empty
      apply Set.Nonempty.mono _ (Set.nonempty_iff_ne_empty.mpr hslice)
      intro point hpoint
      exact ⟨hcompactSub.union_subset hpoint.1, hpoint.2⟩
    exact hcoverageAnchored level z hslice
      (hthinCoverage level z hsliceThin)
  let hwithout : PureWZ2HierarchyWithoutParents
      Zcompact data.sourceGlobalGrains.slope hierarchyLoss :=
    { delta_pos := hdelta
      delta_le_one := hdeltaOne
      hierarchyLoss_pos := hhierarchyLoss
      vertical_bound := by
        intro point hpoint
        exact hZheight point (hcompactZ.union_subset hpoint)
      levelCount := N
      levelCount_two := data.levelCount_two
      trapezoids := trapezoids
      level_nonempty := hnonempty
      height_eq := hheight
      slope_bound := hslope
      length_bounds := hlength
      separated_cores := hseparated
      active_endpoints := hactive
      slope_approximation := hslopeFinal
      active_height_coverage := hcoverageFinal }
  have hconstant : Kakeya.realRpowENN delta (-finalLoss) ≤
      Kakeya.realRpowENN delta (-hierarchyLoss) :=
    pureWZ2_grain_constant_mono hdelta hdeltaOne hfinalHierarchy
  have hconstantTop : Kakeya.realRpowENN delta (-hierarchyLoss) ≠ ⊤ := by
    simp [Kakeya.realRpowENN]
  let localGrains := data.localGrains.restrictWithConstant
    hcompactZ hconstant hconstantTop
  let globalGrains := data.sourceGlobalGrains.restrict
    hcompactZ hconstant hconstantTop
  let hierarchy : PureWZ2LocallyLinearHierarchyData
      source hierarchyLoss hierarchyLoss := {
    levelCount := N
    levelCount_two := data.levelCount_two
    delta_pos := hdelta
    delta_le_one := hdeltaOne
    shading := Zcompact
    subshading := hcompactSource
    volume_lower := hcompactVolume
    localGrains := localGrains
    planeMap_vertical_bound := by
      intro point
      exact data.planeMap_vertical_bound
        ⟨point, hcompactZ.union_subset point.property⟩
    sourceGlobalGrains := globalGrains
    source_slope_eq := data.source_slope_eq
    hierarchy := hwithout.toAnchoredHierarchy }
  have hwithoutLevel : hwithout.levelCount = N := rfl
  have hierarchyLevel : hierarchy.hierarchy.levelCount = N := by
    exact hwithoutLevel
  refine ⟨{
    hierarchy := hierarchy
    levelCount_eq := hierarchyLevel
    quantitative := ?_ }⟩
  intro densityLoss multiplicity hmultiplicityPos hZconstant hsourceMass
  have hZthinConstant : Zthin.HasConstantMultiplicity multiplicity
      (2 * multiplicity) := by
    intro point hpoint
    rw [hsameMultiplicity point hpoint]
    exact hZconstant point (hthinSub.union_subset hpoint)
  have hthinMass : ENNReal.ofReal (1 / 3) * Z.mass ≤ Zthin.mass :=
    PureHierarchyGeneric.mass_retention_from_volume_generic
      hZconstant hZthinConstant hZvolumeFinite hTwoThird
  have hcompactMultiplicityUpper : ∀ point,
      Zcompact.pointMultiplicity point ≤ 2 * multiplicity := by
    intro point
    by_cases hpoint : point ∈ Zcompact.union
    · exact (paperSubshading_pointMultiplicity_le Zcompact Z hcompactZ point).trans
        (hZconstant point (hcompactZ.union_subset hpoint)).2
    · have hzero : Zcompact.pointMultiplicity point = 0 := by
        classical
        unfold Kakeya.Streamlined.Shading.pointMultiplicity
        apply Finset.card_eq_zero.mpr
        rw [Finset.filter_eq_empty_iff]
        intro index _ hindex
        exact hpoint ⟨index, hindex⟩
      rw [hzero]
      omega
  have hcompactHalf : ENNReal.ofReal (1 / 2) * Zthin.mass ≤
      Zcompact.mass := by
    have hdiv : Zthin.mass / 2 =
        ENNReal.ofReal (1 / 2) * Zthin.mass := by
      have htwo : Zthin.mass / 2 = Zthin.mass / ENNReal.ofReal 2 := by
        norm_cast
      rw [htwo, ENNReal.div_eq_inv_mul]
      have hhalf : (ENNReal.ofReal 2)⁻¹ = ENNReal.ofReal (1 / 2) := by
        have hraw : (ENNReal.ofReal 2)⁻¹ =
            ENNReal.ofReal ((2 : ℝ)⁻¹) :=
          (ENNReal.ofReal_inv_of_pos (x := (2 : ℝ)) (by norm_num)).symm
        rw [hraw]
        norm_num
      rw [hhalf, mul_comm]
    rwa [← hdiv]
  have hcompactSixth : ENNReal.ofReal (1 / 6) * Z.mass ≤
      Zcompact.mass := by
    have hcoeff : ENNReal.ofReal (1 / 6) =
        ENNReal.ofReal (1 / 2) * ENNReal.ofReal (1 / 3) := by
      rw [← ENNReal.ofReal_mul] <;> norm_num
    calc
      ENNReal.ofReal (1 / 6) * Z.mass =
          ENNReal.ofReal (1 / 2) *
            (ENNReal.ofReal (1 / 3) * Z.mass) := by
              rw [hcoeff, mul_assoc]
      _ ≤ ENNReal.ofReal (1 / 2) * Zthin.mass := by gcongr
      _ ≤ Zcompact.mass := hcompactHalf
  refine ⟨{
    hierarchy := hierarchy
    multiplicity := multiplicity
    multiplicity_pos := hmultiplicityPos
    pointMultiplicity_upper := by
      simpa [hierarchy] using hcompactMultiplicityUpper
    mass_retention := by
      calc
        ENNReal.ofReal (1 / 6) *
              (Kakeya.realRpowENN delta densityLoss *
                (wz1PaperBodyFamily source.family).mass) ≤
            ENNReal.ofReal (1 / 6) * Z.mass := by gcongr
        _ ≤ Zcompact.mass := hcompactSixth
        _ = hierarchy.shading.mass := rfl }, rfl⟩

/-- Compatibility projection retaining the historical result type. -/
theorem toLocallyLinearHierarchyWithLevelCount
    {sigma inputLoss delta finalLoss hierarchyLoss : ℝ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    (data : PureWZ2MixedRawHierarchyData source finalLoss hierarchyLoss)
    (hbridge : PureWZ2PaperADBridgeStatement)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hhierarchyLoss : 0 < hierarchyLoss)
    (hfinalHierarchy : finalLoss ≤ hierarchyLoss)
    (hfinalLevelZero : finalLoss ≤
      hierarchyLoss / (4 * (data.levelCount : ℝ)))
    (hdeltaStrict : delta < 1)
    (hgeometric : Real.rpow delta
      (hierarchyLoss / (data.levelCount : ℝ)) < 1 / 9)
    (hlevelZero :
      pureWZ2HierarchySlabConstant delta sigma finalLoss *
          ENNReal.ofReal (12 * Real.rpow delta
            (hierarchyLoss / (data.levelCount : ℝ))) <
        Kakeya.realRpowENN delta
          (sigma + hierarchyLoss / (4 * (data.levelCount : ℝ))))
    (hremoved :
      pureWZ2HierarchySlabConstant delta sigma finalLoss *
          ENNReal.ofReal
            (12 * ∑ level : Fin data.levelCount,
              Real.rpow
                (wz1Corollary26Scale delta
                  data.levelCount level) hierarchyLoss) ≤
        ENNReal.ofReal (1 / 3) * volume data.shading.union)
    (hfinalVolume :
      Kakeya.realRpowENN delta (sigma + hierarchyLoss) <
        ENNReal.ofReal (2 / 3) *
          Kakeya.realRpowENN delta (sigma + finalLoss)) :
    Nonempty { hierarchy : PureWZ2LocallyLinearHierarchyData
        source hierarchyLoss hierarchyLoss //
      hierarchy.hierarchy.levelCount = data.levelCount } := by
  rcases data.toPopularityOutputWithLevelCount hbridge hsigma hsigmaOne
      hhierarchyLoss hfinalHierarchy hfinalLevelZero hdeltaStrict
      hgeometric hlevelZero hremoved hfinalVolume with ⟨output⟩
  exact ⟨⟨output.hierarchy, output.levelCount_eq⟩⟩

end PureWZ2MixedRawHierarchyData

/-- Quantitative projection of the same mixed-terminal popularity run.  The
terminal multiplicity and source-mass receipts are threaded through the exact
same thinning and compactification choices as the hierarchy geometry. -/
theorem PureWZ2QuantitativeMixedRawHierarchyData.toQuantitativeLocallyLinearHierarchyWithLevelCount
    {sigma inputLoss delta finalLoss hierarchyLoss densityLoss : ℝ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    (data : PureWZ2QuantitativeMixedRawHierarchyData
      source finalLoss hierarchyLoss densityLoss)
    (hbridge : PureWZ2PaperADBridgeStatement)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hhierarchyLoss : 0 < hierarchyLoss)
    (hfinalHierarchy : finalLoss ≤ hierarchyLoss)
    (hfinalLevelZero : finalLoss ≤
      hierarchyLoss / (4 * (data.mixed.levelCount : ℝ)))
    (hdeltaStrict : delta < 1)
    (hgeometric : Real.rpow delta
      (hierarchyLoss / (data.mixed.levelCount : ℝ)) < 1 / 9)
    (hlevelZero :
      pureWZ2HierarchySlabConstant delta sigma finalLoss *
          ENNReal.ofReal (12 * Real.rpow delta
            (hierarchyLoss / (data.mixed.levelCount : ℝ))) <
        Kakeya.realRpowENN delta
          (sigma + hierarchyLoss / (4 * (data.mixed.levelCount : ℝ))))
    (hremoved :
      pureWZ2HierarchySlabConstant delta sigma finalLoss *
          ENNReal.ofReal
            (12 * ∑ level : Fin data.mixed.levelCount,
              Real.rpow
                (wz1Corollary26Scale delta
                  data.mixed.levelCount level) hierarchyLoss) ≤
        ENNReal.ofReal (1 / 3) * volume data.mixed.shading.union)
    (hfinalVolume :
      Kakeya.realRpowENN delta (sigma + hierarchyLoss) <
        ENNReal.ofReal (2 / 3) *
          Kakeya.realRpowENN delta (sigma + finalLoss)) :
    Nonempty { output : PureWZ2QuantitativeLocallyLinearHierarchyData
        source hierarchyLoss hierarchyLoss densityLoss //
      output.hierarchy.hierarchy.levelCount = data.mixed.levelCount } := by
  rcases data.mixed.toPopularityOutputWithLevelCount hbridge hsigma hsigmaOne
      hhierarchyLoss hfinalHierarchy hfinalLevelZero hdeltaStrict
      hgeometric hlevelZero hremoved hfinalVolume with ⟨output⟩
  let quantitative := output.quantitative densityLoss data.multiplicity
    data.multiplicity_pos data.constant_multiplicity data.mass_lower
  exact ⟨⟨quantitative.1, by
    rw [quantitative.2]
    exact output.levelCount_eq⟩⟩

namespace PureWZ2MixedRawHierarchyData

/-- Compatibility projection which forgets the retained depth equality. -/
theorem toLocallyLinearHierarchy
    {sigma inputLoss delta finalLoss hierarchyLoss : ℝ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    (data : PureWZ2MixedRawHierarchyData source finalLoss hierarchyLoss)
    (hbridge : PureWZ2PaperADBridgeStatement)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hhierarchyLoss : 0 < hierarchyLoss)
    (hfinalHierarchy : finalLoss ≤ hierarchyLoss)
    (hfinalLevelZero : finalLoss ≤
      hierarchyLoss / (4 * (data.levelCount : ℝ)))
    (hdeltaStrict : delta < 1)
    (hgeometric : Real.rpow delta
      (hierarchyLoss / (data.levelCount : ℝ)) < 1 / 9)
    (hlevelZero :
      pureWZ2HierarchySlabConstant delta sigma finalLoss *
          ENNReal.ofReal (12 * Real.rpow delta
            (hierarchyLoss / (data.levelCount : ℝ))) <
        Kakeya.realRpowENN delta
          (sigma + hierarchyLoss / (4 * (data.levelCount : ℝ))))
    (hremoved :
      pureWZ2HierarchySlabConstant delta sigma finalLoss *
          ENNReal.ofReal
            (12 * ∑ level : Fin data.levelCount,
              Real.rpow
                (wz1Corollary26Scale delta
                  data.levelCount level) hierarchyLoss) ≤
        ENNReal.ofReal (1 / 3) * volume data.shading.union)
    (hfinalVolume :
      Kakeya.realRpowENN delta (sigma + hierarchyLoss) <
        ENNReal.ofReal (2 / 3) *
          Kakeya.realRpowENN delta (sigma + finalLoss)) :
    Nonempty (PureWZ2LocallyLinearHierarchyData
      source hierarchyLoss hierarchyLoss) := by
  rcases data.toLocallyLinearHierarchyWithLevelCount hbridge hsigma hsigmaOne
      hhierarchyLoss hfinalHierarchy hfinalLevelZero hdeltaStrict
      hgeometric hlevelZero hremoved hfinalVolume with ⟨hierarchy⟩
  exact ⟨hierarchy.1⟩

end PureWZ2MixedRawHierarchyData
