import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceHorizontalBlockSeparation

/-!
# Weighted residue selection for completed source-block outputs

This module colors completed local block outputs modulo 64 using their actual
rich shading masses as weights.  The selected residue retains at least a
`1/64` fraction of the total indexed mass and its trapezoid cores are already
separated at the final public scale.
-/

noncomputable section

namespace Kakeya.Assouad

open Set

attribute [local instance] Classical.propDecidable

/-- Finite ENNReal weighted pigeonhole over `n` colors. -/
lemma finset_ennreal_weighted_pigeonhole
    {alpha : Type*} [DecidableEq alpha]
    {n : ℕ} (hn : 0 < n)
    (indices : Finset alpha) (weight : alpha → ENNReal)
    (color : alpha → Fin n) :
    ∃ target : Fin n,
      (∑ index ∈ indices, weight index) ≤
        (n : ENNReal) *
          ∑ index ∈ indices.filter (fun index => color index = target),
            weight index := by
  let fiberWeight : Fin n → ENNReal := fun target =>
    ∑ index ∈ indices.filter (fun index => color index = target),
      weight index
  have hcolors : (Finset.univ : Finset (Fin n)).Nonempty := by
    exact Finset.univ_nonempty_iff.mpr ⟨0, hn⟩
  rcases Finset.exists_max_image Finset.univ fiberWeight hcolors with
    ⟨target, _htarget, hmax⟩
  have htotal :
      (∑ target : Fin n, fiberWeight target) =
        ∑ index ∈ indices, weight index := by
    simpa [fiberWeight] using
      Finset.sum_fiberwise indices color weight
  refine ⟨target, ?_⟩
  rw [← htotal]
  calc
    (∑ other : Fin n, fiberWeight other) ≤
        ∑ _other : Fin n, fiberWeight target := by
      exact Finset.sum_le_sum fun other _ => hmax other (Finset.mem_univ _)
    _ = (n : ENNReal) * fiberWeight target := by
      simp [Finset.sum_const, Finset.card_fin]
    _ = (n : ENNReal) *
          ∑ index ∈ indices.filter (fun index => color index = target),
            weight index := rfl

/-- A finite family of already-completed local source-block outputs. -/
structure PureWZ2SourceHorizontalBlockFamilyData
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss normalEta theoremEta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    (twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent) where
  indexCount : ℕ
  indexCount_pos : 0 < indexCount
  block : Fin indexCount → ℤ
  block_injective : Function.Injective block
  shift : ℝ
  pipeline : Fin indexCount →
    PureWZ2SourceHorizontalPipelineData
      (normalEta := normalEta) twoScale
  rich : ∀ index, PureWZ2SourceHorizontalRichPipelineData
    (finalLoss := finalLoss) (theoremEta := theoremEta) (pipeline index)
  left_eq : ∀ index, (pipeline index).window.left =
    pureWZ2SourceCarrierBlockLeft rho (block index) + shift

/-- The selected residue family and its exact aggregate final-height mass
retention. -/
structure PureWZ2SourceHorizontalBlockResidueData
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss normalEta theoremEta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    (blocks : PureWZ2SourceHorizontalBlockFamilyData
      (finalLoss := finalLoss) (normalEta := normalEta)
      (theoremEta := theoremEta) twoScale) where
  residue : Fin 64
  selected : Finset (Fin blocks.indexCount)
  selected_eq : selected = Finset.univ.filter fun index =>
    (blocks.block index % (64 : ℤ)).toNat = residue
  selected_nonempty : selected.Nonempty
  family : PureWZ2SourceHorizontalWindowFamilyData
    (finalLoss := finalLoss) (normalEta := normalEta)
    (theoremEta := theoremEta) twoScale
  total_mass_le :
    (∑ index : Fin blocks.indexCount,
        (blocks.rich index).heightLift.shading.mass) ≤
      64 * family.shading.mass

private lemma sourceBlockResidue_separated
    {first second : ℤ}
    (hne : first ≠ second)
    (hmod : first % (64 : ℤ) = second % (64 : ℤ)) :
    (64 : ℤ) ≤ |first - second| := by
  have hzero : (first - second) % (64 : ℤ) = 0 := by
    rw [Int.sub_emod, hmod]
    simp
  have hdiv : (64 : ℤ) ∣ first - second := by
    rwa [Int.dvd_iff_emod_eq_zero]
  exact Int.le_abs_of_dvd (sub_ne_zero.mpr hne) hdiv

/-- Select one mass-heavy residue class and package it directly as the
existing multi-window input. -/
theorem PureWZ2SourceHorizontalBlockFamilyData.selectResidue
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss normalEta theoremEta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    (blocks : PureWZ2SourceHorizontalBlockFamilyData
      (finalLoss := finalLoss) (normalEta := normalEta)
      (theoremEta := theoremEta) twoScale) :
    Nonempty (PureWZ2SourceHorizontalBlockResidueData blocks) := by
  let label : Fin blocks.indexCount → Fin 64 := fun index =>
    ⟨(blocks.block index % (64 : ℤ)).toNat, by
      have hnonneg : 0 ≤ blocks.block index % (64 : ℤ) :=
        Int.emod_nonneg _ (by norm_num)
      have hlt : blocks.block index % (64 : ℤ) < (64 : ℤ) :=
        Int.emod_lt_of_pos _ (by norm_num)
      omega⟩
  let weight : Fin blocks.indexCount → ENNReal := fun index =>
    (blocks.rich index).heightLift.shading.mass
  rcases finset_ennreal_weighted_pigeonhole (n := 64) (by norm_num)
      Finset.univ weight label with ⟨residue, hretained⟩
  let selected := Finset.univ.filter fun index => label index = residue
  have hweightPos : ∀ index : Fin blocks.indexCount, 0 < weight index := by
    intro index
    dsimp only [weight]
    have hpositive := (blocks.rich index).heightVolume.mass_lower
    have hmult : 0 <
        (twoScale.coarse.fineMultiplicity : ENNReal) := by
      exact_mod_cast twoScale.coarse.fineMultiplicity_pos
    have hheight : 0 <
        ((blocks.rich index).rich.heightIndices.card : ENNReal) := by
      exact_mod_cast (blocks.rich index).rich.heightIndices_card.trans_gt
        (blocks.rich index).rich.richF_nonempty.card_pos
    have hlayer :=
      (blocks.pipeline index).heightPopular.layerMass_pos
    have hheightLayer : 0 <
        ((blocks.rich index).rich.heightIndices.card : ENNReal) *
          (blocks.pipeline index).heightPopular.layerMass :=
      ENNReal.mul_pos hheight.ne' hlayer.ne'
    exact (ENNReal.mul_pos hmult.ne' hheightLayer.ne').trans_le hpositive
  have htotalPos : 0 < ∑ index : Fin blocks.indexCount, weight index := by
    let first : Fin blocks.indexCount := ⟨0, blocks.indexCount_pos⟩
    exact (hweightPos first).trans_le
      (Finset.single_le_sum (fun _ _ => bot_le) (Finset.mem_univ first))
  have hselectedNonempty : selected.Nonempty := by
    by_contra hempty
    have hselectedEmpty : selected = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hempty
    have hzero : ∑ index ∈ selected, weight index = 0 := by
      simp [hselectedEmpty]
    have hleZero : (∑ index : Fin blocks.indexCount, weight index) ≤ 0 := by
      simpa [selected, hzero] using hretained
    exact (not_le_of_gt htotalPos) hleZero
  let selectedEquiv := selected.equivFin
  let selectedIndex : Fin selected.card → Fin blocks.indexCount := fun index =>
    (selectedEquiv.symm index).1
  have hselectedIndexInjective : Function.Injective selectedIndex := by
    intro first second heq
    apply selectedEquiv.symm.injective
    exact Subtype.ext heq
  have hselectedMem : ∀ index, selectedIndex index ∈ selected := fun index =>
    (selectedEquiv.symm index).2
  have hsameResidue : ∀ index,
      blocks.block (selectedIndex index) % (64 : ℤ) = (residue : ℤ) := by
    intro index
    have hlabel := (Finset.mem_filter.mp (hselectedMem index)).2
    have hcast := congrArg (fun value : Fin 64 => (value : ℤ)) hlabel
    have hnonneg : 0 ≤ blocks.block (selectedIndex index) % (64 : ℤ) :=
      Int.emod_nonneg _ (by norm_num)
    simpa [label, Int.toNat_of_nonneg hnonneg] using hcast
  let family : PureWZ2SourceHorizontalWindowFamilyData
      (finalLoss := finalLoss) (normalEta := normalEta)
      (theoremEta := theoremEta) twoScale := {
    windowCount := selected.card
    windowCount_pos := Finset.card_pos.mpr hselectedNonempty
    pipeline := fun index => blocks.pipeline (selectedIndex index)
    rich := fun index => blocks.rich (selectedIndex index)
    trapezoid_injective := by
      intro first second htrapezoid
      by_contra hne
      have hsourceNe : selectedIndex first ≠ selectedIndex second := by
        intro heq
        exact hne (hselectedIndexInjective heq)
      have hblockNe :
          blocks.block (selectedIndex first) ≠
            blocks.block (selectedIndex second) :=
        fun heq => hsourceNe (blocks.block_injective heq)
      have hmod :
          blocks.block (selectedIndex first) % (64 : ℤ) =
            blocks.block (selectedIndex second) % (64 : ℤ) := by
        rw [hsameResidue first, hsameResidue second]
      have hblocks := sourceBlockResidue_separated hblockNe hmod
      let z := (blocks.rich (selectedIndex first)).richTrapezoid.trapezoid.left
      have hzFirst : z ∈
          (blocks.rich (selectedIndex first)).richTrapezoid.trapezoid.core := by
        exact ⟨le_rfl,
          (blocks.rich (selectedIndex first)).richTrapezoid.trapezoid.left_lt_right.le⟩
      have hzSecond : z ∈
          (blocks.rich (selectedIndex second)).richTrapezoid.trapezoid.core := by
        change (blocks.rich (selectedIndex first)).richTrapezoid.trapezoid =
          (blocks.rich (selectedIndex second)).richTrapezoid.trapezoid at htrapezoid
        rw [← htrapezoid]
        exact hzFirst
      have hsep := pureWZ2SourceHorizontalShiftedBlockCores_separated
        (blocks.rich (selectedIndex first))
        (blocks.rich (selectedIndex second))
        blocks.shift
        (blocks.block (selectedIndex first))
        (blocks.block (selectedIndex second))
        (blocks.left_eq (selectedIndex first))
        (blocks.left_eq (selectedIndex second)) hblocks
        z hzFirst z hzSecond
      have hscalePos : 0 < pureWZ2SourceHorizontalFinalScale rho := by
        unfold pureWZ2SourceHorizontalFinalScale
        nlinarith [(blocks.pipeline (selectedIndex first)).line.rho_pos]
      exact (not_le_of_gt (Real.sqrt_pos.mpr hscalePos)) (by simpa using hsep)
    separated_cores := by
      intro first second htrapezoidNe
      have hne : first ≠ second := by
        intro heq
        subst second
        exact htrapezoidNe rfl
      have hsourceNe : selectedIndex first ≠ selectedIndex second := by
        intro heq
        exact hne (hselectedIndexInjective heq)
      have hblockNe :
          blocks.block (selectedIndex first) ≠
            blocks.block (selectedIndex second) :=
        fun heq => hsourceNe (blocks.block_injective heq)
      have hmod :
          blocks.block (selectedIndex first) % (64 : ℤ) =
            blocks.block (selectedIndex second) % (64 : ℤ) := by
        rw [hsameResidue first, hsameResidue second]
      exact pureWZ2SourceHorizontalShiftedBlockCores_separated
        (blocks.rich (selectedIndex first))
        (blocks.rich (selectedIndex second))
        blocks.shift
        (blocks.block (selectedIndex first))
        (blocks.block (selectedIndex second))
        (blocks.left_eq (selectedIndex first))
        (blocks.left_eq (selectedIndex second))
        (sourceBlockResidue_separated hblockNe hmod)
  }
  have hselectedMass :
      (∑ index ∈ selected, weight index) =
        ∑ index : Fin family.windowCount,
          (family.rich index).heightLift.shading.mass := by
    calc
      (∑ index ∈ selected, weight index) =
          ∑ index : selected, weight index.1 :=
        Finset.sum_subtype selected (fun _ => Iff.rfl) weight
      _ = ∑ index : Fin selected.card,
          weight (selectedEquiv.symm index).1 := by
        exact (Equiv.sum_comp selectedEquiv.symm
          (fun index : selected => weight index.1)).symm
      _ = ∑ index : Fin family.windowCount,
          (family.rich index).heightLift.shading.mass := rfl
  have htotal :
      (∑ index : Fin blocks.indexCount,
          (blocks.rich index).heightLift.shading.mass) ≤
        64 * family.shading.mass := by
    rw [PureWZ2SourceHorizontalWindowFamilyData.shading_mass_eq_sum family]
    calc
      (∑ index : Fin blocks.indexCount,
          (blocks.rich index).heightLift.shading.mass) ≤
          64 * ∑ index : Fin family.windowCount,
            (family.rich index).heightLift.shading.mass := by
        simpa [weight, selected, hselectedMass] using hretained
      _ = 64 * ∑ index : Fin family.windowCount,
            (family.rich index).heightLift.shading.mass := rfl
  exact ⟨{
    residue := residue
    selected := selected
    selected_eq := by
      apply Finset.ext
      intro index
      simp only [selected, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro h
        exact congrArg Fin.val h
      · intro h
        exact Fin.ext h
    selected_nonempty := hselectedNonempty
    family := family
    total_mass_le := htotal
  }⟩

end Kakeya.Assouad
