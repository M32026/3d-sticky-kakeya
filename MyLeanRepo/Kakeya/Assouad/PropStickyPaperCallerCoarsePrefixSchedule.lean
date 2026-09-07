import MyLeanRepo.Kakeya.Assouad.PropStickyCallerNestedTransitivity
import MyLeanRepo.Kakeya.Assouad.PropStickyNestedQuotientCounting

/-!
# Nested prefix schedule on caller coarse parents

The strict source tree induces a finite nested family of parent maps on the
caller coarse family itself.  At the terminal coordinate the parent map is
the identity; at earlier coordinates it sends a caller parent to the unique
coarser strict parent containing its complete caller fiber.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

private theorem parent_eq_of_scale_data_heq_prefix
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {sourceScale targetScale :
      Kakeya.Streamlined.AdmissibleScale delta}
    {constant : ENNReal}
    {sourceData :
      WZ2PaperScaleCoverData family sourceScale constant}
    {targetData :
      WZ2PaperScaleCoverData family targetScale constant}
    (hscale : sourceScale = targetScale)
    (hdata : HEq sourceData targetData)
    {first second : Fin family.card}
    (hparent :
      sourceData.cover.parent first =
        sourceData.cover.parent second) :
    targetData.cover.parent first =
      targetData.cover.parent second := by
  subst targetScale
  have hdataEq : sourceData = targetData :=
    eq_of_heq hdata
  rwa [← hdataEq]

def wz2PaperCallerCoarsePrefixScaleCount
    {delta sourceLoss stableLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading source}
    {caller : Kakeya.Streamlined.AdmissibleScale delta}
    {preparationExponent : ℕ}
    (prepared :
      WZ2PaperCallerStrictPreparationData
        (sourceLoss := sourceLoss)
        (stableLoss := stableLoss)
        shading caller preparationExponent) : ℕ :=
  prepared.callerLevel.val + 1

def wz2PaperCallerCoarsePrefixCoordinate
    {delta sourceLoss stableLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading source}
    {caller : Kakeya.Streamlined.AdmissibleScale delta}
    {preparationExponent : ℕ}
    (prepared :
      WZ2PaperCallerStrictPreparationData
        (sourceLoss := sourceLoss)
        (stableLoss := stableLoss)
        shading caller preparationExponent)
    (coordinate :
      Fin (wz2PaperCallerCoarsePrefixScaleCount prepared)) :
    Fin prepared.strictScaleCount :=
  ⟨coordinate.val, by
    have hprefix :
        coordinate.val < prepared.callerLevel.val + 1 :=
      coordinate.isLt
    have hcaller := prepared.callerLevel.isLt
    omega⟩

structure WZ2PaperCallerCoarsePrefixScheduleData
    {delta sourceLoss stableLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading source}
    {caller : Kakeya.Streamlined.AdmissibleScale delta}
    {preparationExponent : ℕ}
    (prepared :
      WZ2PaperCallerStrictPreparationData
        (sourceLoss := sourceLoss)
        (stableLoss := stableLoss)
        shading caller preparationExponent) where
  representative :
    Fin prepared.callerStrict.coarse.card →
      Fin prepared.refinement.selected.family.card
  representative_parent :
    ∀ parent,
      prepared.callerStrict.cover.parent (representative parent) =
        parent
  parent :
    ∀ coordinate :
        Fin (wz2PaperCallerCoarsePrefixScaleCount prepared),
      Fin prepared.callerStrict.coarse.card →
        Fin prepared.callerStrict.coarse.card
  parent_nested :
    ∀ level : ℕ,
      ∀ hnext :
          level + 1 <
            wz2PaperCallerCoarsePrefixScaleCount prepared,
        ∀ first second : Fin prepared.callerStrict.coarse.card,
          parent ⟨level + 1, hnext⟩ first =
              parent ⟨level + 1, hnext⟩ second →
            parent
                ⟨level, Nat.lt_of_succ_lt hnext⟩ first =
              parent
                ⟨level, Nat.lt_of_succ_lt hnext⟩ second
  parent_uniform :
    ∀ coordinate,
      ∀ first second : Fin prepared.callerStrict.coarse.card,
        0 <
            ((Finset.univ :
              Finset (Fin prepared.callerStrict.coarse.card)).filter
              fun current => parent coordinate current = first).card →
        0 <
            ((Finset.univ :
              Finset (Fin prepared.callerStrict.coarse.card)).filter
              fun current => parent coordinate current = second).card →
        (((Finset.univ :
          Finset (Fin prepared.callerStrict.coarse.card)).filter
          fun current => parent coordinate current = first).card :
          ENNReal) ≤
          (prepared.structuralConstant *
            prepared.structuralConstant) *
            (((Finset.univ :
              Finset (Fin prepared.callerStrict.coarse.card)).filter
              fun current => parent coordinate current = second).card :
              ENNReal)
  parent_eq_iff_strict :
    ∀ coordinate,
      ∀ first second : Fin prepared.callerStrict.coarse.card,
        parent coordinate first = parent coordinate second ↔
          (prepared.strictScaleData
            (wz2PaperCallerCoarsePrefixCoordinate
              prepared coordinate)).cover.parent
              (representative first) =
            (prepared.strictScaleData
              (wz2PaperCallerCoarsePrefixCoordinate
                prepared coordinate)).cover.parent
              (representative second)
  terminal :
    Fin (wz2PaperCallerCoarsePrefixScaleCount prepared)
  terminal_eq :
    terminal =
      ⟨prepared.callerLevel.val, by
        simp [wz2PaperCallerCoarsePrefixScaleCount]⟩
  terminal_parent :
    ∀ coarseParent : Fin prepared.callerStrict.coarse.card,
      parent terminal coarseParent = coarseParent

theorem wz2_paper_caller_coarse_prefix_schedule
    {delta sourceLoss stableLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading source}
    {caller : Kakeya.Streamlined.AdmissibleScale delta}
    {preparationExponent : ℕ}
    (prepared :
      WZ2PaperCallerStrictPreparationData
        (sourceLoss := sourceLoss)
        (stableLoss := stableLoss)
        shading caller preparationExponent) :
    Nonempty (WZ2PaperCallerCoarsePrefixScheduleData prepared) := by
  let representative :
      Fin prepared.callerStrict.coarse.card →
        Fin prepared.refinement.selected.family.card :=
    fun parent =>
      Classical.choose
        (prepared.callerStrict.cover.parent_surjective parent)
  have hRepresentative :
      ∀ parent,
        prepared.callerStrict.cover.parent (representative parent) =
          parent :=
    fun parent =>
      Classical.choose_spec
        (prepared.callerStrict.cover.parent_surjective parent)
  let strictParent :
      ∀ coordinate :
          Fin (wz2PaperCallerCoarsePrefixScaleCount prepared),
        Fin prepared.callerStrict.coarse.card →
          Fin
            (prepared.strictScaleData
              (wz2PaperCallerCoarsePrefixCoordinate
                prepared coordinate)).coarse.card :=
    fun coordinate coarseParent =>
      (prepared.strictScaleData
        (wz2PaperCallerCoarsePrefixCoordinate prepared coordinate))
        |>.cover.parent (representative coarseParent)
  let parentClass :
      ∀ coordinate :
          Fin (wz2PaperCallerCoarsePrefixScaleCount prepared),
        Fin prepared.callerStrict.coarse.card →
          Finset (Fin prepared.callerStrict.coarse.card) :=
    fun coordinate coarseParent =>
      Finset.univ.filter fun candidate =>
        strictParent coordinate candidate =
          strictParent coordinate coarseParent
  have hParentClassNonempty :
      ∀ coordinate coarseParent,
        (parentClass coordinate coarseParent).Nonempty := by
    intro coordinate coarseParent
    exact
      ⟨coarseParent,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩
  let parent :
      ∀ coordinate,
        Fin prepared.callerStrict.coarse.card →
          Fin prepared.callerStrict.coarse.card :=
    fun coordinate coarseParent =>
      if htop : coordinate.val = prepared.callerLevel.val then
        coarseParent
      else
        (parentClass coordinate coarseParent).min'
          (hParentClassNonempty coordinate coarseParent)
  have hParentOfStrict :
      ∀ coordinate :
          Fin (wz2PaperCallerCoarsePrefixScaleCount prepared),
        coordinate.val < prepared.callerLevel.val →
        ∀ first second : Fin prepared.callerStrict.coarse.card,
        strictParent coordinate first =
            strictParent coordinate second →
          parent coordinate first = parent coordinate second := by
    intro coordinate hbelow first second hstrict
    have htop :
        coordinate.val ≠ prepared.callerLevel.val :=
      hbelow.ne
    have hClass :
        parentClass coordinate first =
          parentClass coordinate second := by
      ext candidate
      simp only [parentClass, Finset.mem_filter,
        Finset.mem_univ, true_and]
      rw [hstrict]
    simp only [parent, dif_neg htop]
    apply le_antisymm
    · apply Finset.min'_le
      rw [hClass]
      exact Finset.min'_mem _ _
    · apply Finset.min'_le
      rw [← hClass]
      exact Finset.min'_mem _ _
  have hParentClassMem :
      ∀ coordinate coarseParent,
        parent coordinate coarseParent ∈
          parentClass coordinate coarseParent := by
    intro coordinate coarseParent
    by_cases htop :
        coordinate.val = prepared.callerLevel.val
    · simp only [parent, dif_pos htop]
      exact
        Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, rfl⟩
    · simp only [parent, dif_neg htop]
      exact Finset.min'_mem _ _
  have hStrictOfParent :
      ∀ coordinate,
        ∀ first second : Fin prepared.callerStrict.coarse.card,
          parent coordinate first = parent coordinate second →
            strictParent coordinate first =
              strictParent coordinate second := by
    intro coordinate first second hparent
    have hfirst :=
      (Finset.mem_filter.mp
        (hParentClassMem coordinate first)).2
    have hsecond :=
      (Finset.mem_filter.mp
        (hParentClassMem coordinate second)).2
    calc
      strictParent coordinate first =
          strictParent coordinate (parent coordinate first) :=
        hfirst.symm
      _ =
          strictParent coordinate (parent coordinate second) := by
        rw [hparent]
      _ = strictParent coordinate second :=
        hsecond
  have hNested :
      ∀ (level : ℕ),
        ∀ (hnext :
            level + 1 <
              wz2PaperCallerCoarsePrefixScaleCount prepared),
          ∀ (first second :
              Fin prepared.callerStrict.coarse.card),
            parent ⟨level + 1, hnext⟩ first =
                parent ⟨level + 1, hnext⟩ second →
              parent
                  ⟨level, Nat.lt_of_succ_lt hnext⟩ first =
                parent
                  ⟨level, Nat.lt_of_succ_lt hnext⟩ second := by
    intro level hnext first second heq
    by_cases hterminal :
        level + 1 = prepared.callerLevel.val
    · have hfirst : first = second := by
        simpa [parent, hterminal] using heq
      subst second
      rfl
    · have hnextBelow :
          level + 1 < prepared.callerLevel.val := by
        dsimp only [wz2PaperCallerCoarsePrefixScaleCount] at hnext
        omega
      have hlevelBelow : level < prepared.callerLevel.val := by
        omega
      let finer :
          Fin (wz2PaperCallerCoarsePrefixScaleCount prepared) :=
        ⟨level + 1, hnext⟩
      let coarser :
          Fin (wz2PaperCallerCoarsePrefixScaleCount prepared) :=
        ⟨level, Nat.lt_of_succ_lt hnext⟩
      have hFirstMem :
          parent finer first ∈ parentClass finer first := by
        dsimp only [parent, finer]
        rw [dif_neg hterminal]
        exact Finset.min'_mem _ _
      have hSecondMem :
          parent finer second ∈ parentClass finer second := by
        dsimp only [parent, finer]
        rw [dif_neg hterminal]
        exact Finset.min'_mem _ _
      have hFineStrict :
          strictParent finer first =
            strictParent finer second := by
        have hFirstEq :=
          (Finset.mem_filter.mp hFirstMem).2
        have hSecondEq :=
          (Finset.mem_filter.mp hSecondMem).2
        have hLabel :
            parent finer first = parent finer second := by
          exact heq
        calc
          strictParent finer first =
              strictParent finer (parent finer first) :=
            hFirstEq.symm
          _ = strictParent finer (parent finer second) := by
            rw [hLabel]
          _ = strictParent finer second := hSecondEq
      have hStrict :=
        prepared.strict_parent_nested level
          (hnextBelow.trans prepared.callerLevel.isLt)
          (representative first) (representative second)
      have hCoarseStrict :
          (prepared.strictScaleData
            ⟨level + 1,
              hnextBelow.trans
                prepared.callerLevel.isLt⟩).cover.parent
              (representative first) =
            (prepared.strictScaleData
              ⟨level + 1,
                hnextBelow.trans
                  prepared.callerLevel.isLt⟩).cover.parent
              (representative second) := by
        simpa [strictParent, finer,
          wz2PaperCallerCoarsePrefixCoordinate] using hFineStrict
      have hcoarse := hStrict hCoarseStrict
      apply hParentOfStrict coarser hlevelBelow first second
      simpa [strictParent, coarser,
        wz2PaperCallerCoarsePrefixCoordinate] using hcoarse
  have hParentUniform :
      ∀ coordinate,
        ∀ first second : Fin prepared.callerStrict.coarse.card,
          0 <
              ((Finset.univ :
                Finset (Fin prepared.callerStrict.coarse.card)).filter
                fun current => parent coordinate current = first).card →
          0 <
              ((Finset.univ :
                Finset (Fin prepared.callerStrict.coarse.card)).filter
                fun current => parent coordinate current = second).card →
          (((Finset.univ :
            Finset (Fin prepared.callerStrict.coarse.card)).filter
            fun current => parent coordinate current = first).card :
            ENNReal) ≤
            (prepared.structuralConstant *
              prepared.structuralConstant) *
              (((Finset.univ :
                Finset (Fin prepared.callerStrict.coarse.card)).filter
                fun current => parent coordinate current = second).card :
                ENNReal) := by
    intro coordinate first second hfirst hsecond
    by_cases htop :
        coordinate.val = prepared.callerLevel.val
    · have hParentIdentity :
          ∀ current : Fin prepared.callerStrict.coarse.card,
            parent coordinate current = current := by
        intro current
        simp [parent, htop]
      have hFirstFilter :
          (Finset.univ :
            Finset (Fin prepared.callerStrict.coarse.card)).filter
              (fun current => parent coordinate current = first) =
            {first} := by
        ext current
        simp [hParentIdentity current]
      have hSecondFilter :
          (Finset.univ :
            Finset (Fin prepared.callerStrict.coarse.card)).filter
              (fun current => parent coordinate current = second) =
            {second} := by
        ext current
        simp [hParentIdentity current]
      rw [hFirstFilter, hSecondFilter]
      simp only [Finset.card_singleton, Nat.cast_one, mul_one]
      have hOne : (1 : ENNReal) ≤ prepared.structuralConstant :=
        prepared.cwa_nearby.1
      calc
        (1 : ENNReal) ≤ prepared.structuralConstant := hOne
        _ ≤
            prepared.structuralConstant *
              prepared.structuralConstant := by
          simpa using
            mul_le_mul_left'
              hOne prepared.structuralConstant
    · have hbelow :
          coordinate.val < prepared.callerLevel.val := by
        have hcoordinate :
            coordinate.val <
              prepared.callerLevel.val + 1 :=
          coordinate.isLt
        omega
      have hcoordinateLe :
          (wz2PaperCallerCoarsePrefixCoordinate
            prepared coordinate).val ≤
            prepared.callerLevel.val := by
        exact hbelow.le
      have hCompatible :
          ∀ source,
            strictParent coordinate
                (prepared.callerStrict.cover.parent source) =
              (prepared.strictScaleData
                (wz2PaperCallerCoarsePrefixCoordinate
                  prepared coordinate)).cover.parent source := by
        intro source
        dsimp only [strictParent]
        exact
          prepared.caller_parent_nested
            (wz2PaperCallerCoarsePrefixCoordinate
              prepared coordinate)
            hcoordinateLe
            (representative
              (prepared.callerStrict.cover.parent source))
            source
            (hRepresentative
              (prepared.callerStrict.cover.parent source))
      letI : Nonempty (Fin prepared.callerStrict.coarse.card) := by
        let sourceIndex : Fin prepared.refinement.selected.family.card :=
          ⟨0, prepared.selected_card_pos⟩
        exact
          ⟨prepared.callerStrict.cover.parent sourceIndex⟩
      have hQuotientUniform :=
        nested_quotient_parent_count_uniform_square
          prepared.callerStrict.cover.parent
          (prepared.strictScaleData
            (wz2PaperCallerCoarsePrefixCoordinate
              prepared coordinate)).cover.parent
          (strictParent coordinate)
          prepared.callerStrict.cover.parent_surjective
          hCompatible prepared.structuralConstant
          (by
            intro firstParent secondParent
            simpa only [
              prepared.callerStrict.cover.fullFiberCount_eq,
              WZ1PaperTubeCover.fiberIndices
            ] using
              prepared.callerStrict.full_fiber_uniform
                firstParent secondParent)
          (by
            intro firstParent secondParent
            simpa only [
              (prepared.strictScaleData
                (wz2PaperCallerCoarsePrefixCoordinate
                  prepared coordinate)).cover.fullFiberCount_eq,
              WZ1PaperTubeCover.fiberIndices
            ] using
              (prepared.strictScaleData
                (wz2PaperCallerCoarsePrefixCoordinate
                  prepared coordinate)).full_fiber_uniform
                firstParent secondParent)
      have hClassFilter :
          ∀ label : Fin prepared.callerStrict.coarse.card,
            0 <
                ((Finset.univ :
                  Finset (Fin prepared.callerStrict.coarse.card)).filter
                  fun current => parent coordinate current = label).card →
            (Finset.univ :
              Finset (Fin prepared.callerStrict.coarse.card)).filter
                (fun current => parent coordinate current = label) =
              (Finset.univ :
                Finset (Fin prepared.callerStrict.coarse.card)).filter
                (fun current =>
                  strictParent coordinate current =
                    strictParent coordinate label) := by
        intro label hlabel
        rcases Finset.card_pos.mp hlabel with
          ⟨anchor, hanchor⟩
        have hAnchorParent :
            parent coordinate anchor = label :=
          (Finset.mem_filter.mp hanchor).2
        have hLabelStrict :
            strictParent coordinate label =
              strictParent coordinate anchor := by
          have hmem :=
            (Finset.mem_filter.mp
              (hParentClassMem coordinate anchor)).2
          simpa [hAnchorParent] using hmem
        ext current
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · intro hcurrent
          have hmem :=
            (Finset.mem_filter.mp
              (hParentClassMem coordinate current)).2
          calc
            strictParent coordinate current =
                strictParent coordinate
                  (parent coordinate current) :=
              hmem.symm
            _ = strictParent coordinate label := by
              rw [hcurrent]
        · intro hcurrent
          have hCurrentAnchor :
              strictParent coordinate current =
                strictParent coordinate anchor := by
            exact hcurrent.trans hLabelStrict
          exact
            (hParentOfStrict coordinate hbelow
              current anchor hCurrentAnchor).trans
              hAnchorParent
      rw [hClassFilter first hfirst, hClassFilter second hsecond]
      exact
        hQuotientUniform
          (strictParent coordinate first)
          (strictParent coordinate second)
  let terminal :
      Fin (wz2PaperCallerCoarsePrefixScaleCount prepared) :=
    ⟨prepared.callerLevel.val, by
      simp [wz2PaperCallerCoarsePrefixScaleCount]⟩
  have hTerminal :
      ∀ coarseParent,
        parent terminal coarseParent = coarseParent := by
    intro coarseParent
    simp [parent, terminal]
  exact
    ⟨{
      representative := representative
      representative_parent := hRepresentative
      parent := parent
      parent_nested := hNested
      parent_uniform := hParentUniform
      parent_eq_iff_strict := by
        intro coordinate first second
        constructor
        · intro hparent
          simpa [strictParent,
            wz2PaperCallerCoarsePrefixCoordinate] using
              hStrictOfParent coordinate first second hparent
        · intro hstrict
          by_cases htop :
              coordinate.val = prepared.callerLevel.val
          · have hfirst : first = second := by
              have hCallerFirst :=
                hRepresentative first
              have hCallerSecond :=
                hRepresentative second
              have hScaleData :
                  HEq
                    (prepared.strictScaleData
                      (wz2PaperCallerCoarsePrefixCoordinate
                        prepared coordinate))
                    prepared.callerStrict := by
                have hCoordinate :
                    wz2PaperCallerCoarsePrefixCoordinate
                        prepared coordinate =
                      prepared.callerLevel := by
                  apply Fin.ext
                  exact htop
                rw [hCoordinate]
                exact prepared.callerScaleData_eq
              have hStrict' :
                  prepared.callerStrict.cover.parent
                      (representative first) =
                    prepared.callerStrict.cover.parent
                      (representative second) := by
                exact
                  parent_eq_of_scale_data_heq_prefix
                    (by
                      rw [show
                        wz2PaperCallerCoarsePrefixCoordinate
                            prepared coordinate =
                          prepared.callerLevel by
                            apply Fin.ext
                            exact htop]
                      exact prepared.callerScale_eq)
                    hScaleData hstrict
              rw [hCallerFirst, hCallerSecond] at hStrict'
              exact hStrict'
            subst second
            rfl
          · have hbelow :
                coordinate.val < prepared.callerLevel.val := by
              have hcoordinate :
                  coordinate.val <
                    prepared.callerLevel.val + 1 :=
                coordinate.isLt
              omega
            apply hParentOfStrict coordinate hbelow first second
            simpa [strictParent,
              wz2PaperCallerCoarsePrefixCoordinate] using hstrict
      terminal := terminal
      terminal_eq := rfl
      terminal_parent := hTerminal
    }⟩

end Kakeya.Assouad

end
