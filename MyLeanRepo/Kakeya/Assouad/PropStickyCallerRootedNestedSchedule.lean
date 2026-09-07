import MyLeanRepo.Kakeya.Assouad.PropStickyCallerRootedNestedScheduleStatements
import MyLeanRepo.Kakeya.Assouad.PropStickyCallerRootedChain

/-! # Caller-rooted nested geometric schedule -/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

theorem wz2_prop_sticky_caller_rooted_nested_schedule :
    WZ2PropStickyCallerRootedNestedScheduleStatement := by
  intro delta family ambientConstant outputConstant levelCount
    schedule strictAmbient caller callerAmbient callerIndex
    hcallerIndex hcallerLower hcallerUpper
  dsimp only
  intro hbelow hcallerAbove hbeforeTop hambientOne
    hambientTop houtput
  rcases
      wz2_prop_sticky_caller_rooted_chain schedule caller
        callerIndex hcallerIndex hcallerLower hcallerUpper
        hbelow hcallerAbove hbeforeTop hambientOne hambientTop
        houtput with
    ⟨chain⟩
  let forwardEntry :
      Fin schedule.scaleCount →
        Σ scale : Kakeya.Streamlined.AdmissibleScale delta,
          WZ2PaperScaleCoverData family scale ambientConstant :=
    fun coordinate =>
      if hcaller : coordinate ∈ chain.callerCoordinate then
        ⟨caller, callerAmbient⟩
      else
        ⟨schedule.requested (chain.sourceIndex coordinate),
          strictAmbient (chain.sourceIndex coordinate)⟩
  have hforwardScale :
      ∀ coordinate,
        (forwardEntry coordinate).1 = chain.entry coordinate := by
    intro coordinate
    by_cases hcaller :
        coordinate ∈ chain.callerCoordinate
    · simp [forwardEntry, hcaller, chain.entry_eq]
    · simp [forwardEntry, hcaller, chain.entry_eq]
  let reverseIndex :
      Fin schedule.scaleCount →
        Fin schedule.scaleCount :=
    fun coordinate =>
      ⟨schedule.scaleCount - 1 - coordinate.val, by
        omega⟩
  have hreverseInvolutive :
      ∀ coordinate,
        reverseIndex (reverseIndex coordinate) = coordinate := by
    intro coordinate
    apply Fin.ext
    dsimp only [reverseIndex]
    omega
  let entry :
      Fin schedule.scaleCount →
        Σ scale : Kakeya.Streamlined.AdmissibleScale delta,
          WZ2PaperScaleCoverData family scale ambientConstant :=
    fun coordinate => forwardEntry (reverseIndex coordinate)
  have hscaleAntitone :
      ∀ first second : Fin schedule.scaleCount,
        first.val ≤ second.val →
          (entry second).1.1 ≤ (entry first).1.1 := by
    intro first second firstLeSecond
    change
      (forwardEntry (reverseIndex second)).1.1 ≤
        (forwardEntry (reverseIndex first)).1.1
    rw [hforwardScale (reverseIndex second),
      hforwardScale (reverseIndex first)]
    apply chain.entry_mono
    dsimp only [reverseIndex]
    omega
  have hforwardNested :
      ∀ level,
        ∀ hnext : level + 1 < schedule.scaleCount,
          ∀ first second : Fin family.card,
            (forwardEntry
                ⟨level, Nat.lt_of_succ_lt hnext⟩).2.cover.parent
                  first =
              (forwardEntry
                ⟨level, Nat.lt_of_succ_lt hnext⟩).2.cover.parent
                  second →
            (forwardEntry ⟨level + 1, hnext⟩).2.cover.parent
                  first =
              (forwardEntry ⟨level + 1, hnext⟩).2.cover.parent
                  second := by
    intro level hnext first second hparent
    let fine : Fin schedule.scaleCount :=
      ⟨level, Nat.lt_of_succ_lt hnext⟩
    let coarse : Fin schedule.scaleCount :=
      ⟨level + 1, hnext⟩
    have hedge :=
      chain.adjacent_same_source_or_le level hnext
    change
      (forwardEntry coarse).2.cover.parent first =
        (forwardEntry coarse).2.cover.parent second
    change
      (forwardEntry fine).2.cover.parent first =
        (forwardEntry fine).2.cover.parent second at hparent
    rcases hedge with hsame | hscale
    · rcases hsame with hcaller | hstrict
      · have hfineMem :
            fine ∈ chain.callerCoordinate := by
          simpa [fine] using hcaller.1
        have hcoarseMem :
            coarse ∈ chain.callerCoordinate := by
          simpa [coarse] using hcaller.2
        have hfineEntry :
            forwardEntry fine =
              (⟨caller, callerAmbient⟩ :
                Σ scale : Kakeya.Streamlined.AdmissibleScale delta,
                  WZ2PaperScaleCoverData
                    family scale ambientConstant) := by
          simp [forwardEntry, hfineMem]
        have hcoarseEntry :
            forwardEntry coarse =
              (⟨caller, callerAmbient⟩ :
                Σ scale : Kakeya.Streamlined.AdmissibleScale delta,
                  WZ2PaperScaleCoverData
                    family scale ambientConstant) := by
          simp [forwardEntry, hcoarseMem]
        rw [hfineEntry] at hparent
        rw [hcoarseEntry]
        exact hparent
      · have hfineNotMem :
            fine ∉ chain.callerCoordinate := by
          simpa [fine] using hstrict.1
        have hcoarseNotMem :
            coarse ∉ chain.callerCoordinate := by
          simpa [coarse] using hstrict.2.1
        have hsourceEq :
            chain.sourceIndex fine =
              chain.sourceIndex coarse := by
          simpa [fine, coarse] using hstrict.2.2
        have hfineEntry :
            forwardEntry fine =
              ⟨schedule.requested (chain.sourceIndex fine),
                strictAmbient (chain.sourceIndex fine)⟩ := by
          simp [forwardEntry, hfineNotMem]
        have hcoarseEntry :
            forwardEntry coarse =
              ⟨schedule.requested (chain.sourceIndex coarse),
                strictAmbient (chain.sourceIndex coarse)⟩ := by
          simp [forwardEntry, hcoarseNotMem]
        rw [hfineEntry] at hparent
        rw [hcoarseEntry]
        rw [← hsourceEq]
        exact hparent
    · have hscale' :
          2 * (forwardEntry fine).1.1 ≤
            (forwardEntry coarse).1.1 := by
        rw [hforwardScale fine, hforwardScale coarse]
        exact hscale
      exact
        (forwardEntry fine).2.cover.fiber_parent_stable
          (forwardEntry coarse).2.cover hscale'
          ((forwardEntry fine).2.cover.parent first)
          rfl hparent.symm
  have hparentNested :
      ∀ level,
        ∀ hnext : level + 1 < schedule.scaleCount,
          ∀ first second : Fin family.card,
            (entry ⟨level + 1, hnext⟩).2.cover.parent first =
                (entry ⟨level + 1, hnext⟩).2.cover.parent second →
              (entry
                  ⟨level, Nat.lt_of_succ_lt hnext⟩).2.cover.parent first =
                (entry
                  ⟨level, Nat.lt_of_succ_lt hnext⟩).2.cover.parent second := by
    intro level hnext first second hparent
    let current : Fin schedule.scaleCount :=
      ⟨level, Nat.lt_of_succ_lt hnext⟩
    let next : Fin schedule.scaleCount :=
      ⟨level + 1, hnext⟩
    let forwardFine := reverseIndex next
    let forwardCoarse := reverseIndex current
    have hadjacent :
        forwardFine.val + 1 = forwardCoarse.val := by
      dsimp only [forwardFine, forwardCoarse, reverseIndex,
        current, next]
      omega
    have hforwardNext :
        forwardFine.val + 1 <
          schedule.scaleCount := by
      rw [hadjacent]
      exact forwardCoarse.isLt
    have hfineEq :
        (⟨forwardFine.val,
            Nat.lt_of_succ_lt hforwardNext⟩ :
          Fin schedule.scaleCount) = forwardFine := by
      apply Fin.ext
      rfl
    have hcoarseEq :
        (⟨forwardFine.val + 1, hforwardNext⟩ :
          Fin schedule.scaleCount) = forwardCoarse := by
      apply Fin.ext
      exact hadjacent
    have hraw :=
      hforwardNested forwardFine.val hforwardNext first second
    change
      (forwardEntry forwardFine).2.cover.parent first =
        (forwardEntry forwardFine).2.cover.parent second at hparent
    rw [hfineEq] at hraw
    have hresult := hraw hparent
    change
      (forwardEntry forwardCoarse).2.cover.parent first =
        (forwardEntry forwardCoarse).2.cover.parent second
    rw [hcoarseEq] at hresult
    exact hresult
  let callerLevel : Fin schedule.scaleCount :=
    reverseIndex chain.callerLevel
  have hcallerEntry :
      HEq (entry callerLevel)
        (⟨caller, callerAmbient⟩ :
          Σ scale : Kakeya.Streamlined.AdmissibleScale delta,
            WZ2PaperScaleCoverData family scale ambientConstant) := by
    have hreverse :
        reverseIndex callerLevel = chain.callerLevel := by
      exact hreverseInvolutive chain.callerLevel
    simp only [entry, hreverse]
    simp [forwardEntry, chain.caller_level_mem]
  let representative :
      Kakeya.Streamlined.AdmissibleScale delta →
        Fin schedule.scaleCount :=
    fun requested =>
      reverseIndex (chain.representative requested)
  have hrepresentativeEntry :
      ∀ requested,
        entry (representative requested) =
          forwardEntry (chain.representative requested) := by
    intro requested
    simp [entry, representative,
      hreverseInvolutive]
  exact
    ⟨{
      scaleCount := schedule.scaleCount
      scaleCount_pos := schedule.scaleCount_pos
      entry := entry
      scale_antitone := hscaleAntitone
      parent_nested := hparentNested
      callerLevel := callerLevel
      caller_entry_eq := hcallerEntry
      representative := representative
      caller_representative_nested := by
        rw [hrepresentativeEntry caller,
          hforwardScale (chain.representative caller)]
        exact chain.caller_representative_nested
      representative_coarse_of_caller_le := by
        intro requested hcallerRequested
        have hforward :=
          chain.representative_above_caller
            requested hcallerRequested
        dsimp only [representative, callerLevel, reverseIndex]
        omega
      representative_fine_of_ambient_le_caller := by
        intro requested hwindow
        have hforward :=
          chain.representative_below_caller
            requested hwindow
        dsimp only [representative, callerLevel, reverseIndex]
        omega
      requested_le := by
        intro requested
        rw [hrepresentativeEntry requested,
          hforwardScale (chain.representative requested)]
        exact chain.requested_le requested
      within_output := by
        intro requested
        rw [hrepresentativeEntry requested,
          hforwardScale (chain.representative requested)]
        exact chain.within_output requested
    }, rfl⟩

end Kakeya.Assouad

end
