import MyLeanRepo.Kakeya.Assouad.PropStickyCallerRootedNestedSchedule
import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12CoverSynchronization

/-!
# Caller-rooted synchronized exact-cover schedule

The historical caller-rooted schedule records the exact caller entry, but it
does not expose the provenance of every other entry.  This wrapper repeats the
same finite chain construction using the canonical `Classical.choice` witness
at every exact scale.  Synchronization is retained as a higher-order transport:
constructing the schedule requires no synchronization hypothesis, while any
later synchronization theorem for the canonical witnesses transports to every
schedule coordinate.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

/-- The canonical exact-scale witness selected from the historical CWA. -/
noncomputable def wz2PaperCanonicalScaleData
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant : ENNReal}
    (cwa : WZ2PaperCWAAtEveryScale family ambientConstant)
    (rho : Kakeya.Streamlined.AdmissibleScale delta) :
    WZ2PaperScaleCoverData family rho ambientConstant :=
  Classical.choice (cwa.2.2.2 rho)

/--
A historical caller-rooted nested schedule built from canonical exact-scale
witnesses, together with higher-order synchronization transport.
-/
structure WZ2PaperCallerRootedSynchronizedScheduleData
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (ambientConstant outputConstant : ENNReal)
    (caller : Kakeya.Streamlined.AdmissibleScale delta)
    (cwa : WZ2PaperCWAAtEveryScale family ambientConstant) where
  nestedSchedule :
    WZ2PaperCallerRootedNestedScheduleData
      ambientConstant outputConstant caller
        (wz2PaperCanonicalScaleData cwa caller)
  canonical_scaleData_eq :
    ∀ coordinate,
      HEq (nestedSchedule.scaleData coordinate)
        (wz2PaperCanonicalScaleData cwa
          (nestedSchedule.scale coordinate))
  scaleSynchronization :
    (∀ rho : Kakeya.Streamlined.AdmissibleScale delta,
      WZ2PaperPureInternalCoverSynchronization
        family (wz2PaperCanonicalScaleData cwa rho).coarse
        (wz2PaperCanonicalScaleData cwa rho).cover) →
      ∀ coordinate,
        WZ2PaperPureInternalCoverSynchronization
          family
          (nestedSchedule.scaleData coordinate).coarse
          (nestedSchedule.scaleData coordinate).cover

namespace WZ2PaperCallerRootedSynchronizedScheduleData

/-- Apply the retained higher-order transport at one schedule coordinate. -/
theorem coordinateSynchronization
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant outputConstant : ENNReal}
    {caller : Kakeya.Streamlined.AdmissibleScale delta}
    {cwa : WZ2PaperCWAAtEveryScale family ambientConstant}
    (data :
      WZ2PaperCallerRootedSynchronizedScheduleData
        ambientConstant outputConstant caller cwa)
    (canonicalSynchronization :
      ∀ rho : Kakeya.Streamlined.AdmissibleScale delta,
        WZ2PaperPureInternalCoverSynchronization
          family (wz2PaperCanonicalScaleData cwa rho).coarse
          (wz2PaperCanonicalScaleData cwa rho).cover)
    (coordinate : Fin data.nestedSchedule.scaleCount) :
    WZ2PaperPureInternalCoverSynchronization
      family
      (data.nestedSchedule.scaleData coordinate).coarse
      (data.nestedSchedule.scaleData coordinate).cover :=
  data.scaleSynchronization canonicalSynchronization coordinate

end WZ2PaperCallerRootedSynchronizedScheduleData

/--
Choose a caller-rooted nested schedule from the canonical witnesses of one
exact-scale CWA.  No synchronization premise is required.
-/
def WZ2PropStickyCallerRootedSynchronizedScheduleStatement : Prop :=
  ∀ {delta : ℝ},
    ∀ {family : Kakeya.Streamlined.TubeFamily delta},
      ∀ {ambientConstant outputConstant : ENNReal},
        ∀ {levelCount : ℕ},
          ∀ (schedule :
              WZ2PaperFiniteNearbyScheduleData
                (family := family)
                ambientConstant outputConstant levelCount),
            ∀ (cwa :
                WZ2PaperCWAAtEveryScale
                  family ambientConstant),
                ∀ (caller :
                    Kakeya.Streamlined.AdmissibleScale delta),
                  ∀ (callerIndex : ℕ),
                    ∀ (hcallerIndex :
                        callerIndex =
                          (schedule.representative caller).val),
                      ∀ (hcallerLower : 2 ≤ callerIndex),
                      ∀ (hcallerUpper :
                          callerIndex + 2 <
                            schedule.gridTopIndex),
                      let below : Fin schedule.scaleCount :=
                        ⟨callerIndex - 2, by
                          rw [schedule.scaleCount_eq]
                          omega⟩
                      let above : Fin schedule.scaleCount :=
                        ⟨callerIndex + 1, by
                          rw [schedule.scaleCount_eq]
                          omega⟩
                      let beforeTop : Fin schedule.scaleCount :=
                        ⟨schedule.gridTopIndex - 2, by
                          rw [schedule.scaleCount_eq]
                          omega⟩
                      2 * (schedule.requested below).1 ≤ caller.1 →
                      2 * caller.1 ≤
                        (schedule.requested above).1 →
                      2 * (schedule.requested beforeTop).1 ≤ 1 →
                      1 ≤ ambientConstant →
                      ambientConstant ≠ ⊤ →
                      ambientConstant ^ 3 ≤ outputConstant →
                        ∃ data :
                            WZ2PaperCallerRootedSynchronizedScheduleData
                              ambientConstant outputConstant
                              caller cwa,
                          data.nestedSchedule.scaleCount =
                            schedule.scaleCount

theorem wz2_prop_sticky_caller_rooted_synchronized_schedule :
    WZ2PropStickyCallerRootedSynchronizedScheduleStatement := by
  intro delta family ambientConstant outputConstant levelCount
    schedule cwa caller callerIndex
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
        ⟨caller, wz2PaperCanonicalScaleData cwa caller⟩
      else
        ⟨schedule.requested (chain.sourceIndex coordinate),
          wz2PaperCanonicalScaleData cwa
            (schedule.requested (chain.sourceIndex coordinate))⟩
  let forwardSynchronization :
      (∀ rho : Kakeya.Streamlined.AdmissibleScale delta,
        WZ2PaperPureInternalCoverSynchronization
          family (wz2PaperCanonicalScaleData cwa rho).coarse
          (wz2PaperCanonicalScaleData cwa rho).cover) →
        ∀ coordinate,
          WZ2PaperPureInternalCoverSynchronization
            family
            (forwardEntry coordinate).2.coarse
            (forwardEntry coordinate).2.cover :=
    fun canonicalSynchronization coordinate => by
      by_cases hcaller :
          coordinate ∈ chain.callerCoordinate
      · have hentry :
            forwardEntry coordinate =
              (⟨caller, wz2PaperCanonicalScaleData cwa caller⟩ :
                Σ scale : Kakeya.Streamlined.AdmissibleScale delta,
                  WZ2PaperScaleCoverData
                    family scale ambientConstant) := by
          simp [forwardEntry, hcaller]
        rw [hentry]
        exact canonicalSynchronization caller
      · have hentry :
            forwardEntry coordinate =
              ⟨schedule.requested (chain.sourceIndex coordinate),
                wz2PaperCanonicalScaleData cwa
                  (schedule.requested
                    (chain.sourceIndex coordinate))⟩ := by
          simp [forwardEntry, hcaller]
        rw [hentry]
        exact
          canonicalSynchronization
            (schedule.requested (chain.sourceIndex coordinate))
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
              (⟨caller, wz2PaperCanonicalScaleData cwa caller⟩ :
                Σ scale : Kakeya.Streamlined.AdmissibleScale delta,
                  WZ2PaperScaleCoverData
                    family scale ambientConstant) := by
          simp [forwardEntry, hfineMem]
        have hcoarseEntry :
            forwardEntry coarse =
              (⟨caller, wz2PaperCanonicalScaleData cwa caller⟩ :
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
                wz2PaperCanonicalScaleData cwa
                  (schedule.requested
                    (chain.sourceIndex fine))⟩ := by
          simp [forwardEntry, hfineNotMem]
        have hcoarseEntry :
            forwardEntry coarse =
              ⟨schedule.requested (chain.sourceIndex coarse),
                wz2PaperCanonicalScaleData cwa
                  (schedule.requested
                    (chain.sourceIndex coarse))⟩ := by
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
        (⟨caller, wz2PaperCanonicalScaleData cwa caller⟩ :
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
  let nestedSchedule :
      WZ2PaperCallerRootedNestedScheduleData
        ambientConstant outputConstant caller
          (wz2PaperCanonicalScaleData cwa caller) :=
    {
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
    }
  have hcanonicalScaleData :
      ∀ coordinate,
        HEq (nestedSchedule.scaleData coordinate)
          (wz2PaperCanonicalScaleData cwa
            (nestedSchedule.scale coordinate)) := by
    intro coordinate
    let forwardCoordinate := reverseIndex coordinate
    change
      HEq (forwardEntry forwardCoordinate).2
        (wz2PaperCanonicalScaleData cwa
          (forwardEntry forwardCoordinate).1)
    by_cases hcaller :
        forwardCoordinate ∈ chain.callerCoordinate
    · have hforward :
          forwardEntry forwardCoordinate =
            (⟨caller, wz2PaperCanonicalScaleData cwa caller⟩ :
              Σ scale : Kakeya.Streamlined.AdmissibleScale delta,
                WZ2PaperScaleCoverData
                  family scale ambientConstant) := by
        simp [forwardEntry, hcaller]
      rw [hforward]
    · have hforward :
          forwardEntry forwardCoordinate =
            (⟨schedule.requested
                (chain.sourceIndex forwardCoordinate),
              wz2PaperCanonicalScaleData cwa
                (schedule.requested
                  (chain.sourceIndex forwardCoordinate))⟩ :
              Σ scale : Kakeya.Streamlined.AdmissibleScale delta,
                WZ2PaperScaleCoverData
                  family scale ambientConstant) := by
        simp [forwardEntry, hcaller]
      rw [hforward]
  let synchronizedSchedule :
      WZ2PaperCallerRootedSynchronizedScheduleData
        ambientConstant outputConstant caller cwa :=
    {
      nestedSchedule := nestedSchedule
      canonical_scaleData_eq := hcanonicalScaleData
      scaleSynchronization := by
        intro canonicalSynchronization coordinate
        change
          WZ2PaperPureInternalCoverSynchronization
            family
            (entry coordinate).2.coarse
            (entry coordinate).2.cover
        exact
          forwardSynchronization canonicalSynchronization
            (reverseIndex coordinate)
    }
  exact ⟨synchronizedSchedule, rfl⟩

end Kakeya.Assouad

end
