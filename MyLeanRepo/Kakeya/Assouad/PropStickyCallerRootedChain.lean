import MyLeanRepo.Kakeya.Assouad.PropStickyCallerRootedNestedScheduleStatements

/-! # Finite caller-rooted geometric chain -/

noncomputable section

namespace Kakeya.Assouad

structure WZ2PaperCallerRootedChainData
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant outputConstant : ENNReal}
    {levelCount : ℕ}
    (schedule :
      WZ2PaperFiniteNearbyScheduleData
        (family := family)
        ambientConstant outputConstant levelCount)
    (caller : Kakeya.Streamlined.AdmissibleScale delta)
    (callerIndex : ℕ) where
  sourceIndex :
    Fin schedule.scaleCount → Fin schedule.scaleCount
  callerCoordinate : Finset (Fin schedule.scaleCount)
  entry :
    Fin schedule.scaleCount →
      Kakeya.Streamlined.AdmissibleScale delta
  entry_eq :
    ∀ coordinate,
      entry coordinate =
        if coordinate ∈ callerCoordinate then caller
        else schedule.requested (sourceIndex coordinate)
  callerLevel : Fin schedule.scaleCount
  caller_level_mem : callerLevel ∈ callerCoordinate
  caller_level_scale : entry callerLevel = caller
  adjacent_same_source_or_le :
    ∀ level,
      ∀ hnext : level + 1 < schedule.scaleCount,
        ((⟨level, Nat.lt_of_succ_lt hnext⟩ ∈
              callerCoordinate ∧
            ⟨level + 1, hnext⟩ ∈ callerCoordinate) ∨
          (⟨level, Nat.lt_of_succ_lt hnext⟩ ∉
                callerCoordinate ∧
            ⟨level + 1, hnext⟩ ∉ callerCoordinate ∧
            sourceIndex
                ⟨level, Nat.lt_of_succ_lt hnext⟩ =
              sourceIndex ⟨level + 1, hnext⟩)) ∨
          2 * (entry
                ⟨level, Nat.lt_of_succ_lt hnext⟩).1 ≤
            (entry ⟨level + 1, hnext⟩).1
  entry_mono :
    ∀ first second : Fin schedule.scaleCount,
      first.1 ≤ second.1 →
        (entry first).1 ≤ (entry second).1
  representative :
    Kakeya.Streamlined.AdmissibleScale delta →
      Fin schedule.scaleCount
  caller_representative_nested :
    2 * caller.1 ≤
      (entry (representative caller)).1
  representative_above_caller :
    ∀ requested,
      caller.1 ≤ requested.1 →
        callerLevel.val ≤ (representative requested).val
  representative_below_caller :
    ∀ requested,
      ambientConstant * ENNReal.ofReal requested.1 ≤
          ENNReal.ofReal caller.1 →
        (representative requested).val ≤ callerLevel.val
  requested_le :
    ∀ requested,
      requested.1 ≤ (entry (representative requested)).1
  within_output :
    ∀ requested,
      ENNReal.ofReal (entry (representative requested)).1 <
        outputConstant * ENNReal.ofReal requested.1

def WZ2PropStickyCallerRootedChainStatement : Prop :=
  ∀ {delta : ℝ},
    ∀ {family : Kakeya.Streamlined.TubeFamily delta},
      ∀ {ambientConstant outputConstant : ENNReal},
        ∀ {levelCount : ℕ},
          ∀ (schedule :
              WZ2PaperFiniteNearbyScheduleData
                (family := family)
                ambientConstant outputConstant levelCount),
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
                        Nonempty
                          (WZ2PaperCallerRootedChainData
                            schedule caller callerIndex)

theorem wz2_prop_sticky_caller_rooted_chain :
    WZ2PropStickyCallerRootedChainStatement := by
  intro delta family ambientConstant outputConstant levelCount
    schedule caller callerIndex hcallerIndex hcallerLower hcallerUpper
  dsimp only
  intro hbelow hcallerAbove hbeforeTop hambientOne hambientTop houtput
  have hdelta : 0 < delta := by
    have hpowerNonnegative :
        0 ≤ ambientConstant.toReal ^ schedule.gridTopIndex :=
      pow_nonneg ENNReal.toReal_nonneg _
    nlinarith [schedule.grid_top_reaches_one]
  let callerLow : Fin schedule.scaleCount :=
    ⟨callerIndex - 1, by
      rw [schedule.scaleCount_eq]
      omega⟩
  let callerHigh : Fin schedule.scaleCount :=
    ⟨callerIndex, by
      rw [schedule.scaleCount_eq]
      omega⟩
  let topMinusOne : Fin schedule.scaleCount :=
    ⟨schedule.gridTopIndex - 1, by
      rw [schedule.scaleCount_eq]
      omega⟩
  let topMinusTwo : Fin schedule.scaleCount :=
    ⟨schedule.gridTopIndex - 2, by
      rw [schedule.scaleCount_eq]
      omega⟩
  let sourceIndex : Fin schedule.scaleCount →
      Fin schedule.scaleCount := fun coordinate =>
    if coordinate = topMinusOne then topMinusTwo else coordinate
  let callerCoordinate : Finset (Fin schedule.scaleCount) :=
    {callerLow, callerHigh}
  let entry : Fin schedule.scaleCount →
      Kakeya.Streamlined.AdmissibleScale delta := fun coordinate =>
    if coordinate ∈ callerCoordinate then caller
    else schedule.requested (sourceIndex coordinate)
  have hcallerLowVal : callerLow.val = callerIndex - 1 := rfl
  have hcallerHighVal : callerHigh.val = callerIndex := rfl
  have htopOneVal :
      topMinusOne.val = schedule.gridTopIndex - 1 := rfl
  have htopTwoVal :
      topMinusTwo.val = schedule.gridTopIndex - 2 := rfl
  have hcallerLowMem : callerLow ∈ callerCoordinate := by
    simp [callerCoordinate]
  have hcallerHighMem : callerHigh ∈ callerCoordinate := by
    simp [callerCoordinate]
  have htopOneNotCaller :
      topMinusOne ∉ callerCoordinate := by
    simp only [callerCoordinate, Finset.mem_insert,
      Finset.mem_singleton]
    rw [not_or]
    constructor <;> intro heq
    · have hval := congrArg Fin.val heq
      dsimp only [topMinusOne, callerLow] at hval
      omega
    · have hval := congrArg Fin.val heq
      dsimp only [topMinusOne, callerHigh] at hval
      omega
  have htopTwoNotCaller :
      topMinusTwo ∉ callerCoordinate := by
    simp only [callerCoordinate, Finset.mem_insert,
      Finset.mem_singleton]
    rw [not_or]
    constructor <;> intro heq
    · have hval := congrArg Fin.val heq
      dsimp only [topMinusTwo, callerLow] at hval
      omega
    · have hval := congrArg Fin.val heq
      dsimp only [topMinusTwo, callerHigh] at hval
      omega
  have hsourceTopOne :
      sourceIndex topMinusOne = topMinusTwo := by
    simp [sourceIndex]
  have hsourceNotTop :
      ∀ coordinate, coordinate ≠ topMinusOne →
        sourceIndex coordinate = coordinate := by
    intro coordinate hne
    simp [sourceIndex, hne]
  have hentryCallerLow : entry callerLow = caller := by
    simp [entry, hcallerLowMem]
  have hentryCallerHigh : entry callerHigh = caller := by
    simp [entry, hcallerHighMem]
  have hentryTopOne :
      entry topMinusOne =
        schedule.requested topMinusTwo := by
    simp [entry, htopOneNotCaller, hsourceTopOne]
  have hentryTopTwo :
      entry topMinusTwo =
        schedule.requested topMinusTwo := by
    have hne : topMinusTwo ≠ topMinusOne := by
      intro heq
      have hval := congrArg Fin.val heq
      dsimp only [topMinusTwo, topMinusOne] at hval
      omega
    simp [entry, htopTwoNotCaller, sourceIndex, hne]
  have hadjacent :
      ∀ level,
        ∀ hnext : level + 1 < schedule.scaleCount,
          ((⟨level, Nat.lt_of_succ_lt hnext⟩ ∈
                callerCoordinate ∧
              ⟨level + 1, hnext⟩ ∈ callerCoordinate) ∨
            (⟨level, Nat.lt_of_succ_lt hnext⟩ ∉
                  callerCoordinate ∧
              ⟨level + 1, hnext⟩ ∉ callerCoordinate ∧
              sourceIndex
                  ⟨level, Nat.lt_of_succ_lt hnext⟩ =
                sourceIndex ⟨level + 1, hnext⟩)) ∨
            2 * (entry
                  ⟨level, Nat.lt_of_succ_lt hnext⟩).1 ≤
              (entry ⟨level + 1, hnext⟩).1 := by
    intro level hnext
    let current : Fin schedule.scaleCount :=
      ⟨level, Nat.lt_of_succ_lt hnext⟩
    let next : Fin schedule.scaleCount :=
      ⟨level + 1, hnext⟩
    change
      ((current ∈ callerCoordinate ∧
          next ∈ callerCoordinate) ∨
        (current ∉ callerCoordinate ∧
          next ∉ callerCoordinate ∧
          sourceIndex current = sourceIndex next)) ∨
        2 * (entry current).1 ≤ (entry next).1
    have hcases :
        level = callerIndex - 2 ∨
        level = callerIndex - 1 ∨
        level = callerIndex ∨
        level = schedule.gridTopIndex - 2 ∨
        level = schedule.gridTopIndex - 1 ∨
        (level ≠ callerIndex - 2 ∧
          level ≠ callerIndex - 1 ∧
          level ≠ callerIndex ∧
          level ≠ schedule.gridTopIndex - 2 ∧
          level ≠ schedule.gridTopIndex - 1) := by
      omega
    rcases hcases with h | h | h | h | h | h
    · subst level
      right
      have hcurrentNotCaller :
          current ∉ callerCoordinate := by
        simp only [callerCoordinate, Finset.mem_insert,
          Finset.mem_singleton]
        rw [not_or]
        constructor <;> intro heq
        · have hval := congrArg Fin.val heq
          dsimp only [current, callerLow] at hval
          omega
        · have hval := congrArg Fin.val heq
          dsimp only [current, callerHigh] at hval
          omega
      have hcurrentNotTop : current ≠ topMinusOne := by
        intro heq
        have hval := congrArg Fin.val heq
        dsimp only [current, topMinusOne] at hval
        omega
      have hnextEq : next = callerLow := by
        apply Fin.ext
        dsimp only [next, callerLow]
        omega
      rw [hnextEq, hentryCallerLow]
      simpa [entry, hcurrentNotCaller, sourceIndex,
        hcurrentNotTop, current] using hbelow
    · subst level
      have hcurrentEq : current = callerLow := by
        apply Fin.ext
        rfl
      have hnextEq : next = callerHigh := by
        apply Fin.ext
        dsimp only [next, callerHigh]
        omega
      left
      left
      rw [hcurrentEq, hnextEq]
      exact ⟨hcallerLowMem, hcallerHighMem⟩
    · subst level
      right
      have hcurrentEq : current = callerHigh := by
        apply Fin.ext
        rfl
      have hnextNotCaller :
          next ∉ callerCoordinate := by
        simp only [callerCoordinate, Finset.mem_insert,
          Finset.mem_singleton]
        rw [not_or]
        constructor <;> intro heq
        · have hval := congrArg Fin.val heq
          dsimp only [next, callerLow] at hval
          omega
        · have hval := congrArg Fin.val heq
          dsimp only [next, callerHigh] at hval
          omega
      have hnextNotTop : next ≠ topMinusOne := by
        intro heq
        have hval := congrArg Fin.val heq
        dsimp only [next, topMinusOne] at hval
        omega
      rw [hcurrentEq, hentryCallerHigh]
      simpa [entry, hnextNotCaller, sourceIndex,
        hnextNotTop, next] using hcallerAbove
    · subst level
      have hcurrentEq : current = topMinusTwo := by
        apply Fin.ext
        rfl
      have hnextEq : next = topMinusOne := by
        apply Fin.ext
        dsimp only [next, topMinusOne]
        omega
      left
      right
      rw [hcurrentEq, hnextEq]
      exact
        ⟨htopTwoNotCaller, htopOneNotCaller,
          (hsourceNotTop topMinusTwo (by
            intro heq
            have hval := congrArg Fin.val heq
            dsimp only [topMinusTwo, topMinusOne] at hval
            omega)).trans hsourceTopOne.symm⟩
    · subst level
      right
      have hcurrentEq : current = topMinusOne := by
        apply Fin.ext
        rfl
      have hnextNotCaller :
          next ∉ callerCoordinate := by
        simp only [callerCoordinate, Finset.mem_insert,
          Finset.mem_singleton]
        rw [not_or]
        constructor <;> intro heq
        · have hval := congrArg Fin.val heq
          dsimp only [next, callerLow] at hval
          omega
        · have hval := congrArg Fin.val heq
          dsimp only [next, callerHigh] at hval
          omega
      have hnextNotTop : next ≠ topMinusOne := by
        intro heq
        have hval := congrArg Fin.val heq
        dsimp only [next, topMinusOne] at hval
        omega
      have htopValue :
          (schedule.requested next).1 = 1 := by
        rw [schedule.requested_value]
        apply min_eq_right
        have hnextVal : next.val = schedule.gridTopIndex := by
          dsimp only [next]
          omega
        rw [hnextVal]
        exact schedule.grid_top_reaches_one
      rw [hcurrentEq, hentryTopOne]
      simpa [entry, hnextNotCaller, sourceIndex,
        hnextNotTop, htopValue] using hbeforeTop
    · have hcurrentNotCaller :
          current ∉ callerCoordinate := by
        simp only [callerCoordinate, Finset.mem_insert,
          Finset.mem_singleton]
        rw [not_or]
        constructor <;> intro heq
        · exact h.2.1 (by
            have hval := congrArg Fin.val heq
            dsimp only [current, callerLow] at hval
            omega)
        · exact h.2.2.1 (by
            have hval := congrArg Fin.val heq
            dsimp only [current, callerHigh] at hval
            omega)
      have hnextNotCaller :
          next ∉ callerCoordinate := by
        simp only [callerCoordinate, Finset.mem_insert,
          Finset.mem_singleton]
        rw [not_or]
        constructor <;> intro heq
        · exact h.1 (by
            have hval := congrArg Fin.val heq
            dsimp only [next, callerLow] at hval
            omega)
        · exact h.2.1 (by
            have hval := congrArg Fin.val heq
            dsimp only [next, callerHigh] at hval
            omega)
      have hcurrentNotTop : current ≠ topMinusOne := by
        intro heq
        exact h.2.2.2.2 (by
          have hval := congrArg Fin.val heq
          dsimp only [current, topMinusOne] at hval
          omega)
      have hnextNotTop : next ≠ topMinusOne := by
        intro heq
        exact h.2.2.2.1 (by
          have hval := congrArg Fin.val heq
          dsimp only [next, topMinusOne] at hval
          omega)
      have hlevelNextBeforeTop :
          level + 1 < schedule.gridTopIndex := by
        rw [schedule.scaleCount_eq] at hnext
        have hnotLast := h.2.2.2.2
        omega
      have hgrid :=
        schedule.grid_adjacent_nested level hlevelNextBeforeTop
      right
      simpa [entry, hcurrentNotCaller, hnextNotCaller,
        sourceIndex, hcurrentNotTop, hnextNotTop] using hgrid
  let representative :
      Kakeya.Streamlined.AdmissibleScale delta →
        Fin schedule.scaleCount := fun requested =>
    let original := schedule.representative requested
    if original = callerLow then callerLow
    else if original = callerHigh then
      ⟨callerIndex + 1, by
        rw [schedule.scaleCount_eq]
        omega⟩
    else if original = topMinusOne then
      ⟨schedule.gridTopIndex, by
        rw [schedule.scaleCount_eq]
        omega⟩
    else original
  have hrepresentativeAboveCaller :
      ∀ requested,
        caller.1 ≤ requested.1 →
          callerLow.val ≤ (representative requested).val := by
    intro requested hcallerRequested
    let original := schedule.representative requested
    have horiginalLower :
        callerIndex ≤ original.val := by
      by_contra hnot
      have horiginalBefore :
          original.val <
            (schedule.representative caller).val := by
        rw [← hcallerIndex]
        omega
      have hgridBefore :
          (schedule.requested original).1 < caller.1 := by
        simpa [original] using
          schedule.requested_before_representative
            caller original.val horiginalBefore
      have hrequestedGrid :
          requested.1 ≤ (schedule.requested original).1 := by
        simpa [original] using
          schedule.requested_grid_le requested
      linarith
    by_cases hlow : original = callerLow
    · have hval := congrArg Fin.val hlow
      dsimp only [original, callerLow] at hval
      omega
    · by_cases hhigh : original = callerHigh
      · simp only [representative, original, if_neg hlow,
          if_pos hhigh]
        dsimp only [callerLow]
        omega
      · by_cases htop : original = topMinusOne
        · simp only [representative, original, if_neg hlow,
            if_neg hhigh, if_pos htop]
          dsimp only [callerLow]
          omega
        · simp only [representative, original, if_neg hlow,
            if_neg hhigh, if_neg htop]
          dsimp only [callerLow]
          omega
  have hrepresentativeBelowCaller :
      ∀ requested,
        ambientConstant * ENNReal.ofReal requested.1 ≤
            ENNReal.ofReal caller.1 →
          (representative requested).val ≤ callerLow.val := by
    intro requested hwindow
    let original := schedule.representative requested
    have hgridLtCaller :
        (schedule.requested original).1 < caller.1 := by
      have hgridWindow :
          ENNReal.ofReal (schedule.requested original).1 <
            ambientConstant * ENNReal.ofReal requested.1 := by
        simpa [original] using
          schedule.requested_grid_within_ambient requested
      have hENN :
          ENNReal.ofReal (schedule.requested original).1 <
            ENNReal.ofReal caller.1 :=
        hgridWindow.trans_le hwindow
      exact (ENNReal.ofReal_lt_ofReal_iff
        (hdelta.trans_le caller.2.1)).mp hENN
    have hcallerGrid :
        caller.1 ≤ (schedule.requested callerHigh).1 := by
      have h := schedule.requested_grid_le caller
      have hcallerRep :
          schedule.representative caller = callerHigh := by
        apply Fin.ext
        exact hcallerIndex.symm
      rwa [hcallerRep] at h
    have horiginalUpper :
        original.val < callerIndex := by
      by_contra hnot
      have hmono :
          (schedule.requested callerHigh).1 ≤
            (schedule.requested original).1 := by
        apply schedule.requested_mono
        dsimp only [callerHigh]
        omega
      linarith
    by_cases hlow : original = callerLow
    · simp only [representative, original, if_pos hlow]
      exact le_rfl
    · by_cases hhigh : original = callerHigh
      · have hval := congrArg Fin.val hhigh
        dsimp only [original, callerHigh] at hval
        omega
      · by_cases htop : original = topMinusOne
        · have hval := congrArg Fin.val htop
          dsimp only [original, topMinusOne] at hval
          omega
        · simp only [representative, original, if_neg hlow,
            if_neg hhigh, if_neg htop]
          dsimp only [callerLow]
          omega
  have hrequestedLe :
      ∀ requested,
        requested.1 ≤ (entry (representative requested)).1 := by
    intro requested
    let original := schedule.representative requested
    by_cases hlow : original = callerLow
    · have hbefore :
          (schedule.requested callerLow).1 < caller.1 := by
        have h := schedule.requested_before_representative
          caller (callerIndex - 1) (by
            change callerIndex - 1 <
              (schedule.representative caller).val
            rw [← hcallerIndex]
            omega)
        convert h using 1
      have hbase := schedule.requested_grid_le requested
      have hbase' :
          requested.1 ≤ (schedule.requested callerLow).1 := by
        change
          requested.1 ≤
            (schedule.requested
              (schedule.representative requested)).1 at hbase
        rw [show schedule.representative requested =
            callerLow by exact hlow] at hbase
        exact hbase
      have hentry :
          entry (representative requested) = caller := by
        simp [representative, original, hlow,
          entry, hcallerLowMem]
      rw [hentry]
      exact hbase'.trans hbefore.le
    · by_cases hhigh : original = callerHigh
      · let target : Fin schedule.scaleCount :=
          ⟨callerIndex + 1, by
            rw [schedule.scaleCount_eq]
            omega⟩
        have hbase := schedule.requested_grid_le requested
        have hmono :
            (schedule.requested original).1 ≤
              (schedule.requested target).1 := by
          apply schedule.requested_mono
          dsimp only [target]
          rw [hhigh]
          dsimp only [callerHigh]
          omega
        have hbase' := hbase.trans hmono
        have htargetNotCaller :
            target ∉ callerCoordinate := by
          simp only [callerCoordinate, Finset.mem_insert,
            Finset.mem_singleton]
          rw [not_or]
          constructor <;> intro heq
          · have hval := congrArg Fin.val heq
            dsimp only [target, callerLow] at hval
            omega
          · have hval := congrArg Fin.val heq
            dsimp only [target, callerHigh] at hval
            omega
        have htargetNotTop : target ≠ topMinusOne := by
          intro heq
          have hval := congrArg Fin.val heq
          dsimp only [target, topMinusOne] at hval
          omega
        have hentry :
            entry (representative requested) =
              schedule.requested target := by
          have hrep : representative requested = target := by
            simp only [representative, original, if_neg hlow,
              if_pos hhigh]
            exact rfl
          rw [hrep]
          simp [entry, htargetNotCaller, sourceIndex,
            htargetNotTop]
        rw [hentry]
        exact hbase'
      · by_cases htop : original = topMinusOne
        · have hbase : requested.1 ≤ 1 := requested.2.2
          let top : Fin schedule.scaleCount :=
            ⟨schedule.gridTopIndex, by
              rw [schedule.scaleCount_eq]
              omega⟩
          have htopNotCaller :
              top ∉ callerCoordinate := by
            simp only [callerCoordinate, Finset.mem_insert,
              Finset.mem_singleton]
            rw [not_or]
            constructor <;> intro heq
            · have hval := congrArg Fin.val heq
              dsimp only [top, callerLow] at hval
              omega
            · have hval := congrArg Fin.val heq
              dsimp only [top, callerHigh] at hval
              omega
          have htopNotTop : top ≠ topMinusOne := by
            intro heq
            have hval := congrArg Fin.val heq
            dsimp only [top, topMinusOne] at hval
            omega
          have htopEntry :
              entry top = schedule.requested top := by
            simp [entry, htopNotCaller, sourceIndex,
              htopNotTop]
          have htopValue :
              (schedule.requested top).1 = 1 := by
            rw [schedule.requested_value]
            exact min_eq_right schedule.grid_top_reaches_one
          have hrepresentative :
              representative requested = top := by
            simp only [representative, original, if_neg hlow,
              if_neg hhigh, if_pos htop]
            apply Fin.ext
            rfl
          rw [hrepresentative, htopEntry, htopValue]
          exact hbase
        · have hbase := schedule.requested_grid_le requested
          have horiginalNotCaller :
              original ∉ callerCoordinate := by
            simp only [callerCoordinate, Finset.mem_insert,
              Finset.mem_singleton]
            rw [not_or]
            exact ⟨hlow, hhigh⟩
          have hsourceOriginal :
              sourceIndex original = original :=
            hsourceNotTop original htop
          have hrepresentative :
              representative requested = original := by
            simp [representative, original, hlow, hhigh, htop]
          rw [hrepresentative]
          simp [entry, horiginalNotCaller, hsourceOriginal]
          exact hbase
  have hwithin :
      ∀ requested,
        ENNReal.ofReal (entry (representative requested)).1 <
          outputConstant * ENNReal.ofReal requested.1 := by
    intro requested
    let original := schedule.representative requested
    have hC2toOutput :
        ambientConstant ^ 2 ≤ outputConstant := by
      calc
        ambientConstant ^ 2 ≤ ambientConstant ^ 3 :=
          pow_le_pow_right₀ hambientOne (by omega)
        _ ≤ outputConstant := houtput
    have hCtoOutput :
        ambientConstant ≤ outputConstant := by
      calc
        ambientConstant ≤ ambientConstant ^ 2 :=
          calc
            ambientConstant = ambientConstant * 1 := by simp
            _ ≤ ambientConstant * ambientConstant := by
              gcongr
            _ = ambientConstant ^ 2 := by rw [pow_two]
        _ ≤ outputConstant := hC2toOutput
    by_cases hlow : original = callerLow
    · have hcallerLe :
          ENNReal.ofReal caller.1 ≤
            ambientConstant *
              ENNReal.ofReal
                (schedule.requested callerLow).1 := by
        have hnext := schedule.grid_next_le (callerIndex - 1)
          (by omega)
        have hcallerGrid : caller.1 ≤
            (schedule.requested callerHigh).1 := by
          have h := schedule.requested_grid_le caller
          have hcallerRep :
              schedule.representative caller = callerHigh := by
            apply Fin.ext
            exact hcallerIndex.symm
          rwa [hcallerRep] at h
        have hcallerOfReal :
            ENNReal.ofReal caller.1 ≤
              ENNReal.ofReal
                (schedule.requested callerHigh).1 :=
          ENNReal.ofReal_mono hcallerGrid
        have hnext' :
            ENNReal.ofReal
                (schedule.requested callerHigh).1 ≤
              ambientConstant *
                ENNReal.ofReal
                  (schedule.requested callerLow).1 := by
          have hlowEq :
              ⟨callerIndex - 1, by
                rw [schedule.scaleCount_eq]
                omega⟩ = callerLow := by
            apply Fin.ext
            rfl
          have hhighEq :
              ⟨callerIndex - 1 + 1, by
                rw [schedule.scaleCount_eq]
                omega⟩ = callerHigh := by
            apply Fin.ext
            dsimp only [callerHigh]
            exact Nat.sub_add_cancel (by omega)
          simpa [hlowEq, hhighEq] using hnext
        exact hcallerOfReal.trans hnext'
      have hwindow :=
        schedule.requested_grid_within_ambient requested
      have hwindow' :
          ENNReal.ofReal (schedule.requested original).1 <
            ambientConstant * ENNReal.ofReal requested.1 := by
        change
          ENNReal.ofReal
              (schedule.requested
                (schedule.representative requested)).1 <
            ambientConstant * ENNReal.ofReal requested.1 at hwindow
        exact hwindow
      have hentry :
          entry (representative requested) = caller := by
        simp [representative, original, hlow,
          entry, hcallerLowMem]
      calc
        ENNReal.ofReal
            (entry (representative requested)).1 =
            ENNReal.ofReal caller.1 := by rw [hentry]
        _ ≤ ambientConstant *
            ENNReal.ofReal
              (schedule.requested callerLow).1 := hcallerLe
        _ < ambientConstant ^ 2 *
            ENNReal.ofReal requested.1 := by
          have hstrict :=
            ENNReal.mul_lt_mul_right
              (show ambientConstant ≠ 0 by
                exact ne_of_gt (zero_lt_one.trans_le hambientOne))
              hambientTop (by
                rw [hlow] at hwindow'
                exact hwindow')
          simpa [pow_two, mul_assoc] using hstrict
        _ ≤ outputConstant *
            ENNReal.ofReal requested.1 := by
          gcongr
    · by_cases hhigh : original = callerHigh
      · let target : Fin schedule.scaleCount :=
          ⟨callerIndex + 1, by
            rw [schedule.scaleCount_eq]
            omega⟩
        have hstep :=
          schedule.grid_next_le callerIndex (by omega)
        have hwindow :=
          schedule.requested_grid_within_ambient requested
        have hwindow' :
            ENNReal.ofReal (schedule.requested original).1 <
              ambientConstant * ENNReal.ofReal requested.1 := by
          exact hwindow
        have hrep : representative requested = target := by
          simp only [representative, original, if_neg hlow,
            if_pos hhigh]
          rfl
        have htargetNotCaller :
            target ∉ callerCoordinate := by
          simp only [callerCoordinate, Finset.mem_insert,
            Finset.mem_singleton]
          rw [not_or]
          constructor <;> intro heq
          · have hval := congrArg Fin.val heq
            dsimp only [target, callerLow] at hval
            omega
          · have hval := congrArg Fin.val heq
            dsimp only [target, callerHigh] at hval
            omega
        have htargetNotTop : target ≠ topMinusOne := by
          intro heq
          have hval := congrArg Fin.val heq
          dsimp only [target, topMinusOne] at hval
          omega
        have hentryTarget :
            entry target = schedule.requested target := by
          simp [entry, htargetNotCaller, sourceIndex,
            htargetNotTop]
        calc
          ENNReal.ofReal
              (entry (representative requested)).1 =
              ENNReal.ofReal
                (schedule.requested target).1 := by
            rw [hrep, hentryTarget]
          _ ≤ ambientConstant *
              ENNReal.ofReal
                (schedule.requested original).1 := by
            rw [hhigh]
            convert hstep using 1
          _ < ambientConstant ^ 2 *
              ENNReal.ofReal requested.1 := by
            have hstrict :=
              ENNReal.mul_lt_mul_right
                (show ambientConstant ≠ 0 by
                  exact ne_of_gt (zero_lt_one.trans_le hambientOne))
                hambientTop hwindow'
            simpa [pow_two, mul_assoc] using hstrict
          _ ≤ outputConstant *
              ENNReal.ofReal requested.1 := by
            gcongr
      · by_cases htop : original = topMinusOne
        · let top : Fin schedule.scaleCount :=
            ⟨schedule.gridTopIndex, by
              rw [schedule.scaleCount_eq]
              omega⟩
          have hstep :=
            schedule.grid_next_le
              (schedule.gridTopIndex - 1) (by omega)
          have hwindow :=
            schedule.requested_grid_within_ambient requested
          have hwindow' :
              ENNReal.ofReal (schedule.requested original).1 <
                ambientConstant * ENNReal.ofReal requested.1 := by
            exact hwindow
          have hrep : representative requested = top := by
            simp only [representative, original, if_neg hlow,
              if_neg hhigh, if_pos htop]
            rfl
          have htopNotCaller :
              top ∉ callerCoordinate := by
            simp only [callerCoordinate, Finset.mem_insert,
              Finset.mem_singleton]
            rw [not_or]
            constructor <;> intro heq
            · have hval := congrArg Fin.val heq
              dsimp only [top, callerLow] at hval
              omega
            · have hval := congrArg Fin.val heq
              dsimp only [top, callerHigh] at hval
              omega
          have htopNotTop : top ≠ topMinusOne := by
            intro heq
            have hval := congrArg Fin.val heq
            dsimp only [top, topMinusOne] at hval
            omega
          have hentryTop :
              entry top = schedule.requested top := by
            simp [entry, htopNotCaller, sourceIndex,
              htopNotTop]
          calc
            ENNReal.ofReal
                (entry (representative requested)).1 =
                ENNReal.ofReal
                  (schedule.requested top).1 := by
              rw [hrep, hentryTop]
            _ ≤ ambientConstant *
                ENNReal.ofReal
                  (schedule.requested original).1 := by
              rw [htop]
              have htopEq :
                  ⟨schedule.gridTopIndex - 1 + 1, by
                    rw [schedule.scaleCount_eq]
                    omega⟩ = top := by
                apply Fin.ext
                dsimp only [top]
                omega
              have hprevEq :
                  ⟨schedule.gridTopIndex - 1, by
                    rw [schedule.scaleCount_eq]
                    omega⟩ = topMinusOne := by
                apply Fin.ext
                rfl
              simpa [htopEq, hprevEq] using hstep
            _ < ambientConstant ^ 2 *
                ENNReal.ofReal requested.1 := by
              have hstrict :=
                ENNReal.mul_lt_mul_right
                  (show ambientConstant ≠ 0 by
                    exact ne_of_gt (zero_lt_one.trans_le hambientOne))
                  hambientTop hwindow'
              simpa [pow_two, mul_assoc] using hstrict
            _ ≤ outputConstant *
                ENNReal.ofReal requested.1 := by
              gcongr
        · have hwindow :=
            schedule.requested_grid_within_ambient requested
          have hwindow' :
              ENNReal.ofReal (schedule.requested original).1 <
                ambientConstant * ENNReal.ofReal requested.1 := by
            exact hwindow
          calc
            ENNReal.ofReal
                (entry (representative requested)).1 =
                ENNReal.ofReal
                  (schedule.requested original).1 := by
              simp [representative, original, hlow, hhigh,
                htop, entry, callerCoordinate, sourceIndex,
                topMinusOne]
            _ < ambientConstant *
                ENNReal.ofReal requested.1 := hwindow'
            _ ≤ outputConstant *
                ENNReal.ofReal requested.1 := by
              gcongr
  have hcallerRepresentativeNested :
      2 * caller.1 ≤
        (entry (representative caller)).1 := by
    let original := schedule.representative caller
    have hhigh : original = callerHigh := by
      apply Fin.ext
      dsimp only [original, callerHigh]
      exact hcallerIndex.symm
    have hlow : original ≠ callerLow := by
      intro heq
      have hval := congrArg Fin.val heq
      dsimp only [original, callerLow] at hval
      rw [hcallerIndex] at hval
      omega
    let target : Fin schedule.scaleCount :=
      ⟨callerIndex + 1, by
        rw [schedule.scaleCount_eq]
        omega⟩
    have hrep : representative caller = target := by
      dsimp only [representative]
      rw [if_neg hlow, if_pos hhigh]
    have htargetNotCaller :
        target ∉ callerCoordinate := by
      simp only [callerCoordinate, Finset.mem_insert,
        Finset.mem_singleton]
      rw [not_or]
      constructor <;> intro heq
      · have hval := congrArg Fin.val heq
        dsimp only [target, callerLow] at hval
        omega
      · have hval := congrArg Fin.val heq
        dsimp only [target, callerHigh] at hval
        omega
    have htargetNotTop : target ≠ topMinusOne := by
      intro heq
      have hval := congrArg Fin.val heq
      dsimp only [target, topMinusOne] at hval
      omega
    rw [hrep]
    simpa [entry, htargetNotCaller, sourceIndex,
      htargetNotTop, target] using hcallerAbove
  have hentryMono :
      ∀ first second : Fin schedule.scaleCount,
        first.1 ≤ second.1 →
          (entry first).1 ≤ (entry second).1 := by
    have adjacent :
        ∀ level,
          ∀ hnext : level + 1 < schedule.scaleCount,
            (entry
                ⟨level, Nat.lt_of_succ_lt hnext⟩).1 ≤
              (entry ⟨level + 1, hnext⟩).1 := by
      intro level hnext
      let current : Fin schedule.scaleCount :=
        ⟨level, Nat.lt_of_succ_lt hnext⟩
      let next : Fin schedule.scaleCount :=
        ⟨level + 1, hnext⟩
      have edge := hadjacent level hnext
      rcases edge with same | separated
      · rcases same with bothCaller | sameSource
        · have currentEntry : entry current = caller := by
            simp [entry, current, bothCaller.1]
          have nextEntry : entry next = caller := by
            simp [entry, next, bothCaller.2]
          rw [currentEntry, nextEntry]
        · have currentEntry :
              entry current =
                schedule.requested (sourceIndex current) := by
            simp [entry, current, sameSource.1]
          have nextEntry :
              entry next =
                schedule.requested (sourceIndex next) := by
            simp [entry, next, sameSource.2.1]
          rw [currentEntry, nextEntry, sameSource.2.2]
      · have separated' :
            2 * (entry current).1 ≤ (entry next).1 := by
          simpa only [current, next] using separated
        have currentPos : 0 < (entry current).1 :=
          hdelta.trans_le (entry current).2.1
        linarith
    have scaleCountNe : schedule.scaleCount ≠ 0 :=
      Nat.ne_of_gt schedule.scaleCount_pos
    obtain ⟨count, hcount⟩ :=
      Nat.exists_eq_succ_of_ne_zero scaleCountNe
    let castEntry : Fin (count + 1) → ℝ :=
      fun coordinate =>
        (entry (Fin.cast hcount.symm coordinate)).1
    have castMonotone : Monotone castEntry := by
      apply Fin.monotone_iff_le_succ.mpr
      intro coordinate
      have hnext :
          coordinate.val + 1 < schedule.scaleCount := by
        rw [hcount]
        omega
      have currentEq :
          Fin.cast hcount.symm coordinate.castSucc =
            (⟨coordinate.val, Nat.lt_of_succ_lt hnext⟩ :
              Fin schedule.scaleCount) := by
        apply Fin.ext
        rfl
      have nextEq :
          Fin.cast hcount.symm coordinate.succ =
            (⟨coordinate.val + 1, hnext⟩ :
              Fin schedule.scaleCount) := by
        apply Fin.ext
        rfl
      simpa only [castEntry, currentEq, nextEq] using
        adjacent coordinate.val hnext
    intro first second firstLeSecond
    have castLe :
        Fin.cast hcount first ≤ Fin.cast hcount second := by
      simpa only [Fin.le_def, Fin.coe_cast] using firstLeSecond
    have result :=
      castMonotone castLe
    simpa [castEntry] using result
  exact
    ⟨{
      sourceIndex := sourceIndex
      callerCoordinate := callerCoordinate
      entry := entry
      entry_eq := by
        intro coordinate
        rfl
      callerLevel := callerLow
      caller_level_mem := hcallerLowMem
      caller_level_scale := hentryCallerLow
      adjacent_same_source_or_le := hadjacent
      entry_mono := hentryMono
      representative := representative
      caller_representative_nested :=
        hcallerRepresentativeNested
      representative_above_caller := hrepresentativeAboveCaller
      representative_below_caller := hrepresentativeBelowCaller
      requested_le := hrequestedLe
      within_output := hwithin
    }⟩

end Kakeya.Assouad

end
