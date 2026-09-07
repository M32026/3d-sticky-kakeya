import MyLeanRepo.Kakeya.Assouad.PropStickyFiniteNearbyScheduleStatements

/-!
# Caller-rooted nested exact-cover schedule

This is the finite form of the tree used in the proof of
`multiScaleWolffLem`.  Every level is the full-fiber partition of one strict
exact-scale cover, adjacent levels are nested, and the caller's exact cover
appears as one literal level of the same tree.

The representative fields recover Assouad Definition 2.12:

> “for every `rho_0 ∈ [delta,1]`, there exists
> `rho ∈ [rho_0, C rho_0)` ...”

No source tubes are selected in this structure.
-/

noncomputable section

namespace Kakeya.Assouad

structure WZ2PaperCallerRootedNestedScheduleData
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (ambientConstant outputConstant : ENNReal)
    (caller : Kakeya.Streamlined.AdmissibleScale delta)
    (callerAmbient :
      WZ2PaperScaleCoverData family caller ambientConstant) where
  scaleCount : ℕ
  scaleCount_pos : 0 < scaleCount
  entry :
    Fin scaleCount →
      Σ scale : Kakeya.Streamlined.AdmissibleScale delta,
        WZ2PaperScaleCoverData family scale ambientConstant
  scale_antitone :
    ∀ first second : Fin scaleCount,
      first.val ≤ second.val →
        (entry second).1.1 ≤ (entry first).1.1
  parent_nested :
    ∀ level,
      ∀ hnext : level + 1 < scaleCount,
        ∀ first second : Fin family.card,
          (entry ⟨level + 1, hnext⟩).2.cover.parent first =
              (entry ⟨level + 1, hnext⟩).2.cover.parent second →
            (entry
                ⟨level, Nat.lt_of_succ_lt hnext⟩).2.cover.parent first =
              (entry
                ⟨level, Nat.lt_of_succ_lt hnext⟩).2.cover.parent second
  callerLevel : Fin scaleCount
  caller_entry_eq :
    HEq (entry callerLevel) (⟨caller, callerAmbient⟩ :
      Σ scale : Kakeya.Streamlined.AdmissibleScale delta,
        WZ2PaperScaleCoverData family scale ambientConstant)
  representative :
    Kakeya.Streamlined.AdmissibleScale delta →
      Fin scaleCount
  caller_representative_nested :
    2 * caller.1 ≤
      (entry (representative caller)).1.1
  representative_coarse_of_caller_le :
    ∀ requested,
      caller.1 ≤ requested.1 →
        (representative requested).val ≤ callerLevel.val
  representative_fine_of_ambient_le_caller :
    ∀ requested,
      ambientConstant * ENNReal.ofReal requested.1 ≤
          ENNReal.ofReal caller.1 →
        callerLevel.val ≤ (representative requested).val
  requested_le :
    ∀ requested,
      requested.1 ≤
        (entry (representative requested)).1.1
  within_output :
    ∀ requested,
      ENNReal.ofReal
          (entry (representative requested)).1.1 <
        outputConstant * ENNReal.ofReal requested.1

namespace WZ2PaperCallerRootedNestedScheduleData

def scale
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant outputConstant : ENNReal}
    {caller : Kakeya.Streamlined.AdmissibleScale delta}
    {callerAmbient :
      WZ2PaperScaleCoverData family caller ambientConstant}
    (data :
      WZ2PaperCallerRootedNestedScheduleData
        ambientConstant outputConstant caller callerAmbient)
    (coordinate : Fin data.scaleCount) :
    Kakeya.Streamlined.AdmissibleScale delta :=
  (data.entry coordinate).1

def scaleData
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant outputConstant : ENNReal}
    {caller : Kakeya.Streamlined.AdmissibleScale delta}
    {callerAmbient :
      WZ2PaperScaleCoverData family caller ambientConstant}
    (data :
      WZ2PaperCallerRootedNestedScheduleData
        ambientConstant outputConstant caller callerAmbient)
    (coordinate : Fin data.scaleCount) :
    WZ2PaperScaleCoverData
      family (data.scale coordinate) ambientConstant :=
  (data.entry coordinate).2

end WZ2PaperCallerRootedNestedScheduleData

/--
Choose a caller-rooted nested schedule from the exact-scale GWZ source.

The input loss is separated from the output loss by a factor four.  A
geometric grid with ratio `delta^(-inputLoss)` may skip the two grid points
adjacent to the caller and the final point adjacent to scale one; the factor
four absorbs those skips in the nearby-scale window.
-/
def WZ2PropStickyCallerRootedNestedScheduleStatement : Prop :=
  ∀ {delta : ℝ},
    ∀ {family : Kakeya.Streamlined.TubeFamily delta},
      ∀ {ambientConstant outputConstant : ENNReal},
        ∀ {levelCount : ℕ},
          ∀ (schedule :
              WZ2PaperFiniteNearbyScheduleData
                (family := family)
                ambientConstant outputConstant levelCount),
            ∀ (strictAmbient :
                ∀ coordinate,
                  WZ2PaperScaleCoverData
                    family (schedule.requested coordinate)
                      ambientConstant),
            ∀ (caller :
                Kakeya.Streamlined.AdmissibleScale delta),
              ∀ (callerAmbient :
                  WZ2PaperScaleCoverData
                    family caller ambientConstant),
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
                        WZ2PaperCallerRootedNestedScheduleData
                          ambientConstant outputConstant
                          caller callerAmbient,
                      data.scaleCount = schedule.scaleCount

end Kakeya.Assouad

end
