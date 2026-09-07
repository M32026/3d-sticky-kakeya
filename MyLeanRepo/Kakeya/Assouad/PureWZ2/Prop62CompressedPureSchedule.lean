import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62TreePureSchedule

/-!
# Proposition 6.2: compress the old schedule around the metric level

The metric-parent proof keeps the old levels above `rho` and the old levels
from the selected `s`-coordinate downward.  Old levels strictly between them
are replaced by the inserted metric level.  This module removes that middle
interval while retaining the exact old scale witnesses and laminar parent
maps.

The finite rounding statement is supplied separately.  Its proof is the
numerical lower-or-top routing argument using `rho / (K₀ C*) ≤ s ≤ rho / K₀`;
it is not part of this purely combinatorial compression.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

namespace PureWZ2Prop62PureSchedule

variable
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    (schedule :
      PureWZ2Prop62PureSchedule
        fine ambientConstant scaleWindow)

/-- Number of retained old coordinates after removing `(upper, packet)`. -/
def compressedLevelCount
    (upper packet : Fin schedule.levelCount) : ℕ :=
  upper.1 + 1 + (schedule.levelCount - packet.1)

theorem compressedLevelCount_pos
    (upper packet : Fin schedule.levelCount) :
    0 < schedule.compressedLevelCount upper packet := by
  unfold compressedLevelCount
  omega

/-- Embed one compressed coordinate back into the simultaneous old schedule. -/
def compressedAmbientCoordinate
    (upper packet : Fin schedule.levelCount)
    (upperBeforePacket : upper.1 < packet.1)
    (coordinate :
      Fin (schedule.compressedLevelCount upper packet)) :
    Fin schedule.levelCount :=
  if hprefix : coordinate.1 < upper.1 + 1 then
    ⟨coordinate.1, hprefix.trans <| by omega⟩
  else
    ⟨packet.1 + (coordinate.1 - (upper.1 + 1)), by
      have coordinateBound := coordinate.2
      have packetCancel :
          schedule.levelCount - packet.1 + packet.1 =
            schedule.levelCount :=
        Nat.sub_add_cancel (Nat.le_of_lt packet.2)
      unfold compressedLevelCount at coordinateBound
      omega⟩

@[simp] theorem compressedAmbientCoordinate_of_lt
    (upper packet : Fin schedule.levelCount)
    (upperBeforePacket : upper.1 < packet.1)
    (coordinate :
      Fin (schedule.compressedLevelCount upper packet))
    (hprefix : coordinate.1 < upper.1 + 1) :
    (schedule.compressedAmbientCoordinate
      upper packet upperBeforePacket coordinate).1 =
        coordinate.1 := by
  simp [compressedAmbientCoordinate, hprefix]

@[simp] theorem compressedAmbientCoordinate_of_not_lt
    (upper packet : Fin schedule.levelCount)
    (upperBeforePacket : upper.1 < packet.1)
    (coordinate :
      Fin (schedule.compressedLevelCount upper packet))
    (suffix : ¬coordinate.1 < upper.1 + 1) :
    (schedule.compressedAmbientCoordinate
      upper packet upperBeforePacket coordinate).1 =
        packet.1 + (coordinate.1 - (upper.1 + 1)) := by
  simp [compressedAmbientCoordinate, suffix]

theorem compressedAmbientCoordinate_strictMono
    (upper packet : Fin schedule.levelCount)
    (upperBeforePacket : upper.1 < packet.1)
    {first second :
      Fin (schedule.compressedLevelCount upper packet)}
    (firstBeforeSecond : first.1 < second.1) :
    (schedule.compressedAmbientCoordinate
        upper packet upperBeforePacket first).1 <
      (schedule.compressedAmbientCoordinate
        upper packet upperBeforePacket second).1 := by
  by_cases firstPrefix : first.1 < upper.1 + 1
  · by_cases secondPrefix : second.1 < upper.1 + 1
    · rw [
        schedule.compressedAmbientCoordinate_of_lt
          upper packet upperBeforePacket first firstPrefix,
        schedule.compressedAmbientCoordinate_of_lt
          upper packet upperBeforePacket second secondPrefix
      ]
      exact firstBeforeSecond
    · rw [
        schedule.compressedAmbientCoordinate_of_lt
          upper packet upperBeforePacket first firstPrefix,
        schedule.compressedAmbientCoordinate_of_not_lt
          upper packet upperBeforePacket second secondPrefix
      ]
      omega
  · have secondSuffix : ¬second.1 < upper.1 + 1 := by
      omega
    rw [
      schedule.compressedAmbientCoordinate_of_not_lt
        upper packet upperBeforePacket first firstPrefix,
      schedule.compressedAmbientCoordinate_of_not_lt
        upper packet upperBeforePacket second secondSuffix
    ]
    omega

theorem compressedAmbientCoordinate_upper
    (upper packet : Fin schedule.levelCount)
    (upperBeforePacket : upper.1 < packet.1) :
    schedule.compressedAmbientCoordinate
        upper packet upperBeforePacket
        ⟨upper.1, by
          unfold compressedLevelCount
          omega⟩ =
      upper := by
  apply Fin.ext
  simp [compressedAmbientCoordinate]

theorem compressedAmbientCoordinate_packet
    (upper packet : Fin schedule.levelCount)
    (upperBeforePacket : upper.1 < packet.1) :
    schedule.compressedAmbientCoordinate
        upper packet upperBeforePacket
        ⟨upper.1 + 1, by
          unfold compressedLevelCount
          have packetRemaining :
              0 < schedule.levelCount - packet.1 :=
            Nat.sub_pos_of_lt packet.2
          omega⟩ =
      packet := by
  apply Fin.ext
  simp [compressedAmbientCoordinate]

/-- Canonical upper coordinate in the compressed schedule. -/
def compressedUpperCoordinate
    (upper packet : Fin schedule.levelCount) :
    Fin (schedule.compressedLevelCount upper packet) :=
  ⟨upper.1, by
    unfold compressedLevelCount
    omega⟩

/-- Canonical packet coordinate immediately after the retained upper prefix. -/
def compressedPacketCoordinate
    (upper packet : Fin schedule.levelCount) :
    Fin (schedule.compressedLevelCount upper packet) :=
  ⟨upper.1 + 1, by
    unfold compressedLevelCount
    have packetRemaining :
        0 < schedule.levelCount - packet.1 :=
      Nat.sub_pos_of_lt packet.2
    omega⟩

theorem compressedAmbientCoordinate_upper_eq
    (upper packet : Fin schedule.levelCount)
    (upperBeforePacket : upper.1 < packet.1) :
    schedule.compressedAmbientCoordinate
        upper packet upperBeforePacket
        (schedule.compressedUpperCoordinate upper packet) =
      upper :=
  schedule.compressedAmbientCoordinate_upper
    upper packet upperBeforePacket

theorem compressedAmbientCoordinate_packet_eq
    (upper packet : Fin schedule.levelCount)
    (upperBeforePacket : upper.1 < packet.1) :
    schedule.compressedAmbientCoordinate
        upper packet upperBeforePacket
        (schedule.compressedPacketCoordinate upper packet) =
      packet :=
  schedule.compressedAmbientCoordinate_packet
    upper packet upperBeforePacket

/--
Compress the old pure schedule after the numerical rounding route for the
retained coordinates has been verified.
-/
noncomputable def compress
    (upper packet : Fin schedule.levelCount)
    (upperBeforePacket : upper.1 < packet.1)
    (outputWindow : ENNReal)
    (outputWindowFinite :
      WZ2PaperFiniteErrorConstant outputWindow)
    (rounding :
      ∀ requested : WZ2PaperRequestedScale delta,
        ∃ coordinate :
            Fin (schedule.compressedLevelCount upper packet),
          requested.1 ≤
              schedule.actualScale
                (schedule.compressedAmbientCoordinate
                  upper packet upperBeforePacket coordinate) ∧
            ENNReal.ofReal
                (schedule.actualScale
                  (schedule.compressedAmbientCoordinate
                    upper packet upperBeforePacket coordinate)) <
              outputWindow * ENNReal.ofReal requested.1) :
    PureWZ2Prop62PureSchedule
      fine ambientConstant outputWindow where
  ambient_finite := schedule.ambient_finite
  scaleWindow_finite := outputWindowFinite
  fine_distinct := schedule.fine_distinct
  levelCount := schedule.compressedLevelCount upper packet
  levelCount_pos := schedule.compressedLevelCount_pos upper packet
  actualScale := fun coordinate =>
    schedule.actualScale
      (schedule.compressedAmbientCoordinate
        upper packet upperBeforePacket coordinate)
  delta_le_actualScale := fun coordinate =>
    schedule.delta_le_actualScale
      (schedule.compressedAmbientCoordinate
        upper packet upperBeforePacket coordinate)
  actualScale_antitone := by
    intro first second firstLeSecond
    have ambientLe :
        (schedule.compressedAmbientCoordinate
            upper packet upperBeforePacket first).val ≤
          (schedule.compressedAmbientCoordinate
            upper packet upperBeforePacket second).val := by
      rcases firstLeSecond.eq_or_lt with firstEq | firstLt
      · have coordinateEq : first = second := Fin.ext firstEq
        rw [coordinateEq]
      · exact
          (schedule.compressedAmbientCoordinate_strictMono
            upper packet upperBeforePacket firstLt).le
    exact schedule.actualScale_antitone _ _ ambientLe
  scaleData := fun coordinate =>
    schedule.scaleData
      (schedule.compressedAmbientCoordinate
        upper packet upperBeforePacket coordinate)
  coarse_line_class := fun coordinate =>
    schedule.coarse_line_class
      (schedule.compressedAmbientCoordinate
        upper packet upperBeforePacket coordinate)
  parent_covers := fun coordinate =>
    schedule.parent_covers
      (schedule.compressedAmbientCoordinate
        upper packet upperBeforePacket coordinate)
  parent_nested := by
    intro level hnext first second nextParentEq
    let current :
        Fin (schedule.compressedLevelCount upper packet) :=
      ⟨level, Nat.lt_of_succ_lt hnext⟩
    let next :
        Fin (schedule.compressedLevelCount upper packet) :=
      ⟨level + 1, hnext⟩
    have currentNext : current.1 < next.1 := by
      dsimp only [current, next]
      omega
    have ambientLe :
        (schedule.compressedAmbientCoordinate
            upper packet upperBeforePacket current).1 ≤
          (schedule.compressedAmbientCoordinate
            upper packet upperBeforePacket next).1 :=
      (schedule.compressedAmbientCoordinate_strictMono
        upper packet upperBeforePacket
        (first := current) (second := next) currentNext).le
    exact
      schedule.parent_eq_of_coordinate_le
        (schedule.compressedAmbientCoordinate
          upper packet upperBeforePacket current)
        (schedule.compressedAmbientCoordinate
          upper packet upperBeforePacket next)
        ambientLe first second nextParentEq
  rounding := rounding

@[simp] theorem compress_actualScale_upper
    (upper packet : Fin schedule.levelCount)
    (upperBeforePacket : upper.1 < packet.1)
    (outputWindow : ENNReal)
    (outputWindowFinite :
      WZ2PaperFiniteErrorConstant outputWindow)
    (rounding :
      ∀ requested : WZ2PaperRequestedScale delta,
        ∃ coordinate :
            Fin (schedule.compressedLevelCount upper packet),
          requested.1 ≤
              schedule.actualScale
                (schedule.compressedAmbientCoordinate
                  upper packet upperBeforePacket coordinate) ∧
            ENNReal.ofReal
                (schedule.actualScale
                  (schedule.compressedAmbientCoordinate
                    upper packet upperBeforePacket coordinate)) <
              outputWindow * ENNReal.ofReal requested.1) :
    (schedule.compress upper packet upperBeforePacket
      outputWindow outputWindowFinite rounding).actualScale
        (schedule.compressedUpperCoordinate upper packet) =
      schedule.actualScale upper := by
  simp [compress, schedule.compressedAmbientCoordinate_upper_eq]

@[simp] theorem compress_actualScale_packet
    (upper packet : Fin schedule.levelCount)
    (upperBeforePacket : upper.1 < packet.1)
    (outputWindow : ENNReal)
    (outputWindowFinite :
      WZ2PaperFiniteErrorConstant outputWindow)
    (rounding :
      ∀ requested : WZ2PaperRequestedScale delta,
        ∃ coordinate :
            Fin (schedule.compressedLevelCount upper packet),
          requested.1 ≤
              schedule.actualScale
                (schedule.compressedAmbientCoordinate
                  upper packet upperBeforePacket coordinate) ∧
            ENNReal.ofReal
                (schedule.actualScale
                  (schedule.compressedAmbientCoordinate
                    upper packet upperBeforePacket coordinate)) <
              outputWindow * ENNReal.ofReal requested.1) :
    (schedule.compress upper packet upperBeforePacket
      outputWindow outputWindowFinite rounding).actualScale
        (schedule.compressedPacketCoordinate upper packet) =
      schedule.actualScale packet := by
  simp [compress, schedule.compressedAmbientCoordinate_packet_eq]

end PureWZ2Prop62PureSchedule

end Kakeya.Assouad

end
