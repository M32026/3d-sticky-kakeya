import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.DirectHalfOffsetTerminalAssembly
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.LocalizedOrdinaryDistinctnessToLineDistance
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.SameCarrierGrainRetype

/-!
# Canonically centered representatives for the actual half-offset terminal

The terminal construction already fixes its exact and cubical carrier sets.
This module only changes the ordinary representatives of their supporting
lines: every tube is replaced by `pureWZ2PaperCenteredTube`, while every
carrier is retained literally.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Metric Set

namespace PureWZ2DirectCommonYSourceAssembly

variable
    {logExponent : ℕ}
    {sigma epsilon delta : ℝ}
    (commonSource : PureWZ2DirectCommonYSourceAssembly
      logExponent sigma epsilon delta)

namespace TerminalGeometry

/-- The canonical midpoint-centered representatives of the actual terminal
family. -/
abbrev centeredFamily (terminal : commonSource.TerminalGeometry) :
    Kakeya.Streamlined.TubeFamily terminal.targetDelta where
  card := terminal.family.card
  tube index := pureWZ2PaperCenteredTube (terminal.family.tube index)

@[simp] theorem centeredFamily_tube (terminal : commonSource.TerminalGeometry)
    (index : Fin terminal.family.card) :
    (terminal.centeredFamily).tube index =
      pureWZ2PaperCenteredTube (terminal.family.tube index) := rfl

theorem centeredFamily_line_class (terminal : commonSource.TerminalGeometry) :
    WZ1PaperIsLineClass terminal.centeredFamily := by
  intro index
  exact pureWZ2PaperCenteredTube_lineClass
    (TerminalGeometry.line_class commonSource terminal index)

/-- Retype the terminal exact shading without changing a single carrier set. -/
def centeredExactShading (terminal : commonSource.TerminalGeometry) :
    WZ1PaperTubeShading terminal.centeredFamily where
  carrier index := terminal.exactShading.carrier index
  measurable_carrier index := terminal.exactShading.measurable_carrier index
  subset_body index := by
    change terminal.exactShading.carrier index ⊆
      wz1PaperTubeCarrier
        (pureWZ2PaperCenteredTube (terminal.family.tube index))
    rw [pureWZ2PaperCenteredTube_paperCarrier]
    exact terminal.exactShading.subset_body index

/-- Retype the terminal cubical shading without changing a single carrier set. -/
def centeredCubicalShading (terminal : commonSource.TerminalGeometry) :
    WZ1PaperTubeShading terminal.centeredFamily where
  carrier index := terminal.cubicalShading.carrier index
  measurable_carrier index := terminal.cubicalShading.measurable_carrier index
  subset_body index := by
    change terminal.cubicalShading.carrier index ⊆
      wz1PaperTubeCarrier
        (pureWZ2PaperCenteredTube (terminal.family.tube index))
    rw [pureWZ2PaperCenteredTube_paperCarrier]
    exact terminal.cubicalShading.subset_body index

@[simp] theorem centeredExactShading_carrier
    (terminal : commonSource.TerminalGeometry)
    (index : Fin terminal.family.card) :
    terminal.centeredExactShading.carrier index = terminal.exactShading.carrier index := rfl

@[simp] theorem centeredCubicalShading_carrier
    (terminal : commonSource.TerminalGeometry)
    (index : Fin terminal.family.card) :
    terminal.centeredCubicalShading.carrier index = terminal.cubicalShading.carrier index := rfl

theorem centeredCubicalShading_cubical
    (terminal : commonSource.TerminalGeometry) :
    WZ1PaperIsCubicalShading terminal.centeredCubicalShading := by
  intro index point hpoint
  exact TerminalGeometry.cubical commonSource terminal index point hpoint

theorem centeredExactShading_union
    (terminal : commonSource.TerminalGeometry) :
    terminal.centeredExactShading.union = terminal.exactShading.union := by
  apply Set.Subset.antisymm
  · rintro point ⟨index, hpoint⟩
    exact ⟨index, hpoint⟩
  · rintro point ⟨index, hpoint⟩
    exact ⟨index, hpoint⟩

theorem centeredCubicalShading_union
    (terminal : commonSource.TerminalGeometry) :
    terminal.centeredCubicalShading.union = terminal.cubicalShading.union := by
  apply Set.Subset.antisymm
  · rintro point ⟨index, hpoint⟩
    exact ⟨index, hpoint⟩
  · rintro point ⟨index, hpoint⟩
    exact ⟨index, hpoint⟩

theorem centeredExactShading_mass
    (terminal : commonSource.TerminalGeometry) :
    terminal.centeredExactShading.mass = terminal.exactShading.mass := by
  unfold Kakeya.Streamlined.Shading.mass
  rfl

theorem centeredCubicalShading_mass
    (terminal : commonSource.TerminalGeometry) :
    terminal.centeredCubicalShading.mass = terminal.cubicalShading.mass := by
  unfold Kakeya.Streamlined.Shading.mass
  rfl

/-- The ordinary carrier of a centered terminal representative is contained in
the unchanged cropped paper carrier. -/
theorem centeredFamily_ordinary_carrier_subset_paper
    (terminal : commonSource.TerminalGeometry) (index : Fin terminal.family.card) :
    (terminal.centeredFamily.tube index).carrier ⊆
      wz1PaperTubeCarrier (terminal.centeredFamily.tube index) := by
  apply pureWZ2_centered_lineClass_carrier_subset_paper
    commonSource.halfOffsetLineClassTargetDelta_pos
    (commonSource.halfOffsetLineClassTargetDelta_small.le.trans (by norm_num))
    (terminal.centeredFamily.tube index)
    (centeredFamily_line_class commonSource terminal index)
  rw [centeredFamily_tube, pureWZ2PaperCenteredTube_midpoint]
  exact wz1TubeAxisZeroPoint_coord_two _
    (TerminalGeometry.line_class commonSource terminal index).vertical

/-- The same zero-loss retyping is available for the actual cubical output. -/
def retypeCubicalGlobalGrains {C : ENNReal}
    (terminal : commonSource.TerminalGeometry)
    (data : PureWZ2C2GlobalGrainData terminal.cubicalShading sigma C) :
    PureWZ2C2GlobalGrainData terminal.centeredCubicalShading sigma C where
  f := data.f
  normalized := data.normalized
  global_ad := by
    intro z
    rw [centeredCubicalShading_union commonSource terminal]
    exact data.global_ad z

/-- The centered terminal changes only the orientation and anchoring of the
ordinary representatives; its shaded carriers are literally unchanged. -/
def centeredCubicalGrainRetype
    (terminal : commonSource.TerminalGeometry) :
    PureWZ2SameCarrierGrainRetype terminal.family terminal.centeredFamily
      terminal.cubicalShading terminal.centeredCubicalShading where
  indexEquiv := Equiv.refl _
  carrier_eq := fun _ => rfl
  direction_eq_or_neg := by
    intro index
    change wz1PaperDirection (terminal.family.tube index) =
        (terminal.family.tube index).direction ∨
      wz1PaperDirection (terminal.family.tube index) =
        -(terminal.family.tube index).direction
    unfold wz1PaperDirection
    split_ifs with hsign
    · exact Or.inl rfl
    · exact Or.inr rfl

/-- Local grains retype to the centered representatives with no loss. -/
def retypeCubicalLocalGrains {C : ENNReal}
    (terminal : commonSource.TerminalGeometry)
    (data : PureWZ2LocalGrainData terminal.cubicalShading sigma C) :
    PureWZ2LocalGrainData terminal.centeredCubicalShading sigma C :=
  data.retypeSameCarrier (centeredCubicalGrainRetype commonSource terminal)

end TerminalGeometry

end PureWZ2DirectCommonYSourceAssembly

end Kakeya.Assouad

end
