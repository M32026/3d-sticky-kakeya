import MyLeanRepo.Kakeya.Streamlined.RandomTranslation.FrostmanFromDeltaMax
import MyLeanRepo.Kakeya.Streamlined.DilatedTubeCover.FullContainmentFibers
import MyLeanRepo.Kakeya.Streamlined.IndependentDilatedCoverFullFiberMass
import MyLeanRepo.Kakeya.Streamlined.DividingScales.ConvexThickeningGrowth
import MyLeanRepo.Kakeya.Streamlined.GeneralizedFrostman.FromNormalizationSelection.AlgebraFixes

/-!
# Frostman control for one full geometric containment fiber

An auxiliary parent map supplies a disjoint assigned fiber and hence a
convenient lower bound for the mass attached to one coarse parent.  The paper
fiber is larger: it contains every fine tube geometrically contained in the
same dilated parent.  The assigned mass lower bound therefore also controls
the full fiber, while maximal density remains bounded by the ambient fine
family.

This module performs that one-way transport without identifying the assigned
fiber with the paper fiber.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Streamlined.RandomTranslation

/--
Ambient `deltaMax` control and a positive lower bound for the complete
geometric containment-fiber mass control that fiber's Frostman constant.

This is the canonical paper-facing one-scale bridge. It contains no assigned
parent-map datum.
-/
theorem full_containment_fiber_frostman_of_full_mass
    {delta rho A : ℝ}
    {fine : TubeFamily delta}
    {coarse : TubeFamily rho}
    (P : DilatedTubeCover A fine coarse)
    (parent : Fin coarse.card)
    {C m bound : ENNReal}
    (hCpos : 0 < C)
    (hmpos : 0 < m)
    (hmtop : m ≠ ⊤)
    (hcontainerPos :
      0 < volume (dilatedTubeCarrier A (coarse.tube parent)))
    (hcontainerTop :
      volume (dilatedTubeCarrier A (coarse.tube parent)) ≠ ⊤)
    (hdeltaMax : fine.toBodyFamily.deltaMax ≤ C)
    (hmass :
      m ≤
        P.fullContainmentFiberCount parent *
          Kakeya.deltaTubeVolume delta)
    (hbound :
      C * volume (dilatedTubeCarrier A (coarse.tube parent)) / m ≤
        bound) :
    P.fullContainmentFiberFrostmanConstant parent ≤ bound := by
  let fiber := P.fullContainmentFiberSubfamily parent
  let container := dilatedTubeCarrier A (coarse.tube parent)
  have hfiberDeltaMax :
      fiber.family.toBodyFamily.deltaMax ≤ C :=
    (subfamily_deltaMax_le fiber.toBodySubfamily).trans hdeltaMax
  have hfiberContained :
      ∀ index,
        (fiber.family.toBodyFamily.body index).carrier ⊆ container := by
    intro index
    exact P.fullContainmentFiberSubfamily_all_contained parent index
  have hfiberMass :
      fiber.family.toBodyFamily.mass =
        P.fullContainmentFiberCount parent *
          Kakeya.deltaTubeVolume delta := by
    rw [TubeFamily.bodyMass_eq_nominalMass]
    rfl
  have hfiberContainedMass :
      fiber.family.toBodyFamily.containedMass container =
        fiber.family.toBodyFamily.mass :=
    BodyFamily.containedMass_eq_mass_of_all_contained
      fiber.family.toBodyFamily container hfiberContained
  have hfullMass :
      m ≤ fiber.family.toBodyFamily.containedMass container := by
    rw [hfiberContainedMass, hfiberMass]
    exact hmass
  have hfrostman :
      fiber.family.toBodyFamily.IsCFrostmanIn container
        (C * volume container / m) :=
    BodyFamily.frostman_from_deltaMax
      hmpos hmtop hcontainerPos hcontainerTop
      hfiberDeltaMax hfullMass
  exact hfrostman.trans hbound

/--
Ambient `deltaMax` control and a positive mass lower bound supplied by one
assigned anchor fiber control the complete geometric containment fiber.

The assigned fiber is used only to lower-bound the reference mass.  The
conclusion is about the full containment fiber, and no reverse inclusion or
fiber equality is assumed.
-/
theorem full_containment_fiber_frostman_of_assigned_mass
    {delta rho A : ℝ}
    {fine : TubeFamily delta}
    {coarse : TubeFamily rho}
    (P : DilatedTubeCover A fine coarse)
    (parent : Fin coarse.card)
    {C m bound : ENNReal}
    (hCpos : 0 < C)
    (hmpos : 0 < m)
    (hmtop : m ≠ ⊤)
    (hcontainerPos :
      0 < volume (dilatedTubeCarrier A (coarse.tube parent)))
    (hcontainerTop :
      volume (dilatedTubeCarrier A (coarse.tube parent)) ≠ ⊤)
    (hdeltaMax : fine.toBodyFamily.deltaMax ≤ C)
    (hmass :
      m ≤ P.toFactoring.fiberCount parent *
        Kakeya.deltaTubeVolume delta)
    (hbound :
      C * volume (dilatedTubeCarrier A (coarse.tube parent)) / m ≤
        bound) :
    P.fullContainmentFiberFrostmanConstant parent ≤ bound := by
  let fiber := P.fullContainmentFiberSubfamily parent
  let assigned := P.assignedFiberSubfamily parent
  let container := dilatedTubeCarrier A (coarse.tube parent)
  have hfiberDeltaMax :
      fiber.family.toBodyFamily.deltaMax ≤ C :=
    (subfamily_deltaMax_le fiber.toBodySubfamily).trans hdeltaMax
  have hfiberContained :
      ∀ index,
        (fiber.family.toBodyFamily.body index).carrier ⊆ container := by
    intro index
    exact P.fullContainmentFiberSubfamily_all_contained parent index
  have hassignedMass :
      assigned.family.toBodyFamily.mass =
        P.toFactoring.fiberCount parent * Kakeya.deltaTubeVolume delta := by
    rw [TubeFamily.bodyMass_eq_nominalMass]
    change
      ((P.toFactoring.fiberIndices parent).card : ENNReal) *
          Kakeya.deltaTubeVolume delta =
        P.toFactoring.fiberCount parent *
          Kakeya.deltaTubeVolume delta
    rfl
  have hassignedCardLe :
      assigned.family.card ≤ fiber.family.card := by
    dsimp only [assigned, fiber,
      DilatedTubeCover.assignedFiberSubfamily,
      DilatedTubeCover.fullContainmentFiberSubfamily]
    change
      (P.toFactoring.fiberIndices parent).card ≤
        (P.fullContainmentFiberIndices parent).card
    exact Finset.card_le_card
      (P.factoringFiberIndices_subset_fullContainmentFiberIndices parent)
  have hassignedMassLe :
      assigned.family.toBodyFamily.mass ≤ fiber.family.toBodyFamily.mass := by
    rw [TubeFamily.bodyMass_eq_nominalMass,
      TubeFamily.bodyMass_eq_nominalMass]
    dsimp only [TubeFamily.nominalMass, TubeFamily.enncard]
    exact mul_le_mul_right'
      (by exact_mod_cast hassignedCardLe)
      (Kakeya.deltaTubeVolume delta)
  have hfiberContainedMass :
      fiber.family.toBodyFamily.containedMass container =
        fiber.family.toBodyFamily.mass :=
    BodyFamily.containedMass_eq_mass_of_all_contained
      fiber.family.toBodyFamily container hfiberContained
  have hfullMass :
      m ≤ fiber.family.toBodyFamily.containedMass container := by
    rw [hfiberContainedMass]
    calc
      m ≤ P.toFactoring.fiberCount parent *
          Kakeya.deltaTubeVolume delta := hmass
      _ = assigned.family.toBodyFamily.mass := hassignedMass.symm
      _ ≤ fiber.family.toBodyFamily.mass := hassignedMassLe
  have hfrostman :
      fiber.family.toBodyFamily.IsCFrostmanIn container
        (C * volume container / m) :=
    BodyFamily.frostman_from_deltaMax
      hmpos hmtop hcontainerPos hcontainerTop
      hfiberDeltaMax hfullMass
  exact hfrostman.trans hbound

/--
One full geometric containment fiber of an `A`-dilated cover is Frostman once
the assigned anchor fiber supplies the mass required by ambient `deltaMax`.

The right side of `hcluster` is the mass of the auxiliary assigned fiber.  It
is used only as a lower bound for the mass of the complete containment fiber.
-/
theorem full_containment_fiber_frostman_of_dilated_cover_cluster_mass
    {delta rho eta A : ℝ}
    (hdelta : 0 < delta)
    (hrho : 0 < rho)
    {fine : TubeFamily delta}
    {coarse : TubeFamily rho}
    (P : DilatedTubeCover A fine coarse)
    (parent : Fin coarse.card)
    {C volumeFactor : ENNReal}
    (hCpos : 0 < C)
    (hCtop : C ≠ ⊤)
    (hvolumeFactorPos : 0 < volumeFactor)
    (hvolumeFactorTop : volumeFactor ≠ ⊤)
    (hdeltaMax : fine.toBodyFamily.deltaMax ≤ C)
    (hvolumeFactor :
      volume (dilatedTubeCarrier A (coarse.tube parent)) =
        volumeFactor * Kakeya.deltaTubeVolume rho)
    (hcluster :
      C * volumeFactor * Kakeya.deltaTubeVolume rho *
            Kakeya.realRpowENN delta eta ≤
        P.toFactoring.fiberCount parent * Kakeya.deltaTubeVolume delta) :
    P.fullContainmentFiberFrostmanConstant parent ≤
      Kakeya.realRpowENN delta (-eta) := by
  let fiber := P.fullContainmentFiberSubfamily parent
  let assigned := P.assignedFiberSubfamily parent
  let container := dilatedTubeCarrier A (coarse.tube parent)
  let power := Kakeya.realRpowENN delta eta
  let containerVolume := volume container
  let minimumMass := C * containerVolume * power

  have hpower_pos : 0 < power := by
    dsimp only [power, Kakeya.realRpowENN]
    exact ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hdelta eta)
  have hpower_top : power ≠ ⊤ :=
    ENNReal.ofReal_ne_top
  have hcontainer_volume :
      containerVolume =
        volumeFactor * Kakeya.deltaTubeVolume rho := by
    simpa [containerVolume, container] using hvolumeFactor
  have hcontainer_pos : 0 < containerVolume := by
    rw [hcontainer_volume]
    exact ENNReal.mul_pos hvolumeFactorPos.ne'
      (deltaTubeVolume_pos hrho).ne'
  have hcontainer_top : containerVolume ≠ ⊤ := by
    rw [hcontainer_volume]
    exact ENNReal.mul_ne_top hvolumeFactorTop deltaTubeVolume_ne_top
  have hminimum_pos : 0 < minimumMass := by
    dsimp only [minimumMass]
    positivity
  have hminimum_top : minimumMass ≠ ⊤ := by
    dsimp only [minimumMass]
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top hCtop hcontainer_top) hpower_top

  have hfiber_deltaMax :
      fiber.family.toBodyFamily.deltaMax ≤ C := by
    exact (subfamily_deltaMax_le fiber.toBodySubfamily).trans hdeltaMax
  have hfiber_contained :
      ∀ index,
        (fiber.family.toBodyFamily.body index).carrier ⊆ container := by
    intro index
    exact P.fullContainmentFiberSubfamily_all_contained parent index
  have hassigned_mass :
      assigned.family.toBodyFamily.mass =
        P.toFactoring.fiberCount parent * Kakeya.deltaTubeVolume delta := by
    rw [TubeFamily.bodyMass_eq_nominalMass]
    change
      ((P.toFactoring.fiberIndices parent).card : ENNReal) *
          Kakeya.deltaTubeVolume delta =
        P.toFactoring.fiberCount parent *
          Kakeya.deltaTubeVolume delta
    rfl
  have hassigned_card_le :
      assigned.family.card ≤ fiber.family.card := by
    dsimp only [assigned, fiber,
      DilatedTubeCover.assignedFiberSubfamily,
      DilatedTubeCover.fullContainmentFiberSubfamily]
    change
      (P.toFactoring.fiberIndices parent).card ≤
        (P.fullContainmentFiberIndices parent).card
    exact Finset.card_le_card
      (P.factoringFiberIndices_subset_fullContainmentFiberIndices parent)
  have hassigned_mass_le :
      assigned.family.toBodyFamily.mass ≤ fiber.family.toBodyFamily.mass := by
    rw [TubeFamily.bodyMass_eq_nominalMass,
      TubeFamily.bodyMass_eq_nominalMass]
    dsimp only [TubeFamily.nominalMass, TubeFamily.enncard]
    exact mul_le_mul_right'
      (by exact_mod_cast hassigned_card_le)
      (Kakeya.deltaTubeVolume delta)
  have hfiber_contained_mass :
      fiber.family.toBodyFamily.containedMass container =
        fiber.family.toBodyFamily.mass :=
    BodyFamily.containedMass_eq_mass_of_all_contained
      fiber.family.toBodyFamily container hfiber_contained
  have hmass :
      minimumMass ≤ fiber.family.toBodyFamily.containedMass container := by
    rw [hfiber_contained_mass]
    calc
      minimumMass
          = C * volumeFactor * Kakeya.deltaTubeVolume rho * power := by
              dsimp only [minimumMass]
              rw [hcontainer_volume]
              ring
      _ ≤ P.toFactoring.fiberCount parent *
          Kakeya.deltaTubeVolume delta := by
            simpa [power] using hcluster
      _ = assigned.family.toBodyFamily.mass := hassigned_mass.symm
      _ ≤ fiber.family.toBodyFamily.mass := hassigned_mass_le

  have hfrostman :
      fiber.family.toBodyFamily.IsCFrostmanIn container
        (C * containerVolume / minimumMass) :=
    BodyFamily.frostman_from_deltaMax
      hminimum_pos hminimum_top
      hcontainer_pos hcontainer_top
      hfiber_deltaMax hmass
  have hbase_pos : 0 < C * containerVolume := by
    positivity
  have hbase_top : C * containerVolume ≠ ⊤ :=
    ENNReal.mul_ne_top hCtop hcontainer_top
  have hcancel :
      C * containerVolume / minimumMass = power⁻¹ := by
    dsimp only [minimumMass]
    let base := C * containerVolume
    change base / (base * power) = power⁻¹
    have hinverse :
        (base * power)⁻¹ = base⁻¹ * power⁻¹ :=
      ENNReal.mul_inv (Or.inl hbase_pos.ne') (Or.inl hbase_top)
    calc
      base / (base * power)
          = base * (base * power)⁻¹ := by rfl
      _ = base * (base⁻¹ * power⁻¹) := by rw [hinverse]
      _ = (base * base⁻¹) * power⁻¹ := by ring
      _ = (base / base) * power⁻¹ := by rfl
      _ = power⁻¹ := by
        rw [ENNReal.div_self hbase_pos.ne' hbase_top]
        simp
  have hpower_inverse :
      power⁻¹ = Kakeya.realRpowENN delta (-eta) := by
    dsimp only [power]
    exact
      (Kakeya.Streamlined.GeneralizedFrostman.realRpowENN_neg hdelta).symm
  change fiber.family.toBodyFamily.frostmanConstantIn container ≤
    Kakeya.realRpowENN delta (-eta)
  rw [hcancel, hpower_inverse] at hfrostman
  exact hfrostman

end Kakeya.Streamlined.RandomTranslation

end
