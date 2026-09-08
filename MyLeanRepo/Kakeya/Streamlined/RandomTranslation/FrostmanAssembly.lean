import MyLeanRepo.Kakeya.Streamlined.RandomTranslation.FrostmanFromDeltaMax
import MyLeanRepo.Kakeya.Streamlined.RandomTranslation.Submultiplicativity
import MyLeanRepo.Kakeya.Streamlined.TubeRefinement
import MyLeanRepo.Kakeya.Streamlined.IndependentDilatedCoverFullFiberMass
import MyLeanRepo.Kakeya.Streamlined.MaximalDensityFactoring.SubfamilyHelpers
import MyLeanRepo.Kakeya.Streamlined.RandomTranslation.DeterministicHelpers

/-!
# Frostman-at-every-scale from deltaMax control

Assembles the Frostman property for a uniform tube structure from:
- bounded `deltaMax` of the fine family
- uniform lower bounds on fiber mass
- uniform upper bounds on coarse tube volume

## Main results

- `frostmanAtEveryScale_of_deltaMax`: uniform bounds give `IsFrostmanAtEveryScale`
- `frostmanAtScale_of_deltaMax`: scale-dependent bounds give per-scale Frostman
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Streamlined

namespace UniformTubeStructure

/--
Per-scale Frostman property for complete geometric containment fibers of a
public strict uniform structure.
-/
theorem fullContainmentFrostmanAtScale_of_deltaMax
    {δ : ℝ} {F : TubeFamily δ} (U : UniformTubeStructure F)
    {C : ENNReal} (hC_pos : 0 < C)
    (h_deltaMax : F.toBodyFamily.deltaMax ≤ C)
    (rho : AdmissibleScale δ)
    (hrho_pos : 0 < rho.1)
    {m_rho V_rho : ENNReal}
    (hm_pos : 0 < m_rho) (hm_ne_top : m_rho ≠ ⊤)
    (hV_pos : 0 < V_rho) (hV_ne_top : V_rho ≠ ⊤)
    (h_fiber_mass :
      ∀ parent,
        m_rho ≤
          F.containedCount (U.coarse rho) parent *
            Kakeya.deltaTubeVolume δ)
    (h_coarse_vol :
      ∀ parent,
        ((U.coarse rho).toBodyFamily.body parent).volume ≤ V_rho) :
    (U.cover rho).FibersAreCFrostman
      (C * V_rho / m_rho) := by
  intro parent
  let fiber : TubeSubfamily F :=
    TubeSubfamily.fromFinset F
      (F.containedIndices (U.coarse rho) parent)
  have hfiberDelta :
      fiber.family.toBodyFamily.deltaMax ≤ C :=
    (subfamily_deltaMax_le fiber.toBodySubfamily).trans h_deltaMax
  have hfiberContained :
      ∀ index,
        (fiber.family.toBodyFamily.body index).carrier ⊆
          ((U.coarse rho).tube parent).carrier := by
    intro index
    have hmem :=
      Finset.orderEmbOfFin_mem
        (F.containedIndices (U.coarse rho) parent) rfl index
    change
      (F.tube (fiber.embedding index)).carrier ⊆
        ((U.coarse rho).tube parent).carrier
    exact TubeFamily.mem_containedIndices_iff.mp hmem
  have hfiberMass :
      fiber.family.toBodyFamily.mass =
        F.containedCount (U.coarse rho) parent *
          Kakeya.deltaTubeVolume δ := by
    rw [TubeFamily.bodyMass_eq_nominalMass]
    rfl
  have hcontainedMass :
      fiber.family.toBodyFamily.containedMass
          ((U.coarse rho).tube parent).carrier =
        fiber.family.toBodyFamily.mass :=
    BodyFamily.containedMass_eq_mass_of_all_contained
      fiber.family.toBodyFamily
      ((U.coarse rho).tube parent).carrier
      hfiberContained
  have hmass :
      m_rho ≤
        fiber.family.toBodyFamily.containedMass
          ((U.coarse rho).tube parent).carrier := by
    rw [hcontainedMass, hfiberMass]
    exact h_fiber_mass parent
  have hcontainerPos :
      0 < volume ((U.coarse rho).tube parent).carrier := by
    rw [show volume ((U.coarse rho).tube parent).carrier =
        Kakeya.deltaTubeVolume rho.1 by
      exact RandomTranslation.tube_volume_eq_deltaTubeVolume
        ((U.coarse rho).tube parent)]
    exact RandomTranslation.deltaTubeVolume_pos
      hrho_pos
  have hcontainerTop :
      volume ((U.coarse rho).tube parent).carrier ≠ ⊤ := by
    have hle :
        volume ((U.coarse rho).tube parent).carrier ≤ V_rho := by
      exact h_coarse_vol parent
    exact ne_top_of_le_ne_top hV_ne_top hle
  change
    fiber.family.toBodyFamily.frostmanConstantIn
        ((U.coarse rho).tube parent).carrier ≤
      C * V_rho / m_rho
  have hfrost :=
    BodyFamily.frostman_from_deltaMax
      hm_pos hm_ne_top hcontainerPos hcontainerTop
      hfiberDelta hmass
  exact hfrost.trans (by
    gcongr
    exact h_coarse_vol parent)

end UniformTubeStructure

namespace AssignedUniformTubeStructure

/-- Per-scale Frostman property from deltaMax, fiber mass, and coarse volume
bounds that may depend on the scale. -/
theorem frostmanAtScale_of_deltaMax
    {δ : ℝ} {F : TubeFamily δ} (U : AssignedUniformTubeStructure F)
    {C : ENNReal} (hC_pos : 0 < C)
    (h_deltaMax : F.toBodyFamily.deltaMax ≤ C)
    (rho : AdmissibleScale δ)
    {m_rho V_rho : ENNReal}
    (hm_pos : 0 < m_rho) (hm_ne_top : m_rho ≠ ⊤)
    (hV_ne_top : V_rho ≠ ⊤)
    (h_fiber_mass : ∀ j, (U.cover rho).toFactoring.fiberMass j ≥ m_rho)
    (h_coarse_vol : ∀ j, ((U.coarse rho).toBodyFamily.body j).volume ≤ V_rho) :
    (U.cover rho).AssignedFibersAreCFrostman
      (C * V_rho / m_rho) := by
  let Q : Factoring F.toBodyFamily (U.coarse rho).toBodyFamily :=
    (U.cover rho).toFactoring
  have h_contained : ∀ j K, Convex ℝ K → Q.fiberContainedMass j K ≤ C * volume K := by
    intro j K hK
    exact Factoring.fiber_containedMass_le_deltaMax Q j C hC_pos h_deltaMax K hK
  exact Factoring.fibers_frostman_from_containedMass
    hm_pos hm_ne_top hV_ne_top h_contained h_fiber_mass h_coarse_vol

/-- Frostman at every scale from uniform deltaMax, fiber mass, and coarse
volume bounds. -/
theorem frostmanAtEveryScale_of_deltaMax
    {δ : ℝ} {F : TubeFamily δ} (U : AssignedUniformTubeStructure F)
    {C m V : ENNReal}
    (hC_pos : 0 < C)
    (hm_pos : 0 < m) (hm_ne_top : m ≠ ⊤)
    (hV_ne_top : V ≠ ⊤)
    (h_deltaMax : F.toBodyFamily.deltaMax ≤ C)
    (h_fiber_mass : ∀ (rho : AdmissibleScale δ) j,
        (U.cover rho).toFactoring.fiberMass j ≥ m)
    (h_coarse_vol : ∀ (rho : AdmissibleScale δ) j,
        ((U.coarse rho).toBodyFamily.body j).volume ≤ V) :
    U.AssignedIsFrostmanAtEveryScale (C * V / m) := by
  intro rho
  exact U.frostmanAtScale_of_deltaMax hC_pos h_deltaMax rho
    hm_pos hm_ne_top hV_ne_top
    (h_fiber_mass rho) (h_coarse_vol rho)

end AssignedUniformTubeStructure

namespace UniformTubeStructure

/-- Per-scale Frostman property for the chosen parent-map fibers. -/
theorem frostmanAtScale_of_deltaMax
    {δ : ℝ} {F : TubeFamily δ} (U : UniformTubeStructure F)
    {C : ENNReal} (hC_pos : 0 < C)
    (h_deltaMax : F.toBodyFamily.deltaMax ≤ C)
    (rho : AdmissibleScale δ)
    {m_rho V_rho : ENNReal}
    (hm_pos : 0 < m_rho) (hm_ne_top : m_rho ≠ ⊤)
    (hV_ne_top : V_rho ≠ ⊤)
    (h_fiber_mass :
      ∀ j, (U.cover rho).toFactoring.fiberMass j ≥ m_rho)
    (h_coarse_vol :
      ∀ j, ((U.coarse rho).toBodyFamily.body j).volume ≤ V_rho) :
    (U.cover rho).AssignedFibersAreCFrostman
      (C * V_rho / m_rho) :=
  U.toAssigned.frostmanAtScale_of_deltaMax
    hC_pos h_deltaMax rho hm_pos hm_ne_top hV_ne_top
    h_fiber_mass h_coarse_vol

/-- All-scale Frostman property for the chosen parent-map fibers. -/
theorem frostmanAtEveryScale_of_deltaMax
    {δ : ℝ} {F : TubeFamily δ} (U : UniformTubeStructure F)
    {C m V : ENNReal}
    (hC_pos : 0 < C)
    (hm_pos : 0 < m) (hm_ne_top : m ≠ ⊤)
    (hV_ne_top : V ≠ ⊤)
    (h_deltaMax : F.toBodyFamily.deltaMax ≤ C)
    (h_fiber_mass : ∀ (rho : AdmissibleScale δ) j,
        (U.cover rho).toFactoring.fiberMass j ≥ m)
    (h_coarse_vol : ∀ (rho : AdmissibleScale δ) j,
        ((U.coarse rho).toBodyFamily.body j).volume ≤ V) :
    U.IsFrostmanAtEveryScale (C * V / m) :=
  U.toAssigned.frostmanAtEveryScale_of_deltaMax
    hC_pos hm_pos hm_ne_top hV_ne_top h_deltaMax
    h_fiber_mass h_coarse_vol

end UniformTubeStructure

end Kakeya.Streamlined

end
