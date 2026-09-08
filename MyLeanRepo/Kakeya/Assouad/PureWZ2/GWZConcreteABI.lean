import MyLeanRepo.Kakeya.Assouad.PureWZ2.GWZBridge
import MyLeanRepo.Kakeya.Streamlined.DilatedStickyInput
import MyLeanRepo.Kakeya.Streamlined.DividingScales.FrostmanInequalities
import MyLeanRepo.Kakeya.Streamlined.IndependentDilatedCoverFullFiberMass
import MyLeanRepo.Kakeya.Streamlined.RandomTranslation.DeterministicHelpers

/-!
# Concrete GWZ ABI for the reanchored pure WZ2 theorem

This module projects the public GWZ complete-containment-fiber structure to
the branch-independent semantic input of the corrected GWZ remark.  The
auxiliary assigned-fiber API is not used.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Assouad

/--
Project one raw quantitative GWZ structure to the complete-full-fiber
semantic structure consumed by the corrected Node 9.
-/
theorem pureWZ2GWZFullFiberStructure_of_dilatedUniformTubeStructure
    {delta A : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {C : ENNReal}
    (hdelta : 0 < delta)
    (hA : 0 < A)
    (U :
      Kakeya.Streamlined.DilatedUniformTubeStructure
        (A := A) source)
    (hUniformity : U.uniformity ≤ C)
    (hFrostman :
      U.IsFrostmanAtEveryScale C)
    (hCFinite : C ≠ ⊤) :
    PureWZ2GWZFullFiberStructure (A := A) source C := by
  refine ⟨⟨U.one_le_uniformity.trans hUniformity, hCFinite⟩, ?_⟩
  intro rho
  let cover := U.cover rho
  let coarse := U.coarse rho
  let fullFiberIndices :=
    cover.fullContainmentFiberIndices
  have hCarrier :
      ∀ parent : Fin coarse.card,
        wz2PaperCenteredDilatedCarrier A (coarse.tube parent) =
          Kakeya.Streamlined.dilatedTubeCarrier A
            (coarse.tube parent) := by
    intro parent
    rfl
  have hFullFiberNonempty :
      ∀ parent : Fin coarse.card,
        (fullFiberIndices parent).Nonempty := by
    intro parent
    rcases cover.parent_surjective parent with
      ⟨index, hparent⟩
    refine ⟨index, ?_⟩
    rw [cover.mem_fullContainmentFiberIndices_iff]
    simpa [hparent] using cover.nested index
  refine ⟨{
    coarse := coarse
    coarse_distinct := U.coarse_distinct rho
    fullFiberIndices := fullFiberIndices
    fullFiberIndices_eq := by
      intro parent
      ext index
      simp only [fullFiberIndices,
        Kakeya.Streamlined.DilatedTubeCover.mem_fullContainmentFiberIndices_iff,
        Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hCarrier parent]
    full_fiber_nonempty := hFullFiberNonempty
    full_fibers_cover := by
      intro index
      refine ⟨cover.parent index, ?_⟩
      rw [cover.mem_fullContainmentFiberIndices_iff]
      exact cover.nested index
    full_fiber_uniform := by
      intro first second
      have hUniform :=
        (U.uniform rho).2 first second
      change
        cover.fullContainmentFiberCount first ≤
          C * cover.fullContainmentFiberCount second
      exact hUniform.trans (by gcongr)
    full_fiber_frostman := by
      intro parent
      dsimp only
      let fiber :=
        Kakeya.Streamlined.TubeSubfamily.fromFinset
          source (fullFiberIndices parent)
      let container :=
        Kakeya.Streamlined.dilatedTubeCarrier A
          (coarse.tube parent)
      have hrho : 0 < rho.1 :=
        hdelta.trans_le rho.2.1
      have hContainerVolumeZero :
          volume container ≠ 0 := by
        dsimp only [container]
        rw [← hCarrier parent]
        exact
          (wz2_paper_centeredDilatedCarrier_volume_pos
            (coarse.tube parent) hrho hA).ne'
      have hContainerVolumeTop :
          volume container ≠ ⊤ := by
        dsimp only [container]
        rw [← hCarrier parent]
        exact
          wz2_paper_centeredDilatedCarrier_volume_ne_top
            (coarse.tube parent) hrho
      have hAllContained :
          ∀ index,
            (fiber.family.tube index).carrier ⊆ container := by
        intro index
        rw [fiber.tube_eq index]
        have hindex :
            fiber.embedding index ∈ fullFiberIndices parent :=
          Finset.orderEmbOfFin_mem
            (fullFiberIndices parent) rfl index
        exact
          (cover.mem_fullContainmentFiberIndices_iff
            parent (fiber.embedding index)).mp hindex
      have hMassContainer :
          fiber.family.toBodyFamily.containedMass container =
            fiber.family.toBodyFamily.mass :=
        Kakeya.Streamlined.BodyFamily.containedMass_eq_mass_of_all_contained
          _ _ hAllContained
      have hFiberNonempty : fiber.family.Nonempty := by
        change 0 < (fullFiberIndices parent).card
        exact
          Finset.card_pos.mpr
            (hFullFiberNonempty parent)
      have hMassContainerZero :
          fiber.family.toBodyFamily.containedMass container ≠ 0 := by
        rw [hMassContainer,
          Kakeya.Streamlined.TubeFamily.bodyMass_eq_nominalMass]
        exact
          (Kakeya.Streamlined.RandomTranslation.nominalMass_pos
            hdelta hFiberNonempty).ne'
      have hMassContainerTop :
          fiber.family.toBodyFamily.containedMass container ≠ ⊤ := by
        rw [hMassContainer,
          Kakeya.Streamlined.TubeFamily.bodyMass_eq_nominalMass]
        exact
          Kakeya.Streamlined.RandomTranslation.nominalMass_ne_top
      intro convexSet hConvex hSubset
      have hSubsetContainer : convexSet ⊆ container := by
        dsimp only [container]
        rwa [← hCarrier parent]
      have hBound :=
        Kakeya.Streamlined.BodyFamily.containedMass_mul_volume_le_of_frostmanConstantIn_le
          fiber.family.toBodyFamily
          hContainerVolumeZero hContainerVolumeTop
          hMassContainerZero hMassContainerTop
          (hFrostman rho parent)
          hConvex hSubsetContainer
      rw [hMassContainer] at hBound
      simpa only [container, ← hCarrier parent] using hBound
  }⟩

/--
The current paper-facing approximate GWZ structure projects directly to the
semantic input of corrected Node 9.
-/
theorem pureWZ2GWZFullFiberStructure_of_approxDilatedUniformTubeStructure
    {delta A eta : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    (hdelta : 0 < delta)
    (hA : 0 < A)
    (U :
      Kakeya.Streamlined.ApproxDilatedUniformTubeStructure
        (A := A) eta source)
    (hFrostman :
      U.raw.IsFrostmanAtEveryScale
        (Kakeya.realRpowENN delta (-eta))) :
    PureWZ2GWZFullFiberStructure
      (A := A) source
      (Kakeya.realRpowENN delta (-eta)) :=
  pureWZ2GWZFullFiberStructure_of_dilatedUniformTubeStructure
    hdelta hA U.raw U.uniformity_le hFrostman
    (by simp [Kakeya.realRpowENN])

/--
The exact concrete ABI contract: pure WZ2 Theorem 5.2 plus corrected Node 9
supplies the current public GWZ sticky-volume socket.
-/
def PureWZ2ConcreteGWZABIStatement : Prop :=
  PureWZ2Theorem5_2Statement →
    PureWZ2GWZRemarkStatement →
      Kakeya.Streamlined.GWZStickyVolumeSocket

theorem pure_wz2_concrete_gwz_abi :
    PureWZ2ConcreteGWZABIStatement := by
  intro pureTheorem remark
  have semantic :
      PureWZ2FixedSupportDilatedStickyContract 7998000 10 :=
    pure_wz2_semantic_socket_assembly pureTheorem remark
  change
    Kakeya.Streamlined.FixedSupportDilatedStickyHypothesis
      7998000 10
  intro epsilon hepsilon
  rcases semantic epsilon hepsilon with
    ⟨eta, delta₀, heta, hdelta₀, hdelta₀One, hmain⟩
  refine
    ⟨eta, delta₀, heta, hdelta₀, hdelta₀One, ?_⟩
  intro delta hdelta hdeltaSmall source
    hSourceNonempty hSourceSupport hSourceDistinct U
    hFrostman shading hShadingDense
  apply hmain delta hdelta hdeltaSmall source
    hSourceNonempty hSourceSupport hSourceDistinct
  · exact
      pureWZ2GWZFullFiberStructure_of_approxDilatedUniformTubeStructure
        hdelta (by norm_num) U hFrostman
  · exact hShadingDense

end Kakeya.Assouad

end
