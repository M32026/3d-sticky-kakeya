import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23NormalTilt
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23NormalTiltWitnessProducer

/-!
# Large first normal component from one full local grain

This module closes the downstream assembly around the planar fullness leaf.
In its small-tilt branch the numerical small-scale assumption gives the
`1/10` tilt directly.  In its fullness branch the closed normal-tilt theorem
gives the same bound.  The unit-normal algebra then yields `|V_x| >= 1/4`.
-/

namespace Kakeya.Assouad

noncomputable section

/--
Every actual full local grain prepared for Lemma 23 has a normal with large
first horizontal component.
-/
theorem wz1_lemma23_full_grain_normal_first_component
    (hPlanar : WZ1Lemma23PlanarProjectionFullnessStatement)
    (rho sigma eta : ℝ) (C : ENNReal)
    (slope : ℝ → ℝ)
    (hrho : 0 < rho) (hrho_one : rho ≤ 1)
    (hsigma : 0 < sigma) (hsigma_one : sigma < 1)
    (heta : 0 < eta) (heta_sigma : 4 * eta < sigma)
    (hC : C ≠ ⊤)
    (hCpower : C ≤ Kakeya.realRpowENN rho (-eta))
    (hPlanarSmall : 32 * Real.rpow rho eta ≤ 1)
    (hrootSmall : 12 * Real.sqrt rho ≤ 1)
    (habsorb :
      Real.rpow rho (1 - 4 * eta / sigma) ≤
        Real.sqrt rho / 10)
    (input :
      WZ1Lemma23FullLocalGrainInput
        rho sigma eta C slope) :
    1 / 4 ≤ |input.normal (0 : Fin 3)| := by
  rcases
      wz1_lemma23_normal_tilt_witness_from_full_grain
        hPlanar rho sigma eta C slope
        hrho hrho_one heta hPlanarSmall hrootSmall input with
    ⟨z, hz, htiltRoot⟩ | ⟨witness, hwitnessHeight⟩
  · have hrootTenth : Real.sqrt rho ≤ 1 / 10 := by
      linarith [hrootSmall]
    have htilt :
        |input.normal 1 - slope z * input.normal 0| ≤
          1 / 10 :=
      htiltRoot.trans hrootTenth
    exact wz1_lemma23_normal_first_component
      input.normal (slope z)
      input.normal_unit input.normal_vertical
      (input.slope_small z hz) htilt
  · exact
      wz1_lemma23_normal_first_component_from_tilt
        wz1_lemma23_normal_tilt
        rho sigma eta C slope input.normal
        hrho hrho_one hsigma hsigma_one
        heta heta_sigma hC hCpower habsorb witness

/--
The full-grain normal bound for source slopes bounded by `3`.  The small-tilt
branch uses `hrootSmall20`; the fullness branch uses the generalized witness
and the tightened `1 / 14` absorption.
-/
theorem wz1_lemma23_full_grain_normal_first_component_generalized_of_fubini
    (rho sigma eta : ℝ) (C : ENNReal)
    (slope : ℝ → ℝ)
    (hrho : 0 < rho) (hrho_one : rho ≤ 1)
    (hsigma : 0 < sigma) (hsigma_one : sigma < 1)
    (heta : 0 < eta) (heta_sigma : 4 * eta < sigma)
    (hC : C ≠ ⊤)
    (hCpower : C ≤ Kakeya.realRpowENN rho (-eta))
    (hPlanarSmall : 32 * Real.rpow rho eta ≤ 1)
    (hrootSmall20 : 20 * Real.sqrt rho ≤ 1)
    (habsorb :
      Real.rpow rho (1 - 4 * eta / sigma) ≤
        Real.sqrt rho / 14)
    (input : WZ1Lemma23FullLocalGrainGeometryGeneralized rho eta slope)
    (hglobalAt :
      ∀ z (_hz : z ∈ Set.Ico input.heightLeft
          (input.heightLeft + Real.sqrt rho)),
        Kakeya.realRpowENN rho (3 / 2 + 2 * eta) ≤
            MeasureTheory.volume (wz1Lemma23PlanarSlice input.grain z) →
        ∃ projected : Set ℝ,
          IsADSet1 projected rho (1 - sigma) C ∧
          (fun point : Point2 => point 0 + slope z * point 1) ''
              wz1Lemma23PlanarSlice input.grain z ⊆ projected) :
    1 / 4 ≤ |input.normal (0 : Fin 3)| := by
  rcases
      wz1_lemma23_normal_tilt_witness_from_full_grain_generalized_of_fubini
        rho sigma eta C slope
        hrho hrho_one heta hPlanarSmall hrootSmall20 input hglobalAt with
    ⟨z, hz, htiltRoot⟩ | ⟨witness, hwitnessHeight⟩
  · have hrootFourteenth : Real.sqrt rho ≤ 1 / 14 := by
      linarith [hrootSmall20]
    have htilt :
        |input.normal 1 - slope z * input.normal 0| ≤
          1 / 14 :=
      htiltRoot.trans hrootFourteenth
    exact wz1_lemma23_normal_first_component_generalized
      input.normal (slope z)
      input.normal_unit input.normal_vertical
      (input.slope_small z hz) htilt
  · exact
      wz1_lemma23_normal_first_component_from_tilt_generalized
        wz1_lemma23_normal_tilt_generalized
        rho sigma eta C slope input.normal
        hrho hrho_one hsigma hsigma_one
        heta heta_sigma hC hCpower habsorb witness

/-- Compatibility form deriving the selected-height callback from the former
all-window global fields. -/
theorem wz1_lemma23_full_grain_normal_first_component_generalized
    (rho sigma eta : ℝ) (C : ENNReal)
    (slope : ℝ → ℝ)
    (hrho : 0 < rho) (hrho_one : rho ≤ 1)
    (hsigma : 0 < sigma) (hsigma_one : sigma < 1)
    (heta : 0 < eta) (heta_sigma : 4 * eta < sigma)
    (hC : C ≠ ⊤)
    (hCpower : C ≤ Kakeya.realRpowENN rho (-eta))
    (hPlanarSmall : 32 * Real.rpow rho eta ≤ 1)
    (hrootSmall20 : 20 * Real.sqrt rho ≤ 1)
    (habsorb :
      Real.rpow rho (1 - 4 * eta / sigma) ≤
        Real.sqrt rho / 14)
    (input :
      WZ1Lemma23FullLocalGrainInputGeneralized
        rho sigma eta C slope) :
    1 / 4 ≤ |input.normal (0 : Fin 3)| := by
  exact wz1_lemma23_full_grain_normal_first_component_generalized_of_fubini
    rho sigma eta C slope hrho hrho_one hsigma hsigma_one heta heta_sigma
    hC hCpower hPlanarSmall hrootSmall20 habsorb input.toGeometry
    (fun z hz _hslice =>
      ⟨input.projected z, input.globalAD z hz,
        input.global_projection_sub z hz⟩)

/-- Every generalized full grain has one height in its own window where the
normal is quantitatively aligned with the global-grain slope. -/
theorem wz1_lemma23_full_grain_normal_tilt_exists_generalized
    (rho sigma eta : ℝ) (C : ENNReal)
    (slope : ℝ → ℝ)
    (hrho : 0 < rho) (hrho_one : rho ≤ 1)
    (hsigma : 0 < sigma) (hsigma_one : sigma < 1)
    (heta : 0 < eta) (heta_sigma : 4 * eta < sigma)
    (hC : C ≠ ⊤)
    (hCpower : C ≤ Kakeya.realRpowENN rho (-eta))
    (hPlanarSmall : 32 * Real.rpow rho eta ≤ 1)
    (hrootSmall20 : 20 * Real.sqrt rho ≤ 1)
    (habsorb :
      Real.rpow rho (1 - 4 * eta / sigma) ≤
        Real.sqrt rho / 14)
    (input :
      WZ1Lemma23FullLocalGrainInputGeneralized
        rho sigma eta C slope) :
    ∃ z ∈ Set.Ico input.heightLeft
        (input.heightLeft + Real.sqrt rho),
      |input.normal 1 - slope z * input.normal 0| ≤ 1 / 14 := by
  rcases
      wz1_lemma23_normal_tilt_witness_from_full_grain_generalized
        rho sigma eta C slope
        hrho hrho_one heta hPlanarSmall hrootSmall20 input with
    ⟨z, hz, htiltRoot⟩ | ⟨witness, hwitnessHeight⟩
  · refine ⟨z, hz, htiltRoot.trans ?_⟩
    have hrootFourteenth : Real.sqrt rho ≤ 1 / 14 := by
      linarith [hrootSmall20]
    exact hrootFourteenth
  · refine ⟨witness.sliceHeight, hwitnessHeight, ?_⟩
    exact (wz1_lemma23_normal_tilt_generalized
      rho sigma eta C slope input.normal
      hrho hrho_one hsigma hsigma_one
      heta heta_sigma hC hCpower habsorb witness).2

end

end Kakeya.Assouad
