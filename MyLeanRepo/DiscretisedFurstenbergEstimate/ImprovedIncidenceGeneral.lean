module

/-
  Improved Incidence for General (δ,t)-sets.

  Provides:
  1. `improved_incidence_correct_Ncover`: general version via Section 9 assembly
     + Theorem 6.1 uniform data contract.
  2. `improved_incidence_correct_from_Ncover`: Ncover → encard bridge.

  The general version uses `section9_main` from `Section9.Section9Assembly`,
  which consumes `UniformIncidenceData` supplied by the `theorem6_1_uniform_data`
  contract axiom.

  Whiteprint node: improved_incidence_general
  Dependencies: Section9.NcoverAdapter
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.Base
public import MyLeanRepo.DiscretisedFurstenbergEstimate.Section9.NcoverAdapter
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

noncomputable section

attribute [local instance] Classical.propDecidable

namespace DirecretisedFurstenbergEstimate.ImprovedIncidenceGeneral

open DirecretisedFurstenbergEstimate

/-- δ-covering number abbreviation. -/
abbrev Ncover {X : Type*} [PseudoMetricSpace X] (δ : ℝ) (E : Set X) : ENNReal :=
  Metric.externalCoveringNumber δ.toNNReal E

/-! ========================================================================
   Bridge: Ncover lower bound → encard lower bound

   Since singletons are δ-balls, `Ncover δ T ≤ T.encard` always.
   ======================================================================== -/

/-- A lower bound on the δ-covering number implies the same lower bound on
    the extended cardinality. -/
lemma ncover_lower_to_encard {δ : ℝ} {T : Set AffineLine} {C : ℝ} (hC_pos : 0 < C)
    (h : ENNReal.ofReal C ≤ Ncover δ T) :
    ENNReal.ofReal C ≤ (T.encard : ENNReal) := by
  have h1 : (Ncover δ T : ENNReal) ≤ (T.encard : ENNReal) := by
    exact_mod_cast Metric.externalCoveringNumber_le_encard_self (ε := δ.toNNReal) T
  exact le_trans h h1

/-! ========================================================================
   General improved incidence (Ncover version)

   For general (δ,t)-sets. Proved via section9_main + Theorem 6.1 uniform data.
   ======================================================================== -/

/--
  Improved incidence for general (δ,t)-sets, Ncover version.

  Uses the Section 9 assembly (`section9_main`) with uniform incidence data
  from the Theorem 6.1 contract (`theorem6_1_uniform_data`).
-/
theorem improved_incidence_correct_Ncover
    (s t : ℝ)
    (hs : 0 < s) (hs1 : s < 1) (hst : s < t) (ht2 : t < 2) :
    ∃ (ε_G η : ℝ), 0 < ε_G ∧ 0 < η ∧
      ∃ (δ₀ : ℝ), 0 < δ₀ ∧
        ∀ (δ : ℝ), 0 < δ → δ ≤ δ₀ →
          ∀ (P : Set EuclideanPlane),
            P ⊆ Metric.closedBall 0 1 →
            IsDeltaSSet δ t (Real.rpow δ (-ε_G)) P →
            ∀ (T : Set AffineLine)
              (Tp : ∀ (p : EuclideanPlane), p ∈ P → Set AffineLine),
              (∀ p hp, Tp p hp ⊆ T) →
              (∀ p hp, IsDeltaSSet δ s (Real.rpow δ (-ε_G)) (Tp p hp)) →
              (∀ p hp, ∀ ℓ ∈ Tp p hp, p ∈ Metric.cthickening δ ℓ.1) →
              Ncover δ T ≥
                ENNReal.ofReal (Real.rpow δ (-(2 * s + ε_G))) :=
  improved_incidence_correct_Ncover_adapter s t hs hs1 hst ht2

/-! ========================================================================
   Target theorem: improved_incidence_correct

   From Ncover version to encard version using `ncover_lower_to_encard`.
   ======================================================================== -/

/--
  Improved incidence for general (δ,t)-sets, encard version.

  This is the target theorem in FinalProof.lean. Once
  `improved_incidence_correct_Ncover` is proved, this follows by the
  Ncover → encard bridge.
-/
theorem improved_incidence_correct_from_Ncover
    (s t : ℝ)
    (hs : 0 < s) (hs1 : s < 1) (hst : s < t) (ht2 : t < 2)
    (h_main : ∃ (ε_G η : ℝ), 0 < ε_G ∧ 0 < η ∧
      ∃ (δ₀ : ℝ), 0 < δ₀ ∧
        ∀ (δ : ℝ), 0 < δ → δ ≤ δ₀ →
          ∀ (P : Set EuclideanPlane),
            P ⊆ Metric.closedBall 0 1 →
            IsDeltaSSet δ t (Real.rpow δ (-ε_G)) P →
            ∀ (T : Set AffineLine)
              (Tp : ∀ (p : EuclideanPlane), p ∈ P → Set AffineLine),
              (∀ p hp, Tp p hp ⊆ T) →
              (∀ p hp, IsDeltaSSet δ s (Real.rpow δ (-ε_G)) (Tp p hp)) →
              (∀ p hp, ∀ ℓ ∈ Tp p hp, p ∈ Metric.cthickening δ ℓ.1) →
              Ncover δ T ≥
                ENNReal.ofReal (Real.rpow δ (-(2 * s + ε_G)))) :
    ∃ (ε_G η : ℝ), 0 < ε_G ∧ 0 < η ∧
      ∃ (δ₀ : ℝ), 0 < δ₀ ∧
        ∀ (δ : ℝ), 0 < δ → δ ≤ δ₀ →
          ∀ (P : Set EuclideanPlane),
            P ⊆ Metric.closedBall 0 1 →
            IsDeltaSSet δ t (Real.rpow δ (-ε_G)) P →
            ∀ (T : Set AffineLine)
              (Tp : ∀ (p : EuclideanPlane), p ∈ P → Set AffineLine),
              (∀ p hp, Tp p hp ⊆ T) →
              (∀ p hp, IsDeltaSSet δ s (Real.rpow δ (-ε_G)) (Tp p hp)) →
              (∀ p hp, ∀ ℓ ∈ Tp p hp, p ∈ Metric.cthickening δ ℓ.1) →
              (T.encard : ENNReal) ≥
                ENNReal.ofReal (Real.rpow δ (-(2 * s + ε_G))) := by
  rcases h_main with ⟨ε_G, η, hεG_pos, hη_pos, δ₀, hδ₀_pos, h_imp⟩
  refine' ⟨ε_G, η, hεG_pos, hη_pos, δ₀, hδ₀_pos, _⟩
  intro δ hδ_pos hδ_le P hP_bdd hP_sset T Tp hTp_sub hTp_sset hTp_near
  have h_ncover : Ncover δ T ≥
      ENNReal.ofReal (Real.rpow δ (-(2 * s + ε_G))) :=
    h_imp δ hδ_pos hδ_le P hP_bdd hP_sset T Tp hTp_sub hTp_sset hTp_near
  have hC_pos : 0 < Real.rpow δ (-(2 * s + ε_G)) :=
    Real.rpow_pos_of_pos hδ_pos _
  exact ncover_lower_to_encard hC_pos h_ncover

end DirecretisedFurstenbergEstimate.ImprovedIncidenceGeneral
