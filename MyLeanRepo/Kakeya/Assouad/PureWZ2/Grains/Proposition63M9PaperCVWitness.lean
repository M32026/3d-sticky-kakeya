import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.PaperCV
import MyLeanRepo.Kakeya.Assouad.ConstantAbsorption

/-!
# Proposition 6.3 M9: pre-runtime paper CV witness

This low-dependency module freezes the universal paper CV constant and its
normalization-power envelope before any runtime scale or family is known.
It deliberately does not import the dense-root or pre-runtime M9 hierarchy,
so loss schedules may store the witness without creating an import cycle.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory Set

/-- One universal paper CV constant, fixed before any runtime scale or family. -/
structure Proposition63M9PaperCVConstantWitness where
  constant : ENNReal
  constant_ne_top : constant ≠ ⊤
  broad_set_estimate :
    ∀ (delta : ℝ), 0 < delta → delta ≤ 1 →
      ∀ (F : Kakeya.Streamlined.TubeFamily delta),
        ∀ (Y : WZ1PaperTubeShading F),
          ∀ (E : Set Point3) (L : ENNReal),
            MeasurableSet E →
            (∀ point ∈ E, L ≤
              (paperShadingTrilinearMultiplicity Y point) ^
                (1 / 2 : ℝ)) →
            L * volume E ≤
              constant *
                (ENNReal.ofReal (delta ^ 2) * F.enncard) ^
                  (3 / 2 : ℝ)

/-- The completed paper CV theorem supplies a witness independent of every
runtime scale and tube family. -/
theorem proposition63_m9_paperCVConstantWitness_exists :
    Nonempty Proposition63M9PaperCVConstantWitness := by
  rcases paper_cv_broad_set_estimate with
    ⟨constant, constant_ne_top, estimate⟩
  exact ⟨{
    constant := constant
    constant_ne_top := constant_ne_top
    broad_set_estimate := estimate }⟩

/-- A cutoff, chosen after the normalization loss but before the runtime scale,
which absorbs a fixed paper CV constant into the normalization power. -/
structure Proposition63M9NormalizationPowerEnvelope
    (cv : Proposition63M9PaperCVConstantWitness)
    (normalizationLoss : ℝ) where
  cutoff : ℝ
  cutoff_pos : 0 < cutoff
  cutoff_le_one : cutoff ≤ 1
  constant_le_power :
    ∀ delta : ℝ, 0 < delta → delta ≤ cutoff →
      cv.constant ≤ Kakeya.realRpowENN delta (-normalizationLoss)

/-- Every positive normalization loss admits a pre-runtime power envelope for
the already fixed CV witness. -/
theorem Proposition63M9PaperCVConstantWitness.exists_normalizationPowerEnvelope
    (cv : Proposition63M9PaperCVConstantWitness)
    {normalizationLoss : ℝ} (normalizationLoss_pos : 0 < normalizationLoss) :
    Nonempty (Proposition63M9NormalizationPowerEnvelope cv normalizationLoss) := by
  rcases exists_delta_realRpowENN_bound cv.constant cv.constant_ne_top
      normalizationLoss_pos with
    ⟨cutoff, cutoff_pos, cutoff_le_one, bound⟩
  exact ⟨{
    cutoff := cutoff
    cutoff_pos := cutoff_pos
    cutoff_le_one := cutoff_le_one
    constant_le_power := bound }⟩

/-- Explicit quantifier-order interface: choose the CV witness first, then for
each positive normalization loss choose its cutoff. -/
theorem proposition63_m9_fixedCV_then_normalizationEnvelope :
    ∃ cv : Proposition63M9PaperCVConstantWitness,
      ∀ normalizationLoss : ℝ, 0 < normalizationLoss →
        Nonempty
          (Proposition63M9NormalizationPowerEnvelope cv normalizationLoss) := by
  rcases proposition63_m9_paperCVConstantWitness_exists with ⟨cv⟩
  exact ⟨cv, fun _ normalizationLoss_pos =>
    cv.exists_normalizationPowerEnvelope normalizationLoss_pos⟩

end Kakeya.Assouad.PureWZ2

end
