import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.TubeParameterGridOSInitialStateStatements
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.TubeParameterGridOSStateTransitionStatements

/-!
# Effective loss schedule for the corrected finite grid OS iteration

The signed one-scale theorem at effective loss `eta k` outputs density
`scale ^ (4 * eta k)`.  One corrected transition then:

* loses the fixed density factor `1 / 1600`;
* multiplies the parameter Frostman constant by `8`.

In the nonterminal branch `rho < delta ^ (epsilon ^ 2)`.  Taking

`eta (k + 1) = (10 / epsilon ^ 2) * eta k`

leaves a strict power gap that absorbs both fixed constants uniformly for
sufficiently small initial `delta`.

The initial terminal-grid preparation has source loss one quarter of
`eta 0`.  Its density and inverse-cardinality losses are absorbed by the same
small-scale threshold.
-/

noncomputable section

namespace Kakeya.Assouad

/-- One finite effective-loss schedule and all of its numerical certificates. -/
structure GridOSEffectiveLossScheduleData
    (epsilon etaMax : ℝ)
    (steps : ℕ) where
  sourceEta : ℝ
  eta : ℕ → ℝ
  sourceEta_pos : 0 < sourceEta
  eta_formula :
    ∀ index : ℕ,
      eta index =
        4 * sourceEta *
          Real.rpow (10 / epsilon ^ 2) index
  eta_pos :
    ∀ index : ℕ, index ≤ steps → 0 < eta index
  eta_le :
    ∀ index : ℕ, index ≤ steps → eta index ≤ etaMax
  delta₀ : ℝ
  delta₀_pos : 0 < delta₀
  delta₀_lt_one : delta₀ < 1
  initial_density_ready :
    ∀ delta : ℝ,
      0 < delta →
      delta ≤ delta₀ →
        Kakeya.realRpowENN delta (eta 0 / 2) ≤
          terminalCellInitialDensity delta sourceEta
  initial_parameter_ready :
    ∀ delta : ℝ,
      0 < delta →
      delta ≤ delta₀ →
        (2 : ENNReal) *
            Kakeya.realRpowENN delta (-3 * sourceEta) ≤
          Kakeya.realRpowENN delta (-eta 0)
  transition_density_ready :
    ∀ delta : ℝ,
      0 < delta →
      delta ≤ delta₀ →
      ∀ index : ℕ,
        index < steps →
        ∀ scale rho : ℝ,
          delta ≤ scale →
          scale ≤ 1 →
          0 < rho →
          rho < Real.rpow delta (epsilon ^ 2) →
            Kakeya.realRpowENN rho (eta (index + 1) / 2) ≤
              gridOSNextDensity
                (Kakeya.realRpowENN scale (4 * eta index))
  transition_parameter_ready :
    ∀ delta : ℝ,
      0 < delta →
      delta ≤ delta₀ →
      ∀ index : ℕ,
        index < steps →
        ∀ scale rho : ℝ,
          delta ≤ scale →
          scale ≤ 1 →
          0 < rho →
          rho < Real.rpow delta (epsilon ^ 2) →
            (8 : ENNReal) *
                Kakeya.realRpowENN scale (-eta index) ≤
              Kakeya.realRpowENN rho (-eta (index + 1))

/--
For every finite iteration length, choose a positive source loss and a
geometrically growing effective-loss schedule that stays below the one-scale
admissible ceiling.
-/
def GridOSEffectiveLossScheduleStatement : Prop :=
  ∀ epsilon etaMax : ℝ,
    0 < epsilon →
    epsilon < 1 →
    0 < etaMax →
      ∀ steps : ℕ,
        Nonempty
          (GridOSEffectiveLossScheduleData epsilon etaMax steps)

end Kakeya.Assouad
