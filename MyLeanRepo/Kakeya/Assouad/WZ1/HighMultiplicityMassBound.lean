import MyLeanRepo.Kakeya.Assouad.MultiplicityPigeonholing
import MyLeanRepo.Kakeya.Assouad.Definitions
import Mathlib.Tactic

/-!
# High-multiplicity set mass bound

If the point multiplicity of a shading is bounded above by M on a measurable set S,
then the shaded mass restricted to S is at most M * volume(S).

This is used in the fine multiplicity refinement to show that low-multiplicity
regions cannot carry too much mass, so a high-multiplicity dyadic band must
capture most of the shaded mass.
-/

noncomputable section

open MeasureTheory Set Finset

namespace Kakeya.Assouad

/--
**Low-multiplicity mass bound.**

If `Y.pointMultiplicity p ≤ M` for all `p ∈ S`, then the total shaded mass
inside `S` is at most `M * volume S`.

The shaded mass inside S is `∑ i, volume(Y.carrier i ∩ S)`, which equals
`∫⁻ p in S, Y.pointMultiplicity p` by the Fubini identity.
-/
lemma low_multiplicity_mass_bound
    {δ : ℝ} {F : Kakeya.Streamlined.TubeFamily δ}
    (Y : Kakeya.Streamlined.TubeShading F)
    (S : Set Point3) (hS : MeasurableSet S)
    (M : ENNReal)
    (hM : ∀ p ∈ S, (Y.pointMultiplicity p : ENNReal) ≤ M) :
    ∑ i : Fin F.toBodyFamily.card, volume (Y.carrier i ∩ S) ≤ M * volume S := by
  have h_eq : ∑ i : Fin F.toBodyFamily.card, volume (Y.carrier i ∩ S) =
      ∫⁻ p in S, (Y.pointMultiplicity p : ENNReal) :=
    sum_volume_inter_eq_setLIntegral_pointMultiplicity Y hS
  rw [h_eq]
  have h_le : ∫⁻ p in S, (Y.pointMultiplicity p : ENNReal) ≤ ∫⁻ p in S, M := by
    exact setLIntegral_mono' hS hM
  rw [setLIntegral_const] at h_le
  exact h_le

/--
**High-multiplicity tail carries most of the mass.**

Let `H = {p ∈ Y.union | Y.pointMultiplicity p ≥ M}`. If
`Y.mass > 2 * M * volume(Y.union)`, then the mass of `Y.union \ H` is at most
`M * volume(Y.union)`, so the mass of `H` is at least `Y.mass - M * volume(Y.union)`.

This is a direct consequence of `low_multiplicity_mass_bound`.
-/
lemma high_multiplicity_mass_lower
    {δ : ℝ} {F : Kakeya.Streamlined.TubeFamily δ}
    (Y : Kakeya.Streamlined.TubeShading F)
    (M : ENNReal)
    (H : Set Point3)
    (hH : MeasurableSet H)
    (hH_def : H = {p ∈ Y.union | (Y.pointMultiplicity p : ENNReal) ≥ M}) :
    ∑ i : Fin F.toBodyFamily.card, volume (Y.carrier i ∩ (Y.union \ H)) ≤
      M * volume (Y.union \ H) := by
  have hS : MeasurableSet (Y.union \ H) :=
    (measurableSet_shading_union Y).diff hH
  have hM : ∀ p ∈ (Y.union \ H), (Y.pointMultiplicity p : ENNReal) ≤ M := by
    intro p hp
    have hp_union : p ∈ Y.union := hp.1
    have hp_not_H : p ∉ H := hp.2
    have h_in_union : p ∈ Y.union := hp_union
    have h_not_ge : ¬(M ≤ (Y.pointMultiplicity p : ENNReal)) := by
      intro hge
      rw [hH_def] at hp_not_H
      have h3 : p ∈ {p : Point3 | p ∈ Y.union ∧ M ≤ (Y.pointMultiplicity p : ENNReal)} := by
        simpa using ⟨hp_union, hge⟩
      exact hp_not_H h3
    exact le_of_not_ge h_not_ge
  exact low_multiplicity_mass_bound Y (Y.union \ H) hS M hM

/--
**Log loss absorption for dyadic pigeonholing.**

If `K + 1 ≤ δ^(eta - epsilon)` (i.e., the number of dyadic bands is polynomial
in δ with exponent `eta - epsilon`), then a band capturing at least
`Y.mass / (K + 1)` of the mass also satisfies the density bound with
exponent `epsilon`, given that `Y` was `eta`-dense.

This wraps `band_mass_density_absorption` for the common case.
-/
lemma dyadic_log_loss_absorption
    {δ : ℝ} {F : Kakeya.Streamlined.TubeFamily δ}
    (Y : Kakeya.Streamlined.TubeShading F)
    (eta epsilon : ℝ) (hδ : 0 < δ) (_hδ_one : δ ≤ 1)
    (heta : 0 < eta) (heta' : eta < epsilon)
    (hY_dense : Y.IsLambdaDense (Kakeya.realRpowENN δ eta))
    (bandMass : ENNReal) (K : ℕ)
    (hband : ((K + 1 : ℕ) : ENNReal) * bandMass ≥ Y.mass)
    (hK : (K + 1 : ℕ) ≤ Kakeya.realRpowENN δ (eta - epsilon)) :
    bandMass ≥ Kakeya.realRpowENN δ epsilon * F.toBodyFamily.mass := by
  exact band_mass_density_absorption Y eta epsilon hδ heta heta' hY_dense
    bandMass ((K + 1 : ℕ) : ENNReal) hband hK

end Kakeya.Assouad
