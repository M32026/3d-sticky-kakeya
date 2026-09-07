import MyLeanRepo.Kakeya.Assouad.Subunit.HairbrushSelfContainedLeaves
import MyLeanRepo.Kakeya.Assouad.HairbrushBalancedBroadDecomposition.AdditiveVolumeFromMultiplicity

/-!
# Ambient multiplicity incidence identity

This is the lower side of Wang--Zahl Appendix-B equation (B.13): the layer
mass lower bound and its pointwise multiplicity upper bound imply a lower
bound for `mu * volume(layer.union)`.
-/

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

theorem hairbrush_ambient_incidence :
    HairbrushAmbientIncidenceStatement := by
  intro δ inputExponent layerLoss hairLoss hδ F Y core hvol
  have hC : ∀ x, shadedMultiplicity' core.layer x ≤ 2 * core.mu := by
    intro x
    by_cases hx : x ∈ core.layer.union
    · exact (core.multiplicity_upper x hx).le
    · have h_empty : F.filter (fun T => x ∈ core.layer.carrier T) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro T hT hXT
        exact hx ⟨T, hT, hXT⟩
      have h_zero : shadedMultiplicity' core.layer x = 0 := by
        simp only [shadedMultiplicity', h_empty, Finset.card_empty]
      rw [h_zero]
      positivity
  have h_mass_upper : core.layer.mass ≤ (2 * (core.mu : ENNReal)) * volume core.layer.union := by
    have h := mass_le_C_mul_volume' core.layer (2 * core.mu) hC
    simpa [mul_comm] using h
  have h1 : core.layerDensity * F.enncard * ENNReal.ofReal (δ ^ 2) ≤
      core.layerDensity * F.enncard * Kakeya.deltaTubeVolume δ := by
    gcongr
  calc core.layerDensity * F.enncard * ENNReal.ofReal (δ ^ 2)
    ≤ core.layerDensity * F.enncard * Kakeya.deltaTubeVolume δ := h1
  _ ≤ core.layer.mass := core.layer_mass_lower
  _ ≤ (2 * (core.mu : ENNReal)) * volume core.layer.union := h_mass_upper

end Kakeya.Assouad
