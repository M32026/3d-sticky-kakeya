import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains
import MyLeanRepo.Kakeya.Assouad.Definitions

/-!
# Faithful Step-4 witness

This is the minimal certificate consumed by the convex-overload argument.
It records genuine fixed-frame x'z prisms and a card-proportional total mass
lower bound; it contains none of the historical Path-C y-grid fields.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

structure LargeSlopeFaithfulStep4Witness
    {delta : ℝ}
    (F : Kakeya.Streamlined.TubeFamily delta)
    (sigma eta a b : ℝ) where
  rho : ℝ
  rho_eq : rho = 64 * (b - a) ^ 2
  rho_pos : 0 < rho
  delta_le_rho : delta ≤ rho
  six_delta_le_rho : 6 * delta ≤ rho
  rho_le_quarter : rho ≤ 1 / 4
  sqrt_rho_eq : Real.sqrt rho = 8 * (b - a)
  fine : WZ1PaperTubeShading F
  prismCount : ℕ
  prismCount_pos : 0 < prismCount
  prism : Fin prismCount → Set Point3
  prismNormal : Fin prismCount → Point3
  prismNormal_unit : ∀ j, ‖prismNormal j‖ = 1
  prismCenter : Fin prismCount → Point3
  prism_transverse :
    ∀ j, prism j ⊆
      {point | |inner ℝ (point - prismCenter j) (prismNormal j)| ≤
        Real.sqrt rho}
  segmentStart : Fin F.card → Fin prismCount → ℝ
  piece : Fin F.card → Fin prismCount → Set Point3
  piece_measurable : ∀ i j, MeasurableSet (piece i j)
  piece_sub_fine : ∀ i j, piece i j ⊆ fine.carrier i
  piece_sub_prism : ∀ i j, piece i j ⊆ prism j
  piece_sub_segment :
    ∀ i j, piece i j ⊆
      tubeSegmentCarrier (6 * delta) (F.tube i).base (F.tube i).direction
        (segmentStart i j) rho
  total_piece_mass :
    ENNReal.ofReal
        (36 * Real.rpow delta (12 * eta) * delta ^ 2 *
          Real.sqrt rho) * F.enncard ≤
      ∑ i : Fin F.card, ∑ j : Fin prismCount, volume (piece i j)
  piece_mass_lower :
    ∀ i j, volume (piece i j) ≠ 0 →
      ENNReal.ofReal
          (36 * Real.rpow delta (12 * eta) * delta ^ 2 *
            Real.sqrt rho) ≤ volume (piece i j)
  piece_mass_upper :
    ∀ i j, volume (piece i j) ≤
      ENNReal.ofReal (4000 * Real.sqrt rho * delta ^ 2)
  piece_local_ad :
    ∀ i j, volume (piece i j) ≠ 0 →
      IsADSet1 (scalarProjection (prismNormal j) (piece i j))
        rho (1 - sigma) (Kakeya.realRpowENN delta (-(12 * eta)))
  prism_card_upper :
    (prismCount : ENNReal) ≤
      Kakeya.realRpowENN delta (-(12 * eta)) *
        Kakeya.realRpowENN rho ((-1 + sigma) / 2)

end Kakeya.Assouad

end
