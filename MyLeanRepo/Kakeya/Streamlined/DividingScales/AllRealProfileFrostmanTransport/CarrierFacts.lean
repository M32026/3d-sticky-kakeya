import MyLeanRepo.Kakeya.Streamlined.DilatedTubeCover.FullContainmentFibers
import MyLeanRepo.Kakeya.Streamlined.ProfileUniformRefinement.GeometricFullContainmentFibers
import MyLeanRepo.Kakeya.Streamlined.DividingScales.ReferenceDensity
import MyLeanRepo.Kakeya.Streamlined.DividingScales.ConvexThickeningGrowth
import MyLeanRepo.Kakeya.Streamlined.ProfileUniformRefinement.FactorLocalTwoProfileCommonSelection
import MyLeanRepo.Kakeya.Streamlined.DividingScales.RefinedLemmaSevenSevenStatement

/-!
# Carrier and fiber positivity facts for Frostman transport

This module packages the standard positivity/non-top/convexity conditions needed
by `frostmanComparable_of_deltaMax_density`, the `deltaMax = frostman * density`
identity, and the two-direction finite-union transport.

Results are generic in the dilation `A` with `1 ≤ A`, and also specialized
to `A = refinedLemmaSevenSevenCoverDilation` (= 1000).
-/

noncomputable section

namespace Kakeya.Streamlined

open MeasureTheory

namespace DilatedTubeCover

/-- Carrier volume is positive for any coarse parent. -/
lemma fullContainmentFiberCarrier_volume_pos
    {A delta rho : ℝ} {fine : TubeFamily delta} {coarse : TubeFamily rho}
    (P : DilatedTubeCover A fine coarse)
    (hA : 1 ≤ A) (hrho : 0 < rho) (j : Fin coarse.card) :
    0 < volume (dilatedTubeCarrier A (coarse.tube j)) :=
  GeometricLemmas.dilatedTubeCarrier_volume_pos hrho hA (coarse.tube j)

/-- Carrier volume is finite for any coarse parent. -/
lemma fullContainmentFiberCarrier_volume_ne_top
    {A delta rho : ℝ} {fine : TubeFamily delta} {coarse : TubeFamily rho}
    (P : DilatedTubeCover A fine coarse)
    (hA : 1 ≤ A) (hrho : 0 < rho) (j : Fin coarse.card) :
    volume (dilatedTubeCarrier A (coarse.tube j)) ≠ ⊤ :=
  GeometricLemmas.dilatedTubeCarrier_volume_ne_top hrho hA (coarse.tube j)

/-- Carrier is convex for any coarse parent. -/
lemma fullContainmentFiberCarrier_convex
    {A delta rho : ℝ} {fine : TubeFamily delta} {coarse : TubeFamily rho}
    (P : DilatedTubeCover A fine coarse)
    (j : Fin coarse.card) :
    Convex ℝ (dilatedTubeCarrier A (coarse.tube j)) :=
  GeometricLemmas.dilatedTubeCarrier_convex (coarse.tube j)

/-- All parents of one coarse family have equal carrier volume. -/
lemma fullContainmentFiberCarrier_volume_eq
    {A delta rho : ℝ} {fine : TubeFamily delta} {coarse : TubeFamily rho}
    (P : DilatedTubeCover A fine coarse)
    (hA_ne_zero : A ≠ 0)
    (j k : Fin coarse.card) :
    volume (dilatedTubeCarrier A (coarse.tube j)) =
      volume (dilatedTubeCarrier A (coarse.tube k)) :=
  volume_dilatedTubeCarrier_eq hA_ne_zero (coarse.tube j) (coarse.tube k)

/-- The full-containment fiber subfamily is nonempty. -/
lemma fullContainmentFiberSubfamily_nonempty
    {A delta rho : ℝ} {fine : TubeFamily delta} {coarse : TubeFamily rho}
    (P : DilatedTubeCover A fine coarse)
    (j : Fin coarse.card) :
    (P.fullContainmentFiberSubfamily j).family.Nonempty := by
  dsimp only [TubeFamily.Nonempty]
  exact (P.fullContainmentFiberIndices_nonempty j).card_pos

/-- Mass of a full-containment fiber is positive and finite. -/
lemma fullContainmentFiberMass_pos_and_top
    {A delta rho : ℝ} {fine : TubeFamily delta} {coarse : TubeFamily rho}
    (P : DilatedTubeCover A fine coarse)
    (hdelta : 0 < delta) (j : Fin coarse.card) :
    0 < (P.fullContainmentFiberSubfamily j).family.toBodyFamily.mass ∧
      (P.fullContainmentFiberSubfamily j).family.toBodyFamily.mass ≠ ⊤ := by
  let G := (P.fullContainmentFiberSubfamily j).family
  have hG_nonempty : G.Nonempty := P.fullContainmentFiberSubfamily_nonempty j
  have hvol_pos : 0 < Kakeya.deltaTubeVolume delta :=
    RandomTranslation.deltaTubeVolume_pos hdelta
  have hvol_top : Kakeya.deltaTubeVolume delta ≠ ⊤ :=
    RandomTranslation.deltaTubeVolume_ne_top
  have hcard_pos : 0 < (G.card : ENNReal) := by exact_mod_cast hG_nonempty
  have h_mass_eq : G.toBodyFamily.mass =
      (G.card : ENNReal) * Kakeya.deltaTubeVolume delta := by
    have h1 : ∀ i, (G.toBodyFamily.body i).volume = Kakeya.deltaTubeVolume delta :=
      fun i => RandomTranslation.tube_volume_eq_deltaTubeVolume (G.tube i)
    calc
      G.toBodyFamily.mass
        = ∑ i : Fin G.card, (G.toBodyFamily.body i).volume := by rfl
      _ = ∑ i : Fin G.card, Kakeya.deltaTubeVolume delta := by
          apply Finset.sum_congr rfl; intro i _; exact h1 i
      _ = (G.card : ENNReal) * Kakeya.deltaTubeVolume delta := by
          simp [Finset.sum_const, nsmul_eq_mul]
  rw [h_mass_eq]
  exact ⟨ENNReal.mul_pos hcard_pos.ne' hvol_pos.ne',
    ENNReal.mul_ne_top (by simp) hvol_top⟩

/-- Every tube in a full-containment fiber lies in its carrier. -/
lemma fullContainmentFiber_all_contained
    {A delta rho : ℝ} {fine : TubeFamily delta} {coarse : TubeFamily rho}
    (P : DilatedTubeCover A fine coarse)
    (j : Fin coarse.card) :
    ∀ i : Fin (P.fullContainmentFiberSubfamily j).family.card,
      ((P.fullContainmentFiberSubfamily j).family.tube i).carrier ⊆
        dilatedTubeCarrier A (coarse.tube j) :=
  P.fullContainmentFiberSubfamily_all_contained j

/-- The contained mass of a fiber in its carrier equals the fiber mass. -/
lemma fullContainmentFiberContainedMass_eq_mass
    {A delta rho : ℝ} {fine : TubeFamily delta} {coarse : TubeFamily rho}
    (P : DilatedTubeCover A fine coarse)
    (j : Fin coarse.card) :
    (P.fullContainmentFiberSubfamily j).family.toBodyFamily.containedMass
        (dilatedTubeCarrier A (coarse.tube j)) =
      (P.fullContainmentFiberSubfamily j).family.toBodyFamily.mass :=
  BodyFamily.containedMass_eq_mass_of_all_contained
    (P.fullContainmentFiberSubfamily j).family.toBodyFamily
    (dilatedTubeCarrier A (coarse.tube j))
    (P.fullContainmentFiber_all_contained j)

/-- Fiber reference density is nonzero. -/
lemma fullContainmentFiberDensity_ne_zero
    {A delta rho : ℝ} {fine : TubeFamily delta} {coarse : TubeFamily rho}
    (P : DilatedTubeCover A fine coarse)
    (hA : 1 ≤ A) (hdelta : 0 < delta) (hrho : 0 < rho)
    (j : Fin coarse.card) :
    (P.fullContainmentFiberSubfamily j).family.toBodyFamily.density
        (dilatedTubeCarrier A (coarse.tube j)) ≠ 0 := by
  let G := (P.fullContainmentFiberSubfamily j).family.toBodyFamily
  let U := dilatedTubeCarrier A (coarse.tube j)
  have hmass : G.containedMass U = G.mass :=
    P.fullContainmentFiberContainedMass_eq_mass j
  have hmass_pos : 0 < G.mass :=
    (P.fullContainmentFiberMass_pos_and_top hdelta j).1
  have hvol_top : volume U ≠ ⊤ :=
    P.fullContainmentFiberCarrier_volume_ne_top hA hrho j
  dsimp only [BodyFamily.density]
  rw [hmass]
  exact ENNReal.div_ne_zero.mpr ⟨hmass_pos.ne', hvol_top⟩

/-- Fiber reference density is finite. -/
lemma fullContainmentFiberDensity_ne_top
    {A delta rho : ℝ} {fine : TubeFamily delta} {coarse : TubeFamily rho}
    (P : DilatedTubeCover A fine coarse)
    (hA : 1 ≤ A) (hdelta : 0 < delta) (hrho : 0 < rho)
    (j : Fin coarse.card) :
    (P.fullContainmentFiberSubfamily j).family.toBodyFamily.density
        (dilatedTubeCarrier A (coarse.tube j)) ≠ ⊤ := by
  let G := (P.fullContainmentFiberSubfamily j).family.toBodyFamily
  let U := dilatedTubeCarrier A (coarse.tube j)
  have hmass : G.containedMass U = G.mass :=
    P.fullContainmentFiberContainedMass_eq_mass j
  have hmass_top : G.mass ≠ ⊤ :=
    (P.fullContainmentFiberMass_pos_and_top hdelta j).2
  have hvol_pos : 0 < volume U :=
    P.fullContainmentFiberCarrier_volume_pos hA hrho j
  dsimp only [BodyFamily.density]
  rw [hmass]
  exact ENNReal.div_ne_top hmass_top hvol_pos.ne'

/-- The `deltaMax = frostman * density` identity for a full-containment fiber. -/
lemma fullContainmentFiberDeltaMax_eq_frostman_mul_density
    {A delta rho : ℝ} {fine : TubeFamily delta} {coarse : TubeFamily rho}
    (P : DilatedTubeCover A fine coarse)
    (hA : 1 ≤ A) (hdelta : 0 < delta) (hrho : 0 < rho)
    (j : Fin coarse.card) :
    P.fullContainmentFiberDeltaMax j =
      P.fullContainmentFiberFrostmanConstant j *
      (P.fullContainmentFiberSubfamily j).family.toBodyFamily.density
        (dilatedTubeCarrier A (coarse.tube j)) := by
  let G := (P.fullContainmentFiberSubfamily j).family.toBodyFamily
  let U := dilatedTubeCarrier A (coarse.tube j)
  have hall : ∀ i, (G.body i).carrier ⊆ U :=
    P.fullContainmentFiber_all_contained j
  have hmass_pos : 0 < G.containedMass U := by
    rw [P.fullContainmentFiberContainedMass_eq_mass j]
    exact (P.fullContainmentFiberMass_pos_and_top hdelta j).1
  have hmass_top : G.containedMass U ≠ ⊤ := by
    rw [P.fullContainmentFiberContainedMass_eq_mass j]
    exact (P.fullContainmentFiberMass_pos_and_top hdelta j).2
  have hvol_pos : 0 < volume U :=
    P.fullContainmentFiberCarrier_volume_pos hA hrho j
  have hvol_top : volume U ≠ ⊤ :=
    P.fullContainmentFiberCarrier_volume_ne_top hA hrho j
  exact BodyFamily.deltaMax_eq_frostmanConstantIn_mul_density_of_contained
    G U (P.fullContainmentFiberCarrier_convex j) hall
    hmass_pos hmass_top hvol_pos hvol_top

end DilatedTubeCover

namespace AdmissibleScale

/-- An admissible scale is positive when delta is positive. -/
lemma pos {delta : ℝ} (hdelta : 0 < delta)
    (rho : AdmissibleScale delta) : 0 < rho.1 :=
  hdelta.trans_le rho.property.1

/-- An admissible scale is at most one. -/
lemma le_one {delta : ℝ} (rho : AdmissibleScale delta) : rho.1 ≤ 1 :=
  rho.property.2

end AdmissibleScale

/-- `1 ≤ refinedLemmaSevenSevenCoverDilation`. -/
lemma refinedCoverDilation_one_le :
    1 ≤ refinedLemmaSevenSevenCoverDilation := by
  simp [refinedLemmaSevenSevenCoverDilation]

/-- `refinedLemmaSevenSevenCoverDilation ≠ 0`. -/
lemma refinedCoverDilation_ne_zero :
    refinedLemmaSevenSevenCoverDilation ≠ 0 := by
  simp [refinedLemmaSevenSevenCoverDilation]

end Kakeya.Streamlined

end
