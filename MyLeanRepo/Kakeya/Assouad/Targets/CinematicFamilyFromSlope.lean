import MyLeanRepo.Kakeya.Assouad.CinematicStatements
import MyLeanRepo.Kakeya.Assouad.CinematicFamilyFromSlope.Construction
import MyLeanRepo.Kakeya.Assouad.CinematicFamilyFromSlope.UpperBound
import MyLeanRepo.Kakeya.Assouad.CinematicFamilyFromSlope.LowerBound
import MyLeanRepo.Kakeya.Assouad.CinematicFamilyFromSlope.Uniqueness
import MyLeanRepo.Kakeya.Assouad.CinematicFamilyFromSlope.Doubling

/-!
WZ2 Section 7 / WZ1 Lemma 7.3: construct the cinematic parameter family
associated to a nonsingular slope.

This file assembles construction, upper and lower metric bounds, uniqueness,
and the explicit doubling argument into the final theorem.
-/

noncomputable section

namespace Kakeya.Assouad

open Kakeya.Cinematic

theorem cinematic_family_from_slope :
    CinematicFamilyFromSlopeStatement := by
  let K : ℝ := 37500 / 99
  let D : ℝ := (216 ^ 12 : ℝ)
  have hK1 : 1 ≤ K := by norm_num [K]
  have hD1 : 1 ≤ D := by norm_num [D]
  refine' ⟨K, D, hK1, hD1, _⟩
  intro f h_ns h0
  let paramCube : Set (Fin 3 → ℝ) := {p | ∀ i, p i ∈ Set.Icc (-1 : ℝ) 1}
  let φ : (Fin 3 → ℝ) → C2Function := fun p => slopeCurve f (p 0) (p 1) (p 2)
  let family : Set C2Function := φ '' paramCube
  have h_family_def : IsSlopeCurveFamily family f := by
    intro g
    simp only [family, IsSlopeCurveFamily, Set.mem_image, paramCube]
    constructor
    · rintro ⟨p, hp, rfl⟩
      refine ⟨p 0, hp 0, p 1, hp 1, p 2, hp 2, ?_⟩
      exact slopeCurve_represents f (p 0) (p 1) (p 2)
    · rintro ⟨a, ha, b, hb, d, hd, hrep⟩
      let p : Fin 3 → ℝ := fun i =>
        match i with
        | 0 => a
        | 1 => b
        | 2 => d
      have hp0 : p 0 = a := by simp [p]
      have hp1 : p 1 = b := by simp [p]
      have hp2 : p 2 = d := by simp [p]
      have hp : p ∈ paramCube := by
        simp only [paramCube, Set.mem_setOf_eq]
        intro i
        fin_cases i <;> simp [hp0, hp1, hp2, ha, hb, hd] <;> tauto
      have hrep2 : RepresentsSlopeCurve (φ p) f a b d := by
        simpa [φ, hp0, hp1, hp2] using slopeCurve_represents f a b d
      have h_eq : g = φ p := represents_eq hrep hrep2
      exact ⟨p, hp, h_eq.symm⟩
  refine' ⟨family, h_family_def, _⟩
  have h_main : IsCinematicFamily family K D := by
    dsimp only [IsCinematicFamily]
    constructor
    · -- 1. Bounded diameter
      intro g1 hg1 g2 hg2
      rcases (h_family_def g1).mp hg1 with ⟨a1, ha1, b1, hb1, d1, hd1, hrep1⟩
      rcases (h_family_def g2).mp hg2 with ⟨a2, ha2, b2, hb2, d2, hd2, hrep2⟩
      set P : ℝ := |a1 - a2| + |b1 - b2| + |d1 - d2| with hP
      have ha1' : |a1| ≤ 1 := abs_le.mpr ha1
      have ha2' : |a2| ≤ 1 := abs_le.mpr ha2
      have hb1' : |b1| ≤ 1 := abs_le.mpr hb1
      have hb2' : |b2| ≤ 1 := abs_le.mpr hb2
      have hd1' : |d1| ≤ 1 := abs_le.mpr hd1
      have hd2' : |d2| ≤ 1 := abs_le.mpr hd2
      have h1 : |a1 - a2| ≤ 2 := by
        calc |a1 - a2| ≤ |a1| + |a2| := by exact abs_sub a1 a2
          _ ≤ 1 + 1 := by gcongr
          _ = 2 := by norm_num
      have h2 : |b1 - b2| ≤ 2 := by
        calc |b1 - b2| ≤ |b1| + |b2| := by exact abs_sub b1 b2
          _ ≤ 1 + 1 := by gcongr
          _ = 2 := by norm_num
      have h3 : |d1 - d2| ≤ 2 := by
        calc |d1 - d2| ≤ |d1| + |d2| := by exact abs_sub d1 d2
          _ ≤ 1 + 1 := by gcongr
          _ = 2 := by norm_num
      have hP_le : P ≤ 6 := by linarith
      have h_eq1 : g1 = slopeCurve f a1 b1 d1 :=
        represents_eq hrep1 (slopeCurve_represents f a1 b1 d1)
      have h_eq2 : g2 = slopeCurve f a2 b2 d2 :=
        represents_eq hrep2 (slopeCurve_represents f a2 b2 d2)
      have h_dist : c2Distance g1 g2 ≤ 5 * P := by
        rw [h_eq1, h_eq2]
        exact slopeCurve_c2Distance_le f h_ns h0 a1 b1 d1 a2 b2 d2
      have h_final : c2Distance g1 g2 ≤ K := by
        calc c2Distance g1 g2
          ≤ 5 * P := h_dist
        _ ≤ 5 * 6 := by gcongr
        _ = 30 := by norm_num
        _ ≤ K := by norm_num [K]
      exact h_final
    constructor
    · -- 2. Doubling
      have h_doub_core := slopeCurve_doubling_core f h_ns h0 family h_family_def
      intro g0 hg0 r hr
      rcases h_doub_core hg0 r hr with ⟨centers, h_finite, h_subset, h_card, h_cover⟩
      have h_D : (centers.ncard : ℝ) ≤ D := by
        have h1 : (centers.ncard : ℝ) ≤ (216 ^ 12 : ℝ) := h_card
        have h2 : D = (216 ^ 12 : ℝ) := by simp [D]
        rw [h2]
        exact h1
      have h_cover' : ∀ ⦃g : C2Function⦄, g ∈ family → c2Distance g0 g ≤ r → ∃ h ∈ centers, c2Distance h g ≤ r / 2 := by
        intro g hg hdist
        have hdist' : c2Distance g g0 ≤ r := by
          simpa [c2Distance, dist_comm] using hdist
        exact h_cover hg hdist'
      exact ⟨centers, h_finite, h_subset, h_D, h_cover'⟩
    · -- 3. Cinematic lower bound
      intro g1 hg1 g2 hg2 x
      rcases (h_family_def g1).mp hg1 with ⟨a1, ha1, b1, hb1, d1, hd1, hrep1⟩
      rcases (h_family_def g2).mp hg2 with ⟨a2, ha2, b2, hb2, d2, hd2, hrep2⟩
      set P : ℝ := |a1 - a2| + |b1 - b2| + |d1 - d2| with hP
      have h_lower : (99 / 7500 : ℝ) * P ≤ jetGap g1 g2 x :=
        slopeCurve_jetGap_ge f h_ns h0 g1 g2 a1 b1 d1 a2 b2 d2 hrep1 hrep2 x
      have h_eq1 : g1 = slopeCurve f a1 b1 d1 :=
        represents_eq hrep1 (slopeCurve_represents f a1 b1 d1)
      have h_eq2 : g2 = slopeCurve f a2 b2 d2 :=
        represents_eq hrep2 (slopeCurve_represents f a2 b2 d2)
      have h_upper : c2Distance g1 g2 ≤ 5 * P := by
        rw [h_eq1, h_eq2]
        exact slopeCurve_c2Distance_le f h_ns h0 a1 b1 d1 a2 b2 d2
      have hP_ge : c2Distance g1 g2 / 5 ≤ P := by linarith
      have h_main : (99 / 37500 : ℝ) * c2Distance g1 g2 ≤ jetGap g1 g2 x := by
        calc (99 / 37500 : ℝ) * c2Distance g1 g2
          = (99 / 7500 : ℝ) * (c2Distance g1 g2 / 5) := by ring
        _ ≤ (99 / 7500 : ℝ) * P := by gcongr
        _ ≤ jetGap g1 g2 x := h_lower
      have hK_inv : K⁻¹ = (99 / 37500 : ℝ) := by
        simp [K]
      rw [hK_inv]
      exact h_main
  exact h_main

end Kakeya.Assouad
