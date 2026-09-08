import MyLeanRepo.Kakeya.Streamlined.Geometry
import MyLeanRepo.Kakeya.Streamlined.GeometricLemmas.TubeContainment
import MyLeanRepo.Kakeya.Streamlined.RandomTranslation.Multiscale

/-!
# Shift absorption lemma for shared coarse covers

Given a fine tube `T` contained in a coarse tube `C`, a small translation `v`
keeps `T + v` inside `C` provided there is enough "slack" in the containment.

## Main results

- `translate_contained_of_slack`: if the midpoint/direction slack plus
  translation radius `r` fits inside the coarse radius, then `T + v ⊆ C`.
- `translate_contained_of_same_axis`: if `T` and `C` share midpoint and
  direction, then `T + v ⊆ C` whenever `‖v‖ ≤ ρ - δ`.
-/

noncomputable section

open Kakeya.Streamlined.GeometricLemmas Metric

namespace Kakeya.Streamlined.RandomTranslation.WithShading

/-- Translating a tube shifts its midpoint by the same vector. -/
lemma translateTube_midpoint {δ : ℝ} (T : Kakeya.DeltaTube δ) (v : Point3) :
    tubeMidpoint (translateTube T v) = tubeMidpoint T + v := by
  simp [tubeMidpoint, translateTube]
  <;> abel

/-- Translating a tube preserves its direction. -/
lemma translateTube_direction {δ : ℝ} (T : Kakeya.DeltaTube δ) (v : Point3) :
    (translateTube T v).direction = T.direction := by
  rfl

/-- If there is enough slack in the midpoint/direction containment, a small
translation of the fine tube stays inside the coarse tube. -/
lemma translate_contained_of_slack
    {δ ρ r : ℝ} (hδ : 0 ≤ δ)
    (T : Kakeya.DeltaTube δ) (C : Kakeya.DeltaTube ρ)
    (h_slack : ‖tubeMidpoint T - tubeMidpoint C‖ +
        ‖T.direction - C.direction‖ / 2 + δ + r ≤ ρ)
    (v : Point3) (hv : ‖v‖ ≤ r) :
    (translateTube T v).carrier ⊆ C.carrier := by
  have h1 : ‖tubeMidpoint (translateTube T v) - tubeMidpoint C‖ ≤
      ‖tubeMidpoint T - tubeMidpoint C‖ + r := by
    rw [translateTube_midpoint T v]
    have h_eq : (tubeMidpoint T + v) - tubeMidpoint C =
        (tubeMidpoint T - tubeMidpoint C) + v := by abel
    rw [h_eq]
    have h : ‖(tubeMidpoint T - tubeMidpoint C) + v‖ ≤
        ‖tubeMidpoint T - tubeMidpoint C‖ + ‖v‖ := norm_add_le _ _
    exact le_trans h (by gcongr)
  have h2 : ‖(translateTube T v).direction - C.direction‖ =
      ‖T.direction - C.direction‖ := by
    rw [translateTube_direction T v]
  have hclose : ‖tubeMidpoint (translateTube T v) - tubeMidpoint C‖ +
      ‖(translateTube T v).direction - C.direction‖ / 2 + δ ≤ ρ := by
    rw [h2]
    calc
      ‖tubeMidpoint (translateTube T v) - tubeMidpoint C‖ +
          ‖T.direction - C.direction‖ / 2 + δ
        ≤ (‖tubeMidpoint T - tubeMidpoint C‖ + r) +
            ‖T.direction - C.direction‖ / 2 + δ := by gcongr
      _ = ‖tubeMidpoint T - tubeMidpoint C‖ +
            ‖T.direction - C.direction‖ / 2 + δ + r := by ring
      _ ≤ ρ := h_slack
  exact tube_contained_of_midpoint_direction_close hδ (translateTube T v) C hclose

/-- If `T` and `C` share the same midpoint and direction, then `T + v ⊆ C`
for any translation of norm at most `ρ - δ`. -/
lemma translate_contained_of_same_axis
    {δ ρ : ℝ} (hδ : 0 ≤ δ) (h_le : δ ≤ ρ)
    (T : Kakeya.DeltaTube δ) (C : Kakeya.DeltaTube ρ)
    (h_mid : tubeMidpoint T = tubeMidpoint C)
    (h_dir : T.direction = C.direction)
    (v : Point3) (hv : ‖v‖ ≤ ρ - δ) :
    (translateTube T v).carrier ⊆ C.carrier := by
  have h_slack : ‖tubeMidpoint T - tubeMidpoint C‖ +
      ‖T.direction - C.direction‖ / 2 + δ + (ρ - δ) ≤ ρ := by
    rw [h_mid, h_dir]
    <;> simp [norm_zero] <;> linarith
  exact translate_contained_of_slack hδ T C h_slack v hv

end Kakeya.Streamlined.RandomTranslation.WithShading

end
