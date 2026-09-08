/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Plank.AngleDef

/-!
# Moving an arbitrary-centre local-density estimate between radii

The Step-3 machinery produces its almost-filling estimate at the radius of the slab family it was
run on, and `ShadedPlank.reduction_to_slab_atTypicalAngle` asks for it at the radius `θ * b` fixed
by the leaf's own prescribed angle.  This file records exactly when the two can be exchanged.

**Upward is free; downward is not.**  The estimate is universally quantified over centres, so it
can be *coarsened*: given it at radius `r₁`, a centre `x` whose `r₂`-ball meets the set supplies a
point `y` of the set within `r₂` of `x`, the `r₁`-estimate applies at `y`, and the resulting mass
sits inside `closedBall x (3 * r₂)` as soon as `3 * r₁ ≤ 2 * r₂`.  The reference volume stays at
`r₁`, which is where the loss lives.

Going the other way — from a *larger* produced radius to a *smaller* demanded one — is **not**
available for a `∀ x` statement: the mass the hypothesis provides sits in a ball of radius `3 * r₁`
that is not contained in `closedBall x (3 * r₂)` at all.  (The familiar "a dense ball at a large
radius contains a dense ball at a small radius" argument produces *one* good ball, not a bound at
every centre, so it does not apply here.)

That asymmetry is what forces a producer to run at an angle **below** the leaf's `θ`, and it is the
reason the absolute-constant one-sided angle bound matters: without it the produced angle is only
known to be `≤ C * θ`, which is on the wrong side of `3 * r₁ ≤ 2 * r₂`.

`Plank.localDensity_transport_radius` is the geometric half and mentions no dimension;
`Plank.volume_closedBall_ratio` is the one-line scaling that converts the reference volume, and
`Plank.localDensity_transport_radius'` is the two combined.
-/

@[expose] public section

open MeasureTheory Metric
open scoped NNReal Real ENNReal

noncomputable section

namespace Plank

/-- **A `∀`-centre local-density estimate coarsens to any larger radius, with the reference volume
left at the smaller one.**

The hypothesis `3 * r₁ ≤ 2 * r₂` is what makes `closedBall y (3 * r₁) ⊆ closedBall x (3 * r₂)` for
every `y` within `r₂` of `x`; it is strictly stronger than `r₁ ≤ r₂` and it is the real content of
the side condition. -/
theorem localDensity_transport_radius
    {U : Set (EuclideanSpace ℝ (Fin 3))} {r₁ r₂ : ℝ} (h32 : 3 * r₁ ≤ 2 * r₂) {ρ : ENNReal}
    (h : ∀ z : EuclideanSpace ℝ (Fin 3), (U ∩ closedBall z r₁).Nonempty →
      ρ * volume (closedBall z r₁) ≤ volume (U ∩ closedBall z (3 * r₁))) :
    ∀ x : EuclideanSpace ℝ (Fin 3), (U ∩ closedBall x r₂).Nonempty →
      ρ * volume (closedBall x r₁) ≤ volume (U ∩ closedBall x (3 * r₂)) := by
  intro x hx
  obtain ⟨y, hyU, hyx⟩ := hx
  rcases le_or_gt (0:ℝ) r₁ with hr₁ | hr₁
  swap
  · -- a negative radius makes the reference ball empty and the claim vacuous
    rw [Metric.closedBall_eq_empty.mpr hr₁]
    simp
  have hy1 : (U ∩ closedBall y r₁).Nonempty := ⟨y, hyU, by simpa using hr₁⟩
  have hsub : closedBall y (3 * r₁) ⊆ closedBall x (3 * r₂) := by
    intro w hw
    rw [mem_closedBall] at hw ⊢
    have hyx' : dist y x ≤ r₂ := mem_closedBall.mp hyx
    calc dist w x ≤ dist w y + dist y x := dist_triangle w y x
      _ ≤ 3 * r₁ + r₂ := add_le_add hw hyx'
      _ ≤ 2 * r₂ + r₂ := by linarith
      _ = 3 * r₂ := by ring
  have hcentre : volume (closedBall y r₁) = volume (closedBall x r₁) := by
    rw [Measure.addHaar_closedBall_center volume y r₁,
      Measure.addHaar_closedBall_center volume x r₁]
  calc ρ * volume (closedBall x r₁) = ρ * volume (closedBall y r₁) := by rw [hcentre]
    _ ≤ volume (U ∩ closedBall y (3 * r₁)) := h y hy1
    _ ≤ volume (U ∩ closedBall x (3 * r₂)) := measure_mono (Set.inter_subset_inter_right _ hsub)

/-- The reference volumes at two radii differ by the cube of their ratio, `EuclideanSpace ℝ (Fin 3)`
having dimension `3`. -/
theorem volume_closedBall_ratio (x : EuclideanSpace ℝ (Fin 3)) {r₁ r₂ : ℝ}
    (h₁ : 0 ≤ r₁) (h₂ : 0 < r₂) :
    volume (closedBall x r₁)
      = ENNReal.ofReal ((r₁ / r₂) ^ 3) * volume (closedBall x r₂) := by
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
  rw [Measure.addHaar_closedBall volume x h₁, Measure.addHaar_closedBall volume x h₂.le, hdim,
    ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
  congr 2
  field_simp

/-- **The two combined**: the estimate coarsens from `r₁` to `r₂` at the cost of `(r₁ / r₂) ^ 3` in
the density, exactly the loss the ledger charges for a radius transport. -/
theorem localDensity_transport_radius'
    {U : Set (EuclideanSpace ℝ (Fin 3))} {r₁ r₂ : ℝ} (h₁ : 0 ≤ r₁) (h₂ : 0 < r₂)
    (h32 : 3 * r₁ ≤ 2 * r₂) {ρ : ENNReal}
    (h : ∀ z : EuclideanSpace ℝ (Fin 3), (U ∩ closedBall z r₁).Nonempty →
      ρ * volume (closedBall z r₁) ≤ volume (U ∩ closedBall z (3 * r₁))) :
    ∀ x : EuclideanSpace ℝ (Fin 3), (U ∩ closedBall x r₂).Nonempty →
      (ρ * ENNReal.ofReal ((r₁ / r₂) ^ 3)) * volume (closedBall x r₂)
        ≤ volume (U ∩ closedBall x (3 * r₂)) := by
  intro x hx
  have h' := localDensity_transport_radius h32 h x hx
  rwa [volume_closedBall_ratio x h₁ h₂, ← mul_assoc] at h'


/-! ## What the transport needs from the angle, and exactly which datum supplies it -/

variable {ι : Type*}

/-- **A one-sided angle bound at an absolute constant caps the pinned dyadic angle.**

`Plank.exists_restriction_maxPlankAngle_pinned` returns `θ'` with `θ' ≤ maxPlankAngle P (fibre x)`
on the restricted union.  If the family also satisfies
`Kakeya.HasMaxPlankAngleBound s Z P θ 1` — the one-sided bound at the **absolute** constant `1` —
then `θ' ≤ θ`.

This is the only place where an absolute one-sided bound is needed, and
`Kakeya.findingTypicalAngleOfIntersection_perScale` proves exactly it, as its last conclusion. -/
theorem pinned_angle_le_of_absoluteBound {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
    {s : Finset ι} {Z : ι → ShadedBody (EuclideanSpace ℝ (Fin 3))} {P : ι → Plank a b hab hb1}
    {θ θ' : ℝ≥0} (hmaxabs : Kakeya.HasMaxPlankAngleBound s Z P θ 1)
    (hlow : ∀ x ∈ ⋃ i ∈ s, (Z i).shade,
      θ' ≤ Kakeya.maxPlankAngle P (Kakeya.shadeFibre s Z x))
    (hne : (⋃ i ∈ s, (Z i).shade).Nonempty) : θ' ≤ θ := by
  obtain ⟨x, hx⟩ := hne
  calc θ' ≤ Kakeya.maxPlankAngle P (Kakeya.shadeFibre s Z x) := hlow x hx
    _ ≤ 1 * θ := hmaxabs x hx
    _ = θ := one_mul θ

/-- Halving the pinned angle doubles the (still absolute) constant. -/
theorem hasMaxPlankAngleBound_half {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
    {s : Finset ι} {Z : ι → ShadedBody (EuclideanSpace ℝ (Fin 3))} {P : ι → Plank a b hab hb1}
    {θ' : ℝ≥0} (h : Kakeya.HasMaxPlankAngleBound s Z P θ' 2) :
    Kakeya.HasMaxPlankAngleBound s Z P (θ' / 2) 4 := by
  intro x hx
  refine le_trans (h x hx) (le_of_eq ?_)
  rw [eq_comm]
  field_simp
  ring

/-- **The transport side condition, discharged.**

With the pinned angle halved and capped by `θ`, the radii `r₁ = (θ' / 2) * b` and `r₂ = θ * b`
satisfy `3 * r₁ ≤ 2 * r₂`, the hypothesis of `Plank.localDensity_transport_radius`.  So an
almost-filling estimate produced by the slab layer at the halved dyadic angle coarsens to the
leaf's own radius `θ * b`.

Together with `Plank.pinned_angle_le_of_absoluteBound` this is the machine-checked form of the
statement *"an absolute one-sided angle bound is exactly what unlocks the radius transport"*. -/
theorem transport_side_condition {θ θ' b : ℝ≥0} (hθ'θ : θ' ≤ θ) :
    3 * (((θ' / 2) * b : ℝ≥0) : ℝ) ≤ 2 * ((θ * b : ℝ≥0) : ℝ) := by
  have hb : (0 : ℝ) ≤ (b : ℝ) := b.coe_nonneg
  have h : ((θ' : ℝ)) ≤ (θ : ℝ) := by exact_mod_cast hθ'θ
  push_cast
  nlinarith [hb, h, θ'.coe_nonneg, θ.coe_nonneg]

end Plank

end
