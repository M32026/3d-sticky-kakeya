/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Section6CompatThicken

/-!
# The small-radius half of `ShadedPlank.reduction_to_slab_atTypicalAngle`

`Section6CompatDense.lean` and `Section6CompatThicken.lean` both reduce
`ShadedPlank.reduction_to_slab_atTypicalAngle` to an obligation about the *shading union*
`U(s, Y'')` — a dense region inside it, or the volume of its `θb`-thickening.  Both reductions
keep the output index set equal to `s`, and that is what forces the obligation to be about the
union: with `s' = s` the fullness clause asks the retained shades to carry a fixed fraction of the
**total** mass `∑_{i ∈ s} |Y_i|`.

This file takes the other branch.  `ShadedBody.fullness` is a **ratio over the retained index
set**, so an output family supported on a *single* plank has to carry only the **average** plank's
worth of mass, `(∑_{i ∈ s} |Y_i|) / |s|` — and the plank with the largest `Y''`-shade carries at
least `C⁻¹` times that for free.  Discarding the mass-sparse `θb`-balls then happens **inside one
plank**, so the discard is measured against `|N_{θb}(P_{i₀})| ≤ 64 θ b ²`
(`ShadedPlank.volume_cthickening_plank_le`) rather than against the thickening of the union.  Both
`|s|` and the geometry of the union drop out, and the entire obligation collapses to a scalar
inequality **between the parameters `δ, a, b, θ, C` alone**:

```
432 · δ ^ ε' · a ^ (4η) · a ^ ε · C · θ b ≤ a ^ η · a.
```

`ShadedPlank.reduction_to_slab_atTypicalAngle_of_radius_le` is the clean corollary: the target
holds outright whenever

```
θ b ≤ a ^ (1 - 3η - ε),
```

a comparison of two *scales*.  This regime is not empty and not artificial — `a / b ≤ θ` forces
`a ≤ θ b`, and `a ≤ a ^ (1 - 3η - ε)` for `0 < a < 1`
(`ShadedPlank.radius_le_of_min_angle`), so the band `a ≤ θ b ≤ a ^ (1 - 3η - ε)` always contains
the smallest admissible radius.  **At the minimal angle `θ = a / b` the hypothesis is automatic**,
so the narrow-angle case of GWZ Lemma 6.13 at a prescribed typical angle is proved here with no
obligation at all.  What remains open at `Section6Compat.lean` is exactly the **wide-angle**
regime `θ b > a ^ (1 - 3η - ε)`, where the single plank's own thickening ratio `θb / a` is too
large and the multiplicity of the family has to be used.

## Relation to `ShadedPlank.singleBall_necessary_condition_fails`

`Section6CompatDense.lean` certifies that a *single ball* cannot carry the reduction, by the
necessary condition `κ · λ · a · b ≤ (θ b) ³` of
`ShadedPlank.denseBall_mass_forces_cube_bound`.  That obstruction is derived from the hypothesis
`hmass` **on the full index set `s`**, which is why `|s|` cancels out of it and it becomes a
statement about one plank's worth of mass sitting inside one ball.  The route here evades it on
both counts: the retained region `G` is a *union* of good `θb`-balls, not one ball, and the
retained index set is the singleton `{i₀}`.  At the very parameters at which
`ShadedPlank.singleBall_necessary_condition_fails` refutes the one-ball route
(`δ = a`, `b = 1`, `θ = a / b`, `λ = a ^ η`, `c1 = δ ^ ε'`) the hypothesis of
`ShadedPlank.reduction_to_slab_atTypicalAngle_of_radius_le` reads `a ≤ a ^ (1 - 3η - ε)` and is
true.  So the failure recorded there is a failure of `s' = s`, not of locality.

Nothing in this file uses `Kakeya.IsTypicalPlankAngle`, `Kakeya.IsEssentiallyDistinct`,
`Plank.IsWindowedFamily`, `ShadedBody.HasCConstantMultiplicity` or either multiplicity
hypothesis; those are what a producer for the wide-angle regime needs.
-/

@[expose] public section

open MeasureTheory Metric
open scoped NNReal Real ENNReal

noncomputable section

namespace ShadedPlank

variable {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}

/-! ## Two prism-geometry facts -/

/-- **A prism's closed `ρ`-neighbourhood sits in the prism with every half-width raised by `ρ`.**
Only orthonormality of the frame is used: `|⟨v, e i⟩| ≤ ‖v‖`. -/
theorem cthickening_prism_subset_resize
    (P : PrismNDim 3 (EuclideanSpace ℝ (Fin 3)) (EuclideanSpace ℝ (Fin 3)))
    {ρ : ℝ≥0} (hρ : 0 < ρ) :
    Metric.cthickening (ρ : ℝ) (P.carrier : Set (EuclideanSpace ℝ (Fin 3)))
      ⊆ ((P.resize (fun i => P.thicknesses i + ρ)).carrier :
          Set (EuclideanSpace ℝ (Fin 3))) := by
  have hclosed : IsClosed (P.carrier : Set (EuclideanSpace ℝ (Fin 3))) := P.isClosed_carrier
  have hρ0 : (0 : ℝ) < (ρ : ℝ) := by exact_mod_cast hρ
  rw [hclosed.cthickening_eq_biUnion_closedBall hρ0.le]
  intro x hx
  obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp hx
  rw [P.mem_resize_carrier]
  intro i
  have hyi : |P.basis.repr (y -ᵥ P.center) i| ≤ (P.thicknesses i : ℝ) :=
    (P.mem_carrier_iff y).1 hy i
  have hdiff : |P.basis.repr (x -ᵥ y) i| ≤ (ρ : ℝ) := by
    rw [P.basis.repr_apply_apply]
    calc |inner ℝ (P.basis i) (x -ᵥ y)|
        ≤ ‖P.basis i‖ * ‖x -ᵥ y‖ := abs_real_inner_le_norm _ _
      _ = ‖x -ᵥ y‖ := by rw [P.basis.norm_eq_one, one_mul]
      _ = dist x y := by rw [dist_eq_norm_vsub (EuclideanSpace ℝ (Fin 3))]
      _ ≤ (ρ : ℝ) := Metric.mem_closedBall.mp hxy
  have hsplit : P.basis.repr (x -ᵥ P.center) i
      = P.basis.repr (x -ᵥ y) i + P.basis.repr (y -ᵥ P.center) i := by
    rw [show x -ᵥ P.center = (x -ᵥ y) + (y -ᵥ P.center) from
      (vsub_add_vsub_cancel x y P.center).symm, map_add, PiLp.add_apply]
  have hgoal : |P.basis.repr (x -ᵥ P.center) i| ≤ (P.thicknesses i : ℝ) + (ρ : ℝ) := by
    rw [hsplit]
    calc |P.basis.repr (x -ᵥ y) i + P.basis.repr (y -ᵥ P.center) i|
        ≤ |P.basis.repr (x -ᵥ y) i| + |P.basis.repr (y -ᵥ P.center) i| := abs_add_le _ _
      _ ≤ (ρ : ℝ) + (P.thicknesses i : ℝ) := add_le_add hdiff hyi
      _ = (P.thicknesses i : ℝ) + (ρ : ℝ) := by ring
  simpa using hgoal

/-- **The `θb`-neighbourhood of an `a × b × 1` plank has volume at most `64 θ b ²`.**

Every half-width is raised by `θb`; with `a ≤ θb ≤ b ≤ 1` the three raised half-widths are at
most `2θb`, `2b` and `2`, and `2 ³ · 2θb · 2b · 2 = 64 θ b ²`. -/
theorem volume_cthickening_plank_le (P : Plank a b hab hb1) {θ : ℝ≥0}
    (hθ : 0 < θ) (hb : 0 < b) (hθ1 : θ ≤ 1) (hb1' : b ≤ 1) (haθb : a ≤ θ * b) :
    volume (Metric.cthickening ((θ * b : ℝ≥0) : ℝ)
        (P.carrier : Set (EuclideanSpace ℝ (Fin 3))))
      ≤ 64 * (θ : ENNReal) * (b : ENNReal) * (b : ENNReal) := by
  have hρ : (0 : ℝ≥0) < θ * b := mul_pos hθ hb
  have hsub := cthickening_prism_subset_resize P.toPrismNDim hρ
  refine le_trans (measure_mono hsub) ?_
  have hth : P.toPrismNDim.thicknesses = ![a, b, (1 : ℝ≥0)] := P.thicknesses_eq
  have hθbb : θ * b ≤ b := by
    calc θ * b ≤ 1 * b := by gcongr
      _ = b := one_mul b
  have hprod : (∏ i, (P.toPrismNDim.thicknesses i + θ * b)) ≤ 8 * (θ * b) * b := by
    rw [Fin.prod_univ_three, hth]
    have h0 : a + θ * b ≤ 2 * (θ * b) := by
      have : a + θ * b ≤ θ * b + θ * b := by gcongr
      simpa [two_mul] using this
    have h1 : b + θ * b ≤ 2 * b := by
      have : b + θ * b ≤ b + b := by gcongr
      simpa [two_mul] using this
    have h2 : (1 : ℝ≥0) + θ * b ≤ 2 := by
      have hle : θ * b ≤ (1 : ℝ≥0) := le_trans hθbb hb1'
      calc (1 : ℝ≥0) + θ * b ≤ 1 + 1 := by gcongr
        _ = 2 := by norm_num
    calc (![a, b, (1 : ℝ≥0)] 0 + θ * b) * (![a, b, (1 : ℝ≥0)] 1 + θ * b)
            * (![a, b, (1 : ℝ≥0)] 2 + θ * b)
        = (a + θ * b) * (b + θ * b) * (1 + θ * b) := by simp
      _ ≤ (2 * (θ * b)) * (2 * b) * 2 := by gcongr
      _ = 8 * (θ * b) * b := by ring
  rw [PrismNDim.volume_carrier, PrismNDim.resize_thicknesses]
  have hfr : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
  rw [hfr]
  have hcoe : (∏ i, ((P.toPrismNDim.thicknesses i + θ * b : ℝ≥0) : ENNReal))
      = ((∏ i, (P.toPrismNDim.thicknesses i + θ * b) : ℝ≥0) : ENNReal) := by
    simp
  rw [hcoe]
  have : ((∏ i, (P.toPrismNDim.thicknesses i + θ * b) : ℝ≥0) : ENNReal)
      ≤ ((8 * (θ * b) * b : ℝ≥0) : ENNReal) := by exact_mod_cast hprod
  calc (2 : ENNReal) ^ (3 : ℕ) * ((∏ i, (P.toPrismNDim.thicknesses i + θ * b) : ℝ≥0) : ENNReal)
      ≤ (2 : ENNReal) ^ (3 : ℕ) * ((8 * (θ * b) * b : ℝ≥0) : ENNReal) := by gcongr
    _ = 64 * (θ : ENNReal) * (b : ENNReal) * (b : ENNReal) := by
        push_cast
        ring



/-! ## Non-vacuity of the small-radius hypothesis -/

/-- **At the smallest admissible angle the small-radius hypothesis is automatic.**
`a / b ≤ θ` is the only lower bound the target places on `θ`, and at `θ = a / b` the radius is
`θ b = a`, while `a = a ^ 1 ≤ a ^ (1 - 3η - ε)` because `0 < a ≤ 1` and the exponent has
decreased. -/
theorem radius_le_of_min_angle {a b : ℝ≥0} {η ε : ℝ} (hη : 0 < η) (hε : 0 < ε)
    (ha : 0 < a) (ha1 : a ≤ 1) (hb : 0 < b) :
    (a / b) * b ≤ a ^ (1 - 3 * η - ε) := by
  rw [div_mul_cancel₀ _ hb.ne']
  calc (a : ℝ≥0) = a ^ (1 : ℝ) := (NNReal.rpow_one a).symm
    _ ≤ a ^ (1 - 3 * η - ε) :=
        NNReal.rpow_le_rpow_of_exponent_ge ha ha1 (by linarith)

/-! ## The single-plank reduction -/

/-- **The single-plank reduction.**

Discard the sparse `θb`-balls *inside one plank* rather than inside the whole shading union.
Because `ShadedBody.fullness` is a ratio over the retained index set, an output family supported
on a single plank has to carry only the *average* plank's worth of mass, not the total; and the
mass discarded is then measured against the `θb`-thickening of a *single* plank, whose volume is
`≤ 64 θ b ²` by `ShadedPlank.volume_cthickening_plank_le`, rather than against the thickening of
the union.  Both `|s|` and the geometry of the union drop out, and the whole obligation becomes
the scalar inequality `hbudget`. -/
theorem reduction_atTypicalAngle_singlePlank {η ε : ℝ} {ι : Type*}
    (s : Finset ι) (hs : s.Nonempty) (Y : ι → ShadedPlank a b hab hb1)
    (Y'' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (θ c1 C : ℝ≥0) (hC1 : 1 ≤ C)
    (ha : 0 < a) (hb : 0 < b) (hb1' : b ≤ 1) (hθ : 0 < θ) (hθ1 : θ ≤ 1) (haθb : a ≤ θ * b)
    (hlam : 0 < ShadedBody.fullness s (ShadedPlank.bodies Y))
    (hY'' : ShadedBody.IsCRefinement s Y'' s (ShadedPlank.bodies Y) C⁻¹)
    (hledger : 2 * (c1 * a ^ ε) * C ≤ 1)
    (hbudget : 432 * (c1 * a ^ (4 * η) * a ^ ε) * C * (θ * b)
        ≤ ShadedBody.fullness s (ShadedPlank.bodies Y) * a) :
    ∃ (s' : Finset ι) (Y' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3))),
      ShadedBody.IsRefinement s' Y' s (ShadedPlank.bodies Y) ∧
      ShadedBody.IsRefinement s' Y' s Y'' ∧
      (c1 * a ^ ε) * ShadedBody.fullness s (ShadedPlank.bodies Y)
        ≤ ShadedBody.fullness s' Y' ∧
      (∀ x, ((⋃ i ∈ s', (Y' i).shade) ∩ Metric.closedBall x ((θ * b : ℝ))).Nonempty →
        ((c1 * a ^ (4 * η) * a ^ ε : ℝ≥0) : ENNReal)
            * volume (Metric.closedBall x ((θ * b : ℝ)))
          ≤ volume ((⋃ i ∈ s', (Y' i).shade)
              ∩ Metric.closedBall x (redPlankTube.ballDilation * θ * b))) := by
  classical
  set lam : ℝ≥0 := ShadedBody.fullness s (ShadedPlank.bodies Y) with hlamdef
  set t : ℝ≥0 := c1 * a ^ (4 * η) * a ^ ε with htdef
  set r : ℝ := ((θ * b : ℝ≥0) : ℝ) with hrdef
  have hrpos : 0 < r := by
    rw [hrdef]
    exact_mod_cast mul_pos hθ hb
  have hCne : (C : ℝ≥0) ≠ 0 := (lt_of_lt_of_le zero_lt_one hC1).ne'
  -- the plank carrying the largest `Y''`-shade
  obtain ⟨i₀, hi₀s, hi₀max⟩ := s.exists_max_image (fun i => volume (Y'' i).shade) hs
  set M : ENNReal := volume (Y'' i₀).shade with hMdef
  -- the carrier volumes
  have hcarr : ∀ i, volume ((ShadedPlank.bodies Y i).carrier :
      Set (EuclideanSpace ℝ (Fin 3))) = 8 * (a : ENNReal) * (b : ENNReal) := by
    intro i
    rw [show ((ShadedPlank.bodies Y i).carrier : Set (EuclideanSpace ℝ (Fin 3)))
      = (Y i).carrier from rfl, ShadedPlank.volume_carrier (Y i)]
  have hsumcarr : (∑ i ∈ s, volume ((ShadedPlank.bodies Y i).carrier :
      Set (EuclideanSpace ℝ (Fin 3))))
      = (s.card : ENNReal) * (8 * (a : ENNReal) * (b : ENNReal)) := by
    rw [Finset.sum_congr rfl (fun i _ => hcarr i), Finset.sum_const, nsmul_eq_mul]
  have hcard0 : ((s.card : ENNReal)) ≠ 0 := by
    simpa using (Finset.card_ne_zero_of_mem hs.choose_spec)
  have hcardtop : ((s.card : ENNReal)) ≠ ⊤ := by simp
  -- the key lower bound `λ · 8ab ≤ C · M`
  have hMlb : (lam : ENNReal) * (8 * (a : ENNReal) * (b : ENNReal)) ≤ (C : ENNReal) * M := by
    have hsum : (∑ i ∈ s, volume (ShadedPlank.bodies Y i).shade)
        = (lam : ENNReal) * ((s.card : ENNReal) * (8 * (a : ENNReal) * (b : ENNReal))) := by
      rw [ShadedBody.sum_volumeReal_shade_eq_fullness_mul, hsumcarr]
    have hmax : (∑ i ∈ s, volume (Y'' i).shade) ≤ (s.card : ENNReal) * M := by
      calc (∑ i ∈ s, volume (Y'' i).shade) ≤ ∑ _i ∈ s, M :=
            Finset.sum_le_sum fun i hi => hi₀max i hi
        _ = (s.card : ENNReal) * M := by rw [Finset.sum_const, nsmul_eq_mul]
    have hstep := hY''.2
    rw [hsum] at hstep
    have hmul : ((C : ENNReal)) * (((C⁻¹ : ℝ≥0) : ENNReal)) = 1 := by
      rw [← ENNReal.coe_mul, mul_inv_cancel₀ hCne, ENNReal.coe_one]
    set Z : ENNReal :=
      (lam : ENNReal) * ((s.card : ENNReal) * (8 * (a : ENNReal) * (b : ENNReal))) with hZ
    have heq : (C : ENNReal) * (((C⁻¹ : ℝ≥0) : ENNReal) * Z) = Z := by
      rw [← mul_assoc, hmul, one_mul]
    have h1 : (C : ENNReal) * (((C⁻¹ : ℝ≥0) : ENNReal) * Z)
        ≤ (C : ENNReal) * ((s.card : ENNReal) * M) :=
      mul_le_mul_left' (le_trans hstep hmax) _
    have hZle : Z ≤ (C : ENNReal) * ((s.card : ENNReal) * M) := by rw [← heq]; exact h1
    have hkey : (s.card : ENNReal) * ((lam : ENNReal) * (8 * (a : ENNReal) * (b : ENNReal)))
        ≤ (s.card : ENNReal) * ((C : ENNReal) * M) := by
      calc (s.card : ENNReal) * ((lam : ENNReal) * (8 * (a : ENNReal) * (b : ENNReal)))
          = Z := by rw [hZ]; ring
        _ ≤ (C : ENNReal) * ((s.card : ENNReal) * M) := hZle
        _ = (s.card : ENNReal) * ((C : ENNReal) * M) := by ring
    exact (ENNReal.mul_le_mul_iff_right hcard0 hcardtop).mp hkey
  -- the shade of the selected plank is nonempty
  have hMpos : 0 < M := by
    by_contra hcon
    push_neg at hcon
    have hM0 : M = 0 := le_antisymm hcon bot_le
    rw [hM0, mul_zero] at hMlb
    have hlhs : (0 : ENNReal) < (lam : ENNReal) * (8 * (a : ENNReal) * (b : ENNReal)) := by
      refine ENNReal.mul_pos (ENNReal.coe_pos.mpr hlam).ne' ?_
      exact (ENNReal.mul_pos (ENNReal.mul_pos (by norm_num) (ENNReal.coe_pos.mpr ha).ne').ne'
        (ENNReal.coe_pos.mpr hb).ne').ne'
    exact absurd (le_antisymm hMlb bot_le) hlhs.ne'
  have hshne : ((Y'' i₀).shade).Nonempty :=
    MeasureTheory.nonempty_of_measure_ne_zero hMpos.ne'
  have hbdd : Bornology.IsBounded ((Y'' i₀).shade) :=
    ((Y'' i₀).isCompact.isBounded).subset (Y'' i₀).shade_subset
  obtain ⟨T, hTA, _hTne, hsep, hcovT⟩ :=
    Metric.exists_finset_separated_cover hshne hbdd hrpos
  -- the ball budget of the cover, from the thickening of the single plank
  have hplank : ((Y'' i₀).shade) ⊆ ((ShadedPlank.planks Y i₀).carrier :
      Set (EuclideanSpace ℝ (Fin 3))) := by
    have hbody := (hY''.1.2 i₀ hi₀s).1
    intro x hx
    have hxc : x ∈ ((Y'' i₀).carrier : Set (EuclideanSpace ℝ (Fin 3))) :=
      (Y'' i₀).shade_subset hx
    rwa [show ((Y'' i₀).carrier : Set (EuclideanSpace ℝ (Fin 3)))
      = ((Y'' i₀).toConvexSpaceBody : Set (EuclideanSpace ℝ (Fin 3))) from rfl, hbody] at hxc
  have hQ : (∑ z ∈ T, volume (closedBall z r))
      ≤ 1728 * (θ : ENNReal) * (b : ENNReal) * (b : ENNReal) := by
    have hpack := sum_volume_closedBall_le_cthickening (A := ((Y'' i₀).shade))
      hrpos (fun z hz => hTA hz) hsep
    have hmono : volume (Metric.cthickening r ((Y'' i₀).shade))
        ≤ 64 * (θ : ENNReal) * (b : ENNReal) * (b : ENNReal) := by
      refine le_trans (measure_mono (Metric.cthickening_subset_of_subset r hplank)) ?_
      exact volume_cthickening_plank_le (ShadedPlank.planks Y i₀) hθ hb hθ1 hb1' haθb
    calc (∑ z ∈ T, volume (closedBall z r))
        ≤ 27 * volume (Metric.cthickening r ((Y'' i₀).shade)) := hpack
      _ ≤ 27 * (64 * (θ : ENNReal) * (b : ENNReal) * (b : ENNReal)) := by gcongr
      _ = 1728 * (θ : ENNReal) * (b : ENNReal) * (b : ENNReal) := by ring
  -- the carrier of the selected plank
  have hcarrEq : ((Y'' i₀).carrier : Set (EuclideanSpace ℝ (Fin 3)))
      = ((ShadedPlank.bodies Y i₀).carrier : Set (EuclideanSpace ℝ (Fin 3))) := by
    rw [show ((Y'' i₀).carrier : Set (EuclideanSpace ℝ (Fin 3)))
      = (((Y'' i₀).toConvexSpaceBody).carrier : Set (EuclideanSpace ℝ (Fin 3))) from rfl,
      (hY''.1.2 i₀ hi₀s).1]
  -- the mass discard, inside the single plank
  obtain ⟨G, hGmeas, hmass, hcoverG⟩ :=
    exists_massRegion_of_ballCover ({i₀} : Finset ι) Y'' r T (by simpa using hcovT) t
  set X : ENNReal := volume ((Y'' i₀).shade ∩ G) with hXdef
  set Q : ENNReal := ∑ z ∈ T, volume (closedBall z r) with hQdef
  have hmass' : M ≤ X + (t : ENNReal) * Q := by simpa [hXdef, hQdef, hMdef] using hmass
  have hCne' : ((C : ℝ≥0) : ENNReal) ≠ 0 := by simpa using hCne
  have hCtop : ((C : ℝ≥0) : ENNReal) ≠ ⊤ := by simp
  have hbud2 : (3456 : ℝ≥0) * t * C * θ * b * b ≤ 8 * lam * a * b := by
    have h := mul_le_mul_right' hbudget (8 * b)
    calc (3456 : ℝ≥0) * t * C * θ * b * b = (432 * t * C * (θ * b)) * (8 * b) := by ring
      _ ≤ (lam * a) * (8 * b) := h
      _ = 8 * lam * a * b := by ring
  have h3456 : (3456 : ENNReal) * (t : ENNReal) * (θ : ENNReal) * (b : ENNReal) * (b : ENNReal)
      ≤ M := by
    refine (ENNReal.mul_le_mul_iff_right hCne' hCtop).mp ?_
    calc ((C : ℝ≥0) : ENNReal)
          * ((3456 : ENNReal) * (t : ENNReal) * (θ : ENNReal) * (b : ENNReal) * (b : ENNReal))
        = (((3456 : ℝ≥0) * t * C * θ * b * b : ℝ≥0) : ENNReal) := by push_cast; ring
      _ ≤ (((8 : ℝ≥0) * lam * a * b : ℝ≥0) : ENNReal) := by exact_mod_cast hbud2
      _ = (lam : ENNReal) * (8 * (a : ENNReal) * (b : ENNReal)) := by push_cast; ring
      _ ≤ ((C : ℝ≥0) : ENNReal) * M := hMlb
  have hD : (t : ENNReal) * Q + (t : ENNReal) * Q ≤ M := by
    have h1 : (t : ENNReal) * Q
        ≤ (t : ENNReal) * (1728 * (θ : ENNReal) * (b : ENNReal) * (b : ENNReal)) := by
      gcongr
    calc (t : ENNReal) * Q + (t : ENNReal) * Q
        ≤ (t : ENNReal) * (1728 * (θ : ENNReal) * (b : ENNReal) * (b : ENNReal))
            + (t : ENNReal) * (1728 * (θ : ENNReal) * (b : ENNReal) * (b : ENNReal)) :=
          add_le_add h1 h1
      _ = (3456 : ENNReal) * (t : ENNReal) * (θ : ENNReal) * (b : ENNReal) * (b : ENNReal) := by
          ring
      _ ≤ M := h3456
  have hMtop : M ≠ ⊤ :=
    ne_top_of_le_ne_top ((Y'' i₀).isCompact.measure_ne_top) (measure_mono (Y'' i₀).shade_subset)
  have hQtop : (t : ENNReal) * Q ≠ ⊤ :=
    ne_top_of_le_ne_top hMtop (le_trans le_add_self hD)
  have hDX : (t : ENNReal) * Q ≤ X :=
    (ENNReal.add_le_add_iff_right hQtop).mp (le_trans hD hmass')
  have hM2X : M ≤ 2 * X := by
    calc M ≤ X + (t : ENNReal) * Q := hmass'
      _ ≤ X + X := by gcongr
      _ = 2 * X := by ring
  -- the output family
  refine ⟨{i₀}, fun i => (Y'' i).restrictShade G hGmeas, ?_, ?_, ?_, ?_⟩
  · refine ⟨by simpa using hi₀s, ?_⟩
    intro i hi
    rw [Finset.mem_singleton] at hi
    subst hi
    exact ⟨(hY''.1.2 i hi₀s).1, fun x hx => (hY''.1.2 i hi₀s).2 hx.1⟩
  · refine ⟨by simpa using hi₀s, ?_⟩
    intro i hi
    rw [Finset.mem_singleton] at hi
    subst hi
    exact ⟨rfl, fun x hx => hx.1⟩
  · -- the fullness clause
    have h8ab0 : (8 * (a : ENNReal) * (b : ENNReal)) ≠ 0 := by
      refine (ENNReal.mul_pos (ENNReal.mul_pos (by norm_num)
        (ENNReal.coe_pos.mpr ha).ne').ne' (ENNReal.coe_pos.mpr hb).ne').ne'
    have h8abtop : (8 * (a : ENNReal) * (b : ENNReal)) ≠ ⊤ :=
      ENNReal.mul_ne_top (ENNReal.mul_ne_top (by simp) ENNReal.coe_ne_top) ENNReal.coe_ne_top
    have hcarrvol : (∑ i ∈ ({i₀} : Finset ι),
        volume (((Y'' i).restrictShade G hGmeas).carrier :
          Set (EuclideanSpace ℝ (Fin 3))))
        = 8 * (a : ENNReal) * (b : ENNReal) := by
      rw [Finset.sum_singleton]
      rw [show (((Y'' i₀).restrictShade G hGmeas).carrier : Set (EuclideanSpace ℝ (Fin 3)))
        = ((Y'' i₀).carrier : Set (EuclideanSpace ℝ (Fin 3))) from rfl, hcarrEq, hcarr i₀]
    have hshadevol : (∑ i ∈ ({i₀} : Finset ι),
        volume ((Y'' i).restrictShade G hGmeas).shade) = X := by
      rw [Finset.sum_singleton]
      rfl
    rw [← ENNReal.coe_le_coe, ShadedBody.fullness_def, hcarrvol, hshadevol,
      ENNReal.le_div_iff_mul_le (Or.inl h8ab0) (Or.inl h8abtop)]
    have h2C0 : (((2 : ℝ≥0) * C : ℝ≥0) : ENNReal) ≠ 0 := by
      simp [hCne]
    have h2Ctop : (((2 : ℝ≥0) * C : ℝ≥0) : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
    refine (ENNReal.mul_le_mul_iff_right h2C0 h2Ctop).mp ?_
    calc (((2 : ℝ≥0) * C : ℝ≥0) : ENNReal)
          * ((((c1 * a ^ ε) * lam : ℝ≥0) : ENNReal) * (8 * (a : ENNReal) * (b : ENNReal)))
        = (((2 * (c1 * a ^ ε) * C : ℝ≥0)) : ENNReal)
            * ((lam : ENNReal) * (8 * (a : ENNReal) * (b : ENNReal))) := by push_cast; ring
      _ ≤ 1 * ((lam : ENNReal) * (8 * (a : ENNReal) * (b : ENNReal))) := by
          gcongr
          exact_mod_cast hledger
      _ = (lam : ENNReal) * (8 * (a : ENNReal) * (b : ENNReal)) := one_mul _
      _ ≤ ((C : ℝ≥0) : ENNReal) * M := hMlb
      _ ≤ ((C : ℝ≥0) : ENNReal) * (2 * X) := by gcongr
      _ = (((2 : ℝ≥0) * C : ℝ≥0) : ENNReal) * X := by push_cast; ring
  · -- Item 1
    intro x hmeet
    have hUG : (⋃ i ∈ ({i₀} : Finset ι), ((Y'' i).restrictShade G hGmeas).shade)
        = ((Y'' i₀).shade) ∩ G := by
      rw [Plank.biUnion_restrictShade_shade]
      simp
    have hcover' : ∀ y ∈ ((Y'' i₀).shade ∩ G), ∃ c : EuclideanSpace ℝ (Fin 3),
        y ∈ Plank.thetaBall θ b c ∧
        (t : ENNReal) * volume (Plank.thetaBall θ b c)
          ≤ volume (((Y'' i₀).shade ∩ G) ∩ Plank.thetaBall θ b c) := by
      intro y hy
      obtain ⟨z, hyz, hzG, hzdens⟩ := hcoverG y (by simpa using hy)
      refine ⟨z, hyz, ?_⟩
      have hsingle : (∑ i ∈ ({i₀} : Finset ι), volume ((Y'' i).shade ∩ closedBall z r))
          = volume ((Y'' i₀).shade ∩ closedBall z r) := by simp
      have hsub : (Y'' i₀).shade ∩ closedBall z r
          ⊆ ((Y'' i₀).shade ∩ G) ∩ closedBall z r := by
        rintro w ⟨hw1, hw2⟩
        exact ⟨⟨hw1, hzG hw2⟩, hw2⟩
      calc (t : ENNReal) * volume (Plank.thetaBall θ b z)
          ≤ volume ((Y'' i₀).shade ∩ closedBall z r) := by
            rw [← hsingle]; exact hzdens
        _ ≤ volume (((Y'' i₀).shade ∩ G) ∩ Plank.thetaBall θ b z) := measure_mono hsub
    have hmeet' : (((Y'' i₀).shade ∩ G)
        ∩ Metric.closedBall x ((θ * b : ℝ≥0) : ℝ)).Nonempty := by
      rw [← hUG]
      simpa using hmeet
    have hmain := Plank.localDensity_of_denseBallCover (theta := θ) (b := b)
      ((Y'' i₀).shade ∩ G) t hcover' x hmeet'
    rw [hUG]
    refine le_trans ?_ (le_trans hmain (measure_mono (Set.inter_subset_inter_right _ ?_)))
    · exact le_of_eq (by push_cast; ring)
    · have hrad : ((Kakeya.plankReduction.ballDilation : ℝ) * ((θ * b : ℝ≥0) : ℝ))
          = ((redPlankTube.ballDilation : ℝ) * (θ : ℝ) * (b : ℝ)) := by
        simp [Kakeya.plankReduction.ballDilation, redPlankTube.ballDilation]
        ring
      rw [hrad]

/-! ## The target in the small-radius regime -/

/-- **`ShadedPlank.reduction_to_slab_atTypicalAngle` modulo one scalar inequality in the
parameters alone.**

The target statement of `Section6Compat.lean` verbatim — same binders, same hypotheses, same
`128 * ε ≤ ε'`, same conclusion — with exactly one hypothesis inserted just before the conclusion,
and proved.  The inserted hypothesis is

```
432 · δ ^ ε' · a ^ (4η) · a ^ ε · C · θ b ≤ a ^ η · a,
```

an inequality between the *parameters* `δ, a, b, θ, C` only: unlike the obligations of
`Section6CompatDense.lean` and `Section6CompatThicken.lean` it mentions no set, no volume and no
feature of the configuration whatsoever. -/
theorem reduction_to_slab_atTypicalAngle_of_smallRadius :
    ∀ {η ε ε' : ℝ}, 0 < η → 0 < ε → 0 < ε' → 128 * ε ≤ ε' →
    ∀ (Ccard : ℝ≥0) (D : ℝ),
    ∃ δthr : ℝ≥0, 0 < δthr ∧ δthr ≤ 1 ∧
    ∀ {ι : Type*} (s : Finset ι)
      {δ a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
      (Y : ι → ShadedPlank a b hab hb1)
      (θ : ℝ≥0) (_hθ1 : θ ≤ 1) (C : ℝ≥0)
      (Y'' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3))),
      0 < δ → δ ≤ a → a < 1 → δ ≤ δthr →
      Plank.IsWindowedFamily s (ShadedPlank.planks Y) →
      a ^ η ≤ ShadedBody.fullness s (ShadedPlank.bodies Y) →
      (a : ENNReal) ^ (-η) ≤ ShadedBody.multiplicity s (ShadedPlank.bodies Y) →
      (δ : ENNReal) ^ (-η) ≤ ShadedBody.multiplicity s (ShadedPlank.bodies Y) →
      2 ≤ (δ : ENNReal) ^ (-η) →
      (s.card : ℝ≥0) ≤ Ccard * δ ^ (-D) →
      a / b ≤ θ → 1 ≤ C → C ≤ δ ^ (-ε) →
      ShadedBody.IsCRefinement s Y'' s (ShadedPlank.bodies Y) C⁻¹ →
      ShadedBody.HasCConstantMultiplicity s Y'' C →
      Kakeya.IsTypicalPlankAngle s Y'' (ShadedPlank.planks Y) θ C
        (Real.toNNReal (Kakeya.plankAngleScaleA a)) →
      Kakeya.HasMaxPlankAngleBound s Y'' (ShadedPlank.planks Y) θ 1 →
      (432 * ((δ : ℝ≥0) ^ ε' * a ^ (4 * η) * a ^ ε) * C * (θ * b) ≤ a ^ η * a) →
    ∃ (s' : Finset ι)
      (Y' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
      (c1 : ℝ≥0),
      0 < c1 ∧
      ShadedBody.IsRefinement s' Y' s (ShadedPlank.bodies Y) ∧
      ShadedBody.IsRefinement s' Y' s Y'' ∧
      (c1 * a ^ ε) * ShadedBody.fullness s (ShadedPlank.bodies Y) ≤
        ShadedBody.fullness s' Y' ∧
      (∀ x,
        ((⋃ i ∈ s', (Y' i).shade) ∩ Metric.closedBall x ((θ * b : ℝ))).Nonempty →
        (c1 : ENNReal) * (a : ENNReal) ^ (4 * η) * (a : ENNReal) ^ ε *
            volume (Metric.closedBall x ((θ * b : ℝ))) ≤
          volume ((⋃ i ∈ s', (Y' i).shade) ∩
            Metric.closedBall x (redPlankTube.ballDilation * θ * b))) ∧
      c1⁻¹ ≤ δ ^ (-ε') := by
  intro η ε ε' hη hε hε' hgap Ccard D
  classical
  refine ⟨(432 : ℝ≥0) ^ (-(1 / ε)), NNReal.rpow_pos (by norm_num), ?_, ?_⟩
  · exact NNReal.rpow_le_one_of_one_le_of_nonpos (by norm_num)
      (neg_nonpos.mpr (by positivity : (0 : ℝ) ≤ 1 / ε))
  intro ι s δ a b hab hb1 Y θ _hθ1 C Y'' hδ hδa ha1 hδthr _hwin hfull _hma _hmd _h2 _hcard
    hθlb hC1 hCδ hYref _hYmult _htyp hmaxA hsmall
  have ha : (0 : ℝ≥0) < a := lt_of_lt_of_le hδ hδa
  have hb : (0 : ℝ≥0) < b := lt_of_lt_of_le ha hab
  have hδne : (δ : ℝ≥0) ≠ 0 := hδ.ne'
  have hδ1 : (δ : ℝ≥0) ≤ 1 := le_trans hδa ha1.le
  have hθ : (0 : ℝ≥0) < θ := lt_of_lt_of_le (by positivity) hθlb
  have haθb : a ≤ θ * b := by
    have h := mul_le_mul_right' hθlb b
    rwa [div_mul_cancel₀ _ hb.ne'] at h
  have hlam : 0 < ShadedBody.fullness s (ShadedPlank.bodies Y) :=
    lt_of_lt_of_le (NNReal.rpow_pos ha) hfull
  have hsne : s.Nonempty := by
    rcases Finset.eq_empty_or_nonempty s with hs | hs
    · exfalso
      have hz : ShadedBody.fullness s (ShadedPlank.bodies Y) = 0 := by simp [hs]
      rw [hz] at hlam
      exact absurd rfl hlam.ne'
    · exact hs
  -- the threshold buys the refinement ledger
  have hδeps : (δ : ℝ≥0) ^ ε ≤ (432 : ℝ≥0)⁻¹ := by
    have hthr : (δ : ℝ≥0) ^ ε ≤ ((432 : ℝ≥0) ^ (-(1 / ε))) ^ ε := NNReal.rpow_le_rpow hδthr hε.le
    have hval : ((432 : ℝ≥0) ^ (-(1 / ε))) ^ ε = (432 : ℝ≥0)⁻¹ := by
      rw [← NNReal.rpow_mul, show (-(1 / ε)) * ε = (-1 : ℝ) by field_simp, NNReal.rpow_neg,
        NNReal.rpow_one]
    rwa [hval] at hthr
  have hshrink : (δ : ℝ≥0) ^ ε' * C ≤ (δ : ℝ≥0) ^ ε := by
    have hstep : (δ : ℝ≥0) ^ ε' * C ≤ (δ : ℝ≥0) ^ ε' * δ ^ (-ε) := by gcongr
    have hsimp : (δ : ℝ≥0) ^ ε' * δ ^ (-ε) = (δ : ℝ≥0) ^ (ε' - ε) := by
      rw [← NNReal.rpow_add hδne]; ring_nf
    have hge : (δ : ℝ≥0) ^ (ε' - ε) ≤ (δ : ℝ≥0) ^ ε :=
      NNReal.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
    calc (δ : ℝ≥0) ^ ε' * C ≤ (δ : ℝ≥0) ^ ε' * δ ^ (-ε) := hstep
      _ = (δ : ℝ≥0) ^ (ε' - ε) := hsimp
      _ ≤ (δ : ℝ≥0) ^ ε := hge
  have hledger : 2 * ((δ : ℝ≥0) ^ ε' * a ^ ε) * C ≤ 1 := by
    have haε : (a : ℝ≥0) ^ ε ≤ 1 := NNReal.rpow_le_one ha1.le hε.le
    calc 2 * ((δ : ℝ≥0) ^ ε' * a ^ ε) * C = 2 * (a ^ ε) * ((δ : ℝ≥0) ^ ε' * C) := by ring
      _ ≤ 2 * 1 * ((δ : ℝ≥0) ^ ε) := by gcongr
      _ ≤ 2 * 1 * (432 : ℝ≥0)⁻¹ := by gcongr
      _ ≤ 1 := by
          rw [← NNReal.coe_le_coe]
          push_cast
          norm_num
  have hbudget : 432 * ((δ : ℝ≥0) ^ ε' * a ^ (4 * η) * a ^ ε) * C * (θ * b)
      ≤ ShadedBody.fullness s (ShadedPlank.bodies Y) * a := by
    refine le_trans hsmall ?_
    gcongr
  obtain ⟨s', Y', href1, href2, hfullret, hitem1⟩ :=
    reduction_atTypicalAngle_singlePlank (η := η) (ε := ε) s hsne Y Y'' θ ((δ : ℝ≥0) ^ ε') C
      hC1 ha hb hb1 hθ _hθ1 haθb hlam hYref hledger hbudget
  refine ⟨s', Y', (δ : ℝ≥0) ^ ε', NNReal.rpow_pos hδ, href1, href2, hfullret, ?_, ?_⟩
  · intro x hx
    have hco : (((δ : ℝ≥0) ^ ε' * a ^ (4 * η) * a ^ ε : ℝ≥0) : ENNReal)
        = (((δ : ℝ≥0) ^ ε' : ℝ≥0) : ENNReal) * (a : ENNReal) ^ (4 * η)
            * (a : ENNReal) ^ ε := by
      rw [ENNReal.coe_mul, ENNReal.coe_mul,
        ENNReal.coe_rpow_of_nonneg _ (by positivity : (0 : ℝ) ≤ 4 * η),
        ENNReal.coe_rpow_of_nonneg _ hε.le]
    rw [← hco]
    exact hitem1 x hx
  · rw [NNReal.rpow_neg]

/-- **The target holds outright in the small-radius regime `θ b ≤ a ^ (1 - 3η - ε)`.**

`ShadedPlank.reduction_to_slab_atTypicalAngle` verbatim, with the single extra hypothesis
`θ * b ≤ a ^ (1 - 3 * η - ε)` — a comparison of the two *scales* only.  Since `a / b ≤ θ` forces
`a ≤ θ b`, and `a ≤ a ^ (1 - 3η - ε)` for `0 < a < 1`, this is a genuine, nonempty band of
radii, and it contains the smallest admissible one: **at the minimal angle `θ = a / b` the
hypothesis is automatic**, so the narrow-angle case of GWZ Lemma 6.13 at a prescribed typical
angle is proved here with no obligation at all.

The complementary regime `θ b > a ^ (1 - 3η - ε)` — the wide-angle case — is what remains open
at `Section6Compat.lean`. -/
theorem reduction_to_slab_atTypicalAngle_of_radius_le :
    ∀ {η ε ε' : ℝ}, 0 < η → 0 < ε → 0 < ε' → 128 * ε ≤ ε' →
    ∀ (Ccard : ℝ≥0) (D : ℝ),
    ∃ δthr : ℝ≥0, 0 < δthr ∧ δthr ≤ 1 ∧
    ∀ {ι : Type*} (s : Finset ι)
      {δ a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
      (Y : ι → ShadedPlank a b hab hb1)
      (θ : ℝ≥0) (_hθ1 : θ ≤ 1) (C : ℝ≥0)
      (Y'' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3))),
      0 < δ → δ ≤ a → a < 1 → δ ≤ δthr →
      Plank.IsWindowedFamily s (ShadedPlank.planks Y) →
      a ^ η ≤ ShadedBody.fullness s (ShadedPlank.bodies Y) →
      (a : ENNReal) ^ (-η) ≤ ShadedBody.multiplicity s (ShadedPlank.bodies Y) →
      (δ : ENNReal) ^ (-η) ≤ ShadedBody.multiplicity s (ShadedPlank.bodies Y) →
      2 ≤ (δ : ENNReal) ^ (-η) →
      (s.card : ℝ≥0) ≤ Ccard * δ ^ (-D) →
      a / b ≤ θ → 1 ≤ C → C ≤ δ ^ (-ε) →
      ShadedBody.IsCRefinement s Y'' s (ShadedPlank.bodies Y) C⁻¹ →
      ShadedBody.HasCConstantMultiplicity s Y'' C →
      Kakeya.IsTypicalPlankAngle s Y'' (ShadedPlank.planks Y) θ C
        (Real.toNNReal (Kakeya.plankAngleScaleA a)) →
      Kakeya.HasMaxPlankAngleBound s Y'' (ShadedPlank.planks Y) θ 1 →
      (θ * b ≤ a ^ (1 - 3 * η - ε)) →
    ∃ (s' : Finset ι)
      (Y' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
      (c1 : ℝ≥0),
      0 < c1 ∧
      ShadedBody.IsRefinement s' Y' s (ShadedPlank.bodies Y) ∧
      ShadedBody.IsRefinement s' Y' s Y'' ∧
      (c1 * a ^ ε) * ShadedBody.fullness s (ShadedPlank.bodies Y) ≤
        ShadedBody.fullness s' Y' ∧
      (∀ x,
        ((⋃ i ∈ s', (Y' i).shade) ∩ Metric.closedBall x ((θ * b : ℝ))).Nonempty →
        (c1 : ENNReal) * (a : ENNReal) ^ (4 * η) * (a : ENNReal) ^ ε *
            volume (Metric.closedBall x ((θ * b : ℝ))) ≤
          volume ((⋃ i ∈ s', (Y' i).shade) ∩
            Metric.closedBall x (redPlankTube.ballDilation * θ * b))) ∧
      c1⁻¹ ≤ δ ^ (-ε') := by
  intro η ε ε' hη hε hε' hgap Ccard D
  obtain ⟨δthr₀, hδthr₀pos, hδthr₀1, hmain⟩ :=
    reduction_to_slab_atTypicalAngle_of_smallRadius hη hε hε' hgap Ccard D
  refine ⟨min δthr₀ ((432 : ℝ≥0) ^ (-(1 / ε))),
    lt_min hδthr₀pos (NNReal.rpow_pos (by norm_num)),
    le_trans (min_le_left _ _) hδthr₀1, ?_⟩
  intro ι s δ a b hab hb1 Y θ hθ1 C Y'' hδ hδa ha1 hδthr hwin hfull hma hmd h2 hcard
    hθlb hC1 hCδ hYref hYmult htyp hmaxA hrad
  have hδne : (δ : ℝ≥0) ≠ 0 := hδ.ne'
  have hδ1 : (δ : ℝ≥0) ≤ 1 := le_trans hδa ha1.le
  have ha : (0 : ℝ≥0) < a := lt_of_lt_of_le hδ hδa
  have hane : (a : ℝ≥0) ≠ 0 := ha.ne'
  have hδeps : (δ : ℝ≥0) ^ ε ≤ (432 : ℝ≥0)⁻¹ := by
    have hthr : (δ : ℝ≥0) ^ ε ≤ ((432 : ℝ≥0) ^ (-(1 / ε))) ^ ε :=
      NNReal.rpow_le_rpow (le_trans hδthr (min_le_right _ _)) hε.le
    have hval : ((432 : ℝ≥0) ^ (-(1 / ε))) ^ ε = (432 : ℝ≥0)⁻¹ := by
      rw [← NNReal.rpow_mul, show (-(1 / ε)) * ε = (-1 : ℝ) by field_simp, NNReal.rpow_neg,
        NNReal.rpow_one]
    rwa [hval] at hthr
  have hshrink : (δ : ℝ≥0) ^ ε' * C ≤ (δ : ℝ≥0) ^ ε := by
    have hstep : (δ : ℝ≥0) ^ ε' * C ≤ (δ : ℝ≥0) ^ ε' * δ ^ (-ε) := by gcongr
    have hsimp : (δ : ℝ≥0) ^ ε' * δ ^ (-ε) = (δ : ℝ≥0) ^ (ε' - ε) := by
      rw [← NNReal.rpow_add hδne]; ring_nf
    have hge : (δ : ℝ≥0) ^ (ε' - ε) ≤ (δ : ℝ≥0) ^ ε :=
      NNReal.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
    calc (δ : ℝ≥0) ^ ε' * C ≤ (δ : ℝ≥0) ^ ε' * δ ^ (-ε) := hstep
      _ = (δ : ℝ≥0) ^ (ε' - ε) := hsimp
      _ ≤ (δ : ℝ≥0) ^ ε := hge
  have hpow : (a : ℝ≥0) ^ (4 * η) * a ^ ε * a ^ (1 - 3 * η - ε) = a ^ η * a := by
    rw [← NNReal.rpow_add hane, ← NNReal.rpow_add hane,
      show 4 * η + ε + (1 - 3 * η - ε) = η + 1 by ring, NNReal.rpow_add hane, NNReal.rpow_one]
  have hsmall : 432 * ((δ : ℝ≥0) ^ ε' * a ^ (4 * η) * a ^ ε) * C * (θ * b) ≤ a ^ η * a := by
    calc 432 * ((δ : ℝ≥0) ^ ε' * a ^ (4 * η) * a ^ ε) * C * (θ * b)
        = (432 * ((δ : ℝ≥0) ^ ε' * C)) * ((a : ℝ≥0) ^ (4 * η) * a ^ ε * (θ * b)) := by ring
      _ ≤ (432 * (δ : ℝ≥0) ^ ε)
            * ((a : ℝ≥0) ^ (4 * η) * a ^ ε * a ^ (1 - 3 * η - ε)) := by gcongr
      _ = (432 * (δ : ℝ≥0) ^ ε) * ((a : ℝ≥0) ^ η * a) := by rw [hpow]
      _ ≤ (432 * (432 : ℝ≥0)⁻¹) * ((a : ℝ≥0) ^ η * a) := by gcongr
      _ = (a : ℝ≥0) ^ η * a := by
          rw [mul_inv_cancel₀ (by norm_num : (432 : ℝ≥0) ≠ 0), one_mul]
  exact hmain s Y θ hθ1 C Y'' hδ hδa ha1 (le_trans hδthr (min_le_left _ _)) hwin hfull hma
    hmd h2 hcard hθlb hC1 hCδ hYref hYmult htyp hmaxA hsmall

/-! ## What is left: the wide-angle regime -/

/-- **The target reduces to the wide-angle regime.**

The hypothesis `H` is `ShadedPlank.reduction_to_slab_atTypicalAngle` with the single extra
hypothesis `a ^ (1 - 3η - ε) < θ * b`; the conclusion is the target *verbatim*, copied from
`Section6Compat.lean` with only `Type*` written as `Type u` so that the two occurrences share a
universe.  So this is a machine-checked certificate that the whole remaining content of
`ShadedPlank.reduction_to_slab_atTypicalAngle` sits in the wide-angle regime: the complementary
regime `θ b ≤ a ^ (1 - 3η - ε)` is discharged here by
`ShadedPlank.reduction_to_slab_atTypicalAngle_of_radius_le`, with no obligation.

`H` is a hypothesis of this theorem, not a new leaf: nothing below it is asserted. -/
theorem reduction_to_slab_atTypicalAngle_of_wideAngle.{u}
    (H :
    ∀ {η ε ε' : ℝ}, 0 < η → 0 < ε → 0 < ε' → 128 * ε ≤ ε' →
    ∀ (Ccard : ℝ≥0) (D : ℝ),
    ∃ δthr : ℝ≥0, 0 < δthr ∧ δthr ≤ 1 ∧
    ∀ {ι : Type u} (s : Finset ι)
      {δ a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
      (Y : ι → ShadedPlank a b hab hb1)
      (θ : ℝ≥0) (_hθ1 : θ ≤ 1) (C : ℝ≥0)
      (Y'' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3))),
      0 < δ → δ ≤ a → a < 1 → δ ≤ δthr →
      Plank.IsWindowedFamily s (ShadedPlank.planks Y) →
      a ^ η ≤ ShadedBody.fullness s (ShadedPlank.bodies Y) →
      (a : ENNReal) ^ (-η) ≤ ShadedBody.multiplicity s (ShadedPlank.bodies Y) →
      (δ : ENNReal) ^ (-η) ≤ ShadedBody.multiplicity s (ShadedPlank.bodies Y) →
      2 ≤ (δ : ENNReal) ^ (-η) →
      (s.card : ℝ≥0) ≤ Ccard * δ ^ (-D) →
      a / b ≤ θ → 1 ≤ C → C ≤ δ ^ (-ε) →
      ShadedBody.IsCRefinement s Y'' s (ShadedPlank.bodies Y) C⁻¹ →
      ShadedBody.HasCConstantMultiplicity s Y'' C →
      Kakeya.IsTypicalPlankAngle s Y'' (ShadedPlank.planks Y) θ C
        (Real.toNNReal (Kakeya.plankAngleScaleA a)) →
      Kakeya.HasMaxPlankAngleBound s Y'' (ShadedPlank.planks Y) θ 1 →
      (a ^ (1 - 3 * η - ε) < θ * b) →
    ∃ (s' : Finset ι)
      (Y' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
      (c1 : ℝ≥0),
      0 < c1 ∧
      ShadedBody.IsRefinement s' Y' s (ShadedPlank.bodies Y) ∧
      ShadedBody.IsRefinement s' Y' s Y'' ∧
      (c1 * a ^ ε) * ShadedBody.fullness s (ShadedPlank.bodies Y) ≤
        ShadedBody.fullness s' Y' ∧
      (∀ x,
        ((⋃ i ∈ s', (Y' i).shade) ∩ Metric.closedBall x ((θ * b : ℝ))).Nonempty →
        (c1 : ENNReal) * (a : ENNReal) ^ (4 * η) * (a : ENNReal) ^ ε *
            volume (Metric.closedBall x ((θ * b : ℝ))) ≤
          volume ((⋃ i ∈ s', (Y' i).shade) ∩
            Metric.closedBall x (redPlankTube.ballDilation * θ * b))) ∧
      c1⁻¹ ≤ δ ^ (-ε')) :
    ∀ {η ε ε' : ℝ}, 0 < η → 0 < ε → 0 < ε' → 128 * ε ≤ ε' →
    ∀ (Ccard : ℝ≥0) (D : ℝ),
    ∃ δthr : ℝ≥0, 0 < δthr ∧ δthr ≤ 1 ∧
    ∀ {ι : Type u} (s : Finset ι)
      {δ a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
      (Y : ι → ShadedPlank a b hab hb1)
      (θ : ℝ≥0) (_hθ1 : θ ≤ 1) (C : ℝ≥0)
      (Y'' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3))),
      0 < δ → δ ≤ a → a < 1 → δ ≤ δthr →
      Plank.IsWindowedFamily s (ShadedPlank.planks Y) →
      a ^ η ≤ ShadedBody.fullness s (ShadedPlank.bodies Y) →
      (a : ENNReal) ^ (-η) ≤ ShadedBody.multiplicity s (ShadedPlank.bodies Y) →
      (δ : ENNReal) ^ (-η) ≤ ShadedBody.multiplicity s (ShadedPlank.bodies Y) →
      2 ≤ (δ : ENNReal) ^ (-η) →
      (s.card : ℝ≥0) ≤ Ccard * δ ^ (-D) →
      a / b ≤ θ → 1 ≤ C → C ≤ δ ^ (-ε) →
      ShadedBody.IsCRefinement s Y'' s (ShadedPlank.bodies Y) C⁻¹ →
      ShadedBody.HasCConstantMultiplicity s Y'' C →
      Kakeya.IsTypicalPlankAngle s Y'' (ShadedPlank.planks Y) θ C
        (Real.toNNReal (Kakeya.plankAngleScaleA a)) →
      Kakeya.HasMaxPlankAngleBound s Y'' (ShadedPlank.planks Y) θ 1 →
    ∃ (s' : Finset ι)
      (Y' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
      (c1 : ℝ≥0),
      0 < c1 ∧
      ShadedBody.IsRefinement s' Y' s (ShadedPlank.bodies Y) ∧
      ShadedBody.IsRefinement s' Y' s Y'' ∧
      (c1 * a ^ ε) * ShadedBody.fullness s (ShadedPlank.bodies Y) ≤
        ShadedBody.fullness s' Y' ∧
      (∀ x,
        ((⋃ i ∈ s', (Y' i).shade) ∩ Metric.closedBall x ((θ * b : ℝ))).Nonempty →
        (c1 : ENNReal) * (a : ENNReal) ^ (4 * η) * (a : ENNReal) ^ ε *
            volume (Metric.closedBall x ((θ * b : ℝ))) ≤
          volume ((⋃ i ∈ s', (Y' i).shade) ∩
            Metric.closedBall x (redPlankTube.ballDilation * θ * b))) ∧
      c1⁻¹ ≤ δ ^ (-ε') := by
  intro η ε ε' hη hε hε' hgap Ccard D
  obtain ⟨δ₁, hδ₁pos, hδ₁one, hnarrow⟩ :=
    reduction_to_slab_atTypicalAngle_of_radius_le hη hε hε' hgap Ccard D
  obtain ⟨δ₂, hδ₂pos, hδ₂one, hwide⟩ := H hη hε hε' hgap Ccard D
  refine ⟨min δ₁ δ₂, lt_min hδ₁pos hδ₂pos, le_trans (min_le_left _ _) hδ₁one, ?_⟩
  intro ι s δ a b hab hb1 Y θ hθ1 C Y'' hδ hδa ha1 hδthr hwin hfull hma hmd h2 hcard
    hθlb hC1 hCδ hYref hYmult htyp hmaxA
  by_cases hcase : θ * b ≤ a ^ (1 - 3 * η - ε)
  · exact hnarrow s Y θ hθ1 C Y'' hδ hδa ha1 (le_trans hδthr (min_le_left _ _)) hwin hfull
      hma hmd h2 hcard hθlb hC1 hCδ hYref hYmult htyp hmaxA hcase
  · exact hwide s Y θ hθ1 C Y'' hδ hδa ha1 (le_trans hδthr (min_le_right _ _)) hwin hfull
      hma hmd h2 hcard hθlb hC1 hCδ hYref hYmult htyp hmaxA (not_le.mp hcase)

/-- **The sharpest form of the same reduction: the target reduces to the case where the scalar
budget of `ShadedPlank.reduction_to_slab_atTypicalAngle_of_smallRadius` *fails*.**

`H` is the target with the single extra hypothesis
`a ^ η · a < 432 · δ ^ ε' · a ^ (4η) · a ^ ε · C · θ b`; the conclusion is the target verbatim.
This residual is strictly smaller than the wide-angle one of
`ShadedPlank.reduction_to_slab_atTypicalAngle_of_wideAngle`, and it is the one that carries
quantitative information: with `θ b ≤ 1`, `δ ^ ε' · C ≤ δ ^ (ε' - ε) ≤ δ ^ ε` and `2 ε ≤ ε'` it
forces `δ > (a ^ (1 - 3η - ε) / 432) ^ (1/ε)`, hence `C ≤ δ ^ (-ε) < 432 · a ^ (-(1 - 3η - ε))`:
in the open region the comparability constant is a **bounded** power of `a`.

`H` is a hypothesis, not a new leaf. -/
theorem reduction_to_slab_atTypicalAngle_of_budgetExcess.{u}
    (H :
    ∀ {η ε ε' : ℝ}, 0 < η → 0 < ε → 0 < ε' → 128 * ε ≤ ε' →
    ∀ (Ccard : ℝ≥0) (D : ℝ),
    ∃ δthr : ℝ≥0, 0 < δthr ∧ δthr ≤ 1 ∧
    ∀ {ι : Type u} (s : Finset ι)
      {δ a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
      (Y : ι → ShadedPlank a b hab hb1)
      (θ : ℝ≥0) (_hθ1 : θ ≤ 1) (C : ℝ≥0)
      (Y'' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3))),
      0 < δ → δ ≤ a → a < 1 → δ ≤ δthr →
      Plank.IsWindowedFamily s (ShadedPlank.planks Y) →
      a ^ η ≤ ShadedBody.fullness s (ShadedPlank.bodies Y) →
      (a : ENNReal) ^ (-η) ≤ ShadedBody.multiplicity s (ShadedPlank.bodies Y) →
      (δ : ENNReal) ^ (-η) ≤ ShadedBody.multiplicity s (ShadedPlank.bodies Y) →
      2 ≤ (δ : ENNReal) ^ (-η) →
      (s.card : ℝ≥0) ≤ Ccard * δ ^ (-D) →
      a / b ≤ θ → 1 ≤ C → C ≤ δ ^ (-ε) →
      ShadedBody.IsCRefinement s Y'' s (ShadedPlank.bodies Y) C⁻¹ →
      ShadedBody.HasCConstantMultiplicity s Y'' C →
      Kakeya.IsTypicalPlankAngle s Y'' (ShadedPlank.planks Y) θ C
        (Real.toNNReal (Kakeya.plankAngleScaleA a)) →
      Kakeya.HasMaxPlankAngleBound s Y'' (ShadedPlank.planks Y) θ 1 →
      (a ^ η * a < 432 * ((δ : ℝ≥0) ^ ε' * a ^ (4 * η) * a ^ ε) * C * (θ * b)) →
    ∃ (s' : Finset ι)
      (Y' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
      (c1 : ℝ≥0),
      0 < c1 ∧
      ShadedBody.IsRefinement s' Y' s (ShadedPlank.bodies Y) ∧
      ShadedBody.IsRefinement s' Y' s Y'' ∧
      (c1 * a ^ ε) * ShadedBody.fullness s (ShadedPlank.bodies Y) ≤
        ShadedBody.fullness s' Y' ∧
      (∀ x,
        ((⋃ i ∈ s', (Y' i).shade) ∩ Metric.closedBall x ((θ * b : ℝ))).Nonempty →
        (c1 : ENNReal) * (a : ENNReal) ^ (4 * η) * (a : ENNReal) ^ ε *
            volume (Metric.closedBall x ((θ * b : ℝ))) ≤
          volume ((⋃ i ∈ s', (Y' i).shade) ∩
            Metric.closedBall x (redPlankTube.ballDilation * θ * b))) ∧
      c1⁻¹ ≤ δ ^ (-ε')) :
    ∀ {η ε ε' : ℝ}, 0 < η → 0 < ε → 0 < ε' → 128 * ε ≤ ε' →
    ∀ (Ccard : ℝ≥0) (D : ℝ),
    ∃ δthr : ℝ≥0, 0 < δthr ∧ δthr ≤ 1 ∧
    ∀ {ι : Type u} (s : Finset ι)
      {δ a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
      (Y : ι → ShadedPlank a b hab hb1)
      (θ : ℝ≥0) (_hθ1 : θ ≤ 1) (C : ℝ≥0)
      (Y'' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3))),
      0 < δ → δ ≤ a → a < 1 → δ ≤ δthr →
      Plank.IsWindowedFamily s (ShadedPlank.planks Y) →
      a ^ η ≤ ShadedBody.fullness s (ShadedPlank.bodies Y) →
      (a : ENNReal) ^ (-η) ≤ ShadedBody.multiplicity s (ShadedPlank.bodies Y) →
      (δ : ENNReal) ^ (-η) ≤ ShadedBody.multiplicity s (ShadedPlank.bodies Y) →
      2 ≤ (δ : ENNReal) ^ (-η) →
      (s.card : ℝ≥0) ≤ Ccard * δ ^ (-D) →
      a / b ≤ θ → 1 ≤ C → C ≤ δ ^ (-ε) →
      ShadedBody.IsCRefinement s Y'' s (ShadedPlank.bodies Y) C⁻¹ →
      ShadedBody.HasCConstantMultiplicity s Y'' C →
      Kakeya.IsTypicalPlankAngle s Y'' (ShadedPlank.planks Y) θ C
        (Real.toNNReal (Kakeya.plankAngleScaleA a)) →
      Kakeya.HasMaxPlankAngleBound s Y'' (ShadedPlank.planks Y) θ 1 →
    ∃ (s' : Finset ι)
      (Y' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
      (c1 : ℝ≥0),
      0 < c1 ∧
      ShadedBody.IsRefinement s' Y' s (ShadedPlank.bodies Y) ∧
      ShadedBody.IsRefinement s' Y' s Y'' ∧
      (c1 * a ^ ε) * ShadedBody.fullness s (ShadedPlank.bodies Y) ≤
        ShadedBody.fullness s' Y' ∧
      (∀ x,
        ((⋃ i ∈ s', (Y' i).shade) ∩ Metric.closedBall x ((θ * b : ℝ))).Nonempty →
        (c1 : ENNReal) * (a : ENNReal) ^ (4 * η) * (a : ENNReal) ^ ε *
            volume (Metric.closedBall x ((θ * b : ℝ))) ≤
          volume ((⋃ i ∈ s', (Y' i).shade) ∩
            Metric.closedBall x (redPlankTube.ballDilation * θ * b))) ∧
      c1⁻¹ ≤ δ ^ (-ε')  := by
  intro η ε ε' hη hε hε' hgap Ccard D
  obtain ⟨δ₁, hδ₁pos, hδ₁one, hnarrow⟩ :=
    reduction_to_slab_atTypicalAngle_of_smallRadius hη hε hε' hgap Ccard D
  obtain ⟨δ₂, hδ₂pos, hδ₂one, hwide⟩ := H hη hε hε' hgap Ccard D
  refine ⟨min δ₁ δ₂, lt_min hδ₁pos hδ₂pos, le_trans (min_le_left _ _) hδ₁one, ?_⟩
  intro ι s δ a b hab hb1 Y θ hθ1 C Y'' hδ hδa ha1 hδthr hwin hfull hma hmd h2 hcard
    hθlb hC1 hCδ hYref hYmult htyp hmaxA
  by_cases hcase : 432 * ((δ : ℝ≥0) ^ ε' * a ^ (4 * η) * a ^ ε) * C * (θ * b) ≤ a ^ η * a
  · exact hnarrow s Y θ hθ1 C Y'' hδ hδa ha1 (le_trans hδthr (min_le_left _ _)) hwin hfull
      hma hmd h2 hcard hθlb hC1 hCδ hYref hYmult htyp hmaxA hcase
  · exact hwide s Y θ hθ1 C Y'' hδ hδa ha1 (le_trans hδthr (min_le_right _ _)) hwin hfull
      hma hmd h2 hcard hθlb hC1 hCδ hYref hYmult htyp hmaxA (not_le.mp hcase)

end ShadedPlank

end
