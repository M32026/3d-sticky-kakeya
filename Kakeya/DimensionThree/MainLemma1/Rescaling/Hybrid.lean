/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Tube.Rescale
public import Kakeya.Tube.Dilate
public import Kakeya.Tube.IntersectionVolume

/-!
# The one container tube of item (iv): the container's direction at the member's centre

Item (iv) of `Kakeya.ml1Boot.exists_fineNormalization_lower` asks, for each output scale `ρt`
of the truncated window and each `k` of the output index set, for a single `ρt`-tube `T_ρ`
inside `B(0,1)` which

1. **contains the member** `T̃ k`,
2. **contains the rescaled source container** `Ψ(T_σ)` inside its `2`-dilate, and
3. carries the per-body enlargement `∀ i ∈ un, Ψ(U i) ≤ Ψ(T_σ) → T̃ i ≤ 2 · T_ρ`, pinned to
   `2 · T_ρ` and not merely to some enlargement of comparable volume.

The two routes the repository had each supply one half and lose the other.  The *member* route
(`Kakeya.ml1Boot.exists_container_tube_of_endpoints`) takes `T_ρ` to be the rescale of `T̃ k`,
keeping the member's direction, and then has no control over `Ψ(T_σ)`; the *container* route
(`Kakeya.ml1Boot.exists_rescaled_source_container`) takes `T_ρ` to be the centred extension of
`Ψ(T_σ)`'s core, keeping the container's direction, and then contains `Ψ(U k)` but not its
centred extension `T̃ k`.

Neither has to be given up.  `Kakeya.ml1Boot.exists_itemIV_container_tube` takes the
**container's direction at the member's centre**, and all three clauses hold, each of them
tightly:

* clause 1 by `Kakeya.ml1Boot.tube_subset_of_direction_close`, at the transverse-direction
  budget `2 (ρt - dt)`;
* clause 2 because `T_ρ` is then *parallel* to the container tube, so its whole transverse
  budget `2 ρt` pays the centre offset `ρt` plus the radius `ρt`;
* clause 3 with the budget spent as `ρt + (ρt - dt) + dt = 2 ρt`.

The transverse-direction budget `2 (ρt - dt)` — rather than `2 ρt` — is what makes clause 1
compatible with clauses 2 and 3, and it is available because a `τ`-tube whose *carrier* lies
inside a `σ`-tube has its core within `σ - τ`, not merely `σ`, of the container's axis, and
`(σ - τ) / θ = ρt - dt`.  Correspondingly `Kakeya.ml1Boot.tube_subset_of_direction_close` has
to be proved with the axial overshoot and the transverse excess combined by **Pythagoras**:
they are the two orthogonal components of one displacement of length `≤ dt`, and a triangle
inequality would ask for `2 (ρt - 2 dt)`, which the geometry does not supply.  The chain
`a₀ ^ 2 + ((ρt - dt) + b) ^ 2 ≤ dt ^ 2 + 2 (ρt - dt) dt + (ρt - dt) ^ 2 = ρt ^ 2` is an
equality in the extremal configuration, so no constant here is improvable.

## The fifth visibility clause, and where the hypotheses are discharged

The three clauses are stated against the *core data* — centre and direction — of the normalized
members `T̃ i`.  `Kakeya.ml1Boot.exists_fineNormalization` builds `T̃ i` as
`Tube.centredExtension (fineScale τ θ) (hxy i)` on the images of the core endpoints of `U i`,
and its conclusion **now** exposes that core data, as a fifth construction-visibility clause
beside the carrier containment, the shade equality and the volume bracket.  With it, every
hypothesis of `Kakeya.ml1Boot.exists_itemIV_container_tube` is discharged by
`Kakeya.ml1Boot.exists_itemIV_container_of_visibility` (Rescaling/Normalized.lean), which is
where item (iv)'s single container tube is now produced.  The clause is `rfl` in the
construction: writing `Ψ = Tτ.rescaleMap ((Tube.normalization.C 3 : NNReal) : ℝ)`,

```
∀ i ∈ un, (V i).center = midpoint ℝ (Ψ (T i).x) (Ψ (T i).y) ∧
  (V i).direction = ‖Ψ (T i).y - Ψ (T i).x‖⁻¹ • (Ψ (T i).y - Ψ (T i).x)
```

`Kakeya.ml1Boot.exists_fineNormalization` sets `V i` to
`Tube.centredExtension (fineScale δ τ) (hxy i)`, and
`Kakeya.ml1Boot.centredExtension_center_direction` computes both sides of that clause from
`Tube.ofMidpointDirection` by `rfl` up to `midpoint_eq_smul_add`.  Nothing is strengthened and
no constant moves.

Given that clause, the remaining hypotheses of
`Kakeya.ml1Boot.exists_itemIV_container_tube` are supplied by
`Kakeya.ml1Boot.norm_perp_centredExtension_direction_le` (the `hdir` clause, at
`σ = ρt θ`, `τ = dt θ`) and by transverse/axial bounds on the *centres*, which are the
`Ψ`-images of the midpoints of the source cores and so obey the same
`Kakeya.ml1Boot.norm_perp_core_le_of_carrier_subset` bound, divided by the homothety factor
`4 R ≥ 4`.
-/

@[expose] public section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

namespace Kakeya

namespace ml1Boot

section Hybrid

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The transverse part of `w` relative to a unit vector `g` is orthogonal to `g`. -/
theorem inner_perp_eq_zero {g : E} (hg : ‖g‖ = 1) (w : E) :
    (inner ℝ g (w - (inner ℝ g w : ℝ) • g) : ℝ) = 0 := by
  have he : (inner ℝ g g : ℝ) = 1 := by
    rw [real_inner_self_eq_norm_sq, hg]; norm_num
  rw [inner_sub_right, inner_smul_right, he]
  ring

/-- Pythagoras for the axial/transverse split along a unit vector `g`. -/
theorem norm_sq_axis_split {g : E} (hg : ‖g‖ = 1) (w : E) (t : ℝ) :
    ‖t • g + (w - (inner ℝ g w : ℝ) • g)‖ ^ 2
      = t ^ 2 + ‖w - (inner ℝ g w : ℝ) • g‖ ^ 2 := by
  have hz := inner_perp_eq_zero hg w
  have hcross : (inner ℝ (t • g) (w - (inner ℝ g w : ℝ) • g) : ℝ) = 0 := by
    rw [real_inner_smul_left, hz]; ring
  rw [norm_add_sq_real, hcross, norm_smul, hg]
  simp [Real.norm_eq_abs, sq_abs]

/-- The transverse part is no longer than the vector itself. -/
theorem norm_perp_le {g : E} (hg : ‖g‖ = 1) (w : E) :
    ‖w - (inner ℝ g w : ℝ) • g‖ ≤ ‖w‖ := by
  have h := norm_sq_axis_split hg w (inner ℝ g w : ℝ)
  have hw : (inner ℝ g w : ℝ) • g + (w - (inner ℝ g w : ℝ) • g) = w := by abel
  rw [hw] at h
  nlinarith [norm_nonneg (w - (inner ℝ g w : ℝ) • g), norm_nonneg w,
    sq_nonneg (inner ℝ g w : ℝ)]

/-- The axial component is no longer than the vector itself. -/
theorem abs_inner_le {g : E} (hg : ‖g‖ = 1) (w : E) :
    |(inner ℝ g w : ℝ)| ≤ ‖w‖ := by
  have h := abs_real_inner_le_norm g w
  rwa [hg, one_mul] at h

/-- Additivity of the transverse part. -/
theorem perp_add {g : E} (w w' : E) :
    ((w + w') - (inner ℝ g (w + w') : ℝ) • g)
      = (w - (inner ℝ g w : ℝ) • g) + (w' - (inner ℝ g w' : ℝ) • g) := by
  rw [inner_add_right, add_smul]; module

/-- Homogeneity of the transverse part. -/
theorem perp_smul {g : E} (w : E) (l : ℝ) :
    ((l • w) - (inner ℝ g (l • w) : ℝ) • g) = l • (w - (inner ℝ g w : ℝ) • g) := by
  rw [real_inner_smul_right, smul_sub, smul_smul]

/-- The transverse part of a multiple of the reference direction vanishes. -/
theorem perp_smul_self {g : E} (hg : ‖g‖ = 1) (l : ℝ) :
    ((l • g) - (inner ℝ g (l • g) : ℝ) • g) = 0 := by
  have he : (inner ℝ g g : ℝ) = 1 := by rw [real_inner_self_eq_norm_sq, hg]; norm_num
  rw [real_inner_smul_right, he, mul_one, sub_self]

/-- Subtractivity of the transverse part. -/
theorem perp_sub {g : E} (w w' : E) :
    ((w - w') - (inner ℝ g (w - w') : ℝ) • g)
      = (w - (inner ℝ g w : ℝ) • g) - (w' - (inner ℝ g w' : ℝ) • g) := by
  rw [inner_sub_right, sub_smul]; module

/-- Pythagoras for a decomposition into a multiple of `g` and a vector orthogonal to `g`. -/
theorem norm_sq_add_orthogonal {g : E} (hg : ‖g‖ = 1) {p : E}
    (hp : (inner ℝ g p : ℝ) = 0) (t : ℝ) : ‖t • g + p‖ ^ 2 = t ^ 2 + ‖p‖ ^ 2 := by
  have hcross : (inner ℝ (t • g) p : ℝ) = 0 := by rw [real_inner_smul_left, hp]; ring
  rw [norm_add_sq_real, hcross, norm_smul, hg]
  simp [Real.norm_eq_abs, sq_abs]

end Hybrid

section HybridTube

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

omit [MeasurableSpace E] [BorelSpace E] in
/-- **Membership in a dilate from axial/transverse bounds, Pythagorean form.**

If the axial coordinate of `z` relative to the axis of `Tρ` overshoots the half-length `c / 2`
of the `c`-dilate by at most `A`, and its transverse coordinate is at most `P`, then `z` lies in
`c · Tρ` as soon as `A ^ 2 + P ^ 2 ≤ (c ρ) ^ 2`.

The two errors are combined by Pythagoras rather than by the triangle inequality, which is what
makes the constants of `Kakeya.ml1Boot.tube_subset_of_direction_close` sharp: there the axial
overshoot and the transverse excess come from orthogonal components of one and the same
displacement of length `≤ dt`, and a triangle-inequality combination would lose exactly the
`dt` that clause (iv) has no room for. -/
theorem mem_dilate_of_axis_bounds {ρ : NNReal} (Tρ : Tube ρ E) {c : ℝ} (hc : 0 < c)
    {z : E} {A P : ℝ} (hA : 0 ≤ A)
    (haxial : |(inner ℝ Tρ.direction (z - Tρ.center) : ℝ)| ≤ c / 2 + A)
    (hperp : ‖(z - Tρ.center) - (inner ℝ Tρ.direction (z - Tρ.center) : ℝ) • Tρ.direction‖ ≤ P)
    (hbound : A ^ 2 + P ^ 2 ≤ (c * (ρ : ℝ)) ^ 2) :
    z ∈ (Kakeya.Tube.dilate Tρ c).carrier := by
  have hg : ‖Tρ.direction‖ = 1 := Tρ.norm_direction
  set g : E := Tρ.direction with hgdef
  set a : ℝ := (inner ℝ g (z - Tρ.center) : ℝ) with hadef
  set s : ℝ := max (-(c / 2)) (min (c / 2) a) with hsdef
  have hc2 : (0 : ℝ) < c / 2 := by linarith
  have hs : |s| ≤ c / 2 := by
    rw [abs_le]
    constructor
    · exact le_max_left _ _
    · exact max_le (by linarith) (min_le_left _ _)
  have hP0 : (0 : ℝ) ≤ P := le_trans (norm_nonneg _) hperp
  have hdiff : |a - s| ≤ A := by
    rcases le_or_gt a (-(c / 2)) with h | h
    · have hmin : min (c / 2) a = a := min_eq_right (by linarith)
      have : s = -(c / 2) := by rw [hsdef, hmin]; exact max_eq_left (by linarith)
      rw [this, abs_le]
      have := (abs_le.mp haxial).1
      constructor <;> linarith
    · rcases le_or_gt a (c / 2) with h2 | h2
      · have hmin : min (c / 2) a = a := min_eq_right h2
        have : s = a := by rw [hsdef, hmin]; exact max_eq_right (by linarith)
        rw [this]; simpa using hA
      · have hmin : min (c / 2) a = c / 2 := min_eq_left (le_of_lt h2)
        have : s = c / 2 := by rw [hsdef, hmin]; exact max_eq_right (by linarith)
        rw [this, abs_le]
        have := (abs_le.mp haxial).2
        constructor <;> linarith
  have hsplit : z - (Tρ.center + s • g) = (a - s) • g + ((z - Tρ.center) - a • g) := by
    module
  have hnormsq : ‖z - (Tρ.center + s • g)‖ ^ 2
      = (a - s) ^ 2 + ‖(z - Tρ.center) - a • g‖ ^ 2 := by
    rw [hsplit]
    exact norm_sq_axis_split hg (z - Tρ.center) (a - s)
  have hle : ‖z - (Tρ.center + s • g)‖ ≤ c * (ρ : ℝ) := by
    have hcρ : (0 : ℝ) ≤ c * (ρ : ℝ) := by positivity
    have hsq : ‖z - (Tρ.center + s • g)‖ ^ 2 ≤ (c * (ρ : ℝ)) ^ 2 := by
      rw [hnormsq]
      have h1 : (a - s) ^ 2 ≤ A ^ 2 := by
        rw [← sq_abs (a - s)]
        exact pow_le_pow_left₀ (abs_nonneg _) hdiff 2
      have h2 : ‖(z - Tρ.center) - a • g‖ ^ 2 ≤ P ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hperp 2
      linarith
    nlinarith [norm_nonneg (z - (Tρ.center + s • g))]
  refine Kakeya.Tube.mem_dilate_of_dist_axis_le Tρ hc hs ?_
  rwa [dist_eq_norm]

omit [MeasurableSpace E] [BorelSpace E] in
/-- The `1`-dilate of a tube is the tube. -/
theorem dilate_one_carrier {δ : NNReal} (T : Tube δ E) :
    (Kakeya.Tube.dilate T 1).carrier = T.carrier := by
  rw [Kakeya.Tube.dilate_carrier]
  simp

omit [MeasurableSpace E] [BorelSpace E] in
/-- `Kakeya.ml1Boot.mem_dilate_of_axis_bounds` at `c = 1`, landing in the tube itself. -/
theorem mem_carrier_of_axis_bounds {ρ : NNReal} (Tρ : Tube ρ E)
    {z : E} {A P : ℝ} (hA : 0 ≤ A)
    (haxial : |(inner ℝ Tρ.direction (z - Tρ.center) : ℝ)| ≤ 1 / 2 + A)
    (hperp : ‖(z - Tρ.center) - (inner ℝ Tρ.direction (z - Tρ.center) : ℝ) • Tρ.direction‖ ≤ P)
    (hbound : A ^ 2 + P ^ 2 ≤ (ρ : ℝ) ^ 2) :
    z ∈ Tρ.carrier := by
  rw [← dilate_one_carrier Tρ]
  refine mem_dilate_of_axis_bounds Tρ one_pos hA (by simpa using haxial) hperp ?_
  simpa using hbound

/-- **The axial/transverse resolution of a point of a tube against a foreign axis.**

For `z` in the carrier of the `r`-tube `S`, written `z = S.center + t • S.direction + v` with
`|t| ≤ 1/2` and `‖v‖ ≤ r`, the coordinates of `z - Tρ.center` along and across the unit vector
`g = Tρ.direction` are controlled by the corresponding coordinates of `S.center - Tρ.center`,
the transverse part of `S.direction`, and the *orthogonal* split `a₀ ^ 2 + b ^ 2 ≤ r ^ 2` of the
error `v`.  Keeping `a₀` and `b` separate — rather than bounding both by `r` — is what
`Kakeya.ml1Boot.mem_dilate_of_axis_bounds` needs to combine them by Pythagoras. -/
theorem exists_axis_data_of_mem_carrier {r : NNReal} (S : Tube r E) {g c₀ : E} (hg : ‖g‖ = 1)
    {z : E} (hz : z ∈ S.carrier) :
    ∃ a₀ b : ℝ, 0 ≤ a₀ ∧ 0 ≤ b ∧ a₀ ^ 2 + b ^ 2 ≤ (r : ℝ) ^ 2 ∧
      |(inner ℝ g (z - c₀) : ℝ)| ≤ |(inner ℝ g (S.center - c₀) : ℝ)| + 1 / 2 + a₀ ∧
      ‖(z - c₀) - (inner ℝ g (z - c₀) : ℝ) • g‖
        ≤ ‖(S.center - c₀) - (inner ℝ g (S.center - c₀) : ℝ) • g‖
          + 1 / 2 * ‖S.direction - (inner ℝ g S.direction : ℝ) • g‖ + b := by
  obtain ⟨t, ht, hv⟩ := Kakeya.Tube.exists_axis_repr_of_mem_dilate S one_pos
    (_root_.Tube.subset_dilate S le_rfl hz)
  set v : E := z - (S.center + t • S.direction) with hvdef
  have hvnorm : ‖v‖ ≤ (r : ℝ) := by simpa using hv
  refine ⟨|(inner ℝ g v : ℝ)|, ‖v - (inner ℝ g v : ℝ) • g‖, abs_nonneg _, norm_nonneg _, ?_, ?_, ?_⟩
  · have hsplit : ((inner ℝ g v : ℝ)) • g + (v - (inner ℝ g v : ℝ) • g) = v := by abel
    have h := norm_sq_axis_split hg v (inner ℝ g v : ℝ)
    rw [hsplit] at h
    have : ‖v‖ ^ 2 ≤ (r : ℝ) ^ 2 := by
      exact pow_le_pow_left₀ (norm_nonneg _) hvnorm 2
    rw [sq_abs]
    linarith
  · have hzc : z - c₀ = (S.center - c₀) + t • S.direction + v := by
      rw [hvdef]; abel
    rw [hzc, inner_add_right, inner_add_right, real_inner_smul_right]
    have h1 : |(inner ℝ g S.direction : ℝ)| ≤ 1 := by
      have := abs_real_inner_le_norm g S.direction
      rw [hg, one_mul, S.norm_direction] at this
      exact this
    have h2 : |t * (inner ℝ g S.direction : ℝ)| ≤ 1 / 2 := by
      rw [abs_mul]
      have := mul_le_mul ht h1 (abs_nonneg _) (by norm_num)
      simpa using this
    calc |(inner ℝ g (S.center - c₀) : ℝ) + t * (inner ℝ g S.direction : ℝ)
            + (inner ℝ g v : ℝ)|
        ≤ |(inner ℝ g (S.center - c₀) : ℝ) + t * (inner ℝ g S.direction : ℝ)|
            + |(inner ℝ g v : ℝ)| := abs_add_le _ _
      _ ≤ (|(inner ℝ g (S.center - c₀) : ℝ)| + |t * (inner ℝ g S.direction : ℝ)|)
            + |(inner ℝ g v : ℝ)| := by
          gcongr
          exact abs_add_le _ _
      _ ≤ |(inner ℝ g (S.center - c₀) : ℝ)| + 1 / 2 + |(inner ℝ g v : ℝ)| := by linarith
  · have hzc : z - c₀ = (S.center - c₀) + t • S.direction + v := by
      rw [hvdef]; abel
    have hperpadd : ∀ w w' : E,
        (w + w') - (inner ℝ g (w + w') : ℝ) • g
          = (w - (inner ℝ g w : ℝ) • g) + (w' - (inner ℝ g w' : ℝ) • g) := by
      intro w w'
      rw [inner_add_right, add_smul]
      module
    have hperpsmul : ∀ (u : E) (l : ℝ),
        (l • u) - (inner ℝ g (l • u) : ℝ) • g = l • (u - (inner ℝ g u : ℝ) • g) := by
      intro u l
      rw [real_inner_smul_right, smul_sub, smul_smul]
    rw [hzc, hperpadd, hperpadd, hperpsmul]
    calc ‖((S.center - c₀) - (inner ℝ g (S.center - c₀) : ℝ) • g)
            + t • (S.direction - (inner ℝ g S.direction : ℝ) • g)
            + (v - (inner ℝ g v : ℝ) • g)‖
        ≤ ‖((S.center - c₀) - (inner ℝ g (S.center - c₀) : ℝ) • g)
            + t • (S.direction - (inner ℝ g S.direction : ℝ) • g)‖
            + ‖v - (inner ℝ g v : ℝ) • g‖ := norm_add_le _ _
      _ ≤ ‖(S.center - c₀) - (inner ℝ g (S.center - c₀) : ℝ) • g‖
            + ‖t • (S.direction - (inner ℝ g S.direction : ℝ) • g)‖
            + ‖v - (inner ℝ g v : ℝ) • g‖ := by
          gcongr
          exact norm_add_le _ _
      _ ≤ ‖(S.center - c₀) - (inner ℝ g (S.center - c₀) : ℝ) • g‖
            + 1 / 2 * ‖S.direction - (inner ℝ g S.direction : ℝ) • g‖
            + ‖v - (inner ℝ g v : ℝ) • g‖ := by
          gcongr
          rw [norm_smul, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_right ht (norm_nonneg _)

omit [MeasurableSpace E] [BorelSpace E] in
/-- The centre and the direction of `Tube.ofMidpointDirection`. -/
theorem ofMidpointDirection_center_direction {δ : NNReal} (m u : E) (hu : ‖u‖ = 1) :
    (_root_.Tube.ofMidpointDirection δ m u hu).center = m ∧
      (_root_.Tube.ofMidpointDirection δ m u hu).direction = u := by
  constructor
  · change midpoint ℝ (m - (1 / 2 : ℝ) • u) (m + (1 / 2 : ℝ) • u) = m
    rw [midpoint_eq_smul_add]
    simp only [invOf_eq_inv]
    module
  · change (m + (1 / 2 : ℝ) • u) - (m - (1 / 2 : ℝ) • u) = u
    module

/-- **Sharp containment of a concentric thin tube in a fat one.**

If the `r`-tube `S` and the `ρ`-tube `Tρ` share a centre and the direction of `S` is transverse
to that of `Tρ` by at most `2 (ρ - r)`, then `S ⊆ Tρ`.

The constant `2 (ρ - r)` is exactly right and cannot be relaxed to `2 ρ`: the transverse drift of
a core endpoint of `S` is half the transverse part of the direction, and the `r`-thickening of `S`
adds `r` on top of it.  It is also not too small — the `r` subtracted here is *not* lost twice.
The axial overshoot of `S` past the ends of the core of `Tρ` and the transverse excess of the
same point come from the two orthogonal components of one displacement of length `≤ r`, so
`Kakeya.ml1Boot.mem_dilate_of_axis_bounds` combines them by Pythagoras and the total is
`a₀ ^ 2 + ((ρ - r) + b) ^ 2 ≤ r ^ 2 + 2 (ρ - r) r + (ρ - r) ^ 2 = ρ ^ 2`, with equality attained.
Combining them by the triangle inequality instead would demand `2 (ρ - 2 r)` and lose the `r` that
item (iv) has no room for. -/
theorem tube_subset_of_direction_close {r ρ : NNReal} (S : Tube r E) (Tρ : Tube ρ E)
    (hcen : S.center = Tρ.center) (hrρ : (r : ℝ) ≤ (ρ : ℝ))
    (hdir : ‖S.direction - (inner ℝ Tρ.direction S.direction : ℝ) • Tρ.direction‖
      ≤ 2 * ((ρ : ℝ) - (r : ℝ))) :
    S.carrier ⊆ Tρ.carrier := by
  intro z hz
  have hg : ‖Tρ.direction‖ = 1 := Tρ.norm_direction
  obtain ⟨a₀, b, ha₀, hb, hab, haxial, hperp⟩ :=
    exists_axis_data_of_mem_carrier (g := Tρ.direction) (c₀ := Tρ.center) S hg hz
  rw [hcen] at haxial hperp
  simp only [sub_self, inner_zero_right, abs_zero, zero_smul, norm_zero,
    zero_add] at haxial hperp
  have hr0 : (0 : ℝ) ≤ (r : ℝ) := NNReal.coe_nonneg r
  have hq : (0 : ℝ) ≤ (ρ : ℝ) - (r : ℝ) := by linarith
  have hbr : b ≤ (r : ℝ) := by nlinarith
  refine mem_carrier_of_axis_bounds Tρ ha₀ (by linarith) (P := ((ρ : ℝ) - r) + b) ?_ ?_
  · refine hperp.trans ?_
    have : 1 / 2 * ‖S.direction - (inner ℝ Tρ.direction S.direction : ℝ) • Tρ.direction‖
        ≤ (ρ : ℝ) - r := by linarith
    linarith
  · nlinarith

/-- **Containment of a thin tube in the `2`-dilate of a fat one, from centre and direction
offsets.**

`μ` bounds the transverse offset of the two centres, `2 η` the transverse part of the thin
direction, and the axial offset plus the thin radius is at most `1/2`; then `S ⊆ 2 · Tρ` as soon
as `μ + η + r ≤ 2 ρ`.  Here there is genuine slack and the crude triangle-inequality combination
suffices: the axial coordinate never leaves `[-1, 1]`, so `A = 0`. -/
theorem tube_subset_dilate_two_of_close {r ρ : NNReal} (S : Tube r E) (Tρ : Tube ρ E)
    {μ η : ℝ}
    (hax : |(inner ℝ Tρ.direction (S.center - Tρ.center) : ℝ)| + (r : ℝ) ≤ 1 / 2)
    (hcenperp : ‖(S.center - Tρ.center)
      - (inner ℝ Tρ.direction (S.center - Tρ.center) : ℝ) • Tρ.direction‖ ≤ μ)
    (hdir : ‖S.direction - (inner ℝ Tρ.direction S.direction : ℝ) • Tρ.direction‖ ≤ 2 * η)
    (hbound : μ + η + (r : ℝ) ≤ 2 * (ρ : ℝ)) :
    S.carrier ⊆ (Kakeya.Tube.dilate Tρ 2).carrier := by
  intro z hz
  have hg : ‖Tρ.direction‖ = 1 := Tρ.norm_direction
  obtain ⟨a₀, b, ha₀, hb, hab, haxial, hperp⟩ :=
    exists_axis_data_of_mem_carrier (g := Tρ.direction) (c₀ := Tρ.center) S hg hz
  have hr0 : (0 : ℝ) ≤ (r : ℝ) := NNReal.coe_nonneg r
  have hbr : b ≤ (r : ℝ) := by nlinarith
  have ha₀r : a₀ ≤ (r : ℝ) := by nlinarith
  have hρ0 : (0 : ℝ) ≤ (ρ : ℝ) := NNReal.coe_nonneg ρ
  refine mem_dilate_of_axis_bounds Tρ (by norm_num) le_rfl (A := 0)
    (by simpa using (by linarith : |(inner ℝ Tρ.direction (z - Tρ.center) : ℝ)| ≤ 2 / 2 + 0))
    (P := μ + η + b) ?_ ?_
  · refine hperp.trans ?_
    have h1 : 1 / 2 * ‖S.direction - (inner ℝ Tρ.direction S.direction : ℝ) • Tρ.direction‖
        ≤ η := by linarith
    linarith
  · have hP : μ + η + b ≤ 2 * (ρ : ℝ) := by linarith
    have hP0 : (0 : ℝ) ≤ μ + η + b := by
      have := le_trans (norm_nonneg _) hcenperp
      have h2 : (0 : ℝ) ≤ η := by
        have := le_trans (norm_nonneg _) hdir
        linarith
      linarith
    nlinarith

omit [MeasurableSpace E] [BorelSpace E] in
/-- A tube whose core endpoints are `c`-close to the origin, with `c + ρ ≤ 1`, lies in `B(0,1)`.
The `rescale`-specific `Kakeya.ml1Boot.Tube.rescale_carrier_subset_closedBall` of
`Rescaling/LowerWindow.lean` is this statement read at `T.rescale ρt`. -/
theorem carrier_subset_closedBall_of_endpoints {ρ : NNReal} (T : Tube ρ E) {c : ℝ}
    (hx : ‖T.x‖ ≤ c) (hy : ‖T.y‖ ≤ c) (h : c + (ρ : ℝ) ≤ 1) :
    T.carrier ⊆ Metric.closedBall (0 : E) 1 := by
  have hseg : segment ℝ T.x T.y ⊆ Metric.closedBall (0 : E) c := by
    refine (convex_closedBall (0 : E) c).segment_subset ?_ ?_
    · simpa [Metric.mem_closedBall, dist_zero_right] using hx
    · simpa [Metric.mem_closedBall, dist_zero_right] using hy
  intro w hw
  rw [T.carrier_eq] at hw
  simp only [Set.mem_iUnion, exists_prop] at hw
  obtain ⟨z, hz, hwz⟩ := hw
  have hzc : ‖z‖ ≤ c := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hseg hz
  have hwzd : ‖w - z‖ ≤ (ρ : ℝ) := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hwz
  have hfin : ‖w‖ ≤ c + (ρ : ℝ) := by
    calc ‖w‖ = ‖z + (w - z)‖ := by abel_nf
      _ ≤ ‖z‖ + ‖w - z‖ := norm_add_le _ _
      _ ≤ c + (ρ : ℝ) := by linarith
  simpa [Metric.mem_closedBall, dist_zero_right] using hfin.trans h

/-- **The single container tube of item (iv): the source container's direction carried at the
member's centre.**

This is the object the two earlier routes each half-produced.  The *member* route
(`Kakeya.ml1Boot.exists_container_tube_of_endpoints`) keeps the member's direction and loses
`Ψ(T_σ) ≤ 2 · T_ρ`; the *container* route
(`Kakeya.ml1Boot.exists_rescaled_source_container`) keeps the container's direction and loses
`T̃ k ≤ T_ρ`.  Neither has to be given up: take the **container's direction at the member's
centre**.  Then

* `T̃ k ≤ T_ρ` holds by `Kakeya.ml1Boot.tube_subset_of_direction_close`, the two tubes being
  concentric and their directions transverse by at most `2 (ρt - dt)`;
* `S_ρ ≤ 2 · T_ρ` holds because `S_ρ` and `T_ρ` are *parallel*, so the whole transverse budget
  `2 ρt` is spent on the centre offset `ρt` plus the radius `ρt`;
* `T̃ i ≤ 2 · T_ρ` for every ambient `i` caught by the container holds with the budget spent as
  `ρt` (centre offset) `+ (ρt - dt)` (half the transverse direction) `+ dt` (radius) `= 2 ρt`.

Every one of the three is tight, and the middle two are what force `T_ρ` to be parallel to the
container while the first is what forces it to be centred on the member.  The transverse
direction bound `2 (ρt - dt)` is available because a `τ`-tube whose *carrier* lies inside a
`σ`-tube has its core within `σ - τ` of the container's axis, and `(σ - τ) / θ = ρt - dt`. -/
theorem exists_itemIV_container_tube {dt ρt : NNReal} {ι : Type*} {un : Finset ι}
    (Ttil : ι → Tube dt E) (k : ι) (hk : k ∈ un) (Sρ : Tube ρt E)
    (hρ4 : (ρt : ℝ) ≤ 1 / 4) (hdtρ : (dt : ℝ) ≤ (ρt : ℝ))
    (hmk : ‖(Ttil k).center‖ ≤ 1 / 4)
    (hdir : ∀ i ∈ un, ‖(Ttil i).direction
      - (inner ℝ Sρ.direction (Ttil i).direction : ℝ) • Sρ.direction‖
        ≤ 2 * ((ρt : ℝ) - (dt : ℝ)))
    (hax : ∀ i ∈ un, |(inner ℝ Sρ.direction ((Ttil i).center - (Ttil k).center) : ℝ)|
      + (dt : ℝ) ≤ 1 / 2)
    (hperp : ∀ i ∈ un, ‖((Ttil i).center - (Ttil k).center)
      - (inner ℝ Sρ.direction ((Ttil i).center - (Ttil k).center) : ℝ) • Sρ.direction‖
        ≤ (ρt : ℝ))
    (hSax : |(inner ℝ Sρ.direction (Sρ.center - (Ttil k).center) : ℝ)| + (ρt : ℝ) ≤ 1 / 2)
    (hSperp : ‖(Sρ.center - (Ttil k).center)
      - (inner ℝ Sρ.direction (Sρ.center - (Ttil k).center) : ℝ) • Sρ.direction‖
        ≤ (ρt : ℝ)) :
    ∃ Tρ : Tube ρt E,
      Tρ.center = (Ttil k).center ∧ Tρ.direction = Sρ.direction ∧
      Tρ.carrier ⊆ Metric.closedBall (0 : E) 1 ∧
      (Ttil k).toConvexSpaceBody ≤ Tρ.toConvexSpaceBody ∧
      Sρ.toConvexSpaceBody ≤ Kakeya.Tube.dilate Tρ 2 ∧
      ∀ i ∈ un, (Ttil i).toConvexSpaceBody ≤ Kakeya.Tube.dilate Tρ 2 := by
  have hg : ‖Sρ.direction‖ = 1 := Sρ.norm_direction
  set Tρ : Tube ρt E := _root_.Tube.ofMidpointDirection ρt (Ttil k).center Sρ.direction hg with hTρ
  obtain ⟨hcen, hdirT⟩ :=
    ofMidpointDirection_center_direction (δ := ρt) (Ttil k).center Sρ.direction hg
  refine ⟨Tρ, hcen, hdirT, ?_, ?_, ?_, ?_⟩
  · refine carrier_subset_closedBall_of_endpoints Tρ (c := 3 / 4) ?_ ?_ (by linarith)
    · change ‖(Ttil k).center - (1 / 2 : ℝ) • Sρ.direction‖ ≤ 3 / 4
      calc ‖(Ttil k).center - (1 / 2 : ℝ) • Sρ.direction‖
          ≤ ‖(Ttil k).center‖ + ‖(1 / 2 : ℝ) • Sρ.direction‖ := norm_sub_le _ _
        _ ≤ 1 / 4 + 1 / 2 := by
            gcongr
            rw [norm_smul, Real.norm_eq_abs, hg]
            norm_num
        _ = 3 / 4 := by norm_num
    · change ‖(Ttil k).center + (1 / 2 : ℝ) • Sρ.direction‖ ≤ 3 / 4
      calc ‖(Ttil k).center + (1 / 2 : ℝ) • Sρ.direction‖
          ≤ ‖(Ttil k).center‖ + ‖(1 / 2 : ℝ) • Sρ.direction‖ := norm_add_le _ _
        _ ≤ 1 / 4 + 1 / 2 := by
            gcongr
            rw [norm_smul, Real.norm_eq_abs, hg]
            norm_num
        _ = 3 / 4 := by norm_num
  · change (Ttil k).carrier ⊆ Tρ.carrier
    refine tube_subset_of_direction_close (Ttil k) Tρ hcen.symm hdtρ ?_
    rw [hdirT]
    exact hdir k hk
  · change Sρ.carrier ⊆ (Kakeya.Tube.dilate Tρ 2).carrier
    refine tube_subset_dilate_two_of_close Sρ Tρ (μ := (ρt : ℝ)) (η := 0) ?_ ?_ ?_ (by linarith)
    · rw [hdirT, hcen]; exact hSax
    · rw [hdirT, hcen]; exact hSperp
    · rw [hdirT]
      have he : (inner ℝ Sρ.direction Sρ.direction : ℝ) = 1 := by
        rw [real_inner_self_eq_norm_sq, hg]; norm_num
      rw [he, one_smul, sub_self, norm_zero]
      norm_num
  · intro i hi
    change (Ttil i).carrier ⊆ (Kakeya.Tube.dilate Tρ 2).carrier
    refine tube_subset_dilate_two_of_close (Ttil i) Tρ (μ := (ρt : ℝ))
      (η := (ρt : ℝ) - (dt : ℝ)) ?_ ?_ ?_ (by linarith)
    · rw [hdirT, hcen]; exact hax i hi
    · rw [hdirT, hcen]; exact hperp i hi
    · rw [hdirT]; exact hdir i hi

/-- **A tube inside a tube keeps its core `σ - τ` from the container's axis, not merely `σ`.**

The `τ`-thickening of the core of `Tb` is part of `Tb`, hence of `Tσ`; pushing a core point of
`Tb` a further `τ` *directly away from the axis of* `Tσ` therefore stays inside `Tσ`, and the
transverse coordinate of the pushed point is the transverse coordinate of the original plus `τ`
exactly, the push being orthogonal to the axis.

The `τ` recovered here is the whole margin item (iv) runs on: it is what turns the transverse
direction budget `2 σ` into `2 (σ - τ)` and, after normalization, `2 ρt` into `2 (ρt - dt)`. -/
theorem norm_perp_core_le_of_carrier_subset {τ σ : NNReal} (Tb : Tube τ E) (Tσ : Tube σ E)
    (hτσ : (τ : ℝ) ≤ (σ : ℝ)) (hsub : Tb.carrier ⊆ Tσ.carrier)
    {p : E} (hp : p ∈ segment ℝ Tb.x Tb.y) :
    ‖(p - Tσ.center) - (inner ℝ Tσ.direction (p - Tσ.center) : ℝ) • Tσ.direction‖
      ≤ (σ : ℝ) - (τ : ℝ) := by
  have hg : ‖Tσ.direction‖ = 1 := Tσ.norm_direction
  set g : E := Tσ.direction with hgdef
  set W : E := (p - Tσ.center) - (inner ℝ g (p - Tσ.center) : ℝ) • g with hW
  rcases eq_or_ne W 0 with h0 | h0
  · rw [h0, norm_zero]; linarith
  · set n : E := ‖W‖⁻¹ • W with hn
    have hWpos : (0 : ℝ) < ‖W‖ := norm_pos_iff.mpr h0
    have hnn : ‖n‖ = 1 := by
      rw [hn, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (ne_of_gt hWpos)]
    have hgW : (inner ℝ g W : ℝ) = 0 := inner_perp_eq_zero hg (p - Tσ.center)
    have hgn : (inner ℝ g n : ℝ) = 0 := by
      rw [hn, real_inner_smul_right, hgW, mul_zero]
    -- the pushed point
    have hmem : p + (τ : ℝ) • n ∈ Tσ.carrier := by
      refine hsub (Tb.closedBall_subset_carrier_of_mem_segment hp ?_)
      rw [Metric.mem_closedBall, dist_eq_norm]
      simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, hnn, mul_one,
        abs_of_nonneg (NNReal.coe_nonneg τ)]
      exact le_rfl
    have hperp := (_root_.Tube.abs_inner_and_perp_le_of_mem_dilate Tσ (c := 1) one_pos
      (_root_.Tube.subset_dilate Tσ le_rfl hmem)).2
    rw [one_mul] at hperp
    have hsplit : ((p + (τ : ℝ) • n) - Tσ.center)
        - (inner ℝ g ((p + (τ : ℝ) • n) - Tσ.center) : ℝ) • g = W + (τ : ℝ) • n := by
      have : (p + (τ : ℝ) • n) - Tσ.center = (p - Tσ.center) + (τ : ℝ) • n := by abel
      rw [this, perp_add, hW]
      congr 1
      rw [perp_smul, hgdef]
      have : n - (inner ℝ Tσ.direction n : ℝ) • Tσ.direction = n := by
        rw [← hgdef, hgn, zero_smul, sub_zero]
      rw [this]
    rw [hsplit] at hperp
    have hval : ‖W + (τ : ℝ) • n‖ = ‖W‖ + (τ : ℝ) := by
      have : W + (τ : ℝ) • n = (‖W‖ + (τ : ℝ)) • n := by
        rw [hn, smul_smul, add_smul, smul_smul, smul_smul,
          mul_inv_cancel₀ (ne_of_gt hWpos), one_smul]
      rw [this, norm_smul, Real.norm_eq_abs, hnn, mul_one,
        abs_of_nonneg (by positivity : (0:ℝ) ≤ ‖W‖ + (τ : ℝ))]
    rw [hval] at hperp
    linarith

/-- **The sharp transverse-direction bound for a tube inside a tube.**

`‖perp_{Tσ.direction} (Tb.direction)‖ ≤ 2 (σ - τ)`, both core endpoints of `Tb` being within
`σ - τ` of the axis of `Tσ` by `Kakeya.ml1Boot.norm_perp_core_le_of_carrier_subset`.  This is
strictly sharper than `Tube.norm_perp_direction_le_of_chord`, which pays `2 σ + 4 τ`. -/
theorem norm_perp_direction_le_of_carrier_subset {τ σ : NNReal} (Tb : Tube τ E) (Tσ : Tube σ E)
    (hτσ : (τ : ℝ) ≤ (σ : ℝ)) (hsub : Tb.carrier ⊆ Tσ.carrier) :
    ‖Tb.direction - (inner ℝ Tσ.direction Tb.direction : ℝ) • Tσ.direction‖
      ≤ 2 * ((σ : ℝ) - (τ : ℝ)) := by
  have hx := norm_perp_core_le_of_carrier_subset Tb Tσ hτσ hsub (left_mem_segment ℝ Tb.x Tb.y)
  have hy := norm_perp_core_le_of_carrier_subset Tb Tσ hτσ hsub (right_mem_segment ℝ Tb.x Tb.y)
  have hdir : Tb.direction = (Tb.y - Tσ.center) - (Tb.x - Tσ.center) := by
    change Tb.y - Tb.x = _
    abel
  rw [hdir, perp_sub]
  calc ‖((Tb.y - Tσ.center) - (inner ℝ Tσ.direction (Tb.y - Tσ.center) : ℝ) • Tσ.direction)
        - ((Tb.x - Tσ.center) - (inner ℝ Tσ.direction (Tb.x - Tσ.center) : ℝ) • Tσ.direction)‖
      ≤ ‖(Tb.y - Tσ.center) - (inner ℝ Tσ.direction (Tb.y - Tσ.center) : ℝ) • Tσ.direction‖
        + ‖(Tb.x - Tσ.center) - (inner ℝ Tσ.direction (Tb.x - Tσ.center) : ℝ) • Tσ.direction‖ :=
      norm_sub_le _ _
    _ ≤ 2 * ((σ : ℝ) - (τ : ℝ)) := by linarith

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Normalization to a unit vector is invariant under positive rescaling.  This is what lets the
homothety factor `(4 R)⁻¹` of `Tube.rescaleMap` be ignored when comparing directions. -/
theorem normalize_smul {c : ℝ} (hc : 0 < c) (v : E) :
    ‖c • v‖⁻¹ • (c • v) = ‖v‖⁻¹ • v := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc, smul_smul, mul_inv]
  congr 1
  field_simp

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- **Transverse closeness of two normalized vectors.**

If `H` is within `m` of the line `ℝ ∙ G`, then the transverse part of the unit vector of `H`
relative to the unit vector of `G` is at most `m / ‖H‖`.  Only `G ≠ 0` is used; `λ` is free. -/
theorem norm_perp_normalize_le {G H : E} (hG : G ≠ 0) {l m : ℝ} (hm : ‖H - l • G‖ ≤ m) :
    ‖(‖H‖⁻¹ • H)
        - (inner ℝ (‖G‖⁻¹ • G) (‖H‖⁻¹ • H) : ℝ) • (‖G‖⁻¹ • G)‖ ≤ m / ‖H‖ := by
  rcases eq_or_ne H 0 with rfl | hH
  · simp
  have hGpos : (0 : ℝ) < ‖G‖ := norm_pos_iff.mpr hG
  have hHpos : (0 : ℝ) < ‖H‖ := norm_pos_iff.mpr hH
  set g : E := ‖G‖⁻¹ • G with hgdef
  have hg : ‖g‖ = 1 := by
    rw [hgdef, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (ne_of_gt hGpos)]
  have hGg : G = ‖G‖ • g := by
    rw [hgdef, smul_smul, mul_inv_cancel₀ (ne_of_gt hGpos), one_smul]
  -- the transverse part kills the `G` component and is homogeneous
  have hkey : (‖H‖⁻¹ • H) - (inner ℝ g (‖H‖⁻¹ • H) : ℝ) • g
      = ‖H‖⁻¹ • ((H - l • G) - (inner ℝ g (H - l • G) : ℝ) • g) := by
    have hgg : g - (inner ℝ g g : ℝ) • g = 0 := by
      have he : (inner ℝ g g : ℝ) = 1 := by rw [real_inner_self_eq_norm_sq, hg]; norm_num
      rw [he, one_smul, sub_self]
    rw [perp_smul]
    congr 1
    rw [perp_sub, hGg, perp_smul, perp_smul, hgg, smul_zero, smul_zero, sub_zero]
  rw [hkey, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hHpos)]
  rw [div_eq_inv_mul]
  refine mul_le_mul_of_nonneg_left ?_ (inv_pos.mpr hHpos).le
  exact le_trans (norm_perp_le hg (H - l • G)) hm

end HybridTube

section Normalization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

omit [MeasurableSpace E] [BorelSpace E] in
/-- The normalization's linear part in axial/transverse coordinates: the identity along the
core direction, multiplication by `θ⁻¹` across it. -/
theorem normalizationLinear_apply_eq {θ : NNReal} (Tθ : Tube θ E) (v : E) :
    Tθ.normalizationLinear v
      = (inner ℝ Tθ.direction v : ℝ) • Tθ.direction
        + (θ : ℝ)⁻¹ • (v - (inner ℝ Tθ.direction v : ℝ) • Tθ.direction) := by
  rw [_root_.Tube.normalizationLinear_eq_dilateAux, _root_.Tube.dilateAux_apply]
  module

omit [MeasurableSpace E] [BorelSpace E] in
/-- `Φ` does not shrink, for `θ ≤ 1`. -/
theorem norm_le_norm_normalizationLinear {θ : NNReal} (hθ0 : (0 : ℝ) < (θ : ℝ))
    (hθ1 : (θ : ℝ) ≤ 1) (Tθ : Tube θ E) (v : E) : ‖v‖ ≤ ‖Tθ.normalizationLinear v‖ := by
  have he : ‖Tθ.direction‖ = 1 := Tθ.norm_direction
  set t : ℝ := (inner ℝ Tθ.direction v : ℝ) with htdef
  set P : E := v - t • Tθ.direction with hPdef
  have hP : (inner ℝ Tθ.direction P : ℝ) = 0 := inner_perp_eq_zero he v
  have hv : ‖v‖ ^ 2 = t ^ 2 + ‖P‖ ^ 2 := by
    have h := norm_sq_add_orthogonal he hP t
    have hsum : t • Tθ.direction + P = v := by rw [hPdef]; abel
    rw [hsum] at h
    exact h
  have hPs : (inner ℝ Tθ.direction ((θ : ℝ)⁻¹ • P) : ℝ) = 0 := by
    rw [real_inner_smul_right, hP, mul_zero]
  have hn : ‖Tθ.normalizationLinear v‖ ^ 2 = t ^ 2 + ((θ : ℝ)⁻¹) ^ 2 * ‖P‖ ^ 2 := by
    rw [normalizationLinear_apply_eq]
    have h := norm_sq_add_orthogonal he hPs t
    rw [h, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hθ0), mul_pow]
  have hinv : (1 : ℝ) ≤ (θ : ℝ)⁻¹ := by
    have h := one_div_le_one_div_of_le hθ0 hθ1
    simpa using h
  have hgap : (0 : ℝ) ≤ (((θ : ℝ)⁻¹) ^ 2 - 1) * ‖P‖ ^ 2 :=
    mul_nonneg (by nlinarith) (sq_nonneg _)
  have hsq : ‖v‖ ^ 2 ≤ ‖Tθ.normalizationLinear v‖ ^ 2 := by rw [hv, hn]; linarith
  nlinarith [norm_nonneg v, norm_nonneg (Tθ.normalizationLinear v)]

omit [MeasurableSpace E] [BorelSpace E] in
/-- `Φ` expands by at most `θ⁻¹`. -/
theorem norm_normalizationLinear_le {θ : NNReal} (hθ0 : (0 : ℝ) < (θ : ℝ))
    (hθ1 : (θ : ℝ) ≤ 1) (Tθ : Tube θ E) (v : E) :
    ‖Tθ.normalizationLinear v‖ ≤ (θ : ℝ)⁻¹ * ‖v‖ := by
  have he : ‖Tθ.direction‖ = 1 := Tθ.norm_direction
  set t : ℝ := (inner ℝ Tθ.direction v : ℝ) with htdef
  set P : E := v - t • Tθ.direction with hPdef
  have hP : (inner ℝ Tθ.direction P : ℝ) = 0 := inner_perp_eq_zero he v
  have hv : ‖v‖ ^ 2 = t ^ 2 + ‖P‖ ^ 2 := by
    have h := norm_sq_add_orthogonal he hP t
    have hsum : t • Tθ.direction + P = v := by rw [hPdef]; abel
    rw [hsum] at h
    exact h
  have hPs : (inner ℝ Tθ.direction ((θ : ℝ)⁻¹ • P) : ℝ) = 0 := by
    rw [real_inner_smul_right, hP, mul_zero]
  have hn : ‖Tθ.normalizationLinear v‖ ^ 2 = t ^ 2 + ((θ : ℝ)⁻¹) ^ 2 * ‖P‖ ^ 2 := by
    rw [normalizationLinear_apply_eq]
    have h := norm_sq_add_orthogonal he hPs t
    rw [h, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hθ0), mul_pow]
  have hinv : (1 : ℝ) ≤ (θ : ℝ)⁻¹ := by
    have h := one_div_le_one_div_of_le hθ0 hθ1
    simpa using h
  have h1 : ‖Tθ.normalizationLinear v‖ ^ 2 ≤ ((θ : ℝ)⁻¹ * ‖v‖) ^ 2 := by
    rw [mul_pow, hv, hn]
    have : (0 : ℝ) ≤ (((θ : ℝ)⁻¹) ^ 2 - 1) * t ^ 2 :=
      mul_nonneg (by nlinarith) (sq_nonneg _)
    nlinarith
  have h2 : (0 : ℝ) ≤ (θ : ℝ)⁻¹ * ‖v‖ := by positivity
  nlinarith [norm_nonneg (Tθ.normalizationLinear v)]

/-- **The transverse-direction budget of item (iv), transported through the normalization.**

An inner `τ`-tube `Ub` of the `σ`-tube `Tσ` has, after the anisotropic normalization `Φ` of the
ambient `θ`-tube, its direction within `2 (σ - τ) / θ` of the direction of `Φ(Tσ)`.  Read at
`σ = ρt θ` and `τ = dt θ` this is exactly the `2 (ρt - dt)` that
`Kakeya.ml1Boot.tube_subset_of_direction_close` asks for, and it is the reason the sharper
`Kakeya.ml1Boot.norm_perp_core_le_of_carrier_subset` had to be proved: the crude `2 σ` would
transport to `2 ρt` and clause 1 of `Kakeya.ml1Boot.exists_itemIV_container_tube` would fail.

Two features of `Φ` are used and no more: it multiplies the transverse part by `θ⁻¹` — hence
`‖Φ w‖ ≤ θ⁻¹ ‖w‖` — and it does not shrink, so `‖Φ (Ub.direction)‖ ≥ 1`.  The homothety factor
`(4 R)⁻¹` of `Tube.rescaleMap` is irrelevant here by
`Kakeya.ml1Boot.normalize_smul`. -/
theorem norm_perp_direction_normalized_le {τ σ θ : NNReal}
    (hθ0 : (0 : ℝ) < (θ : ℝ)) (hθ1 : (θ : ℝ) ≤ 1) (hτσ : (τ : ℝ) ≤ (σ : ℝ))
    (Tθ : Tube θ E) (Tσ : Tube σ E) (Ub : Tube τ E) (hsub : Ub.carrier ⊆ Tσ.carrier) :
    ‖(‖Tθ.normalizationLinear Ub.direction‖⁻¹ • Tθ.normalizationLinear Ub.direction)
        - (inner ℝ
              (‖Tθ.normalizationLinear Tσ.direction‖⁻¹ • Tθ.normalizationLinear Tσ.direction)
              (‖Tθ.normalizationLinear Ub.direction‖⁻¹ • Tθ.normalizationLinear Ub.direction) : ℝ)
            • (‖Tθ.normalizationLinear Tσ.direction‖⁻¹
                • Tθ.normalizationLinear Tσ.direction)‖
      ≤ 2 * ((σ : ℝ) - (τ : ℝ)) / (θ : ℝ) := by
  set G : E := Tθ.normalizationLinear Tσ.direction with hGdef
  set H : E := Tθ.normalizationLinear Ub.direction with hHdef
  set l : ℝ := (inner ℝ Tσ.direction Ub.direction : ℝ) with hldef
  have hm0 : (0 : ℝ) ≤ 2 * ((σ : ℝ) - (τ : ℝ)) := by linarith
  have hG1 : (1 : ℝ) ≤ ‖G‖ := by
    have h := norm_le_norm_normalizationLinear hθ0 hθ1 Tθ Tσ.direction
    rwa [Tσ.norm_direction] at h
  have hH1 : (1 : ℝ) ≤ ‖H‖ := by
    have h := norm_le_norm_normalizationLinear hθ0 hθ1 Tθ Ub.direction
    rwa [Ub.norm_direction] at h
  have hG : G ≠ 0 := by
    intro h
    rw [h, norm_zero] at hG1
    linarith
  have hlin : H - l • G = Tθ.normalizationLinear (Ub.direction - l • Tσ.direction) := by
    rw [hGdef, hHdef, ← map_smul, ← map_sub]
  have hdirbd : ‖Ub.direction - l • Tσ.direction‖ ≤ 2 * ((σ : ℝ) - (τ : ℝ)) :=
    norm_perp_direction_le_of_carrier_subset Ub Tσ hτσ hsub
  have hHl : ‖H - l • G‖ ≤ (θ : ℝ)⁻¹ * (2 * ((σ : ℝ) - (τ : ℝ))) := by
    rw [hlin]
    refine le_trans (norm_normalizationLinear_le hθ0 hθ1 Tθ _) ?_
    exact mul_le_mul_of_nonneg_left hdirbd (inv_pos.mpr hθ0).le
  refine le_trans (norm_perp_normalize_le hG hHl) ?_
  have hnum : (0 : ℝ) ≤ (θ : ℝ)⁻¹ * (2 * ((σ : ℝ) - (τ : ℝ))) := by positivity
  calc (θ : ℝ)⁻¹ * (2 * ((σ : ℝ) - (τ : ℝ))) / ‖H‖
      ≤ (θ : ℝ)⁻¹ * (2 * ((σ : ℝ) - (τ : ℝ))) / 1 := by
        gcongr
    _ = 2 * ((σ : ℝ) - (τ : ℝ)) / (θ : ℝ) := by
        rw [div_one]
        field_simp

/-- **The rescaling map is `Φ` up to the homothety `(4R)⁻¹` on differences.**  Translations
cancel, so the whole displacement structure of the normalized picture is that of the linear part
`Tube.normalizationLinear`, scaled by `(4R)⁻¹`. -/
theorem rescaleMap_sub {θ : NNReal} (Tθ : Tube θ E) (R : ℝ) (z w : E) :
    Tθ.rescaleMap R z - Tθ.rescaleMap R w
      = (4 * R)⁻¹ • Tθ.normalizationLinear (z - w) := by
  rw [_root_.Tube.rescaleMap_apply, _root_.Tube.rescaleMap_apply,
    _root_.Tube.normalization_apply, _root_.Tube.normalization_apply,
    normalizationLinear_apply_eq]
  rw [show z - w = (z - Tθ.x) - (w - Tθ.x) from by abel]
  simp only [inner_sub_right]
  module

omit [MeasurableSpace E] [BorelSpace E] in
/-- The centre and the direction of a centred extension. -/
theorem centredExtension_center_direction {s : NNReal} {p q : E} (hpq : p ≠ q) :
    (_root_.Tube.centredExtension s hpq).center = midpoint ℝ p q ∧
      (_root_.Tube.centredExtension s hpq).direction = ‖q - p‖⁻¹ • (q - p) :=
  ofMidpointDirection_center_direction _ _ _

/-- **The direction of the normalized member, read on the source.**

The centred extension of the `Ψ`-image of a core has the direction of `Φ` applied to the source
core, the homothety `(4R)⁻¹` being invisible to normalization
(`Kakeya.ml1Boot.normalize_smul`). -/
theorem centredExtension_rescaleMap_direction {θ : NNReal} {R : ℝ} (hR : 0 < R)
    (Tθ : Tube θ E) {s : NNReal} {p q : E} (hpq : Tθ.rescaleMap R p ≠ Tθ.rescaleMap R q) :
    (_root_.Tube.centredExtension s hpq).direction
      = ‖Tθ.normalizationLinear (q - p)‖⁻¹ • Tθ.normalizationLinear (q - p) := by
  rw [(centredExtension_center_direction hpq).2, rescaleMap_sub]
  exact normalize_smul (by positivity) _

/-- **The transverse-direction budget of item (iv), on the objects the construction produces.**

The two `ρt`-tubes are the centred extensions of the `Ψ`-images of the cores of the container
`Tσ` and of an inner tube `Ub ⊆ Tσ`; their directions are transverse by at most
`2 (σ - τ) / θ`.  At `σ = ρt θ`, `τ = dt θ` this is `2 (ρt - dt)`, the hypothesis `hdir` of
`Kakeya.ml1Boot.exists_itemIV_container_tube`. -/
theorem norm_perp_centredExtension_direction_le {τ σ θ : NNReal} {R : ℝ} (hR : 0 < R)
    (hθ0 : (0 : ℝ) < (θ : ℝ)) (hθ1 : (θ : ℝ) ≤ 1) (hτσ : (τ : ℝ) ≤ (σ : ℝ))
    (Tθ : Tube θ E) (Tσ : Tube σ E) (Ub : Tube τ E) (hsub : Ub.carrier ⊆ Tσ.carrier)
    {sb ss : NNReal}
    (hb : Tθ.rescaleMap R Ub.x ≠ Tθ.rescaleMap R Ub.y)
    (hs : Tθ.rescaleMap R Tσ.x ≠ Tθ.rescaleMap R Tσ.y) :
    ‖(_root_.Tube.centredExtension sb hb).direction
        - (inner ℝ (_root_.Tube.centredExtension ss hs).direction
            (_root_.Tube.centredExtension sb hb).direction : ℝ)
          • (_root_.Tube.centredExtension ss hs).direction‖
      ≤ 2 * ((σ : ℝ) - (τ : ℝ)) / (θ : ℝ) := by
  rw [centredExtension_rescaleMap_direction hR Tθ hb,
    centredExtension_rescaleMap_direction hR Tθ hs]
  exact norm_perp_direction_normalized_le hθ0 hθ1 hτσ Tθ Tσ Ub hsub

/-- **Two points of a `σ`-tube differ by an axial multiple of its direction plus `2 σ`.**

`Tube.exists_axis_repr_of_mem_dilate` applied to each of the two points and subtracted: the
two axial parameters lie in `[-1/2, 1/2]`, so their difference is at most `1` in absolute
value, and the two transverse errors are at most `σ` each. -/
theorem exists_core_repr_of_mem_carrier {σ : NNReal} (Tσ : Tube σ E)
    {z z' : E} (hz : z ∈ Tσ.carrier) (hz' : z' ∈ Tσ.carrier) :
    ∃ t : ℝ, |t| ≤ 1 ∧ ‖(z - z') - t • Tσ.direction‖ ≤ 2 * (σ : ℝ) := by
  obtain ⟨s, hs, hv⟩ := Kakeya.Tube.exists_axis_repr_of_mem_dilate Tσ one_pos
    (_root_.Tube.subset_dilate Tσ le_rfl hz)
  obtain ⟨s', hs', hv'⟩ := Kakeya.Tube.exists_axis_repr_of_mem_dilate Tσ one_pos
    (_root_.Tube.subset_dilate Tσ le_rfl hz')
  rw [one_mul] at hv hv'
  refine ⟨s - s', ?_, ?_⟩
  · have h1 : |s| ≤ 1 / 2 := by simpa using hs
    have h2 : |s'| ≤ 1 / 2 := by simpa using hs'
    have h3 : |s - s'| ≤ |s| + |s'| := by
      simpa [sub_eq_add_neg] using abs_add_le s (-s')
    linarith
  · have hrw : (z - z') - (s - s') • Tσ.direction
        = (z - (Tσ.center + s • Tσ.direction)) - (z' - (Tσ.center + s' • Tσ.direction)) := by
      module
    rw [hrw]
    calc ‖(z - (Tσ.center + s • Tσ.direction)) - (z' - (Tσ.center + s' • Tσ.direction))‖
        ≤ ‖z - (Tσ.center + s • Tσ.direction)‖ + ‖z' - (Tσ.center + s' • Tσ.direction)‖ :=
          norm_sub_le _ _
      _ ≤ 2 * (σ : ℝ) := by linarith

/-- **`Φ` does not blow up the direction of an inner tube.**

The direction `d` of a `σ`-tube inside the `θ`-tube `Tθ` has axial component at most `1` and
transverse component at most `2 (θ - σ) ≤ 2 θ`
(`Kakeya.ml1Boot.norm_perp_direction_le_of_carrier_subset`); `Φ` keeps the first and divides the
second by `θ`, so `‖Φ d‖ ^ 2 ≤ 1 + 4` by Pythagoras.  The point is that **no `θ⁻¹` survives**:
the crude `‖Φ d‖ ≤ θ⁻¹` would make the centre estimates of item (iv) useless. -/
theorem norm_normalizationLinear_direction_le {σ θ : NNReal}
    (hθ0 : (0 : ℝ) < (θ : ℝ)) (hσθ : (σ : ℝ) ≤ (θ : ℝ))
    (Tθ : Tube θ E) (Tσ : Tube σ E) (hsub : Tσ.carrier ⊆ Tθ.carrier) :
    ‖Tθ.normalizationLinear Tσ.direction‖ ≤ 3 := by
  have he : ‖Tθ.direction‖ = 1 := Tθ.norm_direction
  set a : ℝ := (inner ℝ Tθ.direction Tσ.direction : ℝ) with ha
  set P : E := Tσ.direction - a • Tθ.direction with hP
  have hPperp : (inner ℝ Tθ.direction P : ℝ) = 0 := inner_perp_eq_zero he Tσ.direction
  have hPb : ‖P‖ ≤ 2 * ((θ : ℝ) - (σ : ℝ)) :=
    norm_perp_direction_le_of_carrier_subset Tσ Tθ hσθ hsub
  have ha1 : |a| ≤ 1 := by
    have h := abs_real_inner_le_norm Tθ.direction Tσ.direction
    rwa [he, one_mul, Tσ.norm_direction] at h
  have hPs : (inner ℝ Tθ.direction (((θ : ℝ))⁻¹ • P) : ℝ) = 0 := by
    rw [real_inner_smul_right, hPperp, mul_zero]
  have hn : ‖Tθ.normalizationLinear Tσ.direction‖ ^ 2
      = a ^ 2 + (((θ : ℝ))⁻¹ * ‖P‖) ^ 2 := by
    rw [normalizationLinear_apply_eq]
    have h := norm_sq_add_orthogonal he hPs a
    rw [h, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hθ0), mul_pow]
  have hσ0 : (0 : ℝ) ≤ (σ : ℝ) := NNReal.coe_nonneg σ
  have hPb' : ‖P‖ ≤ 2 * (θ : ℝ) := by linarith
  have hP2 : ((θ : ℝ))⁻¹ * ‖P‖ ≤ 2 := by
    calc ((θ : ℝ))⁻¹ * ‖P‖ ≤ ((θ : ℝ))⁻¹ * (2 * (θ : ℝ)) := by
          exact mul_le_mul_of_nonneg_left hPb' (inv_pos.mpr hθ0).le
      _ = 2 := by field_simp
  have hP0 : (0 : ℝ) ≤ ((θ : ℝ))⁻¹ * ‖P‖ := by positivity
  have ha2 : a ^ 2 ≤ 1 := by nlinarith [abs_nonneg a, sq_abs a]
  have hP4 : (((θ : ℝ))⁻¹ * ‖P‖) ^ 2 ≤ 4 := by nlinarith
  have hsq : ‖Tθ.normalizationLinear Tσ.direction‖ ^ 2 ≤ 9 := by
    rw [hn]; linarith
  nlinarith [norm_nonneg (Tθ.normalizationLinear Tσ.direction)]

/-- **The normalized picture of an inner tube has diameter `O(1 / R)`.**

For `z, z'` in a `σ`-tube inside the `θ`-tube `Tθ`, the `Ψ`-images differ by at most
`(4 R)⁻¹ (3 + 2 σ / θ)`.  Written at `σ = ρt θ` this is `(4 R)⁻¹ (3 + 2 ρt)`, and with
`R = Tube.normalization.C 3 = 64` and `ρt ≤ 1/4` it is below `1/64`: that is the slack the
axial clauses `hax`, `hSax` of `Kakeya.ml1Boot.exists_itemIV_container_tube` run on. -/
theorem norm_rescaleMap_sub_le_of_mem_carrier {σ θ : NNReal} {R : ℝ} (hR : 0 < R)
    (hθ0 : (0 : ℝ) < (θ : ℝ)) (hθ1 : (θ : ℝ) ≤ 1) (hσθ : (σ : ℝ) ≤ (θ : ℝ))
    (Tθ : Tube θ E) (Tσ : Tube σ E) (hsub : Tσ.carrier ⊆ Tθ.carrier)
    {z z' : E} (hz : z ∈ Tσ.carrier) (hz' : z' ∈ Tσ.carrier) :
    ‖Tθ.rescaleMap R z - Tθ.rescaleMap R z'‖
      ≤ (4 * R)⁻¹ * (3 + 2 * (σ : ℝ) / (θ : ℝ)) := by
  obtain ⟨t, ht, hv⟩ := exists_core_repr_of_mem_carrier Tσ hz hz'
  have hsplit : Tθ.normalizationLinear (z - z')
      = t • Tθ.normalizationLinear Tσ.direction
        + Tθ.normalizationLinear ((z - z') - t • Tσ.direction) := by
    rw [← map_smul, ← map_add]
    congr 1
    abel
  rw [rescaleMap_sub, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by positivity : (0 : ℝ) < (4 * R)⁻¹)]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hd3 : ‖Tθ.normalizationLinear Tσ.direction‖ ≤ 3 :=
    norm_normalizationLinear_direction_le hθ0 hσθ Tθ Tσ hsub
  have hr : ‖Tθ.normalizationLinear ((z - z') - t • Tσ.direction)‖
      ≤ ((θ : ℝ))⁻¹ * (2 * (σ : ℝ)) := by
    refine le_trans (norm_normalizationLinear_le hθ0 hθ1 Tθ _) ?_
    exact mul_le_mul_of_nonneg_left hv (inv_pos.mpr hθ0).le
  have hts : ‖t • Tθ.normalizationLinear Tσ.direction‖ ≤ 1 * 3 := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul ht hd3 (norm_nonneg _) (by norm_num)
  have hfin : ((θ : ℝ))⁻¹ * (2 * (σ : ℝ)) = 2 * (σ : ℝ) / (θ : ℝ) := by
    field_simp
  calc ‖Tθ.normalizationLinear (z - z')‖
      ≤ ‖t • Tθ.normalizationLinear Tσ.direction‖
        + ‖Tθ.normalizationLinear ((z - z') - t • Tσ.direction)‖ := by
        rw [hsplit]; exact norm_add_le _ _
    _ ≤ 1 * 3 + ((θ : ℝ))⁻¹ * (2 * (σ : ℝ)) := by linarith
    _ = 3 + 2 * (σ : ℝ) / (θ : ℝ) := by rw [hfin]; ring

/-- **The transverse displacement of two normalized points of the container, at the
container's own normalized direction.**

This is the estimate the clauses `hperp`, `hSperp` of
`Kakeya.ml1Boot.exists_itemIV_container_tube` need, and the only one that must beat `ρt`
itself rather than an absolute constant.  It does, with the factor `(4 R)⁻¹ · 2` to spare:
the displacement of two points of `Tσ` splits as a multiple of `Tσ.direction` plus a
transverse error of norm `≤ 2 σ`; `Φ` sends the first to a multiple of `g`, which the
transverse part kills exactly, and expands the second by at most `θ⁻¹`, so what survives is
`(4 R)⁻¹ · 2 σ / θ = (4 R)⁻¹ · 2 ρt`. -/
theorem norm_perp_rescaleMap_sub_le_of_mem_carrier {σ θ : NNReal} {R : ℝ} (hR : 0 < R)
    (hθ0 : (0 : ℝ) < (θ : ℝ)) (hθ1 : (θ : ℝ) ≤ 1)
    (Tθ : Tube θ E) (Tσ : Tube σ E)
    {z z' : E} (hz : z ∈ Tσ.carrier) (hz' : z' ∈ Tσ.carrier) :
    ‖(Tθ.rescaleMap R z - Tθ.rescaleMap R z')
        - (inner ℝ (‖Tθ.normalizationLinear Tσ.direction‖⁻¹
              • Tθ.normalizationLinear Tσ.direction)
            (Tθ.rescaleMap R z - Tθ.rescaleMap R z') : ℝ)
          • (‖Tθ.normalizationLinear Tσ.direction‖⁻¹
              • Tθ.normalizationLinear Tσ.direction)‖
      ≤ (4 * R)⁻¹ * (2 * (σ : ℝ) / (θ : ℝ)) := by
  obtain ⟨t, ht, hv⟩ := exists_core_repr_of_mem_carrier Tσ hz hz'
  set D : E := Tθ.normalizationLinear Tσ.direction with hD
  have hD1 : (1 : ℝ) ≤ ‖D‖ := by
    have h := norm_le_norm_normalizationLinear hθ0 hθ1 Tθ Tσ.direction
    rwa [Tσ.norm_direction] at h
  have hDpos : (0 : ℝ) < ‖D‖ := lt_of_lt_of_le zero_lt_one hD1
  set g : E := ‖D‖⁻¹ • D with hg
  have hgnorm : ‖g‖ = 1 := by
    rw [hg, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (ne_of_gt hDpos)]
  have hDg : D = ‖D‖ • g := by
    rw [hg, smul_smul, mul_inv_cancel₀ (ne_of_gt hDpos), one_smul]
  have hlin : Tθ.normalizationLinear (z - z')
      = (t * ‖D‖) • g + Tθ.normalizationLinear ((z - z') - t • Tσ.direction) := by
    have h1 : Tθ.normalizationLinear (z - z')
        = t • D + Tθ.normalizationLinear ((z - z') - t • Tσ.direction) := by
      rw [hD, ← map_smul, ← map_add]
      congr 1
      abel
    have h2 : (t * ‖D‖) • g = t • D := by rw [← smul_smul, ← hDg]
    rw [h1, h2]
  have hsplit : Tθ.rescaleMap R z - Tθ.rescaleMap R z'
      = (4 * R)⁻¹ • ((t * ‖D‖) • g
          + Tθ.normalizationLinear ((z - z') - t • Tσ.direction)) := by
    rw [rescaleMap_sub, hlin]
  rw [hsplit, perp_smul, perp_add, perp_smul_self hgnorm, zero_add,
    norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : (0 : ℝ) < (4 * R)⁻¹)]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hfin : ((θ : ℝ))⁻¹ * (2 * (σ : ℝ)) = 2 * (σ : ℝ) / (θ : ℝ) := by
    field_simp
  calc ‖Tθ.normalizationLinear ((z - z') - t • Tσ.direction)
        - (inner ℝ g (Tθ.normalizationLinear ((z - z') - t • Tσ.direction)) : ℝ) • g‖
      ≤ ‖Tθ.normalizationLinear ((z - z') - t • Tσ.direction)‖ := norm_perp_le hgnorm _
    _ ≤ ((θ : ℝ))⁻¹ * (2 * (σ : ℝ)) := by
        refine le_trans (norm_normalizationLinear_le hθ0 hθ1 Tθ _) ?_
        exact mul_le_mul_of_nonneg_left hv (inv_pos.mpr hθ0).le
    _ = 2 * (σ : ℝ) / (θ : ℝ) := hfin


omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- **The transverse part is symmetric in two unit vectors.**  Both norms square to
`1 - ⟪d, e⟫ ^ 2`. -/
theorem norm_perp_symm {d e : E} (hd : ‖d‖ = 1) (he : ‖e‖ = 1) :
    ‖e - (inner ℝ d e : ℝ) • d‖ = ‖d - (inner ℝ e d : ℝ) • e‖ := by
  have key : ∀ p q : E, ‖p‖ = 1 → ‖q‖ = 1 →
      ‖q - (inner ℝ p q : ℝ) • p‖ ^ 2 = 1 - (inner ℝ p q : ℝ) ^ 2 := by
    intro p q hp hq
    rw [norm_sub_sq_real, real_inner_smul_right, real_inner_comm q p, norm_smul,
      Real.norm_eq_abs, hp, hq]
    simp only [mul_one, sq_abs]
    ring
  have h1 := key d e hd he
  have h2 : ‖d - (inner ℝ e d : ℝ) • e‖ ^ 2 = 1 - (inner ℝ d e : ℝ) ^ 2 := by
    rw [key e d he hd, real_inner_comm e d]
  nlinarith [norm_nonneg (e - (inner ℝ d e : ℝ) • d), norm_nonneg (d - (inner ℝ e d : ℝ) • e)]

set_option maxHeartbeats 1000000 in
/-- **Fact 2: the normalized member sits in a `12 R`-homothety of the normalized source tube,
centred at the image of the source tube's own centre.**

This is the per-body enlargement clause of `hdilate` in the shape
`ConvexSpaceBody.exists_enlargement_of_homothety` consumes, and the constant `12 R` is
**absolute** -- no `θ⁻¹` survives, which is what makes the clause usable.

The proof is a pullback along `Φ = Tube.normalizationLinear`, whose inverse is
`Tube.dilateAux θ`.  A point of `T̃ k` is `m + s₀ • g + v` with `|s₀| ≤ 1/2`, `‖v‖ ≤ dt` and
`g = Φ d / ‖Φ d‖` the normalized direction; the target point of `U k` is
`c + t₀ • d + Φ⁻¹((1/3) • v)` with `t₀ = s₀ / (3 ‖Φ d‖)`.  The axial term is pulled back
*exactly* onto the axis of `U k`, which is the whole point: the crude estimate
`‖Φ⁻¹ w‖ ≤ ‖w‖` applied to `s₀ • g` would cost a factor `θ⁻¹`, because `g` need not be close
to `T_θ.direction` -- a `τ`-tube inside a `θ`-tube may be tilted by a full right angle when
`θ ≥ 1/2`.  Only the *transverse* remainder `v` is pulled back crudely, and there `Φ⁻¹`
contracts the part orthogonal to `T_θ.direction` by exactly `θ`, so `θ · dt ≤ τ` closes the
budget with no slack lost. -/
theorem carrier_subset_homothety_rescaleMap_image
    {θ τ dt : NNReal} {R : ℝ} (hR : 0 < R)
    (hθ0 : (0 : ℝ) < (θ : ℝ)) (hθ1 : (θ : ℝ) ≤ 1) (hτθ : (τ : ℝ) ≤ (θ : ℝ))
    (hdtθτ : (dt : ℝ) * (θ : ℝ) ≤ (τ : ℝ)) (hdt4 : (dt : ℝ) ≤ 1 / 4)
    (Tθ : Tube θ E) (Uk : Tube τ E) (Tk : Tube dt E)
    (hsub : Uk.carrier ⊆ Tθ.carrier)
    (hcen : Tk.center = Tθ.rescaleMap R Uk.center)
    (hdir : Tk.direction
      = ‖Tθ.normalizationLinear Uk.direction‖⁻¹ • Tθ.normalizationLinear Uk.direction) :
    Tk.carrier ⊆ (fun z => (12 * R) • (z - Tθ.rescaleMap R Uk.center)
        + Tθ.rescaleMap R Uk.center) '' (Tθ.rescaleMap R '' Uk.carrier) := by
  classical
  set e : E := Tθ.direction with hedef
  set d : E := Uk.direction with hddef
  have he1 : ‖e‖ = 1 := Tθ.norm_direction
  have hd1 : ‖d‖ = 1 := Uk.norm_direction
  set D : E := Tθ.normalizationLinear d with hDdef
  have hN1 : (1 : ℝ) ≤ ‖D‖ := by
    have h := norm_le_norm_normalizationLinear hθ0 hθ1 Tθ d
    rwa [hd1] at h
  have hN0 : (0 : ℝ) < ‖D‖ := lt_of_lt_of_le zero_lt_one hN1
  have hdt0 : (0 : ℝ) ≤ (dt : ℝ) := NNReal.coe_nonneg dt
  -- `‖perp_d e‖ ≤ 2 θ`
  have hperpE : ‖e - (inner ℝ d e : ℝ) • d‖ ≤ 2 * (θ : ℝ) := by
    have h := norm_perp_direction_le_of_carrier_subset Uk Tθ hτθ hsub
    rw [← hddef, ← hedef] at h
    rw [norm_perp_symm hd1 he1]
    have hτ0 : (0 : ℝ) ≤ (τ : ℝ) := NNReal.coe_nonneg τ
    linarith
  intro z hz
  obtain ⟨s₀, hs₀, hvz⟩ := Kakeya.Tube.exists_axis_repr_of_mem_dilate Tk one_pos
    (_root_.Tube.subset_dilate Tk le_rfl hz)
  rw [one_mul] at hvz
  set v : E := z - (Tk.center + s₀ • Tk.direction) with hvdef
  have hv : ‖v‖ ≤ (dt : ℝ) := hvz
  set w : E := (3 : ℝ)⁻¹ • v with hwdef
  have hw : ‖w‖ ≤ (dt : ℝ) / 3 := by
    rw [hwdef, norm_smul, Real.norm_eq_abs]
    rw [abs_of_pos (by norm_num : (0:ℝ) < (3:ℝ)⁻¹)]
    linarith
  set a : ℝ := (inner ℝ e w : ℝ) with hadef
  have ha : |a| ≤ (dt : ℝ) / 3 := le_trans (abs_inner_le he1 w) hw
  set y : E := w - a • e with hydef
  have hy : ‖y‖ ≤ (dt : ℝ) / 3 := le_trans (norm_perp_le he1 w) hw
  set t₀ : ℝ := s₀ / (3 * ‖D‖) with ht₀def
  have ht₀ : |t₀| ≤ 1 / 6 := by
    rw [ht₀def, abs_div, abs_of_pos (by positivity : (0:ℝ) < 3 * ‖D‖)]
    rw [div_le_iff₀ (by positivity : (0:ℝ) < 3 * ‖D‖)]
    nlinarith [abs_nonneg s₀]
  set η : E := a • e + (θ : ℝ) • y with hηdef
  set ξ : E := t₀ • d + η with hξdef
  -- `Φ ξ = t₀ • D + w`, i.e. `Φ ξ = (1/3) • (z - Tk.center)`
  have hee : (inner ℝ e e : ℝ) = 1 := by
    rw [real_inner_self_eq_norm_sq, he1]; norm_num
  have hey : (inner ℝ e y : ℝ) = 0 := by
    rw [hydef, hadef]; exact inner_perp_eq_zero he1 w
  have hΦe : Tθ.normalizationLinear e = e := by
    rw [normalizationLinear_apply_eq, ← hedef, hee, one_smul, sub_self, smul_zero, add_zero]
  have hΦy : Tθ.normalizationLinear y = (θ : ℝ)⁻¹ • y := by
    rw [normalizationLinear_apply_eq, ← hedef, hey, zero_smul, zero_add, sub_zero]
  have hΦη : Tθ.normalizationLinear η = w := by
    rw [hηdef, map_add, map_smul, map_smul, hΦe, hΦy, smul_smul,
      mul_inv_cancel₀ (ne_of_gt hθ0), one_smul, hydef]
    abel
  have hΦξ : Tθ.normalizationLinear ξ = t₀ • D + w := by
    rw [hξdef, map_add, map_smul, hΦη, ← hDdef]
  -- the source point
  refine ⟨Tθ.rescaleMap R (Uk.center + ξ), ⟨Uk.center + ξ, ?_, rfl⟩, ?_⟩
  · -- membership in `U k`
    refine mem_carrier_of_axis_bounds Uk (A := 0) (P := (τ : ℝ)) le_rfl ?_ ?_ ?_
    · have hsimp : Uk.center + ξ - Uk.center = ξ := by abel
      rw [hsimp, ← hddef]
      have hdd : (inner ℝ d d : ℝ) = 1 := by
        rw [real_inner_self_eq_norm_sq, hd1]; norm_num
      have hinner : (inner ℝ d ξ : ℝ) = t₀ + (inner ℝ d η : ℝ) := by
        rw [hξdef, inner_add_right, real_inner_smul_right, hdd, mul_one]
      have hη : ‖η‖ ≤ (dt : ℝ) / 3 := by
        have hsplit : ‖η‖ ^ 2 = a ^ 2 + ((θ : ℝ) * ‖y‖) ^ 2 := by
          have h2 : (inner ℝ e ((θ : ℝ) • y) : ℝ) = 0 := by
            rw [real_inner_smul_right, hey, mul_zero]
          rw [hηdef, norm_sq_add_orthogonal he1 h2, norm_smul, Real.norm_eq_abs,
            abs_of_pos hθ0]
        have hyy : (0:ℝ) ≤ ‖y‖ := norm_nonneg y
        have hb : ((θ : ℝ) * ‖y‖) ^ 2 ≤ ‖y‖ ^ 2 := by
          rw [mul_pow]
          nlinarith [mul_nonneg (by nlinarith : (0:ℝ) ≤ 1 - (θ : ℝ) ^ 2) (sq_nonneg ‖y‖)]
        have hwsq : ‖w‖ ^ 2 = a ^ 2 + ‖y‖ ^ 2 := by
          have h := norm_sq_add_orthogonal he1 hey a
          rw [show a • e + y = w from by rw [hydef]; abel] at h
          exact h
        have hw3 : ‖w‖ ^ 2 ≤ ((dt : ℝ) / 3) ^ 2 := by
          have := norm_nonneg w
          nlinarith
        have : ‖η‖ ^ 2 ≤ ((dt : ℝ) / 3) ^ 2 := by
          rw [hsplit]
          nlinarith
        nlinarith [norm_nonneg η]
      have h1 : |(inner ℝ d η : ℝ)| ≤ (dt : ℝ) / 3 := le_trans (abs_inner_le hd1 η) hη
      rw [hinner]
      have := abs_add_le t₀ (inner ℝ d η : ℝ)
      rw [add_zero]
      linarith
    · have hsimp : Uk.center + ξ - Uk.center = ξ := by abel
      rw [hsimp, ← hddef]
      have hperpξ : ξ - (inner ℝ d ξ : ℝ) • d = η - (inner ℝ d η : ℝ) • d := by
        rw [hξdef, perp_add, perp_smul_self hd1, zero_add]
      rw [hperpξ, hηdef, perp_add, perp_smul, perp_smul]
      have hbound : ‖a • (e - (inner ℝ d e : ℝ) • d)
          + (θ : ℝ) • (y - (inner ℝ d y : ℝ) • d)‖
          ≤ |a| * (2 * (θ : ℝ)) + (θ : ℝ) * ‖y‖ := by
        refine le_trans (norm_add_le _ _) ?_
        gcongr
        · rw [norm_smul, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_left hperpE (abs_nonneg a)
        · rw [norm_smul, Real.norm_eq_abs, abs_of_pos hθ0]
          exact mul_le_mul_of_nonneg_left (norm_perp_le hd1 y) hθ0.le
      refine le_trans hbound ?_
      have h1 : |a| * (2 * (θ : ℝ)) ≤ ((dt : ℝ) / 3) * (2 * (θ : ℝ)) := by
        gcongr
      have h2 : (θ : ℝ) * ‖y‖ ≤ (θ : ℝ) * ((dt : ℝ) / 3) := by gcongr
      linarith
    · simp
  · -- the homothety identity
    have hRne : (12 : ℝ) * R ≠ 0 := by positivity
    have hsub' : Tθ.rescaleMap R (Uk.center + ξ) - Tθ.rescaleMap R Uk.center
        = (4 * R)⁻¹ • (t₀ • D + w) := by
      rw [rescaleMap_sub]
      rw [show Uk.center + ξ - Uk.center = ξ from by abel, hΦξ]
    have hz' : z - Tk.center = (3 : ℝ) • (t₀ • D + w) := by
      have hzz : z - Tk.center = s₀ • Tk.direction + v := by
        rw [hvdef]; abel
      rw [hzz, hdir, ht₀def, hwdef]
      match_scalars <;> field_simp
    simp only
    rw [hsub', smul_smul, show (12 : ℝ) * R * (4 * R)⁻¹ = 3 by field_simp; ring, ← hz',
      ← hcen]
    abel

end Normalization

end ml1Boot

end Kakeya

#print axioms Kakeya.ml1Boot.norm_perp_symm
#print axioms Kakeya.ml1Boot.carrier_subset_homothety_rescaleMap_image
