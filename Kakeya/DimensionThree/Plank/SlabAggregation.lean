/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Plank.AssignedSlabFamily
public import Kakeya.DimensionThree.Plank.RelativeMultiplicity

/-!
# Aggregating slab-local union retention into global union retention

Phase E of GWZ Lemma 6.13 has to turn slab-local retention estimates into one global estimate
`ρ · |U| ≤ Nov · |U ∩ G|`, which is what `Plank.isCRefinement_restrictShade_of_dense` consumes.

The bridge is the pointwise slab-overlap bound `Nov` returned by
`Kakeya.plankReduction_preassembly`, and it is worth being precise about *which* overlap it bounds,
because there are two candidate readings and only one of them is both true and available.

`Nov` bounds, at each point `x`, the number of used slabs `S` such that `x` lies in the shading
union of the **geometric** family `Plank.inSlabFamilyC` of `S`.  It does *not* bound the number of
slabs having a selected *box* containing `x` — a point of a box of `S` need not be shaded by any
plank of `S` at all.  So the aggregation must be organised so that the sets being summed are
subsets of the slab shading unions, never of the slab boxes.

That is exactly what the assigned families give.  Each `i ∈ s'` is assigned to a single slab, so the
slab-local unions `U_S = ⋃_{i ∈ 𝒜_S} Y'_i` cover `U`, and
`Plank.assignedSlabFamily_subset_inSlabFamilyC` shows `𝒜_S ⊆ inSlabFamilyC … S`, hence
`U_S` is contained in the set `Nov` counts.  Any retained subset `A_S ⊆ U_S` therefore inherits the
pointwise overlap bound, and
`MeasureTheory.sum_measure_le_mul_measure_biUnion_of_card_filter_le` converts the sum of the
`|A_S|` into `Nov · |⋃_S A_S|`.

No disjointness of the slab unions is claimed or needed — they genuinely overlap, which is why the
factor `Nov` appears and why the *indices* rather than the *shadings* are what partition.
-/

@[expose] public section

open MeasureTheory Convexity
open scoped NNReal Real ENNReal

noncomputable section

namespace Plank

variable {ι : Type*}

/-- The assigned family of a slab sits inside its geometric `Plank.inSlabFamilyC` family.

This is the compatibility between the two families that lets the pointwise slab-overlap bound,
which is stated for the geometric family, be applied to the assigned one. -/
theorem assignedSlabFamily_subset_inSlabFamilyC {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
    {θ : ℝ≥0} {hθ1 : θ ≤ 1} (Cset Cang : ℝ≥0) (s' : Finset ι) (P : ι → Plank a b hab hb1)
    (repr : ι → EnsemblePrism) (slabOf : EnsemblePrism → Slab θ hθ1)
    (hslab : ∀ i ∈ s', i ∈ inSlabFamilyC Cset Cang s' P (slabOf (repr i)))
    (S : Slab θ hθ1) :
    assignedSlabFamily s' repr slabOf S ⊆ inSlabFamilyC Cset Cang s' P S := by
  intro i hi
  exact (mem_assignedSlabFamily.mp hi).2 ▸ hslab i (mem_assignedSlabFamily.mp hi).1

/-- **Sum-form capture upgrades to union-form capture, under constant multiplicity.**

Suppose the shadings lose at most an `f`-fraction of their *total mass* outside a measurable
set `W`, and the family has constant multiplicity `C`.  If `2 · f · C ≤ 1` then `W` captures at
least half of the shading *union*:

`|U| ≤ 2 · |U ∩ W|`.

This is the converse direction to `Plank.isCRefinement_restrictShade_of_dense`, and it is the bridge
the good-box selection needs: that selection controls its discarded mass in the sum norm, while the
dense-ball layer and the retention estimate live in the union norm.

The configuration-dependent factor `m = min_U µ` cancels between the two halves, exactly as in
`Plank.isCRefinement_restrictShade_of_dense`, which is why only the product `f · C` appears and no
uniform multiplicity upper bound is required.  Note the direction of the hypothesis on `f`: a
*smaller* discard fraction is needed when `C` is larger, so a caller with `C = Cmult · a ^ (-εint)`
must run its selection at discard fraction `~a ^ εint`, paying that from the epsilon budget. -/
theorem union_capture_of_sum_capture (s' : Finset ι)
    (Y' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (W : Set (EuclideanSpace ℝ (Fin 3))) (hW : MeasurableSet W)
    (C f : ℝ≥0)
    (hC : ShadedBody.HasCConstantMultiplicity s' Y' C)
    (hdiscard : ∑ i ∈ s', volume ((Y' i).shade \ W)
      ≤ (f : ENNReal) * ∑ i ∈ s', volume (Y' i).shade)
    (hfC : 2 * (f * C) ≤ 1)
    (hUtop : volume (⋃ i ∈ s', (Y' i).shade) ≠ ⊤) :
    volume (⋃ i ∈ s', (Y' i).shade)
      ≤ 2 * volume ((⋃ i ∈ s', (Y' i).shade) ∩ W) := by
  classical
  set U : Set (EuclideanSpace ℝ (Fin 3)) := ⋃ i ∈ s', (Y' i).shade with hUdef
  by_cases hne : U.Nonempty
  · -- `U` is nonempty: pick a point `y` of minimal pointwise multiplicity.
    obtain ⟨y, hyU, hmin⟩ := exists_min_pointwiseMultiplicity s' Y' (by simpa [hUdef] using hne)
    let m : ENNReal := (ShadedBody.pointwiseMultiplicity s' Y' y : ENNReal)
    have hy_mem : ∃ i ∈ s', y ∈ (Y' i).shade := by
      rcases Set.mem_iUnion₂.mp hyU with ⟨i, hi, hysh⟩
      exact ⟨i, hi, hysh⟩
    have hm_ne_zero : m ≠ 0 := by
      dsimp [m]
      exact_mod_cast (ne_of_gt ((ShadedBody.pointwiseMultiplicity_pos_iff s' Y' y).mpr hy_mem))
    have hm_top : m ≠ ⊤ := by
      simp [m]
    -- h1: the discarded mass is at least `m` times the discarded union.
    have h1 : m * volume (U \ W) ≤ ∑ i ∈ s', volume ((Y' i).shade \ W) := by
      have h := mul_volume_inter_le_sum_volume_shade_inter s' Y' hmin Wᶜ
      simpa [hUdef, Set.sdiff_eq] using h
    -- h2: the total shading mass is at most `C * m * volume U`.
    have h2 : ∑ i ∈ s', volume (Y' i).shade ≤ (C : ENNReal) * m * volume U := by
      simpa [hUdef, m] using (sum_volume_shade_le_of_hasCConstantMultiplicity s' Y' hC hyU)
    -- Combine h1, hdiscard, h2 into an `m`-prefactored inequality.
    have hsum_le : m * volume (U \ W) ≤ (f : ENNReal) * ((C : ENNReal) * m * volume U) := by
      calc
        m * volume (U \ W) ≤ ∑ i ∈ s', volume ((Y' i).shade \ W) := h1
        _ ≤ (f : ENNReal) * ∑ i ∈ s', volume (Y' i).shade := hdiscard
        _ ≤ (f : ENNReal) * ((C : ENNReal) * m * volume U) := by
          exact mul_le_mul_right h2 (f : ENNReal)
    have hprod : (f : ENNReal) * ((C : ENNReal) * m * volume U) =
        m * (((f * C : ℝ≥0) : ENNReal) * volume U) := by
      simp [ENNReal.coe_mul, mul_assoc, mul_comm, mul_left_comm]
    have hmul_le : m * volume (U \ W) ≤ m * (((f * C : ℝ≥0) : ENNReal) * volume U) := by
      rw [← hprod]
      exact hsum_le
    have hdiff : volume (U \ W) ≤ ((f * C : ℝ≥0) : ENNReal) * volume U := by
      exact (ENNReal.mul_le_mul_iff_right hm_ne_zero hm_top).mp hmul_le
    -- Scale by 2 and use `2 * (f * C) ≤ 1`.
    have h2diff : 2 * volume (U \ W) ≤ volume U := by
      calc
        2 * volume (U \ W) ≤ 2 * (((f * C : ℝ≥0) : ENNReal) * volume U) := by
          exact mul_le_mul_right hdiff (2 : ENNReal)
        _ = ((2 * (f * C) : ℝ≥0) : ENNReal) * volume U := by
          norm_num [ENNReal.coe_mul, mul_assoc]
        _ ≤ (1 : ENNReal) * volume U := by
          exact mul_le_mul_left (ENNReal.coe_le_coe.mpr hfC) (volume U)
        _ = volume U := by
          rw [one_mul]
    -- `U = (U ∩ W) ∪ (U \ W)` gives `2 * |U| ≤ 2 * |U ∩ W| + |U|`; cancel one `|U|`.
    have hUeq : volume U = volume (U ∩ W) + volume (U \ W) :=
      (measure_inter_add_sdiff U hW).symm
    have hmain : 2 * volume U ≤ 2 * volume (U ∩ W) + volume U := by
      calc
        2 * volume U = 2 * (volume (U ∩ W) + volume (U \ W)) := by
          rw [hUeq]
        _ = 2 * volume (U ∩ W) + 2 * volume (U \ W) := by
          rw [mul_add]
        _ ≤ 2 * volume (U ∩ W) + volume U := by
          exact add_le_add le_rfl h2diff
    have hUtop' : volume U ≠ ⊤ := by simpa [← hUdef] using hUtop
    have hgoal : volume U ≤ 2 * volume (U ∩ W) := by
      have h2' : volume U + volume U ≤ 2 * volume (U ∩ W) + volume U := by
        simpa [two_mul] using hmain
      exact (ENNReal.add_le_add_iff_right hUtop').mp h2'
    exact hgoal
  · -- `U` is empty: both sides are zero.
    have hUempty : U = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    simp [hUempty]

/-- The discard fraction `(2 C_mult)⁻¹ a^{ε}` is exactly the reciprocal of twice the multiplicity
`C_mult a^{-ε}`: the two `rpow` factors cancel, needing only `a ≠ 0`, and no bound `a ≤ 1`. -/
theorem two_mul_discardRate_mul_multiplicity_eq_one {a Cmult : ℝ≥0} (εint : ℝ)
    (hCmult : 0 < Cmult) (ha : 0 < a) :
    2 * (((2 * Cmult)⁻¹ * a ^ εint) * (Cmult * a ^ (-εint))) = 1 := by
  have hrpow : a ^ εint * a ^ (-εint) = 1 := by
    rw [← NNReal.rpow_add ha.ne']
    simp
  have h2C : (2 * Cmult : ℝ≥0) ≠ 0 := mul_ne_zero two_ne_zero hCmult.ne'
  calc
    2 * (((2 * Cmult)⁻¹ * a ^ εint) * (Cmult * a ^ (-εint)))
      = ((2 * Cmult)⁻¹ * (2 * Cmult)) * (a ^ εint * a ^ (-εint)) := by ring
    _ = 1 := by
      rw [inv_mul_cancel₀ h2C, hrpow, mul_one]

/-- The half-form of `Plank.two_mul_discardRate_mul_multiplicity_eq_one`: the discard fraction times
the multiplicity is exactly `1/2`.  This is the `hscale` input of
`Plank.isCRefinement_restrictShade_of_dense` at the retention ratio `1/2`. -/
theorem discardRate_mul_multiplicity_eq_half {a Cmult : ℝ≥0} (εint : ℝ)
    (hCmult : 0 < Cmult) (ha : 0 < a) :
    ((2 * Cmult)⁻¹ * a ^ εint) * (Cmult * a ^ (-εint)) = 2⁻¹ := by
  have h := two_mul_discardRate_mul_multiplicity_eq_one εint hCmult ha
  field_simp at h ⊢
  exact h

/-- **Union-form capture at the `a^{-ε}` multiplicity rate.**  `Plank.union_capture_of_sum_capture`
specialised to the shape the plank layer actually produces: constant multiplicity
`C = C_mult a^{-ε_int}`, and a selection run at the matching discard fraction
`f = (2 C_mult)⁻¹ a^{ε_int}`, for which `2 · f · C = 1` holds exactly.

This is the packaged form of the trade-off noted on `Plank.union_capture_of_sum_capture`: a larger
multiplicity forces a smaller discard fraction, and the price is a power `a^{ε_int}` taken from the
epsilon budget.  Only `0 < C_mult` and `0 < a` are needed — in particular no `a ≤ 1`, since the
cancellation `a^{ε} · a^{-ε} = 1` is exact for every nonzero `a`. -/
theorem union_capture_of_sum_capture_rate {a : ℝ≥0} (s' : Finset ι)
    (Y' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (W : Set (EuclideanSpace ℝ (Fin 3))) (hW : MeasurableSet W)
    (Cmult : ℝ≥0) (εint : ℝ) (hCmult : 0 < Cmult) (ha : 0 < a)
    (hC : ShadedBody.HasCConstantMultiplicity s' Y' (Cmult * a ^ (-εint)))
    (hdiscard : ∑ i ∈ s', volume ((Y' i).shade \ W)
      ≤ (((2 * Cmult)⁻¹ * a ^ εint : ℝ≥0) : ENNReal) * ∑ i ∈ s', volume (Y' i).shade)
    (hUtop : volume (⋃ i ∈ s', (Y' i).shade) ≠ ⊤) :
    volume (⋃ i ∈ s', (Y' i).shade)
      ≤ 2 * volume ((⋃ i ∈ s', (Y' i).shade) ∩ W) := by
  have hfC : 2 * (((2 * Cmult)⁻¹ * a ^ εint) * (Cmult * a ^ (-εint))) ≤ 1 :=
    (two_mul_discardRate_mul_multiplicity_eq_one εint hCmult ha).le
  exact union_capture_of_sum_capture s' Y' W hW (Cmult * a ^ (-εint)) ((2 * Cmult)⁻¹ * a ^ εint)
    hC hdiscard hfC hUtop

/-- **The union capture is a quantitative refinement, at the same rate.**

Cutting the shadings against a set `W` that captures half of the shading union produces a
`ShadedBody.restrictShade` family that is a `ρ'`-refinement of the original, at exactly the discard
fraction `ρ' = (2 C_mult)⁻¹ a^{ε_int}` of `Plank.union_capture_of_sum_capture_rate`: the two are the
same constant because `ρ' · C = 1/2` for `C = C_mult a^{-ε_int}`
(`Plank.discardRate_mul_multiplicity_eq_half`).

So the whole good-box layer costs one factor `a^{ε_int}` in the refinement coefficient and nothing
else.  This is the form `Kakeya.plankReduction` consumes for its refinement output. -/
theorem isCRefinement_restrictShade_of_unionCapture {a : ℝ≥0} (s' : Finset ι)
    (Y' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (Cmult : ℝ≥0) (εint : ℝ) (hCmult : 0 < Cmult) (ha : 0 < a)
    (W : Set (EuclideanSpace ℝ (Fin 3))) (hW : MeasurableSet W)
    (hC : ShadedBody.HasCConstantMultiplicity s' Y' (Cmult * a ^ (-εint)))
    (hcap : volume (⋃ i ∈ s', (Y' i).shade)
      ≤ 2 * volume ((⋃ i ∈ s', (Y' i).shade) ∩ W)) :
    ShadedBody.IsCRefinement s' (fun i => ShadedBody.restrictShade (Y' i) W hW) s' Y'
      ((2 * Cmult)⁻¹ * a ^ εint) := by
  have hdense : ((2⁻¹ : ℝ≥0) : ENNReal) * volume (⋃ i ∈ s', (Y' i).shade)
      ≤ volume ((⋃ i ∈ s', (Y' i).shade) ∩ W) := by
    rw [show ((2⁻¹ : ℝ≥0) : ENNReal) = (2 : ENNReal)⁻¹ by simp]
    rw [ENNReal.inv_mul_le_iff (by norm_num) (by norm_num)]
    exact hcap
  exact isCRefinement_restrictShade_of_dense s' Y' hC hW hdense
    (le_of_eq (discardRate_mul_multiplicity_eq_half εint hCmult ha))

/-- The refinement coefficient of a capture at rate `K⁻¹` against multiplicity `C_mult a^{-ε}` is
`(K C_mult)⁻¹ a^{ε}`, and the product is exactly `K⁻¹`: the two `rpow` factors cancel and `C_mult`
cancels, needing only `a ≠ 0`, `C_mult ≠ 0`, `K ≠ 0`. -/
theorem captureRate_mul_multiplicity_eq_inv {a Cmult K : ℝ≥0} (εint : ℝ)
    (hCmult : Cmult ≠ 0) (ha : a ≠ 0) (hK : K ≠ 0) :
    ((K * Cmult)⁻¹ * a ^ εint) * (Cmult * a ^ (-εint)) = K⁻¹ := by
  have hrpow : a ^ εint * a ^ (-εint) = 1 := by
    rw [← NNReal.rpow_add ha]
    simp
  calc
    ((K * Cmult)⁻¹ * a ^ εint) * (Cmult * a ^ (-εint))
        = ((K * Cmult)⁻¹ * Cmult) * (a ^ εint * a ^ (-εint)) := by ring
    _ = ((K * Cmult)⁻¹ * Cmult) := by rw [hrpow, mul_one]
    _ = K⁻¹ := by
          rw [mul_inv]
          field_simp

/-- **The final restriction is a quantitative refinement, at the localized capture rate.**

The `K = 256 · Nov` counterpart of `Plank.isCRefinement_restrictShade_of_unionCapture`: given the
aggregated localized capture `|U| ≤ K · |U ∩ G|` of
`Plank.volume_le_mul_volume_inter_of_localCapture` and the *global* constant multiplicity
`C_mult a^{-ε_int}`, cutting every shade to `G` is a `(K C_mult)⁻¹ a^{ε_int}`-refinement.

The coefficient is exact: `((K C_mult)⁻¹ a^{ε_int}) · (C_mult a^{-ε_int}) = K⁻¹`
(`Plank.captureRate_mul_multiplicity_eq_inv`), so the only loss on the fullness ledger is the single
factor `a^{ε_int}` plus the fixed constant `K = 256 · Nov`.  The index set is unchanged, so there is
no cardinality loss. -/
theorem isCRefinement_restrictShade_of_localCapture {a : ℝ≥0} (s' : Finset ι)
    (Y' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (Cmult : ℝ≥0) (εint : ℝ) (K : ℝ≥0) (hCmult : 0 < Cmult) (ha : 0 < a) (hK : 0 < K)
    (Gtot : Set (EuclideanSpace ℝ (Fin 3))) (hG : MeasurableSet Gtot)
    (hC : ShadedBody.HasCConstantMultiplicity s' Y' (Cmult * a ^ (-εint)))
    (hcap : volume (⋃ i ∈ s', (Y' i).shade)
      ≤ (K : ENNReal) * volume ((⋃ i ∈ s', (Y' i).shade) ∩ Gtot)) :
    ShadedBody.IsCRefinement s' (fun i => ShadedBody.restrictShade (Y' i) Gtot hG) s' Y'
      ((K * Cmult)⁻¹ * a ^ εint) := by
  have hKne : (K : ℝ≥0) ≠ 0 := hK.ne'
  have hKE : (K : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hKne
  have hdense : ((K⁻¹ : ℝ≥0) : ENNReal) * volume (⋃ i ∈ s', (Y' i).shade)
      ≤ volume ((⋃ i ∈ s', (Y' i).shade) ∩ Gtot) := by
    rw [ENNReal.coe_inv hKne]
    rw [ENNReal.inv_mul_le_iff hKE ENNReal.coe_ne_top]
    exact hcap
  exact isCRefinement_restrictShade_of_dense s' Y' hC hG hdense
    (le_of_eq (captureRate_mul_multiplicity_eq_inv εint hCmult.ne' ha.ne' hKne))

open scoped Classical in
/-- **Aggregate union retention: the honest slab-local interface.**

The retention input is the *aggregate* mass bound `ρ · |U| ≤ ∑_S |A_S|`, not a separate retention
ratio on every slab.  That distinction matters: a per-slab lower bound
`ρ · |U_S| ≤ |A_S|` is not available from the plank layer and must not be assumed — the class
realising a fibre retention depends on the point.  What the good-box selection does deliver is a
single global mass statement, and that is exactly what this form consumes.

The bounded-overlap step is unchanged: the retained pieces inherit the pointwise overlap bound `Nov`
of the local unions, so their masses sum into `Nov · |U ∩ G|`.

`Plank.union_retention_of_slabLocal` is the per-slab corollary. -/
theorem union_retention_of_aggregate {σ : Type*} (𝒮 : Finset σ)
    (Uloc Aloc : σ → Set (EuclideanSpace ℝ (Fin 3)))
    (U G : Set (EuclideanSpace ℝ (Fin 3)))
    (Nov : ℕ) (ρ : ℝ≥0)
    (hAmeas : ∀ S ∈ 𝒮, MeasurableSet (Aloc S))
    (hAsubU : ∀ S ∈ 𝒮, Aloc S ⊆ U ∩ G)
    (hAsubUloc : ∀ S ∈ 𝒮, Aloc S ⊆ Uloc S)
    (hoverlap : ∀ x, (𝒮.filter fun S => x ∈ Uloc S).card ≤ Nov)
    (haggregate : (ρ : ENNReal) * volume U ≤ ∑ S ∈ 𝒮, volume (Aloc S)) :
    (ρ : ENNReal) * volume U ≤ (Nov : ENNReal) * volume (U ∩ G) := by
  have hoverlapAloc : ∀ x, (𝒮.filter fun S => x ∈ Aloc S).card ≤ Nov := by
    intro x
    have hsub : (𝒮.filter fun S => x ∈ Aloc S) ⊆ (𝒮.filter fun S => x ∈ Uloc S) :=
      Finset.monotone_filter_right 𝒮 (fun S hS hx => hAsubUloc S hS hx)
    exact le_trans (Finset.card_le_card hsub) (hoverlap x)
  have hsumAloc :
      ∑ S ∈ 𝒮, volume (Aloc S) ≤ (Nov : ENNReal) * volume (⋃ S ∈ 𝒮, Aloc S) :=
    MeasureTheory.sum_measure_le_mul_measure_biUnion_of_card_filter_le (s := 𝒮) (A := Aloc)
      (μ := volume) (hA := hAmeas) (C := Nov) (hC := hoverlapAloc)
  have hvolUG : volume (⋃ S ∈ 𝒮, Aloc S) ≤ volume (U ∩ G) :=
    measure_mono (Set.iUnion₂_subset hAsubU)
  calc
    (ρ : ENNReal) * volume U ≤ ∑ S ∈ 𝒮, volume (Aloc S) := haggregate
    _ ≤ (Nov : ENNReal) * volume (⋃ S ∈ 𝒮, Aloc S) := hsumAloc
    _ ≤ (Nov : ENNReal) * volume (U ∩ G) := mul_le_mul_right hvolUG (Nov : ENNReal)

open scoped Classical in
/-- **Slab-local union retention aggregates to global union retention, at the cost of `Nov`.**

`Uloc S` is the slab-local shading union and `Aloc S` the part of it retained by the slab-local
construction.  The hypotheses are: the local unions cover `U`; each retained piece lies inside the
global retained set `U ∩ G` and inside its own local union; the local unions have pointwise overlap
at most `Nov`; and each slab retains a `ρ`-fraction of its own local union.

The conclusion is the global retention in the form `ρ · |U| ≤ Nov · |U ∩ G|`, stated
multiplicatively so that no `ENNReal` division is needed at the call site.

This is the per-slab corollary of `Plank.union_retention_of_aggregate`; callers that cannot produce
a per-slab retention ratio should use that form instead. -/
theorem union_retention_of_slabLocal {σ : Type*} (𝒮 : Finset σ)
    (Uloc Aloc : σ → Set (EuclideanSpace ℝ (Fin 3)))
    (U G : Set (EuclideanSpace ℝ (Fin 3)))
    (Nov : ℕ) (ρ : ℝ≥0)
    (hAmeas : ∀ S ∈ 𝒮, MeasurableSet (Aloc S))
    (hUcover : U ⊆ ⋃ S ∈ 𝒮, Uloc S)
    (hAsubU : ∀ S ∈ 𝒮, Aloc S ⊆ U ∩ G)
    (hAsubUloc : ∀ S ∈ 𝒮, Aloc S ⊆ Uloc S)
    (hoverlap : ∀ x, (𝒮.filter fun S => x ∈ Uloc S).card ≤ Nov)
    (hlocal : ∀ S ∈ 𝒮, (ρ : ENNReal) * volume (Uloc S) ≤ volume (Aloc S)) :
    (ρ : ENNReal) * volume U ≤ (Nov : ENNReal) * volume (U ∩ G) := by
  refine union_retention_of_aggregate 𝒮 Uloc Aloc U G Nov ρ hAmeas hAsubU hAsubUloc hoverlap ?_
  -- The per-slab ratios aggregate: `U` is covered by the local unions, and each contributes.
  have hU : volume U ≤ ∑ S ∈ 𝒮, volume (Uloc S) := by
    calc
      volume U ≤ volume (⋃ S ∈ 𝒮, Uloc S) := measure_mono hUcover
      _ ≤ ∑ S ∈ 𝒮, volume (Uloc S) := measure_biUnion_finset_le 𝒮 Uloc
  calc
    (ρ : ENNReal) * volume U ≤ (ρ : ENNReal) * ∑ S ∈ 𝒮, volume (Uloc S) :=
      mul_le_mul_right hU (ρ : ENNReal)
    _ = ∑ S ∈ 𝒮, (ρ : ENNReal) * volume (Uloc S) := by
      rw [Finset.mul_sum]
    _ ≤ ∑ S ∈ 𝒮, volume (Aloc S) := Finset.sum_le_sum hlocal

end Plank

end
