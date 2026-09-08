/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Shading

/-!
# The aggregate mass estimates behind Item 2 of GWZ Lemma 6.13

Item 2 of `Kakeya.plankReduction` is a per-slab fullness lower bound on the thickened family.  This
file collects the measure-theoretic and combinatorial steps that turn *summed* mass inequalities
into that fullness, with no geometry and no power of `a` in any statement.

**Item 2 is aggregate, not representative-wise.**  Asking every representative individually to be
dense would force a representative deletion (a greedy dense-survivor selection), and deletion
merges or destroys the `repr`-fibres, hence the common fibre size `N` that Items 3 and 4 depend on.
The aggregate form `c · ∑_t |Q_carrier t| ≤ ∑_t |Y_θ t|` is exactly what `ShadedBody.fullness` is,
so it is the honest target, it tolerates non-dense members, and it keeps every representative.
`Plank.fullness_ge_of_aggregateMass` and its converse `Plank.aggregateMass_of_fullness_ge` are that
translation.

**Where the Item 2 exponent comes from.**  Reading
`Plank.perRepresentativeDensity_saturated_dilated`, the per-representative density coefficient is a
product of three factors: the dense-box absorption factor, the per-box local fullness `lam` — which
enters *squared*, the GWZ Lemma 6.8 doubling — and the cover fraction `κ` of
`Plank.exists_goodCover_saturated_aggregate`.  Both outputs of the good cover are linear in the
captured-mass density, so the three factors each cost one power of the local fullness exponent and
the Item 2 exponent is `4η` at local fullness `a ^ η`.

`Plank.sum_ge_of_linear_density` is the step that closes the aggregate at a *variable* cover
fraction: every representative is kept and is asked only for the density its own `κ t` supplies,
the average lower bound doing the work of a uniform threshold.  That is why no
representative-retention factor appears in the Item 2 constant.
-/

@[expose] public section

open MeasureTheory Convexity
open scoped NNReal Real ENNReal

noncomputable section

namespace Plank

/-! ## Aggregate fullness -/

/-- **Aggregate mass gives fullness.**  The aggregate counterpart of a termwise density bound:
`ShadedBody.fullness` *is* the ratio of the two sums, so a single summed inequality suffices and no
member has to be dense on its own. -/
theorem fullness_ge_of_aggregateMass {τ : Type*} (𝒯 : Finset τ)
    (Yθ : τ → ShadedBody (EuclideanSpace ℝ (Fin 3))) (c : ℝ≥0)
    (hpos : 0 < ∑ t ∈ 𝒯, volume (Yθ t).carrier)
    (hfin : ∑ t ∈ 𝒯, volume (Yθ t).carrier ≠ ⊤)
    (hmass : (c : ENNReal) * ∑ t ∈ 𝒯, volume (Yθ t).carrier
      ≤ ∑ t ∈ 𝒯, volume (Yθ t).shade) :
    c ≤ ShadedBody.fullness 𝒯 Yθ := by
  apply (ENNReal.coe_le_coe).1
  rw [ShadedBody.coe_fullness 𝒯 Yθ, ENNReal.le_div_iff_mul_le (Or.inl hpos.ne') (Or.inl hfin)]
  exact hmass

/-- **Fullness gives aggregate mass.**  The converse of `Plank.fullness_ge_of_aggregateMass`, in the
form Item 4's `Kakeya.multiplicityStep_fullnessLower` consumes. -/
theorem aggregateMass_of_fullness_ge {τ : Type*} (𝒯 : Finset τ)
    (Yθ : τ → ShadedBody (EuclideanSpace ℝ (Fin 3))) {c : ℝ≥0}
    (hfull : c ≤ ShadedBody.fullness 𝒯 Yθ) :
    (c : ENNReal) * ∑ t ∈ 𝒯, volume (Yθ t).carrier
      ≤ ∑ t ∈ 𝒯, volume (Yθ t).shade := by
  calc
    (c : ENNReal) * ∑ t ∈ 𝒯, volume (Yθ t).carrier
        ≤ (ShadedBody.fullness 𝒯 Yθ : ENNReal) * ∑ t ∈ 𝒯, volume (Yθ t).carrier := by
      exact mul_le_mul' (ENNReal.coe_le_coe.mpr hfull) (le_refl _)
    _ = ∑ t ∈ 𝒯, volume (Yθ t).shade := by
      rw [ShadedBody.sum_volumeReal_shade_eq_fullness_mul]

/-- **The aggregate bound from a variable cover fraction, with no deletion and no retention.**
Every member of `𝒯` is kept and is asked only for the density its *own* cover fraction `κ t`
supplies; what closes the aggregate is the *average* lower bound `hsum`, not a threshold met by a
selected few.  Consequently no cardinality-retention factor appears and the exponent is exactly
`α + ρ`.

The content is linear: sum `hmass`, pull the common `c a^α v` out, apply `hsum`, and split
`a^(α+ρ) = a^α a^ρ`.  No Jensen or power-mean step is involved, because the geometry supplies the
density as `λ² · κ(t)` — linear in the representative-dependent factor.

The equal-carrier-volume hypothesis `hvol` is not a restriction: the anchors of a thickened
representative family all have volume exactly `8 θ b ^ 2` (`Plank.volume_indexSet_eq`) and the
carriers are a fixed dilation of them. -/
theorem sum_ge_of_linear_density {τ : Type*} (𝒯 : Finset τ)
    (Yθ : τ → ShadedBody (EuclideanSpace ℝ (Fin 3))) (κ : τ → ℝ≥0)
    (a c cKappa : ℝ≥0) (α ρ : ℝ) (v : ENNReal) (ha : 0 < a)
    (hvol : ∀ t ∈ 𝒯, volume (Yθ t).carrier = v)
    (hsum : ((cKappa * a ^ ρ : ℝ≥0) : ENNReal) * (𝒯.card : ENNReal)
      ≤ ∑ t ∈ 𝒯, ((κ t : ℝ≥0) : ENNReal))
    (hmass : ∀ t ∈ 𝒯, ((c * a ^ α * κ t : ℝ≥0) : ENNReal) * volume (Yθ t).carrier
      ≤ volume (Yθ t).shade) :
    ((c * cKappa * a ^ (α + ρ) : ℝ≥0) : ENNReal) * ∑ t ∈ 𝒯, volume (Yθ t).carrier
      ≤ ∑ t ∈ 𝒯, volume (Yθ t).shade := by
  have ha_ne : a ≠ 0 := ha.ne'
  have ha_pow : (a ^ (α + ρ) : ℝ≥0) = a ^ α * a ^ ρ := NNReal.rpow_add ha_ne α ρ
  have hsumT : ∑ t ∈ 𝒯, volume (Yθ t).carrier = (𝒯.card : ENNReal) * v := by
    calc
      ∑ t ∈ 𝒯, volume (Yθ t).carrier = ∑ t ∈ 𝒯, v :=
        Finset.sum_congr rfl fun t ht => by rw [hvol t ht]
      _ = (𝒯.card : ENNReal) * v := by
        simp [Finset.sum_eq_card_nsmul]
  calc
    ((c * cKappa * a ^ (α + ρ) : ℝ≥0) : ENNReal) * ∑ t ∈ 𝒯, volume (Yθ t).carrier
        = (((c * a ^ α : ℝ≥0) : ENNReal) * v) *
            (((cKappa * a ^ ρ : ℝ≥0) : ENNReal) * (𝒯.card : ENNReal)) := by
          rw [hsumT, ha_pow]
          simp only [ENNReal.coe_mul]
          ring
    _ ≤ ((c * a ^ α : ℝ≥0) : ENNReal) * v * (∑ t ∈ 𝒯, ((κ t : ℝ≥0) : ENNReal)) := by
      exact mul_le_mul_right hsum (((c * a ^ α : ℝ≥0) : ENNReal) * v)
    _ = ∑ t ∈ 𝒯, ((c * a ^ α * κ t : ℝ≥0) : ENNReal) * v := by
      calc
        ((c * a ^ α : ℝ≥0) : ENNReal) * v * (∑ t ∈ 𝒯, ((κ t : ℝ≥0) : ENNReal))
            = ((c * a ^ α : ℝ≥0) : ENNReal) * (∑ t ∈ 𝒯, ((κ t : ℝ≥0) : ENNReal)) * v := by
              ring
        _ = (∑ t ∈ 𝒯, ((c * a ^ α : ℝ≥0) : ENNReal) * ((κ t : ℝ≥0) : ENNReal)) * v := by
              rw [Finset.mul_sum]
        _ = (∑ t ∈ 𝒯, ((c * a ^ α * κ t : ℝ≥0) : ENNReal)) * v := by
              refine congrArg (fun x => x * v) ?_
              refine Finset.sum_congr rfl ?_
              intro t ht
              rw [← ENNReal.coe_mul]
        _ = ∑ t ∈ 𝒯, ((c * a ^ α * κ t : ℝ≥0) : ENNReal) * v := by
              rw [Finset.sum_mul]
    _ = ∑ t ∈ 𝒯, ((c * a ^ α * κ t : ℝ≥0) : ENNReal) * volume (Yθ t).carrier := by
      refine Finset.sum_congr rfl ?_
      intro t ht
      rw [hvol t ht]
    _ ≤ ∑ t ∈ 𝒯, volume (Yθ t).shade := by
      exact Finset.sum_le_sum hmass

open scoped Classical in
/-- **The average cover fraction of the full family.**  The combinatorial half of the C-linear
route, with no geometry in it.

Each representative `u` carries a score `m u` and a `rep`-fibre `s.filter (rep · = u)`, and its
cover fraction is the score normalised by `nrm` times the fibre size — the same normalisation the
Markov step divides by, only never replaced by a threshold.  Given

* an aggregate score bound `T · #s ≤ ∑_u m u`, and
* near-constant fibre sizes `L ≤ #(rep⁻¹ u) ≤ W` on `𝒯`,

the *average* cover fraction is bounded below by `T L / (nrm W)`.  This is the inequality the
Markov step throws away: it converts the aggregate score into a statement about every
representative at once, rather than about a selected subfamily, so no cardinality retention factor
is created.

The two fibre bounds enter in opposite places and for different reasons: `W` bounds the
normalisation of each individual cover fraction from above, while `L` converts `#s` into `#𝒯`.  In
the application both are the preassembly's `N / cN ≤ #(rep⁻¹ u) ≤ cN N`, so the constant loses
exactly `cN ^ (-2)` and no power of `a`.

`0 < L` is not a restriction: on `𝒯 = s.image rep` every fibre is nonempty.  It is what rules out
the degenerate `m u / 0 = 0`. -/
theorem sum_coverFraction_ge {ι σ : Type*} (𝒯 : Finset σ) (s : Finset ι) (rep : ι → σ)
    (m : σ → ℝ≥0) (nrm T L W : ℝ≥0)
    (hnrm : 0 < nrm) (hL : 0 < L) (hW : 0 < W)
    (hmaps : ∀ i ∈ s, rep i ∈ 𝒯)
    (hlo : ∀ u ∈ 𝒯, L ≤ (((s.filter (fun i => rep i = u)).card : ℕ) : ℝ≥0))
    (hup : ∀ u ∈ 𝒯, (((s.filter (fun i => rep i = u)).card : ℕ) : ℝ≥0) ≤ W)
    (hagg : T * (s.card : ℝ≥0) ≤ ∑ u ∈ 𝒯, m u) :
    T * L / (nrm * W) * (𝒯.card : ℝ≥0)
      ≤ ∑ u ∈ 𝒯, m u / (nrm * (((s.filter (fun i => rep i = u)).card : ℕ) : ℝ≥0)) := by
  set w : σ → ℝ≥0 := fun u => (((s.filter (fun i => rep i = u)).card : ℕ) : ℝ≥0)
  have hden_pos : 0 < nrm * W := mul_pos hnrm hW
  -- Step 1: termwise, the denominator `nrm * (fibre size)` is positive and bounded by `nrm * W`,
  -- so `m u / (nrm * W) ≤ m u / (nrm * w u)`.
  have hstep1 : ∀ u ∈ 𝒯, m u / (nrm * W) ≤ m u / (nrm * w u) := by
    intro u hu
    have hw : 0 < w u := lt_of_lt_of_le hL (by simpa [w] using hlo u hu)
    have hnrmw_pos : 0 < nrm * w u := mul_pos hnrm hw
    have hnrmw_le : nrm * w u ≤ nrm * W := by
      exact mul_le_mul_of_nonneg_left (by simpa [w] using hup u hu) (le_of_lt hnrm)
    exact div_le_div_of_nonneg_left (by positivity) hnrmw_pos hnrmw_le
  -- Step 2: pull the constant denominator out of the sum.
  have hsum : (∑ u ∈ 𝒯, m u) / (nrm * W) ≤ ∑ u ∈ 𝒯, m u / (nrm * w u) := by
    calc
      (∑ u ∈ 𝒯, m u) / (nrm * W) = ∑ u ∈ 𝒯, m u / (nrm * W) := Finset.sum_div 𝒯 m (nrm * W)
      _ ≤ ∑ u ∈ 𝒯, m u / (nrm * w u) := Finset.sum_le_sum hstep1
  -- Step 3: the fibres partition `s`, so `#s = ∑_u #(rep⁻¹ u)`; cast to `ℝ≥0`.
  have hpartition : (s.card : ℝ≥0) = ∑ u ∈ 𝒯, w u := by
    have hmaps_set : (s : Set ι).MapsTo rep (𝒯 : Set σ) := fun x hx => hmaps x hx
    have hnat : s.card = ∑ u ∈ 𝒯, (s.filter (fun i => rep i = u)).card :=
      Finset.card_eq_sum_card_fiberwise hmaps_set
    rw [hnat]
    simp [w]
  have hLC : L * (𝒯.card : ℝ≥0) ≤ (s.card : ℝ≥0) := by
    calc
      L * (𝒯.card : ℝ≥0) = ∑ u ∈ 𝒯, L := by
        simp [Finset.sum_const, nsmul_eq_mul, mul_comm]
      _ ≤ ∑ u ∈ 𝒯, w u := Finset.sum_le_sum (fun u hu => by simpa [w] using hlo u hu)
      _ = (s.card : ℝ≥0) := by exact hpartition.symm
  -- Step 4: assemble.
  calc
    T * L / (nrm * W) * (𝒯.card : ℝ≥0)
        = (T * (L * (𝒯.card : ℝ≥0))) / (nrm * W) := by
          rw [div_eq_mul_inv, div_eq_mul_inv]
          ring
    _ ≤ (T * (s.card : ℝ≥0)) / (nrm * W) := by
          exact div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left hLC (by positivity)) (le_of_lt hden_pos)
    _ ≤ (∑ u ∈ 𝒯, m u) / (nrm * W) := by
          exact div_le_div_of_nonneg_right hagg (le_of_lt hden_pos)
    _ ≤ ∑ u ∈ 𝒯, m u / (nrm * w u) := hsum

/-- **Descending a finite aggregate score bound from `ℝ≥0∞` to `ℝ≥0`.**  Volumes live in `ℝ≥0∞`,
but the cover fraction has to be an `ℝ≥0`, because that is what
`Plank.perRepresentativeDensity_saturated_dilated` consumes.  `ENNReal.toNNReal` is faithful
precisely on finite values, so termwise finiteness — supplied in the application by
`Plank.fibreLocalScore_ne_top` — is exactly what carries an aggregate lower bound across. -/
theorem sum_toNNReal_ge_of_aggregate {σ : Type*} (𝒯 : Finset σ) (M : σ → ENNReal) (c : ℝ≥0) (n : ℕ)
    (hfin : ∀ u ∈ 𝒯, M u ≠ ⊤)
    (hagg : (c : ENNReal) * (n : ENNReal) ≤ ∑ u ∈ 𝒯, M u) :
    c * (n : ℝ≥0) ≤ ∑ u ∈ 𝒯, (M u).toNNReal := by
  have hcastR : (↑(∑ u ∈ 𝒯, (M u).toNNReal) : ENNReal) = ∑ u ∈ 𝒯, M u := by
    rw [ENNReal.ofNNReal_finsetSum]
    refine Finset.sum_congr rfl ?_
    intro u hu
    exact ENNReal.coe_toNNReal (hfin u hu)
  have hkey : ((c * (n : ℝ≥0) : ℝ≥0) : ENNReal)
      ≤ ((∑ u ∈ 𝒯, (M u).toNNReal : ℝ≥0) : ENNReal) := by
    calc
      ((c * (n : ℝ≥0) : ℝ≥0) : ENNReal) = (c : ENNReal) * (n : ENNReal) := by
        rw [ENNReal.coe_mul, ENNReal.coe_natCast]
      _ ≤ ∑ u ∈ 𝒯, M u := hagg
      _ = ((∑ u ∈ 𝒯, (M u).toNNReal : ℝ≥0) : ENNReal) := hcastR.symm
  exact ENNReal.coe_le_coe.mp hkey

end Plank

end
