/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSiteClosure

/-!
# A producer for `Kakeya.ML2Core.SiteWitness`

`Kakeya.ML2Core.SiteWitness` (`Reduction/SpineSiteClosure.lean:93-112`, body pin
`19559d0d5eb7ebd9d9db4b35d9050900`) is the *selection* half of the site discharge.  Before this
file the tree carried only the non-vacuity witness `Kakeya.ML2Wit.exists_siteWitness_nonvacuity`
and the trivial rows `Kakeya.ML2Core.siteWitnessRows_of_trivial` (`u' = s`, `lam = 1`, `K = 1`),
neither of which is a producer: the `∀ s T` obligation is the site's.

This file supplies `Kakeya.ML2Core.siteWitness_of_scalars`, an unconditional producer at the
absolute constant `Cu₀ = ShadedTube.ssfUniformConst 3`, under four scalar conditions.

## The route, and where the source charges each step

Refined source `260115_kakeyadetailedproofv3_revised_detailed.tex`, Lemma "One trial"
(l.5793-5860), and the opening of its proof (l.5852-5860).

1. **The dyadic selection.**  The source discards the tubes with `|Z(T)| < δ^{10}|T|` (l.5854) and
   then performs one joint dyadic selection on `w(T) = |Z(T)|/|T|` (l.5860).  Here both are done at
   once by `Kakeya.ML2Shaded.exists_denseShading_refinement`, which is strictly cheaper: it retains
   half the shaded mass (`K`-cost `2`, not a logarithm) and returns the *pointwise* invariant
   `HasDenseShading (fullness s V / 2)`.  The source's `Λ_0 ≤ (2 + log₂(1/δ))^{K_0}` (l.5866) is an
   upper bound on the loss, so paying only `2` is inside the source's budget.

2. **The uniformisation.**  `Tube.exists_uniformTubeSet_subfamily_ssf` at `K₀ = 4`, which is
   exactly the source's cardinality input `#𝕋 ≤ 2^{11}A₀δ^{-4}` (l.5782, l.5858) in the form the
   tree carries it.  It returns `UniformTubeSet u' T (ssfGridLen δ) (uniformConst 3)` at a
   *cardinality* retention `#u₁ ≤ δ^{-α} #u'` with `α > 0` **free**.  Freedom of `α` is what makes
   the budget row close; see `Kakeya.ML2Core.siteWitnessAlpha`.

3. **Cardinality back to mass.**  The uniformisation pays in cardinality and the ledger row is
   stated in mass, so the two are tied by `Kakeya.ML2Core.sum_shade_le_of_card_le_of_denseShading`:
   under a pointwise dense shading at level `lam`, congruence of `δ`-tubes converts a card ratio
   `R` into a mass ratio `R · C/(lam · c)` with `C`, `c` the dimensional volume bracket
   (`Tube.volume_le`, `Tube.le_volume`).  This is the step that costs `lam^{-1} ≤ 2δ^{-η}` and it
   is the reason the producer needs `η + aL < dm` rather than merely `aL ≤ dm`.

## The four scalar conditions, and what licenses them

* `hη1 : η ≤ 1` — the hypothesis of `Kakeya.ML2Assembly.card_le_rpow_neg_four`, the tree's form of
  the source's `#𝕋 ≤ 2^{11}A₀δ^{-4}` (l.5782).  The source's `η₀` is chosen last and small
  (l.5794-5800: "there are `ν₀, η₀ > 0`... depending only on this fixed data"), so `η ≤ 1` is
  free.
* `haL0 : 0 < aL` — forced by the skeleton, not by this file
  (`Kakeya.ML2Core.geometricCoreAt_of_witness_and_trial` instantiates `T-D5` at `aL`;
   the parameter comparison).
* `hladder : η + aL ≤ ηin` — the lam-ladder row 7.  The selection delivers
  `lam ≥ δ^η/2` from the fullness input `λ(s,Z) ≥ δ^η`, and row 7 asks for `δ^{ηin-aL}/2 ≤ lam`.
  The source's own ladder has the same shape: the trial is entered at `λ ≥ δ^{2η₀}` (l.5836) while
  the input carries `δ^{η₀}`, i.e. the ladder exponent is *above* the input exponent.
* `hbudget : η + aL < dm` — the budget row 10.  **Strict**, and strictly stronger than the
  skeleton's `aL ≤ dm`.  This is a measured cost of step 3 above, reported rather than hidden: a
  producer that retains a *proper* subfamily must pay `lam^{-1}` to convert the uniformisation's
  cardinality price into the ledger's mass price, and `lam ≍ δ^η`.  At `aL = dm` the row reads
  `K ≤ 1`, which no proper retention can meet.
-/

@[expose] public section

open MeasureTheory Metric ConvexSpaceBody ShadedBody
open scoped NNReal ENNReal Topology

namespace Kakeya.ML2Core

/-! ## Cardinality retention to mass retention -/

section CardToMass

variable {ι : Type*}

/-- **A cardinality retention is a mass retention, at the price of the shading level.**

If `u' ⊆ u` carries a pointwise dense shading at level `lam` and `#u ≤ R · #u'`, then the shaded
mass of `u` is at most `R · C/(lam · c)` times that of `u'`, with `C`, `c` the dimensional volume
bracket of a `δ`-tube.  Stated multiplicatively so that no division appears.

This is the step the site's producer cannot avoid: `Tube.exists_uniformTubeSet_subfamily_ssf` pays
in cardinality, while `Kakeya.ML2Core.stateMass` is a mass. -/
theorem sum_shade_le_of_card_le_of_denseShading {δ : NNReal} (hδ1 : δ ≤ 1)
    {u u' : Finset ι} {V : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))} {lam : NNReal}
    (hdense : ML2Shaded.HasDenseShading lam u' (fun i => (V i).toShadedBody))
    {R : ℝ≥0∞} (hcard : (u.card : ℝ≥0∞) ≤ R * (u'.card : ℝ≥0∞)) :
    (lam : ℝ≥0∞) * (Tube.le_volume.c 3 : ℝ≥0∞) * (∑ i ∈ u, volume (V i).shade)
      ≤ (Tube.volume_le.C 3 : ℝ≥0∞) * R * ∑ i ∈ u', volume (V i).shade := by
  classical
  have hE : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
  -- the upper bracket on `u`
  have hup : (∑ i ∈ u, volume (V i).shade)
      ≤ (u.card : ℝ≥0∞) * ((Tube.volume_le.C 3 : ℝ≥0∞) * (δ : ℝ≥0∞) ^ 2) := by
    calc (∑ i ∈ u, volume (V i).shade)
        ≤ ∑ _i ∈ u, ((Tube.volume_le.C 3 : ℝ≥0∞) * (δ : ℝ≥0∞) ^ 2) := by
          refine Finset.sum_le_sum ?_
          intro i _
          refine le_trans (measure_mono (V i).shade_subset) ?_
          have h := Tube.volume_le (E := EuclideanSpace ℝ (Fin 3)) hδ1 (V i).toTube
          rw [hE] at h
          refine le_trans h (le_of_eq ?_)
          push_cast
          norm_num
      _ = (u.card : ℝ≥0∞) * ((Tube.volume_le.C 3 : ℝ≥0∞) * (δ : ℝ≥0∞) ^ 2) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  -- the lower bracket on `u'`, through the pointwise dense shading
  have hlo : (lam : ℝ≥0∞) * ((u'.card : ℝ≥0∞) * ((Tube.le_volume.c 3 : ℝ≥0∞) * (δ : ℝ≥0∞) ^ 2))
      ≤ ∑ i ∈ u', volume (V i).shade := by
    have hstep : ∀ i ∈ u', (lam : ℝ≥0∞) * ((Tube.le_volume.c 3 : ℝ≥0∞) * (δ : ℝ≥0∞) ^ 2)
        ≤ volume (V i).shade := by
      intro i hi
      refine le_trans ?_ (hdense i hi)
      have h := Tube.le_volume (E := EuclideanSpace ℝ (Fin 3)) (V i).toTube
      rw [hE] at h
      norm_num at h
      have h' : ((Tube.le_volume.c 3 : ℝ≥0∞) * (δ : ℝ≥0∞) ^ 2)
          ≤ volume ((V i).toShadedBody).carrier := by exact_mod_cast h
      gcongr
    calc (lam : ℝ≥0∞) * ((u'.card : ℝ≥0∞) * ((Tube.le_volume.c 3 : ℝ≥0∞) * (δ : ℝ≥0∞) ^ 2))
        = ∑ _i ∈ u', (lam : ℝ≥0∞) * ((Tube.le_volume.c 3 : ℝ≥0∞) * (δ : ℝ≥0∞) ^ 2) := by
          rw [Finset.sum_const, nsmul_eq_mul]; ring
      _ ≤ ∑ i ∈ u', volume (V i).shade := Finset.sum_le_sum hstep
  calc (lam : ℝ≥0∞) * (Tube.le_volume.c 3 : ℝ≥0∞) * (∑ i ∈ u, volume (V i).shade)
      ≤ (lam : ℝ≥0∞) * (Tube.le_volume.c 3 : ℝ≥0∞)
          * ((u.card : ℝ≥0∞) * ((Tube.volume_le.C 3 : ℝ≥0∞) * (δ : ℝ≥0∞) ^ 2)) := by gcongr
    _ ≤ (lam : ℝ≥0∞) * (Tube.le_volume.c 3 : ℝ≥0∞)
          * ((R * (u'.card : ℝ≥0∞)) * ((Tube.volume_le.C 3 : ℝ≥0∞) * (δ : ℝ≥0∞) ^ 2)) := by gcongr
    _ = (Tube.volume_le.C 3 : ℝ≥0∞) * R
          * ((lam : ℝ≥0∞) * ((u'.card : ℝ≥0∞)
              * ((Tube.le_volume.c 3 : ℝ≥0∞) * (δ : ℝ≥0∞) ^ 2))) := by ring
    _ ≤ (Tube.volume_le.C 3 : ℝ≥0∞) * R * ∑ i ∈ u', volume (V i).shade := by gcongr

end CardToMass

/-! ## The scalars the producer spends -/

section Scalars

/-- **The uniformisation exponent the producer spends.**  `Tube.exists_uniformTubeSet_subfamily_ssf`
takes any `α > 0`; the producer takes half the slack left in the budget row after the shading level
`lam ≍ δ^η` has been paid for.  With this choice the budget row's residual exponent is again `α`. -/
noncomputable def siteWitnessAlpha (η aL dm : ℝ) : ℝ := (dm - aL - η) / 2

theorem siteWitnessAlpha_pos {η aL dm : ℝ} (h : η + aL < dm) : 0 < siteWitnessAlpha η aL dm := by
  unfold siteWitnessAlpha; linarith

/-- **The absolute constant of the producer's mass ledger.**  `4 = 2` (the dense-shading discard)
times `2` (the `/2` in the shading level `fullness / 2`), against the dimensional volume bracket. -/
noncomputable def siteWitnessConst : NNReal :=
  4 * Tube.volume_le.C 3 / Tube.le_volume.c 3

end Scalars


/-- **A fixed constant times a positive power of the scale is eventually at most `1`.**  The
`ENNReal` form the budget row needs; proved in `NNReal` and coerced, so no `⊤` bookkeeping. -/
theorem eventually_coe_mul_rpow_le_one (C : NNReal) {p : ℝ} (hp : 0 < p) :
    ∀ᶠ (δ : NNReal) in 𝓝[>] 0, (C : ℝ≥0∞) * (δ : ℝ≥0∞) ^ p ≤ 1 := by
  have hC1 : (0 : NNReal) < (C + 1)⁻¹ := by positivity
  have ht0 : (0 : NNReal) < ((C + 1)⁻¹) ^ (1 / p) := NNReal.rpow_pos hC1
  filter_upwards [Ioo_mem_nhdsGT ht0] with δ hδ
  obtain ⟨hδ0, hδt⟩ := hδ
  have hkey : C * δ ^ p ≤ 1 := by
    have h1 : (δ : NNReal) ^ p ≤ (((C + 1)⁻¹) ^ (1 / p)) ^ p :=
      NNReal.rpow_le_rpow hδt.le hp.le
    have h2 : (((C + 1)⁻¹ : NNReal) ^ (1 / p)) ^ p = (C + 1)⁻¹ := by
      rw [← NNReal.rpow_mul, one_div, inv_mul_cancel₀ hp.ne', NNReal.rpow_one]
    rw [h2] at h1
    calc C * δ ^ p ≤ C * (C + 1)⁻¹ := by gcongr
      _ ≤ (C + 1) * (C + 1)⁻¹ := by gcongr; exact le_self_add
      _ = 1 := mul_inv_cancel₀ (by positivity)
  have hcoe : (C : ℝ≥0∞) * (δ : ℝ≥0∞) ^ p = ((C * δ ^ p : NNReal) : ℝ≥0∞) := by
    rw [ENNReal.coe_mul, ENNReal.coe_rpow_of_ne_zero hδ0.ne']
  rw [hcoe]
  exact_mod_cast hkey

/-! ## The producer -/

section Producer

/-- **A producer for `Kakeya.ML2Core.SiteWitness`.**

Unconditional in the family: for every Katz-Tao family `s` of shaded `δ`-tubes in the unit ball
with fullness at least `δ^η` and `δ^{-1} ≤ #s`, the ten rows are produced at the absolute constant
`ShadedTube.ssfUniformConst 3`, on a tail of `δ`.

The four scalar conditions are discussed in the module docstring; `hbudget` is strict and is
strictly stronger than the skeleton's `aL ≤ dm`, which is the measured price of retaining a proper
subfamily. -/
theorem siteWitness_of_scalars {η ηin dm aL : ℝ} (hη1 : η ≤ 1) (haL0 : 0 < aL)
    (hladder : η + aL ≤ ηin) (hbudget : η + aL < dm) :
    SiteWitness.{v} η ηin dm aL (ShadedTube.ssfUniformConst 3) := by
  classical
  set α : ℝ := siteWitnessAlpha η aL dm with hαdef
  have hα0 : 0 < α := siteWitnessAlpha_pos hbudget
  have hEr : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
  -- the uniformisation threshold
  obtain ⟨δ₀, hδ₀pos, hδ₀le1, huni⟩ :=
    Tube.exists_uniformTubeSet_subfamily_ssf.{v} (E := EuclideanSpace ℝ (Fin 3)) 4 α hα0
  have hδ₀mem : ∀ᶠ (δ : NNReal) in 𝓝[>] 0, δ ≤ δ₀ := by
    have hmem : Set.Ioo (0 : NNReal) δ₀ ∈ 𝓝[>] (0 : NNReal) := Ioo_mem_nhdsGT hδ₀pos
    filter_upwards [hmem] with δ hδ using hδ.2.le
  -- the budget tail
  have hbud : ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
      (siteWitnessConst : ℝ≥0∞) * (δ : ℝ≥0∞) ^ α ≤ 1 := by
    exact eventually_coe_mul_rpow_le_one siteWitnessConst hα0
  filter_upwards [ML2Assembly.eventually_card_thresholds, hδ₀mem, hbud, self_mem_nhdsWithin]
    with δ hthr hδδ₀ hbudδ hδmem
  obtain ⟨hδ0, hδ1, hδC⟩ := hthr
  clear hδmem
  intro ι s T hball hKT hfull hcardlow
  -- notation
  set W : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)) := fun i => (T i).toShadedBody with hWdef
  have hδE0 : (δ : ℝ≥0∞) ≠ 0 := by simpa using hδ0.ne'
  have hδE1 : (δ : ℝ≥0∞) ≤ 1 := by exact_mod_cast hδ1
  -- row 2: the crude cardinality bound
  have hmax : maxDensity s (fun i => (T i).toConvexSpaceBody) ≤ (δ : ℝ≥0∞) ^ (-η) := hKT
  have hcard4 : (s.card : ℝ) ≤ (δ : ℝ) ^ (-(4 : ℝ)) :=
    ML2Assembly.card_le_rpow_neg_four hδ0 hδ1 hδC s T hball hη1 hmax
  -- `s` is nonempty and carries positive shaded mass
  have hsne : s.Nonempty := by
    rcases Finset.eq_empty_or_nonempty s with h | h
    · rw [h] at hcardlow
      simp only [Finset.card_empty, Nat.cast_zero] at hcardlow
      have : (0 : ℝ) < (δ : ℝ)⁻¹ := by positivity
      linarith
    · exact h
  have hfullpos : 0 < ShadedBody.fullness s W := by
    have hpow : (0 : NNReal) < δ ^ η := NNReal.rpow_pos hδ0
    exact lt_of_lt_of_le hpow hfull
  -- step 1: the dense-shading refinement (rows 5, 6, 7 and the first half of row 9)
  obtain ⟨u₁, hu₁s, hmass1, hdense1⟩ := ML2Shaded.exists_denseShading_refinement s W
  set lam : NNReal := ShadedBody.fullness s W / 2 with hlamdef
  have hlampos : 0 < lam := by rw [hlamdef]; positivity
  -- `u₁` is nonempty
  have hshadene : (∑ i ∈ s, volume (W i).shade) ≠ 0 := by
    intro h
    have hz : ShadedBody.fullness' s W = 0 := by
      rw [ShadedBody.fullness', h, ENNReal.zero_div]
    have hc := ShadedBody.coe_fullness s W
    rw [hz] at hc
    have hf0 : ShadedBody.fullness s W = 0 := by exact_mod_cast hc
    rw [hf0] at hfullpos
    exact lt_irrefl _ hfullpos
  have hu₁ne : u₁.Nonempty := by
    rcases Finset.eq_empty_or_nonempty u₁ with h | h
    · exfalso
      rw [h] at hmass1
      simp only [Finset.sum_empty, mul_zero] at hmass1
      exact hshadene (nonpos_iff_eq_zero.mp hmass1)
    · exact h
  -- step 2: the uniformisation
  have hball₁ : ∀ i ∈ u₁, ((T i).toTube).carrier ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
    fun i hi => hball i (hu₁s hi)
  have hcard₁ : (u₁.card : ℝ) ≤ (δ : ℝ) ^ (-((4 : ℕ) : ℝ)) := by
    refine le_trans ?_ hcard4
    exact_mod_cast Finset.card_le_card hu₁s
  obtain ⟨u', hu'u₁, hcardret, huniform⟩ :=
    huni hδ0 hδδ₀ u₁ (fun i => (T i).toTube) hball₁ hcard₁
  obtain ⟨𝒰⟩ := huniform
  have hu'ne : u'.Nonempty := by
    rcases Finset.eq_empty_or_nonempty u' with h | h
    · exfalso
      rw [h] at hcardret
      simp only [Finset.card_empty, Nat.cast_zero, mul_zero] at hcardret
      have : (0 : ℝ) < (u₁.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hu₁ne
      linarith
    · exact h
  have hu's : u' ⊆ s := hu'u₁.trans hu₁s
  -- the transfer constant
  set R : ℝ≥0∞ := (δ : ℝ≥0∞) ^ (-α) with hRdef
  set K : ℝ≥0∞ := 2 * (Tube.volume_le.C 3 : ℝ≥0∞) * R
      * ((lam : ℝ≥0∞) * (Tube.le_volume.c 3 : ℝ≥0∞))⁻¹ with hKdef
  refine ⟨u', hu's, Tube.uniformConst (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))), 𝒰,
    lam, K, ?_, hcard4, hu'ne, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- row 1
    rw [hEr]
    exact ShadedTube.uniformConst_le_ssfUniformConst 3
  · -- row 4
    calc maxDensity u' (fun i => (T i).toConvexSpaceBody)
        ≤ maxDensity s (fun i => (T i).toConvexSpaceBody) :=
          maxDensity_mono (fun i => (T i).toConvexSpaceBody) hu's
      _ ≤ (δ : ℝ≥0∞) ^ (-η) := hmax
      _ ≤ (δ : ℝ≥0∞) ^ (-ηin) :=
          ENNReal.rpow_le_rpow_of_exponent_ge hδE1 (by linarith)
  · -- row 5
    exact hlampos
  · -- row 6
    exact hdense1.subset hu'u₁
  · -- row 7
    have hstep : (δ : NNReal) ^ (ηin - aL) ≤ ShadedBody.fullness s W := by
      refine le_trans (NNReal.rpow_le_rpow_of_exponent_ge hδ0 hδ1 (by linarith)) hfull
    have : ((δ : NNReal) ^ (ηin - aL) / 2 : NNReal) ≤ lam := by
      rw [hlamdef]; exact div_le_div_of_nonneg_right hstep (by norm_num) |>.trans_eq rfl
    exact_mod_cast this
  · -- row 9: the mass ledger
    have hlamE0 : (lam : ℝ≥0∞) ≠ 0 := by simpa using hlampos.ne'
    have hcE0 : ((Tube.le_volume.c 3 : NNReal) : ℝ≥0∞) ≠ 0 := by
      simpa using (Tube.le_volume.c_pos 3).ne'
    have hprod0 : (lam : ℝ≥0∞) * (Tube.le_volume.c 3 : ℝ≥0∞) ≠ 0 :=
      mul_ne_zero hlamE0 hcE0
    have hprodT : (lam : ℝ≥0∞) * (Tube.le_volume.c 3 : ℝ≥0∞) ≠ ⊤ := by
      exact ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.coe_ne_top
    -- the card retention, in `ℝ≥0∞`
    have hcardE : (u₁.card : ℝ≥0∞) ≤ R * (u'.card : ℝ≥0∞) := by
      have hN : ((u₁.card : NNReal)) ≤ (δ ^ (-α) : NNReal) * (u'.card : NNReal) := by
        have h : ((u₁.card : NNReal) : ℝ) ≤ (((δ ^ (-α) : NNReal) * (u'.card : NNReal) : NNReal) : ℝ) := by
          push_cast [NNReal.coe_rpow]
          exact hcardret
        exact_mod_cast h
      have hRc : R = ((δ ^ (-α) : NNReal) : ℝ≥0∞) := by
        rw [hRdef, ENNReal.coe_rpow_of_ne_zero hδ0.ne']
      rw [hRc]
      exact_mod_cast hN
    have hconv := sum_shade_le_of_card_le_of_denseShading hδ1
      (hdense1.subset hu'u₁) hcardE
    have hchain : ((lam : ℝ≥0∞) * (Tube.le_volume.c 3 : ℝ≥0∞)) * (∑ i ∈ s, volume (W i).shade)
        ≤ 2 * ((Tube.volume_le.C 3 : ℝ≥0∞) * R * ∑ i ∈ u', volume (W i).shade) := by
      calc ((lam : ℝ≥0∞) * (Tube.le_volume.c 3 : ℝ≥0∞)) * (∑ i ∈ s, volume (W i).shade)
          ≤ ((lam : ℝ≥0∞) * (Tube.le_volume.c 3 : ℝ≥0∞))
              * (2 * ∑ i ∈ u₁, volume (W i).shade) := by gcongr
        _ = 2 * (((lam : ℝ≥0∞) * (Tube.le_volume.c 3 : ℝ≥0∞))
              * ∑ i ∈ u₁, volume (W i).shade) := by ring
        _ ≤ 2 * ((Tube.volume_le.C 3 : ℝ≥0∞) * R * ∑ i ∈ u', volume (W i).shade) := by
            gcongr
    have hfin : (∑ i ∈ s, volume (W i).shade) ≤ K * ∑ i ∈ u', volume (W i).shade := by
      calc (∑ i ∈ s, volume (W i).shade)
          = ((lam : ℝ≥0∞) * (Tube.le_volume.c 3 : ℝ≥0∞))⁻¹
              * (((lam : ℝ≥0∞) * (Tube.le_volume.c 3 : ℝ≥0∞))
                  * (∑ i ∈ s, volume (W i).shade)) := by
            rw [← mul_assoc, ENNReal.inv_mul_cancel hprod0 hprodT, one_mul]
        _ ≤ ((lam : ℝ≥0∞) * (Tube.le_volume.c 3 : ℝ≥0∞))⁻¹
              * (2 * ((Tube.volume_le.C 3 : ℝ≥0∞) * R * ∑ i ∈ u', volume (W i).shade)) := by
            gcongr
        _ = K * ∑ i ∈ u', volume (W i).shade := by rw [hKdef]; ring
    simpa [stateMass, hWdef] using hfin
  · -- row 10: the budget
    have hcE0 : ((Tube.le_volume.c 3 : NNReal) : ℝ≥0∞) ≠ 0 := by
      simpa using (Tube.le_volume.c_pos 3).ne'
    have hlamE0 : (lam : ℝ≥0∞) ≠ 0 := by simpa using hlampos.ne'
    -- split the inverse
    have hsplit : ((lam : ℝ≥0∞) * (Tube.le_volume.c 3 : ℝ≥0∞))⁻¹
        = (lam : ℝ≥0∞)⁻¹ * ((Tube.le_volume.c 3 : ℝ≥0∞))⁻¹ :=
      ENNReal.mul_inv (Or.inl hlamE0) (Or.inl ENNReal.coe_ne_top)
    -- the shading level is at least `δ^η / 2`
    have hlamlow : ((δ ^ η / 2 : NNReal) : ℝ≥0∞) ≤ (lam : ℝ≥0∞) := by
      have : ((δ : NNReal) ^ η / 2 : NNReal) ≤ lam := by
        rw [hlamdef]
        exact div_le_div_of_nonneg_right hfull (by norm_num)
      exact_mod_cast this
    have hinvlam : (lam : ℝ≥0∞)⁻¹ ≤ 2 * (δ : ℝ≥0∞) ^ (-η) := by
      refine le_trans (ENNReal.inv_le_inv.mpr hlamlow) (le_of_eq ?_)
      have hcoe : ((δ ^ η / 2 : NNReal) : ℝ≥0∞) = (δ : ℝ≥0∞) ^ η / 2 := by
        rw [ENNReal.coe_div (by norm_num), ENNReal.coe_rpow_of_ne_zero hδ0.ne']
        norm_num
      rw [hcoe, ENNReal.inv_div (Or.inl (by norm_num)) (Or.inl (by norm_num)),
        ENNReal.rpow_neg]
      rw [ENNReal.div_eq_inv_mul]
      ring
    -- the exponent bookkeeping
    have hδT : (δ : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
    have hexp : (δ : ℝ≥0∞) ^ (-α) * (δ : ℝ≥0∞) ^ (-η) * (δ : ℝ≥0∞) ^ (dm - aL)
        = (δ : ℝ≥0∞) ^ α := by
      rw [← ENNReal.rpow_add _ _ hδE0 hδT, ← ENNReal.rpow_add _ _ hδE0 hδT]
      congr 1
      rw [hαdef]
      unfold siteWitnessAlpha
      ring
    have hconst : ((siteWitnessConst : NNReal) : ℝ≥0∞)
        = 4 * (Tube.volume_le.C 3 : ℝ≥0∞) * ((Tube.le_volume.c 3 : ℝ≥0∞))⁻¹ := by
      unfold siteWitnessConst
      rw [ENNReal.coe_div (Tube.le_volume.c_pos 3).ne']
      push_cast
      rw [ENNReal.div_eq_inv_mul]
      ring
    calc K * (δ : ℝ≥0∞) ^ (dm - aL)
        = 2 * (Tube.volume_le.C 3 : ℝ≥0∞) * (δ : ℝ≥0∞) ^ (-α)
            * ((lam : ℝ≥0∞)⁻¹ * ((Tube.le_volume.c 3 : ℝ≥0∞))⁻¹)
            * (δ : ℝ≥0∞) ^ (dm - aL) := by rw [hKdef, hRdef, hsplit]
      _ ≤ 2 * (Tube.volume_le.C 3 : ℝ≥0∞) * (δ : ℝ≥0∞) ^ (-α)
            * ((2 * (δ : ℝ≥0∞) ^ (-η)) * ((Tube.le_volume.c 3 : ℝ≥0∞))⁻¹)
            * (δ : ℝ≥0∞) ^ (dm - aL) := by gcongr
      _ = (4 * (Tube.volume_le.C 3 : ℝ≥0∞) * ((Tube.le_volume.c 3 : ℝ≥0∞))⁻¹)
            * ((δ : ℝ≥0∞) ^ (-α) * (δ : ℝ≥0∞) ^ (-η) * (δ : ℝ≥0∞) ^ (dm - aL)) := by ring
      _ = ((siteWitnessConst : NNReal) : ℝ≥0∞) * (δ : ℝ≥0∞) ^ α := by rw [hconst, hexp]
      _ ≤ 1 := hbudδ

end Producer

end Kakeya.ML2Core
