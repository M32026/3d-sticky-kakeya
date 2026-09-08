/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma1.CaseFamily
public import Kakeya.DimensionThree.MainLemma1.CaseTwo
public import Kakeya.DimensionThree.MainLemma1.Setup
public import Kakeya.DimensionThree.MainLemma1.Envelope
public import Kakeya.DimensionThree.MainLemma1.Rescaling.Thresholds
public import Kakeya.MultiScaleFac
public import Kakeya.StickyKakeya.BallReduction

/-!
# Case (i) of GWZ Lemma 8.1, assembled

This file carries the two pieces that make **Case (i)** of the bootstrap of GWZ Lemma 8.1 a
usable input to `Kakeya.ml1Boot.exists_uniform_step`, and the assembly that consumes them.

* `Kakeya.ml1Boot.exists_bandedUniformFamily` is the input reduction.  It takes the bare family
  `Kakeya.FrostmanEstimate` hands out — pairwise essentially distinct shaded `δ`-tubes in `B₁`
  with a fullness lower bound and a Frostman upper bound — and returns a subfamily carrying a
  `Tube.UniformTubeSet` at the grid length `Tube.ssfGridLen δ`, a Frostman bound at the
  prescribed exponent, and, crucially, a **termwise** shade-density bound.  The termwise form is
  what survives the further, arbitrary, subfamily that `StickyKakeya.dividingScalesFrostman`
  takes: fullness is a ratio of two sums and does not pass to a subfamily, whereas a per-tube
  density bound does (`Kakeya.ml1Boot.le_fullness_of_termwise`).  This is why the shading is
  *not* refined here: `ShadedTube.exists_shadedUniformTubeSet_of_uniformTubeSet` shrinks the
  shades by an amount controlled only in aggregate and so destroys the band, and it is therefore
  applied only *after* the dichotomy has taken its subfamily.

* `Kakeya.ml1Boot.multiplicity_le_caseOne` is Case (i) proper.  It is
  `Kakeya.ml1Boot.multiplicity_le_of_frostmanAtEveryScale` with the family the sticky Kakeya
  input is applied to *decoupled* from the family whose multiplicity is bounded: sticky Kakeya
  is applied to a sub-shading `W` on a subfamily `s' ⊆ s`, and the resulting lower bound on
  `|⋃_{i ∈ s'} Y'(T_i)|` is transported to `|⋃_{i ∈ s} Y(T_i)|` by monotonicity of the measure
  before `Kakeya.multiplicity_le_div_of_le_volume_iUnionShade` is applied to the *original*
  family.  That decoupling is what removes the need to transport a multiplicity or a fullness
  bound back along the dichotomy's subfamily, which no declaration in the development supplies.
-/

@[expose] public section

open MeasureTheory Topology Filter ShadedBody ConvexSpaceBody

noncomputable section

namespace Kakeya

namespace MultiScaleFac

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

/-! ### The uniformity cap of sticky Kakeya, and why Case (i) cannot meet it -/

/-- **A re-uniformized hierarchy always sits above the sticky-Kakeya cap.**

`ShadedTube.ssfUniformConst n = max (max 2 (Tube.overlapConstBOTight n)) 4` is the *tight*
dimension-only constant of the shaded uniformization, and it was the cap that
`StickyKakeya.StickyFrostmanEstimate` used to impose on the bundles it accepts.  Every constant
the multiscale factorization produces passes through `Kakeya.MultiScaleFac.comparableCuOf`, which
squares its argument and multiplies by `2 · 100^{2n}`; so as soon as the argument already
dominates the tight bounded-overlap constant — which it does, every hierarchy in the development
being built from a tight grid net — the result strictly exceeds the cap.

This is what rules out the obvious repair — "strengthen
`StickyKakeya.dividingScalesFrostman` to return a constant below the cap" — and, more usefully,
it says where the repair that *does* work has to go: a route to the cap must **avoid
`Kakeya.MultiScaleFac.comparableCuOf` entirely** and land directly at
`Tube.overlapConstBOTight`.  That is exactly what
`Kakeya.ml1Boot.exists_restrict_uniformTubeSet_band_of_nice` does: it reads bounded overlap off
the *tight net* certificate `Tube.UniformTubeSet.Nice` instead of inheriting it from the bundle
it restricts, which is why the `hCuC : Cu ≤ C` of
`Kakeya.MultiScaleFac.exists_restrict_uniformTubeSet_band` is not fatal.

The cap on `StickyKakeya.StickyFrostmanEstimate` is therefore **retained**: the external input of
this development remains exactly GWZ Theorem 7.3(A). -/
theorem ssfUniformConst_lt_comparableCuOf {Cu : NNReal}
    (hCu : ((Tube.overlapConstBOTight (Module.finrank ℝ E) : ℕ) : NNReal) ≤ Cu) :
    ShadedTube.ssfUniformConst (Module.finrank ℝ E) < comparableCuOf (E := E) Cu := by
  set n := Module.finrank ℝ E with hn
  set B : NNReal := ((Tube.overlapConstBOTight n : ℕ) : NNReal) with hB
  have hB2 : (2 : NNReal) ≤ B := by
    rw [hB]
    have h : 2 ≤ Tube.overlapConstBOTight n := by
      unfold Tube.overlapConstBOTight
      have : 1 ≤ (3073 * n + 1) ^ (2 * n) := Nat.one_le_pow _ _ (by omega)
      omega
    exact_mod_cast h
  have hCu2 : (2 : NNReal) ≤ Cu := hB2.trans hCu
  have hCupos : (0 : NNReal) < Cu := lt_of_lt_of_le two_pos hCu2
  have hcap : ShadedTube.ssfUniformConst n ≤ max Cu 4 := by
    unfold ShadedTube.ssfUniformConst Tube.uniformConst
    exact max_le (max_le (le_max_of_le_left hCu2) (le_max_of_le_left hCu)) (le_max_right _ _)
  set R : NNReal := 2 * (100 : NNReal) ^ (2 * n) * Cu ^ 2 with hR
  have h4Cu : 4 * Cu ≤ R := by
    have e1 : (4 : NNReal) * Cu ≤ 2 * Cu ^ 2 := by
      rw [sq]
      calc (4 : NNReal) * Cu = 2 * (2 * Cu) := by ring
        _ ≤ 2 * (Cu * Cu) := by gcongr
    have e2 : (2 : NNReal) * Cu ^ 2 ≤ R := by
      rw [hR]
      have h100 : (1 : NNReal) ≤ (100 : NNReal) ^ (2 * n) := one_le_pow₀ (by norm_num)
      have h2 : (2 : NNReal) ≤ 2 * 100 ^ (2 * n) := by
        calc (2 : NNReal) = 2 * 1 := (mul_one 2).symm
          _ ≤ 2 * 100 ^ (2 * n) := by gcongr
      exact mul_le_mul_right' h2 _
    exact e1.trans e2
  have hlt : max Cu 4 < R := by
    refine max_lt (lt_of_lt_of_le ?_ h4Cu) (lt_of_lt_of_le ?_ h4Cu)
    · calc Cu = 1 * Cu := (one_mul Cu).symm
        _ < 4 * Cu := mul_lt_mul_of_pos_right (by norm_num) hCupos
    · calc (4 : NNReal) = 4 * 1 := (mul_one 4).symm
        _ < 4 * Cu := mul_lt_mul_of_pos_left (lt_of_lt_of_le one_lt_two hCu2) (by norm_num)
  exact lt_of_lt_of_le (lt_of_le_of_lt hcap hlt) (le_comparableCuOf (E := E) (Cu := Cu)).2



end

end MultiScaleFac

namespace ml1Boot

universe u

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **The input reduction of Case (i)** — a banded, tube-uniform subfamily.

From a family of pairwise essentially distinct shaded `δ`-tubes in `B₁` with fullness at least
`δ ^ η` and Frostman constant at most `δ ^ (-η)`, this produces a nonempty subfamily `s₂ ⊆ s`
carrying

* a **termwise** shade-density bound, delivered in the form that matters downstream: *every*
  nonempty `t ⊆ s₂` has fullness at least `δ ^ θ`.  A fullness bound on `s₂` itself would not
  survive the arbitrary subfamily that `StickyKakeya.dividingScalesFrostman` returns;
* the Frostman bound at the prescribed exponent `θ`, paid for by the cardinality share of the
  two pigeonholes (`ConvexSpaceBody.frostmanConstIn_subfamily_le`);
* a `Tube.UniformTubeSet` at the grid length `Tube.ssfGridLen δ` and the dimension-only constant
  `Tube.uniformConst (Module.finrank ℝ E)`.

The two pigeonholes are `ShadedBody.discardLowShading` at level `1/2` — which is what supplies
*both* the band and a cardinality share, and is available only before any uniformization — and
`Tube.exists_uniformTubeSet_subfamily_ssf` at budget `θ / 4`.  The shading is deliberately left
alone; see the module docstring. -/
theorem exists_bandedUniformFamily [Nontrivial E] (hdim : Module.finrank ℝ E = 3)
    {η θ : ℝ} (hη : 0 < η) (hθ : 0 < θ) (hηθ : η ≤ θ / 8) :
    ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
      ∀ {ι : Type u} (s : Finset ι) (V : ι → ShadedTube δ E),
        (∀ i ∈ s, (V i).carrier ⊆ Metric.closedBall 0 1) →
        (s : Set ι).Pairwise
          (fun i j => IsEssentiallyDistinct (V i).carrier (V j).carrier) →
        (δ : ENNReal) ^ η
          ≤ (ShadedBody.fullness s (fun i => (V i).toShadedBody) : ENNReal) →
        ConvexSpaceBody.frostmanConstIn s (fun i => (V i).toConvexSpaceBody)
            ConvexSpaceBody.closedUnitBall ≤ (δ : ENNReal) ^ (-η) →
        ∃ s₂ ⊆ s, s₂.Nonempty ∧
          (∀ t : Finset ι, t ⊆ s₂ → t.Nonempty →
            (δ : ENNReal) ^ θ
              ≤ (ShadedBody.fullness t (fun i => (V i).toShadedBody) : ENNReal)) ∧
          ConvexSpaceBody.frostmanConstIn s₂ (fun i => (V i).toConvexSpaceBody)
              ConvexSpaceBody.closedUnitBall ≤ (δ : ENNReal) ^ (-θ) ∧
          Nonempty (Tube.UniformTubeSet s₂ (fun i => (V i).toTube) (Tube.ssfGridLen δ)
            (Tube.uniformConst (Module.finrank ℝ E))) := by
  classical
  have hθ4 : (0 : ℝ) < θ / 4 := by positivity
  have hθ8 : (0 : ℝ) < θ / 8 := by positivity
  obtain ⟨δU, hδUpos, _hδUle1, hU⟩ :=
    Tube.exists_uniformTubeSet_subfamily_ssf (E := E) 7 (θ / 4) hθ4
  obtain ⟨δ2, hδ2pos, _hδ2le1, h2thr⟩ := exists_threshold_natCast_le_rpow 2 (θ / 8) hθ8
  filter_upwards [eventually_card_le_rpow_neg_seven (E := E) hdim,
      eventually_le_nhdsGT (c := δU) hδUpos,
      eventually_le_nhdsGT (c := δ2) hδ2pos,
      eventually_le_nhdsGT (c := (1 : NNReal)) one_pos,
      self_mem_nhdsWithin]
    with δ hcard7 hδU hδ2 hδ1 hδmem
  have hδ0 : (0 : NNReal) < δ := hδmem
  have hδR : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ0
  have hδe0 : (δ : ENNReal) ≠ 0 := (ENNReal.coe_pos.mpr hδ0).ne'
  have hδetop : (δ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hδE1 : ((δ : NNReal) : ENNReal) ≤ 1 := by exact_mod_cast hδ1
  have h2E : (2 : ENNReal) ≤ (δ : ENNReal) ^ (-(θ / 8)) := by
    rw [ennreal_coe_nnreal_rpow hδR (-(θ / 8)),
      show (2 : ENNReal) = ENNReal.ofReal (2 : ℝ) by simp]
    exact ENNReal.ofReal_le_ofReal (by exact_mod_cast h2thr hδ0 hδ2)
  intro ι s V hball hED hfull hfro
  set F : ENNReal := (ShadedBody.fullness s (fun i => (V i).toShadedBody) : ENNReal) with hF_def
  have hFtop : F ≠ ⊤ := by rw [hF_def]; exact ENNReal.coe_ne_top
  have hFpos : 0 < F :=
    lt_of_lt_of_le (ENNReal.rpow_pos (ENNReal.coe_pos.mpr hδ0) hδetop) hfull
  have hs : s.Nonempty := by
    rcases Finset.eq_empty_or_nonempty s with rfl | h
    · exact absurd hFpos (by simp [hF_def])
    · exact h
  obtain ⟨j₀, hj₀⟩ := hs
  set v : ENNReal := volume (V j₀).carrier with hv_def
  have hvpos : 0 < v := by
    have hc : 0 < (_root_.Tube.le_volume.c (Module.finrank ℝ E) : ENNReal) :=
      ENNReal.coe_pos.mpr (_root_.Tube.le_volume.c_pos (Module.finrank ℝ E))
    have hδp : 0 < (δ : ENNReal) ^ (Module.finrank ℝ E - 1) :=
      ENNReal.pow_pos (ENNReal.coe_pos.mpr hδ0) (Module.finrank ℝ E - 1)
    exact lt_of_lt_of_le (ENNReal.mul_pos hc.ne' hδp.ne')
      (by simpa [hv_def] using _root_.Tube.le_volume (V j₀).toTube)
  have hvtop : v ≠ ⊤ := (V j₀).isCompact.measure_ne_top
  have hcarr : ∀ i, volume (V i).carrier = v := fun i => by
    simpa [hv_def] using
      _root_.Tube.volume_carrier_eq_volume_carrier (V i).toTube (V j₀).toTube
  have hsumcar : ∀ X : Finset ι, ∑ i ∈ X, volume (V i).carrier = (X.card : ENNReal) * v :=
    fun X => by
      simpa [hv_def] using
        _root_.Tube.sum_volume_carrier_eq_card_mul (fun i => (V i).toTube) (V j₀).toTube X
  have hM : ∑ i ∈ s, volume (V i).shade = F * ((s.card : ENNReal) * v) := by
    rw [← hsumcar s, hF_def]
    exact ShadedBody.sum_volumeReal_shade_eq_fullness_mul s (fun i => (V i).toShadedBody)
  -- **Step 1.**  Discard the tubes of below-average shade density.
  set sa : Finset ι :=
    ShadedBody.discardLowShading s (fun i => (V i).toShadedBody) (2⁻¹ : NNReal) with hsa_def
  have hsa_sub : sa ⊆ s := ShadedBody.discardLowShading_subset _ _ _
  have hmass_a : (2 : ENNReal)⁻¹ * (∑ i ∈ s, volume (V i).shade)
      ≤ ∑ i ∈ sa, volume (V i).shade := by
    have h := ShadedBody.one_sub_mul_sum_volume_shade_le_sum_discardLowShading s
      (fun i => (V i).toShadedBody) (c := (2⁻¹ : NNReal)) (by norm_num)
    have hhalf : ((1 - (2⁻¹ : NNReal) : NNReal) : ENNReal) = (2 : ENNReal)⁻¹ := by
      norm_num
    rwa [hhalf] at h
  have hband_a : ∀ i ∈ sa, (2 : ENNReal)⁻¹ * F * v ≤ volume (V i).shade := by
    intro i hi
    have h := ShadedBody.le_volume_shade_of_mem_discardLowShading (c := (2⁻¹ : NNReal)) hi
    have hc : (((2⁻¹ : NNReal)) : ENNReal) = (2 : ENNReal)⁻¹ := by norm_num
    rwa [hc, ← hF_def, hcarr i] at h
  have hcount_a : (2 : ENNReal)⁻¹ * F * (s.card : ENNReal) ≤ (sa.card : ENNReal) := by
    have hupper : ∑ i ∈ sa, volume (V i).shade ≤ (sa.card : ENNReal) * v := by
      calc ∑ i ∈ sa, volume (V i).shade
          ≤ ∑ i ∈ sa, volume (V i).carrier :=
            Finset.sum_le_sum fun i _ => measure_mono (V i).shade_subset
        _ = (sa.card : ENNReal) * v := hsumcar sa
    have hchain : (2 : ENNReal)⁻¹ * F * (s.card : ENNReal) * v ≤ (sa.card : ENNReal) * v := by
      calc (2 : ENNReal)⁻¹ * F * (s.card : ENNReal) * v
          = (2 : ENNReal)⁻¹ * (F * ((s.card : ENNReal) * v)) := by ring
        _ = (2 : ENNReal)⁻¹ * (∑ i ∈ s, volume (V i).shade) := by rw [hM]
        _ ≤ ∑ i ∈ sa, volume (V i).shade := hmass_a
        _ ≤ (sa.card : ENNReal) * v := hupper
    exact (ENNReal.mul_le_mul_iff_right hvpos.ne' hvtop).mp
      (by simpa [mul_comm] using hchain)
  have hsane : sa.Nonempty := by
    rw [← Finset.card_pos, ← Nat.cast_pos (α := ENNReal)]
    refine lt_of_lt_of_le ?_ hcount_a
    have hcs : (0 : ENNReal) < (s.card : ENNReal) := by
      exact_mod_cast Finset.card_pos.mpr ⟨j₀, hj₀⟩
    exact ENNReal.mul_pos
      (ENNReal.mul_pos (show ((2 : ENNReal))⁻¹ ≠ 0 by simp) hFpos.ne').ne' hcs.ne'
  -- **Step 2.**  Uniformize the tubes on the truncated index set.
  have hcards : (s.card : ℝ) ≤ (δ : ℝ) ^ (-(7 : ℝ)) :=
    hcard7 δ le_rfl s (fun i => (V i).toTube) (by simpa using hball) (by simpa using hED)
  have hcards_a : (sa.card : ℝ) ≤ (δ : ℝ) ^ (-(7 : ℝ)) :=
    le_trans (by exact_mod_cast Finset.card_le_card hsa_sub) hcards
  obtain ⟨s₂, h₂a, hcardret, hunif⟩ :=
    hU hδ0 hδU sa (fun i => (V i).toTube)
      (fun i hi => by simpa using hball i (hsa_sub hi)) hcards_a
  have hs₂s : s₂ ⊆ s := h₂a.trans hsa_sub
  have hs₂ne : s₂.Nonempty := by
    rw [← Finset.card_pos]
    rcases Nat.eq_zero_or_pos s₂.card with hz | hpos
    · exfalso
      rw [hz] at hcardret
      norm_num at hcardret
      exact (Finset.not_nonempty_iff_eq_empty.mpr hcardret) hsane
    · exact hpos
  refine ⟨s₂, hs₂s, hs₂ne, ?_, ?_, hunif⟩
  -- **The fullness clause**, termwise on `sa` and hence on every nonempty subfamily.
  · have hstep : (δ : ENNReal) ^ θ ≤ (2 : ENNReal)⁻¹ * F := by
      have h2 : (2 : ENNReal) * (δ : ENNReal) ^ θ ≤ F := by
        calc (2 : ENNReal) * (δ : ENNReal) ^ θ
            ≤ (δ : ENNReal) ^ (-(θ / 8)) * (δ : ENNReal) ^ θ := mul_le_mul_right' h2E _
          _ = (δ : ENNReal) ^ (-(θ / 8) + θ) := by
              rw [← ENNReal.rpow_add _ _ hδe0 hδetop]
          _ ≤ (δ : ENNReal) ^ η :=
              ENNReal.rpow_le_rpow_of_exponent_ge hδE1 (by linarith)
          _ ≤ F := hfull
      calc (δ : ENNReal) ^ θ = (2 : ENNReal)⁻¹ * (2 * (δ : ENNReal) ^ θ) := by
            rw [← mul_assoc, ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_mul]
        _ ≤ (2 : ENNReal)⁻¹ * F := mul_le_mul_left' h2 _
    have hterm : ∀ i ∈ sa,
        (δ : ENNReal) ^ θ * volume ((fun i => (V i).toShadedBody) i).carrier
          ≤ volume ((fun i => (V i).toShadedBody) i).shade := by
      intro i hi
      refine le_trans ?_ (hband_a i hi)
      have hcv : volume ((fun i => (V i).toShadedBody) i).carrier = v := hcarr i
      rw [hcv]
      exact mul_le_mul_right' hstep v
    intro t ht htne
    exact ml1Boot.le_fullness_of_termwise (fun i => (V i).toShadedBody)
      (fun i _ => by rw [hcarr i]; exact hvpos)
      (fun i _ => by rw [hcarr i]; exact hvtop) hterm (ht.trans h₂a) htne
  -- **The Frostman clause.**
  · have hcardE : (sa.card : ENNReal)
        ≤ (δ : ENNReal) ^ (-(θ / 4)) * (s₂.card : ENNReal) := by
      rw [ennreal_coe_nnreal_rpow hδR (-(θ / 4)), ← ENNReal.ofReal_natCast sa.card,
        ← ENNReal.ofReal_natCast s₂.card, ← ENNReal.ofReal_mul (Real.rpow_nonneg hδR.le _)]
      exact ENNReal.ofReal_le_ofReal hcardret
    have hκcard : (δ : ENNReal) ^ (θ / 2) * (s.card : ENNReal) ≤ (s₂.card : ENNReal) := by
      have hkey : (δ : ENNReal) ^ (θ / 2)
          ≤ (δ : ENNReal) ^ (θ / 4) * ((2 : ENNReal)⁻¹ * (δ : ENNReal) ^ η) := by
        have h2 : (2 : ENNReal) * (δ : ENNReal) ^ (θ / 2)
            ≤ (δ : ENNReal) ^ (θ / 4) * (δ : ENNReal) ^ η := by
          calc (2 : ENNReal) * (δ : ENNReal) ^ (θ / 2)
              ≤ (δ : ENNReal) ^ (-(θ / 8)) * (δ : ENNReal) ^ (θ / 2) := mul_le_mul_right' h2E _
            _ = (δ : ENNReal) ^ (-(θ / 8) + θ / 2) := by
                rw [← ENNReal.rpow_add _ _ hδe0 hδetop]
            _ ≤ (δ : ENNReal) ^ (θ / 4 + η) :=
                ENNReal.rpow_le_rpow_of_exponent_ge hδE1 (by linarith)
            _ = (δ : ENNReal) ^ (θ / 4) * (δ : ENNReal) ^ η := by
                rw [← ENNReal.rpow_add _ _ hδe0 hδetop]
        calc (δ : ENNReal) ^ (θ / 2) = (2 : ENNReal)⁻¹ * (2 * (δ : ENNReal) ^ (θ / 2)) := by
              rw [← mul_assoc, ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_mul]
          _ ≤ (2 : ENNReal)⁻¹ * ((δ : ENNReal) ^ (θ / 4) * (δ : ENNReal) ^ η) :=
              mul_le_mul_left' h2 _
          _ = (δ : ENNReal) ^ (θ / 4) * ((2 : ENNReal)⁻¹ * (δ : ENNReal) ^ η) := by ring
      calc (δ : ENNReal) ^ (θ / 2) * (s.card : ENNReal)
          ≤ ((δ : ENNReal) ^ (θ / 4) * ((2 : ENNReal)⁻¹ * (δ : ENNReal) ^ η))
              * (s.card : ENNReal) := mul_le_mul_right' hkey _
        _ = (δ : ENNReal) ^ (θ / 4) * ((2 : ENNReal)⁻¹ * (δ : ENNReal) ^ η
              * (s.card : ENNReal)) := by ring
        _ ≤ (δ : ENNReal) ^ (θ / 4) * ((2 : ENNReal)⁻¹ * F * (s.card : ENNReal)) := by
              gcongr
        _ ≤ (δ : ENNReal) ^ (θ / 4) * (sa.card : ENNReal) := by
              exact mul_le_mul_left' hcount_a _
        _ ≤ (δ : ENNReal) ^ (θ / 4) * ((δ : ENNReal) ^ (-(θ / 4)) * (s₂.card : ENNReal)) := by
              exact mul_le_mul_left' hcardE _
        _ = (s₂.card : ENNReal) := by
              rw [← mul_assoc, ← ENNReal.rpow_add _ _ hδe0 hδetop]
              simp
    have hκpos : ((δ : ENNReal) ^ (θ / 2)) ≠ 0 :=
      (ENNReal.rpow_pos (ENNReal.coe_pos.mpr hδ0) hδetop).ne'
    have hWK : ∀ i ∈ s, (V i).toConvexSpaceBody
        ≤ (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E) := by
      intro i hi
      change (V i).carrier ⊆ (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E).carrier
      rw [ConvexSpaceBody.closedUnitBall_carrier]
      exact hball i hi
    have hf := ConvexSpaceBody.frostmanConstIn_subfamily_le
      (s := s) (s' := s₂) (W := fun i => (V i).toConvexSpaceBody)
      (K := (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E))
      (κ := (δ : ENNReal) ^ (θ / 2)) (v := v) ⟨j₀, hj₀⟩ (fun i _ => hcarr i) hWK hs₂s
      hκpos hκcard
    rw [← ENNReal.rpow_neg] at hf
    refine hf.trans ?_
    calc (δ : ENNReal) ^ (-(θ / 2)) * ConvexSpaceBody.frostmanConstIn s
            (fun i => (V i).toConvexSpaceBody) ConvexSpaceBody.closedUnitBall
        ≤ (δ : ENNReal) ^ (-(θ / 2)) * (δ : ENNReal) ^ (-η) := mul_le_mul_left' hfro _
      _ = (δ : ENNReal) ^ (-(θ / 2) + -η) := by rw [← ENNReal.rpow_add _ _ hδe0 hδetop]
      _ ≤ (δ : ENNReal) ^ (-θ) := ENNReal.rpow_le_rpow_of_exponent_ge hδE1 (by linarith)

/-- The existing banding construction with its construction-owned cardinal
share exposed.  The inputs and the remaining outputs are those of
`exists_bandedUniformFamily`; forgetting the cardinal-share conjunct gives
that producer's original conclusion. -/
theorem exists_bandedUniformFamily_retaining_card_w59
    [Nontrivial E] (hdim : Module.finrank Real E = 3)
    {etaIn etaRet : Real} (hetaIn : 0 < etaIn) (hetaRet : 0 < etaRet)
    (hetaInRet : etaIn <= etaRet / 8) :
    ∀ᶠ (delta : NNReal) in nhdsWithin 0 (Set.Ioi 0),
      forall {iota : Type u} (s : Finset iota)
        (V : iota -> ShadedTube delta E),
        (forall i, i ∈ s ->
          (V i).carrier <= Metric.closedBall 0 1) ->
        (s : Set iota).Pairwise
          (fun i j => IsEssentiallyDistinct (V i).carrier (V j).carrier) ->
        (delta : ENNReal) ^ etaIn <=
          (ShadedBody.fullness s
            (fun i => (V i).toShadedBody) : ENNReal) ->
        ConvexSpaceBody.frostmanConstIn s
            (fun i => (V i).toConvexSpaceBody)
            ConvexSpaceBody.closedUnitBall <=
          (delta : ENNReal) ^ (-etaIn) ->
        exists sTwo, sTwo <= s /\ sTwo.Nonempty /\
          (delta : ENNReal) ^ (etaRet / 2) * (s.card : ENNReal) <=
            (sTwo.card : ENNReal) /\
          (forall t : Finset iota, t <= sTwo -> t.Nonempty ->
            (delta : ENNReal) ^ etaRet <=
              (ShadedBody.fullness t
                (fun i => (V i).toShadedBody) : ENNReal)) /\
          ConvexSpaceBody.frostmanConstIn sTwo
              (fun i => (V i).toConvexSpaceBody)
              ConvexSpaceBody.closedUnitBall <=
            (delta : ENNReal) ^ (-etaRet) /\
          Nonempty (Tube.UniformTubeSet sTwo
            (fun i => (V i).toTube) (Tube.ssfGridLen delta)
            (Tube.uniformConst (Module.finrank Real E))) := by
  classical
  have hetaRet4 : (0 : Real) < etaRet / 4 := by positivity
  have hetaRet8 : (0 : Real) < etaRet / 8 := by positivity
  obtain ⟨deltaU, hdeltaUpos, _hdeltaUle1, hU⟩ :=
    Tube.exists_uniformTubeSet_subfamily_ssf (E := E) 7 (etaRet / 4) hetaRet4
  obtain ⟨delta2, hdelta2pos, _hdelta2le1, h2thr⟩ :=
    exists_threshold_natCast_le_rpow 2 (etaRet / 8) hetaRet8
  filter_upwards [eventually_card_le_rpow_neg_seven (E := E) hdim,
      eventually_le_nhdsGT (c := deltaU) hdeltaUpos,
      eventually_le_nhdsGT (c := delta2) hdelta2pos,
      eventually_le_nhdsGT (c := (1 : NNReal)) one_pos,
      self_mem_nhdsWithin]
    with delta hcard7 hdeltaU hdelta2 hdelta1 hdeltamem
  have hdelta0 : (0 : NNReal) < delta := hdeltamem
  have hdeltaR : (0 : Real) < (delta : Real) := by exact_mod_cast hdelta0
  have hdeltae0 : (delta : ENNReal) ≠ 0 := (ENNReal.coe_pos.mpr hdelta0).ne'
  have hdeltatop : (delta : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hdeltaE1 : ((delta : NNReal) : ENNReal) ≤ 1 := by exact_mod_cast hdelta1
  have h2E : (2 : ENNReal) ≤ (delta : ENNReal) ^ (-(etaRet / 8)) := by
    rw [ennreal_coe_nnreal_rpow hdeltaR (-(etaRet / 8)),
      show (2 : ENNReal) = ENNReal.ofReal (2 : Real) by simp]
    exact ENNReal.ofReal_le_ofReal (by exact_mod_cast h2thr hdelta0 hdelta2)
  intro iota s V hball hED hfull hfro
  set F : ENNReal :=
    (ShadedBody.fullness s (fun i => (V i).toShadedBody) : ENNReal) with hF_def
  have hFtop : F ≠ ⊤ := by rw [hF_def]; exact ENNReal.coe_ne_top
  have hFpos : 0 < F :=
    lt_of_lt_of_le (ENNReal.rpow_pos (ENNReal.coe_pos.mpr hdelta0) hdeltatop) hfull
  have hs : s.Nonempty := by
    rcases Finset.eq_empty_or_nonempty s with rfl | h
    · exact absurd hFpos (by simp [hF_def])
    · exact h
  obtain ⟨j0, hj0⟩ := hs
  set vol : ENNReal := volume (V j0).carrier with hvol_def
  have hvolpos : 0 < vol := by
    have hc : 0 < (_root_.Tube.le_volume.c (Module.finrank Real E) : ENNReal) :=
      ENNReal.coe_pos.mpr (_root_.Tube.le_volume.c_pos (Module.finrank Real E))
    have hdeltap : 0 < (delta : ENNReal) ^ (Module.finrank Real E - 1) :=
      ENNReal.pow_pos (ENNReal.coe_pos.mpr hdelta0) (Module.finrank Real E - 1)
    exact lt_of_lt_of_le (ENNReal.mul_pos hc.ne' hdeltap.ne')
      (by simpa [hvol_def] using _root_.Tube.le_volume (V j0).toTube)
  have hvoltop : vol ≠ ⊤ := (V j0).isCompact.measure_ne_top
  have hcarr : ∀ i, volume (V i).carrier = vol := fun i => by
    simpa [hvol_def] using
      _root_.Tube.volume_carrier_eq_volume_carrier (V i).toTube (V j0).toTube
  have hsumcar : ∀ X : Finset iota,
      ∑ i ∈ X, volume (V i).carrier = (X.card : ENNReal) * vol :=
    fun X => by
      simpa [hvol_def] using
        _root_.Tube.sum_volume_carrier_eq_card_mul
          (fun i => (V i).toTube) (V j0).toTube X
  have hM : ∑ i ∈ s, volume (V i).shade = F * ((s.card : ENNReal) * vol) := by
    rw [← hsumcar s, hF_def]
    exact ShadedBody.sum_volumeReal_shade_eq_fullness_mul
      s (fun i => (V i).toShadedBody)
  set sa : Finset iota :=
    ShadedBody.discardLowShading s
      (fun i => (V i).toShadedBody) (2⁻¹ : NNReal) with hsa_def
  have hsa_sub : sa ⊆ s := ShadedBody.discardLowShading_subset _ _ _
  have hmass_a : (2 : ENNReal)⁻¹ * (∑ i ∈ s, volume (V i).shade)
      ≤ ∑ i ∈ sa, volume (V i).shade := by
    have h := ShadedBody.one_sub_mul_sum_volume_shade_le_sum_discardLowShading s
      (fun i => (V i).toShadedBody) (c := (2⁻¹ : NNReal)) (by norm_num)
    have hhalf : ((1 - (2⁻¹ : NNReal) : NNReal) : ENNReal) =
        (2 : ENNReal)⁻¹ := by
      norm_num
    rwa [hhalf] at h
  have hband_a : ∀ i ∈ sa,
      (2 : ENNReal)⁻¹ * F * vol ≤ volume (V i).shade := by
    intro i hi
    have h := ShadedBody.le_volume_shade_of_mem_discardLowShading
      (c := (2⁻¹ : NNReal)) hi
    have hc : (((2⁻¹ : NNReal)) : ENNReal) = (2 : ENNReal)⁻¹ := by norm_num
    rwa [hc, ← hF_def, hcarr i] at h
  have hcount_a : (2 : ENNReal)⁻¹ * F * (s.card : ENNReal) ≤
      (sa.card : ENNReal) := by
    have hupper : ∑ i ∈ sa, volume (V i).shade ≤ (sa.card : ENNReal) * vol := by
      calc ∑ i ∈ sa, volume (V i).shade
          ≤ ∑ i ∈ sa, volume (V i).carrier :=
            Finset.sum_le_sum fun i _ => measure_mono (V i).shade_subset
        _ = (sa.card : ENNReal) * vol := hsumcar sa
    have hchain : (2 : ENNReal)⁻¹ * F * (s.card : ENNReal) * vol ≤
        (sa.card : ENNReal) * vol := by
      calc (2 : ENNReal)⁻¹ * F * (s.card : ENNReal) * vol
          = (2 : ENNReal)⁻¹ * (F * ((s.card : ENNReal) * vol)) := by ring
        _ = (2 : ENNReal)⁻¹ * (∑ i ∈ s, volume (V i).shade) := by rw [hM]
        _ ≤ ∑ i ∈ sa, volume (V i).shade := hmass_a
        _ ≤ (sa.card : ENNReal) * vol := hupper
    exact (ENNReal.mul_le_mul_iff_right hvolpos.ne' hvoltop).mp
      (by simpa [mul_comm] using hchain)
  have hsane : sa.Nonempty := by
    rw [← Finset.card_pos, ← Nat.cast_pos (α := ENNReal)]
    refine lt_of_lt_of_le ?_ hcount_a
    have hcs : (0 : ENNReal) < (s.card : ENNReal) := by
      exact_mod_cast Finset.card_pos.mpr ⟨j0, hj0⟩
    exact ENNReal.mul_pos
      (ENNReal.mul_pos (show ((2 : ENNReal))⁻¹ ≠ 0 by simp) hFpos.ne').ne' hcs.ne'
  have hcards : (s.card : Real) ≤ (delta : Real) ^ (-(7 : Real)) :=
    hcard7 delta le_rfl s (fun i => (V i).toTube)
      (by simpa using hball) (by simpa using hED)
  have hcards_a : (sa.card : Real) ≤ (delta : Real) ^ (-(7 : Real)) :=
    le_trans (by exact_mod_cast Finset.card_le_card hsa_sub) hcards
  obtain ⟨sTwo, hTwoa, hcardret, hunif⟩ :=
    hU hdelta0 hdeltaU sa (fun i => (V i).toTube)
      (fun i hi => by simpa using hball i (hsa_sub hi)) hcards_a
  have hsTwos : sTwo ⊆ s := hTwoa.trans hsa_sub
  have hsTwone : sTwo.Nonempty := by
    rw [← Finset.card_pos]
    rcases Nat.eq_zero_or_pos sTwo.card with hz | hpos
    · exfalso
      rw [hz] at hcardret
      norm_num at hcardret
      exact (Finset.not_nonempty_iff_eq_empty.mpr hcardret) hsane
    · exact hpos
  have hcardE : (sa.card : ENNReal)
      ≤ (delta : ENNReal) ^ (-(etaRet / 4)) * (sTwo.card : ENNReal) := by
    rw [ennreal_coe_nnreal_rpow hdeltaR (-(etaRet / 4)),
      ← ENNReal.ofReal_natCast sa.card, ← ENNReal.ofReal_natCast sTwo.card,
      ← ENNReal.ofReal_mul (Real.rpow_nonneg hdeltaR.le _)]
    exact ENNReal.ofReal_le_ofReal hcardret
  have hkappaCard : (delta : ENNReal) ^ (etaRet / 2) * (s.card : ENNReal) ≤
      (sTwo.card : ENNReal) := by
    have hkey : (delta : ENNReal) ^ (etaRet / 2)
        ≤ (delta : ENNReal) ^ (etaRet / 4) *
          ((2 : ENNReal)⁻¹ * (delta : ENNReal) ^ etaIn) := by
      have h2 : (2 : ENNReal) * (delta : ENNReal) ^ (etaRet / 2)
          ≤ (delta : ENNReal) ^ (etaRet / 4) * (delta : ENNReal) ^ etaIn := by
        calc (2 : ENNReal) * (delta : ENNReal) ^ (etaRet / 2)
            ≤ (delta : ENNReal) ^ (-(etaRet / 8)) *
                (delta : ENNReal) ^ (etaRet / 2) := mul_le_mul_right' h2E _
          _ = (delta : ENNReal) ^ (-(etaRet / 8) + etaRet / 2) := by
              rw [← ENNReal.rpow_add _ _ hdeltae0 hdeltatop]
          _ ≤ (delta : ENNReal) ^ (etaRet / 4 + etaIn) :=
              ENNReal.rpow_le_rpow_of_exponent_ge hdeltaE1 (by linarith)
          _ = (delta : ENNReal) ^ (etaRet / 4) *
                (delta : ENNReal) ^ etaIn := by
              rw [← ENNReal.rpow_add _ _ hdeltae0 hdeltatop]
      calc (delta : ENNReal) ^ (etaRet / 2)
          = (2 : ENNReal)⁻¹ * (2 * (delta : ENNReal) ^ (etaRet / 2)) := by
              rw [← mul_assoc,
                ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_mul]
        _ ≤ (2 : ENNReal)⁻¹ *
              ((delta : ENNReal) ^ (etaRet / 4) * (delta : ENNReal) ^ etaIn) :=
              mul_le_mul_left' h2 _
        _ = (delta : ENNReal) ^ (etaRet / 4) *
              ((2 : ENNReal)⁻¹ * (delta : ENNReal) ^ etaIn) := by ring
    calc (delta : ENNReal) ^ (etaRet / 2) * (s.card : ENNReal)
        ≤ ((delta : ENNReal) ^ (etaRet / 4) *
            ((2 : ENNReal)⁻¹ * (delta : ENNReal) ^ etaIn)) *
            (s.card : ENNReal) := mul_le_mul_right' hkey _
      _ = (delta : ENNReal) ^ (etaRet / 4) *
            ((2 : ENNReal)⁻¹ * (delta : ENNReal) ^ etaIn *
              (s.card : ENNReal)) := by ring
      _ ≤ (delta : ENNReal) ^ (etaRet / 4) *
            ((2 : ENNReal)⁻¹ * F * (s.card : ENNReal)) := by
            gcongr
      _ ≤ (delta : ENNReal) ^ (etaRet / 4) * (sa.card : ENNReal) := by
            exact mul_le_mul_left' hcount_a _
      _ ≤ (delta : ENNReal) ^ (etaRet / 4) *
            ((delta : ENNReal) ^ (-(etaRet / 4)) * (sTwo.card : ENNReal)) := by
            exact mul_le_mul_left' hcardE _
      _ = (sTwo.card : ENNReal) := by
            rw [← mul_assoc, ← ENNReal.rpow_add _ _ hdeltae0 hdeltatop]
            simp
  refine ⟨sTwo, hsTwos, hsTwone, hkappaCard, ?_, ?_, hunif⟩
  · have hstep : (delta : ENNReal) ^ etaRet ≤ (2 : ENNReal)⁻¹ * F := by
      have h2 : (2 : ENNReal) * (delta : ENNReal) ^ etaRet ≤ F := by
        calc (2 : ENNReal) * (delta : ENNReal) ^ etaRet
            ≤ (delta : ENNReal) ^ (-(etaRet / 8)) *
                (delta : ENNReal) ^ etaRet := mul_le_mul_right' h2E _
          _ = (delta : ENNReal) ^ (-(etaRet / 8) + etaRet) := by
              rw [← ENNReal.rpow_add _ _ hdeltae0 hdeltatop]
          _ ≤ (delta : ENNReal) ^ etaIn :=
              ENNReal.rpow_le_rpow_of_exponent_ge hdeltaE1 (by linarith)
          _ ≤ F := hfull
      calc (delta : ENNReal) ^ etaRet
          = (2 : ENNReal)⁻¹ * (2 * (delta : ENNReal) ^ etaRet) := by
              rw [← mul_assoc,
                ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_mul]
        _ ≤ (2 : ENNReal)⁻¹ * F := mul_le_mul_left' h2 _
    have hterm : ∀ i ∈ sa,
        (delta : ENNReal) ^ etaRet *
            volume ((fun i => (V i).toShadedBody) i).carrier
          ≤ volume ((fun i => (V i).toShadedBody) i).shade := by
      intro i hi
      refine le_trans ?_ (hband_a i hi)
      have hcv : volume ((fun i => (V i).toShadedBody) i).carrier = vol := hcarr i
      rw [hcv]
      exact mul_le_mul_right' hstep vol
    intro t ht htne
    exact ml1Boot.le_fullness_of_termwise (fun i => (V i).toShadedBody)
      (fun i _ => by rw [hcarr i]; exact hvolpos)
      (fun i _ => by rw [hcarr i]; exact hvoltop) hterm (ht.trans hTwoa) htne
  · have hkappaPos : ((delta : ENNReal) ^ (etaRet / 2)) ≠ 0 :=
      (ENNReal.rpow_pos (ENNReal.coe_pos.mpr hdelta0) hdeltatop).ne'
    have hWK : ∀ i ∈ s, (V i).toConvexSpaceBody
        ≤ (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E) := by
      intro i hi
      change (V i).carrier ⊆
        (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E).carrier
      rw [ConvexSpaceBody.closedUnitBall_carrier]
      exact hball i hi
    have hf := ConvexSpaceBody.frostmanConstIn_subfamily_le
      (s := s) (s' := sTwo) (W := fun i => (V i).toConvexSpaceBody)
      (K := (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E))
      (κ := (delta : ENNReal) ^ (etaRet / 2)) (v := vol) ⟨j0, hj0⟩
      (fun i _ => hcarr i) hWK hsTwos hkappaPos hkappaCard
    rw [← ENNReal.rpow_neg] at hf
    refine hf.trans ?_
    calc (delta : ENNReal) ^ (-(etaRet / 2)) *
            ConvexSpaceBody.frostmanConstIn s
              (fun i => (V i).toConvexSpaceBody)
              ConvexSpaceBody.closedUnitBall
        ≤ (delta : ENNReal) ^ (-(etaRet / 2)) *
            (delta : ENNReal) ^ (-etaIn) := mul_le_mul_left' hfro _
      _ = (delta : ENNReal) ^ (-(etaRet / 2) + -etaIn) := by
            rw [← ENNReal.rpow_add _ _ hdeltae0 hdeltatop]
      _ ≤ (delta : ENNReal) ^ (-etaRet) :=
            ENNReal.rpow_le_rpow_of_exponent_ge hdeltaE1 (by linarith)

/-- **Case (i) of GWZ Lemma 8.1**, with the sticky family decoupled from the target family.

Sticky Kakeya is applied to a sub-shading `W` on a subfamily `s' ⊆ s`; since `⋃_{i ∈ s'} Y'(T_i)`
sits inside `⋃_{i ∈ s} Y(T_i)`, the volume lower bound it produces bounds the multiplicity of
the *original* family through `Kakeya.multiplicity_le_div_of_le_volume_iUnionShade`.  Nothing has
to be transported back along `s' ⊆ s`.

This is what makes Case (i) pluggable downstream of `StickyKakeya.dividingScalesFrostman`, whose
Alternative (i) is stated on a subfamily it chooses itself and which retains only a *cardinality*
share of the input: neither a fullness nor a multiplicity bound can be carried back across it.

Apart from the decoupling the proof is that of
`Kakeya.ml1Boot.multiplicity_le_of_frostmanAtEveryScale`: `η⋆` is an output, produced by sticky
Kakeya at accuracy `γ₀ / 2`, and the step `c` and the accuracy `α` are quantified after it. -/
theorem multiplicity_le_caseOne
    (hSFE : StickyKakeya.StickyFrostmanEstimate.{_, u} (E := E))
    (hdim : Module.finrank ℝ E = 3)
    {β γ₀ : ℝ} (hβ0 : 0 ≤ β) (hγ₀ : γ₀ ∈ Set.Ioc β 1) :
    ∃ ηStar > (0 : ℝ), ∀ (c α : ℝ), 0 < c → c ≤ γ₀ / 2 → 0 < α →
    ∀ᶠ (δ : NNReal) in 𝓝[>] 0, ∀ γ ∈ Set.Icc γ₀ 1,
      ∀ {ι : Type u} (s : Finset ι) (V : ι → ShadedTube δ E),
        (∀ i ∈ s, (V i).carrier ⊆ Metric.closedBall 0 1) →
        (s : Set ι).Pairwise
          (fun i j => IsEssentiallyDistinct (V i).carrier (V j).carrier) →
        ∀ (s' : Finset ι), s' ⊆ s →
        ∀ (W : ι → ShadedTube δ E),
        (∀ i, (W i).toTube = (V i).toTube) →
        (∀ i, (W i).shade ⊆ (V i).shade) →
        ∀ {C : NNReal}, C ≤ ShadedTube.ssfUniformConst (Module.finrank ℝ E) →
        ∀ (𝒲 : ShadedTube.ShadedUniformTubeSet s' W (Tube.ssfGridLen δ) C),
        (δ : ENNReal) ^ ηStar
            ≤ ShadedBody.fullness s' (fun i => (W i).toShadedBody) →
        𝒲.tubeUniform.IsFrostmanAtEveryScale ((δ : ENNReal) ^ (-ηStar)) →
        multiplicity s (fun i => (V i).toShadedBody) ≤
          (δ : ENNReal) ^ (-α) *
            (δ : ENNReal) ^ (-2 * (γ - c)) *
            ((s.card : ENNReal) * (δ : ENNReal) ^ (2 : ℕ)) ^ (1 - (γ - c) / 2) := by
  haveI : Nontrivial E :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [hdim]; norm_num)
  have hγ₀pos : 0 < γ₀ := lt_of_le_of_lt hβ0 hγ₀.1
  have hγ₀half : 0 < γ₀ / 2 := half_pos hγ₀pos
  obtain ⟨ηStar, hηStar_pos, hηStar_ev⟩ :=
    StickyKakeya.volume_iUnionShade_ge_of_isFrostmanAtEveryScale (E := E) hSFE
      (ε := γ₀ / 2) hγ₀half
  refine ⟨ηStar, hηStar_pos, ?_⟩
  intro c α hc0 hc hα
  let Cvol : ENNReal := (Tube.volume_le.C (Module.finrank ℝ E) : ENNReal)
  let Ccard : ENNReal := (cardBound.C : ENNReal)
  let A : ENNReal := Cvol * Ccard
  have hA1 : (1 : ENNReal) ≤ A := by
    dsimp [A, Cvol, Ccard]
    rw [← one_mul (1 : ENNReal)]
    exact mul_le_mul' (ENNReal.one_le_coe_iff.mpr (one_le_pow₀ one_le_two))
      (ENNReal.one_le_coe_iff.mpr cardBound.one_le_C)
  have hAtop : A ≠ ⊤ := by
    dsimp [A, Cvol, Ccard]
    exact ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.coe_ne_top
  have hconst_ev : ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
      0 < δ ∧ δ ≤ 1 ∧ A ≤ (δ : ENNReal) ^ (-α) := by
    have hApos : (0 : ENNReal) < A := zero_lt_one.trans_le hA1
    have htop : A ^ (-1 / α) ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg' hApos hAtop
    have hδ₁ : (0 : NNReal) < min 1 (A ^ (-1 / α)).toNNReal :=
      lt_min zero_lt_one (by
        rw [← ENNReal.coe_pos, ENNReal.coe_toNNReal htop]
        exact ENNReal.rpow_pos hApos hAtop)
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds hδ₁)]
      with δ (hδ_pos : 0 < δ) hδ_lt
    refine ⟨hδ_pos, hδ_lt.le.trans (min_le_left _ _),
      const_le_rpow_neg hA1 hAtop hα hδ_pos ?_⟩
    calc
      (δ : ENNReal) ≤ ((A ^ (-1 / α)).toNNReal : ENNReal) :=
        ENNReal.coe_le_coe.mpr (hδ_lt.le.trans (min_le_right _ _))
      _ = A ^ (-1 / α) := ENNReal.coe_toNNReal htop
  filter_upwards [hηStar_ev, hconst_ev] with δ hδ_sticky ⟨hδ_pos, hδ_le1, hC_le⟩
  intro γ hγ ι s V hB hED s' hs' W hWtube hWshade C hCunif 𝒲 hfull hfrost
  have hδ_ne : (δ : ENNReal) ≠ 0 := (ENNReal.coe_pos.mpr hδ_pos).ne'
  -- the sub-shading lives in `B₁` because its tubes are those of `V`
  have hB' : ∀ i ∈ s', (W i).carrier ⊆ Metric.closedBall (0 : E) 1 := by
    intro i hi
    have : (W i).carrier = (V i).carrier := by
      change ((W i).toTube).carrier = ((V i).toTube).carrier
      rw [hWtube i]
    rw [this]
    exact hB i (hs' hi)
  have hfull_nn : (δ ^ ηStar : NNReal)
      ≤ ShadedBody.fullness s' (fun i => (W i).toShadedBody) :=
    ENNReal.coe_le_coe.mp
      (by simpa [ENNReal.rpow_ofNNReal hηStar_pos.le] using hfull)
  have hED' : (s' : Set ι).Pairwise
      (fun i j => IsEssentiallyDistinct (W i).carrier (W j).carrier) := by
    intro i hi j hj hij
    have hsource := hED (hs' hi) (hs' hj) hij
    change IsEssentiallyDistinct ((W i).toTube).carrier ((W j).toTube).carrier
    rw [hWtube i, hWtube j]
    exact hsource
  have hsticky : (δ : ENNReal) ^ (γ₀ / 2) ≤ volume (⋃ i ∈ s', (W i).shade) :=
    hδ_sticky s' W hB' hED' hCunif 𝒲 hfull_nn hfrost
  -- the shrunk union sits inside the given one
  have hmono : (⋃ i ∈ s', (W i).shade) ⊆ (⋃ i ∈ s, (V i).shade) := by
    intro x hx
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp hx
    exact Set.mem_iUnion₂.mpr ⟨i, hs' hi, hWshade i hxi⟩
  have hunion : (δ : ENNReal) ^ (γ₀ / 2) ≤ volume (⋃ i ∈ s, (V i).shade) :=
    hsticky.trans (measure_mono hmono)
  let X : ENNReal := (s.card : ENNReal) * (δ : ENNReal) ^ (2 : ℕ)
  let a : ℝ := γ - c
  have hbound :=
    Kakeya.multiplicity_le_div_of_le_volume_iUnionShade hδ_le1 s V
      (u := (δ : ENNReal) ^ (γ₀ / 2))
      (ENNReal.rpow_pos (ENNReal.coe_pos.mpr hδ_pos) ENNReal.coe_ne_top) hunion
  have hαge : γ₀ / 2 ≤ a := by
    dsimp [a]
    nlinarith [hc, hγ.1]
  have hαpos : 0 < a := lt_of_lt_of_le hγ₀half hαge
  have hαle2 : a ≤ 2 := by
    dsimp [a]
    nlinarith [hc0, hγ.2]
  have hcard : (s.card : ENNReal) ≤ Ccard * (δ : ENNReal) ^ (-4 : ℝ) := by
    dsimp [Ccard]
    exact card_le hdim hδ_pos hδ_le1 s (fun i => (V i).toTube) hB hED
  have hX_le : X ≤ Ccard * (δ : ENNReal) ^ (-2 : ℝ) := by
    calc
      X ≤ Ccard * (δ : ENNReal) ^ (-4 : ℝ) * (δ : ENNReal) ^ (2 : ℕ) := by
        dsimp [X]
        exact mul_le_mul_left hcard _
      _ = Ccard * (δ : ENNReal) ^ (-2 : ℝ) := by
        rw [mul_assoc, ← ENNReal.rpow_natCast (δ : ENNReal) 2,
          ← ENNReal.rpow_add _ _ hδ_ne ENNReal.coe_ne_top]
        norm_num
  have hXsplit : X ≤ Ccard * (δ : ENNReal) ^ (-a) * X ^ (1 - a / 2) := by
    have hα2 : (0 : ℝ) ≤ a / 2 := by linarith
    rcases eq_or_ne X 0 with hX0 | hXne0
    · rw [hX0]
      exact zero_le
    have hδne2 : (δ : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr (ne_of_gt hδ_pos)
    have hXtop : X ≠ ⊤ :=
      ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top (by simp [hδne2])) hX_le
    have hXα : X ^ (a / 2) ≤ Ccard * (δ : ENNReal) ^ (-a) := by
      calc
        X ^ (a / 2) ≤ (Ccard * (δ : ENNReal) ^ (-2 : ℝ)) ^ (a / 2) :=
          ENNReal.rpow_le_rpow hX_le hα2
        _ = Ccard ^ (a / 2) * (δ : ENNReal) ^ (-a) := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ hα2, ← ENNReal.rpow_mul,
            show (-2 : ℝ) * (a / 2) = -a by ring]
        _ ≤ Ccard * (δ : ENNReal) ^ (-a) := by
          have hCge1 : (1 : ENNReal) ≤ Ccard := by
            dsimp [Ccard]
            exact ENNReal.one_le_coe_iff.mpr cardBound.one_le_C
          have hCpow : Ccard ^ (a / 2) ≤ Ccard ^ (1 : ℝ) :=
            ENNReal.rpow_le_rpow_of_exponent_le hCge1 (by linarith : a / 2 ≤ 1)
          exact mul_le_mul_left (by simpa using hCpow) _
    calc
      X = X ^ (a / 2) * X ^ (1 - a / 2) := by
        rw [← ENNReal.rpow_add _ _ hXne0 hXtop,
          show a / 2 + (1 - a / 2) = (1 : ℝ) by ring, ENNReal.rpow_one]
      _ ≤ Ccard * (δ : ENNReal) ^ (-a) * X ^ (1 - a / 2) := mul_le_mul_left hXα _
  have key : ∀ B : ENNReal, B ≤ (δ : ENNReal) ^ (-α) →
      B / (δ : ENNReal) ^ (γ₀ / 2) * (δ : ENNReal) ^ (-a)
        ≤ (δ : ENNReal) ^ (-α) * (δ : ENNReal) ^ (-2 * a) := by
    intro B hB
    calc
      B / (δ : ENNReal) ^ (γ₀ / 2) * (δ : ENNReal) ^ (-a)
          ≤ (δ : ENNReal) ^ (-α) / (δ : ENNReal) ^ (γ₀ / 2) * (δ : ENNReal) ^ (-a) :=
            mul_le_mul_left (ENNReal.div_le_div_right hB _) _
      _ = (δ : ENNReal) ^ (-α - γ₀ / 2) * (δ : ENNReal) ^ (-a) := by
            rw [ENNReal.rpow_sub _ _ hδ_ne ENNReal.coe_ne_top]
      _ = (δ : ENNReal) ^ (-α - a - γ₀ / 2) := by
            rw [← ENNReal.rpow_add _ _ hδ_ne ENNReal.coe_ne_top,
              show (-α - γ₀ / 2) + -a = -α - a - γ₀ / 2 by ring]
      _ ≤ (δ : ENNReal) ^ (-α - 2 * a) :=
            ENNReal.rpow_le_rpow_of_exponent_ge (by exact_mod_cast hδ_le1) (by nlinarith [hαge])
      _ = (δ : ENNReal) ^ (-α) * (δ : ENNReal) ^ (-2 * a) := by
            rw [← ENNReal.rpow_add _ _ hδ_ne ENNReal.coe_ne_top,
              show (-α + -2 * a : ℝ) = -α - 2 * a by ring]
  have hfinal : multiplicity s (fun i => (V i).toShadedBody) ≤
      (δ : ENNReal) ^ (-α) * (δ : ENNReal) ^ (-2 * a) * X ^ (1 - a / 2) := by
    calc
      multiplicity s (fun i => (V i).toShadedBody)
          ≤ Cvol * ((s.card : ENNReal) * (δ : ENNReal) ^ (Module.finrank ℝ E - 1)) /
              (δ : ENNReal) ^ (γ₀ / 2) :=
            hbound
      _ ≤ Cvol * X / (δ : ENNReal) ^ (γ₀ / 2) := by
            dsimp [X]
            rw [show (δ : ENNReal) ^ (Module.finrank ℝ E - 1) = (δ : ENNReal) ^ (2 : ℕ) by
              rw [hdim]]
      _ ≤ Cvol * (Ccard * (δ : ENNReal) ^ (-a) * X ^ (1 - a / 2)) / (δ : ENNReal) ^ (γ₀ / 2) := by
            exact ENNReal.div_le_div_right
              (by simpa [mul_assoc, mul_comm, mul_left_comm] using (mul_le_mul_left hXsplit Cvol)) _
      _ = (Cvol * Ccard) / (δ : ENNReal) ^ (γ₀ / 2) * (δ : ENNReal) ^ (-a) * X ^ (1 - a / 2) := by
            simp only [div_eq_mul_inv]
            ring
      _ ≤ (δ : ENNReal) ^ (-α) * (δ : ENNReal) ^ (-2 * a) * X ^ (1 - a / 2) := by
            exact mul_le_mul_left (key (Cvol * Ccard) hC_le) _
  simpa [a, X] using hfinal


/-! ### Route A: reaching the sticky-Kakeya cap by a band restriction against the tight net -/

section RouteA

open _root_.Tube

variable {ι : Type*} [Nontrivial E]

open scoped Classical in
/-- **Band restriction against the tight net.** -/
theorem exists_restrict_uniformTubeSet_band_of_nice {δ : NNReal} {s s' : Finset ι}
    {T : ι → Tube δ E} {M : ℕ} {Cu A C : NNReal} (𝒰 : UniformTubeSet s T M Cu)
    (hnice : 𝒰.Nice) (hs' : s' ⊆ s)
    (hBC : ((Tube.overlapConstBOTight (Module.finrank ℝ E) : ℕ) : NNReal) ≤ C)
    (hAC : A ≤ C) (hC1 : 1 ≤ C) (b : ℕ → NNReal)
    (hband : ∀ k ≤ M, ∀ j ∈ s'.image (𝒰.cover.assign k),
      b k ≤ ((coverClass s' (𝒰.cover.assign k) j).card : NNReal) ∧
        ((coverClass s' (𝒰.cover.assign k) j).card : NNReal) ≤ A * b k) :
    ∃ 𝒰' : UniformTubeSet s' T M C,
      (∀ k, 𝒰'.cover.indexSet k = s'.image (𝒰.cover.assign k)) ∧
        (∀ k, 𝒰'.cover.assign k = 𝒰.cover.assign k) ∧
          (∀ k, 𝒰'.cover.tube k = 𝒰.cover.tube k) ∧
            (∀ k, 𝒰'.branchingN k = b k) := by
  refine ⟨⟨⟨fun k => s'.image (𝒰.cover.assign k), 𝒰.cover.assign, 𝒰.cover.tube,
      (fun k hk i hi => Finset.mem_image_of_mem (𝒰.cover.assign k) hi),
      (fun k hk i hi => 𝒰.cover.le_tube_assign k hk i (hs' hi)),
      (fun k hk i hi j hj h => 𝒰.cover.nested k hk i (hs' hi) j (hs' hj) h),
      (fun k hk i hi => 𝒰.cover.tube_nested k hk i (hs' hi))⟩,
      b, ?_, ?_, ?_, ?_⟩, fun k => rfl, fun k => rfl, fun k => rfl, fun k => rfl⟩
  · intro k hk
    refine Set.InjOn.mono ?_ (𝒰.tube_injOn k hk)
    intro j hj
    rcases Finset.mem_image.mp hj with ⟨i, hi, rfl⟩
    exact 𝒰.cover.assign_mem k hk i (hs' hi)
  · -- bounded overlap, read off the *tight* net rather than inherited from `Cu`
    intro k hk V
    have hsub :
        ((s'.image (𝒰.cover.assign k)).filter (fun j => ∃ i ∈ s',
            (T i).toConvexSpaceBody ≤ (𝒰.cover.tube k j).toConvexSpaceBody ∧
            (T i).toConvexSpaceBody ≤ V.toConvexSpaceBody))
          ⊆ ((𝒰.cover.indexSet k).filter (fun v => ∃ i ∈ s,
            (T i).toConvexSpaceBody ≤ (𝒰.cover.tube k v).toConvexSpaceBody ∧
            (T i).toConvexSpaceBody ≤ V.toConvexSpaceBody)) := by
      intro j hj
      rw [Finset.mem_filter] at hj ⊢
      obtain ⟨hjm, i, hi, hb⟩ := hj
      obtain ⟨i', hi', rfl⟩ := Finset.mem_image.mp hjm
      exact ⟨𝒰.cover.assign_mem k hk i' (hs' hi'), i, hs' hi, hb⟩
    calc (((s'.image (𝒰.cover.assign k)).filter (fun j => ∃ i ∈ s',
            (T i).toConvexSpaceBody ≤ (𝒰.cover.tube k j).toConvexSpaceBody ∧
            (T i).toConvexSpaceBody ≤ V.toConvexSpaceBody)).card : NNReal)
        ≤ (((𝒰.cover.indexSet k).filter (fun v => ∃ i ∈ s,
            (T i).toConvexSpaceBody ≤ (𝒰.cover.tube k v).toConvexSpaceBody ∧
            (T i).toConvexSpaceBody ≤ V.toConvexSpaceBody)).card : NNReal) := by
          exact_mod_cast Finset.card_le_card hsub
      _ ≤ ((Tube.overlapConstBOTight (Module.finrank ℝ E) : ℕ) : NNReal) := by
          exact_mod_cast hnice k hk V
      _ ≤ C := hBC
  · exact fun k hk j hj =>
      (hband k hk j hj).2.trans (mul_le_mul_of_nonneg_right hAC zero_le)
  · exact fun k hk j hj => (hband k hk j hj).1.trans (le_mul_of_one_le_left zero_le hC1)

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
open scoped Classical in
/-- **The per-node retention of a band restriction.** -/
theorem card_coverClass_le_of_band {u w : Finset ι} (assign : ι → ι) (huw : u ⊆ w)
    {bk : ℕ} {Cd bn L : ℝ} (hCd1 : 1 ≤ Cd) (hL1 : 1 ≤ L) (hbn0 : 0 ≤ bn)
    (hhigh : ∀ j ∈ u.image assign, ((coverClass u assign j).card : ℝ) ≤ 2 * bk)
    (hlow : ∀ j ∈ u.image assign, (bk : ℝ) ≤ ((coverClass u assign j).card : ℝ))
    (hwlo : ∀ j ∈ w.image assign, bn ≤ Cd * ((coverClass w assign j).card : ℝ))
    (hwhi : ∀ j ∈ w.image assign, ((coverClass w assign j).card : ℝ) ≤ Cd * bn)
    (hret : (w.card : ℝ) ≤ L * (u.card : ℝ)) :
    ∀ j ∈ u.image assign,
      ((coverClass w assign j).card : ℝ)
        ≤ 2 * L * Cd ^ 2 * ((coverClass u assign j).card : ℝ) := by
  classical
  intro j₀ hj₀
  set I : Finset ι := u.image assign with hI
  have hIw : I ⊆ w.image assign := Finset.image_subset_image huw
  have hne : I.Nonempty := ⟨j₀, hj₀⟩
  have hn1 : (1 : ℝ) ≤ (I.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hne
  have hupart : (u.card : ℝ) = ∑ j ∈ I, ((coverClass u assign j).card : ℝ) := by
    rw [hI]
    exact_mod_cast congrArg (Nat.cast : ℕ → ℝ) (Finset.card_eq_sum_card_image assign u)
  have hwpart : (w.card : ℝ) = ∑ j ∈ w.image assign, ((coverClass w assign j).card : ℝ) := by
    exact_mod_cast congrArg (Nat.cast : ℕ → ℝ) (Finset.card_eq_sum_card_image assign w)
  -- `u.card ≤ #I · 2 b_k`
  have hu_le : (u.card : ℝ) ≤ (I.card : ℝ) * (2 * bk) := by
    rw [hupart]
    calc ∑ j ∈ I, ((coverClass u assign j).card : ℝ) ≤ ∑ _j ∈ I, (2 * (bk : ℝ)) :=
          Finset.sum_le_sum hhigh
      _ = (I.card : ℝ) * (2 * bk) := by rw [Finset.sum_const, nsmul_eq_mul]
  -- `#I · bn ≤ Cd · w.card`
  have hsub_sum : ∑ j ∈ I, ((coverClass w assign j).card : ℝ) ≤ (w.card : ℝ) := by
    rw [hwpart]
    exact Finset.sum_le_sum_of_subset_of_nonneg hIw (fun _ _ _ => by positivity)
  have hI_bn : (I.card : ℝ) * bn ≤ Cd * (w.card : ℝ) := by
    calc (I.card : ℝ) * bn = ∑ _j ∈ I, bn := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ j ∈ I, Cd * ((coverClass w assign j).card : ℝ) :=
          Finset.sum_le_sum (fun j hj => hwlo j (hIw hj))
      _ = Cd * ∑ j ∈ I, ((coverClass w assign j).card : ℝ) := by rw [Finset.mul_sum]
      _ ≤ Cd * (w.card : ℝ) := by
          exact mul_le_mul_of_nonneg_left hsub_sum (by linarith)
  -- hence `bn ≤ 2 L Cd b_k`
  have hCd0 : (0 : ℝ) < Cd := by linarith
  have hL0 : (0 : ℝ) < L := by linarith
  have hbk0 : (0 : ℝ) ≤ (bk : ℝ) := by positivity
  have hbn_le : bn ≤ 2 * L * Cd * bk := by
    have hchain : (I.card : ℝ) * bn ≤ (I.card : ℝ) * (2 * L * Cd * bk) := by
      calc (I.card : ℝ) * bn ≤ Cd * (w.card : ℝ) := hI_bn
        _ ≤ Cd * (L * (u.card : ℝ)) := by
            exact mul_le_mul_of_nonneg_left hret hCd0.le
        _ ≤ Cd * (L * ((I.card : ℝ) * (2 * bk))) := by
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hu_le hL0.le) hCd0.le
        _ = (I.card : ℝ) * (2 * L * Cd * bk) := by ring
    have hIpos : (0 : ℝ) < (I.card : ℝ) := by linarith
    exact le_of_mul_le_mul_left (by linarith [hchain]) hIpos
  -- conclude at the node
  calc ((coverClass w assign j₀).card : ℝ) ≤ Cd * bn := hwhi j₀ (hIw hj₀)
    _ ≤ Cd * (2 * L * Cd * bk) := mul_le_mul_of_nonneg_left hbn_le hCd0.le
    _ = 2 * L * Cd ^ 2 * (bk : ℝ) := by ring
    _ ≤ 2 * L * Cd ^ 2 * ((coverClass u assign j₀).card : ℝ) := by
        refine mul_le_mul_of_nonneg_left (hlow j₀ hj₀) ?_
        positivity

open scoped Classical in
/-- **The every-scale Frostman bound survives a band restriction**, at the cost of the per-node
cardinality ratio `κ⁻¹`. -/
theorem isFrostmanAtEveryScale_restrict {δ : NNReal} (hδ : 0 < δ) {s s' : Finset ι}
    {T : ι → Tube δ E} {M : ℕ} {Cu C : NNReal}
    {𝒰 : UniformTubeSet s T M Cu} {𝒰' : UniformTubeSet s' T M C}
    (hs' : s' ⊆ s)
    (hidx : ∀ k, 𝒰'.cover.indexSet k = s'.image (𝒰.cover.assign k))
    (hassign : ∀ k, 𝒰'.cover.assign k = 𝒰.cover.assign k)
    (htube : ∀ k, 𝒰'.cover.tube k = 𝒰.cover.tube k)
    {A κ : ENNReal} (hκ : κ ≠ 0) (h : 𝒰.IsFrostmanAtEveryScale A)
    (hcard : ∀ k ≤ M, ∀ j ∈ s'.image (𝒰.cover.assign k),
      κ * ((coverClass s (𝒰.cover.assign k) j).card : ENNReal)
        ≤ ((coverClass s' (𝒰.cover.assign k) j).card : ENNReal)) :
    𝒰'.IsFrostmanAtEveryScale (κ⁻¹ * A) := by
  intro k hk j hj
  rw [hidx k] at hj
  obtain ⟨i₁, hi₁s', hi₁⟩ := Finset.mem_image.mp hj
  have hjmem : j ∈ 𝒰.cover.indexSet k := by
    rw [← hi₁]; exact 𝒰.cover.assign_mem k hk i₁ (hs' hi₁s')
  have hbig := h k hk j hjmem
  have hbigne : (coverClass s (𝒰.cover.assign k) j).Nonempty := by
    refine ⟨i₁, ?_⟩
    simp only [coverClass, Finset.mem_filter]
    exact ⟨hs' hi₁s', hi₁⟩
  have hclssub : coverClass s' (𝒰.cover.assign k) j ⊆ coverClass s (𝒰.cover.assign k) j := by
    simp only [coverClass]
    exact Finset.filter_subset_filter _ hs'
  obtain ⟨i₀, hi₀⟩ := hbigne
  have hvol : ∀ i ∈ coverClass s (𝒰.cover.assign k) j,
      volume ((fun i => (T i).toConvexSpaceBody) i).carrier
        = volume ((T i₀).toConvexSpaceBody).carrier := by
    intro i _
    exact _root_.Tube.volume_carrier_eq_volume_carrier (T i) (T i₀)
  have hWK : ∀ i ∈ coverClass s (𝒰.cover.assign k) j,
      (T i).toConvexSpaceBody ≤ (𝒰.cover.tube k j).toConvexSpaceBody := by
    intro i hi
    simp only [coverClass, Finset.mem_filter] at hi
    have := 𝒰.cover.le_tube_assign k hk i hi.1
    rwa [hi.2] at this
  have hsub := ConvexSpaceBody.frostmanConstIn_subfamily_le
    (s := coverClass s (𝒰.cover.assign k) j) (s' := coverClass s' (𝒰.cover.assign k) j)
    (W := fun i => (T i).toConvexSpaceBody) (K := (𝒰.cover.tube k j).toConvexSpaceBody)
    (κ := κ) (v := volume ((T i₀).toConvexSpaceBody).carrier)
    ⟨i₀, hi₀⟩ hvol hWK hclssub hκ (hcard k hk j hj)
  have hbigC : ConvexSpaceBody.frostmanConstIn (coverClass s (𝒰.cover.assign k) j)
      (fun i => (T i).toConvexSpaceBody) (𝒰.cover.tube k j).toConvexSpaceBody ≤ A :=
    ConvexSpaceBody.frostmanConstant_le_of_isFrostmanIn hbig
  rw [hassign k, htube k]
  refine ConvexSpaceBody.IsFrostmanIn.mono
    (ConvexSpaceBody.isFrostmanIn_frostmanConstIn _ _ _) ?_
  exact hsub.trans (mul_le_mul_left' hbigC _)


end RouteA

/-! ### The assembly -/

section Assembly

open _root_.Tube




end Assembly

end ml1Boot

end Kakeya
