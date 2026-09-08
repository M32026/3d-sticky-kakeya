/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma1.Factoring
public import Kakeya.DimensionThree.MainLemma1.OneSidedUniform

/-!
# Section 2 uniformization carrying a two-sided density band

`ShadedTube.exists_shadedUniformTubeSet_subfamily_ssf` produces a uniform subfamily whose
shading has been shrunk, but it controls the shrinkage only *in aggregate*
(`ShadedBody.fullness'`).  The factoring bundles of Main Lemma 1 — `IsUniformFactorCore.fine_dens`
and `coarse_dens`, and `IsCaseTwoInput.band` — need instead a *termwise* bracket
`λ |T| ≤ |Y| ≤ 2 λ |T|` on the **output** shading, at the same retained index set that carries
the uniformity.  That is the interface whose previous sorried carrier
`Kakeya.ml1Boot.exists_shadedUniform_of_card_le` was deleted (`MainLemma1/Inventory.lean`, §B).

This file supplies it, in the reading in which it is **provable**: the uniformity clause is the
one-sided `Kakeya.ml1Boot.IsOneSidedUniform` rather than the two-sided
`ShadedTube.ShadedUniformTubeSet`.

## Why the reading has to be one-sided

The two pigeonholes do not commute in the two-sided reading, and the reason is structural.

* Banding *before* uniformizing is useless: `ShadedTube.exists_shadedUniformTubeSet_subfamily_ssf`
  replaces each shading `Y i` by a subset `Y' i` with no per-member lower bound at all, so the
  lower half of the band does not survive the uniformization.
* Banding *after* uniformizing restricts the index set, and
  `ShadedTube.ShadedUniformTubeSet.le_card_shadeClass` is a *lower* bound on a filtered
  cardinality: it is destroyed by any restriction of the index set.  There is no
  `mono_index` for the two-sided predicate and there cannot be one.

The one-sided predicate is exactly the half that survives restriction
(`Kakeya.ml1Boot.IsOneSidedUniform.of_shadedUniformTubeSet_subset`), so "uniformize, then band,
then project-and-restrict" closes.  The input band at `λ₀` is what pays for the cardinality
retention: without it a family may have arbitrarily many members of negligible shade mass, and
the band pigeonhole retains no definite fraction of the index set.

## The arithmetic

With `η = min α α' / 8`, and writing `A = ∑_{s₁} |Y i|`, `B = ∑_{s₁} |Y' i|`:

* the uniformization gives `#s ≤ δ^{-η} #s₁` and `A ≤ δ^{-η} B`;
* the input band gives `A ≥ #s₁ λ₀ v`, whence `B > 0` and the band pigeonhole applies;
* `Kakeya.ml1Boot.exists_massBand` gives `s₂ ⊆ s₁`, a band at `λ`, `B ≤ bandLoss(#s₁) ∑_{s₂}|Y'|`
  and `fullness(s₁, Y') ≤ bandLoss(#s₁) λ`;
* `Kakeya.ml1Boot.eventually_bandLoss_le_rpow_neg` turns `bandLoss` into `δ^{-η}`, giving both
  `δ^{2η} λ₀ ≤ λ` and `#s₁ ≤ 4 δ^{-2η} #s₂ ≤ δ^{-3η} #s₂`, the last step because `λ ≤ 2 λ₀`
  (read at any member of `s₂`) and `4 ≤ δ^{-η}` eventually.

The cardinality budget is read at the exponent `7` supplied by
`Kakeya.ml1Boot.eventually_card_le_rpow_neg_seven` for pairwise essentially distinct tubes in
`B₁ ⊆ ℝ³`, which is the only budget `Kakeya.ml1Boot.eventually_bandLoss_le_rpow_neg` absorbs.

## Main statements

* `Kakeya.ml1Boot.card_le_rpow_mul_card_of_ennreal` — cardinality transport `[0, ∞] → ℝ`;
* `Kakeya.ml1Boot.exists_shadedUniformBand_of_card_le` — the interface.
-/

@[expose] public section

open MeasureTheory ShadedBody Filter Topology
open scoped NNReal ENNReal

namespace Kakeya.ml1Boot

universe u

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

/-- Transport a cardinality comparison from `[0, ∞]` to `ℝ`. -/
theorem card_le_rpow_mul_card_of_ennreal {δ : NNReal} (hδ0 : 0 < δ) {a : ℝ} {m m' : ℕ}
    (h : (m : ENNReal) ≤ (δ : ENNReal) ^ (-a) * (m' : ENNReal)) :
    (m : ℝ) ≤ (δ : ℝ) ^ (-a) * (m' : ℝ) := by
  have hδR : 0 < (δ : ℝ) := by exact_mod_cast hδ0
  have hrw : (δ : ENNReal) ^ (-a) = ENNReal.ofReal ((δ : ℝ) ^ (-a)) :=
    ennreal_coe_nnreal_rpow hδR (-a)
  rw [hrw, ← ENNReal.ofReal_natCast m', ← ENNReal.ofReal_mul (Real.rpow_nonneg hδR.le _),
    ← ENNReal.ofReal_natCast m] at h
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h


/-- **Section 2 uniformization with a density band, one-sided.** -/
theorem exists_shadedUniformBand_of_card_le (hdim : Module.finrank ℝ E = 3)
    {α α' : ℝ} (hα : 0 < α) (hα' : 0 < α') :
    ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
      ∀ {ι : Type u} (s : Finset ι) (V : ι → ShadedTube δ E) (lam₀ : NNReal),
        s.Nonempty → 0 < lam₀ →
        (∀ i ∈ s, (V i).carrier ⊆ Metric.closedBall (0 : E) 1) →
        (s.card : ℝ) ≤ (δ : ℝ) ^ (-(7 : ℝ)) →
        (∀ i ∈ s, (lam₀ : ENNReal) * volume (V i).carrier ≤ volume (V i).shade ∧
          volume (V i).shade ≤ 2 * (lam₀ : ENNReal) * volume (V i).carrier) →
        ∃ s' ⊆ s, ∃ V' : ι → ShadedTube δ E, ∃ lam : NNReal,
          s'.Nonempty ∧ 0 < lam ∧
          (∀ i, (V' i).toTube = (V i).toTube) ∧
          (∀ i, (V' i).shade ⊆ (V i).shade) ∧
          (s.card : ℝ) ≤ (δ : ℝ) ^ (-α) * (s'.card : ℝ) ∧
          (δ : ENNReal) ^ α' * (lam₀ : ENNReal) ≤ (lam : ENNReal) ∧
          (∀ i ∈ s', (lam : ENNReal) * volume (V i).carrier ≤ volume (V' i).shade ∧
            volume (V' i).shade ≤ 2 * (lam : ENNReal) * volume (V i).carrier) ∧
          Nonempty (IsOneSidedUniform s' V' (Tube.ssfGridLen δ)
            (ShadedTube.ssfUniformConst 3)) := by
  classical
  set η : ℝ := min α α' / 8 with hη_def
  have hη : 0 < η := by
    have h : 0 < min α α' := lt_min hα hα'
    simp only [hη_def]; linarith
  have hηα : 4 * η ≤ α := by
    have : min α α' ≤ α := min_le_left _ _
    simp only [hη_def]; linarith
  have hηα' : 2 * η ≤ α' := by
    have : min α α' ≤ α' := min_le_right _ _
    simp only [hη_def]; linarith
  obtain ⟨δ₀, hδ₀pos, hδ₀1, hssf⟩ :=
    ShadedTube.exists_shadedUniformTubeSet_subfamily_ssf.{u} (E := E) 7 η η hη hη
  filter_upwards [eventually_le_nhdsGT hδ₀pos, eventually_bandLoss_le_rpow_neg (η := η) hη,
      eventually_finite_const_le_rpow_neg (c := (4 : ENNReal)) (by simp) (a := η) hη,
      self_mem_nhdsWithin] with δ hδδ₀ hBl h4 hδmem
  have hδ0 : 0 < δ := hδmem
  have hδ1 : δ ≤ 1 := le_trans hδδ₀ hδ₀1
  have hδE : (δ : ENNReal) ≠ 0 := by simpa using ne_of_gt hδ0
  have hδEtop : (δ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hδEle1 : (δ : ENNReal) ≤ 1 := by exact_mod_cast hδ1
  intro ι s V lam₀ hs_ne hlam₀ hball hcard hbandin
  obtain ⟨i₀, hi₀⟩ := hs_ne
  -- the common carrier volume
  set v : ENNReal := volume (V i₀).carrier with hv_def
  have hvpos : 0 < v := (tube_volume_pos_ne_top hδ0 (V i₀).toTube).1
  have hvtop : v ≠ ⊤ := (tube_volume_pos_ne_top hδ0 (V i₀).toTube).2
  have hcar : ∀ i, volume (V i).carrier = v := fun i =>
    _root_.Tube.volume_carrier_eq_volume_carrier (V i).toTube (V i₀).toTube
  -- Step 1: uniformize
  obtain ⟨s₁, hs₁s, V', hVto, hVsh, hcard₁, hfull₁, hstruct⟩ :=
    hssf hδ0 hδδ₀ s V hball hcard
  have hcarV' : ∀ i, volume (V' i).carrier = v := by
    intro i
    have : (V' i).carrier = (V i).carrier := by rw [hVto i]
    rw [this, hcar i]
  -- `s₁` is nonempty
  have hs_pos : 0 < s.card := Finset.card_pos.mpr ⟨i₀, hi₀⟩
  have hs₁ne : s₁.Nonempty := by
    rw [← Finset.card_pos]
    by_contra hzero
    have hz : s₁.card = 0 := by omega
    rw [hz] at hcard₁
    simp only [Nat.cast_zero, mul_zero] at hcard₁
    have : (0 : ℝ) < (s.card : ℝ) := by exact_mod_cast hs_pos
    linarith
  have hs₁pos : 0 < s₁.card := Finset.card_pos.mpr hs₁ne
  -- carrier sums
  have hsumcar : ∑ i ∈ s₁, volume (V i).carrier = (s₁.card : ENNReal) * v := by
    rw [Finset.sum_congr rfl (fun i _ => hcar i), Finset.sum_const, nsmul_eq_mul]
  have hsumcar' : ∑ i ∈ s₁, volume (V' i).carrier = (s₁.card : ENNReal) * v := by
    rw [Finset.sum_congr rfl (fun i _ => hcarV' i), Finset.sum_const, nsmul_eq_mul]
  set D : ENNReal := (s₁.card : ENNReal) * v with hD_def
  have hcardEpos : (0 : ENNReal) < (s₁.card : ENNReal) := by exact_mod_cast hs₁pos
  have hDne : D ≠ 0 := mul_ne_zero (ne_of_gt hcardEpos) (ne_of_gt hvpos)
  have hDtop : D ≠ ⊤ := ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hvtop
  set A : ENNReal := ∑ i ∈ s₁, volume (V i).shade with hA_def
  set B : ENNReal := ∑ i ∈ s₁, volume (V' i).shade with hB_def
  have hcoe : ENNReal.ofReal ((δ : ℝ) ^ (-η)) = (δ : ENNReal) ^ (-η) := by
    have hδR : 0 < (δ : ℝ) := by exact_mod_cast hδ0
    exact (ennreal_coe_nnreal_rpow hδR (-η)).symm
  have hfullA : ShadedBody.fullness' s₁ (fun i => (V i).toShadedBody) = A / D := by
    change (∑ i ∈ s₁, volume (V i).shade) / (∑ i ∈ s₁, volume (V i).carrier) = A / D
    rw [hsumcar]
  have hfullB : ShadedBody.fullness' s₁ (fun i => (V' i).toShadedBody) = B / D := by
    change (∑ i ∈ s₁, volume (V' i).shade) / (∑ i ∈ s₁, volume (V' i).carrier) = B / D
    rw [hsumcar']
  have hAB : A ≤ (δ : ENNReal) ^ (-η) * B := by
    rw [hfullA, hfullB, hcoe] at hfull₁
    calc A = A / D * D := (ENNReal.div_mul_cancel hDne hDtop).symm
      _ ≤ ((δ : ENNReal) ^ (-η) * (B / D)) * D := by exact mul_le_mul_left hfull₁ D
      _ = (δ : ENNReal) ^ (-η) * (B / D * D) := by ring
      _ = (δ : ENNReal) ^ (-η) * B := by rw [ENNReal.div_mul_cancel hDne hDtop]
  -- lower bound on the input mass over `s₁`
  have hA_lower : (s₁.card : ENNReal) * ((lam₀ : ENNReal) * v) ≤ A := by
    have hterm : ∀ i ∈ s₁, (lam₀ : ENNReal) * v ≤ volume (V i).shade := by
      intro i hi
      have := (hbandin i (hs₁s hi)).1
      rwa [hcar i] at this
    calc (s₁.card : ENNReal) * ((lam₀ : ENNReal) * v)
        = ∑ _i ∈ s₁, (lam₀ : ENNReal) * v := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ A := Finset.sum_le_sum hterm
  have hlam₀E : (0 : ENNReal) < (lam₀ : ENNReal) := by exact_mod_cast hlam₀
  have hApos : 0 < A :=
    lt_of_lt_of_le (ENNReal.mul_pos (ne_of_gt hcardEpos) (ne_of_gt
      (ENNReal.mul_pos (ne_of_gt hlam₀E) (ne_of_gt hvpos)))) hA_lower
  have hBpos : 0 < B := by
    by_contra hcon
    have hB0 : B = 0 := by
      simpa using le_antisymm (not_lt.mp hcon) (zero_le : (0:ENNReal) ≤ B)
    rw [hB0, mul_zero] at hAB
    exact absurd (le_antisymm hAB (zero_le : (0:ENNReal) ≤ A)) (ne_of_gt hApos)
  -- Step 2: the dyadic mass band on the uniformized shading
  obtain ⟨s₂, hs₂s₁, lam, hlam0, hs₂ne, hwin, hmassband, hfullband⟩ :=
    exists_massBand hδ0 s₁ V' (by simpa [hB_def] using hBpos)
  -- generic `rpow` bookkeeping
  have hpowcancel : ∀ a : ℝ, (δ : ENNReal) ^ a * (δ : ENNReal) ^ (-a) = 1 := by
    intro a
    rw [← ENNReal.rpow_add a (-a) hδE hδEtop]
    simp
  have hs₁card7 : (s₁.card : ℝ) ≤ (δ : ℝ) ^ (-(7 : ℝ)) := by
    refine le_trans ?_ hcard
    exact_mod_cast Finset.card_le_card hs₁s
  have hBl₁ : bandLoss s₁.card ≤ (δ : ENNReal) ^ (-η) := hBl s₁.card hs₁card7
  -- the retained band, read at the input carriers
  have hbandout : ∀ i ∈ s₂, (lam : ENNReal) * volume (V i).carrier ≤ volume (V' i).shade ∧
      volume (V' i).shade ≤ 2 * (lam : ENNReal) * volume (V i).carrier := by
    intro i hi
    have h := hwin i hi
    rw [hcarV' i] at h
    rw [hcar i]
    exact h
  -- `lam ≤ 2 lam₀`
  obtain ⟨j₀, hj₀⟩ := id hs₂ne
  have hvne : v ≠ 0 := ne_of_gt hvpos
  have hlamle : (lam : ENNReal) ≤ 2 * (lam₀ : ENNReal) := by
    have h1 : (lam : ENNReal) * v ≤ volume (V' j₀).shade := by
      have := (hbandout j₀ hj₀).1
      rwa [hcar j₀] at this
    have h2 : volume (V' j₀).shade ≤ volume (V j₀).shade := measure_mono (hVsh j₀)
    have h3 : volume (V j₀).shade ≤ 2 * (lam₀ : ENNReal) * v := by
      have := (hbandin j₀ (hs₁s (hs₂s₁ hj₀))).2
      rwa [hcar j₀] at this
    have hchain : (lam : ENNReal) * v ≤ (2 * (lam₀ : ENNReal)) * v := by
      rw [mul_assoc] at h3 ⊢
      exact le_trans h1 (le_trans h2 (by rwa [← mul_assoc] at h3 ⊢))
    exact (ENNReal.mul_le_mul_iff_left hvne hvtop).mp hchain
  -- the retained density is not much below the input one
  have hBlower : (δ : ENNReal) ^ η * A ≤ B := by
    calc (δ : ENNReal) ^ η * A ≤ (δ : ENNReal) ^ η * ((δ : ENNReal) ^ (-η) * B) := by
          exact mul_le_mul_right hAB _
      _ = ((δ : ENNReal) ^ η * (δ : ENNReal) ^ (-η)) * B := by ring
      _ = B := by rw [hpowcancel η, one_mul]
  have hfullB' : (δ : ENNReal) ^ η * (lam₀ : ENNReal) ≤ B / D := by
    rw [ENNReal.le_div_iff_mul_le (Or.inl hDne) (Or.inl hDtop)]
    calc (δ : ENNReal) ^ η * (lam₀ : ENNReal) * D
        = (δ : ENNReal) ^ η * ((s₁.card : ENNReal) * ((lam₀ : ENNReal) * v)) := by
          rw [hD_def]; ring
      _ ≤ (δ : ENNReal) ^ η * A := mul_le_mul_right hA_lower _
      _ ≤ B := hBlower
  have hfb : B / D ≤ bandLoss s₁.card * (lam : ENNReal) := by
    have h := hfullband
    rw [coe_fullness] at h
    rwa [hfullB] at h
  have hlamlow : (δ : ENNReal) ^ (2 * η) * (lam₀ : ENNReal) ≤ (lam : ENNReal) := by
    have h1 : (δ : ENNReal) ^ η * (lam₀ : ENNReal) ≤ (δ : ENNReal) ^ (-η) * (lam : ENNReal) :=
      le_trans hfullB' (le_trans hfb (mul_le_mul_left hBl₁ _))
    have h2 : (δ : ENNReal) ^ η * ((δ : ENNReal) ^ η * (lam₀ : ENNReal))
        ≤ (δ : ENNReal) ^ η * ((δ : ENNReal) ^ (-η) * (lam : ENNReal)) :=
      mul_le_mul_right h1 _
    calc (δ : ENNReal) ^ (2 * η) * (lam₀ : ENNReal)
        = (δ : ENNReal) ^ η * ((δ : ENNReal) ^ η * (lam₀ : ENNReal)) := by
          rw [show (2 : ℝ) * η = η + η by ring, ENNReal.rpow_add η η hδE hδEtop, mul_assoc]
      _ ≤ (δ : ENNReal) ^ η * ((δ : ENNReal) ^ (-η) * (lam : ENNReal)) := h2
      _ = ((δ : ENNReal) ^ η * (δ : ENNReal) ^ (-η)) * (lam : ENNReal) := by ring
      _ = (lam : ENNReal) := by rw [hpowcancel η, one_mul]
  have hlamfinal : (δ : ENNReal) ^ α' * (lam₀ : ENNReal) ≤ (lam : ENNReal) := by
    refine le_trans (mul_le_mul_left ?_ _) hlamlow
    exact ENNReal.rpow_le_rpow_of_exponent_ge hδEle1 hηα'
  -- Step 3: the cardinality retention
  have hs₂sum : ∑ i ∈ s₂, volume (V' i).shade
      ≤ (s₂.card : ENNReal) * (2 * (lam : ENNReal) * v) := by
    calc ∑ i ∈ s₂, volume (V' i).shade
        ≤ ∑ _i ∈ s₂, 2 * (lam : ENNReal) * v := by
          refine Finset.sum_le_sum (fun i hi => ?_)
          have h := (hbandout i hi).2
          rwa [hcar i] at h
      _ = (s₂.card : ENNReal) * (2 * (lam : ENNReal) * v) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  have hpow3 : (δ : ENNReal) ^ (-η) * ((δ : ENNReal) ^ (-η) * (δ : ENNReal) ^ (-η))
      = (δ : ENNReal) ^ (-(3 * η)) := by
    rw [← ENNReal.rpow_add (-η) (-η) hδE hδEtop, ← ENNReal.rpow_add (-η) (-η + -η) hδE hδEtop]
    ring_nf
  have hstep : (s₁.card : ENNReal) * ((lam₀ : ENNReal) * v)
      ≤ ((δ : ENNReal) ^ (-(3 * η)) * (s₂.card : ENNReal)) * ((lam₀ : ENNReal) * v) := by
    calc (s₁.card : ENNReal) * ((lam₀ : ENNReal) * v)
        ≤ A := hA_lower
      _ ≤ (δ : ENNReal) ^ (-η) * B := hAB
      _ ≤ (δ : ENNReal) ^ (-η) * (bandLoss s₁.card * ∑ i ∈ s₂, volume (V' i).shade) :=
          mul_le_mul_right hmassband _
      _ ≤ (δ : ENNReal) ^ (-η) * ((δ : ENNReal) ^ (-η)
            * ((s₂.card : ENNReal) * (2 * (lam : ENNReal) * v))) := by
          refine mul_le_mul_right ?_ _
          exact le_trans (mul_le_mul_left hBl₁ _) (mul_le_mul_right hs₂sum _)
      _ ≤ (δ : ENNReal) ^ (-η) * ((δ : ENNReal) ^ (-η)
            * ((s₂.card : ENNReal) * (2 * (2 * (lam₀ : ENNReal)) * v))) := by
          gcongr
      _ = (δ : ENNReal) ^ (-η) * ((δ : ENNReal) ^ (-η)
            * ((s₂.card : ENNReal) * (4 * ((lam₀ : ENNReal) * v)))) := by ring
      _ ≤ (δ : ENNReal) ^ (-η) * ((δ : ENNReal) ^ (-η)
            * ((s₂.card : ENNReal) * ((δ : ENNReal) ^ (-η) * ((lam₀ : ENNReal) * v)))) := by
          gcongr
      _ = ((δ : ENNReal) ^ (-η) * ((δ : ENNReal) ^ (-η) * (δ : ENNReal) ^ (-η)))
            * (s₂.card : ENNReal) * ((lam₀ : ENNReal) * v) := by ring
      _ = ((δ : ENNReal) ^ (-(3 * η)) * (s₂.card : ENNReal)) * ((lam₀ : ENNReal) * v) := by
          rw [hpow3]
  have hlvne : (lam₀ : ENNReal) * v ≠ 0 := mul_ne_zero (ne_of_gt hlam₀E) hvne
  have hlvtop : (lam₀ : ENNReal) * v ≠ ⊤ := ENNReal.mul_ne_top ENNReal.coe_ne_top hvtop
  have hcardE : (s₁.card : ENNReal) ≤ (δ : ENNReal) ^ (-(3 * η)) * (s₂.card : ENNReal) :=
    (ENNReal.mul_le_mul_iff_left hlvne hlvtop).mp hstep
  have hcardR : (s₁.card : ℝ) ≤ (δ : ℝ) ^ (-(3 * η)) * (s₂.card : ℝ) :=
    card_le_rpow_mul_card_of_ennreal hδ0 hcardE
  have hδR : 0 < (δ : ℝ) := by exact_mod_cast hδ0
  have hδR1 : (δ : ℝ) ≤ 1 := by exact_mod_cast hδ1
  have hcardfinal : (s.card : ℝ) ≤ (δ : ℝ) ^ (-α) * (s₂.card : ℝ) := by
    have hpos2 : (0 : ℝ) ≤ (s₂.card : ℝ) := by positivity
    calc (s.card : ℝ) ≤ (δ : ℝ) ^ (-η) * (s₁.card : ℝ) := hcard₁
      _ ≤ (δ : ℝ) ^ (-η) * ((δ : ℝ) ^ (-(3 * η)) * (s₂.card : ℝ)) := by
          exact mul_le_mul_of_nonneg_left hcardR (Real.rpow_nonneg hδR.le _)
      _ = ((δ : ℝ) ^ (-η) * (δ : ℝ) ^ (-(3 * η))) * (s₂.card : ℝ) := by ring
      _ = (δ : ℝ) ^ (-(4 * η)) * (s₂.card : ℝ) := by
          rw [← Real.rpow_add hδR]; ring_nf
      _ ≤ (δ : ℝ) ^ (-α) * (s₂.card : ℝ) := by
          refine mul_le_mul_of_nonneg_right ?_ hpos2
          exact Real.rpow_le_rpow_of_exponent_ge hδR hδR1 (by linarith)
  -- assemble
  refine ⟨s₂, hs₂s₁.trans hs₁s, V', lam, hs₂ne, hlam0, hVto, hVsh, hcardfinal, hlamfinal,
    hbandout, ?_⟩
  refine ⟨?_⟩
  have huni := IsOneSidedUniform.of_shadedUniformTubeSet_subset hstruct.some hs₂s₁
  rwa [hdim] at huni

end Kakeya.ml1Boot
