/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Multiplicity
public import Kakeya.Shading

/-!
# Transferring multiplicity from a refined subfamily back to the whole family

`StickyKakeya.StickyKatzTaoEstimate` bounds the multiplicity of a family that carries a
`ShadedUniformTubeSet` hierarchy, and the only construction of such a hierarchy in the tree,
`ShadedTube.exists_shadedUniformTubeSet_subfamily_ssf`, produces one on a **subfamily** `s' ⊆ s`
with `#s ≤ δ^{-α} #s'` and shrunken shadings `Y' ⊆ Y`.  Passing the conclusion back to `s`
therefore needs a comparison of `ShadedBody.multiplicity s Y` with
`ShadedBody.multiplicity s' Y'`.

The cardinality bound `#s ≤ δ^{-α} #s'` alone does **not** suffice: `multiplicity` is
`(∑ |Y|) / |⋃ Y|`, and refining can shrink the numerator and the denominator independently.
What does suffice is the following observation, which is the content of this file:

* the denominator moves in the *right* direction — `⋃_{s'} Y' ⊆ ⋃_s Y`, so
  `|⋃_{s'} Y'| ≤ |⋃_s Y|` — and therefore the entire comparison reduces to a comparison of the
  two **numerators**, `∑_{i ∈ s} |Y i|` against `∑_{i ∈ s'} |Y' i|`
  (`ShadedBody.multiplicity_le_of_subfamily`);
* and the numerators are comparable for free from data the consumer already has to supply:
  `∑_{i ∈ s} |Y i| ≤ #s · |T|` because each shading sits inside its tube, while
  `∑_{i ∈ s'} |Y' i| = λ(s', Y') · #s' · |T|` by the definition of `ShadedBody.fullness'`.  The
  ratio is `(#s / #s') / λ(s', Y')`, and a lower bound on `λ(s', Y')` is *already a hypothesis*
  of `StickyKakeya.StickyKatzTaoEstimate` (`ShadedBody.multiplicity_le_of_subfamily_of_fullness`).

So the multiplicity transfer costs exactly `δ^{-α}` (the refinement loss) times `δ^{-η}` (the
fullness the estimate is applied with), and needs no extra structure from the refinement.

That leaves one datum, which the route owes twice over — once to *apply*
`StickyKakeya.StickyKatzTaoEstimate` and once to pay the transfer: a lower bound
`δ^η ≤ ShadedBody.fullness' s' V'` on the refined pair.
`ShadedTube.exists_shadedUniformTubeSet_subfamily_ssf` does not deliver it: it delivers only the
relative bound `fullness' s' V ≤ δ^{-α'} · fullness' s' V'`, and `fullness'` being an *average*
over the family rather than a minimum, `fullness' s' V` is *not* bounded below by
`fullness' s V` — an arbitrary subfamily of a dense family can be empty of shading.

The last two results of this file close that gap, and they show the needed extra structure is
much weaker than a dyadic density band.  A single cutoff at half the fullness
(`ShadedBody.exists_shade_threshold_subfamily`) produces `s₀ ⊆ s` with `#s ≤ (2/λ) #s₀` on which
*every* shading is at least `(λ/2)|T|`; on such a family fullness is **hereditary**
(`ShadedBody.le_fullness'_of_shade_band`), so the refinement may afterwards select whatever
subfamily its hierarchy needs and the fullness datum survives.
-/

@[expose] public section

open MeasureTheory

noncomputable section

namespace ShadedBody

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {ι : Type*}

/-- **Multiplicity transfer, numerator form.**

If `s' ⊆ s` and each refined shading sits inside the corresponding original one, then any bound
`∑_{i ∈ s} |Y i| ≤ R · ∑_{i ∈ s'} |Y' i|` on the numerators upgrades to
`µ(s, Y) ≤ R · µ(s', Y')`.

The denominators need no hypothesis at all: `⋃_{s'} Y' ⊆ ⋃_s Y`, so the union of the *larger*
family is the *larger* set, which is the direction that helps.  This is why the refinement loss
enters only through the two sums. -/
theorem multiplicity_le_of_subfamily {s s' : Finset ι} (B B' : ι → ShadedBody E)
    (hsub : s' ⊆ s) (hshade : ∀ i ∈ s', (B' i).shade ⊆ (B i).shade) {R : ENNReal}
    (hR : ∑ i ∈ s, volume (B i).shade ≤ R * ∑ i ∈ s', volume (B' i).shade) :
    multiplicity s B ≤ R * multiplicity s' B' := by
  rw [multiplicity_le_iff]
  have hU : volume (⋃ i ∈ s', (B' i).shade) ≤ volume (⋃ i ∈ s, (B i).shade) := by
    refine measure_mono ?_
    intro x hx
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp hx
    exact Set.mem_iUnion₂.mpr ⟨i, hsub hi, hshade i hi hxi⟩
  have hnum : ∑ i ∈ s', volume (B' i).shade
      ≤ multiplicity s' B' * volume (⋃ i ∈ s', (B' i).shade) :=
    (multiplicity_le_iff s' B').mp le_rfl
  calc ∑ i ∈ s, volume (B i).shade
      ≤ R * ∑ i ∈ s', volume (B' i).shade := hR
    _ ≤ R * (multiplicity s' B' * volume (⋃ i ∈ s', (B' i).shade)) := by gcongr
    _ ≤ R * (multiplicity s' B' * volume (⋃ i ∈ s, (B i).shade)) := by gcongr
    _ = R * multiplicity s' B' * volume (⋃ i ∈ s, (B i).shade) := by rw [mul_assoc]

/-- **Multiplicity transfer, the form the sticky route needs.**

All bodies of both families have the same carrier volume `vol` (for tubes of a fixed radius this
is `Kakeya.WangZahl.tubeVolume δ`).  Then a cardinality bound `#s ≤ C · #s'` and a fullness lower
bound `lam ≤ λ(s', Y')` give `µ(s, Y) ≤ (C / lam) · µ(s', Y')`.

Both inputs are already on the table in the intended application: `C = δ^{-α}` is the loss of
`ShadedTube.exists_shadedUniformTubeSet_subfamily_ssf`, and `lam = δ^η` is the fullness
hypothesis of `StickyKakeya.StickyKatzTaoEstimate` itself. -/
theorem multiplicity_le_of_subfamily_of_fullness {s s' : Finset ι} (B B' : ι → ShadedBody E)
    (hsub : s' ⊆ s) (hshade : ∀ i ∈ s', (B' i).shade ⊆ (B i).shade)
    {vol : ENNReal} (hvoltop : vol ≠ ⊤)
    (hcar : ∀ i ∈ s, volume (B i).carrier = vol)
    (hcar' : ∀ i ∈ s', volume (B' i).carrier = vol)
    {C lam : ENNReal} (hlam0 : lam ≠ 0) (hlamtop : lam ≠ ⊤)
    (hcard : (s.card : ENNReal) ≤ C * (s'.card : ENNReal))
    (hfull : lam ≤ fullness' s' B') :
    multiplicity s B ≤ (C / lam) * multiplicity s' B' := by
  refine multiplicity_le_of_subfamily B B' hsub hshade ?_
  -- the two carrier sums
  have hsum : ∑ i ∈ s, volume (B i).carrier = (s.card : ENNReal) * vol := by
    rw [Finset.sum_congr rfl hcar, Finset.sum_const, nsmul_eq_mul]
  have hsum' : ∑ i ∈ s', volume (B' i).carrier = (s'.card : ENNReal) * vol := by
    rw [Finset.sum_congr rfl hcar', Finset.sum_const, nsmul_eq_mul]
  -- the numerator of the big family
  have hbig : ∑ i ∈ s, volume (B i).shade ≤ (s.card : ENNReal) * vol := by
    rw [← hsum]
    exact Finset.sum_le_sum fun i _ => measure_mono (B i).shade_subset
  -- the numerator of the small family, from the fullness bound
  have hden : (s'.card : ENNReal) * vol ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hvoltop
  have hsmall : lam * ((s'.card : ENNReal) * vol) ≤ ∑ i ∈ s', volume (B' i).shade := by
    rcases eq_or_ne ((s'.card : ENNReal) * vol) 0 with hz | hz
    · rw [hz, mul_zero]; exact bot_le
    · have := hfull
      rw [fullness', hsum', ENNReal.le_div_iff_mul_le (Or.inl hz) (Or.inl hden)] at this
      exact this
  calc ∑ i ∈ s, volume (B i).shade
      ≤ (s.card : ENNReal) * vol := hbig
    _ ≤ (C * (s'.card : ENNReal)) * vol := by gcongr
    _ = (C / lam) * (lam * ((s'.card : ENNReal) * vol)) := by
        rw [← mul_assoc (C / lam) lam, ENNReal.div_mul_cancel hlam0 hlamtop, mul_assoc]
    _ ≤ (C / lam) * ∑ i ∈ s', volume (B' i).shade := by gcongr

/-! ### The shade-threshold refinement: where the fullness datum comes from -/

open Classical in
/-- **The shade-threshold refinement.**

A family of fullness at least `lam` (all carriers of the same volume `vol`) contains a subfamily
`s₀` on which *every* shading is at least `lam/2` of the carrier, and which retains a `lam/2`
fraction of the members: `#s ≤ (2/lam) · #s₀`.

The proof is a single cutoff, not a dyadic pigeonhole: the members below the threshold contribute
at most `(lam/2) · #s · vol`, i.e. at most half of the total shaded volume `lam · #s · vol` that
fullness guarantees, so the members above it carry the other half, and each of those carries at
most `vol`.

This is the structure the refinement of `ShadedTube.exists_shadedUniformTubeSet_subfamily_ssf`
does not itself supply, and it is what makes fullness *hereditary*: after the cutoff, every
further subfamily still has fullness at least `lam/2`
(`ShadedBody.le_fullness'_of_shade_band`), which is exactly the datum
`StickyKakeya.StickyKatzTaoEstimate` demands of the refined pair and the datum the multiplicity
transfer spends. -/
theorem exists_shade_threshold_subfamily {s : Finset ι} (B : ι → ShadedBody E)
    {vol : ENNReal} (hvol0 : vol ≠ 0) (hvoltop : vol ≠ ⊤)
    (hcar : ∀ i ∈ s, volume (B i).carrier = vol)
    {lam : ENNReal} (hlam0 : lam ≠ 0) (hlamtop : lam ≠ ⊤)
    (hfull : lam ≤ fullness' s B) :
    ∃ s₀ ⊆ s, (∀ i ∈ s₀, lam / 2 * vol ≤ volume (B i).shade) ∧
      (s.card : ENNReal) ≤ 2 / lam * (s₀.card : ENNReal) := by
  classical
  set s₀ := s.filter (fun i => lam / 2 * vol ≤ volume (B i).shade) with hs₀
  refine ⟨s₀, Finset.filter_subset _ _, fun i hi => (Finset.mem_filter.mp hi).2, ?_⟩
  have hsumcar : ∑ i ∈ s, volume (B i).carrier = (s.card : ENNReal) * vol := by
    rw [Finset.sum_congr rfl hcar, Finset.sum_const, nsmul_eq_mul]
  -- the fullness bound, cleared of the division
  have hlow : lam * ((s.card : ENNReal) * vol) ≤ ∑ i ∈ s, volume (B i).shade := by
    rcases eq_or_ne ((s.card : ENNReal) * vol) 0 with hz | hz
    · rw [hz, mul_zero]; exact bot_le
    · have h := hfull
      rw [fullness', hsumcar,
        ENNReal.le_div_iff_mul_le (Or.inl hz)
          (Or.inl (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hvoltop))] at h
      exact h
  -- split the sum at the threshold
  have hsplit : ∑ i ∈ s, volume (B i).shade
      ≤ (s₀.card : ENNReal) * vol + lam / 2 * ((s.card : ENNReal) * vol) := by
    have hpart : (∑ i ∈ s₀, volume (B i).shade) + ∑ i ∈ s \ s₀, volume (B i).shade
        = ∑ i ∈ s, volume (B i).shade := by
      rw [add_comm]
      exact Finset.sum_sdiff (Finset.filter_subset _ _)
    have hhi : ∑ i ∈ s₀, volume (B i).shade ≤ (s₀.card : ENNReal) * vol := by
      have : ∀ i ∈ s₀, volume (B i).shade ≤ vol := by
        intro i hi
        have his : i ∈ s := Finset.filter_subset _ _ hi
        rw [← hcar i his]
        exact measure_mono (B i).shade_subset
      calc ∑ i ∈ s₀, volume (B i).shade ≤ ∑ _i ∈ s₀, vol := Finset.sum_le_sum this
        _ = (s₀.card : ENNReal) * vol := by rw [Finset.sum_const, nsmul_eq_mul]
    have hlo : ∑ i ∈ s \ s₀, volume (B i).shade
        ≤ lam / 2 * ((s.card : ENNReal) * vol) := by
      have hbd : ∀ i ∈ s \ s₀, volume (B i).shade ≤ lam / 2 * vol := by
        intro i hi
        obtain ⟨his, hni⟩ := Finset.mem_sdiff.mp hi
        by_contra hcon
        exact hni (Finset.mem_filter.mpr ⟨his, (not_le.mp hcon).le⟩)
      calc ∑ i ∈ s \ s₀, volume (B i).shade ≤ ∑ _i ∈ s \ s₀, lam / 2 * vol :=
            Finset.sum_le_sum hbd
        _ = ((s \ s₀).card : ENNReal) * (lam / 2 * vol) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ((s.card : ENNReal)) * (lam / 2 * vol) := by
            gcongr
            exact Finset.sdiff_subset
        _ = lam / 2 * ((s.card : ENNReal) * vol) := by ring
    rw [← hpart]
    exact add_le_add hhi hlo
  -- absorb the half
  have hXfin : lam * ((s.card : ENNReal) * vol) ≠ ⊤ :=
    ENNReal.mul_ne_top hlamtop (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hvoltop)
  have hhalf : lam / 2 * ((s.card : ENNReal) * vol)
      = lam * ((s.card : ENNReal) * vol) / 2 := by
    rw [ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul]; ring
  have hstep : lam * ((s.card : ENNReal) * vol) / 2 ≤ (s₀.card : ENNReal) * vol := by
    have hchain : lam * ((s.card : ENNReal) * vol)
        ≤ (s₀.card : ENNReal) * vol + lam * ((s.card : ENNReal) * vol) / 2 := by
      rw [← hhalf]; exact hlow.trans hsplit
    have hfin2 : lam * ((s.card : ENNReal) * vol) / 2 ≠ ⊤ := by
      simp [ENNReal.div_eq_inv_mul, ENNReal.mul_ne_top, hXfin]
    have hchain2 : lam * ((s.card : ENNReal) * vol) / 2
        + lam * ((s.card : ENNReal) * vol) / 2
        ≤ (s₀.card : ENNReal) * vol + lam * ((s.card : ENNReal) * vol) / 2 := by
      rw [show lam * ((s.card : ENNReal) * vol) / 2 + lam * ((s.card : ENNReal) * vol) / 2
        = lam * ((s.card : ENNReal) * vol) from ENNReal.add_halves _]
      exact hchain
    exact (ENNReal.add_le_add_iff_right hfin2).mp hchain2
  -- cancel `vol` and clear `lam`
  have hcancel : lam / 2 * (s.card : ENNReal) ≤ (s₀.card : ENNReal) := by
    have h := hstep
    rw [← hhalf] at h
    have h' : lam / 2 * (s.card : ENNReal) * vol ≤ (s₀.card : ENNReal) * vol := by
      calc lam / 2 * (s.card : ENNReal) * vol
          = lam / 2 * ((s.card : ENNReal) * vol) := by ring
        _ ≤ (s₀.card : ENNReal) * vol := h
    exact (ENNReal.mul_le_mul_iff_left hvol0 hvoltop).mp h'
  have hkey : (2 : ENNReal) / lam * (lam / 2) = 1 := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    calc (2 : ENNReal) * lam⁻¹ * (lam * 2⁻¹) = (2 * 2⁻¹) * (lam⁻¹ * lam) := by ring
      _ = 1 := by
          rw [ENNReal.mul_inv_cancel (by norm_num) (by norm_num),
            ENNReal.inv_mul_cancel hlam0 hlamtop, one_mul]
  calc (s.card : ENNReal) = (2 / lam * (lam / 2)) * (s.card : ENNReal) := by rw [hkey, one_mul]
    _ = 2 / lam * (lam / 2 * (s.card : ENNReal)) := by ring
    _ ≤ 2 / lam * (s₀.card : ENNReal) := by gcongr

/-- **A uniform shade lower bound makes fullness hereditary.**

If every member of `s'` has shading at least `c` times its carrier volume, and all carriers have
the same volume, then `c ≤ λ(s', Y)` — for *every* nonempty `s'` with that property, in
particular for every nonempty subfamily of the family produced by
`ShadedBody.exists_shade_threshold_subfamily`.  This is the property that the plain average
`ShadedBody.fullness'` does not have: without a pointwise lower bound, a subfamily of a full
family can be arbitrarily empty of shading. -/
theorem le_fullness'_of_shade_band {s' : Finset ι} (B : ι → ShadedBody E)
    {vol c : ENNReal} (hvol0 : vol ≠ 0) (hvoltop : vol ≠ ⊤) (hne : s'.Nonempty)
    (hcar : ∀ i ∈ s', volume (B i).carrier = vol)
    (hband : ∀ i ∈ s', c * vol ≤ volume (B i).shade) :
    c ≤ fullness' s' B := by
  have hsumcar : ∑ i ∈ s', volume (B i).carrier = (s'.card : ENNReal) * vol := by
    rw [Finset.sum_congr rfl hcar, Finset.sum_const, nsmul_eq_mul]
  have hcard0 : (s'.card : ENNReal) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero, Finset.card_eq_zero]
    exact Finset.nonempty_iff_ne_empty.mp hne
  have hz : (s'.card : ENNReal) * vol ≠ 0 := mul_ne_zero hcard0 hvol0
  have hntop : (s'.card : ENNReal) * vol ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hvoltop
  rw [fullness', hsumcar, ENNReal.le_div_iff_mul_le (Or.inl hz) (Or.inl hntop)]
  calc c * ((s'.card : ENNReal) * vol) = ∑ _i ∈ s', c * vol := by
        rw [Finset.sum_const, nsmul_eq_mul]; ring
    _ ≤ ∑ i ∈ s', volume (B i).shade := Finset.sum_le_sum hband

end ShadedBody

end

end
