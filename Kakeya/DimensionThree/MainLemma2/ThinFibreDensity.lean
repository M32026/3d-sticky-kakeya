/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.ThinFullness
public import Kakeya.DimensionThree.MainLemma2.ThinEccentricity
public import Kakeya.CThickening
public import Kakeya.Pigeonhole

/-!
# Conjunct (i) of the thin-case factoring step without per-block retention

`Kakeya.ThinCase.fullness_ge_three_eta` (`ThinFullness.lean`) proves conjunct (i) of
`Kakeya.ThinCase.factoringApply` from a **per-fibre** mass retention `hret`, and the only producer
of that hypothesis, `Kakeya.ThinCase.exists_denseBodies`, discards bodies — which the cell route of
`Kakeya.ThinCase.exists_factoringApplyData` cannot afford after its cell band has been computed.

This file follows GWZ's own Item 2 accounting (proof of Proposition 5.1, the dyadic classes
`𝒲'_τ`), which **discards nothing**: the Córdoba estimate is applied on every fibre with its own
density parameter `λ_j = m'_j / v_j`, and the resulting per-fibre bounds are summed with a
Cauchy–Schwarz (Sedrakyan) step against the *global* retention. The one hypothesis this needs
beyond `factoringApply`'s own binders is that the fibre carrier densities `ρ_j = v_j / w_j`
(`v_j` the total carrier mass of the fibre, `w_j = |N_{τ₂(W_j)}(W_j)|` the volume of the enlarged
body) are pairwise comparable — GWZ's "`|V'_W|` approximately constant" — which a mass-weighted
dyadic pigeonhole supplies **before** the cell construction, where discarding bodies is harmless.

* `Kakeya.ThinCase.exists_densityBand` — the abstract mass-weighted dyadic pigeonhole on a ratio
  `v j / w j`, a wrapper of `ENNReal.dyadic_pigeonhole₁'` returning the pairwise band in
  division-free form, the `[ρ, 2ρ]` form, and the loss `1 + log₂ (range)`.
* `Kakeya.ThinCase.fibreCarrierMass_le_bodyVolume` and
  `Kakeya.ThinCase.bodyVolume_le_fibreCarrierMass` — the two-sided comparison
  `(C_vol · C_F)⁻¹ · w_j ≤ v_j ≤ |segs| · w_j`, from `hle`, `hFr` and the carrier
  non-degeneracy; `Kakeya.ThinCase.bodyVolume_le_fibreCarrierMass_of_exponent` is the same lower
  bound read through an eccentricity exponent `N` (the shape of
  `ShadedBody.OuterInnerVolumeRatio.exponent`).
* `Kakeya.ThinCase.exists_fibreDensityBand` — the two combined: the retained bodies have pairwise
  comparable fibre densities, at the loss `Kakeya.ThinCase.fibreDensityBandLoss`.
* `Kakeya.ThinCase.weighted_cauchySchwarz_accounting` — the real-arithmetic core of GWZ's Item 2
  summation.
* `Kakeya.ThinCase.fullness_inducedShading_ge_of_globalRetention` — conjunct (i) at the exponent
  **`2 η`** for the induced-shading family, from `hdens`, the global retention `hret`, the fibre
  density band and the aggregate Córdoba estimate
  `ShadedBody.aggregateFullnessForInducedShading_of_measurable`. Its constant
  `Kakeya.ThinCase.thinFibreDensityConstant` is `4 · C_F · C_full² · C_Córdoba · (N + 1) / θ²`.

Nothing here restricts the segment family or discards a body: every hypothesis is a binder of
`factoringApply`, a side condition of the Córdoba estimate (`hne`, `hVpos`, `hecc`), the global
retention (vi), or the band. The exponent is `2 η` because `hdens` is used per segment and the
Frostman constant of the *original* fibres is what the Córdoba estimate sees — the `δ^{-η}` that
`fullness_ge_three_eta` pays to transport Frostman to a subfibre never arises.
-/

@[expose] public section

open MeasureTheory Metric Set ShadedBody Convexity
open scoped ENNReal NNReal

namespace Kakeya.ThinCase

/-! ### The abstract density band -/

section DensityBand

/-- **Mass-weighted dyadic pigeonhole on a ratio.** Given weights `μ`, numerators `v` and positive
finite denominators `w` on a finite index set, with every ratio `v j / w j` in `[a, b]`, there is a
sub-index-set carrying a `(1 + log₂ (b / a))⁻¹` fraction of the weight on which the ratios are
pairwise comparable by `2` — stated division-free — and lie in a single dyadic band `[ρ, 2 ρ]`. -/
theorem exists_densityBand {κ : Type*} (bodies : Finset κ) (v w μ : κ → ENNReal) {a b : ℝ}
    (ha : 0 < a)
    (hw0 : ∀ j ∈ bodies, w j ≠ 0) (hwtop : ∀ j ∈ bodies, w j ≠ ⊤)
    (hband : ∀ j ∈ bodies, ENNReal.ofReal a ≤ v j / w j ∧ v j / w j ≤ ENNReal.ofReal b) :
    ∃ bodies' ⊆ bodies,
      (∀ j ∈ bodies', ∀ k ∈ bodies', v j * w k ≤ 2 * (v k * w j)) ∧
      (∃ ρ : ENNReal, ∀ j ∈ bodies', ρ ≤ v j / w j ∧ v j / w j ≤ 2 * ρ) ∧
      ∑ j ∈ bodies, μ j ≤ ENNReal.ofReal (1 + Real.logb 2 (b / a)) * ∑ j ∈ bodies', μ j := by
  classical
  obtain ⟨t, hts, hmass, hcomp⟩ :=
    ENNReal.dyadic_pigeonhole₁' bodies μ (fun j => v j / w j) ha (fun j hj => hband j hj)
  refine ⟨t, hts, ?_, ?_, hmass⟩
  · intro j hj k hk
    have h : v j / w j ≤ 2 * (v k / w k) := hcomp j hj k hk
    have hwj0 := hw0 j (hts hj)
    have hwjt := hwtop j (hts hj)
    have hwk0 := hw0 k (hts hk)
    have hwkt := hwtop k (hts hk)
    calc v j * w k = v j / w j * (w j * w k) := by
          rw [← mul_assoc, ENNReal.div_mul_cancel hwj0 hwjt]
      _ ≤ 2 * (v k / w k) * (w j * w k) := by gcongr
      _ = 2 * (v k * w j) := by
          rw [mul_comm (w j) (w k), mul_assoc, ← mul_assoc (v k / w k),
            ENNReal.div_mul_cancel hwk0 hwkt]
  · rcases t.eq_empty_or_nonempty with ht | ht
    · exact ⟨0, by simp [ht]⟩
    obtain ⟨j₀, hj₀, hmin⟩ := Finset.exists_min_image t (fun j => v j / w j) ht
    exact ⟨v j₀ / w j₀, fun j hj => ⟨hmin j hj, hcomp j hj j₀ hj₀⟩⟩

end DensityBand

/-! ### The two-sided comparison of the fibre carrier mass with the body volume -/

section CarrierMass

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **Upper bound.** Every segment of a fibre lies in its body, which lies in its own
enlargement, so the fibre carrier mass is at most `|segs|` times the enlarged body volume. -/
theorem fibreCarrierMass_le_bodyVolume {ι κ : Type*} [DecidableEq κ] (segs : Finset ι)
    (Y : ι → ShadedBody E)
    (Wb : κ → ConvexSpaceBody E) (blk : ι → κ)
    (hle : ∀ p ∈ segs, (Y p).toConvexSpaceBody ≤ Wb (blk p)) (j : κ) :
    ∑ p ∈ {p ∈ segs | blk p = j}, volume (Y p).carrier ≤
      (segs.card : ENNReal) * volume ((Wb j).cthickening (Wb j).scale).carrier := by
  classical
  have hper : ∀ p ∈ {p ∈ segs | blk p = j},
      volume (Y p).carrier ≤ volume ((Wb j).cthickening (Wb j).scale).carrier := by
    intro p hp
    obtain ⟨hps, hpj⟩ := Finset.mem_filter.mp hp
    have h1 : (Y p).carrier ⊆ (Wb (blk p)).carrier := hle p hps
    have h2 : (Wb j).carrier ⊆ ((Wb j).cthickening (Wb j).scale).carrier :=
      Metric.self_subset_cthickening _
    rw [hpj] at h1
    exact measure_mono (h1.trans h2)
  calc ∑ p ∈ {p ∈ segs | blk p = j}, volume (Y p).carrier
      ≤ ∑ _p ∈ {p ∈ segs | blk p = j}, volume ((Wb j).cthickening (Wb j).scale).carrier :=
        Finset.sum_le_sum hper
    _ = (({p ∈ segs | blk p = j}).card : ENNReal) *
          volume ((Wb j).cthickening (Wb j).scale).carrier := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (segs.card : ENNReal) * volume ((Wb j).cthickening (Wb j).scale).carrier := by
        gcongr
        exact Finset.filter_subset _ _

/-- **Lower bound.** The enlargement at the body's own scale inflates the volume by at most the
dimensional constant `Metric.volume_comparison.C n`, and the Frostman property of the fibre bounds
the body volume by `C_F` times the fibre carrier mass
(`Kakeya.ThinCase.Produce.volume_carrier_le_of_isFrostmanIn`). -/
theorem bodyVolume_le_fibreCarrierMass [Nontrivial E] {ι κ : Type*} [DecidableEq κ]
    (segs : Finset ι) (Y : ι → ShadedBody E)
    (Wb : κ → ConvexSpaceBody E) (blk : ι → κ) {CF : ENNReal}
    (hle : ∀ p ∈ segs, (Y p).toConvexSpaceBody ≤ Wb (blk p))
    (hVpos : ∀ p ∈ segs, volume (Y p).carrier ≠ 0) (j : κ)
    (hFr : ConvexSpaceBody.IsFrostmanIn {p ∈ segs | blk p = j}
      (fun p => (Y p).toConvexSpaceBody) (Wb j) CF)
    (hne : ({p ∈ segs | blk p = j}).Nonempty) :
    volume ((Wb j).cthickening (Wb j).scale).carrier ≤
      (Metric.volume_comparison.C (Module.finrank ℝ E) : ENNReal) * CF *
        ∑ p ∈ {p ∈ segs | blk p = j}, volume (Y p).carrier := by
  classical
  obtain ⟨p, hp⟩ := hne
  have hVK : ∀ i ∈ {p ∈ segs | blk p = j}, (Y i).toConvexSpaceBody ≤ Wb j := by
    intro i hi
    obtain ⟨his, hij⟩ := Finset.mem_filter.mp hi
    rw [← hij]
    exact hle i his
  have h1 := Produce.volume_carrier_le_of_isFrostmanIn hFr hVK hp
    (hVpos p (Finset.mem_filter.mp hp).1)
  have hsc : (0 : ℝ) ≤ (Wb j).scale := Metric.thickness_nonneg _ _
  have h2 := ConvexSpaceBody.volume_cthickening_le (Wb j) ⟨(Wb j).scale, hsc⟩ le_rfl
  calc volume ((Wb j).cthickening (Wb j).scale).carrier
      ≤ (Metric.volume_comparison.C (Module.finrank ℝ E) : ENNReal) *
          volume (Wb j).carrier := h2
    _ ≤ (Metric.volume_comparison.C (Module.finrank ℝ E) : ENNReal) *
          (CF * ∑ p ∈ {p ∈ segs | blk p = j}, volume (Y p).carrier) := by gcongr
    _ = _ := by ring

/-- The lower bound read through an eccentricity exponent `N` with
`|W_j| ≤ 2 ^ N · |V_p|` for every `p` in the fibre (the shape of
`ShadedBody.OuterInnerVolumeRatio.exponent`, supplied for the thin family by
`Kakeya.ThinCase.thinVolumeRatio`). -/
theorem bodyVolume_le_fibreCarrierMass_of_exponent [Nontrivial E] {ι κ : Type*} [DecidableEq κ]
    (segs : Finset ι)
    (Y : ι → ShadedBody E) (Wb : κ → ConvexSpaceBody E) (blk : ι → κ) {N : ℕ} (j : κ)
    (hecc : ∀ p ∈ {p ∈ segs | blk p = j},
      volume (Wb j).carrier ≤ 2 ^ N * volume (Y p).carrier)
    (hne : ({p ∈ segs | blk p = j}).Nonempty) :
    volume ((Wb j).cthickening (Wb j).scale).carrier ≤
      (Metric.volume_comparison.C (Module.finrank ℝ E) : ENNReal) * 2 ^ N *
        ∑ p ∈ {p ∈ segs | blk p = j}, volume (Y p).carrier := by
  classical
  obtain ⟨p, hp⟩ := hne
  have hsc : (0 : ℝ) ≤ (Wb j).scale := Metric.thickness_nonneg _ _
  have h2 := ConvexSpaceBody.volume_cthickening_le (Wb j) ⟨(Wb j).scale, hsc⟩ le_rfl
  have hsingle : volume (Y p).carrier ≤ ∑ q ∈ {p ∈ segs | blk p = j}, volume (Y q).carrier :=
    Finset.single_le_sum (f := fun q => volume (Y q).carrier) (fun _ _ => zero_le) hp
  calc volume ((Wb j).cthickening (Wb j).scale).carrier
      ≤ (Metric.volume_comparison.C (Module.finrank ℝ E) : ENNReal) *
          volume (Wb j).carrier := h2
    _ ≤ (Metric.volume_comparison.C (Module.finrank ℝ E) : ENNReal) *
          (2 ^ N * ∑ q ∈ {p ∈ segs | blk p = j}, volume (Y q).carrier) := by
        gcongr
        exact (hecc p hp).trans (by gcongr)
    _ = _ := by ring

/-- The enlarged body volume is positive as soon as the fibre has one segment of positive
carrier volume. -/
theorem bodyVolume_ne_zero_of_fibre {ι κ : Type*} [DecidableEq κ] (segs : Finset ι)
    (Y : ι → ShadedBody E)
    (Wb : κ → ConvexSpaceBody E) (blk : ι → κ)
    (hle : ∀ p ∈ segs, (Y p).toConvexSpaceBody ≤ Wb (blk p))
    (hVpos : ∀ p ∈ segs, volume (Y p).carrier ≠ 0) (j : κ)
    (hne : ({p ∈ segs | blk p = j}).Nonempty) :
    volume ((Wb j).cthickening (Wb j).scale).carrier ≠ 0 := by
  classical
  obtain ⟨p, hp⟩ := hne
  obtain ⟨hps, hpj⟩ := Finset.mem_filter.mp hp
  have h1 : (Y p).carrier ⊆ (Wb (blk p)).carrier := hle p hps
  have h2 : (Wb j).carrier ⊆ ((Wb j).cthickening (Wb j).scale).carrier :=
    Metric.self_subset_cthickening _
  rw [hpj] at h1
  have : volume (Y p).carrier ≤ volume ((Wb j).cthickening (Wb j).scale).carrier :=
    measure_mono (h1.trans h2)
  intro h0
  exact hVpos p hps (le_antisymm (h0 ▸ this) zero_le)

/-- **The loss of the fibre-density band**: `1 + log₂ (|segs| · C_vol · C_F)`, the logarithm of
the range `[(C_vol · C_F)⁻¹, |segs|]` of the fibre carrier densities. -/
noncomputable def fibreDensityBandLoss (n : ℕ) (CF : NNReal) (m : ℕ) : ENNReal :=
  ENNReal.ofReal (1 + Real.logb 2 ((m : ℝ) * ((Metric.volume_comparison.C n * CF : NNReal) : ℝ)))

/-- **The fibre-density band for the thin family.** A mass-weighted dyadic pigeonhole over the
bodies, with an arbitrary weight `μ`, retains a sub-family of bodies whose fibre carrier
densities `v_j / w_j` are pairwise comparable by `2` — in the division-free form `v_j · w_k ≤ 2 ·
v_k · w_j` that `Kakeya.ThinCase.fullness_inducedShading_ge_of_globalRetention` consumes, and in
the band form `ρ ≤ v_j / w_j ≤ 2 ρ` — at the loss `Kakeya.ThinCase.fibreDensityBandLoss`.

Here `v_j = ∑_{p ∈ fibre j} |V_p|` and `w_j = |N_{τ₂(W_j)}(W_j)|`. Nothing is assumed about the
shadings: the band is a statement about carriers only, so it may be run before or after any
refinement of the shading. -/
theorem exists_fibreDensityBand [Nontrivial E] {ι κ : Type*} [DecidableEq κ] (segs : Finset ι)
    (Y : ι → ShadedBody E)
    (bodies : Finset κ) (Wb : κ → ConvexSpaceBody E) (blk : ι → κ) {CF : NNReal}
    (hCF : 0 < CF)
    (hle : ∀ p ∈ segs, (Y p).toConvexSpaceBody ≤ Wb (blk p))
    (hFr : ∀ j ∈ bodies, ConvexSpaceBody.IsFrostmanIn {p ∈ segs | blk p = j}
      (fun p => (Y p).toConvexSpaceBody) (Wb j) (CF : ENNReal))
    (hVpos : ∀ p ∈ segs, volume (Y p).carrier ≠ 0)
    (hne : ∀ j ∈ bodies, ({p ∈ segs | blk p = j}).Nonempty)
    (μ : κ → ENNReal) :
    ∃ bodies' ⊆ bodies,
      (∀ j ∈ bodies', ∀ k ∈ bodies',
        (∑ p ∈ {p ∈ segs | blk p = j}, volume (Y p).carrier) *
            volume ((Wb k).cthickening (Wb k).scale).carrier ≤
          2 * ((∑ p ∈ {p ∈ segs | blk p = k}, volume (Y p).carrier) *
            volume ((Wb j).cthickening (Wb j).scale).carrier)) ∧
      (∃ ρ : ENNReal, ∀ j ∈ bodies',
        ρ ≤ (∑ p ∈ {p ∈ segs | blk p = j}, volume (Y p).carrier) /
            volume ((Wb j).cthickening (Wb j).scale).carrier ∧
          (∑ p ∈ {p ∈ segs | blk p = j}, volume (Y p).carrier) /
            volume ((Wb j).cthickening (Wb j).scale).carrier ≤ 2 * ρ) ∧
      ∑ j ∈ bodies, μ j ≤
        fibreDensityBandLoss (Module.finrank ℝ E) CF segs.card * ∑ j ∈ bodies', μ j := by
  classical
  set v : κ → ENNReal := fun j => ∑ p ∈ {p ∈ segs | blk p = j}, volume (Y p).carrier with hv
  set w : κ → ENNReal := fun j => volume ((Wb j).cthickening (Wb j).scale).carrier with hw
  set c : NNReal := Metric.volume_comparison.C (Module.finrank ℝ E) * CF with hc
  have hcpos : 0 < c := mul_pos (Metric.volume_comparison.C_pos _) hCF
  have hcR : (0 : ℝ) < (c : ℝ) := by exact_mod_cast hcpos
  have hw0 : ∀ j ∈ bodies, w j ≠ 0 := fun j hj =>
    bodyVolume_ne_zero_of_fibre segs Y Wb blk hle hVpos j (hne j hj)
  have hwtop : ∀ j ∈ bodies, w j ≠ ⊤ := fun j _ =>
    ((Wb j).cthickening (Wb j).scale).isCompact.measure_ne_top
  have hband : ∀ j ∈ bodies,
      ENNReal.ofReal ((c : ℝ)⁻¹) ≤ v j / w j ∧ v j / w j ≤ ENNReal.ofReal (segs.card : ℝ) := by
    intro j hj
    constructor
    · have hlow := bodyVolume_le_fibreCarrierMass segs Y Wb blk hle hVpos j (hFr j hj) (hne j hj)
      rw [ENNReal.ofReal_inv_of_pos hcR, ENNReal.ofReal_coe_nnreal,
        ENNReal.le_div_iff_mul_le (Or.inl (hw0 j hj)) (Or.inl (hwtop j hj)),
        ENNReal.inv_mul_le_iff (by exact_mod_cast hcpos.ne') ENNReal.coe_ne_top]
      simpa [hc, hv, hw, ENNReal.coe_mul] using hlow
    · have hup := fibreCarrierMass_le_bodyVolume segs Y Wb blk hle j
      rw [ENNReal.ofReal_natCast]
      exact ENNReal.div_le_of_le_mul hup
  obtain ⟨bodies', hsub, hpair, hρ, hmass⟩ :=
    exists_densityBand bodies v w μ (inv_pos.mpr hcR) hw0 hwtop hband
  refine ⟨bodies', hsub, hpair, hρ, ?_⟩
  have hloss : ENNReal.ofReal (1 + Real.logb 2 ((segs.card : ℝ) / (c : ℝ)⁻¹)) =
      fibreDensityBandLoss (Module.finrank ℝ E) CF segs.card := by
    rw [fibreDensityBandLoss, div_inv_eq_mul]
  rw [← hloss]
  exact hmass

end CarrierMass

/-! ### The Cauchy–Schwarz accounting -/

section Accounting

/-- **GWZ's Item 2 summation, in `ℝ`.** With `V_j, W_j > 0` pairwise comparable in ratio
(`V_j · W_k ≤ 2 · V_k · W_j`) and a global lower bound `c · ∑ V_j ≤ ∑ M_j`, the Córdoba weights
`(M_j / V_j)² · W_j` sum to at least `c² / 4` times `∑ W_j`. The proof is Sedrakyan's inequality
`(∑ M_j)² / ∑ V_j ≤ ∑ M_j² / V_j` (`Finset.sq_sum_div_le_sum_sq_div`) between the two uses of the
band. -/
theorem weighted_cauchySchwarz_accounting {κ : Type*} (s : Finset κ) (hs : s.Nonempty)
    (V W M : κ → ℝ) (hV : ∀ j ∈ s, 0 < V j) (hW : ∀ j ∈ s, 0 < W j)
    (hband : ∀ j ∈ s, ∀ k ∈ s, V j * W k ≤ 2 * (V k * W j))
    {c : ℝ} (hc : 0 ≤ c) (hlow : c * ∑ j ∈ s, V j ≤ ∑ j ∈ s, M j) :
    c ^ 2 * ∑ j ∈ s, W j ≤ 4 * ∑ j ∈ s, (M j / V j) ^ 2 * W j := by
  obtain ⟨j₀, hj₀⟩ := hs
  have hV₀ := hV j₀ hj₀
  have hW₀ := hW j₀ hj₀
  set r : ℝ := W j₀ / V j₀ with hr
  have hr_pos : 0 < r := div_pos hW₀ hV₀
  -- the two halves of the band, against the reference body `j₀`
  have h1 : ∀ j ∈ s, r * V j ≤ 2 * W j := by
    intro j hj
    have hb := hband j hj j₀ hj₀
    rw [hr, div_mul_eq_mul_div, div_le_iff₀ hV₀]
    linarith
  have h2 : ∀ j ∈ s, W j ≤ 2 * r * V j := by
    intro j hj
    have hb := hband j₀ hj₀ j hj
    calc W j = V j₀ * W j / V j₀ := (mul_div_cancel_left₀ (W j) hV₀.ne').symm
      _ ≤ 2 * (V j * W j₀) / V j₀ := by gcongr
      _ = 2 * r * V j := by rw [hr]; ring
  -- Sedrakyan
  have hsed : (∑ j ∈ s, M j) ^ 2 / ∑ j ∈ s, V j ≤ ∑ j ∈ s, (M j) ^ 2 / V j :=
    Finset.sq_sum_div_le_sum_sq_div s M hV
  have hsumV : 0 < ∑ j ∈ s, V j := Finset.sum_pos hV ⟨j₀, hj₀⟩
  -- the Córdoba weights dominate `(r / 2) · ∑ M_j² / V_j`
  have h3 : (r / 2) * ∑ j ∈ s, (M j) ^ 2 / V j ≤ ∑ j ∈ s, (M j / V j) ^ 2 * W j := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j hj => ?_
    have hVj := hV j hj
    have hrew : (M j / V j) ^ 2 * W j = (M j) ^ 2 / V j * (W j / V j) := by
      ring
    rw [hrew]
    have hnn : 0 ≤ (M j) ^ 2 / V j := div_nonneg (sq_nonneg _) hVj.le
    have hhalf : r / 2 ≤ W j / V j := by
      rw [le_div_iff₀ hVj]
      linarith [h1 j hj]
    calc r / 2 * ((M j) ^ 2 / V j) = (M j) ^ 2 / V j * (r / 2) := by ring
      _ ≤ (M j) ^ 2 / V j * (W j / V j) := by gcongr
  -- the global lower bound, squared
  have h4 : c ^ 2 * ∑ j ∈ s, V j ≤ (∑ j ∈ s, M j) ^ 2 / ∑ j ∈ s, V j := by
    rw [le_div_iff₀ hsumV]
    have hsq : (c * ∑ j ∈ s, V j) ^ 2 ≤ (∑ j ∈ s, M j) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hlow 2
    calc (c ^ 2 * ∑ j ∈ s, V j) * ∑ j ∈ s, V j = (c * ∑ j ∈ s, V j) ^ 2 := by ring
      _ ≤ (∑ j ∈ s, M j) ^ 2 := hsq
  -- the total carrier mass dominates the total enlarged volume
  have h5 : ∑ j ∈ s, W j ≤ 2 * r * ∑ j ∈ s, V j := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum h2
  calc c ^ 2 * ∑ j ∈ s, W j ≤ c ^ 2 * (2 * r * ∑ j ∈ s, V j) := by gcongr
    _ = 4 * ((r / 2) * (c ^ 2 * ∑ j ∈ s, V j)) := by ring
    _ ≤ 4 * ((r / 2) * ((∑ j ∈ s, M j) ^ 2 / ∑ j ∈ s, V j)) := by gcongr
    _ ≤ 4 * ((r / 2) * ∑ j ∈ s, (M j) ^ 2 / V j) := by gcongr
    _ ≤ 4 * ∑ j ∈ s, (M j / V j) ^ 2 * W j := by gcongr

end Accounting

/-! ### Conjunct (i) at the exponent `2 η`, without per-block retention -/

section Fullness

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **The output constant of conjunct (i) at the exponent `2 η`**:
`4 · C_F · C_full² · C_Córdoba · (N + 1) / θ²`, with `θ` the global retention and `N` the
eccentricity exponent. -/
noncomputable def thinFibreDensityConstant (CF Cfull θ : NNReal) (N : ℕ) : NNReal :=
  4 * CF * Cfull ^ 2 * ShadedBody.lambdaInducedSingleWUniform.C * (N + 1) / θ ^ 2

/-- **Conjunct (i) of `Kakeya.ThinCase.factoringApply` at the exponent `2 η`, from the global
retention.**

Every hypothesis is a binder of `factoringApply` (`hcar`, `hblk`, `hle`, `hdims`, `hFr`, `hdens`,
`hδ`, `hCF`), a side condition of the Córdoba estimate (`hVpos`, `hne`, `hecc`, `hbne`), the
**global** shade-mass retention `hret` (conjunct (vi), not the per-fibre form of
`Kakeya.ThinCase.fullness_ge_three_eta`), or the fibre-density band `hρ` produced by
`Kakeya.ThinCase.exists_fibreDensityBand`. No body is discarded and no segment is dropped.

The proof is GWZ's Item 2: `ShadedBody.aggregateFullnessForInducedShading_of_measurable` on every
fibre with its own density `λ_j = m'_j / v_j`, then
`Kakeya.ThinCase.weighted_cauchySchwarz_accounting` with `c = θ δ^η / C_full`. -/
theorem fullness_inducedShading_ge_of_globalRetention [Nontrivial E] {ι κ : Type*}
    [DecidableEq κ]
    (hdim : Module.finrank ℝ E = 3)
    (segs : Finset ι) (Y Y' : ι → ShadedBody E)
    (bodies : Finset κ) (Wb : κ → ConvexSpaceBody E) (blk : ι → κ)
    {δ θ CF Cfull : NNReal} {η : ℝ} {N : ℕ}
    (hδ : 0 < δ) (hθ : 0 < θ) (hCF : 0 < CF) (hCfull : 0 < Cfull)
    (hbne : bodies.Nonempty)
    (hcar : ∀ p ∈ segs, (Y' p).toConvexSpaceBody = (Y p).toConvexSpaceBody)
    (hblk : ∀ p ∈ segs, blk p ∈ bodies)
    (hle : ∀ p ∈ segs, (Y p).toConvexSpaceBody ≤ Wb (blk p))
    (hdims : ∀ p ∈ segs, ∀ q ∈ segs,
      Metric.thickness ℝ (Y p).carrier ≤ 2 • Metric.thickness ℝ (Y q).carrier)
    (hFr : ∀ j ∈ bodies, ConvexSpaceBody.IsFrostmanIn {p ∈ segs | blk p = j}
      (fun p => (Y p).toConvexSpaceBody) (Wb j) (CF : ENNReal))
    (hdens : ∀ p ∈ segs,
      (δ : ENNReal) ^ η * volume (Y p).carrier ≤ (Cfull : ENNReal) * volume (Y p).shade)
    (hVpos : ∀ p ∈ segs, volume (Y p).carrier ≠ 0)
    (hne : ∀ j ∈ bodies, ({p ∈ segs | blk p = j}).Nonempty)
    (hecc : ∀ j ∈ bodies, ∀ p ∈ {p ∈ segs | blk p = j},
      volume (Wb j).carrier ≤ 2 ^ N * volume (Y p).carrier)
    (hret : (θ : ENNReal) * ∑ p ∈ segs, volume (Y p).shade ≤ ∑ p ∈ segs, volume (Y' p).shade)
    (hρ : ∀ j ∈ bodies, ∀ k ∈ bodies,
      (∑ p ∈ {p ∈ segs | blk p = j}, volume (Y p).carrier) *
          volume ((Wb k).cthickening (Wb k).scale).carrier ≤
        2 * ((∑ p ∈ {p ∈ segs | blk p = k}, volume (Y p).carrier) *
          volume ((Wb j).cthickening (Wb j).scale).carrier)) :
    (δ : ENNReal) ^ (2 * η) ≤ (thinFibreDensityConstant CF Cfull θ N : ENNReal) *
      (ShadedBody.fullness bodies (fun j => ShadedBody.inducedShading
        {p ∈ segs | blk p = j} Y' (Wb j)) : ENNReal) := by
  classical
  -- the fibres and the per-body quantities
  set fib : κ → Finset ι := fun j => {p ∈ segs | blk p = j} with hfib
  set v : κ → ENNReal := fun j => ∑ p ∈ fib j, volume (Y p).carrier with hv
  set m : κ → ENNReal := fun j => ∑ p ∈ fib j, volume (Y p).shade with hm
  set m' : κ → ENNReal := fun j => ∑ p ∈ fib j, volume (Y' p).shade with hm'
  set w : κ → ENNReal := fun j => volume ((Wb j).cthickening (Wb j).scale).carrier with hw
  set Wind : κ → ShadedBody E := fun j => ShadedBody.inducedShading (fib j) Y' (Wb j) with hWind
  set sh : κ → ENNReal := fun j => volume (Wind j).shade with hsh
  set lam : κ → ENNReal := fun j => m' j / v j with hlam
  set L : ENNReal :=
    (ShadedBody.lambdaInducedSingleWUniform.C : ENNReal) * ((N : ENNReal) + 1) with hL
  have hfibsub : ∀ j, fib j ⊆ segs := fun j => Finset.filter_subset _ _
  have hcarY : ∀ p ∈ segs, volume (Y' p).carrier = volume (Y p).carrier := fun p hp =>
    congrArg (fun K : ConvexSpaceBody E => volume K.carrier) (hcar p hp)
  -- finiteness and positivity of the per-body quantities
  have hvtop : ∀ j, v j ≠ ⊤ := fun j =>
    (ENNReal.sum_lt_top.mpr fun p _ => (Y p).isCompact'.measure_lt_top).ne
  have hv0 : ∀ j ∈ bodies, v j ≠ 0 := by
    intro j hj
    obtain ⟨p, hp⟩ := hne j hj
    have hsingle : volume (Y p).carrier ≤ v j :=
      Finset.single_le_sum (f := fun p => volume (Y p).carrier) (fun _ _ => zero_le) hp
    intro h0
    exact hVpos p (hfibsub j hp) (le_antisymm (h0 ▸ hsingle) zero_le)
  have hwtop : ∀ j, w j ≠ ⊤ := fun j =>
    ((Wb j).cthickening (Wb j).scale).isCompact.measure_ne_top
  have hw0 : ∀ j ∈ bodies, w j ≠ 0 := fun j hj =>
    bodyVolume_ne_zero_of_fibre segs Y Wb blk hle hVpos j (hne j hj)
  have hm'top : ∀ j, m' j ≠ ⊤ := fun j => sum_volume_shade_finite _ _
  have hmtop : ∀ j, m j ≠ ⊤ := fun j => sum_volume_shade_finite _ _
  have hshtop : ∀ j, sh j ≠ ⊤ := fun j =>
    (lt_of_le_of_lt (measure_mono (Wind j).shade_subset) (Wind j).isCompact'.measure_lt_top).ne
  -- the factor family fed to the Córdoba estimate
  let F : ShadedBody.FactorFamily E ι κ :=
    { innerSet := segs
      innerBody := Y'
      outerSet := bodies
      outerBody := Wb
      parent := blk
      parent_mem := hblk
      inner_le_parent := fun i hi => by rw [hcar i hi]; exact hle i hi }
  have hfiber : ∀ j, F.fiber j = fib j := by
    intro j
    ext p
    simp [ShadedBody.FactorFamily.fiber, F, hfib]
  have hshape : F.InnerHasSimilarShape 2 := by
    intro i hi i' hi' k
    have h := hdims i hi i' hi' k
    have hci : (Y' i).carrier = (Y i).carrier := congrArg ConvexSpaceBody.carrier (hcar i hi)
    have hci' : (Y' i').carrier = (Y i').carrier :=
      congrArg ConvexSpaceBody.carrier (hcar i' hi')
    change Metric.thickness ℝ (Y' i).carrier k ≤
      ((2 : NNReal) : ℝ) • Metric.thickness ℝ (Y' i').carrier k
    rw [hci, hci']
    simpa [Pi.smul_apply, nsmul_eq_mul, smul_eq_mul] using h
  have hFrostman : F.HasFrostmanFibers (CF : ENNReal) := by
    intro j hj
    rw [hfiber j]
    exact isFrostmanIn_congr_of_eqOn (fun p hp => (hcar p (hfibsub j hp)).symm) (hFr j hj)
  have hne' : ∀ j ∈ F.outerSet, (F.fiber j).Nonempty := fun j hj => by
    rw [hfiber j]; exact hne j hj
  have hVpos' : ∀ i ∈ F.innerSet, volume (F.innerBody i).carrier ≠ 0 := by
    intro i hi
    change volume (Y' i).carrier ≠ 0
    rw [hcarY i hi]
    exact hVpos i hi
  have hcv : ∀ j, ∑ i ∈ fib j, volume (Y' i).carrier = v j := fun j =>
    Finset.sum_congr rfl fun p hp => hcarY p (hfibsub j hp)
  have hlam' : ∀ j ∈ F.outerSet,
      lam j * (∑ i ∈ F.fiber j, volume (F.innerBody i).carrier) ≤
        ∑ i ∈ F.fiber j, volume (F.innerBody i).shade := by
    intro j hj
    rw [hfiber j]
    change lam j * ∑ i ∈ fib j, volume (Y' i).carrier ≤ ∑ i ∈ fib j, volume (Y' i).shade
    rw [hcv j]
    exact le_of_eq (ENNReal.div_mul_cancel (hv0 j hj) (hvtop j))
  have hecc' : ∀ j ∈ F.outerSet, ∀ i ∈ F.fiber j,
      volume (F.outerBody j).carrier ≤ 2 ^ N * volume (F.innerBody i).carrier := by
    intro j hj i hi
    rw [hfiber j] at hi
    change volume (Wb j).carrier ≤ 2 ^ N * volume (Y' i).carrier
    rw [hcarY i (hfibsub j hi)]
    exact hecc j hj i hi
  have hcord := ShadedBody.aggregateFullnessForInducedShading_of_measurable F hdim hshape
    hFrostman hne' hVpos' lam hlam' hecc'
  -- the per-body Córdoba bounds, summed
  have hsum : (CF : ENNReal)⁻¹ * ∑ j ∈ bodies, lam j ^ 2 * w j ≤ L * ∑ j ∈ bodies, sh j := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun j hj => ?_
    have h := hcord j hj
    rw [hfiber j] at h
    rw [← mul_assoc]
    exact h
  -- pass to real numbers
  set Vr : κ → ℝ := fun j => (v j).toReal with hVr
  set Wr : κ → ℝ := fun j => (w j).toReal with hWr
  set Mr : κ → ℝ := fun j => (m' j).toReal with hMr
  set Mmr : κ → ℝ := fun j => (m j).toReal with hMmr
  set Shr : κ → ℝ := fun j => (sh j).toReal with hShr
  set d : ℝ := ((δ : ENNReal) ^ η).toReal with hd
  have hδpos : (0 : ENNReal) < (δ : ENNReal) := ENNReal.coe_pos.mpr hδ
  have hdtop : (δ : ENNReal) ^ η ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg' hδpos ENNReal.coe_ne_top
  have hdnn : 0 ≤ d := ENNReal.toReal_nonneg
  have hVrpos : ∀ j ∈ bodies, 0 < Vr j := fun j hj => ENNReal.toReal_pos (hv0 j hj) (hvtop j)
  have hWrpos : ∀ j ∈ bodies, 0 < Wr j := fun j hj => ENNReal.toReal_pos (hw0 j hj) (hwtop j)
  have hθR : (0 : ℝ) < (θ : ℝ) := by exact_mod_cast hθ
  have hCFR : (0 : ℝ) < (CF : ℝ) := by exact_mod_cast hCF
  have hCfullR : (0 : ℝ) < (Cfull : ℝ) := by exact_mod_cast hCfull
  -- the band, in `ℝ`
  have hband_r : ∀ j ∈ bodies, ∀ k ∈ bodies, Vr j * Wr k ≤ 2 * (Vr k * Wr j) := by
    intro j hj k hk
    have h := ENNReal.toReal_mono
      (ENNReal.mul_ne_top (by norm_num) (ENNReal.mul_ne_top (hvtop k) (hwtop j))) (hρ j hj k hk)
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofNat] at h
    exact h
  -- the global lower bound `c · ∑ V ≤ ∑ M'` with `c = θ d / C_full`
  have hsumv : ∑ j ∈ bodies, v j = ∑ p ∈ segs, volume (Y p).carrier :=
    Finset.sum_fiberwise_of_maps_to hblk _
  have hsumm : ∑ j ∈ bodies, m j = ∑ p ∈ segs, volume (Y p).shade :=
    Finset.sum_fiberwise_of_maps_to hblk _
  have hsumm' : ∑ j ∈ bodies, m' j = ∑ p ∈ segs, volume (Y' p).shade :=
    Finset.sum_fiberwise_of_maps_to hblk _
  have hdensSum : (δ : ENNReal) ^ η * ∑ j ∈ bodies, v j ≤
      (Cfull : ENNReal) * ∑ j ∈ bodies, m j := by
    rw [hsumv, hsumm, Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_le_sum fun p hp => hdens p hp
  have hretSum : (θ : ENNReal) * ∑ j ∈ bodies, m j ≤ ∑ j ∈ bodies, m' j := by
    rw [hsumm, hsumm']
    exact hret
  have hsumVtop : ∑ j ∈ bodies, v j ≠ ⊤ := (ENNReal.sum_lt_top.mpr fun j _ =>
    lt_top_iff_ne_top.mpr (hvtop j)).ne
  have hsumMtop : ∑ j ∈ bodies, m j ≠ ⊤ := (ENNReal.sum_lt_top.mpr fun j _ =>
    lt_top_iff_ne_top.mpr (hmtop j)).ne
  have hsumM'top : ∑ j ∈ bodies, m' j ≠ ⊤ := (ENNReal.sum_lt_top.mpr fun j _ =>
    lt_top_iff_ne_top.mpr (hm'top j)).ne
  have hdensSum_r : d * ∑ j ∈ bodies, Vr j ≤ (Cfull : ℝ) * ∑ j ∈ bodies, Mmr j := by
    have h := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.coe_ne_top hsumMtop) hdensSum
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_sum (fun j _ => hvtop j),
      ENNReal.toReal_sum (fun j _ => hmtop j), ENNReal.coe_toReal] at h
    exact h
  have hretSum_r : (θ : ℝ) * ∑ j ∈ bodies, Mmr j ≤ ∑ j ∈ bodies, Mr j := by
    have h := ENNReal.toReal_mono hsumM'top hretSum
    rw [ENNReal.toReal_mul, ENNReal.toReal_sum (fun j _ => hmtop j),
      ENNReal.toReal_sum (fun j _ => hm'top j), ENNReal.coe_toReal] at h
    exact h
  set c : ℝ := (θ : ℝ) * d / (Cfull : ℝ) with hc
  have hcnn : 0 ≤ c := by positivity
  have hlow : c * ∑ j ∈ bodies, Vr j ≤ ∑ j ∈ bodies, Mr j := by
    have h1 : (θ : ℝ) * (d * ∑ j ∈ bodies, Vr j) ≤ (θ : ℝ) * ((Cfull : ℝ) * ∑ j ∈ bodies, Mmr j) :=
      mul_le_mul_of_nonneg_left hdensSum_r hθR.le
    have h2 : c * ∑ j ∈ bodies, Vr j = ((θ : ℝ) * (d * ∑ j ∈ bodies, Vr j)) / (Cfull : ℝ) := by
      rw [hc]; ring
    rw [h2, div_le_iff₀ hCfullR]
    calc (θ : ℝ) * (d * ∑ j ∈ bodies, Vr j)
        ≤ (θ : ℝ) * ((Cfull : ℝ) * ∑ j ∈ bodies, Mmr j) := h1
      _ = ((θ : ℝ) * ∑ j ∈ bodies, Mmr j) * (Cfull : ℝ) := by ring
      _ ≤ (∑ j ∈ bodies, Mr j) * (Cfull : ℝ) := by gcongr
  -- the Cauchy–Schwarz accounting
  have hcs := weighted_cauchySchwarz_accounting bodies hbne Vr Wr Mr hVrpos hWrpos hband_r
    hcnn hlow
  -- the summed Córdoba bound, in `ℝ`
  have hLr : L.toReal = (ShadedBody.lambdaInducedSingleWUniform.C : ℝ) * ((N : ℝ) + 1) := by
    rw [hL, ENNReal.toReal_mul, ENNReal.coe_toReal, ENNReal.toReal_add (ENNReal.natCast_ne_top _)
      ENNReal.one_ne_top, ENNReal.toReal_natCast, ENNReal.toReal_one]
  have hLtop : L ≠ ⊤ := ENNReal.mul_ne_top ENNReal.coe_ne_top
    (ENNReal.add_ne_top.mpr ⟨ENNReal.natCast_ne_top _, ENNReal.one_ne_top⟩)
  have hsumShtop : ∑ j ∈ bodies, sh j ≠ ⊤ := (ENNReal.sum_lt_top.mpr fun j _ =>
    lt_top_iff_ne_top.mpr (hshtop j)).ne
  have hsum_r : (CF : ℝ)⁻¹ * ∑ j ∈ bodies, (Mr j / Vr j) ^ 2 * Wr j ≤
      L.toReal * ∑ j ∈ bodies, Shr j := by
    have h := ENNReal.toReal_mono (ENNReal.mul_ne_top hLtop hsumShtop) hsum
    have hterm : ∀ j ∈ bodies, lam j ^ 2 * w j ≠ ⊤ := fun j hj =>
      ENNReal.mul_ne_top (ENNReal.pow_ne_top
        (ENNReal.div_ne_top (hm'top j) (hv0 j hj))) (hwtop j)
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_sum hterm,
      ENNReal.toReal_sum (fun j _ => hshtop j), ENNReal.toReal_inv, ENNReal.coe_toReal] at h
    refine le_of_le_of_eq (le_of_eq_of_le ?_ h) rfl
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_div]
  -- the final real inequality: `d² ≤ K · (∑ Sh / ∑ W)`
  have hsumWr : 0 < ∑ j ∈ bodies, Wr j := Finset.sum_pos hWrpos hbne
  have hKr : ((thinFibreDensityConstant CF Cfull θ N : NNReal) : ℝ) =
      4 * (CF : ℝ) * (Cfull : ℝ) ^ 2 * (ShadedBody.lambdaInducedSingleWUniform.C : ℝ) *
        ((N : ℝ) + 1) / (θ : ℝ) ^ 2 := by
    rw [thinFibreDensityConstant]
    push_cast
    ring
  have hkey : (θ : ℝ) ^ 2 * d ^ 2 * ∑ j ∈ bodies, Wr j ≤
      4 * (CF : ℝ) * (Cfull : ℝ) ^ 2 * L.toReal * ∑ j ∈ bodies, Shr j := by
    have hcs' : ∑ j ∈ bodies, (Mr j / Vr j) ^ 2 * Wr j ≤
        (CF : ℝ) * (L.toReal * ∑ j ∈ bodies, Shr j) := by
      rw [← inv_mul_le_iff₀ hCFR]
      exact hsum_r
    have hc2 : c ^ 2 = (θ : ℝ) ^ 2 * d ^ 2 / (Cfull : ℝ) ^ 2 := by
      rw [hc]; ring
    have h := hcs
    rw [hc2] at h
    have h' : (θ : ℝ) ^ 2 * d ^ 2 * ∑ j ∈ bodies, Wr j ≤
        (Cfull : ℝ) ^ 2 * (4 * ∑ j ∈ bodies, (Mr j / Vr j) ^ 2 * Wr j) := by
      have hCf2 : 0 < (Cfull : ℝ) ^ 2 := by positivity
      have := mul_le_mul_of_nonneg_left h hCf2.le
      calc (θ : ℝ) ^ 2 * d ^ 2 * ∑ j ∈ bodies, Wr j
          = (Cfull : ℝ) ^ 2 * ((θ : ℝ) ^ 2 * d ^ 2 / (Cfull : ℝ) ^ 2 * ∑ j ∈ bodies, Wr j) := by
            field_simp
        _ ≤ (Cfull : ℝ) ^ 2 * (4 * ∑ j ∈ bodies, (Mr j / Vr j) ^ 2 * Wr j) := this
    calc (θ : ℝ) ^ 2 * d ^ 2 * ∑ j ∈ bodies, Wr j
        ≤ (Cfull : ℝ) ^ 2 * (4 * ∑ j ∈ bodies, (Mr j / Vr j) ^ 2 * Wr j) := h'
      _ ≤ (Cfull : ℝ) ^ 2 * (4 * ((CF : ℝ) * (L.toReal * ∑ j ∈ bodies, Shr j))) := by gcongr
      _ = 4 * (CF : ℝ) * (Cfull : ℝ) ^ 2 * L.toReal * ∑ j ∈ bodies, Shr j := by ring
  have hfinal_r : d ^ 2 ≤ ((thinFibreDensityConstant CF Cfull θ N : NNReal) : ℝ) *
      ((∑ j ∈ bodies, Shr j) / ∑ j ∈ bodies, Wr j) := by
    rw [hLr] at hkey
    rw [hKr, div_mul_div_comm, le_div_iff₀ (by positivity)]
    calc d ^ 2 * ((θ : ℝ) ^ 2 * ∑ j ∈ bodies, Wr j)
        = (θ : ℝ) ^ 2 * d ^ 2 * ∑ j ∈ bodies, Wr j := by ring
      _ ≤ 4 * (CF : ℝ) * (Cfull : ℝ) ^ 2 * ((ShadedBody.lambdaInducedSingleWUniform.C : ℝ) *
          ((N : ℝ) + 1)) * ∑ j ∈ bodies, Shr j := hkey
      _ = _ := by ring
  -- back to `ℝ≥0∞`
  have hfull : (ShadedBody.fullness bodies Wind : ENNReal) =
      (∑ j ∈ bodies, sh j) / ∑ j ∈ bodies, w j := by
    rw [ShadedBody.fullness_def]
    rfl
  have hpow : (δ : ENNReal) ^ (2 * η) = ((δ : ENNReal) ^ η) ^ 2 := by
    rw [mul_comm, ENNReal.rpow_mul, ENNReal.rpow_two]
  have hLHStop : ((δ : ENNReal) ^ η) ^ 2 ≠ ⊤ := ENNReal.pow_ne_top hdtop
  have hRHStop : (thinFibreDensityConstant CF Cfull θ N : ENNReal) *
      (ShadedBody.fullness bodies Wind : ENNReal) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.coe_ne_top
  have hsumWtop : ∑ j ∈ bodies, w j ≠ ⊤ := (ENNReal.sum_lt_top.mpr fun j _ =>
    lt_top_iff_ne_top.mpr (hwtop j)).ne
  change (δ : ENNReal) ^ (2 * η) ≤ (thinFibreDensityConstant CF Cfull θ N : ENNReal) *
    (ShadedBody.fullness bodies Wind : ENNReal)
  rw [hpow, ← ENNReal.toReal_le_toReal hLHStop hRHStop, ENNReal.toReal_pow, ENNReal.toReal_mul,
    ENNReal.coe_toReal, hfull, ENNReal.toReal_div, ENNReal.toReal_sum (fun j _ => hshtop j),
    ENNReal.toReal_sum (fun j _ => hwtop j)]
  exact hfinal_r

end Fullness

end Kakeya.ThinCase
