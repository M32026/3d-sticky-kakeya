/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.RandomTranslation.RigidEDBridge
public import Kakeya.RandomTranslation.RigidRandCF

/-!
# The corrected random-copy theorem, GWZ Lemma 3.8

This is the replacement for `Kakeya.exists_randCF_translation_family`. It assembles

* `Kakeya.rigid_frostman_bad_prob_lt` — the Frostman conjunct, failure probability `< 1/4`;
* `Kakeya.rigid_edFail_bad_prob_lt` — the ED conjunct for the *correct* count, failure `< 1/4`;
* `Kakeya.rigidPiMeasure_translation_outside_eq_zero` — translations lie in `B₁` almost surely;
* `Kakeya.isEDUpToMult_rigidProduct_of_net_good` — the deterministic bridge;
* `Kakeya.fullness_rigidProduct` and `Kakeya.multiplicity_le_rigidProduct` — the retention data.

## The ED multiplicity cap

The deterministic bridge loses **nothing**: it is an injection followed by a fibrewise count, so the
`IsEDUpToMult` multiplicity is exactly the net-goodness threshold `rigidMED C_EDlog δ`. There is no
`C_ED` factor and no additive `C₀`. Since `rigidMED C δ = O(log (1/δ))`, the cap and its square are
absorbed into `δ^(-η)` for every `η > 0` (`Kakeya.rigidMED_succ_eventually_le_rpow_neg` and
`Kakeya.rigidMED_succ_sq_eventually_le_rpow_neg` below), and the cap is independent of the Frostman
constant. This is exactly what replaces the old `M_ED := ⌈C_F⌉₊ · C_pack_ext + 1`.

## Quantifier order

The constants come first, then `∀ᶠ δ`, and only then the family. `C_F` and `J = ⌈C_F⌉₊` are defined
*after* the family is in scope, so no external Frostman parameter appears anywhere before `δ`.

## Geometry

The randomised copies land in `B₂`, not `B₁`: a rotation preserves `B₁`, and a subsequent
translation by a vector of `B₁` can only be guaranteed to stay inside `B₂`
(`Kakeya.rigidProduct_carrier_subset_closedBall_two`). The paper's `B₁` is a typo and is not
reproduced.
-/

@[expose] public section

open MeasureTheory Metric Set Filter Topology

namespace Kakeya

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {δ : NNReal}

/-! ## Polylogarithmic absorption of the final ED cap -/

/-- `rigidMED C δ + 1 ≤ δ^(-η)` eventually, for every `η > 0`. The `+1` is the loss of the
pairwise-ED refinement `Kakeya.IsEDUpToMult.exists_pairwise_subset_with_weight`. -/
theorem rigidMED_succ_eventually_le_rpow_neg {C η : ℝ} (hC : 0 < C) (hη : 0 < η) :
    ∀ᶠ (δ : NNReal) in 𝓝[>] 0, ((rigidMED C δ : ℕ) : ℝ) + 1 ≤ (δ : ℝ) ^ (-η) := by
  apply eventually_le_rpow_neg_of_le_polylog (by linarith : (0 : ℝ) < C + 3) hη 1
  intro δ hδ hδ1
  let L : ℝ := 1 + Real.log (1 / (δ : ℝ))
  have hδR : 0 < (δ : ℝ) := NNReal.coe_pos.mpr hδ
  have hone : (1 : ℝ) ≤ 1 / (δ : ℝ) := one_le_one_div hδR hδ1
  have hlog : 0 ≤ Real.log (1 / (δ : ℝ)) := Real.log_nonneg hone
  have hL : (1 : ℝ) ≤ L := by
    dsimp [L]
    linarith
  have hR : ((rigidMED C δ : ℕ) : ℝ) ≤ (C + 2) * L := by
    have hmain := rigidMED_le_polylog hC δ hδ hδ1
    have hp : (1 + Real.log (1 / (δ : ℝ))) ^ 1 = L := by
      dsimp [L]
      rw [pow_one]
    rw [hp] at hmain
    change ((rigidMED C δ : ℕ) : ℝ) ≤ (C + 2) * L
    exact hmain
  have hp1 : (1 + Real.log (1 / (δ : ℝ))) ^ 1 = L := by
    dsimp [L]
    rw [pow_one]
  rw [hp1]
  calc
    ((rigidMED C δ : ℕ) : ℝ) + 1 ≤ (C + 2) * L + 1 := by linarith
    _ ≤ (C + 2) * L + L := by linarith
    _ = (C + 3) * L := by ring

/-- `(rigidMED C δ + 1)^2 ≤ δ^(-η)` eventually, for every `η > 0`. -/
theorem rigidMED_succ_sq_eventually_le_rpow_neg {C η : ℝ} (hC : 0 < C) (hη : 0 < η) :
    ∀ᶠ (δ : NNReal) in 𝓝[>] 0, (((rigidMED C δ : ℕ) : ℝ) + 1) ^ 2 ≤ (δ : ℝ) ^ (-η) := by
  apply eventually_le_rpow_neg_of_le_polylog (by nlinarith : (0 : ℝ) < (C + 3) ^ 2) hη 2
  intro δ hδ hδ1
  let L : ℝ := 1 + Real.log (1 / (δ : ℝ))
  let R := ((rigidMED C δ : ℕ) : ℝ)
  have hδR : 0 < (δ : ℝ) := NNReal.coe_pos.mpr hδ
  have hone : (1 : ℝ) ≤ 1 / (δ : ℝ) := one_le_one_div hδR hδ1
  have hlog : 0 ≤ Real.log (1 / (δ : ℝ)) := Real.log_nonneg hone
  have hL : (1 : ℝ) ≤ L := by
    dsimp [L]
    linarith
  have hLnn : 0 ≤ L := by linarith [hL]
  have hR : R ≤ (C + 2) * L := by
    have hmain := rigidMED_le_polylog hC δ hδ hδ1
    have hp : (1 + Real.log (1 / (δ : ℝ))) ^ 1 = L := by
      dsimp [L]
      rw [pow_one]
    rw [hp] at hmain
    change R ≤ (C + 2) * L
    exact hmain
  have hR1 : R + 1 ≤ (C + 3) * L := by
    calc
      R + 1 ≤ (C + 2) * L + 1 := by linarith
      _ ≤ (C + 2) * L + L := by linarith
      _ = (C + 3) * L := by ring
  have hR1nn : 0 ≤ R + 1 := by positivity
  have hpow : (R + 1) ^ 2 ≤ ((C + 3) * L) ^ 2 := pow_le_pow_left₀ hR1nn hR1 2
  have hmul : ((C + 3) * L) ^ 2 = (C + 3) ^ 2 * L ^ 2 := by ring
  rw [hmul] at hpow
  have hp2 : (1 + Real.log (1 / (δ : ℝ))) ^ 2 = L ^ 2 := by
    dsimp [L]
  rw [hp2]
  exact hpow

/-! ## The corrected tuple extraction -/

/-- **One rigid tuple satisfying both conjuncts, for the corrected ED count.**

Identical to `Kakeya.exists_rigid_tuple_frostman_and_ed` except that the ED conjunct is stated for
`Kakeya.edFailCountAt`, the volume-fraction count that the deterministic bridge consumes. -/
theorem exists_rigid_tuple_frostman_and_edFail [Nontrivial E] (hn : 1 < Module.finrank ℝ E)
    {η : ℝ} (hη : 0 < η) :
    ∃ C_EDlog : ℝ, 0 < C_EDlog ∧
    ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
    ∀ {ι : Type*} (s : Finset ι) (T : ι → ShadedTube δ E),
      (∀ i ∈ s, (T i).carrier ⊆ closedBall (0 : E) 1) →
      (s : Set ι).Pairwise
        (fun i j => IsEssentiallyDistinct (T i).carrier (T j).carrier) →
      0 < s.card →
      ∀ J : ℕ, 0 < J →
        (ConvexSpaceBody.frostmanConstant s (fun i => (T i).toConvexSpaceBody)
            ConvexSpaceBody.closedUnitBall).toReal ≤ (J : ℝ) →
        (J : ℝ) ≤ (⌈(ConvexSpaceBody.frostmanConstant s (fun i => (T i).toConvexSpaceBody)
            ConvexSpaceBody.closedUnitBall).toReal⌉₊ : ℝ) →
        ∃ (NetT : Finset (Tube δ E)) (ω : Fin J → unitary (E →L[ℝ] E) × E),
          (∀ T₀ ∈ NetT, T₀.carrier ⊆ closedBall (0 : E) (7 / 2)) ∧
          (∀ T₀ : Tube δ E, T₀.carrier ⊆ closedBall (0 : E) 2 →
            ∃ T₀' ∈ NetT,
              T₀.carrier ⊆ Metric.cthickening (99 * (δ : ℝ)) T₀'.carrier) ∧
          (∀ j, (ω j).2 ∈ closedBall (0 : E) 1) ∧
          ConvexSpaceBody.IsFrostmanIn (s ×ˢ (Finset.univ : Finset (Fin J)))
            (fun p => (rigidProduct T J ω p).toConvexSpaceBody)
            (ConvexSpaceBody.cthickening 1
              (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E))
            (ENNReal.ofReal ((δ : ℝ) ^ (-η))) ∧
          (∀ T₀ ∈ NetT,
            ∑ j : Fin J, edFailCountAt s (fun i => (T i).toTube) T₀ J j ω
              ≤ ((rigidMED C_EDlog δ : ℕ) : ℝ)) := by
  classical
  obtain ⟨C_EDlog, hC_pos, hED_filter⟩ := Kakeya.rigid_edFail_bad_prob_lt (E := E) hn
  refine ⟨C_EDlog, hC_pos, ?_⟩
  filter_upwards [rigid_frostman_bad_prob_lt (E := E) hn hη, hED_filter] with δ hF hED
  intro ι s T hT_ball hED_pairwise hs_card J hJ hJ_ge hJ_le
  obtain ⟨NetT, hNetB, happrox, hBadED⟩ :=
    hED s (fun i => (T i).toTube) (by simpa using hT_ball) (by simpa using hED_pairwise) J hJ
      (by simpa using hJ_le)
  set BadF : Set (Fin J → unitary (E →L[ℝ] E) × E) :=
    {ω | ¬ ConvexSpaceBody.IsFrostmanIn (s ×ˢ (Finset.univ : Finset (Fin J)))
      (fun p => (rigidProduct T J ω p).toConvexSpaceBody)
      (ConvexSpaceBody.cthickening 1 (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E))
      (ENNReal.ofReal ((δ : ℝ) ^ (-η)))}
  set BadED : Set (Fin J → unitary (E →L[ℝ] E) × E) :=
    {ω | ∃ T₀ ∈ NetT, ((rigidMED C_EDlog δ : ℕ) : ℝ) <
      ∑ j : Fin J, edFailCountAt s (fun i => (T i).toTube) T₀ J j ω}
  set Out : Set (Fin J → unitary (E →L[ℝ] E) × E) :=
    {ω | ∃ j, (ω j).2 ∉ closedBall (0 : E) 1}
  let μ : Measure (Fin J → unitary (E →L[ℝ] E) × E) := rigidPiMeasure E J
  have hμuniv : μ Set.univ = 1 := by
    change rigidPiMeasure E J Set.univ = 1
    exact (inferInstance : IsProbabilityMeasure (rigidPiMeasure E J)).measure_univ
  have hunion : μ (BadF ∪ BadED ∪ Out) < 1 := by
    have hFm : μ BadF < ENNReal.ofReal (1 / 4) := by
      simpa [μ, BadF] using hF s T hT_ball hs_card J hJ hJ_ge
    have hEm : μ BadED < ENNReal.ofReal (1 / 4) := by
      simpa [μ, BadED] using hBadED
    have hOm : μ Out = 0 := by
      simpa [μ, Out] using rigidPiMeasure_translation_outside_eq_zero (E := E) J
    have hle : μ (BadF ∪ BadED ∪ Out) ≤ μ BadF + μ BadED + μ Out := by
      calc
        μ (BadF ∪ BadED ∪ Out) ≤ μ (BadF ∪ BadED) + μ Out :=
          measure_union_le (BadF ∪ BadED) Out
        _ ≤ (μ BadF + μ BadED) + μ Out :=
          add_le_add (measure_union_le BadF BadED) le_rfl
    have hFle : μ BadF ≤ ENNReal.ofReal (1 / 4) := le_of_lt hFm
    have hEle : μ BadED ≤ ENNReal.ofReal (1 / 4) := le_of_lt hEm
    have hleq : μ BadF + μ BadED + μ Out ≤
        ENNReal.ofReal (1 / 4) + ENNReal.ofReal (1 / 4) + 0 := by
      exact add_le_add (add_le_add hFle hEle) hOm.le
    have hsum : ENNReal.ofReal (1 / 4) + ENNReal.ofReal (1 / 4) + 0 =
        ENNReal.ofReal (1 / 2) := by
      rw [← ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ (1 / 4 : ℝ))
        (by norm_num : (0 : ℝ) ≤ (1 / 4 : ℝ)), add_zero]
      rw [show (1 / 4 : ℝ) + 1 / 4 = 1 / 2 by norm_num]
    have hle2 : μ BadF + μ BadED + μ Out ≤ ENNReal.ofReal (1 / 2) := by
      rw [← hsum]
      exact hleq
    have hhalf : ENNReal.ofReal (1 / 2) < 1 := by
      rw [← ENNReal.ofReal_one]
      exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ) < (1 : ℝ))).mpr
        (by norm_num : (1 / 2 : ℝ) < 1)
    exact lt_of_le_of_lt (le_trans hle hle2) hhalf
  have hUneq : BadF ∪ BadED ∪ Out ≠ Set.univ := by
    intro hEq
    have : μ (BadF ∪ BadED ∪ Out) = 1 := by rw [hEq]; exact hμuniv
    exact (ne_of_lt hunion) this
  obtain ⟨ω, hωnot⟩ : ∃ ω, ω ∉ BadF ∪ BadED ∪ Out := by
    by_contra hbad
    have hAll : (BadF ∪ BadED ∪ Out) = Set.univ := by
      rw [Set.eq_univ_iff_forall]
      intro z
      by_contra hz
      exact hbad ⟨z, hz⟩
    exact hUneq hAll
  have hnotF : ω ∉ BadF := by
    intro hmem
    exact hωnot (by simp [hmem])
  have hnotED : ω ∉ BadED := by
    intro hmem
    exact hωnot (by simp [hmem])
  have hout : ω ∉ Out := by
    intro hmem
    exact hωnot (by simp [hmem])
  have hBall : ∀ j, (ω j).2 ∈ closedBall (0 : E) 1 := by
    intro j
    by_contra hb
    exact hout ⟨j, hb⟩
  have hFrost : ConvexSpaceBody.IsFrostmanIn (s ×ˢ (Finset.univ : Finset (Fin J)))
      (fun p => (rigidProduct T J ω p).toConvexSpaceBody)
      (ConvexSpaceBody.cthickening 1 (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E))
      (ENNReal.ofReal ((δ : ℝ) ^ (-η))) := by
    by_contra hbad
    exact hnotF (by simpa [BadF] using hbad)
  have hEDgood : ∀ T₀ ∈ NetT,
      ∑ j : Fin J, edFailCountAt s (fun i => (T i).toTube) T₀ J j ω
        ≤ ((rigidMED C_EDlog δ : ℕ) : ℝ) := by
    intro T₀ hT₀
    have hnotBad : ¬ (((rigidMED C_EDlog δ : ℕ) : ℝ) <
        ∑ j : Fin J, edFailCountAt s (fun i => (T i).toTube) T₀ J j ω) := by
      by_contra hbad
      exact hnotED (by simpa [BadED] using ⟨T₀, hT₀, hbad⟩)
    exact not_lt.mp hnotBad
  exact ⟨NetT, ω, hNetB, happrox, hBall, hFrost, hEDgood⟩

/-! ## GWZ Lemma 3.8 -/

/-- **[GWZ, Lemma 3.8], corrected.** The random-copy theorem for rigid motions.

Given a pairwise essentially distinct family of `δ`-tubes in `B₁` with fullness at least `δ^η`, and
taking `J = ⌈C_F⌉₊` copies with `C_F` the *actual* canonical Frostman constant of the family, there
is a randomised family on `s ×ˢ Fin J` which

* lies in `B₂` (the corrected geometry);
* is `δ^(-η)`-convex-Frostman in `B₂`;
* is essentially distinct up to multiplicity `M_cap` with `M_cap + 1 ≤ δ^(-η)`;
* has cardinality `J · |s|`;
* has the same fullness as the input;
* has multiplicity at least that of the input.

No external Frostman bound is supplied, and the eventual `δ`-set precedes the family. -/
theorem exists_randCF_rigid_family [Nontrivial E] (hn : 1 < Module.finrank ℝ E)
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
    ∀ {ι : Type*} (s : Finset ι) (T : ι → ShadedTube δ E),
      (∀ i ∈ s, (T i).carrier ⊆ closedBall (0 : E) 1) →
      (s : Set ι).Pairwise
        (fun i j => IsEssentiallyDistinct (T i).carrier (T j).carrier) →
      0 < s.card →
      ∃ (J : ℕ) (ω : Fin J → unitary (E →L[ℝ] E) × E) (M_cap : ℕ),
        J = ⌈(ConvexSpaceBody.frostmanConstant s (fun i => (T i).toConvexSpaceBody)
              ConvexSpaceBody.closedUnitBall).toReal⌉₊ ∧
        0 < J ∧
        (∀ j, (ω j).2 ∈ closedBall (0 : E) 1) ∧
        ((M_cap : ℝ) + 1 ≤ (δ : ℝ) ^ (-η)) ∧
        ((s ×ˢ (Finset.univ : Finset (Fin J))).card = J * s.card) ∧
        (∀ p ∈ s ×ˢ (Finset.univ : Finset (Fin J)),
          (rigidProduct T J ω p).carrier ⊆ closedBall (0 : E) 2) ∧
        IsEDUpToMult (s ×ˢ (Finset.univ : Finset (Fin J)))
          (fun p => (rigidProduct T J ω p).carrier) M_cap ∧
        ConvexSpaceBody.IsFrostmanIn (s ×ˢ (Finset.univ : Finset (Fin J)))
          (fun p => (rigidProduct T J ω p).toConvexSpaceBody)
          (ConvexSpaceBody.cthickening 1
            (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E))
          (ENNReal.ofReal ((δ : ℝ) ^ (-η))) ∧
        ShadedBody.fullness (s ×ˢ (Finset.univ : Finset (Fin J)))
            (fun p => (rigidProduct T J ω p).toShadedBody)
          = ShadedBody.fullness s (fun i => (T i).toShadedBody) ∧
        ShadedBody.multiplicity s (fun i => (T i).toShadedBody)
          ≤ ShadedBody.multiplicity (s ×ˢ (Finset.univ : Finset (Fin J)))
              (fun p => (rigidProduct T J ω p).toShadedBody) := by
  classical
  obtain ⟨C_EDlog, hC_pos, hTuple⟩ := exists_rigid_tuple_frostman_and_edFail (E := E) hn hη
  have hlt1 : ∀ᶠ (x : ℝ) in 𝓝[>] (0 : ℝ), x < (1 : ℝ) := by
    refine Filter.eventually_of_mem (Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)) ?_
    intro x hx
    exact hx.2
  filter_upwards [hTuple, rigidMED_succ_eventually_le_rpow_neg hC_pos hη,
      self_mem_nhdsWithin, nnreal_eventually_of_real_eventually hlt1]
    with δ hTupleδ hMcap hδpos hδlt
  have hδleR : (δ : ℝ) ≤ 1 := le_of_lt hδlt
  have hδ1 : δ ≤ 1 := by exact_mod_cast hδleR
  intro ι s T hT_ball hED hs_card
  set CF : ENNReal :=
    ConvexSpaceBody.frostmanConstant s (fun i => (T i).toConvexSpaceBody)
      ConvexSpaceBody.closedUnitBall with hCF
  set J : ℕ := ⌈CF.toReal⌉₊ with hJdef
  have hsne : s.Nonempty := Finset.card_pos.mp hs_card
  let W : ι → ConvexSpaceBody E := fun i => (T i).toConvexSpaceBody
  let B1 : ConvexSpaceBody E := ConvexSpaceBody.closedUnitBall
  have hDpos : 0 < densityIn s W B1 := by
    rw [densityIn_pos_iff]
    obtain ⟨i, hi⟩ := hsne
    refine ⟨i, hi, ?_, ?_⟩
    · have hP0 : (δ : ENNReal) ^ (Module.finrank ℝ E - 1) ≠ 0 :=
        pow_ne_zero (Module.finrank ℝ E - 1)
          (ENNReal.coe_ne_zero.mpr (ne_of_gt hδpos))
      have hcp0 : (0 : ENNReal) <
            ((Tube.le_volume.c (Module.finrank ℝ E) : NNReal) : ENNReal)
              * (δ : ENNReal) ^ (Module.finrank ℝ E - 1) :=
        lt_of_le_of_ne zero_le (mul_ne_zero
          (ENNReal.coe_ne_zero.mpr (ne_of_gt (Tube.le_volume.c_pos (Module.finrank ℝ E))))
          hP0).symm
      exact lt_of_lt_of_le hcp0 (by
        simpa [W] using (Tube.le_volume (T i).toTube))
    · exact SetLike.coe_subset_coe.mp (by
        calc
          (W i : Set E) = (T i).carrier := rfl
          _ ⊆ Metric.closedBall (0 : E) 1 := hT_ball i hi
          _ = (B1 : Set E) := rfl)
  have hCF_one : (1 : ENNReal) ≤ CF := by
    have hFC : (1 : ENNReal) ≤ ConvexSpaceBody.frostmanConstant s W B1 :=
      ConvexSpaceBody.one_le_frostmanConstant hDpos
    simpa [CF, W, B1] using hFC
  have hCFtop : CF ≠ ⊤ := by
    dsimp [CF]
    exact Tube.frostmanConstant_ne_top hδpos s (fun i => (T i).toTube) (by simpa using hT_ball)
  have hCFtoReal : (1 : ℝ) ≤ CF.toReal :=
    (ENNReal.toReal_le_toReal (by norm_num : (1 : ENNReal) ≠ ⊤) hCFtop).mpr hCF_one
  have hJ : 0 < J := by
    dsimp [J]
    exact Nat.ceil_pos.mpr (lt_of_lt_of_le zero_lt_one hCFtoReal)
  have hJge : CF.toReal ≤ (J : ℝ) := by
    simpa [J] using (Nat.le_ceil CF.toReal)
  obtain ⟨NetT, ω, hNetB, happrox, hω, hFrost, hgood⟩ :=
    hTupleδ s T hT_ball hED hs_card J hJ hJge le_rfl
  refine ⟨J, ω, rigidMED C_EDlog δ, hJdef, hJ, hω, hMcap, ?_, ?_, ?_, hFrost, ?_, ?_⟩
  · rw [Finset.card_product, Finset.card_univ, Fintype.card_fin, mul_comm]
  · intro p hp
    exact rigidProduct_carrier_subset_closedBall_two s T hT_ball J ω hω p
      (Finset.mem_product.mp hp).1
  · exact isEDUpToMult_rigidProduct_of_net_good hδpos hδ1 s T hT_ball J ω hω NetT happrox
      (rigidMED C_EDlog δ) hgood
  · exact fullness_rigidProduct s T J hJ ω
  · exact multiplicity_le_rigidProduct s T J hJ ω

end

end Kakeya

end
