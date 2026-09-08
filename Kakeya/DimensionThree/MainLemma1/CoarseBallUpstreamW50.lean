/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma1.Cases
public import Kakeya.DimensionThree.MainLemma1.Rescaling.BallRadius

/-!
# The coarse factor of Case (ii) at an ambient radius `R`

`Kakeya.ml1Boot.multiplicity_le_coarse` is stated for a family of shaded `θ`-tubes in the unit
ball, because the Frostman estimate `K_F` it applies is normalised to `B₁`.  The coarse family of
the Case (ii) chain — the level-`a` nodes of the dividing block — lies in `B₄`
(`Kakeya.ml1Boot.caseTwoNodeBalls_four`), not in `B₁`, and a `Kakeya.Tube` has core length exactly
`1`, so no similarity brings it there.  What does bring it there is the cell decomposition of
`Kakeya.ml1Boot.multiplicity_le_of_ball_of_unitBall`: translate each cell of a fixed finite cover
into `B₁` and apply the unit-ball statement there.

The one hypothesis that does not descend to a cell for free is the Frostman bound.  For a cell
`t' ⊆ t` carrying the share `D = #t / #t'` of the (equal) tube volumes,
`ConvexSpaceBody.IsFrostmanIn.translate_of_le_of_subset` gives the translated cell the Frostman
constant `C · D` relative to `B₁`; since the Frostman estimate is applied with the factor
`C ^ (1 - γ/2) · (#t' θ²) ^ (1 - γ/2)`, the share cancels exactly:
`(C D) ^ p (#t' θ²) ^ p = (C · #t · θ²) ^ p`.  So every cell obeys the *same* bound as the whole
family would in `B₁`, and the cell sum costs the constant `2 M` of the cover, which is paid out
of the numeric hypothesis `hc` exactly as `Kakeya.ml1Boot.multiplicity_le_coarse` pays its `L`.
-/

@[expose] public section

open MeasureTheory ConvexSpaceBody ShadedBody Filter Topology
open scoped NNReal ENNReal

namespace Kakeya

universe u

namespace ml1Boot

section CoarseBall

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- Every finite family has the vacuous body-level ED multiplicity cap given by its own
cardinality.  This is the strongest cap available without additional geometric information. -/
theorem isEDUpToMult_card {ι : Type*} (s : Finset ι) (V : ι → Set E) :
    IsEDUpToMult s V s.card := by
  classical
  intro i hi
  unfold notEssDistinctSet
  exact Finset.card_le_card (Finset.filter_subset _ _)

/-- At unit tube scale, the vacuous cardinality cap cannot satisfy the cap payment required by
`FrostmanEstimate.ball2_version_edUpToMult` for any nonempty family. -/
theorem not_card_cap_at_unitScale {ι : Type*} {s : Finset ι} (hs : s.Nonempty) (η : ℝ) :
    ¬ ((s.card : ℝ) + 1 ≤ (1 : ℝ) ^ (-η)) := by
  intro hcap
  rw [Real.one_rpow] at hcap
  have hcard : (1 : ℝ) ≤ (s.card : ℝ) := by
    exact_mod_cast Finset.one_le_card.mpr hs
  linarith

/-- A fixed ambient ball costs no power in the standard `δ ^ (-7)` cardinality bound.

Indeed, essential distinctness gives `#t ≤ C₃ (R / σ)^6`.  Since `δ ≤ σ`, this is at
most `(C₃ R^6) δ^(-6)`, and the fixed factor `C₃ R^6` is eventually at most
`δ^(-1)`. -/
theorem eventually_card_le_rpow_neg_seven_ball [Nontrivial E]
    (hdim : Module.finrank ℝ E = 3)
    (R : ℝ) (hR : 1 ≤ R) :
    Filter.Eventually (fun δ : NNReal => ∀ σ : NNReal, δ ≤ σ →
      ∀ {κ : Type u} (t : Finset κ) (T : κ → Tube σ E),
        (∀ k ∈ t, (T k).carrier ⊆ Metric.closedBall 0 R) →
        (t : Set κ).Pairwise
          (fun k k' => IsEssentiallyDistinct (T k).carrier (T k').carrier) →
        (t.card : ℝ) ≤ (δ : ℝ) ^ (-(7 : ℝ))) (nhdsWithin 0 (Set.Ioi 0)) := by
  let D : ℝ := Tube.card_le_of_EssDistinct.C 3 * R ^ 6
  have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hC0 : 0 < Tube.card_le_of_EssDistinct.C 3 :=
    Tube.card_le_of_EssDistinct.C_pos
  have hD0 : 0 < D := mul_pos hC0 (pow_pos hR0 6)
  let Dnn : NNReal := ⟨D, hD0.le⟩
  have hDtop : (Dnn : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  filter_upwards [eventually_finite_const_le_rpow_neg hDtop (by norm_num : (0 : ℝ) < 1),
    self_mem_nhdsWithin] with δ hDabs hδ0
  intro σ hδσ κ t T hball hED
  have hσ0 : 0 < σ := hδ0.trans_le hδσ
  have hδR : 0 < (δ : ℝ) := by exact_mod_cast hδ0
  have hσR : 0 < (σ : ℝ) := by exact_mod_cast hσ0
  have hratio : R / (σ : ℝ) ≤ R / (δ : ℝ) :=
    div_le_div_of_nonneg_left hR0.le hδR (by exact_mod_cast hδσ)
  have hratioPow : (R / (σ : ℝ)) ^ 6 ≤ (R / (δ : ℝ)) ^ 6 :=
    pow_le_pow_left₀ (div_nonneg hR0.le hσR.le) hratio 6
  have hcard : (t.card : ℝ) ≤
      Tube.card_le_of_EssDistinct.C 3 * (R / (σ : ℝ)) ^ 6 := by
    simpa [hdim] using
      Tube.card_le_of_EssDistinct hσ0 R t T hball hED
  have hcardD : (t.card : ℝ) ≤ D * (δ : ℝ) ^ (-(6 : ℝ)) := by
    calc
      (t.card : ℝ) ≤ Tube.card_le_of_EssDistinct.C 3 * (R / (σ : ℝ)) ^ 6 := hcard
      _ ≤ Tube.card_le_of_EssDistinct.C 3 * (R / (δ : ℝ)) ^ 6 := by gcongr
      _ = D * (δ : ℝ) ^ (-(6 : ℝ)) := by
        dsimp [D]
        rw [Real.rpow_neg hδR.le]
        norm_num
        field_simp
  have hcardE : (t.card : ENNReal) ≤
      (Dnn : ENNReal) * (δ : ENNReal) ^ (-(6 : ℝ)) := by
    have h := ENNReal.ofReal_le_ofReal hcardD
    rw [ENNReal.ofReal_natCast] at h
    rw [ENNReal.ofReal_mul hD0.le] at h
    have hDcoe : ENNReal.ofReal D = (Dnn : ENNReal) := by
      calc
        ENNReal.ofReal D = ENNReal.ofReal (Dnn : ℝ) := by rfl
        _ = (Dnn : ENNReal) := ENNReal.ofReal_coe_nnreal
    rw [hDcoe] at h
    rw [show ENNReal.ofReal ((δ : ℝ) ^ (-(6 : ℝ))) =
        (δ : ENNReal) ^ (-(6 : ℝ)) by
      simpa using (ennreal_coe_nnreal_rpow hδR (-(6 : ℝ))).symm] at h
    exact h
  have hgoalE : (t.card : ENNReal) ≤ (δ : ENNReal) ^ (-(7 : ℝ)) := by
    calc
      (t.card : ENNReal) ≤ (Dnn : ENNReal) * (δ : ENNReal) ^ (-(6 : ℝ)) := hcardE
      _ ≤ (δ : ENNReal) ^ (-(1 : ℝ)) * (δ : ENNReal) ^ (-(6 : ℝ)) := by
        gcongr
      _ = (δ : ENNReal) ^ (-(7 : ℝ)) := by
        rw [← ENNReal.rpow_add _ _ (ENNReal.coe_ne_zero.mpr hδ0.ne') ENNReal.coe_ne_top]
        norm_num
  have hrightTop : (δ : ENNReal) ^ (-(7 : ℝ)) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg' (ENNReal.coe_pos.mpr hδ0) ENNReal.coe_ne_top
  have hreal := ENNReal.toReal_mono hrightTop hgoalE
  calc
    (t.card : ℝ) ≤ ((δ : ENNReal) ^ (-(7 : ℝ))).toReal := by
      simpa using hreal
    _ = (δ : ℝ) ^ (-(7 : ℝ)) := by
      rw [← ENNReal.toReal_rpow]
      simp

/-- **(GWZ Lemma 8.1) The coarse factor, for a family in `B_R`** —
`Kakeya.ml1Boot.multiplicity_le_coarse` at an ambient radius `R ≥ 1` (blueprint
`lem:ml1bootCoarseFactorBall`).

Relative to the unit-ball statement: the family lies in `closedBall 0 R`, its Frostman constant
is read against the convex body `closedBall 0 R`, the fullness hypothesis carries the factor `2`
of the low-shading discard, the tube scale satisfies `θ ≤ 1/4` (the side condition of the cell
cover), and the numeric hypothesis pays the cell constant `2 M`, where `M` depends only on `R`.
The conclusion is unchanged. -/
theorem multiplicity_le_coarse_ball [Nontrivial E] (hdim : Module.finrank ℝ E = 3) {γ : ℝ}
    (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) (hKF : FrostmanEstimate.{u} E γ) (R : ℝ) (hR : 1 ≤ R) :
    ∀ e > (0 : ℝ), ∃ ηs > (0 : ℝ),
    ∃ M : ℕ, 0 < M ∧ ∀ L : NNReal, 1 ≤ L → ∀ n₀ a : ℝ, 0 ≤ n₀ → 0 ≤ a →
    ∀ᶠ (δ : NNReal) in 𝓝[>] 0, ∀ θ : NNReal, δ ≤ θ → (θ : ℝ) ≤ 1 / 4 →
      ∀ {κ : Type u} {t : Finset κ} (Tθ : κ → ShadedTube θ E),
        t.Nonempty →
        (∀ l ∈ t, (Tθ l).carrier ⊆ Metric.closedBall 0 R) →
        (t : Set κ).Pairwise
          (fun l l' => IsEssentiallyDistinct (Tθ l).carrier (Tθ l').carrier) →
        frostmanConstIn t (fun l => (Tθ l).toConvexSpaceBody)
            (ConvexSpaceBody.closedBall (0 : E) R (le_trans zero_le_one hR))
          ≤ (L : ENNReal) * (δ : ENNReal) ^ (-n₀) →
        (2 : ENNReal) * (δ : ENNReal) ^ ηs
          ≤ (ShadedBody.fullness t (fun l => (Tθ l).toShadedBody) : ENNReal) →
        (2 * (M : ENNReal) * (L : ENNReal)) * (δ : ENNReal) ^ (-n₀ - e)
          ≤ (δ : ENNReal) ^ (-4 * a) →
        ShadedBody.multiplicity t (fun l => (Tθ l).toShadedBody)
          ≤ (δ : ENNReal) ^ (-4 * a) * (θ : ENNReal) ^ (-2 * γ)
            * ((t.card : ENNReal) * (θ : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2) := by
  classical
  intro e he
  have hn : 1 < Module.finrank ℝ E := by rw [hdim]; norm_num
  obtain ⟨ηs, hηs, hev⟩ :=
    FrostmanEstimate.multiplicity_bound_auxScale_of_isFrostmanIn
      E hγ0 hγ1 hn hKF e he
  have hp0 : (0 : ℝ) ≤ 1 - γ / 2 := by linarith
  have hp1 : (1 - γ / 2 : ℝ) ≤ 1 := by linarith
  -- the cell cover of `B_R`
  obtain ⟨M, hM0, hred⟩ := multiplicity_le_of_ball_of_unitBall (E := E) R hR
  refine ⟨ηs, hηs, M, hM0, ?_⟩
  intro L hL n₀ a hn₀ ha
  filter_upwards [hev, self_mem_nhdsWithin] with δ hδ_aux hδ_pos
  intro θ hδθ hθ4 κ t Tθ htne hball hED hfrost hfull hc
  have hδpos : (0 : NNReal) < δ := hδ_pos
  have hθ0 : 0 < θ := lt_of_lt_of_le hδpos hδθ
  have hθ1 : θ ≤ 1 := by
    rw [← NNReal.coe_le_coe]; push_cast; linarith
  have hδ1 : (δ : ENNReal) ≤ 1 := by exact_mod_cast (le_trans hδθ hθ1)
  have hδ_ne0 : (δ : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr (ne_of_gt hδpos)
  have hδ_ne_top : (δ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  -- the Frostman constant of the whole family
  set C : ENNReal := (L : ENNReal) * (δ : ENNReal) ^ (-n₀) with hC_def
  have hL' : (1 : ENNReal) ≤ (L : ENNReal) := by exact_mod_cast hL
  have h1_le_δinv : 1 ≤ (δ : ENNReal) ^ (-n₀) := by
    calc (1 : ENNReal) = (δ : ENNReal) ^ (0 : ℝ) := by simp
      _ ≤ (δ : ENNReal) ^ (-n₀) :=
        ENNReal.rpow_le_rpow_of_exponent_ge hδ1 (by linarith)
  have hC1 : 1 ≤ C := by
    calc (1 : ENNReal) = 1 * 1 := by simp
      _ ≤ (L : ENNReal) * (δ : ENNReal) ^ (-n₀) := mul_le_mul' hL' h1_le_δinv
  have hCtop : C ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.coe_ne_top (ENNReal.rpow_ne_top_of_ne_zero hδ_ne0 hδ_ne_top)
  -- the family as convex bodies, inside the ambient ball `K`
  set W : κ → ConvexSpaceBody E := fun l => (Tθ l).toConvexSpaceBody with hW_def
  set K : ConvexSpaceBody E := ConvexSpaceBody.closedBall (0 : E) R (le_trans zero_le_one hR)
    with hK_def
  have hWK : ∀ l ∈ t, W l ≤ K := fun l hl x hx => hball l hl hx
  have hFrostK : IsFrostmanIn t W K C := isFrostmanIn_of_frostmanConstIn_le hfrost
  -- all tubes of the family have one and the same carrier volume
  obtain ⟨l₀, hl₀⟩ := htne
  set v₀ : ENNReal := volume (W l₀).carrier with hv₀_def
  have hvolEq : ∀ l, volume (W l).carrier = v₀ := fun l =>
    Tube.volume_carrier_eq_volume_carrier (Tθ l).toTube (Tθ l₀).toTube
  have hv₀pos : 0 < v₀ ∧ v₀ < ⊤ := Tube.volume_pos_and_lt_top hθ0 hθ1 (Tθ l₀).toTube
  have hv₀0 : v₀ ≠ 0 := hv₀pos.1.ne'
  have hv₀top : v₀ ≠ ⊤ := hv₀pos.2.ne
  -- the ambient volumes
  have hK0 : volume K.carrier ≠ 0 := by
    change volume (Metric.closedBall (0 : E) R) ≠ 0
    exact (Metric.measure_closedBall_pos volume 0 (by linarith)).ne'
  have hU0 : volume (ConvexSpaceBody.closedUnitBall (E := E)).carrier ≠ 0 :=
    ConvexSpaceBody.closedUnitBall_volume_pos.ne'
  have hUK : volume (ConvexSpaceBody.closedUnitBall (E := E)).carrier ≤ volume K.carrier := by
    apply measure_mono
    intro x hx
    change x ∈ Metric.closedBall (0 : E) R
    exact Metric.closedBall_subset_closedBall hR hx
  have hKtop : volume K.carrier ≠ ⊤ := K.isCompact.measure_ne_top
  -- the fullness hypothesis, in the shape of the cell cover
  set lam : NNReal := 2 * δ ^ ηs with hlam_def
  have hlam : ((lam : NNReal) : ENNReal) = 2 * (δ : ENNReal) ^ ηs := by
    simp [lam, ENNReal.coe_rpow_of_nonneg _ hηs.le]
  have hfull' : (lam : ENNReal)
      ≤ (ShadedBody.fullness t (fun l => (Tθ l).toShadedBody) : ENNReal) := by
    rw [hlam]; exact hfull
  have hlam_half : ((lam / 2 : NNReal) : ENNReal) = (δ : ENNReal) ^ ηs := by
    rw [hlam_def, mul_div_cancel_left₀ _ (two_ne_zero), ENNReal.coe_rpow_of_nonneg _ hηs.le]
  -- the common bound of every translated cell
  set Bound : ENNReal := (δ : ENNReal) ^ (-e) * C ^ (1 - γ / 2)
      * (θ : ENNReal) ^ (-2 * γ)
      * ((t.card : ENNReal) * (θ : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2) with hBound_def
  have hcell : ∀ (t' : Finset κ) (v : E), t' ⊆ t → t'.Nonempty →
      (∀ l ∈ t', ((Tθ l).translate v).carrier ⊆ Metric.closedBall 0 1) →
      ((lam / 2 : NNReal) : ENNReal)
        ≤ (ShadedBody.fullness t'
            (fun l => ((Tθ l).translate v).toShadedBody) : ENNReal) →
      ShadedBody.multiplicity t' (fun l => ((Tθ l).translate v).toShadedBody) ≤ Bound := by
    intro t' v ht' hne hballcell hfullcell
    set T'' : κ → ShadedTube θ E := fun l => (Tθ l).translate v with hT''_def
    -- essential distinctness is translation invariant
    have hED'' : (t' : Set κ).Pairwise
        (fun l l' => IsEssentiallyDistinct ((T'' l).carrier) ((T'' l').carrier)) := by
      intro l hl l' hl' hll'
      change IsEssentiallyDistinct ((Tθ l).translate v).carrier ((Tθ l').translate v).carrier
      rw [StickyKakeya.shadedTube_translate_carrier, StickyKakeya.shadedTube_translate_carrier]
      exact (isEssentiallyDistinct_translate _ _ v).mpr
        (hED (ht' (Finset.mem_coe.mp hl)) (ht' (Finset.mem_coe.mp hl')) hll')
    -- the cell's share of the volume
    have hcard'0 : (t'.card : ENNReal) ≠ 0 := by
      exact_mod_cast (Finset.card_pos.mpr hne).ne'
    have hcard'top : (t'.card : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top _
    set D : ENNReal := (t.card : ENNReal) / (t'.card : ENNReal) with hD_def
    have hDmul : D * (t'.card : ENNReal) = (t.card : ENNReal) :=
      ENNReal.div_mul_cancel hcard'0 hcard'top
    have hD1 : 1 ≤ D := by
      rw [hD_def, ENNReal.le_div_iff_mul_le (Or.inl hcard'0) (Or.inl hcard'top), one_mul]
      exact_mod_cast Finset.card_le_card ht'
    have hDtop : D ≠ ⊤ := ENNReal.div_ne_top (ENNReal.natCast_ne_top _) hcard'0
    have hsum : ∀ u : Finset κ, ∑ i ∈ u, volume (W i).carrier = (u.card : ENNReal) * v₀ := by
      intro u
      rw [Finset.sum_congr rfl (fun i _ => hvolEq i), Finset.sum_const, nsmul_eq_mul]
    have hvol : (∑ i ∈ t, volume (W i).carrier) ≤ D * ∑ i ∈ t', volume (W i).carrier := by
      rw [hsum, hsum, ← mul_assoc, hDmul]
    -- the translated cell lies in the unit ball
    have hWL : ∀ i ∈ t', (W i).translate v ≤ ConvexSpaceBody.closedUnitBall := by
      intro i hi x hx
      exact hballcell i hi hx
    -- the Frostman bound of the translated cell
    have hFrost'' : IsFrostmanIn t' (fun l => (T'' l).toConvexSpaceBody)
        ConvexSpaceBody.closedUnitBall (C * D) := by
      have h := IsFrostmanIn.translate_of_le_of_subset hFrostK hWK ht' hvol v hWL hK0 hU0
      have hratio : volume (ConvexSpaceBody.closedUnitBall (E := E)).carrier
          / volume K.carrier ≤ 1 := by
        rw [ENNReal.div_le_iff_le_mul (Or.inl hK0) (Or.inl hKtop), one_mul]
        exact hUK
      have hmono : (C * D) * (volume (ConvexSpaceBody.closedUnitBall (E := E)).carrier
          / volume K.carrier) ≤ C * D := mul_le_of_le_one_right' hratio
      exact (h.mono hmono)
    have hCD1 : 1 ≤ C * D := le_trans hC1 (le_mul_of_one_le_right' hD1)
    have hCDtop : C * D ≠ ⊤ := ENNReal.mul_ne_top hCtop hDtop
    have hfull'' : ShadedBody.fullness t' (fun l => (T'' l).toShadedBody)
        ≥ (δ : ENNReal) ^ ηs := by
      rw [← hlam_half]; exact hfullcell
    have hmult := hδ_aux (C * D) hCD1 hCDtop θ hδθ hθ1 t' T'' hne hballcell hED'' hfull''
      hFrost''
    rw [show Module.finrank ℝ E - 1 = 2 from by rw [hdim]] at hmult
    -- the share cancels against the cardinality
    have hcancel : (C * D) ^ (1 - γ / 2) * ((t'.card : ENNReal) * (θ : ENNReal) ^ (2 : ℕ))
          ^ (1 - γ / 2)
        = C ^ (1 - γ / 2) * ((t.card : ENNReal) * (θ : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2) := by
      rw [← ENNReal.mul_rpow_of_nonneg _ _ hp0, ← ENNReal.mul_rpow_of_nonneg _ _ hp0]
      congr 1
      calc C * D * ((t'.card : ENNReal) * (θ : ENNReal) ^ (2 : ℕ))
          = C * ((D * (t'.card : ENNReal)) * (θ : ENNReal) ^ (2 : ℕ)) := by ring
        _ = C * ((t.card : ENNReal) * (θ : ENNReal) ^ (2 : ℕ)) := by rw [hDmul]
    calc ShadedBody.multiplicity t' (fun l => (T'' l).toShadedBody)
        ≤ (δ : ENNReal) ^ (-e) * (C * D) ^ (1 - γ / 2) * (θ : ENNReal) ^ (-2 * γ)
          * ((t'.card : ENNReal) * (θ : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2) := hmult
      _ = (δ : ENNReal) ^ (-e) * (θ : ENNReal) ^ (-2 * γ)
          * ((C * D) ^ (1 - γ / 2)
            * ((t'.card : ENNReal) * (θ : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2)) := by ring
      _ = (δ : ENNReal) ^ (-e) * (θ : ENNReal) ^ (-2 * γ)
          * (C ^ (1 - γ / 2)
            * ((t.card : ENNReal) * (θ : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2)) := by
          rw [hcancel]
      _ = Bound := by rw [hBound_def]; ring
  -- sum over the cells
  have hmain : ShadedBody.multiplicity t (fun l => (Tθ l).toShadedBody)
      ≤ 2 * (M : ENNReal) * Bound :=
    hred hθ0 hθ4 t Tθ hball hfull' hcell
  -- the arithmetic of `multiplicity_le_coarse`, with the cell constant folded into `hc`
  have hCpow_le : C ^ (1 - γ / 2) ≤ C := by
    calc C ^ (1 - γ / 2) ≤ C ^ (1 : ℝ) := ENNReal.rpow_le_rpow_of_exponent_le hC1 hp1
      _ = C := by rw [ENNReal.rpow_one]
  have hpre : 2 * (M : ENNReal) * ((δ : ENNReal) ^ (-e) * C ^ (1 - γ / 2))
      ≤ (δ : ENNReal) ^ (-4 * a) := by
    calc 2 * (M : ENNReal) * ((δ : ENNReal) ^ (-e) * C ^ (1 - γ / 2))
        ≤ 2 * (M : ENNReal) * ((δ : ENNReal) ^ (-e) * C) := by gcongr
      _ = (2 * (M : ENNReal) * (L : ENNReal)) * ((δ : ENNReal) ^ (-e) * (δ : ENNReal) ^ (-n₀)) := by
          rw [hC_def]; ring
      _ = (2 * (M : ENNReal) * (L : ENNReal)) * (δ : ENNReal) ^ (-n₀ - e) := by
          rw [← ENNReal.rpow_add _ _ hδ_ne0 hδ_ne_top]; congr 1; ring
      _ ≤ (δ : ENNReal) ^ (-4 * a) := hc
  calc ShadedBody.multiplicity t (fun l => (Tθ l).toShadedBody)
      ≤ 2 * (M : ENNReal) * Bound := hmain
    _ = 2 * (M : ENNReal) * ((δ : ENNReal) ^ (-e) * C ^ (1 - γ / 2))
        * ((θ : ENNReal) ^ (-2 * γ)
          * ((t.card : ENNReal) * (θ : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2)) := by
        rw [hBound_def]; ring
    _ ≤ (δ : ENNReal) ^ (-4 * a)
        * ((θ : ENNReal) ^ (-2 * γ)
          * ((t.card : ENNReal) * (θ : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2)) := by
        gcongr
    _ = (δ : ENNReal) ^ (-4 * a) * (θ : ENNReal) ^ (-2 * γ)
        * ((t.card : ENNReal) * (θ : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2) := by ring

/-- **The coarse-factor shape is automatic when the tube scale is bounded below.**

For `1 / 4 < θ ≤ 1`, essential distinctness and containment in a fixed ball bound the number of
`θ`-tubes by a constant depending only on the ambient radius.  The trivial multiplicity bound is
therefore absorbed by `δ ^ (-4 a)` for every `a > 0`.  This is the large-scale complement of
`Kakeya.ml1Boot.multiplicity_le_coarse_ball`; no Frostman or fullness input is needed here. -/
theorem eventually_multiplicity_le_coarse_largeScale [Nontrivial E]
    (hdim : Module.finrank ℝ E = 3) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (R : ℝ) (hR : 1 ≤ R) {a : ℝ} (ha : 0 < a) :
    ∀ᶠ (δ : NNReal) in 𝓝[>] 0, ∀ θ : NNReal, (1 / 4 : ℝ) < (θ : ℝ) → θ ≤ 1 →
      ∀ {κ : Type u} {t : Finset κ} (Tθ : κ → ShadedTube θ E),
        t.Nonempty →
        (∀ l ∈ t, (Tθ l).carrier ⊆ Metric.closedBall 0 R) →
        (t : Set κ).Pairwise
          (fun l l' => IsEssentiallyDistinct (Tθ l).carrier (Tθ l').carrier) →
        ShadedBody.multiplicity t (fun l => (Tθ l).toShadedBody)
          ≤ (δ : ENNReal) ^ (-4 * a) * (θ : ENNReal) ^ (-2 * γ)
            * ((t.card : ENNReal) * (θ : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2) := by
  classical
  let ρ₀ : NNReal := 1 / 4
  let D : ℝ := Tube.card_le_of_EssDistinct.C 3
  let N₀ : ℝ := D * (R / (ρ₀ : ℝ)) ^ 6
  let c₁ : ℝ := ((ρ₀ : ℝ) ^ 2) ^ (1 - γ / 2)
  have hρ₀ : 0 < ρ₀ := by simp [ρ₀]
  have hD : 0 < D := by
    simpa [D] using (Tube.card_le_of_EssDistinct.C_pos (n := 3))
  have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hN₀ : 0 < N₀ := by
    exact mul_pos hD (pow_pos (div_pos hR0 (by exact_mod_cast hρ₀)) 6)
  have hp0 : 0 ≤ 1 - γ / 2 := by linarith
  have hc₁ : 0 < c₁ := by
    exact Real.rpow_pos_of_pos (pow_pos (by exact_mod_cast hρ₀) 2) _
  have hconstTop : ENNReal.ofReal (N₀ / c₁) ≠ ⊤ := ENNReal.ofReal_ne_top
  filter_upwards [eventually_finite_const_le_rpow_neg hconstTop (by positivity : 0 < 4 * a),
    self_mem_nhdsWithin] with δ hδabs hδ0
  intro θ hθlarge hθ1 κ t Tθ ht hball hED
  have hθ0 : 0 < θ := by
    exact_mod_cast (lt_trans (by norm_num : (0 : ℝ) < 1 / 4) hθlarge)
  have hρ₀θ : ρ₀ ≤ θ := by
    exact_mod_cast (show (ρ₀ : ℝ) ≤ (θ : ℝ) by simpa [ρ₀] using hθlarge.le)
  have hratio : R / (θ : ℝ) ≤ R / (ρ₀ : ℝ) := by
    exact div_le_div_of_nonneg_left hR0.le (by exact_mod_cast hρ₀) (by exact_mod_cast hρ₀θ)
  have hpow : (R / (θ : ℝ)) ^ 6 ≤ (R / (ρ₀ : ℝ)) ^ 6 :=
    pow_le_pow_left₀ (div_nonneg hR0.le (by exact_mod_cast hθ0.le)) hratio 6
  have hcardReal : (t.card : ℝ) ≤ D * (R / (θ : ℝ)) ^ 6 := by
    simpa [D, hdim] using
      Tube.card_le_of_EssDistinct hθ0 R t (fun l => (Tθ l).toTube) hball hED
  have hcardN₀ : (t.card : ℝ) ≤ N₀ := by
    calc
      (t.card : ℝ) ≤ D * (R / (θ : ℝ)) ^ 6 := hcardReal
      _ ≤ D * (R / (ρ₀ : ℝ)) ^ 6 := mul_le_mul_of_nonneg_left hpow hD.le
      _ = N₀ := rfl
  have hcard1 : (1 : ENNReal) ≤ (t.card : ENNReal) := by
    exact_mod_cast Finset.one_le_card.mpr ht
  have hρpow : (ρ₀ : ENNReal) ^ (2 : ℕ) ≤ (θ : ENNReal) ^ (2 : ℕ) := by
    exact pow_le_pow_left₀ zero_le (by exact_mod_cast hρ₀θ) 2
  have hbracket : (ρ₀ : ENNReal) ^ (2 : ℕ) ≤
      (t.card : ENNReal) * (θ : ENNReal) ^ (2 : ℕ) := by
    calc
      (ρ₀ : ENNReal) ^ (2 : ℕ) = 1 * (ρ₀ : ENNReal) ^ (2 : ℕ) := by simp
      _ ≤ (t.card : ENNReal) * (θ : ENNReal) ^ (2 : ℕ) := mul_le_mul' hcard1 hρpow
  have hc₁E : ENNReal.ofReal c₁ = ((ρ₀ : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2) := by
    rw [show c₁ = ((ρ₀ : ℝ) ^ 2) ^ (1 - γ / 2) from rfl]
    rw [← ENNReal.ofReal_coe_nnreal]
    rw [← ENNReal.ofReal_pow (by exact_mod_cast hρ₀.le)]
    rw [ENNReal.ofReal_rpow_of_pos (pow_pos (by exact_mod_cast hρ₀) 2)]
  have hθloss : (1 : ENNReal) ≤ (θ : ENNReal) ^ (-2 * γ) := by
    rw [show -2 * γ = -(2 * γ) by ring, ENNReal.rpow_neg]
    exact ENNReal.one_le_inv.mpr
      (ENNReal.rpow_le_one (by exact_mod_cast hθ1) (by linarith))
  have hc₁Lower : ENNReal.ofReal c₁ ≤ (θ : ENNReal) ^ (-2 * γ)
      * ((t.card : ENNReal) * (θ : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2) := by
    calc
      ENNReal.ofReal c₁ = ((ρ₀ : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2) := hc₁E
      _ ≤ ((t.card : ENNReal) * (θ : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2) :=
        ENNReal.rpow_le_rpow hbracket hp0
      _ = 1 * ((t.card : ENNReal) * (θ : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2) := by simp
      _ ≤ (θ : ENNReal) ^ (-2 * γ)
          * ((t.card : ENNReal) * (θ : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2) := by gcongr
  have hδabs' : ENNReal.ofReal (N₀ / c₁) ≤ (δ : ENNReal) ^ (-4 * a) := by
    convert hδabs using 1 <;> ring
  calc
    ShadedBody.multiplicity t (fun l => (Tθ l).toShadedBody)
        ≤ (t.card : ENNReal) := ShadedBody.multiplicity_le_card _ _
    _ = ENNReal.ofReal (t.card : ℝ) := by rw [ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal N₀ := ENNReal.ofReal_le_ofReal hcardN₀
    _ = ENNReal.ofReal (N₀ / c₁) * ENNReal.ofReal c₁ := by
      rw [mul_comm, ← ENNReal.ofReal_mul hc₁.le]
      congr 1
      field_simp [hc₁.ne']
    _ ≤ (δ : ENNReal) ^ (-4 * a) * ENNReal.ofReal c₁ := by gcongr
    _ ≤ (δ : ENNReal) ^ (-4 * a) *
        ((θ : ENNReal) ^ (-2 * γ)
          * ((t.card : ENNReal) * (θ : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2)) := by gcongr
    _ = (δ : ENNReal) ^ (-4 * a) * (θ : ENNReal) ^ (-2 * γ)
        * ((t.card : ENNReal) * (θ : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2) := by ring

/- The downstream direct-factor adapter is intentionally excluded from this upstream module.
/-- Current direct-factor adapter for the coarse consumer, conditional only on strict
essential distinctness of the selected coarse nodes.  This hypothesis is deliberately visible:
the current `IsCaseTwoDirectFactors` record supplies every other geometric and analytic premise
below, but contains no body-level ED field. -/
theorem multiplicity_le_coarse_of_directFactors_of_pairwiseED [Nontrivial E]
    (hdim : Module.finrank ℝ E = 3) {γ : ℝ}
    (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) (hKF : FrostmanEstimate.{u} E γ) :
    ∀ e > (0 : ℝ), ∃ ηs > (0 : ℝ),
    ∃ Mc : ℕ, 0 < Mc ∧ ∀ L : NNReal, 1 ≤ L → ∀ n₀ av' : ℝ,
    0 ≤ n₀ → 0 ≤ av' →
    ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
      ∀ {ι : Type u} [DecidableEq ι] {s : Finset ι}
        (T : ι → ShadedTube δ E) {N a b : ℕ} {Cds : NNReal},
        1 ≤ Cds →
        ∀ (𝒰 : Tube.UniformTubeSet s (fun i => (T i).toTube) N Cds)
          (pθ : ι → ι),
        IsCoarseNodeParents 𝒰 a b pθ →
        ∀ {Mf : ℕ}, 0 < Mf → ∀ {tm sf : Finset ι}
          {Zτ : ι → ShadedTube (Tube.gridScale δ N b) E}
          {Zf : ι → ShadedTube δ E} {u : Finset ι} {v : E}
          {tθAct sm : Finset ι}
          {Yc : ι → ShadedTube (Tube.gridScale δ N a) E}
          {Zm : ι → ShadedTube (Tube.gridScale δ N b) E} {kF lM : ι},
        IsCaseTwoDirectFactors s T
          (𝒰.cover.indexSet b) (𝒰.cover.tube b) (𝒰.cover.assign b)
          (𝒰.cover.indexSet a) (𝒰.cover.tube a) pθ
          Mf tm sf Zτ Zf u v tθAct sm Yc Zm kF lM →
        0 < Tube.gridScale δ N b → Tube.gridScale δ N b ≤ 1 →
        δ ≤ Tube.gridScale δ N a →
        ((Tube.gridScale δ N a : NNReal) : ℝ) ≤ 1 / 4 →
        δ ≤ 1 →
        0 < ShadedBody.fullness s (fun i => (T i).toShadedBody) →
        (∀ l ∈ 𝒰.cover.indexSet a,
          (𝒰.cover.tube a l).carrier ⊆ Metric.closedBall 0 4) →
        ∀ {Kcoarse : ENNReal},
        frostmanConstIn (𝒰.cover.indexSet a)
            (fun l => (𝒰.cover.tube a l).toConvexSpaceBody)
            (ConvexSpaceBody.closedBall (0 : E) 4 (by norm_num))
          ≤ Kcoarse →
        (((((((factorOneScale.C u.card (Tube.gridScale δ N b))⁻¹ : NNReal) : ENNReal) *
                  (4 * (Mf : ENNReal))⁻¹) *
                ShadedBody.fullness tm (fun k => (Zτ k).toShadedBody)) *
              ((Cds : ENNReal) ^ 2)⁻¹ *
              ((((factorOneScale.C s.card δ)⁻¹ : NNReal) : ENNReal) *
                ShadedBody.fullness s (fun i => (T i).toShadedBody))) *
              ((Cds : ENNReal) ^ 5)⁻¹)⁻¹ * Kcoarse
          ≤ (L : ENNReal) * (δ : ENNReal) ^ (-n₀) →
        (2 : ENNReal) * (δ : ENNReal) ^ ηs ≤
          (((factorOneScale.C u.card (Tube.gridScale δ N b))⁻¹ : NNReal) : ENNReal) *
            (((1 / 2 : NNReal) : ENNReal) *
              ((((factorOneScale.C s.card δ)⁻¹ : NNReal) : ENNReal) *
                ShadedBody.fullness s (fun i => (T i).toShadedBody))) →
        (2 * (Mc : ENNReal) * (L : ENNReal)) * (δ : ENNReal) ^ (-n₀ - e)
          ≤ (δ : ENNReal) ^ (-4 * av') →
        (tθAct : Set ι).Pairwise
          (fun l l' => IsEssentiallyDistinct (𝒰.cover.tube a l).carrier
            (𝒰.cover.tube a l').carrier) →
        ShadedBody.multiplicity tθAct (fun l => (Yc l).toShadedBody)
          ≤ (δ : ENNReal) ^ (-4 * av') *
            (Tube.gridScale δ N a : ENNReal) ^ (-2 * γ) *
            ((tθAct.card : ENNReal) *
              (Tube.gridScale δ N a : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2) := by
  intro e he
  obtain ⟨ηs, hηs, Mc, hMc, hcoarse⟩ :=
    multiplicity_le_coarse_ball hdim hγ0 hγ1 hKF 4 (by norm_num) e he
  refine ⟨ηs, hηs, Mc, hMc, ?_⟩
  intro L hL n₀ av' hn₀ hav'
  filter_upwards [hcoarse L hL n₀ av' hn₀ hav', self_mem_nhdsWithin]
    with δ hcoarseδ hδ0
  intro ι _ s T N a b Cds hCds 𝒰 pθ hcnp Mf hMf tm sf Zτ Zf u v
    tθAct sm Yc Zm kF lM hfac hτ0 hτ1 hδθ hθ4 hδ1 hfulls hball
    Kcoarse hfixedFrost hFrostPay hfull hfinalPay hEDnodes
  let K : ConvexSpaceBody E := ConvexSpaceBody.closedBall (0 : E) 4 (by norm_num)
  have hnodeK : ∀ l ∈ 𝒰.cover.indexSet a,
      (𝒰.cover.tube a l).toConvexSpaceBody ≤ K := by
    intro l hl
    exact hball l hl
  have hFrostLocal := hfac.coarse_frostman_le T hCds 𝒰 hcnp hMf
    hδ0 hδ1 hτ0 hτ1 hfulls hnodeK hfixedFrost
  have hFrost : frostmanConstIn tθAct (fun l => (Yc l).toConvexSpaceBody) K ≤
      (L : ENNReal) * (δ : ENNReal) ^ (-n₀) :=
    hFrostLocal.trans hFrostPay
  have hfullActual : (2 : ENNReal) * (δ : ENNReal) ^ ηs ≤
      ShadedBody.fullness tθAct (fun l => (Yc l).toShadedBody) :=
    hfull.trans hfac.coarse_factor_fullness
  have hballY : ∀ l ∈ tθAct, (Yc l).carrier ⊆ Metric.closedBall 0 4 := by
    intro l hl
    rw [hfac.coarse_tube l]
    exact hball l (hfac.coarse_subset hl)
  have hEDY : (tθAct : Set ι).Pairwise
      (fun l l' => IsEssentiallyDistinct (Yc l).carrier (Yc l').carrier) := by
    intro l hl l' hl' hll'
    rw [hfac.coarse_tube l, hfac.coarse_tube l']
    exact hEDnodes hl hl' hll'
  exact hcoarseδ (Tube.gridScale δ N a) hδθ hθ4 Yc hfac.coarse_nonempty
    hballY hEDY hFrost hfullActual hfinalPay
-/

end CoarseBall

end ml1Boot

end Kakeya

#print axioms Kakeya.ml1Boot.multiplicity_le_coarse_ball
#print axioms Kakeya.ml1Boot.eventually_multiplicity_le_coarse_largeScale
#print axioms Kakeya.ml1Boot.isEDUpToMult_card
#print axioms Kakeya.ml1Boot.not_card_cap_at_unitScale
