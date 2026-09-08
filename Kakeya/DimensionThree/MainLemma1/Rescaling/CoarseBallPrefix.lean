/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma1.Cases
public import Kakeya.DimensionThree.MainLemma1.Rescaling.BallRadius

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

end CoarseBall

end ml1Boot

end Kakeya
