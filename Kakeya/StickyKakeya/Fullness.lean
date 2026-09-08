/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.FibreCommon

/-!
# Theorem 7.3(A) ⇒ (B): fullness and the Frostman transfers

The shading-side facts: a per-body lower bound for `ShadedBody.fullness'`, the half-mass reduction
to the shade-heavy subfamily, and the two transfers that carry
`Kakeya.StickyKakeya.IsFrostmanAtEveryScale` to a subfamily — to a heavy one, and to a
carrier-deduplicated one.
-/

@[expose] public section

open MeasureTheory
open Tube

namespace Kakeya

open MultiScaleFac

namespace StickyKakeya

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

section stickyKatzTaoOfStickyFrostman

omit [Nontrivial E] in
/-- Per-body lower bound for `fullness'`: if every body's shade volume is at least
`c` times its carrier volume, then `c ≤ fullness' s V` (given the total carrier
volume is positive and finite).  This is the final assembly step for E5: a per-pair
fullness bound (from shaded uniformity) yields the global fullness lower bound. -/
lemma fullness'_ge_of_per_body {ι : Type*} (s : Finset ι)
    (V : ι → ShadedBody E) (c : ENNReal)
    (hpos : 0 < ∑ i ∈ s, MeasureTheory.volume (V i).carrier)
    (htop : (∑ i ∈ s, MeasureTheory.volume (V i).carrier) ≠ ⊤)
    (h : ∀ i ∈ s, c * MeasureTheory.volume (V i).carrier
        ≤ MeasureTheory.volume (V i).shade) :
    c ≤ ShadedBody.fullness' s V := by
  simp only [ShadedBody.fullness']
  rw [ENNReal.le_div_iff_mul_le (Or.inl hpos.ne') (Or.inl htop)]
  calc c * ∑ i ∈ s, MeasureTheory.volume (V i).carrier
      = ∑ i ∈ s, c * MeasureTheory.volume (V i).carrier := by rw [Finset.mul_sum]
    _ ≤ ∑ i ∈ s, MeasureTheory.volume (V i).shade := Finset.sum_le_sum h

omit [Nontrivial E] in
/-- **Heavy-set half-mass** (E5 `s_heavy` reduction): the shade-heavy subset
`s_heavy = {i : τ·carrier ≤ shade}` retains at least half the total shade mass, so
`∑_s shade ≤ 2·∑_{s_heavy} shade`.  This lets the whole assembly run on `s_heavy`, where every tube
is individually heavy, while the conclusion stays about the original `s`. -/
lemma heavy_half_mass {ι : Type*} (s : Finset ι) (V : ι → ShadedBody E) (τ : ENNReal)
    (hfin : ∑ i ∈ s, MeasureTheory.volume (V i).shade ≠ ⊤)
    (hpoor : τ * (∑ i ∈ s, MeasureTheory.volume (V i).carrier)
        ≤ (1 / 2 : ENNReal) * ∑ i ∈ s, MeasureTheory.volume (V i).shade) :
    ∑ i ∈ s, MeasureTheory.volume (V i).shade
      ≤ 2 * ∑ i ∈ s.filter (fun i =>
            τ * MeasureTheory.volume (V i).carrier ≤ MeasureTheory.volume (V i).shade),
          MeasureTheory.volume (V i).shade := by
  classical
  set sh : ι → ENNReal := fun i => MeasureTheory.volume (V i).shade with hsh_def
  set ca : ι → ENNReal := fun i => MeasureTheory.volume (V i).carrier with hca_def
  set P : ι → Prop := fun i => τ * ca i ≤ sh i with hP_def
  set T : ENNReal := ∑ i ∈ s, sh i with hT_def
  set H : ENNReal := ∑ i ∈ s.filter P, sh i with hH_def
  have hsplit : T = H + ∑ i ∈ s.filter (fun i => ¬ P i), sh i :=
    (Finset.sum_filter_add_sum_filter_not s P sh).symm
  have hpoor_sum : ∑ i ∈ s.filter (fun i => ¬ P i), sh i ≤ (1 / 2 : ENNReal) * T := by
    refine le_trans ?_ hpoor
    calc ∑ i ∈ s.filter (fun i => ¬ P i), sh i
        ≤ ∑ i ∈ s.filter (fun i => ¬ P i), τ * ca i := by
          refine Finset.sum_le_sum (fun i hi => ?_)
          have hnP : ¬ P i := (Finset.mem_filter.mp hi).2
          simp only [hP_def, not_le] at hnP
          exact hnP.le
      _ = τ * ∑ i ∈ s.filter (fun i => ¬ P i), ca i := by rw [Finset.mul_sum]
      _ ≤ τ * ∑ i ∈ s, ca i :=
          mul_le_mul_right (Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)) τ
  have hle : T ≤ H + (1 / 2 : ENNReal) * T := by
    calc T = H + ∑ i ∈ s.filter (fun i => ¬ P i), sh i := hsplit
      _ ≤ H + (1 / 2 : ENNReal) * T := by gcongr
  have hhalf_fin : (1 / 2 : ENNReal) * T ≠ ⊤ := ENNReal.mul_ne_top (by norm_num) hfin
  have h2half : (2 : ENNReal) * (1 / 2 : ENNReal) = 1 := by
    rw [mul_one_div, ENNReal.div_self (by norm_num) (by norm_num)]
  have hTsum : (1 / 2 : ENNReal) * T + (1 / 2 : ENNReal) * T = T := by
    rw [← two_mul, ← mul_assoc, h2half, one_mul]
  have hcancel : (1 / 2 : ENNReal) * T ≤ H := by
    have hle' : (1 / 2 : ENNReal) * T + (1 / 2 : ENNReal) * T ≤ H + (1 / 2 : ENNReal) * T := by
      rw [hTsum]; exact hle
    exact (ENNReal.add_le_add_iff_right hhalf_fin).mp hle'
  calc T = 2 * ((1 / 2 : ENNReal) * T) := by rw [← mul_assoc, h2half, one_mul]
    _ ≤ 2 * H := mul_le_mul_right hcancel 2

omit [Nontrivial E] in
/-- **Frostman transfer to a heavy subfamily.**  If `t ⊆ s'` and, per anchor `(ρ, i₀)`, the
filtered volume of `s'` is `≤ C'·` that of `t` (the per-anchor heaviness), then the
`C`-Frostman family `s'` gives a `C·C'`-Frostman `t`.  Isolates the per-anchor heaviness
as a single clean hypothesis (the GWZ "harmless refinement"); `C'` is meant to be the
already-absorbed `δ^(-(η₁-(n+3)ε))`. -/
private lemma isFrostmanAtEveryScale_of_subset_heavy {δ : NNReal} {ι : Type*}
    {s' t : Finset ι} (hts : t ⊆ s') {T : ι → Tube δ E} {C C' : ENNReal}
    (h : IsFrostmanAtEveryScale s' T C)
    (h_heavy : ∀ ρ : NNReal, δ ≤ ρ → ρ ≤ 1 → ∀ i₀ ∈ t,
        (∑ i ∈ s'.filter (fun i =>
            (T i).toConvexSpaceBody ≤ (Tube.rescale (T i₀) ρ).toConvexSpaceBody),
          MeasureTheory.volume (T i).toConvexSpaceBody.carrier)
        ≤ C' * ∑ i ∈ t.filter (fun i =>
            (T i).toConvexSpaceBody ≤ (Tube.rescale (T i₀) ρ).toConvexSpaceBody),
          MeasureTheory.volume (T i).toConvexSpaceBody.carrier) :
    IsFrostmanAtEveryScale t T (C * C') := by
  intro ρ hρ hρ' i₀ hi₀
  refine (h ρ hρ hρ' i₀ (hts hi₀)).of_subset (Finset.filter_subset_filter _ hts) ?_
  simpa only [Finset.filter_filter, and_self] using h_heavy ρ hρ hρ' i₀ hi₀

omit [Nontrivial E] in
open Classical in
/-- **Per-cap mass retention under carrier dedup** (E7 route, `h_heavy` input).  If the
carrier-injective `s_inj ⊆ s_src` covers every carrier of `s_src`, then in every cap `K` the total
body volume of `s_src` is at most `Cmax` times that of `s_inj`, where `Cmax` bounds
`maxDensity s_src W`: each carrier class has cardinality `≤ Cmax` and lies entirely inside or
entirely outside the cap-filter, so the sum may be taken class by class. -/
private lemma sum_volume_le_of_carrier_cover
    {ι : Type*} (s_src s_inj : Finset ι) (W : ι → ConvexSpaceBody E)
    (hcover : ∀ p ∈ s_src, ∃ q ∈ s_inj, (W p).carrier = (W q).carrier)
    (hpos : ∀ q ∈ s_inj, 0 < MeasureTheory.volume (W q).carrier)
    (hfin : ∀ q ∈ s_inj, MeasureTheory.volume (W q).carrier ≠ ⊤)
    (Cmax : ENNReal) (h_md : Kakeya.maxDensity s_src W ≤ Cmax)
    (K : ConvexSpaceBody E) :
    (∑ p ∈ s_src.filter (fun p => W p ≤ K), MeasureTheory.volume (W p).carrier)
      ≤ Cmax * ∑ q ∈ s_inj.filter (fun q => W q ≤ K),
          MeasureTheory.volume (W q).carrier := by
  classical
  have h_class : ∀ q ∈ s_inj,
      ((s_src.filter (fun p => (W p).carrier = (W q).carrier)).card : ENNReal) ≤ Cmax := by
    intro q hq
    have hcount := Kakeya.densityIn_ge_of_count_volume (s := s_src) (W := W)
        (K := W q) (t := s_src.filter (fun p => (W p).carrier = (W q).carrier))
        (vmin := MeasureTheory.volume (W q).carrier)
        (Finset.filter_subset _ _)
        (fun i hi => le_of_eq (SetLike.coe_injective (Finset.mem_filter.mp hi).2))
        (fun i hi => (congrArg MeasureTheory.volume (Finset.mem_filter.mp hi).2).symm.le)
    rw [mul_div_assoc, ENNReal.div_self (hpos q hq).ne' (hfin q hq), mul_one] at hcount
    exact le_trans hcount (le_trans (Kakeya.le_maxDensity s_src W (W q)) h_md)
  have h_body_eq : ∀ p q : ι, (W p).carrier = (W q).carrier → W p = W q :=
    fun p q h => SetLike.coe_injective h
  have h_vol_eq : ∀ p q : ι, (W p).carrier = (W q).carrier →
      MeasureTheory.volume (W p).carrier = MeasureTheory.volume (W q).carrier :=
    fun p q h => by rw [h_body_eq p q h]
  set T := s_src.filter (fun p => W p ≤ K) with hT_def
  set J := s_inj.filter (fun q => W q ≤ K) with hJ_def
  have h_cov : T ⊆ J.biUnion (fun q => s_src.filter (fun p => (W p).carrier = (W q).carrier)) := by
    intro p hp
    rw [hT_def] at hp
    rcases Finset.mem_filter.mp hp with ⟨hp_src, hp_le⟩
    obtain ⟨q, hq_inj, h_eq⟩ := hcover p hp_src
    have hq_body : W p = W q := h_body_eq p q h_eq
    have hq_le : W q ≤ K := by
      rw [← hq_body]
      exact hp_le
    have hq_in_J : q ∈ J := by
      rw [hJ_def]
      exact Finset.mem_filter.mpr ⟨hq_inj, hq_le⟩
    have hp_in_class : p ∈ s_src.filter (fun p' => (W p').carrier = (W q).carrier) :=
      Finset.mem_filter.mpr ⟨hp_src, h_eq⟩
    exact Finset.mem_biUnion.mpr ⟨q, hq_in_J, hp_in_class⟩
  choose! g hg_mem hg_eq using hcover
  have h_mapsTo : ∀ p ∈ T, g p ∈ J := by
    intro p hp
    rw [hT_def] at hp
    rcases Finset.mem_filter.mp hp with ⟨hp_src, hp_le⟩
    have h_eq : (W p).carrier = (W (g p)).carrier := hg_eq p hp_src
    have h_body : W p = W (g p) := h_body_eq p (g p) h_eq
    have h_g_le : W (g p) ≤ K := by
      rw [← h_body]; exact hp_le
    rw [hJ_def]
    exact Finset.mem_filter.mpr ⟨hg_mem p hp_src, h_g_le⟩
  have h_fiber_eq : ∑ q ∈ J, ∑ p ∈ T with g p = q, MeasureTheory.volume (W p).carrier
      = ∑ p ∈ T, MeasureTheory.volume (W p).carrier :=
    Finset.sum_fiberwise_of_maps_to h_mapsTo (fun p => MeasureTheory.volume (W p).carrier)
  have h_fiber_bound : ∀ q ∈ J,
      ∑ p ∈ T with g p = q, MeasureTheory.volume (W p).carrier
      ≤ Cmax * MeasureTheory.volume (W q).carrier := by
    intro q hq
    rw [hJ_def] at hq
    rcases Finset.mem_filter.mp hq with ⟨hq_inj, hq_le⟩
    have h_fiber_sub_class : (T.filter (fun p => g p = q)) ⊆
        s_src.filter (fun p => (W p).carrier = (W q).carrier) := by
      intro p hp
      rw [Finset.mem_filter] at hp
      rcases hp with ⟨hpT, hgp_eq⟩
      rw [hT_def] at hpT
      rcases Finset.mem_filter.mp hpT with ⟨hp_src, _⟩
      have h_eq_carrier : (W p).carrier = (W q).carrier := by
        calc
          (W p).carrier = (W (g p)).carrier := hg_eq p hp_src
          _ = (W q).carrier := by rw [hgp_eq]
      exact Finset.mem_filter.mpr ⟨hp_src, h_eq_carrier⟩
    have h_vol_fiber : ∀ p ∈ T.filter (fun p => g p = q),
        MeasureTheory.volume (W p).carrier = MeasureTheory.volume (W q).carrier := by
      intro p hp
      rw [Finset.mem_filter] at hp
      rcases hp with ⟨hpT, hgp_eq⟩
      rw [hT_def] at hpT
      rcases Finset.mem_filter.mp hpT with ⟨hp_src, _⟩
      have h_eq_carrier : (W p).carrier = (W q).carrier := by
        calc
          (W p).carrier = (W (g p)).carrier := hg_eq p hp_src
          _ = (W q).carrier := by rw [hgp_eq]
      exact h_vol_eq p q h_eq_carrier
    calc
      ∑ p ∈ T with g p = q, MeasureTheory.volume (W p).carrier
          = ((T.filter (fun p => g p = q)).card : ENNReal) *
            MeasureTheory.volume (W q).carrier := by
            rw [Finset.sum_congr rfl h_vol_fiber, Finset.sum_const, nsmul_eq_mul]
      _ ≤ ((s_src.filter (fun p => (W p).carrier = (W q).carrier)).card : ENNReal) *
          MeasureTheory.volume (W q).carrier := by
        refine mul_le_mul_left (Nat.cast_le.mpr ?_) _
        exact Finset.card_le_card h_fiber_sub_class
      _ ≤ Cmax * MeasureTheory.volume (W q).carrier :=
        mul_le_mul_of_nonneg_right (h_class q hq_inj) (by positivity)
  calc
    (∑ p ∈ T, MeasureTheory.volume (W p).carrier)
        = ∑ q ∈ J, ∑ p ∈ T with g p = q, MeasureTheory.volume (W p).carrier := by
        rw [h_fiber_eq]
    _ ≤ ∑ q ∈ J, Cmax * MeasureTheory.volume (W q).carrier :=
      Finset.sum_le_sum h_fiber_bound
    _ = Cmax * ∑ q ∈ J, MeasureTheory.volume (W q).carrier := by
      rw [Finset.mul_sum]
    _ = Cmax * ∑ q ∈ s_inj.filter (fun q => W q ≤ K), MeasureTheory.volume (W q).carrier := rfl

/-- **Frostman transfers to a carrier-dedup subfamily** (E7 route, replacing the E6
uniform/telescoping route).  If `s_inj ⊆ s_src` meets every carrier class of `s_src` and `s_src` has
`maxDensity ≤ Cmax`, then `s_src`'s Frostman constant `C` transfers to `s_inj` at the cost of a
single extra factor `Cmax`.  This is what makes the *paper's* route work. -/
lemma isFrostmanAtEveryScale_of_carrier_dedup
    {δ : NNReal} (hδ_pos : 0 < δ) {ι : Type*}
    (s_src s_inj : Finset ι) (T : ι → Tube δ E)
    (hsub : s_inj ⊆ s_src)
    (hcover : ∀ p ∈ s_src, ∃ q ∈ s_inj, (T p).carrier = (T q).carrier)
    (Cmax : ENNReal)
    (h_md : Kakeya.maxDensity s_src (fun p => (T p).toConvexSpaceBody) ≤ Cmax)
    (C : ENNReal) (h_frost : IsFrostmanAtEveryScale s_src T C) :
    IsFrostmanAtEveryScale s_inj T (C * Cmax) := by
  apply isFrostmanAtEveryScale_of_subset_heavy hsub h_frost (C' := Cmax)
  intro ρ hρ hρ' i₀ hi₀
  have hpos_nn : 0 < (Tube.le_volume.c (Module.finrank ℝ E) : NNReal) *
    δ ^ (Module.finrank ℝ E - 1) :=
    mul_pos (Tube.le_volume.c_pos (Module.finrank ℝ E)) (pow_pos hδ_pos _)
  have hpos : ∀ q ∈ s_inj, 0 < MeasureTheory.volume ((T q).toConvexSpaceBody).carrier := by
    intro q hq
    have hpos_lower : 0 < (Tube.le_volume.c (Module.finrank ℝ E) : ENNReal) *
    (δ : ENNReal) ^ (Module.finrank ℝ E - 1) := by
      simpa using ENNReal.coe_pos.mpr hpos_nn
    have h_le := Tube.le_volume (T q)
    have hvol_pos : 0 < MeasureTheory.volume (T q).carrier :=
      lt_of_lt_of_le hpos_lower h_le
    simpa
  have hfin : ∀ q ∈ s_inj, MeasureTheory.volume ((T q).toConvexSpaceBody).carrier ≠ ⊤ := by
    intro q hq
    have hfin' : MeasureTheory.volume (T q).carrier ≠ ⊤ :=
      (T q).isCompact.measure_lt_top.ne
    simpa
  have hcover' : ∀ p ∈ s_src, ∃ q ∈ s_inj,
    ((T p).toConvexSpaceBody).carrier = ((T q).toConvexSpaceBody).carrier := by
    intro p hp
    rcases hcover p hp with ⟨q, hq, h⟩
    exact ⟨q, hq, by simpa using h⟩
  have hsum := sum_volume_le_of_carrier_cover s_src s_inj (fun p => (T p).toConvexSpaceBody)
    hcover' hpos hfin Cmax h_md ((Tube.rescale (T i₀) ρ).toConvexSpaceBody)
  simpa using hsum
end stickyKatzTaoOfStickyFrostman

end StickyKakeya

end Kakeya
