/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Sticky
public import Kakeya.StickyKakeya.Absorption
public import Kakeya.StickyKakeya.Assembly
public import Kakeya.StickyKakeya.Constants
public import Kakeya.StickyKakeya.Counting
public import Kakeya.StickyKakeya.Fullness
public import Kakeya.StickyKakeya.Lemma75
public import Kakeya.StickyKakeya.Step1
public import Kakeya.StickyKakeya.BallReduction
public import Kakeya.StickyKakeya.CrossScale

/-!
# Sticky Kakeya: Theorem 7.3(A) ⇒ Theorem 7.3(B)

The implication recorded in the GWZ paper at Theorem 7.3: part (A) (the sticky Frostman
estimate) implies part (B) (the sticky Katz–Tao estimate).  The two parts are defined in
`Kakeya/Sticky.lean` as `StickyKakeya.StickyFrostmanEstimate` and
`StickyKakeya.StickyKatzTaoEstimate`.

The implication is dimension-free: both estimates are stated for an arbitrary finite-dimensional
`E`, so the reduction below never uses `Module.finrank ℝ E = 3`.  Only part (A) itself is
three-dimensional, and it is a hypothesis here.
-/

@[expose] public section

open MeasureTheory
open Tube

open Kakeya.StickyKakeya
open Kakeya.MultiScaleFac

namespace StickyKakeya

/-! ## Structure of the proof of GWZ Theorem 7.3 (A) ⇒ (B)

The proof follows the paper (section7.tex L186–L199) literally, as three steps, plus a trivial
reduction.

* **Step 1** (paper L188): apply GWZ Lemma 7.5 to the Katz–Tao family `(𝕋, Y)`, producing a
  finite translation set `R` and a refined family `𝕋' = ⋃ⱼ Rⱼ(𝕋)` that is uniform,
  fullness-preserving (`λ(𝕋', Y') = λ(𝕋, Y)`), and Frostman at every scale with error
  `δ^{-η₁}`.  This is the paper's main content.
* **Step 2** (paper L191): apply Theorem 7.3(A) to `(𝕋', Y')`, giving `δ^ε ≤ |U(𝕋', Y')|`.
* **Step 3** (paper L194–L196): average back via Lebesgue translation invariance,
  `|U(𝕋', Y')| ≤ |R| · |U(𝕋, Y)|`, combined with the packing cardinality bound
  `|R| · |s| · δ^{n-1} ≲ 1`.

Two points where the Lean argument departs from the paper.  The refined family is reindexed by
`Fin n'`, whose universe must be bridged to the one part (A) quantifies over; this is done with
`ULift`.  And the paper's "harmless refinement to make `μ(T, Y)(x)` roughly constant" is
unnecessary, because `ShadedBody.multiplicity` is already the average `(∑ |shade|) / |U|`, so the
reduction `μ ≤ δ^{-ε} ⇔ ∑ |shade| ≤ δ^{-ε} · |U|` is available directly.
-/

/-- **GWZ Theorem 7.3: part (A) implies part (B).**  The sticky Frostman estimate
`StickyKakeya.StickyFrostmanEstimate` implies the sticky Katz–Tao estimate
`StickyKakeya.StickyKatzTaoEstimate`.  Stated for an arbitrary `E`, since the reduction is
dimension-free; the three-dimensionality lives in part (A). -/
theorem stickyKatzTaoEstimate_of_stickyFrostmanEstimate.{uE}
    {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E] :
    StickyFrostmanEstimate.{uE, uE} (E := E)
      → StickyKatzTaoEstimate.{uE} (E := E) := by
  intro hA ε hε
  obtain ⟨η₁, δ₀_A, hη₁_pos, hδ₀_A_pos, hA_apply⟩ := hA (ε / 2 / 2) (half_pos (half_pos hε))
  set M_outer : ℕ := gridLen (Module.finrank ℝ E) η₁ (ε / 2) with hM_outer_def
  set δ₀_quarter : ℝ := (1/8 : ℝ) ^ M_outer with hδ₀_quarter_def
  have hδ₀_quarter_pos : 0 < δ₀_quarter := by
    rw [hδ₀_quarter_def]; positivity
  have hssfδ₀_pos :
      0 < ssfδ₀ (E := E) η₁ (ε / 2) :=
    ssfδ₀_pos (E := E) η₁ (ε / 2)
  have hM_outer_pos_nat : 0 < M_outer := by
    rw [hM_outer_def]
    exact gridLen_pos _ _ _
  have hM_outer_pos : (0 : ℝ) < (M_outer : ℝ) := by exact_mod_cast hM_outer_pos_nat
  have hMinv_pos : (0 : ℝ) < 1 / (M_outer : ℝ) := one_div_pos.mpr hM_outer_pos
  have hMsq_pos : (0 : ℝ) < (1 / (M_outer : ℝ)) ^ 2 := pow_pos hMinv_pos 2
  set η_B : ℝ := min (min (η₁ / 2) ((1 / (M_outer : ℝ)) ^ 2 / 4)) (ε / 16) with hη_B_def
  have hη_B_pos : 0 < η_B :=
    lt_min (lt_min (half_pos hη₁_pos) (div_pos hMsq_pos (by norm_num)))
      (div_pos hε (by norm_num))
  have hη_B_two_lt_sq : 2 * η_B < (1 / (M_outer : ℝ)) ^ 2 := by
    have h1 : η_B ≤ (1 / (M_outer : ℝ)) ^ 2 / 4 := (min_le_left _ _).trans (min_le_right _ _)
    linarith
  have hη_B_lt_η₁ : η_B < η₁ :=
    lt_of_le_of_lt ((min_le_left _ _).trans (min_le_left _ _)) (half_lt_self hη₁_pos)
  have hη_B_le_η₁ : η_B ≤ η₁ := hη_B_lt_η₁.le
  have hη_B_lt_sq : η_B < (1 / (M_outer : ℝ)) ^ 2 :=
    lt_of_le_of_lt (le_mul_of_one_le_left hη_B_pos.le one_le_two) hη_B_two_lt_sq
  have hη_B_le_sixteenth : η_B ≤ ε / 16 := min_le_right _ _
  have hA_pos : (0 : ℝ) < (Module.finrank ℝ E : ℝ) - 1 + η_B + 1 := by
    have hfr : (1 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := by exact_mod_cast Module.finrank_pos
    linarith
  have hgrid_lt : 1 / ((gridLen
      (Module.finrank ℝ E) η₁ (ε / 2) : ℕ) : ℝ) < (ε / 2) / 4 :=
    one_div_gridLen_lt
      (Module.finrank ℝ E) η₁ (half_pos hε)
  obtain ⟨δ₀_abs, hδ₀_abs_pos, hδ₀_abs_spec⟩ :=
    e2_absorb_threshold
      (E := E) (ε / 2) η_B η₁ (half_pos hε) hη_B_pos
      (by linarith [hη_B_le_sixteenth, hgrid_lt])
  obtain ⟨δ₀_dmax, hδ₀_dmax_pos, hδ₀_dmax_spec⟩ :=
    dmax_absorb_threshold
      (E := E) η_B η₁ (ε / 2) hη₁_pos hη_B_pos hη_B_lt_sq
  obtain ⟨δ₀_dmax2, hδ₀_dmax2_pos, hδ₀_dmax2_spec⟩ :=
    const_absorb_threshold
      (crossScaleConst (Module.finrank ℝ E)
        * (2 * (Tube.overlapConstBOTight (Module.finrank ℝ E) : NNReal)))
      (2 * η_B) ((1 / (M_outer : ℝ)) ^ 2) hη_B_two_lt_sq
  obtain ⟨δ₀_grid, hδ₀_grid_pos, hδ₀_grid_spec⟩ :=
    exists_threshold_le_ssfGridLen (3 * (Module.finrank ℝ E : ℝ) / η_B)
  have hqC_ge1 : (1 : ℝ) ≤ qCardConst (Module.finrank ℝ E) M_outer (cnEff (Module.finrank ℝ E))
      (prodConst (Module.finrank ℝ E) M_outer) :=
    one_le_qCardConst (Module.finrank ℝ E) M_outer (cnEff (Module.finrank ℝ E))
      (prodConst (Module.finrank ℝ E) M_outer)
  have hC₀_ge1 : (1 : ℝ) ≤ (((2 * Tube.overlapConstBO (Module.finrank ℝ E)) ^ 2 : ℕ) : ℝ)
      * (qCardConst (Module.finrank ℝ E) M_outer (cnEff (Module.finrank ℝ E))
            (prodConst (Module.finrank ℝ E) M_outer) *
        (MeasureTheory.volume.real (Metric.closedBall (0 : E) 2)
            / (Tube.le_volume.c (Module.finrank ℝ E) : ℝ) + 1)) := by
    have hX : (1 : ℝ) ≤ (((2 * Tube.overlapConstBO (Module.finrank ℝ E)) ^ 2 : ℕ) : ℝ) := by
      have h0 : 0 < Tube.overlapConstBO (Module.finrank ℝ E) := by
        unfold Tube.overlapConstBO; positivity
      exact_mod_cast Nat.one_le_pow 2 _ (by omega)
    have hge0 : (0 : ℝ) ≤ MeasureTheory.volume.real (Metric.closedBall (0 : E) 2)
        / (Tube.le_volume.c (Module.finrank ℝ E) : ℝ) := by positivity
    exact one_le_mul_of_one_le_of_one_le hX
      (one_le_mul_of_one_le_of_one_le hqC_ge1 (le_add_of_nonneg_left hge0))
  obtain ⟨δ₀_k, hδ₀_k_pos, hk_spec⟩ :=
    kpoly_subpoly η₁ η_B
      ((Module.finrank ℝ E : ℝ) - 1 + η_B + 1)
      ((((2 * Tube.overlapConstBO (Module.finrank ℝ E)) ^ 2 : ℕ) : ℝ)
        * (qCardConst (Module.finrank ℝ E) M_outer (cnEff (Module.finrank ℝ E))
              (prodConst (Module.finrank ℝ E) M_outer) *
          (MeasureTheory.volume.real (Metric.closedBall (0 : E) 2)
              / (Tube.le_volume.c (Module.finrank ℝ E) : ℝ) + 1)))
      hη_B_lt_η₁ hA_pos hC₀_ge1
  set δ₀_two : ℝ := (1 / 2 : ℝ) ^ (2 / ε) with hδ₀_two_def
  have hδ₀_two_pos : 0 < δ₀_two := by rw [hδ₀_two_def]; positivity
  set δ₀_B : ℝ := min (min (min (min δ₀_A δ₀_quarter)
      (ssfδ₀ (E := E) η₁ (ε / 2) : ℝ))
      δ₀_abs) δ₀_dmax
    with hδ₀_B_def
  have hδ₀_B_pos : 0 < δ₀_B :=
    lt_min (lt_min (lt_min (lt_min hδ₀_A_pos hδ₀_quarter_pos)
      (by exact_mod_cast hssfδ₀_pos)) hδ₀_abs_pos) hδ₀_dmax_pos
  obtain ⟨δ₀_e6, hδ₀_e6_pos, hδ₀_e6_spec⟩ :=
    e6_thresholds (E := E) η₁ hη₁_pos
  have hη_F_pos : 0 < 2 * ((Module.finrank ℝ E : ℝ) + 3) * (1 / (M_outer : ℝ)) :=
    mul_pos (by positivity) hMinv_pos
  have hη_D_pos : 0 < ((Module.finrank ℝ E : ℝ) + 3) * (1 / (M_outer : ℝ)) :=
    mul_pos (by positivity) hMinv_pos
  have hη_budget : 2 * (2 * ((Module.finrank ℝ E : ℝ) + 3) * (1 / (M_outer : ℝ)))
      + 2 * (((Module.finrank ℝ E : ℝ) + 3) * (1 / (M_outer : ℝ))) < η₁ := by
    have h6 : 6 * ((Module.finrank ℝ E : ℝ) + 3) * (1 / (M_outer : ℝ)) < η₁ := by
      rw [hM_outer_def]
      exact six_np3_mul_one_div_gridLen_lt
        (Module.finrank ℝ E) η₁ (ε / 2) hη₁_pos
    calc 2 * (2 * ((Module.finrank ℝ E : ℝ) + 3) * (1 / (M_outer : ℝ)))
          + 2 * (((Module.finrank ℝ E : ℝ) + 3) * (1 / (M_outer : ℝ)))
        = 6 * ((Module.finrank ℝ E : ℝ) + 3) * (1 / (M_outer : ℝ)) := by ring
      _ < η₁ := h6
  have hR_br : (1 : ℝ) ≤ ((M_outer : ℕ) : ℝ) + 1 :=
    le_add_of_nonneg_left (Nat.cast_nonneg _)
  obtain ⟨δ₀_br, hδ₀_br_pos, hbr⟩ :=
    exists_union_volume_ge_of_ball (E := E) η₁ (ε / 2 / 2) hη₁_pos
      η_B (2 * ((Module.finrank ℝ E : ℝ) + 3) * (1 / (M_outer : ℝ)))
      (((Module.finrank ℝ E : ℝ) + 3) * (1 / (M_outer : ℝ)))
      hη_B_pos hη_B_lt_η₁ hη_F_pos hη_D_pos hη_budget
      ((Module.finrank ℝ E : ℝ) + ε / 2 - ε / 2 / 2) (((M_outer : ℕ) : ℝ) + 1) hR_br
  set δ₀_Cvol : ℝ := (Tube.volume_le.C (Module.finrank ℝ E) : ℝ) with hδ₀_Cvol_def
  have hδ₀_Cvol_pos : 0 < δ₀_Cvol := by
    rw [hδ₀_Cvol_def]
    unfold Tube.volume_le.C
    positivity
  set δ₀_B2 : ℝ := min (min (min δ₀_B (min δ₀_k δ₀_two)) δ₀_e6) (min δ₀_br δ₀_Cvol)
    with hδ₀_B2_def
  have hδ₀_B2_pos : 0 < δ₀_B2 :=
    lt_min (lt_min (lt_min hδ₀_B_pos (lt_min hδ₀_k_pos hδ₀_two_pos)) hδ₀_e6_pos)
      (lt_min hδ₀_br_pos hδ₀_Cvol_pos)
  set δ₀_B3 : ℝ := min δ₀_B2 (min δ₀_dmax2 δ₀_grid) with hδ₀_B3_def
  have hδ₀_B3_pos : 0 < δ₀_B3 :=
    lt_min hδ₀_B2_pos (lt_min hδ₀_dmax2_pos hδ₀_grid_pos)
  refine ⟨η_B, δ₀_B3, hη_B_pos, hδ₀_B3_pos, ?_⟩
  intro δ hδ_pos hδ_le_thr3 ι s V hT_in_unit C_unif 𝒱 hLam hKT_leaf hKT_nodes
  simp only [hδ₀_B3_def, hδ₀_B2_def, hδ₀_B_def, hδ₀_quarter_def, hδ₀_Cvol_def,
    le_min_iff] at hδ_le_thr3
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hδ_le_δ₀_A, hδ_le_quarter⟩, hδ_le_inner'⟩, hδ_le_abs⟩, hδ_le_dmax⟩,
    hδ_le_k, hδ_le_two⟩, hδ_le_e6⟩, hδ_le_br, hδ_le_Cvol⟩, hδ_le_dmax2, hδ_le_grid⟩ :=
    hδ_le_thr3
  have hδ_le_inner : δ ≤ ssfδ₀ (E := E) η₁ (ε / 2) := by exact_mod_cast hδ_le_inner'
  obtain ⟨hδ_thresh, hδ_ratio_thresh, hMout_large⟩ := hδ₀_e6_spec δ hδ_pos hδ_le_e6
  have hδ_pos_real : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ_pos
  have hδ_lt_one_real : (δ : ℝ) < 1 :=
    hδ_le_quarter.trans_lt (pow_lt_one₀ (by norm_num) (by norm_num)
      (by rw [hM_outer_def]; omega))
  have hδ_lt_one : δ < 1 := by exact_mod_cast hδ_lt_one_real
  rw [ShadedBody.multiplicity_le_iff]
  set s_heavy : Finset ι :=
    s.filter (fun i => ENNReal.ofReal ((δ : ℝ) ^ η_B / 2)
        * MeasureTheory.volume ((V i).toShadedBody).carrier
      ≤ MeasureTheory.volume ((V i).toShadedBody).shade) with hsh_def
  have hsh_sub : s_heavy ⊆ s := Finset.filter_subset _ _
  have hT_heavy : ∀ i ∈ s_heavy, (V i).carrier ⊆ Metric.closedBall (0 : E) 1 :=
    fun i hi => hT_in_unit i (hsh_sub hi)
  have hKT_heavy : ∀ k : ℕ, k ≤ gridLen (Module.finrank ℝ E) η₁ (ε / 2) →
      HasNodeCoverAt s_heavy (fun i => (V i).toTube)
        (δ ^ ((k : ℝ) / ((gridLen (Module.finrank ℝ E) η₁ (ε / 2) : ℕ) : ℝ)))
        ((δ : ℝ) ^ (-(η_B / (3 * (Module.finrank ℝ E : ℝ)))))
        (ENNReal.ofReal ((δ : ℝ) ^ (-η_B))) := by
    intro k hk
    have hgrid_le : 3 * (Module.finrank ℝ E : ℝ) / η_B ≤ (ssfGridLen δ : ℝ) :=
      hδ₀_grid_spec hδ_pos hδ_le_grid
    have hn_pos_real : (0 : ℝ) < (Module.finrank ℝ E : ℝ) := by
      exact_mod_cast Module.finrank_pos (R := ℝ) (M := E)
    have hpos : (0 : ℝ) < 3 * (Module.finrank ℝ E : ℝ) / η_B :=
      div_pos (by positivity) hη_B_pos
    have hG_pos : 0 < ssfGridLen δ := by
      exact_mod_cast lt_of_lt_of_le hpos hgrid_le
    have hcov := exists_nodeCover_of_isKatzTaoAtEveryScale hδ_pos hδ_lt_one hG_pos
      𝒱.tubeUniform hKT_nodes
      (M := gridLen (Module.finrank ℝ E) η₁ (ε / 2))
      (gridLen_pos _ _ _) k hk
    obtain ⟨r, Q, W, hρr, hr1, hratio, hQcov, hQdens⟩ := hcov
    refine ⟨r, Q, W, hρr, hr1, ?_, fun i hi => hQcov i (hsh_sub hi), hQdens⟩
    refine hratio.trans (Real.rpow_le_rpow_of_exponent_ge hδ_pos_real hδ_lt_one_real.le ?_)
    have hstep : 1 / ((ssfGridLen δ : ℕ) : ℝ) ≤ η_B / (3 * (Module.finrank ℝ E : ℝ)) :=
      (one_div_le_one_div_of_le hpos hgrid_le).trans_eq (one_div_div _ _)
    exact neg_le_neg hstep
  have h_pertube_heavy : ∀ i ∈ s_heavy, ENNReal.ofReal ((δ : ℝ) ^ η_B / 2)
      * MeasureTheory.volume (V i).carrier ≤ MeasureTheory.volume (V i).shade :=
    fun i hi => (Finset.mem_filter.mp hi).2
  have hKT_leaf_heavy : ConvexSpaceBody.IsKatzTao s_heavy (fun i => (V i).toConvexSpaceBody)
      (ENNReal.ofReal ((δ : ℝ) ^ (-η_B))) :=
    ConvexSpaceBody.IsKatzTao.subset hKT_leaf hsh_sub
  have habsorb := hδ₀_abs_spec hδ_pos hδ_le_abs hδ_lt_one s_heavy (fun i => (V i).toTube)
    hT_heavy hKT_leaf_heavy
  have h_kpoly_heavy := hk_spec hδ_pos hδ_le_k hδ_lt_one_real
  have h_dmax := hδ₀_dmax_spec hδ_pos hδ_le_dmax hδ_lt_one_real
  have h_dmax2 := hδ₀_dmax2_spec hδ_pos hδ_le_dmax2 hδ_lt_one_real
  have h_asm : ∑ i ∈ s_heavy, MeasureTheory.volume (V i).shade
      ≤ ENNReal.ofReal ((δ : ℝ) ^ (-(ε / 2))) *
        MeasureTheory.volume (⋃ i ∈ s_heavy, (V i).shade) := by
    refine assembly_helper
      (E := E) (ε / 2) (half_pos hε) (ε / 2 / 2) (half_pos (half_pos hε)) η₁ hη₁_pos
      η_B hη_B_le_η₁ η_B hη_B_pos
      hδ_pos hδ_lt_one ?_ hδ_le_quarter hη_B_lt_sq hδ_le_inner hδ_thresh
      hδ_ratio_thresh hMout_large h_dmax h_dmax2 hδ_le_Cvol s_heavy V
      hT_heavy h_pertube_heavy h_kpoly_heavy hKT_leaf_heavy hKT_heavy habsorb
    exact fun s_idx V'' hne hcarrier hcard hheavy hfro hmd =>
      hbr hδ_pos hδ_le_br
        (fun s_idx' V₂ h_carrier hED C' hC' 𝒱' h_fullness h_frostman =>
          hA_apply hδ_pos hδ_le_δ₀_A s_idx' V₂ h_carrier hED hC' 𝒱' h_fullness h_frostman)
        s_idx V'' hne hcarrier hcard hheavy hfro hmd
  have h_fin : ∑ i ∈ s, MeasureTheory.volume ((V i).toShadedBody).shade ≠ ⊤ := by
    refine ne_of_lt (ENNReal.sum_lt_top.mpr (fun i _ => ?_))
    exact lt_of_le_of_lt (measure_mono (V i).shade_subset) (V i).toTube.isCompact.measure_lt_top
  have h_car_fin : ∑ i ∈ s, MeasureTheory.volume ((V i).toShadedBody).carrier ≠ ⊤ := by
    refine ne_of_lt (ENNReal.sum_lt_top.mpr (fun i _ => ?_))
    exact (V i).toTube.isCompact.measure_lt_top
  have h_poor : ENNReal.ofReal ((δ : ℝ) ^ η_B / 2)
        * (∑ i ∈ s, MeasureTheory.volume ((V i).toShadedBody).carrier)
      ≤ (1 / 2 : ENNReal) * ∑ i ∈ s, MeasureTheory.volume ((V i).toShadedBody).shade := by
    have hmul : ENNReal.ofReal ((δ : ℝ) ^ η_B)
          * (∑ i ∈ s, MeasureTheory.volume ((V i).toShadedBody).carrier)
        ≤ ∑ i ∈ s, MeasureTheory.volume ((V i).toShadedBody).shade := by
      rcases eq_or_ne (∑ i ∈ s, MeasureTheory.volume ((V i).toShadedBody).carrier) 0 with h0 | hne
      · rw [h0, mul_zero]; exact bot_le
      · exact (ENNReal.le_div_iff_mul_le (Or.inl hne) (Or.inl h_car_fin)).mp hLam
    have he : ENNReal.ofReal ((δ : ℝ) ^ η_B / 2)
        = (1 / 2 : ENNReal) * ENNReal.ofReal ((δ : ℝ) ^ η_B) := by
      rw [show (δ : ℝ) ^ η_B / 2 = (1 / 2) * (δ : ℝ) ^ η_B by ring,
        ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      congr 1
      rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2), ENNReal.ofReal_one,
        ENNReal.ofReal_ofNat]
    rw [he, mul_assoc]
    exact mul_le_mul_right hmul _
  have h_half := heavy_half_mass s
    (fun i => (V i).toShadedBody) (ENNReal.ofReal ((δ : ℝ) ^ η_B / 2)) h_fin h_poor
  have h_union : MeasureTheory.volume (⋃ i ∈ s_heavy, (V i).shade)
      ≤ MeasureTheory.volume (⋃ i ∈ s, (V i).shade) :=
    measure_mono (Set.biUnion_subset_biUnion_left hsh_sub)
  have hδpow : (δ : ℝ) ^ (ε / 2) ≤ 1 / 2 := by
    calc (δ : ℝ) ^ (ε / 2) ≤ δ₀_two ^ (ε / 2) :=
          Real.rpow_le_rpow hδ_pos_real.le hδ_le_two (div_nonneg hε.le zero_le_two)
      _ = 1 / 2 := by
          rw [hδ₀_two_def, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 1 / 2),
            show (2 / ε) * (ε / 2) = 1 by
              rw [div_mul_div_comm, mul_comm (2 : ℝ) ε,
                div_self (mul_ne_zero hε.ne' two_ne_zero)]]
          exact Real.rpow_one _
  have hreal2 : 2 * (δ : ℝ) ^ (-(ε / 2)) ≤ (δ : ℝ) ^ (-ε) := by
    have hsplit : (δ : ℝ) ^ (-ε) = (δ : ℝ) ^ (-(ε / 2)) * (δ : ℝ) ^ (-(ε / 2)) := by
      rw [← Real.rpow_add hδ_pos_real]; congr 1; ring
    have h2le : (2 : ℝ) ≤ (δ : ℝ) ^ (-(ε / 2)) := by
      rw [Real.rpow_neg hδ_pos_real.le,
        le_inv_comm₀ two_pos (Real.rpow_pos_of_pos hδ_pos_real _)]
      exact hδpow.trans (by norm_num)
    exact hsplit ▸ mul_le_mul_of_nonneg_right h2le
      (Real.rpow_pos_of_pos hδ_pos_real _).le
  have h_two : (2 : ENNReal) * ENNReal.ofReal ((δ : ℝ) ^ (-(ε / 2)))
      ≤ ENNReal.ofReal ((δ : ℝ) ^ (-ε)) := by
    rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num)]
    exact ENNReal.ofReal_le_ofReal hreal2
  calc ∑ i ∈ s, MeasureTheory.volume (V i).shade
      ≤ 2 * ∑ i ∈ s_heavy, MeasureTheory.volume (V i).shade := h_half
    _ ≤ 2 * (ENNReal.ofReal ((δ : ℝ) ^ (-(ε / 2))) *
          MeasureTheory.volume (⋃ i ∈ s_heavy, (V i).shade)) := by gcongr
    _ ≤ 2 * (ENNReal.ofReal ((δ : ℝ) ^ (-(ε / 2))) *
          MeasureTheory.volume (⋃ i ∈ s, (V i).shade)) := by gcongr
    _ = (2 * ENNReal.ofReal ((δ : ℝ) ^ (-(ε / 2)))) *
          MeasureTheory.volume (⋃ i ∈ s, (V i).shade) := by ring
    _ ≤ ENNReal.ofReal ((δ : ℝ) ^ (-ε)) * MeasureTheory.volume (⋃ i ∈ s, (V i).shade) := by
        exact mul_le_mul_left h_two _

end StickyKakeya
