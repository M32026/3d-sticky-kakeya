/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Mathlib.Analysis.EuclideanNet
public import Kakeya.Tube.Nets
public import Kakeya.Tube.Rigidity

/-!
# The per-scale grid net and its bounded overlap

The `ρ/32`-separated net of tubes at one scale, the bound on how many of its members a single tube
can meet, and the two-scale chain form `L2_chain_bo_tight` that the tree construction iterates.
-/

@[expose] public section


open MeasureTheory Real

open scoped ENNReal NNReal

namespace Tube

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E] [MeasurableSpace E] [BorelSpace E] [ProperSpace E]

open Classical in
/-- **Tight per-scale net** (finer `ε`, exposes covering closeness). Same as `grid_net` but the
direction net is `ρ/32`-spaced and the midpoint net `ρ/64`-spaced, so the covering tube `W` is
within `ρ/32` (midpoint) and `ρ/16` (direction) of the covered `σ`-tube `U`. This closeness, when
telescoped through the chain, makes a representative leaf's `ρ_k`-rescale cover its whole node — the
key to the `[δ,1]` "parent = `s'`-leaf rescale" strengthening. Separation is `ρ/32`. -/
theorem grid_net_tight {ρ : NNReal} (hρ_pos : 0 < ρ) (hρ_le1 : (ρ : ℝ) ≤ 1) :
    ∃ (G : Finset (Tube ρ E)),
      (∀ {σ : NNReal} (U : Tube σ E), 2 * (σ : ℝ) ≤ (ρ : ℝ) →
        U.midpoint ∈ Metric.closedBall (0 : E) 3 →
        ∃ W ∈ G, U.toConvexSpaceBody ≤ W.toConvexSpaceBody ∧
          ‖U.midpoint - W.midpoint‖ ≤ (ρ : ℝ) / 32 ∧
          ‖U.direction - W.direction‖ ≤ (ρ : ℝ) / 16) ∧
      (∀ a ∈ G, ∀ b ∈ G, a ≠ b → (ρ : ℝ) / 32 ≤ ‖a.x - b.x‖ + ‖a.y - b.y‖) ∧
      (∀ W ∈ G, W.carrier ⊆ Metric.closedBall (0 : E) 5) ∧
      (∀ W ∈ G, W.midpoint ∈ Metric.closedBall (0 : E) 3) := by
  classical
  have hρ_pos_r : (0 : ℝ) < (ρ : ℝ) := by exact_mod_cast hρ_pos
  have hεd_pos : (0 : ℝ) < (ρ : ℝ) / 32 := by linarith
  have hεd_le1 : (ρ : ℝ) / 32 ≤ 1 := by linarith
  have hεp_pos : (0 : ℝ) < (ρ : ℝ) / 64 := by linarith
  obtain ⟨D, hD_unit, hD_sep, hD_cover⟩ := sphere_sep_net (E := E) hεd_pos hεd_le1
  obtain ⟨Pm, hPm_loc, hPm_sep, hPm_cover⟩ := midpoint_sep_net (E := E) hεp_pos
  obtain ⟨x₀, hx₀⟩ := exists_ne (0 : E)
  set u₀ : E := ‖x₀‖⁻¹ • x₀ with hu₀_def
  have hu₀ : ‖u₀‖ = 1 := by
    rw [hu₀_def, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx₀)]
  set tubeAt : E → E → Tube ρ E := fun m d =>
    if h : ‖d‖ = 1 then Tube.ofMidpointDirection ρ m d h
    else Tube.ofMidpointDirection ρ m u₀ hu₀
    with htubeAt_def
  have htubeAt_x : ∀ m d, ‖d‖ = 1 → (tubeAt m d).x = m - (1/2 : ℝ) • d := by
    intro m d hd; rw [htubeAt_def]; simp only [dif_pos hd]
    simp [Tube.ofMidpointDirection]
  have htubeAt_y : ∀ m d, ‖d‖ = 1 → (tubeAt m d).y = m + (1/2 : ℝ) • d := by
    intro m d hd; rw [htubeAt_def]; simp only [dif_pos hd]
    simp [Tube.ofMidpointDirection]
  have htubeAt_mid : ∀ m d, ‖d‖ = 1 → (tubeAt m d).midpoint = m := by
    intro m d hd; rw [htubeAt_def]; simp only [dif_pos hd]
    simp only [Tube.midpoint, Tube.ofMidpointDirection_x, Tube.ofMidpointDirection_y]
    module
  have htubeAt_dir : ∀ m d, ‖d‖ = 1 → (tubeAt m d).direction = d := by
    intro m d hd; rw [htubeAt_def]; simp only [dif_pos hd]
    simp only [Tube.direction, Tube.ofMidpointDirection_x, Tube.ofMidpointDirection_y]
    module
  set G : Finset (Tube ρ E) := (Pm ×ˢ D).image (fun p => tubeAt p.1 p.2) with hG_def
  refine ⟨G, ?_, ?_, ?_, ?_⟩
  · intro σ U hσ hU_mid
    have hU_dir : ‖U.direction‖ = 1 := U.norm_direction
    obtain ⟨d, hd_mem, hd_close⟩ := hD_cover U.direction hU_dir
    have hd_unit : ‖d‖ = 1 := hD_unit d hd_mem
    obtain ⟨m, hm_mem, hm_close⟩ := hPm_cover U.midpoint hU_mid
    have hdir_le : ‖U.direction - (tubeAt m d).direction‖ ≤ 2 * ((ρ : ℝ) / 32) := by
      rw [htubeAt_dir m d hd_unit]; exact hd_close
    have hmid_le : ‖U.midpoint - (tubeAt m d).midpoint‖ ≤ 2 * ((ρ : ℝ) / 64) := by
      rw [htubeAt_mid m d hd_unit]; exact hm_close
    refine ⟨tubeAt m d, ?_, ?_, ?_, ?_⟩
    · rw [hG_def, Finset.mem_image]
      exact ⟨(m, d), Finset.mem_product.mpr ⟨hm_mem, hd_mem⟩, rfl⟩
    · refine Tube.tube_carrier_subset_of_close U (tubeAt m d) hdir_le hmid_le ?_
      have : (σ : ℝ) ≤ (ρ : ℝ) / 2 := by linarith
      linarith
    · calc ‖U.midpoint - (tubeAt m d).midpoint‖ ≤ 2 * ((ρ : ℝ) / 64) := hmid_le
        _ = (ρ : ℝ) / 32 := by ring
    · calc ‖U.direction - (tubeAt m d).direction‖ ≤ 2 * ((ρ : ℝ) / 32) := hdir_le
        _ = (ρ : ℝ) / 16 := by ring
  · intro a ha b hb hab
    rw [hG_def, Finset.mem_image] at ha hb
    obtain ⟨⟨ma, da⟩, hmda, haeq⟩ := ha
    obtain ⟨⟨mb, db⟩, hmdb, hbeq⟩ := hb
    rw [Finset.mem_product] at hmda hmdb
    obtain ⟨hma, hda⟩ := hmda
    obtain ⟨hmb, hdb⟩ := hmdb
    have hda_unit : ‖da‖ = 1 := hD_unit da hda
    have hdb_unit : ‖db‖ = 1 := hD_unit db hdb
    subst haeq; subst hbeq
    rw [htubeAt_x ma da hda_unit, htubeAt_x mb db hdb_unit,
      htubeAt_y ma da hda_unit, htubeAt_y mb db hdb_unit]
    have hne : ma ≠ mb ∨ da ≠ db := by
      by_contra h
      push Not at h
      exact hab (by rw [h.1, h.2])
    set A : E := ma - mb with hA
    set B : E := da - db with hB
    have hxx : (ma - (1/2 : ℝ) • da) - (mb - (1/2 : ℝ) • db) = A - (1/2 : ℝ) • B := by
      rw [hA, hB]; module
    have hyy : (ma + (1/2 : ℝ) • da) - (mb + (1/2 : ℝ) • db) = A + (1/2 : ℝ) • B := by
      rw [hA, hB]; module
    rw [hxx, hyy]
    have htri1 : 2 * ‖A‖ ≤ ‖A - (1/2 : ℝ) • B‖ + ‖A + (1/2 : ℝ) • B‖ := by
      have h := norm_add_le (A - (1/2 : ℝ) • B) (A + (1/2 : ℝ) • B)
      have he : (A - (1/2 : ℝ) • B) + (A + (1/2 : ℝ) • B) = (2 : ℝ) • A := by module
      rw [he, norm_smul, Real.norm_eq_abs] at h
      simp only [abs_two] at h
      linarith
    have htri2 : 2 * ‖(1/2 : ℝ) • B‖ ≤ ‖A - (1/2 : ℝ) • B‖ + ‖A + (1/2 : ℝ) • B‖ := by
      have h := norm_sub_le (A + (1/2 : ℝ) • B) (A - (1/2 : ℝ) • B)
      have he : (A + (1/2 : ℝ) • B) - (A - (1/2 : ℝ) • B) = (2 : ℝ) • ((1/2 : ℝ) • B) := by module
      rw [he, norm_smul, Real.norm_eq_abs] at h
      simp only [abs_two] at h
      linarith
    rcases hne with hmne | hdne
    · have hApos : (ρ : ℝ) / 64 ≤ ‖A‖ := by rw [hA]; exact hPm_sep ma hma mb hmb hmne
      linarith
    · have hBpos : (ρ : ℝ) / 32 ≤ ‖B‖ := by rw [hB]; exact hD_sep da hda db hdb hdne
      have hBhalf : ‖(1/2 : ℝ) • B‖ = (1/2) * ‖B‖ := by
        rw [norm_smul, Real.norm_eq_abs]; norm_num
      rw [hBhalf] at htri2
      linarith
  · intro W hW
    rw [hG_def, Finset.mem_image] at hW
    obtain ⟨⟨m, d⟩, hmd, hWeq⟩ := hW
    rw [Finset.mem_product] at hmd
    obtain ⟨hm, hd⟩ := hmd
    have hd_unit : ‖d‖ = 1 := hD_unit d hd
    have hm_norm : ‖m‖ ≤ 3 := by
      have := hPm_loc m hm; rwa [Metric.mem_closedBall, dist_zero_right] at this
    have hhalf : ‖(1/2 : ℝ) • d‖ = 1/2 := by
      rw [norm_smul, Real.norm_eq_abs, hd_unit]; norm_num
    subst hWeq
    have hWx : ‖(tubeAt m d).x‖ ≤ 7/2 := by
      rw [htubeAt_x m d hd_unit]
      calc ‖m - (1/2 : ℝ) • d‖ ≤ ‖m‖ + ‖(1/2 : ℝ) • d‖ := norm_sub_le _ _
        _ ≤ 3 + 1/2 := by rw [hhalf]; linarith
        _ = 7/2 := by norm_num
    have hWy : ‖(tubeAt m d).y‖ ≤ 7/2 := by
      rw [htubeAt_y m d hd_unit]
      calc ‖m + (1/2 : ℝ) • d‖ ≤ ‖m‖ + ‖(1/2 : ℝ) • d‖ := norm_add_le _ _
        _ ≤ 3 + 1/2 := by rw [hhalf]; linarith
        _ = 7/2 := by norm_num
    intro p hp
    rw [(tubeAt m d).carrier_eq] at hp
    obtain ⟨z, hz_seg, hp_ball⟩ := Set.mem_iUnion₂.mp hp
    obtain ⟨a, b, hga, hgb, hgab, hzeq⟩ := hz_seg
    have hz_norm : ‖z‖ ≤ 7/2 := by
      rw [← hzeq]
      calc ‖a • (tubeAt m d).x + b • (tubeAt m d).y‖
          ≤ ‖a • (tubeAt m d).x‖ + ‖b • (tubeAt m d).y‖ := norm_add_le _ _
        _ = a * ‖(tubeAt m d).x‖ + b * ‖(tubeAt m d).y‖ := by
            rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
              abs_of_nonneg hga, abs_of_nonneg hgb]
        _ ≤ a * (7/2) + b * (7/2) := by gcongr
        _ = 7/2 := by rw [← add_mul, hgab, one_mul]
    rw [Metric.mem_closedBall, dist_zero_right]
    have hpz : dist p z ≤ (ρ : ℝ) := by rwa [Metric.mem_closedBall] at hp_ball
    calc ‖p‖ ≤ ‖z‖ + ‖p - z‖ := norm_le_norm_add_norm_sub' p z
      _ = ‖z‖ + dist p z := by rw [dist_eq_norm]
      _ ≤ 7/2 + 1 := add_le_add hz_norm (hpz.trans hρ_le1)
      _ ≤ 5 := by norm_num
  · intro W hW
    rw [hG_def, Finset.mem_image] at hW
    obtain ⟨⟨m, d⟩, hmd, hWeq⟩ := hW
    rw [Finset.mem_product] at hmd
    obtain ⟨hm, hd⟩ := hmd
    have hd_unit : ‖d‖ = 1 := hD_unit d hd
    subst hWeq
    rw [htubeAt_mid m d hd_unit]
    exact hPm_loc m hm

open Classical in
/-- **Bounded overlap for the tight net** (`ρ/32`-separated). Same as `grid_overlap` but for the
finer separation produced by `grid_net_tight`; the looser gap gives the larger constant
`2·(3073n+1)^(2n)` (ratio `24·128 + 1 = 3073`). -/
theorem grid_overlap_tight {δ ρ : NNReal} (hρ_pos : 0 < ρ)
    (G : Finset (Tube ρ E))
    (hsep : ∀ a ∈ G, ∀ b ∈ G, a ≠ b → (ρ : ℝ) / 32 ≤ ‖a.x - b.x‖ + ‖a.y - b.y‖)
    (V : Tube ρ E) :
    (G.filter (fun W => ∃ (U : Tube δ E),
        U.carrier ⊆ Metric.closedBall (0 : E) 1 ∧
        U.toConvexSpaceBody ≤ W.toConvexSpaceBody ∧
        U.toConvexSpaceBody ≤ V.toConvexSpaceBody)).card ≤
      2 * (3073 * (Module.finrank ℝ E) + 1) ^ (2 * Module.finrank ℝ E) := by
  classical
  set n : ℕ := Module.finrank ℝ E with hn_def
  have hn_pos : 0 < n := Module.finrank_pos
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_pos
  set ρk : ℝ := (ρ : ℝ) with hρk_def
  have hρk_pos : (0 : ℝ) < ρk := by rw [hρk_def]; exact_mod_cast hρ_pos
  set F := G.filter (fun W => ∃ (U : Tube δ E),
      U.carrier ⊆ Metric.closedBall (0 : E) 1 ∧
      U.toConvexSpaceBody ≤ W.toConvexSpaceBody ∧
      U.toConvexSpaceBody ≤ V.toConvexSpaceBody) with hF
  have hFG : ∀ W ∈ F, W ∈ G := fun W hW => (Finset.mem_filter.mp hW).1
  have hsep_endpoints : ∀ W ∈ F, ∀ W' ∈ F, W ≠ W' →
      ρk / 32 ≤ ‖W.x - W'.x‖ + ‖W.y - W'.y‖ :=
    fun W hW W' hW' hne => hsep W (hFG W hW) W' (hFG W' hW') hne
  have hloc24 : ∀ W ∈ F,
      (‖W.x - V.x‖ ≤ 24 * ρk ∧ ‖W.y - V.y‖ ≤ 24 * ρk) ∨
      (‖W.x - V.y‖ ≤ 24 * ρk ∧ ‖W.y - V.x‖ ≤ 24 * ρk) := by
    intro W hW
    obtain ⟨_, U, _hU1, hUW, hUV⟩ := Finset.mem_filter.mp hW
    have hW_rescale : W.toConvexSpaceBody ≤ (U.rescale (4 * ρ)).toConvexSpaceBody :=
      Tube.rescale_le_of_le U W hUW
    have hV_rescale : V.toConvexSpaceBody ≤ (U.rescale (4 * ρ)).toConvexSpaceBody :=
      Tube.rescale_le_of_le U V hUV
    have hscale : ((4 * ρ : NNReal) : ℝ) = 4 * ρk := by rw [hρk_def]; push_cast; ring
    have hWend := Tube.endpoints_close_of_body_le W (U.rescale (4 * ρ)) hW_rescale
    have hVend := Tube.endpoints_close_of_body_le V (U.rescale (4 * ρ)) hV_rescale
    simp only [Tube.rescale, Tube.mk'_x, Tube.mk'_y, hscale] at hWend hVend
    have h12 : (3 : ℝ) * (4 * ρk) = 12 * ρk := by ring
    rw [h12] at hWend hVend
    rcases hWend with ⟨hWx, hWy⟩ | ⟨hWx, hWy⟩ <;>
      rcases hVend with ⟨hVx, hVy⟩ | ⟨hVx, hVy⟩
    · left; refine ⟨?_, ?_⟩
      · have ht := norm_sub_le_norm_sub_add_norm_sub W.x U.x V.x
        have : ‖U.x - V.x‖ ≤ 12 * ρk := by rw [norm_sub_rev]; exact hVx
        linarith [ht, hWx, this]
      · have ht := norm_sub_le_norm_sub_add_norm_sub W.y U.y V.y
        have : ‖U.y - V.y‖ ≤ 12 * ρk := by rw [norm_sub_rev]; exact hVy
        linarith [ht, hWy, this]
    · right; refine ⟨?_, ?_⟩
      · have ht := norm_sub_le_norm_sub_add_norm_sub W.x U.x V.y
        have : ‖U.x - V.y‖ ≤ 12 * ρk := by rw [norm_sub_rev]; exact hVy
        linarith [ht, hWx, this]
      · have ht := norm_sub_le_norm_sub_add_norm_sub W.y U.y V.x
        have : ‖U.y - V.x‖ ≤ 12 * ρk := by rw [norm_sub_rev]; exact hVx
        linarith [ht, hWy, this]
    · right; refine ⟨?_, ?_⟩
      · have ht := norm_sub_le_norm_sub_add_norm_sub W.x U.y V.y
        have : ‖U.y - V.y‖ ≤ 12 * ρk := by rw [norm_sub_rev]; exact hVy
        linarith [ht, hWx, this]
      · have ht := norm_sub_le_norm_sub_add_norm_sub W.y U.x V.x
        have : ‖U.x - V.x‖ ≤ 12 * ρk := by rw [norm_sub_rev]; exact hVx
        linarith [ht, hWy, this]
    · left; refine ⟨?_, ?_⟩
      · have ht := norm_sub_le_norm_sub_add_norm_sub W.x U.y V.x
        have : ‖U.y - V.x‖ ≤ 12 * ρk := by rw [norm_sub_rev]; exact hVx
        linarith [ht, hWx, this]
      · have ht := norm_sub_le_norm_sub_add_norm_sub W.y U.x V.y
        have : ‖U.x - V.y‖ ≤ 12 * ρk := by rw [norm_sub_rev]; exact hVy
        linarith [ht, hWy, this]
  set Fp : Finset (Tube ρ E) :=
    F.filter (fun W => ‖W.x - V.x‖ ≤ 24 * ρk ∧ ‖W.y - V.y‖ ≤ 24 * ρk) with hFp
  set Fm : Finset (Tube ρ E) := F \ Fp with hFm
  have hr_pos : (0 : ℝ) < ρk / 32 := by linarith
  have hratio : (24 * ρk + (ρk / 32) / 4) / ((ρk / 32) / 4) ≤ (3073 * (n : ℝ) + 1) := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [hρk_pos, hn1]
  have hpart_bound : ∀ (Gp : Finset (Tube ρ E)) (cx cy : E),
      (∀ W ∈ Gp, W ∈ F) →
      (∀ W ∈ Gp, ‖W.x - cx‖ ≤ 24 * ρk) → (∀ W ∈ Gp, ‖W.y - cy‖ ≤ 24 * ρk) →
      Gp.card ≤ (3073 * n + 1) ^ (2 * n) := by
    intro Gp cx cy hGF hGx hGy
    have hsepG : ∀ a ∈ Gp, ∀ b ∈ Gp, a ≠ b → ρk / 32 ≤ ‖a.x - b.x‖ + ‖a.y - b.y‖ :=
      fun a ha b hb hab => hsep_endpoints a (hGF a ha) b (hGF b hb) hab
    have hpack := Tube.card_le_of_L1_separated_in_box (E := E) Gp (fun W => W.x) (fun W => W.y)
      cx cy hr_pos hsepG hGx hGy
    have hbase_nn : (0 : ℝ) ≤ (24 * ρk + (ρk / 32) / 4) / ((ρk / 32) / 4) := by positivity
    have hmono : ((24 * ρk + (ρk / 32) / 4) / ((ρk / 32) / 4)) ^ (2 * n)
        ≤ ((3073 * (n : ℝ) + 1)) ^ (2 * n) := pow_le_pow_left₀ hbase_nn hratio _
    have hcardR : (Gp.card : ℝ) ≤ ((3073 * (n : ℝ) + 1)) ^ (2 * n) := le_trans hpack hmono
    have hcast : ((3073 * (n : ℝ) + 1)) ^ (2 * n) = (((3073 * n + 1) ^ (2 * n) : ℕ) : ℝ) := by
      push_cast; ring
    rw [hcast] at hcardR
    exact_mod_cast hcardR
  have hFpF : ∀ W ∈ Fp, W ∈ F := fun W hW => (Finset.mem_filter.mp hW).1
  have hFp_x : ∀ W ∈ Fp, ‖W.x - V.x‖ ≤ 24 * ρk := fun W hW => (Finset.mem_filter.mp hW).2.1
  have hFp_y : ∀ W ∈ Fp, ‖W.y - V.y‖ ≤ 24 * ρk := fun W hW => (Finset.mem_filter.mp hW).2.2
  have hFp_card : Fp.card ≤ (3073 * n + 1) ^ (2 * n) := hpart_bound Fp V.x V.y hFpF hFp_x hFp_y
  have hFmF : ∀ W ∈ Fm, W ∈ F := fun W hW => (Finset.mem_sdiff.mp hW).1
  have hFm_x : ∀ W ∈ Fm, ‖W.x - V.y‖ ≤ 24 * ρk := by
    intro W hW
    obtain ⟨hWF, hWnp⟩ := Finset.mem_sdiff.mp hW
    rcases hloc24 W hWF with hpos | hneg
    · exact absurd (Finset.mem_filter.mpr ⟨hWF, hpos⟩) hWnp
    · exact hneg.1
  have hFm_y : ∀ W ∈ Fm, ‖W.y - V.x‖ ≤ 24 * ρk := by
    intro W hW
    obtain ⟨hWF, hWnp⟩ := Finset.mem_sdiff.mp hW
    rcases hloc24 W hWF with hpos | hneg
    · exact absurd (Finset.mem_filter.mpr ⟨hWF, hpos⟩) hWnp
    · exact hneg.2
  have hFm_card : Fm.card ≤ (3073 * n + 1) ^ (2 * n) := hpart_bound Fm V.y V.x hFmF hFm_x hFm_y
  have hFsplit : F.card ≤ Fp.card + Fm.card := by
    have hFeq : F.card = (Fp ∪ Fm).card := by
      congr 1
      rw [hFm, Finset.union_sdiff_of_subset (Finset.filter_subset _ _)]
    rw [hFeq]; exact Finset.card_union_le _ _
  calc F.card ≤ Fp.card + Fm.card := hFsplit
    _ ≤ (3073 * n + 1) ^ (2 * n) + (3073 * n + 1) ^ (2 * n) := Nat.add_le_add hFp_card hFm_card
    _ = 2 * (3073 * n + 1) ^ (2 * n) := by ring

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Root tube at scale `σ` (axis through the origin): its carrier contains the ball `B_σ` and is
contained in `B_{σ+1/2}` (the unit axis lies in `B_{1/2}`). With `σ = ρ 0 = 1` this gives the chain
root covering `B_1 ⊆ W_∗` and localization `W_∗ ⊆ B_{3/2}`. -/
theorem exists_root_ball {σ : NNReal} :
    ∃ W : Tube σ E, Metric.closedBall (0 : E) (σ : ℝ) ⊆ W.carrier ∧
      W.carrier ⊆ Metric.closedBall (0 : E) ((σ : ℝ) + 1/2) := by
  obtain ⟨v, hv⟩ := exists_ne (0 : E)
  set u : E := ‖v‖⁻¹ • v with hu_def
  have hu : ‖u‖ = 1 := by
    rw [hu_def, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)]
  have hdist : dist (-(1/2 : ℝ) • u) ((1/2 : ℝ) • u) = 1 := by
    rw [dist_eq_norm]
    have he : -(1/2 : ℝ) • u - (1/2 : ℝ) • u = (-1 : ℝ) • u := by module
    rw [he, norm_smul, Real.norm_eq_abs, hu]; norm_num
  refine ⟨Tube.mk' σ hdist, fun p hp => ?_, fun p hp => ?_⟩
  · rw [(Tube.mk' σ hdist).carrier_eq]
    refine Set.mem_biUnion (show (0 : E) ∈ _ from ?_) hp
    rw [Tube.mk'_x, Tube.mk'_y]
    exact ⟨1/2, 1/2, by norm_num, by norm_num, by norm_num, by module⟩
  · rw [(Tube.mk' σ hdist).carrier_eq] at hp
    obtain ⟨z, hz_seg, hz_ball⟩ := Set.mem_iUnion₂.mp hp
    rw [Tube.mk'_x, Tube.mk'_y] at hz_seg
    obtain ⟨a, b, ha, hb, hab, hzeq⟩ := hz_seg
    rw [Metric.mem_closedBall, dist_zero_right]
    have hz_norm : ‖z‖ ≤ 1/2 := by
      rw [← hzeq]
      have hzc : a • (-(1/2 : ℝ) • u) + b • ((1/2 : ℝ) • u) = ((b - a) / 2) • u := by module
      rw [hzc, norm_smul, hu, mul_one, Real.norm_eq_abs, abs_div, abs_two]
      have hba : |b - a| ≤ 1 := by rw [abs_le]; constructor <;> nlinarith
      linarith
    have hpz : dist p z ≤ (σ : ℝ) := by rwa [Metric.mem_closedBall] at hz_ball
    calc ‖p‖ ≤ ‖z‖ + ‖p - z‖ := norm_le_norm_add_norm_sub' p z
      _ = ‖z‖ + dist p z := by rw [dist_eq_norm]
      _ ≤ 1/2 + (σ : ℝ) := add_le_add hz_norm hpz
      _ = (σ : ℝ) + 1/2 := by ring

/-- Boundary scale `ρ_M = δ^(M/M) = δ`. -/
theorem rho_M (δ : NNReal) {M : ℕ} (hM : 0 < M) : (δ ^ ((M : ℝ) / (M : ℝ)) : NNReal) = δ := by
  rw [div_self (Nat.cast_ne_zero.mpr hM.ne'), NNReal.rpow_one]

omit [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- A `σ`-tube built on a `δ`-tube `V`'s axis has `V`'s carrier when `σ = δ`. With `σ = ρ_M = δ`
this is the leaf identification `(leaf tube).carrier = (T i).carrier`. -/
theorem leaf_carrier_eq {δ σ : NNReal} (hσ : σ = δ) (V : Tube δ E) :
    (Tube.mk' σ V.dist_eq_one).carrier = V.carrier := by
  subst hσ
  rw [(Tube.mk' σ V.dist_eq_one).carrier_eq, V.carrier_eq, Tube.mk'_x, Tube.mk'_y]

/-- `2δ ≤ ρ_k` for every `k < M`: the leaf scale `δ` is at least a factor `2` below every coarser
scale, so a `δ`-tube can be covered by the level-`k` grid (`grid_net` needs `2δ ≤ ρ_k`). Writing
`b = δ^(1/M) ≤ 1/2`, one has `δ = b^M`, `ρ_k = b^k`, and `2 b^{M-k} ≤ 2b ≤ 1` since `M-k ≥ 1`. -/
theorem two_delta_le_rho {δ : NNReal} (hδ : 0 < δ) {M : ℕ} (hM : 0 < M)
    (hgap : (δ : ℝ) ^ ((1 : ℝ) / (M : ℝ)) ≤ 1 / 2) {k : ℕ} (hk : k < M) :
    2 * (δ : ℝ) ≤ (δ : ℝ) ^ ((k : ℝ) / (M : ℝ)) := by
  have hδr : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ
  have hMr : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hM.ne'
  set b : ℝ := (δ : ℝ) ^ ((1 : ℝ) / (M : ℝ)) with hb
  have hb_pos : 0 < b := Real.rpow_pos_of_pos hδr _
  have hbk : (δ : ℝ) ^ ((k : ℝ) / (M : ℝ)) = b ^ k := by
    rw [hb, ← Real.rpow_natCast ((δ : ℝ) ^ ((1 : ℝ) / (M : ℝ))) k, ← Real.rpow_mul hδr.le]
    congr 1
    field_simp
  have hbM : (δ : ℝ) = b ^ M := by
    rw [hb, ← Real.rpow_natCast ((δ : ℝ) ^ ((1 : ℝ) / (M : ℝ))) M, ← Real.rpow_mul hδr.le,
      show (1 : ℝ) / (M : ℝ) * (M : ℝ) = 1 by field_simp, Real.rpow_one]
  rw [hbk, hbM]
  have hbk_pos : 0 < b ^ k := pow_pos hb_pos k
  have hbmk : b ^ (M - k) ≤ b := by
    calc b ^ (M - k) ≤ b ^ 1 := pow_le_pow_of_le_one hb_pos.le (by linarith) (by omega)
      _ = b := pow_one b
  have hbmk_half : b ^ (M - k) ≤ 1 / 2 := le_trans hbmk (by linarith)
  have hMk : M = k + (M - k) := by omega
  rw [hMk, pow_add]
  nlinarith [mul_le_mul_of_nonneg_left hbmk_half hbk_pos.le, hbk_pos]

open Classical in
/-- **L2 (tight bounded-overlap chain).** Strengthening of `L2_chain_bo` using the finer
`grid_net_tight` / `grid_overlap_tight`: the chain-projection output now also carries per-step
geometric closeness `‖w.mid - w'.mid‖ ≤ ρ_k/32 ∧ ‖w.dir - w'.dir‖ ≤ ρ_k/16` (read straight off
`grid_net_tight`'s covering, no `grid_nest` needed), and the per-level overlap constant is the tight
`2·(3073n+1)^(2n)`. Built additively alongside `L2_chain_bo`; the green chain is untouched. -/
theorem L2_chain_bo_tight {ι : Type*} {δ : NNReal} (hδ : 0 < δ) (hδ1 : δ < 1)
    (s : Finset ι) (T : ι → Tube δ E)
    (hT_inj : Set.InjOn (fun i => (T i).carrier) (s : Set ι))
    (M : ℕ) (hM_pos : 0 < M)
    (hgap : (δ : ℝ) ^ ((1 : ℝ) / (M : ℝ)) ≤ 1 / 2)
    (hs_B1 : ∀ ⦃i⦄, i ∈ s → (T i).carrier ⊆ Metric.closedBall (0 : E) 1) :
    let ρ : ℕ → NNReal := fun k => δ ^ ((k : ℝ) / (M : ℝ))
    ∃ (P : ∀ k, Finset (Tube (ρ k) E)),
      (∀ k, k < M → ∀ w ∈ P (k + 1), ∃ w' ∈ P k,
        w.toConvexSpaceBody ≤ w'.toConvexSpaceBody ∧
        ‖w.midpoint - w'.midpoint‖ ≤ ((ρ k : NNReal) : ℝ) / 32 ∧
        ‖w.direction - w'.direction‖ ≤ ((ρ k : NNReal) : ℝ) / 16) ∧
      (∀ k ≤ M, ∀ W ∈ P k, W.carrier ⊆ Metric.closedBall (0 : E) 5) ∧
      (∀ k ≤ M, ∀ ⦃i⦄, i ∈ s → ∃ W ∈ P k,
        (T i).toConvexSpaceBody ≤ W.toConvexSpaceBody) ∧
      (∀ k ≤ M, ∀ (V : Tube (ρ k) E),
        ((P k).filter (fun W => ∃ (U : Tube δ E),
            U.carrier ⊆ Metric.closedBall (0 : E) 1 ∧
            U.toConvexSpaceBody ≤ W.toConvexSpaceBody ∧
            U.toConvexSpaceBody ≤ V.toConvexSpaceBody)).card ≤
          2 * (3073 * (Module.finrank ℝ E) + 1) ^ (2 * Module.finrank ℝ E)) ∧
      (∀ ⦃i⦄, i ∈ s → ∃ W ∈ P M, W.carrier = (T i).carrier ∧
        W.midpoint = (T i).midpoint ∧ W.direction = (T i).direction) ∧
      (∀ k, k < M → ((P k).card : ℝ) ≤
        (641 : ℝ) ^ (2 * Module.finrank ℝ E)
          * ((4 : ℝ) / ((ρ k : NNReal) : ℝ)) ^ (2 * Module.finrank ℝ E)) := by
  intro ρ
  classical
  have hδr : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ
  have hδr1 : (δ : ℝ) < 1 := by exact_mod_cast hδ1
  have hρ_pos : ∀ k, 0 < ρ k := fun k => NNReal.rpow_pos hδ
  have hρ_le1 : ∀ k, (ρ k : ℝ) ≤ 1 := by
    intro k
    change ((δ ^ ((k : ℝ) / (M : ℝ)) : NNReal) : ℝ) ≤ 1
    rw [NNReal.coe_rpow]
    exact Real.rpow_le_one hδr.le hδr1.le (by positivity)
  have coe_rho : ∀ j : ℕ, ((ρ j : NNReal) : ℝ) = (δ : ℝ) ^ ((j : ℝ) / (M : ℝ)) := by
    intro j
    change (((δ ^ ((j : ℝ) / (M : ℝ)) : NNReal)) : ℝ) = _
    rw [NNReal.coe_rpow]
  set rootT : ∀ k, Tube (ρ k) E := fun k => (exists_root_ball (σ := ρ k)).choose with hrootT
  set leafT : ∀ k, ι → Tube (ρ k) E := fun k i => Tube.mk' (ρ k) (T i).dist_eq_one with hleafT
  set gridG : ∀ k, Finset (Tube (ρ k) E) :=
    fun k => (grid_net_tight (hρ_pos k) (hρ_le1 k)).choose with hgridG
  set P : ∀ k, Finset (Tube (ρ k) E) :=
    fun k => if k = M then s.image (leafT k) else gridG k with hP
  have hPM : P M = s.image (leafT M) := by
    change (if M = M then s.image (leafT M) else gridG M) = s.image (leafT M)
    rw [if_pos rfl]
  have hPk_grid : ∀ k, k ≠ M → P k = gridG k := by
    intro k hkM
    change (if k = M then s.image (leafT k) else gridG k) = gridG k
    rw [if_neg hkM]
  refine ⟨P, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k hkM w hw
    rw [hPk_grid k hkM.ne]
    obtain ⟨hcov_k, -, -, -⟩ := (grid_net_tight (E := E) (hρ_pos k) (hρ_le1 k)).choose_spec
    have hgapk : 2 * ((ρ (k + 1) : NNReal) : ℝ) ≤ ((ρ k : NNReal) : ℝ) := by
      rw [coe_rho (k + 1), coe_rho k, Nat.cast_add, Nat.cast_one]
      exact rho_scale_gap hδ hM_pos hgap k
    rcases lt_or_eq_of_le (Nat.succ_le_of_lt hkM) with hk1lt | hk1eq
    · have hmid : ∀ W' ∈ P (k + 1), W'.midpoint ∈ Metric.closedBall (0 : E) 3 := by
        intro W' hW'
        rw [hPk_grid (k + 1) hk1lt.ne] at hW'
        obtain ⟨-, -, -, hmidg⟩ :=
          (grid_net_tight (E := E) (hρ_pos (k + 1)) (hρ_le1 (k + 1))).choose_spec
        exact hmidg W' hW'
      exact hcov_k w hgapk (hmid w hw)
    · subst hk1eq
      have hmid : ∀ W' ∈ P (k + 1), W'.midpoint ∈ Metric.closedBall (0 : E) 3 := by
        intro W' hW'
        rw [hPM, Finset.mem_image] at hW'
        obtain ⟨i, hi, rfl⟩ := hW'
        have hmideq : (leafT (k + 1) i).midpoint = (T i).midpoint := by
          simp only [hleafT, Tube.midpoint, Tube.mk'_x, Tube.mk'_y]
        rw [hmideq]
        have hmid_seg : (T i).midpoint ∈ segment ℝ (T i).x (T i).y := by
          have h : (T i).midpoint = (1/2 : ℝ) • (T i).x + (1/2 : ℝ) • (T i).y := by
            simp only [Tube.midpoint]; module
          rw [h]; exact ⟨1/2, 1/2, by norm_num, by norm_num, by norm_num, rfl⟩
        have hmid_mem : (T i).midpoint ∈ (T i).carrier := by
          rw [(T i).carrier_eq]
          exact Set.mem_biUnion hmid_seg (Metric.mem_closedBall_self δ.coe_nonneg)
        have h1 := hs_B1 hi hmid_mem
        rw [Metric.mem_closedBall, dist_zero_right] at h1 ⊢; linarith
      exact hcov_k w hgapk (hmid w hw)
  · intro k hk W hW
    rcases eq_or_lt_of_le hk with hkM | hkMlt
    · have hMk : M = k := hkM.symm
      subst hMk
      rw [hPM, Finset.mem_image] at hW
      obtain ⟨i, hi, rfl⟩ := hW
      have hcar : (leafT M i).carrier = (T i).carrier := leaf_carrier_eq (rho_M δ hM_pos) (T i)
      rw [hcar]
      exact fun p hp => Metric.closedBall_subset_closedBall (by norm_num) (hs_B1 hi hp)
    · rw [hPk_grid k hkMlt.ne] at hW
      obtain ⟨-, -, hloc, -⟩ := (grid_net_tight (E := E) (hρ_pos k) (hρ_le1 k)).choose_spec
      exact hloc W hW
  · intro k hk i hi
    rcases eq_or_lt_of_le hk with hkM | hkMlt
    · rw [hkM]
      refine ⟨leafT M i, by rw [hPM]; exact Finset.mem_image_of_mem _ hi, ?_⟩
      have hleaf_carr : (leafT M i).carrier = (T i).carrier :=
        leaf_carrier_eq (rho_M δ hM_pos) (T i)
      change (T i).carrier ⊆ (leafT M i).carrier
      exact hleaf_carr.symm.subset
    · rw [hPk_grid k hkMlt.ne]
      obtain ⟨hcov, -, -, -⟩ := (grid_net_tight (E := E) (hρ_pos k) (hρ_le1 k)).choose_spec
      have hρk_coe : ((ρ k : NNReal) : ℝ) = (δ : ℝ) ^ ((k : ℝ) / (M : ℝ)) := by
        change (((δ ^ ((k : ℝ) / (M : ℝ)) : NNReal)) : ℝ) = _
        rw [NNReal.coe_rpow]
      have h2δ : 2 * ((δ : NNReal) : ℝ) ≤ ((ρ k : NNReal) : ℝ) := by
        rw [hρk_coe]; exact two_delta_le_rho hδ hM_pos hgap hkMlt
      have hmid_seg : (T i).midpoint ∈ segment ℝ (T i).x (T i).y := by
        have h : (T i).midpoint = (1/2 : ℝ) • (T i).x + (1/2 : ℝ) • (T i).y := by
          simp only [Tube.midpoint]; module
        rw [h]; exact ⟨1/2, 1/2, by norm_num, by norm_num, by norm_num, rfl⟩
      have hmid_mem : (T i).midpoint ∈ (T i).carrier := by
        rw [(T i).carrier_eq]
        exact Set.mem_biUnion hmid_seg (Metric.mem_closedBall_self δ.coe_nonneg)
      have hmid_B3 : (T i).midpoint ∈ Metric.closedBall (0 : E) 3 := by
        have h1 := hs_B1 hi hmid_mem
        rw [Metric.mem_closedBall, dist_zero_right] at h1 ⊢; linarith
      obtain ⟨W, hW, hWbody, -, -⟩ := hcov (T i) h2δ hmid_B3
      exact ⟨W, hW, hWbody⟩
  · intro k hk V
    rcases eq_or_lt_of_le hk with hkM | hkMlt
    · have hMk : M = k := hkM.symm
      subst hMk
      refine le_trans (Finset.card_le_one.mpr ?_) (Nat.one_le_iff_ne_zero.mpr (by positivity))
      have hδM : δ = ρ M := (rho_M δ hM_pos).symm
      intro a ha b hb
      obtain ⟨haP, U, -, hUa, hUV⟩ := Finset.mem_filter.mp ha
      obtain ⟨hbP, U', -, hU'b, hU'V⟩ := Finset.mem_filter.mp hb
      have haV : a.carrier = V.carrier := by
        rw [← carrier_eq_of_subset' hδM U a hUa, carrier_eq_of_subset' hδM U V hUV]
      have hbV : b.carrier = V.carrier := by
        rw [← carrier_eq_of_subset' hδM U' b hU'b, carrier_eq_of_subset' hδM U' V hU'V]
      rw [hPM, Finset.mem_image] at haP hbP
      obtain ⟨i, hi, rfl⟩ := haP
      obtain ⟨j, hj, rfl⟩ := hbP
      have hcia : (leafT M i).carrier = (T i).carrier := leaf_carrier_eq (rho_M δ hM_pos) (T i)
      have hcjb : (leafT M j).carrier = (T j).carrier := leaf_carrier_eq (rho_M δ hM_pos) (T j)
      have hTij : (T i).carrier = (T j).carrier := by
        rw [← hcia, ← hcjb, haV, hbV]
      rw [hT_inj (Finset.mem_coe.mpr hi) (Finset.mem_coe.mpr hj) hTij]
    · rw [hPk_grid k hkMlt.ne]
      obtain ⟨-, hsep, -, -⟩ := (grid_net_tight (E := E) (hρ_pos k) (hρ_le1 k)).choose_spec
      exact grid_overlap_tight (δ := δ) (hρ_pos k) (gridG k) hsep V
  · intro i hi
    refine ⟨leafT M i, by rw [hPM]; exact Finset.mem_image_of_mem _ hi,
      leaf_carrier_eq (rho_M δ hM_pos) (T i), ?_, ?_⟩
    · simp only [hleafT, Tube.midpoint, Tube.mk'_x, Tube.mk'_y]
    · simp only [hleafT, Tube.direction, Tube.mk'_x, Tube.mk'_y]
  · intro k hkM
    set n : ℕ := Module.finrank ℝ E with hn_def
    set ρk : ℝ := ((ρ k : NNReal) : ℝ) with hρk_def
    have hρk_pos : (0 : ℝ) < ρk := by rw [hρk_def]; exact_mod_cast hρ_pos k
    have hρk_le1 : ρk ≤ 1 := hρ_le1 k
    · rw [hPk_grid k hkM.ne]
      obtain ⟨-, hsep, hball, -⟩ := (grid_net_tight (E := E) (hρ_pos k) (hρ_le1 k)).choose_spec
      set G := (grid_net_tight (E := E) (hρ_pos k) (hρ_le1 k)).choose with hG
      have hx_loc : ∀ W ∈ G, ‖W.x - (0 : E)‖ ≤ 5 := by
        intro W hW
        have hxmem : W.x ∈ W.carrier :=
          W.carrier_eq ▸ Set.mem_iUnion₂.mpr
            ⟨W.x, left_mem_segment ℝ W.x W.y, Metric.mem_closedBall_self (by positivity)⟩
        have h5 := hball W hW hxmem
        rw [Metric.mem_closedBall, dist_zero_right] at h5; rwa [sub_zero]
      have hy_loc : ∀ W ∈ G, ‖W.y - (0 : E)‖ ≤ 5 := by
        intro W hW
        have hymem : W.y ∈ W.carrier :=
          W.carrier_eq ▸ Set.mem_iUnion₂.mpr
            ⟨W.y, right_mem_segment ℝ W.x W.y, Metric.mem_closedBall_self (by positivity)⟩
        have h5 := hball W hW hymem
        rw [Metric.mem_closedBall, dist_zero_right] at h5; rwa [sub_zero]
      have hpack := card_le_of_L1_separated_in_box (E := E) G
        (fun W => W.x) (fun W => W.y) (0 : E) (0 : E)
        (R := 5) (r := ρk / 32) (by positivity)
        (fun a ha b hb hab => by
          have := hsep a ha b hb hab; rw [hρk_def]; exact this)
        hx_loc hy_loc
      have hbase_eq : ((5 : ℝ) + (ρk / 32) / 4) / ((ρk / 32) / 4) = 640 / ρk + 1 := by
        field_simp; ring
      rw [hbase_eq] at hpack
      have htarget_eq : (641 : ℝ) ^ (2 * n) * ((4 : ℝ) / ρk) ^ (2 * n)
          = (2564 / ρk) ^ (2 * n) := by
        rw [← mul_pow]; congr 1; field_simp; ring
      rw [htarget_eq]
      refine le_trans hpack (pow_le_pow_left₀ (by positivity) ?_ _)
      have hcalc : 640 / ρk + 1 = (640 + ρk) / ρk := by field_simp
      rw [hcalc]
      gcongr
      linarith [hρk_le1]

end Tube
