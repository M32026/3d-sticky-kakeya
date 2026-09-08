/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Tube.Fubini
public import Kakeya.Thickness.ConvexSpaceBody
public import Kakeya.Tube.Basic
public import Kakeya.Tube.Volume

/-!
# Telescoping the volume of iterated cthickenings

`Kakeya.volume_thickening_telescope_paper_four` bounds the volume of the `4ρ`-cthickening of a
convex body against the volume of its `ρ`-cthickening, uniformly along a chain of scales.  It is
the volume input of GWZ Lemma 7.4 and has no other consumer, which is why it sits under
`Kakeya.ParentBodyDensity` rather than at the top level: `maxDensity_le_prod_of_uniform_at_scales`
is the one result that needs it.

Lemma 7.4 is *not* specific to the sticky Kakeya argument: besides `Kakeya.StickyKakeya.Lemma75`
it is used by `Kakeya.MultiScaleFac`.  Those two are independent subtrees, so Lemma 7.4 and this
helper sit under `Kakeya.Uniform` — the layer both of them already depend on — rather than inside
either one.

It cannot live in the `Kakeya.Thickness.*` family: the proof goes through the tube volume bound
`Tube.volume_cthickening_le` (`Kakeya.Tube.Volume`) and the Fubini ratio
`Tube.cthickening_inter_body_ratio_div_le_toReal` (`Kakeya.Tube.Fubini`), both of which sit *above*
the
thickness layer.  Everything in this development that is free of both has been pushed down:
the `ConvexSpaceBody` cthickening-volume bounds are in `Kakeya.Thickness.ConvexSpaceBody`, and the
`Metric.thickness` facts they rest on are in `Kakeya.Thickness.Cthickening`.
-/

@[expose] public section


open MeasureTheory

namespace Tube


private lemma prod_range_div_telescope (N : ℕ) (g : ℕ → ℝ) (hg : ∀ i ≤ N, g i ≠ 0) :
    ∏ i ∈ Finset.range N, (g i / g (i + 1)) = g 0 / g N := by
  induction N with
  | zero => simp [div_self (hg 0 le_rfl)]
  | succ k IH =>
    rw [Finset.prod_range_succ, IH (fun i hi => hg i (hi.trans (Nat.le_succ k)))]
    field_simp [hg k (Nat.le_succ k), hg (k + 1) le_rfl]

private lemma prod_castSucc_succ_pow_div_eq
    (M : ℕ) (ρr : Fin (M + 1) → ℝ) (δr : ℝ) (p : ℕ)
    (hρr_M : ρr (Fin.last M) = δr)
    (hρr_pos : ∀ m, 0 < ρr m) :
    ∏ m : Fin M, ((ρr m.castSucc) ^ p / (ρr m.succ) ^ p) = ρr 0 ^ p / δr ^ p := by
  let f : ℕ → ℝ := fun i =>
    if h : i < M + 1 then (ρr ⟨i, h⟩) ^ p else (1 : ℝ)
  have hf_pos_ne : ∀ i ≤ M, f i ≠ 0 := fun i hi => by
    change (if h : i < M + 1 then (ρr ⟨i, h⟩) ^ p else (1 : ℝ)) ≠ 0
    rw [dif_pos (Nat.lt_succ_of_le hi)]; exact (pow_pos (hρr_pos _) _).ne'
  have hf0 : f 0 = ρr 0 ^ p := by
    change (if h : (0 : ℕ) < M + 1 then (ρr ⟨0, h⟩) ^ p else (1 : ℝ)) = ρr 0 ^ p
    rw [dif_pos (Nat.succ_pos _), show ρr ⟨0, Nat.succ_pos _⟩ = ρr 0 from rfl]
  have hfM : f M = δr ^ p := by
    change (if h : M < M + 1 then (ρr ⟨M, h⟩) ^ p else (1 : ℝ)) = δr ^ p
    rw [dif_pos (Nat.lt_succ_self _),
      show ρr ⟨M, Nat.lt_succ_self _⟩ = ρr (Fin.last M) from rfl, hρr_M]
  calc ∏ m : Fin M, ((ρr m.castSucc) ^ p / (ρr m.succ) ^ p)
      = ∏ m : Fin M, (f m.val / f (m.val + 1)) := by
        refine Finset.prod_congr rfl fun m _ => ?_
        change (ρr m.castSucc) ^ p / (ρr m.succ) ^ p =
          (if h : m.val < M + 1 then (ρr ⟨m.val, h⟩) ^ p else (1 : ℝ)) /
          (if h : m.val + 1 < M + 1 then (ρr ⟨m.val + 1, h⟩) ^ p else (1 : ℝ))
        rw [dif_pos (Nat.lt_succ_of_lt m.isLt), dif_pos (by omega : m.val + 1 < M + 1)]
        rfl
    _ = ∏ i ∈ Finset.range M, (f i / f (i + 1)) :=
          Fin.prod_univ_eq_prod_range (fun i => f i / f (i + 1)) M
    _ = f 0 / f M := prod_range_div_telescope M f hf_pos_ne
    _ = ρr 0 ^ p / δr ^ p := by rw [hf0, hfM]

/-- **4ρ-tolerant volume telescope.**  The product of per-scale volume ratios at thickening radius
`4·ρ_succ`, on both the `K`-cthickening and the par-cthickening, telescopes into a dimension-only
constant times `vol(cth(4δ) K) / (δ^(n-1)·vol(cth (ρ 0) K))`.  It requires the separation
`4·ρ_succ(m) ≤ ρ_castSucc(m)`, and the coarsest scale need only satisfy `1 ≤ ρ 0 ≤ 4`. -/
theorem volume_thickening_telescope_paper_four
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [Nontrivial E] [MeasurableSpace E] [BorelSpace E] :
    ∃ Cdim : ℝ, 0 < Cdim ∧ ∀ (R : ℝ), 1 ≤ R →
      ∀ {δ : NNReal}, 0 < δ → δ ≤ 1 →
      ∀ (M : ℕ), 0 < M → ∀ (ρ : Fin (M + 1) → NNReal),
      1 ≤ ρ 0 → ρ 0 ≤ 4 → ρ (Fin.last M) = δ → Antitone ρ →
      (∀ m : Fin M, 4 * (ρ m.succ : ℝ) ≤ (ρ m.castSucc : ℝ)) →
      ∀ (K : ConvexSpaceBody E),
      K.carrier ⊆ Metric.closedBall (0 : E) R →
      0 < volume.real K.carrier →
      ∀ (par : ∀ m : Fin M, Tube (ρ m.castSucc) E),
      (∀ m : Fin M, (par m).carrier ⊆ Metric.closedBall (0 : E) (R + 3)) →
      ∏ m : Fin M,
          volume.real
            ((ConvexSpaceBody.cthickening (4 * (ρ m.succ : ℝ)) K).carrier
              ∩ Metric.cthickening (4 * (ρ m.succ : ℝ)) (par m).carrier)
          / ((ρ m.succ : ℝ) ^ (Module.finrank ℝ E - 1))
        ≤ Cdim ^ M * (ρ 0 : ℝ) ^ (Module.finrank ℝ E - 1)
              * volume.real (Metric.cthickening (4 * (δ : ℝ)) K.carrier)
            / ((δ : ℝ) ^ (Module.finrank ℝ E - 1)
                * volume.real (Metric.cthickening ((ρ 0 : ℝ)) K.carrier)) := by
  classical
  set n : ℕ := Module.finrank ℝ E with hn_def
  obtain ⟨C_F, hC_F_pos, hC_F⟩ :=
    Tube.cthickening_inter_body_ratio_div_le_toReal (E := E)
  obtain ⟨CvolNN, hCvolNN_pos, hCvolNN⟩ := Tube.volume_cthickening_le (E := E)
  obtain ⟨Cdbl, hCdbl_pos, hCdbl⟩ := Kakeya.volume_cthickening_four_le (E := E)
  set Cvol_cth : ℝ := (CvolNN : ℝ) with hCvol_cth_def
  have hCvol_cth_pos : 0 < Cvol_cth := by exact_mod_cast hCvolNN_pos
  set Cdim : ℝ := C_F * Cvol_cth * Cdbl + 1 with hCdim_def
  have hCdim_pos : 0 < Cdim := by
    rw [hCdim_def]; positivity
  refine ⟨Cdim, hCdim_pos, ?_⟩
  intro R hR_ge_one δ hδ_pos hδ_le_one M hM_pos ρ hρ_0_ge_one hρ_0_le_four
    hρ_M hρ_anti hsep K hK_sub_R hK_vol_pos
    par hpar_sub
  set δr : ℝ := (δ : ℝ) with hδr_def
  set ρr : Fin (M + 1) → ℝ := fun k => ((ρ k : NNReal) : ℝ) with hρr_def
  have hδr_pos : (0 : ℝ) < δr := by exact_mod_cast hδ_pos
  have hδr_le_one : δr ≤ 1 := by exact_mod_cast hδ_le_one
  have hρ_pos : ∀ k : Fin (M + 1), 0 < ρ k := fun k => by
    have hle : ρ (Fin.last M) ≤ ρ k := hρ_anti (Fin.le_last k)
    rw [hρ_M] at hle; exact lt_of_lt_of_le hδ_pos hle
  have hρr_pos : ∀ k : Fin (M + 1), (0 : ℝ) < ρr k := fun k => by exact_mod_cast hρ_pos k
  have hρr_M : ρr (Fin.last M) = δr := by
    simp only [hρr_def, hδr_def]; exact_mod_cast hρ_M
  have hρ_castSucc_le_four : ∀ m : Fin M, ρ m.castSucc ≤ 4 := fun m => by
    have := hρ_anti (Fin.zero_le m.castSucc)
    exact le_trans this hρ_0_le_four
  have hρ_castSucc_pos : ∀ m : Fin M, 0 < ρ m.castSucc := fun m => hρ_pos m.castSucc
  have hρ_succ_pos : ∀ m : Fin M, 0 < ρ m.succ := fun m => hρ_pos m.succ
  have hρ_succ_le_castSucc : ∀ m : Fin M, ρ m.succ ≤ ρ m.castSucc := fun m =>
    hρ_anti (Fin.castSucc_le_succ m)
  have hsep_r : ∀ m : Fin M, 4 * ρr m.succ ≤ ρr m.castSucc := hsep
  have hρ_castSucc_le_four_r : ∀ m : Fin M, ρr m.castSucc ≤ 4 := fun m => by
    exact_mod_cast hρ_castSucc_le_four m
  have hρr_0_pos : 0 < ρr 0 := hρr_pos 0
  have hρr_0_ge_one : 1 ≤ ρr 0 := by exact_mod_cast hρ_0_ge_one
  have hρr_0_le_four : ρr 0 ≤ 4 := by exact_mod_cast hρ_0_le_four
  have h4ρsucc_le_castSucc_nn : ∀ m : Fin M, (4 : NNReal) * ρ m.succ ≤ ρ m.castSucc := fun m => by
    have := hsep m
    rw [← NNReal.coe_le_coe]; push_cast; exact this
  have hKρ_vol_pos : ∀ ρ' : ℝ, 0 < ρ' →
      0 < volume.real (Metric.cthickening ρ' K.carrier) := fun ρ' hρ' => by
    obtain ⟨p, hp⟩ := K.nonempty
    have h_ball : Metric.closedBall p ρ' ⊆ Metric.cthickening ρ' K.carrier := by
      intro x hx
      refine Metric.mem_cthickening_of_dist_le x p ρ' K.carrier hp ?_
      rwa [Metric.mem_closedBall] at hx
    have hVolBall_pos :
        0 < volume.real (Metric.closedBall p ρ') := by
      have h_ball_pos : 0 < volume (Metric.closedBall p ρ') := by
        rw [MeasureTheory.Measure.addHaar_closedBall_center
          (volume : MeasureTheory.Measure E) p ρ',
          InnerProductSpace.volume_closedBall]
        apply ENNReal.mul_pos
        · exact pow_ne_zero _ (ENNReal.ofReal_ne_zero_iff.mpr hρ')
        · rw [ENNReal.ofReal_ne_zero_iff]; positivity
      have h_ball_fin : volume (Metric.closedBall p ρ') ≠ ⊤ :=
        (isCompact_closedBall _ _).measure_lt_top.ne
      change 0 < (volume (Metric.closedBall p ρ')).toReal
      rw [ENNReal.toReal_pos_iff]
      exact ⟨h_ball_pos, lt_top_iff_ne_top.mpr h_ball_fin⟩
    exact lt_of_lt_of_le hVolBall_pos (measureReal_mono h_ball
      K.isCompact.cthickening.measure_lt_top.ne)
  have hTρ_vol_pos : ∀ m : Fin M,
      0 < volume.real (Metric.cthickening ((ρ m.castSucc : ℝ)) (par m).carrier) := fun m => by
    obtain ⟨p, hp⟩ := (par m).toConvexSpaceBody.nonempty
    have h_ball : Metric.closedBall p (ρ m.castSucc : ℝ)
        ⊆ Metric.cthickening ((ρ m.castSucc : ℝ)) (par m).carrier := by
      intro x hx
      refine Metric.mem_cthickening_of_dist_le x p (ρ m.castSucc : ℝ) (par m).carrier hp ?_
      rwa [Metric.mem_closedBall] at hx
    have hVolBall_pos :
        0 < volume.real (Metric.closedBall p (ρ m.castSucc : ℝ)) := by
      have hpos : (0 : ℝ) < (ρ m.castSucc : ℝ) := by exact_mod_cast hρ_castSucc_pos m
      have h_ball_pos : 0 < volume (Metric.closedBall p (ρ m.castSucc : ℝ)) := by
        rw [MeasureTheory.Measure.addHaar_closedBall_center
          (volume : MeasureTheory.Measure E) p (ρ m.castSucc : ℝ),
          InnerProductSpace.volume_closedBall]
        apply ENNReal.mul_pos
        · exact pow_ne_zero _ (ENNReal.ofReal_ne_zero_iff.mpr hpos)
        · rw [ENNReal.ofReal_ne_zero_iff]; positivity
      have h_ball_fin : volume (Metric.closedBall p (ρ m.castSucc : ℝ)) ≠ ⊤ :=
        (isCompact_closedBall _ _).measure_lt_top.ne
      change 0 < (volume (Metric.closedBall p (ρ m.castSucc : ℝ))).toReal
      rw [ENNReal.toReal_pos_iff]
      exact ⟨h_ball_pos, lt_top_iff_ne_top.mpr h_ball_fin⟩
    exact lt_of_lt_of_le hVolBall_pos (measureReal_mono h_ball
      (par m).isCompact.cthickening.measure_lt_top.ne)
  have hT_vol_cth_le : ∀ m : Fin M,
      volume.real (Metric.cthickening ((ρ m.castSucc : ℝ)) (par m).carrier)
        ≤ Cvol_cth * (ρ m.castSucc : ℝ) ^ (n - 1) := fun m => by
    have h := hCvolNN (ρ m.castSucc) (hρ_castSucc_pos m) (hρ_castSucc_le_four m)
      (ρ m.castSucc) le_rfl (par m)
    have hRHS_fin : (CvolNN : ENNReal) * (ρ m.castSucc : ENNReal) ^ (n - 1) ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.coe_ne_top (ENNReal.pow_ne_top ENNReal.coe_ne_top)
    have hreal := ENNReal.toReal_mono hRHS_fin h
    simpa [ENNReal.toReal_mul, ENNReal.coe_toReal, ENNReal.toReal_pow,
      MeasureTheory.Measure.real, hCvol_cth_def] using hreal
  have h_cth_4succ_sub_castSucc : ∀ m : Fin M,
      Metric.cthickening (4 * ρr m.succ) (par m).carrier
        ⊆ Metric.cthickening ((ρ m.castSucc : ℝ)) (par m).carrier := fun m =>
    Metric.cthickening_mono (hsep_r m) _
  have h_factor : ∀ m : Fin M,
      volume.real
          ((ConvexSpaceBody.cthickening (4 * ρr m.succ) K).carrier
            ∩ Metric.cthickening (4 * ρr m.succ) (par m).carrier)
        / (ρr m.succ ^ (n - 1))
        ≤ Cdim *
            ((ρr m.castSucc) ^ (n - 1) / (ρr m.succ) ^ (n - 1)) *
            (volume.real (Metric.cthickening (4 * ρr m.succ) K.carrier)
              / volume.real (Metric.cthickening (4 * ρr m.castSucc) K.carrier)) := fun m => by
    have hρcs_pow_pos : (0 : ℝ) < (ρr m.castSucc) ^ (n - 1) := pow_pos (hρr_pos _) _
    have hρs_pow_pos : (0 : ℝ) < (ρr m.succ) ^ (n - 1) := pow_pos (hρr_pos _) _
    have h4ρsucc_pos : (0 : ℝ) < 4 * ρr m.succ := by
      have := hρr_pos m.succ; linarith
    have h4ρcs_pos : (0 : ℝ) < 4 * ρr m.castSucc := by
      have := hρr_pos m.castSucc; linarith
    have hK4ρcs_pos := hKρ_vol_pos (4 * ρr m.castSucc) h4ρcs_pos
    have hK4ρs_pos := hKρ_vol_pos (4 * ρr m.succ) h4ρsucc_pos
    have hKρcs_pos := hKρ_vol_pos (ρr m.castSucc) (hρr_pos _)
    have hTρcs_pos := hTρ_vol_pos m
    have h_inter_sub :
        (ConvexSpaceBody.cthickening (4 * ρr m.succ) K).carrier
            ∩ Metric.cthickening (4 * ρr m.succ) (par m).carrier
          ⊆ Metric.cthickening (4 * ρr m.succ) K.carrier
              ∩ Metric.cthickening ((ρ m.castSucc : ℝ)) (par m).carrier := by
      refine Set.subset_inter ?_ ?_
      · exact fun x hx => hx.1
      · exact fun x hx => h_cth_4succ_sub_castSucc m hx.2
    have h_LHS_le_inter :
        volume.real
            ((ConvexSpaceBody.cthickening (4 * ρr m.succ) K).carrier
              ∩ Metric.cthickening (4 * ρr m.succ) (par m).carrier)
          ≤ volume.real
              (Metric.cthickening (4 * ρr m.succ) K.carrier
                ∩ Metric.cthickening ((ρ m.castSucc : ℝ)) (par m).carrier) := by
      have hfin : volume
          (Metric.cthickening (4 * ρr m.succ) K.carrier
            ∩ Metric.cthickening ((ρ m.castSucc : ℝ)) (par m).carrier) ≠ ⊤ :=
        (lt_of_le_of_lt (measure_mono Set.inter_subset_left)
          K.isCompact.cthickening.measure_lt_top).ne
      exact measureReal_mono h_inter_sub hfin
    have hcast_inner : ((4 * ρ m.succ : NNReal) : ℝ) = 4 * ρr m.succ := by
      push_cast; rfl
    have hC_F_applied := hC_F (par m) K (ρ := ρ m.castSucc) (ρ' := 4 * ρ m.succ)
      (h4ρsucc_le_castSucc_nn m) hKρcs_pos hTρcs_pos
    rw [hcast_inner] at hC_F_applied
    simp only [← MeasureTheory.measureReal_def] at hC_F_applied
    have h_inter_bound :
        volume.real
            (Metric.cthickening (4 * ρr m.succ) K.carrier
              ∩ Metric.cthickening ((ρ m.castSucc : ℝ)) (par m).carrier)
          ≤ C_F * volume.real (Metric.cthickening ((ρ m.castSucc : ℝ)) (par m).carrier)
              * (volume.real (Metric.cthickening (4 * ρr m.succ) K.carrier)
                  / volume.real (Metric.cthickening (ρr m.castSucc) K.carrier)) := by
      rw [div_le_iff₀ hTρcs_pos] at hC_F_applied
      calc volume.real
              (Metric.cthickening (4 * ρr m.succ) K.carrier
                ∩ Metric.cthickening ((ρ m.castSucc : ℝ)) (par m).carrier)
          ≤ C_F * volume.real (Metric.cthickening (4 * ρr m.succ) K.carrier)
              / volume.real (Metric.cthickening (ρr m.castSucc) K.carrier)
              * volume.real (Metric.cthickening ((ρ m.castSucc : ℝ)) (par m).carrier) :=
            hC_F_applied
        _ = C_F * volume.real (Metric.cthickening ((ρ m.castSucc : ℝ)) (par m).carrier)
              * (volume.real (Metric.cthickening (4 * ρr m.succ) K.carrier)
                  / volume.real (Metric.cthickening (ρr m.castSucc) K.carrier)) := by
            rw [show (ρr m.castSucc) = ((ρ m.castSucc : ℝ)) from rfl]; ring
    have h_inter_bound2 :
        volume.real
            (Metric.cthickening (4 * ρr m.succ) K.carrier
              ∩ Metric.cthickening ((ρ m.castSucc : ℝ)) (par m).carrier)
          ≤ C_F * (Cvol_cth * (ρr m.castSucc) ^ (n - 1))
              * (volume.real (Metric.cthickening (4 * ρr m.succ) K.carrier)
                  / volume.real (Metric.cthickening (ρr m.castSucc) K.carrier)) := by
      refine h_inter_bound.trans ?_
      have h_ratio_nn : 0 ≤
          volume.real (Metric.cthickening (4 * ρr m.succ) K.carrier)
            / volume.real (Metric.cthickening (ρr m.castSucc) K.carrier) :=
        div_nonneg measureReal_nonneg measureReal_nonneg
      have hT_le : volume.real (Metric.cthickening ((ρ m.castSucc : ℝ)) (par m).carrier)
          ≤ Cvol_cth * (ρr m.castSucc) ^ (n - 1) := hT_vol_cth_le m
      have h1 : C_F * volume.real (Metric.cthickening ((ρ m.castSucc : ℝ)) (par m).carrier)
          ≤ C_F * (Cvol_cth * (ρr m.castSucc) ^ (n - 1)) :=
        mul_le_mul_of_nonneg_left hT_le hC_F_pos.le
      exact mul_le_mul_of_nonneg_right h1 h_ratio_nn
    have h_doubling :
        volume.real (Metric.cthickening (4 * ρr m.succ) K.carrier)
            / volume.real (Metric.cthickening (ρr m.castSucc) K.carrier)
          ≤ Cdbl * (volume.real (Metric.cthickening (4 * ρr m.succ) K.carrier)
              / volume.real (Metric.cthickening (4 * ρr m.castSucc) K.carrier)) := by
      have hdbl := hCdbl K (ρr m.castSucc) (hρr_pos _) (hρ_castSucc_le_four_r m)
      rw [div_le_iff₀ hKρcs_pos]
      rw [mul_comm Cdbl, mul_assoc, div_mul_eq_mul_div, le_div_iff₀ hK4ρcs_pos]
      have hnum_nn : 0 ≤ volume.real (Metric.cthickening (4 * ρr m.succ) K.carrier) :=
        measureReal_nonneg
      calc volume.real (Metric.cthickening (4 * ρr m.succ) K.carrier)
              * volume.real (Metric.cthickening (4 * ρr m.castSucc) K.carrier)
          ≤ volume.real (Metric.cthickening (4 * ρr m.succ) K.carrier)
              * (Cdbl * volume.real (Metric.cthickening (ρr m.castSucc) K.carrier)) :=
            mul_le_mul_of_nonneg_left hdbl hnum_nn
        _ = volume.real (Metric.cthickening (4 * ρr m.succ) K.carrier)
              * (Cdbl * volume.real (Metric.cthickening (ρr m.castSucc) K.carrier)) := by ring
    have h_inter_bound3 :
        volume.real
            (Metric.cthickening (4 * ρr m.succ) K.carrier
              ∩ Metric.cthickening ((ρ m.castSucc : ℝ)) (par m).carrier)
          ≤ (C_F * Cvol_cth * Cdbl) * (ρr m.castSucc) ^ (n - 1)
              * (volume.real (Metric.cthickening (4 * ρr m.succ) K.carrier)
                  / volume.real (Metric.cthickening (4 * ρr m.castSucc) K.carrier)) := by
      refine h_inter_bound2.trans ?_
      have hcoef_nn : 0 ≤ C_F * (Cvol_cth * (ρr m.castSucc) ^ (n - 1)) :=
        by positivity
      calc C_F * (Cvol_cth * (ρr m.castSucc) ^ (n - 1))
              * (volume.real (Metric.cthickening (4 * ρr m.succ) K.carrier)
                  / volume.real (Metric.cthickening (ρr m.castSucc) K.carrier))
          ≤ C_F * (Cvol_cth * (ρr m.castSucc) ^ (n - 1))
              * (Cdbl * (volume.real (Metric.cthickening (4 * ρr m.succ) K.carrier)
                  / volume.real (Metric.cthickening (4 * ρr m.castSucc) K.carrier))) :=
            mul_le_mul_of_nonneg_left h_doubling hcoef_nn
        _ = (C_F * Cvol_cth * Cdbl) * (ρr m.castSucc) ^ (n - 1)
              * (volume.real (Metric.cthickening (4 * ρr m.succ) K.carrier)
                  / volume.real (Metric.cthickening (4 * ρr m.castSucc) K.carrier)) := by ring
    have h_LHS_div_le :
        volume.real
            ((ConvexSpaceBody.cthickening (4 * ρr m.succ) K).carrier
              ∩ Metric.cthickening (4 * ρr m.succ) (par m).carrier)
          / (ρr m.succ) ^ (n - 1)
            ≤ ((C_F * Cvol_cth * Cdbl) * (ρr m.castSucc) ^ (n - 1)
                * (volume.real (Metric.cthickening (4 * ρr m.succ) K.carrier)
                    / volume.real (Metric.cthickening (4 * ρr m.castSucc) K.carrier)))
                / (ρr m.succ) ^ (n - 1) :=
      div_le_div_of_nonneg_right (h_LHS_le_inter.trans h_inter_bound3) hρs_pow_pos.le
    refine h_LHS_div_le.trans ?_
    have h_simp :
        ((C_F * Cvol_cth * Cdbl) * (ρr m.castSucc) ^ (n - 1)
            * (volume.real (Metric.cthickening (4 * ρr m.succ) K.carrier)
                / volume.real (Metric.cthickening (4 * ρr m.castSucc) K.carrier)))
            / (ρr m.succ) ^ (n - 1)
          = (C_F * Cvol_cth * Cdbl)
              * ((ρr m.castSucc) ^ (n - 1) / (ρr m.succ) ^ (n - 1))
              * (volume.real (Metric.cthickening (4 * ρr m.succ) K.carrier)
                  / volume.real (Metric.cthickening (4 * ρr m.castSucc) K.carrier)) := by
      field_simp
    rw [h_simp]
    have h_C_le_Cdim : C_F * Cvol_cth * Cdbl ≤ Cdim := by rw [hCdim_def]; linarith
    have h_pos_factor : 0 ≤ (ρr m.castSucc) ^ (n - 1) / (ρr m.succ) ^ (n - 1) :=
      div_nonneg (pow_nonneg (hρr_pos _).le _) hρs_pow_pos.le
    have h_pos_factor2 :
        0 ≤ volume.real (Metric.cthickening (4 * ρr m.succ) K.carrier)
            / volume.real (Metric.cthickening (4 * ρr m.castSucc) K.carrier) :=
      div_nonneg measureReal_nonneg measureReal_nonneg
    have hmul1 : (C_F * Cvol_cth * Cdbl) * ((ρr m.castSucc) ^ (n - 1) / (ρr m.succ) ^ (n - 1))
        ≤ Cdim * ((ρr m.castSucc) ^ (n - 1) / (ρr m.succ) ^ (n - 1)) :=
      mul_le_mul_of_nonneg_right h_C_le_Cdim h_pos_factor
    exact mul_le_mul_of_nonneg_right hmul1 h_pos_factor2
  have h_telescope_ρ : ∏ m : Fin M, ((ρr m.castSucc) ^ (n - 1) / (ρr m.succ) ^ (n - 1))
      = ρr 0 ^ (n - 1) / δr ^ (n - 1) :=
    prod_castSucc_succ_pow_div_eq M ρr δr (n - 1) hρr_M hρr_pos
  have h_telescope_K :
      ∏ m : Fin M,
          (volume.real (Metric.cthickening (4 * ρr m.succ) K.carrier)
            / volume.real (Metric.cthickening (4 * ρr m.castSucc) K.carrier))
        = volume.real (Metric.cthickening (4 * δr) K.carrier)
            / volume.real (Metric.cthickening (4 * ρr 0) K.carrier) := by
    let g : ℕ → ℝ := fun i =>
      if h : i < M + 1 then
        volume.real (Metric.cthickening (4 * ρr ⟨i, h⟩) K.carrier) else (1 : ℝ)
    have hg_pos_ne : ∀ i ≤ M, g i ≠ 0 := fun i hi => by
      change (if h : i < M + 1 then
        volume.real (Metric.cthickening (4 * ρr ⟨i, h⟩) K.carrier) else (1 : ℝ)) ≠ 0
      rw [dif_pos (Nat.lt_succ_of_le hi)]
      refine (hKρ_vol_pos (4 * ρr ⟨i, Nat.lt_succ_of_le hi⟩) ?_).ne'
      have := hρr_pos ⟨i, Nat.lt_succ_of_le hi⟩; linarith
    have hg0 : g 0 = volume.real (Metric.cthickening (4 * ρr 0) K.carrier) := by
      change (if h : (0 : ℕ) < M + 1 then
        volume.real (Metric.cthickening (4 * ρr ⟨0, h⟩) K.carrier) else (1 : ℝ))
          = volume.real (Metric.cthickening (4 * ρr 0) K.carrier)
      rw [dif_pos (Nat.succ_pos _),
        show ρr ⟨0, Nat.succ_pos _⟩ = ρr 0 from rfl]
    have hgM : g M = volume.real (Metric.cthickening (4 * δr) K.carrier) := by
      change (if h : M < M + 1 then
        volume.real (Metric.cthickening (4 * ρr ⟨M, h⟩) K.carrier) else (1 : ℝ))
          = volume.real (Metric.cthickening (4 * δr) K.carrier)
      rw [dif_pos (Nat.lt_succ_self _),
        show ρr ⟨M, Nat.lt_succ_self _⟩ = ρr (Fin.last M) from rfl, hρr_M]
    calc ∏ m : Fin M,
            (volume.real (Metric.cthickening (4 * ρr m.succ) K.carrier)
              / volume.real (Metric.cthickening (4 * ρr m.castSucc) K.carrier))
        = ∏ m : Fin M, (g (m.val + 1) / g m.val) := by
            refine Finset.prod_congr rfl fun m _ => ?_
            change volume.real (Metric.cthickening (4 * ρr m.succ) K.carrier)
                / volume.real (Metric.cthickening (4 * ρr m.castSucc) K.carrier)
              = (if h : m.val + 1 < M + 1 then
                  volume.real (Metric.cthickening (4 * ρr ⟨m.val + 1, h⟩) K.carrier)
                    else (1 : ℝ))
                / (if h : m.val < M + 1 then
                  volume.real (Metric.cthickening (4 * ρr ⟨m.val, h⟩) K.carrier) else (1 : ℝ))
            rw [dif_pos (Nat.lt_succ_of_lt m.isLt), dif_pos (by omega : m.val + 1 < M + 1)]
            rfl
      _ = ∏ i ∈ Finset.range M, (g (i + 1) / g i) :=
            Fin.prod_univ_eq_prod_range (fun i => g (i + 1) / g i) M
      _ = g M / g 0 := by
            have h_inv : ∏ i ∈ Finset.range M, (g (i + 1) / g i)
                = (∏ i ∈ Finset.range M, ((g i)⁻¹ / (g (i + 1))⁻¹)) := by
              refine Finset.prod_congr rfl fun i _ => ?_
              rw [inv_div_inv]
            rw [h_inv]
            have h_g_inv_ne : ∀ i ≤ M, (g i)⁻¹ ≠ 0 := fun i hi => by
              rw [ne_eq, inv_eq_zero]; exact hg_pos_ne i hi
            rw [prod_range_div_telescope M (fun i => (g i)⁻¹) h_g_inv_ne]
            rw [inv_div_inv]
      _ = volume.real (Metric.cthickening (4 * δr) K.carrier)
            / volume.real (Metric.cthickening (4 * ρr 0) K.carrier) := by rw [hgM, hg0]
  have h_lhs_nn : ∀ m : Fin M,
      0 ≤ volume.real
          ((ConvexSpaceBody.cthickening (4 * ρr m.succ) K).carrier
            ∩ Metric.cthickening (4 * ρr m.succ) (par m).carrier)
        / (ρr m.succ ^ (n - 1)) := fun m =>
    div_nonneg measureReal_nonneg (pow_nonneg (hρr_pos _).le _)
  have h_prod_le_factor : ∏ m : Fin M,
        volume.real
            ((ConvexSpaceBody.cthickening (4 * ρr m.succ) K).carrier
              ∩ Metric.cthickening (4 * ρr m.succ) (par m).carrier)
          / (ρr m.succ ^ (n - 1))
      ≤ ∏ m : Fin M, Cdim *
          ((ρr m.castSucc) ^ (n - 1) / (ρr m.succ) ^ (n - 1)) *
          (volume.real (Metric.cthickening (4 * ρr m.succ) K.carrier)
            / volume.real (Metric.cthickening (4 * ρr m.castSucc) K.carrier)) :=
    Finset.prod_le_prod (fun m _ => h_lhs_nn m) (fun m _ => h_factor m)
  have h_prod_const :
      ∏ m : Fin M, Cdim *
          ((ρr m.castSucc) ^ (n - 1) / (ρr m.succ) ^ (n - 1)) *
          (volume.real (Metric.cthickening (4 * ρr m.succ) K.carrier)
            / volume.real (Metric.cthickening (4 * ρr m.castSucc) K.carrier))
        = Cdim ^ M
            * (∏ m : Fin M, ((ρr m.castSucc) ^ (n - 1) / (ρr m.succ) ^ (n - 1)))
            * ∏ m : Fin M, (volume.real (Metric.cthickening (4 * ρr m.succ) K.carrier)
                / volume.real (Metric.cthickening (4 * ρr m.castSucc) K.carrier)) := by
    rw [Finset.prod_mul_distrib]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have h_cthρ0_le_cth4ρ0 :
      volume.real (Metric.cthickening (ρr 0) K.carrier)
        ≤ volume.real (Metric.cthickening (4 * ρr 0) K.carrier) := by
    have hpos : 0 < ρr 0 := hρr_pos 0
    refine measureReal_mono (Metric.cthickening_mono (by nlinarith) _) ?_
    exact K.isCompact.cthickening.measure_lt_top.ne
  have hcthρ0_pos : 0 < volume.real (Metric.cthickening (ρr 0) K.carrier) :=
    hKρ_vol_pos (ρr 0) (hρr_pos 0)
  have hcth4ρ0_pos : 0 < volume.real (Metric.cthickening (4 * ρr 0) K.carrier) :=
    hKρ_vol_pos (4 * ρr 0) (by nlinarith)
  have hcth4δ_nn : 0 ≤ volume.real (Metric.cthickening (4 * δr) K.carrier) :=
    measureReal_nonneg
  have hρr0_pow_nn : 0 ≤ ρr 0 ^ (n - 1) := pow_nonneg (by positivity : 0 ≤ ρr 0) _
  refine h_prod_le_factor.trans ?_
  rw [h_prod_const, h_telescope_ρ, h_telescope_K]
  have hδ_pow_pos : (0 : ℝ) < δr ^ (n - 1) := pow_pos hδr_pos _
  have hCdimM_nn : (0 : ℝ) ≤ Cdim ^ M := pow_nonneg hCdim_pos.le _
  have h_num_nonneg : 0 ≤ Cdim ^ M * ρr 0 ^ (n - 1)
      * volume.real (Metric.cthickening (4 * δr) K.carrier) := by
    positivity
  have h_denom_pos : 0 < δr ^ (n - 1) * volume.real (Metric.cthickening (ρr 0) K.carrier) :=
    mul_pos hδ_pow_pos hcthρ0_pos
  have h_denom_pos4 : 0 < δr ^ (n - 1) * volume.real (Metric.cthickening (4 * ρr 0) K.carrier) :=
    mul_pos hδ_pow_pos hcth4ρ0_pos
  have h_denom_le : δr ^ (n - 1) * volume.real (Metric.cthickening (ρr 0) K.carrier)
      ≤ δr ^ (n - 1) * volume.real (Metric.cthickening (4 * ρr 0) K.carrier) :=
    mul_le_mul_of_nonneg_left h_cthρ0_le_cth4ρ0 (by positivity : 0 ≤ δr ^ (n - 1))
  have h_inv_le : (δr ^ (n - 1) * volume.real (Metric.cthickening (4 * ρr 0) K.carrier))⁻¹
      ≤ (δr ^ (n - 1) * volume.real (Metric.cthickening (ρr 0) K.carrier))⁻¹ := by
    rw [inv_eq_one_div, inv_eq_one_div]
    exact (one_div_le_one_div h_denom_pos4 h_denom_pos).mpr h_denom_le
  calc
    Cdim ^ M * (ρr 0 ^ (n - 1) / δr ^ (n - 1)) *
        (volume.real (Metric.cthickening (4 * δr) K.carrier)
          / volume.real (Metric.cthickening (4 * ρr 0) K.carrier))
        = (Cdim ^ M * ρr 0 ^ (n - 1) * volume.real (Metric.cthickening (4 * δr) K.carrier)) *
            ((δr ^ (n - 1) * volume.real (Metric.cthickening (4 * ρr 0) K.carrier))⁻¹) := by
      field_simp [hδ_pow_pos.ne', hcth4ρ0_pos.ne']
    _ ≤ (Cdim ^ M * ρr 0 ^ (n - 1) * volume.real (Metric.cthickening (4 * δr) K.carrier)) *
          ((δr ^ (n - 1) * volume.real (Metric.cthickening (ρr 0) K.carrier))⁻¹) :=
      mul_le_mul_of_nonneg_left h_inv_le h_num_nonneg
    _ = Cdim ^ M * ↑(ρ 0) ^ (n - 1) * volume.real (Metric.cthickening (4 * δr) K.carrier) /
        (δr ^ (n - 1) * volume.real (Metric.cthickening (↑(ρ 0)) K.carrier)) := by
      simp [hρr_def, div_eq_mul_inv]

end Tube
