/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Tube.EDPacking.BadCount
public import Kakeya.Tube.EDPacking.PositionCount
public import Kakeya.Tube.Basic
public import Kakeya.Tube.IntersectionVolume

/-!
# The `BadAgainstSet` predicate and its ED packing bound

A δ-tube is *bad against* a reference set `K` at density `c` when it meets `K`
in more than a `c`-fraction of its own volume.  This file collects the purely
geometric facts about that predicate:

* `BadAgainstSet` and its monotonicity `BadAgainstSet_mono_set` in the
  reference set;
* `badAgainstSet_count_le_of_ED_thinBox`, the volume-aware Córdoba/Wolff
  packing bound: among pairwise essentially-distinct δ-tubes, only
  `≲ M² / c^n` can be bad against a thin reference body of volume
  `≤ M · δ^(n-1)`;
* `notED_implies_BadAgainstSet` and
  `badAgainstSet_of_notED_subset_cthickening`, the bridge turning a failure of
  essential distinctness into a `BadAgainstSet` event.

Nothing here is probabilistic; the Chernoff layer built on top of
`BadAgainstSet` lives in `Kakeya/RandomTranslation/EssDistinct.lean`.
-/

@[expose] public section

open MeasureTheory Metric

namespace Kakeya

universe u

section BadAgainstSet

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- **The "bad" event for a tube `T'` against a reference set `K`**: the
intersection has volume at least a `c`-fraction of the volume of `T'`. -/
def BadAgainstSet {δ : NNReal} (T' : Tube δ E) (K : Set E) (c : ℝ) : Prop :=
  ENNReal.ofReal c * volume T'.carrier ≤ volume (T'.carrier ∩ K)

/-- Monotone in the reference set: enlarging `K` only makes `BadAgainstSet`
easier to trigger. -/
lemma BadAgainstSet_mono_set {δ : NNReal} (T' : Tube δ E) {K K' : Set E} {c : ℝ}
    (_hc : 0 ≤ c) (hKK' : K ⊆ K') (h : BadAgainstSet T' K c) :
    BadAgainstSet T' K' c := by
  unfold BadAgainstSet at *
  have hsub : T'.carrier ∩ K ⊆ T'.carrier ∩ K' :=
    Set.inter_subset_inter_right _ hKK'
  exact h.trans (measure_mono hsub)

/-! ### Volume-aware thin-box ED-packing bound

Direction × position packing with a dimension-only constant.

For `T₀' : Tube δ E ⊆ B(0, 7/2)` with a volume upper bound
`vol(cthickening (99·δ) T₀'.carrier) ≤ M · δ^(n-1)` (the "thin" condition),
the count of pairwise-ED δ-tubes that are bad against
`K_thick := cthickening (99·δ) T₀'.carrier` with density threshold `c` is bounded
by `⌈C_dim · M^2 / c^n⌉₊` where `n = Module.finrank ℝ E`.

This formalizes GWZ Lemma 3.8: "since the tubes of `𝕋` are essentially
distinct, we have `|𝕋[K]| ≲ (|K|/|T_δ|)²`."

**Proof scheme (convex-projection + Fubini).** Set
`S' := cthickening (100·δ) T₀'.carrier` (closed convex; volume
`≤ C₀ · M · δ^(n-1)`).

*Step 1 (direction count).* For each bad tube `T_i`, the axial parameter
set `A_i := {t : center_i(t) ∈ S'}` has Lebesgue measure `≥ c` (Fubini
on the radius-δ axial cylinder with `vol(T_i ∩ K_thick) ≥ c · vol(T_i)`),
so the projection length of `S'` onto the direction line satisfies
`L_{e_i}(S') ≥ c`. Take a maximal `δ`-separated subset of feasible
directions; double counting against a representative fibre of length
`≥ c` per direction, plus the sphere packing bound
`#{δ-separated unit vectors} ≤ C_n / δ^(n-1)`, gives
`N ≤ C₁ · M / c`.

*Step 2 (position count).* Fix a direction class. Fubini on the
convex `S'` gives `vol_{n-1}(π_{e^⊥} S') ≤ vol(S') / L_e(S')`. ED forces
the perp-projected axial points to be `δ`-separated in `ℝ^{n-1}`, so an
`(n-1)`-dim packing bound yields `|Bad_e| ≤ C₂ · M / c`.

*Step 3 (combine).* `Bad.card ≤ N · |Bad_e| ≤ C₁ C₂ · M² / c² ≤ C₁ C₂ · M² / c^n`
for `c ≤ 1`, `n ≥ 2`.

The auxiliary infrastructure lives in:
- `Kakeya/Tube/EDPacking/PerpSeparation.lean` — ED ⟹ perp-projected
  axial midpoints `c_slide·δ`-separated, packaged as
  `multiplicity_le_of_ED_directionClass`.
- `Kakeya/Tube/EDPacking/PositionCount.lean` — Fubini / indicator-sum
  double counting per direction cap.
- `Kakeya/Tube/EDPacking/BadCount.lean` — Cordoba-style L²
  combination of the two bounds.

The body is assembled from `badAgainstSet_card_le_M2_cN` (which takes the
position-count constants `c_slide, C_pc, δ_pc, hPC` as explicit parameters and
returns an existential `∃ C_dim`) plus an arithmetic upgrade `c^(n-1) ↦ c^n`
valid for `n ≥ 2` and `c ≤ 1`. -/

open Classical in
lemma badAgainstSet_count_le_of_ED_thinBox
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E] [ProperSpace E]
    (hn : 1 < Module.finrank ℝ E) :
    ∃ (C_dim : ℕ) (δ₀ : ℝ), 0 < C_dim ∧ 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ {ι : Type u} {δ : NNReal} (_hδ : 0 < δ) (_hδ_le : (δ : ℝ) ≤ δ₀) (s : Finset ι)
        (T : ι → Tube δ E) (T₀' : Tube δ E)
        (_hK_in_B2 : T₀'.carrier ⊆ Metric.closedBall (0 : E) (7 / 2))
        (M : ℝ) (_hM_pos : 0 < M)
        (_h_vol_ub :
          volume (Metric.cthickening (99 * (δ : ℝ)) T₀'.carrier)
            ≤ ENNReal.ofReal M *
              (δ : ENNReal) ^ (Module.finrank ℝ E - 1))
        (v : E),
        (s : Set ι).Pairwise
          (fun i j => IsEssentiallyDistinct (T i).carrier (T j).carrier) →
        (s.filter (fun i => BadAgainstSet ((T i).translate v)
            (Metric.cthickening (99 * (δ : ℝ)) T₀'.carrier)
            (((Tube.le_volume.c (Module.finrank ℝ E) : NNReal) : ℝ) /
              (2 * ((Tube.volume_le.C (Module.finrank ℝ E) : NNReal) : ℝ))))).card
          ≤ ⌈(C_dim : ℝ) * M ^ 2 /
              (((Tube.le_volume.c (Module.finrank ℝ E) : NNReal) : ℝ) /
                (2 * ((Tube.volume_le.C (Module.finrank ℝ E) : NNReal) : ℝ))) ^
                (Module.finrank ℝ E)⌉₊ := by
  -- The density threshold `c` is internally fixed to `c_vol/(2·M_vol)` so the
  -- Frostman consumer's bridge expression is definitionally identical.
  -- Destructure the position-count lemma once at the outer ι universe,
  -- so the constants `c_slide, C_pc, δ₀_pc, hPC` are uniform across all ι.
  obtain ⟨c_slide, C_pc, δ₀_pc, hc_slide_pos, hC_pc_pos, hδ₀_pc_pos, hδ₀_pc_le, hPC⟩ :=
    Kakeya.position_count_le_of_bad_directionClass (E := E) hn
  -- Apply `badAgainstSet_card_le_M2_cN` at outer scope to extract its concrete
  -- `C_dim` witness uniformly over ι.
  obtain ⟨C_dim_inner, hC_dim_inner_pos, h_M2_inner⟩ :=
    badAgainstSet_card_le_M2_cN (E := E) hn
      c_slide hc_slide_pos C_pc hC_pc_pos δ₀_pc hδ₀_pc_pos hδ₀_pc_le
      (by
        intro ι δ' hδ' hδ'_le s' T' hED' e he_unit h_dir_class K
          hK_meas hK_cpt M' hM'_pos hK_vol c hc hbad
        exact hPC hδ' hδ'_le s' T' hED' he_unit h_dir_class hK_meas hK_cpt
          hM'_pos hK_vol hc hbad)
  refine ⟨C_dim_inner,
    min 1 δ₀_pc,
    hC_dim_inner_pos,
    lt_min zero_lt_one hδ₀_pc_pos,
    min_le_left _ _, ?_⟩
  intro ι δ hδ hδ_le s T T₀' hK_in_B2 M hM_pos h_vol_ub v hED
  -- Volume-bound constants and the dim-only density threshold.
  set c_vol : ℝ := (Tube.le_volume.c (Module.finrank ℝ E) : ℝ) with hc_vol_def
  have hc_vol_pos : 0 < c_vol := by
    rw [hc_vol_def]; exact NNReal.coe_pos.mpr (Tube.le_volume.c_pos _)
  have hT_vol_lb_all : ∀ (δ' : NNReal), 0 < δ' → ∀ T : Tube δ' E,
      c_vol * (δ' : ℝ) ^ (Module.finrank ℝ E - 1) ≤ volume.real T.carrier := by
    intro δ' _ T
    have h := Tube.le_volume (δ := δ') T
    have hreal := ENNReal.toReal_mono T.isCompact.measure_lt_top.ne h
    rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.coe_toReal,
      ENNReal.coe_toReal] at hreal
    exact hreal
  set M_vol : ℝ := (Tube.volume_le.C (Module.finrank ℝ E) : ℝ) with hM_vol_def
  have hM_vol_pos : 0 < M_vol := by
    change (0 : ℝ) < ((Tube.volume_le.C (Module.finrank ℝ E) : NNReal) : ℝ)
    unfold Tube.volume_le.C
    push_cast
    positivity
  have hT_vol_ub_all : ∀ (δ' : NNReal), 0 < δ' → δ' ≤ 1 → ∀ T : Tube δ' E,
      volume.real T.carrier ≤ M_vol * (δ' : ℝ) ^ (Module.finrank ℝ E - 1) := by
    intro δ' hδ' hδ'1 T
    have h := Tube.volume_le hδ'1 T
    have hRHS_fin : (Tube.volume_le.C (Module.finrank ℝ E) : ENNReal) *
        (δ' : ENNReal) ^ (Module.finrank ℝ E - 1) ≠ ⊤ := by
      exact ENNReal.mul_ne_top ENNReal.coe_ne_top
        (ENNReal.pow_ne_top ENNReal.coe_ne_top)
    have hreal := ENNReal.toReal_mono hRHS_fin h
    rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.coe_toReal,
      ENNReal.coe_toReal] at hreal
    exact hreal
  set c_dim : ℝ := c_vol / (2 * M_vol) with hc_dim_def
  have hc_dim_pos : 0 < c_dim := div_pos hc_vol_pos (by positivity)
  -- `c_dim ≤ 1` from `c_vol ≤ M_vol`. The latter follows from
  -- `c_vol·δ^(n-1) ≤ vol(T) ≤ M_vol·δ^(n-1)` applied to a witness tube at
  -- `δ := 1/2`; the witness is built from a unit vector in the nontrivial
  -- finite-dim space `E` via `Tube.ofMidpointDirection`.
  have hc_dim_le_one : c_dim ≤ 1 := by
    obtain ⟨e, he⟩ : ∃ e : E, e ≠ 0 := exists_ne (0 : E)
    set u : E := ‖e‖⁻¹ • e with hu_def
    have hu_norm : ‖u‖ = 1 := by
      rw [hu_def, norm_smul, Real.norm_eq_abs,
          abs_of_pos (inv_pos.mpr (norm_pos_iff.mpr he))]
      field_simp
    have hδ0 : (0 : NNReal) < 1 / 2 := by
      rw [← NNReal.coe_lt_coe]; push_cast; norm_num
    let T_wit : Tube (1 / 2 : NNReal) E :=
      Tube.ofMidpointDirection (1 / 2 : NNReal) (0 : E) u hu_norm
    have hlb := hT_vol_lb_all (1 / 2 : NNReal) hδ0 T_wit
    have hub := hT_vol_ub_all (1 / 2 : NNReal) hδ0
      (by rw [← NNReal.coe_le_coe]; push_cast; norm_num) T_wit
    have h_half_coe : (((1 / 2 : NNReal) : ℝ)) = (1 / 2 : ℝ) := by push_cast; ring
    have hchain :
        c_vol * (((1 / 2 : NNReal) : ℝ)) ^ (Module.finrank ℝ E - 1)
          ≤ M_vol * (((1 / 2 : NNReal) : ℝ)) ^ (Module.finrank ℝ E - 1) :=
      hlb.trans hub
    have hpow_pos : (0 : ℝ) < (((1 / 2 : NNReal) : ℝ)) ^ (Module.finrank ℝ E - 1) :=
      pow_pos (by rw [h_half_coe]; norm_num) _
    have hcv_le_Mv : c_vol ≤ M_vol :=
      le_of_mul_le_mul_right hchain hpow_pos
    have h2Mv_pos : 0 < 2 * M_vol := by linarith
    change c_vol / (2 * M_vol) ≤ 1
    rw [div_le_iff₀ h2Mv_pos]
    linarith
  -- Apply the const · M² bound (ι-uniform, with the position count threaded).
  have h_d_le_one : (δ : ℝ) ≤ 1 := le_trans hδ_le (min_le_left _ _)
  have h_d_le_pc : (δ : ℝ) ≤ δ₀_pc := le_trans hδ_le (min_le_right _ _)
  have h_M2 := h_M2_inner (ι := ι) (δ := δ) hδ
    (1 : ℝ) zero_lt_one le_rfl h_d_le_one h_d_le_pc s T T₀'
    hK_in_B2 M hM_pos h_vol_ub v hED
  -- Upgrade const·M² → const·M²/c_dim^n via `c_dim ≤ 1` (`1 ≤ 1/c_dim^n`).
  have h_powN_pos : (0 : ℝ) < c_dim ^ Module.finrank ℝ E :=
    pow_pos hc_dim_pos _
  have h_powN_le_one : c_dim ^ Module.finrank ℝ E ≤ 1 :=
    pow_le_one₀ hc_dim_pos.le hc_dim_le_one
  have h_numer_nn : (0 : ℝ) ≤ (C_dim_inner : ℝ) * M ^ 2 := by
    have : 0 ≤ (C_dim_inner : ℝ) := by exact_mod_cast hC_dim_inner_pos.le
    positivity
  have h_upgrade :
      (C_dim_inner : ℝ) * M ^ 2
        ≤ (C_dim_inner : ℝ) * M ^ 2 / c_dim ^ Module.finrank ℝ E := by
    rw [le_div_iff₀ h_powN_pos]
    -- goal: x * c_dim^n ≤ x, where x = C_dim_inner · M² ≥ 0 and c_dim^n ≤ 1
    have h_step : (C_dim_inner : ℝ) * M ^ 2 * c_dim ^ Module.finrank ℝ E
        ≤ (C_dim_inner : ℝ) * M ^ 2 * 1 :=
      mul_le_mul_of_nonneg_left h_powN_le_one h_numer_nn
    linarith
  -- Convert filter form: BadAgainstSet ↔ unfolded inequality.
  have h_filter_eq :
      s.filter (fun i => BadAgainstSet ((T i).translate v)
          (Metric.cthickening (99 * (δ : ℝ)) T₀'.carrier) c_dim)
        = s.filter (fun i =>
            volume (((T i).translate v).carrier
                ∩ Metric.cthickening (99 * (δ : ℝ)) T₀'.toConvexSpaceBody.carrier)
              ≥ ENNReal.ofReal c_dim * volume ((T i).translate v).carrier) := by
    apply Finset.filter_congr
    intro i _
    rfl
  rw [h_filter_eq]
  -- Combine real-valued bounds, then convert to ⌈·⌉₊.
  have h_real := h_M2.trans h_upgrade
  exact_mod_cast h_real.trans (Nat.le_ceil _)

/-- Failure of ED implies `BadAgainstSet` at density `c_low / (2 * c_up)`.

Requires `c_low ≤ vol T_p` and `vol T' ≤ c_up`: callers use
`Tube.volume_lower_bound` / `Tube.volume_upper_bound` and substitute
`c_low * δ^(n-1)`, `c_up * δ^(n-1)`. -/
lemma notED_implies_BadAgainstSet
    {δ : NNReal} (_hδ : 0 < δ) (T' : Tube δ E) (T_p : Tube δ E)
    (c_low c_up : ℝ) (_hc_low_pos : 0 < c_low) (hc_up_pos : 0 < c_up)
    (hvol_low : ENNReal.ofReal c_low ≤ volume T_p.carrier)
    (hvol_up : volume T'.carrier ≤ ENNReal.ofReal c_up)
    (_h : ¬ IsEssentiallyDistinct T'.carrier T_p.carrier) :
    BadAgainstSet T' T_p.carrier (c_low / (2 * c_up)) := by
  unfold IsEssentiallyDistinct at _h
  rw [not_le] at _h
  unfold BadAgainstSet
  -- Tubes are compact ⇒ finite volume; the ENNReal inequality `_h` lifts
  -- to a real-valued strict inequality.
  have hT'_fin : volume T'.carrier ≠ ⊤ := T'.isCompact.measure_lt_top.ne
  have hT_p_fin : volume T_p.carrier ≠ ⊤ := T_p.isCompact.measure_lt_top.ne
  have hinter_fin : volume (T'.carrier ∩ T_p.carrier) ≠ ⊤ :=
    ne_top_of_le_ne_top hT'_fin (measure_mono Set.inter_subset_left)
  have hvol_low_real : c_low ≤ volume.real T_p.carrier := by
    have hreal := ENNReal.toReal_mono hT_p_fin hvol_low
    simpa [Measure.real, ENNReal.toReal_ofReal _hc_low_pos.le] using hreal
  have hvol_up_real : volume.real T'.carrier ≤ c_up := by
    have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hvol_up
    simpa [Measure.real, ENNReal.toReal_ofReal hc_up_pos.le] using hreal
  have hmax_fin : (1 / 2 : ENNReal) * max (volume T'.carrier) (volume T_p.carrier) ≠ ⊤ := by
    refine ENNReal.mul_ne_top (by simp) ?_
    cases le_total (volume T'.carrier) (volume T_p.carrier) with
    | inl h => simp [max_eq_right h, hT_p_fin]
    | inr h => simp [max_eq_left h, hT'_fin]
  have h_real : (1 / 2 : ℝ) * max (volume.real T'.carrier) (volume.real T_p.carrier)
      < volume.real (T'.carrier ∩ T_p.carrier) := by
    have hmono := (ENNReal.toReal_lt_toReal hmax_fin hinter_fin).mpr _h
    have hmax_eq :
        ((1 / 2 : ENNReal) * max (volume T'.carrier) (volume T_p.carrier)).toReal
          = (1 / 2 : ℝ) * max (volume.real T'.carrier) (volume.real T_p.carrier) := by
      rw [ENNReal.toReal_mul]
      congr 1
      · simp
      · cases le_total (volume T'.carrier) (volume T_p.carrier) with
        | inl h =>
          rw [max_eq_right h]
          have h' : volume.real T'.carrier ≤ volume.real T_p.carrier :=
            ENNReal.toReal_mono hT_p_fin h
          rw [max_eq_right h']
          rfl
        | inr h =>
          rw [max_eq_left h]
          have h' : volume.real T_p.carrier ≤ volume.real T'.carrier :=
            ENNReal.toReal_mono hT'_fin h
          rw [max_eq_left h']
          rfl
    rw [hmax_eq] at hmono
    exact hmono
  have hkey : (c_low / (2 * c_up)) * c_up = c_low / 2 := by field_simp
  have h1 : (c_low / (2 * c_up)) * volume.real T'.carrier
      ≤ (c_low / (2 * c_up)) * c_up :=
    mul_le_mul_of_nonneg_left hvol_up_real (by positivity)
  have h2 : (1/2 : ℝ) * volume.real T_p.carrier
      ≤ (1/2 : ℝ) * max (volume.real T'.carrier) (volume.real T_p.carrier) :=
    mul_le_mul_of_nonneg_left (le_max_right _ _) (by norm_num : (0 : ℝ) ≤ 1/2)
  have hgoal_real :
      (c_low / (2 * c_up)) * volume.real T'.carrier
        ≤ volume.real (T'.carrier ∩ T_p.carrier) := by
    linarith [hvol_low_real]
  have hratio_nn : 0 ≤ c_low / (2 * c_up) := by positivity
  have hlhs_fin :
      ENNReal.ofReal (c_low / (2 * c_up)) * volume T'.carrier ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hT'_fin
  refine (ENNReal.toReal_le_toReal hlhs_fin hinter_fin).mp ?_
  simpa [Measure.real, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hratio_nn] using hgoal_real

/-- If `T_p.carrier ⊆ K` (for instance `K = cthickening (99·δ) T₀'.carrier`) and
`¬ ED(T', T_p)`, then `T'` is `BadAgainstSet` for the reference set `K`.

This composes `notED_implies_BadAgainstSet` with `BadAgainstSet_mono_set`, and
is the "not ED ⟹ `T'` is bad against a thickened net member" bridge used in
`Kakeya/RandomTranslation/RandCF.lean`. -/
lemma badAgainstSet_of_notED_subset_cthickening
    {δ : NNReal} (hδ : 0 < δ) (T' : Tube δ E) (T_p : Tube δ E) (K : Set E)
    (c_low c_up : ℝ) (hc_low_pos : 0 < c_low) (hc_up_pos : 0 < c_up)
    (hvol_low : ENNReal.ofReal c_low ≤ volume T_p.carrier)
    (hvol_up : volume T'.carrier ≤ ENNReal.ofReal c_up)
    (hsub : T_p.carrier ⊆ K)
    (h : ¬ IsEssentiallyDistinct T'.carrier T_p.carrier) :
    BadAgainstSet T' K (c_low / (2 * c_up)) := by
  have hbad : BadAgainstSet T' T_p.carrier (c_low / (2 * c_up)) :=
    notED_implies_BadAgainstSet hδ T' T_p c_low c_up hc_low_pos hc_up_pos
      hvol_low hvol_up h
  have hc_nn : (0 : ℝ) ≤ c_low / (2 * c_up) := by positivity
  exact BadAgainstSet_mono_set T' hc_nn hsub hbad

end BadAgainstSet

end Kakeya
