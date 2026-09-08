/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Tube.EDPacking.AxialAngle
public import Kakeya.Mathlib.Analysis.ProjectivePacking

/-!
# Composite bound: `BadAgainstSet` count ≤ `C · M² / c²`

Cordoba-style L² double-counting argument on ED δ-tubes.
-/

@[expose] public section

open MeasureTheory Metric Set
open scoped InnerProductSpace RealInnerProductSpace

namespace Kakeya

noncomputable section
variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E] [ProperSpace E]

universe u

/-! ### Composite bound: `BadAgainstSet` count ≤ `C · M² / c²`

Cordoba-style L² double-counting argument on the ED δ-tubes. Combines:

- A maximal `c_slide·δ`-separated set `V` of representative directions
  among bad indices (extracted by `exists_maximal_separated_directions`);
  every bad tube's direction lies in some representative's `c_slide·δ`-cap.
- `position_count_le_of_bad_directionClass`
  applied per cap to bound `|Bad_e| ≤ C₂ · M / c`.
- The ED hypothesis `_hED` contributes the pairwise volume control
  `vol(Tᵢ ∩ Tⱼ) ≤ (1/2)·max(vol Tᵢ, vol Tⱼ)`, which lets the
  representative count `|V|` be controlled by Cordoba's `(|K|/|T_δ|)²`
  estimate, giving `|V| ≤ C₁ · M / c`.

Summing per-cap counts then gives `Bad.card ≤ |V| · max |Bad_e| ≤
C₁ C₂ · M² / c²`.

This is the direct numerator that
`Kakeya/Tube/EDPacking/BadAgainstSet.lean` consumes; the final
`c²` → `c^n` arithmetic happens at the consumer level (using
`c ≤ 1`, `n ≥ 2`, `pow_le_pow_of_le_one`). The blueprint restricts
to `n ≥ 2` (the `n = 1` case is excluded at the
`badAgainstSet_count_le_of_ED_thinBox` interface). -/

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E]
  [BorelSpace E] [ProperSpace E] in
/-- **Finset-level greedy maximal separated subset extraction.**

For a finite set `Bad` of indices and a "direction" map `f : ι → E` together
with a real `r > 0`, there exists a subset `V ⊆ Bad` such that:

* `V` is `r`-separated in projective direction-distance (using
  `min ‖f i - f j‖ ‖f i + f j‖`, matching the separation metric used by
  `position_count_le_of_bad_directionClass`);
* every `i ∈ Bad` satisfies the cap condition
  `min ‖f i - f j‖ ‖f i + f j‖ < r` for some `j ∈ V`, or `i = j` for some
  `j ∈ V` (i.e. is in the `r`-direction-cap around some representative).

Standard greedy maximal pick: take `V ⊆ Bad` of maximum cardinality among
`r`-separated subsets; by maximality every new `i ∈ Bad` would create a
violator unless it lies in some existing cap. -/
private lemma exists_maximal_separated_directions
    {ι : Type u} (Bad : Finset ι) (f : ι → E) {r : ℝ} (_hr_pos : 0 < r) :
    ∃ V : Finset ι, V ⊆ Bad ∧
      (∀ i ∈ V, ∀ j ∈ V, i ≠ j →
        r ≤ min ‖f i - f j‖ ‖f i + f j‖) ∧
      (∀ i ∈ Bad, ∃ j ∈ V,
        min ‖f i - f j‖ ‖f i + f j‖ < r ∨ i = j) := by
  classical
  set P : Finset ι → Prop :=
    fun V => V ⊆ Bad ∧
      (∀ i ∈ V, ∀ j ∈ V, i ≠ j →
        r ≤ min ‖f i - f j‖ ‖f i + f j‖) with hP_def
  have hP_empty : P (∅ : Finset ι) := by
    refine ⟨?_, ?_⟩
    · intro x hx; simp at hx
    · intro i hi; simp at hi
  have h_card_le : ∀ V : Finset ι, P V → V.card ≤ Bad.card :=
    fun V hV => Finset.card_le_card hV.1
  set Q : ℕ → Prop := fun k => ∃ V : Finset ι, P V ∧ V.card = k with hQ_def
  have hQ_dec : DecidablePred Q := Classical.decPred Q
  set M : ℕ := Bad.card with hM_def
  have hQ0 : Q 0 := ⟨∅, hP_empty, by simp⟩
  set kmax : ℕ := Nat.findGreatest Q M with hkmax_def
  have hkmax_le : kmax ≤ M := Nat.findGreatest_le M
  have hQ_kmax : Q kmax := Nat.findGreatest_spec (Nat.zero_le M) hQ0
  obtain ⟨V, hP_V, hV_card⟩ := hQ_kmax
  refine ⟨V, hP_V.1, hP_V.2, ?_⟩
  intro i hi_Bad
  classical
  by_cases hiV : i ∈ V
  · exact ⟨i, hiV, Or.inr rfl⟩
  by_contra h_no
  push Not at h_no
  let V' : Finset ι := insert i V
  have hV'_sub : V' ⊆ Bad := by
    intro x hx
    simp only [V', Finset.mem_insert] at hx
    rcases hx with rfl | hxV
    · exact hi_Bad
    · exact hP_V.1 hxV
  have hV'_sep : ∀ a ∈ V', ∀ b ∈ V', a ≠ b →
      r ≤ min ‖f a - f b‖ ‖f a + f b‖ := by
    intro a ha b hb hab
    simp only [V', Finset.mem_insert] at ha hb
    rcases ha with rfl | haV
    · rcases hb with rfl | hbV
      · exact (hab rfl).elim
      · exact (h_no b hbV).1
    · rcases hb with rfl | hbV
      · have hh := (h_no a haV).1
        have h1 : ‖f a - f b‖ = ‖f b - f a‖ := by rw [← norm_neg]; congr 1; abel
        have h2 : ‖f a + f b‖ = ‖f b + f a‖ := by rw [add_comm]
        rw [h1, h2]; exact hh
      · exact hP_V.2 a haV b hbV hab
  have hP_V' : P V' := ⟨hV'_sub, hV'_sep⟩
  have hV'_card : V'.card = kmax + 1 := by
    simp only [V', Finset.card_insert_of_notMem hiV, hV_card]
  have hQ_succ : Q (kmax + 1) := ⟨V', hP_V', hV'_card⟩
  have hV'_card_le : V'.card ≤ M := h_card_le V' hP_V'
  have h_succ_le_M : kmax + 1 ≤ M := by
    rw [← hV'_card]; exact hV'_card_le
  have h_succ_le_kmax : kmax + 1 ≤ Nat.findGreatest Q M :=
    Nat.le_findGreatest h_succ_le_M hQ_succ
  rw [← hkmax_def] at h_succ_le_kmax
  exact absurd h_succ_le_kmax (Nat.not_succ_le_self kmax)

/-- **Bad-tube count under ED + thin-box volume hypothesis: `≤ C · M²`.**

For pairwise-ED δ-tubes `T : ι → Tube δ E` indexed by `s : Finset ι`,
all bad against `K = cthickening (99·δ) T₀'.carrier` with the fixed
dimension-only density threshold
`c_dim := c_vol / (2 · M_vol)` (where `c_vol`, `M_vol` are the
`Tube.volume_lower_bound` / `Tube.volume_upper_bound` constants), and
with the thin-box volume bound `vol(K) ≤ M · δ^(n-1)`, the number
of bad tubes is at most `C · M²` for a dimension-only constant `C`.

**Why a fixed density `c_dim`.** This lemma's only consumer is
`badAgainstSet_count_le_of_ED_thinBox` in
`Kakeya/Tube/EDPacking/BadAgainstSet.lean`, which plugs `c = c_dim`
(matching the upstream `notED_implies_BadAgainstSet` bridge). With `c`
specialized to a fixed dimension constant, the angle bound
`sin∠(T_i, T₀'.direction) ≤ C·δ/c_dim = const·δ` collapses to a single
`δ`-cap of directions, and the `c^(-(n-1))` direction-count factor
absorbs into the dimension constant. The lemma reduces to a one-step
position count via `position_count_le_of_bad_directionClass`.

**Why `T₀' : Tube δ E`, not `ConvexBody E`.** The volume hypothesis
`vol(K) ≤ M·δ^(n-1)` alone does *not* force geometric thinness on `T₀'`.
A small ball `T₀' = B(0, δ)` satisfies the volume bound trivially but
allows `δ⁻²` bad tubes (in `n = 3`), breaking any constant bound.
Constraining `T₀'` to be a δ-tube enforces "length 1 × radius δ"
geometry that matches GWZ §9 line 768 / 830 (`K` is convex of
dimensions `k₁ ×... × k_{n-1} × 1`).

**Proof outline (single δ-cap).**
1. (`bad_axial_angle_le`) Each bad tube's direction makes
   angle `≤ C₃·δ/c_dim = const·δ` with `T₀'.direction`.
2. All bad tubes lie in a single direction cap of radius `const·δ`
   (single `c_slide·δ` cap after possibly subdividing by a dim const).
3. Apply `position_count_le_of_bad_directionClass` to this cap,
   giving `|Bad| ≤ C₂·M/c_dim = const'·M`.
4. Upgrade `const'·M ≤ const''·M²` via the M ≥ c_dim regime
   (otherwise `Bad = ∅` by volume incompatibility and the bound is
   trivial). -/
lemma badAgainstSet_card_le_M2_cN
    (_hn : 1 < Module.finrank ℝ E)
    -- PC constants threaded explicitly by the caller (uniform across ι).
    (c_slide : ℝ) (hc_slide_pos : 0 < c_slide)
    (C_pc : ℕ) (hC_pc_pos : 0 < C_pc)
    (δ_pc : ℝ) (_hδ_pc_pos : 0 < δ_pc) (_hδ_pc_le : δ_pc ≤ 1)
    (hPC : ∀ {ι : Type u} {δ' : NNReal} (_hδ' : 0 < δ') (_hδ'_le : (δ' : ℝ) ≤ δ_pc)
        (s' : Finset ι) (T' : ι → Tube δ' E)
        (_hED' : (s' : Set ι).Pairwise
            (fun i j => IsEssentiallyDistinct (T' i).carrier (T' j).carrier))
        {e : E} (_he_unit : ‖e‖ = 1)
        (_h_dir_class : ∀ i ∈ s',
            min ‖(T' i).direction - e‖ ‖(T' i).direction + e‖ ≤ c_slide * (δ' : ℝ))
        {K : Set E}
        (_hK_meas : MeasurableSet K) (_hK_cpt : IsCompact K)
        {M' : ℝ} (_hM'_pos : 0 < M')
        (_hK_vol : volume K ≤ ENNReal.ofReal M' *
          (δ' : ENNReal) ^ (Module.finrank ℝ E - 1))
        {c : ℝ} (_hc : 0 < c)
        (_hbad : ∀ i ∈ s',
            volume ((T' i).carrier ∩ K) ≥ ENNReal.ofReal c * volume (T' i).carrier),
        (s'.card : ℝ) ≤ (C_pc : ℝ) * M' / c) :
    ∃ (C_dim : ℕ), 0 < C_dim ∧
    ∀ {ι : Type u} {δ : NNReal} (_hδ : 0 < δ)
      (δ₀ : ℝ) (_hδ₀_pos : 0 < δ₀) (_hδ₀_le : δ₀ ≤ 1) (_hδ_le : (δ : ℝ) ≤ δ₀)
      (_hδ_le_pc : (δ : ℝ) ≤ δ_pc)
      (s : Finset ι)
      (T : ι → Tube δ E) (T₀' : Tube δ E)
      (_hK_in_B2 : T₀'.carrier ⊆ Metric.closedBall (0 : E) (7 / 2))
      (M : ℝ) (_hM_pos : 0 < M)
      (_h_vol_ub :
        volume (Metric.cthickening (99 * (δ : ℝ)) T₀'.carrier)
          ≤ ENNReal.ofReal M * (δ : ENNReal) ^ (Module.finrank ℝ E - 1))
      (v : E)
      (_hED : (s : Set ι).Pairwise
        (fun i j => IsEssentiallyDistinct (T i).carrier (T j).carrier)),
      ((s.filter (fun i =>
          volume (((T i).translate v).carrier ∩
              Metric.cthickening (99 * (δ : ℝ)) T₀'.carrier) ≥
            ENNReal.ofReal (((Tube.le_volume.c (Module.finrank ℝ E) : NNReal) : ℝ) /
              (2 * ((Tube.volume_le.C (Module.finrank ℝ E) : NNReal) : ℝ))) *
                volume ((T i).translate v).carrier)).card : ℝ) ≤
        (C_dim : ℝ) * M ^ 2 := by
  classical
  -- ===== Compute outer constants (depending only on E, _hn, c_slide, C_pc) =====
  set c_vol : ℝ := (Tube.le_volume.c (Module.finrank ℝ E) : ℝ) with hc_vol_def
  have hc_vol_pos : 0 < c_vol := by
    rw [hc_vol_def]; exact NNReal.coe_pos.mpr (Tube.le_volume.c_pos _)
  have hc_vol_bound : ∀ (δ : NNReal), 0 < δ → ∀ T : Tube δ E,
      c_vol * (δ : ℝ) ^ (Module.finrank ℝ E - 1) ≤ volume.real T.carrier := by
    intro δ _ T
    have h := Tube.le_volume (δ := δ) T
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
  have hM_vol_bound : ∀ (δ : NNReal), 0 < δ → δ ≤ 1 → ∀ T : Tube δ E,
      volume.real T.carrier ≤ M_vol * (δ : ℝ) ^ (Module.finrank ℝ E - 1) := by
    intro δ hδ hδ1 T
    have h := Tube.volume_le hδ1 T
    have hRHS_fin : (Tube.volume_le.C (Module.finrank ℝ E) : ENNReal) *
        (δ : ENNReal) ^ (Module.finrank ℝ E - 1) ≠ ⊤ := by
      exact ENNReal.mul_ne_top ENNReal.coe_ne_top
        (ENNReal.pow_ne_top ENNReal.coe_ne_top)
    have hreal := ENNReal.toReal_mono hRHS_fin h
    rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.coe_toReal,
      ENNReal.coe_toReal] at hreal
    exact hreal
  set c_dim : ℝ := c_vol / (2 * M_vol) with hc_dim_def
  have hc_dim_pos : 0 < c_dim := div_pos hc_vol_pos (by positivity)
  -- Angular constant (outer).
  obtain ⟨C_A, hC_A_pos, h_A⟩ := bad_axial_angle_le (E := E) _hn
  -- Cap-packing constant (outer).
  set C_cap : ℝ := projectiveCapPackingConstant E with hC_cap_def
  have hC_cap_pos : 0 < C_cap := by
    rw [hC_cap_def]
    exact projectiveCapPackingConstant_pos E
  -- Define K_natural = (C_cap * (C_A / (c_dim * c_slide))^n + C_cap) * C_pc
  set K_pack : ℝ :=
    C_cap * (C_A / (c_dim * c_slide)) ^ Module.finrank ℝ E + C_cap
    with hK_pack_def
  have hK_pack_pos : 0 < K_pack := by
    have h_pow : 0 ≤ (C_A / (c_dim * c_slide)) ^ Module.finrank ℝ E :=
      pow_nonneg (by positivity) _
    nlinarith [mul_nonneg hC_cap_pos.le h_pow]
  set K_natural : ℝ := K_pack * (C_pc : ℝ) with hK_natural_def
  have hK_natural_pos : 0 < K_natural :=
    mul_pos hK_pack_pos (by exact_mod_cast hC_pc_pos)
  -- Define C_dim as the concrete natural witness.
  set C_dim_real : ℝ := K_natural / (c_dim * (c_dim * c_vol)) with hC_dim_real_def
  have h_denom_pos : 0 < c_dim * (c_dim * c_vol) :=
    mul_pos hc_dim_pos (mul_pos hc_dim_pos hc_vol_pos)
  have hC_dim_real_pos : 0 < C_dim_real :=
    div_pos hK_natural_pos h_denom_pos
  set C_dim : ℕ := ⌈C_dim_real⌉₊ + 1 with hC_dim_def
  have hC_dim_pos : 0 < C_dim := by
    simp [hC_dim_def]
  refine ⟨C_dim, hC_dim_pos, ?_⟩
  -- ===== Inner ∀ block =====
  intro ι δ _hδ δ₀ _hδ₀_pos _hδ₀_le _hδ_le _hδ_le_pc s T T₀' _hK_in_B2
    M _hM_pos _h_vol_ub v _hED
  have _h_vol_ub_real :
      volume.real (Metric.cthickening (99 * (δ : ℝ)) T₀'.carrier)
        ≤ M * (δ : ℝ) ^ (Module.finrank ℝ E - 1) := by
    have hreal := ENNReal.toReal_mono
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (ENNReal.pow_ne_top ENNReal.coe_ne_top)) _h_vol_ub
    simpa [Measure.real, ENNReal.toReal_mul, ENNReal.toReal_pow,
      ENNReal.toReal_ofReal _hM_pos.le, ENNReal.coe_toReal] using hreal
  -- Folded bad-filter set.
  set Bad : Finset ι :=
    s.filter (fun i => volume (((T i).translate v).carrier
          ∩ Metric.cthickening (99 * (δ : ℝ)) T₀'.carrier)
        ≥ ENNReal.ofReal c_dim * volume ((T i).translate v).carrier) with hBad_def
  by_cases hBad_nonempty : Bad.Nonempty
  · -- Non-empty Bad branch.
    -- Step 1: derive `c_dim · c_vol ≤ M` from any one bad index.
    obtain ⟨i₀, hi₀_Bad⟩ := hBad_nonempty
    -- Real-valued positivity of `δ`.
    have _hδ_real : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast _hδ
    have hi₀_mem : i₀ ∈ s ∧
        volume (((T i₀).translate v).carrier
            ∩ Metric.cthickening (99 * (δ : ℝ)) T₀'.carrier)
          ≥ ENNReal.ofReal c_dim * volume ((T i₀).translate v).carrier := by
      rw [hBad_def, Finset.mem_filter] at hi₀_Bad; exact hi₀_Bad
    obtain ⟨_, hi₀_bad⟩ := hi₀_mem
    -- Tube volume lower bound for translated tube.
    have h_volT_lb : c_vol * (δ : ℝ) ^ (Module.finrank ℝ E - 1)
        ≤ volume.real ((T i₀).translate v).carrier :=
      hc_vol_bound δ _hδ ((T i₀).translate v)
    -- Set monotonicity for `vol(_ ∩ K) ≤ vol(K)`.
    have hK_cpt : IsCompact (Metric.cthickening (99 * (δ : ℝ)) T₀'.carrier) :=
      T₀'.isCompact.cthickening
    have hK_fin : volume (Metric.cthickening (99 * (δ : ℝ)) T₀'.carrier) ≠ ⊤ :=
      hK_cpt.measure_lt_top.ne
    have h_inter_le_K :
        volume.real (((T i₀).translate v).carrier
              ∩ Metric.cthickening (99 * (δ : ℝ)) T₀'.carrier)
          ≤ volume.real (Metric.cthickening (99 * (δ : ℝ)) T₀'.carrier) :=
      ENNReal.toReal_mono hK_fin
        (measure_mono (μ := (volume : Measure E)) Set.inter_subset_right)
    have h_inter_le : volume.real (((T i₀).translate v).carrier
            ∩ Metric.cthickening (99 * (δ : ℝ)) T₀'.carrier)
          ≤ M * (δ : ℝ) ^ (Module.finrank ℝ E - 1) :=
      le_trans h_inter_le_K _h_vol_ub_real
    have hi₀_bad_real :
        c_dim * volume.real ((T i₀).translate v).carrier ≤
          volume.real (((T i₀).translate v).carrier ∩
            Metric.cthickening (99 * (δ : ℝ)) T₀'.carrier) := by
      have hinter_fin :
          volume (((T i₀).translate v).carrier ∩
            Metric.cthickening (99 * (δ : ℝ)) T₀'.carrier) ≠ ⊤ :=
        ne_top_of_le_ne_top ((T i₀).translate v).isCompact.measure_lt_top.ne
          (measure_mono Set.inter_subset_left)
      have hreal := ENNReal.toReal_mono hinter_fin hi₀_bad
      simpa [Measure.real, ENNReal.toReal_mul,
        ENNReal.toReal_ofReal hc_dim_pos.le] using hreal
    have hδpow_pos : 0 < (δ : ℝ) ^ (Module.finrank ℝ E - 1) := pow_pos _hδ_real _
    -- Combine to get `c_dim * c_vol ≤ M`.
    have h_cdim_cvol_le_M : c_dim * c_vol ≤ M := by
      have h1 : c_dim * (c_vol * (δ : ℝ) ^ (Module.finrank ℝ E - 1))
            ≤ c_dim * volume.real ((T i₀).translate v).carrier :=
        mul_le_mul_of_nonneg_left h_volT_lb hc_dim_pos.le
      have h2 : c_dim * (c_vol * (δ : ℝ) ^ (Module.finrank ℝ E - 1))
            ≤ M * (δ : ℝ) ^ (Module.finrank ℝ E - 1) :=
        le_trans h1 (le_trans hi₀_bad_real h_inter_le)
      have h3 : (c_dim * c_vol) * (δ : ℝ) ^ (Module.finrank ℝ E - 1)
            ≤ M * (δ : ℝ) ^ (Module.finrank ℝ E - 1) := by linarith [h2]
      exact le_of_mul_le_mul_right (by linarith [h3]) hδpow_pos
    -- Step 2: cap-subdivision direction-count using outer PC constants.
    have h_card_le_KM_cdim : (Bad.card : ℝ) ≤ K_natural * M / c_dim := by
      -- Translate preserves direction.
      have h_trans_dir : ∀ i : ι, ((T i).translate v).direction = (T i).direction := by
        intro i
        change ((T i).translate v).y - ((T i).translate v).x = (T i).y - (T i).x
        simp [Tube.translate, Tube.vadd]
      have hδ_le_one_real : (δ : ℝ) ≤ 1 := le_trans _hδ_le _hδ₀_le
      have hδ_le_one : δ ≤ 1 := by exact_mod_cast hδ_le_one_real
      -- c_dim ≤ 1 (in fact ≤ 1/2). Uses c_vol ≤ M_vol.
      have hc_dim_le_one : c_dim ≤ 1 := by
        rw [hc_dim_def]
        have h_ub : volume.real ((T i₀).translate v).carrier
            ≤ M_vol * (δ : ℝ) ^ (Module.finrank ℝ E - 1) := by
          exact hM_vol_bound δ _hδ hδ_le_one ((T i₀).translate v)
        have h_c_le_M : c_vol * (δ : ℝ) ^ (Module.finrank ℝ E - 1)
            ≤ M_vol * (δ : ℝ) ^ (Module.finrank ℝ E - 1) := h_volT_lb.trans h_ub
        have h_c_le : c_vol ≤ M_vol :=
          le_of_mul_le_mul_right (by linarith) hδpow_pos
        rw [div_le_one (by positivity)]
        linarith
      -- For each i in Bad, get angular bound w.r.t. T₀'.direction.
      have h_dir_angle : ∀ i ∈ Bad,
          min ‖(T i).direction - T₀'.direction‖ ‖(T i).direction + T₀'.direction‖
            ≤ C_A * (δ : ℝ) / c_dim := by
        intro i hi
        rw [hBad_def, Finset.mem_filter] at hi
        obtain ⟨_, hi_bad⟩ := hi
        have h_dir_eq : ((T i).translate v).direction = (T i).direction := h_trans_dir i
        have := h_A (δ := δ) _hδ hδ_le_one ((T i).translate v) T₀'
          (c := c_dim) hc_dim_pos hc_dim_le_one hi_bad
        rw [h_dir_eq] at this
        exact this
      -- Step A: extract maximal c_slide·δ-separated subset of Bad's directions.
      have hr_pos : (0 : ℝ) < c_slide * (δ : ℝ) := mul_pos hc_slide_pos _hδ_real
      obtain ⟨V, hV_sub, hV_sep, hV_cover⟩ :=
        exists_maximal_separated_directions Bad
          (fun i => (T i).direction) hr_pos
      -- Step B: bound |V| by cap-packing.
      -- The direction map V → E is injective on V (different elements yield
      -- different directions, since the separation hypothesis with d_i = d_j
      -- would give 0 ≥ c_slide·δ > 0).
      have h_dir_inj : Set.InjOn (fun i => (T i).direction) (V : Set ι) := by
        intro i hi j hj hij
        by_contra hne
        have hsep_ij := hV_sep i hi j hj hne
        simp only at hij
        have h1 : ‖(T i).direction - (T j).direction‖ = 0 := by
          rw [hij]; simp
        have h2 : min ‖(T i).direction - (T j).direction‖
            ‖(T i).direction + (T j).direction‖
            ≤ ‖(T i).direction - (T j).direction‖ := min_le_left _ _
        have h3 : min ‖(T i).direction - (T j).direction‖
            ‖(T i).direction + (T j).direction‖ ≤ 0 := by
          calc min ‖(T i).direction - (T j).direction‖
                ‖(T i).direction + (T j).direction‖
              ≤ ‖(T i).direction - (T j).direction‖ := h2
            _ = 0 := h1
        have h4 : c_slide * (δ : ℝ) ≤ 0 := le_trans hsep_ij h3
        have h5 : 0 < c_slide * (δ : ℝ) := mul_pos hc_slide_pos _hδ_real
        linarith
      -- For cap packing: the directions are unit vectors and lie within
      -- a (C_A * (δ : ℝ) / c_dim)-cap of T₀'.direction.
      have h_dir_unit_pf : ∀ T : Tube δ E, ‖T.direction‖ = 1 := by
        intro T
        have := T.dist_eq_one
        rwa [dist_eq_norm, ← neg_sub, norm_neg] at this
      have h_dir_unit : ∀ i : ι, ‖(T i).direction‖ = 1 := fun i => h_dir_unit_pf (T i)
      have h_T₀'_unit : ‖T₀'.direction‖ = 1 := h_dir_unit_pf T₀'
      -- V.image (T ·).direction: cardinality equals V.card by injectivity.
      let V_E : Finset E := V.image (fun i => (T i).direction)
      have hV_E_card : V_E.card = V.card := by
        exact Finset.card_image_of_injOn h_dir_inj
      have hV_E_unit : ∀ v ∈ V_E, ‖v‖ = 1 := by
        intro x hx
        simp only [V_E, Finset.mem_image] at hx
        obtain ⟨i, _, rfl⟩ := hx
        exact h_dir_unit i
      have hV_E_sep : ∀ x ∈ V_E, ∀ y ∈ V_E, x ≠ y →
          c_slide * (δ : ℝ) ≤ min ‖x - y‖ ‖x + y‖ := by
        intro x hx y hy hxy
        simp only [V_E, Finset.mem_image] at hx hy
        obtain ⟨i, hi, rfl⟩ := hx
        obtain ⟨j, hj, rfl⟩ := hy
        have hij : i ≠ j := fun h => hxy (by rw [h])
        exact hV_sep i hi j hj hij
      have hV_E_cap : ∀ x ∈ V_E,
          min ‖x - T₀'.direction‖ ‖x + T₀'.direction‖ ≤ C_A * (δ : ℝ) / c_dim := by
        intro x hx
        simp only [V_E, Finset.mem_image] at hx
        obtain ⟨i, hi, rfl⟩ := hx
        exact h_dir_angle i (hV_sub hi)
      -- Apply the projective cap-packing bound.
      have hC_A_delta_pos : 0 < C_A * (δ : ℝ) / c_dim :=
        div_pos (mul_pos hC_A_pos _hδ_real) hc_dim_pos
      have hV_E_bound : (V_E.card : ℝ) ≤
          C_cap * ((C_A * (δ : ℝ) / c_dim) / (c_slide * (δ : ℝ))) ^ Module.finrank ℝ E + C_cap :=
        card_le_of_projective_separated_in_cap h_T₀'_unit hV_E_unit
          hr_pos hC_A_delta_pos hV_E_sep hV_E_cap
      -- Simplify (C_A * (δ : ℝ) / c_dim) / (c_slide * (δ : ℝ)) = C_A / (c_dim * c_slide).
      have h_ratio : (C_A * (δ : ℝ) / c_dim) / (c_slide * (δ : ℝ)) = C_A / (c_dim * c_slide) := by
        have hδne : (δ : ℝ) ≠ 0 := ne_of_gt _hδ_real
        have hc_dim_ne : c_dim ≠ 0 := ne_of_gt hc_dim_pos
        have hc_slide_ne : c_slide ≠ 0 := ne_of_gt hc_slide_pos
        field_simp
      rw [h_ratio] at hV_E_bound
      -- Step C: for each j ∈ V, define Bad_j := { i ∈ Bad | direction is in (c_slide·δ)-cap }.
      -- Then by cover, Bad = ⋃ j ∈ V, Bad_j.
      let Bad_j : ι → Finset ι := fun j =>
        (Bad.filter (fun i =>
          min ‖(T i).direction - (T j).direction‖
            ‖(T i).direction + (T j).direction‖ < c_slide * (δ : ℝ) ∨ i = j))
      -- For each j ∈ V, apply position count to Bad_j.
      -- We need s.card-style hypothesis. Bad_j is a Finset of ι.
      -- Hypotheses:
      --  (a) ED holds on Bad_j (since Bad_j ⊆ s).
      --  (b) Direction class: each i ∈ Bad_j has
      --      min‖d_i - d_j‖ ‖d_i + d_j‖ ≤ c_slide·δ (from definition).
      --  (c) K = cthickening(99δ, T₀'.carrier) measurable+compact.
      --  (d) vol(K) ≤ M · δ^(n-1) (from _h_vol_ub).
      --  (e) bad-against: c_dim · vol(T_i) ≤ vol(T_i ∩ K) for i ∈ Bad.
      -- Use ((T i).translate v) as the family.
      have hPC_per_cap : ∀ j ∈ V, (Bad_j j).card ≤ C_pc * M / c_dim := by
        intro j hj_V
        -- Build the needed hypotheses for hPC.
        have h_Bad_j_sub_s : Bad_j j ⊆ s := by
          intro i hi
          simp only [Bad_j, Finset.mem_filter] at hi
          rw [hBad_def, Finset.mem_filter] at hi
          exact hi.1.1
        have h_ED_Bad_j : (↑(Bad_j j) : Set ι).Pairwise
            (fun i k => IsEssentiallyDistinct ((T i).translate v).carrier
              ((T k).translate v).carrier) := by
          intro i hi k hk hik
          have hi_s : i ∈ s := h_Bad_j_sub_s hi
          have hk_s : k ∈ s := h_Bad_j_sub_s hk
          have h_ED_ik := _hED hi_s hk_s hik
          -- Translate preserves ED via image equals preimage under -v.
          have him_pre : ∀ A : Set E,
              (fun x : E => v + x) '' A = (fun x : E => -v + x) ⁻¹' A := by
            intro A
            ext y
            constructor
            · rintro ⟨x, hx, rfl⟩
              change -v + (v + x) ∈ A
              simpa using hx
            · intro hy
              refine ⟨-v + y, hy, ?_⟩
              simp
          have hi_eq : ((T i).translate v).carrier =
              (fun x => -v + x) ⁻¹' (T i).carrier := by
            change (v + ·) '' (T i).carrier = _
            exact him_pre (T i).carrier
          have hk_eq : ((T k).translate v).carrier =
              (fun x => -v + x) ⁻¹' (T k).carrier := by
            change (v + ·) '' (T k).carrier = _
            exact him_pre (T k).carrier
          have key : ∀ A : Set E,
              volume ((fun x => -v + x) ⁻¹' A) = volume A := by
            intro A
            rw [MeasureTheory.measure_preimage_add]
          unfold IsEssentiallyDistinct at h_ED_ik ⊢
          rw [hi_eq, hk_eq, ← Set.preimage_inter, key, key, key]
          exact h_ED_ik
        -- Direction class for Bad_j.
        have h_dir_class : ∀ i ∈ Bad_j j,
            min ‖((T i).translate v).direction - (T j).direction‖
                ‖((T i).translate v).direction + (T j).direction‖ ≤ c_slide * (δ : ℝ) := by
          intro i hi
          simp only [Bad_j, Finset.mem_filter] at hi
          obtain ⟨_, hcap⟩ := hi
          rw [h_trans_dir]
          rcases hcap with hlt | heq
          · linarith
          · rw [heq]
            have h0 : min ‖(T j).direction - (T j).direction‖
                ‖(T j).direction + (T j).direction‖ = 0 := by
              have hsub : ‖(T j).direction - (T j).direction‖ = 0 := by simp
              rw [hsub]
              exact min_eq_left (norm_nonneg _)
            rw [h0]
            exact (mul_pos hc_slide_pos _hδ_real).le
        -- K = cthickening (99δ) T₀'.carrier.
        have hK_meas : MeasurableSet (Metric.cthickening (99 * (δ : ℝ)) T₀'.carrier) :=
          Metric.isClosed_cthickening.measurableSet
        have hK_cpt : IsCompact (Metric.cthickening (99 * (δ : ℝ)) T₀'.carrier) :=
          T₀'.isCompact.cthickening
        -- Bad condition on Bad_j (lifted to translate).
        have h_bad_filter : ∀ i ∈ Bad_j j,
            volume (((T i).translate v).carrier ∩
                Metric.cthickening (99 * (δ : ℝ)) T₀'.carrier)
              ≥ ENNReal.ofReal c_dim * volume ((T i).translate v).carrier := by
          intro i hi
          simp only [Bad_j, Finset.mem_filter] at hi
          obtain ⟨hi_Bad, _⟩ := hi
          rw [hBad_def, Finset.mem_filter] at hi_Bad
          exact hi_Bad.2
        -- Apply hPC (outer-supplied, with `δ ≤ δ_pc` from `_hδ_le_pc`).
        have h_call := hPC (δ' := δ) _hδ _hδ_le_pc (Bad_j j)
          (fun i => (T i).translate v) h_ED_Bad_j
          (e := (T j).direction) (h_dir_unit j) h_dir_class
          (K := Metric.cthickening (99 * (δ : ℝ)) T₀'.carrier)
          hK_meas hK_cpt _hM_pos _h_vol_ub hc_dim_pos h_bad_filter
        exact h_call
      -- Step D: cover Bad ⊆ ⋃ j ∈ V, Bad_j.
      have h_Bad_cover : Bad ⊆ V.biUnion Bad_j := by
        intro i hi_Bad
        obtain ⟨j, hj_V, hj_cap⟩ := hV_cover i hi_Bad
        simp only [Finset.mem_biUnion]
        refine ⟨j, hj_V, ?_⟩
        simp only [Bad_j, Finset.mem_filter]
        exact ⟨hi_Bad, hj_cap⟩
      -- Bound Bad.card by sum of (Bad_j j).card.
      have h_Bad_card_le_sum :
          (Bad.card : ℝ) ≤ ∑ j ∈ V, ((Bad_j j).card : ℝ) := by
        have h1 : Bad.card ≤ (V.biUnion Bad_j).card :=
          Finset.card_le_card h_Bad_cover
        have h2 : (V.biUnion Bad_j).card ≤ ∑ j ∈ V, (Bad_j j).card :=
          Finset.card_biUnion_le
        have : (Bad.card : ℝ) ≤ ((∑ j ∈ V, (Bad_j j).card : ℕ) : ℝ) := by
          exact_mod_cast (Nat.le_trans h1 h2)
        rw [Nat.cast_sum] at this
        exact this
      -- Total bound: Bad.card ≤ |V| * (C_pc * M / c_dim).
      have h_sum_le : ∑ j ∈ V, ((Bad_j j).card : ℝ) ≤
          (V.card : ℝ) * (C_pc * M / c_dim) := by
        calc ∑ j ∈ V, ((Bad_j j).card : ℝ)
            ≤ ∑ j ∈ V, (C_pc * M / c_dim) :=
              Finset.sum_le_sum (fun j hj => hPC_per_cap j hj)
          _ = (V.card : ℝ) * (C_pc * M / c_dim) := by
              rw [Finset.sum_const, nsmul_eq_mul]
      -- Establish `Bad.card ≤ K_natural * M / c_dim` via cap-packing × position count.
      calc (Bad.card : ℝ)
          ≤ ∑ j ∈ V, ((Bad_j j).card : ℝ) := h_Bad_card_le_sum
        _ ≤ (V.card : ℝ) * ((C_pc : ℝ) * M / c_dim) := h_sum_le
        _ = (V_E.card : ℝ) * ((C_pc : ℝ) * M / c_dim) := by rw [hV_E_card]
        _ ≤ K_pack * ((C_pc : ℝ) * M / c_dim) := by
            apply mul_le_mul_of_nonneg_right hV_E_bound
            have hM_div_pos : 0 < M / c_dim := div_pos _hM_pos hc_dim_pos
            have : 0 ≤ (C_pc : ℝ) := by exact_mod_cast hC_pc_pos.le
            positivity
        _ = K_natural * M / c_dim := by rw [hK_natural_def]; ring
    -- Step 3: convert `Bad.card ≤ K_natural * M / c_dim` to `Bad.card ≤ C_dim * M²`.
    have hM_pos : 0 < M := _hM_pos
    have h_cv_pos : 0 < c_dim * c_vol := mul_pos hc_dim_pos hc_vol_pos
    -- `M / c_dim ≤ M² / (c_dim * (c_dim * c_vol))` using `c_dim * c_vol ≤ M`.
    have h_div_le_sq : M / c_dim ≤ M ^ 2 / (c_dim * (c_dim * c_vol)) := by
      rw [div_le_div_iff₀ hc_dim_pos (mul_pos hc_dim_pos h_cv_pos)]
      have hM_cdim_nn : 0 ≤ M * c_dim := mul_nonneg hM_pos.le hc_dim_pos.le
      calc M * (c_dim * (c_dim * c_vol))
          = (c_dim * c_vol) * (M * c_dim) := by ring
        _ ≤ M * (M * c_dim) := mul_le_mul_of_nonneg_right h_cdim_cvol_le_M hM_cdim_nn
        _ = M ^ 2 * c_dim := by ring
    -- Combine: Bad.card ≤ K_natural * M² / (c_dim * (c_dim * c_vol)) = C_dim_real * M².
    have h_card_le_sq : (Bad.card : ℝ) ≤ C_dim_real * M ^ 2 := by
      have hK_nat_nn : 0 ≤ K_natural := hK_natural_pos.le
      calc (Bad.card : ℝ)
          ≤ K_natural * M / c_dim := h_card_le_KM_cdim
        _ = K_natural * (M / c_dim) := by ring
        _ ≤ K_natural * (M ^ 2 / (c_dim * (c_dim * c_vol))) :=
            mul_le_mul_of_nonneg_left h_div_le_sq hK_nat_nn
        _ = (K_natural / (c_dim * (c_dim * c_vol))) * M ^ 2 := by ring
        _ = C_dim_real * M ^ 2 := by rw [hC_dim_real_def]
    -- Finally absorb `C_dim_real ≤ C_dim` via `⌈·⌉₊` upgrade.
    have h_real_le : C_dim_real ≤ (C_dim : ℝ) := by
      have h1 : C_dim_real ≤ (⌈C_dim_real⌉₊ : ℝ) := Nat.le_ceil _
      have h2 : (⌈C_dim_real⌉₊ : ℝ) ≤ ((⌈C_dim_real⌉₊ + 1 : ℕ) : ℝ) := by
        push_cast; linarith
      rw [hC_dim_def]; exact h1.trans h2
    have hM2_nn : 0 ≤ M ^ 2 := sq_nonneg _
    calc (Bad.card : ℝ)
        ≤ C_dim_real * M ^ 2 := h_card_le_sq
      _ ≤ (C_dim : ℝ) * M ^ 2 := mul_le_mul_of_nonneg_right h_real_le hM2_nn
  · -- Empty Bad: `Bad.card = 0`, bound is trivial.
    rw [Finset.not_nonempty_iff_eq_empty] at hBad_nonempty
    rw [hBad_nonempty, Finset.card_empty, Nat.cast_zero]
    have hM2_nn : 0 ≤ M ^ 2 := sq_nonneg _
    positivity

end -- close noncomputable section
end Kakeya
