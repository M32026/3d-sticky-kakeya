/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.RandomTranslation.EDChernoffNet
public import Kakeya.RandomTranslation.RigidMED

/-!
# A single tuple of rigid motions that is ED-good against every test tube

`Kakeya.edBadCount_chernoff_tail` bounds, for one test tube, the probability that the total bad
count of `J` independent rigid copies exceeds a threshold `S`. This file performs the union bound
over the whole test-tube net and extracts a **single** tuple of rigid motions that works for all
test tubes simultaneously.

## The arithmetic, with nothing hidden

The net is `Kakeya.exists_thin_tube_net`, whose cardinality is bounded by the named dimensional
quantities

`NetT.card ≤ netGeomConstantC E * δ^(-netGeomConstantM E)`.

The Chernoff bound contributes `exp (10e - S/M)` per net member with `M` dimensional
(`edBadCount_chernoff_tail`). Choosing

`S = rigidMED (M · A) δ`,  `A = 10e + |log (10 · netGeomConstantC E)| + 1 + netGeomConstantM E`,

gives `S/M ≥ A · (1 + log (1/δ)) ≥ 10e + log (10 · netGeomConstantC E) + 1
+ netGeomConstantM E · log (1/δ)`, hence

`NetT.card · exp (10e - S/M) ≤ (netGeomConstantC E · δ^(-netGeomConstantM E))
    · (10 · netGeomConstantC E)⁻¹ · δ^(netGeomConstantM E) · e⁻¹ = e⁻¹/10 < 1/10`.

So the failure probability is below `1/10` and the good event has probability at least `9/10 > 0`.
The threshold `S` is `O(log (1/δ))` and, crucially, is free of the Frostman constant.
-/

@[expose] public section

open MeasureTheory Metric Set Filter Topology

namespace Kakeya

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The dimensional constant calibrating the Chernoff threshold against the polynomial size of the
test-tube net. The absolute value makes it unconditionally large enough regardless of the sign of
`log (10 · netGeomConstantC E)`. -/
def edNetCalibration (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] : ℝ :=
  10 * Real.exp 1 + |Real.log (10 * netGeomConstantC E)| + 1 + netGeomConstantM E

theorem edNetCalibration_pos [Nontrivial E] : 0 < edNetCalibration E := by
  unfold edNetCalibration
  have hM : 0 ≤ netGeomConstantM E := (netGeomConstantM_pos E).le
  have hE : 0 < Real.exp 1 := Real.exp_pos 1
  have hlog : 0 ≤ |Real.log (10 * netGeomConstantC E)| := abs_nonneg _
  nlinarith

/-- **The union-bound arithmetic, fully explicit.** With the threshold `rigidMED (M · A) δ` the
product of the net cardinality bound and the per-tube Chernoff probability is below `1/10`. -/
theorem net_union_bound_lt [Nontrivial E] {M A : ℝ} (hM : 0 < M)
    (hA : edNetCalibration E ≤ A)
    {δ : NNReal} (hδ : 0 < δ) (hδ1 : (δ : ℝ) ≤ 1) :
    (netGeomConstantC E * (δ : ℝ) ^ (-(netGeomConstantM E)))
        * Real.exp (10 * Real.exp 1 - ((rigidMED (M * A) δ : ℕ) : ℝ) / M)
      < 1 / 10 := by
  set C : ℝ := netGeomConstantC E
  set MM : ℝ := netGeomConstantM E
  set e : ℝ := Real.exp 1
  let l : ℝ := Real.log (1 / (δ : ℝ))
  let L : ℝ := 1 + l
  let P : ℝ := M * A * L
  set S : ℝ := ((rigidMED (M * A) δ : ℕ) : ℝ)
  have hδR : 0 < (δ : ℝ) := NNReal.coe_pos.mpr hδ
  have hδnn : 0 ≤ (δ : ℝ) := NNReal.coe_nonneg δ
  have hone : (1 : ℝ) ≤ 1 / (δ : ℝ) := one_le_one_div hδR hδ1
  have hlog : 0 ≤ l := by
    dsimp [l]
    exact Real.log_nonneg hone
  have hCpos : 0 < C := by
    dsimp [C]
    exact netGeomConstantC_pos E
  have hMpos : 0 < MM := by
    dsimp [MM]
    exact netGeomConstantM_pos E
  have heposs : 0 < e := by
    dsimp [e]
    exact Real.exp_pos 1
  have hMMnn : 0 ≤ MM := hMpos.le
  have hCNn : 0 ≤ C := hCpos.le
  have hCabsnn : 0 ≤ |Real.log (10 * C)| := abs_nonneg _
  -- Step 2: bounds on A from hA
  have hA' : 10 * e + |Real.log (10 * C)| + 1 + MM ≤ A := by
    rw [edNetCalibration] at hA
    simpa [C] using hA
  have hlog_le_abs : Real.log (10 * C) ≤ |Real.log (10 * C)| := le_abs_self _
  have hA_ge_M : MM ≤ A := by
    nlinarith [hA', heposs, hCabsnn, hMMnn]
  have hA_ge_base : 10 * e + Real.log (10 * C) + 1 ≤ A := by
    nlinarith [hA', hlog_le_abs, hMMnn]
  -- Step 3: S/M ≥ A·L
  have hS_eq : S = ((⌈P⌉₊ : ℕ) : ℝ) + 1 := by
    have hPa : (M * A) * (1 + Real.log (1 / (δ : ℝ))) = P := by
      dsimp [P, L]
    dsimp [S]
    rw [rigidMED]
    rw [← hPa]
    norm_cast
  have hPceil : P ≤ ((⌈P⌉₊ : ℕ) : ℝ) := Nat.le_ceil P
  have hS_ge : P ≤ S := by
    rw [hS_eq]
    nlinarith [hPceil]
  have hSM : A * L ≤ S / M := by
    rw [le_div_iff₀ hM]
    calc
      A * L * M = M * A * L := by ring
      _ = P := rfl
      _ ≤ S := hS_ge
  -- Step 4: lower bound on A·L
  have hAL_prod : A * L = A + A * l := by
    dsimp [L]
    ring
  have hA_log : MM * l ≤ A * l := mul_le_mul_of_nonneg_right hA_ge_M hlog
  have hB4 : 10 * e + Real.log (10 * C) + 1 + MM * l ≤ A * L := by
    rw [hAL_prod]
    nlinarith [hA_ge_base, hA_log]
  have hST : 10 * e - S / M ≤ -(Real.log (10 * C) + 1 + MM * l) := by
    nlinarith [hSM, hB4]
  -- Step 5: bound the exponential factor
  have hExpLe :
      Real.exp (10 * e - S / M) ≤
        Real.exp (-(Real.log (10 * C) + 1 + MM * l)) :=
    Real.exp_le_exp.mpr hST
  have hC10pos : 0 < 10 * C := by positivity
  have hC10ne : 10 * C ≠ 0 := ne_of_gt hC10pos
  have hCne : C ≠ 0 := ne_of_gt hCpos
  have hE1 : Real.exp (-(Real.log (10 * C))) = (10 * C)⁻¹ := by
    rw [Real.exp_neg (Real.log (10 * C)), Real.exp_log hC10pos]
  have hE2 : Real.exp (-1) = e⁻¹ := by
    dsimp [e]
    exact Real.exp_neg 1
  have hl_inv : l = -(Real.log (δ : ℝ)) := by
    dsimp [l]
    rw [one_div] at ⊢
    exact Real.log_inv (δ : ℝ)
  have hArg3 : -(MM * l) = Real.log (δ : ℝ) * MM := by
    rw [hl_inv]
    ring
  have hE3 : Real.exp (-(MM * l)) = (δ : ℝ) ^ MM := by
    rw [hArg3]
    rw [← Real.rpow_def_of_pos hδR MM]
  have hArgT : -(Real.log (10 * C) + 1 + MM * l) =
      -(Real.log (10 * C)) + (-1) + (-(MM * l)) := by ring
  have hExpT :
      Real.exp (-(Real.log (10 * C) + 1 + MM * l)) =
        (10 * C)⁻¹ * e⁻¹ * (δ : ℝ) ^ MM := by
    rw [hArgT]
    calc
      Real.exp (-(Real.log (10 * C)) + (-1) + (-(MM * l)))
          = Real.exp (-(Real.log (10 * C))) * Real.exp (-1) * Real.exp (-(MM * l)) := by
            rw [Real.exp_add]
            rw [Real.exp_add]
      _ = (10 * C)⁻¹ * e⁻¹ * (δ : ℝ) ^ MM := by rw [hE1, hE2, hE3]
  -- Step 6: multiply and cancel
  have hCt : 0 ≤ C * (δ : ℝ) ^ (-MM) :=
    mul_nonneg hCNn (Real.rpow_nonneg hδnn _)
  have hδE : (δ : ℝ) ^ (-MM) * (δ : ℝ) ^ MM = 1 := by
    rw [← Real.rpow_add hδR (-MM) MM]
    have hz : (-MM) + MM = (0 : ℝ) := by ring
    rw [hz]
    simp
  have hCinv : C * (10 * C)⁻¹ = (1 / 10 : ℝ) := by
    field_simp [hCne, hC10ne]
  have hProd :
      (C * (δ : ℝ) ^ (-MM)) * ((10 * C)⁻¹ * e⁻¹ * (δ : ℝ) ^ MM) = (1 / 10) * e⁻¹ := by
    calc
      (C * (δ : ℝ) ^ (-MM)) * ((10 * C)⁻¹ * e⁻¹ * (δ : ℝ) ^ MM)
          = (C * (10 * C)⁻¹) * ((δ : ℝ) ^ (-MM) * (δ : ℝ) ^ MM) * e⁻¹ := by ring
      _ = (1 / 10) * 1 * e⁻¹ := by rw [hCinv, hδE]
      _ = (1 / 10) * e⁻¹ := by ring
  have hone_e : (1 : ℝ) < e := by
    dsimp [e]
    exact (Real.one_lt_exp_iff).mpr (by norm_num)
  have hEinv : e⁻¹ < 1 := by
    dsimp [e]
    rw [← Real.exp_neg (1 : ℝ)]
    calc
      Real.exp (-(1 : ℝ)) < Real.exp (0 : ℝ) :=
        (Real.exp_lt_exp).mpr (by norm_num : (-(1 : ℝ)) < (0 : ℝ))
      _ = 1 := Real.exp_zero
  have hfinite : (1 / 10) * e⁻¹ < 1 / 10 := by
    have hpos : (0 : ℝ) < 1 / 10 := by norm_num
    calc
      (1 / 10) * e⁻¹ < (1 / 10) * 1 := mul_lt_mul_of_pos_left hEinv hpos
      _ = 1 / 10 := by norm_num
  have hMain : C * (δ : ℝ) ^ (-MM) * Real.exp (10 * e - S / M) ≤ (1 / 10) * e⁻¹ := by
    calc
      C * (δ : ℝ) ^ (-MM) * Real.exp (10 * e - S / M)
          ≤ C * (δ : ℝ) ^ (-MM) * Real.exp (-(Real.log (10 * C) + 1 + MM * l)) := by
            apply mul_le_mul_of_nonneg_left _ hCt
            exact hExpLe
      _ = (1 / 10) * e⁻¹ := by
            rw [hExpT]
            exact hProd
  exact lt_of_le_of_lt hMain hfinite

/-- **The ED-bad event has probability below `1/4`.**

This event-level form of `Kakeya.exists_rigid_family_ed_good` bounds the
probability of failure. It can be combined with the Frostman bound
`Kakeya.rigid_frostman_bad_prob_lt` under a shared probability budget.
No independence is needed: `P(Aᶜ) + P(Bᶜ) < 1` suffices.

The cap `rigidMED C_EDlog δ` is `O(log (1/δ))` and is independent of the
Frostman constant. -/
theorem rigid_ed_bad_prob_lt [Nontrivial E] (hn : 1 < Module.finrank ℝ E) :
    ∃ C_EDlog : ℝ, 0 < C_EDlog ∧
      ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
      ∀ {ι : Type*} (s : Finset ι) (T : ι → Tube δ E),
        (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall (0 : E) 1) →
        (s : Set ι).Pairwise
          (fun i j => IsEssentiallyDistinct (T i).carrier (T j).carrier) →
        ∀ (J : ℕ), 0 < J →
          (J : ℝ) ≤ (⌈(ConvexSpaceBody.frostmanConstant s (fun i => (T i).toConvexSpaceBody)
              ConvexSpaceBody.closedUnitBall).toReal⌉₊ : ℝ) →
          ∃ NetT : Finset (Tube δ E),
            (∀ T₀ ∈ NetT, T₀.carrier ⊆ Metric.closedBall (0 : E) (7 / 2)) ∧
            (∀ T₀ : Tube δ E, T₀.carrier ⊆ Metric.closedBall (0 : E) 2 →
              ∃ T₀' ∈ NetT,
                T₀.carrier ⊆ Metric.cthickening (99 * (δ : ℝ)) T₀'.carrier) ∧
            rigidPiMeasure E J
                {ω : Fin J → unitary (E →L[ℝ] E) × E |
                  ∃ T₀ ∈ NetT, ((rigidMED C_EDlog δ : ℕ) : ℝ)
                    < ∑ j : Fin J, edBadCountAt s T T₀ J j ω}
              < ENNReal.ofReal (1 / 4) := by
  classical
  obtain ⟨M, δ₀, hM, hδ₀, hTail⟩ := edBadCount_chernoff_tail (E := E) hn
  refine ⟨M * edNetCalibration E, mul_pos hM edNetCalibration_pos, ?_⟩
  have hδ₀pos : (0 : ℝ) < (δ₀ : ℝ) := by exact_mod_cast hδ₀
  have hlt1 : ∀ᶠ (x : ℝ) in 𝓝[>] (0 : ℝ), x < (1 : ℝ) := by
    refine Filter.eventually_of_mem (Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)) ?_
    intro x hx
    exact hx.2
  have hle₀ : ∀ᶠ (δ : NNReal) in 𝓝[>] (0 : NNReal), δ ≤ δ₀ := by
    have hx : ∀ᶠ (x : ℝ) in 𝓝[>] (0 : ℝ), x ≤ (δ₀ : ℝ) := by
      refine Filter.eventually_of_mem (Ioo_mem_nhdsGT hδ₀pos) ?_
      intro x hx
      exact le_of_lt hx.2
    filter_upwards [nnreal_eventually_of_real_eventually hx] with δ hx
    exact_mod_cast hx
  filter_upwards [self_mem_nhdsWithin, nnreal_eventually_of_real_eventually hlt1,
      hle₀] with δ hδpos hδlt hδle₀
  intro ι s T hSub hPairwise_J J hJ hJle
  have hδltOne : δ < 1 := by exact_mod_cast hδlt
  have hδleOneR : (δ : ℝ) ≤ 1 := le_of_lt hδlt
  obtain ⟨NetT, hcard, hNetB, _hvol, happrox⟩ :=
    Kakeya.exists_thin_tube_net (E := E) hδpos hδltOne
  let S : ℝ := ((rigidMED (M * edNetCalibration E) δ : ℕ) : ℝ)
  let Ω := Fin J → (unitary (E →L[ℝ] E) × E)
  let μ : Measure Ω := rigidPiMeasure E J
  have hμuniv : μ Set.univ = 1 := by
    simpa [μ] using
      (inferInstance : IsProbabilityMeasure (rigidPiMeasure E J)).measure_univ
  haveI : IsFiniteMeasure μ := by
    constructor
    rw [hμuniv]
    exact ENNReal.coe_lt_top
  let BadOf : Tube δ E → Set Ω :=
    fun T₀ => {ω | S < ∑ j : Fin J, edBadCountAt s T T₀ J j ω}
  let B : Set Ω := ⋃ T₀ ∈ NetT, BadOf T₀
  let EXP : ℝ := Real.exp (10 * Real.exp 1 - S / M)
  have hTailB : ∀ T₀ ∈ NetT, (μ (BadOf T₀)).toReal ≤ EXP := by
    intro T₀ hT₀
    have h7 : T₀.carrier ⊆ Metric.closedBall (0 : E) (7 / 2) := hNetB T₀ hT₀
    simpa [μ, BadOf, EXP] using
      (hTail hδpos hδle₀ s T T₀ hSub hPairwise_J h7 J hJ hJle S)
  have hsum : (∑ T₀ ∈ NetT, (μ (BadOf T₀)).toReal) ≤ (NetT.card : ℝ) * EXP := by
    calc
      (∑ T₀ ∈ NetT, (μ (BadOf T₀)).toReal) ≤ ∑ T₀ ∈ NetT, EXP := by
        exact Finset.sum_le_sum (fun T₀ hT₀ => hTailB T₀ hT₀)
      _ = (NetT.card : ℝ) * EXP := by
        simp [Finset.sum_const]
  have htoRealB : (μ B).toReal ≤ (NetT.card : ℝ) * EXP := by
    have hBunion : μ B ≤ ∑ T₀ ∈ NetT, μ (BadOf T₀) :=
      measure_biUnion_finset_le NetT BadOf
    have hSn : (∑ T₀ ∈ NetT, μ (BadOf T₀)) ≠ (⊤ : ENNReal) := by
      rw [ENNReal.sum_ne_top]
      intro T₀ hT₀
      exact measure_ne_top μ (BadOf T₀)
    calc
      (μ B).toReal ≤ (∑ T₀ ∈ NetT, μ (BadOf T₀)).toReal :=
        ENNReal.toReal_mono hSn hBunion
      _ = ∑ T₀ ∈ NetT, (μ (BadOf T₀)).toReal := by
        exact ENNReal.toReal_sum (fun T₀ hT₀ => measure_ne_top μ (BadOf T₀))
      _ ≤ (NetT.card : ℝ) * EXP := hsum
  have hbelow : (NetT.card : ℝ) * EXP < 1 / 10 := by
    have hmono : (NetT.card : ℝ) * EXP ≤
        (netGeomConstantC E * (δ : ℝ) ^ (-(netGeomConstantM E))) * EXP :=
      mul_le_mul_of_nonneg_right hcard (Real.exp_pos _).le
    have hU : (netGeomConstantC E * (δ : ℝ) ^ (-(netGeomConstantM E))) * EXP < 1 / 10 := by
      simpa [S, EXP] using
        (net_union_bound_lt (M := M) (A := edNetCalibration E) hM le_rfl hδpos hδleOneR)
    exact lt_of_le_of_lt hmono hU
  have h1_10 : (μ B).toReal < 1 / 10 := lt_of_le_of_lt htoRealB hbelow
  refine ⟨NetT, hNetB, happrox, ?_⟩
  have hset : {ω : Ω | ∃ T₀ ∈ NetT, S < ∑ j : Fin J, edBadCountAt s T T₀ J j ω} = B := by
    ext ω
    simp [B, BadOf]
  rw [hset]
  have hBnt : μ B ≠ (⊤ : ENNReal) := measure_ne_top μ B
  have hB_eq : ENNReal.ofReal (μ B).toReal = μ B := ENNReal.ofReal_toReal hBnt
  rw [← hB_eq]
  have hq : (1 / 10 : ℝ) < 1 / 4 := by norm_num
  have hmu14 : (μ B).toReal < 1 / 4 := lt_trans h1_10 hq
  exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ) < 1 / 4)).mpr hmu14

/-- **A single tuple of rigid motions, ED-good against every net member.**

Together with the net's approximation property (the second conjunct), this is what the deterministic
`IsEDUpToMult` bridge consumes. The cap `rigidMED C_EDlog δ` is polylogarithmic in `1/δ` and
does not depend on the Frostman constant of the family; the number of copies `J` may be taken
to be `⌈C_F⌉₊`. -/
theorem exists_rigid_family_ed_good [Nontrivial E] (hn : 1 < Module.finrank ℝ E) :
    ∃ C_EDlog : ℝ, 0 < C_EDlog ∧
      ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
      ∀ {ι : Type*} (s : Finset ι) (T : ι → Tube δ E),
        (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall (0 : E) 1) →
        (s : Set ι).Pairwise
          (fun i j => IsEssentiallyDistinct (T i).carrier (T j).carrier) →
        ∀ (J : ℕ), 0 < J →
          (J : ℝ) ≤ (⌈(ConvexSpaceBody.frostmanConstant s (fun i => (T i).toConvexSpaceBody)
              ConvexSpaceBody.closedUnitBall).toReal⌉₊ : ℝ) →
          ∃ (NetT : Finset (Tube δ E)) (ω : Fin J → (unitary (E →L[ℝ] E) × E)),
            (∀ T₀ ∈ NetT, T₀.carrier ⊆ Metric.closedBall (0 : E) (7 / 2)) ∧
            (∀ T₀ : Tube δ E, T₀.carrier ⊆ Metric.closedBall (0 : E) 2 →
              ∃ T₀' ∈ NetT,
                T₀.carrier ⊆ Metric.cthickening (99 * (δ : ℝ)) T₀'.carrier) ∧
            (∀ T₀ ∈ NetT,
              ∑ j : Fin J, edBadCountAt s T T₀ J j ω
                ≤ ((rigidMED C_EDlog δ : ℕ) : ℝ)) := by
  classical
  obtain ⟨M, δ₀, hM, hδ₀, hTail⟩ := edBadCount_chernoff_tail (E := E) hn
  refine ⟨M * edNetCalibration E, mul_pos hM edNetCalibration_pos, ?_⟩
  have hδ₀pos : (0 : ℝ) < (δ₀ : ℝ) := by exact_mod_cast hδ₀
  have hlt1 : ∀ᶠ (x : ℝ) in 𝓝[>] (0 : ℝ), x < (1 : ℝ) := by
    refine Filter.eventually_of_mem (Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)) ?_
    intro x hx
    exact hx.2
  have hle₀ : ∀ᶠ (δ : NNReal) in 𝓝[>] (0 : NNReal), δ ≤ δ₀ := by
    have hx : ∀ᶠ (x : ℝ) in 𝓝[>] (0 : ℝ), x ≤ (δ₀ : ℝ) := by
      refine Filter.eventually_of_mem (Ioo_mem_nhdsGT hδ₀pos) ?_
      intro x hx
      exact le_of_lt hx.2
    filter_upwards [nnreal_eventually_of_real_eventually hx] with δ hx
    exact_mod_cast hx
  filter_upwards [self_mem_nhdsWithin, nnreal_eventually_of_real_eventually hlt1,
      hle₀] with δ hδpos hδlt hδle₀
  intro ι s T hSub hPairwise_J J hJ hJle
  have hδltOne : δ < 1 := by exact_mod_cast hδlt
  have hδleOneR : (δ : ℝ) ≤ 1 := le_of_lt hδlt
  obtain ⟨NetT, hcard, hNetB, _hvol, happrox⟩ :=
    Kakeya.exists_thin_tube_net (E := E) hδpos hδltOne
  let S : ℝ := ((rigidMED (M * edNetCalibration E) δ : ℕ) : ℝ)
  let Ω := Fin J → (unitary (E →L[ℝ] E) × E)
  let μ : Measure Ω := rigidPiMeasure E J
  have hμuniv : μ Set.univ = 1 := by
    simpa [μ] using
      (inferInstance : IsProbabilityMeasure (rigidPiMeasure E J)).measure_univ
  haveI : IsFiniteMeasure μ := by
    constructor
    rw [hμuniv]
    exact ENNReal.coe_lt_top
  let BadOf : Tube δ E → Set Ω :=
    fun T₀ => {ω | S < ∑ j : Fin J, edBadCountAt s T T₀ J j ω}
  let B : Set Ω := ⋃ T₀ ∈ NetT, BadOf T₀
  let EXP : ℝ := Real.exp (10 * Real.exp 1 - S / M)
  have hTailB : ∀ T₀ ∈ NetT, (μ (BadOf T₀)).toReal ≤ EXP := by
    intro T₀ hT₀
    have h7 : T₀.carrier ⊆ Metric.closedBall (0 : E) (7 / 2) := hNetB T₀ hT₀
    simpa [μ, BadOf, EXP] using
      (hTail hδpos hδle₀ s T T₀ hSub hPairwise_J h7 J hJ hJle S)
  have hsum : (∑ T₀ ∈ NetT, (μ (BadOf T₀)).toReal) ≤ (NetT.card : ℝ) * EXP := by
    calc
      (∑ T₀ ∈ NetT, (μ (BadOf T₀)).toReal) ≤ ∑ T₀ ∈ NetT, EXP := by
        exact Finset.sum_le_sum (fun T₀ hT₀ => hTailB T₀ hT₀)
      _ = (NetT.card : ℝ) * EXP := by
        simp [Finset.sum_const]
  have htoRealB : (μ B).toReal ≤ (NetT.card : ℝ) * EXP := by
    have hBunion : μ B ≤ ∑ T₀ ∈ NetT, μ (BadOf T₀) :=
      measure_biUnion_finset_le NetT BadOf
    have hSn : (∑ T₀ ∈ NetT, μ (BadOf T₀)) ≠ (⊤ : ENNReal) := by
      rw [ENNReal.sum_ne_top]
      intro T₀ hT₀
      exact measure_ne_top μ (BadOf T₀)
    calc
      (μ B).toReal ≤ (∑ T₀ ∈ NetT, μ (BadOf T₀)).toReal :=
        ENNReal.toReal_mono hSn hBunion
      _ = ∑ T₀ ∈ NetT, (μ (BadOf T₀)).toReal := by
        exact ENNReal.toReal_sum (fun T₀ hT₀ => measure_ne_top μ (BadOf T₀))
      _ ≤ (NetT.card : ℝ) * EXP := hsum
  have hbelow : (NetT.card : ℝ) * EXP < 1 / 10 := by
    have hmono : (NetT.card : ℝ) * EXP ≤
        (netGeomConstantC E * (δ : ℝ) ^ (-(netGeomConstantM E))) * EXP :=
      mul_le_mul_of_nonneg_right hcard (Real.exp_pos _).le
    have hU : (netGeomConstantC E * (δ : ℝ) ^ (-(netGeomConstantM E))) * EXP < 1 / 10 := by
      simpa [S, EXP] using
        (net_union_bound_lt (M := M) (A := edNetCalibration E) hM le_rfl hδpos hδleOneR)
    exact lt_of_le_of_lt hmono hU
  have h1_10 : (μ B).toReal < 1 / 10 := lt_of_le_of_lt htoRealB hbelow
  have h1 : (μ B).toReal < 1 := lt_trans h1_10 (by norm_num)
  have hle1 : μ B ≤ 1 := by
    calc μ B ≤ μ Set.univ := measure_mono (Set.subset_univ B)
         _ = 1 := hμuniv
  have hne1 : μ B ≠ 1 := by
    intro hEq
    have h1r : (μ B).toReal = 1 := by rw [hEq]; simp
    have : (μ B).toReal < 1 := h1
    linarith
  have hmuB : μ B < 1 := lt_of_le_of_ne hle1 hne1
  have hBune : B ≠ Set.univ := by
    intro hEq
    have hmu1 : μ B = 1 := by rw [hEq]; exact hμuniv
    exact hne1 hmu1
  obtain ⟨ω, hωnot⟩ : ∃ ω, ω ∉ B := by
    by_contra hnot
    have hAll : B = Set.univ := by
      rw [Set.eq_univ_iff_forall]
      intro z
      by_contra hz
      exact hnot ⟨z, hz⟩
    exact hBune hAll
  have hGood : ∀ T₀ ∈ NetT,
      ∑ j : Fin J, edBadCountAt s T T₀ J j ω ≤ S := by
    intro T₀ hT₀
    have hnotM : ω ∉ BadOf T₀ := by
      by_contra hmem
      have hIn : ω ∈ B := by
        exact Set.mem_biUnion hT₀ hmem
      exact hωnot hIn
    change ¬ S < ∑ j : Fin J, edBadCountAt s T T₀ J j ω at hnotM
    exact not_lt.mp hnotM
  exact ⟨NetT, ω, ⟨hNetB, happrox, hGood⟩⟩

end

end Kakeya

end
