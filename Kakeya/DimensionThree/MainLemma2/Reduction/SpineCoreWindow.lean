/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineTwoScale
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineEveryScale
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineEccentric
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineShadingBridge
public import Kakeya.StickyKakeya.BallReduction

/-!
# Branch (ii) of the geometric core: entering the dividing window
-/

@[expose] public section

open MeasureTheory ConvexSpaceBody ShadedBody Tube
open scoped NNReal ENNReal

namespace Kakeya.ML2Core

universe u v

variable {E : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

/-! ## the estimate: the two window scales -/

/-- The fine endpoint of the grid is the smallest grid scale. -/
theorem delta_le_gridScale {δ : NNReal} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) {M k : ℕ} (hk : k ≤ M) :
    δ ≤ gridScale δ M k := by
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · have hk0 : k = 0 := Nat.le_zero.mp hk
    subst hk0
    simpa using hδ1
  · calc δ = gridScale δ M M := (gridScale_self δ hM).symm
      _ ≤ gridScale δ M k := gridScale_antitone hδ0 hδ1 M hk

variable {ι : Type u}

section Window

variable {δ Cst : NNReal} {s : Finset ι} {T : ι → Tube δ E}

omit [Nontrivial E] in
/-- **the estimate, the scale hierarchy of a dividing window.**  `δ ≤ τ ≤ θ ≤ 1`. -/
theorem window_scales {𝒰 : UniformTubeSet s T (ssfGridLen δ) Cst} {Cstar : ENNReal}
    {η : ℕ → ℝ} {εd : ℝ} {N a b m : ℕ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hw : ML2Reduction.IsKatzTaoDividingWindow 𝒰 Cstar η εd N a b m) :
    δ ≤ gridScale δ (ssfGridLen δ) b ∧
      gridScale δ (ssfGridLen δ) b ≤ gridScale δ (ssfGridLen δ) a ∧
      gridScale δ (ssfGridLen δ) a ≤ 1 :=
  ⟨delta_le_gridScale hδ0 hδ1 hw.fine_le_gridLen,
    gridScale_antitone hδ0 hδ1 _ hw.coarse_lt_fine.le,
    gridScale_le_one hδ1 _ _⟩

/-- `⌈log log (1/δ)⌉ ≤ log(1/δ)/4 + 2`: the grid length of GWZ Definition 2.1 is a
*doubly* logarithmic quantity, so it is beaten by every fixed fraction of `log (1/δ)`.

Only the crude bounds `log x ≤ x - 1` (twice) and `log 2 ≤ 1` enter, which is why the constants
are `1/4` and `2` rather than sharp. -/
theorem ssfGridLen_le_quarter_log {δ : NNReal} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    (ssfGridLen δ : ℝ) ≤ Real.log (1 / (δ : ℝ)) / 4 + 2 := by
  set L : ℝ := Real.log (1 / (δ : ℝ)) with hL
  have hd : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ0
  have hd1 : (δ : ℝ) ≤ 1 := hδ1
  have hL0 : 0 ≤ L := by
    rw [hL, one_div, Real.log_inv]
    exact neg_nonneg.mpr (Real.log_nonpos hd.le hd1)
  by_cases h1 : (1 : ℝ) ≤ L
  · have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one h1
    have h : 0 ≤ Real.log L := Real.log_nonneg h1
    have hceil : (⌈Real.log L⌉₊ : ℝ) < Real.log L + 1 := Nat.ceil_lt_add_one h
    have hq : Real.log (L / 4) ≤ L / 4 - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    have hsplit : Real.log (L / 4) = Real.log L - Real.log 4 := by
      rw [Real.log_div hLpos.ne' (by norm_num)]
    have hlog4 : Real.log 4 ≤ 2 := by
      have h2 : Real.log 2 ≤ 1 := by
        have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num)
        linarith
      have : Real.log 4 = 2 * Real.log 2 := by
        rw [show (4:ℝ) = 2 ^ (2:ℕ) by norm_num, Real.log_pow]
        push_cast
        ring
      linarith
    have hle : (ssfGridLen δ : ℝ) ≤ Real.log L + 1 := by
      rw [ssfGridLen, ← hL]
      exact hceil.le
    linarith
  · have hlogL : Real.log L ≤ 0 := by
      rcases eq_or_lt_of_le hL0 with h0 | h0
      · rw [← h0]; simp
      · exact Real.log_nonpos h0.le (not_le.mp h1).le
    have hceil0 : ⌈Real.log L⌉₊ = 0 := Nat.ceil_eq_zero.mpr hlogL
    have : (ssfGridLen δ : ℝ) = 0 := by
      rw [ssfGridLen, ← hL, hceil0]; norm_num
    rw [this]
    have : (0:ℝ) ≤ L / 4 := by positivity
    linarith

/-- **The threshold that makes the fine window scale small.**  Below the absolute threshold
`e^{-8}`, `2 ⌈log log 1/δ⌉ ≤ log (1/δ)`, which is what makes every grid scale of index `≥ 1` at
most `1/4` (`Kakeya.ML2Core.gridScale_le_quarter`). -/
theorem exists_threshold_two_mul_ssfGridLen_le_log :
    ∃ δ₀ : NNReal, 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ δ : NNReal, 0 < δ → δ ≤ δ₀ → 2 * (ssfGridLen δ : ℝ) ≤ Real.log (1 / (δ : ℝ)) := by
  refine ⟨⟨Real.exp (-8), (Real.exp_pos _).le⟩, ?_, ?_, ?_⟩
  · rw [← NNReal.coe_pos]; exact Real.exp_pos _
  · rw [← NNReal.coe_le_coe, NNReal.coe_one]
    change Real.exp (-8) ≤ (1 : ℝ)
    rw [Real.exp_le_one_iff]; norm_num
  · intro δ hδ0 hδle
    have hdR : (δ : ℝ) ≤ Real.exp (-8) := hδle
    have hd : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ0
    have hδ1 : δ ≤ 1 := by
      rw [← NNReal.coe_le_coe, NNReal.coe_one]
      refine hdR.trans ?_
      rw [Real.exp_le_one_iff]; norm_num
    have hL8 : 8 ≤ Real.log (1 / (δ : ℝ)) := by
      have h1 : Real.log (δ : ℝ) ≤ -8 := by simpa using Real.log_le_log hd hdR
      rw [one_div, Real.log_inv]; linarith
    have hM := ssfGridLen_le_quarter_log hδ0 hδ1
    linarith

/-- **Every grid scale of index `≥ 1` is at most `1/4`** once `2 M ≤ log (1/δ)` at the grid
length `M`.  This is the side condition of `Kakeya.StickyKakeya.exists_ball_assignment` at the
parent scale, and (with room to spare) the hypothesis `2 τ < 1` of
`Kakeya.ML2Reduction.tube_carrier_subset_closedBall_of_le`. -/
theorem gridScale_le_quarter {δ : NNReal} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) {M k : ℕ}
    (hk : 1 ≤ k) (hkM : k ≤ M) (h : 2 * (M : ℝ) ≤ Real.log (1 / (δ : ℝ))) :
    ((gridScale δ M k : NNReal) : ℝ) ≤ 1 / 4 := by
  have hM0 : 0 < M := lt_of_lt_of_le hk hkM
  have hMR : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM0
  have hd : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ0
  have hd1 : (δ : ℝ) ≤ 1 := hδ1
  have hlogd : Real.log (δ : ℝ) = -Real.log (1 / (δ : ℝ)) := by
    rw [one_div, Real.log_inv]; ring
  have hlog4 : Real.log 4 ≤ 2 := by
    have h2 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num)
      linarith
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4:ℝ) = 2 ^ (2:ℕ) by norm_num, Real.log_pow]
      push_cast; ring
    linarith
  have hcoe : ((gridScale δ M k : NNReal) : ℝ) = (δ : ℝ) ^ ((k : ℝ) / (M : ℝ)) := by
    rw [gridScale, NNReal.coe_rpow]
  rw [hcoe]
  have hstep : (δ : ℝ) ^ ((k : ℝ) / (M : ℝ)) ≤ (δ : ℝ) ^ ((1 : ℝ) / (M : ℝ)) := by
    refine Real.rpow_le_rpow_of_exponent_ge hd hd1 ?_
    have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    exact div_le_div_of_nonneg_right hk1 hMR.le
  refine hstep.trans ?_
  rw [Real.rpow_def_of_pos hd]
  have h2M : (2 : ℝ) ≤ Real.log (1 / (δ : ℝ)) * ((1 : ℝ) / (M : ℝ)) := by
    rw [mul_one_div, le_div_iff₀ hMR]
    linarith
  have hexp : Real.log (δ : ℝ) * ((1 : ℝ) / (M : ℝ)) ≤ Real.log (1 / 4 : ℝ) := by
    rw [hlogd, show Real.log (1 / 4 : ℝ) = -Real.log 4 by rw [one_div, Real.log_inv],
      neg_mul, neg_le_neg_iff]
    linarith
  calc Real.exp (Real.log (δ : ℝ) * ((1 : ℝ) / (M : ℝ)))
      ≤ Real.exp (Real.log (1 / 4 : ℝ)) := Real.exp_le_exp.mpr hexp
    _ = 1 / 4 := Real.exp_log (by norm_num)

end Window

/-! ## the estimate: the parent-ball seam -/

section ParentSeam

variable {δ : NNReal} {s : Finset ι} {T : ι → Tube δ E} {N : ℕ} {σ : ℕ → NNReal}

omit [MeasurableSpace E] [BorelSpace E] [Nontrivial E] in
/-- **An active node of a nested cover carries a leaf.**  Unpacking
`Kakeya.ML2Reduction.activeNodes`. -/
theorem exists_leaf_of_mem_activeNodes (𝒞 : Tube.ChainCoverSystem s T N σ) {b : ℕ}
    {j : ι} (hj : j ∈ ML2Reduction.activeNodes 𝒞 b) :
    ∃ i ∈ s, 𝒞.assign b i = j := by
  classical
  have h : (Tube.coverClass s (𝒞.assign b) j).Nonempty := (Finset.mem_filter.mp hj).2
  obtain ⟨i, hi⟩ := h
  simp only [Tube.coverClass, Finset.mem_filter] at hi
  exact ⟨i, hi.1, hi.2⟩

omit [MeasurableSpace E] [BorelSpace E] [Nontrivial E] in
/-- **The parent-ball seam, measured.**  A level-`b` node of a nested cover whose leaves lie in
`B̄(0, r)` lies in `B̄(0, r + 4 σ b)` — and no better, since a node's core is a unit segment
pinned only to within `O(σ b)` of the leaf's core
(`Kakeya.ML2Reduction.tube_carrier_subset_closedBall_of_le`).

This is the chain-hierarchy reading of `Kakeya.ML2Reduction.parentTube_subset_unitBall_of_leafBall`,
whose `Tube.IsUniformAtScale` form does not apply to a `Tube.ChainCoverSystem`. -/
theorem coverTube_carrier_subset_closedBall (𝒞 : Tube.ChainCoverSystem s T N σ) {b : ℕ}
    (hbN : b ≤ N) (hσ : 2 * (σ b : ℝ) < 1) {r : ℝ}
    (hleaf : ∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall (0 : E) r) :
    ∀ j ∈ ML2Reduction.activeNodes 𝒞 b,
      (𝒞.tube b j).carrier ⊆ Metric.closedBall (0 : E) (r + 4 * (σ b : ℝ)) := by
  intro j hj
  obtain ⟨i, hi, hassign⟩ := exists_leaf_of_mem_activeNodes 𝒞 hj
  have hle : (T i).carrier ⊆ (𝒞.tube b j).carrier := by
    have := 𝒞.le_tube_assign b hbN i hi
    rw [hassign] at this
    exact this
  exact ML2Reduction.tube_carrier_subset_closedBall_of_le (T i) (𝒞.tube b j) hσ hle (hleaf i hi)

omit [MeasurableSpace E] [BorelSpace E] [Nontrivial E] in
/-- **Step 1 of the seam: one translation puts a bounded fraction of the nodes into `B₁`.**

The bare-`Tube` companion of `Kakeya.StickyKakeya.exists_translate_subfamily_unit_ball`, needed
because the level-`b` nodes of a hierarchy are `Tube (σ b) E`, not shaded tubes.  The
cardinality loss `M` is the cardinality of a `1/4`-net of `B̄(0,R)` and is quantified **before**
the scale, hence `δ`-independent. -/
theorem exists_translate_tube_subfamily_unit_ball (R : ℝ) (hR : 1 ≤ R) :
    ∃ M : ℕ, 0 < M ∧
      ∀ {ρ : NNReal}, (ρ : ℝ) ≤ 1 / 4 →
        ∀ {κ : Type u} (t : Finset κ) (P : κ → Tube ρ E),
          (∀ j ∈ t, (P j).carrier ⊆ Metric.closedBall (0 : E) R) →
          ∃ (v : E) (t₀ : Finset κ), t₀ ⊆ t ∧
            (t.card : ℝ) ≤ (M : ℝ) * (t₀.card : ℝ) ∧
            ∀ j ∈ t₀, ((P j).translate v).carrier ⊆ Metric.closedBall (0 : E) 1 := by
  classical
  obtain ⟨xs, hxs_ne, _hxs_norm, hnet⟩ := StickyKakeya.exists_ball_assignment (E := E) R hR
  refine ⟨xs.card, Finset.card_pos.mpr hxs_ne, ?_⟩
  intro ρ hρ κ t P hball
  let x₀ : E := hxs_ne.choose
  have hx₀ : x₀ ∈ xs := hxs_ne.choose_spec
  let g : κ → E := fun j =>
    if h : ∃ x ∈ xs, (P j).carrier ⊆ Metric.closedBall x 1 then h.choose else x₀
  have hg : ∀ j ∈ t, g j ∈ xs := by
    intro j _
    dsimp [g]
    by_cases h : ∃ x ∈ xs, (P j).carrier ⊆ Metric.closedBall x 1
    · rw [dif_pos h]; exact h.choose_spec.1
    · rw [dif_neg h]; exact hx₀
  have hgball : ∀ j ∈ t, (P j).carrier ⊆ Metric.closedBall (g j) 1 := by
    intro j hj
    have hcond : ∃ x ∈ xs, (P j).carrier ⊆ Metric.closedBall x 1 :=
      hnet hρ (P j) (hball j hj)
    dsimp [g]
    rw [dif_pos hcond]
    exact hcond.choose_spec.2
  obtain ⟨x₁, _hx₁, t₀, ht₀, hlabel, hcard⟩ :=
    StickyKakeya.exists_pigeonhole_subfamily t xs hxs_ne g hg
  refine ⟨-x₁, t₀, ht₀, hcard, ?_⟩
  intro j hj
  have hsub : (P j).carrier ⊆ Metric.closedBall (x₁ : E) 1 := by
    simpa [hlabel j hj] using hgball j (ht₀ hj)
  intro y hy
  obtain ⟨z, hz, rfl⟩ := hy
  rw [Metric.mem_closedBall, dist_eq_norm]
  calc ‖(-x₁ + z) - 0‖ = ‖z - x₁‖ := by rw [show (-x₁ + z) - 0 = z - x₁ by abel]
    _ ≤ 1 := by simpa [dist_eq_norm] using (Metric.mem_closedBall.mp (hsub hz))

omit [MeasurableSpace E] [BorelSpace E] [Nontrivial E] in
open Classical in
/-- **Step 2 of the seam: a cardinality share of the nodes is a cardinality share of the
leaves**, at the square of the uniformity constant.

This is the step that makes the seam affordable, and it is the step the plan's §6 D2 says is
missing: a cardinality retention on the *parents* says nothing about the leaves in general,
because parent classes may be wildly unbalanced.  Under GWZ Definition 2.1(iii) — the two
`Tube.UniformTubeSet.card_class_le` / `Tube.UniformTubeSet.le_card_class` brackets — they are
balanced to within `Cu`, and the retention transfers at `Cu ^ 2`.

No positivity of the branching number is needed: the bound is a chain of products in `ℝ≥0`. -/
theorem card_le_of_node_subfamily (𝒞 : Tube.ChainCoverSystem s T N σ) {b : ℕ}
    (hbN : b ≤ N) {Cu Bn A : NNReal}
    (hup : ∀ j ∈ 𝒞.indexSet b, ((Tube.coverClass s (𝒞.assign b) j).card : NNReal) ≤ Cu * Bn)
    (hlo : ∀ j ∈ 𝒞.indexSet b, Bn ≤ Cu * ((Tube.coverClass s (𝒞.assign b) j).card : NNReal))
    {t₁ : Finset ι} (ht₁ : t₁ ⊆ ML2Reduction.activeNodes 𝒞 b)
    (hA : ((ML2Reduction.activeNodes 𝒞 b).card : NNReal) ≤ A * (t₁.card : NNReal)) :
    (s.card : NNReal) ≤ A * Cu * Cu * (({i ∈ s | 𝒞.assign b i ∈ t₁}).card : NNReal) := by
  classical
  set act : Finset ι := ML2Reduction.activeNodes 𝒞 b with hact
  set s₁ : Finset ι := {i ∈ s | 𝒞.assign b i ∈ t₁} with hs₁
  -- the classes of the active nodes partition `s`
  have hfib : s.card = ∑ j ∈ act, (Tube.coverClass s (𝒞.assign b) j).card := by
    rw [hact, Finset.card_eq_sum_card_fiberwise
      (fun i hi => ML2Reduction.assign_mem_activeNodes 𝒞 hbN hi)]
    exact Finset.sum_congr rfl (fun j _ => by rw [Tube.coverClass])
  --... and those of `t₁` partition `s₁`
  have hfib₁ : s₁.card = ∑ j ∈ t₁, (Tube.coverClass s (𝒞.assign b) j).card := by
    rw [Finset.card_eq_sum_card_fiberwise
      (f := 𝒞.assign b) (s := s₁) (t := t₁) (fun i hi => (Finset.mem_filter.mp hi).2)]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    congr 1
    rw [hs₁, Tube.coverClass, Finset.filter_filter]
    refine Finset.filter_congr (fun i _ => ?_)
    exact ⟨fun h => h.2, fun h => ⟨h ▸ hj, h⟩⟩
  have hupper : (s.card : NNReal) ≤ (act.card : NNReal) * (Cu * Bn) := by
    rw [hfib]
    push_cast
    calc (∑ j ∈ act, ((Tube.coverClass s (𝒞.assign b) j).card : NNReal))
        ≤ ∑ _j ∈ act, Cu * Bn :=
          Finset.sum_le_sum (fun j hj => hup j (ML2Reduction.activeNodes_subset 𝒞 b hj))
      _ = (act.card : NNReal) * (Cu * Bn) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  have hlower : (t₁.card : NNReal) * Bn ≤ Cu * (s₁.card : NNReal) := by
    rw [hfib₁]
    push_cast
    calc (t₁.card : NNReal) * Bn = ∑ _j ∈ t₁, Bn := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ j ∈ t₁, Cu * ((Tube.coverClass s (𝒞.assign b) j).card : NNReal) :=
          Finset.sum_le_sum (fun j hj =>
            hlo j (ML2Reduction.activeNodes_subset 𝒞 b (ht₁ hj)))
      _ = Cu * ∑ j ∈ t₁, ((Tube.coverClass s (𝒞.assign b) j).card : NNReal) :=
          (Finset.mul_sum _ _ _).symm
  calc (s.card : NNReal) ≤ (act.card : NNReal) * (Cu * Bn) := hupper
    _ ≤ (A * (t₁.card : NNReal)) * (Cu * Bn) := by gcongr
    _ = A * Cu * ((t₁.card : NNReal) * Bn) := by ring
    _ ≤ A * Cu * (Cu * (s₁.card : NNReal)) := by gcongr
    _ = A * Cu * Cu * (s₁.card : NNReal) := by ring

end ParentSeam

/-! ### the estimate assembled: the seam, translated and priced -/

section SeamAssembled

omit [MeasurableSpace E] [BorelSpace E] [Nontrivial E] in
open Classical in
/-- **the estimate, the parent-ball seam of `Kakeya.ML2Reduction.exists_spineTwoScale`, discharged.**

`Kakeya.ML2Reduction.exists_spineTwoScale` needs the level-`b` nodes in `B̄(0,1)`; `Dichotomy`
grants only the leaves, and a node lies in `B̄(0, 1 + 4 σ_b)` and no better
(`Kakeya.ML2Core.coverTube_carrier_subset_closedBall`).  This is the plan's §6 **D2 Option A**:
translate the configuration by one fixed vector and keep the nodes that the translation carries
into `B₁`, at the `δ`-independent cardinality loss `M` of a `1/4`-net of `B̄(0,2)`.

The retention is stated on the **leaves**, not on the nodes, which is what a consumer needs and
what §6 D2 says a bare translation does not give: the transfer is
`Kakeya.ML2Core.card_le_of_node_subfamily`, and it is paid for by GWZ Definition 2.1(iii)'s two
class brackets, at `Cu ^ 2`.

`M` is quantified before the scale, so it is a genuine constant.  The side condition
`σ b ≤ 1/4` is discharged for the grid chain by `Kakeya.ML2Core.gridScale_le_quarter` together
with `Kakeya.ML2Core.exists_threshold_two_mul_ssfGridLen_le_log`. -/
theorem exists_parentSeam :
    ∃ M : ℕ, 0 < M ∧
      ∀ {δ : NNReal} {κ : Type u} {s : Finset κ} {T : κ → Tube δ E} {N : ℕ} {σ : ℕ → NNReal}
        (𝒞 : Tube.ChainCoverSystem s T N σ) {b : ℕ} {Cu Bn : NNReal},
        b ≤ N → (σ b : ℝ) ≤ 1 / 4 →
        (∀ j ∈ 𝒞.indexSet b, ((Tube.coverClass s (𝒞.assign b) j).card : NNReal) ≤ Cu * Bn) →
        (∀ j ∈ 𝒞.indexSet b, Bn ≤ Cu * ((Tube.coverClass s (𝒞.assign b) j).card : NNReal)) →
        (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall (0 : E) 1) →
        ∃ (v : E) (t₁ : Finset κ), t₁ ⊆ ML2Reduction.activeNodes 𝒞 b ∧
          (∀ j ∈ t₁, ((𝒞.tube b j).translate v).carrier ⊆ Metric.closedBall (0 : E) 1) ∧
          (∀ i ∈ ({i ∈ s | 𝒞.assign b i ∈ t₁} : Finset κ),
            ((T i).translate v).carrier ⊆ Metric.closedBall (0 : E) 1) ∧
          (s.card : NNReal)
            ≤ (M : NNReal) * Cu * Cu
              * (({i ∈ s | 𝒞.assign b i ∈ t₁} : Finset κ).card : NNReal) := by
  classical
  obtain ⟨M, hM0, hM⟩ :=
    exists_translate_tube_subfamily_unit_ball (E := E) 2 (by norm_num)
  refine ⟨M, hM0, ?_⟩
  intro δ κ s T N σ 𝒞 b Cu Bn hbN hσ4 hup hlo hball
  have hσ0 : (0 : ℝ) ≤ (σ b : ℝ) := (σ b).coe_nonneg
  have hσ1 : 2 * (σ b : ℝ) < 1 := by linarith
  -- the nodes lie in `B̄(0, 1 + 4 σ_b) ⊆ B̄(0, 2)`
  have hnode2 : ∀ j ∈ ML2Reduction.activeNodes 𝒞 b,
      (𝒞.tube b j).carrier ⊆ Metric.closedBall (0 : E) 2 := by
    intro j hj
    refine (coverTube_carrier_subset_closedBall 𝒞 hbN hσ1 hball j hj).trans ?_
    exact Metric.closedBall_subset_closedBall (by linarith)
  obtain ⟨v, t₁, ht₁sub, hcardt, hballt⟩ :=
    hM (ρ := σ b) hσ4 (ML2Reduction.activeNodes 𝒞 b) (𝒞.tube b) hnode2
  refine ⟨v, t₁, ht₁sub, hballt, ?_, ?_⟩
  · -- the leaves of the retained nodes are translated into `B₁` as well
    intro i hi
    obtain ⟨his, hit⟩ := Finset.mem_filter.mp hi
    refine subset_trans ?_ (hballt _ hit)
    have hle : (T i).carrier ⊆ (𝒞.tube b (𝒞.assign b i)).carrier :=
      𝒞.le_tube_assign b hbN i his
    exact Set.image_mono hle
  · -- the cardinality retention, transferred from the nodes to the leaves
    refine card_le_of_node_subfamily 𝒞 hbN hup hlo ht₁sub ?_
    have : ((ML2Reduction.activeNodes 𝒞 b).card : ℝ) ≤ (M : ℝ) * (t₁.card : ℝ) := hcardt
    exact_mod_cast this

end SeamAssembled

/-! ### The mass half of the seam -/

/-- **The leaf-cardinality retention of the seam becomes a mass retention**, under the pointwise
density invariant `Kakeya.ML2Shaded.HasDenseShading` that GC-P1's dividing-scales package hands
out at `lam ≥ δ^ν/2` (this file does not import it, so the reference is informal on purpose).

This is `Kakeya.ML2Shading.sum_shade_le_of_card_le_of_denseShading` at an `ℝ≥0` loss, which is the
form `Kakeya.ML2Core.exists_parentSeam` produces.  It is the pointwise companion the plan's §6 D2
says the cardinality-only route needs: without it,
`Kakeya.ML2Inputs.no_mass_share_of_essDistinct_refinement` is the refutation that no
finite mass loss follows from a cardinality share alone. -/
theorem sum_shade_le_of_node_subfamily {δ : NNReal} (hδ1 : δ ≤ 1) {s s₁ : Finset ι}
    (hsub : s₁ ⊆ s) {V : ι → ShadedTube δ E} {lam A : NNReal}
    (hdense : ML2Shaded.HasDenseShading lam s (fun i => (V i).toShadedBody))
    (hcard : (s.card : NNReal) ≤ A * (s₁.card : NNReal)) :
    (lam : ENNReal) * (Tube.le_volume.c (Module.finrank ℝ E) : ENNReal)
        * ∑ i ∈ s, volume (V i).shade
      ≤ (A : ENNReal) * (Tube.volume_le.C (Module.finrank ℝ E) : ENNReal)
          * ∑ i ∈ s₁, volume (V i).shade := by
  refine ML2Shading.sum_shade_le_of_card_le_of_denseShading hδ1 hsub hdense ?_
  have : ((s.card : NNReal) : ENNReal) ≤ ((A * (s₁.card : NNReal) : NNReal) : ENNReal) := by
    exact_mod_cast hcard
  simpa [ENNReal.coe_mul] using this

/-! ## the estimate: the two-scale split at the two window levels -/

section TwoScaleRun

variable {δ : NNReal} {s : Finset ι} {V : ι → ShadedTube δ E} {N : ℕ} {σ : ℕ → NNReal}

open Classical in
/-- **the estimate.**  `Kakeya.ML2Reduction.exists_spineTwoScale` run at the two levels `a ≤ b` of a
nested cover, on the configuration `Kakeya.ML2Core.exists_parentSeam` translates into `B₁`.

The two outer quantities — the multiplicity of the leaf family and its fullness — are stated on
the **untranslated** shading, by `ShadedBody.multiplicity_translate_const` and
`ShadedBody.fullness_translate_const`; only the four manufactured shadings `Y'`, `Yτ`, `Yτ'`,
`Yθ` live on the translated tubes, as they must, since they are refinements of them.

The retained node set satisfies `tτ' ⊆ t₁ ⊆ activeNodes 𝒞 b` and the coarse one
`tθ' ⊆ 𝒞.indexSet a`, and the loss is
`spineScaleLoss 3 |s₁| δ · spineScaleLoss 3 |tτ'| (σ b)` — the product of the two applications of
GWZ Lemma 5.11, with the *retained* fine-node cardinality in the second factor, as
`Kakeya.ML2Reduction.exists_spineTwoScale` delivers it.

This declaration proves no new geometry: it is the wiring that discharges
`Kakeya.ML2Reduction.exists_spineTwoScale`'s six structural hypotheses from the hierarchy
(`Tube.ChainCoverSystem.le_tube_assign`, `Kakeya.ML2Reduction.tube_le_coarseNode`,
`Kakeya.ML2Reduction.coarseNode_mem`) and its two ball hypotheses from the seam.  The reason it
is *not* `Kakeya.ML2Reduction.exists_spineTwoScale_ofChain` is exactly the seam: that wrapper
pins the fine parent family to the whole of `activeNodes 𝒞 b`, which the seam cannot normalise. -/
theorem exists_spineTwoScale_ofChain_translated
    (hδ0 : 0 < δ) (𝒞 : Tube.ChainCoverSystem s (fun i => (V i).toTube) N σ)
    {a b : ℕ} (hab : a ≤ b) (haN : a ≤ N) (hbN : b ≤ N)
    (hδτ : δ ≤ σ b) (hτθ : σ b ≤ σ a) (hθ1 : σ a ≤ 1)
    (v : E) {t₁ : Finset ι} (ht₁ : t₁ ⊆ ML2Reduction.activeNodes 𝒞 b)
    (hballt : ∀ j ∈ t₁, ((𝒞.tube b j).translate v).carrier ⊆ Metric.closedBall (0 : E) 1)
    (hballs : ∀ i ∈ ({i ∈ s | 𝒞.assign b i ∈ t₁} : Finset ι),
      ((V i).translate v).carrier ⊆ Metric.closedBall (0 : E) 1) :
    ∃ tτ' ⊆ t₁, ∃ tθ' ⊆ 𝒞.indexSet a,
      ∃ (Yτ Yτ' : ι → ShadedTube (σ b) E) (Yθ : ι → ShadedTube (σ a) E)
        (Y' : ι → ShadedTube δ E),
        tτ'.card ≤ t₁.card ∧
        (∀ j, (Yτ j).toTube = (𝒞.tube b j).translate v) ∧
        (∀ j, (Yτ' j).toTube = (𝒞.tube b j).translate v) ∧
        (∀ k, (Yθ k).toTube = (𝒞.tube a k).translate v) ∧
        (∀ i, (Y' i).toTube = ((V i).translate v).toTube) ∧
        (∀ i, (Y' i).shade ⊆ ((V i).translate v).shade) ∧
        (∀ j, (Yτ' j).shade ⊆ (Yτ j).shade) ∧
        (0 < ∑ i ∈ ({i ∈ s | 𝒞.assign b i ∈ t₁} : Finset ι), volume (V i).shade →
          tτ'.Nonempty ∧ tθ'.Nonempty) ∧
        ShadedBody.IsCRefinement
            {i ∈ ({i ∈ s | 𝒞.assign b i ∈ t₁} : Finset ι) | 𝒞.assign b i ∈ tτ'}
            (fun i => (Y' i).toShadedBody)
            ({i ∈ s | 𝒞.assign b i ∈ t₁} : Finset ι)
            (fun i => ((V i).translate v).toShadedBody)
            (ML2Reduction.spineScaleLoss (Module.finrank ℝ E)
              ({i ∈ s | 𝒞.assign b i ∈ t₁} : Finset ι).card δ)⁻¹ ∧
        ShadedBody.IsCRefinement {j ∈ tτ' | ML2Reduction.coarseNode 𝒞 a b j ∈ tθ'}
            (fun j => (Yτ' j).toShadedBody) tτ' (fun j => (Yτ j).toShadedBody)
            (ML2Reduction.spineScaleLoss (Module.finrank ℝ E) tτ'.card (σ b))⁻¹ ∧
        (ML2Reduction.spineScaleLoss (Module.finrank ℝ E)
              ({i ∈ s | 𝒞.assign b i ∈ t₁} : Finset ι).card δ)⁻¹ *
            ShadedBody.fullness ({i ∈ s | 𝒞.assign b i ∈ t₁} : Finset ι)
              (fun i => (V i).toShadedBody)
          ≤ ShadedBody.fullness tτ' (fun j => (Yτ j).toShadedBody) ∧
        (ML2Reduction.spineScaleLoss (Module.finrank ℝ E)
                ({i ∈ s | 𝒞.assign b i ∈ t₁} : Finset ι).card δ *
              ML2Reduction.spineScaleLoss (Module.finrank ℝ E) tτ'.card (σ b))⁻¹ *
            ShadedBody.fullness ({i ∈ s | 𝒞.assign b i ∈ t₁} : Finset ι)
              (fun i => (V i).toShadedBody)
          ≤ ShadedBody.fullness tθ' (fun k => (Yθ k).toShadedBody) ∧
        (∀ jτ ∈ tτ', ∀ jθ ∈ tθ',
          ShadedBody.multiplicity ({i ∈ s | 𝒞.assign b i ∈ t₁} : Finset ι)
              (fun i => (V i).toShadedBody)
            ≤ ((ML2Reduction.spineScaleLoss (Module.finrank ℝ E)
                    ({i ∈ s | 𝒞.assign b i ∈ t₁} : Finset ι).card δ *
                  ML2Reduction.spineScaleLoss (Module.finrank ℝ E) tτ'.card (σ b)
                    : NNReal) : ENNReal)
              * ShadedBody.multiplicity
                  {i ∈ ({i ∈ s | 𝒞.assign b i ∈ t₁} : Finset ι) | 𝒞.assign b i = jτ}
                  (fun i => (Y' i).toShadedBody)
              * ShadedBody.multiplicity {j ∈ tτ' | ML2Reduction.coarseNode 𝒞 a b j = jθ}
                  (fun j => (Yτ' j).toShadedBody)
              * ShadedBody.multiplicity tθ' (fun k => (Yθ k).toShadedBody)) := by
  classical
  set s₁ : Finset ι := {i ∈ s | 𝒞.assign b i ∈ t₁} with hs₁
  have hs₁s : s₁ ⊆ s := Finset.filter_subset _ _
  have hmapsτ : ∀ i ∈ s₁, 𝒞.assign b i ∈ t₁ := fun i hi => (Finset.mem_filter.mp hi).2
  have hleτ : ∀ i ∈ s₁, ((V i).translate v).toConvexSpaceBody
      ≤ ((𝒞.tube b (𝒞.assign b i)).translate v).toConvexSpaceBody := by
    intro i hi
    exact translate_le_translate v (𝒞.le_tube_assign b hbN i (hs₁s hi))
  have hmapsθ : ∀ j ∈ t₁, ML2Reduction.coarseNode 𝒞 a b j ∈ 𝒞.indexSet a :=
    fun j hj => ML2Reduction.coarseNode_mem 𝒞 haN (ht₁ hj)
  have hleθ : ∀ j ∈ t₁, ((𝒞.tube b j).translate v).toConvexSpaceBody
      ≤ ((𝒞.tube a (ML2Reduction.coarseNode 𝒞 a b j)).translate v).toConvexSpaceBody := by
    intro j hj
    exact translate_le_translate v
      (ML2Reduction.tube_le_coarseNode 𝒞 hab hbN (ht₁ hj))
  have hfullEq : ShadedBody.fullness s₁ (fun i => ((V i).translate v).toShadedBody)
      = ShadedBody.fullness s₁ (fun i => (V i).toShadedBody) :=
    ShadedBody.fullness_translate_const s₁ (fun i => (V i).toShadedBody) v
  have hmulEq : ShadedBody.multiplicity s₁ (fun i => ((V i).translate v).toShadedBody)
      = ShadedBody.multiplicity s₁ (fun i => (V i).toShadedBody) :=
    ShadedBody.multiplicity_translate_const s₁ (fun i => (V i).toShadedBody) v
  have hmassEq : ∀ i, volume ((V i).translate v).shade = volume (V i).shade := by
    intro i
    exact MeasureTheory.measure_image_add _ v (V i).shade
  obtain ⟨tτ', htτ', tθ', htθ', Yτ, Yτ', Yθ, Y', hcard, hYτ, hYτ', hYθ, hY'tube, hY'shade,
      hYτ'shade, hne, href1, href2, hfull1, hfull2, hprod⟩ :=
    ML2Reduction.exists_spineTwoScale (E := E) hδ0 hδτ hτθ hθ1
      (s := s₁) (t := t₁) (u := 𝒞.indexSet a)
      (fun i => (V i).translate v) (fun j => (𝒞.tube b j).translate v)
      (fun k => (𝒞.tube a k).translate v) (𝒞.assign b) (ML2Reduction.coarseNode 𝒞 a b)
      hballs hballt hmapsτ hleτ hmapsθ hleθ
  refine ⟨tτ', htτ', tθ', htθ', Yτ, Yτ', Yθ, Y', hcard, hYτ, hYτ', hYθ, hY'tube, hY'shade,
    hYτ'shade, ?_, href1, href2, ?_, ?_, ?_⟩
  · intro hpos
    exact hne (by simpa [hmassEq] using hpos)
  · rw [← hfullEq]; exact hfull1
  · rw [← hfullEq]; exact hfull2
  · intro jτ hjτ jθ hjθ
    rw [← hmulEq]
    exact hprod jτ hjτ jθ hjθ

end TwoScaleRun

/-! ## the component estimates as one entry point: the window, converted and normalised -/

section WindowEntry

omit [Nontrivial E] in
open Classical in
/-- **The entry point of branch (ii): a dividing window, converted to a chain hierarchy and
normalised to the unit ball.**

`Kakeya.ML2Inputs.DividingScalesOutput`'s right alternative hands a
`Kakeya.ML2Reduction.IsKatzTaoDividingWindow` on `𝒲.tubeUniform`.  This declaration performs
two jobs — extract the two window scales `θ = ρ_a`, `τ = ρ_b` together with
`δ ≤ τ ≤ θ ≤ 1`, and convert the uniform tube set to a `Tube.ChainCoverSystem` by
`Tube.GridCoverSystem.toChain` — and then, the parent-ball seam.

The three density clauses of the window are *not* restated: they are the fields
`coarse_maxDensity_le`, `middle_maxDensity_le` and `le_window_maxDensity`, and the estimate read
them directly off the hypothesis `hw`, at the scales this declaration names.  `τ ≤ δ^{εd} θ` is
the field `scale_sep`, likewise unchanged.

`hlog : 2 ⌈log log 1/δ⌉ ≤ log (1/δ)` is the *only* new side condition, and it is what forces
`τ ≤ 1/4` (`Kakeya.ML2Core.gridScale_le_quarter`, using `a < b` so that `1 ≤ b`).  It is
eventually true (`Kakeya.ML2Core.exists_threshold_two_mul_ssfGridLen_le_log`), so a consumer
working under `∀ᶠ δ in 𝓝[>] 0` gets it for free. -/
theorem exists_windowSeam :
    ∃ M : ℕ, 0 < M ∧
      ∀ {δ Cu : NNReal} {κ : Type u} {s : Finset κ} {V : κ → ShadedTube δ E}
        (𝒰 : Tube.UniformTubeSet s (fun i => (V i).toTube) (ssfGridLen δ) Cu)
        {Cstar : ENNReal} {η : ℕ → ℝ} {εd : ℝ} {N a b m : ℕ},
        0 < δ → δ ≤ 1 → 2 * (ssfGridLen δ : ℝ) ≤ Real.log (1 / (δ : ℝ)) →
        ML2Reduction.IsKatzTaoDividingWindow 𝒰 Cstar η εd N a b m →
        (∀ i ∈ s, (V i).carrier ⊆ Metric.closedBall (0 : E) 1) →
        ∃ (v : E) (t₁ : Finset κ),
          t₁ ⊆ ML2Reduction.activeNodes 𝒰.cover.toChain b ∧
          (∀ j ∈ t₁,
            ((𝒰.cover.tube b j).translate v).carrier ⊆ Metric.closedBall (0 : E) 1) ∧
          (∀ i ∈ ({i ∈ s | 𝒰.cover.assign b i ∈ t₁} : Finset κ),
            ((V i).translate v).carrier ⊆ Metric.closedBall (0 : E) 1) ∧
          (s.card : NNReal) ≤ (M : NNReal) * Cu * Cu
            * (({i ∈ s | 𝒰.cover.assign b i ∈ t₁} : Finset κ).card : NNReal) ∧
          δ ≤ gridScale δ (ssfGridLen δ) b ∧
          gridScale δ (ssfGridLen δ) b ≤ gridScale δ (ssfGridLen δ) a ∧
          gridScale δ (ssfGridLen δ) a ≤ 1 := by
  classical
  obtain ⟨M, hM0, hseam⟩ := exists_parentSeam (E := E)
  refine ⟨M, hM0, ?_⟩
  intro δ Cu κ s V 𝒰 Cstar η εd N a b m hδ0 hδ1 hlog hw hball
  obtain ⟨hδτ, hτθ, hθ1⟩ := window_scales hδ0 hδ1 hw
  have hb1 : 1 ≤ b := Nat.one_le_of_lt (Nat.lt_of_le_of_lt (Nat.zero_le a) hw.coarse_lt_fine)
  have hτ4 : ((gridScale δ (ssfGridLen δ) b : NNReal) : ℝ) ≤ 1 / 4 :=
    gridScale_le_quarter hδ0 hδ1 hb1 hw.fine_le_gridLen hlog
  obtain ⟨v, t₁, ht₁, hballt, hballs, hcard⟩ :=
    hseam 𝒰.cover.toChain hw.fine_le_gridLen hτ4
      (𝒰.card_class_le b hw.fine_le_gridLen) (𝒰.le_card_class b hw.fine_le_gridLen) hball
  exact ⟨v, t₁, ht₁, hballt, hballs, hcard, hδτ, hτθ, hθ1⟩

end WindowEntry

/-! ## The three rows composed: a compatibility -/

open Classical in
/-- **compatibility: the component estimates compose, and the split they produce is non-degenerate.**

From a dividing window on a uniform hierarchy whose leaves lie in `B₁`, carrying the pointwise
density invariant GC-P1 hands out and any positive shaded mass, this produces the translation, the
retained node set, the two retained families of the two-scale split, **their nonemptiness**, and
the leaf-cardinality retention.

Its only purpose is that the compiler adjudicate the three interfaces:
`Kakeya.ML2Core.exists_windowSeam`'s output is *exactly*
`Kakeya.ML2Core.exists_spineTwoScale_ofChain_translated`'s hypothesis block, and
`Kakeya.ML2Core.sum_shade_le_of_node_subfamily` is what carries the mass positivity across the
seam's discard — which is the step §6 D2 says a cardinality-only reduction cannot take.  Any drift
in any of the three statements breaks this declaration. -/
theorem exists_windowSplit_nonempty :
    ∃ M : ℕ, 0 < M ∧
      ∀ {δ Cu lam : NNReal} {κ : Type u} {s : Finset κ} {V : κ → ShadedTube δ E}
        (𝒰 : Tube.UniformTubeSet s (fun i => (V i).toTube) (ssfGridLen δ) Cu)
        {Cstar : ENNReal} {η : ℕ → ℝ} {εd : ℝ} {N a b m : ℕ},
        0 < δ → δ ≤ 1 → 0 < lam →
        2 * (ssfGridLen δ : ℝ) ≤ Real.log (1 / (δ : ℝ)) →
        ML2Reduction.IsKatzTaoDividingWindow 𝒰 Cstar η εd N a b m →
        (∀ i ∈ s, (V i).carrier ⊆ Metric.closedBall (0 : E) 1) →
        ML2Shaded.HasDenseShading lam s (fun i => (V i).toShadedBody) →
        0 < ∑ i ∈ s, volume (V i).shade →
        ∃ (v : E) (t₁ tτ' tθ' : Finset κ),
          t₁ ⊆ ML2Reduction.activeNodes 𝒰.cover.toChain b ∧
          (∀ j ∈ t₁,
            ((𝒰.cover.tube b j).translate v).carrier ⊆ Metric.closedBall (0 : E) 1) ∧
          tτ' ⊆ t₁ ∧
          tθ' ⊆ 𝒰.cover.indexSet a ∧
          tτ'.Nonempty ∧ tθ'.Nonempty ∧
          (s.card : NNReal) ≤ (M : NNReal) * Cu * Cu
            * (({i ∈ s | 𝒰.cover.assign b i ∈ t₁} : Finset κ).card : NNReal) := by
  classical
  obtain ⟨M, hM0, hwin⟩ := exists_windowSeam (E := E)
  refine ⟨M, hM0, ?_⟩
  intro δ Cu lam κ s V 𝒰 Cstar η εd N a b m hδ0 hδ1 hlam hlog hw hball hdense hmass
  obtain ⟨v, t₁, ht₁, hballt, hballs, hcard, hδτ, hτθ, hθ1⟩ :=
    hwin 𝒰 hδ0 hδ1 hlog hw hball
  set s₁ : Finset κ := {i ∈ s | 𝒰.cover.assign b i ∈ t₁} with hs₁
  have hs₁s : s₁ ⊆ s := Finset.filter_subset _ _
  -- mass positivity survives the discard, by the density invariant
  have hret := sum_shade_le_of_node_subfamily (E := E) hδ1 hs₁s hdense hcard
  have hc0 : ((Tube.le_volume.c (Module.finrank ℝ E) : NNReal) : ENNReal) ≠ 0 := by
    simpa using (Tube.le_volume.c_pos (Module.finrank ℝ E)).ne'
  have hlam0 : ((lam : NNReal) : ENNReal) ≠ 0 := by simpa using hlam.ne'
  have hlhs : (0 : ENNReal) < (lam : ENNReal)
      * (Tube.le_volume.c (Module.finrank ℝ E) : ENNReal) * ∑ i ∈ s, volume (V i).shade :=
    ENNReal.mul_pos (ENNReal.mul_pos hlam0 hc0).ne' hmass.ne'
  have hrhs : (0 : ENNReal) < ((M : NNReal) * Cu * Cu : NNReal)
      * (Tube.volume_le.C (Module.finrank ℝ E) : ENNReal) * ∑ i ∈ s₁, volume (V i).shade :=
    lt_of_lt_of_le hlhs hret
  have hmass₁ : (0 : ENNReal) < ∑ i ∈ s₁, volume (V i).shade := by
    rw [pos_iff_ne_zero]
    intro h
    rw [h] at hrhs
    simp at hrhs
  -- and the split runs
  obtain ⟨tτ', htτ', tθ', htθ', _Yτ, _Yτ', _Yθ, _Y', _hcardτ, _h1, _h2, _h3, _h4, _h5, _h6,
      hne, _h7, _h8, _h9, _h10, _h11⟩ :=
    exists_spineTwoScale_ofChain_translated (E := E) hδ0 𝒰.cover.toChain
      hw.coarse_lt_fine.le (le_trans hw.coarse_lt_fine.le hw.fine_le_gridLen)
      hw.fine_le_gridLen hδτ hτθ hθ1 v ht₁ hballt hballs
  obtain ⟨hτne, hθne⟩ := hne hmass₁
  exact ⟨v, t₁, tτ', tθ', ht₁, hballt, htτ', htθ', hτne, hθne, hcard⟩

end Kakeya.ML2Core
