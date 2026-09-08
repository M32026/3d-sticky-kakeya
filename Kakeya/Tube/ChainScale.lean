/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Mathlib.Analysis.EuclideanNet
public import Kakeya.Tube.Nets
public import Mathlib
public import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Fattened chains of scales and prefix offsets

The two constructions GWZ Lemma 7.5 runs on a chain of scales: fattening a chain so consecutive
scales leave room for a translate, and the prefix-offset chain of accumulated translations.
-/

@[expose] public section


open MeasureTheory Real

open scoped ENNReal NNReal

namespace Tube

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E] [MeasurableSpace E] [BorelSpace E] [ProperSpace E]

/-- **Fattened chain scale.**  Given a scale chain `ρ` from `ρ 0 = 1` down to `ρ (Fin.last M) = δ`
with the standard quarter gap `4 * ρ_succ ≤ ρ_cs`, the fattened chain `σ k = 3 * ρ k` — kept sharp
at the leaf level — is again antitone with the same quarter gap, and its coarsest value `3` lies in
`[1, 4]`.  The factor `3` is forced: a covering tube absorbs a prefix offset of comparable norm. -/
theorem exists_fattened_chain_scale
    {δ : NNReal} {M : ℕ} (hM : 1 ≤ M) (ρ : Fin (M + 1) → NNReal)
    (hρ_0 : ρ 0 = 1) (hρ_M : ρ (Fin.last M) = δ) (hρ_anti : Antitone ρ)
    (hρ_quarter : ∀ m : Fin M, 4 * (ρ m.succ : ℝ) ≤ (ρ m.castSucc : ℝ)) :
    ∃ σ : Fin (M + 1) → NNReal,
      σ (Fin.last M) = δ ∧
      1 ≤ σ 0 ∧ σ 0 ≤ 4 ∧
      Antitone σ ∧
      (∀ m : Fin M, 4 * (σ m.succ : ℝ) ≤ (σ m.castSucc : ℝ)) ∧
      (∀ m : Fin M, (σ m.castSucc : ℝ) = 3 * (ρ m.castSucc : ℝ)) ∧
      (∀ k : Fin (M + 1), ρ k ≤ σ k) ∧
      (∀ k : Fin (M + 1), σ k ≤ 4) ∧
      (∀ k : Fin (M + 1), (σ k : ℝ) ≤ 3 * (ρ k : ℝ)) := by
  have hMpos : 0 < M := by omega
  set σ : Fin (M + 1) → NNReal := Fin.lastCases δ (fun m => 3 * ρ m.castSucc) with hσ_def
  have hσL : σ (Fin.last M) = δ := by
    simp [σ]
  have hσC : ∀ m : Fin M, σ m.castSucc = 3 * ρ m.castSucc := by
    intro m; simp [σ]
  let z0 : Fin M := ⟨0, hMpos⟩
  have hz0_castSucc_eq_zero : (z0.castSucc : Fin (M + 1)) = (0 : Fin (M + 1)) := by
    ext; simp [z0]
  have h_one_le_σ0 : 1 ≤ σ 0 := by
    rw [← hz0_castSucc_eq_zero, hσC z0]
    have : ρ z0.castSucc = 1 := by
      rw [hz0_castSucc_eq_zero, hρ_0]
    rw [this]; norm_num
  have h_σ0_le_4 : σ 0 ≤ 4 := by
    rw [← hz0_castSucc_eq_zero, hσC z0]
    have : ρ z0.castSucc = 1 := by
      rw [hz0_castSucc_eq_zero, hρ_0]
    rw [this]; norm_num
  have hδ_le_1 : δ ≤ 1 := by
    calc
      δ = ρ (Fin.last M) := by symm; exact hρ_M
      _ ≤ ρ 0 := hρ_anti (Fin.zero_le _)
      _ = 1 := hρ_0
  have hρ_le_σ : ∀ k : Fin (M + 1), ρ k ≤ σ k := by
    intro k; cases k using Fin.lastCases with
    | last => rw [hσL, hρ_M]
    | cast m =>
        have h_nonneg : (0 : NNReal) ≤ ρ m.castSucc := NNReal.zero_le_coe
        calc
          ρ m.castSucc = 1 * ρ m.castSucc := by simp
          _ ≤ 3 * ρ m.castSucc :=
            mul_le_mul_of_nonneg_right (by norm_num : (1 : NNReal) ≤ 3) h_nonneg
          _ = σ m.castSucc := by symm; exact hσC m
  have hσR_le_3ρ : ∀ k : Fin (M + 1), (σ k : ℝ) ≤ 3 * (ρ k : ℝ) := by
    intro k; cases k using Fin.lastCases with
    | last =>
        rw [hσL, hρ_M]
        nlinarith [NNReal.coe_nonneg δ]
    | cast m =>
        have h_eq : (σ m.castSucc : ℝ) = 3 * (ρ m.castSucc : ℝ) := by exact_mod_cast hσC m
        rw [h_eq]
  have hρ_cs_le_1 : ∀ m : Fin M, ρ m.castSucc ≤ 1 := by
    intro m
    calc
      ρ m.castSucc ≤ ρ 0 := hρ_anti (Fin.zero_le _)
      _ = 1 := hρ_0
  have hσ_anti : Antitone σ := by
    intro j k hjk
    apply NNReal.coe_le_coe.mp
    cases j using Fin.lastCases with
    | last =>
        cases k using Fin.lastCases with
        | last => rfl
        | cast k' =>
            exfalso
            have h_val : (Fin.last M : ℕ) ≤ (k'.castSucc : ℕ) := by exact_mod_cast hjk
            simp at h_val
            have hk'_lt_M : (k' : ℕ) < M := k'.2
            omega
    | cast j' =>
        cases k using Fin.lastCases with
        | last =>
            rw [hσL, hσC j']
            have hδ_le_ρ : (δ : ℝ) ≤ (ρ j'.castSucc : ℝ) := by
              calc
                (δ : ℝ) = (ρ (Fin.last M) : ℝ) := by exact_mod_cast hρ_M.symm
                _ ≤ (ρ j'.castSucc : ℝ) := by exact_mod_cast hρ_anti (Fin.le_last _)
            calc
              (δ : ℝ) ≤ (ρ j'.castSucc : ℝ) := hδ_le_ρ
              _ ≤ 3 * (ρ j'.castSucc : ℝ) := by nlinarith [NNReal.coe_nonneg (ρ j'.castSucc)]
        | cast k' =>
            rw [hσC j', hσC k']
            have h' : j' ≤ k' := by
              rw [Fin.le_def]
              have h_coe : (j'.castSucc : ℕ) ≤ (k'.castSucc : ℕ) := by exact_mod_cast hjk
              simpa using h_coe
            have hρ_ineq : (ρ k'.castSucc : ℝ) ≤ (ρ j'.castSucc : ℝ) := by
              exact_mod_cast hρ_anti h'
            have h_nonneg_3 : (0 : ℝ) ≤ 3 := by norm_num
            exact mul_le_mul_of_nonneg_left hρ_ineq h_nonneg_3
  have hσ_gap : ∀ m : Fin M, 4 * (σ m.succ : ℝ) ≤ (σ m.castSucc : ℝ) := by
    intro m
    have hσ_cs_r : (σ m.castSucc : ℝ) = 3 * (ρ m.castSucc : ℝ) := by exact_mod_cast hσC m
    rw [hσ_cs_r]
    rcases Fin.eq_castSucc_or_eq_last m.succ with ⟨j, hj⟩ | hj
    · rw [hj]
      have hσ_succ_r : (σ j.castSucc : ℝ) = 3 * (ρ j.castSucc : ℝ) := by exact_mod_cast hσC j
      rw [hσ_succ_r]
      have hq : 4 * (ρ m.succ : ℝ) ≤ (ρ m.castSucc : ℝ) := hρ_quarter m
      have : (ρ m.succ : ℝ) = (ρ j.castSucc : ℝ) := by simp [hj]
      rw [this] at hq
      nlinarith
    · rw [hj, hσL]
      have hq : 4 * (ρ m.succ : ℝ) ≤ (ρ m.castSucc : ℝ) := hρ_quarter m
      have hρ_succ_eq_δ : (ρ m.succ : ℝ) = (δ : ℝ) := by
        calc
          (ρ m.succ : ℝ) = (ρ (Fin.last M) : ℝ) := by rw [hj]
          _ = (δ : ℝ) := by exact_mod_cast hρ_M
      rw [hρ_succ_eq_δ] at hq
      nlinarith
  have hσ_cs_r_eq : ∀ m : Fin M, (σ m.castSucc : ℝ) = 3 * (ρ m.castSucc : ℝ) := by
    intro m; exact_mod_cast hσC m
  have hσ_le_4 : ∀ k : Fin (M + 1), σ k ≤ 4 := by
    intro k; cases k using Fin.lastCases with
    | last =>
        calc
          σ (Fin.last M) = δ := hσL
          _ ≤ 1 := hδ_le_1
          _ ≤ 4 := by norm_num
    | cast m =>
        calc
          σ m.castSucc = 3 * ρ m.castSucc := hσC m
          _ ≤ 3 * 1 := mul_le_mul_of_nonneg_left (hρ_cs_le_1 m) (by norm_num : (0 : NNReal) ≤ 3)
          _ = 3 := by norm_num
          _ ≤ 4 := by norm_num
  refine ⟨σ, hσL, h_one_le_σ0, h_σ0_le_4, hσ_anti, hσ_gap, hσ_cs_r_eq, hρ_le_σ, hσ_le_4, hσR_le_3ρ⟩

open Classical in
omit [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- **Prefix-offset chain projection.**  A hierarchy of nodes `nodes k ⊆ ι × E`, whose level-`k+1`
nodes come from the level-`k` ones by picking a child index and adding a per-scale offset, carries a
functional parent map `proj` under which the fattened translated parent tubes are nested.  This is
GWZ Lemma 7.5, eq. (52); nesting holds because each offset has norm at most the coarser scale. -/
theorem exists_prefix_offset_chain
    {ι : Type*} {M : ℕ} {ρ σ : Fin (M + 1) → NNReal}
    (hσ_gap : ∀ m : Fin M, 4 * (σ m.succ : ℝ) ≤ (σ m.castSucc : ℝ))
    (hσ_cs : ∀ m : Fin M, (σ m.castSucc : ℝ) = 3 * (ρ m.castSucc : ℝ))
    (parentTube : ∀ k : Fin (M + 1), ι → Tube (ρ k) E)
    (nodes : Fin (M + 1) → Finset (ι × E))
    (children : Fin M → ι → Finset (ι × E))
    (hnodes_succ : ∀ m : Fin M, nodes m.succ
      = (nodes m.castSucc).biUnion (fun p : ι × E =>
          (children m p.1).image (fun pair : ι × E => (pair.1, p.2 + pair.2))))
    (hchild : ∀ m : Fin M, ∀ p ∈ nodes m.castSucc, ∀ pair ∈ children m p.1,
      (parentTube m.succ pair.1).toConvexSpaceBody
          ≤ (parentTube m.castSucc p.1).toConvexSpaceBody
        ∧ ‖pair.2‖ ≤ (ρ m.castSucc : ℝ)) :
    ∃ proj : Fin M → (ι × E) → (ι × E),
      (∀ m : Fin M, ∀ q ∈ nodes m.succ, proj m q ∈ nodes m.castSucc) ∧
      (∀ m : Fin M, ∀ q ∈ nodes m.succ,
        ∃ pair ∈ children m (proj m q).1, q = (pair.1, (proj m q).2 + pair.2)) ∧
      (∀ m : Fin M, ∀ q ∈ nodes m.succ,
        (((parentTube m.succ q.1).rescale (σ m.succ)).translate q.2).toConvexSpaceBody
          ≤ (((parentTube m.castSucc (proj m q).1).rescale (σ m.castSucc)).translate
              (proj m q).2).toConvexSpaceBody) := by
  classical
  have haux : ∀ m : Fin M, ∀ q ∈ nodes m.succ,
      ∃ p ∈ nodes m.castSucc, ∃ pair ∈ children m p.1, q = (pair.1, p.2 + pair.2) := by
    intro m q hq
    rw [hnodes_succ m, Finset.mem_biUnion] at hq
    obtain ⟨p, hp, hq_img⟩ := hq
    obtain ⟨pair, hpair, hpair_eq⟩ := Finset.mem_image.mp hq_img
    exact ⟨p, hp, pair, hpair, hpair_eq.symm⟩
  set proj : Fin M → (ι × E) → (ι × E) :=
    fun m q => if hq : q ∈ nodes m.succ then (haux m q hq).choose else q
    with hproj_def
  refine ⟨proj, ?_, ?_, ?_⟩
  · intro m q hq
    dsimp [proj]
    rw [dif_pos hq]
    exact (haux m q hq).choose_spec.1
  · intro m q hq
    dsimp [proj] at *
    rw [dif_pos hq] at *
    have hspec := (haux m q hq).choose_spec.2
    obtain ⟨pair, hpair, hq_eq⟩ := hspec
    refine ⟨pair, hpair, hq_eq⟩
  · intro m q hq
    dsimp [proj]
    rw [dif_pos hq]
    set p := (haux m q hq).choose with hp_def
    have hp_mem : p ∈ nodes m.castSucc := (haux m q hq).choose_spec.1
    have hspec := (haux m q hq).choose_spec.2
    obtain ⟨pair, hpair, hq_eq⟩ := hspec
    have hchild_spec := hchild m p hp_mem pair hpair
    obtain ⟨hbody, hnorm⟩ := hchild_spec
    have hnonneg_ρ : 0 ≤ (ρ m.castSucc : ℝ) := NNReal.coe_nonneg _
    rw [hq_eq]
    have hLHS_eq :
        (((parentTube m.succ pair.1).rescale (σ m.succ)).translate
            (p.2 + pair.2)).toConvexSpaceBody
          = ((((parentTube m.succ pair.1).rescale (σ m.succ)).translate pair.2).translate
              p.2).toConvexSpaceBody := by
      calc
        (((parentTube m.succ pair.1).rescale (σ m.succ)).translate
              (p.2 + pair.2)).toConvexSpaceBody
            = ConvexSpaceBody.translate
                ((parentTube m.succ pair.1).rescale (σ m.succ)).toConvexSpaceBody
                (p.2 + pair.2) := rfl
        _ = ConvexSpaceBody.translate
              (ConvexSpaceBody.translate
                ((parentTube m.succ pair.1).rescale (σ m.succ)).toConvexSpaceBody pair.2) p.2 := by
          rw [ConvexSpaceBody.translate_translate, add_comm]
        _ = ((((parentTube m.succ pair.1).rescale (σ m.succ)).translate pair.2).translate
              p.2).toConvexSpaceBody := rfl
    rw [hLHS_eq]
    have hinner :
      (((parentTube m.succ pair.1).rescale (σ m.succ)).translate pair.2).toConvexSpaceBody
        ≤ ((parentTube m.castSucc p.1).rescale (σ m.castSucc)).toConvexSpaceBody := by
      have hbudget : (ρ m.castSucc : ℝ) + (σ m.succ : ℝ) + (ρ m.castSucc : ℝ)
          ≤ (σ m.castSucc : ℝ) := by
        rw [hσ_cs m]
        have hgap : 4 * (σ m.succ : ℝ) ≤ (σ m.castSucc : ℝ) := hσ_gap m
        rw [hσ_cs m] at hgap
        nlinarith
      refine translate_rescale_le_rescale_of_body_le
        (parentTube m.succ pair.1) (parentTube m.castSucc p.1) hbody pair.2
        hnonneg_ρ hnorm hbudget
    have h_translate : ConvexSpaceBody.translate
        (((parentTube m.succ pair.1).rescale (σ m.succ)).translate pair.2).toConvexSpaceBody p.2 ≤
        ConvexSpaceBody.translate
          ((parentTube m.castSucc p.1).rescale (σ m.castSucc)).toConvexSpaceBody p.2 :=
      translate_le_translate p.2 hinner
    simpa [Tube.translate] using h_translate

omit [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- **Localization of a fattened, translated tube.**  If `X` sits in `B_a`, fattening it from `ρ` to
`r ≤ ρ + c` and translating by a vector of norm at most `b` keeps it inside `B_{a+c+b}`.  Used to
localize the prefix-offset chain of GWZ Lemma 7.5, whose level-`k` covering tube is a parent tube in
`B_4` fattened from `ρ k` to `3 * ρ k` and translated by a prefix offset of norm at most `M`. -/
theorem rescale_translate_carrier_subset_closedBall
    {ρ r : NNReal} (X : Tube ρ E) {a b c : ℝ}
    (hX : X.carrier ⊆ Metric.closedBall (0 : E) a)
    (hc : 0 ≤ c) (hr : (r : ℝ) ≤ (ρ : ℝ) + c) (v : E) (hv : ‖v‖ ≤ b) :
    ((X.rescale r).translate v).carrier ⊆ Metric.closedBall (0 : E) (a + c + b) := by
  have htrans_carrier : ((X.rescale r).translate v).carrier = (v + ·) '' (X.rescale r).carrier := by
    unfold Tube.translate; rfl
  rw [htrans_carrier]
  have hYball : (X.rescale r).carrier ⊆ Metric.closedBall (0 : E) (a + c) := by
    by_cases hρr : (ρ : ℝ) ≤ (r : ℝ)
    · have h_nonneg_diff : 0 ≤ (r : ℝ) - (ρ : ℝ) := by linarith
      have h_sub_eq : (X.rescale r).carrier = Metric.cthickening ((r : ℝ) - (ρ : ℝ)) X.carrier := by
        have hρr' : ρ ≤ r := by exact_mod_cast hρr
        have hbody_eq := X.toConvexBody_cthickening_sub hρr'
        calc
          (X.rescale r).carrier = ((X.rescale r).toConvexSpaceBody : Set E) := rfl
          _ = (X.toConvexSpaceBody.cthickening ((r : ℝ) - (ρ : ℝ)) : Set E) := by rw [hbody_eq]
          _ = Metric.cthickening ((r : ℝ) - (ρ : ℝ)) X.carrier := rfl
      rw [h_sub_eq]
      have ha_nonneg : 0 ≤ a := by
        have hpt : X.nonempty'.some ∈ X.carrier := X.nonempty'.choose_spec
        have hball : X.nonempty'.some ∈ Metric.closedBall (0 : E) a := hX hpt
        have : dist (X.nonempty'.some) (0 : E) ≤ a := by
          rw [Metric.mem_closedBall] at hball
          exact hball
        exact le_trans dist_nonneg this
      calc
        Metric.cthickening ((r : ℝ) - (ρ : ℝ)) X.carrier
            ⊆ Metric.cthickening ((r : ℝ) - (ρ : ℝ)) (Metric.closedBall (0 : E) a) :=
          Metric.cthickening_subset_of_subset ((r : ℝ) - (ρ : ℝ)) hX
        _ = Metric.closedBall (0 : E) (((r : ℝ) - (ρ : ℝ)) + a) := by
          rw [cthickening_closedBall h_nonneg_diff ha_nonneg]
        _ ⊆ Metric.closedBall (0 : E) (c + a) :=
          Metric.closedBall_subset_closedBall (by
            have : (r : ℝ) - (ρ : ℝ) ≤ c := by linarith
            nlinarith)
        _ = Metric.closedBall (0 : E) (a + c) := by simp [add_comm]
    · push Not at hρr
      have hrρ : r ≤ ρ := by exact_mod_cast hρr.le
      have h_carrier_sub : (X.rescale r).carrier ⊆ X.carrier := by
        rw [X.carrier_eq_cthickening, (X.rescale r).carrier_eq_cthickening]
        exact Metric.cthickening_mono (by exact_mod_cast hrρ) (segment ℝ X.x X.y)
      calc
        (X.rescale r).carrier ⊆ X.carrier := h_carrier_sub
        _ ⊆ Metric.closedBall (0 : E) a := hX
        _ ⊆ Metric.closedBall (0 : E) (a + c) :=
          Metric.closedBall_subset_closedBall (by nlinarith)
  calc
    (v + ·) '' (X.rescale r).carrier ⊆ (v + ·) '' Metric.closedBall (0 : E) (a + c) := by
      intro z hz
      rcases hz with ⟨y, hy, rfl⟩
      exact (Set.mem_image (v + ·) (Metric.closedBall (0 : E) (a + c)) (v + y)).mpr
        ⟨y, hYball hy, rfl⟩
    _ ⊆ Metric.closedBall (0 : E) (a + c + b) := by
      intro z hz
      rcases hz with ⟨y, hy, rfl⟩
      rw [mem_closedBall_zero_iff]
      calc
        ‖v + y‖ ≤ ‖v‖ + ‖y‖ := norm_add_le _ _
        _ ≤ b + (a + c) := add_le_add hv (by
          rw [mem_closedBall_zero_iff] at hy
          exact hy)
        _ = a + c + b := by ring

end Tube
