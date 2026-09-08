/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.BallGeneralGlue
public import Kakeya.DimensionThree.MainLemma2.BallCoreOfCover
public import Kakeya.DimensionThree.MainLemma2.EDConstants

/-!
# The general-`(a, b)` branch: the mass bookkeeping of GWZ §9.3 steps 5–7

General-branch steps G5. Nothing here changes a
existing statement: every declaration is new.
-/

@[expose] public section

namespace Kakeya.VeryNotSticky

open MeasureTheory Metric Set ShadedBody
open scoped NNReal ENNReal

universe u

/-! ### `ϱ ≤ 1/21` is a theorem of the existing parameter set -/

/-- **The `w₁` budget's only input is a consequence of `CaseParams`** (obligation `G4-O2`).
`Kakeya.VNSUniform.CaseParams.slabBias` reads `2 ^ 20 * ϱ < exscal` and
`Kakeya.VNSUniform.CaseParams.scale` reads `exscal < 1/2`, so `ϱ < 2 ^ (-21) < 1/21`. With
`Kakeya.VeryNotSticky.dimsConstant_eq_left_of_lemma92` this discharges the `hϱ21` binder that
 row G5 and  item 2 both left open.

The name begins with an ASCII letter deliberately: `cli_tools/_lean/sourcetools.py`'s `DECL_RE`
matches names by `[A-Za-z_][\w']*`, so a declaration called `ϱ_le_…` is enumerated with
`name = None` and is **silently dropped** from `lean.py axioms FILE` (measured: 21 of 22
declarations checked, `not_audited: []`). -/
theorem caseParams_ϱ_le_one_div_21 {β ζ exscal ϱ η τ τ' : ℝ}
    (params : CaseParams β ζ exscal ϱ η τ τ') : ϱ ≤ 1 / 21 := by
  have h1 := params.slabBias
  have h2 := params.scale
  rw [parameterSeparationConstant] at h1
  have hnum : (2 : ℝ) ^ 20 = 1048576 := by norm_num
  rw [hnum] at h1
  linarith

/-- `dimsConstant` is `C₀` for every configuration whose parameters are admissible: the
`hϱ21` binder of `Kakeya.VeryNotSticky.dimsConstant_eq_left_of_lemma92` is free. -/
theorem dimsConstant_eq_left_of_caseParams {C₀ : NNReal} (h4 : 4 ≤ C₀)
    {β ζ exscal ϱ η τ τ' : ℝ} (params : CaseParams β ζ exscal ϱ η τ τ') :
    dimsConstant C₀ (3 / 2) (lemma92Constant ϱ) = C₀ :=
  dimsConstant_eq_left_of_lemma92 h4 (caseParams_ϱ_le_one_div_21 params)

/-! ### The partition mass identity -/

/-- **The partition mass identity.** The pieces of a pairwise disjoint measurable family that
covers `F` split `volume F` additively; no measurability of `F` is needed. -/
theorem sum_volume_inter_pieces {E : Type*} [MeasureSpace E] {bι : Type*}
    (bs : Finset bι) (P : bι → Set E)
    (hdisj : (bs : Set bι).PairwiseDisjoint P) (hPmeas : ∀ B ∈ bs, MeasurableSet (P B))
    {F : Set E} (hF : F ⊆ ⋃ B ∈ bs, P B) :
    ∑ B ∈ bs, volume (F ∩ P B) = volume F := by
  classical
  have hres_sum : ∀ s ⊆ bs, (volume : Measure E).restrict (⋃ B ∈ s, P B) =
      ∑ B ∈ s, (volume : Measure E).restrict (P B) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert b t hbt ih =>
        intro hs
        have hsubt : t ⊆ bs := fun x hx => hs (by simp [hx])
        have hbdisj : Disjoint (P b) (⋃ B ∈ t, P B) := by
          rw [Set.disjoint_iUnion₂_right]
          exact fun B hB => hdisj (hs (by simp)) (hsubt hB) fun h => hbt (h ▸ hB)
        rw [Finset.set_biUnion_insert, Finset.sum_insert hbt, ← ih hsubt,
          MeasureTheory.Measure.restrict_union hbdisj
            (Finset.measurableSet_biUnion t fun B hB => hPmeas B (hsubt hB))]
  have hbsmeas : MeasurableSet (⋃ B ∈ bs, P B) := Finset.measurableSet_biUnion bs hPmeas
  calc ∑ B ∈ bs, volume (F ∩ P B)
      = (∑ B ∈ bs, (volume : Measure E).restrict (P B) : Measure E) F := by
          rw [MeasureTheory.Measure.finsetSum_apply]
          exact Finset.sum_congr rfl fun B hB =>
            (MeasureTheory.Measure.restrict_apply' (hPmeas B hB)).symm
    _ = volume F := by
          rw [← hres_sum bs Finset.Subset.rfl,
            MeasureTheory.Measure.restrict_apply' hbsmeas,
            Set.inter_eq_self_of_subset_left hF]

/-! ### The configuration's aggregate fullness, cleared of division -/

/-- The total carrier mass of a configuration is finite. -/
theorem sum_volume_carrier_ne_top (cfg : VeryNotSticky.{u}) :
    ∑ i ∈ cfg.s, volume (cfg.T i).carrier ≠ ⊤ := by
  refine (ENNReal.sum_lt_top.2 fun i hi => ?_).ne
  exact lt_of_le_of_lt (measure_mono (cfg.contained i hi)) measure_closedBall_lt_top

/-- **`cfg.fullness_ge` cleared of division**: `δ^{2η} ∑|T| ≤ ∑|Y(T)|`. -/
theorem delta_pow_mul_sum_carrier_le (cfg : VeryNotSticky.{u}) :
    (cfg.δ : ENNReal) ^ (2 * cfg.η) * ∑ i ∈ cfg.s, volume (cfg.T i).carrier ≤
      ∑ i ∈ cfg.s, volume (cfg.T i).shade := by
  by_cases hz : ∑ i ∈ cfg.s, volume (cfg.T i).carrier = 0
  · simp [hz]
  have h := cfg.fullness_ge
  have hne : ∑ i ∈ cfg.s, volume ((cfg.T i).toShadedBody).carrier ≠ ⊤ :=
    sum_volume_carrier_ne_top cfg
  have hz' : ∑ i ∈ cfg.s, volume ((cfg.T i).toShadedBody).carrier ≠ 0 := hz
  have hc : ((cfg.δ ^ (2 * cfg.η) : NNReal) : ENNReal) ≤
      ShadedBody.fullness' cfg.s (fun i ↦ (cfg.T i).toShadedBody) := by
    rw [← ShadedBody.coe_fullness]
    exact ENNReal.coe_le_coe.2 h
  rw [ShadedBody.fullness', ENNReal.le_div_iff_mul_le (Or.inl hz') (Or.inl hne)] at hc
  rwa [ENNReal.coe_rpow_of_ne_zero (ne_of_gt cfg.hδ)] at hc

/-! ### The family cardinality bound `#𝕋 ≲ δ^{-2-η}` -/

/-- **The family of a configuration has at most `∼ δ^{-2-η}` members.** -/
theorem card_mul_le_of_maxDensity (cfg : VeryNotSticky.{u}) :
    ((cfg.s.card : ℕ) : ENNReal) * (((Tube.le_volume.c 3 : NNReal) : ENNReal) *
        (cfg.δ : ENNReal) ^ (2 : ℕ)) ≤
      (cfg.δ : ENNReal) ^ (-cfg.η) *
        volume (ConvexSpaceBody.closedUnitBall (E := EuclideanSpace ℝ (Fin 3))).carrier := by
  have hfr : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := finrank_euclideanSpace_fin
  have hlow : ((cfg.s.card : ℕ) : ENNReal) * (((Tube.le_volume.c 3 : NNReal) : ENNReal) *
      (cfg.δ : ENNReal) ^ (2 : ℕ)) ≤ ∑ i ∈ cfg.s, volume (cfg.T i).carrier := by
    have h := Finset.card_nsmul_le_sum cfg.s (fun i => volume (cfg.T i).carrier)
      (((Tube.le_volume.c 3 : NNReal) : ENNReal) * (cfg.δ : ENNReal) ^ (2 : ℕ))
      (fun i _ => by
        have h := Tube.le_volume (cfg.T i).toTube
        rwa [hfr] at h)
    rwa [nsmul_eq_mul] at h
  refine hlow.trans ?_
  have hle : ∀ i ∈ cfg.s, (cfg.T i).toConvexSpaceBody ≤
      ConvexSpaceBody.closedUnitBall (E := EuclideanSpace ℝ (Fin 3)) := by
    intro i hi
    exact cfg.contained i hi
  refine le_trans (sum_volume_le_maxDensity_mul_volume' hle) ?_
  gcongr
  exact cfg.maxDensity_le

/-! ### Reindexing the segments of the cover core by their parent tube -/

variable (cfg : VeryNotSticky.{u}) {bι : Type u}

open scoped Classical in
/-- The double sum over the balls and their capsule segments, reindexed by parent tube. -/
theorem sum_sum_segsOfCover (P : bι → Set (EuclideanSpace ℝ (Fin 3))) (bs : Finset bι)
    (f : cfg.ι × bι → ENNReal) :
    ∑ B ∈ bs, ∑ p ∈ segsOfCover cfg P B, f p
      = ∑ i ∈ cfg.s, ∑ B ∈ bs with ((cfg.T i).shade ∩ P B).Nonempty, f (i, B) := by
  classical
  have hstep : ∀ B : bι, ∑ p ∈ segsOfCover cfg P B, f p
      = ∑ i ∈ cfg.s with ((cfg.T i).shade ∩ P B).Nonempty, f (i, B) := by
    intro B
    rw [segsOfCover, Finset.sum_image (by intro a _ b _ h; exact (Prod.mk.injEq .. ▸ h).1)]
  simp only [hstep, Finset.sum_filter]
  exact Finset.sum_comm

open scoped Classical in
/-- **The shading of a capsule segment is exactly `Y(T) ∩ B̂`**: the extra intersection with
the capsule in `Kakeya.VeryNotSticky.segShadedBody` is vacuous on the pieces of the cover. -/
theorem segBodyOfCover_shade_eq {bs : Finset bι} {ctr : bι → EuclideanSpace ℝ (Fin 3)}
    {P : bι → Set (EuclideanSpace ℝ (Fin 3))} (hPmeas : ∀ B, MeasurableSet (P B))
    (hδr : 16 * (cfg.δ : ℝ) ≤ (cfg.r₁ : ℝ))
    (hPball16 : ∀ B ∈ bs, P B ⊆ ball (ctr B) ((cfg.r₁ : ℝ) / 16))
    {i : cfg.ι} {B : bι} (hB : B ∈ bs) :
    (segBodyOfCover cfg ctr P hPmeas (i, B)).shade = (cfg.T i).shade ∩ P B := by
  have hr₁pos : (0 : ℝ) < (cfg.r₁ : ℝ) := by exact_mod_cast NNReal.rpow_pos cfg.hδ
  have hL : (0 : ℝ) ≤ (cfg.r₁ : ℝ) / 4 := by positivity
  rw [segBodyOfCover_shade]
  refine Set.inter_eq_self_of_subset_left ?_
  intro x hx
  refine tube_inter_ball_subset_segCarrierSet (cfg.T i).toTube (ctr B)
    (ρ := (cfg.r₁ : ℝ) / 16) hL (by linarith) ⟨(cfg.T i).shade_subset hx.1, ?_⟩
  exact hPball16 B hB hx.2

open scoped Classical in
/-- The segments of a piece are indexed by a subfamily of `𝕋`: `#𝕋_B ≤ #𝕋`. This is the
uniformisation Lemma 9.2's ball-dependent loss `L 3 (#𝕋_B) (δ/r₁) ϱ` needs in order to become a
single `K` for `Kakeya.VeryNotSticky.tierCore`. -/
theorem card_segsOfCover_le (P : bι → Set (EuclideanSpace ℝ (Fin 3))) (B : bι) :
    (segsOfCover cfg P B).card ≤ cfg.s.card := by
  classical
  refine le_trans (Finset.card_image_le) ?_
  exact Finset.card_filter_le _ _

/-! ### The two mass bridges -/

open scoped Classical in
/-- **Bounded overlap of the capsules of one tube across the ball family.** The capsules
`T_B = T ∩ B̂` of a fixed tube `T` all lie inside `T` and no point lies in more than
`ballCoverConstant` of them, because each of them lies inside `ball (ctr B) r₁`. -/
theorem sum_volume_segCarrierSet_le
    (bs : Finset bι) (ctr : bι → EuclideanSpace ℝ (Fin 3))
    (P : bι → Set (EuclideanSpace ℝ (Fin 3)))
    (hδr : 16 * (cfg.δ : ℝ) ≤ (cfg.r₁ : ℝ))
    (hPball16 : ∀ B ∈ bs, P B ⊆ ball (ctr B) ((cfg.r₁ : ℝ) / 16))
    (hoverlap : ∀ (x : EuclideanSpace ℝ (Fin 3)) (t : Finset bι), t ⊆ bs →
      (∀ B ∈ t, x ∈ ball (ctr B) (cfg.r₁ : ℝ)) → t.card ≤ ballCoverConstant)
    (i : cfg.ι) :
    ∑ B ∈ bs with ((cfg.T i).shade ∩ P B).Nonempty,
        volume (segCarrierSet (cfg.T i).toTube (ctr B) ((cfg.r₁ : ℝ) / 4))
      ≤ (ballCoverConstant : ENNReal) * volume (cfg.T i).carrier := by
  classical
  have hr₁pos : (0 : ℝ) < (cfg.r₁ : ℝ) := by exact_mod_cast NNReal.rpow_pos cfg.hδ
  have hr₁1 : (cfg.r₁ : ℝ) ≤ 1 := r₁_le_one cfg
  have hL : (0 : ℝ) ≤ (cfg.r₁ : ℝ) / 4 := by positivity
  have hL1 : 2 * ((cfg.r₁ : ℝ) / 4) ≤ 1 := by linarith
  set t : Finset bι := bs.filter (fun B => ((cfg.T i).shade ∩ P B).Nonempty) with ht
  have htsub : t ⊆ bs := Finset.filter_subset _ _
  have hmeet : ∀ B ∈ t,
      ((cfg.T i).toTube.carrier ∩ ball (ctr B) ((cfg.r₁ : ℝ) / 16)).Nonempty := by
    intro B hB
    obtain ⟨hBbs, hne⟩ := Finset.mem_filter.1 hB
    obtain ⟨x, hxs, hxP⟩ := hne
    exact ⟨x, (cfg.T i).shade_subset hxs, hPball16 B hBbs hxP⟩
  have hball : ∀ B ∈ t, segCarrierSet (cfg.T i).toTube (ctr B) ((cfg.r₁ : ℝ) / 4) ⊆
      ball (ctr B) (cfg.r₁ : ℝ) := by
    intro B hB
    refine (segCarrierSet_subset_closedBall_ctr (cfg.T i).toTube (ctr B)
      (ρ := (cfg.r₁ : ℝ) / 16) (R := 3 * (cfg.r₁ : ℝ) / 4) hL (hmeet B hB)
      (by linarith)).trans ?_
    exact Metric.closedBall_subset_ball (by linarith)
  refine le_trans (MeasureTheory.sum_measure_le_mul_measure_of_card_le volume t
    (fun B => segCarrierSet (cfg.T i).toTube (ctr B) ((cfg.r₁ : ℝ) / 4))
    (fun B _ => (isClosed_segCarrierSet _ _ _).measurableSet)
    (F := (cfg.T i).toTube.carrier)
    (by rw [(cfg.T i).toTube.carrier_eq_cthickening]; exact isClosed_cthickening.measurableSet)
    (fun B _ => segCarrierSet_subset_tube _ _ hL hL1)
    (M := (ballCoverConstant : ENNReal)) ?_) le_rfl
  intro x _
  have hcard := hoverlap x (t.filter (fun B => x ∈ segCarrierSet (cfg.T i).toTube (ctr B)
      ((cfg.r₁ : ℝ) / 4)))
    ((Finset.filter_subset _ _).trans htsub) (fun B hB => by
      obtain ⟨hBt, hxB⟩ := Finset.mem_filter.1 hB
      exact hball B hBt hxB)
  exact_mod_cast hcard

open scoped Classical in
/-- **The segment shading mass is the tube shading mass**, exactly. -/
theorem sum_sum_segShade_eq {bs : Finset bι} {ctr : bι → EuclideanSpace ℝ (Fin 3)}
    {P : bι → Set (EuclideanSpace ℝ (Fin 3))} (hPmeas : ∀ B, MeasurableSet (P B))
    (hδr : 16 * (cfg.δ : ℝ) ≤ (cfg.r₁ : ℝ))
    (hPball16 : ∀ B ∈ bs, P B ⊆ ball (ctr B) ((cfg.r₁ : ℝ) / 16))
    (hPdisj : (bs : Set bι).PairwiseDisjoint P)
    (hPcov : ∀ i ∈ cfg.s, (cfg.T i).shade ⊆ ⋃ B ∈ bs, P B) :
    ∑ B ∈ bs, ∑ p ∈ segsOfCover cfg P B,
        volume (segBodyOfCover cfg ctr P hPmeas p).shade
      = ∑ i ∈ cfg.s, volume (cfg.T i).shade := by
  classical
  rw [sum_sum_segsOfCover]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hstep : ∀ B ∈ bs, volume (segBodyOfCover cfg ctr P hPmeas (i, B)).shade
      = volume ((cfg.T i).shade ∩ P B) := fun B hB => by
    rw [segBodyOfCover_shade_eq cfg hPmeas hδr hPball16 hB]
  calc ∑ B ∈ bs with ((cfg.T i).shade ∩ P B).Nonempty,
        volume (segBodyOfCover cfg ctr P hPmeas (i, B)).shade
      = ∑ B ∈ bs with ((cfg.T i).shade ∩ P B).Nonempty, volume ((cfg.T i).shade ∩ P B) :=
        Finset.sum_congr rfl fun B hB => hstep B (Finset.mem_filter.1 hB).1
    _ = ∑ B ∈ bs, volume ((cfg.T i).shade ∩ P B) := by
        refine Finset.sum_subset (Finset.filter_subset _ _) fun B hB hnB => ?_
        have hemp : (cfg.T i).shade ∩ P B = ∅ := by
          refine Set.not_nonempty_iff_eq_empty.1 fun hc => hnB ?_
          exact Finset.mem_filter.2 ⟨hB, hc⟩
        rw [hemp, measure_empty]
    _ = volume (cfg.T i).shade :=
        sum_volume_inter_pieces bs P hPdisj (fun B _ => hPmeas B) (hPcov i hi)

open scoped Classical in
/-- **The segment carrier mass is at most `ballCoverConstant` times the tube carrier mass.** -/
theorem sum_sum_segCarrier_le {bs : Finset bι} {ctr : bι → EuclideanSpace ℝ (Fin 3)}
    {P : bι → Set (EuclideanSpace ℝ (Fin 3))} (hPmeas : ∀ B, MeasurableSet (P B))
    (hδr : 16 * (cfg.δ : ℝ) ≤ (cfg.r₁ : ℝ))
    (hPball16 : ∀ B ∈ bs, P B ⊆ ball (ctr B) ((cfg.r₁ : ℝ) / 16))
    (hoverlap : ∀ (x : EuclideanSpace ℝ (Fin 3)) (t : Finset bι), t ⊆ bs →
      (∀ B ∈ t, x ∈ ball (ctr B) (cfg.r₁ : ℝ)) → t.card ≤ ballCoverConstant) :
    ∑ B ∈ bs, ∑ p ∈ segsOfCover cfg P B,
        volume (segBodyOfCover cfg ctr P hPmeas p).carrier
      ≤ (ballCoverConstant : ENNReal) * ∑ i ∈ cfg.s, volume (cfg.T i).carrier := by
  classical
  rw [sum_sum_segsOfCover, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  simpa using sum_volume_segCarrierSet_le cfg bs ctr P hδr hPball16 hoverlap i

/-! ### The global segment fullness -/

/-- **The `c₁` condition of `Kakeya.VeryNotSticky.segs_fullness_of_cover` is satisfiable**, so
the theorem is not vacuous: `ballCoverConstant = 35937`, and `c₁ = 1/143748` works. -/
theorem exists_c₁_admissible :
    ∃ c₁ : NNReal, 0 < c₁ ∧ 4 * c₁ * (ballCoverConstant : NNReal) ≤ 1 := by
  refine ⟨(143748 : NNReal)⁻¹, by norm_num, ?_⟩
  rw [ballCoverConstant]
  norm_num


open scoped Classical in
/-- **The global fullness of the segment family of the cover core**, at the Markov threshold
`4 c₁ δ^{2η}` that `Kakeya.VeryNotSticky.exists_heavyBalls_at` reads.

The hypothesis `hc₁ : 4 * c₁ * ballCoverConstant ≤ 1` is **not** decoration: the segment carrier
mass exceeds the tube carrier mass by the bounded-overlap factor `ballCoverConstant`, and the
Markov cut costs a further factor `4`. Both factors are `δ`-free. -/
theorem segs_fullness_of_cover {bs : Finset bι} {ctr : bι → EuclideanSpace ℝ (Fin 3)}
    {P : bι → Set (EuclideanSpace ℝ (Fin 3))} (hPmeas : ∀ B, MeasurableSet (P B))
    (hδr : 16 * (cfg.δ : ℝ) ≤ (cfg.r₁ : ℝ))
    (hPball16 : ∀ B ∈ bs, P B ⊆ ball (ctr B) ((cfg.r₁ : ℝ) / 16))
    (hPdisj : (bs : Set bι).PairwiseDisjoint P)
    (hPcov : ∀ i ∈ cfg.s, (cfg.T i).shade ⊆ ⋃ B ∈ bs, P B)
    (hoverlap : ∀ (x : EuclideanSpace ℝ (Fin 3)) (t : Finset bι), t ⊆ bs →
      (∀ B ∈ t, x ∈ ball (ctr B) (cfg.r₁ : ℝ)) → t.card ≤ ballCoverConstant)
    {c₁ : NNReal} (hc₁ : 4 * c₁ * (ballCoverConstant : NNReal) ≤ 1) :
    4 * ((c₁ : ENNReal) * (cfg.δ : ENNReal) ^ (2 * cfg.η)) *
        ∑ B ∈ bs, ∑ p ∈ segsOfCover cfg P B,
          volume (segBodyOfCover cfg ctr P hPmeas p).carrier ≤
      ∑ B ∈ bs, ∑ p ∈ segsOfCover cfg P B,
        volume (segBodyOfCover cfg ctr P hPmeas p).shade := by
  classical
  have hc₁E : 4 * (c₁ : ENNReal) * (ballCoverConstant : ENNReal) ≤ 1 := by
    have := ENNReal.coe_le_coe.2 hc₁
    push_cast at this ⊢
    exact this
  rw [sum_sum_segShade_eq cfg hPmeas hδr hPball16 hPdisj hPcov]
  calc 4 * ((c₁ : ENNReal) * (cfg.δ : ENNReal) ^ (2 * cfg.η)) *
        ∑ B ∈ bs, ∑ p ∈ segsOfCover cfg P B,
          volume (segBodyOfCover cfg ctr P hPmeas p).carrier
      ≤ 4 * ((c₁ : ENNReal) * (cfg.δ : ENNReal) ^ (2 * cfg.η)) *
          ((ballCoverConstant : ENNReal) * ∑ i ∈ cfg.s, volume (cfg.T i).carrier) := by
        gcongr
        exact sum_sum_segCarrier_le cfg hPmeas hδr hPball16 hoverlap
    _ = (4 * (c₁ : ENNReal) * (ballCoverConstant : ENNReal)) *
          ((cfg.δ : ENNReal) ^ (2 * cfg.η) * ∑ i ∈ cfg.s, volume (cfg.T i).carrier) := by
        ring
    _ ≤ 1 * ∑ i ∈ cfg.s, volume (cfg.T i).shade := by
        gcongr
        exact delta_pow_mul_sum_carrier_le cfg
    _ = ∑ i ∈ cfg.s, volume (cfg.T i).shade := one_mul _


/-! ### Step 5 of GWZ §9.3: the heavy-ball cut and the Markov/dyadic tier -/

section CoverAux

variable (cfg : VeryNotSticky.{u}) {bι : Type u}

open scoped Classical in
/-- The segment shading mass of a piece is the working-shading mass of that piece. -/
theorem sum_segShade_eq_ballYgMass_aux {bs : Finset bι} {ctr : bι → EuclideanSpace ℝ (Fin 3)}
    {P : bι → Set (EuclideanSpace ℝ (Fin 3))} (hPmeas : ∀ B, MeasurableSet (P B))
    (hδr : 16 * (cfg.δ : ℝ) ≤ (cfg.r₁ : ℝ))
    (hPball16 : ∀ B ∈ bs, P B ⊆ ball (ctr B) ((cfg.r₁ : ℝ) / 16))
    {B : bι} (hB : B ∈ bs) :
    ∑ p ∈ segsOfCover cfg P B, volume (segBodyOfCover cfg ctr P hPmeas p).shade
      = ∑ i ∈ cfg.s, volume ((cfg.T i).shade ∩ P B) := by
  classical
  rw [segsOfCover, Finset.sum_image (by intro a _ b _ h; exact (Prod.mk.injEq .. ▸ h).1)]
  calc ∑ i ∈ cfg.s with ((cfg.T i).shade ∩ P B).Nonempty,
        volume (segBodyOfCover cfg ctr P hPmeas (i, B)).shade
      = ∑ i ∈ cfg.s with ((cfg.T i).shade ∩ P B).Nonempty, volume ((cfg.T i).shade ∩ P B) :=
        Finset.sum_congr rfl fun i _ => by
          rw [segBodyOfCover_shade_eq cfg hPmeas hδr hPball16 hB]
    _ = ∑ i ∈ cfg.s, volume ((cfg.T i).shade ∩ P B) := by
        refine Finset.sum_subset (Finset.filter_subset _ _) fun i hi hni => ?_
        have hemp : (cfg.T i).shade ∩ P B = ∅ := by
          refine Set.not_nonempty_iff_eq_empty.1 fun hc => hni ?_
          exact Finset.mem_filter.2 ⟨hi, hc⟩
        rw [hemp, measure_empty]

/-- The total shading mass of a non-empty configuration is positive. -/
theorem sum_volume_shade_pos_of_nonempty (hs : cfg.s.Nonempty) :
    0 < ∑ i ∈ cfg.s, volume (cfg.T i).shade := by
  refine lt_of_lt_of_le ?_ (delta_pow_mul_sum_carrier_le cfg)
  have hfr : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := finrank_euclideanSpace_fin
  obtain ⟨i, hi⟩ := hs
  have hcar : 0 < volume (cfg.T i).carrier := by
    have h := Tube.le_volume (cfg.T i).toTube
    rw [hfr] at h
    refine lt_of_lt_of_le ?_ h
    have hc : (0 : ENNReal) < ((Tube.le_volume.c 3 : NNReal) : ENNReal) := by
      exact_mod_cast Tube.le_volume.c_pos 3
    have hd : (0 : ENNReal) < (cfg.δ : ENNReal) := by exact_mod_cast cfg.hδ
    positivity
  have hsum : 0 < ∑ i ∈ cfg.s, volume (cfg.T i).carrier :=
    lt_of_lt_of_le hcar (Finset.single_le_sum
      (f := fun i => volume (cfg.T i).carrier) (fun _ _ => by simp) hi)
  have hd : (0 : ENNReal) < (cfg.δ : ENNReal) ^ (2 * cfg.η) :=
    ENNReal.rpow_pos (by exact_mod_cast cfg.hδ) ENNReal.coe_ne_top
  positivity


end CoverAux

section Steps

variable {cfg : VeryNotSticky.{u}}

open scoped Classical in
/-- **The heavy-ball cut on a core, in `restrictBalls` form** (GWZ §9.3, `gwz.txt` l.2029–2032;
G3-O2). -/
theorem exists_heavyBalls_core (core : BallDataCore cfg) {c₁ : NNReal}
    (hSm : ∀ B ∈ core.bs, ∑ p ∈ core.segs B, volume (core.Y p).shade = ballYgMass core B)
    (hCtop : ∑ B ∈ core.bs, ∑ p ∈ core.segs B, volume (core.Y p).carrier ≠ ⊤)
    (hS0 : ∑ B ∈ core.bs, ∑ p ∈ core.segs B, volume (core.Y p).shade ≠ 0)
    (hfull : 4 * ((c₁ : ENNReal) * (cfg.δ : ENNReal) ^ (2 * cfg.η)) *
        ∑ B ∈ core.bs, ∑ p ∈ core.segs B, volume (core.Y p).carrier ≤
      ∑ B ∈ core.bs, ∑ p ∈ core.segs B, volume (core.Y p).shade) :
    ∃ bs' : Finset core.bι, bs' ⊆ core.bs ∧ bs'.Nonempty ∧
      (((2 : NNReal) : ENNReal)⁻¹ * ∑ i ∈ cfg.s, volume (core.Yg i) ≤
        ∑ i ∈ cfg.s, volume (restrictYg core bs' i)) ∧
      (∀ B ∈ bs', 2 * ((c₁ : ENNReal) * (cfg.δ : ENNReal) ^ (2 * cfg.η)) *
          ∑ p ∈ core.segs B, volume (core.Y p).carrier ≤
        ∑ p ∈ core.segs B, volume (core.Y p).shade) := by
  classical
  set Cm : core.bι → ENNReal := fun B => ∑ p ∈ core.segs B, volume (core.Y p).carrier with hCm
  set Sm : core.bι → ENNReal := fun B => ∑ p ∈ core.segs B, volume (core.Y p).shade with hSmd
  set θ : ENNReal := (c₁ : ENNReal) * (cfg.δ : ENNReal) ^ (2 * cfg.η) with hθd
  have hθ : θ ≠ ⊤ := by
    rw [hθd, ← ENNReal.coe_rpow_of_ne_zero (ne_of_gt cfg.hδ), ← ENNReal.coe_mul]
    exact ENNReal.coe_ne_top
  have hheavy := exists_heavyBalls_at core.bs Cm Sm hθ hCtop hfull
  set bs' : Finset core.bι := core.bs.filter (fun B => 2 * θ * Cm B ≤ Sm B) with hbs'
  have hsub : bs' ⊆ core.bs := Finset.filter_subset _ _
  have hne : bs'.Nonempty := by
    rcases Finset.eq_empty_or_nonempty bs' with hemp | h
    · rw [hemp, Finset.sum_empty, le_zero_iff, mul_eq_zero] at hheavy
      rcases hheavy with h2 | hS
      · exact absurd h2 (by simp)
      · exact absurd hS hS0
    · exact h
  have hretY : ((2 : NNReal) : ENNReal)⁻¹ * ∑ i ∈ cfg.s, volume (core.Yg i) ≤
      ∑ i ∈ cfg.s, volume (restrictYg core bs' i) := by
    refine restrictYg_mass_of_retention core bs' hsub (K := 2) ?_
    have h1 : ∑ B ∈ core.bs, ballYgMass core B = ∑ B ∈ core.bs, Sm B :=
      Finset.sum_congr rfl fun B hB => (hSm B hB).symm
    have h2 : ∑ B ∈ bs', ballYgMass core B = ∑ B ∈ bs', Sm B :=
      Finset.sum_congr rfl fun B hB => (hSm B (hsub hB)).symm
    rw [h1, h2]
    simpa using hheavy
  refine ⟨bs', hsub, hne, hretY, fun B hB => ?_⟩
  exact (Finset.mem_filter.1 hB).2

/-- The segment carrier mass of a ball is positive. -/
theorem sum_volume_carrier_pos (core : BallDataCore cfg) {B : core.bι} (hB : B ∈ core.bs) :
    0 < ∑ p ∈ core.segs B, volume (core.Y p).carrier := by
  obtain ⟨p, hp⟩ := core.segs_nonempty B hB
  refine lt_of_lt_of_le (carrier_volume_pos core hB hp) ?_
  exact Finset.single_le_sum (f := fun p => volume (core.Y p).carrier)
    (fun _ _ => by simp) hp

/-- On a ball where the per-ball fullness holds the segment shading mass is positive. -/
theorem sum_volume_shade_pos (core : BallDataCore cfg) {c₁ : NNReal} (hc₁ : 0 < c₁)
    {B : core.bι} (hB : B ∈ core.bs)
    (hfull : 2 * ((c₁ : ENNReal) * (cfg.δ : ENNReal) ^ (2 * cfg.η)) *
        ∑ p ∈ core.segs B, volume (core.Y p).carrier ≤
      ∑ p ∈ core.segs B, volume (core.Y p).shade) :
    0 < ∑ p ∈ core.segs B, volume (core.Y p).shade := by
  refine lt_of_lt_of_le ?_ hfull
  have h1 : (0 : ENNReal) < (c₁ : ENNReal) := by
    exact_mod_cast hc₁
  have h2 : (0 : ENNReal) < (cfg.δ : ENNReal) ^ (2 * cfg.η) :=
    ENNReal.rpow_pos (by exact_mod_cast cfg.hδ) ENNReal.coe_ne_top
  have h3 := sum_volume_carrier_pos core hB
  positivity

open scoped Classical in
/-- **The tier data of GWZ §9.3 steps 5–6**, on a core carrying the per-ball fullness. -/
theorem exists_markovDyadicTier_data (core : BallDataCore cfg) {c₁ : NNReal} (hc₁ : 0 < c₁)
    (hfull : ∀ B ∈ core.bs, 2 * ((c₁ : ENNReal) * (cfg.δ : ENNReal) ^ (2 * cfg.η)) *
        ∑ p ∈ core.segs B, volume (core.Y p).carrier ≤
      ∑ p ∈ core.segs B, volume (core.Y p).shade) :
    ∃ k : core.bι → ℕ,
      (∀ B ∈ core.bs, (markovDyadicTier core c₁ k B).Nonempty) ∧
      (∀ B ∈ core.bs, ((tierRetention cfg c₁ : NNReal) : ENNReal)⁻¹ *
          ∑ p ∈ core.segs B, volume (core.Y p).shade ≤
        ∑ p ∈ markovDyadicTier core c₁ k B, volume (core.Y p).shade) := by
  classical
  obtain ⟨k, hk⟩ := exists_markovDyadicTier_retention core hc₁ hfull
  have hne : ∀ B ∈ core.bs, (markovDyadicTier core c₁ k B).Nonempty := by
    intro B hB
    exact tier_nonempty_of_retention core (markovDyadicTier core c₁ k)
      (sum_volume_shade_pos core hc₁ hB (hfull B hB)) (hk B hB)
  exact ⟨k, hne, hk⟩



/-- A tier that carries Lemma 9.2's carrier retention in a ball is non-empty. -/
theorem tier_nonempty_of_carrier_retention (core : BallDataCore cfg)
    {tier : core.bι → Finset core.σ} {B : core.bι} (hB : B ∈ core.bs) {L : ENNReal}
    (hret : ∑ p ∈ core.segs B, volume (core.Y p).carrier ≤
      L * ∑ p ∈ tier B, volume (core.Y p).carrier) :
    (tier B).Nonempty := by
  rcases Finset.eq_empty_or_nonempty (tier B) with hemp | hne
  · rw [hemp, Finset.sum_empty, mul_zero, nonpos_iff_eq_zero] at hret
    exact absurd hret (ne_of_gt (sum_volume_carrier_pos core hB))
  · exact hne


/-! ### The per-ball factorings of Lemma 9.2, glued -/

open scoped Classical in
/-- **The per-ball factorings of Lemma 9.2, glued into one global family**. The body index type is
`core.bι × Finset core.σ`, tagging each block by its ball; the tag is well defined because on a
core carrying `segs_density` every retained segment lies in exactly one ball
(`Kakeya.VeryNotSticky.ballTag_eq_of_segs_density`). -/
theorem exists_ballFactoring_glued (core : BallDataCore cfg) {c₁ : NNReal} (hc₁ : 0 < c₁)
    (hdens : ∀ B ∈ core.bs, ∀ p ∈ core.segs B,
      (c₁ : ENNReal) * (cfg.δ : ENNReal) ^ (2 * cfg.η) * volume (core.Y p).carrier ≤
        volume (core.Y p).shade) :
    ∃ (tier : core.bι → Finset core.σ)
      (bodies : core.bι → Finset (core.bι × Finset core.σ))
      (Wb : core.bι × Finset core.σ → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)))
      (blk : core.σ → core.bι × Finset core.σ),
      (∀ B ∈ core.bs, tier B ⊆ core.segs B) ∧
      (∀ B ∈ core.bs, ∑ p ∈ core.segs B, volume (core.Y p).carrier ≤
        ConvexSpaceBody.nonempty_biasedFactorization.L 3 (core.segs B).card
            (cfg.δ / cfg.r₁) cfg.ϱ *
          ∑ p ∈ tier B, volume (core.Y p).carrier) ∧
      (∀ B ∈ core.bs, ∀ p ∈ tier B, blk p ∈ bodies B) ∧
      (∀ B ∈ core.bs, ∀ p ∈ tier B, (core.Y p).toConvexSpaceBody ≤ Wb (blk p)) ∧
      (∀ B ∈ core.bs, ∀ j ∈ bodies B,
        (Wb j).carrier ⊆ closedBall (core.ctr B) (cfg.r₁ : ℝ)) ∧
      (∀ B ∈ core.bs, ∀ j ∈ bodies B,
        ConvexSpaceBody.IsFrostmanIn ((tier B).filter fun p => blk p = j)
          (fun p => (core.Y p).toConvexSpaceBody) (Wb j) (lemma92Constant cfg.ϱ)) ∧
      (∀ B ∈ core.bs, ∀ j ∈ bodies B,
        ∀ K : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)), K ≤ Wb j →
          densityIn ((tier B).filter fun p => blk p = j)
              (fun p => (core.Y p).toConvexSpaceBody) K ≤
            (lemma92Bias core.C₀ cfg.ϱ : ENNReal) *
              (volume K.carrier / volume (Wb j).carrier) ^ cfg.ϱ *
              densityIn ((tier B).filter fun p => blk p = j)
                (fun p => (core.Y p).toConvexSpaceBody) (Wb j)) ∧
      (∀ B ∈ core.bs, maxDensity (bodies B) Wb ≤
        (lemma92Bias core.C₀ cfg.ϱ : ENNReal) * (cfg.δ : ENNReal) ^ (-(2 * cfg.ϱ))) ∧
      (∀ B ∈ core.bs, ∀ j ∈ bodies B, ∀ j' ∈ bodies B,
        ethickness ℝ (Wb j).carrier ≤ lemma92Constant cfg.ϱ • ethickness ℝ (Wb j').carrier) ∧
      (∀ B ∈ core.bs, ∀ j ∈ bodies B, ∃ p ∈ tier B, blk p = j) := by
  classical
  have hex : ∀ B : core.bι, B ∈ core.bs →
      ∃ (s' : Finset core.σ) (parts : Finset (Finset core.σ))
        (W : Finset core.σ → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)))
        (bk : core.σ → Finset core.σ),
        s' ⊆ core.segs B ∧
        (∑ p ∈ core.segs B, volume (core.Y p).carrier ≤
          ConvexSpaceBody.nonempty_biasedFactorization.L 3 (core.segs B).card
              (cfg.δ / cfg.r₁) cfg.ϱ * ∑ p ∈ s', volume (core.Y p).carrier) ∧
        (∀ p ∈ s', bk p ∈ parts) ∧
        (∀ p ∈ s', (core.Y p).toConvexSpaceBody ≤ W (bk p)) ∧
        (∀ j ∈ parts, (W j).carrier ⊆ closedBall (core.ctr B) (cfg.r₁ : ℝ)) ∧
        (∀ j ∈ parts,
          ConvexSpaceBody.IsFrostmanIn (s'.filter fun p => bk p = j)
            (fun p => (core.Y p).toConvexSpaceBody) (W j) (lemma92Constant cfg.ϱ)) ∧
        (∀ j ∈ parts,
          ∀ K : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)), K ≤ W j →
            densityIn (s'.filter fun p => bk p = j)
                (fun p => (core.Y p).toConvexSpaceBody) K ≤
              (lemma92Bias core.C₀ cfg.ϱ : ENNReal) *
                (volume K.carrier / volume (W j).carrier) ^ cfg.ϱ *
                densityIn (s'.filter fun p => bk p = j)
                  (fun p => (core.Y p).toConvexSpaceBody) (W j)) ∧
        maxDensity parts W ≤
          (lemma92Bias core.C₀ cfg.ϱ : ENNReal) * (cfg.δ : ENNReal) ^ (-(2 * cfg.ϱ)) ∧
        (∀ j ∈ parts, ∀ j' ∈ parts,
          ethickness ℝ (W j).carrier ≤ lemma92Constant cfg.ϱ • ethickness ℝ (W j').carrier) ∧
        (∀ j ∈ parts, ∃ p ∈ s', bk p = j) := by
    intro B hB
    obtain ⟨s', parts, W, bk, h1, h2, h3, h4, h5, h6, h7, h8, -, h10, h11⟩ :=
      exists_ballFactoring_core_inhab cfg core hB
    exact ⟨s', parts, W, bk, h1, h2, h3, h4, h5, h6, h7, h8, h10, h11⟩
  choose! s' parts W bk h1 h2 h3 h4 h5 h6 h7 h8 h10 h11 using hex
  have htag : ∀ B ∈ core.bs, ∀ p ∈ core.segs B, core.ballTag p = B :=
    fun B hB p hp => ballTag_eq_of_segs_density core hc₁ hdens hB hp
  have hinj : ∀ B : core.bι, Function.Injective (fun t : Finset core.σ => (B, t)) :=
    fun B a b h => (Prod.mk.injEq .. ▸ h).2
  have hfilt : ∀ B ∈ core.bs, ∀ t : Finset core.σ,
      ((s' B).filter fun p => (core.ballTag p, bk (core.ballTag p) p) = (B, t))
        = (s' B).filter fun p => bk B p = t := by
    intro B hB t
    refine Finset.filter_congr fun p hp => ?_
    have htg : core.ballTag p = B := htag B hB p (h1 B hB hp)
    simp [htg]
  refine ⟨s', fun B => (parts B).image (fun t => (B, t)), fun q => W q.1 q.2,
    fun p => (core.ballTag p, bk (core.ballTag p) p), h1, h2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `blk_mem`
    intro B hB p hp
    have htg : core.ballTag p = B := htag B hB p (h1 B hB hp)
    simp only [htg]
    exact Finset.mem_image_of_mem _ (h3 B hB p hp)
  · -- `segs_le`
    intro B hB p hp
    have htg : core.ballTag p = B := htag B hB p (h1 B hB hp)
    simpa only [htg] using h4 B hB p hp
  · -- `bodies_subset_ball`
    intro B hB j hj
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hj
    exact h5 B hB t ht
  · -- `frostman`
    intro B hB j hj
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hj
    simpa only [hfilt B hB t] using h6 B hB t ht
  · -- `biasedDensity`
    intro B hB j hj
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hj
    simpa only [hfilt B hB t] using h7 B hB t ht
  · -- `bodies_antiClustering`
    intro B hB
    rw [maxDensity_le_iff]
    intro K
    have hdi : densityIn ((parts B).image (fun t => (B, t))) (fun q => W q.1 q.2) K
        = densityIn (parts B) (W B) K := by
      unfold densityIn
      congr 1
      rw [Finset.filter_image, Finset.sum_image (fun a _ b _ h => hinj B h)]
    rw [hdi]
    exact le_trans (le_maxDensity _ _ _) (h8 B hB)
  · -- `simDims`
    intro B hB j hj j' hj'
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hj
    obtain ⟨t', ht', rfl⟩ := Finset.mem_image.1 hj'
    exact h10 B hB t ht t' ht'
  · -- block inhabitation
    intro B hB j hj
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hj
    obtain ⟨p, hp, hpt⟩ := h11 B hB t ht
    refine ⟨p, hp, ?_⟩
    have htg : core.ballTag p = B := htag B hB p (h1 B hB hp)
    simp only [htg, hpt]


end Steps

/-! ### The core of GWZ §9.3 after steps 5–6, from conjunct 1's cover hypotheses -/

open scoped Classical in
theorem exists_core_segsDensity_of_cover (cfg : VeryNotSticky.{u}) {bι : Type u}
    {C₀ : NNReal} (hC₀ : 4 ≤ C₀) {D : ℕ} (hD : ballCoverConstant ≤ D)
    (hδr : 16 * (cfg.δ : ℝ) ≤ (cfg.r₁ : ℝ))
    (bs : Finset bι) (ctr : bι → EuclideanSpace ℝ (Fin 3))
    (P : bι → Set (EuclideanSpace ℝ (Fin 3)))
    (hbsne : bs.Nonempty)
    (hPball16 : ∀ B ∈ bs, P B ⊆ ball (ctr B) ((cfg.r₁ : ℝ) / 16))
    (hPball : ∀ B ∈ bs, P B ⊆ closedBall (ctr B) (cfg.r₁ : ℝ))
    (hPdisj : (bs : Set bι).PairwiseDisjoint P)
    (hPmeas : ∀ B, MeasurableSet (P B))
    (hPcov : ∀ i ∈ cfg.s, (cfg.T i).shade ⊆ ⋃ B ∈ bs, P B)
    (hoverlap : ∀ (x : EuclideanSpace ℝ (Fin 3)) (t : Finset bι), t ⊆ bs →
      (∀ B ∈ t, x ∈ ball (ctr B) (cfg.r₁ : ℝ)) → t.card ≤ ballCoverConstant)
    (hPne : ∀ B ∈ bs, (P B ∩ ⋃ i ∈ cfg.s, (cfg.T i).shade).Nonempty)
    {c₁ : NNReal} (hc₁ : 0 < c₁)
    (hc₁' : 4 * c₁ * (ballCoverConstant : NNReal) ≤ 1) :
    ∃ core : BallDataCore cfg,
      core.C₀ = C₀ ∧ core.D = D ∧ core.m = 1 ∧ core.Cm = 1 ∧
      core.Cg = 2 * tierRetention cfg c₁ ∧
      (∀ B ∈ core.bs, ∀ p ∈ core.segs B,
        (c₁ : ENNReal) * (cfg.δ : ENNReal) ^ (2 * cfg.η) * volume (core.Y p).carrier ≤
          volume (core.Y p).shade) ∧
      (∀ B ∈ core.bs, (cfg.r₁ : ENNReal) ^ 2 *
          maxDensity (core.segs B) (fun p ↦ (core.Y p).toConvexSpaceBody) ≤
        (segsDilationConstant : ENNReal) *
          maxDensity cfg.s (fun i ↦ (cfg.T i).toConvexSpaceBody)) ∧
      (∀ B ∈ core.bs, ∀ p ∈ core.segs B, ∀ q ∈ core.segs B,
        shadeFractionClass core p = shadeFractionClass core q) := by
  classical
  -- step 0: T3's coarse core
  set core₀ := ballDataCoreOfCover cfg hC₀ hD hδr bs ctr P hbsne hPball16 hPball hPdisj hPmeas
    hPcov hoverlap hPne with hcore₀
  have hbs₀ : core₀.bs = bs := rfl
  have hsegs₀ : core₀.segs = segsOfCover cfg P := rfl
  have hY₀ : core₀.Y = segBodyOfCover cfg ctr P hPmeas := rfl
  have hYg₀ : core₀.Yg = fun i => (cfg.T i).shade := rfl
  have hP₀ : core₀.P = P := rfl
  -- the three inputs of the heavy-ball cut
  have hsne : cfg.s.Nonempty := by
    obtain ⟨B, hB⟩ := hbsne
    obtain ⟨x, -, hxs⟩ := hPne B hB
    obtain ⟨i, hi, -⟩ := Set.mem_iUnion₂.mp hxs
    exact ⟨i, hi⟩
  have hSm : ∀ B ∈ core₀.bs, ∑ p ∈ core₀.segs B, volume (core₀.Y p).shade
      = ballYgMass core₀ B := by
    intro B hB
    exact sum_segShade_eq_ballYgMass_aux cfg hPmeas hδr hPball16 hB
  have hCtop : ∑ B ∈ core₀.bs, ∑ p ∈ core₀.segs B, volume (core₀.Y p).carrier ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (sum_sum_segCarrier_le cfg hPmeas hδr hPball16 hoverlap)
    exact ENNReal.mul_ne_top (by simp) (sum_volume_carrier_ne_top cfg)
  have hS0eq : ∑ B ∈ core₀.bs, ∑ p ∈ core₀.segs B, volume (core₀.Y p).shade
      = ∑ i ∈ cfg.s, volume (cfg.T i).shade :=
    sum_sum_segShade_eq cfg hPmeas hδr hPball16 hPdisj hPcov
  have hS0 : ∑ B ∈ core₀.bs, ∑ p ∈ core₀.segs B, volume (core₀.Y p).shade ≠ 0 := by
    rw [hS0eq]
    exact ne_of_gt (sum_volume_shade_pos_of_nonempty cfg hsne)
  have hfull : 4 * ((c₁ : ENNReal) * (cfg.δ : ENNReal) ^ (2 * cfg.η)) *
      ∑ B ∈ core₀.bs, ∑ p ∈ core₀.segs B, volume (core₀.Y p).carrier ≤
      ∑ B ∈ core₀.bs, ∑ p ∈ core₀.segs B, volume (core₀.Y p).shade := by
    rw [hbs₀, hsegs₀, hY₀]
    exact segs_fullness_of_cover cfg hPmeas hδr hPball16 hPdisj hPcov hoverlap hc₁'
  -- step 1: the heavy-ball cut
  obtain ⟨bs', hsub, hne, hret, hheavy⟩ :=
    exists_heavyBalls_core core₀ hSm hCtop hS0 hfull
  set core₁ := core₀.restrictBalls bs' hsub hne (K := 2) (by norm_num) hret with hcore₁
  -- step 2: the Markov / dyadic tier
  have hfull₁ : ∀ B ∈ core₁.bs, 2 * ((c₁ : ENNReal) * (cfg.δ : ENNReal) ^ (2 * cfg.η)) *
      ∑ p ∈ core₁.segs B, volume (core₁.Y p).carrier ≤
      ∑ p ∈ core₁.segs B, volume (core₁.Y p).shade := hheavy
  obtain ⟨k, hkne, hkret⟩ := exists_markovDyadicTier_data core₁ hc₁ hfull₁
  refine ⟨markovDyadicTierCore core₁ c₁ k hkne hkret, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · have hCgeq : (markovDyadicTierCore core₁ c₁ k hkne hkret).Cg
        = core₀.Cg * 2 * (1 : NNReal) ^ 2 * tierRetention cfg c₁ := rfl
    have hCg₀ : core₀.Cg = 1 := rfl
    rw [hCgeq, hCg₀]
    norm_num
  · exact markovDyadicTierCore_segs_density core₁ c₁ k hkne hkret
  · exact tierCore_segs_dilation core₁ _ _ _ _ _
      (restrictBalls_segs_dilation core₀ bs' hsub hne (by norm_num) hret
        (segs_dilation_ballDataCoreOfCover (cfg := cfg) (hC₀ := hC₀) (hD := hD) (hδr := hδr)
          (bs := bs) (ctr := ctr) (P := P) (hbsne := hbsne) (hPball16 := hPball16)
          (hPball := hPball) (hPdisj := hPdisj) (hPmeas := hPmeas) (hPcov := hPcov)
          (hoverlap := hoverlap) (hPne := hPne)))
  · intro B hB p hp q hq
    exact markovDyadicTier_shadeFractionClass_eq core₁ c₁ k hp hq

/-! ### The re-cut general-branch contract -/

section GeneralContract

open Topology Filter

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **`segsDilationConstant ≤ capsuleDilationConstant`.**  The T3 core's dilation constant sits
under the contract's ceiling, so the existing producer meets the ceiling
clause `bd.Cdil ≤ capsuleDilationConstant` from its pin `bd.Cdil = segsDilationConstant` by
`le_of_eq` and this.  Stated here — the first file importing both `BallCoreOfCover`
(`segsDilationConstant`) and `EDConstants` (`capsuleDilationConstant`); `EDConstants` does not
import `BallCoreOfCover`. -/
theorem segsDilationConstant_le_capsuleDilationConstant :
    segsDilationConstant ≤ capsuleDilationConstant := by
  unfold segsDilationConstant capsuleDilationConstant
  gcongr
  norm_num

/-- The general working-dimension construction.

The hypotheses fix `CaseParams`, a geometric comparison floor
`edSegmentsConstant ≤ C₀bd`, the overlap bound `ballCoverConstant ≤ D`,
and an admissible positive density constant
`edDensityConstant * c₁ * ballCoverConstant ≤ 1`. The consequence
`ϱ ≤ 1/21` follows from `CaseParams` and is not a separate assumption.

For sufficiently small `δ` and a cover satisfying the eight listed conditions,
the conclusion chooses `δ ≤ a ≤ b ≤ r₁` and a `BallData` at these dimensions.
Its constants satisfy `Cbias = lemma92Bias C₀bd ϱ`,
`CF = lemma92Constant ϱ`, `Cdil ≤ capsuleDilationConstant`, and
`Cg ≤ δ^{-εg}` for the prescribed `εg > 0`.
The degree-four polylogarithmic loss in `nonempty_biasedFactorization.L`
is absorbed by `eventually_uniformLossBound_three_le_rpow_neg`; an
additive logarithmic bound alone would not suffice.

The fibre estimate retains `Cm = 1` and controls `Cm * m` by
`fibreMassConstant * δ^{-(η + 2 exscal)}`. This constant is accounted for
in `SlabScale.final` and `SlabInputs.finalThreshold`. The dilation ceiling
accommodates the capsule estimate `576000 / c₃`; the smaller value
`3 * 2^15 / c₃` would not suffice.

The bodies are localized unconditionally inside the ball of radius
`11r₁/16` and have thickness profile `![r₁, b, a]` at constant `C₀bd`.
Their scale-thickenings lie in the radius-`r₁` ball under the thin-case
guard `a ≤ δ^(1 - τ)`. Localization and the thickness profile are
independent of this guard. The enlarged radius floor is
`edRadiusConstant * δ ≤ r₁`, which implies `16δ ≤ r₁`.

All hypotheses are concrete: there is no arbitrary proposition standing
for essential distinctness. Such a negatively used proposition could be
instantiated by `False`, making a conditional construction vacuous. -/
def BallDataGeneralTarget (β ζ exscal ϱ η τ τ' : ℝ)
    (C₀bd : NNReal) (D : ℕ) (c₁ : NNReal) (εg : ℝ) : Prop :=
  CaseParams β ζ exscal ϱ η τ τ' → edSegmentsConstant ≤ C₀bd → ballCoverConstant ≤ D →
    0 < c₁ → edDensityConstant * c₁ * (ballCoverConstant : NNReal) ≤ 1 → 0 < εg →
    ∀ᶠ δ : NNReal in 𝓝[>] 0, ∀ (cfg : VeryNotSticky.{u}),
      cfg.δ = δ → cfg.η = η → cfg.exscal = exscal → cfg.ϱ = ϱ →
      ((edRadiusConstant : NNReal) : ℝ) * (cfg.δ : ℝ) ≤ (cfg.r₁ : ℝ) →
      ∀ {bι : Type u} (bs : Finset bι) (ctr : bι → E3) (P : bι → Set E3),
        bs.Nonempty →
        (∀ B ∈ bs, P B ⊆ Metric.ball (ctr B) ((cfg.r₁ : ℝ) / 16)) →
        (∀ B ∈ bs, P B ⊆ Metric.closedBall (ctr B) (cfg.r₁ : ℝ)) →
        (bs : Set bι).PairwiseDisjoint P →
        (∀ B, MeasurableSet (P B)) →
        (∀ i ∈ cfg.s, (cfg.T i).shade ⊆ ⋃ B ∈ bs, P B) →
        (∀ (x : E3) (t : Finset bι), t ⊆ bs →
          (∀ B ∈ t, x ∈ Metric.ball (ctr B) (cfg.r₁ : ℝ)) → t.card ≤ ballCoverConstant) →
        (∀ B ∈ bs, (P B ∩ ⋃ i ∈ cfg.s, (cfg.T i).shade).Nonempty) →
        ∃ (a b : NNReal) (h : cfg.δ ≤ a ∧ a ≤ b ∧ b ≤ cfg.δ ^ cfg.exscal)
          (bd : BallData (cfg.withDims a b h)),
          bd.C₀ = C₀bd ∧ bd.Cbias = lemma92Bias C₀bd ϱ ∧ bd.CF = lemma92Constant ϱ ∧
          bd.Cdil ≤ capsuleDilationConstant ∧
          bd.c₁ = c₁ ∧ bd.D = D ∧ bd.Cg ≤ cfg.δ ^ (-εg) ∧ bd.Cm = 1 ∧
          (bd.Cm : ENNReal) * (bd.m : ENNReal) ≤
            (fibreMassConstant : ENNReal) *
              (cfg.δ : ENNReal) ^ (-(cfg.η + 2 * cfg.exscal)) ∧
          cfg.δ ≤ bd.w₁ ∧ bd.w₁ ≤ 1 ∧
          (∀ B ∈ bd.bs, ∀ j ∈ bd.bodies B,
            (bd.Wb j).carrier ⊆ Metric.closedBall (bd.ctr B) (11 * (cfg.r₁ : ℝ) / 16)) ∧
          (∀ B ∈ bd.bs, ∀ j ∈ bd.bodies B,
            HasThicknesses (bd.Wb j).carrier C₀bd ![(cfg.r₁ : ℝ), (b : ℝ), (a : ℝ)]) ∧
          ((a : ℝ) ≤ (cfg.δ : ℝ) ^ (1 - τ) →
            ∀ B ∈ bd.bs, ∀ j ∈ bd.bodies B,
              Metric.cthickening (bd.Wb j).scale (bd.Wb j).carrier ⊆
                Metric.closedBall (bd.ctr B) (cfg.r₁ : ℝ))

/-- **Tripwire: the licensed F23″ text of  §I-4 +  §C-iv, verbatim, is
exactly `BallDataGeneralTarget`.** The proof is the bare application, so this `example` fails to
elaborate the moment the `def` above and the licensed statement diverge — in a floor, in a pin,
in the fibre budget, in the margin block, or in one of the eight cover binders.

The shape is load-bearing, not decorative — measured negative controls, each `EXIT=1`:
dropping `params` from the application gives an application type mismatch at `hC₀bd`; putting
`4 ≤ C₀bd` back in the `def`'s floor gives one at `hC₀bd`; putting (at the F23″ landing)
`bd.m = 1 ∧ bd.Cm = 1` back in the conclusion gave a type mismatch on the whole application; and
widening the margin guard from `δ ^ (1 - τ)` to `δ ^ (1 - 2 * τ)` does the same.  Since the
 re-cut the pins read `bd.Cdil ≤ capsuleDilationConstant ∧ … ∧ bd.Cm = 1 ∧` and the
fibre budget carries `fibreMassConstant`; the `example` below is byte-identical to the `def`'s
conclusion at that text. -/
example
    (hT : ∀ (β ζ exscal ϱ η τ τ' : ℝ) (C₀bd : NNReal) (D : ℕ) (c₁ : NNReal) (εg : ℝ),
      BallDataGeneralTarget.{u} β ζ exscal ϱ η τ τ' C₀bd D c₁ εg)
    (β ζ exscal ϱ η τ τ' : ℝ) (params : CaseParams β ζ exscal ϱ η τ τ')
    (C₀bd : NNReal) (hC₀bd : edSegmentsConstant ≤ C₀bd)
    (D : ℕ) (hD : ballCoverConstant ≤ D)
    {c₁ : NNReal} (hc₁ : 0 < c₁)
    (hc₁' : edDensityConstant * c₁ * (ballCoverConstant : NNReal) ≤ 1)
    {εg : ℝ} (hεg : 0 < εg) :
    ∀ᶠ δ : NNReal in 𝓝[>] 0, ∀ (cfg : VeryNotSticky.{u}),
      cfg.δ = δ → cfg.η = η → cfg.exscal = exscal → cfg.ϱ = ϱ →
      ((edRadiusConstant : NNReal) : ℝ) * (cfg.δ : ℝ) ≤ (cfg.r₁ : ℝ) →
      ∀ {bι : Type u} (bs : Finset bι) (ctr : bι → E3) (P : bι → Set E3),
        bs.Nonempty →
        (∀ B ∈ bs, P B ⊆ Metric.ball (ctr B) ((cfg.r₁ : ℝ) / 16)) →
        (∀ B ∈ bs, P B ⊆ Metric.closedBall (ctr B) (cfg.r₁ : ℝ)) →
        (bs : Set bι).PairwiseDisjoint P →
        (∀ B, MeasurableSet (P B)) →
        (∀ i ∈ cfg.s, (cfg.T i).shade ⊆ ⋃ B ∈ bs, P B) →
        (∀ (x : E3) (t : Finset bι), t ⊆ bs →
          (∀ B ∈ t, x ∈ Metric.ball (ctr B) (cfg.r₁ : ℝ)) → t.card ≤ ballCoverConstant) →
        (∀ B ∈ bs, (P B ∩ ⋃ i ∈ cfg.s, (cfg.T i).shade).Nonempty) →
        ∃ (a b : NNReal) (h : cfg.δ ≤ a ∧ a ≤ b ∧ b ≤ cfg.δ ^ cfg.exscal)
          (bd : BallData (cfg.withDims a b h)),
          bd.C₀ = C₀bd ∧ bd.Cbias = lemma92Bias C₀bd ϱ ∧ bd.CF = lemma92Constant ϱ ∧
          bd.Cdil ≤ capsuleDilationConstant ∧
          bd.c₁ = c₁ ∧ bd.D = D ∧ bd.Cg ≤ cfg.δ ^ (-εg) ∧ bd.Cm = 1 ∧
          (bd.Cm : ENNReal) * (bd.m : ENNReal) ≤
            (fibreMassConstant : ENNReal) *
              (cfg.δ : ENNReal) ^ (-(cfg.η + 2 * cfg.exscal)) ∧
          cfg.δ ≤ bd.w₁ ∧ bd.w₁ ≤ 1 ∧
          (∀ B ∈ bd.bs, ∀ j ∈ bd.bodies B,
            (bd.Wb j).carrier ⊆ Metric.closedBall (bd.ctr B) (11 * (cfg.r₁ : ℝ) / 16)) ∧
          (∀ B ∈ bd.bs, ∀ j ∈ bd.bodies B,
            HasThicknesses (bd.Wb j).carrier C₀bd ![(cfg.r₁ : ℝ), (b : ℝ), (a : ℝ)]) ∧
          ((a : ℝ) ≤ (cfg.δ : ℝ) ^ (1 - τ) →
            ∀ B ∈ bd.bs, ∀ j ∈ bd.bodies B,
              Metric.cthickening (bd.Wb j).scale (bd.Wb j).carrier ⊆
                Metric.closedBall (bd.ctr B) (cfg.r₁ : ℝ)) :=
  hT β ζ exscal ϱ η τ τ' C₀bd D c₁ εg params hC₀bd hD hc₁ hc₁' hεg

end GeneralContract

end Kakeya.VeryNotSticky
