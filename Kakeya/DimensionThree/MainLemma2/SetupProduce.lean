/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.VeryNotStickyCase
public import Kakeya.DimensionThree.MainLemma2.BallCountRepair
public import Kakeya.DimensionThree.MainLemma2.SetupFullnessBudget
public import Kakeya.DimensionThree.MainLemma2.Reduction.Assembly

/-!
# Producing Configuration `hyp:ml2setup`
-/

@[expose] public section

namespace Kakeya.VeryNotSticky

open MeasureTheory Metric Set Topology Filter ShadedBody

universe u

/-- **The density band of `Kakeya.VeryNotSticky` is exactly individual `δ^{2η}`-fullness.** -/
theorem exists_band_of_pointwise_two_eta {ι : Type*} {δ : NNReal} {η : ℝ} {s : Finset ι}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hη : 0 < η)
    (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3)))
    (hpt : ∀ i ∈ s, (δ : ENNReal) ^ (2 * η) * volume (T i).toShadedBody.carrier
      ≤ volume (T i).toShadedBody.shade) :
    ∃ lam Cd : NNReal, 1 ≤ Cd ∧ Cd * δ ^ (2 * η) ≤ lam ∧
      (∀ i ∈ s, (Cd : ENNReal)⁻¹ * ((lam : ENNReal) * volume (T i).toShadedBody.carrier) ≤
        volume (T i).toShadedBody.shade) ∧
      (∀ i ∈ s, volume (T i).toShadedBody.shade ≤
        (Cd : ENNReal) * ((lam : ENNReal) * volume (T i).toShadedBody.carrier)) := by
  have hδ0 : δ ≠ 0 := hδ.ne'
  have hδE : (δ : ENNReal) ≠ 0 := by simpa using hδ0
  have hδEtop : (δ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hcoeneg : ((δ ^ (-η) : NNReal) : ENNReal) = (δ : ENNReal) ^ (-η) :=
    ENNReal.coe_rpow_of_ne_zero hδ0 _
  have hcoepos : ((δ ^ η : NNReal) : ENNReal) = (δ : ENNReal) ^ η :=
    ENNReal.coe_rpow_of_ne_zero hδ0 _
  refine ⟨δ ^ η, δ ^ (-η), ?_, ?_, ?_, ?_⟩
  · exact NNReal.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1 (by linarith)
  · rw [← NNReal.rpow_add hδ0]
    apply le_of_eq
    congr 1
    ring
  · intro i hi
    have hkey : ((δ ^ (-η) : NNReal) : ENNReal)⁻¹ * ((δ ^ η : NNReal) : ENNReal)
        = (δ : ENNReal) ^ (2 * η) := by
      rw [hcoeneg, hcoepos, ← ENNReal.rpow_neg, neg_neg, ← ENNReal.rpow_add _ _ hδE hδEtop]
      congr 1
      ring
    calc ((δ ^ (-η) : NNReal) : ENNReal)⁻¹ *
          (((δ ^ η : NNReal) : ENNReal) * volume (T i).toShadedBody.carrier)
        = (δ : ENNReal) ^ (2 * η) * volume (T i).toShadedBody.carrier := by
          rw [← mul_assoc, hkey]
      _ ≤ _ := hpt i hi
  · intro i hi
    have hkey : ((δ ^ (-η) : NNReal) : ENNReal) * ((δ ^ η : NNReal) : ENNReal) = 1 := by
      rw [hcoeneg, hcoepos, ← ENNReal.rpow_add _ _ hδE hδEtop]
      simp
    calc volume (T i).toShadedBody.shade ≤ volume (T i).toShadedBody.carrier :=
          measure_mono (T i).toShadedBody.shade_subset
      _ = ((δ ^ (-η) : NNReal) : ENNReal) *
            (((δ ^ η : NNReal) : ENNReal) * volume (T i).toShadedBody.carrier) := by
          rw [← mul_assoc, hkey, one_mul]



/-! ### The producer -/

namespace Produce

/-- The ambient space of Section 9. -/
abbrev E3 := EuclideanSpace ℝ (Fin 3)

end Produce

open Produce in
/-- **Configuration `hyp:ml2setup` is producible.** The `ρ`-count datum
`Kakeya.VeryNotSticky.RhoParentData` of the refined family is a binder;
`Kakeya.VeryNotSticky.eventually_exists_veryNotSticky` below produces it from Lemma 9.1's
binders on the input family. -/
theorem exists_veryNotSticky_of_data {β ζ exscal ϱ η : ℝ} {δ : NNReal}
    (hβ : 0 < β) (hβ1 : β ≤ 1) (hζ : 0 < ζ) (hexscal : 0 < exscal) (hϱ : 0 < ϱ) (hη : 0 < η)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hKT : KatzTaoEstimate.{u} E3 β) (hF : FrostmanEstimate.{u} E3 β)
    (w : Kakeya.CoarseKTWindow.{u} β ϱ η exscal)
    (hwδ : 6 * δ ^ (exscal - η) ≤ w.wρ)
    {C₀ : NNReal} (hC₀ : 1 ≤ C₀)
    (hgrid : 1 ≤ η * (Tube.ssfGridLen δ : ℝ))
    (habs : (aScaleDataConstant C₀ 1 : ENNReal) ^ 2
      ≤ (δ : ENNReal) ^ (-η))
    {ι : Type u} {s : Finset ι} {T : ι → ShadedTube δ E3}
    (hball : ∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1)
    (hmax : maxDensity s (fun i ↦ (T i).toConvexSpaceBody) ≤ (δ : ENNReal) ^ (-η))
    {s' : Finset ι} (hs' : s' ⊆ s) {T' : ι → ShadedTube δ E3}
    (htube : ∀ i, (T' i).toTube = (T i).toTube)
    (hsh : ∀ i, (T' i).shade ⊆ (T i).shade)
    (hrho : RhoParentData δ ζ exscal η s' T')
    (huni : Nonempty (ShadedTube.ShadedUniformTubeSet s' T' (Tube.ssfGridLen δ) C₀))
    (hpt : ∀ i ∈ s', (δ : ENNReal) ^ (2 * η) * volume (T' i).toShadedBody.carrier
      ≤ volume (T' i).toShadedBody.shade)
    (htc : (1 : ENNReal) ≤ (δ : ENNReal) * (s'.card : ENNReal))
    (hloss : ((_root_.ShadedBody.rhoTubesSection9Loss 3 s'.card δ : NNReal) : ENNReal)
      ≤ (δ : ENNReal) ^ (-η))
    (hindloss : ((_root_.ShadedBody.rhoTubesInducedFullnessLoss 3 : NNReal) : ENNReal)
      ≤ (δ : ENNReal) ^ (-η))
    (hclm : ∀ k : ℕ, k ≤ Tube.ssfGridLen δ → ∀ x : E3,
      (δ : ENNReal) ^ η *
          (volume (Metric.cthickening
                (2 * (Tube.gridScale δ (Tube.ssfGridLen δ) k : ℝ))
                (⋃ i ∈ s', (T' i).toShadedBody.shade)) *
            (volume ((⋃ i ∈ s', (T' i).toShadedBody.shade) ∩
                  Metric.ball x (Tube.gridScale δ (Tube.ssfGridLen δ) k : ℝ)) /
              volume (Metric.ball x (Tube.gridScale δ (Tube.ssfGridLen δ) k : ℝ)))) ≤
        volume (⋃ i ∈ s', (T' i).toShadedBody.shade))
    (hmass : (δ : ENNReal) ^ η * ∑ i ∈ s, volume (T i).shade
      ≤ ∑ i ∈ s', volume (T' i).shade)
    {a b : NNReal}
    (hdims : δ ≤ a ∧ a ≤ b ∧ b ≤ δ ^ exscal) :
    ∃ (cfg : VeryNotSticky.{u}) (e : cfg.ι ≃ ι) (c : NNReal),
      (cfg.β = β ∧ cfg.ζ = ζ ∧ cfg.δ = δ ∧ cfg.exscal = exscal ∧ cfg.ϱ = ϱ ∧ cfg.η = η) ∧
      ShadedBody.IsCRefinement (cfg.s.map e.toEmbedding)
        (fun i ↦ (cfg.T (e.symm i)).toShadedBody) s (fun i ↦ (T i).toShadedBody) c ∧
      (δ : ENNReal) ^ η ≤ (c : ENNReal) := by
  classical
  have hδ0 : δ ≠ 0 := hδ.ne'
  have hδE : (δ : ENNReal) ≠ 0 := by simpa using hδ0
  have hbody : ∀ i, (T' i).toConvexSpaceBody = (T i).toConvexSpaceBody :=
    fun i => congrArg Tube.toConvexSpaceBody (htube i)
  have hcarset : ∀ i, (T' i).carrier = (T i).carrier :=
    fun i => congrArg ConvexSpaceBody.carrier (hbody i)
  have hball' : ∀ i ∈ s, (T' i).carrier ⊆ Metric.closedBall 0 1 := by
    intro i hi; rw [hcarset i]; exact hball i hi
  have hmax' : maxDensity s (fun i ↦ (T' i).toConvexSpaceBody) ≤ (δ : ENNReal) ^ (-η) := by
    rw [maxDensity_congr (fun i _ => hbody i)]; exact hmax
  have hmaxs' : maxDensity s' (fun i ↦ (T' i).toConvexSpaceBody) ≤ (δ : ENNReal) ^ (-η) :=
    le_trans (maxDensity_mono _ hs') hmax'
  obtain ⟨lam, Cd, hCd, hlam, hlb, hub⟩ :=
    exists_band_of_pointwise_two_eta hδ hδ1 hη T' hpt
  have hs'ne : s'.Nonempty := by
    rcases Finset.eq_empty_or_nonempty s' with h | h
    · rw [h] at htc; simp at htc
    · exact h
  obtain ⟨i₀, hi₀⟩ := hs'ne
  have hvpos : 0 < volume (T' i₀).carrier := by
    refine lt_of_lt_of_le ?_ (Tube.le_volume (T' i₀).toTube)
    have hc : ((Tube.le_volume.c (Module.finrank ℝ E3) : NNReal) : ENNReal) ≠ 0 := by
      simpa using (Tube.le_volume.c_pos (Module.finrank ℝ E3)).ne'
    have hd : ((δ : ENNReal) ^ (Module.finrank ℝ E3 - 1)) ≠ 0 :=
      pow_ne_zero _ (by simpa using hδ.ne')
    exact pos_iff_ne_zero.mpr (mul_ne_zero hc hd)
  have hsumne : ∑ i ∈ s', volume (T' i).toShadedBody.carrier ≠ 0 := by
    refine ne_of_gt (lt_of_lt_of_le hvpos ?_)
    exact Finset.single_le_sum (f := fun i => volume (T' i).toShadedBody.carrier)
      (fun i _ => bot_le) hi₀
  have hfull : (δ ^ (2 * η) : NNReal) ≤ ShadedBody.fullness s' (fun i ↦ (T' i).toShadedBody) := by
    refine le_fullness_of_pointwise hsumne (fun i hi => ?_)
    rw [ENNReal.coe_rpow_of_ne_zero hδ0]
    exact hpt i hi
  refine ⟨{ β := β, hβ := hβ, hβ1 := hβ1, ζ := ζ, hζ := hζ, δ := δ, hδ := hδ, hδ1 := hδ1,
            exscalb := exscal, hexscalb := hexscal, exscal := exscal, hexscal := hexscal,
            hscale := rfl, η := η, hη := hη, ι := ι, decidableEq := inferInstance,
            s := s', T := T',
            contained := fun i hi => hball' i (hs' hi),
            C₀ := C₀,
            hC₀ := hC₀,
            D₀ := 1, hD₀ := le_rfl, ckt := w.toData hwδ,
            uniform := huni,
            maxDensity_le := hmaxs',
            fullness_ge := hfull,
            lam := lam, Cd := Cd, hCd := hCd, lam_ge := hlam,
            shading_lb := hlb, shading_ub := hub,
            rho_count := hrho,
            ktEstimate := hKT, fEstimate := hF,
            ϱ := ϱ, hϱ := hϱ, a := a, b := b, hdims := hdims,
            tube_count := htc,
            aScaleData_absorb := habs,
            coarseLoss_absorb := hloss,
            inducedFullnessLoss_absorb := hindloss,
            coarseLocalMass := hclm,
            gridFine := hgrid },
    Equiv.refl ι, δ ^ η, ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_, ?_⟩
  · simp only [Equiv.refl_toEmbedding, Finset.map_refl, Equiv.refl_symm, Equiv.refl_apply]
    refine ⟨⟨hs', fun i _ => ⟨hbody i, hsh i⟩⟩, ?_⟩
    rw [ENNReal.coe_rpow_of_ne_zero hδ0]
    exact hmass
  · rw [ENNReal.coe_rpow_of_ne_zero hδ0]



/-! ### The (C4) group: the singleton biased factoring -/

/-- The partition of a `Finset` into its singletons. -/
def singletonFinpartition {ι : Type*} [DecidableEq ι] (s : Finset ι) : Finpartition s :=
  Finpartition.ofExistsUnique (s.image (fun i => ({i} : Finset ι)))
    (by
      intro p hp
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hp
      simpa using hi)
    (by
      intro a ha
      refine ⟨{a}, ⟨Finset.mem_image_of_mem _ ha, Finset.mem_singleton_self a⟩, ?_⟩
      rintro t ⟨ht, hat⟩
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 ht
      rw [Finset.mem_singleton] at hat
      rw [hat])
    (by simp)

@[simp]
theorem singletonFinpartition_parts {ι : Type*} [DecidableEq ι] (s : Finset ι) :
    (singletonFinpartition s).parts = s.image (fun i => ({i} : Finset ι)) := rfl



/-- **The density of a one-member family in its own member is `1`.**

A local copy of `Kakeya.densityIn_singleton_self` (`Kakeya/Factoring/RhoFreeParentCount.lean`),
reproved here in three lines so that this module does not have to import that file: its import
closure reaches `Kakeya.DimensionThree.MainLemma1.Factoring`, and Section 9 should not create a
dependency edge into Section 8's territory for one arithmetic identity. -/
theorem densityIn_singleton_self' {ι : Type*}
    (V : ι → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))) (i : ι)
    (hvol : 0 < volume (V i).carrier) (hvolt : volume (V i).carrier ≠ ⊤) :
    densityIn ({i} : Finset ι) V (V i) = 1 := by
  classical
  have hfil : ({i} : Finset ι).filter (fun j => V j ≤ V i) = {i} := by simp
  simp only [densityIn, hfil, Finset.sum_singleton]
  exact ENNReal.div_self hvol.ne' hvolt

/-- The density of the singleton-parts family in any body equals the density of the original
family. -/
theorem densityIn_singletonParts {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (V : ι → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)))
    (K : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))) :
    densityIn (s.image (fun i => ({i} : Finset ι))) (fun t => t.convexHull_biUnion V) K
      = densityIn s V K := by
  classical
  have hsum : (∑ t ∈ s.image (fun i => ({i} : Finset ι)) with
        (t.convexHull_biUnion V) ≤ K, volume (t.convexHull_biUnion V).carrier)
      = ∑ i ∈ s with V i ≤ K, volume (V i).carrier := by
    rw [Finset.sum_filter, Finset.sum_filter,
      Finset.sum_image (by intro a _ b _ h; simpa using h)]
    exact Finset.sum_congr rfl (fun i _ => by
      simp only [Finset.convexHull_biUnion_singleton])
  simp only [densityIn, hsum]



open Produce in
/-- **The (C4) biased factoring of Configuration `hyp:ml2setup` is free**, at the singleton
partition and the constant `max 4 δ^{-η}`. -/
theorem exists_biasedFactorization_singletons {ι : Type u} [DecidableEq ι] {δ : NNReal}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) {ϱ η : ℝ} (hϱ : 0 < ϱ) {s : Finset ι}
    (T : ι → ShadedTube δ E3)
    (hball : ∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1)
    (hmax : maxDensity s (fun i ↦ (T i).toConvexSpaceBody) ≤ (δ : ENNReal) ^ (-η)) :
    ∃ fact : ConvexSpaceBody.BiasedFactorization s (fun i ↦ (T i).toConvexSpaceBody)
        ConvexSpaceBody.closedUnitBall ϱ (max 4 (δ ^ (-η))),
      fact.parts = s.image (fun i => ({i} : Finset ι)) := by
  classical
  set V : ι → ConvexSpaceBody E3 := fun i ↦ (T i).toConvexSpaceBody with hVdef
  set Cf : NNReal := max 4 (δ ^ (-η)) with hCfdef
  have hCf4 : (4 : NNReal) ≤ Cf := le_max_left _ _
  have hCfη : δ ^ (-η) ≤ Cf := le_max_right _ _
  have hCf1 : (1 : NNReal) ≤ Cf := le_trans (by norm_num) hCf4
  have hCf1E : (1 : ENNReal) ≤ (Cf : ENNReal) := by exact_mod_cast hCf1
  have hCf0 : (Cf : ENNReal) ≠ 0 := by
    intro h; rw [h] at hCf1E; simp at hCf1E
  have hCftop : (Cf : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hvolpos : ∀ i, 0 < volume (V i).carrier := by
    intro i
    refine lt_of_lt_of_le ?_ (Tube.le_volume (T i).toTube)
    have hc : ((Tube.le_volume.c (Module.finrank ℝ E3) : NNReal) : ENNReal) ≠ 0 := by
      simpa using (Tube.le_volume.c_pos (Module.finrank ℝ E3)).ne'
    have hd : ((δ : ENNReal) ^ (Module.finrank ℝ E3 - 1)) ≠ 0 :=
      pow_ne_zero _ (by simpa using hδ.ne')
    exact pos_iff_ne_zero.mpr (mul_ne_zero hc hd)
  have hvoltop : ∀ i, volume (V i).carrier ≠ ⊤ := fun i => (V i).isCompact.measure_lt_top.ne
  have hhull : ∀ i : ι, ({i} : Finset ι).convexHull_biUnion V = V i :=
    fun i => Finset.convexHull_biUnion_singleton V i
  have hself : ∀ i, densityIn ({i} : Finset ι) V (V i) = 1 :=
    fun i => densityIn_singleton_self' V i (hvolpos i) (hvoltop i)
  have hmem : ∀ t ∈ (singletonFinpartition s).parts, ∃ i ∈ s, t = {i} := by
    intro t ht
    rw [singletonFinpartition_parts] at ht
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 ht
    exact ⟨i, hi, rfl⟩
  -- the max density of the singleton-parts family
  have hktparts : maxDensity (singletonFinpartition s).parts
      (fun t => t.convexHull_biUnion V) ≤ (δ : ENNReal) ^ (-η) := by
    rw [maxDensity_le_iff]
    intro K
    rw [singletonFinpartition_parts, densityIn_singletonParts]
    exact le_trans (le_maxDensity s V K) hmax
  refine ⟨{ toFinpartition := singletonFinpartition s
            contained := hball
            densityIn_le_biased := ?_
            maxDensity_le_densityIn_biased := ?_
            isKatzTao := ?_
            simDims := ?_ }, rfl⟩
  · -- (factmaxmod1)
    intro t ht K
    obtain ⟨i, hi, rfl⟩ := hmem t ht
    rw [hhull i, hself i, mul_one]
    by_cases hle : V i ≤ K
    · have hsub : volume (V i).carrier ≤ volume K.carrier := measure_mono hle
      have hKpos : volume K.carrier ≠ 0 := by
        intro h; rw [h] at hsub; exact (hvolpos i).ne' (le_antisymm hsub bot_le)
      have hd1 : densityIn ({i} : Finset ι) V K ≤ 1 := by
        have hfil : ({i} : Finset ι).filter (fun j => V j ≤ K) = {i} := by simp [hle]
        simp only [densityIn, hfil, Finset.sum_singleton]
        exact ENNReal.div_le_of_le_mul (by rw [one_mul]; exact hsub)
      refine le_trans hd1 ?_
      have hone : (1 : ENNReal) ≤ volume K.carrier / volume (V i).carrier :=
        (ENNReal.le_div_iff_mul_le (Or.inl (hvolpos i).ne') (Or.inl (hvoltop i))).mpr
          (by rw [one_mul]; exact hsub)
      calc (1 : ENNReal) ≤ (Cf : ENNReal) := hCf1E
        _ = (Cf : ENNReal) * 1 := (mul_one _).symm
        _ ≤ (Cf : ENNReal) * (volume K.carrier / volume (V i).carrier) ^ ϱ := by
            gcongr
            exact ENNReal.one_le_rpow hone hϱ
    · have hfil : ({i} : Finset ι).filter (fun j => V j ≤ K) = ∅ := by simp [hle]
      simp only [densityIn, hfil, Finset.sum_empty, ENNReal.zero_div]
      exact bot_le
  · -- the biased lower bound on the part density
    intro t ht
    obtain ⟨i, hi, rfl⟩ := hmem t ht
    rw [hhull i, hself i]
    have hUle : volume (V i).carrier
        ≤ volume (ConvexSpaceBody.closedUnitBall (E := E3)).carrier :=
      measure_mono (hball i hi)
    have hratio : volume (V i).carrier
        / volume (ConvexSpaceBody.closedUnitBall (E := E3)).carrier ≤ 1 :=
      ENNReal.div_le_of_le_mul (by rw [one_mul]; exact hUle)
    have hrpow : (volume (V i).carrier
        / volume (ConvexSpaceBody.closedUnitBall (E := E3)).carrier) ^ ϱ ≤ 1 := by
      calc (volume (V i).carrier
            / volume (ConvexSpaceBody.closedUnitBall (E := E3)).carrier) ^ ϱ
          ≤ (1 : ENNReal) ^ ϱ := by gcongr
        _ = 1 := ENNReal.one_rpow ϱ
    have hmaxCf : maxDensity s V ≤ (Cf : ENNReal) := by
      refine le_trans hmax ?_
      rw [← ENNReal.coe_rpow_of_ne_zero hδ.ne']
      exact_mod_cast hCfη
    calc (Cf : ENNReal)⁻¹ * (volume (V i).carrier
            / volume (ConvexSpaceBody.closedUnitBall (E := E3)).carrier) ^ ϱ * maxDensity s V
        ≤ (Cf : ENNReal)⁻¹ * 1 * (Cf : ENNReal) := by gcongr
      _ = 1 := by rw [mul_one, ENNReal.inv_mul_cancel hCf0 hCftop]
  · -- (factmaxmod2)
    intro t ht
    obtain ⟨i, hi, rfl⟩ := hmem t ht
    have hUle : volume (V i).carrier
        ≤ volume (ConvexSpaceBody.closedUnitBall (E := E3)).carrier :=
      measure_mono (hball i hi)
    have hUtop : volume (ConvexSpaceBody.closedUnitBall (E := E3)).carrier ≠ ⊤ :=
      (ConvexSpaceBody.closedUnitBall (E := E3)).isCompact.measure_lt_top.ne
    have hratio1 : volume (V i).carrier
        / volume (ConvexSpaceBody.closedUnitBall (E := E3)).carrier ≤ 1 :=
      ENNReal.div_le_of_le_mul (by rw [one_mul]; exact hUle)
    have hratio0 : 0 < volume (V i).carrier
        / volume (ConvexSpaceBody.closedUnitBall (E := E3)).carrier :=
      ENNReal.div_pos (hvolpos i).ne' hUtop
    have hge1 : (1 : ENNReal) ≤ (volume (V i).carrier
        / volume (ConvexSpaceBody.closedUnitBall (E := E3)).carrier) ^ (-ϱ) :=
      ENNReal.one_le_rpow_of_pos_of_le_one_of_neg hratio0 hratio1 (by linarith)
    rw [ConvexSpaceBody.IsKatzTao, hhull i]
    calc maxDensity (singletonFinpartition s).parts (fun t' => t'.convexHull_biUnion V)
        ≤ (δ : ENNReal) ^ (-η) := hktparts
      _ ≤ (Cf : ENNReal) := by
          rw [← ENNReal.coe_rpow_of_ne_zero hδ.ne']; exact_mod_cast hCfη
      _ = (Cf : ENNReal) * 1 := (mul_one _).symm
      _ ≤ (Cf : ENNReal) * (volume (V i).carrier
            / volume (ConvexSpaceBody.closedUnitBall (E := E3)).carrier) ^ (-ϱ) := by gcongr
  · -- similar dimensions
    intro t ht t' ht'
    obtain ⟨i, hi, rfl⟩ := hmem t ht
    obtain ⟨j, hj, rfl⟩ := hmem t' ht'
    rw [hhull i, hhull j, Pi.le_def]
    intro k
    rw [Pi.smul_apply, ENNReal.smul_def]
    have hlo : (1 : ENNReal) / 2 ≤ Metric.ethickness ℝ (V j).carrier 0 :=
      (T j).toTube.le_ethickness_zero
    have hhi : Metric.ethickness ℝ (V i).carrier 0 ≤ 1 + (δ : ENNReal) :=
      (T i).toTube.ethickness_zero_le
    have hrk : Module.finrank ℝ E3 - 1 = 2 := by simp
    have hlo2 : (δ : ENNReal) ≤ Metric.ethickness ℝ (V j).carrier 2 := by
      have h := (T j).toTube.le_ethickness_finrank_sub_one
      rwa [hrk] at h
    have hup1 : Metric.ethickness ℝ (V i).carrier 1 ≤ (δ : ENNReal) :=
      (T i).toTube.ethickness_one_le
    have hδE1 : (δ : ENNReal) ≤ 1 := by exact_mod_cast hδ1
    rcases Nat.lt_or_ge k 3 with hk | hk
    · interval_cases k
      · calc Metric.ethickness ℝ (V i).carrier 0 ≤ 1 + (δ : ENNReal) := hhi
          _ ≤ 2 := by
              calc (1 : ENNReal) + (δ : ENNReal) ≤ 1 + 1 := by gcongr
                _ = 2 := by norm_num
          _ = (4 : ENNReal) * ((1 : ENNReal) / 2) := by
              rw [one_div, show (4 : ENNReal) = 2 * 2 by norm_num, mul_assoc,
                ENNReal.mul_inv_cancel (by norm_num) (by norm_num), mul_one]
          _ ≤ (Cf : ENNReal) * Metric.ethickness ℝ (V j).carrier 0 := by
              gcongr
              exact_mod_cast hCf4
      · calc Metric.ethickness ℝ (V i).carrier 1 ≤ (δ : ENNReal) := hup1
          _ ≤ Metric.ethickness ℝ (V j).carrier 2 := hlo2
          _ ≤ Metric.ethickness ℝ (V j).carrier 1 := Metric.ethickness_antitone (by norm_num)
          _ = 1 * Metric.ethickness ℝ (V j).carrier 1 := (one_mul _).symm
          _ ≤ (Cf : ENNReal) * Metric.ethickness ℝ (V j).carrier 1 := by gcongr
      · calc Metric.ethickness ℝ (V i).carrier 2
            ≤ Metric.ethickness ℝ (V i).carrier 1 := Metric.ethickness_antitone (by norm_num)
          _ ≤ (δ : ENNReal) := hup1
          _ ≤ Metric.ethickness ℝ (V j).carrier 2 := hlo2
          _ = 1 * Metric.ethickness ℝ (V j).carrier 2 := (one_mul _).symm
          _ ≤ (Cf : ENNReal) * Metric.ethickness ℝ (V j).carrier 2 := by gcongr
    · have hfr : Module.finrank ℝ E3 ≤ k := by simpa using hk
      rw [Metric.ethickness_eq_zero_of_finrank_le hfr,
        Metric.ethickness_eq_zero_of_finrank_le hfr]
      simp



open Produce in
/-- **The two small John axes of a `δ`-tube in `ℝ³` are both `δ`.** -/
theorem thickness_tube_two {δ : NNReal} (T : Tube δ E3) :
    Metric.thickness ℝ T.carrier 2 = (δ : ℝ) := by
  have hrk : Module.finrank ℝ E3 - 1 = 2 := by simp
  have hlo2 : (δ : ENNReal) ≤ Metric.ethickness ℝ T.carrier 2 := by
    have h := T.le_ethickness_finrank_sub_one
    rwa [hrk] at h
  have hup1 : Metric.ethickness ℝ T.carrier 1 ≤ (δ : ENNReal) := T.ethickness_one_le
  have hup2 : Metric.ethickness ℝ T.carrier 2 ≤ (δ : ENNReal) :=
    le_trans (Metric.ethickness_antitone (by norm_num)) hup1
  have heq : Metric.ethickness ℝ T.carrier 2 = (δ : ENNReal) := le_antisymm hup2 hlo2
  have hbdd : Bornology.IsBounded T.carrier := T.toConvexSpaceBody.isCompact.isBounded
  rw [Metric.ethickness_thickness' hbdd 2, ← ENNReal.ofReal_coe_nnreal,
    ENNReal.ofReal_eq_ofReal_iff (Metric.thickness_nonneg _ _) δ.coe_nonneg] at heq
  exact heq



/-! ### The single missing datum, and the eventual producer -/

open Produce in
/-- **The band-uniform refinement**: the one object the construction of Configuration
`hyp:ml2setup` needs and that the tree does not supply. -/
def BandUniformRefinement {ι : Type u} (δ : NNReal) (η η' : ℝ) (s : Finset ι)
    (T : ι → ShadedTube δ E3) : Prop :=
  ∃ (s' : Finset ι) (T' : ι → ShadedTube δ E3), s' ⊆ s ∧
    (∀ i, (T' i).toTube = (T i).toTube) ∧
    (∀ i, (T' i).shade ⊆ (T i).shade) ∧
    (∃ C₀ : NNReal, 1 ≤ C₀ ∧ (C₀ : ENNReal) ≤ (δ : ENNReal) ^ (-η') ∧
      Nonempty (ShadedTube.ShadedUniformTubeSet s' T' (Tube.ssfGridLen δ) C₀)) ∧
    (∀ i ∈ s', (δ : ENNReal) ^ (2 * η) * volume (T' i).carrier ≤ volume (T' i).shade) ∧
    (1 : ENNReal) ≤ (δ : ENNReal) * (s'.card : ENNReal) ∧
    (δ : ENNReal) ^ η * ∑ i ∈ s, volume (T i).shade ≤ ∑ i ∈ s', volume (T' i).shade

/-- **The `δ`-free uniformity constant is eventually below the sub-polynomial cap.**

`ShadedTube.ssfUniformConst 3` depends on the dimension alone, so the cap
`C₀ ≤ δ^{-η'}` of `Kakeya.VeryNotSticky.BandUniformRefinement` is met by it for all small `δ`.
This is what makes the relaxation of the constant a genuine *weakening* of the clause: every
witness at the old, absolute constant is still a witness. -/
theorem eventually_ssfUniformConst_le_rpow_neg {η' : ℝ} (hη' : 0 < η') :
    ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
      ((ShadedTube.ssfUniformConst 3 : NNReal) : ENNReal) ≤ (δ : ENNReal) ^ (-η') :=
  eventually_ennreal_le_rpow_neg ENNReal.coe_ne_top hη'

open Produce in
/-- **Definition 2.2 at the `δ`-free constant supplies the capped clause.**  The witness is
`ShadedTube.ssfUniformConst 3` itself. -/
theorem capped_uniform_of_ssf {ι : Type u} {δ : NNReal} {η' : ℝ} {s : Finset ι}
    {T : ι → ShadedTube δ E3}
    (hcap : ((ShadedTube.ssfUniformConst 3 : NNReal) : ENNReal) ≤ (δ : ENNReal) ^ (-η'))
    (huni : Nonempty (ShadedTube.ShadedUniformTubeSet s T (Tube.ssfGridLen δ)
      (ShadedTube.ssfUniformConst 3))) :
    ∃ C₀ : NNReal, 1 ≤ C₀ ∧ (C₀ : ENNReal) ≤ (δ : ENNReal) ^ (-η') ∧
      Nonempty (ShadedTube.ShadedUniformTubeSet s T (Tube.ssfGridLen δ) C₀) :=
  ⟨ShadedTube.ssfUniformConst 3, ShadedTube.one_le_ssfUniformConst 3, hcap, huni⟩

open Produce in
/-- **Configuration `hyp:ml2setup` follows from the binders of
`Kakeya.VeryNotSticky.exists_setup_caseSideData` together with
`Kakeya.VeryNotSticky.BandUniformRefinement`, for all small `δ`.** The binders are Lemma 9.1's;
the `ρ`-count datum of the refined family is `Kakeya.VeryNotSticky.rhoParentData_of_binders`
with the retention `Kakeya.VeryNotSticky.card_retention_of_mass` at `c = δ^η`. -/
theorem eventually_exists_veryNotSticky {β ζ exscal ϱ η η' τ τ' : ℝ}
    (hβ : 0 < β) (hβ1 : β ≤ 1) (hζ : 0 < ζ) (hexscal : 0 < exscal) (hϱ : 0 < ϱ) (hη : 0 < η)
    (h8 : 8 * η' < η)
    (params : CaseParams β ζ exscal ϱ η τ τ')
    (hKT : KatzTaoEstimate.{u} E3 β) (hF : FrostmanEstimate.{u} E3 β)
    (w : Kakeya.CoarseKTWindow.{u} β ϱ η exscal) :
    ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
      ∀ {ι : Type u} (s : Finset ι) (T : ι → ShadedTube δ E3),
        (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1) →
        (∃ C : NNReal, 1 ≤ C ∧ (C : ENNReal) ≤ (δ : ENNReal) ^ (-η) ∧
          Nonempty (ShadedTube.ShadedUniformTubeSet s T (Tube.ssfGridLen δ) C)) →
        maxDensity s (fun i ↦ (T i).toConvexSpaceBody) ≤ (δ : ENNReal) ^ (-η) →
        ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) ≥ δ ^ η →
        (∀ ρ : NNReal, ρ ∈ Set.Icc (δ ^ (1 - exscal)) (δ ^ exscal) →
          ∃ (κ : Type u) (tρ : Finset κ) (Tρ : κ → Tube ρ E3),
            (tρ : Set κ).Pairwise
              (fun j k ↦ IsEssentiallyDistinct (Tρ j).carrier (Tρ k).carrier) ∧
            (∀ j ∈ tρ, ∃ i ∈ s, (T i).toConvexSpaceBody ≤ (Tρ j).toConvexSpaceBody) ∧
            (ρ : ℝ) ^ (-2 - ζ) ≤ (tρ.card : ℝ)) →
        BandUniformRefinement δ η η' s T →
        (∀ (s' : Finset ι) (T' : ι → ShadedTube δ E3), s' ⊆ s →
          (∀ i, (T' i).shade ⊆ (T i).shade) →
          ∀ k : ℕ, k ≤ Tube.ssfGridLen δ → ∀ x : E3,
            (δ : ENNReal) ^ η *
                (volume (Metric.cthickening
                      (2 * (Tube.gridScale δ (Tube.ssfGridLen δ) k : ℝ))
                      (⋃ i ∈ s', (T' i).toShadedBody.shade)) *
                  (volume ((⋃ i ∈ s', (T' i).toShadedBody.shade) ∩
                        Metric.ball x (Tube.gridScale δ (Tube.ssfGridLen δ) k : ℝ)) /
                    volume (Metric.ball x (Tube.gridScale δ (Tube.ssfGridLen δ) k : ℝ)))) ≤
              volume (⋃ i ∈ s', (T' i).toShadedBody.shade)) →
        ∃ (cfg : VeryNotSticky.{u}) (e : cfg.ι ≃ ι) (c : NNReal),
          (cfg.β = β ∧ cfg.ζ = ζ ∧ cfg.δ = δ ∧ cfg.exscal = exscal ∧ cfg.ϱ = ϱ ∧
              cfg.η = η) ∧
          ShadedBody.IsCRefinement (cfg.s.map e.toEmbedding)
            (fun i ↦ (cfg.T (e.symm i)).toShadedBody) s (fun i ↦ (T i).toShadedBody) c ∧
          (δ : ENNReal) ^ η ≤ (c : ENNReal) := by
  classical
  have hη1 : η ≤ 1 := by
    have h1 := params.slabDensity
    have h2 := params.scale
    linarith
  have hexscal1 : exscal ≤ 1 := le_of_lt (lt_trans params.scale (by norm_num))
  filter_upwards [eventually_gridFine hη,
      eventually_aScaleData_absorb_of_le 1 h8,
      eventually_coarseLoss_absorb (η := η) (K := (4 : ℝ)) hη (by norm_num),
      Kakeya.ML2Assembly.eventually_card_thresholds,
      Kakeya.VeryNotSticky.eventually_ennreal_le_rpow_neg
        (K := ((_root_.ShadedBody.rhoTubesInducedFullnessLoss 3 : NNReal) : ENNReal))
        ENNReal.coe_ne_top hη,
      w.eventually_radius (by linarith [params.slabDensity, hη] : (0:ℝ) < exscal - η)] with
    δ hgrid habs hcoarse hthr hindloss hwδ
  obtain ⟨hδ, hδ1, hδC⟩ := hthr
  intro ι s T hball huniS hmax hfull hcount hband hclmAll
  letI : DecidableEq ι := Classical.decEq ι
  obtain ⟨s', T', hs', htube, hsh, ⟨C₀, hC₀, hcap, huni⟩, hpt, htc, hmass⟩ := hband
  -- carriers are unchanged
  have hbody : ∀ i, (T' i).toConvexSpaceBody = (T i).toConvexSpaceBody :=
    fun i => congrArg Tube.toConvexSpaceBody (htube i)
  have hcarset : ∀ i, (T' i).carrier = (T i).carrier :=
    fun i => congrArg ConvexSpaceBody.carrier (hbody i)
  have hball' : ∀ i ∈ s, (T' i).carrier ⊆ Metric.closedBall 0 1 := by
    intro i hi; rw [hcarset i]; exact hball i hi
  have hmax' : maxDensity s (fun i ↦ (T' i).toConvexSpaceBody) ≤ (δ : ENNReal) ^ (-η) := by
    rw [maxDensity_congr (fun i _ => hbody i)]; exact hmax
  have hmaxs' : maxDensity s' (fun i ↦ (T' i).toConvexSpaceBody) ≤ (δ : ENNReal) ^ (-η) :=
    le_trans (maxDensity_mono _ hs') hmax'
  -- the cardinality budget, from the binders
  have hcardR : (s'.card : ℝ) ≤ (δ : ℝ) ^ (-(4 : ℝ)) :=
    Kakeya.ML2Assembly.card_le_rpow_neg_four hδ hδ1 hδC s' T'
      (fun i hi => hball' i (hs' hi)) hη1 hmaxs'
  have hcardN : ((s'.card : NNReal)) ≤ δ ^ (-(4 : ℝ)) := by
    have h : ((s'.card : NNReal) : ℝ) ≤ ((δ ^ (-(4 : ℝ)) : NNReal) : ℝ) := by
      rw [NNReal.coe_natCast, NNReal.coe_rpow]; exact hcardR
    exact_mod_cast h
  -- `s'` is nonempty
  have hs'ne : s'.Nonempty := by
    rcases Finset.eq_empty_or_nonempty s' with h | h
    · rw [h] at htc; simp at htc
    · exact h
  obtain ⟨i₀, hi₀⟩ := hs'ne
  have hloss := hcoarse s'.card (Finset.card_pos.mpr ⟨i₀, hi₀⟩) hcardN
  -- the working dimensions, at `a = b = δ`
  have hdd : δ ≤ δ ^ exscal := by
    have h := NNReal.rpow_le_rpow_of_exponent_ge hδ hδ1 hexscal1
    simpa using h
  -- the `ρ`-count datum on the parent `s`, with the retention from `hmass` at `c = δ^η`
  have hret : (δ : ENNReal) ^ (2 * η) * (s.card : ENNReal) ≤ (s'.card : ENNReal) :=
    card_retention_of_mass hδ hδ1 hs' htube hfull le_rfl hmass
  have hrho : RhoParentData δ ζ exscal η s' T' :=
    rhoParentData_of_binders hs' htube hball hmax huniS hcount hret
  exact exists_veryNotSticky_of_data hβ hβ1 hζ hexscal hϱ hη hδ hδ1 hKT hF w hwδ hC₀ hgrid
    (habs C₀ hC₀ hcap)
    hball hmax hs' htube hsh hrho huni hpt htc hloss hindloss (hclmAll s' T' hs' hsh)
    hmass ⟨le_rfl, le_rfl, hdd⟩



open Produce in
/-- **`BandUniformRefinement` is met by the identity refinement** as soon as the input family
is itself uniform at the dimension-only constant, individually `δ^{2η}`-full, and large.

This is the non-vacuity certificate for `Kakeya.VeryNotSticky.BandUniformRefinement`: the
predicate carries no clause beyond the three named ones, and in particular the refinement and
mass-retention clauses are free at `s' = s`, `T' = T`. -/
theorem bandUniformRefinement_self {ι : Type u} {δ : NNReal} (hδ1 : δ ≤ 1) {η η' : ℝ}
    (hη : 0 ≤ η) (s : Finset ι) (T : ι → ShadedTube δ E3)
    (huni : ∃ C₀ : NNReal, 1 ≤ C₀ ∧ (C₀ : ENNReal) ≤ (δ : ENNReal) ^ (-η') ∧
      Nonempty (ShadedTube.ShadedUniformTubeSet s T (Tube.ssfGridLen δ) C₀))
    (hpt : ∀ i ∈ s, (δ : ENNReal) ^ (2 * η) * volume (T i).carrier ≤ volume (T i).shade)
    (htc : (1 : ENNReal) ≤ (δ : ENNReal) * (s.card : ENNReal)) :
    BandUniformRefinement δ η η' s T := by
  have hδE1 : (δ : ENNReal) ≤ 1 := by exact_mod_cast hδ1
  refine ⟨s, T, Finset.Subset.refl s, fun _ => rfl, fun _ => Set.Subset.refl _, huni, hpt, htc, ?_⟩
  exact mul_le_of_le_one_left bot_le (ENNReal.rpow_le_one hδE1 hη)


open Produce in
/-- **Non-vacuity of the relaxed clause, retained by the old certificate.**

`Kakeya.VeryNotSticky.bandUniformRefinement_self` at the relaxed constant, fed from exactly the
data the `δ`-free version consumed. Nothing is lost by the relaxation: a family that is uniform
at `ShadedTube.ssfUniformConst 3`, individually `δ^{2η}`-full and large still witnesses
`Kakeya.VeryNotSticky.BandUniformRefinement` for all small `δ`. -/
theorem eventually_bandUniformRefinement_self {η η' : ℝ} (hη : 0 ≤ η) (hη' : 0 < η') :
    ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
      ∀ {ι : Type u} (s : Finset ι) (T : ι → ShadedTube δ E3),
        Nonempty (ShadedTube.ShadedUniformTubeSet s T (Tube.ssfGridLen δ)
          (ShadedTube.ssfUniformConst 3)) →
        (∀ i ∈ s, (δ : ENNReal) ^ (2 * η) * volume (T i).carrier ≤ volume (T i).shade) →
        (1 : ENNReal) ≤ (δ : ENNReal) * (s.card : ENNReal) →
        BandUniformRefinement δ η η' s T := by
  filter_upwards [eventually_ssfUniformConst_le_rpow_neg (η' := η') hη',
    Kakeya.ML2Assembly.eventually_card_thresholds] with δ hcap hthr
  obtain ⟨-, hδ1, -⟩ := hthr
  intro ι s T huni hpt htc
  exact bandUniformRefinement_self hδ1 hη s T (capped_uniform_of_ssf hcap huni) hpt htc



open Produce in
/-- **Three of the six clauses of `Kakeya.VeryNotSticky.BandUniformRefinement` are already
supplied by the binders**: the same-tube, shrinking-shade and *uniform* clauses, at the
dimension-only constant `ShadedTube.ssfUniformConst 3`, together with the aggregate fullness at
`δ^{2η}`.

The cardinality side condition of `Kakeya.VeryNotSticky.exists_uniform_refinement_fullness_two_eta`
is not an extra hypothesis: it follows from the binders `hball` and `hmax` through
`Kakeya.ML2Assembly.card_le_rpow_neg_four`, at the budget `K₀ = 4`.

What this leaves open in `BandUniformRefinement` is exactly the **pointwise** band clause, the
tube count `1 ≤ δ|𝕋'|`, and the mass-retention clause. -/
theorem eventually_uniform_refinement_of_binders {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) :
    ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
      ∀ {ι : Type u} (s : Finset ι) (T : ι → ShadedTube δ E3),
        (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1) →
        maxDensity s (fun i ↦ (T i).toConvexSpaceBody) ≤ (δ : ENNReal) ^ (-η) →
        δ ^ η ≤ ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) →
        ∃ s' ⊆ s, ∃ T' : ι → ShadedTube δ E3,
          (∀ i, (T' i).toTube = (T i).toTube) ∧
          (∀ i, (T' i).shade ⊆ (T i).shade) ∧
          Nonempty (ShadedTube.ShadedUniformTubeSet s' T' (Tube.ssfGridLen δ)
            (ShadedTube.ssfUniformConst 3)) ∧
          ShadedBody.IsRefinement s' (fun i ↦ (T' i).toShadedBody) s
            (fun i ↦ (T i).toShadedBody) ∧
          δ ^ (2 * η) ≤ ShadedBody.fullness s' (fun i ↦ (T' i).toShadedBody) := by
  obtain ⟨δ₀, hδ₀pos, hδ₀1, H⟩ := exists_uniform_refinement_fullness_two_eta.{u} hη 4
  have hfr : Module.finrank ℝ E3 = 3 := by simp
  have hle : ∀ᶠ (d : NNReal) in 𝓝[>] 0, d ≤ δ₀ := by
    filter_upwards [mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hδ₀pos)] with d hd
    exact le_of_lt hd
  filter_upwards [hle, Kakeya.ML2Assembly.eventually_card_thresholds] with δ hδδ₀ hthr
  obtain ⟨hδ0, hδ1, hδC⟩ := hthr
  intro ι s T hball hmax hfull
  have hcard : (s.card : ℝ) ≤ (δ : ℝ) ^ (-((4 : ℕ) : ℝ)) := by
    have h := Kakeya.ML2Assembly.card_le_rpow_neg_four hδ0 hδ1 hδC s T hball hη1 hmax
    simpa using h
  obtain ⟨s', hs', T', htube, hsh, huni, href, hfull2⟩ := H hδ0 hδδ₀ s T hball hcard hfull
  rw [hfr] at huni
  exact ⟨s', hs', T', htube, hsh, huni, href, hfull2⟩



/-! ### The residue, sharpened: the band and the mass budget are free -/

open Produce in
/-- **Two of the three open clauses of `Kakeya.VeryNotSticky.BandUniformRefinement` are free.**

Taking the refinement to be an *index selection with the shading untouched* — `T' := T` — the
pointwise band clause and the mass-retention clause are both delivered by
`Kakeya.VeryNotSticky.eventually_exists_shadingBand_eta` from the target's aggregate binder
`hfull` alone. What is left is the pair (uniformity of the selected index set at the
dimension-only constant, and the tube count), asked here of the subfamily the band pigeonhole
produces.

So the configuration half of GWZ Lemma 9.1 is **exactly**: *a `δ^{2η}`-dense subfamily that is
still uniform and still has `δ^{-1}` members.* No clause about the shading is open. -/
theorem eventually_bandUniformRefinement_of_uniformCount {η η' : ℝ} (hη : 0 < η) :
    ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
      ∀ {ι : Type u} (s : Finset ι) (T : ι → ShadedTube δ E3),
        s.Nonempty →
        δ ^ η ≤ ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) →
        (∀ s₂ ⊆ s,
          (∀ i ∈ s₂, (δ : ENNReal) ^ (2 * η) * volume (T i).carrier ≤ volume (T i).shade) →
          (1 : ENNReal) ≤ (δ : ENNReal) * (s₂.card : ENNReal) ∧
            (∃ C₀ : NNReal, 1 ≤ C₀ ∧ (C₀ : ENNReal) ≤ (δ : ENNReal) ^ (-η') ∧
              Nonempty (ShadedTube.ShadedUniformTubeSet s₂ T (Tube.ssfGridLen δ) C₀))) →
        BandUniformRefinement δ η η' s T := by
  filter_upwards [self_mem_nhdsWithin, eventually_exists_shadingBand_eta.{u} hη]
    with δ hδ0 hband
  intro ι s T hsne hfull hres
  have hδpos : (0 : NNReal) < δ := hδ0
  obtain ⟨i₀, hi₀⟩ := hsne
  set V : ι → ShadedBody E3 := fun i ↦ (T i).toShadedBody with hVdef
  set v : ENNReal := volume (T i₀).carrier with hvdef
  have hvol : ∀ i ∈ s, volume (V i).carrier = v := fun i _ =>
    _root_.Tube.volume_carrier_eq_volume_carrier (T i).toTube (T i₀).toTube
  have hvne : v ≠ 0 := by
    refine ne_of_gt (lt_of_lt_of_le ?_ (Tube.le_volume (T i₀).toTube))
    have hc : ((Tube.le_volume.c (Module.finrank ℝ E3) : NNReal) : ENNReal) ≠ 0 := by
      simpa using (Tube.le_volume.c_pos (Module.finrank ℝ E3)).ne'
    have hd : ((δ : ENNReal) ^ (Module.finrank ℝ E3 - 1)) ≠ 0 :=
      pow_ne_zero _ (by simpa using hδpos.ne')
    exact pos_iff_ne_zero.mpr (mul_ne_zero hc hd)
  obtain ⟨s₂, hs₂, lam, hlampos, hlamge, hbd, c, hcgood, href⟩ := hband hvol hvne hfull
  -- the pointwise band, cleared of `lam`
  have hhalf : (δ : ENNReal) ^ (2 * η) ≤ (2 : ENNReal)⁻¹ * (lam : ENNReal) := by
    have h2 : ((2 * δ ^ (2 * η) : NNReal) : ENNReal) ≤ (lam : ENNReal) := by exact_mod_cast hlamge
    have hcoe : ((2 * δ ^ (2 * η) : NNReal) : ENNReal)
        = 2 * (δ : ENNReal) ^ (2 * η) := by
      rw [ENNReal.coe_mul, ENNReal.coe_rpow_of_ne_zero hδpos.ne']
      norm_num
    rw [hcoe] at h2
    have h3 : (2 : ENNReal)⁻¹ * (2 * (δ : ENNReal) ^ (2 * η))
        ≤ (2 : ENNReal)⁻¹ * (lam : ENNReal) := by gcongr
    rwa [← mul_assoc, ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_mul] at h3
  have hpt : ∀ i ∈ s₂, (δ : ENNReal) ^ (2 * η) * volume (T i).carrier
      ≤ volume (T i).shade := by
    intro i hi
    refine le_trans ?_ (hbd i hi).1
    rw [← mul_assoc]
    gcongr
  obtain ⟨htc, huni⟩ := hres s₂ hs₂ hpt
  -- the mass-retention clause
  have hmass : (δ : ENNReal) ^ η * ∑ i ∈ s, volume (T i).shade
      ≤ ∑ i ∈ s₂, volume (T i).shade := by
    refine le_trans ?_ href.2
    have hcc : ((δ ^ η : NNReal) : ENNReal) ≤ (c : ENNReal) := by exact_mod_cast hcgood
    rw [← ENNReal.coe_rpow_of_ne_zero hδpos.ne']
    gcongr
  exact ⟨s₂, T, hs₂, fun _ => rfl, fun _ => Set.Subset.refl _, huni, hpt, htc, hmass⟩



/-! ### The tube count, reduced to a covering statement about `ρ`-tubes -/

open Produce in
/-- **`tube_count` follows from the `ρ`-count binder and *any* essentially distinct cover.**

The binder `hcount` supplies a *lower* bound `ρ^{-2-ζ}` on the size of every essentially
distinct family of `ρ`-tubes containing the members of `𝕋`. So a producer does not need a
*large* cover: it needs **one legal cover at all**, of cardinality at most `n`, and the binder
does the rest. Read at the coarse endpoint `ρ = δ^{1-exscal}` — admissible because
`exscal ≤ 1/2` (`Kakeya.VeryNotSticky.coarseScale_mem_window`) — the exponent arithmetic is
`(1 - exscal)(2 + ζ) ≥ 1`, so `δ^{-1} ≤ ρ^{-2-ζ} ≤ n`, which is the field
`Kakeya.VeryNotSticky.tube_count` at `n`.

This is the whole analytic content of clause (e) of
`Kakeya.VeryNotSticky.BandUniformRefinement`; what is left is the purely geometric
`hcover`, a **containment-preserving** essentially distinct coarsening. The tree's
`Kakeya.Tube.exists_maximal_essDistinct` and `Kakeya.Tube.refineToEssDistinctLeaves` extract an
essentially distinct *subfamily* and lose the containment, and
`Kakeya.Tube.overlapContainment` returns a convex body rather than a `ρ`-tube. -/
theorem eventually_tubeCount_of_edCover {ζ exscal : ℝ} (hζ : 0 ≤ ζ)
    (hexscal : exscal ≤ 1 / 2) :
    ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
      ∀ {ι : Type u} (s : Finset ι) (T : ι → ShadedTube δ E3) (n : ℕ),
        (∀ ρ : NNReal, ρ ∈ Set.Icc (δ ^ (1 - exscal)) (δ ^ exscal) →
          ∀ {κ : Type u} (tρ : Finset κ) (Tρ : κ → Tube ρ E3),
            (∀ i ∈ s, ∃ j ∈ tρ, (T i).toConvexSpaceBody ≤ (Tρ j).toConvexSpaceBody) →
            (tρ : Set κ).Pairwise
              (fun j k ↦ IsEssentiallyDistinct (Tρ j).carrier (Tρ k).carrier) →
            (ρ : ℝ) ^ (-2 - ζ) ≤ (tρ.card : ℝ)) →
        (∃ (κ : Type u) (tρ : Finset κ) (Tρ : κ → Tube (δ ^ (1 - exscal)) E3),
            (∀ i ∈ s, ∃ j ∈ tρ, (T i).toConvexSpaceBody ≤ (Tρ j).toConvexSpaceBody) ∧
            (tρ : Set κ).Pairwise
              (fun j k ↦ IsEssentiallyDistinct (Tρ j).carrier (Tρ k).carrier) ∧
            tρ.card ≤ n) →
        (1 : ENNReal) ≤ (δ : ENNReal) * (n : ENNReal) := by
  have hsmall : ∀ᶠ d : NNReal in 𝓝[>] 0, d ≤ 1 := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : NNReal) < 1 by norm_num)] with d hd
    exact hd.2.le
  filter_upwards [self_mem_nhdsWithin, hsmall] with δ hδ0 hδ1
  intro ι s T n hcount hcov
  obtain ⟨κ, tρ, Tρ, hcover, hED, hcard⟩ := hcov
  have hδpos : (0 : NNReal) < δ := hδ0
  have hδR : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδpos
  have hδR1 : (δ : ℝ) ≤ 1 := by exact_mod_cast hδ1
  have hmem : (δ ^ (1 - exscal) : NNReal) ∈ Set.Icc (δ ^ (1 - exscal)) (δ ^ exscal) :=
    coarseScale_mem_window hδpos hδ1 hexscal
  have hkey := hcount (δ ^ (1 - exscal)) hmem tρ Tρ hcover hED
  -- rewrite `ρ^{-2-ζ}` as a power of `δ`
  have hρR : ((δ ^ (1 - exscal) : NNReal) : ℝ) = (δ : ℝ) ^ (1 - exscal) := NNReal.coe_rpow _ _
  have hrw : (((δ ^ (1 - exscal) : NNReal) : ℝ)) ^ (-2 - ζ)
      = (δ : ℝ) ^ ((1 - exscal) * (-2 - ζ)) := by
    rw [hρR, ← Real.rpow_mul hδR.le]
  rw [hrw] at hkey
  -- `δ^{-1} ≤ δ^{(1-exscal)(-2-ζ)}` because the exponent is at most `-1`
  have hexp : (1 - exscal) * (-2 - ζ) ≤ -1 := by nlinarith
  have hstep : (δ : ℝ) ^ (-1 : ℝ) ≤ (δ : ℝ) ^ ((1 - exscal) * (-2 - ζ)) :=
    Real.rpow_le_rpow_of_exponent_ge hδR hδR1 hexp
  have hcardR : ((tρ.card : ℝ)) ≤ (n : ℝ) := by exact_mod_cast hcard
  have hfin : (δ : ℝ)⁻¹ ≤ (n : ℝ) := by
    rw [← Real.rpow_neg_one (δ : ℝ)]
    exact le_trans hstep (le_trans hkey hcardR)
  have hmulR : (1 : ℝ) ≤ (δ : ℝ) * (n : ℝ) := by
    rw [inv_le_iff_one_le_mul₀ hδR] at hfin
    linarith
  have hN : (1 : NNReal) ≤ δ * (n : NNReal) := by
    rw [← NNReal.coe_le_coe]
    push_cast
    exact hmulR
  calc (1 : ENNReal) = ((1 : NNReal) : ENNReal) := by simp
    _ ≤ ((δ * (n : NNReal) : NNReal) : ENNReal) := by exact_mod_cast hN
    _ = (δ : ENNReal) * (n : ENNReal) := by rw [ENNReal.coe_mul]; simp



/-! ### What the `ρ`-count binder does and does not force -/

open Produce in
/-- **The `ρ`-count binder forces the family to be non-empty**, by testing it on the *empty*
cover: the empty family of `ρ`-tubes covers `∅` and is vacuously pairwise essentially distinct,
so `hcount` would read `ρ^{-2-ζ} ≤ 0`. -/
theorem nonempty_of_rhoCount {δ : NNReal} {ζ exscal : ℝ} {ι : Type u} {s : Finset ι}
    {T : ι → ShadedTube δ E3} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hexscal : exscal ≤ 1 / 2)
    (hcount : ∀ ρ : NNReal, ρ ∈ Set.Icc (δ ^ (1 - exscal)) (δ ^ exscal) →
      ∀ {κ : Type u} (tρ : Finset κ) (Tρ : κ → Tube ρ E3),
        (∀ i ∈ s, ∃ j ∈ tρ, (T i).toConvexSpaceBody ≤ (Tρ j).toConvexSpaceBody) →
        (tρ : Set κ).Pairwise
          (fun j k ↦ IsEssentiallyDistinct (Tρ j).carrier (Tρ k).carrier) →
        (ρ : ℝ) ^ (-2 - ζ) ≤ (tρ.card : ℝ)) :
    s.Nonempty := by
  rcases Finset.eq_empty_or_nonempty s with h | h
  · exfalso
    have hmem := coarseScale_mem_window (exscal := exscal) hδ hδ1 hexscal
    have hkey := hcount (δ ^ (1 - exscal)) hmem (κ := PEmpty.{u + 1}) ∅ (fun x => x.elim)
      (by intro i hi; rw [h] at hi; simp at hi) (by simp)
    rw [Finset.card_empty] at hkey
    have hpos : 0 < ((δ ^ (1 - exscal) : NNReal) : ℝ) ^ (-2 - ζ) := by
      refine Real.rpow_pos_of_pos ?_ _
      exact_mod_cast NNReal.rpow_pos hδ
    simp only [Nat.cast_zero] at hkey
    linarith
  · exact h

open Produce in
/-- **The `ρ`-count binder forbids the whole family from sitting inside a single `ρ`-tube**, by
testing it on the *singleton* cover, on which `Set.Pairwise` is vacuous. -/
theorem not_all_le_of_rhoCount {δ ρ : NNReal} {ζ exscal : ℝ} {ι : Type u} {s : Finset ι}
    {T : ι → ShadedTube δ E3} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hζ : 0 ≤ ζ)
    (hρmem : ρ ∈ Set.Icc (δ ^ (1 - exscal)) (δ ^ exscal))
    (hcount : ∀ ρ : NNReal, ρ ∈ Set.Icc (δ ^ (1 - exscal)) (δ ^ exscal) →
      ∀ {κ : Type u} (tρ : Finset κ) (Tρ : κ → Tube ρ E3),
        (∀ i ∈ s, ∃ j ∈ tρ, (T i).toConvexSpaceBody ≤ (Tρ j).toConvexSpaceBody) →
        (tρ : Set κ).Pairwise
          (fun j k ↦ IsEssentiallyDistinct (Tρ j).carrier (Tρ k).carrier) →
        (ρ : ℝ) ^ (-2 - ζ) ≤ (tρ.card : ℝ)) :
    ∀ V : Tube ρ E3, ¬ (∀ i ∈ s, (T i).toConvexSpaceBody ≤ V.toConvexSpaceBody) := by
  intro V hall
  have hkey := hcount ρ hρmem (κ := PUnit.{u + 1}) {PUnit.unit} (fun _ => V)
    (fun i hi => ⟨PUnit.unit, Finset.mem_singleton_self _, hall i hi⟩)
    (by
      intro a ha b hb hab
      exact absurd (Subsingleton.elim a b) hab)
  rw [Finset.card_singleton] at hkey
  have hρR : (0 : ℝ) < (ρ : ℝ) := by exact_mod_cast hρ0
  have hρR1 : (ρ : ℝ) < 1 := by exact_mod_cast hρ1
  have hlt : (1 : ℝ) < (ρ : ℝ) ^ (-2 - ζ) := by
    refine Real.one_lt_rpow_iff_of_pos hρR |>.mpr (Or.inr ⟨hρR1, by linarith⟩)
  simp only [Nat.cast_one] at hkey
  linarith



/-! ### The missing positive primitive: essential distinctness *from* angular separation -/

open Produce in
/-- **Two `δ`-tubes whose directions are separated by `K δ` are essentially distinct.**

The tree carries only the *negative* direction — `Kakeya.Tube.tubeOverlapCoreClose` and
`Kakeya.Tube.exists_maximal_essDistinct` deduce closeness *from* failure of essential
distinctness — so every producer of an essentially distinct family in this development has to
*select* a subfamily rather than *construct* one. This is the converse, and it is the first half
of any construction of the cover asked for by
`Kakeya.VeryNotSticky.eventually_tubeCount_of_edCover`.

It is the transversality estimate `Kakeya.Tube.volume_inter_le_of_angle` divided by the uniform
lower bound `Kakeya.Tube.le_volume` on a tube's own volume: at angular separation `M ≥ K δ` the
intersection is at most `C δ² (δ / M) ≤ (C / K) δ²`, while each tube has volume at least `c₃ δ²`,
so `K := 2 C / c₃` puts the intersection below half the maximum. The constant is existential for
the same reason `volume_inter_le_of_angle`'s is. -/
theorem exists_isEssentiallyDistinct_of_direction_sep :
    ∃ K : ℝ, 1 ≤ K ∧
      ∀ {δ : NNReal}, 0 < δ → δ ≤ 1 → ∀ T T' : Tube δ E3,
        K * (δ : ℝ) ≤ min ‖T.direction - T'.direction‖ ‖T.direction + T'.direction‖ →
        IsEssentiallyDistinct T.carrier T'.carrier := by
  obtain ⟨C, hCpos, hC⟩ := Tube.volume_inter_le_of_angle (E := E3) (by simp)
  set c : ℝ := ((Tube.le_volume.c 3 : NNReal) : ℝ) with hcdef
  have hcpos : 0 < c := by
    rw [hcdef]; exact_mod_cast Tube.le_volume.c_pos 3
  refine ⟨max 1 (2 * C / c), le_max_left _ _, ?_⟩
  intro δ hδ hδ1 T T' hsep
  have hδR : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ
  set K : ℝ := max 1 (2 * C / c) with hKdef
  have hK1 : (1 : ℝ) ≤ K := le_max_left _ _
  have hK2 : 2 * C / c ≤ K := le_max_right _ _
  set M : ℝ := min ‖T.direction - T'.direction‖ ‖T.direction + T'.direction‖ with hMdef
  have hδM : (δ : ℝ) ≤ M := le_trans (by nlinarith) hsep
  have hMpos : 0 < M := lt_of_lt_of_le hδR hδM
  have hbound := hC hδ hδ1 T T'
  rw [← hMdef, max_eq_left hδM] at hbound
  have hfr : Module.finrank ℝ E3 - 1 = 2 := by simp
  rw [hfr] at hbound
  -- the separation, cleared of the division
  have hcm : 2 * C * (δ : ℝ) ≤ c * M := by
    have h2 : 2 * C / c * (δ : ℝ) ≤ M := le_trans (by nlinarith) hsep
    have h3 : c * (2 * C / c * (δ : ℝ)) ≤ c * M := by nlinarith
    have hce : c * (2 * C / c) = 2 * C := by field_simp
    rw [← mul_assoc, hce] at h3
    exact h3
  have hd2 : (0 : ℝ) ≤ (δ : ℝ) ^ 2 := by positivity
  have hfin : volume.real (T.carrier ∩ T'.carrier) ≤ c * (δ : ℝ) ^ 2 / 2 := by
    refine le_trans hbound ?_
    have hstep : C * (δ : ℝ) ^ 2 * min 1 ((δ : ℝ) / M)
        ≤ C * (δ : ℝ) ^ 2 * ((δ : ℝ) / M) :=
      mul_le_mul_of_nonneg_left (min_le_right _ _) (by positivity)
    refine le_trans hstep ?_
    rw [← mul_div_assoc, div_le_iff₀ hMpos]
    nlinarith [mul_le_mul_of_nonneg_right hcm hd2]
  -- transport to `ENNReal`
  have hvol_eq : volume T.carrier = volume T'.carrier :=
    _root_.Tube.volume_carrier_eq_volume_carrier T T'
  have hinter_top : volume (T.carrier ∩ T'.carrier) ≠ ⊤ :=
    ne_top_of_le_ne_top T'.toConvexSpaceBody.isCompact.measure_lt_top.ne
      (measure_mono Set.inter_subset_right)
  have hlow : ((Tube.le_volume.c 3 : NNReal) : ENNReal) * (δ : ENNReal) ^ 2
      ≤ volume T'.carrier := by
    have h := Tube.le_volume (E := E3) T'
    rw [hfr] at h
    simpa using h
  have hofReal : volume (T.carrier ∩ T'.carrier)
      ≤ ENNReal.ofReal (c * (δ : ℝ) ^ 2 / 2) := by
    rw [← ENNReal.ofReal_toReal hinter_top]
    exact ENNReal.ofReal_le_ofReal hfin
  have h2inv : ENNReal.ofReal ((2 : ℝ)⁻¹) = (2 : ENNReal)⁻¹ := by
    simp
  have hrewrite : ENNReal.ofReal (c * (δ : ℝ) ^ 2 / 2)
      = (2 : ENNReal)⁻¹ * (((Tube.le_volume.c 3 : NNReal) : ENNReal) * (δ : ENNReal) ^ 2) := by
    have hsplit : c * (δ : ℝ) ^ 2 / 2 = (2 : ℝ)⁻¹ * (c * (δ : ℝ) ^ 2) := by ring
    rw [hsplit, ENNReal.ofReal_mul (by norm_num), h2inv, hcdef,
      ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by positivity)]
    simp
  rw [IsEssentiallyDistinct, hvol_eq, max_self]
  calc volume (T.carrier ∩ T'.carrier)
      ≤ ENNReal.ofReal (c * (δ : ℝ) ^ 2 / 2) := hofReal
    _ = (2 : ENNReal)⁻¹ * (((Tube.le_volume.c 3 : NNReal) : ENNReal) * (δ : ENNReal) ^ 2) :=
        hrewrite
    _ ≤ (2 : ENNReal)⁻¹ * volume T'.carrier := by gcongr
    _ = 1 / 2 * volume T'.carrier := by rw [one_div]



/-! ### What `tube_count` would need if it were a binder rather than a derivation -/

open Produce in
/-- **The exact binder that discharges `Kakeya.VeryNotSticky.tube_count`.**

`hcount` is the only binder of `Kakeya.VeryNotSticky.exists_setup_caseSideData` that bounds
`|𝕋|` from *below*, and it can be spent only through an essentially distinct cover
(`Kakeya.VeryNotSticky.eventually_tubeCount_of_edCover`). The two other candidates go the wrong
way or carry no cardinality at all: `hball` together with `hΔ` bound `|𝕋|` from **above**
(`Kakeya.ML2Assembly.card_le_rpow_neg_four`), `hfull` is a ratio, and `huni` is met by a
one-member family (`Kakeya.ml1Boot.nonempty_shadedUniformTubeSet_singleton`).

If the cover is unavailable, the honest repair is the one `hβ1` and `hplankF` already received:
make it a binder. This lemma says exactly which binder, and it is **not** `1 ≤ δ|𝕋|`: the
refinement that produces `cfg.s` loses a factor `δ^α` of the cardinality (`α = η/2` on the
`ShadedTube.exists_shadedUniformTubeSet_subfamily_ssf` route), so the binder has to be asked at
`δ^{1+α}`, i.e. `|𝕋| ≥ δ^{-1-α}`. -/
theorem tubeCount_of_parent_of_retention {δ : NNReal} {α : ℝ} (hδ : 0 < δ)
    {ι : Type u} {s s' : Finset ι}
    (hparent : (1 : ENNReal) ≤ (δ : ENNReal) ^ (1 + α) * (s.card : ENNReal))
    (hret : (δ : ENNReal) ^ α * (s.card : ENNReal) ≤ (s'.card : ENNReal)) :
    (1 : ENNReal) ≤ (δ : ENNReal) * (s'.card : ENNReal) := by
  have hδ0 : (δ : ENNReal) ≠ 0 := by simpa using hδ.ne'
  have hδtop : (δ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  calc (1 : ENNReal) ≤ (δ : ENNReal) ^ (1 + α) * (s.card : ENNReal) := hparent
    _ = (δ : ENNReal) * ((δ : ENNReal) ^ α * (s.card : ENNReal)) := by
        rw [ENNReal.rpow_add _ _ hδ0 hδtop, ENNReal.rpow_one, mul_assoc]
    _ ≤ (δ : ENNReal) * (s'.card : ENNReal) := by gcongr

end Kakeya.VeryNotSticky

namespace Kakeya.VeryNotSticky

open MeasureTheory Metric Set Topology Filter ShadedBody

universe u

open Produce in
/-- **The transverse twin: two parallel `ρ`-tubes separated in a direction orthogonal to their
common axis are essentially distinct.**

Together with `Kakeya.VeryNotSticky.exists_isEssentiallyDistinct_of_direction_sep` this gives the
development, for the first time, a way to **construct** an essentially distinct family of tubes
rather than *select* one: the angular criterion covers the case of separated directions, this one
the case of a common direction. Every other essential-distinctness lemma in the tree
(`Kakeya.Tube.overlapTransversal`, `Kakeya.Tube.tubeOverlapCoreClose`,
`Kakeya.Tube.exists_maximal_essDistinct`, `Kakeya.Tube.refineToEssDistinctLeaves`) runs the other
way, deducing closeness *from failure* of essential distinctness.

The separating functional `e` is taken as data — a unit vector orthogonal to the common direction,
together with the size of the midpoint gap it sees. That is the form a net construction supplies
it in, and it avoids normalising the transverse component of the gap.

**The bound proved here is `2ρ`, i.e. outright disjointness**, which is the sharpest threshold
reachable from containment alone: a point of the tube is within `ρ` of the core, the core is
`e`-constant, so the two `e`-projections are intervals of radius `ρ` about the two midpoints. -/
theorem isEssentiallyDistinct_of_transverse_sep {ρ : NNReal} (T T' : Tube ρ E3)
    (e : E3) (he : ‖e‖ = 1)
    (heT : inner ℝ e T.direction = (0 : ℝ)) (heT' : inner ℝ e T'.direction = (0 : ℝ))
    (hsep : 2 * (ρ : ℝ) < |inner ℝ e (T.midpoint - T'.midpoint)|) :
    IsEssentiallyDistinct T.carrier T'.carrier := by
  have key : ∀ S : Tube ρ E3, inner ℝ e S.direction = (0 : ℝ) → ∀ p ∈ S.carrier,
      |inner ℝ e (p - S.midpoint)| ≤ (ρ : ℝ) := by
    intro S hSe p hpS
    rw [S.carrier_eq] at hpS
    obtain ⟨z, hz, hpz⟩ := Set.mem_iUnion₂.1 hpS
    obtain ⟨a, b, ha, hb, hab, hzeq⟩ := hz
    have hzmid : z - S.midpoint = (b - 1 / 2 : ℝ) • S.direction := by
      have ha' : a = 1 - b := by linarith
      simp only [Tube.midpoint, Tube.direction, ← hzeq, ha']
      module
    have hinner_z : inner ℝ e (z - S.midpoint) = (0 : ℝ) := by
      rw [hzmid, real_inner_smul_right, hSe, mul_zero]
    have hsplit : p - S.midpoint = (p - z) + (z - S.midpoint) := by abel
    have hpz' : ‖p - z‖ ≤ (ρ : ℝ) := by
      have := Metric.mem_closedBall.1 hpz
      rwa [dist_eq_norm] at this
    calc |inner ℝ e (p - S.midpoint)|
        = |inner ℝ e (p - z)| := by rw [hsplit, inner_add_right, hinner_z, add_zero]
      _ ≤ ‖e‖ * ‖p - z‖ := abs_real_inner_le_norm e (p - z)
      _ ≤ (ρ : ℝ) := by rw [he, one_mul]; exact hpz'
  have hdisj : Disjoint T.carrier T'.carrier := by
    rw [Set.disjoint_left]
    intro p hp hp'
    have h1 := key T heT p hp
    have h2 := key T' heT' p hp'
    have hmid : inner ℝ e (T.midpoint - T'.midpoint)
        = inner ℝ e (p - T'.midpoint) - inner ℝ e (p - T.midpoint) := by
      rw [← inner_sub_right]
      congr 1
      abel
    rw [hmid] at hsep
    have := abs_sub (inner ℝ e (p - T'.midpoint)) (inner ℝ e (p - T.midpoint))
    have hle : |inner ℝ e (p - T'.midpoint) - inner ℝ e (p - T.midpoint)| ≤ 2 * (ρ : ℝ) :=
      le_trans (abs_sub _ _) (by linarith)
    linarith
  have hzero : volume (T.carrier ∩ T'.carrier) = 0 := by
    rw [Set.disjoint_iff_inter_eq_empty.1 hdisj, measure_empty]
  rw [IsEssentiallyDistinct, hzero]
  exact bot_le

end Kakeya.VeryNotSticky

namespace Kakeya.VeryNotSticky

open MeasureTheory Metric Set Topology Filter ShadedBody

universe u

open Produce in
/-- **The sharp transverse criterion: a gap of `ρ` already forces essential distinctness.**

`Kakeya.VeryNotSticky.isEssentiallyDistinct_of_transverse_sep` proves the threshold `2ρ`, which is
outright disjointness and is the most a containment argument can give. This lemma halves it, to
`ρ`, which is what the parallel case of the covering question needs: a midpoint net of covering
radius `ρ - δ` — the most `Kakeya.Tube.tube_carrier_subset_of_close` affords at `ε_dir = 0` — has
separation up to `2(ρ - δ)`, and `ρ < 2(ρ - δ)` as soon as `δ < ρ/2`. **So the parallel case
closes, with a factor-`2` margin rather than the `2δ` deficit the disjointness threshold leaves.**

The proof is not a volume computation at all, which is why it is short. Two `ρ`-tubes with a common
direction are exact **translates**: `T'.carrier = T.carrier + w` with `w` the midpoint gap. Put
`A := T ∩ T'` and `B := A + w`. Then `B ⊆ T'`, and `A ∩ B ⊆ T ∩ (T + 2w) = ∅` because a gap of
`2 ρ` in the `e`-projection separates `T` from `T + 2w`. So `A` and its translate are disjoint
subsets of `T'`, and translation invariance of Lebesgue measure gives `2 |A| ≤ |T'|` — which is
essential distinctness on the nose. -/
theorem isEssentiallyDistinct_of_transverse_sep_sharp {ρ : NNReal} (T T' : Tube ρ E3)
    (e : E3) (he : ‖e‖ = 1) (heT : inner ℝ e T.direction = (0 : ℝ))
    (hdir : T'.direction = T.direction)
    (hsep : (ρ : ℝ) < |inner ℝ e (T'.midpoint - T.midpoint)|) :
    IsEssentiallyDistinct T.carrier T'.carrier := by
  classical
  set w : E3 := T'.midpoint - T.midpoint with hw
  -- the two tubes are exact translates
  have hd : T'.y - T'.x = T.y - T.x := hdir
  have hx : T'.x = T.x + w := by
    have h : T'.x - (T.x + w) = (-(1 : ℝ) / 2) • ((T'.y - T'.x) - (T.y - T.x)) := by
      simp only [hw, Tube.midpoint]; module
    rw [hd, sub_self, smul_zero, sub_eq_zero] at h
    exact h
  have hy : T'.y = T.y + w := by
    have h : T'.y - (T.y + w) = ((1 : ℝ) / 2) • ((T'.y - T'.x) - (T.y - T.x)) := by
      simp only [hw, Tube.midpoint]; module
    rw [hd, sub_self, smul_zero, sub_eq_zero] at h
    exact h
  have htrans : ∀ p : E3, p ∈ T'.carrier ↔ p - w ∈ T.carrier := by
    intro p
    rw [T.carrier_eq, T'.carrier_eq]
    constructor
    · rintro hp
      obtain ⟨z, hz, hpz⟩ := Set.mem_iUnion₂.1 hp
      obtain ⟨a, b, ha, hb, hab, hzeq⟩ := hz
      refine Set.mem_iUnion₂.2 ⟨z - w, ⟨a, b, ha, hb, hab, ?_⟩, ?_⟩
      · have hb' : b = 1 - a := by linarith
        subst hb'
        rw [← hzeq, hx, hy]; module
      · rw [Metric.mem_closedBall, dist_eq_norm] at hpz ⊢
        rw [show p - w - (z - w) = p - z from by abel]; exact hpz
    · rintro hp
      obtain ⟨z, hz, hpz⟩ := Set.mem_iUnion₂.1 hp
      obtain ⟨a, b, ha, hb, hab, hzeq⟩ := hz
      refine Set.mem_iUnion₂.2 ⟨z + w, ⟨a, b, ha, hb, hab, ?_⟩, ?_⟩
      · have hb' : b = 1 - a := by linarith
        subst hb'
        rw [hx, hy, ← hzeq]; module
      · rw [Metric.mem_closedBall, dist_eq_norm] at hpz ⊢
        rw [show p - (z + w) = p - w - z from by abel]; exact hpz
  -- the `e`-projection bound on a tube
  have key : ∀ S : Tube ρ E3, inner ℝ e S.direction = (0 : ℝ) → ∀ p ∈ S.carrier,
      |inner ℝ e (p - S.midpoint)| ≤ (ρ : ℝ) := by
    intro S hSe p hpS
    rw [S.carrier_eq] at hpS
    obtain ⟨z, hz, hpz⟩ := Set.mem_iUnion₂.1 hpS
    obtain ⟨a, b, ha, hb, hab, hzeq⟩ := hz
    have hzmid : z - S.midpoint = (b - 1 / 2 : ℝ) • S.direction := by
      have ha' : a = 1 - b := by linarith
      simp only [Tube.midpoint, Tube.direction, ← hzeq, ha']
      module
    have hinner_z : inner ℝ e (z - S.midpoint) = (0 : ℝ) := by
      rw [hzmid, real_inner_smul_right, hSe, mul_zero]
    have hpz' : ‖p - z‖ ≤ (ρ : ℝ) := by
      have := Metric.mem_closedBall.1 hpz; rwa [dist_eq_norm] at this
    calc |inner ℝ e (p - S.midpoint)|
        = |inner ℝ e (p - z)| := by
          rw [show p - S.midpoint = (p - z) + (z - S.midpoint) from by abel,
            inner_add_right, hinner_z, add_zero]
      _ ≤ ‖e‖ * ‖p - z‖ := abs_real_inner_le_norm e (p - z)
      _ ≤ (ρ : ℝ) := by rw [he, one_mul]; exact hpz'
  -- `T` and `T + 2w` are disjoint
  have hdisj2 : ∀ q : E3, q ∈ T.carrier → q - w - w ∈ T.carrier → False := by
    intro q hq hq2
    have h1 := key T heT q hq
    have h2 := key T heT (q - w - w) hq2
    have hww : inner ℝ e (q - T.midpoint) - inner ℝ e (q - w - w - T.midpoint)
        = (2 : ℝ) * inner ℝ e w := by
      rw [← inner_sub_right]
      rw [show q - T.midpoint - (q - w - w - T.midpoint) = (2 : ℝ) • w from by module,
        real_inner_smul_right]
    have habs : |(2 : ℝ) * inner ℝ e w| ≤ 2 * (ρ : ℝ) := by
      rw [← hww]
      exact le_trans (abs_sub _ _) (by linarith)
    rw [abs_mul, abs_two] at habs
    have : |inner ℝ e w| ≤ (ρ : ℝ) := by linarith
    rw [hw] at hsep
    linarith
  -- the packing argument
  set A : Set E3 := T.carrier ∩ T'.carrier with hA
  set B : Set E3 := (fun p => p - w) ⁻¹' A with hB
  have hAmeas : MeasurableSet A :=
    (T.toConvexSpaceBody.isCompact.measurableSet).inter
      (T'.toConvexSpaceBody.isCompact.measurableSet)
  have hBmeas : MeasurableSet B := hAmeas.preimage (measurable_id.sub_const w)
  have hBsub : B ⊆ T'.carrier := by
    intro q hq
    exact (htrans q).2 hq.1
  have hAsub : A ⊆ T'.carrier := fun q hq => hq.2
  have hdisjAB : Disjoint A B := by
    rw [Set.disjoint_left]
    intro q hqA hqB
    exact hdisj2 q hqA.1 ((htrans (q - w)).1 hqB.2)
  have hvolB : volume B = volume A := by
    rw [hB, show (fun p : E3 => p - w) = (fun p : E3 => p + (-w)) from by
      funext p; rw [sub_eq_add_neg]]
    exact measure_preimage_add_right volume (-w) A
  have hsum : volume A + volume B ≤ volume T'.carrier := by
    rw [← measure_union hdisjAB hBmeas]
    exact measure_mono (Set.union_subset hAsub hBsub)
  rw [hvolB] at hsum
  have htwo : 2 * volume A ≤ volume T'.carrier := by
    rw [two_mul]; exact hsum
  rw [IsEssentiallyDistinct, ← hA, one_div]
  calc volume A = (2 : ENNReal)⁻¹ * (2 * volume A) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_mul]
    _ ≤ (2 : ENNReal)⁻¹ * volume T'.carrier := by gcongr
    _ ≤ (2 : ENNReal)⁻¹ * max (volume T.carrier) (volume T'.carrier) := by
        gcongr; exact le_max_right _ _

end Kakeya.VeryNotSticky

namespace Kakeya.VeryNotSticky

open MeasureTheory Metric Set Topology Filter ShadedBody

universe u

/-- **The product-net route to the cover of `Kakeya.VeryNotSticky.eventually_tubeCount_of_edCover`
is arithmetically impossible unless the angular essential-distinctness threshold is at most
`2ρ - 4δ`.**

A cover built as a product net — a net of directions of covering radius `ε_dir` crossed with a net
of transverse positions of covering radius `ε_pos` — has to satisfy three constraints at once:

* `hbudget`, the containment budget of `Kakeya.Tube.tube_carrier_subset_of_close`: a `δ`-tube whose
  direction is within `ε_dir` and whose midpoint is within `ε_pos` of a net point lies inside that
  net point's `ρ`-tube exactly when `ε_pos + ε_dir/2 + δ ≤ ρ`;
* `hpos`, the transverse essential-distinctness threshold, which
  `Kakeya.VeryNotSticky.isEssentiallyDistinct_of_transverse_sep_sharp` puts at `ρ`: two net points
  in the same direction cell must be `ρ` apart transversally, and **no** net of covering radius
  `ε_pos` has minimum separation above `2 ε_pos`;
* `hdir`, the same for the angular threshold `tdir`, with the same best-case net inequality.

Both `hpos` and `hdir` are stated at the **most optimistic** net ratio, separation `= 2 ×` covering
radius, which no two-dimensional net achieves (the hexagonal optimum is `√3 ×`); so the conclusion
below is a *lower* bound on what would be needed, and any real net does worse.

The conclusion is the whole content: a product net exists only at an angular threshold
`tdir ≤ 2ρ - 4δ`. The sharp geometric threshold is `≈ 2.5 ρ`, and the one this development can
actually prove is `K ρ` with `K = max 1 (2 C / c₃)` from `Kakeya.Tube.volume_inter_le_of_angle`
(numerically `K ≈ 76`). Both exceed `2ρ`. **So the product-net route is closed, and the shortfall
is a constant — between `12.5 %` at the optimistic ratio and `30 %` at the achievable hexagonal
one — which, `hcount` quantifying a single `ρ`, no exponent in `Kakeya.VeryNotSticky.CaseParams`
can buy.** -/
theorem productNet_budget_infeasible {ρ δ tdir εpos εdir : ℝ}
    (hbudget : εpos + εdir / 2 + δ ≤ ρ)
    (hpos : ρ ≤ 2 * εpos)
    (hdir : tdir ≤ 2 * εdir) :
    tdir ≤ 2 * ρ - 4 * δ := by
  linarith

/-- **The same, in the contrapositive form a producer meets it in**: at any angular threshold
strictly above `2ρ - 4δ` — in particular at the sharp `2.5 ρ`, and at the `K ρ` this development
can prove — no product net satisfies the containment budget.

This is the compiled form of the statement that clause (e) of
`Kakeya.VeryNotSticky.BandUniformRefinement` does **not** close from the two essential-distinctness
criteria of this file. What is left uncovered is the *intermediate-angle band*: pairs of covering
tubes whose directions differ by a nonzero amount below the angular threshold and whose gap along
the single common normal is at most `2ρ`. The angular criterion
(`Kakeya.VeryNotSticky.exists_isEssentiallyDistinct_of_direction_sep`) needs the directions further
apart; the sharp transverse criterion
(`Kakeya.VeryNotSticky.isEssentiallyDistinct_of_transverse_sep_sharp`) needs them *equal*; and the
disjointness criterion (`Kakeya.VeryNotSticky.isEssentiallyDistinct_of_transverse_sep`) needs a gap
above `2ρ` along the one direction orthogonal to both axes. A product net at the optimal split of
the budget lands squarely inside that band, and by the previous lemma it cannot be moved out. -/
theorem not_productNet_of_threshold_gt {ρ δ tdir : ℝ} (h : 2 * ρ - 4 * δ < tdir) :
    ¬ ∃ εpos εdir : ℝ, εpos + εdir / 2 + δ ≤ ρ ∧ ρ ≤ 2 * εpos ∧ tdir ≤ 2 * εdir := by
  rintro ⟨εpos, εdir, hbudget, hpos, hdir⟩
  exact absurd (productNet_budget_infeasible hbudget hpos hdir) (not_le.mpr h)

/-- **The threshold `2ρ - 4δ` is sharp, so the previous two lemmas are not vacuous.**

At any angular threshold `tdir ≤ 2ρ - 4δ` the product net *does* fit the budget, at
`ε_pos = ρ/2` and `ε_dir = tdir/2`. So `Kakeya.VeryNotSticky.productNet_budget_infeasible` is an
equivalence in disguise, and `Kakeya.VeryNotSticky.not_productNet_of_threshold_gt` rules out
exactly the thresholds above it — including the sharp `2.5 ρ` and the provable `K ρ`, and
excluding nothing that a correct criterion could ever reach. -/
theorem exists_productNet_of_threshold_le {ρ δ tdir : ℝ} (h : tdir ≤ 2 * ρ - 4 * δ) :
    ∃ εpos εdir : ℝ, εpos + εdir / 2 + δ ≤ ρ ∧ ρ ≤ 2 * εpos ∧ tdir ≤ 2 * εdir :=
  ⟨ρ / 2, tdir / 2, by linarith, by linarith, by linarith⟩

end Kakeya.VeryNotSticky
