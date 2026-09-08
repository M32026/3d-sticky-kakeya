/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineFourFactorRowsSite

@[expose] public section

open MeasureTheory Metric ConvexSpaceBody ShadedBody
open scoped NNReal ENNReal Topology

namespace Kakeya.ML2Core

open Classical in
/-- B31's hand-back wrapper with its producer's quantitative retained-card row preserved.
The geometric supplier is required only on subsets satisfying that same row. -/
theorem source_exists_handBack_at_fibre.{w} (K₀ : ℕ)
    {α α' : ℝ} (hα0 : 0 < α) (hα'0 : 0 < α') :
    ∃ δ₀ : NNReal, 0 < δ₀ ∧
      ∀ {ι : Type w} {δ δ' Cu : NNReal} {u : Finset ι}
        {T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
        (𝒰 : Tube.UniformTubeSet u (fun i => (T i).toTube) (Tube.ssfGridLen δ) Cu)
        {t₁ : Finset ι} {p b : ℕ} {v : EuclideanSpace ℝ (Fin 3)} {R ϖ ζ ηd qc : ℝ}
        (hsit : Tube.IsRescalingSituation (Tube.gridScale δ (Tube.ssfGridLen δ) p)
          (Tube.gridScale δ (Tube.ssfGridLen δ) b) δ' R 3) (hR : 0 < R),
        (Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)
            / (Tube.gridScale δ (Tube.ssfGridLen δ) p : ℝ) ≤ 4 * (δ' : ℝ) →
        0 < δ' → δ' ≤ δ₀ → (δ' : ℝ) ≤ 1 / 20 →
        0 < qc → α' ≤ qc → (512 : ENNReal) ≤ (δ' : ENNReal) ^ (-qc) →
        0 ≤ ϖ → 0 ≤ 2 + ζ → δ' ^ ϖ ≤ 1 / 2 →
        ((ShadedTube.ssfUniformConst 3 : NNReal) : ENNReal) ≤ (δ' : ENNReal) ^ (-ηd) →
        p ≤ b → b ≤ Tube.ssfGridLen δ →
        ∀ tτ' : Finset ι,
        tτ' ⊆ ML2Reduction.activeNodes (retainedLeafChain 𝒰 t₁ b) b →
        ∀ Yτ' : ι → ShadedTube (Tube.gridScale δ (Tube.ssfGridLen δ) b)
            (EuclideanSpace ℝ (Fin 3)),
        (∀ j, (Yτ' j).toTube = ((retainedLeafChain 𝒰 t₁ b).tube b j).translate v) →
        ∀ jp : ι,
        ({j ∈ tτ' | ML2Reduction.coarseNode (retainedLeafChain 𝒰 t₁ b) p b j = jp}
          : Finset ι).Nonempty →
        (({j ∈ tτ' | ML2Reduction.coarseNode (retainedLeafChain 𝒰 t₁ b) p b j = jp}
          : Finset ι).card : ℝ) ≤ (δ' : ℝ) ^ (-(K₀ : ℝ)) →
        Kakeya.maxDensity
          ({j ∈ tτ' | ML2Reduction.coarseNode (retainedLeafChain 𝒰 t₁ b) p b j = jp}
            : Finset ι)
          (fun i => (ML2Reduction.outerFamily hsit.pos_ambient
            (((retainedLeafChain 𝒰 t₁ b).tube p jp).translate v) hR δ' Yτ' i).toConvexSpaceBody)
            ≤ (δ' : ENNReal) ^ (-qc) →
        (δ' : ENNReal) ^ qc ≤ ShadedBody.fullness
          ({j ∈ tτ' | ML2Reduction.coarseNode (retainedLeafChain 𝒰 t₁ b) p b j = jp}
            : Finset ι)
          (fun i => (ML2Reduction.outerFamily hsit.pos_ambient
            (((retainedLeafChain 𝒰 t₁ b).tube p jp).translate v) hR δ' Yτ' i).toShadedBody) →
        (∀ t ⊆ ({j ∈ tτ' | ML2Reduction.coarseNode (retainedLeafChain 𝒰 t₁ b) p b j = jp}
            : Finset ι),
          (({j ∈ tτ' | ML2Reduction.coarseNode (retainedLeafChain 𝒰 t₁ b) p b j = jp}
            : Finset ι).card : ℝ) ≤ (δ' : ℝ) ^ (-α) * (t.card : ℝ) →
          (δ' : ENNReal) ^ qc ≤ ShadedBody.fullness t
            (fun i => (ML2Reduction.outerFamily hsit.pos_ambient
              (((retainedLeafChain 𝒰 t₁ b).tube p jp).translate v) hR δ' Yτ' i).toShadedBody)) →
        (∀ t ⊆ ({j ∈ tτ' | ML2Reduction.coarseNode (retainedLeafChain 𝒰 t₁ b) p b j = jp}
            : Finset ι),
          (({j ∈ tτ' | ML2Reduction.coarseNode (retainedLeafChain 𝒰 t₁ b) p b j = jp}
            : Finset ι).card : ℝ) ≤ (δ' : ℝ) ^ (-α) * (t.card : ℝ) →
          ShadedBody.multiplicity
            ({j ∈ tτ' | ML2Reduction.coarseNode (retainedLeafChain 𝒰 t₁ b) p b j = jp}
              : Finset ι)
            (fun i => (ML2Reduction.outerFamily hsit.pos_ambient
              (((retainedLeafChain 𝒰 t₁ b).tube p jp).translate v) hR δ' Yτ' i).toShadedBody)
            ≤ (δ' : ENNReal) ^ (-(3 * qc - α')) * ShadedBody.multiplicity t
              (fun i => (ML2Reduction.outerFamily hsit.pos_ambient
                (((retainedLeafChain 𝒰 t₁ b).tube p jp).translate v) hR δ' Yτ' i).toShadedBody)) →
        (∀ s'' : Finset ι,
          s'' ⊆ ({j ∈ tτ' | ML2Reduction.coarseNode (retainedLeafChain 𝒰 t₁ b) p b j = jp}
            : Finset ι) →
          (({j ∈ tτ' | ML2Reduction.coarseNode (retainedLeafChain 𝒰 t₁ b) p b j = jp}
            : Finset ι).card : ℝ) ≤ (δ' : ℝ) ^ (-α) * (s''.card : ℝ) →
          ∀ ρ : NNReal, ρ ∈ Set.Icc (δ' ^ (1 - ϖ)) (δ' ^ ϖ) →
          ∃ (κ₀ : Type w) (t : Finset κ₀)
            (W : κ₀ → Tube (ρ / Kakeya.VeryNotSticky.centringCoverRadiusConstant)
              (EuclideanSpace ℝ (Fin 3))),
            ((t : Set κ₀).Pairwise
              fun j k => _root_.IsEssentiallyDistinct (W j).carrier (W k).carrier) ∧
            (∀ j ∈ t, ∃ i ∈ s'',
              (ML2Reduction.spineFamily (ML2Reduction.spineRescaleUnit hsit.pos_ambient
                (((retainedLeafChain 𝒰 t₁ b).tube p jp).translate v) hR) Yτ' i).toConvexSpaceBody
                  ≤ (W j).toConvexSpaceBody) ∧
            (Kakeya.VeryNotSticky.centringCountLossConstant R : ℝ)
              * ((ρ / Kakeya.VeryNotSticky.centringCoverRadiusConstant : NNReal) : ℝ) ^ (-2 - ζ)
                ≤ (t.card : ℝ)) →
        ∃ (s'' : Finset ι) (U'' : ι → ShadedTube δ' (EuclideanSpace ℝ (Fin 3))),
          s'' ⊆ ({j ∈ tτ' | ML2Reduction.coarseNode (retainedLeafChain 𝒰 t₁ b) p b j = jp}
            : Finset ι) ∧
          (({j ∈ tτ' | ML2Reduction.coarseNode (retainedLeafChain 𝒰 t₁ b) p b j = jp}
            : Finset ι).card : ℝ) ≤ (δ' : ℝ) ^ (-α) * (s''.card : ℝ) ∧
          Kakeya.VeryNotSticky.CentredHandBack hsit hR
            (((retainedLeafChain 𝒰 t₁ b).tube p jp).translate v) 0 qc
            ({j ∈ tτ' | ML2Reduction.coarseNode (retainedLeafChain 𝒰 t₁ b) p b j = jp}
              : Finset ι) s'' Yτ' U'' ∧
          (∃ C : NNReal, 1 ≤ C ∧ (C : ENNReal) ≤ (δ' : ENNReal) ^ (-ηd) ∧
            Nonempty (ShadedTube.ShadedUniformTubeSet s'' U'' (Tube.ssfGridLen δ') C)) ∧
          (∀ ρ : NNReal, ρ ∈ Set.Icc (δ' ^ (1 - ϖ)) (δ' ^ ϖ) →
            ∃ (κ : Type w) (tρ : Finset κ) (Tρ : κ → Tube ρ (EuclideanSpace ℝ (Fin 3))),
              (tρ : Set κ).Pairwise
                (fun j k => _root_.IsEssentiallyDistinct (Tρ j).carrier (Tρ k).carrier) ∧
              (∀ j ∈ tρ, ∃ i ∈ s'', (U'' i).toConvexSpaceBody ≤ (Tρ j).toConvexSpaceBody) ∧
              (ρ : ℝ) ^ (-2 - ζ) ≤ (tρ.card : ℝ)) := by
  obtain ⟨δ₀, hδ₀0, hcore⟩ :=
    Kakeya.VeryNotSticky.exists_centredHandBack_uniform_and_countTransport.{w} K₀ hα0 hα'0
  refine ⟨δ₀, hδ₀0, ?_⟩
  intro ι δ δ' Cu u T 𝒰 t₁ p b v R ϖ ζ ηd qc hsit hR hτσ hδ'0 hδle hδ'20 hqc0 hα'qc hthr512
    hϖ hζ hthr hunithr hpb hbN tτ' htτ' Yτ' hYτ' jp hfne hcardfib hdensfib hfullfib hretfull
    hretmult hsupp
  obtain ⟨s'', hs''sub, U'', hcardret, hcb, hct, hstruct⟩ :=
    hcore hsit hR hτσ hδ'0 hδle hδ'20
      (((retainedLeafChain 𝒰 t₁ b).tube p jp).translate v) hqc0 hα'qc hthr512 hϖ hζ hthr
      ({j ∈ tτ' | ML2Reduction.coarseNode (retainedLeafChain 𝒰 t₁ b) p b j = jp} : Finset ι)
      Yτ' hfne (fibre_subset_parentTube 𝒰 hpb hbN htτ' hYτ' jp) hcardfib hdensfib hfullfib
      hretfull hretmult
  exact ⟨s'', U'', hs''sub, hcardret, hcb,
    ⟨ShadedTube.ssfUniformConst 3, ShadedTube.one_le_ssfUniformConst 3, hunithr, hstruct⟩,
    fun ρ hρ => hct ρ hρ (hsupp s'' hs''sub hcardret ρ hρ)⟩

open Classical in
/-- The old supply conclusion at the empty subset fails at this named positive radius.
The interval membership is retained; no assertion about an uninhabited interval is made. -/
theorem source_not_empty_cover_supply_at_radius.{w}
    {ι : Type w} {δ δ' Cu : NNReal} {u : Finset ι}
    {T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
    (𝒰 : Tube.UniformTubeSet u (fun i => (T i).toTube) (Tube.ssfGridLen δ) Cu)
    (t₁ tτ' : Finset ι) (p b : ℕ) (jp : ι) (v : EuclideanSpace ℝ (Fin 3))
    {R ϖ ζ : ℝ}
    (hsit : Tube.IsRescalingSituation (Tube.gridScale δ (Tube.ssfGridLen δ) p)
      (Tube.gridScale δ (Tube.ssfGridLen δ) b) δ' R 3) (hR : 0 < R)
    (hδ' : 0 < δ')
    (Yτ' : ι → ShadedTube (Tube.gridScale δ (Tube.ssfGridLen δ) b)
      (EuclideanSpace ℝ (Fin 3)))
    (ρ : NNReal) (hρ0 : 0 < ρ) (hρ : ρ ∈ Set.Icc (δ' ^ (1 - ϖ)) (δ' ^ ϖ)) :
    ¬ ∃ (κ₀ : Type w) (t : Finset κ₀)
      (W : κ₀ → Tube (ρ / Kakeya.VeryNotSticky.centringCoverRadiusConstant)
        (EuclideanSpace ℝ (Fin 3))),
      ((t : Set κ₀).Pairwise
        fun j k => _root_.IsEssentiallyDistinct (W j).carrier (W k).carrier) ∧
      (∀ j ∈ t, ∃ i ∈ (∅ : Finset ι),
        (ML2Reduction.spineFamily (ML2Reduction.spineRescaleUnit hsit.pos_ambient
          (((retainedLeafChain 𝒰 t₁ b).tube p jp).translate v) hR) Yτ' i).toConvexSpaceBody
            ≤ (W j).toConvexSpaceBody) ∧
      (Kakeya.VeryNotSticky.centringCountLossConstant R : ℝ)
        * ((ρ / Kakeya.VeryNotSticky.centringCoverRadiusConstant : NNReal) : ℝ) ^ (-2 - ζ)
          ≤ (t.card : ℝ) := by
  rintro ⟨κ₀, t, W, _, hused, hcount⟩
  have ht : t = ∅ := Finset.eq_empty_iff_forall_notMem.mpr (by
    intro j hj
    obtain ⟨i, hi, _⟩ := hused j hj
    exact Finset.notMem_empty i hi)
  rw [ht, Finset.card_empty, Nat.cast_zero] at hcount
  have hrad : (0 : ℝ) < ((ρ / Kakeya.VeryNotSticky.centringCoverRadiusConstant : NNReal) : ℝ) := by
    exact_mod_cast div_pos hρ0 Kakeya.VeryNotSticky.centringCoverRadiusConstant_pos
  have hconstant : (0 : ℝ) < Kakeya.VeryNotSticky.centringCountLossConstant R := by
    have h : (1 : ℝ) ≤ Kakeya.VeryNotSticky.centringCountLossConstant R := by
      exact_mod_cast Kakeya.VeryNotSticky.one_le_centringCountLossConstant R
    linarith
  exact (mul_pos hconstant (Real.rpow_pos_of_pos hrad _)).not_ge hcount

end Kakeya.ML2Core
